/* -*- Mode: C; tab-width: 4; c-basic-offset: 4; indent-tabs-mode: nil -*- */
/*
 * Hash table
 *
 * The hash function used here is by Bob Jenkins, 1996:
 *    <http://burtleburtle.net/bob/hash/doobs.html>
 *       "By Bob Jenkins, 1996.  bob_jenkins@burtleburtle.net.
 *       You may use this code any way you wish, private, educational,
 *       or commercial.  It's free."
 *
 * The rest of the file is licensed under the BSD license.  See LICENSE.
 */

#include "memcached.h"
#include <sys/stat.h>
#include <sys/socket.h>
#include <sys/resource.h>
#include <signal.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <errno.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <pthread.h>

/* how many powers of 2's worth of buckets we use */
unsigned int hashpower = HASHPOWER_DEFAULT;

#define hashsize(n) ((uint64_t)1<<(n))
#define hashmask(n) (hashsize(n)-1)


#define JOIN(a,b,c) a ## b ## c
#define GET_CLOCK_TYPE(size) JOIN(uint, size, _t)
#define GET_CLOCK_MAX(size) JOIN(UINT, size, _MAX)

#define CLOCK_SIZE 8 //Size of each clock variable in bits
#define CLOCK_TYPE GET_CLOCK_TYPE(CLOCK_SIZE)

//#define CLOCK
#ifdef CLOCK
    #define CLOCK_MAX 1
    #define INC_FACTOR 1
    #define DEC_FACTOR 1
#else
    #define CLOCK_MAX GET_CLOCK_MAX(CLOCK_SIZE)
    #define INC_FACTOR 1
    #define DEC_FACTOR 1
#endif

/* Main hash table. This is where we look except during expansion. */
static item** hashtable = 0;
static CLOCK_TYPE* clock_val = NULL;
static __thread uint32_t hand = 0;

void assoc_init(const int hashtable_init) {
    if (hashtable_init) {
        hashpower = hashtable_init;
    }

    hashtable = calloc(hashsize(hashpower), sizeof(void *));
    if (!hashtable) {
        fprintf(stderr, "Failed to init hashtable.\n");
        exit(EXIT_FAILURE);
    }

    clock_val = calloc(hashsize(hashpower), sizeof(CLOCK_TYPE));
    if (!clock_val) {
        fprintf(stderr, "Failed to init CLOCK values.\n");
        exit(EXIT_FAILURE);
    }

    STATS_LOCK();
    stats_state.hash_power_level = hashpower;
    stats_state.hash_bytes = hashsize(hashpower) * sizeof(void *);
    STATS_UNLOCK();
}

void static inline inc_clock(uint32_t bucket) {
    CLOCK_TYPE *clock = &clock_val[bucket];
    CLOCK_TYPE val = *clock;
    if(val < CLOCK_MAX - INC_FACTOR) {
        *clock = val + INC_FACTOR;
    } else {
        *clock = CLOCK_MAX;
    }
}

uint32_t static inline dec_clock(uint32_t bucket) {
    CLOCK_TYPE *clock = &clock_val[bucket];
    CLOCK_TYPE val = *clock;
    if(val > DEC_FACTOR) {
        *clock = val - DEC_FACTOR;
        return val;
    } else {
        *clock = 0;
        return val;
    }
}

item *assoc_find(const char *key, const size_t nkey, const uint32_t hv) {
    item *it;
    uint32_t hmask;

    hmask = hv & hashmask(hashpower);
    it = hashtable[hmask];
    inc_clock(hmask);

    item *ret = NULL;

    while (it) {
        if ((nkey == it->nkey) && (memcmp(key, ITEM_key(it), nkey) == 0)) {
            ret = it;
            break;
        }
        it = it->next;
    }

    MEMCACHED_ASSOC_FIND(key, nkey, depth);
    return ret;
}

/* returns the address of the item pointer before the key.  if *item == 0,
   the item wasn't found */

static item** _hashitem_before (const char *key, const size_t nkey, const uint32_t hmask) {
    item **pos;

    pos = &hashtable[hmask];

    while (*pos && ((nkey != (*pos)->nkey) || memcmp(key, ITEM_key(*pos), nkey))) {
        pos = &(*pos)->next;
    }
    return pos;
}

//static item** _hashitem_last (const uint32_t hmask) {
//    item **pos;
//    pos = &hashtable[hmask];
//    if(*pos == NULL) {return pos;}
//    while ((*pos)->next != NULL) {pos = &(*pos)->next;}
//    return pos;
//}

/* Note: this isn't an assoc_update.  The key must not already exist to call this */
int assoc_insert(item *it, const uint32_t hv) {
    uint32_t hmask;

    hmask = hv & hashmask(hashpower);
    inc_clock(hmask);

    it->next = hashtable[hmask];
    hashtable[hmask] = it;

    MEMCACHED_ASSOC_INSERT(ITEM_key(it), it->nkey);

    return 1;
}

item* assoc_delete(const char *key, const size_t nkey, const uint32_t hv) {
    uint32_t hmask;
    item **before;

    hmask = hv & hashmask(hashpower);
    //Should decrement CLOCK reference?

    before = _hashitem_before(key, nkey, hmask);

    if (*before) {
        item *nxt;
        /* The DTrace probe cannot be triggered as the last instruction
         * due to possible tail-optimization by the compiler
         */
        MEMCACHED_ASSOC_DELETE(key, nkey);
        nxt = (*before)->next;
        (*before)->next = 0;   /* probably pointless, but whatever. */
        item *ret = *before;
        *before = nxt;
        return ret;
    }
    /* Note:  we never actually get here.  the callers don't delete things
       they can't find. */

    assert(*before != 0);
    return NULL;
}

void assoc_bump(item *it, const uint32_t hv) {
    uint32_t hmask;
    hmask = hv & hashmask(hashpower);
    inc_clock(hmask);

    //Bump item in hash bucket
    //This causes significant loss in performance
    //assoc_delete(ITEM_key(it), it->nkey, hv);
    //assoc_insert(it, hv);
}

/* Returns number of items removed. */
int try_evict(const int orig_id, const uint64_t total_bytes, const rel_time_t max_age) {
    item *head, *next, *prev;
    head = next = prev = NULL;

    //Slab where we wanted to alloc (and therefore called this function)
    int id = orig_id; 
    if (id == 0)
        return 0;

    size_t removed = 0;
    size_t bytes_removed = 0;

    void *hold_lock = NULL;
    size_t num_buckets = hashsize(hashpower);

    uint32_t c = 0;
    while(c++ < num_buckets) { //Do one trip around every bucket at maximum
        hand = (hand + 1) % num_buckets;

        //Update this bucket's clock val
        //Only try to evict non-empty buckets: check if head != NULL
        //Note: does not need to be thread safe as we are not derefing head
        if(dec_clock(hand) == 0 && hashtable[hand] != NULL) {

            if ((hold_lock = item_trylock(hand)) == NULL)
                continue; //If we can't get lock immedeatly, search for next bucket

            //Pop off entire bucket
            head = hashtable[hand];
            hashtable[hand] = NULL;

            item_trylock_unlock(hold_lock);


            //another thread removed this bucket between
            //  checking if head was != NULL and acquiring the lock
            if(!head) continue; 

            next = head;
            while(next) {
                removed++;
                bytes_removed += ITEM_ntotal(next);

                prev = next;
                next = next->next;
                do_item_remove(prev);
            }

            if(bytes_removed >= total_bytes) {
                return removed;
            }
        }
    }

    return removed;
}
