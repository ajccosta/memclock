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

static pthread_cond_t maintenance_cond = PTHREAD_COND_INITIALIZER;
static pthread_mutex_t maintenance_lock = PTHREAD_MUTEX_INITIALIZER;

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
static item** primary_hashtable = 0;
static item** old_hashtable = 0;

/* Flag: Are we in the middle of expanding now? */
static bool expanding = false;
/*
 * During expansion we migrate values with bucket granularity; this is how
 * far we've gotten so far. Ranges from 0 .. hashsize(hashpower - 1) - 1.
 */
static uint64_t expand_bucket = 0;


static CLOCK_TYPE* clock_val = NULL;
static CLOCK_TYPE* old_clock_val = NULL; //Old clock values when 
static __thread uint32_t hand = 0;

void assoc_init(const int primary_hashtable_init) {
    if (primary_hashtable_init) {
        hashpower = primary_hashtable_init;
    }

    primary_hashtable = calloc(hashsize(hashpower), sizeof(void *));
    if (!primary_hashtable) {
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
    item *it = NULL;
    uint32_t hmask;

    if (expanding &&
        (hmask = (hv & hashmask(hashpower - 1))) >= expand_bucket)
    {
        it = old_hashtable[hmask];
    } else {
        hmask = hv & hashmask(hashpower);
        it = primary_hashtable[hmask];
    }

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
static item** _hashitem_before (const char *key, const size_t nkey, item **start) {
    item **pos = start;

    while (*pos && ((nkey != (*pos)->nkey) || memcmp(key, ITEM_key(*pos), nkey))) {
        pos = &(*pos)->next;
    }
    return pos;
}

//static item** _hashitem_last (const uint32_t hmask) {
//    item **pos;
//    pos = &primary_hashtable[hmask];
//    if(*pos == NULL) {return pos;}
//    while ((*pos)->next != NULL) {pos = &(*pos)->next;}
//    return pos;
//}

/* Note: this isn't an assoc_update.  The key must not already exist to call this */
int assoc_insert(item *it, const uint32_t hv) {
    uint32_t hmask;

    if (expanding &&
        (hmask = (hv & hashmask(hashpower - 1))) >= expand_bucket)
    {
        it->next = old_hashtable[hmask];
        old_hashtable[hmask] = it;

    } else {
        hmask = hv & hashmask(hashpower);
        it->next = primary_hashtable[hmask];
        primary_hashtable[hmask] = it;
    }

    inc_clock(hmask);

    MEMCACHED_ASSOC_INSERT(ITEM_key(it), it->nkey);

    return 1;
}

item* assoc_delete(const char *key, const size_t nkey, const uint32_t hv) {
    uint32_t hmask;
    item **before;
    item **start; //Item to start searching -> either old or curr hashtable

    if (expanding) {
        hmask = hv & hashmask(hashpower - 1);
        start = &old_hashtable[hmask];

        if(hmask < expand_bucket) {
            hmask = hv & hashmask(hashpower);
            start = &primary_hashtable[hmask];
        }

    } else {
        hmask = hv & hashmask(hashpower);
        start = &primary_hashtable[hmask];
    }
    //Should decrement CLOCK reference?

    before = _hashitem_before(key, nkey, start);

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
    //Problably ok to not care about expansion
    //  as it will only increase a clock val
    inc_clock(hmask);

    //Bump item in hash bucket
    //This may cause significant loss in performance
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
        if(dec_clock(hand) == 0 && primary_hashtable[hand] != NULL) {

            if ((hold_lock = item_trylock(hand)) == NULL)
                continue; //If we can't get lock immedeatly, search for next bucket

            //Pop off entire bucket
            head = primary_hashtable[hand];
            primary_hashtable[hand] = NULL;

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



//Hash table expasion check
void assoc_start_expand(uint64_t curr_items) {
    if (pthread_mutex_trylock(&maintenance_lock) == 0) {
        if (curr_items > (hashsize(hashpower) * 3) / 2 && hashpower < HASHPOWER_MAX) {
            pthread_cond_signal(&maintenance_cond);
        }
        pthread_mutex_unlock(&maintenance_lock);
    }
}


static void assoc_expand(void) {
    old_hashtable = primary_hashtable;
    old_clock_val = clock_val;

    primary_hashtable = calloc(hashsize(hashpower + 1), sizeof(void *));
    clock_val = calloc(hashsize(hashpower + 1), sizeof(CLOCK_TYPE));

    if (primary_hashtable && clock_val) {
        //Copy CLOCK values
        memcpy(clock_val, old_clock_val, hashsize(hashpower));
        memcpy(clock_val + hashsize(hashpower), old_clock_val, hashsize(hashpower));

        if (settings.verbose >= 1)
            fprintf(stderr, "Hash table expansion starting\n");
        hashpower++;
        expanding = true;
        expand_bucket = 0;
        STATS_LOCK();
        stats_state.hash_power_level = hashpower;
        stats_state.hash_bytes += hashsize(hashpower) * sizeof(void *);
        stats_state.hash_is_expanding = true;
        STATS_UNLOCK();
    } else {
        primary_hashtable = old_hashtable;
        clock_val = old_clock_val;
        /* Bad news, but we can keep running. */
    }
}


#define DEFAULT_HASH_BULK_MOVE 1
int hash_bulk_move = DEFAULT_HASH_BULK_MOVE;

static void *assoc_maintenance_thread(void *arg) {
    mutex_lock(&maintenance_lock);
    while (true) {
        int ii = 0;

        /* There is only one expansion thread, so no need to global lock. */
        for (ii = 0; ii < hash_bulk_move && expanding; ++ii) {
            item *it, *next;
            uint64_t bucket;
            void *item_lock = NULL;

            /* bucket = hv & hashmask(hashpower) =>the bucket of hash table
             * is the lowest N bits of the hv, and the bucket of item_locks is
             *  also the lowest M bits of hv, and N is greater than M.
             *  So we can process expanding with only one item_lock. cool! */
            if ((item_lock = item_trylock(expand_bucket))) {
                    for (it = old_hashtable[expand_bucket]; NULL != it; it = next) {
                        next = it->next;
                        bucket = hash(ITEM_key(it), it->nkey) & hashmask(hashpower);
                        it->next = primary_hashtable[bucket];
                        primary_hashtable[bucket] = it;
                    }

                    old_hashtable[expand_bucket] = NULL;

                    expand_bucket++;
                    if (expand_bucket == hashsize(hashpower - 1)) {
                        expanding = false;
                        free(old_hashtable);
                        STATS_LOCK();
                        stats_state.hash_bytes -= hashsize(hashpower - 1) * sizeof(void *);
                        stats_state.hash_is_expanding = false;
                        STATS_UNLOCK();
                        if (settings.verbose >= 1)
                            fprintf(stderr, "Hash table expansion done\n");
                    }

            } else {
                usleep(10*1000);
            }

            if (item_lock) {
                item_trylock_unlock(item_lock);
                item_lock = NULL;
            }
        }

        if (!expanding) {
            /* We are done expanding.. just wait for next invocation */
            pthread_cond_wait(&maintenance_cond, &maintenance_lock);
            /* assoc_expand() swaps out the hash table entirely, so we need
             * all threads to not hold any references related to the hash
             * table while this happens.
             * This is instead of a more complex, possibly slower algorithm to
             * allow dynamic hash table expansion without causing significant
             * wait times.
             */
            pause_threads(PAUSE_ALL_THREADS);
            assoc_expand();
            pause_threads(RESUME_ALL_THREADS);
        }
    }
    mutex_unlock(&maintenance_lock);
    return NULL;
}


static pthread_t maintenance_tid;
int start_assoc_maintenance_thread(void) {
    int ret;
    char *env = getenv("MEMCACHED_HASH_BULK_MOVE");
    if (env != NULL) {
        hash_bulk_move = atoi(env);
        if (hash_bulk_move == 0) {
            hash_bulk_move = DEFAULT_HASH_BULK_MOVE;
        }
    }

    if ((ret = pthread_create(&maintenance_tid, NULL,
                              assoc_maintenance_thread, NULL)) != 0) {
        fprintf(stderr, "Can't create thread: %s\n", strerror(ret));
        return -1;
    }
    thread_setname(maintenance_tid, "mc-assocmaint");
    return 0;
}
