/* associative array */
void assoc_init(const int hashpower_init);

item *assoc_find(const char *key, const size_t nkey, const uint32_t hv);
int assoc_insert(item *item, const uint32_t hv);
item *assoc_delete(const char *key, const size_t nkey, const uint32_t hv);
void assoc_bump(item *it, const uint32_t hv);

int try_evict(const int orig_id, const uint64_t total_bytes, const rel_time_t max_age);

extern unsigned int hashpower;

void assoc_start_expand(uint64_t curr_items);
int start_assoc_maintenance_thread(void);
