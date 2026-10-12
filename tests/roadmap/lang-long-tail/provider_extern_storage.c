/* The external definitions that extern_storage.zig declares (L12): the native counterpart of
 * the `ext : ExternInit` that ModelExternStorage.lean passes to `mem0`. */
#include <stdint.h>

struct Node {
    uint32_t v;
    struct Node *next;
};

static struct Node n2 = {7, 0};
static struct Node n1 = {5, &n2};
static uint32_t slot_target = 9;

uint32_t ext_counter = 41;
struct Node *ext_head = &n1;
const char *const ext_name = "provider";
uint32_t *ext_slot = &slot_target;
