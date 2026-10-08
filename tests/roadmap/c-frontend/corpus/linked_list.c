/* Singly linked list over a static node pool: push, reverse, remove through a pointer-to-pointer, sum. */
#include <stddef.h>

struct node { unsigned value; struct node *next; };

static struct node pool[8];

static struct node *push(struct node *head, struct node *n, unsigned v) { n->value = v; n->next = head; return n; }

static struct node *reverse(struct node *head) {
    struct node *prev = NULL;
    while (head) { struct node *next = head->next; head->next = prev; prev = head; head = next; }
    return prev;
}

static struct node *remove_if_odd(struct node *head) {
    struct node **link = &head;
    while (*link) {
        if ((*link)->value & 1u) *link = (*link)->next;
        else link = &(*link)->next;
    }
    return head;
}

unsigned entry(unsigned a, unsigned b) {
    struct node *head = NULL;
    for (unsigned i = 0; i < 8; i++) head = push(head, &pool[i], a + i * b);
    head = reverse(head);
    head = remove_if_odd(head);
    unsigned s = 0, k = 1;
    for (struct node *n = head; n != NULL; n = n->next) s += n->value * k++;
    return s;
}
