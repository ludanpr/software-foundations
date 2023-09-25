#include <stddef.h>

struct list {
    unsigned head;
    struct list *tail;
};

struct list three[] = {
    { 1, three + 1},
    { 2, three + 2},
    { 3, NULL },
};

unsigned sumlist(struct list *p)
{
    unsigned s = 0;
    struct list *t = p;

    unsigned h;
    while (t) {
        h = t->head;
        t = t->tail;
        s = s + h;
    }

    return s;
}

struct list *reverse(struct list *p)
{
    struct list *w = NULL;
    struct list *v = p;
    struct list *t;

    while (v) {
        t = v->tail;
        v->tail = w;
        w = v;
        v = t;
    }

    return w;
}


int main (void)
{
    struct list *r = reverse(three);
    unsigned s = sumlist(r);

    return (int) s;
}

