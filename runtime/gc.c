#include <stdlib.h>

#define STACK_SIZE (4 * 1024)

typedef char* value;

struct gc
{
    /* The call stack, which grows downwards */
    value* stack;
    /* The pointer to the top of the stack */
    value* sp;
    /* The pointer to the bottom of the current frame */
    value* fp;
};

_Thread_local struct gc gc;

void gc_init()
{
    gc.stack = malloc(STACK_SIZE);
    gc.sp = gc.stack + STACK_SIZE;
    gc.fp = gc.stack + STACK_SIZE;
}

void gc_destroy()
{
    free(gc.stack);
}

char* gc_alloca()
{
    if(gc.sp < gc.stack) {
        /* Stack overflow, return NULL */
        return 0;
    }
    /* Initialize stack slot to 0 */
    *gc.sp = 0;
    return *(gc.sp--);
}

char* gc_malloc(int size)
{
    return 0;
}

void gc_push_frame()
{
    /* The bottom of the new frame */
    value* new_frame = gc.sp--;
    /* Store the old frame pointer at the bottom of the new frame */
    *new_frame = (value) gc.fp;
    /* Update the frame pointer to point to the bottom of the new frame */
    gc.fp = new_frame;
}

void gc_pop_frame()
{
    /* Point the stack pointer to the current frame pointer */
    gc.sp = gc.fp;
    /* Point the frame pointer to the old frame pointer, located at the bottom
       of the frame */
    gc.fp = (value*) *gc.fp;
}
