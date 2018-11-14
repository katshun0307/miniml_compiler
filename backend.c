#include <stdio.h>
#include <stdlib.h>

typedef struct closure
{
    int (*f)(struct closure *, const int);
    int *vars;
    int length;
} closure;
