#include <stdio.h>
#include <stdlib.h>

typedef struct{
    int (*f)(const int*, const int);
    int* vars;
    int length;

} closure;
