#include "limits.h"

/*@ //TODO : compléter
    ensures \forall integer i; 0 <= i < size ==> \old(src[i] == val) ==> target[i] == 2*val;
*/
void mul_val(int *src, int *target, unsigned int size, int val)
{
    unsigned int pos = 0;
    while (pos < size)
    {
        target[pos] = src[pos];
        if (target[pos] == val)
        {
            target[pos] *= 2;
        }
        pos++;
    }
    return;
}