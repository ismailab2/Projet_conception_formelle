#include "limits.h"

/*@
  axiomatic CountVal {
    logic integer count_val(int *src, integer lo, integer hi, int val);

    axiom count_val_empty :
      \forall int *src, integer lo, hi, int val;
      lo >= hi ==> count_val(src, lo, hi, val) == 0;

    axiom count_val_hit :
      \forall int *src, integer lo, hi, int val;
      lo < hi && src[hi-1] == val ==>
      count_val(src, lo, hi, val) == count_val(src, lo, hi-1, val) + 1;

    axiom count_val_miss :
      \forall int *src, integer lo, hi, int val;
      lo < hi && src[hi-1] != val ==>
      count_val(src, lo, hi, val) == count_val(src, lo, hi-1, val);
  }
*/

/*@
  requires \valid_read(src + (0..size-1));
  requires \valid(target + (0..size-1));
  requires \separated(src + (0..size-1), target + (0..size-1));
  
  // to avoid overflow of count
  requires count_val(src, 0, size, val) <= UINT_MAX;

  // to avoid overflow of target[pos] *= 2
  requires val <= INT_MAX / 2;
  requires val >= INT_MIN / 2;
  
  assigns target[0..size-1];

  ensures \forall integer i; 0 <= i < size ==>
      \old(src[i]) == val ==> target[i] == 2 * val;

  ensures \forall integer i; 0 <= i < size ==>
      \old(src[i]) != val ==> target[i] == \old(src[i]);

  ensures \result == count_val(src, 0, size, val);
*/


unsigned int mul_val_modif(int *src, int *target,
                           unsigned int size, int val)
{
    unsigned int pos = 0;
    unsigned int count = 0;

     /*@ loop invariant I1: 0 <= pos <= size;
        loop invariant I2: \forall integer j; 0 <= j < pos ==>
            src[j] == val ==> target[j] == 2*val;
        loop invariant I3: \forall integer j; 0 <= j < pos ==>
            src[j] != val ==> target[j] == src[j];
        loop invariant I4: count == count_val(src, 0, pos, val);
        loop invariant count <= UINT_MAX;
        loop assigns pos, count, target[0..size-1];
        loop variant size - pos;
    */
    while (pos < size)
    {
        target[pos] = src[pos];
        if (target[pos] == val)
        {
            target[pos] *= 2;
            count++;
        }
        pos++;
    }
    return count;
}