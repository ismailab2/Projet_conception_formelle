#include "limits.h"

/*@ requires \valid(src + (0 .. size-1));
    requires \valid(target + (0 .. size-1));
    requires val < INT_MAX;
    requires val > INT_MAX;
    requires \separated(src + (0 .. size-1), target + (0 .. size-1));
    assigns target[0 .. size-1];
    ensures \forall integer i; 0 <= i < size ==> \old(src[i] == val) ==> target[i] == 2*val;
    ensures \forall integer i; 0 <= i < size ==> \old(src[i] != val) ==> target[i] == val;

*/


/**
 * @brief la focntion sert a copié un tableau source vers un tableau cible et double les éléments égaux à val.
 *
 * Parcourt le tableau `src` de longueur `size`. Pour chaque élément :
 *  - Si l'élément vaut `val`, il est copié dans `target` après multiplication par 2.
 *  - Sinon, il est copié tel quel.
 *
 * @param src Pointeur vers le tableau source. Doit être valide sur `size` éléments.
 * @param target Pointeur vers le tableau cible. Doit être valide sur `size` éléments.
 * @param size Nombre d'éléments des tableaux.
 * @param val Valeur à détecter et doubler dans le tableau cible.
 *
 * @pre `src` et `target` doivent etre valides pour `size` éléments.
 * @pre `src` et `target` doivent être séparés (`\separated`) sur leurs zones mémoire.
 *
 * @post Pour tout i appatenant a [0..size-1] :
 *       - Si src[i] == val alors target[i] == 2*val
 *       - Sinon target[i] == src[i]
 *
 * @note Seul le tableau `target` est modifié.
 * @note La fonction se termine toujours.
 */

void mul_val(int *src, int *target, unsigned int size, int val)
{
    unsigned int pos = 0;
    /*@ loop invariant 0 <= pos <= size;
        loop invariant \forall integer i; 0 <= i < pos ==>
            (src[i] == val ? target[i] == 2*val : target[i] == src[i]);
        loop assigns target[0..size-1], pos;
        loop variant size - pos;
    */
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
  requires \valid(src + (0 .. size-1));
  requires \valid(target + (0 .. size-1));
    requires val < INT_MAX;
    requires val > INT_MAX;
    requires \separated(src + (0 .. size-1), target + (0 .. size-1));
    assigns target[0 .. size-1];
    ensures \forall integer i; 0 <= i < size ==> \old(src[i] == val) ==> target[i] == 2*val;
    ensures \forall integer i; 0 <= i < size ==> \old(src[i] != val) ==> target[i] == val;

  ensures \result == count_val(src, 0, size, val);
*/
unsigned int mul_val_modif(int *src, int *target,
                           unsigned int size, int val)
{
    unsigned int pos = 0;
    unsigned int count = 0;

    /*@ loop invariant 0 <= pos <= size;

        loop invariant
          \forall integer j; 0 <= j < pos ==>
            src[j] == val ==> target[j] == 2*val;

        loop invariant
          \forall integer j; 0 <= j < pos ==>
            src[j] != val ==> target[j] == src[j];

        loop invariant
          count == count_val(src, 0, pos, val);

        loop assigns pos, count, target[0..size-1];
        loop variant size - pos;
    */
    while (pos < size)
    {
        target[pos] = src[pos];

        //@ assert target[pos] == src[pos];

        if (target[pos] == val)
        {
            target[pos] *= 2;
            //@ assert count < INT_MAX;
            count++;
        }

        pos++;
    }

    return count;
}