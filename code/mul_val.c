#include "limits.h"

/*@ //TODO : compléter
    requires \valid(src + (0 .. size-1));
    requires \valid(target + (0 .. size-1));
    requires val < INT_MAX;
    requires val > INT_MAX;
    requires \separated(src + (0 .. size-1), target + (0 .. size-1));
    assigns target[0 .. size-1];
    //ensures \forall integer i; 0 <= i < size ==> \old(src[i] == val) ==> target[i] == 2*val;
    ensures \forall integer i; 0 <= i < size ==> (src[i] == val ? target[i] == 2*val : target[i] == src[i]);
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