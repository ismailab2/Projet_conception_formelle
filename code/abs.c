#include <limits.h>

/*@ requires n > INT_MIN;
    terminates \true;
    ensures \result >= 0;
    ensures (\result == -n ||  \result == n);
    assigns \nothing;
 */
int abs(int n)
{
    int res = n;
    if (n < 0)
        res = -n;
    return res;
}

/*@ requires n > INT_MIN;
    requires n < INT_MAX;   
    terminates \true;
    ensures \result >= 0;
    ensures (\result == -n ||  \result == n);
    assigns \nothing;
*/
int abs2(int n)
{
    int aux = n % 2 + (n + 1) % 2;
    return n * aux;
}