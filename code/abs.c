#include <limits.h>

/*@ terminates \true;
    //ensures TODO;
 */
int abs(int n)
{
    int res = n;
    if (n < 0)
        res = -n;
    return res;
}

/*@ terminates \true;
    //ensures  TODO;*/
int abs2(int n)
{
    int aux = n % 2 + (n + 1) % 2;
    return n * aux;
}