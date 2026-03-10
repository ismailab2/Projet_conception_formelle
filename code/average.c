#include "limits.h"

/*@ ensures \result == (a+b)/2;*/
unsigned int average(unsigned int a, unsigned int b){
    unsigned int qa = a/2;
    unsigned int qb = b/2;
    unsigned int ra = a%2;
    unsigned int rb = b%2;
    return qa + qb + (ra+rb)/2;
}