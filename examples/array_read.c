unsigned long int get1(unsigned long int *pair_p)
/*@ requires take pairStart = each (integer j; 0 <= j && j < 2) {Owned(pair_p + (j * sizeof<unsigned long int>))} @*/
/*@ ensures take pairEnd = each (integer j; 0 <= j && j < 2) {Owned(pair_p + (j * sizeof<unsigned long int>))} @*/
/*@ ensures pairStart == pairEnd @*/
/*@ ensures return == pairEnd[1] @*/
{
    /*@ extract Owned<unsigned long int>, 1; @*/
    /*@ instantiate 1; @*/
    return pair_p[1];
}