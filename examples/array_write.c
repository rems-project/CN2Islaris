void write1(unsigned long int *pair_p, unsigned long int value)
/*@ requires take pairStart = each (integer j; 0 <= j && j < 2) {Owned(pair_p + (j * sizeof<unsigned long int>))} @*/
/*@ ensures take pairEnd = each (integer j; 0 <= j && j < 2) {Owned(pair_p + (j * sizeof<unsigned long int>))} @*/
/*@ ensures pairEnd[1] == value @*/
{
    /*@ extract Owned<unsigned long int>, 1; @*/
    /*@ instantiate good<unsigned long int>, 1; @*/
    pair_p[1] = value;
}