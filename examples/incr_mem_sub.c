unsigned long int incr(unsigned long int *i)
/*@ requires take iStart = Owned(i) @*/
/*@ requires iStart < power(2,64) - 1 @*/
/*@ ensures take iEnd = Owned(i) @*/
/*@ ensures iEnd == iStart + 1 @*/
/*@ ensures return == iEnd @*/
{
    *i = *i + 1;
    return *i;
}

int main(void)
/*@ ensures return == 0 @*/
{
    unsigned long int i = 1;
    unsigned long int j = incr(&i);
    return i - j;
}