unsigned long int incr(unsigned long int i)
/*@ requires i < power(2,64) - 1 @*/
/*@ ensures return == i + 1 @*/
{
    i = i + 1;
    return i;
}

void decr(unsigned long int *i)
/*@ requires take iStart = Owned(i) @*/
/*@ requires 0 < iStart @*/
/*@ ensures take iEnd = Owned(i) @*/
/*@ ensures iEnd == iStart - 1 @*/
{
    *i = *i - 1;
}

int main(void)
/*@ ensures return == 0 @*/
{
    unsigned long int i = 0;
    i = incr(i);
    decr(&i);
    return i;
}