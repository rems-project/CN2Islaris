unsigned long int incr(unsigned long int i)
/*@ requires i < power(2,64) - 1 @*/
/*@ ensures return == i + 1 @*/
{
    i = i + 1;
    return i;
}

int main(void)
/*@ ensures return == 1 @*/
{
    unsigned long int i = 0;
    return incr(i);
}