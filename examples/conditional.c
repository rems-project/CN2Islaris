unsigned long int incr_twice_neq_zero(unsigned long int i)
/*@ requires i < power(2,64) - 2 @*/
/*@ ensures return == ((i == 0) ? i + 1 : i + 2) @*/
{
    if (i == 0) {
        i = i + 1;
    } else {
        i = i + 2;
    }
    return i;
}