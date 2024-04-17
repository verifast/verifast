unsigned long alignmentRest(void const * const pointer, unsigned int const byte_count)
//@ requires byte_count > 0;
//@ ensures result <= byte_count;
{
	unsigned long const p = (unsigned long) pointer;
	//@ div_rem_nonneg(p, byte_count);

	return byte_count - (p % byte_count);
}
