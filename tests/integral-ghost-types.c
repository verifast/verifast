/*
 * In ghostcode, all integral types are types of each other.
 * You can still write the C types and typedefs (e.g. size_t) for practical readability.
 */
/*@
predicate accept_char(char c;) = true;
predicate accept_unsigned_char(unsigned char c;) = true;
predicate accept_short(short c;) = true;
predicate accept_unsigned_short(unsigned short c;) = true;
predicate accept_int(int c;) = true;
predicate accept_unsigned_int(unsigned int c;) = true;

lemma void test()
requires true;
ensures true;
{
	int si = -8589934592;
	unsigned int ui = si;
	char sc = si;
	unsigned char uc = si;
	short ss = si;
	unsigned short us = si;
	
	
	close accept_char(si);
	close accept_char(ui);
	close accept_char(uc);
	close accept_char(ss);
	close accept_char(us);

	close accept_unsigned_char(si);
	close accept_unsigned_char(ui);
	close accept_unsigned_char(uc);
	close accept_unsigned_char(ss);
	close accept_unsigned_char(us);

	close accept_short(si);
	close accept_short(ui);
	close accept_short(uc);
	close accept_short(ss);
	close accept_short(us);

	close accept_unsigned_short(si);
	close accept_unsigned_short(ui);
	close accept_unsigned_short(uc);
	close accept_unsigned_short(ss);
	close accept_unsigned_short(us);

	close accept_int(si);
	close accept_int(ui);
	close accept_int(uc);
	close accept_int(ss);
	close accept_int(us);

	close accept_unsigned_int(si);
	close accept_unsigned_int(ui);
	close accept_unsigned_int(uc);
	close accept_unsigned_int(ss);
	close accept_unsigned_int(us);
	
	assert 1 * (si + ui + sc + uc + ss + us) * ui * sc * uc * ss * us == 2410407066388485413312943138511743903783304490674189252952064;
}

fixpoint int myfp();
fixpoint unsigned int myfpu();
lemma void test2()
requires myfp() == myfpu();
ensures myfp() < myfpu() + 1;
{
}
@*/