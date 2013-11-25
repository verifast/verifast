#include <stdio.h>

struct s0{
	char c;
};

struct s1{
	struct s0 v1;
	struct s0 v2;
};
struct s2{
	struct s1 v1;
	struct s1 v2;
};
struct s3{
	struct s2 v1;
	struct s2 v2;
};
struct s4{
	struct s3 v1;
	struct s3 v2;
};
struct s5{
	struct s4 v1;
	struct s4 v2;
};
struct s6{
	struct s5 v1;
	struct s5 v2;
};
struct s7{
	struct s6 v1;
	struct s6 v2;
};
struct s8{
	struct s7 v1;
	struct s7 v2;
};
struct s9{
	struct s8 v1;
	struct s8 v2;
};
struct s10{
	struct s9 v1;
	struct s9 v2;
};
struct s11{
	struct s10 v1;
	struct s10 v2;
};
struct s12{
	struct s11 v1;
	struct s11 v2;
};
struct s13{
	struct s12 v1;
	struct s12 v2;
};
struct s14{
	struct s13 v1;
	struct s13 v2;
};
struct s15{
	struct s14 v1;
	struct s14 v2;
};
struct s16{
	struct s15 v1;
	struct s15 v2;
};
struct s17{
	struct s16 v1;
	struct s16 v2;
};
struct s18{
	struct s17 v1;
	struct s17 v2;
};
struct s19{
	struct s18 v1;
	struct s18 v2;
};
struct s20{
	struct s19 v1;
	struct s19 v2;
};
struct s21{
	struct s20 v1;
	struct s20 v2;
};
struct s22{
	struct s21 v1;
	struct s21 v2;
};
struct s23{
	struct s22 v1;
	struct s22 v2;
};
struct s24{
	struct s23 v1;
	struct s23 v2;
};
struct s25{
	struct s24 v1;
	struct s24 v2;
};
struct s26{
	struct s25 v1;
	struct s25 v2;
};
struct s27{
	struct s26 v1;
	struct s26 v2;
};
struct s28{
	struct s27 v1;
	struct s27 v2;
};
struct s29{
	struct s28 v1;
	struct s28 v2;
};
struct s30{
	struct s29 v1;
	struct s29 v2;
};

struct two_and_a_half_gb{
	struct s30 one_gb;
	struct s30 another_gb;
	struct s29 half_gb;
};

int main() //@ : main
//@ requires true;
//@ ensures true;
{
	int x = sizeof(struct two_and_a_half_gb); //~ should-fail
	if (x < 0){
		// When ignoring signedness or typing sizeof wrongly,
		// VeriFast would allow this program while the program crashes.
		int *evil = 0;
		*evil = 0;
	}
	return 0;
}
