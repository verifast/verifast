#define DEF_ZERO 0
#define DEF_ONE 1

#if DEF_ZERO + DEF_ONE << 2 == 4
#define DEF_OK
#else
#error ERROR
#endif
