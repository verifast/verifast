#undef __NOT_DEFINED_MACRO__

#if __NOT_DEFINED_MACRO__ == 0
#define DEF_OK
#else
#error ERROR
#endif
