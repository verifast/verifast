#define DEF_ZERO 0
#define DEF_ONE 1

#if DEF_ZERO + DEF_ONE << 2 == 4
#define DEF_OK
#else
#error ERROR
#endif

#if 18446744073709551615U != 18446744073709551615UL
  #error ERROR
#endif

#if 18446744073709551615U - 1 != 18446744073709551614U
  #error ERROR
#endif

#if -9223372036854775807 - 1 >= -9223372036854775807
  #error ERROR
#endif

#if 3 * 7 != 21
  #error ERROR
#endif

#if -1 * 1U != 18446744073709551615U
  #error ERROR
#endif

#if 1U * -1 != 18446744073709551615U
  #error ERROR
#endif

#if -20 / 7 != -2
  #error ERROR
#endif

#if 20 % 7 != 6
  #error ERROR
#endif

#if 20 % -7 != 6
  #error ERROR
#endif

#if -20 % 7 != -6
  #error ERROR
#endif

#if -20 % -7 != -6
  #error ERROR
#endif

#if -2147483647 + -2147483647 != -4294967294
  #error ERROR
#endif

#if 1 << 62 != 4611686018427387904
  #error ERROR
#endif

#if 4611686018427387904 >> 61 != 2
  #error ERROR
#endif

#if -1 >> 62 != -1
  #error ERROR
#endif

#if -4611686018427387904 >> 61 != -2
  #error ERROR
#endif

#if !(1U < -1)
  #error ERROR
#endif

#if !(-1 > 1U)
  #error ERROR
#endif

#if 3 < 1
  #error ERROR
#endif

#if 3 == 1
  #error ERROR
#endif

#if 3 <= 1
  #error ERROR
#endif

#if 3 > 3
  #error ERROR
#endif

#if 1 >= 3
  #error ERROR
#endif

#if (0xf0f0f0f0f0f0f0f0U & 0x123456789ABCDEF0) != 0x1030507090B0D0F0
  #error ERROR
#endif

#if (0xf0f0f0f0f0f0f0f0U | 0x123456789ABCDEF0) != 0xf2f4f6f8fAfCfEf0U
  #error ERROR
#endif

#if (0xf0f0f0f0f0f0f0f0U ^ 0xff00ff00ff00ff00U) != 0x0ff00ff00ff00ff0
  #error ERROR
#endif

#if ((-9223372036854775807 - 1) | 0) != (-9223372036854775807 - 1)
  #error ERROR
#endif

#if (1 && 0) != 0
  #error ERROR
#endif

#if (0 && 1) != 0
  #error ERROR
#endif

#if (0 && 0) != 0
  #error ERROR
#endif

#if (1 && 1) != 1
  #error ERROR
#endif

#if (0 || 0) != 0
  #error ERROR
#endif

#if (0 || 1) != 1
  #error ERROR
#endif

#if (1 || 0) != 1
  #error ERROR
#endif

#if (1 || 1) != 1
  #error ERROR
#endif

#if (!0) != 1
  #error ERROR
#endif
