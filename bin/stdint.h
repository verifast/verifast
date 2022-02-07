#ifndef STDINT_H
#define STDINT_H

#ifdef __VF_CXX_CLANG_FRONTEND__

typedef __UINT8_TYPE__   uint8_t;
typedef __UINT16_TYPE__  uint16_t;
typedef __UINT32_TYPE__  uint32_t;
typedef __UINT64_TYPE__  uint64_t;

typedef __INT8_TYPE__   int8_t;
typedef __INT16_TYPE__  int16_t;
typedef __INT32_TYPE__  int32_t;
typedef __INT64_TYPE__  int64_t;

#else

typedef __int8   int8_t;
typedef __int16  int16_t;
typedef __int32  int32_t;
typedef __int64  int64_t;
typedef __int128 int128_t;

typedef unsigned __int8   uint8_t;
typedef unsigned __int16  uint16_t;
typedef unsigned __int32  uint32_t;
typedef unsigned __int64  uint64_t;
typedef unsigned __int128 uint128_t;

#endif

#define INT8_MIN (-127 - 1)
#define INT8_MAX 127
#define INT16_MIN (-32767 - 1)
#define INT16_MAX 32767
#define INT32_MIN (-2147483647 - 1)
#define INT32_MAX 2147483647
#define INT64_MIN (-9223372036854775807 - 1)
#define INT64_MAX 9223372036854775807
#define INT128_MIN (-170141183460469231731687303715884105727 - 1)
#define INT128_MAX 170141183460469231731687303715884105727

#define UINT8_MAX 255
#define UINT16_MAX 65535
#define UINT32_MAX 4294967295
#define UINT64_MAX 18446744073709551615
#define UINT128_MAX 340282366920938463463374607431768211455

#define SIZE_MAX UINTPTR_MAX

#endif // STDINT_H
