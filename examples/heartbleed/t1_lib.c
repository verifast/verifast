#include "openssl.h"

int
tls1_process_heartbeat(SSL *s)
	//@ requires SSL(s);
	//@ ensures SSL(s);
{
	unsigned char *p = s->s3->rrec.data;
	unsigned char *pl;
	unsigned short hbtype;
	unsigned int payload;
	unsigned int padding = 16;

	hbtype = *p; p++;
	n2s(p, payload);
	if (payload + 19UL > s->s3->rrec.length)
	    return 0;
	pl = p;

	if ((unsigned)hbtype == TLS1_HB_REQUEST)
	{
		unsigned char *buffer;
		unsigned char *bp;
		int r;

		buffer = OPENSSL_malloc(1u + 2u + payload + padding);
		bp = buffer;
		
		*bp = TLS1_HB_RESPONSE; bp++;
		s2n(bp, payload);
		memcpy(bp, pl, payload);
		bp += (int)payload;
		RAND_pseudo_bytes(bp, padding);

		r = ssl3_write_bytes(s, TLS1_RT_HEARTBEAT, buffer, 3 + payload + padding);

		OPENSSL_free(buffer);

		if (r < 0)
			return r;
	}

	return 0;
}
