void megahash (uint32_t buf[4])
{
	for (int i=0; i<16; i++)
	{
		uint32_t t0=buf[0]^0x12345678^buf[1];
		uint32_t t1=buf[1]^0xabcdef01^buf[2];
		uint32_t t2=buf[2]^0x23456789^buf[3];
		uint32_t t3=buf[3]^0x0abcdef0^buf[0];

		buf[0]=rotl32b(t0, t1&0x1F);
		buf[1]=rotr32b(t1, t2&0x1F);
		buf[2]=rotl32b(t2, t3&0x1F);
		buf[3]=rotr32b(t3, t0&0x1F);
	};
};

