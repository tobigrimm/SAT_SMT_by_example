// copypasted from http://blog.regehr.org/archives/1063
uint32_t rotl32b (uint32_t x, uint32_t n)
{
	        assert (n<32);
		        if (!n) return x;
			        return (x<<n) | (x>>(32-n));
}

uint32_t rotr32b (uint32_t x, uint32_t n)
{
	        assert (n<32);
		        if (!n) return x;
			        return (x>>n) | (x<<(32-n));
}

void megahash (uint32_t buf[4])
{
	for (int i=0; i<4; i++)
	{
		uint32_t t0=buf[0]^0x12345678^buf[1];
		uint32_t t1=buf[1]^0xabcdef01^buf[2];
		uint32_t t2=buf[2]^0x23456789^buf[3];
		uint32_t t3=buf[3]^0x0abcdef0^buf[0];

		buf[0]=rotl32b(t0, 1);
		buf[1]=rotr32b(t1, 2);
		buf[2]=rotl32b(t2, 3);
		buf[3]=rotr32b(t3, 4);
	};
};

int main()
{
	uint32_t buf[4];
	klee_make_symbolic(buf, sizeof buf);
	megahash (buf);
	if (buf[0]==0x18f71ce6		// or whatever
		&& buf[1]==0xf37c2fc9
		&& buf[2]==0x1cfe96fe
		&& buf[3]==0x8c02c75e)
		klee_assert(0);
};

