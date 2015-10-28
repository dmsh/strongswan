/*
 * Copyright (C) 2015 Andreas Steffen
 * HSR Hochschule fuer Technik Rapperswil
 *
 * Based on the implementation by the Keccak, Keyak and Ketje Teams, namely,
 * Guido Bertoni, Joan Daemen, Michaël Peeters, Gilles Van Assche and
 * Ronny Van Keer, hereby denoted as "the implementer".
 *
 * To the extent possible under law, the implementer has waived all copyright
 * and related or neighboring rights to the source code in this file.
 * http://creativecommons.org/publicdomain/zero/1.0/
 */

#include <string.h>

#include "sha3_hasher.h"

typedef struct private_sha3_hasher_t private_sha3_hasher_t;

#define KECCAK_STATE_SIZE	 200	/* bytes */
#define DELIMITED_SUFFIX	0x06

static const uint8_t rotation_constants[] = {
	 1,  3,  6, 10, 15, 21, 28, 36, 45, 55,  2, 14,
	27, 41, 56,  8, 25, 43, 62, 18, 39, 61, 20, 44
};

static const uint8_t pi_lane[] = {
	10,  7, 11, 17, 18,  3,  5, 16,  8, 21, 24,  4,
	15, 23, 19, 13, 12,  2, 20, 14, 22,  9,  6,  1
};

/**
 * Private data structure with hashing context for SHA-3
 */
struct private_sha3_hasher_t {

	/**
	 * Public interface for this hasher.
	 */
	sha3_hasher_t public;

	/**
	 * SHA-3 algorithm to be used
	 */
	hash_algorithm_t algorithm;

	/**
	 * Internal state of 1600 bits as defined by FIPS-202
	 */
	uint8_t state[KECCAK_STATE_SIZE];

	/**
	 * Rate in bytes
	 */
	u_int rate;

	/**
	 * Index pointing to the current position in the rate buffer
	 */
	u_int rate_index;

};

#if BYTE_ORDER != LITTLE_ENDIAN
/**
 * Function to load a 64-bit value using the little-endian (LE) convention.
 * On a LE platform, this could be greatly simplified using a cast.
 */
static uint64_t load64(const uint8_t *x)
{
	int i;
	uint64_t u = 0;

	for (i = 7; i >= 0; --i)
	{
		u <<= 8;
		u |= x[i];
	}
	return u;
}

/**
 * Function to store a 64-bit value using the little-endian (LE) convention.
 * On a LE platform, this could be greatly simplified using a cast.
 */
static void store64(uint8_t *x, uint64_t u)
{
	u_int i;

	for (i = 0; i < 8; ++i)
	{
		x[i] = u;
		u >>= 8;
	}
}

/**
 * Function to XOR into a 64-bit value using the little-endian (LE) convention.
 * On a LE platform, this could be greatly simplified using a cast.
 */
static void xor64(uint8_t *x, uint64_t u)
{
	u_int i;

	for (i = 0; i < 8; ++i)
	{
		x[i] ^= u;
		u >>= 8;
	}
}
#endif

/**
 * A readable and compact implementation of the Keccak-f[1600] permutation.
 */

#define ROL64(a, offset) ((((uint64_t)a) << offset) ^ (((uint64_t)a) >> (64-offset)))

#if BYTE_ORDER == LITTLE_ENDIAN
    #define readLane(i)          (((uint64_t*)state)[i])
    #define writeLane(i, lane)   (((uint64_t*)state)[i])  = (lane)
    #define XORLane(i, lane)     (((uint64_t*)state)[i]) ^= (lane)
#elif BYTE_ORDER == BIG_ENDIAN
    #define readLane(i)          load64((uint8_t*)state+sizeof(uint64_t)*i))
    #define writeLane(i, lane)   store64((uint8_t*)state+sizeof(uint64_t)*i, lane)
    #define XORLane(i, lane)     xor64((uint8_t*)state+sizeof(uint64_t)*i, lane)
#endif

/**
 * Function that computes the linear feedback shift register (lfsr) used to
 * define the round constants (see [Keccak Reference, Section 1.2]).
 */
static int lfsr_86540(uint8_t *lfsr)
{
	int result = ((*lfsr) & 0x01) != 0;

	if (((*lfsr) & 0x80) != 0)
	{
		/* Primitive polynomial over GF(2): x^8+x^6+x^5+x^4+1 */
		(*lfsr) = ((*lfsr) << 1) ^ 0x71;
	}
	else
	{
		(*lfsr) <<= 1;
	}
	return result;
}

/**
 * Function that computes the Keccak-f[1600] permutation on the given state.
 */
static void keccak_f1600_state_permute(void *state)
{
	u_int round, x, y, i, j, k, t;
	uint8_t lfsrstate = 0x01;

	for (round = 0; round < 24; round++)
	{
		{   /* θ step (see [Keccak Reference, Section 2.3.2]) */
			uint64_t C[5], D;

			/* Compute the parity of the columns */
			for (x = 0; x < 5; x++)
			{
				C[x] = readLane(x) ^ readLane(x +  5) ^ readLane(x + 10)
					               ^ readLane(x + 15) ^ readLane(x + 20);
			}
			for (x = 0; x < 5; x++) 
			{
				/* Compute the θ effect for a given column */
				j = (x == 0) ? 4 : x - 1;
				k = (x == 4) ? 0 : x + 1;
				D = C[j] ^ ROL64(C[k], 1);

				/* Add the θ effect to the whole column */
				for (y = 0; y < 25; y += 5)
				{
					XORLane(x + y, D);
				}
			}
		}

		{   /* ρ and π steps (see [Keccak Reference, Sections 2.3.3 and 2.3.4]) */
			uint64_t temp;
			uint64_t current = readLane(1);

			for (t = 0; t < 24; t++)
			{
				/* Swap current lane and state[pi_lane[t]], and rotate */
				temp = readLane(pi_lane[t]);
				writeLane(pi_lane[t], ROL64(current, rotation_constants[t]));
				current = temp;
			}
		}

		{   /* χ step (see [Keccak Reference, Section 2.3.1]) */
			uint64_t temp[5];

			for (y = 0; y < 5; y++)
			{
				i = 5 * y;

				/* Take a copy of the plane */
				for (x = 0; x < 5; x++)
				{
					temp[x] = readLane(i + x);
				}

				/* Compute χ on the plane */
				for (x = 0; x < 5; x++)
				{
					j = (x == 4) ? 0 : x + 1;
					k = (x >= 3) ? x - 3 : x + 2;
					writeLane(i + x, temp[x] ^((~temp[j]) & temp[k]));
				}
			}
		}

		{   /* ι step (see [Keccak Reference, Section 2.3.5]) */
			u_int bitPosition;

			for (j = 0; j < 7; j++)
			{
				bitPosition = (1 << j) - 1; /* 2^j-1 */

				if (lfsr_86540(&lfsrstate))
				{
					XORLane(0, (uint64_t)1 << bitPosition);
				}
			}
		}
	}
}

METHOD(hasher_t, reset, bool,
	private_sha3_hasher_t *this)
{
    memset(this->state, 0x00, KECCAK_STATE_SIZE);
	this->rate_index = 0;

	return TRUE;
}

METHOD(hasher_t, get_hash_size, size_t,
	private_sha3_hasher_t *this)
{
	switch (this->algorithm)
	{
		case HASH_SHA3_224:
			return HASH_SIZE_SHA224;
		case HASH_SHA3_256:
			return HASH_SIZE_SHA256;
		case HASH_SHA3_384:
			return HASH_SIZE_SHA384;
		case HASH_SHA3_512:
			return HASH_SIZE_SHA512;
		default:
			return 0;
	}
}

static void sha3_absorb(private_sha3_hasher_t *this, chunk_t data)
{
	while (data.len--)
	{
		this->state[this->rate_index++] ^= *data.ptr++;

		if (this->rate_index == this->rate)
		{
			keccak_f1600_state_permute(this->state);
			this->rate_index = 0;
		}
	}
}

static void sha3_final(private_sha3_hasher_t *this)
{
	/* Add the delimitedSuffix as the first bit of padding */
	this->state[this->rate_index] ^= DELIMITED_SUFFIX;

	/* Add the second bit of padding */
	this->state[this->rate - 1] ^= 0x80;

	/* Switch to the squeezing phase */
	keccak_f1600_state_permute(this->state);
}

METHOD(hasher_t, get_hash, bool,
	private_sha3_hasher_t *this, chunk_t chunk, uint8_t *buffer)
{
	sha3_absorb(this, chunk);

	if (buffer != NULL)
	{
		sha3_final(this);
		memcpy(buffer, this->state, get_hash_size(this));
		reset(this);
	}
	return TRUE;
}

METHOD(hasher_t, allocate_hash, bool,
	private_sha3_hasher_t *this, chunk_t chunk, chunk_t *hash)
{
	chunk_t allocated_hash;

	sha3_absorb(this, chunk);

	if (hash != NULL)
	{
		sha3_final(this);
		allocated_hash = chunk_alloc(get_hash_size(this));
		memcpy(allocated_hash.ptr, this->state, allocated_hash.len);
		reset(this);
		*hash = allocated_hash;
	}
	return TRUE;
}

METHOD(hasher_t, destroy, void,
	sha3_hasher_t *this)
{
	free(this);
}

/*
 * Described in header.
 */
sha3_hasher_t *sha3_hasher_create(hash_algorithm_t algorithm)
{
	private_sha3_hasher_t *this;

	switch (algorithm)
	{
		case HASH_SHA3_224:
		case HASH_SHA3_256:
		case HASH_SHA3_384:
		case HASH_SHA3_512:
			break;
		default:
			return NULL;
	}

	INIT(this,
		.public = {
			.hasher_interface = {
			.reset = _reset,
			.get_hash_size = _get_hash_size,
			.get_hash = _get_hash,
			.allocate_hash = _allocate_hash,
			.destroy = _destroy,
			},
		},
		.algorithm = algorithm,
	);

	this->rate = KECCAK_STATE_SIZE - 2*get_hash_size(this);
	reset(this);

	return &this->public;
}
