/*

Copyright (c) 2008-2016, Arvid Norberg
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:

    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in
      the documentation and/or other materials provided with the distribution.
    * Neither the name of the author nor the names of its
      contributors may be used to endorse or promote products derived
      from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
POSSIBILITY OF SUCH DAMAGE.

*/

#include "libtorrent/bitfield.hpp"
#include "libtorrent/aux_/cpuid.hpp"

#ifdef _MSC_VER
#include <intrin.h>
#endif

namespace libtorrent
{
	bool bitfield::all_set() const
	{
		const int words = size() / 32;
		for (int i = 0; i < words; ++i)
		{
			if (m_buf[i] != 0xffffffff) return false;
		}
		int rest = size() & 31;
		if (rest > 0)
		{
			boost::uint32_t mask = aux::host_to_network(0xffffffff << (32-rest));
			if ((m_buf[words] & mask) != mask) return false;
		}
		return true;
	}

	int bitfield::count() const
	{
		int ret = 0;
		const int words = num_words();
#if TORRENT_HAS_SSE
		if (aux::mmx_support)
		{
			for (int i = 0; i < words; ++i)
			{
#ifdef __GNUC__
				ret += __builtin_popcount(m_buf[i]);
#else
				ret += _mm_popcnt_u32(m_buf[i]);
#endif
			}

			return ret;
		}
#endif // TORRENT_HAS_SSE

		for (int i = 0; i < words; ++i)
		{
			boost::uint32_t const v = m_buf[i];
			// from:
			// http://graphics.stanford.edu/~seander/bithacks.html#CountBitsSetParallel
			static const int S[] = {1, 2, 4, 8, 16}; // Magic Binary Numbers
			static const int B[] = {0x55555555, 0x33333333, 0x0F0F0F0F, 0x00FF00FF, 0x0000FFFF};

			boost::uint32_t c = v - ((v >> 1) & B[0]);
			c = ((c >> S[1]) & B[1]) + (c & B[1]);
			c = ((c >> S[2]) + c) & B[2];
			c = ((c >> S[3]) + c) & B[3];
			c = ((c >> S[4]) + c) & B[4];
			ret += c;
		}

		TORRENT_ASSERT(ret <= size());
		TORRENT_ASSERT(ret >= 0);
		return ret;
	}

	void bitfield::resize(int bits, bool val)
	{
		if (bits == size()) return;

		int s = size();
		int b = size() & 31;
		resize(bits);
		if (s >= size()) return;
		int old_size_words = (s + 31) / 32;
		int new_size_words = num_words();
		if (val)
		{
			if (old_size_words && b) m_buf[old_size_words - 1] |= aux::host_to_network((0xffffffff >> b));
			if (old_size_words < new_size_words)
				std::memset(m_buf + old_size_words, 0xff
					, size_t((new_size_words - old_size_words) * 4));
			clear_trailing_bits();
		}
		else
		{
			if (old_size_words < new_size_words)
				std::memset(m_buf + old_size_words, 0x00
					, size_t((new_size_words - old_size_words) * 4));
		}
		TORRENT_ASSERT(size() == bits);
	}

	void bitfield::resize(int bits)
	{
		if (bits == size()) return;

		TORRENT_ASSERT(bits >= 0);
		const int b = (bits + 31) / 32;
		if (bits == 0)
		{
			if (m_buf != NULL)
			{
				std::free(m_buf-1);
				m_buf = NULL;
			}
			return;
		}

		if (m_buf)
		{
			boost::uint32_t* tmp = static_cast<boost::uint32_t*>(std::realloc(m_buf-1, (b+1) * 4));
#ifndef BOOST_NO_EXCEPTIONS
			if (tmp == NULL) throw std::bad_alloc();
#endif
			m_buf = tmp + 1;
			m_buf[-1] = bits;
		}
		else
		{
			// +1 because the first word is the size (in bits)
			boost::uint32_t* tmp = static_cast<boost::uint32_t*>(std::malloc((b+1) * 4));
#ifndef BOOST_NO_EXCEPTIONS
			if (tmp == NULL) throw std::bad_alloc();
#endif
			m_buf = tmp + 1;
			m_buf[-1] = bits;
		}
		clear_trailing_bits();
		TORRENT_ASSERT(size() == bits);
	}

	int bitfield::find_first_set() const
	{
		const int words = num_words();
		for (int i = 0; i < words; ++i)
		{
			if (m_buf[i] == 0) continue;

			// now, find the index of the first set bit in m_buf[i]
			uint32_t v = aux::network_to_host(m_buf[i]);

#if TORRENT_HAS_SSE
			if (aux::mmx_support)
			{
#ifdef __GNUC__
				return i * 32 + __builtin_clz(v);
#else
				DWORD pos;
				_BitScanReverse(&pos, v);
				return i * 32 + 31 - pos;
#endif
			}
#endif

			// http://graphics.stanford.edu/~seander/bithacks.html#IntegerLogObvious
			static const int MultiplyDeBruijnBitPosition[32] =
			{
				0, 9, 1, 10, 13, 21, 2, 29, 11, 14, 16, 18, 22, 25, 3, 30,
				8, 12, 20, 28, 15, 17, 24, 7, 19, 27, 23, 6, 26, 5, 4, 31
			};

			v |= v >> 1; // first round down to one less than a power of 2
			v |= v >> 2;
			v |= v >> 4;
			v |= v >> 8;
			v |= v >> 16;

			return i * 32 + MultiplyDeBruijnBitPosition[static_cast<uint32_t>(v * 0x07C4ACDDU) >> 27];
		}
		return -1;
	}

	int bitfield::find_last_clear() const
	{
		const int words = num_words();

		uint32_t const mask = 0xffffffff << (32 - (size() & 31));
		uint32_t last = aux::network_to_host(m_buf[words - 1]);

		// turn it into a problem of finding the last _set_ bit instead
		last ^= mask;

		// if no bit is _set_ in this word, keep scanning full words in the
		// loop below
		if (last != 0)
		{
			int const i = words - 1;
#if TORRENT_HAS_SSE
			if (aux::mmx_support)
			{
#ifdef __GNUC__
				return i * 32 + 31 - __builtin_ctz(last);
#else
				DWORD pos;
				_BitScanForward(&pos, last);
				return i * 32 + 31 - pos;
#endif
			}
#endif

			for (int k = 0; k < 32; ++k, last >>= 1)
			{
				if ((last & 1) == 1) continue;
				return i * 32 + 31 - k;
			}
			TORRENT_ASSERT(false && "how is this possible?");
			return -1;
		}

		for (int i = words - 2; i >= 0; --i)
		{
			if (m_buf[i] == 0xffffffff) continue;

			// now, find the index of the last clear bit in m_buf[i]
			// to take advantage of special instructions, negate the word
			uint32_t v = ~aux::network_to_host(m_buf[i]);

#if TORRENT_HAS_SSE
			if (aux::mmx_support)
			{
#ifdef __GNUC__
				return i * 32 + 31 - __builtin_ctz(v);
#else
				DWORD pos;
				_BitScanForward(&pos, v);
				return i * 32 + 31 - pos;
#endif
			}
#endif

			for (int k = 0; k < 32; ++k, v >>= 1)
			{
				if ((v & 1) == 1) continue;
				return i * 32 + 31 - k;
			}
		}
		return -1;
	}

}
