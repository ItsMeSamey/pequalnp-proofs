#ifndef HEREDITARY_HPP
#define HEREDITARY_HPP
#include <array>
#include <algorithm>
#include <bit>
#include <cstdint>
// Bit position J in a 128-bit word represents one subfamily of target lines.
// Every vote is one gate of the lower bound for all subfamilies named by that word.
namespace hereditary {
using Word = unsigned __int128;
using Mask = std::array<int, 11>;
int target[7], touch[8192], rich[8192], part[7][8192];
uint64_t subraw[8192], superraw[8192];
Word subsets[128], permitted[7][128];
void setup() {
    int raw[55], n = 0;
    for (int i = 0; i < 13; i++)
        raw[n++] = 1 << i;
    for (int l = 0; l < 13; l++) {
        int a = (1 << l) | (1 << ((l + 1) % 13)), b = (1 << ((l + 3) % 13)) | (1 << ((l + 9) % 13));
        if (l < 6) {
            raw[n++] = a;
            raw[n++] = b;
            raw[n++] = a | b;
        } else
            target[l - 6] = a | b;
    }
    int orbitraw[] = {1,    2,    3,    4,    6,    8,    9,    10,   12,   16,   17,
                      18,   20,   24,   32,   33,   34,   36,   40,   48,   64,   66,
                      72,   80,   96,   128,  129,  144,  160,  177,  256,  258,  288,
                      320,  354,  512,  513,  514,  520,  523,  1024, 1026, 1028, 1040,
                      1046, 2048, 2052, 2056, 2080, 2092, 4096, 4104, 4112, 4160, 4184};
    std::copy(orbitraw, orbitraw + 55, raw);
    n = 55;
    for (int m = 0; m < 8192; m++) {
        for (int j = 0; j < n; j++) {
            if (!(raw[j] & ~m))
                subraw[m] |= uint64_t(1) << j;
            if (!(m & ~raw[j]))
                superraw[m] |= uint64_t(1) << j;
        }
        for (int t = 0; t < 7; t++) {
            int z = m & target[t];
            if (z)
                touch[m] |= 1 << t;
            if (std::popcount((unsigned)z) >= 2)
                rich[m] |= 1 << t;
            int q = 0;
            for (int b = target[t]; b; b &= b - 1, q++)
                if (m & (b & -b))
                    part[t][m] |= 1 << q;
        }
    }
    for (int a = 0; a < 128; a++)
        for (int j = 0; j < 128; j++)
            if (!(j & ~a))
                subsets[a] |= Word(1) << j;
    for (int t = 0; t < 7; t++)
        for (int bad = 0; bad < 128; bad++)
            permitted[t][bad] = subsets[127 ^ bad] & ~subsets[127 ^ (1 << t)];
}
struct Counter {
    Word plane[6]{};
    void add(Word x) {
        for (int i = 0; x; i++) {
            Word carry = x & plane[i];
            plane[i] ^= x;
            x = carry;
        }
    }
    int max() const {
        Word avail = ~Word(0);
        int mx = 0;
        for (int i = 5; i >= 0; i--) {
            Word x = avail & plane[i];
            if (x) {
                avail = x;
                mx |= 1 << i;
            } else
                avail &= ~plane[i];
        }
        return mx;
    }
};
int known_groups[7]{};
template <bool exact = false> int bound(const Mask &lo, const Mask &hi) {
    Counter votes;
    bool paid[11];
    for (int i = 0; i < 11; i++) {
        paid[i] = !(subraw[hi[i]] & superraw[lo[i]]);
        for (int j = 0; j < i; j++)
            if (paid[j] && !(lo[i] & ~hi[j]) && !(lo[j] & ~hi[i]))
                paid[i] = false;
        if (!paid[i])
            continue;
        // A projected transversal, or a duplicate projected paid mask, saves its gate.
        Word dead = subsets[127 ^ rich[hi[i]]];
        for (int j = 0; j < i; j++)
            if (paid[j]) {
                int different = (hi[i] ^ lo[i]) | (hi[j] ^ lo[j]) | (lo[i] ^ lo[j]);
                dead |= subsets[127 ^ touch[different]];
            }
        votes.add(dead);
    }
    for (int t = 0; t < 7; t++) {
        // The three bitmaps record one, two or three guaranteed savings in the
        // cost of reconstructing this target after projecting to each line subfamily.
        Word one = 0, two = 0, three = 0, pairs[16]{};
        int supers[11], ns = 0;
        for (int i = 0; i < 11; i++) {
            int p = part[t][lo[i]], sz = std::popcount((unsigned)p);
            if (sz < 2)
                continue;
            Word ok = permitted[t][touch[hi[i] & ~target[t]]];
            one |= ok;
            if (sz >= 3)
                two |= ok;
            else
                pairs[p] |= ok;
            if (sz == 4) {
                three |= ok;
                supers[ns++] = i;
            }
        }
        two |= (pairs[3] & pairs[12]) | (pairs[5] & pairs[10]) | (pairs[6] & pairs[9]);
        for (int i = 0; i < ns; i++)
            for (int j = 0; j < i; j++) {
                Word ok = permitted[t][touch[(hi[supers[i]] & hi[supers[j]]) & ~target[t]]];
                one |= ok;
                two |= ok;
            }
        if (known_groups[t]) {
            int saved = 3 - (known_groups[t] - 1) / 2;
            Word contains = permitted[t][0];
            if (saved >= 1)
                one |= contains;
            if (saved >= 2)
                two |= contains;
            if (saved >= 3)
                three |= contains;
        }
        votes.add(one);
        votes.add(two);
        votes.add(three);
    }
    return exact ? votes.max() : (votes.max() >= 12);
}
} // namespace hereditary
#endif
