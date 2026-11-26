#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <cstdio>
#include <set>
using Mask = std::uint32_t;

struct Audit {
    int n, depth, largest = 0;
    Mask diagonal = 0, universe;
    std::array<Mask, 20> original{}, truncated{};
    std::array<bool, 65536> allowed{};
    std::array<std::uint64_t, 5> prefixes{};
    std::uint64_t first_events = 0;
    Audit(int side, int gates): n(side), depth(gates), universe((1u << (n*n)) - 1) {
        std::set<Mask> terms{0, universe};
        for (int i=0; i<n; ++i) {
            diagonal |= 1u << (n*i+i);
            for (int j=0; j<n; ++j) {
                original[i] |= 1u << (n*i+j);
                original[n+i] |= 1u << (n*j+i);
                terms.insert(1u << (n*i+j));
            }
        }
        for (int i=0; i<2*n; ++i) terms.insert(original[i]);
        truncated = original;
        for (auto a:terms) for (auto b:terms) allowed[a|b] = true;
    }
    void sweep(int k, Mask active, Mask previous_first) {
        ++prefixes[k];
        if (k == depth) return;
        const int top = 2*n+k;
        auto visit = [&](bool is_or, Mask value, Mask before_cut) {
            const Mask ds = value & diagonal;
            if (is_or && (ds & active)) return;
            assert((before_cut & diagonal) == ds);
            assert((before_cut & ~value) == 0);
            const Mask survivor = ds ? before_cut : 0;
            assert(allowed[survivor]);
            Mask newly_first = ds ? 0 : value & ~previous_first;
            if (newly_first) {
                ++first_events;
                assert(!is_or);
                assert((newly_first & ~before_cut) == 0);
                assert(std::popcount(before_cut) <= 4);
                largest = std::max(largest, std::popcount(newly_first));
            }
            original[top] = value; truncated[top] = survivor;
            sweep(k+1, active | (is_or ? ds : 0), previous_first | newly_first);
        };
        for (bool is_or : {false,true}) {
            visit(is_or, is_or ? 0 : universe, is_or ? 0 : universe);
            for (int a=0; a<top; ++a) {
                visit(is_or, original[a], truncated[a]);
                for (int b=0; b<=a; ++b) {
                    visit(is_or, is_or ? original[a]|original[b] : original[a]&original[b],
                               is_or ? truncated[a]|truncated[b] : truncated[a]&truncated[b]);
                }
            }
        }
    }
    void run() {
        sweep(0,0,0);
        std::printf("n=%d depth=%d prefixes=",n,depth);
        for (int k=0;k<=depth;++k) std::printf("%s%llu",k?",":"",(unsigned long long)prefixes[k]);
        std::printf(" first_gate_events=%llu largest_new_charge=%d\n",
                    (unsigned long long)first_events,largest);
    }
};
int main(){ Audit(3,4).run(); Audit(4,3).run(); }
