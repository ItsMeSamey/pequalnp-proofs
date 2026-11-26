#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <utility>
#include <vector>

using Row = std::pair<int,int>;
using Witnesses = std::vector<Row>;
using Histogram = std::array<std::uint64_t,8>;

int main() {
    std::array<Histogram,4> totals{};
    std::array<int,4> bases{};
    for (int orbit=0; orbit<23; ++orbit) {
        int missing, multiplicity;
        if (!(std::cin >> missing >> multiplicity) || missing<1 || missing>3 || multiplicity<1) return 2;
        bases[missing] += multiplicity;
        std::array<std::vector<Witnesses>,7> tests;
        for (auto &line : tests) {
            int count;
            if (!(std::cin >> count) || count<1) return 2;
            line.resize(count);
            for (auto &choices : line) {
                int size;
                if (!(std::cin >> size) || size<1) return 2;
                choices.resize(size);
                for (auto &[p,n] : choices)
                    if (!(std::cin >> p >> n) || p<1 || p>=8192 || (p & (p-1)) || n<0 || n>=8192) return 2;
            }
        }
        Histogram histogram{};
        for (int first=0; first<8192; ++first) {
            std::array<unsigned char,8192> unsafe{};
            for (int j=0; j<7; ++j) {
                for (const auto &choices : tests[j]) {
                    int required=0, forbidden=0;
                    for (auto [p,n] : choices) {
                        if ((first & p) && !(first & n)) continue;
                        required |= p;
                        forbidden |= n;
                        if (required & forbidden) break;
                    }
                    if (required & forbidden) continue;
                    int free = 8191 & ~(required | forbidden);
                    for (int subset=free; ; subset=(subset-1)&free) {
                        unsafe[required | subset] |= 1 << j;
                        if (!subset) break;
                    }
                }
            }
            for (int second=first; second<8192; ++second)
                ++histogram[__builtin_popcount(unsafe[second])];
        }
        for (int i=0; i<8; ++i) totals[missing][i] += multiplicity * histogram[i];
    }
    if (bases != std::array<int,4>{0,175,21,6}) return 1;
    std::array<Histogram,4> expected{};
    expected[1] = {5599834434ULL,270947967,1959189,810};
    expected[2] = {687436950,17204220,87918};
    expected[3] = {196316760,5008248,26160};
    for (int r=1; r<=3; ++r) {
        std::cout << r;
        for (auto n : totals[r]) std::cout << ' ' << n;
        std::cout << '\n';
    }
    return expected != totals;
}
