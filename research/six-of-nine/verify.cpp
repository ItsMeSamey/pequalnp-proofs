#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <unordered_set>
#include <utility>
#include <vector>

using Pair = std::pair<int,int>;
using Pairs = std::vector<Pair>;
using Witnesses = std::array<std::array<Pairs,36>,7>;

Pairs read_pairs() {
    int count;
    if (!(std::cin >> count) || count <= 0) throw std::runtime_error("empty obligation table");
    Pairs result(count);
    for (auto &[p,n] : result)
        if (!(std::cin >> p >> n) || p <= 0 || p >= 8192 || (p & (p-1)) || n < 0 || n >= 8192)
            throw std::runtime_error("malformed obligation");
    return result;
}

bool distinguishes(int signature, Pair row) {
    return (signature & row.first) && !(signature & row.second);
}

Pairs uncovered(const Pairs &pairs, int signature) {
    Pairs rest;
    for (auto pair : pairs) if (!distinguishes(signature,pair)) rest.push_back(pair);
    return rest;
}

template<class Visitor>
void each_signature(int required, int forbidden, int omitted, Visitor visit) {
    if (required & forbidden) return;
    int free = 8191 & ~(required | forbidden);
    for (int s=free; ; s=(s-1)&free) {
        if ((required | s) != omitted) visit(required | s);
        if (!s) break;
    }
}

int main() {
    Witnesses witnesses;
    for (auto &line : witnesses) for (auto &pair : line) pair = read_pairs();
    std::array<Pairs,7> obligations;
    for (auto &set : obligations) set = read_pairs();
    std::array<int,7> canonical;
    for (int &mask : canonical) if (!(std::cin >> mask)) return 2;

    for (int j=0; j<7; ++j) {
        int omitted = canonical[j];
        auto &pairs = obligations[j];
        // Any obligation is valid here. Larger negative masks give smaller subcubes.
        std::sort(pairs.begin(),pairs.end(),[](Pair a, Pair b) {
            return __builtin_popcount(a.second) > __builtin_popcount(b.second);
        });
        std::unordered_set<std::uint64_t> seen;
        std::array<int,7> histogram{};
        auto [must,avoid] = pairs.front();
        each_signature(must,avoid,omitted,[&](int first) {
            auto rest = uncovered(pairs,first);
            if (rest.empty()) throw std::runtime_error("unexpected one-signal completion");
            auto [p,n] = rest.front();
            each_signature(p,n,omitted,[&](int second) {
                int required=0, forbidden=0;
                for (auto row : rest) {
                    if (distinguishes(second,row)) continue;
                    required |= row.first;
                    forbidden |= row.second;
                }
                if (required & forbidden) return;
                std::array<unsigned char,8192> unsafe{};
                for (int k=0; k<7; ++k) {
                    if (k == j) continue;
                    for (const auto &choices : witnesses[k]) {
                        int on=0, off=0;
                        for (auto row : choices) {
                            if (distinguishes(first,row) || distinguishes(second,row)) continue;
                            on |= row.first;
                            off |= row.second;
                            if (on & off) break;
                        }
                        each_signature(on,off,omitted,[&](int third) { unsafe[third] |= 1 << k; });
                    }
                }
                each_signature(required,forbidden,omitted,[&](int third) {
                    std::array<int,3> s{first,second,third};
                    std::sort(s.begin(),s.end());
                    std::uint64_t key = (std::uint64_t(s[0])*8192+s[1])*8192+s[2];
                    if (seen.insert(key).second) ++histogram[__builtin_popcount(unsafe[third])];
                });
            });
        });
        std::cout << omitted << ' ' << seen.size() << ' ' << histogram[0] << ' ' << histogram[1] << std::endl;
        if (seen.size() != 204717 || histogram[0] + histogram[1] != 204717) return 1;
    }
}
