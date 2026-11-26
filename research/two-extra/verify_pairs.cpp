#include <array>
#include <cstdint>
#include <iostream>
#include <utility>
#include <vector>

int main() {
    constexpr int signatures = 1 << 13;
    std::array<std::array<std::vector<std::pair<int,int>>,36>,7> witnesses;
    for (auto &line : witnesses) {
        for (auto &pair : line) {
            int count;
            if (!(std::cin >> count) || count < 1) return 2;
            for (int i=0; i<count; ++i) {
                int p, n;
                if (!(std::cin >> p >> n) || p <= 0 || p >= signatures ||
                    (p & (p-1)) || n < 0 || n >= signatures) return 2;
                pair.emplace_back(p,n);
            }
        }
    }
    std::array<std::uint64_t,8> histogram{};
    for (int first=0; first<signatures; ++first) {
        std::array<unsigned char,signatures> unsafe_count{};
        for (const auto &line : witnesses) {
            std::array<bool,signatures> unsafe{};
            for (const auto &pair : line) {
                int required=0, forbidden=0;
                for (auto [p,n] : pair) {
                    if ((first & p) && !(first & n)) continue;
                    required |= p;
                    forbidden |= n;
                    if (required & forbidden) break;
                }
                if (required & forbidden) continue;
                int free = (signatures-1) & ~(required | forbidden);
                for (int subset=free; ; subset=(subset-1)&free) {
                    unsafe[required | subset]=true;
                    if (!subset) break;
                }
            }
            for (int second=first; second<signatures; ++second)
                unsafe_count[second] += unsafe[second];
        }
        for (int second=first; second<signatures; ++second)
            ++histogram[unsafe_count[second]];
    }
    for (auto count : histogram) std::cout << count << ' ';
    std::cout << '\n';
    std::array<std::uint64_t,8> expected{32979201,577227,2100,0,0,0,0,0};
    return histogram != expected;
}
