// Exact monotone circuit search on the matrix emitted by decode.py.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>

using Mask = std::uint64_t;
using Negatives = Mask __attribute__((vector_size(32)));
constexpr int num_inputs = 38, num_pos = 28, num_neg = 245;
constexpr Mask bit(int i) { return Mask{1} << i; }

bool any(Negatives set) {
    return (set[0] | set[1] | set[2] | set[3]) != 0;
}

struct Search {
    std::array<Mask, num_pos> positive_rows{};
    std::array<unsigned, 64> positive_columns{};
    std::array<Negatives, 64> negative_columns{};
    Negatives all_negatives{};

    bool possible(Mask live, int slack, int next = num_inputs, int previous = -1) {
        if (std::popcount(live) == 1) return true;  // Conservative terminal acceptance.
        std::array<Mask, 64> and_partners;
        and_partners.fill(live);
        std::array<Negatives, 64> witnesses{};
        for (Mask positive : positive_rows) {
            std::array<int, 64> bits;
            std::array<Negatives, 65> prefix;
            prefix[0] = all_negatives;
            int length = 0;
            for (Mask rest = positive & live; rest; rest &= rest - 1) {
                int i = std::countr_zero(rest);
                bits[length] = i;
                prefix[length+1] = prefix[length] & negative_columns[i];
                ++length;
            }
            if (any(prefix[length])) return false; // A negative dominates this positive.
            Negatives suffix = all_negatives;
            for (int k = length; k-- > 0;) {
                int i = bits[k];
                Negatives group = prefix[k] & suffix;
                if (any(group)) {
                    // Exactly i distinguishes this positive from these negatives.
                    and_partners[i] &= positive;
                    witnesses[i] |= group;
                }
                suffix &= negative_columns[i];
            }
        }

        Mask output = bit(next);
        for (Mask right = live; right; right &= right - 1) {
            int j = std::countr_zero(right);
            for (Mask left = live & (bit(j)-1); left; left &= left - 1) {
                int i = std::countr_zero(left);
                Mask operands = bit(i) | bit(j);
                for (bool conjunction : {false, true}) {
                    int recipe = (j*64 + i)*2 + conjunction;
                    if (recipe <= previous) continue;
                    auto neg = conjunction ? negative_columns[i] & negative_columns[j]
                                           : negative_columns[i] | negative_columns[j];
                    auto pos = conjunction ? positive_columns[i] & positive_columns[j]
                                           : positive_columns[i] | positive_columns[j];
                    if (!pos || !any(all_negatives & ~neg)) continue;
                    bool redundant = false;
                    for (Mask rest = live; rest; rest &= rest - 1) {
                        int r = std::countr_zero(rest);
                        if (!(pos & ~positive_columns[r]) && !any(negative_columns[r] & ~neg)) {
                            redundant = true;
                            break;
                        }
                    }
                    if (redundant) continue;

                    Mask allowed = 0;
                    if (conjunction ? bool(and_partners[i] & bit(j))
                                    : !any(witnesses[i] & negative_columns[j])) allowed |= bit(i);
                    if (conjunction ? bool(and_partners[j] & bit(i))
                                    : !any(witnesses[j] & negative_columns[i])) allowed |= bit(j);
                    for (Mask retire : {operands, bit(i), bit(j), Mask{0}}) {
                        int cost = 2 - std::popcount(retire);
                        if (cost > slack || (retire & ~allowed)) continue;
                        negative_columns[next] = neg;
                        positive_columns[next] = pos;
                        for (Mask &row : positive_rows) {
                            bool value = conjunction ? (row & operands) == operands : bool(row & operands);
                            row = (row & ~output) | (value ? output : 0);
                        }
                        if (possible((live & ~retire) | output, slack-cost, next+1, recipe)) return true;
                    }
                }
            }
        }
        return false;
    }
};

int main(int argc, char **argv) {
    int budget = argc == 2 ? std::atoi(argv[1]) : 23;
    int positives, negatives;
    if (budget < 19 || budget > 25 || !(std::cin >> positives >> negatives)
        || positives != num_pos || negatives != num_neg) return 2;
    Search search;
    for (int k = 0; k < positives; ++k) {
        Mask &x = search.positive_rows[k];
        if (!(std::cin >> x) || x >= bit(num_inputs)) return 2;
        for (Mask rest=x; rest; rest &= rest-1) search.positive_columns[std::countr_zero(rest)] |= 1u << k;
    }
    for (int k = 0; k < negatives; ++k) {
        Mask row;
        if (!(std::cin >> row) || row >= bit(num_inputs)) return 2;
        search.all_negatives[k/64] |= bit(k%64);
        for (; row; row &= row-1) search.negative_columns[std::countr_zero(row)][k/64] |= bit(k%64);
    }
    for (int size = 20; size <= budget+1; ++size) {
        int count = 0;
        for (unsigned optional = 0; optional < (1u<<19); ++optional) {
            if (std::popcount(optional) != size-19) continue;
            // Optional bits encode input 1, then inputs 20 through 37.
            Mask live = (bit(20)-3) | ((optional & 1u)<<1) | (Mask(optional>>1)<<20);
            Mask alternatives = bit(20) | bit(21) | bit(31);
            if (!(live & bit(1)) && (live & alternatives) != alternatives) continue;
            if (search.possible(live, budget-size+1)) {
                std::cerr << "Search accepted support " << live << '\n';
                return 1;
            }
            ++count;
        }
        std::cout << size << ' ' << count << std::endl;
    }
}
