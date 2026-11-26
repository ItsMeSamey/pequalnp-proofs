// Exact monotone circuit search on the restricted matrix emitted by run.py.
// Adapted from the residual-gate-bound verifier for variable matrix dimensions.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>

using Mask = std::uint64_t;
using Negatives = Mask __attribute__((vector_size(32)));
int num_inputs, num_pos, num_neg;
constexpr Mask bit(int i) { return Mask{1} << i; }

bool any(Negatives set) {
    return (set[0] | set[1] | set[2] | set[3]) != 0;
}

struct Search {
    std::array<Mask, 28> positive_rows{};
    std::array<unsigned, 64> positive_columns{};
    std::array<Negatives, 64> negative_columns{};
    Negatives all_negatives{};

    bool possible(Mask live, int slack, int next = num_inputs, int previous = -1) {
        if (std::popcount(live) == 1) return true;  // Conservative terminal acceptance.
        std::array<Mask, 64> and_partners;
        and_partners.fill(live);
        std::array<Negatives, 64> witnesses{};
        for (int p=0; p<num_pos; ++p) {
            Mask positive = positive_rows[p];
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
                        for (int p=0; p<num_pos; ++p) {
                            Mask &row=positive_rows[p];
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
    int budget, positives, negatives, num_cuts;
    if (!(std::cin >> budget >> num_inputs >> positives >> negatives >> num_cuts)) return 2;
    num_pos=positives;num_neg=negatives;
    if (positives<1 || positives>28 || negatives<1 || negatives>245 || num_cuts<1 || num_cuts>8192
        || num_inputs<1 || budget<0 || num_inputs+budget>63) return 2;
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
    Mask required=0; std::array<Mask,8192> cuts;
    for(int i=0; i<num_cuts; ++i) {
        std::cin>>cuts[i];
        if (std::has_single_bit(cuts[i])) required|=cuts[i];
    }
    Mask opt=(bit(num_inputs)-1)^required;
    size_t tested=0;
    for(Mask e=opt;;e=(e-1)&opt) {
        Mask live=required|e;
        bool hit=std::popcount(live)<=budget+1;
        for(int k=0;hit && k<num_cuts;++k) if(!(live&cuts[k]))hit=false;
        if(hit) {
            ++tested;
            if(search.possible(live,budget-std::popcount(live)+1)) {
                std::cout << "POSSIBLE "<<live<<" "<<tested<<std::endl;
                return 1;
            }
        }
        if(!e)break;
    }
    std::cout << "UNSAT "<<tested<<std::endl;
}
