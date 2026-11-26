#include <algorithm>
#include <array>
#include <fstream>
#include <iostream>
#include <set>
#include <stdexcept>
#include <utility>
#include <vector>

using Family = std::array<int, 9>;
constexpr int all_points = 8191;

struct Enumerator {
    std::vector<std::pair<int,int>> obligations;
    std::array<int,7> canonical;
    std::vector<std::array<int,8>> eight;
    std::set<Family> families;
    long long nodes = 0;
    long long solutions = 0;

    bool already_covered(const Family& yes, const Family& no) const {
        Family complete{};
        int count = 0;
        for (int i = 0; i < 9; ++i)
            if ((yes[i] | no[i]) == all_points) complete[count++] = yes[i];
        int fixed = 0;
        for (int mask : canonical)
            if (std::find(complete.begin(), complete.begin()+count, mask) != complete.begin()+count)
                ++fixed;
        if (fixed == 7) return true;
        // The classified eight-mask families retain at least four canonical masks.
        if (fixed < 4 || count < 8) return false;
        std::sort(complete.begin(), complete.begin()+count);
        for (const auto& base : eight)
            if (std::includes(complete.begin(), complete.begin()+count, base.begin(), base.end()))
                return true;
        return false;
    }

    void visit(Family yes, Family no) {
        ++nodes;
        int branch = -1, bit = 0;
        bool changed;
        do {
            changed = false;
            int best = 10;
            branch = -1;
            for (auto [point, avoid] : obligations) {
                bool satisfied = false;
                int count = 0, slot = -1;
                for (int i = 0; i < 9; ++i) {
                    if ((yes[i] & avoid) || (no[i] & point)) continue;
                    if ((yes[i] & point) && !(avoid & ~no[i])) {
                        satisfied = true;
                        break;
                    }
                    ++count;
                    slot = i;
                }
                if (satisfied) continue;
                if (!count) return;
                if (count == 1) {
                    yes[slot] |= point;
                    no[slot] |= avoid;
                    changed = true;
                } else if (count < best) {
                    best = count;
                    branch = slot;
                    int undecided = (point | avoid) & ~(yes[slot] | no[slot]);
                    bit = undecided & -undecided;
                }
            }
            if (already_covered(yes, no)) return;
        } while (changed);
        if (branch < 0) {
            for (int i = 0; i < 9; ++i) {
                int undecided = all_points & ~(yes[i] | no[i]);
                if (undecided) {
                    branch = i;
                    bit = undecided & -undecided;
                    break;
                }
            }
        }
        if (branch < 0) {
            ++solutions;
            std::sort(yes.begin(), yes.end());
            families.insert(yes);
            return;
        }
        Family alternative = yes;
        alternative[branch] |= bit;
        visit(alternative, no);
        no[branch] |= bit;
        visit(yes, no);
    }
};

int main() {
    Enumerator search;
    std::ifstream eight("families.txt");
    std::array<int,8> base;
    while (eight >> base[0]) {
        for (int i = 1; i < 8; ++i)
            if (!(eight >> base[i])) throw std::runtime_error("incomplete eight-mask row");
        search.eight.push_back(base);
    }
    if (search.eight.size() != 202) throw std::runtime_error("expected 202 eight-mask families");
    for (int& m : search.canonical) std::cin >> m;
    Family yes{}, no{};
    for (int i = 0; i < 7; ++i) std::cin >> yes[i] >> no[i];
    int point, avoid;
    while (std::cin >> point >> avoid) search.obligations.emplace_back(point, avoid);
    if (search.obligations.size() != 1323) throw std::runtime_error("expected 1323 constraints");
    search.visit(yes, no);
    std::cerr << "nodes " << search.nodes << " solutions " << search.solutions
              << " families " << search.families.size() << '\n';
    for (auto family : search.families) {
        for (int mask : family) std::cout << mask << ' ';
        std::cout << '\n';
    }
}
