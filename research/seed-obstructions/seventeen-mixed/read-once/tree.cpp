#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <cstdint>
#include <iostream>
#include <map>
#include <set>
#include <utility>
#include <vector>

using namespace std;
using Rows = array<uint64_t, 5>;
using LineMasks = bitset<128>;
using Family = array<int, 10>;
enum Side { point, line, mixed };
using Wire = pair<Rows, Side>;

int positives, negatives;
vector<pair<int,int>> samples;
map<Wire,int> ids;
vector<Wire> wires;
set<vector<int>> seen;

int intern(const Wire &wire) {
    auto [it, created] = ids.emplace(wire, ids.size());
    if (created) wires.push_back(wire);
    return it->second;
}

int atom(Side side, int mask) {
    Rows rows{};
    for (size_t i = 0; i < samples.size(); ++i) {
        auto [p,l] = samples[i];
        if ((side == point ? p : l) & mask)
            rows[i/64] |= uint64_t(1) << (i%64);
    }
    return intern({rows,side});
}

// Return true iff some tree over the current mixed-cone frontier separates the rows.
bool tree(vector<int> state) {
    sort(state.begin(), state.end());
    if (!seen.insert(state).second) return false;
    int n = state.size(), all = (1 << n) - 1;
    vector<int> active(samples.size());
    for (int i = 0; i < n; ++i) {
        const Rows &r = wires[state[i]].first;
        for (size_t k = 0; k < active.size(); ++k)
            if ((r[k/64] >> (k%64)) & 1) active[k] |= 1 << i;
    }
    vector<int> andPartners(n, all), orPartners(n, all);
    for (int p = 0; p < positives; ++p) {
        for (int j = 0; j < negatives; ++j) {
            int neg = active[positives+j];
            unsigned diff = active[p] & ~neg;
            if (!diff) return false;
            if (has_single_bit(diff)) {
                int i = countr_zero(diff);
                andPartners[i] &= active[p];
                orPartners[i] &= ~neg;
            }
        }
    }
    if (n == 1) return true;
    for (int i = 0; i < n; ++i) for (int j = 0; j < i; ++j) {
        auto [a,as] = wires[state[i]];
        auto [b,bs] = wires[state[j]];
        if (as == bs && as != mixed) continue;
        for (bool conjunction : {false,true}) {
            const auto &v = conjunction ? andPartners : orPartners;
            if (!(v[i] & (1 << j)) || !(v[j] & (1 << i))) continue;
            Rows next{};
            for (size_t k = 0; k < next.size(); ++k)
                next[k] = conjunction ? a[k]&b[k] : a[k]|b[k];
            vector<int> reduced = state;
            reduced.erase(reduced.begin()+i);
            reduced.erase(reduced.begin()+j);
            reduced.push_back(intern({next,mixed}));
            if (tree(reduced)) return true;
        }
    }
    return false;
}

// Check all eighth line masks simultaneously. Bit e represents precisely the
// family with the seven singleton line signals and the extra line mask e.
LineMasks mandatoryGuard(const Family &family, int maxBits) {
    LineMasks eligible;
    array<LineMasks,128> activeLine;
    for (int e = 0; e < 128; ++e) {
        if (popcount(unsigned(e)) <= maxBits) eligible.set(e);
        for (int l = 0; l < 128; ++l) if (e & l) activeLine[l].set(e);
    }
    vector<int> fixed;
    for (auto [p,l] : samples) {
        int bits = l << 10;
        for (int i = 0; i < 10; ++i) if (p & family[i]) bits |= 1 << i;
        fixed.push_back(bits);
    }
    vector<array<LineMasks,18>> pos(positives), neg(negatives);
    for (int i = 0; i < positives; ++i) for (int j = 0; j < negatives; ++j) {
        int n = positives+j;
        unsigned diff = fixed[i] & ~fixed[n];
        if (diff & (diff-1)) continue;
        LineMasks extra = activeLine[samples[i].second] & ~activeLine[samples[n].second];
        int bit;
        LineMasks mandatory;
        if (diff) {
            bit = countr_zero(diff);
            mandatory = ~extra;
        } else {
            bit = 17;
            mandatory = extra;
            eligible &= extra;
        }
        pos[i][bit] |= mandatory;
        neg[j][bit] |= mandatory;
    }
    for (int a = 0; a < 18 && eligible.any(); ++a) for (int b = 0; b < a; ++b) {
        LineMasks bothPos, bothNeg;
        for (const auto &p : pos) bothPos |= p[a] & p[b];
        if ((bothPos & eligible).none()) continue;
        for (const auto &n : neg) bothNeg |= n[a] & n[b];
        eligible &= ~(bothPos & bothNeg);
    }
    return eligible;
}

int main() {
    if (!(cin >> positives >> negatives) || positives != 28 || negatives != 245) return 2;
    for (int i = 0; i < positives+negatives; ++i) {
        int p,l;
        if (!(cin >> p >> l) || p < 0 || p >= 8192 || l < 0 || l >= 128) return 2;
        samples.emplace_back(p,l);
    }
    int maxBits;
    while (cin >> maxBits) {
        if (maxBits < 0 || maxBits > 7) return 2;
        Family family;
        for (int &m : family) if (!(cin >> m) || m < 0 || m >= 8192) return 2;
        auto keep = mandatoryGuard(family, maxBits);
        int sat = 0;
        for (int e = 0; e < 128; ++e) if (keep[e]) {
            ids.clear(); wires.clear(); seen.clear();
            vector<int> state;
            for (int m : family) state.push_back(atom(point,m));
            for (int i = 0; i < 7; ++i) state.push_back(atom(line,1 << i));
            state.push_back(atom(line,e));
            sat += tree(state);
        }
        cout << keep.count() << ' ' << sat << '\n';
    }
    return cin.eof() ? 0 : 2;
}
