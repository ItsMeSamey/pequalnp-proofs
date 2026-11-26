#include "hereditaryrole.hpp"
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <fstream>
#include <set>
#include <vector>
using namespace std;
constexpr int W = 11, A = 8191, B = 21;
using U = uint64_t;
using Row = array<int, W>;
using Bits = array<U, B>;
struct R {
    int a, b;
};
vector<R> rows;
Bits pos[8192]{}, neg[8192]{}, full{};
int stars[7];
uint64_t family_count = 0, nodes = 0, charge_pruned = 0;
Row anchors{}, excluded{};
uint64_t stars_pruned = 0;
int fixedfour, nanchors;
int role[11], gsz[7];
uint64_t ncase = 0;
// Each designated group must reject every pair exterior to its target.
int four_propagate(Row &yes, Row &no) {
    bool changed = false;
    for (int t = 0; t < 7; t++)
        if (gsz[t] > 1) {
            int T = stars[t], ex = A ^ T;
            if (gsz[t] == 3) {
                int have = 0;
                for (int i = 0; i < W; i++)
                    if (role[i] == t) {
                        int x = yes[i] & ex;
                        if (x & have)
                            return -1;
                        have |= x;
                    }
                for (int i = 0; i < W; i++)
                    if (role[i] == t) {
                        int need = have & ~yes[i];
                        if (need & ~no[i]) {
                            no[i] |= need;
                            changed = true;
                        }
                    }
            }
            for (int i = 0; i < W; i++)
                if (role[i] == t && !(yes[i] & ex)) {
                    int free = ex & ~no[i];
                    if (!free)
                        return -1;
                    if (!(free & (free - 1))) {
                        yes[i] |= free;
                        changed = true;
                    }
                }
            if (gsz[t] > 3) {
                for (int x = ex; x; x &= x - 1)
                    for (int y = x & (x - 1); y; y &= y - 1) {
                        int pair = (x & -x) | (y & -y), ct = 0, last = -1;
                        for (int i = 0; i < W && ct < 2; i++)
                            if (role[i] == t && !(yes[i] & pair)) {
                                ct++;
                                last = i;
                            }
                        if (ct == 0)
                            return -1;
                        if (ct == 1 && (pair & ~no[last])) {
                            no[last] |= pair;
                            changed = true;
                        }
                    }
            }
        }
    return changed;
}
void visit(Row yes, Row no) {
    if (++nodes % 1000000 == 0)
        cerr << nodes << " nodes " << family_count << " surviving families " << charge_pruned
             << " charge-pruned nodes " << stars_pruned << " recovery-pruned nodes" << endl;
    int slot = -1, bit = 0;
    for (;;) {
        for (int i = nanchors; i + 1 < W; i++)
            if (role[i] == role[i + 1] && yes[i] > (A ^ no[i + 1]))
                return;
        for (int j = nanchors; j < W; j++)
            for (int i = 0; i < nanchors; i++) {
                if (role[i] == role[j] && !(anchors[i] & ~yes[j]) && !(excluded[i] & ~no[j]) &&
                    (A ^ no[j]) < yes[i])
                    return;
            }
        // For each slot and witness row track possible coverage, guaranteed
        // coverage, possible private coverage, and coverage forced onto this slot.
        Bits can[W], got[W], others[W], sole[W];
        bool change = false;
        int selected = -1, best = W + 1;
        int fullstars = 0;
        for (int i = 0; i < W; i++)
            if ((yes[i] | no[i]) == A)
                for (int l = 0; l < 7; l++)
                    if (yes[i] == stars[l])
                        fullstars++;
        if (fullstars >= 6)
            return;
        int prop = four_propagate(yes, no);
        if (prop < 0) {
            ++stars_pruned;
            return;
        }
        if (prop)
            continue;
        for (int z = 0; z < B; z++) {
            U c = 0, mc = 0, g = 0, mg = 0;
            for (int i = 0; i < W; i++) {
                U x = can[i][z] = pos[A ^ no[i]][z] & neg[yes[i]][z];
                U y = got[i][z] = pos[yes[i]][z] & neg[A ^ no[i]][z];
                mc |= c & x;
                c |= x;
                mg |= g & y;
                g |= y;
            }
            if (c != full[z])
                return;
            for (int i = 0; i < W; i++) {
                others[i][z] = can[i][z] & ~(mg | (g & ~got[i][z]));
                sole[i][z] = can[i][z] & ~(mc | g);
            }
            if (best == 2)
                continue;
            U opt = full[z] & ~g & mc;
            while (opt) {
                int b = countr_zero(opt), ct = 0;
                for (int i = 0; i < W && ct < best; i++)
                    ct += (can[i][z] >> b) & 1;
                if (ct < best) {
                    best = ct;
                    selected = z * 64 + b;
                }
                opt &= opt - 1;
                if (best == 2)
                    break;
            }
        }
        for (int i = 0; i < W; i++) {
            int must = A, ban = A, forced = 0, avoid = 0;
            bool has = false;
            for (int z = 0; z < B; z++) {
                U v = sole[i][z];
                while (v) {
                    auto r = rows[64 * z + countr_zero(v)];
                    v &= v - 1;
                    forced |= r.a;
                    avoid |= r.b;
                }
                v = others[i][z];
                has |= bool(v);
                while (v && (must || ban)) {
                    auto r = rows[64 * z + countr_zero(v)];
                    v &= v - 1;
                    must &= r.a;
                    ban &= r.b;
                }
            }
            if (!has)
                return;
            forced |= must;
            avoid |= ban;
            if ((forced | yes[i]) & (avoid | no[i]))
                return;
            if ((forced & ~yes[i]) || (avoid & ~no[i])) {
                yes[i] |= forced;
                no[i] |= avoid;
                change = true;
            }
        }
        if (change)
            continue;
        Row high;
        for (int i = 0; i < W; i++)
            high[i] = A ^ no[i];
        if (hereditary::bound(yes, high)) {
            ++charge_pruned;
            return;
        }
        if (selected >= 0) {
            auto r = rows[selected];
            for (slot = 0; slot < W; slot++)
                if (!((r.a & no[slot]) | (r.b & yes[slot])))
                    break;
            int free = (r.a | r.b) & ~(yes[slot] | no[slot]);
            bit = free & -free;
        } else {
            for (slot = 0; slot < W; slot++) {
                int f = A & ~(yes[slot] | no[slot]);
                if (f) {
                    bit = f & -f;
                    break;
                }
            }
            if (slot == W) {
                sort(yes.begin(), yes.end());
                ++family_count;
                for (int x : yes)
                    cout << x << ' ';
                cout << '\n';
                return;
            }
        }
        break;
    }
    Row alt = yes;
    alt[slot] |= bit;
    visit(alt, no);
    no[slot] |= bit;
    visit(yes, no);
}
// Assign the seven slots after the four dedicated group anchors to a group or to unused.
void generate(int i, Row y, Row n) {
    if (i == W) {
        for (int t = 0; t < 7; t++)
            if (gsz[t] == 2)
                return;
        for (int k = 0; k < W; k++)
            if (role[k] >= 0) {
                int T = stars[role[k]];
                if (T & n[k])
                    return;
                y[k] |= T;
                if (gsz[role[k]] == 1) {
                    if (y[k] & ~T)
                        return;
                    n[k] = A ^ T;
                }
            }
        copy(gsz, gsz + 7, hereditary::known_groups);
        ++ncase;
        visit(y, n);
        return;
    }
    if (i < 4) {
        generate(i + 1, y, n);
        return;
    }
    for (int t = -1; t < 7; t++) {
        if (t >= 0 && (!(fixedfour >> t & 1) || (stars[t] & n[i])))
            continue;
        if (i > nanchors && t < role[i - 1])
            continue;
        role[i] = t;
        if (t >= 0)
            gsz[t]++;
        generate(i + 1, y, n);
        if (t >= 0)
            gsz[t]--;
    }
}

int main(int argc, char **argv) {
    if (argc != 3)
        return 1;
    fixedfour = stoi(argv[1]);
    hereditary::setup();
    for (int i = 0; i < 7; i++)
        cin >> stars[i];
    Row y{}, n{};
    for (int i = 0; i < 7; i++)
        cin >> y[i] >> n[i];
    y.fill(0);
    n.fill(0);
    std::ifstream cert(argv[2]);
    int P, Q;
    while (cert >> P >> Q) {
        if (nanchors >= W)
            return 2;
        for (int i = 0; i < nanchors; i++)
            if (!(P & n[i]) && !(Q & y[i]))
                return 3;
        y[nanchors] = P;
        n[nanchors++] = Q;
    }
    if (!nanchors)
        return 4;
    anchors = y;
    excluded = n;
    int a, b;
    while (cin >> a >> b)
        rows.push_back({a, b});
    if (rows.size() != 1323)
        return 1;
    for (int j = 0; j < (int)rows.size(); j++) {
        auto r = rows[j];
        U s = U(1) << (j % 64);
        full[j / 64] |= s;
        for (int v = 0; v <= A; v++) {
            if (v & r.a)
                pos[v][j / 64] |= s;
            if (!(v & r.b))
                neg[v][j / 64] |= s;
        }
    }
    for (int i = 0; i < 4; i++) {
        int t = 0;
        while (t < 7 && stars[t] != y[i])
            t++;
        if (t == 7 || !(fixedfour >> t & 1) || gsz[t])
            return 5;
        role[i] = t;
        gsz[t]++;
    }
    generate(0, y, n);
    cerr << "role cases " << ncase << endl;
    cerr << "DONE " << nodes << " " << family_count << " " << stars_pruned << endl;
}
