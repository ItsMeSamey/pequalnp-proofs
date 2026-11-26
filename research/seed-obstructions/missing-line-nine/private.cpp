#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <vector>
#include <algorithm>
using namespace std;
struct Node {
    int m, a, b, op;
};
struct Gen {
    vector<Node> nodes;
    vector<int> tree[512];
    int adj[9]{}, root, mark[6], act[6], members[512]{};
    long stats[4][7]{}, invalid[4]{};
    void generate(uint64_t g) {
        for (auto &t : tree)
            t.clear();
        nodes.clear();
        fill(adj, adj + 9, 0);
        int k = 0;
        for (int i = 0; i < 9; i++)
            for (int j = i + 1; j < 9; j++, k++)
                if (g >> k & 1)
                    adj[i] |= 1 << j, adj[j] |= 1 << i;
        for (int m = 1; m < 512; m++) {
            if (has_single_bit(unsigned(m))) {
                tree[m].push_back(nodes.size());
                nodes.push_back({m, -1, -1, -1});
                continue;
            }
            for (int a = (m - 1) & m; a; a = (a - 1) & m) {
                int b = m ^ a;
                if (a >= b)
                    continue;
                int x = adj[countr_zero(unsigned(a))] & b;
                if (x != 0 && x != b)
                    continue;
                bool ok = true;
                for (int u = a; u; u &= u - 1)
                    if ((adj[countr_zero(unsigned(u))] & b) != x)
                        ok = false;
                if (ok)
                    for (int i : tree[a])
                        for (int j : tree[b]) {
                            tree[m].push_back(nodes.size());
                            nodes.push_back({m, i, j, x != 0});
                        }
            }
        }
    }
    void process(int mode) {
        for (int i = 0; i < 6; i++)
            mark[i] = 1 << i, act[i] = i < 3 ? (1 << i) | (1 << (6 + i)) : (1 << i);
        if (mode) {
            int i = mode - 1;
            mark[i] = 1 << (6 + i);
            act[i] = 448;
        }
        if (mode)
            for (int i = 0; i < 6; i++)
                for (int j = 0; j < i; j++)
                    if (adj[countr_zero(unsigned(mark[i]))] & mark[j])
                        return;
        for (int m = 0; m < 512; m++) {
            members[m] = 0;
            for (int i = 0; i < 6; i++)
                if (mark[i] & m)
                    members[m] |= 1 << i;
        }
        for (int r : tree[511]) {
            int ok = 0;
            bool impossible = false;
            for (int i = 0; i < 6 && !impossible; i++) {
                int qs[20]{}, nq = 0;
                auto need = [&](int bits) {
                    if (find(qs, qs + nq, bits) == qs + nq)
                        qs[nq++] = bits;
                };
                int id = r;
                for (;;) {
                    Node N = nodes[id];
                    int others = members[N.m] & ~(1 << i);
                    if (others)
                        need(others); // any unary AND on this nonprivate segment
                    if (N.a < 0)
                        break;
                    if (!(nodes[N.a].m & mark[i]))
                        swap(N.a, N.b);
                    int a = nodes[N.a].m, b = nodes[N.b].m;
                    if (N.op) {
                        if (members[b] && !(act[i] & b)) {
                            impossible = true;
                            break;
                        }
                        int eligible = 0;
                        for (int j = 0; j < 6; j++)
                            if (j != i && (mark[j] & a) && !((act[j] & b) & ~act[i]))
                                eligible |= 1 << j;
                        need(eligible);
                    }
                    id = N.a;
                }
                bool good = false;
                for (int j = 0; j < 6 && !good; j++)
                    for (int k = j + 1; k < 6; k++)
                        if (j != i && k != i) {
                            int w = (1 << j) | (1 << k);
                            bool succ = true;
                            for (int n = 0; n < nq; n++)
                                if (!(qs[n] & w))
                                    succ = false;
                            if (succ) {
                                good = true;
                                break;
                            }
                        }
                if (good)
                    ok++;
            }
            if (impossible)
                invalid[mode]++;
            else {
                stats[mode][ok]++;
                if (ok < 4)
                    cout << mode << " " << r << " " << ok << "\n";
            }
        }
    }
};
int main() {
    Gen x;
    uint64_t g;
    while (cin >> g) {
        x.generate(g);
        for (int k = 0; k < 4; k++)
            x.process(k);
    }
    for (int k = 0; k < 4; k++) {
        cerr << k << " invalid " << x.invalid[k] << " good";
        for (int j = 0; j < 7; j++)
            cerr << " " << x.stats[k][j];
        cerr << endl;
    }
}
