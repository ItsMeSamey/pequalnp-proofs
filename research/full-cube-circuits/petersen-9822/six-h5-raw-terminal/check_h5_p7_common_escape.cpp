// Replay chronological mixed-terminal suffixes on packed original extremal rows.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <set>
#include <vector>
using Mask = unsigned;
using Bank = std::vector<Mask>;
constexpr Mask edges = 8191;
void unique(Bank& bank) {
    std::sort(bank.begin(), bank.end());
    bank.erase(std::unique(bank.begin(), bank.end()), bank.end());
}
bool legal(Mask trace, Mask wanted) {
    return (trace & edges) && (trace & ~edges) && !(trace & ~wanted);
}
bool covers(Bank grants, Mask wanted) {
    unique(grants);
    Mask all = 0;
    for (Mask term : grants) all |= term;
    if (all != wanted) return false;
    std::set<Mask> pairs;
    for (Mask a : grants) for (Mask b : grants) pairs.insert(a|b);
    for (Mask pair : pairs) for (Mask c : grants)
        if ((pair|c) == wanted) return true;
    return false;
}
int main() {
    Mask wanted;
    if (!(std::cin >> wanted)) return 1;
    std::array<Mask,1024> raw{};
    for (auto &s : raw) std::cin >> s;
    std::array<Bank,1024> subsets;
    for (Mask m=1; m<1024; ++m) for (Mask v=1; v<=m; ++v)
        if ((v&m)==v) subsets[m].push_back(raw[v]);
    int counted=0, union_pass=0, triple_pass=0, any_e_pass=0;
    Mask a,b,c,d,u;
    while (std::cin >> a >> b >> c >> d >> u) {
        Mask h = raw[a]&raw[b], q=raw[c]&raw[d];
        if (!((a&b)!=a && (a&b)!=b && (c&d)!=c && (c&d)!=d)) continue;
        if (!(h&edges) || !(h&~edges) || !(q&edges) || !(q&~edges)) continue;
        if (((h|raw[u&1023]) & wanted) != edges) return 2;
        ++counted;
        Bank bank{q};
        for (int j=0;j<10;++j) bank.push_back(raw[1U<<j]);
        for (Mask m : {a,b,c,d}) bank.insert(bank.end(),subsets[m].begin(),subsets[m].end());
        unique(bank);
        Bank base;
        Mask aggregate=0;
        for (Mask x : bank) for (Mask y : bank) {
            Mask t=x&y;
            if (legal(t,wanted)) { base.push_back(t); aggregate|=t; }
        }
        for (Mask x : bank) {
            Mask e=h|x;
            if (legal(e,wanted)) aggregate |= e;
            for (Mask y : bank) {
                Mask t=e&y;
                if (legal(t,wanted)) aggregate |= t;
            }
        }
        if (aggregate!=wanted) continue;
        ++union_pass;
        bool some_e=false, three=false;
        for (Mask x : bank) {
            Mask e=h|x, all=0;
            Bank terms=base;
            if (legal(e,wanted)) terms.push_back(e);
            for (Mask y : bank) if (legal(e&y,wanted)) terms.push_back(e&y);
            for (Mask t : terms) all|=t;
            if (all==wanted) { some_e=true; three|=covers(terms,wanted); }
        }
        any_e_pass+=some_e; triple_pass+=three;
    }
    std::cout << counted << ' ' << union_pass << ' ' << any_e_pass << ' ' << triple_pass << '\n';
}
