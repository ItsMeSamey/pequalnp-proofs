// Exhaustively enumerate raw tables and compare them to the explicit representatives.
#include <array>
#include <cstdint>
#include <iostream>
#include <map>
#include <stdexcept>
#include <vector>
using Mask = unsigned int;
using Table = unsigned int;
int weight(Mask x) { return __builtin_popcount(x); }
Table signature(const std::vector<Mask>& graph, const std::vector<int>& label) {
    Table table = 0;
    for (Mask s=0; s<(1u<<graph.size()); ++s) {
        int outgoing=0;
        Mask admissible=15;
        for (unsigned i=0; i<graph.size(); ++i) if ((s>>i)&1u) {
            outgoing ^= label[i];
            int parity=weight(s&graph[i])%2;
            for (int b=0;b<4;++b)
                if (parity!=weight(b&label[i])%2) admissible &= ~(1u<<b);
        }
        for (int b=0;b<4;++b) if ((admissible>>b)&1u) table |= 1u<<(4*b+outgoing);
    }
    return table;
}
Mask reachable(const std::vector<Mask>& g, Mask start, Mask interior) {
    Mask reached=start, old;
    do {
        old=reached;
        for(unsigned i=0;i<g.size();++i) if ((old>>i)&1u) reached|=g[i]&interior;
    } while(old!=reached);
    return reached;
}
int main() {
    const Table full=signature({0,0,0},{1,2,3});
    std::map<Table,std::uint64_t> counts;
    for(int n=2;n<=5;++n) {
        std::vector<Mask> g(n);
        std::vector<int> label(n);
        for(Mask edges=0;edges<(1u<<(n*(n-1)/2));++edges) {
            std::fill(g.begin(),g.end(),0);
            int j=0;
            for(int v=0;v<n;++v) for(int w=0;w<v;++w,++j)
                if ((edges>>j)&1u) { g[v]|=1u<<w; g[w]|=1u<<v; }
            for(Mask labs=0;labs<(1u<<(2*n));++labs) {
                std::array<Mask,4> sites{};
                for(int v=0;v<n;++v) { label[v]=(labs>>(2*v))&3; sites[label[v]]|=1u<<v; }
                std::vector<int> types;
                for(int t=1;t<4;++t) if(sites[t]) types.push_back(t);
                if(types.size()<2) continue;
                Table predicted=full;
                if(types.size()==2) {
                    int a=types[0], b=types[1];
                    bool same_component=reachable(g,sites[a],(1u<<n)-1)&sites[b];
                    Mask entry=0,exit=0;
                    for(int v=0;v<n;++v) if(label[v]==a) entry |= g[v]&sites[0];
                    for(int v=0;v<n;++v) if(label[v]==b) exit |= g[v]&sites[0];
                    bool neutral_path=reachable(g,entry,sites[0])&exit;
                    bool nonedge=false;
                    for(int v=0;v<n;++v) if(label[v]==a && (sites[b]&~g[v])) nonedge=true;
                    bool zero_input=nonedge || neutral_path;
                    if(!same_component && !zero_input) throw std::runtime_error("impossible table");
                    if(!same_component) predicted=signature({0,0},{a,b});
                    if(!zero_input) predicted=signature({2,1},{a,b});
                }
                Table actual=signature(g,label);
                if(actual!=predicted) throw std::runtime_error("mismatch");
                ++counts[actual];
            }
        }
    }
    std::uint64_t total=0;
    for(auto [table,count]:counts) { total+=count; std::cout<<table<<" "<<count<<"\n"; }
    std::cout<<"distinct "<<counts.size()<<" total "<<total<<"\n";
}
