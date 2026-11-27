#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <set>
#include <vector>
using Bits=std::uint32_t;
constexpr Bits positive=(1u<<13)-1;
const std::array<int,29> rows={6,24,17,33,66,132,264,528,160,640,576,320,288,
  50,77,108,116,139,201,208,276,387,402,523,525,554,556,771,773};
std::vector<Bits> maxima(const std::set<Bits>& pool) {
    std::vector<Bits> kept;
    for(Bits s:pool) {
        bool dominated=false;
        for(Bits t:pool) if(s!=t && (s&t)==s) {dominated=true; break;}
        if(!dominated) kept.push_back(s);
    }
    return kept;
}
int main() {
    std::array<Bits,1024> traces{};
    std::array<std::vector<Bits>,1024> raw;
    for(int s=1;s<1024;++s) for(unsigned k=0;k<rows.size();++k)
        if(s & rows[k]) traces[s]|=1u<<k;
    for(int target=1;target<1024;++target)
        for(int s=1;s<1024;++s) if((s&target)==s) raw[target].push_back(traces[s]);
    int ix,i,j,a,b,c,d,y;
    while(std::cin>>ix>>i>>j>>a>>b>>c>>d>>y) {
        Bits h=traces[a]&traces[b], q=traces[c]&traces[d], u=h|traces[y];
        Bits wanted=positive|(1u<<(13+i))|(1u<<(13+j));
        if((u&wanted)!=positive) return 2;
        std::set<Bits> bank{q};
        for(int k=0;k<10;++k) bank.insert(traces[1<<k]);
        for(int mask:{a,b,c,d}) bank.insert(raw[mask].begin(),raw[mask].end());
        std::set<Bits> ordinary,escaped;
        auto append=[&](std::set<Bits>& list,Bits s) {
            if(!(s&~wanted) && (s&positive) && (s&~positive)) list.insert(s);
        };
        for(Bits s:bank) for(Bits t:bank) {
            append(ordinary,s&t);
            append(escaped,(s|h)&t);
        }
        Bits total=0;
        for(auto s:ordinary) total|=s;
        for(auto s:escaped) total|=s;
        int status=0;
        if(total==wanted) {
            status=1;
            auto regular=maxima(ordinary), escapes=maxima(escaped);
            for(auto first:regular) for(auto second:regular) for(auto third:escapes)
                if((first|second|third)==wanted) status=2;
        }
        std::array<int,4> sizes={__builtin_popcount((unsigned)a),__builtin_popcount((unsigned)b),
                                 __builtin_popcount((unsigned)c),__builtin_popcount((unsigned)d)};
        std::sort(sizes.begin(),sizes.end());
        std::cout<<ix<<' ';
        for(auto k:sizes) std::cout<<k;
        std::cout<<' '<<status<<'\n';
    }
}
