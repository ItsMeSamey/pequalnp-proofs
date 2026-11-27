#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

using Word = std::uint64_t;
using Bank = std::vector<Word>;
constexpr Word target=65535;
constexpr std::array<Word,11> raw{2147418115,663661903884,34144976944,728266375360,
    21653750532,103293914128,26322415680,344922804352,414195942664,581968119809,1065151898146};
void check(bool valid) { if (!valid) throw std::logic_error("verification failure"); }

// All nonempty meets using the new generator consist of itself and its
// intersections with the previous full meet closure (all 40 bits retained).
Bank extend(const Bank& bank,Word gen) {
    Bank result=bank;
    result.reserve(bank.size()*2+1);
    result.push_back(gen);
    for (Word w:bank) result.push_back(w&gen);
    std::sort(result.begin(),result.end());
    result.erase(std::unique(result.begin(),result.end()),result.end());
    return result;
}
bool mixed(Word w) {return (w&target) && (w&~target);}
Bank next_outputs(const Bank& bank) {
    std::set<Word> next;
    for (auto a=bank.begin();a!=bank.end();++a) {
        if (!mixed(*a)) continue;
        for (auto b=bank.begin();b!=a;++b) {
            if (!mixed(*b)) continue;
            Word z=*a|*b;
            if (!std::binary_search(bank.begin(),bank.end(),z)) next.insert(z);
        }
    }
    return Bank(next.begin(),next.end());
}
// Search subsets of multirow taps in index order. Uncovered rows may use
// singleton taps, verified to exist in the initial bank for every row.
bool choose(const Bank& taps,const Bank& suffix,std::size_t begin,Word missing,int budget) {
    if (std::popcount(missing)<=budget) return true;
    if (!budget || begin==taps.size()) return false;
    if (std::popcount(missing&~suffix[begin])>=budget) return false;
    for (auto i=begin;i<taps.size();++i) {
        if (std::popcount(missing&taps[i])<2) continue;
        if (choose(taps,suffix,i+1,missing&~taps[i],budget-1)) return true;
    }
    return false;
}
bool cover(const Bank& taps,Word missing,int budget) {
    Bank suffix(taps.size()+1);
    for (std::size_t i=taps.size();i>0;--i) suffix[i-1]=suffix[i]|taps[i-1];
    return choose(taps,suffix,0,missing,budget);
}
bool feasible(const Bank& bank) {
    Bank taps;
    for (Word w:bank) {
        if (w>target) break;
        if (std::popcount(w)>1) taps.push_back(w);
    }
    return cover(taps,target,8);
}
struct Counts {std::array<unsigned long long,4> seen{},hits{};};
void visit(const Bank& bank,int depth,Counts& c) {
    ++c.seen[depth];
    if (feasible(bank)) ++c.hits[depth];
    if (depth<3) for (Word z:next_outputs(bank)) visit(extend(bank,z),depth+1,c);
}
void controls(const Bank& base) {
    for(int i=0;i<16;++i) check(std::binary_search(base.begin(),base.end(),Word(1)<<i));
    check(!feasible(base));
    const Bank masks{3,5,6,7,9,10,12};
    for (unsigned f=0;f<128;++f) {
        Bank taps;
        for (unsigned j=0;j<7;++j) if(f&(1u<<j)) taps.push_back(masks[j]);
        std::set<Word> states{0};
        for (int k=0;k<=4;++k) {
            check(cover(taps,15,k)==states.contains(15));
            auto next=states;
            for (Word s:states) {
                for (Word w:taps) next.insert(s|w);
                for (Word w:{1,2,4,8}) next.insert(s|w);
            }
            states=std::move(next);
        }
    }
}
int main(int argc,char** argv) {
    Bank base;
    for(Word w:raw) base=extend(base,w);
    controls(base);
    Bank first=next_outputs(base);
    check(first.size()==55);
    if(argc==2 && std::string(argv[1])=="--controls") {
        std::cout<<"640 cover controls passed; 55 initial OR outputs\n";return 0;
    }
    check(argc==3);
    int lo=std::stoi(argv[1]),hi=std::stoi(argv[2]);
    check(lo>=0 && hi>=lo && hi<=55);
    for(int i=lo;i<hi;++i) {
        Counts c;
        visit(extend(base,first[i]),1,c);
        std::cout<<i<<' '<<first[i];
        for(int d=1;d<=3;++d) std::cout<<' '<<c.seen[d]<<' '<<c.hits[d];
        std::cout<<std::endl;
    }
}
