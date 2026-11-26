#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using namespace std;
using Bits=uint64_t;
using Signature=array<Bits,6>; // positives, up to 245 negatives, ancestry side
using Family=array<int,9>;
using Frontier=array<int,16>; // zero entries are padding
template<class T> struct ArrayHash {
    size_t operator()(const T& values)const{
        size_t h=0x9e3779b97f4a7c15ULL;
        for(auto v:values){h^=v+0x9e3779b97f4a7c15ULL+(h<<6)+(h>>2);}
        return h;
    }
};
using States=unordered_set<Frontier,ArrayHash<Frontier>>;
struct Wire{
    Signature value;
    // For each positive row, mask of the negatives distinguished by this wire.
    vector<Bits> separates;
};
struct Search{
    int count_pos, count_neg, blocks;
    vector<Wire> wires{{}};
    unordered_map<Signature,int,ArrayHash<Signature>> ids;
    unordered_map<uint64_t,int> joins;

    int intern(Signature sig){
        auto [entry,created]=ids.emplace(sig,wires.size());
        if(!created)return entry->second;
        Wire wire{sig,vector<Bits>(count_pos*blocks)};
        for(int p=0;p<count_pos;p++)if(sig[0]>>p&1){
            for(int b=0;b<blocks;b++)wire.separates[p*blocks+b]=~sig[b+1];
        }
        wires.push_back(move(wire));
        return entry->second;
    }
    int combine(int a,int b,int op){
        auto key=(uint64_t(a)<<33)|(uint64_t(b)<<1)|op;
        auto it=joins.find(key);
        if(it!=joins.end())return it->second;
        Signature s{};
        for(int k=0;k<=blocks;k++)s[k]=op? wires[a].value[k]|wires[b].value[k] : wires[a].value[k]&wires[b].value[k];
        s[5]=2;
        return joins[key]=intern(s);
    }
    void next(const Frontier&state,int size,States&ordinary,States*copied){
        // Only obligations uniquely distinguished by one consumed wire can be
        // lost, because either operation preserves an obligation distinguished
        // by both operands. Store the two projections of these private pairs.
        array<Signature,16> need{};
        for(int p=0;p<count_pos;p++)for(int b=0;b<blocks;b++){
            Bits once=0,twice=0,d[16];
            for(int i=0;i<size;i++){
                d[i]=wires[state[i]].separates[p*blocks+b];
                twice|=once&d[i];once|=d[i];
            }
            Bits valid=(b+1<blocks||count_neg%64==0)?~Bits(0):((Bits(1)<<(count_neg%64))-1);
            Bits single=once&~twice&valid;
            if(!single)continue;
            for(int i=0;i<size;i++)if(Bits x=single&d[i]){
                need[i][0]|=Bits(1)<<p;need[i][1+b]|=x;
            }
        }
        for(int i=0;i<size;i++)for(int j=i+1;j<size;j++){
            int a=state[i],b=state[j];
            auto av=wires[a].value,bv=wires[b].value;
            if(av[5]==bv[5]&&av[5]!=2)continue;
            for(int op=0;op<2;op++){
                // Both operands distinguish every obligation in need[i][j];
                // either AND or OR still distinguishes those obligations.
                // At need[i], a already separates; b must take the right
                // value at the positive (AND) or the negative (OR).
                bool unsafeA=false,unsafeB=false;
                if(!op){
                    unsafeA=need[i][0]&~bv[0];
                    unsafeB=need[j][0]&~av[0];
                }else{
                    for(int k=1;k<=blocks;k++){
                        unsafeA|=bool(need[i][k]&bv[k]);
                        unsafeB|=bool(need[j][k]&av[k]);
                    }
                }
                if((unsafeA||unsafeB)&&(!copied||(unsafeA&&unsafeB)))continue;
                int h=combine(a,b,op);
                auto push=[&](States& out,int keep){
                    Frontier n{};int t=0;
                    for(int k=0;k<size;k++)if((k!=i&&k!=j)||k==keep)n[t++]=state[k];
                    n[t++]=h;sort(n.begin(),n.begin()+t);out.insert(n);
                };
                if(!unsafeA&&!unsafeB)push(ordinary,-1);
                if(copied&&!unsafeB)push(*copied,i);
                if(copied&&!unsafeA)push(*copied,j);
            }
        }
    }
    pair<int,int> run(const vector<int>&ps,const vector<int>&ns,int cap){
        count_pos=ps.size();count_neg=ns.size();blocks=(count_neg+63)/64;
        assert(count_pos<=64&&blocks<=4);
        Frontier orig{};
        for(int i=0;i<16;i++){
            Signature v{};
            for(int j=0;j<count_pos;j++)if(ps[j]>>i&1)v[0]|=Bits(1)<<j;
            for(int j=0;j<count_neg;j++)if(ns[j]>>i&1)v[1+j/64]|=Bits(1)<<(j%64);
            v[5]=i>=7;
            orig[i]=intern(v);
        }
        sort(orig.begin(),orig.end());
        States plain{orig}, copied;
        for(int gate=1;gate<=16;gate++){
            States np,nc;
            for(auto&s:plain)next(s,17-gate,np,&nc);
            for(auto&s:copied){next(s,18-gate,nc,nullptr);if(int(nc.size())>cap)return {gate,-1};}
            if(np.empty()&&nc.empty())return {gate,0};
            plain.swap(np);copied.swap(nc);
        }
        return {16,int(copied.size())};
    }
};
int main(int argc,char**argv){
    if(argc<3)return 1;ifstream rows(argv[1]),families(argv[2]);
    int p,n;rows>>p>>n;vector<int> raw_p(p),raw_n(n);
    for(int&x:raw_p)rows>>x;for(int&x:raw_n)rows>>x;
    int cap=argc>3?stoi(argv[3]):10000;
    Family fam;while(families>>fam[0]){
        for(int k=1;k<9;k++){families>>fam[k];assert(families);}
        auto project=[&](int r){
            int v=(r>>13)&127;for(int j=0;j<9;j++)if(r&fam[j])v|=1<<(7+j);return v;
        };
        set<int> pset,nset;for(int r:raw_p)pset.insert(project(r));for(int r:raw_n)nset.insert(project(r));
        vector<int> ps(pset.begin(),pset.end()),ns;
        for(int x:nset)if(none_of(nset.upper_bound(x),nset.end(),[&](int y){return !(x&~y);}))ns.push_back(x);
        Search search;auto [gate,status]=search.run(ps,ns,cap);
        for(int x:fam)cout<<x<<' ';cout<<gate<<' '<<status<<'\n';
    }
}
