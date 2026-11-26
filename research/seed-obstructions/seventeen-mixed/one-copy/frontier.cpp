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
using Family=array<int,10>;
using Frontier=array<int,17>; // zero entries are padding
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
        array<Signature,17> need{};
        for(int p=0;p<count_pos;p++)for(int b=0;b<blocks;b++){
            Bits once=0,twice=0,d[17];
            for(int i=0;i<size;i++){
                d[i]=wires[state[i]].separates[p*blocks+b];
                twice|=once&d[i];once|=d[i];
            }
            Bits valid=(b+1<blocks||count_neg%64==0)?~Bits(0):((Bits(1)<<(count_neg%64))-1);
            if((once&valid)!=valid)return;
            Bits single=once&~twice&valid;
            if(!single)continue;
            for(int i=0;i<size;i++)if(Bits x=single&d[i]){
                need[i][0]|=Bits(1)<<p;need[i][1+b]|=x;
            }
        }
        // Once no further use can be retained the remainder is read-once.
        // On each positive a private obligation forces its wire into every
        // accepting minterm; on each negative it lies in every rejecting
        // maxterm. A read-once minterm and maxterm intersect once.
        if(!copied){
            for(int i=0;i<size;i++)for(int j=i+1;j<size;j++){
                if(!(need[i][0]&need[j][0]))continue;
                for(int b=1;b<=blocks;b++)if(need[i][b]&need[j][b])return;
            }
        }
        for(int i=0;i<size;i++)for(int j=i+1;j<size;j++){
            int a=state[i],b=state[j];
            auto av=wires[a].value,bv=wires[b].value;
            if(av[5]==bv[5]&&av[5]!=2)continue;
            for(int op=0;op<2;op++){
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
    pair<int,int> run(const vector<int>&ps,const vector<int>&ns,int nleaves){
        count_pos=ps.size();count_neg=ns.size();blocks=(count_neg+63)/64;
        assert(count_pos<=64&&blocks<=4);
        Frontier orig{};
        for(int i=0;i<nleaves;i++){
            Signature v{};
            for(int j=0;j<count_pos;j++)if(ps[j]>>i&1)v[0]|=Bits(1)<<j;
            for(int j=0;j<count_neg;j++)if(ns[j]>>i&1)v[1+j/64]|=Bits(1)<<(j%64);
            v[5]=i>=7;
            orig[i]=intern(v);
        }
        sort(orig.begin(),orig.begin()+nleaves);
        States unused{orig},spent;
        for(int gate=1;gate<=nleaves;gate++){
            States next_unused,next_spent;
            for(const auto& s:unused)next(s,nleaves+1-gate,next_unused,&next_spent);
            for(const auto& s:spent)next(s,nleaves+2-gate,next_spent,nullptr);
            if(next_unused.empty()&&next_spent.empty())return {gate,0};
            unused.swap(next_unused);
            spent.swap(next_spent);
        }
        return {nleaves,int(spent.size())};
    }
};
int main(){
    int p=0,n=0,count=0;
    cin>>p>>n;
    if(p!=28||n!=245)return 1;
    vector<int> raw_p(p),raw_n(n);
    for(int&x:raw_p)cin>>x;
    for(int&x:raw_n)cin>>x;
    cin>>count;
    for(int i=0;i<count;i++){
        Family fam{};
        for(int&x:fam)if(!(cin>>x)||x<0||x>=8192)return 2;
        auto project=[&](int row){
            int result=row>>13;
            for(int j=0;j<10;j++)if(row&fam[j])result|=1<<(7+j);
            return result;
        };
        set<int> pset,nset;
        for(int r:raw_p)pset.insert(project(r));
        for(int r:raw_n)nset.insert(project(r));
        vector<int> ps(pset.begin(),pset.end()),ns;
        for(int r:nset){
            auto dominates=[&](int v){return !(r&~v);};
            if(none_of(nset.upper_bound(r),nset.end(),dominates))ns.push_back(r);
        }
        Search search;
        auto [gate,status]=search.run(ps,ns,17);
        if(status!=0)return 3;
        cout<<gate<<'\n';
    }
}
