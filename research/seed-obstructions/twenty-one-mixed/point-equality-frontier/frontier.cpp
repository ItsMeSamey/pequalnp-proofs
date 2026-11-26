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

using Frontier=array<int,24>; // zero entries are padding
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
static bool colorable(const array<int,24>&adj,int size,int colors){
    // Peel vertices of degree < colors: they always extend a coloring.
    unsigned live=(1u<<size)-1;
    for(bool changed=true;changed;){
        changed=false;
        for(unsigned a=live;a;a&=a-1){
            int v=__builtin_ctz(a);
            if(__builtin_popcount(live&adj[v])<colors){live^=1u<<v;changed=true;}
        }
    }
    if(!live)return true;
    array<unsigned,24> color{};
    auto solve=[&](auto&&rec,unsigned left,unsigned used)->bool{
        if(!left)return true;
        int best=-1,score=-1;unsigned banned=0;
        for(unsigned a=left;a;a&=a-1){
            int v=__builtin_ctz(a);unsigned taken=0;
            for(unsigned b=adj[v]&live&~left;b;b&=b-1)taken|=color[__builtin_ctz(b)];
            int priority=32*__builtin_popcount(taken)+__builtin_popcount(adj[v]&left);
            if(priority>score){score=priority;best=v;banned=taken;}
        }
        unsigned allowed=((1u<<colors)-1)&~banned;
        for(unsigned options=allowed;options;options&=options-1){
            unsigned c=options&-options;color[best]=c;
            if(rec(rec,left^(1u<<best),used|c))return true;
            if(!(c&used))break;
        }
        return false;
    };
    return solve(solve,live,0);
}
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
    bool may_read_once(const Frontier&state,int size){
        // Only obligations uniquely distinguished by one consumed wire can be
        // lost, because either operation preserves an obligation distinguished
        // by both operands. Store the two projections of these private pairs.
        array<Signature,24> need{};
        for(int p=0;p<count_pos;p++)for(int b=0;b<blocks;b++){
            Bits once=0,twice=0,d[24];
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
            if(!(need[i][0]&need[j][0]))continue;
            for(int b=1;b<=blocks;b++)if(need[i][b]&need[j][b])return false;
        }
        return true;
    }
    void next(const Frontier&state,int size,States&ordinary,States*copied,States*doublecopy,int remaining){
        // Only obligations uniquely distinguished by one consumed wire can be
        // lost, because either operation preserves an obligation distinguished
        // by both operands. Store the two projections of these private pairs.
        array<Signature,24> need{};
        for(int p=0;p<count_pos;p++)for(int b=0;b<blocks;b++){
            Bits once=0,twice=0,d[24];
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
        // Once no further use can be retained the remainder is read-once.
        // On each positive a private obligation forces its wire into every
        // accepting minterm; on each negative it lies in every rejecting
        // maxterm. A read-once minterm and maxterm intersect once.
        array<int,24> adj{},degree{};int edges=0;
        for(int i=0;i<size;i++)for(int j=i+1;j<size;j++){
            if(!(need[i][0]&need[j][0]))continue;
            bool conflict=false;
            for(int b=1;b<=blocks;b++)if(need[i][b]&need[j][b]){conflict=true;break;}
            if(conflict){adj[i]|=1u<<j;adj[j]|=1u<<i;degree[i]++;degree[j]++;edges++;}
        }
        if(edges&&!colorable(adj,size,remaining+1))return;
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
                if(!doublecopy&&(unsafeA||unsafeB)&&(!copied||(unsafeA&&unsafeB)))continue;
                int h=combine(a,b,op);
                auto push=[&](States& out,int keep){
                    Frontier n{};int t=0;
                    for(int k=0;k<size;k++)if((k!=i&&k!=j)||k==keep||keep==-2)n[t++]=state[k];
                    n[t++]=h;sort(n.begin(),n.begin()+t);out.insert(n);
                };
                if(!unsafeA&&!unsafeB)push(ordinary,-1);
                if(copied&&!unsafeB&&(remaining!=1||degree[i]==edges))push(*copied,i);
                if(copied&&!unsafeA&&(remaining!=1||degree[j]==edges))push(*copied,j);
                if(doublecopy&&(remaining!=2||degree[i]+degree[j]-((adj[i]>>j)&1)==edges))push(*doublecopy,-2);
            }
        }
    }
    pair<int,int> run(const vector<int>&ps,const vector<int>&ns,int nleaves,int budget,int point_count){
        count_pos=ps.size();count_neg=ns.size();blocks=(count_neg+63)/64;
        assert(count_pos<=64&&blocks<=4);
        Frontier orig{};
        for(int i=0;i<nleaves;i++){
            Signature v{};
            for(int j=0;j<count_pos;j++)if(ps[j]>>i&1)v[0]|=Bits(1)<<j;
            for(int j=0;j<count_neg;j++)if(ns[j]>>i&1)v[1+j/64]|=Bits(1)<<(j%64);
            v[5]=i>=7&&i<7+point_count;
            orig[i]=intern(v);
        }
        sort(orig.begin(),orig.begin()+nleaves);
        vector<States> states(budget+1);states[0].insert(orig);
        for(int gate=1;gate<=nleaves-1+budget;gate++){
            vector<States> following(budget+1);size_t next_cleanup=100000;
            for(int u=0;u<=budget;u++)for(auto&s:states[u]){
                next(s,nleaves-(gate-1)+u,following[u],u<budget?&following[u+1]:nullptr,u+2<=budget?&following[u+2]:nullptr,budget-u);
                if(following[budget].size()>next_cleanup){
                    auto& group=following[budget];
                    for(auto it=group.begin();it!=group.end();){
                        if(may_read_once(*it,nleaves-gate+budget))++it;
                        else it=group.erase(it);
                    }
                    next_cleanup=max<size_t>(100000,2*group.size()+1);
                }
            }
            if(all_of(following.begin(),following.end(),[](const States&x){return x.empty();}))return {gate,0};
            states.swap(following);
        }
        return {nleaves-1+budget,int(states[budget].size())};
    }
};
int main(){
    int p=0,n=0,count=0,point_count=0,line_count=0,budget=0;
    cin>>p>>n;
    if(p!=28||n!=245)return 1;
    vector<int> raw_p(p),raw_n(n);
    for(int&x:raw_p)cin>>x;for(int&x:raw_n)cin>>x;
    cin>>count>>point_count>>line_count>>budget;
    if((point_count!=11&&point_count!=12) || line_count<7 || line_count>10 || budget<0 || budget>5)return 2;
    for(int i=0;i<count;i++){
        vector<int> f(point_count);
        for(int&x:f)if(!(cin>>x)||x<0||x>=8192)return 3;
        array<int,10> lines{};
        for(int j=0;j<line_count;j++)
            if(!(cin>>lines[j])||lines[j]<0||lines[j]>=128)return 4;
        auto project=[&](int r){
            int z=0;
            for(int j=0;j<7;j++)if((r>>13)&lines[j])z|=1<<j;
            for(int j=0;j<point_count;j++)if(r&f[j])z|=1<<(7+j);
            for(int j=7;j<line_count;j++)if((r>>13)&lines[j])z|=1<<(point_count+j);
            return z;
        };
        set<int> pp,nn;
        for(int r:raw_p)pp.insert(project(r));for(int r:raw_n)nn.insert(project(r));
        vector<int> ps(pp.begin(),pp.end()),ns;
        for(int r:nn)if(none_of(nn.upper_bound(r),nn.end(),[&](int q){return !(r&~q);}))ns.push_back(r);
        Search search;auto [gate,status]=search.run(ps,ns,point_count+line_count,budget,point_count);
        if(status!=0){cerr<<"surviving family row "<<i<<" status "<<status<<endl;return 5;}
        cout<<gate<<'\n';
    }
}
