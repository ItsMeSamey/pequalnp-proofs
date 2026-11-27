// Enumerate connected five-input AO2 DAGs via their depth-first postfix encodings.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <stdexcept>
#include <string>

#ifndef VERTICES
#define VERTICES 5
#endif
using Word = std::uint64_t;
constexpr int n=VERTICES, max_gates=10;
static_assert(n>=2 && n<=6, "truth table must fit in 64 bits");
struct Gate { int a,b; bool is_and; };
struct Stats { int depth=0; std::uint64_t total=0,dirty=0,topform=0,violations=0; };
struct Search {
    std::array<Word,n+max_gates> val{};
    std::array<Gate,max_gates> gates{};
    std::array<int,n+max_gates> levels{};
    std::array<int,max_gates+1> stack{};
    std::map<Word,int> graphs; // full truth table -> canonical graph edge mask
    std::map<int,Stats> stats;
    int depth=0;
    static int edgebit(int a,int b) {
        if (a>b) std::swap(a,b);
        return 1 << (a*(2*n-1-a)/2+b-a-1);
    }
    Search() {
        for(int i=0;i<n;i++) for(int x=0;x<(1<<n);x++)
            if(x & (1<<i)) val[i] |= Word(1)<<x;
        for(int mask=1;mask<(1<<(n*(n-1)/2));mask++){
            bool square=false;
            for(int a=0;a<n;a++) for(int b=a+1;b<n;b++) {
                int common=0;
                for(int c=0;c<n;c++) if(c!=a && c!=b &&
                    (mask&edgebit(a,c)) && (mask&edgebit(b,c))) ++common;
                if(common>=2) square=true;
            }
            if(square) continue;
            bool active=true;
            for(int a=0;a<n;++a) {
                bool has=false;
                for(int b=0;b<n;++b) if(a!=b && (mask&edgebit(a,b))) has=true;
                active &= has;
            }
            if(!active) continue;
            Word target=0;
            for(int a=0;a<n;a++) for(int b=a+1;b<n;b++)
                if(mask&edgebit(a,b)) target |= val[a]&val[b];
            std::array<int,n> p{}; for(int i=0;i<n;++i) p[i]=i; int key=mask;
            do {
                int transformed=0;
                for(int a=0;a<n;a++) for(int b=a+1;b<n;b++)
                    if(mask&edgebit(a,b)) transformed |= edgebit(p[a],p[b]);
                key=std::min(key,transformed);
            } while(std::next_permutation(p.begin(),p.end()));
            graphs[target]=key;
        }
    }
    void record(Word target){
        auto it=graphs.find(target);
        if(it==graphs.end()) return;
        auto &s=stats[it->second];
        if(s.depth && s.depth<depth) return;
        s.depth=depth; ++s.total;
        bool dirty=false;
        for(int i=0;i<depth;i++)
            if(gates[i].is_and && (val[n+i]&~target)) dirty=true;
        std::array<int,n+max_gates> raw{}, orcone{}, below{};
        int tops=0, centreless=0, junk=0, orn=0, lam=0, star=0, edges=0;
        bool topform=true;
        for(int i=0;i<n;i++) raw[i]=1<<i;
        for(int i=0;i<depth;i++){
            auto [a,b,is_and]=gates[i]; int w=n+i, tag=1<<i;
            below[w]=below[a]|below[b];
            if(a>=n) below[w]|=1<<(a-n);
            if(b>=n) below[w]|=1<<(b-n);
            if(!is_and){
                raw[w]=raw[a]|raw[b]; orcone[w]=orcone[a]|orcone[b]|tag;
                if(val[w]&~target) orn|=tag;
                continue;
            }
            if(below[w]&tops) topform=false;
            if(val[w]&~target){junk|=tag;continue;}
            tops|=tag;
            if(!raw[a] || !raw[b]) centreless|=tag;
            for(int x=0;x<n;x++) for(int y=0;y<n;y++)
                if(x!=y && (raw[a]&(1<<x)) && (raw[b]&(1<<y))) star|=edgebit(x,y);
            for(int h=0;h<i;h++) if(orn&(1<<h)){
                auto side=gates[h];
                if(raw[side.a] && raw[side.b] &&
                   (((orcone[a]&(1<<h)) && __builtin_popcount(raw[b])==1) ||
                    ((orcone[b]&(1<<h)) && __builtin_popcount(raw[a])==1))) lam|=1<<h;
            }
        }
        for(int a=0;a<n;a++) for(int b=a+1;b<n;b++)
            if(target&(Word(1)<<((1<<a)|(1<<b)))) edges|=edgebit(a,b);
        int tau=n;
        for(int v=0;v<(1<<n);v++){
            bool cover=true;
            for(int a=0;a<n;a++) for(int b=a+1;b<n;b++)
                if((edges&edgebit(a,b)) && !(v&((1<<a)|(1<<b)))) cover=false;
            if(cover) tau=std::min(tau,__builtin_popcount(static_cast<unsigned>(v)));
        }
        int lhs=tau+__builtin_popcount(edges&~star);
        int rhs=__builtin_popcount(tops)+__builtin_popcount(centreless)+
                __builtin_popcount(junk)+__builtin_popcount(orn&~lam);
        if(topform) ++s.topform;
        bool first_violation=topform && lhs>rhs && !s.violations++;
        bool first_dirty=dirty && !s.dirty++;
        bool short_benchmark=depth < __builtin_popcount(edges)+tau-1;
        if(first_dirty || first_violation || (short_benchmark && s.total==1)){
            std::cout<<"candidate "<<it->second<<" lhs "<<lhs<<" rhs "<<rhs<<" topform "<<topform<<" short_benchmark "<<short_benchmark<<" truth "<<target<<" gates";
            for(int i=0;i<depth;i++)
                std::cout<<" "<<(gates[i].is_and?"A":"O")<<","<<gates[i].a<<","<<gates[i].b;
            std::cout<<std::endl;
        }
    }
    void dfs(int used,int height,int leaves,int inputs){
        if(inputs+(depth+1-leaves)<n) return;
        if(used==depth){ if(inputs==n && height==1) record(val[n+used-1]); return; }
        if(leaves<depth+1){
            // Each input is either already seen or is the next fresh label.
            for(int i=0;i<std::min(inputs+1,n);i++){
                stack[height]=i;
                dfs(used,height+1,leaves+1,std::max(inputs,i+1));
            }
            for(int i=0;i<used;i++){
                stack[height]=n+i;
                dfs(used,height+1,leaves+1,inputs);
            }
        }
        if(height<2) return;
        int a=stack[height-2], b=stack[height-1];
        // Bigger-depth child is traversed first. Depth is intrinsic to the
        // DAG and invariant under the canonical first-use renaming of inputs.
        // A raw/raw pair is visited in increasing first-use label order.
        if(levels[a]<levels[b] || (a<n && b<n && a>b)) return;
        if(a>=n && b>=n && levels[a]==levels[b]){
            // Label-independent intrinsic truth weights canonically break equal depth.
            if(__builtin_popcountll(val[a])<__builtin_popcountll(val[b])) return;
        }
        Word x=val[a],y=val[b];
        for(bool is_and : {true,false}){
            Word z=is_and ? x&y : x|y;
            if(std::find(val.begin(),val.begin()+n+used,z)!=val.begin()+n+used) continue;
            if(used+1==depth && !graphs.count(z)) continue;
            gates[used]={a,b,is_and};
            val[n+used]=z; levels[n+used]=1+std::max(levels[a],levels[b]); stack[height-2]=n+used;
            dfs(used+1,height-1,leaves,inputs);
            stack[height-2]=a; stack[height-1]=b;
        }
    }
};
int main(int argc,char**argv){
    int lo=argc>1?std::stoi(argv[1]):4, hi=argc>2?std::stoi(argv[2]):7;
    if(lo<1 || hi>max_gates || lo>hi) throw std::invalid_argument("usage: connected4186 [min_depth max_depth], 1..7");
    Search s;
    for(s.depth=lo;s.depth<=hi;++s.depth){
        s.dfs(0,0,0,0);
        for(auto &[key,v]:s.stats) if(v.depth==s.depth)
            std::cout<<"first-in-range "<<key<<" gates "<<v.depth<<" encodings "<<v.total<<" dirty "<<v.dirty<<" topform "<<v.topform<<" violations "<<v.violations<<"\n";
        std::cout<<"completed "<<s.depth<<std::endl;
    }
}
