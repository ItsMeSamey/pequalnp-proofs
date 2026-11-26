#include <array>
#include <cassert>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <algorithm>
#include <random>

using Poly=unsigned __int128;
int lead(Poly x) {
    auto hi=uint64_t(x>>64);
    return hi?127-__builtin_clzll(hi):63-__builtin_clzll(uint64_t(x));
}
struct Graph{
    int n=8, right=240, target=0;
    std::array<int,12> row{}, label{};
    Graph add(bool onRight,int adjacency,int lab) const {
        Graph y=*this;
        y.n++; y.label[n]=lab;
        if(onRight)y.right|=1<<n;
        int k=0;
        for(int i=0;i<n;i++)if(bool(right&(1<<i))!=onRight){
            if(adjacency&(1<<k)){y.row[i]|=1<<n;y.row[n]|=1<<i;}
            k++;
        }
        return y;
    }
    int sideCount(bool rightSide)const {int r=__builtin_popcount((unsigned)right);return rightSide?r:n-r;}
};
struct Ring{
    int k,cap[4]{},nmono=0;
    std::array<int,256> rank{},mon{};
    std::array<std::array<Poly,128>,8> mul{};
    explicit Ring(int k):k(k){
        for(int d=0;d<=3;d++){
            for(int mask=0;mask<(1<<k);mask++)if(__builtin_popcount((unsigned)mask)==d){
                rank[mask]=nmono;mon[nmono++]=mask;
            }
            cap[d]=nmono;
        }
        assert(nmono<=128);
        for(int i=0;i<k;i++)for(int j=0;j<cap[2];j++)
            mul[i][j]=Poly(1)<<rank[mon[j]|(1<<i)];
    }
    Poly multiply(Poly p,int i)const{
        Poly a=0;
        while(p){int l=lead(p);p^=Poly(1)<<l;a^=mul[i][l];}
        return a;
    }
    Poly product(int p,int q)const{
        Poly out=0;
        for(int a=p;a;a&=a-1)for(int b=q;b;b&=b-1){
            int i=__builtin_ctz(a),j=__builtin_ctz(b);
            out ^= Poly(1)<<rank[((1<<i)>>1)|((1<<j)>>1)];
        }
        return out;
    }
    bool pc(const std::vector<Poly>& rows,int d)const {
        std::array<Poly,128> piv{};
        auto todo=rows;
        while(!todo.empty()){
            Poly p=todo.back();todo.pop_back();
            while(p){
                int j=lead(p);
                if(!piv[j]){
                    if(j==0)return true;
                    piv[j]=p;
                    if(j<cap[d-1])for(int i=0;i<k;i++)todo.push_back(multiply(p,i));
                    break;
                }
                p^=piv[j];
            }
        }
        return false;
    }
};
std::array<Ring,5> rings={Ring(4),Ring(5),Ring(6),Ring(7),Ring(8)};
std::array<long long,5> counts{};
int classify(const Graph& g){
    int basis[3]{},rhs[3]{},cols[3]{},free=0;
    int forms[12]{};
    for(int l=0;l<3;l++){
        int row=0,b=(g.target>>l)&1;
        for(int j=0;j<g.n;j++)row|=((g.label[j]>>l)&1)<<j;
        for(int i=0;i<l;i++)if(row&(1<<cols[i])){row^=basis[i];b^=rhs[i];}
        assert(row);
        cols[l]=__builtin_ctz((unsigned)row);basis[l]=row;rhs[l]=b;
    }
    for(int j=0;j<g.n;j++)if(j!=cols[0]&&j!=cols[1]&&j!=cols[2])forms[j]=1<<(++free);
    for(int l=2;l>=0;l--){
        int rest=basis[l]^(1<<cols[l]),p=rhs[l];
        for(;rest;rest&=rest-1)p^=forms[__builtin_ctz((unsigned)rest)];
        forms[cols[l]]=p;
    }
    auto& ring=rings[free-4];
    std::vector<Poly> polys;
    for(int j=0;j<g.n;j++){
        int p=0,rest=g.row[j];
        for(;rest;rest&=rest-1)p^=forms[__builtin_ctz((unsigned)rest)];
        polys.push_back(ring.product(forms[j],p));
    }
    if(ring.pc(polys,2)){counts[2]++;return 2;}
    for(int y=0;y<(1<<free);y++){
        int x=0;
        for(int j=0;j<g.n;j++)x|=__builtin_parity((unsigned)(forms[j]&((y<<1)|1)))<<j;
        bool ok=true;
        for(int v=x;v;v&=v-1)if(__builtin_parity((unsigned)(g.row[__builtin_ctz((unsigned)v)]&x))){ok=false;break;}
        if(ok){counts[0]++;return 0;}
    }
    if(ring.pc(polys,3)){counts[3]++;return 3;}
    counts[4]++;
    std::printf("NO DEGREE THREE: n=%d right=%d t=%d\nRows",g.n,g.right,g.target);
    for(int i=0;i<g.n;i++) std::printf(" %d",g.row[i]);
    std::printf("\nLabels");for(int i=0;i<g.n;i++)std::printf(" %d",g.label[i]);std::puts("");
    std::exit(0);
}
int main(int argc,char**argv){
    FILE* f=std::fopen(argv[1],"r"); if(!f)return 1;
    int g,h[3],x;
    std::vector<Graph> seeds, pool;
    while(fscanf(f,"%d %d %d %d %d",&g,&h[0],&h[1],&h[2],&x)==5){
        Graph a;
        for(int i=0;i<4;i++)for(int j=0;j<4;j++)if(g&(1<<(4*i+j))){a.row[i]|=1<<(j+4);a.row[j+4]|=1<<i;}
        for(int j=0;j<3;j++){
            a.target |= __builtin_parity((unsigned)(h[j]&x))<<j;
            for(int k=0;k<8;k++)a.label[k] |= (h[j]>>k&1)<<j;
        }
        assert(classify(a)==3);
        seeds.push_back(a);
    }
    assert(seeds.size()==312);
    counts={};
    for(auto &a:seeds)for(bool r:{false,true})for(int adj=0;adj<16;adj++)for(int l=0;l<8;l++){
        auto b=a.add(r,adj,l);if(classify(b)==3)pool.push_back(b);
    }
    std::printf("Single extensions: SAT %lld quadratic %lld cubic %lld\n",counts[0],counts[2],counts[3]);std::fflush(stdout);
    std::mt19937 rng(19731107);
    int rounds=argc>2?std::atoi(argv[2]):500000;
    if(rounds<0) {
        long long satFirst=counts[0];
        assert(counts[2]==0);
        counts={};
        for(const auto& a:pool)for(bool r:{false,true})
            for(int adj=0;adj<(1<<a.sideCount(!r));adj++)for(int l=0;l<8;l++)
                classify(a.add(r,adj,l));
        std::printf("Complete two extensions: SAT %lld quadratic %lld cubic %lld (including %lld SAT pruned)\n",
                    counts[0]+384*satFirst,counts[2],counts[3],384*satFirst);
        return 0;
    }
    std::vector<Graph> hardTen;
    counts={};
    for(int i=0;i<rounds;i++){
        auto a=pool[rng()%pool.size()]; bool r=rng()&1;
        auto b=a.add(r,rng()%(1<<a.sideCount(!r)),rng()%8);
        if(i&1){
            int s=rng()%b.n,t=rng()%b.n;
            if(bool(b.right&(1<<s))!=bool(b.right&(1<<t))){b.row[s]^=1<<t;b.row[t]^=1<<s;}
        }
        if(classify(b)==3 && hardTen.size()<100000)hardTen.push_back(b);
    }
    std::printf("Ten vertex mutation sample: SAT %lld quadratic %lld cubic %lld\n",counts[0],counts[2],counts[3]);std::fflush(stdout);
    counts={};
    for(int i=0;i<rounds;i++){
        auto a=hardTen[rng()%hardTen.size()];bool r=rng()&1;
        auto b=a.add(r,rng()%(1<<a.sideCount(!r)),rng()%8);
        if(i%3==0){int j=rng()%b.n;b.label[j]^=rng()%8;}
        // Reweighting an old vertex can reduce marker rank. Check first.
        bool full=true;
        for(int h=1;h<8;h++){
            bool used=false;for(int j=0;j<b.n;j++)used|=__builtin_parity((unsigned)(h&b.label[j]));
            full &= used;
        }
        if(full)classify(b);
    }
    std::printf("Eleven vertex mutation sample: SAT %lld quadratic %lld cubic %lld\n",counts[0],counts[2],counts[3]);
}
