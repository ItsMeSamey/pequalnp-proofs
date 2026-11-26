#include <algorithm>
#include <array>
#include <cstdio>
#include <random>
#include <set>
#include <unordered_set>
#include <vector>
using Graph=std::array<unsigned short,12>;
const int n=12;
const Graph input={1550,401,9,2197,2218,1232,2720,3450,2178,2113,2209,2008};
int parity(int x){return __builtin_parity((unsigned)x);}
Graph complement(Graph g,int v){
    int neighbors=g[v];for(int bits=neighbors;bits;bits&=bits-1){
        int i=__builtin_ctz(bits);g[i]^=neighbors^(1<<i);
    }return g;
}
int defect(const Graph&g,int x){
    int d=0;for(int bits=x;bits;bits&=bits-1){int j=__builtin_ctz(bits);d|=parity(g[j]&x)<<j;}return d;
}
struct Weight{
    int mask=0,rhs=0;
    Graph unsafe{};
    Weight()=default;
    explicit Weight(int encoded){
        mask=(encoded&~1)<<1;rhs=encoded&1;
        for(int x=3;x<(1<<n);x+=4)if(parity(x&mask)!=rhs){
            int d=defect(input,x);
            if(__builtin_popcount((unsigned)d)==2){
                int i=__builtin_ctz(d),j=31-__builtin_clz(d);
                unsafe[i]|=1<<j;unsafe[j]|=1<<i;
            }
        }
    }
    void update(int v,int nb){if(mask&(1<<v)){mask^=nb;rhs^=1;}}
};
bool violates(const Graph&g,const Graph&f,const Weight&w){
    for(int x=3;x<(1<<n);x+=4)if(parity(x&w.mask)!=w.rhs){
        int d=defect(g,x),a=x;bool works=true;
        while(a&&d){
            int component=a&-a,front=component;
            while(front){
                int adj=0;
                for(int b=front;b;b&=b-1)adj|=f[__builtin_ctz(b)];
                front=adj&x&~component;component|=front;
            }
            if(parity(d&component)){works=false;break;}
            d&=~component;a&=~component;
        }
        if(works)return true;
    }
    return false;
}
long long approved=0,tried=0;
std::set<std::array<unsigned short,15>> discovered;std::mt19937 ordergen(152331);
void emit(const Graph&g,const Graph&f,const Weight&w,int cut){
  std::printf("%d %d %d",cut,w.mask,w.rhs);
  for(auto val:g)std::printf(" %d",val);for(auto val:f)std::printf(" %d",val);std::puts("");
}
bool solve(const Graph&g,const Weight&w){
    // Forced-color pairs must be bichromatic. Compress connected color components.
    if(!(g[0]&2))return false;
    Graph required{};
    for(int i=0;i<n;i++)required[i]=g[i]&w.unsafe[i];
    required[0]|=2;required[1]|=1;
    int covered=0,one=0;
    std::vector<int> comps;
    for(int i=0;i<n;i++)if(!(covered>>i&1)){
        int block=1<<i,front=block,c=0;covered|=front;
        while(front){
            if(c)one|=front;
            int adj=0;for(int b=front;b;b&=b-1)adj|=required[__builtin_ctz(b)];
            if(adj&(c?one:covered&~one))return false;
            front=adj&~covered;block|=front;covered|=front;c^=1;
        }
        if(i)comps.push_back(block);
    }
    approved++;
    for(int flip=0;flip<(1<<comps.size());flip++){
        int cut=one;for(int j=0;j<(int)comps.size();j++)if(flip>>j&1)cut^=comps[j];
        int support=w.mask&~3;
        if((support&cut)&&(support&~cut))continue;
        Graph f{};for(int i=0;i<n;i++)f[i]=g[i]&((cut>>i&1)?cut:~cut);
        tried++;
        if(violates(g,f,w))continue;
        std::array<unsigned short,15> key;
        std::copy(g.begin(),g.end(),key.begin());key[12]=w.mask;key[13]=w.rhs;key[14]=cut;
        if(!discovered.insert(key).second)continue;
        emit(g,f,w,cut);
        std::vector<std::pair<int,int>> options;
        for(int i=0;i<12;i++)for(int j=0;j<i;j++)
          if((g[i]>>j&1)&&!(f[i]>>j&1)&&!(w.unsafe[i]>>j&1)&&!(i==1&&j==0))options.push_back({i,j});
        std::shuffle(options.begin(),options.end(),ordergen);auto ext=f;
        for(auto e:options){auto alt=ext;int i=e.first,j=e.second;alt[i]|=1<<j;alt[j]|=1<<i;
          if(!violates(g,alt,w))ext=alt;}
        if(ext!=f)emit(g,ext,w,cut);
    }return false;
}
int main(){
    const std::array<Weight,4> old={Weight(2),Weight(2^775),Weight(2^201),Weight(2^775^201)};
    int inv=0;std::set<Graph> unique;
    for(int id=0;id<59049;id++){
        int pattern=id,chosen[12]={};std::array<int,12> basis{},tracks{};
        auto local=[](int i,int j){return j==0?1<<i:j==1?int(input[i]):(1<<12)^(1<<i)^int(input[i]);};
        bool ok=true;
        for(int i=0;i<12;i++){
            if(i>=2){chosen[i]=pattern%3;pattern/=3;}
            int row=local(i,chosen[i]);int tag=(1<<i)|(row&(1<<12));row&=4095;
            while(row){
                int j=31-__builtin_clz((unsigned)row);
                if(!basis[j]){basis[j]=row;tracks[j]=tag;break;}
                row^=basis[j];tag^=tracks[j];
            }
            if(!row){ok=false;break;}
        }
        if(!ok)continue;inv++;
        auto substitute=[&](int row){
            int result=row&(1<<12);row&=4095;
            while(row){int j=31-__builtin_clz((unsigned)row);row^=basis[j];result^=tracks[j];}
            return result;
        };
        Graph g{};
        for(int i=0;i<12;i++){
            int h=substitute(local(i,(chosen[i]+1)%3));
            if(h>>i&1)h^=(1<<12)|(1<<i);
            if(h>>12){std::fprintf(stderr,"bad offset");return 1;}
            g[i]=h;
        }
        for(int i=0;i<12;i++)for(int j=0;j<i;j++)
            if((g[i]>>j&1)!=(g[j]>>i&1))return 2;
        unique.insert(g);
        if(!(g[0]&2))continue;
        for(auto w:old){
            int f=substitute(w.mask|(w.rhs<<12));w.mask=f&4095;w.rhs=f>>12;
            solve(g,w);
        }
    }
    std::fprintf(stderr,"Invertible charts %d, distinct graph matrices %zu, compatible tests %lld, pure cuts tried %lld, pure cases %zu\n",inv,unique.size(),approved,tried,discovered.size());
}
