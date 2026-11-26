#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <vector>

using namespace std;
constexpr int axes=8, terminalAxes=6, literalCount=16, maskCount=1<<literalCount;
using Key=pair<int,int>;
struct Cube {
    array<uint64_t,4> v{};
    void set(int p){v[p/64]|=uint64_t(1)<<(p%64);}
    int size()const{return popcount(v[0])+popcount(v[1])+popcount(v[2])+popcount(v[3]);}
    bool overlaps(const Cube& b)const{return (v[0]&b.v[0])|(v[1]&b.v[1])|(v[2]&b.v[2])|(v[3]&b.v[3]);}
    bool subset(const Cube& b)const{return !((v[0]&~b.v[0])|(v[1]&~b.v[1])|(v[2]&~b.v[2])|(v[3]&~b.v[3]));}
    Cube intersect(const Cube& b)const{return {{{v[0]&b.v[0],v[1]&b.v[1],v[2]&b.v[2],v[3]&b.v[3]}}};}
    Cube join(const Cube& b)const{return {{{v[0]|b.v[0],v[1]|b.v[1],v[2]|b.v[2],v[3]|b.v[3]}}};}
    auto operator<=>(const Cube&)const=default;
};
bool consistent(int m){return !(m&(m>>1)&0x5555);}
Key canonical(int a,int b){
    array<pair<int,int>,terminalAxes> c{};
    for(int j=2;j<axes;j++){
        int x=(a>>(2*j))&3,y=(b>>(2*j))&3;
        if(x==2||(!x&&y==2)){x=((x>>1)|x<<1)&3;y=((y>>1)|y<<1)&3;}
        c[j-2]={x,y};
    }
    sort(c.begin(),c.end());int x=a&15,y=0;
    for(int j=0;j<terminalAxes;j++){x|=c[j].first<<(4+2*j);y|=c[j].second<<(4+2*j);}
    return {x,y};
}
vector<Key> makeTemplates(){
    set<Key> result;vector<int> terms;
    for(int m=0;m<maskCount;m+=16)if(consistent(m)) terms.push_back(m);
    for(int dep:{0,4,12})for(int a:terms)for(int b:terms){
        if(!b||(!a&&!dep)||(dep==12&&!consistent(a|b)))continue;
        Key k=canonical(a|dep,b);if(!dep)k=min(k,canonical(b,a));
        result.insert(k);
    }
    return {result.begin(),result.end()};
}
struct Template {
    Key t;vector<Cube> deficit;vector<uint32_t> parity;
    explicit Template(Key k):t(k),deficit(maskCount),parity(maskCount){
        deficit[0].v.fill(~uint64_t(0));
        for(int j=0;j<literalCount;j++)for(int p=0;p<256;p++){
            int m=1<<j;
            if(m&(1<<(p&1)))m|=t.first;
            if(m&(1<<(2+((p>>1)&1))))m|=t.second;
            bool hit=false;
            for(int a=2;a<axes;a++)if(m&(1<<(2*a+((p>>a)&1))))hit=true;
            if(!hit)deficit[1<<j].set(p);
        }
        for(int m=1;m<maskCount;m++){
            if(!has_single_bit((unsigned)m))deficit[m]=deficit[m&-m].intersect(deficit[m&(m-1)]);
            int r=m;if((r&3)==3)r|=t.first;if((r&12)==12)r|=t.second;
            uint32_t z=0;int pos=0;
            for(int a=2;a<axes;a++)for(int b=a+1;b<axes;b++,pos+=2){
                int sa=(r>>(2*a))&3,sb=(r>>(2*b))&3;
                if(sa&&sb&&sa!=3&&sb!=3)z|=uint32_t(1)<<(pos+(sa!=sb));
            }
            parity[m]=z;
        }
    }
};
struct Candidate{int m;Cube d;int volume;uint32_t cover;};
constexpr uint32_t allPairs=(uint32_t(1)<<30)-1;
bool pack(vector<Candidate>const&c,int start,int count,Cube used,uint32_t required){
    if(!count)return !required;
    uint32_t cover=0;int room=256-used.size(),sum=0,available=0;
    for(int i=start;i<(int)c.size();i++)if(!used.overlaps(c[i].d)){
        if(available<count)sum+=c[i].volume;
        ++available;cover|=c[i].cover;
    }
    if(available<count||sum>room||(required&~cover))return false;
    for(int i=start;i+count<=(int)c.size();i++){
        if(c[i].volume*count>room)break;
        if(!used.overlaps(c[i].d)&&pack(c,i+1,count-1,used.join(c[i].d),required&~c[i].cover))return true;
    }
    return false;
}
using TreeList=vector<vector<int>>;
map<int,TreeList> cache;
const TreeList& trees(int m){
    auto [it,fresh]=cache.try_emplace(m);auto&r=it->second;if(!fresh)return r;
    if(has_single_bit((unsigned)m)){r.emplace_back();return r;}
    for(int a=(m-1)&m;a;a=(a-1)&m){int b=m^a;if(a>b)continue;
        for(auto&l:trees(a))for(auto&u:trees(b)){vector<int> v=l;v.insert(v.end(),u.begin(),u.end());v.push_back(m);r.push_back(v);}
    }
    return r;
}
int main(int argc,char**argv){
    auto templates=makeTemplates();
    if(argc<2){cout<<templates.size()<<" templates\n";return 0;}
    int w=atoi(argv[1]),lo=argc>2?atoi(argv[2]):0,hi=argc>3?atoi(argv[3]):templates.size();bool parity=argc<=4||atoi(argv[4]);
    for(int index=lo;index<min(hi,(int)templates.size());index++){
        auto t=templates[index];if(popcount((unsigned)t.first)!=w)continue;
        Template q(t);long long anchors=0,banks=0,volume=0,hits=0;
        for(int e=4;e<maskCount;e+=4){
            if((e&t.first)||popcount((unsigned)e)!=6-w)continue;
            int K=e|3;if(!q.deficit[K].size())continue;++anchors;
            for(auto&x:trees(t.first))for(auto&y:trees(K)){
                ++banks;vector<int> bank;
                for(int j=0;j<literalCount;j++)bank.push_back(1<<j);
                bank.insert(bank.end(),x.begin(),x.end());bank.insert(bank.end(),y.begin(),prev(y.end()));
                vector<int> out;for(int a:bank)for(int b:bank)if(a<b)out.push_back(a|b);
                sort(out.begin(),out.end());out.erase(unique(out.begin(),out.end()),out.end());
                vector<Candidate> c;
                for(int m:out){
                    Cube z=q.deficit[m];int v=z.size();if(popcount((unsigned)m)<2||!v||z.overlaps(q.deficit[K]))continue;
                    c.push_back({m,z,v,parity?q.parity[m]:0});
                }
                sort(c.begin(),c.end(),[](auto&a,auto&b){return a.volume!=b.volume?a.volume<b.volume:a.m<b.m;});
                vector<Candidate> small;
                for(auto&x:c){bool drop=false;for(auto&z:small)if(z.d.subset(x.d)&&!(x.cover&~z.cover)){drop=true;break;}if(!drop)small.push_back(x);}
                if(small.size()<11)continue;
                int total=q.deficit[K].size();for(int i=0;i<11;i++)total+=small[i].volume;if(total>256)continue;
                ++volume;if(pack(small,0,11,q.deficit[K],parity?allPairs&~q.parity[K]:0)){++hits;cout<<"candidate "<<index<<" "<<K<<endl;}
            }
        }
        cout<<index<<" "<<t.first<<" "<<t.second<<" "<<anchors<<" "<<banks<<" "<<volume<<" "<<hits<<endl;
    }
    return 0;
}
