#include <algorithm>
#include <array>
#include <cstdio>
#include <vector>
#include <cstdint>

struct Flat {
    std::array<unsigned char,32> at{};
    std::array<unsigned long long,4> set{};
};
std::vector<Flat> flats() {
    std::vector<Flat> all;
    for(int u=0;u<6;u++)for(int v=u+1;v<7;v++)for(int w=v+1;w<8;w++) {
        int piv[]={u,v,w};
        std::vector<int> free;
        std::vector<std::pair<int,int>> pos;
        for(int j=0;j<8;j++) if(j!=u&&j!=v&&j!=w) {
            free.push_back(j);
            for(int i=0;i<3;i++)if(piv[i]<j)pos.push_back({i,j});
        }
        for(int mask=0;mask<(1<<pos.size());mask++) {
            int row[3]={};
            for(size_t k=0;k<pos.size();k++)if(mask>>k&1)row[pos[k].first]|=1<<pos[k].second;
            for(int rhs=0;rhs<8;rhs++){
                Flat flat;
                for(int y=0;y<32;y++){
                    int x=0;
                    for(int k=0;k<5;k++) x|=(y>>k&1)<<free[k];
                    for(int k=0;k<3;k++)x|=((rhs>>k&1)^__builtin_parity(row[k]&x))<<piv[k];
                    flat.at[y]=x;
                    flat.set[x>>6]|=1ULL<<(x&63);
                }
                all.push_back(flat);
            }
        }
    }
    return all;
}

struct Ring {
    int rank[32], mon[32];
    Ring() {
        int n=0;
        for(int k=0;k<=5;k++)for(int m=0;m<32;m++)if(__builtin_popcount((unsigned)m)==k) {
            rank[m]=n; mon[n++]=m;
        }
    }
    uint32_t form(uint32_t c) const {
        constexpr uint32_t masks[]={0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000};
        for(int j=0;j<5;j++) c ^= (c<<(1<<j))&masks[j];
        uint32_t p=0;
        for(;c;c&=c-1)p|=1u<<rank[__builtin_ctz(c)];
        return p;
    }
    uint32_t mult(int j,uint32_t p) const {
        uint32_t q=0;
        for(;p;p&=p-1) q ^= 1u<<rank[mon[__builtin_ctz(p)]|(1<<j)];
        return q;
    }
    bool proves(const std::array<uint32_t,8>& guards,int degree) const {
        uint32_t piv[32]={};int cap=degree==2?6:16;
        std::vector<uint32_t> todo;
        for(uint32_t g:guards)todo.push_back(form(g));
        while(!todo.empty()) {
            uint32_t x=todo.back();todo.pop_back();
            while(x) {
                int p=31-__builtin_clz(x);
                if(piv[p]){x^=piv[p];continue;}
                if(x==1)return true;
                piv[p]=x;
                if(p<cap)for(int j=0;j<5;j++)todo.push_back(mult(j,x));
                break;
            }
        }
        return false;
    }
};

int main(int argc,char**) {
    auto all=flats();
    static const Ring ring;
    long long nos=0,d2=0,d3=0; int count=0;
    for(int g=0;g<65536;g++) {
        int p[]={0,1,2,3},q[]={0,1,2,3};
        bool canon=true;
        do {do {
            int m=0;
            for(int i=0;i<4;i++)for(int j=0;j<4;j++)m|=(g>>(4*i+j)&1)<<(4*p[i]+q[j]);
            if(m<g){canon=false;break;}
        }while(std::next_permutation(q,q+4));}while(canon&&std::next_permutation(p,p+4));
        if(!canon)continue;
        count++;
        int viol[256]={}; unsigned long long models[4]={};
        for(int x=0;x<256;x++){
            for(int i=0;i<4;i++)for(int j=0;j<4;j++)
                if((g>>(4*i+j)&1)&&(x>>i&1)&&(x>>(j+4)&1))viol[x]^=(1<<i)|(1<<(j+4));
            if(!viol[x])models[x>>6]|=1ULL<<(x&63);
        }
        for(const auto& flat:all) {
            if((flat.set[0]&models[0])||(flat.set[1]&models[1])||(flat.set[2]&models[2])||(flat.set[3]&models[3]))continue;
            nos++;
            std::array<uint32_t,8> guards{};
            for(int t=0;t<32;t++)for(int k=0;k<8;k++)guards[k]|=uint32_t(viol[flat.at[t]]>>k&1)<<t;
            if(ring.proves(guards,2)){d2++;continue;}
            if(ring.proves(guards,3)){
                if(argc>1){
                    std::array<int,3> h{};int sz=0;
                    for(int a=1;a<256&&sz<3;a++){
                        bool normal=true;
                        for(int x:flat.at)if(__builtin_parity((x^flat.at[0])&a)){normal=false;break;}
                        if(!normal || (sz==2&&a==(h[0]^h[1])))continue;
                        h[sz++]=a;
                    }
                    std::printf("%d %d %d %d %d\n",g,h[0],h[1],h[2],flat.at[0]);
                }
                if(argc==1&&!d3){std::printf("First cubic g=%d flat",g);for(int a:flat.at)std::printf(" %d",a);std::puts("");}
                d3++;continue;
            }
            std::printf("Degree >3 g=%d flat",g);for(int a:flat.at)std::printf(" %d",a);std::puts("");return 1;
        }
    }
    std::printf("%d graph classes; %zu 5-flats per graph; %lld NO; %lld quadratic; %lld exactly cubic\n",count,all.size(),nos,d2,d3);
}
