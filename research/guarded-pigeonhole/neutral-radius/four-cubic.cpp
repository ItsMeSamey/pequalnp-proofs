#include <array>
#include <vector>
#include <cstdio>
#include <cassert>
#include <cstdint>

struct Poly {
    std::array<uint64_t,4> a{};
    void flip(int i){a[i>>6]^=uint64_t(1)<<(i&63);}
    void plus(const Poly& b){for(int i=0;i<4;i++)a[i]^=b.a[i];}
    int lead()const{for(int i=3;i>=0;i--)if(a[i])return 64*i+63-__builtin_clzll(a[i]);return -1;}
};
struct Ring{
    int idx[35][8]{},mul[3][256]{},low=0;
    Ring(int m){
        int n=0;
        for(int d=0;d<=3;d++){
            for(int y=0;y<=m;y++)for(int s=0;s<8;s++)if(__builtin_popcount((unsigned)s)+(y>0)==d)idx[y][s]=n++;
            if(d==2)low=n;
        }
        assert(n<=256);
        for(int y=0;y<=m;y++)for(int s=0;s<8;s++)if(__builtin_popcount((unsigned)s)+(y>0)<3)
            for(int j=0;j<3;j++)mul[j][idx[y][s]]=idx[y][s|(1<<j)];
    }
    void add(Poly& p,int y,int form)const{
        while(form){int bit=__builtin_ctz((unsigned)form);form&=form-1;p.flip(idx[y][(1<<bit)>>1]);}
    }
    bool proves(std::vector<Poly> todo){
        std::array<Poly,256> piv{};
        while(!todo.empty()){
            Poly p=todo.back();todo.pop_back();
            while(true){
                int r=p.lead();if(r<0)break;
                if(piv[r].lead()!=-1){p.plus(piv[r]);continue;}
                if(r==0)return true;
                piv[r]=p;
                if(r<low){
                    std::array<Poly,3> out{};
                    for(int i=0;i<4;i++)for(uint64_t a=p.a[i];a;a&=a-1){
                        int k=64*i+__builtin_ctzll(a);
                        for(int j=0;j<3;j++)out[j].flip(mul[j][k]);
                    }
                    for(auto& z:out)todo.push_back(z);
                }
                break;
            }
        }return false;
    }
};
bool solve(const int l[4],uint64_t mask){
    int piv=0;while(!(l[piv]&4))piv++;
    int forms[4]{},free=0;forms[piv]=1;
    for(int i=0;i<4;i++)if(i!=piv){forms[i]=1<<(++free);if(l[i]&4)forms[piv]^=forms[i];}
    std::vector<int> types;
    for(;mask;mask&=mask-1)types.push_back(__builtin_ctzll(mask));
    Ring ring(types.size());
    std::vector<Poly> rows(6+types.size());
    for(int j=0;j<2;j++)for(int i=0;i<4;i++)if(l[i]>>j&1)ring.add(rows[j],0,forms[i]);
    for(size_t h=0;h<types.size();h++){
        int v=types[h]/4,s=types[h]%4,y=h+1,form=0;
        for(int j=0;j<2;j++)if(s>>j&1)ring.add(rows[j],y,1);
        for(int i=0;i<4;i++)if(v>>i&1){ring.add(rows[2+i],y,forms[i]);form^=forms[i];}
        ring.add(rows[6+h],y,form);
    }
    return ring.proves(rows);
}
int main(int argc,char**argv){
    FILE* in=std::fopen(argv[1],"r");assert(in);
    FILE* fail=argc>2?std::fopen(argv[2],"w"):nullptr;
    int l[4],total=0,good=0;unsigned long long mask;
    while(fscanf(in,"%d %d %d %d %llx",l,l+1,l+2,l+3,&mask)==5){
        total++;if(solve(l,mask))good++;
        else if(fail)std::fprintf(fail,"%d %d %d %d %016llx\n",l[0],l[1],l[2],l[3],mask);
    }std::printf("Restricted cubic %d/%d; unresolved %d\n",good,total,total-good);
}
