#include <array>
#include <cstdint>
#include <iostream>
#include <vector>
#include <algorithm>
using namespace std;
using M = uint16_t;
constexpr M identity=0x8421;
array<int,65536> phi;
array<array<M,16>,65536> combination;
array<unsigned long long,17> visits{};
array<M,16> basis{},best{};
int dimension=0;

M mul(M x,M y){
    auto &t=combination[y];
    return t[x&15] | (t[(x>>4)&15]<<4) | (t[(x>>8)&15]<<8) | (t[x>>12]<<12);
}
bool compatible(M x,M y){
    return phi[x^y]>=0 && phi[x^y]==(phi[x]^phi[y]);
}
int pivot(M v){return 31-__builtin_clz(unsigned(v));}

void search(const vector<M>& options,int depth){
    visits[depth]++;
    if(depth==4){
        for(int i=0;i<4;i++) for(int j=0;j<4;j++)
            if(mul(basis[i],basis[j])!=0) abort();
        cout<<"zero-product extremizer through "<<basis[0]<<"\n";
    }
    if(depth>dimension){
        dimension=depth;
        copy_n(basis.begin(),depth,best.begin());
    }
    for(size_t i=0;i<options.size();i++){
        M x=options[i];
        int p=pivot(x);
        vector<M> next;
        for(size_t j=i+1;j<options.size();j++){
            M y=options[j];
            if(pivot(y)>p && !(y&(1u<<p)) && compatible(x,y)) next.push_back(y);
        }
        basis[depth]=x;
        search(next,depth+1);
    }
}

int main(){
    for(int y=0;y<65536;y++) for(int k=1;k<16;k++){
        int j=__builtin_ctz(unsigned(k));
        combination[y][k]=combination[y][k&(k-1)]^((y>>(4*j))&15);
    }
    vector<M> valid;
    phi.fill(-1);
    for(int v=0;v<65536;v++){
        array<int,4> row{};
        for(int i=0;i<4;i++) row[i]=((v>>(4*i))&15)|(1<<(i+4));
        bool ok=true;
        for(int j=0;j<4;j++){
            int k=j;
            while(k<4 && !(row[k]&(1<<j))) k++;
            if(k==4){ ok=false;break; }
            swap(row[k],row[j]);
            for(int i=0;i<4;i++) if(i!=j && (row[i]&(1<<j))) row[i]^=row[j];
        }
        if(ok){
            M inv=0;
            for(int i=0;i<4;i++) inv|=(row[i]>>4)<<(4*i);
            if(mul(v,inv)!=identity || mul(inv,v)!=identity) return 1;
            phi[v^identity]=inv^identity;
            if(v!=identity) valid.push_back(v^identity);
        }
    }
    sort(valid.begin(),valid.end());
    array<bool,65536> seen{};
    int orbits=0, covered=0;
    for(M a:valid){
        if(seen[a]) continue;
        vector<M> orbit{a};
        seen[a]=true;
        for(size_t k=0;k<orbit.size();k++){
            for(int i=0;i<4;i++) for(int j=0;j<4;j++) if(i!=j){
                M g=identity^(1u<<(4*i+j));
                M z=mul(mul(g,orbit[k]),g);
                if(phi[z]<0) return 2;
                if(!seen[z]){seen[z]=true;orbit.push_back(z);}
            }
        }
        vector<M> opt;
        for(M x:valid) if(!(x&(1u<<pivot(a))) && compatible(x,a)) opt.push_back(x);
        basis[0]=a;
        search(opt,1);
        cout<<"first "<<a<<" orbit "<<orbit.size()<<" quotient candidates "<<opt.size()<<'\n';
        orbits++; covered+=orbit.size();
    }
    cout<<"orbits "<<orbits<<" nonzero covered "<<covered<<" maximum "<<dimension<<" basis";
    for(int i=0;i<dimension;i++) cout<<" "<<best[i];
    cout<<"\nvisited";
    for(int i=1;i<=dimension;i++) cout<<" "<<visits[i];
    cout<<'\n';
    return covered==20159?0:3;
}
