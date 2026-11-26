#ifndef HEREDITARY_HPP
#define HEREDITARY_HPP
#include <array>
#include <algorithm>
#include <bit>
#include <cstdint>
namespace hereditary {
using Word=unsigned __int128;using Mask=std::array<int,11>;
int target[7],touch[8192],rich[8192],part[7][8192];uint32_t subraw[8192],superraw[8192];Word subsets[128],permitted[7][128];
void setup(){
 int raw[31],n=0;
 for(int i=0;i<13;i++)raw[n++]=1<<i;
 for(int l=0;l<13;l++){
    int a=(1<<l)|(1<<((l+1)%13)),b=(1<<((l+3)%13))|(1<<((l+9)%13));
    if(l<6){raw[n++]=a;raw[n++]=b;raw[n++]=a|b;}else target[l-6]=a|b;
 }
 for(int m=0;m<8192;m++){
   for(int j=0;j<n;j++){
    if(!(raw[j]&~m))subraw[m]|=uint32_t(1)<<j;
    if(!(m&~raw[j]))superraw[m]|=uint32_t(1)<<j;
   }
   for(int t=0;t<7;t++){
    int z=m&target[t];if(z)touch[m]|=1<<t;
    if(std::popcount((unsigned)z)>=2)rich[m]|=1<<t;
    int q=0;for(int b=target[t];b;b&=b-1,q++)if(m&(b&-b))part[t][m]|=1<<q;
   }
 }
 for(int a=0;a<128;a++)for(int j=0;j<128;j++)if(!(j&~a))subsets[a]|=Word(1)<<j;
 for(int t=0;t<7;t++)for(int bad=0;bad<128;bad++)permitted[t][bad]=subsets[127^bad]&~subsets[127^(1<<t)];
}
struct Counter{
 Word plane[6]{};
 void add(Word x){for(int i=0;x;i++){Word carry=x&plane[i];plane[i]^=x;x=carry;}}
 int max()const{Word avail=~Word(0);int mx=0;for(int i=5;i>=0;i--){Word x=avail&plane[i];if(x){avail=x;mx|=1<<i;}else avail&=~plane[i];}return mx;}
};
template<bool exact=false> int bound(const Mask&lo,const Mask&hi){
 Counter votes;
 for(int i=0;i<11;i++)if(!(subraw[hi[i]]&superraw[lo[i]]))votes.add(subsets[127^rich[hi[i]]]);
 for(int t=0;t<7;t++){
    Word one=0,two=0,three=0,pairs[16]{};int supers[11],ns=0;
    for(int i=0;i<11;i++){
        int p=part[t][lo[i]],sz=std::popcount((unsigned)p);if(sz<2)continue;
        Word ok=permitted[t][touch[hi[i]&~target[t]]];one|=ok;
        if(sz>=3)two|=ok;else pairs[p]|=ok;
        if(sz==4){three|=ok;supers[ns++]=i;}
    }
    two|=(pairs[3]&pairs[12])|(pairs[5]&pairs[10])|(pairs[6]&pairs[9]);
    for(int i=0;i<ns;i++)for(int j=0;j<i;j++){Word ok=permitted[t][touch[(hi[supers[i]]&hi[supers[j]])&~target[t]]];one|=ok;two|=ok;}
    votes.add(one);votes.add(two);votes.add(three);
 }
 return exact?votes.max():bool(votes.plane[4]|votes.plane[5]);
}
}
#endif
