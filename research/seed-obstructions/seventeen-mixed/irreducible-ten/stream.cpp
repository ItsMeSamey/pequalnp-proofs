#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <set>
#include <vector>
using namespace std;
constexpr int W=10,A=8191,B=21;
using U=uint64_t;
using Row=array<int,W>;
using Bits=array<U,B>;
struct R{int a,b;};vector<R> rows;Bits pos[8192]{},neg[8192]{},full{};
uint64_t family_count=0,nodes=0;Row anchors{},excluded{};
void visit(Row yes,Row no){
 if(++nodes%1000000==0)cerr<<nodes<<" "<<family_count<<endl;
 int slot=-1,bit=0;
 for(;;){
  // Sort extra masks and assign each anchor its least witnessing mask.
  for(int i=7;i+1<W;i++)if(yes[i]>(A^no[i+1]))return;
  for(int j=7;j<W;j++)for(int i=0;i<7;i++){
   if(!(anchors[i]&~yes[j]) && !(excluded[i]&~no[j]) && (A^no[j])<yes[i])return;
  }
  Bits can[W],got[W],others[W],sole[W];
  bool change=false;int selected=-1,best=W+1;
  for(int z=0;z<B;z++){
   // c/g mean covered by at least one possible/guaranteed witness.
   // mc/mg track the same events with at least two witnesses.
   U c=0,mc=0,g=0,mg=0;
   for(int i=0;i<W;i++){
    U x=can[i][z]=pos[A^no[i]][z]&neg[yes[i]][z];
    U y=got[i][z]=pos[yes[i]][z]&neg[A^no[i]][z];
    mc|=c&x;c|=x;mg|=g&y;g|=y;
   }
   if(c!=full[z])return;
   for(int i=0;i<W;i++){
    // Obligations still eligible to become private to i.
    others[i][z]=can[i][z]&~(mg|(g&~got[i][z]));
    // Unresolved obligations with i as their sole possible witness.
    sole[i][z]=can[i][z]&~(mc|g);
   }
   if(best==2)continue;
   U opt=full[z]&~g&mc;
   while(opt){
    int b=countr_zero(opt),ct=0;
    for(int i=0;i<W&&ct<best;i++)ct+=(can[i][z]>>b)&1;
    if(ct<best){best=ct;selected=z*64+b;}
    opt&=opt-1;
    if(best==2)break;
   }
  }
  for(int i=0;i<W;i++){
   int must=A,ban=A,forced=0,avoid=0;bool has=false;
   for(int z=0;z<B;z++){
    U v=sole[i][z];
    while(v){
     auto r=rows[64*z+countr_zero(v)];v&=v-1;forced|=r.a;avoid|=r.b;
    }
    v=others[i][z];has|=bool(v);
    while(v&&(must||ban)){
     auto r=rows[64*z+countr_zero(v)];v&=v-1;must&=r.a;ban&=r.b;
    }
   }
   if(!has)return;
   // Every final slot must have a private witness; all candidate witnesses
   // agree on the positive and negative bits accumulated by intersection.
   forced|=must;avoid|=ban;
   if((forced|yes[i])&(avoid|no[i]))return;
   if((forced&~yes[i])||(avoid&~no[i])){yes[i]|=forced;no[i]|=avoid;change=true;}
  }
  if(change)continue;
  if(selected>=0){
   auto r=rows[selected];
   for(slot=0;slot<W;slot++)if(!((r.a&no[slot])|(r.b&yes[slot])))break;
   int free=(r.a|r.b)&~(yes[slot]|no[slot]);bit=free&-free;
  }else{
   for(slot=0;slot<W;slot++){int f=A&~(yes[slot]|no[slot]);if(f){bit=f&-f;break;}}
   if(slot==W){sort(yes.begin(),yes.end());++family_count;for(int x:yes)cout<<x<<' ';cout<<'\n';return;}
  }
  break;
 }
 Row alt=yes;alt[slot]|=bit;visit(alt,no);no[slot]|=bit;visit(yes,no);
}
int main(){
 int tmp;for(int i=0;i<7;i++)cin>>tmp;Row y{},n{};for(int i=0;i<7;i++)cin>>y[i]>>n[i];
 anchors=y;excluded=n;int a,b;while(cin>>a>>b)rows.push_back({a,b});if(rows.size()!=1323)return 1;
 for(int j=0;j<(int)rows.size();j++){
  auto r=rows[j];U s=U(1)<<(j%64);full[j/64]|=s;
  for(int v=0;v<=A;v++){
   if(v&r.a)pos[v][j/64]|=s;
   if(!(v&r.b))neg[v][j/64]|=s;
  }
 }
 visit(y,n);cerr<<"DONE "<<nodes<<" "<<family_count<<endl;
}
