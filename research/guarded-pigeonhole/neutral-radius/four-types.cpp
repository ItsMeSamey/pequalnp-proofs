#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <set>
#include <vector>
using Mask=uint64_t;
using Labels=std::array<int,4>;
int dot(int a,int b){return __builtin_parity((unsigned)(a&b));}
std::vector<Mask> maximal(std::vector<Mask> a){
    std::sort(a.begin(),a.end());a.erase(std::unique(a.begin(),a.end()),a.end());
    std::sort(a.begin(),a.end(),[](Mask p,Mask q){int c=__builtin_popcountll(p),d=__builtin_popcountll(q);return c==d?p<q:c>d;});
    std::vector<Mask> ans;
    for(Mask x:a){bool redundant=false;for(Mask y:ans)if((x&~y)==0){redundant=true;break;}if(!redundant)ans.push_back(x);}
    return ans;
}
Labels canon(Labels a){
    Labels result={8,8,8,8};
    for(int b=1;b<=3;b++)for(int c=1;c<=3;c++)if(b!=c){
        Labels q=a;for(int& s:q)s=(s&4)^((s&1)?b:0)^((s&2)?c:0);
        std::sort(q.begin(),q.end());result=std::min(result,q);
    }return result;
}
int main(int argc,char** argv){
    FILE* out=argc>1?std::fopen(argv[1],"w"):nullptr;
    std::set<Labels> classes;
    for(int k=0;k<4096;k++){
        Labels l;int span=1;
        for(int j=0;j<4;j++){
            l[j]=k>>(3*j)&7;int next=span;
            for(int s=0;s<8;s++)if(span>>s&1)next|=1<<(s^l[j]);span=next;
        }
        if((span&16)||(span&240)==0)continue;
        classes.insert(canon(l));
    }
    long long total=0;int peak=0,maxTypes=0;
    for(auto l:classes){
        std::vector<std::vector<Mask>> clauses;
        for(int p=0;p<16;p++){
            int residual=4;for(int j=0;j<4;j++)if(p>>j&1)residual^=l[j];
            if(residual&4)continue;std::vector<Mask> choices;
            for(int b=1;b<4;b++)if(dot(b,residual))
            for(int a=0;a<16;a++)if((a&~p)==0&&a<(a^p)){
                Mask choice=0;
                for(int v=0;v<16;v++)for(int s=0;s<4;s++)
                    if(dot(v,p)||dot(v,a)==dot(b,s))choice|=Mask(1)<<(4*v+s);
                choices.push_back(choice);
            }
            clauses.push_back(maximal(choices));
        }
        std::sort(clauses.begin(),clauses.end(),[](const auto& a,const auto& b){return a.size()<b.size();});
        std::vector<Mask> masks={~Mask(0)};
        for(auto& row:clauses){
            std::vector<Mask> next;for(Mask a:masks)for(Mask b:row)next.push_back(a&b);
            masks=maximal(next);peak=std::max(peak,(int)masks.size());
        }
        total+=masks.size();
        for(Mask m:masks){
            maxTypes=std::max(maxTypes,__builtin_popcountll(m));
            if(out)std::fprintf(out,"%d %d %d %d %016llx\n",l[0],l[1],l[2],l[3],(unsigned long long)m);
        }
        std::printf("%d%d%d%d %zu\n",l[0],l[1],l[2],l[3],masks.size());std::fflush(stdout);
    }
    std::printf("classes %zu maximal %lld peak %d maxTypes %d\n",classes.size(),total,peak,maxTypes);
}
