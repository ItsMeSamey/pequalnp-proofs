/* C99. FIRST SECOND_START SECOND_END [THIRD_START THIRD_END].
   Reference smoke: 0 0 1 0 1 prints "leaf 0 0 0 states 135".
   Mixed conjunctions: at depth 3 at most 8*11+7=95 distinct masks.
   Candidate unions: at most C(95,2)=4465. */
#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <limits.h>
typedef uint64_t mask;
enum { MAXOP=95, MAXUNION=4465, MAXTAP=190 };
#define LOW UINT64_C(65535)
#define FULL ((UINT64_C(1)<<40)-1)
static const mask raw[11]={2147418115,663661903884,34144976944,728266375360,
21653750532,103293914128,26322415680,344922804352,414195942664,581968119809,1065151898146};
typedef struct {mask a[MAXUNION];int n;} Gates;
typedef struct {mask op[MAXOP];unsigned clean[MAXOP],joined;int n,c;} Bank;
static Gates stage[4];
static unsigned char bits[65536];
static int cmp64(const void *p,const void *q) {
    mask a=*(const mask *)p,b=*(const mask *)q;return (a>b)-(a<b);
}
static int cmp_tap(const void *p,const void *q) {
    unsigned a=*(const unsigned *)p,b=*(const unsigned *)q;
    if(bits[a]!=bits[b])return (int)bits[b]-(int)bits[a];
    return (a>b)-(a<b);
}
static int uniq(mask *a,int n) {
    int k=0;
    qsort(a,n,sizeof(*a),cmp64);
    for(int i=0;i<n;i++)if(!k||a[i]!=a[k-1])a[k++]=a[i];
    return k;
}
static int contains(const mask *a,int n,mask z) {
    int l=0,r=n;
    while(l<r){int m=(l+r)/2;if(a[m]<z)l=m+1;else r=m;}
    return l<n&&a[l]==z;
}
static void add(Bank *b,mask x) {
    if(x>>16){if(x&LOW)b->op[b->n++]=x;}
    else if(bits[(unsigned)x]>=2) {
        b->clean[b->c++]=(unsigned)x;b->joined|=(unsigned)x;
    }
}
static void generate(int depth,const mask *prefix,Bank *b) {
    Gates *g=&stage[depth]; mask p[8]={FULL};
    b->n=b->c=0;b->joined=0;g->n=0;
    for(int s=0;s<(1<<depth);s++){
        if(s){p[s]=p[s&(s-1)]&prefix[__builtin_ctz((unsigned)s)];add(b,p[s]);}
        for(int j=0;j<11;j++)add(b,p[s]&raw[j]);
    }
    b->n=uniq(b->op,b->n);
    for(int i=0;i<b->n;i++)for(int j=i+1;j<b->n;j++){
        mask z=b->op[i]|b->op[j];
        if(!contains(b->op,b->n,z))g->a[g->n++]=z;
    }
    g->n=uniq(g->a,g->n);
}
static int ordered(mask z,int d,const mask *prefix) {
    for(int i=0;i<d;i++)if(z<prefix[i]&&contains(stage[i].a,stage[i].n,z))return 0;
    return 1;
}
static int savings(const unsigned *ms,int n,int start,unsigned covered,int used) {
    int saved=(int)bits[covered]-used;
    if(saved>=9)return 1;
    if(used==7)return 0;
    int gains[16]={0};unsigned all=covered;
    for(int i=start;i<n;i++){
        int k=bits[ms[i]&~covered];if(k>=2){gains[k-1]++;all|=ms[i];}
    }
    if((int)bits[all]-used-1<9)return 0;
    int bound=saved,slots=7-used;
    for(int g=15;g&&slots;g--){
        int t=gains[g]<slots?gains[g]:slots;bound+=t*g;slots-=t;
    }
    if(bound<9)return 0;
    for(int i=start;i<n;i++)if(bits[ms[i]&~covered]>=2&&savings(ms,n,i+1,covered|ms[i],used+1))return 1;
    return 0;
}
static int hit(const Bank *b,mask z) {
    unsigned all=b->joined,ms[MAXTAP];int n=b->c;
    for(int i=0;i<n;i++)ms[i]=b->clean[i];
    for(int i=0;i<b->n;i++){
        mask m=b->op[i]&z;
        if(!(m>>16)&&bits[(unsigned)m]>=2){all|=(unsigned)m;ms[n++]=(unsigned)m;}
    }
    if(bits[all]<10)return 0;
    qsort(ms,n,sizeof(*ms),cmp_tap);
    int k=0;
    for(int i=0;i<n;i++){
        unsigned x=ms[i];int j=0;
        while(j<k&&(x&ms[j])!=x)j++;
        if(j==k)ms[k++]=x;
    }
    return savings(ms,k,0,0,0);
}
static int number(const char *s) {
    char *end;errno=0;long x=strtol(s,&end,10);
    if(errno||end==s||*end||x<0||x>INT_MAX)exit(2);
    return (int)x;
}
int main(int argc,char **argv) {
    if(argc!=4&&argc!=6)return 2;
    int f=number(argv[1]),s0=number(argv[2]),s1=number(argv[3]);
    int t0=argc==6?number(argv[4]):0,t1=argc==6?number(argv[5]):100000;
    if(s0>=s1||t0>=t1)return 2;
    for(unsigned i=1;i<65536;i++)bits[i]=(unsigned char)(bits[i>>1]+(i&1));
    mask p[3]={0};Bank b;
    generate(0,p,&b);if(f>=stage[0].n)return 2;
    p[0]=stage[0].a[f];generate(1,p,&b);
    int si=-1;uint64_t total=0;
    for(int a=0;a<stage[1].n;a++) {
        p[1]=stage[1].a[a];if(!ordered(p[1],1,p))continue;
        ++si;if(si<s0||si>=s1)continue;
        generate(2,p,&b);int ti=-1;uint64_t count=0;
        for(int j=0;j<stage[2].n;j++){
            p[2]=stage[2].a[j];if(!ordered(p[2],2,p))continue;
            ++ti;if(ti<t0||ti>=t1)continue;
            generate(3,p,&b);unsigned leaves=0;
            for(int k=0;k<stage[3].n;k++){
                mask z=stage[3].a[k];if(!ordered(z,3,p))continue;
                leaves++;
                if(hit(&b,z)){
                    printf("hit %d %d %d masks %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 "\n",f,si,ti,p[0],p[1],p[2],z);return 0;
                }
            }
            count+=leaves;printf("leaf %d %d %d states %u\n",f,si,ti,leaves);fflush(stdout);
        }
        total+=count;printf("closed %d %d third-range %d %d states %" PRIu64 "\n",f,si,t0,t1<ti+1?t1:ti+1,count);fflush(stdout);
    }
    printf("range-end %d %d %d states %" PRIu64 "\n",f,s0,s1,total);return 0;
}
