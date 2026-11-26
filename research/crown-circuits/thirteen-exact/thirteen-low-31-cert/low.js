function solveBase(raw,extra=[]) {
  const A=raw.length,D=1<<A,N=1<<(2*A),full=(1n<<BigInt(D))-1n, dirs=raw.map(BigInt);
  let big=[];
  for(let j=0;j<A;j++){let s=0n;for(let i=0;i<D;i++)if(i>>j&1)s|=1n<<BigInt(i);big.push(s&dirs[j],(~s)&dirs[j]);}
  let atoms=[full];for(const v of big)atoms=atoms.flatMap(a=>[a&v,a&~v].filter(Boolean));
  const L=atoms.length;
  const cv=m=>atoms.reduce((a,b,j)=>a|((b&m)?1n<<BigInt(j):0n),0n);const hi=x=>Number(x>>32n),merge=(a,b)=>a|b;
  const F=cv(full),B=[...new Set(big.map(cv).filter(x=>x!==0n))],W=[...new Set(dirs.map(cv))].filter(x=>x!==F&&!B.includes(x)),budget=6-W.length-extra.length;
  function wc(x){x-=(x>>>1)&0x55555555;x=(x&0x33333333)+((x>>>2)&0x33333333);return (((x+(x>>>4))&0x0f0f0f0f)*0x01010101)>>>24;}
  const wt=x=>wc(Number(x&4294967295n))+wc(hi(x));
  const cl=new Set([0n]);for(const b of B)for(const u of [...cl])cl.add(merge(u,b));
  const pool=[...cl].sort((a,b)=>wt(a)-wt(b)||(a<b?-1:a>b?1:0)),n=pool.length;
  const id=new Map(pool.map((v,j)=>[v,j])),base=[...B,...W,...extra.map(cv)].map(v=>id.get(v)),join=new Uint16Array(n*n),wei=pool.map(v=>wt(F-v));
  for(let i=0;i<n;i++)for(let j=0;j<n;j++)join[i*n+j]=id.get(merge(pool[i],pool[j]));
  const dlo=pool.map(v=>Number((F-v)&4294967295n)>>>0),dhi=pool.map(v=>hi(F-v));let visits=0;
  const candidates=[];
for(const u of dirs.filter(m=>m!==full)){const w=cv(u),masks=[];for(let k=0;k<n;k++)if(wei[k]&&wei[k]<=L-12&&pool[k]!==w&&merge(w,pool[k])===pool[k]&&!B.some(b=>merge(w,b)!==F && merge(pool[k],merge(w,b))===merge(w,b))&&!base.some(a=>join[a*n+k]===a))masks.push(k);candidates.push(masks);}
candidates.sort((a,b)=>a.length-b.length);
const smallest=pool.map((_,k)=>k).filter(k=>wei[k]>0&&wei[k]<=Math.floor(L/13)&&!base.some(b=>join[k*n+b]===b));candidates.push(smallest);candidates.sort((a,b)=>a.length-b.length);const goodAnchor=new Set(candidates[0]);
const literalId=big.map(b=>id.get(cv(b)));
const physical=new Uint16Array(N), expression=new Uint16Array(n);
for(let b=1;b<N;b++){const one=b&-b;physical[b]=join[physical[b^one]*n+literalId[31-Math.clz32(one)]];expression[physical[b]]=b;}
const halves=Array.from({length:A},(_,j)=>{let m=0n;for(let k=0;k<D;k++)if(k>>j&1)m|=1n<<BigInt(k);return m;});
function flipDir(m,j){const k=1n<<BigInt(j);return ((m&~halves[j])<<k)|((m&halves[j])>>k);}
const flipped=dirs.map(u=>{const v=[u];for(let j=0;j<A;j++)v.push(...v.map(x=>flipDir(x,j)));return v;});
const countDir=u=>{let n=0;while(u){u&=u-1n;n++;}return n;};
const sizes=dirs.map(countDir),influ=dirs.map(u=>halves.map((_,j)=>countDir(u^flipDir(u,j))));
function perms(a){return !a.length?[[]]:a.flatMap(i=>perms(a.filter(j=>j!==i)).map(p=>[i,...p]));}
const autos=[];
for(const P of perms(Array.from({length:A},(_,i)=>i))){
 if(P.some((v,i)=>sizes[i]!==sizes[v]||P.some((w,k)=>influ[i][k]!==influ[v][w])))continue;
 const mapped=Array.from({length:D},(_,j)=>P.reduce((v,k,i)=>v|((j>>i&1)<<k),0));
 const expected=P.map(j=>mapped.reduce((v,k,i)=>v|(((dirs[j]>>BigInt(k))&1n)<<BigInt(i)),0n));
 for(let f=0;f<D;f++){
  if(expected.some((v,i)=>v!==flipped[i][f]))continue;
  const ptr=Array.from({length:2*A},(_,l)=>2*P[l>>1]+((l&1)^((f>>(l>>1))&1)));
  const map=new Uint16Array(N);
  for(let b=1;b<N;b++){const one=b&-b;map[b]=map[b^one]|(1<<ptr[31-Math.clz32(one)]);}
  const tab=Uint16Array.from(expression,v=>physical[map[v]]);
  if(candidates[0].every(k=>goodAnchor.has(tab[k])))autos.push(tab);
 }
}
  for(let ak=0;ak<n;ak++){
    const anc=pool[ak],def=F-anc,sw=wei[ak];
    if(!goodAnchor.has(ak)||autos.some(p=>p[ak]<ak))continue;const group=autos.filter(p=>p[ak]===ak);
    
    const ins=[],out=[],valid=new Uint8Array(n),tgt=[];
    for(let v=0;v<n;v++){
      const m=pool[v],d=F-m;
      if(wei[v]&&wei[v]<=L-12&&!(dlo[v]&dlo[ak])&&!(dhi[v]&dhi[ak])&&!base.some(k=>join[k*n+v]===k)){tgt.push(v);valid[v]=1;}
      if(m!==0n&&m!==F&&v!==ak&&!base.includes(v)&&join[ak*n+v]!==v)(join[ak*n+v]===ak?ins:out).push(v);
    }
    tgt.sort((a,b)=>wei[a]-wei[b]);if(tgt.length<12)continue;
    const act=[...base], ways=new Uint16Array(n);let count=0;
    function inc(z){if(!ways[z]++&&valid[z])count++;}
    function dec(z){if(!--ways[z]&&valid[z])count--;}
    for(let i=0;i<act.length;i++)for(let j=0;j<i;j++)inc(join[act[i]*n+act[j]]);
    function add(k){for(const a of act)inc(join[a*n+k]);act.push(k);}
    function undo(k){act.pop();for(const a of act)dec(join[a*n+k]);}
    function fit(ds,lo,h,pos,k){if(!k)return true;let cnt=0;for(let j=pos;j<ds.length;j++)if(!(dlo[ds[j]]&lo)&&!(dhi[ds[j]]&h))cnt++;if(cnt<k)return false;
      for(let j=pos;j<=ds.length-k;j++)if(!(dlo[ds[j]]&lo)&&!(dhi[ds[j]]&h)&&fit(ds,lo|dlo[ds[j]],h|dhi[ds[j]],j+1,k-1))return true;return false;}
    function test(){
      visits++;if(count<12)return false;
      const ds=[];let vol=sw;
      for(const v of tgt)if(ways[v]){
        if(act.some(a=>join[a*n+v]===a)||ds.some(z=>join[z*n+v]===z))continue;
        ds.push(v);if(ds.length<=12){vol+=wei[v];if(vol>L)return false;}
      }
      return ds.length>=12&&fit(ds,dlo[ak],dhi[ak],0,12);
    }
    function outside(i,rem,st){if(test())return true;if(!rem)return false;
      for(let j=i;j<out.length;j++){const v=out[j];if(!ways[v]||st.some(p=>p[v]<v))continue;add(v);const win=outside(j+1,rem-1,st.filter(p=>p[v]===v));undo(v);if(win)return true;}return false;}
    function inside(i,rem,st){if(ways[ak]&&outside(0,rem,st))return true;if(!rem)return false;
      for(let j=i;j<ins.length;j++){const v=ins[j];if(!ways[v]||st.some(p=>p[v]<v))continue;add(v);const win=inside(j+1,rem-1,st.filter(p=>p[v]===v));undo(v);if(win)return true;}return false;}
    if(inside(0,budget,group))return {L,budget,visits,hit:1};
  }
  return {L,budget,visits,hit:0};
}


const fs=require('fs');for(const line of fs.readFileSync(process.argv[2],'utf8').trim().split('\n')){if(!line.trim())continue;const [id,...u]=line.trim().split(/\s+/);const v=solveBase(u);console.log(id,v.L,v.visits,v.hit);}
