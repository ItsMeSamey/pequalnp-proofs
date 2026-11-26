function solveBase(raw,extra=[]) {
  const full=(1n<<64n)-1n, dirs=raw.map(BigInt);
  let big=[];
  for(let j=0;j<6;j++){let s=0n;for(let i=0;i<64;i++)if(i>>j&1)s|=1n<<BigInt(i);big.push(s&dirs[j],(~s)&dirs[j]);}
  let atoms=[full];for(const v of big)atoms=atoms.flatMap(a=>[a&v,a&~v].filter(Boolean));
  const L=atoms.length;if(L>52)throw Error("width overflow");
  const cv=m=>atoms.reduce((a,b,j)=>a+((b&m)?2**j:0),0); const wide=4294967296,hi=x=>Math.floor(x/wide),merge=(a,b)=>((a|b)>>>0)+wide*(hi(a)|hi(b));
  const F=cv(full),B=[...new Set(big.map(cv).filter(x=>x!==0))],W=[...new Set(dirs.map(cv))].filter(x=>x!==F&&!B.includes(x)),budget=5-W.length-extra.length;
  function wc(x){x-=(x>>>1)&0x55555555;x=(x&0x33333333)+((x>>>2)&0x33333333);return (((x+(x>>>4))&0x0f0f0f0f)*0x01010101)>>>24;}
  const wt=x=>wc(x)+wc(hi(x));
  const cl=new Set([0]);for(const b of B)for(const u of [...cl])cl.add(merge(u,b));
  const pool=[...cl].sort((a,b)=>wt(a)-wt(b)||a-b),n=pool.length;
  const id=new Map(pool.map((v,j)=>[v,j])),base=[...B,...W,...extra.map(cv)].map(v=>id.get(v)),join=new Uint16Array(n*n),wei=pool.map(v=>wt(F-v));
  for(let i=0;i<n;i++)for(let j=0;j<n;j++)join[i*n+j]=id.get(merge(pool[i],pool[j]));
  const dlo=pool.map(v=>(F-v)>>>0),dhi=pool.map(v=>hi(F-v));let visits=0;
  const candidates=[];
for(const u of dirs.filter(m=>m!==full)){const w=cv(u),masks=[];for(let k=0;k<n;k++)if(wei[k]&&wei[k]<=L-11&&pool[k]!==w&&merge(w,pool[k])===pool[k]&&!B.some(b=>merge(w,b)!==F && merge(pool[k],merge(w,b))===merge(w,b))&&!base.some(a=>join[a*n+k]===a))masks.push(k);candidates.push(masks);}
candidates.sort((a,b)=>a.length-b.length);
const goodAnchor=new Set(candidates[0]);
const parent=dirs.map(u=>u===full?-1:big.indexOf(u));if(parent.some((v,j)=>v===-1&&dirs[j]!==full))throw Error("expected free activations");
function permutations(a){if(!a.length)return [[]];return a.flatMap(x=>permutations(a.filter(v=>v!==x)).map(rest=>[x,...rest]));}
const phys=new Uint16Array(4096),expr=new Uint16Array(n),lit=big.map(x=>id.get(cv(x)));phys[0]=id.get(0);
for(let bits=1;bits<4096;bits++){const one=bits&-bits;phys[bits]=join[phys[bits^one]*n+lit[31-Math.clz32(one)]];expr[phys[bits]]=bits;}
const autos=[];for(const perm of permutations([0,1,2,3,4,5])){
if(perm.some((v,i)=>(parent[v]<0)!==(parent[i]<0)))continue;
for(let f=0;f<64;f++){const ptr=Array.from({length:12},(_,i)=>2*perm[i>>1]+((i&1)^(f>>(i>>1)&1)));if(parent.some((v,j)=>v>=0&&ptr[v]!==parent[perm[j]]))continue;
const change=new Uint16Array(4096);for(let bits=1;bits<4096;bits++){const one=bits&-bits;change[bits]=change[bits^one]|(1<<ptr[31-Math.clz32(one)]);}
const tab=Uint16Array.from(expr,v=>phys[change[v]]);if(candidates[0].every(k=>goodAnchor.has(tab[k])))autos.push(tab);
}}
  for(let ak=0;ak<n;ak++){
    const anc=pool[ak],def=F-anc,sw=wei[ak];
    if(!goodAnchor.has(ak)||autos.some(p=>p[ak]<ak))continue;const group=autos.filter(p=>p[ak]===ak);
    
    const ins=[],out=[],valid=new Uint8Array(n),tgt=[];
    for(let v=0;v<n;v++){
      const m=pool[v],d=F-m;
      if(wei[v]&&wei[v]<=L-11&&!(dlo[v]&dlo[ak])&&!(dhi[v]&dhi[ak])&&!base.some(k=>join[k*n+v]===k)){tgt.push(v);valid[v]=1;}
      if(m!==0&&m!==F&&v!==ak&&!base.includes(v)&&join[ak*n+v]!==v)(join[ak*n+v]===ak?ins:out).push(v);
    }
    tgt.sort((a,b)=>wei[a]-wei[b]);if(tgt.length<11)continue;
    const act=[...base], ways=new Uint16Array(n);let count=0;
    function inc(z){if(!ways[z]++&&valid[z])count++;}
    function dec(z){if(!--ways[z]&&valid[z])count--;}
    for(let i=0;i<act.length;i++)for(let j=0;j<i;j++)inc(join[act[i]*n+act[j]]);
    function add(k){for(const a of act)inc(join[a*n+k]);act.push(k);}
    function undo(k){act.pop();for(const a of act)dec(join[a*n+k]);}
    function fit(ds,lo,h,pos,k){if(!k)return true;let cnt=0;for(let j=pos;j<ds.length;j++)if(!(dlo[ds[j]]&lo)&&!(dhi[ds[j]]&h))cnt++;if(cnt<k)return false;
      for(let j=pos;j<=ds.length-k;j++)if(!(dlo[ds[j]]&lo)&&!(dhi[ds[j]]&h)&&fit(ds,lo|dlo[ds[j]],h|dhi[ds[j]],j+1,k-1))return true;return false;}
    function test(){
      visits++;if(count<11)return false;
      const ds=[];let vol=sw;
      for(const v of tgt)if(ways[v]){
        if(act.some(a=>join[a*n+v]===a)||ds.some(z=>join[z*n+v]===z))continue;
        ds.push(v);if(ds.length<=11){vol+=wei[v];if(vol>L)return false;}
      }
      return ds.length>=11&&fit(ds,dlo[ak],dhi[ak],0,11);
    }
    function outside(i,rem,st){if(test())return true;if(!rem)return false;
      for(let j=i;j<out.length;j++){const v=out[j];if(!ways[v]||st.some(p=>p[v]<v))continue;add(v);const win=outside(j+1,rem-1,st.filter(p=>p[v]===v));undo(v);if(win)return true;}return false;}
    function inside(i,rem,st){if(ways[ak]&&outside(0,rem,st))return true;if(!rem)return false;
      for(let j=i;j<ins.length;j++){const v=ins[j];if(!ways[v]||st.some(p=>p[v]<v))continue;add(v);const win=inside(j+1,rem-1,st.filter(p=>p[v]===v));undo(v);if(win)return true;}return false;}
    if(inside(0,budget,group))return {L,budget,visits,hit:1};
  }
  return {L,budget,visits,hit:0};
}

function solveEarly(raw){
const us=raw.map(BigInt),full=(1n<<64n)-1n,initial=[],branches=[];for(let j=0;j<6;j++){let h=0n;for(let p=0;p<64;p++)if((p>>j)&1)h|=1n<<BigInt(p);initial.push([...branches]);branches.push(us[j]&h,us[j]&~h);}
const W=[...new Set(us)].filter(u=>u!==full&&!branches.includes(u)),budget=5-W.length;
const plan=require("./six_causal_precursors.js").precursorPlan(us,branches,W);
if(plan.mode!=="invariant")return solveBase(raw);
const {goal,sources:eLib,closure:clo}=plan;
const extra=[],b=[...eLib],states=[...clo].filter(x=>x&&x!==goal&&!b.includes(x));
function wt(x){let n=0;while(x){x&=x-1n;n++;}return n;}states.sort((x,y)=>wt(x)-wt(y)||(x<y?-1:1));
function made(m){for(let i=0;i<b.length;i++)for(let j=0;j<i;j++)if((b[i]|b[j])===m)return true;return false;}
let visits=0,hit=0,L=0;
function dfs(i){if(made(goal)){const r=solveBase(raw,extra);visits+=r.visits;L=r.L;return r.hit;}
if(extra.length===budget)return false;
for(let j=i;j<states.length;j++){const z=states[j];if(!made(z))continue;b.push(z);extra.push(z);if(dfs(j+1))return true;extra.pop();b.pop();}return false;}
hit=dfs(0)?1:0;return {L,budget,visits,hit};}

function solve(raw){return solveEarly(raw);}
module.exports={solve};

