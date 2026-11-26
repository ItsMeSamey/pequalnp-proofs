const short64=(function(){function solve(raw) {
  const full=(1n<<64n)-1n, dirs=raw.map(BigInt);
  let big=[];
  for(let j=0;j<6;j++){let s=0n;for(let i=0;i<64;i++)if(i>>j&1)s|=1n<<BigInt(i);big.push(s&dirs[j],(~s)&dirs[j]);}
  let atoms=[full];for(const v of big)atoms=atoms.flatMap(a=>[a&v,a&~v].filter(Boolean));
  const L=atoms.length;if(L>64)throw Error("width overflow");
  const cv=m=>atoms.reduce((a,b,j)=>a|((b&m)?1n<<BigInt(j):0n),0n); const hi=x=>Number(x>>32n),merge=(a,b)=>a|b;
  const F=cv(full),B=[...new Set(big.map(cv).filter(x=>x!==0n))],W=[...new Set(dirs.map(cv))].filter(x=>x!==F&&!B.includes(x)),budget=5-W.length;
  function wc(x){x-=(x>>>1)&0x55555555;x=(x&0x33333333)+((x>>>2)&0x33333333);return (((x+(x>>>4))&0x0f0f0f0f)*0x01010101)>>>24;}
  const wt=x=>wc(Number(x&0xffffffffn))+wc(hi(x));
  const cl=new Set([0n]);for(const b of B)for(const u of [...cl])cl.add(merge(u,b));
  const pool=[...cl].sort((a,b)=>wt(a)-wt(b)||(a<b?-1:a>b?1:0)),n=pool.length;
  const id=new Map(pool.map((v,j)=>[v,j])),base=[...B,...W].map(v=>id.get(v)),join=new Uint16Array(n*n),wei=pool.map(v=>wt(F-v));
  for(let i=0;i<n;i++)for(let j=0;j<n;j++)join[i*n+j]=id.get(merge(pool[i],pool[j]));
  const dlo=pool.map(v=>Number((F-v)&0xffffffffn)),dhi=pool.map(v=>hi(F-v));let visits=0;
  const targets=pool.map((_,i)=>i).filter(k=>wei[k]>0&&wei[k]<=L-11&&!base.some(a=>join[a*n+k]===a)).sort((a,b)=>wei[a]-wei[b]);
  const act=[...base],ways=new Uint16Array(n), valid=new Uint8Array(n);for(const v of targets)valid[v]=1;
  let count=0;function inc(z){if(!ways[z]++&&valid[z])count++;}function dec(z){if(!--ways[z]&&valid[z])count--;}
  for(let i=0;i<act.length;i++)for(let j=0;j<i;j++)inc(join[act[i]*n+act[j]]);
  function add(k){for(const a of act)inc(join[k*n+a]);act.push(k);}function undo(k){act.pop();for(const a of act)dec(join[k*n+a]);}
  function fit(ds,lo,h,pos,k){if(!k)return true;let cnt=0;for(let j=pos;j<ds.length;j++)if(!(dlo[ds[j]]&lo)&&!(dhi[ds[j]]&h))cnt++;if(cnt<k)return false;
      for(let j=pos;j<=ds.length-k;j++)if(!(dlo[ds[j]]&lo)&&!(dhi[ds[j]]&h)&&fit(ds,lo|dlo[ds[j]],h|dhi[ds[j]],j+1,k-1))return true;return false;}
  function test(){visits++;if(count<12)return false;const ds=[];let sum=0;for(const v of targets)if(ways[v]){if(act.some(a=>join[a*n+v]===a)||ds.some(z=>join[z*n+v]===z))continue;ds.push(v);if(ds.length<=12){sum+=wei[v];if(sum>L)return false;}}return ds.length>=12&&fit(ds,0,0,0,12);}
  const lib=pool.map((_,i)=>i).filter(i=>pool[i]!==0n&&pool[i]!==F&&!base.includes(i));
  function go(pos,rem){if(test())return true;if(rem)for(let j=pos;j<lib.length;j++){let v=lib[j];if(!ways[v])continue;add(v);const win=go(j+1,rem-1);undo(v);if(win)return true;}return false;}
  const hit=go(0,budget)?1:0;return {L,budget,visits,hit};
}
return solve;})();
const hot64=(function(){function solveBase(raw,extra=[]) {
  const full=(1n<<64n)-1n, dirs=raw.map(BigInt);
  let big=[];
  for(let j=0;j<6;j++){let s=0n;for(let i=0;i<64;i++)if(i>>j&1)s|=1n<<BigInt(i);big.push(s&dirs[j],(~s)&dirs[j]);}
  let atoms=[full];for(const v of big)atoms=atoms.flatMap(a=>[a&v,a&~v].filter(Boolean));
  const L=atoms.length;if(L>64)throw Error("width overflow");
  const cv=m=>atoms.reduce((a,b,j)=>a|((b&m)?1n<<BigInt(j):0n),0n); const hi=x=>Number(x>>32n),merge=(a,b)=>a|b;
  const F=cv(full),B=[...new Set(big.map(cv).filter(x=>x!==0n))],W=[...new Set(dirs.map(cv))].filter(x=>x!==F&&!B.includes(x)),budget=5-W.length-extra.length;
  function wc(x){x-=(x>>>1)&0x55555555;x=(x&0x33333333)+((x>>>2)&0x33333333);return (((x+(x>>>4))&0x0f0f0f0f)*0x01010101)>>>24;}
  const wt=x=>wc(Number(x&0xffffffffn))+wc(hi(x));
  const cl=new Set([0n]);for(const b of B)for(const u of [...cl])cl.add(merge(u,b));
  const pool=[...cl].sort((a,b)=>wt(a)-wt(b)||(a<b?-1:a>b?1:0)),n=pool.length;
  const id=new Map(pool.map((v,j)=>[v,j])),base=[...B,...W,...extra.map(cv)].map(v=>id.get(v)),join=new Uint16Array(n*n),wei=pool.map(v=>wt(F-v));
  for(let i=0;i<n;i++)for(let j=0;j<n;j++)join[i*n+j]=id.get(merge(pool[i],pool[j]));
  const dlo=pool.map(v=>Number((F-v)&0xffffffffn)),dhi=pool.map(v=>hi(F-v));let visits=0;
const samples=atoms.map(a=>{let i=0;while(!((a>>BigInt(i))&1n))i++;return i;});
const atomAt=Array.from({length:64},(_,p)=>atoms.findIndex(a=>!!(a&(1n<<BigInt(p)))));
const perms=[];for(let f=0;f<64;f++){let ok=true;for(const u of [...dirs,...extra]){for(let p=0;p<64;p++)if(((u>>BigInt(p))&1n)!==((u>>BigInt(p^f))&1n)){ok=false;break;}if(!ok)break;}if(ok&&f)perms.push(samples.map(p=>atomAt[p^f]));}
function isCanon(d){for(const p of perms){let v=0n;for(let i=0;i<p.length;i++)if((d>>BigInt(i))&1n)v|=1n<<BigInt(p[i]);if(v<d)return false;}return true;}
  const candidates=[];
for(const u of dirs.filter(m=>m!==full)){const w=cv(u),masks=[];for(let k=0;k<n;k++)if(wei[k]&&wei[k]<=L-11&&pool[k]!==w&&merge(w,pool[k])===pool[k]&&!B.some(b=>merge(w,b)!==F && merge(pool[k],merge(w,b))===merge(w,b))&&!base.some(a=>join[a*n+k]===a))masks.push(k);candidates.push(masks);}
candidates.sort((a,b)=>a.length-b.length);
const goodAnchor=new Set(candidates[0]);
  for(let ak=0;ak<n;ak++){
    const anc=pool[ak],def=F-anc,sw=wei[ak];
    if(!goodAnchor.has(ak)||!isCanon(def))continue;
    
    const ins=[],out=[],valid=new Uint8Array(n),tgt=[];
    for(let v=0;v<n;v++){
      const m=pool[v],d=F-m;
      if(wei[v]&&wei[v]<=L-11&&!(dlo[v]&dlo[ak])&&!(dhi[v]&dhi[ak])&&!base.some(k=>join[k*n+v]===k)){tgt.push(v);valid[v]=1;}
      if(m!==0n&&m!==F&&v!==ak&&!base.includes(v)&&join[ak*n+v]!==v)(join[ak*n+v]===ak?ins:out).push(v);
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
    function outside(i,rem){if(test())return true;if(!rem)return false;
      for(let j=i;j<out.length;j++){const v=out[j];if(!ways[v])continue;add(v);const win=outside(j+1,rem-1);undo(v);if(win)return true;}return false;}
    function inside(i,rem){if(ways[ak]&&outside(0,rem))return true;if(!rem)return false;
      for(let j=i;j<ins.length;j++){const v=ins[j];if(!ways[v])continue;add(v);const win=inside(j+1,rem-1);undo(v);if(win)return true;}return false;}
    if(inside(0,budget))return {L,budget,visits,hit:1};
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
return solve;})();
module.exports = {short64, hot64};
