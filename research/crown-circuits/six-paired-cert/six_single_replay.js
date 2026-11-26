function profiles(sparse=true){const full=(1n<<64n)-1n,low=[],hi=[];for(let j=0;j<6;j++){let m=0n;for(let p=0;p<64;p++)if(!(p>>j&1))m|=1n<<BigInt(p);low.push(m);hi.push(full^m);}
function flip(m,d){for(let j=0;d;j++,d>>=1)if(d&1){const k=1n<<BigInt(j);m=((m&low[j])<<k)|((m&hi[j])>>k);}return m;}
const seen=[0,0,0,0,0,0],data=[[],[],[],[],[]];
function walk(us,bs,atoms,stab){const j=us.length;if(j===6){if(atoms.length<12)return;const B=new Set(bs),W=new Set(us.filter(x=>x!==full&&!B.has(x))),q=W.size;seen[q]++;if(sparse&&Math.min(...[low[0],hi[0]].map(m=>atoms.filter(a=>a&m).length))===1)return;if(sparse&&us.some(m=>m!==full&&atoms.filter(a=>!(a&m)).length===1))return;data[q].push(us.map(String));return;}
let cl=new Set([0n]);for(const b of bs)for(const a of [...cl])cl.add(a|b);cl.add(full);
for(const u of cl){if(!u||(j>0&&u===full))continue;const st=[];let ok=true;for(const d of stab){const v=flip(u,d);if(v<u){ok=false;break;}if(v===u)st.push(d);}if(!ok)continue;const x=u&low[j],y=u&hi[j];const aa=atoms.flatMap(a=>(a&u)?[a&x,a&y]:[a]);walk([...us,u],[...bs,x,y],aa,[...st,...st.map(d=>d|(1<<j))]);}}walk([],[],[full],[0]);return {seen,data};}
function canon(rows) {
const full=(1n<<64n)-1n,low=[],hi=[],sbit=[],wm=new Map(),fm=new Map(),more=new Map();
for(let j=0;j<6;j++){let m=0n;for(let p=0;p<64;p++)if(!(p>>j&1))m|=1n<<BigInt(p);low.push(m);hi.push(full^m);}
function wt(x){let n=wm.get(x);if(n!==undefined)return n;let m=x;n=0;while(m){m&=m-1n;n++;}wm.set(x,n);return n;}
function flips(m){let f=fm.get(m);if(f)return f;f=[m];for(let j=0;j<6;j++){const k=1n<<BigInt(j);f.push(...f.map(v=>((v&low[j])<<k)|((v&hi[j])>>k)));}fm.set(m,f);return f;}
function permutations(axes){if(axes.length<2)return [axes];return axes.flatMap(x=>permutations(axes.filter(z=>z!==x)).map(t=>[x,...t]));}
const ps=permutations([0,1,2,3,4,5]).map(p=>{let mapped=[];for(let i=0;i<64;i++){let v=0;for(let j=0;j<6;j++)v|=((i>>p[j])&1)<<j;mapped.push(1n<<BigInt(v));}return {p,mapped,m:new Map()};});
function rearr(mask,P){const early=P.m.get(mask);if(early!==undefined)return early;let u=0n;for(let i=0;i<64;i++)if((mask>>BigInt(i))&1n)u|=P.mapped[i];P.m.set(mask,u);return u;}
const out=new Map();
for(const row of rows){const u=row.map(BigInt),w=u.map(wt);const sig=u.map((m,i)=>[w[i],...u.map((n,j)=>[w[j],wt(m&n),Math.min(wt(m&low[j]),wt(m&hi[j])),Math.min(wt(n&low[i]),wt(n&hi[i]))].join('/')).sort()].join(':'));
const sorted=[...sig].sort();const groupKey=sig.map(x=>sorted.indexOf(x)).join(',');
let perms=more.get(groupKey);if(!perms){perms=ps.filter(P=>P.p.every((v,j)=>sig[v]===sorted[j]));more.set(groupKey,perms);}
let key=null;
for(const P of perms){const fs=P.p.map(i=>flips(rearr(u[i],P)));let ds=Array.from({length:64},(_,j)=>j),vs=[];
for(const f of fs){let min=f[ds[0]];for(const d of ds)if(f[d]<min)min=f[d];vs.push(min);ds=ds.filter(d=>f[d]===min);}
const k=vs.map(x=>x.toString(16).padStart(16,'0')).join('');if(key===null||k<key)key=k;}
if(!out.has(key))out.set(key,row);
}
return [...out.values()];}
function solve(raw) {
  const full=(1n<<64n)-1n, dirs=raw.map(BigInt);
  let big=[];
  for(let j=0;j<6;j++){let s=0n;for(let i=0;i<64;i++)if(i>>j&1)s|=1n<<BigInt(i);big.push(s&dirs[j],(~s)&dirs[j]);}
  let atoms=[full];for(const v of big)atoms=atoms.flatMap(a=>[a&v,a&~v].filter(Boolean));
  const L=atoms.length;if(L>32)throw Error("width overflow");
  const cv=m=>atoms.reduce((a,b,j)=>a|((b&m)?1<<j:0),0);
  const F=cv(full),B=[...new Set(big.map(cv).filter(x=>x!==0))],W=[...new Set(dirs.map(cv))].filter(x=>x!==F&&!B.includes(x)),budget=5-W.length;
  function wt(x){x-=(x>>>1)&0x55555555;x=(x&0x33333333)+((x>>>2)&0x33333333);return (((x+(x>>>4))&0x0f0f0f0f)*0x01010101)>>>24;}
  const cl=new Set([0]);for(const b of B)for(const u of [...cl])cl.add(u|b);
  const pool=[...cl].sort((a,b)=>wt(a)-wt(b)||(a>>>0)-(b>>>0)),n=pool.length;
  const id=new Map(pool.map((v,j)=>[v,j])),base=[...B,...W].map(v=>id.get(v)),join=new Uint16Array(n*n),wei=pool.map(v=>wt(F^v));
  for(let i=0;i<n;i++)for(let j=0;j<n;j++)join[i*n+j]=id.get(pool[i]|pool[j]);
  let visits=0;
  const maxSize=Math.floor(L/12);
  for(let ak=0;ak<n;ak++){
    const anc=pool[ak],def=F^anc,sw=wei[ak];
    if(!sw||sw>maxSize||base.some(k=>join[ak*n+k]===k))continue;
    if(sw===1&&L<24&&(31-Math.clz32(def))>2*L-24)continue;
    const ins=[],out=[],valid=new Uint8Array(n),tgt=[];
    for(let v=0;v<n;v++){
      const m=pool[v],d=m^F;
      if(wei[v]>=sw&&wei[v]<=L-11&&!(d&def)&&(wei[v]!==sw||(d>>>0)>(def>>>0))&&!base.some(k=>join[k*n+v]===k)){tgt.push(v);valid[v]=1;}
      if(m!==0&&m!==F&&v!==ak&&!base.includes(v)&&join[ak*n+v]!==v)(join[ak*n+v]===ak?ins:out).push(v);
    }
    tgt.sort((a,b)=>wei[a]-wei[b]);if(tgt.length<11)continue;
    const act=[...base], ways=new Uint16Array(n);let count=0;
    function inc(z){if(!ways[z]++&&valid[z])count++;}
    function dec(z){if(!--ways[z]&&valid[z])count--;}
    for(let i=0;i<act.length;i++)for(let j=0;j<i;j++)inc(join[act[i]*n+act[j]]);
    function add(k){for(const a of act)inc(join[a*n+k]);act.push(k);}
    function undo(k){act.pop();for(const a of act)dec(join[a*n+k]);}
    function fit(ds,occ,pos,k){if(!k)return true;let cnt=0;for(let j=pos;j<ds.length;j++)if(!(ds[j]&occ))cnt++;if(cnt<k)return false;
      for(let j=pos;j<=ds.length-k;j++)if(!(occ&ds[j])&&fit(ds,occ|ds[j],j+1,k-1))return true;return false;}
    function test(){
      visits++;if(count<11)return false;
      const ds=[];let vol=sw;
      for(const v of tgt)if(ways[v]){
        const d=F^pool[v];if(act.some(a=>join[a*n+v]===a)||ds.some(z=>!(z&~d)))continue;
        ds.push(d);if(ds.length<=11){vol+=wei[v];if(vol>L)return false;}
      }
      return ds.length>=11&&fit(ds,def,0,11);
    }
    function outside(i,rem){if(test())return true;if(!rem)return false;
      for(let j=i;j<out.length;j++){const v=out[j];if(!ways[v])continue;add(v);const win=outside(j+1,rem-1);undo(v);if(win)return true;}return false;}
    function inside(i,rem){if(ways[ak]&&outside(0,rem))return true;if(!rem)return false;
      for(let j=i;j<ins.length;j++){const v=ins[j];if(!ways[v])continue;add(v);const win=inside(j+1,rem-1);undo(v);if(win)return true;}return false;}
    if(inside(0,budget))return {L,budget,visits,hit:1};
  }
  return {L,budget,visits,hit:0};
}

function solveShort(raw) {
  const full=(1n<<64n)-1n, dirs=raw.map(BigInt);
  let big=[];
  for(let j=0;j<6;j++){let s=0n;for(let i=0;i<64;i++)if(i>>j&1)s|=1n<<BigInt(i);big.push(s&dirs[j],(~s)&dirs[j]);}
  let atoms=[full];for(const v of big)atoms=atoms.flatMap(a=>[a&v,a&~v].filter(Boolean));
  const L=atoms.length;if(L>32)throw Error("width overflow");
  const cv=m=>atoms.reduce((a,b,j)=>a|((b&m)?1<<j:0),0);
  const F=cv(full),B=[...new Set(big.map(cv).filter(x=>x!==0))],W=[...new Set(dirs.map(cv))].filter(x=>x!==F&&!B.includes(x)),budget=5-W.length;
  function wt(x){x-=(x>>>1)&0x55555555;x=(x&0x33333333)+((x>>>2)&0x33333333);return (((x+(x>>>4))&0x0f0f0f0f)*0x01010101)>>>24;}
  const cl=new Set([0]);for(const b of B)for(const u of [...cl])cl.add(u|b);
  const pool=[...cl].sort((a,b)=>wt(a)-wt(b)||(a>>>0)-(b>>>0)),n=pool.length;
  const id=new Map(pool.map((v,j)=>[v,j])),base=[...B,...W].map(v=>id.get(v)),join=new Uint16Array(n*n),wei=pool.map(v=>wt(F^v));
  for(let i=0;i<n;i++)for(let j=0;j<n;j++)join[i*n+j]=id.get(pool[i]|pool[j]);
  let visits=0;
  const targets=pool.map((_,i)=>i).filter(k=>wei[k]>0&&wei[k]<=L-11&&!base.some(a=>join[a*n+k]===a)).sort((a,b)=>wei[a]-wei[b]);
  const act=[...base],ways=new Uint16Array(n), valid=new Uint8Array(n);for(const v of targets)valid[v]=1;
  let count=0;function inc(z){if(!ways[z]++&&valid[z])count++;}function dec(z){if(!--ways[z]&&valid[z])count--;}
  for(let i=0;i<act.length;i++)for(let j=0;j<i;j++)inc(join[act[i]*n+act[j]]);
  function add(k){for(const a of act)inc(join[k*n+a]);act.push(k);}function undo(k){act.pop();for(const a of act)dec(join[k*n+a]);}
  function fit(ds,occ,pos,k){if(!k)return true;let cnt=0;for(let j=pos;j<ds.length;j++)if(!(ds[j]&occ))cnt++;if(cnt<k)return false;
      for(let j=pos;j<=ds.length-k;j++)if(!(occ&ds[j])&&fit(ds,occ|ds[j],j+1,k-1))return true;return false;}
  function test(){visits++;if(count<12)return false;const ds=[];let sum=0;for(const v of targets)if(ways[v]){const d=F^pool[v];if(act.some(a=>join[a*n+v]===a)||ds.some(z=>!(z&~d)))continue;ds.push(d);if(ds.length<=12){sum+=wei[v];if(sum>L)return false;}}return ds.length>=12&&fit(ds,0,0,12);}
  const lib=pool.map((_,i)=>i).filter(i=>pool[i]!==0&&pool[i]!==F&&!base.includes(i));
  function go(pos,rem){if(test())return true;if(rem)for(let j=pos;j<lib.length;j++){let v=lib[j];if(!ways[v])continue;add(v);const win=go(j+1,rem-1);undo(v);if(win)return true;}return false;}
  const hit=go(0,budget)?1:0;return {L,budget,visits,hit};
}
if(require.main===module){const [q0,a,b]=process.argv.slice(2),{seen,data}=profiles();if(q0===undefined){console.log(JSON.stringify({seen,remaining:data.map(v=>canon(v).length)}));}else{const q=+q0,rows=canon(data[q]),start=+a||0,end=b===undefined?rows.length:Math.min(rows.length,+b);let visits=0,hits=[];for(let i=start;i<end;i++){const r=q>=3?solveShort(rows[i]):solve(rows[i]);visits+=r.visits;if(r.hit)hits.push(i);}console.log(JSON.stringify({start,count:end-start,visits,hits}));}}
module.exports = {profiles, canon, solve, solveShort};
