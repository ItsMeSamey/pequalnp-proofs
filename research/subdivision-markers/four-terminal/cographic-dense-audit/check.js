// Run with node check.js. Deterministically exhaust edge subsets of seeded small hosts.
"use strict";
let seed=412719;
function rng(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return Math.floor(seed*n/4294967296);}
function assert(ok){if(!ok)throw Error("failed finite audit");}
function range(n){return Array.from({length:n},(_,i)=>i);}
function parity(x){let y=0;for(;x;x&=x-1)y^=1;return y;}
function sum(cols){return cols.reduce((a,b)=>a^b,0);}
function sums(cols){let out=[0];for(const x of cols)out=out.concat(out.map(t=>t^x));return out;}
function add(b,x){while(x){let p=31-Math.clz32(x);if(!b[p]){b[p]=x;return true;}x^=b[p];}return false;}
function rem(b,x){for(let j=b.length-1;j>=0;j--)if(x>>j&1)x^=b[j]||0;return x;}
function eq(a,b){return a.size===b.size && [...a].every(x=>b.has(x));}
function bitlist(x){return range(31).filter(i=>x>>i&1);}
function submasks(x){let out=[];for(let s=x;;s=(s-1)&x){out.push(s);if(!s)return out;}}
function fundamentalCore(E,H,gain){
  const piv=[],forest=[],chords=[];
  for(const i of bitlist(H)){const [a,b]=E[i];(add(piv,(1<<a)^(1<<b))?forest:chords).push(i);}
  const gains=[];let core=0,rank=0;
  for(const e of chords){const [a,b]=E[e],path=new Map([[a,0]]),todo=[a];
    while(todo.length&&!path.has(b)){const u=todo.pop();for(const i of forest){
      const [x,y]=E[i];if(u!==x&&u!==y)continue;const v=x^y^u;
      if(!path.has(v)){path.set(v,path.get(u)|(1<<i));todo.push(v);}
    }}
    const c=path.get(b)|(1<<e);if(add(gains,gain[c])){core|=c;rank++;}
  }
  return [core,rank];
}
const stats={cases:0,strict:0,external:0,yes:0,traces:0,deletions:0};
for(let trial=0;trial<500;trial++){
 const n=2+rng(4),m=2+rng(7),E=range(m).map(()=>[rng(n),rng(n)]),mask=(1<<m)-1;
 const B=E.map(([u,v])=>(1<<u)^(1<<v)),boundary=sums(B);
 const cuts=range(n).map(v=>E.reduce((s,[u,w],i)=>s|((((u===v)^(w===v)))<<i),0));
 const ker=[];cuts.forEach(c=>add(ker,c));const K=[];
 for(let j=0,k=rng(3);j<k;j++){const v=rng(1<<m);if(add(ker,v))K.push(v);}
 const O=range(m).map(i=>rem(ker,1<<i)),ov=sums(O),J=new Map();
 ov.forEach((x,j)=>J.set(x,j));
 const roots=[],pb=[];for(let j=0,s=rng(4);j<s;j++){let z=ov[rng(ov.length)]^(rng(4)<<m);if(add(pb,z))roots.push(z);}
 const t=ov[rng(ov.length)],last=t^sum(roots);if(!add(pb,last))continue;
 roots.push(last);const pv=sums(roots),W=[t],wb=[];add(wb,t);for(const v of pv)if(J.has(v)&&add(wb,v))W.push(v);
 const Wv=sums(W),Wset=new Set(Wv),r=W.length,helpers=W.map(v=>J.get(v)).concat(K);
 const gain=sums(range(m).map(i=>helpers.reduce((a,z,j)=>a|((z>>i&1)<<j),0)));
 let yes=false,circuit=false;
 for(let H=0;H<=mask;H++){
  const T=new Set(submasks(mask^H).map(s=>ov[s]).filter(v=>Wset.has(v)));
  const L=new Set(submasks(H).filter(s=>!boundary[s]).map(s=>gain[s])), projected=new Set();
  for(let x=0;x<(1<<helpers.length);x++)if([...L].every(v=>!parity(v&x)))projected.add(Wv[x&((1<<r)-1)]);
  assert(eq(T,projected));yes ||= eq(T,new Set([0,t]));
  const [core,rank]=fundamentalCore(E,H,gain);
  assert(eq(L,new Set(submasks(core).filter(s=>!boundary[s]).map(s=>gain[s]))));assert(L.size==1<<rank);
  if(ov[H]===t){const cols=roots.concat(bitlist(H).map(j=>O[j])),b=[];cols.forEach(x=>add(b,x));
    circuit ||= b.filter(Boolean).length===cols.length-1;}
  stats.traces++;
 }
 assert(yes===circuit);stats.cases++;stats.strict+=K.length>0;stats.external+=roots.some(x=>!J.has(x));stats.yes+=yes;
 // Restrict ordinary columns by deleting R and contract R in the dual host.
 const R=rng(1<<m),parent=range(n);function find(x){while(parent[x]!==x)x=parent[x];return x;}
 bitlist(R).forEach(i=>{const [a,b]=E[i];parent[find(a)]=find(b);});
 const ccut=range(n).map(v=>E.reduce((s,[a,b],i)=>s|((!(R>>i&1)&&((find(a)===v)^(find(b)===v)))<<i),0));
 const small=new Set(sums(ccut)),zeroCuts=new Set(sums(cuts).filter(c=>!(c&R)));
 assert(eq(small,zeroCuts));const restricted=range(1<<m).filter(s=>!(s&R)&&!ov[s]);
 assert(restricted.length<=small.size*(1<<K.length));stats.deletions++;
}
console.log(JSON.stringify(stats));
