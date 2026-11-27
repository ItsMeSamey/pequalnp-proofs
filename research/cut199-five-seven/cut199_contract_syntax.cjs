const fs=require('node:fs'),path=require('node:path'),{bankWords,rows}=require('./cut199_portfolio_onefork.cjs');
const templates=require('./cut199-contract-templates.json');
const word=(n,i)=>Array.from({length:1<<n},(_,x)=>BigInt(x>>i&1)<<BigInt(x)).reduce((a,b)=>a|b,0n);
const L=Array.from({length:5},(_,i)=>word(5,i)),hot=word(6,0),edges=[5,17,6,10,12];
const favorable=s=>Array.from({length:64},(_,x)=>BigInt(!!((x>>1)&s)||edges.some(e=>((x>>1)&e)===e))<<BigInt(x)).reduce((a,b)=>a|b,0n);
function solve(t,anchor,h,control=null){
 const W=bankWords(L,[hot,hot|favorable(h),...t.s.map(favorable)]);W.push(W[anchor]);
 const row=rows.map((_,j)=>W.reduce((m,w,k)=>m|Number(w>>BigInt(j)&1n)<<k,0));
 const ev=(tree,code)=>Number.isInteger(tree)?((code>>tree)&1):(tree[0]?ev(tree[1],code)&ev(tree[2],code):ev(tree[1],code)|ev(tree[2],code));
 const P=control?row.filter(x=>ev(control,x)).slice(0,3):row.slice(0,16);
 const N=control?row.filter(x=>!ev(control,x)).slice(0,3):row.slice(16);
 const U=8191,active=(7|(31<<7)),hotmask=3<<5;
 const bans=t.pairs.map(([i,j,op])=>[(1<<i)|(1<<j),op]);
 // Forced singleton differences in one positive row require AND; in one negative column require OR.
 const fixed=new Map(bans.map(([m,op])=>[m,op]));
 let bad=false;
 function impose(words,op){for(const ds of words){let req=0;for(const d of ds)if(d&&!(d&(d-1)))req|=d;
  for(let u=req;u;u&=u-1)for(let v=u&(u-1);v;v&=v-1){const m=(u&-u)|(v&-v);
   if(fixed.has(m)&&fixed.get(m)!==op)bad=true;else fixed.set(m,op);}
 }}
 impose(P.map(x=>N.map(y=>x&~y)),1);impose(N.map(y=>P.map(x=>x&~y)),0);
 if(bad)return null;
 bans.splice(0,bans.length,...[...fixed]);
 const memo=new Map(),splits=new Map();
 function options(m,face){
  const id=m+8192*face;if(splits.has(id))return splits.get(id);const out=[];
  for(let a=(m-1)&m;a;a=(a-1)&m){const b=m^a;if(a>b)continue;
   const A=!!(a&active),B=!!(b&active);
   for(let op=0;op<2;op++){
    if(bans.some(([v,p])=>p!==op&&(a&v)&&(b&v)))continue;
    if(A&&B)out.push([a,b,op,2,2]);
    else if(A||B)out.push([a,b,op,A?2:op,B?2:op]);
    else for(let x=0;x<2;x++)for(let y=0;y<2;y++)if((op?(x&y):(x|y))===face)out.push([a,b,op,x,y]);
   }
  }splits.set(id,out);return out;
 }
 function rec(m,pp,nn,face){
  const key=[m,pp,nn,face].join();if(memo.has(key))return memo.get(key);
  let p=[],n=[];for(let x=pp;x;x&=x-1)p.push(31-Math.clz32(x&-x));for(let x=nn;x;x&=x-1)n.push(31-Math.clz32(x&-x));
  if(p.some(i=>!(m&P[i]))||n.some(j=>!(m&~N[j]))||p.some(i=>n.some(j=>!(m&P[i]&~N[j]))))return null;
  if(!(m&(m-1))){const k=31-Math.clz32(m);return (m&active)||Number(!!(m&hotmask))===face?k:null}
  const S=[];
  for(const [a,b,op,fa,fb] of options(m,face)){
   let fixedA=0,fixedB=0,amb=0,size=0,ok=true;
   for(const i of op?n:p){
    const ds=op?p.map(j=>P[j]&~N[i]):n.map(j=>P[i]&~N[j]);
    ds.push(op?~N[i]:P[i]);
    const aa=ds.every(d=>d&a),bb=ds.every(d=>d&b);
    if(!aa&&!bb){ok=false;break}if(!aa)fixedB|=1<<i;else if(!bb)fixedA|=1<<i;else{amb|=1<<i;size++}
   }
   if(ok)S.push([size,a,b,op,fa,fb,fixedA,fixedB,amb]);
  }
  S.sort((x,y)=>x[0]-y[0]);
  for(const [,a,b,op,fa,fb,aa,bb,amb] of S){
   for(let x=amb;;x=(x-1)&amb){
    let A=rec(a,op?pp:aa|x,op?aa|x:nn,fa);
    if(A!==null){let B=rec(b,op?pp:bb|(amb^x),op?bb|(amb^x):nn,fb);
     if(B!==null){const ans=[op,A,B];memo.set(key,ans);return ans;}}
    if(!x)break;
   }
  }memo.set(key,null);return null;
 }
 return rec(U,(1<<P.length)-1,(1<<N.length)-1,2);
}
if(require.main===module){
 const results=[];
 for(const [i,t] of templates.entries())for(const anchor of [3,4]){
  const h=t.s.includes(8)?16:8,tree=solve(t,anchor,h);results.push({i,anchor,h,tree});
 }
 fs.writeFileSync(path.join(__dirname,'cut199-contraction-syntax-results.json'),JSON.stringify(results));
 console.log(JSON.stringify({tested:results.length,hits:results.filter(x=>x.tree!==null).length}));
}
module.exports={solve};
