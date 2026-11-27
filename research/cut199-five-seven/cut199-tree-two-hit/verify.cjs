'use strict';
const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const assert = require('node:assert/strict');
const sha = data => crypto.createHash('sha256').update(data).digest('hex');
const input = fs.readFileSync(path.join(__dirname, 'issued18272.txt'));
const inputHash = sha(input);
assert.equal(inputHash, '9ec4bd7fce25977e79676fd87f567c30812b34f80a264e9df1a9aeb6d972f84b');
const literal = input.toString().match(/x5 ↑x7 = \[(.*?)\]\.getD/u)[1];
const words = [...literal.matchAll(/\((\d+) : ℕ\)/gu)].map(m => BigInt(m[1]));
assert.equal(words.length,11);
const edge = Array.from({length:16}, (_,j) =>
  words.reduce((s,w,i) => s | (Number((w >> BigInt(j)) & 1n) << i), 0));
const left = [0,1,2,6,7], faceRaw = [4,5,8,9,10];
const expand = (a,vars) => vars.reduce((s,v,i) => s | ((a >> i & 1) << v),0);
const accepts = s => edge.some(e => (s & e) === e);
const isSubset = (x,y) => (x & y) === x;
const profiles = Array.from({length:32}, (_,r) => {
  let result = 0n;
  for(let l=0;l<32;l++)
    if(accepts(8 | expand(r,faceRaw) | expand(l,left))) result |= 1n << BigInt(l);
  return result;
});
const allPairs = [];
for(let a=0;a<32;a++) for(let b=0;b<32;b++)
  if(profiles[a] & ~profiles[b]) allPairs.push([a,b]);
const needs = allPairs.filter(([a,b],i) => !allPairs.some(([c,d],j) =>
  i!==j && isSubset(c,a) && isSubset(b,d)));
assert.equal(needs.length,22);
const all = (1 << needs.length)-1;
const distinguishes = f => needs.reduce((s,[a,b],i) => s | (((f>>>a)&~(f>>>b)&1)<<i),0);

function upperPortfolios(){
  let monotone=[0,1];
  for(let n=0;n<5;n++){
    const next=[];
    for(const low of monotone) for(const high of monotone)
      if((low & ~high)===0) next.push(low | (high << (1<<n)));
    monotone=next;
  }
  assert.equal(monotone.length,7581);
  // Maximal coverage masks suffice for preliminary tests of extendibility.
  const masks=[...new Set(monotone.map(distinguishes))];
  const maximal=masks.filter(x=>!masks.some(y=>x!==y&&isSubset(x,y)));
  const pairs=[...new Set(maximal.flatMap(x=>maximal.map(y=>x|y)))];
  const triples=[...new Set(maximal.flatMap(x=>pairs.map(y=>x|y)))];
  const signals=monotone.filter(x=>triples.some(t=>(distinguishes(x)|t)===all));
  assert.equal(signals.length,344);
  const coverage=signals.map(distinguishes), portfolios=[];
  for(let i=0;i<signals.length;i++) for(let j=0;j<i;j++)
    for(let k=0;k<j;k++){
      const m=coverage[i]|coverage[j]|coverage[k];
      for(let a=0;a<k;a++) if((m|coverage[a])===all)
        portfolios.push([signals[a],signals[k],signals[j],signals[i]]);
    }
  return portfolios;
}

// For each labelled read-once tree, record the truth tables obtainable
// by fixing any subformula to a constant. Tables use four formal port bits.
function prunedTrees(){
  const vars=[43690,52428,61680,65280], memo=new Map();
  function visit(mask){
    if(memo.has(mask)) return memo.get(mask);
    const lists=[];
    if(!(mask & (mask-1))) lists.push([0,65535,vars[Math.log2(mask)]]);
    else for(let a=(mask-1)&mask;a;a=(a-1)&mask){
      const b=mask^a;
      if(a>=b) continue;
      for(const x of visit(a)) for(const y of visit(b)) for(const op of [0,1]){
        const z=new Set();
        for(const i of x) for(const j of y) z.add(op ? i&j : i|j);
        lists.push([...z]);
      }
    }
    memo.set(mask,lists);return lists;
  }
  const byFunction=new Map(), ts=visit(15);
  assert.equal(ts.length,120);
  ts.forEach((row,k)=>{
    const bit=1n<<BigInt(k);
    for(const f of row) byFunction.set(f,(byFunction.get(f)||0n)|bit);
  });
  return byFunction;
}
function commonTree(portfolios){
  const by=prunedTrees(), result=[];
  for(const q of portfolios){
    const codes=profiles.map((_,r)=>q.reduce((s,f,i)=>s|((f>>>r&1)<<i),0));
    let common=(1n<<120n)-1n;
    // Left vertices 6,7 are zero in these eight necessary sections.
    for(let l=0;l<8 && common;l++){
      let on=0,off=0;
      for(let r=0;r<32;r++){
        if((profiles[r]>>BigInt(l))&1n) on |= 1<<codes[r];
        else off |= 1<<codes[r];
      }
      assert.equal(on&off,0);
      const free=65535^(on|off);
      let shapes=0n;
      for(let a=free;;a=(a-1)&free){
        shapes |= by.get(on|a)||0n;
        if(!a) break;
      }
      common &= shapes;
    }
    if(common) result.push(q);
  }
  return result;
}
function eightGates(portfolios){
  const raw=faceRaw.map((_,i)=>Array.from({length:32},(_,x)=>(x>>i&1)<<x).reduce((a,b)=>a|b,0));
  const goals=[...new Set(portfolios.flat())];
  assert.equal(goals.length,19);assert(goals.every(x=>!raw.includes(x)));
  const bit=new Map(goals.map((x,i)=>[x,1<<i]));
  const target=portfolios.map(q=>q.reduce((m,x)=>m|bit.get(x),0));
  let nodes=0;
  const solved=new Set(), cached=new Map();
  function options(w){
    const out=new Set();
    for(let i=0;i<w.length;i++) for(let j=0;j<i;j++){
      out.add(w[i]&w[j]);out.add(w[i]|w[j]);
    }
    for(const x of w) out.delete(x);
    return [...out];
  }
  function visit(w,d,active){
    const key=w.slice(5).sort((x,y)=>x-y).join(',')+':'+d;
    let old=cached.get(key)||0n;
    const fresh=[];
    for(const i of active){
      const mask=1n<<BigInt(i);
      if(!(old&mask)&&!solved.has(i)){old|=mask;fresh.push(i);}
    }
    if(!fresh.length) return;
    cached.set(key,old);nodes++;
    const choices=options(w);
    const have=w.reduce((m,x)=>m|(bit.get(x)||0),0);
    const ready=choices.reduce((m,x)=>m|(bit.get(x)||0),0);
    const groups=new Map();
    for(const i of fresh){
      const need=target[i]&~have;
      if(!need){solved.add(i);continue;}
      const now=ready&need;
      if(!now&&!d) continue;
      if(!groups.has(now)) groups.set(now,[]);
      groups.get(now).push(i);
    }
    for(const [now,list] of groups){
      if(now){visit(w.concat(goals.filter((_,i)=>now>>i&1)),d,list);continue;}
      if(d>1){for(const x of choices)visit([...w,x],d-1,list);continue;}
      // With one helper left, that helper must immediately unlock a goal.
      for(const x of choices){
        let unlocked=0;
        for(const y of w) unlocked |= (bit.get(x&y)||0)|(bit.get(x|y)||0);
        if(unlocked) visit([...w,x],0,list.filter(i=>target[i]&unlocked));
      }
    }
  }
  visit(raw,4,portfolios.map((_,i)=>i));
  return {nodes,hits:solved.size};
}
const allPortfolios=upperPortfolios();assert.equal(allPortfolios.length,12248);
const survivors=commonTree(allPortfolios);assert.equal(survivors.length,180);
const check=eightGates(survivors);assert.equal(check.hits,0);
const canonical=survivors.map(q=>q.map(x=>x>>>0).sort((a,b)=>a-b).join(',')).sort().join('\n')+'\n';
console.log(JSON.stringify({issued_sha256:inputHash,upper_comparisons:needs.length,
  four_portfolios:allPortfolios.length,common_tree_portfolios:survivors.length,
  survivor_sha256:sha(canonical),distinct_nonraw_goals:19,helper_states:check.nodes,eight_gate_hits:check.hits}));
