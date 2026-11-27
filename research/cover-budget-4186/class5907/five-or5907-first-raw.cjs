// node five-or5907.cjs list | shard BANK_KEY OFFSET LIMIT | replay HIT.json
// Output is JSONL; a completed shard prints the next offset and total length.
'use strict';
const fs = require('node:fs');
const edges = [[0,1],[0,2],[0,5],[1,5],[2,3],[2,4],[3,4]];
const bits = [1,2,4,8,16,32], pos = edges.map(([a,b]) => 1<<a | 1<<b);
const independent = x => pos.every(v => (x & v) !== v);
const neg = Array.from({length:64}, (_,i)=>i).filter(x => independent(x) &&
  bits.every(v => (v & x) || !independent(v | x)));
const rows = pos.concat(neg), all=(1<<rows.length)-1, target=127;
const raw = bits.map(b => rows.reduce((m,v,i)=>m | (Number(Boolean(v&b))<<i),0));
const emit = value => console.log(JSON.stringify(value));
const uniqueSorted = xs => [...new Set(xs)].sort((a,b)=>a-b);
const key = bank => bank.map(x => x.toString(16).padStart(4,'0')).join('.') || '-';
const images=[];
for(let l=0;l<2;l++)for(let r=0;r<2;r++)for(let swap=0;swap<2;swap++) {
  let p=[0,l?5:1,2,r?4:3,r?3:4,l?1:5];
  if(swap) p=p.map(x=>[2,3,0,1,5,4][x]);
  const perm=rows.map(v=>rows.indexOf(p.reduce((m,d,i)=>m|((v>>i&1)<<d),0)));
  if(perm.includes(-1))throw Error('invalid graph automorphism');
  const image=new Uint16Array(all+1);
  for(let m=1;m<=all;m++) {
    const low=m&-m;
    image[m]=image[m^low] | 1<<perm[31-Math.clz32(low)];
  }
  images.push(image);
}
function canonical(bank) {
  return images.map(im=>key(uniqueSorted(bank.map(v=>im[v])))).sort()[0];
}
function bankOf(k) {
  return k==='-' ? [] : k.split('.').map(s=>parseInt(s,16));
}
// Recipes use raw gate references or executable A/O tuples. A null atom is
// false and true is represented by a separate sentinel in internal closures.
const TOP=-1, BOT=-2;
function combine(op,x,y) {
  if(x===y)return x;
  if(op==='A') {
    if(x===BOT || y===BOT)return BOT;
    if(x===TOP)return y;
    if(y===TOP)return x;
  } else {
    if(x===TOP || y===TOP)return TOP;
    if(x===BOT)return y;
    if(y===BOT)return x;
  }
  return [op,x,y];
}
function closure(bank) {
  const result=new Map([[all,TOP],[0,BOT]]);
  raw.concat(bank).forEach((v,i)=>{
    for(const [m,tree] of [...result]) {
      const h=m&v;
      if((h&target) && !result.has(h)) result.set(h,combine('A',tree,i));
    }
  });
  return result;
}
function extensions(bank) {
  const conj=closure(bank), opts=new Map([[0,BOT]]), entries=[...conj];
  for(let i=0;i<entries.length;i++)for(let j=0;j<i;j++) {
    const [a,x]=entries[i],[b,y]=entries[j],z=a|b;
    if(z!==a && z!==b && !bank.includes(z) && !opts.has(z))
      opts.set(z,combine('O',x,y));
  }
  return opts;
}
function add(bank,v) { return v ? uniqueSorted([...bank,v]) : bank; }
function listBanks() {
  let layer=new Set(['-']);
  for(let k=0;k<2;k++) {
    const next=new Set();
    for(const name of [...layer].sort()) {
      const bank=bankOf(name);
      for(const v of extensions(bank).keys())next.add(canonical(add(bank,v)));
    }
    layer=next;
  }
  return [...layer].sort();
}
function strongest(wires,s) {
  if(!s)return [0,BOT];
  let m=all, tree=TOP;
  wires.forEach((v,i)=>{
    if((v&s)===s) {m&=v;tree=combine('A',tree,i);}
  });
  return [m,tree];
}
function suffix(bank) {
  const wires=raw.concat(bank);
  const n=new Uint16Array(128);
  for(let s=1;s<=127;s++) {
    let m=all;
    for(const v of wires)if((v&s)===s)m&=v;
    n[s]=m>>7;
  }
  const expr=s=>strongest(wires,s)[1];
  for(let s=1;s<=127;s+=2) {
    const t=target^s, bad=n[s]|n[t];
    const required=(n[s]?s:0)|(n[t]?t:0);
    for(let x=required;;x=(x-1)&required) {
      if(!((n[x]|n[required^x])&bad)) {
        const o=combine('O',expr(x),expr(required^x));
        const side=v=>n[v]?combine('A',expr(v),o):expr(v);
        return combine('O',side(s),side(t));
      }
      if(!x)break;
    }
  }
  return null;
}
// Rediscover a construction of a canonical unordered prefix bank rather than
// assuming its numerical sort is a topological order.
function orderedTrees(goal) {
  function visit(done,trees) {
    if(done.length===goal.length)return goal.map(v=>trees[done.indexOf(v)]);
    const opts=extensions(done);
    for(const v of goal)if(!done.includes(v) && opts.has(v)) {
      const p=visit([...done,v],[...trees,expand(opts.get(v),trees)]);
      if(p)return p;
    }
    return null;
  }
  const result=visit([],[]);
  if(!result)throw Error('unreachable canonical bank');
  return result;
}
function expand(x,trees) {
  if(!Array.isArray(x))return x>=6?trees[x-6]:x;
  return combine(x[0],expand(x[1],trees),expand(x[2],trees));
}
function serialize(tree) {
  const gates=[], memo=new Map();
  function build(x) {
    if(!Array.isArray(x)) {
      if(x<0)throw Error('nonconstant witness has an unsimplified constant');
      return x;
    }
    const [a,b]=[build(x[1]),build(x[2])].sort((u,v)=>u-v);
    const k=x[0]+','+a+','+b;
    if(!memo.has(k)) {memo.set(k,6+gates.length);gates.push([x[0],a,b]);}
    return memo.get(k);
  }
  const output=build(tree);return {gates,output};
}
function replay(c) {
  const ors=c.gates.filter(g=>g[0]==='O').length;
  if(ors>5)throw Error('OR count exceeds five');
  for(let row=0;row<64;row++) {
    const w=bits.map(b=>Boolean(b&row));
    for(const [op,a,b] of c.gates) {
      if(!['A','O'].includes(op)||![a,b].every(i=>Number.isInteger(i)&&i>=0&&i<w.length))
        throw Error('invalid gate');
      w.push(op==='A'?w[a]&&w[b]:w[a]||w[b]);
    }
    if(w[c.output]!==edges.some(([a,b])=>(row>>a & row>>b & 1)!==0))
      throw Error('full-cube mismatch on '+row);
  }
  return {assignments:64,ors};
}

// Restrict the first OR to the union of two raw inputs. In the minimum
// TopForm dirty-prefix case a first raw AND is either clean or has no
// positive edge and simplifies to zero; hence a raw OR is necessary.
const firstBanks = new Set();
for (let a=0; a<6; a++) for (let b=a+1; b<6; b++)
  firstBanks.add(canonical([raw[a] | raw[b]]));
const secondBanks = new Set();
for (const key of firstBanks) {
  const bank = bankOf(key);
  for (const next of extensions(bank).keys())
    secondBanks.add(canonical(add(bank,next)));
}
const orderedBanks = [...secondBanks].sort();
const start = Number(process.argv[2] || 0);
const end = Number(process.argv[3] || orderedBanks.length);
if (!(Number.isInteger(start) && Number.isInteger(end) &&
      0<=start && start<=end && end<=orderedBanks.length)) throw Error('invalid range');
const thirdBanks = new Set();
let hits = 0;
for (const key of orderedBanks.slice(start,end)) {
  const bank=bankOf(key);
  for (const [v,recipe] of extensions(bank)) {
    const name=canonical(add(bank,v));
    if (thirdBanks.has(name)) continue;
    thirdBanks.add(name);
    const candidate=v ? [...bank,v] : bank;
    const tail=suffix(candidate);
    if (tail!==null) {
      const base=orderedTrees(bank);
      const trees=v ? [...base,expand(recipe,base)] : base;
      const circuit=serialize(expand(tail,trees));
      emit({key,v,circuit,replay:replay(circuit)});
      hits++;
    }
  }
}
emit({first:firstBanks.size,second:secondBanks.size,start,end,third:thirdBanks.size,hits});
