'use strict';
const fs=require('node:fs'),path=require('node:path');
const {patterns,F,raw}=require('./cut199-m12-four-guard-template.cjs');
const Q=[24,5,18]; // singleton supports, bit order 4,5,8,9,10
const masks=Array.from({length:32},(_,x)=>x);
const words=masks.map(s=>raw.reduce((w,x,i)=>(s>>i&1)?w|x:w,0));
const banks=new Map(),counts=[],roles=[];
for(const {J,bare} of patterns){
 let ordered=0;
 for(const d of masks){
  const G=Q.map((q,i)=>masks.filter(g=>((J>>i&1)?(g&d):g)===q&&
   !((words[g]&((J>>i&1)?words[d]:-1))&~words[q]&~F)));
  for(const a of G[0])for(const b of G[1])for(const c of G[2]){
   const guards=[a,b,c,d],meet=guards.reduce((w,g,i)=>(bare>>i&1)?w&words[g]:w,-1);
   for(const leaf of masks){
    if(words[leaf]&meet&~F)continue;
    ordered++;
    const role=[a,b,c,d,leaf],s=role.slice().sort((x,y)=>x-y),key=s.join(',');
    roles.push({J,bare,role});
    if(!banks.has(key))banks.set(key,{s,example:{J,bare,role}});
   }
  }
 }
 counts.push({J,bare,ordered});
}
const out={counts,roles,banks:[...banks.values()]};
fs.writeFileSync(path.join(__dirname,'cut199-four-guard-singletons.json'),JSON.stringify(out));
console.log({templates:counts.length,ordered:counts.reduce((n,c)=>n+c.ordered,0),banks:banks.size});
