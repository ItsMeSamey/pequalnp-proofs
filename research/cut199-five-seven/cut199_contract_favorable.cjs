const fs=require('node:fs'),path=require('node:path');
const {check}=require('./cut199_check_eight_portfolio.cjs');
const banks=require('./cut199-contract-supports.json');
const E=[5,17,6,10,12];
const word=Array.from({length:32},(_,s)=>Array.from({length:32},(_,y)=>Number(!!(s&y)||E.some(e=>(y&e)===e))<<y).reduce((a,b)=>a|b,0));
let tested=0,hits=[];
for(let i=0;i<banks.length;i++){
 const p=banks[i].s.map(s=>word[s]);
 for(let h=0;h<32;h++){
  const r=check(p,word[h]);tested+=r.length;
  for(const t of r)if(t.tree!==null)hits.push({i,h,anchor:t.anchor,tree:t.tree});
 }
}
fs.writeFileSync(path.join(__dirname,'cut199-contract-favorable.json'),JSON.stringify(hits));
console.log(JSON.stringify({tested,hits:hits.length,banks:new Set(hits.map(t=>t.i)).size}));
