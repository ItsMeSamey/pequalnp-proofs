// Five-bit right order: 4,5,8,9,10. Output rows are 32-bit signed integers.
'use strict';
const raw=Array.from({length:5},(_,k)=>Array.from({length:32},(_,x)=>(x>>k&1)<<x).reduce((a,b)=>a|b,0));
const [a,b,c,d,e]=raw,F=(a&c)|(a&e)|(b&c)|(b&d)|(c&d),Q=[d|e,a|c,b|e];
const patterns=[];
for(let J=1;J<8;J++)for(let bare=0;bare<16;bare++){
 const s=[1,2,4,J].map((v,i)=>v|((bare>>i&1)<<3));
 if(s.some(x=>s.some(y=>(x&y)!==0&&(x&y)!==x&&(x&y)!==y)))continue;
 patterns.push({J,bare});
}
function witnesses(bank){
 const result=[];
 for(const {J,bare} of patterns){
  const allowed=(w,i)=>!(bare>>i&1)||!(F&~w);
  for(const extra of bank){
   if(!allowed(extra,3))continue;
   const choices=Q.map((q,i)=>bank.filter(w=>allowed(w,i)&&!((q^(w&(J>>i&1?extra:-1)))&~F)));
   if(choices.some(c=>!c.length))continue;
   for(const g0 of choices[0])for(const g1 of choices[1])for(const g2 of choices[2]){
    const guards=[g0,g1,g2,extra];let mask=-1;
    guards.forEach((w,k)=>{if(bare>>k&1)mask&=w});
    for(const leaf of bank)if((leaf&mask)===F)result.push({J,bare,guards,leaf});
   }
  }
 }
 return result;
}
module.exports={patterns,witnesses,F,Q,raw};
if(require.main===module){
 const banks=require('./cut199-m12-seven-meet-banks.json');
 let hits=0;for(const s of banks)hits+=witnesses([...raw,...s.split(',').map(Number)]).length;
 if(hits)throw Error('unexpected lower-cost witness');
 console.log({patterns:patterns.length,sevenGateBanks:banks.length,hits});
}
