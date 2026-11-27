const fs=require('fs'),path=require('path'),D=__dirname;
const bank=JSON.parse(fs.readFileSync(path.join(D,'cut199-left-bank-cotree-survivors.json'))).hits;
const E=[513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768],L=199,R=2047^L;
const N=Array.from({length:2048},(_,i)=>i).filter(x=>E.every(e=>(x&e)!==e)).filter((x,i,a)=>!a.some(y=>y!==x&&(x&y)===x));
const cv=x=>[0,1,2,6,7].reduce((s,b,j)=>s|((x>>b&1)<<j),0);
const nums=Array.from({length:64},(_,i)=>i),pc=nums.map(i=>i.toString(2).replace(/0/g,'').length);
function audit(key){
 const ws=key.split(',').map(Number), code=x=>ws.reduce((s,w,i)=>s|((w>>cv(x)&1)<<i),0);
 const rows=[72,136,1088,640,192];
 const opts=rows.map(e=>nums.filter(a=>a && !(a&~code(e))&&N.every(I=>(e&R&~I)||(a&~code(I)))));
 const choices=N.map(I=>nums.filter(b=>!(b&code(I))));
 let sig=[];
 for(let g of opts[0])if(opts[1].includes(g))
 for(let a of opts[2])for(let b of opts[3])for(let f of opts[4]){
   const parity=a^b^f;if(!parity||parity===g)continue;
   const masks=[g,g,a,b,f];
   if(N.every((I,i)=>choices[i].some(col=>rows.every((e,j)=>{
      const v=pc[col&masks[j]];if(v>1)return false;
      if(!(e&R&~I))return v===1;
      if(!(e&L&~I))return v===0;
      return true;
   }))))sig.push([g,a,b,f]);
 }
 return sig;
}
const survivors=[],tally={};
for(const [key,cost] of bank){let sig=audit(key);if(!sig.length)continue;survivors.push({key,cost,sig});tally[cost]=(tally[cost]||0)+1}
console.log({tested:bank.length,survivors:survivors.length,tally,signatures:survivors.reduce((n,s)=>n+s.sig.length,0)});
if(process.argv[2])fs.writeFileSync(process.argv[2],JSON.stringify(survivors));
