const fs=require('fs'),path=require('path'),D=__dirname,bank=require('./cut199-left-general-parity.json');
const E=[72,136,1088,640,192,513,1025,18,258,36,1028,272,1040,288,544,768],L=199,R=2047^L;
const N=Array.from({length:2048},(_,i)=>i).filter(x=>E.every(e=>(x&e)!==e)).filter((x,i,a)=>!a.some(y=>y!==x&&(x&y)===x));
const cv=x=>[0,1,2,6,7].reduce((s,b,j)=>s|((x>>b&1)<<j),0);
const nums=Array.from({length:64},(_,i)=>i),pc=nums.map(i=>i.toString(2).replace(/0/g,'').length);
function audit(key,sig){
 const ws=key.split(',').map(Number),code=x=>ws.reduce((s,w,i)=>s|((w>>cv(x)&1)<<i),0),[g,a,b,f]=sig;
 const pre=[g,g,a,b,f],opts=E.map((e,i)=>i<5?[pre[i]]:nums.filter(s=>!(s&~code(e))&&N.every(I=>(e&R&~I)||(s&~code(I)))));
 let count=0,full=0,rel=0;
 function run(alpha){
   count++;
   const B=N.map(I=>nums.filter(c=>!(c&code(I))&&E.every((e,j)=>{
    let z=pc[c&alpha[j]];return z<=1&&((e&R&~I)||z==1)&&((e&L&~I)||!z);
   })));
   if(B.some(opts=>!opts.length))return;
   full++;
   // Every right coefficient column is a linear functional of alpha XOR f.
   // On e36 it is either 0, or belongs to the sole Z which must reject 9 and 10.
   const T=nums.slice(1).map(t=>{
     let rows=0;for(let i=0;i<E.length;i++)if(pc[t&(alpha[i]^f)]%2)rows|=1<<i;
     if(!rows||(rows&1)&&(rows&12))return null;
     const cols=N.map((I,j)=>!E.some((e,i)=>(rows>>i&1)&&!(e&R&~I))
       &&B[j].some(c=>E.every((e,i)=>!(rows>>i&1)||!(c&alpha[i]))));
     return cols.some(Boolean)?{t,rows,cols}:null;
   }).filter(Boolean);
   if(!B.every((opts,j)=>opts.some(c=>E.every((e,i)=>(c&alpha[i])||T.some(v=>(v.rows>>i&1)&&v.cols[j])))))return;
   rel++;
 }
 function rec(i,alpha){if(i===E.length)return run(alpha);for(let s of opts[i])rec(i+1,[...alpha,s])}
 rec(0,[]);return {count,full,rel};
}
const out=[];
for(const {key,cost,sig} of bank) {let keep=[];for(const s of sig) {let v=audit(key,s);if(v.rel)keep.push([s,v])}
 console.log({key,cost,kept:keep.length});if(keep.length)out.push({key,cost,keep})}
fs.writeFileSync(path.join(D,'cut199-parity-full.json'),JSON.stringify(out));
