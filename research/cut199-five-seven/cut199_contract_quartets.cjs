const fs=require('node:fs'),path=require('node:path');
const dir=path.join(__dirname,'cut199-tree-two-hit');
const src=fs.readFileSync(path.join(dir,'verify.cjs'),'utf8');
const end=src.indexOf('const check=eightGates(survivors)');
if(end<0)throw Error('changed source');
const quartets=Function('require','__dirname',src.slice(0,end)+'return survivors;')(require,dir);
const raw=Array.from({length:5},(_,i)=>Array.from({length:32},(_,x)=>(x>>i&1)<<x).reduce((a,b)=>a|b,0));
const [a,b,c,d,e]=raw,F=(a&c)|(a&e)|(b&c)|(b&d)|(c&d),Q=[d|e,a|c,b|e];
const out=[];
for(const w of quartets){
 if(Q.some(v=>w.filter(t=>!((v^t)&~F)).length!==1))throw Error('ambiguous query role');
 const ids=Q.map(v=>w.findIndex(t=>!((v^t)&~F)));
 if(ids.includes(-1)||new Set(ids).size!==3)continue;
 const bi=w.findIndex((_,i)=>!ids.includes(i)),bare=w[bi];
 const guard=ids.filter(i=>(bare&w[i])===F);
 if(bare===F)guard.push(-1);
 if(guard.length)out.push({w,bare:bi,queries:ids,guard});
}
fs.writeFileSync(path.join(__dirname,'cut199-contraction-quartets.json'),JSON.stringify(out));
console.log({from:quartets.length,pass:out.length,withBareF:out.filter(v=>v.guard.includes(-1)).length,words:new Set(out.flatMap(v=>v.w)).size});
