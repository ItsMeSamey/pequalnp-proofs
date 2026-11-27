const keys=require('./cut199-m12-seven-meet-banks.json').map(k=>k.split(',').map(Number)),{wedge,exactTree}=require('./cut199-cotree-engine.cjs');
const raw=Array.from({length:5},(_,j)=>Array.from({length:32},(_,i)=>(i>>j&1)<<i).reduce((a,b)=>a|b,0)),[a,b,c,d,e]=raw;
const F=(a&c)|(a&e)|(b&c)|(b&d)|(c&d),M=~F;
const edges=[[0,6],[0,7],[1,3],[1,5],[2,4],[2,7],[3,5],[3,7],[4,5],[4,6],[5,6]].map(([a,b])=>1<<a|1<<b);
const neg=Array.from({length:256},(_,x)=>x).filter(x=>!edges.some(t=>(t&x)===t)).filter((x,i,arr)=>!arr.some(y=>x!==y&&(x&y)===x));
const rows=Array.from({length:32},(_,y)=>Array.from({length:8},(_,x)=>edges.some(e=>(e&(8*y+x))===e)?1<<x:0).reduce((a,b)=>a|b,0));
let need=[];for(let x=0;x<32;x++)for(let y=0;y<32;y++)if(rows[x]&~rows[y])need.push([x,y]);
need=need.filter(([x,y])=>!need.some(([i,j])=>(i!==x||j!==y)&&((i&x)===i)&&((y&j)===y)));if(need.length>30)throw Error('mask overflow');
const all=(1<<need.length)-1,cache=new Map;function cv(w){if(!cache.has(w))cache.set(w,need.reduce((m,[x,y],i)=>m|(((w>>>x)&~(w>>>y)&1)<<i),0));return cache.get(w)}
let sets=new Set,count=0,pass=0,hits=0,states=0,controls=[];
for(let key of keys){let bank=raw.concat(key);function choose(sel,j,meet){if(sel.length===5){if(meet!==F||sel.reduce((v,x)=>v|cv(x),0)!==all)return;let k=sel.slice().sort((a,b)=>a-b).join();if(sets.has(k))return;sets.add(k);count++;
let code=x=>sel.reduce((m,w,i)=>m|((w>>(x>>3)&1)<<(3+i)),x&7),P=edges.map(code),N=neg.map(code);if(!wedge(P,N,8))return;pass++;let z=exactTree(P,N,8,3,Infinity);if(z.tree!==null){hits++;controls.push({ports:sel,tree:z.tree,key})}states+=z.visits;return}
for(let i=j;i<bank.length;i++){let w=bank[i];choose([...sel,w],i,((F&~w)===0)?meet&w:meet)}}choose([],0,-1)}
console.log(JSON.stringify({banks:keys.length,need:need.length,count,pass,hits,states}));require("fs").writeFileSync(require("path").join(__dirname,"cut199-m12-face-four-guards-seven.json"),JSON.stringify(controls));
