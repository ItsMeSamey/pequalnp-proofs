function reachableBases(us){
const F=(1n<<64n)-1n,U=us.map(BigInt),pairs=U.map((v,j)=>{let h=0n;for(let p=1<<j;p<64;p++)if(p&(1<<j))h|=1n<<BigInt(p);return[v&h,v&~h]}),B=new Set(pairs.flat()),required=new Set(U.filter(x=>x!==F&&!B.has(x))),fixed=new Set([...B,...U]),demands=U.filter(x=>x!==F);
if(!required.size)return [[]];
const key=a=>a.map(String).sort().join('/');
let todo=[[]],seen=new Set(['']),answers=[];
while(todo.length){let extra=todo.pop();if(answers.some(A=>A.every(v=>extra.includes(v))))continue;let allowed=new Set([...fixed,...extra]),given=new Set([F]);
for(;;){let n=given.size;for(let j=0;j<6;j++)if(given.has(U[j]))for(let b of pairs[j])given.add(b);let a=[...given];for(let i=0;i<a.length;i++)for(let j=0;j<i;j++){let x=a[i]|a[j];if(allowed.has(x))given.add(x)}if(given.size===n)break}
if(U.every(x=>given.has(x))){answers.push(extra);continue}
if(extra.length+required.size>=4)continue;
let a=[...given];for(let i=0;i<a.length;i++)for(let j=0;j<i;j++){let x=a[i]|a[j];if(allowed.has(x)||!demands.some(v=>(v&x)===x))continue;let nxt=extra.concat(x),token=key(nxt);if(!seen.has(token)){seen.add(token);todo.push(nxt)}}
}return answers.filter(A=>!answers.some(B=>B.length<A.length&&B.every(x=>A.includes(x))))}
const fs=require('fs');const expected=require('./protected.js');const key=sets=>JSON.stringify(sets.map(s=>s.map(String).sort()).sort((a,b)=>a.join().localeCompare(b.join())));
let checked=0;for(const line of fs.readFileSync(process.argv[2],'utf8').trim().split('\n')){const [id,...us]=line.split(/\s+/);if(key(reachableBases(us))!==key(expected(us,true)))throw Error('protected basis mismatch '+id);checked++;}console.log('Independently matched protected bases on '+checked+' hard profiles.');

