// Isolated right raw 3, with at most seven pure gates on the other five inputs.
const fs=require('fs'),path=require('path'),D=__dirname;
const raw = Array.from({length:5},(_,i)=>Array.from({length:32},(_,x)=>(x>>i&1)<<x).reduce((a,b)=>a|b,0));
const [a,c,b,d,e]=raw, T=(a&b)|(a&e)|(b&c)|(b&d)|(c&d);
const edge=[[0,9],[0,10],[1,4],[1,8],[2,5],[2,10],[3,6],[3,7],[4,8],[4,10],[5,8],[5,9],[6,7],[6,10],[7,9],[8,9]].map(([x,y])=>1<<x|1<<y);
const pack=(s,labels)=>labels.reduce((z,v,i)=>z|((s>>i&1)<<v),0);
const rows=Array.from({length:32},(_,x)=>Array.from({length:64},(_,y)=>{let z=pack(x,[4,5,8,9,10])|pack(y,[0,1,2,6,7,3]);return edge.some(m=>(z&m)===m)}));
let need=[];for(let x=0;x<32;x++)for(let y=0;y<32;y++)if(rows[x].some((v,i)=>v&&!rows[y][i]))need.push([x,y]);
need=need.filter(([x,y])=>!need.some(([i,j])=>(x!==i||y!==j)&&(x&i)===i&&(y&j)===y));
const bank=[...raw], seen=new Set(), witness=new Set();let factorPrograms=0;

const certs=[[513,1025,18,36,136,1088],[513,1025,258,36,136,1088],[513,18,36,72,136,1088],[513,258,36,72,136,1088],[513,1025,18,36,72,640],[513,1025,258,36,72,640],[1025,18,36,72,136,640],[1025,258,36,72,136,640]].flatMap(c=>edge.filter(e=>!(e&199)).map(e=>[...c,e].map(x=>[4,5,8,9,10].reduce((s,b,i)=>s|((x>>b&1)<<i),0))));
const active=new Map();
function good(w){if(!active.has(w))active.set(w,certs.every(c=>c.some(x=>(w>>>x)&1)));return active.get(w)}
function check(){seen.add(bank.slice(5).sort((a,b)=>a-b).join(','));}
function visit(depth,intersection,unused){
 if(depth===7){
  if(intersection===T){check();for(let j=1;j<bank.length;j++)for(let i=0;i<j;i++)for(const v of [bank[i]&bank[j],bank[i]|bank[j]])if(!bank.includes(v)){bank.push(v);check();bank.pop()}return}
  let bad=intersection&~T;
  for(let j=1;j<bank.length;j++)if(!(bank[j]&bad))for(let i=0;i<j;i++){if((unused&~(1<<i|1<<j))||(bank[i]&bad))continue;
  let v=bank[i]|bank[j];if((T&~v)||bank.includes(v))continue;bank.push(v);factorPrograms++;check();bank.pop()}return;
 }
 for(let j=1;j<bank.length;j++)for(let i=0;i<j;i++)for(let op=0;op<2;op++){
  let v=op?bank[i]&bank[j]:bank[i]|bank[j];if(bank.includes(v))continue;let ok=true;
  for(let h=Math.max(5,j+1);h<bank.length;h++)if((bank[h]>>>0)>(v>>>0)){ok=false;break}if(!ok)continue;
  let covers=(v&T)===T;bank.push(v);visit(depth+1,covers?v&intersection:intersection,(unused&~(1<<i|1<<j))|(covers?0:1<<(bank.length-1)));bank.pop()
 }
}
visit(1,-1,0);console.log({banks:seen.size});fs.writeFileSync(path.join(D,'cut199-m12-seven-meet-banks.json'),JSON.stringify([...seen]));