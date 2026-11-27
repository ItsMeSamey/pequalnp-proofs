// Six pure gates after pinning 3=0 are all necessary for the free conjunction.
// Raw order 4,5,8,9,10. Canonical adjacent commuting uses unsigned truth-table order.
const raw = Array.from({length:5},(_,i)=>Array.from({length:32},(_,x)=>(x>>i&1)<<x).reduce((a,b)=>a|b,0));
const [a,c,b,d,e]=raw, T=(a&b)|(a&e)|(b&c)|(b&d)|(c&d);
const edge=[[0,9],[0,10],[1,4],[1,8],[2,5],[2,10],[3,6],[3,7],[4,8],[4,10],[5,8],[5,9],[6,7],[6,10],[7,9],[8,9]].map(([x,y])=>1<<x|1<<y);
const pack=(s,labels)=>labels.reduce((z,v,i)=>z|((s>>i&1)<<v),0);
const rows=Array.from({length:32},(_,x)=>Array.from({length:64},(_,y)=>{let z=pack(x,[4,5,8,9,10])|pack(y,[0,1,2,6,7,3]);return edge.some(m=>(z&m)===m)}));
let need=[];for(let x=0;x<32;x++)for(let y=0;y<32;y++)if(rows[x].some((v,i)=>v&&!rows[y][i]))need.push([x,y]);
need=need.filter(([x,y])=>!need.some(([i,j])=>(x!==i||y!==j)&&(x&i)===i&&(y&j)===y));
const bank=[...raw], seen=new Set(), witness=new Set();let factorPrograms=0;
function check(){
 let key=bank.slice(5).sort((a,b)=>a-b).join(',');if(seen.has(key))return;seen.add(key);
 function take(i,sel){if(sel.length===5){if(sel.reduce((m,v)=>(T&~v)?m:m&v,-1)!==T)return;if(need.every(([x,y])=>sel.some(v=>(v>>>x&1)&&!(v>>>y&1))))witness.add(sel.slice().sort((a,b)=>a-b).join(','));return}
 for(let j=i;j<=bank.length-(5-sel.length);j++)take(j+1,[...sel,bank[j]])}take(0,[]);
}
function visit(depth,intersection,unused){
 for(let j=1;j<bank.length;j++)for(let i=0;i<j;i++)for(let op=0;op<2;op++){
  let v=op?bank[i]&bank[j]:bank[i]|bank[j];let covers=(T&~v)===0;
  if(depth===6&&(!covers||(intersection&v)!==T))continue;
  let pending=unused&~(1<<i|1<<j);if(!covers)pending|=1<<bank.length;
  if(depth===6&&pending)continue;
  if(bank.includes(v))continue;
  let ok=true;for(let h=Math.max(5,j+1);h<bank.length;h++)if((bank[h]>>>0)>(v>>>0)){ok=false;break}if(!ok)continue;
  bank.push(v);
  if(depth===6){factorPrograms++;check()}else visit(depth+1,covers?intersection&v:intersection,pending);
  bank.pop();
 }
}
visit(1,-1,0);console.log(JSON.stringify({need:need.length,factorPrograms,banks:seen.size,portSets:witness.size,examples:[...witness].slice(0,4)}));
