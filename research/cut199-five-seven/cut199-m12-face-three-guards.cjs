// Upper face for exactly five independent guards at 3=1. Up to five paid survivors.
const budget=Number(process.argv[2]||6);
const raw=Array.from({length:5},(_,j)=>Array.from({length:32},(_,i)=>(i>>j&1)<<i).reduce((a,b)=>a|b,0)),[a,b,c,d,e]=raw;
const F=(a&c)|(a&e)|(b&c)|(b&d)|(c&d),M=~F,goal=[d|e,a|c,b|e].map(t=>t&M),pop=x=>x?1+pop(x&(x-1)):0;
const seen=new Set,hit=new Set;
let states=0,goalBanks=0,termBanks=0;
function visit(bank,labels){let k=bank.slice(5).sort((x,y)=>x-y).join();if(seen.has(k))return;seen.add(k);states++;let paid=bank.length-5;
if(labels===7){goalBanks++;
let gs=goal.map(g=>bank.filter(v=>(v&M)===g)),ok=false;
for(let g0 of gs[0])for(let g1 of gs[1])for(let g2 of gs[2]){let guards=[-1,g0,g1,g2],parts=[];
for(let p of bank)for(let q of guards){let t=p&q;if(t&&!(t&~F))parts.push(t)}
if(parts.some(u=>parts.some(v=>(u|v)===F))){ok=true;hit.add(k);break}}
if(ok)termBanks++;}
if(paid>=budget)return;
for(let i=0;i<bank.length;i++)for(let j=0;j<i;j++)for(let v of [bank[i]&bank[j],bank[i]|bank[j]]){if(bank.includes(v))continue;
let idx=goal.indexOf(v&M),l=idx<0?labels:labels|1<<idx;if(3-pop(l)>budget-1-paid)continue;visit([...bank,v],l)}
}
visit(raw,0);console.log(JSON.stringify({states,goalBanks,termBanks,hits:[...hit].slice(0,10)}));
