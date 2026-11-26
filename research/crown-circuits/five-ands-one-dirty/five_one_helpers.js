function I(t){let F=0xffffffff>>>0,b=[];for(let j=0;j<4;j++){let w=0;for(let p=0;p<32;p++)if((p>>j)&1)w|=1<<p;b.push((~w)>>>0,w>>>0)}let u=b.filter((_,i)=>!(i&1)&&i<2*t).reduce((a,c)=>(a|c)>>>0,0);b.push((u&65535)>>>0,(u&0xffff0000)>>>0);function size(x){let n=0;x=x>>>0;while(x){x=(x&(x-1))>>>0;n++}return n}return {b,u,F,size}}
function search(t,q,need){let {b,F,size}=I(t),seen=Array.from({length:q+1},()=>new Set()),found=null,trials=0,max=0;
function fold(a,h){if(found)return;let id=h.slice().sort((a,b)=>a-b).join(',');if(seen[h.length].has(id))return;seen[h.length].add(id);trials++;
let p=new Set(a);for(let x of a)for(let y of a)p.add((x|y)>>>0);p.delete(F);let list=[...p].map(z=>(~z)>>>0).sort((x,y)=>size(x)-size(y));let min=[];for(let x of list)if(!min.some(y=>((y&x)>>>0)==y))min.push(x);
function dfs(pos,k,left){if(k==0)return [];if(pos.length<k)return null;for(let i=0;i<=pos.length-k;i++){let w=pos[i];let later=pos.slice(i+1).filter(z=>!(w&z));let a=dfs(later,k-1,left);if(a)return [w,...a]}return null}
let ans=dfs(min,need,F);if(ans){found={h,ans};return}
if(h.length<q){for(let z of p)if(!a.includes(z))fold([...a,z],[...h,z]);}}
fold(b,[]);return {t,q,need,trials,found}}
for(let d=6;d>=3;d--)for(let t=1;t<=4;t++)console.log(JSON.stringify(search(t,6-d,14-d)));
