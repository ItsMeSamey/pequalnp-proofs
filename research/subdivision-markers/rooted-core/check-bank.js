function feasibleF(edges,mask,n){
 const adj=Array.from({length:n},()=>[]);
 edges.forEach(([u,v],i)=>{if(mask>>i&1){adj[u].push(v);adj[v].push(u)}});
 const seen=new Set();
 for(let i=0;i<n;i++)if(!seen.has(i)){const queue=[i];seen.add(i);let deg=0;for(let h=0;h<queue.length;h++){const u=queue[h];deg+=adj[u].length;for(const v of adj[u])if(!seen.has(v)){seen.add(v);queue.push(v)}}if((deg/2)%2)return false}
 return true;
}
function inspect(edges,n){
 const lim=1<<edges.length,real=Array.from({length:lim},(_,x)=>feasibleF(edges,x,n)),direct=new Set();
 let matching=0;
 for(let m=0;m<lim;m++){let used=0,size=0,ok=true;edges.forEach(([u,v],i)=>{if(m>>i&1){let p=(1<<u)|(1<<v);if(used&p)ok=false;used|=p;size++}});if(ok)matching=Math.max(matching,size)}
 for(let o=0;o<lim;o++){const labels=edges.map(([u,v],i)=>1<<((o>>i&1)?u:v)),sum=[0];for(const g of labels)sum.push(...sum.map(z=>z^g));sum.forEach((s,i)=>{if(!s)direct.add(i)})}
 if(real.some((x,i)=>x!==direct.has(i)))throw Error('states');
 function find(span,p,d){if(!d)return true;for(let j=p;j>=d-1;j--)for(let v=1<<j;v<2<<j;v++){const add=span.map(z=>z^v);if(!add.some(z=>real[z])&&find(span.concat(add),j-1,d-1))return true}return false}
 return {matching,larger:find([0],edges.length-1,matching+1)}
}
let checked=0,example=null;for(let n=1;n<=5;n++){const all=[];for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)all.push([i,j]);for(let g=0;g<1<<all.length;g++){let edges=all.filter((_,i)=>g>>i&1);if(edges.length>6)continue;let result=inspect(edges,n);checked++;if(result.larger&&!example)example={edges,result}}}
console.log({checked,example});
