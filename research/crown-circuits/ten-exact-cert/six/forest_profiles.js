const n=6,full=(1n<<64n)-1n;
const halves=Array.from({length:n},(_,j)=>{let m=0n;for(let w=0;w<64;w++)if((w>>j)&1)m|=1n<<BigInt(w);return m;});
const seen=new Map();
function walk(parent){
 if(parent.length<n){for(let b=-1;b<2*parent.length;b++)walk([...parent,b]);return;}
 function shape(i){
  const children=[[],[]];
  for(let j=i+1;j<n;j++)if(parent[j]>=0&&(parent[j]>>1)===i)children[parent[j]&1].push(shape(j));
  return "("+children.map(s=>s.sort().join("")).sort().join("/")+")";
 }
 const key=parent.flatMap((b,i)=>b<0?[shape(i)]:[]).sort().join("");
 if(seen.has(key))return;
 const U=[],B=[];
 for(let j=0;j<n;j++){const u=parent[j]<0?full:B[parent[j]];U.push(u);B.push(u&halves[j],u&~halves[j]);}
 const traces=new Set(Array.from({length:64},(_,w)=>B.reduce((a,b,i)=>a|(Number((b>>BigInt(w))&1n)<<i),0)));
 if(traces.size>=10)seen.set(key,U.map(String));
}
walk([]);
console.log(JSON.stringify([...seen.values()]));
