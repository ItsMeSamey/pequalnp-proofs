// Exact 5+7 one-fork decision for fixed physical boundary ports, on 16 edges and 24 maximal negatives.
const {exactTree,wedge}=require('./cut199-cotree-engine.cjs');
const parentSource=exactTree.toString();
const edits=[
 ['left=6,limit=250000','colors,limit=Infinity'],
 ['lc=(1<<left)-1,rc=full^lc','lc=colors.reduce((m,c,i)=>m|((c&1)?1<<i:0),0),rc=colors.reduce((m,c,i)=>m|((c&2)?1<<i:0),0)'],
 ['const j=ids.findIndex(i=>(i<left)!==(ids[0]<left))','const j=ids.findIndex((i,k)=>k>0&&(colors[i]|colors[ids[0]])===3)']
];
let definition=parentSource;
for(const [a,b] of edits){if(!definition.includes(a))throw Error('changed tree-engine API');definition=definition.replace(a,b)}
const sideMask=k=>k===0||(k&(k-1))===0;
const coloredTree=Function('sideMask','return ('+definition+')')(sideMask);
const edges=[513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768];
const neg=Array.from({length:2048},(_,y)=>y).filter(x=>!edges.some(e=>(x&e)===e)&&Array.from({length:11},(_,i)=>1<<i).every(b=>(x&b)||edges.some(e=>((x|b)&e)===e)));
const rows=[...edges,...neg],N=rows.length,FULL=(1n<<BigInt(N))-1n,P=(1n<<16n)-1n;
function bankWords(left,right){
 const pack=(x,s)=>s.reduce((z,k,j)=>z|((x>>k&1)<<j),0);
 return [...left,...right].map((w,i)=>rows.reduce((v,x,j)=>v|((BigInt(w)>>BigInt(pack(x,i<5?[0,1,2,6,7]:[3,4,5,8,9,10]))&1n)<<BigInt(j)),0n));
}
function idx(mask,n){return Array.from({length:n},(_,i)=>i).filter(i=>mask>>i&1)}
function rename(t,names){return Number.isInteger(t)?names[t]:[t[0],rename(t[1],names),rename(t[2],names)]}
function separate(words,colors,ones,zeros,names){
 const q=[[],[]];
 for(let j=0;j<N;j++){
  const b=1n<<BigInt(j);if(!((ones|zeros)&b))continue;
  const code=words.reduce((v,w,i)=>v|(Number(w>>BigInt(j)&1n)<<i),0);
  q[(zeros&b)?1:0].push(code);
 }
 if(!wedge(q[0],q[1],words.length))return null;
 const result=coloredTree(q[0],q[1],words.length,colors);
 if(!result.complete)throw Error('tree bound reached');
 return result.tree===null?null:rename(result.tree,names);
}
function enumerate(words,colors,names){
 const memo=new Map();
 function calc(mask){
  if(memo.has(mask))return memo.get(mask);
  const s=idx(mask,words.length), out=new Map();
  if(s.length===1){out.set(words[s[0]],names[s[0]])}
  else if(s.reduce((z,i)=>z|colors[i],0)===3){
   for(let a=(mask-1)&mask;a;a=(a-1)&mask){
    const b=mask^a;if(a>b)continue;
    for(const [x,tx] of calc(a))for(const [y,ty] of calc(b)){
     for(const [v,op] of [[x|y,0],[x&y,1]])if(!out.has(v))out.set(v,[op,tx,ty]);
    }
   }
  }
  memo.set(mask,out);return out;
 }
 return calc((1<<words.length)-1);
}
function test(words,mask){
 const inside=idx(mask,12), outside=idx(4095^mask,12),n=inside.length;
 if(!n)return null;
 const color=i=>i<5?1:2, donorColor=inside.reduce((m,i)=>m|color(i),0);
 if(n>1&&donorColor!==3)return null;
 const iw=inside.map(i=>words[i]),ic=inside.map(color),ow=outside.map(i=>words[i]),oc=[...outside.map(color),donorColor,donorColor],on=[...outside,12,12];
 if(n<=7){
  let one=0n,zero=0n;
  for(let i=0;i<16;i++)for(let j=16;j<N;j++){
   if(ow.some(w=>(w>>BigInt(i)&1n)&&!(w>>BigInt(j)&1n)))continue;
   one|=1n<<BigInt(i);zero|=1n<<BigInt(j);
  }
  for(const [v,donor] of enumerate(iw,ic,inside)){
   if((one&~v)||(zero&v))continue;
   const exterior=separate([...ow,v,v],oc,P,FULL^P,on);
   if(exterior!==null)return {donor,exterior};
  }
 } else {
  const sym=FULL<<BigInt(N), ext=ow.map(w=>w|(w<<BigInt(N)));
  for(const [v,exterior] of enumerate([...ext,sym,sym],oc,on)){
   const e0=v&FULL,e1=v>>BigInt(N);
   if((e0&~P)||(P&~e1))continue;
   const donor=separate(iw,ic,P&~e0,(FULL^P)&e1,inside);
   if(donor!==null)return {donor,exterior};
  }
 }
 return null;
}
function normalized(words,anchor){
 if(words.length!==12||![3,4].includes(anchor))throw Error('expected five left and seven right ports, repeated left index 3 or 4');
 const names=[...words.keys(),anchor], all=names.map(i=>words[i]);
 return separate(all,Array(13).fill(3),P,FULL^P,names);
}
module.exports={bankWords,test,normalized,rows};
