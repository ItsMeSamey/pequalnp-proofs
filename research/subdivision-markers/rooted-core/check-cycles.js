function double4(x){return ((x<<1)^((x&8)?19:0))&15}
function multiple(v,values){return values.reduce((sum,bit,i)=>sum^((v>>i&1)?bit:0),0)}
function badBlock(mask,n){
  if(!mask)return false;
  if(mask===(1<<n)-1)return Boolean(n%2);
  let anchor=0;while(mask>>anchor&1)anchor++;
  let run=0;
  for(let d=1;d<=n;d++){
    if(mask>>((anchor+d)%n)&1)run++;
    else{if(run%2)return true;run=0}
  }
  return false;
}
const powers=[1];for(let i=1;i<15;i++)powers.push(double4(powers.at(-1)));
const basis=Array.from({length:4},(_,i)=>powers[3*i]);
const match=Array.from({length:4},(_,i)=>(1<<i)|(1<<((i+2)%5)));
const phi=Array(16);for(let i=0;i<16;i++)phi[multiple(i,basis)]=multiple(i,match);
const seen=new Set();
for(let z=0;z<16;z++)for(let odd=0;odd<8;odd++){
  const words=[phi[z],phi[double4(z)],phi[double4(double4(z))]].map((v,i)=>v^(odd>>i&1));
  if((odd||z)&&!words.some(w=>badBlock(w,5)))throw Error('joint C5 code');
  seen.add(words.join(','));
}
if(seen.size!==128)throw Error('joint dimension');
const columns=[1];for(let i=1;i<7;i++){const x=columns.at(-1);columns.push(((x<<1)^((x&4)?11:0))&7)}
let count=0;for(let v=0;v<128;v++)if(!multiple(v,columns)){
  if(v&&!badBlock(v,7))throw Error('C7 code');
  count++;
}
if(count!==16)throw Error('C7 dimension');
console.log('All 16 C7 and 128 joint C5 kernel words verified');
