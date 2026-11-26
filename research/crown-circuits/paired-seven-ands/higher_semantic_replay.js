// Seven-coordinate adaptation of calculus/six_single_early.js solveBase.
function solveBase(raw,extra=[]) {
  const full=(1n<<128n)-1n, dirs=raw.map(BigInt);
  let big=[];
  for(let j=0;j<7;j++){let s=0n;for(let i=0;i<128;i++)if(i>>j&1)s|=1n<<BigInt(i);big.push(s&dirs[j],(~s)&dirs[j]);}
  let atoms=[full];for(const v of big)atoms=atoms.flatMap(a=>[a&v,a&~v].filter(Boolean));
  const L=atoms.length;if(L>32)throw Error("width overflow");
  const cv=m=>atoms.reduce((a,b,j)=>a|((b&m)?1<<j:0),0);
  const F=cv(full),B=[...new Set(big.map(cv).filter(x=>x!==0))],W=[...new Set(dirs.map(cv))].filter(x=>x!==F&&!B.includes(x)),budget=5-W.length-extra.length;
  function wt(x){x-=(x>>>1)&0x55555555;x=(x&0x33333333)+((x>>>2)&0x33333333);return (((x+(x>>>4))&0x0f0f0f0f)*0x01010101)>>>24;}
  const cl=new Set([0]);for(const b of B)for(const u of [...cl])cl.add(u|b);
  const pool=[...cl].sort((a,b)=>wt(a)-wt(b)||(a>>>0)-(b>>>0)),n=pool.length;
  const id=new Map(pool.map((v,j)=>[v,j])),base=[...B,...W,...extra.map(cv)].map(v=>id.get(v)),join=new Uint16Array(n*n),wei=pool.map(v=>wt(F^v));
  for(let i=0;i<n;i++)for(let j=0;j<n;j++)join[i*n+j]=id.get(pool[i]|pool[j]);
  let visits=0;
const samples=atoms.map(a=>{let i=0;while(!((a>>BigInt(i))&1n))i++;return i;});
const atomAt=Array.from({length:128},(_,p)=>atoms.findIndex(a=>!!(a&(1n<<BigInt(p)))));
const perms=[];for(let f=0;f<128;f++){let ok=true;for(const u of [...dirs,...extra]){for(let p=0;p<128;p++)if(((u>>BigInt(p))&1n)!==((u>>BigInt(p^f))&1n)){ok=false;break;}if(!ok)break;}if(ok&&f)perms.push(samples.map(p=>atomAt[p^f]));}
function isCanon(d){const nz=d>>>0;for(const pp of perms){let a=d,v=0;while(a){const bit=a&-a,j=31-Math.clz32(bit);v|=1<<pp[j];a^=bit;}if((v>>>0)<nz)return false;}return true;}
  const maxSize=Math.floor(L/12);
  for(let ak=0;ak<n;ak++){
    const anc=pool[ak],def=F^anc,sw=wei[ak];
    if(!isCanon(def)||!sw||sw>maxSize||base.some(k=>join[ak*n+k]===k))continue;
    if(sw===1&&L<24&&(31-Math.clz32(def))>2*L-24)continue;
    const ins=[],out=[],valid=new Uint8Array(n),tgt=[];
    for(let v=0;v<n;v++){
      const m=pool[v],d=m^F;
      if(wei[v]>=sw&&wei[v]<=L-11&&!(d&def)&&(wei[v]!==sw||(d>>>0)>(def>>>0))&&!base.some(k=>join[k*n+v]===k)){tgt.push(v);valid[v]=1;}
      if(m!==0&&m!==F&&v!==ak&&!base.includes(v)&&join[ak*n+v]!==v)(join[ak*n+v]===ak?ins:out).push(v);
    }
    tgt.sort((a,b)=>wei[a]-wei[b]);if(tgt.length<11)continue;
    const act=[...base], ways=new Uint16Array(n);let count=0;
    function inc(z){if(!ways[z]++&&valid[z])count++;}
    function dec(z){if(!--ways[z]&&valid[z])count--;}
    for(let i=0;i<act.length;i++)for(let j=0;j<i;j++)inc(join[act[i]*n+act[j]]);
    function add(k){for(const a of act)inc(join[a*n+k]);act.push(k);}
    function undo(k){act.pop();for(const a of act)dec(join[a*n+k]);}
    function fit(ds,occ,pos,k){if(!k)return true;let cnt=0;for(let j=pos;j<ds.length;j++)if(!(ds[j]&occ))cnt++;if(cnt<k)return false;
      for(let j=pos;j<=ds.length-k;j++)if(!(occ&ds[j])&&fit(ds,occ|ds[j],j+1,k-1))return true;return false;}
    function test(){
      visits++;if(count<11)return false;
      const ds=[];let vol=sw;
      for(const v of tgt)if(ways[v]){
        const d=F^pool[v];if(act.some(a=>join[a*n+v]===a)||ds.some(z=>!(z&~d)))continue;
        ds.push(d);if(ds.length<=11){vol+=wei[v];if(vol>L)return false;}
      }
      return ds.length>=11&&fit(ds,def,0,11);
    }
    function outside(i,rem){if(test())return true;if(!rem)return false;
      for(let j=i;j<out.length;j++){const v=out[j];if(!ways[v])continue;add(v);const win=outside(j+1,rem-1);undo(v);if(win)return true;}return false;}
    function inside(i,rem){if(ways[ak]&&outside(0,rem))return true;if(!rem)return false;
      for(let j=i;j<ins.length;j++){const v=ins[j];if(!ways[v])continue;add(v);const win=inside(j+1,rem-1);undo(v);if(win)return true;}return false;}
    if(inside(0,budget))return {L,budget,visits,hit:1};
  }
  return {L,budget,visits,hit:0};
}

const fs=require('fs');
const path=process.argv[2],selected=process.argv[3]?Number(process.argv[3]):-1;
for(const line of fs.readFileSync(path,'utf8').trim().split('\n')) {
 const [id,c,cap,...t]=line.split(' ').map(Number);if(selected>=0&&selected!==id)continue;
 const act=Array(7).fill(0n);
 for(let s=0;s<128;s++){let pins=0;for(let j=6;j>=0;j--)if(j>=t.length||(t[j]&pins)){
  act[j]|=1n<<BigInt(s);pins|=1<<(2*j+(s>>j&1));}}
 const v=solveBase(act);console.log(id,v.L,v.budget,v.visits,v.hit);
}
