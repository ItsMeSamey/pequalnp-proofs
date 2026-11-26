// The observable domain is four ordinary binary axes times three states.
// The states are inactive, active-left, and active-right respectively.
function census(arity) {
  const full = (1n<<48n)-1n, B = [];
  function feature(test) {
    let m=0n;
    for(let a=0;a<16;a++)for(let b=0;b<3;b++)
      if(test(a,b))m|=1n<<BigInt(3*a+b);
    return m;
  }
  for(let j=0;j<4;j++){
    const m=feature(a=>(a>>j)&1);
    B.push(m,full^m);
  }
  const inactive=feature((a,b)=>b===0);
  B.push(inactive,full^inactive,feature((a,b)=>b===1),feature((a,b)=>b===2));
  let vals=new Set([0n]);for(const f of B)for(const v of [...vals])vals.add(f|v);
  function wt(v){let s=0;for(;v;v&=v-1n)s++;return s;}
  const pool=[...vals].sort((x,y)=>wt(x)-wt(y)||(x<y?-1:1)), n=pool.length;
  const id=new Map(pool.map((v,i)=>[v,i])), jn=new Uint16Array(n*n), w=pool.map(v=>wt(full^v));
  const dc=new Uint8Array(n*n);
  for(let i=0;i<n;i++)for(let j=0;j<n;j++){
    jn[i*n+j]=id.get(pool[i]|pool[j]);
    dc[i*n+j]=!((full^pool[i])&(full^pool[j]));
  }
  const ak=id.get(full^feature((a,b)=>!b&&!(a&((1<<arity)-1))));
  const base=B.map(v=>id.get(v)), active=[...base], ways=new Uint16Array(n);
  for(let i=0;i<base.length;i++)for(let j=0;j<i;j++)ways[jn[base[i]*n+base[j]]]++;
  const inside=[],outside=[];
  for(let k=0;k<n;k++)if(k!==ak&&pool[k]&&pool[k]!==full&&!base.includes(k)&&jn[k*n+ak]!==k)
    (jn[k*n+ak]===ak?inside:outside).push(k);
  const targets=Array.from({length:n},(_,i)=>i).filter(i=>w[i]&&w[i]<=38&&dc[i*n+ak]&&!base.includes(i)).sort((a,b)=>w[a]-w[b]);
  const lows=pool.map(v=>Number((full^v)&0xffffffffn)), highs=pool.map(v=>Number((full^v)>>32n));
  let hits=0,visits=0,dependencies=0;
  function add(k){for(const i of active)ways[jn[k*n+i]]++;active.push(k);}
  function pop(k){active.pop();for(const i of active)ways[jn[k*n+i]]--;}
  function fit(list,lo,hi,pos,k){
    if(!k)return true;
    let count=0;
    for(let j=pos;j<list.length;j++)if(!(lows[list[j]]&lo)&&!(highs[list[j]]&hi))count++;
    if(count<k)return false;
    for(let j=pos;j<=list.length-k;j++){
      const v=list[j];
      if(!(lows[v]&lo)&&!(highs[v]&hi)&&fit(list,lo|lows[v],hi|highs[v],j+1,k-1))return true;
    }
    return false;
  }
  function test(){
    visits++;
    const xs=[];let sum=w[ak];
    for(const z of targets)if(ways[z]){
      if(active.some(a=>jn[a*n+z]===a)||xs.some(x=>jn[x*n+z]===x))continue;
      xs.push(z);
      if(xs.length<=10){sum+=w[z];if(sum>48)return false;}
    }
    return xs.length>=10&&fit(xs,lows[ak],highs[ak],0,10);
  }
  function out(pos,rem){
    if(test()){hits++;return true;}
    if(!rem)return false;
    for(let j=pos;j<outside.length;j++){
      const k=outside[j];if(!ways[k])continue;
      add(k);const r=out(j+1,rem-1);pop(k);if(r)return true;
    }return false;
  }
  function ins(pos,rem){
    if(ways[ak]){dependencies++;if(out(0,rem))return true;}
    if(!rem)return false;
    for(let j=pos;j<inside.length;j++){
      const k=inside[j];if(!ways[k])continue;
      add(k);const r=ins(j+1,rem-1);pop(k);if(r)return true;
    }return false;
  }
  ins(0,5);return {arity,dependencies,visits,hits};
}
if (typeof module !== 'undefined' && require.main === module) {
  for (const k of [2,3,4]) console.log(JSON.stringify(census(k)));
}
