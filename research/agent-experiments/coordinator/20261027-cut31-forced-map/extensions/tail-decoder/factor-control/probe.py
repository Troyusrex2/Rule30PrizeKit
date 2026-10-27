from pathlib import Path
import hashlib,json,time
root=Path(__file__).resolve().parent
start=time.monotonic()
RULE=(0,1,1,1,1,0,0,0)
def rule(left,center,right):return RULE[4*left+2*center+right]
def step(b,n):return ((n<<1)|b) ^ (n | (n>>1))
states=[1]
for q in range(186):states.append(step(1,step(0,states[-1])))
row=[];right_stencils=0;odd_rows=0
for t in range(373):
 nxt=[]
 for i in range(len(row)+1):
  left=int(t%2==0) if i==0 else row[i-1]
  center=row[i] if i<len(row) else 0
  right=row[i+1] if i+1<len(row) else 0
  v=rule(left,center,right)
  assert v==(left^(center|right))
  nxt.append(v);right_stencils+=1
 row=nxt
 if (t+1)%2:
  q=t//2;packed=sum(v<<i for i,v in enumerate(row))
  assert packed==states[q],q
  odd_rows+=1
actual=[states[155+r]&1 for r in range(32)]
histories=[('pure_period5',[int(r%5==0) for r in range(32)]),('actual_empty',actual)]
outputs=[];cones={}
for name,g in histories:
 a=[1-g[t//2] if t%2==0 else 1 for t in range(64)]
 x=[[0]*65,a];checked=0
 for k in range(2,35):
  col=[]
  for t in range(len(x[-1])-1):
   solutions=[v for v in (0,1) if rule(v,x[k-1][t],x[k-2][t])==x[k-1][t+1]]
   assert len(solutions)==1
   v=solutions[0]
   assert v==(x[k-1][t+1]^(x[k-1][t]|x[k-2][t]))
   col.append(v);checked+=1
  x.append(col)
 def b(j,t):return x[j+31][t]
 def ell(j,t):return x[j+30][t]&(1-x[j+31][t])
 def marker(j,r):return ell(j,2*r)&ell(j,2*r+2)
 details=[];y={}
 for j in range(4):
  for t in range(3):
   r=t//2
   if t%2==0:
    offsets=[0,4,6,7,11];bt=2*r+12;product=None
   else:
    offsets=[2,3,6,7,10,12];bt=2*r+13;product=[r+3,r+11]
   ms=[{'r':r+i,'L0':ell(j,2*(r+i)),'L1':ell(j,2*(r+i)+2),'value':marker(j,r+i)} for i in offsets]
   value=b(j,bt)
   for m in ms:value^=m['value']
   product_value=0 if product is None else marker(j,product[0])&marker(j,product[1])
   value^=product_value;y[j,t]=value
   details.append({'j':j,'t':t,'B_time':bt,'B':b(j,bt),'markers':ms,'product_indices':product,'product':product_value,'Y':value})
 boundary=[{'t':t,'Y1':y[1,t],'a_shift14':a[t+14],'pass':y[1,t]==a[t+14]} for t in range(3)]
 stencils=[]
 for k in (1,2):
  for t in (0,1):
   left,center,right=y[k+1,t],y[k,t],y[k-1,t]
   wallright=0 if k==1 else right
   stencils.append({'k':k,'t':t,'next':y[k,t+1],'outer_left':left,'center':center,'inner_right':right,
    'full_rule':rule(left,center,right),'full_pass':y[k,t+1]==rule(left,center,right),
    'zero_wall_rule':rule(left,center,wallright),'zero_wall_pass':y[k,t+1]==rule(left,center,wallright)})
 seam=[{'t':t,'Y0':y[0,t],'Y1':y[1,t],'mask':y[0,t]&(1-y[1,t])} for t in (0,1)]
 outputs.append({'history':name,'gate':g,'gate_packed':sum(v<<i for i,v in enumerate(g)),'boundary_control':boundary,
  'Y_rows_by_time':[[y[j,t] for j in range(4)] for t in range(3)],'stencils':stencils,'wall_seam':seam,'details':details,
  'inverse_stencils_checked':checked,'boundary_pass':all(z['pass'] for z in boundary),
  'full_stencils_pass':all(z['full_pass'] for z in stencils),'zero_wall_stencils_pass':all(z['zero_wall_pass'] for z in stencils)})
 cones[name]=x
(root/'CONES.json').write_text(json.dumps(cones,separators=(',',':'))+'\n',encoding='utf-8')
result={'status':'FIXED_EXPERIMENT_COMPLETE','scope':'Two prescribed histories,4 stencils each; no expansion or parameter search.',
 'protocol_sha256':hashlib.sha256((root/'PROTOCOL.md').read_bytes()).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'right_scalar_control':{'max_physical_time':373,'max_white_index':186,'full_odd_rows_matched':odd_rows,'scalar_stencils_checked':right_stencils,
 'white_window_hex':[hex(n) for n in states[155:187]]},'histories':outputs,'elapsed_seconds':time.monotonic()-start}
(root/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'status':result['status'],'right_scalar_stencils':right_stencils,'histories':[{k:h[k] for k in ['history','boundary_pass','full_stencils_pass','zero_wall_stencils_pass','Y_rows_by_time']} for h in outputs],'elapsed_seconds':result['elapsed_seconds']}))
