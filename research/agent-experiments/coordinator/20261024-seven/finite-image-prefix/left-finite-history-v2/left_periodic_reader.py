"""Correctly align the periodic reader with words containing left cells only.

The full folded reader consumes a center marker before any left cell.
Remove that dedicated root when projecting to the binary left-only word.
Check actual left-prefix meanings and both transducer reader endpoints.
"""
import numpy as np
from vacuum_patterns import vacua,reader
import left_zero_wall_graph as domain

def build():
 patterns=vacua();full,allstates,old_sink=reader(patterns)
 assert allstates[0] is None and allstates[1]==tuple((r,0) for r in range(5))
 assert np.min(full[1:,:2])>=1
 T=(full[1:,:2]-1).copy();states=allstates[1:];sink=old_sink-1
 def bit(r,j):
  p=patterns[r];a=p['left_bits'];mu=p['transient'];return a[j if j<len(a) else mu+(j-mu)%p['period']]
 def expected(word):
  out=[];n=len(word)
  for r in range(5):
   if all(bit(r,j)==x for j,x in enumerate(word)):
    p=patterns[r];pos=n if n<len(p['left_bits']) else p['transient']+(n-p['transient'])%p['period'];out.append((r,pos))
  return tuple(out)
 prefix_checks=0
 for r in range(5):
  for flip in [-1,1,7,53,151,300]:
   q=0;word=[]
   for j in range(400):
    x=bit(r,j)^int(j==flip);word.append(x);q=int(T[q,x]);assert states[q]==expected(word);prefix_checks+=1
 # These traces consume actual canonical left words, without a center token.
 graph=domain.graph(T);gstates,edges,terminals,live=graph;lookup={(u,x):v for u,v,p,x,out in edges};physical=0
 for r in range(5):
  before=[bit(r,j) for j in range(64)]
  while not before[-1]:before.pop()
  after=domain.updated(before);assert after is not None;u=p=q=0
  for x in before:u=lookup[u,x];p=int(T[p,x])
  assert u in terminals and gstates[u][2]==p and states[p]==expected(before)
  for x in after:q=int(T[q,x])
  assert terminals[u][1]==q and states[q]==expected(after)
  assert any(rr==r for rr,pos in states[p]);physical+=1
 control={'binary_left_reader_states':len(T),'dedicated_center_marker_root_removed':True,'direct_entire_left_prefix_language_checks':prefix_checks,'actual_canonical_left_transducer_endpoint_checks':physical,'all_passed':True,'Lean_verified':False}
 return T,states,sink,control
