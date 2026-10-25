"""Generate a finite counterexample linked to official Theta by lane semantics."""
import hashlib,json
from pathlib import Path
from core import HERE
from zero_tail_rank import step

def main():
 raw=json.loads((HERE/'zero-run-charge-beam.json').read_text())['counterexample']
 n=raw['length'];w=int(raw['free_prefix_hex'],16);assert n==28
 f=[(w>>i)&1 for i in range(n)];assert sum(int(not x and (j==0 or f[j-1])) for j,x in enumerate(f))==12
 R=[];Rm=[];diags=[[]];cells=[0]
 for t in range(2*n):
  y=1 if not t%2 else f[t//2]
  R,Rm=step(R,Rm,y);diags.append(R);cells.append(R[-1])
 assert sum(cells)==11
 def nums(xs):return '['+','.join(map(str,xs))+']'
 source='''import Rule30ZeroRunSpatialChargeReductionResearch
import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes

/-! The unrestricted zero-run spatial charge is false. The explicit stream
has adjacent zeros; this does not refute the no00 or actual-coupling target.
Every computed anti-diagonal is linked to the official reconstruction using
the kit's generic level theorem, then checked by the unchanged full replay.
The wall is depth 0, so blackCount (Theta s) (2*n+1) counts depths 1..2*n.
-/
namespace Rule30ZeroRunChargeCounterexampleResearch
open Ruliology.CellularAutomata
open Rule30ZeroBoundary (Theta alt recon)
open Rule30ZeroBoundaryLanes (AD scanN level)
open Rule30TotalSpatialChargeReductionResearch (blackCount)
open Rule30ZeroRunSpatialChargeReductionResearch (zeroRuns ZeroRunSpatialCharge)

set_option maxRecDepth 20000
set_option maxHeartbeats 0

def witness (j : Nat) : Bool := if j<28 then (89822358 : Nat).testBit j else true

def diag0 : List Nat := []
theorem sem0 : diag0.map (fun a => a.testBit 0)=AD (alt witness) 0 0 0 := by rfl
theorem cell0 : Theta witness 0=false := by rfl

'''
 assert int('55a9496',16)==89822358
 for i in range(1,2*n+1):
  y=1 if (i-1)%2==0 else f[(i-1)//2];b='true' if cells[i] else 'false'
  source+=f'def diag{i} : List Nat := '+nums(diags[i])+'\n'
  source+=f'''theorem level{i} :
    diag{i}.map (fun a => a.testBit 0)=AD (alt witness) {i} 0 {i} /\\
    Theta witness {i}={b} := by
  have h := level (alt witness) 0 {i-1} diag{i-1} diag{max(i-2,0)} {y}
    {'sem0' if i==1 else f'level{i-1}.1'} {'sem0' if i<=2 else f'level{i-2}.1'} (by decide +kernel)
  have hc : ({y} :: (scanN {y} diag{i-1} (0 :: diag{max(i-2,0)})).1)=diag{i} := by decide +kernel
  have hl : (scanN {y} diag{i-1} (0 :: diag{max(i-2,0)})).2.testBit 0={b} := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

'''
 source+='''theorem zero_run_count : zeroRuns witness 28=12 := by decide +kernel

theorem spatial_black_count : blackCount (Theta witness) 57=11 := by
  simp only [blackCount,cell0,'''+','.join(f'level{i}.2' for i in range(1,2*n+1))+''']
  decide +kernel

theorem unrestricted_charge_false : Not ZeroRunSpatialCharge := by
  intro hc
  have h := hc witness 28
  rw [zero_run_count,spatial_black_count] at h
  omega

theorem witness_has_adjacent_zeros : witness 5=false /\\ witness 6=false := by decide +kernel

end Rule30ZeroRunChargeCounterexampleResearch
'''
 target=HERE/'Rule30ZeroRunChargeCounterexampleResearch.lean';target.write_text(source,encoding='utf-8',newline='\n')
 (HERE/'zero-run-charge-counterexample-provenance.json').write_text(json.dumps({'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'free_prefix_hex':hex(w),'n':n,'zero_runs':12,'blackCount_Theta_57':11,'wall_depth_zero_excluded_from_count':True,'domain':'arbitrary free word; adjacent zeros present','full_problem_solved':False},indent=2)+'\n',encoding='utf-8')
 print({'generated':target.name,'antidiagonals':2*n,'counts':[12,11]},flush=True)
if __name__=='__main__':main()
