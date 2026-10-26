from pathlib import Path
import json
r=Path(__file__).resolve().parent
mods=json.loads((r/'certificate-check-modules.json').read_bytes())
s='module\n'
for m in ['Rule30CubicOrbitSemantics',*mods]:s+=f'public import {m}\n'
s+='''@[expose] public section
namespace Rule30CubicCertificateChecked
open Rule30CubicCertificateData
open Rule30ReaderCanonicalResearch
open Rule30CubicOrbitSemantics
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
'''
parts=[f'(orbits.drop {i} |>.take {min(32,290-i)})' for i in range(0,290,32)]
s+='def orbitGroups : List (List Orbit) := ['+',\n'.join(parts)+']\n'
s+='theorem orbitGroups_flatten : orbitGroups.flatten=orbits := by rfl\n'
s+='theorem all_orbits_checked : orbits.all checkOrbit=true := by\n'
s+='  rw [←orbitGroups_flatten,List.all_flatten]\n'
s+='  simp only [orbitGroups,List.all_cons,List.all_nil,'
s+=','.join(f'Rule30CubicOrbitCheck{i:02d}.checked' for i in range(10))
s+=',Bool.and_self]\n'
s+='theorem all_moments_checked : (List.range 64).all (fun a =>\n'
s+='    (List.range (64-a)).all (fun j => !(moment a (a+j))))=true := by\n'
s+='  have hr : List.range 64='+str(list(range(64)))+' := rfl\n  rw [hr]\n'
s+='  simp only [List.all_cons,List.all_nil,Nat.reduceSub,'
s+=','.join(f'Rule30CubicMomentCheck{a//4:02d}.row{a}' for a in range(64))
s+=',Bool.and_self]\n'
s+='''theorem target_checked : target=true := by decide +kernel
theorem shape_checked : orbits.all (fun o =>
    (o.period==32 || o.period==64) &&
    (o.r<2^o.period) && (o.g<2^o.period))=true := by decide +kernel
theorem phase_count : orbits.foldl (fun n o => n+o.period) 0=18528 := by decide +kernel
theorem every_record_is_canonical_cycle (o : Orbit) (ho : o∈orbits) :
    Canonical (word o.initial width++[false]) ∧
    iter (word o.initial width) o.period=word o.initial width := by
  exact checked_orbit_is_actual_cycle o (List.all_eq_true.mp all_orbits_checked o ho)
end Rule30CubicCertificateChecked
'''
(r/'Rule30CubicCertificateChecked.lean').write_text(s,encoding='utf-8')
p=r/'replay.py';t=p.read_text(encoding='utf-8')
for name,heads in [('Rule30CubicOrbitSemantics',['packed_iter','run_profile','checked_orbit_is_actual_cycle']),
                   ('Rule30CubicCertificateChecked',['all_orbits_checked','all_moments_checked','target_checked','phase_count','every_record_is_canonical_cycle'])]:
    line=f'HEADS[{name!r}]={heads!r}\n'
    if line not in t:t=t.replace('assert module in HEADS',line+'assert module in HEADS')
p.write_text(t,encoding='utf-8')
