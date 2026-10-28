from pathlib import Path
import json

root = Path(__file__).resolve().parent
entries = json.loads((root/'HISTORY-CERTIFICATE-DATA.json').read_text(encoding='utf-8'))
data = []
for item in entries:
    row = [(n&1) for n in item['columns']]
    model = []
    for p in range(8):
        q = row[:]
        model.append(sum(bit << k for k,bit in enumerate(q)))
        for j in range(6):
            head = 1 if j%2==0 else 1-((p >> (2-j//2))&1)
            new = [0,head]
            for bit in q[1:]:
                new.append(bit^(new[-1]|new[-2]))
            q = new
            model.append(sum(bit << k for k,bit in enumerate(q)))
    data.append((item['gate10'],model))

source = r'''module
public import Rule30GateInverseMergeResearch

/-! Three legal gate bits of temporal past can be edited without changing the far spatial tail.
The theorem is uniform in the entire future but fixes the edited past length to three. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30GatePastThreeResearch
open Rule30ZeroBoundary Rule30GateInverseMergeResearch

def head (p : Fin 8) (j : Nat) : Bool :=
  if j%2=0 then true else !(Nat.testBit p.val (2-j/2))

def history (p : Fin 8) (L : Nat → Bool) : Nat → Nat → Bool
  | 0 => L
  | j+1 => back (head p j) (history p L j)

def Allowed (w : Nat) (p : Fin 8) : Prop :=
  ∀ i : Fin 3, (((p.val ||| (w <<< 3)) >>> i.val) &&& 255) ∈ words

def modelData : Nat → List Nat
'''
source += ''.join('  | '+str(w)+' => '+str(model)+'\n' for w,model in data)
source += r'''  | _ => []

def model (c : HistoryCertificate) (p : Fin 8) (j k : Nat) : Bool :=
  Nat.testBit ((modelData c.gate)[7*p.val+j]!) k

def Valid (c : HistoryCertificate) : Prop :=
  (∀ p : Fin 8, ∀ k : Fin 21, 1 ≤ k.val → model c p 0 k = tabRow c k) ∧
  (∀ p : Fin 8, ∀ j : Fin 6,
    BackValid (model c p j) (head p j) (model c p (j.val+1)) 20) ∧
  (∀ p q : Fin 8, Allowed c.gate p → Allowed c.gate q → ∀ j : Fin 6,
    model c p (j.val+1) 20 = model c q (j.val+1) 20 ∧
    model c p (j.val+1) 21 = model c q (j.val+1) 21)

instance validDecidable : DecidablePred Valid := fun c => by
  unfold Valid Allowed BackValid
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem certificates_valid : ∀ c ∈ historyCertificates, Valid c := by
  decide +kernel

theorem model_sound (L : Nat → Bool) (c : HistoryCertificate)
    (hc : c ∈ historyCertificates)
    (hh : ∀ t, t < 20 → zrow L t 1 = oddPhase c.gate t) (p : Fin 8) :
    ∀ j, j ≤ 6 →
      (∀ k, 1 ≤ k → k ≤ 20 → model c p j k = history p L j k) ∧
      (0 < j → model c p j 21 = history p L j 21) := by
  obtain ⟨hbase,hback,hmerge⟩ := certificates_valid c hc
  have rowmatch := history_row_matches L c (history_certificates_valid c hc).1 hh
  intro j
  induction j with
  | zero =>
      intro hj
      constructor
      · intro k hk hn
        exact (hbase p ⟨k,by omega⟩ hk).trans (rowmatch k hk hn).symm
      · intro hp
        omega
  | succ j ih =>
      intro hj
      have hold := ih (by omega)
      have child : ∀ k, k ≤ 21 → model c p (j+1) k = history p L (j+1) k := by
        intro k hk
        calc
          model c p (j+1) k = back (head p j) (model c p j) k :=
            back_valid_sound _ _ _ 20 (hback p ⟨j,by omega⟩) k (by omega)
          _ = history p L (j+1) k := by
            change back (head p j) (model c p j) k = back (head p j) (history p L j) k
            cases k with
            | zero => rfl
            | succ k =>
                exact (back_congr_pair (head p j) (model c p j) (history p L j) k
                  (fun i hi hn => hold.1 i hi (by omega))).2
      exact ⟨fun k hk hn => child k (by omega),fun hp => child 21 (by omega)⟩

theorem joint_tail (L : Nat → Bool) (p q : Fin 8)
    (h0 : ∀ j, j ≤ 6 → history p L j 20 = history q L j 20)
    (h1 : ∀ j, j ≤ 6 → history p L j 21 = history q L j 21) :
    ∀ k, 20 ≤ k → ∀ j, j ≤ 6 → history p L j k = history q L j k := by
  have key : ∀ i, ∀ j, j ≤ 6 →
      history p L j (20+i) = history q L j (20+i) ∧
      history p L j (20+i+1) = history q L j (20+i+1) := by
    intro i
    induction i with
    | zero => intro j hj; exact ⟨h0 j hj,h1 j hj⟩
    | succ i ih =>
        intro j hj
        constructor
        · simpa only [Nat.add_assoc] using (ih j hj).2
        · cases j with
          | zero => rfl
          | succ j =>
              change xor (history p L j (20+i+1))
                (history p L (j+1) (20+i+1) || history p L (j+1) (20+i)) =
                xor (history q L j (20+i+1))
                (history q L (j+1) (20+i+1) || history q L (j+1) (20+i))
              rw [(ih j (by omega)).2,(ih (j+1) hj).1,(ih (j+1) hj).2]
  intro k hk j hj
  simpa only [Nat.add_sub_of_le hk] using (key (k-20) j hj).1

theorem three_legal_pasts_agree (L : Nat → Bool) (c : HistoryCertificate)
    (hc : c ∈ historyCertificates)
    (hh : ∀ t, t < 20 → zrow L t 1 = oddPhase c.gate t)
    (p q : Fin 8) (hp : Allowed c.gate p) (hq : Allowed c.gate q) :
    ∀ k, 20 ≤ k → history p L 6 k = history q L 6 k := by
  have hm := (certificates_valid c hc).2.2 p q hp hq
  have hs := model_sound L c hc hh
  have hpair : ∀ j, j ≤ 6 →
      history p L j 20 = history q L j 20 ∧ history p L j 21 = history q L j 21 := by
    intro j hj
    cases j with
    | zero => constructor <;> rfl
    | succ j =>
        have hcj := hm ⟨j,by omega⟩
        constructor
        · exact ((hs p (j+1) hj).1 20 (by omega) (by omega)).symm.trans
            (hcj.1.trans ((hs q (j+1) hj).1 20 (by omega) (by omega)))
        · exact ((hs p (j+1) hj).2 (by omega)).symm.trans
            (hcj.2.trans ((hs q (j+1) hj).2 (by omega)))
  intro k hk
  exact joint_tail L p q (fun j hj => (hpair j hj).1)
    (fun j hj => (hpair j hj).2) k hk 6 (by omega)

theorem legal_gate_prefix_edits_agree (L : Nat → Bool) (w : Fin 1024)
    (hw : ∀ i : Fin 3, ((w.val >>> i.val) &&& 255) ∈ words)
    (hh : ∀ t, t < 20 → zrow L t 1 = oddPhase w.val t)
    (p q : Fin 8) (hp : Allowed w.val p) (hq : Allowed w.val q) :
    ∀ k, 20 ≤ k → history p L 6 k = history q L 6 k := by
  obtain ⟨c,hc,hcw⟩ := List.mem_map.mp ((gate_prefix_coverage w).1 hw)
  apply three_legal_pasts_agree L c hc
  · simpa only [hcw] using hh
  · simpa only [hcw] using hp
  · simpa only [hcw] using hq

theorem legal_gate_prefix_edits_finite_iff (L : Nat → Bool) (w : Fin 1024)
    (hw : ∀ i : Fin 3, ((w.val >>> i.val) &&& 255) ∈ words)
    (hh : ∀ t, t < 20 → zrow L t 1 = oddPhase w.val t)
    (p q : Fin 8) (hp : Allowed w.val p) (hq : Allowed w.val q) :
    FinSupp (history p L 6) ↔ FinSupp (history q L 6) := by
  have he := legal_gate_prefix_edits_agree L w hw hh p q hp hq
  constructor
  · rintro ⟨W,hW⟩
    refine ⟨max W 20,fun k hk => ?_⟩
    rw [← he k (by omega)]
    exact hW k (by omega)
  · rintro ⟨W,hW⟩
    refine ⟨max W 20,fun k hk => ?_⟩
    rw [he k (by omega)]
    exact hW k (by omega)

end Ruliology.CellularAutomata.Rule30GatePastThreeResearch
'''
extension = root/'PastTraceExtension.lean.txt'
if extension.exists():
    ending = 'end Ruliology.CellularAutomata.Rule30GatePastThreeResearch'
    assert source.rstrip().endswith(ending)
    source = source.rstrip()[:-len(ending)]+extension.read_text(encoding='utf-8')+ending+'\n'
(root/'Rule30GatePastThreeResearch.lean').write_text(source,encoding='utf-8',newline='\r\n')
print(json.dumps({'certificate_entries':len(data),'source_bytes':len(source.encode('utf-8'))}))
