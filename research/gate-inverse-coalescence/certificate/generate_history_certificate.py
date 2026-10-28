from pathlib import Path
import json

root = Path(__file__).resolve().parent
module = root/'Rule30GateInverseMergeResearch.lean'
base = root/'BASE-VERIFIED.lean'
if not base.exists():
    base.write_bytes(module.read_bytes())
text = base.read_text(encoding='utf-8')
ending = 'end Ruliology.CellularAutomata.Rule30GateInverseMergeResearch'
assert text.rstrip().endswith(ending)
text = text.rstrip()[:-len(ending)]
S = [8,9,16,18,33,36,66,72,132,144]
words = S[:]
for n in (9,10):
    words = [w|(b << (n-1)) for w in words for b in (0,1)
             if ((w >> (n-8))|(b << 7)) in S]
words = sorted(words)
assert len(words) == 12


def inverse(row, b):
    q = [0,b]
    for x in row:
        q.append(x ^ (q[-1] | q[-2]))
    return q


entries = []
for w in words:
    boundary = sum((1 if t % 2 else 1-((w >> (t//2)) & 1)) << t for t in range(20))
    cols = [0,boundary]
    for k in range(1,20):
        cols.append(((cols[-1] >> 1) ^ (cols[-1] | cols[-2])) & ((1 << (20-k))-1))
    row = [(cols[k] & 1) for k in range(1,21)]
    parents = [inverse(row,b) for b in (0,1)]
    children = [inverse(parents[c][1:21],b) for c in (0,1) for b in (0,1)]
    assert parents[0][7:9] == parents[1][7:9]
    assert all(q[20:22] == children[3][20:22] for q in children)
    data = [sum(bit << k for k,bit in enumerate(q)) for q in parents+children]
    entries.append((w,cols,data))

text += r'''

/-! ### All four two-step histories, using a checked finite triangular table -/

structure HistoryCertificate where
  gate : Nat
  columns : List Nat
  preimages : List Nat
  deriving DecidableEq

def historyCertificates : List HistoryCertificate :=
'''
text += '  ['+',\n   '.join('⟨'+str(w)+', '+str(cols)+', '+str(data)+'⟩' for w,cols,data in entries)+']\n'
text += r'''

def tab (c : HistoryCertificate) (k t : Nat) : Bool :=
  Nat.testBit (c.columns[k]!) t

def tabRow (c : HistoryCertificate) (k : Nat) : Bool := tab c k 0

def parent (c : HistoryCertificate) (b : Bool) (k : Nat) : Bool :=
  Nat.testBit (c.preimages[if b then 1 else 0]!) k

def child (c : HistoryCertificate) (b₀ b₁ : Bool) (k : Nat) : Bool :=
  Nat.testBit (c.preimages[2 + 2*(if b₀ then 1 else 0) + (if b₁ then 1 else 0)]!) k

def TriangleValid (c : HistoryCertificate) : Prop :=
  (∀ t : Fin 21, tab c 0 t = false) ∧
  (∀ t : Fin 20, tab c 1 t = oddPhase c.gate t) ∧
  (∀ k : Fin 19, ∀ t : Fin 21, k.val+t.val+2 ≤ 20 →
    tab c (k.val+2) t = xor (tab c (k.val+1) (t.val+1))
      (tab c (k.val+1) t || tab c k t))

def BackValid (y : Nat → Bool) (b : Bool) (q : Nat → Bool) (n : Nat) : Prop :=
  q 0 = false ∧ q 1 = b ∧ ∀ k : Fin n,
    q (k.val+2) = xor (y (k.val+1)) (q (k.val+1) || q k)

def HistoryValid (c : HistoryCertificate) : Prop :=
  TriangleValid c ∧
  (∀ b : Bool, BackValid (tabRow c) b (parent c b) 19) ∧
  (∀ b₀ b₁ : Bool, BackValid (parent c b₀) b₁ (child c b₀ b₁) 20) ∧
  (parent c false 7 = parent c true 7 ∧ parent c false 8 = parent c true 8) ∧
  (∀ b₀ b₁ : Bool, child c b₀ b₁ 20 = child c true true 20 ∧
    child c b₀ b₁ 21 = child c true true 21)

instance historyValidDecidable : DecidablePred HistoryValid := fun c => by
    unfold HistoryValid TriangleValid BackValid
    infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem history_certificates_valid : ∀ c ∈ historyCertificates, HistoryValid c := by
  decide +kernel

theorem triangle_sound (c : HistoryCertificate) (hc : TriangleValid c) :
    ∀ k t, k+t ≤ 20 → tab c k t = recon (oddPhase c.gate) k t := by
  obtain ⟨h0,h1,hs⟩ := hc
  have key : ∀ k,
      (∀ t, k+t ≤ 20 → tab c k t = recon (oddPhase c.gate) k t) ∧
      (∀ t, k+1+t ≤ 20 → tab c (k+1) t = recon (oddPhase c.gate) (k+1) t) := by
    intro k
    induction k with
    | zero =>
        constructor
        · intro t ht
          exact h0 ⟨t,by omega⟩
        · intro t ht
          exact h1 ⟨t,by omega⟩
    | succ k ih =>
        constructor
        · simpa only [Nat.add_assoc] using ih.2
        · intro t ht
          rw [hs ⟨k,by omega⟩ ⟨t,by omega⟩ (by change k+t+2 ≤ 20; omega)]
          rw [ih.2 (t+1) (by omega), ih.2 t (by omega), ih.1 t (by omega)]
          rfl
  intro k t ht
  exact (key k).1 t ht

theorem back_valid_sound (y : Nat → Bool) (b : Bool) (q : Nat → Bool) (n : Nat)
    (h : BackValid y b q n) : ∀ k, k ≤ n+1 → q k = back b y k := by
  obtain ⟨h0,h1,hs⟩ := h
  have key : ∀ j, j ≤ n → q j = back b y j ∧ q (j+1) = back b y (j+1) := by
    intro j
    induction j with
    | zero => intro hj; exact ⟨h0,h1⟩
    | succ j ih =>
        intro hj
        obtain ⟨ha,hb⟩ := ih (by omega)
        constructor
        · exact hb
        · change q (j+2) = xor (y (j+1)) (back b y (j+1) || back b y j)
          rw [hs ⟨j,by omega⟩, ha, hb]
  intro k hk
  by_cases hn : k ≤ n
  · exact (key k hn).1
  · have hx : k=n+1 := by omega
    rw [hx]
    exact (key n (by omega)).2

/-- Exactly the legal length-ten gate prefixes, read during twenty boundary ticks. -/
def LegalHistory20 (L : Nat → Bool) : Prop :=
  ∃ c, c ∈ historyCertificates ∧ ∀ t, t < 20 → zrow L t 1 = oddPhase c.gate t

theorem history_row_matches (L : Nat → Bool) (c : HistoryCertificate)
    (hc : TriangleValid c)
    (h : ∀ t, t < 20 → zrow L t 1 = oddPhase c.gate t) :
    ∀ k, 1 ≤ k → k ≤ 20 → L k = tabRow c k := by
  intro k hk hbound
  calc
    L k = recon (fun t => zrow L t 1) k 0 :=
      (zrow_zero_of_pos L hk).symm.trans (history_eq_recon L k 0)
    _ = recon (oddPhase c.gate) k 0 := by
      apply recon_local
      intro j hj
      simpa only [Nat.zero_add] using h j (by omega)
    _ = tabRow c k := (triangle_sound c hc k 0 (by omega)).symm

theorem back_tails_of_equal_targets (y z : Nat → Bool) (b d : Bool) (n : Nat)
    (hy : ∀ k, n ≤ k → y k = z k)
    (h0 : back b y n = back d z n)
    (h1 : back b y (n+1) = back d z (n+1)) :
    ∀ k, n ≤ k → back b y k = back d z k := by
  have key : ∀ j, back b y (n+j) = back d z (n+j) ∧
      back b y (n+j+1) = back d z (n+j+1) := by
    intro j
    induction j with
    | zero => simpa using And.intro h0 h1
    | succ j ih =>
        constructor
        · simpa only [Nat.add_assoc] using ih.2
        · change xor (y (n+j+1)) (back b y (n+j+1) || back b y (n+j)) =
            xor (z (n+j+1)) (back d z (n+j+1) || back d z (n+j))
          rw [hy (n+j+1) (by omega), ih.1, ih.2]
  intro k hk
  simpa only [Nat.add_sub_of_le hk] using (key (k-n)).1

theorem all_two_step_heads_agree (L : Nat → Bool) (h : LegalHistory20 L) :
    ∀ b₀ b₁ : Bool, ∀ k, 20 ≤ k →
      back b₁ (back b₀ L) k = back true (back true L) k := by
  obtain ⟨c,hc,hh⟩ := h
  obtain ⟨ht,hp,hq,hm,hcmerge⟩ := history_certificates_valid c hc
  have rowmatch := history_row_matches L c ht hh
  have pmatch (b : Bool) : ∀ k, k ≤ 20 → parent c b k = back b L k := by
    intro k hk
    calc
      parent c b k = back b (tabRow c) k := back_valid_sound _ _ _ 19 (hp b) k (by omega)
      _ = back b L k :=
        (back_congr_pair b (tabRow c) L k
          (fun i hi hn => (rowmatch i hi (by omega)).symm)).1
  have qmatch (b₀ b₁ : Bool) : ∀ k, k ≤ 21 →
      child c b₀ b₁ k = back b₁ (back b₀ L) k := by
    intro k hk
    calc
      child c b₀ b₁ k = back b₁ (parent c b₀) k :=
        back_valid_sound _ _ _ 20 (hq b₀ b₁) k (by omega)
      _ = back b₁ (back b₀ L) k := by
        cases k with
        | zero => rfl
        | succ k =>
            exact (back_congr_pair b₁ (parent c b₀) (back b₀ L) k
              (fun i hi hn => pmatch b₀ i (by omega))).2
  have ptail : ∀ b : Bool, ∀ k, 7 ≤ k → back b L k = back true L k := by
    intro b
    cases b with
    | true => intro k hk; rfl
    | false =>
        apply back_tail_of_pair L false true 7
        · exact (pmatch false 7 (by omega)).symm.trans
            (hm.1.trans (pmatch true 7 (by omega)))
        · exact (pmatch false 8 (by omega)).symm.trans
            (hm.2.trans (pmatch true 8 (by omega)))
  intro b₀ b₁
  apply back_tails_of_equal_targets (back b₀ L) (back true L) b₁ true 20
  · intro k hk
    exact ptail b₀ k (by omega)
  · exact (qmatch b₀ b₁ 20 (by omega)).symm.trans
      ((hcmerge b₀ b₁).1.trans (qmatch true true 20 (by omega)))
  · exact (qmatch b₀ b₁ 21 (by omega)).symm.trans
      ((hcmerge b₀ b₁).2.trans (qmatch true true 21 (by omega)))

theorem two_step_finiteness_independent (L : Nat → Bool) (h : LegalHistory20 L)
    (b₀ b₁ : Bool) : FinSupp (back b₁ (back b₀ L)) ↔ FinSupp (back true (back true L)) := by
  have he := all_two_step_heads_agree L h b₀ b₁
  constructor
  · rintro ⟨W,hW⟩
    refine ⟨max W 20, fun k hk => ?_⟩
    rw [← he k (by omega)]
    exact hW k (by omega)
  · rintro ⟨W,hW⟩
    refine ⟨max W 20, fun k hk => ?_⟩
    rw [he k (by omega)]
    exact hW k (by omega)

theorem any_two_step_preimage_iff_canonical (L : Nat → Bool) (h : LegalHistory20 L) :
    (∃ b₀ b₁ : Bool, FinSupp (back b₁ (back b₀ L))) ↔ FinSupp (back true (back true L)) := by
  constructor
  · rintro ⟨b₀,b₁,hb⟩
    exact (two_step_finiteness_independent L h b₀ b₁).1 hb
  · intro ht
    exact ⟨true,true,ht⟩

'''
extension = root/'HistoryFinalExtension.lean.txt'
if extension.exists():
    text += extension.read_text(encoding='utf-8')
wall_extension = root/'WallExtension.lean.txt'
if wall_extension.exists():
    text += wall_extension.read_text(encoding='utf-8')
text += ending+'\n'
module.write_text(text, encoding='utf-8', newline='\r\n')
(root/'HISTORY-CERTIFICATE-DATA.json').write_text(json.dumps(
    [{'gate10':w,'columns':cols,'preimages':data} for w,cols,data in entries], indent=2)+'\n', encoding='utf-8')
print(json.dumps({'entries': len(entries), 'source_bytes': len(text.encode('utf-8'))}))
