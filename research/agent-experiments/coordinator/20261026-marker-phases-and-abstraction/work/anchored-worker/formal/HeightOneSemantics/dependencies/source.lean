import HeightOneLogic
import RootShortExtensionCore
import CedarWhiteTransport
import CedarNo11011

/-! Literal finite-white trace transport, leaf complementation, and the
return8-only classification of actual equal parent profiles. -/
namespace HeightOneSemantics
open CedarSafetySoundness CedarSafety RootShortExtensionCore
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

abbrev Trace := Nat → Bool
def histories (p r : Trace) : List Bool → Trace × Trace
  | [] => (p,r)
  | v::vs => histories (history p r v) p vs
def z : Trace := lift8 zero
def tr (xs : List Bool) : Trace := (histories z z xs).1
def old (xs : List Bool) : Trace := (histories z z xs).2

theorem histories_append (xs ys : List Bool) (p r : Trace) :
    histories p r (xs++ys)=histories (histories p r xs).1 (histories p r xs).2 ys := by
  induction xs generalizing p r with
  | nil => rfl
  | cons v vs ih => exact ih (history p r v) p

theorem tr_snoc (xs : List Bool) (v : Bool) :
    tr (xs++[v])=history (tr xs) (old xs) v := by
  unfold tr old
  rw [histories_append]
  rfl

theorem old_snoc (xs : List Bool) (v : Bool) : old (xs++[v])=tr xs := by
  unfold tr old
  rw [histories_append]
  rfl

theorem driven_append (xs ys : List Bool) (p r : Trace) (t : Nat) :
    driven p r t (xs++ys)=driven p r t xs ++
      driven (histories p r xs).1 (histories p r xs).2 t ys := by
  induction xs generalizing p r with
  | nil =>
      have hn : ∀ t, driven p r t []=[] := by
        intro t;induction t with
        | zero => rfl
        | succ t ih => rw [driven,ih];rfl
      rw [hn]
      rfl
  | cons v vs ih =>
      simp only [List.cons_append,driven_cons,histories]
      rw [ih]

theorem trace_driven (xs : List Bool) (p r : Trace) (t : Nat) :
    (driven p r t xs).getLastD (p t)=(histories p r xs).1 t := by
  induction xs generalizing p r with
  | nil =>
      have hn : ∀ t, driven p r t []=[] := by
        intro t;induction t with
        | zero => rfl
        | succ t ih => rw [driven,ih];rfl
      rw [hn];rfl
  | cons v vs ih =>
      rw [driven_cons,List.getLastD_cons]
      exact ih (history p r v) p

theorem trace_eq (xs : List Bool) (t : Nat) : tr xs t=newest (evolution t xs) := by
  have h := trace_driven xs z z t
  rw [show z t=false from lift8_zero t] at h
  change (driven (lift8 zero) (lift8 zero) t xs).getLastD false=tr xs t at h
  rw [driven_white] at h
  exact h.symm

theorem driven_singleton (p r : Trace) (v : Bool) (t : Nat) :
    driven p r t [v]=[history p r v t] := by
  induction t with
  | zero => rfl
  | succ t ih => rw [driven,ih];rfl

theorem evolution_snoc (xs : List Bool) (v : Bool) (t : Nat) :
    evolution t (xs++[v])=evolution t xs++[tr (xs++[v]) t] := by
  rw [← driven_white,driven_append,driven_white,driven_singleton,tr_snoc]
  rfl

theorem trace_restart (xs : List Bool) (t s : Nat) :
    tr (evolution t xs) s=tr xs (t+s) := by
  rw [trace_eq,trace_eq,← evolution_add,Nat.add_comm s t]

theorem xor_not : ∀ x y : Bool, xor (!x) y=!(xor x y) := by decide +kernel

theorem history_not (p r : Trace) (v : Bool) (t : Nat) :
    history p r (!v) t=!(history p r v t) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [history,history,ih,xor_not]

theorem leaf_flip_trace (xs : List Bool) (v : Bool) (t : Nat) :
    tr (xs++[!v]) t=!(tr (xs++[v]) t) := by
  rw [tr_snoc,tr_snoc,history_not]

theorem snoc_eq (xs ys : List Bool) (a b : Bool) :
    xs++[a]=ys++[b] ↔ xs=ys ∧ a=b := by
  constructor
  · intro h
    have h' : a=b ∧ xs=ys := by simpa using congrArg List.reverse h
    exact ⟨h'.2,h'.1⟩
  · rintro ⟨rfl,rfl⟩;rfl

theorem leaf_flip_return (xs : List Bool) (v : Bool) (t : Nat) :
    evolution t (xs++[!v])=xs++[!v] ↔ evolution t (xs++[v])=xs++[v] := by
  rw [evolution_snoc,evolution_snoc,snoc_eq,snoc_eq,leaf_flip_trace]
  simp

theorem trace_step (xs : List Bool) (v : Bool) (t : Nat) :
    xor (tr (xs++[v]) t) (tr (xs++[v]) (t+1))=(tr xs t || old xs t) := by
  rw [tr_snoc,history]
  cases history (tr xs) (old xs) v t <;> cases (tr xs t || old xs t) <;> rfl

def profilePair (p r : Profile) : List Bool → Profile × Profile
  | [] => (p,r)
  | v::vs => profilePair (nextProfile p r v) p vs

theorem profile_fst (xs : List Bool) (p r : Profile) :
    (profilePair p r xs).1=profileTrace p r xs := by
  induction xs generalizing p r with
  | nil => rfl
  | cons v vs ih => exact ih (nextProfile p r v) p

theorem profile_append (xs ys : List Bool) (p r : Profile) :
    profilePair p r (xs++ys)=profilePair (profilePair p r xs).1 (profilePair p r xs).2 ys := by
  induction xs generalizing p r with
  | nil => rfl
  | cons v vs ih => exact ih (nextProfile p r v) p

theorem profile_snoc_older (xs : List Bool) (v : Bool) :
    (profilePair zero zero (xs++[v])).2=profileTrace zero zero xs := by
  rw [profile_append]
  exact profile_fst xs zero zero

theorem return8_coverage (xs : List Bool) : ∀ i : Fin 36,
    run8 (CedarSafetyBridge.state i).previous (CedarSafetyBridge.state i).older xs=xs →
    ∃ j : Fin 36,
      (profilePair (CedarSafetyBridge.state i).previous (CedarSafetyBridge.state i).older xs).1=
        (CedarSafetyBridge.state j).previous ∧
      (profilePair (CedarSafetyBridge.state i).previous (CedarSafetyBridge.state i).older xs).2=
        (CedarSafetyBridge.state j).older := by
  induction xs with
  | nil => intro i h;exact ⟨i,rfl,rfl⟩
  | cons v vs ih =>
      intro i h
      rw [run8_cons,List.cons.injEq] at h
      have cert := CedarSafetyBridge.transition_certificate i v
      simp only [h.1,ite_true] at cert
      obtain ⟨j,hq,hp,hr⟩ := cert
      have hret : run8 (CedarSafetyBridge.state j).previous (CedarSafetyBridge.state j).older vs=vs := by
        rw [hp,hr];exact h.2
      obtain ⟨k,hk0,hk1⟩ := ih j hret
      rw [hp,hr] at hk0 hk1
      exact ⟨k,hk0,hk1⟩

theorem profile_ext (p q : Profile)
    (h : ∀ t : Fin 9, profileAt p t.val=profileAt q t.val) : p=q := by
  have h0 := h ⟨0,by decide⟩;have h1 := h ⟨1,by decide⟩
  have h2 := h ⟨2,by decide⟩;have h3 := h ⟨3,by decide⟩
  have h4 := h ⟨4,by decide⟩;have h5 := h ⟨5,by decide⟩
  have h6 := h ⟨6,by decide⟩;have h7 := h ⟨7,by decide⟩
  have h8 := h ⟨8,by decide⟩
  cases p;cases q;simp_all [profileAt]

theorem twin_return_certificate : ∀ i : Fin 36,
    (CedarSafetyBridge.state i).previous=(CedarSafetyBridge.state i).older →
    (CedarSafetyBridge.state i).previous.t2=(CedarSafetyBridge.state i).previous.t0 := by
  decide +kernel

theorem return8_twins_at_zero (xs : List Bool) (v : Bool)
    (hr : evolution 8 (xs++[v])=xs++[v])
    (ht : ∀ t, tr (xs++[v]) t=tr xs t) : tr (xs++[v]) 2=tr (xs++[v]) 0 := by
  have hz : CedarSafetyBridge.state (0 : Fin 36)=⟨0,zero,zero⟩ := by decide +kernel
  have hc := return8_coverage (xs++[v]) (0 : Fin 36)
  rw [hz] at hc
  obtain ⟨i,hp,ho⟩ := hc hr
  change (profilePair zero zero (xs++[v])).1=(CedarSafetyBridge.state i).previous at hp
  change (profilePair zero zero (xs++[v])).2=(CedarSafetyBridge.state i).older at ho
  rw [profile_fst] at hp
  rw [profile_snoc_older] at ho
  have heq : (CedarSafetyBridge.state i).previous=(CedarSafetyBridge.state i).older := by
    rw [← hp,← ho]
    apply profile_ext
    intro t
    rw [trace_white _ t.val (by omega),trace_white _ t.val (by omega),← trace_eq,← trace_eq]
    exact ht t.val
  have hc := twin_return_certificate i heq
  have h2 := trace_white (xs++[v]) 2 (by decide)
  have h0 := trace_white (xs++[v]) 0 (by decide)
  rw [hp] at h2 h0
  change (CedarSafetyBridge.state i).previous.t2=newest (evolution 2 (xs++[v])) at h2
  change (CedarSafetyBridge.state i).previous.t0=newest (evolution 0 (xs++[v])) at h0
  rw [trace_eq,trace_eq,← h2,← h0]
  exact hc

theorem return8_twins_two (xs : List Bool) (v : Bool)
    (hr : evolution 8 (xs++[v])=xs++[v])
    (ht : ∀ t, tr (xs++[v]) t=tr xs t) :
    ∀ t, tr (xs++[v]) (t+2)=tr (xs++[v]) t := by
  intro t
  let w := tr (xs++[v]) t
  have hs : evolution t (xs++[v])=evolution t xs++[w] := evolution_snoc xs v t
  have hr' : evolution 8 (evolution t xs++[w])=evolution t xs++[w] := by
    rw [← hs,← evolution_add,Nat.add_comm 8 t,evolution_add,hr]
  have ht' : ∀ s, tr (evolution t xs++[w]) s=tr (evolution t xs) s := by
    intro s
    rw [← hs,trace_restart,trace_restart]
    exact ht (t+s)
  have h := return8_twins_at_zero (evolution t xs) w hr' ht'
  rw [← hs,trace_restart,trace_restart,Nat.add_zero] at h
  exact h

end HeightOneSemantics
