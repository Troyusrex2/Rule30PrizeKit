import RootShortExtensionCertificate

/-! Exact conditional short-extension theorem. Safe means all-time safety,
and the prefix's whole-word eight-step return remains an explicit premise.
This does not prove the open unbounded safety-completeness conjecture. -/
namespace RootShortExtension
open CedarSafetySoundness CedarSafety CedarSafetyBridge
open RootShortExtensionCore RootShortExtensionCertificate
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem extension_aux (u : List Bool) : ∀ (q : Nat) (p r : Profile) (v : List Bool),
    Good q p r → accepted (read q u)=true → v.length≤3 →
    DrivenSafe (lift8 p) (lift8 r) (u++v) →
    driven (lift8 p) (lift8 r) 8 (u++v)=u++v := by
  induction u with
  | nil =>
    intro q p r v hg ha hv hs
    obtain ⟨i,hq,hp,hr⟩ := hg
    subst q p r
    obtain ⟨k,hk⟩ := shortWord_complete v hv
    subst v
    rcases extension_certificate i k ha with hret | ⟨t,hbad⟩
    · exact hret
    · exact False.elim (hs t hbad)
  | cons a us ih =>
    intro q p r v hg ha hv hs
    have htail : accepted (read (transition q a) us)=true := ha
    have hlive : transition q a≠11 := by
      intro he
      rw [he,sink_read] at htail
      contradiction
    obtain ⟨hreturn,hnext⟩ := good_step hg a hlive
    have hs' := safe_cons (lift8 p) (lift8 r) a (us++v) hs
    rw [history_lift8 p r a hreturn] at hs'
    have hr := ih (transition q a) (nextProfile p r a) p v hnext htail hv hs'
    change driven (lift8 p) (lift8 r) 8 (a::(us++v))=a::(us++v)
    rw [driven_cons,history_lift8 p r a hreturn,hr]
    rfl

theorem accepted_short_extension (u v : List Bool)
    (hu : accepted (read 0 u)=true) (hv : v.length≤3) (hs : Safe (u++v)) :
    evolution 8 (u++v)=u++v := by
  have hg : Good 0 zero zero := ⟨⟨0,by decide⟩,rfl,rfl,rfl⟩
  have he := extension_aux u 0 zero zero v hg hu hv (white_safe (u++v) hs)
  rwa [driven_white] at he

/-- Every safe append of at most three cells to a safe returning prefix
returns as a whole word after eight genuine white-boundary updates. -/
theorem safe_short_extension (u v : List Bool) (hu : Safe u)
    (hr : evolution 8 u=u) (hv : v.length≤3) (hs : Safe (u++v)) :
    evolution 8 (u++v)=u++v :=
  accepted_short_extension u v ((safe_return_iff_accepted u).mp ⟨hu,hr⟩) hv hs

theorem accepted_short_extension_language (u v : List Bool)
    (hu : accepted (read 0 u)=true) (hv : v.length≤3) (hs : Safe (u++v)) :
    accepted (read 0 (u++v))=true :=
  (safe_return_iff_accepted (u++v)).mp ⟨hs,accepted_short_extension u v hu hv hs⟩

end RootShortExtension
