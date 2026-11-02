module
public import RightOneLayer
@[expose] public section
namespace RightOneLayerPeriodTwo
open RightOneLayer

def center (t : Nat) : Bool := decide (t%2=0)
def left (f : Nat → Bool) (t : Nat) : Bool := if t%2=0 then true else f (t/2)
def No00 (f : Nat → Bool) : Prop := ∀ n,f n=false → f (n+1)=true

/-- The known no-00 necessary gate is EXACT for the first right column with a
free outer input. It is not exact for a full right half or a finite right start. -/
theorem compatible_iff_no00 (f : Nat → Bool) : Compatible center (left f) ↔ No00 f := by
  rw [compatible_iff]
  constructor
  · intro h n hn
    have hc0 : center (2*n+1)=false := by simp [center,Nat.add_mod]
    have hc1 : center (2*n+1+1)=true := by simp [center,Nat.add_mod]
    have hc2 : center (2*n+1+2)=false := by simp [center,Nat.add_mod]
    have hf : forced center (left f) (2*n+1)=true := by
      have hd0 : (2*n+1)/2=n := by omega
      simp [forced,left,center,Nat.add_mod,hd0,hn]
    have hh:=h.2.2 (2*n+1) hc0 hc1 hc2 hf
    have hd : (2*n+1+2)/2=n+1 := by omega
    simpa [forced,left,center,Nat.add_mod,hd] using hh
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro t ht
      have he : t%2=0 := by simpa [center] using ht
      have ho : (t+1)%2=1 := by omega
      simp [left,center,he,ho]
    · intro t h0 h1 hf
      have he0 : ¬t%2=0 := by simpa [center] using h0
      have he1 : ¬(t+1)%2=0 := by simpa [center] using h1
      omega
    · intro t h0 h1 h2 hf
      have he : t%2=1 := by
        have h0' : ¬t%2=0 := by simpa [center] using h0
        omega
      have he1 : (t+1)%2=0 := by omega
      have he2 : (t+2)%2=1 := by omega
      have he3 : (t+2+1)%2=0 := by omega
      have hf0 : f (t/2)=false := by simpa [forced,left,center,he,he1] using hf
      have hf1:=h (t/2) hf0
      have hd : (t+2)/2=t/2+1 := by omega
      simp [forced,left,center,he2,he3,hd,hf1]

#print axioms compatible_iff_no00
end RightOneLayerPeriodTwo
