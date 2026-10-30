module
public import CanonicalDecoration
/-! Exact dual certificate for swarm's width-4 TOP local-ranking search.
The numerical solver proposes 28 transitions; every use of the actual edge
map and the universal integer-weight contradiction is checked by Lean. -/
@[expose] public section
namespace WindowBarrier
open Ruliology.CellularAutomata.Rule30FrozenRuler
open CanonicalDecoration

def code (n : Nat) : Code := n.testBit
def cell (x y : Code) (j : Nat) : Nat :=
  (if x j then 2 else 0)+(if y j then 1 else 0)
def window (x y : Code) (j : Nat) : Nat :=
  64*cell x y (j+3)+16*cell x y (j+2)+4*cell x y (j+1)+cell x y j
def potential (w : Nat → Nat → Int) (x y : Code) : Int :=
  w 0 (window x y 5)+w 1 (window x y 4)+w 2 (window x y 3)+
  w 3 (window x y 2)+w 4 (window x y 1)+w 5 (window x y 0)
def Good (x y : Code) : Prop :=
  x 0=true ∧ y 0=true ∧
  x 1=x 2 ∧ y 1=y 2 ∧
  ((List.range 7).any (fun j => x j != y j))=true ∧
  x 7=y 7 ∧ x 8=y 8 ∧ T x 7=T y 7 ∧ T x 8=T y 8

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
/-- No position-dependent sum of four-digit joint-window weights strictly
decreases on every non-leaking K=6 transition. This excludes exactly this
grammar even after restricting both codes to the parentless class. It does
not exclude arbitrary potentials or added nonlocal features. -/
theorem no_ranking (w : Nat → Nat → Int) :
    ¬ ∀ x y,Good x y → potential w (T x) (T y)<potential w x y := by
  intro decrease
  have h0:=decrease (code 15) (code 9) (by unfold Good;decide)
  change w 0 3+w 1 15+w 2 61+w 3 245+w 4 213+w 5 87<w 0 0+w 1 0+w 2 3+w 3 14+w 4 58+w 5 235 at h0
  have h1:=decrease (code 57) (code 55) (by unfold Good;decide)
  change w 0 60+w 1 240+w 2 195+w 3 14+w 4 58+w 5 235<w 0 3+w 1 15+w 2 62+w 3 249+w 4 229+w 5 151 at h1
  have h2:=decrease (code 73) (code 79) (by unfold Good;decide)
  change w 0 255+w 1 255+w 2 254+w 3 250+w 4 234+w 5 171<w 0 12+w 1 48+w 2 195+w 3 13+w 4 53+w 5 215 at h2
  have h3:=decrease (code 81) (code 103) (by unfold Good;decide)
  change w 0 243+w 1 207+w 2 61+w 3 246+w 4 218+w 5 107<w 0 13+w 1 54+w 2 216+w 3 97+w 4 133+w 5 23 at h3
  have h4:=decrease (code 89) (code 95) (by unfold Good;decide)
  change w 0 243+w 1 204+w 2 50+w 3 202+w 4 42+w 5 171<w 0 12+w 1 51+w 2 207+w 3 61+w 4 245+w 5 215 at h4
  have h5:=decrease (code 119) (code 121) (by unfold Good;decide)
  change w 0 240+w 1 192+w 2 3+w 3 13+w 4 53+w 5 215<w 0 15+w 1 63+w 2 253+w 3 246+w 4 218+w 5 107 at h5
  have h6:=decrease (code 143) (code 137) (by unfold Good;decide)
  change w 0 243+w 1 207+w 2 61+w 3 245+w 4 213+w 5 87<w 0 48+w 1 192+w 2 3+w 3 14+w 4 58+w 5 235 at h6
  have h7:=decrease (code 161) (code 175) (by unfold Good;decide)
  change w 0 206+w 1 57+w 2 228+w 3 146+w 4 74+w 5 43<w 0 51+w 1 204+w 2 49+w 3 197+w 4 21+w 5 87 at h7
  have h8:=decrease (code 169) (code 199) (by unfold Good;decide)
  change w 0 204+w 1 51+w 2 207+w 3 62+w 4 250+w 5 235<w 0 54+w 1 216+w 2 98+w 3 137+w 4 37+w 5 151 at h8
  have h9:=decrease (code 177) (code 191) (by unfold Good;decide)
  change w 0 204+w 1 50+w 2 200+w 3 34+w 4 138+w 5 43<w 0 51+w 1 207+w 2 61+w 3 245+w 4 213+w 5 87 at h9
  have h10:=decrease (code 185) (code 183) (by unfold Good;decide)
  change w 0 204+w 1 48+w 2 195+w 3 14+w 4 58+w 5 235<w 0 51+w 1 207+w 2 62+w 3 249+w 4 229+w 5 151 at h10
  have h11:=decrease (code 191) (code 177) (by unfold Good;decide)
  change w 0 204+w 1 49+w 2 196+w 3 17+w 4 69+w 5 23<w 0 51+w 1 207+w 2 62+w 3 250+w 4 234+w 5 171 at h11
  have h12:=decrease (code 199) (code 169) (by unfold Good;decide)
  change w 0 204+w 1 51+w 2 207+w 3 61+w 4 245+w 5 215<w 0 57+w 1 228+w 2 145+w 3 70+w 4 26+w 5 107 at h12
  have h13:=decrease (code 201) (code 207) (by unfold Good;decide)
  change w 0 207+w 1 63+w 2 254+w 3 250+w 4 234+w 5 171<w 0 60+w 1 240+w 2 195+w 3 13+w 4 53+w 5 215 at h13
  have h14:=decrease (code 247) (code 249) (by unfold Good;decide)
  change w 0 192+w 1 0+w 2 3+w 3 13+w 4 53+w 5 215<w 0 63+w 1 255+w 2 253+w 3 246+w 4 218+w 5 107 at h14
  have h15:=decrease (code 265) (code 271) (by unfold Good;decide)
  change w 0 195+w 1 15+w 2 62+w 3 250+w 4 234+w 5 171<w 0 192+w 1 0+w 2 3+w 3 13+w 4 53+w 5 215 at h15
  have h16:=decrease (code 311) (code 313) (by unfold Good;decide)
  change w 0 252+w 1 240+w 2 195+w 3 13+w 4 53+w 5 215<w 0 195+w 1 15+w 2 61+w 3 246+w 4 218+w 5 107 at h16
  have h17:=decrease (code 321) (code 343) (by unfold Good;decide)
  change w 0 57+w 1 228+w 2 145+w 3 70+w 4 26+w 5 107<w 0 204+w 1 49+w 2 196+w 3 17+w 4 69+w 5 23 at h17
  have h18:=decrease (code 335) (code 329) (by unfold Good;decide)
  change w 0 63+w 1 255+w 2 253+w 3 245+w 4 213+w 5 87<w 0 204+w 1 48+w 2 195+w 3 14+w 4 58+w 5 235 at h18
  have h19:=decrease (code 343) (code 321) (by unfold Good;decide)
  change w 0 54+w 1 216+w 2 98+w 3 137+w 4 37+w 5 151<w 0 204+w 1 50+w 2 200+w 3 34+w 4 138+w 5 43 at h19
  have h20:=decrease (code 351) (code 345) (by unfold Good;decide)
  change w 0 51+w 1 204+w 2 49+w 3 197+w 4 21+w 5 87<w 0 204+w 1 51+w 2 207+w 3 62+w 4 250+w 5 235 at h20
  have h21:=decrease (code 359) (code 337) (by unfold Good;decide)
  change w 0 51+w 1 207+w 2 62+w 3 249+w 4 229+w 5 151<w 0 206+w 1 57+w 2 228+w 3 146+w 4 74+w 5 43 at h21
  have h22:=decrease (code 377) (code 375) (by unfold Good;decide)
  change w 0 48+w 1 192+w 2 3+w 3 14+w 4 58+w 5 235<w 0 207+w 1 63+w 2 254+w 3 249+w 4 229+w 5 151 at h22
  have h23:=decrease (code 399) (code 393) (by unfold Good;decide)
  change w 0 51+w 1 207+w 2 61+w 3 245+w 4 213+w 5 87<w 0 240+w 1 192+w 2 3+w 3 14+w 4 58+w 5 235 at h23
  have h24:=decrease (code 431) (code 417) (by unfold Good;decide)
  change w 0 13+w 1 54+w 2 216+w 3 97+w 4 133+w 5 23<w 0 243+w 1 204+w 2 50+w 3 202+w 4 42+w 5 171 at h24
  have h25:=decrease (code 433) (code 447) (by unfold Good;decide)
  change w 0 12+w 1 50+w 2 200+w 3 34+w 4 138+w 5 43<w 0 243+w 1 207+w 2 61+w 3 245+w 4 213+w 5 87 at h25
  have h26:=decrease (code 463) (code 457) (by unfold Good;decide)
  change w 0 15+w 1 63+w 2 253+w 3 245+w 4 213+w 5 87<w 0 252+w 1 240+w 2 195+w 3 14+w 4 58+w 5 235 at h26
  have h27:=decrease (code 505) (code 503) (by unfold Good;decide)
  change w 0 0+w 1 0+w 2 3+w 3 14+w 4 58+w 5 235<w 0 255+w 1 255+w 2 254+w 3 249+w 4 229+w 5 151 at h27
  omega

/-- The same obstruction survives two-step amortization, even when both
intermediate states remain non-leaking. Ten exact witness transitions suffice. -/
theorem no_two_step_ranking (w : Nat → Nat → Int) :
    ¬ ∀ x y,Good x y → Good (T x) (T y) →
      potential w (T (T x)) (T (T y))<potential w x y := by
  intro decrease
  have h0:=decrease (code 55) (code 57) (by unfold Good;decide) (by unfold Good;decide)
  change w 0 207+w 1 63+w 2 254+w 3 250+w 4 234+w 5 171<w 0 3+w 1 15+w 2 61+w 3 246+w 4 218+w 5 107 at h0
  have h1:=decrease (code 161) (code 175) (by unfold Good;decide) (by unfold Good;decide)
  change w 0 51+w 1 207+w 2 62+w 3 249+w 4 229+w 5 151<w 0 51+w 1 204+w 2 49+w 3 197+w 4 21+w 5 87 at h1
  have h2:=decrease (code 175) (code 161) (by unfold Good;decide) (by unfold Good;decide)
  change w 0 51+w 1 207+w 2 61+w 3 246+w 4 218+w 5 107<w 0 51+w 1 204+w 2 50+w 3 202+w 4 42+w 5 171 at h2
  have h3:=decrease (code 375) (code 377) (by unfold Good;decide) (by unfold Good;decide)
  change w 0 243+w 1 207+w 2 62+w 3 250+w 4 234+w 5 171<w 0 207+w 1 63+w 2 253+w 3 246+w 4 218+w 5 107 at h3
  have h4:=decrease (code 425) (code 455) (by unfold Good;decide) (by unfold Good;decide)
  change w 0 243+w 1 204+w 2 49+w 3 197+w 4 21+w 5 87<w 0 246+w 1 216+w 2 98+w 3 137+w 4 37+w 5 151 at h4
  have h5:=decrease (code 433) (code 447) (by unfold Good;decide) (by unfold Good;decide)
  change w 0 246+w 1 216+w 2 98+w 3 137+w 4 37+w 5 151<w 0 243+w 1 207+w 2 61+w 3 245+w 4 213+w 5 87 at h5
  have h6:=decrease (code 441) (code 439) (by unfold Good;decide) (by unfold Good;decide)
  change w 0 255+w 1 255+w 2 253+w 3 245+w 4 213+w 5 87<w 0 243+w 1 207+w 2 62+w 3 249+w 4 229+w 5 151 at h6
  have h7:=decrease (code 447) (code 433) (by unfold Good;decide) (by unfold Good;decide)
  change w 0 249+w 1 228+w 2 145+w 3 70+w 4 26+w 5 107<w 0 243+w 1 207+w 2 62+w 3 250+w 4 234+w 5 171 at h7
  have h8:=decrease (code 455) (code 425) (by unfold Good;decide) (by unfold Good;decide)
  change w 0 243+w 1 204+w 2 50+w 3 202+w 4 42+w 5 171<w 0 249+w 1 228+w 2 145+w 3 70+w 4 26+w 5 107 at h8
  have h9:=decrease (code 505) (code 503) (by unfold Good;decide) (by unfold Good;decide)
  change w 0 3+w 1 15+w 2 61+w 3 245+w 4 213+w 5 87<w 0 255+w 1 255+w 2 254+w 3 249+w 4 229+w 5 151 at h9
  omega

end WindowBarrier
