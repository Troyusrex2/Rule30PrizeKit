module

public import Ruliology.CellularAutomata.Rule30WhitePaddingResearch

@[expose] public section

/-! Finite certificates for infinite white-padding families. Generated and independently
cross-checked with individual Boolean-cell updates on 2026-10-22. -/

namespace Ruliology.CellularAutomata.Rule30WhitePaddingResearch.CheapTails

open Rule30StripCertificates Rule30WhitePaddingResearch

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Tail `1`, width 8, padding threshold 21. -/
def tailF : List Bool := [true]
def fullAfterF : Nat := 18276598471178533808653620785334407632999626230426982429422313919827417768481
def S1F : Nat := 9308082195878321786929399657238249500747145232440464204667349278320665825554
def firstAfterF : Nat := 56539106086072335008300159443458547530007962734750140563158938493558718464
def S2F : Nat := 28269553043036167504150079721729273765003981367375070281579469246779359232
def secondAfterF : Nat := 56539106086072335008300159443458547530007962734750140563158938493558718464
theorem reachedFullF :
    zeros 8 21 (fullSet 8) = fullAfterF := by decide +kernel
theorem fullFixedF :
    image 8 false fullAfterF = fullAfterF := by decide +kernel
theorem firstTailF :
    applyWord 8 tailF fullAfterF = S1F := by decide +kernel
theorem reachedS1F :
    zeros 8 21 S1F = firstAfterF := by decide +kernel
theorem s1FixedF :
    image 8 false firstAfterF = firstAfterF := by decide +kernel
theorem secondTailF :
    applyWord 8 tailF firstAfterF = S2F := by decide +kernel
theorem reachedS2F :
    zeros 8 21 S2F = secondAfterF := by decide +kernel
theorem s2FixedF :
    image 8 false secondAfterF = secondAfterF := by decide +kernel
theorem returnCheckF :
    subsetB 8 (applyWord 8 tailF secondAfterF) S2F = true := by decide +kernel
theorem prefixCheckF :
    (List.range (21 + 1)).all (fun j => Forces 8 (zeros 8 j S2F)) = true := by decide +kernel
theorem tailCheckF :
    (List.range tailF.length).all (fun j => tailF.getD j false || Forces 8 (applyWord 8 (tailF.take j) secondAfterF)) = true := by decide +kernel

/-- Tail `11`, width 6, padding threshold 11. -/
def tailG : List Bool := [true, true]
def fullAfterG : Nat := 12135283909754106411
def S1G : Nat := 16273687805569385670
def firstAfterG : Nat := 2314885530281582624
def S2G : Nat := 9259542121126330496
def secondAfterG : Nat := 2314885530281582624
theorem reachedFullG :
    zeros 6 11 (fullSet 6) = fullAfterG := by decide +kernel
theorem fullFixedG :
    image 6 false fullAfterG = fullAfterG := by decide +kernel
theorem firstTailG :
    applyWord 6 tailG fullAfterG = S1G := by decide +kernel
theorem reachedS1G :
    zeros 6 11 S1G = firstAfterG := by decide +kernel
theorem s1FixedG :
    image 6 false firstAfterG = firstAfterG := by decide +kernel
theorem secondTailG :
    applyWord 6 tailG firstAfterG = S2G := by decide +kernel
theorem reachedS2G :
    zeros 6 11 S2G = secondAfterG := by decide +kernel
theorem s2FixedG :
    image 6 false secondAfterG = secondAfterG := by decide +kernel
theorem returnCheckG :
    subsetB 6 (applyWord 6 tailG secondAfterG) S2G = true := by decide +kernel
theorem prefixCheckG :
    (List.range (11 + 1)).all (fun j => Forces 6 (zeros 6 j S2G)) = true := by decide +kernel
theorem tailCheckG :
    (List.range tailG.length).all (fun j => tailG.getD j false || Forces 6 (applyWord 6 (tailG.take j) secondAfterG)) = true := by decide +kernel

/-- Tail `1001`, width 8, padding threshold 22. -/
def tailH : List Bool := [true, false, false, true]
def fullAfterH : Nat := 18276598471178533808653620785334407632999626230426982429422313919827417768481
def S1H : Nat := 38030306938552811678086419077549010051149760153345990876459986161065547338004
def firstAfterH : Nat := 56539106086072335008300159443458547530007962734750140563158938493558718464
def S2H : Nat := 7237005579017258881062420408762694083841019230048017992084344127175515963392
def secondAfterH : Nat := 56539106086072335008300159443458547530007962734750140563158938493558718464
theorem reachedFullH :
    zeros 8 22 (fullSet 8) = fullAfterH := by decide +kernel
theorem fullFixedH :
    image 8 false fullAfterH = fullAfterH := by decide +kernel
theorem firstTailH :
    applyWord 8 tailH fullAfterH = S1H := by decide +kernel
theorem reachedS1H :
    zeros 8 22 S1H = firstAfterH := by decide +kernel
theorem s1FixedH :
    image 8 false firstAfterH = firstAfterH := by decide +kernel
theorem secondTailH :
    applyWord 8 tailH firstAfterH = S2H := by decide +kernel
theorem reachedS2H :
    zeros 8 22 S2H = secondAfterH := by decide +kernel
theorem s2FixedH :
    image 8 false secondAfterH = secondAfterH := by decide +kernel
theorem returnCheckH :
    subsetB 8 (applyWord 8 tailH secondAfterH) S2H = true := by decide +kernel
theorem prefixCheckH :
    (List.range (22 + 1)).all (fun j => Forces 8 (zeros 8 j S2H)) = true := by decide +kernel
theorem tailCheckH :
    (List.range tailH.length).all (fun j => tailH.getD j false || Forces 8 (applyWord 8 (tailH.take j) secondAfterH)) = true := by decide +kernel

/-- Tail `1011`, width 6, padding threshold 13. -/
def tailI : List Bool := [true, false, true, true]
def fullAfterI : Nat := 12135283909754106411
def S1I : Nat := 16701288908436334022
def firstAfterI : Nat := 2314885530281582624
def S2I : Nat := 4917935467153851456
def secondAfterI : Nat := 2314885530281582624
theorem reachedFullI :
    zeros 6 13 (fullSet 6) = fullAfterI := by decide +kernel
theorem fullFixedI :
    image 6 false fullAfterI = fullAfterI := by decide +kernel
theorem firstTailI :
    applyWord 6 tailI fullAfterI = S1I := by decide +kernel
theorem reachedS1I :
    zeros 6 13 S1I = firstAfterI := by decide +kernel
theorem s1FixedI :
    image 6 false firstAfterI = firstAfterI := by decide +kernel
theorem secondTailI :
    applyWord 6 tailI firstAfterI = S2I := by decide +kernel
theorem reachedS2I :
    zeros 6 13 S2I = secondAfterI := by decide +kernel
theorem s2FixedI :
    image 6 false secondAfterI = secondAfterI := by decide +kernel
theorem returnCheckI :
    subsetB 6 (applyWord 6 tailI secondAfterI) S2I = true := by decide +kernel
theorem prefixCheckI :
    (List.range (13 + 1)).all (fun j => Forces 6 (zeros 6 j S2I)) = true := by decide +kernel
theorem tailCheckI :
    (List.range tailI.length).all (fun j => tailI.getD j false || Forces 6 (applyWord 6 (tailI.take j) secondAfterI)) = true := by decide +kernel



theorem stableFullF : zeros 8 (21 + 1) (fullSet 8) = zeros 8 21 (fullSet 8) := by
  rw [zeros_succ, reachedFullF, fullFixedF]

theorem stableS1F : zeros 8 (21 + 1) S1F = zeros 8 21 S1F := by
  rw [zeros_succ, reachedS1F, s1FixedF]

theorem stableS2F : zeros 8 (21 + 1) S2F = zeros 8 21 S2F := by
  rw [zeros_succ, reachedS2F, s2FixedF]

/-- Every padding length `r >= 21` is excluded, whatever the transient. -/
theorem no_paddingF (r : Nat) (hr : 21 ≤ r) :
    ¬ EventuallyWord (List.replicate r false ++ tailF) := by
  apply no_padding_word tailF 8 21 S1F S2F
  · rw [reachedFullF]; exact firstTailF
  · rw [reachedS1F]; exact secondTailF
  · exact stableFullF
  · exact stableS1F
  · exact stableS2F
  · rw [reachedS2F]; exact returnCheckF
  · exact prefixCheckF
  · rw [reachedS2F]; exact tailCheckF
  · decide
  · decide
  · exact hr

theorem stableFullG : zeros 6 (11 + 1) (fullSet 6) = zeros 6 11 (fullSet 6) := by
  rw [zeros_succ, reachedFullG, fullFixedG]

theorem stableS1G : zeros 6 (11 + 1) S1G = zeros 6 11 S1G := by
  rw [zeros_succ, reachedS1G, s1FixedG]

theorem stableS2G : zeros 6 (11 + 1) S2G = zeros 6 11 S2G := by
  rw [zeros_succ, reachedS2G, s2FixedG]

/-- Every padding length `r >= 11` is excluded, whatever the transient. -/
theorem no_paddingG (r : Nat) (hr : 11 ≤ r) :
    ¬ EventuallyWord (List.replicate r false ++ tailG) := by
  apply no_padding_word tailG 6 11 S1G S2G
  · rw [reachedFullG]; exact firstTailG
  · rw [reachedS1G]; exact secondTailG
  · exact stableFullG
  · exact stableS1G
  · exact stableS2G
  · rw [reachedS2G]; exact returnCheckG
  · exact prefixCheckG
  · rw [reachedS2G]; exact tailCheckG
  · decide
  · decide
  · exact hr

theorem stableFullH : zeros 8 (22 + 1) (fullSet 8) = zeros 8 22 (fullSet 8) := by
  rw [zeros_succ, reachedFullH, fullFixedH]

theorem stableS1H : zeros 8 (22 + 1) S1H = zeros 8 22 S1H := by
  rw [zeros_succ, reachedS1H, s1FixedH]

theorem stableS2H : zeros 8 (22 + 1) S2H = zeros 8 22 S2H := by
  rw [zeros_succ, reachedS2H, s2FixedH]

/-- Every padding length `r >= 22` is excluded, whatever the transient. -/
theorem no_paddingH (r : Nat) (hr : 22 ≤ r) :
    ¬ EventuallyWord (List.replicate r false ++ tailH) := by
  apply no_padding_word tailH 8 22 S1H S2H
  · rw [reachedFullH]; exact firstTailH
  · rw [reachedS1H]; exact secondTailH
  · exact stableFullH
  · exact stableS1H
  · exact stableS2H
  · rw [reachedS2H]; exact returnCheckH
  · exact prefixCheckH
  · rw [reachedS2H]; exact tailCheckH
  · decide
  · decide
  · exact hr

theorem stableFullI : zeros 6 (13 + 1) (fullSet 6) = zeros 6 13 (fullSet 6) := by
  rw [zeros_succ, reachedFullI, fullFixedI]

theorem stableS1I : zeros 6 (13 + 1) S1I = zeros 6 13 S1I := by
  rw [zeros_succ, reachedS1I, s1FixedI]

theorem stableS2I : zeros 6 (13 + 1) S2I = zeros 6 13 S2I := by
  rw [zeros_succ, reachedS2I, s2FixedI]

/-- Every padding length `r >= 13` is excluded, whatever the transient. -/
theorem no_paddingI (r : Nat) (hr : 13 ≤ r) :
    ¬ EventuallyWord (List.replicate r false ++ tailI) := by
  apply no_padding_word tailI 6 13 S1I S2I
  · rw [reachedFullI]; exact firstTailI
  · rw [reachedS1I]; exact secondTailI
  · exact stableFullI
  · exact stableS1I
  · exact stableS2I
  · rw [reachedS2I]; exact returnCheckI
  · exact prefixCheckI
  · rw [reachedS2I]; exact tailCheckI
  · decide
  · decide
  · exact hr

end Ruliology.CellularAutomata.Rule30WhitePaddingResearch.CheapTails
