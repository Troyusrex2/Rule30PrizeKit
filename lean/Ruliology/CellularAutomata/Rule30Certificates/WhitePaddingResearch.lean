module

public import Ruliology.CellularAutomata.Rule30WhitePaddingResearch

@[expose] public section

/-! Finite certificates for infinite white-padding families. Generated and independently
cross-checked with individual Boolean-cell updates on 2026-10-22. -/

namespace Ruliology.CellularAutomata.Rule30WhitePaddingResearch.Data

open Rule30StripCertificates Rule30WhitePaddingResearch

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Tail `101011`, width 6, padding threshold 13. -/
def tailA : List Bool := [true, false, true, false, true, true]
def fullAfterA : Nat := 12135283909754106411
def S1A : Nat := 16670045254742042054
def firstAfterA : Nat := 2314885530281582624
def S2A : Nat := 2450556340775428098
def secondAfterA : Nat := 2314885530281582624
theorem reachedFullA :
    zeros 6 13 (fullSet 6) = fullAfterA := by decide +kernel
theorem fullFixedA :
    image 6 false fullAfterA = fullAfterA := by decide +kernel
theorem firstTailA :
    applyWord 6 tailA fullAfterA = S1A := by decide +kernel
theorem reachedS1A :
    zeros 6 13 S1A = firstAfterA := by decide +kernel
theorem s1FixedA :
    image 6 false firstAfterA = firstAfterA := by decide +kernel
theorem secondTailA :
    applyWord 6 tailA firstAfterA = S2A := by decide +kernel
theorem reachedS2A :
    zeros 6 13 S2A = secondAfterA := by decide +kernel
theorem s2FixedA :
    image 6 false secondAfterA = secondAfterA := by decide +kernel
theorem returnCheckA :
    subsetB 6 (applyWord 6 tailA secondAfterA) S2A = true := by decide +kernel
theorem prefixCheckA :
    (List.range (13 + 1)).all (fun j => Forces 6 (zeros 6 j S2A)) = true := by decide +kernel
theorem tailCheckA :
    (List.range tailA.length).all (fun j => tailA.getD j false || Forces 6 (applyWord 6 (tailA.take j) secondAfterA)) = true := by decide +kernel

/-- Tail `1101`, width 7, padding threshold 14. -/
def tailB : List Bool := [true, true, false, true]
def fullAfterB : Nat := 223851284248093862149563454824011801131
def S1B : Nat := 113753186067998389845652128419517919508
def firstAfterB : Nat := 42702098401736576605054148790399803424
def S2B : Nat := 90408273238766351698413123729916706820
def secondAfterB : Nat := 42702098401736576605054148790399803424
theorem reachedFullB :
    zeros 7 14 (fullSet 7) = fullAfterB := by decide +kernel
theorem fullFixedB :
    image 7 false fullAfterB = fullAfterB := by decide +kernel
theorem firstTailB :
    applyWord 7 tailB fullAfterB = S1B := by decide +kernel
theorem reachedS1B :
    zeros 7 14 S1B = firstAfterB := by decide +kernel
theorem s1FixedB :
    image 7 false firstAfterB = firstAfterB := by decide +kernel
theorem secondTailB :
    applyWord 7 tailB firstAfterB = S2B := by decide +kernel
theorem reachedS2B :
    zeros 7 14 S2B = secondAfterB := by decide +kernel
theorem s2FixedB :
    image 7 false secondAfterB = secondAfterB := by decide +kernel
theorem returnCheckB :
    subsetB 7 (applyWord 7 tailB secondAfterB) S2B = true := by decide +kernel
theorem prefixCheckB :
    (List.range (14 + 1)).all (fun j => Forces 7 (zeros 7 j S2B)) = true := by decide +kernel
theorem tailCheckB :
    (List.range tailB.length).all (fun j => tailB.getD j false || Forces 7 (applyWord 7 (tailB.take j) secondAfterB)) = true := by decide +kernel

/-- Tail `11101`, width 9, padding threshold 23. -/
def tailC : List Bool := [true, true, true, false, true]
def fullAfterC : Nat := 2116285514885801457635146027046740496486532127015752388745986936636056968695200882703331342502516213612914180386061239056673935869658686492862515608298017
def S1C : Nat := 916780779437495096225433410957078671666245257464487717391412273520243154885168947103517908183877893529987605309737908219451586664310583719169140233150726
def firstAfterC : Nat := 6546781217316575024715261696231958128819265592889731469339975697437060823672137628419460291436582434356409746466282348087791606870152268051427186704384
def S2C : Nat := 25573364130142871190293991000906086440700256222225513552109280068113518842469287611013516763424150134204725572133915422217935964336532297075887448064
def secondAfterC : Nat := 6546781217316575024715261696231958128819265592889731469339975697437060823672137628419460291436582434356409746466282348087791606870152268051427186704384
theorem reachedFullC :
    zeros 9 23 (fullSet 9) = fullAfterC := by decide +kernel
theorem fullFixedC :
    image 9 false fullAfterC = fullAfterC := by decide +kernel
theorem firstTailC :
    applyWord 9 tailC fullAfterC = S1C := by decide +kernel
theorem reachedS1C :
    zeros 9 23 S1C = firstAfterC := by decide +kernel
theorem s1FixedC :
    image 9 false firstAfterC = firstAfterC := by decide +kernel
theorem secondTailC :
    applyWord 9 tailC firstAfterC = S2C := by decide +kernel
theorem reachedS2C :
    zeros 9 23 S2C = secondAfterC := by decide +kernel
theorem s2FixedC :
    image 9 false secondAfterC = secondAfterC := by decide +kernel
theorem returnCheckC :
    subsetB 9 (applyWord 9 tailC secondAfterC) S2C = true := by decide +kernel
theorem prefixCheckC :
    (List.range (23 + 1)).all (fun j => Forces 9 (zeros 9 j S2C)) = true := by decide +kernel
theorem tailCheckC :
    (List.range tailC.length).all (fun j => tailC.getD j false || Forces 9 (applyWord 9 (tailC.take j) secondAfterC)) = true := by decide +kernel

/-- Tail `101`, width 9, padding threshold 23. -/
def tailD : List Bool := [true, false, true]
def fullAfterD : Nat := 2116285514885801457635146027046740496486532127015752388745986936636056968695200882703331342502516213612914180386061239056673935869658686492862515608298017
def S1D : Nat := 1051785368839430038111105340624616718743352105526631297980524740110279997038810093468615589443687092390484735668583803795121266605297789947542550955181076
def firstAfterD : Nat := 6546781217316575024715261696231958128819265592889731469339975697437060823672137628419460291436582434356409746466282348087791606870152268051427186704384
def S2D : Nat := 818347652164571878089407712028994766102408199111216433667496962179632602959017203552432536429572804294551218308285293510973950858769033506428398338048
def secondAfterD : Nat := 6546781217316575024715261696231958128819265592889731469339975697437060823672137628419460291436582434356409746466282348087791606870152268051427186704384
theorem reachedFullD :
    zeros 9 23 (fullSet 9) = fullAfterD := by decide +kernel
theorem fullFixedD :
    image 9 false fullAfterD = fullAfterD := by decide +kernel
theorem firstTailD :
    applyWord 9 tailD fullAfterD = S1D := by decide +kernel
theorem reachedS1D :
    zeros 9 23 S1D = firstAfterD := by decide +kernel
theorem s1FixedD :
    image 9 false firstAfterD = firstAfterD := by decide +kernel
theorem secondTailD :
    applyWord 9 tailD firstAfterD = S2D := by decide +kernel
theorem reachedS2D :
    zeros 9 23 S2D = secondAfterD := by decide +kernel
theorem s2FixedD :
    image 9 false secondAfterD = secondAfterD := by decide +kernel
theorem returnCheckD :
    subsetB 9 (applyWord 9 tailD secondAfterD) S2D = true := by decide +kernel
theorem prefixCheckD :
    (List.range (23 + 1)).all (fun j => Forces 9 (zeros 9 j S2D)) = true := by decide +kernel
theorem tailCheckD :
    (List.range tailD.length).all (fun j => tailD.getD j false || Forces 9 (applyWord 9 (tailD.take j) secondAfterD)) = true := by decide +kernel

/-- Tail `1111`, width 10, padding threshold 31. -/
def tailE : List Bool := [true, true, true, true]
def fullAfterE : Nat := 22735012826402829640330845028270138285322580040444007300909362385916439266896543149610238686320216056435780344404205848328219421260474298750385351543389654728234198340007085173652166890015379376283335268515280352133205158392792810606103065109052716427422735929218602287628814021845225225961682986285373333537
def S1E : Nat := 4220203796918006597885377979697452555332151157780197425716103857574784588535011671961832494393949002521501215053941225433690111992318267371412433395247133250285348030933806639083585881283348764741258548489951615680861468225935543863980651986906262883390892808935077976779606176710456743585139547350839075842
def firstAfterE : Nat := 20437404769635530871361256581497226916590761041489522826825853024121123827628862611258784858531572093583605497426944983270793880309205576804419431127455768907053467041024236605610570403038465597814610342235701210833797771300296279067536471169722007548774791550692823419537948698000785373422157824
def S2E : Nat := 326998476314168493941780105303955630665452176663832365229213648385937981242061801780140557736505153497337687958831119732332702084947289228870710898039292302512855472656387785689769126448615449565033765475771219373340764340804740465080583538715552120780396664811085174712607179168012565974754525184
def secondAfterE : Nat := 20437404769635530871361256581497226916590761041489522826825853024121123827628862611258784858531572093583605497426944983270793880309205576804419431127455768907053467041024236605610570403038465597814610342235701210833797771300296279067536471169722007548774791550692823419537948698000785373422157824
theorem reachedFullE :
    zeros 10 31 (fullSet 10) = fullAfterE := by decide +kernel
theorem fullFixedE :
    image 10 false fullAfterE = fullAfterE := by decide +kernel
theorem firstTailE :
    applyWord 10 tailE fullAfterE = S1E := by decide +kernel
theorem reachedS1E :
    zeros 10 31 S1E = firstAfterE := by decide +kernel
theorem s1FixedE :
    image 10 false firstAfterE = firstAfterE := by decide +kernel
theorem secondTailE :
    applyWord 10 tailE firstAfterE = S2E := by decide +kernel
theorem reachedS2E :
    zeros 10 31 S2E = secondAfterE := by decide +kernel
theorem s2FixedE :
    image 10 false secondAfterE = secondAfterE := by decide +kernel
theorem returnCheckE :
    subsetB 10 (applyWord 10 tailE secondAfterE) S2E = true := by decide +kernel
theorem prefixCheckE :
    (List.range (31 + 1)).all (fun j => Forces 10 (zeros 10 j S2E)) = true := by decide +kernel
theorem tailCheckE :
    (List.range tailE.length).all (fun j => tailE.getD j false || Forces 10 (applyWord 10 (tailE.take j) secondAfterE)) = true := by decide +kernel



theorem stableFullA : zeros 6 (13 + 1) (fullSet 6) = zeros 6 13 (fullSet 6) := by
  rw [zeros_succ, reachedFullA, fullFixedA]

theorem stableS1A : zeros 6 (13 + 1) S1A = zeros 6 13 S1A := by
  rw [zeros_succ, reachedS1A, s1FixedA]

theorem stableS2A : zeros 6 (13 + 1) S2A = zeros 6 13 S2A := by
  rw [zeros_succ, reachedS2A, s2FixedA]

/-- Every padding length `r >= 13` is excluded, whatever the transient. -/
theorem no_paddingA (r : Nat) (hr : 13 ≤ r) :
    ¬ EventuallyWord (List.replicate r false ++ tailA) := by
  apply no_padding_word tailA 6 13 S1A S2A
  · rw [reachedFullA]; exact firstTailA
  · rw [reachedS1A]; exact secondTailA
  · exact stableFullA
  · exact stableS1A
  · exact stableS2A
  · rw [reachedS2A]; exact returnCheckA
  · exact prefixCheckA
  · rw [reachedS2A]; exact tailCheckA
  · decide
  · decide
  · exact hr

theorem stableFullB : zeros 7 (14 + 1) (fullSet 7) = zeros 7 14 (fullSet 7) := by
  rw [zeros_succ, reachedFullB, fullFixedB]

theorem stableS1B : zeros 7 (14 + 1) S1B = zeros 7 14 S1B := by
  rw [zeros_succ, reachedS1B, s1FixedB]

theorem stableS2B : zeros 7 (14 + 1) S2B = zeros 7 14 S2B := by
  rw [zeros_succ, reachedS2B, s2FixedB]

/-- Every padding length `r >= 14` is excluded, whatever the transient. -/
theorem no_paddingB (r : Nat) (hr : 14 ≤ r) :
    ¬ EventuallyWord (List.replicate r false ++ tailB) := by
  apply no_padding_word tailB 7 14 S1B S2B
  · rw [reachedFullB]; exact firstTailB
  · rw [reachedS1B]; exact secondTailB
  · exact stableFullB
  · exact stableS1B
  · exact stableS2B
  · rw [reachedS2B]; exact returnCheckB
  · exact prefixCheckB
  · rw [reachedS2B]; exact tailCheckB
  · decide
  · decide
  · exact hr

theorem stableFullC : zeros 9 (23 + 1) (fullSet 9) = zeros 9 23 (fullSet 9) := by
  rw [zeros_succ, reachedFullC, fullFixedC]

theorem stableS1C : zeros 9 (23 + 1) S1C = zeros 9 23 S1C := by
  rw [zeros_succ, reachedS1C, s1FixedC]

theorem stableS2C : zeros 9 (23 + 1) S2C = zeros 9 23 S2C := by
  rw [zeros_succ, reachedS2C, s2FixedC]

/-- Every padding length `r >= 23` is excluded, whatever the transient. -/
theorem no_paddingC (r : Nat) (hr : 23 ≤ r) :
    ¬ EventuallyWord (List.replicate r false ++ tailC) := by
  apply no_padding_word tailC 9 23 S1C S2C
  · rw [reachedFullC]; exact firstTailC
  · rw [reachedS1C]; exact secondTailC
  · exact stableFullC
  · exact stableS1C
  · exact stableS2C
  · rw [reachedS2C]; exact returnCheckC
  · exact prefixCheckC
  · rw [reachedS2C]; exact tailCheckC
  · decide
  · decide
  · exact hr

theorem stableFullD : zeros 9 (23 + 1) (fullSet 9) = zeros 9 23 (fullSet 9) := by
  rw [zeros_succ, reachedFullD, fullFixedD]

theorem stableS1D : zeros 9 (23 + 1) S1D = zeros 9 23 S1D := by
  rw [zeros_succ, reachedS1D, s1FixedD]

theorem stableS2D : zeros 9 (23 + 1) S2D = zeros 9 23 S2D := by
  rw [zeros_succ, reachedS2D, s2FixedD]

/-- Every padding length `r >= 23` is excluded, whatever the transient. -/
theorem no_paddingD (r : Nat) (hr : 23 ≤ r) :
    ¬ EventuallyWord (List.replicate r false ++ tailD) := by
  apply no_padding_word tailD 9 23 S1D S2D
  · rw [reachedFullD]; exact firstTailD
  · rw [reachedS1D]; exact secondTailD
  · exact stableFullD
  · exact stableS1D
  · exact stableS2D
  · rw [reachedS2D]; exact returnCheckD
  · exact prefixCheckD
  · rw [reachedS2D]; exact tailCheckD
  · decide
  · decide
  · exact hr

theorem stableFullE : zeros 10 (31 + 1) (fullSet 10) = zeros 10 31 (fullSet 10) := by
  rw [zeros_succ, reachedFullE, fullFixedE]

theorem stableS1E : zeros 10 (31 + 1) S1E = zeros 10 31 S1E := by
  rw [zeros_succ, reachedS1E, s1FixedE]

theorem stableS2E : zeros 10 (31 + 1) S2E = zeros 10 31 S2E := by
  rw [zeros_succ, reachedS2E, s2FixedE]

/-- Every padding length `r >= 31` is excluded, whatever the transient. -/
theorem no_paddingE (r : Nat) (hr : 31 ≤ r) :
    ¬ EventuallyWord (List.replicate r false ++ tailE) := by
  apply no_padding_word tailE 10 31 S1E S2E
  · rw [reachedFullE]; exact firstTailE
  · rw [reachedS1E]; exact secondTailE
  · exact stableFullE
  · exact stableS1E
  · exact stableS2E
  · rw [reachedS2E]; exact returnCheckE
  · exact prefixCheckE
  · rw [reachedS2E]; exact tailCheckE
  · decide
  · decide
  · exact hr

end Ruliology.CellularAutomata.Rule30WhitePaddingResearch.Data
