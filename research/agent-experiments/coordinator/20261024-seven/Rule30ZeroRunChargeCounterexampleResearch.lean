import Rule30ZeroRunSpatialChargeReductionResearch
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

def diag1 : List Nat := [1]
theorem level1 :
    diag1.map (fun a => a.testBit 0)=AD (alt witness) 1 0 1 /\
    Theta witness 1=true := by
  have h := level (alt witness) 0 0 diag0 diag0 1
    sem0 sem0 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag0 (0 :: diag0)).1)=diag1 := by decide +kernel
  have hl : (scanN 1 diag0 (0 :: diag0)).2.testBit 0=true := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag2 : List Nat := [0,1]
theorem level2 :
    diag2.map (fun a => a.testBit 0)=AD (alt witness) 2 0 2 /\
    Theta witness 2=true := by
  have h := level (alt witness) 0 1 diag1 diag0 0
    level1.1 sem0 (by decide +kernel)
  have hc : (0 :: (scanN 0 diag1 (0 :: diag0)).1)=diag2 := by decide +kernel
  have hl : (scanN 0 diag1 (0 :: diag0)).2.testBit 0=true := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag3 : List Nat := [1,1,0]
theorem level3 :
    diag3.map (fun a => a.testBit 0)=AD (alt witness) 3 0 3 /\
    Theta witness 3=false := by
  have h := level (alt witness) 0 2 diag2 diag1 1
    level2.1 level1.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag2 (0 :: diag1)).1)=diag3 := by decide +kernel
  have hl : (scanN 1 diag2 (0 :: diag1)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag4 : List Nat := [1,0,1,0]
theorem level4 :
    diag4.map (fun a => a.testBit 0)=AD (alt witness) 4 0 4 /\
    Theta witness 4=false := by
  have h := level (alt witness) 0 3 diag3 diag2 1
    level3.1 level2.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag3 (0 :: diag2)).1)=diag4 := by decide +kernel
  have hl : (scanN 1 diag3 (0 :: diag2)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag5 : List Nat := [1,0,1,0,0]
theorem level5 :
    diag5.map (fun a => a.testBit 0)=AD (alt witness) 5 0 5 /\
    Theta witness 5=false := by
  have h := level (alt witness) 0 4 diag4 diag3 1
    level4.1 level3.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag4 (0 :: diag3)).1)=diag5 := by decide +kernel
  have hl : (scanN 1 diag4 (0 :: diag3)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag6 : List Nat := [1,0,1,0,1,1]
theorem level6 :
    diag6.map (fun a => a.testBit 0)=AD (alt witness) 6 0 6 /\
    Theta witness 6=true := by
  have h := level (alt witness) 0 5 diag5 diag4 1
    level5.1 level4.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag5 (0 :: diag4)).1)=diag6 := by decide +kernel
  have hl : (scanN 1 diag5 (0 :: diag4)).2.testBit 0=true := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag7 : List Nat := [1,0,1,0,1,0,1]
theorem level7 :
    diag7.map (fun a => a.testBit 0)=AD (alt witness) 7 0 7 /\
    Theta witness 7=true := by
  have h := level (alt witness) 0 6 diag6 diag5 1
    level6.1 level5.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag6 (0 :: diag5)).1)=diag7 := by decide +kernel
  have hl : (scanN 1 diag6 (0 :: diag5)).2.testBit 0=true := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag8 : List Nat := [0,1,0,1,0,1,0,1]
theorem level8 :
    diag8.map (fun a => a.testBit 0)=AD (alt witness) 8 0 8 /\
    Theta witness 8=true := by
  have h := level (alt witness) 0 7 diag7 diag6 0
    level7.1 level6.1 (by decide +kernel)
  have hc : (0 :: (scanN 0 diag7 (0 :: diag6)).1)=diag8 := by decide +kernel
  have hl : (scanN 0 diag7 (0 :: diag6)).2.testBit 0=true := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag9 : List Nat := [1,1,0,0,1,1,0,0,1]
theorem level9 :
    diag9.map (fun a => a.testBit 0)=AD (alt witness) 9 0 9 /\
    Theta witness 9=true := by
  have h := level (alt witness) 0 8 diag8 diag7 1
    level8.1 level7.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag8 (0 :: diag7)).1)=diag9 := by decide +kernel
  have hl : (scanN 1 diag8 (0 :: diag7)).2.testBit 0=true := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag10 : List Nat := [1,0,1,0,0,1,0,1,1,0]
theorem level10 :
    diag10.map (fun a => a.testBit 0)=AD (alt witness) 10 0 10 /\
    Theta witness 10=false := by
  have h := level (alt witness) 0 9 diag9 diag8 1
    level9.1 level8.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag9 (0 :: diag8)).1)=diag10 := by decide +kernel
  have hl : (scanN 1 diag9 (0 :: diag8)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag11 : List Nat := [1,0,1,0,0,0,1,0,1,0,1]
theorem level11 :
    diag11.map (fun a => a.testBit 0)=AD (alt witness) 11 0 11 /\
    Theta witness 11=true := by
  have h := level (alt witness) 0 10 diag10 diag9 1
    level10.1 level9.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag10 (0 :: diag9)).1)=diag11 := by decide +kernel
  have hl : (scanN 1 diag10 (0 :: diag9)).2.testBit 0=true := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag12 : List Nat := [0,1,0,1,0,0,0,1,1,0,1,0]
theorem level12 :
    diag12.map (fun a => a.testBit 0)=AD (alt witness) 12 0 12 /\
    Theta witness 12=false := by
  have h := level (alt witness) 0 11 diag11 diag10 0
    level11.1 level10.1 (by decide +kernel)
  have hc : (0 :: (scanN 0 diag11 (0 :: diag10)).1)=diag12 := by decide +kernel
  have hl : (scanN 0 diag11 (0 :: diag10)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag13 : List Nat := [1,1,0,0,1,1,1,1,0,1,0,1,0]
theorem level13 :
    diag13.map (fun a => a.testBit 0)=AD (alt witness) 13 0 13 /\
    Theta witness 13=false := by
  have h := level (alt witness) 0 12 diag12 diag11 1
    level12.1 level11.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag12 (0 :: diag11)).1)=diag13 := by decide +kernel
  have hl : (scanN 1 diag12 (0 :: diag11)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag14 : List Nat := [0,1,0,1,1,0,1,0,1,0,1,1,0,0]
theorem level14 :
    diag14.map (fun a => a.testBit 0)=AD (alt witness) 14 0 14 /\
    Theta witness 14=false := by
  have h := level (alt witness) 0 13 diag13 diag12 0
    level13.1 level12.1 (by decide +kernel)
  have hc : (0 :: (scanN 0 diag13 (0 :: diag12)).1)=diag14 := by decide +kernel
  have hl : (scanN 0 diag13 (0 :: diag12)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag15 : List Nat := [1,1,0,1,0,1,0,1,0,1,1,0,1,0,0]
theorem level15 :
    diag15.map (fun a => a.testBit 0)=AD (alt witness) 15 0 15 /\
    Theta witness 15=false := by
  have h := level (alt witness) 0 14 diag14 diag13 1
    level14.1 level13.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag14 (0 :: diag13)).1)=diag15 := by decide +kernel
  have hl : (scanN 1 diag14 (0 :: diag13)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag16 : List Nat := [1,0,1,0,1,0,1,1,0,0,1,0,1,0,0,0]
theorem level16 :
    diag16.map (fun a => a.testBit 0)=AD (alt witness) 16 0 16 /\
    Theta witness 16=false := by
  have h := level (alt witness) 0 15 diag15 diag14 1
    level15.1 level14.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag15 (0 :: diag14)).1)=diag16 := by decide +kernel
  have hl : (scanN 1 diag15 (0 :: diag14)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag17 : List Nat := [1,0,1,0,0,1,1,0,1,0,0,1,0,1,0,0,0]
theorem level17 :
    diag17.map (fun a => a.testBit 0)=AD (alt witness) 17 0 17 /\
    Theta witness 17=false := by
  have h := level (alt witness) 0 16 diag16 diag15 1
    level16.1 level15.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag16 (0 :: diag15)).1)=diag17 := by decide +kernel
  have hl : (scanN 1 diag16 (0 :: diag15)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag18 : List Nat := [0,1,0,1,0,0,1,0,1,0,0,0,1,1,0,0,0,0]
theorem level18 :
    diag18.map (fun a => a.testBit 0)=AD (alt witness) 18 0 18 /\
    Theta witness 18=false := by
  have h := level (alt witness) 0 17 diag17 diag16 0
    level17.1 level16.1 (by decide +kernel)
  have hc : (0 :: (scanN 0 diag17 (0 :: diag16)).1)=diag18 := by decide +kernel
  have hl : (scanN 0 diag17 (0 :: diag16)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag19 : List Nat := [1,1,0,0,1,1,1,0,1,0,1,1,1,0,1,0,0,0,0]
theorem level19 :
    diag19.map (fun a => a.testBit 0)=AD (alt witness) 19 0 19 /\
    Theta witness 19=false := by
  have h := level (alt witness) 0 18 diag18 diag17 1
    level18.1 level17.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag18 (0 :: diag17)).1)=diag19 := by decide +kernel
  have hl : (scanN 1 diag18 (0 :: diag17)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag20 : List Nat := [0,1,0,1,1,0,1,0,1,0,1,0,1,0,1,0,0,0,0,0]
theorem level20 :
    diag20.map (fun a => a.testBit 0)=AD (alt witness) 20 0 20 /\
    Theta witness 20=false := by
  have h := level (alt witness) 0 19 diag19 diag18 0
    level19.1 level18.1 (by decide +kernel)
  have hc : (0 :: (scanN 0 diag19 (0 :: diag18)).1)=diag20 := by decide +kernel
  have hl : (scanN 0 diag19 (0 :: diag18)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag21 : List Nat := [1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,0,0,0]
theorem level21 :
    diag21.map (fun a => a.testBit 0)=AD (alt witness) 21 0 21 /\
    Theta witness 21=false := by
  have h := level (alt witness) 0 20 diag20 diag19 1
    level20.1 level19.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag20 (0 :: diag19)).1)=diag21 := by decide +kernel
  have hl : (scanN 1 diag20 (0 :: diag19)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag22 : List Nat := [1,0,1,0,1,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,0,0]
theorem level22 :
    diag22.map (fun a => a.testBit 0)=AD (alt witness) 22 0 22 /\
    Theta witness 22=false := by
  have h := level (alt witness) 0 21 diag21 diag20 1
    level21.1 level20.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag21 (0 :: diag20)).1)=diag22 := by decide +kernel
  have hl : (scanN 1 diag21 (0 :: diag20)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag23 : List Nat := [1,0,1,0,0,1,1,0,1,0,0,1,0,1,1,0,1,0,0,0,0,0,0]
theorem level23 :
    diag23.map (fun a => a.testBit 0)=AD (alt witness) 23 0 23 /\
    Theta witness 23=false := by
  have h := level (alt witness) 0 22 diag22 diag21 1
    level22.1 level21.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag22 (0 :: diag21)).1)=diag23 := by decide +kernel
  have hl : (scanN 1 diag22 (0 :: diag21)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag24 : List Nat := [0,1,0,1,0,0,1,0,1,0,0,0,1,0,1,0,1,0,0,0,0,0,0,0]
theorem level24 :
    diag24.map (fun a => a.testBit 0)=AD (alt witness) 24 0 24 /\
    Theta witness 24=false := by
  have h := level (alt witness) 0 23 diag23 diag22 0
    level23.1 level22.1 (by decide +kernel)
  have hc : (0 :: (scanN 0 diag23 (0 :: diag22)).1)=diag24 := by decide +kernel
  have hl : (scanN 0 diag23 (0 :: diag22)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag25 : List Nat := [1,1,0,0,1,1,1,0,1,0,1,1,1,0,0,1,0,1,0,0,0,0,0,0,0]
theorem level25 :
    diag25.map (fun a => a.testBit 0)=AD (alt witness) 25 0 25 /\
    Theta witness 25=false := by
  have h := level (alt witness) 0 24 diag24 diag23 1
    level24.1 level23.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag24 (0 :: diag23)).1)=diag25 := by decide +kernel
  have hl : (scanN 1 diag24 (0 :: diag23)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag26 : List Nat := [1,0,1,0,0,1,0,1,0,1,0,1,0,1,0,0,1,1,0,0,0,0,0,0,0,0]
theorem level26 :
    diag26.map (fun a => a.testBit 0)=AD (alt witness) 26 0 26 /\
    Theta witness 26=false := by
  have h := level (alt witness) 0 25 diag25 diag24 1
    level25.1 level24.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag25 (0 :: diag24)).1)=diag26 := by decide +kernel
  have hl : (scanN 1 diag25 (0 :: diag24)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag27 : List Nat := [1,0,1,0,0,0,1,0,1,1,0,0,1,0,1,1,1,0,1,0,0,0,0,0,0,0,0]
theorem level27 :
    diag27.map (fun a => a.testBit 0)=AD (alt witness) 27 0 27 /\
    Theta witness 27=false := by
  have h := level (alt witness) 0 26 diag26 diag25 1
    level26.1 level25.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag26 (0 :: diag25)).1)=diag27 := by decide +kernel
  have hl : (scanN 1 diag26 (0 :: diag25)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag28 : List Nat := [0,1,0,1,0,0,0,1,1,0,1,0,0,1,1,0,1,0,1,0,0,0,0,0,0,0,0,0]
theorem level28 :
    diag28.map (fun a => a.testBit 0)=AD (alt witness) 28 0 28 /\
    Theta witness 28=false := by
  have h := level (alt witness) 0 27 diag27 diag26 0
    level27.1 level26.1 (by decide +kernel)
  have hc : (0 :: (scanN 0 diag27 (0 :: diag26)).1)=diag28 := by decide +kernel
  have hl : (scanN 0 diag27 (0 :: diag26)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag29 : List Nat := [1,1,0,0,1,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0]
theorem level29 :
    diag29.map (fun a => a.testBit 0)=AD (alt witness) 29 0 29 /\
    Theta witness 29=false := by
  have h := level (alt witness) 0 28 diag28 diag27 1
    level28.1 level27.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag28 (0 :: diag27)).1)=diag29 := by decide +kernel
  have hl : (scanN 1 diag28 (0 :: diag27)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag30 : List Nat := [0,1,0,1,1,0,1,0,1,0,1,1,0,1,0,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0]
theorem level30 :
    diag30.map (fun a => a.testBit 0)=AD (alt witness) 30 0 30 /\
    Theta witness 30=false := by
  have h := level (alt witness) 0 29 diag29 diag28 0
    level29.1 level28.1 (by decide +kernel)
  have hc : (0 :: (scanN 0 diag29 (0 :: diag28)).1)=diag30 := by decide +kernel
  have hl : (scanN 0 diag29 (0 :: diag28)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag31 : List Nat := [1,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,0,0,1,0,1,1,1,1,1,1,1,1,1,1]
theorem level31 :
    diag31.map (fun a => a.testBit 0)=AD (alt witness) 31 0 31 /\
    Theta witness 31=true := by
  have h := level (alt witness) 0 30 diag30 diag29 1
    level30.1 level29.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag30 (0 :: diag29)).1)=diag31 := by decide +kernel
  have hl : (scanN 1 diag30 (0 :: diag29)).2.testBit 0=true := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag32 : List Nat := [1,0,1,0,1,0,1,1,0,0,1,0,1,0,0,1,1,0,0,0,1,0,1,0,1,0,1,0,1,0,1,0]
theorem level32 :
    diag32.map (fun a => a.testBit 0)=AD (alt witness) 32 0 32 /\
    Theta witness 32=false := by
  have h := level (alt witness) 0 31 diag31 diag30 1
    level31.1 level30.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag31 (0 :: diag30)).1)=diag32 := by decide +kernel
  have hl : (scanN 1 diag31 (0 :: diag30)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag33 : List Nat := [1,0,1,0,0,1,1,0,1,0,0,1,0,1,0,0,1,0,1,1,1,0,0,1,0,1,0,1,0,1,0,1,0]
theorem level33 :
    diag33.map (fun a => a.testBit 0)=AD (alt witness) 33 0 33 /\
    Theta witness 33=false := by
  have h := level (alt witness) 0 32 diag32 diag31 1
    level32.1 level31.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag32 (0 :: diag31)).1)=diag33 := by decide +kernel
  have hl : (scanN 1 diag32 (0 :: diag31)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag34 : List Nat := [0,1,0,1,0,0,1,0,1,0,0,0,1,1,0,0,0,1,0,1,0,1,0,0,1,1,0,0,1,1,0,0,1,1]
theorem level34 :
    diag34.map (fun a => a.testBit 0)=AD (alt witness) 34 0 34 /\
    Theta witness 34=true := by
  have h := level (alt witness) 0 33 diag33 diag32 0
    level33.1 level32.1 (by decide +kernel)
  have hc : (0 :: (scanN 0 diag33 (0 :: diag32)).1)=diag34 := by decide +kernel
  have hl : (scanN 0 diag33 (0 :: diag32)).2.testBit 0=true := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag35 : List Nat := [1,1,0,0,1,1,1,0,1,0,1,1,1,0,1,0,0,0,1,1,0,1,0,0,0,1,0,1,1,0,1,0,0,1,0]
theorem level35 :
    diag35.map (fun a => a.testBit 0)=AD (alt witness) 35 0 35 /\
    Theta witness 35=false := by
  have h := level (alt witness) 0 34 diag34 diag33 1
    level34.1 level33.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag34 (0 :: diag33)).1)=diag35 := by decide +kernel
  have hl : (scanN 1 diag34 (0 :: diag33)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag36 : List Nat := [1,0,1,0,0,1,0,1,0,1,0,1,0,1,0,1,1,1,1,0,1,0,1,0,0,0,1,0,1,0,1,0,0,0,1,0]
theorem level36 :
    diag36.map (fun a => a.testBit 0)=AD (alt witness) 36 0 36 /\
    Theta witness 36=false := by
  have h := level (alt witness) 0 35 diag35 diag34 1
    level35.1 level34.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag35 (0 :: diag34)).1)=diag36 := by decide +kernel
  have hl : (scanN 1 diag35 (0 :: diag34)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag37 : List Nat := [1,0,1,0,0,0,1,0,1,1,0,0,1,0,1,1,0,1,0,1,0,1,1,0,0,0,0,1,1,0,1,0,1,1,1,0,0]
theorem level37 :
    diag37.map (fun a => a.testBit 0)=AD (alt witness) 37 0 37 /\
    Theta witness 37=false := by
  have h := level (alt witness) 0 36 diag36 diag35 1
    level36.1 level35.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag36 (0 :: diag35)).1)=diag37 := by decide +kernel
  have hl : (scanN 1 diag36 (0 :: diag35)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag38 : List Nat := [0,1,0,1,0,0,0,1,1,0,1,0,0,1,1,0,1,0,1,0,1,1,0,1,0,0,0,0,1,0,1,0,1,0,1,0,1,1]
theorem level38 :
    diag38.map (fun a => a.testBit 0)=AD (alt witness) 38 0 38 /\
    Theta witness 38=true := by
  have h := level (alt witness) 0 37 diag37 diag36 0
    level37.1 level36.1 (by decide +kernel)
  have hc : (0 :: (scanN 0 diag37 (0 :: diag36)).1)=diag38 := by decide +kernel
  have hl : (scanN 0 diag37 (0 :: diag36)).2.testBit 0=true := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag39 : List Nat := [1,1,0,0,1,1,1,1,0,1,0,1,1,1,0,1,0,1,1,0,0,1,0,1,0,0,0,0,0,1,0,1,0,1,0,1,0,1,0]
theorem level39 :
    diag39.map (fun a => a.testBit 0)=AD (alt witness) 39 0 39 /\
    Theta witness 39=false := by
  have h := level (alt witness) 0 38 diag38 diag37 1
    level38.1 level37.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag38 (0 :: diag37)).1)=diag39 := by decide +kernel
  have hl : (scanN 1 diag38 (0 :: diag37)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag40 : List Nat := [1,0,1,0,0,1,0,1,0,1,0,0,1,0,1,0,1,1,0,1,0,0,1,0,1,0,0,0,0,0,1,1,0,0,1,1,0,0,1,0]
theorem level40 :
    diag40.map (fun a => a.testBit 0)=AD (alt witness) 40 0 40 /\
    Theta witness 40=false := by
  have h := level (alt witness) 0 39 diag39 diag38 1
    level39.1 level38.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag39 (0 :: diag38)).1)=diag40 := by decide +kernel
  have hl : (scanN 1 diag39 (0 :: diag38)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag41 : List Nat := [1,0,1,0,0,0,1,0,1,0,1,0,0,1,0,1,1,0,1,0,1,1,1,0,0,1,1,1,1,1,1,0,1,0,0,1,0,1,1,0,0]
theorem level41 :
    diag41.map (fun a => a.testBit 0)=AD (alt witness) 41 0 41 /\
    Theta witness 41=false := by
  have h := level (alt witness) 0 40 diag40 diag39 1
    level40.1 level39.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag40 (0 :: diag39)).1)=diag41 := by decide +kernel
  have hl : (scanN 1 diag40 (0 :: diag39)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag42 : List Nat := [1,0,1,0,1,1,1,0,0,1,1,0,0,0,1,1,0,1,0,1,1,0,1,0,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,0]
theorem level42 :
    diag42.map (fun a => a.testBit 0)=AD (alt witness) 42 0 42 /\
    Theta witness 42=false := by
  have h := level (alt witness) 0 41 diag41 diag40 1
    level41.1 level40.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag41 (0 :: diag40)).1)=diag42 := by decide +kernel
  have hl : (scanN 1 diag41 (0 :: diag40)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag43 : List Nat := [1,0,1,0,1,0,1,0,1,1,0,1,0,0,0,1,0,1,0,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,0,0,0]
theorem level43 :
    diag43.map (fun a => a.testBit 0)=AD (alt witness) 43 0 43 /\
    Theta witness 43=false := by
  have h := level (alt witness) 0 42 diag42 diag41 1
    level42.1 level41.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag42 (0 :: diag41)).1)=diag43 := by decide +kernel
  have hl : (scanN 1 diag42 (0 :: diag41)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag44 : List Nat := [0,1,0,1,0,1,0,1,0,1,0,1,0,0,0,0,1,0,1,0,0,1,0,1,0,1,0,1,1,0,0,1,1,0,1,0,1,0,1,0,1,0,0,0]
theorem level44 :
    diag44.map (fun a => a.testBit 0)=AD (alt witness) 44 0 44 /\
    Theta witness 44=false := by
  have h := level (alt witness) 0 43 diag43 diag42 0
    level43.1 level42.1 (by decide +kernel)
  have hc : (0 :: (scanN 0 diag43 (0 :: diag42)).1)=diag44 := by decide +kernel
  have hl : (scanN 0 diag43 (0 :: diag42)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag45 : List Nat := [1,1,0,0,1,1,0,0,1,1,0,1,0,1,1,1,1,0,0,1,1,1,0,0,1,1,0,0,1,0,1,1,0,1,0,1,1,0,0,1,1,0,0,0,0]
theorem level45 :
    diag45.map (fun a => a.testBit 0)=AD (alt witness) 45 0 45 /\
    Theta witness 45=false := by
  have h := level (alt witness) 0 44 diag44 diag43 1
    level44.1 level43.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag44 (0 :: diag43)).1)=diag45 := by decide +kernel
  have hl : (scanN 1 diag44 (0 :: diag43)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag46 : List Nat := [1,0,1,0,0,1,0,1,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,1,0,1,0,0,1,0,1,0,1,0,0,1,0,1,1,0,1,0,0,0,0]
theorem level46 :
    diag46.map (fun a => a.testBit 0)=AD (alt witness) 46 0 46 /\
    Theta witness 46=false := by
  have h := level (alt witness) 0 45 diag45 diag44 1
    level45.1 level44.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag45 (0 :: diag44)).1)=diag46 := by decide +kernel
  have hl : (scanN 1 diag45 (0 :: diag44)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag47 : List Nat := [1,0,1,0,0,0,1,0,1,0,1,0,0,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,0,1,1,0,1,0,1,1,0,1,0,1,0,1,1,1,1,1]
theorem level47 :
    diag47.map (fun a => a.testBit 0)=AD (alt witness) 47 0 47 /\
    Theta witness 47=true := by
  have h := level (alt witness) 0 46 diag46 diag45 1
    level46.1 level45.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag46 (0 :: diag45)).1)=diag47 := by decide +kernel
  have hl : (scanN 1 diag46 (0 :: diag45)).2.testBit 0=true := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag48 : List Nat := [0,1,0,1,0,0,0,1,1,0,1,0,1,1,0,1,0,1,0,1,0,1,1,0,0,1,0,1,0,0,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0]
theorem level48 :
    diag48.map (fun a => a.testBit 0)=AD (alt witness) 48 0 48 /\
    Theta witness 48=false := by
  have h := level (alt witness) 0 47 diag47 diag46 0
    level47.1 level46.1 (by decide +kernel)
  have hc : (0 :: (scanN 0 diag47 (0 :: diag46)).1)=diag48 := by decide +kernel
  have hl : (scanN 0 diag47 (0 :: diag46)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag49 : List Nat := [1,1,0,0,1,1,1,1,0,1,0,1,0,1,0,1,0,0,1,1,0,0,1,0,1,1,0,0,1,1,1,1,0,1,0,1,0,1,0,0,1,1,0,1,0,1,0,1,0]
theorem level49 :
    diag49.map (fun a => a.testBit 0)=AD (alt witness) 49 0 49 /\
    Theta witness 49=false := by
  have h := level (alt witness) 0 48 diag48 diag47 1
    level48.1 level47.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag48 (0 :: diag47)).1)=diag49 := by decide +kernel
  have hl : (scanN 1 diag48 (0 :: diag47)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag50 : List Nat := [1,0,1,0,0,1,0,1,0,1,0,0,1,1,0,1,0,1,1,0,1,0,0,1,0,1,0,1,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0,0,1,1,0,0]
theorem level50 :
    diag50.map (fun a => a.testBit 0)=AD (alt witness) 50 0 50 /\
    Theta witness 50=false := by
  have h := level (alt witness) 0 49 diag49 diag48 1
    level49.1 level48.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag49 (0 :: diag48)).1)=diag50 := by decide +kernel
  have hl : (scanN 1 diag49 (0 :: diag48)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag51 : List Nat := [1,0,1,0,0,0,1,0,1,0,1,0,0,1,0,1,0,1,0,1,0,1,1,1,0,0,1,0,1,0,1,0,1,0,0,1,1,0,0,1,1,1,0,1,0,1,1,0,1,0,0]
theorem level51 :
    diag51.map (fun a => a.testBit 0)=AD (alt witness) 51 0 51 /\
    Theta witness 51=false := by
  have h := level (alt witness) 0 50 diag50 diag49 1
    level50.1 level49.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag50 (0 :: diag49)).1)=diag51 := by decide +kernel
  have hl : (scanN 1 diag50 (0 :: diag49)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag52 : List Nat := [0,1,0,1,0,0,0,1,1,0,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,0,1,1,0,1,0,1,0,1,1,0,1,0,0,1,0,1,0,1,0,1,0,1,0,0,0]
theorem level52 :
    diag52.map (fun a => a.testBit 0)=AD (alt witness) 52 0 52 /\
    Theta witness 52=false := by
  have h := level (alt witness) 0 51 diag51 diag50 0
    level51.1 level50.1 (by decide +kernel)
  have hc : (0 :: (scanN 0 diag51 (0 :: diag50)).1)=diag52 := by decide +kernel
  have hl : (scanN 0 diag51 (0 :: diag50)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag53 : List Nat := [1,1,0,0,1,1,1,1,0,1,0,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,0,0,1,0,1,1,0,0,1,0,1,0,0,0]
theorem level53 :
    diag53.map (fun a => a.testBit 0)=AD (alt witness) 53 0 53 /\
    Theta witness 53=false := by
  have h := level (alt witness) 0 52 diag52 diag51 1
    level52.1 level51.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag52 (0 :: diag51)).1)=diag53 := by decide +kernel
  have hl : (scanN 1 diag52 (0 :: diag51)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag54 : List Nat := [1,0,1,0,0,1,0,1,0,1,0,0,0,1,0,1,1,0,0,1,1,0,0,0,1,1,0,1,0,1,0,0,1,1,0,0,1,0,1,0,0,0,1,1,0,1,0,0,1,1,0,0,0,0]
theorem level54 :
    diag54.map (fun a => a.testBit 0)=AD (alt witness) 54 0 54 /\
    Theta witness 54=false := by
  have h := level (alt witness) 0 53 diag53 diag52 1
    level53.1 level52.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag53 (0 :: diag52)).1)=diag54 := by decide +kernel
  have hl : (scanN 1 diag53 (0 :: diag52)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag55 : List Nat := [1,0,1,0,0,0,1,0,1,0,1,0,0,0,1,1,0,1,0,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,1,0,0,1,1,1,1,0,1,0,1,1,1,0,1,0,0,0,0]
theorem level55 :
    diag55.map (fun a => a.testBit 0)=AD (alt witness) 55 0 55 /\
    Theta witness 55=false := by
  have h := level (alt witness) 0 54 diag54 diag53 1
    level54.1 level53.1 (by decide +kernel)
  have hc : (1 :: (scanN 1 diag54 (0 :: diag53)).1)=diag55 := by decide +kernel
  have hl : (scanN 1 diag54 (0 :: diag53)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

def diag56 : List Nat := [0,1,0,1,0,0,0,1,1,0,0,1,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,1,0,0,0,1,0,1,0,1,1,0,1,0,1,0,1,1,0,1,0,1,0,0,0,0,0]
theorem level56 :
    diag56.map (fun a => a.testBit 0)=AD (alt witness) 56 0 56 /\
    Theta witness 56=false := by
  have h := level (alt witness) 0 55 diag55 diag54 0
    level55.1 level54.1 (by decide +kernel)
  have hc : (0 :: (scanN 0 diag55 (0 :: diag54)).1)=diag56 := by decide +kernel
  have hl : (scanN 0 diag55 (0 :: diag54)).2.testBit 0=false := by decide +kernel
  constructor
  · rw [hc] at h; exact h.1
  · exact h.2.symm.trans hl

theorem zero_run_count : zeroRuns witness 28=12 := by decide +kernel

theorem spatial_black_count : blackCount (Theta witness) 57=11 := by
  simp only [blackCount,cell0,level1.2,level2.2,level3.2,level4.2,level5.2,level6.2,level7.2,level8.2,level9.2,level10.2,level11.2,level12.2,level13.2,level14.2,level15.2,level16.2,level17.2,level18.2,level19.2,level20.2,level21.2,level22.2,level23.2,level24.2,level25.2,level26.2,level27.2,level28.2,level29.2,level30.2,level31.2,level32.2,level33.2,level34.2,level35.2,level36.2,level37.2,level38.2,level39.2,level40.2,level41.2,level42.2,level43.2,level44.2,level45.2,level46.2,level47.2,level48.2,level49.2,level50.2,level51.2,level52.2,level53.2,level54.2,level55.2,level56.2]
  decide +kernel

theorem unrestricted_charge_false : Not ZeroRunSpatialCharge := by
  intro hc
  have h := hc witness 28
  rw [zero_run_count,spatial_black_count] at h
  omega

theorem witness_has_adjacent_zeros : witness 5=false /\ witness 6=false := by decide +kernel

end Rule30ZeroRunChargeCounterexampleResearch
