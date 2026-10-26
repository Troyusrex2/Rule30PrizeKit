module
public import Rule30CubicOrbitSemantics
public import Rule30CubicOrbitCheck00
public import Rule30CubicOrbitCheck01
public import Rule30CubicOrbitCheck02
public import Rule30CubicOrbitCheck03
public import Rule30CubicOrbitCheck04
public import Rule30CubicOrbitCheck05
public import Rule30CubicOrbitCheck06
public import Rule30CubicOrbitCheck07
public import Rule30CubicOrbitCheck08
public import Rule30CubicOrbitCheck09
public import Rule30CubicMomentCheck00
public import Rule30CubicMomentCheck01
public import Rule30CubicMomentCheck02
public import Rule30CubicMomentCheck03
public import Rule30CubicMomentCheck04
public import Rule30CubicMomentCheck05
public import Rule30CubicMomentCheck06
public import Rule30CubicMomentCheck07
public import Rule30CubicMomentCheck08
public import Rule30CubicMomentCheck09
public import Rule30CubicMomentCheck10
public import Rule30CubicMomentCheck11
public import Rule30CubicMomentCheck12
public import Rule30CubicMomentCheck13
public import Rule30CubicMomentCheck14
public import Rule30CubicMomentCheck15
@[expose] public section
namespace Rule30CubicCertificateChecked
open Rule30CubicCertificateData
open Rule30ReaderCanonicalResearch
open Rule30CubicOrbitSemantics
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
def orbitGroups : List (List Orbit) := [(orbits.drop 0 |>.take 32),
(orbits.drop 32 |>.take 32),
(orbits.drop 64 |>.take 32),
(orbits.drop 96 |>.take 32),
(orbits.drop 128 |>.take 32),
(orbits.drop 160 |>.take 32),
(orbits.drop 192 |>.take 32),
(orbits.drop 224 |>.take 32),
(orbits.drop 256 |>.take 32),
(orbits.drop 288 |>.take 2)]
theorem orbitGroups_flatten : orbitGroups.flatten=orbits := by rfl
theorem all_orbits_checked : orbits.all checkOrbit=true := by
  rw [←orbitGroups_flatten,List.all_flatten]
  simp only [orbitGroups,List.all_cons,List.all_nil,Rule30CubicOrbitCheck00.checked,Rule30CubicOrbitCheck01.checked,Rule30CubicOrbitCheck02.checked,Rule30CubicOrbitCheck03.checked,Rule30CubicOrbitCheck04.checked,Rule30CubicOrbitCheck05.checked,Rule30CubicOrbitCheck06.checked,Rule30CubicOrbitCheck07.checked,Rule30CubicOrbitCheck08.checked,Rule30CubicOrbitCheck09.checked,Bool.and_self]
theorem all_moments_checked : (List.range 64).all (fun a =>
    (List.range (64-a)).all (fun j => !(moment a (a+j))))=true := by
  have hr : List.range 64=[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63] := rfl
  rw [hr]
  simp only [List.all_cons,List.all_nil,Nat.reduceSub,Rule30CubicMomentCheck00.row0,Rule30CubicMomentCheck00.row1,Rule30CubicMomentCheck00.row2,Rule30CubicMomentCheck00.row3,Rule30CubicMomentCheck01.row4,Rule30CubicMomentCheck01.row5,Rule30CubicMomentCheck01.row6,Rule30CubicMomentCheck01.row7,Rule30CubicMomentCheck02.row8,Rule30CubicMomentCheck02.row9,Rule30CubicMomentCheck02.row10,Rule30CubicMomentCheck02.row11,Rule30CubicMomentCheck03.row12,Rule30CubicMomentCheck03.row13,Rule30CubicMomentCheck03.row14,Rule30CubicMomentCheck03.row15,Rule30CubicMomentCheck04.row16,Rule30CubicMomentCheck04.row17,Rule30CubicMomentCheck04.row18,Rule30CubicMomentCheck04.row19,Rule30CubicMomentCheck05.row20,Rule30CubicMomentCheck05.row21,Rule30CubicMomentCheck05.row22,Rule30CubicMomentCheck05.row23,Rule30CubicMomentCheck06.row24,Rule30CubicMomentCheck06.row25,Rule30CubicMomentCheck06.row26,Rule30CubicMomentCheck06.row27,Rule30CubicMomentCheck07.row28,Rule30CubicMomentCheck07.row29,Rule30CubicMomentCheck07.row30,Rule30CubicMomentCheck07.row31,Rule30CubicMomentCheck08.row32,Rule30CubicMomentCheck08.row33,Rule30CubicMomentCheck08.row34,Rule30CubicMomentCheck08.row35,Rule30CubicMomentCheck09.row36,Rule30CubicMomentCheck09.row37,Rule30CubicMomentCheck09.row38,Rule30CubicMomentCheck09.row39,Rule30CubicMomentCheck10.row40,Rule30CubicMomentCheck10.row41,Rule30CubicMomentCheck10.row42,Rule30CubicMomentCheck10.row43,Rule30CubicMomentCheck11.row44,Rule30CubicMomentCheck11.row45,Rule30CubicMomentCheck11.row46,Rule30CubicMomentCheck11.row47,Rule30CubicMomentCheck12.row48,Rule30CubicMomentCheck12.row49,Rule30CubicMomentCheck12.row50,Rule30CubicMomentCheck12.row51,Rule30CubicMomentCheck13.row52,Rule30CubicMomentCheck13.row53,Rule30CubicMomentCheck13.row54,Rule30CubicMomentCheck13.row55,Rule30CubicMomentCheck14.row56,Rule30CubicMomentCheck14.row57,Rule30CubicMomentCheck14.row58,Rule30CubicMomentCheck14.row59,Rule30CubicMomentCheck15.row60,Rule30CubicMomentCheck15.row61,Rule30CubicMomentCheck15.row62,Rule30CubicMomentCheck15.row63,Bool.and_self]
theorem target_checked : target=true := by decide +kernel
theorem shape_checked : orbits.all (fun o =>
    (o.period==32 || o.period==64) &&
    (o.r<2^o.period) && (o.g<2^o.period))=true := by decide +kernel
theorem phase_count : orbits.foldl (fun n o => n+o.period) 0=18528 := by decide +kernel
theorem every_record_is_canonical_cycle (o : Orbit) (ho : o∈orbits) :
    Canonical (word o.initial width++[false]) ∧
    iter (word o.initial width) o.period=word o.initial width := by
  exact checked_orbit_is_actual_cycle o (List.all_eq_true.mp all_orbits_checked o ho)
end Rule30CubicCertificateChecked
