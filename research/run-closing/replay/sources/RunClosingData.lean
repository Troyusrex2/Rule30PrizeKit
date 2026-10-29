module
public import Std.Tactic
public import Ruliology.CellularAutomata.Rule30Prize
@[expose] public section
namespace RunClosing
-- Finite untrusted table, checked by kernel reduction in RunClosing.lean.
def records : List (Nat × Nat × Nat × Nat) := [(228, 0, 1, 2),
  (220, 1, 3, 4),
  (137, 0, 5, 6),
  (252, 1, 3, 4),
  (169, 2, 7, 8),
  (71, 1, 9, 10),
  (18, 0, 11, 12),
  (87, 4, 13, 14),
  (2, 3, 15, 16),
  (207, 1, 9, 10),
  (154, 2, 17, 18),
  (49, 1, 19, 20),
  (100, 0, 1, 2),
  (255, 5, 13, 14),
  (170, 5, 21, 22),
  (1, 1, 23, 24),
  (84, 1, 3, 4),
  (117, 4, 13, 14),
  (32, 3, 25, 26),
  (51, 1, 19, 20),
  (102, 2, 27, 28),
  (85, 5, 13, 14),
  (0, 5, 22, 21),
  (3, 1, 23, 24),
  (86, 2, 29, 30),
  (16, 1, 31, 32),
  (69, 1, 9, 10),
  (221, 4, 13, 14),
  (136, 3, 33, 34),
  (253, 4, 13, 14),
  (168, 3, 16, 15),
  (48, 1, 31, 32),
  (101, 2, 35, 36),
  (68, 1, 37, 38),
  (17, 1, 19, 20),
  (223, 4, 13, 14),
  (138, 3, 26, 25),
  (204, 1, 37, 38),
  (153, 2, 39, 40),
  (119, 4, 13, 14),
  (34, 3, 34, 33)]
theorem records_length : records.length=41 := by decide
end RunClosing
