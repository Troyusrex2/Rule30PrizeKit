import Rule30PrefixMonotoneRankObstructionResearch

/-! The same exact word cycle excludes a rank in any ordered value type.
The order laws are explicit hypotheses, so this statement covers integer,
rational and real-valued discovery models without importing Mathlib.
Physical realization is independently tested by the companion controls;
the bridge from those controls to official right dynamics is not formalized.
-/
namespace Rule30PrefixMonotoneOrderObstructionResearch
open Rule30PrefixMonotoneRankObstructionResearch

theorem no_prefix_monotone_order_rank {A : Type}
    (le lt : A -> A -> Prop)
    (trans : forall a b c, le a b -> le b c -> le a c)
    (strict : forall a b, lt a b -> Not (le b a))
    (E : Nat -> List Nat -> A)
    (hext : forall p xs tail, le (E p xs) (E p (xs++tail)))
    (h0 : lt (E 21 middleWord) (E 42 shortWord))
    (h1 : le (E 42 longWord) (E 21 middleWord)) : False := by
  have hp := hext 42 shortWord extension
  rw [<-long_eq] at hp
  exact strict _ _ h0 (trans _ _ _ hp h1)

end Rule30PrefixMonotoneOrderObstructionResearch
