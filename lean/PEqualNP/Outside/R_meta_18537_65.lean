import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_18537_65
    (caseA : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], x1 < (50 : ℕ) → (∀ (x4 : Fin x1), (x2.neighborSet x4).ncard = (0 : ℕ) ∨ (x2.neighborSet x4).ncard = (3 : ℕ)) → (∀ (x5 : Fin x1) (x6 : x2.Walk x5 x5), x6.IsCycle → (7 : ℕ) ≤ x6.length) → (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) → (∀ (x7 x8 : Fin x1), (∃ (x9 : Fin x1), x2.Adj x7 x9) → (∃ (x10 : Fin x1), x2.Adj x8 x10) → x2.Reachable x7 x8) → ∀ (x8 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x8 → PEqualNP.BicliqueBlockCost.HasBlockCost x2 x8)
    (caseB : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (50 : ℕ) ≤ x1 → (∀ (x4 : Fin x1), (x2.neighborSet x4).ncard = (0 : ℕ) ∨ (x2.neighborSet x4).ncard = (3 : ℕ)) → (∀ (x5 : Fin x1) (x6 : x2.Walk x5 x5), x6.IsCycle → (7 : ℕ) ≤ x6.length) → (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) → (∀ (x7 x8 : Fin x1), (∃ (x9 : Fin x1), x2.Adj x7 x9) → (∃ (x10 : Fin x1), x2.Adj x8 x10) → x2.Reachable x7 x8) → ∀ (x8 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x8 → PEqualNP.BicliqueBlockCost.HasBlockCost x2 x8) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 : Fin x1), (x2.neighborSet x4).ncard = (0 : ℕ) ∨ (x2.neighborSet x4).ncard = (3 : ℕ)) → (∀ (x5 : Fin x1) (x6 : x2.Walk x5 x5), x6.IsCycle → (7 : ℕ) ≤ x6.length) → (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) → (∀ (x7 x8 : Fin x1), (∃ (x9 : Fin x1), x2.Adj x7 x9) → (∃ (x10 : Fin x1), x2.Adj x8 x10) → x2.Reachable x7 x8) → ∀ (x8 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x8 → PEqualNP.BicliqueBlockCost.HasBlockCost x2 x8 := by
  intro x1 x2 x3
  rcases Nat.lt_or_ge x1 (50 : ℕ) with h | h
  · exact @caseA x1 x2 x3 h
  · exact @caseB x1 x2 x3 h
