import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_8027_65
    (caseA : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool), x1 < (50 : ℕ) → x2.Colorable (2 : ℕ) → (∀ (x5 : Fin x1), (x2.neighborSet x5).ncard = (0 : ℕ) ∨ (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → (∀ (x8 : Fin x1 → Bool), x3 x8 = Bool.true ↔ ∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) → ∀ (x9 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x9 → x2.edgeSet.ncard + x2.support.ncard / (2 : ℕ) ≤ x9 + (1 : ℕ))
    (caseB : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool), (50 : ℕ) ≤ x1 → x2.Colorable (2 : ℕ) → (∀ (x5 : Fin x1), (x2.neighborSet x5).ncard = (0 : ℕ) ∨ (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → (∀ (x8 : Fin x1 → Bool), x3 x8 = Bool.true ↔ ∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) → ∀ (x9 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x9 → x2.edgeSet.ncard + x2.support.ncard / (2 : ℕ) ≤ x9 + (1 : ℕ)) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool), x2.Colorable (2 : ℕ) → (∀ (x5 : Fin x1), (x2.neighborSet x5).ncard = (0 : ℕ) ∨ (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → (∀ (x8 : Fin x1 → Bool), x3 x8 = Bool.true ↔ ∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) → ∀ (x9 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x9 → x2.edgeSet.ncard + x2.support.ncard / (2 : ℕ) ≤ x9 + (1 : ℕ) := by
  intro x1 x2 x3
  rcases Nat.lt_or_ge x1 (50 : ℕ) with h | h
  · exact @caseA x1 x2 x3 h
  · exact @caseB x1 x2 x3 h
