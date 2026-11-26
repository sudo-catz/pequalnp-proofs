import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18498_65
    (caseA : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), x1 < (50 : ℕ) → (∀ x5 ∉ x4, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x4) → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → ∀ (x9 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4) x9 → ∃ x11 ⊆ x4ᶜ, (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) ∧ x4.card + x2.edgeFinset.card + x11.card ≤ x9 + (1 : ℕ))
    (caseB : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), (50 : ℕ) ≤ x1 → (∀ x5 ∉ x4, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x4) → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → ∀ (x9 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4) x9 → ∃ x11 ⊆ x4ᶜ, (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) ∧ x4.card + x2.edgeFinset.card + x11.card ≤ x9 + (1 : ℕ)) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), (∀ x5 ∉ x4, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x4) → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → ∀ (x9 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4) x9 → ∃ x11 ⊆ x4ᶜ, (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) ∧ x4.card + x2.edgeFinset.card + x11.card ≤ x9 + (1 : ℕ) := by
  intro x1 x2 x3 x4
  rcases Nat.lt_or_ge x1 (50 : ℕ) with h | h
  · exact @caseA x1 x2 x3 x4 h
  · exact @caseB x1 x2 x3 x4 h
