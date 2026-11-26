import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_19026_65
    (caseA : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.HeptadCover.singerLines3 x1 → PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x1 (2 : ℕ) → (64 : ℕ) ≤ x1.size)
    (caseB : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), ¬(PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.HeptadCover.singerLines3 x1 → PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x1 (2 : ℕ) → (64 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.HeptadCover.singerLines3 x1 → PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x1 (2 : ℕ) → (64 : ℕ) ≤ x1.size := by
  intro x1
  by_cases h : (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and
  · exact @caseA x1 h
  · exact @caseB x1 h
