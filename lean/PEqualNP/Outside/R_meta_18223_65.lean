import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18223_65
    (caseA : have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), x2 ∈ PEqualNP.HeptadCover.singerLines3 x3 ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true; ∀ (x2 : Fin (26 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 → (∀ (x5 : Fin (26 : ℕ) → Bool), x5 x2 = Bool.false → (x3.eval (List.ofFn x5) = Bool.true ↔ x1 x5)) → (59 : ℕ) ≤ x3.size)
    (caseB : have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), x2 ∈ PEqualNP.HeptadCover.singerLines3 x3 ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true; ∀ (x2 : Fin (26 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), ¬(PEqualNP.MetaComplexity.NestedCover.gateAt x3 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 → (∀ (x5 : Fin (26 : ℕ) → Bool), x5 x2 = Bool.false → (x3.eval (List.ofFn x5) = Bool.true ↔ x1 x5)) → (59 : ℕ) ≤ x3.size) :
    have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), x2 ∈ PEqualNP.HeptadCover.singerLines3 x3 ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true; ∀ (x2 : Fin (26 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 → (∀ (x5 : Fin (26 : ℕ) → Bool), x5 x2 = Bool.false → (x3.eval (List.ofFn x5) = Bool.true ↔ x1 x5)) → (59 : ℕ) ≤ x3.size := by
  intro x1 x2 x3
  by_cases h : (PEqualNP.MetaComplexity.NestedCover.gateAt x3 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and
  · exact @caseA x2 x3 h
  · exact @caseB x2 x3 h
