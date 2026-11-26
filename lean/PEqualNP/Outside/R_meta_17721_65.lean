import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_17721_65
    (caseA : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ x2 ∈ x1.gates, x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ (x3 x4 : List Bool), (∀ (x5 : ℕ), x3.getD x5 Bool.false = Bool.true → x4.getD x5 Bool.false = Bool.true) → x1.eval x3 = Bool.true → x1.eval x4 = Bool.true)
    (caseB : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), ¬(PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ x2 ∈ x1.gates, x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ (x3 x4 : List Bool), (∀ (x5 : ℕ), x3.getD x5 Bool.false = Bool.true → x4.getD x5 Bool.false = Bool.true) → x1.eval x3 = Bool.true → x1.eval x4 = Bool.true) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x2 ∈ x1.gates, x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ (x3 x4 : List Bool), (∀ (x5 : ℕ), x3.getD x5 Bool.false = Bool.true → x4.getD x5 Bool.false = Bool.true) → x1.eval x3 = Bool.true → x1.eval x4 = Bool.true := by
  intro x1
  by_cases h : (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and
  · exact @caseA x1 h
  · exact @caseB x1 h
