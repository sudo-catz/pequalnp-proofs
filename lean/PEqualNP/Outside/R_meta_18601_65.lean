import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_18601_65
    (caseA : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), x1 < (50 : ℕ) → x2.IsBipartite → PEqualNP.TopForm.NoFourCycle x2 → (∀ (x7 : Finset (Fin x1)), x7.card ≤ (2 : ℕ) → (SimpleGraph.induce (↑x7)ᶜ x2).Connected) → (∃ (x8 : x2.Subgraph), x8.IsPerfectMatching) → ((2 : ℕ) * x2.edgeFinset.card - (3 : ℕ) * x1) ^ (3 : ℕ) ≤ x1 ^ (2 : ℕ) → PEqualNP.TopForm.IsAO2 x1 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x2.edgeFinset.card + x1 / (2 : ℕ) ≤ x4.size + (1 : ℕ) + x1.sqrt)
    (caseB : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), (50 : ℕ) ≤ x1 → x2.IsBipartite → PEqualNP.TopForm.NoFourCycle x2 → (∀ (x7 : Finset (Fin x1)), x7.card ≤ (2 : ℕ) → (SimpleGraph.induce (↑x7)ᶜ x2).Connected) → (∃ (x8 : x2.Subgraph), x8.IsPerfectMatching) → ((2 : ℕ) * x2.edgeFinset.card - (3 : ℕ) * x1) ^ (3 : ℕ) ≤ x1 ^ (2 : ℕ) → PEqualNP.TopForm.IsAO2 x1 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x2.edgeFinset.card + x1 / (2 : ℕ) ≤ x4.size + (1 : ℕ) + x1.sqrt) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2.IsBipartite → PEqualNP.TopForm.NoFourCycle x2 → (∀ (x7 : Finset (Fin x1)), x7.card ≤ (2 : ℕ) → (SimpleGraph.induce (↑x7)ᶜ x2).Connected) → (∃ (x8 : x2.Subgraph), x8.IsPerfectMatching) → ((2 : ℕ) * x2.edgeFinset.card - (3 : ℕ) * x1) ^ (3 : ℕ) ≤ x1 ^ (2 : ℕ) → PEqualNP.TopForm.IsAO2 x1 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x2.edgeFinset.card + x1 / (2 : ℕ) ≤ x4.size + (1 : ℕ) + x1.sqrt := by
  intro x1 x2 x3 x4
  rcases Nat.lt_or_ge x1 (50 : ℕ) with h | h
  · exact @caseA x1 x2 x3 x4 h
  · exact @caseB x1 x2 x3 x4 h
