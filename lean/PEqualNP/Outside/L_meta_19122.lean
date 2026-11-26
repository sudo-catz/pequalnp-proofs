import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19122_aux
open PEqualNP.CircuitLowerBounds PEqualNP.Represents

theorem gL {n : ℕ} (u i : Fin n) (v : Fin n) :
    (oneEach u v).getD i false = decide (u = i) := by
  simp [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left, eq_comm]

theorem gR {n : ℕ} (u : Fin n) (v j : Fin n) :
    (oneEach u v).getD (n + j) false = decide (v = j) := by
  simp [oneEach, List.getD_eq_getElem?_getD, eq_comm]

end PEqualNP.Outside.L_meta_19122_aux

open PEqualNP.Outside.L_meta_19122_aux in
theorem PEqualNP.Outside.L_meta_19122 : ∀ (n : ℕ) (i j : Fin n), ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun u v : Fin n => xor (decide (u = i)) (decide (v = j))) C := by
  intro n i j
  refine ⟨⟨[⟨.or, [i, n + j]⟩, ⟨.and, [i, n + j]⟩, ⟨.not, [n + n + 1]⟩, ⟨.and, [n + n, n + n + 2]⟩],
    n + n + 3⟩, ?_, le_rfl, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · intro u v
    have hl : (PEqualNP.Represents.oneEach u v).length = n + n := by
      simp [PEqualNP.Represents.oneEach]
    have h1 := gL u i v
    have h2 := gR u v j
    generalize PEqualNP.Represents.oneEach u v = l at hl h1 h2
    have hi : (i : ℕ) < l.length := by omega
    have hj : n + (j : ℕ) < l.length := by omega
    rw [show n + n = l.length from hl.symm]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      List.foldl, List.map, List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hj, h1, h2]
    simp [List.getD_eq_getElem?_getD, PEqualNP.CircuitLowerBounds.GateOp.eval]
    cases decide (u = i) <;> cases decide (v = j) <;> rfl
