import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19141_aux

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership

theorem main_proof :
    ∀ (p : Fin 21 → Bool × Fin 32 × Fin 32) (m : ℕ → Bool),
      (∀ j, (p j).1 = true ∨ m (11 + j.val) = true → m (p j).2.1 = true ∧ m (p j).2.2 = true) →
      let C : Circuit := ⟨(List.ofFn p).map (fun g => ⟨if g.1 = true then .and else .or, [g.2.1.val, g.2.2.val]⟩), 31⟩
      ∀ i j : Fin 21, m (11 + i.val) = false → (p j).1 = true → ¬ InCone 11 C i.val j.val := by
  intro p m hm
  dsimp only
  let C : Circuit := ⟨(List.ofFn p).map (fun g => ⟨if g.1 = true then .and else .or, [g.2.1.val, g.2.2.val]⟩), 31⟩
  have hlenC : C.gates.length = 21 := by simp [C]
  have hgate : ∀ (k : ℕ) (hk : k < 21),
      (C.gates[k]'(by omega)).inputs = [(p ⟨k, hk⟩).2.1.val, (p ⟨k, hk⟩).2.2.val] := by
    intro k hk
    simp only [C, List.getElem_map, List.getElem_ofFn]
  have hinv : ∀ k (hk : k ≤ 21),
      let cs := (C.gates.take k).foldl (coneStep 11) []
      cs.length = k ∧
      ∀ (j : ℕ) (hj : j < k),
        ((p ⟨j, by omega⟩).1 = true ∨ m (11 + j) = true) →
        ∀ a ∈ cs.getD j [], m (11 + a) = true := by
    intro k hk
    induction k with
    | zero => exact ⟨rfl, fun j hj => by omega⟩
    | succ k ih =>
      obtain ⟨hlen, hall⟩ := ih (by omega)
      have hklt : k < C.gates.length := by omega
      have htake : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]] := List.take_succ_eq_append_getElem hklt
      set cs := (C.gates.take k).foldl (coneStep 11) []
      have hcs1 : (C.gates.take (k + 1)).foldl (coneStep 11) [] = coneStep 11 cs C.gates[k] := by
        rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
      dsimp only
      rw [hcs1]
      refine ⟨by simp [coneStep, hlen], ?_⟩
      intro j hj hor a ha
      by_cases hjk : j < k
      · rw [coneStep, List.getD_append cs _ [] j (by omega)] at ha
        exact hall j hjk hor a ha
      · have hjeq : j = k := by omega
        subst hjeq
        have hget : (coneStep 11 cs C.gates[j]).getD j [] =
            (C.gates[j].inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + cs.length))).flatMap
              (fun w => (w - 11) :: cs.getD (w - 11) []) := by
          rw [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
              show j - cs.length = 0 by omega]
          rfl
        rw [hget] at ha
        simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons] at ha
        rcases ha with ⟨w, ⟨hwin, hw1, hw2⟩, rfl | hmem⟩
        · rw [hgate j (by omega)] at hwin
          have hboth := hm ⟨j, by omega⟩ hor
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hwin
          have heq : 11 + (w - 11) = w := by omega
          rw [heq]
          rcases hwin with hw | hw
          · rw [hw]; exact hboth.1
          · rw [hw]; exact hboth.2
        · rw [hgate j (by omega)] at hwin
          have hboth := hm ⟨j, by omega⟩ hor
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hwin
          have hmw : m (11 + (w - 11)) = true := by
            have heq : 11 + (w - 11) = w := by omega
            rw [heq]
            rcases hwin with hw | hw
            · rw [hw]; exact hboth.1
            · rw [hw]; exact hboth.2
          exact hall (w - 11) (by omega) (Or.inr hmw) a hmem
  intro i j hmi hpj hcone
  have h21 := (hinv 21 (le_refl _)).2 j.val j.isLt (Or.inl hpj) i.val
  have htake21 : C.gates.take 21 = C.gates := List.take_of_length_le (by omega)
  rw [htake21] at h21
  have hmt : m (11 + i.val) = true := h21 hcone
  rw [hmi] at hmt
  cases hmt

end PEqualNP.Outside.L_meta_19141_aux

theorem PEqualNP.Outside.L_meta_19141 : (∀ (x1 : Fin (21 : ℕ) → Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) (x2 : ℕ → Bool),   (∀ (x3 : Fin (21 : ℕ)), (x1 x3).1 = Bool.true ∨ x2 ((11 : ℕ) + ↑x3) = Bool.true → x2 ↑(x1 x3).2.1 = Bool.true ∧ x2 ↑(x1 x3).2.2 = Bool.true) →     have x4 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.map (fun (x4 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => { op := if x4.1 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [↑x4.2.1, ↑x4.2.2] : PEqualNP.CircuitLowerBounds.Gate }) (List.ofFn x1), output := (31 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit };     ∀ (x5 x6 : Fin (21 : ℕ)), x2 ((11 : ℕ) + ↑x5) = Bool.false → (x1 x6).1 = Bool.true → ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x4 ↑x5 ↑x6)  := by
  exact PEqualNP.Outside.L_meta_19141_aux.main_proof
