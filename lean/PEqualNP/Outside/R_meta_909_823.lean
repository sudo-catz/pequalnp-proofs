import PEqualNP.Defs

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_909_823 :
  (let rows : List ℕ → Finset (Finset (Fin 10)) := fun ms =>
    (ms.flatMap fun m => (List.finRange 4).flatMap fun a => (List.finRange 5).map fun b =>
      ((List.finRange 10).filter fun v : Fin 10 =>
        m.testBit (((a.val + 1) * (v.val % 5) + b.val) % 5 +
          5 * ((v.val / 5 + (if a.val = 1 ∨ a.val = 2 then 1 else 0)) % 2))).toFinset).toFinset
  ∃ K : PEqualNP.AndCount.AndCountCircuit 10, K.WellFormed ∧ K.size ≤ 6 ∧
    (∀ v : Fin 10, let readers : Finset (Fin K.size) := Finset.univ.filter (fun i =>
      v ∈ K.leftVars i ∨ v ∈ K.rightVars i)
     readers.card ≤ 2) ∧
    ∀ P ∈ rows [51,54,101,108], ∃ i : Fin K.size, K.gateVal P i = true ∧
      ∀ N ∈ rows [50,116], K.gateVal N i = false) →
  (let rows : List ℕ → Finset (Finset (Fin 10)) := fun ms =>
    (ms.flatMap fun m => (List.finRange 4).flatMap fun a => (List.finRange 5).map fun b =>
      ((List.finRange 10).filter fun v : Fin 10 =>
        m.testBit (((a.val + 1) * (v.val % 5) + b.val) % 5 +
          5 * ((v.val / 5 + (if a.val = 1 ∨ a.val = 2 then 1 else 0)) % 2))).toFinset).toFinset
  let H : SimpleGraph (Fin 10) := SimpleGraph.fromRel (fun a b : Fin 10 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (ℕ × ℕ)))
  ∀ I : Finset (Fin 10), (∀ a ∈ I, ∀ c ∈ I, ¬ H.Adj a c) →
    (∀ w : Fin 10, w ∉ I → ∃ a ∈ I, H.Adj a w) →
    I ∈ rows [50,116] ∧ ∀ w : Fin 10, w ∉ I →
      ∃ P ∈ rows [51,54,101,108], P ⊆ insert w I) →
  ∀ G : SimpleGraph (Fin 10), G = SimpleGraph.fromRel (fun a b : Fin 10 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (ℕ × ℕ))) →
  ∃ C : PEqualNP.AndCount.AndCountCircuit 10, C.WellFormed ∧ C.size ≤ 6 ∧
    (∀ v : Fin 10, (Finset.univ.filter (fun i : Fin C.size => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)).card ≤ 2) ∧
    (∀ I : Finset (Fin 10), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 10, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 10, w ∉ I → C.eval (insert w I) = true) := by
  intro search coverage G hG
  subst G
  let rows : List ℕ → Finset (Finset (Fin 10)) := fun ms =>
    (ms.flatMap fun m => (List.finRange 4).flatMap fun a => (List.finRange 5).map fun b =>
      ((List.finRange 10).filter fun v : Fin 10 =>
        m.testBit (((a.val + 1) * (v.val % 5) + b.val) % 5 +
          5 * ((v.val / 5 + (if a.val = 1 ∨ a.val = 2 then 1 else 0)) % 2))).toFinset).toFinset
  change ∃ K : PEqualNP.AndCount.AndCountCircuit 10, K.WellFormed ∧ K.size ≤ 6 ∧
    (∀ v : Fin 10, let readers : Finset (Fin K.size) := Finset.univ.filter (fun i =>
      v ∈ K.leftVars i ∨ v ∈ K.rightVars i)
     readers.card ≤ 2) ∧
    ∀ P ∈ rows [51,54,101,108], ∃ i : Fin K.size, K.gateVal P i = true ∧
      ∀ N ∈ rows [50,116], K.gateVal N i = false at search
  obtain ⟨K, wf, bound, reads, accepted⟩ := search
  let safe : Finset (Fin K.size) := Finset.univ.filter fun i =>
    ∀ N ∈ rows [50,116], K.gateVal N i = false
  let C : PEqualNP.AndCount.AndCountCircuit 10 := { K with outVars := ∅, outGates := safe }
  have same (S : Finset (Fin 10)) (d : ℕ) :
      ∀ i : Fin K.size, C.gateValFuel S d i = K.gateValFuel S d i := by
    induction d with
    | zero => intro i; rfl
    | succ d ih =>
      intro i
      exact congrArg (fun f : Fin K.size → Bool =>
        PEqualNP.AndCount.AndCountCircuit.sideTrue S (K.leftVars i) (K.leftGates i) i f &&
        PEqualNP.AndCount.AndCountCircuit.sideTrue S (K.rightVars i) (K.rightGates i) i f) (funext ih)
  have output (S : Finset (Fin 10)) :
      C.eval S = true ↔ ∃ i ∈ safe, K.gateVal S i = true := by
    change decide ((∃ v ∈ (∅ : Finset (Fin 10)), v ∈ S) ∨
      ∃ i ∈ safe, C.gateValFuel S K.size i = true) = true ↔
      ∃ i ∈ safe, K.gateValFuel S K.size i = true
    simp [same S K.size]
  have grows (S T : Finset (Fin 10)) (sub : S ⊆ T) (d : ℕ) :
      ∀ i, K.gateValFuel S d i = true → K.gateValFuel T d i = true := by
    induction d with
    | zero =>
      intro i h
      change false = true at h
      contradiction
    | succ d ih =>
      intro i h
      change (PEqualNP.AndCount.AndCountCircuit.sideTrue S (K.leftVars i) (K.leftGates i) i (K.gateValFuel S d) &&
        PEqualNP.AndCount.AndCountCircuit.sideTrue S (K.rightVars i) (K.rightGates i) i (K.gateValFuel S d)) = true at h
      change (PEqualNP.AndCount.AndCountCircuit.sideTrue T (K.leftVars i) (K.leftGates i) i (K.gateValFuel T d) &&
        PEqualNP.AndCount.AndCountCircuit.sideTrue T (K.rightVars i) (K.rightGates i) i (K.gateValFuel T d)) = true
      rw [Bool.and_eq_true] at h ⊢
      have side (B : Finset (Fin 10)) (F : Finset (Fin K.size)) :
          PEqualNP.AndCount.AndCountCircuit.sideTrue S B F i (K.gateValFuel S d) = true →
          PEqualNP.AndCount.AndCountCircuit.sideTrue T B F i (K.gateValFuel T d) = true := by
        change decide ((∃ v ∈ B, v ∈ S) ∨ ∃ j ∈ F, j < i ∧ K.gateValFuel S d j = true) = true →
          decide ((∃ v ∈ B, v ∈ T) ∨ ∃ j ∈ F, j < i ∧ K.gateValFuel T d j = true) = true
        simp only [decide_eq_true_eq]
        rintro (⟨v, hv, mem⟩ | ⟨j, hj, lt, on⟩)
        · exact Or.inl ⟨v, hv, sub mem⟩
        · exact Or.inr ⟨j, hj, lt, ih j on⟩
      exact ⟨side _ _ h.1, side _ _ h.2⟩
  refine ⟨C, wf, bound, reads, ?_⟩
  intro I independent maximal
  obtain ⟨hneg, hpos⟩ := coverage I independent maximal
  constructor
  · cases hx : C.eval I with
    | false => rfl
    | true =>
      obtain ⟨i, hi, on⟩ := (output I).mp hx
      have off := (Finset.mem_filter.mp hi).2 I hneg
      simp [off] at on
  · intro w hw
    obtain ⟨P, hp, sub⟩ := hpos w hw
    obtain ⟨i, on, off⟩ := accepted P hp
    exact (output _).mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, off⟩,
      grows P _ sub K.size i on⟩
