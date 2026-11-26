import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.R_meta_17243_1
    (oneGenerated : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2.length = (1 : ℕ) → (∀ w ∈ x2, (26 : ℕ) ≤ w ∧ w < (26 : ℕ) + x1.size) →       (let x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => (↑x5 + ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];         have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);         have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x7 : Finset (Fin (13 : ℕ))) => {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, ¬x5 x9 x8};         have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 x9 : Finset (Fin (13 : ℕ))) => PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => (x1.wires (List.ofFn (x6 x8 x9))).getD x10 Bool.false) x2);         (∀ (x9 x10 : Fin (13 : ℕ)), x5 x9 x10 → x8 {x9} {x10} = Bool.true) ∧ ∀ (x9 : Finset (Fin (13 : ℕ))), x9.card ≤ (3 : ℕ) → x8 x9 (x7 x9) = Bool.false ∧ x8 (x7 x9) x9 = Bool.false) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → (63 : ℕ) ≤ x1.size)
    (twoGenerated : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2.length = (2 : ℕ) → x2.Nodup → (∀ w ∈ x2, (26 : ℕ) ≤ w ∧ w < (26 : ℕ) + x1.size) →       (let x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => (↑x5 + ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];         have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);         have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x7 : Finset (Fin (13 : ℕ))) => {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, ¬x5 x9 x8};         have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 x9 : Finset (Fin (13 : ℕ))) => PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => (x1.wires (List.ofFn (x6 x8 x9))).getD x10 Bool.false) x2);         (∀ (x9 x10 : Fin (13 : ℕ)), x5 x9 x10 → x8 {x9} {x10} = Bool.true) ∧ ∀ (x9 : Finset (Fin (13 : ℕ))), x9.card ≤ (3 : ℕ) → x8 x9 (x7 x9) = Bool.false ∧ x8 (x7 x9) x9 = Bool.false) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → (63 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2.length ≤ (2 : ℕ) →       (let x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => (↑x5 + ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];         have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);         have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x7 : Finset (Fin (13 : ℕ))) => {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, ¬x5 x9 x8};         have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 x9 : Finset (Fin (13 : ℕ))) => PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => (x1.wires (List.ofFn (x6 x8 x9))).getD x10 Bool.false) x2);         (∀ (x9 x10 : Fin (13 : ℕ)), x5 x9 x10 → x8 {x9} {x10} = Bool.true) ∧ ∀ (x9 : Finset (Fin (13 : ℕ))), x9.card ≤ (3 : ℕ) → x8 x9 (x7 x9) = Bool.false ∧ x8 (x7 x9) x9 = Bool.false) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → (63 : ℕ) ≤ x1.size := by
  intro C outputs hmon hlength hspec hlast
  let edge (p l : Fin 13) : Prop := (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
  let input (P L : Finset (Fin 13)) (i : Fin 26) : Bool :=
    if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ P)
    else decide (Fin.ofNat 13 i.val ∈ L)
  let avoid (P : Finset (Fin 13)) : Finset (Fin 13) := {l | ∀ p ∈ P, ¬ edge p l}
  let wire (P L : Finset (Fin 13)) (i : ℕ) : Bool :=
    (C.wires (List.ofFn (input P L))).getD i false
  let scan (rs : List ℕ) (P L : Finset (Fin 13)) : Bool :=
    (rs.map (wire P L)).any id
  have hs : (∀ (p l : Fin 13), edge p l → scan outputs {p} {l} = true) ∧
      ∀ P : Finset (Fin 13), P.card ≤ 3 →
        scan outputs P (avoid P) = false ∧ scan outputs (avoid P) P = false := hspec
  let appendGate (ws : List Bool) (g : Gate) : List Bool :=
    ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  have preserveInputs : ∀ (gs : List Gate) (ws : List Bool) (i : ℕ), i < ws.length →
      (gs.foldl appendGate ws).getD i false = ws.getD i false := by
    intro gs
    induction gs with
    | nil => intros; rfl
    | cons g gs ih =>
      intro ws i hi
      rw [List.foldl_cons, ih]
      · exact List.getD_append _ _ _ _ hi
      · simp [appendGate]; omega
  have wire_length : ∀ (gs : List Gate) (ws : List Bool),
      (gs.foldl appendGate ws).length = ws.length + gs.length := by
    intro gs
    induction gs with
    | nil => intros; simp
    | cons g gs ih =>
      intro ws
      rw [List.foldl_cons, ih]
      simp [appendGate]
      omega
  have primary (P L : Finset (Fin 13)) (i : ℕ) (hi : i < 26) :
      wire P L i = input P L ⟨i, hi⟩ := by
    change (C.gates.foldl appendGate (List.ofFn (input P L))).getD i false = _
    rw [preserveInputs _ _ _ (by simpa using hi)]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi)]
    simp only [List.getElem_ofFn]
  have missing (P L : Finset (Fin 13)) (i : ℕ) (hi : 26 + C.size ≤ i) :
      wire P L i = false := by
    change (C.gates.foldl appendGate (List.ofFn (input P L))).getD i false = false
    apply List.getD_eq_default
    change 26 + C.gates.length ≤ i at hi
    simpa only [wire_length, List.length_ofFn] using hi
  have scan_true (rs : List ℕ) (P L : Finset (Fin 13)) :
      scan rs P L = true ↔ ∃ i ∈ rs, wire P L i = true := by
    simp [scan, List.any_eq_true]
  have zerorows : scan outputs ∅ Finset.univ = false ∧
      scan outputs Finset.univ ∅ = false := by
    simpa [avoid] using hs.2 ∅ (by simp)
  have nonprimary (i : ℕ) (hi : i ∈ outputs) : 26 ≤ i := by
    by_contra h
    have hi26 : i < 26 := Nat.lt_of_not_ge h
    by_cases hp : i < 13
    · have ht : wire Finset.univ ∅ i = true := by
        rw [primary _ _ _ hi26]
        simp [input, hp]
      have hv := (scan_true _ _ _).2 ⟨i, hi, ht⟩
      exact Bool.false_ne_true (zerorows.2.symm.trans hv)
    · have ht : wire ∅ Finset.univ i = true := by
        rw [primary _ _ _ hi26]
        simp [input, hp]
      have hv := (scan_true _ _ _).2 ⟨i, hi, ht⟩
      exact Bool.false_ne_true (zerorows.1.symm.trans hv)
  let filtered := outputs.filter fun i => decide (i < 26 + C.size)
  let selected := filtered.dedup
  have mem_selected (i : ℕ) : i ∈ selected ↔ i ∈ outputs ∧ i < 26 + C.size := by
    simp [selected, filtered]
  have valid (i : ℕ) (hi : i ∈ selected) : 26 ≤ i ∧ i < 26 + C.size := by
    obtain ⟨hm, hv⟩ := (mem_selected i).1 hi
    exact ⟨nonprimary i hm, hv⟩
  have replay (P L : Finset (Fin 13)) : scan selected P L = scan outputs P L := by
    apply Bool.eq_iff_iff.2
    rw [scan_true, scan_true]
    constructor
    · rintro ⟨i, hi, hv⟩
      exact ⟨i, ((mem_selected i).1 hi).1, hv⟩
    · rintro ⟨i, hi, hv⟩
      have hirange : i < 26 + C.size := by
        by_contra h
        exact Bool.false_ne_true ((missing P L i (Nat.le_of_not_gt h)).symm.trans hv)
      exact ⟨i, (mem_selected i).2 ⟨hi, hirange⟩, hv⟩
  have normalized_spec : (∀ (p l : Fin 13), edge p l → scan selected {p} {l} = true) ∧
      ∀ P : Finset (Fin 13), P.card ≤ 3 →
        scan selected P (avoid P) = false ∧ scan selected (avoid P) P = false := by
    constructor
    · intro p l he
      rw [replay]
      exact hs.1 p l he
    · intro P hP
      simp only [replay]
      exact hs.2 P hP
  have hcap : selected.length ≤ 2 :=
    (List.dedup_sublist filtered).length_le.trans ((List.length_filter_le _ _).trans hlength)
  have hnonempty : 1 ≤ selected.length := by
    obtain ⟨i, hi, _⟩ := (scan_true selected _ _).1 (normalized_spec.1 0 0 (by decide))
    exact List.length_pos_of_mem hi
  by_cases hsingle : selected.length = 1
  · exact oneGenerated C selected hmon hsingle valid normalized_spec hlast
  · exact twoGenerated C selected hmon (by omega) (List.nodup_dedup _) valid normalized_spec hlast
