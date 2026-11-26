import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5176_263
    (nestedClean :
      let G := PEqualNP.EdgeOwnership.edgeGraph 26
        ((List.finRange 13).flatMap fun l : Fin 13 =>
          [(l.val, 13 + l.val), ((l + 1).val, 13 + l.val),
           ((l + 3).val, 13 + l.val), ((l + 9).val, 13 + l.val)])
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        63 ≤ C.size → C.size ≤ 64 →
        PEqualNP.TopForm.IsAO2 26 C →
        (∀ g ∈ C.gates, g.inputs.Nodup) →
        PEqualNP.MetaComplexity.circuitFun 26 C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        ¬ PEqualNP.ReadK.IsSingleRead C 26 (fun i => decide (13 ≤ i)) [(0, 13)] →
        (∃ h, PEqualNP.Core.InOutputCone 26 C h ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C h).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          PEqualNP.EdgeOwnership.gateVal 26 C h (PEqualNP.EdgeOwnership.pairInput 0 13) = true ∧
          PEqualNP.EdgeOwnership.gateVal 26 C h (PEqualNP.EdgeOwnership.pairInput 0 0) = false ∧
          PEqualNP.EdgeOwnership.gateVal 26 C h (PEqualNP.EdgeOwnership.pairInput 13 13) = false ∧
          ¬ PEqualNP.ReadK.IsSingleRead (PEqualNP.Core.atGate 26 C h) 26 (fun i => decide (13 ≤ i)) [(0, 13)] ∧
          ∃ i ∈ PEqualNP.TopForm.tops G C,
            PEqualNP.EdgeOwnership.InCone 26 C i h ∧
            PEqualNP.EdgeOwnership.gateVal 26 C i (PEqualNP.EdgeOwnership.pairInput 0 13) = true) →
        False)
    (nestedJunk :
      let G := PEqualNP.EdgeOwnership.edgeGraph 26
        ((List.finRange 13).flatMap fun l : Fin 13 =>
          [(l.val, 13 + l.val), ((l + 1).val, 13 + l.val),
           ((l + 3).val, 13 + l.val), ((l + 9).val, 13 + l.val)])
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        63 ≤ C.size → C.size ≤ 64 →
        PEqualNP.TopForm.IsAO2 26 C →
        (∀ g ∈ C.gates, g.inputs.Nodup) →
        PEqualNP.MetaComplexity.circuitFun 26 C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        ¬ PEqualNP.ReadK.IsSingleRead C 26 (fun i => decide (13 ≤ i)) [(0, 13)] →
        (∃ h ∈ PEqualNP.TopForm.junk G C,
          PEqualNP.Core.InOutputCone 26 C h ∧
          PEqualNP.EdgeOwnership.gateVal 26 C h (PEqualNP.EdgeOwnership.pairInput 0 13) = true ∧
          PEqualNP.EdgeOwnership.gateVal 26 C h (PEqualNP.EdgeOwnership.pairInput 0 0) = false ∧
          PEqualNP.EdgeOwnership.gateVal 26 C h (PEqualNP.EdgeOwnership.pairInput 13 13) = false ∧
          ¬ PEqualNP.ReadK.IsSingleRead (PEqualNP.Core.atGate 26 C h) 26 (fun i => decide (13 ≤ i)) [(0, 13)] ∧
          (∀ i ∈ PEqualNP.TopForm.tops G C, PEqualNP.EdgeOwnership.InCone 26 C i h →
            PEqualNP.EdgeOwnership.gateVal 26 C i (PEqualNP.EdgeOwnership.pairInput 0 13) = false) ∧
          ∃ i ∈ PEqualNP.TopForm.junk G C,
            PEqualNP.EdgeOwnership.InCone 26 C i h ∧
            PEqualNP.EdgeOwnership.gateVal 26 C i (PEqualNP.EdgeOwnership.pairInput 0 13) = true) →
        False)
    (cleanAboveTwoJunk :
      let G := PEqualNP.EdgeOwnership.edgeGraph 26
        ((List.finRange 13).flatMap fun l : Fin 13 =>
          [(l.val, 13 + l.val), ((l + 1).val, 13 + l.val),
           ((l + 3).val, 13 + l.val), ((l + 9).val, 13 + l.val)])
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        63 ≤ C.size → C.size ≤ 64 →
        PEqualNP.TopForm.IsAO2 26 C →
        (∀ g ∈ C.gates, g.inputs.Nodup) →
        PEqualNP.MetaComplexity.circuitFun 26 C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        ¬ PEqualNP.ReadK.IsSingleRead C 26 (fun i => decide (13 ≤ i)) [(0, 13)] →
        (∃ h ∈ PEqualNP.TopForm.tops G C,
          PEqualNP.Core.InOutputCone 26 C h ∧
          PEqualNP.EdgeOwnership.gateVal 26 C h (PEqualNP.EdgeOwnership.pairInput 0 13) = true ∧
          ¬ PEqualNP.ReadK.IsSingleRead (PEqualNP.Core.atGate 26 C h) 26 (fun i => decide (13 ≤ i)) [(0, 13)] ∧
          (∀ i ∈ PEqualNP.TopForm.tops G C, PEqualNP.EdgeOwnership.InCone 26 C i h →
            PEqualNP.EdgeOwnership.gateVal 26 C i (PEqualNP.EdgeOwnership.pairInput 0 13) = false) ∧
          ∃ i1 ∈ PEqualNP.TopForm.junk G C, ∃ i2 ∈ PEqualNP.TopForm.junk G C,
            i1 ≠ i2 ∧
            PEqualNP.EdgeOwnership.InCone 26 C i1 h ∧
            PEqualNP.EdgeOwnership.InCone 26 C i2 h ∧
            PEqualNP.EdgeOwnership.gateVal 26 C i1 (PEqualNP.EdgeOwnership.pairInput 0 13) = true ∧
            PEqualNP.EdgeOwnership.gateVal 26 C i2 (PEqualNP.EdgeOwnership.pairInput 0 13) = true) →
        False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (63 : ℕ) ≤ x1.size →     x1.size ≤ (64 : ℕ) →       PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →         (∀ x5 ∈ x1.gates, x5.inputs.Nodup) →           (∀ (x6 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) →             have x7 : ℕ → ℕ → Bool := fun (x7 x8 : ℕ) => (x1.wires (List.ofFn fun (x9 : Fin (26 : ℕ)) => x7.testBit ↑x9)).getD x8 Bool.false;             ∃ x8 ∈ [(0 : ℕ), (13 : ℕ)],               have x9 : ℕ := if x8 = (0 : ℕ) then (25034751 : ℕ) else (67108341 : ℕ);               have x10 : ℕ := if x8 = (0 : ℕ) then (8191 : ℕ) else (67100672 : ℕ);               have x11 : ℕ := if x8 = (0 : ℕ) then (25018369 : ℕ) else (15860 : ℕ);               ∀ (x12 : Set ℕ), x1.output ∈ x12 → (∀ (x14 : Fin (26 : ℕ)), ↑x14 ∈ x12 → x9.testBit ↑x14 = Bool.false) → ¬∀ (x15 : ℕ) (x16 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x15]? = Option.some x16 → (26 : ℕ) + x15 ∈ x12 → (x16.op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ x20 ∈ x16.inputs, x20 ∈ x12) ∧ (x16.op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ x20 ∈ x16.inputs, x20 ∈ x12) ∨ (∀ x20 ∈ x16.inputs, x7 ((2 : ℕ) ^ x8) x20 = Bool.false) ∧ x7 x10 ((26 : ℕ) + x15) = Bool.false ∧ x7 x11 ((26 : ℕ) + x15) = Bool.false) := by
  classical
  dsimp only
  intro C h63 h64 hAO hNodup hSpec0
  let dGate : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩
  let pgAdj : Fin 13 → Fin 13 → Prop := fun p l => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
  let pgFun : (Fin 26 → Bool) → Bool := fun z =>
    decide (∃ p l : Fin 13, pgAdj p l ∧
      z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true)
  let maskVec : ℕ → Fin 26 → Bool := fun m i => m.testBit i.val
  let wireStep : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let wval : (Fin 26 → Bool) → ℕ → Bool := fun x k => (C.wires (List.ofFn x)).getD k false
  let maskWval : ℕ → ℕ → Bool := fun m k => wval (maskVec m) k
  have hSpec : ∀ z : Fin 26 → Bool, C.eval (List.ofFn z) = true ↔ pgFun z = true := by
    intro z
    dsimp only [pgFun, pgAdj]
    rw [decide_eq_true_eq]
    exact hSpec0 z
  have pgFun_e0 : pgFun (maskVec 8193) = true := by decide
  have foldl_wireStep_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : List Bool),
      (gs.foldl wireStep u).length = u.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro u; rfl
    | cons g gs ih =>
      intro u; rw [List.foldl_cons, ih]; simp [wireStep]; omega
  have foldl_wireStep_prefix : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : List Bool) (i : ℕ),
      i < u.length → (gs.foldl wireStep u).getD i false = u.getD i false := by
    intro gs
    induction gs with
    | nil => intro u i _; rfl
    | cons g gs ih =>
      intro u i hi
      rw [List.foldl_cons, ih]
      · dsimp only [wireStep]; rw [List.getD_append _ _ _ _ hi]
      · simp [wireStep]; omega
  have foldl_wireStep_take : ∀ (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : List Bool) (i : ℕ),
      i < u.length + (gs.take n).length →
      ((gs.take n).foldl wireStep u).getD i false = (gs.foldl wireStep u).getD i false := by
    intro n gs u i hi
    conv_rhs =>
      rw [← List.take_append_drop n gs, List.foldl_append,
        foldl_wireStep_prefix _ _ _ (by rw [foldl_wireStep_len]; exact hi)]
  have wval_input : ∀ (x : Fin 26 → Bool) (i : ℕ) (hi : i < 26), wval x i = x ⟨i, hi⟩ := by
    intro x i hi
    change (C.gates.foldl wireStep (List.ofFn x)).getD i false = x ⟨i, hi⟩
    rw [foldl_wireStep_prefix _ _ _ (by simp [hi])]
    rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]
  have list_len2 : ∀ l : List ℕ, l.length = 2 → l = [l.getD 0 0, l.getD 1 0] := by
    intro l hl
    cases l with
    | nil => simp at hl
    | cons a xs =>
      cases xs with
      | nil => simp at hl
      | cons b ys =>
        cases ys with
        | nil => rfl
        | cons c zs => simp at hl
  have wval_gate : ∀ (x : Fin 26 → Bool) (j : ℕ), j < C.gates.length →
      let g := C.gates.getD j dGate
      let a := g.inputs.getD 0 0
      let b := g.inputs.getD 1 0
      wval x (26 + j) = g.op.eval [wval x a, wval x b] := by
    intro x j hj
    dsimp only
    have hgMem : C.gates.getD j dGate ∈ C.gates := by
      rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
    have hgEq := list_len2 _ (hAO.2.2 _ hgMem)
    have haLt : (C.gates.getD j dGate).inputs.getD 0 0 < 26 + j :=
      hAO.2.1 j hj _ (by change _ ∈ (C.gates.getD j dGate).inputs; rw [hgEq]; simp)
    have hbLt : (C.gates.getD j dGate).inputs.getD 1 0 < 26 + j :=
      hAO.2.1 j hj _ (by change _ ∈ (C.gates.getD j dGate).inputs; rw [hgEq]; simp)
    let y := List.ofFn x
    have hyLen : y.length = 26 := by simp [y]
    have hd : C.gates.drop j = C.gates.getD j dGate :: C.gates.drop (j + 1) := by
      rw [← List.getElem_cons_drop hj, List.getD_eq_getElem _ _ hj]
    have hpreLen : ((C.gates.take j).foldl wireStep y).length = 26 + j := by
      rw [foldl_wireStep_len, hyLen, List.length_take]; omega
    have hstepLen : (wireStep ((C.gates.take j).foldl wireStep y) (C.gates.getD j dGate)).length = 26 + j + 1 := by
      dsimp only [wireStep]; rw [List.length_append, List.length_singleton, hpreLen]
    change (C.gates.foldl wireStep y).getD (26 + j) false = _
    conv_lhs =>
      rw [← List.take_append_drop j C.gates, List.foldl_append, hd, List.foldl_cons,
        foldl_wireStep_prefix _ _ _ (by rw [hstepLen]; omega)]
    dsimp only [wireStep]
    rw [List.getD_append_right _ _ _ _ (by rw [hpreLen]), hpreLen, Nat.sub_self]
    have h0 : ∀ v : Bool, ([v] : List Bool).getD 0 false = v := fun _ => rfl
    rw [h0]
    conv_lhs => rw [hgEq]
    simp only [List.map_cons, List.map_nil]
    rw [foldl_wireStep_take j C.gates y _ (by rw [hyLen, List.length_take]; omega),
        foldl_wireStep_take j C.gates y _ (by rw [hyLen, List.length_take]; omega)]
    rfl
  have wval_gate_or : ∀ (x : Fin 26 → Bool) (j : ℕ), j < C.gates.length →
      (C.gates.getD j dGate).op = PEqualNP.CircuitLowerBounds.GateOp.or →
      wval x (26 + j) = (wval x ((C.gates.getD j dGate).inputs.getD 0 0) ||
        wval x ((C.gates.getD j dGate).inputs.getD 1 0)) := by
    intro x j hj hor
    have h := wval_gate x j hj
    dsimp only at h; rw [h, hor]
    change [wval x ((C.gates.getD j dGate).inputs.getD 0 0),
      wval x ((C.gates.getD j dGate).inputs.getD 1 0)].any id = _
    simp only [List.any_cons, List.any_nil, Bool.or_false, id_eq]
  have wval_gate_and : ∀ (x : Fin 26 → Bool) (j : ℕ), j < C.gates.length →
      (C.gates.getD j dGate).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      wval x (26 + j) = (wval x ((C.gates.getD j dGate).inputs.getD 0 0) &&
        wval x ((C.gates.getD j dGate).inputs.getD 1 0)) := by
    intro x j hj hand
    have h := wval_gate x j hj
    dsimp only at h; rw [h, hand]
    change [wval x ((C.gates.getD j dGate).inputs.getD 0 0),
      wval x ((C.gates.getD j dGate).inputs.getD 1 0)].all id = _
    simp only [List.all_cons, List.all_nil, Bool.and_true, id_eq]
  have hOutBd : 26 ≤ C.output ∧ C.output < 26 + C.gates.length := by
    constructor
    · by_contra hlt26
      have hlt : C.output < 26 := by omega
      let q : Fin 13 := ⟨(if C.output < 13 then C.output + 1 else C.output - 13 + 1) % 13,
        Nat.mod_lt _ (by decide : 0 < 13)⟩
      let z : Fin 26 → Bool := fun i =>
        if i.val < 13 then decide (i.val = q.val) else decide (i.val = 13 + q.val)
      have hzPG : pgFun z = true := by
        dsimp only [pgFun, pgAdj]
        rw [decide_eq_true_eq]
        refine ⟨q, q, Or.inl rfl, ?_, ?_⟩
        · dsimp only [z]
          change (if q.val < 13 then decide (q.val = q.val) else decide (q.val = 13 + q.val)) = true
          simp [q.isLt]
        · dsimp only [z]
          change (if 13 + q.val < 13 then decide (13 + q.val = q.val) else decide (13 + q.val = 13 + q.val)) = true
          simp [show ¬ 13 + q.val < 13 by omega]
      have hzTrue : wval z C.output = true := (hSpec z).mpr hzPG
      rw [wval_input z C.output hlt] at hzTrue
      dsimp only [z] at hzTrue
      by_cases h13 : C.output < 13
      · simp only [h13, ↓reduceIte, decide_eq_true_eq] at hzTrue
        dsimp only [q] at hzTrue
        simp only [h13, ↓reduceIte] at hzTrue
        omega
      · simp only [h13, ↓reduceIte, decide_eq_true_eq] at hzTrue
        dsimp only [q] at hzTrue
        simp only [h13, ↓reduceIte] at hzTrue
        omega
    · by_contra hge
      have hzTrue : C.eval (List.ofFn (maskVec 8193)) = true := (hSpec (maskVec 8193)).mpr pgFun_e0
      have hle : (C.gates.foldl wireStep (List.ofFn (maskVec 8193))).length ≤ C.output := by
        rw [foldl_wireStep_len]; simp; omega
      change (C.gates.foldl wireStep (List.ofFn (maskVec 8193))).getD C.output false = true at hzTrue
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle] at hzTrue
      cases hzTrue
  let sStep : List Bool → List Bool → List Bool → List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun wb wx wy s g =>
      let a := g.inputs.getD 0 0
      let c := g.inputs.getD 1 0
      let cur := s.length
      s ++ [PEqualNP.CircuitLowerBounds.GateOp.casesOn g.op
        ((s.getD a false || s.getD c false) ||
          (!(wb.getD a false) && !(wb.getD c false) && !(wx.getD cur false) && !(wy.getD cur false)))
        (s.getD a false && s.getD c false)
        false (fun _ => false) false]
  let sMax : ℕ → List Bool := fun b =>
    let u := if b = 0 then 25034751 else 67108341
    let x := if b = 0 then 8191 else 67100672
    let y := if b = 0 then 25018369 else 15860
    let wb := C.wires (List.ofFn (maskVec (2 ^ b)))
    let wx := C.wires (List.ofFn (maskVec x))
    let wy := C.wires (List.ofFn (maskVec y))
    let s0 : List Bool := List.ofFn fun i : Fin 26 => !(u.testBit i.val)
    C.gates.foldl (sStep wb wx wy) s0
  have sStep_len : ∀ (wb wx wy : List Bool) (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : List Bool),
      (gs.foldl (sStep wb wx wy) u).length = u.length + gs.length := by
    intro wb wx wy gs
    induction gs with
    | nil => intro u; rfl
    | cons g gs ih =>
      intro u; rw [List.foldl_cons, ih]; simp [sStep]; omega
  have sStep_prefix : ∀ (wb wx wy : List Bool) (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : List Bool) (i : ℕ),
      i < u.length → (gs.foldl (sStep wb wx wy) u).getD i false = u.getD i false := by
    intro wb wx wy gs
    induction gs with
    | nil => intro u i _; rfl
    | cons g gs ih =>
      intro u i hi
      rw [List.foldl_cons, ih]
      · dsimp only [sStep]; rw [List.getD_append _ _ _ _ hi]
      · simp [sStep]; omega
  have sStep_take : ∀ (wb wx wy : List Bool) (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : List Bool) (i : ℕ),
      i < u.length + (gs.take n).length →
      ((gs.take n).foldl (sStep wb wx wy) u).getD i false = (gs.foldl (sStep wb wx wy) u).getD i false := by
    intro wb wx wy n gs u i hi
    conv_rhs =>
      rw [← List.take_append_drop n gs, List.foldl_append,
        sStep_prefix _ _ _ _ _ _ (by rw [sStep_len]; exact hi)]
  have sMax_init : ∀ (b i : ℕ), i < 26 →
      (sMax b).getD i false = !((if b = 0 then 25034751 else 67108341 : ℕ).testBit i) := by
    intro b i hi
    dsimp only [sMax]
    rw [sStep_prefix _ _ _ _ _ i (by simp [hi])]
    rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]
  have sMax_gate : ∀ (b j : ℕ), j < C.gates.length →
      let x := if b = 0 then 8191 else 67100672
      let y := if b = 0 then 25018369 else 15860
      let g := C.gates.getD j dGate
      let a := g.inputs.getD 0 0
      let c := g.inputs.getD 1 0
      let s := fun k => (sMax b).getD k false
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → s (26 + j) = (s a && s c)) ∧
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        s (26 + j) = (s a || s c ||
          (!(maskWval (2 ^ b) a) && !(maskWval (2 ^ b) c) &&
           !(maskWval x (26 + j)) && !(maskWval y (26 + j))))) := by
    intro b j hj
    dsimp only
    have hgMem : C.gates.getD j dGate ∈ C.gates := by
      rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
    have hgEq := list_len2 _ (hAO.2.2 _ hgMem)
    have haLt : (C.gates.getD j dGate).inputs.getD 0 0 < 26 + j :=
      hAO.2.1 j hj _ (by change _ ∈ (C.gates.getD j dGate).inputs; rw [hgEq]; simp)
    have hcLt : (C.gates.getD j dGate).inputs.getD 1 0 < 26 + j :=
      hAO.2.1 j hj _ (by change _ ∈ (C.gates.getD j dGate).inputs; rw [hgEq]; simp)
    let u0 := if b = 0 then 25034751 else 67108341
    let x0 := if b = 0 then 8191 else 67100672
    let y0 := if b = 0 then 25018369 else 15860
    let wb := C.wires (List.ofFn (maskVec (2 ^ b)))
    let wx := C.wires (List.ofFn (maskVec x0))
    let wy := C.wires (List.ofFn (maskVec y0))
    let sInit : List Bool := List.ofFn fun i : Fin 26 => !(u0.testBit i.val)
    let pref := (C.gates.take j).foldl (sStep wb wx wy) sInit
    have hpreLen : pref.length = 26 + j := by
      dsimp only [pref]; rw [sStep_len, List.length_take]; simp [sInit]; omega
    have hstepLen : (sStep wb wx wy pref (C.gates.getD j dGate)).length = 26 + j + 1 := by
      dsimp only [sStep]; rw [List.length_append, List.length_singleton, hpreLen]
    have hd : C.gates.drop j = C.gates.getD j dGate :: C.gates.drop (j + 1) := by
      rw [← List.getElem_cons_drop hj, List.getD_eq_getElem _ _ hj]
    have hsAt : (sMax b).getD (26 + j) false =
        (sStep wb wx wy pref (C.gates.getD j dGate)).getD (26 + j) false := by
      change (C.gates.foldl (sStep wb wx wy) sInit).getD (26 + j) false = _
      conv_lhs => rw [← List.take_append_drop j C.gates, List.foldl_append, hd, List.foldl_cons]
      exact sStep_prefix wb wx wy (C.gates.drop (j + 1)) _ (26 + j) (by rw [hstepLen]; omega)
    rw [hsAt]
    dsimp only [sStep]
    rw [List.getD_append_right _ _ _ _ (by rw [hpreLen]), hpreLen, Nat.sub_self]
    have h0 : ∀ v : Bool, ([v] : List Bool).getD 0 false = v := fun _ => rfl
    rw [h0]
    have hsPre : ∀ i, i < 26 + j → pref.getD i false = (sMax b).getD i false := by
      intro i hi
      exact sStep_take wb wx wy j C.gates sInit i (by simp [sInit, List.length_take]; omega)
    constructor
    · intro hor
      rw [hor]; dsimp only [PEqualNP.CircuitLowerBounds.GateOp.casesOn]
      rw [hsPre _ haLt, hsPre _ hcLt]
    · intro hand
      rw [hand]; dsimp only [PEqualNP.CircuitLowerBounds.GateOp.casesOn]
      rw [hsPre _ haLt, hsPre _ hcLt]
  have kill_of_sMax_false : ∀ (b : ℕ), (sMax b).getD C.output false = false →
      have x9 : ℕ := if b = 0 then 25034751 else 67108341
      have x10 : ℕ := if b = 0 then 8191 else 67100672
      have x11 : ℕ := if b = 0 then 25018369 else 15860
      ∀ (S : Set ℕ), C.output ∈ S → (∀ (i : Fin 26), i.val ∈ S → x9.testBit i.val = false) →
        ¬ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → 26 + j ∈ S →
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ i ∈ g.inputs, i ∈ S) ∧
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i ∈ g.inputs, i ∈ S) ∨
            (∀ i ∈ g.inputs, maskWval (2 ^ b) i = false) ∧
            maskWval x10 (26 + j) = false ∧
            maskWval x11 (26 + j) = false) := by
    intro b hfalse x9 x10 x11 S hOutS hBaseS hStepS
    have hClose : ∀ k < 26 + C.gates.length, k ∈ S → (sMax b).getD k false = true := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro hk hkS
        by_cases hk26 : k < 26
        · rw [sMax_init b k hk26]
          have hbit := hBaseS ⟨k, hk26⟩ hkS
          dsimp only [x9] at hbit
          rw [hbit]; rfl
        · let j := k - 26
          have hj : j < C.gates.length := by omega
          have hkEq : 26 + j = k := by omega
          have hInS : 26 + j ∈ S := hkEq ▸ hkS
          have hgSome : C.gates[j]? = some (C.gates.getD j dGate) := by
            rw [List.getElem?_eq_getElem hj, List.getD_eq_getElem _ _ hj]
          have hSt := hStepS j (C.gates.getD j dGate) hgSome hInS
          have hgMem : C.gates.getD j dGate ∈ C.gates := by
            rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
          have hgEq := list_len2 _ (hAO.2.2 _ hgMem)
          let a := (C.gates.getD j dGate).inputs.getD 0 0
          let c := (C.gates.getD j dGate).inputs.getD 1 0
          have haMem : a ∈ (C.gates.getD j dGate).inputs := by rw [hgEq]; simp [a]
          have hcMem : c ∈ (C.gates.getD j dGate).inputs := by rw [hgEq]; simp [c]
          have haLt : a < 26 + j := hAO.2.1 j hj _ haMem
          have hcLt : c < 26 + j := hAO.2.1 j hj _ hcMem
          have hGate := sMax_gate b j hj
          dsimp only at hGate
          rw [← hkEq]
          rcases hAO.1 _ hgMem with hand | hor
          · rw [hGate.2 hand]
            rcases hSt.2 hand with ⟨i, hiIn, hiS⟩ | ⟨hwB, hwX, hwY⟩
            · rw [hgEq] at hiIn
              rcases List.mem_cons.mp hiIn with hia | hm
              · rw [hia] at hiS
                change ((sMax b).getD a false || (sMax b).getD c false || _) = true
                rw [ih a (by omega) (by omega) hiS]; simp
              · rw [List.mem_singleton.mp hm] at hiS
                change ((sMax b).getD a false || (sMax b).getD c false || _) = true
                rw [ih c (by omega) (by omega) hiS]; simp
            · have haB := hwB a haMem
              have hcB := hwB c hcMem
              dsimp only [a, c] at haB hcB
              dsimp only [x10, x11] at hwX hwY
              rw [haB, hcB, hwX, hwY]; simp
          · rw [hGate.1 hor]
            have hAll := hSt.1 hor
            change ((sMax b).getD a false && (sMax b).getD c false) = true
            rw [ih a (by omega) (by omega) (hAll a haMem),
                ih c (by omega) (by omega) (hAll c hcMem)]
            rfl
    have hT := hClose C.output hOutBd.2 hOutS
    rw [hfalse] at hT; cases hT
  by_cases hs0 : (sMax 0).getD C.output false = false
  · exact ⟨0, by simp, kill_of_sMax_false 0 hs0⟩
  · have hs0T : (sMax 0).getD C.output false = true := Bool.eq_true_of_not_eq_false hs0
    by_cases hs1 : (sMax 13).getD C.output false = false
    · exact ⟨13, by simp, kill_of_sMax_false 13 hs1⟩
    · have hs1T : (sMax 13).getD C.output false = true := Bool.eq_true_of_not_eq_false hs1
      exfalso
      let isLine : ℕ → Bool := fun i => decide (13 ≤ i)
      let x013 : List Bool := (List.range 26).map fun i => i == 0 || i == 13
      let lpStep : List (Bool × Bool) → PEqualNP.CircuitLowerBounds.Gate → List (Bool × Bool) := fun w g =>
        let ins := g.inputs.map fun i => w.getD i (false, false)
        w ++ [PEqualNP.CircuitLowerBounds.GateOp.casesOn g.op
          (ins.foldl (fun (acc : Bool × Bool) p =>
            (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false))
          (ins.any (·.1), ins.any (·.2))
          (false, false) (fun _ => (false, false)) (false, false)]
      have lpFoldEq (isL : ℕ → Bool) (x : List Bool) :
          PEqualNP.ReadK.linearParts C isL x =
            C.gates.foldl lpStep ((x.zipIdx).map fun bi =>
              if isL bi.2 then (false, bi.1) else (bi.1, false)) := by
        unfold PEqualNP.ReadK.linearParts
        congr 1
        funext w g
        dsimp only [lpStep]
        cases g.op <;> rfl
      have lpStep_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : List (Bool × Bool)),
          (gs.foldl lpStep u).length = u.length + gs.length := by
        intro gs
        induction gs with
        | nil => intro u; rfl
        | cons g gs ih => intro u; rw [List.foldl_cons, ih]; simp [lpStep]; omega
      have lpStep_prefix : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : List (Bool × Bool)) (i : ℕ),
          i < u.length → (gs.foldl lpStep u).getD i (false, false) = u.getD i (false, false) := by
        intro gs
        induction gs with
        | nil => intro u i _; rfl
        | cons g gs ih =>
          intro u i hi
          rw [List.foldl_cons, ih]
          · dsimp only [lpStep]; rw [List.getD_append _ _ _ _ hi]
          · simp [lpStep]; omega
      have lpStep_take : ∀ (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : List (Bool × Bool)) (i : ℕ),
          i < u.length + (gs.take n).length →
          ((gs.take n).foldl lpStep u).getD i (false, false) = (gs.foldl lpStep u).getD i (false, false) := by
        intro n gs u i hi
        conv_rhs =>
          rw [← List.take_append_drop n gs, List.foldl_append,
            lpStep_prefix _ _ _ (by rw [lpStep_len]; exact hi)]
      have lp_gate : ∀ (isL : ℕ → Bool) (x : List Bool), x.length = 26 → ∀ j < C.gates.length,
          let lp := fun k => (PEqualNP.ReadK.linearParts C isL x).getD k (false, false)
          let g := C.gates.getD j dGate
          let a := g.inputs.getD 0 0
          let c := g.inputs.getD 1 0
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → lp (26 + j) = ((lp a).1 || (lp c).1, (lp a).2 || (lp c).2)) ∧
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
            lp (26 + j) = ((lp a).1 && (lp c).1, ((lp a).1 && (lp c).2) || ((lp a).2 && (lp c).1))) := by
        intro isL x hx j hj
        dsimp only
        have hgMem : C.gates.getD j dGate ∈ C.gates := by
          rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
        have hgEq := list_len2 _ (hAO.2.2 _ hgMem)
        have haLt : (C.gates.getD j dGate).inputs.getD 0 0 < 26 + j :=
          hAO.2.1 j hj _ (by change _ ∈ (C.gates.getD j dGate).inputs; rw [hgEq]; simp)
        have hcLt : (C.gates.getD j dGate).inputs.getD 1 0 < 26 + j :=
          hAO.2.1 j hj _ (by change _ ∈ (C.gates.getD j dGate).inputs; rw [hgEq]; simp)
        let init : List (Bool × Bool) := (x.zipIdx).map fun bi => if isL bi.2 then (false, bi.1) else (bi.1, false)
        have hInitLen : init.length = 26 := by simp [init, hx]
        let pref := (C.gates.take j).foldl lpStep init
        have hpreLen : pref.length = 26 + j := by
          dsimp only [pref]; rw [lpStep_len, hInitLen, List.length_take]; omega
        have hstepLen : (lpStep pref (C.gates.getD j dGate)).length = 26 + j + 1 := by
          dsimp only [lpStep]; rw [List.length_append, List.length_singleton, hpreLen]
        have hd : C.gates.drop j = C.gates.getD j dGate :: C.gates.drop (j + 1) := by
          rw [← List.getElem_cons_drop hj, List.getD_eq_getElem _ _ hj]
        have hAt : (PEqualNP.ReadK.linearParts C isL x).getD (26 + j) (false, false) =
            (lpStep pref (C.gates.getD j dGate)).getD (26 + j) (false, false) := by
          rw [lpFoldEq]
          change (C.gates.foldl lpStep init).getD (26 + j) (false, false) = _
          conv_lhs => rw [← List.take_append_drop j C.gates, List.foldl_append, hd, List.foldl_cons]
          exact lpStep_prefix (C.gates.drop (j + 1)) _ (26 + j) (by rw [hstepLen]; omega)
        rw [hAt]
        dsimp only [lpStep]
        rw [List.getD_append_right _ _ _ _ (by rw [hpreLen]), hpreLen, Nat.sub_self]
        have h0 : ∀ v : Bool × Bool, ([v] : List (Bool × Bool)).getD 0 (false, false) = v := fun _ => rfl
        rw [h0]
        have hPre : ∀ i, i < 26 + j → pref.getD i (false, false) =
            (PEqualNP.ReadK.linearParts C isL x).getD i (false, false) := by
          intro i hi
          rw [lpFoldEq]
          exact lpStep_take j C.gates init i (by rw [hInitLen, List.length_take]; omega)
        constructor
        · intro hor
          rw [hor]
          conv_lhs => rw [hgEq]
          simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false]
          rw [hPre _ haLt, hPre _ hcLt]
        · intro hand
          rw [hand]
          conv_lhs => rw [hgEq]
          simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
            Bool.true_and, Bool.false_and, Bool.or_false]
          rw [hPre _ haLt, hPre _ hcLt]
      have lp_fst_isLine : ∀ k < 26 + C.gates.length,
          ((PEqualNP.ReadK.linearParts C isLine x013).getD k (false, false)).1 = maskWval 1 k := by
        intro k
        induction k using Nat.strong_induction_on with
        | ind k ih =>
          intro hk
          let init : List (Bool × Bool) := (x013.zipIdx).map fun bi => if isLine bi.2 then (false, bi.1) else (bi.1, false)
          by_cases hk26 : k < 26
          · rw [lpFoldEq]
            change ((C.gates.foldl lpStep init).getD k (false, false)).1 = maskWval 1 k
            rw [lpStep_prefix _ _ _ (by simp [init, x013]; exact hk26)]
            dsimp only [maskWval]; rw [wval_input (maskVec 1) k hk26]
            have hDec : ∀ i : Fin 26, (init.getD i.val (false, false)).1 = (1 : ℕ).testBit i.val := by decide
            exact hDec ⟨k, hk26⟩
          · let j := k - 26
            have hj : j < C.gates.length := by omega
            have hkEq : 26 + j = k := by omega
            rw [← hkEq]
            have hgMem : C.gates.getD j dGate ∈ C.gates := by
              rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
            have hgEq := list_len2 _ (hAO.2.2 _ hgMem)
            have haLt : (C.gates.getD j dGate).inputs.getD 0 0 < 26 + j :=
              hAO.2.1 j hj _ (by change _ ∈ (C.gates.getD j dGate).inputs; rw [hgEq]; simp)
            have hcLt : (C.gates.getD j dGate).inputs.getD 1 0 < 26 + j :=
              hAO.2.1 j hj _ (by change _ ∈ (C.gates.getD j dGate).inputs; rw [hgEq]; simp)
            have hG := lp_gate isLine x013 (by simp [x013]) j hj
            dsimp only at hG
            rcases hAO.1 _ hgMem with hand | hor
            · rw [hG.2 hand]; dsimp only [maskWval]; rw [wval_gate_and (maskVec 1) j hj hand]
              exact congrArg₂ (· && ·) (ih _ (by omega) (by omega)) (ih _ (by omega) (by omega))
            · rw [hG.1 hor]; dsimp only [maskWval]; rw [wval_gate_or (maskVec 1) j hj hor]
              exact congrArg₂ (· || ·) (ih _ (by omega) (by omega)) (ih _ (by omega) (by omega))
      have lp_fst_notIsLine : ∀ k < 26 + C.gates.length,
          ((PEqualNP.ReadK.linearParts C (fun i => !isLine i) x013).getD k (false, false)).1 = maskWval 8192 k := by
        intro k
        induction k using Nat.strong_induction_on with
        | ind k ih =>
          intro hk
          let init : List (Bool × Bool) := (x013.zipIdx).map fun bi => if !isLine bi.2 then (false, bi.1) else (bi.1, false)
          by_cases hk26 : k < 26
          · rw [lpFoldEq]
            change ((C.gates.foldl lpStep init).getD k (false, false)).1 = maskWval 8192 k
            rw [lpStep_prefix _ _ _ (by simp [init, x013]; exact hk26)]
            dsimp only [maskWval]; rw [wval_input (maskVec 8192) k hk26]
            have hDec : ∀ i : Fin 26, (init.getD i.val (false, false)).1 = (8192 : ℕ).testBit i.val := by decide
            exact hDec ⟨k, hk26⟩
          · let j := k - 26
            have hj : j < C.gates.length := by omega
            have hkEq : 26 + j = k := by omega
            rw [← hkEq]
            have hgMem : C.gates.getD j dGate ∈ C.gates := by
              rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
            have hgEq := list_len2 _ (hAO.2.2 _ hgMem)
            have haLt : (C.gates.getD j dGate).inputs.getD 0 0 < 26 + j :=
              hAO.2.1 j hj _ (by change _ ∈ (C.gates.getD j dGate).inputs; rw [hgEq]; simp)
            have hcLt : (C.gates.getD j dGate).inputs.getD 1 0 < 26 + j :=
              hAO.2.1 j hj _ (by change _ ∈ (C.gates.getD j dGate).inputs; rw [hgEq]; simp)
            have hG := lp_gate (fun i => !isLine i) x013 (by simp [x013]) j hj
            dsimp only at hG
            rcases hAO.1 _ hgMem with hand | hor
            · rw [hG.2 hand]; dsimp only [maskWval]; rw [wval_gate_and (maskVec 8192) j hj hand]
              exact congrArg₂ (· && ·) (ih _ (by omega) (by omega)) (ih _ (by omega) (by omega))
            · rw [hG.1 hor]; dsimp only [maskWval]; rw [wval_gate_or (maskVec 8192) j hj hor]
              exact congrArg₂ (· || ·) (ih _ (by omega) (by omega)) (ih _ (by omega) (by omega))
      have lp_zero_of_sMax0 : ∀ k < 26 + C.gates.length, (sMax 0).getD k false = true →
          (PEqualNP.ReadK.linearParts C isLine x013).getD k (false, false) = (false, false) := by
        intro k
        induction k using Nat.strong_induction_on with
        | ind k ih =>
          intro hk hsk
          let init : List (Bool × Bool) := (x013.zipIdx).map fun bi => if isLine bi.2 then (false, bi.1) else (bi.1, false)
          by_cases hk26 : k < 26
          · rw [sMax_init 0 k hk26] at hsk
            simp only [↓reduceIte, Bool.not_eq_true'] at hsk
            rw [lpFoldEq]
            change (C.gates.foldl lpStep init).getD k (false, false) = (false, false)
            rw [lpStep_prefix _ _ _ (by simp [init, x013]; exact hk26)]
            have hDec : ∀ i : Fin 26, (25034751 : ℕ).testBit i.val = false →
                init.getD i.val (false, false) = (false, false) := by decide
            exact hDec ⟨k, hk26⟩ hsk
          · let j := k - 26
            have hj : j < C.gates.length := by omega
            have hkEq : 26 + j = k := by omega
            rw [← hkEq] at hsk ⊢
            have hgMem : C.gates.getD j dGate ∈ C.gates := by
              rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
            have hgEq := list_len2 _ (hAO.2.2 _ hgMem)
            let a := (C.gates.getD j dGate).inputs.getD 0 0
            let c := (C.gates.getD j dGate).inputs.getD 1 0
            have haLt : a < 26 + j := hAO.2.1 j hj _ (by change _ ∈ (C.gates.getD j dGate).inputs; rw [hgEq]; simp [a])
            have hcLt : c < 26 + j := hAO.2.1 j hj _ (by change _ ∈ (C.gates.getD j dGate).inputs; rw [hgEq]; simp [c])
            have hS := sMax_gate 0 j hj
            have hG := lp_gate isLine x013 (by simp [x013]) j hj
            dsimp only at hS hG
            simp only [↓reduceIte, pow_zero] at hS
            rcases hAO.1 _ hgMem with hand | hor
            · rw [hS.2 hand] at hsk
              rw [hG.2 hand]
              rcases (Bool.or_eq_true _ _).mp hsk with hsc | hstop
              · rcases (Bool.or_eq_true _ _).mp hsc with hsa | hsc'
                · rw [ih a (by omega) (by omega) hsa]; simp
                · rw [ih c (by omega) (by omega) hsc']; simp
              · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hstop
                have ha1 : ((PEqualNP.ReadK.linearParts C isLine x013).getD a (false, false)).1 = false := by
                  rw [lp_fst_isLine a (by omega)]; exact hstop.1.1.1
                have hc1 : ((PEqualNP.ReadK.linearParts C isLine x013).getD c (false, false)).1 = false := by
                  rw [lp_fst_isLine c (by omega)]; exact hstop.1.1.2
                rw [ha1, hc1]; simp
            · rw [hS.1 hor, Bool.and_eq_true] at hsk
              rw [hG.1 hor, ih a (by omega) (by omega) hsk.1, ih c (by omega) (by omega) hsk.2]; rfl
      have lp_zero_of_sMax13 : ∀ k < 26 + C.gates.length, (sMax 13).getD k false = true →
          (PEqualNP.ReadK.linearParts C (fun i => !isLine i) x013).getD k (false, false) = (false, false) := by
        intro k
        induction k using Nat.strong_induction_on with
        | ind k ih =>
          intro hk hsk
          let init : List (Bool × Bool) := (x013.zipIdx).map fun bi => if !isLine bi.2 then (false, bi.1) else (bi.1, false)
          by_cases hk26 : k < 26
          · rw [sMax_init 13 k hk26] at hsk
            simp only [show ¬ (13 : ℕ) = 0 by decide, ↓reduceIte, Bool.not_eq_true'] at hsk
            rw [lpFoldEq]
            change (C.gates.foldl lpStep init).getD k (false, false) = (false, false)
            rw [lpStep_prefix _ _ _ (by simp [init, x013]; exact hk26)]
            have hDec : ∀ i : Fin 26, (67108341 : ℕ).testBit i.val = false →
                init.getD i.val (false, false) = (false, false) := by decide
            exact hDec ⟨k, hk26⟩ hsk
          · let j := k - 26
            have hj : j < C.gates.length := by omega
            have hkEq : 26 + j = k := by omega
            rw [← hkEq] at hsk ⊢
            have hgMem : C.gates.getD j dGate ∈ C.gates := by
              rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
            have hgEq := list_len2 _ (hAO.2.2 _ hgMem)
            let a := (C.gates.getD j dGate).inputs.getD 0 0
            let c := (C.gates.getD j dGate).inputs.getD 1 0
            have haLt : a < 26 + j := hAO.2.1 j hj _ (by change _ ∈ (C.gates.getD j dGate).inputs; rw [hgEq]; simp [a])
            have hcLt : c < 26 + j := hAO.2.1 j hj _ (by change _ ∈ (C.gates.getD j dGate).inputs; rw [hgEq]; simp [c])
            have hS := sMax_gate 13 j hj
            have hG := lp_gate (fun i => !isLine i) x013 (by simp [x013]) j hj
            dsimp only at hS hG
            simp only [show ¬ (13 : ℕ) = 0 by decide, ↓reduceIte] at hS
            rw [show (2 ^ 13 : ℕ) = 8192 from rfl] at hS
            rcases hAO.1 _ hgMem with hand | hor
            · rw [hS.2 hand] at hsk
              rw [hG.2 hand]
              rcases (Bool.or_eq_true _ _).mp hsk with hsc | hstop
              · rcases (Bool.or_eq_true _ _).mp hsc with hsa | hsc'
                · rw [ih a (by omega) (by omega) hsa]; simp
                · rw [ih c (by omega) (by omega) hsc']; simp
              · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hstop
                have ha1 : ((PEqualNP.ReadK.linearParts C (fun i => !isLine i) x013).getD a (false, false)).1 = false := by
                  rw [lp_fst_notIsLine a (by omega)]; exact hstop.1.1.1
                have hc1 : ((PEqualNP.ReadK.linearParts C (fun i => !isLine i) x013).getD c (false, false)).1 = false := by
                  rw [lp_fst_notIsLine c (by omega)]; exact hstop.1.1.2
                rw [ha1, hc1]; simp
            · rw [hS.1 hor, Bool.and_eq_true] at hsk
              rw [hG.1 hor, ih a (by omega) (by omega) hsk.1, ih c (by omega) (by omega) hsk.2]; rfl
      have hLP0Out : (PEqualNP.ReadK.linearParts C isLine x013).getD C.output (false, false) = (false, false) :=
        lp_zero_of_sMax0 C.output hOutBd.2 hs0T
      have hLP1Out : (PEqualNP.ReadK.linearParts C (fun i => !isLine i) x013).getD C.output (false, false) = (false, false) :=
        lp_zero_of_sMax13 C.output hOutBd.2 hs1T
      have hNotSR : ¬ PEqualNP.ReadK.IsSingleRead C 26 isLine [(0, 13)] := by
        intro hSR
        have h1 : PEqualNP.ReadK.lineSingle C 26 isLine 0 13 = false := by
          unfold PEqualNP.ReadK.lineSingle; rw [hLP0Out]
        have h2 : PEqualNP.ReadK.lineSingle C 26 (fun i => !isLine i) 0 13 = false := by
          unfold PEqualNP.ReadK.lineSingle; rw [hLP1Out]
        unfold PEqualNP.ReadK.IsSingleRead PEqualNP.ReadK.doubleReread at hSR
        simp [h1, h2] at hSR
      let pgEdges : List (ℕ × ℕ) :=
        (List.finRange 13).flatMap fun l : Fin 13 =>
          [(l.val, 13 + l.val), ((l + 1).val, 13 + l.val),
           ((l + 3).val, 13 + l.val), ((l + 9).val, 13 + l.val)]
      let G : SimpleGraph (Fin 26) := PEqualNP.EdgeOwnership.edgeGraph 26 pgEdges
      have mem_pgEdges_iff : ∀ a b : ℕ,
          (a, b) ∈ pgEdges ↔ ∃ p l : Fin 13, pgAdj p l ∧ a = p.val ∧ b = 13 + l.val := by
        intro a b
        dsimp only [pgEdges, pgAdj]
        simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons, List.not_mem_nil,
          or_false, Prod.mk.injEq]
        constructor
        · rintro ⟨l, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
          · exact ⟨l, l, Or.inl rfl, rfl, rfl⟩
          · exact ⟨l + 1, l, Or.inr (Or.inl rfl), rfl, rfl⟩
          · exact ⟨l + 3, l, Or.inr (Or.inr (Or.inl rfl)), rfl, rfl⟩
          · exact ⟨l + 9, l, Or.inr (Or.inr (Or.inr rfl)), rfl, rfl⟩
        · rintro ⟨p, l, h, rfl, rfl⟩
          refine ⟨l, ?_⟩
          rcases h with rfl | rfl | rfl | rfl
          · exact Or.inl ⟨rfl, rfl⟩
          · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
      have graphFun_pgGraph : ∀ z : Fin 26 → Bool,
          PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ z = true ↔ pgFun z = true := by
        intro z
        change (decide (∃ a ∈ (∅ : Finset (Fin 26)), z a = true) ||
          decide (∃ u v, G.Adj u v ∧ z u = true ∧ z v = true)) = true ↔ pgFun z = true
        dsimp only [pgFun]
        simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
          decide_eq_true_eq]
        constructor
        · rintro ⟨u, v, hadj, hu, hv⟩
          rcases hadj.2 with h1 | h2
          · obtain ⟨p, l, hpl, hup, hvl⟩ := (mem_pgEdges_iff u.val v.val).mp h1
            refine ⟨p, l, hpl, ?_, ?_⟩
            · have : Fin.castAdd 13 p = u := Fin.ext hup.symm
              rw [this]; exact hu
            · have : Fin.natAdd 13 l = v := Fin.ext (by simp [Fin.natAdd]; omega)
              rw [this]; exact hv
          · obtain ⟨p, l, hpl, hvp, hul⟩ := (mem_pgEdges_iff v.val u.val).mp h2
            refine ⟨p, l, hpl, ?_, ?_⟩
            · have : Fin.castAdd 13 p = v := Fin.ext hvp.symm
              rw [this]; exact hv
            · have : Fin.natAdd 13 l = u := Fin.ext (by simp [Fin.natAdd]; omega)
              rw [this]; exact hu
        · rintro ⟨p, l, hpl, hp, hl⟩
          refine ⟨Fin.castAdd 13 p, Fin.natAdd 13 l, ?_, hp, hl⟩
          refine ⟨?_, Or.inl ((mem_pgEdges_iff _ _).mpr ⟨p, l, hpl, rfl, by simp [Fin.natAdd]⟩)⟩
          intro heq
          have := congrArg Fin.val heq
          change p.val = 13 + l.val at this
          omega
      have hCircuitFun : PEqualNP.MetaComplexity.circuitFun 26 C =
          PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
        funext z
        unfold PEqualNP.MetaComplexity.circuitFun
        exact Bool.eq_iff_iff.mpr ((hSpec z).trans (graphFun_pgGraph z).symm)
      let orReachStep : List (Finset (Fin 26)) → PEqualNP.CircuitLowerBounds.Gate → List (Finset (Fin 26)) :=
        fun rs g =>
          let a := g.inputs.getD 0 0
          let b := g.inputs.getD 1 0
          rs ++ [PEqualNP.CircuitLowerBounds.GateOp.casesOn g.op ∅ (rs.getD a ∅ ∪ rs.getD b ∅) ∅ (fun _ => ∅) ∅]
      let orReachList : List (Finset (Fin 26)) :=
        C.gates.foldl orReachStep (List.ofFn fun i : Fin 26 => ({i} : Finset (Fin 26)))
      let orReach : ℕ → Finset (Fin 26) := fun w => orReachList.getD w ∅
      have orReachStep_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : List (Finset (Fin 26))),
          (gs.foldl orReachStep u).length = u.length + gs.length := by
        intro gs
        induction gs with
        | nil => intro u; rfl
        | cons g gs ih => intro u; rw [List.foldl_cons, ih]; simp [orReachStep]; omega
      have orReachStep_prefix : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : List (Finset (Fin 26))) (i : ℕ),
          i < u.length → (gs.foldl orReachStep u).getD i ∅ = u.getD i ∅ := by
        intro gs
        induction gs with
        | nil => intro u i _; rfl
        | cons g gs ih =>
          intro u i hi
          rw [List.foldl_cons, ih]
          · dsimp only [orReachStep]; rw [List.getD_append _ _ _ _ hi]
          · simp [orReachStep]; omega
      have orReachStep_take : ∀ (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : List (Finset (Fin 26))) (i : ℕ),
          i < u.length + (gs.take n).length →
          ((gs.take n).foldl orReachStep u).getD i ∅ = (gs.foldl orReachStep u).getD i ∅ := by
        intro n gs u i hi
        conv_rhs =>
          rw [← List.take_append_drop n gs, List.foldl_append,
            orReachStep_prefix _ _ _ (by rw [orReachStep_len]; exact hi)]
      have orReach_input : ∀ (i : ℕ) (hi : i < 26), orReach i = {⟨i, hi⟩} := by
        intro i hi
        dsimp only [orReach, orReachList]
        rw [orReachStep_prefix _ _ _ (by simp [hi])]
        rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]
      have orReach_gate : ∀ j < C.gates.length,
          let g := C.gates.getD j dGate
          let a := g.inputs.getD 0 0
          let b := g.inputs.getD 1 0
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → orReach (26 + j) = orReach a ∪ orReach b) ∧
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.and → orReach (26 + j) = ∅) := by
        intro j hj
        dsimp only
        have hgMem : C.gates.getD j dGate ∈ C.gates := by
          rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
        have hgEq := list_len2 _ (hAO.2.2 _ hgMem)
        have haLt : (C.gates.getD j dGate).inputs.getD 0 0 < 26 + j :=
          hAO.2.1 j hj _ (by change _ ∈ (C.gates.getD j dGate).inputs; rw [hgEq]; simp)
        have hbLt : (C.gates.getD j dGate).inputs.getD 1 0 < 26 + j :=
          hAO.2.1 j hj _ (by change _ ∈ (C.gates.getD j dGate).inputs; rw [hgEq]; simp)
        let init : List (Finset (Fin 26)) := List.ofFn fun i : Fin 26 => ({i} : Finset (Fin 26))
        let pref := (C.gates.take j).foldl orReachStep init
        have hpreLen : pref.length = 26 + j := by
          dsimp only [pref]; rw [orReachStep_len, List.length_take]; simp [init]; omega
        have hstepLen : (orReachStep pref (C.gates.getD j dGate)).length = 26 + j + 1 := by
          dsimp only [orReachStep]; rw [List.length_append, List.length_singleton, hpreLen]
        have hd : C.gates.drop j = C.gates.getD j dGate :: C.gates.drop (j + 1) := by
          rw [← List.getElem_cons_drop hj, List.getD_eq_getElem _ _ hj]
        have hrAt : orReach (26 + j) = (orReachStep pref (C.gates.getD j dGate)).getD (26 + j) ∅ := by
          dsimp only [orReach, orReachList]
          conv_lhs => rw [← List.take_append_drop j C.gates, List.foldl_append, hd, List.foldl_cons]
          exact orReachStep_prefix (C.gates.drop (j + 1)) _ (26 + j) (by rw [hstepLen]; omega)
        rw [hrAt]
        dsimp only [orReachStep]
        rw [List.getD_append_right _ _ _ _ (by rw [hpreLen]), hpreLen, Nat.sub_self]
        have h0 : ∀ v : Finset (Fin 26), ([v] : List (Finset (Fin 26))).getD 0 ∅ = v := fun _ => rfl
        rw [h0]
        have hPre : ∀ i, i < 26 + j → pref.getD i ∅ = orReach i := by
          intro i hi
          exact orReachStep_take j C.gates init i (by simp [init, List.length_take]; omega)
        constructor
        · intro hor
          rw [hor]; dsimp only [PEqualNP.CircuitLowerBounds.GateOp.casesOn]
          rw [hPre _ haLt, hPre _ hbLt]
        · intro hand; rw [hand]
      have wval_of_mem_orReach : ∀ (x : Fin 26 → Bool), ∀ k < 26 + C.gates.length,
          ∀ v ∈ orReach k, x v = true → wval x k = true := by
        intro x k
        induction k using Nat.strong_induction_on with
        | ind k ih =>
          intro hk v hv hxv
          by_cases hk26 : k < 26
          · rw [orReach_input k hk26, Finset.mem_singleton] at hv
            rw [wval_input x k hk26, ← hv]; exact hxv
          · let j := k - 26
            have hj : j < C.gates.length := by omega
            have hkEq : 26 + j = k := by omega
            rw [← hkEq] at hv ⊢
            have hgMem : C.gates.getD j dGate ∈ C.gates := by
              rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
            have hgEq := list_len2 _ (hAO.2.2 _ hgMem)
            have haLt : (C.gates.getD j dGate).inputs.getD 0 0 < 26 + j :=
              hAO.2.1 j hj _ (by change _ ∈ (C.gates.getD j dGate).inputs; rw [hgEq]; simp)
            have hbLt : (C.gates.getD j dGate).inputs.getD 1 0 < 26 + j :=
              hAO.2.1 j hj _ (by change _ ∈ (C.gates.getD j dGate).inputs; rw [hgEq]; simp)
            have hrg := orReach_gate j hj
            dsimp only at hrg
            rcases hAO.1 _ hgMem with hand | hor
            · rw [hrg.2 hand] at hv; exact absurd hv (Finset.notMem_empty v)
            · rw [hrg.1 hor, Finset.mem_union] at hv
              rw [wval_gate_or x j hj hor, Bool.or_eq_true]
              rcases hv with h1 | h2
              · exact Or.inl (ih _ (by omega) (by omega) v h1 hxv)
              · exact Or.inr (ih _ (by omega) (by omega) v h2 hxv)
      have lp_snd_of_mem_orReach : ∀ (isL : ℕ → Bool) (v : Fin 26),
          (((x013.zipIdx).map fun bi => if isL bi.2 then (false, bi.1) else (bi.1, false)).getD v.val (false, false)).2 = true →
          ∀ w < 26 + C.gates.length, v ∈ orReach w →
            ((PEqualNP.ReadK.linearParts C isL x013).getD w (false, false)).2 = true := by
        intro isL v hvInit w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hw hv
          let init : List (Bool × Bool) := (x013.zipIdx).map fun bi => if isL bi.2 then (false, bi.1) else (bi.1, false)
          by_cases hw26 : w < 26
          · rw [orReach_input w hw26, Finset.mem_singleton] at hv
            rw [lpFoldEq]
            change ((C.gates.foldl lpStep init).getD w (false, false)).2 = true
            rw [lpStep_prefix _ _ _ (by simp [init, x013]; exact hw26)]
            have hwv : w = v.val := by rw [hv]
            rw [hwv]; exact hvInit
          · let j := w - 26
            have hj : j < C.gates.length := by omega
            have hwEq : 26 + j = w := by omega
            rw [← hwEq] at hv ⊢
            have hgMem : C.gates.getD j dGate ∈ C.gates := by
              rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
            have hgEq := list_len2 _ (hAO.2.2 _ hgMem)
            have haLt : (C.gates.getD j dGate).inputs.getD 0 0 < 26 + j :=
              hAO.2.1 j hj _ (by change _ ∈ (C.gates.getD j dGate).inputs; rw [hgEq]; simp)
            have hbLt : (C.gates.getD j dGate).inputs.getD 1 0 < 26 + j :=
              hAO.2.1 j hj _ (by change _ ∈ (C.gates.getD j dGate).inputs; rw [hgEq]; simp)
            have hrg := orReach_gate j hj
            have hG := lp_gate isL x013 (by simp [x013]) j hj
            dsimp only at hrg hG
            rcases hAO.1 _ hgMem with hand | hor
            · rw [hrg.2 hand] at hv; exact absurd hv (Finset.notMem_empty v)
            · rw [hrg.1 hor, Finset.mem_union] at hv
              rw [hG.1 hor]; dsimp only; rw [Bool.or_eq_true]
              rcases hv with h1 | h2
              · exact Or.inl (ih _ (by omega) (by omega) h1)
              · exact Or.inr (ih _ (by omega) (by omega) h2)
      have hZeroOrReach : ∀ w < 26 + C.gates.length, (⟨0, by decide⟩ : Fin 26) ∈ orReach w →
          ((PEqualNP.ReadK.linearParts C isLine x013).getD w (false, false)).1 = true ∧
          ((PEqualNP.ReadK.linearParts C (fun i => !isLine i) x013).getD w (false, false)).2 = true := by
        intro w hw hmem
        constructor
        · rw [lp_fst_isLine w hw]
          exact wval_of_mem_orReach (maskVec 1) w hw ⟨0, by decide⟩ hmem (by decide)
        · exact lp_snd_of_mem_orReach (fun i => !isLine i) ⟨0, by decide⟩ (by decide) w hw hmem
      have h13OrReach : ∀ w < 26 + C.gates.length, (⟨13, by decide⟩ : Fin 26) ∈ orReach w →
          ((PEqualNP.ReadK.linearParts C (fun i => !isLine i) x013).getD w (false, false)).1 = true ∧
          ((PEqualNP.ReadK.linearParts C isLine x013).getD w (false, false)).2 = true := by
        intro w hw hmem
        constructor
        · rw [lp_fst_notIsLine w hw]
          exact wval_of_mem_orReach (maskVec 8192) w hw ⟨13, by decide⟩ hmem (by decide)
        · exact lp_snd_of_mem_orReach isLine ⟨13, by decide⟩ (by decide) w hw hmem
      have coneStep_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : List (List ℕ)),
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep 26) u).length = u.length + gs.length := by
        intro gs
        induction gs with
        | nil => intro u; rfl
        | cons g gs ih =>
          intro u
          rw [List.foldl_cons, ih]
          change (u ++ [_]).length + gs.length = u.length + (g :: gs).length
          simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
          omega
      have coneStep_prefix : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : List (List ℕ)) (i : ℕ),
          i < u.length → (gs.foldl (PEqualNP.EdgeOwnership.coneStep 26) u).getD i [] = u.getD i [] := by
        intro gs
        induction gs with
        | nil => intro u i _; rfl
        | cons g gs ih =>
          intro u i hi
          rw [List.foldl_cons, ih]
          · dsimp only [PEqualNP.EdgeOwnership.coneStep]; rw [List.getD_append _ _ _ _ hi]
          · change i < (u ++ [_]).length
            simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
            omega
      have coneStep_take : ∀ (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : List (List ℕ)) (i : ℕ),
          i < u.length + (gs.take n).length →
          ((gs.take n).foldl (PEqualNP.EdgeOwnership.coneStep 26) u).getD i [] =
            (gs.foldl (PEqualNP.EdgeOwnership.coneStep 26) u).getD i [] := by
        intro n gs u i hi
        conv_rhs =>
          rw [← List.take_append_drop n gs, List.foldl_append,
            coneStep_prefix _ _ _ (by rw [coneStep_len]; exact hi)]
      have inCone_iff_step : ∀ j < C.gates.length, ∀ i : ℕ,
          PEqualNP.EdgeOwnership.InCone 26 C i j ↔
            ∃ w ∈ (C.gates.getD j dGate).inputs, 26 ≤ w ∧ w < 26 + j ∧
              (i = w - 26 ∨ PEqualNP.EdgeOwnership.InCone 26 C i (w - 26)) := by
        intro j hj i
        let pref := (C.gates.take j).foldl (PEqualNP.EdgeOwnership.coneStep 26) []
        have hpreLen : pref.length = j := by
          dsimp only [pref]; rw [coneStep_len, List.length_nil, Nat.zero_add, List.length_take]; omega
        have hstepLen : (PEqualNP.EdgeOwnership.coneStep 26 pref (C.gates.getD j dGate)).length = j + 1 := by
          dsimp only [PEqualNP.EdgeOwnership.coneStep]; rw [List.length_append, List.length_singleton, hpreLen]
        have hd : C.gates.drop j = C.gates.getD j dGate :: C.gates.drop (j + 1) := by
          rw [← List.getElem_cons_drop hj, List.getD_eq_getElem _ _ hj]
        have hAt : (PEqualNP.EdgeOwnership.cones 26 C).getD j [] =
            (PEqualNP.EdgeOwnership.coneStep 26 pref (C.gates.getD j dGate)).getD j [] := by
          unfold PEqualNP.EdgeOwnership.cones
          conv_lhs => rw [← List.take_append_drop j C.gates, List.foldl_append, hd, List.foldl_cons]
          exact coneStep_prefix (C.gates.drop (j + 1)) _ j (by rw [hstepLen]; omega)
        unfold PEqualNP.EdgeOwnership.InCone
        rw [hAt]
        dsimp only [PEqualNP.EdgeOwnership.coneStep]
        rw [List.getD_append_right _ _ _ _ (by rw [hpreLen]), hpreLen, Nat.sub_self]
        have h0 : ∀ v : List ℕ, ([v] : List (List ℕ)).getD 0 [] = v := fun _ => rfl
        rw [h0, List.mem_flatMap]
        constructor
        · rintro ⟨w, hw, hiw⟩
          rw [List.mem_filter, decide_eq_true_eq] at hw
          refine ⟨w, hw.1, hw.2.1, hw.2.2, ?_⟩
          rcases List.mem_cons.mp hiw with rfl | hmem
          · exact Or.inl rfl
          · right
            unfold PEqualNP.EdgeOwnership.cones
            have hPre := coneStep_take j C.gates [] (w - 26) (by simp [List.length_take]; omega)
            rw [← hPre]; exact hmem
        · rintro ⟨w, hw, hw26, hwlt, hcase⟩
          refine ⟨w, List.mem_filter.mpr ⟨hw, decide_eq_true ⟨hw26, hwlt⟩⟩, ?_⟩
          rcases hcase with rfl | hmem
          · exact List.mem_cons.mpr (Or.inl rfl)
          · apply List.mem_cons_of_mem
            unfold PEqualNP.EdgeOwnership.cones at hmem
            have hPre := coneStep_take j C.gates [] (w - 26) (by simp [List.length_take]; omega)
            rw [hPre]; exact hmem
      have inCone_lt : ∀ j < C.gates.length, ∀ i, PEqualNP.EdgeOwnership.InCone 26 C i j → i < j := by
        intro j
        induction j using Nat.strong_induction_on with
        | ind j ih =>
          intro hj i hij
          obtain ⟨w, _, hw26, hwlt, hcase⟩ := (inCone_iff_step j hj i).mp hij
          rcases hcase with rfl | hsub
          · omega
          · have := ih (w - 26) (by omega) (by omega) i hsub; omega
      have inCone_trans : ∀ k < C.gates.length, ∀ i j,
          PEqualNP.EdgeOwnership.InCone 26 C i j →
          PEqualNP.EdgeOwnership.InCone 26 C j k →
          PEqualNP.EdgeOwnership.InCone 26 C i k := by
        intro k
        induction k using Nat.strong_induction_on with
        | ind k ih =>
          intro hk i j hij hjk
          obtain ⟨w, hw, hw26, hwlt, hcase⟩ := (inCone_iff_step k hk j).mp hjk
          rw [inCone_iff_step k hk i]
          rcases hcase with rfl | hsub
          · exact ⟨w, hw, hw26, hwlt, Or.inr hij⟩
          · exact ⟨w, hw, hw26, hwlt, Or.inr (ih (w - 26) (by omega) (by omega) i j hij hsub)⟩
      let ReachesInCone : ℕ → ℕ → Prop := fun w i =>
        w = 26 + i ∨ (26 ≤ w ∧ PEqualNP.EdgeOwnership.InCone 26 C i (w - 26))
      have reachesInCone_step : ∀ j < C.gates.length, ∀ w ∈ (C.gates.getD j dGate).inputs,
          ∀ i, ReachesInCone w i → PEqualNP.EdgeOwnership.InCone 26 C i j := by
        intro j hj w hw i hri
        have hwlt : w < 26 + j := hAO.2.1 j hj w hw
        rw [inCone_iff_step j hj i]
        rcases hri with rfl | ⟨hw26, hic⟩
        · exact ⟨26 + i, hw, by omega, hwlt, Or.inl (by omega)⟩
        · exact ⟨w, hw, hw26, hwlt, Or.inr hic⟩
      let InOutWire : ℕ → Prop := fun w =>
        w = C.output ∨ (26 ≤ w ∧ PEqualNP.EdgeOwnership.InCone 26 C (w - 26) (C.output - 26))
      have inOutWire_input : ∀ j < C.gates.length, InOutWire (26 + j) →
          ∀ w ∈ (C.gates.getD j dGate).inputs, 26 ≤ w → InOutWire w := by
        intro j hj hjOut w hw hw26
        have hwlt : w < 26 + j := hAO.2.1 j hj w hw
        have hwc : PEqualNP.EdgeOwnership.InCone 26 C (w - 26) j :=
          (inCone_iff_step j hj (w - 26)).mpr ⟨w, hw, hw26, hwlt, Or.inl rfl⟩
        right
        refine ⟨hw26, ?_⟩
        rcases hjOut with heq | ⟨_, hic⟩
        · have hjEq : j = C.output - 26 := by omega
          rw [← hjEq]; exact hwc
        · have hsub : 26 + j - 26 = j := by omega
          rw [hsub] at hic
          exact inCone_trans (C.output - 26) (by omega) (w - 26) j hwc hic
      have hPairE0 : PEqualNP.EdgeOwnership.pairInput (0 : Fin 26) (13 : Fin 26) = maskVec 8193 := by
        funext i; revert i; decide
      have hPairP0 : PEqualNP.EdgeOwnership.pairInput (0 : Fin 26) (0 : Fin 26) = maskVec 1 := by
        funext i; revert i; decide
      have hPairL0 : PEqualNP.EdgeOwnership.pairInput (13 : Fin 26) (13 : Fin 26) = maskVec 8192 := by
        funext i; revert i; decide
      have hE0bits : ∀ y : Fin 26, (8193 : ℕ).testBit y.val = true → y.val = 0 ∨ y.val = 13 := by decide
      have mem_filter_any : ∀ (s : Finset ℕ) (p : ℕ → Prop) (inst : DecidablePred p) (a : ℕ),
          a ∈ @Finset.filter ℕ p inst s ↔ a ∈ s ∧ p a := by
        intro s p inst a
        letI : DecidablePred p := inst
        exact Finset.mem_filter
      have mem_tops_iff : ∀ j : ℕ,
          j ∈ PEqualNP.TopForm.tops G C ↔
            j < C.gates.length ∧ (C.gates.getD j dGate).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
              PEqualNP.TopForm.BelowF G C j := by
        intro j
        unfold PEqualNP.TopForm.tops PEqualNP.TopForm.gatesWhere
        rw [mem_filter_any, Finset.mem_range]
        rfl
      have mem_junk_iff : ∀ j : ℕ,
          j ∈ PEqualNP.TopForm.junk G C ↔
            j < C.gates.length ∧ (C.gates.getD j dGate).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
              ¬ PEqualNP.TopForm.BelowF G C j := by
        intro j
        unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
        rw [Finset.mem_filter, Finset.mem_range]
        unfold PEqualNP.CleanedNonEdge.IsDirtyAnd PEqualNP.CleanedNonEdge.IsDirty PEqualNP.TopForm.BelowF
        constructor
        · rintro ⟨hj, hand, _, x, hgx, hfx⟩
          refine ⟨hj, hand, fun hbf => ?_⟩
          have ht := hbf x hgx; rw [hfx] at ht; cases ht
        · rintro ⟨hj, hand, hnot⟩
          refine ⟨hj, hand, hj, ?_⟩
          obtain ⟨x, hx⟩ := not_forall.mp hnot
          obtain ⟨hgx, hfx⟩ := not_imp.mp hx
          exact ⟨x, hgx, Bool.eq_false_iff.mpr hfx⟩
      have noActive_orReach : ∀ w < 26 + C.gates.length,
          (∀ i < C.gates.length, (C.gates.getD i dGate).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            ReachesInCone w i → maskWval 8193 (26 + i) = false) →
          maskWval 8193 w = true → ∃ v ∈ orReach w, maskVec 8193 v = true := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hw hNo hE0
          by_cases hw26 : w < 26
          · dsimp only [maskWval] at hE0
            rw [wval_input (maskVec 8193) w hw26] at hE0
            exact ⟨⟨w, hw26⟩, by rw [orReach_input w hw26]; exact Finset.mem_singleton_self _, hE0⟩
          · let j := w - 26
            have hj : j < C.gates.length := by omega
            have hwEq : 26 + j = w := by omega
            rw [← hwEq] at hNo hE0 ⊢
            have hgMem : C.gates.getD j dGate ∈ C.gates := by
              rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
            have hgEq := list_len2 _ (hAO.2.2 _ hgMem)
            let a := (C.gates.getD j dGate).inputs.getD 0 0
            let c := (C.gates.getD j dGate).inputs.getD 1 0
            have haMem : a ∈ (C.gates.getD j dGate).inputs := by rw [hgEq]; simp [a]
            have hcMem : c ∈ (C.gates.getD j dGate).inputs := by rw [hgEq]; simp [c]
            have haLt : a < 26 + j := hAO.2.1 j hj _ haMem
            have hcLt : c < 26 + j := hAO.2.1 j hj _ hcMem
            have hrg := orReach_gate j hj
            dsimp only at hrg
            rcases hAO.1 _ hgMem with hand | hor
            · have hf := hNo j hj hand (Or.inl rfl)
              rw [hf] at hE0; cases hE0
            · dsimp only [maskWval] at hE0
              rw [wval_gate_or (maskVec 8193) j hj hor, Bool.or_eq_true] at hE0
              rw [hrg.1 hor]
              rcases hE0 with ha | hc
              · obtain ⟨v, hv, hvE⟩ := ih a (by omega) (by omega)
                  (fun i hi handi hri => hNo i hi handi (Or.inr ⟨by omega, by simpa using reachesInCone_step j hj a haMem i hri⟩)) ha
                exact ⟨v, Finset.mem_union_left _ hv, hvE⟩
              · obtain ⟨v, hv, hvE⟩ := ih c (by omega) (by omega)
                  (fun i hi handi hri => hNo i hi handi (Or.inr ⟨by omega, by simpa using reachesInCone_step j hj c hcMem i hri⟩)) hc
                exact ⟨v, Finset.mem_union_right _ hv, hvE⟩
      have active_decomp : ∀ (J : ℕ), ∀ w < 26 + C.gates.length,
          (∀ i < C.gates.length, (C.gates.getD i dGate).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            ReachesInCone w i → maskWval 8193 (26 + i) = true → i = J) →
          maskWval 8193 w = true →
          (∃ v ∈ orReach w, maskVec 8193 v = true) ∨
          ((∀ x : Fin 26 → Bool, wval x (26 + J) = true → wval x w = true) ∧
           (∀ isL : ℕ → Bool,
             (PEqualNP.ReadK.linearParts C isL x013).getD w (false, false) = (false, false) →
             (PEqualNP.ReadK.linearParts C isL x013).getD (26 + J) (false, false) = (false, false))) := by
        intro J w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hw hOnly hE0
          by_cases hw26 : w < 26
          · dsimp only [maskWval] at hE0
            rw [wval_input (maskVec 8193) w hw26] at hE0
            exact Or.inl ⟨⟨w, hw26⟩, by rw [orReach_input w hw26]; exact Finset.mem_singleton_self _, hE0⟩
          · let j := w - 26
            have hj : j < C.gates.length := by omega
            have hwEq : 26 + j = w := by omega
            rw [← hwEq] at hOnly hE0 ⊢
            have hgMem : C.gates.getD j dGate ∈ C.gates := by
              rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
            have hgEq := list_len2 _ (hAO.2.2 _ hgMem)
            let a := (C.gates.getD j dGate).inputs.getD 0 0
            let c := (C.gates.getD j dGate).inputs.getD 1 0
            have haMem : a ∈ (C.gates.getD j dGate).inputs := by rw [hgEq]; simp [a]
            have hcMem : c ∈ (C.gates.getD j dGate).inputs := by rw [hgEq]; simp [c]
            have haLt : a < 26 + j := hAO.2.1 j hj _ haMem
            have hcLt : c < 26 + j := hAO.2.1 j hj _ hcMem
            have hrg := orReach_gate j hj
            dsimp only at hrg
            rcases hAO.1 _ hgMem with hand | hor
            · have hjJ : j = J := hOnly j hj hand (Or.inl rfl) hE0
              rw [hjJ]
              exact Or.inr ⟨fun _ h => h, fun _ h => h⟩
            · dsimp only [maskWval] at hE0
              rw [wval_gate_or (maskVec 8193) j hj hor, Bool.or_eq_true] at hE0
              rcases hE0 with ha | hc
              · rcases ih a (by omega) (by omega)
                    (fun i hi handi hri hE => hOnly i hi handi (Or.inr ⟨by omega, by simpa using reachesInCone_step j hj a haMem i hri⟩) hE) ha with
                  ⟨v, hv, hvE⟩ | ⟨hW, hLP⟩
                · exact Or.inl ⟨v, by rw [hrg.1 hor]; exact Finset.mem_union_left _ hv, hvE⟩
                · refine Or.inr ⟨fun x hx => ?_, fun isL hlp => ?_⟩
                  · rw [wval_gate_or x j hj hor]; change (wval x a || wval x c) = true; rw [hW x hx]; rfl
                  · have hG := (lp_gate isL x013 (by simp [x013]) j hj).1 hor
                    dsimp only at hG; rw [hG] at hlp
                    apply hLP isL
                    have h1 := (Bool.or_eq_false_iff.mp (congrArg Prod.fst hlp)).1
                    have h2 := (Bool.or_eq_false_iff.mp (congrArg Prod.snd hlp)).1
                    exact Prod.ext h1 h2
              · rcases ih c (by omega) (by omega)
                    (fun i hi handi hri hE => hOnly i hi handi (Or.inr ⟨by omega, by simpa using reachesInCone_step j hj c hcMem i hri⟩) hE) hc with
                  ⟨v, hv, hvE⟩ | ⟨hW, hLP⟩
                · exact Or.inl ⟨v, by rw [hrg.1 hor]; exact Finset.mem_union_right _ hv, hvE⟩
                · refine Or.inr ⟨fun x hx => ?_, fun isL hlp => ?_⟩
                  · rw [wval_gate_or x j hj hor]; change (wval x a || wval x c) = true; rw [hW x hx]; simp
                  · have hG := (lp_gate isL x013 (by simp [x013]) j hj).1 hor
                    dsimp only at hG; rw [hG] at hlp
                    apply hLP isL
                    have h1 := (Bool.or_eq_false_iff.mp (congrArg Prod.fst hlp)).2
                    have h2 := (Bool.or_eq_false_iff.mp (congrArg Prod.snd hlp)).2
                    exact Prod.ext h1 h2
      have lp_ne_zero_of_orReach : ∀ w < 26 + C.gates.length,
          (∃ v ∈ orReach w, maskVec 8193 v = true) →
          (PEqualNP.ReadK.linearParts C isLine x013).getD w (false, false) ≠ (false, false) ∧
          (PEqualNP.ReadK.linearParts C (fun i => !isLine i) x013).getD w (false, false) ≠ (false, false) := by
        intro w hw hExOR
        obtain ⟨v, hv, hvE⟩ := hExOR
        rcases hE0bits v hvE with h0 | h13
        · have hvEq : v = ⟨0, by decide⟩ := Fin.ext h0
          rw [hvEq] at hv
          obtain ⟨h1, h2⟩ := hZeroOrReach w hw hv
          exact ⟨fun heq => (by rw [heq] at h1; cases h1), fun heq => (by rw [heq] at h2; cases h2)⟩
        · have hvEq : v = ⟨13, by decide⟩ := Fin.ext h13
          rw [hvEq] at hv
          obtain ⟨h1, h2⟩ := h13OrReach w hw hv
          exact ⟨fun heq => (by rw [heq] at h2; cases h2), fun heq => (by rw [heq] at h1; cases h1)⟩
      have and_lp_zero_cases : ∀ (isL : ℕ → Bool) (j : ℕ), j < C.gates.length →
          (C.gates.getD j dGate).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (PEqualNP.ReadK.linearParts C isL x013).getD (26 + j) (false, false) = (false, false) →
          (((PEqualNP.ReadK.linearParts C isL x013).getD ((C.gates.getD j dGate).inputs.getD 0 0) (false, false)).1 = false ∧
           ((PEqualNP.ReadK.linearParts C isL x013).getD ((C.gates.getD j dGate).inputs.getD 1 0) (false, false)).1 = false) ∨
          (((PEqualNP.ReadK.linearParts C isL x013).getD ((C.gates.getD j dGate).inputs.getD 0 0) (false, false)).1 = true ∧
           (PEqualNP.ReadK.linearParts C isL x013).getD ((C.gates.getD j dGate).inputs.getD 1 0) (false, false) = (false, false)) ∨
          (((PEqualNP.ReadK.linearParts C isL x013).getD ((C.gates.getD j dGate).inputs.getD 1 0) (false, false)).1 = true ∧
           (PEqualNP.ReadK.linearParts C isL x013).getD ((C.gates.getD j dGate).inputs.getD 0 0) (false, false) = (false, false)) := by
        intro isL j hj hand hlp
        let lp := fun k => (PEqualNP.ReadK.linearParts C isL x013).getD k (false, false)
        let a := (C.gates.getD j dGate).inputs.getD 0 0
        let c := (C.gates.getD j dGate).inputs.getD 1 0
        change lp (26 + j) = (false, false) at hlp
        have hG := (lp_gate isL x013 (by simp [x013]) j hj).2 hand
        dsimp only at hG
        change lp (26 + j) = _ at hG
        rw [hG] at hlp
        have h1 : ((lp a).1 && (lp c).1) = false := congrArg Prod.fst hlp
        have h2 : (((lp a).1 && (lp c).2) || ((lp a).2 && (lp c).1)) = false := congrArg Prod.snd hlp
        cases ha1 : (lp a).1 <;> cases hc1 : (lp c).1
        · exact Or.inl ⟨rfl, rfl⟩
        · rw [ha1, hc1] at h2
          simp only [Bool.false_and, Bool.false_or, Bool.and_true] at h2
          exact Or.inr (Or.inr ⟨rfl, Prod.ext ha1 h2⟩)
        · rw [ha1, hc1] at h2
          simp only [Bool.true_and, Bool.and_false, Bool.or_false] at h2
          exact Or.inr (Or.inl ⟨rfl, Prod.ext hc1 h2⟩)
        · rw [ha1, hc1] at h1; cases h1
      have both_orReach_kill : ∀ (j : ℕ), j < C.gates.length →
          (C.gates.getD j dGate).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (PEqualNP.ReadK.linearParts C isLine x013).getD (26 + j) (false, false) = (false, false) →
          (PEqualNP.ReadK.linearParts C (fun i => !isLine i) x013).getD (26 + j) (false, false) = (false, false) →
          (∃ v ∈ orReach ((C.gates.getD j dGate).inputs.getD 0 0), maskVec 8193 v = true) →
          (∃ v ∈ orReach ((C.gates.getD j dGate).inputs.getD 1 0), maskVec 8193 v = true) →
          False := by
        intro j hj hand hlp0 hlp13 haOR hcOR
        have hgMem : C.gates.getD j dGate ∈ C.gates := by
          rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
        have hgEq := list_len2 _ (hAO.2.2 _ hgMem)
        let a := (C.gates.getD j dGate).inputs.getD 0 0
        let c := (C.gates.getD j dGate).inputs.getD 1 0
        have haLt : a < 26 + j := hAO.2.1 j hj _ (by change _ ∈ (C.gates.getD j dGate).inputs; rw [hgEq]; simp [a])
        have hcLt : c < 26 + j := hAO.2.1 j hj _ (by change _ ∈ (C.gates.getD j dGate).inputs; rw [hgEq]; simp [c])
        obtain ⟨ha0Ne, ha13Ne⟩ := lp_ne_zero_of_orReach a (by omega) haOR
        obtain ⟨hc0Ne, hc13Ne⟩ := lp_ne_zero_of_orReach c (by omega) hcOR
        have ha0F : ((PEqualNP.ReadK.linearParts C isLine x013).getD a (false, false)).1 = false := by
          rcases and_lp_zero_cases isLine j hj hand hlp0 with ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨_, h3⟩
          · exact h1
          · exact absurd h2 hc0Ne
          · exact absurd h3 ha0Ne
        have ha13F : ((PEqualNP.ReadK.linearParts C (fun i => !isLine i) x013).getD a (false, false)).1 = false := by
          rcases and_lp_zero_cases (fun i => !isLine i) j hj hand hlp13 with ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨_, h3⟩
          · exact h1
          · exact absurd h2 hc13Ne
          · exact absurd h3 ha13Ne
        obtain ⟨va, hva, hvaE⟩ := haOR
        rcases hE0bits va hvaE with h0 | h13
        · have hvEq : va = ⟨0, by decide⟩ := Fin.ext h0
          rw [hvEq] at hva
          have hT := (hZeroOrReach a (by omega) hva).1
          rw [ha0F] at hT; cases hT
        · have hvEq : va = ⟨13, by decide⟩ := Fin.ext h13
          rw [hvEq] at hva
          have hT := (h13OrReach a (by omega) hva).1
          rw [ha13F] at hT; cases hT
      have one_side_active_kill : ∀ (h J : ℕ) (hh : h < C.gates.length) (hJLt : J < C.gates.length),
          (C.gates.getD h dGate).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (C.gates.getD J dGate).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (PEqualNP.ReadK.linearParts C isLine x013).getD (26 + h) (false, false) = (false, false) →
          (PEqualNP.ReadK.linearParts C (fun i => !isLine i) x013).getD (26 + h) (false, false) = (false, false) →
          maskWval 8193 (26 + J) = true →
          (∀ i < C.gates.length, (C.gates.getD i dGate).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            PEqualNP.EdgeOwnership.InCone 26 C i J → maskWval 8193 (26 + i) = false) →
          ∀ w1 w2 : ℕ, w1 < 26 + h → w2 < 26 + h →
          ((w1 = (C.gates.getD h dGate).inputs.getD 0 0 ∧ w2 = (C.gates.getD h dGate).inputs.getD 1 0) ∨
           (w1 = (C.gates.getD h dGate).inputs.getD 1 0 ∧ w2 = (C.gates.getD h dGate).inputs.getD 0 0)) →
          (∀ x : Fin 26 → Bool, wval x (26 + J) = true → wval x w1 = true) →
          (∀ isL : ℕ → Bool,
            (PEqualNP.ReadK.linearParts C isL x013).getD w1 (false, false) = (false, false) →
            (PEqualNP.ReadK.linearParts C isL x013).getD (26 + J) (false, false) = (false, false)) →
          (∃ v ∈ orReach w2, maskVec 8193 v = true) →
          False := by
        intro h J hh hJLt hHand hJAnd hhLP0 hhLP13 hJE0 hNoBelowJ w1 w2 hw1Lt hw2Lt hSwap hW1 hLP1 hw2OR
        have hJMem : C.gates.getD J dGate ∈ C.gates := by
          rw [List.getD_eq_getElem _ _ hJLt]; exact List.getElem_mem hJLt
        have hJEq := list_len2 _ (hAO.2.2 _ hJMem)
        let aJ := (C.gates.getD J dGate).inputs.getD 0 0
        let cJ := (C.gates.getD J dGate).inputs.getD 1 0
        have haJMem : aJ ∈ (C.gates.getD J dGate).inputs := by rw [hJEq]; simp [aJ]
        have hcJMem : cJ ∈ (C.gates.getD J dGate).inputs := by rw [hJEq]; simp [cJ]
        have haJLt : aJ < 26 + J := hAO.2.1 J hJLt _ haJMem
        have hcJLt : cJ < 26 + J := hAO.2.1 J hJLt _ hcJMem
        dsimp only [maskWval] at hJE0
        rw [wval_gate_and (maskVec 8193) J hJLt hJAnd, Bool.and_eq_true] at hJE0
        have haJOR : ∃ v ∈ orReach aJ, maskVec 8193 v = true :=
          noActive_orReach aJ (by omega)
            (fun i hi handi hri => hNoBelowJ i hi handi (reachesInCone_step J hJLt aJ haJMem i hri)) hJE0.1
        have hcJOR : ∃ v ∈ orReach cJ, maskVec 8193 v = true :=
          noActive_orReach cJ (by omega)
            (fun i hi handi hri => hNoBelowJ i hi handi (reachesInCone_step J hJLt cJ hcJMem i hri)) hJE0.2
        obtain ⟨haJ0Ne, haJ13Ne⟩ := lp_ne_zero_of_orReach aJ (by omega) haJOR
        obtain ⟨hcJ0Ne, hcJ13Ne⟩ := lp_ne_zero_of_orReach cJ (by omega) hcJOR
        obtain ⟨ya, hya, hyaE⟩ := haJOR
        obtain ⟨yc, hyc, hycE⟩ := hcJOR
        obtain ⟨x, hx, hxE⟩ := hw2OR
        rcases hE0bits x hxE with hx0 | hx13
        · have hxEq : x = ⟨0, by decide⟩ := Fin.ext hx0
          rw [hxEq] at hx
          obtain ⟨hw2_0_1, hw2_13_2⟩ := hZeroOrReach w2 (by omega) hx
          have hw1LP0 : (PEqualNP.ReadK.linearParts C isLine x013).getD w1 (false, false) = (false, false) := by
            rcases and_lp_zero_cases isLine h hh hHand hhLP0 with ⟨h1, h2⟩ | ⟨_, h2⟩ | ⟨_, h3⟩
            · rcases hSwap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · rw [hw2_0_1] at h2; cases h2
              · rw [hw2_0_1] at h1; cases h1
            · rcases hSwap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · rw [h2] at hw2_0_1; cases hw2_0_1
              · exact h2
            · rcases hSwap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact h3
              · rw [h3] at hw2_0_1; cases hw2_0_1
          have hJLP0 := hLP1 isLine hw1LP0
          have haJ0F : ((PEqualNP.ReadK.linearParts C isLine x013).getD aJ (false, false)).1 = false := by
            rcases and_lp_zero_cases isLine J hJLt hJAnd hJLP0 with ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨_, h3⟩
            · exact h1
            · exact absurd h2 hcJ0Ne
            · exact absurd h3 haJ0Ne
          have hcJ0F : ((PEqualNP.ReadK.linearParts C isLine x013).getD cJ (false, false)).1 = false := by
            rcases and_lp_zero_cases isLine J hJLt hJAnd hJLP0 with ⟨_, h1⟩ | ⟨_, h2⟩ | ⟨_, h3⟩
            · exact h1
            · exact absurd h2 hcJ0Ne
            · exact absurd h3 haJ0Ne
          have hya13 : ya = ⟨13, by decide⟩ := by
            rcases hE0bits ya hyaE with h0 | h13
            · exfalso
              have hEq : ya = ⟨0, by decide⟩ := Fin.ext h0
              rw [hEq] at hya
              have hT := (hZeroOrReach aJ (by omega) hya).1
              rw [haJ0F] at hT; cases hT
            · exact Fin.ext h13
          have hyc13 : yc = ⟨13, by decide⟩ := by
            rcases hE0bits yc hycE with h0 | h13
            · exfalso
              have hEq : yc = ⟨0, by decide⟩ := Fin.ext h0
              rw [hEq] at hyc
              have hT := (hZeroOrReach cJ (by omega) hyc).1
              rw [hcJ0F] at hT; cases hT
            · exact Fin.ext h13
          have haJ8192 : wval (maskVec 8192) aJ = true :=
            wval_of_mem_orReach (maskVec 8192) aJ (by omega) ya hya (by rw [hya13]; decide)
          have hcJ8192 : wval (maskVec 8192) cJ = true :=
            wval_of_mem_orReach (maskVec 8192) cJ (by omega) yc hyc (by rw [hyc13]; decide)
          have hJ8192 : wval (maskVec 8192) (26 + J) = true := by
            rw [wval_gate_and (maskVec 8192) J hJLt hJAnd]
            change (wval (maskVec 8192) aJ && wval (maskVec 8192) cJ) = true
            rw [haJ8192, hcJ8192]; rfl
          have hw1_8192 : maskWval 8192 w1 = true := hW1 (maskVec 8192) hJ8192
          have hw1_13_1 : ((PEqualNP.ReadK.linearParts C (fun i => !isLine i) x013).getD w1 (false, false)).1 = true := by
            rw [lp_fst_notIsLine w1 (by omega)]; exact hw1_8192
          have hG13 := (lp_gate (fun i => !isLine i) x013 (by simp [x013]) h hh).2 hHand
          dsimp only at hG13
          rw [hG13] at hhLP13
          have hSnd := congrArg Prod.snd hhLP13
          rcases hSwap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [hw1_13_1, hw2_13_2] at hSnd; cases hSnd
          · rw [hw1_13_1, hw2_13_2] at hSnd; simp at hSnd
        · have hxEq : x = ⟨13, by decide⟩ := Fin.ext hx13
          rw [hxEq] at hx
          obtain ⟨hw2_13_1, hw2_0_2⟩ := h13OrReach w2 (by omega) hx
          have hw1LP13 : (PEqualNP.ReadK.linearParts C (fun i => !isLine i) x013).getD w1 (false, false) = (false, false) := by
            rcases and_lp_zero_cases (fun i => !isLine i) h hh hHand hhLP13 with ⟨h1, h2⟩ | ⟨_, h2⟩ | ⟨_, h3⟩
            · rcases hSwap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · rw [hw2_13_1] at h2; cases h2
              · rw [hw2_13_1] at h1; cases h1
            · rcases hSwap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · rw [h2] at hw2_13_1; cases hw2_13_1
              · exact h2
            · rcases hSwap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact h3
              · rw [h3] at hw2_13_1; cases hw2_13_1
          have hJLP13 := hLP1 (fun i => !isLine i) hw1LP13
          have haJ13F : ((PEqualNP.ReadK.linearParts C (fun i => !isLine i) x013).getD aJ (false, false)).1 = false := by
            rcases and_lp_zero_cases (fun i => !isLine i) J hJLt hJAnd hJLP13 with ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨_, h3⟩
            · exact h1
            · exact absurd h2 hcJ13Ne
            · exact absurd h3 haJ13Ne
          have hcJ13F : ((PEqualNP.ReadK.linearParts C (fun i => !isLine i) x013).getD cJ (false, false)).1 = false := by
            rcases and_lp_zero_cases (fun i => !isLine i) J hJLt hJAnd hJLP13 with ⟨_, h1⟩ | ⟨_, h2⟩ | ⟨_, h3⟩
            · exact h1
            · exact absurd h2 hcJ13Ne
            · exact absurd h3 haJ13Ne
          have hya0 : ya = ⟨0, by decide⟩ := by
            rcases hE0bits ya hyaE with h0 | h13
            · exact Fin.ext h0
            · exfalso
              have hEq : ya = ⟨13, by decide⟩ := Fin.ext h13
              rw [hEq] at hya
              have hT := (h13OrReach aJ (by omega) hya).1
              rw [haJ13F] at hT; cases hT
          have hyc0 : yc = ⟨0, by decide⟩ := by
            rcases hE0bits yc hycE with h0 | h13
            · exact Fin.ext h0
            · exfalso
              have hEq : yc = ⟨13, by decide⟩ := Fin.ext h13
              rw [hEq] at hyc
              have hT := (h13OrReach cJ (by omega) hyc).1
              rw [hcJ13F] at hT; cases hT
          have haJ1 : wval (maskVec 1) aJ = true :=
            wval_of_mem_orReach (maskVec 1) aJ (by omega) ya hya (by rw [hya0]; decide)
          have hcJ1 : wval (maskVec 1) cJ = true :=
            wval_of_mem_orReach (maskVec 1) cJ (by omega) yc hyc (by rw [hyc0]; decide)
          have hJ1 : wval (maskVec 1) (26 + J) = true := by
            rw [wval_gate_and (maskVec 1) J hJLt hJAnd]
            change (wval (maskVec 1) aJ && wval (maskVec 1) cJ) = true
            rw [haJ1, hcJ1]; rfl
          have hw1_1 : maskWval 1 w1 = true := hW1 (maskVec 1) hJ1
          have hw1_0_1 : ((PEqualNP.ReadK.linearParts C isLine x013).getD w1 (false, false)).1 = true := by
            rw [lp_fst_isLine w1 (by omega)]; exact hw1_1
          have hG0 := (lp_gate isLine x013 (by simp [x013]) h hh).2 hHand
          dsimp only at hG0
          rw [hG0] at hhLP0
          have hSnd := congrArg Prod.snd hhLP0
          rcases hSwap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [hw1_0_1, hw2_0_2] at hSnd; cases hSnd
          · rw [hw1_0_1, hw2_0_2] at hSnd; simp at hSnd
      let P : ℕ → Prop := fun k =>
        k < 26 + C.gates.length ∧
        InOutWire k ∧
        (PEqualNP.ReadK.linearParts C isLine x013).getD k (false, false) = (false, false) ∧
        (PEqualNP.ReadK.linearParts C (fun i => !isLine i) x013).getD k (false, false) = (false, false) ∧
        maskWval 8193 k = true
      have hNotInput : ∀ w < 26,
          (PEqualNP.ReadK.linearParts C isLine x013).getD w (false, false) = (false, false) →
          (PEqualNP.ReadK.linearParts C (fun i => !isLine i) x013).getD w (false, false) = (false, false) →
          maskWval 8193 w = true → False := by
        intro w hw26 hwLP0 hwLP1 hwE0
        dsimp only [maskWval] at hwE0
        rw [wval_input (maskVec 8193) w hw26] at hwE0
        rcases hE0bits ⟨w, hw26⟩ hwE0 with h0 | h13
        · have hT : ((PEqualNP.ReadK.linearParts C isLine x013).getD w (false, false)).1 = true := by
            rw [lp_fst_isLine w (by omega)]
            dsimp only [maskWval]; rw [wval_input (maskVec 1) w hw26]
            dsimp only [maskVec]; change w = 0 at h0; rw [h0]; decide
          rw [hwLP0] at hT; cases hT
        · have hT : ((PEqualNP.ReadK.linearParts C (fun i => !isLine i) x013).getD w (false, false)).1 = true := by
            rw [lp_fst_notIsLine w (by omega)]
            dsimp only [maskWval]; rw [wval_input (maskVec 8192) w hw26]
            dsimp only [maskVec]; change w = 13 at h13; rw [h13]; decide
          rw [hwLP1] at hT; cases hT
      have hOutE0 : maskWval 8193 C.output = true := (hSpec (maskVec 8193)).mpr pgFun_e0
      have hEx : ∃ k, P k := ⟨C.output, hOutBd.2, Or.inl rfl, hLP0Out, hLP1Out, hOutE0⟩
      set k := Nat.find hEx with hkDef
      have hkSpec : P k := hkDef ▸ Nat.find_spec hEx
      obtain ⟨hkLt, hkOut, hkLP0, hkLP1, hkE0⟩ := hkSpec
      have hkMin : ∀ m < k, ¬ P m := fun m hm => Nat.find_min hEx (hkDef ▸ hm)
      have hkGe26 : 26 ≤ k := by
        by_contra hlt26
        exact hNotInput k (by omega) hkLP0 hkLP1 hkE0
      let h := k - 26
      have hh : h < C.gates.length := by omega
      have hkEq : 26 + h = k := by omega
      rw [← hkEq] at hkOut hkLP0 hkLP1 hkE0
      have hhInOut : PEqualNP.Core.InOutputCone 26 C h := by
        refine ⟨hh, ?_⟩
        rcases hkOut with heq | ⟨_, hic⟩
        · exact Or.inl heq.symm
        · right
          refine ⟨hOutBd.1, ?_⟩
          have hsub : 26 + h - 26 = h := by omega
          rw [hsub] at hic; exact hic
      have hgMem : C.gates.getD h dGate ∈ C.gates := by
        rw [List.getD_eq_getElem _ _ hh]; exact List.getElem_mem hh
      have hgEq := list_len2 _ (hAO.2.2 _ hgMem)
      let u := (C.gates.getD h dGate).inputs.getD 0 0
      let v := (C.gates.getD h dGate).inputs.getD 1 0
      have huMem : u ∈ (C.gates.getD h dGate).inputs := by rw [hgEq]; simp [u]
      have hvMem : v ∈ (C.gates.getD h dGate).inputs := by rw [hgEq]; simp [v]
      have huLt : u < 26 + h := hAO.2.1 h hh _ huMem
      have hvLt : v < 26 + h := hAO.2.1 h hh _ hvMem
      have hHand : (C.gates.getD h dGate).op = PEqualNP.CircuitLowerBounds.GateOp.and := by
        rcases hAO.1 _ hgMem with hand | hor
        · exact hand
        · exfalso
          have hG0 := (lp_gate isLine x013 (by simp [x013]) h hh).1 hor
          have hG1 := (lp_gate (fun i => !isLine i) x013 (by simp [x013]) h hh).1 hor
          dsimp only at hG0 hG1
          rw [hG0] at hkLP0
          rw [hG1] at hkLP1
          have huLP0 : (PEqualNP.ReadK.linearParts C isLine x013).getD u (false, false) = (false, false) :=
            Prod.ext (Bool.or_eq_false_iff.mp (congrArg Prod.fst hkLP0)).1
              (Bool.or_eq_false_iff.mp (congrArg Prod.snd hkLP0)).1
          have hvLP0 : (PEqualNP.ReadK.linearParts C isLine x013).getD v (false, false) = (false, false) :=
            Prod.ext (Bool.or_eq_false_iff.mp (congrArg Prod.fst hkLP0)).2
              (Bool.or_eq_false_iff.mp (congrArg Prod.snd hkLP0)).2
          have huLP1 : (PEqualNP.ReadK.linearParts C (fun i => !isLine i) x013).getD u (false, false) = (false, false) :=
            Prod.ext (Bool.or_eq_false_iff.mp (congrArg Prod.fst hkLP1)).1
              (Bool.or_eq_false_iff.mp (congrArg Prod.snd hkLP1)).1
          have hvLP1 : (PEqualNP.ReadK.linearParts C (fun i => !isLine i) x013).getD v (false, false) = (false, false) :=
            Prod.ext (Bool.or_eq_false_iff.mp (congrArg Prod.fst hkLP1)).2
              (Bool.or_eq_false_iff.mp (congrArg Prod.snd hkLP1)).2
          dsimp only [maskWval] at hkE0
          rw [wval_gate_or (maskVec 8193) h hh hor, Bool.or_eq_true] at hkE0
          rcases hkE0 with huE | hvE
          · by_cases hu26 : u < 26
            · exact hNotInput u hu26 huLP0 huLP1 huE
            · exact hkMin u (by omega) ⟨by omega, inOutWire_input h hh hkOut u huMem (by omega), huLP0, huLP1, huE⟩
          · by_cases hv26 : v < 26
            · exact hNotInput v hv26 hvLP0 hvLP1 hvE
            · exact hkMin v (by omega) ⟨by omega, inOutWire_input h hh hkOut v hvMem (by omega), hvLP0, hvLP1, hvE⟩
      have hhPairE0 : PEqualNP.EdgeOwnership.gateVal 26 C h (PEqualNP.EdgeOwnership.pairInput 0 13) = true := by
        rw [hPairE0]; exact hkE0
      have hhUnit0 : PEqualNP.EdgeOwnership.gateVal 26 C h (PEqualNP.EdgeOwnership.pairInput 0 0) = false := by
        rw [hPairP0]
        change maskWval 1 (26 + h) = false
        rw [← lp_fst_isLine (26 + h) (by omega), hkLP0]
      have hhUnit13 : PEqualNP.EdgeOwnership.gateVal 26 C h (PEqualNP.EdgeOwnership.pairInput 13 13) = false := by
        rw [hPairL0]
        change maskWval 8192 (26 + h) = false
        rw [← lp_fst_notIsLine (26 + h) (by omega), hkLP1]
      have hhNotSR : ¬ PEqualNP.ReadK.IsSingleRead (PEqualNP.Core.atGate 26 C h) 26 isLine [(0, 13)] := by
        intro hSR
        have h1 : PEqualNP.ReadK.lineSingle (PEqualNP.Core.atGate 26 C h) 26 isLine 0 13 = false := by
          unfold PEqualNP.ReadK.lineSingle PEqualNP.Core.atGate
          change ((PEqualNP.ReadK.linearParts C isLine x013).getD (26 + h) (false, false)).2 = false
          rw [hkLP0]
        have h2 : PEqualNP.ReadK.lineSingle (PEqualNP.Core.atGate 26 C h) 26 (fun i => !isLine i) 0 13 = false := by
          unfold PEqualNP.ReadK.lineSingle PEqualNP.Core.atGate
          change ((PEqualNP.ReadK.linearParts C (fun i => !isLine i) x013).getD (26 + h) (false, false)).2 = false
          rw [hkLP1]
        unfold PEqualNP.ReadK.IsSingleRead PEqualNP.ReadK.doubleReread at hSR
        simp [h1, h2] at hSR
      dsimp only [maskWval] at hkE0
      rw [wval_gate_and (maskVec 8193) h hh hHand, Bool.and_eq_true] at hkE0
      have huE0 : maskWval 8193 u = true := hkE0.1
      have hvE0 : maskWval 8193 v = true := hkE0.2
      by_cases hCleanIn : ∃ i ∈ PEqualNP.TopForm.tops G C,
          PEqualNP.EdgeOwnership.InCone 26 C i h ∧
          PEqualNP.EdgeOwnership.gateVal 26 C i (PEqualNP.EdgeOwnership.pairInput 0 13) = true
      · exact nestedClean C h63 h64 hAO hNodup hCircuitFun hNotSR
          ⟨h, hhInOut, hHand, hhPairE0, hhUnit0, hhUnit13, hhNotSR, hCleanIn⟩
      · have hNoCleanIn : ∀ i ∈ PEqualNP.TopForm.tops G C, PEqualNP.EdgeOwnership.InCone 26 C i h →
            PEqualNP.EdgeOwnership.gateVal 26 C i (PEqualNP.EdgeOwnership.pairInput 0 13) = false := by
          intro i hi hic
          cases hv : PEqualNP.EdgeOwnership.gateVal 26 C i (PEqualNP.EdgeOwnership.pairInput 0 13) with
          | false => rfl
          | true => exact absurd ⟨i, hi, hic, hv⟩ hCleanIn
        have hActiveJunk : ∀ i < C.gates.length, (C.gates.getD i dGate).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            PEqualNP.EdgeOwnership.InCone 26 C i h → maskWval 8193 (26 + i) = true →
            i ∈ PEqualNP.TopForm.junk G C := by
          intro i hi hiAnd hiCone hiE0
          rw [mem_junk_iff]
          refine ⟨hi, hiAnd, fun hbf => ?_⟩
          have hiTop : i ∈ PEqualNP.TopForm.tops G C := (mem_tops_iff i).mpr ⟨hi, hiAnd, hbf⟩
          have hF := hNoCleanIn i hiTop hiCone
          rw [hPairE0] at hF
          change maskWval 8193 (26 + i) = false at hF
          rw [hiE0] at hF; cases hF
        have hActiveEx : ∃ i < C.gates.length, (C.gates.getD i dGate).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
            PEqualNP.EdgeOwnership.InCone 26 C i h ∧ maskWval 8193 (26 + i) = true := by
          by_contra hNone
          have hNoA : ∀ i < C.gates.length, (C.gates.getD i dGate).op = PEqualNP.CircuitLowerBounds.GateOp.and →
              PEqualNP.EdgeOwnership.InCone 26 C i h → maskWval 8193 (26 + i) = false := by
            intro i hi hiAnd hiCone
            cases hv : maskWval 8193 (26 + i) with
            | false => rfl
            | true => exact absurd ⟨i, hi, hiAnd, hiCone, hv⟩ hNone
          have huOR := noActive_orReach u (by omega)
            (fun i hi hiAnd hri => hNoA i hi hiAnd (reachesInCone_step h hh u huMem i hri)) huE0
          have hvOR := noActive_orReach v (by omega)
            (fun i hi hiAnd hri => hNoA i hi hiAnd (reachesInCone_step h hh v hvMem i hri)) hvE0
          exact both_orReach_kill h hh hHand hkLP0 hkLP1 huOR hvOR
        obtain ⟨i0, hi0Lt, hi0And, hi0Cone, hi0E0⟩ := hActiveEx
        have hi0Junk : i0 ∈ PEqualNP.TopForm.junk G C := hActiveJunk i0 hi0Lt hi0And hi0Cone hi0E0
        have hi0Val : PEqualNP.EdgeOwnership.gateVal 26 C i0 (PEqualNP.EdgeOwnership.pairInput 0 13) = true := by
          rw [hPairE0]; exact hi0E0
        by_cases hhJunk : h ∈ PEqualNP.TopForm.junk G C
        · exact nestedJunk C h63 h64 hAO hNodup hCircuitFun hNotSR
            ⟨h, hhJunk, hhInOut, hhPairE0, hhUnit0, hhUnit13, hhNotSR, hNoCleanIn, i0, hi0Junk, hi0Cone, hi0Val⟩
        · have hhBF : PEqualNP.TopForm.BelowF G C h := by
            by_contra hnot
            exact hhJunk ((mem_junk_iff h).mpr ⟨hh, hHand, hnot⟩)
          have hhTop : h ∈ PEqualNP.TopForm.tops G C := (mem_tops_iff h).mpr ⟨hh, hHand, hhBF⟩
          by_cases hSecond : ∃ i1 < C.gates.length, i1 ≠ i0 ∧
              (C.gates.getD i1 dGate).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
              PEqualNP.EdgeOwnership.InCone 26 C i1 h ∧ maskWval 8193 (26 + i1) = true
          · obtain ⟨i1, hi1Lt, hne, hi1And, hi1Cone, hi1E0⟩ := hSecond
            have hi1Junk : i1 ∈ PEqualNP.TopForm.junk G C := hActiveJunk i1 hi1Lt hi1And hi1Cone hi1E0
            have hi1Val : PEqualNP.EdgeOwnership.gateVal 26 C i1 (PEqualNP.EdgeOwnership.pairInput 0 13) = true := by
              rw [hPairE0]; exact hi1E0
            exact cleanAboveTwoJunk C h63 h64 hAO hNodup hCircuitFun hNotSR
              ⟨h, hhTop, hhInOut, hhPairE0, hhNotSR, hNoCleanIn,
                i0, hi0Junk, i1, hi1Junk, hne.symm, hi0Cone, hi1Cone, hi0Val, hi1Val⟩
          · have hOnlyI0 : ∀ i < C.gates.length, (C.gates.getD i dGate).op = PEqualNP.CircuitLowerBounds.GateOp.and →
                PEqualNP.EdgeOwnership.InCone 26 C i h → maskWval 8193 (26 + i) = true → i = i0 := by
              intro i hi hiAnd hiCone hiE0
              by_contra hne
              exact hSecond ⟨i, hi, hne, hiAnd, hiCone, hiE0⟩
            have hNoBelowI0 : ∀ i < C.gates.length, (C.gates.getD i dGate).op = PEqualNP.CircuitLowerBounds.GateOp.and →
                PEqualNP.EdgeOwnership.InCone 26 C i i0 → maskWval 8193 (26 + i) = false := by
              intro i hi hiAnd hic
              cases hv : maskWval 8193 (26 + i) with
              | false => rfl
              | true =>
                have hiEq := hOnlyI0 i hi hiAnd (inCone_trans h hh i i0 hic hi0Cone) hv
                have hilt := inCone_lt i0 hi0Lt i hic
                omega
            have huDec := active_decomp i0 u (by omega)
              (fun i hi hiAnd hri hiE => hOnlyI0 i hi hiAnd (reachesInCone_step h hh u huMem i hri) hiE) huE0
            have hvDec := active_decomp i0 v (by omega)
              (fun i hi hiAnd hri hiE => hOnlyI0 i hi hiAnd (reachesInCone_step h hh v hvMem i hri) hiE) hvE0
            rcases huDec with huOR | ⟨huW, huLP⟩
            · rcases hvDec with hvOR | ⟨hvW, hvLP⟩
              · exact both_orReach_kill h hh hHand hkLP0 hkLP1 huOR hvOR
              · exact one_side_active_kill h i0 hh hi0Lt hHand hi0And hkLP0 hkLP1 hi0E0 hNoBelowI0
                  v u hvLt huLt (Or.inr ⟨rfl, rfl⟩) hvW hvLP huOR
            · rcases hvDec with hvOR | ⟨hvW, hvLP⟩
              · exact one_side_active_kill h i0 hh hi0Lt hHand hi0And hkLP0 hkLP1 hi0E0 hNoBelowI0
                  u v huLt hvLt (Or.inl ⟨rfl, rfl⟩) huW huLP hvOR
              · have hi0NotBF := ((mem_junk_iff i0).mp hi0Junk).2.2
                apply hi0NotBF
                intro x hi0x
                have hux := huW x hi0x
                have hvx := hvW x hi0x
                have hhx : PEqualNP.EdgeOwnership.gateVal 26 C h x = true := by
                  change wval x (26 + h) = true
                  rw [wval_gate_and x h hh hHand]
                  change (wval x u && wval x v) = true
                  rw [hux, hvx]; rfl
                exact hhBF x hhx
