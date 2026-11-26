import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- Reduce L-meta-2223 via two checked Fano results (L-meta-8986 exact size 27 lower bound and
-- L-meta-17415 pair-clean rigidity) and inline flag-transitivity wire-remapping transport.
-- Tree circuits satisfy the conclusion immediately; non-tree circuits normalize to flag (0, 0),
-- must have exact size 27 with every gate live in the cone of the output (by deleting a maximal
-- dead gate against L-meta-8986), and must contain a pair-dirty AND gate strictly nested below
-- another AND gate (by L-meta-17415 and OR-propagation). Splitting on whether the non-edge pair
-- lies on one side (including singletons) or crosses between points and lines gives two clean regimes.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.R_meta_2223_1
    (hPairClean :
      have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ));
      have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true;
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 →
        (∀ (x5 : ℕ), PEqualNP.ReadTwo.isAnd x3 x5 → ∀ (x7 x8 : Fin (14 : ℕ)),
          have x9 : Fin (14 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput x7 x8;
          PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x3 x5 x9 = Bool.true → x3.eval (List.ofFn x9) = Bool.true) →
        ∀ (x6 x7 : Fin (7 : ℕ)), x1 x6 x7 →
          x3.lineDeg (14 : ℕ) {↑x6} ≤ (1 : ℕ) ∨ x3.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x7} ≤ (1 : ℕ))
    (hNo26 :
      ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (26 : ℕ) ∧
        (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 →
          (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧
        ∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔
          ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)),
            (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧
            x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true)
    (hSameSideDirty :
      ∀ (C : Circuit),
        C.size = 27 →
        (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
          (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
          ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) →
        (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
            x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
        ¬ ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))).Nodup →
        2 ≤ C.lineDeg 14 {0} →
        2 ≤ C.lineDeg 14 {7} →
        (∃ (j : ℕ) (u v : Fin 14), PEqualNP.ReadTwo.isAnd C j ∧
          ((u.val < 7 ∧ v.val < 7) ∨ (7 ≤ u.val ∧ 7 ≤ v.val)) ∧
          PEqualNP.EdgeOwnership.gateVal 14 C j (PEqualNP.EdgeOwnership.pairInput u v) = true ∧
          ∃ k : ℕ, PEqualNP.ReadTwo.isAnd C k ∧ PEqualNP.EdgeOwnership.InCone 14 C j k) →
        False)
    (hCrossDirty :
      ∀ (C : Circuit),
        C.size = 27 →
        (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
          (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
          ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) →
        (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
            x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
        ¬ ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))).Nodup →
        2 ≤ C.lineDeg 14 {0} →
        2 ≤ C.lineDeg 14 {7} →
        (∀ (j : ℕ) (u v : Fin 14), PEqualNP.ReadTwo.isAnd C j →
          ((u.val < 7 ∧ v.val < 7) ∨ (7 ≤ u.val ∧ 7 ≤ v.val)) →
          PEqualNP.EdgeOwnership.gateVal 14 C j (PEqualNP.EdgeOwnership.pairInput u v) = false) →
        (∃ (j : ℕ) (a b : Fin 7), PEqualNP.ReadTwo.isAnd C j ∧
          ¬ (a = b ∨ a = b + 1 ∨ a = b + 3) ∧
          PEqualNP.EdgeOwnership.gateVal 14 C j
            (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd 7 a) (Fin.natAdd 7 b)) = true ∧
          ∃ k : ℕ, PEqualNP.ReadTwo.isAnd C k ∧ PEqualNP.EdgeOwnership.InCone 14 C j k) →
        False) :
    have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (7 : ℕ)), x2 x4 → x1 x5 x6 → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {↑x5} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6} → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), x2 x11 ∧ x3 x11 ∧ (2 : ℕ) ≤ x11.lineDeg (14 : ℕ) {↑x5} ∧ (2 : ℕ) ≤ x11.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6} := by
  intro inc valid tree C0 p0 l0 hC0 hFlag hDegP0 hDegL0
  by_cases hTree0 : tree C0
  · exact ⟨C0, hC0, hTree0, hDegP0, hDegL0⟩
  exfalso
  classical
  -- Step 1: Flag transitivity on PG(2, 2) maps (p0, l0) to (0, 0), and wire-remapping transports C0.
  let mul : Fin 3 → Fin 7 := fun k => if k = 0 then 1 else if k = 1 then 2 else 4
  let off : Fin 3 → Fin 7 := fun k => if k = 0 then 0 else if k = 1 then 1 else 3
  let point (k : Fin 3) (b z : Fin 7) := mul k * (z - b) + off k
  let line (k : Fin 3) (b z : Fin 7) := mul k * (z - b)
  have pinj : ∀ (k : Fin 3) (b u v : Fin 7), point k b u = point k b v → u = v := by
    dsimp only [point, mul, off]; decide +kernel
  have linj : ∀ (k : Fin 3) (b u v : Fin 7), line k b u = line k b v → u = v := by
    dsimp only [line, mul]; decide +kernel
  have psurj : ∀ (k : Fin 3) (b v : Fin 7), ∃ u : Fin 7, point k b u = v := by
    dsimp only [point, mul, off]; decide +kernel
  have lsurj : ∀ (k : Fin 3) (b v : Fin 7), ∃ u : Fin 7, line k b u = v := by
    dsimp only [line, mul]; decide +kernel
  have hauto : ∀ (k : Fin 3) (b u v : Fin 7), inc (point k b u) (line k b v) ↔ inc u v := by
    dsimp only [inc, point, line, mul, off]; decide +kernel
  have hmove : ∀ u v : Fin 7, inc u v → ∃ k : Fin 3, point k v u = 0 ∧ line k v v = 0 := by
    dsimp only [inc, point, line, mul, off]; decide +kernel
  obtain ⟨k0, hmP, hmL⟩ := hmove p0 l0 hFlag
  let P : Equiv.Perm (Fin 7) :=
    Equiv.ofBijective (point k0 l0) ⟨fun _ _ => pinj k0 l0 _ _, psurj k0 l0⟩
  let L : Equiv.Perm (Fin 7) :=
    Equiv.ofBijective (line k0 l0) ⟨fun _ _ => linj k0 l0 _ _, lsurj k0 l0⟩
  have hP0 : P p0 = 0 := hmP
  have hL0 : L l0 = 0 := hmL
  have hA : ∀ u v : Fin 7, inc (P u) (L v) ↔ inc u v := hauto k0 l0
  let wm : ℕ → ℕ := fun w =>
    if h1 : w < 7 then (P ⟨w, h1⟩).val
    else if h2 : w < 14 then 7 + (L ⟨w - 7, by omega⟩).val
    else w
  have wm_ge : ∀ w, 14 ≤ w → wm w = w := by
    intro w hw; dsimp only [wm]; rw [dite_eq_right (by omega), dite_eq_right (by omega)]
  have wm_lt : ∀ w, w < 14 → wm w < 14 := by
    intro w hw; dsimp only [wm]
    by_cases h1 : w < 7
    · rw [dite_eq_left h1]; have := (P ⟨w, h1⟩).isLt; omega
    · rw [dite_eq_right h1, dite_eq_left hw]; have := (L ⟨w - 7, by omega⟩).isLt; omega
  have wm_le_of : ∀ w k, w < 14 + k → wm w < 14 + k := by
    intro w k hw
    by_cases h14 : w < 14
    · have := wm_lt w h14; omega
    · rw [wm_ge w (by omega)]; exact hw
  have wm_inj : Function.Injective wm := by
    intro a b hab
    rcases lt_or_ge a 14 with ha | ha <;> rcases lt_or_ge b 14 with hb | hb
    · rcases lt_or_ge a 7 with ha7 | ha7 <;> rcases lt_or_ge b 7 with hb7 | hb7
      · dsimp only [wm] at hab
        rw [dite_eq_left ha7, dite_eq_left hb7] at hab
        have := P.injective (Fin.ext hab)
        simpa using this
      · dsimp only [wm] at hab
        rw [dite_eq_left ha7, dite_eq_right (show ¬ b < 7 by omega), dite_eq_left hb] at hab
        have := (P ⟨a, ha7⟩).isLt; omega
      · dsimp only [wm] at hab
        rw [dite_eq_left hb7, dite_eq_right (show ¬ a < 7 by omega), dite_eq_left ha] at hab
        have := (P ⟨b, hb7⟩).isLt; omega
      · dsimp only [wm] at hab
        rw [dite_eq_right (show ¬ a < 7 by omega), dite_eq_left ha, dite_eq_right (show ¬ b < 7 by omega),
          dite_eq_left hb] at hab
        have h' : L ⟨a - 7, by omega⟩ = L ⟨b - 7, by omega⟩ := Fin.ext (by omega)
        have := L.injective h'
        simp only [Fin.mk.injEq] at this; omega
    · rw [wm_ge b hb] at hab; have := wm_lt a ha; omega
    · rw [wm_ge a ha] at hab; have := wm_lt b hb; omega
    · rw [wm_ge a ha, wm_ge b hb] at hab; exact hab
  have wm_left : ∀ p : Fin 7, wm p.val = (P p).val := by
    intro p; dsimp only [wm]; rw [dite_eq_left p.isLt]
  have wm_right : ∀ l : Fin 7, wm (7 + l.val) = 7 + (L l).val := by
    intro l; dsimp only [wm]; rw [dite_eq_right (by omega), dite_eq_left (by omega)]; simp
  let rg : Gate → Gate := fun g => ⟨g.op, g.inputs.map wm⟩
  let C : Circuit := ⟨C0.gates.map rg, wm C0.output⟩
  have rel_fold : ∀ {α : Type} (d0 : α) (F : Gate → List α → α),
      (∀ (g : Gate) (W W' : List α), (∀ w : ℕ, W'.getD (wm w) d0 = W.getD w d0) → F (rg g) W' = F g W) →
      ∀ (gs : List Gate) (W W' : List α),
        (14 ≤ W.length ∧ W'.length = W.length ∧ ∀ w : ℕ, W'.getD (wm w) d0 = W.getD w d0) →
        14 ≤ (gs.foldl (fun w g => w ++ [F g w]) W).length ∧
        ((gs.map rg).foldl (fun w g => w ++ [F g w]) W').length =
          (gs.foldl (fun w g => w ++ [F g w]) W).length ∧
        ∀ w : ℕ, ((gs.map rg).foldl (fun w g => w ++ [F g w]) W').getD (wm w) d0 =
          (gs.foldl (fun w g => w ++ [F g w]) W).getD w d0 := by
    intro α d0 F hF gs
    induction gs with
    | nil => intro W W' h; exact h
    | cons g rest ih =>
      intro W W' hRel
      have h1 := hRel.1
      have h2 := hRel.2.1
      have h3 := hRel.2.2
      simp only [List.map_cons, List.foldl_cons]
      apply ih
      have hv := hF g W W' h3
      refine ⟨by simp; omega, by simp; omega, ?_⟩
      intro w
      rcases Nat.lt_trichotomy w W.length with hw | hw | hw
      · have hlt : wm w < W'.length := by
          rcases lt_or_ge w 14 with h14 | h14
          · have := wm_lt w h14; omega
          · rw [wm_ge w h14]; omega
        rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
        exact h3 w
      · have he : wm w = W'.length := by rw [wm_ge w (by omega)]; omega
        rw [he, hw]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, hv]
      · have hge : W'.length + 1 ≤ wm w := by rw [wm_ge w (by omega)]; omega
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  have hF_bool : ∀ (g : Gate) (W W' : List Bool),
      (∀ w : ℕ, W'.getD (wm w) false = W.getD w false) →
      (rg g).op.eval ((rg g).inputs.map fun i => W'.getD i false) =
        g.op.eval (g.inputs.map fun i => W.getD i false) := by
    intro g W W' h
    have hm : ((rg g).inputs.map fun i => W'.getD i false) = g.inputs.map fun i => W.getD i false := by
      dsimp only [rg]; rw [List.map_map]; exact List.map_congr_left (fun a _ => h a)
    dsimp only [rg]; rw [hm]
  have hF_deg : ∀ (g : Gate) (W W' : List ℕ),
      (∀ w : ℕ, W'.getD (wm w) 0 = W.getD w 0) →
      (rg g).lineDegree W' = g.lineDegree W := by
    intro g W W' h
    have hm : ((rg g).inputs.map fun i => W'.getD i 0) = g.inputs.map fun i => W.getD i 0 := by
      dsimp only [rg]; rw [List.map_map]; exact List.map_congr_left (fun a _ => h a)
    unfold Gate.lineDegree
    rw [hm]
  have hEvalC : ∀ a : Fin 14 → Bool,
      C.eval (List.ofFn a) = C0.eval (List.ofFn (fun i : Fin 14 => a ⟨wm i, wm_lt i i.isLt⟩)) := by
    intro a
    exact (rel_fold false (fun g w => g.op.eval (g.inputs.map fun i => w.getD i false)) hF_bool
      C0.gates _ _ ⟨by simp, by simp, fun w => by
        rcases lt_or_ge w 14 with hw | hw
        · rw [List.getD_eq_getElem _ _ (by simpa using wm_lt w hw),
            List.getD_eq_getElem _ _ (by simpa using hw)]
          simp only [List.getElem_ofFn]
        · rw [wm_ge w hw, List.getD_eq_default _ _ (by simpa using hw),
            List.getD_eq_default _ _ (by simpa using hw)]⟩).2.2 C0.output
  have hDegC : ∀ m : ℕ, C.lineDeg 14 {wm m} = C0.lineDeg 14 {m} := by
    intro m
    exact (rel_fold 0 (fun g w => g.lineDegree w) hF_deg C0.gates _ _
      ⟨by simp, by simp, fun w => by
        rcases lt_or_ge w 14 with hw | hw
        · rw [List.getD_eq_getElem _ _ (by simpa using wm_lt w hw),
            List.getD_eq_getElem _ _ (by simpa using hw)]
          simp [wm_inj.eq_iff]
        · rw [wm_ge w hw, List.getD_eq_default _ _ (by simpa using hw),
            List.getD_eq_default _ _ (by simpa using hw)]⟩).2.2 C0.output
  have hFlatMap_rg : ∀ gs : List Gate, (gs.map rg).flatMap Gate.inputs = (gs.flatMap Gate.inputs).map wm := by
    intro gs
    induction gs with
    | nil => simp
    | cons g rest ih => simp [rg, ih]
  have hFilter_wm : ∀ lst : List ℕ, (lst.map wm).filter (fun x => decide (14 ≤ x)) = lst.filter (fun x => decide (14 ≤ x)) := by
    intro lst
    induction lst with
    | nil => simp
    | cons a rest ih =>
      by_cases ha : 14 ≤ a
      · simp [ha, wm_ge a ha, ih]
      · have h1 : ¬ 14 ≤ wm a := by have := wm_lt a (by omega); omega
        simp [ha, h1, ih]
  have hNotTree : ¬ ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))).Nodup := by
    have hl : C.output :: C.gates.flatMap Gate.inputs = (C0.output :: C0.gates.flatMap Gate.inputs).map wm := by
      change wm C0.output :: (C0.gates.map rg).flatMap Gate.inputs = _
      rw [hFlatMap_rg, List.map_cons]
    rw [hl, hFilter_wm]
    exact hTree0
  have hDeg0 : 2 ≤ C.lineDeg 14 {0} := by
    have he := hDegC p0.val
    rw [wm_left p0, hP0] at he
    change C.lineDeg 14 {0} = _ at he
    rw [he]; exact hDegP0
  have hDeg7 : 2 ≤ C.lineDeg 14 {7} := by
    have he := hDegC (7 + l0.val)
    rw [wm_right l0, hL0] at he
    change C.lineDeg 14 {7} = _ at he
    rw [he]; exact hDegL0
  obtain ⟨hSizeLe0, hGates0, hCorr0⟩ := hC0
  have hSizeLe : C.size ≤ 27 := by
    change (C0.gates.map rg).length ≤ 27
    rw [List.length_map]
    exact hSizeLe0
  have hGates : ∀ (x3 : ℕ) (x4 : Gate), C.gates[x3]? = some x4 →
      (x4.op = GateOp.and ∨ x4.op = GateOp.or) ∧
      ∃ x6 x7 : ℕ, x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < 14 + x3 ∧ x7 < 14 + x3 := by
    intro i g hg
    change (C0.gates.map rg)[i]? = some g at hg
    rw [List.getElem?_map] at hg
    obtain ⟨g0, hc, hge⟩ := Option.map_eq_some_iff.mp hg
    subst hge
    obtain ⟨hop, a, b, hin, hab, ha, hb⟩ := hGates0 i g0 hc
    refine ⟨hop, wm a, wm b, ?_, fun h => hab (wm_inj h), wm_le_of a i ha, wm_le_of b i hb⟩
    change g0.inputs.map wm = _
    rw [hin]; rfl
  have hCorr : ∀ x3 : Fin 14 → Bool, C.eval (List.ofFn x3) = true ↔
      ∃ x4 x5 : Fin 7, inc x4 x5 ∧ x3 (Fin.castAdd 7 x4) = true ∧ x3 (Fin.natAdd 7 x5) = true := by
    intro a
    rw [hEvalC, hCorr0]
    have hb1 : ∀ p : Fin 7, (⟨wm (Fin.castAdd 7 p).val, wm_lt _ (Fin.castAdd 7 p).isLt⟩ : Fin 14) = Fin.castAdd 7 (P p) := by
      intro p; apply Fin.ext; exact wm_left p
    have hb2 : ∀ l : Fin 7, (⟨wm (Fin.natAdd 7 l).val, wm_lt _ (Fin.natAdd 7 l).isLt⟩ : Fin 14) = Fin.natAdd 7 (L l) := by
      intro l; apply Fin.ext; exact wm_right l
    constructor
    · rintro ⟨p, l, hpl, h1, h2⟩
      exact ⟨P p, L l, (hA p l).2 hpl, (congrArg a (hb1 p)).symm.trans h1, (congrArg a (hb2 l)).symm.trans h2⟩
    · rintro ⟨p, l, hpl, h1, h2⟩
      refine ⟨P.symm p, L.symm l, (hA _ _).1 (by rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact hpl), ?_, ?_⟩
      · have e := congrArg a (hb1 (P.symm p)); rw [Equiv.apply_symm_apply] at e; exact e.trans h1
      · have e := congrArg a (hb2 (L.symm l)); rw [Equiv.apply_symm_apply] at e; exact e.trans h2
  have hSizeEq : C.size = 27 := by
    by_contra hne
    have hle26 : C.size ≤ 26 := by omega
    exact hNo26 ⟨C, hle26, hGates, hCorr⟩
  have hLenEq : C.gates.length = 27 := hSizeEq
  -- Step 2: General wire and cone foldl helpers for C.
  let wstep : List Bool → Gate → List Bool :=
    fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  have wfold_len : ∀ (gs : List Gate) (xs : List Bool),
      (gs.foldl wstep xs).length = xs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro xs; simp
    | cons g rest ih =>
      intro xs
      simp only [List.foldl_cons, ih, wstep, List.length_append, List.length_cons, List.length_nil]
      omega
  have wfold_getD_lt : ∀ (gs : List Gate) (xs : List Bool) (r : ℕ),
      r < xs.length → (gs.foldl wstep xs).getD r false = xs.getD r false := by
    intro gs
    induction gs with
    | nil => intro xs r _; rfl
    | cons g rest ih =>
      intro xs r hr
      simp only [List.foldl_cons]
      have hr' : r < (wstep xs g).length := by
        simp only [wstep, List.length_append, List.length_singleton]; omega
      rw [ih (wstep xs g) r hr']
      simp only [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hr]
  have hgetD_snoc_lt : ∀ (l : List Bool) (a : Bool) (i : ℕ),
      i < l.length → (l ++ [a]).getD i false = l.getD i false := by
    intro l a i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have hgetD_snoc_eq : ∀ (l : List Bool) (a : Bool),
      (l ++ [a]).getD l.length false = a := by
    intro l a
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  have hgetD_ge : ∀ (l : List Bool) (i : ℕ), l.length ≤ i → l.getD i false = false := by
    intro l i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]
  have wireVal_gate : ∀ (x : Fin 14 → Bool) (k : ℕ) (hk : k < C.gates.length),
      PEqualNP.EdgeOwnership.gateVal 14 C k x =
        (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun i => (C.wires (List.ofFn x)).getD i false) := by
    intro x k hk
    have hgk : C.gates[k]? = some C.gates[k] := List.getElem?_eq_getElem hk
    obtain ⟨_, a, b, hinp, _, ha, hb⟩ := hGates k C.gates[k] hgk
    have hlt : ∀ i ∈ C.gates[k].inputs, i < 14 + k := by
      intro i hi
      rw [hinp] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    have hsplit : C.gates = C.gates.take k ++ C.gates[k] :: C.gates.drop (k + 1) := by
      rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
    let pref := (C.gates.take k).foldl wstep (List.ofFn x)
    have hpref_len : pref.length = 14 + k := by
      dsimp only [pref]; rw [wfold_len, List.length_ofFn, List.length_take]; omega
    have hwires_eq : C.wires (List.ofFn x) =
        (C.gates.drop (k + 1)).foldl wstep (wstep pref C.gates[k]) := by
      change C.gates.foldl wstep (List.ofFn x) = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have hpref_get : ∀ i < 14 + k, pref.getD i false = (C.wires (List.ofFn x)).getD i false := by
      intro i hi
      rw [hwires_eq]
      have hi1 : i < (wstep pref C.gates[k]).length := by
        simp only [wstep, List.length_append, List.length_singleton]; omega
      rw [wfold_getD_lt _ _ i hi1]
      exact (hgetD_snoc_lt pref _ i (by omega)).symm
    change (C.wires (List.ofFn x)).getD (14 + k) false = _
    conv_lhs => rw [hwires_eq]
    have hidx : 14 + k < (wstep pref C.gates[k]).length := by
      simp only [wstep, List.length_append, List.length_singleton]; omega
    rw [wfold_getD_lt _ _ (14 + k) hidx]
    have hstep_at : (wstep pref C.gates[k]).getD (14 + k) false =
        (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun i => pref.getD i false) := by
      dsimp only [wstep]
      rw [← hpref_len, hgetD_snoc_eq]
    rw [hstep_at]
    congr 1
    exact List.map_congr_left fun i hi => hpref_get i (hlt i hi)
  -- Cone characterization and transitivity.
  let cstep : List (List ℕ) → Gate → List (List ℕ) := fun cs g =>
    cs ++ [(g.inputs.filter (fun w => decide (14 ≤ w ∧ w < 14 + cs.length))).flatMap
      (fun w => (w - 14) :: cs.getD (w - 14) [])]
  have cfold_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl cstep cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g rest ih =>
      intro cs
      simp only [List.foldl_cons, ih, cstep, List.length_append, List.length_cons, List.length_nil]
      omega
  have cfold_getD_lt : ∀ (gs : List Gate) (cs : List (List ℕ)) (r : ℕ),
      r < cs.length → (gs.foldl cstep cs).getD r [] = cs.getD r [] := by
    intro gs
    induction gs with
    | nil => intro cs r _; rfl
    | cons g rest ih =>
      intro cs r hr
      simp only [List.foldl_cons]
      have hr' : r < (cstep cs g).length := by
        simp only [cstep, List.length_append, List.length_singleton]; omega
      rw [ih (cstep cs g) r hr']
      simp only [cstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hr]
  have inCone_iff : ∀ (i j : ℕ),
      PEqualNP.EdgeOwnership.InCone 14 C i j ↔
        j < C.gates.length ∧ ∃ w ∈ C.gates[j]?.getD ⟨GateOp.or, []⟩ |>.inputs,
          14 ≤ w ∧ w < 14 + j ∧ (i = w - 14 ∨ PEqualNP.EdgeOwnership.InCone 14 C i (w - 14)) := by
    intro i j
    by_cases hj : j < C.gates.length
    · let gj := C.gates[j]
      have hsplit : C.gates = C.gates.take j ++ gj :: C.gates.drop (j + 1) := by
        dsimp only [gj]
        rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
      let pref := (C.gates.take j).foldl cstep []
      have hpref_len : pref.length = j := by
        dsimp only [pref]; rw [cfold_len, List.length_nil, List.length_take]; omega
      have hcones_eq : C.gates.foldl cstep [] =
          (C.gates.drop (j + 1)).foldl cstep (cstep pref gj) := by
        conv_lhs => rw [hsplit]
        rw [List.foldl_append, List.foldl_cons]
      have hpref_get : ∀ r < j, pref.getD r [] = (C.gates.foldl cstep []).getD r [] := by
        intro r hr
        rw [hcones_eq]
        have hr1 : r < (cstep pref gj).length := by
          simp only [cstep, List.length_append, List.length_singleton]; omega
        rw [cfold_getD_lt _ _ r hr1]
        simp only [cstep, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : r < pref.length)]
      have hj_at : (C.gates.foldl cstep []).getD j [] =
          (gj.inputs.filter (fun w => decide (14 ≤ w ∧ w < 14 + j))).flatMap
            (fun w => (w - 14) :: pref.getD (w - 14) []) := by
        rw [hcones_eq]
        have hj1 : j < (cstep pref gj).length := by
          simp only [cstep, List.length_append, List.length_singleton]; omega
        rw [cfold_getD_lt _ _ j hj1]
        simp only [cstep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega), hpref_len]
        simp
      have hgetj : (C.gates[j]?.getD ⟨GateOp.or, []⟩) = gj := by
        rw [List.getElem?_eq_getElem hj]; rfl
      change i ∈ (C.gates.foldl cstep []).getD j [] ↔ _
      rw [hj_at, hgetj, List.mem_flatMap]
      constructor
      · intro hmem
        obtain ⟨w, hw_filt, hi_mem⟩ := hmem
        obtain ⟨hw_in, hw_dec⟩ := List.mem_filter.mp hw_filt
        obtain ⟨hw14, hwj⟩ := of_decide_eq_true hw_dec
        refine ⟨hj, w, hw_in, hw14, hwj, ?_⟩
        rcases List.mem_cons.mp hi_mem with h1 | h2
        · exact Or.inl h1
        · right
          change i ∈ (C.gates.foldl cstep []).getD (w - 14) []
          rw [← hpref_get (w - 14) (by omega)]
          exact h2
      · rintro ⟨_, w, hw_in, hw14, hwj, h1 | h2⟩
        · exact ⟨w, List.mem_filter.mpr ⟨hw_in, decide_eq_true ⟨hw14, hwj⟩⟩,
            h1 ▸ List.mem_cons_self⟩
        · refine ⟨w, List.mem_filter.mpr ⟨hw_in, decide_eq_true ⟨hw14, hwj⟩⟩,
            List.mem_cons_of_mem _ ?_⟩
          rw [hpref_get (w - 14) (by omega)]
          exact h2
    · have hge : (C.gates.foldl cstep []).length ≤ j := by
        rw [cfold_len, List.length_nil]; omega
      have hnil : (C.gates.foldl cstep []).getD j [] = [] := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none]
      change i ∈ (C.gates.foldl cstep []).getD j [] ↔ _
      rw [hnil]
      exact ⟨fun h => False.elim (List.not_mem_nil h), fun h => False.elim (hj h.1)⟩
  have inCone_lt : ∀ (i j : ℕ), PEqualNP.EdgeOwnership.InCone 14 C i j → i < j := by
    intro i j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hij
      obtain ⟨_, w, _, hw14, hwj, h1 | h2⟩ := (inCone_iff i j).mp hij
      · omega
      · have hlt := ih (w - 14) (by omega) h2
        omega
  have inCone_trans : ∀ (j : ℕ) (a b : ℕ),
      PEqualNP.EdgeOwnership.InCone 14 C a b →
      PEqualNP.EdgeOwnership.InCone 14 C b j →
      PEqualNP.EdgeOwnership.InCone 14 C a j := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro a b hab hbj
      obtain ⟨hj, w, hw_in, hw14, hwj, h1 | h2⟩ := (inCone_iff b j).mp hbj
      · apply (inCone_iff a j).mpr
        refine ⟨hj, w, hw_in, hw14, hwj, Or.inr ?_⟩
        rw [← h1]
        exact hab
      · apply (inCone_iff a j).mpr
        exact ⟨hj, w, hw_in, hw14, hwj, Or.inr (ih (w - 14) (by omega) a b hab h2)⟩
  -- Step 3: C.output is a valid gate wire 14 + outG.
  have hOut_lt : C.output < 14 + C.gates.length := by
    by_contra hge
    have htrue : C.eval (List.ofFn (fun _ : Fin 14 => true)) = true :=
      (hCorr _).mpr ⟨0, 0, Or.inl rfl, rfl, rfl⟩
    have hlen : (C.wires (List.ofFn (fun _ : Fin 14 => true))).length = 14 + C.gates.length := by
      change (C.gates.foldl wstep (List.ofFn (fun _ : Fin 14 => true))).length = _
      rw [wfold_len, List.length_ofFn]
    have hfalse : C.eval (List.ofFn (fun _ : Fin 14 => true)) = false :=
      hgetD_ge _ C.output (by omega)
    rw [htrue] at hfalse
    exact Bool.noConfusion hfalse
  have hOut_ge14 : 14 ≤ C.output := by
    by_contra hlt
    have hlt14 : C.output < 14 := by omega
    let x1 : Fin 14 → Bool := fun i => decide (i = ⟨C.output, hlt14⟩)
    have hev : C.eval (List.ofFn x1) = true := by
      change (C.gates.foldl wstep (List.ofFn x1)).getD C.output false = true
      rw [wfold_getD_lt C.gates (List.ofFn x1) C.output (by rw [List.length_ofFn]; exact hlt14)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt14, ↓reduceDIte,
        Option.getD_some, x1, decide_true]
    obtain ⟨u, t, _, hu, ht⟩ := (hCorr x1).mp hev
    have hu' : Fin.castAdd 7 u = ⟨C.output, hlt14⟩ := of_decide_eq_true hu
    have ht' : Fin.natAdd 7 t = ⟨C.output, hlt14⟩ := of_decide_eq_true ht
    have hv1 : u.val = C.output := congrArg Fin.val hu'
    have hv2 : 7 + t.val = C.output := congrArg Fin.val ht'
    have hu7 := u.isLt
    omega
  let outG : ℕ := C.output - 14
  have houtG_lt : outG < C.gates.length := by omega
  have houtG_eq : 14 + outG = C.output := by omega
  -- Step 4: Every gate j < C.gates.length reaches outG (else delete maximal dead gate against hNo26).
  have hAllLive : ∀ j < C.gates.length, j = outG ∨ PEqualNP.EdgeOwnership.InCone 14 C j outG := by
    intro j hj
    by_contra hdead
    have hj_ne : j ≠ outG := fun e => hdead (Or.inl e)
    have hj_nc : ¬ PEqualNP.EdgeOwnership.InCone 14 C j outG := fun h => hdead (Or.inr h)
    let deadSet : Finset ℕ :=
      (Finset.range C.gates.length).filter
        (fun d => d ≠ outG ∧ ¬ PEqualNP.EdgeOwnership.InCone 14 C d outG)
    have hne : deadSet.Nonempty :=
      ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hj_ne, hj_nc⟩⟩
    let d : ℕ := deadSet.max' hne
    have hd_mem : d ∈ deadSet := Finset.max'_mem deadSet hne
    have hd_lt : d < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hd_mem).1
    have hd_ne : d ≠ outG := (Finset.mem_filter.mp hd_mem).2.1
    have hd_nc : ¬ PEqualNP.EdgeOwnership.InCone 14 C d outG := (Finset.mem_filter.mp hd_mem).2.2
    have hno_read : ∀ m : ℕ, ∀ hm : m < C.gates.length, 14 + d ∉ C.gates[m].inputs := by
      intro m hm hmem
      obtain ⟨_, a, b, hinp, _, ha, hb⟩ := hGates m C.gates[m] (List.getElem?_eq_getElem hm)
      have hltm : 14 + d < 14 + m := by
        rw [hinp] at hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h1 | h2 <;> omega
      have hm_not : m ∉ deadSet := by
        intro hmd
        have hle := Finset.le_max' deadSet m hmd
        omega
      have hm_live : m = outG ∨ PEqualNP.EdgeOwnership.InCone 14 C m outG := by
        by_contra hm_bad
        apply hm_not
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm,
          fun e => hm_bad (Or.inl e), fun h => hm_bad (Or.inr h)⟩
      have hdm : PEqualNP.EdgeOwnership.InCone 14 C d m := by
        apply (inCone_iff d m).mpr
        refine ⟨hm, 14 + d, ?_, by omega, hltm, Or.inl (by omega)⟩
        rw [List.getElem?_eq_getElem hm]
        exact hmem
      rcases hm_live with rfl | hmo
      · exact hd_nc hdm
      · exact hd_nc (inCone_trans outG d m hdm hmo)
    let dropIdx : ℕ → ℕ := fun w => if w < 14 + d then w else w - 1
    let pre : List Gate := C.gates.take d
    let post : List Gate := C.gates.drop (d + 1)
    let post' : List Gate := post.map (fun g => ⟨g.op, g.inputs.map dropIdx⟩)
    let C' : Circuit := ⟨pre ++ post', dropIdx C.output⟩
    have hpre_len : pre.length = d := List.length_take_of_le (Nat.le_of_lt hd_lt)
    have hpost_len : post.length = C.gates.length - (d + 1) := List.length_drop
    have hC'_sz : C'.size ≤ 26 := by
      change (pre ++ post').length ≤ 26
      simp only [List.length_append, hpre_len, post', List.length_map, hpost_len]
      omega
    have hC'_gates : ∀ (i : ℕ) (g : Gate), C'.gates[i]? = some g →
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + i ∧ b < 14 + i := by
      intro i g hig
      change (pre ++ post')[i]? = some g at hig
      by_cases hi : i < d
      · have hi' : i < pre.length := by omega
        rw [List.getElem?_append_left hi'] at hig
        have heq : pre[i]? = C.gates[i]? := by
          dsimp only [pre]
          rw [List.getElem?_take_of_lt hi]
        rw [heq] at hig
        exact hGates i g hig
      · have hi' : pre.length ≤ i := by omega
        rw [List.getElem?_append_right hi', hpre_len] at hig
        simp only [post', List.getElem?_map] at hig
        obtain ⟨g0, hpo, hge⟩ := Option.map_eq_some_iff.mp hig
        subst hge
        have hget_orig : C.gates[i + 1]? = some g0 := by
          have h1 : post[i - d]? = C.gates[(d + 1) + (i - d)]? := List.getElem?_drop
          rw [h1] at hpo
          have hidx_eq : (d + 1) + (i - d) = i + 1 := by omega
          rwa [hidx_eq] at hpo
        have hi1_lt : i + 1 < C.gates.length := (List.getElem?_eq_some_iff.mp hget_orig).1
        have hg0_eq : C.gates[i + 1] = g0 :=
          Option.some.inj ((List.getElem?_eq_getElem hi1_lt).symm.trans hget_orig)
        obtain ⟨hop, a, b, hinp, hab, ha, hb⟩ := hGates (i + 1) g0 hget_orig
        have ha_ne : a ≠ 14 + d := by
          intro he
          apply hno_read (i + 1) hi1_lt
          rw [hg0_eq, hinp, he]
          exact List.mem_cons_self
        have hb_ne : b ≠ 14 + d := by
          intro he
          apply hno_read (i + 1) hi1_lt
          rw [hg0_eq, hinp, he]
          exact List.mem_cons_of_mem _ List.mem_cons_self
        refine ⟨hop, dropIdx a, dropIdx b, by simp [hinp], ?_, ?_, ?_⟩
        · dsimp only [dropIdx]
          by_cases h1 : a < 14 + d <;> by_cases h2 : b < 14 + d
          · rw [ite_eq_left h1, ite_eq_left h2]; exact hab
          · rw [ite_eq_left h1, ite_eq_right h2]; omega
          · rw [ite_eq_right h1, ite_eq_left h2]; omega
          · rw [ite_eq_right h1, ite_eq_right h2]; omega
        · dsimp only [dropIdx]
          by_cases h1 : a < 14 + d
          · rw [ite_eq_left h1]; omega
          · rw [ite_eq_right h1]; omega
        · dsimp only [dropIdx]
          by_cases h2 : b < 14 + d
          · rw [ite_eq_left h2]; omega
          · rw [ite_eq_right h2]; omega
    have hsim_post : ∀ (gs : List Gate) (w1 w2 : List Bool),
        w1.length = w2.length + 1 →
        14 + d ≤ w2.length →
        (∀ g ∈ gs, 14 + d ∉ g.inputs) →
        (∀ i, i ≠ 14 + d → w2.getD (dropIdx i) false = w1.getD i false) →
        (gs.foldl wstep w1).length =
          ((gs.map fun g => ⟨g.op, g.inputs.map dropIdx⟩).foldl wstep w2).length + 1 ∧
        ∀ i, i ≠ 14 + d →
          ((gs.map fun g => ⟨g.op, g.inputs.map dropIdx⟩).foldl wstep w2).getD (dropIdx i) false =
          (gs.foldl wstep w1).getD i false := by
      intro gs
      induction gs with
      | nil => intro w1 w2 hl _ _ hag; exact ⟨hl, hag⟩
      | cons g rest ih =>
        intro w1 w2 hl hge hnod hag
        simp only [List.map_cons, List.foldl_cons]
        have hg_nod : 14 + d ∉ g.inputs := hnod g List.mem_cons_self
        have hmap : ((g.inputs.map dropIdx).map fun i => w2.getD i false) =
            (g.inputs.map fun i => w1.getD i false) := by
          rw [List.map_map]
          apply List.map_congr_left
          intro i hi
          exact hag i (fun he => hg_nod (he ▸ hi))
        apply ih (wstep w1 g) (wstep w2 ⟨g.op, g.inputs.map dropIdx⟩)
        · simp only [wstep, List.length_append, List.length_singleton]; omega
        · simp only [wstep, List.length_append, List.length_singleton]; omega
        · intro g' hg'; exact hnod g' (List.mem_cons_of_mem _ hg')
        · intro i hine
          dsimp only [wstep]
          rw [hmap]
          by_cases hlt : i < 14 + d
          · have hdi : dropIdx i = i := ite_eq_left hlt
            rw [hdi, hgetD_snoc_lt w2 _ i (by omega), hgetD_snoc_lt w1 _ i (by omega)]
            have h0 := hag i hine
            rwa [hdi] at h0
          · have hdi : dropIdx i = i - 1 := ite_eq_right hlt
            rw [hdi]
            by_cases hilt1 : i < w1.length
            · rw [hgetD_snoc_lt w2 _ (i - 1) (by omega), hgetD_snoc_lt w1 _ i hilt1]
              have h0 := hag i hine
              rwa [hdi] at h0
            · by_cases heq1 : i = w1.length
              · have heq2 : i - 1 = w2.length := by omega
                rw [heq2, heq1, hgetD_snoc_eq w2, hgetD_snoc_eq w1]
              · rw [hgetD_ge _ (i - 1) (by simp only [List.length_append, List.length_singleton]; omega),
                    hgetD_ge _ i (by simp only [List.length_append, List.length_singleton]; omega)]
    have hC'_eval : ∀ x : Fin 14 → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
      intro x
      have hsplit : C.gates = pre ++ C.gates[d] :: post := by
        dsimp only [pre, post]
        rw [← List.drop_eq_getElem_cons hd_lt, List.take_append_drop]
      let w0 := pre.foldl wstep (List.ofFn x)
      have hw0_len : w0.length = 14 + d := by
        dsimp only [w0]; rw [wfold_len, List.length_ofFn, hpre_len]
      have hpost_nod : ∀ g ∈ post, 14 + d ∉ g.inputs := by
        intro g hg
        obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg
        have hdt : d + 1 + t < C.gates.length := by rw [hpost_len] at ht; omega
        have heq_el : post[t] = C.gates[d + 1 + t] := List.getElem_drop
        rw [heq_el]
        exact hno_read (d + 1 + t) hdt
      have hout_ne : C.output ≠ 14 + d := by omega
      have hsim := (hsim_post post (wstep w0 C.gates[d]) w0
        (by simp only [wstep, List.length_append, List.length_singleton]) (by omega)
        hpost_nod (fun i hine => by
          dsimp only [dropIdx]
          by_cases hlt : i < 14 + d
          · rw [ite_eq_left hlt]
            dsimp only [wstep]
            rw [hgetD_snoc_lt w0 _ i (by omega)]
          · rw [ite_eq_right hlt]
            rw [hgetD_ge w0 (i - 1) (by omega),
                hgetD_ge (wstep w0 C.gates[d]) i (by simp only [wstep, List.length_append, List.length_singleton]; omega)])).2
        C.output hout_ne
      change ((pre ++ post').foldl wstep (List.ofFn x)).getD (dropIdx C.output) false =
        (C.gates.foldl wstep (List.ofFn x)).getD C.output false
      rw [List.foldl_append]
      conv_rhs => rw [hsplit, List.foldl_append, List.foldl_cons]
      exact hsim
    have hC'_corr : ∀ x : Fin 14 → Bool, C'.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
      intro x; rw [hC'_eval x]; exact hCorr x
    exact hNo26 ⟨C', hC'_sz, hC'_gates, hC'_corr⟩
  -- Step 5: Any pair-dirty AND gate j (true at x while C.eval x = false) must be nested below another AND gate.
  have hNested : ∀ (j : ℕ) (x : Fin 14 → Bool),
      PEqualNP.ReadTwo.isAnd C j →
      PEqualNP.EdgeOwnership.gateVal 14 C j x = true →
      C.eval (List.ofFn x) = false →
      ∃ k : ℕ, PEqualNP.ReadTwo.isAnd C k ∧ PEqualNP.EdgeOwnership.InCone 14 C j k := by
    intro j x hjAnd hjTrue hOutFalse
    by_contra hNoK
    have hj_ne_out : j ≠ outG := by
      intro he
      have h1 : C.eval (List.ofFn x) = true := by
        change (C.wires (List.ofFn x)).getD C.output false = true
        rw [← houtG_eq, ← he]
        exact hjTrue
      rw [hOutFalse] at h1
      exact Bool.noConfusion h1
    have hj_in_out : PEqualNP.EdgeOwnership.InCone 14 C j outG :=
      (hAllLive j hjAnd.1).resolve_left hj_ne_out
    have hProp : ∀ m : ℕ, m < C.gates.length →
        PEqualNP.EdgeOwnership.InCone 14 C j m →
        PEqualNP.EdgeOwnership.gateVal 14 C m x = true := by
      intro m
      induction m using Nat.strong_induction_on with
      | ind m ih =>
        intro hm hjm
        have hgm : C.gates[m]? = some C.gates[m] := List.getElem?_eq_getElem hm
        obtain ⟨hop, a, b, hinp, _, ha, hb⟩ := hGates m C.gates[m] hgm
        have hOr : (C.gates[m]).op = GateOp.or := by
          rcases hop with hand | hor
          · exfalso
            apply hNoK
            refine ⟨m, ⟨hm, ?_⟩, hjm⟩
            change (C.gates.getD m ⟨GateOp.or, []⟩).op = GateOp.and
            rw [List.getD_eq_getElem _ _ hm]
            exact hand
          · exact hor
        obtain ⟨_, w, hw_in, hw14, hwm, hw_eq⟩ := (inCone_iff j m).mp hjm
        rw [hgm] at hw_in
        change w ∈ C.gates[m].inputs at hw_in
        have hw_true : (C.wires (List.ofFn x)).getD w false = true := by
          have hw_split : w = 14 + (w - 14) := by omega
          rw [hw_split]
          rcases hw_eq with rfl | hrec
          · exact hjTrue
          · exact ih (w - 14) (by omega) (by omega) hrec
        rw [wireVal_gate x m hm, hOr, hinp]
        have hw_ab : w = a ∨ w = b := by
          rw [hinp] at hw_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw_in
          exact hw_in
        change ((C.wires (List.ofFn x)).getD a false || ((C.wires (List.ofFn x)).getD b false || false)) = true
        rcases hw_ab with rfl | rfl
        · rw [hw_true]; rfl
        · rw [hw_true]
          by_cases ha_val : (C.wires (List.ofFn x)).getD a false = true
          · rw [ha_val]; rfl
          · rw [Bool.eq_false_iff.mpr ha_val]; rfl
    have hOutTrue : C.eval (List.ofFn x) = true := by
      change (C.wires (List.ofFn x)).getD C.output false = true
      rw [← houtG_eq]
      exact hProp outG houtG_lt hj_in_out
    rw [hOutFalse] at hOutTrue
    exact Bool.noConfusion hOutTrue
  -- Step 6: L-meta-17415 produces a pair-dirty AND gate (j, u, v).
  have hNotClean : ¬ (∀ (j : ℕ), PEqualNP.ReadTwo.isAnd C j → ∀ (u v : Fin 14),
      have x9 : Fin 14 → Bool := PEqualNP.EdgeOwnership.pairInput u v;
      PEqualNP.EdgeOwnership.gateVal 14 C j x9 = true → C.eval (List.ofFn x9) = true) := by
    intro hClean
    have hRes := hPairClean C ⟨hSizeLe, hGates, hCorr⟩ hClean 0 0 (Or.inl rfl)
    rcases hRes with h1 | h2
    · change C.lineDeg 14 {0} ≤ 1 at h1; omega
    · change C.lineDeg 14 {7} ≤ 1 at h2; omega
  have hDirty : ∃ (j : ℕ) (u v : Fin 14), PEqualNP.ReadTwo.isAnd C j ∧
      PEqualNP.EdgeOwnership.gateVal 14 C j (PEqualNP.EdgeOwnership.pairInput u v) = true ∧
      C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) = false := by
    by_contra hNone
    apply hNotClean
    intro j hj u v x9 hgv
    by_cases hEv : C.eval (List.ofFn x9) = true
    · exact hEv
    · exact False.elim (hNone ⟨j, u, v, hj, hgv, Bool.eq_false_iff.mpr hEv⟩)
  -- Step 7: Split into same-side (including singleton) pair-dirty and cross non-edge dirty regimes.
  by_cases hSame : ∃ (j : ℕ) (u v : Fin 14), PEqualNP.ReadTwo.isAnd C j ∧
      ((u.val < 7 ∧ v.val < 7) ∨ (7 ≤ u.val ∧ 7 ≤ v.val)) ∧
      PEqualNP.EdgeOwnership.gateVal 14 C j (PEqualNP.EdgeOwnership.pairInput u v) = true
  · obtain ⟨j, u, v, hj, hside, hgv⟩ := hSame
    have hSameFalse : C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) = false := by
      by_contra hne
      have htr : C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) = true :=
        Bool.eq_true_of_not_eq_false hne
      obtain ⟨a, b, _, ha, hb⟩ := (hCorr _).mp htr
      have ha' : Fin.castAdd 7 a = u ∨ Fin.castAdd 7 a = v := of_decide_eq_true ha
      have hb' : Fin.natAdd 7 b = u ∨ Fin.natAdd 7 b = v := of_decide_eq_true hb
      have ha7 := a.isLt
      rcases hside with ⟨hu7, hv7⟩ | ⟨hu7, hv7⟩
      · rcases hb' with h1 | h1
        · have hv := congrArg Fin.val h1; change 7 + b.val = u.val at hv; omega
        · have hv := congrArg Fin.val h1; change 7 + b.val = v.val at hv; omega
      · rcases ha' with h1 | h1
        · have hv := congrArg Fin.val h1; change a.val = u.val at hv; omega
        · have hv := congrArg Fin.val h1; change a.val = v.val at hv; omega
    exact hSameSideDirty C hSizeEq hGates hCorr hNotTree hDeg0 hDeg7
      ⟨j, u, v, hj, hside, hgv, hNested j _ hj hgv hSameFalse⟩
  · have hNoSame : ∀ (j : ℕ) (u v : Fin 14), PEqualNP.ReadTwo.isAnd C j →
        ((u.val < 7 ∧ v.val < 7) ∨ (7 ≤ u.val ∧ 7 ≤ v.val)) →
        PEqualNP.EdgeOwnership.gateVal 14 C j (PEqualNP.EdgeOwnership.pairInput u v) = false := by
      intro j u v hj hside
      by_contra hne
      exact hSame ⟨j, u, v, hj, hside, Bool.eq_true_of_not_eq_false hne⟩
    obtain ⟨j, u, v, hj, hgv, hOff⟩ := hDirty
    have hCross : (u.val < 7 ∧ 7 ≤ v.val) ∨ (7 ≤ u.val ∧ v.val < 7) := by
      by_cases hu : u.val < 7 <;> by_cases hv : v.val < 7
      · exfalso
        have h0 := hNoSame j u v hj (Or.inl ⟨hu, hv⟩)
        rw [hgv] at h0; exact Bool.noConfusion h0
      · exact Or.inl ⟨hu, by omega⟩
      · exact Or.inr ⟨by omega, hv⟩
      · exfalso
        have h0 := hNoSame j u v hj (Or.inr ⟨by omega, by omega⟩)
        rw [hgv] at h0; exact Bool.noConfusion h0
    have hPairSymm : ∀ x y : Fin 14,
        PEqualNP.EdgeOwnership.pairInput x y = PEqualNP.EdgeOwnership.pairInput y x := by
      intro x y
      funext i
      change decide (i = x ∨ i = y) = decide (i = y ∨ i = x)
      exact decide_eq_decide.mpr or_comm
    rcases hCross with ⟨hu7, hv7⟩ | ⟨hu7, hv7⟩
    · let a : Fin 7 := ⟨u.val, hu7⟩
      let b : Fin 7 := ⟨v.val - 7, by have := v.isLt; omega⟩
      have hua : Fin.castAdd 7 a = u := Fin.ext rfl
      have hvb : Fin.natAdd 7 b = v := Fin.ext (by change 7 + (v.val - 7) = v.val; omega)
      rw [← hua, ← hvb] at hgv hOff
      have hNonInc : ¬ (a = b ∨ a = b + 1 ∨ a = b + 3) := by
        intro hInc
        have htr : C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd 7 a) (Fin.natAdd 7 b))) = true :=
          (hCorr _).mpr ⟨a, b, hInc, decide_eq_true (Or.inl rfl), decide_eq_true (Or.inr rfl)⟩
        rw [hOff] at htr; exact Bool.noConfusion htr
      exact hCrossDirty C hSizeEq hGates hCorr hNotTree hDeg0 hDeg7 hNoSame
        ⟨j, a, b, hj, hNonInc, hgv, hNested j _ hj hgv hOff⟩
    · rw [hPairSymm u v] at hgv hOff
      let a : Fin 7 := ⟨v.val, hv7⟩
      let b : Fin 7 := ⟨u.val - 7, by have := u.isLt; omega⟩
      have hva : Fin.castAdd 7 a = v := Fin.ext rfl
      have hub : Fin.natAdd 7 b = u := Fin.ext (by change 7 + (u.val - 7) = u.val; omega)
      rw [← hva, ← hub] at hgv hOff
      have hNonInc : ¬ (a = b ∨ a = b + 1 ∨ a = b + 3) := by
        intro hInc
        have htr : C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd 7 a) (Fin.natAdd 7 b))) = true :=
          (hCorr _).mpr ⟨a, b, hInc, decide_eq_true (Or.inl rfl), decide_eq_true (Or.inr rfl)⟩
        rw [hOff] at htr; exact Bool.noConfusion htr
      exact hCrossDirty C hSizeEq hGates hCorr hNotTree hDeg0 hDeg7 hNoSame
        ⟨j, a, b, hj, hNonInc, hgv, hNested j _ hj hgv hOff⟩
