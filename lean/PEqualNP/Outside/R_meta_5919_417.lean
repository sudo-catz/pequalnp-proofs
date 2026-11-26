import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection PEqualNP.HeptadCover

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_5919_417
    (size62 : ∀ (C : Circuit), Monotone2 C → C.size ≤ 62 →
      RightOnIncidentPairs singerLines3 C →
      (∀ (X Y : Finset (Fin 13)), IsMaximalFalse singerLines3 X Y →
        (¬ InNoLine singerLines3 X ∨ ¬ InNoPencil singerLines3 Y) →
        C.eval (incidenceInput X Y) = false) → False)
    (oneGateTerm : ∀ (B : Circuit) (T : Finset (Finset ℕ)) (u v : ℕ),
      Monotone2 B →
      (∃ g ∈ B.gates, g.op = GateOp.and) →
      T.card ≤ 11 →
      B.size + 2 * T.card ≤ 62 →
      26 ≤ u → u < 26 + B.size → 26 ≤ v → v < 26 + B.size → u ≠ v →
      (∀ t ∈ T, t.card = 2 ∧ (∃ w ∈ t, w < 26) ∧ t ⊆ Finset.range (26 + B.size)) →
      let U : Finset (Finset ℕ) := insert {u, v} T
      let fires : Finset ℕ → List Bool → Prop := fun t x => ∀ i ∈ t, (B.wires x).getD i false = true
      8 ≤ ((incidences singerLines3).filter fun e => fires {u, v} (incidenceInput {e.1} {e.2})).card →
      (∀ t ∈ U, ∃ (p l : Fin 13), p ∈ singerLines3 l ∧
        fires t (incidenceInput {p} {l}) ∧
        ∀ s ∈ U, s ≠ t → ¬ fires s (incidenceInput {p} {l})) →
      (∀ (X Y : Finset (Fin 13)), IsMaximalFalse singerLines3 X Y →
        (¬ InNoLine singerLines3 X ∨ ¬ InNoPencil singerLines3 Y) →
        ∀ t ∈ U, ¬ fires t (incidenceInput X Y)) →
      (∀ (p l : Fin 13), p ∈ singerLines3 l →
        ∃ t ∈ U, fires t (incidenceInput {p} {l})) → False)
    (multiGateTerms : ∀ (B : Circuit) (T : Finset (Finset ℕ)),
      Monotone2 B →
      (∃ g ∈ B.gates, g.op = GateOp.and) →
      T.card ≤ 12 →
      B.size + 2 * T.card ≤ 64 →
      (∀ t ∈ T, t.card = 2 ∧ t ⊆ Finset.range (26 + B.size)) →
      2 ≤ (T.filter fun t => ∀ w ∈ t, 26 ≤ w).card →
      let fires : Finset ℕ → List Bool → Prop := fun t x => ∀ i ∈ t, (B.wires x).getD i false = true
      (∀ t ∈ T, ∃ (p l : Fin 13), p ∈ singerLines3 l ∧
        fires t (incidenceInput {p} {l}) ∧
        ∀ s ∈ T, s ≠ t → ¬ fires s (incidenceInput {p} {l})) →
      (∀ (X Y : Finset (Fin 13)), IsMaximalFalse singerLines3 X Y →
        (¬ InNoLine singerLines3 X ∨ ¬ InNoPencil singerLines3 Y) →
        ∀ t ∈ T, ¬ fires t (incidenceInput X Y)) →
      (∀ (p l : Fin 13), p ∈ singerLines3 l →
        ∃ t ∈ T, fires t (incidenceInput {p} {l})) → False) :
    (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := fun (x2 : Fin (13 : ℕ)) => {x3 : Fin (13 : ℕ) | x3 - x2 ∈ x1}; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Finset (Finset ℕ)),   PEqualNP.MetaComplexity.Monotone2 x3 →     x4.card ≤ (12 : ℕ) →       x3.size + (2 : ℕ) * x4.card ≤ (64 : ℕ) →         (∀ x8 ∈ x4, x8.card ≤ (2 : ℕ) ∧ x8 ⊆ Finset.range ((26 : ℕ) + x3.size)) →           let x9 : Finset ℕ → List Bool → Prop := fun (x9 : Finset ℕ) (x10 : List Bool) => ∀ x11 ∈ x9, (x3.wires x10).getD x11 Bool.false = Bool.true;           (∀ x10 ∈ x4, ∃ (x12 : Fin (13 : ℕ)) (x13 : Fin (13 : ℕ)), x12 ∈ x2 x13 ∧ x9 x10 (PEqualNP.GenericRejection.incidenceInput {x12} {x13}) ∧ ∀ x14 ∈ x4, x14 ≠ x10 → ¬x9 x14 (PEqualNP.GenericRejection.incidenceInput {x12} {x13})) →             (∀ (x11 x12 : Finset (Fin (13 : ℕ))), PEqualNP.GenericRejection.IsMaximalFalse x2 x11 x12 → ¬PEqualNP.GenericRejection.InNoLine x2 x11 ∨ ¬PEqualNP.GenericRejection.InNoPencil x2 x12 → ∀ x15 ∈ x4, ¬x9 x15 (PEqualNP.GenericRejection.incidenceInput x11 x12)) →               (∃ x12 ∈ x4,                   have x13 : Finset (Fin (13 : ℕ) × Fin (13 : ℕ)) := {x13 ∈ PEqualNP.HeptadCover.incidences x2 | x9 x12 (PEqualNP.GenericRejection.incidenceInput {x13.1} {x13.2})};                   (5 : ℕ) ≤ x13.card ∧ ∃ x14 ∈ x13, ∃ x15 ∈ x13, x14.1 ∉ x2 x15.2 ∧ ¬x9 x12 (PEqualNP.GenericRejection.incidenceInput {x14.1} {x15.2})) →                 ∃ (x13 : Fin (13 : ℕ)) (x14 : Fin (13 : ℕ)), x13 ∈ x2 x14 ∧ ∀ x15 ∈ x4, ¬x9 x15 (PEqualNP.GenericRejection.incidenceInput {x13} {x14})) := by
  dsimp only
  intro B T hMono hTcard hBudget hTerms hWit hSafe hBig
  let x1 : Finset (Fin 13) := {0, 1, 3, 9}
  let x2 : Fin 13 → Finset (Fin 13) := fun l => {p : Fin 13 | p - l ∈ x1}
  have hSingDef : ∀ l : Fin 13, singerLines3 l =
      Finset.univ.filter fun p : Fin 13 => (p.val + 13 - l.val) % 13 ∈ ({0, 1, 3, 9} : Finset ℕ) :=
    fun _ => rfl
  have hIncDef : ∀ (X Y : Finset (Fin 13)), incidenceInput X Y =
      List.ofFn (fun p : Fin 13 => decide (p ∈ X)) ++ List.ofFn (fun l : Fin 13 => decide (l ∈ Y)) :=
    fun _ _ => rfl
  have opAnd : ∀ xs : List Bool, GateOp.and.eval xs = xs.all id := fun _ => rfl
  have opOr : ∀ xs : List Bool, GateOp.or.eval xs = xs.any id := fun _ => rfl
  have hSizeDef : ∀ C : Circuit, C.size = C.gates.length := fun _ => rfl
  have hMemS : ∀ p l : Fin 13, p ∈ x2 l ↔ p ∈ singerLines3 l := by
    intro p l
    rw [hSingDef]
    simp only [x2, x1, Finset.mem_filter, Finset.mem_univ, true_and]
    revert p l
    decide
  have hS : (fun l : Fin 13 => ({p : Fin 13 | p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))} : Finset (Fin 13))) =
      singerLines3 := by
    funext l
    ext p
    exact hMemS p l
  have hSApp : ∀ l : Fin 13, ({p : Fin 13 | p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))} : Finset (Fin 13)) =
      singerLines3 l := fun l => congrFun hS l
  simp only [hSApp] at hWit hSafe hBig ⊢
  by_contra hNoMiss
  push Not at hNoMiss
  let fires : Finset ℕ → List Bool → Prop := fun t x => ∀ i ∈ t, (B.wires x).getD i false = true
  have hCover : ∀ p l : Fin 13, p ∈ singerLines3 l → ∃ t ∈ T, fires t (incidenceInput {p} {l}) := by
    intro p l hpl
    exact hNoMiss p l hpl
  have hLenInc : ∀ (X Y : Finset (Fin 13)), (incidenceInput X Y).length = 26 := by
    intro X Y
    rw [hIncDef]
    simp
  have hWiresLen : ∀ (gs : List Gate) (x : List Bool), ((Circuit.mk gs 0).wires x).length = x.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro x; rfl
    | cons g gs ih =>
      intro x
      change ((Circuit.mk gs 0).wires (x ++ [_])).length = _
      rw [ih]
      simp
      omega
  have hWiresAppend : ∀ (gs₁ gs₂ : List Gate) (x : List Bool),
      (Circuit.mk (gs₁ ++ gs₂) 0).wires x =
        (Circuit.mk gs₂ 0).wires ((Circuit.mk gs₁ 0).wires x) := by
    intro gs₁ gs₂ x
    change List.foldl _ x (gs₁ ++ gs₂) = List.foldl _ (List.foldl _ x gs₁) gs₂
    rw [List.foldl_append]
  have hWiresSnoc : ∀ (gs : List Gate) (g : Gate) (x : List Bool),
      (Circuit.mk (gs ++ [g]) 0).wires x =
        (Circuit.mk gs 0).wires x ++ [g.op.eval (g.inputs.map fun i => ((Circuit.mk gs 0).wires x).getD i false)] := by
    intro gs g x
    rw [hWiresAppend]
    rfl
  have hGetDPrefix : ∀ (gs₁ gs₂ : List Gate) (x : List Bool) (i : ℕ),
      i < x.length + gs₁.length →
      ((Circuit.mk (gs₁ ++ gs₂) 0).wires x).getD i false =
        ((Circuit.mk gs₁ 0).wires x).getD i false := by
    intro gs₁ gs₂ x i hi
    induction gs₂ using List.reverseRecOn with
    | nil => simp
    | append_singleton gs₂ g ih =>
      rw [← List.append_assoc, hWiresSnoc]
      have hlt : i < ((Circuit.mk (gs₁ ++ gs₂) 0).wires x).length := by
        rw [hWiresLen]
        simp
        omega
      rw [List.getD_append _ _ _ _ hlt, ih]
  have hGetDInput : ∀ (gs : List Gate) (x : List Bool) (i : ℕ),
      i < x.length → ((Circuit.mk gs 0).wires x).getD i false = x.getD i false := by
    intro gs x i hi
    have h := hGetDPrefix [] gs x i (by simpa using hi)
    exact h
  have hGetDLast : ∀ (gs : List Gate) (g : Gate) (x : List Bool),
      ((Circuit.mk (gs ++ [g]) 0).wires x).getD (x.length + gs.length) false =
        g.op.eval (g.inputs.map fun i => ((Circuit.mk gs 0).wires x).getD i false) := by
    intro gs g x
    rw [hWiresSnoc]
    have hlen : ((Circuit.mk gs 0).wires x).length = x.length + gs.length := hWiresLen gs x
    rw [← hlen, List.getD_eq_getElem _ _ (by simp)]
    simp
  have hGetDOther : ∀ (gs : List Gate) (g : Gate) (x : List Bool) (i : ℕ),
      i ≠ x.length + gs.length →
      ((Circuit.mk (gs ++ [g]) 0).wires x).getD i false =
        ((Circuit.mk gs 0).wires x).getD i false := by
    intro gs g x i hi
    rw [hWiresSnoc]
    have hlen : ((Circuit.mk gs 0).wires x).length = x.length + gs.length := hWiresLen gs x
    by_cases hlt : i < ((Circuit.mk gs 0).wires x).length
    · exact List.getD_append _ _ _ _ hlt
    · have hge1 : ((Circuit.mk gs 0).wires x).length ≤ i := Nat.le_of_not_lt hlt
      let b := g.op.eval (g.inputs.map fun k => ((Circuit.mk gs 0).wires x).getD k false)
      have hge2 : (((Circuit.mk gs 0).wires x) ++ [b]).length ≤ i := by
        simp
        omega
      rw [List.getD_eq_default _ _ hge2, List.getD_eq_default _ _ hge1]
  have hIncBitPt : ∀ (X Y : Finset (Fin 13)) (p : Fin 13),
      (incidenceInput X Y).getD p.val false = decide (p ∈ X) := by
    intro X Y p
    rw [hIncDef]
    have hlt : p.val < (List.ofFn fun q : Fin 13 => decide (q ∈ X)).length := by simp
    rw [List.getD_append _ _ _ _ hlt, List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
  have hIncBitLn : ∀ (X Y : Finset (Fin 13)) (l : Fin 13),
      (incidenceInput X Y).getD (13 + l.val) false = decide (l ∈ Y) := by
    intro X Y l
    rw [hIncDef]
    have hlen : (List.ofFn fun q : Fin 13 => decide (q ∈ X)).length = 13 := by simp
    have hlt : 13 + l.val < (List.ofFn (fun q : Fin 13 => decide (q ∈ X)) ++
        List.ofFn (fun k : Fin 13 => decide (k ∈ Y))).length := by simp; omega
    rw [List.getD_eq_getElem _ _ hlt, List.getElem_append_right (by omega)]
    simp only [hlen, Nat.add_sub_cancel_left, List.getElem_ofFn]
  have hMonoWires : ∀ (gs : List Gate), Monotone2 ⟨gs, 0⟩ →
      ∀ (X₁ X₂ Y₁ Y₂ : Finset (Fin 13)), X₁ ⊆ X₂ → Y₁ ⊆ Y₂ →
      ∀ (i : ℕ), ((Circuit.mk gs 0).wires (incidenceInput X₁ Y₁)).getD i false = true →
        ((Circuit.mk gs 0).wires (incidenceInput X₂ Y₂)).getD i false = true := by
    intro gs hgm X₁ X₂ Y₁ Y₂ hX hY
    induction gs using List.reverseRecOn with
    | nil =>
      intro i hi
      change (incidenceInput X₁ Y₁).getD i false = true at hi
      change (incidenceInput X₂ Y₂).getD i false = true
      by_cases h1 : i < 13
      · let p : Fin 13 := ⟨i, h1⟩
        have hp : p.val = i := rfl
        rw [← hp, hIncBitPt] at hi ⊢
        exact decide_eq_true (hX (of_decide_eq_true hi))
      · by_cases h2 : i < 26
        · let l : Fin 13 := ⟨i - 13, by omega⟩
          have hl : 13 + l.val = i := by dsimp [l]; omega
          rw [← hl, hIncBitLn] at hi ⊢
          exact decide_eq_true (hY (of_decide_eq_true hi))
        · rw [List.getD_eq_default _ _ (by rw [hLenInc]; omega)] at hi
          exact Bool.noConfusion hi
    | append_singleton gs g ih =>
      have hgm0 : Monotone2 ⟨gs, 0⟩ := fun z hz => hgm z (List.mem_append_left _ hz)
      have hmg := hgm g (List.mem_append_right _ (List.mem_singleton_self _))
      intro i hi
      by_cases heq : i = 26 + gs.length
      · subst i
        have hlen1 := hLenInc X₁ Y₁
        have hlen2 := hLenInc X₂ Y₂
        rw [← hlen1, hGetDLast] at hi
        rw [← hlen2, hGetDLast]
        rcases hmg.1 with ha | ho
        · rw [ha, opAnd] at hi ⊢
          simp only [List.all_eq_true, id_eq, List.mem_map, forall_exists_index,
            and_imp, forall_apply_eq_imp_iff₂] at hi ⊢
          intro k hk
          exact ih hgm0 k (hi k hk)
        · rw [ho, opOr] at hi ⊢
          simp only [List.any_eq_true, id_eq, List.mem_map, exists_exists_and_eq_and] at hi ⊢
          obtain ⟨k, hk, hvk⟩ := hi
          exact ⟨k, hk, ih hgm0 k hvk⟩
      · have hne1 : i ≠ (incidenceInput X₁ Y₁).length + gs.length := by rw [hLenInc]; exact heq
        have hne2 : i ≠ (incidenceInput X₂ Y₂).length + gs.length := by rw [hLenInc]; exact heq
        rw [hGetDOther gs g _ i hne1] at hi
        rw [hGetDOther gs g _ i hne2]
        exact ih hgm0 i hi
  have hDiag : ∀ p : Fin 13, p ∈ singerLines3 p := by
    intro p
    rw [← hMemS]
    simp [x2, x1]
  have hEmptyUnivMF : IsMaximalFalse singerLines3 ∅ Finset.univ ∧ ¬ InNoLine singerLines3 ∅ := by
    refine ⟨⟨fun l _ => Finset.disjoint_empty_right _, ?_, fun l hl => False.elim (hl (Finset.mem_univ l))⟩,
      fun h => h 0 (Finset.empty_subset _)⟩
    intro p _ hf
    exact Finset.disjoint_left.mp (hf p (Finset.mem_univ p)) (hDiag p) (Finset.mem_insert_self p ∅)
  have hUnivEmptyMF : IsMaximalFalse singerLines3 Finset.univ ∅ ∧ ¬ InNoPencil singerLines3 ∅ := by
    refine ⟨⟨fun l hl => False.elim (Finset.notMem_empty l hl), fun p hp => False.elim (hp (Finset.mem_univ p)), ?_⟩,
      fun h => h 0 (fun l hl => False.elim (Finset.notMem_empty l hl))⟩
    intro l _ hf
    exact Finset.disjoint_left.mp (hf l (Finset.mem_insert_self l ∅)) (hDiag l) (Finset.mem_univ l)
  let E13 : Finset (Fin 13) := ∅
  let U13 : Finset (Fin 13) := Finset.univ
  have hRejEU : ∀ t ∈ T, ¬ fires t (incidenceInput E13 U13) :=
    hSafe E13 U13 hEmptyUnivMF.1 (Or.inl hEmptyUnivMF.2)
  have hRejUE : ∀ t ∈ T, ¬ fires t (incidenceInput U13 E13) :=
    hSafe U13 E13 hUnivEmptyMF.1 (Or.inr hUnivEmptyMF.2)
  have hNonEmpty : ∀ t ∈ T, 1 ≤ t.card := by
    intro t ht
    by_contra h0
    have hcard0 : t.card = 0 := by omega
    have hte : t = ∅ := Finset.card_eq_zero.mp hcard0
    exact hRejEU t ht (by simp [fires, hte])
  have hCard12 : ∀ t ∈ T, t.card = 1 ∨ t.card = 2 := by
    intro t ht
    have h1 := hNonEmpty t ht
    have h2 := (hTerms t ht).1
    omega
  have hOrOnlySplit : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.or) →
      ∀ (X Y : Finset (Fin 13)) (i : ℕ),
      ((Circuit.mk gs 0).wires (incidenceInput X Y)).getD i false = true →
      ((Circuit.mk gs 0).wires (incidenceInput X E13)).getD i false = true ∨
      ((Circuit.mk gs 0).wires (incidenceInput E13 Y)).getD i false = true := by
    intro gs hOr X Y
    induction gs using List.reverseRecOn with
    | nil =>
      intro i hi
      change (incidenceInput X Y).getD i false = true at hi
      by_cases h1 : i < 13
      · left
        let p : Fin 13 := ⟨i, h1⟩
        have hp : p.val = i := rfl
        change (incidenceInput X E13).getD i false = true
        rw [← hp, hIncBitPt] at hi ⊢
        exact hi
      · by_cases h2 : i < 26
        · right
          let l : Fin 13 := ⟨i - 13, by omega⟩
          have hl : 13 + l.val = i := by dsimp [l]; omega
          change (incidenceInput E13 Y).getD i false = true
          rw [← hl, hIncBitLn] at hi ⊢
          exact hi
        · rw [List.getD_eq_default _ _ (by rw [hLenInc]; omega)] at hi
          exact Bool.noConfusion hi
    | append_singleton gs g ih =>
      have hOr0 : ∀ z ∈ gs, z.op = GateOp.or := fun z hz => hOr z (List.mem_append_left _ hz)
      have hOg : g.op = GateOp.or := hOr g (List.mem_append_right _ (List.mem_singleton_self _))
      intro i hi
      by_cases heq : i = 26 + gs.length
      · subst i
        have hlenXY := hLenInc X Y
        have hlenX := hLenInc X E13
        have hlenY := hLenInc E13 Y
        rw [← hlenXY, hGetDLast, hOg, opOr] at hi
        simp only [List.any_eq_true, id_eq, List.mem_map, exists_exists_and_eq_and] at hi
        obtain ⟨k, hk, hvk⟩ := hi
        rcases ih hOr0 k hvk with hkx | hky
        · left
          rw [← hlenX, hGetDLast, hOg, opOr]
          simp only [List.any_eq_true, id_eq, List.mem_map, exists_exists_and_eq_and]
          exact ⟨k, hk, hkx⟩
        · right
          rw [← hlenY, hGetDLast, hOg, opOr]
          simp only [List.any_eq_true, id_eq, List.mem_map, exists_exists_and_eq_and]
          exact ⟨k, hk, hky⟩
      · have hneXY : i ≠ (incidenceInput X Y).length + gs.length := by rw [hLenInc]; exact heq
        have hneX : i ≠ (incidenceInput X E13).length + gs.length := by rw [hLenInc]; exact heq
        have hneY : i ≠ (incidenceInput E13 Y).length + gs.length := by rw [hLenInc]; exact heq
        rw [hGetDOther gs g _ i hneXY] at hi
        rw [hGetDOther gs g _ i hneX, hGetDOther gs g _ i hneY]
        exact ih hOr0 i hi
  obtain ⟨tStar, htStar, hStarCard, e, heH, f, hfH, _, hNotCross⟩ := hBig
  have hHasAnd : ∃ g ∈ B.gates, g.op = GateOp.and := by
    by_contra hNoAnd
    push Not at hNoAnd
    have hAllOr : ∀ g ∈ B.gates, g.op = GateOp.or := by
      intro g hg
      rcases (hMono g hg).1 with ha | ho
      · exact False.elim (hNoAnd g hg ha)
      · exact ho
    have hNotCross' : ¬ ∀ i ∈ tStar, (B.wires (incidenceInput {e.1} {f.2})).getD i false = true := hNotCross
    push Not at hNotCross'
    obtain ⟨w, hwMem, hwFalse⟩ := hNotCross'
    have hwFalse' : ((Circuit.mk B.gates 0).wires (incidenceInput {e.1} {f.2})).getD w false = false :=
      Bool.eq_false_iff.mpr hwFalse
    have hwe : ((Circuit.mk B.gates 0).wires (incidenceInput {e.1} {e.2})).getD w false = true :=
      (Finset.mem_filter.mp heH).2 w hwMem
    have hwf : ((Circuit.mk B.gates 0).wires (incidenceInput {f.1} {f.2})).getD w false = true :=
      (Finset.mem_filter.mp hfH).2 w hwMem
    have hwEU : ((Circuit.mk B.gates 0).wires (incidenceInput E13 U13)).getD w false = true := by
      rcases hOrOnlySplit B.gates hAllOr {e.1} {e.2} w hwe with h1 | h2
      · have hcontra := hMonoWires B.gates hMono {e.1} {e.1} E13 {f.2} (Finset.Subset.rfl) (Finset.empty_subset _) w h1
        rw [hwFalse'] at hcontra
        exact Bool.noConfusion hcontra
      · exact hMonoWires B.gates hMono E13 E13 {e.2} U13 (Finset.Subset.rfl) (Finset.subset_univ _) w h2
    have hwUE : ((Circuit.mk B.gates 0).wires (incidenceInput U13 E13)).getD w false = true := by
      rcases hOrOnlySplit B.gates hAllOr {f.1} {f.2} w hwf with h1 | h2
      · exact hMonoWires B.gates hMono {f.1} U13 E13 E13 (Finset.subset_univ _) (Finset.Subset.rfl) w h1
      · have hcontra := hMonoWires B.gates hMono E13 {e.1} {f.2} {f.2} (Finset.empty_subset _) (Finset.Subset.rfl) w h2
        rw [hwFalse'] at hcontra
        exact Bool.noConfusion hcontra
    have hRejEU' := hRejEU tStar htStar
    have hRejUE' := hRejUE tStar htStar
    dsimp only [fires] at hRejEU' hRejUE'
    push Not at hRejEU' hRejUE'
    obtain ⟨u, huMem, huFalse⟩ := hRejEU'
    obtain ⟨v, hvMem, hvFalse⟩ := hRejUE'
    have huNeW : u ≠ w := by
      intro heq
      subst heq
      exact huFalse hwEU
    have hvNeW : v ≠ w := by
      intro heq
      subst heq
      exact hvFalse hwUE
    have huv : u = v := by
      by_contra hne
      have hsub : ({w, u, v} : Finset ℕ) ⊆ tStar := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl <;> assumption
      have hcard3 : ({w, u, v} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp [hne]
        · simp [huNeW.symm, hvNeW.symm]
      have hle := (Finset.card_le_card hsub).trans (hTerms tStar htStar).1
      omega
    subst huv
    have hue : ((Circuit.mk B.gates 0).wires (incidenceInput {e.1} {e.2})).getD u false = true :=
      (Finset.mem_filter.mp heH).2 u huMem
    rcases hOrOnlySplit B.gates hAllOr {e.1} {e.2} u hue with h1 | h2
    · exact hvFalse (hMonoWires B.gates hMono {e.1} U13 E13 E13 (Finset.subset_univ _) (Finset.Subset.rfl) u h1)
    · exact huFalse (hMonoWires B.gates hMono E13 E13 {e.2} U13 (Finset.Subset.rfl) (Finset.subset_univ _) u h2)
  by_cases hHasOne : ∃ t ∈ T, t.card = 1
  · have hBuild : ∀ L : List (Finset ℕ), L ≠ [] →
        (∀ t ∈ L, (t.card = 1 ∨ t.card = 2) ∧ t ⊆ Finset.range (26 + B.size)) →
        ∃ (gs : List Gate) (out : ℕ),
          Monotone2 ⟨B.gates ++ gs, out⟩ ∧
          gs.length + 1 + (L.filter fun t => decide (t.card = 1)).length ≤ 2 * L.length ∧
          out < 26 + B.size + gs.length ∧
          ∀ x : List Bool, x.length = 26 →
            ((Circuit.mk (B.gates ++ gs) out).eval x = true ↔ ∃ t ∈ L, fires t x) := by
      intro L
      induction L with
      | nil => intro h; exact False.elim (h rfl)
      | cons t L' ih =>
        intro _ hL
        have htMem : t ∈ t :: L' := List.mem_cons_self
        have htInfo := hL t htMem
        have hSingleOrPair : ∀ s : Finset ℕ, s.card = 1 ∨ s.card = 2 →
            (∃ w, s = {w}) ∨ (∃ a b, a ≠ b ∧ s = {a, b}) := by
          intro s hs
          rcases hs with h1 | h2
          · left; exact Finset.card_eq_one.mp h1
          · right; exact Finset.card_eq_two.mp h2
        by_cases hL'empty : L' = []
        · subst hL'empty
          rcases hSingleOrPair t htInfo.1 with ⟨w, rfl⟩ | ⟨a, b, hab, rfl⟩
          · refine ⟨[], w, ?_, ?_, ?_, ?_⟩
            · intro g hg
              exact hMono g (by simpa using hg)
            · simp
            · have hw := Finset.mem_range.mp (htInfo.2 (Finset.mem_singleton_self w))
              simpa using hw
            · intro x _
              change ((Circuit.mk (B.gates ++ []) w).wires x).getD w false = true ↔ _
              simp only [List.append_nil]
              change (B.wires x).getD w false = true ↔ _
              simp [fires]
          · refine ⟨[⟨GateOp.and, [a, b]⟩], 26 + B.size, ?_, ?_, ?_, ?_⟩
            · intro g hg
              rcases List.mem_append.mp hg with hg | hg
              · exact hMono g hg
              · obtain rfl := List.mem_singleton.mp hg
                exact ⟨Or.inl rfl, by simp⟩
            · have hcard2 : ({a, b} : Finset ℕ).card = 2 := Finset.card_pair hab
              simp [hcard2]
            · simp
            · intro x hx
              change ((Circuit.mk (B.gates ++ [⟨GateOp.and, [a, b]⟩]) 0).wires x).getD (26 + B.size) false = true ↔ _
              rw [← hx]
              change ((Circuit.mk (B.gates ++ [⟨GateOp.and, [a, b]⟩]) 0).wires x).getD (x.length + B.gates.length) false = true ↔ _
              rw [hGetDLast, opAnd]
              simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
                Bool.and_true, Bool.and_eq_true, List.mem_singleton, exists_eq_left, fires,
                Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
              rfl
        · have hL' : ∀ s ∈ L', (s.card = 1 ∨ s.card = 2) ∧ s ⊆ Finset.range (26 + B.size) :=
            fun s hs => hL s (List.mem_cons_of_mem t hs)
          obtain ⟨gs', out', hMono', hLen', hOut', hEval'⟩ := ih hL'empty hL'
          rcases hSingleOrPair t htInfo.1 with ⟨w, rfl⟩ | ⟨a, b, hab, rfl⟩
          · refine ⟨gs' ++ [⟨GateOp.or, [w, out']⟩], 26 + B.size + gs'.length, ?_, ?_, ?_, ?_⟩
            · intro g hg
              rw [← List.append_assoc] at hg
              rcases List.mem_append.mp hg with hg | hg
              · exact hMono' g hg
              · obtain rfl := List.mem_singleton.mp hg
                exact ⟨Or.inr rfl, by simp⟩
            · simp only [List.length_append, List.length_cons, List.length_nil, List.filter_cons,
                Finset.card_singleton, decide_true, ↓reduceIte] at hLen' ⊢
              omega
            · simp
            · intro x hx
              have hw : w < x.length + B.gates.length := by
                have := Finset.mem_range.mp (htInfo.2 (Finset.mem_singleton_self w))
                rw [hx]; exact this
              change ((Circuit.mk (B.gates ++ (gs' ++ [⟨GateOp.or, [w, out']⟩])) 0).wires x).getD (26 + B.size + gs'.length) false = true ↔ _
              rw [← List.append_assoc]
              have hidx : 26 + B.size + gs'.length = x.length + (B.gates ++ gs').length := by
                rw [hSizeDef, hx, List.length_append]; omega
              rw [hidx, hGetDLast, opOr]
              simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
                Bool.or_false, Bool.or_eq_true]
              rw [hGetDPrefix B.gates gs' x w hw]
              change ((B.wires x).getD w false = true ∨
                (Circuit.mk (B.gates ++ gs') out').eval x = true) ↔ _
              rw [hEval' x hx]
              simp [fires]
          · let idx1 := 26 + B.size + gs'.length
            let g1 : Gate := ⟨GateOp.and, [a, b]⟩
            let g2 : Gate := ⟨GateOp.or, [idx1, out']⟩
            refine ⟨gs' ++ [g1, g2], idx1 + 1, ?_, ?_, ?_, ?_⟩
            · intro g hg
              have hsplit : B.gates ++ (gs' ++ [g1, g2]) = ((B.gates ++ gs') ++ [g1]) ++ [g2] := by simp
              rw [hsplit] at hg
              rcases List.mem_append.mp hg with hg | hg
              · rcases List.mem_append.mp hg with hg | hg
                · exact hMono' g hg
                · obtain rfl := List.mem_singleton.mp hg
                  exact ⟨Or.inl rfl, by simp [g1]⟩
              · obtain rfl := List.mem_singleton.mp hg
                exact ⟨Or.inr rfl, by simp [g2]⟩
            · have hcard2 : ({a, b} : Finset ℕ).card = 2 := Finset.card_pair hab
              simp only [List.length_append, List.length_cons, List.length_nil, List.filter_cons,
                hcard2, Nat.reduceEqDiff, decide_false, Bool.false_eq_true, ↓reduceIte] at hLen' ⊢
              omega
            · dsimp [idx1]; simp; omega
            · intro x hx
              have ha : a < x.length + B.gates.length := by
                have := Finset.mem_range.mp (htInfo.2 (Finset.mem_insert_self a {b}))
                rw [hx]; exact this
              have hb : b < x.length + B.gates.length := by
                have := Finset.mem_range.mp (htInfo.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self b)))
                rw [hx]; exact this
              have hsplit : B.gates ++ (gs' ++ [g1, g2]) = ((B.gates ++ gs') ++ [g1]) ++ [g2] := by simp
              change ((Circuit.mk (B.gates ++ (gs' ++ [g1, g2])) 0).wires x).getD (idx1 + 1) false = true ↔ _
              rw [hsplit]
              have hidx2 : idx1 + 1 = x.length + ((B.gates ++ gs') ++ [g1]).length := by
                dsimp [idx1]; rw [hSizeDef, hx]; simp; omega
              have hidx1 : idx1 = x.length + (B.gates ++ gs').length := by
                dsimp [idx1]; rw [hSizeDef, hx]; simp; omega
              rw [hidx2, hGetDLast]
              dsimp only [g2]
              rw [opOr]
              simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
                Bool.or_false, Bool.or_eq_true]
              rw [hidx1, hGetDLast]
              have houtNe : out' ≠ x.length + (B.gates ++ gs').length := by
                rw [← hidx1]; dsimp [idx1]; omega
              rw [hGetDOther (B.gates ++ gs') g1 x out' houtNe]
              dsimp only [g1]
              rw [opAnd]
              simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
                Bool.and_true, Bool.and_eq_true]
              rw [hGetDPrefix B.gates gs' x a ha, hGetDPrefix B.gates gs' x b hb]
              change (((B.wires x).getD a false = true ∧ (B.wires x).getD b false = true) ∨
                (Circuit.mk (B.gates ++ gs') out').eval x = true) ↔ _
              rw [hEval' x hx]
              simp [fires]
    let L := T.toList
    obtain ⟨t1, ht1T, ht1Card⟩ := hHasOne
    have ht1L : t1 ∈ L := Finset.mem_toList.mpr ht1T
    have hLne : L ≠ [] := List.ne_nil_of_mem ht1L
    have hLinfo : ∀ t ∈ L, (t.card = 1 ∨ t.card = 2) ∧ t ⊆ Finset.range (26 + B.size) := by
      intro t ht
      have htT := Finset.mem_toList.mp ht
      exact ⟨hCard12 t htT, (hTerms t htT).2⟩
    obtain ⟨gs, out, hCmono, hClen, _, hCeval⟩ := hBuild L hLne hLinfo
    let C : Circuit := ⟨B.gates ++ gs, out⟩
    have hF1pos : 1 ≤ (L.filter fun t => decide (t.card = 1)).length := by
      have hm : t1 ∈ L.filter fun t => decide (t.card = 1) :=
        List.mem_filter.mpr ⟨ht1L, decide_eq_true ht1Card⟩
      exact List.length_pos_of_mem hm
    have hCsize : C.size ≤ 62 := by
      have hLlen : L.length = T.card := Finset.length_toList T
      have hCsz : C.size = B.size + gs.length := by
        rw [hSizeDef, hSizeDef]; exact List.length_append
      omega
    have hCRight : RightOnIncidentPairs singerLines3 C := by
      intro l p hpl
      rw [hCeval (incidenceInput {p} {l}) (hLenInc {p} {l})]
      obtain ⟨t, htT, hft⟩ := hCover p l hpl
      exact ⟨t, Finset.mem_toList.mpr htT, hft⟩
    have hCSafe : ∀ (X Y : Finset (Fin 13)), IsMaximalFalse singerLines3 X Y →
        (¬ InNoLine singerLines3 X ∨ ¬ InNoPencil singerLines3 Y) →
        C.eval (incidenceInput X Y) = false := by
      intro X Y hmf hdeg
      refine Bool.eq_false_iff.mpr fun hval => ?_
      rw [hCeval (incidenceInput X Y) (hLenInc X Y)] at hval
      obtain ⟨t, htL, hft⟩ := hval
      exact hSafe X Y hmf hdeg t (Finset.mem_toList.mp htL) hft
    exact size62 C hCmono hCsize hCRight hCSafe
  · push Not at hHasOne
    have hAllTwo : ∀ t ∈ T, t.card = 2 := by
      intro t ht
      rcases hCard12 t ht with h1 | h2
      · exact False.elim (hHasOne t ht h1)
      · exact h2
    have hInputBound : ∀ t : Finset ℕ, (∃ w ∈ t, w < 26) →
        ((incidences singerLines3).filter fun e => fires t (incidenceInput {e.1} {e.2})).card ≤ 4 := by
      intro t hEx
      obtain ⟨w, hwMem, hwLt⟩ := hEx
      by_cases h13 : w < 13
      · let p0 : Fin 13 := ⟨w, h13⟩
        have hsub : ((incidences singerLines3).filter fun e => fires t (incidenceInput {e.1} {e.2})) ⊆
            (incidences singerLines3).filter fun e => e.1 = p0 := by
          intro e he
          obtain ⟨heInc, heF⟩ := Finset.mem_filter.mp he
          refine Finset.mem_filter.mpr ⟨heInc, ?_⟩
          have hwTrue := heF w hwMem
          change ((Circuit.mk B.gates 0).wires (incidenceInput {e.1} {e.2})).getD w false = true at hwTrue
          rw [hGetDInput B.gates _ w (by rw [hLenInc]; exact hwLt)] at hwTrue
          have hp0 : p0.val = w := rfl
          rw [← hp0, hIncBitPt] at hwTrue
          exact (Finset.mem_singleton.mp (of_decide_eq_true hwTrue)).symm
        have hcard4 : ((incidences singerLines3).filter fun e => e.1 = p0).card ≤ 4 := by
          have hsubD : ((incidences singerLines3).filter fun e => e.1 = p0) ⊆
              x1.image (fun d => (p0, p0 - d)) := by
            intro e he
            obtain ⟨heInc, he1⟩ := Finset.mem_filter.mp he
            have hpOn : e.1 ∈ x2 e.2 := (hMemS e.1 e.2).mpr (Finset.mem_filter.mp heInc).2
            have hd : e.1 - e.2 ∈ x1 := (Finset.mem_filter.mp hpOn).2
            refine Finset.mem_image.mpr ⟨e.1 - e.2, hd, ?_⟩
            exact Prod.ext he1.symm (by rw [← he1]; abel)
          have hx1card : x1.card = 4 := by decide
          exact (Finset.card_le_card hsubD).trans (Finset.card_image_le.trans (le_of_eq hx1card))
        exact (Finset.card_le_card hsub).trans hcard4
      · let l0 : Fin 13 := ⟨w - 13, by omega⟩
        have hsub : ((incidences singerLines3).filter fun e => fires t (incidenceInput {e.1} {e.2})) ⊆
            (incidences singerLines3).filter fun e => e.2 = l0 := by
          intro e he
          obtain ⟨heInc, heF⟩ := Finset.mem_filter.mp he
          refine Finset.mem_filter.mpr ⟨heInc, ?_⟩
          have hwTrue := heF w hwMem
          change ((Circuit.mk B.gates 0).wires (incidenceInput {e.1} {e.2})).getD w false = true at hwTrue
          rw [hGetDInput B.gates _ w (by rw [hLenInc]; exact hwLt)] at hwTrue
          have hl0 : 13 + l0.val = w := by dsimp [l0]; omega
          rw [← hl0, hIncBitLn] at hwTrue
          exact (Finset.mem_singleton.mp (of_decide_eq_true hwTrue)).symm
        have hcard4 : ((incidences singerLines3).filter fun e => e.2 = l0).card ≤ 4 := by
          have hsubD : ((incidences singerLines3).filter fun e => e.2 = l0) ⊆
              x1.image (fun d => (l0 + d, l0)) := by
            intro e he
            obtain ⟨heInc, he2⟩ := Finset.mem_filter.mp he
            have hpOn : e.1 ∈ x2 e.2 := (hMemS e.1 e.2).mpr (Finset.mem_filter.mp heInc).2
            have hd : e.1 - e.2 ∈ x1 := (Finset.mem_filter.mp hpOn).2
            refine Finset.mem_image.mpr ⟨e.1 - e.2, hd, ?_⟩
            exact Prod.ext (by rw [← he2]; abel) he2.symm
          have hx1card : x1.card = 4 := by decide
          exact (Finset.card_le_card hsubD).trans (Finset.card_image_le.trans (le_of_eq hx1card))
        exact (Finset.card_le_card hsub).trans hcard4
    let Tgate := T.filter fun t => ∀ w ∈ t, 26 ≤ w
    have htStarGate : tStar ∈ Tgate := by
      refine Finset.mem_filter.mpr ⟨htStar, ?_⟩
      intro w hw
      by_contra hlt
      have hle4 := hInputBound tStar ⟨w, hw, Nat.lt_of_not_ge hlt⟩
      have hge5 : 5 ≤ ((incidences singerLines3).filter fun e => fires tStar (incidenceInput {e.1} {e.2})).card :=
        hStarCard
      omega
    by_cases hTwoGate : 2 ≤ Tgate.card
    · exact multiGateTerms B T hMono hHasAnd hTcard hBudget
        (fun t ht => ⟨hAllTwo t ht, (hTerms t ht).2⟩) hTwoGate hWit hSafe hCover
    · have hOneGate : Tgate.card = 1 := by
        have hpos : 1 ≤ Tgate.card := Finset.card_pos.mpr ⟨tStar, htStarGate⟩
        omega
      have hTgateEq : Tgate = {tStar} := by
        obtain ⟨s, hs⟩ := Finset.card_eq_one.mp hOneGate
        rw [hs] at htStarGate
        rw [hs, Finset.mem_singleton.mp htStarGate]
      obtain ⟨u, v, huv, htStarPair⟩ := Finset.card_eq_two.mp (hAllTwo tStar htStar)
      let Tstar := T.erase tStar
      have hTins : insert ({u, v} : Finset ℕ) Tstar = T := by
        rw [← htStarPair, Finset.insert_erase htStar]
      have hTstarCard : Tstar.card + 1 = T.card := Finset.card_erase_add_one htStar
      have hTstarLe : Tstar.card ≤ 11 := by omega
      have hTstarBudget : B.size + 2 * Tstar.card ≤ 62 := by omega
      have huMem : u ∈ tStar := by rw [htStarPair]; simp
      have hvMem : v ∈ tStar := by rw [htStarPair]; simp
      have huGe : 26 ≤ u := (Finset.mem_filter.mp htStarGate).2 u huMem
      have hvGe : 26 ≤ v := (Finset.mem_filter.mp htStarGate).2 v hvMem
      have huLt : u < 26 + B.size := Finset.mem_range.mp ((hTerms tStar htStar).2 huMem)
      have hvLt : v < 26 + B.size := Finset.mem_range.mp ((hTerms tStar htStar).2 hvMem)
      have hTstarInfo : ∀ t ∈ Tstar, t.card = 2 ∧ (∃ w ∈ t, w < 26) ∧ t ⊆ Finset.range (26 + B.size) := by
        intro t ht
        obtain ⟨hne, htT⟩ := Finset.mem_erase.mp ht
        refine ⟨hAllTwo t htT, ?_, (hTerms t htT).2⟩
        by_contra hno
        push Not at hno
        have hmemG : t ∈ Tgate := Finset.mem_filter.mpr ⟨htT, hno⟩
        rw [hTgateEq, Finset.mem_singleton] at hmemG
        exact hne hmemG
      have hStarEight : 8 ≤ ((incidences singerLines3).filter fun e => fires {u, v} (incidenceInput {e.1} {e.2})).card := by
        let cov (t : Finset ℕ) := (incidences singerLines3).filter fun e => fires t (incidenceInput {e.1} {e.2})
        have hall : incidences singerLines3 ⊆ cov {u, v} ∪ Tstar.biUnion cov := by
          intro e he
          have heInc : e.1 ∈ singerLines3 e.2 := (Finset.mem_filter.mp he).2
          obtain ⟨t, htT, hft⟩ := hCover e.1 e.2 heInc
          rw [← hTins] at htT
          rcases Finset.mem_insert.mp htT with rfl | htS
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, hft⟩)
          · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨t, htS, Finset.mem_filter.mpr ⟨he, hft⟩⟩)
        have h52 : 52 ≤ (incidences singerLines3).card := by
          have hx1card : x1.card = 4 := by decide
          have hprod : ((Finset.univ : Finset (Fin 13)) ×ˢ x1).card = 52 := by
            rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, hx1card]
          rw [← hprod]
          refine Finset.card_le_card_of_injOn (fun ld => (ld.1 + ld.2, ld.1)) ?_ ?_
          · intro ld hld
            have hd : ld.2 ∈ x1 := (Finset.mem_product.mp hld).2
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hMemS _ _).mp ?_⟩
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            simpa using hd
          · intro a _ b _ hab
            have h2 : a.1 = b.1 := congrArg Prod.snd hab
            have h1 : a.1 + a.2 = b.1 + b.2 := congrArg Prod.fst hab
            rw [h2] at h1
            exact Prod.ext h2 (add_left_cancel h1)
        have hle1 : (incidences singerLines3).card ≤ (cov {u, v}).card + (Tstar.biUnion cov).card :=
          (Finset.card_le_card hall).trans (Finset.card_union_le _ _)
        have hle2 : (Tstar.biUnion cov).card ≤ Tstar.card * 4 :=
          Finset.card_biUnion_le_card_mul Tstar cov 4 (fun t ht => hInputBound t (hTstarInfo t ht).2.1)
        change 8 ≤ (cov {u, v}).card
        omega
      exact oneGateTerm B Tstar u v hMono hHasAnd hTstarLe hTstarBudget huGe huLt hvGe hvLt huv
        hTstarInfo hStarEight (hTins ▸ hWit) (hTins ▸ hSafe) (hTins ▸ hCover)
