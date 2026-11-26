import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_7619_417
    (h1 :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 (26 : ℕ) C →
        (∀ (x : Fin (26 : ℕ) → Bool),
          PEqualNP.MetaComplexity.circuitFun (26 : ℕ) C x = Bool.true ↔
            ∃ (p : Fin (13 : ℕ)) (l : Fin (13 : ℕ)),
              (↑p + ↑l) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧
              x (Fin.castAdd (13 : ℕ) p) = Bool.true ∧
              x (Fin.natAdd (13 : ℕ) l) = Bool.true) →
        (63 : ℕ) ≤ C.size)
    (h2 :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 (26 : ℕ) C →
        C.output = (88 : ℕ) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C (62 : ℕ)).op =
          PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ (b : Fin (2 : ℕ)),
          ∃ (x : Fin (26 : ℕ) → Bool),
            (C.wires (List.ofFn x)).getD (PEqualNP.TopForm.opnd C (62 : ℕ) b) Bool.false = Bool.true ∧
            ¬∃ (p : Fin (13 : ℕ)) (l : Fin (13 : ℕ)),
              (↑p + ↑l) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧
              x (Fin.castAdd (13 : ℕ) p) = Bool.true ∧
              x (Fin.natAdd (13 : ℕ) l) = Bool.true) →
        (∀ (x : Fin (26 : ℕ) → Bool),
          PEqualNP.MetaComplexity.circuitFun (26 : ℕ) C x = Bool.true ↔
            ∃ (p : Fin (13 : ℕ)) (l : Fin (13 : ℕ)),
              (↑p + ↑l) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧
              x (Fin.castAdd (13 : ℕ) p) = Bool.true ∧
              x (Fin.natAdd (13 : ℕ) l) = Bool.true) →
        C.size ≠ (63 : ℕ)) :
    (let x1 : Type := Fin (26 : ℕ) → Bool; have x2 : Set (Set x1) := {∅, Set.univ} ∪ Set.range fun (x2 : Fin (26 : ℕ)) => {x3 : x1 | x3 x2 = Bool.true}; have x3 : Set x1 := {x3 : x1 | ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (↑x4 + ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true}; ∀ (x4 : Finset (Set x1)), x4.card ≤ (62 : ℕ) → (∀ x6 ∈ x4, x6 ∉ x2) → ∃ (x7 : Set (Set x1)), x2 ⊆ x7 ∧ (∀ x8 ∈ x7, ∀ x10 ∈ x7, ∀ x12 ∈ x4, x12 = x8 ∩ x10 ∨ x12 = x8 ∪ x10 → x12 ∈ x7) ∧ ∀ x8 ∈ x7, ∀ x10 ∈ x7, x8 ∩ x10 ≠ x3) := by
  classical
  dsimp only
  let X : Type := Fin 26 → Bool
  let B : Set (Set X) := {∅, Set.univ} ∪ Set.range fun i : Fin 26 => {x : X | x i = true}
  let G : Set X := {x : X | ∃ (p l : Fin 13), (p.val + l.val) % 13 ∈ [0, 1, 3, 9] ∧
    x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true}
  intro x4 hcard hdisj
  have eval_and (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have eval_or (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have getD_snoc (xs : List Bool) (a : Bool) (k : ℕ) :
      (xs ++ [a]).getD k false =
        if k < xs.length then xs.getD k false else if k = xs.length then a else false := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    split_ifs with hlt heq
    · rw [List.getElem?_append_left hlt]
    · subst heq; simp
    · rw [List.getElem?_append_right (by omega)]
      rw [List.getElem?_eq_none (by simp; omega)]
      simp
  have wires_snoc (gs : List Gate) (g : Gate) (xs : List Bool) :
      (Circuit.mk (gs ++ [g]) 0).wires xs =
        (Circuit.mk gs 0).wires xs ++
          [g.op.eval (g.inputs.map fun i => ((Circuit.mk gs 0).wires xs).getD i false)] := by
    show (gs ++ [g]).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs = _
    rw [List.foldl_append]
    rfl
  have wires_len (gs : List Gate) (xs : List Bool) :
      ((Circuit.mk gs 0).wires xs).length = xs.length + gs.length := by
    induction gs using List.reverseRecOn with
    | nil =>
      show xs.length = xs.length + 0
      omega
    | append_singleton gs g ih =>
      rw [wires_snoc, List.length_append, List.length_singleton, ih, List.length_append,
        List.length_singleton]
      omega
  have wires_getD_input (gs : List Gate) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
      ((Circuit.mk gs 0).wires xs).getD i false = xs.getD i false := by
    induction gs using List.reverseRecOn with
    | nil => rfl
    | append_singleton gs g ih =>
      rw [wires_snoc, getD_snoc, wires_len]
      have hlt : i < xs.length + gs.length := by omega
      rw [ite_eq_left hlt, ih]
  have wires_snoc_lt (gs : List Gate) (g : Gate) (x : X) (k : ℕ) (hk : k < 26 + gs.length) :
      ((Circuit.mk (gs ++ [g]) 0).wires (List.ofFn x)).getD k false =
        ((Circuit.mk gs 0).wires (List.ofFn x)).getD k false := by
    rw [wires_snoc, getD_snoc, wires_len, List.length_ofFn, ite_eq_left hk]
  have wires_snoc_eq (gs : List Gate) (g : Gate) (x : X) :
      ((Circuit.mk (gs ++ [g]) 0).wires (List.ofFn x)).getD (26 + gs.length) false =
        g.op.eval (g.inputs.map fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false) := by
    rw [wires_snoc, getD_snoc, wires_len, List.length_ofFn, ite_eq_right (Nat.lt_irrefl _), ite_eq_left rfl]
  have gateAt_snoc_lt (gs : List Gate) (g : Gate) (j : ℕ) (hj : j < gs.length) :
      gateAt ⟨gs ++ [g], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
    show (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
  have gateAt_snoc_eq (gs : List Gate) (g : Gate) :
      gateAt ⟨gs ++ [g], 0⟩ gs.length = g := by
    show (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g
    simp [List.getD_eq_getElem?_getD]
  have isAO2_snoc (gs : List Gate) (op : GateOp) (u v : ℕ)
      (hAO : IsAO2 26 ⟨gs, 0⟩)
      (hop : op = GateOp.and ∨ op = GateOp.or)
      (hu : u < 26 + gs.length) (hv : v < 26 + gs.length) :
      IsAO2 26 ⟨gs ++ [⟨op, [u, v]⟩], 0⟩ := by
    obtain ⟨hAndOr, hBack, hLen⟩ := hAO
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hAndOr g hg
      · simp only [List.mem_singleton] at hg
        subst hg
        exact hop
    · intro j hj i hi
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hlt : j < gs.length
      · rw [gateAt_snoc_lt gs _ j hlt] at hi
        exact hBack j hlt i hi
      · have hjeq : j = gs.length := by omega
        subst hjeq
        rw [gateAt_snoc_eq] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> assumption
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hLen g hg
      · simp only [List.mem_singleton] at hg
        subst hg
        rfl
  let Valid (gs : List Gate) (fs : List (Set X)) : Prop :=
    gs.length = fs.length ∧
    fs.Nodup ∧
    (∀ s ∈ fs, s ∈ x4) ∧
    IsAO2 26 ⟨gs, 0⟩ ∧
    ∀ (j : ℕ) (hj : j < fs.length),
      {x : X | ((Circuit.mk gs 0).wires (List.ofFn x)).getD (26 + j) false = true} = fs[j]
  have valid_nil : Valid [] [] := by
    refine ⟨rfl, List.nodup_nil, (fun _ h => by cases h), ⟨?_, ?_, ?_⟩, (fun _ hj => by simp at hj)⟩
    · intro g hg; cases hg
    · intro j hj; simp at hj
    · intro g hg; cases hg
  have valid_len_le (gs : List Gate) (fs : List (Set X)) (hv : Valid gs fs) :
      fs.length ≤ x4.card := by
    have hsub : fs.toFinset ⊆ x4 := by
      intro s hs
      exact hv.2.2.1 s (List.mem_toFinset.mp hs)
    have hcard_eq : fs.toFinset.card = fs.length := List.toFinset_card_of_nodup hv.2.1
    rw [← hcard_eq]
    exact Finset.card_le_card hsub
  have lookup_wire (gs : List Gate) (fs : List (Set X)) (hv : Valid gs fs)
      (s : Set X) (hs : s ∈ B ∪ {t | t ∈ fs}) (hne : s ≠ ∅) (hnu : s ≠ Set.univ) :
      ∃ w < 26 + gs.length,
        {x : X | ((Circuit.mk gs 0).wires (List.ofFn x)).getD w false = true} = s := by
    rcases hs with hsB | hsF
    · rcases hsB with hconst | ⟨i, rfl⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hconst
        rcases hconst with rfl | rfl
        · exact absurd rfl hne
        · exact absurd rfl hnu
      · refine ⟨i.val, by omega, ?_⟩
        ext x
        simp only [Set.mem_ofPred_eq]
        rw [wires_getD_input gs (List.ofFn x) i.val (by simp)]
        rw [List.getD_eq_getElem _ _ (by simp)]
        rw [List.getElem_ofFn]
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hsF
      exact ⟨26 + j, by rw [hv.1]; omega, hv.2.2.2.2 j hj⟩
  have extend_valid (gs : List Gate) (fs : List (Set X)) (hv : Valid gs fs)
      (a b z : Set X)
      (ha : a ∈ B ∪ {t | t ∈ fs}) (hb : b ∈ B ∪ {t | t ∈ fs})
      (hz : z ∈ x4) (hzF : z ∉ fs) (hcomb : z = a ∩ b ∨ z = a ∪ b) :
      ∃ g : Gate, Valid (gs ++ [g]) (fs ++ [z]) := by
    have hzB : z ∉ B := hdisj z hz
    have hzU : z ∉ B ∪ {t | t ∈ fs} := fun h => h.elim hzB hzF
    have hemptyB : (∅ : Set X) ∈ B := Or.inl (by simp)
    have hunivB : (Set.univ : Set X) ∈ B := Or.inl (by simp)
    have ha_ne : a ≠ ∅ := by
      intro h; subst h
      rcases hcomb with rfl | rfl
      · exact hzB (by simpa using hemptyB)
      · exact hzU (by simpa using hb)
    have ha_nu : a ≠ Set.univ := by
      intro h; subst h
      rcases hcomb with rfl | rfl
      · exact hzU (by simpa using hb)
      · exact hzB (by simpa using hunivB)
    have hb_ne : b ≠ ∅ := by
      intro h; subst h
      rcases hcomb with rfl | rfl
      · exact hzB (by simpa using hemptyB)
      · exact hzU (by simpa using ha)
    have hb_nu : b ≠ Set.univ := by
      intro h; subst h
      rcases hcomb with rfl | rfl
      · exact hzU (by simpa using ha)
      · exact hzB (by simpa using hunivB)
    obtain ⟨u, hu, hwu⟩ := lookup_wire gs fs hv a ha ha_ne ha_nu
    obtain ⟨v, hv_lt, hwv⟩ := lookup_wire gs fs hv b hb hb_ne hb_nu
    rcases hcomb with hcap | hcup
    · refine ⟨⟨GateOp.and, [u, v]⟩, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hv.1]
      · exact List.nodup_append.mpr ⟨hv.2.1, List.nodup_singleton z,
          fun x hx y hy => by simp only [List.mem_singleton] at hy; subst hy; exact fun h => hzF (h ▸ hx)⟩
      · intro s hs
        rcases List.mem_append.mp hs with hs | hs
        · exact hv.2.2.1 s hs
        · simp only [List.mem_singleton] at hs; exact hs ▸ hz
      · exact isAO2_snoc gs GateOp.and u v hv.2.2.2.1 (Or.inl rfl) hu hv_lt
      · intro j hj
        simp only [List.length_append, List.length_singleton] at hj
        by_cases hlt : j < fs.length
        · rw [List.getElem_append_left hlt]
          have hlt' : 26 + j < 26 + gs.length := by rw [hv.1]; omega
          have heq := hv.2.2.2.2 j hlt
          rw [← heq]
          ext x
          simp only [Set.mem_ofPred_eq, wires_snoc_lt gs _ x (26 + j) hlt']
        · have hjeq : j = fs.length := by omega
          subst hjeq
          rw [List.getElem_append_right (le_refl _)]
          simp only [Nat.sub_self, List.getElem_cons_zero]
          ext x
          simp only [Set.mem_ofPred_eq]
          rw [← hv.1, wires_snoc_eq, eval_and]
          simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
            Bool.and_true, Bool.and_eq_true]
          have hxu : ((Circuit.mk gs 0).wires (List.ofFn x)).getD u false = true ↔ x ∈ a := by
            rw [← hwu]; rfl
          have hxv : ((Circuit.mk gs 0).wires (List.ofFn x)).getD v false = true ↔ x ∈ b := by
            rw [← hwv]; rfl
          rw [hxu, hxv, hcap]
          rfl
    · refine ⟨⟨GateOp.or, [u, v]⟩, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hv.1]
      · exact List.nodup_append.mpr ⟨hv.2.1, List.nodup_singleton z,
          fun x hx y hy => by simp only [List.mem_singleton] at hy; subst hy; exact fun h => hzF (h ▸ hx)⟩
      · intro s hs
        rcases List.mem_append.mp hs with hs | hs
        · exact hv.2.2.1 s hs
        · simp only [List.mem_singleton] at hs; exact hs ▸ hz
      · exact isAO2_snoc gs GateOp.or u v hv.2.2.2.1 (Or.inr rfl) hu hv_lt
      · intro j hj
        simp only [List.length_append, List.length_singleton] at hj
        by_cases hlt : j < fs.length
        · rw [List.getElem_append_left hlt]
          have hlt' : 26 + j < 26 + gs.length := by rw [hv.1]; omega
          have heq := hv.2.2.2.2 j hlt
          rw [← heq]
          ext x
          simp only [Set.mem_ofPred_eq, wires_snoc_lt gs _ x (26 + j) hlt']
        · have hjeq : j = fs.length := by omega
          subst hjeq
          rw [List.getElem_append_right (le_refl _)]
          simp only [Nat.sub_self, List.getElem_cons_zero]
          ext x
          simp only [Set.mem_ofPred_eq]
          rw [← hv.1, wires_snoc_eq, eval_or]
          simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
            Bool.or_false, Bool.or_eq_true]
          have hxu : ((Circuit.mk gs 0).wires (List.ofFn x)).getD u false = true ↔ x ∈ a := by
            rw [← hwu]; rfl
          have hxv : ((Circuit.mk gs 0).wires (List.ofFn x)).getD v false = true ↔ x ∈ b := by
            rw [← hwv]; rfl
          rw [hxu, hxv, hcup]
          rfl
  have build : ∀ (k : ℕ) (gs : List Gate) (fs : List (Set X)),
      Valid gs fs → x4.card - fs.length ≤ k →
      ∃ gs' fs', Valid gs' fs' ∧
        ∀ a ∈ B ∪ {s | s ∈ fs'}, ∀ b ∈ B ∪ {s | s ∈ fs'}, ∀ z ∈ x4,
          z = a ∩ b ∨ z = a ∪ b → z ∈ B ∪ {s | s ∈ fs'} := by
    intro k
    induction k with
    | zero =>
      intro gs fs hv hk
      refine ⟨gs, fs, hv, ?_⟩
      intro a ha b hb z hz hcomb
      by_contra hnot
      have hzF : z ∉ fs := fun h => hnot (Or.inr h)
      obtain ⟨g, hv'⟩ := extend_valid gs fs hv a b z ha hb hz hzF hcomb
      have hle := valid_len_le (gs ++ [g]) (fs ++ [z]) hv'
      simp only [List.length_append, List.length_singleton] at hle
      omega
    | succ k ih =>
      intro gs fs hv hk
      by_cases hcl : ∀ a ∈ B ∪ {s | s ∈ fs}, ∀ b ∈ B ∪ {s | s ∈ fs}, ∀ z ∈ x4,
          z = a ∩ b ∨ z = a ∪ b → z ∈ B ∪ {s | s ∈ fs}
      · exact ⟨gs, fs, hv, hcl⟩
      · push Not at hcl
        obtain ⟨a, ha, b, hb, z, hz, hcomb, hnot⟩ := hcl
        have hzF : z ∉ fs := fun h => hnot (Or.inr h)
        obtain ⟨g, hv'⟩ := extend_valid gs fs hv a b z ha hb hz hzF hcomb
        have hle := valid_len_le (gs ++ [g]) (fs ++ [z]) hv'
        simp only [List.length_append, List.length_singleton] at hle
        exact ih (gs ++ [g]) (fs ++ [z]) hv' (by simp; omega)
  obtain ⟨gs, fs, hvalid, hclosed⟩ := build x4.card [] [] valid_nil (by simp)
  refine ⟨B ∪ {s | s ∈ fs}, Set.subset_union_left, hclosed, ?_⟩
  intro a ha b hb hab
  change a ∩ b = G at hab
  have hG_ne_empty : G ≠ ∅ := by
    intro h
    let x0 : X := fun i => decide (i = Fin.castAdd 13 (0 : Fin 13) ∨ i = Fin.natAdd 13 (0 : Fin 13))
    have hx0 : x0 ∈ G := ⟨0, 0, by decide, by simp [x0], by simp [x0]⟩
    rw [h] at hx0
    exact hx0
  have hG_ne_univ : G ≠ Set.univ := by
    intro h
    have hx : (fun _ : Fin 26 => false) ∈ G := by rw [h]; trivial
    obtain ⟨p, l, _, hp, _⟩ := hx
    exact Bool.false_ne_true hp
  have hG_not_sub_var : ∀ i : Fin 26, ¬ (G ⊆ {x : X | x i = true}) := by
    intro i hsub
    by_cases hi : i.val < 13
    · let p : Fin 13 := ⟨(i.val + 1) % 13, Nat.mod_lt _ (by omega)⟩
      let l : Fin 13 := ⟨(13 - p.val) % 13, Nat.mod_lt _ (by omega)⟩
      let x0 : X := fun j => decide (j = Fin.castAdd 13 p ∨ j = Fin.natAdd 13 l)
      have hinc : (p.val + l.val) % 13 ∈ [0, 1, 3, 9] := by
        have hp : p.val < 13 := p.isLt
        have hmod : (p.val + (13 - p.val) % 13) % 13 = 0 := by omega
        simp [p, l, hmod]
      have hxG : x0 ∈ G := ⟨p, l, hinc, by simp [x0], by simp [x0]⟩
      have hxi : x0 i = true := hsub hxG
      simp only [x0, decide_eq_true_eq] at hxi
      rcases hxi with h1 | h2
      · have hv1 := congrArg Fin.val h1
        simp only [Fin.val_castAdd, p] at hv1
        omega
      · have hv2 := congrArg Fin.val h2
        simp only [Fin.val_natAdd] at hv2
        omega
    · let l : Fin 13 := ⟨(i.val - 13 + 1) % 13, Nat.mod_lt _ (by omega)⟩
      let p : Fin 13 := ⟨(13 - l.val) % 13, Nat.mod_lt _ (by omega)⟩
      let x0 : X := fun j => decide (j = Fin.castAdd 13 p ∨ j = Fin.natAdd 13 l)
      have hinc : (p.val + l.val) % 13 ∈ [0, 1, 3, 9] := by
        have hl : l.val < 13 := l.isLt
        have hmod : ((13 - l.val) % 13 + l.val) % 13 = 0 := by omega
        simp [p, l, hmod]
      have hxG : x0 ∈ G := ⟨p, l, hinc, by simp [x0], by simp [x0]⟩
      have hxi : x0 i = true := hsub hxG
      simp only [x0, decide_eq_true_eq] at hxi
      rcases hxi with h1 | h2
      · have hv1 := congrArg Fin.val h1
        simp only [Fin.val_castAdd] at hv1
        have hp : p.val < 13 := p.isLt
        omega
      · have hv2 := congrArg Fin.val h2
        simp only [Fin.val_natAdd, l] at hv2
        omega
  have hG_not_B : G ∉ B := by
    rintro (hc | ⟨i, hi⟩)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with h | h
      · exact hG_ne_empty h
      · exact hG_ne_univ h
    · exact hG_not_sub_var i (hi ▸ Set.Subset.rfl)
  have hfs_le : fs.length ≤ 62 := (valid_len_le gs fs hvalid).trans hcard
  by_cases hGfs : G ∈ fs
  · obtain ⟨k, hk, hfk⟩ := List.mem_iff_getElem.mp hGfs
    let C : Circuit := ⟨gs, 26 + k⟩
    have hAO_C : IsAO2 26 C := hvalid.2.2.2.1
    have hfun_C : ∀ x : X, circuitFun 26 C x = true ↔
        ∃ (p l : Fin 13), (p.val + l.val) % 13 ∈ [0, 1, 3, 9] ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
      intro x
      have hw := hvalid.2.2.2.2 k hk
      rw [hfk] at hw
      have hmem : x ∈ {y : X | ((Circuit.mk gs 0).wires (List.ofFn y)).getD (26 + k) false = true} ↔ x ∈ G := by
        rw [hw]
      exact hmem
    have h63 := h1 C hAO_C hfun_C
    have hsz : C.size ≤ 62 := by
      show gs.length ≤ 62
      rw [hvalid.1]
      exact hfs_le
    omega
  · have hGa : G ⊆ a := fun x hx => (hab ▸ hx).1
    have hGb : G ⊆ b := fun x hx => (hab ▸ hx).2
    have ha_not_B : a ∉ B := by
      rintro (hc | ⟨i, hi⟩)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
        rcases hc with rfl | rfl
        · exact hG_ne_empty (Set.subset_empty_iff.mp hGa)
        · have hbG : b = G := by rw [← Set.univ_inter b, hab]
          rcases hb with hbB | hbF
          · exact hG_not_B (hbG ▸ hbB)
          · exact hGfs (hbG ▸ hbF)
      · dsimp only at hi
        subst hi
        exact hG_not_sub_var i hGa
    have hb_not_B : b ∉ B := by
      rintro (hc | ⟨i, hi⟩)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
        rcases hc with rfl | rfl
        · exact hG_ne_empty (Set.subset_empty_iff.mp hGb)
        · have haG : a = G := by rw [← Set.inter_univ a, hab]
          rcases ha with haB | haF
          · exact hG_not_B (haG ▸ haB)
          · exact hGfs (haG ▸ haF)
      · dsimp only at hi
        subst hi
        exact hG_not_sub_var i hGb
    have haF : a ∈ fs := ha.elim (fun h => absurd h ha_not_B) id
    have hbF : b ∈ fs := hb.elim (fun h => absurd h hb_not_B) id
    obtain ⟨p, hp, hfp⟩ := List.mem_iff_getElem.mp haF
    obtain ⟨q, hq, hfq⟩ := List.mem_iff_getElem.mp hbF
    have hp_lt : 26 + p < 26 + gs.length := by rw [hvalid.1]; omega
    have hq_lt : 26 + q < 26 + gs.length := by rw [hvalid.1]; omega
    let gtop : Gate := ⟨GateOp.and, [26 + p, 26 + q]⟩
    let C : Circuit := ⟨gs ++ [gtop], 26 + gs.length⟩
    have hAO_C : IsAO2 26 C := isAO2_snoc gs GateOp.and (26 + p) (26 + q) hvalid.2.2.2.1 (Or.inl rfl) hp_lt hq_lt
    have hfun_C : ∀ x : X, circuitFun 26 C x = true ↔
        ∃ (p' l' : Fin 13), (p'.val + l'.val) % 13 ∈ [0, 1, 3, 9] ∧
          x (Fin.castAdd 13 p') = true ∧ x (Fin.natAdd 13 l') = true := by
      intro x
      have hxp : ((Circuit.mk gs 0).wires (List.ofFn x)).getD (26 + p) false = true ↔ x ∈ a := by
        have hw := hvalid.2.2.2.2 p hp
        rw [hfp] at hw
        have hm : x ∈ {y : X | ((Circuit.mk gs 0).wires (List.ofFn y)).getD (26 + p) false = true} ↔ x ∈ a := by
          rw [hw]
        simpa using hm
      have hxq : ((Circuit.mk gs 0).wires (List.ofFn x)).getD (26 + q) false = true ↔ x ∈ b := by
        have hw := hvalid.2.2.2.2 q hq
        rw [hfq] at hw
        have hm : x ∈ {y : X | ((Circuit.mk gs 0).wires (List.ofFn y)).getD (26 + q) false = true} ↔ x ∈ b := by
          rw [hw]
        simpa using hm
      have hce : circuitFun 26 C x = ((Circuit.mk (gs ++ [gtop]) 0).wires (List.ofFn x)).getD (26 + gs.length) false := rfl
      rw [hce, wires_snoc_eq, eval_and]
      simp only [gtop, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
        Bool.and_true, Bool.and_eq_true, hxp, hxq]
      have hmem : x ∈ a ∩ b ↔ x ∈ G := by rw [hab]
      simpa [G] using hmem
    have h63 := h1 C hAO_C hfun_C
    have hCsz_le : C.size ≤ 63 := by
      show (gs ++ [gtop]).length ≤ 63
      simp only [List.length_append, List.length_singleton]
      rw [hvalid.1]
      omega
    have hCsz : C.size = 63 := by omega
    have hgs62 : gs.length = 62 := by
      have : (gs ++ [gtop]).length = 63 := hCsz
      simp only [List.length_append, List.length_singleton] at this
      omega
    have hCout : C.output = 88 := by
      show 26 + gs.length = 88
      omega
    have hgate62 : gateAt C 62 = gtop := by
      have := gateAt_snoc_eq gs gtop
      rw [hgs62] at this
      exact this
    have hop62 : (gateAt C 62).op = GateOp.and := by rw [hgate62]
    have ha_ne_G : a ≠ G := fun h => hGfs (h ▸ haF)
    have hb_ne_G : b ≠ G := fun h => hGfs (h ▸ hbF)
    have hex_a : ∃ x ∈ a, x ∉ G := by
      by_contra hno
      push Not at hno
      exact ha_ne_G (Set.Subset.antisymm hno hGa)
    have hex_b : ∃ x ∈ b, x ∉ G := by
      by_contra hno
      push Not at hno
      exact hb_ne_G (Set.Subset.antisymm hno hGb)
    have hdirty : ∀ (b' : Fin 2), ∃ (x : X),
        (C.wires (List.ofFn x)).getD (opnd C 62 b') false = true ∧
        ¬∃ (p' l' : Fin 13), (p'.val + l'.val) % 13 ∈ [0, 1, 3, 9] ∧
          x (Fin.castAdd 13 p') = true ∧ x (Fin.natAdd 13 l') = true := by
      intro b'
      fin_cases b'
      · obtain ⟨x, hxa, hxG⟩ := hex_a
        refine ⟨x, ?_, hxG⟩
        have hop0 : opnd C 62 0 = 26 + p := by
          show (gateAt C 62).inputs.getD 0 0 = 26 + p
          rw [hgate62]
          rfl
        change (C.wires (List.ofFn x)).getD (opnd C 62 0) false = true
        rw [hop0]
        change ((Circuit.mk (gs ++ [gtop]) 0).wires (List.ofFn x)).getD (26 + p) false = true
        rw [wires_snoc_lt gs gtop x (26 + p) hp_lt]
        have hw := hvalid.2.2.2.2 p hp
        rw [hfp] at hw
        have hm : x ∈ {y : X | ((Circuit.mk gs 0).wires (List.ofFn y)).getD (26 + p) false = true} := by
          rw [hw]; exact hxa
        exact hm
      · obtain ⟨x, hxb, hxG⟩ := hex_b
        refine ⟨x, ?_, hxG⟩
        have hop1 : opnd C 62 1 = 26 + q := by
          show (gateAt C 62).inputs.getD 1 0 = 26 + q
          rw [hgate62]
          rfl
        change (C.wires (List.ofFn x)).getD (opnd C 62 1) false = true
        rw [hop1]
        change ((Circuit.mk (gs ++ [gtop]) 0).wires (List.ofFn x)).getD (26 + q) false = true
        rw [wires_snoc_lt gs gtop x (26 + q) hq_lt]
        have hw := hvalid.2.2.2.2 q hq
        rw [hfq] at hw
        have hm : x ∈ {y : X | ((Circuit.mk gs 0).wires (List.ofFn y)).getD (26 + q) false = true} := by
          rw [hw]; exact hxb
        exact hm
    exact h2 C hAO_C hCout hop62 hdirty hfun_C hCsz
