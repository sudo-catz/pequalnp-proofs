import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.CircuitMoves (eraseRedirect)
open PEqualNP.EdgeOwnership (pairInput)

set_option maxHeartbeats 1000000 in
/-- Reduce to a smaller gate budget and to size-124 circuits with two distinct earlier
operands per gate, a necessary incident pair at each gate, and a marked input of size
at most two that activates the first AND to fire on the full marked input. -/
theorem PEqualNP.Outside.R_meta_1894_731
    (small :
      let incident := fun u v : Fin 42 =>
        u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      ∀ C : Circuit, Monotone2 C → C.size ≤ 123 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack 42 C →
        (∀ j < C.gates.length, ∃ a b : ℕ, a ≠ b ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [a, b]) →
        (∀ k < C.gates.length, ∃ u v : Fin 42, incident u v ∧
          (PEqualNP.CircuitMoves.eraseGate 42 C k (42 + C.gates.length)).eval
            (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) = false) →
        ¬ (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ u v : Fin 42, incident u v ∧ x u = true ∧ x v = true))
    (essentialCase :
      let incident := fun u v : Fin 42 =>
        u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      let marked := fun i : Fin 42 =>
        decide (i.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ))
      ∀ C : Circuit, Monotone2 C → C.size = 124 →
        C.output = 165 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack 42 C →
        (∀ j < C.gates.length, ∃ a b : ℕ, a ≠ b ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [a, b]) →
        (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ u v : Fin 42, incident u v ∧ x u = true ∧ x v = true) →
        (∃ (k : ℕ) (g : Gate) (u v : Fin 42) (a b : ℕ), C.gates[k]? = some g ∧
          g.op = .and ∧ g.inputs = [a, b] ∧ marked u = true ∧ marked v = true ∧
          (C.wires (List.ofFn fun i : Fin 42 => decide (i = u))).getD a false = true ∧
          (C.wires (List.ofFn fun i : Fin 42 => decide (i = v))).getD b false = true ∧
          (C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).getD (42 + k) false = true ∧
          ∀ j < k, ¬ ∃ f : Gate, C.gates[j]? = some f ∧ f.op = .and ∧
            (C.wires (List.ofFn marked)).getD (42 + j) false = true) →
        (∀ k < C.gates.length, ∃ u v : Fin 42, incident u v ∧
          (PEqualNP.CircuitMoves.eraseGate 42 C k (42 + C.gates.length)).eval
            (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) = false) →
        False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 →
      x1.size ≤ (124 : ℕ) →
      (∃ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x4]? = Option.some x5 ∧
        x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (x1.wires (List.ofFn fun (x6 : Fin (42 : ℕ)) => Decidable.decide
          (↑x6 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ),
            (31 : ℕ), (33 : ℕ), (37 : ℕ)]))).getD ((42 : ℕ) + x4) Bool.false = Bool.true) →
      ∃ (x5 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x5) = Bool.true ↔
        ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), (↑x6 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧
          (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧
          x5 x6 = Bool.true ∧ x5 x7 = Bool.true) := by
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
    simp only [step, List.length_append, List.length_singleton]

  have run_length (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih, step_length, Nat.add_right_comm]
      rfl

  let Below (w v : List Bool) : Prop :=
    ∀ i, w.getD i false = true → v.getD i false = true

  have append_below {w v : List Bool} {a b : Bool} (hlen : w.length = v.length)
      (hw : Below w v) (hab : a = true → b = true) : Below (w ++ [a]) (v ++ [b]) := by
    intro i hi
    by_cases h : i < w.length
    · rw [List.getD_append _ _ _ _ h] at hi
      rw [List.getD_append _ _ _ _ (hlen ▸ h)]
      exact hw i hi
    · have h' : w.length ≤ i := Nat.le_of_not_gt h
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h'] at hi
      have hv : v.length ≤ i := hlen ▸ h'
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hv, ← hlen]
      cases hidx : i - w.length with
      | zero => simpa [hidx] using hab (by simpa [hidx] using hi)
      | succ j => simp [hidx] at hi

  have step_below {g : Gate} (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
      {w v : List Bool} (hlen : w.length = v.length) (hw : Below w v) :
      Below (step w g) (step v g) := by
    apply append_below hlen hw
    rcases Set.mem_insert_iff.mp hop with hop | hop
    · rw [hop]
      change (g.inputs.map (fun i => w.getD i false)).all id = true →
        (g.inputs.map (fun i => v.getD i false)).all id = true
      simp only [List.all_map]
      exact fun h => List.all_eq_true.mpr fun i hi => hw i (List.all_eq_true.mp h i hi)
    · rw [Set.mem_singleton_iff.mp hop]
      change (g.inputs.map (fun i => w.getD i false)).any id = true →
        (g.inputs.map (fun i => v.getD i false)).any id = true
      simp only [List.any_map]
      intro h
      obtain ⟨i, hi, ht⟩ := List.any_eq_true.mp h
      exact List.any_eq_true.mpr ⟨i, hi, hw i ht⟩

  have run_below (gs : List Gate)
      (hm : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
      {w v : List Bool} (hlen : w.length = v.length) (hw : Below w v) :
      Below (gs.foldl step w) (gs.foldl step v) := by
    induction gs generalizing w v with
    | nil => exact hw
    | cons g gs ih =>
      simp only [List.foldl_cons]
      exact ih (fun a ha => hm a (List.mem_cons_of_mem _ ha)) (by simp [step, hlen])
        (step_below (hm g (by simp)) hlen hw)

  have wires_mono {n : ℕ} {C : Circuit} (hm : Monotone2 C)
      {x y : Fin n → Bool} (h : ∀ i, x i = true → y i = true) :
      Below (C.wires (List.ofFn x)) (C.wires (List.ofFn y)) := by
    apply run_below C.gates (fun g hg => (hm g hg).1) (by simp) _
    intro i hi
    by_cases hin : i < n
    · simpa [List.getD_eq_getElem?_getD, hin] using h ⟨i, hin⟩ (by
        simpa [List.getD_eq_getElem?_getD, hin] using hi)
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hin)] at hi
      contradiction

  have eval_mono {n : ℕ} {C : Circuit} (hm : Monotone2 C)
      {x y : Fin n → Bool} (h : ∀ i, x i = true → y i = true) :
      C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true :=
    wires_mono hm h C.output

  let redirectInputs (k dead : ℕ) (g : Gate) : Gate :=
    ⟨g.op, g.inputs.map (eraseRedirect 42 k dead)⟩

  let eraseGate (C : Circuit) (k dest : ℕ) : Circuit :=
    PEqualNP.CircuitMoves.eraseGate 42 C k dest

  have erase_eq (C : Circuit) (k dest : ℕ) :
      eraseGate C k dest =
        if k < C.gates.length then
          ⟨C.gates.take k ++ (C.gates.drop (k + 1)).map (redirectInputs k dest),
            eraseRedirect 42 k dest C.output⟩
        else C := rfl

  have erase_size {C : Circuit} {k : ℕ} (hk : k < C.gates.length) (dest : ℕ) :
      (eraseGate C k dest).size + 1 = C.size := by
    change (eraseGate C k dest).gates.length + 1 = C.gates.length
    rw [erase_eq, ite_eq_left hk]
    simp only [List.length_append, List.length_take, List.length_map, List.length_drop,
      Nat.min_eq_left hk.le]
    calc
      k + (C.gates.length - (k + 1)) + 1 = (C.gates.length - (k + 1)) + (k + 1) := by
        rw [Nat.add_comm k, Nat.add_assoc]
      _ = C.gates.length := Nat.sub_add_cancel hk

  have erase_mono {C : Circuit} (hm : Monotone2 C) (k dest : ℕ) :
      Monotone2 (eraseGate C k dest) := by
    intro g hg
    by_cases hk : k < C.gates.length
    · rw [erase_eq, ite_eq_left hk] at hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hm g (List.mem_of_mem_take hg)
      · obtain ⟨original, hmem, heq⟩ := List.mem_map.mp hg
        rw [← heq]
        obtain ⟨hop, hlen⟩ := hm original (List.mem_of_mem_drop hmem)
        exact ⟨hop, by simpa [redirectInputs] using hlen⟩
    · exact hm g (by simpa only [erase_eq, ite_eq_right hk] using hg)

  have rename_other (v : List Bool) (k dest : ℕ) {i : ℕ} (hi : i ≠ 42 + k) :
      (v.eraseIdx (42 + k)).getD (eraseRedirect 42 k dest i) false = v.getD i false := by
    change (v.eraseIdx (42 + k)).getD (if i = 42 + k then dest else if 42 + k < i then i - 1 else i) false = _
    rw [ite_eq_right hi]
    by_cases h : 42 + k < i
    · have hge : 42 + k ≤ i - 1 := Nat.le_sub_of_add_le h
      have heq : i - 1 + 1 = i := Nat.sub_add_cancel ((Nat.succ_le_succ (Nat.zero_le _)).trans h)
      simp [ite_eq_left h, List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_ge hge, heq]
    · have hlt : i < 42 + k := Nat.lt_of_le_of_ne (Nat.le_of_not_gt h) hi
      simp [ite_eq_right h, List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_lt hlt]

  have read_erased {v : List Bool} {k dest : ℕ}
      (hrep : dest < 42 + k ∨ v.length ≤ dest)
      (hval : v.getD dest false = v.getD (42 + k) false) (i : ℕ) :
      (v.eraseIdx (42 + k)).getD (eraseRedirect 42 k dest i) false = v.getD i false := by
    by_cases hi : i = 42 + k
    · subst i
      change (v.eraseIdx (42 + k)).getD (if 42 + k = 42 + k then dest else _) false = _
      rw [ite_eq_left rfl, ← hval]
      rcases hrep with hearly | hdead
      · simp [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_lt hearly]
      · rw [List.getD_eq_default _ _ ((List.length_eraseIdx_le v _).trans hdead),
          List.getD_eq_default _ _ hdead]
    · exact rename_other v k dest hi

  have append_eq_reads {w : List Bool} {k dest : ℕ} (hp : 42 + k < w.length)
      (hdest : dest < 42 + k ∨ w.length + 1 ≤ dest)
      (hval : w.getD dest false = w.getD (42 + k) false) (b : Bool) :
      (w ++ [b]).getD dest false = (w ++ [b]).getD (42 + k) false := by
    rw [List.getD_append _ _ _ _ hp, ← hval]
    rcases hdest with hearly | hdead
    · exact List.getD_append _ _ _ _ (hearly.trans hp)
    · rw [List.getD_eq_default _ _ (by simpa using hdead),
        List.getD_eq_default _ _ ((Nat.le_succ _).trans hdead)]

  have run_erased (k dest : ℕ) (gs : List Gate) (v : List Bool)
      (hp : 42 + k < v.length) (hdest : dest < 42 + k ∨ v.length + gs.length ≤ dest)
      (hval : v.getD dest false = v.getD (42 + k) false) :
      (gs.map (redirectInputs k dest)).foldl step (v.eraseIdx (42 + k)) =
          (gs.foldl step v).eraseIdx (42 + k) ∧
        (gs.foldl step v).getD dest false = (gs.foldl step v).getD (42 + k) false := by
    induction gs generalizing v with
    | nil => exact ⟨rfl, hval⟩
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons]
      have hnow := hdest.imp id (fun h => (Nat.le_add_right _ _).trans h)
      have he : step (v.eraseIdx (42 + k)) (redirectInputs k dest g) =
          (step v g).eraseIdx (42 + k) := by
        simp only [step, redirectInputs, List.eraseIdx_append_of_lt_length hp, List.map_map]
        congr 2
        apply congrArg (GateOp.eval g.op)
        exact List.map_congr_left fun i _ => read_erased hnow hval i
      rw [he]
      have hnext : dest < 42 + k ∨ (step v g).length + gs.length ≤ dest := by
        simpa only [step_length, List.length_cons, Nat.add_right_comm v.length 1,
          Nat.add_assoc] using hdest
      apply ih _ (by rw [step_length]; exact hp.trans (Nat.lt_succ_self _)) hnext
      apply append_eq_reads hp _ hval
      rw [step_length] at hnext
      exact hnext.imp id (fun h => (Nat.le_add_right _ _).trans h)

  have run_preserves (gs : List Gate) (v : List Bool) (i : ℕ) (hi : i < v.length) :
      (gs.foldl step v).getD i false = v.getD i false := by
    induction gs generalizing v with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by rw [step_length]; exact hi.trans (Nat.lt_succ_self _))]
      exact List.getD_append _ _ _ _ hi

  let beforeGate (C : Circuit) (k : ℕ) (x : Fin 42 → Bool) :=
    (C.gates.take k).foldl step (List.ofFn x)

  have prefix_length {C : Circuit} {k : ℕ} (hk : k ≤ C.gates.length) (x : Fin 42 → Bool) :
      (beforeGate C k x).length = 42 + k := by
    simp [beforeGate, run_length, Nat.min_eq_left hk]

  -- Read the erased wire from an earlier wire, or from the out-of-range false wire.
  have erase_eval {C : Circuit} {k dest : ℕ} (hk : k < C.gates.length) (x : Fin 42 → Bool)
      (hdest : dest < 42 + k ∨ 42 + C.gates.length ≤ dest) :
      (eraseGate C k dest).eval (List.ofFn x) =
        ((C.gates.drop (k + 1)).foldl step
          (beforeGate C k x ++ [(beforeGate C k x).getD dest false])).getD C.output false := by
    let w := beforeGate C k x
    let gs := C.gates.drop (k + 1)
    let v := w ++ [w.getD dest false]
    let p := 42 + k
    have hw : w.length = p := prefix_length hk.le x
    have hlen : v.length + gs.length = 42 + C.gates.length := by
      change (w ++ [_]).length + (C.gates.drop (k + 1)).length = 42 + C.gates.length
      simp only [List.length_append, List.length_singleton, List.length_drop, hw]
      change (42 + k + 1) + (C.gates.length - (k + 1)) = 42 + C.gates.length
      rw [Nat.add_assoc 42 k 1, Nat.add_assoc, Nat.add_sub_of_le hk]
    have hv : p < v.length := by simp [v, hw]
    have hval : v.getD dest false = v.getD p false := by
      have he : v.getD p false = w.getD dest false := by rw [← hw]; simp [v]
      rw [he]
      rcases hdest with hearly | hdead
      · exact List.getD_append _ _ _ _ (hw ▸ hearly)
      · have hle : v.length ≤ dest := (Nat.le_add_right _ _).trans (hlen ▸ hdead)
        rw [List.getD_eq_default _ _ hle,
          List.getD_eq_default _ _ ((show w.length ≤ v.length by simp [v]).trans hle)]
    have he : v.eraseIdx p = w := by
      simp [v, ← hw, List.eraseIdx_append_of_length_le]
    rw [erase_eq, ite_eq_left hk]
    change ((C.gates.take k ++ gs.map (redirectInputs k dest)).foldl step (List.ofFn x)).getD
      (eraseRedirect 42 k dest C.output) false = _
    rw [List.foldl_append]
    change ((gs.map (redirectInputs k dest)).foldl step w).getD
      (eraseRedirect 42 k dest C.output) false = _
    have hr := run_erased k dest gs v hv (by rw [hlen]; exact hdest) hval
    rw [← he, hr.1]
    exact read_erased (by rw [run_length, hlen]; exact hdest) hr.2 _

  have wires_split {C : Circuit} {k : ℕ} (hk : k < C.gates.length) (x : Fin 42 → Bool) :
      C.wires (List.ofFn x) =
        (C.gates.drop (k + 1)).foldl step (step (beforeGate C k x) C.gates[k]) := by
    have hsplit : C.gates = C.gates.take k ++ C.gates[k] :: C.gates.drop (k + 1) := by simp
    change C.gates.foldl step (List.ofFn x) = _
    conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]

  have eval_split {C : Circuit} {k : ℕ} (hk : k < C.gates.length) (x : Fin 42 → Bool) :
      C.eval (List.ofFn x) =
        ((C.gates.drop (k + 1)).foldl step (step (beforeGate C k x) C.gates[k])).getD
          C.output false :=
    congrArg (fun w : List Bool => w.getD C.output false) (wires_split hk x)

  have gate_wire {C : Circuit} {k : ℕ} (hk : k < C.gates.length) (x : Fin 42 → Bool) :
      (C.wires (List.ofFn x)).getD (42 + k) false =
        C.gates[k].op.eval (C.gates[k].inputs.map fun i => (beforeGate C k x).getD i false) := by
    rw [wires_split hk x, run_preserves]
    · change ((beforeGate C k x) ++ [_]).getD (42 + k) false = _
      rw [← prefix_length hk.le x]
      simp
    · rw [step_length, prefix_length hk.le]
      exact Nat.lt_succ_self _

  let eraseFalse (C : Circuit) (k : ℕ) := eraseGate C k (42 + C.gates.length)

  have erase_below {C : Circuit} (hm : Monotone2 C) {k : ℕ}
      (hk : k < C.gates.length) (x : Fin 42 → Bool) :
      (eraseFalse C k).eval (List.ofFn x) = true → C.eval (List.ofFn x) = true := by
    change (eraseGate C k (42 + C.gates.length)).eval (List.ofFn x) = true → _
    have hdead : (beforeGate C k x).getD (42 + C.gates.length) false = false :=
      List.getD_eq_default _ _ (by rw [prefix_length hk.le]; exact Nat.add_le_add_left hk.le _)
    rw [erase_eval hk x (Or.inr (Nat.le_refl _)), eval_split hk x, hdead]
    apply run_below _ (fun g hg => (hm g (List.mem_of_mem_drop hg)).1) (by simp [step]) _ C.output
    exact append_below rfl (fun _ h => h) (by simp)

  have op_cases {g : Gate} (h : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
      g.op = GateOp.and ∨ g.op = GateOp.or :=
    (Set.mem_insert_iff.mp h).imp id Set.mem_singleton_iff.mp

  -- A forward read is false at evaluation time.
  let normalizeGate (cap : ℕ) (g : Gate) : Gate :=
    if g.op.eval [] = true ∧ ¬ (∀ i ∈ g.inputs, i < cap) then ⟨GateOp.or, []⟩
    else ⟨g.op, g.inputs.filter fun i => decide (i < cap)⟩

  have normalize_props (cap : ℕ) (g : Gate)
      (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
      ((normalizeGate cap g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
        (normalizeGate cap g).inputs.length ≤ 2) ∧
      ∀ i ∈ (normalizeGate cap g).inputs, i < cap := by
    dsimp only [normalizeGate]
    split_ifs
    · exact ⟨⟨Set.mem_insert_of_mem _ (Set.mem_singleton _), by decide⟩, by simp⟩
    · refine ⟨⟨hg.1, (List.length_filter_le _ _).trans hg.2⟩, ?_⟩
      intro i hi
      exact of_decide_eq_true (List.mem_filter.mp hi).2

  have normalize_step (w : List Bool) (g : Gate)
      (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
      step w (normalizeGate w.length g) = step w g := by
    rcases op_cases hop with ha | ho
    · by_cases hb : ∀ i ∈ g.inputs, i < w.length
      · have he : g.inputs.filter (fun i => decide (i < w.length)) = g.inputs :=
          List.filter_eq_self.mpr fun i hi => decide_eq_true (hb i hi)
        have hn : normalizeGate w.length g = g := by
          dsimp only [normalizeGate]
          rw [ite_eq_right (fun h => h.2 hb), he]
        rw [hn]
      · have hf : (g.inputs.map fun i => w.getD i false).all id = false := by
          apply List.all_eq_false.mpr
          obtain ⟨i, hi⟩ := not_forall.mp hb
          have hmem : i ∈ g.inputs := Classical.byContradiction fun h => hi fun h' => False.elim (h h')
          have hbad : w.length ≤ i := Nat.le_of_not_gt fun h => hi fun _ => h
          exact ⟨_, List.mem_map.mpr ⟨i, hmem, rfl⟩, by
            rw [List.getD_eq_default _ _ hbad]; simp⟩
        have hn : normalizeGate w.length g = ⟨GateOp.or, []⟩ := by
          dsimp only [normalizeGate]
          rw [ite_eq_left ⟨by rw [ha]; rfl, hb⟩]
        rw [hn]
        change w ++ [false] = w ++ [g.op.eval _]
        rw [ha]
        exact congrArg (fun b => w ++ [b]) hf.symm
    · have he : ∀ is : List ℕ,
          ((is.filter fun i => decide (i < w.length)).map fun i => w.getD i false).any id =
          (is.map fun i => w.getD i false).any id := by
        intro is
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_map]
        constructor
        · intro h
          obtain ⟨i, hi, hval⟩ := List.any_eq_true.mp h
          exact List.any_eq_true.mpr ⟨i, (List.mem_filter.mp hi).1, hval⟩
        · intro h
          obtain ⟨i, hi, hval⟩ := List.any_eq_true.mp h
          have hlt : i < w.length := by
            change w.getD i false = true at hval
            by_contra h
            rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)] at hval
            contradiction
          exact List.any_eq_true.mpr ⟨i, List.mem_filter.mpr ⟨hi, decide_eq_true hlt⟩, hval⟩
      have hn : normalizeGate w.length g = ⟨GateOp.or, g.inputs.filter fun i => decide (i < w.length)⟩ := by
        dsimp only [normalizeGate]
        have hf : g.op.eval [] = false := by rw [ho]; rfl
        rw [ite_eq_right (fun h => Bool.noConfusion (hf.symm.trans h.1))]
        rw [ho]
      rw [hn]
      change w ++ [_] = w ++ [g.op.eval _]
      rw [ho]
      exact congrArg (fun b => w ++ [b]) (he g.inputs)

  let normalizeList (gs : List Gate) (cap : ℕ) : List Gate :=
    (gs.zipIdx cap).map fun p => normalizeGate p.2 p.1

  have normalize_run (gs : List Gate) (w : List Bool)
      (hm : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
      (normalizeList gs w.length).foldl step w = gs.foldl step w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [normalizeList, List.zipIdx_cons, List.map_cons, List.foldl_cons]
      rw [normalize_step w g (hm g (by simp)), ← step_length]
      exact ih _ (fun g hg => hm g (List.mem_cons_of_mem _ hg))

  let normalize (C : Circuit) : Circuit := ⟨normalizeList C.gates 42, C.output⟩

  have normalize_len (C : Circuit) : (normalize C).gates.length = C.gates.length := by
    simp [normalize, normalizeList]

  have normalize_get (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
      (normalize C).gates[j]? = some (normalizeGate (42 + j) C.gates[j]) := by
    change ((C.gates.zipIdx 42).map _)[j]? = _
    simp only [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hj]
    rfl

  have normalize_monotone {C : Circuit} (hm : Monotone2 C) : Monotone2 (normalize C) := by
    intro g hg
    obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hg
    have hjC : j < C.gates.length := (normalize_len C) ▸ hj
    have he : some (normalizeGate (42 + j) C.gates[j]) = some g :=
      (normalize_get C hjC).symm.trans ((List.getElem?_eq_getElem hj).trans (congrArg some hget))
    rw [← Option.some.inj he]
    exact (normalize_props _ _ (hm _ (List.getElem_mem hjC))).1

  have normalize_back (C : Circuit) (hm : Monotone2 C) :
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 42 (normalize C) := by
    intro j hj
    have hjC : j < C.gates.length := (normalize_len C) ▸ hj
    change ∀ i ∈ ((normalize C).gates.getD j ⟨GateOp.or, []⟩).inputs, i < 42 + j
    simp only [List.getD_eq_getElem?_getD, normalize_get C hjC, Option.getD_some]
    exact (normalize_props _ _ (hm _ (List.getElem_mem hjC))).2

  have normalize_wires {C : Circuit} (hm : Monotone2 C) (x : Fin 42 → Bool) :
      (normalize C).wires (List.ofFn x) = C.wires (List.ofFn x) := by
    change (normalizeList C.gates 42).foldl step (List.ofFn x) = C.gates.foldl step (List.ofFn x)
    simpa only [List.length_ofFn] using normalize_run C.gates (List.ofFn x) (fun g hg => (hm g hg).1)

  have normalize_firing {C : Circuit} {k : ℕ} {g : Gate}
      (hg : C.gates[k]? = some g) (hop : g.op = GateOp.and) (x : Fin 42 → Bool)
      (hfire : (C.wires (List.ofFn x)).getD (42 + k) false = true) :
      (normalize C).gates[k]? = some g := by
    have hk : k < C.gates.length := by
      by_contra h
      rw [List.getElem?_eq_none (Nat.le_of_not_gt h)] at hg
      contradiction
    have he : C.gates[k] = g := Option.some.inj ((List.getElem?_eq_getElem hk).symm.trans hg)
    rw [gate_wire hk, he, hop] at hfire
    change (g.inputs.map fun i => (beforeGate C k x).getD i false).all id = true at hfire
    have hback : ∀ i ∈ g.inputs, i < 42 + k := by
      intro i hi
      have hread := List.all_eq_true.mp hfire _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
      by_contra h
      have hn : (beforeGate C k x).length ≤ i := by rw [prefix_length hk.le]; exact Nat.le_of_not_gt h
      rw [List.getD_eq_default _ _ hn] at hread
      contradiction
    rw [normalize_get C hk, he]
    have hfilter : g.inputs.filter (fun i => decide (i < 42 + k)) = g.inputs :=
      List.filter_eq_self.mpr fun i hi => decide_eq_true (hback i hi)
    dsimp only [normalizeGate]
    rw [ite_eq_right (fun h => h.2 hback), hfilter]

  let Incident (u v : Fin 42) : Prop :=
    u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)

  let HasEdge (x : Fin 42 → Bool) : Prop :=
    ∃ u v : Fin 42, Incident u v ∧ x u = true ∧ x v = true

  let Computes (C : Circuit) : Prop :=
    ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔ HasEdge x

  let Essential (C : Circuit) (k : ℕ) : Prop :=
    ∃ u v, Incident u v ∧ (eraseFalse C k).eval (List.ofFn (pairInput u v)) = false

  let Minimal (C : Circuit) : Prop := ∀ D : Circuit, Monotone2 D → D.size < C.size → ¬ Computes D

  have normalize_computes {C : Circuit} (hm : Monotone2 C) (hc : Computes C) :
      Computes (normalize C) := by
    intro x
    change ((normalize C).wires (List.ofFn x)).getD C.output false = true ↔ HasEdge x
    rw [normalize_wires hm x]
    exact hc x

  have essential_of_minimal {C : Circuit} (hm : Monotone2 C) (hc : Computes C)
      (hmin : Minimal C) {k : ℕ} (hk : k < C.gates.length) :
      Essential C k := by
    change ∃ u v, Incident u v ∧ (eraseFalse C k).eval (List.ofFn (pairInput u v)) = false
    by_contra h
    have heval (u v : Fin 42) (huv : Incident u v) :
        (eraseFalse C k).eval (List.ofFn (pairInput u v)) = true := by
      cases he : (eraseFalse C k).eval (List.ofFn (pairInput u v))
      · exact False.elim (h ⟨u, v, huv, he⟩)
      · rfl
    have hmono := erase_mono hm k (42 + C.gates.length)
    have hsize := erase_size hk (42 + C.gates.length)
    apply hmin (eraseFalse C k) hmono (Nat.lt_of_succ_le hsize.le)
    intro x
    constructor
    · exact fun hx => (hc x).mp (erase_below hm hk x hx)
    · rintro ⟨u, v, huv, hu, hv⟩
      apply eval_mono hmono (x := pairInput u v) _ (heval u v huv)
      intro i hi
      change decide (i = u ∨ i = v) = true at hi
      simp only [decide_eq_true_eq] at hi
      rcases hi with rfl | rfl
      · exact hu
      · exact hv

  -- Delete a constant true wire by simplifying every later read of it.
  let simplifyTrue (k : ℕ) (g : Gate) : Gate :=
    if g.op.eval [] = false ∧ 42 + k ∈ g.inputs then ⟨GateOp.and, []⟩
    else ⟨g.op, (g.inputs.filter fun i => decide (i ≠ 42 + k)).map (eraseRedirect 42 k 0)⟩

  have simplify_true_mono (k : ℕ) (g : Gate)
      (hm : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
      (simplifyTrue k g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
        (simplifyTrue k g).inputs.length ≤ 2 := by
    dsimp only [simplifyTrue]
    split_ifs
    · exact ⟨Set.mem_insert _ _, by decide⟩
    · exact ⟨hm.1, by rw [List.length_map]; exact (List.length_filter_le _ _).trans hm.2⟩

  have simplify_true_step (k : ℕ) (g : Gate) (v : List Bool)
      (hm : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
      (hp : 42 + k < v.length) (ht : v.getD (42 + k) false = true) :
      step (v.eraseIdx (42 + k)) (simplifyTrue k g) = (step v g).eraseIdx (42 + k) := by
    let kept := g.inputs.filter fun i => decide (i ≠ 42 + k)
    have keep_mem (i : ℕ) (hi : i ∈ kept) : i ∈ g.inputs ∧ i ≠ 42 + k := by
      exact ⟨(List.mem_filter.mp hi).1, of_decide_eq_true (List.mem_filter.mp hi).2⟩
    have reads :
        (kept.map (eraseRedirect 42 k 0)).map (fun i => (v.eraseIdx (42 + k)).getD i false) =
          kept.map (fun i => v.getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left fun i hi => rename_other v k 0 (keep_mem i hi).2
    simp only [step, List.eraseIdx_append_of_lt_length hp]
    rcases op_cases hm with ha | ho
    · have hn : simplifyTrue k g = ⟨GateOp.and, kept.map (eraseRedirect 42 k 0)⟩ := by
        dsimp only [simplifyTrue]
        have htrue : g.op.eval [] = true := by rw [ha]; rfl
        rw [ite_eq_right (fun h => Bool.noConfusion (htrue.symm.trans h.1))]
        exact congrArg (fun op => Gate.mk op _) ha
      rw [hn, ha]
      change v.eraseIdx (42 + k) ++ [(GateOp.and.eval _)] = _
      rw [reads]
      apply congrArg (fun b : Bool => v.eraseIdx (42 + k) ++ [b])
      change (kept.map fun i => v.getD i false).all id = (g.inputs.map fun i => v.getD i false).all id
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_map]
      constructor
      · intro h
        apply List.all_eq_true.mpr
        intro i hi
        by_cases he : i = 42 + k
        · change v.getD i false = true
          rw [he, ht]
        · exact List.all_eq_true.mp h i (List.mem_filter.mpr ⟨hi, decide_eq_true he⟩)
      · exact fun h => List.all_eq_true.mpr fun i hi => List.all_eq_true.mp h i (keep_mem i hi).1
    · by_cases hmem : 42 + k ∈ g.inputs
      · have hn : simplifyTrue k g = ⟨GateOp.and, []⟩ := by
          dsimp only [simplifyTrue]
          rw [ite_eq_left ⟨by rw [ho]; rfl, hmem⟩]
        rw [hn, ho]
        change v.eraseIdx (42 + k) ++ [true] =
          v.eraseIdx (42 + k) ++ [(g.inputs.map fun i => v.getD i false).any id]
        exact congrArg (fun b => v.eraseIdx (42 + k) ++ [b])
          (List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨_, hmem, ht⟩, rfl⟩).symm
      · have hn : simplifyTrue k g = ⟨GateOp.or, kept.map (eraseRedirect 42 k 0)⟩ := by
          dsimp only [simplifyTrue]
          rw [ite_eq_right (fun h => hmem h.2)]
          exact congrArg (fun op => Gate.mk op _) ho
        have hkept : kept = g.inputs :=
          List.filter_eq_self.mpr fun i hi => decide_eq_true (fun he => hmem (he ▸ hi))
        rw [hn, ho]
        change v.eraseIdx (42 + k) ++ [GateOp.or.eval _] = _
        rw [reads, hkept]

  have simplify_true_run (k : ℕ) (gs : List Gate) (v : List Bool)
      (hm : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
      (hp : 42 + k < v.length) (ht : v.getD (42 + k) false = true) :
      (gs.map (simplifyTrue k)).foldl step (v.eraseIdx (42 + k)) =
        (gs.foldl step v).eraseIdx (42 + k) := by
    induction gs generalizing v with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons]
      rw [simplify_true_step k g v (hm g (by simp)) hp ht]
      apply ih _ (fun g hg => hm g (List.mem_cons_of_mem _ hg))
      · rw [step_length]
        exact hp.trans (Nat.lt_succ_self _)
      · exact (List.getD_append _ _ _ _ hp).trans ht

  have no_true_gate {C : Circuit} (hm : Monotone2 C) (hc : Computes C) (hmin : Minimal C)
      {j : ℕ} (hj : j < C.gates.length)
      (htrue : ∀ x : Fin 42 → Bool, (C.wires (List.ofFn x)).getD (42 + j) false = true) : False := by
    have hout : C.output ≠ 42 + j := by
      intro he
      have hz : C.eval (List.ofFn fun _ : Fin 42 => false) = true := by
        change (C.wires _).getD C.output false = true
        rw [he]
        exact htrue _
      obtain ⟨u, v, _, hu, _⟩ := (hc _).mp hz
      contradiction
    let gs := C.gates.drop (j + 1)
    let D : Circuit := ⟨C.gates.take j ++ gs.map (simplifyTrue j), eraseRedirect 42 j 0 C.output⟩
    have hsize : D.size + 1 = C.size := by
      have hh := erase_size hj 0
      change (eraseGate C j 0).gates.length + 1 = C.gates.length at hh
      rw [erase_eq, ite_eq_left hj] at hh
      change (C.gates.take j ++ gs.map (simplifyTrue j)).length + 1 = C.gates.length
      simp only [List.length_append, List.length_map] at hh ⊢
      exact hh
    have hdm : Monotone2 D := by
      intro g hg
      rcases List.mem_append.mp hg with ht | ht
      · exact hm g (List.mem_of_mem_take ht)
      · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ht
        exact simplify_true_mono j f (hm f (List.mem_of_mem_drop hf))
    apply hmin D hdm (Nat.lt_of_succ_le hsize.le)
    intro x
    have he : D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
      let w := beforeGate C j x
      let v := step w C.gates[j]
      have hp : 42 + j < v.length := by rw [step_length, prefix_length hj.le]; exact Nat.lt_succ_self _
      have ht : v.getD (42 + j) false = true := by
        have hh := htrue x
        rw [wires_split hj x] at hh
        rw [run_preserves _ _ _ hp] at hh
        exact hh
      have hv : v.eraseIdx (42 + j) = w := by
        have hl : w.length = 42 + j := prefix_length hj.le x
        simp [v, step, ← hl, List.eraseIdx_append_of_length_le]
      change ((C.gates.take j ++ gs.map (simplifyTrue j)).foldl step (List.ofFn x)).getD
        (eraseRedirect 42 j 0 C.output) false = _
      rw [List.foldl_append]
      change ((gs.map (simplifyTrue j)).foldl step w).getD (eraseRedirect 42 j 0 C.output) false = _
      rw [← hv, simplify_true_run j gs v (fun g hg => (hm g (List.mem_of_mem_drop hg)).1) hp ht]
      exact (rename_other _ _ 0 hout).trans (eval_split hj x).symm
    rw [he]
    exact hc x

  have cannot_redirect {C : Circuit} (hm : Monotone2 C) (hc : Computes C) (hmin : Minimal C)
      {j dest : ℕ} (hj : j < C.gates.length)
      (hdest : dest < 42 + j ∨ 42 + C.gates.length ≤ dest)
      (he : ∀ x : Fin 42 → Bool,
        C.gates[j].op.eval (C.gates[j].inputs.map fun i => (beforeGate C j x).getD i false) =
          (beforeGate C j x).getD dest false) : False := by
    have hsize := erase_size hj dest
    apply hmin (eraseGate C j dest) (erase_mono hm j dest) (Nat.lt_of_succ_le hsize.le)
    intro x
    rw [erase_eval hj x hdest]
    have heval := eval_split hj x
    change C.eval (List.ofFn x) = ((C.gates.drop (j + 1)).foldl step
      (beforeGate C j x ++ [C.gates[j].op.eval
        (C.gates[j].inputs.map fun i => (beforeGate C j x).getD i false)])).getD C.output false at heval
    rw [he x] at heval
    rw [← heval]
    exact hc x

  have binary_distinct {C : Circuit} (hm : Monotone2 C) (hc : Computes C) (hmin : Minimal C)
      (hb : PEqualNP.MetaComplexity.NestedCover.ReadsBack 42 C) {j : ℕ}
      (hj : j < C.gates.length) :
      ∃ a b : ℕ, a ≠ b ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [a, b] := by
    have hget : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
      change C.gates.getD j _ = C.gates[j]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    rw [hget]
    have hback : ∀ i ∈ C.gates[j].inputs, i < 42 + j := by
      simpa only [hget] using hb j hj
    obtain ⟨hop, hlen⟩ := hm _ (List.getElem_mem hj)
    cases hi : C.gates[j].inputs with
    | nil =>
      exfalso
      rcases op_cases hop with ha | ho
      · apply no_true_gate hm hc hmin hj
        intro x
        rw [gate_wire hj x, ha, hi]
        rfl
      · apply cannot_redirect hm hc hmin hj (dest := 42 + C.gates.length) (Or.inr (Nat.le_refl _))
        intro x
        rw [ho, hi]
        exact (List.getD_eq_default _ _ (by
          rw [prefix_length hj.le]; exact Nat.add_le_add_left hj.le _)).symm
    | cons a tail =>
      have hlt := hback a (by rw [hi]; exact List.mem_cons_self)
      cases tail with
      | nil =>
        exfalso
        apply cannot_redirect hm hc hmin hj (Or.inl hlt)
        intro x
        rw [hi]
        rcases op_cases hop with ha | ho
        · rw [ha]
          change ([(beforeGate C j x).getD a false] : List Bool).all id = _
          exact Bool.and_true _
        · rw [ho]
          change ([(beforeGate C j x).getD a false] : List Bool).any id = _
          exact Bool.or_false _
      | cons b tail =>
        cases tail with
        | nil =>
          by_cases he : a = b
          · subst b
            exfalso
            apply cannot_redirect hm hc hmin hj (Or.inl hlt)
            intro x
            rw [hi]
            rcases op_cases hop with ha | ho
            · rw [ha]
              change ([(beforeGate C j x).getD a false,
                (beforeGate C j x).getD a false] : List Bool).all id = _
              simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_self]
            · rw [ho]
              change ([(beforeGate C j x).getD a false,
                (beforeGate C j x).getD a false] : List Bool).any id = _
              simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_self]
          · exact ⟨a, b, he, rfl⟩
        | cons c tail =>
          rw [hi] at hlen
          exact False.elim (Nat.not_succ_le_zero _ (Nat.le_of_succ_le_succ
            (Nat.le_of_succ_le_succ hlen)))

  have prefix_read {C : Circuit} {j i : ℕ} (hj : j ≤ C.gates.length)
      (hi : i < 42 + j) (x : Fin 42 → Bool) :
      (C.wires (List.ofFn x)).getD i false = (beforeGate C j x).getD i false := by
    change (C.gates.foldl step (List.ofFn x)).getD i false = _
    conv_lhs => rw [← List.take_append_drop j C.gates, List.foldl_append]
    exact run_preserves _ _ _ (by rw [prefix_length hj]; exact hi)

  have output_last {C : Circuit} (hs : C.size = 124) (hc : Computes C)
      (he : ∀ j < C.gates.length, Essential C j) : C.output = 165 := by
    have hl : C.gates.length = 124 := hs
    have hj : 123 < C.gates.length := hl.symm ▸ (by decide : 123 < 124)
    by_contra h
    obtain ⟨u, v, huv, herase⟩ := he 123 hj
    let x := pairInput u v
    have htrue : C.eval (List.ofFn x) = true :=
      (hc x).mpr ⟨u, v, huv, decide_eq_true (Or.inl rfl), decide_eq_true (Or.inr rfl)⟩
    have hdrop : C.gates.drop (123 + 1) = [] :=
      List.drop_eq_nil_of_le (Nat.le_of_eq hl)
    have sameRead (b : Bool) :
        (beforeGate C 123 x ++ [b]).getD C.output false =
          (beforeGate C 123 x).getD C.output false := by
      by_cases hlt : C.output < 165
      · exact List.getD_append _ _ _ _ (by rw [prefix_length hj.le]; exact hlt)
      · have hle : 166 ≤ C.output := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm h)
        rw [List.getD_eq_default _ _ (by
              simp only [List.length_append, List.length_singleton, prefix_length hj.le]; exact hle),
          List.getD_eq_default _ _ (by rw [prefix_length hj.le]; exact (Nat.le_succ _).trans hle)]
    have heval : (eraseFalse C 123).eval (List.ofFn x) = C.eval (List.ofFn x) := by
      change (eraseGate C 123 (42 + C.gates.length)).eval (List.ofFn x) = _
      rw [erase_eval hj x (Or.inr (Nat.le_refl _)), eval_split hj x, hdrop]
      exact (sameRead _).trans (sameRead _).symm
    exact Bool.noConfusion ((herase.symm.trans heval).trans htrue)

  let marked (i : Fin 42) : Bool :=
    decide (i.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ))

  let singleton (u : Fin 42) (i : Fin 42) : Bool := decide (i = u)

  let Hit (C : Circuit) (j : ℕ) : Prop :=
    ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and ∧
      (C.wires (List.ofFn marked)).getD (42 + j) false = true

  have marked_pair {C : Circuit} (hm : Monotone2 C)
      (hback : PEqualNP.MetaComplexity.NestedCover.ReadsBack 42 C)
      (hbinary : ∀ j < C.gates.length, ∃ a b : ℕ, a ≠ b ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [a, b])
      (h : ∃ j, Hit C j) :
      ∃ (k : ℕ) (g : Gate) (u v : Fin 42) (a b : ℕ),
        C.gates[k]? = some g ∧ g.op = GateOp.and ∧ g.inputs = [a, b] ∧
        marked u = true ∧ marked v = true ∧
        (C.wires (List.ofFn (singleton u))).getD a false = true ∧
        (C.wires (List.ofFn (singleton v))).getD b false = true ∧
        (C.wires (List.ofFn (pairInput u v))).getD (42 + k) false = true ∧
        ∀ j < k, ¬ Hit C j := by
    classical
    let k := Nat.find h
    obtain ⟨g, hg, hop, hfire⟩ := Nat.find_spec h
    have hk : k < C.gates.length := by
      by_contra h
      rw [List.getElem?_eq_none (Nat.le_of_not_gt h)] at hg
      contradiction
    have hbefore : ∀ j < k, ¬ Hit C j := fun _ hj => Nat.find_min h hj
    have gateAt_get (j : ℕ) (hj : j < C.gates.length) :
        PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
      change C.gates.getD j _ = C.gates[j]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    have hor (j : ℕ) (hj : j < k)
        (ht : (C.wires (List.ofFn marked)).getD (42 + j) false = true) :
        (C.gates[j]'(hj.trans hk)).op = GateOp.or := by
      have hj' := hj.trans hk
      rcases op_cases (hm _ (List.getElem_mem hj')).1 with ha | ho
      · exact (hbefore j hj ⟨_, List.getElem?_eq_getElem hj', ha, ht⟩).elim
      · exact ho
    have trace (i : ℕ) (hi : i < 42 + k)
        (ht : (C.wires (List.ofFn marked)).getD i false = true) :
        ∃ u : Fin 42, marked u = true ∧
          (C.wires (List.ofFn (singleton u))).getD i false = true := by
      induction i using Nat.strong_induction_on with
      | ind i ih =>
        by_cases hin : i < 42
        · let u : Fin 42 := ⟨i, hin⟩
          change (C.gates.foldl step (List.ofFn marked)).getD i false = true at ht
          rw [run_preserves _ _ _ (by simpa only [List.length_ofFn] using hin)] at ht
          refine ⟨u, ?_, ?_⟩
          · simpa only [u, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hin,
              Option.getD_some] using ht
          · change (C.gates.foldl step (List.ofFn (singleton u))).getD i false = true
            rw [run_preserves _ _ _ (by simpa only [List.length_ofFn] using hin)]
            simp only [u, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hin,
              Option.getD_some, singleton, decide_eq_true_eq]
        · let j := i - 42
          have he : 42 + j = i := Nat.add_sub_of_le (Nat.le_of_not_gt hin)
          have hj : j < k := Nat.lt_of_add_lt_add_left (he.symm ▸ hi)
          have hj' := hj.trans hk
          rw [← he] at ht ⊢
          have ho := hor j hj ht
          rw [gate_wire hj', ho] at ht
          change (C.gates[j].inputs.map fun p => (beforeGate C j marked).getD p false).any id = true at ht
          obtain ⟨b, hmem, hbit⟩ := List.any_eq_true.mp ht
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hmem
          have hpl := hback j hj' p (by simpa only [gateAt_get j hj'] using hp)
          have hmark : (C.wires (List.ofFn marked)).getD p false = true :=
            (prefix_read hj'.le hpl marked).trans hbit
          obtain ⟨u, hu, huval⟩ := ih p (he ▸ hpl) (hpl.trans (Nat.add_lt_add_left hj 42)) hmark
          refine ⟨u, hu, ?_⟩
          rw [gate_wire hj', ho]
          change (C.gates[j].inputs.map fun p =>
            (beforeGate C j (singleton u)).getD p false).any id = true
          have hsingle := (prefix_read hj'.le hpl (singleton u)).symm.trans huval
          exact List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨p, hp, hsingle⟩, rfl⟩
    have hg' : C.gates[k] = g := Option.some.inj ((List.getElem?_eq_getElem hk).symm.trans hg)
    obtain ⟨a, b, _, hab⟩ := hbinary k hk
    rw [gateAt_get k hk, hg'] at hab
    have ah : a < 42 + k := hback k hk a (by rw [gateAt_get k hk, hg', hab]; simp)
    have bh : b < 42 + k := hback k hk b (by rw [gateAt_get k hk, hg', hab]; simp)
    have hreads : ((beforeGate C k marked).getD a false = true) ∧
        ((beforeGate C k marked).getD b false = true) := by
      rw [gate_wire hk, hg', hop, hab] at hfire
      change ([(beforeGate C k marked).getD a false,
        (beforeGate C k marked).getD b false] : List Bool).all id = true at hfire
      simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true] at hfire
      exact Bool.and_eq_true_iff.mp hfire
    obtain ⟨u, hu, huval⟩ := trace a ah ((prefix_read hk.le ah marked).trans hreads.1)
    obtain ⟨v, hv, hvval⟩ := trace b bh ((prefix_read hk.le bh marked).trans hreads.2)
    refine ⟨k, g, u, v, a, b, hg, hop, hab, hu, hv, huval, hvval, ?_, hbefore⟩
    have liftU : ∀ i, singleton u i = true → pairInput u v i = true := by
      intro i hi
      exact decide_eq_true (Or.inl (of_decide_eq_true hi))
    have liftV : ∀ i, singleton v i = true → pairInput u v i = true := by
      intro i hi
      exact decide_eq_true (Or.inr (of_decide_eq_true hi))
    have ha := (prefix_read hk.le ah (pairInput u v)).symm.trans (wires_mono hm liftU a huval)
    have hb := (prefix_read hk.le bh (pairInput u v)).symm.trans (wires_mono hm liftV b hvval)
    rw [gate_wire hk, hg', hop, hab]
    change ([(beforeGate C k (pairInput u v)).getD a false,
      (beforeGate C k (pairInput u v)).getD b false] : List Bool).all id = true
    rw [ha, hb]
    rfl

  have small_bound (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 123) : ¬ Computes C := by
    intro hc
    classical
    let Fits (s : ℕ) : Prop := ∃ E : Circuit, Monotone2 E ∧ E.size = s ∧ Computes E
    have hex : ∃ s, Fits s := ⟨C.size, C, hm, rfl, hc⟩
    obtain ⟨E, hem, hes, hec⟩ := Nat.find_spec hex
    let T := normalize E
    have htlen : T.size = Nat.find hex := (normalize_len E).trans hes
    have hts : T.size ≤ 123 := htlen.trans_le ((Nat.find_min' hex ⟨C, hm, rfl, hc⟩).trans hs)
    have htm := normalize_monotone hem
    have htc := normalize_computes hem hec
    have htb := normalize_back E hem
    have htmin : Minimal T := by
      intro F hfm hfs hfc
      exact Nat.find_min hex (htlen ▸ hfs) ⟨F, hfm, rfl, hfc⟩
    exact small T htm hts htb (fun _ hj => binary_distinct htm htc htmin htb hj)
      (fun _ hj => essential_of_minimal htm htc htmin hj) htc

  rintro C hm hs ⟨k, g, hg, hop, hfire⟩
  by_contra h
  have hc : Computes C := fun x => Classical.byContradiction fun hx => h ⟨x, hx⟩
  have hsize : C.size = 124 := by
    by_contra hne
    exact small_bound C hm (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hs hne)) hc
  let D := normalize C
  have hdsize : D.size = 124 := (normalize_len C).trans hsize
  have hdm := normalize_monotone hm
  have hdc : Computes D := normalize_computes hm hc
  have hdmin : Minimal D := fun E hem hlt =>
    small_bound E hem (Nat.le_of_lt_succ (show E.size < 124 from hdsize ▸ hlt))
  have hdg := normalize_firing hg hop _ hfire
  have hdf : (D.wires _).getD (42 + k) false = true :=
    (congrArg (fun w : List Bool => w.getD (42 + k) false) (normalize_wires hm _)).trans hfire
  have hback := normalize_back C hm
  have hbinary := fun j hj => binary_distinct hdm hdc hdmin hback (j := j) hj
  have hhit : ∃ j, Hit D j := ⟨k, g, hdg, hop, hdf⟩
  have hessential : ∀ j < D.gates.length, Essential D j :=
    fun _ hj => essential_of_minimal hdm hdc hdmin hj
  exact essentialCase D hdm hdsize (output_last hdsize hdc hessential) hback hbinary hdc
    (marked_pair hdm hback hbinary hhit) hessential
