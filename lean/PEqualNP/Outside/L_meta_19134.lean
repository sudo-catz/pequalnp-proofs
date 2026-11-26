import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19134

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, List.foldl_append]

lemma run_ext (gs : List Gate) (w : List Bool) :
    ∃ t : List Bool, run gs w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [run], rfl⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    change run gs (w ++ [v]) = w ++ v :: t
    simp [ht]

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_ext gs w
  rw [ht, List.length_append, hl]

lemma run_input (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := run_ext gs w
  rw [ht, List.getD_append _ _ _ _ hi]

lemma prefix_read (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (run (gs.take k) w).getD i false =
      if i < w.length + k then (run gs w).getD i false else false := by
  have hlen : (run (gs.take k) w).length = w.length + k := by
    rw [run_length, List.length_take, min_eq_left hk]
  split_ifs with hi
  · conv_rhs => rw [← List.take_append_drop k gs, run_append]
    exact (run_input _ _ _ (by omega)).symm
  · exact List.getD_eq_default _ _ (by omega)

lemma run_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (run gs w).getD (w.length + k) false =
      gs[k].op.eval (gs[k].inputs.map fun i =>
        if i < w.length + k then (run gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h
    exact h
  have hlen : (run (gs.take k) w).length = w.length + k := by
    rw [run_length, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : run gs w =
      run (gs.drop (k + 1)) (run (gs.take k) w ++
        [gs[k].op.eval (gs[k].inputs.map fun i => (run (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, run_append]
    rfl
  calc
    (run gs w).getD (w.length + k) false =
        gs[k].op.eval (gs[k].inputs.map fun i => (run (gs.take k) w).getD i false) := by
      rw [heq, run_input]
      · simp [← hlen]
      · simp [hlen]
    _ = _ := by
      congr 1
      apply List.map_congr_left
      intro i _
      exact prefix_read gs w k i (Nat.le_of_lt hk)

abbrev Input := Fin 12 → Bool

def wire (C : Circuit) (y : Input) (i : ℕ) : Bool :=
  (C.wires (List.ofFn y)).getD i false

def read (C : Circuit) (y : Input) (k i : ℕ) : Bool :=
  if i < 12 + k then wire C y i else false

lemma wire_input (C : Circuit) (y : Input) (i : Fin 12) : wire C y i.val = y i := by
  change (run C.gates (List.ofFn y)).getD i.val false = y i
  rw [run_input, List.getD_eq_getElem, List.getElem_ofFn]
  all_goals simp

lemma wire_outside (C : Circuit) (y : Input) {i : ℕ} (hi : 12 + C.gates.length ≤ i) :
    wire C y i = false := by
  change (run C.gates (List.ofFn y)).getD i false = false
  exact List.getD_eq_default _ _ (by simpa [run_length] using hi)

lemma gate_sem (C : Circuit) (y : Input) {k : ℕ} (hk : k < C.gates.length) :
    wire C y (12 + k) = C.gates[k].op.eval (C.gates[k].inputs.map (read C y k)) := by
  change (run C.gates (List.ofFn y)).getD (12 + k) false = _
  have h := run_gate C.gates (List.ofFn y) k hk
  rw [List.length_ofFn] at h
  exact h

lemma gate_ops {C : Circuit} (hc : Monotone2 C) {k : ℕ} (hk : k < C.gates.length) :
    (C.gates[k].op = .and ∨ C.gates[k].op = .or) ∧ C.gates[k].inputs.length ≤ 2 := by
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
    hc _ (List.getElem_mem hk)

lemma mono {C : Circuit} (hc : Monotone2 C) (y z : Input) (hyz : ∀ i, y i = true → z i = true) :
    ∀ w, wire C y w = true → wire C z w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hin : w < 12
    · have h1 := wire_input C y ⟨w, hin⟩
      have h2 := wire_input C z ⟨w, hin⟩
      simp only at h1 h2
      rw [h2]
      exact hyz _ (h1 ▸ hw)
    · by_cases hout : 12 + C.gates.length ≤ w
      · rw [wire_outside C y hout] at hw
        exact absurd hw (by simp)
      · obtain ⟨k, rfl⟩ : ∃ k, w = 12 + k := ⟨w - 12, by omega⟩
        have hk : k < C.gates.length := by omega
        have hrd : ∀ i, read C y k i = true → read C z k i = true := by
          intro i hi
          unfold read at hi ⊢
          split_ifs at hi ⊢ with hlt
          · exact ih i hlt hi
        rw [gate_sem C y hk] at hw
        rw [gate_sem C z hk]
        rcases (gate_ops hc hk).1 with ho | ho
        · rw [ho] at hw ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at hw ⊢
          rintro _ ⟨i, hi, rfl⟩
          exact hrd i (hw _ ⟨i, hi, rfl⟩)
        · rw [ho] at hw ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hw ⊢
          obtain ⟨_, ⟨i, hi, rfl⟩, hv⟩ := hw
          exact ⟨_, ⟨i, hi, rfl⟩, hrd i hv⟩

def pt (u v : Fin 6) : Input := fun i => decide (i.val = u.val ∨ i.val = 6 + v.val)

lemma oneEach_pt : ∀ u v : Fin 6, oneEach u v = List.ofFn (pt u v) := by decide

def lo (t : ℕ) : Input := fun i => decide (i.val = (if t < 6 then 6 else 0))

def hi (t : ℕ) : Input := fun i => decide (i.val = (if t < 6 then 6 else 0) ∨ i.val = t)

def T : Finset ℕ := {1, 2, 3, 4, 5, 7, 8, 9, 10, 11}

lemma T_card : T.card = 10 := by decide

lemma T_lt : ∀ t ∈ T, t < 12 := by decide

lemma T_spec : ∀ t ∈ T, (∃ u v : Fin 6, hi t = pt u v ∧ (u ≠ 0 ∨ v ≠ 0)) ∧
    ∀ i, lo t i = true → pt 0 0 i = true := by decide

def sens (C : Circuit) (t w : ℕ) : Prop := wire C (lo t) w ≠ wire C (hi t) w

lemma sens_input (C : Circuit) {t w : ℕ} (hw : w < 12) (h : sens C t w) : w = t := by
  by_contra hne
  apply h
  rw [wire_input C (lo t) ⟨w, hw⟩, wire_input C (hi t) ⟨w, hw⟩]
  simp only [lo, hi]
  by_cases hc : w = (if t < 6 then 6 else 0) <;> simp [hc, hne]

lemma sens_gate (C : Circuit) {t k : ℕ} (hk : k < C.gates.length) (h : sens C t (12 + k)) :
    ∃ i ∈ C.gates[k].inputs, i < 12 + k ∧ sens C t i := by
  by_contra hno
  push Not at hno
  apply h
  rw [gate_sem C (lo t) hk, gate_sem C (hi t) hk]
  congr 1
  apply List.map_congr_left
  intro i hi'
  unfold read
  split_ifs with hlt
  · by_contra hne
    exact hno i hi' hlt hne
  · rfl

lemma cover {C : Circuit} (hc : Monotone2 C) :
    ∀ k ≤ C.gates.length, ∀ L : List ℕ, (∀ w ∈ L, w < 12 + k) →
      (∀ t ∈ T, ∃ w ∈ L, sens C t w) → T.card ≤ L.length + k := by
  intro k
  induction k with
  | zero =>
    intro _ L hL hcov
    have hsub : T ⊆ L.toFinset := by
      intro t ht
      obtain ⟨w, hw, hs⟩ := hcov t ht
      have := sens_input C (by simpa using hL w hw) hs
      exact List.mem_toFinset.mpr (this ▸ hw)
    have := Finset.card_le_card hsub
    have := List.toFinset_card_le L
    omega
  | succ k ih =>
    intro hk L hL hcov
    have hk' : k < C.gates.length := by omega
    by_cases hmem : 12 + k ∈ L
    · let L' := L.filter (fun w => decide (w ≠ 12 + k)) ++
        (C.gates[k].inputs.filter (fun i => decide (i < 12 + k)))
      have hL' : ∀ w ∈ L', w < 12 + k := by
        intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · obtain ⟨hw, hne⟩ := List.mem_filter.mp hw
          have := hL w hw
          simp only [decide_eq_true_eq] at hne
          omega
        · simpa using (List.mem_filter.mp hw).2
      have hcov' : ∀ t ∈ T, ∃ w ∈ L', sens C t w := by
        intro t ht
        obtain ⟨w, hw, hs⟩ := hcov t ht
        by_cases he : w = 12 + k
        · subst he
          obtain ⟨i, hi, hlt, hs'⟩ := sens_gate C hk' hs
          exact ⟨i, List.mem_append_right _ (List.mem_filter.mpr ⟨hi, by simpa using hlt⟩), hs'⟩
        · exact ⟨w, List.mem_append_left _ (List.mem_filter.mpr ⟨hw, by simpa using he⟩), hs⟩
      have h1 : (L.filter (fun w => decide (w ≠ 12 + k))).length < L.length :=
        List.length_filter_lt_length_iff_exists.mpr ⟨12 + k, hmem, by simp⟩
      have h2 : (C.gates[k].inputs.filter (fun i => decide (i < 12 + k))).length ≤ 2 :=
        (List.length_filter_le _ _).trans (gate_ops hc hk').2
      have := ih (by omega) L' hL' hcov'
      have hlen : L'.length = (L.filter (fun w => decide (w ≠ 12 + k))).length +
          (C.gates[k].inputs.filter (fun i => decide (i < 12 + k))).length := List.length_append
      omega
    · have hL' : ∀ w ∈ L, w < 12 + k := by
        intro w hw
        have := hL w hw
        have hne : w ≠ 12 + k := fun he => hmem (he ▸ hw)
        omega
      have := ih (by omega) L hL' hcov
      omega

end PEqualNP.Outside.L_meta_19134

open PEqualNP.Outside.L_meta_19134 in
theorem PEqualNP.Outside.L_meta_19134 : (¬ (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => !(decide (u = 0) && decide (v = 0))) 8)) := by
  rintro ⟨C, hc, hsize, hrep⟩
  have heval : ∀ u v : Fin 6, wire C (pt u v) C.output = !(decide (u = 0) && decide (v = 0)) := by
    intro u v
    have := hrep u v
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval at this
    rw [oneEach_pt] at this
    exact this
  have hout : C.output < 12 + C.gates.length := by
    by_contra hge
    have := heval 1 0
    rw [wire_outside C _ (by omega)] at this
    exact absurd this (by decide)
  have hsens : ∀ t ∈ T, sens C t C.output := by
    intro t ht
    obtain ⟨⟨u, v, hhi, huv⟩, hlo⟩ := T_spec t ht
    have htrue : wire C (hi t) C.output = true := by
      rw [hhi, heval u v]
      rcases huv with h | h <;> simp [h]
    have hfalse : wire C (lo t) C.output = false := by
      by_contra hne
      have := mono hc (lo t) (pt 0 0) hlo C.output (by simpa using hne)
      rw [heval 0 0] at this
      exact absurd this (by decide)
    unfold sens
    rw [htrue, hfalse]
    decide
  have := cover hc C.gates.length le_rfl [C.output] (by simpa using hout)
    (fun t ht => ⟨C.output, List.mem_singleton_self _, hsens t ht⟩)
  rw [T_card] at this
  have hs : C.gates.length ≤ 8 := hsize
  simp at this
  omega
