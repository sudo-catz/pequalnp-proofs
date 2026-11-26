import PEqualNP.Defs

-- The argument for deleting an operand with a single reader follows R_meta_6766_565.
-- The recurrence for paths through OR gates follows L_meta_3805.

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadTwo
open PEqualNP.CleanedNonEdge

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 50000 in
theorem PEqualNP.Outside.R_meta_6766_1
    (boundary : let G := edgeGraph 11 (([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List ℕ).map
        fun e => (e / 11, e % 11))
      ∀ (v : Fin 11) (C : Circuit), v.val < 4 → IsAO2 11 C → C.size = 18 →
        (∀ a b : Fin 11, G.Adj a b → a ≠ v → b ≠ v →
          circuitFun 11 C (pairInput a b) = true) →
        (∀ x : Fin 11 → Bool, x v = false → graphFun G ∅ x = false →
          (∀ y : Fin 11 → Bool, x < y → y v = false → graphFun G ∅ y = true) →
          circuitFun 11 C x = false) → False)
    (shared : let G := edgeGraph 11 (([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List ℕ).map
        fun e => (e / 11, e % 11))
      ∀ C : Circuit, IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card → C.size ≤ 21 →
        2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card < 2 * (Ustar G C).card →
        ∀ (v : Fin 11) (g r : ℕ), v.val < 4 → g < r → r < C.size →
          (gateAt C g).op = .and → (gateAt C r).op = .or →
          readers 0 C v.val = {g} → readers 11 C g = {r} →
          (∀ j, 11 + j ∈ (gateAt C g).inputs →
            ∃ k < C.size, k ≠ g ∧ 11 + j ∈ (gateAt C k).inputs ∧
              (BelowF G C k → (gateAt C k).op = .and → ∀ w ∈ (gateAt C k).inputs, 11 ≤ w)) →
          G.neighborFinset v ⊆ wmax G C r → orIn 11 C (11 + r) = ∅ →
          ∃ (u : Fin 11) (E : Circuit), u.val < 4 ∧ IsAO2 11 E ∧ E.size ≤ 18 ∧
            ∀ x : Fin 11 → Bool, x u = false → circuitFun 11 E x = graphFun G ∅ x) :
    let G : SimpleGraph (Fin 11) := edgeGraph 11
      [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
       (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
    ∀ C : Circuit, IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card → C.size ≤ 21 →
      2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card < 2 * (Ustar G C).card →
      ∀ (v : Fin 11) (g r : ℕ), v.val < 4 → g < r → r < C.size →
        (gateAt C g).op = .and → (gateAt C r).op = .or →
        (∀ k < C.size, v.val ∈ (gateAt C k).inputs ↔ k = g) →
        (∀ k < C.size, 11 + g ∈ (gateAt C k).inputs ↔ k = r) →
        ∃ u : Fin 11, u.val < 4 ∧
          (have redundant : ℕ → Prop := fun j => ∃ w < 11 + j, ∀ x : Fin 11 → Bool,
             x u = false → wval C x (11 + j) = wval C x w
           ∃ i j k : ℕ, i < j ∧ j < k ∧ k < C.size ∧ redundant i ∧ redundant j ∧ redundant k) := by
  classical
  intro x1 D hm ht hj hsz hnum v g r hv hgr hr hgop hrop hvin hgin
  exfalso
  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq_foldl (C : Circuit) (x : List Bool) :
      C.wires x = C.gates.foldl stepWire x := rfl

  have foldl_length (gs : List Gate) (w : List Bool) :
      (gs.foldl stepWire w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [stepWire]
      omega

  have foldl_getD_lt2 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

  have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp [stepWire]
        rw [Nat.add_zero, foldl_getD_lt2 gs (stepWire w g) w.length h1]
        simp only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp [stepWire, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
          simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact key

  let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

  have eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

  have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    change C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]
    simp [List.getD_eq_getElem?_getD, hj]

  have gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj

  have val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
      val C x u = x.getD u false := by
    unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)

  have val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
      (hu : n + C.gates.length ≤ u) : val C x u = false := by
    unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

  have val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
      (hj : j < C.gates.length) :
      val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < n + j then val C x i else false) := by
    subst hx
    rw [gateAt_eq hj]
    exact foldl_getD_gate C.gates x j hj

  have agreeOutside {n : ℕ} (C : Circuit) (x y : Fin n → Bool) (excluded : ℕ → Prop)
      (raw : ∀ i : Fin n, ¬excluded i.val → x i = y i)
      (gate : ∀ j < C.gates.length, ¬excluded (n+j) →
        wval C x (n+j) = wval C y (n+j) ∨
         ∀ i ∈ (gateAt C j).inputs, i < n+j → ¬excluded i) :
      ∀ w, ¬excluded w → wval C x w = wval C y w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro how
      change val C (List.ofFn x) w = val C (List.ofFn y) w
      by_cases hw : w < n
      · rw [val_input List.length_ofFn hw, val_input List.length_ofFn hw]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hw, Option.getD_some]
        exact raw ⟨w,hw⟩ how
      · by_cases hl : n + C.gates.length ≤ w
        · rw [val_ge List.length_ofFn hl, val_ge List.length_ofFn hl]
        · obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
          have hj : j < C.gates.length := by omega
          rcases gate j hj how with same | src
          · exact same
          · rw [val_gate List.length_ofFn hj,val_gate List.length_ofFn hj]
            congr 1
            apply List.map_congr_left
            intro i hi
            by_cases bound : i < n+j
            · rw [ite_eq_left bound,ite_eq_left bound]
              exact ih i bound (src i hi bound)
            · rw [ite_eq_right bound,ite_eq_right bound]
  
  have beforeReader {n : ℕ} (C : Circuit) (x y : Fin n → Bool) (v g : ℕ)
      (raw : ∀ i : Fin n, i.val ≠ v → x i = y i)
      (only : ∀ j < C.gates.length, v ∈ (gateAt C j).inputs → j = g)
      (w : ℕ) (hv : w ≠ v) (before : w < n+g) : wval C x w = wval C y w := by
    refine agreeOutside C x y (fun i => i = v ∨ n+g ≤ i) ?_ ?_ w ?_
    · intro i h
      exact raw i (fun q => h (Or.inl q))
    · intro j hj ho
      right
      intro i hi smaller equ
      rcases equ with rfl | upper
      · have e := only j hj hi
        exact ho (Or.inr (by omega))
      · have limit : n+j < n+g := Nat.lt_of_not_ge (fun q => ho (Or.inr q))
        omega
    · rintro (e | after)
      · exact hv e
      · omega
  
  have readOnceEffect {n : ℕ} (C : Circuit) (x y : Fin n → Bool) (v g : ℕ)
      (raw : ∀ i : Fin n, i.val ≠ v → x i = y i)
      (only : ∀ j < C.gates.length, v ∈ (gateAt C j).inputs → j = g)
      (out_ne : C.output ≠ v) (out_diff : C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
      wval C x (n+g) ≠ wval C y (n+g) := by
    intro hg
    apply out_diff
    apply agreeOutside C x y (fun i => i = v) raw ?_ C.output out_ne
    intro j hj _
    by_cases eq : j = g
    · subst j
      exact Or.inl hg
    · right
      intro i hi _ e
      subst i
      exact eq (only j hj hi)
  
  let OpMono (R : Bool → Bool → Prop) : Prop :=
    ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
      (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

  have opMono_eq : OpMono Eq := by
    intro op _ l f g h
    rw [List.map_congr_left h]

  have val_prefix {n : ℕ} {C D : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
      (hmC : m ≤ C.gates.length) (hmD : m ≤ D.gates.length)
      (hg : ∀ k < m, gateAt D k = gateAt C k) : ∀ u, u < n + m → val D x u = val C x u := by
    intro u
    induction u using Nat.strong_induction_on with
    | _ u ih =>
      intro hu
      by_cases hun : u < n
      · rw [val_input hx hun, val_input hx hun]
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
        have hk : k < m := by omega
        rw [val_gate hx (by omega), val_gate hx (by omega), hg k hk]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < n + k
        · rw [ite_eq_left hi, ite_eq_left hi]; exact ih i hi (by omega)
        · rw [ite_eq_right hi, ite_eq_right hi]

  let aliasWire (w i u : ℕ) : ℕ := if u = w then i else if w < u then u - 1 else u

  let aliasGate (w i : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire w i)⟩

  let bypass (n : ℕ) (C : Circuit) (r i : ℕ) : Circuit :=
    ⟨(List.range (C.gates.length - 1)).map (fun k =>
        if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1))),
      aliasWire (n + r) i C.output⟩

  have bypass_length (n : ℕ) (C : Circuit) (r i : ℕ) :
      (bypass n C r i).gates.length = C.gates.length - 1 := by simp [bypass]

  have bypass_output (n : ℕ) (C : Circuit) (r i : ℕ) :
      (bypass n C r i).output = aliasWire (n + r) i C.output := rfl

  have gateAt_bypass {n : ℕ} {C : Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
      gateAt (bypass n C r i) k =
        if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1)) := by
    have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
    rw [gateAt_eq hk']
    simp [bypass]

  have bypass_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
      (hr : r < C.gates.length) : ∀ u, u < n + r → val (bypass n C r i) x u = val C x u := by
    apply val_prefix hx (by omega) (by rw [bypass_length]; omega)
    intro k hk
    rw [gateAt_bypass (by omega), ite_eq_left hk]

  have aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp [aliasWire]

  have aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
    unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_right (by omega)]

  have aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
    unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_left hu]

  have bypass_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
      {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
      (hR : (∃ k, r < k ∧ k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs) →
        R (val C x (n + r)) (val C x i)) :
      ∀ u, u ≠ n + r → R (val C x u) (val (bypass n C r i) x (aliasWire (n + r) i u)) := by
    intro u
    induction u using Nat.strong_induction_on with
    | _ u ih =>
      intro hne
      by_cases hlt : u < n + r
      · rw [aliasWire_lt_self hlt, bypass_val_lt hx hr u hlt]; exact hrefl _
      · rw [aliasWire_gt_self (by omega)]
        by_cases hge : n + C.gates.length ≤ u
        · rw [val_ge hx hge, val_ge hx (by rw [bypass_length]; omega)]; exact hrefl _
        · obtain ⟨k, rfl⟩ : ∃ k, u = n + (k + 1) := ⟨u - n - 1, by omega⟩
          have hk1 : k + 1 < C.gates.length := by omega
          have hkr : ¬ k < r := by omega
          have e : n + (k + 1) - 1 = n + k := by omega
          rw [e, val_gate hx hk1, val_gate hx (by rw [bypass_length]; omega),
            gateAt_bypass (by omega), ite_eq_right hkr]
          simp only [aliasGate, List.map_map]
          refine hmono _ (hAO _ hk1) _ _ _ ?_
          intro i' hi'
          simp only [Function.comp_apply]
          by_cases h1 : i' = n + r
          · subst h1
            rw [aliasWire_self, ite_eq_left (by omega)]
            have hgi : (if i < n + k then val (bypass n C r i) x i else false) = val C x i := by
              rcases hi with hi | hi
              · rw [ite_eq_left (by omega), bypass_val_lt hx hr i hi]
              · rw [ite_eq_right (by omega), val_ge hx hi]
            rw [hgi]
            exact hR ⟨k + 1, by omega, hk1, hi'⟩
          · by_cases h2 : i' < n + r
            · rw [aliasWire_lt_self h2, ite_eq_left (by omega), ite_eq_left (by omega),
                bypass_val_lt hx hr i' h2]
              exact hrefl _
            · by_cases h3 : i' < n + (k + 1)
              · have key := ih i' h3 h1
                rw [aliasWire_gt_self (by omega)] at key
                rw [aliasWire_gt_self (by omega), ite_eq_left h3, ite_eq_left (by omega)]
                exact key
              · rw [aliasWire_gt_self (by omega), ite_eq_right h3, ite_eq_right (by omega)]
                exact hrefl _

  have bypass_eval_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
      {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
      (hR : R (val C x (n + r)) (val C x i)) :
      R (C.eval x) ((bypass n C r i).eval x) := by
    rw [eval_eq_val, eval_eq_val, bypass_output]
    by_cases h : C.output = n + r
    · have hgi : val (bypass n C r i) x i = val C x i := by
        rcases hi with hi | hi
        · exact bypass_val_lt hx hr i hi
        · rw [val_ge hx hi, val_ge hx (by rw [bypass_length]; omega)]
      rw [h, aliasWire_self, hgi]; exact hR
    · exact bypass_rel hrefl hmono hx hAO hr hi (fun _ => hR) _ h

  have bypass_eval_eq {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
      (hR : val C x (n + r) = val C x i) :
      (bypass n C r i).eval x = C.eval x :=
    (bypass_eval_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi hR).symm

  have bypass_ok {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r)
      (hR : ((∃ k, r < k ∧ k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs) ∨
        C.output = n + r) → val C x (n + r) = val C x i) :
      (bypass n C r i).eval x = C.eval x := by
    rw [eval_eq_val, eval_eq_val, bypass_output]
    by_cases h : C.output = n + r
    · rw [h, aliasWire_self, bypass_val_lt hx hr i hi]
      exact (hR (Or.inr h)).symm
    · exact (bypass_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr (Or.inl hi)
        (fun hk => hR (Or.inl hk)) _ h).symm

  have bypass_mem {n : ℕ} {C : Circuit} {r i : ℕ} :
      ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧
        g.inputs.length = g'.inputs.length := by
    intro g hg
    simp only [bypass, List.mem_map, List.mem_range] at hg
    obtain ⟨k, hk, rfl⟩ := hg
    split_ifs with h
    · exact ⟨gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
    · exact ⟨gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp [aliasGate]⟩

  have aliasWire_lt {w i u m : ℕ} (hi : i < w) (hwm : w ≤ m) (hu : u < m + 1) :
      aliasWire w i u < m := by
    unfold aliasWire; split_ifs <;> omega

  have bypass_readsBack {n : ℕ} {C : Circuit} {r i : ℕ} (hi : i < n + r)
      (hRB : ∀ k < C.gates.length, ∀ u ∈ (gateAt C k).inputs, u < n + k) :
      ∀ k < (bypass n C r i).gates.length,
        ∀ u ∈ (gateAt (bypass n C r i) k).inputs, u < n + k := by
    intro k hk u hu
    rw [bypass_length] at hk
    rw [gateAt_bypass hk] at hu
    split_ifs at hu with h
    · exact hRB k (by omega) u hu
    · simp only [aliasGate, List.mem_map] at hu
      obtain ⟨u', hu', rfl⟩ := hu
      have := hRB (k + 1) (by omega) u' hu'
      exact aliasWire_lt hi (by omega) (by omega)

  have modelBypass {n : ℕ} {C : Circuit} {r i : ℕ} (model : IsAO2 n C) (hi : i < n + r) :
      IsAO2 n (bypass n C r i) := by
    refine ⟨?_, bypass_readsBack hi model.2.1, ?_⟩
    · intro g hg
      obtain ⟨g', hmem, hop, _⟩ := bypass_mem g hg
      rw [hop]
      exact model.1 g' hmem
    · intro g hg
      obtain ⟨g', hmem, _, hlen⟩ := bypass_mem g hg
      exact hlen.trans (model.2.2 g' hmem)

  have drop : ∀ (C : Circuit) (u : Fin 11) (r w : ℕ),
      IsAO2 11 C → r < C.size → w < 11 + r →
      (∀ x : Fin 11 → Bool, x u = false → wval C x (11 + r) = wval C x w) →
      ∃ E : Circuit, IsAO2 11 E ∧ E.size + 1 = C.size ∧
        (∀ x : Fin 11 → Bool, x u = false → circuitFun 11 E x = circuitFun 11 C x) ∧
        ∀ (x : Fin 11 → Bool) (t : ℕ), t < 11 + r → wval E x t = wval C x t := by
    intro C u r w model hr hw heq
    change r < C.gates.length at hr
    have ops : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and ∨
        (gateAt C j).op = GateOp.or := fun j hj => model.1 _ (gateAt_mem hj)
    refine ⟨bypass 11 C r w, modelBypass model hw, ?_, ?_, ?_⟩
    · change (bypass 11 C r w).gates.length + 1 = C.gates.length
      rw [bypass_length]
      omega
    · intro x hx
      exact bypass_eval_eq List.length_ofFn ops hr (Or.inl hw) (heq x hx)
    · intro x t ht
      exact bypass_val_lt List.length_ofFn hr t ht

  have edgeAtPair : ∀ a b : Fin 11, graphFun x1 ∅ (pairInput a b) = true ↔ x1.Adj a b := by
    decide +kernel
  -- Pad to eighteen gates while preserving the output on the original wires.
  have faceBound (v : Fin 11) (C : Circuit) (hv : v.val < 4) (model : IsAO2 11 C)
      (faithful : ∀ x : Fin 11 → Bool, x v = false → circuitFun 11 C x = graphFun x1 ∅ x) :
      19 ≤ C.size := by
    by_contra tooSmall
    change ¬ 19 ≤ C.gates.length at tooSmall
    let pad : Gate := ⟨.or, [0, 0]⟩
    let E : Circuit := ⟨C.gates ++ List.replicate (18 - C.gates.length) pad, C.output⟩
    have lengthE : E.gates.length = 18 := by
      change (C.gates ++ List.replicate (18 - C.gates.length) pad).length = 18
      rw [List.length_append, List.length_replicate]
      omega
    have atGate (k : ℕ) (hk : k < E.gates.length) :
        gateAt E k = if k < C.gates.length then gateAt C k else pad := by
      rw [gateAt_eq hk]
      change (C.gates ++ List.replicate (18 - C.gates.length) pad)[k] = _
      by_cases old : k < C.gates.length
      · rw [if_pos old, gateAt_eq old, List.getElem_append_left old]
      · rw [if_neg old, List.getElem_append_right (by omega), List.getElem_replicate]
    have fromOld (gate : Gate) (hg : gate ∈ E.gates) : gate ∈ C.gates ∨ gate = pad := by
      change gate ∈ C.gates ++ List.replicate (18 - C.gates.length) pad at hg
      exact (List.mem_append.mp hg).imp id List.eq_of_mem_replicate
    have modelE : IsAO2 11 E := by
      refine ⟨?_, ?_, ?_⟩
      · intro gate hg
        rcases fromOld gate hg with old | eq
        · exact model.1 gate old
        · exact Or.inr (eq ▸ rfl)
      · intro k hk w hw
        rw [atGate k hk] at hw
        split_ifs at hw with old
        · exact model.2.1 k old w hw
        · have zero : w = 0 := by simpa [pad] using hw
          omega
      · intro gate hg
        rcases fromOld gate hg with old | eq
        · exact model.2.2 gate old
        · rw [eq]; rfl
    have off : ∀ u : Fin 11, u.val < 4 → pairInput (8 : Fin 11) 9 u = false := by decide +kernel
    have hit : x1.Adj 8 9 := by decide +kernel
    have valid : C.output < 11 + C.gates.length := by
      by_contra outside
      have no : circuitFun 11 C (pairInput 8 9) = false :=
        val_ge (C := C) (x := List.ofFn (pairInput (8 : Fin 11) 9)) List.length_ofFn (by omega)
      have yes := (faithful _ (off v hv)).trans ((edgeAtPair 8 9).mpr hit)
      exact Bool.false_ne_true (no.symm.trans yes)
    have same (x : Fin 11 → Bool) : circuitFun 11 E x = circuitFun 11 C x := by
      apply val_prefix (C := C) (D := E) (x := List.ofFn x) (m := C.gates.length)
        List.length_ofFn le_rfl (by omega) _ C.output valid
      intro k hk
      exact (atGate k (by omega)).trans (if_pos hk)
    apply boundary v E hv modelE lengthE
    · intro a b hab ha hb
      have vOff : pairInput a b v = false := by
        change decide (v = a ∨ v = b) = false
        simp [Ne.symm ha, Ne.symm hb]
      exact (same _).trans ((faithful _ vOff).trans ((edgeAtPair a b).mpr hab))
    · intro x hx negative _
      exact (same x).trans ((faithful x hx).trans negative)
  have hAO2 : IsAO2 11 D := hm.1
  have hfun : circuitFun 11 D = graphFun x1 ∅ := hm.2.1

  have dropG : ∀ (C : Circuit) (r w : ℕ), IsAO2 11 C → r < C.gates.length → w < 11 + r →
      (((∃ k, r < k ∧ k < C.gates.length ∧ 11 + r ∈ (gateAt C k).inputs) ∨ C.output = 11 + r) →
        ∀ x : Fin 11 → Bool, wval C x (11 + r) = wval C x w) →
      ∃ E : Circuit, IsAO2 11 E ∧ E.gates.length + 1 = C.gates.length ∧
        circuitFun 11 E = circuitFun 11 C := by
    intro C r w model hr hw heq
    have ops : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and ∨
        (gateAt C j).op = GateOp.or := fun j hj => model.1 _ (gateAt_mem hj)
    refine ⟨bypass 11 C r w, modelBypass model hw, ?_, ?_⟩
    · rw [bypass_length]
      omega
    · funext x
      exact bypass_ok List.length_ofFn ops hr hw (fun h => heq h x)

  have noRep : ∀ r w : ℕ, r < D.gates.length → w < 11 + r →
      (((∃ k, r < k ∧ k < D.gates.length ∧ 11 + r ∈ (gateAt D k).inputs) ∨ D.output = 11 + r) →
        ∀ x : Fin 11 → Bool, wval D x (11 + r) = wval D x w) → False := by
    intro r w hr hw heq
    obtain ⟨E, mE, lE, fE⟩ := dropG D r w hAO2 hr hw heq
    have hle := hm.2.2 E mE (fE.trans hfun)
    change D.gates.length ≤ E.gates.length at hle
    omega

  have hasReader : ∀ r, r < D.gates.length → D.output ≠ 11 + r →
      ∃ k, r < k ∧ k < D.gates.length ∧ 11 + r ∈ (gateAt D k).inputs := by
    intro r hr hout
    by_contra hno
    refine noRep r 0 hr (by omega) ?_
    rintro (h | h)
    · exact absurd h hno
    · exact absurd h hout

  have hRB : ∀ k < D.gates.length, ∀ u ∈ (gateAt D k).inputs, u < 11 + k := hAO2.2.1
  have hlen2 : ∀ k < D.gates.length, (gateAt D k).inputs.length = 2 :=
    fun k hk => hAO2.2.2 _ (gateAt_mem hk)

  have hinC : ∀ (C : Circuit) (w : Fin 11) (x : Fin 11 → Bool), wval C x w.val = x w := by
    intro C w x
    have hv := val_input (C := C) (x := List.ofFn x) List.length_ofFn w.isLt
    refine hv.trans ?_
    rw [List.getD_eq_getElem _ _ (by simp)]
    exact List.getElem_ofFn _

  have andFalse : ∀ (C : Circuit) (k : ℕ) (f : ℕ → Bool) (w : ℕ), (gateAt C k).op = GateOp.and →
      w ∈ (gateAt C k).inputs → f w = false →
      (gateAt C k).op.eval ((gateAt C k).inputs.map f) = false := by
    intro C k f w hop hw hf
    rw [hop]
    show ((gateAt C k).inputs.map f).all id = false
    rw [Bool.eq_false_iff]
    intro hall
    rw [List.all_eq_true] at hall
    have h1 := hall (f w) (List.mem_map.mpr ⟨w, hw, rfl⟩)
    rw [hf] at h1
    exact Bool.false_ne_true h1

  have hrl : r < D.gates.length := hr
  have hgl : g < D.gates.length := by omega
  have lastOut : D.output = 11 + (D.gates.length - 1) := by
    by_contra hne
    obtain ⟨k, hk1, hk2, _⟩ := hasReader (D.gates.length - 1) (by omega) hne
    omega

  by_cases priv : ∃ j, 11 + j ∈ (gateAt D g).inputs ∧
      ∀ k < D.gates.length, 11 + j ∈ (gateAt D k).inputs → k = g
  · obtain ⟨j, hjin, onlyG⟩ := priv
    have hjlt : 11 + j < 11 + g := hRB g hgl _ hjin
    have hjout : D.output ≠ 11 + j := by
      rw [lastOut]
      omega
    have hv11 : (v : ℕ) < 11 := v.isLt
    have hvg : (v : ℕ) ∈ (gateAt D g).inputs := (hvin g hgl).mpr rfl

    obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp (hlen2 r hrl)
    have hgr_in : 11 + g ∈ (gateAt D r).inputs := (hgin r hr).mpr rfl
    have hp : p < 11 + r := hRB r hrl p (by rw [hpq]; simp)
    have hq : q < 11 + r := hRB r hrl q (by rw [hpq]; simp)
    obtain ⟨z, hz⟩ : ∃ z : ℕ, z = if p = 11 + g then q else p := ⟨_, rfl⟩
    have hz_in : z ∈ (gateAt D r).inputs := by
      rw [hpq, hz]
      by_cases h : p = 11 + g
      · rw [ite_eq_left h]; simp
      · rw [ite_eq_right h]; simp
    have hzlt : z < 11 + r := hRB r hrl z hz_in
    have hzj : z ≠ 11 + j := by
      intro e
      have := onlyG r hrl (e ▸ hz_in)
      omega

    obtain ⟨D2, hD2⟩ : ∃ D2 : Circuit, D2 = ⟨(D.gates.set g ⟨GateOp.and, [(v : ℕ), (v : ℕ)]⟩).set j
        ⟨GateOp.and, [0, 0]⟩, D.output⟩ := ⟨_, rfl⟩
    have hlenD2 : D2.gates.length = D.gates.length := by
      rw [hD2]
      simp
    have hD2out : D2.output = D.output := by rw [hD2]
    have gateAt_D2 : ∀ k, gateAt D2 k = if k = j then (⟨GateOp.and, [0, 0]⟩ : Gate)
        else if k = g then (⟨GateOp.and, [(v : ℕ), (v : ℕ)]⟩ : Gate) else gateAt D k := by
      intro k
      have hjl : j < D.gates.length := by omega
      rw [hD2]
      change ((D.gates.set g ⟨GateOp.and, [(v : ℕ), (v : ℕ)]⟩).set j
        ⟨GateOp.and, [0, 0]⟩).getD k ⟨GateOp.or, []⟩ = _
      by_cases hkj : k = j
      · subst hkj
        rw [ite_eq_left rfl]
        simp [List.getD_eq_getElem?_getD, hjl]
      · rw [ite_eq_right hkj]
        by_cases hkg : k = g
        · subst hkg
          rw [ite_eq_left rfl]
          simp [List.getD_eq_getElem?_getD, hgl, Ne.symm hkj]
        · rw [ite_eq_right hkg]
          change _ = D.gates.getD k ⟨GateOp.or, []⟩
          simp [List.getD_eq_getElem?_getD, Ne.symm hkj, Ne.symm hkg]
    have memD2 : ∀ y ∈ D2.gates, y = (⟨GateOp.and, [0, 0]⟩ : Gate) ∨
        y = (⟨GateOp.and, [(v : ℕ), (v : ℕ)]⟩ : Gate) ∨ y ∈ D.gates := by
      intro y hy
      rw [hD2] at hy
      rcases List.mem_or_eq_of_mem_set hy with h | h
      · rcases List.mem_or_eq_of_mem_set h with h' | h'
        · exact Or.inr (Or.inr h')
        · exact Or.inr (Or.inl h')
      · exact Or.inl h
    have mD2 : IsAO2 11 D2 := by
      refine ⟨?_, ?_, ?_⟩
      · intro y hy
        rcases memD2 y hy with rfl | rfl | h
        · exact Or.inl rfl
        · exact Or.inl rfl
        · exact hAO2.1 y h
      · intro k hk u hu
        rw [hlenD2] at hk
        rw [gateAt_D2] at hu
        split_ifs at hu with h1 h2
        · simp at hu
          omega
        · simp at hu
          omega
        · exact hRB k hk u hu
      · intro y hy
        rcases memD2 y hy with rfl | rfl | h
        · rfl
        · rfl
        · exact hAO2.2.2 y h

    have FA : ∀ x : Fin 11 → Bool, x v = false → ∀ u, u ≠ 11 + j → wval D2 x u = wval D x u := by
      intro x hxv u
      have hx : (List.ofFn x).length = 11 := List.length_ofFn
      induction u using Nat.strong_induction_on with
      | _ u ih =>
        intro hne
        change val D2 (List.ofFn x) u = val D (List.ofFn x) u
        by_cases hu : u < 11
        · rw [val_input hx hu, val_input hx hu]
        · by_cases hge : 11 + D.gates.length ≤ u
          · rw [val_ge hx (by rw [hlenD2]; exact hge), val_ge hx hge]
          · obtain ⟨k, rfl⟩ : ∃ k, u = 11 + k := ⟨u - 11, by omega⟩
            have hk : k < D.gates.length := by omega
            have hkj : k ≠ j := by omega
            rw [val_gate hx (by rw [hlenD2]; exact hk), val_gate hx hk, gateAt_D2, ite_eq_right hkj]
            by_cases hkg : k = g
            · subst hkg
              rw [ite_eq_left rfl]
              have hvf : val D (List.ofFn x) (v : ℕ) = false := (hinC D v x).trans hxv
              have hvf2 : val D2 (List.ofFn x) (v : ℕ) = false := (hinC D2 v x).trans hxv
              rw [andFalse D k _ (v : ℕ) hgop hvg (by rw [ite_eq_left (by omega)]; exact hvf)]
              simp only [List.map_cons, List.map_nil, ite_eq_left (show (v : ℕ) < 11 + k by omega), hvf2]
              rfl
            · rw [ite_eq_right hkg]
              congr 1
              apply List.map_congr_left
              intro i hi
              by_cases hik : i < 11 + k
              · rw [ite_eq_left hik, ite_eq_left hik]
                exact ih i hik (fun e => hkg (onlyG k hk (e ▸ hi)))
              · rw [ite_eq_right hik, ite_eq_right hik]
    have hvalD2 : ∀ (x : Fin 11 → Bool) (k : ℕ), k < D.gates.length →
        wval D2 x (11 + k) = (gateAt D2 k).op.eval ((gateAt D2 k).inputs.map fun i =>
          if i < 11 + k then wval D2 x i else false) :=
      fun x k hk => val_gate List.length_ofFn (by rw [hlenD2]; exact hk)
    have repJ : ∀ x : Fin 11 → Bool, wval D2 x (11 + j) = wval D2 x 0 := by
      intro x
      rw [hvalD2 x j (by omega), gateAt_D2, ite_eq_left rfl]
      simp only [List.map_cons, List.map_nil, ite_eq_left (show 0 < 11 + j by omega)]
      cases wval D2 x 0 <;> rfl
    have repG : ∀ x : Fin 11 → Bool, wval D2 x (11 + g) = wval D2 x v := by
      intro x
      rw [hvalD2 x g hgl, gateAt_D2, ite_eq_right (by omega), ite_eq_left rfl]
      simp only [List.map_cons, List.map_nil, ite_eq_left (show (v : ℕ) < 11 + g by omega)]
      cases wval D2 x v <;> rfl
    have gFalse : ∀ x : Fin 11 → Bool, x v = false → wval D x (11 + g) = false := by
      intro x hxv
      change val D (List.ofFn x) (11 + g) = false
      rw [val_gate List.length_ofFn hgl]
      exact andFalse D g _ (v : ℕ) hgop hvg (by rw [ite_eq_left (by omega)]; exact (hinC D v x).trans hxv)
    have repR : ∀ x : Fin 11 → Bool, x v = false → wval D2 x (11 + r) = wval D2 x z := by
      intro x hxv
      rw [FA x hxv _ (by omega), FA x hxv _ hzj]
      have hgf := gFalse x hxv
      change val D (List.ofFn x) (11 + r) = val D (List.ofFn x) z
      change val D (List.ofFn x) (11 + g) = false at hgf
      rw [val_gate List.length_ofFn hrl, hrop, hpq]
      simp only [List.map_cons, List.map_nil, ite_eq_left hp, ite_eq_left hq]
      have hgin2 := hgr_in
      rw [hpq, List.mem_pair] at hgin2
      by_cases hpg : p = 11 + g
      · rw [hz, ite_eq_left hpg, hpg, hgf]
        cases val D (List.ofFn x) q <;> rfl
      · have hqg : q = 11 + g := by
          rcases hgin2 with h | h
          · exact absurd h.symm hpg
          · exact h.symm
        rw [hz, ite_eq_right hpg, hqg, hgf]
        cases val D (List.ofFn x) p <;> rfl

    have hD2size : D2.size = D.size := hlenD2
    obtain ⟨E1, mE1, lE1, oE1, pE1⟩ := drop D2 v r z mD2 (by omega) hzlt repR
    have repG1 : ∀ x : Fin 11 → Bool, x v = false → wval E1 x (11 + g) = wval E1 x v := by
      intro x _
      rw [pE1 x _ (by omega), pE1 x _ (by omega)]
      exact repG x
    obtain ⟨E2, mE2, lE2, oE2, pE2⟩ := drop E1 v g v mE1 (by omega) (by omega) repG1
    have repJ2 : ∀ x : Fin 11 → Bool, x v = false → wval E2 x (11 + j) = wval E2 x 0 := by
      intro x _
      rw [pE2 x _ (by omega), pE2 x _ (by omega), pE1 x _ (by omega), pE1 x _ (by omega)]
      exact repJ x
    obtain ⟨E3, mE3, lE3, oE3, _⟩ := drop E2 v j 0 mE2 (by omega) (by omega) repJ2
    have hD2fun : ∀ x : Fin 11 → Bool, x v = false → circuitFun 11 D2 x = graphFun x1 ∅ x := by
      intro x hxv
      have e1 : circuitFun 11 D2 x = wval D2 x D2.output := rfl
      rw [e1, hD2out, FA x hxv _ hjout]
      exact congrFun hfun x
    have h19 := faceBound v E3 hv mE3 (fun x hxv =>
      (oE3 x hxv).trans ((oE2 x hxv).trans ((oE1 x hxv).trans (hD2fun x hxv))))
    omega
  · have priv' : ∀ j, 11 + j ∈ (gateAt D g).inputs →
        ∃ k < D.size, k ≠ g ∧ 11 + j ∈ (gateAt D k).inputs := by
      intro j hj
      by_contra hne
      exact priv ⟨j, hj, fun k hk hkin => by
        by_contra hkg
        exact hne ⟨k, hk, hkg, hkin⟩⟩
    have neighborPair : ∀ v : Fin 11, v.val < 4 → ∃ a b : Fin 11,
        a ≠ b ∧ x1.Adj v a ∧ x1.Adj v b := by decide +kernel
    have noDouble : ∀ v u a b : Fin 11, v ≠ u → a ≠ b →
        x1.Adj v a → x1.Adj v b → x1.Adj u a → x1.Adj u b → False := by
      decide +kernel
    have andOp (l : List Bool) : GateOp.and.eval l = l.all id := rfl
    have orOp (l : List Bool) : GateOp.or.eval l = l.any id := rfl
    have pairBit (p q i : Fin 11) : pairInput p q i = decide (i = p ∨ i = q) := rfl
    obtain ⟨a,b,hab,hva,hvb⟩ := neighborPair v hv
    have outNe : D.output ≠ (v : ℕ) := by
      rw [lastOut]
      have hh := v.isLt
      omega
    have rawOnly : ∀ j < D.gates.length, (v : ℕ) ∈ (gateAt D j).inputs → j = g :=
      fun j hj => (hvin j hj).mp
    have neighborWire (j : ℕ) (hw : 11+j ∈ (gateAt D g).inputs)
        (a : Fin 11) (ha : x1.Adj v a) : wval D (pairInput a a) (11+j) = true := by
      let xx := pairInput a a
      let yy := pairInput v a
      have raw : ∀ i : Fin 11, i.val ≠ v.val → xx i = yy i := by
        intro i hi
        have hne : i ≠ v := fun h => hi (congrArg Fin.val h)
        simp [xx,yy,pairBit,hne]
      have no : graphFun x1 ∅ xx = false := by
        apply Bool.eq_false_iff.mpr
        intro hit
        exact x1.loopless.irrefl a ((edgeAtPair a a).mp hit)
      have yes : graphFun x1 ∅ yy = true := (edgeAtPair v a).mpr ha
      have diff : D.eval (List.ofFn xx) ≠ D.eval (List.ofFn yy) := by
        change circuitFun 11 D xx ≠ circuitFun 11 D yy
        rw [congrFun hfun xx, congrFun hfun yy, no, yes]
        decide
      have effect := readOnceEffect D xx yy v.val g raw rawOnly outNe diff
      have hilt := hRB g hgl _ hw
      have hh := v.isLt
      have equal := beforeReader D xx yy v.val g raw rawOnly (11+j) (by omega) hilt
      by_contra notOn
      have off : wval D xx (11+j) = false := Bool.eq_false_iff.mpr notOn
      have offAtGate (z : Fin 11 → Bool) (hz : wval D z (11+j) = false) :
          wval D z (11+g) = false := by
        change val D (List.ofFn z) (11+g) = false
        rw [val_gate List.length_ofFn hgl]
        apply andFalse D g _ (11+j) hgop hw
        rw [ite_eq_left hilt]
        exact hz
      exact effect ((offAtGate xx off).trans (offAtGate yy (equal.symm.trans off)).symm)
    have monoW (x y : Fin 11 → Bool) (up : ∀ i, x i = true → y i = true) :
        ∀ w, wval D x w = true → wval D y w = true := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        by_cases raw : w < 11
        · rw [hinC D ⟨w,raw⟩ x, hinC D ⟨w,raw⟩ y]
          exact up _
        · change val D (List.ofFn x) w = true → val D (List.ofFn y) w = true
          by_cases outside : 11+D.gates.length ≤ w
          · rw [val_ge List.length_ofFn outside, val_ge List.length_ofFn outside]
            exact fun h => h
          · obtain ⟨k,rfl⟩ : ∃ k, w=11+k := ⟨w-11,by omega⟩
            have hk : k < D.gates.length := by omega
            rw [val_gate List.length_ofFn hk,val_gate List.length_ofFn hk]
            have operands : ∀ i ∈ (gateAt D k).inputs,
                (if i < 11+k then val D (List.ofFn x) i else false) = true →
                (if i < 11+k then val D (List.ofFn y) i else false) = true := by
              intro i hi
              have hb := hRB k hk i hi
              rw [ite_eq_left hb, ite_eq_left hb]
              exact ih i hb
            rcases hAO2.1 (gateAt D k) (gateAt_mem hk) with hop | hop
            · simp only [hop, andOp, List.all_map, Function.comp_def, id_eq, List.all_eq_true]
              exact fun hx i hi => operands i hi (hx i hi)
            · simp only [hop, orOp, List.any_map, Function.comp_def, id_eq, List.any_eq_true]
              rintro ⟨i,hi,hx⟩
              exact ⟨i,hi,operands i hi hx⟩
    have onlyInternal (j k : ℕ) (hj : 11+j ∈ (gateAt D g).inputs)
        (hk : k < D.size) (ne : k ≠ g) (hkj : 11+j ∈ (gateAt D k).inputs)
        (safe : BelowF x1 D k) (hand : (gateAt D k).op = GateOp.and) :
        ∀ u ∈ (gateAt D k).inputs, 11 ≤ u := by
      intro u hu
      by_contra huBound
      have ub : u < 11 := by omega
      let uu : Fin 11 := ⟨u,ub⟩
      have hh : uu ≠ v := by
        intro eq
        have eq' : u = v.val := congrArg Fin.val eq
        exact ne (rawOnly k hk (eq' ▸ hu))
      obtain ⟨p,q,hpq⟩ := List.length_eq_two.mp (hlen2 k hk)
      have operands : ∀ i ∈ (gateAt D k).inputs, i = u ∨ i = 11+j := by
        have one : u = p ∨ u = q := by simpa only [hpq,List.mem_pair] using hu
        have two : 11+j = p ∨ 11+j = q := by simpa only [hpq,List.mem_pair] using hkj
        intro i hi
        have here : i = p ∨ i = q := by simpa only [hpq,List.mem_pair] using hi
        omega
      have adj (p : Fin 11) (hvp : x1.Adj v p) : x1.Adj uu p := by
        let y := pairInput uu p
        have extend : ∀ i, (pairInput p p) i = true → y i = true := by
          intro i hi
          have e : i = p := by simpa [pairBit] using hi
          simp [y,pairBit,e]
        have nonzero := monoW _ y extend _ (neighborWire j hj p hvp)
        have rawTrue : wval D y u = true := (hinC D uu y).trans (by simp [y,pairBit])
        apply (edgeAtPair uu p).mp
        apply safe y
        change val D (List.ofFn y) (11+k) = true
        rw [val_gate List.length_ofFn hk,hand]
        simp only [andOp,List.all_map,Function.comp_def,id_eq,List.all_eq_true]
        intro i hi
        rw [ite_eq_left (hRB k hk i hi)]
        rcases operands i hi with h | h <;> rw [h]
        · exact rawTrue
        · exact nonzero
      exact noDouble v uu a b hh.symm hab hva hvb (adj a hva) (adj b hvb)
    have sharedWithInternal : ∀ j, 11+j ∈ (gateAt D g).inputs →
        ∃ k < D.size, k ≠ g ∧ (11+j ∈ (gateAt D k).inputs) ∧
          (BelowF x1 D k → (gateAt D k).op = .and → ∀ u ∈ (gateAt D k).inputs, 11 ≤ u) := by
      intro j hj
      obtain ⟨k,hk,hne,hread⟩ := priv' j hj
      exact ⟨k,hk,hne,hread,onlyInternal j k hj hk hne hread⟩
    have uniqueReaders (offset wire k : ℕ) (hk : k < D.size)
        (only : ∀ j < D.size, offset + wire ∈ (gateAt D j).inputs ↔ j = k) :
        readers offset D wire = {k} := by
      ext j
      change j ∈ (Finset.range D.gates.length).filter (fun i => offset + wire ∈ (gateAt D i).inputs) ↔ j ∈ ({k} : Finset ℕ)
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      exact ⟨fun h => (only j h.1).mp h.2, fun e => e ▸ ⟨hk, (only k hk).mpr rfl⟩⟩
    have rv := uniqueReaders 0 v.val g hgl (by simpa only [Nat.zero_add] using hvin)
    have rg := uniqueReaders 11 g r hr hgin
    -- With this OR gate already on, switching on v cannot change the output.
    have masked : x1.neighborFinset v ⊆ wmax x1 D r := by
      intro t ht
      have hvt : x1.Adj v t := (SimpleGraph.mem_neighborFinset x1 v t).mp ht
      change t ∈ Finset.univ.filter (fun w : Fin 11 =>
        ∀ x : Fin 11 → Bool, gateVal 11 D r x = true → x w = true → graphFun x1 ∅ x = true)
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ t, ?_⟩
      intro x onX xt
      let y := fun i : Fin 11 => decide (i = v) || x i
      have onY := monoW x y (by intro i hi; simp [y, hi]) (11+r) onX
      have raw (i : Fin 11) (hi : i.val ≠ v.val) : x i = y i := by
        have hi' : i ≠ v := fun e => hi (congrArg Fin.val e)
        simp [y, hi']
      have equal := agreeOutside D x y (fun w => w = v.val ∨ w = 11+g)
        (fun i hi => raw i (fun e => hi (Or.inl e))) (by
          intro j hj allowed
          by_cases jr : j = r
          · subst j
            exact Or.inl (onX.trans onY.symm)
          · right
            intro w hw _ blocked
            rcases blocked with e | e
            · subst w
              exact allowed (Or.inr (congrArg (fun k => 11 + k) ((hvin j hj).mp hw)))
            · subst w
              exact jr ((hgin j hj).mp hw)) D.output (by
              rintro (e | e)
              · exact outNe e
              · rw [lastOut] at e
                omega)
      change circuitFun 11 D x = circuitFun 11 D y at equal
      rw [hfun] at equal
      rw [equal]
      change (decide (∃ a ∈ (∅ : Finset (Fin 11)), y a = true) ||
        decide (∃ a b, x1.Adj a b ∧ y a = true ∧ y b = true)) = true
      simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
        decide_eq_true_eq]
      exact ⟨v, t, hvt, by simp [y], by simp [y, xt]⟩
    have foldl_snoc_length {α β : Type} (h : List α → β → α) (gs : List β) (init : List α) :
        (gs.foldl (fun acc g => acc ++ [h acc g]) init).length = init.length + gs.length := by
      induction gs generalizing init with
      | nil => simp
      | cons g gs ih =>
        simp only [List.foldl_cons, List.length_cons]
        rw [ih, List.length_append, List.length_singleton]
        omega

    have foldl_snoc_getD_lt {α β : Type} (h : List α → β → α) (gs : List β) (init : List α)
        (i : ℕ) (d : α) (hi : i < init.length) :
        (gs.foldl (fun acc g => acc ++ [h acc g]) init).getD i d = init.getD i d := by
      induction gs generalizing init with
      | nil => rfl
      | cons g gs ih =>
        simp only [List.foldl_cons]
        have hi' : i < (init ++ [h init g]).length := by
          rw [List.length_append, List.length_singleton]; omega
        rw [ih (init ++ [h init g]) hi']
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

    have foldl_snoc_getD_add {α β : Type} (h : List α → β → α) (gs : List β) (init : List α)
        (j : ℕ) (d : α) (hj : j < gs.length) :
        (gs.foldl (fun acc g => acc ++ [h acc g]) init).getD (init.length + j) d =
          h ((gs.take j).foldl (fun acc g => acc ++ [h acc g]) init) (gs[j]) := by
      induction gs generalizing init j with
      | nil => simp at hj
      | cons g gs ih =>
        cases j with
        | zero =>
          simp only [List.foldl_cons, List.take_zero, List.foldl_nil, List.getElem_cons_zero, Nat.add_zero]
          have hlt : init.length < (init ++ [h init g]).length := by
            rw [List.length_append, List.length_singleton]; omega
          rw [foldl_snoc_getD_lt h gs (init ++ [h init g]) init.length d hlt]
          simp [List.getD_eq_getElem?_getD]
        | succ j =>
          simp only [List.foldl_cons, List.take_succ_cons, List.getElem_cons_succ]
          have hlen : (init ++ [h init g]).length = init.length + 1 := by simp
          have hj' : j < gs.length := by simp at hj; omega
          have hidx : init.length + (j + 1) = (init ++ [h init g]).length + j := by rw [hlen]; omega
          rw [hidx]
          exact ih (init ++ [h init g]) j hj'

    have foldl_snoc_take_getD {α β : Type} (h : List α → β → α) (gs : List β) (init : List α)
        (j k : ℕ) (d : α) (hj : j ≤ gs.length) (hk : k < init.length + j) :
        ((gs.take j).foldl (fun acc g => acc ++ [h acc g]) init).getD k d =
          (gs.foldl (fun acc g => acc ++ [h acc g]) init).getD k d := by
      have hsplit : gs = gs.take j ++ gs.drop j := (List.take_append_drop j gs).symm
      conv_rhs => rw [hsplit, List.foldl_append]
      have hlen : ((gs.take j).foldl (fun acc g => acc ++ [h acc g]) init).length = init.length + j := by
        rw [foldl_snoc_length, List.length_take, Nat.min_eq_left hj]
      rw [foldl_snoc_getD_lt h (gs.drop j) _ k d (by omega)]

    have orReaches_iff_gate (n : ℕ) (C : Circuit) (j g : ℕ) (hj : j < C.gates.length) :
        OrReaches n C (n + j) g ↔
          g = j ∨ ((gateAt C j).op = GateOp.or ∧
            ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ OrReaches n C w g) := by
      let f : List (List ℕ) → Gate → List ℕ := fun cs g =>
        cs.length :: (@ite _ (g.op = GateOp.or) (gateOpDecEq _ _)
          ((g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
            (fun w => cs.getD (w - n) []))
          [])
      unfold OrReaches orSets orStep
      simp only [Nat.le_add_right, Nat.add_sub_cancel_left, true_and]
      change g ∈ (C.gates.foldl (fun acc g => acc ++ [f acc g]) []).getD j [] ↔ _
      have hstep := foldl_snoc_getD_add f C.gates [] j [] hj
      simp only [List.length_nil, Nat.zero_add] at hstep
      rw [hstep, ← gateAt_eq (C := C) hj]
      have hplen : ((C.gates.take j).foldl (fun acc g => acc ++ [f acc g]) []).length = j := by
        rw [foldl_snoc_length, List.length_nil, Nat.zero_add, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
      simp only [f, hplen, List.mem_cons]
      constructor
      · rintro (rfl | hmem)
        · exact Or.inl rfl
        · right
          split_ifs at hmem with hor
          · simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at hmem
            rcases hmem with ⟨w, ⟨hw, hnw, hlt⟩, hg⟩
            have hsub : w - n < ([] : List (List ℕ)).length + j := by simp; omega
            rw [foldl_snoc_take_getD f C.gates [] j (w - n) [] (Nat.le_of_lt hj) hsub] at hg
            exact ⟨hor, w, hw, hnw, hlt, hnw, hg⟩
          · simp at hmem
      · rintro (rfl | ⟨hor, w, hw, hnw, hlt, _, hg⟩)
        · exact Or.inl rfl
        · right
          rw [if_pos hor]
          simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
          refine ⟨w, ⟨hw, hnw, hlt⟩, ?_⟩
          have hsub : w - n < ([] : List (List ℕ)).length + j := by simp; omega
          rwa [foldl_snoc_take_getD f C.gates [] j (w - n) [] (Nat.le_of_lt hj) hsub]

    have orReader (j : ℕ) (hj : j < D.size) (hop : (gateAt D j).op = .or)
        (w : ℕ) (hw : w ∈ (gateAt D j).inputs) (x : Fin 11 → Bool)
        (high : wval D x w = true) : wval D x (11+j) = true := by
      change val D (List.ofFn x) (11+j) = true
      rw [val_gate List.length_ofFn hj, hop, orOp, List.any_eq_true]
      refine ⟨true, List.mem_map.mpr ⟨w, hw, ?_⟩, rfl⟩
      rw [ite_eq_left (hRB j hj w hw)]
      exact high
    have upOR (x : Fin 11 → Bool) (k : ℕ) (high : wval D x (11+k) = true) :
        ∀ j < D.size, OrReaches 11 D (11+j) k → wval D x (11+j) = true := by
      intro j
      induction j using Nat.strong_induction_on with
      | ind j ih =>
        intro hj path
        rcases (orReaches_iff_gate 11 D j k hj).mp path with eq | ⟨hop, w, hw, hn, hlt, child⟩
        · exact eq ▸ high
        · have name : 11 + (w - 11) = w := by omega
          apply orReader j hj hop w hw x
          rw [← name] at child ⊢
          exact ih (w-11) (by omega) (by omega) child
    -- An input in the OR closure would have to share both neighbors of v.
    have noRawPath : orIn 11 D (11+r) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.2
      intro u hu
      delta PEqualNP.TopForm.orIn at hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      rcases hu with impossible | ⟨k, hk, path, hop, input⟩
      · have h := u.isLt
        omega
      · have different : u ≠ v := by
          intro e
          subst u
          have same := rawOnly k hk input
          rw [same, hgop] at hop
          contradiction
        have both (t : Fin 11) (adj : x1.Adj v t) : x1.Adj u t := by
          let x := pairInput u t
          have wireHigh := (hinC D u x).trans (show x u = true by simp [x, pairBit])
          have sourceHigh := orReader k hk hop u.val input x wireHigh
          have targetHigh := upOR x k sourceHigh r hr path
          have inMax := masked ((SimpleGraph.mem_neighborFinset x1 v t).mpr adj)
          have guarded : ∀ z : Fin 11 → Bool, gateVal 11 D r z = true → z t = true →
              graphFun x1 ∅ z = true := (Finset.mem_filter.mp inMax).2
          exact (edgeAtPair u t).mp (guarded x targetHigh (by simp [x,pairBit]))
        exact noDouble v u a b different.symm hab hva hvb (both a hva) (both b hvb)
    obtain ⟨u, E, hu, mE, hEs, hEf⟩ :=
      shared D hm ht hj hsz hnum v g r hv hgr hr hgop hrop rv rg sharedWithInternal masked noRawPath
    have h19 := faceBound u E hu mE hEf
    omega
