import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19139_aux

private def step (w : List ℕ) (g : Bool × Fin 32 × Fin 32) : List ℕ :=
  w ++ [if g.1 = Bool.true then w.getD g.2.1.val 0 &&& w.getD g.2.2.val 0 else w.getD g.2.1.val 0 ||| w.getD g.2.2.val 0]

private lemma foldl_step_length (gs : List (Bool × Fin 32 × Fin 32)) (w : List ℕ) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

private lemma foldl_step_getD_lt (gs : List (Bool × Fin 32 × Fin 32)) (w : List ℕ) (i : ℕ)
    (hi : i < w.length) :
    (gs.foldl step w).getD i 0 = w.getD i 0 := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    rw [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]

private lemma foldl_step_getD_of_take (gs : List (Bool × Fin 32 × Fin 32)) (w : List ℕ)
    (k i : ℕ) (hi : i < w.length + min k gs.length) :
    (gs.foldl step w).getD i 0 = ((gs.take k).foldl step w).getD i 0 := by
  have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
  conv_lhs => rw [hsplit]
  rw [List.foldl_append]
  apply foldl_step_getD_lt
  rw [foldl_step_length, List.length_take]
  omega

private lemma take_ofFn_succ {α : Type*} {n : ℕ} (f : Fin n → α) (k : ℕ) (hk : k < n) :
    (List.ofFn f).take (k + 1) = (List.ofFn f).take k ++ [f ⟨k, hk⟩] := by
  have hlen : k < (List.ofFn f).length := by simpa using hk
  rw [List.take_succ_eq_append_getElem hlen]
  simp

private def findPos : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: t, v => if a = v then 0 else 1 + findPos t v

private lemma findPos_lt : ∀ (l : List ℕ) (v : ℕ), v ∈ l → findPos l v < l.length
  | [], _, h => by simp at h
  | a :: t, v, h => by
    simp only [findPos]
    by_cases hav : a = v
    · simp [hav]
    · simp only [hav, ite_false, List.length_cons]
      have ht : v ∈ t := by
        rcases List.mem_cons.mp h with rfl | ht
        · exact False.elim (hav rfl)
        · exact ht
      have := findPos_lt t v ht
      omega

private lemma findPos_getD : ∀ (l : List ℕ) (v : ℕ), v ∈ l → l.getD (findPos l v) 0 = v
  | [], _, h => by simp at h
  | a :: t, v, h => by
    simp only [findPos]
    by_cases hav : a = v
    · subst hav; simp
    · simp only [hav, ite_false]
      have ht : v ∈ t := by
        rcases List.mem_cons.mp h with rfl | ht
        · exact False.elim (hav rfl)
        · exact ht
      have h1 : (a :: t).getD (1 + findPos t v) 0 = t.getD (findPos t v) 0 := by
        rw [Nat.add_comm]; rfl
      rw [h1]
      exact findPos_getD t v ht

private def foldOr (l : List (ℕ × ℕ)) : ℕ :=
  l.foldl (fun acc p => acc ||| p.1 &&& p.2) 0

private lemma foldOr_take_one (x4 : List (ℕ × ℕ)) (h0 : 0 < x4.length) :
    foldOr (x4.take 1) = (x4.get ⟨0, h0⟩).1 &&& (x4.get ⟨0, h0⟩).2 := by
  have ht : x4.take 1 = [x4.get ⟨0, h0⟩] := by
    rw [List.take_succ_eq_append_getElem h0]
    simp
  rw [foldOr, ht, List.foldl_cons, List.foldl_nil, Nat.zero_or]

private lemma foldOr_take_succ (x4 : List (ℕ × ℕ)) (t : ℕ) (ht : t < x4.length) :
    foldOr (x4.take (t + 1)) = foldOr (x4.take t) ||| ((x4.get ⟨t, ht⟩).1 &&& (x4.get ⟨t, ht⟩).2) := by
  rw [foldOr, List.take_succ_eq_append_getElem ht, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

private lemma count_true_ofFn_eq_card (x2 : List ℕ) (x3 : Finset ℕ) (hnodup : x2.Nodup)
    (hsub : x3 ⊆ x2.toFinset) (hb : x2.length ≤ 21) (p : Fin 21 → Bool)
    (hp : ∀ k : Fin 21, p k = if hk : k.val < x2.length then decide (x2.get ⟨k.val, hk⟩ ∈ x3) else false) :
    List.count Bool.true (List.ofFn p) = x3.card := by
  have h1 : List.count Bool.true (List.ofFn p) =
      List.count Bool.true ((List.range 21).map (fun i => if hi : i < x2.length then decide (x2.get ⟨i, hi⟩ ∈ x3) else false)) := by
    congr 1
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
      exact hp ⟨i, by simpa using hi1⟩
  rw [h1]
  have hsplit : List.range 21 = List.range x2.length ++ (List.range (21 - x2.length)).map (fun j => x2.length + j) := by
    apply List.ext_getElem
    · simp; omega
    · intro i hi1 hi2
      rw [List.getElem_range]
      by_cases hlt : i < x2.length
      · rw [List.getElem_append_left (by simp; exact hlt), List.getElem_range]
      · rw [List.getElem_append_right (by simp; omega)]
        simp only [List.length_range, List.getElem_map, List.getElem_range]
        omega
  rw [hsplit, List.map_append, List.count_append]
  have hzero : List.count Bool.true (((List.range (21 - x2.length)).map (fun j => x2.length + j)).map
      (fun i => if hi : i < x2.length then decide (x2.get ⟨i, hi⟩ ∈ x3) else false)) = 0 := by
    rw [List.count_eq_zero]
    intro hmem
    rw [List.mem_map] at hmem
    rcases hmem with ⟨i, hi, hval⟩
    rw [List.mem_map] at hi
    rcases hi with ⟨j, _, rfl⟩
    have hnot : ¬ (x2.length + j < x2.length) := by omega
    rw [dif_neg hnot] at hval
    exact Bool.false_ne_true hval
  rw [hzero, Nat.add_zero]
  have hmap : (List.range x2.length).map
      (fun i => if hi : i < x2.length then decide (x2.get ⟨i, hi⟩ ∈ x3) else false) =
      x2.map (fun v => decide (v ∈ x3)) := by
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      have hi : i < x2.length := by simpa using hi1
      simp [hi]
  rw [hmap, List.count_eq_countP, List.countP_map]
  have hcp : x2.countP ((fun x => x == Bool.true) ∘ fun v => decide (v ∈ x3)) =
      (x2.filter (fun v => decide (v ∈ x3))).length := by
    rw [List.countP_eq_length_filter]
    apply congrArg List.length
    apply List.filter_congr
    intro v _
    simp
  rw [hcp]
  have hfnodup : (x2.filter (fun v => decide (v ∈ x3))).Nodup := hnodup.filter _
  have hfeq : (x2.filter (fun v => decide (v ∈ x3))).toFinset = x3 := by
    ext v
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · intro h; exact h.2
    · intro hv
      have hm : v ∈ x2.toFinset := hsub hv
      exact ⟨List.mem_toFinset.mp hm, hv⟩
  rw [← List.toFinset_card_of_nodup hfnodup, hfeq]

theorem main :
    ∀ (x1 x2 : List ℕ) (x3 : Finset ℕ) (x4 : List (ℕ × ℕ)) (x5 : ℕ),
      x1.length = 11 →
        x2.Nodup →
          x3 ⊆ x2.toFinset →
            x4 ≠ [] →
              x2.length + 2 * x4.length ≤ 22 →
                (∀ (x11 : Fin x2.length),
                    have x12 : List ℕ := x1 ++ List.take (↑x11) x2;
                    ∃ x13 ∈ x12, ∃ x14 ∈ x12, x2.get x11 = if x2.get x11 ∈ x3 then x13 &&& x14 else x13 ||| x14) →
                  (∀ x12 ∈ x3, x12 &&& x5 ≠ 0) →
                    (∀ x13 ∈ x4, x13.1 ∈ x1 ++ x2 ∧ x13.2 ∈ x1 ++ x2 ∧ x13.1 &&& x13.2 &&& x5 = 0) →
                      ∃ (x14 : Fin 21 → Bool × Fin 32 × Fin 32) (x15 : ℕ → Bool),
                        have x16 : List ℕ := List.foldl (fun (x16 : List ℕ) (x17 : Bool × Fin 32 × Fin 32) => x16 ++ [if x17.1 = Bool.true then x16.getD ↑x17.2.1 0 &&& x16.getD ↑x17.2.2 0 else x16.getD ↑x17.2.1 0 ||| x16.getD ↑x17.2.2 0]) x1 (List.ofFn x14);
                        (∀ (x17 : Fin 21), (x14 x17).2.1.val < 11 + x17.val ∧ (x14 x17).2.2.val < 11 + x17.val) ∧ x16.getD 31 0 = List.foldl (fun (x17 : ℕ) (x18 : ℕ × ℕ) => x17 ||| x18.1 &&& x18.2) 0 x4 ∧ List.count Bool.true (List.ofFn fun (x17 : Fin 21) => Decidable.decide ((x14 x17).1 = Bool.true ∧ x16.getD (11 + x17.val) 0 &&& x5 ≠ 0)) = x3.card ∧ (∀ (x17 : Fin 21), (x14 x17).1 = Bool.true ∨ x15 (11 + x17.val) = Bool.true → x15 (x14 x17).2.1.val = Bool.true ∧ x15 (x14 x17).2.2.val = Bool.true) ∧ ∀ (x17 : Fin 21), (x14 x17).1 = Bool.true → x16.getD (11 + x17.val) 0 &&& x5 = 0 → x15 (11 + x17.val) = Bool.false := by
  intro x1 x2 x3 x4 x5 hx1 hnodup hx3sub hx4ne hsize hx2gen hx3nz hx4ok
  let b := x2.length
  let m := x4.length
  have hmpos : 1 ≤ m := by
    cases x4 with
    | nil => exact False.elim (hx4ne rfl)
    | cons _ _ => simp [m]
  have hb20 : b ≤ 20 := by omega
  have hbm21 : b + m ≤ 21 := by omega
  have hbm2 : b + 2 * m - 1 ≤ 21 := by omega
  let g1 : (k : ℕ) → k < b → Bool × Fin 32 × Fin 32 := fun k hk =>
    let hex := hx2gen ⟨k, hk⟩
    let a := Classical.choose hex
    let haSpec := Classical.choose_spec hex
    let c := Classical.choose haSpec.2
    let hcSpec := Classical.choose_spec haSpec.2
    let l := x1 ++ x2.take k
    let i1 := findPos l a
    let i2 := findPos l c
    have hl : l.length = 11 + k := by simp [l, hx1]; omega
    have hi1 : i1 < 11 + k := by rw [← hl]; exact findPos_lt l a haSpec.1
    have hi2 : i2 < 11 + k := by rw [← hl]; exact findPos_lt l c hcSpec.1
    (decide (x2.get ⟨k, hk⟩ ∈ x3), ⟨i1, by omega⟩, ⟨i2, by omega⟩)
  let g2 : (k : ℕ) → ¬ k < b → k < b + m → Bool × Fin 32 × Fin 32 := fun k hnb hk =>
    let j := k - b
    have hj : j < x4.length := by omega
    let p := x4.get ⟨j, hj⟩
    have hp : p ∈ x4 := List.get_mem x4 ⟨j, hj⟩
    have hok := hx4ok p hp
    let l := x1 ++ x2
    let i1 := findPos l p.1
    let i2 := findPos l p.2
    have hl : l.length = 11 + b := by simp [l, hx1, b]
    have hi1 : i1 < 11 + b := by rw [← hl]; exact findPos_lt l p.1 hok.1
    have hi2 : i2 < 11 + b := by rw [← hl]; exact findPos_lt l p.2 hok.2.1
    (Bool.true, ⟨i1, by omega⟩, ⟨i2, by omega⟩)
  let x14 : Fin 21 → Bool × Fin 32 × Fin 32 := fun k =>
    if hk1 : k.val < b then g1 k.val hk1
    else if hk2 : k.val < b + m then g2 k.val hk1 hk2
    else if hk3 : k.val < b + 2 * m - 1 then
      let j := k.val - (b + m)
      let i1 := if j = 0 then 11 + b else 11 + k.val - 1
      let i2 := 11 + b + j + 1
      have hi1 : i1 < 32 := by dsimp [i1]; split <;> omega
      (Bool.false, ⟨i1, hi1⟩, ⟨i2, by omega⟩)
    else
      (Bool.false, ⟨11 + k.val - 1, by omega⟩, ⟨11 + k.val - 1, by omega⟩)
  let x15 : ℕ → Bool := fun w => decide (w < 11 + b)
  refine ⟨x14, x15, ?_⟩
  let W : ℕ → List ℕ := fun k => ((List.ofFn x14).take k).foldl step x1
  have hW21 : W 21 = List.foldl step x1 (List.ofFn x14) := by
    simp [W]
  have hWlen : ∀ k ≤ 21, (W k).length = 11 + k := by
    intro k hk
    simp only [W, foldl_step_length, hx1, List.length_take, List.length_ofFn]
    omega
  have hWsucc : ∀ (k : ℕ) (hk : k < 21), W (k + 1) = step (W k) (x14 ⟨k, hk⟩) := by
    intro k hk
    simp only [W, take_ofFn_succ x14 k hk, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hWget_lt : ∀ k ≤ 21, ∀ i < 11 + k, (W 21).getD i 0 = (W k).getD i 0 := by
    intro k hk i hi
    rw [hW21]
    exact foldl_step_getD_of_take (List.ofFn x14) x1 k i (by simp [hx1]; omega)
  have hWget_gate : ∀ (k : ℕ) (hk : k < 21),
      (W 21).getD (11 + k) 0 =
        if (x14 ⟨k, hk⟩).1 = Bool.true then
          (W k).getD (x14 ⟨k, hk⟩).2.1.val 0 &&& (W k).getD (x14 ⟨k, hk⟩).2.2.val 0
        else
          (W k).getD (x14 ⟨k, hk⟩).2.1.val 0 ||| (W k).getD (x14 ⟨k, hk⟩).2.2.val 0 := by
    intro k hk
    rw [hWget_lt (k + 1) (by omega) (11 + k) (by omega), hWsucc k hk, step]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hWlen k (by omega)])]
    rw [hWlen k (by omega), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  have hphase1 : ∀ k ≤ b, W k = x1 ++ x2.take k := by
    intro k
    induction k with
    | zero =>
      intro _
      simp [W]
    | succ k ih =>
      intro hkb
      have hk21 : k < 21 := by omega
      have hkb' : k < b := by omega
      rw [hWsucc k hk21, ih (by omega)]
      simp only [x14, dif_pos hkb', g1, step]
      set hex := hx2gen ⟨k, hkb'⟩
      set a := Classical.choose hex
      set haSpec := Classical.choose_spec hex
      set c := Classical.choose haSpec.2
      set hcSpec := Classical.choose_spec haSpec.2
      have hga : (x1 ++ x2.take k).getD (findPos (x1 ++ x2.take k) a) 0 = a :=
        findPos_getD (x1 ++ x2.take k) a haSpec.1
      have hgc : (x1 ++ x2.take k).getD (findPos (x1 ++ x2.take k) c) 0 = c :=
        findPos_getD (x1 ++ x2.take k) c hcSpec.1
      have hval : (if decide (x2.get ⟨k, hkb'⟩ ∈ x3) = Bool.true then a &&& c else a ||| c) = x2.get ⟨k, hkb'⟩ := by
        have h2 := hcSpec.2
        by_cases hmem : x2.get ⟨k, hkb'⟩ ∈ x3
        · rw [if_pos hmem] at h2
          rw [if_pos (decide_eq_true hmem)]
          exact h2.symm
        · rw [if_neg hmem] at h2
          rw [if_neg (by rw [decide_eq_true_eq]; exact hmem)]
          exact h2.symm
      rw [hga, hgc, hval]
      rw [List.append_assoc, List.take_succ_eq_append_getElem hkb']
      rfl
  have hWb : W b = x1 ++ x2 := by
    have h := hphase1 b le_rfl
    simpa [b] using h
  have hphase1_get : ∀ (k : ℕ) (hk : k < b), (W 21).getD (11 + k) 0 = x2.get ⟨k, hk⟩ := by
    intro k hk
    rw [hWget_lt b (by omega) (11 + k) (by omega), hWb]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hx1]
    have hsub : 11 + k - 11 = k := by omega
    rw [hsub, List.getElem?_eq_getElem hk, Option.getD_some]
    rfl
  have hphase2_get : ∀ (j : ℕ) (hj : j < m),
      (W 21).getD (11 + (b + j)) 0 = (x4.get ⟨j, hj⟩).1 &&& (x4.get ⟨j, hj⟩).2 := by
    intro j hj
    have hk21 : b + j < 21 := by omega
    rw [hWget_gate (b + j) hk21]
    have hnb : ¬ (b + j < b) := by omega
    have hbm : b + j < b + m := by omega
    simp only [x14, dif_neg hnb, dif_pos hbm, g2, ↓reduceIte]
    have hjb : b + j - b = j := by omega
    have hj_fin : (⟨b + j - b, by omega⟩ : Fin x4.length) = ⟨j, hj⟩ := Fin.ext hjb
    have hp : x4.get ⟨b + j - b, by omega⟩ ∈ x4 := List.get_mem x4 _
    have hok := hx4ok _ hp
    have hi1lt : findPos (x1 ++ x2) (x4.get ⟨b + j - b, by omega⟩).1 < 11 + b := by
      have := findPos_lt (x1 ++ x2) _ hok.1
      simp only [List.length_append, hx1, b] at this
      exact this
    have hi2lt : findPos (x1 ++ x2) (x4.get ⟨b + j - b, by omega⟩).2 < 11 + b := by
      have := findPos_lt (x1 ++ x2) _ hok.2.1
      simp only [List.length_append, hx1, b] at this
      exact this
    have hget1 : (W (b + j)).getD (findPos (x1 ++ x2) (x4.get ⟨b + j - b, by omega⟩).1) 0 =
        (x4.get ⟨b + j - b, by omega⟩).1 := by
      rw [← hWget_lt (b + j) (by omega) _ (by omega), hWget_lt b (by omega) _ hi1lt, hWb]
      exact findPos_getD (x1 ++ x2) _ hok.1
    have hget2 : (W (b + j)).getD (findPos (x1 ++ x2) (x4.get ⟨b + j - b, by omega⟩).2) 0 =
        (x4.get ⟨b + j - b, by omega⟩).2 := by
      rw [← hWget_lt (b + j) (by omega) _ (by omega), hWget_lt b (by omega) _ hi2lt, hWb]
      exact findPos_getD (x1 ++ x2) _ hok.2.1
    rw [hget1, hget2, hj_fin]
  let pos : ℕ → ℕ := fun j => if j = 0 then 11 + b else 11 + b + m + j - 1
  have hphase3 : ∀ j < m, (W 21).getD (pos j) 0 = foldOr (x4.take (j + 1)) := by
    intro j
    induction j with
    | zero =>
      intro hj
      simp only [pos, ↓reduceIte]
      have h0 := hphase2_get 0 hj
      rw [Nat.add_zero] at h0
      rw [h0, foldOr_take_one x4 hj]
    | succ j ih =>
      intro hj
      have hjm : j < m := by omega
      have hpos_succ : pos (j + 1) = 11 + (b + m + j) := by
        simp only [pos, Nat.add_one_ne_zero, ↓reduceIte]
        omega
      rw [hpos_succ]
      have hk21 : b + m + j < 21 := by omega
      rw [hWget_gate (b + m + j) hk21]
      have hnb : ¬ (b + m + j < b) := by omega
      have hnbm : ¬ (b + m + j < b + m) := by omega
      have hk3 : b + m + j < b + 2 * m - 1 := by omega
      simp only [x14, dif_neg hnb, dif_neg hnbm, dif_pos hk3, Bool.false_eq_true, ↓reduceIte]
      have hjdiff : b + m + j - (b + m) = j := by omega
      have hi1_eq : (if b + m + j - (b + m) = 0 then 11 + b else 11 + (b + m + j) - 1) = pos j := by
        rw [hjdiff]
        simp only [pos]
        split <;> omega
      have hi1_lt : pos j < 11 + (b + m + j) := by
        simp only [pos]
        split <;> omega
      have hi2_eq : 11 + b + (b + m + j - (b + m)) + 1 = 11 + (b + (j + 1)) := by omega
      have hi2_lt : 11 + (b + (j + 1)) < 11 + (b + m + j) := by omega
      rw [hi1_eq, hi2_eq]
      rw [← hWget_lt (b + m + j) (by omega) (pos j) hi1_lt]
      rw [← hWget_lt (b + m + j) (by omega) (11 + (b + (j + 1))) hi2_lt]
      rw [ih hjm, hphase2_get (j + 1) hj, foldOr_take_succ x4 (j + 1) hj]
  have hphase3_end : (W 21).getD (11 + (b + 2 * m - 2)) 0 = foldOr x4 := by
    have hpeq : pos (m - 1) = 11 + (b + 2 * m - 2) := by
      simp only [pos]
      split <;> omega
    have h := hphase3 (m - 1) (by omega)
    rw [hpeq] at h
    have htake : x4.take (m - 1 + 1) = x4 := by
      have : m - 1 + 1 = x4.length := by omega
      rw [this, List.take_length]
    rw [htake] at h
    exact h
  have hphase4 : ∀ d : ℕ, b + 2 * m - 2 + d ≤ 20 → (W 21).getD (11 + (b + 2 * m - 2 + d)) 0 = foldOr x4 := by
    intro d
    induction d with
    | zero =>
      intro _
      simpa using hphase3_end
    | succ d ih =>
      intro hd
      set k := b + 2 * m - 2 + (d + 1)
      have hk21 : k < 21 := by omega
      rw [hWget_gate k hk21]
      have hnb : ¬ (k < b) := by omega
      have hnbm : ¬ (k < b + m) := by omega
      have hnk3 : ¬ (k < b + 2 * m - 1) := by omega
      simp only [x14, dif_neg hnb, dif_neg hnbm, dif_neg hnk3, Bool.false_eq_true, ↓reduceIte]
      have hprev : 11 + k - 1 = 11 + (b + 2 * m - 2 + d) := by omega
      rw [hprev, ← hWget_lt k (by omega) (11 + (b + 2 * m - 2 + d)) (by omega)]
      rw [ih (by omega), Nat.or_self]
  have hclaim1 : ∀ k : Fin 21, (x14 k).2.1.val < 11 + k.val ∧ (x14 k).2.2.val < 11 + k.val := by
    intro k
    by_cases hk1 : k.val < b
    · simp only [x14, dif_pos hk1, g1]
      set hex := hx2gen ⟨k.val, hk1⟩
      set a := Classical.choose hex
      set haSpec := Classical.choose_spec hex
      set c := Classical.choose haSpec.2
      set hcSpec := Classical.choose_spec haSpec.2
      have hl : (x1 ++ x2.take k.val).length = 11 + k.val := by simp [hx1]; omega
      exact ⟨by rw [← hl]; exact findPos_lt _ a haSpec.1, by rw [← hl]; exact findPos_lt _ c hcSpec.1⟩
    · by_cases hk2 : k.val < b + m
      · simp only [x14, dif_neg hk1, dif_pos hk2, g2]
        have hp : x4.get ⟨k.val - b, by omega⟩ ∈ x4 := List.get_mem x4 _
        have hok := hx4ok _ hp
        have hl : (x1 ++ x2).length = 11 + b := by simp [hx1, b]
        have hi1 := findPos_lt (x1 ++ x2) _ hok.1
        have hi2 := findPos_lt (x1 ++ x2) _ hok.2.1
        rw [hl] at hi1 hi2
        exact ⟨by omega, by omega⟩
      · by_cases hk3 : k.val < b + 2 * m - 1
        · simp only [x14, dif_neg hk1, dif_neg hk2, dif_pos hk3]
          constructor
          · split <;> omega
          · omega
        · simp only [x14, dif_neg hk1, dif_neg hk2, dif_neg hk3]
          omega
  have hclaim2 : (W 21).getD 31 0 = foldOr x4 := by
    have h := hphase4 (20 - (b + 2 * m - 2)) (by omega)
    have heq : 11 + (b + 2 * m - 2 + (20 - (b + 2 * m - 2))) = 31 := by omega
    rw [heq] at h
    exact h
  have hclaim3 : List.count Bool.true (List.ofFn fun k : Fin 21 =>
      Decidable.decide ((x14 k).1 = Bool.true ∧ (W 21).getD (11 + k.val) 0 &&& x5 ≠ 0)) = x3.card := by
    apply count_true_ofFn_eq_card x2 x3 hnodup hx3sub (by omega)
    intro k
    by_cases hk1 : k.val < b
    · rw [dif_pos hk1, hphase1_get k.val hk1]
      have h14op : (x14 k).1 = decide (x2.get ⟨k.val, hk1⟩ ∈ x3) := by
        simp only [x14, dif_pos hk1, g1]
      rw [h14op]
      by_cases hmem : x2.get ⟨k.val, hk1⟩ ∈ x3
      · have hnz := hx3nz _ hmem
        rw [decide_eq_true hmem]
        exact decide_eq_true ⟨rfl, hnz⟩
      · rw [decide_eq_false hmem]
        exact decide_eq_false (fun h => Bool.false_ne_true h.1)
    · rw [dif_neg hk1]
      by_cases hk2 : k.val < b + m
      · have hj : k.val - b < m := by omega
        have hk_eq : k.val = b + (k.val - b) := by omega
        have hv := hphase2_get (k.val - b) hj
        rw [← hk_eq] at hv
        have hp : x4.get ⟨k.val - b, hj⟩ ∈ x4 := List.get_mem x4 _
        have hz := (hx4ok _ hp).2.2
        rw [hv, decide_eq_false_iff_not]
        intro h
        exact h.2 hz
      · have h14f : (x14 k).1 = Bool.false := by
          by_cases hk3 : k.val < b + 2 * m - 1
          · simp only [x14, dif_neg hk1, dif_neg hk2, dif_pos hk3]
          · simp only [x14, dif_neg hk1, dif_neg hk2, dif_neg hk3]
        rw [h14f]
        simp
  have hclaim4 : ∀ k : Fin 21, (x14 k).1 = Bool.true ∨ x15 (11 + k.val) = Bool.true →
      x15 (x14 k).2.1.val = Bool.true ∧ x15 (x14 k).2.2.val = Bool.true := by
    intro k hor
    by_cases hk1 : k.val < b
    · have hlt := hclaim1 k
      simp only [x15, decide_eq_true_eq]
      exact ⟨by omega, by omega⟩
    · by_cases hk2 : k.val < b + m
      · simp only [x14, dif_neg hk1, dif_pos hk2, g2, x15, decide_eq_true_eq]
        have hp : x4.get ⟨k.val - b, by omega⟩ ∈ x4 := List.get_mem x4 _
        have hok := hx4ok _ hp
        have hl : (x1 ++ x2).length = 11 + b := by simp [hx1, b]
        have hi1 := findPos_lt (x1 ++ x2) _ hok.1
        have hi2 := findPos_lt (x1 ++ x2) _ hok.2.1
        rw [hl] at hi1 hi2
        exact ⟨hi1, hi2⟩
      · have h15f : x15 (11 + k.val) = Bool.false := by simp [x15]; omega
        have h14f : (x14 k).1 = Bool.false := by
          by_cases hk3 : k.val < b + 2 * m - 1
          · simp only [x14, dif_neg hk1, dif_neg hk2, dif_pos hk3]
          · simp only [x14, dif_neg hk1, dif_neg hk2, dif_neg hk3]
        rcases hor with h1 | h2
        · rw [h14f] at h1; exact False.elim (Bool.false_ne_true h1)
        · rw [h15f] at h2; exact False.elim (Bool.false_ne_true h2)
  have hclaim5 : ∀ k : Fin 21, (x14 k).1 = Bool.true →
      (W 21).getD (11 + k.val) 0 &&& x5 = 0 → x15 (11 + k.val) = Bool.false := by
    intro k hop hz
    by_cases hk1 : k.val < b
    · simp only [x14, dif_pos hk1, g1, decide_eq_true_eq] at hop
      rw [hphase1_get k.val hk1] at hz
      exact False.elim (hx3nz _ hop hz)
    · simp only [x15, decide_eq_false_iff_not]
      omega
  have hW21' : List.foldl (fun (x16 : List ℕ) (x17 : Bool × Fin 32 × Fin 32) => x16 ++ [if x17.1 = Bool.true then x16.getD ↑x17.2.1 0 &&& x16.getD ↑x17.2.2 0 else x16.getD ↑x17.2.1 0 ||| x16.getD ↑x17.2.2 0]) x1 (List.ofFn x14) = W 21 := hW21.symm
  refine ⟨hclaim1, ?_, ?_, hclaim4, ?_⟩
  · rw [hW21']; exact hclaim2
  · rw [hW21']; exact hclaim3
  · intro k; rw [hW21']; exact hclaim5 k

end PEqualNP.Outside.L_meta_19139_aux

theorem PEqualNP.Outside.L_meta_19139 : (∀ (x1 x2 : List ℕ) (x3 : Finset ℕ) (x4 : List (ℕ × ℕ)) (x5 : ℕ),   x1.length = (11 : ℕ) →     x2.Nodup →       x3 ⊆ x2.toFinset →         x4 ≠ [] →           x2.length + (2 : ℕ) * x4.length ≤ (22 : ℕ) →             (∀ (x11 : Fin x2.length),                 have x12 : List ℕ := x1 ++ List.take (↑x11) x2;                 ∃ x13 ∈ x12, ∃ x14 ∈ x12, x2.get x11 = if x2.get x11 ∈ x3 then x13 &&& x14 else x13 ||| x14) →               (∀ x12 ∈ x3, x12 &&& x5 ≠ (0 : ℕ)) →                 (∀ x13 ∈ x4, x13.1 ∈ x1 ++ x2 ∧ x13.2 ∈ x1 ++ x2 ∧ x13.1 &&& x13.2 &&& x5 = (0 : ℕ)) →                   ∃ (x14 : Fin (21 : ℕ) → Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) (x15 : ℕ → Bool),                     have x16 : List ℕ := List.foldl (fun (x16 : List ℕ) (x17 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => x16 ++ [if x17.1 = Bool.true then x16.getD ↑x17.2.1 (0 : ℕ) &&& x16.getD ↑x17.2.2 (0 : ℕ) else x16.getD ↑x17.2.1 (0 : ℕ) ||| x16.getD ↑x17.2.2 (0 : ℕ)]) x1 (List.ofFn x14);                     (∀ (x17 : Fin (21 : ℕ)), ↑(x14 x17).2.1 < (11 : ℕ) + ↑x17 ∧ ↑(x14 x17).2.2 < (11 : ℕ) + ↑x17) ∧ x16.getD (31 : ℕ) (0 : ℕ) = List.foldl (fun (x17 : ℕ) (x18 : ℕ × ℕ) => x17 ||| x18.1 &&& x18.2) (0 : ℕ) x4 ∧ List.count Bool.true (List.ofFn fun (x17 : Fin (21 : ℕ)) => Decidable.decide ((x14 x17).1 = Bool.true ∧ x16.getD ((11 : ℕ) + ↑x17) (0 : ℕ) &&& x5 ≠ (0 : ℕ))) = x3.card ∧ (∀ (x17 : Fin (21 : ℕ)), (x14 x17).1 = Bool.true ∨ x15 ((11 : ℕ) + ↑x17) = Bool.true → x15 ↑(x14 x17).2.1 = Bool.true ∧ x15 ↑(x14 x17).2.2 = Bool.true) ∧ ∀ (x17 : Fin (21 : ℕ)), (x14 x17).1 = Bool.true → x16.getD ((11 : ℕ) + ↑x17) (0 : ℕ) &&& x5 = (0 : ℕ) → x15 ((11 : ℕ) + ↑x17) = Bool.false) :=
  PEqualNP.Outside.L_meta_19139_aux.main
