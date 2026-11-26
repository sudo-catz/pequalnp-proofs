import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19152_aux

def adjB (a b : Fin 10) : Bool :=
  let es : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
  a ≠ b && (es.contains (a.val, b.val) || es.contains (b.val, a.val))

def rowsB (ms : List ℕ) : List ℕ :=
  ms.flatMap fun m => (List.finRange 4).flatMap fun a => (List.finRange 5).map fun b =>
    (List.finRange 10).foldl (fun acc (v : Fin 10) =>
      if m.testBit (((a.val + 1) * (v.val % 5) + b.val) % 5 +
        5 * ((v.val / 5 + (if a.val = 1 ∨ a.val = 2 then 1 else 0)) % 2))
      then acc ||| (1 <<< v.val) else acc) 0

def maskOfFinset (I : Finset (Fin 10)) : ℕ :=
  (List.finRange 10).foldl (fun acc (v : Fin 10) => if v ∈ I then acc ||| (1 <<< v.val) else acc) 0

def finsetOfMask (k : ℕ) : Finset (Fin 10) :=
  ((List.finRange 10).filter fun v : Fin 10 => k.testBit v.val).toFinset

def isMaxIndepB (k : ℕ) : Bool :=
  (List.finRange 10).all (fun a =>
    if k.testBit a.val then
      (List.finRange 10).all (fun c => !(k.testBit c.val && adjB a c))
    else
      (List.finRange 10).any (fun a' => k.testBit a'.val && adjB a' a))

def checkAllB : Bool :=
  let rNeg := rowsB [50, 116]
  let rPos := rowsB [51, 54, 101, 108]
  (List.range 1024).all fun k =>
    if isMaxIndepB k then
      rNeg.contains k &&
      (List.finRange 10).all (fun w =>
        k.testBit w.val || rPos.any (fun p => (p &&& (k ||| (1 <<< w.val))) == p))
    else true

set_option maxRecDepth 200000 in
lemma checkAllB_true : checkAllB = true := by decide +kernel

lemma testBit_foldl_or (l : List (Fin 10)) (p : Fin 10 → Bool) (acc : ℕ) (u : Fin 10) :
    (l.foldl (fun a v => if p v then a ||| (1 <<< v.val) else a) acc).testBit u.val =
      (acc.testBit u.val || (u ∈ l && p u)) := by
  induction l generalizing acc with
  | nil => simp
  | cons v l ih =>
    simp only [List.foldl_cons, ih, List.mem_cons]
    by_cases hp : p v = true
    · simp only [hp, ↓reduceIte, Nat.testBit_or, Nat.testBit_shiftLeft]
      by_cases huv : u = v
      · subst huv; simp [hp]
      · have hne : v.val ≠ u.val := fun h => huv (Fin.ext h.symm)
        have h1 : (1 : ℕ).testBit (u.val - v.val) = false ∨ ¬(v.val ≤ u.val) := by
          by_cases hle : v.val ≤ u.val
          · left
            have hpos : u.val - v.val ≠ 0 := by omega
            cases hd : u.val - v.val with
            | zero => omega
            | succ d => simp [Nat.testBit_succ]
          · exact Or.inr hle
        rcases h1 with h1 | h1
        · simp [huv, h1]
        · simp [huv, h1]
    · have hpf : p v = false := Bool.eq_false_iff.mpr hp
      simp only [hpf, Bool.false_eq_true, ↓reduceIte]
      by_cases huv : u = v
      · subst huv; simp [hpf]
      · simp [huv]

lemma maskOfFinset_testBit (I : Finset (Fin 10)) (u : Fin 10) :
    (maskOfFinset I).testBit u.val = decide (u ∈ I) := by
  unfold maskOfFinset
  have h := testBit_foldl_or (List.finRange 10) (fun v => decide (v ∈ I)) 0 u
  simpa using h

lemma maskOfFinset_lt (I : Finset (Fin 10)) : maskOfFinset I < 1024 := by
  have hlt : ∀ (l : List (Fin 10)) (acc : ℕ), acc < 1024 →
      l.foldl (fun a (v : Fin 10) => if v ∈ I then a ||| (1 <<< v.val) else a) acc < 1024 := by
    intro l
    induction l with
    | nil => intro acc ha; exact ha
    | cons v l ih =>
      intro acc ha
      simp only [List.foldl_cons]
      apply ih
      split_ifs
      · change acc ||| (1 <<< v.val) < 2 ^ 10
        apply Nat.or_lt_two_pow (by change acc < 2 ^ 10; exact ha)
        have hv : v.val < 10 := v.isLt
        have : 1 <<< v.val = 2 ^ v.val := by simp [Nat.shiftLeft_eq]
        rw [this]
        exact Nat.pow_lt_pow_right (by omega) hv
      · exact ha
  exact hlt (List.finRange 10) 0 (by omega)

lemma maskOfFinset_eq_finset (I : Finset (Fin 10)) : finsetOfMask (maskOfFinset I) = I := by
  ext u
  simp [finsetOfMask, maskOfFinset_testBit]

lemma adjB_iff (a b : Fin 10) :
    adjB a b = true ↔
      (SimpleGraph.fromRel (fun a b : Fin 10 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (ℕ × ℕ)))).Adj a b := by
  revert a b; decide

lemma rows_eq_image (ms : List ℕ) :
    ((ms.flatMap fun m => (List.finRange 4).flatMap fun a => (List.finRange 5).map fun b =>
      ((List.finRange 10).filter fun v : Fin 10 =>
        m.testBit (((a.val + 1) * (v.val % 5) + b.val) % 5 +
          5 * ((v.val / 5 + (if a.val = 1 ∨ a.val = 2 then 1 else 0)) % 2))).toFinset).toFinset) =
    (rowsB ms).toFinset.image finsetOfMask := by
  ext S
  simp only [rowsB, List.mem_toFinset, Finset.mem_image, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨m, hm, a, ha, b, hb, rfl⟩
    refine ⟨_, ⟨m, hm, a, ha, b, hb, rfl⟩, ?_⟩
    ext u
    simp only [finsetOfMask, List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and]
    have ht := testBit_foldl_or (List.finRange 10) (fun v : Fin 10 =>
        m.testBit (((a.val + 1) * (v.val % 5) + b.val) % 5 +
          5 * ((v.val / 5 + (if a.val = 1 ∨ a.val = 2 then 1 else 0)) % 2))) 0 u
    simpa using ht
  · rintro ⟨k, ⟨m, hm, a, ha, b, hb, rfl⟩, rfl⟩
    refine ⟨m, hm, a, ha, b, hb, ?_⟩
    ext u
    simp only [finsetOfMask, List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and]
    have ht := testBit_foldl_or (List.finRange 10) (fun v : Fin 10 =>
        m.testBit (((a.val + 1) * (v.val % 5) + b.val) % 5 +
          5 * ((v.val / 5 + (if a.val = 1 ∨ a.val = 2 then 1 else 0)) % 2))) 0 u
    simpa using ht.symm

lemma subset_of_and_eq (p k : ℕ) (w : Fin 10) (h : (p &&& (k ||| (1 <<< w.val))) = p) :
    finsetOfMask p ⊆ insert w (finsetOfMask k) := by
  intro u hu
  simp only [finsetOfMask, List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and, Finset.mem_insert] at hu ⊢
  have hb : (p &&& (k ||| (1 <<< w.val))).testBit u.val = true := by rw [h]; exact hu
  simp only [Nat.testBit_and, Nat.testBit_or, Bool.and_eq_true, Bool.or_eq_true] at hb
  rcases hb.2 with hk | hw
  · exact Or.inr hk
  · left
    simp only [Nat.testBit_shiftLeft] at hw
    by_cases huw : u = w
    · exact huw
    · exfalso
      have hne : w.val ≠ u.val := fun he => huw (Fin.ext he.symm)
      by_cases hle : w.val ≤ u.val
      · cases hd : u.val - w.val with
        | zero => omega
        | succ d => simp [hle, hd, Nat.testBit_succ] at hw
      · simp [hle] at hw

theorem main_proof :
    let rows : List ℕ → Finset (Finset (Fin 10)) := fun ms =>
      (ms.flatMap fun m => (List.finRange 4).flatMap fun a => (List.finRange 5).map fun b =>
        ((List.finRange 10).filter fun v : Fin 10 =>
          m.testBit (((a.val + 1) * (v.val % 5) + b.val) % 5 +
            5 * ((v.val / 5 + (if a.val = 1 ∨ a.val = 2 then 1 else 0)) % 2))).toFinset).toFinset
    let H : SimpleGraph (Fin 10) := SimpleGraph.fromRel (fun a b : Fin 10 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (ℕ × ℕ)))
    ∀ I : Finset (Fin 10), (∀ a ∈ I, ∀ c ∈ I, ¬ H.Adj a c) →
      (∀ w : Fin 10, w ∉ I → ∃ a ∈ I, H.Adj a w) →
      I ∈ rows [50,116] ∧ ∀ w : Fin 10, w ∉ I →
        ∃ P ∈ rows [51,54,101,108], P ⊆ insert w I := by
  intro rows H I hind hmax
  let k := maskOfFinset I
  have hklt : k < 1024 := maskOfFinset_lt I
  have hk_is : isMaxIndepB k = true := by
    unfold isMaxIndepB
    rw [List.all_eq_true]
    intro a _
    by_cases ha : a ∈ I
    · have hka : k.testBit a.val = true := by simp [k, maskOfFinset_testBit, ha]
      simp only [hka, ↓reduceIte, List.all_eq_true]
      intro c _
      by_cases hc : c ∈ I
      · have hkc : k.testBit c.val = true := by simp [k, maskOfFinset_testBit, hc]
        have hna : adjB a c = false := by
          cases h : adjB a c
          · rfl
          · exact absurd ((adjB_iff a c).mp h) (hind a ha c hc)
        simp [hkc, hna]
      · have hkc : k.testBit c.val = false := by simp [k, maskOfFinset_testBit, hc]
        simp [hkc]
    · have hka : k.testBit a.val = false := by simp [k, maskOfFinset_testBit, ha]
      simp only [hka, Bool.false_eq_true, ↓reduceIte, List.any_eq_true]
      rcases hmax a ha with ⟨a', ha', hadj⟩
      refine ⟨a', List.mem_finRange a', ?_⟩
      simp [k, maskOfFinset_testBit, ha', (adjB_iff a' a).mpr hadj]
  have hall := checkAllB_true
  unfold checkAllB at hall
  have hkchk := List.all_eq_true.mp hall k (List.mem_range.mpr hklt)
  simp only [hk_is, ↓reduceIte, Bool.and_eq_true] at hkchk
  rcases hkchk with ⟨hneg, hpos⟩
  constructor
  · dsimp only [rows]; rw [rows_eq_image]
    refine Finset.mem_image.mpr ⟨k, ?_, maskOfFinset_eq_finset I⟩
    simpa [List.contains_iff_mem] using hneg
  · intro w hw
    have hwchk := List.all_eq_true.mp hpos w (List.mem_finRange w)
    have hkw : k.testBit w.val = false := by simp [k, maskOfFinset_testBit, hw]
    simp only [hkw, Bool.false_or, List.any_eq_true, beq_iff_eq] at hwchk
    rcases hwchk with ⟨p, hp, hsub⟩
    refine ⟨finsetOfMask p, ?_, ?_⟩
    · dsimp only [rows]; rw [rows_eq_image]
      exact Finset.mem_image.mpr ⟨p, List.mem_toFinset.mpr hp, rfl⟩
    · rw [← maskOfFinset_eq_finset I]
      exact subset_of_and_eq p k w hsub

end PEqualNP.Outside.L_meta_19152_aux

theorem PEqualNP.Outside.L_meta_19152 : (have x1 : List ℕ → Finset (Finset (Fin (10 : ℕ))) := fun (x1 : List ℕ) => (List.flatMap (fun (x2 : ℕ) => List.flatMap (fun (x3 : Fin (4 : ℕ)) => List.map (fun (x4 : Fin (5 : ℕ)) => (List.filter (fun (x5 : Fin (10 : ℕ)) => x2.testBit (((↑x3 + (1 : ℕ)) * (↑x5 % (5 : ℕ)) + ↑x4) % (5 : ℕ) + (5 : ℕ) * ((↑x5 / (5 : ℕ) + if ↑x3 = (1 : ℕ) ∨ ↑x3 = (2 : ℕ) then (1 : ℕ) else (0 : ℕ)) % (2 : ℕ)))) (List.finRange (10 : ℕ))).toFinset) (List.finRange (5 : ℕ))) (List.finRange (4 : ℕ))) x1).toFinset; have x2 : SimpleGraph (Fin (10 : ℕ)) := SimpleGraph.fromRel fun (x2 x3 : Fin (10 : ℕ)) => (↑x2, ↑x3) ∈ [((0 : ℕ), (1 : ℕ)), ((1 : ℕ), (2 : ℕ)), ((2 : ℕ), (3 : ℕ)), ((3 : ℕ), (4 : ℕ)), ((4 : ℕ), (0 : ℕ)), ((0 : ℕ), (5 : ℕ)), ((1 : ℕ), (6 : ℕ)), ((2 : ℕ), (7 : ℕ)), ((3 : ℕ), (8 : ℕ)), ((4 : ℕ), (9 : ℕ)), ((5 : ℕ), (7 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((9 : ℕ), (6 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((8 : ℕ), (5 : ℕ))]; ∀ (x3 : Finset (Fin (10 : ℕ))), (∀ x4 ∈ x3, ∀ x6 ∈ x3, ¬x2.Adj x4 x6) → (∀ x5 ∉ x3, ∃ x7 ∈ x3, x2.Adj x7 x5) → x3 ∈ x1 [(50 : ℕ), (116 : ℕ)] ∧ ∀ x6 ∉ x3, ∃ x8 ∈ x1 [(51 : ℕ), (54 : ℕ), (101 : ℕ), (108 : ℕ)], x8 ⊆ Insert.insert x6 x3)  := by
  exact PEqualNP.Outside.L_meta_19152_aux.main_proof
