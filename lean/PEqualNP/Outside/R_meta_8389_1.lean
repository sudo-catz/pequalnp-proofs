import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_8389_1
    (core : ∃ (n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit) (M : Finset (Fin n)),
      (∀ i, i ∈ M ↔ i ∉ S i) ∧
      (∀ i, i ∈ S i ∨ S i = ∅ ∨ ∀ j, i ∉ S j) ∧
      (∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) ∧
      Monotone2 C ∧
      (∀ x : Fin (n + n) → Bool, circuitFun (n + n) C x = true ↔
        ∃ p l, p ∈ S l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true) ∧
      C.size + 1 + M.card <
        (∑ i, (S i).card) + n)
    (attach : ∀ (n : ℕ) (M : Finset (Fin n)) (C : Circuit), Monotone2 C →
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size + 2 * M.card ∧
        ∀ x : Fin (n + n) → Bool, circuitFun (n + n) D x = true ↔
          circuitFun (n + n) C x = true ∨
            ∃ i ∈ M, x (Fin.castAdd n i) = true ∧ x (Fin.natAdd n i) = true) :
    ∃ (x1 : ℕ) (x2 : Fin x1 → Finset (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 : Fin x1), x4 ∈ x2 x4) ∧ (∀ (x4 x5 : Fin x1), x4 ≠ x5 → (x2 x4 ∩ x2 x5).card ≤ (1 : ℕ)) ∧ PEqualNP.MetaComplexity.Monotone2 x3 ∧ (∀ (x4 x5 : Fin x1), x4 ∈ x2 x5 → (PEqualNP.MetaComplexity.circuitFun (x1 + x1) x3 fun (x7 : Fin (x1 + x1)) => Decidable.decide (x7 = Fin.castAdd x1 x4 ∨ x7 = Fin.natAdd x1 x5)) = Bool.true) ∧ (∀ (x4 : Finset (Fin x1)), (PEqualNP.MetaComplexity.circuitFun (x1 + x1) x3 fun (x5 : Fin (x1 + x1)) => Fin.addCases (fun (x6 : Fin x1) => Decidable.decide (x6 ∈ x4)) (fun (x6 : Fin x1) => Decidable.decide (∀ x7 ∈ x4, x7 ∉ x2 x6)) x5) = Bool.false) ∧ x3.size + (1 : ℕ) < ∑ x4 : Fin x1, (x2 x4).card + x1 := by
  classical
  obtain ⟨n, S, C, M, hM, hprivate, hfour, hmono, hcore, hbudget⟩ := core
  let T := fun i => insert i (S i)
  obtain ⟨D, hDmono, hsize, heval⟩ := attach n M C hmono
  have inside {i j w : Fin n} (hne : i ≠ j) (hi : S i ≠ ∅)
      (hwi : w ∈ T i) (hwj : w ∈ T j) : w ∈ S i := by
    rcases Finset.mem_insert.mp hwi with eqwi | hw
    · subst w
      rcases hprivate i with h | h | h
      · exact h
      · exact (hi h).elim
      · rcases Finset.mem_insert.mp hwj with e | e
        · exact (hne e).elim
        · exact (h j e).elim
    · exact hw
  have whole (x : Fin (n + n) → Bool) : circuitFun (n+n) D x = true ↔
      ∃ p l, p ∈ T l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true := by
    rw [heval, hcore]
    constructor
    · rintro (⟨p, l, h, hp, hl⟩ | ⟨i, _, hp, hl⟩)
      · exact ⟨p, l, Finset.mem_insert_of_mem h, hp, hl⟩
      · exact ⟨i, i, Finset.mem_insert_self _ _, hp, hl⟩
    · rintro ⟨p, l, h, hp, hl⟩
      rcases Finset.mem_insert.mp h with eqpl | h
      · subst p
        by_cases hold : l ∈ S l
        · exact Or.inl ⟨l, l, hold, hp, hl⟩
        · exact Or.inr ⟨l, (hM l).2 hold, hp, hl⟩
      · exact Or.inl ⟨p, l, h, hp, hl⟩
  have addOne (i : Fin n) : (T i).card = (S i).card + (if i ∈ M then 1 else 0) := by
    by_cases hi : i ∈ S i <;> simp [T, hM, hi]
  have cardSum : (∑ i, (T i).card) = (∑ i, (S i).card) + M.card := by
    simp_rw [addOne]
    simp [Finset.sum_add_distrib]
  refine ⟨n, T, D, ?_, ?_, hDmono, ?_, ?_, ?_⟩
  · intro i
    exact Finset.mem_insert_self _ _
  · intro i j hne
    by_cases hi : S i = ∅
    · exact (Finset.card_le_card (Finset.inter_subset_left :
        T i ∩ T j ⊆ T i)).trans (by simp [T, hi])
    by_cases hj : S j = ∅
    · exact (Finset.card_le_card (Finset.inter_subset_right :
        T i ∩ T j ⊆ T j)).trans (by simp [T, hj])
    apply le_trans (Finset.card_le_card ?_) (hfour i j hne)
    intro w hw
    obtain ⟨hw₁, hw₂⟩ := Finset.mem_inter.mp hw
    exact Finset.mem_inter.mpr ⟨inside hne hi hw₁ hw₂, inside hne.symm hj hw₂ hw₁⟩
  · intro p l he
    apply (whole _).2
    exact ⟨p, l, he, by simp, by simp⟩
  · intro A
    let x : Fin (n+n) → Bool := Fin.addCases (fun p => decide (p ∈ A))
      (fun l => decide (∀ p ∈ A, p ∉ T l))
    change circuitFun (n+n) D x = false
    cases hx : circuitFun (n+n) D x with
    | false => rfl
    | true =>
      obtain ⟨p, l, h, hp, hl⟩ := (whole x).1 hx
      have hpa : p ∈ A := by simpa [x] using hp
      have hla : ∀ q ∈ A, q ∉ T l := by simpa only [x, Fin.addCases_right, decide_eq_true_eq] using hl
      exact (hla p hpa h).elim
  · change C.size + 1 + M.card < (∑ i, (S i).card) + n at hbudget
    rw [cardSum]
    omega
