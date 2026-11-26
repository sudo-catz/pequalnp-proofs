import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.HeptadCover PEqualNP.GenericRejection

set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_9450_2
    (tests :
      let S := fun l : Fin 13 => if l = 1 then ∅ else singerLines3 l
      let row := fun P L : Finset (Fin 13) =>
        incidenceInput P L ++ [decide (1 ∈ P ∨ 2 ∈ P)]
      ∃ C : Circuit, C.size ≤ 58 ∧ IsAO2 27 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        27 ≤ C.output ∧ C.output < 27 + C.size ∧
        (∀ l, ∀ p ∈ S l, C.eval (row {p} {l}) = true) ∧
        ∀ P : Finset (Fin 13),
          (∀ p : Fin 13, (∀ l ∈ missLines S P, p ∉ S l) → p ∈ P) →
          C.eval (row P (missLines S P)) = false)
    (splitGate : ∀ (n : ℕ) (C : Circuit), IsAO2 n C → (∀ g ∈ C.gates, g.inputs.Nodup) →
      n ≤ C.output → C.output < n + C.size →
      ∃ (D : Circuit) (b : Bool) (u v : Fin (n + D.size)),
        u ≠ v ∧ D.size + 1 ≤ C.size ∧ IsAO2 n D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
        ∀ z : List Bool, z.length = n →
          let w := D.wires z
          (if b = true then w.getD u.val false || w.getD v.val false
           else w.getD u.val false && w.getD v.val false) = C.eval z) :
    (have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) =>
       ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), x3 ≠ (1 : Fin (13 : ℕ)) ∧
         (x2 = x3 ∨ x2 = x3 + (1 : Fin (13 : ℕ)) ∨ x2 = x3 + (3 : Fin (13 : ℕ)) ∨
          x2 = x3 + (9 : Fin (13 : ℕ))) ∧
         x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true;
     ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Bool) (x4 : Fin ((27 : ℕ) + x2.size))
       (x5 : List (Fin ((27 : ℕ) + x2.size))),
       x5 ≠ [] ∧ (x4 :: x5).Nodup ∧ x2.size + x5.length ≤ (58 : ℕ) ∧
       PEqualNP.TopForm.IsAO2 (27 : ℕ) x2 ∧ (∀ x6 ∈ x2.gates, x6.inputs.Nodup) ∧
       ∀ (x6 : Fin (26 : ℕ) → Bool),
         Minimal x1 x6 ∨ Maximal (fun (x7 : Fin (26 : ℕ) → Bool) => ¬x1 x7) x6 →
         have x8 : List Bool := x2.wires (List.ofFn x6 ++ [x6 (1 : Fin (26 : ℕ)) || x6 (2 : Fin (26 : ℕ))]);
         (if x3 = Bool.true then
            (x4 :: x5).any fun (x9 : Fin ((27 : ℕ) + x2.size)) => x8.getD (↑x9) Bool.false
          else (x4 :: x5).all fun (x9 : Fin ((27 : ℕ) + x2.size)) => x8.getD (↑x9) Bool.false) = Bool.true ↔
           x1 x6) := by
  classical
  intro F
  let S := fun l : Fin 13 => if l = 1 then ∅ else singerLines3 l
  let row := fun P L : Finset (Fin 13) =>
    incidenceInput P L ++ [decide (1 ∈ P ∨ 2 ∈ P)]
  let vec := fun P L : Finset (Fin 13) =>
    Fin.append (fun p => decide (p ∈ P)) (fun l => decide (l ∈ L))
  obtain ⟨C, size, ao, nodup, low, high, pos, neg⟩ := tests
  change ∀ l, ∀ p ∈ S l, C.eval (row {p} {l}) = true at pos
  change ∀ P : Finset (Fin 13),
    (∀ p : Fin 13, (∀ l ∈ missLines S P, p ∉ S l) → p ∈ P) →
    C.eval (row P (missLines S P)) = false at neg
  have leftBit (P L : Finset (Fin 13)) (p : Fin 13) :
      vec P L (Fin.castAdd 13 p) = decide (p ∈ P) := Fin.append_left _ _ _
  have rightBit (P L : Finset (Fin 13)) (l : Fin 13) :
      vec P L (Fin.natAdd 13 l) = decide (l ∈ L) := Fin.append_right _ _ _
  have incident : ∀ p l : Fin 13,
      p ∈ S l ↔ l ≠ 1 ∧ (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) := by decide
  have occurs (P L : Finset (Fin 13)) :
      F (vec P L) ↔ ∃ p ∈ P, ∃ l ∈ L, p ∈ S l := by
    constructor
    · rintro ⟨p,l,hl,hi,hp,hy⟩
      exact ⟨p, by simpa only [leftBit, decide_eq_true_eq] using hp, l, by simpa only [rightBit, decide_eq_true_eq] using hy,
        (incident p l).mpr ⟨hl,hi⟩⟩
    · rintro ⟨p,hp,l,hl,hi⟩
      obtain ⟨hne,hr⟩ := (incident p l).mp hi
      exact ⟨p,l,hne,hr,by simpa only [leftBit, decide_eq_true_eq] using hp,by simpa only [rightBit, decide_eq_true_eq] using hl⟩
  have encode (P L : Finset (Fin 13)) :
      List.ofFn (vec P L) ++ [vec P L 1 || vec P L 2] = row P L := by
    have bits : List.ofFn (vec P L) = incidenceInput P L := List.ofFn_fin_append _ _
    have one : vec P L 1 = decide (1 ∈ P) := Fin.append_left _ _ (1 : Fin 13)
    have two : vec P L 2 = decide (2 ∈ P) := Fin.append_left _ _ (2 : Fin 13)
    rw [bits, one, two]
    simp [row]
  have order {P L Q T : Finset (Fin 13)} (points : P ⊆ Q) (lines : L ⊆ T) :
      vec P L ≤ vec Q T := by
    intro i
    refine Fin.addCases (motive := fun i => vec P L i ≤ vec Q T i) ?_ ?_ i
    · intro p
      rw [Bool.le_iff_imp]
      simpa only [leftBit, decide_eq_true_eq] using (@points p)
    · intro l
      rw [Bool.le_iff_imp]
      simpa only [rightBit, decide_eq_true_eq] using (@lines l)
  have check (P L : Finset (Fin 13))
      (boundary : Minimal F (vec P L) ∨ Maximal (fun x => ¬F x) (vec P L)) :
      C.eval (row P L) = true ↔ F (vec P L) := by
    rcases boundary with minimal | maximal
    · obtain ⟨p,hp,l,hl,hi⟩ := (occurs P L).mp minimal.1
      have yes := (occurs {p} {l}).mpr ⟨p,by simp,l,by simp,hi⟩
      have eqv := minimal.eq_of_ge yes (order (Finset.singleton_subset_iff.mpr hp)
        (Finset.singleton_subset_iff.mpr hl))
      apply iff_of_true _ minimal.1
      rw [← encode, eqv, encode]
      exact pos l p hi
    · let T := missLines S P
      let Q := Finset.univ.filter fun p => ∀ l ∈ T, p ∉ S l
      have points : P ⊆ Q := by
        intro p hp
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro l hl hi
        exact Finset.disjoint_left.mp (Finset.mem_filter.mp hl).2 hi hp
      have lines : L ⊆ T := by
        intro l hl
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, Finset.disjoint_left.mpr ?_⟩
        intro p hi hp
        exact maximal.1 ((occurs P L).mpr ⟨p,hp,l,hl,hi⟩)
      have fixed : missLines S Q = T := by
        ext l
        constructor
        · intro hl
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.disjoint_left.mpr
            (fun p hi hp => Finset.disjoint_left.mp (Finset.mem_filter.mp hl).2 hi (points hp))⟩
        · intro hl
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.disjoint_left.mpr
            (fun p hi hp => (Finset.mem_filter.mp hp).2 l hl hi)⟩
      have no : ¬ F (vec Q T) := by
        intro yes
        obtain ⟨p,hp,l,hl,hi⟩ := (occurs Q T).mp yes
        exact (Finset.mem_filter.mp hp).2 l hl hi
      have eqv := maximal.eq_of_le no (order points lines)
      have closed (p : Fin 13) (h : ∀ l ∈ missLines S Q, p ∉ S l) : p ∈ Q := by
        rw [fixed] at h
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      have off := neg Q closed
      rw [fixed] at off
      apply iff_of_false _ maximal.1
      rw [← encode, eqv, encode, off]
      decide
  obtain ⟨D,b,u,v,distinct,budget,dao,dnd,ports⟩ := splitGate 27 C ao nodup low high
  refine ⟨D,b,u,[v],by simp,by simp [distinct],by simpa using budget.trans size,dao,dnd,?_⟩
  intro x boundary
  let P := Finset.univ.filter fun p : Fin 13 => x (Fin.castAdd 13 p) = true
  let L := Finset.univ.filter fun l : Fin 13 => x (Fin.natAdd 13 l) = true
  have eqv : vec P L = x := by
    funext i
    refine Fin.addCases (motive := fun i => vec P L i = x i) ?_ ?_ i
    · intro p
      rw [leftBit]
      simp [P]
    · intro l
      rw [rightBit]
      simp [L]
  let z := List.ofFn x ++ [x 1 || x 2]
  have encoded : z = row P L := by
    simpa only [eqv, z] using encode P L
  have result : C.eval z = true ↔ F x := by
    rw [encoded]
    simpa only [eqv] using check P L (by simpa only [eqv] using boundary)
  have two := ports z (by simp [z])
  simp only [List.any_cons, List.any_nil, Bool.or_false, List.all_cons, List.all_nil, Bool.and_true]
  change (if b = true then (D.wires z).getD u.val false || (D.wires z).getD v.val false
    else (D.wires z).getD u.val false && (D.wires z).getD v.val false) = true ↔ F x
  rw [two]
  exact result
