import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_9063_2
    (geometry : ∀ P : Finset (Fin 13), P.card = 4 →
      (Fintype.card {l : Fin 13 // l ≠ 1 ∧ ∀ p ∈ P,
        ¬ (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9)}) ≤ 3)
    (synthesis : ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      C.size ≤ 58 ∧ 27 ≤ C.output ∧ C.output < 27 + C.size ∧
      PEqualNP.TopForm.IsAO2 27 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      let E := fun p l : Fin 13 => l ≠ 1 ∧ (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9)
      let run := fun (P L : Finset (Fin 13)) =>
        C.eval (List.ofFn (Fin.append (fun p => decide (p ∈ P)) (fun l => decide (l ∈ L))) ++
          [decide ((1 : Fin 13) ∈ P ∨ (2 : Fin 13) ∈ P)])
      (∀ p l, E p l → run {p} {l} = true) ∧
      ∀ A : Finset (Fin 13), A.card ≤ 3 →
        run A (Finset.univ.filter fun l => ∀ p ∈ A, ¬ E p l) = false ∧
        run (Finset.univ.filter fun p => ∀ l ∈ A, ¬ E p l) (insert 1 A) = false) :
    (have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), x3 ≠ (1 : Fin (13 : ℕ)) ∧ (x2 = x3 ∨ x2 = x3 + (1 : Fin (13 : ℕ)) ∨ x2 = x3 + (3 : Fin (13 : ℕ)) ∨ x2 = x3 + (9 : Fin (13 : ℕ))) ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (58 : ℕ) ∧ (27 : ℕ) ≤ x2.output ∧ x2.output < (27 : ℕ) + x2.size ∧ PEqualNP.TopForm.IsAO2 (27 : ℕ) x2 ∧ (∀ x3 ∈ x2.gates, x3.inputs.Nodup) ∧ ∀ (x3 : Fin (26 : ℕ) → Bool), Minimal x1 x3 ∨ Maximal (fun (x4 : Fin (26 : ℕ) → Bool) => ¬x1 x4) x3 → (x2.eval (List.ofFn x3 ++ [x3 (1 : Fin (26 : ℕ)) || x3 (2 : Fin (26 : ℕ))]) = Bool.true ↔ x1 x3)) := by
  classical
  let E := fun p l : Fin 13 => l ≠ 1 ∧ (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9)
  let row := fun (P L : Finset (Fin 13)) =>
    Fin.append (fun p => decide (p ∈ P)) (fun l => decide (l ∈ L))
  let F := fun x : Fin 26 → Bool => ∃ p l, E p l ∧
    x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
  let avoidL := fun A : Finset (Fin 13) =>
    Finset.univ.filter fun l => ∀ p ∈ A, ¬ E p l
  let avoidP := fun A : Finset (Fin 13) =>
    Finset.univ.filter fun p => ∀ l ∈ A, ¬ E p l
  obtain ⟨C, size, outputLo, outputHi, ao, nodup, hon, hoff⟩ := synthesis
  let run := fun P L : Finset (Fin 13) => C.eval (List.ofFn (row P L) ++
    [decide ((1 : Fin 13) ∈ P ∨ (2 : Fin 13) ∈ P)])
  change (∀ p l, E p l → run {p} {l} = true) at hon
  change ∀ A : Finset (Fin 13), A.card ≤ 3 →
    run A (avoidL A) = false ∧ run (avoidP A) (insert 1 A) = false at hoff
  have left (P L : Finset (Fin 13)) (p : Fin 13) :
      row P L (Fin.castAdd 13 p) = decide (p∈P) := Fin.append_left _ _ _
  have right (P L : Finset (Fin 13)) (l : Fin 13) :
      row P L (Fin.natAdd 13 l) = decide (l∈L) := Fin.append_right _ _ _
  have evalRow (P L : Finset (Fin 13)) :
      C.eval (List.ofFn (row P L) ++ [row P L 1 || row P L 2]) = run P L := by
    have e1 := left P L 1
    have e2 := left P L 2
    change row P L 1 = _ at e1
    change row P L 2 = _ at e2
    simp [run,e1,e2]
  have rowle {P L P' L' : Finset (Fin 13)} (hp : P ⊆ P') (hl : L ⊆ L') :
      row P L ≤ row P' L' := by
    intro v
    refine Fin.addCases (m := 13) (n := 13) ?_ ?_ v
    · intro p
      rw [left,left]
      by_cases h : p ∈ P
      · simp [h,hp h]
      · simp [h]
    · intro l
      rw [right,right]
      by_cases h : l ∈ L
      · simp [h,hl h]
      · simp [h]
  have edgeRow (P L : Finset (Fin 13)) :
      F (row P L) ↔ ∃ p ∈ P, ∃ l ∈ L, E p l := by
    change (∃ p l, E p l ∧ row P L (Fin.castAdd 13 p) = true ∧ row P L (Fin.natAdd 13 l) = true) ↔ _
    simp only [left, right, decide_eq_true_eq]
    constructor
    · rintro ⟨p,l,e,hp,hl⟩
      exact ⟨p,hp,l,hl,e⟩
    · rintro ⟨p,hp,l,hl,e⟩
      exact ⟨p,l,e,hp,hl⟩
  refine ⟨C,size,outputLo,outputHi,ao,nodup,?_⟩
  intro x hx
  have isF : (fun z : Fin 26 → Bool => ∃ p l : Fin 13, l ≠ 1 ∧
      (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧
      z (Fin.castAdd 13 p)=true ∧ z (Fin.natAdd 13 l)=true) = F := by
    funext z
    simp only [F,E,and_assoc]
  have atF (z : Fin 26 → Bool) : (∃ p l : Fin 13, l ≠ 1 ∧ (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧
      z (Fin.castAdd 13 p)=true ∧ z (Fin.natAdd 13 l)=true) = F z := congrFun isF z
  dsimp only at hx ⊢
  simp only [atF] at hx ⊢
  change Minimal F x ∨ Maximal (fun y => ¬ F y) x at hx
  change _ ↔ F x
  let P := Finset.univ.filter (fun p : Fin 13 => x (Fin.castAdd 13 p) = true)
  let L := Finset.univ.filter (fun l : Fin 13 => x (Fin.natAdd 13 l) = true)
  have ex : x = row P L := by
    funext v
    refine Fin.addCases (m := 13) (n := 13) ?_ ?_ v
    · intro p
      rw [left]
      simp [P]
    · intro l
      rw [right]
      simp [L]
  rcases hx with hpos | hneg
  · obtain ⟨p,hp,l,hl,he⟩ := (edgeRow P L).1 (ex ▸ hpos.1)
    have small : F (row {p} {l}) := (edgeRow _ _).2 ⟨p,by simp,l,by simp,he⟩
    have leq : row {p} {l} ≤ x := ex ▸
      rowle (Finset.singleton_subset_iff.mpr hp) (Finset.singleton_subset_iff.mpr hl)
    have eq := le_antisymm (hpos.2 small leq) leq
    exact iff_of_true (by rw [eq,evalRow]; exact hon p l he) hpos.1
  · have disj (p) (hp : p ∈ P) (l) (hl : l ∈ L) : ¬ E p l :=
      fun e => hneg.1 (ex ▸ (edgeRow _ _).2 ⟨p,hp,l,hl,e⟩)
    have classifies {Q B : Finset (Fin 13)} (hp : P ⊆ Q) (hl : L ⊆ B)
        (safe : ∀ p ∈ Q, ∀ l ∈ B, ¬ E p l) : x = row Q B := by
      have leq : x ≤ row Q B := ex ▸ rowle hp hl
      apply le_antisymm leq (hneg.2 ?_ leq)
      intro h
      obtain ⟨p,pq,l,lb,e⟩ := (edgeRow _ _).1 h
      exact safe p pq l lb e
    have rejected : C.eval (List.ofFn x ++ [x 1 || x 2]) = false := by
      by_cases sz : P.card ≤ 3
      · have eq : x = row P (avoidL P) := classifies (fun _ h => h)
          (fun l h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun p hp => disj p hp l h⟩)
          (fun p hp l hl => (Finset.mem_filter.mp hl).2 p hp)
        rw [eq,evalRow]
        exact (hoff _ sz).1
      · let A := L.erase 1
        obtain ⟨U, sub, u4⟩ := Finset.exists_subset_card_eq (show 4 ≤ P.card by omega)
        have ha : A.card ≤ 3 := by
          have geo := geometry U u4
          rw [Fintype.card_subtype] at geo
          apply le_trans (Finset.card_le_card ?_) geo
          intro l hl
          obtain ⟨h1,hL⟩ := Finset.mem_erase.mp hl
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1,
            fun p hu adj => disj p (sub hu) l hL ⟨h1,adj⟩⟩
        have eq : x = row (avoidP A) (insert 1 A) := classifies
          (fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            fun l hl => disj p hp l (Finset.mem_of_mem_erase hl)⟩)
          (fun l hl => by by_cases e : l=1 <;> simp [A,e,hl])
          (fun p hp l hl => by
            rcases Finset.mem_insert.mp hl with rfl | hm
            · exact fun e => e.1 rfl
            · exact (Finset.mem_filter.mp hp).2 l hm)
        rw [eq,evalRow]
        exact (hoff _ ha).2
    exact iff_of_false (fun h => Bool.false_ne_true (rejected.symm.trans h)) hneg.1
