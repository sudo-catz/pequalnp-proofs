import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.HeptadCover PEqualNP.GenericRejection
open PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
theorem PEqualNP.Outside.R_meta_8893_417
    (andCase : have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x2 : Finset (Fin (13 : ℕ))), (∀ x3 ∉ x2, ∃ x5 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x2, x3 ∈ PEqualNP.HeptadCover.singerLines3 x5) → ¬PEqualNP.GenericRejection.InNoLine PEqualNP.HeptadCover.singerLines3 x2 ∨ ¬PEqualNP.GenericRejection.InNoPencil PEqualNP.HeptadCover.singerLines3 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x2) → x1.eval (PEqualNP.GenericRejection.incidenceInput x2 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x2)) = Bool.false; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (63 : ℕ) → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 x2 → x1 x2 → (2 : ℕ) < x2.lineDeg (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) → (2 : ℕ) < x2.lineDeg (26 : ℕ) (Finset.range (13 : ℕ)) → (∀ (j a b : ℕ), x2.gates[j]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [a,b] } : PEqualNP.CircuitLowerBounds.Gate) → a ≠ b ∧ j ≤ x2.output - 26) → 26 ≤ x2.output → x2.output < 26 + x2.size → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x2.output - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x9 : ℕ) (x10 : ℕ) (x11 : ℕ) (x12 : ℕ), x2.gates[x9]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x10, x11] : PEqualNP.CircuitLowerBounds.Gate } ∧ (x12 = x10 ∨ x12 = x11) ∧ x1 { gates := x2.gates.set x9 { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x12] : PEqualNP.CircuitLowerBounds.Gate }, output := x2.output : PEqualNP.CircuitLowerBounds.Circuit })
    (orCase : have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x2 : Finset (Fin (13 : ℕ))), (∀ x3 ∉ x2, ∃ x5 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x2, x3 ∈ PEqualNP.HeptadCover.singerLines3 x5) → ¬PEqualNP.GenericRejection.InNoLine PEqualNP.HeptadCover.singerLines3 x2 ∨ ¬PEqualNP.GenericRejection.InNoPencil PEqualNP.HeptadCover.singerLines3 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x2) → x1.eval (PEqualNP.GenericRejection.incidenceInput x2 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x2)) = Bool.false; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (63 : ℕ) → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 x2 → x1 x2 → (2 : ℕ) < x2.lineDeg (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) → (2 : ℕ) < x2.lineDeg (26 : ℕ) (Finset.range (13 : ℕ)) → (∀ (j a b : ℕ), x2.gates[j]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [a,b] } : PEqualNP.CircuitLowerBounds.Gate) → a ≠ b ∧ j ≤ x2.output - 26) → 26 ≤ x2.output → x2.output < 26 + x2.size → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x2.output - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∃ (x9 : ℕ) (x10 : ℕ) (x11 : ℕ) (x12 : ℕ), x2.gates[x9]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x10, x11] : PEqualNP.CircuitLowerBounds.Gate } ∧ (x12 = x10 ∨ x12 = x11) ∧ x1 { gates := x2.gates.set x9 { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x12] : PEqualNP.CircuitLowerBounds.Gate }, output := x2.output : PEqualNP.CircuitLowerBounds.Circuit })
    : have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x2 : Finset (Fin (13 : ℕ))), (∀ x3 ∉ x2, ∃ x5 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x2, x3 ∈ PEqualNP.HeptadCover.singerLines3 x5) → ¬PEqualNP.GenericRejection.InNoLine PEqualNP.HeptadCover.singerLines3 x2 ∨ ¬PEqualNP.GenericRejection.InNoPencil PEqualNP.HeptadCover.singerLines3 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x2) → x1.eval (PEqualNP.GenericRejection.incidenceInput x2 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x2)) = Bool.false; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (63 : ℕ) → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 x2 → x1 x2 → (2 : ℕ) < x2.lineDeg (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) → (2 : ℕ) < x2.lineDeg (26 : ℕ) (Finset.range (13 : ℕ)) → ∃ (x9 : ℕ) (x10 : ℕ) (x11 : ℕ) (x12 : ℕ), x2.gates[x9]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x10, x11] : PEqualNP.CircuitLowerBounds.Gate } ∧ (x12 = x10 ∨ x12 = x11) ∧ x1 { gates := x2.gates.set x9 { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x12] : PEqualNP.CircuitLowerBounds.Gate }, output := x2.output : PEqualNP.CircuitLowerBounds.Circuit } := by
  classical
  dsimp only
  intro C mono small positive rejects manyLines manyPoints
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have prefixValue (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have lengths (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have pref (gs : List Gate) (n : ℕ) (w : List Bool) (i : ℕ)
      (hi : i < ((gs.take n).foldl step w).length) :
      (gs.foldl step w).getD i false = ((gs.take n).foldl step w).getD i false := by
    calc
      (gs.foldl step w).getD i false = ((gs.take n ++ gs.drop n).foldl step w).getD i false := by
        rw [List.take_append_drop]
      _ = _ := by
        rw [List.foldl_append]
        exact prefixValue _ _ _ hi
  have sameOutside (j : ℕ) (g : Gate) (w : List Bool) (hw : w.length = 26) (later : C.output < 26+j)
      (inside : j < C.gates.length) :
      ({gates := C.gates.set j g, output := C.output} : Circuit).eval w = C.eval w := by
    have hx : C.output < ((C.gates.take j).foldl step w).length := by
      rw [lengths, List.length_take, hw, Nat.min_eq_left (Nat.le_of_lt inside)]
      exact later
    have agree : (C.gates.set j g).take j = C.gates.take j := List.take_set_of_le (Nat.le_refl _)
    have hy : C.output < (((C.gates.set j g).take j).foldl step w).length := by rw [agree]; exact hx
    change ((C.gates.set j g).foldl step w).getD C.output false = (C.gates.foldl step w).getD C.output false
    rw [pref _ j w _ hy, pref C.gates j w _ hx, agree]
  have dupEval (j a : ℕ) (found : C.gates[j]? = some (⟨.and,[a,a]⟩ : Gate)) (w : List Bool) :
      ({gates := C.gates.set j ⟨.and,[a]⟩, output := C.output} : Circuit).eval w = C.eval w := by
    have inside := List.getElem?_eq_some_iff.mp found |>.1
    have old : C.gates = C.gates.take j ++ (⟨.and,[a,a]⟩ : Gate) :: C.gates.drop (j+1) := by
      calc
        C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop ..).symm
        _ = _ := by rw [List.drop_eq_getElem_cons inside, List.getElem?_eq_some_iff.mp found |>.2]
    have new : C.gates.set j (⟨.and,[a]⟩ : Gate) = C.gates.take j ++ (⟨.and,[a]⟩ : Gate) :: C.gates.drop (j+1) := by
      rw [List.set_eq_take_append_cons_drop, ite_eq_left inside]
    change ((C.gates.set j _).foldl step w).getD C.output false = (C.gates.foldl step w).getD C.output false
    conv_rhs => rw [old]
    rw [new, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
    have one (v : List Bool) : step v ⟨.and,[a]⟩ = step v ⟨.and,[a,a]⟩ := by
      have repeatBit (bit : Bool) : GateOp.and.eval [bit] = GateOp.and.eval [bit,bit] := by
        cases bit <;> rfl
      exact congrArg (fun b => v ++ [b]) (repeatBit (v.getD a false))
    rw [one]
  have inputLength (X Y : Finset (Fin 13)) : (incidenceInput X Y).length = 26 := by
    change ((List.ofFn fun p : Fin 13 => decide (p ∈ X)) ++
      (List.ofFn fun l : Fin 13 => decide (l ∈ Y))).length = 26
    simp only [List.length_append, List.length_ofFn]
  by_cases repeats : ∃ (j a : ℕ), C.gates[j]? = some (⟨.and,[a,a]⟩ : Gate)
  · obtain ⟨j,a,found⟩ := repeats
    refine ⟨j,a,a,a,found,Or.inl rfl,?_⟩
    intro X maxFalse degenerate
    rw [dupEval j a found]
    exact rejects X maxFalse degenerate
  by_cases tail : ∃ (j a b : ℕ), C.gates[j]? = some (⟨.and,[a,b]⟩ : Gate) ∧ C.output < 26+j
  · obtain ⟨j,a,b,found,later⟩ := tail
    refine ⟨j,a,b,a,found,Or.inl rfl,?_⟩
    intro X maxFalse degenerate
    have inside := List.getElem?_eq_some_iff.mp found |>.1
    rw [sameOutside j ⟨.and,[a]⟩ _ (inputLength _ _) later inside]
    exact rejects X maxFalse degenerate
  have normal (j a b : ℕ) (found : C.gates[j]? = some (⟨.and,[a,b]⟩ : Gate)) : a ≠ b ∧ j ≤ C.output-26 := by
    constructor
    · rintro rfl
      exact repeats ⟨j,a,found⟩
    · have h : ¬ C.output < 26+j := fun h => tail ⟨j,a,b,found,h⟩
      omega
  let zero := incidenceInput ({0} : Finset (Fin 13)) ({0} : Finset (Fin 13))
  let one := incidenceInput ({1} : Finset (Fin 13)) ({1} : Finset (Fin 13))
  have zlen : zero.length = 26 := inputLength _ _
  have olen : one.length = 26 := inputLength _ _
  have yesZero : (C.gates.foldl step zero).getD C.output false = true :=
    positive 0 0 (by decide +kernel)
  have yesOne : (C.gates.foldl step one).getD C.output false = true :=
    positive 1 1 (by decide +kernel)
  have different : ∀ i : Fin 26, (zero.getD i.val false && one.getD i.val false) = false := by
    decide +kernel
  have hlo : 26 ≤ C.output := by
    by_contra! h
    rw [prefixValue _ _ _ (by omega)] at yesZero
    rw [prefixValue _ _ _ (by omega)] at yesOne
    have absurd := different ⟨C.output,h⟩
    change (zero.getD C.output false && one.getD C.output false) = false at absurd
    rw [yesZero, yesOne] at absurd
    cases absurd
  have hhi : C.output < 26 + C.size := by
    by_contra! beyond
    have len := lengths C.gates zero
    have sz : C.size = C.gates.length := rfl
    rw [List.getD_eq_default _ _ (by omega)] at yesZero
    cases yesZero
  have idx : C.output-26 < C.gates.length := by
    have sz : C.size = C.gates.length := rfl
    omega
  have gateMem : gateAt C (C.output-26) ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ idx]
    exact List.getElem_mem idx
  rcases (mono _ gateMem).1 with h | h
  · exact andCase C mono small positive rejects manyLines manyPoints normal hlo hhi h
  · exact orCase C mono small positive rejects manyLines manyPoints normal hlo hhi h
