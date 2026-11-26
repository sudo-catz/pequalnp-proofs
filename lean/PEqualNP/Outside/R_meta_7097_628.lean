import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.GenericRejection

-- The seven exact line stars pay for their point sums. The residual circuit may read
-- both pair sums and the four-point sum on every one of these lines. Pair (0,1)
-- is already the supplied input. Twenty preprocessing gates and fourteen final gates
-- surround the 28-gate search on lines 1 through 6, without moving a residual wire.
set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_7097_628
  (localSearch : let S := fun l : Fin 13 => ({l,l+1,l+3,l+9} : Finset (Fin 13))
     let feed := fun x : Fin 26 → Bool => List.ofFn x ++ ([0,7,8,9,10,11,12] : List (Fin 13)).flatMap (fun l =>
       let a := x (Fin.castAdd 13 l) || x (Fin.castAdd 13 (l+1))
       let b := x (Fin.castAdd 13 (l+3)) || x (Fin.castAdd 13 (l+9))
       [a,b,a || b])
     ∃ C : Circuit, Monotone2 C ∧ ReadsBack 47 C ∧ C.size ≤ 28 ∧ C.output < 47+C.size ∧
       (∀ l : Fin 13, 1 ≤ l.val → l.val ≤ 6 → ∀ p ∈ S l,
         C.eval (feed (fun i => decide (i=Fin.castAdd 13 p ∨ i=Fin.natAdd 13 l)))=true) ∧
       (∀ x : Fin 26 → Bool,
         let P := Finset.univ.filter (fun p : Fin 13 => x (Fin.castAdd 13 p)=true)
         let L := Finset.univ.filter (fun l : Fin 13 => x (Fin.natAdd 13 l)=true)
         IsFalseInput S P L → IsGeneric S 3 P L → C.eval (feed x)=false))
  (rowGeometry : let S := fun l : Fin 13 => ({l,l+1,l+3,l+9} : Finset (Fin 13))
     ∀ z ∈ ([(7,904),(13,2848),(19,708),(21,2720),(25,2656),(37,2440),(41,2370),(133,808)] : List (ℕ × ℕ)),
       ∀ m ∈ ([1,3,9] : List (Fin 13)), ∀ (t : Fin 13) (d : Bool),
         let bit := fun (a b : ℕ) (i : Fin 13) =>
           if d then b.testBit (-(m*i+t)).val else a.testBit (m*i+t).val
         let P := Finset.univ.filter (fun i => bit z.1 z.2 i=true)
         let L := Finset.univ.filter (fun i => bit z.2 z.1 i=true)
         IsFalseInput S P L ∧ IsGeneric S 3 P L) :
    ∃ (x1 : Fin (4 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 ∧     PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x2 ∧       x2.size ≤ (62 : ℕ) ∧         have x3 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x4 x5 : Fin (13 : ℕ)) => ∃ x6 ∈ x3, x4 = x5 + x6;         have x5 : Fin (26 : ℕ) := if ↑x1 = (1 : ℕ) then (1 : Fin (26 : ℕ)) else if ↑x1 = (3 : ℕ) then (14 : Fin (26 : ℕ)) else (13 : Fin (26 : ℕ));         have x6 : Bool := Decidable.decide (↑x1 = (0 : ℕ));         have x7 : (Fin (26 : ℕ) → Bool) → Fin (27 : ℕ) → Bool := fun (x7 : Fin (26 : ℕ) → Bool) (x8 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (if x6 = Bool.true then x7 (0 : Fin (26 : ℕ)) && x7 x5 else x7 (0 : Fin (26 : ℕ)) || x7 x5) x7 x8;         have x8 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))];         have x9 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x9 : ℕ × ℕ) (x10 x11 : Fin (13 : ℕ)) (x12 : Bool) =>           have x13 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x13 x14 : ℕ) (x15 : Fin (13 : ℕ)) => if x12 = Bool.true then x14.testBit ↑(-(x10 * x15 + x11)) else x13.testBit ↑(x10 * x15 + x11);           Fin.append (x13 x9.1 x9.2) (x13 x9.2 x9.1);         (∀ (x10 x11 : Fin (13 : ℕ)), x4 x10 x11 → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x2 (x7 fun (x13 : Fin (26 : ℕ)) => Decidable.decide (x13 = Fin.castAdd (13 : ℕ) x10 ∨ x13 = Fin.natAdd (13 : ℕ) x11)) = Bool.true) ∧ ∀ x10 ∈ x8, ∀ x12 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∀ (x14 : Fin (13 : ℕ)) (x15 : Bool), PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x2 (x7 (x9 x10 x12 x14 x15)) = Bool.false := by
  let S := fun l : Fin 13 => ({l,l+1,l+3,l+9} : Finset (Fin 13))
  let outside := ([0,7,8,9,10,11,12] : List (Fin 13))
  let feed := fun x : Fin 26 → Bool => List.ofFn x ++ ([0,7,8,9,10,11,12] : List (Fin 13)).flatMap (fun l =>
       let a := x (Fin.castAdd 13 l) || x (Fin.castAdd 13 (l+1))
       let b := x (Fin.castAdd 13 (l+3)) || x (Fin.castAdd 13 (l+9))
       [a,b,a || b])
  let initial := fun x : Fin 26 → Bool => List.ofFn (Fin.lastCases (x 0 || x 1) x)
  let starSum := fun (x : Fin 26 → Bool) (l : Fin 13) =>
    (x (Fin.castAdd 13 l) || x (Fin.castAdd 13 (l+1))) ||
    (x (Fin.castAdd 13 (l+3)) || x (Fin.castAdd 13 (l+9)))
  obtain ⟨C,mono,back,small,valid,localOn,localOff⟩ := localSearch
  let OR := fun (a b : ℕ) => (⟨.or,[a,b]⟩ : Gate)
  let AND := fun (a b : ℕ) => (⟨.and,[a,b]⟩ : Gate)
  let step := fun (w : List Bool) (g : Gate) => w++[g.op.eval (g.inputs.map fun i => w.getD i false)]
  have stepOr (w : List Bool) (a b : ℕ) : step w (OR a b)=w++[w.getD a false || w.getD b false] := by
    change w++[([w.getD a false,w.getD b false] : List Bool).any id]=_
    simp only [List.any_cons,List.any_nil,id_eq,Bool.or_false]
  have stepAnd (w : List Bool) (a b : ℕ) : step w (AND a b)=w++[w.getD a false && w.getD b false] := by
    change w++[([w.getD a false,w.getD b false] : List Bool).all id]=_
    simp only [List.all_cons,List.all_nil,id_eq,Bool.and_true]
  have sizeFold (gs : List Gate) (w : List Bool) : (gs.foldl step w).length=w.length+gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons,ih]; simp [step]; omega
  have kept (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j<w.length) :
      (gs.foldl step w).getD j false=w.getD j false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih => rw [List.foldl_cons,ih _ (by simp [step];omega)]; exact List.getD_append _ _ _ _ hj
  let B := fun (n : ℕ) (gs : List Gate) => ∀ i : Fin gs.length, ∀ w ∈ (gs.get i).inputs, w<n+i.val
  have backIff (n : ℕ) (D : Circuit) : ReadsBack n D ↔ B n D.gates := by
    constructor
    · intro h i w hw; apply h i.val (by exact i.isLt) w
      change w ∈ (D.gates.getD i.val ⟨.or,[]⟩).inputs
      rw [List.getD_eq_getElem _ _ i.isLt]; exact hw
    · intro h i hi w hw
      have ilt : i<D.gates.length := hi
      change w ∈ (D.gates.getD i ⟨.or,[]⟩).inputs at hw
      rw [List.getD_eq_getElem _ _ ilt] at hw
      exact h ⟨i,ilt⟩ w hw
  have cat (n : ℕ) (u v : List Gate) (a : B n u) (b : B (n+u.length) v) : B n (u++v) := by
    intro i w hw
    have hi := i.isLt
    change w ∈ (u++v)[i.val].inputs at hw
    by_cases hu : i.val<u.length
    · rw [List.getElem_append_left hu] at hw
      exact a ⟨i.val,hu⟩ w hw
    · have hv : i.val-u.length<v.length := by simp at hi; omega
      rw [List.getElem_append_right (by omega)] at hw
      have h := b ⟨i.val-u.length,hv⟩ w hw
      change w<n+u.length+(i.val-u.length) at h
      omega
  let pre : List Gate := [OR 3 9,OR 26 27,OR 7 8,OR 10 3,OR 29 30,OR 8 9,OR 11 4,OR 32 33,OR 9 10,OR 12 5,OR 35 36,OR 10 11,OR 0 6,OR 38 39,OR 11 12,OR 1 7,OR 41 42,OR 12 0,OR 2 8,OR 44 45]
  have lenPre : pre.length=20 := rfl
  have preBack : B 27 pre := by
    change ∀ i : Fin 20, ∀ w ∈ (pre.get i).inputs, w<27+i.val
    dsimp only [pre,OR]; decide
  have preMono : ∀ g ∈ pre, g.op∈({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2 := by
    intro g hg
    simp only [pre,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [OR]
  have initEq (x : Fin 26→Bool) : initial x=List.ofFn x++[x 0 || x 1] := by
    change List.ofFn (Fin.lastCases (x 0 || x 1) x) = _
    rw [List.ofFn_succ']
    simp only [Fin.lastCases_castSucc,Fin.lastCases_last,List.concat_eq_append]
  have readRaw (x : Fin 26→Bool) (v : List Bool) (w : Fin 26) :
      (List.ofFn x++v).getD w.val false = x w := by
    have hw : w.val<(List.ofFn x).length := by simp
    rw [List.getD_append _ _ _ _ hw,List.getD_eq_getElem _ _ hw,List.getElem_ofFn hw]
  have readAux (x : Fin 26→Bool) (v : List Bool) (w : ℕ) :
      (List.ofFn x++v).getD (26+w) false=v.getD w false := by
    rw [List.getD_append_right _ _ _ _ (by simp)];simp
  have evaluated (x : Fin 26→Bool) : pre.foldl step (initial x)=feed x := by
    rw [initEq]
    let R := List.ofFn x
    let t0 := x 0 || x 1
    let t1 := x 3 || x 9
    have e0 : step (R++[t0]) (OR 3 9)=R++[t0,t1] := by
      rw [stepOr]
      have u3 : (R++[t0]).getD 3 false=x 3 := readRaw x _ (3 : Fin 26)
      have u9 : (R++[t0]).getD 9 false=x 9 := readRaw x _ (9 : Fin 26)
      rw [u3,u9,List.append_assoc]
      rfl
    let t2 := t0 || t1
    have e1 : step (R++[t0,t1]) (OR 26 27)=R++[t0,t1,t2] := by
      rw [stepOr]
      have u26 : (R++[t0,t1]).getD 26 false=t0 := (readAux x _ 0).trans (by rfl)
      have u27 : (R++[t0,t1]).getD 27 false=t1 := (readAux x _ 1).trans (by rfl)
      rw [u26,u27,List.append_assoc]
      rfl
    let t3 := x 7 || x 8
    have e2 : step (R++[t0,t1,t2]) (OR 7 8)=R++[t0,t1,t2,t3] := by
      rw [stepOr]
      have u7 : (R++[t0,t1,t2]).getD 7 false=x 7 := readRaw x _ (7 : Fin 26)
      have u8 : (R++[t0,t1,t2]).getD 8 false=x 8 := readRaw x _ (8 : Fin 26)
      rw [u7,u8,List.append_assoc]
      rfl
    let t4 := x 10 || x 3
    have e3 : step (R++[t0,t1,t2,t3]) (OR 10 3)=R++[t0,t1,t2,t3,t4] := by
      rw [stepOr]
      have u10 : (R++[t0,t1,t2,t3]).getD 10 false=x 10 := readRaw x _ (10 : Fin 26)
      have u3 : (R++[t0,t1,t2,t3]).getD 3 false=x 3 := readRaw x _ (3 : Fin 26)
      rw [u10,u3,List.append_assoc]
      rfl
    let t5 := t3 || t4
    have e4 : step (R++[t0,t1,t2,t3,t4]) (OR 29 30)=R++[t0,t1,t2,t3,t4,t5] := by
      rw [stepOr]
      have u29 : (R++[t0,t1,t2,t3,t4]).getD 29 false=t3 := (readAux x _ 3).trans (by rfl)
      have u30 : (R++[t0,t1,t2,t3,t4]).getD 30 false=t4 := (readAux x _ 4).trans (by rfl)
      rw [u29,u30,List.append_assoc]
      rfl
    let t6 := x 8 || x 9
    have e5 : step (R++[t0,t1,t2,t3,t4,t5]) (OR 8 9)=R++[t0,t1,t2,t3,t4,t5,t6] := by
      rw [stepOr]
      have u8 : (R++[t0,t1,t2,t3,t4,t5]).getD 8 false=x 8 := readRaw x _ (8 : Fin 26)
      have u9 : (R++[t0,t1,t2,t3,t4,t5]).getD 9 false=x 9 := readRaw x _ (9 : Fin 26)
      rw [u8,u9,List.append_assoc]
      rfl
    let t7 := x 11 || x 4
    have e6 : step (R++[t0,t1,t2,t3,t4,t5,t6]) (OR 11 4)=R++[t0,t1,t2,t3,t4,t5,t6,t7] := by
      rw [stepOr]
      have u11 : (R++[t0,t1,t2,t3,t4,t5,t6]).getD 11 false=x 11 := readRaw x _ (11 : Fin 26)
      have u4 : (R++[t0,t1,t2,t3,t4,t5,t6]).getD 4 false=x 4 := readRaw x _ (4 : Fin 26)
      rw [u11,u4,List.append_assoc]
      rfl
    let t8 := t6 || t7
    have e7 : step (R++[t0,t1,t2,t3,t4,t5,t6,t7]) (OR 32 33)=R++[t0,t1,t2,t3,t4,t5,t6,t7,t8] := by
      rw [stepOr]
      have u32 : (R++[t0,t1,t2,t3,t4,t5,t6,t7]).getD 32 false=t6 := (readAux x _ 6).trans (by rfl)
      have u33 : (R++[t0,t1,t2,t3,t4,t5,t6,t7]).getD 33 false=t7 := (readAux x _ 7).trans (by rfl)
      rw [u32,u33,List.append_assoc]
      rfl
    let t9 := x 9 || x 10
    have e8 : step (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8]) (OR 9 10)=R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9] := by
      rw [stepOr]
      have u9 : (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8]).getD 9 false=x 9 := readRaw x _ (9 : Fin 26)
      have u10 : (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8]).getD 10 false=x 10 := readRaw x _ (10 : Fin 26)
      rw [u9,u10,List.append_assoc]
      rfl
    let t10 := x 12 || x 5
    have e9 : step (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9]) (OR 12 5)=R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10] := by
      rw [stepOr]
      have u12 : (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9]).getD 12 false=x 12 := readRaw x _ (12 : Fin 26)
      have u5 : (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9]).getD 5 false=x 5 := readRaw x _ (5 : Fin 26)
      rw [u12,u5,List.append_assoc]
      rfl
    let t11 := t9 || t10
    have e10 : step (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10]) (OR 35 36)=R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11] := by
      rw [stepOr]
      have u35 : (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10]).getD 35 false=t9 := (readAux x _ 9).trans (by rfl)
      have u36 : (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10]).getD 36 false=t10 := (readAux x _ 10).trans (by rfl)
      rw [u35,u36,List.append_assoc]
      rfl
    let t12 := x 10 || x 11
    have e11 : step (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11]) (OR 10 11)=R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12] := by
      rw [stepOr]
      have u10 : (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11]).getD 10 false=x 10 := readRaw x _ (10 : Fin 26)
      have u11 : (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11]).getD 11 false=x 11 := readRaw x _ (11 : Fin 26)
      rw [u10,u11,List.append_assoc]
      rfl
    let t13 := x 0 || x 6
    have e12 : step (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12]) (OR 0 6)=R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13] := by
      rw [stepOr]
      have u0 : (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12]).getD 0 false=x 0 := readRaw x _ (0 : Fin 26)
      have u6 : (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12]).getD 6 false=x 6 := readRaw x _ (6 : Fin 26)
      rw [u0,u6,List.append_assoc]
      rfl
    let t14 := t12 || t13
    have e13 : step (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13]) (OR 38 39)=R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14] := by
      rw [stepOr]
      have u38 : (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13]).getD 38 false=t12 := (readAux x _ 12).trans (by rfl)
      have u39 : (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13]).getD 39 false=t13 := (readAux x _ 13).trans (by rfl)
      rw [u38,u39,List.append_assoc]
      rfl
    let t15 := x 11 || x 12
    have e14 : step (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14]) (OR 11 12)=R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15] := by
      rw [stepOr]
      have u11 : (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14]).getD 11 false=x 11 := readRaw x _ (11 : Fin 26)
      have u12 : (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14]).getD 12 false=x 12 := readRaw x _ (12 : Fin 26)
      rw [u11,u12,List.append_assoc]
      rfl
    let t16 := x 1 || x 7
    have e15 : step (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15]) (OR 1 7)=R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16] := by
      rw [stepOr]
      have u1 : (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15]).getD 1 false=x 1 := readRaw x _ (1 : Fin 26)
      have u7 : (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15]).getD 7 false=x 7 := readRaw x _ (7 : Fin 26)
      rw [u1,u7,List.append_assoc]
      rfl
    let t17 := t15 || t16
    have e16 : step (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16]) (OR 41 42)=R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17] := by
      rw [stepOr]
      have u41 : (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16]).getD 41 false=t15 := (readAux x _ 15).trans (by rfl)
      have u42 : (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16]).getD 42 false=t16 := (readAux x _ 16).trans (by rfl)
      rw [u41,u42,List.append_assoc]
      rfl
    let t18 := x 12 || x 0
    have e17 : step (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17]) (OR 12 0)=R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18] := by
      rw [stepOr]
      have u12 : (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17]).getD 12 false=x 12 := readRaw x _ (12 : Fin 26)
      have u0 : (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17]).getD 0 false=x 0 := readRaw x _ (0 : Fin 26)
      rw [u12,u0,List.append_assoc]
      rfl
    let t19 := x 2 || x 8
    have e18 : step (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18]) (OR 2 8)=R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19] := by
      rw [stepOr]
      have u2 : (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18]).getD 2 false=x 2 := readRaw x _ (2 : Fin 26)
      have u8 : (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18]).getD 8 false=x 8 := readRaw x _ (8 : Fin 26)
      rw [u2,u8,List.append_assoc]
      rfl
    let t20 := t18 || t19
    have e19 : step (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19]) (OR 44 45)=R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20] := by
      rw [stepOr]
      have u44 : (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19]).getD 44 false=t18 := (readAux x _ 18).trans (by rfl)
      have u45 : (R++[t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19]).getD 45 false=t19 := (readAux x _ 19).trans (by rfl)
      rw [u44,u45,List.append_assoc]
      rfl
    change pre.foldl step (R++[t0])=feed x
    simp only [pre,List.foldl_cons,List.foldl_nil,e0,e1,e2,e3,e4,e5,e6,e7,e8,e9,e10,e11,e12,e13,e14,e15,e16,e17,e18,e19]
    rfl
  have feedLen (x : Fin 26→Bool) : (feed x).length=47 := by
    change (List.ofFn x++_).length=47
    rw [List.length_append,List.length_ofFn];rfl
  let start : Circuit := ⟨pre++C.gates,C.output⟩
  have wiresStart (x : Fin 26→Bool) : start.wires (initial x)=C.wires (feed x) := by
    change (pre++C.gates).foldl step (initial x)=C.gates.foldl step (feed x)
    rw [List.foldl_append,evaluated]
  let Model := fun (D : Circuit) (s : ℕ) (h : (Fin 26→Bool)→Bool) =>
    Monotone2 D ∧ ReadsBack 27 D ∧ D.size=s ∧ D.output<27+D.size ∧
    (∀ x,D.eval (initial x)=h x) ∧
    (∀ x w, w<47 → (D.wires (initial x)).getD w false=(feed x).getD w false)
  have baseModel : Model start (C.size+20) (fun x=>C.eval (feed x)) := by
    have sz : start.size=C.size+20 := by
      change (pre++C.gates).length=C.gates.length+20
      rw [List.length_append,lenPre,Nat.add_comm]
    refine ⟨?_,?_,sz,?_,?_,?_⟩
    · intro g hg; rcases List.mem_append.mp hg with hp|hc
      · exact preMono g hp
      · exact mono g hc
    · apply (backIff 27 start).mpr
      exact cat 27 pre C.gates preBack (by simpa only [lenPre] using (backIff 47 C).mp back)
    · change C.output<27+start.size; omega
    · intro x; change (start.wires (initial x)).getD C.output false=_
      rw [wiresStart];rfl
    · intro x w hw; rw [wiresStart]
      exact kept C.gates (feed x) w (by rw [feedLen];exact hw)
  have addLine (D : Circuit) (s : ℕ) (h : (Fin 26→Bool)→Bool) (good : Model D s h)
      (room : 47≤27+D.size) (a b : Fin 47) :
      ∃ E, Model E (s+2) (fun x => h x || ((feed x).getD a.val false && (feed x).getD b.val false)) := by
    obtain ⟨dm,db,ds,doBound,correct,reads⟩ := good
    let extra : List Gate := [AND a.val b.val,OR D.output (27+D.size)]
    let E : Circuit := ⟨D.gates++extra,27+D.size+1⟩
    have es : E.size=D.size+2 := by
      change (D.gates++extra).length=D.gates.length+2
      rw [List.length_append];rfl
    have eb : B (27+D.size) extra := by
      intro i w hw
      have hi := i.isLt
      change i.val<2 at hi
      have casesI : i.val=0 ∨ i.val=1 := by omega
      rcases casesI with hi|hi
      · have eq : i=(⟨0,by change 0<2;decide⟩ : Fin extra.length) := Fin.ext hi
        subst i; simp [extra,AND] at hw
        rcases hw with rfl|rfl <;> simp <;> omega
      · have eq : i=(⟨1,by change 1<2;decide⟩ : Fin extra.length) := Fin.ext hi
        subst i; simp [extra,OR] at hw
        rcases hw with rfl|rfl <;> simp <;> omega
    have wdLen (x : Fin 26→Bool) : (D.wires (initial x)).length=27+D.size := by
      change (D.gates.foldl step (initial x)).length=_
      rw [sizeFold];change (initial x).length + D.gates.length=27+D.gates.length
      rw [show (initial x).length=27 from List.length_ofFn]
    have after (x : Fin 26→Bool) : E.wires (initial x)=
        D.wires (initial x)++[(feed x).getD a.val false && (feed x).getD b.val false,
          h x || ((feed x).getD a.val false && (feed x).getD b.val false)] := by
      let v := (feed x).getD a.val false && (feed x).getD b.val false
      let W := D.wires (initial x)
      have hfirst : step W (AND a.val b.val)=W++[v] := by
        rw [stepAnd]
        simp only [W,v,reads x a.val a.isLt,reads x b.val b.isLt]
      have firstOut : (W++[v]).getD (27+D.size) false=v := by
        have sizeW : W.length=27+D.size := wdLen x
        rw [List.getD_append_right _ _ _ _ (by omega),sizeW,Nat.sub_self];rfl
      have prevOut : (W++[v]).getD D.output false=h x := by
        rw [List.getD_append _ _ _ _ (show D.output<W.length by simpa only [W,wdLen] using doBound)]
        exact correct x
      change ((D.gates++extra).foldl step (initial x))=W++[v,h x || v]
      rw [List.foldl_append]
      change step (step W (AND a.val b.val)) (OR D.output (27+D.size))=_
      rw [hfirst,stepOr,prevOut,firstOut,List.append_assoc]
      rfl
    refine ⟨E,?_,?_,es.trans (by omega),?_,?_,?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hd|he
      · exact dm g hd
      · simp [extra] at he
        rcases he with rfl|rfl <;> simp [AND,OR]
    · apply (backIff 27 E).mpr
      exact cat 27 D.gates extra ((backIff 27 D).mp db) eb
    · change 27+D.size+1 < 27+E.size; omega
    · intro x;change (E.wires (initial x)).getD (27+D.size+1) false=_
      rw [after,List.getD_append_right _ _ _ _ (by rw [wdLen];omega),wdLen]
      rw [show 27+D.size+1-(27+D.size)=1 by omega];rfl
    · intro x w hw
      rw [after,List.getD_append _ _ _ _ (by rw [wdLen];omega)]
      exact reads x w hw
  let term := fun (x : Fin 26→Bool) (p : Fin 47 × Fin 47) =>
    (feed x).getD p.1.val false && (feed x).getD p.2.val false
  have assemble (ps : List (Fin 47 × Fin 47)) :
      ∃ D, Model D (C.size+20+2*ps.length) (fun x => C.eval (feed x) || ps.any (term x)) := by
    induction ps with
    | nil =>
      refine ⟨start,?_⟩
      simpa only [List.length_nil,Nat.mul_zero,Nat.add_zero,List.any_nil,Bool.or_false] using baseModel
    | cons p ps ih =>
      obtain ⟨D,ok⟩ := ih
      have sz := ok.2.2.1
      obtain ⟨E,em,eb,es,eo,ev,er⟩ := addLine D _ _ ok (by omega) p.1 p.2
      refine ⟨E,em,eb,?_,eo,?_,er⟩
      · simp only [List.length_cons];omega
      · intro x; rw [ev]
        change (C.eval (feed x) || ps.any (term x) || term x p)=(C.eval (feed x) || (p::ps).any (term x))
        rw [List.any_cons]
        ac_rfl
  let items : List (Fin 47 × Fin 47) := [(13,28),(20,31),(21,34),(22,37),(23,40),(24,43),(25,46)]
  have linesCorrect (x : Fin 26→Bool) : items.any (term x)=
      outside.any (fun l => x (Fin.natAdd 13 l) && starSum x l) := by
    have ln (l : Fin 13) : (feed x).getD (13+l.val) false=x (Fin.natAdd 13 l) :=
      readRaw x _ (Fin.natAdd 13 l)
    have l0 : (feed x).getD 13 false=x (Fin.natAdd 13 (0:Fin 13)) := ln 0
    have l7 : (feed x).getD 20 false=x (Fin.natAdd 13 (7:Fin 13)) := ln 7
    have l8 : (feed x).getD 21 false=x (Fin.natAdd 13 (8:Fin 13)) := ln 8
    have l9 : (feed x).getD 22 false=x (Fin.natAdd 13 (9:Fin 13)) := ln 9
    have l10 : (feed x).getD 23 false=x (Fin.natAdd 13 (10:Fin 13)) := ln 10
    have l11 : (feed x).getD 24 false=x (Fin.natAdd 13 (11:Fin 13)) := ln 11
    have l12 : (feed x).getD 25 false=x (Fin.natAdd 13 (12:Fin 13)) := ln 12
    have s0 : (feed x).getD 28 false=starSum x 0 := (readAux x _ 2).trans (by rfl)
    have s7 : (feed x).getD 31 false=starSum x 7 := (readAux x _ 5).trans (by rfl)
    have s8 : (feed x).getD 34 false=starSum x 8 := (readAux x _ 8).trans (by rfl)
    have s9 : (feed x).getD 37 false=starSum x 9 := (readAux x _ 11).trans (by rfl)
    have s10 : (feed x).getD 40 false=starSum x 10 := (readAux x _ 14).trans (by rfl)
    have s11 : (feed x).getD 43 false=starSum x 11 := (readAux x _ 17).trans (by rfl)
    have s12 : (feed x).getD 46 false=starSum x 12 := (readAux x _ 20).trans (by rfl)
    simp only [items,outside,List.any_cons,List.any_nil,term]
    change (((feed x).getD 13 false && (feed x).getD 28 false) || (((feed x).getD 20 false && (feed x).getD 31 false) || (((feed x).getD 21 false && (feed x).getD 34 false) || (((feed x).getD 22 false && (feed x).getD 37 false) || (((feed x).getD 23 false && (feed x).getD 40 false) || (((feed x).getD 24 false && (feed x).getD 43 false) || (((feed x).getD 25 false && (feed x).getD 46 false) || false))))))) = _
    rw [l0,l7,l8,l9,l10,l11,l12,s0,s7,s8,s9,s10,s11,s12]
  obtain ⟨D,dm,db,ds,_,ev,_⟩ := assemble items
  have finalValue (x : Fin 26→Bool) : D.eval (initial x)=
      (C.eval (feed x) || outside.any (fun l => x (Fin.natAdd 13 l) && starSum x l)) :=
    (ev x).trans (congrArg (fun v => C.eval (feed x) || v) (linesCorrect x))
  have inSum (x : Fin 26→Bool) (l : Fin 13) :
      starSum x l=true ↔ ∃ p ∈ S l, x (Fin.castAdd 13 p)=true := by
    simp only [starSum,S,Bool.or_eq_true,Finset.mem_insert,Finset.mem_singleton]
    aesop
  have others : ∀ l : Fin 13, ¬ (1≤l.val ∧ l.val≤6) → l∈outside := by decide
  refine ⟨(1 : Fin 4),D,dm,db,?_,?_,?_⟩
  · have n : items.length=7 := rfl;rw [n] at ds;omega
  · intro p l inc
    let x := fun i : Fin 26 => decide (i=Fin.castAdd 13 p ∨ i=Fin.natAdd 13 l)
    change D.eval (initial x)=true
    rw [finalValue,Bool.or_eq_true]
    have member : p∈S l := by
      obtain ⟨v,hv,hp⟩ := inc
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with rfl|rfl|rfl|rfl <;> subst p <;> simp [S]
    by_cases localLine : 1≤l.val ∧ l.val≤6
    · exact Or.inl (localOn l localLine.1 localLine.2 p member)
    · apply Or.inr
      exact List.any_eq_true.mpr ⟨l,others l localLine,by
        simp only [Bool.and_eq_true]
        exact ⟨by simp [x],(inSum x l).mpr ⟨p,member,by simp [x]⟩⟩⟩
  · intro z hz m hm t dual
    let bit := fun (a b : ℕ) (i : Fin 13) =>
      if dual then b.testBit (-(m*i+t)).val else a.testBit (m*i+t).val
    let x : Fin 26→Bool := Fin.append (bit z.1 z.2) (bit z.2 z.1)
    let P := Finset.univ.filter (fun p : Fin 13 => x (Fin.castAdd 13 p)=true)
    let L := Finset.univ.filter (fun l : Fin 13 => x (Fin.natAdd 13 l)=true)
    have hrow : IsFalseInput S P L ∧ IsGeneric S 3 P L := by
      simpa only [P,L,x,Fin.append_left,Fin.append_right,S,bit] using rowGeometry z hz m hm t dual
    change D.eval (initial x)=false
    rw [finalValue,show C.eval (feed x)=false from localOff x hrow.1 hrow.2,Bool.false_or]
    apply Bool.eq_false_iff.mpr
    intro hit
    obtain ⟨l,_,hl⟩ := List.any_eq_true.mp hit
    have both : x (Fin.natAdd 13 l)=true ∧ starSum x l=true := by simpa only [Bool.and_eq_true] using hl
    obtain ⟨lineOn,pointOn⟩ := both
    obtain ⟨p,mem,yes⟩ := (inSum x l).mp pointOn
    have ml : l∈L := Finset.mem_filter.mpr ⟨Finset.mem_univ _,lineOn⟩
    have mp : p∈P := Finset.mem_filter.mpr ⟨Finset.mem_univ _,yes⟩
    exact Finset.disjoint_left.mp (hrow.1 l ml) mem mp
