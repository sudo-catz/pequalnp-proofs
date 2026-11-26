import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Remove the only two gates that can read the chosen vertex or its negation.
-- The shared sixteen gates see nine variables. On one slice the deleted gates
-- copy tapped wires. On the other they supply opposite constants.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4037_4
    (positiveFirst : ∀ (P M S : Circuit) (a b : ℕ), FanInTwo P → FanInTwo M → FanInTwo S →
      P.size + M.size + S.size = 16 → ¬ ∀ y : Fin 9 → Bool,
        let h := ([1,12,23,5,16,27,38,46,68,85,57,74] : List ℕ).any fun e => y (Fin.ofNat 9 (e / 10)) && y (Fin.ofNat 9 (e % 10))
        let w := P.wires ((false :: List.ofFn y) ++ [true])
        let l := M.wires (w ++ [w.getD a false])
        let r := M.wires (w ++ [true])
        S.eval (l ++ [l.getD b false]) = h ∧
          S.eval (r ++ [false]) = (h || y 0 || y 3 || y 4))
    (negativeFirst : ∀ (P M S : Circuit) (a b : ℕ), FanInTwo P → FanInTwo M → FanInTwo S →
      P.size + M.size + S.size = 16 → ¬ ∀ y : Fin 9 → Bool,
        let h := ([1,12,23,5,16,27,38,46,68,85,57,74] : List ℕ).any fun e => y (Fin.ofNat 9 (e / 10)) && y (Fin.ofNat 9 (e % 10))
        let w := P.wires ((false :: List.ofFn y) ++ [true])
        let l := M.wires (w ++ [w.getD a false])
        let r := M.wires (w ++ [false])
        S.eval (l ++ [l.getD b false]) = h ∧
          S.eval (r ++ [true]) = (h || y 0 || y 3 || y 4)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size = (18 : ℕ)
      → (∀ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (10 : ℕ))]) = (x4 (0 : Fin
      (10 : ℕ)) && x4 (1 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (2 : Fin (10 : ℕ)) || x4 (2 : Fin
      (10 : ℕ)) && x4 (3 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (4 : Fin (10 : ℕ)) || x4 (4 : Fin
      (10 : ℕ)) && x4 (0 : Fin (10 : ℕ)) || x4 (0 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)) || x4 (1 : Fin
      (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (3 : Fin
      (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (5 : Fin
      (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (7 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (9 : Fin
      (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (6 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (8 : Fin
      (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)))) → ¬∃ (x5 : Fin x1.gates.length) (x6 : Fin x1.gates.length), x5
      ≠ x6 ∧ (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (0 : ℕ) ∈ (x1.gates.get
      x5).inputs ∧ (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (10 : ℕ) ∈
      (x1.gates.get x6).inputs ∧ ∀ x7 ∈ [((0 : ℕ), x5), ((10 : ℕ), x6)], ∀ (x9 : Fin x1.gates.length),
      ((x1.gates.get x9).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x9).inputs.head? =
      Option.some x7.1 → x9 = x7.2) ∧ ((x1.gates.get x9).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not →
      x7.1 ∈ (x1.gates.get x9).inputs → x9 = x7.2) := by
  classical
  intro C legal count computes bad
  obtain ⟨j₀, j₁, diff, orOp, orUses, andOp, andUses, alone⟩ := bad
  let value (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
  let step (w : List Bool) (g : Gate) := w ++ [value g w]
  let low (y : Fin 9 → Bool) :=
    ([1,12,23,5,16,27,38,46,68,85,57,74] : List ℕ).any fun e =>
      y (Fin.ofNat 9 (e / 10)) && y (Fin.ofNat 9 (e % 10))
  let base (t : Bool) (y : Fin 9 → Bool) := (t :: List.ofFn y) ++ [!t]
  have slices (y : Fin 9 → Bool) :
      C.eval (base false y) = low y ∧ C.eval (base true y) = (low y || y 0 || y 3 || y 4) := by
    let x (t : Bool) : Fin 10 → Bool := Fin.cons t y
    have slice (t : Bool) := computes (x t)
    have input (t : Bool) : List.ofFn (x t) ++ [!(x t 0)] = base t y := by
      rw [List.ofFn_succ]
      rfl
    have h0 := slice false
    have h1 := slice true
    rw [input] at h0 h1
    change C.eval (base false y) = _ at h0
    change C.eval (base true y) = _ at h1
    constructor
    · refine h0.trans ?_
      change ((false && y 0) || (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) ||
        (y 3 && false) || (false && y 4) || (y 0 && y 5) || (y 1 && y 6) ||
        (y 2 && y 7) || (y 3 && y 8) || (y 4 && y 6) || (y 6 && y 8) ||
        (y 8 && y 5) || (y 5 && y 7) || (y 7 && y 4)) = _
      simp only [low,List.any_cons,List.any_nil,Bool.false_and,Bool.and_false,Bool.or_false,
        Bool.false_or,Bool.or_assoc]
      rfl
    · refine h1.trans ?_
      change ((true && y 0) || (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) ||
        (y 3 && true) || (true && y 4) || (y 0 && y 5) || (y 1 && y 6) ||
        (y 2 && y 7) || (y 3 && y 8) || (y 4 && y 6) || (y 6 && y 8) ||
        (y 8 && y 5) || (y 5 && y 7) || (y 7 && y 4)) = _
      simp only [low,List.any_cons,List.any_nil,Bool.true_and,Bool.and_true,Bool.or_false]
      change _ = (((y 0 && y 1) || ((y 1 && y 2) || ((y 2 && y 3) || ((y 0 && y 5) || ((y 1 && y 6) || ((y 2 && y 7) || ((y 3 && y 8) || ((y 4 && y 6) || ((y 6 && y 8) || ((y 8 && y 5) || ((y 5 && y 7) || (y 7 && y 4)))))))))))) || y 0 || y 3 || y 4)
      simp only [Bool.or_assoc,Bool.or_comm,Bool.or_left_comm]
  have extension (gs : List Gate) (w : List Bool) : ∃ t, gs.foldl step w = w ++ t := by
    induction gs generalizing w with
    | nil => exact ⟨[], by simp⟩
    | cons g gs ih =>
      obtain ⟨t, ht⟩ := ih (step w g)
      exact ⟨value g w :: t, by simpa [step,List.append_assoc] using ht⟩
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    obtain ⟨t,ht⟩ := extension gs w
    rw [ht,List.getD_append _ _ _ _ h]
  have keepsBase (w : List Bool) (y : Fin 9 → Bool) (t : Bool) (h : ∃ z, w = base t y ++ z) :
      w.getD 0 false = t ∧ w.getD 10 false = !t := by
    obtain ⟨z,rfl⟩ := h
    rw [List.getD_append _ _ _ _ (by simp [base] : 0 < (base t y).length),
        List.getD_append _ _ _ _ (by simp [base] : 10 < (base t y).length)]
    constructor
    · rfl
    · change (((t :: List.ofFn y) ++ [!t]).getD 10 false) = _
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp
  have output : C.output ≠ 0 ∧ C.output ≠ 10 := by
    let edge : Fin 9 → Bool := fun i => decide (i=0 ∨ i=1)
    let zero : Fin 9 → Bool := fun _ => false
    have out (y : Fin 9 → Bool) (i : ℕ) (e : C.output=i) (hi : i<11) :
        C.eval (base false y) = (base false y).getD i false := by
      change (C.gates.foldl step (base false y)).getD C.output false = _
      rw [e,keep _ _ _ (by simpa [base] using hi)]
    constructor
    · intro e
      have h := (out edge 0 e (by decide)).symm.trans (slices edge).1
      change false = low edge at h
      rw [show low edge = true by decide] at h
      contradiction
    · intro e
      have h := (out zero 10 e (by decide)).symm.trans (slices zero).1
      have one := (keepsBase (base false zero) zero false ⟨[],by simp⟩).2
      rw [one,show low zero = false by decide] at h
      contradiction
  let Quiet (g : Gate) := if g.op = .not then g.inputs.head? ≠ some 0 ∧ g.inputs.head? ≠ some 10
    else 0 ∉ g.inputs ∧ 10 ∉ g.inputs
  have quietIndex (j : Fin C.gates.length) (h₀ : j ≠ j₀) (h₁ : j ≠ j₁) : Quiet (C.gates.get j) := by
    have t₀ := alone (0,j₀) (by simp) j
    have t₁ := alone (10,j₁) (by simp) j
    by_cases h : (C.gates.get j).op = .not
    · simp only [Quiet,h,ite_true]
      exact ⟨fun e => h₀ (t₀.1 h e), fun e => h₁ (t₁.1 h e)⟩
    · simp only [Quiet,h,ite_false]
      exact ⟨fun e => h₀ (t₀.2 h e), fun e => h₁ (t₁.2 h e)⟩
  let Agree (w u : List Bool) := w.length = u.length ∧ ∀ i : ℕ, i ≠ 0 → i ≠ 10 →
    w.getD i false = u.getD i false
  have rawAgree (y : Fin 9 → Bool) : Agree (base true y) (base false y) := by
    constructor
    · simp [base]
    · intro i nz nt
      by_cases h : i < 10
      · change ((true :: List.ofFn y) ++ [false]).getD i false = ((false :: List.ofFn y) ++ [true]).getD i false
        rw [List.getD_append _ _ _ _ (by simpa using h),
            List.getD_append _ _ _ _ (by simpa using h)]
        cases i with
        | zero => contradiction
        | succ i => rfl
      · rw [List.getD_eq_default _ _ (by simp [base]; omega), List.getD_eq_default _ _ (by simp [base]; omega)]
  have pushAgree {w u : List Bool} {v z : Bool} (h : Agree w u) (same : v = z) :
      Agree (w ++ [v]) (u ++ [z]) := by
    rcases h with ⟨len, values⟩
    subst z
    constructor
    · simp [len]
    · intro i n₀ n₁
      by_cases hi : i < w.length
      · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (len ▸ hi), values i n₀ n₁]
      · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),len]
  have quietValue (g : Gate) (hq : Quiet g) (w u : List Bool) (h : Agree w u) : value g w = value g u := by
    by_cases hn : g.op = .not
    · simp only [Quiet,hn,ite_true] at hq
      change g.op.eval _ = g.op.eval _
      rw [hn]
      cases he : g.inputs with
      | nil => rfl
      | cons i is =>
        simp only [he,List.head?_cons] at hq
        change (!w.getD i false) = (!u.getD i false)
        rw [h.2 i (fun e => hq.1 (congrArg some e)) (fun e => hq.2 (congrArg some e))]
    · simp only [Quiet,hn,ite_false] at hq
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro i mem
      exact h.2 i (fun e => hq.1 (e ▸ mem)) (fun e => hq.2 (e ▸ mem))
  have runAgree (gs : List Gate) (hq : ∀ g ∈ gs, Quiet g) (w u : List Bool) (h : Agree w u) :
      Agree (gs.foldl step w) (gs.foldl step u) := by
    induction gs generalizing w u with
    | nil => exact h
    | cons g gs ih =>
      exact ih (fun f hh => hq f (by simp [hh])) _ _
        (pushAgree h (quietValue g (hq g List.mem_cons_self) w u h))
  have evalOr (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have evalAnd (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have tap (g : Gate) (r : ℕ) (pol : Bool) (which : g.op = if pol then .or else .and)
      (uses : r ∈ g.inputs) (arity : g.inputs.length ≤ 2) :
      ∃ a : ℕ, (∀ w : List Bool, w.getD r false = !pol → value g w = w.getD a false) ∧
        (∀ w : List Bool, w.getD r false = pol → value g w = pol) := by
    rcases g with ⟨op,ins⟩
    change op = _ at which
    subst op
    change r ∈ ins at uses
    change ins.length ≤ 2 at arity
    cases ins with
    | nil => simp at uses
    | cons i is =>
      cases is with
      | nil =>
        have ei : r = i := by simpa using uses
        subst i
        refine ⟨r, ?_, ?_⟩ <;> intro w eq <;> cases pol <;>
            simp only [value, evalAnd, evalOr, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              List.all_cons, List.all_nil, id_eq, Bool.false_eq_true, ite_false, ite_true, eq,
              Bool.not_true, Bool.not_false, Bool.and_true, Bool.or_false]
      | cons j js =>
        cases js with
        | cons k ks => simp at arity
        | nil =>
          have part : r = i ∨ r = j := by simpa using uses
          rcases part with rfl | rfl
          · refine ⟨j, ?_, ?_⟩ <;> intro w eq <;> cases pol <;>
              simp only [value, evalAnd, evalOr, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                List.all_cons, List.all_nil, id_eq, Bool.false_eq_true, ite_false, ite_true, eq,
                Bool.not_true, Bool.not_false, Bool.true_and, Bool.and_true, Bool.false_and, Bool.true_or,
                Bool.or_false, Bool.false_or]
          · refine ⟨i, ?_, ?_⟩ <;> intro w eq <;> cases pol <;>
              simp only [value, evalAnd, evalOr, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                List.all_cons, List.all_nil, id_eq, Bool.false_eq_true, ite_false, ite_true, eq,
                Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false, Bool.or_true, Bool.or_false]
  have segments (i j : Fin C.gates.length) (lt : i.val < j.val)
      (allQuiet : ∀ k : Fin C.gates.length, k ≠ i → k ≠ j → Quiet (C.gates.get k)) :
      ∃ p m s : List Gate,
        C.gates = p ++ C.gates.get i :: (m ++ C.gates.get j :: s) ∧
        (∀ g ∈ p, Quiet g) ∧ (∀ g ∈ m, Quiet g) ∧ (∀ g ∈ s, Quiet g) := by
    let p := C.gates.take i.val
    let tail := C.gates.drop (i.val+1)
    let gap := j.val-(i.val+1)
    let m := tail.take gap
    let s := C.gates.drop (j.val+1)
    have place : i.val+1+gap = j.val := by dsimp [gap]; omega
    have place' : i.val+1+(gap+1) = j.val+1 := by omega
    have inside : gap < tail.length := by
      simp only [tail,List.length_drop]
      have := j.isLt
      omega
    have cut (ls : List Gate) (n : ℕ) (hn : n < ls.length) :
        ls = ls.take n ++ ls[n] :: ls.drop (n+1) := by
      calc ls = ls.take n ++ ls.drop n := (List.take_append_drop _ _).symm
           _ = _ := by rw [List.drop_eq_getElem_cons hn]
    have second : tail = m ++ C.gates.get j :: s := by
      apply (cut tail gap inside).trans
      simp only [m,s,tail,List.getElem_drop,List.drop_drop,place,place']
      rfl
    refine ⟨p,m,s,(cut C.gates i.val i.isLt).trans
      (congrArg (fun z => p ++ C.gates.get i :: z) second),?_,?_,?_⟩
    · intro g mem
      obtain ⟨k,hk,e⟩ := List.mem_iff_getElem.mp mem
      have bounds : k < min i.val C.gates.length := by simpa [p] using hk
      have hg : C.gates[k] = g := by simpa [p] using e
      rw [← hg]
      apply allQuiet ⟨k, by omega⟩ <;> intro h <;> have h' := congrArg Fin.val h <;> dsimp at h' <;> omega
    · intro g mem
      obtain ⟨k,hk,e⟩ := List.mem_iff_getElem.mp mem
      have bounds : k < min gap (C.gates.length-(i.val+1)) := by simpa [m,tail] using hk
      have hg : C.gates[i.val+1+k] = g := by simpa [m,tail] using e
      rw [← hg]
      apply allQuiet ⟨_,by omega⟩ <;> intro h <;> have h' := congrArg Fin.val h <;> dsimp at h' <;> omega
    · intro g mem
      obtain ⟨k,hk,e⟩ := List.mem_iff_getElem.mp mem
      have bounds : k < C.gates.length-(j.val+1) := by simpa [s] using hk
      have hg : C.gates[j.val+1+k] = g := by simpa [s] using e
      rw [← hg]
      apply allQuiet ⟨_,by omega⟩ <;> intro h <;> have h' := congrArg Fin.val h <;> dsimp at h' <;> omega
  have noCore (pol : Bool) (P M S : Circuit) (a b : ℕ)
      (hp : FanInTwo P) (hm : FanInTwo M) (hs : FanInTwo S) (hn : P.size + M.size + S.size = 16) :
      ¬ ∀ y : Fin 9 → Bool,
        let w := P.wires (base false y)
        let l := M.wires (w ++ [w.getD a false])
        let r := M.wires (w ++ [pol])
        S.eval (l ++ [l.getD b false]) = low y ∧ S.eval (r ++ [!pol]) = (low y || y 0 || y 3 || y 4) := by
    cases pol
    · exact negativeFirst P M S a b hp hm hs hn
    · exact positiveFirst P M S a b hp hm hs hn
  have ordered (i j : Fin C.gates.length) (lt : i.val < j.val) (pol : Bool)
      (firstOp : (C.gates.get i).op = if pol then .or else .and)
      (secondOp : (C.gates.get j).op = if !pol then .or else .and)
      (firstUse : (if pol then 0 else 10) ∈ (C.gates.get i).inputs)
      (secondUse : (if pol then 10 else 0) ∈ (C.gates.get j).inputs)
      (other : ∀ k : Fin C.gates.length, k ≠ i → k ≠ j → Quiet (C.gates.get k)) : False := by
    obtain ⟨p,m,s,split,hqp,hqm,hqs⟩ := segments i j lt other
    let P : Circuit := ⟨p,0⟩
    let M : Circuit := ⟨m,0⟩
    let S : Circuit := ⟨s,C.output⟩
    have hp : FanInTwo P := by
      intro g mem
      change g ∈ p at mem
      exact legal g (by rw [split]; simp [mem])
    have hm : FanInTwo M := by
      intro g mem
      change g ∈ m at mem
      exact legal g (by rw [split]; simp [mem])
    have hs : FanInTwo S := by
      intro g mem
      change g ∈ s at mem
      exact legal g (by rw [split]; simp [mem])
    have n : P.size + M.size + S.size = 16 := by
      have lengths := congrArg List.length split
      change C.gates.length = 18 at count
      simp only [List.length_append,List.length_cons] at lengths
      change p.length + m.length + s.length = 16
      omega
    obtain ⟨a,copy₁,clamp₁⟩ := tap _ _ pol firstOp firstUse (legal _ (List.get_mem ..)).2
    obtain ⟨b,copy₂,clamp₂⟩ := tap _ _ (!pol) secondOp secondUse (legal _ (List.get_mem ..)).2
    have ports (t : Bool) (y : Fin 9 → Bool) (w : List Bool) (hw : ∃ z, w = base t y ++ z) :
        w.getD (if pol then 0 else 10) false = (if t then pol else !pol) ∧
        w.getD (if pol then 10 else 0) false = (if t then !pol else pol) := by
      have q := keepsBase w y t hw
      cases pol <;> cases t <;> first | exact q | exact q.symm
    have eRun (x : List Bool) (v z : Bool)
        (ha : value (C.gates.get i) (P.wires x) = v)
        (hb : value (C.gates.get j) (M.wires (P.wires x ++ [v])) = z) :
        C.eval x = S.eval (M.wires (P.wires x ++ [v]) ++ [z]) := by
      have eq := congrArg (fun gs : List Gate => (gs.foldl step x).getD C.output false) split
      simp only [List.foldl_append,List.foldl_cons] at eq
      change C.eval x = S.eval (M.wires (P.wires x ++ [value (C.gates.get i) (P.wires x)]) ++
        [value (C.gates.get j) (M.wires (P.wires x ++ [value (C.gates.get i) (P.wires x)]))]) at eq
      rw [ha,hb] at eq
      exact eq
    apply noCore pol P M S a b hp hm hs n
    intro y
    let w := P.wires (base false y)
    let u := P.wires (base true y)
    let l := M.wires (w ++ [w.getD a false])
    let r := M.wires (w ++ [pol])
    let t := M.wires (u ++ [pol])
    have extM (c v : Bool) : ∃ z, M.wires (P.wires (base c y) ++ [v]) = base c y ++ z := by
      obtain ⟨s₁,e₁⟩ := extension p (base c y)
      obtain ⟨s₂,e₂⟩ := extension m (P.wires (base c y) ++ [v])
      change P.wires (base c y) = _ at e₁
      change M.wires (P.wires (base c y) ++ [v]) = _ at e₂
      exact ⟨s₁ ++ v :: s₂,by rw [e₂,e₁]; simp [List.append_assoc]⟩
    have lo₁ := copy₁ w (ports false y w (extension p _)).1
    have hi₁ := clamp₁ u (ports true y u (extension p _)).1
    have lo₂ := copy₂ l (by simpa using (ports false y l (extM false _)).2)
    have hi₂ := clamp₂ t (ports true y t (extM true _)).2
    have lower := eRun (base false y) _ _ lo₁ lo₂
    have upper := eRun (base true y) _ _ hi₁ hi₂
    have startAgree : Agree u w := runAgree p hqp _ _ (rawAgree y)
    have mid : Agree t r := runAgree m hqm _ _ (pushAgree startAgree (rfl : pol = pol))
    have last := runAgree s hqs _ _ (pushAgree mid (rfl : (!pol) = !pol))
    have same : S.eval (t ++ [!pol]) = S.eval (r ++ [!pol]) := last.2 C.output output.1 output.2
    exact ⟨lower.symm.trans (slices y).1, same.symm.trans (upper.symm.trans (slices y).2)⟩
  by_cases forward : j₀.val < j₁.val
  · exact ordered j₀ j₁ forward true orOp andOp orUses andUses quietIndex
  · have unequal : j₀.val ≠ j₁.val := fun h => diff (Fin.ext h)
    exact ordered j₁ j₀ (by omega) false andOp orOp andUses orUses
      (fun k p q => quietIndex k q p)
