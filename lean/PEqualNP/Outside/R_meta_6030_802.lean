import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_6030_802
    (sparse : ∀ (C : Circuit) (k : Fin 12), FanInTwo C →
      (∀ g ∈ C.gates, g.op ≠ .not) → C.size ≤ 17 →
      ∃ x : Fin 10 → Bool, (List.ofFn x).count true ≤ 4 ∧
        let W := List.ofFn x ++ [x 0 && x 2]
        let U := W ++ [!W.getD k.val false]
        C.eval U ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)))
    (shorter : ∀ (A B : Circuit) (k : Fin 12) (v : Fin (13 + A.size)),
      FanInTwo A → FanInTwo B → (∀ g ∈ A.gates, g.op ≠ .not) →
      A.size + B.size ≤ 16 →
      ∃ x : Fin 10 → Bool,
        let W := List.ofFn x ++ [x 0 && x 2]
        let U := W ++ [!W.getD k.val false]
        let P := A.wires U
        B.eval (P ++ [!P.getD v false]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (∃ (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 : List PEqualNP.CircuitLowerBounds.Gate), x1.gates = x5 :: x6 ∧ x5.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x6 (0 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  have canonical : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (12 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (17 : ℕ) →       ∃ (x5 : Fin (10 : ℕ) → Bool),         have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ))];         x1.eval (x6 ++ [!x6.getD (↑x2) Bool.false]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x5) := by
    intro C k legal size
    by_cases none : ∀ g ∈ C.gates, g.op ≠ .not
    · obtain ⟨x, _, hx⟩ := sparse C k legal none size
      exact ⟨x, hx⟩
    · have split (gs : List Gate) (bad : ¬ ∀ g ∈ gs, g.op ≠ .not) :
          ∃ pre ins post, gs = pre ++ ⟨.not, ins⟩ :: post ∧ ∀ g ∈ pre, g.op ≠ .not := by
        induction gs with
        | nil => simp at bad
        | cons g gs ih =>
          by_cases hg : g.op = .not
          · obtain ⟨op, args⟩ := g
            change op = .not at hg
            subst op
            exact ⟨[], args, gs, rfl, by simp⟩
          · have rest : ¬ ∀ a ∈ gs, a.op ≠ .not := by
              intro good
              exact bad (fun a mem => (List.mem_cons.mp mem).elim (fun e => e ▸ hg) (good a))
            obtain ⟨pre, ins, post, eq, hp⟩ := ih rest
            exact ⟨g :: pre, ins, post, by simp [eq], fun a mem =>
              (List.mem_cons.mp mem).elim (fun e => e ▸ hg) (hp a)⟩
      obtain ⟨pre, ins, post, eq, hp⟩ := split C.gates none
      let A : Circuit := ⟨pre, 0⟩
      let B : Circuit := ⟨post, C.output⟩
      have la : FanInTwo A := by
        intro g h
        exact legal g (eq ▸ List.mem_append_left _ h)
      have lb : FanInTwo B := by
        intro g h
        exact legal g (eq ▸ List.mem_append_right _ (List.mem_cons_of_mem _ h))
      have cap : A.size + B.size ≤ 16 := by
        change pre.length + post.length ≤ 16
        change C.gates.length ≤ 17 at size
        rw [eq,List.length_append,List.length_cons] at size
        omega
      let capWire := 12 + pre.length
      let v : Fin (13 + A.size) := ⟨min (ins.headD capWire) capWire, by
        change min _ (12 + pre.length) < 13 + pre.length
        omega⟩
      obtain ⟨x, hx⟩ := shorter A B k v la lb hp cap
      refine ⟨x, ?_⟩
      let W := List.ofFn x ++ [x 0 && x 2]
      let U := W ++ [!W.getD k.val false]
      let step := fun (w : List Bool) (g : Gate) =>
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      have lengths (gs : List Gate) (z : List Bool) : (gs.foldl step z).length = z.length + gs.length := by
        induction gs generalizing z with
        | nil => simp
        | cons g gs ih =>
          rw [List.foldl_cons, ih]
          simp [step]
          omega
      have width : (A.wires U).length = 12 + pre.length := by
        change (pre.foldl step U).length = _
        rw [lengths]
        simp [U,W]
      have read : (ins.map fun i => (A.wires U).getD i false).headD false = (A.wires U).getD v false := by
        cases ins with
        | nil =>
          change false = (A.wires U).getD (min (12 + pre.length) (12 + pre.length)) false
          rw [min_self]
          rw [List.getD_eq_default _ _ (by omega)]
        | cons i rest =>
          change (A.wires U).getD i false = (A.wires U).getD (min i (12 + pre.length)) false
          by_cases bound : i ≤ 12 + pre.length
          · rw [min_eq_left bound]
          · rw [min_eq_right (le_of_lt (Nat.lt_of_not_ge bound)),
                List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      have same : C.eval U = B.eval (A.wires U ++ [!(A.wires U).getD v false]) := by
        unfold Circuit.eval Circuit.wires
        rw [eq,List.foldl_append,List.foldl_cons]
        change (post.foldl step (A.wires U ++ [!((ins.map fun i => (A.wires U).getD i false).headD false)])).getD C.output false =
          (post.foldl step (A.wires U ++ [!(A.wires U).getD v false])).getD C.output false
        rw [read]
      exact fun equal => hx (same.symm.trans equal)
  have transport :
      ∀ (n : ℕ) (C : Circuit) (p : Fin n → Fin n), FanInTwo C →
        ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧
          ∀ (x : Fin n → Bool) (tail : List Bool),
            D.eval (List.ofFn x ++ tail) = C.eval (List.ofFn (x ∘ p) ++ tail) := by
    intro n C p hfan
    let rename (i : ℕ) : ℕ := if hi : i < n then (p ⟨i, hi⟩).val else i
    have early (i : ℕ) (hi : i < n) : rename i < n := by simp [rename, hi]
    have late (i : ℕ) (hi : n ≤ i) : rename i = i := by simp [rename, Nat.not_lt.mpr hi]
    let mapGate (g : Gate) : Gate := ⟨g.op, g.inputs.map rename⟩
    let D : Circuit := ⟨C.gates.map mapGate, rename C.output⟩
    refine ⟨D, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      exact ⟨(hfan g' hg').1, by simpa [mapGate] using (hfan g' hg').2⟩
    · exact List.length_map mapGate
    have run (gs : List Gate) (x y : List Bool) (len : x.length = y.length)
        (lo : n ≤ x.length) (agree : ∀ i, y.getD (rename i) false = x.getD i false) :
        ∀ i, ((Circuit.mk (gs.map mapGate) 0).wires y).getD (rename i) false =
          ((Circuit.mk gs 0).wires x).getD i false := by
      induction gs generalizing x y with
      | nil => exact agree
      | cons g rest ih =>
        let b := g.op.eval (g.inputs.map fun i => x.getD i false)
        have next : (mapGate g).op.eval ((mapGate g).inputs.map fun i => y.getD i false) = b := by
          simp only [b, mapGate, List.map_map, Function.comp_def, agree]
        change ∀ i, ((Circuit.mk (rest.map mapGate) 0).wires (y ++ [_])).getD (rename i) false =
          ((Circuit.mk rest 0).wires (x ++ [b])).getD i false
        rw [next]
        apply ih _ _ (by simp [len]) (by simp; omega)
        intro i
        by_cases hi : i < x.length
        · have hy : rename i < y.length := by
            by_cases hn : i < n
            · have := early i hn
              omega
            · rw [late i (by omega)]
              omega
          rw [List.getD_append _ _ _ _ hy, List.getD_append _ _ _ _ hi]
          exact agree i
        · rw [late i (by omega), List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by omega), len]
    intro x tail
    apply run C.gates _ _ (by simp) (by simp) _ C.output
    intro i
    by_cases hi : i < n
    · have hx : rename i < (List.ofFn x).length := by simpa using early i hi
      have hy : i < (List.ofFn (x ∘ p)).length := by simpa using hi
      rw [List.getD_append _ _ _ _ hx, List.getD_append _ _ _ _ hy,
          List.getD_eq_getElem _ _ hx, List.getD_eq_getElem _ _ hy]
      simp only [List.getElem_ofFn, Function.comp_apply]
      congr 1
      apply Fin.ext
      exact dite_eq_left hi
    · rw [late i (by omega), List.getD_append_right _ _ _ _ (by simpa using Nat.not_lt.mp hi),
          List.getD_append_right _ _ _ _ (by simpa using Nat.not_lt.mp hi)]
      simp
  intro C p fits small first
  obtain ⟨g, gs, shape, hop⟩ := first
  let D : Circuit := ⟨gs, C.output⟩
  have df : FanInTwo D := fun h hh => fits h (shape ▸ List.mem_cons_of_mem g hh)
  have ds : D.size ≤ 17 := by
    change gs.length ≤ 17
    change C.gates.length ≤ 18 at small
    rw [shape, List.length_cons] at small
    omega
  let pre (x : Fin 10 → Bool) := List.ofFn x ++ [x 0 && x 2]
  let F (x : Fin 10 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  let read (k : Fin 12) (x : Fin 10 → Bool) := (pre x).getD k.val false
  let idx := g.inputs.headD 11
  let k : Fin 12 := if h : idx < 10 then ⟨(p ⟨idx,h⟩).val, by omega⟩ else ⟨min idx 11, by omega⟩
  have input (x : Fin 10 → Bool) :
      g.op.eval (g.inputs.map fun i => (List.ofFn (x ∘ p) ++ [x 0 && x 2]).getD i false) = !(read k x) := by
    rw [hop]
    let w := List.ofFn (x ∘ p) ++ [x 0 && x 2]
    have hw : w.length = 11 := by simp [w]
    have hp : (pre x).length = 11 := by simp [pre]
    have hfirst : GateOp.not.eval (g.inputs.map fun i => w.getD i false) = !(w.getD idx false) := by
      cases he : g.inputs with
      | nil =>
        change (!false) = !(w.getD idx false)
        rw [show idx = 11 by simp [idx,he], List.getD_eq_default _ _ (by omega)]
      | cons u us =>
        change (!(w.getD u false)) = !(w.getD idx false)
        rw [show idx = u by simp [idx, he]]
    change GateOp.not.eval (g.inputs.map fun i => w.getD i false) = _
    rw [hfirst]
    congr 1
    by_cases hi : idx < 10
    · have hpi : (p ⟨idx,hi⟩).val < (List.ofFn x).length := by simp
      simp only [read, k, dif_pos hi, w, pre]
      rw [List.getD_append _ _ _ _ (by simpa using hi), List.getD_append _ _ _ _ hpi,
        List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hpi]
      simp only [List.getElem_ofFn,Function.comp_apply]
    · by_cases e : idx = 10
      · simp [read,k,hi,e,w,pre]
      · have ge : 11 ≤ idx := by omega
        simp only [read,k,dif_neg hi,min_eq_right ge]
        rw [List.getD_eq_default _ _ (show w.length ≤ idx by omega), List.getD_eq_default _ _ (show (pre x).length ≤ 11 by omega)]
  obtain ⟨E, ef, sz, run⟩ := transport 10 D p df
  have bound := sz.le.trans ds
  obtain ⟨x, hx⟩ := canonical E k ef bound
  refine ⟨x, ?_⟩
  change C.eval (List.ofFn (x ∘ p) ++ [x 0 && x 2]) ≠ F x
  intro he
  apply hx
  change E.eval (List.ofFn x ++ [x 0 && x 2, !(read k x)]) = F x
  rw [run]
  have eqC : C.eval (List.ofFn (x ∘ p) ++ [x 0 && x 2]) =
      D.eval ((List.ofFn (x ∘ p) ++ [x 0 && x 2]) ++ [!(read k x)]) := by
    unfold Circuit.eval Circuit.wires
    rw [shape, List.foldl_cons, input x]
  rw [eqC, List.append_assoc] at he
  exact he
