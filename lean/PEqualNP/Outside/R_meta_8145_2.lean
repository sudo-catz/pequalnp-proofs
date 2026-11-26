import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.ReadTwo

set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.R_meta_8145_2
    (common : let offsets : Finset (Fin 13) := {0, 1, 3, 9}
    let correct := fun C : Circuit => Monotone2 C ∧ ReadsBack 26 C ∧
      ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, p - l ∈ offsets ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
    ∀ C : Circuit, correct C → (∀ D : Circuit, correct D → C.size ≤ D.size) →
    (∃ (j : Fin C.gates.length) (u : Fin 26), (u = 0 ∨ u = 1) ∧
      (C.gates.get j).op = GateOp.and ∧
      ∀ w ∈ (C.gates.get j).inputs, orp C 26 u.val w) → 64 ≤ C.size)
    (opposite : let offsets : Finset (Fin 13) := {0, 1, 3, 9}
    let correct := fun C : Circuit => Monotone2 C ∧ ReadsBack 26 C ∧
      ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, p - l ∈ offsets ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
    ∀ C : Circuit, correct C → (∀ D : Circuit, correct D → C.size ≤ D.size) →
    (∃ (j : Fin C.gates.length) (a b : ℕ), (C.gates.get j).op = GateOp.and ∧
      ((C.gates.get j).inputs = [a,b] ∨ (C.gates.get j).inputs = [b,a]) ∧
      orp C 26 0 a ∧ ¬ orp C 26 1 a ∧ orp C 26 1 b ∧ ¬ orp C 26 0 b) → 64 ≤ C.size) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ ∀ (x4 : Fin (26 : ℕ) → Bool), x3.eval (List.ofFn x4) = Bool.true ↔ x2 x4; have x4 : Fin (26 : ℕ) → Fin (26 : ℕ) → Fin (26 : ℕ) → Bool := fun (x4 x5 x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = x4 ∨ x6 = x5); have x5 : PEqualNP.CircuitLowerBounds.Circuit → Fin (26 : ℕ) → Fin (26 : ℕ) → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : Fin (26 : ℕ)) => ∃ (x8 : Fin x5.gates.length), (x5.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x5.wires (List.ofFn (x4 x6 x7))).getD ((26 : ℕ) + ↑x8) Bool.false = Bool.true; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x3 x6 → (∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit), x3 x8 → x6.size ≤ x8.size) → x5 x6 (0 : Fin (26 : ℕ)) (1 : Fin (26 : ℕ)) → (64 : ℕ) ≤ x6.size := by
  intro offsets target correct pair fires C hC least lit
  let appendGate (ws : List Bool) (g : Gate) : List Bool :=
    ws ++ [g.op.eval (g.inputs.map fun w => ws.getD w false)]

  have run_length (gs : List Gate) (ws : List Bool) :
      (gs.foldl appendGate ws).length = ws.length + gs.length := by
    induction gs generalizing ws with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih, List.length_cons]
      simp only [appendGate, List.length_append, List.length_singleton]
      omega

  have at_snoc (ws : List Bool) (b : Bool) (i : ℕ) :
      (ws ++ [b]).getD i false = if i = ws.length then b else ws.getD i false := by
    split_ifs with h
    · subst i
      simp
    · by_cases hl : i < ws.length
      · exact List.getD_append _ _ _ _ hl
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

  let traced (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) : Prop :=
    ∃ k : Fin n, x k = true ∧ orp C n k.val w

  have prefix_paths (n : ℕ) (C : Circuit) (x : Fin n → Bool)
      (hm : Monotone2 C) (hb : ReadsBack n C)
      (absent : ¬ ∃ j : Fin C.gates.length, (C.gates.get j).op = GateOp.and ∧
        ∀ w ∈ (C.gates.get j).inputs, traced C n x w)
      (pre : List Gate) (hpre : ∃ tail, C.gates = pre ++ tail) :
      ∀ w, (pre.foldl appendGate (List.ofFn x)).getD w false = true → traced C n x w := by
    induction pre using List.reverseRecOn with
    | nil =>
      intro w h
      change (List.ofFn x).getD w false = true at h
      by_cases hw : w < n
      · refine ⟨⟨w, hw⟩, ?_, Relation.ReflTransGen.refl⟩
        simpa only [List.getD_eq_getElem _ _ (by simpa using hw : w < (List.ofFn x).length),
          List.getElem_ofFn] using h
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hw)] at h
        contradiction
    | append_singleton pre g ih =>
      obtain ⟨tail, ht⟩ := hpre
      have hall : C.gates = pre ++ g :: tail := by simpa [List.append_assoc] using ht
      have hj : pre.length < C.gates.length := by simp [hall]
      let j : Fin C.gates.length := ⟨pre.length, hj⟩
      have hjg : C.gates.get j = g := by
        change C.gates[pre.length] = g
        simp [hall, List.getElem_append_right]
      have atj : gateAt C pre.length = g := by
        change C.gates.getD pre.length ⟨.or, []⟩ = g
        rw [List.getD_eq_getElem _ _ hj]
        exact hjg
      have old := ih ⟨g :: tail, hall⟩
      let ws := pre.foldl appendGate (List.ofFn x)
      have hlen : ws.length = n + pre.length := by simp [ws, run_length]
      intro w h
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at h
      change (ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]).getD w false = true at h
      rw [at_snoc, hlen] at h
      by_cases hw : w = n + pre.length
      · subst w
        simp only [↓reduceIte] at h
        have hops : g.op = GateOp.and ∨ g.op = GateOp.or := by
          simpa using (hm g (by simp [hall])).1
        rcases hops with hand | hor
        · have hon : ∀ i ∈ g.inputs, ws.getD i false = true := by
            rw [hand] at h
            change (g.inputs.map fun i => ws.getD i false).all id = true at h
            simpa [List.all_eq_true] using h
          exact (absent ⟨j, hjg ▸ hand, by rw [hjg]; exact fun i hi => old i (hon i hi)⟩).elim
        · have hon : ∃ i ∈ g.inputs, ws.getD i false = true := by
            rw [hor] at h
            change (g.inputs.map fun i => ws.getD i false).any id = true at h
            simpa [List.any_eq_true] using h
          obtain ⟨i, hi, hv⟩ := hon
          obtain ⟨k, hk, path⟩ := old i hv
          have hi' : i ∈ (gateAt C pre.length).inputs := atj ▸ hi
          exact ⟨k, hk, path.tail ⟨hb pre.length hj i hi', pre.length, rfl, ⟨hj, atj ▸ hor⟩, hi'⟩⟩
      · exact old w (by simpa only [ite_eq_right hw] using h)
  have trace : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1 → Bool), PEqualNP.MetaComplexity.Monotone2 x2 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x2 → (∃ (x6 : Fin x2.gates.length), (x2.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x2.wires (List.ofFn x3)).getD (x1 + ↑x6) Bool.false = Bool.true) → ∃ (x7 : Fin x2.gates.length), (x2.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∀ x8 ∈ (x2.gates.get x7).inputs, ∃ (x10 : Fin x1), x3 x10 = Bool.true ∧ PEqualNP.ReadTwo.orp x2 x1 (↑x10) x8 := by
    intro n C x hm hb lit
    by_contra absent
    obtain ⟨j, hand, onWire⟩ := lit
    have paths := prefix_paths n C x hm hb absent C.gates
      ⟨[], by simp⟩ (n + j.val) onWire
    obtain ⟨k, _, path⟩ := paths
    change Relation.ReflTransGen _ k.val (n + j.val) at path
    generalize hwire : n + j.val = w at path
    cases path with
    | refl => have := k.isLt; omega
    | tail _ last =>
      obtain ⟨_, i, heq, ⟨_, hor⟩, _⟩ := last
      have hi : i = j.val := by omega
      subst i
      change (C.gates.getD j.val ⟨.or, []⟩).op = GateOp.or at hor
      rw [List.getD_eq_getElem _ _ j.isLt] at hor
      change C.gates[j.val].op = GateOp.and at hand
      rw [hand] at hor
      contradiction
  obtain ⟨j, hop, src⟩ := trace 26 C (pair 0 1) hC.1 hC.2.1 lit
  have reach : ∀ w ∈ (C.gates.get j).inputs, orp C 26 0 w ∨ orp C 26 1 w := by
    intro w hw
    obtain ⟨k, hk, path⟩ := src w hw
    change decide (k = 0 ∨ k = 1) = true at hk
    rcases of_decide_eq_true hk with rfl | rfl
    · exact Or.inl path
    · exact Or.inr path
  by_cases left : ∀ w ∈ (C.gates.get j).inputs, orp C 26 0 w
  · exact @common C hC least ⟨j, 0, Or.inl rfl, hop, left⟩
  by_cases right : ∀ w ∈ (C.gates.get j).inputs, orp C 26 1 w
  · exact @common C hC least ⟨j, 1, Or.inr rfl, hop, right⟩
  push Not at left right
  obtain ⟨b, hb, hb0⟩ := left
  obtain ⟨a, ha, ha1⟩ := right
  have ha0 := (reach a ha).resolve_right ha1
  have hb1 := (reach b hb).resolve_left hb0
  have distinct : a ≠ b := by rintro rfl; exact ha1 hb1
  have pair_list (xs : List ℕ) (u v : ℕ) (huv : u ≠ v) (hu : u ∈ xs) (hv : v ∈ xs)
      (hlen : xs.length ≤ 2) : xs = [u,v] ∨ xs = [v,u] := by
    rcases xs with _ | ⟨z, rest⟩
    · simp at hu
    rcases rest with _ | ⟨y, rest⟩
    · simp only [List.mem_singleton] at hu hv
      exact (huv (hu.trans hv.symm)).elim
    rcases rest with _ | ⟨t, ys⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact (huv rfl).elim
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact (huv rfl).elim
    · simp only [List.length_cons] at hlen
      omega
  have fan := (hC.1 _ (List.get_mem C.gates j)).2
  exact @opposite C hC least
    ⟨j, a, b, hop, pair_list _ _ _ distinct ha hb fan, ha0, ha1, hb1, hb0⟩
