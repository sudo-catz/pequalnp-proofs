import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem PEqualNP.Outside.R_meta_5757_2
    (single : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   x2 ∈ ([[],[0],[13]] : List (List ℕ)) →     PEqualNP.MetaComplexity.Monotone2 x1 →       (∀ (x5 : Fin x1.gates.length), ∀ x6 ∈ (x1.gates.get x5).inputs, x6 < (27 : ℕ) + ↑x5) →         have x6 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x7 x8 : Fin (13 : ℕ)) => (List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x7)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x8);         have x8 : Finset (Fin (13 : ℕ)) → List Bool := fun (x8 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x8)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (∀ x10 ∈ x8, x10 - x9 ∉ x6);         have x9 : Finset (Fin (13 : ℕ)) → Prop := fun (x9 : Finset (Fin (13 : ℕ))) => x9.card = (4 : ℕ) ∧ ∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x11 - x10 ∈ x6}.card ≤ (2 : ℕ);         have x10 : List Bool → List Bool := fun (x10 : List Bool) => x10 ++ [x2.any fun (x11 : ℕ) => x10.getD x11 Bool.false];         (∀ (x11 x12 : Fin (13 : ℕ)), x11 - x12 ∈ x6 → x1.eval (x10 (x7 x11 x12)) = Bool.true) → (∀ (x12 : Finset (Fin (13 : ℕ))), x9 x12 → x1.eval (x10 (x8 x12)) = Bool.false) → (¬∃ (x13 : Fin x1.gates.length), ∃ x14 ∈ (x1.gates.get x13).inputs, (x1.gates.get x13).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (27 : ℕ) ≤ x14 ∧ ∃ (x15 : Fin x1.gates.length), x14 = (27 : ℕ) + ↑x15 ∧ (x1.gates.get x15).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (63 : ℕ) ≤ x1.size)
    (sameSide : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   x2 ∈ ([[0,1],[13,14]] : List (List ℕ)) →     PEqualNP.MetaComplexity.Monotone2 x1 →       (∀ (x5 : Fin x1.gates.length), ∀ x6 ∈ (x1.gates.get x5).inputs, x6 < (27 : ℕ) + ↑x5) →         have x6 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x7 x8 : Fin (13 : ℕ)) => (List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x7)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x8);         have x8 : Finset (Fin (13 : ℕ)) → List Bool := fun (x8 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x8)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (∀ x10 ∈ x8, x10 - x9 ∉ x6);         have x9 : Finset (Fin (13 : ℕ)) → Prop := fun (x9 : Finset (Fin (13 : ℕ))) => x9.card = (4 : ℕ) ∧ ∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x11 - x10 ∈ x6}.card ≤ (2 : ℕ);         have x10 : List Bool → List Bool := fun (x10 : List Bool) => x10 ++ [x2.any fun (x11 : ℕ) => x10.getD x11 Bool.false];         (∀ (x11 x12 : Fin (13 : ℕ)), x11 - x12 ∈ x6 → x1.eval (x10 (x7 x11 x12)) = Bool.true) → (∀ (x12 : Finset (Fin (13 : ℕ))), x9 x12 → x1.eval (x10 (x8 x12)) = Bool.false) → (¬∃ (x13 : Fin x1.gates.length), ∃ x14 ∈ (x1.gates.get x13).inputs, (x1.gates.get x13).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (27 : ℕ) ≤ x14 ∧ ∃ (x15 : Fin x1.gates.length), x14 = (27 : ℕ) + ↑x15 ∧ (x1.gates.get x15).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (63 : ℕ) ≤ x1.size)
    (opposite : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   x2 ∈ ([[0,13],[0,14]] : List (List ℕ)) →     PEqualNP.MetaComplexity.Monotone2 x1 →       (∀ (x5 : Fin x1.gates.length), ∀ x6 ∈ (x1.gates.get x5).inputs, x6 < (27 : ℕ) + ↑x5) →         have x6 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x7 x8 : Fin (13 : ℕ)) => (List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x7)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x8);         have x8 : Finset (Fin (13 : ℕ)) → List Bool := fun (x8 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x8)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (∀ x10 ∈ x8, x10 - x9 ∉ x6);         have x9 : Finset (Fin (13 : ℕ)) → Prop := fun (x9 : Finset (Fin (13 : ℕ))) => x9.card = (4 : ℕ) ∧ ∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x11 - x10 ∈ x6}.card ≤ (2 : ℕ);         have x10 : List Bool → List Bool := fun (x10 : List Bool) => x10 ++ [x2.any fun (x11 : ℕ) => x10.getD x11 Bool.false];         (∀ (x11 x12 : Fin (13 : ℕ)), x11 - x12 ∈ x6 → x1.eval (x10 (x7 x11 x12)) = Bool.true) → (∀ (x12 : Finset (Fin (13 : ℕ))), x9 x12 → x1.eval (x10 (x8 x12)) = Bool.false) → (¬∃ (x13 : Fin x1.gates.length), ∃ x14 ∈ (x1.gates.get x13).inputs, (x1.gates.get x13).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (27 : ℕ) ≤ x14 ∧ ∃ (x15 : Fin x1.gates.length), x14 = (27 : ℕ) + ↑x15 ∧ (x1.gates.get x15).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (63 : ℕ) ≤ x1.size) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   x2.length ≤ (2 : ℕ) →     PEqualNP.MetaComplexity.Monotone2 x1 →       (∀ (x5 : Fin x1.gates.length), ∀ x6 ∈ (x1.gates.get x5).inputs, x6 < (27 : ℕ) + ↑x5) →         have x6 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x7 x8 : Fin (13 : ℕ)) => (List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x7)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x8);         have x8 : Finset (Fin (13 : ℕ)) → List Bool := fun (x8 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x8)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (∀ x10 ∈ x8, x10 - x9 ∉ x6);         have x9 : Finset (Fin (13 : ℕ)) → Prop := fun (x9 : Finset (Fin (13 : ℕ))) => x9.card = (4 : ℕ) ∧ ∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x11 - x10 ∈ x6}.card ≤ (2 : ℕ);         have x10 : List Bool → List Bool := fun (x10 : List Bool) => x10 ++ [x2.any fun (x11 : ℕ) => x10.getD x11 Bool.false];         (∀ (x11 x12 : Fin (13 : ℕ)), x11 - x12 ∈ x6 → x1.eval (x10 (x7 x11 x12)) = Bool.true) → (∀ (x12 : Finset (Fin (13 : ℕ))), x9 x12 → x1.eval (x10 (x8 x12)) = Bool.false) → (¬∃ (x13 : Fin x1.gates.length), ∃ x14 ∈ (x1.gates.get x13).inputs, (x1.gates.get x13).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (27 : ℕ) ≤ x14 ∧ ∃ (x15 : Fin x1.gates.length), x14 = (27 : ℕ) + ↑x15 ∧ (x1.gates.get x15).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (63 : ℕ) ≤ x1.size) := by
  let D : Finset (Fin 13) :=
    {(0 : Fin 13), (1 : Fin 13), (3 : Fin 13), (9 : Fin 13)}

  let ptLine (p l : Fin 13) : List Bool :=
    (List.ofFn fun x : Fin 13 => Decidable.decide (x = p)) ++
      List.ofFn fun x : Fin 13 => Decidable.decide (x = l)

  let quadIn (Q : Finset (Fin 13)) : List Bool :=
    (List.ofFn fun x : Fin 13 => Decidable.decide (x ∈ Q)) ++
      List.ofFn fun x : Fin 13 => Decidable.decide (∀ y ∈ Q, y - x ∉ D)

  let isQuad (Q : Finset (Fin 13)) : Prop :=
    Q.card = 4 ∧ ∀ l : Fin 13, (Q.filter fun p => p - l ∈ D).card ≤ 2

  let valid (C : Circuit) (ins : List ℕ) : Prop :=
    let ext : List Bool → List Bool := fun v => v ++ [ins.any fun i => v.getD i false]
    (∀ p l : Fin 13, p - l ∈ D → C.eval (ext (ptLine p l)) = true) ∧
      ∀ Q : Finset (Fin 13), isQuad Q → C.eval (ext (quadIn Q)) = false

  let adjacent (C : Circuit) : Prop :=
    ∃ j : Fin C.gates.length, ∃ w ∈ (C.gates.get j).inputs,
      (C.gates.get j).op = GateOp.and ∧ 27 ≤ w ∧
      ∃ k : Fin C.gates.length, w = 27+k.val ∧ (C.gates.get k).op = GateOp.and

  let good (s : ℕ) (ins : List ℕ) : Prop :=
    ∃ C : Circuit,
      C.size = s ∧
      Monotone2 C ∧
      (∀ j : Fin C.gates.length, ∀ a ∈ (C.gates.get j).inputs, a < 27 + j.val) ∧
      (¬ adjacent C) ∧ valid C ins

  let wireMap (σ τ : Fin 13 → Fin 13) (w : ℕ) : ℕ :=
    if h1 : w < 13 then (σ ⟨w, h1⟩).val
    else if h2 : w < 26 then 13 + (τ ⟨w - 13, by omega⟩).val
    else w

  let mapCircuit (σ τ : Fin 13 → Fin 13) (C : Circuit) : Circuit :=
    ⟨C.gates.map fun g => ⟨g.op, g.inputs.map (wireMap σ τ)⟩, wireMap σ τ C.output⟩

  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
      (w ++ t).getD i false = w.getD i false := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have getD_append_self (w : List Bool) (b : Bool) :
      (w ++ [b]).getD w.length false = b := by
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (le_refl w.length)]
    simp

  have getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
      w.getD i false = false := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

  have ptLine_len (p l : Fin 13) : (ptLine p l).length = 26 := by
    simp [ptLine]

  have quadIn_len (Q : Finset (Fin 13)) : (quadIn Q).length = 26 := by
    simp [quadIn]

  have wireMap_lt26 (σ τ : Fin 13 → Fin 13) (w : ℕ) (hw : w < 26) :
      wireMap σ τ w < 26 := by
    unfold wireMap
    split_ifs with h1
    · have := (σ ⟨w, h1⟩).isLt; omega
    · have := (τ ⟨w - 13, by omega⟩).isLt; omega

  have wireMap_ge26 (σ τ : Fin 13 → Fin 13) (w : ℕ) (hw : 26 ≤ w) :
      wireMap σ τ w = w := by
    unfold wireMap
    have h1 : ¬ w < 13 := by omega
    have h2 : ¬ w < 26 := by omega
    simp [h1, h2]

  have adjacent_of_map (σ τ : Fin 13 → Fin 13) (C : Circuit)
      (nested : adjacent (mapCircuit σ τ C)) : adjacent C := by
    obtain ⟨j,w,member,hand,large,k,source,lower⟩ := nested
    have bounds (t : Fin (mapCircuit σ τ C).gates.length) : t.val < C.gates.length := by
      simpa [mapCircuit] using t.isLt
    have get (t : Fin (mapCircuit σ τ C).gates.length) : (mapCircuit σ τ C).gates.get t =
        ⟨(C.gates.get ⟨t.val,bounds t⟩).op, (C.gates.get ⟨t.val,bounds t⟩).inputs.map (wireMap σ τ)⟩ := by
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp [mapCircuit]
    rw [get j] at member hand
    rw [get k] at lower
    obtain ⟨u,hu,eq⟩ := List.mem_map.mp member
    have high : 26 ≤ u := by
      by_contra! low
      have bound := wireMap_lt26 σ τ u low
      omega
    have same : u = w := (wireMap_ge26 σ τ u high).symm.trans eq
    exact ⟨⟨j.val,bounds j⟩,u,hu,hand,by omega,⟨k.val,bounds k⟩,same.trans source,lower⟩

  have foldl_map_wires (σ τ : Fin 13 → Fin 13) (gs : List Gate) (w w' : List Bool)
      (hlen : w.length = w'.length) (hlen26 : 26 ≤ w.length)
      (hinit : ∀ i : ℕ, w'.getD (wireMap σ τ i) false = w.getD i false) :
      ∀ i : ℕ,
        ((gs.map fun g => ⟨g.op, g.inputs.map (wireMap σ τ)⟩).foldl step w').getD (wireMap σ τ i) false =
        (gs.foldl step w).getD i false := by
    induction gs generalizing w w' with
    | nil => exact hinit
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons]
      apply ih (step w g) (step w' ⟨g.op, g.inputs.map (wireMap σ τ)⟩)
      · simp [step, hlen]
      · simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
      · intro i
        by_cases hlt : i < w.length
        · have hlt' : wireMap σ τ i < w'.length := by
            by_cases h26 : i < 26
            · have := wireMap_lt26 σ τ i h26; omega
            · rw [wireMap_ge26 σ τ i (by omega)]; omega
          simp only [step]
          rw [getD_append_left_lt w' _ _ hlt', getD_append_left_lt w _ _ hlt]
          exact hinit i
        · by_cases heq : i = w.length
          · subst heq
            have hwm : wireMap σ τ w.length = w'.length := by
              rw [wireMap_ge26 σ τ w.length hlen26, hlen]
            simp only [step]
            rw [hwm, getD_append_self, getD_append_self]
            congr 1
            rw [List.map_map]
            apply List.map_congr_left
            intro a _
            exact hinit a
          · have hge : (step w g).length ≤ i := by
              simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
            have hge' : (step w' ⟨g.op, g.inputs.map (wireMap σ τ)⟩).length ≤ wireMap σ τ i := by
              rw [wireMap_ge26 σ τ i (by omega)]
              simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
            rw [getD_ge_len _ _ hge', getD_ge_len _ _ hge]

  have good_replace (s : ℕ) (ins ins' : List ℕ)
      (heq : ∀ v : List Bool, v.length = 26 →
        (ins'.any fun i => v.getD i false) = (ins.any fun i => v.getD i false))
      (h : good s ins) : good s ins' := by
    obtain ⟨C, hsz, hmono, hrb, hsep, hval1, hval2⟩ := h
    refine ⟨C, hsz, hmono, hrb, hsep, ?_, ?_⟩
    · intro p l hpl
      have h1 := hval1 p l hpl
      have h2 := heq (ptLine p l) (ptLine_len p l)
      dsimp only at h1 ⊢
      rw [h2]
      exact h1
    · intro Q hQ
      have h1 := hval2 Q hQ
      have h2 := heq (quadIn Q) (quadIn_len Q)
      dsimp only at h1 ⊢
      rw [h2]
      exact h1

  have good_swap (s a b : ℕ) (h : good s [a, b]) : good s [b, a] := by
    apply good_replace s [a, b] [b, a] _ h
    intro v _
    simp [Bool.or_comm]

  have good_aut (s : ℕ) (ins : List ℕ) (σ σi τ τi : Fin 13 → Fin 13)
      (hσ1 : ∀ p, σi (σ p) = p) (hσ2 : ∀ p, σ (σi p) = p)
      (hτ1 : ∀ l, τi (τ l) = l) (hτ2 : ∀ l, τ (τi l) = l)
      (hD : ∀ p l : Fin 13, σ p - τ l ∈ D ↔ p - l ∈ D)
      (h : good s ins) : good s (ins.map (wireMap σ τ)) := by
    obtain ⟨C, hsz, hmono, hrb, hsep, hval1, hval2⟩ := h
    refine ⟨mapCircuit σ τ C, ?_, ?_, ?_, fun d => hsep (adjacent_of_map σ τ C d), ?_, ?_⟩
    · change C.gates.length = s at hsz
      change (mapCircuit σ τ C).gates.length = s
      simp [mapCircuit, hsz]
    · intro g hg
      simp only [mapCircuit, List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      have hm := hmono g0 hg0
      exact ⟨hm.1, by simpa using hm.2⟩
    · intro j a ha
      have hj : j.val < C.gates.length := by simpa [mapCircuit] using j.isLt
      have hget : (mapCircuit σ τ C).gates.get j =
          ⟨(C.gates.get ⟨j.val, hj⟩).op, (C.gates.get ⟨j.val, hj⟩).inputs.map (wireMap σ τ)⟩ := by
        rw [List.get_eq_getElem, List.get_eq_getElem]
        simp [mapCircuit]
      rw [hget] at ha
      simp only [List.mem_map] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      have hblt : b < 27 + j.val := hrb ⟨j.val, hj⟩ b hb
      by_cases h26 : b < 26
      · have := wireMap_lt26 σ τ b h26; omega
      · rw [wireMap_ge26 σ τ b (by omega)]; exact hblt
    · have heval_eq : ∀ (v v' : List Bool), v.length = 26 → v'.length = 26 →
          (∀ p : Fin 13, v'.getD (σ p).val false = v.getD p.val false) →
          (∀ l : Fin 13, v'.getD (13 + (τ l).val) false = v.getD (13 + l.val) false) →
          (mapCircuit σ τ C).eval (v' ++ [(ins.map (wireMap σ τ)).any fun i => v'.getD i false]) =
          C.eval (v ++ [ins.any fun i => v.getD i false]) := by
        intro v v' hv hv' hp hl
        have hv_map : ∀ i : ℕ, v'.getD (wireMap σ τ i) false = v.getD i false := by
          intro i
          by_cases h1 : i < 13
          · unfold wireMap; simp only [h1, ↓reduceDIte]; exact hp ⟨i, h1⟩
          · by_cases h2 : i < 26
            · unfold wireMap
              simp only [h1, h2, ↓reduceDIte]
              have h3 := hl ⟨i - 13, by omega⟩
              have h4 : 13 + (i - 13) = i := by omega
              rwa [h4] at h3
            · rw [wireMap_ge26 σ τ i (by omega)]
              rw [getD_ge_len v' i (by omega), getD_ge_len v i (by omega)]
        have hany : ((ins.map (wireMap σ τ)).any fun i => v'.getD i false) =
            (ins.any fun i => v.getD i false) := by
          rw [List.any_map]
          congr 1
          funext i
          exact hv_map i
        rw [hany]
        set b := ins.any fun i => v.getD i false
        have hinit : ∀ i : ℕ, (v' ++ [b]).getD (wireMap σ τ i) false = (v ++ [b]).getD i false := by
          intro i
          by_cases h26 : i < 26
          · have hlt' : wireMap σ τ i < v'.length := by rw [hv']; exact wireMap_lt26 σ τ i h26
            rw [getD_append_left_lt v' [b] _ hlt', getD_append_left_lt v [b] _ (by omega)]
            exact hv_map i
          · by_cases h27 : i = 26
            · subst h27
              rw [wireMap_ge26 σ τ 26 (by omega)]
              rw [← hv', getD_append_self, hv', ← hv, getD_append_self]
            · rw [wireMap_ge26 σ τ i (by omega)]
              rw [getD_ge_len (v' ++ [b]) i (by simp [hv']; omega),
                  getD_ge_len (v ++ [b]) i (by simp [hv]; omega)]
        exact foldl_map_wires σ τ C.gates (v ++ [b]) (v' ++ [b])
          (by simp [hv, hv']) (by simp [hv]) hinit C.output
      intro p' l' hpl'
      let p := σi p'
      let l := τi l'
      have hpl : p - l ∈ D := by
        have h1 := (hD p l).mp
        rw [hσ2 p', hτ2 l'] at h1
        exact h1 hpl'
      rw [heval_eq (ptLine p l) (ptLine p' l') (ptLine_len p l) (ptLine_len p' l')]
      · exact hval1 p l hpl
      · intro q
        have hlt1 : (σ q).val < (List.ofFn fun x : Fin 13 => Decidable.decide (x = p')).length := by simp
        have hlt2 : q.val < (List.ofFn fun x : Fin 13 => Decidable.decide (x = p)).length := by simp
        simp only [ptLine]
        rw [getD_append_left_lt _ _ _ hlt1, getD_append_left_lt _ _ _ hlt2]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, Fin.is_lt, ↓reduceDIte,
          Option.getD_some, Fin.eta]
        have hiff : σ q = p' ↔ q = p := by
          constructor
          · intro hq; calc q = σi (σ q) := (hσ1 q).symm
              _ = σi p' := by rw [hq]
          · intro hq; rw [hq]; exact hσ2 p'
        simp [hiff]
      · intro r
        simp only [ptLine, List.getD_eq_getElem?_getD]
        have hlen1 : (List.ofFn fun x : Fin 13 => Decidable.decide (x = p')).length = 13 := by simp
        have hlen2 : (List.ofFn fun x : Fin 13 => Decidable.decide (x = p)).length = 13 := by simp
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
        simp only [hlen1, hlen2, Nat.add_sub_cancel_left, List.getElem?_ofFn, Fin.is_lt, ↓reduceDIte,
          Option.getD_some, Fin.eta]
        have hiff : τ r = l' ↔ r = l := by
          constructor
          · intro hr; calc r = τi (τ r) := (hτ1 r).symm
              _ = τi l' := by rw [hr]
          · intro hr; rw [hr]; exact hτ2 l'
        simp [hiff]
    · have heval_eq : ∀ (v v' : List Bool), v.length = 26 → v'.length = 26 →
          (∀ p : Fin 13, v'.getD (σ p).val false = v.getD p.val false) →
          (∀ l : Fin 13, v'.getD (13 + (τ l).val) false = v.getD (13 + l.val) false) →
          (mapCircuit σ τ C).eval (v' ++ [(ins.map (wireMap σ τ)).any fun i => v'.getD i false]) =
          C.eval (v ++ [ins.any fun i => v.getD i false]) := by
        intro v v' hv hv' hp hl
        have hv_map : ∀ i : ℕ, v'.getD (wireMap σ τ i) false = v.getD i false := by
          intro i
          by_cases h1 : i < 13
          · unfold wireMap; simp only [h1, ↓reduceDIte]; exact hp ⟨i, h1⟩
          · by_cases h2 : i < 26
            · unfold wireMap
              simp only [h1, h2, ↓reduceDIte]
              have h3 := hl ⟨i - 13, by omega⟩
              have h4 : 13 + (i - 13) = i := by omega
              rwa [h4] at h3
            · rw [wireMap_ge26 σ τ i (by omega)]
              rw [getD_ge_len v' i (by omega), getD_ge_len v i (by omega)]
        have hany : ((ins.map (wireMap σ τ)).any fun i => v'.getD i false) =
            (ins.any fun i => v.getD i false) := by
          rw [List.any_map]
          congr 1
          funext i
          exact hv_map i
        rw [hany]
        set b := ins.any fun i => v.getD i false
        have hinit : ∀ i : ℕ, (v' ++ [b]).getD (wireMap σ τ i) false = (v ++ [b]).getD i false := by
          intro i
          by_cases h26 : i < 26
          · have hlt' : wireMap σ τ i < v'.length := by rw [hv']; exact wireMap_lt26 σ τ i h26
            rw [getD_append_left_lt v' [b] _ hlt', getD_append_left_lt v [b] _ (by omega)]
            exact hv_map i
          · by_cases h27 : i = 26
            · subst h27
              rw [wireMap_ge26 σ τ 26 (by omega)]
              rw [← hv', getD_append_self, hv', ← hv, getD_append_self]
            · rw [wireMap_ge26 σ τ i (by omega)]
              rw [getD_ge_len (v' ++ [b]) i (by simp [hv']; omega),
                  getD_ge_len (v ++ [b]) i (by simp [hv]; omega)]
        exact foldl_map_wires σ τ C.gates (v ++ [b]) (v' ++ [b])
          (by simp [hv, hv']) (by simp [hv]) hinit C.output
      intro Q' hQ'
      let Q := Q'.image σi
      have hσi_inj : Function.Injective σi := Function.LeftInverse.injective hσ2
      have hσ_inj : Function.Injective σ := Function.LeftInverse.injective hσ1
      have hmemQ : ∀ p : Fin 13, σ p ∈ Q' ↔ p ∈ Q := by
        intro p
        constructor
        · intro hp; exact Finset.mem_image.mpr ⟨σ p, hp, hσ1 p⟩
        · intro hp
          rcases Finset.mem_image.mp hp with ⟨p', hp', hpeq⟩
          have : σ p = p' := by rw [← hpeq, hσ2 p']
          rwa [this]
      have hQ : isQuad Q := by
        refine ⟨?_, ?_⟩
        · rw [Finset.card_image_of_injective Q' hσi_inj]; exact hQ'.1
        · intro l
          have hsub : (Q.filter fun p => p - l ∈ D).image σ = Q'.filter fun p' => p' - τ l ∈ D := by
            ext p'
            simp only [Finset.mem_image, Finset.mem_filter]
            constructor
            · rintro ⟨p, ⟨hpQ, hpl⟩, rfl⟩
              exact ⟨(hmemQ p).mpr hpQ, (hD p l).mpr hpl⟩
            · rintro ⟨hp', hp'l⟩
              refine ⟨σi p', ⟨Finset.mem_image.mpr ⟨p', hp', rfl⟩, ?_⟩, hσ2 p'⟩
              have h1 := (hD (σi p') l).mp
              rw [hσ2 p'] at h1
              exact h1 hp'l
          rw [← Finset.card_image_of_injective _ hσ_inj, hsub]
          exact hQ'.2 (τ l)
      rw [heval_eq (quadIn Q) (quadIn Q') (quadIn_len Q) (quadIn_len Q')]
      · exact hval2 Q hQ
      · intro p
        have hlt1 : (σ p).val < (List.ofFn fun x : Fin 13 => Decidable.decide (x ∈ Q')).length := by simp
        have hlt2 : p.val < (List.ofFn fun x : Fin 13 => Decidable.decide (x ∈ Q)).length := by simp
        simp only [quadIn]
        rw [getD_append_left_lt _ _ _ hlt1, getD_append_left_lt _ _ _ hlt2]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, Fin.is_lt, ↓reduceDIte,
          Option.getD_some, Fin.eta]
        simp [hmemQ p]
      · intro l
        simp only [quadIn, List.getD_eq_getElem?_getD]
        have hlen1 : (List.ofFn fun x : Fin 13 => Decidable.decide (x ∈ Q')).length = 13 := by simp
        have hlen2 : (List.ofFn fun x : Fin 13 => Decidable.decide (x ∈ Q)).length = 13 := by simp
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
        simp only [hlen1, hlen2, Nat.add_sub_cancel_left, List.getElem?_ofFn, Fin.is_lt, ↓reduceDIte,
          Option.getD_some, Fin.eta]
        have hiff : (∀ y ∈ Q', y - τ l ∉ D) ↔ (∀ y ∈ Q, y - l ∉ D) := by
          constructor
          · intro h1 y hy hyl
            exact h1 (σ y) ((hmemQ y).mpr hy) ((hD y l).mpr hyl)
          · intro h1 y' hy' hy'l
            have hyQ : σi y' ∈ Q := Finset.mem_image.mpr ⟨y', hy', rfl⟩
            have h2 := (hD (σi y') l).mp
            rw [hσ2 y'] at h2
            exact h1 (σi y') hyQ (h2 hy'l)
        simp [hiff]

  have good_shift (s : ℕ) (ins : List ℕ) (c : Fin 13) (h : good s ins) :
      good s (ins.map (wireMap (fun x => x + c) (fun x => x + c))) := by
    apply good_aut s ins (fun x => x + c) (fun x => x - c) (fun x => x + c) (fun x => x - c)
      (fun p => by abel) (fun p => by abel) (fun l => by abel) (fun l => by abel)
      (fun p l => by simp [add_sub_add_right_eq_sub]) h

  have good_frob3 (s : ℕ) (ins : List ℕ) (h : good s ins) :
      good s (ins.map (wireMap (fun x => 3 * x) (fun x => 3 * x))) := by
    apply good_aut s ins (fun x => 3 * x) (fun x => 9 * x) (fun x => 3 * x) (fun x => 9 * x)
      (by decide) (by decide) (by decide) (by decide) (by decide) h

  have good_frob9 (s : ℕ) (ins : List ℕ) (h : good s ins) :
      good s (ins.map (wireMap (fun x => 9 * x) (fun x => 9 * x))) := by
    apply good_aut s ins (fun x => 9 * x) (fun x => 3 * x) (fun x => 9 * x) (fun x => 3 * x)
      (by decide) (by decide) (by decide) (by decide) (by decide) h

  let tbl (l : List (Fin 13)) (x : Fin 13) : Fin 13 := l.getD x.val 0

  let a1s : Fin 13 → Fin 13 := tbl [0, 12, 1, 2, 11, 10, 5, 6, 9, 8, 7, 4, 3]
  let a1t : Fin 13 → Fin 13 := tbl [12, 11, 1, 2, 10, 9, 5, 6, 8, 7, 4, 3, 0]
  let a1si : Fin 13 → Fin 13 := tbl [0, 2, 3, 12, 11, 6, 7, 10, 9, 8, 5, 4, 1]
  let a1ti : Fin 13 → Fin 13 := tbl [12, 2, 3, 11, 10, 6, 7, 9, 8, 5, 4, 1, 0]

  let a2s : Fin 13 → Fin 13 := tbl [0, 6, 5, 10, 8, 12, 3, 2, 4, 11, 1, 9, 7]
  let a2t : Fin 13 → Fin 13 := tbl [10, 5, 9, 7, 12, 3, 2, 1, 8, 11, 0, 6, 4]
  let a2si : Fin 13 → Fin 13 := tbl [0, 10, 7, 6, 8, 2, 1, 12, 4, 11, 3, 9, 5]
  let a2ti : Fin 13 → Fin 13 := tbl [10, 7, 6, 5, 12, 1, 11, 3, 8, 2, 0, 9, 4]

  let a3s : Fin 13 → Fin 13 := tbl [0, 9, 4, 1, 11, 10, 12, 6, 5, 3, 8, 2, 7]
  let a3t : Fin 13 → Fin 13 := tbl [0, 8, 1, 11, 10, 9, 3, 5, 2, 7, 12, 6, 4]
  let a3si : Fin 13 → Fin 13 := tbl [0, 3, 11, 9, 2, 8, 7, 12, 10, 1, 5, 4, 6]
  let a3ti : Fin 13 → Fin 13 := tbl [0, 2, 8, 6, 12, 7, 11, 9, 1, 5, 4, 3, 10]

  have good_a1 (s : ℕ) (ins : List ℕ) (h : good s ins) :
      good s (ins.map (wireMap a1s a1t)) :=
    good_aut s ins a1s a1si a1t a1ti (by decide) (by decide) (by decide) (by decide) (by decide) h

  have good_a2 (s : ℕ) (ins : List ℕ) (h : good s ins) :
      good s (ins.map (wireMap a2s a2t)) :=
    good_aut s ins a2s a2si a2t a2ti (by decide) (by decide) (by decide) (by decide) (by decide) h

  have good_a3 (s : ℕ) (ins : List ℕ) (h : good s ins) :
      good s (ins.map (wireMap a3s a3t)) :=
    good_aut s ins a3s a3si a3t a3ti (by decide) (by decide) (by decide) (by decide) (by decide) h

  have pts_0d (s : ℕ) (d : Fin 13) (hd : d ≠ 0) (h : good s [0, d.val]) : good s [0, 1] := by
    fin_cases d
    · exact absurd rfl hd
    · exact h
    · simpa [wireMap, a1s, tbl] using good_a1 s [0, 2] h
    · simpa [wireMap] using good_frob9 s [0, 3] h
    · have h1 : good s [9, 0] := by simpa [wireMap] using good_shift s [0, 4] 9 h
      have h2 : good s [1, 0] := by simpa [wireMap] using good_frob3 s [9, 0] h1
      exact good_swap s 1 0 h2
    · have h1 : good s [0, 2] := by simpa [wireMap] using good_frob3 s [0, 5] h
      simpa [wireMap, a1s, tbl] using good_a1 s [0, 2] h1
    · have h1 : good s [0, 2] := by simpa [wireMap] using good_frob9 s [0, 6] h
      simpa [wireMap, a1s, tbl] using good_a1 s [0, 2] h1
    · have h1 : good s [6, 0] := by simpa [wireMap] using good_shift s [0, 7] 6 h
      have h2 : good s [2, 0] := by simpa [wireMap] using good_frob9 s [6, 0] h1
      have h3 : good s [1, 0] := by simpa [wireMap, a1s, tbl] using good_a1 s [2, 0] h2
      exact good_swap s 1 0 h3
    · have h1 : good s [5, 0] := by simpa [wireMap] using good_shift s [0, 8] 5 h
      have h2 : good s [2, 0] := by simpa [wireMap] using good_frob3 s [5, 0] h1
      have h3 : good s [1, 0] := by simpa [wireMap, a1s, tbl] using good_a1 s [2, 0] h2
      exact good_swap s 1 0 h3
    · simpa [wireMap] using good_frob3 s [0, 9] h
    · have h1 : good s [3, 0] := by simpa [wireMap] using good_shift s [0, 10] 3 h
      have h2 : good s [1, 0] := by simpa [wireMap] using good_frob9 s [3, 0] h1
      exact good_swap s 1 0 h2
    · have h1 : good s [2, 0] := by simpa [wireMap] using good_shift s [0, 11] 2 h
      have h2 : good s [1, 0] := by simpa [wireMap, a1s, tbl] using good_a1 s [2, 0] h1
      exact good_swap s 1 0 h2
    · have h1 : good s [1, 0] := by simpa [wireMap] using good_shift s [0, 12] 1 h
      exact good_swap s 1 0 h1

  have lines_0d (s : ℕ) (d : Fin 13) (hd : d ≠ 0) (h : good s [13, 13 + d.val]) : good s [13, 14] := by
    fin_cases d
    · exact absurd rfl hd
    · exact h
    · simpa [wireMap, a3t, tbl] using good_a3 s [13, 15] h
    · simpa [wireMap] using good_frob9 s [13, 16] h
    · have h1 : good s [22, 13] := by simpa [wireMap] using good_shift s [13, 17] 9 h
      have h2 : good s [14, 13] := by simpa [wireMap] using good_frob3 s [22, 13] h1
      exact good_swap s 14 13 h2
    · have h1 : good s [13, 15] := by simpa [wireMap] using good_frob3 s [13, 18] h
      simpa [wireMap, a3t, tbl] using good_a3 s [13, 15] h1
    · have h1 : good s [13, 15] := by simpa [wireMap] using good_frob9 s [13, 19] h
      simpa [wireMap, a3t, tbl] using good_a3 s [13, 15] h1
    · have h1 : good s [19, 13] := by simpa [wireMap] using good_shift s [13, 20] 6 h
      have h2 : good s [15, 13] := by simpa [wireMap] using good_frob9 s [19, 13] h1
      have h3 : good s [14, 13] := by simpa [wireMap, a3t, tbl] using good_a3 s [15, 13] h2
      exact good_swap s 14 13 h3
    · have h1 : good s [18, 13] := by simpa [wireMap] using good_shift s [13, 21] 5 h
      have h2 : good s [15, 13] := by simpa [wireMap] using good_frob3 s [18, 13] h1
      have h3 : good s [14, 13] := by simpa [wireMap, a3t, tbl] using good_a3 s [15, 13] h2
      exact good_swap s 14 13 h3
    · simpa [wireMap] using good_frob3 s [13, 22] h
    · have h1 : good s [16, 13] := by simpa [wireMap] using good_shift s [13, 23] 3 h
      have h2 : good s [14, 13] := by simpa [wireMap] using good_frob9 s [16, 13] h1
      exact good_swap s 14 13 h2
    · have h1 : good s [15, 13] := by simpa [wireMap] using good_shift s [13, 24] 2 h
      have h2 : good s [14, 13] := by simpa [wireMap, a3t, tbl] using good_a3 s [15, 13] h1
      exact good_swap s 14 13 h2
    · have h1 : good s [14, 13] := by simpa [wireMap] using good_shift s [13, 25] 1 h
      exact good_swap s 14 13 h1

  have ptline_0d (s : ℕ) (d : Fin 13) (h : good s [0, 13 + d.val]) :
      good s [0, 13] ∨ good s [0, 14] := by
    fin_cases d
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr (by simpa [wireMap, a1s, a1t, tbl] using good_a1 s [0, 15] h)
    · exact Or.inr (by simpa [wireMap] using good_frob9 s [0, 16] h)
    · have h1 : good s [0, 25] := by simpa [wireMap] using good_frob3 s [0, 17] h
      exact Or.inl (by simpa [wireMap, a1s, a1t, tbl] using good_a1 s [0, 25] h1)
    · have h1 : good s [0, 15] := by simpa [wireMap] using good_frob3 s [0, 18] h
      exact Or.inr (by simpa [wireMap, a1s, a1t, tbl] using good_a1 s [0, 15] h1)
    · have h1 : good s [0, 15] := by simpa [wireMap] using good_frob9 s [0, 19] h
      exact Or.inr (by simpa [wireMap, a1s, a1t, tbl] using good_a1 s [0, 15] h1)
    · exact Or.inr (by simpa [wireMap, a2s, a2t, tbl] using good_a2 s [0, 20] h)
    · have h1 : good s [0, 20] := by simpa [wireMap] using good_frob9 s [0, 21] h
      exact Or.inr (by simpa [wireMap, a2s, a2t, tbl] using good_a2 s [0, 20] h1)
    · exact Or.inr (by simpa [wireMap] using good_frob3 s [0, 22] h)
    · have h1 : good s [0, 25] := by simpa [wireMap] using good_frob9 s [0, 23] h
      exact Or.inl (by simpa [wireMap, a1s, a1t, tbl] using good_a1 s [0, 25] h1)
    · have h1 : good s [0, 20] := by simpa [wireMap] using good_frob3 s [0, 24] h
      exact Or.inr (by simpa [wireMap, a2s, a2t, tbl] using good_a2 s [0, 20] h1)
    · exact Or.inl (by simpa [wireMap, a1s, a1t, tbl] using good_a1 s [0, 25] h)

  have reduce_one (s a : ℕ) (h : good s [a]) :
      ∃ ins ∈ [[], [0], [13], [0, 1], [13, 14], [0, 13], [0, 14]], good s ins := by
    by_cases h1 : a < 13
    · refine ⟨[0], by simp, ?_⟩
      have hsh := good_shift s [a] (-⟨a, h1⟩) h
      have hm : [a].map (wireMap (fun x => x + -⟨a, h1⟩) (fun x => x + -⟨a, h1⟩)) = [0] := by
        simp [wireMap, h1]
      rwa [hm] at hsh
    · by_cases h2 : a < 26
      · refine ⟨[13], by simp, ?_⟩
        have hsh := good_shift s [a] (-⟨a - 13, by omega⟩) h
        have hm : [a].map (wireMap (fun x => x + -⟨a - 13, by omega⟩) (fun x => x + -⟨a - 13, by omega⟩)) = [13] := by
          simp [wireMap, h1, h2]
        rwa [hm] at hsh
      · refine ⟨[], by simp, ?_⟩
        apply good_replace s [a] [] _ h
        intro v hv
        have h0 := getD_ge_len v a (by omega)
        simp only [List.any_cons, List.any_nil, h0, Bool.or_false]

  have reduce_two_ordered (s a b : ℕ) (hab : a < b) (hb : b < 26) (h : good s [a, b]) :
      ∃ ins ∈ [[], [0], [13], [0, 1], [13, 14], [0, 13], [0, 14]], good s ins := by
    by_cases ha13 : a < 13
    · by_cases hb13 : b < 13
      · refine ⟨[0, 1], by simp, ?_⟩
        let pa : Fin 13 := ⟨a, ha13⟩
        let pb : Fin 13 := ⟨b, hb13⟩
        have hsh := good_shift s [a, b] (-pa) h
        have hm : [a, b].map (wireMap (fun x => x + -pa) (fun x => x + -pa)) = [0, (pb + -pa).val] := by
          simp [wireMap, ha13, hb13, pa, pb]
        rw [hm] at hsh
        have hne : pb + -pa ≠ 0 := by
          intro heq
          have : pb = pa := by
            calc pb = pb + -pa + pa := by abel
              _ = 0 + pa := by rw [heq]
              _ = pa := zero_add pa
          have : b = a := congrArg Fin.val this
          omega
        exact pts_0d s (pb + -pa) hne hsh
      · let pa : Fin 13 := ⟨a, ha13⟩
        let lb : Fin 13 := ⟨b - 13, by omega⟩
        have hsh := good_shift s [a, b] (-pa) h
        have hm : [a, b].map (wireMap (fun x => x + -pa) (fun x => x + -pa)) = [0, 13 + (lb + -pa).val] := by
          simp [wireMap, ha13, hb13, hb, pa, lb]
        rw [hm] at hsh
        rcases ptline_0d s (lb + -pa) hsh with h13 | h14
        · exact ⟨[0, 13], by simp, h13⟩
        · exact ⟨[0, 14], by simp, h14⟩
    · refine ⟨[13, 14], by simp, ?_⟩
      have ha26 : a < 26 := by omega
      have hb13 : ¬ b < 13 := by omega
      let la : Fin 13 := ⟨a - 13, by omega⟩
      let lb : Fin 13 := ⟨b - 13, by omega⟩
      have hsh := good_shift s [a, b] (-la) h
      have hm : [a, b].map (wireMap (fun x => x + -la) (fun x => x + -la)) = [13, 13 + (lb + -la).val] := by
        simp [wireMap, ha13, ha26, hb13, hb, la, lb]
      rw [hm] at hsh
      have hne : lb + -la ≠ 0 := by
        intro heq
        have : lb = la := by
          calc lb = lb + -la + la := by abel
            _ = 0 + la := by rw [heq]
            _ = la := zero_add la
        have : b - 13 = a - 13 := congrArg Fin.val this
        omega
      exact lines_0d s (lb + -la) hne hsh

  have reduce_all (s : ℕ) (ins : List ℕ) (hlen : ins.length ≤ 2) (h : good s ins) :
      ∃ ins' ∈ [[], [0], [13], [0, 1], [13, 14], [0, 13], [0, 14]], good s ins' := by
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · exact ⟨[], by simp, h⟩
    · exact reduce_one s a h
    · by_cases ha : a < 26
      · by_cases hb : b < 26
        · by_cases hlt : a < b
          · exact reduce_two_ordered s a b hlt hb h
          · by_cases heq : a = b
            · subst heq
              have h1 : good s [a] := by
                apply good_replace s [a, a] [a] _ h
                intro v _; simp
              exact reduce_one s a h1
            · exact reduce_two_ordered s b a (by omega) ha (good_swap s a b h)
        · have h1 : good s [a] := by
            apply good_replace s [a, b] [a] _ h
            intro v hv
            have h0 := getD_ge_len v b (by omega)
            simp only [List.any_cons, List.any_nil, h0, Bool.or_false]
          exact reduce_one s a h1
      · have h1 : good s [b] := by
          apply good_replace s [a, b] [b] _ h
          intro v hv
          have h0 := getD_ge_len v a (by omega)
          simp only [List.any_cons, List.any_nil, h0, Bool.false_or, Bool.or_false]
        exact reduce_one s b h1
    · simp at hlen


  have seven {C : Circuit} {ops : List ℕ} (hs : ops.length ≤ 2) (mono : Monotone2 C)
      (back : ∀ j : Fin C.gates.length, ∀ i ∈ (C.gates.get j).inputs, i < 27+j.val)
      (ok : valid C ops) (separate : ¬ adjacent C) :
      ∃ t ∈ [[],[0],[13],[0,1],[13,14],[0,13],[0,14]], good C.size t :=
    reduce_all C.size ops hs ⟨C,rfl,mono,back,separate,ok⟩

  intro C ops hs mono back diff posInput negInput isQuad' extend pos neg noDirect
  obtain ⟨t,rep,B,sizeB,hm,rb,separated,tests⟩ := seven hs mono back ⟨pos,neg⟩ noDirect
  have family : t ∈ ([[],[0],[13]] : List (List ℕ)) ∨
      t ∈ ([[0,1],[13,14]] : List (List ℕ)) ∨ t ∈ ([[0,13],[0,14]] : List (List ℕ)) := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] using rep
  rw [← sizeB]
  rcases family with h | h | h
  · exact single B t h hm rb tests.1 tests.2 separated
  · exact sameSide B t h hm rb tests.1 tests.2 separated
  · exact opposite B t h hm rb tests.1 tests.2 separated
