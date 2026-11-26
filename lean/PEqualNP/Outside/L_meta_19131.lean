import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_19131

private def push (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma length_run (gs : List Gate) (w : List Bool) :
    (gs.foldl push w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [push]; omega

private lemma read_old (w : List Bool) (b : Bool) (i : ℕ) (h : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  by_cases hi : i < w.length
  · exact List.getD_append _ _ _ _ hi
  · rw [List.getD_eq_default (w ++ [b]) false (by simp; omega),
        List.getD_eq_default w false (by omega)]

private lemma gate_mono (w z : List Bool) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (h : ∀ i ∈ g.inputs, w.getD i false = true → z.getD i false = true) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = true →
    g.op.eval (g.inputs.map fun i => z.getD i false) = true := by
  rcases (show g.op = .and ∨ g.op = .or from hop) with hAnd | hOr
  · rw [hAnd]
    intro hv
    apply List.all_eq_true.mpr
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact h i hi (List.all_eq_true.mp hv _ (List.mem_map.mpr ⟨i, hi, rfl⟩))
  · rw [hOr]
    intro hv
    obtain ⟨b, hb, hv⟩ := List.any_eq_true.mp hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨i, hi, rfl⟩, h i hi hv⟩

private lemma support (n : ℕ) (gs : List Gate) (W : Finset ℕ)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∃ S : Finset ℕ, S ⊆ Finset.range n ∧ S.card ≤ W.card + gs.length ∧
      ∀ w z : List Bool, w.length = n → z.length = n →
        (∀ i ∈ S, w.getD i false = true → z.getD i false = true) →
        ∀ i ∈ W, (gs.foldl push w).getD i false = true →
          (gs.foldl push z).getD i false = true := by
  induction gs using List.reverseRecOn generalizing W with
  | nil =>
    refine ⟨W.filter (· < n), ?_, by simpa using Finset.card_filter_le W (· < n), ?_⟩
    · intro i hi
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
    · intro w z hw _ hs i hi hv
      by_cases h : i < n
      · exact hs i (Finset.mem_filter.mpr ⟨hi, h⟩) hv
      · change w.getD i false = true at hv
        rw [List.getD_eq_default w false (by omega)] at hv
        contradiction
  | append_singleton gs g ih =>
    let k := n + gs.length
    let V := if k ∈ W then W.erase k ∪ g.inputs.toFinset else W
    have hprefix : ∀ a ∈ gs,
        a.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ a.inputs.length ≤ 2 :=
      fun a ha => hg a (List.mem_append_left _ ha)
    have hgate := hg g (by simp)
    obtain ⟨S, hS, hc, hs⟩ := ih V hprefix
    have hV : V.card ≤ W.card + 1 := by
      by_cases hk : k ∈ W
      · simp only [V, ite_eq_left hk]
        have h₁ := Finset.card_union_le (W.erase k) g.inputs.toFinset
        have h₂ := (List.toFinset_card_le g.inputs).trans hgate.2
        have h₃ := Finset.card_erase_of_mem hk
        have h₄ := Finset.card_pos.mpr (show W.Nonempty from ⟨k, hk⟩)
        omega
      · simp [V, hk]
    refine ⟨S, hS, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
    intro w z hw hz hag i hi
    let a := gs.foldl push w
    let b := gs.foldl push z
    have ha : a.length = k := by simp [a, length_run, hw, k]
    have hb : b.length = k := by simp [b, length_run, hz, k]
    have hp := hs w z hw hz hag
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (push a g).getD i false = true → (push b g).getD i false = true
    by_cases eq : i = k
    · subst i
      have read_new (xs : List Bool) (hxs : xs.length = k) :
          (push xs g).getD k false = g.op.eval (g.inputs.map fun j => xs.getD j false) := by
        rw [← hxs]
        simp [push]
      rw [read_new a ha, read_new b hb]
      apply gate_mono a b g hgate.1
      intro j hj
      exact hp j (by simp only [V, ite_eq_left hi]; exact Finset.mem_union_right _ (List.mem_toFinset.mpr hj))
    · rw [show (push a g).getD i false = a.getD i false from read_old _ _ _ (by simpa [ha] using eq),
        show (push b g).getD i false = b.getD i false from read_old _ _ _ (by simpa [hb] using eq)]
      apply hp i
      by_cases hk : k ∈ W
      · simp only [V, ite_eq_left hk]
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq, hi⟩)
      · simpa [V, hk] using hi

private def matrix (u v : Fin 6) : Bool :=
  xor (decide (u = 0)) (decide (v = 0))

private def witness (i : Fin 12) : (Fin 6 × Fin 6) × (Fin 6 × Fin 6) :=
  if i.val < 6 then
    if i.val = 0 then ((0, 1), (1, 1)) else ((Fin.ofNat 6 i.val, 0), (0, 0))
  else
    if i.val = 6 then ((1, 0), (1, 1)) else ((0, Fin.ofNat 6 (i.val - 6)), (0, 0))

private lemma separates : ∀ i : Fin 12,
    let (p, q) := witness i
    matrix p.1 p.2 = true ∧ matrix q.1 q.2 = false ∧
      ∀ j : Fin 12, j ≠ i →
        (oneEach p.1 p.2).getD j.val false = true →
          (oneEach q.1 q.2).getD j.val false = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_19131

open PEqualNP.Outside.L_meta_19131 in
theorem PEqualNP.Outside.L_meta_19131 : (¬ (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => xor (decide (u = 0)) (decide (v = 0))) 10)) := by
  rintro ⟨C, hmon, hsize, hrep⟩
  obtain ⟨S, hS, hcard, hmono⟩ := support 12 C.gates {C.output} hmon
  have hall : Finset.range 12 ⊆ S := by
    intro i hi
    by_contra hn
    let j : Fin 12 := ⟨i, Finset.mem_range.mp hi⟩
    rcases hw : witness j with ⟨⟨u, v⟩, ⟨u', v'⟩⟩
    have hwit := separates j
    rw [hw] at hwit
    obtain ⟨hp, hq, hpair⟩ := hwit
    have hgood := (hrep u v).trans hp
    have hbad := (hrep u' v').trans hq
    have hg := hmono (oneEach u v) (oneEach u' v') (by simp [oneEach]) (by simp [oneEach])
      (by
        intro k hk
        let l : Fin 12 := ⟨k, Finset.mem_range.mp (hS hk)⟩
        apply hpair l
        intro eq
        have he : k = i := congrArg Fin.val eq
        exact hn (he ▸ hk))
      C.output (Finset.mem_singleton_self _) hgood
    exact Bool.noConfusion (hbad.symm.trans hg)
  have hge := Finset.card_le_card hall
  simp only [Finset.card_range] at hge
  simp only [Finset.card_singleton] at hcard
  change C.gates.length ≤ 10 at hsize
  omega
