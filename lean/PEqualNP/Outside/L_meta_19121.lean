import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19121_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len (gs : List Gate) (x : List Bool) : (gs.foldl stp x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append, stp, ih]; omega

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

/-- Only the wires of a set of at most `|R| + |gs|` wires decide the wires in `R`. -/
theorem cone (N : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) (R : Finset ℕ) :
    ∃ R' : Finset ℕ, R'.card ≤ R.card + gs.length ∧ ∀ x y : List Bool, x.length = N → y.length = N →
      (∀ i ∈ R', x.getD i false = y.getD i false) →
      ∀ w ∈ R, (gs.foldl stp x).getD w false = (gs.foldl stp y).getD w false := by
  induction gs using List.reverseRecOn generalizing R with
  | nil => exact ⟨R, by simp, fun x y _ _ h => by simpa using h⟩
  | append_singleton gs g ih =>
    have hg' : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g' h => hg g' (by simp [h])
    have h2 : g.inputs.length ≤ 2 := hg g (by simp)
    let t := N + gs.length
    let R0 := if t ∈ R then R.erase t ∪ g.inputs.toFinset else R
    obtain ⟨R', hc, hR'⟩ := ih hg' R0
    refine ⟨R', ?_, ?_⟩
    · have : R0.card ≤ R.card + 1 := by
        simp only [R0]; split_ifs with ht
        · have := Finset.card_union_le (R.erase t) g.inputs.toFinset
          have := Finset.card_erase_of_mem ht
          have := List.toFinset_card_le g.inputs
          have : 0 < R.card := Finset.card_pos.2 ⟨t, ht⟩
          omega
        · omega
      simp; omega
    · intro x y hx hy hxy w hw
      have e := hR' x y hx hy hxy
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, stp]
      rw [getD_snoc, getD_snoc, len, len, hx, hy]
      split_ifs with h1 h3
      · exact e w (by simp only [R0]; split_ifs <;> simp_all; omega)
      · have ht : t ∈ R := by simp only [t]; rw [← h3]; exact hw
        congr 1
        refine List.map_congr_left fun i hi => e i ?_
        simp [R0, ht, hi]
      · rfl

theorem mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length) (hxy : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (gs.foldl stp x).getD i false = true → (gs.foldl stp y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => simpa using hxy
  | append_singleton gs g ih =>
    have ih := ih fun g' h => hg g' (by simp [h])
    intro i
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, stp]
    rw [getD_snoc, getD_snoc, len, len, hl]
    split_ifs
    · exact ih i
    · rcases hg g (by simp) with h | h
      · simp only [h, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
        exact fun hh a ha => ih a (hh a ha)
      · simp only [h, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
        exact fun ⟨a, ha, hh⟩ => ⟨a, ha, ih a hh⟩
    · simp


theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega

theorem lb {n m : ℕ} (A : Fin n → Fin m → Bool) (C : Circuit) (hM : Monotone2 C)
    (hR : Represents A C) (K : Finset ℕ)
    (hK : ∀ k ∈ K, ∃ (u : Fin n) (v : Fin m) (u' : Fin n) (v' : Fin m), A u v = true ∧
      A u' v' = false ∧ (u.val = k ∨ u = u') ∧ (n + v.val = k ∨ v = v')) :
    K.card ≤ C.size + 1 := by
  obtain ⟨R', hc, hR'⟩ := cone (n + m) C.gates (fun g hg => (hM g hg).2) {C.output}
  have hsub : K ⊆ R' := by
    intro k hk
    by_contra hk'
    obtain ⟨u, v, u', v', h1, h2, h3, h4⟩ := hK k hk
    have e1 := hR u v
    have e2 := hR u' v'
    have hx : (oneEach u v).length = n + m := by simp [oneEach]
    have hyD : ∀ i, ((oneEach u v).set k false).getD i false =
        if i = k then false else (oneEach u v).getD i false := by
      intro i
      rw [List.getD_eq_getElem?_getD, List.getElem?_set, List.getD_eq_getElem?_getD]
      by_cases h : k = i
      · subst h; simp only [ite_true]; split_ifs <;> rfl
      · simp [h, Ne.symm h]
    have eq := hR' (oneEach u v) ((oneEach u v).set k false) hx (by simp [hx])
      (fun i hi => by
        rw [hyD]; split_ifs with h
        · exact absurd (h ▸ hi) hk'
        · rfl) _ (Finset.mem_singleton_self _)
    have := mono C.gates (fun g hg => by simpa using (hM g hg).1) ((oneEach u v).set k false)
      (oneEach u' v') (by simp [oneEach]) (fun i hi => by
        rw [hyD] at hi
        split_ifs at hi with h
        rw [oe] at hi ⊢
        rcases hi with rfl | rfl
        · rcases h3 with h3 | rfl
          · exact absurd h3 h
          · exact Or.inl rfl
        · rcases h4 with h4 | rfl
          · exact absurd h4 h
          · exact Or.inr rfl) C.output
    simp only [Circuit.eval, Circuit.wires] at e1 e2
    change (C.gates.foldl stp _).getD _ _ = _ at e1 e2
    rw [e1, h1] at eq
    rw [e2, h2] at this
    exact absurd (this eq.symm) (by simp)
  have := Finset.card_le_card hsub
  rw [Finset.card_singleton] at hc
  simp only [Circuit.size]
  omega

theorem other {n : ℕ} (hn : 2 ≤ n) (a : Fin n) : ∃ b : Fin n, b ≠ a := by
  by_cases h : a.val = 0
  · exact ⟨⟨1, by omega⟩, fun e => by simp [Fin.ext_iff] at e; omega⟩
  · exact ⟨⟨0, by omega⟩, fun e => by simp [Fin.ext_iff] at e; omega⟩

theorem xor_lb (n : ℕ) (i j : Fin n) (hn : 2 ≤ n) :
    ¬ RepSizeAtMost (fun u v : Fin n => xor (decide (u = i)) (decide (v = j))) (2 * n - 2) := by
  rintro ⟨C, hM, hs, hR⟩
  have := lb _ C hM hR (Finset.range (n + n)) ?_
  · simp at this; omega
  intro k hk
  simp only [Finset.mem_range] at hk
  obtain ⟨i', hi'⟩ := other hn i
  obtain ⟨j', hj'⟩ := other hn j
  by_cases hkn : k < n
  · by_cases hki : k = i.val
    · exact ⟨i, j', i', j', by simp [hj'], by simp [hi', hj'], Or.inl hki.symm, Or.inr rfl⟩
    · refine ⟨⟨k, hkn⟩, j, i, j, ?_, by simp, Or.inl rfl, Or.inr rfl⟩
      simp [Fin.ext_iff, hki]
  · by_cases hkj : k - n = j.val
    · exact ⟨i', j, i', j', by simp [hi'], by simp [hi', hj'], Or.inr rfl, Or.inl (by omega)⟩
    · refine ⟨i, ⟨k - n, by omega⟩, i, j, ?_, by simp, Or.inr rfl, Or.inl (by simp; omega)⟩
      simp [Fin.ext_iff, hkj]

def chain (b a : ℕ) : List ℕ → List Gate
  | [] => []
  | c :: L => ⟨GateOp.or, [a, c]⟩ :: chain (b + 1) b L

def last (b a : ℕ) : List ℕ → ℕ
  | [] => a
  | _ :: L => last (b + 1) b L

theorem chain_good (b a : ℕ) (L : List ℕ) :
    ∀ g ∈ chain b a L, g.op = GateOp.or ∧ g.inputs.length ≤ 2 := by
  induction L generalizing b a with
  | nil => simp [chain]
  | cons c L ih =>
    intro g hg
    simp only [chain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp
    · exact ih _ _ g hg

theorem chain_len (b a : ℕ) (L : List ℕ) : (chain b a L).length = L.length := by
  induction L generalizing b a with
  | nil => rfl
  | cons c L ih => simp [chain, ih]

theorem pre_stp (x : List Bool) (g : Gate) (w : ℕ) (h : w < x.length) :
    (stp x g).getD w false = x.getD w false := by
  rw [stp, getD_snoc, if_pos h]

theorem anyc {f g : ℕ → Bool} : ∀ (L : List ℕ), (∀ c ∈ L, f c = g c) → L.any f = L.any g
  | [], _ => rfl
  | c :: L, h => by
    rw [List.any_cons, List.any_cons, h c (by simp), anyc L fun c' h' => h c' (by simp [h'])]

theorem chain_val (L : List ℕ) : ∀ (x : List Bool) (a : ℕ), (∀ c ∈ L, c < x.length) →
    a < x.length →
    (∀ w < x.length, ((chain x.length a L).foldl stp x).getD w false = x.getD w false) ∧
    ((chain x.length a L).foldl stp x).getD (last x.length a L) false =
      (x.getD a false || L.any fun c => x.getD c false) := by
  induction L with
  | nil => intro x a _ ha; simp [chain, last]
  | cons c L ih =>
    intro x a hc ha
    have hl : (stp x ⟨GateOp.or, [a, c]⟩).length = x.length + 1 := by simp [stp]
    have hc' : ∀ c' ∈ L, c' < (stp x ⟨GateOp.or, [a, c]⟩).length := fun c' h => by
      have := hc c' (by simp [h]); omega
    obtain ⟨h1, h2⟩ := ih (stp x ⟨GateOp.or, [a, c]⟩) x.length hc' (by omega)
    simp only [chain, last, List.foldl_cons]
    rw [hl] at h1 h2
    refine ⟨fun w hw => by rw [h1 w (by omega), pre_stp _ _ _ hw], ?_⟩
    have : ∀ c' ∈ L, (stp x ⟨GateOp.or, [a, c]⟩).getD c' false = x.getD c' false :=
      fun c' h => pre_stp _ _ _ (hc c' (by simp [h]))
    rw [h2, anyc L this, stp, getD_snoc, if_neg (lt_irrefl _), if_pos rfl]
    simp [GateOp.eval, Bool.or_assoc]

def Lst (n : ℕ) (i j : ℕ) : List ℕ := (List.range n).erase i ++ ((List.range n).erase j).map (n + ·)

theorem Lst_len (n : ℕ) (i j : Fin n) : (Lst n i j).length = 2 * n - 2 := by
  simp [Lst, List.length_erase_of_mem, List.mem_range]; omega

theorem Lst_lt (n : ℕ) (i j : ℕ) : ∀ c ∈ Lst n i j, c < n + n := by
  intro c hc
  simp only [Lst, List.mem_append, List.mem_map] at hc
  rcases hc with h | ⟨k, h, rfl⟩
  · have := List.mem_range.1 (List.mem_of_mem_erase h); omega
  · have := List.mem_range.1 (List.mem_of_mem_erase h); omega

theorem Lst_any (n : ℕ) (i j u v : Fin n) :
    ((Lst n i j).any fun c => (oneEach u v).getD c false) = !(decide (u = i) && decide (v = j)) := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, oe, Lst, List.mem_append, List.mem_map,
    (List.nodup_range).mem_erase_iff, List.mem_range, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not, Fin.ext_iff]
  constructor
  · rintro ⟨c, h | ⟨k, h, rfl⟩, h'⟩ <;> omega
  · rintro (h | h)
    · exact ⟨u, Or.inl ⟨h, u.2⟩, Or.inl rfl⟩
    · exact ⟨n + v, Or.inr ⟨v, ⟨h, v.2⟩, rfl⟩, Or.inr rfl⟩

theorem xor_ub (n : ℕ) (i j : Fin n) (hn : 2 ≤ n) :
    RepSizeAtMost (fun u v : Fin n => xor (decide (u = i)) (decide (v = j))) (2 * n - 1) := by
  obtain ⟨c0, L', hL⟩ := List.exists_cons_of_length_pos (by rw [Lst_len n i j]; omega : 0 < (Lst n i j).length)
  have hlen := Lst_len n i j
  rw [hL] at hlen
  refine ⟨⟨⟨GateOp.or, [i, n + j]⟩ :: (chain (n + n + 1) c0 L' ++
    [⟨GateOp.and, [n + n, last (n + n + 1) c0 L']⟩]), n + n + 1 + L'.length⟩, fun g hg => ?_, ?_, fun u v => ?_⟩
  · simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | hg | rfl
    · simp
    · have := chain_good _ _ _ g hg; simp [this.1, this.2]
    · simp
  · simp only [Circuit.size, List.length_cons, List.length_append, chain_len, List.length_singleton, List.length_nil]
    simp at hlen; omega
  · have hx : (oneEach u v).length = n + n := by simp [oneEach]
    have hlt := Lst_lt n i j
    rw [hL] at hlt
    let x1 := stp (oneEach u v) ⟨GateOp.or, [i, n + j]⟩
    have hx1 : x1.length = n + n + 1 := by simp [x1, stp, hx]
    have hlt1 : ∀ c ∈ L', c < x1.length := fun c h => by have := hlt c (by simp [h]); omega
    obtain ⟨h1, h2⟩ := chain_val L' x1 c0 hlt1 (by have := hlt c0 (by simp); omega)
    rw [hx1] at h1 h2
    have hpre : ∀ c ∈ c0 :: L', x1.getD c false = (oneEach u v).getD c false :=
      fun c h => pre_stp _ _ _ (by have := hlt c h; omega)
    change (List.foldl stp _ _).getD _ _ = _
    rw [List.foldl_cons, List.foldl_append]
    change (List.foldl stp x1 _ ++ [_]).getD (n + n + 1 + L'.length) false = _
    rw [getD_snoc, len, hx1, chain_len, if_neg (by omega), if_pos rfl]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true]
    rw [h1 (n + n) (by omega), h2, hpre c0 (by simp), anyc L' (fun c h => hpre c (by simp [h]))]
    have e := Lst_any n i j u v
    rw [hL, List.any_cons] at e
    rw [e]
    simp only [x1, stp, getD_snoc, hx, if_neg (lt_irrefl _), if_pos rfl, GateOp.eval, List.map_cons,
      List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false]
    have g1 : (oneEach u v).getD i false = decide (u = i) := by
      apply Bool.eq_iff_iff.2; rw [oe]; simp [Fin.ext_iff]; omega
    have g2 : (oneEach u v).getD (n + j) false = decide (v = j) := by
      apply Bool.eq_iff_iff.2; rw [oe]; simp [Fin.ext_iff]; omega
    rw [g1, g2]
    cases decide (u = i) <;> cases decide (v = j) <;> rfl

end PEqualNP.Outside.L_meta_19121_aux

open PEqualNP.Outside.L_meta_19121_aux in
theorem PEqualNP.Outside.L_meta_19121 : ∀ (n : ℕ) (i j : Fin n), 2 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => xor (decide (u = i)) (decide (v = j))) (2 * n - 1) ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => xor (decide (u = i)) (decide (v = j))) (2 * n - 2) :=
  fun n i j hn => ⟨xor_ub n i j hn, xor_lb n i j hn⟩
