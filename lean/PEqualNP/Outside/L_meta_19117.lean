import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19117_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma len (gs : List Gate) (acc : List Bool) :
    (gs.foldl wstep acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [wstep]; omega

lemma keep (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < acc.length) :
    (gs.foldl wstep acc).getD j false = acc.getD j false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (wstep acc g) (by simp [wstep]; omega)]
    rw [wstep, List.getD_append _ _ _ _ hj]

def orG (a b : ℕ) : Gate := ⟨GateOp.or, [a, b]⟩

lemma last (w : List Bool) (a b : ℕ) :
    (wstep w (orG a b)).getD w.length false = (w.getD a false || w.getD b false) := by
  simp [wstep, orG, GateOp.eval, List.getD_eq_getElem?_getD]

def cp (f : ℕ → ℕ) (base i : ℕ) : ℕ := if i = 0 then f 0 else base + i - 1

def chain (f : ℕ → ℕ) (base n : ℕ) : List Gate :=
  (List.range n).map fun i => orG (cp f base i) (f (i + 1))

lemma chain_spec (f : ℕ → ℕ) (base : ℕ) : ∀ (n : ℕ) (acc : List Bool), acc.length = base →
    (∀ i ≤ n, f i < base) →
    ((chain f base n).foldl wstep acc).getD (cp f base n) false =
      decide (∃ i ≤ n, acc.getD (f i) false = true) := by
  intro n
  induction n with
  | zero =>
    intro acc _ _
    cases h : acc.getD (f 0) false <;> simp [chain, cp]
  | succ n ih =>
    intro acc hacc hf
    have hW : ((chain f base n).foldl wstep acc).length = base + n := by
      rw [len]; simp [chain, hacc]
    have hc : cp f base (n + 1) = ((chain f base n).foldl wstep acc).length := by
      rw [hW]; simp [cp]
    simp only [chain, List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [← chain, hc, last, keep _ _ (f (n + 1)) (by rw [hacc]; exact hf _ le_rfl),
      ih acc hacc (fun i hi => hf i (by omega))]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨n + 1, le_rfl, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_or_ge i (n + 1) with h1 | h1
      · exact Or.inl ⟨i, by omega, h⟩
      · obtain rfl : i = n + 1 := by omega
        exact Or.inr h

def pairs (ws : ℕ → ℕ) (n : ℕ) : List Gate :=
  (List.range n).map fun i => orG (ws (2 * i)) (ws (2 * i + 1))

lemma pairs_spec (ws : ℕ → ℕ) : ∀ (n : ℕ) (acc : List Bool),
    (∀ i < n, ws (2 * i) < acc.length ∧ ws (2 * i + 1) < acc.length) →
    ∀ i < n, ((pairs ws n).foldl wstep acc).getD (acc.length + i) false =
      (acc.getD (ws (2 * i)) false || acc.getD (ws (2 * i + 1)) false) := by
  intro n
  induction n with
  | zero => intro _ _ i hi; omega
  | succ n ih =>
    intro acc hws i hi
    have hW : ((pairs ws n).foldl wstep acc).length = acc.length + n := by
      rw [len]; simp [pairs]
    simp only [pairs, List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [← pairs]
    rcases Nat.lt_or_ge i n with h1 | h1
    · rw [wstep, List.getD_append _ _ _ _ (by omega), ih acc (fun i hi => hws i (by omega)) i h1]
    · rw [show i = n by omega, ← hW, last, keep _ _ _ (hws n (by omega)).1, keep _ _ _ (hws n (by omega)).2]

def enc : ℕ → (ℕ → ℕ) → ℕ → List Gate × (ℕ → ℕ)
  | 0, _, _ => ([], fun _ => 0)
  | m + 1, ws, base =>
    (chain (fun i => ws (2 * i + 1)) base (2 ^ m - 1) ++ pairs ws (2 ^ m) ++
        (enc m (fun i => base + (2 ^ m - 1) + i) (base + (2 ^ m - 1) + 2 ^ m)).1,
      fun t => if t = 0 then cp (fun i => ws (2 * i + 1)) base (2 ^ m - 1) else
        (enc m (fun i => base + (2 ^ m - 1) + i) (base + (2 ^ m - 1) + 2 ^ m)).2 (t - 1))

lemma enc_len : ∀ (m : ℕ) (ws : ℕ → ℕ) (base : ℕ),
    (enc m ws base).1.length + m + 2 = 2 ^ (m + 1) := by
  intro m
  induction m with
  | zero => intro _ _; simp [enc]
  | succ m ih =>
    intro ws base
    have h := ih (fun i => base + (2 ^ m - 1) + i) (base + (2 ^ m - 1) + 2 ^ m)
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    have h3 : 2 ^ (m + 1 + 1) = 2 * 2 ^ (m + 1) := by ring
    simp only [enc, List.length_append, chain, pairs, List.length_map, List.length_range]
    omega

lemma enc_gates : ∀ (m : ℕ) (ws : ℕ → ℕ) (base : ℕ),
    ∀ g ∈ (enc m ws base).1, g.op = GateOp.or ∧ g.inputs.length = 2 := by
  intro m
  induction m with
  | zero => intro _ _ g hg; simp [enc] at hg
  | succ m ih =>
    intro ws base g hg
    simp only [enc, List.mem_append, chain, pairs, List.mem_map] at hg
    rcases hg with (⟨i, _, rfl⟩ | ⟨i, _, rfl⟩) | hg
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact ih _ _ g hg

lemma enc_spec : ∀ (m : ℕ) (ws : ℕ → ℕ) (base : ℕ) (acc : List Bool) (j : ℕ),
    acc.length = base → j < 2 ^ m →
    (∀ i < 2 ^ m, ws i < base ∧ acc.getD (ws i) false = decide (i = j)) →
    ∀ t < m, (enc m ws base).2 t < base + (enc m ws base).1.length ∧
      ((enc m ws base).1.foldl wstep acc).getD ((enc m ws base).2 t) false = j.testBit t := by
  intro m
  induction m with
  | zero => intro _ _ _ _ _ _ _ t ht; omega
  | succ m ih =>
    intro ws base acc j hacc hj hws t ht
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    have hW1 : ((chain (fun i => ws (2 * i + 1)) base (2 ^ m - 1)).foldl wstep acc).length =
        base + (2 ^ m - 1) := by
      rw [len]; simp [chain, hacc]
    have hW2 : ((pairs ws (2 ^ m)).foldl wstep
        ((chain (fun i => ws (2 * i + 1)) base (2 ^ m - 1)).foldl wstep acc)).length =
        base + (2 ^ m - 1) + 2 ^ m := by
      rw [len, hW1]; simp [pairs]
    simp only [enc, List.foldl_append, List.length_append]
    rcases t with _ | t
    · simp only [↓reduceIte]
      have hcp : cp (fun i => ws (2 * i + 1)) base (2 ^ m - 1) < base + (2 ^ m - 1) := by
        unfold cp
        split_ifs with h
        · have := (hws 1 (by omega)).1; simp only [Nat.mul_zero, Nat.zero_add]; omega
        · omega
      constructor
      · simp only [chain, pairs, List.length_map, List.length_range]; omega
      rw [keep _ _ _ (by omega), keep _ _ _ (by omega),
        chain_spec _ base _ acc hacc (fun i hi => (hws _ (by omega)).1), Nat.testBit_zero]
      apply decide_eq_decide.mpr
      constructor
      · rintro ⟨i, hi, h⟩
        rw [(hws _ (by omega)).2] at h
        simp at h; omega
      · intro h
        exact ⟨j / 2, by omega, by rw [(hws _ (by omega)).2]; simp; omega⟩
    · simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      obtain ⟨hb, hv⟩ := ih (fun i => base + (2 ^ m - 1) + i) (base + (2 ^ m - 1) + 2 ^ m) _ (j / 2)
        hW2 (by omega) (fun i hi => ⟨by omega, by
          rw [← hW1, pairs_spec ws _ _ (fun i hi => by
              rw [hW1]; exact ⟨by have := (hws (2 * i) (by omega)).1; omega,
                by have := (hws (2 * i + 1) (by omega)).1; omega⟩) i hi,
            keep _ _ _ (by rw [hacc]; exact (hws _ (by omega)).1),
            keep _ _ _ (by rw [hacc]; exact (hws _ (by omega)).1),
            (hws _ (by omega)).2, (hws _ (by omega)).2]
          apply Bool.eq_iff_iff.mpr
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          omega⟩) t (by omega)
      constructor
      · simp only [chain, pairs, List.length_map, List.length_range] at hb ⊢; omega
      · rw [hv, Nat.testBit_succ]

lemma oneEach_getD_left' {n m : ℕ} (u : Fin n) (v : Fin m) (i : Fin n) :
    (oneEach u v).getD i.val false = decide (i = u) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, i.isLt]

lemma oneEach_getD_right' {n m : ℕ} (u : Fin n) (v : Fin m) (j : Fin m) :
    (oneEach u v).getD (n + j.val) false = decide (j = v) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, j.isLt]

def remap (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

lemma sim (xs P : List Bool) (ρ : ℕ → ℕ)
    (hρ : ∀ (p : ℕ) (R : List Bool), (P ++ R).getD (ρ p) false = (xs ++ R).getD p false) :
    ∀ (gs : List Gate) (R : List Bool), ∃ R' : List Bool,
      gs.foldl wstep (xs ++ R) = xs ++ R' ∧ (gs.map (remap ρ)).foldl wstep (P ++ R) = P ++ R' := by
  intro gs
  induction gs with
  | nil => intro R; exact ⟨R, rfl, rfl⟩
  | cons g gs ih =>
    intro R
    have e1 : wstep (xs ++ R) g =
        xs ++ (R ++ [g.op.eval (g.inputs.map fun i => (xs ++ R).getD i false)]) := by
      simp [wstep]
    have e2 : wstep (P ++ R) (remap ρ g) =
        P ++ (R ++ [g.op.eval (g.inputs.map fun i => (xs ++ R).getD i false)]) := by
      simp only [wstep, remap, List.map_map, Function.comp_def, hρ, List.append_assoc]
    rw [List.foldl_cons, List.map_cons, List.foldl_cons, e1, e2]
    exact ih _

theorem testBit_tableIndex : ∀ (m : ℕ) (x : Fin m → Bool) (j : ℕ),
    (tableIndex x).testBit j = if h : j < m then x ⟨j, h⟩ else false := by
  intro m
  induction m with
  | zero => intro x j; simp [tableIndex]
  | succ m ih =>
    intro x j
    have hs : tableIndex x = (if x 0 = true then 1 else 0) + 2 * tableIndex (Fin.tail x) := by
      unfold tableIndex
      rw [Fin.sum_univ_succ, Finset.mul_sum]
      have h2 : (∑ i : Fin m, if x i.succ = true then 2 ^ ((i.succ : Fin (m + 1)) : ℕ) else 0)
          = ∑ i : Fin m, 2 * (if Fin.tail x i = true then 2 ^ (i : ℕ) else 0) :=
        Finset.sum_congr rfl (fun i _ => by
          by_cases hx : x i.succ = true <;> simp [hx, Fin.tail, pow_succ, mul_comm])
      rw [h2]
      simp
    rw [hs]
    cases j with
    | zero =>
      rw [dif_pos (by omega)]
      show _ = x 0
      cases hx : x 0 <;> simp [Nat.testBit_zero, Nat.add_mul_mod_self_left]
    | succ j =>
      rw [Nat.testBit_succ]
      have e : ((if x 0 = true then 1 else 0) + 2 * tableIndex (Fin.tail x)) / 2
          = tableIndex (Fin.tail x) := by
        split_ifs <;> omega
      rw [e, ih]
      by_cases hj : j < m
      · rw [dif_pos hj, dif_pos (by omega)]; rfl
      · rw [dif_neg hj, dif_neg (by omega)]

lemma ofNat_bits {k : ℕ} (u : Fin (2 ^ k)) (y : Fin k → Bool) (hy : ∀ i : Fin k, y i = u.val.testBit i) :
    Fin.ofNat (2 ^ k) (tableIndex y) = u := by
  apply Fin.ext
  rw [Fin.val_ofNat]
  have : tableIndex y = u.val := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [testBit_tableIndex]
    split_ifs with h
    · exact hy ⟨j, h⟩
    · exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le u.isLt
        (Nat.pow_le_pow_right (by omega) (by omega)))).symm
  rw [this, Nat.mod_eq_of_lt u.isLt]

theorem main (k l s : ℕ) (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool)
    (hC0 : HasCircuitSize (k + l) (adjFun A) s) : ∃ C : Circuit, FanInTwo C ∧
      C.size ≤ s + (2 * 2 ^ k - 2 - k) + (2 * 2 ^ l - 2 - l) ∧ Represents A C := by
  obtain ⟨C, hF, hsz, hC⟩ := hC0
  obtain ⟨EL, hEL⟩ : ∃ E, E = enc k (fun i => i) (2 ^ k + 2 ^ l) := ⟨_, rfl⟩
  obtain ⟨ER, hER⟩ : ∃ E, E = enc l (fun i => 2 ^ k + i) (2 ^ k + 2 ^ l + EL.1.length) := ⟨_, rfl⟩
  have hLl : EL.1.length + k + 2 = 2 ^ (k + 1) := by rw [hEL]; exact enc_len _ _ _
  have hRl : ER.1.length + l + 2 = 2 ^ (l + 1) := by rw [hER]; exact enc_len _ _ _
  have hk2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have hl2 : 2 ^ (l + 1) = 2 * 2 ^ l := by ring
  have hkk : k < 2 ^ k := Nat.lt_two_pow_self
  have hll : l < 2 ^ l := Nat.lt_two_pow_self
  let ρ : ℕ → ℕ := fun p => if p < k + l then (if p < k then EL.2 p else ER.2 (p - k))
    else p + (2 ^ k + 2 ^ l + EL.1.length + ER.1.length - (k + l))
  refine ⟨⟨EL.1 ++ ER.1 ++ C.gates.map (remap ρ), ρ C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_map] at hg
    rcases hg with (hg | hg) | ⟨g', hg', rfl⟩
    · obtain ⟨h1, h2⟩ := enc_gates _ _ _ g (by rw [hEL] at hg; exact hg); rw [h1]; exact ⟨by simp, by omega⟩
    · obtain ⟨h1, h2⟩ := enc_gates _ _ _ g (by rw [hER] at hg; exact hg); rw [h1]; exact ⟨by simp, by omega⟩
    · exact ⟨(hF g' hg').1, by simpa [remap] using (hF g' hg').2⟩
  · simp only [Circuit.size, List.length_append, List.length_map] at hsz ⊢
    omega
  · intro u v
    let x : Fin (k + l) → Bool := fun i =>
      if i.val < k then u.val.testBit i.val else v.val.testBit (i.val - k)
    have hadj : adjFun A x = A u v := by
      unfold adjFun
      rw [ofNat_bits u _ (fun i => by simp [x]), ofNat_bits v _ (fun j => by simp [x])]
    have hlen : (oneEach u v).length = 2 ^ k + 2 ^ l := by simp [oneEach]
    obtain ⟨WL, hWL⟩ : ∃ W, W = EL.1.foldl wstep (oneEach u v) := ⟨_, rfl⟩
    have hWLl : WL.length = 2 ^ k + 2 ^ l + EL.1.length := by rw [hWL, len, hlen]
    obtain ⟨P, hP⟩ : ∃ P, P = ER.1.foldl wstep WL := ⟨_, rfl⟩
    have hPl : P.length = 2 ^ k + 2 ^ l + EL.1.length + ER.1.length := by rw [hP, len, hWLl]
    have hbw : ∀ (p : ℕ) (hp : p < k + l), (if p < k then EL.2 p else ER.2 (p - k)) < P.length ∧
        P.getD (if p < k then EL.2 p else ER.2 (p - k)) false = x ⟨p, hp⟩ := by
      intro p hp
      by_cases hk : p < k
      · simp only [if_pos hk, x]
        have hs := enc_spec k (fun i => i) (2 ^ k + 2 ^ l) (oneEach u v) u.val hlen
          u.isLt (fun i hi => ⟨by omega, by
            have := oneEach_getD_left' u v ⟨i, hi⟩; simpa [Fin.ext_iff] using this⟩) p hk
        rw [← hEL] at hs
        obtain ⟨hb, hv⟩ := hs
        refine ⟨by omega, ?_⟩
        rw [hP, keep _ _ _ (by omega), hWL, hv]
      · simp only [if_neg hk, x]
        have hs := enc_spec l (fun i => 2 ^ k + i) (2 ^ k + 2 ^ l + EL.1.length) WL
          v.val hWLl v.isLt (fun i hi => ⟨by omega, by
            rw [hWL, keep _ _ _ (by omega)]
            have := oneEach_getD_right' u v ⟨i, hi⟩; simpa [Fin.ext_iff] using this⟩) (p - k)
          (by omega)
        rw [← hER] at hs
        obtain ⟨hb, hv⟩ := hs
        refine ⟨by omega, ?_⟩
        rw [hP, hv]
    have hρ : ∀ (p : ℕ) (R : List Bool), (P ++ R).getD (ρ p) false = (List.ofFn x ++ R).getD p false := by
      intro p R
      by_cases hp : p < k + l
      · simp only [ρ, if_pos hp]
        obtain ⟨hb1, hb2⟩ := hbw p hp
        rw [List.getD_append _ _ _ _ hb1, hb2, List.getD_append _ _ _ _ (by simpa using hp)]
        simp [List.getD_eq_getElem?_getD, hp]
      · simp only [ρ, if_neg hp]
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by simp; omega)]
        congr 1
        simp only [List.length_ofFn]
        omega
    obtain ⟨R', h1, h2⟩ := sim (List.ofFn x) P ρ hρ C.gates []
    rw [List.append_nil] at h1 h2
    rw [← hadj, ← hC x]
    show ((EL.1 ++ ER.1 ++ C.gates.map (remap ρ)).foldl wstep (oneEach u v)).getD (ρ C.output) false =
      (C.gates.foldl wstep (List.ofFn x)).getD C.output false
    rw [List.foldl_append, List.foldl_append, ← hWL, ← hP, h2, h1, hρ]

end PEqualNP.Outside.L_meta_19117_aux

theorem PEqualNP.Outside.L_meta_19117 : ∀ (k l s : ℕ) (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool), PEqualNP.MetaComplexity.HasCircuitSize (k + l) (PEqualNP.Represents.adjFun A) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s + (2 * 2 ^ k - 2 - k) + (2 * 2 ^ l - 2 - l) ∧ PEqualNP.Represents.Represents A C :=
  PEqualNP.Outside.L_meta_19117_aux.main
