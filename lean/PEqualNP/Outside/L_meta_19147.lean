import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19147_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    show (W gs (step w g)).length = _
    rw [ih]; simp [step]; omega

theorem getD_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    show (W gs (step w g)).getD i false = _
    rw [ih (step w g) i (by simp [step]; omega)]
    exact getD_lt w _ i hi

def sh (L k i : ℕ) : ℕ := if i < L then i else i + k

def shG (L k : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sh L k)⟩

theorem W_shift (L k : ℕ) (gs : List Gate) : ∀ (v w : List Bool), L ≤ w.length →
    v.length = w.length + k → (∀ i, v.getD (sh L k i) false = w.getD i false) →
    ∀ i, (W (gs.map (shG L k)) v).getD (sh L k i) false = (W gs w).getD i false := by
  induction gs with
  | nil => intro v w _ _ h; exact h
  | cons g gs ih =>
    intro v w hL hlen h
    apply ih (step v (shG L k g)) (step w g)
    · simp [step]; omega
    · simp [step]; omega
    · intro i
      have hval : (shG L k g).op.eval ((shG L k g).inputs.map fun i => v.getD i false) =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp only [shG, List.map_map]; congr 1; apply List.map_congr_left; intro j _; exact h j
      unfold step
      rcases lt_trichotomy i w.length with hi | hi | hi
      · have : sh L k i < v.length := by unfold sh; split <;> omega
        rw [getD_lt _ _ _ this, getD_lt _ _ _ hi, h]
      · subst hi
        have : sh L k w.length = v.length := by unfold sh; split <;> omega
        rw [this, hval]; simp [List.getD]
      · rw [getD_ge _ _ (by simp; unfold sh; split <;> omega), getD_ge _ _ (by simp; omega)]

theorem tail4 (V : List Bool) (N a b : ℕ) (hN : V.length = N) (ha : a < N ∨ N + 4 ≤ a)
    (hb : b < N ∨ N + 4 ≤ b) :
    (W [⟨GateOp.or, [a, b]⟩, ⟨GateOp.and, [a, b]⟩, ⟨GateOp.not, [N + 1]⟩,
      ⟨GateOp.and, [N, N + 2]⟩] V).getD (N + 3) false =
      xor (V.getD a false) (V.getD b false) := by
  have key : ∀ c, (c < N ∨ N + 4 ≤ c) → ∀ t : List Bool, t.length ≤ 3 →
      (V ++ t).getD c false = V.getD c false := by
    intro c hc t ht
    rcases hc with hc | hc
    · exact getD_lt _ _ _ (by omega)
    · rw [getD_ge _ _ (by simp; omega), getD_ge _ _ (by omega)]
  have ka := key a ha
  have kb := key b hb
  subst hN
  simp only [List.getD_eq_getElem?_getD] at ka kb
  simp [W, step, GateOp.eval, ka, kb]
  generalize V[a]?.getD false = p
  generalize V[b]?.getD false = q
  cases p <;> cases q <;> rfl

end PEqualNP.Outside.L_meta_19147_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_19147_aux in
theorem PEqualNP.Outside.L_meta_19147 : ∀ (n m s t : ℕ) (A B : Fin n → Fin m → Bool),
    PEqualNP.Represents.RepSizeAtMost A s → PEqualNP.Represents.RepSizeAtMost B t →
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s + t + 4 ∧
      PEqualNP.Represents.Represents (fun u v => xor (A u v) (B u v)) C := by
  intro n m s t A B ⟨C1, hm1, hs1, hr1⟩ ⟨C2, hm2, hs2, hr2⟩
  have hk : ∀ (u : Fin n) (v : Fin m), (PEqualNP.Represents.oneEach u v).length = n + m := by
    intro u v; simp [PEqualNP.Represents.oneEach]
  refine ⟨⟨C1.gates ++ C2.gates.map (shG (n + m) C1.gates.length) ++
    [⟨GateOp.or, [if C1.output < n + m + C1.gates.length then C1.output
        else n + m + C1.gates.length + C2.gates.length + 4,
      if C2.output < n + m + C2.gates.length then sh (n + m) C1.gates.length C2.output
        else n + m + C1.gates.length + C2.gates.length + 4]⟩,
     ⟨GateOp.and, [if C1.output < n + m + C1.gates.length then C1.output
        else n + m + C1.gates.length + C2.gates.length + 4,
      if C2.output < n + m + C2.gates.length then sh (n + m) C1.gates.length C2.output
        else n + m + C1.gates.length + C2.gates.length + 4]⟩,
     ⟨GateOp.not, [n + m + C1.gates.length + C2.gates.length + 1]⟩,
     ⟨GateOp.and, [n + m + C1.gates.length + C2.gates.length,
       n + m + C1.gates.length + C2.gates.length + 2]⟩],
    n + m + C1.gates.length + C2.gates.length + 3⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with (h | ⟨g', h', rfl⟩) | h | h | h | h
    · obtain ⟨h1, h2⟩ := hm1 g h
      refine ⟨?_, h2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 ⊢; tauto
    · obtain ⟨h1, h2⟩ := hm2 g' h'
      refine ⟨?_, by simpa [shG] using h2⟩
      simp only [shG, Set.mem_insert_iff, Set.mem_singleton_iff] at h1 ⊢; tauto
    all_goals (subst h; simp)
  · simp only [Circuit.size] at hs1 hs2 ⊢; simp; omega
  · intro u v
    beta_reduce
    rw [← hr1 u v, ← hr2 u v]
    have hx := hk u v
    generalize PEqualNP.Represents.oneEach u v = x at hx ⊢
    show (W _ x).getD _ false = xor ((W C1.gates x).getD C1.output false)
      ((W C2.gates x).getD C2.output false)
    rw [W_append, W_append]
    have h1 := W_length C1.gates x
    have h2 := W_length (C2.gates.map (shG (n + m) C1.gates.length)) (W C1.gates x)
    rw [h1, List.length_map] at h2
    have hrel : ∀ i, (W C1.gates x).getD (sh (n + m) C1.gates.length i) false = x.getD i false := by
      intro i; unfold sh; split
      · exact W_prefix _ _ _ (by omega)
      · rw [getD_ge _ _ (by omega), getD_ge _ _ (by omega)]
    have hS := W_shift (n + m) C1.gates.length C2.gates (W C1.gates x) x (by omega) (by omega) hrel
    rw [tail4 _ _ _ _ (by omega) (by split <;> omega)
      (by split <;> [(unfold sh; split <;> omega); omega])]
    congr 1
    · split
      · exact W_prefix _ _ _ (by omega)
      · rw [getD_ge _ _ (by omega), getD_ge _ _ (by omega)]
    · split
      · exact hS _
      · rw [getD_ge _ _ (by omega), getD_ge _ _ (by rw [W_length]; omega)]
