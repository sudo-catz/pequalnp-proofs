import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19062_aux

namespace P18183

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_stepWire_len (gs : List Gate) :
    ∀ xs : List Bool, (gs.foldl stepWire xs).length = xs.length + gs.length := by
  induction gs with
  | nil => intro xs; simp
  | cons g gs ih =>
      intro xs
      simp only [List.foldl_cons, List.length_cons, ih, stepWire, List.length_append, List.length_nil]
      omega

theorem foldl_stepWire_getD_lt (gs : List Gate) :
    ∀ (xs : List Bool) (i : ℕ), i < xs.length →
      (gs.foldl stepWire xs).getD i false = xs.getD i false := by
  induction gs with
  | nil => intro xs i _; rfl
  | cons g gs ih =>
      intro xs i hi
      simp only [List.foldl_cons]
      rw [ih (stepWire xs g) i (by simp [stepWire]; omega)]
      exact List.getD_append _ _ _ _ hi

theorem getD_append_add (p w : List Bool) (i : ℕ) :
    (p ++ w).getD (i + p.length) false = w.getD i false := by
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by omega)]
    rw [List.getD_eq_getElem _ _ hi]
    simp
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_self (l : List Bool) (x : Bool) (n : ℕ) (h : l.length = n) :
    (l ++ [x]).getD n false = x := by
  subst h; simp

-- Helper: chain of OR gates over a list of wire indices of length >= 1.
-- Given base index `base` (current wire count) and a non-empty list of wire indices `ws`,
-- `orChainGates base ws` appends `ws.length - 1` OR gates computing the OR of `ws`,
-- whose output wire is `orChainOut base ws`.
def orChainAux : ℕ → ℕ → List ℕ → List Gate
  | _, _, [] => []
  | base, acc, x :: xs => ⟨.or, [acc, x]⟩ :: orChainAux (base + 1) base xs

def orChainGates (base : ℕ) : List ℕ → List Gate
  | [] => []
  | x :: xs => orChainAux base x xs

def orChainOut (base : ℕ) : List ℕ → ℕ
  | [] => 0
  | [x] => x
  | _ :: xs => base + xs.length - 1

theorem orChainAux_len (base acc : ℕ) (xs : List ℕ) :
    (orChainAux base acc xs).length = xs.length := by
  induction xs generalizing base acc with
  | nil => rfl
  | cons x xs ih => simp [orChainAux, ih]

theorem orChainGates_len (base : ℕ) (ws : List ℕ) :
    (orChainGates base ws).length = ws.length - 1 := by
  cases ws with
  | nil => rfl
  | cons x xs => simp [orChainGates, orChainAux_len]

theorem orChainAux_mono (base acc : ℕ) (xs : List ℕ) :
    ∀ g ∈ orChainAux base acc xs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction xs generalizing base acc with
  | nil => intro g hg; cases hg
  | cons x xs ih =>
      intro g hg
      simp only [orChainAux, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact ⟨by simp, by simp⟩
      · exact ih _ _ g hg

theorem orChainGates_mono (base : ℕ) (ws : List ℕ) :
    ∀ g ∈ orChainGates base ws, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  cases ws with
  | nil => intro g hg; cases hg
  | cons x xs => exact orChainAux_mono base x xs

theorem foldl_orChainAux (base acc : ℕ) (xs : List ℕ) :
    ∀ (w : List Bool), w.length = base →
      (∀ x ∈ xs, x < base) →
      acc < base →
      ((orChainAux base acc xs).foldl stepWire w).getD (if xs.isEmpty then acc else base + xs.length - 1) false =
        xs.foldl (fun b x => b || w.getD x false) (w.getD acc false) := by
  induction xs generalizing base acc with
  | nil =>
      intro w _ _ _
      simp [orChainAux]
  | cons x xs ih =>
      intro w hlen hxs hacc
      simp only [orChainAux, List.foldl_cons, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        List.length_cons]
      have hx : x < base := hxs x List.mem_cons_self
      let w' := stepWire w ⟨.or, [acc, x]⟩
      have hw'_len : w'.length = base + 1 := by simp [w', stepWire, hlen]
      have hw'_acc : w'.getD base false = (w.getD acc false || w.getD x false) := by
        simp only [w', stepWire, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false, getD_snoc_self w _ base hlen]
      have hxs' : ∀ y ∈ xs, y < base + 1 := fun y hy => by
        have := hxs y (List.mem_cons_of_mem _ hy); omega
      have hsub := ih (base + 1) base w' hw'_len hxs' (by omega)
      have hfold_eq : xs.foldl (fun b y => b || w'.getD y false) (w'.getD base false) =
          xs.foldl (fun b y => b || w.getD y false) (w.getD acc false || w.getD x false) := by
        rw [hw'_acc]
        have hcong : ∀ (l : List ℕ) (b0 : Bool), (∀ y ∈ l, y < base) →
            l.foldl (fun b y => b || w'.getD y false) b0 =
            l.foldl (fun b y => b || w.getD y false) b0 := by
          intro l
          induction l with
          | nil => intro b0 _; rfl
          | cons y ys ihl =>
              intro b0 hyl
              simp only [List.foldl_cons]
              have hy : y < base := hyl y List.mem_cons_self
              have hget : w'.getD y false = w.getD y false := by
                simpa [w', stepWire] using List.getD_append w _ false y (by omega)
              rw [hget]
              exact ihl _ (fun z hz => hyl z (List.mem_cons_of_mem _ hz))
        exact hcong xs _ (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
      cases xs with
      | nil =>
          simp only [List.isEmpty_nil, ↓reduceIte, List.length_nil] at hsub ⊢
          have hidx : base + 1 - 1 = base := by omega
          rw [hidx, hsub, hfold_eq]
      | cons y ys =>
          simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.length_cons] at hsub ⊢
          have hidx : base + (ys.length + 1 + 1) - 1 = base + 1 + (ys.length + 1) - 1 := by omega
          rw [hidx, hsub, hfold_eq]

theorem foldl_orChainGates (base : ℕ) (ws : List ℕ) (w : List Bool)
    (hlen : w.length = base) (hne : ws ≠ []) (hlt : ∀ x ∈ ws, x < base) :
    ((orChainGates base ws).foldl stepWire w).getD (orChainOut base ws) false =
      ws.any (fun x => w.getD x false) := by
  cases ws with
  | nil => exact absurd rfl hne
  | cons x xs =>
      have h1 := foldl_orChainAux base x xs w hlen
        (fun y hy => hlt y (List.mem_cons_of_mem _ hy)) (hlt x List.mem_cons_self)
      have hout : orChainOut base (x :: xs) = if xs.isEmpty then x else base + xs.length - 1 := by
        cases xs <;> simp [orChainOut]
      rw [orChainGates, hout, h1]
      have hany : ∀ (l : List ℕ) (b : Bool),
          l.foldl (fun acc y => acc || w.getD y false) b = (b || l.any (fun y => w.getD y false)) := by
        intro l
        induction l with
        | nil => intro b; simp
        | cons y ys ihl =>
            intro b
            simp only [List.foldl_cons, List.any_cons, ihl, Bool.or_assoc]
      rw [hany, List.any_cons]

-- Threshold-2 circuit on a list of wires `xs` of length >= 2, starting at wire index `base`.
-- Cost: 3 * xs.length - 5 gates!
-- For [a, b]: 1 gate: AND(a, b), out = base.
-- For a :: b :: c :: rest:
--   gate base: OR(a, b) = t1
--   gate base+1: AND(a, b) = t2
--   then `t2Loop (base + 2) t1 t2 (c :: rest)`:
--     on [z]: AND(t1, z) at p, OR(t2, p) at p+1 -> out = p+1 (2 gates)
--     on z :: zs (zs non-empty):
--       p: OR(t1, z)
--       p+1: AND(t1, z)
--       p+2: OR(t2, p+1)
--       recurse with base=p+3, t1=p, t2=p+2, zs! (3 gates)
def t2Loop : ℕ → ℕ → ℕ → List ℕ → List Gate
  | _, _, _, [] => []
  | p, t1, t2, [z] => [⟨.and, [t1, z]⟩, ⟨.or, [t2, p]⟩]
  | p, t1, t2, z :: y :: ys =>
      ⟨.or, [t1, z]⟩ :: ⟨.and, [t1, z]⟩ :: ⟨.or, [t2, p + 1]⟩ ::
        t2Loop (p + 3) p (p + 2) (y :: ys)

def t2Gates (base : ℕ) : List ℕ → List Gate
  | [] => []
  | [_] => []
  | [a, b] => [⟨.and, [a, b]⟩]
  | a :: b :: c :: rest => ⟨.or, [a, b]⟩ :: ⟨.and, [a, b]⟩ :: t2Loop (base + 2) base (base + 1) (c :: rest)

def t2Out (base : ℕ) (xs : List ℕ) : ℕ :=
  base + (3 * xs.length - 5) - 1

theorem t2Loop_len (p t1 t2 : ℕ) : ∀ zs : List ℕ, zs ≠ [] →
    (t2Loop p t1 t2 zs).length = 3 * zs.length - 1
  | [], h => absurd rfl h
  | [_], _ => by simp [t2Loop]
  | _ :: y :: ys, _ => by
      have ih := t2Loop_len (p + 3) p (p + 2) (y :: ys) (by simp)
      simp only [t2Loop, List.length_cons, ih]
      omega

theorem t2Gates_len (base : ℕ) (xs : List ℕ) (h : 2 ≤ xs.length) :
    (t2Gates base xs).length = 3 * xs.length - 5 := by
  match xs with
  | [] => simp at h
  | [_] => simp at h
  | [_, _] => simp [t2Gates]
  | _ :: _ :: c :: rest =>
      have hl := t2Loop_len (base + 2) base (base + 1) (c :: rest) (by simp)
      simp only [t2Gates, List.length_cons, hl]
      omega

theorem t2Loop_mono (p t1 t2 : ℕ) : ∀ zs : List ℕ,
    ∀ g ∈ t2Loop p t1 t2 zs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2
  | [], g, hg => by cases hg
  | [_], g, hg => by
      simp only [t2Loop, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl <;> exact ⟨by simp, by simp⟩
  | _ :: y :: ys, g, hg => by
      simp only [t2Loop, List.mem_cons] at hg
      rcases hg with rfl | rfl | rfl | hg
      · exact ⟨by simp, by simp⟩
      · exact ⟨by simp, by simp⟩
      · exact ⟨by simp, by simp⟩
      · exact t2Loop_mono (p + 3) p (p + 2) (y :: ys) g hg

theorem t2Gates_mono (base : ℕ) (xs : List ℕ) :
    ∀ g ∈ t2Gates base xs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  match xs with
  | [] => intro g hg; cases hg
  | [_] => intro g hg; cases hg
  | [_, _] =>
      intro g hg
      simp only [t2Gates, List.mem_cons, List.not_mem_nil, or_false] at hg
      subst hg; exact ⟨by simp, by simp⟩
  | _ :: _ :: c :: rest =>
      intro g hg
      simp only [t2Gates, List.mem_cons] at hg
      rcases hg with rfl | rfl | hg
      · exact ⟨by simp, by simp⟩
      · exact ⟨by simp, by simp⟩
      · exact t2Loop_mono (base + 2) base (base + 1) (c :: rest) g hg

theorem t1_step_bool (cnt : ℕ) (b : Bool) :
    (decide (1 ≤ cnt) || b) = decide (1 ≤ cnt + if b then 1 else 0) := by
  rcases cnt with _ | n <;> cases b <;> simp

theorem t2_step_bool (cnt : ℕ) (b : Bool) :
    (decide (2 ≤ cnt) || (decide (1 ≤ cnt) && b)) = decide (2 ≤ cnt + if b then 1 else 0) := by
  rcases cnt with _ | _ | n <;> cases b <;> simp

-- Semantic spec of t2Loop: given initial counts `c1 = (1 <= cnt)` at `t1` and `c2 = (2 <= cnt)` at `t2`,
-- computes `2 <= cnt + count true on zs` at wire `p + (3 * zs.length - 1) - 1`!
def countTrue (w : List Bool) (xs : List ℕ) : ℕ :=
  (xs.map fun i => w.getD i false).count true

theorem countTrue_cons (w : List Bool) (a : ℕ) (xs : List ℕ) :
    countTrue w (a :: xs) = (if w.getD a false then 1 else 0) + countTrue w xs := by
  unfold countTrue
  rw [List.map_cons, List.count_cons]
  cases w.getD a false <;> simp [Nat.add_comm]

theorem countTrue_nil (w : List Bool) : countTrue w [] = 0 := rfl

theorem t2Loop_eval (p t1 t2 : ℕ) :
    ∀ (zs : List ℕ) (hne : zs ≠ []) (w : List Bool) (cnt : ℕ),
      w.length = p →
      t1 < p → t2 < p →
      (∀ z ∈ zs, z < p) →
      w.getD t1 false = decide (1 ≤ cnt) →
      w.getD t2 false = decide (2 ≤ cnt) →
      ((t2Loop p t1 t2 zs).foldl stepWire w).getD (p + (3 * zs.length - 1) - 1) false =
        decide (2 ≤ cnt + countTrue w zs)
  | [], hne, _, _, _, _, _, _, _, _ => absurd rfl hne
  | [z], _, w, cnt, hlen, ht1, ht2, hzs, h1, h2 => by
      have hz : z < p := hzs z List.mem_cons_self
      let w1 := stepWire w ⟨.and, [t1, z]⟩
      let w2 := stepWire w1 ⟨.or, [t2, p]⟩
      have hw1_len : w1.length = p + 1 := by simp [w1, stepWire, hlen]
      have hw1_p : w1.getD p false = (decide (1 ≤ cnt) && w.getD z false) := by
        simp only [w1, stepWire, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, getD_snoc_self w _ p hlen, h1]
      have hw1_t2 : w1.getD t2 false = decide (2 ≤ cnt) := by
        rw [show w1.getD t2 false = w.getD t2 false from List.getD_append w _ false t2 (by omega), h2]
      have hidx : p + (3 * [z].length - 1) - 1 = p + 1 := by simp
      simp only [t2Loop, List.foldl_cons, List.foldl_nil, hidx]
      change w2.getD (p + 1) false = decide (2 ≤ cnt + countTrue w [z])
      have hw2_out : w2.getD (p + 1) false = (decide (2 ≤ cnt) || (decide (1 ≤ cnt) && w.getD z false)) := by
        simp only [w2, stepWire, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false, getD_snoc_self w1 _ (p + 1) hw1_len, hw1_t2, hw1_p]
      rw [hw2_out, t2_step_bool]
      have hct : countTrue w [z] = if w.getD z false then 1 else 0 := by
        rw [countTrue_cons, countTrue_nil]; omega
      rw [hct]
  | z :: y :: ys, _, w, cnt, hlen, ht1, ht2, hzs, h1, h2 => by
      have hz : z < p := hzs z List.mem_cons_self
      let w1 := stepWire w ⟨.or, [t1, z]⟩
      let w2 := stepWire w1 ⟨.and, [t1, z]⟩
      let w3 := stepWire w2 ⟨.or, [t2, p + 1]⟩
      have hw1_len : w1.length = p + 1 := by simp [w1, stepWire, hlen]
      have hw2_len : w2.length = p + 2 := by simp [w2, stepWire, hw1_len]
      have hw3_len : w3.length = p + 3 := by simp [w3, stepWire, hw2_len]
      have hw1_lt : ∀ i < p, w1.getD i false = w.getD i false := fun i hi =>
        List.getD_append w _ false i (by omega)
      have hw2_lt : ∀ i < p + 1, w2.getD i false = w1.getD i false := fun i hi =>
        List.getD_append w1 _ false i (by omega)
      have hw3_lt : ∀ i < p + 2, w3.getD i false = w2.getD i false := fun i hi =>
        List.getD_append w2 _ false i (by omega)
      have hw3_old : ∀ i < p, w3.getD i false = w.getD i false := fun i hi => by
        rw [hw3_lt i (by omega), hw2_lt i (by omega), hw1_lt i hi]
      have hw1_p : w1.getD p false = (decide (1 ≤ cnt) || w.getD z false) := by
        simp only [w1, stepWire, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false, getD_snoc_self w _ p hlen, h1]
      have hw2_p1 : w2.getD (p + 1) false = (decide (1 ≤ cnt) && w.getD z false) := by
        simp only [w2, stepWire, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, getD_snoc_self w1 _ (p + 1) hw1_len, hw1_lt t1 ht1, hw1_lt z hz, h1]
      have hw3_p : w3.getD p false = decide (1 ≤ cnt + (if w.getD z false then 1 else 0)) := by
        rw [hw3_lt p (by omega), hw2_lt p (by omega), hw1_p, t1_step_bool]
      have hw3_p2 : w3.getD (p + 2) false = decide (2 ≤ cnt + (if w.getD z false then 1 else 0)) := by
        have ht2' : w2.getD t2 false = decide (2 ≤ cnt) := by
          rw [hw2_lt t2 (by omega), hw1_lt t2 ht2, h2]
        simp only [w3, stepWire, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false, getD_snoc_self w2 _ (p + 2) hw2_len, ht2', hw2_p1, t2_step_bool]
      have ih := t2Loop_eval (p + 3) p (p + 2) (y :: ys) (by simp) w3
        (cnt + if w.getD z false then 1 else 0) hw3_len (by omega) (by omega)
        (fun q hq => by have := hzs q (List.mem_cons_of_mem _ hq); omega) hw3_p hw3_p2
      have hidx : p + (3 * (z :: y :: ys).length - 1) - 1 = (p + 3) + (3 * (y :: ys).length - 1) - 1 := by
        simp; omega
      have hct : countTrue w3 (y :: ys) = countTrue w (y :: ys) := by
        unfold countTrue
        congr 1
        apply List.map_congr_left
        intro q hq
        exact hw3_old q (hzs q (List.mem_cons_of_mem _ hq))
      have hct_cons : countTrue w (z :: y :: ys) = (if w.getD z false then 1 else 0) + countTrue w (y :: ys) :=
        countTrue_cons w z (y :: ys)
      simp only [t2Loop, List.foldl_cons, hidx]
      change ((t2Loop (p + 3) p (p + 2) (y :: ys)).foldl stepWire w3).getD
        ((p + 3) + (3 * (y :: ys).length - 1) - 1) false = _
      rw [ih, hct, hct_cons, Nat.add_assoc]

theorem or_eq_ge1 (ba bb : Bool) :
    (ba || bb) = decide (1 ≤ (if ba then 1 else 0) + (if bb then 1 else 0)) := by
  cases ba <;> cases bb <;> rfl

theorem and_eq_ge2 (ba bb : Bool) :
    (ba && bb) = decide (2 ≤ (if ba then 1 else 0) + (if bb then 1 else 0)) := by
  cases ba <;> cases bb <;> rfl

theorem t2Gates_eval (base : ℕ) (xs : List ℕ) (w : List Bool)
    (hlen : w.length = base) (h2 : 2 ≤ xs.length) (hlt : ∀ x ∈ xs, x < base) :
    ((t2Gates base xs).foldl stepWire w).getD (t2Out base xs) false =
      decide (2 ≤ countTrue w xs) := by
  match xs with
  | [] => simp at h2
  | [_] => simp at h2
  | [a, b] =>
      have hidx : t2Out base [a, b] = base := by simp [t2Out]
      rw [t2Gates, hidx, List.foldl_cons, List.foldl_nil]
      simp only [stepWire, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        id_eq, Bool.and_true, getD_snoc_self w _ base hlen]
      rw [countTrue_cons, countTrue_cons, countTrue_nil, Nat.add_zero]
      exact and_eq_ge2 _ _
  | a :: b :: c :: rest =>
      have ha : a < base := hlt a List.mem_cons_self
      have hb : b < base := hlt b (List.mem_cons_of_mem _ List.mem_cons_self)
      let w1 := stepWire w ⟨.or, [a, b]⟩
      let w2 := stepWire w1 ⟨.and, [a, b]⟩
      have hw1_len : w1.length = base + 1 := by simp [w1, stepWire, hlen]
      have hw2_len : w2.length = base + 2 := by simp [w2, stepWire, hw1_len]
      have hw1_lt : ∀ i < base, w1.getD i false = w.getD i false := fun i hi =>
        List.getD_append w _ false i (by omega)
      have hw2_lt : ∀ i < base + 1, w2.getD i false = w1.getD i false := fun i hi =>
        List.getD_append w1 _ false i (by omega)
      let cnt0 := (if w.getD a false then 1 else 0) + (if w.getD b false then 1 else 0)
      have hw2_b0 : w2.getD base false = decide (1 ≤ cnt0) := by
        rw [hw2_lt base (by omega)]
        simp only [w1, stepWire, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false, getD_snoc_self w _ base hlen]
        exact or_eq_ge1 _ _
      have hw2_b1 : w2.getD (base + 1) false = decide (2 ≤ cnt0) := by
        simp only [w2, stepWire, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, getD_snoc_self w1 _ (base + 1) hw1_len, hw1_lt a ha, hw1_lt b hb]
        exact and_eq_ge2 _ _
      have hloop := t2Loop_eval (base + 2) base (base + 1) (c :: rest) (by simp) w2 cnt0 hw2_len
        (by omega) (by omega)
        (fun q hq => by have := hlt q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)); omega)
        hw2_b0 hw2_b1
      have hidx : t2Out base (a :: b :: c :: rest) = (base + 2) + (3 * (c :: rest).length - 1) - 1 := by
        simp only [t2Out, List.length_cons]; omega
      have hct : countTrue w2 (c :: rest) = countTrue w (c :: rest) := by
        unfold countTrue
        congr 1
        apply List.map_congr_left
        intro q hq
        rw [hw2_lt q (by have := hlt q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)); omega),
            hw1_lt q (hlt q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)))]
      have hct_all : countTrue w (a :: b :: c :: rest) = cnt0 + countTrue w (c :: rest) := by
        rw [countTrue_cons, countTrue_cons]
        dsimp only [cnt0]; omega
      simp only [t2Gates, List.foldl_cons, hidx]
      change ((t2Loop (base + 2) base (base + 1) (c :: rest)).foldl stepWire w2).getD
        ((base + 2) + (3 * (c :: rest).length - 1) - 1) false = _
      rw [hloop, hct, hct_all]

-- Now assemble the r x c product crown circuit on 2*(r*c) inputs!
-- Stage 1 (rc gates): w[k] = u[k] | v[k] at wire 2*rc + k
def uvGates (rc : ℕ) : List Gate :=
  List.ofFn (fun k : Fin rc => ⟨.or, [k.1, rc + k.1]⟩)

-- Stage 2 (r*(c-1) gates): row ORs, each row i in Fin r ORs wires [2*rc + i*c + j | j in Fin c]
def rowWires (r c i : ℕ) : List ℕ :=
  (List.range c).map (fun j => 2 * (r * c) + i * c + j)

def rowBase (r c i : ℕ) : ℕ :=
  3 * (r * c) + i * (c - 1)

def rowGates (r c : ℕ) : List Gate :=
  (List.range r).flatMap (fun i => orChainGates (rowBase r c i) (rowWires r c i))

def rowOut (r c i : ℕ) : ℕ :=
  orChainOut (rowBase r c i) (rowWires r c i)

-- Stage 3 (c*(r-1) gates): col ORs, each col j in Fin c ORs wires [2*rc + i*c + j | i in Fin r]
def colWires (r c j : ℕ) : List ℕ :=
  (List.range r).map (fun i => 2 * (r * c) + i * c + j)

def colBase (r c j : ℕ) : ℕ :=
  3 * (r * c) + r * (c - 1) + j * (r - 1)

def colGates (r c : ℕ) : List Gate :=
  (List.range c).flatMap (fun j => orChainGates (colBase r c j) (colWires r c j))

def colOut (r c j : ℕ) : ℕ :=
  orChainOut (colBase r c j) (colWires r c j)

-- Stage 4 (3r - 5 gates): T_2^r on rowOuts
def t2RowBase (r c : ℕ) : ℕ :=
  3 * (r * c) + r * (c - 1) + c * (r - 1)

def rowOutList (r c : ℕ) : List ℕ :=
  (List.range r).map (rowOut r c)

def t2RowGates (r c : ℕ) : List Gate :=
  t2Gates (t2RowBase r c) (rowOutList r c)

def t2RowOut (r c : ℕ) : ℕ :=
  t2Out (t2RowBase r c) (rowOutList r c)

-- Stage 5 (3c - 5 gates): T_2^c on colOuts
def t2ColBase (r c : ℕ) : ℕ :=
  t2RowBase r c + (3 * r - 5)

def colOutList (r c : ℕ) : List ℕ :=
  (List.range c).map (colOut r c)

def t2ColGates (r c : ℕ) : List Gate :=
  t2Gates (t2ColBase r c) (colOutList r c)

def t2ColOut (r c : ℕ) : ℕ :=
  t2Out (t2ColBase r c) (colOutList r c)

-- Stage 6 (1 gate): OR(t2RowOut, t2ColOut)
def prodCrownGates (r c : ℕ) : List Gate :=
  uvGates (r * c) ++ rowGates r c ++ colGates r c ++ t2RowGates r c ++ t2ColGates r c ++
    [⟨.or, [t2RowOut r c, t2ColOut r c]⟩]

def prodCrownOut (r c : ℕ) : ℕ :=
  t2ColBase r c + (3 * c - 5)

def prodCrown (r c : ℕ) : Circuit :=
  ⟨prodCrownGates r c, prodCrownOut r c⟩

theorem rowGates_len (r c : ℕ) : (rowGates r c).length = r * (c - 1) := by
  unfold rowGates
  have : ∀ k, ((List.range k).flatMap (fun i => orChainGates (rowBase r c i) (rowWires r c i))).length = k * (c - 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [List.range_succ, List.flatMap_append, List.length_append, ih,
            List.flatMap_singleton, orChainGates_len]
        simp [rowWires]; ring
  exact this r

theorem colGates_len (r c : ℕ) : (colGates r c).length = c * (r - 1) := by
  unfold colGates
  have : ∀ k, ((List.range k).flatMap (fun j => orChainGates (colBase r c j) (colWires r c j))).length = k * (r - 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [List.range_succ, List.flatMap_append, List.length_append, ih,
            List.flatMap_singleton, orChainGates_len]
        simp [colWires]; ring
  exact this c

theorem prodCrown_size (r c : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) :
    (prodCrown r c).size ≤ 3 * r * c + 2 * (r + c) - 9 := by
  simp only [Circuit.size, prodCrown, prodCrownGates, List.length_append, List.length_cons, List.length_nil,
    uvGates, List.length_ofFn, rowGates_len, colGates_len, t2RowGates, t2ColGates]
  rw [t2Gates_len _ _ (by simp [rowOutList]; omega), t2Gates_len _ _ (by simp [colOutList]; omega)]
  simp only [rowOutList, colOutList, List.length_map, List.length_range]
  have h1 : r * (c - 1) + r = r * c := by
    calc r * (c - 1) + r = r * ((c - 1) + 1) := by ring
    _ = r * c := by rw [Nat.sub_add_cancel (by omega)]
  have h2 : c * (r - 1) + c = c * r := by
    calc c * (r - 1) + c = c * ((r - 1) + 1) := by ring
    _ = c * r := by rw [Nat.sub_add_cancel (by omega)]
  have h3 : c * r = r * c := Nat.mul_comm c r
  have h4 : 3 * r * c = 3 * (r * c) := by ring
  omega

theorem prodCrown_mono (r c : ℕ) : Monotone2 (prodCrown r c) := by
  intro g hg
  simp only [prodCrown, prodCrownGates, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with ((((hg | hg) | hg) | hg) | hg) | rfl
  · simp only [uvGates, List.mem_ofFn] at hg
    obtain ⟨_, rfl⟩ := hg; exact ⟨by simp, by simp⟩
  · simp only [rowGates, List.mem_flatMap] at hg
    obtain ⟨_, _, hg⟩ := hg; exact orChainGates_mono _ _ g hg
  · simp only [colGates, List.mem_flatMap] at hg
    obtain ⟨_, _, hg⟩ := hg; exact orChainGates_mono _ _ g hg
  · exact t2Gates_mono _ _ g hg
  · exact t2Gates_mono _ _ g hg
  · exact ⟨by simp, by simp⟩

-- Semantic evaluation on `oneEach u v`!
theorem oneEach_len (n : ℕ) (u v : Fin n) : (oneEach u v).length = 2 * n := by
  simp [oneEach]; omega

theorem oneEach_getD_left (n : ℕ) (u v : Fin n) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD i false = decide (i = u.1) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp; omega)]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  by_cases h : i = u.1
  · rw [decide_eq_true (Fin.ext h : (⟨i, hi⟩ : Fin n) = u), decide_eq_true h]
  · rw [decide_eq_false (fun he => h (congrArg Fin.val he)), decide_eq_false h]

theorem oneEach_getD_right (n : ℕ) (u v : Fin n) (i : ℕ) (hi1 : n ≤ i) (hi2 : i < 2 * n) :
    (oneEach u v).getD i false = decide (i - n = v.1) := by
  unfold oneEach
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by simp; omega)]
  simp only [List.length_ofFn, List.getElem_ofFn]
  have hj : i - n < n := by omega
  by_cases h : i - n = v.1
  · rw [decide_eq_true (Fin.ext h : (⟨i - n, hj⟩ : Fin n) = v), decide_eq_true h]
  · rw [decide_eq_false (fun he => h (congrArg Fin.val he)), decide_eq_false h]

def uvVal (n : ℕ) (u v : Fin n) (k : Fin n) : Bool :=
  decide (k.1 = u.1) || decide (k.1 = v.1)

theorem foldl_uvGates_take (n : ℕ) (u v : Fin n) :
    ∀ k ≤ n, ((uvGates n).take k).foldl stepWire (oneEach u v) =
      oneEach u v ++ (List.ofFn (uvVal n u v)).take k
  | 0, _ => by simp
  | k + 1, hk => by
      have ih := foldl_uvGates_take n u v k (by omega)
      have hlen_g : (uvGates n).length = n := by simp [uvGates]
      have hlen_v : (List.ofFn (uvVal n u v)).length = n := by simp
      rw [List.take_succ_eq_append_getElem (by omega), List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
      rw [List.take_succ_eq_append_getElem (by omega), ← List.append_assoc]
      simp only [stepWire, uvGates, List.getElem_ofFn, uvVal, GateOp.eval,
        List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      have hlen_oe := oneEach_len n u v
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      rw [oneEach_getD_left n u v k (by omega), oneEach_getD_right n u v (n + k) (by omega) (by omega)]
      have hsub : n + k - n = k := by omega
      rw [hsub]

theorem foldl_uvGates (n : ℕ) (u v : Fin n) :
    (uvGates n).foldl stepWire (oneEach u v) = oneEach u v ++ List.ofFn (uvVal n u v) := by
  have h := foldl_uvGates_take n u v n (Nat.le_refl n)
  rw [List.take_of_length_le (by simp [uvGates]), List.take_of_length_le (by simp)] at h
  exact h

theorem uv_wire_getD (n : ℕ) (u v : Fin n) (k : ℕ) (hk : k < n) :
    (oneEach u v ++ List.ofFn (uvVal n u v)).getD (2 * n + k) false =
      (decide (k = u.1) || decide (k = v.1)) := by
  have h := getD_append_add (oneEach u v) (List.ofFn (uvVal n u v)) k
  rw [oneEach_len] at h
  have hcomm : k + 2 * n = 2 * n + k := by omega
  rw [hcomm] at h
  rw [h, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  rfl

-- Row gates evaluation
theorem rowGates_prefix (r c : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) (u v : Fin (r * c)) :
    ∀ k ≤ r,
      let w0 := oneEach u v ++ List.ofFn (uvVal (r * c) u v)
      let wk := ((List.range k).flatMap (fun i => orChainGates (rowBase r c i) (rowWires r c i))).foldl stepWire w0
      wk.length = rowBase r c k ∧
      (∀ i < k, wk.getD (rowOut r c i) false = (decide (i = u.1 / c) || decide (i = v.1 / c))) ∧
      (∀ t < r * c, wk.getD (2 * (r * c) + t) false = (decide (t = u.1) || decide (t = v.1)))
  | 0, _ => by
      refine ⟨?_, fun i hi => by omega, fun t ht => uv_wire_getD (r * c) u v t ht⟩
      simp [oneEach_len, rowBase]; omega
  | k + 1, hk => by
      have ih := rowGates_prefix r c hr hc u v k (by omega)
      dsimp only at ih ⊢
      obtain ⟨hlen, hprev, huv⟩ := ih
      let w0 := oneEach u v ++ List.ofFn (uvVal (r * c) u v)
      let wk := ((List.range k).flatMap (fun i => orChainGates (rowBase r c i) (rowWires r c i))).foldl stepWire w0
      have hsplit : ((List.range (k + 1)).flatMap (fun i => orChainGates (rowBase r c i) (rowWires r c i))).foldl stepWire w0 =
          (orChainGates (rowBase r c k) (rowWires r c k)).foldl stepWire wk := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.foldl_append]
      rw [hsplit]
      have hne : rowWires r c k ≠ [] := by
        simp [rowWires]; omega
      have hlt : ∀ x ∈ rowWires r c k, x < rowBase r c k := by
        intro x hx
        simp only [rowWires, List.mem_map, List.mem_range] at hx
        obtain ⟨j, hj, rfl⟩ := hx
        have hkc : k * c + j < r * c := by
          calc k * c + j < k * c + c := by omega
          _ = (k + 1) * c := by ring
          _ ≤ r * c := Nat.mul_le_mul_right c (by omega)
        simp only [rowBase]; omega
      have heval := foldl_orChainGates (rowBase r c k) (rowWires r c k) wk hlen hne hlt
      have hlen' : ((orChainGates (rowBase r c k) (rowWires r c k)).foldl stepWire wk).length = rowBase r c (k + 1) := by
        rw [foldl_stepWire_len, hlen, orChainGates_len]
        simp only [rowWires, List.length_map, List.length_range, rowBase]
        rw [Nat.add_mul, Nat.one_mul]; omega
      refine ⟨hlen', ?_, ?_⟩
      · intro i hi
        by_cases hik : i < k
        · have hout_lt : rowOut r c i < rowBase r c k := by
            unfold rowOut rowWires
            cases hc0 : c with
            | zero => omega
            | succ c' =>
                cases c' with
                | zero => omega
                | succ c'' =>
                    simp only [List.range_succ_eq_map, List.map_cons, List.map_map, orChainOut,
                      List.length_cons, List.length_map, List.length_range, rowBase]
                    have hsub : c'' + 1 + 1 - 1 = c'' + 1 := by omega
                    rw [hsub]
                    have : (i + 1) * (c'' + 1) ≤ k * (c'' + 1) := Nat.mul_le_mul_right _ (by omega)
                    rw [Nat.add_mul, Nat.one_mul] at this
                    omega
          rw [foldl_stepWire_getD_lt _ wk _ (by rw [hlen]; exact hout_lt)]
          exact hprev i hik
        · have heq : i = k := by omega
          subst heq
          rw [rowOut, heval]
          simp only [rowWires, List.any_map]
          have hany : (List.range c).any (fun j => wk.getD (2 * (r * c) + i * c + j) false) =
              (decide (i = u.1 / c) || decide (i = v.1 / c)) := by
            apply Bool.eq_iff_iff.mpr
            simp only [List.any_eq_true, Function.comp_apply, List.mem_range, Bool.or_eq_true, decide_eq_true_eq]
            constructor
            · rintro ⟨j, hj, hbit⟩
              have hkc : i * c + j < r * c := by
                calc i * c + j < i * c + c := by omega
                _ = (i + 1) * c := by ring
                _ ≤ r * c := Nat.mul_le_mul_right c (by omega)
              have hadd : 2 * (r * c) + i * c + j = 2 * (r * c) + (i * c + j) := by omega
              rw [hadd, huv (i * c + j) hkc] at hbit
              simp only [Bool.or_eq_true, decide_eq_true_eq] at hbit
              rcases hbit with h | h
              · left
                have hdiv : (i * c + j) / c = i := by
                  rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj]; omega
                rw [← h, hdiv]
              · right
                have hdiv : (i * c + j) / c = i := by
                  rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj]; omega
                rw [← h, hdiv]
            · rintro (hu | hv)
              · refine ⟨u.1 % c, Nat.mod_lt _ (by omega), ?_⟩
                have hkc : i * c + u.1 % c = u.1 := by
                  rw [hu, Nat.mul_comm]; exact Nat.div_add_mod u.1 c
                have hadd : 2 * (r * c) + i * c + u.1 % c = 2 * (r * c) + u.1 := by omega
                rw [hadd, huv u.1 u.2]
                simp
              · refine ⟨v.1 % c, Nat.mod_lt _ (by omega), ?_⟩
                have hkc : i * c + v.1 % c = v.1 := by
                  rw [hv, Nat.mul_comm]; exact Nat.div_add_mod v.1 c
                have hadd : 2 * (r * c) + i * c + v.1 % c = 2 * (r * c) + v.1 := by omega
                rw [hadd, huv v.1 v.2]
                simp
          exact hany
      · intro t ht
        rw [foldl_stepWire_getD_lt _ wk _ (by rw [hlen]; simp only [rowBase]; omega)]
        exact huv t ht

-- Col gates evaluation
theorem colGates_prefix (r c : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) (u v : Fin (r * c))
    (w1 : List Bool) (hw1_len : w1.length = colBase r c 0)
    (hw1_uv : ∀ t < r * c, w1.getD (2 * (r * c) + t) false = (decide (t = u.1) || decide (t = v.1))) :
    ∀ k ≤ c,
      let wk := ((List.range k).flatMap (fun j => orChainGates (colBase r c j) (colWires r c j))).foldl stepWire w1
      wk.length = colBase r c k ∧
      (∀ j < k, wk.getD (colOut r c j) false = (decide (j = u.1 % c) || decide (j = v.1 % c))) ∧
      (∀ t < r * c, wk.getD (2 * (r * c) + t) false = (decide (t = u.1) || decide (t = v.1)))
  | 0, _ => ⟨by simpa using hw1_len, fun j hj => by omega, hw1_uv⟩
  | k + 1, hk => by
      have ih := colGates_prefix r c hr hc u v w1 hw1_len hw1_uv k (by omega)
      dsimp only at ih ⊢
      obtain ⟨hlen, hprev, huv⟩ := ih
      let wk := ((List.range k).flatMap (fun j => orChainGates (colBase r c j) (colWires r c j))).foldl stepWire w1
      have hsplit : ((List.range (k + 1)).flatMap (fun j => orChainGates (colBase r c j) (colWires r c j))).foldl stepWire w1 =
          (orChainGates (colBase r c k) (colWires r c k)).foldl stepWire wk := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.foldl_append]
      rw [hsplit]
      have hne : colWires r c k ≠ [] := by simp [colWires]; omega
      have hlt : ∀ x ∈ colWires r c k, x < colBase r c k := by
        intro x hx
        simp only [colWires, List.mem_map, List.mem_range] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        have hic : i * c + k < r * c := by
          calc i * c + k < i * c + c := by omega
          _ = (i + 1) * c := by ring
          _ ≤ r * c := Nat.mul_le_mul_right c (by omega)
        simp only [colBase]; omega
      have heval := foldl_orChainGates (colBase r c k) (colWires r c k) wk hlen hne hlt
      have hlen' : ((orChainGates (colBase r c k) (colWires r c k)).foldl stepWire wk).length = colBase r c (k + 1) := by
        rw [foldl_stepWire_len, hlen, orChainGates_len]
        simp only [colWires, List.length_map, List.length_range, colBase]
        rw [Nat.add_mul, Nat.one_mul]; omega
      refine ⟨hlen', ?_, ?_⟩
      · intro j hj
        by_cases hjk : j < k
        · have hout_lt : colOut r c j < colBase r c k := by
            unfold colOut colWires
            cases hr0 : r with
            | zero => omega
            | succ r' =>
                cases r' with
                | zero => omega
                | succ r'' =>
                    simp only [List.range_succ_eq_map, List.map_cons, List.map_map, orChainOut,
                      List.length_cons, List.length_map, List.length_range, colBase]
                    have hsub : r'' + 1 + 1 - 1 = r'' + 1 := by omega
                    rw [hsub]
                    have : (j + 1) * (r'' + 1) ≤ k * (r'' + 1) := Nat.mul_le_mul_right _ (by omega)
                    rw [Nat.add_mul, Nat.one_mul] at this
                    omega
          rw [foldl_stepWire_getD_lt _ wk _ (by rw [hlen]; exact hout_lt)]
          exact hprev j hjk
        · have heq : j = k := by omega
          subst heq
          rw [colOut, heval]
          simp only [colWires, List.any_map]
          apply Bool.eq_iff_iff.mpr
          simp only [List.any_eq_true, Function.comp_apply, List.mem_range, Bool.or_eq_true, decide_eq_true_eq]
          constructor
          · rintro ⟨i, hi, hbit⟩
            have hic : i * c + j < r * c := by
              calc i * c + j < i * c + c := by omega
              _ = (i + 1) * c := by ring
              _ ≤ r * c := Nat.mul_le_mul_right c (by omega)
            have hadd : 2 * (r * c) + i * c + j = 2 * (r * c) + (i * c + j) := by omega
            rw [hadd, huv (i * c + j) hic] at hbit
            simp only [Bool.or_eq_true, decide_eq_true_eq] at hbit
            rcases hbit with h | h
            · left
              have hmod : (i * c + j) % c = j := by
                rw [Nat.mul_comm i c, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
              rw [← h, hmod]
            · right
              have hmod : (i * c + j) % c = j := by
                rw [Nat.mul_comm i c, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
              rw [← h, hmod]
          · rintro (hu | hv)
            · refine ⟨u.1 / c, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq u.2 (Nat.mul_comm r c)), ?_⟩
              have hic : (u.1 / c) * c + j = u.1 := by
                rw [hu, Nat.mul_comm]; exact Nat.div_add_mod u.1 c
              have hadd : 2 * (r * c) + (u.1 / c) * c + j = 2 * (r * c) + u.1 := by omega
              rw [hadd, huv u.1 u.2]; simp
            · refine ⟨v.1 / c, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq v.2 (Nat.mul_comm r c)), ?_⟩
              have hic : (v.1 / c) * c + j = v.1 := by
                rw [hv, Nat.mul_comm]; exact Nat.div_add_mod v.1 c
              have hadd : 2 * (r * c) + (v.1 / c) * c + j = 2 * (r * c) + v.1 := by omega
              rw [hadd, huv v.1 v.2]; simp
      · intro t ht
        rw [foldl_stepWire_getD_lt _ wk _ (by rw [hlen]; simp only [colBase]; omega)]
        exact huv t ht

-- Counting true entries of `(fun i => decide (i = a) || decide (i = b))` over `List.range m`
theorem count_two_eq (m a b : ℕ) (ha : a < m) (hb : b < m) :
    ((List.range m).map (fun i => decide (i = a) || decide (i = b))).count true =
      if a = b then 1 else 2 := by
  have hgen : ∀ k,
      ((List.range k).map (fun i => decide (i = a) || decide (i = b))).count true =
        if a = b then (if a < k then 1 else 0)
        else (if a < k then 1 else 0) + (if b < k then 1 else 0) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [List.range_succ, List.map_append, List.count_append, ih, List.map_singleton, List.count_singleton]
        by_cases hab : a = b
        · subst hab
          by_cases hka : k = a
          · subst hka; simp
          · by_cases hlt : a < k
            · have hlt2 : a < k + 1 := by omega
              simp [hlt, hlt2, hka]
            · have hlt2 : ¬ a < k + 1 := by omega
              simp [hlt, hlt2, hka]
        · by_cases hka : k = a
          · subst hka
            have hkb : k ≠ b := hab
            by_cases hbk : b < k
            · have hbk2 : b < k + 1 := by omega
              simp [hab, hkb, hbk, hbk2]
            · have hbk2 : ¬ b < k + 1 := by omega
              simp [hab, hkb, hbk, hbk2]
          · by_cases hkb : k = b
            · subst hkb
              by_cases hak : a < k
              · have hak2 : a < k + 1 := by omega
                simp [hab, hka, hak, hak2]
              · have hak2 : ¬ a < k + 1 := by omega
                simp [hab, hka, hak, hak2]
            · by_cases hak : a < k <;> by_cases hbk : b < k
              · have hak2 : a < k + 1 := by omega
                have hbk2 : b < k + 1 := by omega
                simp [hab, hka, hkb, hak, hak2, hbk, hbk2]
              · have hak2 : a < k + 1 := by omega
                have hbk2 : ¬ b < k + 1 := by omega
                simp [hab, hka, hkb, hak, hak2, hbk, hbk2]
              · have hak2 : ¬ a < k + 1 := by omega
                have hbk2 : b < k + 1 := by omega
                simp [hab, hka, hkb, hak, hak2, hbk, hbk2]
              · have hak2 : ¬ a < k + 1 := by omega
                have hbk2 : ¬ b < k + 1 := by omega
                simp [hab, hka, hkb, hak, hak2, hbk, hbk2]
  rw [hgen m]
  simp [ha, hb]

theorem rowOut_lt (r c i : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) (hi : i < r) :
    rowOut r c i < rowBase r c r := by
  unfold rowOut rowWires
  cases hc0 : c with
  | zero => omega
  | succ c' =>
      cases c' with
      | zero => omega
      | succ c'' =>
          simp only [List.range_succ_eq_map, List.map_cons, List.map_map, orChainOut,
            List.length_cons, List.length_map, List.length_range, rowBase]
          have hsub : c'' + 1 + 1 - 1 = c'' + 1 := by omega
          rw [hsub]
          have : (i + 1) * (c'' + 1) ≤ r * (c'' + 1) := Nat.mul_le_mul_right _ (by omega)
          rw [Nat.add_mul, Nat.one_mul] at this
          omega

theorem colOut_lt (r c j : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) (hj : j < c) :
    colOut r c j < colBase r c c := by
  unfold colOut colWires
  cases hr0 : r with
  | zero => omega
  | succ r' =>
      cases r' with
      | zero => omega
      | succ r'' =>
          simp only [List.range_succ_eq_map, List.map_cons, List.map_map, orChainOut,
            List.length_cons, List.length_map, List.length_range, colBase]
          have hsub : r'' + 1 + 1 - 1 = r'' + 1 := by omega
          rw [hsub]
          have : (j + 1) * (r'' + 1) ≤ c * (r'' + 1) := Nat.mul_le_mul_right _ (by omega)
          rw [Nat.add_mul, Nat.one_mul] at this
          omega

theorem prodCrown_rep (r c : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) :
    Represents (fun u v : Fin (r * c) => decide (u ≠ v)) (prodCrown r c) := by
  intro u v
  unfold Circuit.eval Circuit.wires prodCrown prodCrownGates
  change (((uvGates (r * c) ++ rowGates r c ++ colGates r c ++ t2RowGates r c ++ t2ColGates r c ++
    [({ op := .or, inputs := [t2RowOut r c, t2ColOut r c] } : Gate)]).foldl stepWire (oneEach u v)).getD (prodCrownOut r c) false) = decide (u ≠ v)
  simp only [List.foldl_append]
  rw [foldl_uvGates]
  -- Stage 2: rowGates
  have hrow := rowGates_prefix r c hr hc u v r (Nat.le_refl r)
  dsimp only at hrow
  obtain ⟨hw1_len, hw1_row, hw1_uv⟩ := hrow
  let w1 := (rowGates r c).foldl stepWire (oneEach u v ++ List.ofFn (uvVal (r * c) u v))
  have hw1_len' : w1.length = colBase r c 0 := by
    simpa [w1, rowGates, rowBase, colBase] using hw1_len
  -- Stage 3: colGates
  have hcol := colGates_prefix r c hr hc u v w1 hw1_len' hw1_uv c (Nat.le_refl c)
  dsimp only at hcol
  obtain ⟨hw2_len, hw2_col, _⟩ := hcol
  let w2 := (colGates r c).foldl stepWire w1
  have hw2_len' : w2.length = t2RowBase r c := by
    simpa [w2, colGates, colBase, t2RowBase] using hw2_len
  have hw2_row : ∀ i < r, w2.getD (rowOut r c i) false = (decide (i = u.1 / c) || decide (i = v.1 / c)) := by
    intro i hi
    have hlt := rowOut_lt r c i hr hc hi
    rw [show w2.getD (rowOut r c i) false = w1.getD (rowOut r c i) false from
      foldl_stepWire_getD_lt (colGates r c) w1 (rowOut r c i) (by rw [hw1_len']; simp [rowBase, colBase] at hlt ⊢; omega)]
    exact hw1_row i hi
  -- Stage 4: t2RowGates
  let w3 := (t2RowGates r c).foldl stepWire w2
  have hw3_len : w3.length = t2ColBase r c := by
    simp only [w3, t2RowGates, foldl_stepWire_len, hw2_len', t2ColBase]
    rw [t2Gates_len _ _ (by simp [rowOutList]; omega)]
    simp [rowOutList]
  have hw3_row_out : w3.getD (t2RowOut r c) false = decide (u.1 / c ≠ v.1 / c) := by
    have he := t2Gates_eval (t2RowBase r c) (rowOutList r c) w2 hw2_len'
      (by simp [rowOutList]; omega)
      (by
        intro x hx
        simp only [rowOutList, List.mem_map, List.mem_range] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        have hlt := rowOut_lt r c i hr hc hi
        simp only [rowBase, t2RowBase] at hlt ⊢; omega)
    rw [show w3.getD (t2RowOut r c) false = decide (2 ≤ countTrue w2 (rowOutList r c)) from he]
    have hct : countTrue w2 (rowOutList r c) =
        ((List.range r).map (fun i => decide (i = u.1 / c) || decide (i = v.1 / c))).count true := by
      unfold countTrue rowOutList
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hw2_row i (List.mem_range.mp hi)
    rw [hct, count_two_eq r (u.1 / c) (v.1 / c)
      (Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq u.2 (Nat.mul_comm r c)))
      (Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq v.2 (Nat.mul_comm r c)))]
    by_cases h : u.1 / c = v.1 / c <;> simp [h]
  -- Stage 5: t2ColGates
  let w4 := (t2ColGates r c).foldl stepWire w3
  have hw4_len : w4.length = prodCrownOut r c := by
    simp only [w4, t2ColGates, foldl_stepWire_len, hw3_len, prodCrownOut]
    rw [t2Gates_len _ _ (by simp [colOutList]; omega)]
    simp [colOutList]
  have hw3_col : ∀ j < c, w3.getD (colOut r c j) false = (decide (j = u.1 % c) || decide (j = v.1 % c)) := by
    intro j hj
    have hlt := colOut_lt r c j hr hc hj
    rw [show w3.getD (colOut r c j) false = w2.getD (colOut r c j) false from
      foldl_stepWire_getD_lt (t2RowGates r c) w2 (colOut r c j) (by rw [hw2_len']; simp [colBase, t2RowBase] at hlt ⊢; omega)]
    exact hw2_col j hj
  have hw4_col_out : w4.getD (t2ColOut r c) false = decide (u.1 % c ≠ v.1 % c) := by
    have he := t2Gates_eval (t2ColBase r c) (colOutList r c) w3 hw3_len
      (by simp [colOutList]; omega)
      (by
        intro x hx
        simp only [colOutList, List.mem_map, List.mem_range] at hx
        obtain ⟨j, hj, rfl⟩ := hx
        have hlt := colOut_lt r c j hr hc hj
        simp only [colBase, t2RowBase, t2ColBase] at hlt ⊢; omega)
    rw [show w4.getD (t2ColOut r c) false = decide (2 ≤ countTrue w3 (colOutList r c)) from he]
    have hct : countTrue w3 (colOutList r c) =
        ((List.range c).map (fun j => decide (j = u.1 % c) || decide (j = v.1 % c))).count true := by
      unfold countTrue colOutList
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro j hj
      exact hw3_col j (List.mem_range.mp hj)
    rw [hct, count_two_eq c (u.1 % c) (v.1 % c)
      (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))]
    by_cases h : u.1 % c = v.1 % c <;> simp [h]
  have hw4_row_out : w4.getD (t2RowOut r c) false = decide (u.1 / c ≠ v.1 / c) := by
    have hlt : t2RowOut r c < t2ColBase r c := by
      simp only [t2RowOut, t2Out, rowOutList, List.length_map, List.length_range, t2ColBase]
      omega
    rw [show w4.getD (t2RowOut r c) false = w3.getD (t2RowOut r c) false from
      foldl_stepWire_getD_lt (t2ColGates r c) w3 (t2RowOut r c) (by omega)]
    exact hw3_row_out
  -- Stage 6: final OR gate
  change ((stepWire w4 ⟨.or, [t2RowOut r c, t2ColOut r c]⟩)).getD (prodCrownOut r c) false = decide (u ≠ v)
  simp only [stepWire, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    id_eq, Bool.or_false, getD_snoc_self w4 _ (prodCrownOut r c) hw4_len, hw4_row_out, hw4_col_out]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · intro h heq
    subst heq
    rcases h with h | h <;> exact h rfl
  · intro hne
    by_cases hd : u.1 / c = v.1 / c
    · right
      intro hm
      apply hne
      apply Fin.ext
      have hu := Nat.div_add_mod u.1 c
      have hv := Nat.div_add_mod v.1 c
      rw [hd, hm] at hu
      omega
    · left; exact hd

end P18183

theorem P18183 : ∀ r c : ℕ, 2 ≤ r → 2 ≤ c → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin (r * c) => decide (u ≠ v)) (3 * r * c + 2 * (r + c) - 9) :=
  fun r c hr hc =>
    ⟨P18183.prodCrown r c,
     P18183.prodCrown_mono r c,
     P18183.prodCrown_size r c hr hc,
     P18183.prodCrown_rep r c hr hc⟩


namespace P18153

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)

theorem mono (gs : List Gate) (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ i, (run gs x).getD i false = true → (run gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => intro i hi; exact h i hi
  | append_singleton gs g ih =>
    intro i hi
    have ih' := ih (fun g hg' => hg g (by simp [hg']))
    have l1 := run_length gs x
    have l2 := run_length gs y
    rw [run_snoc] at hi ⊢
    rcases Nat.lt_trichotomy i (x.length + gs.length) with hlt | heq | hgt
    · rw [getD_lt _ _ _ (by omega)] at hi ⊢; exact ih' i hi
    · have e1 : i = (run gs x).length := by omega
      have e2 : i = (run gs y).length := by omega
      have hi' : g.op.eval (g.inputs.map fun i => (run gs x).getD i false) = true := by
        rw [← getD_at (run gs x) (g.op.eval (g.inputs.map fun i => (run gs x).getD i false)), ← e1]
        exact hi
      rw [e2, getD_at]
      rcases hg g (by simp) with ho | ho
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hi' ⊢
        exact fun q hq => ih' q (hi' q hq)
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hi' ⊢
        obtain ⟨q, h1, h2⟩ := hi'
        exact ⟨q, h1, ih' q h2⟩
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; cases hi

theorem det : ∀ (gs : List Gate) (N : ℕ), (∀ g ∈ gs, g.inputs.length ≤ 2) → ∀ S : Finset ℕ, ∃ S' : Finset ℕ, S'.card ≤ S.card + gs.length ∧
    ∀ x y : List Bool, x.length = N → y.length = N → (∀ w ∈ S', x.getD w false = y.getD w false) → ∀ w ∈ S, (run gs x).getD w false = (run gs y).getD w false := by
  intro gs
  induction gs with
  | nil => intro N _ S; exact ⟨S, by simp, fun x y _ _ h => h⟩
  | cons g gs ih =>
    intro N hg S
    obtain ⟨T, hT, hd⟩ := ih (N + 1) (fun g' h' => hg g' (List.mem_cons_of_mem _ h')) S
    have step : ∀ x y : List Bool, x.length = N → y.length = N → (∀ w ∈ T, w ≠ N → x.getD w false = y.getD w false) →
        (N ∈ T → ∀ w ∈ g.inputs, x.getD w false = y.getD w false) → ∀ w ∈ S, (run (g :: gs) x).getD w false = (run (g :: gs) y).getD w false := by
      intro x y hx hy h1 h2
      refine hd (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)]) (by simp [hx]) (by simp [hy]) ?_
      intro w hw
      rcases Nat.lt_trichotomy w N with h | h | h
      · rw [getD_lt _ _ _ (by omega), getD_lt _ _ _ (by omega)]
        exact h1 w hw (by omega)
      · subst h
        have e1 : (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]).getD w false = g.op.eval (g.inputs.map fun i => x.getD i false) := by
          rw [← hx]; exact getD_at _ _
        have e2 : (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)]).getD w false = g.op.eval (g.inputs.map fun i => y.getD i false) := by
          rw [← hy]; exact getD_at _ _
        rw [e1, e2, List.map_congr_left fun i hi => h2 hw i hi]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    by_cases hN : N ∈ T
    · refine ⟨T.erase N ∪ g.inputs.toFinset, ?_, fun x y hx hy h => step x y hx hy (fun w hw hne => h w ?_) (fun _ w hw => h w ?_)⟩
      · have e1 := Finset.card_union_le (T.erase N) g.inputs.toFinset
        have e2 := Finset.card_erase_add_one hN
        have e3 := List.toFinset_card_le g.inputs
        have e4 := hg g List.mem_cons_self
        simp only [List.length_cons]
        omega
      · exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hne, hw⟩)
      · exact Finset.mem_union_right _ (List.mem_toFinset.2 hw)
    · refine ⟨T, by simp only [List.length_cons]; omega, fun x y hx hy h => step x y hx hy (fun w hw _ => h w hw) (fun h' => absurd h' hN)⟩

def rv (w : List Bool) : Bool ⊕ ℕ → Bool
  | .inl b => b
  | .inr t => w.getD t false

def fok (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem rv_ext (hs e : List Gate) (y : List Bool) (r : Bool ⊕ ℕ) (h : ∀ t, r = .inr t → t < y.length + hs.length) :
    rv (run (hs ++ e) y) r = rv (run hs y) r := by
  rcases r with b | t
  · rfl
  · exact run_prefix _ _ _ _ (h t rfl)

theorem emit (N : ℕ) (hs : List Gate) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (rs : List (Bool ⊕ ℕ)) (hl : rs.length ≤ 2) (hv : ∀ r ∈ rs, ∀ t, r = .inr t → t < N + hs.length) :
    ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
      ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
  have keep : ∀ r : Bool ⊕ ℕ, (∀ t, r = .inr t → t < N + hs.length) → (∀ y : List Bool, y.length = N → rv (run hs y) r = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro r h1 h2
    exact ⟨r, [], by simp, by simp, by simpa using h1, fun y hy => by rw [List.append_nil]; exact h2 y hy⟩
  have add : ∀ g : Gate, fok g → (∀ y : List Bool, y.length = N → g.op.eval (g.inputs.map fun i => (run hs y).getD i false) = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro g h1 h2
    refine ⟨.inr (N + hs.length), [g], by simp, by simpa using h1, ?_, fun y hy => ?_⟩
    · intro t ht
      cases ht
      simp
    · have : N + hs.length = (run hs y).length := by rw [run_length, hy]
      simp only [rv]
      rw [run_snoc, this, getD_at]
      exact h2 y hy
  rcases rs with _ | ⟨r, _ | ⟨s, _ | ⟨u, rs⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact keep (.inl true) (by simp) (by intro y _; rfl)
    · exact keep (.inl false) (by simp) (by intro y _; rfl)
  · have hr := hv r (by simp)
    rcases hop with rfl | rfl
    · exact keep r hr (by intro y _; simp [GateOp.eval])
    · exact keep r hr (by intro y _; simp [GateOp.eval])
  · have hr := hv r (by simp)
    have hs' := hv s (by simp)
    rcases hop with rfl | rfl
    · rcases r with b | t
      · cases b
        · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
        · exact add ⟨GateOp.and, [t, q]⟩ ⟨by simp, by simp⟩ (by intro y _; simp [GateOp.eval, rv])
    · rcases r with b | t
      · cases b
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
        · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact add ⟨GateOp.or, [t, q]⟩ ⟨by simp, by simp⟩ (by intro y _; simp [GateOp.eval, rv])
  · simp at hl

theorem engine3 {X : Type} (n M : ℕ) (C : Circuit) (src tgt : X → List Bool) (hsrc : ∀ x, (src x).length = n) (htgt : ∀ x, (tgt x).length = M) (F : Finset ℕ)
    (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (h0 : ∀ w < n, (∃ b, ∀ x, (src x).getD w false = b) ∨ ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false)
    (hne : ¬∃ b, ∀ x, C.eval (src x) = b)
    (hF : ∀ j ∈ F, j < C.gates.length ∧ ((∃ b, ∀ x, (run C.gates (src x)).getD (n + j) false = b) ∨
      ∃ w < n + j, ∀ x, (run C.gates (src x)).getD (n + j) false = (run C.gates (src x)).getD w false)) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size + F.card ≤ C.size ∧ ∀ x, D.eval (tgt x) = C.eval (src x) := by
  classical
  have key : ∀ k, k ≤ C.gates.length → ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, fok g) ∧ hs.length + (F.filter fun j => j < k).card ≤ k ∧
      (∀ w t, w < n + k → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + k, (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => if h : ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false then .inr h.choose else if hb : ∃ b, ∀ x, (src x).getD w false = b then .inl hb.choose else .inl false, by simp, by simp, ?_, ?_⟩
      · intro w t hw ht
        beta_reduce at ht
        split_ifs at ht with h1 h2
        cases ht
        simpa using h1.choose_spec.1
      · intro x w hw
        simp only [Nat.add_zero] at hw
        rw [run_input _ _ _ (by rw [hsrc]; exact hw)]
        beta_reduce
        split_ifs with h1 h2
        · exact h1.choose_spec.2 x
        · exact h2.choose_spec x
        · rcases h0 w hw with h | h
          · exact absurd h h2
          · exact absurd h h1
    | succ k ih =>
      intro hk
      obtain ⟨hs, m, h1, h2, h3, h4⟩ := ih (by omega)
      have hk' : k < C.gates.length := by omega
      have fin : ∀ (r : Bool ⊕ ℕ) (e : List Gate), (∀ g ∈ e, fok g) → (∀ t, r = .inr t → t < M + hs.length + e.length) → e.length + (if k ∈ F then 1 else 0) ≤ 1 →
          (∀ x : X, (run C.gates (src x)).getD (n + k) false = rv (run (hs ++ e) (tgt x)) r) →
          ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, fok g) ∧ hs.length + (F.filter fun j => j < k + 1).card ≤ k + 1 ∧
      (∀ w t, w < n + (k + 1) → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + (k + 1), (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
        intro r e he hr hlen hval
        refine ⟨hs ++ e, Function.update m (n + k) r, ?_, ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact h1 g hg
          · exact he g hg
        · have e1 : (F.filter fun j => j < k + 1) ⊆ (F.filter fun j => j < k) ∪ (if k ∈ F then {k} else ∅) := by
            intro j hj
            rw [Finset.mem_filter] at hj
            rcases Nat.lt_or_ge j k with h | h
            · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hj.1, h⟩)
            · have : j = k := by omega
              subst this
              rw [if_pos hj.1]; simp
          have e2 := (Finset.card_le_card e1).trans (Finset.card_union_le _ _)
          rw [List.length_append]
          by_cases hkF : k ∈ F
          · rw [if_pos hkF] at e2 hlen
            rw [Finset.card_singleton] at e2
            omega
          · rw [if_neg hkF] at e2 hlen
            rw [Finset.card_empty] at e2
            omega
        · intro w t hw ht
          rw [List.length_append]
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self] at ht
            have := hr t ht; omega
          · rw [Function.update_of_ne hwe] at ht
            have := h3 w t (by omega) ht; omega
        · intro x w hw
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self]; exact hval x
          · rw [Function.update_of_ne hwe, h4 x w (by omega)]
            refine (rv_ext hs e (tgt x) (m w) fun t ht => ?_).symm
            have := h3 w t (by omega) ht
            rw [htgt]; exact this
      by_cases hkF : k ∈ F
      · rcases (hF k hkF).2 with ⟨b, hb⟩ | ⟨w, hw, hb⟩
        · exact fin (.inl b) [] (by simp) (by simp) (by simp [hkF]) (fun x => hb x)
        · refine fin (m w) [] (by simp) (fun t ht => by simpa using h3 w t hw ht) (by simp [hkF]) (fun x => ?_)
          rw [List.append_nil, ← h4 x w hw]
          exact hb x
      · have hg := hC _ (List.getElem_mem hk')
        have hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or := by simpa using hg.1
        let m' : ℕ → Bool ⊕ ℕ := fun i => if i < n + k then m i else .inl false
        obtain ⟨r, e, e1, e2, e3, e4⟩ := emit M hs C.gates[k].op hop (C.gates[k].inputs.map m') (by rw [List.length_map]; exact hg.2) (by
          intro r hr t ht
          obtain ⟨i, _, rfl⟩ := List.mem_map.1 hr
          simp only [m'] at ht
          split_ifs at ht with h
          exact h3 i t h ht)
        refine fin r e e2 e3 (by simp [hkF]; exact e1) (fun x => ?_)
        rw [e4 _ (htgt x)]
        have rg := run_gate C.gates (src x) k hk'
        rw [hsrc] at rg
        rw [rg, List.map_map]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp, m']
        split_ifs with h
        · exact h4 x i h
        · rfl
  obtain ⟨hs, m, h1, h2, h3, h4⟩ := key C.gates.length le_rfl
  have hFc : (F.filter fun j => j < C.gates.length) = F := Finset.filter_true_of_mem fun j hj => (hF j hj).1
  rw [hFc] at h2
  have hout : C.output < n + C.gates.length := by
    by_contra h
    refine hne ⟨false, fun x => ?_⟩
    change (run C.gates (src x)).getD C.output false = false
    rw [List.getD_eq_default _ _ (by rw [run_length, hsrc]; omega)]
  have hev : ∀ x, C.eval (src x) = rv (run hs (tgt x)) (m C.output) := fun x => h4 x _ hout
  rcases hm : m C.output with b | t
  · exact absurd ⟨b, fun x => by rw [hev, hm]; rfl⟩ hne
  · refine ⟨⟨hs, t⟩, ?_, h2, fun x => ?_⟩
    · intro g hg
      exact ⟨by simpa using (h1 g hg).1, (h1 g hg).2⟩
    · have := hev x
      rw [hm] at this
      exact this.symm

def rd (A B : ℕ → ℕ) (k w : ℕ) : Prop := A k = w ∨ B k = w

def pt (n u v : ℕ) : ℕ → Bool := fun k => decide (k = u ∨ k = n + v)

def Tg (n m : ℕ) (A B : ℕ → ℕ) (An : ℕ → Bool) (i j : ℕ) : Prop :=
  i < n ∧ j < m ∧ An j = false ∧ ((A j = i ∧ B j = n + i) ∨ (A j = n + i ∧ B j = i)) ∧
    ∀ k < m, (rd A B k i ∨ rd A B k (n + i)) → k = j

def Kill (n : ℕ) (V : (ℕ → Bool) → ℕ → Bool) (i j : ℕ) : Prop :=
  (∃ b, ∀ u v, u < n → v < n → u ≠ i → v ≠ i → V (pt n u v) (n + n + j) = b) ∨
    ∃ w < n + n + j, ∀ u v, u < n → v < n → u ≠ i → v ≠ i → V (pt n u v) (n + n + j) = V (pt n u v) w

theorem core (n : ℕ) (hn : 3 ≤ n) (m : ℕ) (A B : ℕ → ℕ) (An : ℕ → Bool) (V : (ℕ → Bool) → ℕ → Bool) (o : ℕ)
    (hA : ∀ j < m, A j < n + n + j) (hB : ∀ j < m, B j < n + n + j) (hAB : ∀ j < m, A j ≠ B j)
    (v0 : ∀ P k, k < n + n → V P k = P k)
    (v1 : ∀ P j, j < m → V P (n + n + j) = if An j = true then V P (A j) && V P (B j) else V P (A j) || V P (B j))
    (ho : o < n + n + m)
    (hf : ∀ u v, u < n → v < n → V (pt n u v) o = decide (u ≠ v))
    (irr : ∀ j < m, ∀ w < n + n + j, ¬∀ u v, u < n → v < n → V (pt n u v) (n + n + j) = V (pt n u v) w) :
    ∃ i < n, ∃ a b c, a < m ∧ b < m ∧ c < m ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Kill n V i a ∧ Kill n V i b ∧ Kill n V i c := by
  classical
  have mono : ∀ (P Q : ℕ → Bool), (∀ k, P k = true → Q k = true) → ∀ w < n + n + m, V P w = true → V Q w = true := by
    intro P Q hPQ w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw h
      by_cases hwn : w < n + n
      · rw [v0 _ _ hwn] at h ⊢; exact hPQ _ h
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + n + j := ⟨w - (n + n), by omega⟩
        have hj : j < m := by omega
        have a1 := hA j hj
        have b1 := hB j hj
        rw [v1 _ _ hj] at h ⊢
        split_ifs at h ⊢ with hAn
        · rw [Bool.and_eq_true] at h ⊢
          exact ⟨ih _ a1 (by omega) h.1, ih _ b1 (by omega) h.2⟩
        · rw [Bool.or_eq_true] at h ⊢
          exact h.imp (ih _ a1 (by omega)) (ih _ b1 (by omega))
  have rep : ∀ (Hd : ℕ → Prop) (P Q : ℕ → Bool), (∀ k < n + n, ¬Hd k → P k = Q k) →
      (∀ j < m, ¬Hd (n + n + j) → (Hd (A j) ∨ Hd (B j)) → V P (n + n + j) = V Q (n + n + j)) →
      ∀ w < n + n + m, ¬Hd w → V P w = V Q w := by
    intro Hd P Q h1 h2 w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw hH
      by_cases hwn : w < n + n
      · rw [v0 _ _ hwn, v0 _ _ hwn]; exact h1 _ hwn hH
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + n + j := ⟨w - (n + n), by omega⟩
        have hj : j < m := by omega
        have a1 := hA j hj
        have b1 := hB j hj
        by_cases hr : Hd (A j) ∨ Hd (B j)
        · exact h2 j hj hH hr
        · rw [not_or] at hr
          rw [v1 _ _ hj, v1 _ _ hj, ih _ a1 (by omega) hr.1, ih _ b1 (by omega) hr.2]
  have row1 : ∀ u < n, V (fun k => decide (k = u)) o = false := by
    intro u hu
    by_contra h
    have h1 := mono (fun k => decide (k = u)) (pt n u u) (by
      intro k hk
      have : k = u := by simpa using hk
      simp [pt, this]) o ho (by simpa using h)
    rw [hf u u hu hu] at h1
    simp at h1
  have col1 : ∀ v < n, V (fun k => decide (k = n + v)) o = false := by
    intro v hv
    by_contra h
    have h1 := mono (fun k => decide (k = n + v)) (pt n v v) (by
      intro k hk
      have : k = n + v := by simpa using hk
      simp [pt, this]) o ho (by simpa using h)
    rw [hf v v hv hv] at h1
    simp at h1
  obtain ⟨jo, hjo, rfl⟩ : ∃ jo, jo < m ∧ o = n + n + jo := by
    by_cases h : o < n + n
    · exfalso
      by_cases h2 : o < n
      · have := hf o o h2 h2
        rw [v0 _ _ h] at this
        simp [pt] at this
      · have := hf (o - n) (o - n) (by omega) (by omega)
        rw [v0 _ _ h] at this
        have e : o = n + (o - n) := by omega
        simp only [pt, ← e] at this
        simp at this
    · exact ⟨o - (n + n), by omega, by omega⟩
  let Z : ℕ → ℕ → Prop := fun i w => ∀ u v, u < n → v < n → u ≠ i → v ≠ i → V (pt n u v) w = false
  have zr : ∀ i < n, Z i i := by
    intro i hi u v hu hv hui hvi
    rw [v0 _ _ (by omega)]
    simp only [pt, decide_eq_false_iff_not, not_or]
    omega
  have zc : ∀ i < n, Z i (n + i) := by
    intro i hi u v hu hv hui hvi
    rw [v0 _ _ (by omega)]
    simp only [pt, decide_eq_false_iff_not, not_or]
    omega
  have kr : ∀ i j w, j < m → rd A B j w → Z i w → Kill n V i j := by
    intro i j w hj hr hz
    have a1 := hA j hj
    have b1 := hB j hj
    by_cases hAn : An j = true
    · left
      refine ⟨false, fun u v hu hv hui hvi => ?_⟩
      rw [v1 _ _ hj, if_pos hAn]
      rcases hr with rfl | rfl
      · rw [hz u v hu hv hui hvi]; rfl
      · rw [hz u v hu hv hui hvi, Bool.and_false]
    · right
      rcases hr with rfl | rfl
      · refine ⟨B j, b1, fun u v hu hv hui hvi => ?_⟩
        rw [v1 _ _ hj, if_neg hAn, hz u v hu hv hui hvi, Bool.false_or]
      · refine ⟨A j, a1, fun u v hu hv hui hvi => ?_⟩
        rw [v1 _ _ hj, if_neg hAn, hz u v hu hv hui hvi, Bool.or_false]
  have zor : ∀ i j, j < m → An j = false → Z i (A j) → Z i (B j) → Z i (n + n + j) := by
    intro i j hj hAn h1 h2 u v hu hv hui hvi
    rw [v1 _ _ hj, if_neg (by simp [hAn]), h1 u v hu hv hui hvi, h2 u v hu hv hui hvi]; rfl
  have orii : ∀ i j, i < n → j < m → An j = false → (rd A B j i ∨ rd A B j (n + i)) → V (pt n i i) (n + n + j) = true := by
    intro i j hi hj hAn hr
    have p1 : V (pt n i i) i = true := by rw [v0 _ _ (by omega)]; simp [pt]
    have p2 : V (pt n i i) (n + i) = true := by rw [v0 _ _ (by omega)]; simp [pt]
    rw [v1 _ _ hj, if_neg (by simp [hAn]), Bool.or_eq_true]
    rcases hr with (h | h) | (h | h)
    · exact Or.inl (by rw [h]; exact p1)
    · exact Or.inr (by rw [h]; exact p1)
    · exact Or.inl (by rw [h]; exact p2)
    · exact Or.inr (by rw [h]; exact p2)
  have notout : ∀ i j, i < n → j < m → An j = false → (rd A B j i ∨ rd A B j (n + i)) → j ≠ jo := by
    rintro i j hi hj hAn hr rfl
    have h1 := orii i j hi hj hAn hr
    rw [hf i i hi hi] at h1
    simp at h1
  have seesC : ∀ i < n, ∃ P Q : ℕ → Bool, (∀ k, k ≠ n + i → P k = Q k) ∧ P i = false ∧ Q i = false ∧ V P (n + n + jo) ≠ V Q (n + n + jo) := by
    intro i hi
    obtain ⟨u, hu, hui⟩ : ∃ u < n, u ≠ i := by
      by_cases h : i = 0
      · exact ⟨1, by omega, by omega⟩
      · exact ⟨0, by omega, by omega⟩
    refine ⟨pt n u i, fun k => decide (k = u), ?_, ?_, ?_, ?_⟩
    · intro k hk; simp [pt, hk]
    · simp only [pt, decide_eq_false_iff_not, not_or]; omega
    · simp only [decide_eq_false_iff_not]; omega
    · rw [hf u i hu hi, row1 u hu]; simp [hui]
  have seesR : ∀ i < n, ∃ P Q : ℕ → Bool, (∀ k, k ≠ i → P k = Q k) ∧ P (n + i) = false ∧ Q (n + i) = false ∧ V P (n + n + jo) ≠ V Q (n + n + jo) := by
    intro i hi
    obtain ⟨v, hv, hvi⟩ : ∃ v < n, v ≠ i := by
      by_cases h : i = 0
      · exact ⟨1, by omega, by omega⟩
      · exact ⟨0, by omega, by omega⟩
    refine ⟨pt n i v, fun k => decide (k = n + v), ?_, ?_, ?_, ?_⟩
    · intro k hk; simp [pt, hk]
    · simp only [pt, decide_eq_false_iff_not, not_or]; omega
    · simp only [decide_eq_false_iff_not]; omega
    · rw [hf i v hi hv, col1 v hv]; simp [Ne.symm hvi]
  have raw : ∀ (i x y h g : ℕ), i < n → ((x = i ∧ y = n + i) ∨ (x = n + i ∧ y = i)) → h < m → g < m → h ≠ g → rd A B h x → rd A B g x →
      (∀ a, rd A B h a → a < n + n ∨ ∃ i' j, a = n + n + j ∧ Tg n m A B An i' j) →
      (∃ P Q : ℕ → Bool, (∀ k, k ≠ y → P k = Q k) ∧ P x = false ∧ Q x = false ∧ V P (n + n + jo) ≠ V Q (n + n + jo)) →
      ∃ i < n, ∃ a b c, a < m ∧ b < m ∧ c < m ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Kill n V i a ∧ Kill n V i b ∧ Kill n V i c := by
    intro i x y h g hi hxy hh hg hhg rhx rgx hat hsee
    have zx : Z i x := by rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> [exact zr _ hi; exact zc _ hi]
    have zy : Z i y := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> [exact zc _ hi; exact zr _ hi]
    have hxN : x < n + n := by rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
    have hyN : y < n + n := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
    have hne : x ≠ y := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
    by_cases h3 : ∃ k < m, (rd A B k x ∨ rd A B k y) ∧ k ≠ h ∧ k ≠ g
    · obtain ⟨k, hk, hr, k1, k2⟩ := h3
      refine ⟨i, hi, h, g, k, hh, hg, hk, hhg, Ne.symm k1, Ne.symm k2, kr i h x hh rhx zx, kr i g x hg rgx zx, ?_⟩
      exact hr.elim (fun r => kr i k x hk r zx) (fun r => kr i k y hk r zy)
    push Not at h3
    have only : ∀ k < m, (rd A B k x ∨ rd A B k y) → k = h ∨ k = g := by
      intro k hk hr
      by_contra hc
      rw [not_or] at hc
      exact hc.2 (h3 k hk hr hc.1)
    obtain ⟨P, Q, pq, px, qx, hdiff⟩ := hsee
    have both : ∀ k < m, rd A B k x → rd A B k y → (A k = x ∧ B k = y) ∨ (A k = y ∧ B k = x) := by
      intro k _ h1 h2
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact absurd (h1.symm.trans h2) hne
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h2, h1⟩
      · exact absurd (h1.symm.trans h2) hne
    have andv : ∀ k < m, An k = true → rd A B k x → ∀ W : ℕ → Bool, W x = false → V W (n + n + k) = false := by
      intro k hk hAn hr W hW
      rw [v1 _ _ hk, if_pos hAn]
      rcases hr with hr | hr
      · rw [hr, v0 _ _ hxN, hW]; rfl
      · rw [hr, v0 _ _ hxN, hW, Bool.and_false]
    have orxy : ∀ k < m, An k = false → (rd A B k x ∧ rd A B k y) → k ≠ jo := by
      intro k hk hAn hr
      refine notout i k hi hk hAn ?_
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl hr.1
      · exact Or.inl hr.2
    have zgate : ∀ k < m, An k = false → rd A B k x → rd A B k y → Z i (n + n + k) := by
      intro k hk hAn r1 r2
      rcases both k hk r1 r2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact zor i k hk hAn (by rw [e1]; exact zx) (by rw [e2]; exact zy)
      · exact zor i k hk hAn (by rw [e1]; exact zy) (by rw [e2]; exact zx)
    by_cases rhy : rd A B h y
    · by_cases rgy : rd A B g y
      ·
        have hops : An h ≠ An g := by
          intro e
          have same : ∀ W, V W (n + n + h) = V W (n + n + g) := by
            intro W
            rw [v1 _ _ hh, v1 _ _ hg, e]
            rcases both h hh rhx rhy with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases both g hg rgx rgy with ⟨e3, e4⟩ | ⟨e3, e4⟩ <;> rw [e1, e2, e3, e4] <;>
              cases V W x <;> cases V W y <;> cases An g <;> rfl
          rcases Nat.lt_or_gt_of_ne hhg with hlt | hlt
          · exact irr g hg (n + n + h) (by omega) fun u v _ _ => (same _).symm
          · exact irr h hh (n + n + g) (by omega) fun u v _ _ => same _
        obtain ⟨p, q, hp, hq, hpq, pAn, qAn, rpx, rpy, rqx, rqy, hset⟩ : ∃ p q, p < m ∧ q < m ∧ p ≠ q ∧ An p = false ∧ An q = true ∧ rd A B p x ∧ rd A B p y ∧ rd A B q x ∧ rd A B q y ∧ (∀ k, k = h ∨ k = g → k = p ∨ k = q) := by
          cases e1 : An h with
          | false =>
            have e2 : An g = true := by
              cases e2 : An g with
              | true => rfl
              | false => exact absurd (e1.trans e2.symm) hops
            exact ⟨h, g, hh, hg, hhg, e1, e2, rhx, rhy, rgx, rgy, fun k hk => hk⟩
          | true =>
            have e2 : An g = false := by
              cases e2 : An g with
              | false => rfl
              | true => exact absurd (e1.trans e2.symm) hops
            exact ⟨g, h, hg, hh, Ne.symm hhg, e2, e1, rgx, rgy, rhx, rhy, fun k hk => hk.symm⟩
        have hrd : ∃ k < m, rd A B k (n + n + p) := by
          by_contra hno
          push Not at hno
          refine hdiff (rep (fun w => w = y ∨ w = n + n + p) P Q (fun k _ hk => pq k fun e => hk (Or.inl e)) ?_ _ (by omega) ?_)
          · intro j hj hjH hr
            have hjp : j ≠ p := fun e => hjH (Or.inr (by rw [e]))
            have : rd A B j y := by
              rcases hr with (e | e) | (e | e)
              · exact Or.inl e
              · exact absurd (Or.inl e) (hno j hj)
              · exact Or.inr e
              · exact absurd (Or.inr e) (hno j hj)
            have hjq : j = q := by
              rcases hset j (only j hj (Or.inr this)) with e | e
              · exact absurd e hjp
              · exact e
            subst hjq
            rw [andv j hj qAn rqx P px, andv j hj qAn rqx Q qx]
          · rintro (e | e)
            · omega
            · exact orxy p hp pAn ⟨rpx, rpy⟩ (by omega)
        obtain ⟨k, hk, hr⟩ := hrd
        have ar : ∀ c < m, rd A B c x → rd A B c y → ¬rd A B c (n + n + p) := by
          intro c hc c1 c2 c3
          rcases both c hc c1 c2 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases c3 with e3 | e3 <;> omega
        refine ⟨i, hi, p, q, k, hp, hq, hk, hpq, ?_, ?_, kr i p x hp rpx zx, kr i q x hq rqx zx, kr i k _ hk hr (zgate p hp pAn rpx rpy)⟩
        · rintro rfl; exact ar _ hp rpx rpy hr
        · rintro rfl; exact ar _ hq rqx rqy hr
      ·
        have oy : ∀ k < m, rd A B k y → k = h := by
          intro k hk r
          rcases only k hk (Or.inr r) with e | e
          · exact e
          · subst e; exact absurd r rgy
        cases hAn : An h with
        | true =>
          exfalso
          refine hdiff (rep (fun w => w = y) P Q (fun k _ hk => pq k hk) ?_ _ (by omega) (by omega))
          intro j hj _ hr
          have : j = h := oy j hj hr
          subst this
          rw [andv j hj hAn rhx P px, andv j hj hAn rhx Q qx]
        | false =>
          have hrd : ∃ k < m, rd A B k (n + n + h) := by
            by_contra hno
            push Not at hno
            refine hdiff (rep (fun w => w = y ∨ w = n + n + h) P Q (fun k _ hk => pq k fun e => hk (Or.inl e)) ?_ _ (by omega) ?_)
            · intro j hj hjH hr
              exfalso
              have : rd A B j y := by
                rcases hr with (e | e) | (e | e)
                · exact Or.inl e
                · exact absurd (Or.inl e) (hno j hj)
                · exact Or.inr e
                · exact absurd (Or.inr e) (hno j hj)
              exact hjH (Or.inr (by rw [oy j hj this]))
            · rintro (e | e)
              · omega
              · exact orxy h hh hAn ⟨rhx, rhy⟩ (by omega)
          by_cases hother : ∃ k < m, rd A B k (n + n + h) ∧ k ≠ g
          · obtain ⟨k, hk, hr, hkg⟩ := hother
            refine ⟨i, hi, h, g, k, hh, hg, hk, hhg, ?_, Ne.symm hkg, kr i h x hh rhx zx, kr i g x hg rgx zx, kr i k _ hk hr (zgate h hh hAn rhx rhy)⟩
            rintro rfl
            have a1 := hA h hh
            have b1 := hB h hh
            rcases hr with e | e <;> omega
          · exfalso
            push Not at hother
            obtain ⟨k, hk, hr⟩ := hrd
            have hkg := hother k hk hr
            subst hkg
            have hhk : h < k := by
              have a1 := hA k hk
              have b1 := hB k hk
              rcases hr with e | e <;> omega
            have ops : (A k = x ∧ B k = n + n + h) ∨ (A k = n + n + h ∧ B k = x) := by
              rcases rgx with e1 | e1 <;> rcases hr with e2 | e2
              · omega
              · exact Or.inl ⟨e1, e2⟩
              · exact Or.inr ⟨e2, e1⟩
              · omega
            have hhv : ∀ W, V W (n + n + h) = (V W x || V W y) := by
              intro W
              rw [v1 _ _ hh, if_neg (by simp [hAn])]
              rcases both h hh rhx rhy with ⟨e1, e2⟩ | ⟨e1, e2⟩
              · rw [e1, e2]
              · rw [e1, e2, Bool.or_comm]
            cases hAk : An k with
            | true =>
              refine irr k hk x (by omega) fun u v _ _ => ?_
              rw [v1 _ _ hk, if_pos hAk]
              rcases ops with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2, hhv] <;> cases V (pt n u v) x <;> cases V (pt n u v) y <;> rfl
            | false =>
              refine irr k hk (n + n + h) (by omega) fun u v _ _ => ?_
              rw [v1 _ _ hk, if_neg (by simp [hAk])]
              rcases ops with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2, hhv] <;> cases V (pt n u v) x <;> cases V (pt n u v) y <;> rfl
    ·
      have oy : ∀ k < m, rd A B k y → k = g := by
        intro k hk r
        rcases only k hk (Or.inr r) with e | e
        · subst e; exact absurd r rhy
        · exact e
      have rgy : rd A B g y := by
        by_contra hno
        refine hdiff (rep (fun w => w = y) P Q (fun k _ hk => pq k hk) ?_ _ (by omega) (by omega))
        intro j hj _ hr
        exfalso
        have := oy j hj hr
        subst this
        exact hno hr
      cases hAn : An g with
      | true =>
        exfalso
        refine hdiff (rep (fun w => w = y) P Q (fun k _ hk => pq k hk) ?_ _ (by omega) (by omega))
        intro j hj _ hr
        have : j = g := oy j hj hr
        subst this
        rw [andv j hj hAn rgx P px, andv j hj hAn rgx Q qx]
      | false =>
        have hrd : ∃ k < m, rd A B k (n + n + g) := by
          by_contra hno
          push Not at hno
          refine hdiff (rep (fun w => w = y ∨ w = n + n + g) P Q (fun k _ hk => pq k fun e => hk (Or.inl e)) ?_ _ (by omega) ?_)
          · intro j hj hjH hr
            exfalso
            have : rd A B j y := by
              rcases hr with (e | e) | (e | e)
              · exact Or.inl e
              · exact absurd (Or.inl e) (hno j hj)
              · exact Or.inr e
              · exact absurd (Or.inr e) (hno j hj)
            exact hjH (Or.inr (by rw [oy j hj this]))
          · rintro (e | e)
            · omega
            · exact orxy g hg hAn ⟨rgx, rgy⟩ (by omega)
        obtain ⟨k, hk, hr⟩ := hrd
        refine ⟨i, hi, h, g, k, hh, hg, hk, hhg, ?_, ?_, kr i h x hh rhx zx, kr i g x hg rgx zx, kr i k _ hk hr (zgate g hg hAn rgx rgy)⟩
        · rintro rfl
          rcases hat _ hr with e | ⟨i', j, e, hT⟩
          · omega
          · have hjg : j = g := by omega
            subst hjg
            obtain ⟨_, _, _, hops, hex⟩ := hT
            have hx' : x = i' ∨ x = n + i' := by
              rcases hops with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases rgx with e3 | e3 <;> omega
            have : h = j := by
              refine hex h hh ?_
              rcases hx' with rfl | rfl
              · exact Or.inl rhx
              · exact Or.inr rhx
            exact hhg this
        · rintro rfl
          have a1 := hA g hg
          have b1 := hB g hg
          rcases hr with e | e <;> omega
  by_contra hG
  have hexT : ∃ j, j < m ∧ ¬∃ i, Tg n m A B An i j := by
    refine ⟨jo, hjo, ?_⟩
    rintro ⟨i, hi, hj, hAn, hops, _⟩
    refine notout i jo hi hj hAn ?_ rfl
    rcases hops with ⟨e, _⟩ | ⟨_, e⟩
    · exact Or.inl (Or.inl e)
    · exact Or.inl (Or.inr e)
  obtain ⟨hh, hhT⟩ := Nat.find_spec hexT
  have hmin : ∀ j, j < Nat.find hexT → ∃ i, Tg n m A B An i j := by
    intro j hj
    by_contra hc
    exact Nat.find_min hexT hj ⟨by omega, hc⟩
  generalize Nat.find hexT = h at hh hhT hmin
  clear hexT
  have hAh := hA h hh
  have hBh := hB h hh
  have hat : ∀ a, rd A B h a → a < n + n ∨ ∃ i' j, a = n + n + j ∧ Tg n m A B An i' j := by
    intro a ha
    by_cases h1 : a < n + n
    · exact Or.inl h1
    · right
      have : a < n + n + h := by rcases ha with e | e <;> omega
      obtain ⟨i, hi⟩ := hmin (a - (n + n)) (by omega)
      exact ⟨i, a - (n + n), by omega, hi⟩
  have Tne : ∀ i j, Tg n m A B An i j → j ≠ h := by
    rintro i j hT rfl
    exact hhT ⟨i, hT⟩
  have Tno : ∀ i j, Tg n m A B An i j → j ≠ jo := by
    rintro i j ⟨hi, hj, hAn, hops, _⟩
    refine notout i j hi hj hAn ?_
    rcases hops with ⟨e, _⟩ | ⟨_, e⟩
    · exact Or.inl (Or.inl e)
    · exact Or.inl (Or.inr e)
  have VT : ∀ i j, Tg n m A B An i j → ∀ W : ℕ → Bool, V W (n + n + j) = (W i || W (n + i)) := by
    rintro i j ⟨hi, hj, hAn, hops, _⟩ W
    rw [v1 _ _ hj, if_neg (by simp [hAn])]
    rcases hops with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2, v0 _ _ (by omega), v0 _ _ (by omega)]
    · rw [e1, e2, v0 _ _ (by omega), v0 _ _ (by omega), Bool.or_comm]
  have sole : ∀ a, rd A B h a → ∀ k < m, rd A B k a → k = h := by
    intro a ha k hk hr
    by_contra hkh
    apply hG
    rcases hat a ha with h1 | ⟨i, j, rfl, hT⟩
    · by_cases h2 : a < n
      · exact raw a a (n + a) h k h2 (Or.inl ⟨rfl, rfl⟩) hh hk (Ne.symm hkh) ha hr hat (seesC a h2)
      · have e : a = n + (a - n) := by omega
        exact raw (a - n) a (a - n) h k (by omega) (Or.inr ⟨e, rfl⟩) hh hk (Ne.symm hkh) ha hr hat (by
          have := seesR (a - n) (by omega)
          rwa [← e] at this)
    · obtain ⟨hi, hj, hAn, hops, hex⟩ := hT
      have zA : Z i (A j) := by rcases hops with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> [exact zr i hi; exact zc i hi]
      have zB : Z i (B j) := by rcases hops with ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] <;> [exact zc i hi; exact zr i hi]
      have zj := zor i j hj hAn zA zB
      refine ⟨i, hi, j, h, k, hj, hh, hk, Tne i j ⟨hi, hj, hAn, hops, hex⟩, ?_, Ne.symm hkh, kr i j _ hj (Or.inl rfl) zA, kr i h _ hh ha zj, kr i k _ hk hr zj⟩
      rintro rfl
      have a1 := hA j hj
      have b1 := hB j hj
      rcases hr with e | e <;> omega
  have fin : ∀ (Hd : ℕ → Prop) (P Q : ℕ → Bool), (∀ k < n + n, ¬Hd k → P k = Q k) →
      (∀ j < m, ¬Hd (n + n + j) → (Hd (A j) ∨ Hd (B j)) → j = h) → V P (n + n + h) = V Q (n + n + h) → ¬Hd (n + n + jo) →
      V P (n + n + jo) = V Q (n + n + jo) := by
    intro Hd P Q h1 h2 h3 h4
    refine rep Hd P Q h1 (fun j hj hjH hr => ?_) _ (by omega) h4
    rw [h2 j hj hjH hr]; exact h3
  have hVh : ∀ W, V W (n + n + h) = if An h = true then V W (A h) && V W (B h) else V W (A h) || V W (B h) := fun W => v1 W h hh
  have ra : rd A B h (A h) := Or.inl rfl
  have rb : rd A B h (B h) := Or.inr rfl
  have sa := sole _ ra
  have sb := sole _ rb
  have hab := hAB h hh
  have atom : ∀ a, rd A B h a → (∃ i < n, a = i) ∨ (∃ i < n, a = n + i) ∨ ∃ i j, a = n + n + j ∧ Tg n m A B An i j := by
    intro a ha
    rcases hat a ha with h1 | h1
    · by_cases h2 : a < n
      · exact Or.inl ⟨a, h2, rfl⟩
      · exact Or.inr (Or.inl ⟨a - n, by omega, by omega⟩)
    · exact Or.inr (Or.inr h1)
  have third : ∀ i j, i < n → j < n → ∃ v < n, v ≠ i ∧ v ≠ j := by
    intro i j _ _
    by_cases h0 : 0 ≠ i ∧ 0 ≠ j
    · exact ⟨0, by omega, h0.1, h0.2⟩
    · by_cases h1 : 1 ≠ i ∧ 1 ≠ j
      · exact ⟨1, by omega, h1.1, h1.2⟩
      · refine ⟨2, by omega, ?_, ?_⟩ <;> omega
  rcases atom _ ra with ⟨i, hi, ea⟩ | ⟨i, hi, ea⟩ | ⟨i, ja, ea, hTa⟩
  · rcases atom _ rb with ⟨j, hj, eb⟩ | ⟨j, hj, eb⟩ | ⟨j, jb, eb, hTb⟩
    · by_cases hij : i = j
      · subst hij
        exact hab (ea.trans eb.symm)
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + v)
          let Q : ℕ → Bool := fun k => decide (k = n + v)
          have va : V P (i) = true := by rw [v0 _ _ (by omega)]; exact (show P (i) = true from by show decide ((i) = i ∨ (i) = n + v) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (j) = false := by rw [v0 _ _ (by omega)]; exact (show P (j) = false from by show decide ((j) = i ∨ (j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ua : V Q (i) = false := by rw [v0 _ _ (by omega)]; exact (show Q (i) = false from by show decide ((i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ub : V Q (j) = false := by rw [v0 _ _ (by omega)]; exact (show Q (j) = false from by show decide ((j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have hfin := fin (fun w => w = i) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i v hi hv).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + v) = decide (k = n + v)
            have hH2 : ¬(k = i) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = i) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = i) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = i := hH
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = j ∨ k = n + i)
          have va : V P (i) = true := by rw [v0 _ _ (by omega)]; exact (show P (i) = true from by show decide ((i) = i ∨ (i) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (j) = false := by rw [v0 _ _ (by omega)]; exact (show P (j) = false from by show decide ((j) = i ∨ (j) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ua : V Q (i) = false := by rw [v0 _ _ (by omega)]; exact (show Q (i) = false from by show decide ((i) = j ∨ (i) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ub : V Q (j) = true := by rw [v0 _ _ (by omega)]; exact (show Q (j) = true from by show decide ((j) = j ∨ (j) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have hfin := fin (fun w => w = i ∨ w = j) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = false := (hf i i hi hi).trans (by simp)
            have f2 : V Q (n + n + jo) = true := (hf j i hj hi).trans (by simp <;> omega)
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + i) = decide (k = j ∨ k = n + i)
            have hH2 : ¬(k = i ∨ k = j) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = i ∨ n + n + k = j) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = i ∨ w = j) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl | rfl
            · exact sa k hk (by rw [ea]; exact hw)
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = i ∨ n + n + jo = j := hH
            omega
    · by_cases hij : i = j
      · subst hij
        cases hAn : An h with
        | false =>
          refine hhT ⟨i, hi, hh, hAn, Or.inl ⟨ea, eb⟩, fun k hk hr => ?_⟩
          rcases hr with hr | hr
          · exact sa k hk (by rw [ea]; exact hr)
          · exact sb k hk (by rw [eb]; exact hr)
        | true =>
          obtain ⟨P, Q, pq, px, qx, hdiff⟩ := seesC i hi
          refine hdiff (fin (fun w => w = n + i) P Q (fun k _ hk => pq k hk) ?_ ?_ (by omega))
          · intro k hk _ hr
            exact sb k hk (by rw [eb]; exact hr)
          · rw [hVh, hVh, if_pos hAn, if_pos hAn, ea, eb, v0 _ i (by omega), v0 _ i (by omega), px, qx]
            simp
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + v)
          let Q : ℕ → Bool := fun k => decide (k = n + v)
          have va : V P (i) = true := by rw [v0 _ _ (by omega)]; exact (show P (i) = true from by show decide ((i) = i ∨ (i) = n + v) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (n + j) = false := by rw [v0 _ _ (by omega)]; exact (show P (n + j) = false from by show decide ((n + j) = i ∨ (n + j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ua : V Q (i) = false := by rw [v0 _ _ (by omega)]; exact (show Q (i) = false from by show decide ((i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ub : V Q (n + j) = false := by rw [v0 _ _ (by omega)]; exact (show Q (n + j) = false from by show decide ((n + j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have hfin := fin (fun w => w = i) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i v hi hv).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + v) = decide (k = n + v)
            have hH2 : ¬(k = i) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = i) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = i) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = i := hH
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + j)
          let Q : ℕ → Bool := fun k => decide (k = i)
          have va : V P (i) = true := by rw [v0 _ _ (by omega)]; exact (show P (i) = true from by show decide ((i) = i ∨ (i) = n + j) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (n + j) = true := by rw [v0 _ _ (by omega)]; exact (show P (n + j) = true from by show decide ((n + j) = i ∨ (n + j) = n + j) = true; rw [decide_eq_true_eq] <;> omega)
          have ua : V Q (i) = true := by rw [v0 _ _ (by omega)]; exact (show Q (i) = true from by show decide ((i) = i) = true; rw [decide_eq_true_eq] <;> omega)
          have ub : V Q (n + j) = false := by rw [v0 _ _ (by omega)]; exact (show Q (n + j) = false from by show decide ((n + j) = i) = false; rw [decide_eq_false_iff_not] <;> omega)
          have hfin := fin (fun w => w = i ∨ w = n + j) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i j hi hj).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 i hi
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + j) = decide (k = i)
            have hH2 : ¬(k = i ∨ k = n + j) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = i ∨ n + n + k = n + j) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = i ∨ w = n + j) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl | rfl
            · exact sa k hk (by rw [ea]; exact hw)
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = i ∨ n + n + jo = n + j := hH
            omega
    · have hj := hTb.1
      have xb := hTb.2.2.2.2
      by_cases hij : i = j
      · subst hij
        exact Tne i jb hTb (xb h hh (Or.inl (by rw [← ea]; exact ra))).symm
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + v)
          let Q : ℕ → Bool := fun k => decide (k = n + v)
          have va : V P (i) = true := by rw [v0 _ _ (by omega)]; exact (show P (i) = true from by show decide ((i) = i ∨ (i) = n + v) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (n + n + jb) = false := by rw [VT j jb hTb P, (show P (j) = false from by show decide ((j) = i ∨ (j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega), (show P (n + j) = false from by show decide ((n + j) = i ∨ (n + j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ua : V Q (i) = false := by rw [v0 _ _ (by omega)]; exact (show Q (i) = false from by show decide ((i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ub : V Q (n + n + jb) = false := by rw [VT j jb hTb Q, (show Q (j) = false from by show decide ((j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + j) = false from by show decide ((n + j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have hfin := fin (fun w => w = i) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i v hi hv).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + v) = decide (k = n + v)
            have hH2 : ¬(k = i) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = i) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = i) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = i := hH
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + j)
          let Q : ℕ → Bool := fun k => decide (k = i)
          have va : V P (i) = true := by rw [v0 _ _ (by omega)]; exact (show P (i) = true from by show decide ((i) = i ∨ (i) = n + j) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (n + n + jb) = true := by rw [VT j jb hTb P, (show P (j) = false from by show decide ((j) = i ∨ (j) = n + j) = false; rw [decide_eq_false_iff_not] <;> omega), (show P (n + j) = true from by show decide ((n + j) = i ∨ (n + j) = n + j) = true; rw [decide_eq_true_eq] <;> omega)]; rfl
          have ua : V Q (i) = true := by rw [v0 _ _ (by omega)]; exact (show Q (i) = true from by show decide ((i) = i) = true; rw [decide_eq_true_eq] <;> omega)
          have ub : V Q (n + n + jb) = false := by rw [VT j jb hTb Q, (show Q (j) = false from by show decide ((j) = i) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + j) = false from by show decide ((n + j) = i) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have hfin := fin (fun w => w = i ∨ (w = j ∨ w = n + j ∨ w = n + n + jb)) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i j hi hj).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 i hi
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + j) = decide (k = i)
            have hH2 : ¬(k = i ∨ (k = j ∨ k = n + j ∨ k = n + n + jb)) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = i ∨ (n + n + k = j ∨ n + n + k = n + j ∨ n + n + k = n + n + jb)) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = i ∨ (w = j ∨ w = n + j ∨ w = n + n + jb)) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl | (rfl | rfl | rfl)
            · exact sa k hk (by rw [ea]; exact hw)
            · exfalso; have := xb k hk (Or.inl hw); omega
            · exfalso; have := xb k hk (Or.inr hw); omega
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = i ∨ (n + n + jo = j ∨ n + n + jo = n + j ∨ n + n + jo = n + n + jb) := hH
            have := Tno j jb hTb
            omega
  · rcases atom _ rb with ⟨j, hj, eb⟩ | ⟨j, hj, eb⟩ | ⟨j, jb, eb, hTb⟩
    · by_cases hij : i = j
      · subst hij
        cases hAn : An h with
        | false =>
          refine hhT ⟨i, hi, hh, hAn, Or.inr ⟨ea, eb⟩, fun k hk hr => ?_⟩
          rcases hr with hr | hr
          · exact sb k hk (by rw [eb]; exact hr)
          · exact sa k hk (by rw [ea]; exact hr)
        | true =>
          obtain ⟨P, Q, pq, px, qx, hdiff⟩ := seesC i hi
          refine hdiff (fin (fun w => w = n + i) P Q (fun k _ hk => pq k hk) ?_ ?_ (by omega))
          · intro k hk _ hr
            exact sa k hk (by rw [ea]; exact hr)
          · rw [hVh, hVh, if_pos hAn, if_pos hAn, ea, eb, v0 _ i (by omega), v0 _ i (by omega), px, qx]
            simp
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = v ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = v)
          have va : V P (n + i) = true := by rw [v0 _ _ (by omega)]; exact (show P (n + i) = true from by show decide ((n + i) = v ∨ (n + i) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (j) = false := by rw [v0 _ _ (by omega)]; exact (show P (j) = false from by show decide ((j) = v ∨ (j) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ua : V Q (n + i) = false := by rw [v0 _ _ (by omega)]; exact (show Q (n + i) = false from by show decide ((n + i) = v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ub : V Q (j) = false := by rw [v0 _ _ (by omega)]; exact (show Q (j) = false from by show decide ((j) = v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have hfin := fin (fun w => w = n + i) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf v i hv hi).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = v ∨ k = n + i) = decide (k = v)
            have hH2 : ¬(k = n + i) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = n + i) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = n + i) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = n + i := hH
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = j ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = j)
          have va : V P (n + i) = true := by rw [v0 _ _ (by omega)]; exact (show P (n + i) = true from by show decide ((n + i) = j ∨ (n + i) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (j) = true := by rw [v0 _ _ (by omega)]; exact (show P (j) = true from by show decide ((j) = j ∨ (j) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have ua : V Q (n + i) = false := by rw [v0 _ _ (by omega)]; exact (show Q (n + i) = false from by show decide ((n + i) = j) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ub : V Q (j) = true := by rw [v0 _ _ (by omega)]; exact (show Q (j) = true from by show decide ((j) = j) = true; rw [decide_eq_true_eq] <;> omega)
          have hfin := fin (fun w => w = n + i ∨ w = j) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf j i hj hi).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 j hj
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = j ∨ k = n + i) = decide (k = j)
            have hH2 : ¬(k = n + i ∨ k = j) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = n + i ∨ n + n + k = j) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = n + i ∨ w = j) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl | rfl
            · exact sa k hk (by rw [ea]; exact hw)
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = n + i ∨ n + n + jo = j := hH
            omega
    · by_cases hij : i = j
      · subst hij
        exact hab (ea.trans eb.symm)
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = v ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = v)
          have va : V P (n + i) = true := by rw [v0 _ _ (by omega)]; exact (show P (n + i) = true from by show decide ((n + i) = v ∨ (n + i) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (n + j) = false := by rw [v0 _ _ (by omega)]; exact (show P (n + j) = false from by show decide ((n + j) = v ∨ (n + j) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ua : V Q (n + i) = false := by rw [v0 _ _ (by omega)]; exact (show Q (n + i) = false from by show decide ((n + i) = v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ub : V Q (n + j) = false := by rw [v0 _ _ (by omega)]; exact (show Q (n + j) = false from by show decide ((n + j) = v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have hfin := fin (fun w => w = n + i) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf v i hv hi).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = v ∨ k = n + i) = decide (k = v)
            have hH2 : ¬(k = n + i) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = n + i) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = n + i) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = n + i := hH
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = i ∨ k = n + j)
          have va : V P (n + i) = true := by rw [v0 _ _ (by omega)]; exact (show P (n + i) = true from by show decide ((n + i) = i ∨ (n + i) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (n + j) = false := by rw [v0 _ _ (by omega)]; exact (show P (n + j) = false from by show decide ((n + j) = i ∨ (n + j) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ua : V Q (n + i) = false := by rw [v0 _ _ (by omega)]; exact (show Q (n + i) = false from by show decide ((n + i) = i ∨ (n + i) = n + j) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ub : V Q (n + j) = true := by rw [v0 _ _ (by omega)]; exact (show Q (n + j) = true from by show decide ((n + j) = i ∨ (n + j) = n + j) = true; rw [decide_eq_true_eq] <;> omega)
          have hfin := fin (fun w => w = n + i ∨ w = n + j) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = false := (hf i i hi hi).trans (by simp)
            have f2 : V Q (n + n + jo) = true := (hf i j hi hj).trans (by simp <;> omega)
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + i) = decide (k = i ∨ k = n + j)
            have hH2 : ¬(k = n + i ∨ k = n + j) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = n + i ∨ n + n + k = n + j) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = n + i ∨ w = n + j) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl | rfl
            · exact sa k hk (by rw [ea]; exact hw)
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = n + i ∨ n + n + jo = n + j := hH
            omega
    · have hj := hTb.1
      have xb := hTb.2.2.2.2
      by_cases hij : i = j
      · subst hij
        exact Tne i jb hTb (xb h hh (Or.inr (by rw [← ea]; exact ra))).symm
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = v ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = v)
          have va : V P (n + i) = true := by rw [v0 _ _ (by omega)]; exact (show P (n + i) = true from by show decide ((n + i) = v ∨ (n + i) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (n + n + jb) = false := by rw [VT j jb hTb P, (show P (j) = false from by show decide ((j) = v ∨ (j) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega), (show P (n + j) = false from by show decide ((n + j) = v ∨ (n + j) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ua : V Q (n + i) = false := by rw [v0 _ _ (by omega)]; exact (show Q (n + i) = false from by show decide ((n + i) = v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ub : V Q (n + n + jb) = false := by rw [VT j jb hTb Q, (show Q (j) = false from by show decide ((j) = v) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + j) = false from by show decide ((n + j) = v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have hfin := fin (fun w => w = n + i) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf v i hv hi).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = v ∨ k = n + i) = decide (k = v)
            have hH2 : ¬(k = n + i) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = n + i) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = n + i) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = n + i := hH
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = j ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = n + i)
          have va : V P (n + i) = true := by rw [v0 _ _ (by omega)]; exact (show P (n + i) = true from by show decide ((n + i) = j ∨ (n + i) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have vb : V P (n + n + jb) = true := by rw [VT j jb hTb P, (show P (j) = true from by show decide ((j) = j ∨ (j) = n + i) = true; rw [decide_eq_true_eq] <;> omega), (show P (n + j) = false from by show decide ((n + j) = j ∨ (n + j) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ua : V Q (n + i) = true := by rw [v0 _ _ (by omega)]; exact (show Q (n + i) = true from by show decide ((n + i) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have ub : V Q (n + n + jb) = false := by rw [VT j jb hTb Q, (show Q (j) = false from by show decide ((j) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + j) = false from by show decide ((n + j) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have hfin := fin (fun w => w = n + i ∨ (w = j ∨ w = n + j ∨ w = n + n + jb)) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf j i hj hi).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 i hi
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = j ∨ k = n + i) = decide (k = n + i)
            have hH2 : ¬(k = n + i ∨ (k = j ∨ k = n + j ∨ k = n + n + jb)) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = n + i ∨ (n + n + k = j ∨ n + n + k = n + j ∨ n + n + k = n + n + jb)) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = n + i ∨ (w = j ∨ w = n + j ∨ w = n + n + jb)) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl | (rfl | rfl | rfl)
            · exact sa k hk (by rw [ea]; exact hw)
            · exfalso; have := xb k hk (Or.inl hw); omega
            · exfalso; have := xb k hk (Or.inr hw); omega
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = n + i ∨ (n + n + jo = j ∨ n + n + jo = n + j ∨ n + n + jo = n + n + jb) := hH
            have := Tno j jb hTb
            omega
  · rcases atom _ rb with ⟨j, hj, eb⟩ | ⟨j, hj, eb⟩ | ⟨j, jb, eb, hTb⟩
    · have hi := hTa.1
      have xa := hTa.2.2.2.2
      by_cases hij : i = j
      · subst hij
        exact Tne i ja hTa (xa h hh (Or.inl (by rw [← eb]; exact rb))).symm
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + v)
          let Q : ℕ → Bool := fun k => decide (k = n + v)
          have va : V P (n + n + ja) = true := by rw [VT i ja hTa P, (show P (i) = true from by show decide ((i) = i ∨ (i) = n + v) = true; rw [decide_eq_true_eq] <;> omega), (show P (n + i) = false from by show decide ((n + i) = i ∨ (n + i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have vb : V P (j) = false := by rw [v0 _ _ (by omega)]; exact (show P (j) = false from by show decide ((j) = i ∨ (j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ua : V Q (n + n + ja) = false := by rw [VT i ja hTa Q, (show Q (i) = false from by show decide ((i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + i) = false from by show decide ((n + i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ub : V Q (j) = false := by rw [v0 _ _ (by omega)]; exact (show Q (j) = false from by show decide ((j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have hfin := fin (fun w => (w = i ∨ w = n + i ∨ w = n + n + ja)) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i v hi hv).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + v) = decide (k = n + v)
            have hH2 : ¬((k = i ∨ k = n + i ∨ k = n + n + ja)) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬((n + n + k = i ∨ n + n + k = n + i ∨ n + n + k = n + n + ja)) := hkH
            have hr2 : ∃ w, rd A B k w ∧ ((w = i ∨ w = n + i ∨ w = n + n + ja)) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with (rfl | rfl | rfl)
            · exfalso; have := xa k hk (Or.inl hw); omega
            · exfalso; have := xa k hk (Or.inr hw); omega
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : (n + n + jo = i ∨ n + n + jo = n + i ∨ n + n + jo = n + n + ja) := hH
            have := Tno i ja hTa
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = j ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = j)
          have va : V P (n + n + ja) = true := by rw [VT i ja hTa P, (show P (i) = false from by show decide ((i) = j ∨ (i) = n + i) = false; rw [decide_eq_false_iff_not] <;> omega), (show P (n + i) = true from by show decide ((n + i) = j ∨ (n + i) = n + i) = true; rw [decide_eq_true_eq] <;> omega)]; rfl
          have vb : V P (j) = true := by rw [v0 _ _ (by omega)]; exact (show P (j) = true from by show decide ((j) = j ∨ (j) = n + i) = true; rw [decide_eq_true_eq] <;> omega)
          have ua : V Q (n + n + ja) = false := by rw [VT i ja hTa Q, (show Q (i) = false from by show decide ((i) = j) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + i) = false from by show decide ((n + i) = j) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ub : V Q (j) = true := by rw [v0 _ _ (by omega)]; exact (show Q (j) = true from by show decide ((j) = j) = true; rw [decide_eq_true_eq] <;> omega)
          have hfin := fin (fun w => (w = i ∨ w = n + i ∨ w = n + n + ja) ∨ w = j) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf j i hj hi).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 j hj
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = j ∨ k = n + i) = decide (k = j)
            have hH2 : ¬((k = i ∨ k = n + i ∨ k = n + n + ja) ∨ k = j) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬((n + n + k = i ∨ n + n + k = n + i ∨ n + n + k = n + n + ja) ∨ n + n + k = j) := hkH
            have hr2 : ∃ w, rd A B k w ∧ ((w = i ∨ w = n + i ∨ w = n + n + ja) ∨ w = j) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with (rfl | rfl | rfl) | rfl
            · exfalso; have := xa k hk (Or.inl hw); omega
            · exfalso; have := xa k hk (Or.inr hw); omega
            · exact sa k hk (by rw [ea]; exact hw)
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : (n + n + jo = i ∨ n + n + jo = n + i ∨ n + n + jo = n + n + ja) ∨ n + n + jo = j := hH
            have := Tno i ja hTa
            omega
    · have hi := hTa.1
      have xa := hTa.2.2.2.2
      by_cases hij : i = j
      · subst hij
        exact Tne i ja hTa (xa h hh (Or.inr (by rw [← eb]; exact rb))).symm
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + v)
          let Q : ℕ → Bool := fun k => decide (k = n + v)
          have va : V P (n + n + ja) = true := by rw [VT i ja hTa P, (show P (i) = true from by show decide ((i) = i ∨ (i) = n + v) = true; rw [decide_eq_true_eq] <;> omega), (show P (n + i) = false from by show decide ((n + i) = i ∨ (n + i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have vb : V P (n + j) = false := by rw [v0 _ _ (by omega)]; exact (show P (n + j) = false from by show decide ((n + j) = i ∨ (n + j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have ua : V Q (n + n + ja) = false := by rw [VT i ja hTa Q, (show Q (i) = false from by show decide ((i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + i) = false from by show decide ((n + i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ub : V Q (n + j) = false := by rw [v0 _ _ (by omega)]; exact (show Q (n + j) = false from by show decide ((n + j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)
          have hfin := fin (fun w => (w = i ∨ w = n + i ∨ w = n + n + ja)) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i v hi hv).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + v) = decide (k = n + v)
            have hH2 : ¬((k = i ∨ k = n + i ∨ k = n + n + ja)) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬((n + n + k = i ∨ n + n + k = n + i ∨ n + n + k = n + n + ja)) := hkH
            have hr2 : ∃ w, rd A B k w ∧ ((w = i ∨ w = n + i ∨ w = n + n + ja)) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with (rfl | rfl | rfl)
            · exfalso; have := xa k hk (Or.inl hw); omega
            · exfalso; have := xa k hk (Or.inr hw); omega
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : (n + n + jo = i ∨ n + n + jo = n + i ∨ n + n + jo = n + n + ja) := hH
            have := Tno i ja hTa
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + j)
          let Q : ℕ → Bool := fun k => decide (k = n + j)
          have va : V P (n + n + ja) = true := by rw [VT i ja hTa P, (show P (i) = true from by show decide ((i) = i ∨ (i) = n + j) = true; rw [decide_eq_true_eq] <;> omega), (show P (n + i) = false from by show decide ((n + i) = i ∨ (n + i) = n + j) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have vb : V P (n + j) = true := by rw [v0 _ _ (by omega)]; exact (show P (n + j) = true from by show decide ((n + j) = i ∨ (n + j) = n + j) = true; rw [decide_eq_true_eq] <;> omega)
          have ua : V Q (n + n + ja) = false := by rw [VT i ja hTa Q, (show Q (i) = false from by show decide ((i) = n + j) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + i) = false from by show decide ((n + i) = n + j) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ub : V Q (n + j) = true := by rw [v0 _ _ (by omega)]; exact (show Q (n + j) = true from by show decide ((n + j) = n + j) = true; rw [decide_eq_true_eq] <;> omega)
          have hfin := fin (fun w => (w = i ∨ w = n + i ∨ w = n + n + ja) ∨ w = n + j) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i j hi hj).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 j hj
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + j) = decide (k = n + j)
            have hH2 : ¬((k = i ∨ k = n + i ∨ k = n + n + ja) ∨ k = n + j) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬((n + n + k = i ∨ n + n + k = n + i ∨ n + n + k = n + n + ja) ∨ n + n + k = n + j) := hkH
            have hr2 : ∃ w, rd A B k w ∧ ((w = i ∨ w = n + i ∨ w = n + n + ja) ∨ w = n + j) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with (rfl | rfl | rfl) | rfl
            · exfalso; have := xa k hk (Or.inl hw); omega
            · exfalso; have := xa k hk (Or.inr hw); omega
            · exact sa k hk (by rw [ea]; exact hw)
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : (n + n + jo = i ∨ n + n + jo = n + i ∨ n + n + jo = n + n + ja) ∨ n + n + jo = n + j := hH
            have := Tno i ja hTa
            omega
    · have hi := hTa.1
      have hj := hTb.1
      have xa := hTa.2.2.2.2
      have xb := hTb.2.2.2.2
      by_cases hij : i = j
      · subst hij
        exfalso
        have e1 : ja = jb := by
          refine xb ja hTa.2.1 ?_
          rcases hTa.2.2.2.1 with ⟨e, _⟩ | ⟨_, e⟩
          · exact Or.inl (Or.inl e)
          · exact Or.inl (Or.inr e)
        exact hab (by rw [ea, eb, e1])
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + v)
          let Q : ℕ → Bool := fun k => decide (k = n + v)
          have va : V P (n + n + ja) = true := by rw [VT i ja hTa P, (show P (i) = true from by show decide ((i) = i ∨ (i) = n + v) = true; rw [decide_eq_true_eq] <;> omega), (show P (n + i) = false from by show decide ((n + i) = i ∨ (n + i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have vb : V P (n + n + jb) = false := by rw [VT j jb hTb P, (show P (j) = false from by show decide ((j) = i ∨ (j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega), (show P (n + j) = false from by show decide ((n + j) = i ∨ (n + j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ua : V Q (n + n + ja) = false := by rw [VT i ja hTa Q, (show Q (i) = false from by show decide ((i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + i) = false from by show decide ((n + i) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ub : V Q (n + n + jb) = false := by rw [VT j jb hTb Q, (show Q (j) = false from by show decide ((j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + j) = false from by show decide ((n + j) = n + v) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have hfin := fin (fun w => (w = i ∨ w = n + i ∨ w = n + n + ja)) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i v hi hv).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + v) = decide (k = n + v)
            have hH2 : ¬((k = i ∨ k = n + i ∨ k = n + n + ja)) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬((n + n + k = i ∨ n + n + k = n + i ∨ n + n + k = n + n + ja)) := hkH
            have hr2 : ∃ w, rd A B k w ∧ ((w = i ∨ w = n + i ∨ w = n + n + ja)) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with (rfl | rfl | rfl)
            · exfalso; have := xa k hk (Or.inl hw); omega
            · exfalso; have := xa k hk (Or.inr hw); omega
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : (n + n + jo = i ∨ n + n + jo = n + i ∨ n + n + jo = n + n + ja) := hH
            have := Tno i ja hTa
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + j)
          let Q : ℕ → Bool := fun k => decide (k = i)
          have va : V P (n + n + ja) = true := by rw [VT i ja hTa P, (show P (i) = true from by show decide ((i) = i ∨ (i) = n + j) = true; rw [decide_eq_true_eq] <;> omega), (show P (n + i) = false from by show decide ((n + i) = i ∨ (n + i) = n + j) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have vb : V P (n + n + jb) = true := by rw [VT j jb hTb P, (show P (j) = false from by show decide ((j) = i ∨ (j) = n + j) = false; rw [decide_eq_false_iff_not] <;> omega), (show P (n + j) = true from by show decide ((n + j) = i ∨ (n + j) = n + j) = true; rw [decide_eq_true_eq] <;> omega)]; rfl
          have ua : V Q (n + n + ja) = true := by rw [VT i ja hTa Q, (show Q (i) = true from by show decide ((i) = i) = true; rw [decide_eq_true_eq] <;> omega), (show Q (n + i) = false from by show decide ((n + i) = i) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have ub : V Q (n + n + jb) = false := by rw [VT j jb hTb Q, (show Q (j) = false from by show decide ((j) = i) = false; rw [decide_eq_false_iff_not] <;> omega), (show Q (n + j) = false from by show decide ((n + j) = i) = false; rw [decide_eq_false_iff_not] <;> omega)]; rfl
          have hfin := fin (fun w => (w = i ∨ w = n + i ∨ w = n + n + ja) ∨ (w = j ∨ w = n + j ∨ w = n + n + jb)) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i j hi hj).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 i hi
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + j) = decide (k = i)
            have hH2 : ¬((k = i ∨ k = n + i ∨ k = n + n + ja) ∨ (k = j ∨ k = n + j ∨ k = n + n + jb)) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬((n + n + k = i ∨ n + n + k = n + i ∨ n + n + k = n + n + ja) ∨ (n + n + k = j ∨ n + n + k = n + j ∨ n + n + k = n + n + jb)) := hkH
            have hr2 : ∃ w, rd A B k w ∧ ((w = i ∨ w = n + i ∨ w = n + n + ja) ∨ (w = j ∨ w = n + j ∨ w = n + n + jb)) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with (rfl | rfl | rfl) | (rfl | rfl | rfl)
            · exfalso; have := xa k hk (Or.inl hw); omega
            · exfalso; have := xa k hk (Or.inr hw); omega
            · exact sa k hk (by rw [ea]; exact hw)
            · exfalso; have := xb k hk (Or.inl hw); omega
            · exfalso; have := xb k hk (Or.inr hw); omega
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : (n + n + jo = i ∨ n + n + jo = n + i ∨ n + n + jo = n + n + ja) ∨ (n + n + jo = j ∨ n + n + jo = n + j ∨ n + n + jo = n + n + jb) := hH
            have := Tno i ja hTa
            have := Tno j jb hTb
            omega

def onl (n : ℕ) (Q : ℕ → Bool) : List Bool := (List.range (n + n)).map Q

theorem onl_len (n : ℕ) (Q : ℕ → Bool) : (onl n Q).length = n + n := by simp [onl]

theorem onl_get (n : ℕ) (Q : ℕ → Bool) (k : ℕ) (hk : k < n + n) : (onl n Q).getD k false = Q k := by
  simp [onl, List.getD_eq_getElem?_getD, List.getElem?_range hk]

theorem one_onl (n : ℕ) (u v : Fin n) : PEqualNP.Represents.oneEach u v = onl n (pt n u v) := by
  refine List.ext_getElem (by simp [PEqualNP.Represents.oneEach, onl]) fun k h1 h2 => ?_
  have hk : k < n + n := by simpa [onl] using h2
  simp only [PEqualNP.Represents.oneEach, onl, List.getElem_map, List.getElem_range, pt]
  by_cases h : k < n
  · rw [List.getElem_append_left (by simpa using h)]
    simp only [List.getElem_ofFn, Fin.ext_iff]
    rw [decide_eq_decide]
    have := v.isLt
    omega
  · rw [List.getElem_append_right (by simpa using h)]
    simp only [List.getElem_ofFn, List.length_ofFn, Fin.ext_iff]
    rw [decide_eq_decide]
    have := u.isLt
    omega

theorem vmono (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (Q R : ℕ → Bool) (h : ∀ k, Q k = true → R k = true) (w : ℕ)
    (hw : (run C.gates (onl n Q)).getD w false = true) : (run C.gates (onl n R)).getD w false = true := by
  refine mono C.gates (onl n Q) (onl n R) (by simp [onl]) ?_ (fun g hg => by simpa using (hC g hg).1) w hw
  intro i hi
  by_cases hin : i < n + n
  · rw [onl_get n _ i hin] at hi ⊢; exact h i hi
  · rw [List.getD_eq_default _ _ (by rw [onl_len]; omega)] at hi; cases hi

theorem two (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (hf : ∀ u v : Fin 2, C.eval (PEqualNP.Represents.oneEach u v) = decide (u ≠ v)) : 3 ≤ C.size := by
  classical
  obtain ⟨S, hS, hdet⟩ := det C.gates 4 (fun g hg => (hC g hg).2) {C.output}
  have hv : ∀ u v : Fin 2, (run C.gates (onl 2 (pt 2 u v))).getD C.output false = decide (u ≠ v) := by
    intro u v
    rw [← one_onl]; exact hf u v
  have row : ∀ u : Fin 2, (run C.gates (onl 2 fun k => decide (k = (u : ℕ)))).getD C.output false = false := by
    intro u
    by_contra h
    have h1 := vmono 2 C hC (fun k => decide (k = (u : ℕ))) (pt 2 u u) (by
      intro k hk
      have : k = (u : ℕ) := by simpa using hk
      simp [pt, this]) C.output (by simpa using h)
    rw [hv u u] at h1
    simp at h1
  have col : ∀ u : Fin 2, (run C.gates (onl 2 fun k => decide (k = 2 + (u : ℕ)))).getD C.output false = false := by
    intro u
    by_contra h
    have h1 := vmono 2 C hC (fun k => decide (k = 2 + (u : ℕ))) (pt 2 u u) (by
      intro k hk
      have : k = 2 + (u : ℕ) := by simpa using hk
      simp [pt, this]) C.output (by simpa using h)
    rw [hv u u] at h1
    simp at h1
  have see : ∀ (w : ℕ) (Q R : ℕ → Bool), (∀ k, k ≠ w → Q k = R k) → (run C.gates (onl 2 Q)).getD C.output false ≠ (run C.gates (onl 2 R)).getD C.output false → w ∈ S := by
    intro w Q R hQR hne
    by_contra hw
    refine hne (hdet (onl 2 Q) (onl 2 R) (by simp [onl]) (by simp [onl]) (fun i hi => ?_) C.output (by simp))
    by_cases hin : i < 2 + 2
    · rw [onl_get 2 _ i hin, onl_get 2 _ i hin]
      exact hQR i fun e => hw (e ▸ hi)
    · rw [List.getD_eq_default _ _ (by rw [onl_len]; omega), List.getD_eq_default _ _ (by rw [onl_len]; omega)]
  have h0 : 0 ∈ S := see 0 (pt 2 (0 : Fin 2) (1 : Fin 2)) (fun k => decide (k = 2 + ((1 : Fin 2) : ℕ))) (by intro k hk; simp [pt, hk]) (by rw [hv, col]; decide)
  have h1 : 1 ∈ S := see 1 (pt 2 (1 : Fin 2) (0 : Fin 2)) (fun k => decide (k = 2 + ((0 : Fin 2) : ℕ))) (by intro k hk; simp [pt, hk]) (by rw [hv, col]; decide)
  have h2 : 2 ∈ S := see 2 (pt 2 (1 : Fin 2) (0 : Fin 2)) (fun k => decide (k = ((1 : Fin 2) : ℕ))) (by intro k hk; simp [pt, hk]) (by rw [hv, row]; decide)
  have h3 : 3 ∈ S := see 3 (pt 2 (0 : Fin 2) (1 : Fin 2)) (fun k => decide (k = ((0 : Fin 2) : ℕ))) (by intro k hk; simp [pt, hk]) (by rw [hv, row]; decide)
  have hsub : ({0, 1, 2, 3} : Finset ℕ) ⊆ S := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> assumption
  have hc := Finset.card_le_card hsub
  have e : ({0, 1, 2, 3} : Finset ℕ).card = 4 := by decide
  rw [e] at hc
  rw [Finset.card_singleton] at hS
  have : C.size = C.gates.length := rfl
  omega

theorem step3 (k : ℕ) (hk : 2 ≤ k) (C0 : Circuit) (hC0 : PEqualNP.MetaComplexity.Monotone2 C0)
    (hf0 : ∀ u v : Fin (k + 1), C0.eval (PEqualNP.Represents.oneEach u v) = decide (u ≠ v)) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size + 3 ≤ C0.size ∧
      ∀ u v : Fin k, D.eval (PEqualNP.Represents.oneEach u v) = decide (u ≠ v) := by
  classical
  have hex : ∃ s, ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = s ∧ ∀ u v : Fin (k + 1), C.eval (PEqualNP.Represents.oneEach u v) = decide (u ≠ v) := ⟨_, C0, hC0, rfl, hf0⟩
  obtain ⟨C, hC, hCs, hf⟩ := Nat.find_spec hex
  have hmin : ∀ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D → (∀ u v : Fin (k + 1), D.eval (PEqualNP.Represents.oneEach u v) = decide (u ≠ v)) → C.size ≤ D.size := by
    intro D h1 h2
    rw [hCs]
    exact Nat.find_min' hex ⟨D, h1, rfl, h2⟩
  have hle : C.size ≤ C0.size := hmin C0 hC0 hf0
  set n := k + 1 with hn
  have hn3 : 3 ≤ n := by omega
  let V : (ℕ → Bool) → ℕ → Bool := fun Q w => (run C.gates (onl n Q)).getD w false
  have hm : C.size = C.gates.length := rfl
  have hV : ∀ u v : Fin n, ∀ w, V (pt n u v) w = (run C.gates (PEqualNP.Represents.oneEach u v)).getD w false := by
    intro u v w
    rw [one_onl]
  have hlen1 : ∀ u v : Fin n, (PEqualNP.Represents.oneEach u v).length = n + n := fun u v => by
    simp only [PEqualNP.Represents.oneEach, List.length_append, List.length_ofFn]
  have nonc : ¬∃ b, ∀ p : Fin n × Fin n, C.eval (PEqualNP.Represents.oneEach p.1 p.2) = b := by
    rintro ⟨b, hb⟩
    have h1 := hb (⟨0, by omega⟩, ⟨0, by omega⟩)
    have h2 := hb (⟨0, by omega⟩, ⟨1, by omega⟩)
    rw [hf] at h1 h2
    rw [← h1] at h2
    simp at h2
  have irr0 : ∀ j < C.gates.length, ¬((∃ b, ∀ p : Fin n × Fin n, (run C.gates (PEqualNP.Represents.oneEach p.1 p.2)).getD (n + n + j) false = b) ∨
      ∃ w < n + n + j, ∀ p : Fin n × Fin n, (run C.gates (PEqualNP.Represents.oneEach p.1 p.2)).getD (n + n + j) false = (run C.gates (PEqualNP.Represents.oneEach p.1 p.2)).getD w false) := by
    intro j hj hbad
    obtain ⟨D, d1, d2, d3⟩ := engine3 (n + n) (n + n) C (fun p : Fin n × Fin n => PEqualNP.Represents.oneEach p.1 p.2) (fun p => PEqualNP.Represents.oneEach p.1 p.2)
      (fun p => hlen1 _ _) (fun p => hlen1 _ _) {j} hC (fun w hw => Or.inr ⟨w, hw, fun _ => rfl⟩) nonc (by
        intro i hi
        have : i = j := by simpa using hi
        subst this
        exact ⟨hj, hbad⟩)
    have := hmin D d1 fun u v => (d3 (u, v)).trans (hf u v)
    rw [Finset.card_singleton] at d2
    omega
  have shape : ∀ j, j < C.gates.length → ∃ a b : ℕ, ∃ c : Bool, a < n + n + j ∧ b < n + n + j ∧ a ≠ b ∧
      ∀ Q, V Q (n + n + j) = if c = true then V Q a && V Q b else V Q a || V Q b := by
    intro j hj
    obtain ⟨hop, hl⟩ := hC _ (List.getElem_mem hj)
    have hop' : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or := by simpa using hop
    have rg0 : ∀ l : List Bool, l.length = n + n → (run C.gates l).getD (n + n + j) false = C.gates[j].op.eval (C.gates[j].inputs.map fun i => if i < n + n + j then (run C.gates l).getD i false else false) := by
      intro l hll
      have := run_gate C.gates l j hj
      rw [hll] at this
      exact this
    have bad := irr0 j hj
    generalize hin : C.gates[j].inputs = l at hl rg0
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · exact absurd (Or.inl ⟨C.gates[j].op.eval [], fun p => by rw [rg0 _ (hlen1 _ _)]; rfl⟩) bad
    · by_cases ha : a < n + n + j
      · refine absurd (Or.inr ⟨a, ha, fun p => ?_⟩) bad
        rw [rg0 _ (hlen1 _ _)]
        rcases hop' with e | e <;> simp [e, GateOp.eval, ha]
      · refine absurd (Or.inl ⟨false, fun p => ?_⟩) bad
        rw [rg0 _ (hlen1 _ _)]
        rcases hop' with e | e <;> simp [e, GateOp.eval, ha]
    · by_cases ha : a < n + n + j
      · by_cases hb : b < n + n + j
        · by_cases hab : a = b
          · refine absurd (Or.inr ⟨a, ha, fun p => ?_⟩) bad
            rw [rg0 _ (hlen1 _ _), ← hab]
            rcases hop' with e | e <;> simp [e, GateOp.eval, ha]
          · rcases hop' with e | e
            · refine ⟨a, b, true, ha, hb, hab, fun Q => ?_⟩
              have := rg0 (onl n Q) (onl_len n Q)
              rw [e] at this
              simp only [List.map_cons, List.map_nil, if_pos ha, if_pos hb, GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true] at this
              simpa [V] using this
            · refine ⟨a, b, false, ha, hb, hab, fun Q => ?_⟩
              have := rg0 (onl n Q) (onl_len n Q)
              rw [e] at this
              simp only [List.map_cons, List.map_nil, if_pos ha, if_pos hb, GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] at this
              simpa [V] using this
        · rcases hop' with e | e
          · refine absurd (Or.inl ⟨false, fun p => ?_⟩) bad
            rw [rg0 _ (hlen1 _ _)]
            simp [e, GateOp.eval, hb]
          · refine absurd (Or.inr ⟨a, ha, fun p => ?_⟩) bad
            rw [rg0 _ (hlen1 _ _)]
            simp [e, GateOp.eval, ha, hb]
      · rcases hop' with e | e
        · refine absurd (Or.inl ⟨false, fun p => ?_⟩) bad
          rw [rg0 _ (hlen1 _ _)]
          simp [e, GateOp.eval, ha]
        · by_cases hb : b < n + n + j
          · refine absurd (Or.inr ⟨b, hb, fun p => ?_⟩) bad
            rw [rg0 _ (hlen1 _ _)]
            simp [e, GateOp.eval, ha, hb]
          · refine absurd (Or.inl ⟨false, fun p => ?_⟩) bad
            rw [rg0 _ (hlen1 _ _)]
            simp [e, GateOp.eval, ha, hb]
    · simp at hl
  choose! A B An hA hB hAB hv1 using shape
  have hout : C.output < n + n + C.gates.length := by
    by_contra h
    refine nonc ⟨false, fun p => ?_⟩
    change (run C.gates (PEqualNP.Represents.oneEach p.1 p.2)).getD C.output false = false
    exact List.getD_eq_default _ _ (by rw [run_length, hlen1]; omega)
  obtain ⟨i, hi, a, b, c, ha, hb, hc, hab, hac, hbc, ka, kb, kc⟩ := core n hn3 C.gates.length A B An V C.output hA hB hAB
    (fun Q w hw => by
      simp only [V]
      rw [run_input _ _ _ (by rw [onl_len]; exact hw), onl_get n Q w hw])
    (fun Q j hj => hv1 j hj Q) hout
    (fun u v hu hv => by
      have := hf ⟨u, hu⟩ ⟨v, hv⟩
      rw [one_onl] at this
      change (run C.gates (onl n (pt n u v))).getD C.output false = _ at this
      simp only [V]
      rw [this]
      simp [Fin.ext_iff])
    (fun j hj w hw hall => irr0 j hj (Or.inr ⟨w, hw, fun p => by rw [← hV, ← hV]; exact hall _ _ p.1.isLt p.2.isLt⟩))
  let ii : Fin (k + 1) := ⟨i, hi⟩
  have hsa : ∀ u : Fin k, ((ii.succAbove u : Fin (k + 1)) : ℕ) ≠ i := fun u h => Fin.succAbove_ne ii u (Fin.ext h)
  have hlen2 : ∀ u v : Fin k, (PEqualNP.Represents.oneEach u v).length = k + k := by intro u v; simp [PEqualNP.Represents.oneEach]
  have kf : ∀ j, Kill n V i j → (∃ b, ∀ p : Fin k × Fin k, (run C.gates (PEqualNP.Represents.oneEach (ii.succAbove p.1) (ii.succAbove p.2))).getD (n + n + j) false = b) ∨
      ∃ w < n + n + j, ∀ p : Fin k × Fin k, (run C.gates (PEqualNP.Represents.oneEach (ii.succAbove p.1) (ii.succAbove p.2))).getD (n + n + j) false = (run C.gates (PEqualNP.Represents.oneEach (ii.succAbove p.1) (ii.succAbove p.2))).getD w false := by
    rintro j (⟨b, h⟩ | ⟨w, hw, h⟩)
    · exact Or.inl ⟨b, fun p => by rw [← hV]; exact h _ _ (Fin.isLt _) (Fin.isLt _) (hsa _) (hsa _)⟩
    · exact Or.inr ⟨w, hw, fun p => by rw [← hV, ← hV]; exact h _ _ (Fin.isLt _) (Fin.isLt _) (hsa _) (hsa _)⟩
  obtain ⟨D, d1, d2, d3⟩ := engine3 (n + n) (k + k) C (fun p : Fin k × Fin k => PEqualNP.Represents.oneEach (ii.succAbove p.1) (ii.succAbove p.2)) (fun p => PEqualNP.Represents.oneEach p.1 p.2)
    (fun p => hlen1 _ _) (fun p => hlen2 _ _) {a, b, c} hC (by
      intro w hw
      by_cases h : w < n
      · by_cases hwi : w = i
        · left
          refine ⟨false, fun p => ?_⟩
          rw [one_onl, onl_get n _ w hw, pt, decide_eq_false_iff_not]
          have := hsa p.1
          omega
        · right
          obtain ⟨u', hu'⟩ := Fin.exists_succAbove_eq (x := (⟨w, h⟩ : Fin (k + 1))) (y := ii) (fun e => hwi (congrArg Fin.val e))
          refine ⟨u', by have := u'.isLt; omega, fun p => ?_⟩
          rw [one_onl, one_onl, onl_get n _ w hw, onl_get k _ _ (by have := u'.isLt; omega)]
          simp only [pt]
          rw [decide_eq_decide]
          have e1 : w = ((ii.succAbove p.1 : Fin (k + 1)) : ℕ) ↔ (u' : ℕ) = p.1 := by
            rw [← show ((ii.succAbove u' : Fin (k + 1)) : ℕ) = w from congrArg Fin.val hu', ← Fin.ext_iff, ← Fin.ext_iff, (Fin.succAbove_right_injective).eq_iff]
          have := u'.isLt
          constructor
          · rintro (e | e)
            · exact Or.inl (e1.1 e)
            · omega
          · rintro (e | e)
            · exact Or.inl (e1.2 e)
            · omega
      · by_cases hwi : w = n + i
        · left
          refine ⟨false, fun p => ?_⟩
          rw [one_onl, onl_get n _ w hw, pt, decide_eq_false_iff_not]
          have := hsa p.2
          have := (ii.succAbove p.1).isLt
          omega
        · right
          obtain ⟨u', hu'⟩ := Fin.exists_succAbove_eq (x := (⟨w - n, by omega⟩ : Fin (k + 1))) (y := ii) (fun e => hwi (by have := congrArg Fin.val e; simp only [ii] at this; omega))
          refine ⟨k + u', by have := u'.isLt; omega, fun p => ?_⟩
          rw [one_onl, one_onl, onl_get n _ w hw, onl_get k _ _ (by have := u'.isLt; omega)]
          simp only [pt]
          rw [decide_eq_decide]
          have e0 : ((ii.succAbove u' : Fin (k + 1)) : ℕ) = w - n := congrArg Fin.val hu'
          have e1 : w - n = ((ii.succAbove p.2 : Fin (k + 1)) : ℕ) ↔ (u' : ℕ) = p.2 := by
            rw [← e0, ← Fin.ext_iff, ← Fin.ext_iff, (Fin.succAbove_right_injective).eq_iff]
          have h1 := u'.isLt
          have h2 := p.1.isLt
          have h3 := (ii.succAbove p.1).isLt
          constructor
          · rintro (e | e)
            · omega
            · have := e1.1 (by omega); omega
          · rintro (e | e)
            · omega
            · have := e1.2 (by omega); omega)
    (by
      rintro ⟨b, hb⟩
      have h1 := hb (⟨0, by omega⟩, ⟨0, by omega⟩)
      have h2 := hb (⟨0, by omega⟩, ⟨1, by omega⟩)
      simp only [hf] at h1 h2
      rw [← h1] at h2
      simp [(Fin.succAbove_right_injective).eq_iff] at h2)
    (by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl | rfl
      · exact ⟨ha, kf _ ka⟩
      · exact ⟨hb, kf _ kb⟩
      · exact ⟨hc, kf _ kc⟩)
  have hcard : ({a, b, c} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  rw [hcard] at d2
  refine ⟨D, d1, by omega, fun u v => ?_⟩
  rw [d3 (u, v), hf]
  simp only [ne_eq, (Fin.succAbove_right_injective).eq_iff]

end P18153

open P18153 in
theorem P18153 : (∀ n s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin (n + 1) => decide (u ≠ v)) (s + 3) → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s) := by
  rintro n s ⟨C, hC, hs, hf⟩
  rcases Nat.lt_or_ge n 2 with hn | hn
  · refine ⟨⟨[], n + n⟩, ?_, ?_, ?_⟩
    · intro g hg
      simp at hg
    · show 0 ≤ s
      omega
    · intro u v
      have huv : u = v := by
        apply Fin.ext
        have := u.isLt
        have := v.isLt
        omega
      subst huv
      simp only [ne_eq, not_true_eq_false, decide_false]
      show (List.foldl _ (PEqualNP.Represents.oneEach u u) []).getD (n + n) false = false
      simp only [List.foldl_nil]
      exact List.getD_eq_default _ _ (by simp [PEqualNP.Represents.oneEach])
  · obtain ⟨D, d1, d2, d3⟩ := step3 n hn C hC hf
    exact ⟨D, d1, by omega, d3⟩


theorem down (n : ℕ) : ∀ k s : ℕ,
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin (n + k) => decide (u ≠ v)) (s + 3 * k) →
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s
  | 0, s, h => h
  | k + 1, s, h => by
      apply down n k s
      apply P18153 (n + k) (s + 3 * k)
      have e : s + 3 * k + 3 = s + 3 * (k + 1) := by omega
      rw [e]
      exact h

theorem main (n : ℕ) (hn : 4 ≤ n) :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ v))
      (3 * n + 4 * (Nat.sqrt (n - 1) + 1) - 9) := by
  have h1 : n - 1 < (Nat.sqrt (n - 1) + 1) * (Nat.sqrt (n - 1) + 1) := Nat.lt_succ_sqrt (n - 1)
  have h2 : 0 < Nat.sqrt (n - 1) := Nat.sqrt_pos.mpr (by omega)
  have hm : 2 ≤ Nat.sqrt (n - 1) + 1 := by omega
  generalize Nat.sqrt (n - 1) + 1 = m at h1 hm ⊢
  obtain ⟨k, hk⟩ : ∃ k, m * m = n + k := ⟨m * m - n, by omega⟩
  have h := P18183 m m hm hm
  rw [hk] at h
  apply down n k
  have e : 3 * n + 4 * m - 9 + 3 * k = 3 * m * m + 2 * (m + m) - 9 := by
    rw [Nat.mul_assoc, hk]; omega
  rw [e]
  exact h

end PEqualNP.Outside.L_meta_19062_aux

theorem PEqualNP.Outside.L_meta_19062 : ∀ n : ℕ, 4 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) (3 * n + 4 * (Nat.sqrt (n - 1) + 1) - 9) :=
  fun n hn => PEqualNP.Outside.L_meta_19062_aux.main n hn
