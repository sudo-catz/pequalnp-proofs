import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19118_aux

open PEqualNP.CircuitLowerBounds

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

def Const {Y : Type} (f : Y → Bool) : Prop := ∃ c, ∀ y, f y = c

def Drop {Y : Type} (n : ℕ) (F : ℕ → Y → Bool) (j : ℕ) : Prop :=
  Const (F (n + j)) ∨ ∃ w < n + j, ∀ y, F (n + j) y = F w y

theorem restrict (n m : ℕ) (gs : List Gate) (F : ℕ → (Fin m → Bool) → Bool)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hin : ∀ i < n, Const (F i) ∨ ∃ k < m, ∀ y, F i y = (List.ofFn y).getD k false)
    (hF : ∀ (j : ℕ) (hj : j < gs.length) (y : Fin m → Bool), F (n + j) y =
      gs[j].op.eval (gs[j].inputs.map fun i => if i < n + j then F i y else false)) :
    ∀ K ≤ gs.length, ∃ (ds : List Gate) (S : Finset ℕ),
      (∀ g ∈ ds, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧
      (∀ (j : ℕ) (hj : j < ds.length), ∀ i ∈ ds[j].inputs, i < m + j) ∧
      (∀ j ∈ S, j < K ∧ ¬ Drop n F j) ∧ ds.length ≤ S.card ∧
      ∀ w < n + K, Const (F w) ∨
        ∃ k < m + ds.length, ∀ y, F w y = (run ds (List.ofFn y)).getD k false := by
  intro K
  induction K with
  | zero =>
    intro _
    refine ⟨[], ∅, by simp, by simp, by simp, by simp, fun w hw => ?_⟩
    simpa [run] using hin w (by omega)
  | succ K ih =>
    intro hK
    obtain ⟨ds, S, h1, hb, h2, h3, h4⟩ := ih (by omega)
    have h2' : ∀ j ∈ S, j < K + 1 ∧ ¬ Drop n F j := fun j hj =>
      ⟨by have := (h2 j hj).1; omega, (h2 j hj).2⟩
    by_cases hd : Drop n F K
    · refine ⟨ds, S, h1, hb, h2', h3, fun w hw => ?_⟩
      rcases Nat.lt_or_ge w (n + K) with h | h
      · exact h4 w h
      · rw [show w = n + K by omega]
        rcases hd with hc | ⟨u, hu, he⟩
        · exact Or.inl hc
        · rcases h4 u hu with ⟨c, hc⟩ | ⟨k, hk, hk'⟩
          · exact Or.inl ⟨c, fun y => (he y).trans (hc y)⟩
          · exact Or.inr ⟨k, hk, fun y => (he y).trans (hk' y)⟩
    · have hnc : ¬ Const (F (n + K)) := fun h => hd (Or.inl h)
      have hne : ∀ u < n + K, ¬ ∀ y, F (n + K) y = F u y := fun u hu h => hd (Or.inr ⟨u, hu, h⟩)
      have addg : ∀ g : Gate, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
          g.inputs.length ≤ 2 → (∀ i ∈ g.inputs, i < m + ds.length) →
          (∀ y, F (n + K) y = g.op.eval (g.inputs.map fun i =>
            (run ds (List.ofFn y)).getD i false)) →
          ∃ (ds : List Gate) (S : Finset ℕ),
            (∀ g ∈ ds, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
              g.inputs.length ≤ 2) ∧
            (∀ (j : ℕ) (hj : j < ds.length), ∀ i ∈ ds[j].inputs, i < m + j) ∧
            (∀ j ∈ S, j < K + 1 ∧ ¬ Drop n F j) ∧ ds.length ≤ S.card ∧
            ∀ w < n + (K + 1), Const (F w) ∨
              ∃ k < m + ds.length, ∀ y, F w y = (run ds (List.ofFn y)).getD k false := by
        intro g ho hl hgb hg
        have hKS : K ∉ S := fun h => by have := (h2 K h).1; omega
        refine ⟨ds ++ [g], insert K S, ?_, ?_, ?_, ?_, ?_⟩
        · intro g' hg'
          rcases List.mem_append.1 hg' with h | h
          · exact h1 g' h
          · rw [List.mem_singleton.1 h]; exact ⟨ho, hl⟩
        · intro j hj i hi
          rcases Nat.lt_or_ge j ds.length with h | h
          · rw [List.getElem_append_left h] at hi
            exact hb j h i hi
          · have hjj : j = ds.length := by simp at hj; omega
            subst hjj
            exact hgb i (by simpa using hi)
        · intro j hj
          rcases Finset.mem_insert.1 hj with rfl | h
          · exact ⟨by omega, hd⟩
          · exact h2' j h
        · rw [Finset.card_insert_of_notMem hKS]; simp; omega
        · intro w hw
          rcases Nat.lt_or_ge w (n + K) with h | h
          · rcases h4 w h with hc | ⟨k, hk, hk'⟩
            · exact Or.inl hc
            · refine Or.inr ⟨k, by simp; omega, fun y => ?_⟩
              rw [run_snoc, getD_lt _ _ _ (by rw [run_length, List.length_ofFn]; exact hk)]
              exact hk' y
          · refine Or.inr ⟨m + ds.length, by simp, fun y => ?_⟩
            have hl' : (run ds (List.ofFn y)).length = m + ds.length := by
              rw [run_length, List.length_ofFn]
            rw [show w = n + K by omega, run_snoc, ← hl', getD_at]
            exact hg y
      have hval : ∀ i, (∃ c, ∀ y, (if i < n + K then F i y else false) = c) ∨
          (i < n + K ∧ ∃ k < m + ds.length, ∀ y,
            F i y = (run ds (List.ofFn y)).getD k false) := by
        intro i
        by_cases hi : i < n + K
        · rcases h4 i hi with ⟨c, hc⟩ | h
          · exact Or.inl ⟨c, fun y => by rw [if_pos hi]; exact hc y⟩
          · exact Or.inr ⟨hi, h⟩
        · exact Or.inl ⟨false, fun y => by rw [if_neg hi]⟩
      have hj : K < gs.length := by omega
      have hFK := hF K hj
      obtain ⟨hop, hlen⟩ := hops _ (List.getElem_mem hj)
      generalize gs[K].inputs = I at *
      generalize gs[K].op = o at *
      match I, hlen with
      | [], _ =>
        refine absurd ⟨o.eval [], fun y => ?_⟩ hnc
        simpa using hFK y
      | [a], _ =>
        rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
        · refine absurd ⟨o.eval [c], fun y => ?_⟩ hnc
          rw [hFK y, List.map_singleton, hc y]
        · rcases hop with rfl | rfl | rfl
          · refine absurd (fun y => ?_) (hne a ha)
            rw [hFK y]; simp [GateOp.eval, ha]
          · refine absurd (fun y => ?_) (hne a ha)
            rw [hFK y]; simp [GateOp.eval, ha]
          · refine addg ⟨GateOp.not, [k]⟩ (by simp) (by simp) (by simpa using hk) fun y => ?_
            rw [hFK y]; simp [GateOp.eval, ha, hk' y]
      | [a, b], _ =>
        rcases hop with rfl | rfl | rfl
        · rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
          · have he : ∀ y, F (n + K) y = (c && if b < n + K then F b y else false) := by
              intro y
              rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval]
            cases c
            · exact absurd ⟨false, fun y => by rw [he y]; rfl⟩ hnc
            · by_cases hb' : b < n + K
              · exact absurd (fun y => by rw [he y, if_pos hb']; rfl) (hne b hb')
              · exact absurd ⟨false, fun y => by rw [he y, if_neg hb']; rfl⟩ hnc
          · rcases hval b with ⟨c, hc⟩ | ⟨hb', l, hl, hl'⟩
            · have he : ∀ y, F (n + K) y = (F a y && c) := by
                intro y
                rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval, ha]
              cases c
              · exact absurd ⟨false, fun y => by rw [he y]; simp⟩ hnc
              · exact absurd (fun y => by rw [he y]; simp) (hne a ha)
            · refine addg ⟨GateOp.and, [k, l]⟩ (by simp) (by simp) (by simpa using ⟨hk, hl⟩) fun y => ?_
              rw [hFK y]; simp [GateOp.eval, ha, hb', hk' y, hl' y]
        · rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
          · have he : ∀ y, F (n + K) y = (c || if b < n + K then F b y else false) := by
              intro y
              rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval]
            cases c
            · by_cases hb' : b < n + K
              · exact absurd (fun y => by rw [he y, if_pos hb']; rfl) (hne b hb')
              · exact absurd ⟨false, fun y => by rw [he y, if_neg hb']; rfl⟩ hnc
            · exact absurd ⟨true, fun y => by rw [he y]; rfl⟩ hnc
          · rcases hval b with ⟨c, hc⟩ | ⟨hb', l, hl, hl'⟩
            · have he : ∀ y, F (n + K) y = (F a y || c) := by
                intro y
                rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval, ha]
              cases c
              · exact absurd (fun y => by rw [he y]; simp) (hne a ha)
              · exact absurd ⟨true, fun y => by rw [he y]; simp⟩ hnc
            · refine addg ⟨GateOp.or, [k, l]⟩ (by simp) (by simp) (by simpa using ⟨hk, hl⟩) fun y => ?_
              rw [hFK y]; simp [GateOp.eval, ha, hb', hk' y, hl' y]
        · rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
          · refine absurd ⟨!c, fun y => ?_⟩ hnc
            rw [hFK y, List.map_cons, hc y]; simp [GateOp.eval]
          · refine addg ⟨GateOp.not, [k]⟩ (by simp) (by simp) (by simpa using hk) fun y => ?_
            rw [hFK y]; simp [GateOp.eval, ha, hk' y]

theorem circuit (n m : ℕ) (C : Circuit) (X : (Fin m → Bool) → List Bool)
    (hops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hX : ∀ y, (X y).length = n)
    (hin : ∀ i < n, (∃ c, ∀ y, (X y).getD i false = c) ∨
      ∃ k < m, ∀ y, (X y).getD i false = (List.ofFn y).getD k false)
    (hrec : ∀ (j : ℕ) (hj : j < C.gates.length) (y : Fin m → Bool),
      (C.wires (X y)).getD (n + j) false = C.gates[j].op.eval
        (C.gates[j].inputs.map fun i => if i < n + j then (C.wires (X y)).getD i false else false))
    (hinw : ∀ i < n, ∀ y, (C.wires (X y)).getD i false = (X y).getD i false)
    (hout : C.output < n + C.gates.length)
    (hnc : ¬ ∃ c, ∀ y, C.eval (X y) = c) :
    ∃ (D : Circuit) (S : Finset ℕ),
      (∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧
      (∀ (j : ℕ) (hj : j < D.gates.length), ∀ i ∈ D.gates[j].inputs, i < m + j) ∧
      D.output < m + D.gates.length ∧ D.gates.length ≤ S.card ∧
      (∀ j ∈ S, j < C.gates.length ∧
        ¬ Drop n (fun w (y : Fin m → Bool) => (C.wires (X y)).getD w false) j) ∧
      ∀ y, D.eval (List.ofFn y) = C.eval (X y) := by
  obtain ⟨ds, S, h1, hb, h2, h3, h4⟩ := restrict n m C.gates
    (fun w y => (C.wires (X y)).getD w false) hops (fun i hi => by
      rcases hin i hi with ⟨c, hc⟩ | ⟨k, hk, h⟩
      · exact Or.inl ⟨c, fun y => (hinw i hi y).trans (hc y)⟩
      · exact Or.inr ⟨k, hk, fun y => (hinw i hi y).trans (h y)⟩) hrec C.gates.length le_rfl
  rcases h4 C.output hout with hc | ⟨k, hk, hk'⟩
  · exact absurd hc hnc
  · exact ⟨⟨ds, k⟩, S, h1, hb, hk, h3, h2, fun y => (hk' y).symm⟩

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


def rds (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

theorem eval_congr (g : Gate) (u v : ℕ → Bool)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (huv : ∀ i ∈ rds g, u i = v i) : g.op.eval (g.inputs.map u) = g.op.eval (g.inputs.map v) := by
  rcases hop with h | h | h
  · simp only [rds, h] at huv
    rw [List.map_congr_left huv]
  · simp only [rds, h] at huv
    rw [List.map_congr_left huv]
  · simp only [rds, h] at huv
    rw [h]
    cases hi : g.inputs with
    | nil => rfl
    | cons a t =>
      have := huv a (by simp [hi])
      simp [GateOp.eval, this]

theorem getD_sn (l : List Bool) (b : Bool) (t : ℕ) :
    (l ++ [b]).getD t false = if t = l.length then b else l.getD t false := by
  rcases lt_trichotomy t l.length with h | h | h
  · rw [if_neg (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem indep (v : ℕ) (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hno : ∀ g ∈ gs, v ∉ rds g) (x y : List Bool) (hl : x.length = y.length)
    (hxy : ∀ i, i ≠ v → x.getD i false = y.getD i false) :
    ∀ i, i ≠ v → (run gs x).getD i false = (run gs y).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simpa [run] using hxy
  | append_singleton gs g ih =>
    have ih' := ih (fun g' h => hop g' (by simp [h])) (fun g' h => hno g' (by simp [h]))
    intro i hi
    have e : g.op.eval (g.inputs.map fun i => (run gs x).getD i false) =
        g.op.eval (g.inputs.map fun i => (run gs y).getD i false) :=
      eval_congr g _ _ (hop g (by simp)) fun k hk =>
        ih' k fun hc => hno g (by simp) (hc ▸ hk)
    rw [run_snoc, run_snoc, getD_sn, getD_sn, run_length, run_length, hl, e]
    split_ifs
    · rfl
    · exact ih' i hi

theorem one_drop (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C) (i : Fin n)
    (b : Bool)
    (hess : ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧
      C.eval (List.ofFn x) ≠ C.eval (List.ofFn y))
    (hnc : ¬ ∃ c, ∀ y : Fin n → Bool, C.eval (List.ofFn (Function.update y i b)) = c) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + 1 ≤ C.size ∧
      ∀ y : Fin n → Bool, D.eval (List.ofFn y) = C.eval (List.ofFn (Function.update y i b)) := by
  have hops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hC g hg
    exact ⟨by simpa using h1, h2⟩
  have hw : ∀ x, C.wires x = run C.gates x := fun _ => rfl
  have hev : ∀ x, C.eval x = (run C.gates x).getD C.output false := fun _ => rfl
  have hout : C.output < n + C.gates.length := by
    by_contra hcon
    obtain ⟨x, y, -, hxy⟩ := hess
    apply hxy
    rw [hev, hev, List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega),
      List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega)]
  let X : (Fin n → Bool) → List Bool := fun y => List.ofFn (Function.update y i b)
  have hXl : ∀ y, (X y).length = n := fun y => by simp [X]
  have hXi : ∀ y, (X y).getD i false = b := by
    intro y
    simp only [X]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    simp
  have hXk : ∀ (k : ℕ), k < n → k ≠ i → ∀ y, (X y).getD k false = (List.ofFn y).getD k false := by
    intro k hk hki y
    simp only [X]
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getD_eq_getElem _ _ (by simpa using hk),
      List.getElem_ofFn, List.getElem_ofFn]
    exact Function.update_of_ne (fun hc => hki (congrArg Fin.val hc)) _ _
  have hinw : ∀ k < n, ∀ y, (C.wires (X y)).getD k false = (X y).getD k false := by
    intro k hk y
    rw [hw]
    exact run_input _ _ _ (by rw [hXl]; exact hk)
  have hrec : ∀ (j : ℕ) (hj : j < C.gates.length) (y : Fin n → Bool),
      (C.wires (X y)).getD (n + j) false = C.gates[j].op.eval
        (C.gates[j].inputs.map fun k =>
          if k < n + j then (C.wires (X y)).getD k false else false) := by
    intro j hj y
    have h := run_gate C.gates (X y) j hj
    rw [hXl] at h
    exact h
  have hoi : C.output ≠ i := by
    intro h
    apply hnc
    refine ⟨b, fun y => ?_⟩
    rw [hev, h, run_input _ _ _ (by simp)]
    exact hXi y
  have hread : ∃ g ∈ C.gates, (i : ℕ) ∈ rds g := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, y, hxy, hne⟩ := hess
    apply hne
    rw [hev, hev]
    refine indep i C.gates (fun g hg => (hops g hg).1) hcon _ _ (by simp) (fun k hk => ?_) _ hoi
    by_cases h : k < n
    · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h),
        List.getElem_ofFn, List.getElem_ofFn]
      exact hxy _ fun hc => hk (congrArg Fin.val hc)
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  obtain ⟨g, hg, hgi⟩ := hread
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
  obtain ⟨D, S, d1, -, -, d4, d5, d6⟩ := circuit n n C X hops hXl (fun k hk => by
      by_cases h : k = i
      · exact Or.inl ⟨b, fun y => by rw [h]; exact hXi y⟩
      · exact Or.inr ⟨k, hk, hXk k hk h⟩) hrec hinw hout hnc
  refine ⟨D, fun g hg => ?_, ?_, fun y => d6 y⟩
  · obtain ⟨h1, h2⟩ := d1 g hg
    exact ⟨by simpa using h1, h2⟩
  · have hdrop : Drop n (fun w (y : Fin n → Bool) => (C.wires (X y)).getD w false) j := by
      obtain ⟨hop, hlen⟩ := hops _ hg
      have hv := hrec j hj
      have hii : ∀ y, (if (i : ℕ) < n + j then (C.wires (X y)).getD (i : ℕ) false else false) = b := by
        intro y
        rw [if_pos (by have := i.2; omega), hinw i i.2, hXi]
      generalize hI : C.gates[j].inputs = I at *
      generalize hO : C.gates[j].op = o at *
      have two : ∀ c : ℕ, (∀ y, (C.wires (X y)).getD (n + j) false =
          (b && if c < n + j then (C.wires (X y)).getD c false else false)) ∨
          (∀ y, (C.wires (X y)).getD (n + j) false =
          (b || if c < n + j then (C.wires (X y)).getD c false else false)) →
          Drop n (fun w (y : Fin n → Bool) => (C.wires (X y)).getD w false) j := by
        intro c hc
        by_cases hcl : c < n + j
        · simp only [hcl, if_true] at hc
          rcases hc with hc | hc <;> cases b
          · exact Or.inl ⟨false, fun y => by simp only; rw [hc y]; rfl⟩
          · exact Or.inr ⟨c, hcl, fun y => by simp only; rw [hc y]; rfl⟩
          · exact Or.inr ⟨c, hcl, fun y => by simp only; rw [hc y]; rfl⟩
          · exact Or.inl ⟨true, fun y => by simp only; rw [hc y]; rfl⟩
        · simp only [hcl, if_false] at hc
          rcases hc with hc | hc
          · exact Or.inl ⟨b && false, fun y => hc y⟩
          · exact Or.inl ⟨b || false, fun y => hc y⟩
      match I, hlen with
      | [], _ =>
        exfalso
        simp only [rds, hO, hI] at hgi
        rcases hop with rfl | rfl | rfl <;> simp at hgi
      | [a], _ =>
        have hai : a = i := by
          simp only [rds, hO, hI] at hgi
          rcases hop with rfl | rfl | rfl
          · exact (List.mem_singleton.1 hgi).symm
          · exact (List.mem_singleton.1 hgi).symm
          · exact (List.mem_singleton.1 hgi).symm
        subst hai
        refine Or.inl ⟨o.eval [b], fun y => ?_⟩
        simp only
        rw [hv y, List.map_singleton, hii y]
      | [a, c], _ =>
        rcases hop with rfl | rfl | rfl
        · have hac : (i : ℕ) = a ∨ (i : ℕ) = c := by
            simp only [rds, hO, hI] at hgi
            simpa using hgi
          rcases hac with rfl | rfl
          · refine two c (Or.inl fun y => ?_)
            rw [hv y, List.map_cons, List.map_singleton, hii y]
            simp [GateOp.eval]
          · refine two a (Or.inl fun y => ?_)
            rw [hv y, List.map_cons, List.map_singleton, hii y]
            simp [GateOp.eval, Bool.and_comm]
        · have hac : (i : ℕ) = a ∨ (i : ℕ) = c := by
            simp only [rds, hO, hI] at hgi
            simpa using hgi
          rcases hac with rfl | rfl
          · refine two c (Or.inr fun y => ?_)
            rw [hv y, List.map_cons, List.map_singleton, hii y]
            simp [GateOp.eval]
          · refine two a (Or.inr fun y => ?_)
            rw [hv y, List.map_cons, List.map_singleton, hii y]
            simp [GateOp.eval, Bool.or_comm]
        · have hai : (i : ℕ) = a := by
            simp only [rds, hO, hI] at hgi
            simpa using hgi
          subst hai
          refine Or.inl ⟨!b, fun y => ?_⟩
          simp only
          rw [hv y, List.map_cons, hii y]
          rfl
    have hsub : S ⊆ (Finset.range C.gates.length).erase j := by
      intro k hk
      obtain ⟨h1, h2⟩ := d5 k hk
      refine Finset.mem_erase.2 ⟨?_, Finset.mem_range.2 h1⟩
      rintro rfl
      exact h2 hdrop
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_range.2 hj), Finset.card_range] at h1
    change D.gates.length + 1 ≤ C.gates.length
    omega

theorem add_or (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (h : PEqualNP.MetaComplexity.HasCircuitSize n f s) (i : Fin n) :
    PEqualNP.MetaComplexity.HasCircuitSize n (fun x => f x || x i) (s + 1) := by
  obtain ⟨C, h1, h2, h3⟩ := h
  refine ⟨⟨C.gates ++ [⟨GateOp.or, [C.output, i]⟩], n + C.gates.length⟩, ?_, ?_, fun x => ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · exact h1 g h
    · rw [List.mem_singleton.1 h]; simp
  · change (C.gates ++ [_]).length ≤ s + 1
    have : C.gates.length ≤ s := h2
    simpa using this
  · change (run (C.gates ++ [⟨GateOp.or, [C.output, i]⟩]) (List.ofFn x)).getD _ false = _
    rw [run_snoc, getD_sn, run_length, List.length_ofFn, if_pos rfl]
    simp only
    rw [← h3 x]
    have hi : (run C.gates (List.ofFn x)).getD (i : ℕ) false = x i := by
      rw [run_input _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    have ho : (run C.gates (List.ofFn x)).getD C.output false = C.eval (List.ofFn x) := rfl
    simp only [GateOp.eval, List.map_cons, List.map_nil]
    rw [hi, ho]
    simp

theorem dropOne : ∀ (x1 : ℕ) (x2 : Fin x1) (x3 : (Fin x1 → Bool) → Bool) (x4 : ℕ), (∀ (x5 : Fin x1 → Bool), x3 (Function.update x5 x2 Bool.false) = x3 x5) → (∃ (x6 : Fin x1 → Bool) (x7 : Fin x1 → Bool), x3 x6 ≠ x3 x7) → PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x7 : Fin x1 → Bool) => x7 x2 || x3 x7) x4 → ∃ (x8 : ℕ), x8 + (1 : ℕ) ≤ x4 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x8 := by
  intro n i f s hind hnc h
  obtain ⟨C, h1, h2, h3⟩ := h
  have hf : ∀ y : Fin n → Bool, C.eval (List.ofFn (Function.update y i false)) = f y := by
    intro y
    rw [h3]
    simp only [Function.update_self, Bool.false_or]
    exact hind y
  obtain ⟨x, y, hxy⟩ := hnc
  have hff : ∃ z : Fin n → Bool, f z = false := by
    cases hx : f x
    · exact ⟨x, hx⟩
    · cases hy : f y
      · exact ⟨y, hy⟩
      · exact absurd (hx.trans hy.symm) hxy
  obtain ⟨z, hz⟩ := hff
  obtain ⟨D, d1, d2, d3⟩ := PEqualNP.Outside.L_meta_19118_aux.one_drop n C h1 i false (by
    refine ⟨Function.update z i true, Function.update z i false, fun j hj => ?_, ?_⟩
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
    · rw [hf, hz, h3]
      simp) (by
    rintro ⟨c, hc⟩
    apply hxy
    rw [← hf x, ← hf y, hc, hc])
  exact ⟨D.size, by omega, D, d1, le_rfl, fun w => by rw [d3, hf]⟩

end PEqualNP.Outside.L_meta_19118_aux

theorem PEqualNP.Outside.L_meta_19118 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (u w : Fin n) (s : ℕ), u ≠ w → (∃ x : Fin n → Bool, f x = false) → (∃ x : Fin n → Bool, f x = true) → (∀ x : Fin n → Bool, ∀ b : Bool, f (Function.update x u b) = f x) → (∀ x : Fin n → Bool, ∀ b : Bool, f (Function.update x w b) = f x) → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => f x || x u || x w) s → ∃ t : ℕ, t + 2 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize n f t := by
  intro n f u w s huw hf0 hf1 hu hw hs
  obtain ⟨a, ha⟩ := hf0
  obtain ⟨b, hb⟩ := hf1
  let g : (Fin n → Bool) → Bool := fun x => f x || x u
  have hgw (x : Fin n → Bool) : g (Function.update x w false) = g x := by
    simp only [g, hw, Function.update_of_ne huw]
  have g0 : g (Function.update a u false) = false := by simp [g, hu, ha]
  have g1 : g b = true := by simp [g, hb]
  have hsg : PEqualNP.MetaComplexity.HasCircuitSize n (fun x => x w || g x) s := by
    have he : (fun x : Fin n → Bool => x w || g x) = (fun x => f x || x u || x w) := by
      funext x
      exact Bool.or_comm _ _
    rw [he]
    exact hs
  obtain ⟨t, ht, hc⟩ := PEqualNP.Outside.L_meta_19118_aux.dropOne n w g s hgw
    ⟨Function.update a u false, b, by simp [g0, g1]⟩ hsg
  have hsc : PEqualNP.MetaComplexity.HasCircuitSize n (fun x => x u || f x) t := by
    have he : (fun x : Fin n → Bool => x u || f x) = g := by
      funext x
      exact Bool.or_comm _ _
    rw [he]
    exact hc
  obtain ⟨t', ht', hc'⟩ := PEqualNP.Outside.L_meta_19118_aux.dropOne n u f t
    (fun x => hu x false) ⟨a, b, by simp [ha, hb]⟩ hsc
  exact ⟨t', by omega, hc'⟩
