import PEqualNP.Library.Helpers.PromiseCol

/-!
# Promise column replay with the wires in a balanced tree (seat-gct-2)

`PromiseCol.pcols` keeps the wire columns in a list: each gate appends and reads by index, so its cost grows like
the square of the number of gates (255 gates in 5.4 s, 2047 gates past five minutes, locally). Here the columns live
in a complete binary tree of depth `D` (`2 ^ D` leaves, one a wire), read and written along one path, so a gate costs
`D` steps and a big-number operation. `tcols_eq_pcols` says the tree gives the same column as the list for every wire,
when the circuit has at most `2 ^ D` wires; `represents_of_tcols` is the soundness in the tree form.
-/

namespace PEqualNP.Library.Helpers.PromiseColTree

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Library.Helpers.Replay
  PEqualNP.Library.Helpers.ReplayCol PEqualNP.Library.Helpers.PromiseCol PEqualNP.Represents

/-- A binary tree of numbers. -/
inductive BT where
  | leaf (v : ℕ)
  | node (l r : BT)

/-- Read index `i` in a tree of depth `d` (lowest bit chooses the side). -/
def BT.get : ℕ → BT → ℕ → ℕ
  | _, BT.leaf v, _ => v
  | 0, BT.node _ _, _ => 0
  | d + 1, BT.node l r, i => if i % 2 = 0 then BT.get d l (i / 2) else BT.get d r (i / 2)

/-- Write `v` at index `i` in a tree of depth `d`. -/
def BT.set : ℕ → BT → ℕ → ℕ → BT
  | _, BT.leaf _, _, v => BT.leaf v
  | 0, BT.node l r, _, _ => BT.node l r
  | d + 1, BT.node l r, i, v => if i % 2 = 0 then BT.node (BT.set d l (i / 2) v) r else BT.node l (BT.set d r (i / 2) v)

/-- The tree of depth `d` with every leaf `0`. -/
def BT.zeros : ℕ → BT
  | 0 => BT.leaf 0
  | d + 1 => BT.node (BT.zeros d) (BT.zeros d)

/-- Full shape of depth `d`: leaves exactly at depth `d`. -/
def BT.WF : ℕ → BT → Prop
  | 0, BT.leaf _ => True
  | 0, BT.node _ _ => False
  | _ + 1, BT.leaf _ => False
  | d + 1, BT.node l r => BT.WF d l ∧ BT.WF d r

/-- A guarded read: `0` at or past `2 ^ d`. -/
def BT.rd (d : ℕ) (t : BT) (i : ℕ) : ℕ := if i < 2 ^ d then t.get d i else 0

theorem wf_zeros : ∀ d, BT.WF d (BT.zeros d)
  | 0 => trivial
  | d + 1 => ⟨wf_zeros d, wf_zeros d⟩

theorem get_zeros : ∀ d i, (BT.zeros d).get d i = 0
  | 0, _ => rfl
  | d + 1, i => by simp only [BT.zeros, BT.get]; split <;> exact get_zeros d _

theorem wf_set : ∀ d t i v, BT.WF d t → BT.WF d (BT.set d t i v)
  | 0, BT.leaf _, _, _, _ => trivial
  | 0, BT.node _ _, _, _, h => h.elim
  | _ + 1, BT.leaf _, _, _, h => h.elim
  | d + 1, BT.node l r, i, v, h => by
    simp only [BT.set]; split
    · exact ⟨wf_set d l _ v h.1, h.2⟩
    · exact ⟨h.1, wf_set d r _ v h.2⟩

theorem get_set : ∀ d t i j v, BT.WF d t → i < 2 ^ d → j < 2 ^ d →
    (BT.set d t i v).get d j = if i = j then v else t.get d j
  | 0, BT.leaf _, i, j, v, _, hi, hj => by
    have : i = 0 := by simpa using hi
    have : j = 0 := by simpa using hj
    subst_vars; simp [BT.set, BT.get]
  | 0, BT.node _ _, _, _, _, h, _, _ => h.elim
  | _ + 1, BT.leaf _, _, _, _, h, _, _ => h.elim
  | d + 1, BT.node l r, i, j, v, h, hi, hj => by
    have hi2 : i / 2 < 2 ^ d := by rw [pow_succ] at hi; omega
    have hj2 : j / 2 < 2 ^ d := by rw [pow_succ] at hj; omega
    by_cases hpi : i % 2 = 0 <;> by_cases hpj : j % 2 = 0
    · simp only [BT.set, hpi, if_true, BT.get, hpj, get_set d l _ _ v h.1 hi2 hj2]
      by_cases e : i = j
      · simp [e]
      · have : i / 2 ≠ j / 2 := by omega
        simp [e, this]
    · simp only [BT.set, hpi, if_true, BT.get, hpj, if_false]
      have : i ≠ j := by omega
      simp [this]
    · simp only [BT.set, hpi, if_false, BT.get, hpj, if_true]
      have : i ≠ j := by omega
      simp [this]
    · simp only [BT.set, hpi, if_false, BT.get, hpj, get_set d r _ _ v h.2 hi2 hj2]
      by_cases e : i = j
      · simp [e]
      · have : i / 2 ≠ j / 2 := by omega
        simp [e, this]

/-- The state of the fold: the tree and the number of wires written. -/
def push (D : ℕ) (st : BT × ℕ) (c : ℕ) : BT × ℕ := (st.1.set D st.2 c, st.2 + 1)

/-- The column of a gate, reading the tree (the tree twin of `ReplayCol.gateCol`). -/
def gateColT (N D : ℕ) (g : Gate) (t : BT) : ℕ :=
  match g.op with
  | GateOp.and => (g.inputs.map fun a => t.rd D a).foldr (· &&& ·) (mask N)
  | GateOp.or => (g.inputs.map fun a => t.rd D a).foldr (· ||| ·) 0
  | GateOp.not => mask N ^^^ (g.inputs.map fun a => t.rd D a).headD 0
  | _ => 0

/-- All wire columns of `C` on the promise rows, in a tree of depth `D`. -/
def tcols (N D : ℕ) (C : Circuit) (n m : ℕ) : BT × ℕ :=
  C.gates.foldl (fun st g => push D st (gateColT N D g st.1)) ((inCols n m).foldl (push D) (BT.zeros D, 0))

/-- The invariant: the tree reads what the list holds, the counter is the list's length, the tree is well formed. -/
def Inv (D : ℕ) (st : BT × ℕ) (cs : List ℕ) : Prop :=
  BT.WF D st.1 ∧ st.2 = cs.length ∧ ∀ j, st.1.rd D j = cs.getD j 0

theorem inv_push {D : ℕ} {st : BT × ℕ} {cs : List ℕ} (h : Inv D st cs) (c : ℕ) (hl : cs.length < 2 ^ D) :
    Inv D (push D st c) (cs ++ [c]) := by
  obtain ⟨hw, hn, hr⟩ := h
  refine ⟨wf_set D _ _ _ hw, by simp [push, hn], fun j => ?_⟩
  simp only [push, BT.rd]
  by_cases hj : j < 2 ^ D
  · rw [if_pos hj, get_set D _ _ _ _ hw (hn ▸ hl) hj]
    rcases lt_trichotomy j cs.length with h1 | h1 | h1
    · have : st.2 ≠ j := by omega
      rw [if_neg this, List.getD_append _ _ _ _ h1]
      have := hr j; simp only [BT.rd, if_pos hj] at this; exact this
    · subst h1; rw [if_pos hn]; simp
    · have : st.2 ≠ j := by omega
      rw [if_neg this, List.getD_eq_default _ _ (by simp; omega)]
      have := hr j; simp only [BT.rd, if_pos hj] at this
      rw [this, List.getD_eq_default _ _ (by omega)]
  · rw [if_neg hj, List.getD_eq_default _ _ (by simp; omega)]

theorem inv_inputs {D : ℕ} : ∀ (l : List ℕ) (st : BT × ℕ) (cs : List ℕ), Inv D st cs → cs.length + l.length ≤ 2 ^ D →
    Inv D (l.foldl (push D) st) (cs ++ l) := by
  intro l
  induction l with
  | nil => intro st cs h _; simpa using h
  | cons c l ih =>
    intro st cs h hl
    have := ih (push D st c) (cs ++ [c]) (inv_push h c (by simp at hl; omega)) (by simp at hl ⊢; omega)
    simpa using this

theorem gateColT_eq {N D : ℕ} {st : BT × ℕ} {cs : List ℕ} (h : Inv D st cs) (g : Gate) :
    gateColT N D g st.1 = gateCol N g cs := by
  have e : (g.inputs.map fun a => st.1.rd D a) = (g.inputs.map fun a => cs.getD a 0) :=
    List.map_congr_left (fun a _ => h.2.2 a)
  unfold gateColT gateCol; rw [e]; cases g.op <;> rfl

theorem inv_gates {N D : ℕ} : ∀ (gs : List Gate) (st : BT × ℕ) (cs : List ℕ), Inv D st cs →
    cs.length + gs.length ≤ 2 ^ D →
    Inv D (gs.foldl (fun st g => push D st (gateColT N D g st.1)) st)
      (gs.foldl (fun cs g => cs ++ [gateCol N g cs]) cs) := by
  intro gs
  induction gs with
  | nil => intro st cs h _; exact h
  | cons g gs ih =>
    intro st cs h hl
    simp only [List.foldl_cons]
    rw [gateColT_eq h g]
    exact ih _ _ (inv_push h _ (by simp at hl; omega)) (by simp at hl ⊢; omega)

/-- The tree gives the list's column for every wire, when the circuit has at most `2 ^ D` wires. -/
theorem tcols_eq_pcols {N D n m : ℕ} (C : Circuit) (hsz : n + m + C.gates.length ≤ 2 ^ D) (o : ℕ) :
    (tcols N D C n m).1.rd D o = (pcols N C n m).getD o 0 := by
  have h0 : Inv D (BT.zeros D, 0) [] := ⟨wf_zeros D, rfl, fun j => by simp [BT.rd, get_zeros]⟩
  have hin := inv_inputs (inCols n m) _ [] h0 (by simp [inCols]; omega)
  simp only [List.nil_append] at hin
  have := inv_gates (N := N) C.gates _ _ hin (by simp [inCols]; omega)
  exact this.2.2 o

/-- Soundness in the tree form. -/
theorem represents_of_tcols {n m N D : ℕ} (hN : n * m ≤ 2 ^ N) (C : Circuit) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ m) (hg : aonB C = true) (hsz : n + m + C.gates.length ≤ 2 ^ D)
    (h : ((tcols N D C n m).1.rd D C.output == tcol m rows) = true) :
    Represents (fun (u : Fin n) (v : Fin m) => (rows.getD u.val 0).testBit v.val) C := by
  rw [tcols_eq_pcols C hsz] at h
  exact represents_of_pcols hN C rows hrows hg h

end PEqualNP.Library.Helpers.PromiseColTree
