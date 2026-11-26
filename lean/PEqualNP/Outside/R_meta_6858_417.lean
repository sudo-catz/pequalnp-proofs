import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_6858_417
    (lift49 : ∀ D : Circuit, Monotone2 D →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ D.size ∧
        ∀ w : List Bool, w.length = 56 →
          C.eval w = D.eval (List.ofFn (fun i : Fin 14 => w.getD (3 * (i.val / 2) + i.val % 2) false) ++ w.drop 21))
    (boundary49 :
      let adj (i : Fin 14) (l : Fin 21) : Bool :=
        let d := (l.val + 21 - (3 * (i.val / 2) + i.val % 2)) % 21
        d == 0 || d == 5 || d == 7 || d == 17 || d == 20
      let B49 (p : Fin 14 → Bool) (y : Fin 21 → Bool) :=
        let L (j : Fin 7) (d : ℕ) := y (Fin.ofNat 21 ((3 * j.val + d) % 21))
        ((List.ofFn p ++ List.ofFn y) ++ List.ofFn (fun j : Fin 7 => L j 5 || L j 17)) ++
          List.ofFn (fun j : Fin 7 => L j 5 || L j 17 || L j 20)
      let free (p : Fin 14 → Bool) (l : Fin 21) : Bool :=
        !(List.finRange 14).any (fun i => p i && adj i l)
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 68 ∧
        (∀ (i : Fin 14) (l : Fin 21), adj i l = true →
          D.eval (B49 (fun a => a == i) (fun b => b == l)) = true) ∧
        (∀ p : Fin 14 → Bool,
          (∀ i : Fin 14, (∀ l : Fin 21, free p l = true → adj i l = false) → p i = true) →
          D.eval (B49 p (free p)) = false)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (68 : ℕ) ∧       ∀ (x2 : Fin (42 : ℕ) → Bool),         have x3 : Fin (7 : ℕ) → ℕ → Bool := fun (x3 : Fin (7 : ℕ)) (x4 : ℕ) => x2 (Fin.ofNat (42 : ℕ) ((21 : ℕ) + ((3 : ℕ) * ↑x3 + x4) % (21 : ℕ)));         x1.eval ((List.ofFn x2 ++ List.ofFn fun (x4 : Fin (7 : ℕ)) => x3 x4 (5 : ℕ) || x3 x4 (17 : ℕ)) ++ List.ofFn fun (x4 : Fin (7 : ℕ)) => x3 x4 (5 : ℕ) || x3 x4 (17 : ℕ) || x3 x4 (20 : ℕ)) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4 < (21 : ℕ) ∧ ↑x4 % (3 : ℕ) ≠ (2 : ℕ) ∧ (21 : ℕ) ≤ ↑x5 ∧ (↑x5 + (21 : ℕ) - ↑x4) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x2 x4 = Bool.true ∧ x2 x5 = Bool.true := by
  let adj (i : Fin 14) (l : Fin 21) : Bool :=
    let d := (l.val + 21 - (3 * (i.val / 2) + i.val % 2)) % 21
    d == 0 || d == 5 || d == 7 || d == 17 || d == 20
  let B49 (p : Fin 14 → Bool) (y : Fin 21 → Bool) :=
    let L (j : Fin 7) (d : ℕ) := y (Fin.ofNat 21 ((3 * j.val + d) % 21))
    ((List.ofFn p ++ List.ofFn y) ++ List.ofFn (fun j : Fin 7 => L j 5 || L j 17)) ++
      List.ofFn (fun j : Fin 7 => L j 5 || L j 17 || L j 20)
  let free (p : Fin 14 → Bool) (l : Fin 21) : Bool :=
    !(List.finRange 14).any (fun i => p i && adj i l)
  obtain ⟨D, hD, hDsize, hPos, hNeg⟩ := boundary49
  obtain ⟨C, hC, hCsize, hLift⟩ := lift49 D hD
  have hMonoFold : ∀ (gs : List Gate),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      ∀ (a b : List Bool), a.length = b.length →
        (∀ k, a.getD k false = true → b.getD k false = true) →
        ∀ k, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a).getD k false = true →
             (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) b).getD k false = true := by
    intro gs
    induction gs with
    | nil =>
      intro _ a b _ hab k hk
      exact hab k hk
    | cons g gs ih =>
      intro hgs a b hlen hab k hk
      have hg : g.op = GateOp.and ∨ g.op = GateOp.or := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using (hgs g (List.mem_cons_self ..)).1
      have hrest : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
        fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
      have hval : g.op.eval (g.inputs.map fun i => a.getD i false) = true →
                  g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
        rcases hg with hop | hop
        · rw [hop]
          change (g.inputs.map fun i => a.getD i false).all id = true →
            (g.inputs.map fun i => b.getD i false).all id = true
          simp only [List.all_eq_true, List.mem_map, id_eq, forall_exists_index, and_imp,
            forall_apply_eq_imp_iff₂]
          intro h i hi
          exact hab i (h i hi)
        · rw [hop]
          change (g.inputs.map fun i => a.getD i false).any id = true →
            (g.inputs.map fun i => b.getD i false).any id = true
          simp only [List.any_eq_true, List.mem_map, id_eq]
          rintro ⟨_, ⟨i, hi, rfl⟩, hia⟩
          exact ⟨true, ⟨i, hi, hab i hia⟩, rfl⟩
      apply ih hrest (a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)])
        (b ++ [g.op.eval (g.inputs.map fun i => b.getD i false)])
      · simp [hlen]
      · intro j hj
        by_cases hlt : j < a.length
        · rw [List.getD_append _ _ _ _ hlt] at hj
          rw [List.getD_append _ _ _ _ (hlen ▸ hlt)]
          exact hab j hj
        · by_cases heq : j = a.length
          · subst heq
            rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)] at hj
            rw [List.getD_append_right _ _ _ _ (Nat.le_of_eq hlen.symm)]
            simp only [Nat.sub_self, List.getD_cons_zero] at hj
            rw [hlen, Nat.sub_self, List.getD_cons_zero]
            exact hval hj
          · have hge : (a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]).length ≤ j := by
              simp; omega
            rw [List.getD_eq_default _ _ hge] at hj
            cases hj
      · exact hk
  have hApp : ∀ (u1 u2 v1 v2 : List Bool), u1.length = u2.length →
      (∀ k, u1.getD k false = true → u2.getD k false = true) →
      (∀ k, v1.getD k false = true → v2.getD k false = true) →
      ∀ k, (u1 ++ v1).getD k false = true → (u2 ++ v2).getD k false = true := by
    intro u1 u2 v1 v2 hlen hu hv k hk
    by_cases hlt : k < u1.length
    · rw [List.getD_append _ _ _ _ hlt] at hk
      rw [List.getD_append _ _ _ _ (hlen ▸ hlt)]
      exact hu k hk
    · have hge : u1.length ≤ k := Nat.le_of_not_lt hlt
      rw [List.getD_append_right _ _ _ _ hge] at hk
      rw [List.getD_append_right _ _ _ _ (hlen ▸ hge), ← hlen]
      exact hv (k - u1.length) hk
  have hOfFn : ∀ {n : ℕ} (f1 f2 : Fin n → Bool),
      (∀ i, f1 i = true → f2 i = true) →
      ∀ k, (List.ofFn f1).getD k false = true → (List.ofFn f2).getD k false = true := by
    intro n f1 f2 hf k hk
    by_cases hlt : k < n
    · rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hlt), List.getElem_ofFn] at hk
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hlt), List.getElem_ofFn]
      exact hf ⟨k, hlt⟩ hk
    · rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; exact Nat.le_of_not_lt hlt)] at hk
      cases hk
  have hB49mono : ∀ (p1 p2 : Fin 14 → Bool) (y1 y2 : Fin 21 → Bool),
      (∀ i, p1 i = true → p2 i = true) →
      (∀ l, y1 l = true → y2 l = true) →
      D.eval (B49 p1 y1) = true → D.eval (B49 p2 y2) = true := by
    intro p1 p2 y1 y2 hp hy heval
    apply hMonoFold D.gates hD (B49 p1 y1) (B49 p2 y2)
    · simp [B49]
    · apply hApp _ _ _ _ (by simp)
      · apply hApp _ _ _ _ (by simp)
        · apply hApp _ _ _ _ (by simp)
          · exact hOfFn p1 p2 hp
          · exact hOfFn y1 y2 hy
        · apply hOfFn
          intro j hj
          rcases Bool.or_eq_true_iff.mp hj with h1 | h2
          · exact Bool.or_eq_true_iff.mpr (Or.inl (hy _ h1))
          · exact Bool.or_eq_true_iff.mpr (Or.inr (hy _ h2))
      · apply hOfFn
        intro j hj
        rcases Bool.or_eq_true_iff.mp hj with h12 | h3
        · rcases Bool.or_eq_true_iff.mp h12 with h1 | h2
          · exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inl (hy _ h1))))
          · exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inr (hy _ h2))))
        · exact Bool.or_eq_true_iff.mpr (Or.inr (hy _ h3))
    · exact heval
  have hmem_iff : ∀ d : ℕ, (d == 0 || d == 5 || d == 7 || d == 17 || d == 20) = true ↔
      d ∈ ([0, 5, 7, 17, 20] : List ℕ) := by
    intro d
    simp [or_assoc]
  refine ⟨C, hC, Nat.le_trans hCsize hDsize, ?_⟩
  intro x
  let L (j : Fin 7) (d : ℕ) := x (Fin.ofNat 42 (21 + (3 * j.val + d) % 21))
  let w := (List.ofFn x ++ List.ofFn (fun j : Fin 7 => L j 5 || L j 17)) ++
    List.ofFn (fun j : Fin 7 => L j 5 || L j 17 || L j 20)
  let px : Fin 14 → Bool := fun i => x (Fin.ofNat 42 (3 * (i.val / 2) + i.val % 2))
  let yx : Fin 21 → Bool := fun l => x (Fin.ofNat 42 (21 + l.val))
  have hwlen : w.length = 56 := by simp [w]
  have hw49 : List.ofFn (fun i : Fin 14 => w.getD (3 * (i.val / 2) + i.val % 2) false) ++ w.drop 21 =
      B49 px yx := by
    have hL : ∀ (j : Fin 7) (d : ℕ), yx (Fin.ofNat 21 ((3 * j.val + d) % 21)) = L j d := by
      intro j d
      dsimp only [yx, L]
      congr 1
      apply Fin.ext
      have hm : (3 * j.val + d) % 21 < 21 := Nat.mod_lt _ (by decide)
      simp [Nat.mod_eq_of_lt hm]
    have hpt : List.ofFn (fun i : Fin 14 => w.getD (3 * (i.val / 2) + i.val % 2) false) = List.ofFn px := by
      congr 1
      funext i
      have hi : 3 * (i.val / 2) + i.val % 2 < 42 := by omega
      dsimp only [w, px]
      rw [List.getD_append _ _ _ _ (by simp; omega),
          List.getD_append _ _ _ _ (by simp; omega),
          List.getD_eq_getElem _ _ (by simp; omega),
          List.getElem_ofFn]
      congr 1
      apply Fin.ext
      simp [Nat.mod_eq_of_lt hi]
    have hdx : (List.ofFn x).drop 21 = List.ofFn yx := by
      apply List.ext_getElem
      · simp
      · intro k hk1 hk2
        simp only [List.getElem_drop, List.getElem_ofFn]
        dsimp only [yx]
        congr 1
        apply Fin.ext
        have hk : 21 + k < 42 := by simp at hk2; omega
        simp [Nat.mod_eq_of_lt hk]
    have hdrop : w.drop 21 =
        (List.ofFn yx ++ List.ofFn (fun j : Fin 7 => L j 5 || L j 17)) ++
          List.ofFn (fun j : Fin 7 => L j 5 || L j 17 || L j 20) := by
      dsimp only [w]
      rw [List.drop_append_of_le_length (by simp),
          List.drop_append_of_le_length (by simp), hdx]
    rw [hpt, hdrop]
    dsimp only [B49]
    simp only [hL, List.append_assoc]
  change C.eval w = true ↔ _
  rw [hLift w hwlen, hw49]
  constructor
  · intro hEval
    by_contra hNoEdge
    have hNoAdj : ∀ (i : Fin 14) (l : Fin 21), adj i l = true → px i = true → yx l = true → False := by
      intro i l hadj hpi hyl
      let u : Fin 42 := Fin.ofNat 42 (3 * (i.val / 2) + i.val % 2)
      let v : Fin 42 := Fin.ofNat 42 (21 + l.val)
      have hu : u.val = 3 * (i.val / 2) + i.val % 2 := by
        simp [u, Nat.mod_eq_of_lt (by omega : 3 * (i.val / 2) + i.val % 2 < 42)]
      have hv : v.val = 21 + l.val := by
        simp [v, Nat.mod_eq_of_lt (by omega : 21 + l.val < 42)]
      have hmem : (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ) := by
        have h1 : (l.val + 21 - (3 * (i.val / 2) + i.val % 2)) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ) :=
          (hmem_iff _).mp hadj
        have hmod : (v.val + 21 - u.val) % 21 = (l.val + 21 - (3 * (i.val / 2) + i.val % 2)) % 21 := by
          rw [hu, hv]
          omega
        rw [hmod]
        exact h1
      exact hNoEdge ⟨u, v, ⟨by omega, by omega, by omega, hmem⟩, hpi, hyl⟩
    let L0 (l : Fin 21) : Bool := !(List.finRange 14).any (fun i => px i && adj i l)
    let Pcl (i : Fin 14) : Bool := !(List.finRange 21).any (fun l => L0 l && adj i l)
    have hpx_cl : ∀ i : Fin 14, px i = true → Pcl i = true := by
      intro i hpi
      dsimp only [Pcl]
      rw [Bool.not_eq_true', List.any_eq_false]
      intro l _
      cases hL0 : L0 l with
      | false => simp
      | true =>
        dsimp only [L0] at hL0
        rw [Bool.not_eq_true', List.any_eq_false] at hL0
        have hi := hL0 i (List.mem_finRange i)
        simp [hpi] at hi
        simp [hi]
    have hfree_eq : ∀ l : Fin 21, free Pcl l = L0 l := by
      intro l
      cases hL0 : L0 l with
      | true =>
        dsimp only [free]
        rw [Bool.not_eq_true', List.any_eq_false]
        intro i _
        cases hPi : Pcl i with
        | false => simp
        | true =>
          dsimp only [Pcl] at hPi
          rw [Bool.not_eq_true', List.any_eq_false] at hPi
          have hl := hPi l (List.mem_finRange l)
          simp [hL0] at hl
          simp [hl]
      | false =>
        dsimp only [L0] at hL0
        rw [Bool.not_eq_false', List.any_eq_true] at hL0
        obtain ⟨i, _, hi⟩ := hL0
        have hpi : px i = true := (Bool.and_eq_true _ _).mp hi |>.1
        have hadj : adj i l = true := (Bool.and_eq_true _ _).mp hi |>.2
        dsimp only [free]
        rw [Bool.not_eq_false', List.any_eq_true]
        exact ⟨i, List.mem_finRange i, by rw [hpx_cl i hpi, hadj]; rfl⟩
    have hclosed : ∀ i : Fin 14, (∀ l : Fin 21, free Pcl l = true → adj i l = false) → Pcl i = true := by
      intro i hi
      dsimp only [Pcl]
      rw [Bool.not_eq_true', List.any_eq_false]
      intro l _
      cases hL0 : L0 l with
      | false => simp
      | true =>
        have hfl : free Pcl l = true := by rw [hfree_eq l]; exact hL0
        simp [hi l hfl]
    have hyx_free : ∀ l : Fin 21, yx l = true → free Pcl l = true := by
      intro l hyl
      rw [hfree_eq l]
      dsimp only [L0]
      rw [Bool.not_eq_true', List.any_eq_false]
      intro i _
      cases hpi : px i with
      | false => simp
      | true =>
        cases hadj : adj i l with
        | false => simp
        | true => exact False.elim (hNoAdj i l hadj hpi hyl)
    have htrue : D.eval (B49 Pcl (free Pcl)) = true :=
      hB49mono px Pcl yx (free Pcl) hpx_cl hyx_free hEval
    have hfalse : D.eval (B49 Pcl (free Pcl)) = false := hNeg Pcl hclosed
    rw [hfalse] at htrue
    cases htrue
  · rintro ⟨u, v, ⟨hu1, hu2, hv1, hmem⟩, hxu, hxv⟩
    let i : Fin 14 := ⟨2 * (u.val / 3) + u.val % 3, by omega⟩
    let l : Fin 21 := ⟨v.val - 21, by omega⟩
    have hi_eq : 3 * (i.val / 2) + i.val % 2 = u.val := by
      dsimp only [i]
      omega
    have hl_eq : 21 + l.val = v.val := by
      dsimp only [l]
      omega
    have hadj : adj i l = true := by
      dsimp only [adj]
      rw [hi_eq, hmem_iff]
      have hmod : (l.val + 21 - u.val) % 21 = (v.val + 21 - u.val) % 21 := by
        dsimp only [l]
        omega
      rw [hmod]
      exact hmem
    have hpx_i : px i = true := by
      dsimp only [px]
      rw [hi_eq]
      have hfu : Fin.ofNat 42 u.val = u := by
        apply Fin.ext
        simp
      rw [hfu]
      exact hxu
    have hyx_l : yx l = true := by
      dsimp only [yx]
      rw [hl_eq]
      have hfv : Fin.ofNat 42 v.val = v := by
        apply Fin.ext
        simp
      rw [hfv]
      exact hxv
    exact hB49mono (fun a => a == i) px (fun b => b == l) yx
      (fun a ha => by rw [beq_iff_eq.mp ha]; exact hpx_i)
      (fun b hb => by rw [beq_iff_eq.mp hb]; exact hyx_l)
      (hPos i l hadj)
