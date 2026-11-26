import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19137

abbrev Pair := ℕ × ℕ
def keys (l : List Pair) := (l.map Prod.fst).toFinset
def value : List Pair → ℕ
  | [] => 0
  | (a,b) :: l => (a &&& b) ||| value l

theorem keys_cons (a b : ℕ) (l : List Pair) : keys ((a,b)::l) = insert a (keys l) := by
  simp [keys]
theorem keys_append (l r : List Pair) : keys (l++r) = keys l ∪ keys r := by
  simp [keys]
theorem value_append (l r : List Pair) : value (l++r) = value l ||| value r := by
  induction l with
  | nil => simp [value]
  | cons p l ih => obtain ⟨a,b⟩ := p; simp [value,ih,Nat.or_assoc]

theorem fold_value (l : List Pair) (z : ℕ) :
    l.foldl (fun v p => v ||| (p.1 &&& p.2)) z = z ||| value l := by
  induction l generalizing z with
  | nil => simp [value]
  | cons p l ih => obtain ⟨a,b⟩ := p; simp [value,ih,Nat.or_assoc]

def Code (base g : List ℕ) : Prop :=
  ∀ (i : Fin g.length), ∃ a ∈ base ++ g.take i.val, ∃ b ∈ base ++ g.take i.val, g.get i = a ||| b

def Valid (base : List ℕ) (mask : ℕ) (l : List Pair) : Prop :=
  ∀ p ∈ l, p.1 ∈ base ∧ p.2 ∈ base ∧ p.1 &&& p.2 &&& mask = 0

theorem add_code {base g : List ℕ} {a b : ℕ} (nd : g.Nodup)
    (fresh : ∀ v ∈ g, v ∉ base) (code : Code base g)
    (ha : a ∈ base++g) (hb : b ∈ base++g) :
    ∃ t : List ℕ, t.Nodup ∧ (∀ v ∈ t, v ∉ base) ∧ Code base t ∧
      (∀ v ∈ base++g, v ∈ base++t) ∧ a ||| b ∈ base++t ∧ t.length ≤ g.length+1 := by
  let v := a ||| b
  by_cases h : v ∈ base++g
  · exact ⟨g,nd,fresh,code,fun _ h => h,h,by omega⟩
  have newbase : v ∉ base := fun hv => h (List.mem_append_left _ hv)
  have newg : v ∉ g := fun hv => h (List.mem_append_right _ hv)
  refine ⟨g++[v],by rw [List.nodup_append_comm]; simpa using And.intro newg nd,?_,?_,?_,by simp [v],by simp⟩
  · intro w hw
    rcases List.mem_append.mp hw with e | e
    · exact fresh w e
    · have ew : w = v := by simpa using e
      exact ew ▸ newbase
  · intro i
    have lim : i.val ≤ g.length := by have := i.isLt; simp at this; omega
    have take_eq : (g++[v]).take i.val = g.take i.val := List.take_append_of_le_length lim
    rw [take_eq]
    by_cases lt : i.val < g.length
    · have e : (g++[v]).get i = g.get ⟨i.val,lt⟩ := by
        change (g++[v])[i.val] = g[i.val]; rw [List.getElem_append_left lt]
      rw [e]; exact code ⟨i.val,lt⟩
    · have e : i.val = g.length := by omega
      have ev : (g++[v]).get i = v := by
        change (g++[v])[i.val] = v
        rw [List.getElem_append_right (by omega)]; simp [e]
      rw [ev,e,List.take_length]
      exact ⟨a,ha,b,hb,rfl⟩
  · intro w hw
    rcases List.mem_append.mp hw with e | e
    · exact List.mem_append_left _ e
    · exact List.mem_append_right _ (List.mem_append_left _ e)

theorem pack (base : List ℕ) (mask : ℕ) (l : List Pair) (good : Valid base mask l) :
    ∃ (g : List ℕ) (ys : List Pair), g.Nodup ∧ (∀ v ∈ g, v ∉ base) ∧ Code base g ∧
      Valid (base++g) mask ys ∧ keys ys = keys l ∧ ys.length = (keys l).card ∧
      g.length + ys.length ≤ l.length ∧ value ys = value l := by
  induction l with
  | nil =>
    exact ⟨[],[],by simp,by simp,fun i => Fin.elim0 i,by simp [Valid],rfl,by simp [keys],by simp,rfl⟩
  | cons p l ih =>
    obtain ⟨a,b⟩ := p
    obtain ⟨g,ys,nd,fresh,code,legal,ks,lc,budget,eq⟩ := ih (fun p hp => good p (List.mem_cons_of_mem _ hp))
    obtain ⟨ha,hb,hzero⟩ := good (a,b) List.mem_cons_self
    have ab := List.mem_append_left g ha
    have bb := List.mem_append_left g hb
    by_cases hkey : a ∈ keys l
    · have hit : a ∈ ys.map Prod.fst := by
        have : a ∈ keys ys := ks.symm ▸ hkey
        simpa only [keys,List.mem_toFinset] using this
      obtain ⟨⟨a',b'⟩,old,e⟩ := List.mem_map.mp hit
      change a' = a at e
      subst a'
      obtain ⟨wa,wb,wzero⟩ := legal _ old
      obtain ⟨t,nt,ft,ct,keep,joined,cost⟩ := add_code nd fresh code bb wb
      obtain ⟨left,right,ey⟩ := List.mem_iff_append.mp old
      let out : List Pair := left ++ (a,b ||| b') :: right
      have same : keys out = keys ys := by simp [out,ey,keys_append,keys_cons]
      have same_len : out.length = ys.length := by simp [out,ey]
      refine ⟨t,out,nt,ft,ct,?_,by rw [same,ks,keys_cons,Finset.insert_eq_of_mem hkey],
        by rw [same_len,lc,keys_cons,Finset.insert_eq_of_mem hkey],by simp; omega,?_⟩
      · intro p hp
        rcases List.mem_append.mp hp with hleft | hright
        · obtain ⟨e1,e2,e3⟩ := legal p (ey ▸ List.mem_append_left _ hleft)
          exact ⟨keep _ e1,keep _ e2,e3⟩
        · rcases List.mem_cons.mp hright with rfl | he
          · exact ⟨keep _ wa,joined,by simp only [Nat.and_or_distrib_left,Nat.and_or_distrib_right]; simpa [hzero,wzero]⟩
          · obtain ⟨e1,e2,e3⟩ := legal p (ey ▸ List.mem_append_right _ (List.mem_cons_of_mem _ he))
            exact ⟨keep _ e1,keep _ e2,e3⟩
      · change value (left ++ (a,b ||| b')::right) = (a &&& b) ||| value l
        rw [←eq,ey,value_append,value_append]
        simp only [value,Nat.and_or_distrib_left]; ac_rfl
    · refine ⟨g,(a,b)::ys,nd,fresh,code,?_,by rw [keys_cons,keys_cons,ks],
        by simp [keys_cons,hkey,lc],by simp; omega,by simp [value,eq]⟩
      intro p hp
      rcases List.mem_cons.mp hp with rfl | e
      · exact ⟨ab,bb,hzero⟩
      · exact legal p e

end PEqualNP.Outside.L_meta_19137

theorem PEqualNP.Outside.L_meta_19137 : (∀ (x1 : List ℕ) (x2 : List (ℕ × ℕ)) (x3 x4 : ℕ),   x2 ≠ [] →     (∀ x6 ∈ x2, x6.1 ∈ x1 ∧ x6.2 ∈ x1 ∧ x6.1 &&& x6.2 &&& x3 = (0 : ℕ)) →       ∃ (x7 : List ℕ) (x8 : List (ℕ × ℕ)),         x7.Nodup ∧           (∀ x9 ∈ x7, x9 ∉ x1) ∧             x8 ≠ [] ∧               x7.length + (2 : ℕ) * x8.length ≤ x2.length + (List.map Prod.fst x2).toFinset.card ∧                 (∀ (x9 : Fin x7.length),                     have x10 : List ℕ := x1 ++ List.take (↑x9) x7;                     ∃ x11 ∈ x10, ∃ x12 ∈ x10, x7.get x9 = x11 ||| x12) ∧                   (∀ x9 ∈ x8, x9.1 ∈ x1 ++ x7 ∧ x9.2 ∈ x1 ++ x7 ∧ x9.1 &&& x9.2 &&& x3 = (0 : ℕ)) ∧ List.foldl (fun (x9 : ℕ) (x10 : ℕ × ℕ) => x9 ||| x10.1 &&& x10.2) x4 x8 = List.foldl (fun (x9 : ℕ) (x10 : ℕ × ℕ) => x9 ||| x10.1 &&& x10.2) x4 x2) := by
  intro base l mask z hne h
  obtain ⟨g,ys,nd,fr,code,good,ks,lc,budget,eq⟩ := PEqualNP.Outside.L_meta_19137.pack base mask l h
  have ne : ys ≠ [] := by
    rintro rfl
    cases l with
    | nil => exact hne rfl
    | cons p t =>
      obtain ⟨a,b⟩ := p
      have ha : a ∈ PEqualNP.Outside.L_meta_19137.keys ((a,b)::t) := by simp [PEqualNP.Outside.L_meta_19137.keys_cons]
      rw [←ks] at ha
      simpa [PEqualNP.Outside.L_meta_19137.keys] using ha
  exact ⟨g,ys,nd,fr,ne,by change g.length + 2*ys.length ≤ l.length + (PEqualNP.Outside.L_meta_19137.keys l).card; omega,
    code,good,by rw [PEqualNP.Outside.L_meta_19137.fold_value,PEqualNP.Outside.L_meta_19137.fold_value,eq]⟩
