import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_7698_aux
open Finset
abbrev O:=Fin 14
abbrev o:=Finset O
abbrev _E8:o:={2,4,5,6,9,11,12,13}
abbrev _d:=Bool
abbrev _F:=List
lemma V{p:Prop}[Decidable p](h:decide p=true:=by decide):p:=of_decide_eq_true h
abbrev _ep:=@Equiv.Perm
abbrev _of{α:Type u_1}{n:Nat}(f:Fin n->α):=List.ofFn f
lemma _mg{α:Type u_1}{β:Type u_2}[DecidableEq β]{f:α->β}{s:Finset α}{b:β}:b∈s.image f<->∃a∈s,f a=b:=mem_image
lemma _mss{α:Type u_1}(a:α):a∈({a}:Finset α):=mem_singleton_self a
lemma _ms{α:Type u_1}{a b:α}:b∈({a}:Finset α)<->b=a:=mem_singleton
lemma _mf{α:Type u_1}{p:α->Prop}[DecidablePred p]{s:Finset α}{a:α}:a∈s.filter p<->a∈s/\p a:=mem_filter
lemma _mi{α:Type u_1}[DecidableEq α]{s:Finset α}{a b:α}:a∈insert b s<->a=b\/a∈s:=mem_insert
lemma _cl{α:Type u_1}{s t:Finset α}(h:s⊆t):s.card<=t.card:=card_le_card h
lemma _cp{α:Type u_1}{s:Finset α}:0<s.card<->s.Nonempty:=card_pos
lemma _c1{α:Type u_1}{s:Finset α}:s.card=1<->∃a,s={a}:=card_eq_one
lemma _ct2{α:Type u_1}{s:Finset α}[DecidableEq α]:s.card=2<->∃x y,x≠y/\s={x,y}:=card_eq_two
lemma _c2{α:Type u_1}{a b:α}[DecidableEq α](h:a≠b):({a,b}:Finset α).card=2:=card_pair h
lemma _fs{α:Type u_1}(p:α->Prop)[DecidablePred p](s:Finset α):s.filter p⊆s:=filter_subset p s
lemma _eqc{α:Type u_1}{s t:Finset α}(h1:s⊆t)(h2:t.card<=s.card):s=t:=eq_of_subset_of_card_le h1 h2
lemma _dl{α:Type u_1}{s t:Finset α}:Disjoint s t<->∀⦃a:α⦄,a∈s->a∉t:=disjoint_left
lemma _mu{α:Type u_1}[DecidableEq α]{s t:Finset α}{a:α}:a∈s∪t<->a∈s\/a∈t:=mem_union
lemma _mn{α:Type u_1}[DecidableEq α]{a:α}{s t:Finset α}:a∈s∩t<->a∈s/\a∈t:=mem_inter
lemma _md{α:Type u_1}[DecidableEq α]{s t:Finset α}{a:α}:a∈s\t<->a∈s/\a∉t:=mem_sdiff
lemma _me{α:Type u_1}[DecidableEq α]{a b:α}{s:Finset α}:a∈erase s b<->a≠b/\a∈s:=mem_erase
lemma _mv{α:Type u_1}[Fintype α](x:α):x∈univ:=mem_univ x
lemma _si{α:Type u_1}{s t:Finset α}:s⊆t<->∀⦃x:α⦄,x∈s->x∈t:=subset_iff
lemma _cs{α:Type u_1}(a:α):({a}:Finset α).card=1:=card_singleton a
lemma _ce{α:Type u_1}:(∅:Finset α).card=0:=card_empty
lemma _nt(a b:Nat):a<b\/a=b\/b<a:=Nat.lt_trichotomy a b
lemma _nr(n:Nat):¬n<n:=Nat.lt_irrefl n
lemma _fe{n:Nat}{a b:Fin n}(h:a.val=b.val):a=b:=Fin.ext h
lemma _fnt:false≠true:=Bool.false_ne_true
lemma _lge{α:Type u_1}(l:_F α)(d:α){n:Nat}(h:n<l.length):l.getD n d=l[n]:=List.getD_eq_getElem l d h
lemma _cfl{α:Type u_1}(s:Finset α)(p:α->Prop)[DecidablePred p]:(s.filter p).card<=s.card:=card_filter_le s p
lemma _cin{α:Type u_1}[DecidableEq α]{a:α}{s:Finset α}(h:a∉s):(insert a s).card=s.card+1:=card_insert_of_notMem h
lemma _cii{α:Type u_1}{β:Type u_2}[DecidableEq β]{s:Finset α}(f:α->β)(hf:Function.Injective f):(s.image f).card=s.card:=card_image_of_injective s hf
lemma _cij{α:Type u_1}{β:Type u_2}[DecidableEq β]{s:Finset α}{f:α->β}(hf:Set.InjOn f s):(s.image f).card=s.card:=card_image_of_injOn hf
lemma _cud{α:Type u_1}[DecidableEq α]{s t:Finset α}(h:Disjoint s t):(s∪t).card=s.card+t.card:=card_union_of_disjoint h
lemma _nf(b:_d):(¬b=false)=(b=true):=Bool.not_eq_false b
def kF:_d->_d->_d->_d
 | true,a,b=>a&&b
 | false,a,b=>a||b
@[simp] lemma gop_true (a b:_d):kF true a b=(a&&b):=rfl
@[simp] lemma gop_false (a b:_d):kF false a b=(a||b):=rfl
abbrev Dag:=_F (_d×ℕ×ℕ)
def cR (D:Dag) (j:ℕ):_d:=(D.getD j (false,0,0)).1
def cj (D:Dag) (j:ℕ):ℕ:=(D.getD j (false,0,0)).2.1
def ck (D:Dag) (j:ℕ):ℕ:=(D.getD j (false,0,0)).2.2
def gl (w:_F _d) (g:_d×ℕ×ℕ):_F _d:=w ++ [kF g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]
def kD (D:Dag) (w:_F _d):_F _d:=D.foldl gl w
def val (D:Dag) {n:ℕ} (x:Fin n->_d) (w:ℕ):_d:=(kD D (_of x)).getD w false
def au (n:ℕ) (D:Dag):Prop:=∀ j,j<D.length->cj D j<n+j/\ck D j<n+j/\cj D j≠ck D j
def bV (D:Dag) (w:ℕ):Finset ℕ:=(range D.length).filter (fun j=>cj D j=w\/ck D j=w)
def aF (D:Dag) (w:ℕ):ℕ:=(bV D w).card
def o7 (n:ℕ) (D:Dag):Prop:=∀ w,w+1<n+D.length->1<=aF D w
def ai (n:ℕ) (D:Dag):Prop:=au n D/\o7 n D/\D≠[]
def bH (n:ℕ) (D:Dag):ℕ:=n+D.length - 1
def cl {n:ℕ} (v:Fin n):Fin n->_d:=fun i=>decide (i=v)
def ag (n:ℕ) (D:Dag) (w:ℕ):Finset (Fin n):=univ.filter (fun v=>val D (cl v) w=true)
def bn (D:Dag) (K:Finset ℕ):ℕ:=∑ w∈K,(aF D w - 1)
def cD (n:ℕ) (D:Dag):Finset ℕ:=range (n+D.length - 1)
def ap (n:ℕ) (D:Dag):ℕ:=bn D (cD n D)
def bd (n:ℕ) (D:Dag):ℕ:=bn D ((cD n D).filter (fun w=>(ag n D w).Nonempty))
def bL (n:ℕ) (D:Dag):ℕ:=bn D ((cD n D).filter (fun w=>¬ (ag n D w).Nonempty))
def m5 (n:ℕ) (D:Dag):Finset ℕ:=(range (n+D.length)).filter (fun w=>2<=aF D w)
def al (n:ℕ) (D:Dag):Finset (Fin n):=(m5 n D).biUnion (ag n D)
def aa (n:ℕ) (D:Dag):Finset (Fin n):=univ\al n D
def dq (n:ℕ) (D:Dag):Finset (Σ _:ℕ,ℕ):=(cD n D).sigma (fun w=>range (aF D w - 1))
def da (n:ℕ) (D:Dag):Finset (Σ _:ℕ,ℕ):=(dq n D).filter (fun u=>(ag n D u.1).Nonempty)
def eK (D:Dag):Finset (ℕ×_d):=range D.length ×ˢ univ
def aw (D:Dag) (e:ℕ×_d):ℕ:=if e.2=true then ck D e.1 else cj D e.1
def aE (n:ℕ) (D:Dag) (K:Finset ℕ):Finset (ℕ×_d):=(eK D).filter (fun e=>aw D e∈K/\n+e.1∉K)
def aW (n:ℕ) (D:Dag) (K:Finset ℕ):Finset ℕ:=(range D.length).filter (fun j=>n+j∈K/\cj D j∈K/\ck D j∈K)
def gb (n:ℕ) (K:Finset ℕ):Finset ℕ:=K.filter (fun w=>w<n)
def ao (n:ℕ) (D:Dag) (T:Finset (Fin n)):Finset ℕ:=(range (n+D.length)).filter (fun w=>(ag n D w∩T).Nonempty)
def aR (n:ℕ) (D:Dag) (x y:Fin n):Finset ℕ:=(range (n+D.length)).filter (fun w=>x∈ag n D w/\y∉ag n D w)
def aM (n:ℕ) (D:Dag) (b:Fin n->ℕ):Prop:=∀ v∈al n D,2<=aF D (b v)/\ag n D (b v)={v}
def cz (n:ℕ) (D:Dag) (b:Fin n->ℕ):Finset (Σ _:ℕ,ℕ):=(al n D).image (fun v=>(⟨b v,0⟩:Σ _:ℕ,ℕ))
def aj (n:ℕ) (D:Dag) (b:Fin n->ℕ):Finset (Σ _:ℕ,ℕ):=da n D\cz n D b
lemma ou (D:Dag) (j:ℕ) (h:j<D.length):cR D j=(D[j]).1:=by
 simp[cR,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]
lemma ov (D:Dag) (j:ℕ) (h:j<D.length):cj D j=(D[j]).2.1:=by
 simp[cj,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]
lemma ow (D:Dag) (j:ℕ) (h:j<D.length):ck D j=(D[j]).2.2:=by
 simp[ck,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]
lemma m6 (g:_d×ℕ×ℕ) (D:Dag) (w:_F _d):kD (g :: D) w=kD D (gl w g):=rfl
lemma k4 (D E:Dag) (w:_F _d):kD (D ++ E) w=kD E (kD D w):=by
 simp[kD,List.foldl_append]
lemma iR (w:_F _d) (g:_d×ℕ×ℕ):(gl w g).length=w.length+1:=by
 simp[gl]
lemma jr (D:Dag):∀ w:_F _d,(kD D w).length=w.length+D.length:=by
 induction D with
 | nil=>intro w;simp[kD]
 | cons g D ih=>intro w;rw[m6,ih,iR];simp;omega
lemma jZ (w:_F _d) (g:_d×ℕ×ℕ) (i:ℕ) (h:i<w.length):(gl w g).getD i false=w.getD i false:=by
 simp[gl,List.getD_eq_getElem?_getD,List.getElem?_append_left h]
lemma j3 (D:Dag):∀(w:_F _d) (i:ℕ),i<w.length ->(kD D w).getD i false=w.getD i false:=by
 induction D with
 | nil=>intro w i _;rfl
 | cons g D ih=>
  intro w i h;rw[m6,ih _ _ (by rw[iR];omega),jZ _ _ _ h]
lemma rm (w:_F _d) (i:ℕ) (h:w.length<=i):w.getD i false=false:=by
 simp[List.getD_eq_getElem?_getD,List.getElem?_eq_none h]
lemma jd (w:_F _d) (g:_d×ℕ×ℕ):(gl w g).getD w.length false=kF g.1 (w.getD g.2.1 false) (w.getD g.2.2 false):=by
 simp[gl,List.getD_eq_getElem?_getD]
lemma nK (D:Dag) (w:_F _d) (j:ℕ) (c:j<D.length):(kD D w).getD (w.length+j) false =kF (cR D j) ((kD (D.take j) w).getD (cj D j) false) ((kD (D.take j) w).getD (ck D j) false):=by
 have a:D=D.take j ++ D[j]:: D.drop (j+1):=by simp
 have b:(kD (D.take j) w).length=w.length+j:=by{rw[jr,List.length_take];omega};rw[ou D j c,ov D j c,ow D j c];conv_lhs=>rw[a,k4,m6]
 rw[j3 _ _ _ (by rw[iR,b];omega),<-b,jd]
lemma iS (D:Dag) (w:_F _d) (j i:ℕ) (c:i<w.length+j) (d:j<=D.length):(kD (D.take j) w).getD i false=(kD D w).getD i false:=by
 have a:D=D.take j ++ D.drop j:=by simp
 have b:(kD (D.take j) w).length=w.length+j:=by{rw[jr,List.length_take];omega};conv_rhs=>rw[a,k4]
 rw[j3 (D.drop j) (kD (D.take j) w) i (by rw[b];exact c)]
lemma bY (D:Dag) {n:ℕ} (x:Fin n->_d) (i:ℕ) (h:i<n):val D x i=x ⟨i,h⟩:=by
 unfold val;rw[j3 _ _ _ (by simpa using h)];simp[List.getD_eq_getElem?_getD,h]
lemma fs (D:Dag) {n:ℕ} (x:Fin n->_d) (w:ℕ) (h:n+D.length<=w):val D x w=false:=by
 unfold val;exact rm _ _ (by rw[jr];simpa using h)
lemma oe (D:Dag) {n:ℕ} (x:Fin n->_d) (k w:ℕ) (a:w<n+k) (b:k<=D.length):val (D.take k) x w=val D x w:=by
 unfold val;exact iS D _ k w (by simpa using a) b
lemma cS {n:ℕ} {D:Dag} (b:au n D) (x:Fin n->_d) (j:ℕ) (a:j<D.length):val D x (n+j)=kF (cR D j) (val D x (cj D j)) (val D x (ck D j)):=by
 obtain⟨c,d,-⟩:=b j a;have h:=nK D (_of x) j a;simp only[List.length_ofFn] at h;unfold val;rw[h,iS D _ j _ (by simpa using c) a.le,iS D _ j _ (by simpa using d) a.le]
lemma iA {n:ℕ} {D:Dag} (c:au n D) (x:Fin n->_d) (f:ℕ->_d) (a:∀ i (h:i<n),f i=x ⟨i,h⟩) (e:∀ j,j<D.length->f (n+j)=kF (cR D j) (f (cj D j)) (f (ck D j))):∀ w,w<n+D.length->val D x w=f w:=by
 intro w;induction w using Nat.strong_induction_on with
 | _ w ih=>
  intro l;by_cases d:w<n;{rw[bY D x w d,a w d]}
  · obtain⟨j,rfl⟩:∃ j,w=n+j:=⟨w - n,by omega⟩
    have b:j<D.length:=by omega
    obtain⟨g,k,-⟩:=c j b;rw[cS c x j b,e j b,ih _ g (by omega),ih _ k (by omega)]
abbrev js:=_d ⊕ ℕ
def db (W:_F _d):js->_d
 | Sum.inl b=>b
 | Sum.inr k=>W.getD k false
def eP (m:_F js) (i:ℕ):js:=m.getD i (Sum.inl false)
def d7 (t:_d):js->js->js ⊕ (ℕ×ℕ)
 | Sum.inl a,r=>Sum.inl (if a=t then r else Sum.inl a)
 | Sum.inr i,Sum.inl b=>Sum.inl (if b=t then Sum.inr i else Sum.inl b)
 | Sum.inr i,Sum.inr j=>if i=j then Sum.inl (Sum.inr i) else Sum.inr (i,j)
def dQ:GateOp->_d
 | GateOp.and=>true
 | _=>false
def cH (n:ℕ) (c:_F js×Dag) (g:Gate):_F js×Dag:=match g.inputs with
 |[]=>(c.1 ++ [Sum.inl (dQ g.op)],c.2)
 |[a]=>(c.1 ++ [eP c.1 a],c.2)
 | a :: b :: _=>
  match d7 (dQ g.op) (eP c.1 a) (eP c.1 b) with
  | Sum.inl r=>(c.1 ++ [r],c.2)
  | Sum.inr p=>(c.1 ++ [Sum.inr (n+c.2.length)],c.2 ++ [(dQ g.op,p.1,p.2)])
def iT (B:ℕ):js->Prop
 | Sum.inl _=>True
 | Sum.inr k=>k<B
def j4 (n:ℕ) (a:_F js×Dag):Prop:=au n a.2/\∀ r∈a.1,iT (n+a.2.length) r
lemma o8 {B B':ℕ} (h:B<=B') (r:js) (a:iT B r):iT B' r:=by
 rcases r with b|k;{trivial};{exact lt_of_lt_of_le a h}
lemma fD (W:_F _d) (m:_F js) (i:ℕ):db W (eP m i)=(m.map (db W)).getD i false:=by
 simp only[eP,List.getD_eq_getElem?_getD,List.getElem?_map];cases m[i]? <;> rfl
lemma iB (B:ℕ) (m:_F js) (a:∀ r∈m,iT B r) (i:ℕ):iT B (eP m i):=by
 simp only[eP,List.getD_eq_getElem?_getD];rcases h:m[i]? with _|r;{trivial};{exact a r (List.mem_of_getElem? h)}
lemma lT (W:_F _d) (g:_d×ℕ×ℕ) (r:js) (a:iT W.length r):db (gl W g) r=db W r:=by
 rcases r with b|k;{rfl};{exact jZ W g k a}
lemma ox (t:_d) (W:_F _d) (a b r:js) (h:d7 t a b=Sum.inl r):db W r=kF t (db W a) (db W b):=by
 rcases a with a|i
 · simp only[d7,Sum.inl.injEq] at h
   subst h;cases t <;> cases a <;> simp[db]
 · rcases b with b|j
   · simp only[d7,Sum.inl.injEq] at h
     subst h;cases t <;> cases b <;> simp[db]
   · simp only[d7] at h
     split_ifs at h with c;simp only[Sum.inl.injEq] at h;subst h;subst c;cases t <;> simp[db]
lemma o9 (B:ℕ) (t:_d) (a b r:js) (c:iT B a) (d:iT B b) (h:d7 t a b=Sum.inl r):iT B r:=by
 rcases a with a|i
 · simp only[d7,Sum.inl.injEq] at h
   subst h;split_ifs;{exact d};{trivial}
 · rcases b with b|j
   · simp only[d7,Sum.inl.injEq] at h
     subst h;split_ifs;{exact c};{trivial}
   · simp only[d7] at h
     split_ifs at h;simp only[Sum.inl.injEq] at h;subst h;exact c
lemma oy (t:_d) (a b:js) (p:ℕ×ℕ) (h:d7 t a b=Sum.inr p):a=Sum.inr p.1/\b=Sum.inr p.2/\p.1≠p.2:=by
 rcases a with a|i;{simp[d7] at h}
 · rcases b with b|j
   · simp[d7] at h
   · simp only[d7] at h
     split_ifs at h with c;cases h
     exact⟨rfl,rfl,c⟩
lemma qL (op:GateOp) (a:op∈({GateOp.and,GateOp.or}:Set GateOp)):op.eval []=dQ op:=by
 rcases a with rfl|rfl <;> rfl
lemma qM (op:GateOp) (a:op∈({GateOp.and,GateOp.or}:Set GateOp)) (u:_d):op.eval [u]=u:=by
 rcases a with rfl|rfl <;> simp[GateOp.eval]
lemma og (op:GateOp) (a:op∈({GateOp.and,GateOp.or}:Set GateOp)) (u v:_d):op.eval [u,v]=kF (dQ op) u v:=by
 rcases a with rfl|rfl <;> simp[GateOp.eval,dQ]
lemma gM (D E:Dag) (k:ℕ) (h:k<D.length):(D ++ E).getD k (false,0,0)=D.getD k (false,0,0):=by
 simp[List.getD_eq_getElem?_getD,List.getElem?_append_left h]
lemma f9 (D:Dag) (g:_d×ℕ×ℕ):(D ++ [g]).getD D.length (false,0,0)=g:=by
 simp[List.getD_eq_getElem?_getD]
lemma jG {n:ℕ} {D:Dag} (d:au n D) (t:_d) (i j:ℕ) (e:i<n+D.length) (f:j<n+D.length) (b:i≠j):au n (D ++ [(t,i,j)]):=by
 intro k g;simp only[List.length_append,List.length_singleton] at g;by_cases g':k<D.length
 · simp only[cj,ck,gM D _ k g']
   exact d k g'
 · have c:k=D.length:=by omega
   subst c;simp only[cj,ck,f9];exact⟨e,f,b⟩
lemma mE {n:ℕ} {D:Dag} (c:au n D) (k:ℕ):au n (D.take k):=by
 intro j d;simp only[List.length_take] at d;have a:j<k:=by omega
 have b:j<D.length:=by omega
 have e:(D.take k).getD j (false,0,0)=D.getD j (false,0,0):=by{simp[List.getD_eq_getElem?_getD,a]};simp only[cj,ck,e];exact c j b
lemma nL (n:ℕ) (l:_F js×Dag) (g:Gate) (C:g.op∈({GateOp.and,GateOp.or}:Set GateOp)/\g.inputs.length<=2) (h:j4 n l):j4 n (cH n l g)/\(cH n l g).2.length<=l.2.length+1 /\∀(x:Fin n->_d) (w:_F _d),l.1.map (db (kD l.2 (_of x)))=w ->(cH n l g).1.map (db (kD (cH n l g).2 (_of x)))=w ++ [g.op.eval (g.inputs.map fun i=>w.getD i false)]:=by
 obtain⟨m,D⟩:=l;obtain⟨op,ins⟩:=g;obtain⟨f,q⟩:=C;obtain⟨v,e⟩:=h;dsimp only at v e f q⊢;rcases ins with _|⟨a,_|⟨b,_|⟨c,rest⟩⟩⟩
 · refine⟨⟨v,?_⟩,by simp[cH],fun x w s=>?_⟩
   · intro r d
     simp only[cH,List.mem_append,List.mem_singleton] at d;rcases d with d|rfl;{exact e r d};{trivial}
   · subst s
     simp only[cH,List.map_append,List.map_cons,List.map_nil,db,qL op f]
 · refine⟨⟨v,?_⟩,by simp[cH],fun x w s=>?_⟩
   · intro r d
     simp only[cH,List.mem_append,List.mem_singleton] at d;rcases d with d|rfl;{exact e r d};{exact iB _ m e a}
   · subst s
     simp only[cH,List.map_append,List.map_cons,List.map_nil,qM op f,fD]
 · have t:=iB _ m e a
   have u:=iB _ m e b;rcases j:d7 (dQ op) (eP m a) (eP m b) with r|p
   · refine⟨⟨by simpa only[cH,j] using v,?_⟩,by simp[cH,j],fun x w s=>?_⟩
     · intro r' d
       simp only[cH,j,List.mem_append,List.mem_singleton] at d⊢;rcases d with d|rfl;{exact e r' d};{exact o9 _ _ _ _ _ t u j}
     · subst s
       simp only[cH,j,List.map_append,List.map_cons,List.map_nil,og op f,ox _ (kD D (_of x)) _ _ _ j,fD]
   · obtain⟨ea,eb,z⟩:=oy _ _ _ _ j
     rw[ea] at t;rw[eb] at u;have v':=jG v (dQ op) p.1 p.2 t u z;refine⟨⟨by simpa only[cH,j] using v',?_⟩,by simp[cH,j],fun x w s=>?_⟩
     · intro r' d
       simp only[cH,j,List.mem_append,List.mem_singleton,List.length_append,List.length_singleton] at d⊢;rcases d with d|rfl;{exact o8 (by omega) r' (e r' d)}
       · show n+D.length<n+(D.length+1)
         omega
     · subst s
       have k:(kD D (_of x)).length=n+D.length:=by{rw[jr,List.length_ofFn]};have hW':kD (D ++ [(dQ op,p.1,p.2)]) (_of x)=gl (kD D (_of x)) (dQ op,p.1,p.2):=by{rw[k4];rfl};have E:m.map (db (gl (kD D (_of x)) (dQ op,p.1,p.2)))=m.map (db (kD D (_of x))):=List.map_congr_left (fun r d=>lT _ _ r (by rw[k];exact e r d));have F:(gl (kD D (_of x)) (dQ op,p.1,p.2)).getD (n+D.length) false =kF (dQ op) ((m.map (db (kD D (_of x)))).getD a false) ((m.map (db (kD D (_of x)))).getD b false):=by{rw[<- k,jd,<-fD,<-fD,ea,eb];rfl};simp only[cH,j,hW',List.map_append,List.map_cons,List.map_nil,E,db,F,og op f]
 · simp at q
lemma nM (n:ℕ) (b:_F Gate) (c:∀ g∈b,g.op∈({GateOp.and,GateOp.or}:Set GateOp)/\g.inputs.length<=2):∀ a:_F js×Dag,j4 n a ->j4 n (b.foldl (cH n) a) /\(b.foldl (cH n) a).2.length<=a.2.length+b.length /\∀(x:Fin n->_d) (w:_F _d),a.1.map (db (kD a.2 (_of x)))=w ->(b.foldl (cH n) a).1.map (db (kD (b.foldl (cH n) a).2 (_of x)))=b.foldl (fun w g=>w ++ [g.op.eval (g.inputs.map fun i=>w.getD i false)]) w:=by
 induction b with
 | nil=>intro a h;exact⟨h,by simp,fun x w d=>d⟩
 | cons g b ih=>
  intro a h;obtain⟨f,l,j⟩:=nL n a g (c g (by simp)) h;obtain⟨i1,i2,i3⟩:=ih (fun g' hg'=>c g' (by simp[hg'])) _ f;refine⟨i1,?_,fun x w d=>?_⟩;{simp only[List.foldl_cons,List.length_cons];omega};{simp only[List.foldl_cons];exact i3 x _ (j x w d)}
lemma rn (n:ℕ) (x:Fin n->_d):((List.range n).map Sum.inr).map (db (kD ([]:Dag) (_of x)))=_of x:=by
 apply List.ext_getElem;{simp}
 · intro i a b
   simp only[List.length_map,List.length_range] at a;simp[db,kD,List.getD_eq_getElem?_getD,a]
lemma gv {n:ℕ} (C:Circuit) (d:Monotone2 C):(∃ b:_d,∀ x:Fin n->_d,C.eval (_of x)=b) \/(∃ i:Fin n,∀ x:Fin n->_d,C.eval (_of x)=x i) \/(∃ D:Dag,au n D/\D≠[]/\D.length<=C.size /\∀ x:Fin n->_d,val D x (bH n D)=C.eval (_of x)):=by
 have t:j4 n ((List.range n).map Sum.inr,([]:Dag)):=by{refine⟨fun j u=>absurd u (by simp),fun r e=>?_⟩;simp only[List.mem_map,List.mem_range] at e;obtain⟨k,p,rfl⟩:=e;simpa[iT] using p};obtain⟨⟨s,f⟩,a,c⟩:=nM n C.gates d _ t;generalize C.gates.foldl (cH n) ((List.range n).map Sum.inr,([]:Dag))=st at s f a c;obtain⟨m,D⟩:=st;dsimp only at s f a c;have g:∀ x:Fin n->_d,C.eval (_of x)=db (kD D (_of x)) (eP m C.output):=by{intro x;rw[fD,c x (_of x) (rn n x)];rfl};have p:=iB _ m f C.output;rcases e:eP m C.output with b|k;{exact Or.inl ⟨b,fun x=>by rw[g x,e];rfl⟩}
 · rw[e] at p
   have p':k<n+D.length:=p;by_cases l:k<n;{exact Or.inr (Or.inl ⟨⟨k,l⟩,fun x=>by rw[g x,e];exact bY D x k l⟩)}
   · have q:(D.take (k - n+1)).length=k - n+1:=by
      rw[List.length_take];omega
     refine Or.inr (Or.inr ⟨D.take (k - n+1),mE s _,?_,?_,fun x=>?_⟩)
     · intro h
       rw[h] at q;simp at q
     · rw[q]
       simp only[List.length_nil,Nat.zero_add] at a;unfold Circuit.size;omega
     · have w:bH n (D.take (k - n+1))=k:=by unfold bH;rw[q];omega
       rw[w,oe D x (k - n+1) k (by omega) (by omega),g x,e];rfl
lemma iU {D:Dag} {w:ℕ} (h:aF D w=0) (j:ℕ) (a:j<D.length):cj D j≠w/\ck D j≠w:=by
 unfold aF bV at h;rw[card_eq_zero,filter_eq_empty_iff] at h;have:=h (mem_range.mpr a);tauto
def jt (c a:ℕ):ℕ:=if c<a then a - 1 else a
def cX (c w:ℕ):ℕ:=if w<c then w else w+1
def eL (n j:ℕ) (D:Dag):Dag:=(D.eraseIdx j).map (fun g=>(g.1,jt (n+j) g.2.1,jt (n+j) g.2.2))
lemma fE (n j:ℕ) (D:Dag) (a:j<D.length):(eL n j D).length=D.length - 1:=by
 simp[eL,List.length_eraseIdx,a]
lemma ms (n j:ℕ) (D:Dag) (k:ℕ) (a:cX j k<D.length):cR (eL n j D) k=cR D (cX j k) /\cj (eL n j D) k=jt (n+j) (cj D (cX j k)) /\ck (eL n j D) k=jt (n+j) (ck D (cX j k)):=by
 have e:(eL n j D).getD k (false,0,0)=((D.getD (cX j k) (false,0,0)).1,jt (n+j) (D.getD (cX j k) (false,0,0)).2.1,jt (n+j) (D.getD (cX j k) (false,0,0)).2.2):=by{simp only[eL,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eraseIdx];unfold cX at a⊢;split_ifs at a⊢<;> simp[List.getElem?_eq_getElem a]};unfold cR cj ck;rw[e];exact⟨rfl,rfl,rfl⟩
lemma j5 {n:ℕ} {D:Dag} (d:au n D) (j:ℕ) (e:j<D.length) (f:aF D (n+j)=0):au n (eL n j D):=by
 intro k g;rw[fE n j D e] at g;have g':cX j k<D.length:=by unfold cX;split_ifs <;> omega
 have h:(k<j/\cX j k=k)\/(j<=k/\cX j k=k+1):=by{unfold cX;split_ifs <;> omega};obtain⟨l,m,i⟩:=d _ g';obtain⟨ra,rb⟩:=iU f _ g';obtain⟨-,ea,eb⟩:=ms n j D k g';rw[ea,eb];generalize cX j k=k' at *
 generalize cj D k'=a at *
 generalize ck D k'=b at *
 refine⟨?_,?_,?_⟩<;> unfold jt <;> split_ifs <;> omega
lemma o_ {n:ℕ} {D:Dag} (d:au n D) (j:ℕ) (c:j<D.length) (f:aF D (n+j)=0) (x:Fin n->_d) (w:ℕ) (l:w<n+(D.length - 1)):val (eL n j D) x w=val D x (cX (n+j) w):=by
 refine iA (j5 d j c f) x (fun u=>val D x (cX (n+j) u)) (fun i g=>?_) (fun k m=>?_) w (by rw[fE n j D c];exact l)
 · have e:cX (n+j) i=i:=by unfold cX;split_ifs <;> omega
   show val D x (cX (n+j) i)=x ⟨i,g⟩;rw[e];exact bY D x i g
 · rw[fE n j D c] at m
   have m':cX j k<D.length:=by unfold cX;split_ifs <;> omega
   obtain⟨et,ea,eb⟩:=ms n j D k m';obtain⟨ra,rb⟩:=iU f _ m';have p:cX (n+j) (n+k)=n+cX j k:=by unfold cX;split_ifs <;> omega
   have h:∀ a,a≠n+j->cX (n+j) (jt (n+j) a)=a:=by{intro a q;unfold cX jt;split_ifs <;> omega};show val D x (cX (n+j) (n+k))=kF (cR (eL n j D) k) (val D x (cX (n+j) (cj (eL n j D) k))) (val D x (cX (n+j) (ck (eL n j D) k)));rw[p,et,ea,eb,h _ ra,h _ rb];exact cS d x _ m'
lemma oz {n:ℕ} (F:(Fin n->_d)->_d) (e:∀ i:Fin n,∃ x y:Fin n->_d,(∀ k,k≠i->x k=y k)/\F x≠F y):∀(s:ℕ) (D:Dag),D.length=s->au n D->D≠[] ->(∀ x:Fin n->_d,val D x (bH n D)=F x) ->∃ D':Dag,ai n D'/\D'.length<=s /\∀ x:Fin n->_d,val D' x (bH n D')=F x:=by
 intro s;induction s using Nat.strong_induction_on with
 | _ s ih=>
  intro D f g l v;have C:0<D.length:=List.length_pos_iff.mpr l;by_cases E:o7 n D;{exact⟨D,⟨g,E,l⟩,f.le,v⟩}
  · obtain⟨w,G,a⟩:∃ w,w+1<n+D.length/\aF D w=0:=by
     by_contra m
     exact E (fun w G=>by
      by_contra P
      exact m ⟨w,G,by omega⟩)
    by_cases p:w<n
    · exfalso
      obtain⟨x,y,A,q⟩:=e ⟨w,p⟩;apply q;rw[<- v x,<-v y];have r:bH n D≠w:=by unfold bH;omega
      have t:=iA g y (fun u=>if u=w then y ⟨w,p⟩ else val D x u) (fun i H=>by
       by_cases b:i=w;{subst b;simp}
       · simp only[b,ite_false]
         rw[bY D x i H]
         exact A ⟨i,H⟩ (fun h=>b (congrArg Fin.val h)))
       (fun j d=>by
        obtain⟨I,J⟩:=iU a j d;have B:n+j≠w:=by omega
        simp only[B,I,J,ite_false]
        exact cS g x j d)
       (bH n D) (by unfold bH;omega)
      simp only[r,ite_false] at t;exact t.symm
    · obtain⟨j,rfl⟩:∃ j,w=n+j:=⟨w - n,by omega⟩
      have d:j<D.length:=by omega
      have z:=fE n j D d
      obtain⟨D',K,Q,L⟩:=ih (D.length - 1) (by omega) (eL n j D) z (j5 g j d a) (fun h=>by rw[h] at z;simp at z;omega) (fun x=>by
       have M:bH n (eL n j D)=n+(D.length - 1) - 1:=by unfold bH;rw[z]
       have N:cX (n+j) (n+(D.length - 1) - 1)=bH n D:=by{unfold cX bH;split_ifs <;> omega};rw[M,o_ g j d a x _ (by omega),N]
       exact v x)
      exact⟨D',K,by omega,L⟩
lemma gm {n:ℕ} (F:(Fin n->_d)->_d) (a:∀ i:Fin n,∃ x y:Fin n->_d,(∀ k,k≠i->x k=y k)/\F x≠F y) (D:Dag) (d:au n D) (c:D≠[]) (e:∀ x:Fin n->_d,val D x (bH n D)=F x):∃ D':Dag,ai n D'/\D'.length<=D.length /\∀ x:Fin n->_d,val D' x (bH n D')=F x:=oz F a D.length D rfl d c e
lemma fV {n:ℕ} (C:Circuit) (a:Monotone2 C) (d:∀ b:_d,∃ x:Fin n->_d,C.eval (_of x)≠b) (e:∀ i:Fin n,∃ x:Fin n->_d,C.eval (_of x)≠x i) (c:∀ i:Fin n,∃ x y:Fin n->_d,(∀ k,k≠i->x k=y k) /\C.eval (_of x)≠C.eval (_of y)):∃ D:Dag,ai n D/\D.length<=C.size /\∀ x:Fin n->_d,val D x (bH n D)=C.eval (_of x):=by
 rcases gv (n:=n) C a with
  ⟨b,j⟩|⟨i,l⟩|⟨D,m,f,h,p⟩
 · obtain⟨x,g⟩:=d b
   exact absurd (j x) g
 · obtain⟨x,g⟩:=e i
   exact absurd (l x) g
 · obtain⟨D',q,s,r⟩:=gm (fun x=>C.eval (_of x)) c D m f p
   exact⟨D',q,by omega,r⟩
section SurplusFlow
variable {n : ℕ} {D : Dag}
lemma bP {w:ℕ}:w∈cD n D↔w+1<n+D.length:=by
 unfold cD;rw[mem_range];omega
lemma aX (j:ℕ):aw D (j,false)=cj D j:=by simp[aw]
lemma bh (j:ℕ):aw D (j,true)=ck D j:=by simp[aw]
lemma d0 (b:au n D) (w:ℕ) (h:n+D.length<=w+1):aF D w=0:=by
 unfold aF bV;rw[card_eq_zero,filter_eq_empty_iff];intro j c;have a:=mem_range.mp c;have:=b j a;omega
lemma dc (a:au n D) {w:ℕ} (h:1<=aF D w):w+1<n+D.length:=by
 by_contra b;have:=d0 a w (by omega);omega
lemma d8 (P:ℕ×_d->Prop) [DecidablePred P]:((eK D).filter P).card=∑ j∈range D.length,((if P (j,false) then 1 else 0)+(if P (j,true) then 1 else 0)):=by
 rw[card_filter,eK,sum_product];refine sum_congr rfl (fun j _=>?_);rw[Fintype.sum_bool,add_comm]
lemma nN:(eK D).card=2*D.length:=by
 simp[eK,card_product,Nat.mul_comm]
lemma pV (a:au n D) (e:ℕ×_d) (b:e∈eK D):aw D e+1<n+D.length:=by
 obtain⟨j,c⟩:=e;have d:j<D.length:=by simpa[eK] using b
 have:=a j d;cases c;{rw[aX];omega};{rw[bh];omega}
lemma mF (a:au n D) (w:ℕ):aF D w=((eK D).filter (fun e=>aw D e=w)).card:=by
 rw[d8,aF,bV,card_filter];refine sum_congr rfl (fun j b=>?_);have:=(a j (mem_range.mp b)).2.2;rw[aX,bh];split_ifs <;> omega
lemma fF (b:au n D) (K:Finset ℕ):∑ w∈K,aF D w=((eK D).filter (fun e=>aw D e∈K)).card:=by
 rw[card_eq_sum_card_fiberwise (f:=aw D) (s:=(eK D).filter (fun e=>aw D e∈K)) (t:=K) (fun e a=>mem_coe.mpr (_mf.mp (mem_coe.mp a)).2)];refine sum_congr rfl (fun w c=>?_);rw[mF b,filter_filter];congr 1;ext e;simp only[_mf];constructor;{rintro⟨a,rfl⟩;exact⟨a,c,rfl⟩};{rintro⟨a,-,h⟩;exact⟨a,h⟩}
lemma eQ {K:Finset ℕ} (a:∀ w∈K,1<=aF D w):bn D K+K.card=∑ w∈K,aF D w:=by
 rw[bn,card_eq_sum_ones,<-sum_add_distrib];exact sum_congr rfl (fun w b=>Nat.sub_add_cancel (a w b))
lemma iC (h:ai n D):ap n D+n=D.length+1:=by
 obtain⟨b,d,a⟩:=h;have c:0<D.length:=List.length_pos_iff.mpr a;have i:bn D (cD n D)+(cD n D).card=∑ w∈cD n D,aF D w:=eQ (fun w f=>d w (bP.mp f));have j:∑ w∈cD n D,aF D w=2*D.length:=by{rw[fF b,filter_true_of_mem,nN];intro e g;exact bP.mpr (pV b e g)};have k:(cD n D).card=n+D.length - 1:=card_range _;unfold ap;omega
lemma bg (n:ℕ) (D:Dag):ap n D=bd n D+bL n D:=by
 unfold ap bd bL bn;exact(sum_filter_add_sum_filter_not _ _ _).symm
lemma dC (n:ℕ) (D:Dag):bd n D<=ap n D:=by
 rw[bg];omega
lemma iD (h:ai n D) (w:ℕ) (i:w<n+D.length):Relation.ReflTransGen (fun a b=>b<n+D.length/\n<=b /\(cj D (b - n)=a\/ck D (b - n)=a)) w (bH n D):=by
 obtain⟨f,g,-⟩:=h;generalize l:n+D.length - w=k;induction k using Nat.strong_induction_on generalizing w with
 | _ k ih=>
  by_cases c:w+1=n+D.length
  · have d:w=bH n D:=by unfold bH;omega
    rw[d]
  · obtain⟨j,e⟩:=_cp.mp (g w (by omega))
    simp only[bV,_mf,mem_range] at e;have m:=f j e.1;refine Relation.ReflTransGen.head (b:=n+j) ⟨by omega,by omega,?_⟩ (ih (n+D.length - (n+j)) (by omega) (n+j) (by omega) rfl);simpa using e.2
lemma ee {v:Fin n} {w:ℕ}:v∈ag n D w↔val D (cl v) w=true:=by
 simp[ag]
lemma gJ (a:au n D) (x y:Fin n->_d) (b:∀ i,x i=true->y i=true) (w:ℕ):val D x w=true->val D y w=true:=by
 induction w using Nat.strong_induction_on with
 | _ w ih=>
  by_cases d:w<n;{rw[bY D x w d,bY D y w d];exact b _}
  · by_cases g:w<n+D.length
    · obtain⟨j,rfl⟩:∃ j,w=n+j:=⟨w - n,by omega⟩
      have c:j<D.length:=by omega
      obtain⟨e,f,-⟩:=a j c;rw[cS a x j c,cS a y j c];have h:=ih _ e;have k:=ih _ f;cases cR D j <;>
       simp only[gop_true,gop_false,Bool.and_eq_true,Bool.or_eq_true]<;> tauto
    · rw[fs D x w (by omega)];simp
lemma qN (a:au n D) (w:ℕ):val D (fun _:Fin n=>false) w=false:=by
 by_cases b:w<n+D.length;{exact iA a _ (fun _=>false) (fun _ _=>rfl) (fun j _=>by cases cR D j <;> rfl) w b};{exact fs D _ w (by omega)}
lemma dr (D:Dag) (i:Fin n):ag n D i.val={i}:=by
 ext v;rw[ee,bY D (cl v) i.val i.isLt];simp[cl,eq_comm]
lemma pc (D:Dag) (w:ℕ) (h:n+D.length<=w):ag n D w=∅:=by
 ext v;simp[ee,fs D (cl v) w h]
lemma fY (a:au n D) (j:ℕ) (b:j<D.length):ag n D (n+j)=if cR D j=true then ag n D (cj D j)∩ag n D (ck D j)
 else ag n D (cj D j)∪ag n D (ck D j):=by
 ext v;rw[ee,cS a _ j b];cases cR D j <;> simp[ee]
lemma kN (h:ai n D) (K:Finset ℕ) (g:K⊆cD n D) (b:∀ j,j<D.length->n+j∈K->cj D j∈K\/ck D j∈K):(aE n D K).card+(aW n D K).card=(gb n K).card+bn D K:=by
 obtain⟨i,k,-⟩:=h;have a:∀ w∈K,w+1<n+D.length:=fun w c=>bP.mp (g c);have p:bn D K+K.card=((eK D).filter (fun e=>aw D e∈K)).card:=by{rw[<- fF i,eQ (fun w c=>k w (a w c))]};have l:=card_filter_add_card_filter_not (s:=(eK D).filter (fun e=>aw D e∈K)) (fun e:ℕ×_d=>n+e.1∈K);rw[filter_filter,filter_filter] at l;have q:((eK D).filter (fun e=>aw D e∈K/\n+e.1∈K)).card =((range D.length).filter (fun j=>n+j∈K)).card+(aW n D K).card:=by
  rw[d8,aW,card_filter,card_filter,<- sum_add_distrib];refine sum_congr rfl (fun j f=>?_);have:=b j (mem_range.mp f);rw[aX,bh];by_cases m:n+j∈K <;> by_cases r:cj D j∈K <;> by_cases t:ck D j∈K <;>
   simp_all
 have u:K.card=(gb n K).card + ((range D.length).filter (fun j=>n+j∈K)).card:=by
  rw[<- card_filter_add_card_filter_not (s:=K) (fun w=>w<n),gb];congr 1;have d:K.filter (fun w=>¬ w<n)=((range D.length).filter (fun j=>n+j∈K)).image (fun j=>n+j):=by
   ext w;simp only[_mf,_mg,mem_range];constructor
   · rintro⟨c,v⟩
     have:=a w c;exact⟨w - n,⟨by omega,by rwa[Nat.add_sub_cancel' (by omega)]⟩,by omega⟩
   · rintro⟨j,⟨-,f⟩,rfl⟩
     exact⟨f,by omega⟩
  rw[d,_cii _ (add_right_injective n)]
 unfold aE;omega
lemma lU (T:Finset (Fin n)) (a:ag n D (bH n D)∩T=∅):ao n D T⊆cD n D:=by
 intro w b;simp only[ao,_mf,mem_range] at b;rw[bP];by_contra d;have c:w=bH n D:=by unfold bH;omega
 rw[c,a] at b;exact not_nonempty_empty b.2
lemma j6 (D:Dag) (T:Finset (Fin n)):(gb n (ao n D T)).card=T.card:=by
 have a:gb n (ao n D T)=T.image (fun v:Fin n=>v.val):=by
  ext w;simp only[gb,ao,_mf,mem_range,_mg];constructor
  · rintro⟨⟨-,v,b⟩,c⟩
    have d:ag n D w={⟨w,c⟩}:=dr D ⟨w,c⟩;rw[d,_mn,_ms] at b;exact⟨v,b.2,by rw[b.1]⟩
  · rintro⟨v,b,rfl⟩
    refine⟨⟨by have:=v.isLt;omega,v,?_⟩,v.isLt⟩;rw[dr];simp[b]
 rw[a,_cii _ Fin.val_injective]
lemma co (h:ai n D) (T:Finset (Fin n)) (b:ag n D (bH n D)∩T=∅):(aE n D (ao n D T)).card+(aW n D (ao n D T)).card =T.card+bn D (ao n D T):=by
 rw[<- j6 D T];refine kN h _ (lU T b) (fun j d e=>?_);obtain⟨f,g,-⟩:=h.1 j d;simp only[ao,_mf,mem_range] at e⊢;obtain⟨v,a⟩:=e.2;rw[_mn,fY h.1 j d] at a;split_ifs at a with i
 · rw[_mn] at a
   exact Or.inl ⟨by omega,v,_mn.mpr ⟨a.1.1,a.2⟩⟩
 · rw[_mu] at a
   rcases a.1 with c|c;{exact Or.inl ⟨by omega,v,_mn.mpr ⟨c,a.2⟩⟩};{exact Or.inr ⟨by omega,v,_mn.mpr ⟨c,a.2⟩⟩}
lemma gN (h:ai n D) (x y:Fin n) (l:x≠y) (e:x∉ag n D (bH n D)):(aE n D (aR n D x y)).card+(aW n D (aR n D x y)).card =1+bn D (aR n D x y):=by
 have f:aR n D x y⊆cD n D:=by
  intro w d;simp only[aR,_mf,mem_range] at d;rw[bP];by_contra b;have m:w=bH n D:=by unfold bH;omega
  rw[m] at d;exact e d.2.1
 have g:gb n (aR n D x y)={x.val}:=by
  ext w;simp only[gb,aR,_mf,mem_range,_ms];constructor
  · rintro⟨⟨-,a,-⟩,d⟩
    have s:ag n D w={⟨w,d⟩}:=dr D ⟨w,d⟩;rw[s,_ms] at a;rw[a]
  · rintro rfl
    refine⟨⟨by have:=x.isLt;omega,?_,?_⟩,x.isLt⟩;{rw[dr];exact _mss x};{rw[dr,_ms];exact fun b=>l b.symm}
 have i:=kN h _ f (fun j q r=>?_);{rw[g,_cs] at i;exact i}
 · obtain⟨t,u,-⟩:=h.1 j q
   simp only[aR,_mf,mem_range] at r⊢;obtain⟨-,a,c⟩:=r;rw[fY h.1 j q] at a c;split_ifs at a c with v
   · rw[_mn] at a c
     by_cases k:y∈ag n D (cj D j);{exact Or.inr ⟨by omega,a.2,fun b=>c ⟨k,b⟩⟩};{exact Or.inl ⟨by omega,a.1,k⟩}
   · rw[_mu] at a c
     rcases a with p|p;{exact Or.inl ⟨by omega,p,fun b=>c (Or.inl b)⟩};{exact Or.inr ⟨by omega,p,fun b=>c (Or.inr b)⟩}
lemma dW {u:Σ _:ℕ,ℕ}:u∈dq n D↔u.1∈cD n D/\u.2+1<aF D u.1:=by
 rw[dq,mem_sigma,mem_range];constructor <;> rintro⟨a,b⟩<;> exact⟨a,by omega⟩
lemma eI (n:ℕ) (D:Dag) (p:ℕ->Prop) [DecidablePred p]:((dq n D).filter (fun u=>p u.1)).card=bn D ((cD n D).filter p):=by
 have a:(dq n D).filter (fun u=>p u.1)=((cD n D).filter p).sigma (fun w=>range (aF D w - 1)):=by{ext u;simp only[dq,_mf,mem_sigma];tauto};rw[a,card_sigma,bn];simp
lemma mv (n:ℕ) (D:Dag):(dq n D).card=ap n D:=by
 rw[dq,card_sigma,ap,bn];simp
lemma jH (n:ℕ) (D:Dag):(da n D).card=bd n D:=by
 unfold da bd;exact eI n D (fun w=>(ag n D w).Nonempty)
lemma eX {v:Fin n}:v∈al n D↔∃ w,2<=aF D w/\v∈ag n D w:=by
 simp only[al,m5,mem_biUnion,_mf,mem_range];constructor;{rintro⟨w,⟨-,b⟩,a⟩;exact⟨w,b,a⟩}
 · rintro⟨w,b,a⟩
   refine⟨w,⟨?_,b⟩,a⟩;by_contra c;rw[pc D w (by omega)] at a;exact notMem_empty v a
lemma fG {v:Fin n}:v∈aa n D↔∀ w,v∈ag n D w->aF D w<=1:=by
 rw[aa,_md,eX];constructor
 · rintro⟨-,h⟩ w a
   by_contra c;exact h ⟨w,by omega,a⟩
 · intro h
   refine⟨_mv v,?_⟩;rintro⟨w,a,b⟩;have:=h w b;omega
lemma es {v:Fin n} {T:Finset (Fin n)}:(({v}:Finset (Fin n))∩T).Nonempty↔v∈T:=by
 constructor
 · rintro⟨u,a⟩
   rw[_mn,_ms] at a;exact a.1▸a.2
 · intro h
   exact⟨v,_mn.mpr ⟨_mss v,h⟩⟩
lemma je (b:Fin n->ℕ) (d:aM n D b):Set.InjOn (fun v=>(⟨b v,0⟩:Σ _:ℕ,ℕ)) (al n D:Set (Fin n)):=by
 intro v g e a h;have c:b v=b e:=congrArg Sigma.fst h;have f:=(d v g).2;rw[c,(d e a).2] at f;exact(singleton_injective f).symm
lemma eY (a:au n D) (b:Fin n->ℕ) (c:aM n D b):cz n D b⊆da n D:=by
 intro u d;obtain⟨v,e,rfl⟩:=_mg.mp d;obtain⟨h,f⟩:=c v e;have g:1<=aF D (b v):=by omega
 rw[da,_mf,dW];refine⟨⟨bP.mpr (dc a g),?_⟩,?_⟩
 · show 0+1<aF D (b v)
   omega
 · show(ag n D (b v)).Nonempty
   rw[f];exact singleton_nonempty v
lemma j7 (b:Fin n->ℕ) (a:aM n D b):(cz n D b).card=(al n D).card:=
 _cij (je b a)
lemma dX (c:au n D) (b:Fin n->ℕ) (a:aM n D b):(al n D).card<=bd n D:=by
 rw[<- j7 b a,<-jH];exact _cl (eY c b a)
lemma bS (c:au n D) (b:Fin n->ℕ) (a:aM n D b):(aj n D b).card+(al n D).card=bd n D:=by
 rw[<- j7 b a,<-jH];exact card_sdiff_add_card_eq_card (eY c b a)
lemma d9 (j:au n D) (b:Fin n->ℕ) (h:aM n D b) (T:Finset (Fin n)):bn D (ao n D T)=(T∩al n D).card + ((aj n D b).filter (fun u=>(ag n D u.1∩T).Nonempty)).card:=by
 have l:bn D (ao n D T)=((dq n D).filter (fun u=>(ag n D u.1∩T).Nonempty)).card:=by
  rw[eI n D (fun w=>(ag n D w∩T).Nonempty)];symm;refine sum_subset (fun w c=>?_) (fun w c d=>?_)
  · rw[_mf] at c
    have:=bP.mp c.1;exact _mf.mpr ⟨mem_range.mpr (by omega),c.2⟩
  · rw[ao,_mf] at c
    have i:w∉cD n D:=fun m=>d (_mf.mpr ⟨m,c.2⟩);rw[bP] at i;simp[d0 j w (by omega)]
 have p:(dq n D).filter (fun u=>(ag n D u.1∩T).Nonempty)=(cz n D b).filter (fun u=>(ag n D u.1∩T).Nonempty)∪ (aj n D b).filter (fun u=>(ag n D u.1∩T).Nonempty):=by
  ext u;have e:=eY j b h;simp only[aj,da,_mu,_mf,_md];constructor
  · intro a
    by_cases k:u∈cz n D b;{exact Or.inl ⟨k,a.2⟩};{exact Or.inr ⟨⟨⟨a.1,a.2.mono inter_subset_left⟩,k⟩,a.2⟩}
  · rintro (a|a)
    · exact⟨(_mf.mp (e a.1)).1,a.2⟩
    · exact⟨a.1.1.1,a.2⟩
 have q:Disjoint ((cz n D b).filter (fun u=>(ag n D u.1∩T).Nonempty)) ((aj n D b).filter (fun u=>(ag n D u.1∩T).Nonempty)):=disjoint_filter_filter disjoint_sdiff;have r:(cz n D b).filter (fun u=>(ag n D u.1∩T).Nonempty)=(T∩al n D).image (fun v=>(⟨b v,0⟩:Σ _:ℕ,ℕ)):=by
  rw[cz,filter_image];congr 1;ext v;simp only[_mf,_mn];constructor
  · rintro⟨f,g⟩
    rw[(h v f).2,es] at g;exact⟨g,f⟩
  · rintro⟨s,f⟩
    refine⟨f,?_⟩;rw[(h v f).2,es];exact s
 rw[l,p,_cud q,r,
  _cij ((je b h).mono (coe_subset.mpr inter_subset_right))]
lemma cZ (a:au n D) (b:Fin n->ℕ) (c:aM n D b) (T:Finset (Fin n)):bn D (ao n D T)+(al n D).card <=(T∩al n D).card+bd n D:=by
 have d:=d9 a b c T;have e:=bS a b c;have f:=_cfl (aj n D b) (fun u=>(ag n D u.1∩T).Nonempty);omega
end SurplusFlow
def cG {n:ℕ} (σ:_ep (Fin n)) (w:ℕ):ℕ:=if h:w<n then (σ ⟨w,h⟩).val else w
def bo {n:ℕ} (σ:_ep (Fin n)) (D:Dag):Dag:=D.map (fun g=>(g.1,cG σ g.2.1,cG σ g.2.2))
lemma gA {n:ℕ} (σ:_ep (Fin n)) {w:ℕ} (h:w<n):cG σ w=(σ ⟨w,h⟩).val:=by
 simp[cG,h]
lemma en {n:ℕ} (σ:_ep (Fin n)) {w:ℕ} (h:n<=w):cG σ w=w:=by
 simp[cG,Nat.not_lt.mpr h]
lemma c9 {n:ℕ} (σ:_ep (Fin n)) {m:ℕ} (a:n<=m) (w:ℕ):cG σ w<m↔w<m:=by
 by_cases h:w<n
 · rw[gA σ h]
   have:=(σ ⟨w,h⟩).isLt;constructor <;> intro <;> omega
 · rw[en σ (Nat.not_lt.mp h)]
lemma fx {n:ℕ} (σ:_ep (Fin n)) (w:ℕ):cG σ⁻¹ (cG σ w)=w:=by
 by_cases h:w<n;{rw[gA σ h,gA σ⁻¹ (σ ⟨w,h⟩).isLt];simp};{rw[en σ (Nat.not_lt.mp h),en σ⁻¹ (Nat.not_lt.mp h)]}
lemma tr_liftP_inv' {n:ℕ} (σ:_ep (Fin n)) (w:ℕ):cG σ (cG σ⁻¹ w)=w:=by
 simpa using fx σ⁻¹ w
lemma iV {n:ℕ} (σ:_ep (Fin n)) {a b:ℕ}:cG σ a=cG σ b↔a=b:=by
 refine⟨fun h=>?_,congrArg _⟩;have:=congrArg (cG σ⁻¹) h;rwa[fx,fx] at this
lemma cc {n:ℕ} (σ:_ep (Fin n)) (D:Dag):(bo σ D).length=D.length:=by
 simp[bo]
lemma sg {n:ℕ} (σ:_ep (Fin n)) (D:Dag) (j:ℕ) (a:j<D.length):cR (bo σ D) j=cR D j:=by
 rw[ou _ j (by rw[cc];exact a),ou D j a];simp[bo]
lemma oA {n:ℕ} (σ:_ep (Fin n)) (D:Dag) (j:ℕ) (a:j<D.length):cj (bo σ D) j=cG σ (cj D j):=by
 rw[ov _ j (by rw[cc];exact a),ov D j a];simp[bo]
lemma oB {n:ℕ} (σ:_ep (Fin n)) (D:Dag) (j:ℕ) (a:j<D.length):ck (bo σ D) j=cG σ (ck D j):=by
 rw[ow _ j (by rw[cc];exact a),ow D j a];simp[bo]
lemma jI {n:ℕ} (σ:_ep (Fin n)) {D:Dag} (c:au n D):au n (bo σ D):=by
 intro j a;rw[cc] at a;obtain⟨d,e,b⟩:=c j a;rw[oA σ D j a,oB σ D j a];exact⟨(c9 σ (Nat.le_add_right n j) _).mpr d,(c9 σ (Nat.le_add_right n j) _).mpr e,fun h=>b ((iV σ).mp h)⟩
lemma lj {n:ℕ} (σ:_ep (Fin n)) {D:Dag} (d:au n D) (x:Fin n->_d) (w:ℕ):val (bo σ D) x (cG σ w)=val D (fun i=>x (σ i)) w:=by
 by_cases e:w<n+D.length
 · refine(iA (jI σ d) x (fun w'=>val D (fun i=>x (σ i)) (cG σ⁻¹ w')) ?_ ?_ (cG σ w) ?_).trans ?_
   · intro i c
     show val D (fun i=>x (σ i)) (cG σ⁻¹ i)=x ⟨i,c⟩;rw[gA σ⁻¹ c,bY D _ _ (σ⁻¹ ⟨i,c⟩).isLt];simp
   · intro j b
     rw[cc] at b;show val D (fun i=>x (σ i)) (cG σ⁻¹ (n+j))=kF (cR (bo σ D) j) (val D (fun i=>x (σ i)) (cG σ⁻¹ (cj (bo σ D) j))) (val D (fun i=>x (σ i)) (cG σ⁻¹ (ck (bo σ D) j)));rw[en σ⁻¹ (Nat.le_add_right n j),sg σ D j b,oA σ D j b,oB σ D j b,fx,fx,cS d _ j b]
   · rw[cc];exact(c9 σ (Nat.le_add_right _ _) w).mpr e
   · show val D (fun i=>x (σ i)) (cG σ⁻¹ (cG σ w))=_
     rw[fx]
 · have e':=Nat.not_lt.mp e
   rw[en σ (le_trans (Nat.le_add_right _ _) e'),fs _ _ _ (by rw[cc];exact e'),fs _ _ _ e']
lemma ft {n:ℕ} (σ:_ep (Fin n)) (D:Dag) (w:ℕ):aF (bo σ D) (cG σ w)=aF D w:=by
 unfold aF bV;rw[cc];congr 1;apply filter_congr;intro j b;have b':=mem_range.mp b;rw[oA σ D j b',oB σ D j b',iV,iV]
lemma nO {n:ℕ} (σ:_ep (Fin n)) {D:Dag} (d:o7 n D):o7 n (bo σ D):=by
 rcases eq_or_ne D [] with rfl|b;{exact d}
 · intro w' hw'
   rw[cc] at hw';have e:=List.length_pos_iff.mpr b;rw[<- tr_liftP_inv' σ w',ft];apply d;by_cases h:w'<n
   · have:=(c9 σ⁻¹ le_rfl w').mpr h
     omega
   · rw[en σ⁻¹ (Nat.not_lt.mp h)];exact hw'
lemma fd {n:ℕ} (σ:_ep (Fin n)) {D:Dag} (h:ai n D):ai n (bo σ D):=⟨jI σ h.1,nO σ h.2.1,by simpa[bo] using h.2.2⟩
lemma fI {n:ℕ} (σ:_ep (Fin n)) {D:Dag} (c:au n D) (a:D≠[]) (x:Fin n->_d):val (bo σ D) x (bH n (bo σ D))=val D (fun i=>x (σ i)) (bH n D):=by
 have b:=List.length_pos_iff.mpr a;have e:bH n (bo σ D)=cG σ (bH n D):=by{rw[en σ (by unfold bH;omega)];simp[bH,cc]};rw[e,lj σ c]
lemma mG {n:ℕ} (σ:_ep (Fin n)) (v:Fin n):(fun i=>cl v (σ i))=cl (σ⁻¹ v):=by
 funext i;simp only[cl,decide_eq_decide];constructor;{intro h;rw[<- h];simp};{intro h;rw[h];simp}
lemma fh {n:ℕ} (σ:_ep (Fin n)) {D:Dag} (b:au n D) (w:ℕ):ag n (bo σ D) (cG σ w)=(ag n D w).image σ:=by
 ext v;simp only[ag,_mf,_mv,true_and,_mg];rw[lj σ b,mG];constructor;{intro h;exact⟨σ⁻¹ v,h,by simp⟩};{rintro⟨a,c,rfl⟩;simpa using c}
lemma nP {n:ℕ} (σ:_ep (Fin n)) {m:ℕ} (c:n<=m) (P:ℕ->Prop) [DecidablePred P] (g:ℕ->ℕ):∑ w∈(range m).filter (fun w=>P (cG σ w)),g (cG σ w)=∑ w∈(range m).filter P,g w:=by
 refine sum_nbij' (cG σ) (cG σ⁻¹) ?_ ?_ ?_ ?_ ?_
 · intro a b
   simp only[_mf,mem_range] at b⊢;exact⟨(c9 σ c a).mpr b.1,b.2⟩
 · intro a b
   simp only[_mf,mem_range] at b⊢;exact⟨(c9 σ⁻¹ c a).mpr b.1,by rw[tr_liftP_inv'];exact b.2⟩
 · intro a _;exact fx σ a
 · intro a _;exact tr_liftP_inv' σ a
 · intro a _;rfl
lemma eo {n:ℕ} (σ:_ep (Fin n)) (D:Dag) (P Q:ℕ->Prop) [DecidablePred P] [DecidablePred Q] (a:∀ w,Q (cG σ w)↔P w):bn (bo σ D) ((cD n (bo σ D)).filter Q)=bn D ((cD n D).filter P):=by
 rcases eq_or_ne D [] with rfl|b;{simp[bn,bo,aF,bV]}
 · have c:=List.length_pos_iff.mpr b
   have d:n<=n+D.length - 1:=by omega
   unfold bn cD;rw[cc];exact(nP σ d Q (fun w=>aF (bo σ D) w - 1)).symm.trans (sum_congr (filter_congr fun w _=>a w) fun w _=>by rw[ft])
lemma eJ {n:ℕ} (σ:_ep (Fin n)) (D:Dag):ap n (bo σ D)=ap n D:=by
 simpa[ap] using eo σ D (fun _=>True) (fun _=>True) (fun _=>Iff.rfl)
lemma j8 {n:ℕ} (σ:_ep (Fin n)) {D:Dag} (a:au n D):bd n (bo σ D)=bd n D:=eo σ D _ _ (fun w=>by rw[fh σ a];simp)
lemma j9 {n:ℕ} (σ:_ep (Fin n)) {D:Dag} (a:au n D):bL n (bo σ D)=bL n D:=eo σ D _ _ (fun w=>by rw[fh σ a];simp)
lemma fZ {n:ℕ} (σ:_ep (Fin n)) {D:Dag} (e:au n D):al n (bo σ D)=(al n D).image σ:=by
 ext v;simp only[al,mem_biUnion,_mg,m5,_mf,mem_range];constructor
 · rintro⟨w',⟨g',c⟩,f⟩
   obtain⟨w,rfl⟩:∃ w,w'=cG σ w:=⟨cG σ⁻¹ w',(tr_liftP_inv' σ w').symm⟩;rw[fh σ e,_mg] at f;obtain⟨a,d,rfl⟩:=f;rw[ft] at c;rw[cc,c9 σ (Nat.le_add_right _ _)] at g';exact⟨a,⟨w,⟨g',c⟩,d⟩,rfl⟩
 · rintro⟨a,⟨w,⟨g,c⟩,d⟩,rfl⟩
   refine⟨cG σ w,⟨?_,?_⟩,?_⟩;{rw[cc];exact(c9 σ (Nat.le_add_right _ _) w).mpr g};{rw[ft];exact c};{rw[fh σ e];exact mem_image_of_mem _ d}
lemma ep {n:ℕ} (σ:_ep (Fin n)) {D:Dag} (d:au n D):aa n (bo σ D)=(aa n D).image σ:=by
 ext v
 simp only[aa,fZ σ d,_md,_mv,true_and,
  _mg]
 constructor
 · intro h
   exact⟨σ⁻¹ v,fun e=>h ⟨σ⁻¹ v,e,by simp⟩,by simp⟩
 · rintro⟨a,f,rfl⟩ ⟨b,g,c⟩
   exact f (σ.injective c▸g)
lemma aV (n:ℕ) (D:Dag):(aa n D).card+(al n D).card=n:=by
 have h:=card_sdiff_add_card_eq_card (subset_univ (al n D));rw[card_univ,Fintype.card_fin] at h;exact h
def cN {n:ℕ} (G:Fin n->Fin n->Prop) (x:Fin n->_d):Prop:=∃ u v:Fin n,G u v/\x u=true/\x v=true
def bJ {n:ℕ} (G:Fin n->Fin n->Prop):Prop:=(∀ u v,G u v->G v u)/\(∀ u,¬ G u u)/\(∀ v w,v≠w->∃ z,G v z/\¬ G w z) /\(∀ u v,∃ a,G u a/\a≠v)
def bk (n:ℕ) (D:Dag) (a b:ℕ):Prop:=b<n+D.length/\n<=b/\(cj D (b - n)=a\/ck D (b - n)=a)
def b4 {n:ℕ} (u z:Fin n):Fin n->_d:=fun i=>decide (i=u)||decide (i=z)
def sem_Umbrella (n:ℕ) (G H:Fin n->Fin n->Prop) (D:Dag):Prop:=bJ H/\(∀ u v,G u v->H u v) /\(∀ x:Fin n->_d,cN G x->val D x (bH n D)=true) /\(∀ x:Fin n->_d,val D x (bH n D)=true->cN H x) /\(∀ u v:Fin n,¬ G u v->val D (b4 u v) (bH n D)=false)
abbrev dg (n:ℕ) (G:Fin n->Fin n->Prop) (D:Dag):Prop:=sem_Umbrella n G G D
lemma kO {n:ℕ} {G:Fin n->Fin n->Prop} {D:Dag} (a:dg n G D) (x:Fin n->_d):val D x (bH n D)=true↔cN G x:=⟨a.2.2.2.1 x,a.2.2.1 x⟩
lemma ju {n:ℕ} {G:Fin n->Fin n->Prop} {D:Dag} (d:bJ G) (h:∀ x:Fin n->_d,val D x (bH n D)=true↔cN G x):dg n G D:=⟨d,fun _ _ k=>k,fun x e=>(h x).2 e,fun x e=>(h x).1 e,fun u v f=>by
 by_contra g;rw[_nf] at g;obtain⟨a,b,c,i,j⟩:=(h _).1 g;simp only[b4,Bool.or_eq_true,decide_eq_true_eq] at i j;rcases i with rfl|rfl <;> rcases j with rfl|rfl;{exact d.2.1 _ c};{exact f c};{exact f (d.1 _ _ c)}
 · exact d.2.1 _ c⟩
def bB {n:ℕ} (v:Fin n) (x:Fin n->_d):Fin n->_d:=fun i=>decide (i=v)||x i
def bM {n:ℕ} (A:Finset (Fin n)):Fin n->_d:=fun i=>decide (i∈A)
lemma eG {α:Type} {r p:α->α->Prop} (h:∀ a b,r a b->p a b) {a b:α} (c:Relation.ReflTransGen r a b):Relation.ReflTransGen p a b:=by
 induction c with
 | refl=>exact Relation.ReflTransGen.refl
 | tail _ d ih=>exact Relation.ReflTransGen.tail ih (h _ _ d)
section SemCore
variable {n : ℕ} {G H : Fin n → Fin n → Prop} {D : Dag}
lemma dd (v:Fin n) (x:Fin n->_d):∀ k,k≠v->x k=bB v x k:=by
 intro k a;simp[bB,a]
lemma dm (v:Fin n) (x:Fin n->_d):bB v x v=true:=by simp[bB]
lemma iE (v:Fin n) (x:Fin n->_d):∀ i,x i=true->bB v x i=true:=by
 intro i a;simp[bB,a]
lemma m7 {x:Fin n->_d} {u:Fin n} (b:x u=true):∀ i,cl u i=true->x i=true:=by
 intro i a;simp only[cl,decide_eq_true_eq] at a;rw[a];exact b
lemma cO (a:au n D) {u:Fin n} {w:ℕ} (b:u∈ag n D w) {x:Fin n->_d} (c:x u=true):val D x w=true:=gJ a (cl u) x (m7 c) w (ee.mp b)
lemma cP {v:Fin n} {w:ℕ} (a:v∈ag n D w):w<n+D.length:=by
 by_contra b;rw[pc D w (by omega)] at a;exact notMem_empty v a
lemma cB (a:au n D) {j:ℕ} (b:j<D.length) (c:cR D j=true):ag n D (n+j)=ag n D (cj D j)∩ag n D (ck D j):=by
 rw[fY a j b];simp[c]
lemma de (a:au n D) {j:ℕ} (b:j<D.length) (c:cR D j=false):ag n D (n+j)=ag n D (cj D j)∪ag n D (ck D j):=by
 rw[fY a j b];simp[c]
lemma cr (a:au n D) {j:ℕ} (b:j<D.length) (c:cR D j=true) (s:_d):ag n D (n+j)⊆ag n D (aw D (j,s)):=by
 rw[cB a b c];cases s;{rw[aX];exact inter_subset_left};{rw[bh];exact inter_subset_right}
lemma dh (a:au n D) {j:ℕ} (b:j<D.length) (s:_d):aw D (j,s)<n+j:=by
 obtain⟨c,d,-⟩:=a j b;cases s;{rw[aX];exact c};{rw[bh];exact d}
lemma pd (b:au n D) {j:ℕ} (c:j<D.length) (s:_d):aw D (j,s)≠aw D (j,!s):=by
 obtain⟨-,-,a⟩:=b j c;cases s;{simpa[aw] using a};{simpa[aw] using a.symm}
lemma cM {j:ℕ} (a:j<D.length) (s:_d):bk n D (aw D (j,s)) (n+j):=by
 refine⟨by omega,by omega,?_⟩;rw[Nat.add_sub_cancel_left];cases s;{exact Or.inl (aX j).symm};{exact Or.inr (bh j).symm}
lemma fj {a b:ℕ}:bk n D a b↔ ∃ j s,j<D.length/\b=n+j/\aw D (j,s)=a:=by
 constructor
 · rintro⟨d,e,c|c⟩
   · exact⟨b - n,false,by omega,by omega,by rw[aX];exact c⟩
   · exact⟨b - n,true,by omega,by omega,by rw[bh];exact c⟩
 · rintro⟨j,s,f,rfl,rfl⟩
   refine⟨by omega,by omega,?_⟩;rw[Nat.add_sub_cancel_left];cases s;{exact Or.inl (aX j).symm};{exact Or.inr (bh j).symm}
lemma jv (c:au n D) {a b:ℕ} (h:bk n D a b):a<b:=by
 obtain⟨d,e,f⟩:=h;have:=c (b - n) (by omega);omega
lemma dR {a c:ℕ} (h:bk n D a c):c - n∈bV D a:=by
 unfold bV;rw[_mf,mem_range];exact⟨by have:=h.1;have:=h.2.1;omega,h.2.2⟩
lemma ef {a c:ℕ} (h:bk n D a c):1<=aF D a:=
 _cp.mpr ⟨_,dR h⟩
lemma dS {a c c':ℕ} (b:bk n D a c) (d:bk n D a c') (e:aF D a=1):c=c':=by
 have f:=dR b;have g:=dR d;obtain⟨r,h⟩:=_c1.mp (show(bV D a).card=1 from e);rw[h,_ms] at f g;have:=b.2.1;have:=d.2.1;omega
lemma d_ (e:au n D) (x y:Fin n->_d) (v:Fin n) (f:∀ k,k≠v->x k=y k) (w:ℕ) (c:val D x w≠val D y w):Relation.ReflTransGen (fun a b=>bk n D a b/\val D x b≠val D y b) v.val w:=by
 induction w using Nat.strong_induction_on with
 | _ w ih=>
  by_cases g:w<n
  · rw[bY D x w g,bY D y w g] at c
    have h:(⟨w,g⟩:Fin n)=v:=by{by_contra q;exact c (f _ q)};rw[<- h]
  · by_cases d:w<n+D.length
    · obtain⟨j,rfl⟩:∃ j,w=n+j:=⟨w - n,by omega⟩
      have i:j<D.length:=by omega
      obtain⟨r,s,-⟩:=e j i;have m:=c;rw[cS e x j i,cS e y j i] at m;by_cases p:val D x (cj D j)=val D y (cj D j)
      · have l:val D x (ck D j)≠val D y (ck D j):=by
         intro l;apply m;rw[p,l]
        exact Relation.ReflTransGen.tail (ih _ s l) ⟨⟨d,by omega,Or.inr (by rw[Nat.add_sub_cancel_left])⟩,c⟩
      · exact Relation.ReflTransGen.tail (ih _ r p) ⟨⟨d,by omega,Or.inl (by rw[Nat.add_sub_cancel_left])⟩,c⟩
    · exfalso;apply c;rw[fs D x w (by omega),fs D y w (by omega)]
def j_ (n:ℕ) (D:Dag) (b v:ℕ):Prop:=b=v\/¬ Relation.ReflTransGen (fun a c=>bk n D a c/\c≠b) v (bH n D)
lemma mw (l:au n D) (x y:Fin n->_d) (v:Fin n) (e:∀ k,k≠v->x k=y k) (b:ℕ) (d:j_ n D b v.val) (i:val D x b=val D y b):val D x (bH n D)=val D y (bH n D):=by
 by_contra f;rcases d with rfl|d
 · rw[bY D x _ v.isLt,bY D y _ v.isLt] at i
   have g:x=y:=by{funext k;by_cases j:k=v;{rw[j];exact i};{exact e k j}};exact f (by rw[g])
 · exact d (eG (fun a c h=>⟨h.1,fun m=>h.2 (by rw[m];exact i)⟩) (d_ l x y v e _ f))
def bz (n:ℕ) (D:Dag) (a b:ℕ):Prop:=Relation.ReflTransGen (fun a c=>bk n D a c/\aF D a=1) a b
lemma ds (k:au n D) {v b:ℕ} (h:bz n D v b):j_ n D b v:=by
 induction h using Relation.ReflTransGen.head_induction_on with
 | refl=>exact Or.inl rfl
 | @head a c d _ ih=>
  by_cases f:b=a;{exact Or.inl f}
  · right
    intro l;rcases Relation.ReflTransGen.cases_head l with g|⟨c',j,e⟩
    · have m:=d0 k a (by rw[g];unfold bH;omega)
      have p:=d.2;omega
    · have i:c=c':=dS d.1 j.1 d.2
      subst i;rcases ih with rfl|ih;{exact j.2 rfl};{exact ih e}
lemma fy (i:au n D) (v:Fin n):∀ w,v∈ag n D w ->(∀ u,u<w->v∈ag n D u->aF D u<=1)->bz n D v.val w:=by
 intro w;induction w using Nat.strong_induction_on with
 | _ w ih=>
  intro d b;by_cases k:w<n
  · have l:ag n D w={⟨w,k⟩}:=dr D ⟨w,k⟩
    rw[l,_ms] at d;rw[d];exact Relation.ReflTransGen.refl
  · have m:=cP d
    obtain⟨j,rfl⟩:∃ j,w=n+j:=⟨w - n,by omega⟩;have h:j<D.length:=by omega
    have e:∀ s:_d,v∈ag n D (aw D (j,s))->bz n D v.val (n+j):=by{intro s f;have a:bk n D (aw D (j,s)) (n+j):=cM h s;have m':=dh i h s;have g:=ef a;have p:=b _ m' f;exact Relation.ReflTransGen.tail (ih _ m' f (fun u q=>b u (by omega))) ⟨a,by omega⟩};rw[fY i j h] at d;split_ifs at d with r;{exact e false (by rw[aX];exact(_mn.mp d).1)}
    · rcases _mu.mp d with g|g
      · exact e false (by rw[aX];exact g)
      · exact e true (by rw[bh];exact g)
lemma dF (f:bJ G) (v:Fin n):¬ cN G (cl v):=by
 rintro⟨a,c,b,d,e⟩;simp only[cl,decide_eq_true_eq] at d e;rw[d,e] at b;exact f.2.1 _ b
lemma nQ {u v:Fin n} (a:G u v):cN G (b4 u v):=⟨u,v,a,by simp[b4],by simp[b4]⟩
lemma cs (c:bJ G) (a:sem_Umbrella n G H D):ag n D (bH n D)=∅:=eq_empty_iff_forall_notMem.2 (fun v b=>dF a.1 v (a.2.2.2.1 _ (ee.1 b)))
lemma fk (r:bJ G) (e:au n D) (k:sem_Umbrella n G H D) (v:Fin n) (b:ℕ) (a:j_ n D b v.val):ag n D b⊆{v}:=by
 intro u l;rw[_ms];by_contra f;obtain⟨m,p,c,-⟩:=r;obtain⟨z,g,h⟩:=c v u (Ne.symm f);have i:val D (b4 u z) b=true:=cO e l (by simp[b4]);have j:val D (bB v (b4 u z)) b=true:=cO e l (by simp[bB,b4]);have d:=mw e _ _ v (dd v (b4 u z)) b a (by rw[i,j]);have s:cN G (bB v (b4 u z)):=⟨v,z,g,dm v _,by simp[bB,b4]⟩;have q:=k.2.2.1 _ s;rw[<- d,k.2.2.2.2 u z h] at q;exact _fnt q
lemma lk (g:bJ G) (d:au n D) (h:sem_Umbrella n G H D) (v:Fin n) (i:v∈al n D):∃ b,2<=aF D b/\ag n D b={v}/\bz n D v.val b:=by
 classical
 have a:∃ w,2<=aF D w/\v∈ag n D w:=eX.mp i;obtain⟨j,f⟩:=Nat.find_spec a
 have c:bz n D v.val (Nat.find a):=fy d v _ f (fun u k e=>by
  have:=Nat.find_min a k;by_contra l
  exact this ⟨by omega,e⟩)
 exact⟨Nat.find a,j,Subset.antisymm (fk g d h v _ (ds d c)) (singleton_subset_iff.mpr f),c⟩
def jf (n:ℕ) (D:Dag) (b:Fin n->ℕ):Prop:=∀ v∈al n D,2<=aF D (b v)/\ag n D (b v)={v}/\bz n D v.val (b v)
lemma jg (d:bJ G) (e:au n D) (f:sem_Umbrella n G H D):∃ b:Fin n->ℕ,jf n D b:=by
 classical
 have h:∀ v:Fin n,∃ b,v∈al n D ->2<=aF D b/\ag n D b={v}/\bz n D v.val b:=by
  intro v;by_cases a:v∈al n D
  · obtain⟨b,c⟩:=lk d e f v a
    exact⟨b,fun _=>c⟩
  · exact⟨0,fun h=>absurd h a⟩
 choose b c using h;exact⟨b,fun v a=>c v a⟩
lemma jU {b:Fin n->ℕ} (a:jf n D b):aM n D b:=fun v c=>⟨(a v c).1,(a v c).2.1⟩
lemma dK (a:bJ G) (c:au n D) (d:sem_Umbrella n G H D):∃ b:Fin n->ℕ,aM n D b:=by
 obtain⟨b,e⟩:=jg a c d;exact⟨b,jU e⟩
lemma aN {v:Fin n}:v∈aa n D↔v∉al n D:=by
 simp[aa]
lemma iF (a:au n D) {v:Fin n} (b:v∈aa n D) {w:ℕ} (c:v∈ag n D w):bz n D v.val w:=fy a v w c (fun u _ d=>fG.mp b u d)
lemma jh (c:bJ G) (a:au n D) (d:sem_Umbrella n G H D) {v:Fin n} (e:v∈aa n D) {w:ℕ} (b:v∈ag n D w):ag n D w={v}:=Subset.antisymm (fk c a d v w (ds a (iF a e b))) (singleton_subset_iff.mpr b)
lemma b7 {v:Fin n} {w:ℕ}:w∈ao n D {v}↔v∈ag n D w:=by
 simp only[ao,_mf,mem_range];constructor
 · rintro⟨-,u,a⟩
   rw[_mn,_ms] at a;exact a.2▸a.1
 · intro h
   exact⟨cP h,v,_mn.mpr ⟨h,_mss v⟩⟩
lemma df {v:Fin n} {e:ℕ×_d}:e∈aE n D (ao n D {v})↔ e.1<D.length/\v∈ag n D (aw D e)/\v∉ag n D (n+e.1):=by
 simp only[aE,eK,_mf,mem_product,mem_range,
  _mv,and_true,b7]
lemma kG {v:Fin n} (a:v∈aa n D):bn D (ao n D {v})=0:=by
 unfold bn;refine sum_eq_zero (fun w b=>?_);have:=fG.mp a w (b7.mp b);omega
lemma eq (I:bJ G) (y:au n D) (B:sem_Umbrella n G H D) {u v:Fin n} (C:G u v):∃ j,j<D.length/\cR D j=true/\val D (b4 u v) (n+j)=true /\u∉ag n D (n+j)/\v∉ag n D (n+j) /\∃ s:_d,u∈ag n D (aw D (j,s))/\v∉ag n D (aw D (j,s)) /\v∈ag n D (aw D (j,!s))/\u∉ag n D (aw D (j,!s)):=by
 classical
 have g:∃ w,val D (b4 u v) w=true/\u∉ag n D w/\v∉ag n D w:=⟨bH n D,B.2.2.1 _ (nQ C),by rw[cs I B];simp,by rw[cs I B];simp⟩;obtain⟨b,c,d⟩:=Nat.find_spec g;have e:∀ a,a<Nat.find g->val D (b4 u v) a=true ->u∈ag n D a\/v∈ag n D a:=by{intro a z E;by_contra l;rw[not_or] at l;exact Nat.find_min g z ⟨E,l.1,l.2⟩};generalize Nat.find g=w at b c d e;have J:w<n+D.length:=by{by_contra l;rw[fs D _ w (by omega)] at b;exact _fnt b};have L:n<=w:=by
  by_contra l;have l':w<n:=by omega
  rw[bY D _ w l'] at b;have K:ag n D w={⟨w,l'⟩}:=dr D ⟨w,l'⟩;rw[K,_ms] at c d;simp only[b4,Bool.or_eq_true,decide_eq_true_eq] at b;rcases b with h|h;{exact c h.symm};{exact d h.symm}
 obtain⟨j,rfl⟩:∃ j,w=n+j:=⟨w - n,by omega⟩;have m:j<D.length:=by omega
 obtain⟨z,F,-⟩:=y j m;have p:=b;rw[cS y _ j m] at b;rw[fY y j m] at c d;cases A:cR D j
 · exfalso
   rw[A] at b c d;simp only[gop_false,Bool.or_eq_true] at b;simp only[Bool.false_eq_true,ite_false,_mu,not_or] at c d;rcases b with h|h
   · rcases e _ z h with h'|h'
     · exact c.1 h'
     · exact d.1 h'
   · rcases e _ F h with h'|h'
     · exact c.2 h'
     · exact d.2 h'
 · rw[A] at b c d
   simp only[gop_true,Bool.and_eq_true] at b;simp only[ite_true,_mn,not_and] at c d;have f:u∉ag n D (n+j)/\v∉ag n D (n+j):=by{rw[cB y m A];simp only[_mn,not_and];exact⟨c,d⟩};refine⟨j,m,A,p,f.1,f.2,?_⟩;rcases e _ z b.1 with q|q
   · have r:u∉ag n D (ck D j):=c q
     have t:v∈ag n D (ck D j):=(e _ F b.2).resolve_left r;exact⟨false,by simpa[aw] using q,by simpa[aw] using fun h=>d h t,by simpa[aw] using t,by simpa[aw] using r⟩
   · have r:v∉ag n D (ck D j):=d q
     have x:u∈ag n D (ck D j):=(e _ F b.2).resolve_right r;exact⟨true,by simpa[aw] using x,by simpa[aw] using r,by simpa[aw] using q,by simpa[aw] using fun h=>c h x⟩
lemma ci (r:bJ G) (h:ai n D) (t:sem_Umbrella n G H D) {v:Fin n} (B:v∈aa n D):∃ e:ℕ×_d,e.1<D.length/\cR D e.1=true/\ag n D (aw D e)={v} /\ag n D (n+e.1)=∅/\(∀ a,G v a->a∈ag n D (aw D (e.1,!e.2))) /\aE n D (ao n D {v})={e}/\aW n D (ao n D {v})=∅:=by
 have u:=h.1;have w:=co h {v} (by rw[cs r t];simp);rw[kG B,_cs] at w;have b:∀ a,G v a->∃ j s,j<D.length/\cR D j=true /\(j,s)∈aE n D (ao n D {v})/\a∈ag n D (aw D (j,!s)):=by{intro a d;obtain⟨j,C,F,-,y,-,s,I,-,J,-⟩:=eq r u t d;exact⟨j,s,C,F,df.mpr ⟨C,I,y⟩,J⟩};obtain⟨a0,z,-⟩:=r.2.2.2 v v;obtain⟨j0,s0,i,k,f,-⟩:=b a0 z;have g:(aE n D (ao n D {v})).card=1:=by{have:=_cp.mpr ⟨_,f⟩;omega};have l:aW n D (ao n D {v})=∅:=card_eq_zero.mp (by omega);obtain⟨e,m⟩:=_c1.mp g;rw[m,_ms] at f;subst f;have c:ag n D (aw D (j0,s0))={v}:=jh r u t B (df.mp (by rw[m];exact _mss _)).2.1;have p:v∉ag n D (n+j0):=(df.mp (by rw[m];exact _mss _)).2.2;refine⟨(j0,s0),i,k,c,?_,?_,m,l⟩
 · refine eq_empty_of_forall_notMem (fun x E=>?_)
   have q:=cr u i k s0 E;rw[c,_ms] at q;exact p (q▸E)
 · intro a d
   obtain⟨j,s,-,-,A,K⟩:=b a d;rw[m,_ms] at A;rw[Prod.mk.injEq] at A;obtain⟨rfl,rfl⟩:=A;exact K
lemma fu (b:bJ G) (h:ai n D) (c:sem_Umbrella n G H D) {u v:Fin n} (d:G u v):u∈al n D\/v∈al n D:=by
 by_contra e;rw[not_or] at e;obtain⟨eu,-,-,-,-,f,g,-⟩:=ci b h c (aN.mpr e.1);obtain⟨ev,-,-,i,-,-,k,-⟩:=ci b h c (aN.mpr e.2);obtain⟨j,r,-,-,l,m,s,y,-,z,-⟩:=eq b h.1 c d;have t:(j,s)∈aE n D (ao n D {u}):=df.mpr ⟨r,y,l⟩;have w:(j,!s)∈aE n D (ao n D {v}):=df.mpr ⟨r,z,m⟩;rw[g,_ms] at t;rw[k,_ms] at w;subst t;subst w;obtain⟨a,p,q⟩:=b.2.2.2 u v;have x:a∈ag n D (aw D (j,!s)):=f a p;rw[i,_ms] at x;exact q x
lemma lV {A:Finset (Fin n)} (g:∀ a∈A,∀ b∈A,¬ G a b):¬ cN G (bM A):=by
 rintro⟨a,c,d,e,f⟩;simp only[bM,decide_eq_true_eq] at e f;exact g a e c f d
lemma gO (I:bJ G) (g:au n D) (E:sem_Umbrella n G H D) (A:Finset (Fin n)) (v:val D (bM A) (bH n D)=false) (x:Fin n) (y:∃ a∈A,G x a):∃ j s,j<D.length/\cR D j=true/\x∈ag n D (aw D (j,s)) /\x∉ag n D (n+j)/\Disjoint (ag n D (aw D (j,s))) A:=by
 by_contra i;have c:∀ j s,j<D.length->cR D j=true->x∈ag n D (aw D (j,s)) ->x∉ag n D (n+j)->val D (bM A) (aw D (j,s))=true /\val D (bB x (bM A)) (aw D (j,s))=true:=by{intro j s d h e z;have k:¬ Disjoint (ag n D (aw D (j,s))) A:=fun J=>i ⟨j,s,d,h,e,z,J⟩;rw[not_disjoint_iff] at k;obtain⟨a,l,m⟩:=k;exact⟨cO g l (by simp[bM,m]),cO g l (by simp[bB,bM,m])⟩};have B:∀ w,x∉ag n D w->val D (bM A) w=val D (bB x (bM A)) w:=by
  intro w;induction w using Nat.strong_induction_on with
  | _ w ih=>
   intro f;by_cases u:w<n
   · rw[bY D _ w u,bY D _ w u]
     have K:ag n D w={⟨w,u⟩}:=dr D ⟨w,u⟩;rw[K,_ms] at f;exact dd x _ _ (fun L=>f L.symm)
   · by_cases M:w<n+D.length
     · obtain⟨j,rfl⟩:∃ j,w=n+j:=⟨w - n,by omega⟩
       have d:j<D.length:=by omega
       obtain⟨p,C,-⟩:=g j d;rw[cS g _ j d,cS g _ j d];cases h:cR D j
       · rw[de g d h,_mu,not_or] at f
         rw[ih _ p f.1,ih _ C f.2]
       · have q:=f
         rw[cB g d h,_mn,not_and] at q;by_cases b:x∈ag n D (cj D j)
         · have e:=c j false d h (by rw[aX];exact b) f
           rw[aX] at e;rw[ih _ C (q b),e.1,e.2]
         · by_cases r:x∈ag n D (ck D j)
           · have e:=c j true d h (by rw[bh];exact r) f
             rw[bh] at e;rw[ih _ p b,e.1,e.2]
           · rw[ih _ p b,ih _ C r]
     · rw[fs D _ w (by omega),fs D _ w (by omega)]
 have t:=B (bH n D) (by rw[cs I E];exact notMem_empty x);obtain⟨a,p,b⟩:=y;have z:cN G (bB x (bM A)):=⟨x,a,b,dm x _,by simp[bB,bM,p]⟩;have F:=E.2.2.1 _ z;rw[<- t,v] at F;exact _fnt F
lemma fm (f:bJ G) (g:au n D) (e:sem_Umbrella n G H D) (A:Finset (Fin n)) (h:∀ a∈A,∀ b∈A,¬ H a b) (x:Fin n) (d:∃ a∈A,G x a):∃ j s,j<D.length/\cR D j=true/\x∈ag n D (aw D (j,s)) /\x∉ag n D (n+j)/\Disjoint (ag n D (aw D (j,s))) A:=by
 refine gO f g e A ?_ x d;by_contra c;rw[_nf] at c;exact lV h (e.2.2.2.1 _ c)
lemma gP (f:bJ G) (g:au n D) (e:sem_Umbrella n G H D) {a z x:Fin n} (c:¬ G a z) (d:G x z):∃ j s,j<D.length/\cR D j=true/\x∈ag n D (aw D (j,s)) /\x∉ag n D (n+j)/\Disjoint (ag n D (aw D (j,s))) {a,z}:=by
 refine gO f g e {a,z} ?_ x ⟨z,by simp,d⟩;have b:bM ({a,z}:Finset (Fin n))=b4 a z:=by{ext i;simp[bM,b4]};rw[b];exact e.2.2.2.2 a z c
lemma ew (q:au n D) (T M:Finset (Fin n)) (G:2<=M.card) (w:ℕ) (z:ag n D w∩T=M):∃ j,j<D.length/\n+j<=w/\ag n D (n+j)∩T=M /\j∈aW n D (ao n D T)/\(∀ u,u<n+j->ag n D u∩T≠M) /\((cR D j=true/\M ⊂ ag n D (cj D j)∩T/\M ⊂ ag n D (ck D j)∩T) \/(cR D j=false/\ag n D (cj D j)∩T ⊂ M/\ag n D (ck D j)∩T ⊂ M /\(ag n D (cj D j)∩T)∪(ag n D (ck D j)∩T)=M /\(ag n D (cj D j)∩T).Nonempty/\(ag n D (ck D j)∩T).Nonempty)):=by
 classical
 have d:∃ u,ag n D u∩T=M:=⟨w,z⟩;have r:Nat.find d<=w:=Nat.find_min' d z;have c:∀ u,u<Nat.find d->ag n D u∩T≠M:=fun u y=>Nat.find_min d y;have a:=Nat.find_spec d;generalize Nat.find d=f at r c a;have e:M.Nonempty:=_cp.mp (by omega);have g:∀ {u:ℕ},(ag n D u∩T).Nonempty->u∈ao n D T:=by{intro u y;obtain⟨v,b⟩:=y;exact _mf.mpr ⟨mem_range.mpr (cP (_mn.mp b).1),v,b⟩};have A:f<n+D.length:=by{obtain⟨v,b⟩:=e;rw[<- a] at b;exact cP (_mn.mp b).1};have B:n<=f:=by
  by_contra H;have H':f<n:=by omega
  have C:ag n D f={⟨f,H'⟩}:=dr D ⟨f,H'⟩;have I:M.card<=1:=by{rw[<- a,C];exact(_cl inter_subset_left).trans (by simp)};omega
 obtain⟨j,rfl⟩:∃ j,f=n+j:=⟨f - n,by omega⟩;have k:j<D.length:=by omega
 obtain⟨E,F,-⟩:=q j k;have h:=c _ E;have i:=c _ F;refine⟨j,k,r,a,?_,c,?_⟩
 · have t:(ag n D (cj D j)∩T).Nonempty/\(ag n D (ck D j)∩T).Nonempty:=by
    cases x:cR D j
    · rw[de q k x,union_inter_distrib_right] at a
      constructor
      · rw[nonempty_iff_ne_empty]
        intro l;rw[l,empty_union] at a;exact i a
      · rw[nonempty_iff_ne_empty]
        intro l;rw[l,union_empty] at a;exact h a
    · rw[cB q k x] at a
      obtain⟨v,b⟩:=e;rw[<- a] at b;simp only[_mn] at b;exact⟨⟨v,_mn.mpr ⟨b.1.1,b.2⟩⟩,⟨v,_mn.mpr ⟨b.1.2,b.2⟩⟩⟩
   rw[aW,_mf,mem_range];exact⟨k,g (by rw[a];exact e),g t.1,g t.2⟩
 · cases x:cR D j
   · right
     rw[de q k x,union_inter_distrib_right] at a;have m:ag n D (cj D j)∩T⊆M:=by rw[<- a];exact subset_union_left
     have p:ag n D (ck D j)∩T⊆M:=by rw[<- a];exact subset_union_right
     refine⟨rfl,Finset.ssubset_iff_subset_ne.mpr ⟨m,h⟩,Finset.ssubset_iff_subset_ne.mpr ⟨p,i⟩,a,?_,?_⟩
     · rw[nonempty_iff_ne_empty]
       intro l;rw[l,empty_union] at a;exact i a
     · rw[nonempty_iff_ne_empty]
       intro l;rw[l,union_empty] at a;exact h a
   · left
     rw[cB q k x] at a;have m:M⊆ag n D (cj D j)∩T:=by{rw[<- a];intro v b;simp only[_mn] at b⊢;exact⟨b.1.1,b.2⟩};have p:M⊆ag n D (ck D j)∩T:=by{rw[<- a];intro v b;simp only[_mn] at b⊢;exact⟨b.1.2,b.2⟩};exact⟨rfl,Finset.ssubset_iff_subset_ne.mpr ⟨m,Ne.symm h⟩,Finset.ssubset_iff_subset_ne.mpr ⟨p,Ne.symm i⟩⟩
end SemCore
def af (n:ℕ) (D:Dag) (x:Fin n):Finset (ℕ×_d):=aE n D (ao n D {x})
def am (e:ℕ×_d):ℕ×_d:=(e.1,!e.2)
section SemCodes
variable {n : ℕ} {G H : Fin n → Fin n → Prop} {D : Dag}
lemma ak {x:Fin n} {e:ℕ×_d}:e∈af n D x↔ e.1<D.length/\x∈ag n D (aw D e)/\x∉ag n D (n+e.1):=df
lemma aB (e:ℕ×_d):am (am e)=e:=by simp[am]
lemma ka {e f:ℕ×_d} (h:e.1=f.1):f=e\/f=am e:=by
 obtain⟨j,s⟩:=e;obtain⟨k,t⟩:=f;simp only at h;subst h;cases s <;> cases t <;> simp[am]
lemma cY (c:au n D) {x:Fin n} {e:ℕ×_d} (d:e∈af n D x):cR D e.1=true:=by
 obtain⟨f,a,g⟩:=ak.mp d;by_contra b;rw[Bool.not_eq_true] at b;apply g;rw[de c f b,_mu];obtain⟨j,s⟩:=e;cases s;{left;simpa[aw] using a};{right;simpa[aw] using a}
lemma m9 (a:bJ G) (h:ai n D) (b:sem_Umbrella n G H D) (x:Fin n):(af n D x).card+(aW n D (ao n D {x})).card =1+bn D (ao n D {x}):=by
 have c:=co h {x} (by rw[cs a b];simp);rwa[_cs] at c
lemma cg (g:bJ G) (h:au n D) (i:sem_Umbrella n G H D) {x y:Fin n} (b:G x y):∃ e,e∈af n D x/\am e∈af n D y /\y∉ag n D (aw D e)/\x∉ag n D (aw D (am e)) /\val D (b4 x y) (n+e.1)=true:=by
 obtain⟨j,f,-,a,c,d,s,k,l,m,p⟩:=eq g h i b;exact⟨(j,s),ak.mpr ⟨f,k,c⟩,ak.mpr ⟨f,m,d⟩,l,p,a⟩
lemma jJ (r:bJ G) (t:au n D) (m:sem_Umbrella n G H D) {x a b y:Fin n} (i:¬ H a b) (p:G x y) (k:¬ H y a) (l:¬ H y b):∃ e,e∈af n D x/\a∉ag n D (aw D e)/\b∉ag n D (aw D e):=by
 have c:=m.1.1;have d:=m.1.2.1;have w:∀ u∈({a,b,y}:Finset (Fin n)),∀ v∈({a,b,y}:Finset (Fin n)),¬ H u v:=by{intro u f v g;simp only[_mi,_ms] at f g;rcases f with f|f|f <;> rcases g with g|g|g <;> rw[f,g];{exact d a};{exact i};{exact fun h=>k (c _ _ h)};{exact fun h=>i (c _ _ h)};{exact d b};{exact fun h=>l (c _ _ h)};{exact k};{exact l};{exact d y}};obtain⟨j,s,z,-,A,B,q⟩:=fm r t m {a,b,y} w x ⟨y,by simp,p⟩;exact⟨(j,s),ak.mpr ⟨z,A,B⟩,fun h=>_dl.mp q h (by simp),fun h=>_dl.mp q h (by simp)⟩
lemma kb (f:bJ G) (g:au n D) (i:sem_Umbrella n G H D) {x a:Fin n} (b:x≠a):∃ e,e∈af n D x/\a∉ag n D (aw D e):=by
 obtain⟨z,c,d⟩:=f.2.2.1 x a b;obtain⟨j,s,k,-,l,m,p⟩:=gP f g i d c;exact⟨(j,s),ak.mpr ⟨k,l,m⟩,fun h=>_dl.mp p h (by simp)⟩
end SemCodes
lemma gq {α:Type} {R:α->α->Prop} (e:∀ a a' b,R a b->R a' b->a=a') {u v c:α} (m:Relation.ReflTransGen R u c) (l:Relation.ReflTransGen R v c):Relation.ReflTransGen R u v\/Relation.ReflTransGen R v u:=by
 induction m with
 | refl=>exact Or.inr l
 | tail i f ih=>
  rcases Relation.ReflTransGen.cases_tail l with h|⟨b',hvb',g⟩
  · left
    rw[<- h];exact Relation.ReflTransGen.tail i f
  · have j:b'=_:=e _ _ _ g f
    rw[j] at hvb';exact ih hvb'
def cU (n:ℕ) (D:Dag) (b:Fin n->ℕ):Prop:=∀ v∈al n D,2<=aF D (b v)/\ag n D (b v)={v}/\bz n D v.val (b v) /\∀ w,2<=aF D w->v∈ag n D w->b v<=w
def ex (n:ℕ) (D:Dag) (X:Finset (Fin n)) (a b:ℕ):Prop:=bk n D a b/\aF D a=1/\∀ x∈X,x∈ag n D a/\x∈ag n D b
section SemArms
variable {n : ℕ} {G H : Fin n → Fin n → Prop} {D : Dag}
lemma dt (d:au n D) {R:ℕ->ℕ->Prop} (e:∀ a b,R a b->bk n D a b) {a b:ℕ} (h:Relation.ReflTransGen R a b):a<=b:=by
 induction h with
 | refl=>exact le_refl _
 | tail _ c ih=>exact le_trans ih (le_of_lt (jv d (e _ _ c)))
lemma b_ (k:bJ G) (e:au n D) (l:sem_Umbrella n G H D):∃ b:Fin n->ℕ,cU n D b:=by
 classical
 have h:∀ v:Fin n,∃ b,v∈al n D ->2<=aF D b/\ag n D b={v}/\bz n D v.val b /\∀ w,2<=aF D w->v∈ag n D w->b<=w:=by
  intro v;by_cases d:v∈al n D
  · have a:∃ w,2<=aF D w/\v∈ag n D w:=eX.mp d
    obtain⟨m,j⟩:=Nat.find_spec a
    have c:bz n D v.val (Nat.find a):=fy e v _ j (fun u p f=>by
     have:=Nat.find_min a p;by_contra r
     exact this ⟨by omega,f⟩)
    exact⟨Nat.find a,fun _=>⟨m,Subset.antisymm (fk k e l v _ (ds e c)) (singleton_subset_iff.mpr j),c,fun w g i=>Nat.find_min' a ⟨g,i⟩⟩⟩
  · exact⟨0,fun h=>absurd h d⟩
 choose b q using h;exact⟨b,fun v d=>q v d⟩
lemma bD {b:Fin n->ℕ} (a:cU n D b):aM n D b:=fun v c=>⟨(a v c).1,(a v c).2.1⟩
lemma dL (g:au n D) {x:Fin n} (h:aW n D (ao n D {x})=∅) {j:ℕ} (c:j<D.length) (b:x∈ag n D (n+j)):cR D j=false/\¬ (x∈ag n D (cj D j)/\x∈ag n D (ck D j)):=by
 have a:¬ (x∈ag n D (cj D j)/\x∈ag n D (ck D j)):=by{intro d;have e:j∈aW n D (ao n D {x}):=by{rw[aW,_mf,mem_range];exact⟨c,b7.mpr b,b7.mpr d.1,b7.mpr d.2⟩};rw[h] at e;exact notMem_empty _ e};refine⟨?_,a⟩;by_contra f;rw[_nf] at f;rw[cB g c f,_mn] at b;exact a b
lemma ez (c:bJ G) (h:ai n D) (d:sem_Umbrella n G H D) (b:Fin n->ℕ) (e:aM n D b) (x:Fin n):(af n D x).card+(aW n D (ao n D {x})).card =1+(({x}:Finset (Fin n))∩al n D).card + ((aj n D b).filter (fun u=>x∈ag n D u.1)).card:=by
 have j:=m9 c h d x;have f:=d9 h.1 b e {x};have g:(aj n D b).filter (fun u=>(ag n D u.1∩{x}).Nonempty)=(aj n D b).filter (fun u=>x∈ag n D u.1):=by
  refine filter_congr (fun u _=>?_);constructor
  · rintro⟨y,a⟩
    rw[_mn,_ms] at a;exact a.2▸a.1
  · intro i
    exact⟨x,_mn.mpr ⟨i,_mss x⟩⟩
 rw[g] at f;omega
lemma lm (F:bJ G) (h:ai n D) (I:sem_Umbrella n G H D) (X:Finset (Fin n)) (J:X.Nonempty) (K:∀ x∈X,aW n D (ao n D {x})=∅):∀ c,(∀ x∈X,x∈ag n D c) ->(∀ x∈X,∀ w,c<=w->x∈ag n D w->aF D w<=1) ->∃ e:ℕ×_d,(∀ x∈X,e∈af n D x) /\Relation.ReflTransGen (ex n D X) c (aw D e):=by
 classical
 have y:=h.1;obtain⟨x0,b⟩:=J;intro c;generalize Q:n+D.length - c=k;induction k using Nat.strong_induction_on generalizing c with
 | _ k ih=>
  intro i d;have E:=cP (i x0 b);have m:c≠bH n D:=by{intro L;have:=i x0 b;rw[L,cs F I] at this;exact notMem_empty _ this};have p:1<=aF D c:=h.2.1 c (by unfold bH at m;omega);have M:aF D c=1:=le_antisymm (d x0 b c (le_refl c) (i x0 b)) p;obtain⟨j,q⟩:=_cp.mp p;simp only[bV,_mf,mem_range] at q;obtain⟨r,t⟩:=q;obtain⟨s,v⟩:∃ s:_d,aw D (j,s)=c:=by{rcases t with l|l;{exact⟨false,by rw[aX];exact l⟩};{exact⟨true,by rw[bh];exact l⟩}};have N:c<n+j:=v▸dh y r s;by_cases f:∃ x1∈X,x1∈ag n D (n+j)
  · obtain⟨x1,z,u⟩:=f
    have P:=(dL y (K x1 z) r u).1;have g:∀ x∈X,x∈ag n D (n+j):=by{intro x a;rw[de y r P,_mu];rcases t with l|l;{left;rw[l];exact i x a};{right;rw[l];exact i x a}};obtain⟨e,A,B⟩:=ih (n+D.length - (n+j)) (by omega) (n+j) rfl g (fun x a w R=>d x a w (by omega));refine⟨e,A,Relation.ReflTransGen.head ⟨?_,M,fun x a=>⟨i x a,g x a⟩⟩ B⟩;rw[<- v];exact cM r s
  · refine⟨(j,s),fun x a=>ak.mpr ⟨r,?_,fun C=>f ⟨x,a,C⟩⟩,?_⟩
    · rw[v];exact i x a
    · rw[v]
lemma kP (hG:bJ G) (h:ai n D) (hC:sem_Umbrella n G H D) (X:Finset (Fin n)) (hX:X.Nonempty) (hM:∀ x∈X,aW n D (ao n D {x})=∅) (r:ℕ) (hr:∀ x∈X,x∈ag n D r) (hf:2<=aF D r) (M:∀ x∈X,∀ w,r<w->x∈ag n D w->aF D w<=1):∃ P Q:ℕ×_d,P.1≠Q.1/\∀ x∈X,P∈af n D x/\Q∈af n D x:=by
 classical
 have l:=h.1;obtain⟨x0,c⟩:=hX;obtain⟨j1,p,j2,q,y⟩:=one_lt_card.mp (show 1<(bV D r).card from hf);have d:∀ j∈bV D r,j<D.length/\r<n+j/\(cj D j=r\/ck D j=r):=by{intro j L;simp only[bV,_mf,mem_range] at L;have:=l j L.1;exact⟨L.1,by omega,L.2⟩};have k:∀ j∈bV D r,∃ e:ℕ×_d,(∀ x∈X,e∈af n D x) /\((e.1=j/\aw D e=r)\/Relation.ReflTransGen (ex n D X) (n+j) (aw D e)):=by
  intro j L;obtain⟨z,hrj,N⟩:=d j L;obtain⟨s,hs⟩:∃ s:_d,aw D (j,s)=r:=by{rcases N with f|f;{exact⟨false,by rw[aX];exact f⟩};{exact⟨true,by rw[bh];exact f⟩}};by_cases t:∃ x1∈X,x1∈ag n D (n+j)
  · obtain⟨x1,hx1,R⟩:=t
    have ht:=(dL l (hM x1 hx1) z R).1;have S:∀ x∈X,x∈ag n D (n+j):=by{intro x m;rw[de l z ht,_mu];rcases N with f|f;{left;rw[f];exact hr x m};{right;rw[f];exact hr x m}};obtain⟨e,he1,he2⟩:=lm hG h hC X ⟨x0,c⟩ hM (n+j) S (fun x m w hw=>M x m w (by omega));exact⟨e,he1,Or.inr he2⟩
  · exact⟨(j,s),fun x m=>ak.mpr ⟨z,by rw[hs];exact hr x m,fun hc2=>t ⟨x,m,hc2⟩⟩,Or.inl ⟨rfl,hs⟩⟩
 have g:∀ a b,ex n D X a b->bk n D a b:=fun _ _ A=>A.1;have T:∀ a a' b,ex n D X a b->ex n D X a' b->a=a':=by
  intro a a' b f h2;by_contra v;obtain⟨hb1,hb2,hba⟩:=f.1;obtain⟨-,-,hba'⟩:=h2.1;have B:b - n<D.length:=by omega
  have C:x0∈ag n D (n+(b - n)):=by{rw[Nat.add_sub_cancel' hb2];exact(f.2.2 x0 c).2};apply(dL l (hM x0 c) B C).2;have ha:=(f.2.2 x0 c).1;have ha':=(h2.2.2 x0 c).1;rcases hba with e1|e1 <;> rcases hba' with e2|e2;{exact absurd (e1.symm.trans e2) v};{rw[e1,e2];exact⟨ha,ha'⟩};{rw[e1,e2];exact⟨ha',ha⟩};{exact absurd (e1.symm.trans e2) v}
 have i:∀ ja∈bV D r,∀ jb∈bV D r,ja≠jb ->¬ Relation.ReflTransGen (ex n D X) (n+ja) (n+jb):=by
  intro ja hja jb B A hp;obtain⟨hjla,hrja,-⟩:=d ja hja;obtain⟨Y,hrjb,Z⟩:=d jb B;rcases Relation.ReflTransGen.cases_tail hp with heq|⟨u,hu1,E⟩;{exact A (by omega)}
  · have hle:=dt l g hu1
    have F:u=r:=by{by_contra F;obtain⟨-,-,h0⟩:=E.1;rw[Nat.add_sub_cancel_left] at h0;apply(dL l (hM x0 c) Y (E.2.2 x0 c).2).2;have hu:=(E.2.2 x0 c).1;have h3:=hr x0 c;rcases h0 with e1|e1 <;> rcases Z with e2|e2;{exact absurd (e1.symm.trans e2) F};{rw[e1,e2];exact⟨hu,h3⟩};{rw[e1,e2];exact⟨h3,hu⟩};{exact absurd (e1.symm.trans e2) F}};omega
 obtain⟨P,I,hP2⟩:=k j1 p;obtain⟨Q,h4,h5⟩:=k j2 q;refine⟨P,Q,fun hPQ=>?_,fun x m=>⟨I x m,h4 x m⟩⟩;have J:Q=P:=by
  rcases ka hPQ with f|f;{exact f}
  · exfalso
    obtain⟨hjP,h6,hnP⟩:=ak.mp (I x0 c);have K:=(ak.mp (h4 x0 c)).2.1;rw[f] at K;apply hnP;rw[cB l hjP (cY l (I x0 c)),_mn];obtain⟨j,s⟩:=P;cases s;{exact⟨by simpa[aw] using h6,by simpa[aw,am] using K⟩};{exact⟨by simpa[aw,am] using K,by simpa[aw] using h6⟩}
 rw[J] at h5;obtain⟨-,hrj1,-⟩:=d j1 p;obtain⟨-,hrj2,-⟩:=d j2 q;rcases hP2 with ⟨hPa,hPb⟩|h7 <;> rcases h5 with ⟨hQa,hQb⟩|h8;{exact y (hPa.symm.trans hQa)}
 · have:=dt l g h8
   omega
 · have:=dt l g h7
   omega
 · rcases gq T h7 h8 with f|f
   · exact i j1 p j2 q y f
   · exact i j2 q j1 p (Ne.symm y) f
lemma gQ (i:bJ G) (h:ai n D) (j:sem_Umbrella n G H D) (b:Fin n->ℕ) (k:aM n D b) {c:Σ _:ℕ,ℕ} (a:aj n D b={c}) {x:Fin n} (f:3<=(af n D x).card):(af n D x).card=3/\aW n D (ao n D {x})=∅/\x∈al n D /\x∈ag n D c.1:=by
 have g:=ez i h j b k x;have p:(({x}:Finset (Fin n))∩al n D).card<=1:=(_cl inter_subset_left).trans (by simp);have l:=_cfl (aj n D b) (fun u=>x∈ag n D u.1);rw[a,_cs] at l;rw[a] at g;refine⟨by omega,card_eq_zero.mp (by omega),?_,?_⟩
 · by_contra m
   have d:({x}:Finset (Fin n))∩al n D=∅:=by{rw[singleton_inter_of_notMem m]};rw[d,_ce] at g;omega
 · have d:0<(({c}:Finset (Σ _:ℕ,ℕ)).filter (fun u=>x∈ag n D u.1)).card:=by
    omega
   obtain⟨u,e⟩:=_cp.mp d;rw[_mf,_ms] at e;exact e.1▸e.2
lemma fW (s:bJ G) (h:ai n D) (t:sem_Umbrella n G H D) (b:Fin n->ℕ) (u:cU n D b) (C:bd n D=(al n D).card+1) (X:Finset (Fin n)) (F:X.Nonempty) (c:∀ x∈X,3<=(af n D x).card):∃ P Q:ℕ×_d,P.1≠Q.1/\∀ x∈X,P∈af n D x/\Q∈af n D x:=by
 have E:=h.1;have e:=bD u;have f:(aj n D b).card=1:=by{have:=bS E b e;omega};obtain⟨u0,a⟩:=_c1.mp f;have y:u0∈aj n D b:=by rw[a];exact _mss _
 have i:u0∈dq n D:=(_mf.mp (_md.mp y).1).1;have j:2<=aF D u0.1:=by{have:=(dW.mp i).2;omega};refine kP s h t X F (fun x k=>(gQ s h t b e a (c x k)).2.1) u0.1 (fun x k=>(gQ s h t b e a (c x k)).2.2.2) j ?_;intro x k w I g;obtain⟨-,-,z,A⟩:=gQ s h t b e a (c x k);by_contra L;have J:2<=aF D w:=by omega
 have B:(⟨w,0⟩:Σ _:ℕ,ℕ)∈da n D:=by{rw[da,_mf,dW];exact⟨⟨bP.mpr (dc E (w:=w) (by omega)),by show 0+1<aF D w;omega⟩,⟨x,g⟩⟩};by_cases l:(⟨w,0⟩:Σ _:ℕ,ℕ)∈cz n D b
 · obtain⟨v,K,m⟩:=_mg.mp l
   have p:b v=w:=congrArg Sigma.fst m;have q:=(u v K).2.1;rw[p] at q;rw[q,_ms] at g;have r:=(u x z).2.2.2 u0.1 j A;rw[g,p] at r;omega
 · have d:(⟨w,0⟩:Σ _:ℕ,ℕ)∈aj n D b:=
    _md.mpr ⟨B,l⟩
   rw[a,_ms] at d;have:w=u0.1:=congrArg Sigma.fst d;omega
end SemArms
section SemPaths
variable {n : ℕ} {G H : Fin n → Fin n → Prop} {D : Dag}
lemma gn (a:Fin n):bM ({a}:Finset (Fin n))=cl a:=by
 funext k;simp[bM,cl]
lemma dz (a:au n D) (x:Fin n->_d) {j:ℕ} (b:j<D.length) (s:_d):val D x (n+j)=kF (cR D j) (val D x (aw D (j,s))) (val D x (aw D (j,!s))):=by
 rw[cS a x j b];cases s;{simp[aw]};{cases cR D j <;> simp[aw,Bool.and_comm,Bool.or_comm]}
lemma iG (f:bJ G) {i:Fin n} {S:Finset (Fin n)} (h:cN G (bB i (bM S))):(∃ a∈S,G i a)\/∃ a∈S,∃ b∈S,G a b:=by
 obtain⟨u,v,c,d,e⟩:=h;simp only[bB,bM,Bool.or_eq_true,decide_eq_true_eq] at d e;rcases d with d|d <;> rcases e with e|e;{rw[d,e] at c;exact absurd c (f.2.1 i)};{rw[d] at c;exact Or.inl ⟨v,e,c⟩};{rw[e] at c;exact Or.inl ⟨u,d,f.1 _ _ c⟩};{exact Or.inr ⟨u,d,v,e,c⟩}
lemma iH (k:au n D) {v b t:ℕ} (h:bz n D v b) (m:b<=t):b=v\/¬ Relation.ReflTransGen (fun a c=>bk n D a c/\c≠b) v t:=by
 induction h using Relation.ReflTransGen.head_induction_on with
 | refl=>exact Or.inl rfl
 | @head a c d f ih=>
  by_cases g:b=a;{exact Or.inl g}
  · right
    intro p;rcases Relation.ReflTransGen.cases_head p with q|⟨c',l,f'⟩
    · have r:=jv k d.1
      have s:=dt k (fun _ _ i=>i.1) f;omega
    · have j:c=c':=dS d.1 l.1 d.2
      subst j;rcases ih with rfl|ih;{exact l.2 rfl};{exact ih f'}
lemma kc (l:au n D) (x y:Fin n->_d) (v:Fin n) (e:∀ k,k≠v->x k=y k) (b t:ℕ) (d:b=v.val\/¬ Relation.ReflTransGen (fun a c=>bk n D a c/\c≠b) v.val t) (i:val D x b=val D y b):val D x t=val D y t:=by
 by_contra f;rcases d with rfl|d
 · rw[bY D x _ v.isLt,bY D y _ v.isLt] at i
   have g:x=y:=by{funext k;by_cases j:k=v;{rw[j];exact i};{exact e k j}};exact f (by rw[g])
 · exact d (eG (fun a c h=>⟨h.1,fun m=>h.2 (by rw[m];exact i)⟩) (d_ l x y v e _ f))
lemma mH (j:au n D) {a c q:ℕ} (k:bz n D a c) (f:Relation.ReflTransGen (bk n D) a q):Relation.ReflTransGen (bk n D) c q\/(bz n D q c/\q≠c):=by
 revert f;induction k using Relation.ReflTransGen.head_induction_on with
 | refl=>exact fun f=>Or.inl f
 | @head a a' b d ih=>
  intro f;rcases Relation.ReflTransGen.cases_head f with g|⟨a'',l,d'⟩
  · right
    have m:=jv j b.1;have p:=dt j (fun _ _ h=>h.1) d;refine⟨?_,by omega⟩;rw[<- g];exact Relation.ReflTransGen.head b d
  · have i:a'=a'':=dS b.1 l b.2
    subst i;exact ih d'
lemma gR (d:au n D) (v:Fin n) {j:ℕ} (g:j<D.length) (s:_d) (l:bz n D v.val (aw D (j,!s))) (u:aF D (aw D (j,!s))=1) (x y:Fin n->_d) (m:∀ k,k≠v->x k=y k):val D x (aw D (j,s))=val D y (aw D (j,s)):=by
 by_contra p;have w:Relation.ReflTransGen (bk n D) v.val (aw D (j,s)):=eG (fun _ _ h=>h.1) (d_ d x y v m _ p);have b:bk n D (aw D (j,!s)) (n+j):=cM g (!s);have c:bk n D (aw D (j,s)) (n+j):=cM g s;have r:=dh d g s;have t:=dh d g (!s);rcases mH d l w with q|⟨q,z⟩
 · rcases Relation.ReflTransGen.cases_head q with e|⟨c',i,a⟩
   · exact pd d g s e.symm
   · have f:n+j=c':=dS b i u
     subst f;have:=dt d (fun _ _ h=>h) a;omega
 · rcases Relation.ReflTransGen.cases_head q with e|⟨q',i,a⟩
   · exact z e
   · have f:n+j=q':=dS c i.1 i.2
     subst f;have:=dt d (fun _ _ h=>h.1) a;omega
lemma kd (g:au n D) (h:sem_Umbrella n G H D) (x:Fin n->_d) (v:Fin n) (b:ℕ) (c:j_ n D b v.val) (i:¬ cN H x) (j:cN G (bB v x)):val D x b=false/\val D (bB v x) b=true:=by
 have d:val D x b≠val D (bB v x) b:=by{intro e;have k:=mw g x _ v (dd v x) b c e;exact i (h.2.2.2.1 x (by rw[k];exact h.2.2.1 _ j))};have a:=gJ g x (bB v x) (iE v x) b;cases f:val D x b
 · refine⟨rfl,?_⟩
   cases l:val D (bB v x) b;{exact absurd (f.trans l.symm) d};{rfl}
 · exact absurd (f.trans (a f).symm) d
lemma pe (e:au n D) (i:Fin n) (w:ℕ) (v:bz n D i.val w) (Bs N:Finset (Fin n)) (L:N⊆Bs) (M:val D (bB i (bM (Bs\N))) w=false) (P:∀ a∈N,val D (bB i (bM {a})) w=true) (Q:∀ a∈N,val D (bM {a}) w=false):∃ j s,j<D.length/\cR D j=true/\n+j<=w /\bz n D i.val (aw D (j,!s))/\ag n D (aw D (j,s))∩Bs=N:=by
 have R:∀ c,bz n D i.val c->(val D (bB i (bM (Bs\N))) c=true \/∃ j s,j<D.length/\cR D j=true/\n+j<=c/\bz n D i.val (aw D (j,!s)) /\aF D (aw D (j,!s))=1/\val D (bM (Bs\N)) (aw D (j,s))=false):=by
  intro c l;induction l with
  | refl=>left;rw[bY D _ _ i.isLt];exact dm i _
  | tail y m ih=>
   obtain⟨j,s,f,rfl,rfl⟩:=fj.mp m.1;have S:=dh e f s;rcases ih with p|⟨j',s',f',k',h,l',J',T'⟩
   · cases k:cR D j
     · left
       rw[dz e _ f s,k,gop_false,p];rfl
     · by_cases I:val D (bB i (bM (Bs\N))) (aw D (j,!s))=true
       · left
         rw[dz e _ f s,k,gop_true,p,I];rfl
       · right
         refine⟨j,!s,f,k,le_refl _,by rw[Bool.not_not];exact y,by rw[Bool.not_not];exact m.2,?_⟩;by_contra b;rw[_nf] at b;exact I (gJ e _ _ (iE i _) _ b)
   · right
     exact⟨j',s',f',k',by omega,l',J',T'⟩
 rcases R w v with p|⟨j,s,f,k,h,l,J,T⟩
 · rw[M] at p
   exact absurd p _fnt
 · refine⟨j,s,f,k,h,l,?_⟩
   have q:bz n D i.val (n+j):=Relation.ReflTransGen.tail l ⟨cM f (!s),J⟩;ext a;rw[_mn];constructor
   · rintro⟨F,G⟩
     by_contra d;have:=cO e F (x:=bM (Bs\N)) (by simp[bM,G,d]);rw[T] at this;exact _fnt this
   · intro d
     refine⟨?_,L d⟩;have r:val D (bM {a}) (n+j)≠val D (bB i (bM {a})) (n+j):=by{intro H;have K:=kc e _ _ i (dd i (bM {a})) (n+j) w (iH e q h) H;rw[Q a d,P a d] at K;exact _fnt K};have t:val D (bB i (bM {a})) (n+j)=true:=by{by_contra b;rw[Bool.not_eq_true] at b;apply r;rw[b];by_contra u;rw[_nf] at u;rw[gJ e _ _ (iE i _) _ u] at b;exact Bool.noConfusion b};rw[dz e _ f s,k,gop_true,Bool.and_eq_true] at t;have g:=gR e i f s l J _ _ (dd i (bM {a}));rw[t.1,gn] at g;exact ee.mpr g
lemma kQ (l:au n D) (i:Fin n) (w:ℕ) (f:bz n D i.val w) (d:Finset (Fin n)) (m:∀ S:Finset (Fin n),S⊆d->(∀ a∈S,¬ G i a) ->val D (bB i (bM S)) w=false) (k:∀ a∈d,G i a ->val D (bB i (bM {a})) w=true/\val D (bM {a}) w=false):∃ j s,j<D.length/\cR D j=true/\n+j<=w /\bz n D i.val (aw D (j,!s)) /\∀ a∈d,(a∈ag n D (aw D (j,s))↔G i a):=by
 classical
 obtain⟨j,s,p,q,g,r,c⟩:=pe l i w f d (d.filter (fun a=>G i a)) (_fs _ _) (m _ sdiff_subset (fun a b e=>by
  rw[_md,_mf] at b
  exact b.2 ⟨b.1,e⟩))
  (fun a b=>(k a (_mf.mp b).1 (_mf.mp b).2).1)
  (fun a b=>(k a (_mf.mp b).1 (_mf.mp b).2).2)
 refine⟨j,s,p,q,g,r,fun a b=>?_⟩;constructor
 · intro h
   have:a∈ag n D (aw D (j,s))∩d:=_mn.mpr ⟨h,b⟩;rw[c,_mf] at this;exact this.2
 · intro e
   have:a∈d.filter (fun a=>G i a):=_mf.mpr ⟨b,e⟩;rw[<- c] at this;exact(_mn.mp this).1
lemma eM (g:bJ G) (d:au n D) (h:sem_Umbrella n G H D) {i:Fin n} (j:i∈aa n D) {b:ℕ} (c:bz n D i.val b) (k:2<=aF D b):ag n D b=∅:=by
 have a:=fk g d h i b (ds d c);refine eq_empty_of_forall_notMem (fun x e=>?_);have f:=a e;rw[_ms] at f;have l:=fG.mp j b (f▸e);omega
lemma jK {a t:ℕ} (f:Relation.ReflTransGen (bk n D) a t):bz n D a t\/∃ b,bz n D a b/\2<=aF D b:=by
 induction f using Relation.ReflTransGen.head_induction_on with
 | refl=>exact Or.inl Relation.ReflTransGen.refl
 | @head a a' c _ ih=>
  by_cases e:aF D a=1
  · rcases ih with d|⟨b,d,g⟩
    · exact Or.inl (Relation.ReflTransGen.head ⟨c,e⟩ d)
    · exact Or.inr ⟨b,Relation.ReflTransGen.head ⟨c,e⟩ d,g⟩
  · have:=ef c
    exact Or.inr ⟨a,Relation.ReflTransGen.refl,by omega⟩
lemma iI (e:bJ G) (h:ai n D) (f:sem_Umbrella n G H D) {i:Fin n} (g:i∈aa n D):bz n D i.val (bH n D) \/∃ b,bz n D i.val b/\2<=aF D b/\ag n D b=∅:=by
 have c:i.val<n+D.length:=by have:=i.isLt;omega
 have j:Relation.ReflTransGen (bk n D) i.val (bH n D):=iD h i.val c;rcases jK j with a|⟨b,a,d⟩;{exact Or.inl a};{exact Or.inr ⟨b,a,d,eM e h.1 f g a d⟩}
lemma ke (a:au n D) {b:ℕ} (d:2<=aF D b) (c:ag n D b=∅):b∈(cD n D).filter (fun w=>¬ (ag n D w).Nonempty):=
 _mf.mpr ⟨bP.mpr (dc a (w:=b) (by omega)),by rw[c];exact not_nonempty_empty⟩
lemma fJ (d:au n D) (c:bL n D=0) {b:ℕ} (e:2<=aF D b):(ag n D b).Nonempty:=by
 by_contra a;rw[not_nonempty_iff_eq_empty] at a;have g:aF D b - 1<=∑ w∈(cD n D).filter (fun w=>¬ (ag n D w).Nonempty),(aF D w - 1):=single_le_sum (f:=fun w=>aF D w - 1) (fun _ _=>Nat.zero_le _) (ke d e a);unfold bL bn at c;omega
lemma gr (f:bJ G) (h:ai n D) (g:sem_Umbrella n G H D) (a:bL n D=0) {i:Fin n} (j:i∈aa n D) {w:ℕ} (k:Relation.ReflTransGen (bk n D) i.val w):bz n D i.val w:=by
 rcases jK k with c|⟨b,c,d⟩;{exact c}
 · have e:=fJ h.1 a d
   rw[eM f h.1 g j c d] at e;exact absurd e not_nonempty_empty
lemma jL (x:bJ G) (t:au n D) (g:sem_Umbrella n G H D) (h:Finset (Fin n)) (l:∀ a∈h,∀ b∈h,¬ H a b) {i:Fin n} (m:∀ a∈h,H i a->G i a) (p:bz n D i.val (bH n D)):∃ j s,j<D.length/\cR D j=true/\bz n D i.val (aw D (j,!s)) /\∀ a∈h,(a∈ag n D (aw D (j,s))↔G i a):=by
 obtain⟨j,s,u,v,-,c,d⟩:=kQ (G:=G) t i (bH n D) p h (fun S e q=>by
  by_contra c;rw[_nf] at c;rcases iG g.1 (g.2.2.2.1 _ c) with ⟨a,k,f⟩|⟨a,k,b,w,r⟩;{exact q a k (m a (e k) f)}
  · exact l a (e k) b (e w) r)
  (fun a _ f=>by
   constructor;{exact g.2.2.1 _ ⟨i,a,f,dm i _,by simp[bB,bM]⟩}
   · by_contra c
     rw[_nf,gn] at c
     exact dF g.1 a (g.2.2.2.1 _ c))
 exact⟨j,s,u,v,c,d⟩
lemma iJ (K:bJ G) (h:au n D) (q:sem_Umbrella n G H D) (d:Finset (Fin n)) (u:∀ a∈d,∀ b∈d,¬ H a b) {i j:Fin n} {w:ℕ} (v:∀ a∈d,H i a->G i a) (l:bz n D i.val w) (x:j_ n D w j.val) (e:∃ a∈d,G j a/\¬ G i a):∃ k s,k<D.length/\cR D k=true/\n+k<=w /\bz n D i.val (aw D (k,!s)) /\∀ a∈d,(a∈ag n D (aw D (k,s))↔G i a):=by
 classical
 have y:¬ cN H (bB i (bM (d.filter (fun a=>¬ G i a)))):=by{intro r;rcases iG q.1 r with ⟨a,t,f⟩|⟨a,t,b,J,z⟩;{exact(_mf.mp t).2 (v a (_mf.mp t).1 f)};{exact u a (_mf.mp t).1 b (_mf.mp J).1 z}};obtain⟨a0,A,m,p⟩:=e;have B:cN G (bB j (bB i (bM (d.filter (fun a=>¬ G i a))))):=⟨j,a0,m,dm j _,by simp[bB,bM,A,p]⟩;have C:=(kd h q _ j w x y B).1;refine kQ h i w l d (fun S E F=>?_) (fun a _ f=>?_)
 · by_contra r
   rw[_nf] at r
   have c:=gJ h (bB i (bM S)) (bB i (bM (d.filter (fun a=>¬ G i a)))) (fun k g=>by
    simp only[bB,bM,Bool.or_eq_true,decide_eq_true_eq] at g⊢;rcases g with g|g;{exact Or.inl g}
    · exact Or.inr (_mf.mpr ⟨E g,F k g⟩)) w r
   rw[C] at c;exact _fnt c
 · have I:=kd h q (bM {a}) i w (ds h l) (by rw[gn];exact dF q.1 a) ⟨i,a,f,dm i _,by simp[bB,bM]⟩
   exact⟨I.2,I.1⟩
lemma ln (E:bJ G) (h:ai n D) (B:sem_Umbrella n G H D) {i:Fin n} (F:i∈aa n D) {e:ℕ×_d} (I:af n D i={e}) (q:∀ j,Relation.ReflTransGen (bk n D) (n+e.1) (n+j)->j≠e.1 ->cR D j=false):∀ t,t∈ag n D (aw D (am e))↔G i t:=by
 have f:=h.1;obtain⟨e0,r,u,b,v,k,w,-⟩:=ci E h B F;have x:e=e0:=singleton_injective (I.symm.trans w);subst x;obtain⟨g,s⟩:=e;intro t;refine⟨fun y=>?_,fun y=>k t y⟩;by_contra z;have d:val D (b4 i t) (n+g)=true:=by{rw[dz f _ r s,u,gop_true,Bool.and_eq_true];exact⟨cO f (by rw[b];exact _mss i) (by simp[b4]),cO f y (by simp[b4])⟩};have l:∀ c,Relation.ReflTransGen (bk n D) (n+g) c ->val D (b4 i t) c=true:=by
  intro c J;induction J with
  | refl=>exact d
  | tail m p ih=>
   obtain⟨j,s',C,rfl,rfl⟩:=fj.mp p;have A:j≠g:=by{have:=dt f (fun _ _ h=>h) m;have:=dh f C s';omega};rw[dz f _ C s',q j (Relation.ReflTransGen.tail m p) A,gop_false,ih];rfl
 have a:=l _ (iD h (n+g) (by omega));rw[B.2.2.2.2 i t z] at a;exact _fnt a
end SemPaths
section SemDiff
variable {n : ℕ} {G H : Fin n → Fin n → Prop} {D : Dag}
lemma f_ {x y:Fin n} {w:ℕ}:w∈aR n D x y↔x∈ag n D w/\y∉ag n D w:=by
 simp only[aR,_mf,mem_range];exact⟨fun h=>h.2,fun h=>⟨cP h.1,h⟩⟩
lemma dY {x y:Fin n} {e:ℕ×_d}:e∈aE n D (aR n D x y)↔e.1<D.length /\(x∈ag n D (aw D e)/\y∉ag n D (aw D e)) /\¬ (x∈ag n D (n+e.1)/\y∉ag n D (n+e.1)):=by
 simp only[aE,eK,_mf,mem_product,mem_range,
  _mv,and_true,f_]
lemma iK (m:au n D) (b:Fin n->ℕ) (i:aM n D b) {x y:Fin n} (j:x≠y) (k:x∈al n D):bn D (aR n D x y)=1+((aj n D b).filter (fun u=>x∈ag n D u.1/\y∉ag n D u.1)).card:=by
 have q:bn D (aR n D x y)=((dq n D).filter (fun u=>x∈ag n D u.1/\y∉ag n D u.1)).card:=by
  rw[eI n D (fun w=>x∈ag n D w/\y∉ag n D w)];symm;refine sum_subset (fun w h=>?_) (fun w h c=>?_)
  · rw[_mf] at h
    exact f_.mpr h.2
  · have l:w∉cD n D:=fun d=>c (_mf.mpr ⟨d,f_.mp h⟩)
    rw[bP] at l;simp[d0 m w (by omega)]
 have r:(dq n D).filter (fun u=>x∈ag n D u.1/\y∉ag n D u.1)={(⟨b x,0⟩:Σ _:ℕ,ℕ)}∪(aj n D b).filter (fun u=>x∈ag n D u.1/\y∉ag n D u.1):=by
  ext u;have e:=eY m b i
  simp only[aj,da,_mu,_mf,_md,
   _ms]
  constructor
  · intro a
    by_cases p:u∈cz n D b
    · left
      obtain⟨v,s,rfl⟩:=_mg.mp p;have f:=a.2.1;rw[(i v s).2,_ms] at f;rw[f]
    · exact Or.inr ⟨⟨⟨a.1,⟨x,a.2.1⟩⟩,p⟩,a.2⟩
  · rintro (rfl|a)
    · have g:=i x k
      refine⟨(_mf.mp (e (_mg.mpr ⟨x,k,rfl⟩))).1,?_,?_⟩;{rw[g.2];exact _mss x};{rw[g.2,_ms];exact fun d=>j d.symm}
    · exact⟨a.1.1.1,a.2⟩
 have t:(⟨b x,0⟩:Σ _:ℕ,ℕ)∉(aj n D b).filter (fun u=>x∈ag n D u.1/\y∉ag n D u.1):=by{intro d;exact(_md.mp (_mf.mp d).1).2 (_mg.mpr ⟨x,k,rfl⟩)};rw[q,r,singleton_union,_cin t];omega
lemma ji (v:au n D) {x y:Fin n} (z:x≠y) {w:ℕ} (A:x∈ag n D w/\y∈ag n D w):∃ j s,j<D.length/\cR D j=false/\x∈ag n D (n+j)/\y∈ag n D (n+j) /\x∈ag n D (aw D (j,s))/\y∉ag n D (aw D (j,s)) /\y∈ag n D (aw D (j,!s))/\x∉ag n D (aw D (j,!s)):=by
 classical
 have d:∃ u,x∈ag n D u/\y∈ag n D u:=⟨w,A⟩;obtain⟨e,g⟩:=Nat.find_spec d;have a:∀ u,u<Nat.find d->¬ (x∈ag n D u/\y∈ag n D u):=fun u B=>Nat.find_min d B;generalize Nat.find d=f at e g a;have C:=cP e;have H:n<=f:=by{by_contra h;have E:ag n D f={⟨f,by omega⟩}:=dr D ⟨f,by omega⟩;rw[E,_ms] at e g;exact z (e.trans g.symm)};obtain⟨j,rfl⟩:∃ j,f=n+j:=⟨f - n,by omega⟩;have l:j<D.length:=by omega
 obtain⟨F,G,-⟩:=v j l;have i:=a _ F;have m:=a _ G;cases t:cR D j
 · have e':=e
   have g':=g;rw[de v l t,_mu] at e' g';refine⟨j,?_⟩;rcases e' with q|r
   · have b:y∉ag n D (cj D j):=fun h=>i ⟨q,h⟩
     have c:y∈ag n D (ck D j):=g'.resolve_left b;exact⟨false,l,t,e,g,by simpa[aw] using q,by simpa[aw] using b,by simpa[aw] using c,by simpa[aw] using fun h=>m ⟨h,c⟩⟩
   · have c:y∉ag n D (ck D j):=fun h=>m ⟨r,h⟩
     have b:y∈ag n D (cj D j):=g'.resolve_right c;exact⟨true,l,t,e,g,by simpa[aw] using r,by simpa[aw] using c,by simpa[aw] using b,by simpa[aw] using fun h=>i ⟨h,b⟩⟩
 · exfalso
   rw[cB v l t,_mn] at e g;exact i ⟨e.1,g.1⟩
lemma gt (J:bJ G) (h:ai n D) (K:sem_Umbrella n G H D) (b:Fin n->ℕ) (L:aM n D b) {x c z:Fin n} (f:x≠c) (M:x∈al n D) (g:∀ u∈aj n D b,x∈ag n D u.1->c∈ag n D u.1) {w:ℕ} (N:x∈ag n D w/\c∈ag n D w) (q:G x z) (r:¬ G c z):bn D (aR n D x c)=1/\aW n D (aR n D x c)=∅ /\(aE n D (aR n D x c)).card=2 /\∃ e∈aE n D (aR n D x c),cR D e.1=false/\c∈ag n D (n+e.1):=by
 have s:=h.1;have a:bn D (aR n D x c)=1:=by{rw[iK s b L f M,filter_eq_empty_iff.mpr (fun u P d=>d.2 (g u P d.1)),_ce]};have t:=gN h x c f (by rw[cs J K];exact notMem_empty x);rw[a] at t;obtain⟨j1,s1,v,y,A,i,j,k,-,-⟩:=ji s f N;have l:(j1,s1)∈aE n D (aR n D x c):=dY.mpr ⟨v,⟨j,k⟩,fun d=>d.2 i⟩;obtain⟨j2,s2,B,-,C,m,E⟩:=gP J s K r q;have F:(j2,s2)∈aE n D (aR n D x c):=dY.mpr ⟨B,⟨C,fun d=>_dl.mp E d (by simp)⟩,fun d=>m d.1⟩;have I:(j1,s1)≠(j2,s2):=by{intro p;rw[Prod.mk.injEq] at p;exact m (p.1▸A)};have Q:2<=(aE n D (aR n D x c)).card:=one_lt_card.mpr ⟨_,l,_,F,I⟩;exact⟨a,card_eq_zero.mp (by omega),by omega,(j1,s1),l,y,i⟩
lemma jV (y:bJ G) (d:au n D) (l:sem_Umbrella n G H D) {i:Fin n} {j:ℕ} (m:j<D.length) (s:_d) (x:cR D j=true) (e:bz n D i.val (aw D (j,!s))) (u:aF D (aw D (j,!s))=1) (f:n+j<=bH n D) {a:Fin n} (p:G i a):a∈ag n D (aw D (j,s)):=by
 have g:bz n D i.val (n+j):=Relation.ReflTransGen.tail e ⟨cM m (!s),u⟩;have q:val D (cl a) (bH n D)=false:=by{by_contra v;rw[_nf] at v;exact dF l.1 a (l.2.2.2.1 _ v)};have r:val D (bB i (cl a)) (bH n D)=true:=l.2.2.1 _ ⟨i,a,p,dm i _,by simp[bB,cl]⟩;have h:val D (bB i (cl a)) (n+j)=true:=by{by_contra b;rw[Bool.not_eq_true] at b;have t:val D (cl a) (n+j)=false:=by{by_contra k;rw[_nf] at k;rw[gJ d _ _ (iE i _) _ k] at b;exact Bool.noConfusion b};have w:=kc d _ _ i (dd i (cl a)) (n+j) (bH n D) (iH d g f) (t.trans b.symm);rw[q,r] at w;exact _fnt w};rw[dz d _ m s,x,gop_true,Bool.and_eq_true] at h;have c:=gR d i m s e u _ _ (dd i (cl a));rw[h.1] at c;exact ee.mpr c
end SemDiff
def aQ (n:ℕ) (D:Dag) (P M:Finset (Fin n)):Prop:=∃ w,ag n D w∩P=M
def du (n:ℕ) (D:Dag) (P:Finset (Fin n)):Finset ℕ:=(aW n D (ao n D P)).filter (fun j=>2<=(ag n D (n+j)∩P).card)
def dG (n:ℕ) (D:Dag) (P U:Finset (Fin n)) (f:Fin n) (e:ℕ×_d):Prop:=e.1<D.length/\cR D e.1=true/\f∈P/\f∈ag n D (aw D e) /\f∉ag n D (n+e.1)/\ag n D (aw D e)∩P⊆U/\(ag n D (aw D e)∩P).card<=2
def ch (n:ℕ) (D:Dag) (P:Finset (Fin n)) (e:ℕ×_d):(ℕ×_d) ⊕ ℕ:=if ag n D (n+e.1)∩P=∅ then Sum.inl e else Sum.inr e.1
def kf (n:ℕ) (D:Dag) (P:Finset (Fin n)) (c:(ℕ×_d) ⊕ ℕ):Prop:=Sum.elim (fun e=>e∈aE n D (ao n D P)/\(ag n D (aw D e)∩P).card<=2) (fun j=>j∈aW n D (ao n D P)/\(ag n D (n+j)∩P).card=1) c
section SupMask
variable {n : ℕ} {D : Dag}
lemma iW (P:Finset (Fin n)) (w:ℕ):aQ n D P (ag n D w∩P):=⟨w,rfl⟩
lemma jw {P M:Finset (Fin n)} (h:aQ n D P M):M⊆P:=by
 obtain⟨w,rfl⟩:=h;exact inter_subset_right
lemma cC {P:Finset (Fin n)} {w:ℕ}:w∈ao n D P↔(ag n D w∩P).Nonempty:=by
 simp only[ao,_mf,mem_range];constructor;{exact fun h=>h.2}
 · intro h
   obtain⟨v,a⟩:=h;exact⟨cP (_mn.mp a).1,v,a⟩
lemma lp (d:au n D) {P M:Finset (Fin n)} (b:2<=M.card) (h:aQ n D P M):∃ j∈du n D P,ag n D (n+j)∩P=M:=by
 obtain⟨w,e⟩:=h;obtain⟨j,-,-,c,a,-,-⟩:=ew d P M b w e;exact⟨j,_mf.mpr ⟨a,by rw[c];exact b⟩,c⟩
lemma eZ (e:au n D) (P:Finset (Fin n)) (F:Finset (Finset (Fin n))) (c:∀ M∈F,2<=M.card/\aQ n D P M):F.card<=(du n D P).card:=by
 have a:F⊆(du n D P).image (fun j=>ag n D (n+j)∩P):=by{intro M d;obtain⟨j,f,b⟩:=lp e (c M d).1 (c M d).2;exact _mg.mpr ⟨j,f,b⟩};exact(_cl a).trans card_image_le
lemma k5 (r:au n D) {P T:Finset (Fin n)} (s:P.card<=7) (E:T.card=3) (h:aQ n D P T):(∃ A,aQ n D P A/\A.card=2/\A⊆T) \/(∃ A,aQ n D P A/\A.card=4/\T⊆A) \/(∃ A B,A≠B/\aQ n D P A/\aQ n D P B/\A.card=5/\B.card=5 /\T⊆A/\T⊆B/\A∩B=T):=by
 obtain⟨w,t⟩:=h;obtain⟨j,u,-,k,-,-,g⟩:=ew r P T (by omega) w t;have a:aQ n D P (ag n D (cj D j)∩P):=iW P _;have b:aQ n D P (ag n D (ck D j)∩P):=iW P _;rcases g with ⟨x,d,e⟩|⟨-,d,e,f,-,-⟩
 · have c:(ag n D (cj D j)∩P)∩(ag n D (ck D j)∩P)=T:=by
    rw[<- k,cB r u x];ext v;simp only[_mn];tauto
   generalize ag n D (cj D j)∩P=A at a d c;generalize ag n D (ck D j)∩P=B at b e c;have l:=card_lt_card d;have i:=card_lt_card e;have F:(A∪B).card<=7:=(_cl (union_subset (jw a) (jw b))).trans s;have m:=card_union_add_card_inter A B;rw[c] at m;by_cases y:A.card=4;{exact Or.inr (Or.inl ⟨A,a,y,d.subset⟩)};by_cases y':B.card=4;{exact Or.inr (Or.inl ⟨B,b,y',e.subset⟩)};refine Or.inr (Or.inr ⟨A,B,?_,a,b,by omega,by omega,d.subset,e.subset,c⟩);intro q;rw[q,inter_self] at c;rw[c] at i;omega
 · generalize ag n D (cj D j)∩P=A at a d f
   generalize ag n D (ck D j)∩P=B at b e f;have l:=card_lt_card d;have i:=card_lt_card e;have z:=card_union_le A B;rw[f] at z;by_cases C:A.card=2;{exact Or.inl ⟨A,a,C,d.subset⟩};{exact Or.inl ⟨B,b,by omega,e.subset⟩}
lemma lW {T T' A:Finset (Fin n)} (e:A.card=2) (c:A⊆T) (d:A⊆T') (a:T≠T'->(T∩T').card<=1):T=T':=by
 by_contra b;have f:=_cl (subset_inter c d);have g:=a b;omega
lemma lX {T T' A:Finset (Fin n)} (f:T.card=3) (f':T'.card=3) (g:A.card=4) (d:T⊆A) (e:T'⊆A) (a:T≠T'->(T∩T').card<=1):T=T':=by
 by_contra b;have h:=_cl (union_subset d e);have i:=card_union_add_card_inter T T';have j:=a b;omega
lemma nS {T1 T2 T3 A:Finset (Fin n)} (g:T1.card=3) (h:T2.card=3) (i:T3.card=3) (j:A.card<=5) (a:T1⊆A) (b:T2⊆A) (c:T3⊆A) (d:(T1∩T2).card<=1) (e:(T1∩T3).card<=1) (f:(T2∩T3).card<=1):False:=by
 have k:=_cl (union_subset (union_subset a b) c);have l:=card_union_add_card_inter T1 T2;have m:=card_union_add_card_inter (T1∪T2) T3;have p:((T1∪T2)∩T3).card<=(T1∩T3).card+(T2∩T3).card:=by{rw[union_inter_distrib_right];exact card_union_le _ _};omega
lemma mI (N:au n D) {P:Finset (Fin n)} (Q:P.card<=7) (L:Finset (Finset (Fin n))) (j:∀ T∈L,T.card=3/\aQ n D P T) (b:∀ T∈L,∀ T'∈L,T≠T'->(T∩T').card<=1):∃ a:Finset (Finset (Fin n)),L.card<=a.card/\∀ A∈a,aQ n D P A /\((A.card=2/\∃ T∈L,A⊆T)\/A.card=4\/A.card=5):=by
 classical
 refine⟨P.powerset.filter (fun A=>aQ n D P A /\((A.card=2/\∃ T∈L,A⊆T)\/A.card=4\/A.card=5)),?_,fun A l=>(_mf.mp l).2⟩;generalize i:P.powerset.filter (fun A=>aQ n D P A /\((A.card=2/\∃ T∈L,A⊆T)\/A.card=4\/A.card=5))=a;have c:∀ A,aQ n D P A ->((A.card=2/\∃ T∈L,A⊆T)\/A.card=4\/A.card=5)->A∈a:=by{intro A m p;rw[<- i];exact _mf.mpr ⟨mem_powerset.mpr (jw m),m,p⟩};have k:∀ A∈a,(A.card=2/\∃ T∈L,A⊆T)\/A.card=4\/A.card=5:=by{intro A l;rw[<- i] at l;exact(_mf.mp l).2.2};have q:∀ T∈L,2<=∑ A∈a,(if A.card=5 then (if T⊆A then 1 else 0) else (if A⊆T\/T⊆A then 2 else 0)):=by
  intro T f;rcases k5 N Q (j T f).1 (j T f).2 with
   ⟨A,z,r,w⟩|⟨A,z,r,w⟩|⟨A,B,C,E,F,s,t,G,H,-⟩
  · refine le_trans ?_ (single_le_sum (fun _ _=>Nat.zero_le _) (c A z (Or.inl ⟨r,T,f,w⟩)))
    simp[r,w]
  · refine le_trans ?_ (single_le_sum (fun _ _=>Nat.zero_le _) (c A z (Or.inr (Or.inl r))))
    simp[r,w]
  · have u:({A,B}:Finset (Finset (Fin n)))⊆a:=by
     intro x M;rw[_mi,_ms] at M;rcases M with rfl|rfl;{exact c _ E (Or.inr (Or.inr s))};{exact c _ F (Or.inr (Or.inr t))}
    refine le_trans ?_ (sum_le_sum_of_subset u);rw[sum_pair C];simp[s,t,G,H]
 have v:∀ A∈a,∑ T∈L,(if A.card=5 then (if T⊆A then 1 else 0) else (if A⊆T\/T⊆A then 2 else 0))<=2:=by
  intro A l;by_cases y:A.card=5
  · have e:∑ T∈L,(if A.card=5 then (if T⊆A then 1 else 0)
     else (if A⊆T\/T⊆A then 2 else 0))=(L.filter (fun T=>T⊆A)).card:=by
     rw[card_filter];exact sum_congr rfl (fun T _=>by simp[y])
    rw[e];by_contra R;obtain⟨T1,T2,T3,m1,m2,m3,n12,n13,n23⟩:=two_lt_card_iff.mp (show 2<(L.filter (fun T=>T⊆A)).card by omega);rw[_mf] at m1 m2 m3;exact nS (j _ m1.1).1 (j _ m2.1).1 (j _ m3.1).1 y.le m1.2 m2.2 m3.2 (b _ m1.1 _ m2.1 n12) (b _ m1.1 _ m3.1 n13) (b _ m2.1 _ m3.1 n23)
  · have e:∑ T∈L,(if A.card=5 then (if T⊆A then 1 else 0)
     else (if A⊆T\/T⊆A then 2 else 0))=
     2*(L.filter (fun T=>A⊆T\/T⊆A)).card:=by
     rw[card_filter,mul_sum];exact sum_congr rfl (fun T _=>by simp[y])
    rw[e];have S:(L.filter (fun T=>A⊆T\/T⊆A)).card<=1:=by
     rw[card_le_one];intro T f T' f';rw[_mf] at f f';have U:=(j T f.1).1;have U':=(j T' f'.1).1;rcases k A l with ⟨p,-⟩|W|y'
     · have J:A⊆T:=f.2.resolve_right (fun h=>by
        have:=_cl h;omega)
       have K:A⊆T':=f'.2.resolve_right (fun h=>by
        have:=_cl h;omega)
       exact lW p J K (b T f.1 T' f'.1)
     · have J:T⊆A:=f.2.resolve_left (fun h=>by
        have:=_cl h;omega)
       have K:T'⊆A:=f'.2.resolve_left (fun h=>by
        have:=_cl h;omega)
       exact lX U U' W J K (b T f.1 T' f'.1)
     · exact absurd y' y
    omega
 have m:=card_nsmul_le_sum L _ 2 q;have p:=sum_le_card_nsmul a _ 2 v;rw[sum_comm] at m;simp only[smul_eq_mul] at m p;omega
lemma my (t:au n D) {P:Finset (Fin n)} (u:P.card<=7) (L:Finset (Finset (Fin n))) (c:∀ T∈L,T.card=3/\aQ n D P T) (b:∀ T∈L,∀ T'∈L,T≠T'->(T∩T').card<=1) (X:Finset (Finset (Fin n))) (d:∀ M∈X,aQ n D P M/\2<=M.card/\M∉L/\M.card≠4/\M.card≠5 /\(M.card=2->∀ T∈L,¬ M⊆T)):2*L.card+X.card<=(du n D P).card:=by
 classical
 obtain⟨Aux,e,a⟩:=mI t u L c b;have f:Disjoint L Aux:=by{rw[_dl];intro T g i;have:=(c T g).1;rcases (a T i).2 with ⟨h,-⟩|h|h <;> omega};have j:Disjoint (L∪Aux) X:=by
  rw[_dl];intro M k l;obtain⟨-,-,m,p,q,r⟩:=d M l;rcases _mu.mp k with h|h;{exact m h}
  · rcases (a M h).2 with ⟨v,T,g,w⟩|x|y
    · exact r v T g w
    · exact p x
    · exact q y
 have s:=eZ t P ((L∪Aux)∪X) (by
  intro M k;rcases _mu.mp k with h|h
  · rcases _mu.mp h with h|h
    · exact⟨by have:=(c M h).1;omega,(c M h).2⟩
    · refine⟨?_,(a M h).1⟩
      rcases (a M h).2 with ⟨h,-⟩|h|h <;> omega
  · exact⟨(d M h).2.1,(d M h).1⟩)
 rw[_cud j,_cud f] at s;omega
lemma jM {G H:Fin n->Fin n->Prop} (r:bJ G) (t:au n D) (u:sem_Umbrella n G H D) {P U X:Finset (Fin n)} (g:U⊆P) (i:U.card<=2\/(U.card=3/\¬ aQ n D P U)) (w:∀ a∈X,∀ b∈X,¬ H a b) (k:P\U⊆X) {f:Fin n} (x:f∈U) (l:∃ a∈X,G f a):∃ e,dG n D P U f e:=by
 obtain⟨j,s,y,z,A,B,C⟩:=fm r t u X w f l;have c:ag n D (aw D (j,s))∩P⊆U:=by{intro v m;rw[_mn] at m;by_contra p;exact _dl.mp C m.1 (k (_md.mpr ⟨m.2,p⟩))};refine⟨(j,s),y,z,g x,A,B,c,?_⟩;rcases i with i|⟨E,d⟩;{exact(_cl c).trans i}
 · have q:ag n D (aw D (j,s))∩P≠U:=fun h=>d ⟨_,h⟩
   have:=card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨c,q⟩);omega
lemma gB (c:au n D) {P U:Finset (Fin n)} {f:Fin n} {e:ℕ×_d} (h:dG n D P U f e):ag n D (n+e.1)∩P⊆(ag n D (aw D e)∩P).erase f:=by
 obtain⟨d,g,-,-,i,-,-⟩:=h;intro v a;rw[_mn] at a;rw[_me,_mn];exact⟨fun b=>i (b▸a.1),cr c d g e.2 a.1,a.2⟩
lemma jN {P U:Finset (Fin n)} {f:Fin n} {e:ℕ×_d} (h:dG n D P U f e) (c:∀ M,M⊆U->M.card=2->f∈M->¬ aQ n D P M):ag n D (aw D e)∩P={f}:=by
 obtain⟨-,-,d,g,-,a,k⟩:=h;have b:f∈ag n D (aw D e)∩P:=_mn.mpr ⟨g,d⟩;have i:(ag n D (aw D e)∩P).card≠2:=fun j=>c _ a j b (iW P _);exact(_eqc (singleton_subset_iff.mpr b) (by rw[_cs];omega)).symm
lemma iX {P:Finset (Fin n)} {e e0:ℕ×_d} (h:ch n D P e=Sum.inl e0):e=e0/\ag n D (n+e.1)∩P=∅:=by
 unfold ch at h;split_ifs at h with a;exact⟨Sum.inl.inj h,a⟩
lemma kR {P:Finset (Fin n)} {e:ℕ×_d} {j:ℕ} (h:ch n D P e=Sum.inr j):e.1=j/\(ag n D (n+e.1)∩P).Nonempty:=by
 unfold ch at h;split_ifs at h with a;exact⟨Sum.inr.inj h,nonempty_iff_ne_empty.mpr a⟩
lemma lq (i:au n D) {P U:Finset (Fin n)} {f:Fin n} {e:ℕ×_d} (h:dG n D P U f e):kf n D P (ch n D P e):=by
 have b:=gB i h;obtain⟨g,l,j,s,-,-,t⟩:=h;have c:f∈ag n D (aw D e)∩P:=_mn.mpr ⟨s,j⟩;unfold ch;split_ifs with m
 · show e∈aE n D (ao n D P)/\(ag n D (aw D e)∩P).card<=2
   refine⟨?_,t⟩;rw[aE,_mf];refine⟨mem_product.mpr ⟨mem_range.mpr g,_mv _⟩,cC.mpr ⟨f,c⟩,?_⟩;rw[cC,m];exact not_nonempty_empty
 · show e.1∈aW n D (ao n D P)/\(ag n D (n+e.1)∩P).card=1
   have d:(ag n D (n+e.1)∩P).Nonempty:=nonempty_iff_ne_empty.mpr m;have k:=_cl b;rw[card_erase_of_mem c] at k;have p:=_cp.mpr d;refine⟨?_,by omega⟩;obtain⟨v,a⟩:=d;rw[_mn] at a;have q:=cr i g l false a.1;have r:=cr i g l true a.1;rw[aX] at q;rw[bh] at r;rw[aW,_mf,mem_range];exact⟨g,cC.mpr ⟨v,_mn.mpr a⟩,cC.mpr ⟨v,_mn.mpr ⟨q,a.2⟩⟩,cC.mpr ⟨v,_mn.mpr ⟨r,a.2⟩⟩⟩
lemma lr (j:au n D) {P U U':Finset (Fin n)} {f f':Fin n} {e:ℕ×_d} (h:dG n D P U f e) (h':dG n D P U' f' e) (d:(ag n D (n+e.1)∩P).Nonempty):f=f':=by
 by_contra g;obtain⟨q,k⟩:=d;have i:=gB j h k;have l:=gB j h' k;rw[_me] at i l;have b:({q,f,f'}:Finset (Fin n))⊆ag n D (aw D e)∩P:=by{intro x a;simp only[_mi,_ms] at a;rcases a with a|a|a <;> rw[a];{exact i.2};{exact _mn.mpr ⟨h.2.2.2.1,h.2.2.1⟩};{exact _mn.mpr ⟨h'.2.2.2.1,h'.2.2.1⟩}};have m:=_cl b;have p:({q,f,f'}:Finset (Fin n)).card=3:=by{rw[_cin,_c2 g];simp only[_mi,_ms,not_or];exact⟨i.1,l.1⟩};have:=h.2.2.2.2.2.2;omega
lemma fK (j:au n D) {P U U':Finset (Fin n)} {f f':Fin n} {e e':ℕ×_d} (h:dG n D P U f e) (h':dG n D P U' f' e') (g:ag n D (aw D e)∩P={f}) (c:f≠f'):ch n D P e≠ch n D P e':=by
 intro b;have k:ag n D (n+e.1)∩P=∅:=by{have a:=gB j h;rw[g,erase_singleton] at a;exact subset_empty.mp a};have l:ch n D P e=Sum.inl e:=by simp[ch,k]
 rw[l] at b;have m:=(iX b.symm).1;subst m;have i:f'∈ag n D (aw D e')∩P:=_mn.mpr ⟨h'.2.2.2.1,h'.2.2.1⟩;rw[g,_ms] at i;exact c i.symm
lemma nT (v:au n D) {P:Finset (Fin n)} (e:Finset (Fin n)) (U:Fin n->Finset (Fin n)) (a:Fin n->ℕ×_d) (b:∀ f∈e,dG n D P (U f) f (a f)) (c:(ℕ×_d) ⊕ ℕ):(e.filter (fun f=>ch n D P (a f)=c)).card<=2:=by
 rcases c with e0|j0
 · by_cases g:(e.filter (fun f=>ch n D P (a f)=Sum.inl e0)).Nonempty
   · obtain⟨f0,h⟩:=g
     rw[_mf] at h;have d:=(b f0 h.1).2.2.2.2.2.2;rw[(iX h.2).1] at d;refine le_trans (_cl ?_) d;intro f i;rw[_mf] at i;have m:=b f i.1;rw[(iX i.2).1] at m;exact _mn.mpr ⟨m.2.2.2.1,m.2.2.1⟩
   · rw[not_nonempty_iff_eq_empty] at g
     rw[g];simp
 · have k:Set.InjOn (fun f=>(a f).2) (e.filter (fun f=>ch n D P (a f)=Sum.inr j0):Set (Fin n)):=by
    intro f i f' i' w;rw[mem_coe,_mf] at i i';obtain⟨x,p⟩:=kR i.2;obtain⟨x',-⟩:=kR i'.2;have r:a f=a f':=Prod.ext (x.trans x'.symm) w;have m':=b f' i'.1;rw[<- r] at m';exact lr v (b f i.1) m' p
   have s:=card_le_card_of_injOn (t:=(univ:Finset _d)) (fun f=>(a f).2) (fun _ _=>_mv _) k;simpa using s
lemma nU (e:au n D) {P:Finset (Fin n)} (a:Finset (Fin n)) (U:Fin n->Finset (Fin n)) (b:Fin n->ℕ×_d) (d:∀ f∈a,dG n D P (U f) f (b f)):a.card<=2*(a.image (fun f=>ch n D P (b f))).card:=card_le_mul_card_image a 2 (fun c _=>nT e a U b d c)
lemma gc (k:au n D) {P:Finset (Fin n)} (Lab S:Finset (Fin n)) (U:Fin n->Finset (Fin n)) (a:Fin n->ℕ×_d) (b:∀ f∈Lab,dG n D P (U f) f (a f)) (g:S⊆Lab) (d:∀ f∈S,ag n D (aw D (a f))∩P={f}):2*S.card+(Lab\S).card <=2*(Lab.image (fun f=>ch n D P (a f))).card:=by
 have r:(S.image (fun f=>ch n D P (a f))).card=S.card:=
  _cij (fun f i f' i' j=>by
   by_contra m
   exact fK k (b f (g i)) (b f' (g i')) (d f i) m j)
 have u:=nU k (Lab\S) U a (fun f i=>b f (_md.mp i).1);have s:Disjoint (S.image (fun f=>ch n D P (a f))) ((Lab\S).image (fun f=>ch n D P (a f))):=by{rw[_dl];intro c p q;obtain⟨f,i,rfl⟩:=_mg.mp p;obtain⟨f',i',j⟩:=_mg.mp q;rw[_md] at i';exact fK k (b f (g i)) (b f' i'.1) (d f i) (fun h=>i'.2 (h▸i)) j.symm};have t:(S.image (fun f=>ch n D P (a f))∪ (Lab\S).image (fun f=>ch n D P (a f))).card <=(Lab.image (fun f=>ch n D P (a f))).card:=
  _cl (union_subset (image_subset_image g) (image_subset_image sdiff_subset))
 rw[_cud s,r] at t;omega
lemma lY (P:Finset (Fin n)) (E:Finset (ℕ×_d)) (p:∀ e∈E,e∈aE n D (ao n D P)) (C:Finset ((ℕ×_d) ⊕ ℕ)) (i:∀ c∈C,kf n D P c) (d:Disjoint E C.toLeft):(du n D P).card+E.card+C.card <=(aE n D (ao n D P)).card+(aW n D (ao n D P)).card:=by
 have q:∀ e∈C.toLeft,e∈aE n D (ao n D P) /\(ag n D (aw D e)∩P).card<=2:=fun e f=>i _ (mem_toLeft.mp f);have k:∀ j∈C.toRight,j∈aW n D (ao n D P) /\(ag n D (n+j)∩P).card=1:=fun j g=>i _ (mem_toRight.mp g);have l:E.card+C.toLeft.card<=(aE n D (ao n D P)).card:=by{rw[<- _cud d];refine _cl (fun e f=>?_);rcases _mu.mp f with h|h;{exact p e h};{exact(q e h).1}};have m:(du n D P).card+C.toRight.card<=(aW n D (ao n D P)).card:=by
  rw[<- _cud]
  · refine _cl (fun j g=>?_)
    rcases _mu.mp g with h|h;{exact(_mf.mp h).1};{exact(k j h).1}
  · rw[_dl]
    intro j l m;have a:=(_mf.mp l).2;have b:=(k j m).2;omega
 have r:=card_toLeft_add_card_toRight (u:=C);omega
lemma mJ (m:au n D) (P:Finset (Fin n)) (E:Finset (ℕ×_d)) (q:∀ e∈E,e∈aE n D (ao n D P)) (Lab S:Finset (Fin n)) (U:Fin n->Finset (Fin n)) (a:Fin n->ℕ×_d) (d:∀ f∈Lab,dG n D P (U f) f (a f)) (j:S⊆Lab) (g:∀ f∈S,ag n D (aw D (a f))∩P={f}) (i:∀ e∈E,∀ f∈Lab,e≠a f):2*((du n D P).card+E.card)+2*S.card+(Lab\S).card <=2*((aE n D (ao n D P)).card+(aW n D (ao n D P)).card):=by
 have t:=gc m Lab S U a d j g;have i':Disjoint E (Lab.image (fun f=>ch n D P (a f))).toLeft:=by{rw[_dl];intro e r p;rw[mem_toLeft,_mg] at p;obtain⟨f,k,b⟩:=p;have l:a f=e:=by{unfold ch at b;split at b;{exact Sum.inl.inj b};{exact absurd b (by simp)}};exact i e r f k l.symm}
 have u:=lY P E q (Lab.image (fun f=>ch n D P (a f))) (by
  intro c s;obtain⟨f,k,rfl⟩:=_mg.mp s
  exact lq m (d f k)) i'
 omega
lemma pg (P:Finset (Fin n)) (E:Finset (ℕ×_d)) (k:∀ e∈E,e∈aE n D (ao n D P)/\3<=(ag n D (aw D e)∩P).card) (C:Finset ((ℕ×_d) ⊕ ℕ)) (l:∀ c∈C,kf n D P c):(du n D P).card+E.card+C.card <=(aE n D (ao n D P)).card+(aW n D (ao n D P)).card:=by
 have m:∀ e∈C.toLeft,e∈aE n D (ao n D P) /\(ag n D (aw D e)∩P).card<=2:=fun e g=>l _ (mem_toLeft.mp g);have p:∀ j∈C.toRight,j∈aW n D (ao n D P) /\(ag n D (n+j)∩P).card=1:=fun j i=>l _ (mem_toRight.mp i);have d:E.card+C.toLeft.card<=(aE n D (ao n D P)).card:=by
  rw[<- _cud]
  · refine _cl (fun e g=>?_)
    rcases _mu.mp g with h|h;{exact(k e h).1};{exact(m e h).1}
  · rw[_dl]
    intro e d f;have a:=(k e d).2;have b:=(m e f).2;omega
 have f:(du n D P).card+C.toRight.card<=(aW n D (ao n D P)).card:=by
  rw[<- _cud]
  · refine _cl (fun j i=>?_)
    rcases _mu.mp i with h|h;{exact(_mf.mp h).1};{exact(p j h).1}
  · rw[_dl]
    intro j d f;have a:=(_mf.mp d).2;have b:=(p j f).2;omega
 have q:=card_toLeft_add_card_toRight (u:=C);omega
lemma pW (h:au n D) (P:Finset (Fin n)) (E:Finset (ℕ×_d)) (i:∀ e∈E,e∈aE n D (ao n D P)/\3<=(ag n D (aw D e)∩P).card) (Lab S:Finset (Fin n)) (U:Fin n->Finset (Fin n)) (a:Fin n->ℕ×_d) (b:∀ f∈Lab,dG n D P (U f) f (a f)) (g:S⊆Lab) (d:∀ f∈S,ag n D (aw D (a f))∩P={f}):2*((du n D P).card+E.card)+2*S.card+(Lab\S).card <=2*((aE n D (ao n D P)).card+(aW n D (ao n D P)).card):=by
 have l:=gc h Lab S U a b g d
 have m:=pg P E i (Lab.image (fun f=>ch n D P (a f))) (by
  intro c j;obtain⟨f,k,rfl⟩:=_mg.mp j
  exact lq h (b f k))
 omega
lemma kH {G H:Fin n->Fin n->Prop} (x:bJ G) (h:ai n D) (y:sem_Umbrella n G H D) (P I:Finset (Fin n)) (t:∀ i∈I,i∈aa n D /\∃ N:Finset (Fin n),N⊆P/\3<=N.card/\∀ a∈N,G i a):∃ E:Finset (ℕ×_d),E.card=I.card/\∀ e∈E,e∈aE n D (ao n D P)/\3<=(ag n D (aw D e)∩P).card:=by
 classical
 have k:∀ i:Fin n,∃ e:ℕ×_d,i∈I->e.1<D.length /\ag n D (aw D e)={i}/\ag n D (n+e.1)=∅ /\∀ a,G i a->a∈ag n D (aw D (e.1,!e.2)):=by
  intro i;by_cases b:i∈I
  · obtain⟨e,j,-,z,A,B,-,-⟩:=ci x h y (t i b).1
    exact⟨e,fun _=>⟨j,z,A,B⟩⟩
  · exact⟨(0,false),fun u=>absurd u b⟩
 choose g l using k;refine⟨I.image (fun i=>((g i).1,!(g i).2)),?_,?_⟩
 · refine _cij (fun i b i' b' c=>?_)
   rw[Prod.mk.injEq,Bool.not_inj_iff] at c;have p:g i=g i':=Prod.ext c.1 c.2;have j:=(l i b).2.1;rw[p,(l i' b').2.1] at j;exact(singleton_injective j).symm
 · intro e p
   obtain⟨i,b,rfl⟩:=_mg.mp p;obtain⟨C,-,d,q⟩:=l i b;obtain⟨N,r,F,s⟩:=(t i b).2;have f:N⊆ag n D (aw D ((g i).1,!(g i).2))∩P:=fun a w=>_mn.mpr ⟨q a (s a w),r w⟩;have u:=_cl f;refine⟨?_,by omega⟩;rw[aE,_mf];refine⟨mem_product.mpr ⟨mem_range.mpr C,_mv _⟩,cC.mpr (_cp.mp (by omega)),?_⟩;rw[cC,d,empty_inter];exact not_nonempty_empty
end SupMask
section K4Generic
variable {n : ℕ} {G H : Fin n → Fin n → Prop} {D : Dag}
lemma mK {T:Finset (Fin n)} {w:ℕ}:w∈ao n D T↔(ag n D w∩T).Nonempty:=by
 simp only[ao,_mf,mem_range,and_iff_right_iff_imp];rintro⟨v,a⟩;exact cP (_mn.mp a).1
lemma fL {T:Finset (Fin n)} {e:ℕ×_d}:e∈aE n D (ao n D T)↔ e.1<D.length/\(ag n D (aw D e)∩T).Nonempty /\¬ (ag n D (n+e.1)∩T).Nonempty:=by
 simp only[aE,eK,_mf,mem_product,mem_range,
  _mv,and_true,mK]
def bA (n:ℕ) (G:Fin n->Fin n->Prop) (D:Dag) (pos:Fin n->ℕ×_d):Prop:=(∀ i∈aa n D,(pos i).1<D.length/\ag n D (n+(pos i).1)=∅ /\(∀ a,G i a->a∈ag n D (aw D (pos i))) /\ag n D (aw D ((pos i).1,!(pos i).2))={i}) /\∀ i∈aa n D,∀ i'∈aa n D,pos i=pos i'->i=i'
lemma bQ (j:bJ G) (h:ai n D) (k:sem_Umbrella n G H D):∃ pos:Fin n->ℕ×_d,bA n G D pos:=by
 classical
 have f:∀ i:Fin n,∃ e:ℕ×_d,i∈aa n D->(e.1<D.length /\ag n D (n+e.1)=∅/\(∀ a,G i a->a∈ag n D (aw D e)) /\ag n D (aw D (e.1,!e.2))={i}):=by
  intro i;by_cases c:i∈aa n D
  · obtain⟨e,d,-,l,m,p,-,-⟩:=ci j h k c
    exact⟨(e.1,!e.2),fun _=>⟨d,m,p,by simpa using l⟩⟩
  · exact⟨(0,false),fun q=>absurd q c⟩
 choose pos b using f;refine⟨pos,b,fun i c i' c' s=>?_⟩;have d:=(b i c).2.2.2;rw[s,(b i' c').2.2.2] at d;exact(singleton_injective d).symm
lemma gC {pos:Fin n->ℕ×_d} (b:bA n G D pos) {i a:Fin n} {T:Finset (Fin n)} (e:i∈aa n D) (c:G i a) (d:a∈T):pos i∈aE n D (ao n D T):=by
 obtain⟨f,g,h,-⟩:=b.1 i e;rw[fL];refine⟨f,⟨a,_mn.mpr ⟨h a c,d⟩⟩,?_⟩;rw[g,empty_inter];exact not_nonempty_empty
lemma e6 {pos:Fin n->ℕ×_d} (b:bA n G D pos) (T J:Finset (Fin n)) (c:∀ i∈J,i∈aa n D/\∃ a∈T,G i a):J.image pos⊆aE n D (ao n D T)/\(J.image pos).card=J.card:=by
 constructor
 · intro e d
   obtain⟨i,f,rfl⟩:=_mg.mp d;obtain⟨g,a,h,j⟩:=c i f;exact gC b g j h
 · exact _cij (fun i f i' f' d=>b.2 i (c i f).1 i' (c i' f').1 d)
lemma gS (a:bJ G) (h:ai n D) (c:sem_Umbrella n G H D) (b:Fin n->ℕ) (d:aM n D b) (T:Finset (Fin n)):(aE n D (ao n D T)).card+(aW n D (ao n D T)).card + (al n D).card<=2*T.card+bd n D:=by
 have e:=co h T (by rw[cs a c,empty_inter]);have f:=cZ h.1 b d T;have g:=_cl (inter_subset_left:T∩al n D⊆T);omega
lemma eH (a:au n D) (T:Finset (Fin n)) (w:ℕ) (b:2<=(ag n D w∩T).card):∃ j∈aW n D (ao n D T),ag n D (n+j)∩T=ag n D w∩T:=by
 obtain⟨j,-,-,c,d,-,-⟩:=ew a T _ b w rfl;exact⟨j,d,c⟩
lemma eA (r:au n D) {T:Finset (Fin n)} (G:T.card=3) {a b c:Fin n} (H:a∈T) (J:b∈T) (K:c∈T) (h:a≠b) (i:a≠c) (s:b≠c) {w1 w2:ℕ} (t:a∈ag n D w1) (u:b∈ag n D w1) (v:a∈ag n D w2) (x:c∈ag n D w2):2<=(aW n D (ao n D T)).card:=by
 have k:a∈ag n D w1∩T:=_mn.mpr ⟨t,H⟩;have l:b∈ag n D w1∩T:=_mn.mpr ⟨u,J⟩;have y:a∈ag n D w2∩T:=_mn.mpr ⟨v,H⟩;have m:c∈ag n D w2∩T:=_mn.mpr ⟨x,K⟩;have L:2<=(ag n D w1∩T).card:=one_lt_card.mpr ⟨a,k,b,l,h⟩;have M:2<=(ag n D w2∩T).card:=one_lt_card.mpr ⟨a,y,c,m,i⟩;obtain⟨j1,z,e1⟩:=eH r T w1 L;by_cases p:ag n D w1∩T=ag n D w2∩T
 · have d:ag n D w1∩T=T:=by
    refine _eqc inter_subset_right ?_;rw[G];exact two_lt_card.mpr ⟨a,k,b,l,c,by rw[p];exact m,h,i,s⟩
   obtain⟨j,-,-,I,N,-,e⟩:=ew r T T (by omega) w1 d;rcases e with ⟨-,A,-⟩|⟨-,A,P,Q,-,-⟩;{exact absurd rfl (Finset.ssubset_of_ssubset_of_subset A inter_subset_right).ne}
   · have B:3<=(ag n D (cj D j)∩T).card+(ag n D (ck D j)∩T).card:=by
      have:=card_union_le (ag n D (cj D j)∩T) (ag n D (ck D j)∩T);rw[Q,G] at this;exact this
     have q:∀ w,ag n D w∩T ⊂ T->2<=(ag n D w∩T).card ->2<=(aW n D (ao n D T)).card:=by{intro w C f;obtain⟨j',hj',e'⟩:=eH r T w f;refine one_lt_card.mpr ⟨j,N,j',hj',fun g=>?_⟩;rw[g,e'] at I;exact C.ne I};by_cases f:2<=(ag n D (cj D j)∩T).card;{exact q _ A f};{exact q _ P (by omega)}
 · obtain⟨j2,F,e2⟩:=eH r T w2 M
   exact one_lt_card.mpr ⟨j1,z,j2,F,fun g=>p (by rw[<- e1,<-e2,g])⟩
lemma m_ (g:bJ G) (h:ai n D) (y:sem_Umbrella n G H D) {pos:Fin n->ℕ×_d} (a:bA n G D pos) {u i1 i2 i3:Fin n} (k:i1∈aa n D) (l:i2∈aa n D) (m:i1≠i2) (d:i1≠i3) (e:i2≠i3) (z:G u i1) (A:G u i2) (v:G u i3):3<=(aE n D (ao n D {u})).card:=by
 have p:=_mss u;have w:=gC a k (g.1 _ _ z) p;have x:=gC a l (g.1 _ _ A) p;have b:pos i1≠pos i2:=fun c=>m (a.2 i1 k i2 l c);by_cases q:i3∈aa n D;{exact two_lt_card.mpr ⟨_,w,_,x,_,gC a q (g.1 _ _ v) p,b,fun c=>d (a.2 i1 k i3 q c),fun c=>e (a.2 i2 l i3 q c)⟩}
 · obtain⟨j,B,-,-,r,-,s,s1,-,s3,-⟩:=eq g h.1 y v
   have C:(j,s)∈aE n D (ao n D {u}):=df.mpr ⟨B,s1,r⟩;have f:∀ i∈aa n D,i≠i3->pos i≠(j,s):=by{intro i E t c;have F:ag n D (aw D (j,!s))={i}:=by{have:=(a.1 i E).2.2.2;rw[c] at this;exact this};rw[F,_ms] at s3;exact t s3.symm};exact two_lt_card.mpr ⟨_,w,_,x,_,C,b,f i1 k d,f i2 l e⟩
lemma ro (h:ai n D) (K:Finset ℕ) (f:K⊆cD n D):(aE n D K).card+(aW n D K).card =(K.filter (fun w=>w<n\/(cj D (w - n)∉K/\ck D (w - n)∉K))).card + bn D K:=by
 obtain⟨g,i,-⟩:=h;have a:∀ w∈K,w+1<n+D.length:=fun w b=>bP.mp (f b);have r:bn D K+K.card=((eK D).filter (fun e=>aw D e∈K)).card:=by{rw[<- fF g,eQ (fun w b=>i w (a w b))]};have k:=card_filter_add_card_filter_not (s:=(eK D).filter (fun e=>aw D e∈K)) (fun e:ℕ×_d=>n+e.1∈K);rw[filter_filter,filter_filter] at k;have t:((eK D).filter (fun e=>aw D e∈K/\n+e.1∈K)).card =((range D.length).filter (fun j=>n+j∈K/\(cj D j∈K\/ck D j∈K))).card+(aW n D K).card:=by
  rw[d8,aW,card_filter,card_filter,<- sum_add_distrib];refine sum_congr rfl (fun j _=>?_);rw[aX,bh];by_cases l:n+j∈K <;> by_cases u:cj D j∈K <;> by_cases v:ck D j∈K <;>
   simp_all
 have x:K.card =(K.filter (fun w=>w<n\/(cj D (w - n)∉K/\ck D (w - n)∉K))).card + ((range D.length).filter (fun j=>n+j∈K/\(cj D j∈K\/ck D j∈K))).card:=by
  rw[<- card_filter_add_card_filter_not (s:=K) (fun w=>w<n\/(cj D (w - n)∉K/\ck D (w - n)∉K))];congr 1;have c:K.filter (fun w=>¬ (w<n\/(cj D (w - n)∉K/\ck D (w - n)∉K)))=((range D.length).filter (fun j=>n+j∈K/\(cj D j∈K\/ck D j∈K))).image (fun j=>n+j):=by
   ext w;simp only[_mf,_mg,mem_range];constructor
   · rintro⟨b,m⟩
     have:=a w b;rw[not_or] at m;exact⟨w - n,⟨by omega,by rwa[Nat.add_sub_cancel' (by omega)],by tauto⟩,by omega⟩
   · rintro⟨j,⟨-,p,q⟩,rfl⟩
     refine⟨p,?_⟩;rw[Nat.add_sub_cancel_left];intro d;rcases d with d|d;{omega};{tauto}
  rw[c,_cii _ (add_right_injective n)]
 unfold aE;omega
def dA (n:ℕ) (D:Dag) (u t:Fin n):Finset ℕ:=(range (n+D.length)).filter (fun w=>u∈ag n D w/\t∈ag n D w)
lemma ec {u t:Fin n} {w:ℕ}:w∈dA n D u t↔u∈ag n D w/\t∈ag n D w:=by
 simp only[dA,_mf,mem_range,and_iff_right_iff_imp];exact fun h=>cP h.1
lemma pX (a:au n D) {j:ℕ} (b:j<D.length) (c:cR D j=false) (s:_d):ag n D (aw D (j,s))⊆ag n D (n+j):=by
 rw[de a b c];cases s;{rw[aX];exact subset_union_left};{rw[bh];exact subset_union_right}
lemma mM (Y:bJ G) (h:ai n D) (Z:sem_Umbrella n G H D) {u t:Fin n} (S:aW n D (ao n D {u})=∅) (mt:aW n D (ao n D {t})=∅) {r:ℕ} (I:u∈ag n D r) (J:t∈ag n D r) (T:2<=aF D r):∃ i k:ℕ×_d,i≠k/\i∈aE n D (ao n D {u}) /\i∈aE n D (ao n D {t})/\k∈aE n D (ao n D {u}) /\k∈aE n D (ao n D {t}):=by
 have K:=h.1;have m:dA n D u t⊆cD n D:=by
  intro w C;rw[ec] at C;rw[bP];have L:=cP C.1;by_contra E;have M:w=bH n D:=by unfold bH;omega
  rw[M,cs Y Z] at C;exact notMem_empty u C.1
 have p:r∈dA n D u t:=ec.mpr ⟨I,J⟩;have N:=ro h _ m;have hM:aW n D (dA n D u t)=∅:=by{refine eq_empty_of_forall_notMem (fun j b=>?_);rw[aW,_mf,mem_range] at b;have:j∈aW n D (ao n D {u}):=by{rw[aW,_mf,mem_range];exact⟨b.1,b7.mpr (ec.mp b.2.1).1,b7.mpr (ec.mp b.2.2.1).1,b7.mpr (ec.mp b.2.2.2).1⟩};rw[S] at this;exact notMem_empty _ this};have P:1<=((dA n D u t).filter (fun w=>w<n \/(cj D (w - n)∉dA n D u t/\ck D (w - n)∉dA n D u t))).card:=by
  have c:(dA n D u t).Nonempty:=⟨r,p⟩;have U:=min'_mem _ c;refine _cp.mpr ⟨_,_mf.mpr ⟨U,?_⟩⟩;by_cases Q:(dA n D u t).min' c<n;{exact Or.inl Q}
  · right
    have L:=cP (ec.mp U).1;have hs:=K ((dA n D u t).min' c - n) (by omega);constructor
    · intro E
      have:=min'_le _ _ E;omega
    · intro E
      have:=min'_le _ _ E;omega
 have W:1<=bn D (dA n D u t):=by
  have:=single_le_sum (f:=fun w=>aF D w - 1) (fun _ _=>Nat.zero_le _) p;unfold bn;have h2:1<=aF D r - 1:=by omega
  exact h2.trans this
 rw[hM,_ce] at N;obtain⟨i,q,k,s,c⟩:=one_lt_card.mp (by omega :1<(aE n D (dA n D u t)).card);have a:∀ e∈aE n D (dA n D u t),e∈aE n D (ao n D {u})/\e∈aE n D (ao n D {t}):=by
  intro e X
  simp only[aE,eK,_mf,mem_product,mem_range,
   _mv,and_true,ec] at X
  obtain⟨b,⟨v,z⟩,d⟩:=X;have A:∀ x y:Fin n,aW n D (ao n D {x})=∅->y∈ag n D (aw D e) ->y∉ag n D (n+e.1)->x∉ag n D (n+e.1):=by
   intro x y mx B R g;cases F:cR D e.1;{exact R (pX K b F e.2 B)}
   · have l:=g
     rw[cB K b F,_mn] at l;have:e.1∈aW n D (ao n D {x}):=by{rw[aW,_mf,mem_range];exact⟨b,b7.mpr g,b7.mpr l.1,b7.mpr l.2⟩};rw[mx] at this;exact notMem_empty _ this
  have hu:u∉ag n D (n+e.1):=fun g=>A u t S z (fun B=>d ⟨g,B⟩) g;have F:t∉ag n D (n+e.1):=fun g=>A t u mt v (fun B=>d ⟨B,g⟩) g;exact⟨df.mpr ⟨b,v,hu⟩,df.mpr ⟨b,z,F⟩⟩
 exact⟨i,k,c,(a i q).1,(a i q).2,(a k s).1,(a k s).2⟩
end K4Generic
section L3Gen
variable {n : ℕ} {G H : Fin n → Fin n → Prop} {D : Dag}
lemma qO (t:au n D) {P:Finset (Fin n)} (y:P.card<=7) (L:Finset (Finset (Fin n))) (u:∀ T∈L,T.card=3/\aQ n D P T) (i:∀ T∈L,∀ T'∈L,T≠T'->(T∩T').card<=1) (E:Finset (ℕ×_d)) (z:∀ e∈E,e∈aE n D (ao n D P)/\3<=(ag n D (aw D e)∩P).card) (a:Finset (Fin n)) (U:Fin n->Finset (Fin n)) (A:∀ f∈a,∃ e,dG n D P (U f) f e) (l:∀ f∈a,∀ T∈L,(U f∩T).card<=1):2*L.card+E.card+a.card <=(aE n D (ao n D P)).card+(aW n D (ao n D P)).card:=by
 classical
 choose! wit c using A;let S:=a.filter (fun f=>∀ M,M⊆U f->M.card=2->f∈M->¬ aQ n D P M);have d:S⊆a:=_fs _ _;have m:∀ f∈a\S,∃ M,M⊆U f/\M.card=2/\f∈M/\aQ n D P M:=by{intro f b;rw[_md,_mf] at b;by_contra B;exact b.2 ⟨b.1,fun M p v q C=>B ⟨M,p,v,q,C⟩⟩};choose! pr h using m
 have I:=my t y L u i ((a\S).image pr) (by
  intro M F;obtain⟨f,b,rfl⟩:=_mg.1 F;obtain⟨p,v,-,q⟩:=h f b;refine⟨q,by omega,fun G=>by have:=(u _ G).1;omega,by omega,by omega,fun _ T H j=>?_⟩;have:=_cl (subset_inter p j);have:=l f (_md.1 b).1 T H
  omega)
 have w:=pW t P E z a S U wit c d (fun f b=>
  jN (c f (d b)) (_mf.1 b).2)
 have x:(a\S).card<=2*((a\S).image pr).card:=by
  refine card_le_mul_card_image _ 2 (fun M _=>?_);by_cases k:((a\S).filter (fun f=>pr f=M)).Nonempty
  · obtain⟨g,r⟩:=k
    rw[_mf] at r;have s:M.card=2:=r.2▸(h g r.1).2.1;rw[<- s];refine _cl (fun f b=>?_);rw[_mf] at b;exact b.2▸(h f b.1).2.2.1
  · rw[not_nonempty_iff_eq_empty.1 k];simp
 have:=card_sdiff_add_card_eq_card d;omega
lemma ph (e:au n D) (Z:Finset ℕ) (c:∀ b∈Z,2<=aF D b/\ag n D b=∅):Z.card<=bL n D:=by
 have a:Z⊆(cD n D).filter (fun w=>¬ (ag n D w).Nonempty):=fun b d=>ke e (c b d).1 (c b d).2;calc Z.card=∑ _w∈Z,1:=by simp
  _<=∑ w∈Z,(aF D w - 1):=sum_le_sum (fun w f=>by have:=(c w f).1;omega)
  _<=bL n D:=sum_le_sum_of_subset a
lemma na (S:bJ G) (R:au n D) (U:sem_Umbrella n G H D) {pos:Fin n->ℕ×_d} (d:bA n G D pos) (T J:Finset (Fin n)) (A:Fin n->Finset (Fin n)) (u:∀ i∈J,i∈aa n D/\(∃ a∈T,G i a)/\∀ f∈T,∃ a∈A f,G i a) (v:∀ f∈T,(∀ a∈A f,∀ b∈A f,¬ H a b)/\T.erase f⊆A f/\∃ a∈A f,G f a):J.card+T.card<=(aE n D (ao n D T)).card:=by
 classical
 obtain⟨p,k⟩:=e6 d T J (fun i q=>⟨(u i q).1,(u i q).2.1⟩);have z:∀ f∈T,∃ e:ℕ×_d,e.1<D.length/\cR D e.1=true /\f∈ag n D (aw D e)/\f∉ag n D (n+e.1)/\Disjoint (ag n D (aw D e)) (A f):=by{intro f c;obtain⟨j,s,x,B,C,E,F⟩:=fm S R U (A f) (v f c).1 f (v f c).2.2;exact⟨(j,s),x,B,C,E,F⟩};choose! w y using z;have r:Set.InjOn w T:=by{intro f c g l I;by_contra K;exact _dl.1 (y f c).2.2.2.2 (I▸(y g l).2.2.1) ((v f c).2.1 (_me.2 ⟨fun h=>K h.symm,l⟩))};have t:Disjoint (J.image pos) (T.image w):=by{rw[_dl];intro e L M;obtain⟨i,q,rfl⟩:=_mg.1 L;obtain⟨f,c,N⟩:=_mg.1 M;obtain⟨a,W,P⟩:=(u i q).2.2 f c;exact _dl.1 (y f c).2.2.2.2 (N▸(d.1 i (u i q).1).2.2.1 a P) W};have m:T.image w⊆aE n D (ao n D T):=by{intro e X;obtain⟨f,c,rfl⟩:=_mg.1 X;obtain⟨x,B,C,E,F⟩:=y f c;refine fL.2 ⟨x,⟨f,_mn.2 ⟨C,c⟩⟩,?_⟩;rintro⟨g,l⟩;rw[_mn] at l;have Q:g∈ag n D (aw D (w f)):=cr R x B (w f).2 l.1;exact _dl.1 F Q ((v f c).2.1 (_me.2 ⟨fun h=>E (h▸l.1),l.2⟩))};have:=_cl (union_subset p m);rw[_cud t,k,_cij r] at this;exact this
lemma nb (p:bJ G) (h:ai n D) (q:sem_Umbrella n G H D) (b:Fin n->ℕ) (r:aM n D b) {pos:Fin n->ℕ×_d} (d:bA n G D pos) (T J:Finset (Fin n)) (A:Fin n->Finset (Fin n)) (s:∀ i∈J,i∈aa n D/\(∃ a∈T,G i a)/\∀ f∈T,∃ a∈A f,G i a) (t:∀ f∈T,(∀ a∈A f,∀ b∈A f,¬ H a b)/\T.erase f⊆A f/\∃ a∈A f,G f a) {x y z:Fin n} (k:T={x,y,z}) (e:x≠y) (g:x≠z) (j:y≠z) {w v:ℕ} (u:x∈ag n D w) (B:y∈ag n D w) (u':x∈ag n D v) (C:z∈ag n D v):J.card+2+(al n D).card<=3+bd n D:=by
 have m:T.card=3:=by
  rw[k,_cin (by simp[e,g]),
   _cin (by simp[j]),_cs]
 have E:=na p h.1 q d T J A s t;have F:=eA h.1 m (a:=x) (b:=y) (c:=z) (by simp[k]) (by simp[k]) (by simp[k]) e g j u B u' C;have I:=co h T (by rw[cs p q];simp);have K:=cZ h.1 b r T;have L:=_cl (inter_subset_left:T∩al n D⊆T);omega
end L3Gen
lemma pY {n:ℕ} {D:Dag} (I:au n D) {P:Finset (Fin n)} (N:P.card<=7) (l:Finset (Finset (Fin n))) (x:∀ T∈l,T.card=3/\aQ n D P T) (q:∀ T∈l,∀ T'∈l,T≠T'->(T∩T').card<=1) (r:Finset (Finset (Fin n))) (y:∀ M∈r,M.card=2/\aQ n D P M/\∀ T∈l,¬ M⊆T) (E:Finset (ℕ×_d)) (Q:∀ e∈E,e∈aE n D (ao n D P)) (a:Finset (Fin n)) (U:Fin n->Finset (Fin n)) (R:∀ f∈a,∃ e,dG n D P (U f) f e) (s:∀ f∈a,∀ T∈l,(U f∩T).card<=1) (t:∀ f∈a,∀ M∈r,(U f∩M).card<=1) (m:∀ e∈E,∀ f∈a,∀ w,dG n D P (U f) f w->e≠w):2*l.card+r.card+E.card+a.card <=(aE n D (ao n D P)).card+(aW n D (ao n D P)).card:=by
 classical
 choose! wit c using R;let S:=a.filter (fun f=>∀ M,M⊆U f->M.card=2->f∈M->¬ aQ n D P M);have p:S⊆a:=_fs _ _;have z:∀ f∈a\S,∃ M,M⊆U f/\M.card=2/\f∈M/\aQ n D P M:=by{intro f b;rw[_md,_mf] at b;by_contra J;exact b.2 ⟨b.1,fun M A y B W=>J ⟨M,A,y,B,W⟩⟩};choose! pr d using z;have k:Disjoint r ((a\S).image pr):=by{rw[_dl];intro M h i;obtain⟨f,b,rfl⟩:=_mg.1 i;have j:=(d f b).1;have C:=(d f b).2.1;have:=_cl (subset_inter j (Subset.refl _));have:=t f (_md.1 b).1 _ h;omega}
 have X:=my I N l x q (r∪(a\S).image pr) (by
  intro M Y;rcases _mu.1 Y with h|i
  · obtain⟨J,Z,u⟩:=y M h
    refine⟨Z,by omega,fun F=>by have:=(x _ F).1;omega,by omega,by omega,fun _ T G=>u T G⟩
  · obtain⟨f,b,rfl⟩:=_mg.1 i
    obtain⟨A,y',-,B⟩:=d f b;refine⟨B,by omega,fun F=>by have:=(x _ F).1;omega,by omega,by omega,fun _ T G j=>?_⟩;have:=_cl (subset_inter A j);have:=s f (_md.1 b).1 T G
    omega)
 rw[_cud k] at X;have K:=mJ I P E Q a S U wit c p (fun f b=>jN (c f (p b)) (_mf.1 b).2) (fun e he f b=>m e he f b (wit f) (c f b));have L:(a\S).card<=2*((a\S).image pr).card:=by
  refine card_le_mul_card_image _ 2 (fun M _=>?_);by_cases v:((a\S).filter (fun f=>pr f=M)).Nonempty
  · obtain⟨g,H⟩:=v
    rw[_mf] at H;have h:M.card=2:=H.2▸(d g H.1).2.1;rw[<- h];refine _cl (fun f b=>?_);rw[_mf] at b;exact b.2▸(d f b.1).2.2.1
  · rw[not_nonempty_iff_eq_empty.1 v];simp
 have:=card_sdiff_add_card_eq_card p;omega
section L3bGen
variable {n : ℕ} {G H : Fin n → Fin n → Prop} {D : Dag}
lemma jx (s:bJ G) (h:ai n D) (y:sem_Umbrella n G H D) (b:Fin n->ℕ) (A:aM n D b) {x c:Fin n} (a:x≠c) (B:x∈al n D) (d:∀ u∈aj n D b,x∈ag n D u.1->c∈ag n D u.1) {w:ℕ} (C:x∈ag n D w/\c∈ag n D w):∃ f,∀ e∈af n D x,e≠f->c∈ag n D (aw D e):=by
 classical
 obtain⟨z,g,i⟩:=s.2.2.1 x c a;obtain⟨-,-,E,e1,j,k,-⟩:=gt s h y b A a B d C g i;have l:((aE n D (aR n D x c)).erase e1).card=1:=by{rw[card_erase_of_mem j,E]};obtain⟨f,m⟩:=_c1.1 l;refine⟨f,fun e t p=>?_⟩;by_contra q;obtain⟨F,I,J⟩:=ak.1 t;have v:e∈(aE n D (aR n D x c)).erase e1:=
  _me.2 ⟨fun r=>by
   have:=cY h.1 t;rw[r,k] at this
   exact _fnt this,dY.2 ⟨F,⟨I,q⟩,fun K=>J K.1⟩⟩
 rw[m,_ms] at v;exact p v
lemma gD (d:au n D) {c:Fin n} (f:aW n D (ao n D {c})=∅) {e:ℕ×_d} (b:e.1<D.length) (g:cR D e.1=true) (h:c∈ag n D (aw D e)):e∈af n D c:=ak.2 ⟨b,h,fun a=>by
 have:=(dL d f b a).1;rw[g] at this
 exact Bool.noConfusion this⟩
lemma pi (z:bJ G) (h:ai n D) (A:sem_Umbrella n G H D) (b:Fin n->ℕ) (y:cU n D b) {c:Σ _:ℕ,ℕ} (r:c∈aj n D b) (X:Finset (Fin n)) (B:X.Nonempty) (a:∀ x∈X,aW n D (ao n D {x})=∅/\x∈ag n D c.1 /\∀ u∈aj n D b,x∈ag n D u.1->u=c):∃ P Q:ℕ×_d,P.1≠Q.1/\∀ x∈X,P∈af n D x/\Q∈af n D x:=by
 have C:=h.1;have g:c∈dq n D:=(_mf.mp (_md.mp r).1).1;have e:2<=aF D c.1:=by{have:=(dW.mp g).2;omega};refine kP z h A X B (fun x i=>(a x i).1) c.1 (fun x i=>(a x i).2.1) e ?_;intro x i w E d;obtain⟨-,j,f⟩:=a x i;have s:x∈al n D:=eX.2 ⟨c.1,e,j⟩;by_contra J;have t:(⟨w,0⟩:Σ _:ℕ,ℕ)∈da n D:=by{rw[da,_mf,dW];exact⟨⟨bP.mpr (dc C (w:=w) (by omega)),by show 0+1<aF D w;omega⟩,⟨x,d⟩⟩};by_cases k:(⟨w,0⟩:Σ _:ℕ,ℕ)∈cz n D b
 · obtain⟨v,F,l⟩:=_mg.mp k
   have m:b v=w:=congrArg Sigma.fst l;have p:=(y v F).2.1;rw[m] at p;rw[p,_ms] at d;have q:=(y x s).2.2.2 c.1 e j;rw[d,m] at q;omega
 · have I:=f _ (_md.mpr ⟨t,k⟩) d
   have:w=c.1:=congrArg Sigma.fst I;omega
lemma oh (r:bJ G) (h:ai n D) (u:sem_Umbrella n G H D) (x:bL n D=0) {i v:Fin n} (B:i∈aa n D) {e:ℕ×_d} (M:af n D i={e}) (y:G i v) (R:∀ p∈af n D v,p.1≠e.1->¬ ag n D (aw D (am p))⊆{i}):∀ t,t∈ag n D (aw D (am e))↔G i t:=by
 have g:=h.1;refine ln r h u B M (fun j c N=>?_);by_contra C;rw[_nf] at C;rcases Relation.ReflTransGen.cases_tail c with S|⟨w,E,z⟩;{exact N (by omega)}
 · obtain⟨j',s,N',P,d⟩:=fj.1 z
   have F:j'=j:=by omega
   subst F;have I:e∈af n D i:=by rw[M];exact _mss e
   obtain⟨J,K,-⟩:=ak.1 I;have a:Relation.ReflTransGen (bk n D) i.val w:=((eG (fun _ _ L=>L.1) (iF g B K)).tail (cM J e.2)).trans E;have l:=gr r h u x B a;have T:aF D w=1:=by{have Z:=ef z;by_contra U;have W:=eM r g u B l (by omega);have Q:=fJ g x (b:=w) (by omega);rw[W] at Q;exact not_nonempty_empty Q};have f:ag n D w⊆{i}:=fk r g u i w (ds g l);have m:v≠i:=fun m=>r.2.1 i (m▸y);have hw':aw D (j',!(!s))=w:=by rw[Bool.not_not];exact d
   have A:v∈ag n D (aw D (j',!s)):=jV r g u N' (!s) C (hw'▸l) (hw'▸T) (by unfold bH;omega) y
   have X:((j',!s):ℕ×_d)∈af n D v:=ak.2 ⟨N',A,fun Y=>by
    have:=f (d▸cr g N' C s Y)
    exact m (_ms.1 this)⟩
   exact R _ X N (by rw[show am (j',!s)=(j',!(!s)) from rfl,hw'];exact f)
lemma pj (d:bJ G) (h:ai n D) (e:sem_Umbrella n G H D) (b:Fin n->ℕ) (g:aM n D b) {pos:Fin n->ℕ×_d} (c:bA n G D pos) (T J:Finset (Fin n)) (A:Fin n->Finset (Fin n)) (j:∀ i∈J,i∈aa n D/\(∃ a∈T,G i a)/\∀ f∈T,∃ a∈A f,G i a) (k:∀ f∈T,(∀ a∈A f,∀ b∈A f,¬ H a b)/\T.erase f⊆A f/\∃ a∈A f,G f a) (F:Finset (Finset (Fin n))) (l:∀ M∈F,2<=M.card/\aQ n D T M):J.card+F.card+(al n D).card<=T.card+bd n D:=by
 have m:=na d h.1 e c T J A j k;have p:=eZ h.1 T F l;have q:(du n D T).card<=(aW n D (ao n D T)).card:=
  _cl (_fs _ _)
 have r:=co h T (by rw[cs d e];simp);have s:=cZ h.1 b g T;have t:=_cl (inter_subset_left:T∩al n D⊆T);omega
end L3bGen
section L3bTri
variable {n : ℕ} {G H : Fin n → Fin n → Prop} {D : Dag}
lemma pk (hG:bJ G) (h:ai n D) (hC:sem_Umbrella n G H D) (b:Fin n->ℕ) (hb:aM n D b) {pos:Fin n->ℕ×_d} (P:bA n G D pos) (T J:Finset (Fin n)) (A:Fin n->Finset (Fin n)) (hJ:∀ i∈J,i∈aa n D/\(∃ a∈T,G i a)/\∀ f∈T,∃ a∈A f,G i a) (hA:∀ f∈T,(∀ a∈A f,∀ b∈A f,¬ H a b)/\T.erase f⊆A f/\∃ a∈A f,G f a) (F:Finset (Finset (Fin n))) (hF:∀ M∈F,M.card=2/\aQ n D T M) (hT3:T.card=3) (hbud:T.card+bd n D<=J.card+F.card+(al n D).card):(∀ w,¬ T⊆ag n D w) /\(∀ t∈T,aW n D (ao n D {t})=∅ /\∃ e1,∀ e∈af n D t,e=e1\/e∈J.image pos) /\∀ u∈aj n D b,(ag n D u.1∩T).Nonempty:=by
 classical
 have p:=h.1;obtain⟨Q,q⟩:=e6 P T J (fun i hi=>⟨(hJ i hi).1,(hJ i hi).2.1⟩);have hex:∀ f∈T,∃ e:ℕ×_d,e.1<D.length/\cR D e.1=true /\f∈ag n D (aw D e)/\f∉ag n D (n+e.1)/\Disjoint (ag n D (aw D e)) (A f):=by{intro f k;obtain⟨j,s,R,h2,h4,h5,h6⟩:=fm hG p hC (A f) (hA f k).1 f (hA f k).2.2;exact⟨(j,s),R,h2,h4,h5,h6⟩};choose! w hw using hex;have S:Set.InjOn w T:=by{intro f k g l hfg;by_contra hne;exact _dl.1 (hw f k).2.2.2.2 (hfg▸(hw g l).2.2.1) ((hA f k).2.1 (_me.2 ⟨fun h=>hne h.symm,l⟩))};have U:Disjoint (J.image pos) (T.image w):=by{rw[_dl];intro e m r;obtain⟨i,hi,rfl⟩:=_mg.1 m;obtain⟨f,k,B⟩:=_mg.1 r;obtain⟨a,ha,hia⟩:=(hJ i hi).2.2 f k;exact _dl.1 (hw f k).2.2.2.2 (B▸(P.1 i (hJ i hi).1).2.2.1 a hia) ha};have x:T.image w⊆aE n D (ao n D T):=by{intro e he;obtain⟨f,k,rfl⟩:=_mg.1 he;obtain⟨R,h2,h4,h5,h6⟩:=hw f k;refine fL.2 ⟨R,⟨f,_mn.2 ⟨h4,k⟩⟩,?_⟩;rintro⟨g,l⟩;rw[_mn] at l;have hgs:g∈ag n D (aw D (w f)):=cr p R h2 (w f).2 l.1;exact _dl.1 h6 hgs ((hA f k).2.1 (_me.2 ⟨fun h=>h5 (h▸l.1),l.2⟩))};have Z:∀ M∈F,2<=M.card/\aQ n D T M:=fun M C=>⟨by rw[(hF M C).1],(hF M C).2⟩;have h2:=eZ p T F Z;have h3:(du n D T).card<=(aW n D (ao n D T)).card:=
  _cl (_fs _ _)
 have h4:=co h T (by rw[cs hG hC];simp);have h5:=cZ p b hb T;have h6:=_cl (inter_subset_left:T∩al n D⊆T);have hEx:=_cl (union_subset Q x);rw[_cud U,q,_cij S] at hEx;have h0:J.image pos∪T.image w=aE n D (ao n D T):=
  _eqc (union_subset Q x) (by
   rw[_cud U,q,_cij S];omega)
 have W:du n D T=aW n D (ao n D T):=
  _eqc (_fs _ _) (by omega)
 have d:∀ w',¬ T⊆ag n D w':=by
  intro w' hTw;have hnot:T∉F:=fun hTF=>by have:=(hF T hTF).1;omega
  have:=eZ p T (insert T F) (fun M C=>by
   rcases _mi.1 C with rfl|C;{exact⟨by omega,⟨w',inter_eq_right.2 hTw⟩⟩}
   · exact Z M C)
  rw[_cin hnot] at this;omega
 have E:∀ u∈aj n D b,(ag n D u.1∩T).Nonempty:=by
  have h7:=d9 p b hb T;have h8:=bS p b hb;have heq:(aj n D b).filter (fun u=>(ag n D u.1∩T).Nonempty)=aj n D b:=
   _eqc (_fs _ _) (by omega)
  intro u hu;rw[<- heq] at hu;exact(_mf.1 hu).2
 have h9:Set.InjOn (fun j=>ag n D (n+j)∩T) (du n D T):=by{have hd:F⊆(du n D T).image (fun j=>ag n D (n+j)∩T):=by{intro M C;obtain⟨j,hj,hjM⟩:=lp p (Z M C).1 (hF M C).2;exact _mg.2 ⟨j,hj,hjM⟩};have:=_cl hd;exact card_image_iff.1 (le_antisymm card_image_le (by omega))};have c:∀ {t:Fin n} {v:ℕ},t∈T->t∈ag n D v->v∈ao n D T:=fun z hv=>cC.2 ⟨_,_mn.2 ⟨hv,z⟩⟩;refine⟨d,fun t z=>⟨?_,w t,fun e he=>?_⟩,E⟩
 · rw[eq_empty_iff_forall_notMem]
   intro j hj;rw[aW,_mf,mem_range] at hj;obtain⟨hjl,hj1,hh,hk⟩:=hj;rw[b7] at hj1 hh hk;have I:j∈du n D T:=by{rw[W,aW,_mf,mem_range];exact⟨hjl,c z hj1,c z hh,c z hk⟩};have K:2<=(ag n D (n+j)∩T).card:=(_mf.1 I).2;obtain⟨j0,-,-,X,L,-,hstr⟩:=ew p T _ K (n+j) rfl;have hjj:j0=j:=h9 (_mf.2 ⟨L,by rw[X];exact K⟩) I X;subst hjj;have hlt:∀ v,(ag n D v∩T).card<3:=by{intro v;by_contra hc;exact d v (inter_eq_right.1 (_eqc inter_subset_right (by omega)))};rcases hstr with ⟨-,hl,-⟩|⟨-,hl,hB1,hU,-,-⟩
   · have:=card_lt_card hl
     have:=hlt (cj D j0);omega
   · have hcA:=card_lt_card hl
     have hcB:=card_lt_card hB1;have:=hlt (n+j0);have hA':({t}:Finset (Fin n))=ag n D (cj D j0)∩T:=
      _eqc (singleton_subset_iff.2 (_mn.2 ⟨hh,z⟩)) (by rw[_cs];omega)
     have hB':({t}:Finset (Fin n))=ag n D (ck D j0)∩T:=
      _eqc (singleton_subset_iff.2 (_mn.2 ⟨hk,z⟩)) (by rw[_cs];omega)
     rw[<- hU,<-hA',<-hB',union_self,_cs] at K;omega
 · obtain⟨m,r,he3⟩:=ak.1 he
   have Y:=cY p he;have y:e∈aE n D (ao n D T):=by
    refine fL.2 ⟨m,⟨t,_mn.2 ⟨r,z⟩⟩,?_⟩;rintro⟨g,l⟩;rw[_mn] at l;have hop:∀ s,g∈ag n D (aw D (e.1,s)):=fun s=>cr p m Y s l.1;have I:e.1∈du n D T:=by
     rw[W,aW,_mf,mem_range];refine⟨m,c l.2 l.1,c l.2 ?_,c l.2 ?_⟩
     · have:=hop false
       rwa[aX] at this
     · have:=hop true
       rwa[bh] at this
    have K:2<=(ag n D (n+e.1)∩T).card:=(_mf.1 I).2;have hm:ag n D (n+e.1)∩T⊆T.erase t:=fun a ha=>
     _me.2 ⟨fun N=>he3 (N▸(_mn.1 ha).1),(_mn.1 ha).2⟩
    have heqE:=_eqc hm (by rw[card_erase_of_mem z,hT3];omega);apply d (aw D e);intro a ha;by_cases N:a=t;{rw[N];exact r}
    · have:a∈ag n D (n+e.1)∩T:=by
       rw[heqE];exact _me.2 ⟨N,ha⟩
      exact cr p m Y e.2 (_mn.1 this).1
   rw[<- h0,_mu] at y;rcases y with R|R;{exact Or.inr R}
   · obtain⟨f,k,B⟩:=_mg.1 R
     left;by_cases hft:f=t;{rw[<- B,hft]}
     · exfalso
       exact _dl.1 (hw f k).2.2.2.2 (B▸r) ((hA f k).2.1 (_me.2 ⟨fun h=>hft h.symm,z⟩))
end L3bTri
namespace _B
def e8:_F (ℕ×ℕ):=[(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
def bw (x:O->_d):Prop:=∃ u v:O,(u.val,v.val)∈e8/\x u=true/\x v=true
abbrev aO (u v:O):Prop:=(u.val,v.val)∈e8\/(v.val,u.val)∈e8
def ab (u v:O):_d:=(([1408,8832,12544,6272,11264,5632,2816,11,69,98,49,88,44,22]:_F ℕ).getD u.val 0).testBit v.val
lemma ad:∀ u v:O,ab u v=true↔aO u v:=by decide +kernel
lemma bl {u v:O}:aO u v->aO v u:=Or.symm
lemma dv (u:O):¬ aO u u:=by revert u;decide +kernel
lemma ce (x:O->_d):bw x↔∃ u v:O,aO u v/\x u=true/\x v=true:=by
 constructor;{rintro⟨u,v,h,a,b⟩;exact⟨u,v,Or.inl h,a,b⟩}
 · rintro⟨u,v,h|h,a,b⟩
   · exact⟨u,v,h,a,b⟩
   · exact⟨v,u,h,b,a⟩
lemma iY (v:O):(univ.filter (fun u=>aO v u)).card=3:=by
 rw[filter_congr (fun u _=>(ad v u).symm)];revert v;decide +kernel
lemma gT (u v:O) (h:u≠v):(univ.filter (fun z=>aO u z/\aO v z)).card<=1:=by
 rw[filter_congr (fun z _=>and_congr (ad u z).symm (ad v z).symm)];revert u v;decide +kernel
lemma oC:∀ v w:O,v≠w ->∃ z,ab v z=true/\ab w z=false:=by decide +kernel
lemma dT (v w:O) (h:v≠w):∃ z,aO v z/\¬ aO w z:=by
 obtain⟨z,b,c⟩:=oC v w h;refine⟨z,(ad v z).mp b,fun a=>?_⟩;rw[<- ad,c] at a;exact _fnt a
def eB (S:o):Prop:=∀ u v:O,aO u v->u∈S\/v∈S
def dH (I:o):Prop:=∀ u∈I,∀ v∈I,¬ aO u v
lemma jy (I:o):dH I↔eB (univ\I):=by
 constructor
 · intro h u v a
   by_contra b;simp only[_md,_mv,true_and,not_or,not_not] at b;exact h u b.1 v b.2 a
 · intro h u d v e a
   rcases h u v a with c|c <;> simp[d,e] at c
def gK:_F (O×O):=[(0,7),(1,13),(2,8),(3,12),(4,11),(5,10),(6,9)]
def cp (v:O):O:=Fin.ofNat 14 (([7,13,8,12,11,10,9,0,2,6,5,4,3,1]:_F ℕ).getD v.val 0)
lemma pZ:∀ e∈gK,aO e.1 e.2:=by decide +kernel
lemma gU:∀ v:O,ab v (cp v)=true/\cp (cp v)=v:=by
 decide +kernel
lemma p5:∀ v:O,(v,cp v)∈gK\/(cp v,v)∈gK:=by
 decide +kernel
lemma iZ:(∀ e∈gK,aO e.1 e.2)/\∀ v:O,aO v (cp v) /\cp (cp v)=v/\((v,cp v)∈gK\/(cp v,v)∈gK):=⟨pZ,fun v=>⟨(ad _ _).mp (gU v).1,(gU v).2,p5 v⟩⟩
lemma eR (S:o) (h:eB S):7<=S.card:=by
 have a:(univ:o)⊆S∪S.image cp:=by{intro v _;rcases h v (cp v) (iZ.2 v).1 with b|b;{exact mem_union_left _ b};{exact mem_union_right _ (_mg.mpr ⟨_,b,(iZ.2 v).2.1⟩)}};have c:=_cl a;have d:=card_union_le S (S.image cp);have e:=card_image_le (s:=S) (f:=cp);simp only[card_univ,Fintype.card_fin] at c;omega
def cI (σ:_ep (O)):Prop:=∀ u v:O,aO (σ u) (σ v)↔aO u v
lemma lt {σ:_ep (O)} (h:∀ u v:O,ab (σ u) (σ v)=ab u v):cI σ:=fun u v=>by
 rw[<- ad,<-ad u v,h]
lemma p6:cI 1:=fun _ _=>Iff.rfl
lemma p7 {σ τ:_ep (O)} (hσ:cI σ) (hτ:cI τ):cI (σ*τ):=fun u v=>(hσ (τ u) (τ v)).trans (hτ u v)
lemma lZ (σ:_ep (O)) (hσ:cI σ) (x:O->_d):bw (fun i=>x (σ i))↔bw x:=by
 rw[ce,ce];constructor;{rintro⟨u,v,h,a,b⟩;exact⟨σ u,σ v,(hσ u v).mpr h,a,b⟩}
 · rintro⟨u,v,h,a,b⟩
   refine⟨σ.symm u,σ.symm v,?_,by simpa using a,by simpa using b⟩;rw[<- hσ,Equiv.apply_symm_apply,Equiv.apply_symm_apply];exact h
lemma l5 {σ:_ep (O)} (hσ:cI σ) {I:o} (c:dH I):dH (I.image σ):=by
 intro u d v e;obtain⟨a,f,rfl⟩:=_mg.mp d;obtain⟨b,g,rfl⟩:=_mg.mp e;rw[hσ a b];exact c a f b g
def k6 (l:_F ℕ) (v:O):O:=Fin.ofNat 14 (l.getD v.val 0)
def d3:_F (o):=[{0,1,2,3,4,5,6},{0,1,2,3,4,5},{0,1,2,3,4},{0,1,2,5,11},{0,1,2,3},{0,1,2,5},{0,1,2,11},{0,1,11,12},{0,1,2},{0,1,3},{0,1,11},{0,1},{0,9},{0}]
def bT (n:Fin 15):o:=((∅:o):: d3).getD n.val ∅
lemma fM {R:o} (h:R∈d3):∃ n:Fin 15,n≠0/\bT n=R:=by
 obtain⟨i,a,rfl⟩:=List.mem_iff_getElem.mp h;have a':i<14:=a;refine⟨⟨i+1,by omega⟩,by simp[Fin.ext_iff],?_⟩;show((∅:o):: d3).getD (i+1) ∅=d3[i];rw[List.getD_cons_succ];exact _lge _ _ a
abbrev qz (I:o):Prop:=∀ u∈I,∀ v∈I,ab u v=false
lemma pl {I:o}:qz I↔dH I:=by
 refine forall₂_congr fun u _=>forall₂_congr fun v _=>?_;rw[<- ad,Bool.not_eq_true]
lemma mN (R:o) (h:R∈d3):(R.card=7/\R={0,1,2,3,4,5,6})\/(R.card=6/\R={0,1,2,3,4,5}) \/(R.card=5/\(R={0,1,2,3,4}\/R={0,1,2,5,11})) \/(R.card=4/\(R={0,1,2,3}\/R={0,1,2,5}\/R={0,1,2,11} \/R={0,1,11,12})) \/(R.card=3/\(R={0,1,2}\/R={0,1,3}\/R={0,1,11})) \/(R.card=2/\(R={0,1}\/R={0,9}))\/(R.card=1/\R={0}):=by
 obtain⟨n,a,rfl⟩:=fM h;revert n;decide +kernel
def sh:_F (_F ℕ):=[[0,1,2,3,4,5,6,7,8,9,10,11,12,13],[1,0,4,3,5,6,2,7,13,8,9,12,11,10],[0,3,2,1,5,4,6,7,8,11,10,9,13,12],[0,1,5,3,6,2,4,7,10,13,8,11,12,9],[0,2,1,6,4,5,3,8,7,12,10,11,9,13],[0,2,4,6,1,3,5,8,10,12,7,9,11,13],[0,2,3,6,5,4,1,8,7,13,10,9,11,12],[1,3,5,0,2,4,6,7,9,11,13,8,10,12],[1,2,5,4,3,0,6,13,9,8,7,11,10,12],[1,6,0,5,2,4,3,9,7,11,13,12,10,8],[1,6,2,5,0,3,4,9,13,11,7,10,12,8],[11,13,8,10,12,7,9,4,6,1,3,5,0,2],[11,13,12,10,8,9,7,4,3,1,6,0,5,2],[11,7,13,12,9,8,10,3,4,0,6,5,2,1],[1,2,3,4,5,6,0,13,7,8,9,10,11,12],[2,0,1,6,3,5,4,8,13,10,12,11,9,7],[13,8,7,12,10,11,9,2,1,6,4,5,3,0],[8,13,7,12,9,11,10,2,0,4,6,5,3,1],[8,13,9,12,7,10,11,2,6,4,0,3,5,1],[8,7,13,10,9,11,12,0,2,3,6,5,4,1]]
def kg (k:Fin 20):O->O:=k6 (sh.getD k.val [])
lemma p8:∀ k:Fin 20,∀ a b:O,kg k a=kg k b->a=b:=by
 decide +kernel
lemma p9:∀ k:Fin 20,∀ u v:O,ab (kg k u) (kg k v)=ab u v:=by decide +kernel
lemma p_ (k:Fin 20):∃ τ:_ep (O),cI τ/\⇑τ=kg k:=by
 have c:Function.Injective (kg k):=fun a b h=>p8 k a b h;exact⟨Equiv.ofBijective (kg k) ⟨c,Finite.injective_iff_surjective.mp c⟩,lt fun u v=>p9 k u v,rfl⟩
def qc:_F (_F ℕ):=[[0,1,9,7,10,8,14,19,17,13,18,12,11,16],[],[],[0,0,0,0,0,0,1],[],[0,0,0,0,0,2,1],[0,0,0,2,5,0,6],[],[],[0,0,0,0,15,0,4],[0,0,0,0,7,3,1],[0,0,0,0,0,3],[0,0,0,0,5,3,1,0,0,0,0,0,1],[0,0,9,2,10,0,0,0,0,0,0,12,11,13],[0,0,4,2,5,8,6,0,0,0,0,2,4,3]]
def qA (n:Fin 15) (w:O):Fin 20:=Fin.ofNat 20 ((qc.getD n.val []).getD w.val 0)
lemma qP:∀ n:Fin 15,∀ w:O,w∉bT n ->qz (insert w (bT n)) ->(insert w (bT n)).image (kg (qA n w))∈d3:=by decide +kernel
lemma rp (R:o) (a:R=∅\/R∈d3) (w:O) (b:w∉R) (c:dH (insert w R)):∃ τ:_ep (O),cI τ/\(insert w R).image τ∈d3:=by
 obtain⟨n,rfl⟩:∃ n:Fin 15,bT n=R:=by{rcases a with rfl|a;{exact⟨0,rfl⟩};{obtain⟨n,-,h⟩:=fM a;exact⟨n,h⟩}};obtain⟨τ,hτ,d⟩:=p_ (qA n w);exact⟨τ,hτ,by rw[d];exact qP n w b (pl.mpr c)⟩
lemma qQ (I:o):dH I ->I=∅\/∃ σ:_ep (O),cI σ/\I.image σ∈d3:=by
 induction I using Finset.induction_on with
 | empty=>intro _;exact Or.inl rfl
 | insert v J e ih=>
  intro c;have f:dH J:=fun u g w i=>
   c u (mem_insert_of_mem g) w (mem_insert_of_mem i)
  obtain⟨σ,hσ,R,j,a⟩:∃ σ:_ep (O),cI σ /\∃ R,(R=∅\/R∈d3)/\J.image σ=R:=by{rcases ih f with h|⟨σ,hσ,b⟩;{exact⟨1,p6,∅,Or.inl rfl,by simp[h]⟩};{exact⟨σ,hσ,_,Or.inr b,rfl⟩}};have d:(insert v J).image σ=insert (σ v) R:=by rw[image_insert,a]
  have k:σ v∉R:=by rw[<- a];simpa using e
  have l:dH (insert (σ v) R):=by rw[<- d];exact l5 hσ c
  obtain⟨τ,hτ,b⟩:=rp R j (σ v) k l;refine Or.inr ⟨τ*σ,p7 hτ hσ,?_⟩;rw[Equiv.Perm.coe_mul,<-image_image,d];exact b
lemma jW (I:o) (b:dH I) (a:I.Nonempty):∃ σ:_ep (O),cI σ/\I.image σ∈d3:=by
 rcases qQ I b with h|h;{exact absurd h a.ne_empty};{exact h}
lemma k8:¬ bw (fun _=>false):=by
 rintro⟨u,v,-,h,-⟩;exact _fnt h
lemma fe (v:O):¬ bw (fun i=>decide (i=v)):=by
 rw[ce];rintro⟨a,b,c,d,e⟩;simp only[decide_eq_true_eq] at d e;subst d;subst e;exact dv _ c
lemma iL (u v:O):bw (fun i=>decide (i=u)||decide (i=v))↔aO u v:=by
 rw[ce];constructor
 · rintro⟨a,b,c,d,e⟩
   simp only[Bool.or_eq_true,decide_eq_true_eq] at d e;rcases d with rfl|rfl <;> rcases e with rfl|rfl;{exact absurd c (dv _)};{exact c};{exact bl c};{exact absurd c (dv _)}
 · intro h;exact⟨u,v,h,by simp,by simp⟩
lemma fn {u v:O} (h:aO u v):bw (fun i=>decide (i=u)||decide (i=v)):=(iL u v).mpr h
lemma k9 (i:O):∃ x y:O->_d,(∀ k,k≠i->x k=y k)/\¬ bw x/\bw y:=by
 refine⟨fun k=>decide (k=cp i),fun k=>decide (k=i)||decide (k=cp i),?_,fe _,fn (iZ.2 i).1⟩;intro k a;simp[a]
def aq (D:Dag):Prop:=∀ x:O->_d,val D x (bH 14 D)=true↔bw x
lemma k_ (C:Circuit) (a:Monotone2 C) (c:∀ x:O->_d,C.eval (_of x)=true↔bw x):∃ D:Dag,ai 14 D/\D.length<=C.size/\aq D:=by
 have f:aO (0:O) 7:=V
 obtain⟨D,j,d,e⟩:=fV (n:=14) C a (by
  intro b;cases b;{exact⟨_,by rw[Ne,_nf];exact(c _).2 (fn f)⟩}
  · exact⟨fun _=>false,fun h=>k8 ((c _).1 h)⟩)
  (by
   intro i;refine⟨fun k=>decide (k=i),fun h=>fe i ((c _).1 ?_)⟩
   rw[h];simp)
  (by
   intro i;obtain⟨x,y,g,l,m⟩:=k9 i;refine⟨x,y,g,fun h=>l ((c x).1 ?_)⟩
   rw[h];exact(c y).2 m)
 exact⟨D,j,d,fun x=>by rw[e x];exact c x⟩
lemma fN {D:Dag} (a:aq D):ag 14 D (bH 14 D)=∅:=eq_empty_iff_forall_notMem.2 (fun v b=>fe v ((a _).1 (ee.1 b)))
lemma jj (σ:_ep (O)) (hσ:cI σ) {D:Dag} (h:ai 14 D) (a:aq D):ai 14 (bo σ D)/\aq (bo σ D) /\(bo σ D).length=D.length /\ap 14 (bo σ D)=ap 14 D /\bd 14 (bo σ D)=bd 14 D/\bL 14 (bo σ D)=bL 14 D /\al 14 (bo σ D)=(al 14 D).image σ /\aa 14 (bo σ D)=(aa 14 D).image σ:=by
 refine⟨fd σ h,fun x=>?_,cc σ D,eJ σ D,j8 σ h.1,j9 σ h.1,fZ σ h.1,ep σ h.1⟩;rw[fI σ h.1 h.2.2 x,a];exact lZ σ hσ x
lemma i6 (D:Dag):eB (al 14 D)↔dH (aa 14 D):=by
 have h:univ\aa 14 D=al 14 D:=by simp[aa]
 rw[jy,h]
lemma nV {D:Dag} (h:ai 14 D) (d:aq D) (e:dH (aa 14 D)) (c:(aa 14 D).Nonempty):∃ D':Dag,ai 14 D'/\aq D'/\D'.length=D.length /\ap 14 D'=ap 14 D/\bd 14 D'=bd 14 D /\bL 14 D'=bL 14 D/\(al 14 D').card=(al 14 D).card /\aa 14 D'∈d3:=by
 obtain⟨σ,hσ,b⟩:=jW _ e c;obtain⟨f,g,i,j,k,l,m,n⟩:=jj σ hσ h d;refine⟨bo σ D,f,g,i,j,k,l,?_,?_⟩;{rw[m,_cii _ σ.injective]};{rw[n];exact b}
lemma go {D:Dag} (h:ai 14 D) (a:D.length<=26):ap 14 D+13=D.length/\ap 14 D<=13:=by
 have:=iC h;omega
lemma iM {D:Dag} (h:ai 14 D) (a:D.length<=26) (b:O->ℕ) (d:aM 14 D b) (c:eB (al 14 D)):7<=(al 14 D).card/\(al 14 D).card<=bd 14 D /\bd 14 D<=ap 14 D/\ap 14 D<=13:=⟨eR _ c,dX h.1 b d,dC 14 D,(go h a).2⟩
lemma jz {D:Dag} (h:ai 14 D) (a:D.length<=26) (b:O->ℕ) (d:aM 14 D b) (c:eB (al 14 D)):(aa 14 D).Nonempty/\(aa 14 D).card<=7:=by
 obtain⟨f,g,i,e⟩:=iM h a b d c;have j:=aV 14 D;exact⟨_cp.1 (by omega),by omega⟩
lemma nc:∀ u v:O,∃ a,ab u a=true/\a≠v:=by decide +kernel
lemma aK:bJ (fun u v:O=>aO u v):=⟨fun _ _=>bl,dv,dT,fun u v=>by
 obtain⟨a,b,c⟩:=nc u v
 exact⟨a,(ad u a).mp b,c⟩⟩
lemma aC {D:Dag} (a:aq D):dg 14 (fun u v:O=>aO u v) D:=ju aK (fun x=>(a x).trans (ce x))
lemma bt {D:Dag} (h:ai 14 D) (a:aq D):∃ b:O->ℕ,aM 14 D b:=dK aK h.1 (aC a)
lemma fo {D:Dag} (h:ai 14 D) (b:aq D):eB (al 14 D):=fun _ _ a=>fu aK h (aC b) a
lemma kI (C:Circuit) (d:Monotone2 C) (n:∀ x:O->_d,C.eval (_of x)=true↔bw x) (i:C.size<=26):∃ D:Dag,ai 14 D/\aq D/\D.length<=26 /\ap 14 D+13=D.length/\ap 14 D<=13 /\7<=(al 14 D).card/\(al 14 D).card<=bd 14 D /\bd 14 D<=ap 14 D/\aa 14 D∈d3:=by
 obtain⟨D0,h,j,e⟩:=k_ C d n;have f:D0.length<=26:=by omega
 obtain⟨b,p⟩:=bt h e;have c:=fo h e;obtain⟨k,-⟩:=jz h f b p c;obtain⟨D,g,l,r,s,t,-,u,q⟩:=nV h e ((i6 D0).mp c) k;have f':D.length<=26:=by omega
 obtain⟨b',p'⟩:=bt g l;obtain⟨p1,p2,p3,p4⟩:=iM g f' b' p' (fo g l);exact⟨D,g,l,f',(go g f').1,p4,p1,p2,p3,q⟩
lemma nW:∀ x a b:O,x≠a->x≠b->ab a b=false ->∃ y,ab x y=true/\ab y a=false/\ab y b=false:=by decide +kernel
lemma jk:∀ i x:O,∃ r s,r≠s/\ab i r=true /\ab i s=true/\r≠x/\s≠x:=by decide +kernel
lemma kh:∀ r s t i:O,r≠s->ab i r=true->ab i s=true ->ab t r=true->ab t s=true->t=i:=by decide +kernel
lemma aG {u v:O}:ab u v=false↔¬ aO u v:=by
 rw[<- ad,Bool.not_eq_true]
lemma bR {D:Dag} (h:ai 14 D) (g:aq D) {x a b:O} (d:x≠a) (f:x≠b) (c:¬ aO a b):∃ e,e∈af 14 D x/\a∉ag 14 D (aw D e)/\b∉ag 14 D (aw D e):=by
 obtain⟨y,i,j,k⟩:=nW x a b d f (aG.mpr c);exact jJ aK h.1 (aC g) c ((ad x y).mp i) (aG.mp j) (aG.mp k)
lemma gd {D:Dag} (h:ai 14 D) (hD:aq D) {i x:O} (hi:i∈aa 14 D) (N:x≠i) {e:ℕ×_d} (he:af 14 D i={e}) (hY:am e∈af 14 D x) (P:(af 14 D x).card<=2):∃ Z,Z≠am e/\af 14 D x={am e,Z}/\(∀ t,t≠x->Z∉af 14 D t) /\∀ i'∈aa 14 D,∀ e',af 14 D i'={e'}->Z.1≠e'.1:=by
 have hG:=aK;have hC:=aC hD;have hS:=h.1;have j:∀ i'∈aa 14 D,∀ e',af 14 D i'={e'} ->ag 14 D (aw D e')={i'}/\ag 14 D (14+e'.1)=∅ /\∀ q,aO i' q->q∈ag 14 D (aw D (am e')):=by{intro i' hi' e' he';obtain⟨e0,-,-,v,w,E,Q,-⟩:=ci hG h hC hi';have m:({e'}:Finset (ℕ×_d))={e0}:=he'.symm.trans Q;have R:e'=e0:=singleton_injective m;subst R;exact⟨v,w,E⟩};obtain⟨F,-,y⟩:=j i hi e he;obtain⟨r,s,S,n,z,G,T⟩:=jk i x;rw[ad] at n z;obtain⟨Z,U,W⟩:=kb hG hS hC (x:=x) (a:=r) (Ne.symm G);have A:Z≠am e:=by{rintro rfl;exact W (y r n)};have X:af 14 D x={am e,Z}:=by
  symm;refine _eqc (fun f H=>?_) ?_
  · rw[_mi,_ms] at H
    rcases H with rfl|rfl;{exact hY};{exact U}
  · rw[_c2 (Ne.symm A)];exact P
 have c:∀ t,t≠x->Z∉af 14 D t:=by{intro t Y B;have I:∀ q,q≠x->q∈ag 14 D (aw D (am e))->aO q t:=by{intro q h0 hq;by_contra h3;obtain⟨f,H,m,R⟩:=bR h hD (x:=x) (a:=q) (b:=t) (Ne.symm h0) (Ne.symm Y) h3;rw[X,_mi,_ms] at H;rcases H with rfl|rfl;{exact m hq};{exact R (ak.mp B).2.1}};have h4:=bl (I r G (y r n));have h5:=bl (I s T (y s z));have h6:t=i:=kh r s t i S ((ad _ _).mpr n) ((ad _ _).mpr z) ((ad _ _).mpr h4) ((ad _ _).mpr h5);rw[h6,he,_ms] at B;have J:=(ak.mp U).2.1;rw[B,F,_ms] at J;exact N J};refine⟨Z,A,X,c,?_⟩;intro i' hi' e' he' l;obtain⟨-,hemp',y'⟩:=j i' hi' e' he';have N':x≠i':=by
  intro P;have m:(af 14 D x).card=2:=by rw[X,_c2 (Ne.symm A)]
  rw[P,he',_cs] at m;omega
 rcases ka l.symm with m|m;{exact c i' (Ne.symm N') (by rw[he',_ms];exact m)}
 · obtain⟨r',s',S',n',z',G',-⟩:=jk i' x
   rw[ad] at n';refine c r' G' (ak.mpr ⟨(ak.mp U).1,?_,?_⟩);{rw[m];exact y' r' n'};{rw[l,hemp'];exact notMem_empty _}
def aU (i:O):o:=univ.filter (fun a=>decide (a.val<7)≠decide (i.val<7))
def aA (i:O):o:=univ.filter (fun a=>aO i a)
lemma kS:∀ a b:O,ab a b=true ->decide (a.val<7)≠decide (b.val<7):=by decide +kernel
lemma dB (i:O):∀ a∈aU i,∀ b∈aU i,¬ aO a b:=by
 intro a d b e c;simp only[aU,_mf,_mv,true_and] at d e;have f:=kS a b ((ad a b).mpr c);cases g:decide (a.val<7)<;> cases h:decide (b.val<7)<;>
  cases j:decide (i.val<7)<;> simp_all
lemma nd {i a:O} (h:aO i a):a∈aU i:=by
 simp only[aU,_mf,_mv,true_and];exact(kS i a ((ad i a).mpr h)).symm
lemma dM (u v:O) (h:u≠v) (P:o):((univ.filter (fun z=>aO u z)∩P)∩ (univ.filter (fun z=>aO v z)∩P)).card<=1:=by
 refine le_trans (_cl (fun z a=>?_)) (gT u v h);simp only[_mn,_mf,_mv,true_and] at a;exact _mf.mpr ⟨_mv z,a.1.1,a.2.1⟩
def gV (u v:Fin 10):_d:=(([112,400,672,832,3,5,9,6,10,12]:_F ℕ).getD u.val 0).testBit v.val
abbrev bI (u v:Fin 10):Prop:=gV u v=true
lemma eS:bJ bI:=⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩
lemma mO:∀ I:Finset (Fin 10),(∀ u∈I,∀ v∈I,gV u v=false) ->5<=I.card->(∀ q∈I,4<=q.val) /\((4∈I/\5∈I)\/(4∈I/\7∈I)\/(5∈I/\7∈I)):=by decide +kernel
lemma lu:∀ i:Fin 10,4<=i.val ->∃ a∈({0,1,2}:Finset (Fin 10)),bI i a:=by decide +kernel
lemma jl {D:Dag} (h:ai 10 D) (c:dg 10 bI D):∀ u∈aa 10 D,∀ v∈aa 10 D,gV u v=false:=by
 intro u d v e;by_contra b;rw[_nf] at b;rcases fu eS h c (u:=u) (v:=v) b with a|a;{exact aN.mp d a};{exact aN.mp e a}
lemma jO {D:Dag} (h:ai 10 D) (g:dg 10 bI D):6<=bd 10 D:=by
 by_contra s;obtain⟨b,n⟩:=dK eS h.1 g;have v:=dX h.1 b n;have k:=aV 10 D;obtain⟨l,d⟩:=mO _ (jl h g) (by omega);obtain⟨pos,e⟩:=bQ eS h g;have p:=gS eS h g b n ({0,1,2}:Finset (Fin 10));obtain⟨f,t⟩:=e6 e ({0,1,2}:Finset (Fin 10)) (aa 10 D) (fun i j=>⟨j,lu i (l i j)⟩);have u:=_cl f;have m:({0,1,2}:Finset (Fin 10)).card=3:=V;have q:∀ i∈aa 10 D,∀ a,bI i a->a∈ag 10 D (aw D (pos i)):=fun i j=>(e.1 i j).2.2.1;have r:2<=(aW 10 D (ao 10 D ({0,1,2}:Finset (Fin 10)))).card:=by{rcases d with ⟨i4,i5⟩|⟨i4,i7⟩|⟨i5,i7⟩;{exact eA h.1 m (a:=0) (b:=1) (c:=2) V V V V V V (q 4 i4 0 V) (q 4 i4 1 V) (q 5 i5 0 V) (q 5 i5 2 V)};{exact eA h.1 m (a:=1) (b:=0) (c:=2) V V V V V V (q 4 i4 1 V) (q 4 i4 0 V) (q 7 i7 1 V) (q 7 i7 2 V)};{exact eA h.1 m (a:=2) (b:=0) (c:=1) V V V V V V (q 5 i5 2 V) (q 5 i5 0 V) (q 7 i7 2 V) (q 7 i7 1 V)}};omega
lemma l_ {G:Fin 10->Fin 10->Prop} (σ:_ep (Fin 10)) (hσ:∀ u v,G u v↔bI (σ u) (σ v)) {D:Dag} (h:ai 10 D) (d:dg 10 G D):dg 10 bI (bo σ D):=by
 refine ju eS (fun x=>?_);rw[fI σ h.1 h.2.2 x,kO d];unfold cN;constructor
 · rintro⟨u,v,a,b,c⟩
   exact⟨σ u,σ v,(hσ u v).mp a,b,c⟩
 · rintro⟨u,v,a,b,c⟩
   exact⟨σ.symm u,σ.symm v,(hσ _ _).mpr (by simpa using a),by simpa using b,by simpa using c⟩
lemma rq:∀ x:Fin 10,x.val<4->∃ a b c:Fin 10,a≠b/\a≠c/\b≠c /\bI x a/\bI x b/\bI x c /\∀ i:Fin 10,bI x i->i=a\/i=b\/i=c:=by decide +kernel
lemma qd:∀ u t i i':Fin 10,u≠t->bI u i->bI t i ->bI u i'->bI t i'->i=i':=by decide +kernel
lemma oD:∀ q:Fin 10,q.val<4 ->gV q 4=true\/gV q 9=true:=by decide +kernel
lemma qR:∀ i:Fin 10,4<=i.val->i≠4->i≠9->∃ u a:Fin 10,bI u 4/\bI u i/\bI u a/\(4:Fin 10)≠a/\i≠a:=by decide +kernel
lemma si:∀ v:Fin 10,4<=v.val->∃ u t:Fin 10,u≠t/\u.val<4/\t.val<4 /\(∀ i:Fin 10,bI u i->4<=i.val/\i≠v) /\(∀ i:Fin 10,bI t i->4<=i.val/\i≠v):=by decide +kernel
lemma lv:(univ.filter (fun i:Fin 10=>4<=i.val)).card=6:=V
lemma qB {D:Dag} (h:ai 10 D) (w:dg 10 bI D) (b:Fin 10->ℕ) (y:aM 10 D b) {pos:Fin 10->ℕ×_d} (g:bA 10 bI D pos) (z:bd 10 D<=(al 10 D).card+1) {x:Fin 10} (k:x.val<4) (B:∀ i,bI x i->i∈aa 10 D):aW 10 D (ao 10 D {x})=∅ /\(∀ e∈aE 10 D (ao 10 D {x}),∃ i,bI x i/\e=pos i) /\∃ ρ∈aj 10 D b,x∈ag 10 D ρ.1:=by
 obtain⟨a,b',c,l,m,n,C,y',E,-⟩:=rq x k;have q:∀ i∈({a,b',c}:Finset (Fin 10)),bI x i:=by{intro i f;simp only[_mi,_ms] at f;rcases f with rfl|rfl|rfl;{exact C};{exact y'};{exact E}};obtain⟨d,F⟩:=e6 g ({x}:Finset (Fin 10)) ({a,b',c}:Finset (Fin 10)) (fun i f=>⟨B i (q i f),x,_mss x,eS.1 _ _ (q i f)⟩);have J:({a,b',c}:Finset (Fin 10)).card=3:=card_eq_three.mpr ⟨a,b',c,l,m,n,rfl⟩;have G:=_cl d;have j:=gS eS h w b y ({x}:Finset (Fin 10));have r:=co h ({x}:Finset (Fin 10)) (by rw[cs eS w,empty_inter]);rw[_cs] at j r;have H:=d9 h.1 b y ({x}:Finset (Fin 10));have I:(({x}:Finset (Fin 10))∩al 10 D).card<=1:=(_cl inter_subset_left).trans (by simp);refine⟨card_eq_zero.mp (by omega),fun e A=>?_,?_⟩
 · have s:=_eqc d (by omega)
   rw[<- s] at A;obtain⟨i,f,rfl⟩:=_mg.mp A;exact⟨i,q i f,rfl⟩
 · obtain⟨ρ,hρ⟩:=_cp.mp (by omega :0<((aj 10 D b).filter (fun u=>(ag 10 D u.1∩{x}).Nonempty)).card)
   rw[_mf] at hρ;obtain⟨v,t⟩:=hρ.2;rw[_mn,_ms] at t;exact⟨ρ,hρ.1,t.2▸t.1⟩
lemma qS {D:Dag} (h:ai 10 D) (e:dg 10 bI D) (b:Fin 10->ℕ) (f:aM 10 D b) {pos:Fin 10->ℕ×_d} (a:bA 10 bI D pos) (c:bd 10 D<=(al 10 D).card+1) {u t:Fin 10} (g:u≠t) (j:u.val<4) (k:t.val<4) (l:∀ i,bI u i->i∈aa 10 D) (m:∀ i,bI t i->i∈aa 10 D):False:=by
 obtain⟨mu,xu,ρu,hρu,cu⟩:=qB h e b f a c j l;obtain⟨mt,xt,ρt,hρt,ct⟩:=qB h e b f a c k m;have p:=bS h.1 b f;have hρ:ρu=ρt:=card_le_one.mp (by omega) ρu hρu ρt hρt;rw[<- hρ] at ct;have d:2<=aF D ρu.1:=by{unfold aj da at hρu;have:=(dW.mp (_mf.mp (_md.mp hρu).1).1).2;omega};obtain⟨e1,e2,n,a1,a2,b1,b2⟩:=mM eS h e mu mt cu ct d;obtain⟨i1,p1,q1⟩:=xu e1 a1;obtain⟨i1',p1',q1'⟩:=xt e1 a2;obtain⟨i2,p2,q2⟩:=xu e2 b1;obtain⟨i2',p2',q2'⟩:=xt e2 b2;have q:i1=i1':=a.2 i1 (l i1 p1) i1' (m i1' p1') (q1.symm.trans q1');have r:i2=i2':=a.2 i2 (l i2 p2) i2' (m i2' p2') (q2.symm.trans q2');rw[<- q] at p1';rw[<- r] at p2';have s:i1=i2:=qd u t i1 i2 g p1 p1' p2 p2';exact n (by rw[q1,q2,s])
lemma oE {D:Dag} (h:ai 10 D) (N:dg 10 bI D) (b:Fin 10->ℕ) (Y:aM 10 D b) {pos:Fin 10->ℕ×_d} (c:bA 10 bI D pos) (P:bd 10 D<=(al 10 D).card+2) (d:∀ i:Fin 10,4<=i.val->i∈aa 10 D) (T:Finset (Fin 10)) (a z i1 i2 x y w:Fin 10) (Z:T.card=3) (B:a∈T) (C:bI a z) (l:∀ u∈insert z (T.erase a),∀ v∈insert z (T.erase a),¬ bI u v) (m:∀ i:Fin 10,4<=i.val->∃ t∈T,bI i t) (f:∀ i:Fin 10,4<=i.val->(∀ t∈T.erase a,¬ bI i t)->i=z) (g:x∈T/\y∈T/\w∈T/\x≠y/\x≠w/\y≠w/\4<=i1.val/\4<=i2.val /\bI i1 x/\bI i1 y/\bI i2 x/\bI i2 w):Disjoint (ag 10 D (aw D (pos z))) (T.erase a):=by
 have Q:=gS eS h N b Y T;obtain⟨n,h0⟩:=e6 c T (univ.filter (fun i:Fin 10=>4<=i.val)) (fun i r=>⟨d i (_mf.mp r).2,m i (_mf.mp r).2⟩);have h6:=lv;have R:2<=(aW 10 D (ao 10 D T)).card:=by{obtain⟨hx,hy,hw,E,F,G,S,U,a1,a2,a3,a4⟩:=g;exact eA h.1 Z hx hy hw E F G ((c.1 i1 (d i1 S)).2.2.1 x a1) ((c.1 i1 (d i1 S)).2.2.1 y a2) ((c.1 i2 (d i2 U)).2.2.1 x a3) ((c.1 i2 (d i2 U)).2.2.1 w a4)};have H:=_eqc n (by omega);obtain⟨j,s,W,ht,s1,s2,I⟩:=fm eS h.1 N (insert z (T.erase a)) l a ⟨z,mem_insert_self _ _,C⟩;have e:(j,s)∈aE 10 D (ao 10 D T):=by{rw[fL];refine⟨W,⟨a,_mn.mpr ⟨s1,B⟩⟩,?_⟩;rintro⟨v,A⟩;rw[_mn] at A;have J:=cr h.1 W ht s A.1;by_cases p:v=a;{exact s2 (p▸A.1)};{exact _dl.mp I J (mem_insert_of_mem (_me.mpr ⟨p,A.2⟩))}};rw[<- H] at e;obtain⟨i,r,k⟩:=_mg.mp e;have q:=(_mf.mp r).2
 have K:i=z:=f i q (fun t ht' M=>by
  have X:=(c.1 i (d i q)).2.2.1 t M;rw[k] at X
  exact _dl.mp I X (mem_insert_of_mem ht'))
 rw[K] at k;rw[k];exact I.mono_right (subset_insert _ _)
lemma qT {D:Dag} (h:ai 10 D) (m:dg 10 bI D) (b:Fin 10->ℕ) (n:aM 10 D b) {pos:Fin 10->ℕ×_d} (d:bA 10 bI D pos) (f:bd 10 D<=(al 10 D).card+2) (e:∀ i:Fin 10,4<=i.val->i∈aa 10 D):False:=by
 have F:=oE h m b n d f e {1,2,3} 1 4 7 9 2 1 3 V V V V V V V;have G:=oE h m b n d f e {1,2,3} 2 5 7 9 2 1 3 V V V V V V V;have H:=oE h m b n d f e {0,2,3} 2 7 5 9 2 0 3 V V V V V V V;have q:∀ i:Fin 10,4<=i.val->∀ a,bI i a->a∈ag 10 D (aw D (pos i)):=fun i g=>(d.1 i (e i g)).2.2.1;have z:(2:Fin 10)∉ag 10 D (aw D (pos 4)):=fun j=>_dl.mp F j V;have I:(1:Fin 10)∉ag 10 D (aw D (pos 5)):=fun j=>_dl.mp G j V;have M:(0:Fin 10)∉ag 10 D (aw D (pos 7)):=fun j=>_dl.mp H j V;have A:=gS eS h m b n ({0,1,2}:Finset (Fin 10));obtain⟨k,J⟩:=e6 d ({0,1,2}:Finset (Fin 10)) (univ.filter (fun i:Fin 10=>4<=i.val)) (fun i g=>⟨e i (_mf.mp g).2,lu i (_mf.mp g).2⟩);have K:=_cl k;have N:=lv;have P:({0,1,2}:Finset (Fin 10)).card=3:=V;have mk:∀(i a c:Fin 10),4<=i.val->bI i a->bI i c->a≠c ->a∈({0,1,2}:Finset (Fin 10))->c∈({0,1,2}:Finset (Fin 10)) ->a∈ag 10 D (aw D (pos i))∩{0,1,2}/\c∈ag 10 D (aw D (pos i))∩{0,1,2} /\2<=(ag 10 D (aw D (pos i))∩({0,1,2}:Finset (Fin 10))).card:=by{intro i a c g L j p r s;have B:=_mn.mpr ⟨q i g a L,r⟩;have C:=_mn.mpr ⟨q i g c j,s⟩;exact⟨B,C,one_lt_card.mpr ⟨a,B,c,C,p⟩⟩};obtain⟨a40,a41,c4⟩:=mk 4 0 1 V V V V V V;obtain⟨a50,a52,c5⟩:=mk 5 0 2 V V V V V V;obtain⟨a71,a72,c7⟩:=mk 7 1 2 V V V V V V;obtain⟨g4,t,e4⟩:=eH h.1 _ _ c4;obtain⟨g5,u,e5⟩:=eH h.1 _ _ c5;obtain⟨g7,v,e7⟩:=eH h.1 _ _ c7;have w:g4≠g5:=by{intro l;rw[l,e5] at e4;rw[e4] at a52;exact z (_mn.mp a52).1};have x:g4≠g7:=by{intro l;rw[l,e7] at e4;rw[e4] at a72;exact z (_mn.mp a72).1};have y:g5≠g7:=by{intro l;rw[l,e7] at e5;rw[e5] at a71;exact I (_mn.mp a71).1};have E:3<=(aW 10 D (ao 10 D ({0,1,2}:Finset (Fin 10)))).card:=two_lt_card.mpr ⟨g4,t,g5,u,g7,v,w,x,y⟩;omega
lemma iN {D:Dag} (h:ai 10 D) (f:dg 10 bI D) (N:(4:Fin 10)∈aa 10 D) (S:(9:Fin 10)∈aa 10 D):7<=ap 10 D:=by
 by_contra T;have P:=jO h f;have U:=dC 10 D;obtain⟨b,z⟩:=dK eS h.1 f;have Z:=dX h.1 b z;have C:=aV 10 D;obtain⟨pos,c⟩:=bQ eS h f;have g:=jl h f;have Q:∀ q∈aa 10 D,4<=q.val:=by{intro q A;by_contra l;rcases oD q (by omega) with n|n;{rw[g q A 4 N] at n;exact _fnt n};{rw[g q A 9 S] at n;exact _fnt n}};have a:aa 10 D⊆univ.filter (fun i:Fin 10=>4<=i.val):=fun q A=>_mf.mpr ⟨_mv q,Q q A⟩;have E:=_cl a;rw[lv] at E;have W:(al 10 D).card<=5:=by
  by_cases p:∃ i∈aa 10 D,i≠4/\i≠9
  · obtain⟨i,d,r,F⟩:=p
    obtain⟨u,i3,a1,a2,a3,d1,d2⟩:=qR i (Q i d) r F;have h3:=m_ eS h f c N d (Ne.symm r) d1 d2 a1 a2 a3;have s:=gS eS h f b z ({u}:Finset (Fin 10));rw[_cs] at s;omega
  · have j:aa 10 D⊆({4,9}:Finset (Fin 10)):=by
     intro i d;by_contra l;simp only[_mi,_ms,not_or] at l;exact p ⟨i,d,l.1,l.2⟩
    have:=_cl j;have h2:({4,9}:Finset (Fin 10)).card=2:=V;omega
 have G:=card_sdiff_add_card_eq_card a;rw[lv] at G;have H:(univ.filter (fun i:Fin 10=>4<=i.val)\aa 10 D).card<=1:=by{omega};have w:∀ v v':Fin 10,4<=v.val->4<=v'.val->v∉aa 10 D ->v'∉aa 10 D->v=v':=fun v v' B B' X X'=>
  card_le_one.mp H v (_md.mpr ⟨_mf.mpr ⟨_mv v,B⟩,X⟩) v' (_md.mpr ⟨_mf.mpr ⟨_mv v',B'⟩,X'⟩)
 by_cases e:∀ i:Fin 10,4<=i.val->i∈aa 10 D;{exact qT h f b z c (by omega) e}
 · rw[not_forall] at e
   obtain⟨v,B⟩:=e;rw[Classical.not_imp] at B;obtain⟨k,x⟩:=B;have R:(aa 10 D).card<6:=by
    have:=card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨a,fun Y=>
     x (Y▸_mf.mpr ⟨_mv v,k⟩)⟩)
    rw[lv] at this;exact this
   have y:∀ i:Fin 10,4<=i.val/\i≠v->i∈aa 10 D:=by{intro i d;by_contra l;exact d.2 (w i v d.1 k l x)};obtain⟨u,t,K,L,M,nu,nt⟩:=si v k;exact qS h f b z c (by omega) K L M (fun i d=>y i (nu i d)) (fun i d=>y i (nt i d))
def jA (l:_F ℕ) (v:Fin 10):Fin 10:=Fin.ofNat 10 (l.getD v.val 0)
def lc:_ep (Fin 10):=⟨jA [0,2,1,3,5,4,6,7,9,8],jA [0,2,1,3,5,4,6,7,9,8],by intro x;revert x;decide +kernel,by intro x;revert x;decide +kernel⟩
def ld:_ep (Fin 10):=⟨jA [0,3,2,1,6,5,4,9,8,7],jA [0,3,2,1,6,5,4,9,8,7],by intro x;revert x;decide +kernel,by intro x;revert x;decide +kernel⟩
lemma nf:∀ u v:Fin 10,bI u v↔bI (lc u) (lc v):=by
 decide +kernel
lemma ng:∀ u v:Fin 10,bI u v↔bI (ld u) (ld v):=by
 decide +kernel
lemma gW {D:Dag} (h:ai 10 D) (b:dg 10 bI D) {i1 i2:Fin 10} (c:i1∈aa 10 D) (d:i2∈aa 10 D) (e:(i1=4/\i2=9)\/(i1=5/\i2=8)\/(i1=6/\i2=7)):7<=ap 10 D:=by
 have a:∀ σ:_ep (Fin 10),(∀ u v:Fin 10,bI u v↔bI (σ u) (σ v)) ->σ i1=4->σ i2=9->7<=ap 10 D:=by{intro σ hσ e1 e2;rw[<- eJ σ D];refine iN (fd σ h) (l_ σ hσ h b) ?_ ?_;{rw[ep σ h.1,<-e1];exact mem_image_of_mem σ c};{rw[ep σ h.1,<-e2];exact mem_image_of_mem σ d}};rcases e with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩;{exact iN h b c d};{exact a lc nf V V};{exact a ld ng V V}
def cf {n m:ℕ} (ρ:Fin n->Option _d) (ι:Fin m->Fin n) (y:Fin m->_d):Fin n->_d:=fun v=>(ρ v).getD (decide (∃ i:Fin m,ι i=v/\y i=true))
def fv {n m:ℕ} (ρ:Fin n->Option _d) (ι:Fin m->Fin n):Prop:=Function.Injective ι/\∀ v,ρ v=none↔∃ i,ι i=v
lemma dN {n m:ℕ} {ρ:Fin n->Option _d} {ι:Fin m->Fin n} (a:fv ρ ι) (y:Fin m->_d) (i:Fin m):cf ρ ι y (ι i)=y i:=by
 have h:ρ (ι i)=none:=(a.2 _).mpr ⟨i,rfl⟩;unfold cf;rw[h,Option.getD_none];by_cases b:y i=true;{rw[b,decide_eq_true_eq];exact⟨i,rfl,b⟩}
 · rw[Bool.not_eq_true] at b
   rw[b,decide_eq_false_iff_not];rintro⟨i',d,c⟩;rw[a.1 d,b] at c;exact _fnt c
lemma dw {n m:ℕ} {ρ:Fin n->Option _d} (ι:Fin m->Fin n) (y:Fin m->_d) {v:Fin n} {b:_d} (h:ρ v=some b):cf ρ ι y v=b:=by
 unfold cf;rw[h,Option.getD_some]
lemma kk {n m:ℕ} {ρ:Fin n->Option _d} {ι:Fin m->Fin n} (a:fv ρ ι) {y y':Fin m->_d} {i:Fin m} (h:∀ k,k≠i->y k=y' k):∀ v,v≠ι i->cf ρ ι y v=cf ρ ι y' v:=by
 intro v d;cases c:ρ v with
 | some b=>rw[dw ι y c,dw ι y' c]
 | none=>
  obtain⟨k,rfl⟩:=(a.2 v).mp c;rw[dN a,dN a];exact h k (fun e=>d (by rw[e]))
lemma kT {n:ℕ} {D:Dag} (a:au n D) {j:ℕ} (b:j<D.length) (s:_d) (x:Fin n->_d):val D x (n+j)=kF (cR D j) (val D x (aw D (j,s))) (val D x (aw D (j,!s))):=by
 rw[cS a x j b];cases s;{simp[aw]};{cases cR D j <;> simp[aw,Bool.and_comm,Bool.or_comm]}
lemma ma (f:ℕ->ℕ) (K:Finset ℕ) (h:∀ w∈K,1<=f w):∑ w∈K,(f w - 1)+K.card=∑ w∈K,f w:=by
 rw[card_eq_sum_ones,<-sum_add_distrib];exact sum_congr rfl (fun w a=>Nat.sub_add_cancel (h w a))
lemma oi (E:Dag) (g:_d×ℕ×ℕ):cj (E ++ [g]) E.length=g.2.1/\ck (E ++ [g]) E.length=g.2.2 /\cR (E ++ [g]) E.length=g.1 /\∀ i,i<E.length->cj (E ++ [g]) i=cj E i/\ck (E ++ [g]) i=ck E i:=by
 refine⟨?_,?_,?_,fun i a=>?_⟩;{unfold cj;rw[f9]};{unfold ck;rw[f9]};{unfold cR;rw[f9]};{unfold cj ck;rw[gM E [g] i a];exact⟨rfl,rfl⟩}
lemma kU {m:ℕ} {E:Dag} {g:_d×ℕ×ℕ} (c:au m (E ++ [g])) (y:Fin m->_d):(∀ w,w<m+E.length->val (E ++ [g]) y w=val E y w) /\val (E ++ [g]) y (m+E.length)=kF g.1 (val E y g.2.1) (val E y g.2.2):=by
 have a:∀ w,w<m+E.length->val (E ++ [g]) y w=val E y w:=by{intro w f;have h:=oe (E ++ [g]) y E.length w f (by simp);rw[<- h];simp};refine⟨a,?_⟩;have b:E.length<(E ++ [g]).length:=by simp
 obtain⟨d,e,-⟩:=c E.length b;obtain⟨e1,e2,e3,-⟩:=oi E g;rw[cS c y E.length b,e3];rw[e1] at d;rw[e2] at e;rw[e1,e2,a _ d,a _ e]
noncomputable section CofRestrict
open Classical
variable {n m : ℕ} (D : Dag) (ρ : Fin n → Option Bool) (ι : Fin m → Fin n)
def dD (w:ℕ):Prop:=∀ y y':Fin m->_d,val D (cf ρ ι y) w=val D (cf ρ ι y') w
def aL (w:ℕ):Prop:=¬ dD D ρ ι w /\Relation.ReflTransGen (fun a b=>bk n D a b/\¬ dD D ρ ι b) w (bH n D)
def cF (w:ℕ):ℕ:=((bV D w).filter (fun j=>aL D ρ ι (n+j))).card
def f4 (w:ℕ):Finset (Fin m):=univ.filter (fun i=>val D (cf ρ ι (cl i)) w=true)
def kl:ℕ:=∑ w∈(cD n D).filter (fun w=>aL D ρ ι w),(cF D ρ ι w - 1)
def jm:ℕ:=∑ w∈(cD n D).filter (fun w=>aL D ρ ι w/\(f4 D ρ ι w).Nonempty),(cF D ρ ι w - 1)
def eT (t:ℕ->ℕ) (e:ℕ):Finset ℕ:=(range (n+D.length)).filter (fun w=>aL D ρ ι w/\t w=e)
variable {D ρ ι}
lemma nX {w:ℕ} {i:Fin m}:i∈f4 D ρ ι w↔val D (cf ρ ι (cl i)) w=true:=by
 simp[f4]
lemma e9 {w:ℕ} (h:aL D ρ ι w):w<n+D.length:=by
 by_contra a;exact h.1 (fun y y'=>by rw[fs D _ w (by omega),fs D _ w (by omega)])
lemma fO {a c:ℕ} (d:bk n D a c) (e:¬ dD D ρ ι a) (b:aL D ρ ι c):aL D ρ ι a:=⟨e,Relation.ReflTransGen.head ⟨d,b.1⟩ b.2⟩
lemma jn {w:ℕ} (h:aL D ρ ι w) (b:w≠bH n D):∃ c,bk n D w c/\aL D ρ ι c:=by
 rcases Relation.ReflTransGen.cases_head h.2 with d|⟨c,e,a⟩;{exact absurd d b};{exact⟨c,e.1,e.2,a⟩}
lemma mz (w:ℕ):cF D ρ ι w<=aF D w:=_cfl _ _
lemma oF {w:ℕ} (h:aL D ρ ι w) (a:w≠bH n D):1<=cF D ρ ι w:=by
 obtain⟨c,b,d⟩:=jn h a;refine _cp.mpr ⟨c - n,_mf.mpr ⟨dR b,?_⟩⟩;rw[Nat.add_sub_cancel' b.2.1];exact d
lemma lf (a:au n D) {c:Fin n} (b:ρ c=some true) {w:ℕ} (d:c∈ag n D w):dD D ρ ι w:=by
 intro y y';rw[cO a d (dw ι y b),cO a d (dw ι y' b)]
lemma fX (a:au n D) {c:Fin n} (b:ρ c=some true) {w:ℕ} (d:c∈ag n D w):¬ aL D ρ ι w:=fun h=>h.1 (lf a b d)
lemma eC (a:fv ρ ι) {w:ℕ} (c:w<n) (e:aL D ρ ι w):∃ i:Fin m,(ι i).val=w:=by
 cases d:ρ ⟨w,c⟩ with
 | some b=>
  exact absurd (fun y y'=>by
   rw[bY D _ w c,bY D _ w c,dw ι y d,dw ι y' d]) e.1
 | none=>
  obtain⟨i,g⟩:=(a.2 _).mp d;exact⟨i,by rw[g]⟩
lemma nh (r:au n D) (c:fv ρ ι) (i:Fin m) (e:∃ y y':Fin m->_d,(∀ k,k≠i->y k=y' k) /\val D (cf ρ ι y) (bH n D)≠val D (cf ρ ι y') (bH n D)):aL D ρ ι (ι i).val:=by
 obtain⟨y,y',f,g⟩:=e;have s:=d_ r _ _ (ι i) (kk c f) _ g;refine⟨fun l=>g ?_,eG (fun a b h=>⟨h.1,fun l=>h.2 (l y y')⟩) s⟩;have p:=l y y';rw[bY D _ _ (ι i).isLt,bY D _ _ (ι i).isLt,Fin.eta,dN c,dN c] at p;have j:y=y':=by{funext k;by_cases q:k=i;{rw[q];exact p};{exact f k q}};rw[j]
lemma mP (a:au n D) {j:ℕ} (b:j<D.length) (d:dD D ρ ι (cj D j)) (e:dD D ρ ι (ck D j)):dD D ρ ι (n+j):=by
 intro y y';rw[cS a _ j b,cS a _ j b,d y y',e y y']
lemma lx (e:au n D) {j:ℕ} (a:j<D.length) (b:aL D ρ ι (n+j)):∃ s,aL D ρ ι (aw D (j,s)):=by
 by_cases c:dD D ρ ι (cj D j)
 · by_cases d:dD D ρ ι (ck D j)
   · exact absurd (mP e a c d) b.1
   · exact⟨true,fO (cM a true) (by rw[bh];exact d) b⟩
 · exact⟨false,fO (cM a false) (by rw[aX];exact c) b⟩
lemma qe (h:au n D) {j:ℕ} (i:j<D.length) (s:_d) (k:dD D ρ ι (aw D (j,!s))) (e:¬ dD D ρ ι (n+j)):∀ y,val D (cf ρ ι y) (n+j)=val D (cf ρ ι y) (aw D (j,s)):=by
 intro y;have a:∀ y',val D (cf ρ ι y') (n+j)=kF (cR D j) (val D (cf ρ ι y') (aw D (j,s))) (val D (cf ρ ι y) (aw D (j,!s))):=fun y'=>by rw[kT h i s,k y' y]
 rw[a y];cases f:cR D j <;> cases g:val D (cf ρ ι y) (aw D (j,!s));{simp};{exfalso;apply e;intro c d;rw[a c,a d,f,g];simp};{exfalso;apply e;intro c d;rw[a c,a d,f,g];simp};{simp}
def eg (D:Dag) (ρ:Fin n->Option _d) (ι:Fin m->Fin n) (k:ℕ) (E:Dag) (t q:ℕ->ℕ):Prop:=au m E /\(∀ w,w<n+k->aL D ρ ι w ->t w<m+E.length/\∀ y,val E y (t w)=val D (cf ρ ι y) w) /\(∀ i,i<E.length->q i<k/\aL D ρ ι (n+q i)/\t (n+q i)=m+i /\cj E i=t (cj D (q i))/\ck E i=t (ck D (q i)) /\aL D ρ ι (cj D (q i))/\aL D ρ ι (ck D (q i))) /\(∀ j,j<k->aL D ρ ι (n+j)->(∃ i,i<E.length/\q i=j) \/∀ s,aL D ρ ι (aw D (j,s))->t (aw D (j,s))=t (n+j)) /\(∀ i:Fin m,t (ι i).val=i.val)
lemma nY (b:fv ρ ι):∃ E t q,eg D ρ ι 0 E t q:=by
 have d:∀ w:ℕ,∃ r:ℕ,∀ i:Fin m,(ι i).val=w->r=i.val:=by
  intro w;by_cases h:∃ i:Fin m,(ι i).val=w
  · obtain⟨i,a⟩:=h
    exact⟨i.val,fun i' a'=>by rw[b.1 (_fe (a.trans a'.symm))]⟩
  · exact⟨0,fun i a=>absurd ⟨i,a⟩ h⟩
 choose t l using d;refine⟨[],t,fun _=>0,fun j g=>absurd g (by simp),?_,fun i a=>absurd a (by simp),fun j g=>absurd g (by simp),fun i=>l _ i rfl⟩;intro w c p;rw[Nat.add_zero] at c;obtain⟨i,a⟩:=eC b c p;have e:=l w i a;have k:(⟨w,c⟩:Fin n)=ι i:=_fe a.symm;refine⟨by rw[e];simp,fun y=>?_⟩;rw[e,bY [] y i.val i.isLt,bY D _ w c,k,dN b]
lemma nZ (l:au n D) {k:ℕ} (r:k<D.length) {E:Dag} {t q:ℕ->ℕ} (h:eg D ρ ι k E t q):∃ E' t' q',eg D ρ ι (k+1) E' t' q':=by
 obtain⟨N,z,P,Q,R⟩:=h;obtain⟨Z,hB,-⟩:=l k r;by_cases G:aL D ρ ι (n+k);swap
 · refine⟨E,t,q,N,fun w S f=>?_,fun i H=>?_,fun j hj g=>?_,R⟩
   · have p:w≠n+k:=fun I=>G (I▸f)
     exact z w (by omega) f
   · obtain⟨a,b⟩:=P i H
     exact⟨by omega,b⟩
   · have p:j≠k:=fun I=>G (I▸g)
     exact Q j (by omega) g
 have c:∀(v:ℕ) (w:ℕ),w<n+k->Function.update t (n+k) v w=t w:=fun v w S=>Function.update_of_ne (by omega) _ _;by_cases I:aL D ρ ι (cj D k)/\aL D ρ ι (ck D k) /\t (cj D k)≠t (ck D k)
 · obtain⟨L,M,p⟩:=I
   obtain⟨ta,va⟩:=z _ Z L;obtain⟨tb,vb⟩:=z _ hB M;have A:au m (E ++ [(cR D k,t (cj D k),t (ck D k))]):=jG N _ _ _ ta tb p;obtain⟨e1,e2,-,e4⟩:=oi E (cR D k,t (cj D k),t (ck D k));have u:(E ++ [(cR D k,t (cj D k),t (ck D k))]).length=E.length+1:=by simp
   refine⟨_,Function.update t (n+k) (m+E.length),Function.update q E.length k,A,fun w S f=>?_,fun i H=>?_,fun j hj g=>?_,fun i=>?_⟩
   · rw[u]
     by_cases B:w=n+k
     · rw[B,Function.update_self]
       refine⟨by omega,fun y=>?_⟩;rw[(kU A y).2,va y,vb y,cS l _ k r]
     · obtain⟨tw,vw⟩:=z w (by omega) f
       rw[c _ w (by omega)];exact⟨by omega,fun y=>by rw[(kU A y).1 _ tw,vw y]⟩
   · rw[u] at H
     by_cases H':i<E.length
     · obtain⟨a1,a2,a3,a4,a5,a6,a7⟩:=P i H'
       obtain⟨sa,sb,-⟩:=l (q i) (by omega);rw[Function.update_of_ne (by omega:i≠E.length),c _ _ (by omega:n+q i<n+k),c _ _ (by omega:cj D (q i)<n+k),c _ _ (by omega:ck D (q i)<n+k),(e4 i H').1,(e4 i H').2];exact⟨by omega,a2,a3,a4,a5,a6,a7⟩
     · have T:i=E.length:=by omega
       rw[T,Function.update_self,Function.update_self,c _ _ Z,c _ _ hB,e1,e2];exact⟨by omega,G,rfl,rfl,rfl,L,M⟩
   · by_cases F:j=k
     · exact Or.inl ⟨E.length,by omega,by rw[F,Function.update_self]⟩
     · rcases Q j (by omega) g with ⟨i,H,U⟩|W
       · exact Or.inl ⟨i,by omega,by rw[Function.update_of_ne (by omega:i≠E.length)];exact U⟩
       · refine Or.inr (fun s d=>?_)
         have X:=dh l (by omega:j<D.length) s;rw[c _ _ (by omega),c _ _ (by omega)];exact W s d
   · rw[c _ _ (by have:=(ι i).isLt;omega)]
     exact R i
 · have J:aL D ρ ι (cj D k)->aL D ρ ι (ck D k) ->t (cj D k)=t (ck D k):=fun L M=>by
    by_contra p;exact I ⟨L,M,p⟩
   obtain⟨s0,ls0⟩:=lx l r G;have x:∀ s,aL D ρ ι (aw D (k,s))->t (aw D (k,s))=t (aw D (k,s0)):=by{intro s d;cases s <;> cases s0 <;> simp only[aX,bh] at d ls0⊢;{exact J d ls0};{exact(J ls0 d).symm}}
   obtain⟨t0,v0⟩:=z _ (dh l r s0) ls0;have K:∀ y,val D (cf ρ ι y) (n+k)=val D (cf ρ ι y) (aw D (k,s0)):=by
    by_cases e:dD D ρ ι (aw D (k,!s0));{exact qe l r s0 e G.1}
    · have lo:=fO (cM r (!s0)) e G
      obtain⟨-,v1⟩:=z _ (dh l r (!s0)) lo;intro y;rw[kT l r s0,<-v1 y,x _ lo,v0 y];cases cR D k <;> simp
   refine⟨E,Function.update t (n+k) (t (aw D (k,s0))),q,N,fun w S f=>?_,fun i H=>?_,fun j hj g=>?_,fun i=>?_⟩
   · by_cases B:w=n+k
     · rw[B,Function.update_self]
       exact⟨t0,fun y=>by rw[v0 y,K y]⟩
     · rw[c _ w (by omega)]
       exact z w (by omega) f
   · obtain⟨a1,a2,a3,a4,a5,a6,a7⟩:=P i H
     obtain⟨sa,sb,-⟩:=l (q i) (by omega);rw[c _ _ (by omega:n+q i<n+k),c _ _ (by omega:cj D (q i)<n+k),c _ _ (by omega:ck D (q i)<n+k)];exact⟨by omega,a2,a3,a4,a5,a6,a7⟩
   · by_cases F:j=k
     · refine Or.inr (fun s d=>?_)
       rw[F] at d⊢;rw[c _ _ (dh l r s),Function.update_self];exact x s d
     · rcases Q j (by omega) g with Y|W
       · exact Or.inl Y
       · refine Or.inr (fun s d=>?_)
         have X:=dh l (by omega:j<D.length) s;rw[c _ _ (by omega),c _ _ (by omega)];exact W s d
   · rw[c _ _ (by have:=(ι i).isLt;omega)]
     exact R i
lemma oG (b:au n D) (a:fv ρ ι):∃ E t q,eg D ρ ι D.length E t q:=by
 have h:∀ k,k<=D.length->∃ E t q,eg D ρ ι k E t q:=by
  intro k;induction k with
  | zero=>exact fun _=>nY a
  | succ k ih=>
   intro d;obtain⟨E,t,q,c⟩:=ih (by omega);exact nZ b (by omega) c
 exact h _ le_rfl
lemma i8 {a:ℕ×_d}:a∈eK D↔a.1<D.length:=by simp[eK]
lemma oH {E:Dag} {t q:ℕ->ℕ} (c:eg D ρ ι D.length E t q) {j:ℕ} (d:j<D.length) (s:_d) (e:aL D ρ ι (aw D (j,s))) (f:aL D ρ ι (n+j)):t (aw D (j,s))<=t (n+j):=by
 obtain⟨g,-,h,k,-⟩:=c;rcases k j d f with ⟨i,b,a⟩|l
 · obtain⟨-,-,e1,e2,e3,-,-⟩:=h i b
   obtain⟨sa,sb,-⟩:=g i b;rw[a] at e1 e2 e3;cases s;{rw[aX,<-e2,e1];omega};{rw[bh,<-e3,e1];omega}
 · exact(l s e).le
lemma ni {E:Dag} {t q:ℕ->ℕ} (g:eg D ρ ι D.length E t q) {w:ℕ} (h:aL D ρ ι w):t w<=t (bH n D):=by
 obtain⟨e,i⟩:=h;revert e;induction i using Relation.ReflTransGen.head_induction_on with
 | refl=>exact fun _=>le_rfl
 | @head a c b d ih=>
  intro e;have f:aL D ρ ι a:=⟨e,Relation.ReflTransGen.head b d⟩;obtain⟨j,s,k,rfl,rfl⟩:=fj.mp b.1;exact(oH g k s f ⟨b.2,d⟩).trans (ih b.2)
lemma nj {E:Dag} {t q:ℕ->ℕ} (l:eg D ρ ι D.length E t q) {w:ℕ} (p:aL D ρ ι w) (d:t w≠t (bH n D)):∃ i,i<E.length/\(cj E i=t w\/ck E i=t w):=by
 obtain⟨g,r⟩:=p;revert g d;induction r using Relation.ReflTransGen.head_induction_on with
 | refl=>exact fun d _=>absurd rfl d
 | @head a c b f ih=>
  intro d g;have h:aL D ρ ι a:=⟨g,Relation.ReflTransGen.head b f⟩;obtain⟨j,s,u,rfl,rfl⟩:=fj.mp b.1;rcases l.2.2.2.1 j u ⟨b.2,f⟩ with ⟨i,m,k⟩|v
  · obtain⟨-,-,-,e2,e3,-,-⟩:=l.2.2.1 i m
    rw[k] at e2 e3;refine⟨i,m,?_⟩;cases s;{left;rw[aX];exact e2};{right;rw[bh];exact e3}
  · have e:=v s h
    rw[e] at d⊢;exact ih d b.2
lemma ly {E:Dag} {t q:ℕ->ℕ} (c:eg D ρ ι D.length E t q) (a:∀ i:Fin m,aL D ρ ι (ι i).val) {e:ℕ} (d:e<m+E.length):∃ w,aL D ρ ι w/\t w=e:=by
 by_cases b:e<m;{exact⟨_,a ⟨e,b⟩,c.2.2.2.2 ⟨e,b⟩⟩}
 · obtain⟨-,h,e1,-⟩:=c.2.2.1 (e - m) (by omega)
   exact⟨_,h,by rw[e1];omega⟩
lemma mA {E:Dag} {t q:ℕ->ℕ} (c:eg D ρ ι D.length E t q) (a:∀ i:Fin m,aL D ρ ι (ι i).val) (g:0<m) (b:aL D ρ ι (bH n D)):t (bH n D)=bH m E:=by
 obtain⟨w,d,f⟩:=ly c a (e:=m+E.length - 1) (by omega);have h:=ni c d;have j:=(c.2.1 _ (e9 b) b).1;show t (bH n D)=m+E.length - 1;omega
lemma oI {E:Dag} {t q:ℕ->ℕ} (c:eg D ρ ι D.length E t q) (a:∀ i:Fin m,aL D ρ ι (ι i).val) (h:0<m) (d:aL D ρ ι (bH n D)):o7 m E:=by
 intro e l;obtain⟨w,j,f⟩:=ly c a (e:=e) (by omega);have g:t (bH n D)=m+E.length - 1:=mA c a h d;obtain⟨i,k,b⟩:=nj c j (by omega);rw[f] at b;exact _cp.mpr ⟨i,_mf.mpr ⟨mem_range.mpr k,b⟩⟩
lemma n0 (e:au n D) (w:ℕ):cF D ρ ι w =((eK D).filter (fun a=>aw D a=w/\aL D ρ ι (n+a.1))).card:=by
 rw[d8,cF,bV,filter_filter,card_filter];refine sum_congr rfl (fun j f=>?_);have b:=(e j (mem_range.mp f)).2.2;rw[aX,bh];by_cases c:cj D j=w <;> by_cases d:ck D j=w <;>
  by_cases g:aL D ρ ι (n+j)<;> simp[c,d,g]
 exact b (c.trans d.symm)
lemma km {E:Dag} {t q:ℕ->ℕ} (Y:au n D) (m:fv ρ ι) (hI:eg D ρ ι D.length E t q) (e:ℕ):aF E e+(eT D ρ ι t e).card<=∑ w∈eT D ρ ι t e,cF D ρ ι w+1:=by
 obtain⟨-,-,y,h4,M⟩:=hI;obtain⟨F,Z⟩:∃ F,F=eT D ρ ι t e:=⟨_,rfl⟩;obtain⟨A,hA⟩:∃ A,A=(eK D).filter (fun a=>aL D ρ ι (n+a.1) /\aL D ρ ι (aw D a)/\t (aw D a)=e):=⟨_,rfl⟩;rw[<- Z];have d:∀ w,w∈F↔aL D ρ ι w/\t w=e:=by{intro w;rw[Z,eT,_mf,mem_range];exact⟨fun h=>h.2,fun h=>⟨e9 h.1,h⟩⟩};have c:∀ a,a∈A↔a.1<D.length/\aL D ρ ι (n+a.1) /\aL D ρ ι (aw D a)/\t (aw D a)=e:=by{intro a;rw[hA,_mf,i8]};have Q:A.card=∑ w∈F,cF D ρ ι w:=by{rw[card_eq_sum_card_fiberwise (f:=aw D) (s:=A) (t:=F) (fun a u=>mem_coe.mpr ((d _).mpr ((c a).mp (mem_coe.mp u)).2.2))];refine sum_congr rfl (fun w v=>?_);rw[n0 Y w];congr 1;ext a;rw[_mf,_mf,c,i8];constructor;{rintro⟨⟨u,R,-,-⟩,rfl⟩;exact⟨u,rfl,R⟩};{rintro⟨u,rfl,R⟩;exact⟨⟨u,R,(d _).mp v⟩,rfl⟩}};have N:=card_filter_add_card_filter_not (s:=A) (fun a:ℕ×_d=>∃ i,i<E.length/\q i=a.1);have hem:aF E e<=(A.filter (fun a:ℕ×_d=>∃ i,i<E.length/\q i=a.1)).card:=by
  have z:∀ i,∃ a:ℕ×_d,a.1=q i/\(i∈bV E e ->a∈A.filter (fun a:ℕ×_d=>∃ i,i<E.length/\q i=a.1)):=by
   intro i;by_cases k:i∈bV E e
   · rw[bV,_mf,mem_range] at k
     obtain⟨j,G⟩:=k;obtain⟨a1,a2,-,a4,a5,a6,a7⟩:=y i j;rw[a4,a5] at G;rcases G with h|h;{exact⟨(q i,false),rfl,fun _=>_mf.mpr ⟨(c _).mpr ⟨a1,a2,by rw[aX];exact a6,by rw[aX];exact h⟩,i,j,rfl⟩⟩};{exact⟨(q i,true),rfl,fun _=>_mf.mpr ⟨(c _).mpr ⟨a1,a2,by rw[bh];exact a7,by rw[bh];exact h⟩,i,j,rfl⟩⟩}
   · exact⟨(q i,false),rfl,fun h=>absurd h k⟩
  choose φ hφ1 hφ2 using z;refine card_le_card_of_injOn φ (fun i k=>hφ2 i k) (fun i k i' k' B=>?_);have S:q i=q i':=by rw[<- hφ1 i,<-hφ1 i',B]
  have j:i∈bV E e:=k;have j':i'∈bV E e:=k';rw[bV,_mf,mem_range] at j j';have H:=(y i j.1).2.2.1;have P:=(y i' j'.1).2.2.1;rw[S] at H;omega
 have hsp:=card_filter_add_card_filter_not (s:=F) (fun w=>w<n\/∃ i,i<E.length/\n+q i=w);have T:(F.filter (fun w=>w<n\/∃ i,i<E.length/\n+q i=w)).card<=1:=by
  rw[card_le_one];intro a u b hb;rw[_mf,d] at u hb;obtain⟨⟨la,ta⟩,ca⟩:=u;obtain⟨⟨lb,tb⟩,cb⟩:=hb;rcases ca with I|⟨i,k,rfl⟩<;> rcases cb with J|⟨i',k',rfl⟩
  · obtain⟨i,rfl⟩:=eC m I la
    obtain⟨i',rfl⟩:=eC m J lb;have H:=M i;have P:=M i';have C:i=i':=_fe (by omega);rw[C]
  · obtain⟨i,rfl⟩:=eC m I la
    have H:=M i;have P:=(y i' k').2.2.1;have:=i.isLt;omega
  · obtain⟨i',rfl⟩:=eC m J lb
    have H:=M i';have P:=(y i k).2.2.1;have:=i'.isLt;omega
  · have H:=(y i k).2.2.1
    have P:=(y i' k').2.2.1;have C:i=i':=by omega
    rw[C]
 have himp:(F.filter (fun w=>¬ (w<n\/∃ i,i<E.length/\n+q i=w))).card <=(A.filter (fun a:ℕ×_d=>¬ ∃ i,i<E.length/\q i=a.1)).card:=by
  have z:∀ w,∃ a:ℕ×_d,a.1=w - n /\(w∈F.filter (fun w=>¬ (w<n\/∃ i,i<E.length/\n+q i=w)) ->a∈A.filter (fun a:ℕ×_d=>¬ ∃ i,i<E.length/\q i=a.1)):=by
   intro w;by_cases v:w∈F.filter (fun w=>¬ (w<n\/∃ i,i<E.length/\n+q i=w))
   · have v':=v
     rw[_mf,d,not_or] at v';obtain⟨⟨lw,tw⟩,hwn,K⟩:=v';have hwlt:=e9 lw;have U:w - n<D.length:=by omega
     have L:n+(w - n)=w:=by omega
     have K':¬ ∃ i,i<E.length/\q i=w - n:=fun ⟨i,k,S⟩=>K ⟨i,k,by omega⟩;have lw':aL D ρ ι (n+(w - n)):=by rw[L];exact lw
     have hr:=(h4 (w - n) U lw').resolve_left K';obtain⟨s,ls⟩:=lx Y U lw';exact⟨(w - n,s),rfl,fun _=>_mf.mpr ⟨(c _).mpr ⟨U,lw',ls,by rw[hr s ls,L];exact tw⟩,K'⟩⟩
   · exact⟨(w - n,false),rfl,fun h=>absurd h v⟩
  choose ψ hψ1 hψ2 using z;refine card_le_card_of_injOn ψ (fun w v=>hψ2 w v) (fun w v w' v' B=>?_);have S:w - n=w' - n:=by rw[<- hψ1 w,<-hψ1 w',B]
  have h1:w∈F.filter (fun w=>¬ (w<n\/∃ i,i<E.length/\n+q i=w)):=v;have h1':w'∈F.filter (fun w=>¬ (w<n\/∃ i,i<E.length/\n+q i=w)):=v';rw[_mf,not_or] at h1 h1';omega
 omega
lemma oj {E:Dag} {t q:ℕ->ℕ} (u:au n D) (i:fv ρ ι) (v:eg D ρ ι D.length E t q) (b:t (bH n D)=bH m E) (T:Finset ℕ) (l:T⊆cD m E):bn E T<=∑ w∈(cD n D).filter (fun w=>aL D ρ ι w/\t w∈T),(cF D ρ ι w - 1):=by
 have b':t (bH n D)=m+E.length - 1:=b;have c:∀ e∈T,aF E e - 1<=∑ w∈eT D ρ ι t e,(cF D ρ ι w - 1):=by{intro e h;have y:=km u i v e;have d:∀ w∈eT D ρ ι t e,1<=cF D ρ ι w:=by{intro w a;rw[eT,_mf] at a;refine oF a.2.1 (fun p=>?_);have r:=bP.mp (l h);have x:=a.2.2;rw[p] at x;omega};have:=ma _ _ d;omega};have f:=sum_fiberwise_of_maps_to (s:=(cD n D).filter (fun w=>aL D ρ ι w/\t w∈T)) (t:=T) (g:=t) (fun w a=>(_mf.mp a).2.2) (fun w=>cF D ρ ι w - 1);rw[<- f];unfold bn;refine(sum_le_sum c).trans (le_of_eq ?_);refine sum_congr rfl (fun e h=>sum_congr ?_ (fun _ _=>rfl));ext w;simp only[eT,_mf,mem_range];constructor
 · rintro⟨a,lw,rfl⟩
   refine⟨⟨bP.mpr ?_,lw,h⟩,rfl⟩;have r:=bP.mp (l h);by_contra p;have k:w=bH n D:=by unfold bH;omega
   rw[k] at r;omega
 · rintro⟨⟨a,lw,-⟩,rfl⟩
   exact⟨by have:=bP.mp a;omega,lw,rfl⟩
lemma n6 (x:au n D) (f:fv ρ ι) (N:2<=m) (g:∀ i:Fin m,∃ y y':Fin m->_d,(∀ k,k≠i->y k=y' k) /\val D (cf ρ ι y) (bH n D)≠val D (cf ρ ι y') (bH n D)):∃ E:Dag,ai m E /\(∀ y,val E y (bH m E)=val D (cf ρ ι y) (bH n D)) /\ap m E<=kl D ρ ι/\bd m E<=jm D ρ ι /\∀ i:Fin m,(∀ w,Relation.ReflTransGen (bk n D) (ι i).val w->aF D w<=1) ->i∈aa m E:=by
 obtain⟨E,t,q,p⟩:=oG x f;have j:∀ i:Fin m,aL D ρ ι (ι i).val:=fun i=>nh x f i (g i);have r:aL D ρ ι (bH n D):=by{obtain⟨y,y',-,d⟩:=g ⟨0,by omega⟩;exact⟨fun z=>d (z y y'),Relation.ReflTransGen.refl⟩};have l:=mA p j (by omega) r;obtain⟨-,c⟩:=p.2.1 _ (e9 r) r;rw[l] at c;have d:E≠[]:=by
  rintro rfl;obtain⟨y,y',A,d⟩:=g ⟨0,by omega⟩;apply d;have J:bH m ([]:Dag)=m - 1:=by simp[bH]
  rw[<- c y,<-c y',J,bY [] y (m - 1) (by omega),bY [] y' (m - 1) (by omega)];exact A _ (fun z=>by have:=congrArg Fin.val z;simp at this;omega)
 refine⟨E,⟨p.1,oI p j (by omega) r,d⟩,c,?_,?_,?_⟩
 · unfold ap kl
   refine(oj x f p l (cD m E) (Subset.refl _)).trans (sum_le_sum_of_subset (fun w s=>?_));rw[_mf] at s⊢;exact⟨s.1,s.2.1⟩
 · unfold bd jm
   refine(oj x f p l _ (_fs _ _)).trans (sum_le_sum_of_subset (fun w s=>?_));rw[_mf] at s⊢;obtain⟨B,lw,C⟩:=s;have K:ag m E (t w)=f4 D ρ ι w:=by{ext i;rw[ee,nX,(p.2.1 w (e9 lw) lw).2]};exact⟨B,lw,by rw[<- K];exact(_mf.mp C).2⟩
 · intro G v
   rw[fG];intro e H;have P:=km x f p e;have L:∑ w∈eT D ρ ι t e,cF D ρ ι w<=(eT D ρ ι t e).card:=by{rw[card_eq_sum_ones];refine sum_le_sum (fun w s=>?_);rw[eT,_mf] at s;obtain⟨-,lw,F⟩:=s;refine(mz w).trans (v w ?_);have I:=(p.2.1 w (e9 lw) lw).2;rw[<- F] at H;have d:val D (cf ρ ι (cl G)) w≠val D (cf ρ ι (fun _=>false)) w:=by{rw[<- I,<-I,ee.mp H,qN p.1];simp};exact eG (fun a b h=>h.1) (d_ x _ _ (ι G) (kk f (fun k M=>by simp[cl,M])) w d)};omega
def f5 (D:Dag) (ρ:Fin n->Option _d) (ι:Fin m->Fin n):Finset (Σ _:ℕ,ℕ):=(dq n D).filter (fun u=>aL D ρ ι u.1/\u.2+1<cF D ρ ι u.1)
def jB (D:Dag) (ρ:Fin n->Option _d) (ι:Fin m->Fin n):Finset (Σ _:ℕ,ℕ):=(dq n D).filter (fun u=>(aL D ρ ι u.1/\(f4 D ρ ι u.1).Nonempty) /\u.2+1<cF D ρ ι u.1)
lemma i9 {u:Σ _:ℕ,ℕ}:u∈f5 D ρ ι↔ u∈dq n D/\aL D ρ ι u.1/\u.2+1<cF D ρ ι u.1:=_mf
lemma gX {u:Σ _:ℕ,ℕ}:u∈jB D ρ ι↔ u∈dq n D/\(aL D ρ ι u.1/\(f4 D ρ ι u.1).Nonempty) /\u.2+1<cF D ρ ι u.1:=_mf
lemma jP (P:ℕ->Prop) [DecidablePred P]:((dq n D).filter (fun u=>P u.1/\u.2+1<cF D ρ ι u.1)).card =∑ w∈(cD n D).filter P,(cF D ρ ι w - 1):=by
 have c:(dq n D).filter (fun u=>P u.1/\u.2+1<cF D ρ ι u.1)=((cD n D).filter P).sigma (fun w=>range (cF D ρ ι w - 1)):=by{ext u;have:=mz (D:=D) (ρ:=ρ) (ι:=ι) u.1;simp only[dq,_mf,mem_sigma,mem_range];constructor;{rintro⟨⟨a,-⟩,b,d⟩;exact⟨⟨a,b⟩,by omega⟩};{rintro⟨⟨a,b⟩,d⟩;exact⟨⟨a,by omega⟩,b,by omega⟩}};rw[c,card_sigma];simp
lemma pm:kl D ρ ι=(f5 D ρ ι).card:=(jP (fun w=>aL D ρ ι w)).symm
lemma oJ:jm D ρ ι=(jB D ρ ι).card:=(jP (fun w=>aL D ρ ι w/\(f4 D ρ ι w).Nonempty)).symm
lemma iO (a:au n D) {c:Fin n} (b:ρ c=some true) {u:Σ _:ℕ,ℕ} (d:c∈ag n D u.1):u∉f5 D ρ ι:=fun h=>fX a b d (i9.mp h).2.1
lemma mb {u:Σ _:ℕ,ℕ} (h:cF D ρ ι u.1<=u.2+1):u∉f5 D ρ ι:=fun a=>by
 have:=(i9.mp a).2.2;omega
lemma nk:jB D ρ ι⊆f5 D ρ ι:=fun _ a=>
 i9.mpr ⟨(gX.mp a).1,(gX.mp a).2.1.1,(gX.mp a).2.2⟩
lemma lA (S:Finset (Σ _:ℕ,ℕ)) (a:S⊆dq n D) (b:∀ u∈S,u∉f5 D ρ ι):kl D ρ ι+S.card<=ap n D:=by
 rw[pm,<-mv,<- _cud (_dl.mpr (fun u c d=>b u d c))];exact _cl (union_subset (_fs _ _) a)
lemma lg (S:Finset (Σ _:ℕ,ℕ)) (a:S⊆dq n D) (b:∀ u∈S,u∉jB D ρ ι):jm D ρ ι+S.card<=ap n D:=by
 rw[oJ,<-mv,<- _cud (_dl.mpr (fun u c d=>b u d c))];exact _cl (union_subset (_fs _ _) a)
lemma n9 (R:au n D) (K:Finset ℕ) (x b:ℕ) (g:∀ w∈K,Relation.ReflTransGen (fun a c=>bk n D a c/\a∈K/\c∈K) x w) (S:b∈K) (u:∀ w∈K,w≠b->aF D w<=1) (e:ℕ×_d) (T:e∈aE n D K) (m:¬ aL D ρ ι (n+e.1)):∃ j∈bV D b,¬ aL D ρ ι (n+j):=by
 obtain⟨F,v,G⟩:=_mf.mp T;have H:e.1<D.length:=i8.mp F;have i:bk n D (aw D e) (n+e.1):=cM H e.2;have r:∀ a c,a∈K->a≠b->bk n D a c->¬ aL D ρ ι c ->¬ aL D ρ ι a/\∀ c',bk n D a c'->c'=c:=by{intro a c I p J U;have y:aF D a=1:=by{have:=u a I p;have:=ef J;omega};have q:∀ c',bk n D a c'->c'=c:=fun c' J'=>dS J' J y;refine⟨fun L=>?_,q⟩;have z:a≠bH n D:=by{have:=dc R (ef J);unfold bH;omega};obtain⟨c',J',U'⟩:=jn L z;rw[q c' J'] at U';exact U U'};have B:∀ a,Relation.ReflTransGen (fun a c=>bk n D a c/\a∈K/\c∈K) a (aw D e)->(∃ j∈bV D b,¬ aL D ρ ι (n+j)) \/(¬ aL D ρ ι a /\¬ Relation.ReflTransGen (fun a c=>bk n D a c/\a∈K/\c∈K) a b):=by
  intro a C;induction C using Relation.ReflTransGen.head_induction_on with
  | refl=>
   by_cases s:aw D e=b
   · have Q:=dR i
     rw[Nat.add_sub_cancel_left,s] at Q;exact Or.inl ⟨e.1,Q,m⟩
   · obtain⟨y,M⟩:=r _ _ v s i m
     refine Or.inr ⟨y,fun C=>?_⟩;rcases Relation.ReflTransGen.cases_head C with t|⟨c',J',-⟩;{exact s t}
     · rw[M c' J'.1] at J'
       exact G J'.2.2
  | @head a c f N ih=>
   rcases ih with W|⟨E,P⟩;{exact Or.inl W}
   · by_cases p:a=b
     · refine Or.inl ⟨c - n,?_,?_⟩
       · rw[<- p];exact dR f.1
       · rw[Nat.add_sub_cancel' f.1.2.1];exact E
     · obtain⟨y,M⟩:=r _ _ f.2.1 p f.1 E
       refine Or.inr ⟨y,fun C=>?_⟩;rcases Relation.ReflTransGen.cases_head C with t|⟨c',J',N'⟩;{exact p t}
       · rw[M c' J'.1] at N'
         exact P N'
 rcases B x (g _ v) with h|⟨-,h⟩;{exact h};{exact absurd (g b S) h}
lemma mQ (p:au n D) (x c:Fin n):∀ w,w∈aR n D x c ->Relation.ReflTransGen (fun a d=>bk n D a d/\a∈aR n D x c /\d∈aR n D x c) x.val w:=by
 intro w;induction w using Nat.strong_induction_on with
 | _ w ih=>
  intro r;have e:∀ u,u∈aR n D x c↔ u<n+D.length/\x∈ag n D u/\c∉ag n D u:=by{intro u;simp only[aR,_mf,mem_range]};obtain⟨z,f,g⟩:=(e w).mp r;by_cases t:w<n
  · have A:ag n D w={⟨w,t⟩}:=dr D ⟨w,t⟩
    rw[A,_ms] at f;have q:x.val=w:=by rw[f]
    rw[q]
  · obtain⟨j,rfl⟩:∃ j,w=n+j:=⟨w - n,by omega⟩
    have m:j<D.length:=by omega
    have b:∀ s:_d,x∈ag n D (aw D (j,s))->c∉ag n D (aw D (j,s)) ->Relation.ReflTransGen (fun a d=>bk n D a d/\a∈aR n D x c /\d∈aR n D x c) x.val (n+j):=by{intro s i B;have z':=dh p m s;have v:aw D (j,s)∈aR n D x c:=(e _).mpr ⟨by omega,i,B⟩;exact Relation.ReflTransGen.tail (ih _ z' v) ⟨cM m s,v,r⟩};cases y:cR D j
    · rw[de p m y,_mu] at f g
      rcases f with i|i;{exact b false (by rw[aX];exact i) (by rw[aX];exact fun h=>g (Or.inl h))};{exact b true (by rw[bh];exact i) (by rw[bh];exact fun h=>g (Or.inr h))}
    · rw[cB p m y,_mn] at f g
      by_cases l:c∈ag n D (cj D j);{exact b true (by rw[bh];exact f.2) (by rw[bh];exact fun h=>g ⟨l,h⟩)};{exact b false (by rw[aX];exact f.1) (by rw[aX];exact l)}
lemma lB (g:au n D) {x c:Fin n} (m:ρ c=some true) {b:ℕ} (l:b∈aR n D x c) (p:2<=aF D b) (a:bn D (aR n D x c)=1) {e:ℕ×_d} (q:e∈aE n D (aR n D x c)) (h:c∈ag n D (n+e.1)):cF D ρ ι b<=1:=by
 have y:aF D b - 1+∑ u∈(aR n D x c).erase b,(aF D u - 1)=∑ u∈aR n D x c,(aF D u - 1):=add_sum_erase _ (fun u=>aF D u - 1) l;unfold bn at a;have d:∀ w∈aR n D x c,w≠b->aF D w<=1:=by{intro w r i;have s:aF D w - 1<=∑ u∈(aR n D x c).erase b,(aF D u - 1):=single_le_sum (f:=fun u=>aF D u - 1) (fun _ _=>Nat.zero_le _) (_me.mpr ⟨i,r⟩);omega};obtain⟨j,t,k⟩:=n9 (ρ:=ρ) (ι:=ι) g _ x.val b (mQ g x c) l d e q (fX g m h);have v:((bV D b).filter (fun j=>aL D ρ ι (n+j))).card < (bV D b).card:=card_lt_card (filter_ssubset.mpr ⟨j,t,k⟩);have s:(bV D b).card=aF D b:=rfl;unfold cF;omega
lemma qU {G:Fin n->Fin n->Prop} (f:fv ρ ι) (j:∀ u v,G u v->G v u) (q:∀ c a,ρ c=some true->G c a->ρ a=some false) (y:Fin m->_d):cN G (cf ρ ι y)↔cN (fun u v:Fin m=>G (ι u) (ι v)) y:=by
 have e:∀ u v,G u v->cf ρ ι y u=true->cf ρ ι y v=true ->∃ i,ι i=u/\y i=true:=by
  intro u v d g k;cases l:ρ u with
  | none=>
   obtain⟨i,rfl⟩:=(f.2 u).mp l;rw[dN f] at g;exact⟨i,rfl,g⟩
  | some b=>
   rw[dw ι y l] at g;subst g;rw[dw ι y (q u v l d)] at k;exact absurd k _fnt
 constructor
 · rintro⟨u,v,d,g,k⟩
   obtain⟨i,rfl,p⟩:=e u v d g k;obtain⟨i',rfl,p'⟩:=e v _ (j _ _ d) k g;exact⟨i,i',d,p,p'⟩
 · rintro⟨i,i',d,p,p'⟩
   exact⟨ι i,ι i',d,by rw[dN f];exact p,by rw[dN f];exact p'⟩
lemma kJ {G:Fin n->Fin n->Prop} (t:au n D) (e:fv ρ ι) (x:dg n G D) (f:∀ u v,G u v->G v u) (z:∀ c a,ρ c=some true->G c a->ρ a=some false) (hG':bJ (fun u v:Fin m=>G (ι u) (ι v))) (r:0<m):∃ E:Dag,ai m E/\dg m (fun u v:Fin m=>G (ι u) (ι v)) E /\ap m E<=kl D ρ ι/\bd m E<=jm D ρ ι /\∀ i:Fin m,(∀ w,Relation.ReflTransGen (bk n D) (ι i).val w->aF D w<=1) ->i∈aa m E:=by
 have b:∀ y,val D (cf ρ ι y) (bH n D)=true↔ cN (fun u v:Fin m=>G (ι u) (ι v)) y:=fun y=>(kO x _).trans (qU e f z y);have j:2<=m:=by{obtain⟨a,-,l⟩:=hG'.2.2.2 ⟨0,r⟩ ⟨0,r⟩;by_contra H;exact l (_fe (by have:=a.isLt;show a.val=0;omega))};have g:∀ i:Fin m,∃ y y':Fin m->_d,(∀ k,k≠i->y k=y' k) /\val D (cf ρ ι y) (bH n D)≠val D (cf ρ ι y') (bH n D):=by{intro i;obtain⟨a,A,-⟩:=hG'.2.2.2 i i;refine⟨cl a,bB i (cl a),dd i _,fun p=>?_⟩;have q:cN (fun u v:Fin m=>G (ι u) (ι v)) (bB i (cl a)):=⟨i,a,A,dm i _,by simp[bB,cl]⟩;have h:=(b _).mpr q;rw[<- p] at h;exact dF hG' a ((b _).mp h)};obtain⟨E,q,h,B,C,F⟩:=n6 t e j g;exact⟨E,q,ju hG' (fun y=>by rw[h y];exact b y),B,C,F⟩
end CofRestrict
noncomputable section CofCount
open Classical
variable {n m : ℕ} {D : Dag} {ρ : Fin n → Option Bool} {ι : Fin m → Fin n}
end CofCount
lemma qf {i j:O} (h:aA i=aA j):i=j:=by
 by_contra a;obtain⟨z,b,c⟩:=dT i j a;have:z∈aA j:=h▸(by simp[aA,b]);simp[aA,c] at this
lemma cJ {i a:O}:a∈aA i↔aO i a:=by
 simp[aA]
lemma kn {D:Dag} (h:ai 14 D) (z:aq D) (P:o) (x:∀ a∈P,∀ b∈P,¬ aO a b) (J:o) (g:∀ i∈J,i∈aa 14 D/\aA i⊆P/\¬ aQ 14 D P (aA i)):J.card<=bL 14 D:=by
 classical
 have p:=aK;have r:=aC z;have d:∀ i∈J,∀ q,(∀ a∈P,(a∈ag 14 D q↔aO i a))->False:=by{intro i c q e;refine(g i c).2.2 ⟨q,?_⟩;ext a;rw[_mn,cJ];exact⟨fun f=>(e a f.2).1 f.1,fun f=>⟨(e a ((g i c).2.1 (cJ.2 f))).2 f,(g i c).2.1 (cJ.2 f)⟩⟩};have l:∀ i∈J,∃ b,bz 14 D i.val b/\2<=aF D b/\ag 14 D b=∅:=by
  intro i c;rcases iI p h r (g i c).1 with t|l
  · obtain⟨j,s,-,-,-,e⟩:=jL p h.1 r P x (fun _ _ h=>h) t
    exact(d i c _ e).elim
  · exact l
 choose! β hβ using l;have m:Set.InjOn β J:=by{intro i c j y u;by_contra v;obtain⟨a,n,w⟩:=dT j i (Ne.symm v);obtain⟨k,s,-,-,-,-,e⟩:=iJ p h.1 r P x (fun _ _ h=>h) (hβ i c).1 (ds h.1 (u▸(hβ j y).1)) ⟨a,(g j y).2.1 (cJ.2 n),n,w⟩;exact d i c _ e};rw[<- _cij m];refine ph h.1 _ (fun b l=>?_);obtain⟨i,c,rfl⟩:=_mg.1 l;exact(hβ i c).2
lemma mc {D:Dag} (h:ai 14 D) (x:aq D) (P:o) (l:P⊆aU 0) (y:P⊆al 14 D) (Oc Ct I:o) (n:∀ i∈Oc,aA i⊆P/\aQ 14 D P (aA i)) (p:∀ c∈Ct,c∉Oc/\((aA c∩P).card<=2 \/(aA c⊆P/\¬ aQ 14 D P (aA c)))) (K:∀ i∈I,i∈aa 14 D/\aA i⊆P):2*Oc.card+I.card+(Ct.biUnion (fun c=>aA c∩P)).card + (al 14 D).card<=2*P.card+bd 14 D:=by
 classical
 have L:=aK;have M:=aC x;obtain⟨b,g⟩:=bt h x;have A:∀ a∈P,∀ b∈P,¬ aO a b:=fun a d b g=>dB 0 a (l d) b (l g);have B:P.card<=7:=(_cl l).trans V
 obtain⟨E,C,Q⟩:=kH L h M P I (fun i k=>
  ⟨(K i k).1,aA i,(K i k).2,(iY i).ge,fun a d=>cJ.1 d⟩)
 have q:∀ f∈Ct.biUnion (fun c=>aA c∩P),∃ c∈Ct,f∈aA c∩P:=fun f r=>mem_biUnion.1 r;choose! ct s using q
 have m:=qO h.1 B (Oc.image aA) (fun T t=>by
  obtain⟨i,k,rfl⟩:=_mg.1 t
  exact⟨iY i,(n i k).2⟩)
  (fun T t T' t' G=>by
   obtain⟨i,k,rfl⟩:=_mg.1 t;obtain⟨j,W,rfl⟩:=_mg.1 t';have:=dM i j (fun e=>G (e▸rfl)) univ
   simpa[aA] using this)
  E Q (Ct.biUnion (fun c=>aA c∩P)) (fun f=>aA (ct f)∩P)
  (fun f r=>by
   obtain⟨R,u⟩:=s f r;refine jM L h.1 M (X:=insert (ct f) (P\(aA (ct f)∩P))) inter_subset_right ?_ ?_ (fun a d=>mem_insert_of_mem d) u ⟨ct f,mem_insert_self _ _,bl (cJ.1 (_mn.1 u).1)⟩
   · rcases (p _ R).2 with H|⟨H,N⟩
     · exact Or.inl H
     · rw[inter_eq_left.2 H];exact Or.inr ⟨iY _,N⟩
   · have v:∀ a∈P\(aA (ct f)∩P),¬ aO (ct f) a:=by
      intro a d w;rw[_md,_mn,cJ] at d;exact d.2 ⟨w,d.1⟩
     intro a d b g;rcases _mi.1 d with rfl|d <;> rcases _mi.1 g with rfl|g;{exact dv _};{exact v b g};{exact fun J=>v a d (bl J)}
     · exact A a (_md.1 d).1 b (_md.1 g).1)
  (fun f r T t=>by
   obtain⟨i,k,rfl⟩:=_mg.1 t;have:=dM (ct f) i (fun e=>(p _ (s f r).1).1 (e▸k)) P
   rwa[show univ.filter (fun z=>aO i z)∩P=aA i from inter_eq_left.2 (n i k).1] at this)
 have N:=co h P (by rw[fN x];simp);have S:=cZ h.1 b g P;rw[inter_eq_left.2 y] at S;rw[_cii _ (fun i j e=>qf e),C] at m;omega
lemma kp {D:Dag} (h:ai 14 D) (G:aq D) (hB:bd 14 D=(al 14 D).card) (h0:(0:O)∈aa 14 D):False:=by
 classical
 have H:=aK;have I:=aC G;obtain⟨b,hb⟩:=bt h G;have p:aj 14 D b=∅:=by{have:=bS h.1 b hb;exact card_eq_zero.1 (by omega)};have g:∀ x,(af 14 D x).card<=2:=by{intro x;have f:=ez H h I b hb x;have d:=_cl (inter_subset_left:({x}:o)∩al 14 D⊆{x});rw[p] at f;simp only[filter_empty,_ce,_cs] at f d;omega};obtain⟨e,J,-,K,L,q,M,-⟩:=ci H h I h0;have i:∀ u:O,aO 0 u->∃ Z,(∀ t,t≠u->Z∉af 14 D t) /\∀ w:O,aO w u->w≠0->am Z∈af 14 D w:=by
  intro u s;have hY:am e∈af 14 D u:=ak.2 ⟨J,q u s,by rw[show(am e).1=e.1 from rfl,L];simp⟩;obtain⟨Z,-,N,P,-⟩:=gd h G h0 (fun Q=>dv 0 (by rw[Q] at s;exact s)) M hY (g u);refine⟨Z,P,fun w hw j=>?_⟩;obtain⟨e',f,d,-,-,-⟩:=cg H h.1 I hw;rw[N,_mi,_ms] at d;rcases d with d|d
  · have R:e'=e:=by rw[<- aB e',d,aB]
    rw[R] at f;have:=(ak.1 f).2.1;rw[K,_ms] at this;exact(j this).elim
  · rw[<- d,aB];exact f
 have k:∀ w w' u:O,aO 0 u->aO w u->aO w' u->w≠0->w'≠0->w≠w' ->aO w 9->u≠9->∃ r,am r∈af 14 D 9/\w∈ag 14 D (aw D r) /\∀ a,a≠w->¬ aO a w'->a∉ag 14 D (aw D r):=by{intro w w' u s S v j y hww' T U;obtain⟨Z,P,A⟩:=i u s;obtain⟨r,B,m,-,-,-⟩:=cg H h.1 I T;have W:r≠am Z:=by{intro X;rw[X,aB] at m;exact P 9 (Ne.symm U) m};refine⟨r,m,(ak.1 B).2.1,fun a ha haw' E=>?_⟩;obtain⟨e3,f,d,R⟩:=bR h G (x:=w) (a:=a) (b:=w') (Ne.symm ha) hww' haw';have c:({am Z,r}:Finset (ℕ×_d))⊆af 14 D w:=by{intro x n;rcases _mi.1 n with rfl|n;{exact A w S j};{rw[_ms.1 n];exact B}};have Y:=_eqc c (by rw[_c2 (Ne.symm W)];exact g w);rw[<- Y,_mi,_ms] at f;rcases f with rfl|rfl;{exact R (ak.1 (A w' v y)).2.1};{exact d E}};obtain⟨r1,a1,b1,c1⟩:=k 1 3 7 V V V V V V V V;obtain⟨r5,a5,b5,c5⟩:=k 5 4 10 V V V V V V V V;obtain⟨r6,a6,b6,c6⟩:=k 6 2 8 V V V V V V V V;have h3:am r1≠am r5:=fun F=>
  c1 5 V V (by rw[<- aB r1,F,aB];exact b5)
 have h5:am r1≠am r6:=fun F=>
  c1 6 V V (by rw[<- aB r1,F,aB];exact b6)
 have h6:am r5≠am r6:=fun F=>
  c5 6 V V (by rw[<- aB r5,F,aB];exact b6)
 have c:({am r1,am r5,am r6}:Finset (ℕ×_d))⊆af 14 D 9:=by{intro x n;simp only[_mi,_ms] at n;rcases n with rfl|rfl|rfl <;> assumption};have:=_cl c;rw[_cin (by simp[h3,h5]),_c2 h6] at this;have:=g 9;omega
lemma ok {D:Dag} (h:ai 14 D) (a:aq D) (c:bd 14 D<=(al 14 D).card) (d:(0:O)∈aa 14 D):False:=by
 obtain⟨b,e⟩:=bt h a;exact kp h a (le_antisymm c (dX h.1 b e)) d
lemma qV {D:Dag} (h:ai 14 D) (b:aq D) (c:ap 14 D<=13) (a:aa 14 D={0}):False:=by
 have d:=aV 14 D;have e:=dC 14 D;rw[a,_cs] at d;exact ok h b (by omega) (by rw[a];simp)
def dE (k:Fin 7):O:=⟨k.val,by omega⟩
lemma ed:Function.Injective dE:=V
lemma eU:∀ k:Fin 7,aA (dE k)⊆aU 0:=by decide +kernel
lemma qW:∀ M:Finset (Fin 7),M.Nonempty ->min (M.card+2) 7<=((M.image dE).biUnion (fun c=>aA c∩aU 0)).card:=by decide +kernel
lemma gY {D:Dag} (h:ai 14 D) (u:aq D) (G:ap 14 D<=13) (q:ℕ) (B:q=5\/q=6\/q=7) (v:∀ i:O,i∈aa 14 D↔i.val<q):False:=by
 classical
 obtain⟨b,H⟩:=bt h u;have x:aU 0⊆al 14 D:=by
  intro a C;by_contra y;have:=(v a).1 (aN.2 y);simp only[aU,_mf,_mv,true_and] at C;have P:¬ a.val<7:=by simpa using C
  omega
 let E:=univ.filter (fun k:Fin 7=>aQ 14 D (aU 0) (aA (dE k)));let f:=univ.filter
  (fun k:Fin 7=>¬ aQ 14 D (aU 0) (aA (dE k)))
 let g:=univ.filter (fun k:Fin 7=>k.val<q);have n:∀ k∈g,dE k∈aa 14 D:=fun k d=>(v _).2 (_mf.1 d).2
 have p:=mc h u (aU 0) (Subset.refl _) x (E.image dE) (f.image dE) (g.image dE) (fun i l=>by
  obtain⟨k,d,rfl⟩:=_mg.1 l
  exact⟨eU k,(_mf.1 d).2⟩)
  (fun c I=>by
   obtain⟨k,d,rfl⟩:=_mg.1 I;refine⟨fun I'=>?_,Or.inr ⟨eU k,(_mf.1 d).2⟩⟩;obtain⟨k',d',A⟩:=_mg.1 I';rw[ed A] at d'
   exact(_mf.1 d).2 (_mf.1 d').2)
  (fun i l=>by
   obtain⟨k,d,rfl⟩:=_mg.1 l
   exact⟨n k d,eU k⟩)
 have m:=kn h u (aU 0) (dB 0) ((f∩g).image dE) (fun i l=>by
  obtain⟨k,d,rfl⟩:=_mg.1 l;rw[_mn] at d
  exact⟨n k d.2,eU k,(_mf.1 d.1).2⟩)
 rw[_cii _ ed] at m;rw[_cii _ ed,_cii _ ed] at p;have e:E.card+f.card=7:=by{have:=card_filter_add_card_filter_not (s:=(univ:Finset (Fin 7))) (fun k:Fin 7=>aQ 14 D (aU 0) (aA (dE k)));simpa using this};have j:g.card=q:=by{rcases B with rfl|rfl|rfl <;> rfl};have J:f.card<=(f∩g).card+(7 - q):=by
  have Q:=card_inter_add_card_sdiff f g;have F:(f\g).card<=(univ\g).card:=
   _cl (sdiff_subset_sdiff (subset_univ _) (Subset.refl _))
  rw[card_univ_sdiff,j,Fintype.card_fin] at F;omega
 have K:(aU 0).card=7:=V;have L:=aV 14 D;have M:(aa 14 D).card=q:=by
  have:aa 14 D=g.image dE:=by
   ext i;rw[v,_mg];constructor
   · intro l
     have:i.val<7:=by omega
     exact⟨⟨i.val,this⟩,_mf.2 ⟨_mv _,l⟩,rfl⟩
   · rintro⟨k,d,rfl⟩
     exact(_mf.1 d).2
  rw[this,_cii _ ed,j]
 have F:=dX h.1 b H;have R:=bg 14 D;have t:f.Nonempty->min (f.card+2) 7 <=((f.image dE).biUnion (fun c=>aA c∩aU 0)).card:=qW f;by_cases N:bd 14 D=(al 14 D).card;{exact kp h u N ((v 0).2 (by rcases B with rfl|rfl|rfl <;> decide))}
 · rcases eq_empty_or_nonempty f with w|w
   · rw[w] at e
     simp only[_ce] at e;omega
   · have:=t w
     have:=_cp.2 w;omega
lemma rr {D:Dag} (h:ai 14 D) (b:aq D) (a:D.length<=26) (c:aa 14 D={0,1,2,3,4,5,6}):False:=gY h b (go h a).2 7 (by omega) (by rw[c];decide)
lemma rs {D:Dag} (h:ai 14 D) (b:aq D) (a:ap 14 D<=13) (c:aa 14 D={0,1,2,3,4,5}):False:=gY h b a 6 (by omega) (by rw[c];decide)
lemma lC {D:Dag} (h:ai 14 D) (b:aq D) (a:ap 14 D<=13) (c:aa 14 D={0,1,2,3,4}):False:=gY h b a 5 (by omega) (by rw[c];decide)
def jQ:o:={7,8,9,10,12,13}
def ol (f:O):o:=if f=7 then {3,8,9,10,13} else if f=8 then {6,7,10,12,13} else {4,7,8,9,12}
lemma sq:∀ i∈({0,1,2,5}:o),(∃ a∈({7,8,10}:o),ab i a=true) /\∀ f∈({7,8,10}:o),∃ a∈ol f,ab i a=true:=by decide +kernel
lemma oK:∀ f∈({7,8,10}:o),(∀ a∈ol f,∀ b∈ol f,ab a b=false) /\({7,8,10}:o).erase f⊆ol f/\∃ a∈ol f,ab f a=true:=by
 decide +kernel
lemma oL:∀ i∈({0,1,2,5}:o),aA i⊆jQ:=by decide +kernel
lemma qC:∀ c∈({3,4,6}:o),c∉({0,1,2,5}:o) /\(aA c∩jQ).card<=2:=by decide +kernel
lemma sE:∀ a∈jQ,a∉({0,1,2,5,11}:o):=V
lemma sj :(({3,4,6}:o).biUnion (fun c=>aA c∩jQ)).card=6:=by
 decide +kernel
lemma rt {D:Dag} (h:ai 14 D) (n:aq D) (d:∀ i∈({0,1,2,5}:o),i∈aa 14 D):(al 14 D).card+3<=bd 14 D:=by
 have p:=aK;have q:=aC n;obtain⟨b,l⟩:=bt h n;obtain⟨pos,e⟩:=bQ p h q;have k:=(e.1 0 (d 0 V)).2.2.1;have g:=nb p h q b l e {7,8,10} {0,1,2,5} ol (fun i m=>⟨d i m,(sq i m).1.imp (fun a c=>⟨c.1,(ad _ _).1 c.2⟩),fun f j=>((sq i m).2 f j).imp (fun a c=>⟨c.1,(ad _ _).1 c.2⟩)⟩) (fun f j=>⟨fun a c b l=>aG.1 ((oK f j).1 a c b l),(oK f j).2.1,(oK f j).2.2.imp (fun a c=>⟨c.1,(ad _ _).1 c.2⟩)⟩) rfl V V V (k 7 V) (k 8 V) (k 7 V) (k 10 V);rw[show({0,1,2,5}:o).card=4 from rfl] at g;omega
lemma nm {D:Dag} (h:ai 14 D) (k:aq D) (z:ap 14 D<=13) (l:aa 14 D={0,1,2,5,11}):False:=by
 classical
 have m:=aV 14 D;rw[l,show({0,1,2,5,11}:o).card=5 from rfl] at m;have d:∀ i∈({0,1,2,5}:o),i∈aa 14 D:=by rw[l];decide
 have n:=rt h k d;have f:jQ⊆aU 0:=V;have p:jQ⊆al 14 D:=by{intro a q;by_contra r;have v:=aN.2 r;rw[l] at v;exact sE a q v};let w:=({0,1,2,5}:o).filter (fun i=>aQ 14 D jQ (aA i));let x:=({0,1,2,5}:o).filter (fun i=>¬ aQ 14 D jQ (aA i));have g:=mc h k jQ f p w {3,4,6} {0,1,2,5} (fun i e=>⟨oL i (_mf.1 e).1,(_mf.1 e).2⟩) (fun c y=>⟨fun y'=>(qC c y).1 (_mf.1 y').1,Or.inl (qC c y).2⟩) (fun i e=>⟨d i e,oL i e⟩);have u:=kn h k jQ (fun a q b A=>dB 0 a (f q) b (f A)) x (fun i e=>⟨d i (_mf.1 e).1,oL i (_mf.1 e).1,(_mf.1 e).2⟩);have j:w.card+x.card=4:=card_filter_add_card_filter_not (s:=({0,1,2,5}:o)) (fun i=>aQ 14 D jQ (aA i));rw[sj,show({0,1,2,5}:o).card=4 from rfl,show jQ.card=6 from rfl] at g;have B:=bg 14 D;omega
abbrev md:O->O->Prop:=fun u v=>aO u v
def aY (D:Dag) (b:O->ℕ) (x:O):Finset (Σ _:ℕ,ℕ):=(aj 14 D b).filter (fun u=>x∈ag 14 D u.1)
lemma ax {D:Dag} {b:O->ℕ} {x:O} {u:Σ _:ℕ,ℕ}:u∈aY D b x↔u∈aj 14 D b/\x∈ag 14 D u.1:=_mf
lemma rv {n:ℕ} {D:Dag} {b:Fin n->ℕ} {u:Σ _:ℕ,ℕ} (a:u∈aj n D b):2<=aF D u.1:=by
 have:=(dW.mp (_mf.mp (_md.mp a).1).1).2;omega
lemma fB {n:ℕ} {D:Dag} {b:Fin n->ℕ} {u:Σ _:ℕ,ℕ} (a:u∈aj n D b) {x:Fin n} (c:x∈ag n D u.1):x∈al n D:=eX.2 ⟨u.1,rv a,c⟩
lemma bi {D:Dag} (h:ai 14 D) (a:aq D) (b:O->ℕ) (c:aM 14 D b) (x:O):(af 14 D x).card+(aW 14 D (ao 14 D {x})).card<=2+(aY D b x).card:=by
 have e:=ez aK h (aC a) b c x;have d:=_cl (inter_subset_left:({x}:o)∩al 14 D⊆{x});rw[_cs] at d;unfold aY;omega
lemma me {D:Dag} (h:ai 14 D) (a:aq D) (b:O->ℕ) (c:aM 14 D b) {x:O} (d:x∈al 14 D):(af 14 D x).card+(aW 14 D (ao 14 D {x})).card=2+(aY D b x).card:=by
 have e:=ez aK h (aC a) b c x;rw[inter_eq_left.2 (singleton_subset_iff.2 d),_cs] at e;unfold aY;omega
lemma eh {n:ℕ} {D:Dag} (b:au n D) {x:Fin n} {e:ℕ×_d} (c:e∈af n D x):am e∉af n D x:=by
 intro f;obtain⟨g,d,h⟩:=ak.mp c;have d':=(ak.mp f).2.1;apply h;rw[cB b g (cY b c),_mn];obtain⟨j,s⟩:=e;cases s;{exact⟨by simpa[aw] using d,by simpa[aw,am] using d'⟩};{exact⟨by simpa[aw,am] using d',by simpa[aw] using d⟩}
section Assigned
variable {D : Dag} {pos : Fin 14 → ℕ × Bool}
lemma aI (b:bA 14 md D pos) {i a:O} (d:i∈aa 14 D) (c:aO i a):pos i∈af 14 D a:=by
 obtain⟨e,f,g,-⟩:=b.1 i d;exact ak.2 ⟨e,g a c,by rw[f];exact notMem_empty a⟩
lemma ei (a:bA 14 md D pos) {i t:O} (b:i∈aa 14 D) (c:am (pos i)∈af 14 D t):t=i:=by
 have:=(ak.1 c).2.1;rw[show aw D (am (pos i))=aw D ((pos i).1,!(pos i).2) from rfl,(a.1 i b).2.2.2] at this;exact _ms.1 this
lemma pn (h:ai 14 D) (d:aq D) (a:bA 14 md D pos) {i:O} (b:i∈aa 14 D):af 14 D i={am (pos i)}:=by
 obtain⟨e,-,-,m,-,-,f,-⟩:=ci aK h (aC d) b;obtain⟨g,j,-,k⟩:=a.1 i b
 have c:am (pos i)∈af 14 D i:=ak.2 ⟨g,by
  rw[show aw D (am (pos i))=aw D ((pos i).1,!(pos i).2) from rfl,k];exact _mss i,by
  rw[show(am (pos i)).1=(pos i).1 from rfl,j];exact notMem_empty i⟩
 have l:af 14 D i={e}:=f;rw[l] at c⊢;rw[_ms.1 c]
lemma sF (h:ai 14 D) (c:aq D) (a:bA 14 md D pos) {i x:O} (d:i∈aa 14 D) (b:x≠i) (g:pos i∈af 14 D x) (j:(af 14 D x).card<=2):∃ Z,Z≠pos i/\af 14 D x={pos i,Z}/\∀ t,t≠x->Z∉af 14 D t:=by
 obtain⟨Z,e,f,k,-⟩:=gd h c d b (pn h c a d) (by rw[aB];exact g) j;rw[aB] at e f;exact⟨Z,e,f,k⟩
lemma rx (h:ai 14 D) (d:aq D) (b:bL 14 D=0) (a:bA 14 md D pos) {i v:O} (e:i∈aa 14 D) (c:aO i v) (f:∀ p∈af 14 D v,p.1≠(pos i).1->¬ ag 14 D (aw D (am p))⊆{i}):∀ t,t∈ag 14 D (aw D (pos i))↔aO i t:=by
 have:=oh aK h (aC d) b e (pn h d a e) c f;rwa[aB] at this
end Assigned
lemma po {D:Dag} (h:ai 14 D) (c:aq D) (a:bL 14 D=0) {i:O} (d:i∈aa 14 D):∀ w,Relation.ReflTransGen (bk 14 D) i.val w->aF D w<=1:=by
 intro w f;by_contra j;have g:=eM aK h.1 (aC c) d (gr aK h (aC c) a d f) (by omega);have e:=fJ h.1 a (b:=w) (by omega);rw[g] at e;exact not_nonempty_empty e
lemma qX {D:Dag} (h:ai 14 D) (c:aq D) (d:bL 14 D=0) {i:O} (e:i∈aa 14 D) {T:o} (f:T⊆aU i):aQ 14 D T (aA i∩T):=by
 by_contra b
 have:=kn h c (aU i) (dB i) {i} (fun j g=>by
  rw[_ms.1 g];refine⟨e,fun a k=>nd (cJ.1 k),?_⟩;rintro⟨w,l⟩
  exact b ⟨w,by rw[<- l,inter_assoc,inter_eq_right.2 f]⟩)
 rw[_cs] at this;omega
def kV (T:o) (f:O):o:=T.erase f∪univ.filter (fun a=>ab f a=true/\∀ g∈T.erase f,ab a g=false)
def kK (T J:o):_d:=decide (∀ i∈J,(∃ a∈T,ab i a=true) /\∀ f∈T,∃ a∈kV T f,ab i a=true) && decide (∀ f∈T,(∀ a∈kV T f,∀ b∈kV T f,ab a b=false) /\∃ a∈kV T f,ab f a=true) && decide (T.card=3/\J.card=3) && decide (∀ i∈J,T⊆aU 0/\T⊆aU i/\aA i⊆aU 0 /\(aA i∩T).card=2) && decide (∀ i∈J,∀ j∈J,aA j∩T⊆aA i∩T->j=i) && decide (∀ t∈T,(J.filter (fun i=>ab i t=true)).card<=2 /\∀ i∈J,ab i t=false->T.erase t⊆aA i)
lemma gZ {T J:o} (h:kK T J=true):(∀ i∈J,(∃ a∈T,ab i a=true)/\∀ f∈T,∃ a∈kV T f,ab i a=true) /\(∀ f∈T,(∀ a∈kV T f,∀ b∈kV T f,ab a b=false) /\∃ a∈kV T f,ab f a=true) /\(T.card=3/\J.card=3) /\(∀ i∈J,T⊆aU 0/\T⊆aU i/\aA i⊆aU 0 /\(aA i∩T).card=2) /\(∀ i∈J,∀ j∈J,aA j∩T⊆aA i∩T->j=i) /\∀ t∈T,(J.filter (fun i=>ab i t=true)).card<=2 /\∀ i∈J,ab i t=false->T.erase t⊆aA i:=by
 simpa only[kK,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using h
lemma jo {D:Dag} {T J:o} (e:kK T J=true) (k:∀ i∈J,i∈aa 14 D):(∀ i∈J,i∈aa 14 D/\(∃ a∈T,md i a)/\∀ f∈T,∃ a∈kV T f,md i a) /\∀ f∈T,(∀ a∈kV T f,∀ b∈kV T f,¬ md a b)/\T.erase f⊆kV T f /\∃ a∈kV T f,md f a:=by
 obtain⟨h,j,-⟩:=gZ e;exact⟨fun i g=>⟨k i g,(h i g).1.imp (fun _ c=>⟨c.1,(ad _ _).1 c.2⟩),fun f d=>((h i g).2 f d).imp (fun _ c=>⟨c.1,(ad _ _).1 c.2⟩)⟩,fun f d=>⟨fun a c b l=>aG.1 ((j f d).1 a c b l),subset_union_left,(j f d).2.imp (fun _ c=>⟨c.1,(ad _ _).1 c.2⟩)⟩⟩
lemma sk {D:Dag} (h:ai 14 D) (s:aq D) (L:bL 14 D<=1) {T J:o} (n:kK T J=true) (t:∀ i∈J,i∈aa 14 D):(al 14 D).card+3<=bd 14 D:=by
 classical
 have z:=aK;have A:=aC s;obtain⟨b,B⟩:=bt h s;obtain⟨pos,g⟩:=bQ z h A;obtain⟨t',hA'⟩:=jo n t;obtain⟨-,-,⟨C,E⟩,d,p,-⟩:=gZ n;have l:∀ i∈J,∃ M,aQ 14 D T M/\aA i∩T⊆M /\(aQ 14 D (aU 0) (aA i)->M=aA i∩T):=by
  intro i c;by_cases r:aQ 14 D (aU 0) (aA i)
  · obtain⟨w,F⟩:=r
    have:ag 14 D w∩T=aA i∩T:=by{rw[<- F,inter_assoc,inter_eq_right.2 (d i c).1]};exact⟨_,⟨w,rfl⟩,this▸Subset.refl _,fun _=>this⟩
  · exact⟨ag 14 D (aw D (pos i))∩T,⟨_,rfl⟩,fun a x=>by
     rw[_mn,cJ] at x;exact _mn.2 ⟨(g.1 i (t i c)).2.2.1 a x.1,x.2⟩,
     fun G=>absurd G r⟩
 choose! M l using l
 have y:=kn h s (aU 0) (dB 0) (J.filter (fun i=>¬ aQ 14 D (aU 0) (aA i))) (fun i c=>by
  rw[_mf] at c
  exact⟨t i c.1,(d i c.1).2.2.1,c.2⟩)
 have k:Set.InjOn M J:=by
  intro i c j m f;by_contra e;have q:∀ i∈J,∀ j∈J,M i=M j->i≠j ->¬ aQ 14 D (aU 0) (aA i):=by
   intro i c j m f e r
   exact e (p i c j m (by
    rw[<- (l i c).2.2 r,f];exact(l j m).2.1)).symm
  have H:i∈J.filter (fun i=>¬ aQ 14 D (aU 0) (aA i)):=
   _mf.2 ⟨c,q i c j m f e⟩
  have I:j∈J.filter (fun i=>¬ aQ 14 D (aU 0) (aA i)):=
   _mf.2 ⟨m,q j m i c f.symm (Ne.symm e)⟩
  have:=one_lt_card.2 ⟨i,H,j,I,e⟩;omega
 have:=pj z h A b B g T J (kV T) t' hA' (J.image M) (fun X K=>by
  obtain⟨i,c,rfl⟩:=_mg.1 K;have:=_cl (l i c).2.1;rw[(d i c).2.2.2] at this
  exact⟨this,(l i c).1⟩)
 rw[_cij k] at this;omega
lemma sl {D:Dag} (h:ai 14 D) (g:aq D) (a:∀ i∈({0,1,2}:o),i∈aa 14 D):(al 14 D).card+2<=bd 14 D:=by
 have j:=aK;have k:=aC g;obtain⟨b,n⟩:=bt h g;obtain⟨pos,c⟩:=bQ j h k;have d:kK {7,8,13} {0,1,2}=true:=by decide +kernel
 obtain⟨hJ',hA'⟩:=jo d a;have l:=(c.1 0 (a 0 V)).2.2.1;have m:=(c.1 1 (a 1 V)).2.2.1;have:=nb j h k b n c {7,8,13} {0,1,2} (kV {7,8,13}) hJ' hA' rfl V V V (l 7 V) (l 8 V) (m 7 V) (m 13 V);rw[show({0,1,2}:o).card=3 from rfl] at this;omega
lemma ry {D:Dag} (h:ai 14 D) (b:aq D) (c:ap 14 D<=13) (a:∀ i∈({0,1,2}:o),i∈aa 14 D) (d:10<=(al 14 D).card):(al 14 D).card+3<=bd 14 D:=by
 have e:=sl h b a;have f:=bg 14 D;exact sk h b (by omega) (by decide +kernel:kK {7,8,13} {0,1,2}=true) a
lemma pp {D:Dag} (h:ai 14 D) (F:aq D) (x:bL 14 D=0) (U:bd 14 D<=(al 14 D).card+3) (b:O->ℕ) (M:aM 14 D b) {T J:o} (p:kK T J=true) (y:∀ i∈J,i∈aa 14 D):(∀ t∈T,(af 14 D t).card<=3/\aW 14 D (ao 14 D {t})=∅) /\∀ u∈aj 14 D b,(ag 14 D u.1∩T).Nonempty:=by
 classical
 have G:=aK;have H:=aC F;obtain⟨pos,k⟩:=bQ G h H;obtain⟨y',hA'⟩:=jo p y;obtain⟨-,-,⟨B,N⟩,c,q,l⟩:=gZ p;have n:Set.InjOn (fun i=>aA i∩T) J:=fun i g j P C=>q j P i g (by rw[show aA i∩T=aA j∩T from C])
 obtain⟨d,I,Q⟩:=pk G h H b M k T J (kV T) y' hA' (J.image (fun i=>aA i∩T)) (fun X R=>by
  obtain⟨i,g,rfl⟩:=_mg.1 R
  exact⟨(c i g).2.2.2,qX h F x (y i g) (c i g).2.1⟩) B
  (by rw[_cij n];omega)
 refine⟨fun t w=>⟨?_,(I t w).1⟩,Q⟩;obtain⟨e1,E⟩:=(I t w).2;have r:af 14 D t⊆insert e1 ((J.filter (fun i=>ab i t=true)).image pos):=by
  intro e K;rcases E e K with rfl|L;{exact mem_insert_self _ _}
  · obtain⟨i,g,rfl⟩:=_mg.1 L
    refine mem_insert_of_mem (_mg.2 ⟨i,_mf.2 ⟨g,?_⟩,rfl⟩);by_contra m;rw[Bool.not_eq_true] at m;refine d (aw D (pos i)) (fun a S=>?_);by_cases v:a=t;{rw[v];exact(ak.1 K).2.1};{exact(k.1 i (y i g)).2.2.1 a (cJ.1 ((l t w).2 i g m (_me.2 ⟨v,S⟩)))}
 have L:=_cl r;have W:=card_insert_le e1 ((J.filter (fun i=>ab i t=true)).image pos);have Y:=card_image_le (s:=J.filter (fun i=>ab i t=true)) (f:=pos);have Z:=(l t w).1;omega
def gE (c v:O):Option _d:=if v=c then some true else if ab c v=true then some false else none
def eD (l:_F ℕ) (k:Fin 10):O:=Fin.ofNat 14 (l.getD k.val 0)
abbrev kq (c:O) (l:_F ℕ):Prop:=(∀ a b:Fin 10,eD l a=eD l b->a=b) /\(∀ v:O,gE c v=none↔∃ i:Fin 10,eD l i=v) /\∀ u v:Fin 10,ab (eD l u) (eD l v)=gV u v
def sG:_F ℕ:=[2,4,5,6,13,12,8,10,11,9]
def sH:_F ℕ:=[8,9,10,13,6,0,2,5,1,4]
lemma om:kq 7 sG:=by decide +kernel
lemma oo:kq 3 sH:=by decide +kernel
lemma pq {D:Dag} (h:ai 14 D) (hD:aq D) (b:O->ℕ) (n:aM 14 D b) {c:O} {l:_F ℕ} (r:kq c l) (hc:c∈al 14 D) (X:o) (P:∀ x∈X,x∈al 14 D/\x≠c /\(∀ u∈aj 14 D b,x∈ag 14 D u.1->c∈ag 14 D u.1) /\∃ w,x∈ag 14 D w/\c∈ag 14 D w):∃ E:Dag,ai 10 E/\dg 10 bI E /\ap 10 E+((aY D b c).card+X.card+1)<=ap 14 D /\bd 10 E+((aY D b c).card+X.card+1)<=ap 14 D /\∀ i:Fin 10,(∀ w,Relation.ReflTransGen (bk 14 D) (eD l i).val w ->aF D w<=1)->i∈aa 10 E:=by
 classical
 have hG:=aK;have hC:=aC hD;have H:=h.1;obtain⟨I,s,J⟩:=r;have Q:fv (gE c) (eD l):=⟨fun a b R=>I a b R,s⟩;have hρc:gE c c=some true:=by simp[gE]
 have hT:∀ d a:O,gE c d=some true->md d a->gE c a=some false:=by{intro d a p t;have hd:d=c:=by{by_contra A;unfold gE at p;simp only[A,ite_false] at p;split at p <;> simp at p};subst hd;have A:a≠d:=fun S=>dv d (S▸t);simp[gE,A,(ad d a).2 t]};have K:(fun u v:Fin 10=>md (eD l u) (eD l v))=bI:=by
  funext u v
  exact propext (by
   show aO _ _↔gV u v=true
   rw[<- J u v];exact(ad _ _).symm)
 obtain⟨E,hE,T,hsur,U,B⟩:=kJ H Q hC (fun _ _ W=>bl W) hT (by rw[K];exact eS) (by norm_num);have L:∀ x∈al 14 D,(⟨b x,0⟩:Σ _:ℕ,ℕ)∈dq 14 D:=fun x f=>
  dW.2 ⟨bP.2 (dc H (w:=b x) (by
   have:=(n x f).1;omega)),by
   show 0+1<aF D (b x);have:=(n x f).1;omega⟩
 have k:∀ x∈insert c X,x∈al 14 D:=fun x f=>by{rcases _mi.1 f with rfl|f;{exact hc};{exact(P x f).1}};have m:Set.InjOn (fun x=>(⟨b x,0⟩:Σ _:ℕ,ℕ)) (insert c X:o):=by{intro x f y hy Y;have p:b x=b y:=congrArg Sigma.fst Y;have t:=(n x (k x f)).2;rw[p,(n y (k y hy)).2] at t;exact(singleton_injective t).symm};have M:Disjoint (aY D b c) ((insert c X).image (fun x=>(⟨b x,0⟩:Σ _:ℕ,ℕ))):=by{rw[_dl];intro u Z h0;obtain⟨x,f,rfl⟩:=_mg.1 h0;exact(_md.1 (ax.1 Z).1).2 (_mg.2 ⟨x,k x f,rfl⟩)};have q:aY D b c∪(insert c X).image (fun x=>(⟨b x,0⟩:Σ _:ℕ,ℕ))⊆ dq 14 D:=by
  intro u g;rcases _mu.1 g with g|g;{exact(_mf.1 (_md.1 (ax.1 g).1).1).1}
  · obtain⟨x,f,rfl⟩:=_mg.1 g
    exact L x (k x f)
 have j:∀ u∈aY D b c∪(insert c X).image (fun x=>(⟨b x,0⟩:Σ _:ℕ,ℕ)),u∉f5 D (gE c) (eD l):=by
  intro u g;rcases _mu.1 g with g|g;{exact iO H hρc (ax.1 g).2}
  · obtain⟨x,f,rfl⟩:=_mg.1 g
    rcases _mi.1 f with rfl|f
    · exact iO H hρc (by
       show x∈ag 14 D (b x)
       rw[(n x hc).2];exact _mss x)
    · obtain⟨C,F,N,w,hw⟩:=P x f
      obtain⟨z,h3,h4⟩:=hG.2.2.1 x c F;obtain⟨h5,-,-,e,he,-,h6⟩:=gt hG h hC b n F C N hw h3 h4
      have h7:b x∈aR 14 D x c:=f_.2 (by
       rw[(n x C).2]
       exact⟨_mss x,fun h8=>F (_ms.1 h8).symm⟩)
      exact mb (lB H hρc h7 (n x C).1 h5 he h6)
 have G:(aY D b c∪(insert c X).image (fun x=>(⟨b x,0⟩:Σ _:ℕ,ℕ))).card =(aY D b c).card+X.card+1:=by
  rw[_cud M,_cij m,
   _cin (fun h9=>(P c h9).2.1 rfl)]
  omega
 have p:=lA _ q j;have t:=lg _ q (fun u g hk=>j u g (nk hk));rw[G] at p t;exact⟨E,hE,K▸T,by omega,by omega,B⟩
lemma oM {D:Dag} (h:ai 14 D) (e:aq D) (b:O->ℕ) (f:aM 14 D b) {c:O} {l:_F ℕ} (a:kq c l) (g:c∈al 14 D) (X:o) (i:∀ x∈X,x∈al 14 D/\x≠c /\(∀ u∈aj 14 D b,x∈ag 14 D u.1->c∈ag 14 D u.1) /\∃ w,x∈ag 14 D w/\c∈ag 14 D w):(aY D b c).card+X.card+7<=ap 14 D:=by
 obtain⟨E,j,d,-,k,-⟩:=pq h e b f a g X i;have:=jO j d;omega
lemma qY {D:Dag} (h:ai 14 D) (e:aq D) (d:bL 14 D=0) (b:O->ℕ) (i:aM 14 D b) {c:O} {l:_F ℕ} (a:kq c l) (j:c∈al 14 D) (X:o) (k:∀ x∈X,x∈al 14 D/\x≠c /\(∀ u∈aj 14 D b,x∈ag 14 D u.1->c∈ag 14 D u.1) /\∃ w,x∈ag 14 D w/\c∈ag 14 D w) {i1 i2:Fin 10} (m:eD l i1∈aa 14 D) (n:eD l i2∈aa 14 D) (p:(i1=4/\i2=9)\/(i1=5/\i2=8)\/(i1=6/\i2=7)):(aY D b c).card+X.card+8<=ap 14 D:=by
 obtain⟨E,q,f,r,-,g⟩:=pq h e b i a j X k;have:=gW q f (g i1 (po h e d m)) (g i2 (po h e d n)) p;omega
lemma d5 {α:Type} [DecidableEq α] {s:Finset α} {a b c:α} (j:a∈s) (k:b∈s) (l:c∈s) (f:a≠b) (g:a≠c) (h:b≠c):3<=s.card:=by
 have d:({a,b,c}:Finset α)⊆s:=by{intro e i;simp only[_mi,_ms] at i;rcases i with rfl|rfl|rfl <;> assumption};have:=_cl d;rwa[_cin (by simp[f,g]),_c2 h] at this
lemma aS {α:Type} [DecidableEq α] {s:Finset α} {a b c:α} (i:a∈s) (j:b∈s) (k:c∈s) (f:a≠b) (g:a≠c) (h:b≠c) (m:s.card<=3):∀ e∈s,e=a\/e=b\/e=c:=by
 intro e l;by_contra d;rw[not_or,not_or] at d;have:=d5 (s:=s.erase e) (_me.2 ⟨Ne.symm d.1,i⟩) (_me.2 ⟨Ne.symm d.2.1,j⟩) (_me.2 ⟨Ne.symm d.2.2,k⟩) f g h;rw[card_erase_of_mem l] at this;omega
lemma gF {α:Type} [DecidableEq α] {s:Finset α} {a b:α} (f:a∈s) (g:b∈s) (d:a≠b) (i:s.card<=2):∀ e∈s,e=a\/e=b:=by
 intro e h;by_contra c;rw[not_or] at c;have:=d5 h f g c.1 c.2 d;omega
lemma sI:∀ i k t:O,ab i k=true->t≠i ->∃ q,ab i q=true/\q≠k/\q≠t/\ab t q=false:=by decide +kernel
lemma oN {D:Dag} (h:ai 14 D) (j:aq D) {x a b:O} (d:x≠a) (f:x≠b) (g:¬ aO a b) (c:∀ e∈af 14 D x,e∈af 14 D a\/e∈af 14 D b):False:=by
 obtain⟨e,k,l,m⟩:=bR h j d f g;rcases c e k with i|i;exacts [l (ak.1 i).2.1,m (ak.1 i).2.1]
lemma be {D:Dag} (h:ai 14 D) (j:aq D) {pos:O->ℕ×_d} (a:bA 14 md D pos) {x y:O} (c:aO x y):∃ e∈af 14 D x,am e∈af 14 D y /\(∀ i∈aa 14 D,e=pos i->y=i) /\∀ i∈aa 14 D,am e=pos i->x=i:=by
 obtain⟨e,f,g,-⟩:=cg aK h.1 (aC j) c;exact⟨e,f,g,fun i d b=>ei a d (b▸g),fun i d b=>ei a d (by rw[<- b,aB];exact f)⟩
def iP (D:Dag) (pos:O->ℕ×_d) (P Q:ℕ×_d):Prop:=bA 14 md D pos/\(∀ x,(af 14 D x).card<=3)/\P≠Q /\∀ x,3<=(af 14 D x).card->P∈af 14 D x/\Q∈af 14 D x
lemma oq {D:Dag} (h:ai 14 D) (g:aq D) (p:ap 14 D<=13) (q:(0:O)∈aa 14 D) (s:(al 14 D).card=12):∃ pos P Q,iP D pos P Q:=by
 classical
 have i:=aK;have j:=aC g;obtain⟨b,m⟩:=b_ i h.1 j;have c:=bD m;obtain⟨pos,a⟩:=bQ i h j;have t:=bS h.1 b c;have u:=dC 14 D;have v:bd 14 D=13:=by{by_contra r;exact ok h g (by omega) q};have d:∀ x,(af 14 D x).card<=3:=fun x=>by{have w:=bi h g b c x;have y:(aY D b x).card<=(aj 14 D b).card:=_cfl _ _;omega};by_cases n:(univ.filter (fun x:O=>3<=(af 14 D x).card)).Nonempty
 · obtain⟨P,Q,k,e⟩:=fW i h j b m (by omega) _ n (fun x f=>(_mf.1 f).2)
   exact⟨pos,P,Q,a,d,fun l=>k (l▸rfl),fun x f=>e x (_mf.2 ⟨_mv x,f⟩)⟩
 · exact⟨pos,(0,false),(1,false),a,d,by decide,fun x f=>(n ⟨x,_mf.2 ⟨_mv x,f⟩⟩).elim⟩
lemma nn {D:Dag} (h:ai 14 D) (s:aq D) (T:ap 14 D<=13) (G:aa 14 D={0,1}):False:=by
 have U:=aV 14 D;rw[G,show({0,1}:o).card=2 from rfl] at U;have b:(0:O)∈aa 14 D:=by rw[G];decide
 have d:(1:O)∈aa 14 D:=by rw[G];decide
 have k:∀ x:O,x∉({0,1}:o)->x∉aa 14 D:=fun x hx=>G▸hx;have u:∀ i∈aa 14 D,aO i 7:=by rw[G];decide
 obtain⟨pos,P,Q,a,B,W,v⟩:=oq h s T b (by omega);have I:=fun i F=>aI a F (u i F);have C:pos 0≠pos 1:=fun c=>absurd (a.2 0 b 1 d c) V;obtain⟨H,hH,-,J,-⟩:=be h s a (show aO 7 3 by decide);obtain⟨X,Y⟩:=v 7 (d5 (I 0 b) (I 1 d) hH C (fun c=>absurd (J 0 b c.symm) V) (fun c=>absurd (J 1 d c.symm) V));have R:∀ t,3<=(af 14 D t).card->∀ j∈aa 14 D,pos j∈af 14 D t:=by
  intro t ht j m;by_contra hn;obtain⟨hP,hQ⟩:=v t ht
  obtain⟨q,hq1,hq7,-,hq2⟩:=sI j 7 t ((ad _ _).2 (u j m)) (fun hti=>by
   rw[hti,pn h s a m,_cs] at ht
   omega)
  refine oN h s (fun e:(7:O)=t=>hn (e▸I j m)) hq7.symm (aG.1 hq2) (fun e c=>?_);rcases aS (I j m) X Y (fun e=>hn (e▸hP)) (fun e=>hn (e▸hQ)) W (B 7) e c with rfl|rfl|rfl;exacts [Or.inr (aI a m ((ad _ _).1 hq1)),Or.inl hP,Or.inl hQ]
 have n:∀ l i z:O,i∈aa 14 D->aO i l->aO l z ->z∉aa 14 D->∃ Z∈af 14 D l,(∀ e∈af 14 D l,e=Z\/∃ j∈aa 14 D,e=pos j) /\∀ y,aO l y->y∉aa 14 D->am Z∈af 14 D y:=by
  intro l i z F hil hlz hz;obtain⟨Z,E,-,hZf,-⟩:=be h s a hlz;have f:∀ j∈aa 14 D,pos j≠Z:=fun j m c=>hz (hZf j m c.symm▸m);have w:∀ e∈af 14 D l,e=Z\/∃ j∈aa 14 D,e=pos j:=by
   intro e c;by_cases K:3<=(af 14 D l).card
   · rcases aS (R l K 0 b) (R l K 1 d) E C (f 0 b) (f 1 d) (B l) e c with g|g|g
     exacts [Or.inr ⟨0,b,g⟩,Or.inr ⟨1,d,g⟩,Or.inl g]
   · rcases gF (aI a F hil) E (f i F) (by omega) e c with g|g
     exacts [Or.inr ⟨i,F,g⟩,Or.inl g]
  refine⟨Z,E,w,fun y hly hy=>?_⟩;obtain⟨e,c,hb,hf,-⟩:=be h s a hly;rcases w e c with rfl|⟨j,m,rfl⟩;exacts [hb,(hy (hf j m rfl▸m)).elim]
 have S:=k 2 V;obtain⟨Z8,L,a8,b8⟩:=n 8 0 2 b V V S;obtain⟨Z13,p,-,b13⟩:=n 13 1 2 d V V S;have m8:=b8 2 V S;have M:=b13 2 V S;have A:am Z8≠am Z13:=by
  intro c;have E:Z8=Z13:=by rw[<- aB Z8,c,aB]
  refine oN h s (by decide:(8:O)≠7) (by decide:(8:O)≠13) V (fun e c=>?_);rcases a8 e c with rfl|⟨j,m,rfl⟩;exacts [Or.inr (E▸p),Or.inl (I j m)]
 have r:∀(Z:ℕ×_d) (l i:O),Z∈af 14 D l->i∈aa 14 D ->l∉({0,1}:o)->pos i≠am Z:=fun Z l i E N hl c=>
  k l hl (ei a N (by rw[c,aB];exact E)▸N)
 by_cases K:3<=(af 14 D 2).card
 · rcases aS (R 2 K 0 b) (R 2 K 1 d) m8 C (r Z8 8 0 L b V) (r Z8 8 1 L d V) (B 2) _ M with g|g|g
   exacts [r Z13 13 0 p b V g.symm,r Z13 13 1 p d V g.symm,A g.symm]
 · exact oN h s (by decide:(2:O)≠6) (by decide:(2:O)≠4) V (fun e c=>by
    rcases gF m8 M A (by omega) e c with rfl|rfl
    exacts [Or.inl (b8 6 V (k 6 V)),Or.inr (b13 4 V (k 4 V))])
lemma dk {D:Dag} (h:ai 14 D) (j:aq D) {pos:O->ℕ×_d} (b:bA 14 md D pos) (z k v iz ik:O) (c:(∀ a∈({iz,ik}:o),a∈aa 14 D) /\∀ a∈({z,k,v}:o),a∉aa 14 D) (x:ab iz z=true/\ab ik k=true/\ab z k=true /\ab z v=true/\v≠k) (l:(af 14 D z).card<=2) (m:(af 14 D k).card<=2):False:=by
 obtain⟨g1,g2,g3,g4,g5⟩:=x;rw[ad] at g1 g2 g3 g4;have d:=c.1 iz (by simp);have f:=c.1 ik (by simp);have w:=c.2 k (by simp);obtain⟨Dk,-,n,p⟩:=sF h j b f (fun e:k=ik=>w (e▸f)) (aI b f g2) m;obtain⟨e,y,g,A,A'⟩:=be h j b g3;obtain⟨e',y',g',x',-⟩:=be h j b g4;rw[n,_mi,_ms] at g;have B:am e=Dk:=g.resolve_left (fun t=>c.2 z (by simp) (A' ik f t▸f));rcases gF (aI b d g1) y (fun t=>w (A iz d t.symm▸d)) l e' y' with u|u;{exact c.2 v (by simp) (x' iz d u▸d)};{exact p v g5 (by rw[<- B,<-u];exact g')}
def no (D:Dag) (pos:O->ℕ×_d) (P Q:ℕ×_d) (y:O):Prop:=∃ e,(e=P\/e=Q)/\(∀ i∈aa 14 D,e≠pos i) /\(∀ s,s≠y->am e∉af 14 D s)/\am e∈af 14 D y /\∃ i∈aa 14 D,pos i=P\/pos i=Q
lemma lD {D:Dag} (h:ai 14 D) (N:aq D) {pos:O->ℕ×_d} {P Q:ℕ×_d} (hc:iP D pos P Q) (x y t w ix iy xa xb:O) (k:(∀ a∈({ix,iy}:o),a∈aa 14 D) /\∀ a∈({x,y,w}:o),a∉aa 14 D) (hg:ab ix x=true/\ab iy y=true/\ab x y=true /\ab w y=true/\ab ix t=true/\ix≠iy/\x≠w/\x≠t/\x≠xa /\x≠xb/\ab w xa=false/\ab w xb=false/\ab t xa=false /\ab t xb=false) (R:3<=(af 14 D x).card) (S:3<=(af 14 D xa).card\/3<=(af 14 D xb).card):no D pos P Q y:=by
 obtain⟨b,v,z,g⟩:=hc;obtain⟨g1,g2,g3,g4,g5,g0,g6,g7,g8,g9,g10,g11,g12,g13⟩:=hg;rw[ad] at g1 g2 g3 g4 g5;rw[aG] at g10 g11 g12 g13;have l:=k.1 ix (by simp);have d:=k.1 iy (by simp);have hx:=k.2 x (by simp);have hy:=k.2 y (by simp);obtain⟨u,hu,gu1,gu2,gu3⟩:∃ u,3<=(af 14 D u).card/\x≠u/\¬ aO w u/\¬ aO t u:=by{rcases S with A|A;exacts [⟨xa,A,g8,g10,g12⟩,⟨xb,A,g9,g11,g13⟩]};obtain⟨B,C⟩:=g x R;obtain⟨e,T,m,hf,hf'⟩:=be h N b g3;obtain⟨e',T',m',-,W⟩:=be h N b g4;have G:∀(c:ℕ×_d) (s:O),c∈af 14 D x->c∈af 14 D s->x≠s ->¬ aO s u->c=P\/c=Q:=by
  intro c s Y Z h0 S';by_contra n;rw[not_or] at n;refine oN h N h0 gu1 S' (fun a ha=>?_);rcases aS B C Y z (Ne.symm n.1) (Ne.symm n.2) (v x) a ha with
   rfl|rfl|rfl
  exacts [Or.inr (g u hu).1,Or.inr (g u hu).2,Or.inl Z]
 have I:=G (pos ix) t (aI b l g1) (aI b l g5) g7 gu3;have hB:(∀ c∈af 14 D y,c=am e\/∃ i∈aa 14 D,c=pos i) ->e=P\/e=Q:=by{intro hA;refine G e w T ?_ g6 gu2;rcases hA _ m' with f|⟨i,J,f⟩;{rw[<- aB e,<-f,aB];exact T'};{exact(k.2 w (by simp) (W i J f▸J)).elim}};by_cases h3:(af 14 D y).card<=2
 · obtain⟨Dy,-,j,h4⟩:=sF h N b d (fun e:y=iy=>hy (e▸d)) (aI b d g2) h3
   have h5:Dy∈af 14 D y:=by rw[j];simp
   have hb:am e=Dy:=by{rw[j,_mi,_ms] at m;exact m.resolve_left (fun r=>hx (hf' iy d r▸d))};refine⟨e,hB (fun c hc'=>?_),fun i J hei=>hy (hf i J hei▸J),fun s A=>hb▸h4 s A,hb▸h5,ix,l,I⟩;rw[j,_mi,_ms] at hc';rcases hc' with f|f;exacts [Or.inr ⟨iy,d,f⟩,Or.inl (f.trans hb.symm)]
 · exfalso
   obtain⟨K,L⟩:=g y (by omega);have j:=aS K L m z (fun r=>eh h.1 T (r▸B)) (fun r=>eh h.1 T (r▸C)) (v y);have hy1:pos iy=P\/pos iy=Q:=by{rcases j _ (aI b d g2) with f|f|f;exacts [Or.inl f,Or.inr f,(hx (hf' iy d f.symm▸d)).elim]};have n:pos ix≠pos iy:=fun r=>g0 (b.2 ix l iy d r);have q:∀ X,X=P\/X=Q->∃ i∈aa 14 D,X=pos i:=by
    intro X hX;rcases hX with rfl|rfl <;> rcases I with f|f <;> rcases hy1 with M|M <;>
     first
      | exact⟨ix,l,f.symm⟩
      | exact⟨iy,d,M.symm⟩
      | exact(n (f.trans M.symm)).elim
   rcases hB (fun c hc'=>(j c hc').elim (fun f=>Or.inr (q c (Or.inl f))) (fun f=>f.elim (fun M=>Or.inr (q c (Or.inr M))) Or.inl)) with rfl|rfl;exacts [eh h.1 K m,eh h.1 L m]
lemma sm {D:Dag} {pos:O->ℕ×_d} {P Q:ℕ×_d} {y1 y2:O} (a:y1≠y2) (m:no D pos P Q y1) (n:no D pos P Q y2):False:=by
 obtain⟨e1,b,c,d,-,i,l,e⟩:=m;obtain⟨e2,f,g,-,h,-⟩:=n;have p:=c i l;have q:=g i l;have j:e2=e1:=by
  rcases b with rfl|rfl <;> rcases f with rfl|rfl <;> rcases e with k|k <;>
   first
    | rfl
    | exact absurd k.symm p
    | exact absurd k.symm q
 exact d y2 (Ne.symm a) (j▸h)
lemma mS {D:Dag} (h:ai 14 D) (d:aq D) (g:ap 14 D<=13) (c:aa 14 D={0,9}):False:=by
 have i:=aV 14 D;rw[c,show({0,9}:o).card=2 from rfl] at i;obtain⟨pos,P,Q,f⟩:=oq h d g (by rw[c];decide) (by omega);have j:3<=(af 14 D 1).card\/3<=(af 14 D 7).card:=by{by_contra l;exact dk h d f.1 1 7 13 9 0 (by rw[c];decide) V (by omega) (by omega)};have k:3<=(af 14 D 6).card\/3<=(af 14 D 8).card:=by{by_contra l;exact dk h d f.1 6 8 11 9 0 (by rw[c];decide) V (by omega) (by omega)};have m:no D pos P Q 7\/no D pos P Q 1:=by{rcases j with e|e;{exact Or.inl (lD h d f 1 7 5 3 9 0 6 8 (by rw[c];decide) V e k)};{exact Or.inr (lD h d f 7 1 10 13 0 9 6 8 (by rw[c];decide) V e k)}};have n:no D pos P Q 8\/no D pos P Q 6:=by{rcases k with e|e;{exact Or.inl (lD h d f 6 8 5 2 9 0 1 7 (by rw[c];decide) V e j)};{exact Or.inr (lD h d f 8 6 10 11 0 9 1 7 (by rw[c];decide) V e j)}};rcases m with a|a <;> rcases n with b|b <;> exact sm V a b
abbrev np:o:={8,9,10,11,12,13}
lemma rz {I:o} (a:I={0,1,3}):(∀ i∈I,ab i 7=true)/\(∀ t,t∉I->ab 7 t=false) /\(∀ l∈np,l∉I/\l≠7/\(∃ i∈I,ab i l=true) /\∃ z,ab l z=true/\z∉I) /\(∀ t,t∉I->t≠7->∀ i∈I,∃ q,ab i q=true/\q≠7 /\ab q t=false)/\I.card=3:=by
 subst a;refine⟨?_,?_,?_,?_,?_⟩<;> decide +kernel
abbrev kr (D:Dag) (pos:O->ℕ×_d):Finset (ℕ×_d):=(aa 14 D).image pos
def qg (D:Dag) (b:O->ℕ) (u:Σ _:ℕ,ℕ):Prop:=∀ x:O,x≠7->(af 14 D x).card<=3/\(3<=(af 14 D x).card ->aW 14 D (ao 14 D {x})=∅/\x∈ag 14 D u.1 /\∀ v∈aj 14 D b,x∈ag 14 D v.1->v=u)
def oO (D:Dag) (l:O):Prop:=∃ Q:ℕ×_d,am Q∈af 14 D l/\(∀ t,am Q∈af 14 D t->t=l) /\∀ z,aO l z->z∈al 14 D->Q∈af 14 D z
def mf (D:Dag) (pos:O->ℕ×_d) (l:O):Prop:=∃ F G,F∈af 14 D l/\G∈af 14 D l/\F≠G/\F∉kr D pos /\G∉kr D pos
lemma pt {D:Dag} {pos:O->ℕ×_d} (a:bA 14 md D pos) {y:O} (c:y∈al 14 D) {e:ℕ×_d} (d:am e∈af 14 D y):e∉kr D pos:=by
 intro f;obtain⟨i,b,rfl⟩:=_mg.1 f;have:=ei a b d;subst this;exact aN.1 b c
lemma qh {D:Dag} (h:ai 14 D) (C:aq D) (G:aa 14 D={0,1,3}) {pos:O->ℕ×_d} (a:bA 14 md D pos) {l z0:O} (q:l≠7) (r:aO l z0) (d:z0∈al 14 D) (s:¬ mf D pos l):oO D l:=by
 have E:=rz G;have u:=aK;have v:=aC C;obtain⟨e,w,x,-⟩:=cg u h.1 v r;have b:∀ f∈af 14 D l,f=e\/f∈kr D pos:=by{intro f g;by_contra c;rw[not_or] at c;exact s ⟨e,f,w,g,fun y=>c.1 y.symm,pt a d x,c.2⟩};refine⟨am e,by rw[aB];exact w,fun t j=>?_,fun z H A=>?_⟩
 · rw[aB] at j
   have j:=(ak.1 j).2.1;by_contra k;by_cases m:t∈aa 14 D
   · have hl':=(ak.1 w).2.1
     rw[jh u h.1 v m j,_ms] at hl';exact k hl'.symm
   · obtain⟨f,g,I,j'⟩:=bR h C q (Ne.symm k) (aG.1 (E.2.1 t m))
     rcases b f g with rfl|c;{exact j' j}
     · obtain⟨i,F,rfl⟩:=_mg.1 c
       exact I ((a.1 i F).2.2.1 7 ((ad _ _).1 (E.1 i F)))
 · obtain⟨f,g,p,-⟩:=cg u h.1 v H
   rcases b f g with rfl|c;{exact p};{exact absurd c (pt a A p)}
lemma qi {D:Dag} (h:ai 14 D) (hD:aq D) (hI:aa 14 D={0,1,3}) (b:O->ℕ) (hb:aM 14 D b) {pos:O->ℕ×_d} (a:bA 14 md D pos) {u2:Σ _:ℕ,ℕ} (M:qg D b u2) {l t i j:O} (q:l≠7) (v:t≠7) (w:l≠t) (N:t∉aa 14 D) (P:l∈al 14 D) (r:i∈aa 14 D) (hj:j∈aa 14 D) (Q:aO i l) (R:aO j t) (S:mf D pos l) (T:mf D pos t):i=j:=by
 classical
 have hg:=rz hI;have y:∀ {x k:O},x≠7->k∈aa 14 D->aO k x->mf D pos x ->3<=(af 14 D x).card/\∃ F G,F∉kr D pos/\G∉kr D pos /\af 14 D x={pos k,F,G}:=by
  intro x k U hk W ⟨F,G,hF,hG,z,f,g⟩;have hk':pos k∈kr D pos:=mem_image_of_mem pos hk;have hn:pos k∉({F,G}:Finset (ℕ×_d)):=by{simp only[_mi,_ms,not_or];exact⟨fun c=>f (c▸hk'),fun c=>g (c▸hk')⟩};have p:({pos k,F,G}:Finset (ℕ×_d))⊆af 14 D x:=by{intro e c;simp only[_mi,_ms] at c;rcases c with rfl|rfl|rfl;{exact aI a hk W};{exact hF};{exact hG}};have L:=_cl p;rw[_cin hn,_c2 z] at L
  exact⟨L,F,G,f,g,(_eqc p (by
   rw[_cin hn,_c2 z];exact(M x U).1)).symm⟩
 obtain⟨X,F,G,f,g,m⟩:=y q r Q S;obtain⟨N',F',G',f',g',Y⟩:=y v hj R T;obtain⟨-,Z,H⟩:=(M l q).2 X;have I:=((M t v).2 N').2.1;obtain⟨e0,s⟩:=jx aK h (aC hD) b hb w P (fun u hu Z'=>by rw[H u hu Z'];exact I) ⟨Z,I⟩;have r':pos i∈kr D pos:=mem_image_of_mem pos r;by_cases hp:pos i=e0
 · exfalso
   have L:=s F (by rw[m];simp) (fun c=>f (by rw[c,<-hp];exact r'));have d:=s G (by rw[m];simp) (fun c=>g (by rw[c,<-hp];exact r'));obtain⟨e,c,h7,ht'⟩:=bR h hD q w (aG.1 (hg.2.1 t N));rw[m] at c;simp only[_mi,_ms] at c;rcases c with rfl|rfl|rfl;{exact h7 ((a.1 i r).2.2.1 7 ((ad _ _).1 (hg.1 i r)))};{exact ht' L};{exact ht' d}
 · have d:pos i∈af 14 D t:=ak.2 ⟨(a.1 i r).1,s (pos i) (by rw[m];simp) hp,by
    rw[(a.1 i r).2.1];exact notMem_empty t⟩
   rw[Y] at d;simp only[_mi,_ms] at d;rcases d with d|d|d;{exact a.2 i r j hj d};{exact absurd (d▸r') f'};{exact absurd (d▸r') g'}
def di (l:_F (O)) (k:Fin 4):O:=l.getD k.val 0
abbrev rA (zl ll:_F (O)):Prop:=(∀ k:Fin 4,ab (di ll k) (di zl k)=true /\ab (di ll k) (di zl (k+1))=true/\di zl k≠7 /\di zl k∉({0,1,3}:o)) /\∀ k m:Fin 4,k≠m->di zl k≠di zl m /\ab (di zl k) (di zl m)=false/\di ll k≠di ll m
lemma sn {D:Dag} (h:ai 14 D) (C:aq D) (X:aa 14 D={0,1,3}) (b:O->ℕ) (E:cU 14 D b) {U:Σ _:ℕ,ℕ} (F:U∈aj 14 D b) (W:qg D b U) (zl ll:_F (O)) (G:rA zl ll) (H:∀ k:Fin 4,oO D (di ll k)):False:=by
 classical
 obtain⟨g,i⟩:=G;choose Q I J r using H;have u:∀ k:Fin 4,k - 1≠k/\k+1≠k/\k+1≠k - 1/\k - 1+1=k:=V;have v:∀ k,di zl k∈al 14 D:=fun k=>not_not.1 (fun q=>(g k).2.2.2 (X▸aN.2 q));have j:∀ k,Q k∈af 14 D (di zl k):=fun k=>r k _ ((ad _ _).1 (g k).1) (v k);have l:∀ k,Q k∈af 14 D (di zl (k+1)):=fun k=>r k _ ((ad _ _).1 (g k).2.1) (v _);have B:∀ k m:Fin 4,k≠m->Q k≠Q m:=fun k m K f=>(i k m K).2.2 (J m _ (by rw[<- f];exact I k));have n:∀ k,di zl k≠di zl (k+1):=fun k=>(i _ _ (Ne.symm (u k).2.1)).1;have Y:∀ k,3<=(af 14 D (di zl k)).card:=by
  intro k;by_contra q;have L:Q (k - 1)∈af 14 D (di zl k):=by{have:=l (k - 1);rwa[(u k).2.2.2] at this}
  have M:=_eqc (s:=({Q k,Q (k - 1)}:Finset (ℕ×_d))) (t:=af 14 D (di zl k)) (fun e f=>by
   rcases _mi.1 f with rfl|f;{exact j k}
   · rw[_ms.1 f];exact L)
   (by rw[_c2 (B _ _ (Ne.symm (u k).1))];omega)
  obtain⟨e,f,N,hb'⟩:=bR h C (n k) (i k (k - 1) (Ne.symm (u k).1)).1 (aG.1 (i _ _ (u k).2.2.1).2.1);rw[<- M] at f;rcases _mi.1 f with rfl|f;{exact N (ak.1 (l k)).2.1}
  · rw[_ms.1 f] at hb'
    exact hb' (ak.1 (j (k - 1))).2.1
 obtain⟨P,R,S,y⟩:=pi aK h (aC C) b E F (univ.image (di zl)) ⟨_,mem_image_of_mem _ (_mv 0)⟩ (fun x W'=>by
  obtain⟨k,-,rfl⟩:=_mg.1 W'
  exact(W _ (g k).2.2.1).2 (Y k))
 have z:∀ k,P∈af 14 D (di zl k)/\R∈af 14 D (di zl k):=fun k=>y _ (mem_image_of_mem _ (_mv k));have p:∀ k,Q k=P\/Q k=R:=by
  intro k;by_contra q;rw[not_or] at q;have Z:P∉({R,Q k}:Finset (ℕ×_d)):=by{simp only[_mi,_ms,not_or];exact⟨fun f=>S (f▸rfl),Ne.symm q.1⟩};have A:∀ m,Q k∈af 14 D (di zl m) ->({P,R,Q k}:Finset (ℕ×_d))=af 14 D (di zl m):=fun m hm=>
   _eqc (fun e f=>by
    simp only[_mi,_ms] at f;rcases f with rfl|rfl|rfl;{exact(z m).1};{exact(z m).2}
    · exact hm) (by
    rw[_cin Z,_c2 (Ne.symm q.2)]
    exact(W _ (g m).2.2.1).1)
  obtain⟨e,f,N,-⟩:=bR h C (n k) (n k) (dv _);rw[<- A k (j k),A (k+1) (l k)] at f;exact N (ak.1 f).2.1
 rcases p 0 with a|a <;> rcases p 1 with c|c <;> rcases p 2 with d|d <;>
  first
  | exact B 0 1 V (a.trans c.symm)
  | exact B 0 2 V (a.trans d.symm)
  | exact B 1 2 V (c.trans d.symm)
lemma nq {D:Dag} (h:ai 14 D) (E:aq D) (h13:ap 14 D<=13) (F:aa 14 D={0,1,3}):False:=by
 classical
 have hG:=aK;have hC:=aC E;obtain⟨b,U⟩:=b_ hG h.1 hC;have T:=bD U;obtain⟨pos,J⟩:=bQ hG h hC;have a:bA 14 md D pos:=J;obtain⟨g1,-,g3,g4,g5⟩:=rz F;have A:∀ x:O,x∉aa 14 D->x∈al 14 D:=fun x y=>not_not.1 (mt aN.2 y);have K:(7:O)∈al 14 D:=A 7 (by rw[F];decide);have hY:∀ i∈aa 14 D,pos i∈af 14 D 7:=fun i c=>aI a c ((ad _ _).1 (g1 i c));have n:kr D pos⊆af 14 D 7:=fun e m=>by{obtain⟨i,c,rfl⟩:=_mg.1 m;exact hY i c};have W:(kr D pos).card=3:=(_cij (fun _ c _ hj=>a.2 _ c _ hj)).trans g5;have hW7:=_cl n;rw[W] at hW7;have hcc7:=me h E b T K;have hres:=bS h.1 b T;have hp:=aV 14 D;rw[g5] at hp;have hBt:=dC 14 D;by_cases G:∀ u∈aj 14 D b,(7:O)∈ag 14 D u.1
 · have:=oM h E b T om K np (fun x y=>by
    obtain⟨hx3,hx7,⟨i,c,hix⟩,-⟩:=g3 x y
    exact⟨A x hx3,hx7,fun u d _=>G u d,aw D (pos i),(a.1 i c).2.2.1 x ((ad _ _).1 hix),(a.1 i c).2.2.1 7 ((ad _ _).1 (g1 i c))⟩)
   rw[show np.card=6 from rfl] at this;omega
 · obtain⟨u2,d⟩:=not_forall.1 G
   obtain⟨L,H⟩:=Classical.not_imp.1 d;have p:aY D b 7⊆(aj 14 D b).erase u2:=fun u d=>
    _me.2 ⟨fun m=>H (m▸(ax.1 d).2),(ax.1 d).1⟩
   have hle:=_cl p;rw[card_erase_of_mem L] at hle;obtain⟨u1,hu1⟩:=_c1.1 (show(aY D b 7).card=1 by omega);have I:u1∈aY D b 7:=by rw[hu1];exact _mss _
   obtain⟨X,Y⟩:=ax.1 I;have r:∀ u∈aj 14 D b,u≠u2->u=u1:=fun u d g=>
    card_le_one.1 (by rw[card_erase_of_mem L];omega) u (_me.2 ⟨g,d⟩) u1 (p I)
   have M:kr D pos=af 14 D 7:=
    _eqc n (by rw[W];omega)
   have N:∀ t,t∈ag 14 D u1.1->t=7:=by
    intro t ht;by_contra s
    obtain⟨e0,Z⟩:=jx hG h hC b T (Ne.symm s) K (fun u d hu7=>by
     rw[r u d (fun m=>H (m▸hu7))];exact ht) ⟨Y,ht⟩
    have hex:∃ i3∈aa 14 D,∀ i∈aa 14 D,i≠i3 ->t∈ag 14 D (aw D (pos i)):=by
     by_cases hc:∃ i3∈aa 14 D,pos i3=e0
     · obtain⟨i3,B,m⟩:=hc
       exact⟨i3,B,fun i c g=>Z _ (hY i c) (fun hh=>
        g (a.2 i c i3 B (hh.trans m.symm)))⟩
     · exact⟨0,by rw[F];decide,fun i c _=>Z _ (hY i c) (fun hh=>hc ⟨i,c,hh⟩)⟩
    obtain⟨i3,B,h0⟩:=hex;obtain⟨q,hq1,hq7,hq2⟩:=g4 t (fun hc=>aN.1 hc (fB X ht)) s i3 B;obtain⟨e,m,h1,h2⟩:=bR h E (Ne.symm s) (Ne.symm hq7) (fun h4=>aG.1 hq2 (bl h4));rw[<- M] at m;obtain⟨i,c,rfl⟩:=_mg.1 m;by_cases h5:i=i3
    · subst h5
      exact h2 ((a.1 i c).2.2.1 q ((ad _ _).1 hq1))
    · exact h1 (h0 i c h5)
   have C:∀ x:O,x≠7->∀ u∈aY D b x,u=u2:=by{intro x y u d;by_contra g;obtain⟨hur,h6⟩:=ax.1 d;rw[r u hur g] at h6;exact y (N x h6)};have h7:qg D b u2:=by{intro x y;have h1:=bi h E b T x;have h2:(aY D b x).card<=1:=card_le_one.2 (fun u d v hv=>(C x y u d).trans (C x y v hv).symm);refine⟨by omega,fun h3=>?_⟩;obtain⟨u,d⟩:=_cp.1 (show 0<(aY D b x).card by omega);exact⟨card_eq_zero.1 (by omega),C x y u d▸(ax.1 d).2,fun v hv hxv=>C x y v (ax.2 ⟨hv,hxv⟩)⟩};have hO:∀ l∈np,¬ mf D pos l->oO D l:=fun l P hnd=>by{obtain⟨-,Q,-,z,hz,hz3⟩:=g3 l P;exact qh h E F a Q ((ad _ _).1 hz) (A z hz3) hnd};have f:∃ i0∈aa 14 D,∀ l∈np,ab i0 l=false->oO D l:=by
    by_cases hd:∃ l0∈np,mf D pos l0
    · obtain⟨l0,hl0,hd0⟩:=hd
      obtain⟨hl3,Q,⟨i0,f,w⟩,-⟩:=g3 l0 hl0;refine⟨i0,f,fun l P R=>hO l P (fun S=>?_)⟩;obtain⟨ht3,s,⟨j,hj,h8⟩,-⟩:=g3 l P;have g:l0≠l:=fun m=>by{rw[m,R] at w;exact _fnt w};rw[qi h E F b T a h7 Q s g ht3 (A l0 hl3) f hj ((ad _ _).1 w) ((ad _ _).1 h8) hd0 S,h8] at R;exact Bool.noConfusion R
    · exact⟨0,by rw[F];decide,fun l P _=>hO l P (fun S=>hd ⟨l,P,S⟩)⟩
   obtain⟨i0,f,hsg⟩:=f;have fin:∀ zl ll:_F (O),rA zl ll ->(∀ k:Fin 4,di ll k∈np/\ab i0 (di ll k)=false)->False:=fun zl ll hcg hk=>
    sn h E F b U L h7 zl ll hcg (fun k=>hsg _ (hk k).1 (hk k).2)
   rw[F] at f;simp only[_mi,_ms] at f;rcases f with rfl|rfl|rfl;{exact fin [5,6,4,2] [9,11,13,12] (by decide +kernel) (by decide +kernel)};{exact fin [2,6,4,5] [8,11,10,12] (by decide +kernel) (by decide +kernel)};{exact fin [2,6,5,4] [8,9,10,13] (by decide +kernel) (by decide +kernel)}
lemma gL {α:Type} [DecidableEq α] {S:Finset α} {a b c:α} (k:a∈S) (l:b∈S) (m:c∈S) (f:a≠b) (g:a≠c) (h:b≠c):3<=S.card/\(S.card<=3->∀ e∈S,e=a\/e=b\/e=c):=by
 have d:({a,b,c}:Finset α)⊆S:=by{simp[insert_subset_iff,k,l,m]};have i:({a,b,c}:Finset α).card=3:=by{rw[_cin (by simp[f,g]),_c2 h]};refine⟨i▸_cl d,fun n e j=>?_⟩;rw[<- _eqc d (i▸n)] at j;simpa using j
lemma sJ:∀ j∈({0,1}:o),∀ t:O,t≠j ->∃ q,ab j q=true/\q≠7/\ab t q=false:=by decide +kernel
lemma oP:∀ t:O,aO 0 t->aO 1 t->t=7:=by decide +kernel
lemma so:∀ l:O,aO 1 l->¬ aO 7 l:=by decide +kernel
lemma sp (d la lb:O) (a:(d=4/\la=10/\lb=13)\/(d=6/\la=8/\lb=9)):(d∉({0,1,11}:o)/\la∉({0,1,11}:o) /\lb∉({0,1,11}:o)) /\(aO 11 d/\aO d la/\aO d lb/\aO 0 la/\aO 1 lb) /\(la≠7/\lb≠7/\d≠7/\la≠d/\lb≠d)/\¬ aO 0 d/\¬ aO 1 d:=by
 rcases a with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩<;>
  exact⟨by decide,⟨by decide,by decide,by decide,by decide,V⟩,by decide,by decide,V⟩
lemma mT {D:Dag} (h:ai 14 D) (hD:aq D) (h13:ap 14 D<=13) (hI:aa 14 D={0,1,11}):False:=by
 classical
 have hG:=aK;have hC:=aC hD;obtain⟨b,hbm⟩:=b_ hG h.1 hC;have hb:=bD hbm;obtain⟨pos,f⟩:=bQ hG h hC;have hin:∀ i∈({0,1,11}:o),i∈aa 14 D:=by{rw[hI];exact fun _ B=>B};have C:=hin 0 (by decide);have F:=hin 1 (by decide);have m:=hin 11 (by decide);have n:∀ x:O,x∉({0,1,11}:o)->x∈al 14 D:=by{intro x E;by_contra k;exact E (hI▸aN.2 k)};have hne:∀ x∈al 14 D,∀ i∈aa 14 D,x≠i:=fun x E i B hxi=>aN.1 B (hxi▸E);have z:∀ x y:O,aO x y->x∈al 14 D->y∈al 14 D ->∃ e∈af 14 D x,am e∈af 14 D y /\(∀ i∈aa 14 D,e≠pos i/\am e≠pos i) /\x∉ag 14 D (aw D (am e)):=by{intro x y hxy E hy;obtain⟨e,K,heb,-,hs,-⟩:=cg hG h.1 hC hxy;exact⟨e,K,heb,fun i B=>⟨fun k=>hne y hy i B (ei f B (k▸heb)),fun k=>hne x E i B (ei f B (by rw[<- k,aB];exact K))⟩,hs⟩};have k0:=(f.1 0 C).2.2.1;have k1:=(f.1 1 F).2.2.1;have e7:=n 7 (by decide);have e3:=n 3 (by decide);obtain⟨H,hH7,hH3,hHf,-⟩:=z 7 3 (by decide) e7 e3;have a07:=aI f C (a:=7) (by decide);have a17:=aI f F (a:=7) (by decide);have p01:pos 0≠pos 1:=fun k=>absurd (f.2 0 C 1 F k) (by decide);obtain⟨t71,t72⟩:=gL a07 a17 hH7 p01 (hHf 0 C).1.symm (hHf 1 F).1.symm;have c7:=me h hD b hb e7;have hr:=bS h.1 b hb;have hp:=aV 14 D;rw[hI,show({0,1,11}:o).card=3 from rfl] at hp;have hsplit:=bg 14 D;have hr7:(aY D b 7).card<=(aj 14 D b).card:=_cfl _ _;have lw:∀(u:Σ _:ℕ,ℕ) (x:O),(∀ v∈aj 14 D b,x∈ag 14 D v.1->v=u) ->(af 14 D x).card+(aW 14 D (ao 14 D {x})).card<=3 /\(x∉ag 14 D u.1->(af 14 D x).card<=2):=by
  intro u x A;have q1:=bi h hD b hb x
  have q2:(aY D b x).card<=1:=card_le_one.2 (fun a ha c k=>
   (A a (ax.1 ha).1 (ax.1 ha).2).trans (A c (ax.1 k).1 (ax.1 k).2).symm)
  refine⟨by omega,fun hn=>?_⟩;have:(aY D b x).card=0:=card_eq_zero.2 (filter_eq_empty_iff.2 (fun v hv hxv=>hn (A v hv hxv▸hxv)));omega
 have nB:(aY D b 7).card≠2:=by
  intro hk;have R:∀ u∈aj 14 D b,7∈ag 14 D u.1:=by
   have hE:aY D b 7=aj 14 D b:=
    _eqc (_fs _ _) (by omega)
   intro u A;rw[<- hE] at A;exact(ax.1 A).2
  have hy:∃ y:O,(y=3\/y=12) /\∃ w,y∈ag 14 D w/\7∈ag 14 D w:=by
   by_cases h3:∃ u∈aj 14 D b,3∈ag 14 D u.1
   · obtain⟨u,A,h3u⟩:=h3
     exact⟨3,Or.inl rfl,u.1,h3u,R u A⟩
   · have hr3:(aY D b 3).card=0:=card_eq_zero.2 (filter_eq_empty_iff.2 (fun u A h3u=>h3 ⟨u,A,h3u⟩))
     have:=bi h hD b hb 3;obtain⟨Z,-,hZ,-⟩:=sF h hD f m (by decide) (aI f m (a:=3) (by decide)) (by omega);obtain⟨g,hg,hgb,hgf,-⟩:=z 3 12 (by decide) e3 (n 12 (by decide));rw[hZ,_mi,_ms] at hg hH3;rw[hg.resolve_left (hgf 11 m).1,<-hH3.resolve_left (hHf 11 m).2,aB] at hgb;exact⟨12,Or.inr rfl,_,(ak.1 hgb).2.1,(ak.1 hH7).2.1⟩
  obtain⟨y,hy1,w,hyw,h7w⟩:=hy;have hX:∀ x∈({8,10,9,13,y}:o),x∈al 14 D/\x≠7 /\(∀ u∈aj 14 D b,x∈ag 14 D u.1->7∈ag 14 D u.1) /\∃ w,x∈ag 14 D w/\7∈ag 14 D w:=by
   intro x E;simp only[_mi,_ms] at E;rcases E with rfl|rfl|rfl|rfl|rfl;iterate 2 exact⟨n _ (by decide),by decide,fun u A _=>R u A,_,k0 _ (by decide),k0 7 (by decide)⟩
   iterate 2 exact⟨n _ (by decide),by decide,fun u A _=>R u A,_,k1 _ (by decide),k1 7 (by decide)⟩
   rcases hy1 with rfl|rfl <;>
    exact⟨n _ (by decide),by decide,fun u A _=>R u A,w,hyw,h7w⟩
  have hc5:({8,10,9,13,y}:o).card=5:=by{rcases hy1 with rfl|rfl <;> rfl};have:=oM h hD b hb om e7 _ hX;rw[hc5] at this;omega
 obtain⟨u1,hu1⟩:=_cp.1 (show 0<(aY D b 7).card by omega);obtain⟨hu1r,h7u1⟩:=ax.1 hu1;have huniq:∀ v∈aj 14 D b,7∈ag 14 D v.1->v=u1:=fun v hv h7v=>
  card_le_one.1 (show(aY D b 7).card<=1 by omega) v (ax.2 ⟨hv,h7v⟩) u1 hu1
 have hW7:=t72 (by omega);have hW7':=fun e K=>or_left_comm.1 (hW7 e K);have M:∀ t,t∈ag 14 D u1.1->t≠7 ->t∈ag 14 D (aw D (pos 0))/\t∈ag 14 D (aw D (pos 1)):=by
  intro t ht ht7;have hte:=fB hu1r ht;obtain⟨X,r⟩:=jx hG h hC b hb (Ne.symm ht7) e7 (fun v hv h7v=>by rw[huniq v hv h7v];exact ht) ⟨h7u1,ht⟩;have mk:∀ i j:O,j∈aa 14 D->j∈({0,1}:o) ->(∀ e∈af 14 D 7,e=pos i\/e=pos j\/e=H) ->t∈ag 14 D (aw D (pos i))->t∈ag 14 D (aw D H)->False:=by{intro i j hj hj01 hW hti htH;obtain⟨q,hq1,hq7,hq2⟩:=sJ j hj01 t (hne t hte j hj);obtain⟨e,K,n1,n2⟩:=bR h hD (x:=7) (Ne.symm ht7) (Ne.symm hq7) (aG.1 hq2);rcases hW e K with rfl|rfl|rfl;{exact n1 hti};{exact n2 ((f.1 j hj).2.2.1 q ((ad _ _).1 hq1))};{exact n1 htH}};by_cases c0:pos 0=X;{exact(mk 1 0 C (by decide) hW7' (r _ a17 (fun k=>p01 (c0.trans k.symm))) (r _ hH7 (fun k=>(hHf 0 C).1 (k.trans c0.symm)))).elim}
  · have a0:=r _ a07 c0
    by_cases c1:pos 1=X;{exact(mk 0 1 F (by decide) hW7 a0 (r _ hH7 (fun k=>(hHf 1 F).1 (k.trans c1.symm)))).elim};{exact⟨a0,r _ a17 c1⟩}
 have nR:(aj 14 D b).card≠1:=by
  intro hR;have L:=fun x=>lw u1 x (fun v hv _=>card_le_one.1 hR.le v hv u1 hu1r)
  have asg:∀ i∈aa 14 D,∀ t,t∈ag 14 D (aw D (pos i)) ->pos i∈af 14 D t:=fun i B t ht=>ak.2 ⟨(f.1 i B).1,ht,by
   rw[(f.1 i B).2.1];exact notMem_empty t⟩
  have e4:=n 4 (by decide);have a4:=aI f m (a:=4) (by decide);have a10:=aI f C (a:=10) (by decide);obtain⟨G,N,I,s,-⟩:=z 4 10 (by decide) e4 (n 10 (by decide));obtain⟨S,T,J,hf2,-⟩:=z 4 13 (by decide) e4 (n 13 (by decide));have n4:4∉ag 14 D u1.1:=by{intro h4;obtain⟨q0,q1⟩:=M 4 h4 (by decide);rcases (gL (asg 0 C 4 q0) (asg 1 F 4 q1) N p01 (s 0 C).1.symm (s 1 F).1.symm).2 (by have:=(L 4).1;omega) _ a4 with k|k|k;{exact absurd (f.2 11 m 0 C k) (by decide)};{exact absurd (f.2 11 m 1 F k) (by decide)};{exact(s 11 m).1 k.symm}};have U:G=S:=by{by_contra k;have:=(gL a4 N T (s 11 m).1.symm (hf2 11 m).1.symm k).1;have:=(L 4).2 n4;omega};rw[<- U] at J;obtain⟨e,K,n7,n13⟩:=bR h hD (x:=10) (a:=7) (b:=13) (by decide) (by decide) (by decide);have d1:am G≠e:=fun k=>n13 (k▸(ak.1 J).2.1);have d2:pos 0≠e:=fun k=>n7 (k▸k0 7 (by decide));by_cases h10:10∈ag 14 D u1.1
  · rcases (gL I a10 (asg 1 F 10 (M 10 h10 (by decide)).2) (s 0 C).2 (s 1 F).2 p01).2 (by have:=(L 10).1;omega) e K with k|k|k
    · exact d1 k.symm
    · exact d2 k.symm
    · exact n7 (k▸k1 7 (by decide))
  · have:=(gL I a10 K (s 0 C).2 d1 d2).1
    have:=(L 10).2 h10;omega
 have hB0:bL 14 D=0:=by omega
 have fl:∀ i j:O,i∈aa 14 D->j∈aa 14 D->i≠j->i≠3 ->aO i 7->(∀ e∈af 14 D 7,e=pos i\/e=pos j\/e=H) ->∀ t,t∈ag 14 D (aw D (pos i))->aO i t:=by{intro i j B hj hij hi3 hi7 hW t;refine(rx h hD hB0 f B hi7 (fun p hp hp1 hsub=>?_) t).1;rcases hW p hp with rfl|rfl|rfl;{exact hp1 rfl};{exact hij (singleton_subset_singleton.1 ((f.1 j hj).2.2.2.symm.subset.trans hsub)).symm};{exact hi3 (_ms.1 (hsub (ak.1 hH3).2.1)).symm}};have f0:=fl 0 1 C F (by decide) (by decide) (by decide) hW7;have f1:=fl 1 0 F C (by decide) (by decide) (by decide) hW7';have hpure:∀ t,t∈ag 14 D u1.1->t=7:=by{intro t ht;by_contra ht7;obtain⟨q0,q1⟩:=M t ht ht7;exact ht7 (oP t (f0 t q0) (f1 t q1))};have hc2:((aj 14 D b).erase u1).card=1:=by{rw[card_erase_of_mem hu1r];omega};obtain⟨u2,hu2⟩:=_cp.1 (hc2▸Nat.one_pos);have hu2r:=mem_of_mem_erase hu2;have only2:∀ x:O,x≠7->∀ u∈aj 14 D b,x∈ag 14 D u.1 ->u=u2:=fun x E u A hxu=>card_le_one.1 hc2.le u (_me.2 ⟨fun k=>E (hpure x (k▸hxu)),A⟩) u2 hu2;have L:=fun x E=>lw u2 x (only2 x E);have ct:∀ x y:O,x≠7->x≠y->x∈ag 14 D u2.1->y∈ag 14 D u2.1 ->∃ X,∀ e∈af 14 D x,e≠X->y∈ag 14 D (aw D e):=fun x y E hxy hxu hyu=>jx hG h hC b hb hxy (fB hu2r hxu) (fun u A hxu'=>by rw[only2 x E u A hxu'];exact hyu) ⟨hxu,hyu⟩;have low:∀ i l:O,i∈aa 14 D->aO i l->l≠7->l∉ag 14 D u2.1 ->∀ P∈af 14 D l,P≠pos i->∀ t,t≠l->P∉af 14 D t:=by{intro i l B W hl7 hn P hP hPi;obtain⟨Z,-,hZ,hZp⟩:=sF h hD f B (fun E=>dv i (by rw[E] at W;exact W)) (aI f B W) ((L l hl7).2 hn);rw[hZ,_mi,_ms] at hP;rw[hP.resolve_left hPi];exact hZp};have Q:∀ l1 Y:O,aO 0 l1->aO 1 Y->l1≠7->Y≠7->∀ P:ℕ×_d,P∈af 14 D l1->P∈af 14 D Y->P≠pos 0->P≠pos 1->False:=by{intro l1 Y a1 a2 n1 n2 P hP1 hP2 hP0 hP1';have hl:l1≠Y:=fun k=>n1 (oP l1 a1 (k▸a2));obtain⟨X,r⟩:=ct l1 Y n1 hl (by by_contra hn;exact low 0 l1 C a1 n1 hn P hP1 hP0 Y (Ne.symm hl) hP2) (by by_contra hn;exact low 1 Y F a2 n2 hn P hP2 hP1' l1 hl hP1);have h00:pos 0=X:=by{by_contra k;exact n2 (oP Y (f0 Y (r _ (aI f C a1) k)) a2)};obtain⟨e,K,n7,nl⟩:=bR h hD (x:=l1) (a:=7) (b:=Y) n1 hl (so Y a2);by_cases k:e=X;{exact n7 (by rw[k,<-h00];exact k0 7 (by decide))};{exact nl (r e K k)}};have claim:∀ d la lb:O,(d=4/\la=10/\lb=13)\/(d=6/\la=8/\lb=9) ->∃ G S,(∀ e∈af 14 D d,e=pos 11\/e=G\/e=S)/\G∈af 14 D d /\S∈af 14 D d/\G≠pos 11/\S≠pos 11/\G≠S /\am G∈af 14 D la/\am S∈af 14 D lb /\(∀ t,t≠la->am G∉af 14 D t) /\(∀ t,t≠lb->am S∉af 14 D t) /\d∈ag 14 D u2.1/\aW 14 D (ao 14 D {d})=∅:=by
  intro d la lb hcase;obtain⟨⟨g1,g2,g3⟩,⟨g4,g5,g6,g7,g8⟩,⟨n1,n2,n3,n4,n5⟩,g9,g10⟩:=sp d la lb hcase;obtain⟨G,N,I,s,hs1⟩:=z d la g5 (n d g1) (n la g2);obtain⟨S,T,J,hf2,hs2⟩:=z d lb g6 (n d g1) (n lb g3);have U:G≠S:=fun k=>
   Q la lb g7 g8 n1 n2 (am G) I (k▸J) (s 0 C).2 (s 1 F).2
  obtain⟨t31,t32⟩:=gL (aI f m g4) N T (s 11 m).1.symm (hf2 11 m).1.symm U;have q1:=(L d n3).1;have hdu:d∈ag 14 D u2.1:=by{by_contra hn;have:=(L d n3).2 hn;omega};have side:∀(i l:O) (e:ℕ×_d),i∈aa 14 D->aO i l->l≠7 ->l≠d->am e∈af 14 D l->am e≠pos i ->d∉ag 14 D (aw D (am e)) ->(∀ t,t∈ag 14 D (aw D (pos i))->aO i t)->¬ aO i d ->∀ t,t≠l->am e∉af 14 D t:=by{intro i l e B W hl7 hld hb' hf hs fi hid;refine low i l B W hl7 (fun hl=>?_) _ hb' hf;obtain⟨X,r⟩:=ct l d hl7 hld hl hdu;have E:am e=X:=by{by_contra k;exact hs (r _ hb' k)};exact hid (fi d (r _ (aI f B W) (fun k=>hf (E.trans k.symm))))};exact⟨G,S,t32 (by omega),N,T,(s 11 m).1,(hf2 11 m).1,U,I,J,side 0 la G C g7 n1 n4 I (s 0 C).2 hs1 f0 g9,side 1 lb S F g8 n2 n5 J (hf2 1 F).2 hs2 f1 g10,hdu,card_eq_zero.1 (by omega)⟩
 obtain⟨G,S,-,N,T,m1,m2,U,I,J,-,-,hu4,-⟩:=claim 4 10 13 (Or.inl ⟨rfl,rfl,rfl⟩);obtain⟨g1,g2,hW6,-,-,-,-,-,-,-,hp1,hp2,hu6,hM6⟩:=claim 6 8 9 (Or.inr ⟨rfl,rfl,rfl⟩);obtain⟨X,r⟩:=ct 4 6 (by decide) (by decide) hu4 hu6;have fin:∀(e:ℕ×_d) (l:O),e∈af 14 D 4->am e∈af 14 D l ->l≠8->l≠9->e≠pos 11->e≠X->False:=by{intro e l K hbar h8 h9 hne11 hne0;rcases hW6 e (gD h.1 hM6 (ak.1 K).1 (cY h.1 K) (r e K hne0)) with rfl|rfl|rfl;{exact hne11 rfl};{exact hp1 l h8 hbar};{exact hp2 l h9 hbar}};by_cases c:G=X;{exact fin S 13 T J (by decide) (by decide) m2 (fun k=>U (c.trans k.symm))};{exact fin G 10 N I (by decide) (by decide) m1 c}
lemma oQ:kK {7,8,13} {0,1,2}=true:=by decide +kernel
lemma sK:∀ i t x:O,ab i t=true->x≠t->x≠i ->∃ q,ab i q=true/\q≠t/\q≠x/\ab x q=false:=by decide +kernel
lemma qD {D:Dag} (h:ai 14 D) (d:aq D) (b:ap 14 D<=13) {I:o} (c:aa 14 D=I) (e:I.card=4) (a:({0,1,2}:o)⊆I):bL 14 D=0/\bd 14 D<=(al 14 D).card+3:=by
 have f:=aV 14 D;rw[c,e] at f;have j:=ry h d b (fun i g=>by rw[c];exact a g) (by omega);have k:=bg 14 D;omega
lemma rB {D:Dag} {b:O->ℕ} {u:Σ _:ℕ,ℕ} {x y z:O} (d:u∈aj 14 D b) (e:(ag 14 D u.1∩{x,y,z}).Nonempty):u∈aY D b x\/u∈aY D b y\/u∈aY D b z:=by
 obtain⟨a,c⟩:=e;rw[_mn,_mi,_mi,_ms] at c;rcases c.2 with rfl|rfl|rfl;{exact Or.inl (ax.2 ⟨d,c.1⟩)};{exact Or.inr (Or.inl (ax.2 ⟨d,c.1⟩))};{exact Or.inr (Or.inr (ax.2 ⟨d,c.1⟩))}
lemma nr {D:Dag} {pos:O->ℕ×_d} (h:ai 14 D) (s:aq D) (a:bA 14 md D pos) (w:bL 14 D=0) (Q:bd 14 D<=(al 14 D).card+3) (b:O->ℕ) (N:aM 14 D b) {T J:o} (x:kK T J=true) (y:J⊆aa 14 D) {t i j z:O} (R:t∈T/\i∈J/\j∈J/\i≠j/\ab i t=true/\ab j t=true /\ab t z=true/\z≠i/\z≠j):∃ F,am F∈af 14 D z/\af 14 D t={pos i,pos j,F} /\(F≠pos i/\F≠pos j)/\aW 14 D (ao 14 D {t})=∅ /\(aY D b t).card=1/\∀ u∈aj 14 D b,(ag 14 D u.1∩T).Nonempty:=by
 obtain⟨S,A,B,C,d,k,l,E,G⟩:=R;rw[ad] at d k l;have v:=y A;have H:=y B;obtain⟨U,W⟩:=pp h s w Q b N x (fun _ X=>y X);obtain⟨Y,P⟩:=U t S;obtain⟨F,I,f,-⟩:=cg aK h.1 (aC s) l;have m:F≠pos i:=fun c=>E (ei a v (by rw[<- c];exact f));have n:F≠pos j:=fun c=>G (ei a H (by rw[<- c];exact f));have p:pos i≠pos j:=fun c=>C (a.2 i v j H c);have q:({pos i,pos j,F}:Finset (ℕ×_d))⊆af 14 D t:=by{intro e c;rw[_mi,_mi,_ms] at c;rcases c with rfl|rfl|rfl;{exact aI a v d};{exact aI a H k};{exact I}};have g:({pos i,pos j,F}:Finset (ℕ×_d)).card=3:=by
  rw[_cin (by simp[p,Ne.symm m]),
   _c2 (Ne.symm n)]
 have r:=_eqc q (by omega);have K:t∈al 14 D:=by{rcases fu aK h (aC s) d with L|L;{exact absurd L (aN.1 v)};{exact L}};have M:=me h s b N K;rw[P,<-r,g,_ce] at M;exact⟨F,f,r.symm,⟨m,n⟩,P,by omega,W⟩
lemma ns {D:Dag} {pos:O->ℕ×_d} (h:ai 14 D) (k:aq D) (d:bL 14 D=0) (b:bA 14 md D pos) {t i j z:O} {F:ℕ×_d} (l:i∈aa 14 D) (m:j∈aa 14 D) (e:aO i t/\j≠i/\z≠i) (n:af 14 D t={pos i,pos j,F}) (q:am F∈af 14 D z):∀ a,a∈ag 14 D (aw D (pos i))↔aO i a:=by
 refine rx h k d b l e.1 (fun p g f c=>?_);rw[n,_mi,_mi,_ms] at g;rcases g with rfl|rfl|rfl;{exact f rfl}
 · have:j∈ag 14 D (aw D (am (pos j))):=by
    rw[show aw D (am (pos j))=aw D ((pos j).1,!(pos j).2) from rfl,(b.1 j m).2.2.2];exact _mss j
   exact e.2.1 (_ms.1 (c this))
 · exact e.2.2 (_ms.1 (c (ak.1 q).2.1))
lemma qE {D:Dag} {pos:O->ℕ×_d} (h:ai 14 D) (m:aq D) {t i x:O} {P F:ℕ×_d} (n:∀ e∈af 14 D t,e=pos i\/e=P\/e=F) (c:∀ a,aO i a->a∈ag 14 D (aw D (pos i))) (d:aO i t) (b:x≠t) (f:x≠i) (p:x∈ag 14 D (aw D P)) (r:x∈ag 14 D (aw D F)):False:=by
 obtain⟨q,g,j,-,k⟩:=sK i t x ((ad _ _).2 d) b f;obtain⟨e,s,l,u⟩:=bR h m (Ne.symm b) (Ne.symm j) (aG.1 k);rcases n e s with rfl|rfl|rfl;{exact u (c q ((ad _ _).1 g))};{exact l p};{exact l r}
lemma nw {D:Dag} {pos:O->ℕ×_d} (h:ai 14 D) (B:aq D) (l:bA 14 md D pos) (b:O->ℕ) (W:aM 14 D b) {t i j:O} {F:ℕ×_d} (Q:i∈aa 14 D) (R:j∈aa 14 D) (k:i≠j/\aO i t/\aO j t) (z:af 14 D t={pos i,pos j,F}) (S:F≠pos i/\F≠pos j) (m:∀ a,a∈ag 14 D (aw D (pos i))↔aO i a) (n:∀ a,a∈ag 14 D (aw D (pos j))↔aO j a) (X:(aY D b t).card=1) {u:Σ _:ℕ,ℕ} (C:u∈aj 14 D b) (f:t∈ag 14 D u.1) {x:O} (E:x∈ag 14 D u.1):x=t:=by
 by_contra d;have p:=fB C E;have G:x≠i:=fun e=>aN.1 Q (e▸p);have H:x≠j:=fun e=>aN.1 R (e▸p);obtain⟨v,T⟩:=_c1.1 X;have I:u=v:=by{have:u∈aY D b t:=ax.2 ⟨C,f⟩;rwa[T,_ms] at this}
 obtain⟨e0,c⟩:=jx aK h (aC B) b W (Ne.symm d) (fB C f) (fun u' C' ht'=>by
  have:u'∈aY D b t:=ax.2 ⟨C',ht'⟩;rw[T,_ms] at this
  rw[this,<-I];exact E) ⟨f,E⟩
 have z':∀ e∈af 14 D t,e=pos i\/e=pos j\/e=F:=fun e A=>by{rw[z] at A;simpa using A};have L:pos i∈af 14 D t:=by rw[z];simp
 have r:pos j∈af 14 D t:=by rw[z];simp
 have s:F∈af 14 D t:=by rw[z];simp
 have w:pos i≠pos j:=fun e=>k.1 (l.2 i Q j R e);by_cases M:x∈ag 14 D (aw D (pos i))
 · by_cases U:x∈ag 14 D (aw D (pos j))
   · exact d (kh i j x t k.1 ((ad _ _).2 (bl k.2.1)) ((ad _ _).2 (bl k.2.2)) ((ad _ _).2 (bl ((m x).1 M))) ((ad _ _).2 (bl ((n x).1 U))))
   · have N:pos j=e0:=by
      by_contra g;exact U (c _ r g)
     exact qE h B (fun e A=>or_left_comm.1 (z' e A)) (fun a P=>(n a).2 P) k.2.2 d H M (c F s (fun e=>S.2 (e.trans N.symm)))
 · have y:pos i=e0:=by
    by_contra g;exact M (c _ L g)
   exact qE h B z' (fun a P=>(m a).2 P) k.2.1 d G (c _ r (fun e=>w (y.trans e.symm))) (c F s (fun e=>S.1 (e.trans y.symm)))
lemma mg {D:Dag} {pos:O->ℕ×_d} (h:ai 14 D) (l:aq D) (a:bA 14 md D pos) {i s d:O} (g:i∈aa 14 D) (f:aO i s/\aO d s/\s≠i/\d≠i) (n:(af 14 D s).card<=2):∃ Z,(∀ t,t≠s->Z∉af 14 D t)/\Z∈af 14 D s/\am Z∈af 14 D d:=by
 obtain⟨Z,-,m,j⟩:=sF h l a g f.2.2.1 (aI a g f.1) n;obtain⟨e,b,c,-⟩:=cg aK h.1 (aC l) f.2.1;rw[m,_mi,_ms] at c;rcases c with k|k;{exact absurd (ei a g (by rw[<- k,aB];exact b)) f.2.2.2};{exact⟨Z,j,by rw[m];simp,by rw[<- k,aB];exact b⟩}
lemma lE {D:Dag} (h:ai 14 D) (c:aq D) (a:ap 14 D<=13) (b:aa 14 D={0,1,2}):False:=by
 have d:=aV 14 D;rw[b,show({0,1,2}:o).card=3 from rfl] at d;have f:=ry h c a (fun i e=>by rw[b];exact e) (by omega);have g:=dC 14 D;omega
lemma rC:∀ M:Finset (Fin 7),M.card<=3->2*M.card <=((M.image dE).biUnion (fun c=>aA c∩aU 0)).card:=by decide +kernel
lemma qF {D:Dag} (h:ai 14 D) (p:aq D) (q:ap 14 D<=13) (Q:Finset (Fin 7)) (r:aa 14 D=Q.image dE) (t:Q.card=4) (f:({0,1,2}:o)⊆Q.image dE):False:=by
 classical
 obtain⟨B,H⟩:=qD h p q r (by rw[_cii _ ed,t]) f;have g:∀ k∈Q,dE k∈aa 14 D:=fun k b=>by{rw[r];exact mem_image_of_mem _ b};have u:aU 0⊆al 14 D:=by{intro a C;by_contra v;have w:=aN.2 v;rw[r] at w;obtain⟨k,-,rfl⟩:=_mg.1 w;exact(by decide:∀ k:Fin 7,dE k∉aU 0) k C};let z:=univ.filter (fun k:Fin 7=>aQ 14 D (aU 0) (aA (dE k)));let e:=univ.filter
  (fun k:Fin 7=>¬ aQ 14 D (aU 0) (aA (dE k)))
 have j:=mc h p (aU 0) (Subset.refl _) u (z.image dE) (e.image dE) (Q.image dE) (fun i l=>by
  obtain⟨k,b,rfl⟩:=_mg.1 l
  exact⟨eU k,(_mf.1 b).2⟩)
  (fun c E=>by
   obtain⟨k,b,rfl⟩:=_mg.1 E;refine⟨fun E'=>?_,Or.inr ⟨eU k,(_mf.1 b).2⟩⟩;obtain⟨k',b',y⟩:=_mg.1 E';rw[ed y] at b'
   exact(_mf.1 b).2 (_mf.1 b').2)
  (fun i l=>by
   obtain⟨k,b,rfl⟩:=_mg.1 l
   exact⟨g k b,eU k⟩)
 have d:=kn h p (aU 0) (dB 0) ((e∩Q).image dE) (fun i l=>by
  obtain⟨k,b,rfl⟩:=_mg.1 l;rw[_mn] at b
  exact⟨g k b.2,eU k,(_mf.1 b.1).2⟩)
 rw[_cii _ ed] at d;rw[_cii _ ed,_cii _ ed,t] at j;have n:z.card+e.card=7:=by{have:=card_filter_add_card_filter_not (s:=(univ:Finset (Fin 7))) (fun k:Fin 7=>aQ 14 D (aU 0) (aA (dE k)));simpa using this};have w:=card_inter_add_card_sdiff e Q;have F:(e\Q).card<=(univ\Q).card:=
  _cl (sdiff_subset_sdiff (subset_univ _) (Subset.refl _))
 rw[card_univ_sdiff,t,Fintype.card_fin] at F;have A:=rC e (by omega);have G:(aU 0).card=7:=V;omega
lemma nx {D:Dag} (h:ai 14 D) (b:aq D) (a:ap 14 D<=13) (c:aa 14 D={0,1,2,3}):False:=qF h b a {0,1,2,3} (by rw[c];decide) rfl V
lemma n_ {D:Dag} (h:ai 14 D) (b:aq D) (a:ap 14 D<=13) (c:aa 14 D={0,1,2,5}):False:=qF h b a {0,1,2,5} (by rw[c];decide) rfl V
lemma lF {D:Dag} (h:ai 14 D) (c:aq D) (n:ap 14 D<=13) (M:aa 14 D={0,1,2,11}):False:=by
 obtain⟨f,F⟩:=qD h c n M rfl V;obtain⟨b,p⟩:=bt h c;obtain⟨pos,a⟩:=bQ aK h (aC c);have g:({0,1,2}:o)⊆aa 14 D:=by rw[M];decide
 have r:=g (show(0:O)∈({0,1,2}:o) by decide);have v:=g (show(1:O)∈({0,1,2}:o) by decide);have w:=g (show(2:O)∈({0,1,2}:o) by decide);obtain⟨F7,G,x,n7,-,c7,m1⟩:=nr h c a f F b p oQ g (t:=7) (i:=0) (j:=1) (z:=3) V;obtain⟨F13,A,m,H,-,c13,-⟩:=nr h c a f F b p oQ g (t:=13) (i:=1) (j:=2) (z:=4) V;obtain⟨F8,I,B,n8,-,c8,-⟩:=nr h c a f F b p oQ g (t:=8) (i:=2) (j:=0) (z:=6) V;have N:=ns h c f a r v V x G;have P:=ns h c f a v w V m A;have Q:=ns h c f a w r V B I;have l:∀ y:O,y∉({7,8,13}:o)->(af 14 D y).card<=2:=by
  intro y J;have E:aY D b y=∅:=by
   rw[eq_empty_iff_forall_notMem];intro u R;obtain⟨k,q⟩:=ax.1 R;rcases rB k (m1 u k) with S|T|n
   · exact J (by
      rw[nw h c a b p r v V x n7 N P c7 k (ax.1 S).2 q]
      decide)
   · exact J (by
      rw[nw h c a b p w r V B n8 Q N c8 k (ax.1 T).2 q]
      decide)
   · exact J (by
      rw[nw h c a b p v w V m H P Q c13 k (ax.1 n).2 q]
      decide)
  have:=bi h c b p y;rw[E,_ce] at this;omega
 obtain⟨Z1,p1,q1,r1⟩:=mg h c a r (s:=10) (d:=5) V (l 10 V);obtain⟨Z2,p2,q2,r2⟩:=mg h c a v (s:=9) (d:=5) V (l 9 V);obtain⟨Z3,-,q3,r3⟩:=mg h c a w (s:=12) (d:=5) V (l 12 V);have K:am Z1≠am Z2:=fun e=>
  p1 9 V (by rw[<- aB Z1,e,aB];exact q2)
 have H':am Z1≠am Z3:=fun e=>
  p1 12 V (by rw[<- aB Z1,e,aB];exact q3)
 have L:am Z2≠am Z3:=fun e=>
  p2 12 V (by rw[<- aB Z2,e,aB];exact q3)
 have C:({am Z1,am Z2,am Z3}:Finset (ℕ×_d))⊆af 14 D 5:=by{intro e E;rw[_mi,_mi,_ms] at E;rcases E with rfl|rfl|rfl <;> assumption};have:=_cl C;rw[_cin (by simp[K,H']),_c2 L] at this;have:=l 5 V;omega
section PeMixed
open Finset
def lG:_ep (O):=⟨k6 [11,12,13,7,8,9,10,3,4,5,6,0,1,2],k6 [11,12,13,7,8,9,10,3,4,5,6,0,1,2],by intro x;revert x;decide +kernel,by intro x;revert x;decide +kernel⟩
def ej:o:={0,1,11,12}
def kt (D:Dag) (x:O):ℕ:=bn D ((cD 14 D).filter (fun w=>x∈ag 14 D w))
def ku (D:Dag) (b:O->ℕ) (pos:O->ℕ×_d):Prop:=ai 14 D/\aq D/\aM 14 D b/\bA 14 md D pos/\aa 14 D=ej
lemma os (σ:_ep (O)) {D:Dag} (a:au 14 D) (x:O):kt (bo σ D) (σ x)=kt D x:=eo σ D _ _ (fun w=>by rw[fh σ a];simp)
variable {D : Dag} {pos : Fin 14 → ℕ × Bool} {b : Fin 14 → ℕ}
lemma ot (d:ku D b pos) {x:O} (f:x∈al 14 D):kt D x=1+(aY D b x).card:=by
 obtain⟨h,c,g,-⟩:=d;have k:=m9 aK h (aC c) x;have l:=me h c b g f;have i:(cD 14 D).filter (fun w=>x∈ag 14 D w)=ao 14 D {x}:=by{ext w;rw[mem_filter,b7,bP];refine⟨fun a=>a.2,fun a=>⟨?_,a⟩⟩;have m:=cP a;have j:w≠bH 14 D:=fun e=>by{rw[e,fN c] at a;exact notMem_empty _ a};unfold bH at j;omega};unfold kt;rw[i];omega
lemma g_ (a:ku D b pos) (i:O) (c:i∈ej):i∈aa 14 D:=by
 rw[a.2.2.2.2];exact c
lemma mh (c:ku D b pos) (x:O) (d:x∉ej):x∈al 14 D:=by
 by_contra a;exact d (c.2.2.2.2▸aN.2 a)
lemma lH (a:bA 14 md D pos) {i x:O} {e:ℕ×_d} (c:i∈aa 14 D) (d:x∈al 14 D) (f:am e∈af 14 D x):e≠pos i:=fun b=>aN.1 c (ei a c (b▸f)▸d)
lemma m0 (a:bA 14 md D pos) {i x:O} {e:ℕ×_d} (b:i∈aa 14 D) (c:x∈al 14 D) (d:e∈af 14 D x):am e≠pos i:=lH a b c (by rw[aB];exact d)
lemma lI (a:bA 14 md D pos) {i t:O} (b:i∈aa 14 D) (c:t∈ag 14 D (aw D (pos i))):pos i∈af 14 D t:=ak.2 ⟨(a.1 i b).1,c,by rw[(a.1 i b).2.1];exact notMem_empty t⟩
lemma sr (a:ku D b pos) {x:O} (J:o) (c:∀ i∈J,i∈ej/\ab i x=true):∀ i∈J,i∈aa 14 D/\pos i∈af 14 D x:=fun i d=>
 ⟨g_ a _ (c i d).1,aI a.2.2.2.1 (g_ a _ (c i d).1) ((ad _ _).1 (c i d).2)⟩
lemma kE (a:bA 14 md D pos) {x:O} (J:o) (g:∀ i∈J,i∈aa 14 D/\pos i∈af 14 D x) (f:Finset (ℕ×_d)) (n:∀ e∈f,e∈af 14 D x/\∀ i∈J,e≠pos i):J.card+f.card<=(af 14 D x).card:=by
 classical
 have b:Set.InjOn pos J:=fun i c j p h=>a.2 i (g i c).1 j (g j p).1 h;have d:Disjoint (J.image pos) f:=by{rw[disjoint_left];intro e k l;obtain⟨i,c,rfl⟩:=mem_image.1 k;exact(n _ l).2 i c rfl}
 have:=card_le_card (union_subset (fun e m=>by
  obtain⟨i,c,rfl⟩:=mem_image.1 m
  exact(g i c).2) (fun e m=>(n e m).1):J.image pos∪f⊆af 14 D x)
 rwa[card_union_of_disjoint d,card_image_of_injOn b] at this
lemma ny (s:ku D b pos) {v t j q:O} (p:j∈aa 14 D) (x:v∈al 14 D) (c:∀ u∈aj 14 D b,v∈ag 14 D u.1->t∈ag 14 D u.1) {w:ℕ} (y:v∈ag 14 D w/\t∈ag 14 D w) (z:ab j v=true/\ab j q=true/\v≠t/\v≠q/\ab t q=false):t∈ag 14 D (aw D (pos j)):=by
 obtain⟨h,r,A,a,-⟩:=s;obtain⟨d,f,g,k,l⟩:=z;rw[ad] at d f;obtain⟨e0,i⟩:=jx aK h (aC r) b A g x c y;by_contra B;have C:pos j=e0:=by{by_contra m;exact B (i _ (aI a p d) m)};obtain⟨e,E,F,G⟩:=bR h r g k (aG.1 l);exact F (i e E (fun n=>G (by rw[n,<-C];exact(a.1 j p).2.2.1 q f)))
lemma qG (a:ku D b pos) {v i j t:O} {u:Σ _:ℕ,ℕ} (z:u∈aj 14 D b) (g:v∈ag 14 D u.1) (n:∀ u'∈aj 14 D b,v∈ag 14 D u'.1->u'=u) (A:i∈ej/\j∈ej/\v∉ej/\ab i v=true/\ab j v=true /\∀ t:O,t∉ej->v≠t->∃ h l:O,(ab i h=true/\v≠h/\ab t h=false) /\ab j l=true/\v≠l/\ab t l=false) (f:v≠t) (m:t∈ag 14 D u.1):∀ k∈({i,j}:o),pos k∈af 14 D t:=by
 obtain⟨w,x,y,p,q,B⟩:=A;obtain⟨h,l,⟨a1,a2,a3⟩,a4,a5,a6⟩:=B t (fun C=>aN.1 (g_ a _ C) (fB z m)) f;have c:∀ u'∈aj 14 D b,v∈ag 14 D u'.1->t∈ag 14 D u'.1:=fun u' z' y'=>n u' z' y'▸m;intro k E;rcases mem_insert.1 E with e|e
 · rw[e]
   exact lI a.2.2.2.1 (g_ a _ w) (ny a (g_ a _ w) (mh a _ y) c ⟨g,m⟩ ⟨p,a1,f,a2,a3⟩)
 · rw[mem_singleton.1 e]
   exact lI a.2.2.2.1 (g_ a _ x) (ny a (g_ a _ x) (mh a _ y) c ⟨g,m⟩ ⟨q,a4,f,a5,a6⟩)
lemma qj (x:ku D b pos) (l:bL 14 D=0) {v t0:O} (J:o) (g:∀ i∈J,i∈aa 14 D/\pos i∈af 14 D v) {P:ℕ×_d} (s:P∈af 14 D v/\∀ i∈aa 14 D,P≠pos i) (m:t0∈ag 14 D (aw D (am P))) (n:(af 14 D v).card<=J.card+1) (i:O) (y:i∈J) (u:ab i v=true/\t0≠i):∀ t,t∈ag 14 D (aw D (pos i))↔aO i t:=by
 classical
 obtain⟨h,z,-,a,-⟩:=x;refine rx h z l a (g i y).1 ((ad _ _).1 u.1) (fun p A q c=>?_);by_cases w:∃ j∈J,p=pos j
 · obtain⟨j,d,rfl⟩:=w
   have k:j∈ag 14 D (aw D (am (pos j))):=by{rw[show aw D (am (pos j))=aw D ((pos j).1,!(pos j).2) from rfl,(a.1 j (g j d).1).2.2.2];exact mem_singleton_self j};exact q (by rw[mem_singleton.1 (c k)])
 · by_cases k:p=P
   · exact u.2 (mem_singleton.1 (c (k▸m)))
   · have:=kE a J g {P,p} (fun e f=>by
      rcases mem_insert.1 f with f|f;{rw[f];exact⟨s.1,fun j d=>s.2 j (g j d).1⟩}
      · rw[mem_singleton.1 f]
        exact⟨A,fun j d r=>w ⟨j,d,r⟩⟩)
     rw[card_pair (Ne.symm k)] at this;omega
lemma rD (A:ku D b pos) {v c:O} (B:v∈al 14 D) (d:v≠c) {w:ℕ} (C:v∈ag 14 D w/\c∈ag 14 D w) (z:(aY D b v).card<=(aY D b v∩aY D b c).card+1) {p q P:ℕ×_d} (E:p∈af 14 D v) (F:q∈af 14 D v) (G:P∈af 14 D v) (H:p≠q/\p≠P/\q≠P) (k:c∉ag 14 D (aw D P)):c∈ag 14 D (aw D p)\/c∈ag 14 D (aw D q):=by
 classical
 obtain⟨h,I,J,-⟩:=A;by_contra a;rw[not_or] at a;have M:=iK h.1 b J d B;have N:=gN h v c d (by rw[fN I];exact notMem_empty v);obtain⟨j,s,K,L,-,l,m,n,-⟩:=ji h.1 d C;have f:∀ e∈af 14 D v,c∉ag 14 D (aw D e) ->e∈(aE 14 D (aR 14 D v c)).erase (j,s):=fun e g r=>
  mem_erase.2 ⟨fun t=>by
   have:=cY h.1 g;rw[t,L] at this
   exact _fnt this,dY.2 ⟨(ak.1 g).1,⟨(ak.1 g).2.1,r⟩,fun x=>(ak.1 g).2.2 x.1⟩⟩
 have y:=two_lt_card.2 ⟨p,f _ E a.1,q,f _ F a.2,P,f _ G k,H⟩;rw[card_erase_of_mem (dY.2 ⟨K,⟨m,n⟩,fun x=>x.2 l⟩)] at y
 have Q:((aj 14 D b).filter (fun u=>v∈ag 14 D u.1/\c∉ag 14 D u.1)).card<=(aY D b v\aY D b c).card:=card_le_card (fun u i=>by
  rw[mem_filter] at i
  exact mem_sdiff.2 ⟨ax.2 ⟨i.1,i.2.1⟩,fun f=>i.2.2 (ax.1 f).2⟩)
 have R:=card_inter_add_card_sdiff (aY D b v) (aY D b c);omega
lemma rE (d:ku D b pos) {x y z i j:O} (G:i∈ej/\j∈ej /\x∉ej/\y∉ej/\z∉ej/\ab i x=true/\ab j y=true /\ab x y=true/\ab z x=true/\z≠y) (H:(aY D b x).card=0) (I:(aY D b y).card=0):False:=by
 obtain⟨g1,g2,g3,g4,g5,f,g,k,l,u⟩:=G;rw[ad] at f g k l;have m:=g_ d _ g1;have t:=g_ d _ g2;have A:=mh d _ g3;have B:=mh d _ g4;have J:=mh d _ g5;obtain⟨h,n,C,a,-⟩:=d;have E:=aK;have F:=aC n;obtain⟨Zx,-,p,-⟩:=sF h n a m (fun e=>aN.1 m (e▸A)) (aI a m f) (by have:=bi h n b C x;omega);obtain⟨Zy,-,v,w⟩:=sF h n a t (fun e=>aN.1 t (e▸B)) (aI a t g) (by have:=bi h n b C y;omega);obtain⟨e,q,r,-⟩:=cg E h.1 F k;obtain⟨e',q',r',-⟩:=cg E h.1 F l;have K:e=Zx:=mem_singleton.1 ((mem_insert.1 (p▸q)).resolve_left (lH a m B r));have L:am e=Zy:=mem_singleton.1 ((mem_insert.1 (v▸r)).resolve_left (m0 a t A q));have M:am e'=Zx:=mem_singleton.1 ((mem_insert.1 (p▸r')).resolve_left (m0 a m J q'));have N:e'=Zy:=by rw[<- L,K,<-M,aB]
 exact w z u (N▸q')
lemma rF {x:O} {c:Σ _:ℕ,ℕ} (h:(aY D b x).card=1) (d:c∈aj 14 D b) (e:x∈ag 14 D c.1):∀ u∈aj 14 D b,x∈ag 14 D u.1->u=c:=by
 obtain⟨a,i⟩:=card_eq_one.1 h;intro u j k;have f:u∈aY D b x:=ax.2 ⟨j,k⟩;have g:c∈aY D b x:=ax.2 ⟨d,e⟩;rw[i,mem_singleton] at f g;rw[f,g]
lemma qH (t:ku D b pos) {x i:O} {us uo:Σ _:ℕ,ℕ} (Js Jo:o) {F:ℕ×_d} (w:Js⊆ej/\Jo⊆ej/\Js.card=2/\Jo.card=2/\Disjoint Js Jo/\i∈Js /\ab i x=true) (u:x∈ag 14 D us.1->∀ k∈Js,pos k∈af 14 D x) (v:x∈ag 14 D uo.1->∀ k∈Jo,pos k∈af 14 D x) (hρ:(aY D b x).card<=(if x∈ag 14 D us.1 then 1 else 0) + if x∈ag 14 D uo.1 then 1 else 0) (p:F∈af 14 D x/\∀ k∈aa 14 D,F≠pos k):∀ e∈af 14 D x,e=F\/e∈Js.image pos:=by
 classical
 obtain⟨g1,g2,g3,g4,g5,g6,g7⟩:=w;have c:∀ {k:O},k∈ej->k∈aa 14 D:=g_ t _;obtain⟨h,y,z,d,-⟩:=t;have A:=bi h y b z x;have l:=aI d (c (g1 g6)) ((ad _ _).1 g7);have m:∀ J:o,(∀ k∈J,k∈aa 14 D/\pos k∈af 14 D x) ->J.card+1<=(af 14 D x).card:=fun J q=>by
  have:=kE d J q {F} (fun e r=>by
   rw[mem_singleton.1 r];exact⟨p.1,fun k a=>p.2 k (q k a).1⟩)
  rwa[card_singleton] at this
 by_cases ko:x∈ag 14 D uo.1
 · exfalso
   by_cases ks:x∈ag 14 D us.1
   · have:=m (Js∪Jo) (fun k a=>by
      rcases mem_union.1 a with a|a;{exact⟨c (g1 a),u ks k a⟩}
      · exact⟨c (g2 a),v ko k a⟩)
     rw[card_union_of_disjoint g5] at this;simp only[ko,ks,ite_true] at hρ;omega
   · have:=m (insert i Jo) (fun k a=>by
      rcases mem_insert.1 a with a|a;{rw[a];exact⟨c (g1 g6),l⟩}
      · exact⟨c (g2 a),v ko k a⟩)
     rw[card_insert_of_notMem (disjoint_left.1 g5 g6)] at this;simp only[ko,ks,ite_true,ite_false] at hρ;omega
 · intro e r
   by_contra g;rw[not_or] at g;have n:∀ J:o,J⊆Js->(∀ k∈J,pos k∈af 14 D x) ->J.card+2<=(af 14 D x).card:=fun J j q=>by
    have:=kE d J (fun k a=>⟨c (g1 (j a)),q k a⟩) {F,e} (fun e' r'=>by
     rcases mem_insert.1 r' with r'|r';{rw[r'];exact⟨p.1,fun k a=>p.2 k (c (g1 (j a)))⟩}
     · rw[mem_singleton.1 r']
       exact⟨r,fun k a s=>g.2 (mem_image.2 ⟨k,j a,s.symm⟩)⟩)
    rwa[card_pair (Ne.symm g.1)] at this
   by_cases ks:x∈ag 14 D us.1
   · have:=n Js (Subset.refl _) (u ks)
     simp only[ko,ks,ite_true,ite_false] at hρ;omega
   · have:=n {i} (singleton_subset_iff.2 g6) (fun k a=>by
      rw[mem_singleton.1 a];exact l)
     rw[card_singleton] at this;simp only[ko,ks,ite_false] at hρ;omega
lemma pu {D:Dag} (h:ai 14 D) (U:aq D) (h13:ap 14 D<=13) (hI:aa 14 D=ej) (hle:kt D 7<=kt D 3):False:=by
 classical
 have hG:=aK;have hC:=aC U;obtain⟨b,hb⟩:=bt h U;obtain⟨pos,c⟩:=bQ hG h hC;obtain⟨H,C,E,hn7,hn3,-⟩:=cg hG h.1 hC (x:=3) (y:=7) V;have r:ku D b pos:=⟨h,U,hb,c,hI⟩;have n:=g_ r;have v:=mh r;have i0:=n 0 V;have i1:=n 1 V;have l3:=v 3 V;have l7:=v 7 V;have hR:(aj 14 D b).card+bL 14 D<=3:=by{have h1:=bS h.1 b hb;have h2:=aV 14 D;have h3:=bg 14 D;rw[hI,show ej.card=4 from rfl] at h2;omega};have A:=sr r (x:=7) {0,1} V;have p:=sr r (x:=3) {11,12} V;have L:∀ i∈aa 14 D,am H≠pos i:=fun i g=>m0 c g l3 C;have M:∀ i∈aa 14 D,H≠pos i:=fun i g=>lH c g l7 E
 have c7:=kE c _ A {am H} (fun e he=>by
  rw[mem_singleton.1 he];exact⟨E,fun i g=>L i (A i g).1⟩)
 have c3:=kE c _ p {H} (fun e he=>by
  rw[mem_singleton.1 he];exact⟨C,fun i g=>M i (p i g).1⟩)
 have G:({0,1}:o).card=2/\({11,12}:o).card=2 /\({4,6,2,5}:o).card=4:=⟨rfl,rfl,rfl⟩;rw[card_singleton,G.1] at c7;rw[card_singleton,G.2.1] at c3;have k7:=me h U b hb l7;have k3:=me h U b hb l3;have e7:=ot r l7;have e3:=ot r l3;have W:=(ak.1 C).2.1;have hX:∀ x∈({4,6,2,5}:o),x∈al 14 D/\x≠3/\x≠7 /\∃ w,x∈ag 14 D w/\(3:O)∈ag 14 D w:=by{intro x K;obtain⟨g1,g2,g3,i,g,g4,g5⟩:=(by decide:∀ x∈({4,6,2,5}:o),x∉ej/\x≠3/\x≠7/\∃ i∈ej,ab i x=true/\ab i 3=true) x K;have hi2:=(c.1 i (n i g)).2.2.1;exact⟨v x g1,g2,g3,_,hi2 x ((ad _ _).1 g4),hi2 3 ((ad _ _).1 g5)⟩};have hA:¬ ∀ u∈aj 14 D b,(7:O)∈ag 14 D u.1 ->(3:O)∈ag 14 D u.1:=by
  intro hA;obtain⟨u,l⟩:=card_pos.1 (show 0<(aY D b 7).card by omega);rw[ax] at l;have hw:(7:O)∈ag 14 D u.1/\(3:O)∈ag 14 D u.1:=⟨l.2,hA u l.1 l.2⟩;have p0:=lI c i0 (ny r i0 l7 hA hw (q:=8) V);have p1:=lI c i1 (ny r i1 l7 hA hw (q:=9) V)
  have c5:=kE c ej (fun i g=>⟨n i g,by
   simp only[ej,mem_insert,mem_singleton] at g;rcases g with rfl|rfl|rfl|rfl
   exacts [p0,p1,(p 11 V).2,(p 12 V).2]⟩) {H}
   (fun e he=>by rw[mem_singleton.1 he];exact⟨C,fun i g=>M i (n i g)⟩)
  rw[show ej.card=4 from rfl,card_singleton] at c5;have B:aY D b 3=aj 14 D b:=eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  have:=oM h U b hb oo l3 {4,6,2,5} (fun x K=>
   ⟨(hX x K).1,(hX x K).2.1,fun u l _=>(ax.1 (B▸l)).2,(hX x K).2.2.2⟩)
  rw[G.2.2] at this;omega
 obtain⟨uk,I,hk7,hk3⟩:∃ u∈aj 14 D b,(7:O)∈ag 14 D u.1/\(3:O)∉ag 14 D u.1:=by
  by_contra d
  exact hA (fun u l h7=>by
   by_contra h3
   exact d ⟨u,l,h7,h3⟩)
 have hs3:aY D b 3⊆(aj 14 D b).erase uk:=fun u l=>
  mem_erase.2 ⟨fun e=>hk3 (e▸(ax.1 l).2),(ax.1 l).1⟩
 have hle3:=card_le_card hs3;rw[card_erase_of_mem I] at hle3;have h71:(aY D b 7).card=1:=by
  by_contra h71;have hui:=card_union_add_card_inter (aY D b 3) (aY D b 7);have hun:(aY D b 3∪aY D b 7).card<=(aj 14 D b).card:=card_le_card (union_subset (filter_subset _ _) (filter_subset _ _));obtain⟨uj,Z⟩:=card_pos.1 (show 0<(aY D b 3∩aY D b 7).card by omega);rw[mem_inter,ax,ax] at Z;have hw:(3:O)∈ag 14 D uj.1/\(7:O)∈ag 14 D uj.1:=⟨Z.1.2,Z.2.2⟩;have hpn:∀ i∈ej,∀ j∈ej,i≠j->pos i≠pos j:=fun i g j hj hij e=>hij (c.2 i (n i g) j (n j hj) e);have a7:=rD r l3 V hw (by omega) (p 11 V).2 (p 12 V).2 C ⟨hpn 11 V 12 V V,(M 11 (n 11 V)).symm,(M 12 (n 12 V)).symm⟩ hn7;have a3:=rD r l7 V hw.symm (by rw[inter_comm];omega) (A 0 V).2 (A 1 V).2 E ⟨hpn 0 V 1 V V,(L 0 i0).symm,(L 1 i1).symm⟩ hn3;have fin:∀ j∈({11,12}:o),(7:O)∉ag 14 D (aw D (pos j)):=by{intro j hj h7j;have hJ:∀ i∈insert j ({0,1}:o),i∈aa 14 D/\pos i∈af 14 D 7:=fun i g=>by{rcases mem_insert.1 g with g|g;{rw[g];exact⟨(p j hj).1,lI c (p j hj).1 h7j⟩};{exact A i g}};have N:(insert j ({0,1}:o)).card=3:=by{rw[mem_insert,mem_singleton] at hj;rcases hj with rfl|rfl <;> rfl};have f:=qj r (by omega) _ hJ ⟨E,L⟩ (by rw[aB];exact W) (by omega);rcases a3 with a|a;{exact absurd ((f 0 (by simp) V 3).1 a) V};{exact absurd ((f 1 (by simp) V 3).1 a) V}};rcases a7 with a|a;{exact fin 11 V a};{exact fin 12 V a}
 have hu7:=rF h71 I hk7;have h0:∀ t:O,7≠t->t∈ag 14 D uk.1 ->∀ k∈({0,1}:o),pos k∈af 14 D t:=fun t ht htu=>qG r I hk7 hu7 V ht htu;have f7:=fun m:bL 14 D=0=>qj r m {0,1} A ⟨E,L⟩ (by rw[aB];exact W) (by rw[G.1];omega);have hpk:bL 14 D=0->∀ t∈ag 14 D uk.1,t=7:=by{intro m t ht;by_contra J;have a:=h0 t (Ne.symm J) ht;exact J ((by decide:∀ t:O,aO 0 t->aO 1 t->t=7) t ((f7 m 0 V V t).1 (ak.1 (a 0 V)).2.1) ((f7 m 1 V V t).1 (ak.1 (a 1 V)).2.1))};have h31:(aY D b 3).card=1:=by
  by_contra h31;have m:bL 14 D=0:=by omega
  have heq:=eq_of_subset_of_card_le hs3 (by rw[card_erase_of_mem I];omega)
  have:=qY h U m b hb oo l3 {4,6,2,5} (fun x K=>by
   obtain⟨g1,g2,g3,g4⟩:=hX x K;refine⟨g1,g2,fun u l hxu=>?_,g4⟩;by_cases huu:u=uk;{exact absurd (hpk m x (huu▸hxu)) g3}
   · exact(ax.1 (heq▸mem_erase.2 ⟨huu,l⟩)).2)
   (i1:=5) (i2:=8) i0 i1 (Or.inr (Or.inl ⟨rfl,rfl⟩))
  rw[G.2.2] at this;omega
 obtain⟨uc,s⟩:=card_pos.1 (show 0<(aY D b 3).card by omega);rw[ax] at s;have hu3:=rF h31 s.1 s.2;have J:uc≠uk:=fun e=>hk3 (e▸s.2);have co3:∀ t:O,3≠t->t∈ag 14 D uc.1 ->∀ k∈({11,12}:o),pos k∈af 14 D t:=fun t ht htu=>qG r s.1 s.2 hu3 V ht htu;have hR2:(aj 14 D b).card=2:=by
  by_contra hR2;have m:bL 14 D=0:=by omega
  have f3:=qj r m {11,12} p ⟨C,M⟩ (ak.1 E).2.1 (by rw[G.2.1];omega);have hpc:∀ t∈ag 14 D uc.1,t=3:=by{intro t ht;by_contra J';have a:=co3 t (Ne.symm J') ht;exact J' ((by decide:∀ t:O,aO 11 t->aO 12 t->t=3) t ((f3 11 V V t).1 (ak.1 (a 11 V)).2.1) ((f3 12 V V t).1 (ak.1 (a 12 V)).2.1))};have N:(((aj 14 D b).erase uc).erase uk).card<=1:=by{rw[card_erase_of_mem (mem_erase.2 ⟨Ne.symm J,I⟩),card_erase_of_mem s.1];omega};have Y:∀ x:O,x≠3->x≠7->∀ u∈aj 14 D b,x∈ag 14 D u.1->u∈((aj 14 D b).erase uc).erase uk:=fun x a3 a7 u l K=>mem_erase.2 ⟨fun e=>a7 (hpk m x (e▸K)),mem_erase.2 ⟨fun e=>a3 (hpc x (e▸K)),l⟩⟩;have R:∀ P Q i a:O,(i∈ej/\P∉ej/\P≠3/\P≠7/\Q≠3 /\Q≠7/\(ab i P=true/\ab i a=true/\P≠Q/\P≠a /\ab Q a=false)/\¬ aO i Q) ->(∀ t,t∈ag 14 D (aw D (pos i))↔aO i t) ->(aY D b P).card≠0->(aY D b Q).card≠0->False:=by{intro P Q i a hg hf n1 n2;obtain⟨g1,g2,g3,g4,g5,g6,g7,g8⟩:=hg;obtain⟨u1,S⟩:=card_pos.1 (Nat.pos_of_ne_zero n1);obtain⟨u2,T⟩:=card_pos.1 (Nat.pos_of_ne_zero n2);rw[ax] at S T;have h2:=Y Q g5 g6 u2 T.1 T.2;have B:∀ u∈aj 14 D b,P∈ag 14 D u.1->Q∈ag 14 D u.1:=fun u l K=>card_le_one.1 N u (Y P g3 g4 u l K) u2 h2▸T.2;exact g8 ((hf Q).1 (ny r (n i g1) (v P g2) B ⟨S.2,B u1 S.1 S.2⟩ g7))};have l1:(aY D b 4).card≠0\/(aY D b 10).card≠0:=by{by_contra d;rw[not_or,not_not,not_not] at d;exact rE r (x:=4) (y:=10) (z:=13) (i:=11) (j:=0) V d.1 d.2};have l2:(aY D b 5).card≠0\/(aY D b 9).card≠0:=by{by_contra d;rw[not_or,not_not,not_not] at d;exact rE r (x:=5) (y:=9) (z:=10) (i:=12) (j:=1) V d.1 d.2};have f11:=f3 11 V V;have f0:=f7 m 0 V V;rcases l1 with n1|n1 <;> rcases l2 with n2|n2;{exact R 4 5 11 3 V f11 n1 n2};{exact R 4 9 11 3 V f11 n1 n2};{exact R 10 5 0 7 V f0 n1 n2};{exact R 10 9 0 7 V f0 n1 n2}
 have hres:({uc,uk}:Finset (Σ _:ℕ,ℕ))=aj 14 D b:=eq_of_subset_of_card_le (fun u l=>by
  rcases mem_insert.1 l with l|l;{rw[l];exact s.1}
  · rw[mem_singleton.1 l];exact I) (by rw[card_pair J,hR2])
 have hρ:∀ x:O,(aY D b x).card <=(if x∈ag 14 D uc.1 then 1 else 0)+if x∈ag 14 D uk.1 then 1 else 0:=fun x=>by{have:=card_filter (fun u:Σ _:ℕ,ℕ=>x∈ag 14 D u.1) {uc,uk};rw[sum_pair J,hres] at this;exact this.le};obtain⟨F,hF1,hF2,-⟩:=cg hG h.1 hC (x:=4) (y:=10) V;have P4:=qH r (x:=4) (i:=11) {11,12} {0,1} V (co3 4 V) (h0 4 V) (hρ 4) ⟨hF1,fun k hk=>lH c hk (v 10 V) hF2⟩;have P10:=qH r (x:=10) (i:=0) {0,1} {11,12} V (h0 10 V) (co3 10 V) (by rw[Nat.add_comm];exact hρ 10) ⟨hF2,fun k hk=>m0 c hk (v 4 V) hF1⟩;obtain⟨e,he1,he2,-⟩:=cg hG h.1 hC (x:=4) (y:=13) V;rcases P4 e he1 with h1|h1
 · rw[h1] at he2
   obtain⟨e',he',h4,h5⟩:=bR h U (x:=10) (a:=7) (b:=13) V V V;rcases P10 e' he' with h6|h6;{exact h5 (h6▸(ak.1 he2).2.1)}
   · obtain⟨k,hk,rfl⟩:=mem_image.1 h6
     exact h4 (ak.1 (A k hk).2).2.1
 · obtain⟨k,hk,rfl⟩:=mem_image.1 h1
   exact lH c (p k hk).1 (v 13 V) he2 rfl
lemma lJ {D:Dag} (h:ai 14 D) (c:aq D) (a:ap 14 D<=13) (d:aa 14 D={0,1,11,12}):False:=by
 by_cases b:kt D 7<=kt D 3;{exact pu h c a d b}
 · obtain⟨e,f,-,g,-,-,-,i⟩:=jj lG (lt (by decide +kernel)) h c
   have j:=os lG h.1 3;have k:=os lG h.1 7;rw[show lG 3=7 from by decide] at j;rw[show lG 7=3 from by decide] at k;exact pu e f (g▸a) (by rw[i,d];decide) (by omega)
end PeMixed
lemma hV (C:Circuit) (e:Monotone2 C) (g:∀ x:O->_d,C.eval (_of x)=true↔bw x):27<=C.size:=by
 by_contra i;obtain⟨D,h,c,f,-,a,-,-,-,d⟩:=kI C e g (by omega);rcases mN _ d with ⟨-,b⟩|⟨-,b⟩|⟨-,b|b⟩| ⟨-,b|b|b|b⟩|⟨-,b|b|b⟩|⟨-,b|b⟩|⟨-,b⟩;{exact rr h c f b};{exact rs h c a b};{exact lC h c a b};{exact nm h c a b};{exact nx h c a b};{exact n_ h c a b};{exact lF h c a b};{exact lJ h c a b};{exact lE h c a b};{exact nq h c a b};{exact mT h c a b};{exact nn h c a b};{exact mS h c a b};{exact qV h c a b}
def kW:O->O:=fun i=>([0,1,2,3,4,5,6,7,13,12,11,10,9,8]:_F (O)).getD i.val 0
def cE (w:_F _d) (g:Gate):_F _d:=w ++ [g.op.eval (g.inputs.map fun i=>w.getD i false)]
lemma ss:∀ a b:Fin 7,(a=b\/a=b+1\/a=b+3)->((kW (Fin.castAdd 7 a)).val,(kW (Fin.natAdd 7 b)).val)∈([(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]:_F (ℕ×ℕ)):=by decide +kernel
lemma sL:∀ u v:O,(u.val,v.val)∈([(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]:_F (ℕ×ℕ))->∃ a b:Fin 7,(a=b\/a=b+1\/a=b+3)/\kW (Fin.castAdd 7 a)=u/\kW (Fin.natAdd 7 b)=v:=by decide +kernel
end _B
namespace _S
def e_:_F (ℕ×ℕ):=[(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
def h_ (x:O->_d):Prop:=∃ u v:O,(u.val,v.val)∈e_/\x u=true/\x v=true
abbrev aP (u v:O):Prop:=(u.val,v.val)∈e_\/(v.val,u.val)∈e_
def rG (u:O):ℕ:=match u.val with|0=>1280|1=>8832|2=>12544|3=>6272|4=>11264|5=>5632|6=>2816|7=>10|8=>69|9=>98|10=>49|11=>88|12=>44|_=>22
def ac (u v:O):_d:=(rG u).testBit v.val
lemma ae:∀ u v:O,ac u v=true↔aP u v:=by
 decide +kernel
lemma aH {u v:O}:ac u v=false↔¬ aP u v:=by
 rw[<- ae];cases ac u v <;> decide
lemma bm {u v:O} (h:aP u v):aP v u:=h.symm
lemma dx (u:O):¬ aP u u:=by
 revert u;decide +kernel
lemma ek (x:O->_d):h_ x↔∃ u v:O,aP u v/\x u=true/\x v=true:=by
 constructor;{rintro⟨u,v,a,b,c⟩;exact⟨u,v,Or.inl a,b,c⟩}
 · rintro⟨u,v,a|d,b,c⟩
   · exact⟨u,v,a,b,c⟩
   · exact⟨v,u,d,c,b⟩
def az (v:O):o:=univ.filter (fun u=>ac v u=true)
def aD (v:O):o:=az v
lemma ie (v:O):aD v=az v:=rfl
lemma cn {i a:O}:a∈aD i↔aP i a:=by
 simp only[aD,az,_mf,_mv,true_and,ae]
lemma gf:∀ v:O,(az v).card=2\/(az v).card=3:=by
 decide +kernel
lemma ig:∀ u v:O,u≠v ->(az u∩az v).card<=1:=by
 decide +kernel
lemma dU:∀ u v:O,u≠v->∃ z:O,aP u z/\¬ aP v z:=by
 have h:∀ u v:O,u≠v->∃ z:O,ac u z=true/\ac v z=false:=by{decide +kernel};intro u v a;obtain⟨z,b,c⟩:=h u v a;exact⟨z,(ae u z).1 b,aH.1 c⟩
lemma pw {i j:O} (h:aD i=aD j):i=j:=by
 by_contra a;obtain⟨z,b,c⟩:=dU i j a;have d:z∈aD i:=cn.2 b;rw[h,cn] at d;exact c d
def cq (v:O):O:=match v.val with|0=>10|1=>9|2=>13|3=>7|4=>11|5=>12|6=>8|7=>3|8=>6|9=>1|10=>0|11=>4|12=>5|_=>2
lemma ii:∀ v:O,ac v (cq v)=true/\cq (cq v)=v:=by
 decide +kernel
def eE (S:o):Prop:=∀ u v:O,aP u v->u∈S\/v∈S
def dI (I:o):Prop:=∀ u∈I,∀ v∈I,¬ aP u v
lemma eV {S:o} (b:eE S):7<=S.card:=by
 have a:∀ v:O,v∈S\/cq v∈S:=fun v=>
  b v (cq v) ((ae v (cq v)).1 (ii v).1)
 have c:(univ:o)⊆S∪S.image cq:=by{intro v _;rcases a v with d|e;{exact mem_union_left _ d};{exact mem_union_right _ (_mg.2 ⟨cq v,e,(ii v).2⟩)}};have f:14<=S.card+(S.image cq).card:=(by decide:14<=(univ:o).card).trans ((_cl c).trans (card_union_le _ _));have g:(S.image cq).card<=S.card:=card_image_le;omega
def cK (σ:_ep (O)):Prop:=∀ u v:O,aP (σ u) (σ v)↔aP u v
def rH (v:O):O:=match v.val with|0=>0|1=>1|2=>2|3=>3|4=>4|5=>5|6=>6|7=>7|8=>8|9=>9|10=>10|11=>11|12=>12|_=>13
def qZ (v:O):O:=match v.val with|0=>0|1=>1|2=>2|3=>3|4=>4|5=>5|6=>6|7=>7|8=>8|9=>9|10=>10|11=>11|12=>12|_=>13
def su:_ep (O):=⟨rH,qZ,by decide,V⟩
lemma py:cK su:=by
 intro u v;simp only[<- ae];revert u v;decide +kernel
def rI (v:O):O:=match v.val with|0=>0|1=>1|2=>4|3=>3|4=>2|5=>6|6=>5|7=>7|8=>10|9=>9|10=>8|11=>12|12=>11|_=>13
def q4 (v:O):O:=match v.val with|0=>0|1=>1|2=>4|3=>3|4=>2|5=>6|6=>5|7=>7|8=>10|9=>9|10=>8|11=>12|12=>11|_=>13
def sv:_ep (O):=⟨rI,q4,by decide,V⟩
lemma pz:cK sv:=by
 intro u v;simp only[<- ae];revert u v;decide +kernel
def rJ (v:O):O:=match v.val with|0=>0|1=>1|2=>5|3=>3|4=>6|5=>2|6=>4|7=>7|8=>10|9=>13|10=>8|11=>11|12=>12|_=>9
def q5 (v:O):O:=match v.val with|0=>0|1=>1|2=>5|3=>3|4=>6|5=>2|6=>4|7=>7|8=>10|9=>13|10=>8|11=>11|12=>12|_=>9
def sw:_ep (O):=⟨rJ,q5,by decide,V⟩
lemma pA:cK sw:=by
 intro u v;simp only[<- ae];revert u v;decide +kernel
def rK (v:O):O:=match v.val with|0=>0|1=>1|2=>6|3=>3|4=>5|5=>4|6=>2|7=>7|8=>8|9=>13|10=>10|11=>12|12=>11|_=>9
def q6 (v:O):O:=match v.val with|0=>0|1=>1|2=>6|3=>3|4=>5|5=>4|6=>2|7=>7|8=>8|9=>13|10=>10|11=>12|12=>11|_=>9
def sx:_ep (O):=⟨rK,q6,by decide,V⟩
lemma pB:cK sx:=by
 intro u v;simp only[<- ae];revert u v;decide +kernel
def rL (v:O):O:=match v.val with|0=>0|1=>3|2=>2|3=>1|4=>5|5=>4|6=>6|7=>7|8=>8|9=>11|10=>10|11=>9|12=>13|_=>12
def q7 (v:O):O:=match v.val with|0=>0|1=>3|2=>2|3=>1|4=>5|5=>4|6=>6|7=>7|8=>8|9=>11|10=>10|11=>9|12=>13|_=>12
def sy:_ep (O):=⟨rL,q7,by decide,V⟩
lemma pC:cK sy:=by
 intro u v;simp only[<- ae];revert u v;decide +kernel
def rM (v:O):O:=match v.val with|0=>0|1=>3|2=>4|3=>1|4=>6|5=>2|6=>5|7=>7|8=>10|9=>12|10=>8|11=>9|12=>13|_=>11
def q8 (v:O):O:=match v.val with|0=>0|1=>3|2=>5|3=>1|4=>2|5=>6|6=>4|7=>7|8=>10|9=>11|10=>8|11=>13|12=>9|_=>12
def sz:_ep (O):=⟨rM,q8,by decide,V⟩
lemma pD:cK sz:=by
 intro u v;simp only[<- ae];revert u v;decide +kernel
def rN (v:O):O:=match v.val with|0=>0|1=>3|2=>5|3=>1|4=>2|5=>6|6=>4|7=>7|8=>10|9=>11|10=>8|11=>13|12=>9|_=>12
def q9 (v:O):O:=match v.val with|0=>0|1=>3|2=>4|3=>1|4=>6|5=>2|6=>5|7=>7|8=>10|9=>12|10=>8|11=>9|12=>13|_=>11
def sA:_ep (O):=⟨rN,q9,by decide,V⟩
lemma pE:cK sA:=by
 intro u v;simp only[<- ae];revert u v;decide +kernel
def rO (v:O):O:=match v.val with|0=>0|1=>3|2=>6|3=>1|4=>4|5=>5|6=>2|7=>7|8=>8|9=>12|10=>10|11=>13|12=>9|_=>11
def q_ (v:O):O:=match v.val with|0=>0|1=>3|2=>6|3=>1|4=>4|5=>5|6=>2|7=>7|8=>8|9=>12|10=>10|11=>13|12=>9|_=>11
def sB:_ep (O):=⟨rO,q_,by decide,V⟩
lemma pF:cK sB:=by
 intro u v;simp only[<- ae];revert u v;decide +kernel
def rP (v:O):O:=match v.val with|0=>7|1=>8|2=>9|3=>10|4=>11|5=>12|6=>13|7=>0|8=>1|9=>2|10=>3|11=>4|12=>5|_=>6
def rc (v:O):O:=match v.val with|0=>7|1=>8|2=>9|3=>10|4=>11|5=>12|6=>13|7=>0|8=>1|9=>2|10=>3|11=>4|12=>5|_=>6
def sC:_ep (O):=⟨rP,rc,by decide,V⟩
lemma pG:cK sC:=by
 intro u v;simp only[<- ae];revert u v;decide +kernel
def rQ (v:O):O:=match v.val with|0=>7|1=>8|2=>11|3=>10|4=>9|5=>13|6=>12|7=>0|8=>3|9=>2|10=>1|11=>5|12=>4|_=>6
def rd (v:O):O:=match v.val with|0=>7|1=>10|2=>9|3=>8|4=>12|5=>11|6=>13|7=>0|8=>1|9=>4|10=>3|11=>2|12=>6|_=>5
def sD:_ep (O):=⟨rQ,rd,by decide,V⟩
lemma pH:cK sD:=by
 intro u v;simp only[<- ae];revert u v;decide +kernel
def re (v:O):O:=match v.val with|0=>7|1=>8|2=>12|3=>10|4=>13|5=>9|6=>11|7=>0|8=>3|9=>6|10=>1|11=>4|12=>5|_=>2
def qk (v:O):O:=match v.val with|0=>7|1=>10|2=>13|3=>8|4=>11|5=>12|6=>9|7=>0|8=>1|9=>5|10=>3|11=>6|12=>2|_=>4
def rR:_ep (O):=⟨re,qk,by decide,V⟩
lemma oR:cK rR:=by
 intro u v;simp only[<- ae];revert u v;decide +kernel
def rf (v:O):O:=match v.val with|0=>7|1=>8|2=>13|3=>10|4=>12|5=>11|6=>9|7=>0|8=>1|9=>6|10=>3|11=>5|12=>4|_=>2
def ql (v:O):O:=match v.val with|0=>7|1=>8|2=>13|3=>10|4=>12|5=>11|6=>9|7=>0|8=>1|9=>6|10=>3|11=>5|12=>4|_=>2
def rS:_ep (O):=⟨rf,ql,by decide,V⟩
lemma oS:cK rS:=by
 intro u v;simp only[<- ae];revert u v;decide +kernel
def rg (v:O):O:=match v.val with|0=>7|1=>10|2=>9|3=>8|4=>12|5=>11|6=>13|7=>0|8=>1|9=>4|10=>3|11=>2|12=>6|_=>5
def qm (v:O):O:=match v.val with|0=>7|1=>8|2=>11|3=>10|4=>9|5=>13|6=>12|7=>0|8=>3|9=>2|10=>1|11=>5|12=>4|_=>6
def rT:_ep (O):=⟨rg,qm,by decide,V⟩
lemma oT:cK rT:=by
 intro u v;simp only[<- ae];revert u v;decide +kernel
def rh (v:O):O:=match v.val with|0=>7|1=>10|2=>11|3=>8|4=>13|5=>9|6=>12|7=>0|8=>3|9=>5|10=>1|11=>2|12=>6|_=>4
def qn (v:O):O:=match v.val with|0=>7|1=>10|2=>11|3=>8|4=>13|5=>9|6=>12|7=>0|8=>3|9=>5|10=>1|11=>2|12=>6|_=>4
def rU:_ep (O):=⟨rh,qn,by decide,V⟩
lemma oU:cK rU:=by
 intro u v;simp only[<- ae];revert u v;decide +kernel
def ri (v:O):O:=match v.val with|0=>7|1=>10|2=>12|3=>8|4=>9|5=>13|6=>11|7=>0|8=>3|9=>4|10=>1|11=>6|12=>2|_=>5
def qo (v:O):O:=match v.val with|0=>7|1=>10|2=>12|3=>8|4=>9|5=>13|6=>11|7=>0|8=>3|9=>4|10=>1|11=>6|12=>2|_=>5
def rV:_ep (O):=⟨ri,qo,by decide,V⟩
lemma oV:cK rV:=by
 intro u v;simp only[<- ae];revert u v;decide +kernel
def rj (v:O):O:=match v.val with|0=>7|1=>10|2=>13|3=>8|4=>11|5=>12|6=>9|7=>0|8=>1|9=>5|10=>3|11=>6|12=>2|_=>4
def qp (v:O):O:=match v.val with|0=>7|1=>8|2=>12|3=>10|4=>13|5=>9|6=>11|7=>0|8=>3|9=>6|10=>1|11=>4|12=>5|_=>2
def rW:_ep (O):=⟨rj,qp,by decide,V⟩
lemma oW:cK rW:=by
 intro u v;simp only[<- ae];revert u v;decide +kernel
def bN (k:Fin 16):_ep (O):=match k.val with
 | 0=>su
 | 1=>sv
 | 2=>sw
 | 3=>sx
 | 4=>sy
 | 5=>sz
 | 6=>sA
 | 7=>sB
 | 8=>sC
 | 9=>sD
 | 10=>rR
 | 11=>rS
 | 12=>rT
 | 13=>rU
 | 14=>rV
 | _=>rW
lemma oX (k:Fin 16):cK (bN k):=by
 fin_cases k;{exact py};{exact pz};{exact pA};{exact pB};{exact pC};{exact pD};{exact pE};{exact pF};{exact pG};{exact pH};{exact oR};{exact oS};{exact oT};{exact oU};{exact oV};{exact oW}
def bU (a:Fin 68):o:=match a.val with
 | 0=>({0,1}:o)
 | 1=>({0,2}:o)
 | 2=>({1,2}:o)
 | 3=>({1,3}:o)
 | 4=>({2,4}:o)
 | 5=>({4,5}:o)
 | 6=>({0,7}:o)
 | 7=>({2,7}:o)
 | 8=>({1,8}:o)
 | 9=>({4,8}:o)
 | 10=>({2,9}:o)
 | 11=>({0,1,2}:o)
 | 12=>({0,1,3}:o)
 | 13=>({1,2,3}:o)
 | 14=>({0,2,4}:o)
 | 15=>({1,2,4}:o)
 | 16=>({2,3,4}:o)
 | 17=>({0,4,5}:o)
 | 18=>({1,4,5}:o)
 | 19=>({2,4,5}:o)
 | 20=>({0,2,7}:o)
 | 21=>({2,4,7}:o)
 | 22=>({4,5,7}:o)
 | 23=>({1,3,8}:o)
 | 24=>({1,4,8}:o)
 | 25=>({4,5,8}:o)
 | 26=>({4,7,8}:o)
 | 27=>({0,2,9}:o)
 | 28=>({2,3,9}:o)
 | 29=>({2,4,9}:o)
 | 30=>({0,1,2,3}:o)
 | 31=>({0,1,2,4}:o)
 | 32=>({0,2,3,4}:o)
 | 33=>({1,2,3,4}:o)
 | 34=>({0,1,4,5}:o)
 | 35=>({0,2,4,5}:o)
 | 36=>({1,2,4,5}:o)
 | 37=>({1,3,4,5}:o)
 | 38=>({2,4,5,6}:o)
 | 39=>({0,2,4,7}:o)
 | 40=>({0,4,5,7}:o)
 | 41=>({2,4,5,7}:o)
 | 42=>({1,3,4,8}:o)
 | 43=>({1,4,5,8}:o)
 | 44=>({4,5,7,8}:o)
 | 45=>({0,2,3,9}:o)
 | 46=>({0,2,4,9}:o)
 | 47=>({2,3,4,9}:o)
 | 48=>({0,2,7,9}:o)
 | 49=>({2,4,7,9}:o)
 | 50=>({3,4,8,9}:o)
 | 51=>({1,3,8,10}:o)
 | 52=>({0,1,2,3,4}:o)
 | 53=>({0,1,2,4,5}:o)
 | 54=>({0,1,3,4,5}:o)
 | 55=>({1,2,3,4,5}:o)
 | 56=>({0,2,4,5,6}:o)
 | 57=>({1,2,4,5,6}:o)
 | 58=>({0,2,4,5,7}:o)
 | 59=>({2,4,5,6,7}:o)
 | 60=>({1,3,4,5,8}:o)
 | 61=>({0,2,3,4,9}:o)
 | 62=>({0,2,4,7,9}:o)
 | 63=>({0,1,2,3,4,5}:o)
 | 64=>({0,1,2,4,5,6}:o)
 | 65=>({1,2,3,4,5,6}:o)
 | 66=>({0,2,4,5,6,7}:o)
 | _=>({0,1,2,3,4,5,6}:o)
def pI (a:Fin 68):ℕ:=match a.val with
 | 0=>3
 | 1=>5
 | 2=>6
 | 3=>10
 | 4=>20
 | 5=>48
 | 6=>129
 | 7=>132
 | 8=>258
 | 9=>272
 | 10=>516
 | 11=>7
 | 12=>11
 | 13=>14
 | 14=>21
 | 15=>22
 | 16=>28
 | 17=>49
 | 18=>50
 | 19=>52
 | 20=>133
 | 21=>148
 | 22=>176
 | 23=>266
 | 24=>274
 | 25=>304
 | 26=>400
 | 27=>517
 | 28=>524
 | 29=>532
 | 30=>15
 | 31=>23
 | 32=>29
 | 33=>30
 | 34=>51
 | 35=>53
 | 36=>54
 | 37=>58
 | 38=>116
 | 39=>149
 | 40=>177
 | 41=>180
 | 42=>282
 | 43=>306
 | 44=>432
 | 45=>525
 | 46=>533
 | 47=>540
 | 48=>645
 | 49=>660
 | 50=>792
 | 51=>1290
 | 52=>31
 | 53=>55
 | 54=>59
 | 55=>62
 | 56=>117
 | 57=>118
 | 58=>181
 | 59=>244
 | 60=>314
 | 61=>541
 | 62=>661
 | 63=>63
 | 64=>119
 | 65=>126
 | 66=>245
 | _=>127
def d4:Finset (o):=univ.image bU
lemma fP {R:o} (h:R∈d4):∃ a:Fin 68,bU a=R:=by
 obtain⟨a,-,rfl⟩:=_mg.1 h;exact⟨a,rfl⟩
def bZ (S:o):ℕ:=(if (0:O)∈S then 2 ^ 0 else 0)||| (if (1:O)∈S then 2 ^ 1 else 0)||| (if (2:O)∈S then 2 ^ 2 else 0)||| (if (3:O)∈S then 2 ^ 3 else 0)||| (if (4:O)∈S then 2 ^ 4 else 0)||| (if (5:O)∈S then 2 ^ 5 else 0)||| (if (6:O)∈S then 2 ^ 6 else 0)||| (if (7:O)∈S then 2 ^ 7 else 0)||| (if (8:O)∈S then 2 ^ 8 else 0)||| (if (9:O)∈S then 2 ^ 9 else 0)||| (if (10:O)∈S then 2 ^ 10 else 0)||| (if (11:O)∈S then 2 ^ 11 else 0)||| (if (12:O)∈S then 2 ^ 12 else 0)||| (if (13:O)∈S then 2 ^ 13 else 0)
lemma gg (p:Prop) [Decidable p] (k b:ℕ):(if p then 2 ^ k else 0).testBit b=(decide (k=b)&&decide p):=by
 split_ifs with a <;> simp[Nat.testBit_two_pow,a]
lemma bC (S:o) (i:O):(bZ S).testBit i.val=decide (i∈S):=by
 fin_cases i <;>
  (simp only[bZ,Nat.testBit_or,gg];simp)
lemma jR (p:Prop) [Decidable p] (k:ℕ) (a:k<14):(if p then 2 ^ k else 0)<2 ^ 14:=by
 split_ifs;{exact Nat.pow_lt_pow_right (by omega) a};{omega}
lemma mB (S:o):bZ S<16384:=by
 change bZ S<2 ^ 14;unfold bZ;repeat (apply Nat.or_lt_two_pow)
 all_goals exact jR _ _ (by omega)
lemma oY {S T:o} (h:bZ S=bZ T):S=T:=by
 ext i;have a:=congrArg (fun m=>m.testBit i.val) h;rw[bC,bC] at a;simpa using a
lemma pJ:∀ a:Fin 68,bZ (bU a)=pI a:=by
 decide +kernel
def bW (m:ℕ):Option (Fin 68):=match m with
 | 3=>some ⟨0,V⟩
 | 5=>some ⟨1,V⟩
 | 6=>some ⟨2,V⟩
 | 10=>some ⟨3,V⟩
 | 20=>some ⟨4,V⟩
 | 48=>some ⟨5,V⟩
 | 129=>some ⟨6,V⟩
 | 132=>some ⟨7,V⟩
 | 258=>some ⟨8,V⟩
 | 272=>some ⟨9,V⟩
 | 516=>some ⟨10,V⟩
 | 7=>some ⟨11,V⟩
 | 11=>some ⟨12,V⟩
 | 14=>some ⟨13,V⟩
 | 21=>some ⟨14,V⟩
 | 22=>some ⟨15,V⟩
 | 28=>some ⟨16,V⟩
 | 49=>some ⟨17,V⟩
 | 50=>some ⟨18,V⟩
 | 52=>some ⟨19,V⟩
 | 133=>some ⟨20,V⟩
 | 148=>some ⟨21,V⟩
 | 176=>some ⟨22,V⟩
 | 266=>some ⟨23,V⟩
 | 274=>some ⟨24,V⟩
 | 304=>some ⟨25,V⟩
 | 400=>some ⟨26,V⟩
 | 517=>some ⟨27,V⟩
 | 524=>some ⟨28,V⟩
 | 532=>some ⟨29,V⟩
 | 15=>some ⟨30,V⟩
 | 23=>some ⟨31,V⟩
 | 29=>some ⟨32,V⟩
 | 30=>some ⟨33,V⟩
 | 51=>some ⟨34,V⟩
 | 53=>some ⟨35,V⟩
 | 54=>some ⟨36,V⟩
 | 58=>some ⟨37,V⟩
 | 116=>some ⟨38,V⟩
 | 149=>some ⟨39,V⟩
 | 177=>some ⟨40,V⟩
 | 180=>some ⟨41,V⟩
 | 282=>some ⟨42,V⟩
 | 306=>some ⟨43,V⟩
 | 432=>some ⟨44,V⟩
 | 525=>some ⟨45,V⟩
 | 533=>some ⟨46,V⟩
 | 540=>some ⟨47,V⟩
 | 645=>some ⟨48,V⟩
 | 660=>some ⟨49,V⟩
 | 792=>some ⟨50,V⟩
 | 1290=>some ⟨51,V⟩
 | 31=>some ⟨52,V⟩
 | 55=>some ⟨53,V⟩
 | 59=>some ⟨54,V⟩
 | 62=>some ⟨55,V⟩
 | 117=>some ⟨56,V⟩
 | 118=>some ⟨57,V⟩
 | 181=>some ⟨58,V⟩
 | 244=>some ⟨59,V⟩
 | 314=>some ⟨60,V⟩
 | 541=>some ⟨61,V⟩
 | 661=>some ⟨62,V⟩
 | 63=>some ⟨63,V⟩
 | 119=>some ⟨64,V⟩
 | 126=>some ⟨65,V⟩
 | 245=>some ⟨66,V⟩
 | 127=>some ⟨67,V⟩
 | _=>none
lemma lh (m:ℕ) (a:Fin 68) (h:bW m=some a):m=pI a:=by
 unfold bW at h;split at h <;> cases h <;> rfl
def cA (k:Fin 16) (m:ℕ):ℕ:=(if m.testBit 0 then 2 ^ (bN k 0).val else 0)||| (if m.testBit 1 then 2 ^ (bN k 1).val else 0)||| (if m.testBit 2 then 2 ^ (bN k 2).val else 0)||| (if m.testBit 3 then 2 ^ (bN k 3).val else 0)||| (if m.testBit 4 then 2 ^ (bN k 4).val else 0)||| (if m.testBit 5 then 2 ^ (bN k 5).val else 0)||| (if m.testBit 6 then 2 ^ (bN k 6).val else 0)||| (if m.testBit 7 then 2 ^ (bN k 7).val else 0)||| (if m.testBit 8 then 2 ^ (bN k 8).val else 0)||| (if m.testBit 9 then 2 ^ (bN k 9).val else 0)||| (if m.testBit 10 then 2 ^ (bN k 10).val else 0)||| (if m.testBit 11 then 2 ^ (bN k 11).val else 0)||| (if m.testBit 12 then 2 ^ (bN k 12).val else 0)||| (if m.testBit 13 then 2 ^ (bN k 13).val else 0)
lemma mi (k:Fin 16) (m:ℕ) (i:O):(cA k m).testBit i.val=m.testBit ((bN k)⁻¹ i).val:=by
 have c:∀(j:O),((bN k j).val=i.val)↔j=(bN k)⁻¹ i:=by{intro j;constructor;{intro h;exact((Equiv.eq_symm_apply (bN k)).2 (_fe h))};{intro h;exact congrArg Fin.val ((Equiv.eq_symm_apply (bN k)).1 h)}};have a:∀(j:O),(if m.testBit j.val=true then 2 ^ (bN k j).val else 0).testBit i.val =(decide (j=(bN k)⁻¹ i)&&m.testBit j.val):=by{intro j;rw[gg,decide_eq_decide.2 (c j)];cases m.testBit j.val <;> rfl}
 have b:(cA k m).testBit i.val =((decide ((0:O)=(bN k)⁻¹ i)&&m.testBit 0)|| (decide ((1:O)=(bN k)⁻¹ i)&&m.testBit 1)|| (decide ((2:O)=(bN k)⁻¹ i)&&m.testBit 2)|| (decide ((3:O)=(bN k)⁻¹ i)&&m.testBit 3)|| (decide ((4:O)=(bN k)⁻¹ i)&&m.testBit 4)|| (decide ((5:O)=(bN k)⁻¹ i)&&m.testBit 5)|| (decide ((6:O)=(bN k)⁻¹ i)&&m.testBit 6)|| (decide ((7:O)=(bN k)⁻¹ i)&&m.testBit 7)|| (decide ((8:O)=(bN k)⁻¹ i)&&m.testBit 8)|| (decide ((9:O)=(bN k)⁻¹ i)&&m.testBit 9)|| (decide ((10:O)=(bN k)⁻¹ i)&&m.testBit 10)|| (decide ((11:O)=(bN k)⁻¹ i)&&m.testBit 11)|| (decide ((12:O)=(bN k)⁻¹ i)&&m.testBit 12)|| (decide ((13:O)=(bN k)⁻¹ i)&&m.testBit 13)):=by{change ((if m.testBit (0:O).val=true then 2 ^ (bN k 0).val else 0)||| (if m.testBit (1:O).val=true then 2 ^ (bN k 1).val else 0)||| (if m.testBit (2:O).val=true then 2 ^ (bN k 2).val else 0)||| (if m.testBit (3:O).val=true then 2 ^ (bN k 3).val else 0)||| (if m.testBit (4:O).val=true then 2 ^ (bN k 4).val else 0)||| (if m.testBit (5:O).val=true then 2 ^ (bN k 5).val else 0)||| (if m.testBit (6:O).val=true then 2 ^ (bN k 6).val else 0)||| (if m.testBit (7:O).val=true then 2 ^ (bN k 7).val else 0)||| (if m.testBit (8:O).val=true then 2 ^ (bN k 8).val else 0)||| (if m.testBit (9:O).val=true then 2 ^ (bN k 9).val else 0)||| (if m.testBit (10:O).val=true then 2 ^ (bN k 10).val else 0)||| (if m.testBit (11:O).val=true then 2 ^ (bN k 11).val else 0)||| (if m.testBit (12:O).val=true then 2 ^ (bN k 12).val else 0)||| (if m.testBit (13:O).val=true then 2 ^ (bN k 13).val else 0)).testBit i.val=_;simp only[Nat.testBit_or,a];rfl};rw[b];generalize (bN k)⁻¹ i=t;fin_cases t <;> simp
lemma li (k:Fin 16) (S:o):bZ (S.image (bN k))=cA k (bZ S):=by
 apply Nat.eq_of_testBit_eq;intro b;by_cases a:b<14
 · have e:(bZ (S.image (bN k))).testBit b =decide ((⟨b,a⟩:O)∈S.image (bN k)):=bC (S.image (bN k)) ⟨b,a⟩
   rw[e];have f:(⟨b,a⟩:O)∈S.image (bN k)↔(bN k)⁻¹ ⟨b,a⟩∈S:=by
    constructor
    · intro c
      obtain⟨x,g,h⟩:=_mg.1 c;have:x=(bN k)⁻¹ ⟨b,a⟩:=by rw[<- h];simp
      exact this▸g
    · intro g;exact _mg.2 ⟨(bN k)⁻¹ ⟨b,a⟩,g,by simp⟩
   have i:(cA k (bZ S)).testBit (⟨b,a⟩:O).val =decide ((bN k)⁻¹ ⟨b,a⟩∈S):=by{rw[mi,bC]};change _=(cA k (bZ S)).testBit (⟨b,a⟩:O).val;rw[i,decide_eq_decide];exact f
 · have e:(bZ (S.image (bN k))).testBit b=false:=Nat.testBit_lt_two_pow ((mB _).trans_le (Nat.pow_le_pow_right (by omega:0<2) (by omega:14<=b)))
   have d:cA k (bZ S)<2 ^ 14:=by
    unfold cA;repeat (apply Nat.or_lt_two_pow)
    all_goals exact jR _ _ (Fin.isLt _)
   have i:(cA k (bZ S)).testBit b=false:=Nat.testBit_lt_two_pow (d.trans_le (Nat.pow_le_pow_right (by omega:0<2) (by omega:14<=b)));rw[e,i]
def jC (m:ℕ):_d:=e_.all (fun e=>!(m.testBit e.1&&m.testBit e.2))
def qq (m:ℕ):ℕ:=(if m.testBit 0 then 1 else 0)+(if m.testBit 1 then 1 else 0) + (if m.testBit 2 then 1 else 0)+(if m.testBit 3 then 1 else 0) + (if m.testBit 4 then 1 else 0)+(if m.testBit 5 then 1 else 0) + (if m.testBit 6 then 1 else 0)+(if m.testBit 7 then 1 else 0) + (if m.testBit 8 then 1 else 0)+(if m.testBit 9 then 1 else 0) + (if m.testBit 10 then 1 else 0)+(if m.testBit 11 then 1 else 0) + (if m.testBit 12 then 1 else 0)+(if m.testBit 13 then 1 else 0)
lemma jX {I:o} (e:dI I):jC (bZ I)=true:=by
 have a:∀ u v:O,aP u v ->!((bZ I).testBit u.val&&(bZ I).testBit v.val)=true:=by{intro u v d;rw[bC,bC];by_cases b:u∈I <;> by_cases c:v∈I;{exact absurd d (e u b v c)};{simp[b,c]};{simp[b,c]};{simp[b,c]}};unfold jC e_;simp only[List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true];exact⟨a 0 8 V,a 0 10 V,a 1 7 V,a 1 9 V,a 1 13 V,a 2 8 V,a 2 12 V,a 2 13 V,a 3 7 V,a 3 11 V,a 3 12 V,a 4 10 V,a 4 11 V,a 4 13 V,a 5 9 V,a 5 10 V,a 5 12 V,a 6 8 V,a 6 9 V,a 6 11 V⟩
lemma nz (I:o):qq (bZ I)=I.card:=by
 have b:I.card=∑ x∈(univ:o),if x∈I then 1 else 0:=by{rw[sum_boole,filter_mem_eq_inter,univ_inter,Nat.cast_id]};have a:(univ:o)={0,1,2,3,4,5,6,7,8,9,10,11,12,13}:=by{decide};rw[b,a];simp only[sum_insert,sum_singleton,_mi,_ms,Fin.reduceEq,or_self,not_false_eq_true];dsimp only[qq];rw[show(bZ I).testBit 0=decide ((0:O)∈I) from bC I 0,show(bZ I).testBit 1=decide ((1:O)∈I) from bC I 1,show(bZ I).testBit 2=decide ((2:O)∈I) from bC I 2,show(bZ I).testBit 3=decide ((3:O)∈I) from bC I 3,show(bZ I).testBit 4=decide ((4:O)∈I) from bC I 4,show(bZ I).testBit 5=decide ((5:O)∈I) from bC I 5,show(bZ I).testBit 6=decide ((6:O)∈I) from bC I 6,show(bZ I).testBit 7=decide ((7:O)∈I) from bC I 7,show(bZ I).testBit 8=decide ((8:O)∈I) from bC I 8,show(bZ I).testBit 9=decide ((9:O)∈I) from bC I 9,show(bZ I).testBit 10=decide ((10:O)∈I) from bC I 10,show(bZ I).testBit 11=decide ((11:O)∈I) from bC I 11,show(bZ I).testBit 12=decide ((12:O)∈I) from bC I 12,show(bZ I).testBit 13=decide ((13:O)∈I) from bC I 13];simp only[decide_eq_true_eq];omega
lemma nA:∀ a b:Fin 128,
 let m:=a.val+128*b.val;jC m=true->2<=qq m ->
 (bW (cA 0 m)).isSome ||
 (bW (cA 1 m)).isSome ||
 (bW (cA 2 m)).isSome ||
 (bW (cA 3 m)).isSome ||
 (bW (cA 4 m)).isSome ||
 (bW (cA 5 m)).isSome ||
 (bW (cA 6 m)).isSome ||
 (bW (cA 7 m)).isSome ||
 (bW (cA 8 m)).isSome ||
 (bW (cA 9 m)).isSome ||
 (bW (cA 10 m)).isSome ||
 (bW (cA 11 m)).isSome ||
 (bW (cA 12 m)).isSome ||
 (bW (cA 13 m)).isSome ||
 (bW (cA 14 m)).isSome ||
 (bW (cA 15 m)).isSome=true:=by
 decide +kernel
lemma lK {I:o} (r:dI I) (e:2<=I.card):∃ σ:_ep (O),cK σ/\I.image σ∈d4:=by
 set m:=bZ I with s;have t:m<16384:=mB I;have f:m % 128<128:=Nat.mod_lt _ (by decide);have g:m / 128<128:=by omega
 have b:m % 128+128*(m / 128)=m:=by omega
 have a:=nA ⟨m % 128,f⟩ ⟨m / 128,g⟩;dsimp only at a;rw[b] at a;have c:=a (jX r) (by rw[nz];exact e);have h:∃ k:Fin 16,(bW (cA k m)).isSome=true:=by{simp only[Bool.or_eq_true] at c;rcases c with (((((((((((((((u|v)|w)|x)|y)|z)|A)|B)|C)|D)|i)|j)|l)|n)|p)|q);{exact⟨0,u⟩};{exact⟨1,v⟩};{exact⟨2,w⟩};{exact⟨3,x⟩};{exact⟨4,y⟩};{exact⟨5,z⟩};{exact⟨6,A⟩};{exact⟨7,B⟩};{exact⟨8,C⟩};{exact⟨9,D⟩};{exact⟨10,i⟩};{exact⟨11,j⟩};{exact⟨12,l⟩};{exact⟨13,n⟩};{exact⟨14,p⟩};{exact⟨15,q⟩}};obtain⟨k,E⟩:=h;obtain⟨idx,d⟩:=Option.isSome_iff_exists.1 E;refine⟨bN k,oX k,_mg.2 ⟨idx,_mv _,?_⟩⟩;apply oY;rw[pJ,li,<-s];exact(lh _ _ d).symm
lemma rk {u v:O} (h:aP u v):h_ (fun i=>decide (i=u)||decide (i=v)):=(ek _).2 ⟨u,v,h,by simp,by simp⟩
abbrev dj (u v:O):Prop:=aP u v\/(u=0/\v=7)\/(u=7/\v=0)
def rX (u:O):ℕ:=([1408,8832,12544,6272,11264,5632,2816,11,69,98,49,88,44,22]:_F ℕ).getD u.val 0
def bK (u v:O):_d:=(rX u).testBit v.val
lemma cW:∀ u v:O,bK u v=true↔dj u v:=by decide +kernel
lemma b3 {u v:O}:bK u v=false↔¬ dj u v:=by
 rw[<- cW];cases bK u v <;> decide
lemma lL {u v:O} (h:dj u v):dj v u:=by
 rcases h with h|⟨rfl,rfl⟩|⟨rfl,rfl⟩;{exact Or.inl h.symm};{exact Or.inr (Or.inr ⟨rfl,rfl⟩)};{exact Or.inr (Or.inl ⟨rfl,rfl⟩)}
lemma ij (u:O):¬ dj u u:=by
 intro h;have:=cW u u |>.2 h;revert u this;decide +kernel
def bX (v:O):o:=univ.filter (fun u=>bK v u=true)
lemma cL {i a:O}:a∈bX i↔dj i a:=by
 simp only[bX,_mf,_mv,true_and,cW]
lemma nC:∀ v:O,(bX v).card=3:=by decide +kernel
lemma nD:∀ u v:O,u≠v->(bX u∩bX v).card<=1:=by decide +kernel
lemma fQ (i:O):aD i⊆bX i:=fun a b=>
 cL.2 (Or.inl (cn.1 b))
lemma dO (i j:O) (a:i≠j) (P:o):(bX i∩(bX j∩P)).card<=1:=by
 refine(_cl (fun x b=>?_)).trans (nD i j a);rw[_mn,_mn] at b;exact _mn.2 ⟨b.1,b.2.1⟩
lemma lM:∀ u v:O,u≠v->∃ z:O,dj u z/\¬ dj v z:=by
 have h:∀ u v:O,u≠v->∃ z:O,bK u z=true/\bK v z=false:=by{decide +kernel};intro u v a;obtain⟨z,b,c⟩:=h u v a;exact⟨z,(cW u z).1 b,b3.1 c⟩
lemma qr:∀ u v:O,∃ a,bK u a=true/\a≠v:=by decide +kernel
lemma nE:bJ dj:=⟨fun _ _=>lL,ij,lM,fun u v=>
 let ⟨a,b,c⟩:=qr u v;⟨a,(cW u a).1 b,c⟩⟩
def bx (x:O->_d):Prop:=∃ u v:O,dj u v/\x u=true/\x v=true
lemma oa:¬ bx (fun _=>false):=by
 rintro⟨u,v,-,h,-⟩;exact _fnt h
lemma kv (v:O):¬ bx (fun i=>decide (i=v)):=by
 rintro⟨a,b,c,d,e⟩;simp only[decide_eq_true_eq] at d e;subst d;subst e;exact ij _ c
abbrev eW:O->O->Prop:=fun u v=>aP u v
lemma gp:∀ u v:O,∃ a,ac u a=true/\a≠v:=by decide +kernel
lemma bs:bJ eW:=⟨fun _ _=>bm,dx,fun u v b=>dU u v b,fun u v=>
 let ⟨a,c,d⟩:=gp u v
 ⟨a,(ae u a).1 c,d⟩⟩
def Umbrella (D:Dag):Prop:=sem_Umbrella 14 eW dj D
def ar (D:Dag):Prop:=Umbrella D
lemma ob (σ:_ep (O)) (hσ:cK σ):(σ 0=0/\σ 7=7)\/(σ 0=7/\σ 7=0):=by
 have f:∀ u:O,az (σ u)=(az u).image σ:=by
  intro u;ext w;simp only[az,_mf,_mv,true_and,ae,_mg];constructor
  · intro h;refine⟨σ.symm w,?_,σ.apply_symm_apply w⟩
    exact(hσ u (σ.symm w)).1 (by simpa using h)
  · rintro⟨a,i,rfl⟩;exact(hσ u a).2 i
 have c:∀ u:O,(az (σ u)).card=(az u).card:=by{intro u;rw[f u,_cii _ σ.injective]};have b:∀ w:O,(az w).card=2↔w=0\/w=7:=by decide +kernel
 have d:=(b (σ 0)).1 (by rw[c 0];decide);have e:=(b (σ 7)).1 (by rw[c 7];decide);have g:σ 0≠σ 7:=fun j=>absurd (σ.injective j) V;rcases d with d|d <;> rcases e with e|e;{exfalso;exact g (d.trans e.symm)};{exact Or.inl ⟨d,e⟩};{exact Or.inr ⟨d,e⟩};{exfalso;exact g (d.trans e.symm)}
lemma qs (σ:_ep (O)) (hσ:cK σ):∀ u v:O,dj u v↔dj (σ u) (σ v):=by
 intro u v;rcases ob σ hσ with ⟨a,b⟩|⟨a,b⟩
 · constructor
   · rintro (h|⟨rfl,rfl⟩|⟨rfl,rfl⟩)
     · exact Or.inl ((hσ u v).2 h)
     · exact Or.inr (Or.inl ⟨a,b⟩)
     · exact Or.inr (Or.inr ⟨b,a⟩)
   · rintro (h|⟨c,d⟩|⟨c,d⟩)
     · exact Or.inl ((hσ u v).1 h)
     · exact Or.inr (Or.inl ⟨σ.injective (c.trans a.symm),σ.injective (d.trans b.symm)⟩)
     · exact Or.inr (Or.inr ⟨σ.injective (c.trans b.symm),σ.injective (d.trans a.symm)⟩)
 · constructor
   · rintro (h|⟨rfl,rfl⟩|⟨rfl,rfl⟩)
     · exact Or.inl ((hσ u v).2 h)
     · exact Or.inr (Or.inr ⟨a,b⟩)
     · exact Or.inr (Or.inl ⟨b,a⟩)
   · rintro (h|⟨c,d⟩|⟨c,d⟩)
     · exact Or.inl ((hσ u v).1 h)
     · exact Or.inr (Or.inr ⟨σ.injective (c.trans b.symm),σ.injective (d.trans a.symm)⟩)
     · exact Or.inr (Or.inl ⟨σ.injective (c.trans a.symm),σ.injective (d.trans b.symm)⟩)
lemma oc {D:Dag} (a:ar D):ag 14 D (bH 14 D)=∅:=cs bs a
lemma oZ (σ:_ep (O)) (hσ:cK σ) {D:Dag} (h:ai 14 D) (b:ar D):ai 14 (bo σ D)/\ar (bo σ D) /\(bo σ D).length=D.length /\ap 14 (bo σ D)=ap 14 D /\bd 14 (bo σ D)=bd 14 D/\bL 14 (bo σ D)=bL 14 D /\al 14 (bo σ D)=(al 14 D).image σ /\aa 14 (bo σ D)=(aa 14 D).image σ:=by
 refine⟨fd σ h,?_,cc σ D,eJ σ D,j8 σ h.1,j9 σ h.1,fZ σ h.1,ep σ h.1⟩;refine⟨nE,fun _ _ a=>Or.inl a,?_,?_,?_⟩
 · rintro x ⟨u,v,a,c,d⟩
   rw[fI σ h.1 h.2.2 x];exact b.2.2.1 _ ⟨σ.symm u,σ.symm v,(hσ _ _).1 (by simpa using a),by simpa using c,by simpa using d⟩
 · intro x e
   rw[fI σ h.1 h.2.2 x] at e;obtain⟨u,v,a,c,d⟩:=b.2.2.2.1 _ e;exact⟨σ u,σ v,(qs σ hσ u v).1 a,c,d⟩
 · intro u v a
   rw[fI σ h.1 h.2.2];have f:(fun i=>b4 u v (σ i))=b4 (σ.symm u) (σ.symm v):=by{ext i;simp only[b4,σ.apply_eq_iff_eq_symm_apply]};rw[f];exact b.2.2.2.2 (σ.symm u) (σ.symm v) (fun g=>a (by simpa using (hσ _ _).2 g))
lemma kw (D:Dag):eE (al 14 D)↔dI (aa 14 D):=by
 constructor
 · intro b u e v f a
   have g:=_md.mp e;have h:=_md.mp f;exact(b u v a).elim g.2 h.2
 · intro c u v a
   by_contra d;push Not at d;exact c u (_md.mpr ⟨_mv _,d.1⟩) v (_md.mpr ⟨_mv _,d.2⟩) a
lemma rl {D:Dag} (h:ai 14 D) (f:ar D) (b:dI (aa 14 D)) (d:2<=(aa 14 D).card):∃ D':Dag,ai 14 D'/\ar D'/\D'.length=D.length /\ap 14 D'=ap 14 D /\bd 14 D'=bd 14 D/\bL 14 D'=bL 14 D /\(aa 14 D').card=(aa 14 D).card /\aa 14 D'∈d4:=by
 obtain⟨σ,hσ,c⟩:=lK b d;obtain⟨g,i,j,k,l,m,-,e⟩:=oZ σ hσ h f;refine⟨bo σ D,g,i,j,k,l,m,?_,e▸c⟩;rw[e,_cii _ σ.injective]
lemma mC {D:Dag} (h:ai 14 D) (a:D.length<=25):ap 14 D=D.length - 13/\ap 14 D<=12:=by
 have:=iC h;exact⟨by omega,by omega⟩
lemma od {D:Dag} (h:ai 14 D) (a:D.length<=25) (b:O->ℕ) (d:aM 14 D b) (c:eE (al 14 D)):7<=(al 14 D).card/\(al 14 D).card<=bd 14 D /\bd 14 D<=12/\ap 14 D<=12:=by
 have e:=eV c;have f:=dX h.1 b d;have i:=dC 14 D;have g:=(mC h a).2;exact⟨e,f,by omega,g⟩
lemma il {D:Dag} (h:ai 14 D) (a:D.length<=25) (b:O->ℕ) (d:aM 14 D b) (c:eE (al 14 D)):(aa 14 D).Nonempty/\2<=(aa 14 D).card/\(aa 14 D).card<=7:=by
 obtain⟨f,g,i,e⟩:=od h a b d c;have j:=aV 14 D;exact⟨_cp.1 (by omega),by omega,by omega⟩
lemma bF {D:Dag} (a:ar D):sem_Umbrella 14 eW dj D:=a
lemma bu {D:Dag} (h:ai 14 D) (a:ar D):∃ b:O->ℕ,aM 14 D b:=dK bs h.1 a
lemma fp {D:Dag} (h:ai 14 D) (b:ar D):eE (al 14 D):=fun _ _ a=>fu bs h b a
lemma nF (C:Circuit) (e:Monotone2 C) (f:∀ x:O->_d,h_ x->C.eval (_of x)=true) (d:∀ x:O->_d,C.eval (_of x)=true->bx x) (g:∀ u v:O,¬ eW u v->C.eval (_of (b4 u v))=false):∃ D:Dag,ai 14 D/\D.length<=C.size/\ar D:=by
 have r:aP (0:O) 8:=V
 obtain⟨D,t,l,c⟩:=fV (n:=14) C e (by
  intro b;cases b
  · refine⟨b4 0 8,fun p=>?_⟩
    have m:=f _ (rk r);change C.eval (_of (b4 0 8))=true at m;rw[m] at p;exact Bool.noConfusion p
  · refine⟨fun _=>false,fun p=>oa (d _ p)⟩)
  (by
   intro i
   refine⟨fun k=>decide (k=i),fun h=>kv i (d _ (by rw[h];simp))⟩)
  (by
   intro i;obtain⟨a,w,-⟩:=bs.2.2.2 i i;refine⟨cl a,bB i (cl a),dd i _,fun s=>?_⟩;have m:C.eval (_of (bB i (cl a)))=true:=f _ ((ek _).2 ⟨i,a,w,dm i _,by simp[bB,cl]⟩);rw[<- s] at m
   exact kv a (d _ m))
 refine⟨D,t,l,nE,fun _ _ j=>Or.inl j,fun x q=>by rw[c x];exact f x ((ek x).2 q),fun x q=>by rw[c x] at q;exact d x q,fun u v j=>by rw[c];exact g u v j⟩
lemma mU (C:Circuit) (d:Monotone2 C) (l:∀ x:O->_d,h_ x->C.eval (_of x)=true) (m:∀ x:O->_d,C.eval (_of x)=true->bx x) (e:∀ u v:O,¬ eW u v->C.eval (_of (b4 u v))=false) (n:C.size<=25):∃ D:Dag,ai 14 D/\ar D/\D.length<=25 /\ap 14 D<=12/\2<=(aa 14 D).card/\aa 14 D∈d4:=by
 obtain⟨D0,k,p,f⟩:=nF C d l m e;have h:D0.length<=25:=by omega
 obtain⟨b,s⟩:=bu k f;have c:=fp k f;obtain⟨-,i,-⟩:=il k h b s c;obtain⟨D,j,q,w,-,-,-,-,t⟩:=rl k f ((kw D0).mp c) i;have h':D.length<=25:=by omega
 obtain⟨b',s'⟩:=bu j q;obtain⟨-,i',-⟩:=il j h' b' s' (fp j q);exact⟨D,j,q,h',(mC j h').2,i',t⟩
def i_:o:={7,8,9,10,11,12,13}
def cw (k:Fin 7):O:=⟨k.val,by omega⟩
lemma dP:Function.Injective cw:=fun a b h=>_fe (by
 have:=congrArg Fin.val h;simpa[cw] using this)
def f6 (m:Fin 128):Finset (Fin 7):=univ.filter (fun k:Fin 7=>m.val.testBit k.val)
lemma mj (S:Finset (Fin 7)):∃ m:Fin 128,f6 m=S:=by
 classical
 induction S using Finset.induction_on with
 | empty=>exact⟨0,by ext k;simp[f6]⟩
 | insert a s _ ih=>
  obtain⟨m,d⟩:=ih;have b:2 ^ a.val<2 ^ 7:=Nat.pow_lt_pow_right (by omega) a.isLt;refine⟨⟨m.val ||| 2 ^ a.val,Nat.or_lt_two_pow m.isLt b⟩,?_⟩;ext k;simp only[f6,_mf,_mv,true_and,Nat.testBit_or,Nat.testBit_two_pow,Bool.or_eq_true,decide_eq_true_eq,_mi];have c:m.val.testBit k.val=true↔k∈s:=by{have:=Finset.ext_iff.1 d k;simpa[f6] using this};rw[c,Fin.ext_iff];tauto
lemma f8:∀ a b:O,bK a b=true ->decide (a.val<7)≠decide (b.val<7):=by decide +kernel
lemma lN:∀ a∈i_,∀ b∈i_,¬ dj a b:=by
 intro a f b g c;have d:=f8 a b ((cW a b).2 c);have e:∀ x∈i_,decide (x.val<7)=false:=by decide +kernel
 rw[e a f,e b g] at d;exact d rfl
lemma nG:∀ j i:Fin 7,j≠i ->∃ a:O,a≠7/\ac (cw j) a=true/\ac (cw i) a=false:=by
 decide +kernel
lemma m4:bX 0=insert 7 (aD 0):=by decide +kernel
lemma ml {D:Dag} (h:ai 14 D) (H:ar D) (P:o) (I:∀ a∈P,∀ b∈P,¬ dj a b) (J:o) (k:∀ i∈J,i.val<7/\i∈aa 14 D/\aD i⊆P /\¬ aQ 14 D P (aD i)/\(i=0->¬ aQ 14 D P (bX 0))):J.card<=bL 14 D:=by
 classical
 have K:=bs;let Q:O->o:=fun i=>if i=0 then P.erase 7 else P;have l:∀ i,Q i⊆P:=fun i=>by{by_cases f:i=0;{simp only[Q,f,↓reduceIte];exact erase_subset _ _};{simp only[Q,f,↓reduceIte];exact Subset.refl _}};have A:∀ i a b,a∈Q i->b∈Q i->¬ dj a b:=fun i a b t n=>I a (l i t) b (l i n);have p:∀ i∈J,∀ a∈Q i,dj i a->aP i a:=by{intro i e a t w;rcases w with c|⟨c,z⟩|⟨c,z⟩;{exact c};{exfalso;subst c;dsimp only[Q] at t;rw[if_pos rfl] at t;exact(_me.1 t).1 z};{exfalso;subst c;exact absurd (k 7 e).1 V}};have r:∀ i∈J,∀ q,(∀ a∈Q i,(a∈ag 14 D q↔aP i a))->False:=by
  intro i e q m;by_cases f:i=0
  · subst f
    by_cases U:(7:O)∈ag 14 D q∩P
    · refine(k 0 e).2.2.2.2 rfl ⟨q,?_⟩
      rw[m4];ext a;rw[_mn,_mi,cn];by_cases d:a=7;{subst d;simp[_mn.1 U]}
      · constructor
        · rintro⟨c,z⟩
          exact Or.inr ((m a (_me.2 ⟨d,z⟩)).1 c)
        · rintro (rfl|c)
          · exact absurd rfl d
          · have g:=(k 0 e).2.2.1 (cn.2 c)
            exact⟨(m a (_me.2 ⟨d,g⟩)).2 c,g⟩
    · refine(k 0 e).2.2.2.1 ⟨q,?_⟩
      ext a;rw[_mn,cn];by_cases d:a=7
      · subst d;constructor
        · intro c;exact absurd (_mn.2 c) U
        · intro c;exfalso;exact(by decide:¬ aP 0 7) c
      · constructor
        · rintro⟨c,z⟩;exact(m a (_me.2 ⟨d,z⟩)).1 c
        · intro c
          have g:=(k 0 e).2.2.1 (cn.2 c);exact⟨(m a (_me.2 ⟨d,g⟩)).2 c,g⟩
  · refine(k i e).2.2.2.1 ⟨q,?_⟩
    ext a;rw[_mn,cn];have L:Q i=P:=if_neg f;rw[L] at m;exact⟨fun c=>(m a c.2).1 c.1,fun c=>⟨(m a ((k i e).2.2.1 (cn.2 c))).2 c,(k i e).2.2.1 (cn.2 c)⟩⟩
 have n:∀ i∈J,∃ b,bz 14 D i.val b/\2<=aF D b/\ag 14 D b=∅:=by
  intro i e;rcases iI K h H (k i e).2.1 with M|n
  · obtain⟨j,s,-,-,-,m⟩:=jL K h.1 H (Q i) (fun a t b n=>A i a b t n) (p i e) M
    exact absurd m (r i e _)
  · exact n
 choose! br y using n;have B:Set.InjOn br J:=by{intro i e j N R;by_contra S;let W:Fin 7:=⟨i.val,(k i e).1⟩;let X:Fin 7:=⟨j.val,(k j N).1⟩;have C:X≠W:=fun Y=>S (_fe (congrArg (fun x:Fin 7=>x.val) Y.symm));obtain⟨a,d,E,F⟩:=nG X W C;have G:aP j a:=(ae _ _).1 E;have w:¬ aP i a:=aH.1 F;have g:a∈P:=(k j N).2.2.1 (cn.2 G);have T:a∈Q i:=by{by_cases f:i=0;{simp only[Q,f,↓reduceIte];exact _me.2 ⟨d,g⟩};{simp only[Q,f,↓reduceIte];exact g}};have c:=iJ K h.1 H (Q i) (fun u Z v hv=>A i u v Z hv) (p i e) (y i e).1 (R▸ds h.1 (y j N).1) ⟨a,T,G,w⟩;obtain⟨_,_,-,-,-,-,m⟩:=c;exact r i e _ m};calc J.card=(J.image br).card:=(_cij B).symm
  _<=bL 14 D:=ph h.1 (J.image br) (fun b n=>by
   obtain⟨i,e,rfl⟩:=_mg.1 n
   exact(y i e).2)
lemma qt {D:Dag} (h:ai 14 D) (hD:ar D) (P:o) (hPi:∀ a∈P,∀ b∈P,¬ dj a b) (hP7:P.card<=7) (hPe:P⊆al 14 D) (Oc3 Oc2 Ct Iin:o) (U:∀ i∈Oc3,bX i⊆P/\aQ 14 D P (bX i)) (W:∀ i∈Oc2,i=0/\(0:O)∉Oc3/\aD 0⊆P/\aQ 14 D P (aD 0)) (t:∀ c∈Ct,c∉Oc3/\c∉Oc2 /\(bX c⊆P->¬ aQ 14 D P (bX c)) /\(c=0->aD 0⊆P->¬ aQ 14 D P (aD 0))) (d:∀ i∈Iin,i∈aa 14 D/\aD i⊆P/\i.val<7):2*Oc3.card+Oc2.card+Iin.card+(Ct.biUnion (fun c=>aD c∩P)).card + (al 14 D).card<=2*P.card+bd 14 D:=by
 classical
 have hG:=bs;obtain⟨b,Q⟩:=bu h hD;obtain⟨pos,u⟩:=bQ hG h hD;have F:Set.InjOn pos Iin:=fun i m j R g=>
  u.2 i (d i m).1 j (d j R).1 g
 have hE:∀ e∈Iin.image pos,e∈aE 14 D (ao 14 D P):=by{intro e he;obtain⟨i,m,rfl⟩:=_mg.1 he;obtain⟨R,Y,hnb,-⟩:=u.1 i (d i m).1;have hdeg:=gf i;have v:(aD i).Nonempty:=_cp.1 (by dsimp[aD];omega);obtain⟨a,k⟩:=v;rw[aE,_mf];refine⟨mem_product.2 ⟨mem_range.2 R,_mv _⟩,cC.2 ⟨a,_mn.2 ⟨hnb a (cn.1 k),(d i m).2.1 k⟩⟩,?_⟩;rw[cC,Y,empty_inter];exact not_nonempty_empty};have Z:∀ f∈Ct.biUnion (fun c=>aD c∩P),∃ c∈Ct,f∈aD c∩P:=fun f A=>mem_biUnion.1 A;choose! ct B using Z;have G:Function.Injective bX:=fun i j g=>by{by_contra v;obtain⟨z,hiz,hjz⟩:=lM i j v;have y:z∈bX i:=cL.2 hiz;rw[g,cL] at y;exact hjz y}
 have H:=pY h.1 hP7 (Oc3.image bX) (fun T I=>by
  obtain⟨i,m,rfl⟩:=_mg.1 I
  exact⟨nC i,(U i m).2⟩)
  (fun T I T' I' v=>by
   obtain⟨i,m,rfl⟩:=_mg.1 I;obtain⟨j,R,rfl⟩:=_mg.1 I';have:=dO i j (fun g=>v (g▸rfl)) univ
   simpa using this)
  (Oc2.image aD)
  (fun M hM=>by
   obtain⟨i,m,rfl⟩:=_mg.1 hM;obtain⟨rfl,hn3,-,h0⟩:=W i m;refine⟨by decide,h0,fun T I h3=>?_⟩;obtain⟨j,R,rfl⟩:=_mg.1 I;have g:(0:O)≠j:=fun h=>hn3 (h▸R);have h6:=dO 0 j g univ;have h3':aD 0⊆bX 0∩bX j:=subset_inter (fQ 0) h3;have S:=_cl h3';simp only[inter_univ] at h6;have h2:(aD 0).card=2:=V
   omega)
  (Iin.image pos) hE (Ct.biUnion (fun c=>aD c∩P)) (fun f=>bX (ct f)∩P)
  (fun f A=>by
   obtain⟨S,J⟩:=B f A;have C:f∈bX (ct f)∩P:=
    _mn.2 ⟨fQ _ (_mn.1 J).1,(_mn.1 J).2⟩
   refine jM hG h.1 hD (X:=insert (ct f) (P\(bX (ct f)∩P))) inter_subset_right ?_ ?_ (fun a k=>mem_insert_of_mem k) C ⟨ct f,mem_insert_self _ _,bm (cn.1 (_mn.1 J).1)⟩
   · by_cases q:bX (ct f)⊆P
     · rw[inter_eq_left.2 q]
       exact Or.inr ⟨nC (ct f),(t _ S).2.2.1 q⟩
     · have hlt:(bX (ct f)∩P).card<(bX (ct f)).card:=card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨inter_subset_left,fun r=>q (r▸inter_subset_right)⟩)
       have hd3:=nC (ct f);exact Or.inl (by omega)
   · have h8:∀ a∈P\(bX (ct f)∩P),¬ dj (ct f) a:=by
      intro a k h9;rw[_md,_mn,cL] at k;exact k.2 ⟨h9,k.1⟩
     intro a k b Q;rcases _mi.1 k with rfl|k <;> rcases _mi.1 Q with rfl|Q;{exact ij _};{exact h8 b Q};{exact fun hab=>h8 a k (lL hab)}
     · exact hPi a (_md.1 k).1 b (_md.1 Q).1)
  (fun f A T I=>by
   obtain⟨i,m,rfl⟩:=_mg.1 I;have y:=dO i (ct f) (fun g=>(t _ (B f A).1).1 (g▸m)) P
   rwa[inter_comm (bX i)] at y)
  (fun f A M hM=>by
   obtain⟨i,m,rfl⟩:=_mg.1 hM;have g:i≠ct f:=fun g=>(t _ (B f A).1).2.1 (g▸m);have y:=dO i (ct f) g P;refine le_trans (_cl (fun x hx=>?_)) y
   rw[_mn] at hx⊢;exact⟨fQ i hx.2,hx.1⟩)
  (fun e he f A w hw hew=>by
   obtain⟨i,m,rfl⟩:=_mg.1 he;obtain⟨S,-⟩:=B f A;have s:aD i⊆ag 14 D (aw D (pos i))∩P:=fun a k=>
    _mn.2 ⟨(u.1 i (d i m).1).2.2.1 a (cn.1 k),(d i m).2.1 k⟩
   have l:ag 14 D (aw D (pos i))∩P⊆bX (ct f)∩P:=hew▸hw.2.2.2.2.2.1;by_cases n:ct f=i
   · rw[n] at l
     by_cases hg:i=0
     · subst hg
       by_cases h7:(7:O)∈ag 14 D (aw D (pos 0))∩P
       · have K:bX 0⊆P:=by
          intro a k;rw[m4,_mi] at k;rcases k with rfl|k;{exact(_mn.1 h7).2};{exact(d 0 m).2.1 k}
         have r:ag 14 D (aw D (pos 0))∩P=bX 0:=by{refine Subset.antisymm (l.trans inter_subset_left) ?_;intro a k;rw[m4,_mi] at k;rcases k with rfl|k;{exact h7};{exact s k}};exact(t _ S).2.2.1 (n▸K) ⟨aw D (pos 0),n▸r⟩
       · have r:ag 14 D (aw D (pos 0))∩P=aD 0:=by
          refine Subset.antisymm ?_ s;intro a k;have k':=(_mn.1 (l k)).1;rw[m4,_mi] at k';rcases k' with rfl|k';{exact absurd k h7};{exact k'}
         exact(t _ S).2.2.2 n (n▸(d 0 m).2.1) ⟨aw D (pos 0),r⟩
     · have L:bX i=aD i:=by
        ext a;rw[cL,cn];constructor
        · rintro (y|⟨y,_⟩|⟨h2,_⟩)
          · exact y
          · exact absurd y hg
          · exfalso;rw[h2] at m;exact absurd (d 7 m).2.2 V
        · exact Or.inl
       rw[L,inter_eq_left.2 (d i m).2.1] at l;have r:ag 14 D (aw D (pos i))∩P=bX i:=by{rw[L];exact Subset.antisymm l s};exact(t _ S).2.2.1 (n▸L▸(d i m).2.1) ⟨aw D (pos i),n▸r⟩
   · have h6:=dO i (ct f) (Ne.symm n) P
     have h3':aD i⊆bX i∩(bX (ct f)∩P):=subset_inter (fQ i) (s.trans l);have N:=_cl h3'
     rcases gf i with hd|hd <;> (rw[ie] at N;omega))
 have h4:=co h P (by rw[oc hD];simp);have h5:=cZ h.1 b Q P;rw[inter_eq_left.2 hPe] at h5
 rw[_cii _ G,
  _cii _ (fun i j g=>pw g),
  _cij F] at H
 omega
lemma jS {D:Dag} (h:ai 14 D) (hD:ar D):∃(m:Fin 128) (d:_d),
 let I:=aa 14 D;let P:=i_\I;let f:=f6 m;let g:=if d&&!decide ((0:Fin 7)∈f) then ({0}:Finset (Fin 7)) else ∅;let F:=f∪g;let L:=(univ:Finset (Fin 7))\F;let u:=univ.filter (fun k:Fin 7=>cw k∈I/\az (cw k)⊆P)
 (∀ k∈f,bX (cw k)⊆P)/\(d=true->az 0⊆P) /\
 2*f.card+g.card+u.card+(L.biUnion (fun k=>az (cw k)∩P)).card + (14 - I.card)<=2*P.card+bd 14 D /\
 (u\F).card<=bL 14 D:=by
 classical
 set I:=aa 14 D with X;set P:=i_\I;have G:P⊆i_:=sdiff_subset;have Q:∀ a∈P,∀ b∈P,¬ dj a b:=fun a M b hb=>lN a (G M) b (G hb);have Y:P.card<=7:=(_cl G).trans V;have Z:P⊆al 14 D:=fun a M=>by{by_contra h0;exact(_md.1 M).2 (aN.2 h0)}
 let f:=univ.filter (fun k:Fin 7=>
  bX (cw k)⊆P/\aQ 14 D P (bX (cw k)))
 obtain⟨m,hm⟩:=mj f;let d:_d:=decide (az 0⊆P/\aQ 14 D P (aD 0));refine⟨m,d,?_⟩;dsimp only;rw[hm];let g:=if d&&!decide ((0:Fin 7)∈f) then ({0}:Finset (Fin 7)) else ∅;let F:=f∪g;let L:=(univ:Finset (Fin 7))\F;let u:=univ.filter (fun k:Fin 7=>cw k∈I/\az (cw k)⊆P);have p:cw 0=0:=rfl
 have y:=qt h hD P Q Y Z (f.image cw) (g.image cw) (L.image cw) (u.image cw) (fun i H=>by
  obtain⟨k,l,rfl⟩:=_mg.1 H;have R:=(_mf.1 l).2
  exact⟨R.1,R.2⟩)
  (fun i H=>by
   obtain⟨k,l,rfl⟩:=_mg.1 H;dsimp[g] at l;by_cases N:d&&!decide ((0:Fin 7)∈f)
   · rw[if_pos N,_ms] at l;subst l
     simp only[Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not] at N;obtain⟨J,h4⟩:=N;simp only[d,decide_eq_true_eq] at J;refine⟨rfl,fun K=>h4 ?_,J.1,J.2⟩;obtain⟨k',l',z⟩:=_mg.1 K;rwa[<- dP (z.trans p.symm)]
   · rw[if_neg N] at l;exact absurd l (notMem_empty _))
  (fun c N=>by
   obtain⟨k,l,rfl⟩:=_mg.1 N;have S:k∉F:=(_md.1 l).2;have j:k∉f:=fun K=>S (mem_union_left _ K);have t:k∉g:=fun T=>S (mem_union_right _ T);refine⟨fun K=>?_,fun T=>?_,fun A e=>?_,fun v A e=>?_⟩
   · obtain⟨k',l',z⟩:=_mg.1 K
     exact j (dP z▸l')
   · obtain⟨k',l',z⟩:=_mg.1 T
     exact t (dP z▸l')
   · exact j (_mf.2 ⟨_mv k,A,e⟩)
   · have v':k=0:=dP v
     subst v';have n:d=true:=by{simp only[d,decide_eq_true_eq];exact⟨ie 0▸A,e⟩}
     exact t (by simp[g,n,j]))
  (fun i H=>by
   obtain⟨k,l,rfl⟩:=_mg.1 H;have q:=(_mf.1 l).2
   exact⟨q.1,ie _▸q.2,k.isLt⟩)
 have r:=ml h hD P Q ((u\F).image cw) (fun i H=>by
  obtain⟨k,l,rfl⟩:=_mg.1 H;rw[_md] at l;have q:=(_mf.1 l.1).2;have j:k∉f:=fun K=>l.2 (mem_union_left _ K);have t:k∉g:=fun T=>l.2 (mem_union_right _ T);refine⟨k.isLt,q.1,ie _▸q.2,fun e=>?_,fun h5 e=>?_⟩
  · by_cases v:k=0
    · subst v
      have n:d=true:=by{simp only[d,decide_eq_true_eq];exact⟨p▸q.2,p▸e⟩};exact t (by simp[g,n,j])
    · have W:bX (cw k)=aD (cw k):=by
       ext a;rw[cL,cn];constructor
       · rintro (E|⟨E,_⟩|⟨E,_⟩)
         · exact E
         · exfalso;exact v (dP (E.trans p.symm))
         · exfalso;have h6:(cw k).val<7:=k.isLt;rw[E] at h6;omega
       · exact Or.inl
      exact j (_mf.2 ⟨_mv k,W▸q.2,W▸e⟩)
  · have v:k=0:=dP h5
    subst v
    exact j (_mf.2 ⟨_mv 0,by
     intro a M;obtain⟨w,hw⟩:=e;rw[p,<-hw] at M
     exact(_mn.1 M).2,e⟩))
 rw[_cii _ dP] at r
 rw[_cii _ dP,_cii _ dP,
  _cii _ dP] at y
 have C:((L.image cw).biUnion (fun c=>aD c∩P))=L.biUnion (fun k=>az (cw k)∩P):=by{ext x;simp only[mem_biUnion,_mg,_mn,ie];constructor;{rintro⟨c,⟨k,l,rfl⟩,hx⟩;exact⟨k,l,hx⟩};{rintro⟨k,l,hx⟩;exact⟨cw k,⟨k,l,rfl⟩,hx⟩}};rw[C] at y;simp only[g,F,L,u,P,I] at y r⊢;have hel:=aV 14 D;have s:d=true->az 0⊆i_\aa 14 D:=by{intro E;simp only[d,decide_eq_true_eq] at E;exact E.1};refine⟨fun k l=>(_mf.1 l).2.1,s,?_,r⟩;omega
def aZ (D:Dag) (b:O->ℕ) (x:O):Finset (Σ _:ℕ,ℕ):=(aj 14 D b).filter (fun u=>x∈ag 14 D u.1)
lemma fC {D:Dag} {b:O->ℕ} {u:Σ _:ℕ,ℕ} (a:u∈aj 14 D b) {x:O} (c:x∈ag 14 D u.1):x∈al 14 D:=eX.2 ⟨u.1,by
 have d:=(dW.mp (_mf.mp (_md.mp a).1).1).2
 omega,c⟩
lemma bj {D:Dag} (h:ai 14 D) (a:ar D) (b:O->ℕ) (c:aM 14 D b) (x:O):(af 14 D x).card+(aW 14 D (ao 14 D {x})).card<=2+(aZ D b x).card:=by
 have e:=ez bs h (bF a) b c x;have d:=_cl (inter_subset_left:({x}:o)∩al 14 D⊆{x});rw[_cs] at d;unfold aZ;omega
lemma el {n:ℕ} {D:Dag} (b:au n D) {x:Fin n} {e:ℕ×_d} (c:e∈af n D x):am e∉af n D x:=by
 intro f;obtain⟨g,d,h⟩:=ak.mp c;have d':=(ak.mp f).2.1;apply h;rw[cB b g (cY b c),_mn];obtain⟨j,s⟩:=e;cases s;{exact⟨by simpa[aw] using d,by simpa[aw,am] using d'⟩};{exact⟨by simpa[aw,am] using d',by simpa[aw] using d⟩}
lemma aJ {D:Dag} {pos:O->ℕ×_d} (b:bA 14 eW D pos) {i a:O} (d:i∈aa 14 D) (c:aP i a):pos i∈af 14 D a:=by
 obtain⟨e,f,g,-⟩:=b.1 i d;exact ak.2 ⟨e,g a c,by rw[f];exact notMem_empty a⟩
lemma em {D:Dag} {pos:O->ℕ×_d} (a:bA 14 eW D pos) {i t:O} (b:i∈aa 14 D) (c:am (pos i)∈af 14 D t):t=i:=by
 have:=(ak.1 c).2.1;rw[show aw D (am (pos i))=aw D ((pos i).1,!(pos i).2) from rfl,(a.1 i b).2.2.2] at this;exact _ms.1 this
lemma pK {D:Dag} (h:ai 14 D) (d:ar D) {pos:O->ℕ×_d} (a:bA 14 eW D pos) {i:O} (b:i∈aa 14 D):af 14 D i={am (pos i)}:=by
 obtain⟨e,-,-,-,-,-,f,-⟩:=ci bs h (bF d) b;obtain⟨g,j,-,k⟩:=a.1 i b
 have c:am (pos i)∈af 14 D i:=ak.2 ⟨g,by
  rw[show aw D (am (pos i))=aw D ((pos i).1,!(pos i).2) from rfl,k];exact _mss i,by
  rw[show(am (pos i)).1=(pos i).1 from rfl,j];exact notMem_empty i⟩
 have l:af 14 D i={e}:=f;rw[l] at c⊢;rw[_ms.1 c]
lemma cT {D:Dag} (h:ai 14 D) (d:ar D) (b:bL 14 D=0) {pos:O->ℕ×_d} (a:bA 14 eW D pos) {i v:O} (e:i∈aa 14 D) (c:aP i v) (f:∀ p∈af 14 D v,p.1≠(pos i).1->¬ ag 14 D (aw D (am p))⊆{i}):∀ t,t∈ag 14 D (aw D (pos i))↔aP i t:=by
 have:=oh bs h (bF d) b e (pK h d a e) c f;rwa[aB] at this
lemma d6 {α:Type} [DecidableEq α] {s:Finset α} {a b c:α} (j:a∈s) (k:b∈s) (l:c∈s) (f:a≠b) (g:a≠c) (h:b≠c):3<=s.card:=by
 have d:({a,b,c}:Finset α)⊆s:=by{intro e i;simp only[_mi,_ms] at i;rcases i with rfl|rfl|rfl <;> assumption};have:=_cl d;rwa[_cin (by simp[f,g]),_c2 h] at this
lemma mm {α:Type} [DecidableEq α] {s:Finset α} {a b c d:α} (n:a∈s) (p:b∈s) (q:c∈s) (r:d∈s) (g:a≠b) (h:a≠c) (i:a≠d) (j:b≠c) (k:b≠d) (l:c≠d):4<=s.card:=by
 have f:({a,b,c,d}:Finset α)⊆s:=by{intro e m;simp only[_mi,_ms] at m;rcases m with rfl|rfl|rfl|rfl <;> assumption};have:=_cl f
 rwa[_cin (by simp[g,h,i]),
  _cin (by simp[j,k]),_c2 l] at this
lemma aT {α:Type} [DecidableEq α] {s:Finset α} {a b c:α} (i:a∈s) (j:b∈s) (k:c∈s) (f:a≠b) (g:a≠c) (h:b≠c) (m:s.card<=3):∀ e∈s,e=a\/e=b\/e=c:=by
 intro e l;by_contra d;rw[not_or,not_or] at d;have:=d6 (s:=s.erase e) (_me.2 ⟨Ne.symm d.1,i⟩) (_me.2 ⟨Ne.symm d.2.1,j⟩) (_me.2 ⟨Ne.symm d.2.2,k⟩) f g h;rw[card_erase_of_mem l] at this;omega
lemma gG {α:Type} [DecidableEq α] {s:Finset α} {a b:α} (f:a∈s) (g:b∈s) (d:a≠b) (i:s.card<=2):∀ e∈s,e=a\/e=b:=by
 intro e h;by_contra c;rw[not_or] at c;have:=d6 h f g c.1 c.2 d;omega
lemma bf {D:Dag} (h:ai 14 D) (j:ar D) {pos:O->ℕ×_d} (a:bA 14 eW D pos) {x y:O} (c:aP x y):∃ e∈af 14 D x,am e∈af 14 D y /\(∀ i∈aa 14 D,e=pos i->y=i) /\∀ i∈aa 14 D,am e=pos i->x=i:=by
 obtain⟨e,f,g,-⟩:=cg bs h.1 (bF j) c;exact⟨e,f,g,fun i d b=>em a d (b▸g),fun i d b=>em a d (by rw[<- b,aB];exact f)⟩
lemma mV:∀ x a b:O,(az x).card=3 ->x≠a->x≠b->bK a b=false ->∃ y,ac x y=true/\bK y a=false/\bK y b=false:=by decide +kernel
lemma bE {D:Dag} (h:ai 14 D) (g:ar D) {x a b:O} (i:(az x).card=3) (d:x≠a) (f:x≠b) (c:¬ dj a b):∃ e,e∈af 14 D x/\a∉ag 14 D (aw D e)/\b∉ag 14 D (aw D e):=by
 obtain⟨y,j,k,l⟩:=mV x a b i d f (b3.mpr c);exact jJ bs h.1 g c ((ae x y).mp j) (b3.mp k) (b3.mp l)
lemma qu {D:Dag} (h:ai 14 D) (u:ar D) {pos:O->ℕ×_d} (b:bA 14 eW D pos) {i x r:O} (j:i∈aa 14 D) (k:aP i x) (c:aP i r) (d:r≠x) (l:(az x).card=3) (w:(af 14 D x).card<=2):∃ Z,Z≠pos i/\af 14 D x={pos i,Z} /\∀ t,t≠x->¬ dj r t->Z∉af 14 D t:=by
 obtain⟨Z,y,m⟩:=kb bs h.1 (bF u) (x:=x) (a:=r) (Ne.symm d);have z:pos i∈af 14 D x:=aJ b j k;have e:Z≠pos i:=fun n=>m (n▸(b.1 i j).2.2.1 r c);have v:af 14 D x={pos i,Z}:=by
  symm;refine _eqc (fun f g=>?_) ?_
  · rw[_mi,_ms] at g
    rcases g with rfl|rfl;{exact z};{exact y}
  · rw[_c2 (Ne.symm e)];exact w
 refine⟨Z,e,v,fun t p q s=>?_⟩;obtain⟨f,g,A,B⟩:=bE h u l (Ne.symm d) (Ne.symm p) q;rw[v,_mi,_ms] at g;rcases g with rfl|rfl;{exact A ((b.1 i j).2.2.1 r c)};{exact B (ak.1 s).2.1}
lemma cm {D:Dag} (h:ai 14 D) (l:ar D) {pos:O->ℕ×_d} (a:bA 14 eW D pos) {i x:O} (m:i∈aa 14 D) (b:aP i x) (e:(az x).card=3) (n:(af 14 D x).card<=2):∃ Z,Z≠pos i/\af 14 D x={pos i,Z} /\∀ t,t≠x->decide (t.val<7)=decide (x.val<7)->Z∉af 14 D t:=by
 obtain⟨r,c,f⟩:=bs.2.2.2 i x;obtain⟨Z,g,p,q⟩:=qu h l a m b c f e n;refine⟨Z,g,p,fun t j k=>q t j (fun d=>?_)⟩;have s:=f8 i x ((cW i x).2 (Or.inl b));have u:=f8 i r ((cW i r).2 (Or.inl c));have v:=f8 r t ((cW r t).2 d);cases w:decide (i.val<7)<;> cases y:decide (x.val<7)<;>
  cases z:decide (r.val<7)<;> cases A:decide (t.val<7)<;> simp_all
lemma cx {D:Dag} (h:ai 14 D) (s:ar D) {pos:O->ℕ×_d} (a:bA 14 eW D pos) {i1 i2 u v:O} (b:i1∈aa 14 D) (c:i2∈aa 14 D) (t:i1≠i2/\ac i1 u=true/\ac i2 u=true/\ac u v=true /\v≠i1/\v≠i2):3<=(af 14 D u).card:=by
 obtain⟨g,m,n,i,j,k⟩:=t;rw[ae] at m n i;have p:=aJ a b m;have q:=aJ a c n;have d:pos i1≠pos i2:=fun e=>g (a.2 i1 b i2 c e);by_cases f:v∈aa 14 D;{exact d6 p q (aJ a f (bm i)) d (fun e=>j.symm (a.2 i1 b v f e)) (fun e=>k.symm (a.2 i2 c v f e))}
 · obtain⟨e,w,-,r,-⟩:=bf h s a i
   exact d6 p q w d (fun l=>f (r i1 b l.symm▸b)) (fun l=>f (r i2 c l.symm▸c))
lemma dy {D:Dag} (h:ai 14 D) (Q:ar D) (F:bL 14 D=0) {pos:O->ℕ×_d} (a:bA 14 eW D pos) {i1 i2 u v:O} (r:i1∈aa 14 D) (s:i2∈aa 14 D) (W:i1≠i2/\ac i1 u=true/\ac i2 u=true/\ac u v=true /\v≠i1/\v≠i2) (w:(af 14 D u).card<=3):(∀ t,t∈ag 14 D (aw D (pos i1))->aP i1 t) /\(∀ t,t∈ag 14 D (aw D (pos i2))->aP i2 t):=by
 obtain⟨x,G,H,I,y,z⟩:=W;rw[ae] at G H I;have i:∀(c b:O),c∈aa 14 D->b∈aa 14 D->c≠b ->aP c u->aP b u->v≠c->v≠b ->∀ t,t∈ag 14 D (aw D (pos c))->aP c t:=by
  intro c b d f m j A k B t X;have R:=aJ a d j;have S:=aJ a f A;have C:pos c≠pos b:=fun e=>m (a.2 c d b f e);have n:∀ t,t∈ag 14 D (aw D (pos c))↔aP c t:=by
   refine cT h Q F a d j (fun p T l g=>?_);by_cases q:v∈aa 14 D
   · have Y:=aJ a q (bm I)
     have J:pos c≠pos v:=fun e=>k.symm (a.2 c d v q e);have K:pos b≠pos v:=fun e=>B.symm (a.2 b f v q e);rcases aT R S Y C J K w p T with rfl|rfl|rfl;{exact l rfl}
     · have E:b∈ag 14 D (aw D (am (pos b))):=by
        rw[show aw D (am (pos b))=aw D ((pos b).1,!(pos b).2) from rfl,(a.1 b f).2.2.2];exact _mss b
       exact m.symm (_ms.1 (g E))
     · have E:v∈ag 14 D (aw D (am (pos v))):=by
        rw[show aw D (am (pos v))=aw D ((pos v).1,!(pos v).2) from rfl,(a.1 v q).2.2.2];exact _mss v
       exact k (_ms.1 (g E))
   · obtain⟨e,Z,L,U,-⟩:=bf h Q a I
     have M:pos c≠e:=fun N=>q (U c d N.symm▸d);have P:pos b≠e:=fun N=>q (U b f N.symm▸f);rcases aT R S Z C M P w p T with rfl|rfl|rfl;{exact l rfl}
     · have E:b∈ag 14 D (aw D (am (pos b))):=by
        rw[show aw D (am (pos b))=aw D ((pos b).1,!(pos b).2) from rfl,(a.1 b f).2.2.2];exact _mss b
       exact m.symm (_ms.1 (g E))
     · exact q (_ms.1 (g (ak.1 L).2.1)▸d)
  exact(n t).1 X
 exact⟨i i1 i2 r s x G H y z,i i2 i1 s r x.symm H G z y⟩
lemma dl {D:Dag} (h:ai 14 D) (g:ar D) {pos:O->ℕ×_d} (a:bA 14 eW D pos) (z k v iz ik:O) (b:iz∈aa 14 D) (c:ik∈aa 14 D) (t:z∉aa 14 D) (u:k∉aa 14 D) (w:v∉aa 14 D) (x:ac iz z=true/\ac ik k=true/\ac z k=true /\ac z v=true/\v≠k/\(az k).card=3 /\decide (v.val<7)=decide (k.val<7)) (i:(af 14 D z).card<=2) (j:(af 14 D k).card<=2):False:=by
 obtain⟨g1,g2,g3,g4,g5,g6,g7⟩:=x;rw[ae] at g1 g2 g3 g4;obtain⟨Dk,-,l,m⟩:=cm h g a c g2 g6 j;obtain⟨e,y,d,A,A'⟩:=bf h g a g3;obtain⟨e',y',d',x',-⟩:=bf h g a g4;rw[l,_mi,_ms] at d;have B:am e=Dk:=d.resolve_left (fun r=>t (A' ik c r▸c));rcases gG (aJ a b g1) y (fun r=>u (A iz b r.symm▸b)) i e' y' with s|s;{exact w (x' iz b s▸b)};{exact m v g5 g7 (by rw[<- B,<-s];exact d')}
lemma fR {D:Dag} (h:ai 14 D) (k:ar D) {pos:O->ℕ×_d} (a:bA 14 eW D pos) (u k1 k2 v ik1 ik2:O) (b:ik1∈aa 14 D) (c:ik2∈aa 14 D) (M:u∉aa 14 D) (N:ac u k1=true/\ac u k2=true/\ac u v=true /\ac ik1 k1=true/\ac ik2 k2=true /\k1≠k2/\v≠k1/\v≠k2 /\(az k1).card=3/\(az k2).card=3 /\decide (k1.val<7)=decide (k2.val<7)/\decide (v.val<7)=decide (k1.val<7)) (B:(af 14 D u).card<=2) (l:(af 14 D k1).card<=2) (m:(af 14 D k2).card<=2):False:=by
 obtain⟨g1,g2,g3,g4,g5,n,p,q,C,E,d,e⟩:=N;rw[ae] at g1 g2 g3 g4 g5;obtain⟨D1,-,F,r⟩:=cm h k a b g4 C l;obtain⟨D2,-,s,G⟩:=cm h k a c g5 E m;obtain⟨e1,H,f,-,hf1'⟩:=bf h k a g1;obtain⟨e2,I,g,-,hf2'⟩:=bf h k a g2;obtain⟨e3,J,i,-,-⟩:=bf h k a g3;rw[F,_mi,_ms] at f;have x:am e1=D1:=f.resolve_left (fun K=>M (hf1' ik1 b K▸b));rw[s,_mi,_ms] at g;have y:am e2=D2:=g.resolve_left (fun K=>M (hf2' ik2 c K▸c));have z:e1≠e2:=fun L=>by
  have A:D1=D2:=by rw[<- x,<-y,L]
  have j:D2∈af 14 D k2:=by rw[s];simp
  exact r k2 n.symm d.symm (A▸j)
 rcases gG H I z B e3 J with rfl|rfl;{exact r v p e (x▸i)};{exact G v q (e.trans d) (y▸i)}
def iQ (D:Dag) (pos:O->ℕ×_d) (P Q:ℕ×_d):Prop:=bA 14 eW D pos/\(∀ x,(af 14 D x).card<=3)/\P≠Q /\∀ x,3<=(af 14 D x).card->P∈af 14 D x/\Q∈af 14 D x
lemma fq {D:Dag} (h:ai 14 D) (l:ar D) (p:bd 14 D=(al 14 D).card+1):∃ pos P Q,iQ D pos P Q:=by
 classical
 have g:=bs;have i:=bF l;obtain⟨b,m⟩:=b_ g h.1 i;have c:=bD m;obtain⟨pos,a⟩:=bQ g h i;have q:=bS h.1 b c;have d:∀ x,(af 14 D x).card<=3:=fun x=>by{have r:=bj h l b c x;have s:(aZ D b x).card<=(aj 14 D b).card:=_cfl _ _;omega};by_cases n:(univ.filter (fun x:O=>3<=(af 14 D x).card)).Nonempty
 · obtain⟨P,Q,j,e⟩:=fW g h i b m (by omega) _ n (fun x f=>(_mf.1 f).2)
   exact⟨pos,P,Q,a,d,fun k=>j (k▸rfl),fun x f=>e x (_mf.2 ⟨_mv x,f⟩)⟩
 · refine⟨pos,(0,false),(0,true),a,d,by decide,fun x f=>?_⟩
   exact absurd ⟨x,_mf.2 ⟨_mv x,f⟩⟩ n
lemma gH {D:Dag} (h:ai 14 D) (X:ar D) (K:bL 14 D=0) {pos:O->ℕ×_d} {P Q:ℕ×_d} (z:iQ D pos P Q) (x y ix iy:O) (f:ix∈aa 14 D) (c:iy∈aa 14 D) (Y:x∉aa 14 D) (L:y∉aa 14 D) (Z:ix≠iy/\ac ix x=true/\ac iy y=true/\ac x y=true /\ac ix y=false) (M:3<=(af 14 D x).card) (N:3<=(af 14 D y).card):False:=by
 obtain⟨b,n,A,j⟩:=z;obtain⟨k,g1,g2,g3,g4⟩:=Z;rw[ae] at g1 g2 g3;obtain⟨q,r⟩:=j x M;obtain⟨s,t⟩:=j y N;obtain⟨e,g,i,B,R⟩:=bf h X b g3;have S:e≠P:=fun d=>el h.1 (d▸s) i;have T:e≠Q:=fun d=>el h.1 (d▸t) i;have C:am e≠P:=fun d=>el h.1 q (by rw[<- d,aB];exact g);have E:am e≠Q:=fun d=>el h.1 r (by rw[<- d,aB];exact g);have F:=aJ b f g1;have U:=aJ b c g2;have l:pos ix≠e:=fun d=>L (B ix f d.symm▸f);have u:pos iy≠am e:=fun d=>Y (R iy c d.symm▸c);have G:pos ix∈af 14 D y:=by{rcases aT q r g A S.symm T.symm (n x) (pos ix) F with a|a|a;{exact a▸s};{exact a▸t};{exact absurd a l}};have H:pos iy∈af 14 D x:=by{rcases aT s t i A C.symm E.symm (n y) (pos iy) U with a|a|a;{exact a▸q};{exact a▸r};{exact absurd a u}};have v:pos ix≠pos iy:=fun d=>k (b.2 ix f iy c d);have I:pos iy≠e:=fun d=>L (B iy c d.symm▸c);have W:=aT F H g v l I (n x)
 have w:=cT h X K b f g1 (fun p hp J m=>by
  rcases W p hp with rfl|rfl|rfl;{exact J rfl}
  · have hm:iy∈ag 14 D (aw D (am (pos iy))):=by
     rw[show aw D (am (pos iy))=aw D ((pos iy).1,!(pos iy).2) from rfl,(b.1 iy c).2.2.2];exact _mss iy
    exact k.symm (_ms.1 (m hm))
  · exact L (_ms.1 (m (ak.1 i).2.1)▸f))
 exact aH.1 g4 ((w y).1 (ak.1 G).2.1)
lemma kx {D:Dag} (h:ai 14 D) (I:ar D) {pos:O->ℕ×_d} {P Q:ℕ×_d} (L:iQ D pos P Q) (a1 a2 b0 b1 b2 ia1 ia2 ib0 ib1 ib2:O) (b:ia1∈aa 14 D) (d:ia2∈aa 14 D) (j:ib0∈aa 14 D) (f:ib1∈aa 14 D) (k:ib2∈aa 14 D) (M:a1∉aa 14 D) (N:a2∉aa 14 D) (R:b0∉aa 14 D) (J:b1∉aa 14 D) (S:b2∉aa 14 D) (hg:ia1≠ia2/\b0≠b1/\b0≠b2/\b1≠b2 /\ac ia1 a1=true/\ac ia2 a2=true /\ac ib0 b0=true/\ac ib1 b1=true/\ac ib2 b2=true /\ac a1 b0=true/\ac a1 b1=true /\ac a2 b1=true/\ac a2 b2=true /\(az b0).card=3/\(az b1).card=3/\(az b2).card=3 /\decide (b0.val<7)=decide (b1.val<7)/\decide (b1.val<7)=decide (b2.val<7)) (w:3<=(af 14 D a1).card) (x:3<=(af 14 D a2).card) (T:(af 14 D b0).card<=2) (U:(af 14 D b1).card<=2) (W:(af 14 D b2).card<=2):False:=by
 obtain⟨c,X,hl,g⟩:=L;obtain⟨Y,hm,hn,ho,ga1,ga2,gb0,gb1,gb2,e10,e11,e21,e22,hp,hq,hr,y,z⟩:=hg;rw[ae] at ga1 ga2 gb0 gb1 gb2 e10 e11 e21 e22;obtain⟨D0,-,Z,h0⟩:=cm h I c j gb0 hp T;obtain⟨D1,-,K,hs⟩:=cm h I c f gb1 hq U;obtain⟨D2,-,h1,hp2⟩:=cm h I c k gb2 hr W;have hk:D0∈af 14 D b0:=by rw[Z];simp
 have t:D1∈af 14 D b1:=by rw[K];simp
 have i:D2∈af 14 D b2:=by rw[h1];simp
 obtain⟨f10,h2,l,A,h3⟩:=bf h I c e10;obtain⟨f11,h4,m,h5,h6⟩:=bf h I c e11;obtain⟨f21,h7,n,B,h8⟩:=bf h I c e21;obtain⟨f22,h9,p,C,ha⟩:=bf h I c e22;have q:am f10=D0:=by{rw[Z,_mi,_ms] at l;exact l.resolve_left (fun a=>M (h3 ib0 j a▸j))};have E:am f11=D1:=by{rw[K,_mi,_ms] at m;exact m.resolve_left (fun a=>M (h6 ib1 f a▸f))};have r:am f21=D1:=by{rw[K,_mi,_ms] at n;exact n.resolve_left (fun a=>N (h8 ib1 f a▸f))};have F:am f22=D2:=by{rw[h1,_mi,_ms] at p;exact p.resolve_left (fun a=>N (ha ib2 k a▸k))};have hb:f11=f21:=by rw[<- aB f11,<-aB f21,E,r]
 have G:D0≠D1:=fun a=>h0 b1 hm.symm y.symm (a▸t);have hc:D0≠D2:=fun a=>h0 b2 hn.symm (y.trans z).symm (a▸i);have hd:D1≠D2:=fun a=>hs b2 ho.symm z.symm (a▸i);have u:f10≠f11:=fun a=>G (by rw[<- q,<-E,a]);have v:f21≠f22:=fun a=>hd (by rw[<- r,<-F,a]);have he:=aJ c b ga1;have hf:=aJ c d ga2;have hi:=aT he h2 h4 (fun a=>R (A ia1 b a.symm▸b)) (fun a=>J (h5 ia1 b a.symm▸b)) u (X a1);have H:=aT hf h7 h9 (fun a=>J (B ia2 d a.symm▸d)) (fun a=>S (C ia2 d a.symm▸d)) v (X a2);have s:∀ e,e∈af 14 D a1->e∈af 14 D a2->e=f11:=by
  intro e ht hj;rcases hi e ht with rfl|rfl|rfl
  · rcases H _ hj with a|a|a
    · exact absurd (c.2 ia1 b ia2 d a) Y
    · exact absurd (B ia1 b a.symm▸b) J
    · exact absurd (C ia1 b a.symm▸b) S
  · rcases H _ hj with a|a|a
    · exact absurd (A ia2 d a▸d) R
    · exact absurd (by rw[<- q,<-r,a]) G
    · exact absurd (by rw[<- q,<-F,a]) hc
  · rfl
 exact hl ((s P (g a1 w).1 (g a2 x).1).trans (s Q (g a1 w).2 (g a2 x).2).symm)
lemma mn {α:Type} [DecidableEq α] {s:Finset α} {a b c d e:α} (t:a∈s) (u:b∈s) (v:c∈s) (w:d∈s) (y:e∈s) (g:a≠b) (h:a≠c) (i:a≠d) (j:a≠e) (k:b≠c) (l:b≠d) (m:b≠e) (n:c≠d) (p:c≠e) (q:d≠e):5<=s.card:=by
 have f:({a,b,c,d,e}:Finset α)⊆s:=by{intro x r;simp only[_mi,_ms] at r;rcases r with rfl|rfl|rfl|rfl|rfl <;> assumption};have:=_cl f
 rwa[_cin (by simp[g,h,i,j]),
  _cin (by simp[k,l,m]),
  _cin (by simp[n,p]),
  _c2 q] at this
lemma gh {α:Type} [DecidableEq α] {s:Finset α} {a b c d:α} (m:a∈s) (n:b∈s) (p:c∈s) (q:d∈s) (g:a≠b) (h:a≠c) (i:a≠d) (j:b≠c) (k:b≠d) (l:c≠d) (t:s.card<=4):∀ e∈s,e=a\/e=b\/e=c\/e=d:=by
 intro e r;by_contra f;rw[not_or,not_or,not_or] at f;have:=mn r m n p q f.1 f.2.1 f.2.2.1 f.2.2.2 g h i j k l;omega
lemma cV {D:Dag} {pos:O->ℕ×_d} (a:bA 14 eW D pos) {j t:O} (b:j∈aa 14 D) (c:t∈ag 14 D (aw D (pos j))):pos j∈af 14 D t:=by
 obtain⟨d,e,-,-⟩:=a.1 j b;exact ak.2 ⟨d,c,by rw[e];exact notMem_empty t⟩
lemma cy {D:Dag} (h:ai 14 D) (r:ar D) (b:O->ℕ) (x:aM 14 D b) {pos:O->ℕ×_d} (a:bA 14 eW D pos) {v t j q:O} (s:j∈aa 14 D) (y:v∈al 14 D) (c:∀ u∈aj 14 D b,v∈ag 14 D u.1->t∈ag 14 D u.1) {w:ℕ} (z:v∈ag 14 D w/\t∈ag 14 D w) (A:(az v).card=3/\ac j v=true/\ac j q=true /\v≠t/\v≠q/\bK t q=false):t∈ag 14 D (aw D (pos j)):=by
 obtain⟨k,d,f,g,l,m⟩:=A;rw[ae] at d f;obtain⟨e0,i⟩:=jx bs h (bF r) b x g y c z;by_contra B;have C:pos j=e0:=by{by_contra n;exact B (i _ (aJ a s d) n)};obtain⟨e,E,F,G⟩:=bE h r k g l (b3.1 m);exact F (i e E (fun p=>G (by rw[p,<-C];exact(a.1 j s).2.2.1 q f)))
lemma o0 {D:Dag} (h:ai 14 D) (j:ar D) (k:bL 14 D=0) (b:O->ℕ) (l:aM 14 D b) {pos:O->ℕ×_d} (a:bA 14 eW D pos) {v i1 i2 v3 t:O} (e:i1∈aa 14 D) (f:i2∈aa 14 D) (B:v∈al 14 D) (I:(az v).card=3/\i1≠i2/\ac i1 v=true/\ac i2 v=true /\ac v v3=true/\v3≠i1/\v3≠i2) (C:(aZ D b v).card=1) (c:aZ D b v⊆aZ D b t) (g:v≠t) (J:∃ q:O,(ac i1 q=true/\v≠q/\bK t q=false/\ac i1 t=false) \/(ac i2 q=true/\v≠q/\bK t q=false/\ac i2 t=false)):False:=by
 obtain⟨i,m,E,F,K,n,p⟩:=I;have r:(af 14 D v).card<=3:=by{have:=bj h j b l v;omega};obtain⟨s,w⟩:=dy h j k a e f ⟨m,E,F,K,n,p⟩ r;obtain⟨u,G⟩:=_cp.1 (by omega:0<(aZ D b v).card);have x:=c G;have d:∀ u'∈aj 14 D b,v∈ag 14 D u'.1->t∈ag 14 D u'.1:=fun u' G' B'=>(_mf.1 (c (_mf.2 ⟨G',B'⟩))).2;have H:v∈ag 14 D u.1/\t∈ag 14 D u.1:=⟨(_mf.1 G).2,(_mf.1 x).2⟩;obtain⟨q,⟨a1,a2,a3,a4⟩|⟨a1,a2,a3,a4⟩⟩:=J;{exact aH.1 a4 (s t (cy h j b l a e B d H ⟨i,E,a1,g,a2,a3⟩))};{exact aH.1 a4 (w t (cy h j b l a f B d H ⟨i,F,a1,g,a2,a3⟩))}
lemma fa {D:Dag} (h:ai 14 D) (E:ar D) (j:O->ℕ) (p:aM 14 D j) {pos:O->ℕ×_d} (c:bA 14 eW D pos) (a b a1 a2 qa1 qa2 b1 b2 vb:O) (L:a∈al 14 D) (d:a1∈aa 14 D) (f:a2∈aa 14 D) (g:b1∈aa 14 D) (i:b2∈aa 14 D) (k:vb∉aa 14 D) (Q:a≠b/\a1≠a2/\a1≠b1/\a1≠b2/\a2≠b1/\a2≠b2/\b1≠b2 /\(az a).card=3/\ac a1 a=true/\ac a2 a=true /\ac a1 qa1=true/\a≠qa1/\bK b qa1=false /\ac a2 qa2=true/\a≠qa2/\bK b qa2=false /\ac b1 b=true/\ac b2 b=true/\ac b vb=true) (R:1<=(aZ D j a).card) (m:aZ D j a⊆aZ D j b) (M:(aZ D j b).card<=2):False:=by
 obtain⟨x,y,q,r,s,t,z,A,ga1,ga2,gqa1,v,gbqa1,gqa2,w,gbqa2,gb1,gb2,gvb⟩:=Q;obtain⟨u,N⟩:=_cp.1 (by omega:0<(aZ D j a).card);have n:∀ u'∈aj 14 D j,a∈ag 14 D u'.1->b∈ag 14 D u'.1:=fun u' N' L'=>(_mf.1 (m (_mf.2 ⟨N',L'⟩))).2;have P:a∈ag 14 D u.1/\b∈ag 14 D u.1:=⟨(_mf.1 N).2,(_mf.1 (m N)).2⟩;have I:=cV c d (cy h E j p c d L n P ⟨A,ga1,gqa1,x,v,gbqa1⟩);have J:=cV c f (cy h E j p c f L n P ⟨A,ga2,gqa2,x,w,gbqa2⟩);have B:=aJ c g ((ae _ _).1 gb1);have C:=aJ c i ((ae _ _).1 gb2);obtain⟨ev,K,-,l,-⟩:=bf h E c ((ae _ _).1 gvb);have T:=mn I J B C K (fun e=>y (c.2 _ d _ f e)) (fun e=>q (c.2 _ d _ g e)) (fun e=>r (c.2 _ d _ i e)) (fun e=>k (l _ d e.symm▸d)) (fun e=>s (c.2 _ f _ g e)) (fun e=>t (c.2 _ f _ i e)) (fun e=>k (l _ f e.symm▸f)) (fun e=>z (c.2 _ g _ i e)) (fun e=>k (l _ g e.symm▸g)) (fun e=>k (l _ i e.symm▸i));have S:=bj h E j p b;omega
lemma ay {D:Dag} {b:O->ℕ} {x:O} {u:Σ _:ℕ,ℕ}:u∈aZ D b x↔u∈aj 14 D b/\x∈ag 14 D u.1:=_mf
lemma mW:∀ a b x y:O,a≠b ->ac a x=true->ac b x=true->ac a y=true->ac b y=true->x=y:=by
 decide +kernel
lemma fS:∀ w a b:O,ac w a=true->ac w b=true->decide (a.val<7)=decide (b.val<7):=by
 decide +kernel
lemma cd {D:Dag} {pos:O->ℕ×_d} (a:bA 14 eW D pos) {i:O} (b:i∈aa 14 D):i∈ag 14 D (aw D (am (pos i))):=by
 rw[show aw D (am (pos i))=aw D ((pos i).1,!(pos i).2) from rfl,(a.1 i b).2.2.2];exact _mss i
lemma fz {D:Dag} (h:ai 14 D) (s:ar D) (b:O->ℕ) (t:cU 14 D b) {d:Σ _:ℕ,ℕ} {x:O} (e:aZ D b x={d}) (v:3<=(af 14 D x).card):∃ P Q:ℕ×_d,P≠Q /\∀ y:O,y∈ag 14 D d.1->aZ D b y={d}->3<=(af 14 D y).card ->P∈af 14 D y/\Q∈af 14 D y:=by
 classical
 have k:=bD t;have a:d∈aZ D b x:=by rw[e];exact _mss d
 obtain⟨f,-⟩:=ay.1 a;let X:=univ.filter (fun y:O=>y∈ag 14 D d.1/\aZ D b y={d}/\3<=(af 14 D y).card);have l:x∈X:=_mf.2 ⟨_mv _,(ay.1 a).2,e,v⟩
 obtain⟨P,Q,m,g⟩:=pi bs h (bF s) b t f X ⟨x,l⟩ (fun y w=>by
  obtain⟨-,n,c,i⟩:=_mf.1 w;have p:=bj h s b k y;rw[c,_cs] at p;refine⟨card_eq_zero.1 (by omega),n,fun u z n'=>?_⟩
  exact _ms.1 (c▸ay.2 ⟨z,n'⟩))
 exact⟨P,Q,fun A=>m (A▸rfl),fun y q r i=>
  g y (_mf.2 ⟨_mv _,q,r,i⟩)⟩
lemma dV {D:Dag} (h:ai 14 D) (hD:ar D) (b:O->ℕ) (hb:cU 14 D b) {f:Σ _:ℕ,ℕ} {x:O} (I:aZ D b x={f}) (T:3<=(af 14 D x).card):∃ P Q:ℕ×_d,P≠Q/\P∈af 14 D x/\Q∈af 14 D x /\∀ y:O,y∈ag 14 D f.1->y∈ag 14 D (aw D P)/\y∈ag 14 D (aw D Q):=by
 classical
 have n:=h.1;have hbp:=bD hb;have hcc:=bj h hD b hbp x;rw[I,_cs] at hcc;have U:aW 14 D (ao 14 D {x})=∅:=card_eq_zero.1 (by omega);have W:f∈aZ D b x:=by rw[I];exact _mss f
 obtain⟨F,g⟩:=ay.1 W;have X:f∈dq 14 D:=(_mf.1 (_md.1 F).1).1;have Y:2<=aF D f.1:=by have:=(dW.1 X).2;omega
 have hxe:x∈al 14 D:=fC F g;have Z:∀ w,f.1<w->x∈ag 14 D w->aF D w<=1:=by
  intro w hrw t;by_contra hc;have hwu:(⟨w,0⟩:Σ _:ℕ,ℕ)∈da 14 D:=by{rw[da,_mf,dW];exact⟨⟨bP.2 (dc n (w:=w) (by omega)),by show 0+1<aF D w;omega⟩,⟨x,t⟩⟩};by_cases h0:(⟨w,0⟩:Σ _:ℕ,ℕ)∈cz 14 D b
  · obtain⟨v,hv,h5⟩:=_mg.1 h0
    have h6:b v=w:=congrArg Sigma.fst h5;have h7:=(hb v hv).2.1;rw[h6] at h7;rw[h7,_ms] at t;have h8:=(hb x hxe).2.2.2 f.1 Y g;rw[t,h6] at h8;omega
  · have p:(⟨w,0⟩:Σ _:ℕ,ℕ)∈aZ D b x:=ay.2 ⟨_md.2 ⟨hwu,h0⟩,t⟩
    rw[I,_ms] at p;have:w=f.1:=congrArg Sigma.fst p;omega
 have m:∀ {a c:ℕ},Relation.ReflTransGen (ex 14 D {x}) a c ->ag 14 D a⊆ag 14 D c:=by
  intro a c hp;induction hp with
  | refl=>exact Subset.refl _
  | @tail u v _ h9 ih=>
   obtain⟨J,hge,z⟩:=h9.1;have hv:14+(v - 14)=v:=by omega
   have hxv:x∈ag 14 D (14+(v - 14)):=by{rw[hv];exact(h9.2.2 x (_mss x)).2};have q:cR D (v - 14)=false:=(dL n U (by omega) hxv).1
   exact ih.trans (by
    rw[<- hv,de n (by omega) q];rcases z with k|k;{rw[k];exact subset_union_left}
    · rw[k];exact subset_union_right)
 have d:∀ j∈bV D f.1,j<D.length/\f.1<14+j/\(cj D j=f.1\/ck D j=f.1):=by{intro j J;simp only[bV,_mf,mem_range] at J;have:=n j J.1;exact⟨J.1,by omega,J.2⟩};have r:∀ j∈bV D f.1,∃ e:ℕ×_d,e∈af 14 D x /\ag 14 D f.1⊆ag 14 D (aw D e) /\((e.1=j/\aw D e=f.1)\/Relation.ReflTransGen (ex 14 D {x}) (14+j) (aw D e)):=by
  intro j J;obtain⟨s,hlt,z⟩:=d j J;by_cases A:x∈ag 14 D (14+j)
  · have q:cR D j=false:=(dL n U s A).1
    have K:ag 14 D f.1⊆ag 14 D (14+j):=by{rw[de n s q];rcases z with k|k;{rw[k];exact subset_union_left};{rw[k];exact subset_union_right}};obtain⟨e,he1,hd⟩:=lm bs h (bF hD) {x} ⟨x,_mss x⟩ (fun y G=>by rw[_ms.1 G];exact U) (14+j) (fun y G=>by rw[_ms.1 G];exact A) (fun y G w hrw hf=>by rw[_ms.1 G] at hf;exact Z w (by omega) hf);exact⟨e,he1 x (_mss x),K.trans (m hd),Or.inr hd⟩
  · rcases z with k|k
    · refine⟨(j,false),ak.2 ⟨s,by rw[aX,k];exact g,A⟩,by rw[aX,k],Or.inl ⟨rfl,by rw[aX,k]⟩⟩
    · refine⟨(j,true),ak.2 ⟨s,by rw[bh,k];exact g,A⟩,by rw[bh,k],Or.inl ⟨rfl,by rw[bh,k]⟩⟩
 obtain⟨j1,B,j2,C,L⟩:=one_lt_card.1 (by exact Y:1<(bV D f.1).card);have i:∀ a c,ex 14 D {x} a c->bk 14 D a c:=fun _ _ hr=>hr.1;have hg:∀ a a' c,ex 14 D {x} a c->ex 14 D {x} a' c->a=a':=by
  intro a a' c p h2;by_contra H;obtain⟨s,hge1,hh⟩:=p.1;obtain⟨-,-,hi⟩:=h2.1;have hcv:14+(c - 14)=c:=by omega
  have ha:=(p.2.2 x (_mss x)).1;have ha':=(h2.2.2 x (_mss x)).1;have hc:=(p.2.2 x (_mss x)).2;have hxc:x∈ag 14 D (14+(c - 14)):=by rw[hcv];exact hc
  apply(dL n U (by omega) hxc).2;rcases hh with e1|e1 <;> rcases hi with e2|e2;{exact absurd (e1.symm.trans e2) H};{rw[e1,e2];exact⟨ha,ha'⟩};{rw[e1,e2];exact⟨ha',ha⟩};{exact absurd (e1.symm.trans e2) H}
 have l:∀ ja∈bV D f.1,∀ jb∈bV D f.1,ja≠jb ->¬ Relation.ReflTransGen (ex 14 D {x}) (14+ja) (14+jb):=by
  intro ja hja jb hjb hab hp;obtain⟨-,hlta,-⟩:=d ja hja;obtain⟨hl,-,hm⟩:=d jb hjb;rcases Relation.ReflTransGen.cases_tail hp with heq|⟨u,hu1,M⟩;{exact hab (by omega)}
  · have E:=dt n i hu1
    have N:u=f.1:=by{by_contra N;obtain⟨-,-,hn⟩:=M.1;rw[Nat.add_sub_cancel_left] at hn;apply(dL n U hl (M.2.2 x (_mss x)).2).2;have hu:=(M.2.2 x (_mss x)).1;rcases hn with e1|e1 <;> rcases hm with e2|e2;{exact absurd (e1.symm.trans e2) N};{rw[e1,e2];exact⟨hu,g⟩};{rw[e1,e2];exact⟨g,hu⟩};{exact absurd (e1.symm.trans e2) N}};omega
 obtain⟨P,hPx,R,hP2⟩:=r j1 B;obtain⟨Q,hQx,S,ho⟩:=r j2 C;refine⟨P,Q,fun hPQ=>?_,hPx,hQx,fun y G=>⟨R G,S G⟩⟩;rw[<- hPQ] at ho;rcases hP2 with ⟨p,h2⟩|p <;> rcases ho with ⟨T,h4⟩|T;{exact L (p.symm.trans T)}
 · have E:=dt n i T
   have:=(d j2 C).2.1;rw[h2] at E;omega
 · have E:=dt n i p
   have:=(d j1 B).2.1;rw[h4] at E;omega
 · rcases gq hg p T with h12|h21
   · exact l j1 B j2 C L h12
   · exact l j2 C j1 B L.symm h21
lemma eF {D:Dag} (h:ai 14 D) (G:ar D) (h0:bL 14 D=0) (b:O->ℕ) (hb:cU 14 D b) {pos:O->ℕ×_d} (f:bA 14 eW D pos) {u0:Σ _:ℕ,ℕ} {a i1 i2 v3:O} (p:i1∈aa 14 D) (r:i2∈aa 14 D) (hg:(az a).card=3/\i1≠i2/\ac i1 a=true/\ac i2 a=true /\ac a v3=true/\v3≠i1/\v3≠i2) (H:aZ D b a={u0}):∀ y,y∈ag 14 D u0.1->y=a:=by
 have h2:=bD hb;obtain⟨I,v,m,n,J,K,L⟩:=hg;have h3:=cx h G f p r ⟨v,m,n,J,K,L⟩;have l:(af 14 D a).card<=3:=by{have:=bj h G b h2 a;rw[H,_cs] at this;omega};obtain⟨M,N⟩:=dy h G h0 f p r ⟨v,m,n,J,K,L⟩ l;obtain⟨P,Q,x,z,A,B⟩:=dV h G b hb H h3;have R:pos i1∈af 14 D a:=aJ f p ((ae _ _).1 m);have S:pos i2∈af 14 D a:=aJ f r ((ae _ _).1 n);have T:pos i1≠pos i2:=fun e=>v (f.2 _ p _ r e);intro y hy;by_contra C;obtain⟨U,W⟩:=B y hy;by_cases g:pos i1=P\/pos i1=Q
 · by_cases i:pos i2=P\/pos i2=Q
   · have j:aP i1 y:=M y (by rcases g with rfl|rfl <;> assumption)
     have k:aP i2 y:=N y (by rcases i with rfl|rfl <;> assumption);exact C (mW i1 i2 y a v ((ae _ _).2 j) ((ae _ _).2 k) m n)
   · rw[not_or] at i
     have j:aP i1 y:=M y (by rcases g with rfl|rfl <;> assumption);obtain⟨q,X,E⟩:=gp i2 a;have c:decide (y.val<7)=decide (a.val<7):=fS i1 y a ((ae _ _).2 j) m;have d:decide (q.val<7)=decide (a.val<7):=fS i2 q a X n;have s:¬ dj y q:=fun t=>by{have Y:=f8 y q ((cW _ _).2 t);rw[c,d] at Y;exact Y rfl};obtain⟨e,w,u,F⟩:=bE h G I (Ne.symm C) (Ne.symm E) s;rcases aT z A S x (Ne.symm i.1) (Ne.symm i.2) l e w with rfl|rfl|rfl;{exact u U};{exact u W};{exact F ((f.1 i2 r).2.2.1 q ((ae _ _).1 X))}
 · rw[not_or] at g
   have i:pos i2=P\/pos i2=Q:=by{rcases aT z A R x (Ne.symm g.1) (Ne.symm g.2) l (pos i2) S with w|w|w;{exact Or.inl w};{exact Or.inr w};{exact absurd w T.symm}};have k:aP i2 y:=N y (by rcases i with rfl|rfl <;> assumption);obtain⟨q,Z,E⟩:=gp i1 a;have c:decide (y.val<7)=decide (a.val<7):=fS i2 y a ((ae _ _).2 k) n;have d:decide (q.val<7)=decide (a.val<7):=fS i1 q a Z m;have s:¬ dj y q:=fun t=>by{have Y:=f8 y q ((cW _ _).2 t);rw[c,d] at Y;exact Y rfl};obtain⟨e,w,u,F⟩:=bE h G I (Ne.symm C) (Ne.symm E) s;rcases aT z A R x (Ne.symm g.1) (Ne.symm g.2) l e w with rfl|rfl|rfl;{exact u U};{exact u W};{exact F ((f.1 i1 p).2.2.1 q ((ae _ _).1 Z))}
def qI (a:Fin 68):ℕ×O×O×O×O×O×O:=match a.val with
 | 0=>(2,2,8,13,12,0,1)
 | 1=>(0,8,0,2,6,0,0)
 | 2=>(0,13,1,2,4,0,0)
 | 3=>(2,2,12,13,8,3,1)
 | 4=>(0,13,2,4,1,0,0)
 | 5=>(0,10,4,5,0,0,0)
 | 6=>(0,0,0,0,0,0,0)
 | 7=>(1,1,13,9,7,2,0)
 | 8=>(1,2,13,12,8,1,0)
 | 9=>(1,2,13,12,8,4,0)
 | 10=>(1,1,13,7,9,2,0)
 | 11=>(0,8,0,2,6,0,0)
 | 12=>(2,2,8,12,13,0,3)
 | 13=>(0,12,2,3,5,0,0)
 | 14=>(0,8,0,2,6,0,0)
 | 15=>(0,13,1,2,4,0,0)
 | 16=>(0,11,3,4,6,0,0)
 | 17=>(0,10,0,4,5,0,0)
 | 18=>(0,9,1,5,6,0,0)
 | 19=>(0,10,4,5,0,0,0)
 | 20=>(0,8,0,2,6,0,0)
 | 21=>(0,13,2,4,1,0,0)
 | 22=>(0,10,4,5,0,0,0)
 | 23=>(1,2,12,13,8,3,0)
 | 24=>(0,13,1,4,2,0,0)
 | 25=>(0,10,4,5,0,0,0)
 | 26=>(1,1,13,9,7,4,0)
 | 27=>(0,8,0,2,6,0,0)
 | 28=>(0,12,2,3,5,0,0)
 | 29=>(0,13,2,4,1,0,0)
 | 30=>(0,8,0,2,6,0,0)
 | 31=>(0,8,0,2,6,0,0)
 | 32=>(0,8,0,2,6,0,0)
 | 33=>(0,11,3,4,6,0,0)
 | 34=>(0,9,1,5,6,0,0)
 | 35=>(0,8,0,2,6,0,0)
 | 36=>(0,9,1,5,6,0,0)
 | 37=>(0,9,1,5,6,0,0)
 | 38=>(0,8,2,6,0,0,0)
 | 39=>(0,8,0,2,6,0,0)
 | 40=>(0,10,0,4,5,0,0)
 | 41=>(0,10,4,5,0,0,0)
 | 42=>(0,11,3,4,6,0,0)
 | 43=>(0,9,1,5,6,0,0)
 | 44=>(0,10,4,5,0,0,0)
 | 45=>(0,8,0,2,6,0,0)
 | 46=>(0,8,0,2,6,0,0)
 | 47=>(0,11,3,4,6,0,0)
 | 48=>(0,1,7,9,13,0,0)
 | 49=>(0,1,7,9,13,0,0)
 | 50=>(0,6,8,9,11,0,0)
 | 51=>(1,2,12,13,8,3,0)
 | 52=>(0,8,0,2,6,0,0)
 | 53=>(0,8,0,2,6,0,0)
 | 54=>(0,9,1,5,6,0,0)
 | 55=>(0,9,1,5,6,0,0)
 | 56=>(0,8,0,2,6,0,0)
 | 57=>(0,8,2,6,0,0,0)
 | 58=>(0,8,0,2,6,0,0)
 | 59=>(0,8,2,6,0,0,0)
 | 60=>(0,9,1,5,6,0,0)
 | 61=>(0,8,0,2,6,0,0)
 | 62=>(0,1,7,9,13,0,0)
 | 63=>(0,8,0,2,6,0,0)
 | 64=>(0,8,0,2,6,0,0)
 | 65=>(0,8,2,6,0,0,0)
 | 66=>(0,8,0,2,6,0,0)
 | _=>(0,8,0,2,6,0,0)
lemma qv:∀ g:Fin 68,g.val≠6 ->
 let I:=bU g;let (k,a,b,c,d,e,f):=qI g;if k=0 then
  b∈I/\c∈I/\b≠c/\ac b a=true/\ac c a=true /\ac a d=true/\d≠b/\d≠c
 else if k=1 then
  d∈I/\e∈I/\a∉I/\b∉I/\c∉I /\ac d a=true/\ac e b=true/\ac a b=true /\ac a c=true/\c≠b/\(az b).card=3 /\decide (c.val<7)=decide (b.val<7)
 else
  e∈I/\f∈I/\a∉I /\ac a b=true/\ac a c=true/\ac a d=true /\ac e b=true/\ac f c=true /\b≠c/\d≠b/\d≠c /\(az b).card=3/\(az c).card=3 /\decide (b.val<7)=decide (c.val<7)/\decide (d.val<7)=decide (b.val<7):=by
 decide +kernel
lemma pL {D:Dag} (h:ai 14 D) (r:ar D) {pos:O->ℕ×_d} (a:bA 14 eW D pos) (E:aa 14 D={0,7}) (p:∀ x,(af 14 D x).card<=2):False:=by
 have F:(0:O)∈aa 14 D:=by rw[E];decide
 have K:(7:O)∈aa 14 D:=by rw[E];decide
 have L:(6:O)∉aa 14 D:=by rw[E];decide
 have M:(2:O)∉aa 14 D:=by rw[E];decide
 have N:(9:O)∉aa 14 D:=by rw[E];decide
 have S:(5:O)∉aa 14 D:=by rw[E];decide
 obtain⟨Z8,-,P,Q⟩:=cm h r a F (by decide:aP 0 8) V (p 8);obtain⟨Z1,-,R,G⟩:=cm h r a K (by decide:aP 7 1) V (p 1);obtain⟨e68,u,d,-,hf68'⟩:=bf h r a (by decide:aP 6 8);obtain⟨e28,w,e,-,hf28'⟩:=bf h r a (by decide:aP 2 8);obtain⟨e69,g,i,-,-⟩:=bf h r a (by decide:aP 6 9);obtain⟨e91,z,j,-,hf91'⟩:=bf h r a (by decide:aP 9 1);obtain⟨e95,B,k,-,-⟩:=bf h r a (by decide:aP 9 5);rw[P,_mi,_ms] at d e;have s:am e68=Z8:=d.resolve_left (fun q=>L (hf68' 0 F q▸F));have H:am e28=Z8:=e.resolve_left (fun q=>M (hf28' 0 F q▸F));have l:e28=e68:=by rw[<- aB e28,<-aB e68,H,s]
 rw[R,_mi,_ms] at j;have t:am e91=Z1:=j.resolve_left (fun q=>N (hf91' 7 K q▸K));have b:e68≠e69:=fun q=>Q 9 V V (by rw[<- s,q];exact i);have c:e91≠am e69:=fun q=>
  G 6 V V (by rw[<- t,q,aB];exact g)
 have m:e95=am e69:=by{rcases gG z i c (p 9) e95 B with C|C;{exact absurd (by rw[<- t,<-C];exact k) (G 5 V V)};{exact C}};have n:e69∈af 14 D 5:=by rw[<- aB e69,<-m];exact k
 obtain⟨f,T,I,J⟩:=bE h r (by decide:(az 6).card=3) (by decide:(6:O)≠2) (by decide:(6:O)≠5) (b3.1 V);rcases gG u g b (p 6) f T with rfl|rfl;{exact I (ak.1 (l▸w)).2.1};{exact J (ak.1 n).2.1}
lemma dn {D:Dag} (h:ai 14 D) (n:ar D) (I:bd 14 D<=(al 14 D).card) (j:Fin 68) (l:aa 14 D=bU j):False:=by
 classical
 obtain⟨b,v⟩:=bu h n;obtain⟨pos,i⟩:=bQ bs h (bF n);have p:aj 14 D b=∅:=by{have u:=bS h.1 b v;have J:=dX h.1 b v;exact card_eq_zero.1 (by omega)};have g:∀ x,(af 14 D x).card<=2:=fun x=>by{have u:=bj h n b v x;unfold aZ at u;rw[p] at u;simp only[filter_empty,_ce] at u;omega};by_cases F:j.val=6
 · have q:aa 14 D={0,7}:=by
    rw[l,show j=⟨6,V⟩ from _fe F];decide
   exact pL h n i q g
 · have m:=qv j F
   dsimp only at m;rcases w:qI j with ⟨k,a,b',c,d,e,f⟩;rw[w] at m;by_cases r:k=0
   · simp only[r,↓reduceIte] at m
     obtain⟨y,z,s⟩:=m;have K:=cx h n i (l▸y) (l▸z) s;have:=g a;omega
   · by_cases t:k=1
     · simp only[t,↓reduceIte] at m
       obtain⟨G,A,B,v',hc',s⟩:=m;exact dl h n i a b' c d e (l▸G) (l▸A) (l▸B) (l▸v') (l▸hc') s (g a) (g b')
     · simp only[r,t,↓reduceIte] at m
       obtain⟨A,H,B,s⟩:=m;exact fR h n i a b' c d e f (l▸A) (l▸H) (l▸B) s (g a) (g b') (g c)
lemma mX {D:Dag} (h:ai 14 D) (N:ar D) {pos:O->ℕ×_d} {P Q:ℕ×_d} (C:iQ D pos P Q) {x y i1 i2 vx j1 j2 vy q:O} (d:i1∈aa 14 D) (R:i2∈aa 14 D) (f:j1∈aa 14 D) (g:j2∈aa 14 D) (hg:x≠y/\q≠x/\bK y q=false/\(az x).card=3 /\i1≠i2/\ac i1 x=true/\ac i2 x=true/\ac x vx=true/\vx≠i1/\vx≠i2 /\j1≠j2/\ac j1 y=true/\ac j2 y=true/\ac y vy=true/\vy≠j1/\vy≠j2 /\ac i1 y=false/\ac i1 q=true):False:=by
 obtain⟨a,w,S,p⟩:=C;obtain⟨T,U,E,W,X,F,Y,Z,h0,h1,r,z,A,m,s,t,c,h2⟩:=hg;have h3:=cx h N a d R ⟨X,F,Y,Z,h0,h1⟩;have h4:=cx h N a f g ⟨r,z,A,m,s,t⟩;obtain⟨h5,h6⟩:=p x h3;obtain⟨G,H⟩:=p y h4;have b:pos i1∉af 14 D y:=by
  have u:=aJ a f ((ae _ _).1 z);have v:=aJ a g ((ae _ _).1 A);have l:pos j1≠pos j2:=fun e=>r (a.2 _ f _ g e);have j:i1≠j1:=fun e=>by subst e;rw[z] at c;exact Bool.noConfusion c
  have k:i1≠j2:=fun e=>by subst e;rw[A] at c;exact Bool.noConfusion c
  intro hm;by_cases i:vy∈aa 14 D
  · have I:=aJ a i (bm ((ae _ _).1 m))
    have n:i1≠vy:=fun e=>by{subst e;have:=(ae y i1).1 m;exact aH.1 c (bm this)};rcases aT u v I l (fun e=>s.symm (a.2 _ f _ i e)) (fun e=>t.symm (a.2 _ g _ i e)) (w y) (pos i1) hm with e|e|e;{exact j (a.2 _ d _ f e)};{exact k (a.2 _ d _ g e)};{exact n (a.2 _ d _ i e)}
  · obtain⟨ev,h7,-,B,-⟩:=bf h N a ((ae _ _).1 m)
    rcases aT u v h7 l (fun e=>i (B _ f e.symm▸f)) (fun e=>i (B _ g e.symm▸g)) (w y) (pos i1) hm with e|e|e;{exact j (a.2 _ d _ f e)};{exact k (a.2 _ d _ g e)};{exact i (B _ d e.symm▸d)}
 have J:P≠pos i1:=fun e=>b (e▸G);have K:Q≠pos i1:=fun e=>b (e▸H);have L:=aJ a d ((ae _ _).1 F);obtain⟨e,he,M,h8⟩:=bE h N W T U.symm (b3.1 E);rcases aT h5 h6 L S J K (w x) e he with rfl|rfl|rfl;{exact M (ak.1 G).2.1};{exact M (ak.1 H).2.1};{exact h8 ((a.1 i1 d).2.2.1 q ((ae _ _).1 h2))}
def fw (a:Fin 68):ℕ×O×O×O×O×O×O×O×O×O×O:=match a.val with
 | 0=>(0,0,0,0,0,0,0,0,0,0,0)
 | 1=>(0,0,0,0,0,0,0,0,0,0,0)
 | 2=>(0,0,0,0,0,0,0,0,0,0,0)
 | 3=>(0,0,0,0,0,0,0,0,0,0,0)
 | 4=>(0,0,0,0,0,0,0,0,0,0,0)
 | 5=>(0,0,0,0,0,0,0,0,0,0,0)
 | 6=>(0,0,0,0,0,0,0,0,0,0,0)
 | 7=>(0,0,0,0,0,0,0,0,0,0,0)
 | 8=>(0,0,0,0,0,0,0,0,0,0,0)
 | 9=>(0,0,0,0,0,0,0,0,0,0,0)
 | 10=>(0,0,0,0,0,0,0,0,0,0,0)
 | 11=>(0,8,13,0,2,6,1,2,4,10,0)
 | 12=>(0,0,0,0,0,0,0,0,0,0,0)
 | 13=>(0,12,13,3,2,5,1,2,4,7,0)
 | 14=>(0,8,10,2,0,6,0,4,5,12,0)
 | 15=>(2,13,1,2,4,3,11,12,7,4,2)
 | 16=>(0,11,12,4,3,6,2,3,5,10,0)
 | 17=>(2,10,0,4,5,1,9,13,7,5,4)
 | 18=>(0,9,10,1,5,6,4,5,0,7,0)
 | 19=>(0,10,12,4,5,0,2,5,3,11,0)
 | 20=>(1,8,0,2,6,1,13,9,7,2,0)
 | 21=>(1,13,2,4,1,3,11,12,7,4,0)
 | 22=>(1,10,4,5,0,1,9,13,7,5,0)
 | 23=>(0,0,0,0,0,0,0,0,0,0,0)
 | 24=>(1,13,1,4,2,6,9,11,8,1,0)
 | 25=>(1,10,4,5,0,2,12,13,8,5,0)
 | 26=>(0,0,0,0,0,0,0,0,0,0,0)
 | 27=>(1,8,0,2,6,1,13,7,9,2,0)
 | 28=>(1,12,2,3,5,1,13,7,9,2,0)
 | 29=>(1,13,2,4,1,5,10,12,9,4,0)
 | 30=>(0,8,12,0,2,6,2,3,5,10,0)
 | 31=>(0,8,10,2,0,6,0,4,5,12,0)
 | 32=>(0,8,10,2,0,6,0,4,5,12,0)
 | 33=>(0,11,12,4,3,6,2,3,5,10,0)
 | 34=>(0,9,10,1,5,6,0,4,5,7,0)
 | 35=>(0,8,10,2,0,6,0,4,5,12,0)
 | 36=>(0,9,10,1,5,6,4,5,0,7,0)
 | 37=>(0,9,10,1,5,6,4,5,0,7,0)
 | 38=>(0,8,9,2,6,0,5,6,1,12,0)
 | 39=>(0,8,10,2,0,6,0,4,5,12,0)
 | 40=>(0,0,0,0,0,0,0,0,0,0,0)
 | 41=>(0,10,12,4,5,0,2,5,3,11,0)
 | 42=>(0,11,13,3,4,6,1,4,2,7,0)
 | 43=>(0,9,10,1,5,6,4,5,0,7,0)
 | 44=>(0,0,0,0,0,0,0,0,0,0,0)
 | 45=>(0,8,12,0,2,6,2,3,5,10,0)
 | 46=>(0,8,10,2,0,6,0,4,5,12,0)
 | 47=>(0,11,12,4,3,6,2,3,5,10,0)
 | 48=>(0,1,8,7,9,13,0,2,6,3,0)
 | 49=>(0,1,13,7,9,13,2,4,1,3,0)
 | 50=>(0,6,11,8,9,11,3,4,6,0,0)
 | 51=>(0,0,0,0,0,0,0,0,0,0,0)
 | 52=>(0,8,10,2,0,6,0,4,5,12,0)
 | 53=>(0,8,9,0,2,6,1,5,6,10,0)
 | 54=>(0,9,10,1,5,6,0,4,5,7,0)
 | 55=>(0,9,10,1,5,6,4,5,0,7,0)
 | 56=>(0,8,9,0,2,6,5,6,1,10,0)
 | 57=>(0,8,9,2,6,0,1,5,6,12,0)
 | 58=>(0,8,10,2,0,6,0,4,5,12,0)
 | 59=>(0,8,9,2,6,0,5,6,1,12,0)
 | 60=>(0,9,10,1,5,6,4,5,0,7,0)
 | 61=>(0,8,10,2,0,6,0,4,5,12,0)
 | 62=>(0,1,8,7,9,13,0,2,6,3,0)
 | 63=>(0,8,9,0,2,6,1,5,6,10,0)
 | 64=>(0,8,9,0,2,6,1,5,6,10,0)
 | 65=>(0,8,9,2,6,0,1,5,6,12,0)
 | 66=>(0,8,9,0,2,6,5,6,1,10,0)
 | _=>(0,8,9,0,2,6,1,5,6,10,0)
lemma o1:∀ a:Fin 68,3<=(bU a).card ->a.val≠12->a.val≠23->a.val≠26->a.val≠40->a.val≠44->a.val≠51 ->(fw a).1=0 ->
 let I:=bU a;let (_,a1,a2,a3,a4,_,a6,a7,_,a9,_):=fw a;a3∈I/\a4∈I/\a6∈I/\a7∈I/\a1≠a2/\a9≠a1/\bK a2 a9=false/\(az a1).card=3:=by
 decide +kernel
lemma o2:∀ a:Fin 68,3<=(bU a).card ->a.val≠12->a.val≠23->a.val≠26->a.val≠40->a.val≠44->a.val≠51 ->(fw a).1=0 ->
 let (_,a1,_,a3,a4,a5,_,_,_,_,_):=fw a;a3≠a4/\ac a3 a1=true/\ac a4 a1=true/\ac a1 a5=true/\a5≠a3/\a5≠a4:=by
 decide +kernel
lemma o3:∀ a:Fin 68,3<=(bU a).card ->a.val≠12->a.val≠23->a.val≠26->a.val≠40->a.val≠44->a.val≠51 ->(fw a).1=0 ->
 let (_,_,a2,a3,_,_,a6,a7,a8,a9,_):=fw a;a6≠a7/\ac a6 a2=true/\ac a7 a2=true/\ac a2 a8=true/\a8≠a6/\a8≠a7 /\
 ac a3 a2=false/\ac a3 a9=true:=by
 decide +kernel
lemma pM:∀ a:Fin 68,3<=(bU a).card ->a.val≠12->a.val≠23->a.val≠26->a.val≠40->a.val≠44->a.val≠51 ->(fw a).1=1 ->
 let I:=bU a;let (_,a1,a2,a3,a4,a5,a6,a7,a8,a9,_):=fw a
 (I.card=3/\a2∈I/\a3∈I/\(az a1).card=3/\a2≠a3/\ac a2 a1=true/\ac a3 a1=true/\ac a1 a4=true/\a4≠a2/\a4≠a3) /\
 (a8∈I/\a9∈I/\a5∉I/\a6∉I/\a7∉I/\a5≠a1/\a6≠a1) /\
 (ac a8 a5=true/\ac a9 a6=true/\ac a5 a6=true /\ac a5 a7=true/\a7≠a6/\(az a6).card=3/\decide (a7.val<7)=decide (a6.val<7)):=by
 decide +kernel
lemma pN:∀ a:Fin 68,3<=(bU a).card ->a.val≠12->a.val≠23->a.val≠26->a.val≠40->a.val≠44->a.val≠51 ->(fw a).1≠0->(fw a).1≠1 ->
 let I:=bU a;let (_,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10):=fw a
 (I.card=3/\a2∈I/\a3∈I/\(az a1).card=3/\a2≠a3/\ac a2 a1=true/\ac a3 a1=true/\ac a1 a4=true/\a4≠a2/\a4≠a3) /\
 (a9∈I/\a10∈I/\a5∉I/\a5≠a1/\a6≠a1/\a7≠a1) /\
 (ac a5 a6=true/\ac a5 a7=true/\ac a5 a8=true /\ac a9 a6=true/\ac a10 a7=true/\a6≠a7/\a8≠a6/\a8≠a7 /\(az a6).card=3/\(az a7).card=3/\decide (a6.val<7)=decide (a7.val<7)/\decide (a8.val<7)=decide (a6.val<7)):=by
 decide +kernel
lemma im {D:Dag} (h:ai 14 D) (N:ar D) (R:bL 14 D=0) {pos:O->ℕ×_d} {P Q:ℕ×_d} (z:iQ D pos P Q) (x y ix iy vx qx qy:O) (b:ix∈aa 14 D) (c:iy∈aa 14 D) (m:vx∉aa 14 D) (hg:x≠y/\ix≠iy/\(az x).card=3/\(az y).card=3 /\ac ix x=true/\ac iy y=true/\ac ix y=false /\ac x vx=true/\ac ix qx=true/\qx≠x/\bK y qx=false /\ac iy qy=true/\qy≠y/\bK x qy=false) (S:3<=(af 14 D x).card) (T:3<=(af 14 D y).card):False:=by
 obtain⟨a,n,A,j⟩:=z;obtain⟨B,k,U,W,g1,g2,g3,g4,g5,C,g6,g7,E,g8⟩:=hg;obtain⟨q,r⟩:=j x S;obtain⟨s,t⟩:=j y T;have F:=aJ a b ((ae _ _).1 g1);have X:=aJ a c ((ae _ _).1 g2);by_cases d:pos ix∈af 14 D y
 · by_cases f:pos iy∈af 14 D x
   · obtain⟨ev,Y,G,H,-⟩:=bf h N a ((ae _ _).1 g4)
     have u:pos ix≠pos iy:=fun e=>k (a.2 _ b _ c e);have I:pos ix≠ev:=fun e=>m (H _ b e.symm▸b);have J:pos iy≠ev:=fun e=>m (H _ c e.symm▸c);have Z:=aT F f Y u I J (n x)
     have v:=cT h N R a b ((ae _ _).1 g1) (fun p hp K l=>by
      rcases Z p hp with rfl|rfl|rfl;{exact K rfl};{exact k.symm (_ms.1 (l (cd a c)))}
      · exact m (_ms.1 (l (ak.1 G).2.1)▸b))
     exact aH.1 g3 ((v y).1 (ak.1 d).2.1)
   · have g:P≠pos iy:=fun e=>f (e▸q)
     have i:Q≠pos iy:=fun e=>f (e▸r);obtain⟨e,he,L,w⟩:=bE h N W B.symm E.symm (b3.1 g8);rcases aT s t X A g i (n y) e he with rfl|rfl|rfl;{exact L (ak.1 q).2.1};{exact L (ak.1 r).2.1};{exact w ((a.1 iy c).2.2.1 qy ((ae _ _).1 g7))}
 · have g:P≠pos ix:=fun e=>d (e▸s)
   have i:Q≠pos ix:=fun e=>d (e▸t);obtain⟨e,he,M,w⟩:=bE h N U B C.symm (b3.1 g6);rcases aT q r F A g i (n x) e he with rfl|rfl|rfl;{exact M (ak.1 s).2.1};{exact M (ak.1 t).2.1};{exact w ((a.1 ix b).2.2.1 qx ((ae _ _).1 g5))}
lemma pO {D:Dag} (h:ai 14 D) (z:ar D) (hB0:bL 14 D=0) (hB:bd 14 D=(al 14 D).card+1) (hI:aa 14 D={0,1,3}):False:=by
 obtain⟨pos,P,Q,i⟩:=fq h z hB;have b:=i.1;have d:∀ v:O,v∈({0,1,3}:o)->v∈aa 14 D:=fun v hv=>hI▸hv;have l:∀ v:O,v∉({0,1,3}:o)->v∉aa 14 D:=fun v hv=>hI▸hv;have f:∀(u1 N c t J A u R S T U:O),R∈aa 14 D->S∈aa 14 D->T∈aa 14 D->U∈aa 14 D ->u1∉aa 14 D->N∉aa 14 D ->(t≠J/\t≠A/\t≠u/\J≠A/\J≠u/\A≠u /\t≠c/\J≠c/\A≠c/\u≠c /\ac u1 t=true/\ac u1 J=true/\ac u1 c=true /\ac N A=true/\ac N u=true/\ac N c=true /\ac R t=true/\ac S J=true/\ac T A=true/\ac U u=true /\(az t).card=3/\(az J).card=3/\(az A).card=3/\(az u).card=3 /\decide (t.val<7)=decide (J.val<7)/\decide (t.val<7)=decide (A.val<7) /\decide (t.val<7)=decide (u.val<7)/\decide (t.val<7)=decide (c.val<7)) ->(af 14 D t).card<=2->(af 14 D J).card<=2 ->(af 14 D A).card<=2->(af 14 D u).card<=2->False:=by
  intro u1 N c t J A u R S T U B C E F hu1 hu2 hg la1 lb1 la2 lb2;obtain⟨hab1,ha12,ha1b2,hb1a2,hb12,hab2,W,X,ha2c,hb2c,gu1a,gu1b,gu1c,gu2a,gu2b,gu2c,gia1,gib1,gia2,gib2,hda1,hdb1,hda2,hdb2,K,L,Y,m⟩:=hg;have hu1_3:3<=(af 14 D u1).card:=by{by_contra M;exact fR h z b u1 t J c R S B C hu1 ⟨gu1a,gu1b,gu1c,gia1,gib1,hab1,W.symm,X.symm,hda1,hdb1,K,m.symm⟩ (by omega) la1 lb1};have hu2_3:3<=(af 14 D N).card:=by{by_contra M;exact fR h z b N A u c T U E F hu2 ⟨gu2a,gu2b,gu2c,gia2,gib2,hab2,ha2c.symm,hb2c.symm,hda2,hdb2,L.symm.trans Y,m.symm.trans L⟩ (by omega) la2 lb2};obtain⟨Da1,-,hWa1,n⟩:=cm h z b B ((ae _ _).1 gia1) hda1 la1;obtain⟨Db1,-,hWb1,G⟩:=cm h z b C ((ae _ _).1 gib1) hdb1 lb1;obtain⟨Da2,-,hWa2,hpa2⟩:=cm h z b E ((ae _ _).1 gia2) hda2 la2;obtain⟨Db2,-,hWb2,hpb2⟩:=cm h z b F ((ae _ _).1 gib2) hdb2 lb2;obtain⟨e1a,h1a_u,Z,-,hf1a'⟩:=bf h z b ((ae _ _).1 gu1a);obtain⟨e1b,h1b_u,h0,-,hf1b'⟩:=bf h z b ((ae _ _).1 gu1b);obtain⟨e1c,h1c_u,h4,-,-⟩:=bf h z b ((ae _ _).1 gu1c);obtain⟨e2a,h5,h6,-,hf2a'⟩:=bf h z b ((ae _ _).1 gu2a);obtain⟨e2b,h7,ha,-,hf2b'⟩:=bf h z b ((ae _ _).1 gu2b);obtain⟨e2c,hb,k,-,-⟩:=bf h z b ((ae _ _).1 gu2c);rw[hWa1,_mi,_ms] at Z;have p:am e1a=Da1:=Z.resolve_left (fun g=>hu1 (hf1a' R B g▸B));rw[hWb1,_mi,_ms] at h0;have q:am e1b=Db1:=h0.resolve_left (fun g=>hu1 (hf1b' S C g▸C));rw[hWa2,_mi,_ms] at h6;have H:am e2a=Da2:=h6.resolve_left (fun g=>hu2 (hf2a' T E g▸E));rw[hWb2,_mi,_ms] at ha;have I:am e2b=Db2:=ha.resolve_left (fun g=>hu2 (hf2b' U F g▸F));have hDa1_in:Da1∈af 14 D t:=by rw[hWa1];simp
  have hd:Db1∈af 14 D J:=by rw[hWb1];simp
  have r:Da2∈af 14 D A:=by rw[hWa2];simp
  have j:Db2∈af 14 D u:=by rw[hWb2];simp
  have h1_ab:e1a≠e1b:=fun g=>n J hab1.symm K.symm (by rw[<- p,g,q];exact hd);have h1_ac:e1a≠e1c:=fun g=>n c W.symm m.symm (by rw[<- p,g];exact h4);have h1_bc:e1b≠e1c:=fun g=>G c X.symm (m.symm.trans K) (by rw[<- q,g];exact h4);have he:e2a≠e2b:=fun g=>hpa2 u hab2.symm (Y.symm.trans L) (by rw[<- H,g,I];exact j);have hf:e2a≠e2c:=fun g=>hpa2 c ha2c.symm (m.symm.trans L) (by rw[<- H,g];exact k);have hi:e2b≠e2c:=fun g=>hpb2 c hb2c.symm (m.symm.trans Y) (by rw[<- I,g];exact k);obtain⟨hPu1,hQu1⟩:=i.2.2.2 u1 hu1_3;obtain⟨hPu2,hQu2⟩:=i.2.2.2 N hu2_3;have s:∀ e,e∈af 14 D u1->e∈af 14 D N->e=e1c:=by
   intro e he1 he2;rcases aT h1a_u h1b_u h1c_u h1_ab h1_ac h1_bc (i.2.1 u1) e he1 with hj|hj|hj
   · rw[hj] at he2
     rcases aT h5 h7 hb he hf hi (i.2.1 N) e1a he2 with g|g|g;{exact absurd (by rw[<- p,g,H];exact r) (n A ha12.symm L.symm)};{exact absurd (by rw[<- p,g,I];exact j) (n u ha1b2.symm Y.symm)};{exact absurd (by rw[<- p,g];exact k) (n c W.symm m.symm)}
   · rw[hj] at he2
     rcases aT h5 h7 hb he hf hi (i.2.1 N) e1b he2 with g|g|g;{exact absurd (by rw[<- q,g,H];exact r) (G A hb1a2.symm (L.symm.trans K))};{exact absurd (by rw[<- q,g,I];exact j) (G u hb12.symm (Y.symm.trans K))};{exact absurd (by rw[<- q,g];exact k) (G c X.symm (m.symm.trans K))}
   · exact hj
  exact i.2.2.1 ((s P hPu1 hPu2).trans (s Q hQu1 hQu2).symm)
 have a:∀(x y ix iy vx qx qy:O),ix∈aa 14 D->iy∈aa 14 D->vx∉aa 14 D ->(x≠y/\ix≠iy/\(az x).card=3/\(az y).card=3 /\ac ix x=true/\ac iy y=true/\ac ix y=false /\ac x vx=true/\ac ix qx=true/\qx≠x/\bK y qx=false /\ac iy qy=true/\qy≠y/\bK x qy=false) ->¬ (3<=(af 14 D x).card/\3<=(af 14 D y).card):=fun x y ix iy vx qx qy h1 h2 h3 hg ⟨hx,hy⟩=>
  im h z hB0 i x y ix iy vx qx qy h1 h2 h3 hg hx hy
 by_cases hA:3<=(af 14 D 8).card\/3<=(af 14 D 10).card
 · have l9:(af 14 D 9).card<=2:=by
    rcases hA with h8|w;{by_contra M;exact a 8 9 0 1 6 10 13 (d 0 V) (d 1 V) (l 6 V) V ⟨h8,by omega⟩};{by_contra M;exact a 10 9 0 1 5 8 13 (d 0 V) (d 1 V) (l 5 V) V ⟨w,by omega⟩}
   have l13:(af 14 D 13).card<=2:=by{rcases hA with h8|w;{by_contra M;exact a 8 13 0 1 6 10 9 (d 0 V) (d 1 V) (l 6 V) V ⟨h8,by omega⟩};{by_contra M;exact a 10 13 0 1 5 8 9 (d 0 V) (d 1 V) (l 5 V) V ⟨w,by omega⟩}};have l11:(af 14 D 11).card<=2:=by{rcases hA with h8|w;{by_contra M;exact a 8 11 0 3 6 10 12 (d 0 V) (d 3 V) (l 6 V) V ⟨h8,by omega⟩};{by_contra M;exact a 10 11 0 3 5 8 12 (d 0 V) (d 3 V) (l 5 V) V ⟨w,by omega⟩}};have l12:(af 14 D 12).card<=2:=by{rcases hA with h8|w;{by_contra M;exact a 8 12 0 3 6 10 11 (d 0 V) (d 3 V) (l 6 V) V ⟨h8,by omega⟩};{by_contra M;exact a 10 12 0 3 5 8 11 (d 0 V) (d 3 V) (l 5 V) V ⟨w,by omega⟩}};exact f 2 6 8 12 13 9 11 3 1 1 3 (d 3 V) (d 1 V) (d 1 V) (d 3 V) (l 2 V) (l 6 V) V l12 l13 l9 l11
 · have l8:(af 14 D 8).card<=2:=by omega
   have l10:(af 14 D 10).card<=2:=by omega
   by_cases hB':3<=(af 14 D 9).card\/3<=(af 14 D 13).card
   · have l11:(af 14 D 11).card<=2:=by
      rcases hB' with h9|h13;{by_contra M;exact a 9 11 1 3 6 13 12 (d 1 V) (d 3 V) (l 6 V) V ⟨h9,by omega⟩};{by_contra M;exact a 13 11 1 3 4 9 12 (d 1 V) (d 3 V) (l 4 V) V ⟨h13,by omega⟩}
     have l12:(af 14 D 12).card<=2:=by{rcases hB' with h9|h13;{by_contra M;exact a 9 12 1 3 6 13 11 (d 1 V) (d 3 V) (l 6 V) V ⟨h9,by omega⟩};{by_contra M;exact a 13 12 1 3 4 9 11 (d 1 V) (d 3 V) (l 4 V) V ⟨h13,by omega⟩}};exact f 2 4 13 8 12 10 11 0 3 0 3 (d 0 V) (d 3 V) (d 0 V) (d 3 V) (l 2 V) (l 4 V) V l8 l12 l10 l11
   · have l9:(af 14 D 9).card<=2:=by omega
     have l13:(af 14 D 13).card<=2:=by omega
     exact f 2 5 12 8 13 9 10 0 1 1 0 (d 0 V) (d 1 V) (d 1 V) (d 0 V) (l 2 V) (l 5 V) V l8 l13 l9 l10
lemma jp {D:Dag} (h:ai 14 D) (l:ar D) (t:bL 14 D=0) (hB:bd 14 D=(al 14 D).card+1) (u1 u2 iu a1 b1 a2 b2 ia1 ib1 ia2 ib2 q1a q2a q1b q2b va1 va2:O) (c:iu∈aa 14 D) (g:ia1∈aa 14 D) (i:ib1∈aa 14 D) (j:ia2∈aa 14 D) (k:ib2∈aa 14 D) (u:u1∉aa 14 D) (v:u2∉aa 14 D) (h0:a1∉aa 14 D) (h1:b1∉aa 14 D) (h2:a2∉aa 14 D) (h3:b2∉aa 14 D) (hF:va1∉aa 14 D) (hG:va2∉aa 14 D) (hg:a1≠b1/\a1≠a2/\a1≠b2/\b1≠a2/\b1≠b2/\a2≠b2 /\ia1≠ib1/\ia2≠ib2/\iu≠ia1/\iu≠ib1/\iu≠ia2/\iu≠ib2 /\ac iu u1=true/\ac iu u2=true /\ac u1 a1=true/\ac u1 b1=true /\ac u2 a2=true/\ac u2 b2=true /\ac ia1 a1=true/\ac ib1 b1=true /\ac ia2 a2=true/\ac ib2 b2=true /\ac iu a1=false/\ac iu b1=false/\ac iu a2=false/\ac iu b2=false /\ac ia1 b1=false/\ac ia2 b2=false /\ac a1 va1=true/\ac ia1 q1a=true/\q1a≠a1/\bK b1 q1a=false /\ac ib1 q2a=true/\q2a≠b1/\bK a1 q2a=false /\ac a2 va2=true/\ac ia2 q1b=true/\q1b≠a2/\bK b2 q1b=false /\ac ib2 q2b=true/\q2b≠b2/\bK a2 q2b=false /\(az a1).card=3/\(az b1).card=3/\(az a2).card=3/\(az b2).card=3 /\decide (a1.val<7)=decide (b1.val<7)/\decide (a1.val<7)=decide (a2.val<7) /\decide (a1.val<7)=decide (b2.val<7)):False:=by
 obtain⟨pos,P,Q,b⟩:=fq h l hB;have a:=b.1;obtain⟨r,hH,hd,he,hI,s,hf,hi,hJ,hj,hK,hk,gu1i,gu2i,gu1a,gu1b,gu2a,gu2b,gia1,gib1,gia2,gib2,hl,hm,hn,ho,h4,h5,ga1v,gq1a,hL,gq1b,gq2b,hM,gq2a,ga2v,gq1a2,hp,gq1b2,gq2b2,hq,gq2a2,w,x,y,z,A,B,C⟩:=hg;have p:3<=(af 14 D u1).card:=by{by_contra hc;have hr:3<=(af 14 D a1).card:=by{by_contra hs;exact dl h l a u1 a1 b1 iu ia1 c g u h0 h1 ⟨gu1i,gia1,gu1a,gu1b,r.symm,w,A.symm⟩ (by omega) (by omega)};have ht:3<=(af 14 D b1).card:=by{by_contra hs;exact dl h l a u1 b1 a1 iu ib1 c i u h1 h0 ⟨gu1i,gib1,gu1b,gu1a,r,x,A⟩ (by omega) (by omega)};exact im h l t b a1 b1 ia1 ib1 va1 q1a q2a g i hF ⟨r,hf,w,x,gia1,gib1,h4,ga1v,gq1a,hL,gq1b,gq2b,hM,gq2a⟩ hr ht};have q:3<=(af 14 D u2).card:=by{by_contra hc;have hu:3<=(af 14 D a2).card:=by{by_contra hs;exact dl h l a u2 a2 b2 iu ia2 c j v h2 h3 ⟨gu2i,gia2,gu2a,gu2b,s.symm,y,C.symm.trans B⟩ (by omega) (by omega)};have hv:3<=(af 14 D b2).card:=by{by_contra hs;exact dl h l a u2 b2 a2 iu ib2 c k v h3 h2 ⟨gu2i,gib2,gu2b,gu2a,s,z,B.symm.trans C⟩ (by omega) (by omega)};exact im h l t b a2 b2 ia2 ib2 va2 q1b q2b j k hG ⟨s,hi,y,z,gia2,gib2,h5,ga2v,gq1a2,hp,gq1b2,gq2b2,hq,gq2a2⟩ hu hv};have la1:(af 14 D a1).card<=2:=by{by_contra hc;exact gH h l t b u1 a1 iu ia1 c g u h0 ⟨hJ,gu1i,gia1,gu1a,hl⟩ p (by omega)};have lb1:(af 14 D b1).card<=2:=by{by_contra hc;exact gH h l t b u1 b1 iu ib1 c i u h1 ⟨hj,gu1i,gib1,gu1b,hm⟩ p (by omega)};have la2:(af 14 D a2).card<=2:=by{by_contra hc;exact gH h l t b u2 a2 iu ia2 c j v h2 ⟨hK,gu2i,gia2,gu2a,hn⟩ q (by omega)};have lb2:(af 14 D b2).card<=2:=by{by_contra hc;exact gH h l t b u2 b2 iu ib2 c k v h3 ⟨hk,gu2i,gib2,gu2b,ho⟩ q (by omega)};obtain⟨Da1,-,h7,E⟩:=cm h l a g ((ae _ _).1 gia1) w la1;obtain⟨Db1,-,h8,h9⟩:=cm h l a i ((ae _ _).1 gib1) x lb1;obtain⟨Da2,-,ha,hpa2⟩:=cm h l a j ((ae _ _).1 gia2) y la2;obtain⟨Db2,-,hb,hpb2⟩:=cm h l a k ((ae _ _).1 gib2) z lb2;obtain⟨e1a,hw,F,hfa1,hf1a'⟩:=bf h l a ((ae _ _).1 gu1a);obtain⟨e1b,hy,G,hfb1,hf1b'⟩:=bf h l a ((ae _ _).1 gu1b);obtain⟨e2a,H,I,hfa2,hf2a'⟩:=bf h l a ((ae _ _).1 gu2a);obtain⟨e2b,J,K,hfb2,hf2b'⟩:=bf h l a ((ae _ _).1 gu2b);rw[h7,_mi,_ms] at F;have L:am e1a=Da1:=F.resolve_left (fun d=>u (hf1a' ia1 g d▸g));rw[h8,_mi,_ms] at G;have M:am e1b=Db1:=G.resolve_left (fun d=>u (hf1b' ib1 i d▸i));rw[ha,_mi,_ms] at I;have N:am e2a=Da2:=I.resolve_left (fun d=>v (hf2a' ia2 j d▸j));rw[hb,_mi,_ms] at K;have R:am e2b=Db2:=K.resolve_left (fun d=>v (hf2b' ib2 k d▸k));have hDa1_in:Da1∈af 14 D a1:=by rw[h7];simp
 have S:Db1∈af 14 D b1:=by rw[h8];simp
 have m:Da2∈af 14 D a2:=by rw[ha];simp
 have f:Db2∈af 14 D b2:=by rw[hb];simp
 have hp1:=aJ a c ((ae _ _).1 gu1i);have hp2:=aJ a c ((ae _ _).1 gu2i);have hE:e1a≠e1b:=fun d=>E b1 r.symm A.symm (by rw[<- L,d,M];exact S);have T:e1a≠pos iu:=fun d=>h0 (hfa1 iu c d▸c);have U:e1b≠pos iu:=fun d=>h1 (hfb1 iu c d▸c);have W:e2a≠e2b:=fun d=>hpa2 b2 s.symm (C.symm.trans B) (by rw[<- N,d,R];exact f);have X:e2a≠pos iu:=fun d=>h2 (hfa2 iu c d▸c);have Y:e2b≠pos iu:=fun d=>h3 (hfb2 iu c d▸c);obtain⟨hPu1,hQu1⟩:=b.2.2.2 u1 p;obtain⟨hPu2,hQu2⟩:=b.2.2.2 u2 q;have n:∀ e,e∈af 14 D u1->e∈af 14 D u2->e=pos iu:=by
  intro e he1 h6;rcases aT hw hy hp1 hE T U (b.2.1 u1) e he1 with Z|Z|Z
  · rw[Z] at h6
    rcases aT H J hp2 W X Y (b.2.1 u2) e1a h6 with d|d|d;{exact absurd (by rw[<- L,d,N];exact m) (E a2 hH.symm B.symm)};{exact absurd (by rw[<- L,d,R];exact f) (E b2 hd.symm C.symm)};{exact absurd d T}
  · rw[Z] at h6
    rcases aT H J hp2 W X Y (b.2.1 u2) e1b h6 with d|d|d;{exact absurd (by rw[<- M,d,N];exact m) (h9 a2 he.symm (B.symm.trans A))};{exact absurd (by rw[<- M,d,R];exact f) (h9 b2 hI.symm (C.symm.trans A))};{exact absurd d U}
  · exact Z
 exact b.2.2.1 ((n P hPu1 hPu2).trans (n Q hQu1 hQu2).symm)
lemma pP {D:Dag} (h:ai 14 D) (f:ar D) (c:bL 14 D=0) (g:bd 14 D=(al 14 D).card+1) (e:aa 14 D={1,3,8}):False:=by
 have b:∀ v:O,v∈({1,3,8}:o)->v∈aa 14 D:=fun v d=>e▸d;have a:∀ v:O,v∉({1,3,8}:o)->v∉aa 14 D:=fun v d=>e▸d;exact jp h f c g 2 6 8 12 13 11 9 3 1 3 1 7 7 7 7 5 4 (b 8 V) (b 3 V) (b 1 V) (b 3 V) (b 1 V) (a 2 V) (a 6 V) (a 12 V) (a 13 V) (a 11 V) (a 9 V) (a 5 V) (a 4 V) V
lemma pQ {D:Dag} (h:ai 14 D) (f:ar D) (c:bL 14 D=0) (g:bd 14 D=(al 14 D).card+1) (e:aa 14 D={4,7,8}):False:=by
 have b:∀ v:O,v∈({4,7,8}:o)->v∈aa 14 D:=fun v d=>e▸d;have a:∀ v:O,v∉({4,7,8}:o)->v∉aa 14 D:=fun v d=>e▸d;exact jp h f c g 13 11 4 1 2 3 6 7 8 7 8 3 0 1 0 9 12 (b 4 V) (b 7 V) (b 8 V) (b 7 V) (b 8 V) (a 13 V) (a 11 V) (a 1 V) (a 2 V) (a 3 V) (a 6 V) (a 9 V) (a 12 V) V
lemma ky {D:Dag} (h:ai 14 D) (r:ar D) (hB:bd 14 D=(al 14 D).card+1) (l:(4:O)∈aa 14 D) (m:(5:O)∈aa 14 D) (w:(7:O)∈aa 14 D) (x:(1:O)∉aa 14 D) (T:(6:O)∉aa 14 D) (n:(9:O)∉aa 14 D) (A:(13:O)∉aa 14 D):False:=by
 obtain⟨pos,P,Q,U⟩:=fq h r hB;obtain⟨a,p,y,g⟩:=U;have C:=cx h r a l m (by decide:(4:O)≠5/\ac 4 10=true /\ac 5 10=true/\ac 10 0=true/\(0:O)≠4/\(0:O)≠5);obtain⟨i,j⟩:=g 10 C;have W:=aJ a l (by decide:aP 4 10);have X:=aJ a m (by decide:aP 5 10);have B:pos 4≠pos 5:=fun e=>absurd (a.2 _ l _ m e) V;by_cases Y:3<=(af 14 D 1).card
 · obtain⟨Z,h0⟩:=g 1 Y
   have s:pos 4=P\/pos 4=Q:=by{by_contra d;rw[not_or] at d;obtain⟨e,q,c,E⟩:=bE h r (by decide:(az 10).card=3) (by decide:(10:O)≠1) (by decide:(10:O)≠11) (b3.1 (by decide:bK 1 11=false));rcases aT i j W y (Ne.symm d.1) (Ne.symm d.2) (p 10) e q with rfl|rfl|rfl;{exact c (ak.1 Z).2.1};{exact c (ak.1 h0).2.1};{exact E ((a.1 4 l).2.2.1 11 V)}};have t:pos 5=P\/pos 5=Q:=by{by_contra f;rw[not_or] at f;obtain⟨e,q,c,F⟩:=bE h r (by decide:(az 10).card=3) (by decide:(10:O)≠1) (by decide:(10:O)≠12) (b3.1 (by decide:bK 1 12=false));rcases aT i j X y (Ne.symm f.1) (Ne.symm f.2) (p 10) e q with rfl|rfl|rfl;{exact c (ak.1 Z).2.1};{exact c (ak.1 h0).2.1};{exact F ((a.1 5 m).2.2.1 12 V)}};have G:pos 4∈af 14 D 1:=by rcases s with rfl|rfl <;> assumption
   have H:pos 5∈af 14 D 1:=by rcases t with rfl|rfl <;> assumption
   have I:=aJ a w (by decide:aP 7 1);obtain⟨e19,h1,-,J,-⟩:=bf h r a (by decide:aP 1 9);rcases aT G H I B (fun e=>absurd (a.2 _ l _ w e) V) (fun e=>absurd (a.2 _ m _ w e) V) (p 1) e19 h1 with u|u|u;{exact n (J 4 l u▸l)};{exact n (J 5 m u▸m)};{exact n (J 7 w u▸w)}
 · have l1:(af 14 D 1).card<=2:=by omega
   have h2:3<=(af 14 D 9).card:=by{by_contra hc;exact dl h r a 1 9 13 7 5 w m x n A V l1 (by omega)};have K:3<=(af 14 D 13).card:=by{by_contra hc;exact dl h r a 1 13 9 7 4 w l x A n V l1 (by omega)};obtain⟨hP9,hQ9⟩:=g 9 h2;obtain⟨h3,h6⟩:=g 13 K;have s:pos 4=P\/pos 4=Q:=by{by_contra d;rw[not_or] at d;obtain⟨e,q,k,b⟩:=bE h r (by decide:(az 10).card=3) (by decide:(10:O)≠9) (by decide:(10:O)≠13) (b3.1 (by decide:bK 9 13=false));rcases aT i j W y (Ne.symm d.1) (Ne.symm d.2) (p 10) e q with rfl|rfl|rfl;{exact k (ak.1 hP9).2.1};{exact k (ak.1 hQ9).2.1};{exact b ((a.1 4 l).2.2.1 13 V)}};have t:pos 5=P\/pos 5=Q:=by{by_contra f;rw[not_or] at f;obtain⟨e,q,b,k⟩:=bE h r (by decide:(az 10).card=3) (by decide:(10:O)≠13) (by decide:(10:O)≠9) (b3.1 (by decide:bK 13 9=false));rcases aT i j X y (Ne.symm f.1) (Ne.symm f.2) (p 10) e q with rfl|rfl|rfl;{exact b (ak.1 h3).2.1};{exact b (ak.1 h6).2.1};{exact k ((a.1 5 m).2.2.1 9 V)}};have L:pos 4∈af 14 D 9:=by rcases s with rfl|rfl <;> assumption
   have M:pos 5∈af 14 D 9:=by rcases t with rfl|rfl <;> assumption
   obtain⟨e96,N,R,h8,-⟩:=bf h r a (by decide:aP 9 6);obtain⟨e91,S,v,h9,J'⟩:=bf h r a (by decide:aP 9 1);have z:e91=e96:=by{rcases aT L M N B (fun e=>T (h8 4 l e.symm▸l)) (fun e=>T (h8 5 m e.symm▸m)) (p 9) e91 S with q|q|q;{exact absurd q (fun hh=>x (h9 4 l hh▸l))};{exact absurd q (fun hh=>x (h9 5 m hh▸m))};{exact q}};obtain⟨Z1,-,hW1,hp1⟩:=cm h r a w (by decide:aP 7 1) V l1;rw[hW1,_mi,_ms] at v;have hZ1:am e91=Z1:=v.resolve_left (fun hh=>n (J' 7 w hh▸w));exact hp1 6 V V (by rw[<- hZ1,z];exact R)
lemma pR {D:Dag} (h:ai 14 D) (s:ar D) (hB:bd 14 D=(al 14 D).card+1) (hI:aa 14 D={1,3,8,10}):False:=by
 obtain⟨pos,P,Q,R⟩:=fq h s hB;obtain⟨d,q,t,k⟩:=R;have g:∀ v:O,v∈({1,3,8,10}:o)->v∈aa 14 D:=fun v hv=>hI▸hv;have f:∀ v:O,v∉({1,3,8,10}:o)->v∉aa 14 D:=fun v hv=>hI▸hv;have c:∀(x y n p z w v B C:O),n∈aa 14 D->p∈aa 14 D->B∈aa 14 D->C∈aa 14 D ->x∉aa 14 D->y∉aa 14 D->z∉aa 14 D->w∉aa 14 D->v∉aa 14 D ->(n≠p/\B≠n/\B≠p/\C≠n/\C≠p /\ac n x=true/\ac p y=true/\ac x y=true /\ac B z=true/\ac C w=true/\ac z w=true /\ac z v=true/\v≠w/\(az w).card=3 /\decide (v.val<7)=decide (w.val<7)) ->3<=(af 14 D x).card->3<=(af 14 D y).card->False:=by
  intro x y n p z w v B C l m S T hnx hny U W hnv hg hx3 hy3;obtain⟨X,hzx,hzy,hwx,hwy,gx,gy,gxy,gz,gw,gzw,gzv,hvw,hdw,Y⟩:=hg;obtain⟨Z,h0⟩:=k x hx3;obtain⟨h1,h2⟩:=k y hy3;obtain⟨e,E,F,hfy,hfx⟩:=bf h s d ((ae _ _).1 gxy);have heP:e≠P:=fun j=>el h.1 (j▸h1) F;have heQ:e≠Q:=fun j=>el h.1 (j▸h2) F;have h5:am e≠P:=fun j=>el h.1 Z (by rw[<- j,aB];exact E);have h7:am e≠Q:=fun j=>el h.1 h0 (by rw[<- j,aB];exact E);have hpx:=aJ d l ((ae _ _).1 gx);have hpy:=aJ d m ((ae _ _).1 gy);have u:pos n=P\/pos n=Q:=by{rcases aT Z h0 E t heP.symm heQ.symm (q x) (pos n) hpx with j|j|j;{exact Or.inl j};{exact Or.inr j};{exact absurd j (fun G=>hny (hfy n l G.symm▸l))}};have A:pos p=P\/pos p=Q:=by{rcases aT h1 h2 F t h5.symm h7.symm (q y) (pos p) hpy with j|j|j;{exact Or.inl j};{exact Or.inr j};{exact absurd j (fun G=>hnx (hfx p m G.symm▸m))}};have H:pos n≠pos p:=fun j=>X (d.2 _ l _ m j);have i:∀(a b N:O),N∈aa 14 D->b∉aa 14 D ->N≠n->N≠p->ac N a=true->ac a b=true->(af 14 D a).card<=2:=by
   intro a b N r I hax hay ga gab;by_contra h3;obtain⟨hPa,hQa⟩:=k a (by omega);have h8:pos n∈af 14 D a:=by rcases u with rfl|rfl <;> assumption
   have h9:pos p∈af 14 D a:=by rcases A with rfl|rfl <;> assumption
   have ha:=aJ d r ((ae _ _).1 ga);obtain⟨eab,hb,-,J,-⟩:=bf h s d ((ae _ _).1 gab);rcases aT h8 h9 ha H (fun G=>hax.symm (d.2 _ l _ r G)) (fun G=>hay.symm (d.2 _ m _ r G)) (q a) eab hb with j|j|j;{exact I (J n l j▸l)};{exact I (J p m j▸m)};{exact I (J N r j▸r)}
  have lz:=i z w B S W hzx hzy gz gzw;have lw:=i w z C T U hwx hwy gw ((ae _ _).2 (bm ((ae _ _).1 gzw)));exact dl h s d z w v B C S T U W hnv ⟨gz,gw,gzw,gzv,hvw,hdw,Y⟩ lz lw
 by_cases K:3<=(af 14 D 11).card
 · have l4:(af 14 D 4).card<=2:=by
    by_contra L;exact c 4 11 10 3 2 13 12 8 1 (g 10 V) (g 3 V) (g 8 V) (g 1 V) (f 4 V) (f 11 V) (f 2 V) (f 13 V) (f 12 V) V (by omega) K
   have l6:(af 14 D 6).card<=2:=by{by_contra L;exact c 6 11 8 3 5 9 12 10 1 (g 8 V) (g 3 V) (g 10 V) (g 1 V) (f 6 V) (f 11 V) (f 5 V) (f 9 V) (f 12 V) V (by omega) K};have hd:3<=(af 14 D 13).card:=by{by_contra L;exact dl h s d 4 13 11 10 1 (g 10 V) (g 1 V) (f 4 V) (f 13 V) (f 11 V) V l4 (by omega)};have l2:(af 14 D 2).card<=2:=by{by_contra L;exact c 2 13 8 1 4 11 13 10 3 (g 8 V) (g 1 V) (g 10 V) (g 3 V) (f 2 V) (f 13 V) (f 4 V) (f 11 V) (f 13 V) V (by omega) hd};exact kx h s ⟨d,q,t,k⟩ 13 11 2 4 6 1 3 8 10 8 (g 1 V) (g 3 V) (g 8 V) (g 10 V) (g 8 V) (f 13 V) (f 11 V) (f 2 V) (f 4 V) (f 6 V) V hd K l2 l4 l6
 · have M:(af 14 D 11).card<=2:=by omega
   have h4:3<=(af 14 D 4).card:=by{by_contra L;exact dl h s d 11 4 6 3 10 (g 3 V) (g 10 V) (f 11 V) (f 4 V) (f 6 V) V M (by omega)};have h6:3<=(af 14 D 6).card:=by{by_contra L;exact dl h s d 11 6 4 3 8 (g 3 V) (g 8 V) (f 11 V) (f 6 V) (f 4 V) V M (by omega)};have l13:(af 14 D 13).card<=2:=by{by_contra L;exact c 4 13 10 1 6 11 9 8 3 (g 10 V) (g 1 V) (g 8 V) (g 3 V) (f 4 V) (f 13 V) (f 6 V) (f 11 V) (f 9 V) V h4 (by omega)};have l9:(af 14 D 9).card<=2:=by{by_contra L;exact c 6 9 8 1 4 11 13 10 3 (g 8 V) (g 1 V) (g 10 V) (g 3 V) (f 6 V) (f 9 V) (f 4 V) (f 11 V) (f 13 V) V h6 (by omega)};exact kx h s ⟨d,q,t,k⟩ 4 6 13 11 9 10 8 1 3 1 (g 10 V) (g 8 V) (g 1 V) (g 3 V) (g 1 V) (f 4 V) (f 6 V) (f 13 V) (f 11 V) (f 9 V) V h4 h6 l13 M l9
lemma dp {D:Dag} (h:ai 14 D) (g:ar D) (h12:ap 14 D<=12) (L:bd 14 D=(al 14 D).card+1) (c:Fin 68) (Y:3<=(bU c).card) (d:aa 14 D=bU c):False:=by
 have Z:=aV 14 D;have hts:=bg 14 D;by_cases i:c.val=12
 · have a:aa 14 D={0,1,3}:=by rw[d,show c=⟨12,V⟩ from _fe i];decide
   have y:(aa 14 D).card=3:=by rw[a];decide
   exact pO h g (by omega) L a
 by_cases z:c.val=23
 · have a:aa 14 D={1,3,8}:=by rw[d,show c=⟨23,V⟩ from _fe z];decide
   have y:(aa 14 D).card=3:=by rw[a];decide
   exact pP h g (by omega) L a
 by_cases A:c.val=26
 · have a:aa 14 D={4,7,8}:=by rw[d,show c=⟨26,V⟩ from _fe A];decide
   have y:(aa 14 D).card=3:=by rw[a];decide
   exact pQ h g (by omega) L a
 by_cases B:c.val=40
 · have a:aa 14 D={0,4,5,7}:=by rw[d,show c=⟨40,V⟩ from _fe B];decide
   exact ky h g L (by rw[a];decide) (by rw[a];decide) (by rw[a];decide) (by rw[a];decide) (by rw[a];decide) (by rw[a];decide) (by rw[a];decide)
 by_cases C:c.val=44
 · have a:aa 14 D={4,5,7,8}:=by rw[d,show c=⟨44,V⟩ from _fe C];decide
   exact ky h g L (by rw[a];decide) (by rw[a];decide) (by rw[a];decide) (by rw[a];decide) (by rw[a];decide) (by rw[a];decide) (by rw[a];decide)
 by_cases E:c.val=51
 · have a:aa 14 D={1,3,8,10}:=by rw[d,show c=⟨51,V⟩ from _fe E];decide
   exact pR h g L a
 rcases l:fw c with ⟨k,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10⟩;by_cases K:k=0
 · have M:=o1 c Y i z A B C E (by rw[l];exact K)
   have N:=o2 c Y i z A B C E (by rw[l];exact K);have R:=o3 c Y i z A B C E (by rw[l];exact K);rw[l] at M N R;dsimp only at M N R;obtain⟨n,p,hj1,hj2,hxy,hqx,h0,hdx⟩:=M;obtain⟨h12',hx1,hx2,hxv,q,r⟩:=N;obtain⟨h1,hy1,hy2,hyv,h2,h3,S,hq1⟩:=R;obtain⟨pos,P,Q,h4⟩:=fq h g L;exact mX h g h4 (d▸n) (d▸p) (d▸hj1) (d▸hj2) ⟨hxy,hqx,h0,hdx,h12',hx1,hx2,hxv,q,r,h1,hy1,hy2,hyv,h2,h3,S,hq1⟩
 · by_cases h5:k=1
   · have T:=pM c Y i z A B C E (by rw[l];exact h5)
     rw[l] at T;dsimp only at T;obtain⟨⟨y,n,p,U,h12',F,G,H,q,r⟩,⟨hiz,hik,hnz,hnk,hnv,hza,hka⟩,hg⟩:=T;have W:bL 14 D=0:=by rw[d,y] at Z;omega
     obtain⟨b,hb⟩:=b_ bs h.1 (bF g);have s:=bD hb;obtain⟨pos,f⟩:=bQ bs h (bF g);have X:(aj 14 D b).card=1:=by have:=bS h.1 b s;omega
     obtain⟨u0,m⟩:=_c1.1 X;have ha3:=cx h g f (d▸n) (d▸p) ⟨h12',F,G,H,q,r⟩;have I:aZ D b a1={u0}:=by
      have hcc:=bj h g b s a1;have t:aZ D b a1⊆{u0}:=by rw[<- m];exact _fs _ _
      exact _eqc t (by rw[_cs];omega)
     have v:=eF h g W b hb f (d▸n) (d▸p) ⟨U,h12',F,G,H,q,r⟩ I;have j:∀ x:O,x≠a1->(af 14 D x).card<=2:=fun x hx=>by{have J:aZ D b x=∅:=by{rw[eq_empty_iff_forall_notMem];intro u hu;have w:u=u0:=_ms.1 (m▸(ay.1 hu).1);exact hx (v x (w▸(ay.1 hu).2))};have:=bj h g b s x;rw[J,_ce] at this;omega};exact dl h g f a5 a6 a7 a8 a9 (d▸hiz) (d▸hik) (d▸hnz) (d▸hnk) (d▸hnv) hg (j a5 hza) (j a6 hka)
   · have T:=pN c Y i z A B C E (by rw[l];exact K) (by rw[l];exact h5)
     rw[l] at T;dsimp only at T;obtain⟨⟨y,n,p,U,h12',F,G,H,q,r⟩,⟨hik1,hik2,hnu,hua,hk1a,hk2a⟩,hg⟩:=T;have W:bL 14 D=0:=by rw[d,y] at Z;omega
     obtain⟨b,hb⟩:=b_ bs h.1 (bF g);have s:=bD hb;obtain⟨pos,f⟩:=bQ bs h (bF g);have X:(aj 14 D b).card=1:=by have:=bS h.1 b s;omega
     obtain⟨u0,m⟩:=_c1.1 X;have ha3:=cx h g f (d▸n) (d▸p) ⟨h12',F,G,H,q,r⟩;have I:aZ D b a1={u0}:=by
      have hcc:=bj h g b s a1;have t:aZ D b a1⊆{u0}:=by rw[<- m];exact _fs _ _
      exact _eqc t (by rw[_cs];omega)
     have v:=eF h g W b hb f (d▸n) (d▸p) ⟨U,h12',F,G,H,q,r⟩ I;have j:∀ x:O,x≠a1->(af 14 D x).card<=2:=fun x hx=>by{have J:aZ D b x=∅:=by{rw[eq_empty_iff_forall_notMem];intro u hu;have w:u=u0:=_ms.1 (m▸(ay.1 hu).1);exact hx (v x (w▸(ay.1 hu).2))};have:=bj h g b s x;rw[J,_ce] at this;omega};exact fR h g f a5 a6 a7 a8 a9 a10 (d▸hik1) (d▸hik2) (d▸hnu) hg (j a5 hua) (j a6 hk1a) (j a7 hk2a)
def fA (k:Fin 26):Fin 68:=match k.val with
 | 0=>⟨30,V⟩
 | 1=>⟨31,V⟩
 | 2=>⟨32,V⟩
 | 3=>⟨33,V⟩
 | 4=>⟨34,V⟩
 | 5=>⟨35,V⟩
 | 6=>⟨36,V⟩
 | 7=>⟨37,V⟩
 | 8=>⟨38,V⟩
 | 9=>⟨41,V⟩
 | 10=>⟨43,V⟩
 | 11=>⟨47,V⟩
 | 12=>⟨52,V⟩
 | 13=>⟨53,V⟩
 | 14=>⟨54,V⟩
 | 15=>⟨55,V⟩
 | 16=>⟨56,V⟩
 | 17=>⟨57,V⟩
 | 18=>⟨59,V⟩
 | 19=>⟨60,V⟩
 | 20=>⟨61,V⟩
 | 21=>⟨63,V⟩
 | 22=>⟨64,V⟩
 | 23=>⟨65,V⟩
 | 24=>⟨66,V⟩
 | _=>⟨67,V⟩
lemma pS:∀ k:Fin 26,3<=(bU (fA k)).card:=by decide +kernel
lemma mY:∀ k:Fin 26,∀ m:Fin 128,∀ b:_d,
 let I:=bU (fA k);let P:=i_\I;let a:=f6 m;let d:=if b&&!decide ((0:Fin 7)∈a) then ({0}:Finset (Fin 7)) else ∅;let e:=a∪d;let g:=(univ:Finset (Fin 7))\e;let c:=univ.filter (fun j:Fin 7=>cw j∈I/\az (cw j)⊆P);let f:=g.biUnion (fun j=>az (cw j)∩P)
 (∀ j∈a,bX (cw j)⊆P)->(b=true->az 0⊆P) ->
 (2*P.card+12<2*a.card+d.card+c.card+f.card+(14 - I.card)+(c\e).card) \/
 (12<(14 - I.card)+2+(c\e).card):=by
 decide +kernel
lemma nH {D:Dag} (h:ai 14 D) (g:ar D) (i:ap 14 D<=12) (k:Fin 26) (j:aa 14 D=bU (fA k)):False:=by
 have l:=aV 14 D;have d:3<=(bU (fA k)).card:=pS k;by_cases n:bd 14 D<=(al 14 D).card;{exact dn h g n (fA k) j};by_cases p:bd 14 D=(al 14 D).card+1;{exact dp h g i p (fA k) d j};obtain⟨m,occ0,b,a,e,c⟩:=jS h g;rw[j] at b a e c l;have q:=bg 14 D;rcases mY k m occ0 b a with f|f <;> omega
def kX (T:o) (f:O):o:=T.erase f∪univ.filter (fun a=>ac f a=true/\∀ g∈T.erase f,ac a g=false)
def eN:o:=i_.erase 7
lemma kY:∀ a∈eN,∀ b∈eN,¬ dj a b:=fun a c b d=>lN a (mem_of_mem_erase c) b (mem_of_mem_erase d)
lemma jT {D:Dag}:¬ aQ 14 D eN (bX 0):=by
 rintro⟨w,b⟩;have a:(7:O)∈bX 0:=V;rw[<- b] at a;have c:=(_mn.1 a).2;exact(_me.1 c).1 rfl
def kL (T J:o):_d:=decide (∀ i∈J,(∃ a∈T,ac i a=true) /\∀ f∈T,∃ a∈kX T f,ac i a=true) && decide (∀ f∈T,(∀ a∈kX T f,∀ b∈kX T f,bK a b=false) /\∃ a∈kX T f,ac f a=true) && decide (T.card=3/\J.card=3) && decide (∀ i∈J,i.val<7/\T⊆eN/\aD i⊆eN/\(aD i∩T).card=2) && decide (∀ i∈J,∀ j∈J,aD j∩T⊆aD i∩T->j=i) && decide (∀ t∈T,(J.filter (fun i=>ac i t=true)).card<=2 /\∀ i∈J,ac i t=false->T.erase t⊆aD i)
lemma io {T J:o} (h:kL T J=true):(∀ i∈J,(∃ a∈T,ac i a=true)/\∀ f∈T,∃ a∈kX T f,ac i a=true) /\(∀ f∈T,(∀ a∈kX T f,∀ b∈kX T f,bK a b=false) /\∃ a∈kX T f,ac f a=true) /\(T.card=3/\J.card=3) /\(∀ i∈J,i.val<7/\T⊆eN/\aD i⊆eN/\(aD i∩T).card=2) /\(∀ i∈J,∀ j∈J,aD j∩T⊆aD i∩T->j=i) /\∀ t∈T,(J.filter (fun i=>ac i t=true)).card<=2 /\∀ i∈J,ac i t=false->T.erase t⊆aD i:=by
 simpa only[kL,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using h
lemma jq {T J:o} {D:Dag} (e:kL T J=true) (k:∀ i∈J,i∈aa 14 D):(∀ i∈J,i∈aa 14 D/\(∃ a∈T,eW i a)/\∀ f∈T,∃ a∈kX T f,eW i a) /\∀ f∈T,(∀ a∈kX T f,∀ b∈kX T f,¬ dj a b)/\T.erase f⊆kX T f /\∃ a∈kX T f,eW f a:=by
 obtain⟨h,j,-⟩:=io e;exact⟨fun i g=>⟨k i g,(h i g).1.imp (fun _ c=>⟨c.1,(ae _ _).1 c.2⟩),fun f d=>((h i g).2 f d).imp (fun _ c=>⟨c.1,(ae _ _).1 c.2⟩)⟩,fun f d=>⟨fun a c b l=>b3.1 ((j f d).1 a c b l),subset_union_left,(j f d).2.imp (fun _ c=>⟨c.1,(ae _ _).1 c.2⟩)⟩⟩
lemma qw {D:Dag} (h:ai 14 D) (e:ar D) (f:bL 14 D=0) {P:o} (g:∀ a∈P,∀ b∈P,¬ dj a b) {i:O} (d:i.val<7) (k:i∈aa 14 D) (c:aD i⊆P) (l:i=0->¬ aQ 14 D P (bX 0)):aQ 14 D P (aD i):=by
 by_contra m
 have:=ml h e P g {i} (fun j n=>by
  rw[_ms.1 n];exact⟨d,k,c,m,l⟩)
 rw[_cs] at this;omega
lemma lO {D:Dag} (h:ai 14 D) (s:ar D) (L:bL 14 D<=1) {T J:o} (n:kL T J=true) (t:∀ i∈J,i∈aa 14 D):(al 14 D).card+3<=bd 14 D:=by
 classical
 have z:=bs;have A:=bF s;obtain⟨b,B⟩:=bu h s;obtain⟨pos,g⟩:=bQ z h A;obtain⟨t',hA'⟩:=jq n t;obtain⟨-,-,⟨C,E⟩,c,p,-⟩:=io n;have l:∀ i∈J,∃ M,aQ 14 D T M/\aD i∩T⊆M /\(aQ 14 D eN (aD i)->M=aD i∩T):=by
  intro i d;by_cases r:aQ 14 D eN (aD i)
  · obtain⟨w,F⟩:=r
    have:ag 14 D w∩T=aD i∩T:=by{rw[<- F,inter_assoc,inter_eq_right.2 (c i d).2.1]};exact⟨_,⟨w,rfl⟩,this▸Subset.refl _,fun _=>this⟩
  · exact⟨ag 14 D (aw D (pos i))∩T,⟨_,rfl⟩,fun a x=>by
     rw[_mn,cn] at x;exact _mn.2 ⟨(g.1 i (t i d)).2.2.1 a x.1,x.2⟩,
     fun G=>absurd G r⟩
 choose! M l using l
 have y:=ml h s eN kY (J.filter (fun i=>¬ aQ 14 D eN (aD i))) (fun i d=>by
  rw[_mf] at d
  exact⟨(c i d.1).1,t i d.1,(c i d.1).2.2.1,d.2,fun _=>jT⟩)
 have k:Set.InjOn M J:=by
  intro i d j m f;by_contra e;have q:∀ i∈J,∀ j∈J,M i=M j->i≠j ->¬ aQ 14 D eN (aD i):=by
   intro i d j m f e r
   exact e (p i d j m (by
    rw[<- (l i d).2.2 r,f];exact(l j m).2.1)).symm
  have H:i∈J.filter (fun i=>¬ aQ 14 D eN (aD i)):=
   _mf.2 ⟨d,q i d j m f e⟩
  have I:j∈J.filter (fun i=>¬ aQ 14 D eN (aD i)):=
   _mf.2 ⟨m,q j m i d f.symm (Ne.symm e)⟩
  have:=one_lt_card.2 ⟨i,H,j,I,e⟩;omega
 have:=pj z h A b B g T J (kX T) t' hA' (J.image M) (fun X K=>by
  obtain⟨i,d,rfl⟩:=_mg.1 K;have:=_cl (l i d).2.1;rw[(c i d).2.2.2] at this
  exact⟨this,(l i d).1⟩)
 rw[_cij k] at this;omega
lemma o4 {D:Dag} (h:ai 14 D) (H:ar D) (z:bL 14 D=0) (Z:bd 14 D<=(al 14 D).card+3) (b:O->ℕ) (P:aM 14 D b) {T J:o} (p:kL T J=true) (A:∀ i∈J,i∈aa 14 D):(∀ t∈T,(af 14 D t).card<=3/\aW 14 D (ao 14 D {t})=∅) /\∀ u∈aj 14 D b,(ag 14 D u.1∩T).Nonempty:=by
 classical
 have I:=bs;have K:=bF H;obtain⟨pos,k⟩:=bQ I h K;obtain⟨A',hA'⟩:=jq p A;obtain⟨-,-,⟨E,Q⟩,c,q,l⟩:=io p;have n:Set.InjOn (fun i=>aD i∩T) J:=fun i d j R F=>q j R i d (by rw[show aD i∩T=aD j∩T from F]);have r:∀ i∈J,aQ 14 D T (aD i∩T):=by{intro i d;obtain⟨w,S⟩:=qw h H z kY (c i d).1 (A i d) (c i d).2.2.1 (fun _=>jT);refine⟨w,?_⟩;rw[<- S,inter_assoc,inter_eq_right.2 (c i d).2.1]}
 obtain⟨g,L,U⟩:=pk I h K b P k T J (kX T) A' hA' (J.image (fun i=>aD i∩T)) (fun X W=>by
  obtain⟨i,d,rfl⟩:=_mg.1 W
  exact⟨(c i d).2.2.2,r i d⟩) E
  (by rw[_cij n];omega)
 refine⟨fun t y=>⟨?_,(L t y).1⟩,U⟩;obtain⟨e1,G⟩:=(L t y).2;have v:af 14 D t⊆insert e1 ((J.filter (fun i=>ac i t=true)).image pos):=by
  intro e M;rcases G e M with rfl|N;{exact mem_insert_self _ _}
  · obtain⟨i,d,rfl⟩:=_mg.1 N
    refine mem_insert_of_mem (_mg.2 ⟨i,_mf.2 ⟨d,?_⟩,rfl⟩);by_contra m;rw[Bool.not_eq_true] at m;refine g (aw D (pos i)) (fun a Y=>?_);by_cases x:a=t;{rw[x];exact(ak.1 M).2.1};{exact(k.1 i (A i d)).2.2.1 a (cn.1 ((l t y).2 i d m (_me.2 ⟨x,Y⟩)))}
 have N:=_cl v;have h2:=card_insert_le e1 ((J.filter (fun i=>ac i t=true)).image pos);have h4:=card_image_le (s:=J.filter (fun i=>ac i t=true)) (f:=pos);have h5:=(l t y).1;omega
lemma kz:kL {8,10,13} {0,2,4}=true:=by decide +kernel
lemma rY {D:Dag} (h:ai 14 D) (b:ar D) (c:ap 14 D<=12) (d:aa 14 D=bU ⟨39,V⟩):False:=by
 have e:=aV 14 D;have a:aa 14 D={0,2,4,7}:=by rw[d];decide
 rw[a,show({0,2,4,7}:o).card=4 from by decide] at e;by_cases g:bd 14 D<=(al 14 D).card;{exact dn h b g ⟨39,V⟩ d};by_cases j:bd 14 D=(al 14 D).card+1;{exact dp h b c j ⟨39,V⟩ V d};have k:=bg 14 D;have f:=lO h b (by omega) kz (fun i l=>by rw[a];revert i l;decide);omega
lemma rZ {D:Dag} (h:ai 14 D) (b:ar D) (c:ap 14 D<=12) (d:aa 14 D=bU ⟨46,V⟩):False:=by
 have e:=aV 14 D;have a:aa 14 D={0,2,4,9}:=by rw[d];decide
 rw[a,show({0,2,4,9}:o).card=4 from by decide] at e;by_cases g:bd 14 D<=(al 14 D).card;{exact dn h b g ⟨46,V⟩ d};by_cases j:bd 14 D=(al 14 D).card+1;{exact dp h b c j ⟨46,V⟩ V d};have k:=bg 14 D;have f:=lO h b (by omega) kz (fun i l=>by rw[a];revert i l;decide);omega
lemma mo:∀ m:Fin 128,∀ b:_d,
 let I:=bU ⟨58,V⟩;let P:=i_\I;let a:=f6 m;let d:=if b&&!decide ((0:Fin 7)∈a) then ({0}:Finset (Fin 7)) else ∅;let e:=a∪d;let g:=(univ:Finset (Fin 7))\e;let c:=univ.filter (fun j:Fin 7=>cw j∈I/\az (cw j)⊆P);let f:=g.biUnion (fun j=>az (cw j)∩P)
 (∀ j∈a,bX (cw j)⊆P)->(b=true->az 0⊆P) ->
 (2*P.card+12<2*a.card+d.card+c.card+f.card+(14 - I.card)+(c\e).card) \/
 (12<(14 - I.card)+3+(c\e).card):=by
 decide +kernel
lemma r0 {D:Dag} (h:ai 14 D) (g:ar D) (l:ap 14 D<=12) (j:aa 14 D=bU ⟨58,V⟩):False:=by
 have n:=aV 14 D;have b:aa 14 D={0,2,4,5,7}:=by rw[j];decide
 rw[b,show({0,2,4,5,7}:o).card=5 from by decide] at n;by_cases q:bd 14 D<=(al 14 D).card;{exact dn h g q ⟨58,V⟩ j};by_cases r:bd 14 D=(al 14 D).card+1;{exact dp h g l r ⟨58,V⟩ V j};have s:=bg 14 D;have p:=lO h g (by omega) kz (fun i t=>by rw[b];revert i t;decide);obtain⟨m,occ0,c,a,e,d⟩:=jS h g;rw[j] at c a e d;have k:(bU ⟨58,V⟩).card=5:=V;rcases mo m occ0 c a with f|f <;> omega
def fT (a b:_d×_d×_d):_d:=(!a.1||b.1)&&(!a.2.1||b.2.1)&&(!a.2.2||b.2.2)
lemma lP:∀ a b c d:_d×_d×_d,fT a b=true\/fT b a=true \/fT a c=true\/fT c a=true \/fT a d=true\/fT d a=true \/fT b c=true\/fT c b=true \/fT b d=true\/fT d b=true \/fT c d=true\/fT d c=true:=by decide +kernel
lemma gI {α:Type} [DecidableEq α] {R A B C D:Finset α} (m:R.card=3) (g:A⊆R) (i:B⊆R) (j:C⊆R) (k:D⊆R):A⊆B\/B⊆A\/A⊆C\/C⊆A\/A⊆D\/D⊆A \/B⊆C\/C⊆B\/B⊆D\/D⊆B\/C⊆D\/D⊆C:=by
 classical
 obtain⟨u1,u2,u3,-,-,-,d⟩:=card_eq_three.1 m;let b:Finset α->_d×_d×_d:=fun S=>
  (decide (u1∈S),decide (u2∈S),decide (u3∈S))
 have a:∀ X Y:Finset α,X⊆R->fT (b X) (b Y)=true->X⊆Y:=by{intro X Y l c x f;have e:x∈R:=l f;rw[d,_mi,_mi,_ms] at e;simp only[fT,b,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,decide_eq_true_eq] at c;rcases e with rfl|rfl|rfl;{exact c.1.1.resolve_left (not_not.2 f)};{exact c.1.2.resolve_left (not_not.2 f)};{exact c.2.resolve_left (not_not.2 f)}};rcases lP (b A) (b B) (b C) (b D) with
  h|h|h|h|h|h|h|h|h|h|h|h
 · exact Or.inl (a A B g h)
 · exact Or.inr (Or.inl (a B A i h))
 · exact Or.inr (Or.inr (Or.inl (a A C g h)))
 · exact Or.inr (Or.inr (Or.inr (Or.inl (a C A j h))))
 · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (a A D g h)))))
 · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (a D A k h))))))
 · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (a B C i h)))))))
 · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (a C B j h))))))))
 · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (a B D i h)))))))))
 · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (a D B k h))))))))))
 · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (a C D j h)))))))))))
 · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (a D C k h)))))))))))
lemma r4 {D:Dag} (h:ai 14 D) (r:ar D) (h6:ap 14 D<=12) (hI:aa 14 D=bU ⟨62,V⟩):False:=by
 have hel:=aV 14 D;have s:aa 14 D={0,2,4,7,9}:=by rw[hI];decide
 rw[s,show({0,2,4,7,9}:o).card=5 from by decide] at hel;by_cases h0:bd 14 D<=(al 14 D).card;{exact dn h r h0 ⟨62,V⟩ hI};by_cases h1:bd 14 D=(al 14 D).card+1;{exact dp h r h6 h1 ⟨62,V⟩ V hI};have hts:=bg 14 D;have htri:=lO h r (by omega) kz (fun i hi=>by rw[s];revert i hi;decide);have L:bL 14 D=0:=by omega
 obtain⟨b,M⟩:=bu h r;obtain⟨pos,e⟩:=bQ bs h (bF r);have hR3:(aj 14 D b).card=3:=by have:=bS h.1 b M;omega
 obtain⟨hT,-⟩:=o4 h r L (by omega) b M kz (fun i hi=>by rw[s];revert i hi;decide);have f:∀ v:O,v∈({0,2,4,7,9}:o)->v∈aa 14 D:=fun v Y=>s▸Y;have c:∀ v:O,v∉({0,2,4,7,9}:o)->v∈al 14 D:=fun v Y=>by{by_contra hc;exact Y (s▸aN.2 hc)};have x:=dy h r L e (f 0 V) (f 2 V) (by decide:(0:O)≠2/\ac 0 8=true/\ac 2 8=true/\ac 8 6=true/\(6:O)≠0/\(6:O)≠2) (hT 8 V).1;have N:=dy h r L e (f 0 V) (f 4 V) (by decide:(0:O)≠4/\ac 0 10=true/\ac 4 10=true/\ac 10 5=true/\(5:O)≠0/\(5:O)≠4) (hT 10 V).1
 have H:(aZ D b 1).Nonempty:=_cp.1 (by
  have h3:=cx h r e (f 7 V) (f 9 V) (by decide:(7:O)≠9/\ac 7 1=true/\ac 9 1=true/\ac 1 13=true/\(13:O)≠7/\(13:O)≠9)
  have:=bj h r b M 1;omega)
 have J:(aZ D b 8).Nonempty:=_cp.1 (by
  have h3:=cx h r e (f 0 V) (f 2 V) (by decide:(0:O)≠2/\ac 0 8=true/\ac 2 8=true/\ac 8 6=true/\(6:O)≠0/\(6:O)≠2)
  have:=bj h r b M 8;omega)
 have y:(aZ D b 10).Nonempty:=_cp.1 (by
  have h3:=cx h r e (f 0 V) (f 4 V) (by decide:(0:O)≠4/\ac 0 10=true/\ac 4 10=true/\ac 10 5=true/\(5:O)≠0/\(5:O)≠4)
  have:=bj h r b M 10;omega)
 have E:(aZ D b 13).Nonempty:=_cp.1 (by
  have h3:=cx h r e (f 2 V) (f 4 V) (by decide:(2:O)≠4/\ac 2 13=true/\ac 4 13=true/\ac 13 1=true/\(1:O)≠2/\(1:O)≠4)
  have:=bj h r b M 13;omega)
 have a:∀(v t j q:O),j∈aa 14 D->v∈al 14 D ->(∀ z,z∈ag 14 D (aw D (pos j))->aP j z) ->((az v).card=3/\ac j v=true/\ac j q=true/\v≠t/\v≠q/\bK t q=false/\ac j t=false) ->(aZ D b v).Nonempty->aZ D b v⊆aZ D b t->False:=by{intro v t j q hj Y Q R hne P;obtain⟨u,hu⟩:=hne;have Z:∀ u'∈aj 14 D b,v∈ag 14 D u'.1->t∈ag 14 D u'.1:=fun u' hu' Y'=>(ay.1 (P (ay.2 ⟨hu',Y'⟩))).2;have hw:v∈ag 14 D u.1/\t∈ag 14 D u.1:=⟨(ay.1 hu).2,(ay.1 (P hu)).2⟩;exact aH.1 R.2.2.2.2.2.2 (Q t (cy h r b M e hj Y Z hw ⟨R.1,R.2.1,R.2.2.1,R.2.2.2.1,R.2.2.2.2.1,R.2.2.2.2.2.1⟩))};have k:¬ aZ D b 8⊆aZ D b 10:=a 8 10 2 12 (f 2 V) (c 8 V) x.2 V J;have l:¬ aZ D b 10⊆aZ D b 8:=a 10 8 4 11 (f 4 V) (c 10 V) N.2 V y;have m:¬ aZ D b 8⊆aZ D b 13:=a 8 13 0 10 (f 0 V) (c 8 V) x.1 V J;have I:¬ aZ D b 13⊆aZ D b 8:=a 13 8 4 10 (f 4 V) (c 13 V) N.2 V E;have F:¬ aZ D b 10⊆aZ D b 13:=a 10 13 0 8 (f 0 V) (c 10 V) x.1 V y;have G:¬ aZ D b 13⊆aZ D b 10:=a 13 10 2 8 (f 2 V) (c 13 V) x.2 V E;have w:¬ aZ D b 8⊆aZ D b 1:=a 8 1 0 10 (f 0 V) (c 8 V) x.1 V J;have n:¬ aZ D b 10⊆aZ D b 1:=a 10 1 0 8 (f 0 V) (c 10 V) x.1 V y;have p:¬ aZ D b 13⊆aZ D b 1:=a 13 1 2 8 (f 2 V) (c 13 V) x.2 V E;have g:∀ t∈({8,10,13}:o),¬ aZ D b 1⊆aZ D b t:=by
  intro t W d;have X:(aZ D b 1).card<=(aZ D b t).card:=_cl d;have h4:(aZ D b t).card<3:=by
   by_contra hge;have S:aZ D b t=aj 14 D b:=
    _eqc (_fs _ _) (by omega)
   simp only[_mi,_ms] at W;rcases W with rfl|rfl|rfl;{exact l (by rw[S];exact _fs _ _)};{exact k (by rw[S];exact _fs _ _)};{exact m (by rw[S];exact _fs _ _)}
  by_cases h2:(aZ D b 1).card=1
  · have K:(af 14 D 1).card<=3:=by have:=bj h r b M 1;omega
    have T:=dy h r L e (f 7 V) (f 9 V) (by decide:(7:O)≠9/\ac 7 1=true/\ac 9 1=true/\ac 1 13=true/\(13:O)≠7/\(13:O)≠9) K;simp only[_mi,_ms] at W;rcases W with rfl|rfl|rfl;{exact a 1 8 7 3 (f 7 V) (c 1 V) T.1 V H d};{exact a 1 10 7 3 (f 7 V) (c 1 V) T.1 V H d};{exact a 1 13 7 3 (f 7 V) (c 1 V) T.1 V H d}
  · have h5:0<(aZ D b 1).card:=_cp.2 H
    have U:aZ D b 1=aZ D b t:=_eqc d (by omega);simp only[_mi,_ms] at W;rcases W with rfl|rfl|rfl;{exact w (by rw[U])};{exact n (by rw[U])};{exact p (by rw[U])}
 rcases gI hR3 (_fs _ _) (_fs _ _) (_fs _ _) (_fs _ _) (A:=aZ D b 1) (B:=aZ D b 8) (C:=aZ D b 10) (D:=aZ D b 13) with
  d|d|d|d|d|d|d|d|d|d|d|d
 · exact g 8 V d
 · exact w d
 · exact g 10 V d
 · exact n d
 · exact g 13 V d
 · exact p d
 · exact k d
 · exact l d
 · exact m d
 · exact I d
 · exact F d
 · exact G d
lemma dJ {α:Type} [DecidableEq α] {u1 u2:α} (l:u1≠u2) {A B:Finset α} (m:A⊆{u1,u2}) (n:B⊆{u1,u2}) (g:A.Nonempty) (h:B.Nonempty) (d:¬ A⊆B) (e:¬ B⊆A):(A={u1}/\B={u2})\/(A={u2}/\B={u1}):=by
 have b:∀ S:Finset α,S⊆{u1,u2}->S.Nonempty->S={u1}\/S={u2}\/S={u1,u2}:=by
  intro S f i;by_cases j:u1∈S <;> by_cases k:u2∈S
  · right;right
    refine Subset.antisymm f (fun x c=>?_);simp only[_mi,_ms] at c;rcases c with rfl|rfl <;> assumption
  · left
    refine Subset.antisymm (fun x c=>?_) (singleton_subset_iff.2 j);have a:=f c;simp only[_mi,_ms] at a;rcases a with rfl|rfl;{exact _mss _};{exact absurd c k}
  · right;left
    refine Subset.antisymm (fun x c=>?_) (singleton_subset_iff.2 k);have a:=f c;simp only[_mi,_ms] at a;rcases a with rfl|rfl;{exact absurd c j};{exact _mss _}
  · obtain⟨x,c⟩:=i
    have a:=f c;simp only[_mi,_ms] at a;rcases a with rfl|rfl;{exact absurd c j};{exact absurd c k}
 rcases b A m g with rfl|rfl|rfl <;> rcases b B n h with rfl|rfl|rfl;{exact absurd (Subset.refl _) d};{exact Or.inl ⟨rfl,rfl⟩};{exact absurd (by simp) d};{exact Or.inr ⟨rfl,rfl⟩};{exact absurd (Subset.refl _) d};{exact absurd (by simp) d};{exact absurd (by simp) e};{exact absurd (by simp) e};{exact absurd (Subset.refl _) d}
lemma dZ {D:Dag} (h:ai 14 D) (g:ar D) (K:ap 14 D<=12) (j:Fin 68) (L:aa 14 D=bU j) (M:(bU j).card=4) (a b' ia1 ia2 av ib1 ib2 bv:O) (p:ia1∈aa 14 D) (q:ia2∈aa 14 D) (r:ib1∈aa 14 D) (s:ib2∈aa 14 D) (E:(az a).card=3/\ia1≠ia2/\ac ia1 a=true/\ac ia2 a=true /\ac a av=true/\av≠ia1/\av≠ia2) (F:(az b').card=3/\ib1≠ib2/\ac ib1 b'=true/\ac ib2 b'=true /\ac b' bv=true/\bv≠ib1/\bv≠ib2) (z k v iz ik:O) (N:iz∈aa 14 D) (P:ik∈aa 14 D) (Q:z∉aa 14 D) (R:k∉aa 14 D) (S:v∉aa 14 D) (i:z≠a/\z≠b'/\k≠a/\k≠b' /\ac iz z=true/\ac ik k=true/\ac z k=true /\ac z v=true/\v≠k/\(az k).card=3 /\decide (v.val<7)=decide (k.val<7)) (l:∀(b:O->ℕ) (d:aM 14 D b) (pos:O->ℕ×_d),bL 14 D=0->bA 14 eW D pos->(aj 14 D b).card=2 ->(aZ D b a).Nonempty->aZ D b a⊆aZ D b b'->False) (m:∀(b:O->ℕ) (d:aM 14 D b) (pos:O->ℕ×_d),bL 14 D=0->bA 14 eW D pos->(aj 14 D b).card=2 ->(aZ D b b').Nonempty->aZ D b b'⊆aZ D b a->False):False:=by
 have T:=aV 14 D;rw[L,M] at T;by_cases h0:bd 14 D<=(al 14 D).card;{exact dn h g h0 j L};by_cases h1:bd 14 D=(al 14 D).card+1;{exact dp h g K h1 j (by omega) L};have hts:=bg 14 D;have n:bL 14 D=0:=by omega
 obtain⟨b,A⟩:=b_ bs h.1 (bF g);have d:=bD A;obtain⟨pos,c⟩:=bQ bs h (bF g);have B:(aj 14 D b).card=2:=by have:=bS h.1 b d;omega
 obtain⟨u1,u2,G,e⟩:=_ct2.1 B
 have t:(aZ D b a).Nonempty:=_cp.1 (by
  have h3:=cx h g c p q E.2
  have:=bj h g b d a;omega)
 have w:(aZ D b b').Nonempty:=_cp.1 (by
  have h3:=cx h g c r s F.2
  have:=bj h g b d b';omega)
 have C:=dJ G (e▸_fs _ _) (e▸_fs _ _) t w (fun U=>l b d pos n c B t U) (fun U=>m b d pos n c B w U);have f:∀ W X,aj 14 D b={W,X}->aZ D b a={W}->aZ D b b'={X}->False:=by
  intro W X hR' Z h2;have h4:=eF h g n b A c p q E Z;have h5:=eF h g n b A c r s F h2;have y:∀ x:O,x≠a->x≠b'->(af 14 D x).card<=2:=fun x h6 h7=>by{have H:aZ D b x=∅:=by{rw[eq_empty_iff_forall_notMem];intro u hu;obtain⟨I,J⟩:=ay.1 hu;rw[hR',_mi,_ms] at I;rcases I with rfl|rfl;{exact h6 (h4 x J)};{exact h7 (h5 x J)}};have:=bj h g b d x;rw[H,_ce] at this;omega};exact dl h g c z k v iz ik N P Q R S i.2.2.2.2 (y z i.1 i.2.1) (y k i.2.2.1 i.2.2.2.1)
 rcases C with ⟨h8,h9⟩|⟨ha,hb⟩;{exact f u1 u2 e h8 h9};{exact f u2 u1 (by rw[e,pair_comm]) ha hb}
lemma r7 {D:Dag} (h:ai 14 D) (k:ar D) (l:ap 14 D<=12) (p:aa 14 D=bU ⟨48,V⟩):False:=by
 have b:aa 14 D={0,2,7,9}:=by rw[p];decide
 have a:∀ v:O,v∈({0,2,7,9}:o)->v∈aa 14 D:=fun v f=>b▸f;have g:∀ v:O,v∉({0,2,7,9}:o)->v∉aa 14 D:=fun v f=>b▸f;have i:∀ v:O,v∉({0,2,7,9}:o)->v∈al 14 D:=fun v f=>by{by_contra q;exact f (b▸aN.2 q)};exact dZ h k l ⟨48,V⟩ p V 1 8 7 9 13 0 2 6 (a 7 V) (a 9 V) (a 0 V) (a 2 V) V V 3 12 11 7 2 (a 7 V) (a 2 V) (g 3 V) (g 12 V) (g 11 V) V (fun j d pos _ c m e n=>fa h k j d c 1 8 7 9 3 5 0 2 6 (i 1 V) (a 7 V) (a 9 V) (a 0 V) (a 2 V) (g 6 V) V (_cp.2 e) n (by have:=_cfl (aj 14 D j) (fun u=>(8:O)∈ag 14 D u.1);unfold aZ;omega)) (fun j d pos _ c m e n=>fa h k j d c 8 1 0 2 10 12 7 9 13 (i 8 V) (a 0 V) (a 2 V) (a 7 V) (a 9 V) (g 13 V) V (_cp.2 e) n (by have:=_cfl (aj 14 D j) (fun u=>(1:O)∈ag 14 D u.1);unfold aZ;omega))
lemma r8 {D:Dag} (h:ai 14 D) (k:ar D) (l:ap 14 D<=12) (p:aa 14 D=bU ⟨49,V⟩):False:=by
 have b:aa 14 D={2,4,7,9}:=by rw[p];decide
 have a:∀ v:O,v∈({2,4,7,9}:o)->v∈aa 14 D:=fun v f=>b▸f;have g:∀ v:O,v∉({2,4,7,9}:o)->v∉aa 14 D:=fun v f=>b▸f;have i:∀ v:O,v∉({2,4,7,9}:o)->v∈al 14 D:=fun v f=>by{by_contra q;exact f (b▸aN.2 q)};exact dZ h k l ⟨49,V⟩ p V 1 13 7 9 13 2 4 1 (a 7 V) (a 9 V) (a 2 V) (a 4 V) V V 3 11 12 7 4 (a 7 V) (a 4 V) (g 3 V) (g 11 V) (g 12 V) V (fun j d pos _ c m e n=>fa h k j d c 1 13 7 9 3 5 2 4 1 (i 1 V) (a 7 V) (a 9 V) (a 2 V) (a 4 V) (g 1 V) V (_cp.2 e) n (by have:=_cfl (aj 14 D j) (fun u=>(13:O)∈ag 14 D u.1);unfold aZ;omega)) (fun j d pos _ c m e n=>fa h k j d c 13 1 2 4 8 10 7 9 13 (i 13 V) (a 2 V) (a 4 V) (a 7 V) (a 9 V) (g 13 V) V (_cp.2 e) n (by have:=_cfl (aj 14 D j) (fun u=>(1:O)∈ag 14 D u.1);unfold aZ;omega))
lemma r9 {D:Dag} (h:ai 14 D) (k:ar D) (l:ap 14 D<=12) (p:aa 14 D=bU ⟨50,V⟩):False:=by
 have b:aa 14 D={3,4,8,9}:=by rw[p];decide
 have a:∀ v:O,v∈({3,4,8,9}:o)->v∈aa 14 D:=fun v f=>b▸f;have g:∀ v:O,v∉({3,4,8,9}:o)->v∉aa 14 D:=fun v f=>b▸f;have i:∀ v:O,v∉({3,4,8,9}:o)->v∈al 14 D:=fun v f=>by{by_contra q;exact f (b▸aN.2 q)};exact dZ h k l ⟨50,V⟩ p V 6 11 8 9 11 3 4 6 (a 8 V) (a 9 V) (a 3 V) (a 4 V) V V 1 13 7 9 4 (a 9 V) (a 4 V) (g 1 V) (g 13 V) (g 7 V) V (fun j d pos _ c m e n=>fa h k j d c 6 11 8 9 0 1 3 4 6 (i 6 V) (a 8 V) (a 9 V) (a 3 V) (a 4 V) (g 6 V) V (_cp.2 e) n (by have:=_cfl (aj 14 D j) (fun u=>(11:O)∈ag 14 D u.1);unfold aZ;omega)) (fun j d pos _ c m e n=>fa h k j d c 11 6 3 4 7 10 8 9 11 (i 11 V) (a 3 V) (a 4 V) (a 8 V) (a 9 V) (g 11 V) V (_cp.2 e) n (by have:=_cfl (aj 14 D j) (fun u=>(6:O)∈ag 14 D u.1);unfold aZ;omega))
lemma eO {D:Dag} (h:ai 14 D) (F:ar D) (G:bL 14 D=0) (d:O->ℕ) (s:aM 14 D d) {pos:O->ℕ×_d} (c:bA 14 eW D pos) (hR2:(aj 14 D d).card=2) (a b i0 ia ib va vb qa qb:O) (ha:a∈al 14 D) (hb:b∈al 14 D) (i:i0∈aa 14 D) (f:ia∈aa 14 D) (g:ib∈aa 14 D) (t:vb∉aa 14 D) (hg:a≠b/\i0≠ia/\i0≠ib/\ia≠ib /\(az a).card=3/\(az b).card=3 /\ac i0 a=true/\ac ia a=true/\ac a va=true/\va≠i0/\va≠ia /\ac i0 b=true/\ac ib b=true/\ac b vb=true /\ac ia qa=true/\a≠qa/\bK b qa=false/\ac ia b=false /\ac ib qb=true/\b≠qb/\bK a qb=false/\ac ib a=false) (H:(aZ D d a).Nonempty) (k:aZ D d a⊆aZ D d b):False:=by
 obtain⟨x,I,J,v,K,R,g0a,gaa,gva,L,M,g0b,gbb,gvb,gqa,w,gbqa,gnab,gqb,N,gaqb,gnba⟩:=hg;have hle2:(aZ D d a).card<=2:=by{have:=_cfl (aj 14 D d) (fun u=>a∈ag 14 D u.1);unfold aZ;omega};have S:(aZ D d b).card<=2:=by{have:=_cfl (aj 14 D d) (fun u=>b∈ag 14 D u.1);unfold aZ;omega};have T:0<(aZ D d a).card:=_cp.2 H;by_cases U:(aZ D d a).card=1;{exact o0 h F G d s c i f ha ⟨K,I,g0a,gaa,gva,L,M⟩ U k x ⟨qa,Or.inr ⟨gqa,w,gbqa,gnab⟩⟩}
 · have ha2:(aZ D d a).card=2:=by omega
   have W:aZ D d a=aZ D d b:=_eqc k (by omega);obtain⟨u,hu⟩:=H;have y:∀ u'∈aj 14 D d,a∈ag 14 D u'.1->b∈ag 14 D u'.1:=fun u' hu' ha'=>(ay.1 (k (ay.2 ⟨hu',ha'⟩))).2;have B:∀ u'∈aj 14 D d,b∈ag 14 D u'.1->a∈ag 14 D u'.1:=fun u' hu' hb'=>(ay.1 (by rw[W];exact ay.2 ⟨hu',hb'⟩)).2;have Z:a∈ag 14 D u.1/\b∈ag 14 D u.1:=⟨(ay.1 hu).2,(ay.1 (k hu)).2⟩;have l:=cV c f (cy h F d s c f ha y Z ⟨K,gaa,gqa,x,w,gbqa⟩);have m:=cy h F d s c g hb B ⟨Z.2,Z.1⟩ ⟨R,gbb,gqb,x.symm,N,gaqb⟩;have n:=aJ c i ((ae _ _).1 g0b);have q:=aJ c g ((ae _ _).1 gbb);obtain⟨ev,h0,P,C,-⟩:=bf h F c ((ae _ _).1 gvb);have r:(af 14 D b).card<=4:=by have:=bj h F d s b;omega
   have h1:=gh q n l h0 (fun e=>J.symm (c.2 _ g _ i e)) (fun e=>v.symm (c.2 _ g _ f e)) (fun e=>t (C _ g e.symm▸g)) (fun e=>I (c.2 _ i _ f e)) (fun e=>t (C _ i e.symm▸i)) (fun e=>t (C _ f e.symm▸f)) r
   have E:=cT h F G c g ((ae _ _).1 gbb) (fun p hp Q k'=>by
    rcases h1 p hp with rfl|rfl|rfl|rfl;{exact Q rfl};{exact J (_ms.1 (k' (cd c i)))};{exact v (_ms.1 (k' (cd c f)))}
    · exact t (_ms.1 (k' (ak.1 P).2.1)▸g))
   exact aH.1 gnba ((E a).1 m)
lemma r_ {D:Dag} (h:ai 14 D) (l:ar D) (m:ap 14 D<=12) (q:aa 14 D=bU ⟨42,V⟩):False:=by
 have b:aa 14 D={1,3,4,8}:=by rw[q];decide
 have a:∀ v:O,v∈({1,3,4,8}:o)->v∈aa 14 D:=fun v j=>b▸j;have k:∀ v:O,v∉({1,3,4,8}:o)->v∉aa 14 D:=fun v j=>b▸j;have d:∀ v:O,v∉({1,3,4,8}:o)->v∈al 14 D:=fun v j=>by{by_contra r;exact j (b▸aN.2 r)};exact dZ h l m ⟨42,V⟩ q V 11 13 3 4 6 1 4 2 (a 3 V) (a 4 V) (a 1 V) (a 4 V) V V 2 12 13 8 3 (a 8 V) (a 3 V) (k 2 V) (k 12 V) (k 13 V) V (fun n e pos f c g i p=>eO h l f n e c g 11 13 4 3 1 6 2 12 9 (d 11 V) (d 13 V) (a 4 V) (a 3 V) (a 1 V) (k 2 V) V i p) (fun n e pos f c g i p=>eO h l f n e c g 13 11 4 1 3 2 6 9 12 (d 13 V) (d 11 V) (a 4 V) (a 1 V) (a 3 V) (k 6 V) V i p)
lemma sc {D:Dag} (h:ai 14 D) (l:ar D) (m:ap 14 D<=12) (q:aa 14 D=bU ⟨45,V⟩):False:=by
 have b:aa 14 D={0,2,3,9}:=by rw[q];decide
 have a:∀ v:O,v∈({0,2,3,9}:o)->v∈aa 14 D:=fun v j=>b▸j;have k:∀ v:O,v∉({0,2,3,9}:o)->v∉aa 14 D:=fun v j=>b▸j;have d:∀ v:O,v∉({0,2,3,9}:o)->v∈al 14 D:=fun v j=>by{by_contra r;exact j (b▸aN.2 r)};exact dZ h l m ⟨45,V⟩ q V 8 12 0 2 6 2 3 5 (a 0 V) (a 2 V) (a 2 V) (a 3 V) V V 1 13 7 9 2 (a 9 V) (a 2 V) (k 1 V) (k 13 V) (k 7 V) V (fun n e pos f c g i p=>eO h l f n e c g 8 12 2 0 3 6 5 10 11 (d 8 V) (d 12 V) (a 2 V) (a 0 V) (a 3 V) (k 5 V) V i p) (fun n e pos f c g i p=>eO h l f n e c g 12 8 2 3 0 5 6 11 10 (d 12 V) (d 8 V) (a 2 V) (a 3 V) (a 0 V) (k 6 V) V i p)
lemma fb {D:Dag} (h:ai 14 D) (t:ar D) (hB0:bL 14 D=0) (br:O->ℕ) (hbm:cU 14 D br) {pos:O->ℕ×_d} (a:bA 14 eW D pos) {ua ub:Σ _:ℕ,ℕ} (hR':aj 14 D br={ua,ub}) (hru10:aZ D br 10={ua}) (h4:(4:O)∈aa 14 D) (h5:(5:O)∈aa 14 D) (w:(7:O)∈aa 14 D) (hn1:(1:O)∉aa 14 D) (hn2:(2:O)∉aa 14 D) (hn3:(3:O)∉aa 14 D) (hn6:(6:O)∉aa 14 D) (hn9:(9:O)∉aa 14 D) (T:(11:O)∉aa 14 D) (U:(12:O)∉aa 14 D) (W:(13:O)∉aa 14 D):False:=by
 have hbr:=bD hbm;have hp10:=eF h t hB0 br hbm a h4 h5 (by decide:(az 10).card=3/\(4:O)≠5/\ac 4 10=true/\ac 5 10=true/\ac 10 0=true/\(0:O)≠4/\(0:O)≠5) hru10;have k:∀ y:O,y≠10->aZ D br y⊆{ub}:=fun y hy u hu=>by{obtain⟨huR,hyu⟩:=ay.1 hu;rw[hR',_mi,_ms] at huR;rcases huR with rfl|rfl;{exact absurd (hp10 y hyu) hy};{exact _mss _}};have g:∀ y:O,y≠10->(af 14 D y).card<=3:=fun y hy=>by{have h1:=bj h t br hbr y;have h2:=_cl (k y hy);rw[_cs] at h2;omega};have n:∀ y:O,y≠10->3<=(af 14 D y).card->aZ D br y={ub}:=fun y hy h3=>by{have h1:=bj h t br hbr y;exact _eqc (k y hy) (by rw[_cs];omega)};have q:∀(y1 y2:O),y1≠10->y2≠10 ->3<=(af 14 D y1).card->3<=(af 14 D y2).card ->∃ P Q:ℕ×_d,P≠Q/\P∈af 14 D y1/\Q∈af 14 D y1 /\P∈af 14 D y2/\Q∈af 14 D y2:=by{intro y1 y2 hy1 hy2 h1 h2;have hru1:=n y1 hy1 h1;have hru2:=n y2 hy2 h2;obtain⟨P,Q,v,hall⟩:=fz h t br hbm hru1 h1;have hy1m:y1∈ag 14 D ub.1:=(ay.1 (by rw[hru1];exact _mss _)).2;have hy2m:y2∈ag 14 D ub.1:=(ay.1 (by rw[hru2];exact _mss _)).2;obtain⟨hP1,hQ1⟩:=hall y1 hy1m hru1 h1;obtain⟨hP2,hQ2⟩:=hall y2 hy2m hru2 h2;exact⟨P,Q,v,hP1,hQ1,hP2,hQ2⟩};have c:∀(x y l m:O),x≠10->y≠10 ->l∈aa 14 D->m∈aa 14 D->x∉aa 14 D->y∉aa 14 D ->(l≠m/\ac l x=true/\ac m y=true/\ac x y=true/\ac l y=false) ->3<=(af 14 D x).card->3<=(af 14 D y).card->False:=by
  intro x y l m r z i j hnx hny hg hsx hsy;obtain⟨P,Q,v,K,L,M,N⟩:=q x y r z hsx hsy;obtain⟨hxyi,g1,g2,g3,g4⟩:=hg;rw[ae] at g1 g2 g3;obtain⟨e,hex,hey,hfy,hfx⟩:=bf h t a g3;have heP:e≠P:=fun b=>el h.1 (b▸M) hey;have heQ:e≠Q:=fun b=>el h.1 (b▸N) hey;have hbeP:am e≠P:=fun b=>el h.1 K (by rw[<- b,aB];exact hex);have hbeQ:am e≠Q:=fun b=>el h.1 L (by rw[<- b,aB];exact hex);have hpx:=aJ a i g1;have hpy:=aJ a j g2;have X:pos l≠e:=fun b=>hny (hfy l i b.symm▸i);have hpybe:pos m≠am e:=fun b=>hnx (hfx m j b.symm▸j);have A:pos l∈af 14 D y:=by{rcases aT K L hex v heP.symm heQ.symm (g x r) (pos l) hpx with d|d|d;{exact d▸M};{exact d▸N};{exact absurd d X}};have B:pos m∈af 14 D x:=by{rcases aT M N hey v hbeP.symm hbeQ.symm (g y z) (pos m) hpy with d|d|d;{exact d▸K};{exact d▸L};{exact absurd d hpybe}};have R:pos l≠pos m:=fun b=>hxyi (a.2 l i m j b);have hpye:pos m≠e:=fun b=>hny (hfy m j b.symm▸j);have hWx:=aT hpx B hex R X hpye (g x r)
  have S:=cT h t hB0 a i g1 (fun p hp hne1 C=>by
   rcases hWx p hp with rfl|rfl|rfl;{exact hne1 rfl};{exact hxyi.symm (_ms.1 (C (cd a j)))}
   · exact hny (_ms.1 (C (ak.1 hey).2.1)▸i))
  exact aH.1 g4 ((S y).1 (ak.1 A).2.1)
 have f:∀(x y l m vx qx qy:O),x≠10->y≠10 ->l∈aa 14 D->m∈aa 14 D->vx∉aa 14 D ->(x≠y/\l≠m/\(az x).card=3/\(az y).card=3 /\ac l x=true/\ac m y=true/\ac l y=false /\ac x vx=true/\ac l qx=true/\qx≠x/\bK y qx=false /\ac m qy=true/\qy≠y/\bK x qy=false) ->3<=(af 14 D x).card->3<=(af 14 D y).card->False:=by
  intro x y l m vx qx qy r z i j hvx hg hx3 hy3;obtain⟨P,Q,v,K,L,M,N⟩:=q x y r z hx3 hy3;obtain⟨hxy,hixy,hdx,hdy,g1,g2,g3,g4,g5,hqxx,g6,g7,hqyy,g8⟩:=hg;have hpx:=aJ a i ((ae _ _).1 g1);have hpy:=aJ a j ((ae _ _).1 g2);by_cases A:pos l∈af 14 D y
  · by_cases B:pos m∈af 14 D x
    · obtain⟨ev,hev,hbev,hfv,-⟩:=bf h t a ((ae _ _).1 g4)
      have R:pos l≠pos m:=fun e=>hixy (a.2 _ i _ j e);have X:pos l≠ev:=fun e=>hvx (hfv _ i e.symm▸i);have hpye:pos m≠ev:=fun e=>hvx (hfv _ j e.symm▸j);have hWx:=aT hpx B hev R X hpye (g x r)
      have S:=cT h t hB0 a i ((ae _ _).1 g1) (fun p hp hne1 C=>by
       rcases hWx p hp with rfl|rfl|rfl;{exact hne1 rfl};{exact hixy.symm (_ms.1 (C (cd a j)))}
       · exact hvx (_ms.1 (C (ak.1 hbev).2.1)▸i))
      exact aH.1 g3 ((S y).1 (ak.1 A).2.1)
    · have hPne:P≠pos m:=fun e=>B (e▸K)
      have hQne:Q≠pos m:=fun e=>B (e▸L);obtain⟨e,he,hnx,hnq⟩:=bE h t hdy hxy.symm hqyy.symm (b3.1 g8);rcases aT M N hpy v hPne hQne (g y z) e he with rfl|rfl|rfl;{exact hnx (ak.1 K).2.1};{exact hnx (ak.1 L).2.1};{exact hnq ((a.1 m j).2.2.1 qy ((ae _ _).1 g7))}
  · have hPne:P≠pos l:=fun e=>A (e▸M)
    have hQne:Q≠pos l:=fun e=>A (e▸N);obtain⟨e,he,hny,hnq⟩:=bE h t hdx hxy hqxx.symm (b3.1 g6);rcases aT K L hpx v hPne hQne (g x r) e he with rfl|rfl|rfl;{exact hny (ak.1 M).2.1};{exact hny (ak.1 N).2.1};{exact hnq ((a.1 l i).2.2.1 qx ((ae _ _).1 g5))}
 have h1_3:3<=(af 14 D 1).card:=by{by_contra hc;have h9_3:3<=(af 14 D 9).card:=by{by_contra hc1;exact dl h t a 1 9 13 7 5 w h5 hn1 hn9 W V (by omega) (by omega)};have h13_3:3<=(af 14 D 13).card:=by{by_contra hc1;exact dl h t a 1 13 9 7 4 w h4 hn1 W hn9 V (by omega) (by omega)};exact f 9 13 5 4 6 10 10 V V h5 h4 hn6 V h9_3 h13_3};have h3_3:3<=(af 14 D 3).card:=by{by_contra hc;have h11_3:3<=(af 14 D 11).card:=by{by_contra hc1;exact dl h t a 3 11 12 7 4 w h4 hn3 T U V (by omega) (by omega)};have h12_3:3<=(af 14 D 12).card:=by{by_contra hc1;exact dl h t a 3 12 11 7 5 w h5 hn3 U T V (by omega) (by omega)};exact f 11 12 4 5 6 10 10 V V h4 h5 hn6 V h11_3 h12_3};have l9:(af 14 D 9).card<=2:=by{by_contra hc;exact c 1 9 7 5 V V w h5 hn1 hn9 V h1_3 (by omega)};have l13:(af 14 D 13).card<=2:=by{by_contra hc;exact c 1 13 7 4 V V w h4 hn1 W V h1_3 (by omega)};have l11:(af 14 D 11).card<=2:=by{by_contra hc;exact c 3 11 7 4 V V w h4 hn3 T V h3_3 (by omega)};have l12:(af 14 D 12).card<=2:=by{by_contra hc;exact c 3 12 7 5 V V w h5 hn3 U V h3_3 (by omega)};obtain⟨D9,-,hW9,hp9⟩:=cm h t a h5 (by decide:aP 5 9) V l9;obtain⟨D13,-,hW13,hp13⟩:=cm h t a h4 (by decide:aP 4 13) V l13;obtain⟨D11,-,hW11,hp11⟩:=cm h t a h4 (by decide:aP 4 11) V l11;obtain⟨D12,-,hW12,hp12⟩:=cm h t a h5 (by decide:aP 5 12) V l12;obtain⟨e19,h19_1,h19_9,hf9,hf19'⟩:=bf h t a (by decide:aP 1 9);obtain⟨e113,h113_1,E,hf13,hf113'⟩:=bf h t a (by decide:aP 1 13);obtain⟨e311,Y,F,hf11,hf311'⟩:=bf h t a (by decide:aP 3 11);obtain⟨e312,Z,G,hf12,hf312'⟩:=bf h t a (by decide:aP 3 12);rw[hW9,_mi,_ms] at h19_9;have hb9:am e19=D9:=h19_9.resolve_left (fun b=>hn1 (hf19' 5 h5 b▸h5));rw[hW13,_mi,_ms] at E;have hb13:am e113=D13:=E.resolve_left (fun b=>hn1 (hf113' 4 h4 b▸h4));rw[hW11,_mi,_ms] at F;have hb11:am e311=D11:=F.resolve_left (fun b=>hn3 (hf311' 4 h4 b▸h4));rw[hW12,_mi,_ms] at G;have hb12:am e312=D12:=G.resolve_left (fun b=>hn3 (hf312' 5 h5 b▸h5));have hD9_in:D9∈af 14 D 9:=by rw[hW9];simp
 have hD13_in:D13∈af 14 D 13:=by rw[hW13];simp
 have H:D11∈af 14 D 11:=by rw[hW11];simp
 have s:D12∈af 14 D 12:=by rw[hW12];simp
 have hp7_1:=aJ a w (by decide:aP 7 1);have hp7_3:=aJ a w (by decide:aP 7 3);have h1_913:e19≠e113:=fun b=>hp9 13 V V (by rw[<- hb9,b,hb13];exact hD13_in);have h1_9p:e19≠pos 7:=fun b=>hn9 (hf9 7 w b▸w);have h0:e113≠pos 7:=fun b=>W (hf13 7 w b▸w);have I:e311≠e312:=fun b=>hp11 12 V V (by rw[<- hb11,b,hb12];exact s);have h6:e311≠pos 7:=fun b=>T (hf11 7 w b▸w);have h8:e312≠pos 7:=fun b=>U (hf12 7 w b▸w);obtain⟨P,Q,v,hP1,hQ1,hP3,hQ3⟩:=q 1 3 V V h1_3 h3_3;have J:∀ e,e∈af 14 D 1->e∈af 14 D 3->e=pos 7:=by
  intro e he1 he3;rcases aT h19_1 h113_1 hp7_1 h1_913 h1_9p h0 (g 1 V) e he1 with d|d|d
  · rw[d] at he3
    rcases aT Y Z hp7_3 I h6 h8 (g 3 V) e19 he3 with b|b|b;{exact absurd (by rw[<- hb9,b,hb11];exact H) (hp9 11 V V)};{exact absurd (by rw[<- hb9,b,hb12];exact s) (hp9 12 V V)};{exact absurd b h1_9p}
  · rw[d] at he3
    rcases aT Y Z hp7_3 I h6 h8 (g 3 V) e113 he3 with b|b|b;{exact absurd (by rw[<- hb13,b,hb11];exact H) (hp13 11 V V)};{exact absurd (by rw[<- hb13,b,hb12];exact s) (hp13 12 V V)};{exact absurd b h0}
  · exact d
 exact v ((J P hP1 hP3).trans (J Q hQ1 hQ3).symm)
lemma lQ {D:Dag} (h:ai 14 D) (s:ar D) (k:bL 14 D=0) {pos:O->ℕ×_d} (a:bA 14 eW D pos) {i x y:O} (c:i∈aa 14 D) (u:y∉aa 14 D) (d:aP i x) (l:aP x y) (f:(af 14 D x).card<=2):∀ t,t∈ag 14 D (aw D (pos i))->aP i t:=by
 have m:=aJ a c d;obtain⟨e,v,n,q,-⟩:=bf h s a l;have r:pos i≠e:=fun w=>u (q i c w.symm▸c)
 have b:=cT h s k a c d (fun p z g j=>by
  rcases gG m v r f p z with rfl|rfl;{exact g rfl}
  · exact u (_ms.1 (j (ak.1 n).2.1)▸c))
 exact fun t A=>(b t).1 A
lemma gi {D:Dag} (h:ai 14 D) (x:ar D) (hB0:bL 14 D=0) (d:O->ℕ) (hbm:cU 14 D d) {pos:O->ℕ×_d} (a:bA 14 eW D pos) {u1 u2:Σ _:ℕ,ℕ} (C:u1≠u2) (s:aj 14 D d={u1,u2}) (J:(4:O)∈aa 14 D) (K:(5:O)∈aa 14 D) (h7:(7:O)∈aa 14 D) (hB:(1:O)∉aa 14 D) (hC:(2:O)∉aa 14 D) (E:(3:O)∉aa 14 D) (F:(6:O)∉aa 14 D) (hn9:(9:O)∉aa 14 D) (W:(11:O)∉aa 14 D) (hE:(12:O)∉aa 14 D) (hn13:(13:O)∉aa 14 D) (l1:(af 14 D 1).card<=2) (l3:(af 14 D 3).card<=2):False:=by
 have L:=bD hbm;have hF:∀ v:O,v∉aa 14 D->v∈al 14 D:=fun v hv=>by{by_contra hc;exact hv (aN.2 hc)};obtain⟨Z1,-,hW1,hp1⟩:=cm h x a h7 (by decide:aP 7 1) V l1;obtain⟨Z3,-,hW3,hp3⟩:=cm h x a h7 (by decide:aP 7 3) V l3;obtain⟨e91,M,h2,hG,hf9'⟩:=bf h x a (by decide:aP 9 1);obtain⟨e96,h3,h6,hH,-⟩:=bf h x a (by decide:aP 9 6);obtain⟨e131,X,h131_1,hf1_13,hf13'⟩:=bf h x a (by decide:aP 13 1);obtain⟨e132,hI,h132_2,hf2_13,-⟩:=bf h x a (by decide:aP 13 2);obtain⟨e113,f,i,N,hf11'⟩:=bf h x a (by decide:aP 11 3);obtain⟨e116,g,j,R,-⟩:=bf h x a (by decide:aP 11 6);obtain⟨e123,k,S,hj,hf12'⟩:=bf h x a (by decide:aP 12 3);obtain⟨e122,l,y,hk,-⟩:=bf h x a (by decide:aP 12 2);have h2':=h2;have h131_1':=h131_1;rw[hW1,_mi,_ms] at h2' h131_1';have hn:am e91=Z1:=h2'.resolve_left (fun b=>hn9 (hf9' 7 h7 b▸h7));have hJ:am e131=Z1:=h131_1'.resolve_left (fun b=>hn13 (hf13' 7 h7 b▸h7));have hr:e131=e91:=by rw[<- aB e131,<-aB e91,hJ,hn]
 have i':=i;have S':=S;rw[hW3,_mi,_ms] at i' S';have hb113:am e113=Z3:=i'.resolve_left (fun b=>W (hf11' 7 h7 b▸h7));have hK:am e123=Z3:=S'.resolve_left (fun b=>hE (hf12' 7 h7 b▸h7));have hp5_9:=aJ a K (by decide:aP 5 9);have ho:=aJ a K (by decide:aP 5 12);have hp4_11:=aJ a J (by decide:aP 4 11);have hp4_13:=aJ a J (by decide:aP 4 13);have hZ1_in:Z1∈af 14 D 1:=by rw[hW1];simp
 have hZ3_in:Z3∈af 14 D 3:=by rw[hW3];simp
 have T:pos 5≠e91:=fun b=>hB (hG 5 K b.symm▸K);have h8:pos 5≠e96:=fun b=>F (hH 5 K b.symm▸K);have ha:e91≠e96:=fun b=>hp1 6 V V (by rw[<- hn,b];exact h6);have m:pos 4≠e113:=fun b=>E (N 4 J b.symm▸J);have n:pos 4≠e116:=fun b=>F (R 4 J b.symm▸J);have q:e113≠e116:=fun b=>hp3 6 V V (by rw[<- hb113,b];exact j);have z:pos 5≠e123:=fun b=>E (hj 5 K b.symm▸K);have A:pos 5≠e122:=fun b=>hC (hk 5 K b.symm▸K);have B:e123≠e122:=fun b=>hp3 2 V V (by rw[<- hK,b];exact y);have h13_12:pos 4≠e131:=fun b=>hB (hf1_13 4 J b.symm▸J);have h13_13:pos 4≠e132:=fun b=>hC (hf2_13 4 J b.symm▸J);have h13_23:e131≠e132:=fun b=>hp1 2 V V (by rw[<- hJ,b];exact h132_2);have h9_3:3<=(af 14 D 9).card:=d6 hp5_9 M h3 T h8 ha;have h11_3:3<=(af 14 D 11).card:=d6 hp4_11 f g m n q;have h12_3:3<=(af 14 D 12).card:=d6 ho k l z A B;have h13_3:3<=(af 14 D 13).card:=d6 hp4_13 X hI h13_12 h13_13 h13_23;have hne9:(aZ D d 9).Nonempty:=_cp.1 (by have:=bj h x d L 9;omega);have G:(aZ D d 11).Nonempty:=_cp.1 (by have:=bj h x d L 11;omega);have hb:(aZ D d 12).Nonempty:=_cp.1 (by have:=bj h x d L 12;omega);have hne13:(aZ D d 13).Nonempty:=_cp.1 (by have:=bj h x d L 13;omega);have c:∀(v t iv it nv1 nv2 nt1 nt2:O) (hL hM hs ht:ℕ×_d),iv∈aa 14 D->it∈aa 14 D ->v∉aa 14 D->t∉aa 14 D ->nv1∉aa 14 D->nv2∉aa 14 D->nt1∉aa 14 D->nt2∉aa 14 D ->(v≠t/\iv≠it/\(az v).card=3/\(az t).card=3 /\ac iv v=true/\ac it t=true/\ac iv t=false/\ac it v=false /\ac iv 10=true/\v≠10/\bK t 10=false /\ac it 10=true/\t≠10/\bK v 10=false) ->(hL∈af 14 D v/\hM∈af 14 D v /\am hL∈af 14 D nv1/\am hM∈af 14 D nv2 /\pos iv≠hL/\pos iv≠hM/\hL≠hM) ->(hs∈af 14 D t/\ht∈af 14 D t /\am hs∈af 14 D nt1/\am ht∈af 14 D nt2 /\pos it≠hs/\pos it≠ht/\hs≠ht/\pos iv≠hs/\pos iv≠ht) ->(aZ D d v).Nonempty->aZ D d v⊆aZ D d t->False:=by
  intro v t iv it nv1 nv2 nt1 nt2 hL hM hs ht h1 hx hnv hnt hnv1 hnv2 hnt1 hnt2 hg hd U hne hN;obtain⟨hvt,hO,hdv,hdt,giv,git,gnivt,gnitv,giv10,hv10,gnt10,git10,ht10,gnv10⟩:=hg;obtain⟨u,hu⟩:=hne;have hres:∀ u'∈aj 14 D d,v∈ag 14 D u'.1->t∈ag 14 D u'.1:=fun u' hu' hv'=>(ay.1 (hN (ay.2 ⟨hu',hv'⟩))).2;have hw:v∈ag 14 D u.1/\t∈ag 14 D u.1:=⟨(ay.1 hu).2,(ay.1 (hN hu)).2⟩;have htv:=cy h x d L a h1 (hF v hnv) hres hw ⟨hdv,giv,giv10,hvt,hv10,gnt10⟩;have hcardv:(aZ D d v).card<=2:=by{have:=_cl (s▸_fs _ _:aZ D d v⊆{u1,u2});rw[_c2 C] at this;exact this};have hcardt:(aZ D d t).card<=2:=by{have:=_cl (s▸_fs _ _:aZ D d t⊆{u1,u2});rw[_c2 C] at this;exact this};have hposv:0<(aZ D d v).card:=_cp.2 ⟨u,hu⟩;by_cases hv1:(aZ D d v).card=1
  · have hWv3:(af 14 D v).card<=3:=by have:=bj h x d L v;omega
    have hWv:=aT (aJ a h1 ((ae _ _).1 giv)) hd.1 hd.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2.1 hd.2.2.2.2.2.2 hWv3
    have hf:=cT h x hB0 a h1 ((ae _ _).1 giv) (fun p hp hP hN'=>by
     rcases hWv p hp with rfl|rfl|rfl;{exact hP rfl};{exact hnv1 (_ms.1 (hN' (ak.1 hd.2.2.1).2.1)▸h1)}
     · exact hnv2 (_ms.1 (hN' (ak.1 hd.2.2.2.1).2.1)▸h1))
    exact aH.1 gnivt ((hf t).1 htv)
  · have heq:aZ D d v=aZ D d t:=_eqc hN (by omega)
    have hres2:∀ u'∈aj 14 D d,t∈ag 14 D u'.1->v∈ag 14 D u'.1:=fun u' hu' ht'=>(ay.1 (by rw[heq];exact ay.2 ⟨hu',ht'⟩)).2;have hvt':=cy h x d L a hx (hF t hnt) hres2 ⟨hw.2,hw.1⟩ ⟨hdt,git,git10,hvt.symm,ht10,gnv10⟩;have hWt4:(af 14 D t).card<=4:=by have:=bj h x d L t;omega
    have hWt:=gh (aJ a hx ((ae _ _).1 git)) (cV a h1 htv) U.1 U.2.1 (fun e=>hO.symm (a.2 _ hx _ h1 e)) U.2.2.2.2.1 U.2.2.2.2.2.1 U.2.2.2.2.2.2.2.1 U.2.2.2.2.2.2.2.2 U.2.2.2.2.2.2.1 hWt4
    have hf:=cT h x hB0 a hx ((ae _ _).1 git) (fun p hp hP hN'=>by
     rcases hWt p hp with rfl|rfl|rfl|rfl;{exact hP rfl};{exact hO (_ms.1 (hN' (cd a h1)))};{exact hnt1 (_ms.1 (hN' (ak.1 U.2.2.1).2.1)▸hx)}
     · exact hnt2 (_ms.1 (hN' (ak.1 U.2.2.2.1).2.1)▸hx))
    exact aH.1 gnitv ((hf v).1 hvt')
 have hy:¬ aZ D d 9⊆aZ D d 11:=c 9 11 5 4 1 6 3 6 e91 e96 e113 e116 K J hn9 W hB F E F V ⟨M,h3,h2,h6,T,h8,ha⟩ ⟨f,g,i,j,m,n,q,fun b=>E (N 5 K b.symm▸K),fun b=>F (R 5 K b.symm▸K)⟩ hne9;have hz:¬ aZ D d 11⊆aZ D d 9:=c 11 9 4 5 3 6 1 6 e113 e116 e91 e96 J K W hn9 E F hB F V ⟨f,g,i,j,m,n,q⟩ ⟨M,h3,h2,h6,T,h8,ha,fun b=>hB (hG 4 J b.symm▸J),fun b=>F (hH 4 J b.symm▸J)⟩ G;have H:¬ aZ D d 12⊆aZ D d 11:=c 12 11 5 4 3 2 3 6 e123 e122 e113 e116 K J hE W E hC E F V ⟨k,l,S,y,z,A,B⟩ ⟨f,g,i,j,m,n,q,fun b=>E (N 5 K b.symm▸K),fun b=>F (R 5 K b.symm▸K)⟩ hb;have I:¬ aZ D d 11⊆aZ D d 12:=c 11 12 4 5 3 6 3 2 e113 e116 e123 e122 J K W hE E F E hC V ⟨f,g,i,j,m,n,q⟩ ⟨k,l,S,y,z,A,B,fun b=>E (hj 4 J b.symm▸J),fun b=>hC (hk 4 J b.symm▸J)⟩ G;have hA:∃ ua,aZ D d 9={ua}/\aZ D d 12={ua}:=by
  rcases dJ C (s▸_fs _ _) (s▸_fs _ _) hne9 G hy hz with ⟨h9,h11⟩|⟨h9,h11⟩
  · rcases dJ C (s▸_fs _ _) (s▸_fs _ _) hb G H I with ⟨h12',_⟩|⟨_,hR⟩
    · exact⟨u1,h9,h12'⟩
    · exact absurd (singleton_injective (h11.symm.trans hR)) C.symm
  · rcases dJ C (s▸_fs _ _) (s▸_fs _ _) hb G H I with ⟨_,hR⟩|⟨h12',_⟩
    · exact absurd (singleton_injective (h11.symm.trans hR)) C
    · exact⟨u2,h9,h12'⟩
 obtain⟨ua,hq,hi⟩:=hA;have h9le3:(af 14 D 9).card<=3:=by have:=bj h x d L 9;rw[hq,_cs] at this;omega
 have h12le3:(af 14 D 12).card<=3:=by have:=bj h x d L 12;rw[hi,_cs] at this;omega
 obtain⟨P,Q,hPQ,hall⟩:=fz h x d hbm hq h9_3;have h9ua:9∈ag 14 D ua.1:=(ay.1 (by rw[hq];exact _mss _)).2;have h12ua:12∈ag 14 D ua.1:=(ay.1 (by rw[hi];exact _mss _)).2;obtain⟨hP9,hQ9⟩:=hall 9 h9ua hq h9_3;obtain⟨hP12,hQ12⟩:=hall 12 h12ua hi h12_3;have w:e91∉af 14 D 12:=by{intro hm;rcases aT ho k l z A B h12le3 e91 hm with b|b|b;{exact T b.symm};{exact hp1 3 V V (by rw[<- hn,b,hK];exact hZ3_in)};{exact hp1 2 V V (by rw[<- hn,b];exact y)}};have hPne:P≠e91:=fun b=>w (b▸hP12);have hQne:Q≠e91:=fun b=>w (b▸hQ12);obtain⟨e,he,hS,hn13e⟩:=bE h x (by decide:(az 9).card=3) (by decide:(9:O)≠12) (by decide:(9:O)≠13) (b3.1 (by decide:bK 12 13=false));rcases aT hP9 hQ9 M hPQ hPne hQne h9le3 e he with rfl|rfl|rfl;{exact hS (ak.1 hP12).2.1};{exact hS (ak.1 hQ12).2.1};{exact hn13e (ak.1 (hr▸X)).2.1}
lemma sd {D:Dag} (h:ai 14 D) (m:ar D) (h12:ap 14 D<=12) (hI:aa 14 D=bU ⟨40,V⟩):False:=by
 have hel:=aV 14 D;have F:aa 14 D={0,4,5,7}:=by rw[hI];decide
 rw[F,show({0,4,5,7}:o).card=4 from by decide] at hel;by_cases h0:bd 14 D<=(al 14 D).card;{exact dn h m h0 ⟨40,V⟩ hI};by_cases h1:bd 14 D=(al 14 D).card+1;{exact dp h m h12 h1 ⟨40,V⟩ V hI};have hts:=bg 14 D;have R:bL 14 D=0:=by omega
 obtain⟨br,L⟩:=b_ bs h.1 (bF m);have n:=bD L;obtain⟨pos,b⟩:=bQ bs h (bF m);have hR2:(aj 14 D br).card=2:=by have:=bS h.1 br n;omega
 obtain⟨u1,u2,y,g⟩:=_ct2.1 hR2;have c:∀ v:O,v∈({0,4,5,7}:o)->v∈aa 14 D:=fun v hv=>F▸hv;have i:∀ v:O,v∉({0,4,5,7}:o)->v∉aa 14 D:=fun v hv=>F▸hv;have C:∀ v:O,v∉({0,4,5,7}:o)->v∈al 14 D:=fun v hv=>by{by_contra hc;exact hv (F▸aN.2 hc)};have h10_3:=cx h m b (u:=10) (v:=0) (c 4 V) (c 5 V) V;have h7:(aZ D br 10).Nonempty:=_cp.1 (by have:=bj h m br n 10;omega);have k:aZ D br 10⊆{u1,u2}:=g▸_fs _ _;by_cases z:u1∈aZ D br 10 <;> by_cases S:u2∈aZ D br 10
 · have d:aZ D br 10={u1,u2}:=by
    refine Subset.antisymm k (fun u w=>?_);simp only[_mi,_ms] at w;rcases w with rfl|rfl <;> assumption
   by_cases h13:(af 14 D 1).card<=2/\(af 14 D 3).card<=2;{exact gi h m R br L b y g (c 4 V) (c 5 V) (c 7 V) (i 1 V) (i 2 V) (i 3 V) (i 6 V) (i 9 V) (i 11 V) (i 12 V) (i 13 V) h13.1 h13.2}
   ·
     have s:pos 7∈af 14 D 10:=by
      by_cases l1:(af 14 D 1).card<=2
      · have h3_3:3<=(af 14 D 3).card:=by omega
        obtain⟨u,w⟩:=_cp.1 (by have:=bj h m br n 3;omega:0<(aZ D br 3).card);have T:aZ D br 3⊆aZ D br 10:=by rw[d,<-g];exact _fs _ _
        have A:∀ u'∈aj 14 D br,(3:O)∈ag 14 D u'.1->10∈ag 14 D u'.1:=fun u' w' h3'=>(ay.1 (T (ay.2 ⟨w',h3'⟩))).2;exact cV b (c 7 V) (cy h m br n b (c 7 V) (C 3 V) A ⟨(ay.1 w).2,(ay.1 (T w)).2⟩ (by decide:(az 3).card=3/\ac 7 3=true/\ac 7 1=true/\(3:O)≠10/\(3:O)≠1/\ac 10 1=false))
      · obtain⟨u,w⟩:=_cp.1 (by have:=bj h m br n 1;omega:0<(aZ D br 1).card)
        have X:aZ D br 1⊆aZ D br 10:=by rw[d,<-g];exact _fs _ _
        have A:∀ u'∈aj 14 D br,(1:O)∈ag 14 D u'.1->10∈ag 14 D u'.1:=fun u' w' h1'=>(ay.1 (X (ay.2 ⟨w',h1'⟩))).2;exact cV b (c 7 V) (cy h m br n b (c 7 V) (C 1 V) A ⟨(ay.1 w).2,(ay.1 (X w)).2⟩ (by decide:(az 1).card=3/\ac 7 1=true/\ac 7 3=true/\(1:O)≠10/\(1:O)≠3/\ac 10 3=false))
     have h4:3<=(af 14 D 1).card:=by{by_contra hc;have hf7:=lQ h m R b (x:=1) (c 7 V) (i 9 V) V V (by omega);exact absurd (hf7 10 (ak.1 s).2.1) V};have G:=aJ b (c 0 V) (by decide:aP 0 10);have H:=aJ b (c 4 V) (by decide:aP 4 10);have I:=aJ b (c 5 V) (by decide:aP 5 10);have Y:(af 14 D 10).card<=4:=by have:=bj h m br n 10;rw[d,_c2 y] at this;omega
     have h5:=gh G H I s (fun e=>absurd (b.2 _ (c 0 V) _ (c 4 V) e) V) (fun e=>absurd (b.2 _ (c 0 V) _ (c 5 V) e) V) (fun e=>absurd (b.2 _ (c 0 V) _ (c 7 V) e) V) (fun e=>absurd (b.2 _ (c 4 V) _ (c 5 V) e) V) (fun e=>absurd (b.2 _ (c 4 V) _ (c 7 V) e) V) (fun e=>absurd (b.2 _ (c 5 V) _ (c 7 V) e) V) Y;have f:∀ j∈({0,4,5}:o),∀ t,t∈ag 14 D (aw D (pos j))->aP j t:=by
      intro j hj t ht;have l:∀ a∈({0,4,5}:o),a∈({0,4,5,7}:o)/\aP a 10/\a≠7:=V;have hjI:j∈aa 14 D:=c j (l j hj).1;have hj10:aP j 10:=(l j hj).2.1;have h7j:j≠7:=(l j hj).2.2
      have hf:=cT h m R b hjI hj10 (fun p hp J K=>by
       rcases h5 p hp with rfl|rfl|rfl|rfl
       · by_cases h0j:j=0
         · exact J (by rw[h0j])
         · exact h0j (_ms.1 (K (cd b (c 0 V)))).symm
       · by_cases h4j:j=4
         · exact J (by rw[h4j])
         · exact h4j (_ms.1 (K (cd b (c 4 V)))).symm
       · by_cases h5j:j=5
         · exact J (by rw[h5j])
         · exact h5j (_ms.1 (K (cd b (c 5 V)))).symm
       · exact h7j (_ms.1 (K (cd b (c 7 V)))).symm)
      exact(hf t).1 ht
     have M:(aZ D br 1).card=1:=by
      have hpos1:0<(aZ D br 1).card:=by have:=bj h m br n 1;omega
      have hle2:(aZ D br 1).card<=2:=by{have:=_cl (g▸_fs _ _:aZ D br 1⊆{u1,u2});rw[_c2 y] at this;exact this};by_contra J;have h8:aZ D br 1={u1,u2}:=_eqc (g▸_fs _ _) (by rw[_c2 y];omega);have q:aZ D br 10⊆aZ D br 1:=by rw[d,h8]
      have A:∀ u'∈aj 14 D br,(10:O)∈ag 14 D u'.1->1∈ag 14 D u'.1:=fun u' w' h10'=>(ay.1 (q (ay.2 ⟨w',h10'⟩))).2;have h3:=cy h m br n b (c 4 V) (C 10 V) A ⟨(ay.1 z).2,(ay.1 (q z)).2⟩ (by decide:(az 10).card=3/\ac 4 10=true/\ac 4 11=true/\(10:O)≠1/\(10:O)≠11/\ac 1 11=false);exact absurd (f 4 V 1 h3) V
     obtain⟨u0,Z⟩:=_c1.1 M;have N:u0∈aZ D br 10:=by{rw[d];exact(g▸_fs _ _:aZ D br 1⊆{u1,u2}) (by rw[Z];exact _mss _)};obtain⟨P,Q,hPQ,-,-,h2⟩:=dV h m br L Z h4;obtain⟨P,Q,hPQ,h9,ha,h2⟩:=dV h m br L Z h4;have h6:aW 14 D (ao 14 D {10})=∅:=by{have hb:=bj h m br n 10;have h4_10:4<=(af 14 D 10).card:=mm G H I s (fun e=>absurd (b.2 _ (c 0 V) _ (c 4 V) e) V) (fun e=>absurd (b.2 _ (c 0 V) _ (c 5 V) e) V) (fun e=>absurd (b.2 _ (c 0 V) _ (c 7 V) e) V) (fun e=>absurd (b.2 _ (c 4 V) _ (c 5 V) e) V) (fun e=>absurd (b.2 _ (c 4 V) _ (c 7 V) e) V) (fun e=>absurd (b.2 _ (c 5 V) _ (c 7 V) e) V);rw[d,_c2 y] at hb;exact card_eq_zero.1 (by omega)};obtain⟨h10P,h10Q⟩:=h2 10 (ay.1 N).2;have hP10:P∈af 14 D 10:=gD h.1 h6 (ak.1 h9).1 (cY h.1 h9) h10P;have hQ10:Q∈af 14 D 10:=gD h.1 h6 (ak.1 ha).1 (cY h.1 ha) h10Q;have r:∀ e,e∈af 14 D 1->e∈af 14 D 10->e=pos 7:=by{intro e hd he10;rcases h5 e he10 with rfl|rfl|rfl|rfl;{exact absurd (f 0 V 1 (ak.1 hd).2.1) V};{exact absurd (f 4 V 1 (ak.1 hd).2.1) V};{exact absurd (f 5 V 1 (ak.1 hd).2.1) V};{rfl}};exact hPQ ((r P h9 hP10).trans (r Q ha hQ10).symm)
 · have E:aZ D br 10={u1}:=by
    refine Subset.antisymm (fun u w=>?_) (singleton_subset_iff.2 z);have c':=k w;simp only[_mi,_ms] at c';rcases c' with rfl|rfl;{exact _mss _};{exact absurd w S}
   exact fb h m R br L b g E (c 4 V) (c 5 V) (c 7 V) (i 1 V) (i 2 V) (i 3 V) (i 6 V) (i 9 V) (i 11 V) (i 12 V) (i 13 V)
 · have E:aZ D br 10={u2}:=by
    refine Subset.antisymm (fun u w=>?_) (singleton_subset_iff.2 S);have c':=k w;simp only[_mi,_ms] at c';rcases c' with rfl|rfl;{exact absurd w z};{exact _mss _}
   exact fb h m R br L b (by rw[g,pair_comm]) E (c 4 V) (c 5 V) (c 7 V) (i 1 V) (i 2 V) (i 3 V) (i 6 V) (i 9 V) (i 11 V) (i 12 V) (i 13 V)
 · obtain⟨u,w⟩:=h7
   have c':=k w;simp only[_mi,_ms] at c';rcases c' with rfl|rfl;{exact absurd w z};{exact absurd w S}
lemma se {D:Dag} (h:ai 14 D) (l:ar D) (h12:ap 14 D<=12) (hI:aa 14 D=bU ⟨44,V⟩):False:=by
 have hel:=aV 14 D;have S:aa 14 D={4,5,7,8}:=by rw[hI];decide
 rw[S,show({4,5,7,8}:o).card=4 from by decide] at hel;by_cases h0:bd 14 D<=(al 14 D).card;{exact dn h l h0 ⟨44,V⟩ hI};by_cases h1:bd 14 D=(al 14 D).card+1;{exact dp h l h12 h1 ⟨44,V⟩ V hI};have hts:=bg 14 D;have h7:bL 14 D=0:=by omega
 obtain⟨br,Z⟩:=b_ bs h.1 (bF l);have k:=bD Z;obtain⟨pos,b⟩:=bQ bs h (bF l);have hR2:(aj 14 D br).card=2:=by have:=bS h.1 br k;omega
 obtain⟨u1,u2,E,i⟩:=_ct2.1 hR2;have c:∀ v:O,v∈({4,5,7,8}:o)->v∈aa 14 D:=fun v hv=>S▸hv;have g:∀ v:O,v∉({4,5,7,8}:o)->v∉aa 14 D:=fun v hv=>S▸hv;have s:∀ v:O,v∉({4,5,7,8}:o)->v∈al 14 D:=fun v hv=>by{by_contra hc;exact hv (S▸aN.2 hc)};have h10_3:=cx h l b (u:=10) (v:=0) (c 4 V) (c 5 V) V;have hne10:(aZ D br 10).Nonempty:=_cp.1 (by have:=bj h l br k 10;omega);have y:aZ D br 10⊆{u1,u2}:=i▸_fs _ _;by_cases J:u1∈aZ D br 10 <;> by_cases h8:u2∈aZ D br 10
 · have d:aZ D br 10={u1,u2}:=by
    refine Subset.antisymm y (fun u w=>?_);simp only[_mi,_ms] at w;rcases w with rfl|rfl <;> assumption
   by_cases h13:(af 14 D 1).card<=2/\(af 14 D 3).card<=2;{exact gi h l h7 br Z b E i (c 4 V) (c 5 V) (c 7 V) (g 1 V) (g 2 V) (g 3 V) (g 6 V) (g 9 V) (g 11 V) (g 12 V) (g 13 V) h13.1 h13.2}
   ·
     have G:pos 7∈af 14 D 10:=by
      by_cases l1:(af 14 D 1).card<=2
      · have h3_3:3<=(af 14 D 3).card:=by omega
        obtain⟨u,w⟩:=_cp.1 (by have:=bj h l br k 3;omega:0<(aZ D br 3).card);have ha:aZ D br 3⊆aZ D br 10:=by rw[d,<-i];exact _fs _ _
        have m:∀ u'∈aj 14 D br,(3:O)∈ag 14 D u'.1->10∈ag 14 D u'.1:=fun u' w' h3'=>(ay.1 (ha (ay.2 ⟨w',h3'⟩))).2;exact cV b (c 7 V) (cy h l br k b (c 7 V) (s 3 V) m ⟨(ay.1 w).2,(ay.1 (ha w)).2⟩ (by decide:(az 3).card=3/\ac 7 3=true/\ac 7 1=true/\(3:O)≠10/\(3:O)≠1/\ac 10 1=false))
      · obtain⟨u,w⟩:=_cp.1 (by have:=bj h l br k 1;omega:0<(aZ D br 1).card)
        have hb:aZ D br 1⊆aZ D br 10:=by rw[d,<-i];exact _fs _ _
        have m:∀ u'∈aj 14 D br,(1:O)∈ag 14 D u'.1->10∈ag 14 D u'.1:=fun u' w' h1'=>(ay.1 (hb (ay.2 ⟨w',h1'⟩))).2;exact cV b (c 7 V) (cy h l br k b (c 7 V) (s 1 V) m ⟨(ay.1 w).2,(ay.1 (hb w)).2⟩ (by decide:(az 1).card=3/\ac 7 1=true/\ac 7 3=true/\(1:O)≠10/\(1:O)≠3/\ac 10 3=false))
     have h1_3:3<=(af 14 D 1).card:=by{by_contra hc;have hf7:=lQ h l h7 b (x:=1) (c 7 V) (g 9 V) V V (by omega);exact absurd (hf7 10 (ak.1 G).2.1) V};have T:=aJ b (c 4 V) (by decide:aP 4 10);have U:=aJ b (c 5 V) (by decide:aP 5 10);obtain⟨e100,K,W,r,-⟩:=bf h l b (by decide:aP 10 0);have hd:(af 14 D 10).card<=4:=by have:=bj h l br k 10;rw[d,_c2 E] at this;omega
     have h45:pos 4≠pos 5:=fun e=>absurd (b.2 _ (c 4 V) _ (c 5 V) e) V;have h47:pos 4≠pos 7:=fun e=>absurd (b.2 _ (c 4 V) _ (c 7 V) e) V;have h57:pos 5≠pos 7:=fun e=>absurd (b.2 _ (c 5 V) _ (c 7 V) e) V;have h4e:pos 4≠e100:=fun e=>g 0 V (r 4 (c 4 V) e.symm▸c 4 V);have h5e:pos 5≠e100:=fun e=>g 0 V (r 5 (c 5 V) e.symm▸c 5 V);have h7e:pos 7≠e100:=fun e=>g 0 V (r 7 (c 7 V) e.symm▸c 7 V);have B:=gh T U G K h45 h47 h4e h57 h5e h7e hd;have X:aW 14 D (ao 14 D {10})=∅:=by{have hcc10:=bj h l br k 10;have h4_10:4<=(af 14 D 10).card:=mm T U G K h45 h47 h4e h57 h5e h7e;rw[d,_c2 E] at hcc10;exact card_eq_zero.1 (by omega)};have f:∀ j∈({4,5}:o),∀ t,t∈ag 14 D (aw D (pos j))->aP j t:=by
      intro j hj t ht;have H:∀ a∈({4,5}:o),a∈({4,5,7,8}:o)/\aP a 10/\a≠7:=V;have hC:j∈aa 14 D:=c j (H j hj).1;have hj10:aP j 10:=(H j hj).2.1;have h7j:j≠7:=(H j hj).2.2
      have hf:=cT h l h7 b hC hj10 (fun p hp he Y=>by
       rcases B p hp with rfl|rfl|rfl|rfl
       · by_cases h4j:j=4
         · exact he (by rw[h4j])
         · exact h4j (_ms.1 (Y (cd b (c 4 V)))).symm
       · by_cases h5j:j=5
         · exact he (by rw[h5j])
         · exact h5j (_ms.1 (Y (cd b (c 5 V)))).symm
       · exact h7j (_ms.1 (Y (cd b (c 7 V)))).symm
       · exact g 0 V (_ms.1 (Y (ak.1 W).2.1)▸hC))
      exact(hf t).1 ht
     have h2:(aZ D br 1).card=1:=by
      have hpos1:0<(aZ D br 1).card:=by have:=bj h l br k 1;omega
      have hle2:(aZ D br 1).card<=2:=by{have:=_cl (i▸_fs _ _:aZ D br 1⊆{u1,u2});rw[_c2 E] at this;exact this};by_contra he;have hru1R:aZ D br 1={u1,u2}:=_eqc (i▸_fs _ _) (by rw[_c2 E];omega);have F:aZ D br 10⊆aZ D br 1:=by rw[d,hru1R]
      have m:∀ u'∈aj 14 D br,(10:O)∈ag 14 D u'.1->1∈ag 14 D u'.1:=fun u' w' h10'=>(ay.1 (F (ay.2 ⟨w',h10'⟩))).2;have hE:=cy h l br k b (c 4 V) (s 10 V) m ⟨(ay.1 J).2,(ay.1 (F J)).2⟩ (by decide:(az 10).card=3/\ac 4 10=true/\ac 4 11=true/\(10:O)≠1/\(10:O)≠11/\ac 1 11=false);exact absurd (f 4 V 1 hE) V
     obtain⟨u0,hP⟩:=_c1.1 h2;have h3:u0∈aZ D br 10:=by{rw[d];exact(i▸_fs _ _:aZ D br 1⊆{u1,u2}) (by rw[hP];exact _mss _)};obtain⟨P1,Q1,hPQ1,hi,hk,hF⟩:=dV h l br Z hP h1_3;obtain⟨h10P1,h10Q1⟩:=hF 10 (ay.1 h3).2;have hG:P1∈af 14 D 10:=gD h.1 X (ak.1 hi).1 (cY h.1 hi) h10P1;have hH:Q1∈af 14 D 10:=gD h.1 X (ak.1 hk).1 (cY h.1 hk) h10Q1;have L:e100∈af 14 D 1:=by
      rcases B P1 hG with rfl|rfl|rfl|rfl;{exact absurd (f 4 V 1 (ak.1 hi).2.1) V};{exact absurd (f 5 V 1 (ak.1 hi).2.1) V}
      · rcases B Q1 hH with rfl|rfl|rfl|rfl
        · exact absurd (f 4 V 1 (ak.1 hk).2.1) V
        · exact absurd (f 5 V 1 (ak.1 hk).2.1) V
        · exact absurd rfl hPQ1
        · exact hk
      · exact hi
     have l2:(af 14 D 2).card<=2:=by
      by_contra hc;obtain⟨u,w⟩:=_cp.1 (by have:=bj h l br k 2;omega:0<(aZ D br 2).card);have hl:aZ D br 2⊆aZ D br 10:=by rw[d,<-i];exact _fs _ _
      have m:∀ u'∈aj 14 D br,(2:O)∈ag 14 D u'.1->10∈ag 14 D u'.1:=fun u' w' h2'=>(ay.1 (hl (ay.2 ⟨w',h2'⟩))).2;have I:=cV b (c 8 V) (cy h l br k b (c 8 V) (s 2 V) m ⟨(ay.1 w).2,(ay.1 (hl w)).2⟩ (by decide:(az 2).card=3/\ac 8 2=true/\ac 8 6=true/\(2:O)≠10/\(2:O)≠6/\ac 10 6=false));rcases B (pos 8) I with n|n|n|n;{exact absurd (b.2 _ (c 8 V) _ (c 4 V) n) V};{exact absurd (b.2 _ (c 8 V) _ (c 5 V) n) V};{exact absurd (b.2 _ (c 8 V) _ (c 7 V) n) V};{exact g 0 V (r 8 (c 8 V) n.symm▸c 8 V)}
     have l6:(af 14 D 6).card<=2:=by
      by_contra hc;obtain⟨u,w⟩:=_cp.1 (by have:=bj h l br k 6;omega:0<(aZ D br 6).card);have ho:aZ D br 6⊆aZ D br 10:=by rw[d,<-i];exact _fs _ _
      have m:∀ u'∈aj 14 D br,(6:O)∈ag 14 D u'.1->10∈ag 14 D u'.1:=fun u' w' h6'=>(ay.1 (ho (ay.2 ⟨w',h6'⟩))).2;have I:=cV b (c 8 V) (cy h l br k b (c 8 V) (s 6 V) m ⟨(ay.1 w).2,(ay.1 (ho w)).2⟩ (by decide:(az 6).card=3/\ac 8 6=true/\ac 8 2=true/\(6:O)≠10/\(6:O)≠2/\ac 10 2=false));rcases B (pos 8) I with n|n|n|n;{exact absurd (b.2 _ (c 8 V) _ (c 4 V) n) V};{exact absurd (b.2 _ (c 8 V) _ (c 5 V) n) V};{exact absurd (b.2 _ (c 8 V) _ (c 7 V) n) V};{exact g 0 V (r 8 (c 8 V) n.symm▸c 8 V)}
     have h9_3:3<=(af 14 D 9).card:=by{by_contra hc;exact dl h l b 6 9 11 8 5 (c 8 V) (c 5 V) (g 6 V) (g 9 V) (g 11 V) V l6 (by omega)};have h11_3:3<=(af 14 D 11).card:=by{by_contra hc;exact dl h l b 6 11 9 8 4 (c 8 V) (c 4 V) (g 6 V) (g 11 V) (g 9 V) V l6 (by omega)};have h12_3:3<=(af 14 D 12).card:=by{by_contra hc;exact dl h l b 2 12 13 8 5 (c 8 V) (c 5 V) (g 2 V) (g 12 V) (g 13 V) V l2 (by omega)};have hQ:(aZ D br 9).Nonempty:=_cp.1 (by have:=bj h l br k 9;omega);have P:(aZ D br 11).Nonempty:=_cp.1 (by have:=bj h l br k 11;omega);have hne12:(aZ D br 12).Nonempty:=_cp.1 (by have:=bj h l br k 12;omega);have q:∀(v t j:O),j∈({4,5}:o)->v∉({4,5,7,8}:o) ->((az v).card=3/\ac j v=true/\ac j 10=true/\v≠t/\v≠10/\bK t 10=false/\ac j t=false) ->(aZ D br v).Nonempty->aZ D br v⊆aZ D br t->False:=by{intro v t j hj hv hg hne hs;obtain⟨u,w⟩:=hne;have m:∀ u'∈aj 14 D br,v∈ag 14 D u'.1->t∈ag 14 D u'.1:=fun u' w' hv'=>(ay.1 (hs (ay.2 ⟨w',hv'⟩))).2;have H':∀ a∈({4,5}:o),a∈({4,5,7,8}:o):=V;have hC:j∈aa 14 D:=c j (H' j hj);exact aH.1 hg.2.2.2.2.2.2 (f j hj t (cy h l br k b hC (s v hv) m ⟨(ay.1 w).2,(ay.1 (hs w)).2⟩ ⟨hg.1,hg.2.1,hg.2.2.1,hg.2.2.2.1,hg.2.2.2.2.1,hg.2.2.2.2.2.1⟩))};have h4:¬ aZ D br 9⊆aZ D br 11:=q 9 11 5 V V V hQ;have h5:¬ aZ D br 11⊆aZ D br 9:=q 11 9 4 V V V P;have hno_12_11:¬ aZ D br 12⊆aZ D br 11:=q 12 11 5 V V V hne12;have hno_11_12:¬ aZ D br 11⊆aZ D br 12:=q 11 12 4 V V V P;have Q:∃ ua,aZ D br 9={ua}:=by{rcases dJ E (i▸_fs _ _) (i▸_fs _ _) hQ P h4 h5 with ⟨h9,_⟩|⟨h9,_⟩;{exact⟨u1,h9⟩};{exact⟨u2,h9⟩}};obtain⟨ua,hr⟩:=Q;have h6:ua∈aZ D br 10:=by{rw[d];exact(i▸_fs _ _:aZ D br 9⊆{u1,u2}) (by rw[hr];exact _mss _)};obtain⟨P9,Q9,hPQ9,hw,hx,hJ⟩:=dV h l br Z hr h9_3;obtain⟨h10P9,h10Q9⟩:=hJ 10 (ay.1 h6).2;have hK:P9∈af 14 D 10:=gD h.1 X (ak.1 hw).1 (cY h.1 hw) h10P9;have hL:Q9∈af 14 D 10:=gD h.1 X (ak.1 hx).1 (cY h.1 hx) h10Q9;obtain⟨Z6,-,hW6,hp6⟩:=cm h l b (c 8 V) (by decide:aP 8 6) V l6;obtain⟨e96,h96_9,hy,hz,hf96'⟩:=bf h l b (by decide:aP 9 6);obtain⟨e91,h91_9,hA,hB,-⟩:=bf h l b (by decide:aP 9 1);rw[hW6,_mi,_ms] at hy;have hR:am e96=Z6:=hy.resolve_left (fun n=>g 9 V (hf96' 8 (c 8 V) n▸c 8 V));have hp5_9:=aJ b (c 5 V) (by decide:aP 5 9);have h9le3:(af 14 D 9).card<=3:=by have:=bj h l br k 9;rw[hr,_cs] at this;omega
     have hM:pos 5≠e96:=fun n=>g 6 V (hz 5 (c 5 V) n.symm▸c 5 V);have hN:pos 5≠e91:=fun n=>g 1 V (hB 5 (c 5 V) n.symm▸c 5 V);have hO:e96≠e91:=fun n=>hp6 1 V V (by rw[<- hR,n];exact hA);have hW9:=aT hp5_9 h96_9 h91_9 hM hN hO h9le3;have C:pos 7∉af 14 D 9:=fun hm7=>by{rcases hW9 (pos 7) hm7 with n|n|n;{exact absurd (b.2 _ (c 7 V) _ (c 5 V) n) V};{exact g 6 V (hz 7 (c 7 V) n.symm▸c 7 V)};{exact g 1 V (hB 7 (c 7 V) n.symm▸c 7 V)}};have M:e100∈af 14 D 9:=by
      rcases B P9 hK with rfl|rfl|rfl|rfl;{exact absurd (f 4 V 9 (ak.1 hw).2.1) V}
      · rcases B Q9 hL with rfl|rfl|rfl|rfl
        · exact absurd (f 4 V 9 (ak.1 hx).2.1) V
        · exact absurd rfl hPQ9
        · exact absurd hx C
        · exact hx
      · exact absurd hw C
      · exact hw
     rcases hW9 e100 M with n|n|n;{exact h5e n.symm};{exact hp6 0 V V (by rw[<- hR,<-n];exact W)};{exact el h.1 L (n▸hA)}
 · have R:aZ D br 10={u1}:=by
    refine Subset.antisymm (fun u w=>?_) (singleton_subset_iff.2 J);have c':=y w;simp only[_mi,_ms] at c';rcases c' with rfl|rfl;{exact _mss _};{exact absurd w h8}
   exact fb h l h7 br Z b i R (c 4 V) (c 5 V) (c 7 V) (g 1 V) (g 2 V) (g 3 V) (g 6 V) (g 9 V) (g 11 V) (g 12 V) (g 13 V)
 · have R:aZ D br 10={u2}:=by
    refine Subset.antisymm (fun u w=>?_) (singleton_subset_iff.2 h8);have c':=y w;simp only[_mi,_ms] at c';rcases c' with rfl|rfl;{exact absurd w J};{exact _mss _}
   exact fb h l h7 br Z b (by rw[i,pair_comm]) R (c 4 V) (c 5 V) (c 7 V) (g 1 V) (g 2 V) (g 3 V) (g 6 V) (g 9 V) (g 11 V) (g 12 V) (g 13 V)
 · obtain⟨u,w⟩:=hne10
   have c':=y w;simp only[_mi,_ms] at c';rcases c' with rfl|rfl;{exact absurd w J};{exact absurd w h8}
def b9 (v:O):O:=if v=2\/v=6 then 8 else if v=4\/v=5 then 10 else if v=9\/v=13 then 1 else 3
lemma o5:∀ v t:O,v∈_E8 ->t∈_E8 ->b9 v≠b9 t ->∃ q:O,b9 v∈({1,3,8,10}:o)/\v∉({1,3,8,10}:o) /\(az v).card=3/\ac (b9 v) v=true/\ac (b9 v) q=true /\v≠t/\v≠q/\bK t q=false:=by
 decide +kernel
lemma nI:∀ v t:O,v∈_E8 ->t∈_E8 ->b9 v≠b9 t ->∃ y:O,b9 v∈({1,3,8,10}:o)/\b9 t∈({1,3,8,10}:o) /\y∉({1,3,8,10}:o)/\ac (b9 t) t=true/\ac t y=true/\ac (b9 t) v=false:=by
 decide +kernel
lemma jD:∀ v:O,v∈_E8 ->b9 v∈({1,3,8,10}:o)/\ac (b9 v) v=true /\∃ y:O,y∉({1,3,8,10}:o)/\ac v y=true:=by
 decide +kernel
lemma sf {D:Dag} (h:ai 14 D) (z:ar D) (h12:ap 14 D<=12) (hI:aa 14 D=bU ⟨51,V⟩):False:=by
 have hel:=aV 14 D;have hIeq:aa 14 D={1,3,8,10}:=by rw[hI];decide
 rw[hIeq,show({1,3,8,10}:o).card=4 from by decide] at hel;by_cases h0:bd 14 D<=(al 14 D).card;{exact dn h z h0 ⟨51,V⟩ hI};by_cases h1:bd 14 D=(al 14 D).card+1;{exact dp h z h12 h1 ⟨51,V⟩ V hI};have hts:=bg 14 D;have hB0:bL 14 D=0:=by omega
 obtain⟨br,hbm⟩:=b_ bs h.1 (bF z);have E:=bD hbm;obtain⟨pos,d⟩:=bQ bs h (bF z);have hR2:(aj 14 D br).card=2:=by have:=bS h.1 br E;omega
 obtain⟨u1,u2,s,m⟩:=_ct2.1 hR2;have C:∀ v:O,v∈({1,3,8,10}:o)->v∈aa 14 D:=fun v hv=>hIeq▸hv;have w:∀ v:O,v∉({1,3,8,10}:o)->v∉aa 14 D:=fun v hv=>hIeq▸hv;have helig:∀ v:O,v∉({1,3,8,10}:o)->v∈al 14 D:=fun v hv=>by{by_contra hc;exact hv (hIeq▸aN.2 hc)};have hpe:∀(v t:O),v∈_E8 ->t∈_E8 ->b9 v≠b9 t->(aZ D br v).Nonempty->aZ D br v⊆aZ D br t ->pos (b9 v)∈af 14 D t:=by{intro v t hv ht hblk hne hs;obtain⟨u,hu⟩:=hne;have hres:∀ u'∈aj 14 D br,v∈ag 14 D u'.1->t∈ag 14 D u'.1:=fun u' hu' hv'=>(ay.1 (hs (ay.2 ⟨hu',hv'⟩))).2;obtain⟨q,hiI,hvI,hg⟩:=o5 v t hv ht hblk;exact cV d (C (b9 v) hiI) (cy h z br E d (C (b9 v) hiI) (helig v hvI) hres ⟨(ay.1 hu).2,(ay.1 (hs hu)).2⟩ hg)};have i:∀(v t:O),v∈_E8 ->t∈_E8 ->b9 v≠b9 t->(aZ D br v).Nonempty->aZ D br v⊆aZ D br t->(aZ D br t).card=1->False:=by
  intro v t hv ht hblk hnev hs ht1;have hcardv:(aZ D br v).card=1:=by{have h1:=_cp.2 hnev;have h2:=_cl hs;omega};have heq:aZ D br v=aZ D br t:=_eqc hs (by omega);have hpv_t:=hpe v t hv ht hblk hnev hs;have hpt_v:=hpe t v ht hv hblk.symm (by rw[<- heq];exact hnev) (by rw[heq]);obtain⟨y,hivI,hitI,hyI,gtt,gty,gniv⟩:=nI v t hv ht hblk;have hpt_t:=aJ d (C (b9 t) hitI) ((ae _ _).1 gtt);obtain⟨ey,hey,hbey,hfy,-⟩:=bf h z d ((ae _ _).1 gty);have hWt3:(af 14 D t).card<=3:=by have:=bj h z br E t;omega
  have hWt:=aT hpt_t hpv_t hey (fun e=>hblk.symm (d.2 _ (C _ hitI) _ (C _ hivI) e)) (fun e=>w y hyI (hfy _ (C _ hitI) e.symm▸C _ hitI)) (fun e=>w y hyI (hfy _ (C _ hivI) e.symm▸C _ hivI)) hWt3
  have hfull:=cT h z hB0 d (C (b9 t) hitI) ((ae _ _).1 gtt) (fun p hp hne1 hsub'=>by
   rcases hWt p hp with rfl|rfl|rfl;{exact hne1 rfl};{exact hblk (_ms.1 (hsub' (cd d (C _ hivI))))}
   · exact w y hyI (_ms.1 (hsub' (ak.1 hbey).2.1)▸C _ hitI))
  exact aH.1 gniv ((hfull v).1 (ak.1 hpt_v).2.1)
 have hno_R_all3:∀(t v1 v2 v3:O),t∈_E8 ->v1∈_E8 ->v2∈_E8 ->v3∈_E8 ->(b9 t≠b9 v1/\b9 t≠b9 v2/\b9 t≠b9 v3 /\b9 v1≠b9 v2/\b9 v1≠b9 v3/\b9 v2≠b9 v3) ->aZ D br t={u1,u2}->(aZ D br v1).Nonempty->(aZ D br v2).Nonempty->(aZ D br v3).Nonempty->False:=by
  intro t v1 v2 v3 ht hv1 hv2 hv3 F hrt hn1 hn2 hn3;have hsub:∀ v,aZ D br v⊆aZ D br t:=fun v=>by rw[hrt,<-m];exact _fs _ _
  have hp1:=hpe v1 t hv1 ht F.1.symm hn1 (hsub v1);have hp2:=hpe v2 t hv2 ht F.2.1.symm hn2 (hsub v2);have hp3:=hpe v3 t hv3 ht F.2.2.1.symm hn3 (hsub v3);obtain⟨hi0,gtt,y,hyI,gty⟩:=jD t ht;have hi1:=(jD v1 hv1).1;have hi2:=(jD v2 hv2).1;have hi3:=(jD v3 hv3).1;have hp0:=aJ d (C _ hi0) ((ae _ _).1 gtt);obtain⟨ey,hey,-,hfy,-⟩:=bf h z d ((ae _ _).1 gty);have h5:=mn hp0 hp1 hp2 hp3 hey (fun e=>F.1 (d.2 _ (C _ hi0) _ (C _ hi1) e)) (fun e=>F.2.1 (d.2 _ (C _ hi0) _ (C _ hi2) e)) (fun e=>F.2.2.1 (d.2 _ (C _ hi0) _ (C _ hi3) e)) (fun e=>w y hyI (hfy _ (C _ hi0) e.symm▸C _ hi0)) (fun e=>F.2.2.2.1 (d.2 _ (C _ hi1) _ (C _ hi2) e)) (fun e=>F.2.2.2.2.1 (d.2 _ (C _ hi1) _ (C _ hi3) e)) (fun e=>w y hyI (hfy _ (C _ hi1) e.symm▸C _ hi1)) (fun e=>F.2.2.2.2.2 (d.2 _ (C _ hi2) _ (C _ hi3) e)) (fun e=>w y hyI (hfy _ (C _ hi2) e.symm▸C _ hi2)) (fun e=>w y hyI (hfy _ (C _ hi3) e.symm▸C _ hi3));have hc4:=bj h z br E t;rw[hrt,_c2 s] at hc4;omega
 have hno_3sing:∀(v1 v2 v3:O),v1∈_E8 ->v2∈_E8 ->v3∈_E8 ->b9 v1≠b9 v2->b9 v1≠b9 v3->b9 v2≠b9 v3 ->(aZ D br v1).card=1->(aZ D br v2).card=1->(aZ D br v3).card=1->False:=by{intro v1 v2 v3 hv1 hv2 hv3 h12 h13 h23 c1 W c3;have h6:∀ v,(aZ D br v).card=1->aZ D br v={u1}\/aZ D br v={u2}:=fun v cv=>by{obtain⟨u,hu⟩:=_c1.1 cv;have huR:u∈({u1,u2}:Finset (Σ _:ℕ,ℕ)):=m▸(ay.1 (by rw[hu];exact _mss _)).1;simp only[_mi,_ms] at huR;rcases huR with rfl|rfl <;> simp[hu]};rcases h6 v1 c1 with h1|h1 <;> rcases h6 v2 W with h2|h2 <;> rcases h6 v3 c3 with h3|h3;{exact i v1 v2 hv1 hv2 h12 (by rw[h1];simp) (by rw[h1,h2]) W};{exact i v1 v2 hv1 hv2 h12 (by rw[h1];simp) (by rw[h1,h2]) W};{exact i v1 v3 hv1 hv3 h13 (by rw[h1];simp) (by rw[h1,h3]) c3};{exact i v2 v3 hv2 hv3 h23 (by rw[h2];simp) (by rw[h2,h3]) c3};{exact i v2 v3 hv2 hv3 h23 (by rw[h2];simp) (by rw[h2,h3]) c3};{exact i v1 v3 hv1 hv3 h13 (by rw[h1];simp) (by rw[h1,h3]) c3};{exact i v1 v2 hv1 hv2 h12 (by rw[h1];simp) (by rw[h1,h2]) W};{exact i v1 v2 hv1 hv2 h12 (by rw[h1];simp) (by rw[h1,h2]) W}};have n:∀(x1 x2 c1 W R a2 b1 b2 ix ic J ib:O),ix∈aa 14 D->ic∈aa 14 D->J∈aa 14 D->ib∈aa 14 D ->(x1∈_E8/\x2∈_E8 /\c1∈_E8/\W∈_E8 /\R∈_E8/\a2∈_E8 /\b1∈_E8/\b2∈_E8 /\b9 x1=ix/\b9 x2=ix/\b9 c1=ic/\b9 W=ic /\b9 R=J/\b9 a2=J/\b9 b1=ib/\b9 b2=ib) ->(ix≠ic/\ix≠J/\ix≠ib/\ic≠J/\ic≠ib/\J≠ib /\x1≠x2/\c1≠W/\R≠a2/\b1≠b2 /\x1∉({1,3,8,10}:o)/\x2∉({1,3,8,10}:o) /\c1∉({1,3,8,10}:o)/\W∉({1,3,8,10}:o) /\R∉({1,3,8,10}:o)/\a2∉({1,3,8,10}:o) /\b1∉({1,3,8,10}:o)/\b2∉({1,3,8,10}:o)) ->(ac ix x1=true/\ac ix x2=true/\ac ic c1=true/\ac ic W=true /\ac J R=true/\ac J a2=true/\ac ib b1=true/\ac ib b2=true /\ac x1 R=true/\ac x1 b1=true/\ac x2 a2=true/\ac x2 b2=true /\ac c1 R=true/\ac c1 b2=true/\ac W a2=true/\ac W b1=true) ->(ac J c1=false/\ac J W=false/\ac ib c1=false/\ac ib W=false /\ac ic R=false/\ac ic a2=false/\ac ic b1=false/\ac ic b2=false /\ac J b1=false/\ac J b2=false/\ac ib R=false/\ac ib a2=false /\(az x1).card=3/\(az x2).card=3/\(az c1).card=3/\(az W).card=3 /\(az R).card=3/\(az a2).card=3/\(az b1).card=3/\(az b2).card=3 /\decide (x1.val<7)=decide (x2.val<7)/\decide (x1.val<7)=decide (c1.val<7) /\decide (x1.val<7)=decide (W.val<7)/\decide (R.val<7)=decide (a2.val<7) /\decide (R.val<7)=decide (b1.val<7)/\decide (R.val<7)=decide (b2.val<7)) ->(af 14 D x1).card<=2->(af 14 D x2).card<=2->False:=by
  intro x1 x2 c1 W R a2 b1 b2 ix ic J ib I A k r hg1 hg2 hg3 hg4 lx1 lx2;obtain⟨hx1,hx2,hc1,hc2,ha1,ha2,Y,hb2,bx1,bx2,bc1,bc2,ba1,ba2,bb1,bb2⟩:=hg1;obtain⟨H,hxia,hxib,hcia,hcib,x,hx12,hc12,ha12,hb12,Z,hnx2,hnc1,hnc2,hna1,hna2,hnb1,hnb2⟩:=hg2;obtain⟨gx1,gx2,gc1,gc2,ga1,ga2,gb1,gb2,g11,g1b1,g22,g2b2,gc1a1,gc1b2,gc2a2,gc2b1⟩:=hg3;obtain⟨gniac1,gniac2,gnibc1,gnibc2,gnica1,gnica2,gnicb1,gnicb2,gniab1,gniab2,gniba1,gniba2,hdx1,hdx2,hdc1,hdc2,hda1,hda2,hdb1,hdb2,hsx12,S,T,hsa12,hsab1,hsab2⟩:=hg4;have ha1_3:3<=(af 14 D R).card:=by{by_contra hc;exact dl h z d x1 R b1 ix J I k (w _ Z) (w _ hna1) (w _ hnb1) ⟨gx1,ga1,g11,g1b1,by intro g;exact x (by rw[<- ba1,<-bb1,g]),hda1,hsab1.symm⟩ lx1 (by omega)};have hb1_3:3<=(af 14 D b1).card:=by{by_contra hc;exact dl h z d x1 b1 R ix ib I r (w _ Z) (w _ hnb1) (w _ hna1) ⟨gx1,gb1,g1b1,g11,by intro g;exact x (by rw[<- ba1,<-bb1,g]),hdb1,hsab1⟩ lx1 (by omega)};have ha2_3:3<=(af 14 D a2).card:=by{by_contra hc;exact dl h z d x2 a2 b2 ix J I k (w _ hnx2) (w _ hna2) (w _ hnb2) ⟨gx2,ga2,g22,g2b2,by intro g;exact x (by rw[<- ba2,<-bb2,g]),hda2,hsab2.symm.trans hsa12⟩ lx2 (by omega)};have hb2_3:3<=(af 14 D b2).card:=by{by_contra hc;exact dl h z d x2 b2 a2 ix ib I r (w _ hnx2) (w _ hnb2) (w _ hna2) ⟨gx2,gb2,g2b2,g22,by intro g;exact x (by rw[<- ba2,<-bb2,g]),hdb2,hsa12.symm.trans hsab2⟩ lx2 (by omega)};have hnea1:(aZ D br R).Nonempty:=_cp.1 (by have:=bj h z br E R;omega);have hnea2:(aZ D br a2).Nonempty:=_cp.1 (by have:=bj h z br E a2;omega);have hneb1:(aZ D br b1).Nonempty:=_cp.1 (by have:=bj h z br E b1;omega);have hneb2:(aZ D br b2).Nonempty:=_cp.1 (by have:=bj h z br E b2;omega);obtain⟨Zx1,-,hWx1,hpx1⟩:=cm h z d I ((ae _ _).1 gx1) hdx1 lx1;obtain⟨Zx2,-,hWx2,hpx2⟩:=cm h z d I ((ae _ _).1 gx2) hdx2 lx2;have hZx1_in:Zx1∈af 14 D x1:=by rw[hWx1];simp
  have hZx2_in:Zx2∈af 14 D x2:=by rw[hWx2];simp
  have hkill_c_both_le2:(af 14 D c1).card<=2->(af 14 D W).card<=2->False:=by
   intro lc1 lc2;obtain⟨Zc1,-,hWc1,hpc1⟩:=cm h z d A ((ae _ _).1 gc1) hdc1 lc1;obtain⟨Zc2,-,hWc2,hpc2⟩:=cm h z d A ((ae _ _).1 gc2) hdc2 lc2;have hZc1_in:Zc1∈af 14 D c1:=by rw[hWc1];simp
   have hZc2_in:Zc2∈af 14 D W:=by rw[hWc2];simp
   have hfull_of_card1:∀(p u1' u2' ip:O) (Zu1:ℕ×_d),ip∈aa 14 D->p∉({1,3,8,10}:o) ->u1'∉({1,3,8,10}:o)->u2'∉({1,3,8,10}:o) ->ac ip p=true->ac p u1'=true->ac p u2'=true ->af 14 D u1'={pos ix,Zu1} ->(∀ t,t≠u1'->decide (t.val<7)=decide (u1'.val<7)->Zu1∉af 14 D t) ->u1'≠u2'->decide (u2'.val<7)=decide (u1'.val<7) ->(aZ D br p).card=1->∀ t,t∈ag 14 D (aw D (pos ip))->aP ip t:=by
    intro p u1' u2' ip Zu1 N hpI hu1 hu2 gip gp1 gp2 hWu1 hpu1 s hsu12 cp1;obtain⟨ep1,hep1_p,hep1_u,hf1,hf1'⟩:=bf h z d ((ae _ _).1 gp1);obtain⟨ep2,hep2_p,hep2_u,hf2,-⟩:=bf h z d ((ae _ _).1 gp2);have hep1_u':=hep1_u;rw[hWu1,_mi,_ms] at hep1_u';have hbp1:am ep1=Zu1:=hep1_u'.resolve_left (fun g=>w p hpI (hf1' ix I g▸I));have hWp3:(af 14 D p).card<=3:=by have:=bj h z br E p;omega
    have hWp:=aT (aJ d N ((ae _ _).1 gip)) hep1_p hep2_p (fun g=>w u1' hu1 (hf1 ip N g.symm▸N)) (fun g=>w u2' hu2 (hf2 ip N g.symm▸N)) (fun g=>hpu1 u2' s.symm hsu12 (by rw[<- hbp1,g];exact hep2_u)) hWp3
    have hf:=cT h z hB0 d N ((ae _ _).1 gip) (fun e he G hsub'=>by
     rcases hWp e he with rfl|rfl|rfl;{exact G rfl};{exact w u1' hu1 (_ms.1 (hsub' (ak.1 hep1_u).2.1)▸N)}
     · exact w u2' hu2 (_ms.1 (hsub' (ak.1 hep2_u).2.1)▸N))
    exact fun t ht=>(hf t).1 ht
   have K:∀(p q ux uc vx vc ip iq:O) (Zux Zvx:ℕ×_d),ip∈aa 14 D->iq∈aa 14 D ->p∈_E8->q∈_E8 ->p∉({1,3,8,10}:o)->q∉({1,3,8,10}:o) ->ux∉({1,3,8,10}:o)->uc∉({1,3,8,10}:o) ->vx∉({1,3,8,10}:o)->vc∉({1,3,8,10}:o) ->b9 p=ip->b9 q=iq->ip≠iq ->ac ip p=true->ac p ux=true->ac p uc=true->ac ip q=false ->ac iq q=true->ac q vx=true->ac q vc=true->ac iq p=false ->af 14 D ux={pos ix,Zux}->(∀ t,t≠ux->decide (t.val<7)=decide (ux.val<7)->Zux∉af 14 D t) ->ux≠uc->decide (uc.val<7)=decide (ux.val<7) ->af 14 D vx={pos ix,Zvx}->(∀ t,t≠vx->decide (t.val<7)=decide (vx.val<7)->Zvx∉af 14 D t) ->vx≠vc->decide (vc.val<7)=decide (vx.val<7) ->(aZ D br p).Nonempty->(aZ D br q).Nonempty->(aZ D br p).card=1:=by
    intro p q ux uc vx vc ip iq Zux Zvx N hiq hp hq hpI hqI hux huc hvx hvc bp bq hipq gip gp1 gp2 gnipq giq gq1 gq2 gniqp hWux hpux huxc hsuxc hWvx hpvx hvxc hsvxc hnp hnq;have hple2:(aZ D br p).card<=2:=by{have:=_cl (m▸_fs _ _:aZ D br p⊆{u1,u2});rw[_c2 s] at this;exact this};have hqle2:(aZ D br q).card<=2:=by{have:=_cl (m▸_fs _ _:aZ D br q⊆{u1,u2});rw[_c2 s] at this;exact this};have hposp:0<(aZ D br p).card:=_cp.2 hnp;have hposq:0<(aZ D br q).card:=_cp.2 hnq;by_contra hne1;have hpR:aZ D br p={u1,u2}:=_eqc (m▸_fs _ _) (by rw[_c2 s];omega);have hsub_qp:aZ D br q⊆aZ D br p:=by rw[hpR,<-m];exact _fs _ _
    have hpq_p:=hpe q p hq hp (by rw[bp,bq];exact hipq.symm) hnq hsub_qp;by_cases hq1:(aZ D br q).card=1
    · have hfq:=hfull_of_card1 q vx vc iq Zvx hiq hqI hvx hvc giq gq1 gq2 hWvx hpvx hvxc hsvxc hq1
      exact aH.1 gniqp (hfq p (bq▸(ak.1 hpq_p).2.1))
    · have hqR:aZ D br q={u1,u2}:=_eqc (m▸_fs _ _) (by rw[_c2 s];omega)
      have hpp_q:=hpe p q hp hq (by rw[bp,bq];exact hipq) hnp (by rw[hqR,<-m];exact _fs _ _);obtain⟨ep1,hep1_p,hep1_u,hf1,hf1'⟩:=bf h z d ((ae _ _).1 gp1);obtain⟨ep2,hep2_p,hep2_u,hf2,-⟩:=bf h z d ((ae _ _).1 gp2);have hep1_u':=hep1_u;rw[hWux,_mi,_ms] at hep1_u';have hbp1:am ep1=Zux:=hep1_u'.resolve_left (fun g=>w p hpI (hf1' ix I g▸I));have hWp4:(af 14 D p).card<=4:=by have:=bj h z br E p;rw[hpR,_c2 s] at this;omega
      have hWp:=gh (aJ d N ((ae _ _).1 gip)) (bq▸hpq_p) hep1_p hep2_p (fun g=>hipq (d.2 _ N _ hiq g)) (fun g=>w ux hux (hf1 ip N g.symm▸N)) (fun g=>w uc huc (hf2 ip N g.symm▸N)) (fun g=>w ux hux (hf1 iq hiq g.symm▸hiq)) (fun g=>w uc huc (hf2 iq hiq g.symm▸hiq)) (fun g=>hpux uc huxc.symm hsuxc (by rw[<- hbp1,g];exact hep2_u)) hWp4
      have hfp:=cT h z hB0 d N ((ae _ _).1 gip) (fun e he G hsub'=>by
       rcases hWp e he with rfl|rfl|rfl|rfl;{exact G rfl};{exact hipq.symm (_ms.1 (hsub' (cd d hiq)))};{exact w ux hux (_ms.1 (hsub' (ak.1 hep1_u).2.1)▸N)}
       · exact w uc huc (_ms.1 (hsub' (ak.1 hep2_u).2.1)▸N))
      exact aH.1 gnipq ((hfp q).1 (bp▸(ak.1 hpp_q).2.1))
   have ha1_1:(aZ D br R).card=1:=K R b1 x1 c1 x1 W J ib Zx1 Zx1 k r ha1 Y hna1 hnb1 Z hnc1 Z hnc2 ba1 bb1 x ga1 ((ae _ _).2 (bm ((ae _ _).1 g11))) ((ae _ _).2 (bm ((ae _ _).1 gc1a1))) gniab1 gb1 ((ae _ _).2 (bm ((ae _ _).1 g1b1))) ((ae _ _).2 (bm ((ae _ _).1 gc2b1))) gniba1 hWx1 hpx1 (fun g=>H (by rw[<- bx1,<-bc1,g])) S.symm hWx1 hpx1 (fun g=>H (by rw[<- bx1,<-bc2,g])) T.symm hnea1 hneb1;have ha2_1:(aZ D br a2).card=1:=K a2 b2 x2 W x2 c1 J ib Zx2 Zx2 k r ha2 hb2 hna2 hnb2 hnx2 hnc2 hnx2 hnc1 ba2 bb2 x ga2 ((ae _ _).2 (bm ((ae _ _).1 g22))) ((ae _ _).2 (bm ((ae _ _).1 gc2a2))) gniab2 gb2 ((ae _ _).2 (bm ((ae _ _).1 g2b2))) ((ae _ _).2 (bm ((ae _ _).1 gc1b2))) gniba2 hWx2 hpx2 (fun g=>H (by rw[<- bx2,<-bc2,g])) (T.symm.trans hsx12) hWx2 hpx2 (fun g=>H (by rw[<- bx2,<-bc1,g])) (S.symm.trans hsx12) hnea2 hneb2;have hb1_1:(aZ D br b1).card=1:=K b1 R x1 W x1 c1 ib J Zx1 Zx1 r k Y ha1 hnb1 hna1 Z hnc2 Z hnc1 bb1 ba1 x.symm gb1 ((ae _ _).2 (bm ((ae _ _).1 g1b1))) ((ae _ _).2 (bm ((ae _ _).1 gc2b1))) gniba1 ga1 ((ae _ _).2 (bm ((ae _ _).1 g11))) ((ae _ _).2 (bm ((ae _ _).1 gc1a1))) gniab1 hWx1 hpx1 (fun g=>H (by rw[<- bx1,<-bc2,g])) T.symm hWx1 hpx1 (fun g=>H (by rw[<- bx1,<-bc1,g])) S.symm hneb1 hnea1;have hsame_a:∃ ua,aZ D br R={ua}/\aZ D br a2={ua}:=by{have h6:∀ v,(aZ D br v).card=1->aZ D br v={u1}\/aZ D br v={u2}:=fun v cv=>by{obtain⟨u,hu⟩:=_c1.1 cv;have huR:u∈({u1,u2}:Finset (Σ _:ℕ,ℕ)):=m▸(ay.1 (by rw[hu];exact _mss _)).1;simp only[_mi,_ms] at huR;rcases huR with rfl|rfl <;> simp[hu]};rcases h6 R ha1_1 with h1|h1 <;> rcases h6 a2 ha2_1 with h2|h2 <;> rcases h6 b1 hb1_1 with h3|h3;{exact absurd (by rw[h1,h3]) (fun hs=>i R b1 ha1 Y (by rw[ba1,bb1];exact x) hnea1 hs hb1_1)};{exact⟨u1,h1,h2⟩};{exact absurd (by rw[h1,h3]) (fun hs=>i R b1 ha1 Y (by rw[ba1,bb1];exact x) hnea1 hs hb1_1)};{exact absurd (by rw[h2,h3]) (fun hs=>i a2 b1 ha2 Y (by rw[ba2,bb1];exact x) hnea2 hs hb1_1)};{exact absurd (by rw[h2,h3]) (fun hs=>i a2 b1 ha2 Y (by rw[ba2,bb1];exact x) hnea2 hs hb1_1)};{exact absurd (by rw[h1,h3]) (fun hs=>i R b1 ha1 Y (by rw[ba1,bb1];exact x) hnea1 hs hb1_1)};{exact⟨u2,h1,h2⟩};{exact absurd (by rw[h1,h3]) (fun hs=>i R b1 ha1 Y (by rw[ba1,bb1];exact x) hnea1 hs hb1_1)}};obtain⟨ua,hrua1,hrua2⟩:=hsame_a;obtain⟨P,Q,hPQ,hall⟩:=fz h z br hbm hrua1 ha1_3;have ha1ua:R∈ag 14 D ua.1:=(ay.1 (by rw[hrua1];exact _mss _)).2;have ha2ua:a2∈ag 14 D ua.1:=(ay.1 (by rw[hrua2];exact _mss _)).2;obtain⟨hPa1,hQa1⟩:=hall R ha1ua hrua1 ha1_3;obtain⟨hPa2,hQa2⟩:=hall a2 ha2ua hrua2 ha2_3;obtain⟨e1x,h1x_a,h1x_x,hf1x,hf1x'⟩:=bf h z d (bm ((ae _ _).1 g11));obtain⟨e1c,h1c_a,h1c_c,hf1c,hf1c'⟩:=bf h z d (bm ((ae _ _).1 gc1a1));obtain⟨e2x,h2x_a,h2x_x,hf2x,hf2x'⟩:=bf h z d (bm ((ae _ _).1 g22));obtain⟨e2c,h2c_a,h2c_c,hf2c,hf2c'⟩:=bf h z d (bm ((ae _ _).1 gc2a2));rw[hWx1,_mi,_ms] at h1x_x;have hb1x:am e1x=Zx1:=h1x_x.resolve_left (fun g=>w R hna1 (hf1x' ix I g▸I));rw[hWc1,_mi,_ms] at h1c_c;have hb1c:am e1c=Zc1:=h1c_c.resolve_left (fun g=>w R hna1 (hf1c' ic A g▸A));rw[hWx2,_mi,_ms] at h2x_x;have hb2x:am e2x=Zx2:=h2x_x.resolve_left (fun g=>w a2 hna2 (hf2x' ix I g▸I));rw[hWc2,_mi,_ms] at h2c_c;have hb2c:am e2c=Zc2:=h2c_c.resolve_left (fun g=>w a2 hna2 (hf2c' ic A g▸A));have ha1le3:(af 14 D R).card<=3:=by have:=bj h z br E R;omega
   have ha2le3:(af 14 D a2).card<=3:=by have:=bj h z br E a2;omega
   have hWa1:=aT (aJ d k ((ae _ _).1 ga1)) h1x_a h1c_a (fun g=>w x1 Z (hf1x J k g.symm▸k)) (fun g=>w c1 hnc1 (hf1c J k g.symm▸k)) (fun g=>hpx1 c1 (fun e=>H (by rw[<- bx1,<-bc1,e])) S.symm (by rw[<- hb1x,g,hb1c];exact hZc1_in)) ha1le3;have hWa2:=aT (aJ d k ((ae _ _).1 ga2)) h2x_a h2c_a (fun g=>w x2 hnx2 (hf2x J k g.symm▸k)) (fun g=>w W hnc2 (hf2c J k g.symm▸k)) (fun g=>hpx2 W (fun e=>H (by rw[<- bx2,<-bc2,e])) (T.symm.trans hsx12) (by rw[<- hb2x,g,hb2c];exact hZc2_in)) ha2le3;have hkill_e:∀ e,e∈af 14 D R->e∈af 14 D a2->e=pos J:=by
    intro e he1 he2;rcases hWa1 e he1 with heq|heq|heq;{exact heq}
    · rw[heq] at he2
      rcases hWa2 e1x he2 with g|g|g;{exact absurd g.symm (fun g'=>w x1 Z (hf1x J k g'.symm▸k))};{exact absurd (by rw[<- hb1x,g,hb2x];exact hZx2_in) (hpx1 x2 hx12.symm hsx12.symm)};{exact absurd (by rw[<- hb1x,g,hb2c];exact hZc2_in) (hpx1 W (fun g'=>H (by rw[<- bx1,<-bc2,g'])) T.symm)}
    · rw[heq] at he2
      rcases hWa2 e1c he2 with g|g|g;{exact absurd g.symm (fun g'=>w c1 hnc1 (hf1c J k g'.symm▸k))};{exact absurd (by rw[<- hb1c,g,hb2x];exact hZx2_in) (hpc1 x2 (fun g'=>H (by rw[<- bx2,<-bc1,g'])) (hsx12.symm.trans S))};{exact absurd (by rw[<- hb1c,g,hb2c];exact hZc2_in) (hpc1 W hc12.symm (T.symm.trans S))}
   exact hPQ ((hkill_e P hPa1 hPa2).trans (hkill_e Q hQa1 hQa2).symm)
  have hkill_c_pos:∀(c f j B xa xb:O) (Zxa Zxb:ℕ×_d),c∈_E8 ->f∈_E8 ->j∈_E8 ->c∉({1,3,8,10}:o)->f∉({1,3,8,10}:o) ->j∉({1,3,8,10}:o)->B∉({1,3,8,10}:o) ->xa∉({1,3,8,10}:o)->xb∉({1,3,8,10}:o) ->b9 c=ic->b9 f=J->b9 j=ib ->ac ic c=true->ac J f=true->ac ib j=true ->ac c f=true->ac f xa=true->ac j xb=true->ac j B=true ->ac ic f=false->ac ic j=false->ac J j=false->ac ib f=false ->af 14 D xa={pos ix,Zxa}->(∀ t,t≠xa->decide (t.val<7)=decide (xa.val<7)->Zxa∉af 14 D t) ->xa≠c->decide (c.val<7)=decide (xa.val<7) ->af 14 D xb={pos ix,Zxb}->(∀ t,t≠xb->decide (t.val<7)=decide (xb.val<7)->Zxb∉af 14 D t) ->xb≠B->decide (B.val<7)=decide (xb.val<7) ->(aZ D br c).Nonempty->(aZ D br f).Nonempty->(aZ D br j).Nonempty ->3<=(af 14 D f).card->False:=by
   intro c f j B xa xb Zxa Zxb hc_m ha_m hb_m hcI haI hbI hcoI h4 hxbI bc ba bb gic gia gib gca gaxa gbxb gbco gnica gnicb gniab gniba hWxa hpxa hxac hsxac hWxb hpxb hxbco hsxbco hnc hna hnb ha3;have hno_R_a:aZ D br f≠{u1,u2}:=by
    intro haR;have hpb_a:=hpe j f hb_m ha_m (by rw[ba,bb];exact x.symm) hnb (by rw[haR,<-m];exact _fs _ _);have hpc_a:=hpe c f hc_m ha_m (by rw[ba,bc];exact hcia) hnc (by rw[haR,<-m];exact _fs _ _);obtain⟨eax,X,M,hfx,-⟩:=bf h z d ((ae _ _).1 gaxa);have hWa4:(af 14 D f).card<=4:=by have:=bj h z br E f;rw[haR,_c2 s] at this;omega
    have hWa:=gh (aJ d k ((ae _ _).1 gia)) (bb▸hpb_a) (bc▸hpc_a) X (fun g=>x (d.2 _ k _ r g)) (fun g=>hcia.symm (d.2 _ k _ A g)) (fun g=>w xa h4 (hfx J k g.symm▸k)) (fun g=>hcib.symm (d.2 _ r _ A g)) (fun g=>w xa h4 (hfx ib r g.symm▸r)) (fun g=>w xa h4 (hfx ic A g.symm▸A)) hWa4
    have hfa:=cT h z hB0 d k ((ae _ _).1 gia) (fun e he G hsub'=>by
     rcases hWa e he with rfl|rfl|rfl|rfl;{exact G rfl};{exact x.symm (_ms.1 (hsub' (cd d r)))};{exact hcia (_ms.1 (hsub' (cd d A)))}
     · exact w xa h4 (_ms.1 (hsub' (ak.1 M).2.1)▸k))
    have Y:(aZ D br j).card=1:=by{have hble2:(aZ D br j).card<=2:=by{have:=_cl (m▸_fs _ _:aZ D br j⊆{u1,u2});rw[_c2 s] at this;exact this};have hposb:0<(aZ D br j).card:=_cp.2 hnb;by_contra hne1;have hbR:aZ D br j={u1,u2}:=_eqc (m▸_fs _ _) (by rw[_c2 s];omega);have hpa_b:=hpe f j ha_m hb_m (by rw[ba,bb];exact x) hna (by rw[hbR,<-m];exact _fs _ _);exact aH.1 gniab ((hfa j).1 (ba▸(ak.1 hpa_b).2.1))};obtain⟨ebx,hebx_b,hebx_x,hfxb,hfxb'⟩:=bf h z d ((ae _ _).1 gbxb);obtain⟨ebc,hebc_b,hebc_c,hfcb,-⟩:=bf h z d ((ae _ _).1 gbco);have hebx_x':=hebx_x;rw[hWxb,_mi,_ms] at hebx_x';have hbbx:am ebx=Zxb:=hebx_x'.resolve_left (fun g=>w j hbI (hfxb' ix I g▸I));have hWb3:(af 14 D j).card<=3:=by have:=bj h z br E j;omega
    have hWb:=aT (aJ d r ((ae _ _).1 gib)) hebx_b hebc_b (fun g=>w xb hxbI (hfxb ib r g.symm▸r)) (fun g=>w B hcoI (hfcb ib r g.symm▸r)) (fun g=>hpxb B hxbco.symm hsxbco (by rw[<- hbbx,g];exact hebc_c)) hWb3
    have hfb:=cT h z hB0 d r ((ae _ _).1 gib) (fun e he G hsub'=>by
     rcases hWb e he with rfl|rfl|rfl;{exact G rfl};{exact w xb hxbI (_ms.1 (hsub' (ak.1 hebx_x).2.1)▸r)}
     · exact w B hcoI (_ms.1 (hsub' (ak.1 hebc_c).2.1)▸r))
    exact aH.1 gniba ((hfb f).1 (bb▸(ak.1 hpb_a).2.1))
   have hno_R_b:aZ D br j≠{u1,u2}:=by
    intro hbR;have hpa_b:=hpe f j ha_m hb_m (by rw[ba,bb];exact x) hna (by rw[hbR,<-m];exact _fs _ _);have hpc_b:=hpe c j hc_m hb_m (by rw[bb,bc];exact hcib) hnc (by rw[hbR,<-m];exact _fs _ _);obtain⟨ebx,hebx_b,hebx_x,hfxb,-⟩:=bf h z d ((ae _ _).1 gbxb);have hWb4:(af 14 D j).card<=4:=by have:=bj h z br E j;rw[hbR,_c2 s] at this;omega
    have hWb:=gh (aJ d r ((ae _ _).1 gib)) (ba▸hpa_b) (bc▸hpc_b) hebx_b (fun g=>x.symm (d.2 _ r _ k g)) (fun g=>hcib.symm (d.2 _ r _ A g)) (fun g=>w xb hxbI (hfxb ib r g.symm▸r)) (fun g=>hcia.symm (d.2 _ k _ A g)) (fun g=>w xb hxbI (hfxb J k g.symm▸k)) (fun g=>w xb hxbI (hfxb ic A g.symm▸A)) hWb4
    have hfb:=cT h z hB0 d r ((ae _ _).1 gib) (fun e he G hsub'=>by
     rcases hWb e he with rfl|rfl|rfl|rfl;{exact G rfl};{exact x (_ms.1 (hsub' (cd d k)))};{exact hcib (_ms.1 (hsub' (cd d A)))}
     · exact w xb hxbI (_ms.1 (hsub' (ak.1 hebx_x).2.1)▸r))
    have ha1':(aZ D br f).card=1:=by{have hale2:(aZ D br f).card<=2:=by{have:=_cl (m▸_fs _ _:aZ D br f⊆{u1,u2});rw[_c2 s] at this;exact this};have hposa:0<(aZ D br f).card:=_cp.2 hna;by_contra hne1;exact hno_R_a (_eqc (m▸_fs _ _) (by rw[_c2 s];omega))};obtain⟨eax,X,M,hfxa,hfxa'⟩:=bf h z d ((ae _ _).1 gaxa);obtain⟨eac,heac_a,heac_c,hfca,-⟩:=bf h z d (bm ((ae _ _).1 gca));have M':=M;rw[hWxa,_mi,_ms] at M';have hbax:am eax=Zxa:=M'.resolve_left (fun g=>w f haI (hfxa' ix I g▸I));have hWa3:(af 14 D f).card<=3:=by have:=bj h z br E f;omega
    have hWa:=aT (aJ d k ((ae _ _).1 gia)) X heac_a (fun g=>w xa h4 (hfxa J k g.symm▸k)) (fun g=>w c hcI (hfca J k g.symm▸k)) (fun g=>hpxa c hxac.symm hsxac (by rw[<- hbax,g];exact heac_c)) hWa3
    have hfa:=cT h z hB0 d k ((ae _ _).1 gia) (fun e he G hsub'=>by
     rcases hWa e he with rfl|rfl|rfl;{exact G rfl};{exact w xa h4 (_ms.1 (hsub' (ak.1 M).2.1)▸k)}
     · exact w c hcI (_ms.1 (hsub' (ak.1 heac_c).2.1)▸k))
    exact aH.1 gniab ((hfa j).1 (ba▸(ak.1 hpa_b).2.1))
   have ha1':(aZ D br f).card=1:=by{have hale2:(aZ D br f).card<=2:=by{have:=_cl (m▸_fs _ _:aZ D br f⊆{u1,u2});rw[_c2 s] at this;exact this};have hposa:0<(aZ D br f).card:=_cp.2 hna;by_contra hne1;exact hno_R_a (_eqc (m▸_fs _ _) (by rw[_c2 s];omega))};have Y':(aZ D br j).card=1:=by{have hble2:(aZ D br j).card<=2:=by{have:=_cl (m▸_fs _ _:aZ D br j⊆{u1,u2});rw[_c2 s] at this;exact this};have hposb:0<(aZ D br j).card:=_cp.2 hnb;by_contra hne1;exact hno_R_b (_eqc (m▸_fs _ _) (by rw[_c2 s];omega))};have hcR:aZ D br c={u1,u2}:=by{have hcle2:(aZ D br c).card<=2:=by{have:=_cl (m▸_fs _ _:aZ D br c⊆{u1,u2});rw[_c2 s] at this;exact this};have hposc:0<(aZ D br c).card:=_cp.2 hnc;by_contra hneR;have hc1':(aZ D br c).card=1:=by{by_contra hne1;exact hneR (_eqc (m▸_fs _ _) (by rw[_c2 s];omega))};exact hno_3sing f j c ha_m hb_m hc_m (by rw[ba,bb];exact x) (by rw[ba,bc];exact hcia.symm) (by rw[bb,bc];exact hcib.symm) ha1' Y' hc1'};have hpa_c:=hpe f c ha_m hc_m (by rw[ba,bc];exact hcia.symm) hna (by rw[hcR,<-m];exact _fs _ _);have hpb_c:=hpe j c hb_m hc_m (by rw[bb,bc];exact hcib.symm) hnb (by rw[hcR,<-m];exact _fs _ _);obtain⟨eca,heca_c,heca_a,hfa_c,hfc_a⟩:=bf h z d ((ae _ _).1 gca);obtain⟨eax,X,M,hfx_a,hfa_x⟩:=bf h z d ((ae _ _).1 gaxa);rw[hWxa,_mi,_ms] at M;have hbax:am eax=Zxa:=M.resolve_left (fun g=>w f haI (hfa_x ix I g▸I));have hWc4:(af 14 D c).card<=4:=by have:=bj h z br E c;rw[hcR,_c2 s] at this;omega
   have hWc_card4:4<=(af 14 D c).card:=mm (aJ d A ((ae _ _).1 gic)) (ba▸hpa_c) (bb▸hpb_c) heca_c (fun g=>hcia (d.2 _ A _ k g)) (fun g=>hcib (d.2 _ A _ r g)) (fun g=>w f haI (hfa_c ic A g.symm▸A)) (fun g=>x (d.2 _ k _ r g)) (fun g=>w f haI (hfa_c J k g.symm▸k)) (fun g=>w f haI (hfa_c ib r g.symm▸r));have hMc:aW 14 D (ao 14 D {c})=∅:=by{have hcc:=bj h z br E c;rw[hcR,_c2 s] at hcc;exact card_eq_zero.1 (by omega)};have hWc:=gh (aJ d A ((ae _ _).1 gic)) (ba▸hpa_c) (bb▸hpb_c) heca_c (fun g=>hcia (d.2 _ A _ k g)) (fun g=>hcib (d.2 _ A _ r g)) (fun g=>w f haI (hfa_c ic A g.symm▸A)) (fun g=>x (d.2 _ k _ r g)) (fun g=>w f haI (hfa_c J k g.symm▸k)) (fun g=>w f haI (hfa_c ib r g.symm▸r)) hWc4;have hWa3:(af 14 D f).card<=3:=by have:=bj h z br E f;omega
   have hWa:=aT (aJ d k ((ae _ _).1 gia)) X heca_a (fun g=>w xa h4 (hfx_a J k g.symm▸k)) (fun g=>w c hcI (hfc_a J k g.symm▸k)) (fun g=>hpxa c hxac.symm hsxac (by rw[<- hbax,g,aB];exact heca_c)) hWa3;obtain⟨ua,hrua⟩:=_c1.1 ha1';have hua_inc:ua∈aZ D br c:=by{rw[hcR];exact(m▸_fs _ _:aZ D br f⊆{u1,u2}) (by rw[hrua];exact _mss _)};obtain⟨P,Q,hPQ,hPa,hQa,hsupp⟩:=dV h z br hbm hrua ha3;obtain⟨hcP,hcQ⟩:=hsupp c (ay.1 hua_inc).2;have hPc:P∈af 14 D c:=gD h.1 hMc (ak.1 hPa).1 (cY h.1 hPa) hcP;have hQc:Q∈af 14 D c:=gD h.1 hMc (ak.1 hQa).1 (cY h.1 hQa) hcQ;have hkill_ac:∀ e,e∈af 14 D f->e∈af 14 D c->e=pos J:=by
    intro e hea hec;rcases hWa e hea with heq|heq|heq;{exact heq}
    · rw[heq] at hec
      rcases hWc eax hec with g|g|g|g;{exact absurd g.symm (fun g'=>w xa h4 (hfx_a ic A g'.symm▸A))};{exact absurd g.symm (fun g'=>w xa h4 (hfx_a J k g'.symm▸k))};{exact absurd g.symm (fun g'=>w xa h4 (hfx_a ib r g'.symm▸r))};{exact absurd (g▸heca_a) (el h.1 X)}
    · rw[heq] at hec
      rcases hWc (am eca) hec with g|g|g|g;{exact absurd g.symm (fun g'=>w c hcI (hfc_a ic A g'.symm▸A))};{exact absurd g.symm (fun g'=>w c hcI (hfc_a J k g'.symm▸k))};{exact absurd g.symm (fun g'=>w c hcI (hfc_a ib r g'.symm▸r))};{exact(el h.1 heca_c (g.symm▸heca_c)).elim}
   exact hPQ ((hkill_ac P hPa hPc).trans (hkill_ac Q hQa hQc).symm)
  by_cases lc1:(af 14 D c1).card<=2
  · by_cases lc2:(af 14 D W).card<=2
    · exact hkill_c_both_le2 lc1 lc2
    · have hne_c2:(aZ D br W).Nonempty:=_cp.1 (by have:=bj h z br E W;omega)
      exact hkill_c_pos W a2 b2 c1 x2 x2 Zx2 Zx2 hc2 ha2 hb2 hnc2 hna2 hnb2 hnc1 hnx2 hnx2 bc2 ba2 bb2 gc2 ga2 gb2 gc2a2 ((ae _ _).2 (bm ((ae _ _).1 g22))) ((ae _ _).2 (bm ((ae _ _).1 g2b2))) ((ae _ _).2 (bm ((ae _ _).1 gc1b2))) gnica2 gnicb2 gniab2 gniba2 hWx2 hpx2 (fun g=>H (by rw[<- bx2,<-bc2,g])) (T.symm.trans hsx12) hWx2 hpx2 (fun g=>H (by rw[<- bx2,<-bc1,g])) (S.symm.trans hsx12) hne_c2 hnea2 hneb2 ha2_3
  · have hne_c1:(aZ D br c1).Nonempty:=_cp.1 (by have:=bj h z br E c1;omega)
    exact hkill_c_pos c1 R b1 W x1 x1 Zx1 Zx1 hc1 ha1 Y hnc1 hna1 hnb1 hnc2 Z Z bc1 ba1 bb1 gc1 ga1 gb1 gc1a1 ((ae _ _).2 (bm ((ae _ _).1 g11))) ((ae _ _).2 (bm ((ae _ _).1 g1b1))) ((ae _ _).2 (bm ((ae _ _).1 gc2b1))) gnica1 gnicb1 gniab1 gniba1 hWx1 hpx1 (fun g=>H (by rw[<- bx1,<-bc1,g])) S.symm hWx1 hpx1 (fun g=>H (by rw[<- bx1,<-bc2,g])) T.symm hne_c1 hnea1 hneb1 ha1_3
 by_cases hB0_e:(af 14 D 2).card<=2/\(af 14 D 6).card<=2;{exact n 2 6 4 5 13 9 12 11 8 10 1 3 (C 8 V) (C 10 V) (C 1 V) (C 3 V) V V V V hB0_e.1 hB0_e.2};by_cases hB1_e:(af 14 D 4).card<=2/\(af 14 D 5).card<=2;{exact n 4 5 2 6 13 9 11 12 10 8 1 3 (C 10 V) (C 8 V) (C 1 V) (C 3 V) V V V V hB1_e.1 hB1_e.2};by_cases hB2_e:(af 14 D 13).card<=2/\(af 14 D 9).card<=2;{exact n 13 9 12 11 2 6 4 5 1 3 8 10 (C 1 V) (C 3 V) (C 8 V) (C 10 V) V V V V hB2_e.1 hB2_e.2};by_cases hB3_e:(af 14 D 12).card<=2/\(af 14 D 11).card<=2;{exact n 12 11 13 9 2 6 5 4 3 1 8 10 (C 3 V) (C 1 V) (C 8 V) (C 10 V) V V V V hB3_e.1 hB3_e.2};have hget:∀ a b:O,¬ ((af 14 D a).card<=2/\(af 14 D b).card<=2) ->∃ v,(v=a\/v=b)/\(aZ D br v).Nonempty:=by{intro a b hnot;by_cases ha:(af 14 D a).card<=2;{exact⟨b,Or.inr rfl,_cp.1 (by have:=bj h z br E b;omega)⟩};{exact⟨a,Or.inl rfl,_cp.1 (by have:=bj h z br E a;omega)⟩}};obtain⟨v0,hv0,hnv0⟩:=hget 2 6 hB0_e;obtain⟨v1,hv1,hnv1⟩:=hget 4 5 hB1_e;obtain⟨v2,hv2,hnv2⟩:=hget 13 9 hB2_e;obtain⟨v3,hv3,hnv3⟩:=hget 12 11 hB3_e;have hv0m:v0∈_E8:=by rcases hv0 with rfl|rfl <;> decide
 have hv1m:v1∈_E8:=by rcases hv1 with rfl|rfl <;> decide
 have hv2m:v2∈_E8:=by rcases hv2 with rfl|rfl <;> decide
 have hv3m:v3∈_E8:=by rcases hv3 with rfl|rfl <;> decide
 have hb0:b9 v0=8:=by rcases hv0 with rfl|rfl <;> decide
 have Y:b9 v1=10:=by rcases hv1 with rfl|rfl <;> decide
 have hb2:b9 v2=1:=by rcases hv2 with rfl|rfl <;> decide
 have hb3:b9 v3=3:=by rcases hv3 with rfl|rfl <;> decide
 have hcard1:∀(v:O),v∈_E8 ->(aZ D br v).Nonempty ->(∃ w1 w2 w3:O,w1∈_E8 /\w2∈_E8 /\w3∈_E8 /\(b9 v≠b9 w1/\b9 v≠b9 w2/\b9 v≠b9 w3 /\b9 w1≠b9 w2/\b9 w1≠b9 w3/\b9 w2≠b9 w3) /\(aZ D br w1).Nonempty/\(aZ D br w2).Nonempty/\(aZ D br w3).Nonempty) ->(aZ D br v).card=1:=by{intro v hvm hnv ⟨w1,w2,w3,hw1,hw2,hw3,F,hnw1,hnw2,hnw3⟩;have hle2:(aZ D br v).card<=2:=by{have:=_cl (m▸_fs _ _:aZ D br v⊆{u1,u2});rw[_c2 s] at this;exact this};have hposv:0<(aZ D br v).card:=_cp.2 hnv;by_contra hne1;exact hno_R_all3 v w1 w2 w3 hvm hw1 hw2 hw3 F (_eqc (m▸_fs _ _) (by rw[_c2 s];omega)) hnw1 hnw2 hnw3};have c0:(aZ D br v0).card=1:=hcard1 v0 hv0m hnv0 ⟨v1,v2,v3,hv1m,hv2m,hv3m,by rw[hb0,Y,hb2,hb3];decide,hnv1,hnv2,hnv3⟩;have c1:(aZ D br v1).card=1:=hcard1 v1 hv1m hnv1 ⟨v0,v2,v3,hv0m,hv2m,hv3m,by rw[hb0,Y,hb2,hb3];decide,hnv0,hnv2,hnv3⟩;have W:(aZ D br v2).card=1:=hcard1 v2 hv2m hnv2 ⟨v0,v1,v3,hv0m,hv1m,hv3m,by rw[hb0,Y,hb2,hb3];decide,hnv0,hnv1,hnv3⟩;exact hno_3sing v0 v1 v2 hv0m hv1m hv2m (by rw[hb0,Y];decide) (by rw[hb0,hb2];decide) (by rw[Y,hb2];decide) c0 c1 W
lemma kA:∀ a:Fin 68,(bU a).card<=3 \/(∃ k:Fin 26,fA k=a) \/a.val=39\/a.val=40\/a.val=42\/a.val=44 \/a.val=45\/a.val=46\/a.val=48\/a.val=49 \/a.val=50\/a.val=51\/a.val=58\/a.val=62:=by
 decide +kernel
lemma g14_umbrella_lb_26 (C:Circuit) (d:Monotone2 C) (j:∀ x:O->_d,h_ x->C.eval (_of x)=true) (l:∀ x:O->_d,C.eval (_of x)=true->bx x) (e:∀ u v:O,¬ eW u v->C.eval (_of (b4 u v))=false) (f:C.size<=25):False:=by
 obtain⟨D,h,c,-,b,-,g⟩:=mU C d j l e f;obtain⟨idx,G⟩:=fP g;have G':aa 14 D=bU idx:=G.symm;have H:=bg 14 D;have m:=aV 14 D;rcases kA idx with
  i|⟨k,rfl⟩|n|p|q|r|s|t|w|y|z|A|B|E
 · by_cases I:bd 14 D<=(al 14 D).card
   · exact dn h c I idx G'
   · have F:3<=(bU idx).card:=by rw[<- G'] at i⊢;omega
     exact dp h c b (by rw[G'] at m;omega) idx F G'
 · exact nH h c b k G'
 · exact rY h c b ((show idx=⟨39,V⟩ from _fe n)▸G')
 · exact sd h c b ((show idx=⟨40,V⟩ from _fe p)▸G')
 · exact r_ h c b ((show idx=⟨42,V⟩ from _fe q)▸G')
 · exact se h c b ((show idx=⟨44,V⟩ from _fe r)▸G')
 · exact sc h c b ((show idx=⟨45,V⟩ from _fe s)▸G')
 · exact rZ h c b ((show idx=⟨46,V⟩ from _fe t)▸G')
 · exact r7 h c b ((show idx=⟨48,V⟩ from _fe w)▸G')
 · exact r8 h c b ((show idx=⟨49,V⟩ from _fe y)▸G')
 · exact r9 h c b ((show idx=⟨50,V⟩ from _fe z)▸G')
 · exact sf h c b ((show idx=⟨51,V⟩ from _fe A)▸G')
 · exact r0 h c b ((show idx=⟨58,V⟩ from _fe B)▸G')
 · exact r4 h c b ((show idx=⟨62,V⟩ from _fe E)▸G')
end _S
open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
def c_ (σ:O->O) (i:ℕ):ℕ:=if h:i<14 then (σ ⟨i,h⟩).val else i
lemma er (σ:O->O) {i:ℕ} (h:14<=i):c_ σ i=i:=by
 simp[c_,Nat.not_lt.mpr h]
lemma jE (σ:O->O) {i:ℕ} (h:i<14):c_ σ i<14:=by
 rw[c_,dif_pos h];exact(σ ⟨i,h⟩).isLt
def bG (σ:O->O) (C:Circuit):Circuit:=⟨C.gates.map fun g=>⟨g.op,g.inputs.map (c_ σ)⟩,c_ σ C.output⟩
lemma o6 (σ:_ep (O)) (c:_F Gate):∀ w w':_F _d,w.length=w'.length->14<=w.length ->(∀ i,w'.getD (c_ σ i) false=w.getD i false) ->∀ i,((c.map fun g=>(⟨g.op,g.inputs.map (c_ σ)⟩:Gate)).foldl _B.cE w').getD (c_ σ i) false =(c.foldl _B.cE w).getD i false:=by
 induction c with
 | nil=>intro w w' _ _ h i;exact h i
 | cons g c ih=>
  intro w w' k l h i;simp only[List.map_cons,List.foldl_cons];apply ih;{simp[_B.cE,k]};{simp[_B.cE];omega}
  · intro j
    have m:g.op.eval ((g.inputs.map (c_ σ)).map fun i=>w'.getD i false)=g.op.eval (g.inputs.map fun i=>w.getD i false):=by{rw[List.map_map];congr 1;exact List.map_congr_left (fun a _=>h a)};simp only[_B.cE];rw[m];rcases _nt j w.length with d|d|d
    · have d':c_ σ j<w'.length:=by
       by_cases h':j<14;{have:=jE σ h';omega};{rw[er σ (by omega)];omega}
      have e:=h j;simp only[List.getD_eq_getElem?_getD] at e⊢;rw[List.getElem?_append_left d',List.getElem?_append_left d];exact e
    · subst d;rw[er σ l];simp[List.getD_eq_getElem?_getD,k]
    · rw[er σ (by omega)]
      rw[List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]
lemma gj (σ:_ep (O)) (C:Circuit) (y:O->_d):(bG σ C).eval (_of y)=C.eval (_of fun i=>y (σ i)):=by
 change ((C.gates.map fun g=>(⟨g.op,g.inputs.map (c_ σ)⟩:Gate)).foldl _B.cE (_of y)).getD (c_ σ C.output) false=(C.gates.foldl _B.cE (_of fun i=>y (σ i))).getD C.output false;refine o6 σ C.gates (_of fun i=>y (σ i)) (_of y) (by simp) (by simp) ?_ C.output;intro i;by_cases a:i<14
 · rw[c_,dif_pos a,_lge _ _ (by simp[Fin.isLt]),
    _lge _ _ (by simp[a])]
   simp only[List.getElem_ofFn,Fin.eta]
 · rw[er σ (by omega),List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]
lemma gu (σ:_ep (O)) {C:Circuit} (h:IsAO2 14 C):IsAO2 14 (bG σ C):=by
 refine⟨fun g c=>?_,fun j i x l=>?_,fun g c=>?_⟩;{obtain⟨g',c',rfl⟩:=List.mem_map.mp c;exact h.1 g' c'}
 · simp only[bG] at i
   have i':j<C.gates.length:=by simpa using i
   have i'':j<(bG σ C).gates.length:=i;have c:gateAt (bG σ C) j=⟨(gateAt C j).op,(gateAt C j).inputs.map (c_ σ)⟩:=by{simp only[gateAt];rw[_lge _ _ i'',_lge _ _ i'];simp[bG]};rw[c,List.mem_map] at l;obtain⟨a,m,rfl⟩:=l;have k:=h.2.1 j i' a m;by_cases f:a<14;{have:=jE σ f;omega};{rw[er σ (by omega)];exact k}
 · obtain⟨g',c',rfl⟩:=List.mem_map.mp c;simp[h.2.2 g' c']
lemma pT (σ:_ep (O)):Function.Injective (c_ σ):=by
 intro a b c;by_cases d:a<14 <;> by_cases e:b<14
 · rw[c_,dif_pos d,c_,dif_pos e] at c
   exact Fin.ext_iff.1 (σ.injective (_fe c))
 · have:=jE σ d;rw[er σ (i:=b) (by omega)] at c;omega
 · have:=jE σ e;rw[er σ (i:=a) (by omega)] at c;omega
 · rw[er σ (by omega),er σ (by omega)] at c;exact c
lemma gk (σ:_ep (O)) {C:Circuit} (q:∀ j<C.size,opnd C j 0≠opnd C j 1) (r:∀ g∈C.gates,g.inputs.length=2):∀ j<(bG σ C).size,opnd (bG σ C) j 0≠opnd (bG σ C) j 1:=by
 intro j p;have p':j<C.gates.length:=by simpa[Circuit.size,bG] using p
 have d:=r (gateAt C j) (by rw[gateAt,_lge _ _ p'];exact List.getElem_mem p');obtain⟨a,b,e⟩:∃ a b,(gateAt C j).inputs=[a,b]:=by
  cases i:(gateAt C j).inputs with
  | nil=>simp[i] at d
  | cons x l1=>cases l1 with
   | nil=>simp[i] at d
   | cons y l2=>cases l2 with
    | nil=>exact⟨x,y,rfl⟩
    | cons _ _=>simp[i] at d
 have p'':j<(bG σ C).gates.length:=by simpa[Circuit.size] using p
 have e':C.gates[j].inputs=[a,b]:=by{dsimp only[gateAt] at e;rwa[_lge C.gates _ p'] at e};have s:gateAt (bG σ C) j=⟨(gateAt C j).op,[c_ σ a,c_ σ b]⟩:=by{simp only[gateAt];rw[_lge _ _ p'',_lge _ _ p'];simp[bG,e']};have k:opnd C j 0≠opnd C j 1:=q j p';have l:opnd C j 0=a:=by simp[opnd,e]
 have m:opnd C j 1=b:=by simp[opnd,e]
 simp only[opnd,s];exact fun n=>k (by rw[l,m];exact pT σ n)
def cQ (p l:Fin 7) (i:O):O:=if h:i.val<7 then
 let q:Fin 7:=⟨i.val,h⟩ - l;let r:Fin 7:=
  if p=l then q
  else if p=l+3 then 2*q+1
  else 4*q+3
 Fin.castAdd 7 r
 else
  let q:Fin 7:=⟨i.val - 7,by omega⟩ - l;let r:Fin 7:=
   if p=l then q
   else if p=l+3 then 2*q
   else 4*q
  Fin.natAdd 7 r
lemma mq:∀ p l:Fin 7,(p=l\/p=l+1\/p=l+3) ->∀ a b:O,cQ p l a=cQ p l b->a=b:=by
 decide +kernel
lemma fc:∀ p l a b:Fin 7,(p=l\/p=l+1\/p=l+3) ->((a=b\/a=b+1\/a=b+3)↔ ∃ a' b':Fin 7,cQ p l (Fin.castAdd 7 a)=Fin.castAdd 7 a' /\cQ p l (Fin.natAdd 7 b)=Fin.natAdd 7 b' /\(a'=b'\/a'=b'+1\/a'=b'+3)):=by
 decide +kernel
lemma kM:∀ p l:Fin 7,(p=l\/p=l+1\/p=l+3) ->cQ p l (Fin.castAdd 7 p)=0/\cQ p l (Fin.natAdd 7 l)=7:=by
 decide +kernel
noncomputable def kZ (p l:Fin 7) (a:p=l\/p=l+1\/p=l+3):_ep (O):=Equiv.ofBijective (cQ p l) ((Finite.injective_iff_bijective).1 (mq p l a))
lemma ff (p l:Fin 7) (a:p=l\/p=l+1\/p=l+3) (i:O):kZ p l a i=cQ p l i:=rfl
lemma kB (i:O):_B.kW (_B.kW i)=i:=by revert i;decide +kernel
def a_:_ep (O):=⟨_B.kW,_B.kW,kB,kB⟩
lemma qJ:a_ 0=0:=V
lemma qK:a_ 7=7:=V
lemma fg:∀ u v:O,_B.aO u v ->∃ p l:Fin 7,(p=l\/p=l+1\/p=l+3) /\((a_ u=Fin.castAdd 7 p/\a_ v=Fin.natAdd 7 l) \/(a_ v=Fin.castAdd 7 p/\a_ u=Fin.natAdd 7 l)):=by
 decide +kernel
lemma fU {D:Circuit} (f:Monotone2 D):∀ x y:O->_d,(∀ i,x i=true->y i=true) ->D.eval (_of x)=true->D.eval (_of y)=true:=by
 intro x y q w;have m:∀ n:_F Gate,(∀ g∈n,g.op=GateOp.and\/g.op=GateOp.or) ->∀ j l:_F _d,j.length=l.length ->(∀ k,j.getD k false=true->l.getD k false=true) ->∀ k,(n.foldl _B.cE j).getD k false=true ->(n.foldl _B.cE l).getD k false=true:=by
  intro n;induction n with
  | nil=>intro _ j l _ h k b;exact h k b
  | cons g rest ih=>
   intro p j l c h;apply ih (fun g' B'=>p g' (List.mem_cons_of_mem _ B')) _ _ (by simp[_B.cE,c]);intro k b;rcases _nt k j.length with s|t|A
   · simp only[_B.cE,List.getD_eq_getElem?_getD] at b⊢
     rw[List.getElem?_append_left s] at b;rw[List.getElem?_append_left (by omega)];exact h k b
   · subst t
     simp only[_B.cE,List.getD_eq_getElem?_getD,List.getElem?_append_right (le_refl _),List.getElem?_append_right (by omega:j.length<=l.length),Nat.sub_self,c,List.getElem?_cons_zero,Option.getD_some] at b⊢;rcases p g List.mem_cons_self with d|d <;> rw[d] at b⊢
     · simp only[GateOp.eval,List.all_map,List.all_eq_true,Function.comp_def,id_eq] at b⊢
       intro a u;exact h a (b a u)
     · simp only[GateOp.eval,List.any_map,List.any_eq_true,Function.comp_def,id_eq] at b⊢
       obtain⟨a,u,v⟩:=b;exact⟨a,u,h a v⟩
   · simp only[_B.cE] at b
     rw[List.getD_eq_default _ _ (by simp;omega)] at b;exact absurd b _fnt
 exact m D.gates (fun g B=>(f g B).1) (_of x) (_of y) (by simp) (fun k b=>by
  by_cases e:k<14
  · rw[_lge _ _ (by simp[e])] at b⊢
    simp only[List.getElem_ofFn] at b⊢;exact q ⟨k,e⟩ b
  · rw[List.getD_eq_default _ _ (by simp;omega)] at b
    exact absurd b _fnt) D.output w
abbrev ErSt:=_F Gate×_F (Option ℕ)
def bO (c:ErSt) (g:Gate):ErSt:=
 let a:=g.inputs.getD 0 0;let b:=g.inputs.getD 1 0;match g.op,c.2.getD a none,c.2.getD b none with
 | GateOp.and,some a',some b'=>⟨c.1 ++ [⟨GateOp.and,[a',b']⟩],c.2 ++ [some (14+c.1.length)]⟩
 | GateOp.and,_,_=>⟨c.1,c.2 ++ [none]⟩
 | GateOp.or,some a',some b'=>⟨c.1 ++ [⟨GateOp.or,[a',b']⟩],c.2 ++ [some (14+c.1.length)]⟩
 | GateOp.or,some a',none=>⟨c.1,c.2 ++ [some a']⟩
 | GateOp.or,none,some b'=>⟨c.1,c.2 ++ [some b']⟩
 | GateOp.or,none,none=>⟨c.1,c.2 ++ [none]⟩
 | _,_,_=>⟨c.1,c.2 ++ [none]⟩
def mr:ErSt:=⟨[],(List.range 14).map some ++ [none]⟩
lemma lR:mr.2.length=15:=V
lemma kC {w:ℕ} (h:w<14):mr.2.getD w none=some w:=by
 revert w h;decide
lemma mD:mr.2.getD 14 none=none:=V
lemma pU {w:ℕ} (h:15<=w):mr.2.getD w none=none:=by
 rw[List.getD_eq_default _ _ (by rw[lR];omega)]
lemma fr {w w':ℕ} (a:mr.2.getD w none=some w'):w<14/\w'=w:=by
 rcases Nat.lt_or_ge w 14 with h|h;{rw[kC h] at a;injection a with b;exact⟨h,b.symm⟩}
 · rcases Nat.eq_or_lt_of_le h with rfl|c
   · rw[mD] at a;contradiction
   · rw[pU c] at a;contradiction
lemma ir (a:_F Gate) (b:_F _d):(a.foldl _B.cE b).length=b.length+a.length:=by
 induction a generalizing b with
 | nil=>simp
 | cons g rest ih=>simp[List.foldl_cons,ih,_B.cE];omega
lemma ah {α:Type} (l:_F α) (v d:α) (w:ℕ):(l ++ [v]).getD w d=if w<l.length then l.getD w d else if w=l.length then v else d:=by
 by_cases a:w<l.length;{simp[a,List.getD_eq_getElem?_getD,List.getElem?_append_left a]}
 · by_cases b:w=l.length
   · subst b;simp[List.getD_eq_getElem?_getD]
   · rw[if_neg a,if_neg b]
     exact List.getD_eq_default _ _ (by simp;omega)
lemma an (a:_F _d) (g:Gate) (w:ℕ):(_B.cE a g).getD w false =if w<a.length then a.getD w false
 else if w=a.length then g.op.eval (g.inputs.map fun i=>a.getD i false)
 else false:=
 ah a _ false w
lemma jY (b:ErSt) (g:Gate) {a:ℕ} (c:a<b.2.length):(bO b g).2.getD a none=b.2.getD a none:=by
 cases d:g.op <;>
 cases ha':b.2.getD (g.inputs.getD 0 0) none <;>
 cases hb':b.2.getD (g.inputs.getD 1 0) none <;>
 simp only[bO,d,ha',hb']<;>
 rw[ah,if_pos c]
lemma mZ (d:ErSt) (g:Gate) (k:ℕ) (b:d.2.length=15+k) (z:d.1.length<=k) (l:∀ g'∈d.1,(g'.op=GateOp.and\/g'.op=GateOp.or)/\g'.inputs.length<=2) (i:∀ w w',d.2.getD w none=some w'->w'<14+d.1.length) (u:d.2.getD 14 none=none) (c:g.op=GateOp.and\/g.op=GateOp.or) (j:g.inputs=[g.inputs.getD 0 0,g.inputs.getD 1 0]):
 let d':=bO d g;d'.2.length=15+(k+1) /\
 d'.1.length<=k+1 /\
 d'.1.length<=d.1.length+1 /\
 ((d.2.getD (g.inputs.getD 0 0) none=none\/d.2.getD (g.inputs.getD 1 0) none=none) ->d'.1.length=d.1.length) /\
 (∀ g'∈d'.1,(g'.op=GateOp.and\/g'.op=GateOp.or)/\g'.inputs.length<=2) /\
 (∀ w w',d'.2.getD w none=some w'->w'<14+d'.1.length) /\
 d'.2.getD 14 none=none /\
 ((∀ w,w∈g.inputs->d.2.getD w none≠none)->∃ x,d'.2.getD (15+k) none=some x):=by
 have p:∀(op:GateOp) (A:op=GateOp.and\/op=GateOp.or) (a' b':ℕ),
  let r:ErSt:=(d.1 ++ [⟨op,[a',b']⟩],d.2 ++ [some (14+d.1.length)]);r.2.length=15+(k+1)/\r.1.length<=k+1/\r.1.length<=d.1.length+1 /\
  (∀ g'∈r.1,(g'.op=GateOp.and\/g'.op=GateOp.or)/\g'.inputs.length<=2) /\
  (∀ w w',r.2.getD w none=some w'->w'<14+r.1.length) /\
  r.2.getD 14 none=none:=by
  intro op A a' b';simp only[List.length_append,List.length_singleton,b];refine⟨by omega,by omega,by omega,fun g' hg'=>?_,fun w w' h=>?_,?_⟩
  · rw[List.mem_append,List.mem_singleton] at hg'
    rcases hg' with hg'|rfl;exact l g' hg';exact⟨A,by simp⟩
  · rcases _nt w d.2.length with q|rfl|q
    · rw[ah,if_pos q] at h
      have:=i w w' h;omega
    · rw[ah,if_neg (_nr _),if_pos rfl] at h
      injection h with s;subst s;omega
    · rw[ah,if_neg (by omega),if_neg (by omega)] at h;contradiction
  · rw[ah,if_pos (by omega)];exact u
 have a :
  let r:ErSt:=(d.1,d.2 ++ [none]);r.2.length=15+(k+1)/\r.1.length<=k+1/\r.1.length<=d.1.length+1 /\
  r.1.length=d.1.length /\
  (∀ g'∈r.1,(g'.op=GateOp.and\/g'.op=GateOp.or)/\g'.inputs.length<=2) /\
  (∀ w w',r.2.getD w none=some w'->w'<14+r.1.length) /\
  r.2.getD 14 none=none:=by
  simp only[List.length_append,List.length_singleton,b];refine⟨by omega,by omega,by omega,trivial,l,fun w w' h=>?_,?_⟩
  · rcases _nt w d.2.length with q|rfl|q
    · rw[ah,if_pos q] at h;exact i w w' h
    · rw[ah,if_neg (_nr _),if_pos rfl] at h;contradiction
    · rw[ah,if_neg (by omega),if_neg (by omega)] at h;contradiction
  · rw[ah,if_pos (by omega)];exact u
 rcases c with c|c <;>
 cases e:d.2.getD (g.inputs.getD 0 0) none <;>
 cases f:d.2.getD (g.inputs.getD 1 0) none
 · dsimp only[bO];rw[c,e,f];dsimp only
   exact⟨a.1,a.2.1,a.2.2.1,fun _=>a.2.2.2.1,a.2.2.2.2.1,a.2.2.2.2.2.1,a.2.2.2.2.2.2,fun t=>absurd e (t _ (j▸List.mem_cons_self))⟩
 · dsimp only[bO];rw[c,e,f];dsimp only
   exact⟨a.1,a.2.1,a.2.2.1,fun _=>a.2.2.2.1,a.2.2.2.2.1,a.2.2.2.2.2.1,a.2.2.2.2.2.2,fun t=>absurd e (t _ (j▸List.mem_cons_self))⟩
 · dsimp only[bO];rw[c,e,f];dsimp only
   exact⟨a.1,a.2.1,a.2.2.1,fun _=>a.2.2.2.1,a.2.2.2.2.1,a.2.2.2.2.2.1,a.2.2.2.2.2.2,fun t=>absurd f (t _ (j▸List.mem_cons_of_mem _ (List.mem_singleton_self _)))⟩
 · dsimp only[bO];rw[c,e,f];dsimp only
   refine(fun H=>⟨H.1,H.2.1,H.2.2.1,fun y=>by rcases y with y|y <;> contradiction,H.2.2.2.1,H.2.2.2.2.1,H.2.2.2.2.2,fun _=>⟨14+d.1.length,?_⟩⟩) (p GateOp.and (Or.inl rfl) _ _);rw[ah,if_neg (by omega),if_pos b.symm]
 · dsimp only[bO];rw[c,e,f];dsimp only
   exact⟨a.1,a.2.1,a.2.2.1,fun _=>a.2.2.2.1,a.2.2.2.2.1,a.2.2.2.2.2.1,a.2.2.2.2.2.2,fun t=>absurd e (t _ (j▸List.mem_cons_self))⟩
 · dsimp only[bO];rw[c,e,f];dsimp only
   refine⟨by rw[List.length_append,List.length_singleton,b];omega,by omega,by omega,fun _=>rfl,l,fun w w' h=>?_,?_,fun t=>absurd e (t _ (j▸List.mem_cons_self))⟩
   · rcases _nt w d.2.length with q|rfl|q
     · rw[ah,if_pos q] at h;exact i w w' h
     · rw[ah,if_neg (_nr _),if_pos rfl] at h
       injection h with s;subst s;exact i _ _ f
     · rw[ah,if_neg (by omega),if_neg (by omega)] at h;contradiction
   · rw[ah,if_pos (by omega)];exact u
 · dsimp only[bO];rw[c,e,f];dsimp only
   refine⟨by rw[List.length_append,List.length_singleton,b];omega,by omega,by omega,fun _=>rfl,l,fun w w' h=>?_,?_,fun t=>absurd f (t _ (j▸List.mem_cons_of_mem _ (List.mem_singleton_self _)))⟩
   · rcases _nt w d.2.length with q|rfl|q
     · rw[ah,if_pos q] at h;exact i w w' h
     · rw[ah,if_neg (_nr _),if_pos rfl] at h
       injection h with s;subst s;exact i _ _ e
     · rw[ah,if_neg (by omega),if_neg (by omega)] at h;contradiction
   · rw[ah,if_pos (by omega)];exact u
 · dsimp only[bO];rw[c,e,f];dsimp only
   refine(fun H=>⟨H.1,H.2.1,H.2.2.1,fun y=>by rcases y with y|y <;> contradiction,H.2.2.2.1,H.2.2.2.2.1,H.2.2.2.2.2,fun _=>⟨14+d.1.length,?_⟩⟩) (p GateOp.or (Or.inr rfl) _ _);rw[ah,if_neg (by omega),if_pos b.symm]
lemma nJ (n:ErSt) (g:Gate) (k:ℕ) (A:_F _d) (r:_F _d) (B:A.length=14) (x:n.2.length=15+k) (u:∀ w w',n.2.getD w none=some w'->w'<14+n.1.length) (y:r.length=15+k) (c:g.op=GateOp.and\/g.op=GateOp.or) (j:g.inputs=[g.inputs.getD 0 0,g.inputs.getD 1 0]) (s:g.inputs.getD 0 0<15+k) (t:g.inputs.getD 1 0<15+k) (e:∀ w w',n.2.getD w none=some w'->(n.1.foldl _B.cE A).getD w' false=true->r.getD w false=true) (b:∀ w<15+k,n.2.getD w none=none->r.getD w false=false) (f:∀ w w',n.2.getD w none=some w'->(n.1.foldl _B.cE A).getD w' false=r.getD w false):
 let n':=bO n g;let r':=_B.cE r g;let ws2':=n'.1.foldl _B.cE A
 (∀ w w',n'.2.getD w none=some w'->ws2'.getD w' false=true->r'.getD w false=true) /\
 (∀ w<15+(k+1),n'.2.getD w none=none->r'.getD w false=false) /\
 (∀ w w',n'.2.getD w none=some w'->ws2'.getD w' false=r'.getD w false):=by
 have z:(n.1.foldl _B.cE A).length=14+n.1.length:=by rw[ir,B]
 rcases c with c|c <;>
 cases l:n.2.getD (g.inputs.getD 0 0) none <;>
 cases m:n.2.getD (g.inputs.getD 1 0) none
 · dsimp only[bO];rw[c,l,m];dsimp only
   refine⟨fun w w' a q=>?_,fun w a h=>?_,fun w w' a=>?_⟩
   · rcases _nt w n.2.length with d|rfl|d
     · rw[ah,if_pos d] at a
       rw[an,if_pos (by omega)];exact e w w' a q
     · rw[ah,if_neg (_nr _),if_pos rfl] at a;contradiction
     · rw[ah,if_neg (by omega),if_neg (by omega)] at a;contradiction
   · rcases _nt w r.length with d|rfl|d
     · rw[ah,if_pos (by omega)] at h
       rw[an,if_pos d];exact b w (by omega) h
     · rw[an,if_neg (_nr _),if_pos rfl,j,c]
       simp only[GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,b _ s l];simp
     · omega
   · rcases _nt w n.2.length with d|rfl|d
     · rw[ah,if_pos d] at a
       rw[an,if_pos (by omega)];exact f w w' a
     · rw[ah,if_neg (_nr _),if_pos rfl] at a;contradiction
     · rw[ah,if_neg (by omega),if_neg (by omega)] at a;contradiction
 · dsimp only[bO];rw[c,l,m];dsimp only
   refine⟨fun w w' a q=>?_,fun w a h=>?_,fun w w' a=>?_⟩
   · rcases _nt w n.2.length with d|rfl|d
     · rw[ah,if_pos d] at a
       rw[an,if_pos (by omega)];exact e w w' a q
     · rw[ah,if_neg (_nr _),if_pos rfl] at a;contradiction
     · rw[ah,if_neg (by omega),if_neg (by omega)] at a;contradiction
   · rcases _nt w r.length with d|rfl|d
     · rw[ah,if_pos (by omega)] at h
       rw[an,if_pos d];exact b w (by omega) h
     · rw[an,if_neg (_nr _),if_pos rfl,j,c]
       simp only[GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,b _ s l];simp
     · omega
   · rcases _nt w n.2.length with d|rfl|d
     · rw[ah,if_pos d] at a
       rw[an,if_pos (by omega)];exact f w w' a
     · rw[ah,if_neg (_nr _),if_pos rfl] at a;contradiction
     · rw[ah,if_neg (by omega),if_neg (by omega)] at a;contradiction
 · dsimp only[bO];rw[c,l,m];dsimp only
   refine⟨fun w w' a q=>?_,fun w a h=>?_,fun w w' a=>?_⟩
   · rcases _nt w n.2.length with d|rfl|d
     · rw[ah,if_pos d] at a
       rw[an,if_pos (by omega)];exact e w w' a q
     · rw[ah,if_neg (_nr _),if_pos rfl] at a;contradiction
     · rw[ah,if_neg (by omega),if_neg (by omega)] at a;contradiction
   · rcases _nt w r.length with d|rfl|d
     · rw[ah,if_pos (by omega)] at h
       rw[an,if_pos d];exact b w (by omega) h
     · rw[an,if_neg (_nr _),if_pos rfl,j,c]
       simp only[GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,b _ t m];simp
     · omega
   · rcases _nt w n.2.length with d|rfl|d
     · rw[ah,if_pos d] at a
       rw[an,if_pos (by omega)];exact f w w' a
     · rw[ah,if_neg (_nr _),if_pos rfl] at a;contradiction
     · rw[ah,if_neg (by omega),if_neg (by omega)] at a;contradiction
 · dsimp only[bO];rw[c,l,m];dsimp only
   rw[List.foldl_append,List.foldl_cons,List.foldl_nil];refine⟨fun w w' a q=>?_,fun w a h=>?_,fun w w' a=>?_⟩
   · rcases _nt w n.2.length with d|rfl|d
     · rw[ah,if_pos d] at a
       have v:=u w w' a;rw[an,if_pos (by omega)];rw[an,if_pos (by omega)] at q;exact e w w' a q
     · rw[ah,if_neg (_nr _),if_pos rfl] at a
       injection a with p;subst p;rw[an,if_neg (by omega),if_pos (by omega)] at q;rw[an,if_neg (by omega),if_pos (by omega),j,c];simp only[List.map_cons,List.map_nil,GateOp.eval,id_eq,List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true] at q⊢;exact⟨e _ _ l q.1,e _ _ m q.2⟩
     · rw[ah,if_neg (by omega),if_neg (by omega)] at a;contradiction
   · rcases _nt w n.2.length with d|rfl|d
     · rw[ah,if_pos d] at h
       rw[an,if_pos (by omega)];exact b w (by omega) h
     · rw[ah,if_neg (_nr _),if_pos rfl] at h;contradiction
     · omega
   · rcases _nt w n.2.length with d|rfl|d
     · rw[ah,if_pos d] at a
       have v:=u w w' a;rw[an,if_pos (by omega)];rw[an,if_pos (by omega)];exact f w w' a
     · rw[ah,if_neg (_nr _),if_pos rfl] at a
       injection a with p;subst p;rw[an,if_neg (by omega),if_pos (by omega)];rw[an,if_neg (by omega),if_pos (by omega),j,c];simp only[GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,f _ _ l,f _ _ m]
     · rw[ah,if_neg (by omega),if_neg (by omega)] at a;contradiction
 · dsimp only[bO];rw[c,l,m];dsimp only
   refine⟨fun w w' a q=>?_,fun w a h=>?_,fun w w' a=>?_⟩
   · rcases _nt w n.2.length with d|rfl|d
     · rw[ah,if_pos d] at a
       rw[an,if_pos (by omega)];exact e w w' a q
     · rw[ah,if_neg (_nr _),if_pos rfl] at a;contradiction
     · rw[ah,if_neg (by omega),if_neg (by omega)] at a;contradiction
   · rcases _nt w r.length with d|rfl|d
     · rw[ah,if_pos (by omega)] at h
       rw[an,if_pos d];exact b w (by omega) h
     · rw[an,if_neg (_nr _),if_pos rfl,j,c]
       simp only[GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,b _ s l,b _ t m];simp
     · omega
   · rcases _nt w n.2.length with d|rfl|d
     · rw[ah,if_pos d] at a
       rw[an,if_pos (by omega)];exact f w w' a
     · rw[ah,if_neg (_nr _),if_pos rfl] at a;contradiction
     · rw[ah,if_neg (by omega),if_neg (by omega)] at a;contradiction
 · dsimp only[bO];rw[c,l,m];dsimp only
   refine⟨fun w w' a q=>?_,fun w a h=>?_,fun w w' a=>?_⟩
   · rcases _nt w n.2.length with d|rfl|d
     · rw[ah,if_pos d] at a
       rw[an,if_pos (by omega)];exact e w w' a q
     · rw[ah,if_neg (_nr _),if_pos rfl] at a
       injection a with p;subst p;rw[an,if_neg (by omega),if_pos (by omega),j,c];simp only[List.map_cons,List.map_nil,GateOp.eval,id_eq,List.any_cons,List.any_nil,Bool.or_false,Bool.or_eq_true];exact Or.inr (e _ _ m q)
     · rw[ah,if_neg (by omega),if_neg (by omega)] at a;contradiction
   · rcases _nt w n.2.length with d|rfl|d
     · rw[ah,if_pos d] at h
       rw[an,if_pos (by omega)];exact b w (by omega) h
     · rw[ah,if_neg (_nr _),if_pos rfl] at h;contradiction
     · omega
   · rcases _nt w n.2.length with d|rfl|d
     · rw[ah,if_pos d] at a
       rw[an,if_pos (by omega)];exact f w w' a
     · rw[ah,if_neg (_nr _),if_pos rfl] at a
       injection a with p;subst p;rw[an,if_neg (by omega),if_pos (by omega),j,c];have C:=b _ s l;simp only[GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,C,f _ _ m];simp
     · rw[ah,if_neg (by omega),if_neg (by omega)] at a;contradiction
 · dsimp only[bO];rw[c,l,m];dsimp only
   refine⟨fun w w' a q=>?_,fun w a h=>?_,fun w w' a=>?_⟩
   · rcases _nt w n.2.length with d|rfl|d
     · rw[ah,if_pos d] at a
       rw[an,if_pos (by omega)];exact e w w' a q
     · rw[ah,if_neg (_nr _),if_pos rfl] at a
       injection a with p;subst p;rw[an,if_neg (by omega),if_pos (by omega),j,c];simp only[List.map_cons,List.map_nil,GateOp.eval,id_eq,List.any_cons,List.any_nil,Bool.or_false,Bool.or_eq_true];exact Or.inl (e _ _ l q)
     · rw[ah,if_neg (by omega),if_neg (by omega)] at a;contradiction
   · rcases _nt w n.2.length with d|rfl|d
     · rw[ah,if_pos d] at h
       rw[an,if_pos (by omega)];exact b w (by omega) h
     · rw[ah,if_neg (_nr _),if_pos rfl] at h;contradiction
     · omega
   · rcases _nt w n.2.length with d|rfl|d
     · rw[ah,if_pos d] at a
       rw[an,if_pos (by omega)];exact f w w' a
     · rw[ah,if_neg (_nr _),if_pos rfl] at a
       injection a with p;subst p;rw[an,if_neg (by omega),if_pos (by omega),j,c];have D:=b _ t m;simp only[GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,D,f _ _ l];simp
     · rw[ah,if_neg (by omega),if_neg (by omega)] at a;contradiction
 · dsimp only[bO];rw[c,l,m];dsimp only
   rw[List.foldl_append,List.foldl_cons,List.foldl_nil];refine⟨fun w w' a q=>?_,fun w a h=>?_,fun w w' a=>?_⟩
   · rcases _nt w n.2.length with d|rfl|d
     · rw[ah,if_pos d] at a
       have v:=u w w' a;rw[an,if_pos (by omega)];rw[an,if_pos (by omega)] at q;exact e w w' a q
     · rw[ah,if_neg (_nr _),if_pos rfl] at a
       injection a with p;subst p;rw[an,if_neg (by omega),if_pos (by omega)] at q;rw[an,if_neg (by omega),if_pos (by omega),j,c];simp only[List.map_cons,List.map_nil,GateOp.eval,id_eq,List.any_cons,List.any_nil,Bool.or_false,Bool.or_eq_true] at q⊢;rcases q with q|q;{exact Or.inl (e _ _ l q)};{exact Or.inr (e _ _ m q)}
     · rw[ah,if_neg (by omega),if_neg (by omega)] at a;contradiction
   · rcases _nt w n.2.length with d|rfl|d
     · rw[ah,if_pos d] at h
       rw[an,if_pos (by omega)];exact b w (by omega) h
     · rw[ah,if_neg (_nr _),if_pos rfl] at h;contradiction
     · omega
   · rcases _nt w n.2.length with d|rfl|d
     · rw[ah,if_pos d] at a
       have v:=u w w' a;rw[an,if_pos (by omega)];rw[an,if_pos (by omega)];exact f w w' a
     · rw[ah,if_neg (_nr _),if_pos rfl] at a
       injection a with p;subst p;rw[an,if_neg (by omega),if_pos (by omega)];rw[an,if_neg (by omega),if_pos (by omega),j,c];simp only[GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,f _ _ l,f _ _ m]
     · rw[ah,if_neg (by omega),if_neg (by omega)] at a;contradiction
lemma jF (f:ErSt) (g:Gate) (k:ℕ) (t:_F _d) (p:_F _d) (u:t.length=14) (q:f.2.length=15+k) (n:∀ w w',f.2.getD w none=some w'->w'<14+f.1.length) (r:p.length=15+k) (c:g.op=GateOp.and\/g.op=GateOp.or) (j:g.inputs=[g.inputs.getD 0 0,g.inputs.getD 1 0]) (a:∀ w w',f.2.getD w none=some w'->(f.1.foldl _B.cE t).getD w' false=true->p.getD w false=true):∀ w w',(bO f g).2.getD w none=some w' ->((bO f g).1.foldl _B.cE t).getD w' false=true ->(_B.cE p g).getD w false=true:=by
 have s:(f.1.foldl _B.cE t).length=14+f.1.length:=by rw[ir,u]
 rcases c with c|c <;>
 cases l:f.2.getD (g.inputs.getD 0 0) none <;>
 cases m:f.2.getD (g.inputs.getD 1 0) none <;>
 (dsimp only[bO];rw[c,l,m];dsimp only)<;>
 intro w w' b d
 · rcases _nt w f.2.length with e|rfl|e
   · rw[ah,if_pos e] at b
     rw[an,if_pos (by omega)];exact a w w' b d
   · rw[ah,if_neg (_nr _),if_pos rfl] at b;contradiction
   · rw[ah,if_neg (by omega),if_neg (by omega)] at b;contradiction
 · rcases _nt w f.2.length with e|rfl|e
   · rw[ah,if_pos e] at b
     rw[an,if_pos (by omega)];exact a w w' b d
   · rw[ah,if_neg (_nr _),if_pos rfl] at b;contradiction
   · rw[ah,if_neg (by omega),if_neg (by omega)] at b;contradiction
 · rcases _nt w f.2.length with e|rfl|e
   · rw[ah,if_pos e] at b
     rw[an,if_pos (by omega)];exact a w w' b d
   · rw[ah,if_neg (_nr _),if_pos rfl] at b;contradiction
   · rw[ah,if_neg (by omega),if_neg (by omega)] at b;contradiction
 · rw[List.foldl_append,List.foldl_cons,List.foldl_nil] at d
   rcases _nt w f.2.length with e|rfl|e
   · rw[ah,if_pos e] at b
     have v:=n w w' b;rw[an,if_pos (by omega)];rw[an,if_pos (by omega)] at d;exact a w w' b d
   · rw[ah,if_neg (_nr _),if_pos rfl] at b
     injection b with i;subst i;rw[an,if_neg (by omega),if_pos (by omega)] at d;rw[an,if_neg (by omega),if_pos (by omega),j,c];simp only[List.map_cons,List.map_nil,GateOp.eval,id_eq,List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true] at d⊢;exact⟨a _ _ l d.1,a _ _ m d.2⟩
   · rw[ah,if_neg (by omega),if_neg (by omega)] at b;contradiction
 · rcases _nt w f.2.length with e|rfl|e
   · rw[ah,if_pos e] at b
     rw[an,if_pos (by omega)];exact a w w' b d
   · rw[ah,if_neg (_nr _),if_pos rfl] at b;contradiction
   · rw[ah,if_neg (by omega),if_neg (by omega)] at b;contradiction
 · rcases _nt w f.2.length with e|rfl|e
   · rw[ah,if_pos e] at b
     rw[an,if_pos (by omega)];exact a w w' b d
   · rw[ah,if_neg (_nr _),if_pos rfl] at b
     injection b with i;subst i;rw[an,if_neg (by omega),if_pos (by omega),j,c];simp only[List.map_cons,List.map_nil,GateOp.eval,id_eq,List.any_cons,List.any_nil,Bool.or_false,Bool.or_eq_true];exact Or.inr (a _ _ m d)
   · rw[ah,if_neg (by omega),if_neg (by omega)] at b;contradiction
 · rcases _nt w f.2.length with e|rfl|e
   · rw[ah,if_pos e] at b
     rw[an,if_pos (by omega)];exact a w w' b d
   · rw[ah,if_neg (_nr _),if_pos rfl] at b
     injection b with i;subst i;rw[an,if_neg (by omega),if_pos (by omega),j,c];simp only[List.map_cons,List.map_nil,GateOp.eval,id_eq,List.any_cons,List.any_nil,Bool.or_false,Bool.or_eq_true];exact Or.inl (a _ _ l d)
   · rw[ah,if_neg (by omega),if_neg (by omega)] at b;contradiction
 · rw[List.foldl_append,List.foldl_cons,List.foldl_nil] at d
   rcases _nt w f.2.length with e|rfl|e
   · rw[ah,if_pos e] at b
     have v:=n w w' b;rw[an,if_pos (by omega)];rw[an,if_pos (by omega)] at d;exact a w w' b d
   · rw[ah,if_neg (_nr _),if_pos rfl] at b
     injection b with i;subst i;rw[an,if_neg (by omega),if_pos (by omega)] at d;rw[an,if_neg (by omega),if_pos (by omega),j,c];simp only[List.map_cons,List.map_nil,GateOp.eval,id_eq,List.any_cons,List.any_nil,Bool.or_false,Bool.or_eq_true] at d⊢;rcases d with d|d;{exact Or.inl (a _ _ l d)};{exact Or.inr (a _ _ m d)}
   · rw[ah,if_neg (by omega),if_neg (by omega)] at b;contradiction
lemma jc (d:ErSt) (g:Gate) (k:ℕ) (t:_F _d) (l:_F _d) (u:t.length=14) (q:d.2.length=15+k) (i:∀ w w',d.2.getD w none=some w'->w'<14+d.1.length) (r:l.length=15+k) (b:g.op=GateOp.and\/g.op=GateOp.or) (j:g.inputs=[g.inputs.getD 0 0,g.inputs.getD 1 0]) (f:∃ a',d.2.getD (g.inputs.getD 0 0) none=some a') (h:∃ b',d.2.getD (g.inputs.getD 1 0) none=some b') (a:∀ w w',d.2.getD w none=some w'->(d.1.foldl _B.cE t).getD w' false=l.getD w false):∀ w w',(bO d g).2.getD w none=some w' ->((bO d g).1.foldl _B.cE t).getD w' false=(_B.cE l g).getD w false:=by
 obtain⟨a',m⟩:=f;obtain⟨b',n⟩:=h;have s:(d.1.foldl _B.cE t).length=14+d.1.length:=by rw[ir,u]
 rcases b with b|b <;>
 (dsimp only[bO];rw[b,m,n];dsimp only)<;>
 rw[List.foldl_append,List.foldl_cons,List.foldl_nil]<;>
 intro w w' e <;>
 (rcases _nt w d.2.length with v|rfl|v)
 · rw[ah,if_pos v] at e
   have x:=i w w' e;rw[an,if_pos (by omega)];rw[an,if_pos (by omega)];exact a w w' e
 · rw[ah,if_neg (_nr _),if_pos rfl] at e
   injection e with p;subst p;rw[an,if_neg (by omega),if_pos (by omega)];rw[an,if_neg (by omega),if_pos (by omega),j,b];simp only[GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,a _ _ m,a _ _ n]
 · rw[ah,if_neg (by omega),if_neg (by omega)] at e;contradiction
 · rw[ah,if_pos v] at e
   have x:=i w w' e;rw[an,if_pos (by omega)];rw[an,if_pos (by omega)];exact a w w' e
 · rw[ah,if_neg (_nr _),if_pos rfl] at e
   injection e with p;subst p;rw[an,if_neg (by omega),if_pos (by omega)];rw[an,if_neg (by omega),if_pos (by omega),j,b];simp only[GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,a _ _ m,a _ _ n]
 · rw[ah,if_neg (by omega),if_neg (by omega)] at e;contradiction
lemma lS (u' v':O) (H:Gate) (h5:H.op=GateOp.and/\H.inputs.length=2/\H.inputs.getD 0 0=u'.val/\H.inputs.getD 1 0=v'.val) (d:_F Gate) (A:∀ k,k<d.length ->
 let g:=d.getD k ⟨GateOp.or,[]⟩
 (g.op=GateOp.and\/g.op=GateOp.or)/\g.inputs.length=2 /\
 g.inputs.getD 0 0<14+1+k/\g.inputs.getD 1 0<14+1+k):
 let e:=d.foldl bO mr;e.2.length=15+d.length /\
 e.1.length<=d.length /\
 ((∃ g∈d,14∈g.inputs)->e.1.length+1<=d.length) /\
 (∀ g∈e.1,(g.op=GateOp.and\/g.op=GateOp.or)/\g.inputs.length<=2) /\
 (∀ w w',e.2.getD w none=some w'->w'<14+e.1.length) /\
 e.2.getD 14 none=none /\
 ((∀ g∈d,14∉g.inputs)->∀ w<15+d.length,w≠14->∃ w',e.2.getD w none=some w') /\
 (∀ x:O->_d,
  let y:=_of x;let h:=(H :: d).foldl _B.cE y;let s:=e.1.foldl _B.cE y
  (∀ w w',e.2.getD w none=some w'->s.getD w' false=true->h.getD w false=true) /\
  ((x u'=false\/x v'=false) ->(∀ w<15+d.length,e.2.getD w none=none->h.getD w false=false) /\(∀ w w',e.2.getD w none=some w'->s.getD w' false=h.getD w false)) /\
  ((∀ g∈d,14∉g.inputs) ->∀ w w',e.2.getD w none=some w'->s.getD w' false=h.getD w false)):=by
 have Q:∀ k,k<=d.length ->
  let F:=d.take k;let e:=F.foldl bO mr;e.2.length=15+F.length /\
  e.1.length<=F.length /\
  ((∃ g∈F,14∈g.inputs)->e.1.length+1<=F.length) /\
  (∀ g∈e.1,(g.op=GateOp.and\/g.op=GateOp.or)/\g.inputs.length<=2) /\
  (∀ w w',e.2.getD w none=some w'->w'<14+e.1.length) /\
  e.2.getD 14 none=none /\
  ((∀ g∈F,14∉g.inputs)->∀ w<15+F.length,w≠14->∃ w',e.2.getD w none=some w') /\
  (∀ x:O->_d,
   let y:=_of x;let h:=(H :: F).foldl _B.cE y;let s:=e.1.foldl _B.cE y
   (∀ w w',e.2.getD w none=some w'->s.getD w' false=true->h.getD w false=true) /\
   ((x u'=false\/x v'=false) ->(∀ w<15+F.length,e.2.getD w none=none->h.getD w false=false) /\(∀ w w',e.2.getD w none=some w'->s.getD w' false=h.getD w false)) /\
   ((∀ g∈F,14∉g.inputs) ->∀ w w',e.2.getD w none=some w'->s.getD w' false=h.getD w false)):=by
  intro k hk;induction k with
  | zero=>
   simp only[List.take_zero,List.foldl_nil,List.length_nil];refine⟨lR,Nat.le_refl _,fun ⟨g,hg,_⟩=>absurd hg (by simp),fun g hg=>absurd hg (by simp[mr]),fun w w' G=>(fr G).2▸(fr G).1,mD,fun _ w G R=>⟨w,kC (by omega)⟩,fun x=>?_⟩;refine⟨fun w w' G X=>?_,fun S=>⟨fun w hw15 hwn=>?_,fun w w' G=>?_⟩,fun _ w w' G=>?_⟩
   · obtain⟨r,rfl⟩:=fr G
     dsimp only[mr] at X⊢;rw[List.foldl_nil] at X;rw[List.foldl_cons,List.foldl_nil,an,if_pos (by simp[r])];exact X
   · have Y:w=14:=by
      by_contra R;by_cases hlt:w<14;{rw[kC hlt] at hwn;contradiction};{omega}
     subst Y;obtain⟨Z,i,h0a,h0b⟩:=h5;have T:H.inputs=[u'.val,v'.val]:=by
      cases I:H.inputs with
      | nil=>rw[I] at i;simp at i
      | cons a l1=>cases l1 with
       | nil=>rw[I] at i;simp at i
       | cons b l2=>cases l2 with
        | nil=>
         have ha':a=u'.val:=by simpa[I] using h0a
         have hb':b=v'.val:=by simpa[I] using h0b
         rw[ha',hb']
        | cons _ _=>rw[I] at i;simp at i
     rw[List.foldl_cons,List.foldl_nil,an,if_neg (by simp),if_pos (by simp)];simp only[Z,T,List.map_cons,List.map_nil,GateOp.eval,id_eq,List.all_cons,List.all_nil,Bool.and_true];have L:∀ a:O,(_of x).getD a.val false=x a:=fun a=>by{rw[_lge _ _ (by simp),List.getElem_ofFn]};rw[L u',L v',Bool.and_eq_false_iff];exact S
   · obtain⟨r,rfl⟩:=fr G
     dsimp only[mr];rw[List.foldl_nil,List.foldl_cons,List.foldl_nil,an,if_pos (by simp[r])]
   · obtain⟨r,rfl⟩:=fr G
     dsimp only[mr];rw[List.foldl_nil,List.foldl_cons,List.foldl_nil,an,if_pos (by simp[r])]
  | succ k ih=>
   have B:k<d.length:=by omega
   obtain⟨ih_rlen,ih_glen,ih_g14,ih_gsok,ih_wlt,ih_14,ih_all,ih_x⟩:=ih (by omega);set g:=d.getD k ⟨GateOp.or,[]⟩;have htk:d.take (k+1)=d.take k ++ [g]:=by{rw[List.take_succ_eq_append_getElem B];dsimp only[g];rw[_lge _ _ B]};have c:(d.take k).length=k:=List.length_take_of_le (by omega);set e:=(d.take k).foldl bO mr;obtain⟨z,j,hga,hgb⟩:=A k B;have n:g.inputs=[g.inputs.getD 0 0,g.inputs.getD 1 0]:=by
    cases I:g.inputs with
    | nil=>rw[I] at j;simp at j
    | cons a l1=>cases l1 with
     | nil=>rw[I] at j;simp at j
     | cons b l2=>cases l2 with
      | nil=>simp
      | cons _ _=>rw[I] at j;simp at j
   have M:=mZ e g k (by rw[c] at ih_rlen;exact ih_rlen) (by rw[c] at ih_glen;exact ih_glen) ih_gsok ih_wlt ih_14 z n;have t:(14∈g.inputs)->e.2.getD (g.inputs.getD 0 0) none=none\/e.2.getD (g.inputs.getD 1 0) none=none:=by{intro U;rw[n] at U;simp only[List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at U;rcases U with N|N;{left;rw[<- N];exact ih_14};{right;rw[<- N];exact ih_14}};rw[htk];simp only[List.length_append,List.length_singleton,c,List.foldl_append,List.foldl_cons,List.foldl_nil];refine⟨M.1,M.2.1,fun hex=>?_,M.2.2.2.2.1,M.2.2.2.2.2.1,M.2.2.2.2.2.2.1,fun p w G R=>?_,fun x=>?_⟩
   · rcases hex with ⟨g',hg',hg14'⟩
     rw[List.mem_append,List.mem_singleton] at hg';rcases hg' with hg'|rfl
     · have N:=ih_g14 ⟨g',hg',hg14'⟩;rw[c] at N
       have X:=M.2.2.1;dsimp only[e] at N X;omega
     · have N:=M.2.2.2.1 (t hg14');rw[N];rw[c] at ih_glen;omega
   · by_cases D:w=15+k
     · subst D
       apply M.2.2.2.2.2.2.2;intro u hu P;have q:=p g (List.mem_append_right _ (List.mem_singleton_self g));rw[n] at q hu;simp only[List.mem_cons,List.mem_singleton,not_or] at q;simp only[List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hu;rcases hu with rfl|rfl
       · obtain⟨_,hs⟩:=ih_all (fun g' hg'=>p g' (List.mem_append_left _ hg')) _ (by rw[c];omega) (Ne.symm q.1)
         rw[hs] at P;contradiction
       · obtain⟨_,hs⟩:=ih_all (fun g' hg'=>p g' (List.mem_append_left _ hg')) _ (by rw[c];omega) (Ne.symm q.2.1)
         rw[hs] at P;contradiction
     · have G':w<e.2.length:=by rw[ih_rlen,c];omega
       obtain⟨w',hwt'⟩:=ih_all (fun g' hg'=>p g' (List.mem_append_left _ hg')) w (by rw[c];omega) R;exact⟨w',(jY e g G').trans hwt'⟩
   · obtain⟨E,K,W⟩:=ih_x x
     set y:=_of x;set h:=(H :: d.take k).foldl _B.cE y;have l:h.length=15+k:=by{dsimp only[h];rw[ir];simp only[y,List.length_ofFn,List.length_cons,c];omega};refine⟨jF e g k y h (by simp[y]) (by rw[c] at ih_rlen;exact ih_rlen) ih_wlt l z n E,fun S=>?_,fun p=>?_⟩
     · obtain⟨h4,he1⟩:=K S
       have hv:=nJ e g k y h (by simp[y]) (by rw[c] at ih_rlen;exact ih_rlen) ih_wlt l z n (by omega) (by omega) E (by rw[c] at h4;exact h4) he1;exact⟨hv.2.1,hv.2.2⟩
     · have p':=fun g' hg'=>p g' (List.mem_append_left _ hg')
       have q:=p g (List.mem_append_right _ (List.mem_singleton_self g));rw[n] at q;simp only[List.mem_cons,List.mem_singleton,not_or] at q;exact jc e g k y h (by simp[y]) (by rw[c] at ih_rlen;exact ih_rlen) ih_wlt l z n (ih_all p' _ (by rw[c];omega) (Ne.symm q.1)) (ih_all p' _ (by rw[c];omega) (Ne.symm q.2.1)) (W p')
 simpa[List.take_length] using Q d.length (le_refl _)
lemma l_meta_7698_main (C:Circuit) (hSize:C.size<=27) (hAO:IsAO2 14 C) (hDist:∀ j<C.size,opnd C j 0≠opnd C j 1) (hFirst:(gateAt C 0).op=GateOp.and) (hFano:∀ x:O->_d,C.eval (_of x)=true↔ ∃ p l:Fin 7,(p=l\/p=l+1\/p=l+3) /\x (Fin.castAdd 7 p)=true/\x (Fin.natAdd 7 l)=true):False:=by
 have hC_pos:0<C.size:=by
  by_contra h0;have h0':C.gates=[]:=List.eq_nil_of_length_eq_zero (by simp only[Circuit.size] at h0;omega);have hval0:∀ x:O->_d,C.eval (_of x)=(_of x).getD C.output false:=fun x=>by{simp[Circuit.eval,Circuit.wires,h0']};by_cases hout:C.output<14
  · have S:=(hFano (fun i=>decide (i.val=C.output))).1 (by
     rw[hval0,_lge _ _ (by simp[hout])];simp only[List.getElem_ofFn,decide_true])
    rcases S with ⟨p,l,-,h1,h2⟩;simp only[decide_eq_true_eq] at h1 h2;have:(Fin.castAdd 7 p).val=(Fin.natAdd 7 l).val:=h1.trans h2.symm;simp[Fin.castAdd,Fin.natAdd] at this;omega
  · have S:=(hFano (fun _=>true)).2 ⟨0,0,Or.inl rfl,rfl,rfl⟩
    rw[hval0,List.getD_eq_default _ _ (by simp;omega)] at S;exact _fnt S
 let G:=bG a_ C;have hC0_size:G.size=C.size:=by simp[G,bG,Circuit.size]
 have N:IsAO2 14 G:=gu a_ hAO;have hC0_dist:∀ j<G.size,opnd G j 0≠opnd G j 1:=gk a_ hDist hAO.2.2;have hC0_len:G.gates.length=C.gates.length:=by simp[G,bG]
 have e:0<G.gates.length:=by rw[hC0_len];exact hC_pos
 have Y:(gateAt G 0).op=GateOp.and:=by{have heq:(gateAt G 0).op=(gateAt C 0).op:=by{rw[gateAt,_lge G.gates _ e,gateAt,_lge C.gates _ hC_pos];simp[G,bG];rfl};rw[heq];exact hFirst};have hC0_hw:∀ y:O->_d,G.eval (_of y)=true↔_B.bw y:=by
  intro y;rw[gj,hFano];constructor
  · rintro⟨a,b,q,ha,hb⟩
    exact⟨a_ (Fin.castAdd 7 a),a_ (Fin.natAdd 7 b),_B.ss a b q,ha,hb⟩
  · rintro⟨u,v,huv,W,X⟩
    obtain⟨a,b,q,ha,hb⟩:=_B.sL u v huv;refine⟨a,b,q,?_,?_⟩;{show y (_B.kW (Fin.castAdd 7 a))=true;rw[ha];exact W};{show y (_B.kW (Fin.natAdd 7 b))=true;rw[hb];exact X}
 have B:(gateAt G 0).inputs.length=2:=N.2.2 _ (by rw[gateAt,_lge G.gates _ e];exact List.getElem_mem e)
 have hu0lt:opnd G 0 0<14:=N.2.1 0 e _ (by
  rw[opnd,_lge _ _ (by rw[B];decide)];exact List.getElem_mem _)
 have hv0lt:opnd G 0 1<14:=N.2.1 0 e _ (by
  rw[opnd,_lge _ _ (by rw[B];decide)];exact List.getElem_mem _)
 let u0:O:=⟨opnd G 0 0,hu0lt⟩;let v0:O:=⟨opnd G 0 1,hv0lt⟩
 obtain⟨f,P,r,E,T,H,m,hC1_07⟩:∃ f:Circuit,f.size<=27/\IsAO2 14 f /\(∀ j<f.size,opnd f j 0≠opnd f j 1) /\(gateAt f 0).op=GateOp.and /\(∀ y:O->_d,f.eval (_of y)=true↔_B.bw y) /\0<f.size /\(∀ h14:opnd f 0 0<14/\opnd f 0 1<14,
  _B.aO ⟨opnd f 0 0,h14.1⟩ ⟨opnd f 0 1,h14.2⟩ ->
  ((opnd f 0 0=0/\opnd f 0 1=7)\/(opnd f 0 0=7/\opnd f 0 1=0))):=by
  by_cases hadj:_B.aO u0 v0
  · obtain⟨p,l,hpl,hdir⟩:=fg u0 v0 hadj
    let τ:_ep (O):=a_.trans ((kZ p l hpl).trans a_);let f:=bG τ G;have hC1_len:f.gates.length=G.gates.length:=by simp[f,bG]
    have P:f.size<=27:=by{change f.gates.length<=27;rw[hC1_len,hC0_len];exact hSize};have r:IsAO2 14 f:=gu τ N;have E:=gk τ hC0_dist N.2.2;have m:0<f.size:=by{change 0<f.gates.length;rw[hC1_len];exact e};have T:(gateAt f 0).op=GateOp.and:=by{have heq:(gateAt f 0).op=(gateAt G 0).op:=by{rw[gateAt,_lge f.gates _ m,gateAt,_lge G.gates _ e];simp[f,bG]};rw[heq];exact Y};have H:∀ y:O->_d,f.eval (_of y)=true↔_B.bw y:=by
     intro y;rw[gj,hC0_hw];have J:∀ w:O,a_ (a_ w)=w:=fun w=>kB w;have hτ_simp:∀ w:O,a_ (τ w)=cQ p l (a_ w):=by{intro w;dsimp only[τ];rw[Equiv.trans_apply,Equiv.trans_apply,J,ff]};have hτ_eq:∀ w:O,τ w=a_ (cQ p l (a_ w)):=by{intro w;dsimp only[τ];rw[Equiv.trans_apply,Equiv.trans_apply,ff]};have hτ:∀ z:O->_d,_B.bw (fun i=>z (τ i))↔_B.bw z:=by
      intro z;have haut:∀ a b:O,_B.aO a b↔_B.aO (τ a) (τ b):=by
       intro a b;have hpm:∀ c d:Fin 7,(c=d\/c=d+1\/c=d+3) ->
        _B.aO (a_ (Fin.castAdd 7 c)) (a_ (Fin.natAdd 7 d)):=by
        intro c d hcd;exact Or.inl (_B.ss c d hcd)
       constructor
       · intro q
         obtain⟨c,d,hcd,(⟨S,hd⟩|⟨S,hd⟩)⟩:=fg a b q
         · obtain⟨c',d',h1,h2,h3⟩:=(fc p l c d hpl).1 hcd
           have hA:=hpm c' d' h3;rw[show a_ (Fin.castAdd 7 c')=τ a by rw[hτ_eq,S,h1],show a_ (Fin.natAdd 7 d')=τ b by rw[hτ_eq,hd,h2]] at hA;exact hA
         · obtain⟨c',d',h1,h2,h3⟩:=(fc p l c d hpl).1 hcd
           have hA:=hpm c' d' h3;rw[show a_ (Fin.castAdd 7 c')=τ b by rw[hτ_eq,S,h1],show a_ (Fin.natAdd 7 d')=τ a by rw[hτ_eq,hd,h2]] at hA;exact hA.symm
       · intro q
         obtain⟨c',d',hcd',(⟨S,hd⟩|⟨S,hd⟩)⟩:=fg (τ a) (τ b) q
         · have K:∀ w:O,(a_ (τ w)).val<7↔(a_ w).val<7:=by
            intro w;rw[hτ_simp];generalize a_ w=zz;by_cases hz:zz.val<7 <;> simp[cQ,hz,Fin.castAdd,Fin.natAdd]<;> omega
           have ha7:(a_ a).val<7:=by rw[<- K a,S];simp[Fin.castAdd]
           have hb7:7<=(a_ b).val:=by
            by_contra hlt;have hlt':(a_ b).val<7:=by omega
            rw[<- K b,hd] at hlt';simp[Fin.natAdd] at hlt'
           let c:Fin 7:=⟨(a_ a).val,ha7⟩;let d:Fin 7:=⟨(a_ b).val - 7,by omega⟩;have hpa:a_ a=Fin.castAdd 7 c:=_fe rfl;have hpb:a_ b=Fin.natAdd 7 d:=_fe (by simp[d];omega);have hcd:=(fc p l c d hpl).2 ⟨c',d',by rw[<- hpa,<-hτ_simp,S],by rw[<- hpb,<-hτ_simp,hd],hcd'⟩;have hA:=hpm c d hcd;rw[<- hpa,<-hpb,J,J] at hA;exact hA
         · have K:∀ w:O,(a_ (τ w)).val<7↔(a_ w).val<7:=by
            intro w;rw[hτ_simp];generalize a_ w=zz;by_cases hz:zz.val<7 <;> simp[cQ,hz,Fin.castAdd,Fin.natAdd]<;> omega
           have hb7:(a_ b).val<7:=by rw[<- K b,S];simp[Fin.castAdd]
           have ha7:7<=(a_ a).val:=by
            by_contra hlt;have hlt':(a_ a).val<7:=by omega
            rw[<- K a,hd] at hlt';simp[Fin.natAdd] at hlt'
           let c:Fin 7:=⟨(a_ b).val,hb7⟩;let d:Fin 7:=⟨(a_ a).val - 7,by omega⟩;have hpb:a_ b=Fin.castAdd 7 c:=_fe rfl;have hpa:a_ a=Fin.natAdd 7 d:=_fe (by simp[d];omega);have hcd:=(fc p l c d hpl).2 ⟨c',d',by rw[<- hpb,<-hτ_simp,S],by rw[<- hpa,<-hτ_simp,hd],hcd'⟩;have hA:=hpm c d hcd;rw[<- hpb,<-hpa,J,J] at hA;exact hA.symm
      rw[_B.ce,_B.ce];constructor;{rintro⟨a,b,q,ha,hb⟩;exact⟨τ a,τ b,(haut a b).1 q,ha,hb⟩};{rintro⟨a,b,q,ha,hb⟩;exact⟨τ.symm a,τ.symm b,(haut _ _).2 (by simpa using q),by simpa using ha,by simpa using hb⟩}
     exact hτ y
    refine⟨f,P,r,E,T,H,m,fun _ _=>?_⟩;have hτ_eq2:∀ w:O,τ w=a_ (cQ p l (a_ w)):=by{intro w;dsimp only[τ];rw[Equiv.trans_apply,Equiv.trans_apply,ff]};have op_eq:∀ b:Fin 2,opnd f 0 b=(τ ⟨opnd G 0 b,by fin_cases b <;> [exact hu0lt;exact hv0lt]⟩).val:=by
     intro b;have hinputs0:G.gates[0].inputs=[opnd G 0 0,opnd G 0 1]:=by
      cases h0:G.gates[0].inputs with
      | nil=>rw[gateAt,_lge G.gates _ e,h0] at B;simp at B
      | cons a l1=>cases l1 with
       | nil=>rw[gateAt,_lge G.gates _ e,h0] at B;simp at B
       | cons b' l2=>cases l2 with
        | nil=>simp only[opnd,gateAt];rw[_lge G.gates _ e,h0];simp
        | cons _ _=>rw[gateAt,_lge G.gates _ e,h0] at B;simp at B
     have hg1:gateAt f 0=⟨G.gates[0].op,[c_ τ (opnd G 0 0),c_ τ (opnd G 0 1)]⟩:=by{rw[gateAt,_lge f.gates _ m];simp only[f,bG,List.getElem_map,hinputs0,List.map_cons,List.map_nil]};fin_cases b
     · change (gateAt f 0).inputs.getD 0 0=(τ ⟨opnd G 0 0,hu0lt⟩).val
       rw[hg1];simp only[List.getD_cons_zero,c_,dif_pos hu0lt]
     · change (gateAt f 0).inputs.getD 1 0=(τ ⟨opnd G 0 1,hv0lt⟩).val
       rw[hg1];simp only[List.getD_cons_succ,List.getD_cons_zero,c_,dif_pos hv0lt]
    have hhits:=kM p l hpl;rcases hdir with ⟨W,X⟩|⟨X,W⟩
    · left;constructor
      · rw[op_eq 0];show(τ u0).val=0;rw[hτ_eq2,W,hhits.1];simp[qJ]
      · rw[op_eq 1];show(τ v0).val=7;rw[hτ_eq2,X,hhits.2];simp[qK]
    · right;constructor
      · rw[op_eq 0];show(τ u0).val=7;rw[hτ_eq2,W,hhits.2];simp[qK]
      · rw[op_eq 1];show(τ v0).val=0;rw[hτ_eq2,X,hhits.1];simp[qJ]
  · exact⟨G,by rw[hC0_size];exact hSize,N,hC0_dist,Y,hC0_hw,by rw[hC0_size];exact hC_pos,fun _ S=>absurd S hadj⟩
 cases A:f.gates with
 | nil=>simp[Circuit.size,A] at m
 | cons g0 rest=>
  have hg0_mem:g0∈f.gates:=by rw[A];exact List.mem_cons_self
  have hg0_op:g0.op=GateOp.and:=by
   have:gateAt f 0=g0:=by simp[gateAt,A]
   rw[<- this];exact T
  have Z:g0.inputs.length=2:=r.2.2 g0 hg0_mem;have hg0_in0:g0.inputs.getD 0 0<14:=by{have h0:=r.2.1 0 (by simp[A]) (g0.inputs.getD 0 0);rw[gateAt,A] at h0;exact h0 (by simp only[List.getD_cons_zero];rw[_lge _ _ (by rw[Z];decide)];exact List.getElem_mem _)};have hg0_in1:g0.inputs.getD 1 0<14:=by{have h0:=r.2.1 0 (by simp[A]) (g0.inputs.getD 1 0);rw[gateAt,A] at h0;exact h0 (by simp only[List.getD_cons_zero];rw[_lge _ _ (by rw[Z];decide)];exact List.getElem_mem _)};let u':O:=⟨g0.inputs.getD 0 0,hg0_in0⟩;let v':O:=⟨g0.inputs.getD 1 0,hg0_in1⟩;have hop_u':opnd f 0 0=u'.val:=by simp[opnd,gateAt,A,u']
  have hop_v':opnd f 0 1=v'.val:=by simp[opnd,gateAt,A,v']
  have hrest_ok:∀ k,k<rest.length ->
   let g:=rest.getD k ⟨GateOp.or,[]⟩
   (g.op=GateOp.and\/g.op=GateOp.or)/\g.inputs.length=2 /\
   g.inputs.getD 0 0<14+1+k/\g.inputs.getD 1 0<14+1+k:=by
   intro k hk;have hk1:k+1<f.gates.length:=by simp[A];omega
   have hgk:gateAt f (k+1)=rest[k]:=by{rw[gateAt,_lge _ _ hk1];simp[A]};have hmem:rest.getD k ⟨GateOp.or,[]⟩∈f.gates:=by{rw[_lge _ _ hk,<-hgk,gateAt,_lge _ _ hk1];exact List.getElem_mem hk1};have hlen2:=r.2.2 _ hmem;have hlen2':(rest[k]).inputs.length=2:=by rw[<- _lge _ _ hk];exact hlen2
   refine⟨r.1 _ hmem,hlen2,?_,?_⟩
   · have h0:=r.2.1 (k+1) hk1 (rest[k].inputs.getD 0 0) (by rw[hgk,_lge _ _ (by rw[hlen2'];decide)];exact List.getElem_mem _)
     rw[_lge _ _ hk];omega
   · have h0:=r.2.1 (k+1) hk1 (rest[k].inputs.getD 1 0) (by rw[hgk,_lge _ _ (by rw[hlen2'];decide)];exact List.getElem_mem _)
     rw[_lge _ _ hk];omega
  obtain⟨er_rlen,er_glen,er_g14,er_gsok,er_wlt,er_14,er_all,er_val⟩:=lS u' v' g0 ⟨hg0_op,Z,rfl,rfl⟩ rest hrest_ok;set st:=rest.foldl bO mr;have h4:u'≠v':=fun h=>E 0 m (by simp[hop_u',hop_v',h]);have hex_edge_all:∀ u v:O,u≠v ->∃ a0 b0:O,_B.ab a0 b0=true/\(a0≠u/\a0≠v\/b0≠u/\b0≠v):=by{decide +kernel};obtain⟨a0,b0,hab0B,hne0⟩:=hex_edge_all u' v' h4;have hab0:_B.aO a0 b0:=(_B.ad a0 b0).1 hab0B;let x0:O->_d:=fun i=>decide (i=a0)||decide (i=b0);have hx0_false:x0 u'=false\/x0 v'=false:=by
   rcases hne0 with ⟨h1,h2⟩|⟨h1,h2⟩
   · by_contra S
     simp only[not_or,_nf,x0,Bool.or_eq_true,decide_eq_true_eq] at S;rcases S with ⟨W|W,X|X⟩;{exact h1 W.symm};{exact h1 W.symm};{exact h2 X.symm};{exact h4 (W.trans X.symm)}
   · by_contra S
     simp only[not_or,_nf,x0,Bool.or_eq_true,decide_eq_true_eq] at S;rcases S with ⟨W|W,X|X⟩;{exact h4 (W.trans X.symm)};{exact h2 X.symm};{exact h1 W.symm};{exact h2 X.symm}
  have hc1_x0:f.eval (_of x0)=true:=(H x0).2 (_B.fn hab0);have h5:((g0 :: rest).foldl _B.cE (_of x0)).getD f.output false=true:=by{dsimp only[Circuit.eval,Circuit.wires] at hc1_x0;rw[A] at hc1_x0;exact hc1_x0};have hout_lt:f.output<15+rest.length:=by{by_contra hge;rw[List.getD_eq_default _ _ (by rw[ir,List.length_ofFn];simp;omega)] at h5;exact _fnt h5};obtain⟨out',hout'⟩:∃ out',st.2.getD f.output none=some out':=by
   cases hr:st.2.getD f.output none with
   | none=>
    have hf:=(er_val x0).2.1 hx0_false |>.1 f.output hout_lt hr;rw[h5] at hf;contradiction
   | some w'=>exact⟨w',rfl⟩
  let D:Circuit:=⟨st.1,out'⟩;have n:Monotone2 D:=er_gsok;have hD_size_26:D.size<=26:=by
   have hlen1:f.gates.length=1+rest.length:=by simp[A];omega
   have hsz:f.gates.length<=27:=P;change st.1.length<=26;omega
  have L:∀ x:O->_d,D.eval (_of x)=((st.1.foldl _B.cE (_of x)).getD out' false):=fun _=>rfl;have I:∀ x:O->_d,f.eval (_of x)=(((g0 :: rest).foldl _B.cE (_of x)).getD f.output false):=by{intro x;dsimp only[Circuit.eval,Circuit.wires];rw[A];rfl};have Q:∀ x:O->_d,D.eval (_of x)=true->_B.bw x:=by{intro x hx;rw[L] at hx;have h1:=(er_val x).1 f.output out' hout' hx;rw[<- I] at h1;exact(H x).1 h1};have hD_agree:∀ x:O->_d,(x u'=false\/x v'=false) ->D.eval (_of x)=f.eval (_of x):=by{intro x huv;rw[L,I];exact(er_val x).2.1 huv |>.2 f.output out' hout'};by_cases h14_read:∃ g∈rest,14∈g.inputs
  · by_cases M:_B.aO u' v'
    · have h07:=hC1_07 ⟨by rw[hop_u'];exact hg0_in0,by rw[hop_v'];exact hg0_in1⟩ (by simpa[u',v',hop_u',hop_v'] using M)
      have hD_size_25:D.size<=25:=by
       have hrest26:rest.length<=26:=by simp[Circuit.size,A] at P;omega
       have:=er_g14 h14_read;simp only[D,Circuit.size];omega
      have hD_g14:∀ x:O->_d,_S.h_ x->D.eval (_of x)=true:=by
       intro x hx;obtain⟨a,b,q,hxa,hxb⟩:=(_S.ek x).1 hx;let px:O->_d:=fun i=>decide (i=a)||decide (i=b);have hne_07:px u'=false\/px v'=false:=by
        by_contra S;simp only[not_or,_nf,px,Bool.or_eq_true,decide_eq_true_eq] at S;have U:u'≠v':=fun h=>E 0 m (by simp[hop_u',hop_v',h]);have ha07:a.val=0/\b.val=7\/a.val=7/\b.val=0:=by
         rcases S with ⟨W|W,X|X⟩;{exfalso;exact U (W.trans X.symm)}
         · rcases h07 with ⟨h1,h2⟩|⟨h1,h2⟩
           · left;exact⟨(congrArg Fin.val W).symm.trans (hop_u'▸h1),(congrArg Fin.val X).symm.trans (hop_v'▸h2)⟩
           · right;exact⟨(congrArg Fin.val W).symm.trans (hop_u'▸h1),(congrArg Fin.val X).symm.trans (hop_v'▸h2)⟩
         · rcases h07 with ⟨h1,h2⟩|⟨h1,h2⟩
           · right;exact⟨(congrArg Fin.val X).symm.trans (hop_v'▸h2),(congrArg Fin.val W).symm.trans (hop_u'▸h1)⟩
           · left;exact⟨(congrArg Fin.val X).symm.trans (hop_v'▸h2),(congrArg Fin.val W).symm.trans (hop_u'▸h1)⟩
         · exfalso;exact U (W.trans X.symm)
        rcases ha07 with ⟨ha0,hb7⟩|⟨ha7,hb0⟩
        · have ha':a=0:=_fe ha0;have hb':b=7:=_fe hb7
          rw[ha',hb'] at q;exact absurd q V
        · have ha':a=7:=_fe ha7;have hb':b=0:=_fe hb0
          rw[ha',hb'] at q;exact absurd q V
       have hpx:D.eval (_of px)=true:=by{rw[hD_agree px hne_07,H];have hstep:∀ u v:O,_S.ac u v=true->_B.ab u v=true:=by{decide +kernel};exact _B.fn ((_B.ad a b).1 (hstep a b ((_S.ae a b).2 q)))};refine fU n px x (fun i hi=>?_) hpx;simp only[px,Bool.or_eq_true,decide_eq_true_eq] at hi;rcases hi with rfl|rfl <;> assumption
      let s07:O->_d:=fun i=>decide (i=0)||decide (i=7);cases h07val:D.eval (_of s07)
      · have hG14_lo:∀ x:O->_d,_S.h_ x->D.eval (_of x)=true:=hD_g14
        have hG14_hi:∀ x:O->_d,D.eval (_of x)=true->_S.bx x:=by{intro x hx;obtain⟨a,b,q,ha,hb⟩:=(_B.ce x).1 (Q x hx);have htrans:∀ u v:O,_B.ab u v=true->_S.bK u v=true:=by{decide +kernel};exact⟨a,b,(_S.cW a b).1 (htrans a b ((_B.ad a b).2 q)),ha,hb⟩};have hG14_pair:∀ u v:O,¬ _S.eW u v ->D.eval (_of (b4 u v))=false:=by
         intro u v huv;by_cases hhw:_B.aO u v
         · have hdec:∀ a b:O,_B.ab a b=true->_S.ac a b=false ->(a=0/\b=7)\/(a=7/\b=0):=by decide +kernel
           have R:=hdec u v ((_B.ad u v).2 hhw) (_S.aH.2 huv);have heq_two:b4 u v=s07:=by{ext i;rcases R with ⟨rfl,rfl⟩|⟨rfl,rfl⟩<;> simp[b4,s07,Bool.or_comm]};rw[heq_two,h07val]
         · by_contra S
           rw[_nf] at S;exact hhw ((_B.iL u v).1 (Q _ S))
        exact _S.g14_umbrella_lb_26 D n hG14_lo hG14_hi hG14_pair hD_size_25
      · have F:∀ x:O->_d,D.eval (_of x)=true↔_B.bw x:=by
         intro x;refine⟨Q x,fun hx=>?_⟩;obtain⟨a,b,q,ha,hb⟩:=(_B.ce x).1 hx;by_cases R:(a=0/\b=7)\/(a=7/\b=0)
         · refine fU n s07 x (fun i hi=>?_) h07val
           simp only[s07,Bool.or_eq_true,decide_eq_true_eq] at hi;rcases R with ⟨rfl,rfl⟩|⟨rfl,rfl⟩<;> rcases hi with rfl|rfl <;> assumption
         · refine fU n (fun i=>decide (i=a)||decide (i=b)) x (fun i hi=>?_) ?_
           · simp only[Bool.or_eq_true,decide_eq_true_eq] at hi;rcases hi with rfl|rfl <;> assumption
           · have hd:∀ u v:O,_B.ab u v=true->¬ ((u=0/\v=7)\/(u=7/\v=0)) ->
              _S.ac u v=true:=by decide +kernel
             exact hD_g14 _ ((_S.ek _).2 ⟨a,b,(_S.ae a b).1 (hd a b ((_B.ad a b).2 q) R),by simp,by simp⟩)
        have:=_B.hV D n F;omega
    · have F:∀ x:O->_d,D.eval (_of x)=true↔_B.bw x:=by
       intro x;refine⟨Q x,fun hx=>?_⟩;obtain⟨a,b,q,ha,hb⟩:=(_B.ce x).1 hx;let px:O->_d:=fun i=>decide (i=a)||decide (i=b);have hne_uv:px u'=false\/px v'=false:=by{by_contra S;simp only[not_or,_nf,px,Bool.or_eq_true,decide_eq_true_eq] at S;have U:u'≠v':=fun h=>E 0 m (by simp[hop_u',hop_v',h]);rcases S with ⟨W|W,X|X⟩;{exact U (W.trans X.symm)};{rw[W,X] at M;exact M q};{rw[W,X] at M;exact M (_B.bl q)};{exact U (W.trans X.symm)}};have hpx:D.eval (_of px)=true:=by{rw[hD_agree px hne_uv,H];exact _B.fn q};refine fU n px x (fun i hi=>?_) hpx;simp only[px,Bool.or_eq_true,decide_eq_true_eq] at hi;rcases hi with rfl|rfl <;> assumption
      have:=_B.hV D n F;omega
  · have hno14:∀ g∈rest,14∉g.inputs:=by
     intro g hg hmem;exact h14_read ⟨g,hg,hmem⟩
    have F:∀ x:O->_d,D.eval (_of x)=true↔_B.bw x:=by{intro x;rw[L,(er_val x).2.2 hno14 f.output out' hout',<-I,H]};have:=_B.hV D n F;omega
end PEqualNP.Outside.L_meta_7698_aux
theorem PEqualNP.Outside.L_meta_7698 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             (∃ x7 < x1.size,                 (0 : ℕ) < x7 ∧                   (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧                     have x8 : List Bool := x1.wires (List.ofFn fun (x8 : Fin (14 : ℕ)) => Decidable.decide (x8 = (0 : Fin (14 : ℕ))));                     have x9 : List Bool := x1.wires (List.ofFn fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = (7 : Fin (14 : ℕ))));                     have x10 : List Bool := x1.wires (List.ofFn fun (x10 : Fin (14 : ℕ)) => Decidable.decide (x10 = (0 : Fin (14 : ℕ)) ∨ x10 = (7 : Fin (14 : ℕ))));                     have x11 : ℕ := PEqualNP.TopForm.opnd x1 x7 (0 : Fin (2 : ℕ));                     have x12 : ℕ := PEqualNP.TopForm.opnd x1 x7 (1 : Fin (2 : ℕ));                     x10.getD x11 Bool.false = Bool.true ∧ x10.getD x12 Bool.false = Bool.true ∧ (x8.getD x11 Bool.false = Bool.false ∧ x8.getD x12 Bool.false = Bool.false ∨ x9.getD x11 Bool.false = Bool.false ∧ x9.getD x12 Bool.false = Bool.false) ∧ (x8.getD x11 Bool.false = Bool.false ∧ x9.getD x11 Bool.false = Bool.false ∨ x8.getD x12 Bool.false = Bool.false ∧ x9.getD x12 Bool.false = Bool.false)) →               False := by
  intro C hSize hAO hDist hFirst hFano _
  exact PEqualNP.Outside.L_meta_7698_aux.l_meta_7698_main C hSize hAO hDist hFirst hFano
