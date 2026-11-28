import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1

/-! Exact generic rank on the two highest dimension-count levels.

Write w=(a-1)(b-1) for the critical third dimension of a complex
a by b by k tensor. Throughout the balanced range with 3≤a≤b≤k≤w,
apart from the known three-by-three-by-three exception, the generic
rank equals the dimension-count prediction whenever that prediction is
w or w+1. In particular, for a=b=n≥4 this proves the highest n-1 third
dimensions, including both distinct rank values.

The uppermost level follows by projecting the boundary construction.
The neighboring level uses two sets of marked points. Their bilinear
normal equations yield a signed coordinate matrix and a Vandermonde
matrix. Independent normal spaces on each of finitely many batches can
be realized at a common specialization. One relation in the last factor
per batch then forces every tensor annihilating the tangent space to vanish.

For lower point counts, symmetry of the generic slices identifies the
full rank increment with surjectivity. The third-factor relations must
detect every nonzero family of bilinear normals. The two remaining tests
treat normal spaces of dimension two and of higher dimension.

Friedland, On the generic and typical ranks of 3-tensors, states the
dimension-count conjecture and proves the critical boundary result.
https://arxiv.org/abs/0805.3777
-/

namespace LastSliceDual

/-- A left-kernel vector is an array of matrix slices. Varying the third factors
makes every slice orthogonal to each rank-one matrix. Varying the first two
factors tests the row and column contractions of one weighted matrix per point. -/
theorem transpose_kernel_iff {K : Type*} [Field K] {a b c r : ℕ}
    (x : Fin r → Fin a → K) (y : Fin r → Fin b → K) (z : Fin r → Fin c → K)
    (G : Matrix ((Fin a × Fin b) × Fin c) (Fin r × (Fin a ⊕ (Fin b ⊕ Fin c))) K)
    (entry : ∀ i j k t v, G ((i,j),k) (t,v) =
      v.elim (fun i' => if i'=i then y t j*z t k else 0)
        (Sum.elim (fun j' => if j'=j then x t i*z t k else 0)
          (fun k' => if k'=k then x t i*y t j else 0)))
    (T : ((Fin a × Fin b) × Fin c) → K) :
    G.transpose.mulVec T = 0 ↔
      let D (t : Fin r) (ij : Fin a × Fin b) := ∑ k, z t k*T (ij,k)
      (∀ k s, ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*T (ij,k) = 0) ∧
      (∀ t i, ∑ j, y t j*D t (i,j) = 0) ∧
      (∀ t j, ∑ i, x t i*D t (i,j) = 0) := by
  classical
  let D (t : Fin r) (ij : Fin a × Fin b) := ∑ k, z t k*T (ij,k)
  have first (t : Fin r) (i : Fin a) : G.transpose.mulVec T (t,.inl i) = ∑ j, y t j*D t (i,j) := by
    change (∑ q : (Fin a × Fin b) × Fin c, G q (t,.inl i)*T q) = _
    simp only [Fintype.sum_prod_type]
    calc
      _ = ∑ l : Fin a, if i=l then ∑ j, y t j*D t (l,j) else 0 := by
        apply Finset.sum_congr rfl
        intro l _
        by_cases h : i=l
        · simp [entry,h,D,Finset.mul_sum,mul_assoc]
        · simp [entry,h]
      _ = _ := by simp
  have second (t : Fin r) (j : Fin b) : G.transpose.mulVec T (t,.inr (.inl j)) = ∑ i, x t i*D t (i,j) := by
    change (∑ q : (Fin a × Fin b) × Fin c, G q (t,.inr (.inl j))*T q) = _
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = ∑ l : Fin b, if j=l then x t i*D t (i,l) else 0 := by
        apply Finset.sum_congr rfl
        intro l _
        by_cases h : j=l
        · simp [entry,h,D,Finset.mul_sum,mul_assoc]
        · simp [entry,h]
      _ = _ := by simp
  have third (s : Fin r) (k : Fin c) : G.transpose.mulVec T (s,.inr (.inr k)) =
      ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*T (ij,k) := by
    change (∑ q : (Fin a × Fin b) × Fin c, G q (s,.inr (.inr k))*T q) = _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    rintro ⟨i,j⟩ _
    simp [entry,ite_mul]
  constructor
  · intro h
    exact ⟨fun k s => (third s k).symm.trans (congrFun h _),
      fun t i => (first t i).symm.trans (congrFun h _),
      fun t j => (second t j).symm.trans (congrFun h _)⟩
  · rintro ⟨outer,row,col⟩
    funext ⟨t,v⟩
    rcases v with v | v | v
    · exact (first t v).trans (row t v)
    · exact (second t v).trans (col t v)
    · exact (third t v).trans (outer v t)

/-- If the sampling vectors span the third factor, vanishing of all slice
pairings is equivalent to vanishing of all their sampled pairings. -/
theorem sampled_outer_iff {K : Type*} [Field K] {a b c r : ℕ}
    (x : Fin r → Fin a → K) (y : Fin r → Fin b → K) (z : Fin r → Fin c → K)
    (hz : Submodule.span K (Set.range z) = ⊤) (T : ((Fin a × Fin b) × Fin c) → K) :
    (∀ k s, ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*T (ij,k) = 0) ↔
      ∀ t s, ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*(∑ k, z t k*T (ij,k)) = 0 := by
  classical
  let pairing (s : Fin r) (k : Fin c) := ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*T (ij,k)
  have interchange (s t : Fin r) :
      ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*(∑ k, z t k*T (ij,k)) = ∑ k, z t k*pairing s k := by
    simp only [pairing,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro ij _
    ring
  constructor
  · intro h t s
    rw [interchange]
    simp [pairing,h]
  · intro h k s
    let U : Submodule K (Fin c → K) := {
      carrier := {v | ∑ l, v l*pairing s l = 0}
      zero_mem' := by simp
      add_mem' := by
        intro v w hv hw
        change (∑ l, v l*pairing s l) = 0 at hv
        change (∑ l, w l*pairing s l) = 0 at hw
        change (∑ l, (v l+w l)*pairing s l) = 0
        simp [add_mul,Finset.sum_add_distrib,hv,hw]
      smul_mem' := by
        intro d v hv
        change (∑ l, v l*pairing s l) = 0 at hv
        change (∑ l, (d*v l)*pairing s l) = 0
        simp only [mul_assoc,← Finset.mul_sum,hv,mul_zero] }
    have contain : Submodule.span K (Set.range z) ≤ U := by
      apply Submodule.span_le.mpr
      rintro _ ⟨t,rfl⟩
      exact (interchange s t).symm.trans (h t s)
    rw [hz] at contain
    have hk := contain (show Pi.single k (1:K) ∈ (⊤ : Submodule K (Fin c → K)) from trivial)
    change (∑ l, (Pi.single k (1:K) : Fin c → K) l*pairing s l) = 0 at hk
    simpa [Pi.single_apply,ite_mul,pairing] using hk

end LastSliceDual

namespace LastSliceBatch

/-- The stacked linear equations consist of all sampled-product conditions,
the two contractions at each marked point, and the unweighted sum of the tuple. -/
theorem stack_injective_iff {K A B S G : Type*} [Field K] [Fintype A] [Fintype B] [Fintype G]
    [DecidableEq A] [DecidableEq B] [DecidableEq G]
    (label : G → S) (x : S → A → K) (y : S → B → K)
    (M : Matrix ((G × (S ⊕ (A ⊕ B))) ⊕ (A × B)) (G × (A × B)) K)
    (entry : ∀ row col, M row col = row.elim
      (fun ge => if col.1=ge.1 then ge.2.elim
        (fun s => x s col.2.1*y s col.2.2)
        (Sum.elim (fun i => if col.2.1=i then y (label ge.1) col.2.2 else 0)
          (fun j => if col.2.2=j then x (label ge.1) col.2.1 else 0)) else 0)
      (fun ij => if col.2=ij then 1 else 0)) :
    Function.Injective M.mulVec ↔
      ∀ H : G → A × B → K, (∀ g s, ∑ ij : A × B, (x s ij.1*y s ij.2)*H g ij=0) →
        (∀ g i, ∑ j, y (label g) j*H g (i,j)=0) →
        (∀ g j, ∑ i, x (label g) i*H g (i,j)=0) → (∑ g, H g)=0 → H=0 := by
  classical
  have outer (H : G → A × B → K) (g : G) (s : S) :
      M.mulVec (Function.uncurry H) (.inl (g,.inl s)) = ∑ ij, (x s ij.1*y s ij.2)*H g ij := by
    change (∑ z : G × (A × B), M (.inl (g,.inl s)) z*H z.1 z.2) = _
    rw [Fintype.sum_prod_type]
    simp [entry,ite_mul,Finset.sum_ite_eq']
  have row₁ (H : G → A × B → K) (g : G) (i : A) :
      M.mulVec (Function.uncurry H) (.inl (g,.inr (.inl i))) = ∑ j, y (label g) j*H g (i,j) := by
    change (∑ z : G × (A × B), M (.inl (g,.inr (.inl i))) z*H z.1 z.2) = _
    simp [Fintype.sum_prod_type,entry,ite_mul,Finset.sum_ite_eq']
  have col₁ (H : G → A × B → K) (g : G) (j : B) :
      M.mulVec (Function.uncurry H) (.inl (g,.inr (.inr j))) = ∑ i, x (label g) i*H g (i,j) := by
    change (∑ z : G × (A × B), M (.inl (g,.inr (.inr j))) z*H z.1 z.2) = _
    simp [Fintype.sum_prod_type,entry,ite_mul,Finset.sum_ite_eq']
  have total (H : G → A × B → K) (ij : A × B) :
      M.mulVec (Function.uncurry H) (.inr ij) = (∑ g, H g) ij := by
    change (∑ z : G × (A × B), M (.inr ij) z*H z.1 z.2) = _
    rw [Fintype.sum_prod_type]
    simp [entry,ite_mul,Finset.sum_apply,Finset.sum_ite_eq']
  constructor
  · intro inject H hp hx hy hz
    have ker : M.mulVec (Function.uncurry H)=0 := by
      funext z
      rcases z with ⟨g,s|i|j⟩|ij
      · exact (outer H g s).trans (hp g s)
      · exact (row₁ H g i).trans (hx g i)
      · exact (col₁ H g j).trans (hy g j)
      · exact (total H ij).trans (congrFun hz ij)
    have he := inject (ker.trans (Matrix.mulVec_zero M).symm)
    exact funext fun g => funext fun ij => congrFun he (g,ij)
  · intro hs
    change Function.Injective M.mulVecLin
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro f hf
    let H : G → A × B → K := Function.curry f
    have eq : M.mulVec (Function.uncurry H) = 0 := hf
    have van := hs H (fun g s => (outer H g s).symm.trans (congrFun eq _))
      (fun g i => (row₁ H g i).symm.trans (congrFun eq _))
      (fun g j => (col₁ H g j).symm.trans (congrFun eq _))
      (funext fun ij => (total H ij).symm.trans (congrFun eq _))
    exact funext fun z => congrFun (congrFun van z.1) z.2

end LastSliceBatch


namespace LastSliceBatch

/-- Any two ordered partial markings of the same finite set extend to a
permutation of the whole point set. -/
theorem permutation_of_markings {G S : Type*} [Fintype G] [Fintype S]
    (first second : G ↪ S) : ∃ e : S ≃ S, ∀ g, e (first g)=second g := by
  classical
  let F := Set.range first
  let T := Set.range second
  let inner : F ≃ T := first.toEquivRange.symm.trans second.toEquivRange
  let outer : (Fᶜ : Set S) ≃ (Tᶜ : Set S) := Fintype.equivOfCardEq (by
    rw [Fintype.card_compl_set,Fintype.card_compl_set,Fintype.card_congr inner])
  let e := (Equiv.Set.sumCompl F).symm.trans ((Equiv.sumCongr inner outer).trans (Equiv.Set.sumCompl T))
  refine ⟨e,fun g => ?_⟩
  have mem : first g ∈ F := ⟨g,rfl⟩
  dsimp only [e,Equiv.trans_apply]
  rw [Equiv.Set.sumCompl_symm_apply_of_mem mem]
  change ((second.toEquivRange (first.toEquivRange.symm (first.toEquivRange g)) : T) : S) = second g
  rw [Equiv.symm_apply_apply]
  rfl

end LastSliceBatch


namespace LastSliceBatch

open MvPolynomial

/-- A left inverse at one point gives a polynomial sufficient for injectivity at other points. -/
private lemma injectivity_polynomial {I J V : Type*} [Fintype I] [Fintype J]
    (M : Matrix I J (MvPolynomial V ℂ)) (p : V → ℂ) (hi : Function.Injective (M.map (eval p)).mulVec) :
    ∃ Q : MvPolynomial V ℂ, Q≠0 ∧ ∀ u : V → ℂ, eval u Q≠0 → Function.Injective (M.map (eval u)).mulVec := by
  classical
  let A := M.map (eval p)
  obtain ⟨L,hL⟩ := A.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
  let B := LinearMap.toMatrix' L
  have left : B*A=1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul,Matrix.toLin'_one]
    change (Matrix.toLin' (LinearMap.toMatrix' L)).comp A.mulVecLin=LinearMap.id
    rw [Matrix.toLin'_toMatrix']
    exact hL
  let P := B.map (MvPolynomial.C : ℂ →+* MvPolynomial V ℂ)
  have spec (u : V → ℂ) : eval u (P*M).det = (B*M.map (eval u)).det := by
    have hP : P.map (eval u)=B := by ext; simp [P,Matrix.map_apply]
    rw [RingHom.map_det,RingHom.mapMatrix_apply,Matrix.map_mul,hP]
  have one : eval p (P*M).det=1 := (spec p).trans ((congrArg Matrix.det left).trans Matrix.det_one)
  refine ⟨(P*M).det,fun h => zero_ne_one (by simpa only [h,map_zero] using one),?_⟩
  intro u hu
  have nz : (B*M.map (eval u)).det≠0 := (spec u) ▸ hu
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr nz))
  intro x y he
  apply hinj
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,he]

/-- A finite family of injectivity conditions on a common parameter space holds simultaneously
when each is realized separately. Both matrix index types may depend on the family member. -/
lemma common_injective {G V : Type*} [Fintype G] {U W : G → Type*}
    [∀ g,Fintype (U g)] [∀ g,Fintype (W g)]
    (M : ∀ g,Matrix (U g) (W g) (MvPolynomial V ℂ))
    (h : ∀ g, ∃ u : V → ℂ, Function.Injective ((M g).map (eval u)).mulVec) :
    ∃ u : V → ℂ, ∀ g,Function.Injective ((M g).map (eval u)).mulVec := by
  classical
  choose u hu using h
  choose Q hn hgood using fun g => injectivity_polynomial (M g) (u g) (hu g)
  have hprod : (∏ g,Q g)≠0 := Finset.prod_ne_zero_iff.mpr fun g _ => hn g
  obtain ⟨z,hz⟩ : ∃ z : V → ℂ,eval z (∏ g,Q g)≠0 := by
    by_contra! he
    exact hprod (MvPolynomial.funext fun z => by rw [he z,map_zero])
  have hval : (∏ g, eval z (Q g))≠0 := by simpa only [map_prod] using hz
  exact ⟨z,fun g => hgood g z (Finset.prod_ne_zero_iff.mp hval g (Finset.mem_univ g))⟩

end LastSliceBatch


namespace LastSliceBatch

open MvPolynomial

/-- One independent ordered marking gives common complex factors that work for
every ordered marking of the same size. All use the same sampled outer products. -/
theorem common_markings {A B P Q : Type*} [Fintype A] [Fintype B] [Fintype P] [Fintype Q]
    (first : Q ↪ P) (one : ∃ x : P → A → ℂ, ∃ y : P → B → ℂ, ∀ H : Q → A×B → ℂ,
      (∀ t s, (∑ ij : A×B, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (first t) j*H t (i,j))=0) → (∀ t j, (∑ i, x (first t) i*H t (i,j))=0) →
      (∑ t,H t)=0 → H=0) :
    ∃ x : P → A → ℂ, ∃ y : P → B → ℂ, ∀ e : Q ↪ P, ∀ H : Q → A×B → ℂ,
      (∀ t s, (∑ ij : A×B, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (e t) j*H t (i,j))=0) → (∀ t j, (∑ i, x (e t) i*H t (i,j))=0) →
      (∑ t,H t)=0 → H=0 := by
  classical
  let V := P × (A ⊕ B)
  let Row := (Q × (P ⊕ (A ⊕ B))) ⊕ (A × B)
  let Col := Q × (A × B)
  let M (e : Q ↪ P) : Matrix Row Col (MvPolynomial V ℂ) := fun row col => row.elim
    (fun te => if col.1=te.1 then te.2.elim
      (fun s => X (s,.inl col.2.1)*X (s,.inr col.2.2))
      (Sum.elim (fun i => if col.2.1=i then X (e te.1,.inr col.2.2) else 0)
        (fun j => if col.2.2=j then X (e te.1,.inl col.2.1) else 0)) else 0)
    (fun ij => if col.2=ij then 1 else 0)
  let D (x : P → A → ℂ) (y : P → B → ℂ) (e : Q ↪ P) : Prop := ∀ H : Q → A×B → ℂ,
      (∀ t s, (∑ ij : A×B, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (e t) j*H t (i,j))=0) → (∀ t j, (∑ i, x (e t) i*H t (i,j))=0) →
      (∑ t,H t)=0 → H=0
  have action (e : Q ↪ P) (p : V → ℂ) : Function.Injective ((M e).map (eval p)).mulVec ↔
      D (fun s i => p (s,.inl i)) (fun s j => p (s,.inr j)) e := by
    apply stack_injective_iff e (fun s i => p (s,.inl i)) (fun s j => p (s,.inr j))
    intro row col
    change eval p (M e row col) = _
    rcases row with ⟨t,s|i|j⟩|ij <;> rcases col with ⟨l,u,v⟩
    · by_cases ht : l=t <;> simp [M,ht]
    · by_cases ht : l=t <;> by_cases hi : u=i <;> simp [M,ht,hi]
    · by_cases ht : l=t <;> by_cases hj : v=j <;> simp [M,ht,hj]
    · by_cases he : (u,v)=ij <;> simp [M,he]
  obtain ⟨x₀,y₀,h₀⟩ := one
  have each (e : Q ↪ P) : ∃ p : V → ℂ, Function.Injective ((M e).map (eval p)).mulVec := by
    obtain ⟨σ,hσ⟩ := permutation_of_markings e first
    let p (z : V) := z.2.elim (x₀ (σ z.1)) (y₀ (σ z.1))
    refine ⟨p,(action e p).mpr ?_⟩
    intro H outer row col
    apply h₀ H
    · intro t s
      obtain ⟨s,rfl⟩ := σ.surjective s
      exact outer t s
    · simpa only [p,Sum.elim_inr,hσ] using row
    · simpa only [p,Sum.elim_inl,hσ] using col
  obtain ⟨p,hp⟩ := common_injective (U:=fun _ : Q ↪ P => Row) (W:=fun _ => Col) M each
  exact ⟨fun s i => p (s,.inl i),fun s j => p (s,.inr j),fun e => (action e p).mp (hp e)⟩

/-- Restrict a direct family along an embedding by extending the smaller
tuple by zero on the complement. -/
private lemma restrict_marking {A B P Q T : Type*} [Fintype A] [Fintype B] [Fintype Q] [Fintype T]
    (x : P → A → ℂ) (y : P → B → ℂ) (e : Q ↪ P) (f : T ↪ Q)
    (direct : ∀ H : Q → A×B → ℂ,
      (∀ t s, (∑ ij : A×B, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (e t) j*H t (i,j))=0) → (∀ t j, (∑ i, x (e t) i*H t (i,j))=0) →
      (∑ t,H t)=0 → H=0) : ∀ H : T → A×B → ℂ,
      (∀ t s, (∑ ij : A×B, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (e (f t)) j*H t (i,j))=0) → (∀ t j, (∑ i, x (e (f t)) i*H t (i,j))=0) →
      (∑ t,H t)=0 → H=0 := by
  classical
  let C := (Set.range f)ᶜ
  let q : T ⊕ C ≃ Q := (Equiv.sumCongr f.toEquivRange (Equiv.refl C)).trans (Equiv.Set.sumCompl _)
  have ql (t : T) : q (.inl t)=f t := rfl
  intro H outer row col total
  let F (s : Q) : A × B → ℂ := (q.symm s).elim H (fun _ => 0)
  have fl (t : T) : F (q (.inl t))=H t := by simp only [F,Equiv.symm_apply_apply,Sum.elim_inl]
  have fr (t : C) : F (q (.inr t))=0 := by simp only [F,Equiv.symm_apply_apply,Sum.elim_inr]
  have outer' (t : Q) (s : P) : ∑ ij : A×B, (x s ij.1*y s ij.2)*F t ij=0 := by
    obtain ⟨t|t,rfl⟩ := q.surjective t
    · rw [fl]
      exact outer t s
    · simp [fr]
  have row' (t : Q) (i : A) : (∑ j, y (e t) j*F t (i,j))=0 := by
    obtain ⟨t|t,rfl⟩ := q.surjective t
    · rw [fl,ql]
      exact row t i
    · simp [fr]
  have col' (t : Q) (j : B) : (∑ i, x (e t) i*F t (i,j))=0 := by
    obtain ⟨t|t,rfl⟩ := q.surjective t
    · rw [fl,ql]
      exact col t j
    · simp [fr]
  have all_sum : ∑ t,F t=0 := by
    rw [←q.sum_comp F,Fintype.sum_sum_type]
    simpa only [fl,fr,Finset.sum_const_zero,add_zero] using total
  have zero := direct F outer' row' col' all_sum
  funext t ij
  exact congrFun ((fl t).symm.trans (congrFun zero (q (.inl t)))) ij

/-- Once every maximal marking works at the same factors, so does every
smaller injection. A permutation extends each such injection to a maximal one. -/
private lemma smaller_marking {A B P Q T : Type*} [Fintype A] [Fintype B] [Fintype P] [Fintype Q]
    [Fintype T] (x : P → A → ℂ) (y : P → B → ℂ) (first : Q ↪ P) (label : T ↪ P)
    (size : Fintype.card T ≤ Fintype.card Q) (good : ∀ e : Q ↪ P, ∀ H : Q → A×B → ℂ,
      (∀ t s, (∑ ij : A×B, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (e t) j*H t (i,j))=0) → (∀ t j, (∑ i, x (e t) i*H t (i,j))=0) →
      (∑ t,H t)=0 → H=0) : ∀ H : T → A×B → ℂ,
      (∀ t s, (∑ ij : A×B, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (label t) j*H t (i,j))=0) → (∀ t j, (∑ i, x (label t) i*H t (i,j))=0) →
      (∑ t,H t)=0 → H=0 := by
  classical
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le size
  obtain ⟨σ,hσ⟩ := permutation_of_markings (f.trans first) label
  let e := first.trans σ.toEmbedding
  have agree (t : T) : e (f t)=label t := hσ t
  intro H outer row col total
  apply restrict_marking x y e f (good e) H outer
  · simpa only [agree] using row
  · simpa only [agree] using col
  · exact total

/-- Ragged color classes may have different cardinalities, including zero.
The same factors give independent normal spaces in every color class. -/
theorem common_small_fibers {A B P Q D : Type*} [Fintype A] [Fintype B] [Fintype P] [Fintype Q]
    [DecidableEq D] (first : Q ↪ P) (label : P → D)
    (cap : ∀ g, Fintype.card {t : P // label t=g} ≤ Fintype.card Q) (one : ∃ x : P → A → ℂ, ∃ y : P → B → ℂ, ∀ H : Q → A×B → ℂ,
      (∀ t s, (∑ ij : A×B, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (first t) j*H t (i,j))=0) → (∀ t j, (∑ i, x (first t) i*H t (i,j))=0) →
      (∑ t,H t)=0 → H=0) :
    ∃ x : P → A → ℂ, ∃ y : P → B → ℂ, ∀ g : D, ∀ H : {t : P // label t=g} → A×B → ℂ,
      (∀ t s, (∑ ij : A×B, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (t.val) j*H t (i,j))=0) → (∀ t j, (∑ i, x (t.val) i*H t (i,j))=0) →
      (∑ t,H t)=0 → H=0 := by
  classical
  obtain ⟨x,y,good⟩ := common_markings first one
  exact ⟨x,y,fun g => smaller_marking x y first (Function.Embedding.subtype (fun t => label t=g)) (cap g) good⟩

end LastSliceBatch

namespace LastSliceBatch

/-- Annihilators of the image of a matrix are its row relations. -/
private lemma ragged_surj_of_no_relation {K R C : Type*} [Field K] [Fintype R] [Fintype C]
    (M : Matrix R C K) (h : ∀ u : R → K, M.transpose.mulVec u=0 → u=0) :
    Function.Surjective M.mulVec := by
  classical
  have hk : LinearMap.ker M.transpose.mulVecLin = ⊥ := by
    apply bot_unique
    intro u hu
    exact (Submodule.mem_bot K).mpr (h u hu)
  have he := LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hk)
  change M.transpose.rank = Module.finrank K (R → K) at he
  rw [Matrix.rank_transpose] at he
  change Function.Surjective M.mulVecLin
  apply LinearMap.range_eq_top.mp
  exact Submodule.eq_top_of_finrank_eq he

private lemma indicator_sum {K P G : Type*} [Field K] [Fintype P] [DecidableEq G] [DecidableEq P]
    (label : P → G) (g : G) (p : P) :
    (∑ t : {t : P // label t=g}, if t.val=p then (1 : K) else 0) =
      if label p=g then 1 else 0 := by
  by_cases h : label p=g
  · let v : {t : P // label t=g} := ⟨p,h⟩
    have e (t : {t : P // label t=g}) : t.val=p ↔ t=v :=
      ⟨fun ht => Subtype.ext ht,fun ht => congrArg Subtype.val ht⟩
    simp [h,e]
  · have e (t : {t : P // label t=g}) : t.val≠p := fun ht => h (ht ▸ t.property)
    simp [h,e]

/-- Independent normal tuples on the fibers give a tangent witness. One point
in each fiber is the negative sum of that fiber's other coordinate vectors. -/
theorem spans_of_ragged_independence {K P G : Type*} [Field K] [Fintype P] [Fintype G]
    [DecidableEq G] {a b : ℕ} (label : P → G) (onto : Function.Surjective label)
    (x : P → Fin a → K) (y : P → Fin b → K)
    (independent : ∀ g : G, ∀ H : {t : P // label t=g} → (Fin a × Fin b) → K,
      (∀ t s, ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*H t ij = 0) →
      (∀ t i, ∑ j,y t.val j*H t (i,j)=0) →
      (∀ t j, ∑ i,x t.val i*H t (i,j)=0) →
      (∑ t,H t)=0 → H=0) :
    ∃ X : Fin (Fintype.card P) → Fin a → K, ∃ Y : Fin (Fintype.card P) → Fin b → K,
    ∃ Z : Fin (Fintype.card P) → Fin (Fintype.card P-Fintype.card G) → K,
      ∀ T : Fin a → Fin b → Fin (Fintype.card P-Fintype.card G) → K,
      ∃ u : Fin (Fintype.card P) → Fin a → K, ∃ v : Fin (Fintype.card P) → Fin b → K,
      ∃ w : Fin (Fintype.card P) → Fin (Fintype.card P-Fintype.card G) → K, ∀ i j k, T i j k =
        ∑ t, (u t i*(Y t j*Z t k) + X t i*(v t j*Z t k) + X t i*(Y t j*w t k)) := by
  classical
  choose pivot right using onto
  let Free := {p : P // p ≠ pivot (label p)}
  let split : G ⊕ Free ≃ P :=
    { toFun := Sum.elim pivot Subtype.val
      invFun := fun p => if h : p=pivot (label p) then .inl (label p) else .inr ⟨p,h⟩
      left_inv := by
        rintro (g|⟨p,h⟩)
        · simp [right]
        · simp [h]
      right_inv := by
        intro p
        by_cases hp : p=pivot (label p)
        · simpa only [dif_pos hp,Sum.elim_inl] using hp.symm
        · simp only [dif_neg hp,Sum.elim_inr] }
  have count : Fintype.card Free=Fintype.card P-Fintype.card G := by
    have size := Fintype.card_congr split
    rw [Fintype.card_sum] at size
    omega
  let E : P ≃ Fin (Fintype.card P) := Fintype.equivFin P
  let F : Free ≃ Fin (Fintype.card P-Fintype.card G) := (Fintype.equivFin Free).trans (finCongr count)
  let X (s : Fin (Fintype.card P)) := x (E.symm s)
  let Y (s : Fin (Fintype.card P)) := y (E.symm s)
  let Z (s : Fin (Fintype.card P)) (k : Fin (Fintype.card P-Fintype.card G)) : K :=
    (if E.symm s=(F.symm k).val then 1 else 0) -
      (if E.symm s=pivot (label (F.symm k).val) then 1 else 0)
  have away (p : Free) (g : G) : p.val≠pivot g := by
    intro eq
    apply p.property
    have h : label p.val=g := eq ▸ right g
    rwa [h]
  have basisValue (p : Free) (k : Fin (Fintype.card P-Fintype.card G)) :
      Z (E p.val) k = if F p=k then 1 else 0 := by
    obtain ⟨q,rfl⟩ := F.surjective k
    have eq : p.val=q.val ↔ p=q := ⟨Subtype.ext,congrArg Subtype.val⟩
    simp only [Z,Equiv.symm_apply_apply,if_neg (away p _),sub_zero,Equiv.apply_eq_iff_eq,eq]
  have batchSum (g : G) (k : Fin (Fintype.card P-Fintype.card G)) :
      (∑ t : {p : P // label p=g}, Z (E t.val) k)=0 := by
    simp only [Z,Equiv.symm_apply_apply,Finset.sum_sub_distrib,indicator_sum,right,sub_self]
  let V := Fin (Fintype.card P) × (Fin a ⊕ (Fin b ⊕ Fin (Fintype.card P-Fintype.card G)))
  let M : Matrix ((Fin a × Fin b) × Fin (Fintype.card P-Fintype.card G)) V K := fun row col =>
    col.2.elim (fun i' => if i'=row.1.1 then Y col.1 row.1.2*Z col.1 row.2 else 0)
      (Sum.elim (fun j' => if j'=row.1.2 then X col.1 row.1.1*Z col.1 row.2 else 0)
        (fun k' => if k'=row.2 then X col.1 row.1.1*Y col.1 row.1.2 else 0))
  have full : Function.Surjective M.mulVec := by
    apply ragged_surj_of_no_relation
    intro T ht
    let D (s : P) (ij : Fin a × Fin b) := ∑ k,Z (E s) k*T (ij,k)
    obtain ⟨hout,hrow,hcol⟩ := (LastSliceDual.transpose_kernel_iff X Y Z M (fun _ _ _ _ _ => rfl) T).mp ht
    have outer (k : Fin (Fintype.card P-Fintype.card G)) (s : P) :
        (∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*T (ij,k))=0 := by
      simpa only [X,Y,Equiv.symm_apply_apply] using hout k (E s)
    have zero (g : G) : (fun t : {p : P // label p=g} => D t.val)=0 := by
      apply independent g
      · intro t s
        calc
          _ = ∑ k, Z (E t.val) k * (∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*T (ij,k)) := by
            simp only [D,Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k _
            apply Finset.sum_congr rfl
            intro ij _
            ring
          _ = 0 := by simp [outer]
      · intro t i
        simpa only [D,Y,Equiv.symm_apply_apply] using hrow (E t.val) i
      · intro t j
        simpa only [D,X,Equiv.symm_apply_apply] using hcol (E t.val) j
      · funext ij
        simp only [Finset.sum_apply,D,Pi.zero_apply]
        rw [Finset.sum_comm]
        simp only [← Finset.sum_mul,batchSum,zero_mul,Finset.sum_const_zero]
    funext ⟨ij,k⟩
    obtain ⟨p,rfl⟩ := F.surjective k
    have hh := congrFun (congrFun (zero (label p.val)) ⟨p.val,rfl⟩) ij
    simpa [D,basisValue,ite_mul,Finset.sum_ite_eq] using hh
  refine ⟨X,Y,Z,?_⟩
  intro T
  obtain ⟨z,hz⟩ := full fun q => T q.1.1 q.1.2 q.2
  refine ⟨fun t i => z (t,.inl i),fun t j => z (t,.inr (.inl j)),fun t k => z (t,.inr (.inr k)),?_⟩
  intro i j k
  refine (congrFun hz ((i,j),k)).symm.trans ?_
  change (∑ v : V, M ((i,j),k) v*z v)=_
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp [M,ite_mul,Finset.sum_ite_eq']
  ring

/-- Reduction modulo s distributes r points into s nonempty fibers of size
at most m whenever the available capacity s*m is at least r. -/
theorem balanced_partition {r s m : ℕ} (hs : s ≤ r) (hcap : r ≤ s*m) :
    ∃ label : Fin r → Fin s, Function.Surjective label ∧
      ∀ g, Fintype.card {p : Fin r // label p=g} ≤ m := by
  by_cases h0 : s=0
  · subst s
    obtain rfl : r=0 := by simpa using hcap
    exact ⟨id,Function.surjective_id,fun g => g.elim0⟩
  · have spos : 0 < s := Nat.pos_of_ne_zero h0
    let label (p : Fin r) : Fin s := ⟨p.val%s,Nat.mod_lt _ spos⟩
    refine ⟨label,?_,?_⟩
    · intro g
      refine ⟨⟨g.val,g.isLt.trans_le hs⟩,Fin.ext (Nat.mod_eq_of_lt g.isLt)⟩
    · intro g
      let encode (v : {p : Fin r // label p=g}) : Fin m :=
        ⟨v.val.val/s,(Nat.div_lt_iff_lt_mul spos).mpr (by simpa only [Nat.mul_comm m s] using v.val.isLt.trans_le hcap)⟩
      have inj : Function.Injective encode := by
        intro u v he
        have hq : u.val.val/s=v.val.val/s := congrArg Fin.val he
        have hr : u.val.val%s=v.val.val%s := (congrArg Fin.val u.property).trans (congrArg Fin.val v.property).symm
        apply Subtype.ext
        apply Fin.ext
        calc
          _ = s*(u.val.val/s)+u.val.val%s := (Nat.div_add_mod u.val.val s).symm
          _ = s*(v.val.val/s)+v.val.val%s := by rw [hq,hr]
          _ = _ := Nat.div_add_mod v.val.val s
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective encode inj

end LastSliceBatch

namespace LastSlicePositive

/-- Transport a marked collection of independent normal spaces through
bijections on the total points and both matrix axes. -/
private lemma move_mark {A B P Q A' B' P' : Type*}
    [Fintype A] [Fintype B] [Fintype A'] [Fintype B'] [Fintype Q]
    (ea : A ≃ A') (eb : B ≃ B') (ep : P ≃ P') (first : Q ↪ P)
    (one : ∃ x : P → A → ℂ, ∃ y : P → B → ℂ, ∀ H : Q → A × B → ℂ,
      (∀ t s, ∑ ij : A × B, (x s ij.1*y s ij.2)*H t ij=0) →
      (∀ t i, ∑ j, y (first t) j*H t (i,j)=0) →
      (∀ t j, ∑ i, x (first t) i*H t (i,j)=0) → (∑ t, H t)=0 → H=0) :
    ∃ X : P' → A' → ℂ, ∃ Y : P' → B' → ℂ, ∀ H : Q → A' × B' → ℂ,
      (∀ t s, ∑ ij : A' × B', (X s ij.1*Y s ij.2)*H t ij=0) →
      (∀ t i, ∑ j, Y (ep (first t)) j*H t (i,j)=0) →
      (∀ t j, ∑ i, X (ep (first t)) i*H t (i,j)=0) → (∑ t, H t)=0 → H=0 := by
  classical
  obtain ⟨x,y,ind⟩ := one
  let X (s : P') (i : A') := x (ep.symm s) (ea.symm i)
  let Y (s : P') (j : B') := y (ep.symm s) (eb.symm j)
  refine ⟨X,Y,?_⟩
  intro H outer row col total
  let pull (t : Q) (ij : A × B) := H t (ea ij.1,eb ij.2)
  have out (t : Q) (s : P) : ∑ ij : A × B, (x s ij.1*y s ij.2)*pull t ij=0 := by
    have h := outer t (ep s)
    rw [← (ea.prodCongr eb).sum_comp] at h
    simpa only [pull,X,Y,Equiv.prodCongr_apply,Prod.map,Equiv.symm_apply_apply] using h
  have rows (t : Q) (i : A) : ∑ j, y (first t) j*pull t (i,j)=0 := by
    have h := row t (ea i)
    rw [← eb.sum_comp] at h
    simpa only [pull,Y,Equiv.symm_apply_apply] using h
  have cols (t : Q) (j : B) : ∑ i, x (first t) i*pull t (i,j)=0 := by
    have h := col t (eb j)
    rw [← ea.sum_comp] at h
    simpa only [pull,X,Equiv.symm_apply_apply] using h
  have trace : ∑ t, pull t=0 := by
    funext ij
    simpa only [Finset.sum_apply,pull,Pi.zero_apply] using congrFun total (ea ij.1,eb ij.2)
  have zero := ind pull out rows cols trace
  funext t ij
  simpa only [pull,Equiv.apply_symm_apply,Prod.mk.eta,Pi.zero_apply] using
    congrFun (congrFun zero t) (ea.symm ij.1,eb.symm ij.2)

end LastSlicePositive

namespace LastSlicePositive

/-- A marked independent family of size m permits w points to span whenever
the w−c batches can be chosen with at most m points apiece. -/
private lemma from_capacity {a b w c m : ℕ} {Q : Type*} [Fintype Q]
    (hq : Fintype.card Q=m) (first : Q ↪ Fin w) (hc : c≤w) (fit : w≤(w-c)*m)
    (one : ∃ x : Fin w → Fin a → ℂ, ∃ y : Fin w → Fin b → ℂ, ∀ H : Q → Fin a × Fin b → ℂ,
      (∀ t s, ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*H t ij=0) →
      (∀ t i, ∑ j, y (first t) j*H t (i,j)=0) →
      (∀ t j, ∑ i, x (first t) i*H t (i,j)=0) → (∑ t,H t)=0 → H=0) :
    ∃ x : Fin w → Fin a → ℂ, ∃ y : Fin w → Fin b → ℂ, ∃ z : Fin w → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin w → Fin a → ℂ,
        ∃ v : Fin w → Fin b → ℂ, ∃ v' : Fin w → Fin c → ℂ, ∀ i j k,
          T i j k=∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*v' t k)) := by
  classical
  obtain ⟨label,onto,bound⟩ := LastSliceBatch.balanced_partition (Nat.sub_le w c) fit
  have cap (g : Fin (w-c)) : Fintype.card {t : Fin w // label t=g} ≤ Fintype.card Q := hq ▸ bound g
  obtain ⟨x,y,direct⟩ := LastSliceBatch.common_small_fibers first label cap one
  have result := LastSliceBatch.spans_of_ragged_independence label onto x y direct
  rw [Fintype.card_fin w,Fintype.card_fin (w-c),show w-(w-c)=c by omega] at result
  exact result

end LastSlicePositive

namespace LastSliceTwo

/-- Two marked labels per group have the same moment-curve vector in the last column.
Their coordinates in the old columns distinguish the two types. For both types the
third entry in the last column determines the full normal. -/
lemma exists_two_formulas (A B : ℕ) :
    ∃ x : (Fin B × (Fin 2 ⊕ Fin A)) → (Fin 3 ⊕ Fin A) → ℂ,
    ∃ y : (Fin B × (Fin 2 ⊕ Fin A)) → Option (Fin B) → ℂ,
    ∀ (i : Fin B) (v : Fin 2) (H : (Fin 3 ⊕ Fin A) × Option (Fin B) → ℂ),
      (∀ t, ∑ ij, (x t ij.1*y t ij.2)*H ij=0) →
      (∀ u, ∑ k, y (i,.inl v) k*H (u,k)=0) →
      (∀ k, ∑ u, x (i,.inl v) u*H (u,k)=0) →
      let s := H (.inl 2,none)
      (∀ u : Fin 3 ⊕ Fin A, H (u,none) = s * u.elim ![(i.val:ℂ)^2,-2*(i.val:ℂ),1]
        (fun l => (i.val:ℂ)^(l.val+3))) ∧
      (∀ j, H (.inl 2,some j) = if v=0 then (if i=j then -s else s) else 0) ∧ (s=0 → H=0) := by
  let lam : Fin 2 ⊕ Fin A → ℂ := Sum.elim (fun v => if v=0 then 1 else 0) (fun _ => 2)
  let x (p : Fin B × (Fin 2 ⊕ Fin A)) : (Fin 3 ⊕ Fin A) → ℂ :=
    match p.2 with
    | .inl v => Sum.elim (if v=0 then ![1,(p.1.val:ℂ),(p.1.val:ℂ)^2] else ![0,1,2*(p.1.val:ℂ)]) 0
    | .inr l => Sum.elim ![0,0,-(p.1.val:ℂ)^(l.val+3)] (fun u => if u=l then 1 else 0)
  let y (p : Fin B × (Fin 2 ⊕ Fin A)) : Option (Fin B) → ℂ := fun
    | none => lam p.2
    | some j => if j=p.1 then 1 else 0
  have second_action (p : Fin B × (Fin 2 ⊕ Fin A)) (w : Option (Fin B) → ℂ) :
      (∑ k, y p k*w k) = lam p.2*w none + w (some p.1) := by
    rw [Fintype.sum_option]
    simp [y,ite_mul,Finset.sum_ite_eq']
  have product_action (p : Fin B × (Fin 2 ⊕ Fin A)) (H : (Fin 3 ⊕ Fin A) × Option (Fin B) → ℂ) :
      (∑ ij, (x p ij.1*y p ij.2)*H ij) = ∑ u, x p u*(lam p.2*H (u,none)+H (u,some p.1)) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro u _
    rw [← second_action p (fun k => H (u,k)),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have first_action (j : Fin B) (w : (Fin 3 ⊕ Fin A) → ℂ) : (∑ u, x (j,.inl 0) u*w u) =
      w (.inl 0)+(j.val:ℂ)*w (.inl 1)+(j.val:ℂ)^2*w (.inl 2) := by
    simp [Fintype.sum_sum_type,Fin.sum_univ_three,x,Matrix.cons_val_two]
  have slope_action (j : Fin B) (w : (Fin 3 ⊕ Fin A) → ℂ) : (∑ u, x (j,.inl 1) u*w u) =
      w (.inl 1)+2*(j.val:ℂ)*w (.inl 2) := by
    simp [Fintype.sum_sum_type,Fin.sum_univ_three,x,Matrix.cons_val_two]
  have extra_action (j : Fin B) (l : Fin A) (w : (Fin 3 ⊕ Fin A) → ℂ) : (∑ u, x (j,.inr l) u*w u) =
      w (.inr l)-(j.val:ℂ)^(l.val+3)*w (.inl 2) := by
    simp [Fintype.sum_sum_type,Fin.sum_univ_three,x,Matrix.cons_val_two,ite_mul,Finset.sum_ite_eq']
    ring
  refine ⟨x,y,?_⟩
  intro i v H prod row col s
  let I : ℂ := i.val
  have selected (u : Fin 3 ⊕ Fin A) : (if v=0 then (1:ℂ) else 0)*H (u,none)+H (u,some i)=0 :=
    (second_action (i,.inl v) (fun k => H (u,k))).symm.trans (row u)
  have Xarm (hv : v=0) (k : Option (Fin B)) : H (.inl 0,k)+I*H (.inl 1,k)+I^2*H (.inl 2,k)=0 := by
    subst v
    exact (first_action i (fun u => H (u,k))).symm.trans (col k)
  have Darm (hv : v≠0) (k : Option (Fin B)) : H (.inl 1,k)+2*I*H (.inl 2,k)=0 := by
    have hv' : v=1 := by fin_cases v <;> simp_all
    subst v
    exact (slope_action i (fun u => H (u,k))).symm.trans (col k)
  have anchor (j : Fin B) : (H (.inl 0,none)+H (.inl 0,some j)) +
      (j.val:ℂ)*(H (.inl 1,none)+H (.inl 1,some j)) +
      (j.val:ℂ)^2*(H (.inl 2,none)+H (.inl 2,some j))=0 := by
    apply (first_action j (fun u => H (u,none)+H (u,some j))).symm.trans
    simpa only [lam,Sum.elim_inl,if_true,one_mul] using (product_action (j,.inl 0) H).symm.trans (prod (j,.inl 0))
  have slope (j : Fin B) : H (.inl 1,some j)+2*(j.val:ℂ)*H (.inl 2,some j)=0 := by
    apply (slope_action j (fun u => H (u,some j))).symm.trans
    simpa [lam] using (product_action (j,.inl 1) H).symm.trans (prod (j,.inl 1))
  have extra (j : Fin B) (l : Fin A) : (2*H (.inr l,none)+H (.inr l,some j)) -
      (j.val:ℂ)^(l.val+3)*(2*H (.inl 2,none)+H (.inl 2,some j))=0 := by
    apply (extra_action j l (fun u => 2*H (u,none)+H (u,some j))).symm.trans
    simpa only [lam,Sum.elim_inr] using (product_action (j,.inr l) H).symm.trans (prod (j,.inr l))
  have lastSlope : H (.inl 1,none)+2*I*s=0 := by
    by_cases hv : v=0
    · have u := selected (.inl 1)
      have w := selected (.inl 2)
      simp only [if_pos hv,one_mul] at u w
      dsimp only [I,s]
      linear_combination u + 2*(i.val:ℂ)*w - slope i
    · exact Darm hv none
  have lastPoint : H (.inl 0,none)+I*H (.inl 1,none)+I^2*s=0 := by
    by_cases hv : v=0
    · exact Xarm hv none
    · have zero (u : Fin 3 ⊕ Fin A) : H (u,some i)=0 := by simpa only [if_neg hv,zero_mul,zero_add] using selected u
      simpa only [zero,add_zero] using anchor i
  have last₁ : H (.inl 1,none) = -2*I*s := by linear_combination lastSlope
  have last₀ : H (.inl 0,none) = I^2*s := by linear_combination lastPoint - I*lastSlope
  have lastExtra (l : Fin A) : H (.inr l,none) = I^(l.val+3)*s := by
    have a := selected (.inr l)
    have b := selected (.inl 2)
    dsimp only [I,s]
    by_cases hv : v=0
    · simp only [if_pos hv,one_mul] at a b
      linear_combination extra i l - a + (i.val:ℂ)^(l.val+3)*b
    · simp only [if_neg hv,zero_mul,zero_add] at a b
      linear_combination (extra i l - a + (i.val:ℂ)^(l.val+3)*b)/2
  have atLast (u : Fin 3 ⊕ Fin A) : H (u,none) = s*u.elim ![(i.val:ℂ)^2,-2*(i.val:ℂ),1]
      (fun l => (i.val:ℂ)^(l.val+3)) := by
    rcases u with k|l
    · fin_cases k
      · change H (.inl (0:Fin 3),none)=s*I^2
        rw [last₀,mul_comm]
      · change H (.inl (1:Fin 3),none)=s*(-2*I)
        rw [last₁,mul_comm]
      · change s=s*1
        rw [mul_one]
    · change H (.inr l,none)=s*I^(l.val+3)
      rw [lastExtra,mul_comm]
  have old₁ (j : Fin B) : H (.inl 1,some j) = -2*(j.val:ℂ)*H (.inl 2,some j) := by
    linear_combination slope j
  have old₀ (j : Fin B) : H (.inl 0,some j) = (j.val:ℂ)^2*H (.inl 2,some j) -
      (H (.inl 0,none)+(j.val:ℂ)*H (.inl 1,none)+(j.val:ℂ)^2*s) := by
    dsimp only [s]
    linear_combination anchor j - (j.val:ℂ)*slope j
  have signs (j : Fin B) : H (.inl 2,some j) = if v=0 then (if i=j then -s else s) else 0 := by
    have diff (h : i≠j) : (j.val:ℂ) ≠ I := by
      intro eq
      apply h
      apply Fin.ext
      dsimp only [I] at eq
      exact_mod_cast eq.symm
    by_cases hv : v=0
    · rw [if_pos hv]
      by_cases h : i=j
      · subst j
        rw [if_pos rfl]
        have u := selected (.inl 2)
        simp only [if_pos hv,one_mul] at u
        dsimp only [s]
        linear_combination u
      · rw [if_neg h]
        have fact : ((j.val:ℂ)-I)^2*(s-H (.inl 2,some j))=0 := by
          have hy := Xarm hv (some j)
          rw [old₀,old₁,last₀,last₁] at hy
          linear_combination -hy
        exact (sub_eq_zero.mp ((mul_eq_zero.mp fact).resolve_left (pow_ne_zero _ (sub_ne_zero.mpr (diff h))))).symm
    · rw [if_neg hv]
      by_cases h : i=j
      · subst j
        simpa only [if_neg hv,zero_mul,zero_add] using selected (.inl 2)
      · have fact : (2*(I-(j.val:ℂ)))*H (.inl 2,some j)=0 := by
          linear_combination Darm hv (some j) - slope j
        exact (mul_eq_zero.mp fact).resolve_left (mul_ne_zero (by norm_num) (sub_ne_zero.mpr (Ne.symm (diff h))))
  refine ⟨atLast,signs,?_⟩
  intro hs
  have lastZ (u : Fin 3 ⊕ Fin A) : H (u,none)=0 := by simpa only [hs,zero_mul] using atLast u
  have oldZ (j : Fin B) (u : Fin 3 ⊕ Fin A) : H (u,some j)=0 := by
    have z₂ : H (.inl 2,some j)=0 := by simpa only [hs,neg_zero,ite_self] using signs j
    rcases u with k|l
    · fin_cases k
      · change H (.inl (0 : Fin 3),some j)=0
        simpa only [z₂,lastZ,hs,mul_zero,add_zero,sub_zero] using old₀ j
      · change H (.inl (1 : Fin 3),some j)=0
        simpa only [z₂,mul_zero] using old₁ j
      · exact z₂
    · simpa only [lastZ,z₂,mul_zero,zero_add,add_zero,sub_zero] using extra j l
  funext ⟨u,k⟩
  cases k with
  | none => exact lastZ u
  | some j => exact oldZ j u

end LastSliceTwo

namespace LastSliceTwo

/-- Each signed row sum is the same total minus twice the coefficient at that row. -/
theorem signed_coefficients {B : ℕ} (hB : B ≠ 2) (s : Fin B → ℂ)
    (h : ∀ i, (∑ j, if j=i then -s j else s j)=0) : s=0 := by
  classical
  let T := ∑ j,s j
  have he (i : Fin B) : T = 2*s i := by
    have hrow : (∑ j, if j=i then -s j else s j)=T-2*s i := by
      calc
        _ = ∑ j, (s j-(if j=i then 2*s j else 0)) := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hji : j=i <;> simp [hji]
          ring
        _ = T-2*s i := by rw [Finset.sum_sub_distrib]; simp [T,Finset.sum_ite_eq']
    exact sub_eq_zero.mp (hrow.symm.trans (h i))
  have hall : (B : ℂ)*T=2*T := by
    calc
      _ = ∑ _ : Fin B,T := by simp
      _ = ∑ j,2*s j := Finset.sum_congr rfl fun j _ => he j
      _ = _ := (Finset.mul_sum ..).symm
  have hne : (B : ℂ)-2≠0 := sub_ne_zero.mpr (by exact_mod_cast hB)
  have hz : T=0 := (mul_eq_zero.mp (show ((B : ℂ)-2)*T=0 by linear_combination hall)).resolve_left hne
  funext i
  have hi := he i
  rw [hz] at hi
  change s i=0
  linear_combination -hi/2

/-- The initial three coordinates encode the quadratic, linear and constant moments;
the remaining coordinates supply the powers of degree three and above. -/
theorem moment_coefficients {A m : ℕ} (hm : m≤A+3) (t : Fin m → ℂ) (hit : Function.Injective t)
    (q : Fin m → ℂ) (h : ∀ u : Fin 3 ⊕ Fin A, (∑ j, q j*u.elim ![(t j)^2,-2*(t j),1]
      (fun l => (t j)^(l.val+3)))=0) : q=0 := by
  apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hit
  intro k
  by_cases h₀ : k.val=0
  · simpa [h₀,Matrix.cons_val_two] using h (.inl 2)
  by_cases h₁ : k.val=1
  · simp only [h₁,pow_one]
    have he : (∑ j,q j*t j)*(-2)=0 := by
      calc
        _ = ∑ j,q j*(-2*(t j)) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = 0 := by simpa using h (.inl 1)
    exact (mul_eq_zero.mp he).resolve_right (by norm_num)
  by_cases h₂ : k.val=2
  · simpa only [h₂,Sum.elim_inl,Matrix.cons_val_zero] using h (.inl 0)
  let l : Fin A := ⟨k.val-3,by omega⟩
  have hl : l.val+3=k.val := by dsimp only [l]; omega
  simpa only [Sum.elim_inr,hl] using h (.inr l)

theorem tagged_coefficients {A B : ℕ} (hB : B ≠ 2) (s : Fin B → ℂ) (q : Fin (min (A+3) B) → ℂ) :
    let h (j : Fin B) (u : Fin 3 ⊕ Fin A) : ℂ := u.elim ![(j.val : ℂ)^2,-2*(j.val : ℂ),1] (fun l => (j.val : ℂ)^(l.val+3))
    (∀ i, (∑ j, if j=i then -s j else s j)=0) →
    (∀ u, (∑ j, s j*h j u) + (∑ k, q k*h (k.castLE (Nat.min_le_right _ _)) u)=0) → s=0 ∧ q=0 := by
  intro h hs hq
  have hzero := signed_coefficients hB s hs
  refine ⟨hzero,?_⟩
  exact moment_coefficients (A:=A) (Nat.min_le_left (A+3) B) (fun j => (j.val : ℂ))
    (fun _ _ e => Fin.ext (Nat.cast_injective e)) q (fun u => by
      simpa only [h,hzero,Pi.zero_apply,zero_mul,Finset.sum_const_zero,zero_add,Fin.val_castLE] using hq u)

end LastSliceTwo

namespace LastSliceTwo

/-- Mark all `B` first-tag samples and the initial `min (A+3) B` second-tag samples.
Their normal spaces form an internal direct sum. -/
lemma exists_large_batch (A B : ℕ) (hB : 3 ≤ B) :
    ∃ label : (Fin B ⊕ Fin (min (A+3) B)) ↪ (Fin B × (Fin 2 ⊕ Fin A)),
    ∃ x : (Fin B × (Fin 2 ⊕ Fin A)) → (Fin 3 ⊕ Fin A) → ℂ,
    ∃ y : (Fin B × (Fin 2 ⊕ Fin A)) → Option (Fin B) → ℂ,
    ∀ H : (Fin B ⊕ Fin (min (A+3) B)) → (Fin 3 ⊕ Fin A) × Option (Fin B) → ℂ,
      (∀ t s, (∑ ij, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (label t) j*H t (i,j))=0) →
      (∀ t j, (∑ i, x (label t) i*H t (i,j))=0) → (∑ t,H t)=0 → H=0 := by
  classical
  let k := min (A+3) B
  let inc (t : Fin k) := t.castLE (Nat.min_le_right (A+3) B)
  let label : (Fin B ⊕ Fin k) ↪ (Fin B × (Fin 2 ⊕ Fin A)) := {
    toFun := Sum.elim (fun i => (i,.inl 0)) (fun t => (inc t,.inl 1))
    inj' := by
      rintro (i|i) (j|j) he
      · exact congrArg Sum.inl (congrArg Prod.fst he)
      · have ht : (0 : Fin 2)=1 := Sum.inl.inj (congrArg Prod.snd he)
        exact (zero_ne_one ht).elim
      · have ht : (1 : Fin 2)=0 := Sum.inl.inj (congrArg Prod.snd he)
        exact (one_ne_zero ht).elim
      · have hv : inc i=inc j := congrArg Prod.fst he
        exact congrArg Sum.inr (Fin.ext (congrArg (fun v : Fin B => v.val) hv)) }
  obtain ⟨x,y,formula⟩ := exists_two_formulas A B
  refine ⟨label,x,y,?_⟩
  intro H outer rows cols total
  let s (i : Fin B) := H (.inl i) (.inl 2,none)
  let q (i : Fin k) := H (.inr i) (.inl 2,none)
  let v (i : Fin B) (u : Fin 3 ⊕ Fin A) := u.elim ![(i.val : ℂ)^2,-2*(i.val : ℂ),1] (fun l => (i.val : ℂ)^(l.val+3))
  have first (i : Fin B) := formula i 0 (H (.inl i)) (outer (.inl i)) (rows (.inl i)) (cols (.inl i))
  have extra (i : Fin k) := formula (inc i) 1 (H (.inr i)) (outer (.inr i)) (rows (.inr i)) (cols (.inr i))
  have f₁ (i : Fin B) (u : Fin 3 ⊕ Fin A) : H (.inl i) (u,none) = s i*v i u := (first i).1 u
  have f₂ (i j : Fin B) : H (.inl i) (.inl 2,some j) = if i=j then -s i else s i := (first i).2.1 j
  have e₁ (i : Fin k) (u : Fin 3 ⊕ Fin A) : H (.inr i) (u,none) = q i * v (inc i) u := (extra i).1 u
  have e₂ (i : Fin k) (j : Fin B) : H (.inr i) (.inl 2,some j) = 0 := (extra i).2.1 j
  have signed (j : Fin B) : (∑ i, if i=j then -s i else s i)=0 := by
    have he := congrFun total (.inl 2,some j)
    simpa only [Fintype.sum_sum_type,Pi.add_apply,Finset.sum_apply,f₂,e₂,Finset.sum_const_zero,add_zero,Pi.zero_apply] using he
  have last (u : Fin 3 ⊕ Fin A) : (∑ i, s i*v i u) + (∑ j, q j*v (inc j) u)=0 := by
    have he := congrFun total (u,none)
    simpa only [Fintype.sum_sum_type,Pi.add_apply,Finset.sum_apply,f₁,e₁,Pi.zero_apply] using he
  obtain ⟨hs,hq⟩ := tagged_coefficients (A:=A) (by omega : B≠2) s q signed last
  funext t
  cases t with
  | inl i => exact (first i).2.2 (congrFun hs i)
  | inr i => exact (extra i).2.2 (congrFun hq i)

end LastSliceTwo

namespace LastSlicePositive

/-- For every ordered pair of long sides in this range, the unrestricted
tangent spaces span at w=(a−1)(b−1) points throughout the batch-capacity range. -/
theorem second_full (a b c : ℕ) (ha : 3≤a) (hb : 4≤b) (_hab : a≤b)
    (hc : c≤(a-1)*(b-1))
    (fit : (a-1)*(b-1) ≤ ((a-1)*(b-1)-c)*((b-1)+min a (b-1))) :
    let w := (a-1)*(b-1)
    ∃ x : Fin w → Fin a → ℂ, ∃ y : Fin w → Fin b → ℂ, ∃ z : Fin w → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin w → Fin a → ℂ,
        ∃ v : Fin w → Fin b → ℂ, ∃ v' : Fin w → Fin c → ℂ, ∀ i j k,
          T i j k=∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*v' t k)) := by
  classical
  obtain ⟨A,rfl⟩ : ∃ A, a=A+3 := ⟨a-3,by omega⟩
  obtain ⟨B,rfl⟩ : ∃ B, b=B+1 := ⟨b-1,by omega⟩
  let P := Fin B × (Fin 2 ⊕ Fin A)
  let Q := Fin B ⊕ Fin (min (A+3) B)
  let w := (A+2)*B
  have size : Fintype.card P=w := by simp [P,w,Fintype.card_prod,Nat.mul_comm,Nat.add_comm]
  let ep : P ≃ Fin w := (Fintype.equivFin P).trans (finCongr size)
  let ea : (Fin 3 ⊕ Fin A) ≃ Fin (A+3) := finSumFinEquiv.trans (finCongr (Nat.add_comm 3 A))
  let eb : Option (Fin B) ≃ Fin (B+1) := (finSuccEquiv B).symm
  obtain ⟨mark,x,y,direct⟩ := LastSliceTwo.exists_large_batch A B (by omega)
  let first : Q ↪ Fin w := mark.trans ep.toEmbedding
  have count : Fintype.card Q = B+min (A+3) B := by simp [Q]
  exact from_capacity count first hc fit (move_mark ea eb ep mark ⟨x,y,direct⟩)

end LastSlicePositive

namespace CriticalPlateau

open Arxiv.«0805.3777»

private lemma boundary_product {a b w : ℕ} (ha : 3≤a) (hb : 3≤b) (hw : w=(a-1)*(b-1)) :
    a*b = w+(a+b-2)+1 := by
  have h₁ : a-1+1=a := by omega
  have h₂ : b-1+1=b := by omega
  have h : (a-1+1)*(b-1+1)=a*b := by rw [h₁,h₂]
  have h₃ : a*b+1=w+a+b := by nlinarith only [h,h₁,h₂,hw]
  omega

/-- Exactly the top values of the third dimension have dimension-count
ceiling one above the critical boundary dimension. -/
theorem rank_eq_iff {a b k w : ℕ} (ha : 3≤a) (hb : 3≤b) (hw : w=(a-1)*(b-1)) (hk : k≤w) :
    (a*b*k ⌈/⌉ (a+b+k-2) = w+1) ↔ w*(a+b-2)<(a+b-1)*k := by
  let D := a+b-2
  have hp : 0<D+k := by dsimp [D]; omega
  have hd : a+b+k-2=D+k := by dsimp [D]; omega
  have hs : a+b-1=D+1 := by dsimp [D]; omega
  rw [hd,hs,boundary_product ha hb hw]
  change ((w+D+1)*k ⌈/⌉ (D+k) = w+1) ↔ w*D<(D+1)*k
  let R := (w+D+1)*k ⌈/⌉ (D+k)
  have hihi : R≤w+1 := by
    apply (ceilDiv_le_iff_le_mul hp).mpr
    nlinarith only [Nat.mul_le_mul_left D (show k≤w+1 by omega)]
  have hcomp : R≤w ↔ (w+D+1)*k ≤ (D+k)*w := ceilDiv_le_iff_le_mul hp
  change R=w+1 ↔ w*D<(D+1)*k
  constructor
  · intro he
    have hgt : (D+k)*w < (w+D+1)*k := lt_of_not_ge (fun h => by have := hcomp.mpr h; omega)
    nlinarith only [hgt]
  · intro h
    have hgt : (D+k)*w < (w+D+1)*k := by nlinarith only [h]
    have hn : ¬R≤w := fun hs => (not_le_of_gt hgt) (hcomp.mp hs)
    omega

theorem rank_eq {a b k w : ℕ} (ha : 3≤a) (hb : 3≤b) (hw : w=(a-1)*(b-1)) (hk : k≤w)
    (ht : w*(a+b-2)<(a+b-1)*k) : a*b*k ⌈/⌉ (a+b+k-2) = w+1 :=
  (rank_eq_iff ha hb hw hk).mpr ht

/-- Express the strict threshold in terms of distance below the boundary. -/
theorem offset_mul_iff {a b k w : ℕ} (ha : 3≤a) (hk : k≤w) :
    w*(a+b-2)<(a+b-1)*k ↔ (a+b-1)*(w-k)<w := by
  rw [show a+b-1=(a+b-2)+1 by omega]
  have hd := congrArg (fun u : ℕ => ((a+b-2)+1)*u) (Nat.sub_add_cancel hk)
  constructor <;> intro h <;> nlinarith only [hd,h]

/-- The boundary offset must be strictly smaller than the ceiling of w/(a+b-1). -/
theorem offset_iff {a b k w : ℕ} (ha : 3≤a) (hk : k≤w) :
    w*(a+b-2)<(a+b-1)*k ↔ w-k < w ⌈/⌉ (a+b-1) := by
  rw [offset_mul_iff ha hk]
  have h := (ceilDiv_le_iff_le_mul (by omega : 0<a+b-1) (b:=w) (c:=w-k))
  omega

/-- Restrict the third factors of a boundary witness. Every prescribed
tensor on the retained coordinates extends by zero to the original tensor space. -/
theorem projected_witness {a b k w : ℕ} (ha : 3≤a) (hb : 3≤b) (hw : w=(a-1)*(b-1)) (hk : k≤w) :
    ∃ x : Fin (w+1) → Fin a → ℂ, ∃ y : Fin (w+1) → Fin b → ℂ, ∃ z : Fin (w+1) → Fin k → ℂ,
      ∀ T : Fin a → Fin b → Fin k → ℂ, ∃ u : Fin (w+1) → Fin a → ℂ,
        ∃ v : Fin (w+1) → Fin b → ℂ, ∃ s : Fin (w+1) → Fin k → ℂ, ∀ i j l,
          T i j l = ∑ t, (u t i*(y t j*z t l) + x t i*(v t j*z t l) + x t i*(y t j*s t l)) := by
  have hwit := RemainingBoundary.boundary_witness (a:=a) (b:=b) (c:=w) ha hb hw
  dsimp only at hwit
  have hr : a*b*w ⌈/⌉ (a+b+w-2)=w+1 := by
    subst w
    exact critical_ceilDiv ha hb
  rw [hr] at hwit
  obtain ⟨x,y,z,span⟩ := hwit
  refine ⟨fun t i => ((x t i).val : ℂ), fun t j => ((y t j).val : ℂ),
    fun t l => ((z t (Fin.castLE hk l)).val : ℂ), ?_⟩
  intro T
  let extend (i : Fin a) (j : Fin b) (l : Fin w) := if hl : l.val<k then T i j ⟨l.val,hl⟩ else 0
  obtain ⟨u,v,s,hs⟩ := span extend
  refine ⟨u,v,fun t l => s t (Fin.castLE hk l),?_⟩
  intro i j l
  simpa [extend,l.isLt] using hs i j (Fin.castLE hk l)

open Arxiv.«0805.3777» in
/-- Throughout the complete top plateau the complex generic rank is w+1. -/
theorem generic_rank {a b k w : ℕ} (ha : 3≤a) (hab : a≤b) (hbk : b≤k)
    (hw : w=(a-1)*(b-1)) (hk : k≤w) (ht : w*(a+b-2)<(a+b-1)*k) :
    IsGenericRank [a,b,k] (w+1) := by
  have hr := rank_eq ha (ha.trans hab) hw hk ht
  rw [←hr]
  apply OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1.generic_of_bounded a b k ha hab hbk
  rw [hr]
  exact CriticalReduction.bounded_of_witness (projected_witness ha (ha.trans hab) hw hk)

/-- When the first two sides are equal, the plateau contains one more
boundary offset exactly when n reaches the next even integer. -/
theorem square_offset_iff (n d : ℕ) (hn : 3≤n) :
    (n+n-1)*d < (n-1)^2 ↔ 2*d+2 ≤ n := by
  let h := n-1
  have hpos : 0<h := by dsimp [h]; omega
  rw [show n+n-1=2*h+1 by dsimp [h]; omega]
  change (2*h+1)*d<h^2 ↔ _
  constructor
  · intro ht
    by_contra! hbad
    have hs : h≤2*d := by dsimp [h]; omega
    nlinarith only [Nat.mul_le_mul_left (2*h+1) hs, ht, hpos]
  · intro ht
    have hs : 2*d+1≤h := by dsimp [h]; omega
    nlinarith only [Nat.mul_le_mul_left (2*h+1) hs, hpos]

/-- For n by n matrices the width of the top ceiling plateau is floor(n/2). -/
theorem square_width (n : ℕ) (hn : 3≤n) : (n-1)^2 ⌈/⌉ (n+n-1) = n/2 := by
  have characterize (d : ℕ) : d < (n-1)^2 ⌈/⌉ (n+n-1) ↔ d < n/2 := by
    have hp := (ceilDiv_le_iff_le_mul (by omega : 0<n+n-1) (b:=(n-1)^2) (c:=d))
    have hs := square_offset_iff n d hn
    omega
  apply le_antisymm
  · by_contra! bad
    exact (not_lt_of_ge le_rfl) ((characterize _).mp bad)
  · by_contra! bad
    exact (not_lt_of_ge le_rfl) ((characterize _).mpr bad)

end CriticalPlateau

namespace CriticalPlateau.Full

private lemma budget_id {a b w : ℕ} (ha : 3≤a) (hab : a≤b) (hw : w=(a-1)*(b-1)) :
    0<w ∧ a*b = w+(a+b-1) ∧ a*b=(w-1)+(a+b) := by
  subst w
  have ha₁ : 1≤a := by omega
  have hb₁ : 1≤b := by omega
  have hs : 1≤a+b := by omega
  have hw₀ : 0<(a-1)*(b-1) := Nat.mul_pos (by omega) (by omega)
  refine ⟨hw₀,?_,?_⟩ <;> zify [ha₁,hb₁,hs,Nat.succ_le_iff.mpr hw₀] <;> ring

theorem ceil_le_iff_offset {a b c w : ℕ} (ha : 3≤a) (hab : a≤b)
    (hw : w=(a-1)*(b-1)) (hc : c≤w) :
    a*b*c ⌈/⌉ (a+b+c-2) ≤ w ↔ w ⌈/⌉ (a+b-1) ≤ w-c := by
  obtain ⟨_,hp,_⟩ := budget_id ha hab hw
  rw [ceilDiv_le_iff_le_mul (by omega : 0<a+b+c-2)]
  rw [hp, show a+b+c-2=(a+b-2)+c by omega]
  have h := CriticalPlateau.offset_iff (a:=a) (b:=b) ha hc
  constructor
  · intro he
    have : (a+b-1)*c ≤ w*(a+b-2) := by nlinarith only [he]
    omega
  · intro he
    have : (a+b-1)*c ≤ w*(a+b-2) := by omega
    nlinarith only [this]

private lemma square_capacity (n d : ℕ) (hn : 3≤n) :
    (n-1)^2 ≤ d*(2*(n-1)) ↔ n/2≤d := by
  rw [pow_two, show d*(2*(n-1))=(n-1)*(2*d) by ring]
  constructor
  · intro h
    have := Nat.le_of_mul_le_mul_left h (show 0<n-1 by omega)
    omega
  · intro h
    exact Nat.mul_le_mul_left _ (by omega)

/-- The ragged family has enough directions precisely when the predicted
rank is no greater than w. The formula includes equality of the first two
dimensions, where the normal count is 2(a-1). -/
theorem capacity_iff {a b c w : ℕ} (ha : 3≤a) (hab : a≤b) (hw : w=(a-1)*(b-1)) (hc : c≤w) :
    a*b*c ⌈/⌉ (a+b+c-2) ≤ w ↔ w ≤ (w-c)*((b-1)+min a (b-1)) := by
  rw [ceil_le_iff_offset ha hab hw hc]
  by_cases he : a=b
  · subst b
    have width : w ⌈/⌉ (a+a-1) = a/2 := by
      simpa only [hw, pow_two] using CriticalPlateau.square_width a ha
    rw [width, min_eq_right (Nat.sub_le a 1), show a-1+(a-1)=2*(a-1) by omega]
    simpa only [hw,pow_two] using (square_capacity a (w-c) ha).symm
  · rw [min_eq_left (show a≤b-1 by omega), show b-1+a=a+b-1 by omega,
      ceilDiv_le_iff_le_mul (by omega : 0<a+b-1), Nat.mul_comm (w-c) (a+b-1)]

theorem capacity_of_second {a b c w : ℕ} (ha : 3≤a) (hab : a≤b)
    (hw : w=(a-1)*(b-1)) (hc : c≤w) (hr : a*b*c ⌈/⌉ (a+b+c-2) = w) :
    w≤(w-c)*((b-1)+min a (b-1)) :=
  (capacity_iff ha hab hw hc).mp hr.le

/-- Exact lower endpoint for belonging to either of the two highest ceiling values. -/
theorem at_least_second_iff {a b c w : ℕ} (ha : 3≤a) (hab : a≤b) (hw : w=(a-1)*(b-1)) :
    w ≤ a*b*c ⌈/⌉ (a+b+c-2) ↔ (w-1)*(a+b-2)<(a+b)*c := by
  obtain ⟨hw₀,_,hp⟩ := budget_id ha hab hw
  have h := ceilDiv_le_iff_le_mul (by omega : 0<a+b+c-2) (b:=a*b*c) (c:=w-1)
  have comp : a*b*c ≤ (a+b+c-2)*(w-1) ↔ (a+b)*c ≤ (w-1)*(a+b-2) := by
    rw [hp, show a+b+c-2=(a+b-2)+c by omega]
    constructor <;> intro hx <;> nlinarith only [hx]
  omega

theorem top_two_ceil {a b c w : ℕ} (ha : 3≤a) (hab : a≤b) (hw : w=(a-1)*(b-1))
    (hc : c≤w) (ht : (w-1)*(a+b-2)<(a+b)*c) :
    a*b*c ⌈/⌉ (a+b+c-2) = if w*(a+b-2)<(a+b-1)*c then w+1 else w := by
  by_cases top : w*(a+b-2)<(a+b-1)*c
  · rw [if_pos top]
    exact CriticalPlateau.rank_eq ha (ha.trans hab) hw hc top
  · rw [if_neg top]
    apply le_antisymm _ ((at_least_second_iff ha hab hw).mpr ht)
    apply (ceil_le_iff_offset ha hab hw hc).mpr
    have h := CriticalPlateau.offset_iff (a:=a) (b:=b) ha hc
    omega

/-- At square first dimensions the top two bands together occupy exactly
n-1 successive third dimensions, indexed by offsets 0 through n-2. -/
theorem square_top_two_iff {n d : ℕ} (hn : 3≤n) (hd : d≤(n-1)^2) :
    ((n-1)^2-1)*(n+n-2)<(n+n)*((n-1)^2-d) ↔ d<n-1 := by
  let w := (n-1)^2
  have hw : 0<(n-1)^2 := pow_pos (by omega) _
  have h₁ : (n+n)*w = (w-1)*(n+n-2)+(n+n)*(n-1) := by
    dsimp only [w]
    zify [show 1≤n by omega, Nat.succ_le_iff.mpr hw, show 2≤n+n by omega]
    ring
  have h₂ := congrArg (fun x : ℕ => (n+n)*x) (Nat.sub_add_cancel hd)
  change (w-1)*(n+n-2)<(n+n)*(w-d) ↔ _
  change (n+n)*(w-d+d)=(n+n)*w at h₂
  have hmid : (w-1)*(n+n-2)<(n+n)*(w-d) ↔ (n+n)*d < (n+n)*(n-1) := by
    constructor <;> intro hx <;> nlinarith only [h₁,h₂,hx]
  rw [hmid]
  exact ⟨Nat.lt_of_mul_lt_mul_left, fun h => Nat.mul_lt_mul_of_pos_left h (by omega)⟩

end CriticalPlateau.Full

namespace CriticalPlateau.Full

open Arxiv.«0805.3777»

/-- Under the ragged capacity implication, the numerical ceiling is actually
attained by a spanning tangent in both of the two highest bands. -/
theorem expected_witness {a b c w : ℕ} (ha : 3≤a) (hab : a≤b) (hb : 4≤b)
    (hw : w=(a-1)*(b-1)) (hc : c≤w) (ht : (w-1)*(a+b-2)<(a+b)*c)
    (seed : w ≤ (w-c)*((b-1)+min a (b-1)) →
      ∃ x : Fin w → Fin a → ℂ, ∃ y : Fin w → Fin b → ℂ, ∃ z : Fin w → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin w → Fin a → ℂ,
        ∃ v : Fin w → Fin b → ℂ, ∃ s : Fin w → Fin c → ℂ, ∀ i j l,
          T i j l = ∑ t, (u t i*(y t j*z t l) + x t i*(v t j*z t l) + x t i*(y t j*s t l))) :
    let r := a*b*c ⌈/⌉ (a+b+c-2)
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ s : Fin r → Fin c → ℂ, ∀ i j l,
          T i j l = ∑ t, (u t i*(y t j*z t l) + x t i*(v t j*z t l) + x t i*(y t j*s t l)) := by
  dsimp only
  rw [top_two_ceil ha hab hw hc ht]
  by_cases top : w*(a+b-2)<(a+b-1)*c
  · rw [if_pos top]
    exact CriticalPlateau.projected_witness ha (by omega) hw hc
  · rw [if_neg top]
    apply seed
    apply capacity_of_second ha hab hw hc
    simpa only [if_neg top] using top_two_ceil ha hab hw hc ht

/-- The actual complex generic rank in the full two-band interval, conditional
only on the ragged seed for this format when its capacity is sufficient. -/
theorem generic_rank {a b c w : ℕ} (ha : 3≤a) (hab : a≤b) (hb : 4≤b) (hbc : b≤c)
    (hw : w=(a-1)*(b-1)) (hc : c≤w) (ht : (w-1)*(a+b-2)<(a+b)*c)
    (seed : w ≤ (w-c)*((b-1)+min a (b-1)) →
      ∃ x : Fin w → Fin a → ℂ, ∃ y : Fin w → Fin b → ℂ, ∃ z : Fin w → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin w → Fin a → ℂ,
        ∃ v : Fin w → Fin b → ℂ, ∃ s : Fin w → Fin c → ℂ, ∀ i j l,
          T i j l = ∑ t, (u t i*(y t j*z t l) + x t i*(v t j*z t l) + x t i*(y t j*s t l))) :
    IsGenericRank [a,b,c] (if w*(a+b-2)<(a+b-1)*c then w+1 else w) := by
  rw [← top_two_ceil ha hab hw hc ht]
  apply OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1.generic_of_bounded a b c ha hab hbc
  exact CriticalReduction.bounded_of_witness (expected_witness ha hab hb hw hc ht seed)

/-- A uniform ragged witness with the stated normal count suffices for every
admissible format in the whole top-two rank interval. -/
theorem of_universal_witness
    (seed : ∀ a b c : ℕ, 3≤a → a≤b → 4≤b → b≤c →
      let w := (a-1)*(b-1)
      c≤w → w ≤ (w-c)*((b-1)+min a (b-1)) →
      ∃ x : Fin w → Fin a → ℂ, ∃ y : Fin w → Fin b → ℂ, ∃ z : Fin w → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin w → Fin a → ℂ,
        ∃ v : Fin w → Fin b → ℂ, ∃ s : Fin w → Fin c → ℂ, ∀ i j l,
          T i j l = ∑ t, (u t i*(y t j*z t l) + x t i*(v t j*z t l) + x t i*(y t j*s t l)))
    {a b c w : ℕ} (ha : 3≤a) (hab : a≤b) (hb : 4≤b) (hbc : b≤c)
    (hw : w=(a-1)*(b-1)) (hc : c≤w) (ht : (w-1)*(a+b-2)<(a+b)*c) :
    IsGenericRank [a,b,c] (if w*(a+b-2)<(a+b-1)*c then w+1 else w) := by
  apply generic_rank ha hab hb hbc hw hc ht
  subst w
  exact seed a b c ha hab hb hbc hc

/-- The same uniform construction covers every top-two format in the critical
range away from the exceptional 3-by-3-by-3 cube. At b=3 the remaining
format is the already proved critical boundary 3-by-3-by-4. -/
theorem of_universal_witness_away_cube
    (seed : ∀ a b c : ℕ, 3≤a → a≤b → 4≤b → b≤c →
      let w := (a-1)*(b-1)
      c≤w → w ≤ (w-c)*((b-1)+min a (b-1)) →
      ∃ x : Fin w → Fin a → ℂ, ∃ y : Fin w → Fin b → ℂ, ∃ z : Fin w → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin w → Fin a → ℂ,
        ∃ v : Fin w → Fin b → ℂ, ∃ s : Fin w → Fin c → ℂ, ∀ i j l,
          T i j l = ∑ t, (u t i*(y t j*z t l) + x t i*(v t j*z t l) + x t i*(y t j*s t l)))
    {a b c w : ℕ} (ha : 3≤a) (hab : a≤b) (hbc : b≤c) (hx : (a,b,c) ≠ (3,3,3))
    (hw : w=(a-1)*(b-1)) (hc : c≤w) (ht : (w-1)*(a+b-2)<(a+b)*c) :
    IsGenericRank [a,b,c] (if w*(a+b-2)<(a+b-1)*c then w+1 else w) := by
  by_cases hb : 4≤b
  · exact of_universal_witness seed ha hab hb hbc hw hc ht
  · obtain rfl : a=3 := by omega
    obtain rfl : b=3 := by omega
    obtain rfl : w=4 := hw
    have h₃ : c≠3 := by rintro rfl; exact hx rfl
    obtain rfl : c=4 := by omega
    exact CriticalPlateau.generic_rank (by decide : 3≤3) le_rfl (by decide : 3≤4)
      (by decide : 4=(3-1)*(3-1)) le_rfl (by decide)

/-- For n at least four the top n-1 square offsets give the two ranks shown:
the first floor(n/2) offsets have rank w+1, and the rest have rank w. -/
theorem square_generic_rank (n d : ℕ) (hn : 4≤n) (hd : d<n-1)
    (seed : let w := (n-1)^2
      w ≤ d*(2*(n-1)) →
      ∃ x : Fin w → Fin n → ℂ, ∃ y : Fin w → Fin n → ℂ, ∃ z : Fin w → Fin (w-d) → ℂ,
      ∀ T : Fin n → Fin n → Fin (w-d) → ℂ, ∃ u : Fin w → Fin n → ℂ,
        ∃ v : Fin w → Fin n → ℂ, ∃ s : Fin w → Fin (w-d) → ℂ, ∀ i j l,
          T i j l = ∑ t, (u t i*(y t j*z t l) + x t i*(v t j*z t l) + x t i*(y t j*s t l))) :
    IsGenericRank [n,n,(n-1)^2-d] (if d<n/2 then (n-1)^2+1 else (n-1)^2) := by
  let w := (n-1)^2
  have hs : 2*(n-1) ≤ w := by
    simpa only [w, pow_two] using Nat.mul_le_mul_right (n-1) (show 2≤n-1 by omega)
  have hdn : d≤w := by omega
  have hk : w-d≤w := Nat.sub_le _ _
  have hw : w=(n-1)*(n-1) := by dsimp [w]; ring
  have ht := (square_top_two_iff (by omega : 3≤n) (show d≤(n-1)^2 from hdn)).mpr hd
  have top : w*(n+n-2)<(n+n-1)*(w-d) ↔ d<n/2 := by
    rw [CriticalPlateau.offset_mul_iff (by omega : 3≤n) hk, show w-(w-d)=d by omega]
    exact (CriticalPlateau.square_offset_iff n d (by omega)).trans (by omega)
  have h := generic_rank (by omega : 3≤n) le_rfl hn (show n≤w-d by omega) hw hk ht (by
    intro hcap
    apply seed
    rw [show w-(w-d)=d by omega, min_eq_right (Nat.sub_le n 1),
      show n-1+(n-1)=2*(n-1) by omega] at hcap
    exact hcap)
  change IsGenericRank [n,n,w-d] (if d<n/2 then w+1 else w)
  by_cases b : d<n/2
  · simpa only [if_pos b, if_pos (top.mpr b)] using h
  · simpa only [if_neg b, if_neg (fun v => b (top.mp v))] using h

end CriticalPlateau.Full

namespace CriticalPlateau.Full

open MvPolynomial

/-- On the whole upper two bands the ragged witness implies the exact last-slice
rank increment used by the registered consecutive-to-rectangular reduction. -/
theorem last_rank_increment {a b c w : ℕ} (ha : 3≤a) (hab : a≤b) (hb : 4≤b)
    (hw : w=(a-1)*(b-1)) (hc : c+1≤w) (ht : (w-1)*(a+b-2)<(a+b)*(c+1))
    (seed : w ≤ (w-(c+1))*((b-1)+min a (b-1)) →
      ∃ x : Fin w → Fin a → ℂ, ∃ y : Fin w → Fin b → ℂ, ∃ z : Fin w → Fin (c+1) → ℂ,
      ∀ T : Fin a → Fin b → Fin (c+1) → ℂ, ∃ u : Fin w → Fin a → ℂ,
        ∃ v : Fin w → Fin b → ℂ, ∃ s : Fin w → Fin (c+1) → ℂ, ∀ i j l,
          T i j l = ∑ t, (u t i*(y t j*z t l) + x t i*(v t j*z t l) + x t i*(y t j*s t l))) :
    let r' := (a*b*(c+1) ⌈/⌉ (a+b+(c+1)-2))
    let V := Fin r' × (Fin a ⊕ (Fin b ⊕ Fin (c+1)))
    let R := MvPolynomial V ℂ
    let coord : V → R := MvPolynomial.X
    let P : Matrix ((Fin a × Fin b) × Fin (c+1)) V R := fun row col =>
      col.2.elim (fun i => if i=row.1.1 then coord (col.1,.inr (.inl row.1.2))*coord (col.1,.inr (.inr row.2)) else 0)
        (Sum.elim (fun j => if j=row.1.2 then coord (col.1,.inl row.1.1)*coord (col.1,.inr (.inr row.2)) else 0)
          (fun k => if k=row.2 then coord (col.1,.inl row.1.1)*coord (col.1,.inr (.inl row.1.2)) else 0))
    let G := P.map (algebraMap R (FractionRing R))
    let old := G.submatrix (fun q : (Fin a × Fin b) × Fin c => (q.1,q.2.castSucc)) id
    G.rank = old.rank + a*b := by
  intro r V R coord P G old
  have hs : Function.Surjective G.mulVec := by
    apply (CriticalTensor.Unrestricted.generic_surjective_iff P).mpr
    apply (CriticalJacobian.restricted_tangent_iff id P (fun _ _ _ _ _ => rfl)).mp
    exact expected_witness ha hab hb hw hc ht seed
  simpa only [Fintype.card_prod,Fintype.card_fin] using
    ((UnrestrictedSlice.surjective_iff_increment G).mp hs).2

end CriticalPlateau.Full

namespace CriticalPlateau.Proved

open Arxiv.«0805.3777»

/-- In the two highest predicted-rank bands, the generic complex tensor has
the indicated rank. The only excluded cube in this band statement is 3 by 3 by 3. -/
theorem generic_rank {a b c w : ℕ} (ha : 3≤a) (hab : a≤b) (hbc : b≤c)
    (hx : (a,b,c) ≠ (3,3,3)) (hw : w=(a-1)*(b-1)) (hc : c≤w)
    (ht : (w-1)*(a+b-2)<(a+b)*c) :
    IsGenericRank [a,b,c] (if w*(a+b-2)<(a+b-1)*c then w+1 else w) :=
  CriticalPlateau.Full.of_universal_witness_away_cube
    (fun a b c ha hab hb _ => LastSlicePositive.second_full a b c ha hb hab) ha hab hbc hx hw hc ht

/-- The catalogue dimension-count value is attained throughout both bands. -/
theorem generic_rank_at_ceiling {a b c w : ℕ} (ha : 3≤a) (hab : a≤b) (hbc : b≤c)
    (hx : (a,b,c) ≠ (3,3,3)) (hw : w=(a-1)*(b-1)) (hc : c≤w)
    (high : w ≤ a*b*c ⌈/⌉ (a+b+c-2)) :
    IsGenericRank [a,b,c] (a*b*c ⌈/⌉ (a+b+c-2)) := by
  have ht := (CriticalPlateau.Full.at_least_second_iff ha hab hw).mp high
  rw [CriticalPlateau.Full.top_two_ceil ha hab hw hc ht]
  exact generic_rank ha hab hbc hx hw hc ht

/-- When the first two dimensions are n, the top n−1 third dimensions have
rank (n−1)²+1 for the first floor(n/2) offsets and (n−1)² thereafter. -/
theorem square_generic_rank (n d : ℕ) (hn : 4≤n) (hd : d<n-1) :
    IsGenericRank [n,n,(n-1)^2-d] (if d<n/2 then (n-1)^2+1 else (n-1)^2) := by
  apply CriticalPlateau.Full.square_generic_rank n d hn hd
  let w := (n-1)^2
  have hw : (n-1)*(n-1)=w := by dsimp [w]; ring
  have hle : n-1 ≤ w := by
    simpa only [w,pow_two,one_mul] using Nat.mul_le_mul_right (n-1) (show 1≤n-1 by omega)
  have h := LastSlicePositive.second_full n n (w-d) (by omega) hn le_rfl
  rw [hw,show w-(w-d)=d by omega,min_eq_right (Nat.sub_le n 1),
    show n-1+(n-1)=2*(n-1) by omega] at h
  exact h (Nat.sub_le _ _)

end CriticalPlateau.Proved

namespace CriticalPlateau.Proved

open MvPolynomial

/-- On the top two bands the generic Jacobian gains exactly ab ranks when
the last slice is included. All factors and variations remain unrestricted. -/
theorem last_increment {a b c w : ℕ} (ha : 3≤a) (hab : a≤b) (hb : 4≤b)
    (hw : w=(a-1)*(b-1)) (hc : c+1≤w) (ht : (w-1)*(a+b-2)<(a+b)*(c+1)) :
    let r' := (a*b*(c+1) ⌈/⌉ (a+b+(c+1)-2))
    let V := Fin r' × (Fin a ⊕ (Fin b ⊕ Fin (c+1)))
    let R := MvPolynomial V ℂ
    let coord : V → R := MvPolynomial.X
    let P : Matrix ((Fin a × Fin b) × Fin (c+1)) V R := fun row col =>
      col.2.elim (fun i => if i=row.1.1 then coord (col.1,.inr (.inl row.1.2))*coord (col.1,.inr (.inr row.2)) else 0)
        (Sum.elim (fun j => if j=row.1.2 then coord (col.1,.inl row.1.1)*coord (col.1,.inr (.inr row.2)) else 0)
          (fun k => if k=row.2 then coord (col.1,.inl row.1.1)*coord (col.1,.inr (.inl row.1.2)) else 0))
    let G := P.map (algebraMap R (FractionRing R))
    let old := G.submatrix (fun q : (Fin a × Fin b) × Fin c => (q.1,q.2.castSucc)) id
    G.rank = old.rank + a*b := by
  apply CriticalPlateau.Full.last_rank_increment ha hab hb hw hc ht
  subst w
  exact LastSlicePositive.second_full a b (c+1) ha hb hab hc


/-- The literal rank increment of the registered strict-rectangle step on
its entire second band. The equality hypothesis is the dimension-count test. -/
theorem last_increment_of_second {a b c : ℕ} (ha : 3≤a) (hab : a≤b) (hbc : b<c)
    (hk : c+1<(a-1)*(b-1))
    (hr : a*b*(c+1) ⌈/⌉ (a+b+(c+1)-2) = (a-1)*(b-1)) :
    let r' := (a*b*(c+1) ⌈/⌉ (a+b+(c+1)-2))
    let V := Fin r' × (Fin a ⊕ (Fin b ⊕ Fin (c+1)))
    let R := MvPolynomial V ℂ
    let coord : V → R := MvPolynomial.X
    let P : Matrix ((Fin a × Fin b) × Fin (c+1)) V R := fun row col =>
      col.2.elim (fun i => if i=row.1.1 then coord (col.1,.inr (.inl row.1.2))*coord (col.1,.inr (.inr row.2)) else 0)
        (Sum.elim (fun j => if j=row.1.2 then coord (col.1,.inl row.1.1)*coord (col.1,.inr (.inr row.2)) else 0)
          (fun k => if k=row.2 then coord (col.1,.inl row.1.1)*coord (col.1,.inr (.inl row.1.2)) else 0))
    let G := P.map (algebraMap R (FractionRing R))
    let old := G.submatrix (fun q : (Fin a × Fin b) × Fin c => (q.1,q.2.castSucc)) id
    G.rank = old.rank + a*b := by
  have hb : 4≤b := by
    by_contra! small
    obtain rfl : a=3 := by omega
    obtain rfl : b=3 := by omega
    omega
  exact last_increment ha hab hb rfl hk.le ((CriticalPlateau.Full.at_least_second_iff ha hab rfl).mp hr.ge)

end CriticalPlateau.Proved

namespace LastSliceRelation

private lemma row_map {K : Type*} [Field K] {r c : ℕ} (z : Fin r → Fin c → K) :
    (Fintype.linearCombination K z : (Fin r → K) → Fin c → K) =
      fun v k => ∑ t, v t * z t k := by
  funext v k
  simp [Fintype.linearCombination_apply,Finset.sum_apply]

/-- Coordinate form of the hypothesis that the rows span the last factor. -/
theorem span_iff_surjective {K : Type*} [Field K] {r c : ℕ} (z : Fin r → Fin c → K) :
    Submodule.span K (Set.range z) = ⊤ ↔
      Function.Surjective (fun (v : Fin r → K) (k : Fin c) => ∑ t, v t * z t k) := by
  rw [← row_map z]
  exact span_range_eq_top_iff_surjective_fintypeLinearCombination K z

private lemma sum_of_realization {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    {r c : ℕ} {z : Fin r → Fin c → K} {F : Fin r → E} {T : Fin c → E}
    (hT : ∀ t, F t = ∑ k, z t k • T k) (v : Fin r → K) :
    ∑ t, v t • F t = ∑ k, (∑ t, v t*z t k) • T k := by
  simp_rw [hT,Finset.smul_sum,smul_smul,Finset.sum_smul]
  exact Finset.sum_comm

private lemma decompose (K : Type*) [Field K] {c : ℕ} (s : Fin c → K) :
    s = ∑ k, s k • Pi.single k (1:K) := by
  calc
    _ = ∑ k, Pi.single k (s k) := (Finset.univ_sum_single s).symm
    _ = _ := Finset.sum_congr rfl fun k _ => by
      simpa only [smul_eq_mul,mul_one] using Pi.single_smul' k (s k) (1:K)

/-- Values on a spanning family interpolate linearly if and only if they
satisfy every linear relation among the rows. -/
theorem interpolate_iff {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    {r c : ℕ} (z : Fin r → Fin c → K) (F : Fin r → E)
    (hz : Function.Surjective (fun (v : Fin r → K) (k : Fin c) => ∑ t, v t*z t k)) :
    (∃ T : Fin c → E, ∀ t, F t = ∑ k, z t k • T k) ↔
      ∀ v : Fin r → K, (∀ k, ∑ t, v t*z t k = 0) → ∑ t, v t • F t = 0 := by
  classical
  constructor
  · rintro ⟨T,hT⟩ v h
    rw [sum_of_realization hT]
    simp [h]
  · intro h
    let Z := Fintype.linearCombination K z
    let Y := Fintype.linearCombination K F
    have hZ : Function.Surjective Z := by simpa only [Z,row_map] using hz
    have hker : LinearMap.ker Z ≤ LinearMap.ker Y := by
      intro v hv
      apply h v
      intro k
      have hv' := congrFun (LinearMap.mem_ker.mp hv) k
      simpa only [Z,row_map,Pi.zero_apply] using hv'
    let L : (Fin c → K) →ₗ[K] E := ((LinearMap.ker Z).liftQ Y hker).comp
      (Z.quotKerEquivOfSurjective hZ).symm.toLinearMap
    have factor (v : Fin r → K) : L (Z v) = Y v := by
      change (LinearMap.ker Z).liftQ Y hker ((Z.quotKerEquivOfSurjective hZ).symm (Z v)) = Y v
      rw [LinearMap.quotKerEquivOfSurjective_symm_apply,Submodule.liftQ_apply]
    refine ⟨fun k => L (Pi.single k (1:K)),fun t => ?_⟩
    have at_row : L (z t) = F t := by
      simpa only [Z,Y,Fintype.linearCombination_apply_single,one_smul] using factor (Pi.single t 1)
    calc
      F t = L (z t) := at_row.symm
      _ = L (∑ k, z t k • Pi.single k (1:K)) := congrArg L (decompose K (z t))
      _ = _ := by rw [map_sum]; simp only [map_smul]

/-- Vector-form relation test with the spanning hypothesis stated as a submodule equality. -/
theorem interpolate_iff_of_span {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    {r c : ℕ} (z : Fin r → Fin c → K) (F : Fin r → E) (hz : Submodule.span K (Set.range z) = ⊤) :
    (∃ T : Fin c → E, ∀ t, F t = ∑ k, z t k • T k) ↔
      ∀ v : Fin r → K, (∑ t, v t • z t) = 0 → ∑ t, v t • F t = 0 := by
  rw [interpolate_iff z F ((span_iff_surjective z).mp hz)]
  apply forall_congr'
  intro v
  have same : (∀ k, ∑ t, v t*z t k = 0) ↔ (∑ t, v t • z t) = 0 := by
    rw [funext_iff]
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply]
  rw [same]

/-- Any coefficients representing a coordinate unit recover the corresponding
interpolant value as a linear combination of the prescribed values. -/
private lemma recover {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    {r c : ℕ} {z : Fin r → Fin c → K} {F : Fin r → E} {T : Fin c → E}
    (hT : ∀ t, F t = ∑ k, z t k • T k) {v : Fin r → K} {k : Fin c}
    (hv : (fun j => ∑ t, v t*z t j) = Pi.single k (1:K)) : ∑ t, v t • F t = T k := by
  calc
    ∑ t, v t • F t = ∑ j, (∑ t, v t * z t j) • T j := sum_of_realization hT v
    _ = Fintype.linearCombination K T (Pi.single k 1) :=
      Finset.sum_congr rfl fun j _ => congrArg (fun a : K => a • T j) (congrFun hv j)
    _ = T k := by simp

/-- A spanning family determines the interpolant at every coordinate. -/
theorem interpolant_unique {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    {r c : ℕ} (z : Fin r → Fin c → K) (F : Fin r → E)
    (hz : Function.Surjective (fun (v : Fin r → K) (k : Fin c) => ∑ t, v t*z t k))
    {T S : Fin c → E} (hT : ∀ t, F t = ∑ k, z t k • T k)
    (hS : ∀ t, F t = ∑ k, z t k • S k) : T = S := by
  funext k
  obtain ⟨v,hv⟩ := hz (Pi.single k 1)
  exact (recover hT hv).symm.trans (recover hS hv)

/-- If the prescribed values lie in a submodule, so do all coordinates
of every interpolant. -/
theorem interpolant_mem {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    {r c : ℕ} (z : Fin r → Fin c → K) (F : Fin r → E)
    (hz : Function.Surjective (fun (v : Fin r → K) (k : Fin c) => ∑ t, v t*z t k))
    (W : Submodule K E) (hF : ∀ t, F t ∈ W) {T : Fin c → E}
    (hT : ∀ t, F t = ∑ k, z t k • T k) (k : Fin c) : T k ∈ W := by
  obtain ⟨v,hv⟩ := hz (Pi.single k 1)
  rw [← recover hT hv]
  exact W.sum_mem fun t _ => W.smul_mem _ (hF t)

/-- Zero prescribed values force every coordinate of the interpolant to vanish. -/
theorem interpolant_zero {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    {r c : ℕ} (z : Fin r → Fin c → K) (F : Fin r → E)
    (hz : Function.Surjective (fun (v : Fin r → K) (k : Fin c) => ∑ t, v t*z t k))
    (hF : ∀ t, F t = 0) {T : Fin c → E} (hT : ∀ t, F t = ∑ k, z t k • T k) : T = 0 := by
  apply interpolant_unique z F hz hT
  simp [hF]

end LastSliceRelation

namespace LastSliceRelation

private lemma onto_iff_transpose_kernel {K I J : Type*} [Field K] [Fintype I] [Fintype J]
    (M : Matrix I J K) : Function.Surjective M.mulVec ↔ ∀ u, M.transpose.mulVec u = 0 → u = 0 := by
  classical
  change Function.Surjective M.mulVecLin ↔ ∀ u, M.transpose.mulVecLin u = 0 → u = 0
  rw [← LinearMap.range_eq_top,Submodule.eq_top_iff_finrank_eq,← LinearMap.ker_eq_bot',
    ← Submodule.finrank_eq_zero]
  have h := M.transpose.mulVecLin.finrank_range_add_finrank_ker
  have hr : Module.finrank K (LinearMap.range M.transpose.mulVecLin) =
      Module.finrank K (LinearMap.range M.mulVecLin) := M.rank_transpose
  omega

/-- Surjectivity of the full tangent is equivalent to vanishing of every
family of normal matrices satisfying the relations of the third-axis rows. -/
theorem tangent_iff_normal_relations {K : Type*} [Field K] {a b c r : ℕ}
    (x : Fin r → Fin a → K) (y : Fin r → Fin b → K) (z : Fin r → Fin c → K)
    (hz : Submodule.span K (Set.range z) = ⊤)
    (G : Matrix ((Fin a × Fin b) × Fin c) (Fin r × (Fin a ⊕ (Fin b ⊕ Fin c))) K)
    (entry : ∀ i j k t v, G ((i,j),k) (t,v) =
      v.elim (fun i' => if i'=i then y t j*z t k else 0)
        (Sum.elim (fun j' => if j'=j then x t i*z t k else 0)
          (fun k' => if k'=k then x t i*y t j else 0))) :
    Function.Surjective G.mulVec ↔ ∀ F : Fin r → Fin a × Fin b → K,
      (∀ t s, ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*F t ij = 0) →
      (∀ t i, ∑ j, y t j*F t (i,j) = 0) →
      (∀ t j, ∑ i, x t i*F t (i,j) = 0) →
      (∀ v : Fin r → K, (∀ k, ∑ t, v t*z t k = 0) → ∑ t, v t • F t = 0) →
      F = 0 := by
  classical
  rw [onto_iff_transpose_kernel]
  have hspan := (span_iff_surjective z).mp hz
  let sample (T : ((Fin a × Fin b) × Fin c) → K) (t : Fin r) (ij : Fin a × Fin b) :=
    ∑ k, z t k*T (ij,k)
  have realization (T : ((Fin a × Fin b) × Fin c) → K) (t : Fin r) :
      sample T t = ∑ k, z t k • (fun ij : Fin a × Fin b => T (ij,k)) := by
    funext ij
    simp only [sample,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  have dual (T : ((Fin a × Fin b) × Fin c) → K) :
      G.transpose.mulVec T = 0 ↔
        (∀ t s, ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*sample T t ij = 0) ∧
        (∀ t i, ∑ j, y t j*sample T t (i,j) = 0) ∧
        (∀ t j, ∑ i, x t i*sample T t (i,j) = 0) := by
    rw [LastSliceDual.transpose_kernel_iff x y z G entry T]
    dsimp only
    rw [LastSliceDual.sampled_outer_iff x y z hz T]
  constructor
  · intro trivialKer F outer row col rel
    obtain ⟨P,hP⟩ := (interpolate_iff z F hspan).mpr rel
    let T (q : (Fin a × Fin b) × Fin c) := P q.2 q.1
    have hF : F = sample T := by
      funext t
      exact (hP t).trans (realization T t).symm
    rw [hF] at outer row col
    have hT := trivialKer T ((dual T).mpr ⟨outer,row,col⟩)
    rw [hF,hT]
    funext t ij
    simp [sample]
  · intro trivialFamily T hT
    obtain ⟨outer,row,col⟩ := (dual T).mp hT
    have rel := (interpolate_iff z (sample T) hspan).mp
      ⟨fun k ij => T (ij,k),realization T⟩
    have hF := trivialFamily (sample T) outer row col rel
    have hP := interpolant_zero z (sample T) hspan (fun t => congrFun hF t) (realization T)
    funext ⟨ij,k⟩
    exact congrFun (congrFun hP k) ij

end LastSliceRelation

namespace LastSliceNormal

/-- Coordinate specialization to independent standard vectors certifies that
the original polynomial rows remain independent over the fraction field. -/
private lemma independent_by_cells {J I V : Type} [Fintype J] [DecidableEq J]
    (M : J → I → MvPolynomial V ℂ) (cell : J → I) (p : V → ℂ)
    (hm : ∀ u v, MvPolynomial.eval p (M u (cell v)) = if u=v then 1 else 0) :
    let R := MvPolynomial V ℂ
    let K := FractionRing R
    LinearIndependent K (fun u i => algebraMap R K (M u i)) := by
  classical
  intro R K
  let A : Matrix J J R := fun u v => M u (cell v)
  have h : A.map (MvPolynomial.eval p) = 1 := by
    ext u v
    rw [Matrix.map_apply,Matrix.one_apply]
    exact hm u v
  have det : A.det ≠ 0 := by
    intro hz
    have ev : MvPolynomial.eval p A.det = 1 := by
      rw [RingHom.map_det,RingHom.mapMatrix_apply,h,Matrix.det_one]
    rw [hz,map_zero] at ev
    exact zero_ne_one ev
  let φ := algebraMap R K
  have nz : (A.map φ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply,← RingHom.map_det]
    exact fun hz => det (IsFractionRing.injective R K (hz.trans φ.map_zero.symm))
  let f : (I → K) →ₗ[K] (J → K) := LinearMap.pi (fun v => LinearMap.proj (R:=K) (cell v))
  apply LinearIndependent.of_comp f
  exact Matrix.linearIndependent_rows_of_det_ne_zero nz

private lemma crossing_cells {A B S : Type} (i₀ : A) (j₀ : B)
    (e : S ↪ {i : A // i ≠ i₀} × {j : B // j ≠ j₀}) :
    Function.Injective (Sum.elim (fun i : A => (i,j₀))
      (Sum.elim (fun j : {j : B // j ≠ j₀} => (i₀,j.val))
        (fun s : S => ((e s).1.val,(e s).2.val)))) := by
  rintro (i|j|s) (i'|j'|s') h
  · exact congrArg Sum.inl (congrArg Prod.fst h)
  · exact False.elim (j'.property (congrArg Prod.snd h).symm)
  · exact False.elim ((e s').2.property (congrArg Prod.snd h).symm)
  · exact False.elim (j.property (congrArg Prod.snd h))
  · exact congrArg (fun q => Sum.inr (Sum.inl q)) (Subtype.ext (congrArg Prod.snd h))
  · exact False.elim ((e s').1.property (congrArg Prod.fst h).symm)
  · exact False.elim ((e s).2.property (congrArg Prod.snd h))
  · exact False.elim ((e s).1.property (congrArg Prod.fst h))
  · apply congrArg (fun q => Sum.inr (Sum.inr q))
    apply e.injective
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

/-- One product equation and one column equation can be recovered from the
row equations and the remaining columns when the pivot is nonzero. -/
private lemma remove_two {A B S K E : Type} [Fintype A] [Fintype B] [DecidableEq B]
    [Field K] [AddCommGroup E] [Module K E] (j₀ : B) (t : S)
    (P : S → E) (row : A → E) (col : B → E) (x : A → K) (y : B → K)
    (hy : y j₀ ≠ 0) (left : ∑ i, x i • row i=P t) (right : ∑ j, y j • col j=P t) :
    Submodule.span K (Set.range (Sum.elim P (Sum.elim row col))) =
      Submodule.span K (Set.range (Sum.elim row (Sum.elim
        (fun j : {j : B // j≠j₀} => col j) (fun s : {s : S // s≠t} => P s)))) := by
  classical
  let g := Sum.elim row (Sum.elim (fun j : {j : B // j≠j₀} => col j) (fun s : {s : S // s≠t} => P s))
  let W := Submodule.span K (Set.range g)
  have rowmem (i : A) : row i ∈ W := Submodule.subset_span ⟨Sum.inl i,rfl⟩
  have colmem (j : B) (h : j≠j₀) : col j ∈ W := Submodule.subset_span ⟨Sum.inr (Sum.inl ⟨j,h⟩),rfl⟩
  have prodmem : P t ∈ W := left ▸ W.sum_mem fun i _ => W.smul_mem _ (rowmem i)
  have off : ∑ j ∈ Finset.univ.erase j₀, y j • col j ∈ W :=
    W.sum_mem fun j hj => W.smul_mem _ (colmem j (Finset.mem_erase.mp hj).1)
  have pivot : col j₀ ∈ W := by
    have hsum : ∑ j, y j • col j ∈ W := right ▸ prodmem
    rw [←Finset.sum_erase_add _ _ (Finset.mem_univ j₀)] at hsum
    have hone := (W.add_mem_iff_right off).mp hsum
    simpa only [←mul_smul,inv_mul_cancel₀ hy,one_smul] using W.smul_mem (y j₀)⁻¹ hone
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨s|i|j,rfl⟩
    · change P s ∈ W
      by_cases h : s=t
      · simpa only [h] using prodmem
      · exact Submodule.subset_span ⟨Sum.inr (Sum.inr ⟨s,h⟩),rfl⟩
    · exact rowmem i
    · change col j ∈ W
      by_cases h : j=j₀
      · simpa only [h] using pivot
      · exact colmem j h
  · apply Submodule.span_mono
    rintro _ ⟨i|j|s,rfl⟩
    · exact ⟨Sum.inr (Sum.inl i),rfl⟩
    · exact ⟨Sum.inr (Sum.inr j.val),rfl⟩
    · exact ⟨Sum.inl s.val,rfl⟩

private lemma map_indicator {R F : Type} [Semiring R] [Semiring F] (φ : R →+* F)
    (P : Prop) [Decidable P] :
    φ (if P then 1 else 0) = (if P then 1 else 0) := by
  by_cases h : P <;> simp [h]

private lemma delta_product {A B : Type} [DecidableEq A] [DecidableEq B] (u v : A × B) :
    (if u.1=v.1 then (1:ℂ) else 0)*(if u.2=v.2 then (1:ℂ) else 0) = if u=v then 1 else 0 := by
  rcases u with ⟨i,j⟩
  rcases v with ⟨k,l⟩
  by_cases h₁ : i=k <;> by_cases h₂ : j=l <;> simp [h₁,h₂]

private lemma remaining_dimension {a b r d : ℕ} (ha : 0<a) (hb : 0<b) (hr : 0<r)
    (dim : r+a+b-2+d = a*b) : d = (a-1)*(b-1)+1-r := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
  rw [show (i+1)*(j+1)=i*j+i+j+1 by ring] at dim
  simp only [Nat.succ_sub_one]
  omega

end LastSliceNormal

namespace LastSliceNormal

/-- At a generic product point, the row and column derivatives together
with all the sampled product directions have the expected dimension.
The ordinary dual and the matrix realization give the same normal count. -/
theorem normal_finrank (a b c r : ℕ) (ha : 0<a) (hb : 0<b)
    (hr : r≤(a-1)*(b-1)+1) (t : Fin r) :
    let V := Fin r × (Fin a ⊕ (Fin b ⊕ Fin c))
    let R := MvPolynomial V ℂ
    let K := FractionRing R
    let x (s : Fin r) (i : Fin a) := algebraMap R K (MvPolynomial.X (s,Sum.inl i) : R)
    let y (s : Fin r) (j : Fin b) := algebraMap R K (MvPolynomial.X (s,Sum.inr (Sum.inl j)) : R)
    let P (s : Fin r) (ij : Fin a × Fin b) := x s ij.1*y s ij.2
    let row (i : Fin a) (ij : Fin a × Fin b) := (if ij.1=i then 1 else 0)*y t ij.2
    let col (j : Fin b) (ij : Fin a × Fin b) := x t ij.1*(if ij.2=j then 1 else 0)
    let M : Matrix (Fin r ⊕ (Fin a ⊕ Fin b)) (Fin a × Fin b) K := Sum.elim P (Sum.elim row col)
    let W := Submodule.span K (Set.range (fun s => M s))
    Module.finrank K W = r+a+b-2 ∧
      Module.finrank K W.dualAnnihilator = (a-1)*(b-1)+1-r ∧
      Module.finrank K (LinearMap.ker M.mulVecLin) = (a-1)*(b-1)+1-r := by
  classical
  intro V R K x y P row col M W
  let i₀ : Fin a := ⟨0,ha⟩
  let j₀ : Fin b := ⟨0,hb⟩
  let I := {i : Fin a // i≠i₀}
  let J := {j : Fin b // j≠j₀}
  let S := {s : Fin r // s≠t}
  let L := Fin a ⊕ (J ⊕ S)
  have points : 0<r := (Nat.zero_le t.val).trans_lt t.isLt
  have cI : Fintype.card I = a-1 := by
    change Fintype.card {i : Fin a // ¬ i=i₀} = _
    rw [Fintype.card_subtype_compl,Fintype.card_subtype_eq,Fintype.card_fin]
  have cJ : Fintype.card J = b-1 := by
    change Fintype.card {j : Fin b // ¬ j=j₀} = _
    rw [Fintype.card_subtype_compl,Fintype.card_subtype_eq,Fintype.card_fin]
  have cS : Fintype.card S = r-1 := by
    change Fintype.card {s : Fin r // ¬ s=t} = _
    rw [Fintype.card_subtype_compl,Fintype.card_subtype_eq,Fintype.card_fin]
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α:=S) (β:=I×J)
    (by rw [Fintype.card_prod,cI,cJ,cS]; omega)
  let pos (s : Fin r) : Fin a × Fin b :=
    if h : s=t then (i₀,j₀) else ((e ⟨s,h⟩).1.val,(e ⟨s,h⟩).2.val)
  let cell : L → Fin a × Fin b := Sum.elim (fun i => (i,j₀))
    (Sum.elim (fun j : J => (i₀,j.val)) (fun s : S => ((e s).1.val,(e s).2.val)))
  have inj : Function.Injective cell := crossing_cells i₀ j₀ e
  let p : V → ℂ := fun s => s.2.elim (fun i => if i=(pos s.1).1 then 1 else 0)
    (Sum.elim (fun j => if j=(pos s.1).2 then 1 else 0) (fun _ => 0))
  let xp (s : Fin r) (i : Fin a) : R := MvPolynomial.X (s,Sum.inl i)
  let yp (s : Fin r) (j : Fin b) : R := MvPolynomial.X (s,Sum.inr (Sum.inl j))
  let pro (s : S) (ij : Fin a × Fin b) := xp s ij.1*yp s ij.2
  let ro (i : Fin a) (ij : Fin a × Fin b) := (if ij.1=i then 1 else 0)*yp t ij.2
  let co (j : J) (ij : Fin a × Fin b) := xp t ij.1*(if ij.2=j.val then 1 else 0)
  let mat : L → Fin a × Fin b → R := Sum.elim ro (Sum.elim co pro)
  have pos_t : pos t = (i₀,j₀) := dif_pos rfl
  have pos_other (s : S) : pos s.val = ((e s).1.val,(e s).2.val) := dif_neg s.property
  have ex (s : Fin r) (i : Fin a) : MvPolynomial.eval p (xp s i) = if i=(pos s).1 then 1 else 0 := by
    simp [xp,p]
  have ey (s : Fin r) (j : Fin b) : MvPolynomial.eval p (yp s j) = if j=(pos s).2 then 1 else 0 := by
    simp [yp,p]
  have at_cell (l : L) (ij : Fin a × Fin b) :
      MvPolynomial.eval p (mat l ij) = if ij=cell l then 1 else 0 := by
    rcases l with i|j|s
    · change MvPolynomial.eval p ((if ij.1=i then 1 else 0)*yp t ij.2) = if ij=(i,j₀) then 1 else 0
      rw [map_mul, map_indicator,ey,pos_t]
      exact delta_product ij (i,j₀)
    · change MvPolynomial.eval p (xp t ij.1*(if ij.2=j.val then 1 else 0)) = if ij=(i₀,j.val) then 1 else 0
      rw [map_mul,ex,pos_t,map_indicator]
      exact delta_product ij (i₀,j.val)
    · change MvPolynomial.eval p (xp s.val ij.1*yp s.val ij.2) = if ij=((e s).1.val,(e s).2.val) then 1 else 0
      rw [map_mul,ex,ey,pos_other]
      exact delta_product ij ((e s).1.val,(e s).2.val)
  have id₀ (u v : L) : MvPolynomial.eval p (mat u (cell v)) = if u=v then 1 else 0 := by
    rw [at_cell]
    by_cases h : u=v
    · subst v
      simp
    · simp only [if_neg h,if_neg (fun w => h (inj w).symm : cell v≠cell u)]
  have independent := independent_by_cells mat cell p id₀
  let g : L → Fin a × Fin b → K := Sum.elim row
    (Sum.elim (fun j : J => col j) (fun s : S => P s))
  have thin : LinearIndependent K g := by
    have same : g = (fun u i => algebraMap R K (mat u i)) := by
      funext l ij
      rcases l with i|j|s
      · change _ = algebraMap R K ((if ij.1=i then 1 else 0)*yp t ij.2)
        rw [map_mul,map_indicator]
        rfl
      · change _ = algebraMap R K (xp t ij.1*(if ij.2=j.val then 1 else 0))
        rw [map_mul,map_indicator]
        rfl
      · exact (map_mul (algebraMap R K) (xp s.val ij.1) (yp s.val ij.2)).symm
    rw [same]
    exact independent
  have nonzero : y t j₀ ≠ 0 := by
    intro h
    exact MvPolynomial.X_ne_zero _ (IsFractionRing.injective R K (h.trans (map_zero (algebraMap R K)).symm))
  have via_rows : ∑ i, x t i • row i=P t := by
    funext ij
    simp [row,P,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,ite_mul,mul_ite,Finset.sum_ite_eq]
  have via_cols : ∑ j, y t j • col j=P t := by
    funext ij
    simp [col,P,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,ite_mul,Finset.sum_ite_eq,mul_comm]
  have full : W = Submodule.span K (Set.range g) :=
    remove_two j₀ t P row col (x t) (y t) nonzero via_rows via_cols
  have dim : Module.finrank K W = r+a+b-2 := by
    rw [full,finrank_span_eq_card thin]
    change Fintype.card (Fin a ⊕ (J ⊕ S)) = _
    rw [Fintype.card_sum,Fintype.card_sum,Fintype.card_fin,cJ,cS]
    omega
  have ambient : Module.finrank K (Fin a × Fin b → K)=a*b := by simp
  refine ⟨dim,remaining_dimension ha hb points ?_,remaining_dimension ha hb points ?_⟩
  · rw [←dim,←ambient]
    exact Subspace.finrank_add_finrank_dualAnnihilator_eq W
  · have rank : M.rank = Module.finrank K W := M.rank_eq_finrank_span_row
    rw [←dim,←rank,←ambient]
    exact M.mulVecLin.finrank_range_add_finrank_ker

end LastSliceNormal

namespace LastSliceNormal

/-- The matrix kernel is exactly the space of bilinear forms with the
sampled-product, row and column contractions required at the selected point. -/
theorem mem_normal_iff {K : Type*} [Field K] {a b r : ℕ}
    (x : Fin r → Fin a → K) (y : Fin r → Fin b → K) (t : Fin r) (H : Fin a × Fin b → K) :
    let P (s : Fin r) (ij : Fin a × Fin b) := x s ij.1*y s ij.2
    let row (i : Fin a) (ij : Fin a × Fin b) := (if ij.1=i then 1 else 0)*y t ij.2
    let col (j : Fin b) (ij : Fin a × Fin b) := x t ij.1*(if ij.2=j then 1 else 0)
    let M : Matrix (Fin r ⊕ (Fin a ⊕ Fin b)) (Fin a × Fin b) K := Sum.elim P (Sum.elim row col)
    H ∈ LinearMap.ker M.mulVecLin ↔
      (∀ s, ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*H ij = 0) ∧
      (∀ i, ∑ j, y t j*H (i,j) = 0) ∧ (∀ j, ∑ i, x t i*H (i,j) = 0) := by
  classical
  intro P row col M
  have prod₁ (s : Fin r) : M.mulVec H (.inl s) = ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*H ij := rfl
  have row₁ (i : Fin a) : M.mulVec H (.inr (.inl i)) = ∑ j, y t j*H (i,j) := by
    change (∑ ij : Fin a × Fin b, ((if ij.1=i then 1 else 0)*y t ij.2)*H ij) = _
    rw [Fintype.sum_prod_type]
    simp [ite_mul,Finset.sum_ite_eq']
  have col₁ (j : Fin b) : M.mulVec H (.inr (.inr j)) = ∑ i, x t i*H (i,j) := by
    change (∑ ij : Fin a × Fin b, (x t ij.1*(if ij.2=j then 1 else 0))*H ij) = _
    rw [Fintype.sum_prod_type]
    simp [mul_ite,ite_mul,Finset.sum_ite_eq']
  change M.mulVec H = 0 ↔ _
  constructor
  · intro h
    exact ⟨fun s => (prod₁ s).symm.trans (congrFun h _),
      fun i => (row₁ i).symm.trans (congrFun h _),fun j => (col₁ j).symm.trans (congrFun h _)⟩
  · rintro ⟨p,u,v⟩
    funext l
    rcases l with s|i|j
    · exact (prod₁ s).trans (p s)
    · exact (row₁ i).trans (u i)
    · exact (col₁ j).trans (v j)

end LastSliceNormal

namespace CriticalLastSlice

open Module Submodule
open LinearMap (ker range)

variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]

/-- A deleted slice contributes its entire row count precisely when every
linear relation among the original rows has zero coefficients on that slice. -/
theorem rank_increment_iff_row_relations {c : ℕ} (M : Matrix (I × Fin (c+1)) J K) (l : Fin (c+1)) :
    M.rank = (M.submatrix (fun q : I × Fin c => (q.1,l.succAbove q.2)) id).rank + Fintype.card I ↔
    ∀ u : I × Fin (c+1) → K, M.transpose.mulVec u=0 → ∀ i, u (i,l)=0 := by
  classical
  let N := M.submatrix (fun q : I × Fin c => (q.1,l.succAbove q.2)) id
  let F := M.transpose.mulVecLin
  let G := N.transpose.mulVecLin
  let keep (u : I × Fin (c+1) → K) (q : I × Fin c) := u (q.1,l.succAbove q.2)
  let pad (v : I × Fin c → K) (q : I × Fin (c+1)) :=
    l.insertNth (α:=fun _ => K) 0 (fun j => v (q.1,j)) q.2
  have zero_at (v : I × Fin c → K) (i : I) : pad v (i,l)=0 := Fin.insertNth_apply_same ..
  have at_keep (v : I × Fin c → K) (i : I) (j : Fin c) : pad v (i,l.succAbove j)=v (i,j) :=
    Fin.insertNth_apply_succAbove ..
  have restore (u : I × Fin (c+1) → K) (hu : ∀ i, u (i,l)=0) : pad (keep u) = u := by
    funext ⟨i,j⟩
    refine Fin.succAboveCases l ?_ (fun j => ?_) j
    · exact (zero_at _ _).trans (hu i).symm
    · exact at_keep _ _ _
  have comp (v : I × Fin c → K) : F (pad v)=G v := by
    funext t
    change (∑ q : I × Fin (c+1), M q t*pad v q) = ∑ q : I × Fin c, M (q.1,l.succAbove q.2) t*v q
    rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.sum_univ_succAbove _ l]
    simp only [zero_at,at_keep,mul_zero,zero_add]
  let project : ker F →ₗ[K] (I → K) :=
    { toFun := fun u i => u.val (i,l)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have zzero (u : ker project) (i : I) : u.val.val (i,l)=0 := congrFun (show project u.val = 0 from u.property) i
  let e : ker project ≃ₗ[K] ker G :=
    { toFun := fun u => ⟨keep u.val.val, (comp _).symm.trans ((congrArg F (restore _ (zzero u))).trans u.val.property)⟩
      invFun := fun v => ⟨⟨pad v.val,(comp v.val).trans v.property⟩,funext (zero_at v.val)⟩
      left_inv := fun u => Subtype.ext (Subtype.ext (restore _ (zzero u)))
      right_inv := fun v => Subtype.ext (funext fun ⟨i,j⟩ => at_keep v.val i j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have HF := F.finrank_range_add_finrank_ker
  have HG := G.finrank_range_add_finrank_ker
  have he := e.finrank_eq
  have hF : finrank K (range F)=M.rank := M.rank_transpose
  have hG : finrank K (range G)=N.rank := N.rank_transpose
  rw [hF,finrank_pi,Fintype.card_prod,Fintype.card_fin,Nat.mul_succ] at HF
  rw [hG,finrank_pi,Fintype.card_prod,Fintype.card_fin] at HG
  change M.rank=N.rank+Fintype.card I ↔ _
  constructor
  · intro hr
    have ht : ker project=⊤ := Submodule.eq_top_of_finrank_eq (by omega)
    intro u hu i
    let v : ker F := ⟨u,hu⟩
    have hv : v∈ker project := by rw [ht]; trivial
    exact congrFun (show project v=0 from hv) i
  · intro vanish
    have ht : ker project=⊤ := by
      apply top_unique
      intro u _
      exact funext (vanish u.val u.property)
    rw [ht,finrank_top] at he
    omega

/-- The last-index form uses the usual inclusion of the old c slices. -/
theorem rank_increment_iff_last_relations {c : ℕ} (M : Matrix (I × Fin (c+1)) J K) :
    M.rank = (M.submatrix (fun q : I × Fin c => (q.1,q.2.castSucc)) id).rank + Fintype.card I ↔
    ∀ u : I × Fin (c+1) → K, M.transpose.mulVec u=0 → ∀ i, u (i,Fin.last c)=0 := by
  simpa only [Fin.succAbove_last] using rank_increment_iff_row_relations M (Fin.last c)

private lemma surjective_iff_no_relations (M : Matrix I J K) :
    Function.Surjective M.mulVec ↔ ∀ u, M.transpose.mulVec u=0 → u=0 := by
  classical
  constructor
  · intro hs u hu
    obtain ⟨B,hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hs
    have hleft : B.transpose*M.transpose=1 := by rw [← Matrix.transpose_mul,hB,Matrix.transpose_one]
    calc
      u = (1 : Matrix I I K).mulVec u := (Matrix.one_mulVec u).symm
      _ = B.transpose.mulVec (M.transpose.mulVec u) := by rw [Matrix.mulVec_mulVec,hleft]
      _ = 0 := by rw [hu,Matrix.mulVec_zero]
  · intro hz
    have HK : ker M.transpose.mulVecLin = ⊥ := by
      apply bot_unique
      intro u hu
      exact (Submodule.mem_bot K).mpr (hz u hu)
    have hd := LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp HK)
    change M.transpose.rank = finrank K (I → K) at hd
    rw [Matrix.rank_transpose] at hd
    change Function.Surjective M.mulVecLin
    apply LinearMap.range_eq_top.mp
    exact Submodule.eq_top_of_finrank_eq hd

/-- Equal ranks for the deletions make one maximal slice gain equivalent to
surjectivity: every coordinate of every row relation must then vanish. -/
theorem rank_increment_iff_surjective {c : ℕ} (M : Matrix (I × Fin (c+1)) J K)
    (equalRanks : ∀ l : Fin (c+1),
      (M.submatrix (fun q : I × Fin c => (q.1,l.succAbove q.2)) id).rank =
      (M.submatrix (fun q : I × Fin c => (q.1,q.2.castSucc)) id).rank) :
    M.rank = (M.submatrix (fun q : I × Fin c => (q.1,q.2.castSucc)) id).rank + Fintype.card I ↔
      Function.Surjective M.mulVec := by
  rw [surjective_iff_no_relations]
  constructor
  · intro h u hu
    funext ⟨i,l⟩
    exact (rank_increment_iff_row_relations M l).mp (by rw [equalRanks]; exact h) u hu i
  · intro h
    apply (rank_increment_iff_last_relations M).mpr
    intro u hu i
    exact congrFun (h u hu) (i,Fin.last c)

end CriticalLastSlice

namespace CriticalLastSlice

/-- Mapping the coefficients of a rectangular matrix cannot enlarge its rank.
A factorization through the original column space remains a factorization after mapping. -/
private lemma map_rank_le {K L I J : Type*} [Field K] [Field L] [Fintype I] [Fintype J]
    (M : Matrix I J K) (f : K →+* L) : (M.map f).rank ≤ M.rank := by
  classical
  let S := LinearMap.range M.mulVecLin
  let B : Module.Basis (Fin M.rank) K S := Module.finBasis K S
  let v (j : J) : S := ⟨M.col j,Pi.single j 1,Matrix.mulVec_single_one M j⟩
  let A : Matrix I (Fin M.rank) K := fun i t => ((B t : S) : I → K) i
  let D : Matrix (Fin M.rank) J K := fun t j => B.repr (v j) t
  have he : M=A*D := by
    ext i j
    have hh := congrArg (fun w : S => (w : I → K) i) (B.sum_repr (v j))
    rw [Matrix.mul_apply]
    change M i j = ∑ t,((B t : S) : I → K) i * (B.repr (v j)) t
    change ((∑ t, B.repr (v j) t • B t : S) : I → K) i = M i j at hh
    simpa only [Submodule.coe_sum,Submodule.coe_smul_of_tower,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm] using hh.symm
  calc
    _ = ((A*D).map f).rank := congrArg (fun P : Matrix I J K => (P.map f).rank) he
    _ = (A.map f*D.map f).rank := by rw [Matrix.map_mul]
    _ ≤ (A.map f).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin M.rank) := Matrix.rank_le_card_width _
    _ = _ := Fintype.card_fin _

/-- A field automorphism preserves the rank of a rectangular matrix. -/
lemma rank_map_equiv {K L I J : Type*} [Field K] [Field L] [Fintype I] [Fintype J]
    (M : Matrix I J K) (f : K ≃+* L) : (M.map f).rank = M.rank := by
  apply le_antisymm (map_rank_le M f.toRingHom)
  have h := map_rank_le (M.map f) f.symm.toRingHom
  have he : (M.map f).map f.symm.toRingHom = M := by ext; simp
  rwa [he] at h

open MvPolynomial

/-- Relabeling the third tensor coordinate relabels the third-factor columns and
induces the same permutation of the independent polynomial indeterminates. -/
lemma rank_restrict_permutation {a b c r k : ℕ}
    (P : Matrix ((Fin a × Fin b) × Fin c) (Fin r × (Fin a ⊕ (Fin b ⊕ Fin c)))
      (MvPolynomial (Fin r × (Fin a ⊕ (Fin b ⊕ Fin c))) ℂ))
    (entry : ∀ i j l t v, P ((i,j),l) (t,v) =
      v.elim (fun ii => if ii=i then X (t,.inr (.inl j))*X (t,.inr (.inr l)) else 0)
        (Sum.elim (fun jj => if jj=j then X (t,.inl i)*X (t,.inr (.inr l)) else 0)
          (fun ll => if ll=l then X (t,.inl i)*X (t,.inr (.inl j)) else 0)))
    (σ : Equiv.Perm (Fin c)) (f : Fin k → Fin c) :
    let R := MvPolynomial (Fin r × (Fin a ⊕ (Fin b ⊕ Fin c))) ℂ
    let G := P.map (algebraMap R (FractionRing R))
    (G.submatrix (fun q : (Fin a × Fin b) × Fin k => (q.1,σ (f q.2))) id).rank =
      (G.submatrix (fun q : (Fin a × Fin b) × Fin k => (q.1,f q.2)) id).rank := by
  classical
  let V := Fin r × (Fin a ⊕ (Fin b ⊕ Fin c))
  let R := MvPolynomial V ℂ
  let K := FractionRing R
  let γ : V ≃ V := (Equiv.refl (Fin r)).prodCongr
    (Equiv.sumCongr (Equiv.refl (Fin a)) (Equiv.sumCongr (Equiv.refl (Fin b)) σ))
  let ρ : R ≃+* R := (MvPolynomial.renameEquiv ℂ γ).toRingEquiv
  let φ : K ≃+* K := IsFractionRing.ringEquivOfRingEquiv ρ
  let G := P.map (algebraMap R K)
  have hX (q : V) : ρ (X q) = X (γ q) := MvPolynomial.rename_X γ q
  have γa (t : Fin r) (w : Fin a) : γ (t,.inl w)=(t,.inl w) := rfl
  have γb (t : Fin r) (w : Fin b) : γ (t,.inr (.inl w))=(t,.inr (.inl w)) := rfl
  have γc (t : Fin r) (w : Fin c) : γ (t,.inr (.inr w))=(t,.inr (.inr (σ w))) := rfl
  have hcoord (i : Fin a) (j : Fin b) (l : Fin c) (t : Fin r) (v : Fin a ⊕ (Fin b ⊕ Fin c)) :
      ρ (P ((i,j),l) (t,v)) = P ((i,j),σ l) (γ (t,v)) := by
    rcases v with u|u|u
    · by_cases h : u=i <;> simp [γa,entry,h,hX,γb,γc]
    · by_cases h : u=j <;> simp [γb,entry,h,hX,γa,γc]
    · by_cases h : u=l <;> simp [γc,entry,h,hX,γa,γb]
  have he (i : Fin a) (j : Fin b) (l : Fin c) (t : Fin r) (v : Fin a ⊕ (Fin b ⊕ Fin c)) :
      φ (G ((i,j),l) (t,v)) = G ((i,j),σ l) (γ (t,v)) := by
    change φ (algebraMap R K (P ((i,j),l) (t,v))) = algebraMap R K (P ((i,j),σ l) (γ (t,v)))
    rw [show φ (algebraMap R K (P ((i,j),l) (t,v))) = algebraMap R K (ρ (P ((i,j),l) (t,v))) from
      IsFractionRing.ringEquivOfRingEquiv_algebraMap ρ _,hcoord]
  let G₀ := G.submatrix (fun q : (Fin a × Fin b) × Fin k => (q.1,f q.2)) id
  let G₁ := G.submatrix (fun q : (Fin a × Fin b) × Fin k => (q.1,σ (f q.2))) id
  have hmat : G₀.map φ = G₁.submatrix (Equiv.refl _) γ := by
    ext ⟨⟨i,j⟩,u⟩ ⟨t,v⟩
    exact he i j (f u) t v
  calc
    G₁.rank = (G₁.submatrix (Equiv.refl _) γ).rank := (Matrix.rank_submatrix G₁ (Equiv.refl _) γ).symm
    _ = (G₀.map φ).rank := congrArg Matrix.rank hmat.symm
    _ = G₀.rank := rank_map_equiv G₀ φ

/-- Every single-slice deletion of the generic three-tensor tangent has the rank of the last deletion. -/
lemma rank_delete_eq_last {a b c r : ℕ}
    (P : Matrix ((Fin a × Fin b) × Fin (c+1)) (Fin r × (Fin a ⊕ (Fin b ⊕ Fin (c+1))))
      (MvPolynomial (Fin r × (Fin a ⊕ (Fin b ⊕ Fin (c+1)))) ℂ))
    (entry : ∀ i j l t v, P ((i,j),l) (t,v) =
      v.elim (fun ii => if ii=i then X (t,.inr (.inl j))*X (t,.inr (.inr l)) else 0)
        (Sum.elim (fun jj => if jj=j then X (t,.inl i)*X (t,.inr (.inr l)) else 0)
          (fun ll => if ll=l then X (t,.inl i)*X (t,.inr (.inl j)) else 0)))
    (l : Fin (c+1)) :
    let R := MvPolynomial (Fin r × (Fin a ⊕ (Fin b ⊕ Fin (c+1)))) ℂ
    let G := P.map (algebraMap R (FractionRing R))
    (G.submatrix (fun q : (Fin a × Fin b) × Fin c => (q.1,l.succAbove q.2)) id).rank =
      (G.submatrix (fun q : (Fin a × Fin b) × Fin c => (q.1,q.2.castSucc)) id).rank := by
  let σ := (finSuccEquiv' (Fin.last c)).trans (finSuccEquiv' l).symm
  have hh (v : Fin c) : σ v.castSucc=l.succAbove v := by
    simp only [σ,Equiv.trans_apply,finSuccEquiv'_last_apply_castSucc,finSuccEquiv'_symm_some]
  simpa only [hh] using rank_restrict_permutation P entry σ Fin.castSucc

end CriticalLastSlice

namespace CriticalLastSlice

open MvPolynomial

/-- Independent third-factor variables contain a square coordinate minor
that specializes to the identity. -/
theorem third_span (a b c r : ℕ) (hc : c≤r) :
    let V := Fin r × (Fin a ⊕ (Fin b ⊕ Fin c))
    let R := MvPolynomial V ℂ
    let K := FractionRing R
    let z (t : Fin r) (k : Fin c) := algebraMap R K (X (t,.inr (.inr k)) : R)
    Submodule.span K (Set.range z) = ⊤ := by
  classical
  intro V R K z
  let Z : Matrix (Fin c) (Fin r) R := fun k t => X (t,.inr (.inr k))
  let embed := Fin.castLEEmb hc
  let p : V → ℂ := fun (t,u) => u.elim (fun _ => 0) (Sum.elim (fun _ => 0)
    (fun k => if t=embed k then 1 else 0))
  have specialized : Function.Surjective (Z.map (eval p)).mulVec := by
    intro v
    let lift (t : Fin r) : ℂ := if h : t.val<c then v ⟨t.val,h⟩ else 0
    refine ⟨lift,?_⟩
    funext k
    change (∑ t, eval p (Z k t) * lift t) = v k
    calc
      (∑ t, eval p (Z k t) * lift t) = lift (embed k) := by
        simp [Z,p,ite_mul]
      _ = v k := by simp [lift,embed]
  have generic := (CriticalTensor.Unrestricted.generic_surjective_iff Z).mpr ⟨p,specialized⟩
  apply (LastSliceRelation.span_iff_surjective z).mpr
  intro v
  obtain ⟨u,hu⟩ := generic v
  refine ⟨u,?_⟩
  funext k
  have he := congrFun hu k
  change (∑ t, z t k*u t) = v k at he
  simpa only [mul_comm] using he

/-- In the balanced range there are enough points to span the third factor,
and the critical-boundary rank bounds the dimension count above. -/
lemma point_bounds {a b k : ℕ} (ha : 3≤a) (hb : 3≤b) (hk : k≤(a-1)*(b-1)) :
    k ≤ a*b*k ⌈/⌉ (a+b+k-2) ∧
      a*b*k ⌈/⌉ (a+b+k-2) ≤ (a-1)*(b-1)+1 := by
  obtain ⟨A,rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨B,rfl⟩ := Nat.exists_eq_add_of_le hb
  let w := (A+2)*(B+2)
  have small : k≤w := by simpa only [w,show 3+A-1=A+2 by omega,show 3+B-1=B+2 by omega] using hk
  let D := 4+A+B+k
  have denom : 3+A+(3+B)+k-2=D := by dsimp [D]; omega
  rw [denom,show 3+A-1=A+2 by omega,show 3+B-1=B+2 by omega]
  change k≤(3+A)*(3+B)*k ⌈/⌉ D ∧ (3+A)*(3+B)*k ⌈/⌉ D≤w+1
  have pos : 0<D := by dsimp [D]; omega
  have decomp : (3+A)*(3+B)=w+(5+A+B) := by dsimp [w]; ring
  have less : D≤(3+A)*(3+B) := by rw [decomp]; dsimp [D]; omega
  constructor
  · have h := (ceilDiv_le_iff_le_mul pos).mp
      (le_refl ((3+A)*(3+B)*k ⌈/⌉ D))
    exact Nat.le_of_mul_le_mul_left
      ((Nat.mul_le_mul_right k less).trans h) pos
  · apply (ceilDiv_le_iff_le_mul pos).mpr
    rw [decomp]
    dsimp only [D]
    nlinarith only [Nat.mul_le_mul_left (4+A+B) small]

end CriticalLastSlice

namespace CriticalLastSlice

open MvPolynomial

/-- A generic rank increment can be tested solely on the small normal
spaces. The third-factor relations must detect every nonzero normal tuple. -/
theorem increment_iff_normals {a b c r : ℕ} (hc : c+1≤r)
    (P : Matrix ((Fin a × Fin b) × Fin (c+1)) (Fin r × (Fin a ⊕ (Fin b ⊕ Fin (c+1))))
      (MvPolynomial (Fin r × (Fin a ⊕ (Fin b ⊕ Fin (c+1)))) ℂ))
    (entry : ∀ i j l t v, P ((i,j),l) (t,v) =
      v.elim (fun ii => if ii=i then X (t,.inr (.inl j))*X (t,.inr (.inr l)) else 0)
        (Sum.elim (fun jj => if jj=j then X (t,.inl i)*X (t,.inr (.inr l)) else 0)
          (fun ll => if ll=l then X (t,.inl i)*X (t,.inr (.inl j)) else 0))) :
    let V := Fin r × (Fin a ⊕ (Fin b ⊕ Fin (c+1)))
    let R := MvPolynomial V ℂ
    let K := FractionRing R
    let q := fun s : V => algebraMap R K (X s)
    let x (t : Fin r) (i : Fin a) := q (t,.inl i)
    let y (t : Fin r) (j : Fin b) := q (t,.inr (.inl j))
    let z (t : Fin r) (k : Fin (c+1)) := q (t,.inr (.inr k))
    let G := P.map (algebraMap R K)
    let old := G.submatrix (fun s : (Fin a × Fin b) × Fin c => (s.1,s.2.castSucc)) id
    G.rank = old.rank+a*b ↔ ∀ F : Fin r → Fin a × Fin b → K,
      (∀ t s, ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*F t ij=0) →
      (∀ t i, ∑ j, y t j * F t (i,j)=0) → (∀ t j, ∑ i, x t i * F t (i,j)=0) →
      (∀ v : Fin r → K, (∀ k, ∑ t, v t*z t k=0) → ∑ t, v t • F t=0) → F=0 := by
  intro V R K q x y z G old
  have inc : G.rank=old.rank+a*b ↔ Function.Surjective G.mulVec := by
    simpa only [Fintype.card_prod,Fintype.card_fin] using
      rank_increment_iff_surjective G (fun l => rank_delete_eq_last P entry l)
  apply inc.trans
  apply LastSliceRelation.tangent_iff_normal_relations x y z (third_span a b (c+1) r hc)
  intro i j k t u
  rcases u with ii | jj
  · by_cases h : ii=i <;> simp [G,entry,h,x,y,z,q]
  · rcases jj with jj | ll
    · by_cases h : jj=j <;> simp [G,entry,h,x,y,z,q]
    · by_cases h : ll=k <;> simp [G,entry,h,x,y,z,q]

end CriticalLastSlice

namespace CriticalLastSlice

open MvPolynomial

/-- The normal-compatibility criterion at the literal matrix and point count of the parent. -/
theorem registered_iff {a b c : ℕ} (ha : 3≤a) (hb : 3≤b) (hc : c+1≤(a-1)*(b-1)) :
    (let r := a*b*(c+1) ⌈/⌉ (a+b+(c+1)-2)
     let V := Fin r × (Fin a ⊕ (Fin b ⊕ Fin (c+1)))
     let R := MvPolynomial V ℂ
     let P : Matrix ((Fin a × Fin b) × Fin (c+1)) V R := fun row col =>
       col.2.elim (fun i => if i=row.1.1 then X (col.1,.inr (.inl row.1.2))*X (col.1,.inr (.inr row.2)) else 0)
         (Sum.elim (fun j => if j=row.1.2 then X (col.1,.inl row.1.1)*X (col.1,.inr (.inr row.2)) else 0)
           (fun k => if k=row.2 then X (col.1,.inl row.1.1)*X (col.1,.inr (.inl row.1.2)) else 0))
     let G := P.map (algebraMap R (FractionRing R))
     let old := G.submatrix (fun s : (Fin a × Fin b) × Fin c => (s.1,s.2.castSucc)) id
     G.rank = old.rank+a*b) ↔
    let r := a*b*(c+1) ⌈/⌉ (a+b+(c+1)-2)
    let V := Fin r × (Fin a ⊕ (Fin b ⊕ Fin (c+1)))
    let R := MvPolynomial V ℂ
    let K := FractionRing R
    let q (s : V) := algebraMap R K (X s)
    let x (t : Fin r) (i : Fin a) := q (t,.inl i)
    let y (t : Fin r) (j : Fin b) := q (t,.inr (.inl j))
    let z (t : Fin r) (k : Fin (c+1)) := q (t,.inr (.inr k))
    ∀ F : Fin r → Fin a × Fin b → K,
      (∀ t s, ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*F t ij=0) →
      (∀ t i, ∑ j, y t j*F t (i,j)=0) →
      (∀ t j, ∑ i, x t i*F t (i,j)=0) →
      (∀ v : Fin r → K, (∀ k, ∑ t, v t*z t k=0) → ∑ t, v t • F t=0) → F=0 := by
  let r := a*b*(c+1) ⌈/⌉ (a+b+(c+1)-2)
  let V := Fin r × (Fin a ⊕ (Fin b ⊕ Fin (c+1)))
  let R := MvPolynomial V ℂ
  let P : Matrix ((Fin a × Fin b) × Fin (c+1)) V R := fun row col =>
    col.2.elim (fun i => if i=row.1.1 then X (col.1,.inr (.inl row.1.2))*X (col.1,.inr (.inr row.2)) else 0)
      (Sum.elim (fun j => if j=row.1.2 then X (col.1,.inl row.1.1)*X (col.1,.inr (.inr row.2)) else 0)
        (fun k => if k=row.2 then X (col.1,.inl row.1.1)*X (col.1,.inr (.inl row.1.2)) else 0))
  exact increment_iff_normals (point_bounds ha hb hc).1 P (fun _ _ _ _ _ => rfl)

end CriticalLastSlice

namespace OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1

open MvPolynomial

section TwoDimensionalNormals

/-- At the next point count each sampled bilinear normal space has dimension two. -/
def H1 : Prop :=
  ∀ a b c : ℕ, 3≤a → a≤b → b<c → c+1<(a-1)*(b-1) →
    let w := (a-1)*(b-1)
    let r := a*b*(c+1) ⌈/⌉ (a+b+(c+1)-2)
    r+1=w →
      let V := Fin r × (Fin a ⊕ (Fin b ⊕ Fin (c+1)))
      let R := MvPolynomial V ℂ
      let K := FractionRing R
      let q (s : V) := algebraMap R K (X s)
      let x (t : Fin r) (i : Fin a) := q (t,.inl i)
      let y (t : Fin r) (j : Fin b) := q (t,.inr (.inl j))
      let z (t : Fin r) (k : Fin (c+1)) := q (t,.inr (.inr k))
      ∀ F : Fin r → Fin a × Fin b → K,
        (∀ t s, ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*F t ij=0) →
        (∀ t i, ∑ j, y t j*F t (i,j)=0) →
        (∀ t j, ∑ i, x t i*F t (i,j)=0) →
        (∀ v : Fin r → K, (∀ k, ∑ t, v t*z t k=0) → ∑ t, v t • F t=0) → F=0

end TwoDimensionalNormals

section HigherDimensionalNormals

/-- At the remaining point counts the sampled normal spaces have dimension at least three. -/
def H2 : Prop :=
  ∀ a b c : ℕ, 3≤a → a≤b → b<c → c+1<(a-1)*(b-1) →
    let w := (a-1)*(b-1)
    let r := a*b*(c+1) ⌈/⌉ (a+b+(c+1)-2)
    r+1<w →
      let V := Fin r × (Fin a ⊕ (Fin b ⊕ Fin (c+1)))
      let R := MvPolynomial V ℂ
      let K := FractionRing R
      let q (s : V) := algebraMap R K (X s)
      let x (t : Fin r) (i : Fin a) := q (t,.inl i)
      let y (t : Fin r) (j : Fin b) := q (t,.inr (.inl j))
      let z (t : Fin r) (k : Fin (c+1)) := q (t,.inr (.inr k))
      ∀ F : Fin r → Fin a × Fin b → K,
        (∀ t s, ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*F t ij=0) →
        (∀ t i, ∑ j, y t j*F t (i,j)=0) →
        (∀ t j, ∑ i, x t i*F t (i,j)=0) →
        (∀ v : Fin r → K, (∀ k, ∑ t, v t*z t k=0) → ∑ t, v t • F t=0) → F=0

end HigherDimensionalNormals

theorem main : H1 → H2 → OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1.H2 := by
  intro two higher a b c ha hab hbc region
  let w := (a-1)*(b-1)
  let r := a*b*(c+1) ⌈/⌉ (a+b+(c+1)-2)
  have hb : 3≤b := ha.trans hab
  by_cases high : w≤r
  · have bfour : 4≤b := by
      by_contra! small
      have h₁ : a=3 := by omega
      have h₂ : b=3 := by omega
      have h₃ : (a-1)*(b-1)=4 := by rw [h₁,h₂]
      omega
    exact CriticalPlateau.Proved.last_increment ha hab bfour (w:=w) rfl region.le
      ((CriticalPlateau.Full.at_least_second_iff ha hab (w:=w) rfl).mp high)
  apply (CriticalLastSlice.registered_iff ha hb region.le).mpr
  by_cases next : r+1=w
  · exact two a b c ha hab hbc region next
  · exact higher a b c ha hab hbc region (by omega)

/-- Each residual statement is also necessary for the original slice increment. -/
theorem iff_remaining_normals : OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1.H2 ↔ H1 ∧ H2 := by
  refine ⟨fun original => ⟨?_,?_⟩,fun h => main h.1 h.2⟩
  all_goals
    intro a b c ha hab hbc region
    exact fun _ => (CriticalLastSlice.registered_iff ha (ha.trans hab) region.le).mp
      (original a b c ha hab hbc region)

end OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1
