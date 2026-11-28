import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1

-- Credit: @mattdorman
/-! # The three-slice frontier of the higher-normal tensor problem

On the registered rank intervals write h=2b−r for a three-slice tensor.
Balanced cubic components cover all levels from nine upward when
4b+7h>3h², apart from the sharp width b=h(h−2)−1. The conic calculation
supplies the odd sharp boundary. The low levels follow from finite
partitions and explicit seed ranks.

The hypotheses separate the finite seeds, the even sharp boundary, the
remaining three-slice interior and the larger first factors. The proof
uses the generic-rank/tangent converse to pass back to the registered
normal equations. Only the immediate merged parent is imported.

Friedland, Conjecture 5.1, https://arxiv.org/abs/0805.3777 .
The normal-space problem is the higher-dimensional child of project
PR 12200. Its earlier endpoint formulation appears in PR 17918.
-/

namespace CriticalHigher

theorem count_le_iff {A d n r : ℕ} (hd : 0<d) (hr : r<A) :
    A*n ⌈/⌉ (d+n) ≤ r ↔ n ≤ r*d/(A-r) := by
  rw [ceilDiv_le_iff_le_mul (by omega : 0<d+n), Nat.le_div_iff_mul_le (by omega : 0<A-r)]
  have split := congrArg (fun z : ℕ => z*n) (Nat.sub_add_cancel hr.le)
  constructor <;> intro h <;> nlinarith only [split,h]

/-- Both endpoints are exact, including ranks for which the integer interval
is empty. -/
theorem count_interval {A d n r : ℕ} (hd : 0<d) (hr : 0<r) (proper : r<A) :
    A*n ⌈/⌉ (d+n) = r ↔ (r-1)*d/(A-(r-1)) < n ∧ n ≤ r*d/(A-r) := by
  have hi := count_le_iff (n:=n) hd proper
  have lo := count_le_iff (n:=n) hd (by omega : r-1<A)
  omega

theorem endpoint_count {A d n r : ℕ} (hd : 0<d) (hr : 0<r) (proper : r<A)
    (count : A*n ⌈/⌉ (d+n)=r) :
    let N := r*d/(A-r)
    n≤N ∧ A*N ⌈/⌉ (d+N)=r := by
  obtain ⟨lo,hi⟩ := (count_interval hd hr proper).mp count
  exact ⟨hi,(count_interval hd hr proper).mpr ⟨lo.trans_le hi,le_rfl⟩⟩

/-- The dimension budget for normal planes of arbitrary dimension.
The common annihilator has dimension A−r. Each point contributes A−r−d
scalar unknowns, and the third vectors supply r−n relations. -/
theorem normal_budget {A d n r : ℕ} (hd : 0<d) (proper : r<A) (small : d≤A-r)
    (count : A*n ⌈/⌉ (d+n)=r) :
    n≤r ∧ (A-r-d)*r ≤ (r-n)*(A-r) := by
  have upper := (count_le_iff hd proper).mp count.le
  have product := (Nat.le_div_iff_mul_le (by omega : 0<A-r)).mp upper
  have size : n≤r :=
    Nat.le_of_mul_le_mul_right (product.trans (Nat.mul_le_mul_left r small)) (by omega)
  have lhs := congrArg (fun z : ℕ => r*z) (Nat.sub_add_cancel small)
  have rhs := congrArg (fun z : ℕ => z*(A-r)) (Nat.sub_add_cancel size)
  exact ⟨size,by nlinarith only [lhs,rhs,product]⟩

end CriticalHigher

namespace CriticalLastSlice.TwoPlanes

open MvPolynomial Arxiv.«0805.3777»

/-- A complex spanning tangent witness exists exactly when the normal tuples
at the independent rational-function coordinates are detected by the third-factor relations. -/
theorem witness_iff_normals {a b n r : ℕ} (enough : n ≤ r) :
    (∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
      ∀ T : Fin a → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))) ↔
    let V := Fin r × (Fin a ⊕ (Fin b ⊕ Fin n))
    let R := MvPolynomial V ℂ
    let K := FractionRing R
    let q (s : V) := algebraMap R K (X s)
    let x (t : Fin r) (i : Fin a) := q (t,.inl i)
    let y (t : Fin r) (j : Fin b) := q (t,.inr (.inl j))
    let z (t : Fin r) (k : Fin n) := q (t,.inr (.inr k))
    ∀ F : Fin r → Fin a × Fin b → K,
      (∀ t s, ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*F t ij=0) →
      (∀ t i, ∑ j, y t j*F t (i,j)=0) → (∀ t j, ∑ i, x t i*F t (i,j)=0) →
      (∀ v : Fin r → K, (∀ k, ∑ t, v t*z t k=0) → ∑ t, v t • F t=0) → F=0 := by
  let V := Fin r × (Fin a ⊕ (Fin b ⊕ Fin n))
  let R := MvPolynomial V ℂ
  let K := FractionRing R
  let q (s : V) := algebraMap R K (X s)
  let x (t : Fin r) (i : Fin a) := q (t,.inl i)
  let y (t : Fin r) (j : Fin b) := q (t,.inr (.inl j))
  let z (t : Fin r) (k : Fin n) := q (t,.inr (.inr k))
  let P : Matrix ((Fin a × Fin b) × Fin n) V R := fun row col =>
    col.2.elim (fun i => if i=row.1.1 then X (col.1,.inr (.inl row.1.2))*X (col.1,.inr (.inr row.2)) else 0)
      (Sum.elim (fun j => if j=row.1.2 then X (col.1,.inl row.1.1)*X (col.1,.inr (.inr row.2)) else 0)
        (fun k => if k=row.2 then X (col.1,.inl row.1.1)*X (col.1,.inr (.inl row.1.2)) else 0))
  have specialized := CriticalJacobian.restricted_tangent_iff (a:=a) (b:=b) (c:=n) (r:=r) id P
    (fun _ _ _ _ _ => rfl)
  apply specialized.trans ((CriticalTensor.Unrestricted.generic_surjective_iff P).symm.trans ?_)
  apply LastSliceRelation.tangent_iff_normal_relations x y z (CriticalLastSlice.third_span a b n r enough)
  intro i j k t v
  change algebraMap R K (P ((i,j),k) (t,v)) = _
  rcases v with i' | j' | k'
  · by_cases hi : i'=i <;> simp [P,x,y,z,q,hi]
  · by_cases hj : j'=j <;> simp [P,x,y,z,q,hj]
  · by_cases hk : k'=k <;> simp [P,x,y,z,q,hk]

/-- A spanning witness at the parameter-count ceiling gives the original
complex generic-rank conclusion in balanced dimensions. -/
theorem generic_rank_of_witness {a b n r : ℕ} (ha : 3 ≤ a) (hab : a ≤ b) (hbn : b ≤ n)
    (count : r = a*b*n ⌈/⌉ (a+b+n-2))
    (witness : ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
      ∀ T : Fin a → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))) :
    IsGenericRank [a,b,n] r := by
  subst r
  exact OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1.generic_of_bounded a b n ha hab hbn
    (CriticalReduction.bounded_of_witness witness)

end CriticalLastSlice.TwoPlanes

namespace CriticalHigher

/-- A spanning witness on the seed slice space restricts to every smaller
third dimension, preserving the number of points. -/
theorem project {a b k e w : ℕ} (hk : k≤e)
    (seed : ∃ x : Fin w → Fin a → ℂ, ∃ y : Fin w → Fin b → ℂ, ∃ z : Fin w → Fin e → ℂ,
      ∀ T : Fin a → Fin b → Fin e → ℂ, ∃ u : Fin w → Fin a → ℂ,
        ∃ v : Fin w → Fin b → ℂ, ∃ s : Fin w → Fin e → ℂ, ∀ i j l,
          T i j l = ∑ t, (u t i*(y t j*z t l) + x t i*(v t j*z t l) + x t i*(y t j*s t l))) :
    ∃ x : Fin w → Fin a → ℂ, ∃ y : Fin w → Fin b → ℂ, ∃ z : Fin w → Fin k → ℂ,
      ∀ T : Fin a → Fin b → Fin k → ℂ, ∃ u : Fin w → Fin a → ℂ,
        ∃ v : Fin w → Fin b → ℂ, ∃ s : Fin w → Fin k → ℂ, ∀ i j l,
          T i j l = ∑ t, (u t i*(y t j*z t l) + x t i*(v t j*z t l) + x t i*(y t j*s t l)) := by
  obtain ⟨x,y,z,span⟩ := seed
  refine ⟨x,y,fun t l => z t (Fin.castLE hk l),?_⟩
  intro T
  let extT (i : Fin a) (j : Fin b) (l : Fin e) := if hl : l.val<k then T i j ⟨l.val,hl⟩ else 0
  obtain ⟨u,v,s,hs⟩ := span extT
  refine ⟨u,v,fun t l => s t (Fin.castLE hk l),?_⟩
  intro i j l
  simpa [extT,l.isLt] using hs i j (Fin.castLE hk l)

end CriticalHigher

namespace CriticalHigher

theorem available_normals {a b r : ℕ} (ha : 3≤a) (hab : a≤b)
    (level : r+1<(a-1)*(b-1)) : r<a*b ∧ a+b-2≤a*b-r := by
  have identity : (a-1)*(b-1)+(a+b-1)=a*b := by
    obtain ⟨i,rfl⟩ : ∃ i : ℕ, a=i+1 := ⟨a-1,by omega⟩
    obtain ⟨j,rfl⟩ : ∃ j : ℕ, b=j+1 := ⟨b-1,by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [show i+1+(j+1)-1=i+j+1 by omega]
    ring
  omega

theorem witness_at_count
    (higher : OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1.H2)
    {a b n r : ℕ} (ha : 3≤a) (hab : a≤b) (start : b+2≤n)
    (level : r+1<(a-1)*(b-1)) (count : a*b*n ⌈/⌉ ((a+b-2)+n)=r) :
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
      ∀ T : Fin a → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
          T i j k=∑ t,(u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k)) := by
  obtain ⟨proper,small⟩ := available_normals ha hab level
  have enough := (normal_budget (by omega : 0<a+b-2) proper small count).1
  obtain ⟨c,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  have denom : (a+b-2)+(c+1)=a+b+(c+1)-2 := by omega
  rw [denom] at count
  subst r
  exact (CriticalLastSlice.TwoPlanes.witness_iff_normals (a:=a) (b:=b) enough).mpr
    (higher a b c ha hab (by omega) (by omega) level)

/-- For fixed a,b,r the entire registered normal-space problem is equivalent
to one complex spanning tangent at the largest integer third dimension of the
rank interval. Empty intervals and endpoints outside the strict rectangle
do not require witnesses. -/
theorem higher_iff_endpoints :
    OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1.H2 ↔
    ∀ a b r : ℕ, 3≤a → a≤b → 0<r → r+1<(a-1)*(b-1) →
      let A := a*b
      let d := a+b-2
      let N := r*d/(A-r)
      b+2≤N → (r-1)*d/(A-(r-1))<N →
      ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin N → ℂ,
        ∀ T : Fin a → Fin b → Fin N → ℂ, ∃ u : Fin r → Fin a → ℂ,
          ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin N → ℂ, ∀ i j k,
            T i j k=∑ t,(u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k)) := by
  constructor
  · intro parent a b r ha hab hr level A d N start present
    have proper := (available_normals ha hab level).1
    apply witness_at_count parent ha hab start level
    exact (count_interval (by omega : 0<a+b-2) hr proper).mpr ⟨present,le_rfl⟩
  · intro endpoints a b c ha hab hbc region w r level
    change r+1<(a-1)*(b-1) at level
    have denom : (a+b-2)+(c+1)=a+b+(c+1)-2 := by omega
    have count : a*b*(c+1) ⌈/⌉ ((a+b-2)+(c+1))=r := by rw [denom]
    obtain ⟨proper,small⟩ := available_normals ha hab level
    have hd : 0<a+b-2 := by omega
    have enough := (normal_budget hd proper small count).1
    have hr : 0<r := by omega
    obtain ⟨lo,hi⟩ := (count_interval hd hr proper).mp count
    have witness := endpoints a b r ha hab hr level ((by omega : b+2≤c+1).trans hi) (lo.trans_le hi)
    exact (CriticalLastSlice.TwoPlanes.witness_iff_normals (a:=a) (b:=b) enough).mp
      (CriticalHigher.project hi witness)

end CriticalHigher

namespace CriticalHigher.Blocks

open MvPolynomial

/-- A full-row-rank specialization gives a nonzero determinant polynomial.
Taking the product gives one specialization for a finite family of matrices. -/
theorem common_surjective {G V : Type*} [Fintype G] {I J : G → Type*}
    [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
    (M : ∀ g, Matrix (I g) (J g) (MvPolynomial V ℂ))
    (each : ∀ g, ∃ v : V → ℂ, Function.Surjective ((M g).map (eval v)).mulVec) :
    ∃ p : V → ℂ, ∀ g, Function.Surjective ((M g).map (eval p)).mulVec := by
  classical
  choose v good using each
  choose B inverse using fun g => Matrix.mulVec_surjective_iff_exists_right_inverse.mp (good g)
  let P (g : G) := (B g).map (C : ℂ →+* MvPolynomial V ℂ)
  let Q (g : G) := (M g*P g).det
  have spec (g : G) (u : V → ℂ) :
      eval u (Q g) = ((M g).map (eval u)*B g).det := by
    have constant : (P g).map (eval u)=B g := by ext; simp [P,Matrix.map_apply]
    change eval u (M g*P g).det = _
    rw [RingHom.map_det,RingHom.mapMatrix_apply,Matrix.map_mul,constant]
  have nz (g : G) : Q g≠0 := by
    intro zero
    have atPoint := spec g (v g)
    rw [zero,map_zero,inverse g,Matrix.det_one] at atPoint
    exact zero_ne_one atPoint
  have allnz : (∏ g,Q g)≠0 := Finset.prod_ne_zero_iff.mpr fun g _ => nz g
  obtain ⟨p,hp⟩ : ∃ p : V → ℂ, eval p (∏ g,Q g)≠0 := by
    by_contra! vanish
    exact allnz (MvPolynomial.funext fun q => by rw [vanish q,map_zero])
  have eachnz : (∏ g,eval p (Q g))≠0 := by simpa only [map_prod] using hp
  refine ⟨p,fun g => ?_⟩
  have hdet := Finset.prod_ne_zero_iff.mp eachnz g (Finset.mem_univ g)
  rw [spec] at hdet
  have onto := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  intro t
  obtain ⟨s,hs⟩ := onto t
  exact ⟨(B g).mulVec s,(Matrix.mulVec_mulVec _ _ _).trans hs⟩

/-- In one block all sampled products have free variations in the last
factor. Only the samples assigned to the block have their first two
variations present. Each separately verified block can use different
factors before common specialization. -/
theorem common_tangents {A B C P G : Type*} [Fintype A] [Fintype B] [Fintype C]
    [Fintype P] [Fintype G] [DecidableEq G] (label : P → G) :
    let D (g : G) (x : P → A → ℂ) (y : P → B → ℂ) (z : P → C → ℂ) :=
      ∀ T : A → B → C → ℂ, ∃ u : P → A → ℂ, ∃ v : P → B → ℂ, ∃ w : P → C → ℂ, ∀ i j k,
        T i j k = ∑ t, ((if label t=g then u t i*(y t j*z t k)+x t i*(v t j*z t k) else 0)
          +x t i*(y t j*w t k))
    (∀ g, ∃ x y z, D g x y z) → ∃ x y z, ∀ g, D g x y z := by
  classical
  intro D each
  let V := P × (A ⊕ (B ⊕ C))
  let M (g : G) : Matrix ((A × B) × C) V (MvPolynomial V ℂ) := fun row col => col.2.elim
    (fun i => if label col.1=g ∧ i=row.1.1 then X (col.1,.inr (.inl row.1.2))*X (col.1,.inr (.inr row.2)) else 0)
    (Sum.elim
      (fun j => if label col.1=g ∧ j=row.1.2 then X (col.1,.inl row.1.1)*X (col.1,.inr (.inr row.2)) else 0)
      (fun k => if k=row.2 then X (col.1,.inl row.1.1)*X (col.1,.inr (.inl row.1.2)) else 0))
  let pack (x : P → A → ℂ) (y : P → B → ℂ) (z : P → C → ℂ) : V → ℂ :=
    fun (t,q) => q.elim (x t) (Sum.elim (y t) (z t))
  have action (g : G) (p q : V → ℂ) (i : A) (j : B) (k : C) :
      ((M g).map (eval p)).mulVec q ((i,j),k) = ∑ t,
        ((if label t=g then q (t,.inl i)*(p (t,.inr (.inl j))*p (t,.inr (.inr k))) +
           p (t,.inl i)*(q (t,.inr (.inl j))*p (t,.inr (.inr k))) else 0) +
           p (t,.inl i)*(p (t,.inr (.inl j))*q (t,.inr (.inr k)))) := by
    change (∑ s : V, eval p (M g ((i,j),k) s)*q s) = _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
    by_cases hit : label t=g <;> simp [M,hit,apply_ite,ite_mul,Finset.sum_ite_eq'] <;> ring
  have localFull (g : G) : ∃ p : V → ℂ, Function.Surjective ((M g).map (eval p)).mulVec := by
    obtain ⟨x,y,z,h⟩ := each g
    refine ⟨pack x y z,?_⟩
    intro T
    obtain ⟨u,v,w,cover⟩ := h fun i j k => T ((i,j),k)
    refine ⟨pack u v w,?_⟩
    funext ⟨⟨i,j⟩,k⟩
    exact (action g (pack x y z) (pack u v w) i j k).trans (cover i j k).symm
  obtain ⟨p,good⟩ := common_surjective M localFull
  refine ⟨fun t i => p (t,.inl i),fun t j => p (t,.inr (.inl j)),fun t k => p (t,.inr (.inr k)),?_⟩
  intro g T
  obtain ⟨q,hq⟩ := good g fun s => T s.1.1 s.1.2 s.2
  exact ⟨fun t i => q (t,.inl i),fun t j => q (t,.inr (.inl j)),fun t k => q (t,.inr (.inr k)),
    fun i j k => (congrFun hq ((i,j),k)).symm.trans (action g p q i j k)⟩

/-- Put each point's third vector in its assigned coordinate block. Third
variations can act on all blocks independently, so the local witnesses
produce a spanning tangent for the whole tensor. -/
theorem spans_of_blocks {A B C P G : Type*} [Fintype A] [Fintype B] [Fintype C]
    [Fintype P] [Fintype G] [DecidableEq G] (label : P → G)
    (one : ∀ g, ∃ x : P → A → ℂ, ∃ y : P → B → ℂ, ∃ z : P → C → ℂ,
      ∀ T : A → B → C → ℂ, ∃ u : P → A → ℂ, ∃ v : P → B → ℂ, ∃ w : P → C → ℂ, ∀ i j k,
        T i j k = ∑ t, ((if label t=g then u t i*(y t j*z t k)+x t i*(v t j*z t k) else 0)
          +x t i*(y t j*w t k))) :
    ∃ x : P → A → ℂ, ∃ y : P → B → ℂ, ∃ Z : P → G × C → ℂ,
      ∀ T : A → B → G × C → ℂ, ∃ u : P → A → ℂ, ∃ v : P → B → ℂ, ∃ w : P → G × C → ℂ,
        ∀ i j k, T i j k=∑ t,(u t i*(y t j*Z t k)+x t i*(v t j*Z t k)+x t i*(y t j*w t k)) := by
  classical
  obtain ⟨x,y,z,good⟩ := common_tangents label one
  let Z (t : P) (p : G × C) := if label t=p.1 then z t p.2 else 0
  refine ⟨x,y,Z,?_⟩
  intro T
  choose U V W repr using fun g => good g (fun i j k => T i j (g,k))
  refine ⟨fun t => U (label t) t, fun t => V (label t) t, fun t k => W k.1 t k.2,?_⟩
  rintro i j ⟨g,k⟩
  apply (repr g i j k).trans
  apply Finset.sum_congr rfl
  intro t _
  by_cases hit : label t=g <;> simp [Z,hit]

end CriticalHigher.Blocks

namespace CriticalHigher.Blocks

/-- Reindex a full tangent plus an external-product supplement onto any
finite point set, allowing the first two variations only on its marked set. -/
private theorem restricted_tangent_of_split {A B C P M N : Type*}
    [Fintype P] [Fintype M] [Fintype N] (active : P → Prop) [DecidablePred active]
    (e : (M ⊕ N) ≃ P) (marked : ∀ t : M, active (e (.inl t)))
    (one : ∃ x : M → A → ℂ, ∃ y : M → B → ℂ, ∃ z : M → C → ℂ,
      ∃ x' : N → A → ℂ, ∃ y' : N → B → ℂ,
      ∀ T : A → B → C → ℂ, ∃ u : M → A → ℂ, ∃ v : M → B → ℂ, ∃ w : M → C → ℂ,
      ∃ w' : N → C → ℂ, ∀ i j k,
        T i j k = (∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) +
          ∑ t, x' t i*(y' t j*w' t k)) :
    ∃ X : P → A → ℂ, ∃ Y : P → B → ℂ, ∃ Z : P → C → ℂ,
      ∀ T : A → B → C → ℂ, ∃ u : P → A → ℂ, ∃ v : P → B → ℂ, ∃ w : P → C → ℂ, ∀ i j k,
      T i j k = ∑ t, ((if active t then u t i*(Y t j*Z t k)+X t i*(v t j*Z t k) else 0) +
        X t i*(Y t j*w t k)) := by
  obtain ⟨x,y,z,x',y',hit⟩ := one
  let X (p : P) := (e.symm p).elim x x'
  let Y (p : P) := (e.symm p).elim y y'
  let Z (p : P) := (e.symm p).elim z 0
  refine ⟨X,Y,Z,?_⟩
  intro T
  obtain ⟨u,v,w,w',cover⟩ := hit T
  refine ⟨fun p => (e.symm p).elim u 0,fun p => (e.symm p).elim v 0,fun p => (e.symm p).elim w w',?_⟩
  intro i j k
  rw [cover i j k,← e.sum_comp,Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro t _
    simp only [X,Y,Z,Equiv.symm_apply_apply,Sum.elim_inl,if_pos (marked t)]
  · apply Finset.sum_congr rfl
    intro t _
    simp [X,Y,Z]

/-- Choose a complementary enumeration for one group among the r points.
The designated group is the left summand and every other point is external. -/
private theorem pencil_group_complement {h m r : ℕ} (slots : h*m ≤ r) (g : Fin h) :
    ∃ e : (Fin m ⊕ Fin (r-m)) ≃ ((Fin h × Fin m) ⊕ Fin (r-h*m)),
      ∀ j : Fin m, e (.inl j) = .inl (g,j) := by
  classical
  let P := (Fin h × Fin m) ⊕ Fin (r-h*m)
  let f : Fin m → P := fun j => .inl (g,j)
  have finj : Function.Injective f := fun u v ev => congrArg Prod.snd (Sum.inl.inj ev)
  let front := Equiv.ofInjective f finj
  have size : Fintype.card P = r := by
    simp only [P,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    omega
  have frontSize : Fintype.card {p : P // p ∈ Set.range f} = m := by
    rw [← Fintype.card_congr front,Fintype.card_fin]
  let rest : {p : P // p ∉ Set.range f} ≃ Fin (r-m) := Fintype.equivFinOfCardEq (by
    rw [Fintype.card_subtype_compl,frontSize,size])
  let e := (Equiv.sumCongr front rest.symm).trans (Equiv.sumCompl (fun p => p ∈ Set.range f))
  exact ⟨e,fun _ => rfl⟩

end CriticalHigher.Blocks

namespace CriticalHigher.Blocks

theorem tangent_cycle {A B C P : Type*} [Fintype P]
    (one : ∃ X : P → A → ℂ, ∃ Y : P → B → ℂ, ∃ Z : P → C → ℂ,
      ∀ T : A → B → C → ℂ, ∃ u : P → A → ℂ, ∃ v : P → B → ℂ,
      ∃ w : P → C → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k))) :
    ∃ X : P → C → ℂ, ∃ Y : P → A → ℂ, ∃ Z : P → B → ℂ,
    ∀ T : C → A → B → ℂ, ∃ u : P → C → ℂ, ∃ v : P → A → ℂ,
    ∃ w : P → B → ℂ, ∀ i j k,
      T i j k = ∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k)) := by
  obtain ⟨x,y,z,cover⟩ := one
  refine ⟨z,x,y,?_⟩
  intro T
  obtain ⟨u,v,w,rep⟩ := cover (fun i j k => T k i j)
  refine ⟨w,u,v,?_⟩
  intro k i j
  rw [rep i j k]
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem tangent_swap_last {A B C P : Type*} [Fintype P]
    (one : ∃ X : P → A → ℂ, ∃ Y : P → B → ℂ, ∃ Z : P → C → ℂ,
      ∀ T : A → B → C → ℂ, ∃ u : P → A → ℂ, ∃ v : P → B → ℂ,
      ∃ w : P → C → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k))) :
    ∃ X : P → A → ℂ, ∃ Y : P → C → ℂ, ∃ Z : P → B → ℂ,
    ∀ T : A → C → B → ℂ, ∃ u : P → A → ℂ, ∃ v : P → C → ℂ,
    ∃ w : P → B → ℂ, ∀ i j k,
      T i j k = ∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k)) := by
  obtain ⟨x,y,z,cover⟩ := one
  refine ⟨x,z,y,?_⟩
  intro T
  obtain ⟨u,v,w,rep⟩ := cover (fun i j k => T i k j)
  refine ⟨u,w,v,?_⟩
  intro i k j
  rw [rep i j k]
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem many_pencil_third (a b h m r : ℕ) (slots : h*m ≤ r)
    (one : ∃ x : Fin m → Fin a → ℂ, ∃ y : Fin m → Fin b → ℂ, ∃ z : Fin m → Fin 2 → ℂ,
      ∃ x' : Fin (r-m) → Fin a → ℂ, ∃ y' : Fin (r-m) → Fin b → ℂ,
      ∀ T : Fin a → Fin b → Fin 2 → ℂ, ∃ u : Fin m → Fin a → ℂ, ∃ v : Fin m → Fin b → ℂ,
      ∃ w : Fin m → Fin 2 → ℂ, ∃ w' : Fin (r-m) → Fin 2 → ℂ, ∀ i j k,
        T i j k = (∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) +
          ∑ t, x' t i*(y' t j*w' t k)) :
    ∃ X : Fin r → Fin a → ℂ, ∃ Y : Fin r → Fin b → ℂ, ∃ Z : Fin r → Fin (2*h) → ℂ,
    ∀ T : Fin a → Fin b → Fin (2*h) → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
    ∃ w : Fin r → Fin (2*h) → ℂ, ∀ i j k,
      T i j k = ∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k)) := by
  classical
  by_cases empty : h=0
  · subst h
    exact ⟨0,0,0,fun _ => ⟨0,0,0,fun _ _ k => Fin.elim0 k⟩⟩
  let P := (Fin h × Fin m) ⊕ Fin (r-h*m)
  let label : P → Fin h := Sum.elim Prod.fst (fun _ => ⟨0,Nat.pos_of_ne_zero empty⟩)
  have each (g : Fin h) : ∃ X : P → Fin a → ℂ, ∃ Y : P → Fin b → ℂ, ∃ Z : P → Fin 2 → ℂ,
      ∀ T : Fin a → Fin b → Fin 2 → ℂ, ∃ u : P → Fin a → ℂ, ∃ v : P → Fin b → ℂ, ∃ w : P → Fin 2 → ℂ,
      ∀ i j k, T i j k = ∑ t, ((if label t=g then u t i*(Y t j*Z t k)+X t i*(v t j*Z t k) else 0) +
        X t i*(Y t j*w t k)) := by
    obtain ⟨e,he⟩ := pencil_group_complement slots g
    apply restricted_tangent_of_split (fun t => label t=g) e _ one
    intro s
    rw [he s]
    rfl
  obtain ⟨x,y,z,span⟩ := spans_of_blocks label each
  let points : P ≃ Fin r := Fintype.equivFinOfCardEq (by
    simp only [P,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    omega)
  let coords : (Fin h × Fin 2) ≃ Fin (2*h) := (Equiv.prodComm _ _).trans finProdFinEquiv
  refine ⟨fun t => x (points.symm t),fun t => y (points.symm t),fun t k => z (points.symm t) (coords.symm k),?_⟩
  intro T
  obtain ⟨u,v,w,hcover⟩ := span fun i j k => T i j (coords k)
  refine ⟨fun t => u (points.symm t),fun t => v (points.symm t),fun t k => w (points.symm t) (coords.symm k),?_⟩
  intro i j k
  have atRow := hcover i j (coords.symm k)
  simp only [Equiv.apply_symm_apply] at atRow
  rw [atRow,← points.sum_comp]
  simp only [Equiv.symm_apply_apply]

theorem many_pencil_first (a b h m r : ℕ) (slots : h*m ≤ r)
    (one : ∃ x : Fin m → Fin a → ℂ, ∃ y : Fin m → Fin b → ℂ, ∃ z : Fin m → Fin 2 → ℂ,
      ∃ x' : Fin (r-m) → Fin a → ℂ, ∃ y' : Fin (r-m) → Fin b → ℂ,
      ∀ T : Fin a → Fin b → Fin 2 → ℂ, ∃ u : Fin m → Fin a → ℂ, ∃ v : Fin m → Fin b → ℂ,
      ∃ w : Fin m → Fin 2 → ℂ, ∃ w' : Fin (r-m) → Fin 2 → ℂ, ∀ i j k,
        T i j k = (∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) +
          ∑ t, x' t i*(y' t j*w' t k)) :
    ∃ X : Fin r → Fin (2*h) → ℂ, ∃ Y : Fin r → Fin a → ℂ, ∃ Z : Fin r → Fin b → ℂ,
    ∀ T : Fin (2*h) → Fin a → Fin b → ℂ, ∃ u : Fin r → Fin (2*h) → ℂ, ∃ v : Fin r → Fin a → ℂ,
    ∃ w : Fin r → Fin b → ℂ, ∀ i j k,
      T i j k = ∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k)) := by
  exact tangent_cycle (many_pencil_third a b h m r slots one)

theorem many_pencil_second (a b h m r : ℕ) (slots : h*m ≤ r)
    (one : ∃ x : Fin m → Fin a → ℂ, ∃ y : Fin m → Fin b → ℂ, ∃ z : Fin m → Fin 2 → ℂ,
      ∃ x' : Fin (r-m) → Fin a → ℂ, ∃ y' : Fin (r-m) → Fin b → ℂ,
      ∀ T : Fin a → Fin b → Fin 2 → ℂ, ∃ u : Fin m → Fin a → ℂ, ∃ v : Fin m → Fin b → ℂ,
      ∃ w : Fin m → Fin 2 → ℂ, ∃ w' : Fin (r-m) → Fin 2 → ℂ, ∀ i j k,
        T i j k = (∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) +
          ∑ t, x' t i*(y' t j*w' t k)) :
    ∃ X : Fin r → Fin a → ℂ, ∃ Y : Fin r → Fin (2*h) → ℂ, ∃ Z : Fin r → Fin b → ℂ,
    ∀ T : Fin a → Fin (2*h) → Fin b → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin (2*h) → ℂ,
    ∃ w : Fin r → Fin b → ℂ, ∀ i j k,
      T i j k = ∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k)) := by
  exact tangent_swap_last (many_pencil_third a b h m r slots one)

end CriticalHigher.Blocks

namespace CriticalLastSlice.HigherPencil

/-- Pair consecutive positions in the listing by layer and then label. When
the last position is alone, pair it with the first. Every pair uses two
different labels, and each label's layers occur at distinct primary samples. -/
theorem cyclic_schedule (m n : ℕ) (hm : 2≤ m) :
    let S := Fin ((n*m+1)/2)
    ∃ L R : S → Fin n × Fin m, ∃ sample : Fin m → Fin n → S,
      (∀ s,(L s).2 ≠ (R s).2) ∧ (∀ i,Function.Injective (sample i)) ∧
      ∀ i j,L (sample i j)=(j,i) ∨ R (sample i j)=(j,i) := by
  intro S
  let even (s : S) : Fin (n*m) := ⟨2*s.val,by have := s.isLt; omega⟩
  let next (s : S) : Fin (n*m) := if h : 2*s.val+1<n*m then ⟨2*s.val+1,h⟩
    else ⟨0,by have := s.isLt; omega⟩
  let sample (i : Fin m) (j : Fin n) : S :=
    ⟨(finProdFinEquiv (j,i)).val/2,by have := (finProdFinEquiv (j,i)).isLt; omega⟩
  have next_ne (q : ℕ) : q%m ≠ (q+1)%m := by
    rw [Nat.add_mod,Nat.mod_eq_of_lt (by omega : 1< m)]
    have bound := Nat.mod_lt q (by omega : 0< m)
    by_cases hs : q%m+1< m
    · rw [Nat.mod_eq_of_lt hs]; omega
    · rw [show q%m+1=m by omega,Nat.mod_self]; omega
  refine ⟨fun s => finProdFinEquiv.symm (even s),fun s => finProdFinEquiv.symm (next s),
    sample,?_,?_,?_⟩
  · intro s hg
    apply next_ne (2*s.val)
    have eq := congrArg Fin.val hg
    change (2*s.val)%m=(next s).val%m at eq
    by_cases h : 2*s.val+1<n*m
    · simpa only [next,dif_pos h] using eq
    · have last : 2*s.val+1=n*m := by have := (even s).isLt; change 2*s.val<n*m at this; omega
      simpa [next,h,last] using eq
  · intro i j k eq
    have strict : StrictMono (fun t : ℕ => (i.val+m*t)/2) := by
      apply strictMono_nat_of_lt_succ
      intro t
      have bound : i.val+m*t+2 ≤ i.val+m*(t+1) := by rw [Nat.mul_add]; omega
      omega
    exact Fin.ext (strict.injective (congrArg Fin.val eq))
  · intro i j
    let q := finProdFinEquiv (j,i)
    have hit : (sample i j).val=q.val/2 := rfl
    by_cases h : q.val%2=0
    · left
      have he : even (sample i j)=q := Fin.ext (by change 2*(sample i j).val=q.val; omega)
      exact (congrArg finProdFinEquiv.symm he).trans (finProdFinEquiv.symm_apply_apply _)
    · right
      have he : 2*(sample i j).val+1=q.val := by omega
      have bound : 2*(sample i j).val+1<n*m := he ▸ q.isLt
      have hn : next (sample i j)=q := Fin.ext (by simp only [next,dif_pos bound,he])
      exact (congrArg finProdFinEquiv.symm hn).trans (finProdFinEquiv.symm_apply_apply _)

end CriticalLastSlice.HigherPencil

namespace CriticalLastSlice.HigherPencil

/-- Two pencil coefficients separate the evaluations at different labels.
Vandermonde interpolation at each label's distinct samples recovers both
the complete marked row tail and the complete marked column tail. -/
theorem interpolate_slots {m d e : ℕ} {S : Type*}
    (node : S → ℂ) (hn : Function.Injective node) (μ : Fin m → ℂ) (hμ : Function.Injective μ)
    (L R : S → (Fin e ⊕ Fin d) × Fin m) (sample : Fin m → (Fin e ⊕ Fin d) → S)
    (separate : ∀ s,(L s).2 ≠ (R s).2) (distinct : ∀ i,Function.Injective (sample i))
    (cover : ∀ i j,L (sample i j)=(j,i) ∨ R (sample i j)=(j,i))
    (Y : Fin m → Fin e → ℂ) (X : Fin m → Fin d → ℂ) :
    let value (s : S) (q : (Fin e ⊕ Fin d) × Fin m) := q.1.elim
      (fun _ => ∑ j : Fin e,node s^j.val*Y q.2 j) (fun _ => ∑ i : Fin d,node s^i.val*X q.2 i)
    (∀ s,value s (L s)+value s (R s)=0) →
    (∀ s,μ (L s).2*value s (L s)+μ (R s).2*value s (R s)=0) → Y=0 ∧ X=0 := by
  intro value h₀ h₁
  have zero (s : S) : value s (L s)=0 ∧ value s (R s)=0 := by
    have diff : (μ (L s).2-μ (R s).2)*value s (L s)=0 := by
      linear_combination h₁ s - μ (R s).2 * h₀ s
    have nz : μ (L s).2-μ (R s).2≠0 := sub_ne_zero.mpr (fun eq => separate s (hμ eq))
    have left := (mul_eq_zero.mp diff).resolve_left nz
    exact ⟨left,by simpa only [left,zero_add] using h₀ s⟩
  have sampled (i : Fin m) (j : Fin e ⊕ Fin d) : value (sample i j) (j,i)=0 := by
    rcases cover i j with hl|hr
    · simpa only [hl] using (zero (sample i j)).1
    · simpa only [hr] using (zero (sample i j)).2
  constructor
  · funext i
    apply Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero (f:=fun j : Fin e => node (sample i (.inl j)))
    · intro j k eq
      exact Sum.inl.inj (distinct i (hn eq))
    · exact fun j => sampled i (.inl j)
  · funext i
    apply Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero (f:=fun j : Fin d => node (sample i (.inr j)))
    · intro j k eq
      exact Sum.inr.inj (distinct i (hn eq))
    · exact fun j => sampled i (.inr j)

end CriticalLastSlice.HigherPencil

namespace CriticalLastSlice.HigherPencil

/-- A pure bilinear sample on the two off-diagonal blocks splits into its
upper row contributions and its upper column contributions. -/
theorem sample_off_diagonal {m d e : ℕ} (M : Matrix (Fin m ⊕ Fin d) (Fin m ⊕ Fin e) ℂ)
    (core : ∀ i j,M (.inl i) (.inl j)=0) (bottom : ∀ i j,M (.inr i) (.inr j)=0)
    (x y : Fin m → ℂ) (x' : Fin d → ℂ) (y' : Fin e → ℂ) :
    (∑ i,∑ j,(Sum.elim x x' i)*(Sum.elim y y' j)*M i j) =
      (∑ i,x i*(∑ j,y' j*M (.inl i) (.inr j))) +
      (∑ j,y j*(∑ i,x' i*M (.inr i) (.inl j))) := by
  classical
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,core,bottom,mul_zero,
    Finset.sum_const_zero,zero_add,add_zero]
  congr 1
  · simp only [Finset.mul_sum,mul_assoc]
  · rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- One product reads two evaluation slots at the same Vandermonde node
regardless of whether the slots concern rows, columns, or one of each. -/
theorem two_slot_sample {m d e : ℕ} (z : ℂ) (L R : (Fin e ⊕ Fin d) × Fin m) :
    ∃ x : (Fin m ⊕ Fin d) → ℂ, ∃ y : (Fin m ⊕ Fin e) → ℂ,
      ∀ M : Matrix (Fin m ⊕ Fin d) (Fin m ⊕ Fin e) ℂ,
        (∀ i j,M (.inl i) (.inl j)=0) → (∀ i j,M (.inr i) (.inr j)=0) →
        let value (q : (Fin e ⊕ Fin d) × Fin m) := q.1.elim
          (fun _ => ∑ j : Fin e,z^j.val*M (.inl q.2) (.inr j))
          (fun _ => ∑ i : Fin d,z^i.val*M (.inr i) (.inl q.2))
        (∑ i,∑ j,x i*y j*M i j)=value L+value R := by
  classical
  let xw (q : (Fin e ⊕ Fin d) × Fin m) (i : Fin m) : ℂ :=
    q.1.elim (fun _ => if i=q.2 then 1 else 0) (fun _ => 0)
  let yw (q : (Fin e ⊕ Fin d) × Fin m) (i : Fin m) : ℂ :=
    q.1.elim (fun _ => 0) (fun _ => if i=q.2 then 1 else 0)
  let x (i : Fin m) := xw L i+xw R i
  let y (i : Fin m) := yw L i+yw R i
  refine ⟨Sum.elim x (fun i => z^i.val),Sum.elim y (fun j => z^j.val),?_⟩
  intro M core bottom value
  rw [sample_off_diagonal M core bottom]
  rcases L with ⟨i|i,u⟩ <;> rcases R with ⟨j|j,v⟩ <;>
    simp [x,y,xw,yw,value,add_mul,Finset.sum_add_distrib,ite_mul,Finset.sum_ite_eq',add_comm]

end CriticalLastSlice.HigherPencil

namespace CriticalLastSlice.HigherPencil

/-- Place m full points on the diagonal with third vectors (1,λᵢ). A further
d*e + ceil(m*(d+e)/2) pure products force the whole dual pencil to vanish.
Here the two matrix dimensions are m+d and m+e. -/
theorem product_samples {m d e : ℕ} (hm : 2 ≤ m)
    (lam : Fin m → ℂ) (hlam : Function.Injective lam) :
    let S := Fin (((e+d)*m+1)/2)
    let P := (Fin d × Fin e) ⊕ S
    ∃ x : P → (Fin m ⊕ Fin d) → ℂ, ∃ y : P → (Fin m ⊕ Fin e) → ℂ,
      ∀ U V : Matrix (Fin m ⊕ Fin d) (Fin m ⊕ Fin e) ℂ,
        (∀ i,U (.inl i) (.inl i)=0 ∧ V (.inl i) (.inl i)=0) →
        (∀ i j,U (.inl i) j+lam i*V (.inl i) j=0) →
        (∀ i j,U j (.inl i)+lam i*V j (.inl i)=0) →
        (∀ p,∑ i,∑ j,x p i*y p j*U i j=0) →
        (∀ p,∑ i,∑ j,x p i*y p j*V i j=0) → U=0 ∧ V=0 := by
  classical
  intro S P
  obtain ⟨L₀,R₀,pick,ne,dist,cover₀⟩ := cyclic_schedule m (e+d) hm
  let decode (q : Fin (e+d) × Fin m) : (Fin e ⊕ Fin d) × Fin m := (finSumFinEquiv.symm q.1,q.2)
  let L (s : S) := decode (L₀ s)
  let R (s : S) := decode (R₀ s)
  let sample (i : Fin m) (q : Fin e ⊕ Fin d) := pick i (finSumFinEquiv q)
  have cover (i : Fin m) (q : Fin e ⊕ Fin d) :
      L (sample i q)=(q,i) ∨ R (sample i q)=(q,i) := by
    have back : decode (finSumFinEquiv q,i)=(q,i) := by simp [decode]
    rcases cover₀ i (finSumFinEquiv q) with hl|hr
    · exact Or.inl ((congrArg decode hl).trans back)
    · exact Or.inr ((congrArg decode hr).trans back)
  let node (s : S) : ℂ := s.val
  choose xs ys reading using fun s : S => two_slot_sample (node s) (L s) (R s)
  let x : P → (Fin m ⊕ Fin d) → ℂ := Sum.elim (fun q i => if i=.inr q.1 then 1 else 0) xs
  let y : P → (Fin m ⊕ Fin e) → ℂ := Sum.elim (fun q j => if j=.inr q.2 then 1 else 0) ys
  let eval (M : Matrix (Fin m ⊕ Fin d) (Fin m ⊕ Fin e) ℂ) (s : S) (q : (Fin e ⊕ Fin d) × Fin m) :=
    q.1.elim (fun _ => ∑ j : Fin e,node s^j.val*M (.inl q.2) (.inr j))
      (fun _ => ∑ i : Fin d,node s^i.val*M (.inr i) (.inl q.2))
  have lower (M : Matrix (Fin m ⊕ Fin d) (Fin m ⊕ Fin e) ℂ)
      (sampled : ∀ p,∑ i,∑ j,x p i*y p j*M i j=0) (i : Fin d) (j : Fin e) :
      M (.inr i) (.inr j)=0 := by
    have h := sampled (.inl (i,j))
    simpa [x,y,ite_mul,Finset.sum_ite_eq',Finset.sum_ite_irrel] using h
  have evals (M : Matrix (Fin m ⊕ Fin d) (Fin m ⊕ Fin e) ℂ)
      (core : ∀ i j,M (.inl i) (.inl j)=0) (sampled : ∀ p,∑ i,∑ j,x p i*y p j*M i j=0)
      (s : S) : eval M s (L s)+eval M s (R s)=0 :=
    (reading s M core (lower M sampled)).symm.trans (sampled (.inr s))
  refine ⟨x,y,?_⟩
  intro U V diag row col testU testV
  have core (i j : Fin m) : U (.inl i) (.inl j)=0 ∧ V (.inl i) (.inl j)=0 := by
    by_cases eq : i=j
    · subst j
      exact diag i
    · have weighted : (lam i-lam j)*V (.inl i) (.inl j)=0 := by
        linear_combination row i (.inl j)-col j (.inl i)
      have vzero := (mul_eq_zero.mp weighted).resolve_left (sub_ne_zero.mpr (fun h => eq (hlam h)))
      exact ⟨by simpa only [vzero,mul_zero,add_zero] using row i (.inl j),vzero⟩
  have rowU (i : Fin m) (j : Fin e) :
      U (.inl i) (.inr j)=(-lam i)*V (.inl i) (.inr j) := by
    linear_combination row i (.inr j)
  have colU (i : Fin m) (j : Fin d) :
      U (.inr j) (.inl i)=(-lam i)*V (.inr j) (.inl i) := by
    linear_combination col i (.inr j)
  have relate (s : S) (q : (Fin e ⊕ Fin d) × Fin m) :
      eval U s q=(-lam q.2)*eval V s q := by
    rcases q with ⟨j|i,k⟩
    · simp only [eval,Sum.elim_inl,Finset.mul_sum,rowU]
      apply Finset.sum_congr rfl
      intro i _
      ring
    · simp only [eval,Sum.elim_inr,Finset.mul_sum,colU]
      apply Finset.sum_congr rfl
      intro j _
      ring
  have plain := evals V (fun i j => (core i j).2) testV
  have weighted (s : S) : (-lam (L s).2)*eval V s (L s)+(-lam (R s).2)*eval V s (R s)=0 := by
    rw [← relate,← relate]
    exact evals U (fun i j => (core i j).1) testU s
  obtain ⟨Yzero,Xzero⟩ := interpolate_slots node (fun i j h => Fin.ext (Nat.cast_injective h))
    (fun i => -lam i) (fun i j h => hlam (neg_inj.mp h)) L R sample ne
    (fun i => (dist i).comp finSumFinEquiv.injective) cover
    (fun i j => V (.inl i) (.inr j)) (fun i j => V (.inr j) (.inl i)) plain weighted
  have zero : V=0 := by
    funext i j
    rcases i with i|i <;> rcases j with j|j
    · exact (core i j).2
    · exact congrFun (congrFun Yzero i) j
    · exact congrFun (congrFun Xzero j) i
    · exact lower V testV i j
  refine ⟨?_,zero⟩
  funext i j
  rcases i with i|i <;> rcases j with j|j
  · exact (core i j).1
  · simpa only [zero,Matrix.zero_apply,mul_zero] using rowU i j
  · simpa only [zero,Matrix.zero_apply,mul_zero] using colU j i
  · exact lower U testU i j

end CriticalLastSlice.HigherPencil

namespace HigherPencil

/-- A tensor annihilating the three tangent variations at each marked point
and the third variation at each exterior point detects surjectivity of their sum. -/
theorem augmented_span_of_annihilator {𝕜 I J K P Q : Type*} [Field 𝕜]
    [Fintype I] [Fintype J] [Fintype K] [Fintype P] [Fintype Q]
    (x : P → I → 𝕜) (y : P → J → 𝕜) (z : P → K → 𝕜) (x' : Q → I → 𝕜) (y' : Q → J → 𝕜)
    (detect : ∀ H : I → J → K → 𝕜,
      (∀ t i, ∑ j, ∑ k, (y t j*z t k)*H i j k=0) →
      (∀ t j, ∑ i, ∑ k, (x t i*z t k)*H i j k=0) →
      (∀ t k, ∑ i, ∑ j, (x t i*y t j)*H i j k=0) →
      (∀ t k, ∑ i, ∑ j, (x' t i*y' t j)*H i j k=0) → H=0) :
    ∀ T : I → J → K → 𝕜,
      ∃ u : P → I → 𝕜, ∃ v : P → J → 𝕜, ∃ w : P → K → 𝕜, ∃ w' : Q → K → 𝕜, ∀ i j k,
        T i j k = (∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) +
          ∑ t, x' t i*(y' t j*w' t k) := by
  classical
  let C := (P × I) ⊕ ((P × J) ⊕ ((P × K) ⊕ (Q × K)))
  let M : Matrix (I × J × K) C 𝕜
    | (i,j,k),.inl (t,h) => if h=i then y t j*z t k else 0
    | (i,j,k),.inr (.inl (t,h)) => if h=j then x t i*z t k else 0
    | (i,j,k),.inr (.inr (.inl (t,h))) => if h=k then x t i*y t j else 0
    | (i,j,k),.inr (.inr (.inr (t,h))) => if h=k then x' t i*y' t j else 0
  have no_rel (v : I × J × K → 𝕜) (hv : M.transpose.mulVec v=0) : v=0 := by
    let H (i : I) (j : J) (k : K) := v (i,j,k)
    have read (c : C) : (∑ q : I × J × K, M q c * v q)=0 := congrFun hv c
    have zero := detect H
      (fun t i => by simpa [H,M,Fintype.sum_prod_type,ite_mul,Finset.sum_ite_irrel] using read (.inl (t,i)))
      (fun t j => by simpa [H,M,Fintype.sum_prod_type,ite_mul,Finset.sum_ite_irrel] using read (.inr (.inl (t,j))))
      (fun t k => by simpa [H,M,Fintype.sum_prod_type,ite_mul] using read (.inr (.inr (.inl (t,k)))))
      (fun t k => by simpa [H,M,Fintype.sum_prod_type,ite_mul] using read (.inr (.inr (.inr (t,k)))))
    funext ⟨i,j,k⟩
    exact congrFun (congrFun (congrFun zero i) j) k
  have ker : LinearMap.ker M.transpose.mulVecLin=⊥ := by
    apply bot_unique
    intro u hu
    exact (Submodule.mem_bot 𝕜).mpr (no_rel u hu)
  have size := LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp ker)
  change M.transpose.rank=Module.finrank 𝕜 (I × J × K → 𝕜) at size
  rw [Matrix.rank_transpose] at size
  have onto : Function.Surjective M.mulVec := LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq size)
  intro T
  obtain ⟨p,hp⟩ := onto (fun q => T q.1 q.2.1 q.2.2)
  refine ⟨fun t i => p (.inl (t,i)),fun t j => p (.inr (.inl (t,j))),
    fun t k => p (.inr (.inr (.inl (t,k)))),fun t k => p (.inr (.inr (.inr (t,k)))),?_⟩
  intro i j k
  refine (congrFun hp (i,j,k)).symm.trans ?_
  change (∑ q : (P × I) ⊕ ((P × J) ⊕ ((P × K) ⊕ (Q × K))), M (i,j,k) q*p q)=_
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,M,ite_mul,zero_mul,Finset.sum_ite_eq',
    Finset.mem_univ,if_true,Finset.sum_add_distrib]
  simp only [mul_assoc,mul_comm,add_assoc]

end HigherPencil

namespace HigherPencil

/-- The pencil dimension budget is equivalent to having enough exterior
labels for the lower rectangle and the paired off-diagonal slots. -/
theorem local_pencil_budget_iff {a b m r : ℕ} (hm : 2 ≤ m) (ha : m ≤ a) (hb : m ≤ b)
    (hr : m ≤ r) :
    2*(a*b-r) ≤ m*(a+b-2) ↔
      (a-m)*(b-m)+(((b-m)+(a-m))*m+1)/2 ≤ r-m := by
  let d := a-m
  let e := b-m
  change 2*(a*b-r) ≤ m*(a+b-2) ↔ d*e+((e+d)*m+1)/2 ≤ r-m
  have sa : a=m+d := by dsimp only [d]; omega
  have sb : b=m+e := by dsimp only [e]; omega
  have arms : m*(a+b-2)+2*m=m*(a+b) := calc
    _ = m*((a+b-2)+2) := by ring
    _ = m*(a+b) := by rw [show a+b-2+2=a+b by omega]
  have count : 2*(a*b)=2*(d*e)+(e+d)*m+2*m+m*(a+b-2) := calc
    _ = 2*(d*e)+(e+d)*m+m*(a+b) := by rw [sa,sb]; ring
    _ = _ := by omega
  constructor
  · intro h
    have above : a*b ≤ r+(a*b-r) := by omega
    omega
  · intro h
    by_cases le : r ≤ a*b
    · have hsub := Nat.sub_add_cancel le
      omega
    · have hsub : a*b-r=0 := by omega
      rw [hsub]
      omega

end HigherPencil

namespace HigherPencil

/-- The marked diagonal pencil and its exterior products span the primal
tangent. The exterior labels beyond the interpolation schedule carry zero factors. -/
theorem local_pencil_blocks {m d e q : ℕ} (hm : 2 ≤ m) (room : d*e+((e+d)*m+1)/2 ≤ q) :
    let A := Fin m ⊕ Fin d
    let B := Fin m ⊕ Fin e
    ∃ x : Fin m → A → ℂ, ∃ y : Fin m → B → ℂ, ∃ z : Fin m → Fin 2 → ℂ,
    ∃ x' : Fin q → A → ℂ, ∃ y' : Fin q → B → ℂ,
    ∀ T : A → B → Fin 2 → ℂ,
      ∃ u : Fin m → A → ℂ, ∃ v : Fin m → B → ℂ,
      ∃ w : Fin m → Fin 2 → ℂ, ∃ w' : Fin q → Fin 2 → ℂ, ∀ i j k,
        T i j k = (∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) +
          ∑ t, x' t i*(y' t j*w' t k) := by
  classical
  intro A B
  let lam (t : Fin m) : ℂ := t.val
  have inject : Function.Injective lam := fun i j h => Fin.ext (Nat.cast_injective h)
  obtain ⟨X,Y,read⟩ := CriticalLastSlice.HigherPencil.product_samples (d:=d) (e:=e) hm lam inject
  let P := (Fin d × Fin e) ⊕ Fin (((e+d)*m+1)/2)
  have enough : Fintype.card P ≤ q := by simpa [P] using room
  let put : P ⊕ Fin (q-Fintype.card P) ≃ Fin q := Fintype.equivOfCardEq (by simp; omega)
  let xp (t : Fin q) : A → ℂ := (put.symm t).elim X 0
  let yp (t : Fin q) : B → ℂ := (put.symm t).elim Y 0
  let x (t : Fin m) (i : A) : ℂ := if Sum.inl t=i then 1 else 0
  let y (t : Fin m) (j : B) : ℂ := if Sum.inl t=j then 1 else 0
  let z (t : Fin m) : Fin 2 → ℂ := ![1,lam t]
  refine ⟨x,y,z,xp,yp,augmented_span_of_annihilator x y z xp yp ?_⟩
  intro H xvar yvar zvar exterior
  let U : Matrix A B ℂ := fun i j => H i j 0
  let V : Matrix A B ℂ := fun i j => H i j 1
  have diagonal (t : Fin m) (k : Fin 2) : H (.inl t) (.inl t) k = 0 := by
    simpa [A,B,x,y,mul_ite,ite_mul] using zvar t k
  have row (t : Fin m) (j : B) : U (.inl t) j+lam t*V (.inl t) j=0 := by
    simpa [A,x,z,U,V,Fin.sum_univ_two,ite_mul,Finset.sum_add_distrib] using yvar t j
  have col (t : Fin m) (i : A) : U i (.inl t)+lam t*V i (.inl t)=0 := by
    simpa [B,y,z,U,V,Fin.sum_univ_two,ite_mul,Finset.sum_add_distrib] using xvar t i
  have sampled (p : P) (k : Fin 2) : (∑ i,∑ j, X p i*Y p j*H i j k)=0 := by
    simpa only [xp,yp,Equiv.symm_apply_apply,Sum.elim_inl] using exterior (put (.inl p)) k
  obtain ⟨hu,hv⟩ := read U V (fun t => ⟨diagonal t 0,diagonal t 1⟩) row col
    (fun p => sampled p 0) (fun p => sampled p 1)
  funext i j k
  refine Fin.cases (congrFun (congrFun hu i) j) (fun h => ?_) k
  fin_cases h
  exact congrFun (congrFun hv i) j

end HigherPencil

namespace HigherPencil

/-- In actual finite coordinates a two-slice local tensor is spanned with
m full marked variations and r−m exterior third-factor variations whenever
the pencil dimension budget holds. -/
theorem local_pencil_fin {a b m r : ℕ} (hm : 2 ≤ m) (ha : m ≤ a) (hb : m ≤ b) (hr : m ≤ r)
    (budget : 2*(a*b-r) ≤ m*(a+b-2)) :
    ∃ x : Fin m → Fin a → ℂ, ∃ y : Fin m → Fin b → ℂ, ∃ z : Fin m → Fin 2 → ℂ,
    ∃ x' : Fin (r-m) → Fin a → ℂ, ∃ y' : Fin (r-m) → Fin b → ℂ,
    ∀ T : Fin a → Fin b → Fin 2 → ℂ,
      ∃ u : Fin m → Fin a → ℂ, ∃ v : Fin m → Fin b → ℂ,
      ∃ w : Fin m → Fin 2 → ℂ, ∃ w' : Fin (r-m) → Fin 2 → ℂ, ∀ i j k,
        T i j k = (∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) +
          ∑ t, x' t i*(y' t j*w' t k) := by
  let ea : Fin m ⊕ Fin (a-m) ≃ Fin a := finSumFinEquiv.trans (finCongr (by omega))
  let eb : Fin m ⊕ Fin (b-m) ≃ Fin b := finSumFinEquiv.trans (finCongr (by omega))
  have room := (local_pencil_budget_iff hm ha hb hr).mp budget
  obtain ⟨x,y,z,x',y',span⟩ := local_pencil_blocks (d:=a-m) (e:=b-m) hm room
  refine ⟨fun t i => x t (ea.symm i),fun t j => y t (eb.symm j),z,
    fun t i => x' t (ea.symm i),fun t j => y' t (eb.symm j),?_⟩
  intro T
  obtain ⟨u,v,w,w',hit⟩ := span (fun i j k => T (ea i) (eb j) k)
  refine ⟨fun t i => u t (ea.symm i),fun t j => v t (eb.symm j),w,w',?_⟩
  intro i j k
  simpa only [Equiv.apply_symm_apply] using hit (ea.symm i) (eb.symm j) k

end HigherPencil

namespace CriticalHigher

/-- A two-dimensional block on any axis suffices whenever the marked points
fit and their pencil variations provide the local parameter count. The
criterion is arithmetic in the four dimensions. -/
theorem tangent_of_pencil_screen {a b n r : ℕ}
    (screen :
      let ok (u v w : ℕ) := ∃ h m, w = 2*h ∧ h*m ≤ r ∧ 2 ≤ m ∧ m ≤ u ∧ m ≤ v ∧ m ≤ r ∧ 2*(u*v-r) ≤ m*(u+v-2)
      ok a b n ∨ ok b n a ∨ ok a n b) :
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
      ∀ T : Fin a → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
      ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
        T i j k=∑ t,(u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k)) := by
  rcases screen with ⟨h,m,rfl,slots,hm,ha,hb,hr,budget⟩ |
    ⟨h,m,rfl,slots,hm,hb,hn,hr,budget⟩ | ⟨h,m,rfl,slots,hm,ha,hn,hr,budget⟩
  · exact Blocks.many_pencil_third a b h m r slots (HigherPencil.local_pencil_fin hm ha hb hr budget)
  · exact Blocks.many_pencil_first b n h m r slots (HigherPencil.local_pencil_fin hm hb hn hr budget)
  · exact Blocks.many_pencil_second a n h m r slots (HigherPencil.local_pencil_fin hm ha hn hr budget)

/-- An integer t with 2≤t≤min(a,b) gives a perfect format whenever
ab=t(h+(a+b−2)/2) in the denominator-free form below. This includes
formats for which the block axis is the only even dimension. -/
theorem perfect_pencil_format {a b h t : ℕ} (ha : 3≤a) (hab : a≤b) (order : b≤2*h)
    (ht : 2 ≤ t) (htA : t≤a) (balance : 2*(a*b)=t*(a+b+2*h-2)) :
    Arxiv.«0805.3777».IsGenericRank [a,b,2*h] (h*t) := by
  have hp : 0<h := by omega
  have den : 0<a+b+2*h-2 := by omega
  have num : a*b*(2*h)=(a+b+2*h-2)*(h*t) := by nlinarith only [congrArg (·*h) balance]
  have count : h*t=a*b*(2*h) ⌈/⌉ (a+b+2*h-2) := by
    rw [num]
    apply le_antisymm
    · exact Nat.le_of_mul_le_mul_left ((ceilDiv_le_iff_le_mul den).mp le_rfl) den
    · exact (ceilDiv_le_iff_le_mul den).mpr le_rfl
  have hr : t ≤ h*t := by
    simpa only [one_mul] using Nat.mul_le_mul_right t (show 1 ≤ h from hp)
  have identity : 2*(a*b)=t*(a+b-2)+2*(h*t) := by
    rw [balance,show a+b+2*h-2=(a+b-2)+2*h by omega]
    ring
  have small : h*t≤a*b := by omega
  have budget : 2*(a*b-h*t)≤t*(a+b-2) := by omega
  apply CriticalLastSlice.TwoPlanes.generic_rank_of_witness ha hab order count
  apply tangent_of_pencil_screen
  exact Or.inl ⟨h,t,rfl,le_rfl,ht,htA,htA.trans hab,hr,budget⟩

/-- Even the two unsplit axes may both be odd. Taking three marks per
pencil gives unbounded first dimensions in this rectangular family. -/
theorem odd_sides_three_marks (s t : ℕ) (ordered : 2*s+5 ≤ 6*t+3) :
    let h := (4*s+7)*t+s+2
    Arxiv.«0805.3777».IsGenericRank [2*s+5,6*t+3,2*h] (3*h) := by
  intro h
  have positive : 6*t+3 ≤ 2*h := by dsimp [h]; nlinarith
  have den : (2*s+5)+(6*t+3)+2*h-2=(2*s+5)+(6*t+3)+2*((4*s+7)*t+s+1) := by dsimp [h]; omega
  have balance : 2*((2*s+5)*(6*t+3))=3*((2*s+5)+(6*t+3)+2*h-2) := by rw [den]; ring
  simpa only [Nat.mul_comm h 3] using
    (perfect_pencil_format (a:=2*s+5) (b:=6*t+3) (h:=h) (t:=3) (by omega) ordered positive
      (by decide) (by omega) balance)

/-- For equal sides a=3(s+2), three marks in each pencil give rank 3h
at third dimension 2h, where h=a(s+1)+1. On this family the normal-space
dimension (a−1)²+1−3h is a−1, and tends to infinity. -/
theorem square_three_marks (s : ℕ) :
    let a := 3*(s+2)
    let h := a*(s+1)+1
    Arxiv.«0805.3777».IsGenericRank [a,a,2*h] (3*h) ∧ (a-1)*(a-1)+1-3*h=a-1 := by
  intro a h
  have positive : a ≤ 2*h := by dsimp [a,h]; nlinarith
  have den : a+a+2*h-2=a+a+2*(a*(s+1)) := by dsimp [h]; omega
  have balance : 2*(a*a)=3*(a+a+2*h-2) := by rw [den]; dsimp [a]; ring
  have pred : a-1=3*s+5 := by dsimp [a]; omega
  have dimension : (3*s+5)*(3*s+5)+1=3*h+(3*s+5) := by dsimp [h,a]; ring
  refine ⟨?_,by rw [pred]; omega⟩
  simpa only [Nat.mul_comm h 3] using
    (perfect_pencil_format (a:=a) (b:=a) (h:=h) (t:=3) (by dsimp [a]; omega) le_rfl
      positive (by decide) (by dsimp [a]; omega) balance)

end CriticalHigher

namespace CriticalThreeQuotient

/-- The two point equations determine a three-slice normal at each ordered
pair of distinct samples. Its remaining freedom is one scalar per pair. -/
theorem normal_entries {K I : Type*} [Field K] (l m : I → K)
    (distinct : Function.Injective l) (A B C : I → I → K)
    (diag : ∀ s, A s s = 0 ∧ B s s = 0 ∧ C s s = 0)
    (row : ∀ s t, A s t + l s*B s t + m s*C s t = 0)
    (col : ∀ s t, A s t + l t*B s t + m t*C s t = 0) :
    ∃ E : I → I → K, ∀ s t,
      A s t = (l t*m s - l s*m t)*E s t ∧
      B s t = (m t - m s)*E s t ∧ C s t = (l s - l t)*E s t := by
  let E (s t : I) := C s t / (l s - l t)
  refine ⟨E, fun s t => ?_⟩
  by_cases eq : s=t
  · subst t
    simp [diag s]
  have gap : l s - l t ≠ 0 := sub_ne_zero.mpr (distinct.ne eq)
  have hC : C s t = (l s-l t)*E s t := by dsimp [E]; field_simp
  have hB : B s t = (m t-m s)*E s t := by
    apply (mul_left_cancel₀ gap)
    linear_combination (row s t) - (col s t) - (m s-m t)*hC
  exact ⟨by linear_combination (row s t) - l s*hB - m s*hC,hB,hC⟩

/-- Injectivity modulo diagonal matrices of the two compressed diagonal
commutators kills the full normal. The third slice is then forced entrywise. -/
theorem normal_zero_of_commutators {K I U V : Type*} [Field K] [Fintype I]
    (l m : I → K) (distinct : Function.Injective l) (P : U → I → K) (Q : V → I → K)
    (exactPair : ∀ E : I → I → K,
      (∀ u t, ∑ s, P u s*((l s-l t)*E s t) = 0) →
      (∀ u t, ∑ s, P u s*((m s-m t)*E s t) = 0) →
      (∀ v s, ∑ t, ((l s-l t)*E s t)*Q v t = 0) →
      (∀ v s, ∑ t, ((m s-m t)*E s t)*Q v t = 0) →
      ∀ s t, s≠t → E s t=0)
    (A B C : I → I → K)
    (diag : ∀ s, A s s = 0 ∧ B s s = 0 ∧ C s s = 0)
    (row : ∀ s t, A s t + l s*B s t + m s*C s t = 0)
    (col : ∀ s t, A s t + l t*B s t + m t*C s t = 0)
    (leftB : ∀ u t, ∑ s, P u s*B s t = 0)
    (leftC : ∀ u t, ∑ s, P u s*C s t = 0)
    (rightB : ∀ v s, ∑ t, B s t*Q v t = 0)
    (rightC : ∀ v s, ∑ t, C s t*Q v t = 0) :
    ∀ s t, A s t=0 ∧ B s t=0 ∧ C s t=0 := by
  obtain ⟨E,entries⟩ := normal_entries l m distinct A B C diag row col
  have eC (s t) := (entries s t).2.2
  have eB (s t) : (m s-m t)*E s t = -B s t := by
    rw [(entries s t).2.1]
    ring
  have zero := exactPair E
    (fun u t => by simpa only [← eC] using leftC u t)
    (fun u t => by simp only [eB,mul_neg,Finset.sum_neg_distrib,leftB,neg_zero])
    (fun v s => by simpa only [← eC] using rightC v s)
    (fun v s => by simp only [eB,neg_mul,Finset.sum_neg_distrib,rightB,neg_zero])
  intro s t
  by_cases eq : s=t
  · subst t
    exact diag s
  · simpa only [zero s t eq,mul_zero] using entries s t

/-- A three-slice CP tangent spans if the two diagonal commutators have no
off-diagonal common kernel after compression by relations of the two frames. -/
theorem tangent_of_commutators {K U V : Type*} [Field K] {b n r : ℕ}
    (l m : Fin r → K) (distinct : Function.Injective l)
    (Y : Matrix (Fin r) (Fin b) K) (Z : Matrix (Fin r) (Fin n) K)
    (P : Matrix U (Fin r) K) (Q : Matrix V (Fin r) K)
    (pY : P * Y = 0) (qZ : Q * Z = 0)
    (embed : Function.Injective (fun N : Matrix (Fin b) (Fin n) K => Y * N * Z.transpose))
    (exactPair : ∀ E : Fin r → Fin r → K,
      (∀ u t, ∑ s, P u s*((l s-l t)*E s t) = 0) →
      (∀ u t, ∑ s, P u s*((m s-m t)*E s t) = 0) →
      (∀ v s, ∑ t, ((l s-l t)*E s t)*Q v t = 0) →
      (∀ v s, ∑ t, ((m s-m t)*E s t)*Q v t = 0) →
      ∀ s t, s≠t → E s t=0) :
    let x (s : Fin r) : Fin 3 → K := ![1,l s,m s]
    ∀ T : Fin 3 → Fin b → Fin n → K, ∃ u : Fin r → Fin 3 → K,
      ∃ v : Fin r → Fin b → K, ∃ w : Fin r → Fin n → K, ∀ i j k,
        T i j k=∑ t, (u t i*(Y t j*Z t k) + x t i*(v t j*Z t k) + x t i*(Y t j*w t k)) := by
  classical
  dsimp only
  let x (s : Fin r) : Fin 3 → K := ![1,l s,m s]
  let I := Fin r × (Fin 3 ⊕ (Fin b ⊕ Fin n))
  let M : Matrix ((Fin 3 × Fin b) × Fin n) I K := fun t s =>
    s.2.elim (fun i => if i=t.1.1 then Y s.1 t.1.2 * Z s.1 t.2 else 0)
      (Sum.elim (fun j => if j=t.1.2 then x s.1 t.1.1 * Z s.1 t.2 else 0)
        (fun k => if k=t.2 then x s.1 t.1.1 * Y s.1 t.1.2 else 0))
  have noRelation (H : (Fin 3 × Fin b) × Fin n → K) (relation : M.transpose.mulVec H=0) : H=0 := by
    obtain ⟨outer,diag,col⟩ := (LastSliceDual.transpose_kernel_iff x Y Z M (by intros; rfl) H).mp relation
    let N (i : Fin 3) : Matrix (Fin b) (Fin n) K := fun j k => H ((i,j),k)
    let S (i : Fin 3) := Y * N i * Z.transpose
    have value (i : Fin 3) (s t : Fin r) : S i s t = ∑ j, Y s j*(∑ k, Z t k*H ((i,j),k)) := by
      change (∑ k, (∑ j, Y s j * H ((i,j),k)) * Z t k) = _
      simp only [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    have rowEq (s t : Fin r) : ∑ i, x s i * S i s t = 0 := by
      calc
        _ = ∑ k, Z t k * (∑ ij : Fin 3 × Fin b, (x s ij.1*Y s ij.2)*H (ij,k)) := by
          simp only [value,Fintype.sum_prod_type,Finset.mul_sum]
          calc
            _ = ∑ i, ∑ k, ∑ j, x s i*(Y s j*(Z t k*H ((i,j),k))) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.sum_comm]
            _ = _ := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro k _
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = 0 := by simp [outer]
    have colEq (s t : Fin r) : ∑ i, x t i * S i s t = 0 := by
      calc
        _ = ∑ j, Y s j * (∑ i, x t i*(∑ k, Z t k*H ((i,j),k))) := by
          simp only [value,Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = 0 := by simp [col]
    have leftZero (i : Fin 3) (u : U) (t : Fin r) : ∑ s, P u s*S i s t=0 := by
      have e : P * S i=0 := by simp [S,← Matrix.mul_assoc,pY]
      exact congrFun (congrFun e u) t
    have rightZero (i : Fin 3) (v : V) (s : Fin r) : ∑ t, S i s t*Q v t=0 := by
      have e : S i * Q.transpose=0 := by simp [S,Matrix.mul_assoc,← Matrix.transpose_mul,qZ]
      exact congrFun (congrFun e s) v
    have vanish := normal_zero_of_commutators l m distinct P Q exactPair (S 0) (S 1) (S 2)
      (fun s => ⟨(value 0 s s).trans (diag s 0),(value 1 s s).trans (diag s 1),
        (value 2 s s).trans (diag s 2)⟩)
      (fun s t => by simpa [x,Fin.sum_univ_succ,add_assoc] using rowEq s t)
      (fun s t => by simpa [x,Fin.sum_univ_succ,add_assoc] using colEq s t)
      (leftZero 1) (leftZero 2) (rightZero 1) (rightZero 2)
    have allZero (i : Fin 3) : N i=0 := by
      apply embed
      simp only [Matrix.mul_zero,Matrix.zero_mul]
      ext s t
      fin_cases i
      · exact (vanish s t).1
      · exact (vanish s t).2.1
      · exact (vanish s t).2.2
    funext ⟨⟨i,j⟩,k⟩
    exact congrFun (congrFun (allZero i) j) k
  have surj : Function.Surjective M.mulVec := by
    have hk : LinearMap.ker M.transpose.mulVecLin=⊥ := by
      apply bot_unique
      exact fun t h => (Submodule.mem_bot K).mpr (noRelation t h)
    have hr := LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hk)
    change M.transpose.rank=Module.finrank K (((Fin 3 × Fin b) × Fin n) → K) at hr
    rw [Matrix.rank_transpose] at hr
    exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq hr)
  intro T
  obtain ⟨p,hp⟩ := surj fun q => T q.1.1 q.1.2 q.2
  refine ⟨fun t i => p (t,.inl i),fun t j => p (t,.inr (.inl j)),fun t k => p (t,.inr (.inr k)),?_⟩
  intro i j k
  refine (congrFun hp ((i,j),k)).symm.trans ?_
  change (∑ v : I, M ((i,j),k) v*p v)=_
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp [M,ite_mul,Finset.sum_ite_eq']
  ring

/-- When all three factors use characters, the two compressed commutators
are injective modulo the diagonal as soon as every frequency graph is connected.
The hypotheses state connectivity as propagation of values along its edges. -/
theorem commutators_of_frequency_graphs {G K I U V : Type*} [AddCommGroup G] [Field K] [Fintype I]
    (χ : G → I → K) (law : ∀ a b t, χ (a+b) t=χ a t*χ b t)
    (fourier : Function.Injective (fun N : I → I → K => fun i j : G =>
      ∑ s, ∑ t, χ i s*(N s t*χ j t)))
    (one d : G) (distinct : Function.Injective (χ one)) (P : U → G) (Q : V → G)
    (connected : ∀ k : G, ∀ f : G → K,
      (∀ u, f (P u+one)=f (P u) ∧ f (P u+d)=f (P u)) →
      (∀ v, f (k-Q v-one)=f (k-Q v) ∧ f (k-Q v-d)=f (k-Q v)) →
      ∀ i j, f i=f j)
    (E : I → I → K)
    (leftOne : ∀ u t, ∑ s, χ (P u) s*((χ one s-χ one t)*E s t) = 0)
    (leftD : ∀ u t, ∑ s, χ (P u) s*((χ d s-χ d t)*E s t) = 0)
    (rightOne : ∀ v s, ∑ t, ((χ one s-χ one t)*E s t)*χ (Q v) t = 0)
    (rightD : ∀ v s, ∑ t, ((χ d s-χ d t)*E s t)*χ (Q v) t = 0) :
    ∀ s t, s≠t → E s t=0 := by
  let M (i j : G) := ∑ s, ∑ t, χ i s*(E s t*χ j t)
  let C (c i j : G) := ∑ s, ∑ t, χ i s*(((χ c s-χ c t)*E s t)*χ j t)
  have shift (c i j : G) : M (i+c) j-M i (j+c)=C c i j := by
    simp only [M,C,law,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    ring
  have leftEdge (c : G) (left : ∀ u t, ∑ s, χ (P u) s*((χ c s-χ c t)*E s t)=0)
      (u : U) (j : G) : M (P u+c) j=M (P u) (j+c) := by
    apply sub_eq_zero.mp
    rw [shift]
    change (∑ s, ∑ t, χ (P u) s*(((χ c s-χ c t)*E s t)*χ j t))=0
    rw [Finset.sum_comm]
    calc
      _ = ∑ t, (∑ s, χ (P u) s*((χ c s-χ c t)*E s t)) * χ j t := by
        simp only [Finset.sum_mul,mul_assoc]
      _ = 0 := by simp [left]
  have rightEdge (c : G) (right : ∀ v s, ∑ t, ((χ c s-χ c t)*E s t)*χ (Q v) t=0)
      (v : V) (i : G) : M (i+c) (Q v)=M i (Q v+c) := by
    apply sub_eq_zero.mp
    rw [shift]
    change (∑ s, ∑ t, χ i s*(((χ c s-χ c t)*E s t)*χ (Q v) t))=0
    simp only [← Finset.mul_sum,right,mul_zero,Finset.sum_const_zero]
  have same (k i j : G) : M i (k-i)=M j (k-j) := by
    apply connected k (fun u => M u (k-u))
    · intro u
      have edge (c : G) (hyp : ∀ z, M (P u+c) z=M (P u) (z+c)) :
          M (P u+c) (k-(P u+c))=M (P u) (k-P u) := by
        rw [hyp,show k-(P u+c)+c=k-P u by abel]
      exact ⟨edge one (leftEdge one leftOne u),edge d (leftEdge d leftD u)⟩
    · intro v
      have edge (c : G) (hyp : ∀ z, M (z+c) (Q v)=M z (Q v+c)) :
          M (k-Q v-c) (k-(k-Q v-c))=M (k-Q v) (k-(k-Q v)) := by
        rw [show k-(k-Q v-c)=Q v+c by abel,show k-(k-Q v)=Q v by abel,← hyp,
          show k-Q v-c+c=k-Q v by abel]
      exact ⟨edge one (rightEdge one rightOne v),edge d (rightEdge d rightD v)⟩
  have zero (i j : G) : C one i j=0 := by
    rw [← shift,sub_eq_zero]
    have h := same (i+j+one) (i+one) i
    rwa [show i+j+one-(i+one)=j by abel,show i+j+one-i=j+one by abel] at h
  have annihilated : (fun s t => (χ one s-χ one t)*E s t) = (0 : I → I → K) := by
    apply fourier
    funext i j
    simpa only [Pi.zero_apply,zero_mul,mul_zero,Finset.sum_const_zero] using zero i j
  intro s t ne
  have h := congrFun (congrFun annihilated s) t
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (distinct.ne ne))

/-- Connected frequency graphs give a complex CP tangent at the literal
character factors, with the omitted Fourier modes as frame relations. -/
theorem tangent_of_cyclic_graphs {r b n : ℕ} [NeZero r] (d : ZMod r)
    (P Q : Finset (ZMod r)) (Y : Fin b ↪ ZMod r) (Z : Fin n ↪ ZMod r)
    (avoidY : ∀ j, Y j ∉ P) (avoidZ : ∀ k, Z k ∉ Q)
    (connected : ∀ k : ZMod r, ∀ f : ZMod r → ℂ,
      (∀ u ∈ P, f (u+1)=f u ∧ f (u+d)=f u) →
      (∀ v ∈ Q, f (k-v-1)=f (k-v) ∧ f (k-v-d)=f (k-v)) →
      ∀ i j, f i=f j) :
    ∃ x : Fin r → Fin 3 → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
    ∀ T : Fin 3 → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin 3 → ℂ,
      ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
        T i j k=∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
  classical
  let e := (ZMod.finEquiv r).toEquiv
  let χ (i : ZMod r) (s : Fin r) : ℂ := ZMod.stdAddChar (e s*i)
  have law (a b : ZMod r) (t : Fin r) : χ (a+b) t=χ a t*χ b t := by
    simp only [χ,mul_add,AddChar.map_add_eq_mul]
  have injective : Function.Injective (χ 1) := by
    simpa only [χ,mul_one,Function.comp_def] using ZMod.injective_stdAddChar.comp e.injective
  have orth (i j : ZMod r) : ∑ s, χ i s*χ (-j) s = if i=j then (r:ℂ) else 0 := by
    calc
      _ = ∑ s : Fin r, ZMod.stdAddChar (e s*(i-j)) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [← law,← sub_eq_add_neg]
      _ = ∑ t : ZMod r, ZMod.stdAddChar (t*(i-j)) := e.sum_comp (fun t : ZMod r => ZMod.stdAddChar (t*(i-j)))
      _ = _ := by
        rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar _),ZMod.card]
        by_cases h : i=j <;> simp [h,sub_eq_zero]
  have separates (a b : Fin r → ℂ) (test : ∀ i : ZMod r, ∑ s, χ i s*a s=∑ s, χ i s*b s) : a=b := by
    have eq : (fun j => a (e.symm j))=(fun j => b (e.symm j)) := by
      apply ZMod.dft.injective
      funext i
      rw [ZMod.dft_apply,ZMod.dft_apply]
      simp only [smul_eq_mul]
      rw [← e.sum_comp (fun t : ZMod r => ZMod.stdAddChar (-(t*i))*a (e.symm t)),
        ← e.sum_comp (fun t : ZMod r => ZMod.stdAddChar (-(t*i))*b (e.symm t))]
      simpa only [e.symm_apply_apply,χ,mul_neg] using test (-i)
    funext s
    simpa only [e.symm_apply_apply] using congrFun eq (e s)
  have fourier : Function.Injective (fun N : Fin r → Fin r → ℂ => fun i j : ZMod r =>
      ∑ s, ∑ t, χ i s*(N s t*χ j t)) := by
    intro A B he
    have each (j : ZMod r) : (fun s => ∑ t, A s t*χ j t)=(fun s => ∑ t, B s t*χ j t) := by
      apply separates
      intro i
      simpa only [Finset.mul_sum] using congrFun (congrFun he i) j
    funext s
    apply separates
    intro j
    simpa only [mul_comm (χ j _)] using congrFun (each j) s
  let frame {m : ℕ} (H : Fin m ↪ ZMod r) : Matrix (Fin r) (Fin m) ℂ := fun s j => χ (-(H j)) s
  let dual {m : ℕ} (H : Fin m ↪ ZMod r) : Matrix (Fin m) (Fin r) ℂ := fun j s => χ (H j) s / r
  have frameId {m : ℕ} (H : Fin m ↪ ZMod r) : dual H * frame H=1 := by
    ext i j
    change (∑ s, (χ (H i) s/r)*χ (-(H j)) s)=_
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div,orth]
    by_cases h : i=j
    · subst j
      simp [NeZero.ne r]
    · simp [h,H.injective.ne h]
  have embed : Function.Injective (fun N : Matrix (Fin b) (Fin n) ℂ => frame Y*N*(frame Z).transpose) := by
    intro A B eq
    have extract (N : Matrix (Fin b) (Fin n) ℂ) :
        (dual Y)*(frame Y*N*(frame Z).transpose)*(dual Z).transpose=N := by
      rw [← Matrix.mul_assoc,← Matrix.mul_assoc,frameId,Matrix.one_mul,Matrix.mul_assoc,
        ← Matrix.transpose_mul,frameId,Matrix.transpose_one,Matrix.mul_one]
    exact (extract A).symm.trans ((congrArg (fun N => (dual Y)*N*(dual Z).transpose) eq).trans (extract B))
  have annihilate {m : ℕ} (A : Finset (ZMod r)) (H : Fin m ↪ ZMod r) (avoid : ∀ j, H j∉A) :
      (Matrix.of (fun (i : A) (t : Fin r) => χ i.val t))*frame H=0 := by
    ext i j
    change (∑ s, χ i.val s*χ (-(H j)) s)=0
    have ne : i.val≠H j := fun h => avoid j (h ▸ i.property)
    rw [orth,if_neg ne]
  refine ⟨fun s => ![1,χ 1 s,χ d s],frame Y,frame Z,?_⟩
  apply tangent_of_commutators (χ 1) (χ d) injective (frame Y) (frame Z) _ _
    (annihilate P Y avoidY) (annihilate Q Z avoidZ) embed
  exact commutators_of_frequency_graphs χ law fourier 1 d injective Subtype.val Subtype.val
    (fun k f left right => connected k f (fun i hi => left ⟨i,hi⟩) (fun i hi => right ⟨i,hi⟩))

/-- The dimensions complementary to the two relation sets determine frames
from the unused frequencies. -/
theorem tangent_of_graph_cards {r b n : ℕ} [NeZero r] (d : ZMod r)
    (P Q : Finset (ZMod r)) (pCard : P.card+b=r) (qCard : Q.card+n=r)
    (connected : ∀ k : ZMod r, ∀ f : ZMod r → ℂ,
      (∀ u ∈ P, f (u+1)=f u ∧ f (u+d)=f u) →
      (∀ v ∈ Q, f (k-v-1)=f (k-v) ∧ f (k-v-d)=f (k-v)) →
      ∀ i j, f i=f j) :
    ∃ x : Fin r → Fin 3 → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
    ∀ T : Fin 3 → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin 3 → ℂ,
      ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
        T i j k=∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
  classical
  have choose {m : ℕ} (F : Finset (ZMod r)) (count : F.card+m=r) :
      ∃ J : Fin m ↪ ZMod r, ∀ i, J i∉F := by
    have size : Fintype.card (Fin m)=Fintype.card (↥(Fᶜ) : Type) := by
      rw [Fintype.card_fin,Fintype.card_coe,Finset.card_compl,ZMod.card]
      omega
    let e := Fintype.equivOfCardEq size
    exact ⟨e.toEmbedding.trans (Function.Embedding.subtype _),
      fun i => Finset.mem_compl.mp (e i).property⟩
  obtain ⟨Y,hy⟩ := choose P pCard
  obtain ⟨Z,hz⟩ := choose Q qCard
  exact tangent_of_cyclic_graphs d P Q Y Z hy hz connected

/-- ceil((r−W)/d) is the least number of right centers making the
closing gap at most W. All its sampled centers are distinct modulo r. -/
theorem least_chain {r W d : ℕ} (width : W≤r) (hd : 0<d) (step : d≤W) :
    let q := (r-W) ⌈/⌉ d
    q*d<r ∧ r≤q*d+W ∧ ∀ t : ℕ,r≤t*d+W ↔ q≤t := by
  intro q
  have least (t : ℕ) : r≤t*d+W ↔ q≤t := by
    change r≤t*d+W ↔ (r-W) ⌈/⌉ d≤t
    rw [ceilDiv_le_iff_le_mul hd,Nat.mul_comm d t]
    omega
  have upper : q*d≤(r-W+d-1) := by
    change ((r-W) ⌈/⌉ d)*d≤r-W+d-1
    rw [Nat.ceilDiv_eq_add_pred_div]
    exact Nat.div_mul_le_self _ _
  exact ⟨by omega,(least q).mpr le_rfl,least⟩

/-- Within a block of width 2L+1 the L centers have steps +1 and +(L+1).
These edges force the value on every position to equal the block's first value. -/
theorem block_constant {r L : ℕ} {C : Type*} (f : ZMod r → C) (z : ZMod r)
    (edge : ∀ i : Fin L, f (z+(i.val:ZMod r)+1)=f (z+i.val) ∧
      f (z+(i.val:ZMod r)+((L+1:ℕ):ZMod r))=f (z+i.val)) :
    ∀ o : ℕ,o<2*L+1 → f (z+(o:ZMod r))=f z := by
  have first (t : ℕ) (ht : t≤L) : f (z+(t:ZMod r))=f z := by
    induction t with
    | zero => simp
    | succ t ih =>
      simpa only [Nat.cast_succ,← add_assoc] using
        ((edge ⟨t,by omega⟩).1.trans (ih (by omega)))
  intro o ho
  by_cases h : o≤L
  · exact first o h
  · let i : Fin L := ⟨o-(L+1),by omega⟩
    have eq : i.val+(L+1)=o := by dsimp [i]; omega
    have same : z+(i.val:ZMod r)+((L+1:ℕ):ZMod r)=z+(o:ZMod r) := by
      rw [add_assoc,← Nat.cast_add,eq]
    rw [← same]
    exact (edge i).2.trans (first i.val i.isLt.le)

/-- The longer block has centers 0 and 2 through L+1. Its 0 to L+1
edge joins the two unit chains; its long edges cover the remaining positions. -/
theorem long_block_constant {L : ℕ} (hL : 2≤L) {C : Type*} (f : ℕ → C)
    (first : f 1=f 0 ∧ f (L+1)=f 0)
    (edges : ∀ t : ℕ,2≤t → t≤L+1 → f (t+1)=f t ∧ f (t+(L+1))=f t) :
    ∀ o : ℕ,o<2*L+3 → f o=f 0 := by
  have run (t : ℕ) (lo : 2≤t) (hi : t≤L+2) : f t=f 2 := by
    induction t with
    | zero => omega
    | succ t ih =>
      by_cases eq : t+1=2
      · rw [eq]
      · exact ((edges t (by omega) (by omega)).1).trans (ih (by omega) (by omega))
  have two : f 2=f 0 := (run (L+1) (by omega) (by omega)).symm.trans first.2
  intro o ho
  by_cases small : o<2
  · rcases (by omega : o=0 ∨ o=1) with rfl|rfl
    · rfl
    · exact first.1
  · by_cases mid : o≤L+2
    · exact (run o (by omega) mid).trans two
    · let t := o-(L+1)
      have eq : t+(L+1)=o := by dsimp [t]; omega
      have lo : 2≤t := by dsimp [t]; omega
      have hi : t≤L+1 := by dsimp [t]; omega
      rw [← eq]
      exact ((edges t lo hi).2).trans ((run t lo (by omega)).trans two)

/-- Exactly L+1 distinct left Fourier modes are used in a long block. -/
theorem long_centers (L : ℕ) :
    ∃ centers : Fin (L+1) ↪ Fin (2*L+3),
      ∀ t : ℕ,(∃ i, (centers i).val=t) ↔ t=0 ∨ 2≤t ∧ t≤L+1 := by
  let centers (i : Fin (L+1)) : Fin (2*L+3) :=
    ⟨if i.val=0 then 0 else i.val+1,by split <;> have := i.isLt <;> omega⟩
  have inj : Function.Injective centers := by
    intro i j eq
    apply Fin.ext
    have raw := congrArg Fin.val eq
    change (if i.val=0 then 0 else i.val+1)=(if j.val=0 then 0 else j.val+1) at raw
    split_ifs at raw <;> omega
  refine ⟨⟨centers,inj⟩,?_⟩
  intro t
  constructor
  · rintro ⟨i,rfl⟩
    change (if i.val=0 then 0 else i.val+1)=0 ∨
      2≤(if i.val=0 then 0 else i.val+1) ∧ (if i.val=0 then 0 else i.val+1)≤L+1
    split_ifs <;> have := i.isLt <;> omega
  · rintro (rfl|⟨lo,hi⟩)
    · exact ⟨0,by simp [centers]⟩
    · let t' : Fin (L+1) := ⟨t-1,by omega⟩
      refine ⟨t',?_⟩
      change (if t-1=0 then 0 else t-1+1)=t
      split <;> omega

/-- The gaps between d-spaced samples, including the closing gap, are at
most W. Every residue u is thus t*d plus an offset in [0,W), for t≤q. -/
theorem chain_hits {r W d q u : ℕ} (hd : 0<d) (step : d≤W) (closing : r≤q*d+W)
    (hr : u<r) : ∃ t≤q, ∃ o<W,t*d+o=u := by
  by_cases h : u<q*d
  · refine ⟨u/d,((Nat.div_lt_iff_lt_mul hd).mpr h).le,u%d,(Nat.mod_lt u hd).trans_le step,?_⟩
    rw [Nat.mul_comm,Nat.div_add_mod]
  · exact ⟨q,le_rfl,u-q*d,by omega,by omega⟩

/-- A chain intersects every constant patch that contains at least W
consecutive residues from its start. Patch lengths may vary. -/
theorem patches_of_chain {r W d q : ℕ} [NeZero r] {C : Type*} (f : ZMod r → C) (k : ZMod r)
    (hd : 0<d) (step : d≤W) (closing : r≤q*d+W)
    (patch : ∀ x,∃ B : ZMod r, f x=f B ∧ ∀ o : ℕ,o<W → f (B+(o:ZMod r))=f B)
    (edge : ∀ t : Fin q,f (k-((t.val*d:ℕ):ZMod r)-(d:ZMod r))=f (k-((t.val*d:ℕ):ZMod r))) :
    ∀ i j,f i=f j := by
  have chain (t : ℕ) (ht : t≤q) : f (k-((t*d:ℕ):ZMod r))=f k := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Nat.succ_mul,Nat.cast_add,← sub_sub]
      exact (edge ⟨t,by omega⟩).trans (ih (by omega))
  have all (x : ZMod r) : f x=f k := by
    obtain ⟨B,hx,flat⟩ := patch x
    obtain ⟨t,ht,o,ho,dist⟩ := chain_hits hd step closing (k-B).val_lt
    have eq : ((t*d:ℕ):ZMod r)+(o:ZMod r)=k-B := by
      rw [← Nat.cast_add,dist,ZMod.natCast_zmod_val]
    have hit : B+(o:ZMod r)=k-((t*d:ℕ):ZMod r) := by linear_combination eq
    exact hx.trans ((flat _ ho).symm.trans ((congrArg f hit).trans (chain _ ht)))
  exact fun i j => (all i).trans (all j).symm

/-- Use s initial blocks of width 2L+3 and h−s final blocks of width 2L+1.
Their Fourier centers and one chain of q right modes connect every frequency
graph whenever the chain and its closing gap fit the shorter block width. -/
theorem mixed_graphs_of_q (h L s q : ℕ) (hh : 0<h) (hL : 2≤L) (hs : s≤h)
    (short : q*(L+1)≤h*(2*L+1)+2*s)
    (cover : h*(2*L+1)+2*s≤q*(L+1)+(2*L+1)) :
    let r := h*(2*L+1)+2*s
    ∃ P Q : Finset (ZMod r), P.card=h*L+s ∧ Q.card=q ∧
      ∀ k : ZMod r,∀ f : ZMod r → ℂ,
        (∀ u∈P,f (u+1)=f u ∧ f (u+((L+1:ℕ):ZMod r))=f u) →
        (∀ v∈Q,f (k-v-1)=f (k-v) ∧ f (k-v-((L+1:ℕ):ZMod r))=f (k-v)) →
        ∀ i j,f i=f j := by
  classical
  intro r
  let W := 2*L+1
  let U := 2*L+3
  let d := L+1
  have hw : 0<W := by dsimp [W]; omega
  have hd : 0<d := by dsimp [d]; omega
  have hr : 0<r := Nat.add_pos_left (Nat.mul_pos hh hw) _
  let : NeZero r := ⟨hr.ne'⟩
  have widths : s*U+(h-s)*W=r := by
    have split := congrArg (·*W) (Nat.sub_add_cancel hs)
    change (h-s+s)*W=h*W at split
    change s*U+(h-s)*W=h*W+2*s
    rw [show U=W+2 by rfl]
    nlinarith only [split]
  let G := (Fin s × Fin U) ⊕ (Fin (h-s) × Fin W)
  let M := (Fin s × Fin (L+1)) ⊕ (Fin (h-s) × Fin L)
  let slot : G ≃ Fin r :=
    ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv).trans (finCongr widths)
  let residue : Fin r ↪ ZMod r :=
    { toFun := fun i => (i.val:ZMod r)
      inj' := by
        intro i j eq
        apply Fin.ext
        have raw := congrArg ZMod.val eq
        simpa only [ZMod.val_natCast_of_lt i.isLt,ZMod.val_natCast_of_lt j.isLt] using raw }
  let enc : G ↪ ZMod r := slot.toEmbedding.trans residue
  have onto : Function.Surjective enc := by
    intro x
    obtain ⟨p,hp⟩ := slot.surjective ⟨x.val,x.val_lt⟩
    refine ⟨p,?_⟩
    change ((slot p).val : ZMod r)=x
    rw [hp,ZMod.natCast_zmod_val]
  let lb (j : Fin s) : ZMod r := ((j.val*U:ℕ):ZMod r)
  let sb (j : Fin (h-s)) : ZMod r := ((s*U+j.val*W:ℕ):ZMod r)
  have leval (j : Fin s) (i : Fin U) : enc (.inl (j,i))=lb j+(i.val:ZMod r) := by
    change ((i.val+U*j.val:ℕ):ZMod r)=((j.val*U:ℕ):ZMod r)+i.val
    push_cast
    ring
  have seval (j : Fin (h-s)) (i : Fin W) : enc (.inr (j,i))=sb j+(i.val:ZMod r) := by
    change ((s*U+(i.val+W*j.val):ℕ):ZMod r)=((s*U+j.val*W:ℕ):ZMod r)+i.val
    push_cast
    ring
  obtain ⟨lc,lcRange⟩ := long_centers L
  let sc : Fin L ↪ Fin W := Fin.castLEEmb (by dsimp [W]; omega)
  let pick : M ↪ G := ((Function.Embedding.refl (Fin s)).prodMap lc).sumMap
    ((Function.Embedding.refl (Fin (h-s))).prodMap sc)
  let pe := pick.trans enc
  let P := Finset.univ.map pe
  have lmem (j : Fin s) (i : ℕ) (hi : i=0 ∨ 2≤ i ∧ i≤L+1) : lb j+(i:ZMod r)∈P := by
    obtain ⟨t,ht⟩ := (lcRange i).mpr hi
    have hm : pe (.inl (j,t))∈P := Finset.mem_map.mpr ⟨.inl (j,t),Finset.mem_univ _,rfl⟩
    change enc (.inl (j,lc t))∈P at hm
    simpa only [leval,ht] using hm
  have smem (j : Fin (h-s)) (i : Fin L) : sb j+(i.val:ZMod r)∈P := by
    have hm : pe (.inr (j,i))∈P := Finset.mem_map.mpr ⟨.inr (j,i),Finset.mem_univ _,rfl⟩
    change enc (.inr (j,sc i))∈P at hm
    simpa only [seval,show (sc i).val=i.val from rfl] using hm
  have qlimit (t : Fin q) : t.val*d<r := (Nat.mul_lt_mul_of_pos_right t.isLt hd).trans_le short
  let qe : Fin q ↪ ZMod r :=
    { toFun := fun t => ((t.val*d:ℕ):ZMod r)
      inj' := by
        intro t u eq
        have raw := congrArg ZMod.val eq
        change (((t.val*d:ℕ):ZMod r)).val=(((u.val*d:ℕ):ZMod r)).val at raw
        rw [ZMod.val_natCast_of_lt (qlimit t),ZMod.val_natCast_of_lt (qlimit u)] at raw
        exact Fin.ext (Nat.eq_of_mul_eq_mul_right hd raw) }
  let Q := Finset.univ.map qe
  have countP : P.card=h*L+s := by
    simp only [P,Finset.card_map,Finset.card_univ,M,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    have split := congrArg (·*L) (Nat.sub_add_cancel hs)
    change (h-s+s)*L=h*L at split
    nlinarith only [split]
  refine ⟨P,Q,countP,by simp [Q],?_⟩
  intro k f left right
  have lf (j : Fin s) (o : ℕ) (ho : o<U) : f (lb j+(o:ZMod r))=f (lb j) := by
    let g (t : ℕ) := f (lb j+(t:ZMod r))
    have eq (i : ℕ) (hi : i=0 ∨ 2≤ i ∧ i≤L+1) :
        g (i+1)=g i ∧ g (i+(L+1))=g i := by
      have a := left (lb j+(i:ZMod r)) (lmem j i hi)
      simpa only [g,Nat.cast_add,Nat.cast_one,← add_assoc] using a
    have a := eq 0 (Or.inl rfl)
    have all := long_block_constant hL g (by simpa only [zero_add] using a)
      (fun t hlo hhi => eq t (.inr ⟨hlo,hhi⟩)) o ho
    simpa only [g,Nat.cast_zero,add_zero] using all
  have sf (j : Fin (h-s)) := block_constant f (sb j) (L:=L) (fun i => left _ (smem j i))
  apply patches_of_chain f k hd (by dsimp [d,W]; omega : d≤W) cover
  · intro x
    obtain ⟨⟨j,i⟩|⟨j,i⟩,rfl⟩ := onto x
    · exact ⟨lb j,(congrArg f (leval j i)).trans (lf j _ i.isLt),
        fun o ho => lf j o (by dsimp [W] at ho; dsimp [U]; omega)⟩
    · exact ⟨sb j,(congrArg f (seval j i)).trans (sf j _ i.isLt),sf j⟩
  · intro t
    exact (right (qe t) (Finset.mem_map.mpr ⟨t,Finset.mem_univ _,rfl⟩)).2

/-- The short-chain test after splitting the middle dimension into long and
short blocks. The remainder s can be any integer between 0 and h. -/
theorem mixed_tangent_of_capacity (h L s N : ℕ) (hh : 0<h) (hL : 2≤L) (hs : s≤h) :
    let W := 2*L+1
    let r := h*W+2*s
    let b := h*(L+1)+s
    N≤r → r≤(r-N)*(L+1)+W →
    ∃ x : Fin r → Fin 3 → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin N → ℂ,
      ∀ T : Fin 3 → Fin b → Fin N → ℂ, ∃ u : Fin r → Fin 3 → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin N → ℂ, ∀ i j k,
          T i j k=∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
  intro W r b enough cap
  have hw : 0<W := by dsimp [W]; omega
  have hr : 0<r := by have := Nat.mul_pos hh hw; dsimp [r]; omega
  have : NeZero r := ⟨hr.ne'⟩
  have wle : W≤r := by
    have le : W≤h*W := by simpa only [one_mul] using Nat.mul_le_mul_right W (show 1≤h from hh)
    dsimp [r]
    omega
  let q := (r-W) ⌈/⌉ (L+1)
  have vals := least_chain wle (by omega : 0<L+1) (by dsimp [W]; omega : L+1≤W)
  have qle : q≤r-N := (vals.2.2 _).mp cap
  obtain ⟨P,Q,cardP,cardQ,connected⟩ :=
    mixed_graphs_of_q h L s q hh hL hs vals.1.le vals.2.1
  have psize : P.card+b=r := by rw [cardP]; dsimp [b,r,W]; ring
  have qsize : Q.card+(r-q)=r := by rw [cardQ]; omega
  exact CriticalHigher.project (show N≤r-q by omega)
    (tangent_of_graph_cards _ P Q psize qsize connected)

/-- The mixed-width integer screen in the registered witness coordinates.
It supplies all generic weighted normal equations after the existing transfer. -/
theorem tangent_of_remainder_capacity (b N r h : ℕ) (hh : 0<h) (width : 3*h≤b)
    (enough : N≤r) (level : r+h=2*b) (cap : r+1≤(r-N+2)*(b/h)) :
    ∃ x : Fin r → Fin 3 → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin N → ℂ,
      ∀ T : Fin 3 → Fin b → Fin N → ℂ, ∃ u : Fin r → Fin 3 → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin N → ℂ, ∀ i j k,
          T i j k=∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
  let L := b/h-1
  let s := b%h
  have u : 3≤b/h := (Nat.le_div_iff_mul_le hh).mpr width
  have hL : 2≤L := by dsimp [L]; omega
  have hs : s<h := Nat.mod_lt _ hh
  have quotient : L+1=b/h := by dsimp [L]; omega
  have bsize : h*(L+1)+s=b := by rw [quotient]; exact Nat.div_add_mod b h
  have rsize : h*(2*L+1)+2*s=r := by nlinarith only [level,bsize]
  have capacity : r≤(r-N)*(L+1)+(2*L+1) := by
    rw [← quotient] at cap
    nlinarith only [cap]
  have witness := mixed_tangent_of_capacity h L s N hh hL hs.le
    (by rw [rsize]; exact enough) (by rw [rsize]; exact capacity)
  rwa [bsize,rsize] at witness

/-- The exact generic rank in any strict three-slice rectangle passing a
single integer test, with h=2b−r and the Euclidean quotient b/h. -/
theorem rank_of_remainder_capacity (b N r h : ℕ) (hh : 0<h) (hb : 3≤b) (width : 3*h≤b)
    (ordered : b≤N) (enough : N≤r) (level : r+h=2*b)
    (cap : r+1≤(r-N+2)*(b/h)) (count : 3*b*N ⌈/⌉ (b+N+1)=r) :
    Arxiv.«0805.3777».IsGenericRank [3,b,N] r  := by
  apply CriticalLastSlice.TwoPlanes.generic_rank_of_witness (by decide) hb ordered _
    (tangent_of_remainder_capacity b N r h hh width enough level cap)
  rw [show 3+b+N-2=b+N+1 by omega]
  exact count.symm

private theorem count_of_small_slack {p D r s : ℕ} (hd : 0<D)
    (slack : r*D=p+s) (small : s<D) : p ⌈/⌉ D=r := by
  apply le_antisymm ((ceilDiv_le_iff_le_mul hd).mpr (by nlinarith only [slack])) _
  by_contra! below
  have cover := (ceilDiv_le_iff_le_mul (a:=D) (b:=p) hd).mp le_rfl
  have grow := Nat.mul_le_mul_left D (show (p ⌈/⌉ D)+1≤r by omega)
  rw [Nat.mul_add,Nat.mul_one] at grow
  nlinarith only [grow,cover,slack,small]

/-- At the natural endpoint, b≥h² gives the exact expected count. One size
below, the stated linear inequality in b is necessary and sufficient. -/
theorem precise_mixed_counts (h b : ℕ) (hh : 3≤h) (lower : h^2≤b) :
    let r := 2*b-h
    let N := 2*b-3*h+1
    3≤b ∧ 3*h≤b ∧ b≤N ∧ N+1≤r ∧
    (3*b*N ⌈/⌉ (b+N+1)=r ↔ 3*h^2+h≤2*b+1) ∧
    3*b*(N+1) ⌈/⌉ (b+(N+1)+1)=r := by
  intro r N
  have width : 3*h≤b := by
    have prod := Nat.mul_le_mul_right h hh
    nlinarith only [prod,lower]
  have hb : 3≤b := by omega
  have idn : N+3*h=2*b+1 := by dsimp [N]; omega
  have idr : r+h=2*b := Nat.sub_add_cancel (by omega)
  have hp := congrArg (fun t : ℕ => t*h) (Nat.sub_add_cancel (by omega : 1≤h))
  have s₁ : r*(b+N+1)=3*b*N+(3*h*(h-1)+b+h) := by
    have e := congrArg (fun t : ℕ => t*(b+N+1)) idr
    have f := congrArg (fun t : ℕ => t*b) idn
    have g := congrArg (fun t : ℕ => t*h) idn
    nlinarith only [e,f,g,hp]
  have s₂ : r*(b+(N+1)+1)=3*b*(N+1)+3*h*(h-1) := by nlinarith only [s₁,idr]
  have small : 3*h*(h-1)<b+(N+1)+1 := by nlinarith only [lower,idn,hp]
  refine ⟨hb,width,by omega,by omega,⟨?_,?_⟩,count_of_small_slack (by omega) s₂ small⟩
  · intro count
    by_contra! fail
    have pred := Nat.sub_add_cancel (by omega : 1≤r)
    have next := congrArg (fun t : ℕ => t*(b+N+1)) pred
    have smaller : 3*b*N ⌈/⌉ (b+N+1)≤r-1 := (ceilDiv_le_iff_le_mul (by omega)).mpr
      (by nlinarith only [s₁,fail,next,hp,idn])
    omega
  · intro admissible
    apply count_of_small_slack (by omega) s₁
    nlinarith only [admissible,idn,hp]

/-- At the two adjacent sizes, the mixed interval test reduces respectively
to an automatic inequality and a condition on b modulo h. -/
theorem precise_mixed_capacity (h b : ℕ) (hh : 3≤h) (lower : h^2≤b) :
    let r := 2*b-h
    let N := 2*b-3*h+1
    r+1≤(r-N+2)*(b/h) ∧ (r+1≤(r-(N+1)+2)*(b/h) ↔ 2*(b%h)<h) := by
  intro r N
  have width := (precise_mixed_counts h b hh lower).2.1
  have d : h≤b/h := (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa only [sq] using lower)
  have s := Nat.mod_lt b (by omega : 0<h)
  have euclid := Nat.div_add_mod b h
  have idn : N+3*h=2*b+1 := by dsimp [N]; omega
  have idr : r+h=2*b := Nat.sub_add_cancel (by omega)
  have enough : N+1≤r := by omega
  have q₁ : r-N+2=2*h+1 := by have := Nat.sub_add_cancel (by omega : N≤r); omega
  have q₂ : r-(N+1)+2=2*h := by have := Nat.sub_add_cancel enough; omega
  rw [q₁,q₂]
  have lim : b%h+1≤h := by omega
  constructor
  · nlinarith only [euclid,idr,d,lim]
  · constructor <;> intro edge <;> nlinarith only [euclid,idr,edge]

/-- For every h≥3, all middle widths in which the stated rank is the
dimension prediction have complex generic rank 2b−h at this third size. -/
theorem all_widths_generic_rank_sharp (h b : ℕ) (hh : 3≤h)
    (admissible : 3*h^2+h≤2*b+1) :
    Arxiv.«0805.3777».IsGenericRank [3,b,2*b-3*h+1] (2*b-h) := by
  have lower : h^2≤b := by nlinarith only [admissible,hh,Nat.zero_le (h^2)]
  obtain ⟨hb,width,ordered,enough,count,_⟩ := precise_mixed_counts h b hh lower
  have level := Nat.sub_add_cancel (by omega : h≤2*b)
  exact rank_of_remainder_capacity b (2*b-3*h+1) (2*b-h) h (by omega) hb width
    ordered (by omega) level (precise_mixed_capacity h b hh lower).1 (count.mpr admissible)

/-- At the next third size, b≥h² and the lower half of the residue classes
give the same complex generic rank. -/
theorem small_remainder_generic_rank_sharp (h b : ℕ) (hh : 3≤h) (lower : h^2≤b)
    (rem : 2*(b%h)<h) :
    Arxiv.«0805.3777».IsGenericRank [3,b,2*b-3*h+2] (2*b-h) := by
  obtain ⟨hb,width,ordered,enough,_,count⟩ := precise_mixed_counts h b hh lower
  have level := Nat.sub_add_cancel (by omega : h≤2*b)
  exact rank_of_remainder_capacity b (2*b-3*h+2) (2*b-h) h (by omega) hb width
    (by omega) enough level ((precise_mixed_capacity h b hh lower).2.mpr rem) count

end CriticalThreeQuotient

namespace CriticalHigher.Blocks

open MvPolynomial

/-- The open full-rank conditions for independent coordinate blocks
remain compatible when their dimensions differ. An unassigned point
contributes only its freely chosen last-factor variation. -/
theorem different_common_tangents {A B P G : Type*} {C : G → Type*}
    [Fintype A] [Fintype B] [Fintype P] [Fintype G] [∀ g,Fintype (C g)] [DecidableEq G]
    (label : P → Option G) :
    let D (g : G) (x : P→A→ℂ) (y : P→B→ℂ) (z : P→C g→ℂ) :=
      ∀ T : A→B→C g→ℂ, ∃ u : P→A→ℂ, ∃ v : P→B→ℂ, ∃ w : P→C g→ℂ, ∀ i j k,
        T i j k=∑ t, ((if label t=some g then u t i*(y t j*z t k)+x t i*(v t j*z t k) else 0)
          +x t i*(y t j*w t k))
    (∀ g,∃ x y z,D g x y z) → ∃ x y, ∃ z : ∀ g,P→C g→ℂ, ∀ g,D g x y (z g) := by
  classical
  intro D each
  let V := (P×A) ⊕ (P×B) ⊕ ((g : G) × (P×C g))
  let J (g : G) := P × (A ⊕ B ⊕ C g)
  let M (g : G) : Matrix ((A×B)×C g) (J g) (MvPolynomial V ℂ) := fun row col => col.2.elim
    (fun i => if label col.1=some g ∧ i=row.1.1 then
      X (.inr (.inl (col.1,row.1.2)))*X (.inr (.inr ⟨g,col.1,row.2⟩)) else 0)
    (Sum.elim (fun j => if label col.1=some g ∧ j=row.1.2 then
      X (.inl (col.1,row.1.1))*X (.inr (.inr ⟨g,col.1,row.2⟩)) else 0)
      (fun k => if k=row.2 then X (.inl (col.1,row.1.1))*X (.inr (.inl (col.1,row.1.2))) else 0))
  let x (p : V → ℂ) (t : P) (i : A) := p (.inl (t,i))
  let y (p : V → ℂ) (t : P) (j : B) := p (.inr (.inl (t,j)))
  let z (p : V → ℂ) (g : G) (t : P) (k : C g) := p (.inr (.inr ⟨g,t,k⟩))
  have action (g : G) (p : V→ℂ) (q : J g→ℂ) (i : A) (j : B) (k : C g) :
      ((M g).map (eval p)).mulVec q ((i,j),k)=∑ t,
        ((if label t=some g then q (t,.inl i)*(y p t j*z p g t k)+
           x p t i*(q (t,.inr (.inl j))*z p g t k) else 0)+
           x p t i*(y p t j*q (t,.inr (.inr k)))) := by
    change (∑ s : J g, eval p (M g ((i,j),k) s)*q s)=_
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
    by_cases hit : label t=some g <;> simp [M,hit,x,y,z,apply_ite,ite_mul,Finset.sum_ite_eq'] <;> ring
  have full (g : G) : ∃ p : V→ℂ, Function.Surjective ((M g).map (eval p)).mulVec := by
    obtain ⟨X₀,Y₀,Z₀,good⟩ := each g
    let Zs : ∀ g,P→C g→ℂ := Function.update (fun _ _ _ => 0) g Z₀
    let p : V→ℂ := Sum.elim (fun t => X₀ t.1 t.2)
      (Sum.elim (fun t => Y₀ t.1 t.2) (fun t => Zs t.1 t.2.1 t.2.2))
    have back (t : P) (k : C g) : z p g t k=Z₀ t k := by simp [z,p,Zs]
    refine ⟨p,?_⟩
    intro T
    obtain ⟨u,v,w,repr⟩ := good fun i j k => T ((i,j),k)
    let q : J g→ℂ := fun s => s.2.elim (u s.1) (Sum.elim (v s.1) (w s.1))
    refine ⟨q,?_⟩
    funext ⟨⟨i,j⟩,k⟩
    rw [action]
    simpa only [back,q,x,y,p,Sum.elim_inl,Sum.elim_inr] using (repr i j k).symm
  obtain ⟨p,onto⟩ := common_surjective M full
  refine ⟨x p,y p,z p,?_⟩
  intro g T
  obtain ⟨q,hq⟩ := onto g fun row => T row.1.1 row.1.2 row.2
  exact ⟨fun t i => q (t,.inl i),fun t j => q (t,.inr (.inl j)),fun t k => q (t,.inr (.inr k)),
    fun i j k => (congrFun hq ((i,j),k)).symm.trans (action g p q i j k)⟩

/-- Spanning in each coordinate block gives a spanning tangent in the full
tensor. Both the block widths and the numbers of assigned points may vary. -/
theorem spans_of_different_blocks {A B P G : Type*} {C : G→Type*} [Fintype A] [Fintype B]
    [Fintype P] [Fintype G] [∀ g,Fintype (C g)] [DecidableEq G] (label : P→Option G)
    (one : ∀ g, ∃ x : P→A→ℂ, ∃ y : P→B→ℂ, ∃ z : P→C g→ℂ,
      ∀ T : A→B→C g→ℂ, ∃ u : P→A→ℂ, ∃ v : P→B→ℂ, ∃ w : P→C g→ℂ, ∀ i j k,
        T i j k=∑ t,((if label t=some g then u t i*(y t j*z t k)+x t i*(v t j*z t k) else 0)+
          x t i*(y t j*w t k))) :
    ∃ x : P→A→ℂ, ∃ y : P→B→ℂ, ∃ Z : P→((g : G) × C g)→ℂ,
      ∀ T : A→B→((g : G) × C g)→ℂ, ∃ u : P→A→ℂ, ∃ v : P→B→ℂ,
        ∃ w : P→((g : G) × C g)→ℂ, ∀ i j k,
          T i j k=∑ t,(u t i*(y t j*Z t k)+x t i*(v t j*Z t k)+x t i*(y t j*w t k)) := by
  classical
  obtain ⟨x,y,z,good⟩ := different_common_tangents label one
  let Z (t : P) (p : (g : G) × C g) := if label t=some p.1 then z p.1 t p.2 else 0
  refine ⟨x,y,Z,?_⟩
  intro T
  choose U V W repr using fun g => good g fun i j k => T i j ⟨g,k⟩
  refine ⟨fun t => (label t).elim 0 (fun g => U g t),fun t => (label t).elim 0 (fun g => V g t),
    fun t k => W k.1 t k.2,?_⟩
  rintro i j ⟨g,k⟩
  apply (repr g i j k).trans
  apply Finset.sum_congr rfl
  intro t _
  by_cases hit : label t=some g <;> simp [Z,hit]

end CriticalHigher.Blocks

namespace CriticalHigher.Blocks

/-- Enumerate the complement of any fixed embedded family of m marks.
Under the equivalence each initial mark keeps its specified image. -/
private theorem block_complement_fin {P : Type*} [Fintype P] (m r : ℕ)
    (points : Fintype.card P=r) (f : Fin m → P) (inj : Function.Injective f) :
    ∃ e : (Fin m ⊕ Fin (r-m)) ≃ P, ∀ j, e (.inl j)=f j := by
  classical
  let first := Equiv.ofInjective f inj
  have count : Fintype.card {p : P // p∈Set.range f}=m := by
    rw [← Fintype.card_congr first,Fintype.card_fin]
  let last : {p : P // p∉Set.range f} ≃ Fin (r-m) := Fintype.equivFinOfCardEq (by
    rw [Fintype.card_subtype_compl,count,points])
  exact ⟨(Equiv.sumCongr first last.symm).trans (Equiv.sumCompl (fun p => p ∈ Set.range f)),fun _ => rfl⟩

/-- Dissimilar blocks can be assembled using independent local tests, each
with its prescribed full marks and all remaining points as external products. -/
theorem different_block_tangent (a b g r : ℕ) (width mark : Fin g → ℕ)
    (slots : (∑ q, mark q) ≤ r)
    (each : ∀ q : Fin g,
      ∃ x : Fin (mark q) → Fin a → ℂ, ∃ y : Fin (mark q) → Fin b → ℂ, ∃ z : Fin (mark q) → Fin (width q) → ℂ,
      ∃ x' : Fin (r-mark q) → Fin a → ℂ, ∃ y' : Fin (r-mark q) → Fin b → ℂ,
      ∀ T : Fin a → Fin b → Fin (width q) → ℂ, ∃ u : Fin (mark q) → Fin a → ℂ, ∃ v : Fin (mark q) → Fin b → ℂ,
      ∃ w : Fin (mark q) → Fin (width q) → ℂ, ∃ w' : Fin (r-mark q) → Fin (width q) → ℂ, ∀ i j k,
        T i j k=(∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) +
          ∑ t, x' t i*(y' t j*w' t k)) :
    ∃ X : Fin r → Fin a → ℂ, ∃ Y : Fin r → Fin b → ℂ, ∃ Z : Fin r → Fin (∑ q, width q) → ℂ,
      ∀ T : Fin a → Fin b → Fin (∑ q, width q) → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
      ∃ w : Fin r → Fin (∑ q, width q) → ℂ, ∀ i j k,
        T i j k=∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k)) := by
  classical
  let P := (Σ q : Fin g, Fin (mark q)) ⊕ Fin (r-∑ q,mark q)
  let label : P → Option (Fin g) := Sum.elim (fun p => some p.1) (fun _ => none)
  have size : Fintype.card P=r := by
    simp only [P,Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin]
    omega
  have localPoint (q : Fin g) :
      ∃ X : P → Fin a → ℂ, ∃ Y : P → Fin b → ℂ, ∃ Z : P → Fin (width q) → ℂ,
      ∀ T : Fin a → Fin b → Fin (width q) → ℂ, ∃ u : P → Fin a → ℂ, ∃ v : P → Fin b → ℂ,
      ∃ w : P → Fin (width q) → ℂ, ∀ i j k,
        T i j k=∑ t, ((if label t=some q then u t i*(Y t j*Z t k)+X t i*(v t j*Z t k) else 0) +
          X t i*(Y t j*w t k)) := by
    let f : Fin (mark q) → P := fun j => .inl ⟨q,j⟩
    have inject : Function.Injective f := by
      intro u v eq
      have pair : (⟨q,u⟩ : Σ i : Fin g, Fin (mark i)) = ⟨q,v⟩ := Sum.inl.inj eq
      exact eq_of_heq (Sigma.mk.inj_iff.mp pair).2
    obtain ⟨e,marked⟩ := block_complement_fin (mark q) r size f inject
    apply restricted_tangent_of_split (fun s => label s=some q) e _ (each q)
    intro j
    rw [marked]
    rfl
  obtain ⟨x,y,z,hit⟩ := spans_of_different_blocks (C:=fun q => Fin (width q)) label localPoint
  let points : P ≃ Fin r := Fintype.equivFinOfCardEq size
  let coords : (Σ q : Fin g, Fin (width q)) ≃ Fin (∑ q,width q) :=
    Fintype.equivFinOfCardEq (by simp)
  refine ⟨fun t => x (points.symm t),fun t => y (points.symm t),
    fun t k => z (points.symm t) (coords.symm k),?_⟩
  intro T
  obtain ⟨u,v,w,cover⟩ := hit fun i j k => T i j (coords k)
  refine ⟨fun t => u (points.symm t),fun t => v (points.symm t),
    fun t k => w (points.symm t) (coords.symm k),?_⟩
  intro i j k
  have eq := cover i j (coords.symm k)
  simp only [Equiv.apply_symm_apply] at eq
  rw [eq,←points.sum_comp]
  simp only [Equiv.symm_apply_apply]

end CriticalHigher.Blocks

namespace CriticalThreeQuotient

/-- Enumerate exactly the samples outside the chosen marks. -/
private lemma exterior_embedding {A M : Type*} [Fintype A] [Fintype M] (e : M ↪ A) :
    ∃ f : Fin (Fintype.card A-Fintype.card M) ↪ A, Set.range f = (Set.range e)ᶜ := by
  classical
  let C := {s : A // s ∉ Set.range e}
  let g : C ≃ Fin (Fintype.card A-Fintype.card M) := Fintype.equivFinOfCardEq (by
    change Fintype.card {s : A // s ∉ Set.range e} = _
    rw [Fintype.card_subtype_compl,← Fintype.card_congr e.toEquivRange])
  let f := g.symm.toEmbedding.trans (Function.Embedding.subtype (fun s : A => s ∉ Set.range e))
  refine ⟨f, Set.ext fun s => ⟨?_,?_⟩⟩
  · rintro ⟨p,rfl⟩
    exact (g.symm p).property
  · intro hs
    refine ⟨g ⟨s,hs⟩,?_⟩
    change (g.symm (g ⟨s,hs⟩)).val = s
    rw [Equiv.symm_apply_apply]

/-- Contract the physical normal against the marked third factors. All
samples impose product equations, while only marks impose the two arm
equations. Every relation of the third factors couples the contracted forms. -/
lemma augmented_of_contracted {K I J A M N G : Type*} [Field K]
    [Fintype I] [Fintype J] [Fintype A] [Fintype M] [Fintype N]
    (e : M ↪ A) (x : A → I → K) (y : A → J → K) (Z : Matrix M N K)
    (Q : Matrix G M K) (qZ : Q*Z=0)
    (detect : ∀ (H : I → J → N → K) (F : M → I×J → K),
      (∀ t i j, F t (i,j) = ∑ k, Z t k*H i j k) →
      (∀ t s, (∑ ij, (x s ij.1*y s ij.2)*F t ij)=0) →
      (∀ t i, (∑ j, y (e t) j*F t (i,j))=0) →
      (∀ t j, (∑ i, x (e t) i*F t (i,j))=0) →
      (∀ q, (∑ t, Q q t • F t)=0) → H=0) :
    ∃ f : Fin (Fintype.card A-Fintype.card M) ↪ A, Set.range f = (Set.range e)ᶜ ∧
      ∀ T : I → J → N → K,
      ∃ u : M → I → K, ∃ v : M → J → K, ∃ w : M → N → K,
      ∃ w' : Fin (Fintype.card A-Fintype.card M) → N → K, ∀ i j k,
        T i j k = (∑ t, (u t i*(y (e t) j*Z t k)+x (e t) i*(v t j*Z t k)+x (e t) i*(y (e t) j*w t k))) +
          ∑ t, x (f t) i*(y (f t) j*w' t k) := by
  classical
  obtain ⟨f,hf⟩ := exterior_embedding e
  refine ⟨f,hf,HigherPencil.augmented_span_of_annihilator (fun t => x (e t)) (fun t => y (e t))
    Z (fun p => x (f p)) (fun p => y (f p)) ?_⟩
  intro H xarm yarm marked exterior
  let F (t : M) (ij : I×J) := ∑ k, Z t k*H ij.1 ij.2 k
  have allprod (s : A) (k : N) : (∑ ij : I×J, (x s ij.1*y s ij.2)*H ij.1 ij.2 k)=0 := by
    rw [Fintype.sum_prod_type]
    by_cases hs : s ∈ Set.range e
    · obtain ⟨t,rfl⟩ := hs
      exact marked t k
    · have hm : s ∈ Set.range f := by rw [hf]; exact hs
      obtain ⟨p,rfl⟩ := hm
      exact exterior p k
  refine detect H F (fun _ _ _ => rfl) ?_ ?_ ?_ ?_
  · intro t s
    calc
      _ = ∑ k, Z t k*(∑ ij : I×J, (x s ij.1*y s ij.2)*H ij.1 ij.2 k) := by
        simp only [F,Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro ij _
        ring
      _ = 0 := by simp [allprod]
  · intro t i
    simpa only [F,Finset.mul_sum,mul_assoc] using xarm t i
  · intro t j
    simpa only [F,Finset.mul_sum,mul_assoc] using yarm t j
  · intro q
    funext ij
    have zero (k : N) : (∑ t, Q q t*Z t k)=0 := congrFun (congrFun qZ q) k
    change (∑ t, Q q t • F t) ij = 0
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    calc
      _ = ∑ k, (∑ t, Q q t*Z t k)*H ij.1 ij.2 k := by
        simp only [F,Finset.mul_sum,Finset.sum_mul,mul_assoc]
        rw [Finset.sum_comm]
      _ = 0 := by simp [zero]

/-- Coupled normal forms certify an augmented tangent for an arbitrary
embedding of the marks into the full sample set. -/
lemma augmented_of_normal_relations {K I J A M N G : Type*} [Field K]
    [Fintype I] [Fintype J] [Fintype A] [Fintype M] [Fintype N]
    (e : M ↪ A) (x : A → I → K) (y : A → J → K) (Z : Matrix M N K)
    (Q : Matrix G M K) (qZ : Q*Z=0) (frame : Function.Injective Z.mulVec)
    (detect : ∀ F : M → I×J → K,
      (∀ t s, (∑ ij, (x s ij.1*y s ij.2)*F t ij)=0) →
      (∀ t i, (∑ j, y (e t) j*F t (i,j))=0) →
      (∀ t j, (∑ i, x (e t) i*F t (i,j))=0) →
      (∀ q, (∑ t, Q q t • F t)=0) → F=0) :
    ∃ f : Fin (Fintype.card A-Fintype.card M) ↪ A, ∀ T : I → J → N → K,
      ∃ u : M → I → K, ∃ v : M → J → K, ∃ w : M → N → K,
      ∃ w' : Fin (Fintype.card A-Fintype.card M) → N → K, ∀ i j k,
        T i j k = (∑ t, (u t i*(y (e t) j*Z t k)+x (e t) i*(v t j*Z t k)+x (e t) i*(y (e t) j*w t k))) +
          ∑ t, x (f t) i*(y (f t) j*w' t k) := by
  obtain ⟨f,_,span⟩ := augmented_of_contracted e x y Z Q qZ (by
    intro H F value outer row col coupled
    have zero := detect F outer row col coupled
    funext i j k
    apply congrFun (frame (a₁:=H i j) (a₂:=0) ?_) k
    rw [Matrix.mulVec_zero]
    funext t
    exact (value t i j).symm.trans (congrFun (congrFun zero t) (i,j)))
  exact ⟨f,span⟩

end CriticalThreeQuotient

namespace CriticalThreeQuotient

/-- Select independent columns in the kernel with arbitrary finite row and column
labels. The selected columns have an explicit matrix left inverse. -/
lemma kernel_frame_finite {K M N G : Type*} [Field K] [Fintype M] [Fintype N] [Fintype G]
    [DecidableEq N] (Q : Matrix G M K)
    (room : Fintype.card N ≤ Fintype.card M-Fintype.card G) :
    ∃ Z : Matrix M N K, ∃ L : Matrix N M K, Q*Z=0 ∧ L*Z=1 := by
  classical
  let F := Q.mulVecLin
  have dims : Module.finrank K F.range+Module.finrank K F.ker=Fintype.card M := by
    simpa only [Module.finrank_fintype_fun_eq_card] using F.finrank_range_add_finrank_ker
  have height : Module.finrank K F.range ≤ Fintype.card G := by
    simpa only [Module.finrank_fintype_fun_eq_card] using F.range.finrank_le
  have fit : Module.finrank K (N → K) ≤ Module.finrank K F.ker := by
    rw [Module.finrank_fintype_fun_eq_card]
    omega
  obtain ⟨g,hg⟩ := finrank_le_iff_exists_linearMap.mp fit
  let f := F.ker.subtype.comp g
  have injective : Function.Injective f := Subtype.val_injective.comp hg
  obtain ⟨L,hL⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr injective)
  refine ⟨LinearMap.toMatrix' f,LinearMap.toMatrix' L,?_,?_⟩
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul,Matrix.toLin'_toMatrix',map_zero]
    change F.comp f = 0
    apply LinearMap.ext
    intro v
    exact (g v).property
  · rw [← LinearMap.toMatrix'_comp,hL,LinearMap.toMatrix'_id]

/-- A coupling matrix on the marked labels supplies the third-mode frame
and an augmented spanning witness of width `card M - u`. -/
lemma augmented_of_relation_matrix {K I J A M : Type*} [Field K]
    [Fintype I] [Fintype J] [Fintype A] [Fintype M] {u : ℕ}
    (e : M ↪ A) (x : A → I → K) (y : A → J → K) (Q : Matrix (Fin u) M K)
    (detect : ∀ F : M → I×J → K,
      (∀ t s, (∑ ij, (x s ij.1*y s ij.2)*F t ij)=0) →
      (∀ t i, (∑ j, y (e t) j*F t (i,j))=0) →
      (∀ t j, (∑ i, x (e t) i*F t (i,j))=0) →
      (∀ q, (∑ t, Q q t • F t)=0) → F=0) :
    let N := Fin (Fintype.card M-u)
    ∃ Z : Matrix M N K, ∃ f : Fin (Fintype.card A-Fintype.card M) ↪ A, ∀ T : I → J → N → K,
      ∃ U : M → I → K, ∃ V : M → J → K, ∃ W : M → N → K,
      ∃ W' : Fin (Fintype.card A-Fintype.card M) → N → K, ∀ i j k,
        T i j k = (∑ t, (U t i*(y (e t) j*Z t k)+x (e t) i*(V t j*Z t k)+x (e t) i*(y (e t) j*W t k))) +
          ∑ t, x (f t) i*(y (f t) j*W' t k) := by
  classical
  intro N
  obtain ⟨Z,L,qZ,left⟩ := kernel_frame_finite (N:=N) Q (by simp [N])
  refine ⟨Z,augmented_of_normal_relations e x y Z Q qZ ?_ detect⟩
  have recover (v : N→K) : L.mulVec (Z.mulVec v) = v := by
    rw [Matrix.mulVec_mulVec,left,Matrix.one_mulVec]
  intro s t h
  exact (recover s).symm.trans ((congrArg L.mulVec h).trans (recover t))

end CriticalThreeQuotient

namespace CriticalThreeQuotient

/-- Each off-diagonal entry of the three sampled matrices is governed by one
scalar. Marking only some samples leaves the row and column index types distinct. -/
private lemma rectangular_sample_zero {K A M U V : Type*} [Field K] [Fintype A] [Fintype M]
    (e : M ↪ A) (l d : A → K) (distinct : Function.Injective l)
    (P : Matrix U A K) (Q : Matrix V M K)
    (exactPair : ∀ E : A → M → K,
      (∀ u t, (∑ s, P u s*((l s-l (e t))*E s t))=0) →
      (∀ u t, (∑ s, P u s*((d s-d (e t))*E s t))=0) →
      (∀ v s, (∑ t, ((l s-l (e t))*E s t)*Q v t)=0) →
      (∀ v s, (∑ t, ((d s-d (e t))*E s t)*Q v t)=0) →
      ∀ s t, s≠e t → E s t=0)
    (X B C : Matrix A M K)
    (diag : ∀ t, X (e t) t=0 ∧ B (e t) t=0 ∧ C (e t) t=0)
    (row : ∀ s t, X s t+l s*B s t+d s*C s t=0)
    (col : ∀ s t, X s t+l (e t)*B s t+d (e t)*C s t=0)
    (leftB : P*B=0) (leftC : P*C=0) (rightB : B*Q.transpose=0) (rightC : C*Q.transpose=0) :
    ∀ s t, X s t=0 ∧ B s t=0 ∧ C s t=0 := by
  let E (s : A) (t : M) := C s t/(l s-l (e t))
  have entries (s : A) (t : M) :
      C s t=(l s-l (e t))*E s t ∧ (d s-d (e t))*E s t= -B s t := by
    by_cases eq : s=e t
    · subst s
      simp [diag t]
    · have gap : l s-l (e t)≠0 := sub_ne_zero.mpr (distinct.ne eq)
      have hC : C s t=(l s-l (e t))*E s t := by dsimp only [E]; field_simp
      refine ⟨hC,?_⟩
      apply mul_left_cancel₀ gap
      linear_combination (row s t)-(col s t)-(d s-d (e t))*hC
  have left (N : Matrix A M K) (h : P*N=0) (u : U) (t : M) : (∑ s, P u s*N s t)=0 :=
    congrFun (congrFun h u) t
  have right (N : Matrix A M K) (h : N*Q.transpose=0) (v : V) (s : A) : (∑ t, N s t*Q v t)=0 :=
    congrFun (congrFun h s) v
  have eC (s : A) (t : M) := (entries s t).1
  have eB (s : A) (t : M) := (entries s t).2
  have zero := exactPair E
    (fun u t => by simpa only [← eC] using left C leftC u t)
    (fun u t => by simp only [eB,mul_neg,Finset.sum_neg_distrib,left B leftB,neg_zero])
    (fun v s => by simpa only [← eC] using right C rightC v s)
    (fun v s => by simp only [eB,neg_mul,Finset.sum_neg_distrib,right B rightB,neg_zero])
  intro s t
  by_cases eq : s=e t
  · subst s
    exact diag t
  · have zz := entries s t
    rw [zero s t eq,mul_zero,mul_zero] at zz
    have bzero : B s t=0 := by linear_combination zz.2
    exact ⟨by simpa only [bzero,zz.1,mul_zero,add_zero] using row s t,bzero,zz.1⟩

/-- Rectangular commutator certificates suffice for augmented three-slice
tangents. The full sample set and the set of marks have independent index types. -/
lemma rectangular_tangent_of_samples {K A M B N U V : Type*} [Field K]
    [Fintype A] [Fintype M] [Fintype B] [Fintype N]
    (e : M ↪ A) (l d : A → K) (distinct : Function.Injective l)
    (Y : Matrix A B K) (Z : Matrix M N K) (P : Matrix U A K) (Q : Matrix V M K)
    (pY : P*Y=0) (qZ : Q*Z=0) (embed : Function.Injective (fun H : Matrix B N K => Y*H*Z.transpose))
    (exactPair : ∀ E : A → M → K,
      (∀ u t, (∑ s, P u s*((l s-l (e t))*E s t))=0) →
      (∀ u t, (∑ s, P u s*((d s-d (e t))*E s t))=0) →
      (∀ v s, (∑ t, ((l s-l (e t))*E s t)*Q v t)=0) →
      (∀ v s, (∑ t, ((d s-d (e t))*E s t)*Q v t)=0) →
      ∀ s t, s≠e t → E s t=0) :
    let x (s : A) : Fin 3 → K := ![1,l s,d s]
    ∃ f : Fin (Fintype.card A-Fintype.card M) ↪ A, Set.range f = (Set.range e)ᶜ ∧
      ∀ T : Fin 3 → B → N → K,
      ∃ u : M → Fin 3 → K, ∃ v : M → B → K, ∃ w : M → N → K,
      ∃ w' : Fin (Fintype.card A-Fintype.card M) → N → K, ∀ i j k,
        T i j k = (∑ t, (u t i*(Y (e t) j*Z t k)+x (e t) i*(v t j*Z t k)+x (e t) i*(Y (e t) j*w t k))) +
          ∑ t, x (f t) i*(Y (f t) j*w' t k) := by
  classical
  intro x
  apply augmented_of_contracted e x Y Z Q qZ
  intro H F value outer row col coupled
  let D (i : Fin 3) : Matrix B N K := H i
  let R (i : Fin 3) : Matrix B M K := fun j t => F t (i,j)
  let S (i : Fin 3) := Y*R i
  have repr (i : Fin 3) : R i=D i*Z.transpose := by
    ext j t
    change F t (i,j) = ∑ k, H i j k * Z t k
    simpa only [mul_comm] using value t i j
  have entry (i : Fin 3) (s : A) (t : M) : S i s t=∑ j, Y s j*F t (i,j) := rfl
  have sample (s : A) (t : M) : (∑ i, x s i*S i s t)=0 := by
    have h := outer t s
    rw [Fintype.sum_prod_type] at h
    simpa only [entry,Finset.mul_sum,mul_assoc] using h
  have mark (s : A) (t : M) : (∑ i, x (e t) i*S i s t)=0 := by
    simp only [entry,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    calc
      _ = Y s j*(∑ i, x (e t) i*F t (i,j)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [col,mul_zero]
  have left (i : Fin 3) : P*S i=0 := by simp [S,← Matrix.mul_assoc,pY]
  have right (i : Fin 3) : S i*Q.transpose=0 := by
    have h : R i*Q.transpose=0 := by
      ext j q
      change (∑ t, F t (i,j)*Q q t)=0
      simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,mul_comm] using
        congrFun (coupled q) (i,j)
    simp only [S,Matrix.mul_assoc,h,Matrix.mul_zero]
  have vanish := rectangular_sample_zero e l d distinct P Q exactPair (S 0) (S 1) (S 2)
    (fun t => ⟨row t 0,row t 1,row t 2⟩)
    (fun s t => by simpa [x,Fin.sum_univ_succ,add_assoc] using sample s t)
    (fun s t => by simpa [x,Fin.sum_univ_succ,add_assoc] using mark s t)
    (left 1) (left 2) (right 1) (right 2)
  have allZero (i : Fin 3) : D i=0 := by
    have z : S i=0 := by
      ext s t
      fin_cases i
      · exact (vanish s t).1
      · exact (vanish s t).2.1
      · exact (vanish s t).2.2
    apply embed
    change Y*D i*Z.transpose=Y*0*Z.transpose
    simpa only [Matrix.mul_zero,Matrix.zero_mul,S,repr,Matrix.mul_assoc] using z
  funext i j k
  exact congrFun (congrFun (allZero i) j) k

/-- Numeric form with `m` ordinary points and `r-m` exterior samples. -/
lemma rectangular_tangent_of_commutators {K U V : Type*} [Field K] {b n r m : ℕ}
    (e : (Fin m) ↪ (Fin r)) (l d : (Fin r) → K) (distinct : Function.Injective l)
    (Y : Matrix (Fin r) (Fin b) K) (Z : Matrix (Fin m) (Fin n) K) (P : Matrix U (Fin r) K) (Q : Matrix V (Fin m) K)
    (pY : P*Y=0) (qZ : Q*Z=0) (embed : Function.Injective (fun H : Matrix (Fin b) (Fin n) K => Y*H*Z.transpose))
    (exactPair : ∀ E : (Fin r) → (Fin m) → K,
      (∀ u t, (∑ s, P u s*((l s-l (e t))*E s t))=0) →
      (∀ u t, (∑ s, P u s*((d s-d (e t))*E s t))=0) →
      (∀ v s, (∑ t, ((l s-l (e t))*E s t)*Q v t)=0) →
      (∀ v s, (∑ t, ((d s-d (e t))*E s t)*Q v t)=0) →
      ∀ s t, s≠e t → E s t=0) :
    let x (s : (Fin r)) : Fin 3 → K := ![1,l s,d s]
    ∃ f : Fin (r-m) ↪ (Fin r), ∀ T : Fin 3 → (Fin b) → (Fin n) → K,
      ∃ u : (Fin m) → Fin 3 → K, ∃ v : (Fin m) → (Fin b) → K, ∃ w : (Fin m) → (Fin n) → K,
      ∃ w' : Fin (r-m) → (Fin n) → K, ∀ i j k,
        T i j k = (∑ t, (u t i*(Y (e t) j*Z t k)+x (e t) i*(v t j*Z t k)+x (e t) i*(Y (e t) j*w t k))) +
          ∑ t, x (f t) i*(Y (f t) j*w' t k) := by
  have h := rectangular_tangent_of_samples e l d distinct Y Z P Q pY qZ embed exactPair
  dsimp only at h
  rw [Fintype.card_fin,Fintype.card_fin] at h
  obtain ⟨f,_,span⟩ := h
  exact ⟨f,span⟩

end CriticalThreeQuotient

namespace CriticalThreeQuotient

/-- Choose both rectangular frames from the two relation matrices. The
bounds are on the number of relation rows, with no independence assumption. -/
lemma rectangular_tangent_of_kernel_samples {K A M B N U V : Type*} [Field K]
    [Fintype A] [Fintype M] [Fintype B] [Fintype N] [Fintype U] [Fintype V]
    (hb : Fintype.card B ≤ Fintype.card A-Fintype.card U)
    (hn : Fintype.card N ≤ Fintype.card M-Fintype.card V)
    (e : M ↪ A) (l d : A → K) (distinct : Function.Injective l) (P : Matrix U A K) (Q : Matrix V M K)
    (exactPair : ∀ E : A → M → K,
      (∀ u t, (∑ s, P u s*((l s-l (e t))*E s t))=0) →
      (∀ u t, (∑ s, P u s*((d s-d (e t))*E s t))=0) →
      (∀ v s, (∑ t, ((l s-l (e t))*E s t)*Q v t)=0) →
      (∀ v s, (∑ t, ((d s-d (e t))*E s t)*Q v t)=0) →
      ∀ s t, s≠e t → E s t=0) :
    let x (s : A) : Fin 3 → K := ![1,l s,d s]
    ∃ Y : Matrix A B K, ∃ Z : Matrix M N K, ∃ f : Fin (Fintype.card A-Fintype.card M) ↪ A, ∀ T : Fin 3 → B → N → K,
      ∃ u : M → Fin 3 → K, ∃ v : M → B → K, ∃ w : M → N → K,
      ∃ w' : Fin (Fintype.card A-Fintype.card M) → N → K, ∀ i j k,
        T i j k = (∑ t, (u t i*(Y (e t) j*Z t k)+x (e t) i*(v t j*Z t k)+x (e t) i*(Y (e t) j*w t k))) +
          ∑ t, x (f t) i*(Y (f t) j*w' t k) := by
  classical
  intro x
  obtain ⟨Y,L,pY,left⟩ := kernel_frame_finite P hb
  obtain ⟨Z,R,qZ,right⟩ := kernel_frame_finite Q hn
  have recover (H : Matrix B N K) : L*(Y*H*Z.transpose)*R.transpose=H := by
    calc
      _ = (L*Y)*H*(R*Z).transpose := by simp only [Matrix.transpose_mul,Matrix.mul_assoc]
      _ = H := by rw [left,right,Matrix.transpose_one,Matrix.one_mul,Matrix.mul_one]
  have embed : Function.Injective (fun H : Matrix B N K => Y*H*Z.transpose) :=
    fun H J h => (recover H).symm.trans ((congrArg (fun C => L*C*R.transpose) h).trans (recover J))
  obtain ⟨f,_,span⟩ := rectangular_tangent_of_samples e l d distinct Y Z P Q pY qZ embed exactPair
  exact ⟨Y,Z,f,span⟩

/-- A rectangular commutator kernel test gives the local augmented three-slice
tangent with `m` full marks, `r-m` exterior points, and third width `n`. -/
lemma rectangular_tangent_of_kernel_commutators {K : Type*} [Field K] {b n r m : ℕ}
    (hb : b ≤ r) (hn : n ≤ m) (e : Fin m ↪ Fin r) (l d : Fin r → K) (distinct : Function.Injective l)
    (P : Matrix (Fin (r-b)) (Fin r) K) (Q : Matrix (Fin (m-n)) (Fin m) K)
    (exactPair : ∀ E : (Fin r) → (Fin m) → K,
      (∀ u t, (∑ s, P u s*((l s-l (e t))*E s t))=0) →
      (∀ u t, (∑ s, P u s*((d s-d (e t))*E s t))=0) →
      (∀ v s, (∑ t, ((l s-l (e t))*E s t)*Q v t)=0) →
      (∀ v s, (∑ t, ((d s-d (e t))*E s t)*Q v t)=0) →
      ∀ s t, s≠e t → E s t=0) :
    let x (s : (Fin r)) : Fin 3 → K := ![1,l s,d s]
    ∃ Y : Matrix (Fin r) (Fin b) K, ∃ Z : Matrix (Fin m) (Fin n) K, ∃ f : Fin (r-m) ↪ (Fin r), ∀ T : Fin 3 → (Fin b) → (Fin n) → K,
      ∃ u : (Fin m) → Fin 3 → K, ∃ v : (Fin m) → (Fin b) → K, ∃ w : (Fin m) → (Fin n) → K,
      ∃ w' : Fin (r-m) → (Fin n) → K, ∀ i j k,
        T i j k = (∑ t, (u t i*(Y (e t) j*Z t k)+x (e t) i*(v t j*Z t k)+x (e t) i*(Y (e t) j*w t k))) +
          ∑ t, x (f t) i*(Y (f t) j*w' t k) := by
  have hb' : Fintype.card (Fin b) ≤ Fintype.card (Fin r)-Fintype.card (Fin (r-b)) := by simp; omega
  have hn' : Fintype.card (Fin n) ≤ Fintype.card (Fin m)-Fintype.card (Fin (m-n)) := by simp; omega
  have h := rectangular_tangent_of_kernel_samples hb' hn' e l d distinct P Q exactPair
  dsimp only at h
  rw [Fintype.card_fin,Fintype.card_fin] at h
  exact h

end CriticalThreeQuotient

namespace CriticalThreeBatch

/-- Removing one sample and one pole keeps the same quadratic row with
the updated coefficient `a+x+v`. The removed entry of the new vector is zero. -/
private theorem shift_private_vector {K I : Type*} [Field K] [Fintype I]
    (t f : I → K) (a x v : K) (regular : ∀ i, t i+v≠0)
    (mass : (∑ i, f i)=0) (hub : (∑ i, (t i^2+a*t i)*f i)=0)
    (atPole : (∑ i, f i/(t i+v))=0) :
    let d (i : I) := (t i-x)/(t i+v)*f i
    (∑ i, d i)=0 ∧ (∑ i, (t i^2+(a+x+v)*t i)*d i)=0 ∧
      ∀ y : K, y≠v → (∀ i, t i+y≠0) → (∑ i, f i/(t i+y))=0 → (∑ i, d i/(t i+y))=0 := by
  intro d
  have scale (i : I) : (t i+v)*d i=(t i-x)*f i := by
    dsimp only [d]
    field_simp [regular i]
  have first : (∑ i, d i)=0 := by
    calc
      _ = ∑ i, (f i-(x+v)*(f i/(t i+v))) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [d]
        field_simp [regular i]
        ring
      _ = 0 := by rw [Finset.sum_sub_distrib,← Finset.mul_sum,mass,atPole,mul_zero,sub_zero]
  refine ⟨first,?_,?_⟩
  · calc
      _ = ∑ i, ((t i^2+a*t i)*f i-x*(a+x)*f i-v*(a+x)*d i) := by
        apply Finset.sum_congr rfl
        intro i _
        linear_combination (t i+a+x)*scale i
      _ = 0 := by
        rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,hub,mass,first]
        ring
  · intro y different off hit
    have eq : (y-v)*(∑ i, d i/(t i+y))=0 := by
      calc
        _ = ∑ i, ((y+x)*(f i/(t i+y))-(v+x)*(f i/(t i+v))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          dsimp only [d]
          field_simp [regular i,off i]
          ring
        _ = 0 := by rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,hit,atPole,mul_zero,mul_zero,sub_zero]
    exact (mul_eq_zero.mp eq).resolve_left (sub_ne_zero.mpr different)

private theorem private_no_poles {K : Type*} [Field K] {n : ℕ} (t : Fin n → K) (a : K)
    (inj : Function.Injective t) (size : n≤2) (edge : n=2 → a+(∑ i,t i)≠0)
    (f : Fin n → K) (mass : (∑ i, f i)=0) (hub : (∑ i, (t i^2+a*t i)*f i)=0) : f=0 := by
  interval_cases n
  · exact Subsingleton.elim _ _
  · funext i
    fin_cases i
    change f 0=0
    simpa only [Fin.sum_univ_one] using mass
  · rw [Fin.sum_univ_two] at hub mass
    have sumne : a+t 0+t 1≠0 := by simpa only [Fin.sum_univ_two,add_assoc] using edge rfl
    have difference : (t 0-t 1)*(a+t 0+t 1)*f 0=0 := by
      linear_combination hub-(t 1^2+a*t 1)*mass
    have x : f 0=0 := (mul_eq_zero.mp difference).resolve_left
      (mul_ne_zero (sub_ne_zero.mpr (inj.ne (by decide))) sumne)
    have y : f 1=0 := by simpa only [x,zero_add] using mass
    funext i
    fin_cases i
    · exact x
    · exact y

end CriticalThreeBatch

namespace CriticalThreeBatch

private theorem private_spark_fin {K : Type*} [Field K] (g : ℕ) :
    ∀ (n : ℕ) (t : Fin n → K) (w : Fin g → K) (a : K), Function.Injective t → Function.Injective w →
      (∀ i j, t i+w j≠0) → n≤g+2 → (n=g+2 → a+(∑ i,t i)+(∑ j,w j)≠0) → ∀ f : Fin n → K,
      (∑ i,f i)=0 → (∑ i,(t i^2+a*t i)*f i)=0 → (∀ j,(∑ i,f i/(t i+w j))=0) → f=0 := by
  classical
  induction g with
  | zero =>
    intro n t w a ti _ _ size edge f mass hub _
    exact private_no_poles t a ti size (fun h => by simpa using edge h) f mass hub
  | succ g ih =>
    intro n t w a ti wi regular size edge f mass hub poles
    cases n with
    | zero => exact Subsingleton.elim _ _
    | succ n =>
      let x := t (Fin.last n)
      let v := w (Fin.last g)
      let d (i : Fin (n+1)) := (t i-x)/(t i+v)*f i
      have bottom : d (Fin.last n)=0 := by simp [d,x]
      obtain ⟨zm,zh,zp⟩ := shift_private_vector t f a x v (fun i => regular i (Fin.last g)) mass hub (poles (Fin.last g))
      have trim (F : Fin (n+1) → K) (last : F (Fin.last n)=0) (sum : (∑ i,F i)=0) :
          (∑ i : Fin n,F i.castSucc)=0 := by
        rw [Fin.sum_univ_castSucc,last,add_zero] at sum
        exact sum
      have dt : Function.Injective (fun i : Fin n => t i.castSucc) := fun _ _ h =>
        Fin.ext (congrArg (fun u : Fin (n+1) => u.val) (ti h))
      have dw : Function.Injective (fun j : Fin g => w j.castSucc) := fun _ _ h =>
        Fin.ext (congrArg (fun u : Fin (g+1) => u.val) (wi h))
      have newEdge (eq : n=g+2) : a+x+v+(∑ i : Fin n,t i.castSucc)+(∑ j : Fin g,w j.castSucc)≠0 := by
        have e := edge (by omega)
        rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc] at e
        dsimp only [x,v]
        convert e using 1
        ring
      have killed := ih n (fun i => t i.castSucc) (fun j => w j.castSucc) (a+x+v) dt dw
        (fun i j => regular i.castSucc j.castSucc) (by omega) newEdge (fun i => d i.castSucc)
        (trim d bottom zm)
        (trim (fun i => (t i^2+(a+x+v)*t i)*d i) (by rw [bottom,mul_zero]) zh)
        (fun j => trim (fun i => d i/(t i+w j.castSucc)) (by rw [bottom,zero_div])
          (zp (w j.castSucc) (fun eq => Fin.castSucc_ne_last j (wi eq))
            (fun i => regular i j.castSucc) (poles j.castSucc)))
      have head (i : Fin n) : f i.castSucc=0 := by
        have ne : t i.castSucc≠x := fun eq => Fin.castSucc_ne_last i (ti eq)
        have eq : (t i.castSucc-x)/(t i.castSucc+v)*f i.castSucc=0 := congrFun killed i
        exact (mul_eq_zero.mp eq).resolve_left (div_ne_zero (sub_ne_zero.mpr ne) (regular i.castSucc (Fin.last g)))
      have last : f (Fin.last n)=0 := by
        rw [Fin.sum_univ_castSucc] at mass
        simpa only [head,Finset.sum_const_zero,zero_add] using mass
      funext i
      exact Fin.lastCases last head i

/-- The constant row, the quadratic hub row and the reciprocal pole rows
detect every coefficient vector through two samples beyond the pole count.
Only at that last size is the indicated scalar condition needed. -/
theorem private_full_spark {K I J : Type*} [Field K] [Fintype I] [Fintype J]
    (t : I → K) (w : J → K) (a : K) (tinj : Function.Injective t) (winj : Function.Injective w)
    (regular : ∀ i j, t i+w j≠0) (size : Fintype.card I≤Fintype.card J+2)
    (edge : Fintype.card I=Fintype.card J+2 → a+(∑ i,t i)+(∑ j,w j)≠0) (f : I → K)
    (mass : (∑ i,f i)=0) (hub : (∑ i,(t i^2+a*t i)*f i)=0)
    (poles : ∀ j,(∑ i,f i/(t i+w j))=0) : f=0 := by
  classical
  let E := (Fintype.equivFin I).symm
  let D := (Fintype.equivFin J).symm
  have result := private_spark_fin (Fintype.card J) (Fintype.card I) (fun i => t (E i)) (fun j => w (D j)) a
    (tinj.comp E.injective) (winj.comp D.injective) (fun i j => regular (E i) (D j)) size
    (fun h => by rw [E.sum_comp,D.sum_comp]; exact edge h) (fun i => f (E i))
    ((E.sum_comp f).trans mass) ((E.sum_comp (fun i => (t i^2+a*t i)*f i)).trans hub)
    (fun j => (E.sum_comp (fun i => f i/(t i+w (D j)))).trans (poles (D j)))
  funext i
  change f i=0
  simpa only [Equiv.apply_symm_apply,Pi.zero_apply] using congrFun result (E.symm i)

/-- Positive real nodes, positive poles and a positive hub parameter
automatically satisfy both nonvanishing conditions over the complex field. -/
theorem private_full_spark_positive {I J : Type*} [Fintype I] [Fintype J]
    (t : I → ℝ) (w : J → ℝ) (a : ℝ) (tinj : Function.Injective t) (winj : Function.Injective w)
    (posT : ∀ i,0<t i) (posW : ∀ j,0<w j) (posA : 0<a)
    (size : Fintype.card I≤Fintype.card J+2) (f : I → ℂ) (mass : (∑ i,f i)=0)
    (hub : (∑ i,((t i : ℂ)^2+(a : ℂ)*(t i : ℂ))*f i)=0)
    (poles : ∀ j,(∑ i,f i/((t i : ℂ)+(w j : ℂ)))=0) : f=0 := by
  apply private_full_spark (fun i => (t i : ℂ)) (fun j => (w j : ℂ)) (a : ℂ)
    (Complex.ofReal_injective.comp tinj) (Complex.ofReal_injective.comp winj) _ size _ f mass hub poles
  · intro i j
    exact_mod_cast (ne_of_gt (add_pos (posT i) (posW j)))
  · intro _
    have h : 0<a+(∑ i,t i)+(∑ j,w j) := add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg posA (Finset.sum_nonneg fun i _ => (posT i).le))
      (Finset.sum_nonneg fun j _ => (posW j).le)
    exact_mod_cast (ne_of_gt h)

end CriticalThreeBatch

namespace CriticalThreeBatch

/-- For one hub, distribute its outside marks among u color classes. Each
class has capacity ≤k and its own weighted test recovers its coefficients. -/
theorem one_right_coloring {I M S : Type*} [Fintype M] [DecidableEq I]
    (label : M → I) (i : I) (u k : ℕ) (features : S → M → ℂ)
    (room : Fintype.card {m : M // label m≠i} ≤ u*k)
    (spark : ∀ T : Finset M,(∀ m∈T,label m≠i) → T.card≤k →
      ∀ f : T → ℂ,(∀ z,∑ m : T, features z m.val*f m=0) → f=0) :
    ∃ Q : Matrix (Fin u) M ℂ, ∀ f : M→ℂ,(∀ m,label m=i → f m=0) →
      (∀ q z,∑ m,Q q m*(features z m*f m)=0) → f=0 := by
  classical
  let O := {m : M // label m≠i}
  obtain ⟨slot⟩ : Nonempty (O ↪ Fin u × Fin k) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_prod,Fintype.card_fin] using room)
  let color (m : M) : Option (Fin u) := if h : label m≠i then some (slot ⟨m,h⟩).1 else none
  let cluster (q : Fin u) := Finset.univ.filter (fun m : M => color m=some q)
  let Q : Matrix (Fin u) M ℂ := fun q m => if color m=some q then 1 else 0
  have outside (q : Fin u) (m : M) (hm : m∈cluster q) : label m≠i := by
    have h := (Finset.mem_filter.mp hm).2
    intro eq
    simp only [color,dif_neg (not_not.mpr eq),reduceCtorEq] at h
  have size (q : Fin u) : (cluster q).card≤k := by
    let idx (m : cluster q) : O := ⟨m.val,outside q m.val m.property⟩
    have lab (m : cluster q) : (slot (idx m)).1=q := by
      have hm := (Finset.mem_filter.mp m.property).2
      exact Option.some.inj (by simpa only [color,dif_pos (outside q m.val m.property)] using hm)
    have inj : Function.Injective (fun m : cluster q => (slot (idx m)).2) := by
      intro x y eq
      have both := slot.injective (Prod.ext ((lab x).trans (lab y).symm) eq)
      exact Subtype.ext (congrArg (fun v : O => v.val) both)
    simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective _ inj
  have restrict (q : Fin u) (v : M → ℂ) :
      (∑ m : cluster q,v m.val) = ∑ m : M,Q q m*v m := by
    calc
      _ = ∑ m ∈ cluster q,v m := Finset.sum_coe_sort _ _
      _ = _ := by simp [cluster,Q,Finset.sum_filter,ite_mul]
  refine ⟨Q,?_⟩
  intro f own test
  funext m
  by_cases h : label m=i
  · exact own m h
  · let q := (slot ⟨m,h⟩).1
    have mem : m∈cluster q := by simp [cluster,color,h,q]
    have zero := spark (cluster q) (outside q) (size q) (fun n => f n.val)
      (fun z => (restrict q (fun n => features z n*f n)).trans (test q z))
    exact congrFun zero ⟨m,mem⟩

end CriticalThreeBatch

namespace CriticalThreeBatch

open MvPolynomial

private theorem colors_reindex_injective {A B A' B' : Type*} [Fintype B] [Fintype B']
    (M : Matrix A B ℂ) (e : A'≃A) (f : B'≃B) :
    Function.Injective (M.submatrix e f).mulVec ↔ Function.Injective M.mulVec := by
  constructor
  · intro inj x y h
    have eq : (M.submatrix e f).mulVec (x ∘ f)=(M.submatrix e f).mulVec (y ∘ f) := by
      rw [Matrix.submatrix_mulVec_equiv,Matrix.submatrix_mulVec_equiv]
      simpa only [Function.comp_assoc,Equiv.self_comp_symm,Function.comp_id] using congrArg (· ∘ e) h
    funext b
    simpa only [Function.comp_apply,Equiv.apply_symm_apply] using congrFun (inj eq) (f.symm b)
  · intro inj x y h
    rw [Matrix.submatrix_mulVec_equiv,Matrix.submatrix_mulVec_equiv] at h
    have eq : M.mulVec (x ∘ f.symm)=M.mulVec (y ∘ f.symm) := by
      funext a
      simpa only [Function.comp_apply,Equiv.apply_symm_apply] using congrFun h (e.symm a)
    funext b
    simpa only [Function.comp_apply,Equiv.symm_apply_apply] using congrFun (inj eq) (f b)

/-- Simultaneous injectivity with one additional square test. Reindexing by
Fin lets the square and rectangular systems have unrelated index types. -/
private theorem common_colors_with_square {I R C V : Type*} [Fintype I] [Fintype R] [Fintype C]
    {u : ℕ} (H : I → Matrix R C (MvPolynomial V ℂ)) (T : Matrix (Fin u) (Fin u) (MvPolynomial V ℂ))
    (one : ∀ i,∃ p : V→ℂ,Function.Injective ((H i).map (eval p)).mulVec)
    (square : ∃ p : V→ℂ,Function.Injective (T.map (eval p)).mulVec) :
    ∃ p : V→ℂ,Function.Injective (T.map (eval p)).mulVec ∧
      ∀ i,Function.Injective ((H i).map (eval p)).mulVec := by
  classical
  let rows : Option I → ℕ := Option.elim' u (fun _ => Fintype.card R)
  let cols : Option I → ℕ := Option.elim' u (fun _ => Fintype.card C)
  let er := (Fintype.equivFin R).symm
  let ec := (Fintype.equivFin C).symm
  let test : (i : Option I) → Matrix (Fin (rows i)) (Fin (cols i)) (MvPolynomial V ℂ)
    | none => T
    | some i => (H i).submatrix er ec
  have each : ∀ i : Option I, ∃ p : V→ℂ,Function.Injective ((test i).map (eval p)).mulVec := by
    intro i
    cases i with
    | none => exact square
    | some i =>
      obtain ⟨p,hp⟩ := one i
      exact ⟨p,(colors_reindex_injective ((H i).map (eval p)) er ec).mpr hp⟩
  obtain ⟨p,hp⟩ := LastSliceBatch.common_injective test each
  exact ⟨p,hp none,fun i => (colors_reindex_injective ((H i).map (eval p)) er ec).mp (hp (some i))⟩

private theorem right_system_iff {I M S : Type*} [Fintype M] [DecidableEq M] [DecidableEq I]
    {u : ℕ} (label : M→I) (i : I) (feature : S→M→ℂ) (Q : Matrix (Fin u) M ℂ)
    (H : Matrix (M ⊕ (Fin u × S)) M ℂ)
    (entries : ∀ row m,H row m=row.elim
      (fun c => if m=c ∧ label c=i then 1 else 0)
      (fun e => Q e.1 m * feature e.2 m)) :
    Function.Injective H.mulVec ↔
      ∀ f : M→ℂ,(∀ m,label m=i → f m=0) →
        (∀ q z,∑ m,Q q m*(feature z m*f m)=0) → f=0 := by
  classical
  have own (f : M→ℂ) (m : M) : H.mulVec f (.inl m)=if label m=i then f m else 0 := by
    change (∑ x : M,H (.inl m) x*f x)=_
    by_cases same : label m=i <;> simp [entries,same,ite_mul,Finset.sum_ite_eq']
  have rest (f : M→ℂ) (q : Fin u) (z : S) :
      H.mulVec f (.inr (q,z))=∑ m,Q q m*(feature z m*f m) := by
    change (∑ x : M,H (.inr (q,z)) x*f x)=_
    simp only [entries,Sum.elim_inr,mul_assoc]
  constructor
  · intro inj f atzero test
    have ker : H.mulVec f=0 := by
      funext row
      rcases row with m | ⟨q,z⟩
      · by_cases eq : label m=i <;> simp [own,eq,atzero]
      · exact (rest f q z).trans (test q z)
    exact inj (ker.trans (Matrix.mulVec_zero _).symm)
  · intro direct
    change Function.Injective H.mulVecLin
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro f zero
    apply direct f
    · intro m eq
      have h := congrFun zero (.inl m)
      change H.mulVec f (.inl m)=0 at h
      rwa [own,if_pos eq] at h
    · intro q z
      exact (rest f q z).symm.trans (congrFun zero (.inr (q,z)))

/-- If every small outside subset is detected by its local scalar functions,
one right matrix of full row rank supplies all required hub equations.
The per-hub colorings may use different partitions. -/
theorem common_colored_functionals {I M S : Type*} [Fintype I] [Fintype M] [Fintype S] [DecidableEq I]
    (u : ℕ) (label : M→I) (capacity : I→ℕ) (feature : I→S→M→ℂ)
    (rankRoom : u≤Fintype.card M)
    (room : ∀ i,Fintype.card {m : M // label m≠i}≤u*capacity i)
    (spark : ∀ i,∀ T : Finset M,(∀ m∈T,label m≠i) → T.card≤capacity i →
      ∀ f : T→ℂ,(∀ z,∑ m : T,feature i z m.val*f m=0) → f=0) :
    ∃ Q : Matrix (Fin u) M ℂ,Function.Surjective Q.mulVec ∧
      ∀ i,∀ f : M→ℂ,(∀ m,label m=i → f m=0) →
        (∀ q z,∑ m,Q q m*(feature i z m*f m)=0) → f=0 := by
  classical
  let V := Fin u × M
  let R := M ⊕ (Fin u × S)
  let H (i : I) : Matrix R M (MvPolynomial V ℂ) := fun row m => row.elim
    (fun c => if m=c ∧ label c=i then 1 else 0)
    (fun e => X (e.1,m)*C (feature i e.2 m))
  have action (i : I) (p : V→ℂ) :
      Function.Injective ((H i).map (eval p)).mulVec ↔
      ∀ f : M→ℂ,(∀ m,label m=i → f m=0) →
        (∀ q z,∑ m,p (q,m)*(feature i z m*f m)=0) → f=0 := by
    apply right_system_iff label i (feature i) (fun q m => p (q,m))
    intro row m
    change eval p (H i row m)=_
    rcases row with c|⟨q,z⟩
    · by_cases h : m=c ∧ label c=i <;> simp [H,h]
    · simp [H]
  have possible (i : I) : ∃ p : V→ℂ,Function.Injective ((H i).map (eval p)).mulVec := by
    obtain ⟨Q,hQ⟩ := one_right_coloring label i u (capacity i) (feature i) (room i) (spark i)
    exact ⟨fun v => Q v.1 v.2,(action i _).mpr hQ⟩
  obtain ⟨pivot⟩ : Nonempty (Fin u ↪ M) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_fin] using rankRoom)
  let minor : Matrix (Fin u) (Fin u) (MvPolynomial V ℂ) := fun q j => X (q,pivot j)
  have rankTest : ∃ p : V→ℂ,Function.Injective (minor.map (eval p)).mulVec := by
    let seed (v : V) : ℂ := if v.2=pivot v.1 then 1 else 0
    have ident : minor.map (eval seed)=1 := by
      apply Matrix.ext
      intro i j
      rw [Matrix.one_apply]
      change eval seed (X (i,pivot j))=_
      rw [eval_X]
      change (if pivot j=pivot i then (1:ℂ) else 0)=_
      rw [pivot.injective.eq_iff]
      by_cases e : i=j
      · subst j; simp
      · simp [e,Ne.symm e]
    refine ⟨seed,?_⟩
    rw [ident]
    intro x y eq
    simpa only [Matrix.one_mulVec] using eq
  obtain ⟨p,ind,localTests⟩ := common_colors_with_square H minor possible rankTest
  let Q : Matrix (Fin u) M ℂ := fun q m => p (q,m)
  have evalMinor : minor.map (eval p)=Q.submatrix id pivot := by
    apply Matrix.ext
    intro i j
    change eval p (X (i,pivot j))=p (i,pivot j)
    rw [eval_X]
  rw [evalMinor] at ind
  have surj : Function.Surjective (Q.submatrix id pivot).mulVecLin :=
    Matrix.mulVec_surjective_iff_isUnit.mpr (Matrix.mulVec_injective_iff_isUnit.mp ind)
  have top := LinearMap.range_eq_top.mpr surj
  rw [Matrix.range_mulVecLin] at top
  have full : Function.Surjective Q.mulVecLin := by
    apply LinearMap.range_eq_top.mp
    rw [Matrix.range_mulVecLin]
    apply top_unique
    rw [← top]
    apply Submodule.span_mono
    rintro _ ⟨i,rfl⟩
    exact ⟨pivot i,rfl⟩
  exact ⟨Q,full,fun i => (action i p).mp (localTests i)⟩

end CriticalThreeBatch

namespace CriticalThreeBatch

/-- One right relation matrix detects the mass, quadratic hub and private
pole equations at every hub. The number of outside marks may be as large
as the number of right relations times the local interpolation dimension. -/
theorem common_right_colors {I J M : Type*} [Fintype I] [Fintype J] [Fintype M] [DecidableEq I]
    (u : ℕ) (owner : J→I) (label : M→I) (t : M→ℂ) (a : I→ℂ) (w : J→ℂ)
    (rankRoom : u≤Fintype.card M)
    (room : ∀ i,Fintype.card {m : M // label m≠i} ≤ u*(Fintype.card {j : J // owner j=i}+2))
    (spark : ∀ i,∀ B : Finset M,(∀ m∈B,label m≠i) →
      B.card≤Fintype.card {j : J // owner j=i}+2 →
      ∀ f : B→ℂ,(∑ m,f m)=0 → (∑ m,(t m.val^2+a i*t m.val)*f m)=0 →
        (∀ j,owner j=i → (∑ m,f m/(t m.val+w j))=0) → f=0) :
    ∃ Q : Matrix (Fin u) M ℂ,Function.Surjective Q.mulVec ∧
      ∀ i,∀ f : M→ℂ,(∀ m,label m=i → f m=0) →
        (∀ q,∑ m,Q q m*f m=0) →
        (∀ q,∑ m,(Q q m*f m)*(t m^2+a i*t m)=0) →
        (∀ j,owner j=i → ∀ q,∑ m,(Q q m*f m)/(t m+w j)=0) → f=0 := by
  classical
  let S := Unit ⊕ Unit ⊕ J
  let feature (i : I) (s : S) (m : M) : ℂ := s.elim (fun _ => 1)
    (Sum.elim (fun _ => t m^2+a i*t m) (fun j => if owner j=i then (t m+w j)⁻¹ else 0))
  let cap (i : I) := Fintype.card {j : J // owner j=i}+2
  obtain ⟨Q,onto,good⟩ := common_colored_functionals u label cap feature rankRoom room (by
    intro i B outside size f test
    apply spark i B outside size f
    · simpa only [feature,Sum.elim_inl,one_mul] using test (.inl ())
    · exact test (.inr (.inl ()))
    · intro j hj
      simpa only [feature,Sum.elim_inr,if_pos hj,div_eq_mul_inv,mul_comm (t _+_)⁻¹] using test (.inr (.inr j)))
  refine ⟨Q,onto,?_⟩
  intro i f own mass hub poles
  apply good i f own
  intro q s
  rcases s with ⟨⟩|⟨⟩|j
  · simpa only [feature,Sum.elim_inl,one_mul] using mass q
  · simpa [feature,mul_assoc,mul_comm,mul_left_comm] using hub q
  · by_cases eq : owner j=i
    · simpa [feature,eq,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using poles j eq q
    · simp [feature,eq]

/-- Positive real nodes and distinct private poles give the required local
tests over ℂ, so the common right matrix requires only the count assumptions. -/
theorem common_right_colors_positive {I J M : Type*} [Fintype I] [Fintype J] [Fintype M] [DecidableEq I]
    (u : ℕ) (owner : J→I) (label : M→I) (t : M→ℝ) (a : I→ℝ) (w : J→ℝ)
    (tinj : Function.Injective t)
    (winj : ∀ i,Function.Injective (fun j : {j : J // owner j=i} => w j.val))
    (posT : ∀ m,0<t m) (posA : ∀ i,0<a i) (posW : ∀ j,0<w j)
    (rankRoom : u≤Fintype.card M)
    (room : ∀ i,Fintype.card {m : M // label m≠i} ≤ u*(Fintype.card {j : J // owner j=i}+2)) :
    ∃ Q : Matrix (Fin u) M ℂ,Function.Surjective Q.mulVec ∧
      ∀ i,∀ f : M→ℂ,(∀ m,label m=i → f m=0) →
        (∀ q,∑ m,Q q m*f m=0) →
        (∀ q,∑ m,(Q q m*f m)*((t m:ℂ)^2+(a i:ℂ)*(t m:ℂ))=0) →
        (∀ j,owner j=i → ∀ q,∑ m,(Q q m*f m)/((t m:ℂ)+(w j:ℂ))=0) → f=0 := by
  apply common_right_colors u owner label (fun m => (t m:ℂ)) (fun i => (a i:ℂ)) (fun j => (w j:ℂ)) rankRoom room
  intro i B _ size f mass hub poles
  exact private_full_spark_positive (fun m : B => t m.val) (fun j : {j : J // owner j=i} => w j.val) (a i)
    (tinj.comp Subtype.val_injective) (winj i) (fun m => posT m.val) (fun j => posW j.val) (posA i)
    (by simpa only [Fintype.card_coe] using size) f mass hub (fun j => poles j.val j.property)

end CriticalThreeBatch

namespace CriticalThreeCubic

/-- With first factors (1,t,t³), the two commutators differ entrywise by
a quadratic divided difference. Eliminating one row from a pair leaves
only one pole, at −u−v. -/
theorem cubic_pair {I K : Type*} [Fintype I] [Field K]
    (a p b : I → K) (u v t x y : K) (pole : t+u+v≠0)
    (linear : x+y+∑ i,p i*b i=0)
    (cubic : (u^2+u*t+t^2)*x+(v^2+v*t+t^2)*y+
      ∑ i,p i*(a i^2+a i*t+t^2)*b i=0) :
    let R := (∑ i,p i*(a i-u)*(a i-v)*b i)/(t+u+v)
    (u-v)*x=-(∑ i,p i*(a i-v)*b i)-R ∧
    (u-v)*((u^2+u*t+t^2)*x)=-(∑ i,p i*(a i-v)*((a i^2+a i*t+t^2)*b i))+
      (∑ i,p i*(a i-u)*(a i-v)*(a i+(u+v))*b i)+(u*v-(u+v)^2)*R := by
  intro R
  have elim : (u-v)*(t+u+v)*x=-(∑ i,p i*(a i-v)*(t+a i+v)*b i) := by
    have sub : (∑ i,p i*(a i-v)*(t+a i+v)*b i)=
        (∑ i,p i*(a i^2+a i*t+t^2)*b i)-(v^2+v*t+t^2)*(∑ i,p i*b i) := by
      rw [Finset.mul_sum,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [sub]
    linear_combination cubic - (v^2+v*t+t^2)*linear
  have split : (∑ i,p i*(a i-v)*(t+a i+v)*b i)=
      (t+u+v)*(∑ i,p i*(a i-v)*b i)+(∑ i,p i*(a i-u)*(a i-v)*b i) := by
    rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have clear : R*(t+u+v)=(∑ i,p i*(a i-u)*(a i-v)*b i) := div_mul_cancel₀ _ pole
  have first : (u-v)*x=-(∑ i,p i*(a i-v)*b i)-R := by
    apply mul_right_cancel₀ pole
    rw [split] at elim
    linear_combination elim + clear
  refine ⟨first,?_⟩
  have changeRows : (u^2+u*t+t^2)*(∑ i,p i*(a i-v)*b i)-
      (∑ i,p i*(a i-v)*((a i^2+a i*t+t^2)*b i)) =
      -((t-v)*(∑ i,p i*(a i-u)*(a i-v)*b i)+
        (∑ i,p i*(a i-u)*(a i-v)*(a i+(u+v))*b i)) := by
    rw [Finset.mul_sum,←Finset.sum_sub_distrib,Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  linear_combination (u^2+u*t+t^2)*first - changeRows - (t-v)*clear

end CriticalThreeCubic

namespace CriticalThreeBatch

/-- In a component with several right relations, each pair belongs to
one hub. Its two physical diagonals force that hub coordinate to vanish
at either member of the pair. All remaining tests are scalar. -/
theorem rectangular_private_kernel {K I J A M V : Type*} [Field K] [Fintype A] [Fintype M]
    (node : A→K) (distinct : Function.Injective node) (mark : M↪A)
    (hub : I→A) (left right : J→A) (owner : J→I) (attach : A→I)
    (covers : ∀ s,(∃ i,hub i=s) ∨ (∃ j,left j=s) ∨ ∃ j,right j=s)
    (hubGroup : ∀ i,attach (hub i)=i) (leftGroup : ∀ j,attach (left j)=owner j)
    (rightGroup : ∀ j,attach (right j)=owner j)
    (awayU : ∀ j,hub (owner j)≠left j) (awayV : ∀ j,hub (owner j)≠right j)
    (pairwise : ∀ j,left j≠right j)
    (regular : ∀ j s,node s+node (left j)+node (right j)≠0)
    (Q : Matrix V M K) :
    let a (i : I) := node (hub i)
    let u (j : J) := node (left j)
    let v (j : J) := node (right j)
    let t (k : M) := node (mark k)
    (∀ i : I, ∀ f : M→K, (∀ k, attach (mark k)=i → f k=0) →
      (∀ q,(∑ k,f k*Q q k)=0) → (∀ q,(∑ k,(((t k)^2+a i*t k)*f k)*Q q k)=0) →
      (∀ j, owner j=i → ∀ q,(∑ k,(f k/(t k+u j+v j))*Q q k)=0) → f=0) →
    ∃ P : Matrix J A K, ∀ E : A→M→K,
      (∀ j k,(∑ s,P j s*((node s-t k)*E s k))=0) →
      (∀ j k,(∑ s,P j s*(((node s)^3-(t k)^3)*E s k))=0) →
      (∀ q s,(∑ k,((node s-t k)*E s k)*Q q k)=0) →
      (∀ q s,(∑ k,(((node s)^3-(t k)^3)*E s k)*Q q k)=0) →
      ∀ s k,s≠mark k → E s k=0 := by
  classical
  intro a u v t scalar
  let P : Matrix J A K := fun j s =>
    (if s=left j then 1 else 0)+(if s=right j then 1 else 0)+(if s=hub (owner j) then 1 else 0)
  have row (j : J) (f : A→K) :
      (∑ s,P j s*f s)=f (left j)+f (right j)+f (hub (owner j)) := by
    simp [P,add_mul,Finset.sum_add_distrib,ite_mul]
  refine ⟨P,?_⟩
  intro E leftB leftC rightB rightC
  let B (s : A) (k : M) := (node s-t k)*E s k
  let C (s : A) (k : M) := ((node s)^2+node s*t k+(t k)^2)*B s k
  let S (i : I) := B (hub i)
  have cube (s : A) (k : M) : C s k=((node s)^3-(t k)^3)*E s k := by dsimp [C,B]; ring
  have diag (k : M) : B (mark k) k=0 := by simp [B,t]
  have lin (j : J) (k : M) : B (left j) k+B (right j) k+S (owner j) k=0 :=
    (row j (fun s => B s k)).symm.trans (leftB j k)
  have cub (j : J) (k : M) :
      ((u j)^2+u j*t k+(t k)^2)*B (left j) k+
      ((v j)^2+v j*t k+(t k)^2)*B (right j) k+
      ((a (owner j))^2+a (owner j)*t k+(t k)^2)*S (owner j) k=0 := by
    have z : (∑ s,P j s*C s k)=0 := by simp only [cube,leftC]
    exact (row j (fun s => C s k)).symm.trans z
  have aU (j : J) : a (owner j)-u j≠0 := sub_ne_zero.mpr (distinct.ne (awayU j))
  have aV (j : J) : a (owner j)-v j≠0 := sub_ne_zero.mpr (distinct.ne (awayV j))
  have aSum (j : J) : a (owner j)+u j+v j≠0 := regular j (hub (owner j))
  let G (j : J) := (a (owner j)-u j)*(a (owner j)-v j)
  have pair (j : J) (k : M) :
      (u j-v j)*B (left j) k+(a (owner j)-v j)*S (owner j) k+
      G j*(S (owner j) k/(t k+u j+v j))=0 := by
    have e := (CriticalThreeCubic.cubic_pair (I:=Unit) (fun _ => a (owner j)) (fun _ => 1)
      (fun _ => S (owner j) k) (u j) (v j) (t k) (B (left j) k) (B (right j) k)
      (regular j (mark k)) (by simpa using lin j k) (by simpa using cub j k)).1
    simp only [Fintype.sum_unique,one_mul] at e
    dsimp only [G]
    linear_combination e
  have own (k : M) : S (attach (mark k)) k=0 := by
    rcases covers (mark k) with ⟨i,atI⟩ | ⟨j,atU⟩ | ⟨j,atV⟩
    · rw [← atI,hubGroup]
      exact (congrArg (fun s => B s k) atI).trans (diag k)
    · rw [← atU,leftGroup]
      have z : B (left j) k=0 := atU ▸ diag k
      have lk := lin j k
      have ck := cub j k
      rw [z,zero_add] at lk
      rw [z,mul_zero,zero_add] at ck
      have val : t k=u j := congrArg node atU.symm
      rw [val] at ck
      apply (mul_eq_zero.mp (show ((a (owner j)-v j)*(a (owner j)+u j+v j))*S (owner j) k=0 by
        linear_combination ck-((v j)^2+v j*u j+(u j)^2)*lk)).resolve_left
      exact mul_ne_zero (aV j) (aSum j)
    · rw [← atV,rightGroup]
      have z : B (right j) k=0 := atV ▸ diag k
      have lk := lin j k
      have ck := cub j k
      rw [z,add_zero] at lk
      rw [z,mul_zero,add_zero] at ck
      have val : t k=v j := congrArg node atV.symm
      rw [val] at ck
      apply (mul_eq_zero.mp (show ((a (owner j)-u j)*(a (owner j)+u j+v j))*S (owner j) k=0 by
        linear_combination ck-((u j)^2+u j*v j+(v j)^2)*lk)).resolve_left
      exact mul_ne_zero (aU j) (aSum j)
  let L (q : V) : (M→K) →ₗ[K] K := ∑ k,(Q q k) • (LinearMap.proj k : (M→K) →ₗ[K] K)
  have readL (q : V) (f : M→K) : L q f=∑ k,f k*Q q k := by
    simp [L,LinearMap.sum_apply,mul_comm]
  have hB (q : V) (s : A) : L q (B s)=0 := (readL q _).trans (rightB q s)
  have hC (q : V) (s : A) : L q (C s)=0 := by rw [readL]; simp only [cube,rightC]
  have hubZero (i : I) : S i=0 := by
    apply scalar i _ (fun k eq => eq ▸ own k)
    · exact fun q => (readL q _).symm.trans (hB q (hub i))
    · intro q
      have split : (fun k => ((t k)^2+a i*t k)*S i k)=C (hub i)-(a i)^2 • S i := by
        funext k
        change _=(((a i)^2+a i*t k+(t k)^2)*S i k)-(a i)^2*S i k
        ring
      rw [← readL,split,map_sub,map_smul,hC,hB q (hub i)]
      simp
    · intro j eq q
      subst i
      let f (k : M) := S (owner j) k/(t k+u j+v j)
      have e : (u j-v j) • B (left j)+(a (owner j)-v j) • S (owner j)+G j • f=0 := by
        funext k
        exact pair j k
      have he := congrArg (L q) e
      simp only [map_add,map_smul,map_zero,smul_eq_mul,hB,
        show L q (S (owner j))=0 from hB q _,mul_zero,zero_add] at he
      exact (readL q _).symm.trans ((mul_eq_zero.mp he).resolve_left (mul_ne_zero (aU j) (aV j)))
  intro s k ne
  have all (j : J) : B (left j) k=0 ∧ B (right j) k=0 := by
    have hs : S (owner j) k=0 := congrFun (hubZero _) k
    have e := pair j k
    rw [hs,zero_div,mul_zero,mul_zero,add_zero,add_zero] at e
    have e₁ := (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr (distinct.ne (pairwise j)))
    exact ⟨e₁,by simpa only [hs,e₁,zero_add,add_zero] using lin j k⟩
  have zero : B s k=0 := by
    rcases covers s with ⟨i,rfl⟩ | ⟨j,rfl⟩ | ⟨j,rfl⟩
    · exact congrFun (hubZero i) k
    · exact (all j).1
    · exact (all j).2
  exact (mul_eq_zero.mp zero).resolve_left (sub_ne_zero.mpr (distinct.ne ne))

end CriticalThreeBatch

namespace CriticalThreeBatch

private theorem sigma_fiber_card {I T : Type*} [Fintype I] [Fintype T] [DecidableEq I]
    (slots : I→ℕ) (idx : T ≃ Σ i,Fin (slots i)) (i : I) :
    Fintype.card {z : T // (idx z).1=i}=slots i := by
  classical
  let a : {z : T // (idx z).1=i} ≃ {z : Σ j,Fin (slots j) // z.1=i} :=
    idx.subtypeEquiv fun _ => Iff.rfl
  let b : {z : Σ j,Fin (slots j) // z.1=i} ≃ Fin (slots i) :=
    { toFun := fun z => finCongr (congrArg slots z.property) z.val.2
      invFun := fun x => ⟨⟨i,x⟩,rfl⟩
      left_inv := by rintro ⟨⟨j,x⟩,rfl⟩;rfl
      right_inv := fun _ => rfl }
  simpa only [Fintype.card_fin] using Fintype.card_congr (a.trans b)

/-- Private pairs and component marks with arbitrary prescribed quotas.
Each hub owns itself and both samples of every assigned pair. -/
theorem private_marks {h p m : ℕ} (g e : Fin h→ℕ)
    (pairs : ∑ i,g i=p) (marks : ∑ i,e i=m) (room : ∀ i,e i≤2*g i+1) :
    ∃ owner : Fin p→Fin h, ∃ mark : Fin m ↪ (Fin h ⊕ (Fin p ⊕ Fin p)),
      let attach : Fin h ⊕ (Fin p ⊕ Fin p) → Fin h := Sum.elim id (Sum.elim owner owner)
      (∀ i,Fintype.card {j : Fin p // owner j=i}=g i) ∧
      (∀ i,Fintype.card {k : Fin m // attach (mark k)≠i}=m-e i) := by
  classical
  let pg : (Σ i : Fin h,Fin (g i)) ≃ Fin p := Fintype.equivOfCardEq (by simpa using pairs)
  let me : Fin m ≃ (Σ i : Fin h,Fin (e i)) := Fintype.equivOfCardEq (by simpa using marks.symm)
  let owner (j : Fin p) := (pg.symm j).1
  let Pos (i : Fin h) := Unit ⊕ (Fin (g i) ⊕ Fin (g i))
  let attach : Fin h ⊕ (Fin p ⊕ Fin p) → Fin h := Sum.elim id (Sum.elim owner owner)
  let localSlot (i : Fin h) : Fin (e i) ↪ Pos i := Classical.choice (Function.Embedding.nonempty_of_card_le (by
    simp only [Pos,Fintype.card_sum,Fintype.card_unit,Fintype.card_fin]
    have := room i
    omega))
  let represent (z : Σ i : Fin h,Pos i) : Fin h ⊕ (Fin p ⊕ Fin p) :=
    z.2.elim (fun _ => .inl z.1) (Sum.elim
      (fun j => .inr (.inl (pg ⟨z.1,j⟩))) (fun j => .inr (.inr (pg ⟨z.1,j⟩))))
  have allocated (i : Fin h) (s : Pos i) : attach (represent ⟨i,s⟩)=i := by
    rcases s with _ | j | j <;> simp [represent,attach,owner]
  have atOne (i : Fin h) : Function.Injective (fun s : Pos i => represent ⟨i,s⟩) := by
    rintro (⟨⟩|a|a) (⟨⟩|b|b) eq <;> simp [represent] at eq <;> subst_vars <;> rfl
  have inj : Function.Injective represent := by
    rintro ⟨i,z⟩ ⟨j,w⟩ eq
    have same := congrArg attach eq
    rw [allocated,allocated] at same
    subst j
    exact congrArg (Sigma.mk i) (atOne i eq)
  let lift := Function.Embedding.sigmaMap (Function.Embedding.refl (Fin h)) localSlot
  let mark := (me.toEmbedding.trans lift).trans (show (Σ i,Pos i) ↪ _ from ⟨represent,inj⟩)
  have group (k : Fin m) : attach (mark k)=(me k).1 := allocated _ _
  refine ⟨owner,mark,sigma_fiber_card g pg.symm,?_⟩
  intro i
  change Fintype.card {k : Fin m // ¬attach (mark k)=i}=_
  rw [Fintype.card_subtype_compl,Fintype.card_fin]
  simp only [group,sigma_fiber_card e me]

/-- Natural sample parameters give distinct positive first coordinates
and distinct positive denominators on all the private pairs. -/
theorem private_nodes (h p : ℕ) :
    ∃ node : Fin h ⊕ (Fin p ⊕ Fin p) → ℕ, Function.Injective node ∧ (∀ s,0<node s) ∧
      Function.Injective (fun j : Fin p => node (.inr (.inl j))+node (.inr (.inr j))) := by
  let node : Fin h ⊕ (Fin p ⊕ Fin p)→ℕ := Sum.elim (fun i => i.val+1)
    (Sum.elim (fun j => h+j.val+1) (fun j => h+p+j.val+1))
  refine ⟨node,?_,?_,?_⟩
  · rintro (i|j|j) (i'|j'|j') eq <;> dsimp [node] at eq
    all_goals first | exact congrArg Sum.inl (Fin.ext (by omega))
                    | exact congrArg (fun x => Sum.inr (Sum.inl x)) (Fin.ext (by omega))
                    | exact congrArg (fun x => Sum.inr (Sum.inr x)) (Fin.ext (by omega))
                    | omega
  · rintro (i|j|j) <;> dsimp [node] <;> omega
  · intro j k eq
    dsimp [node] at eq
    exact Fin.ext (by omega)

end CriticalThreeBatch

namespace CriticalThreeBatch

/-- Local CP tangent for a component with u independent right relations.
The numbers eᵢ count marks on the 2gᵢ+1 physical labels belonging to hub
i. Every label outside that hub is detected by its private scalar functions. -/
theorem local_cubic_component {h p m u : ℕ} (hu : u≤ m) (g e : Fin h→ℕ)
    (pairs : (∑ i,g i)=p) (marks : (∑ i,e i)=m)
    (room : ∀ i,e i≤2*g i+1) (fit : ∀ i,m-e i≤u*(g i+2)) :
    let r := 2*p+h
    let b := p+h
    let n := m-u
    ∃ x : Fin m→Fin 3→ℂ, ∃ y : Fin m→Fin b→ℂ, ∃ z : Fin m→Fin n→ℂ,
    ∃ x' : Fin (r-m)→Fin 3→ℂ, ∃ y' : Fin (r-m)→Fin b→ℂ,
    ∀ T : Fin 3→Fin b→Fin n→ℂ, ∃ U : Fin m→Fin 3→ℂ,
      ∃ V : Fin m→Fin b→ℂ, ∃ W : Fin m→Fin n→ℂ, ∃ W' : Fin (r-m)→Fin n→ℂ,
      ∀ i j k,T i j k=(∑ s,(U s i*(y s j*z s k)+x s i*(V s j*z s k)+x s i*(y s j*W s k)))+
        ∑ s,x' s i*(y' s j*W' s k) := by
  classical
  intro r b n
  obtain ⟨owner,mark,fiber,outside⟩ := private_marks g e pairs marks room
  let A := Fin h ⊕ (Fin p ⊕ Fin p)
  let H (i : Fin h) : A := .inl i
  let L (j : Fin p) : A := .inr (.inl j)
  let R (j : Fin p) : A := .inr (.inr j)
  let attach : A→Fin h := Sum.elim id (Sum.elim owner owner)
  let label (k : Fin m) := attach (mark k)
  obtain ⟨natNode,distinct,positive,poleDistinct⟩ := private_nodes h p
  let re (s : A) : ℝ := natNode s
  let node (s : A) : ℂ := re s
  let pole (j : Fin p) : ℝ := re (L j)+re (R j)
  have injReal : Function.Injective re := by
    intro s t eq
    apply distinct
    dsimp only [re] at eq
    exact_mod_cast eq
  have injC : Function.Injective node := Complex.ofReal_injective.comp injReal
  have posReal (s : A) : 0<re s := by dsimp only [re]; exact_mod_cast positive s
  have injPole : Function.Injective pole := by
    intro a b eq
    apply poleDistinct
    dsimp only [pole,re,L,R] at eq
    exact_mod_cast eq
  have reg (j : Fin p) (s : A) : node s+node (L j)+node (R j)≠0 := by
    dsimp only [node]
    exact_mod_cast (ne_of_gt (add_pos (add_pos (posReal s) (posReal (L j))) (posReal (R j))))
  obtain ⟨Q,_,detect⟩ := common_right_colors_positive u owner label (fun k => re (mark k))
    (fun i => re (H i)) pole (injReal.comp mark.injective)
    (fun _ => injPole.comp Subtype.val_injective)
    (fun k => posReal (mark k)) (fun i => posReal (H i)) (fun j => add_pos (posReal _) (posReal _))
    (by simpa only [Fintype.card_fin] using hu)
    (fun i => by
      change Fintype.card {k : Fin m // attach (mark k)≠i}≤_
      rw [outside i,fiber i];exact fit i)
  have cover (s : A) : (∃ i,H i=s) ∨ (∃ j,L j=s) ∨ ∃ j,R j=s := by
    rcases s with i | j | j
    · exact Or.inl ⟨i,rfl⟩
    · exact Or.inr (Or.inl ⟨j,rfl⟩)
    · exact Or.inr (Or.inr ⟨j,rfl⟩)
  obtain ⟨P,kernel⟩ := rectangular_private_kernel node injC mark H L R owner attach cover
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => by simp [H,L])
    (fun _ => by simp [H,R]) (fun _ eq => nomatch Sum.inr.inj eq) reg Q (by
      intro i f own mass quad poles
      apply detect i f own
      · intro q
        simpa only [mul_comm] using mass q
      · intro q
        simpa only [node,mul_assoc,mul_left_comm,mul_comm] using quad q
      · intro j assigned q
        simpa only [node,pole,Complex.ofReal_add,add_assoc,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm]
          using poles j assigned q)
  have countA : Fintype.card A=r := by
    simp only [A,Fintype.card_sum,Fintype.card_fin,r]
    omega
  have hb : Fintype.card (Fin b) ≤ Fintype.card A-Fintype.card (Fin p) := by
    simp only [countA,Fintype.card_fin,b,r]
    omega
  have hn : Fintype.card (Fin n) ≤ Fintype.card (Fin m)-Fintype.card (Fin u) := by
    simp only [Fintype.card_fin,n,le_refl]
  have tangent := CriticalThreeQuotient.rectangular_tangent_of_kernel_samples
    hb hn mark node (fun s => (node s)^3) injC P Q kernel
  dsimp only at tangent
  rw [countA,Fintype.card_fin] at tangent
  obtain ⟨Y,Z,other,span⟩ := tangent
  exact ⟨fun s => ![1,node (mark s),(node (mark s))^3],fun s => Y (mark s),Z,
    fun s => ![1,node (other s),(node (other s))^3],fun s => Y (other s),span⟩

end CriticalThreeBatch

namespace CriticalThreeCubic

private theorem distribute {n M : ℕ} (lo hi : Fin n → ℕ)
    (ordered : ∀ i, lo i ≤ hi i) (below : (∑ i, lo i) ≤ M) (above : M ≤ ∑ i, hi i) :
    ∃ e : Fin n → ℕ, (∑ i, e i) = M ∧ ∀ i, lo i ≤ e i ∧ e i ≤ hi i := by
  induction n generalizing M with
  | zero =>
    simp at above
    exact ⟨fun i => i.elim0, by simp [above], fun i => i.elim0⟩
  | succ n ih =>
    rw [Fin.sum_univ_succ] at below above
    let pick := max (lo 0) (M - ∑ i : Fin n, hi i.succ)
    have ord₀ := ordered 0
    have tails := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin n) _ => ordered i.succ)
    have good₀ : lo 0 ≤ pick ∧ pick ≤ hi 0 := by dsimp [pick]; omega
    have len : pick ≤ M := by dsimp [pick]; omega
    obtain ⟨e, size, ok⟩ := ih (M:=M-pick) (fun i => lo i.succ) (fun i => hi i.succ)
      (fun i => ordered i.succ) (by dsimp [pick]; omega) (by dsimp [pick]; omega)
    refine ⟨Fin.cons pick e, ?_, Fin.cases good₀ (fun i => ok i)⟩
    rw [Fin.sum_univ_succ]
    simpa only [Fin.cons_zero, Fin.cons_succ, size] using (Nat.add_sub_of_le len)

private theorem hub_sum {h s : ℕ} (hs : s ≤ h) (a b : ℕ) :
    (∑ i : Fin h, if i.val < s then a else b) = s*a+(h-s)*b := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [Fin.sum_univ_add]
  simp

private theorem deficit_iff {l s M A B : ℕ} (hl : 1 ≤ l) (ab : A ≤ B) :
    s*(M-B)+l*(M-A) ≤ M ↔
      (s+l-1)*M ≤ s*B+l*A ∧ (l-1)*M ≤ l*A := by
  have total := congrArg (fun k : ℕ => k*M) (Nat.sub_add_cancel (show 1 ≤ s+l by omega))
  have short := congrArg (fun k : ℕ => k*M) (Nat.sub_add_cancel hl)
  constructor
  · intro cover
    have p := Nat.mul_le_mul_left s (show M ≤ M-B+B by omega)
    have q := Nat.mul_le_mul_left l (show M ≤ M-A+A by omega)
    constructor <;> nlinarith only [p,q,cover,short,total,Nat.zero_le (s*(M-B))]
  · rintro ⟨full,part⟩
    by_cases lo : M ≤ A
    · simp [Nat.sub_eq_zero_of_le lo, Nat.sub_eq_zero_of_le (lo.trans ab)]
    have q := congrArg (fun k : ℕ => l*k) (Nat.sub_add_cancel (show A ≤ M by omega))
    by_cases mid : M ≤ B
    · simp only [Nat.sub_eq_zero_of_le mid, Nat.mul_zero, Nat.zero_add]
      nlinarith only [q,short,part]
    have p := congrArg (fun k : ℕ => s*k) (Nat.sub_add_cancel (show B ≤ M by omega))
    nlinarith only [p,q,full,total]

/-- Cardinalities of the long and short private hubs in a balanced specialization. -/
theorem hub_totals {h d s : ℕ} (hs : s ≤ h) (hd : 1 ≤ d) :
    let g (i : Fin h) := if i.val < s then d else d-1
    (∑ i, g i) = h*d+s-h ∧ (∑ i, (2*g i+1)) = 2*(h*d+s)-h := by
  intro g
  have len := Nat.sub_add_cancel hs
  have mulLen := congrArg (fun k : ℕ => k*d) len
  have sh := congrArg (fun k : ℕ => (h-s)*k) (Nat.sub_add_cancel hd)
  have hmul := Nat.mul_le_mul_left h hd
  simp only [Nat.mul_one] at hmul
  have bound₁ := Nat.sub_add_cancel (show h ≤ h*d+s by omega)
  have bound₂ := Nat.sub_add_cancel (show h ≤ 2*(h*d+s) by omega)
  constructor
  · change (∑ i : Fin h, if i.val < s then d else d-1) = _
    rw [hub_sum hs]
    nlinarith only [len,mulLen,sh,bound₁]
  · have eq (i : Fin h) : 2*g i+1 = if i.val < s then 2*d+1 else 2*(d-1)+1 := by
      split <;> simp_all [g]
    simp_rw [eq]
    rw [hub_sum hs]
    nlinarith only [len,mulLen,sh,bound₂]

/-- Exact integer capacities for one component with u independent relations. -/
theorem component_marks_iff {h d s u M : ℕ} (_hh : 2 ≤ h) (hd : 1 ≤ d) (hs : s < h) :
    let g (i : Fin h) := if i.val < s then d else d-1
    (∃ e : Fin h → ℕ, (∑ i, e i)=M ∧ ∀ i, e i ≤ 2*g i+1 ∧ M-e i ≤ u*(g i+2)) ↔
      M ≤ 2*(h*d+s)-h ∧ M ≤ u*(d+1)+2*d-1 ∧
      (h-1)*M ≤ u*(h*d+s+h) ∧ (h-s-1)*M ≤ u*(h-s)*(d+1) := by
  intro g
  let lo (i : Fin h) := M-u*(g i+2)
  let hi (i : Fin h) := 2*g i+1
  have short (i : Fin h) (hit : ¬i.val < s) : g i = d-1 := if_neg hit
  have long (i : Fin h) (hit : i.val < s) : g i = d := if_pos hit
  have gap : d-1+2=d+1 := by omega
  have edge : 2*(d-1)+1+u*(d+1)=u*(d+1)+2*d-1 := by omega
  have big := hub_totals hs.le hd |>.2
  change (∑ i, hi i)=2*(h*d+s)-h at big
  have len := Nat.sub_add_cancel hs.le
  have formula : (s+(h-s)-1)*M=(h-1)*M := by rw [Nat.add_comm s, len]
  have volumes : s*(u*(d+2))+(h-s)*(u*(d+1))=u*(h*d+s+h) := by
    calc
      _ = u*((h-s+s)*d+s+(h-s+s)) := by ring
      _ = _ := by rw [len]
  have cost : (∑ i,lo i) ≤ M ↔ (h-1)*M ≤ u*(h*d+s+h) ∧
      (h-s-1)*M ≤ u*(h-s)*(d+1) := by
    have term (i : Fin h) : lo i = if i.val<s then M-u*(d+2) else M-u*(d+1) := by
      by_cases hit : i.val<s <;> simp [lo,g,hit,gap]
    simp_rw [term]
    rw [hub_sum hs.le, deficit_iff (by omega) (by gcongr; omega), formula, volumes]
    ring_nf
  have interval : (∀ i,lo i ≤ hi i) ↔ M ≤ u*(d+1)+2*d-1 := by
    constructor
    · intro all
      let i : Fin h := ⟨s,hs⟩
      have z := all i
      simp only [lo,hi,short i (show ¬i.val < s by simp [i]),gap] at z
      omega
    · intro test i
      by_cases hit : i.val<s
      · simp only [lo,hi,long i hit]
        have ub : u*(d+1) ≤ u*(d+2) := by gcongr; omega
        omega
      · simp only [lo,hi,short i hit,gap]
        omega
  constructor
  · rintro ⟨e, sumE, constraint⟩
    have ends (i) : lo i ≤ e i ∧ e i ≤ hi i := by
      obtain ⟨cap,rel⟩ := constraint i
      exact ⟨by dsimp [lo]; omega,cap⟩
    have lower := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => (ends i).1)
    have upper := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => (ends i).2)
    rw [sumE] at lower upper
    exact ⟨upper.trans_eq big,interval.mp (fun i => (ends i).1.trans (ends i).2),cost.mp lower⟩
  · rintro ⟨points,width,alls,shorts⟩
    obtain ⟨e,eq,ok⟩ := distribute lo hi (interval.mpr width) (cost.mpr ⟨alls,shorts⟩)
      (by rwa [big])
    refine ⟨e,eq,fun i => ⟨(ok i).2,?_⟩⟩
    have bound := (ok i).1
    dsimp [lo] at bound
    omega

end CriticalThreeCubic

namespace CriticalThreeCubic

/-- Full blocks of D relations and at most one shorter block preserve the
sum of the pro rata floors. The zero remainder contributes no component. -/
theorem floor_partition (D V q : ℕ) (hD : 0 < D) :
    ∃ C : ℕ, ∃ u : Fin C → ℕ, (∑ i, u i)=q ∧
      (∑ i, u i*V/D)=q*V/D ∧ ∀ i, 0<u i ∧ u i≤D := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    by_cases zero : q=0
    · exact ⟨0,Fin.elim0,by simp [zero],by simp [zero],fun i => i.elim0⟩
    by_cases last : q ≤ D
    · exact ⟨1,fun _ => q,by simp,by simp,fun _ => ⟨Nat.pos_of_ne_zero zero,last⟩⟩
    obtain ⟨C,u,qu,sizes,pos⟩ := ih (q-D) (by omega)
    refine ⟨C+1, Fin.cons D u, ?_, ?_, Fin.cases ⟨hD,le_rfl⟩ pos⟩
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero,Fin.cons_succ,qu]
      omega
    · have parts : q*V=(q-D)*V+V*D := by
        calc q*V = (q-D+D)*V := by congr 1; omega
             _ = _ := by ring
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero,Fin.cons_succ,sizes]
      rw [parts,Nat.add_mul_div_right _ _ hD,Nat.mul_div_cancel_left _ hD]
      omega

private theorem distribute_components {ok : ℕ → ℕ → Prop} {r q C : ℕ}
    (u cap : Fin C → ℕ) (total : (∑ i,u i)=q) (supply : r ≤ ∑ i,cap i)
    (budget : q ≤ r) (sizes : ∀ i, 0<u i ∧ u i≤cap i)
    (test : ∀ i M, M≤cap i → ok (u i) M) :
    ∃ G : ℕ, ∃ rel marks : Fin G → ℕ, (∑ i,rel i)=q ∧ (∑ i,marks i)=r ∧
      ∀ i, 0<rel i ∧ rel i≤ marks i ∧ ok (rel i) (marks i) := by
  obtain ⟨M,eq,fit⟩ := distribute u cap (fun i => (sizes i).2) (total.le.trans budget) supply
  exact ⟨C,u,M,total,eq,fun i => ⟨(sizes i).1,(fit i).1,test i _ (fit i).2⟩⟩

/-- In this range both local hub restrictions hold at the exact pro rata
floor, for every relation block of size at most h−1. -/
theorem floor_capacity {h d s u : ℕ} (hh : 2≤h) (hd : 2≤d) (hs : s<h)
    (size : u≤h-1) (shorts : h≤d+s+2) (longs : s+2≤d) :
    let M := u*(h*d+s+h)/(h-1)
    u≤M ∧ M≤2*(h*d+s)-h ∧ M≤u*(d+1)+2*d-1 ∧
    (h-1)*M≤u*(h*d+s+h) ∧ (h-s-1)*M≤u*(h-s)*(d+1) := by
  intro M
  have den : 0<h-1 := by omega
  have denEq : h-1+1=h := by omega
  have len := Nat.sub_add_cancel hs.le
  have edge : h-s-1+1=h-s := by omega
  have effective : h*d+s+h=(h-1)*(d+1)+(d+1+s) := by
    have e := congrArg (fun H : ℕ => H*(d+1)) denEq
    nlinarith only [e]
  have lower : u*(d+2) ≤ M := by
    apply (Nat.le_div_iff_mul_le den).mpr
    have slope : (d+2)*(h-1) ≤ h*d+s+h := by rw [effective]; nlinarith only [shorts,denEq]
    nlinarith only [Nat.mul_le_mul_left u slope]
  have upper : M*(h-1)≤u*(h*d+s+h) := Nat.div_mul_le_self _ _
  have cap : M ≤ h*d+s+h := by
    apply Nat.le_of_mul_le_mul_right _ den
    have z := Nat.mul_le_mul_right (h*d+s+h) size
    nlinarith only [z,upper]
  have twice : 2*h ≤ h*d := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left h hd
  have full : u*(d+1+s) ≤ (h-1)*(2*d-1) := Nat.mul_le_mul size (by omega)
  have left : u*(d+1)+2*d-1 = u*(d+1)+(2*d-1) := by omega
  have localWidth : M≤u*(d+1)+2*d-1 := by
    apply Nat.le_of_mul_le_mul_right _ den
    rw [effective] at upper
    rw [left]
    nlinarith only [full,upper]
  have volume : u*(h*d+s+h)=s*(u*(d+2))+(h-s)*(u*(d+1)) := by
    calc _ = u*((h-s+s)*d+s+(h-s+s)) := by rw [len]
         _ = _ := by ring
  have peel : h-1=s+(h-s-1) := by omega
  have comp := Nat.mul_le_mul_left s lower
  rw [volume] at upper
  rw [peel] at upper
  have paid : u ≤ u*(d+2) := by simpa using Nat.mul_le_mul_left u (show 1≤d+2 by omega)
  exact ⟨paid.trans lower,by omega,localWidth,by simpa [M,Nat.mul_comm] using Nat.div_mul_le_self (u*(h*d+s+h)) (h-1),
    by nlinarith only [upper,comp]⟩

private theorem realize_caps {h d s q r : ℕ} (hh : 2≤h) (hd : 2≤d) (hs : s<h)
    (points : r=2*(h*d+s)-h) (members : q≤r) {C : ℕ} (u cap : Fin C → ℕ)
    (total : (∑ i,u i)=q) (supply : r≤∑ i,cap i)
    (sizes : ∀ i, 0<u i ∧ u i≤cap i) (caps : ∀ i,
      cap i≤r ∧ cap i≤u i*(d+1)+2*d-1 ∧ (h-1)*cap i≤u i*(h*d+s+h) ∧
      (h-s-1)*cap i≤u i*(h-s)*(d+1)) :
    let g (i : Fin h) := if i.val<s then d else d-1
    ∃ G : ℕ, ∃ rel marks : Fin G → ℕ, (∑ i,rel i)=q ∧ (∑ i,marks i)=r ∧
      ∀ i, 0<rel i ∧ rel i≤ marks i ∧ ∃ e : Fin h→ℕ,
        (∑ j,e j)=marks i ∧ ∀ j, e j≤2*g j+1 ∧ marks i-e j≤rel i*(g j+2) := by
  intro g
  apply distribute_components (ok:=fun U M => ∃ e : Fin h→ℕ, (∑ j,e j)=M ∧
    ∀ j, e j≤2*g j+1 ∧ M-e j≤U*(g j+2)) u cap total supply members sizes
  intro i M below
  apply (component_marks_iff (u:=u i) (M:=M) hh (by omega) hs).mpr
  obtain ⟨all,localWidth,ratio,short⟩ := caps i
  refine ⟨below.trans (all.trans_eq points),below.trans localWidth,
    (Nat.mul_le_mul_left _ below).trans ratio,(Nat.mul_le_mul_left _ below).trans short⟩

/-- The true global dimension budget suffices when the two local slope
bounds hold for the residue s modulo h. -/
theorem component_packing_of_slopes {h d s b r q : ℕ} (hh : 2≤h) (hd : 2≤d) (hs : s<h)
    (base : b=h*d+s) (points : r=2*b-h) (members : q≤r) (budget : (h-1)*r≤q*(b+h))
    (shorts : h≤d+s+2) (longs : s+2≤d) :
    let g (i : Fin h) := if i.val<s then d else d-1
    ∃ G : ℕ, ∃ rel marks : Fin G → ℕ, (∑ i,rel i)=q ∧ (∑ i,marks i)=r ∧
      ∀ i, 0<rel i ∧ rel i≤ marks i ∧ ∃ e : Fin h→ℕ,
        (∑ j,e j)=marks i ∧ ∀ j, e j≤2*g j+1 ∧ marks i-e j≤rel i*(g j+2) := by
  subst b
  obtain ⟨C,u,total,floorSum,sizes⟩ := floor_partition (h-1) (h*d+s+h) q (by omega)
  have cover : r≤q*(h*d+s+h)/(h-1) := (Nat.le_div_iff_mul_le (by omega)).mpr
    (by simpa [Nat.mul_comm] using budget)
  have each (i) := floor_capacity hh hd hs (sizes i).2 shorts longs
  apply realize_caps hh hd hs points members u (fun i => u i*(h*d+s+h)/(h-1)) total
    (floorSum.ge.trans' cover)
  · exact fun i => ⟨(sizes i).1,(each i).1⟩
  · intro i
    simpa only [points] using (each i).2

end CriticalThreeCubic

namespace CriticalThreeCubic

private theorem single_capacity {h d s : ℕ} (hh : 2≤h) (hd : 2≤d) (hs : s<h)
    (range : h≤d+1) (edge : d≤ s+1) :
    let M := d+3
    M≤2*(h*d+s)-h ∧ M≤1*(d+1)+2*d-1 ∧ (h-1)*M≤1*(h*d+s+h) ∧
      (h-s-1)*M≤1*(h-s)*(d+1) := by
  intro M
  simp only [M,Nat.one_mul]
  have base := Nat.mul_le_mul_right d hh
  have unit := Nat.mul_le_mul_left h hd
  have bound : d+3+h≤2*(h*d+s) := by nlinarith
  have den := congrArg (fun v : ℕ => v*(d+3)) (Nat.sub_add_cancel (show 1≤h by omega))
  have short : h-s=1 ∨ h-s=2 := by omega
  refine ⟨by omega,by omega,by nlinarith only [den,show 2*h≤d+s+3 by omega],?_⟩
  rcases short with e|e <;> rw [e] <;> omega

private theorem abundant_singletons {h d s b r q : ℕ} (hh : 10≤h) (hs : s<h)
    (range : h≤d+1) (edge : d≤ s+1)
    (base : b=h*d+s) (points : r=2*b-h) (budget : (h-1)*r≤q*(b+h)) :
    r≤q*(d+3) := by
  have dim : h*h≤b+h := by
    rw [base]
    nlinarith only [Nat.mul_le_mul_left h range,Nat.zero_le s]
  have big : h≤b := by nlinarith only [dim,Nat.mul_le_mul_left h (show 2≤h by omega)]
  have rk : r+h=2*b := by rw [points,Nat.sub_add_cancel (by omega)]
  have den := congrArg (fun v : ℕ => v*r) (Nat.sub_add_cancel (show 1≤h by omega))
  have weight := congrArg (fun v : ℕ => h*v) rk
  have enough : 2*h≤q+4 := by
    by_contra! small
    have bad := Nat.mul_le_mul_right (b+h) (show q+5≤2*h by omega)
    nlinarith only [bad,budget,den,weight,rk,dim,hh]
  have paid := Nat.mul_le_mul_right (d+3) enough
  have slack : 4*d+2*s+12≤7*h := by omega
  rw [base] at rk
  nlinarith only [slack,paid,rk]

private theorem single_exceptions {h d s b r q : ℕ} (hh : 2≤h) (hd : 2≤d)
    (hs : s<h) (range : h≤d+1) (edge : d≤ s+1) (base : b=h*d+s)
    (points : r=2*b-h) (budget : (h-1)*r≤q*(b+h)) (scarce : ¬ r≤q*(d+3)) :
    (h=3 ∧ d=3 ∧ s=2 ∧ q=3) ∨ (h=5 ∧ d=4 ∧ s=4 ∧ q=6) ∨
    (h=7 ∧ d=7 ∧ s=6 ∧ q=10) ∨ (h=8 ∧ d=8 ∧ s=7 ∧ q=12) ∨
    (h=9 ∧ d=9 ∧ s=8 ∧ q=14) := by
  have small : h<10 := by
    by_contra! hlarge
    exact scarce (abundant_singletons hlarge hs range edge base points budget)
  have cases : (d=h ∧ s=h-1) ∨ (d=h-1 ∧ s=h-1) ∨ (d=h-1 ∧ s=h-2) := by omega
  subst b r
  rcases cases with ⟨wd,ws⟩|⟨wd,ws⟩|⟨wd,ws⟩ <;> subst d <;> subst s <;>
    interval_cases h <;> norm_num at * <;> omega

/-- Balanced hub components attain the exact dimension budget for
d≥h−1, apart from the single obstructed quadruple (5,4,4,6). -/
theorem component_packing {h d s b r q : ℕ} (hh : 2≤h) (hd : 2≤d) (hs : s<h)
    (base : b=h*d+s) (points : r=2*b-h) (members : q≤r) (budget : (h-1)*r≤q*(b+h))
    (range : h≤d+1) (exception : ¬(h=5 ∧ d=4 ∧ s=4 ∧ q=6)) :
    let g (i : Fin h) := if i.val<s then d else d-1
    ∃ G : ℕ, ∃ rel marks : Fin G → ℕ, (∑ i,rel i)=q ∧ (∑ i,marks i)=r ∧
      ∀ i, 0<rel i ∧ rel i≤ marks i ∧ ∃ e : Fin h→ℕ,
        (∑ j,e j)=marks i ∧ ∀ j, e j≤2*g j+1 ∧ marks i-e j≤rel i*(g j+2) := by
  by_cases slopes : s+2≤d
  · exact component_packing_of_slopes hh hd hs base points members budget (by omega) slopes
  have edge : d≤ s+1 := by omega
  by_cases enough : r≤q*(d+3)
  · subst b
    apply realize_caps hh hd hs points members (C:=q) (fun _ => 1) (fun _ => d+3)
      (by simp) (by simpa using enough) (fun _ => ⟨by decide,by omega⟩)
    intro _
    simpa only [points] using single_capacity hh hd hs range edge
  obtain c|c|c|c|c := single_exceptions hh hd hs range edge base points budget enough
  · rcases c with ⟨rfl,rfl,rfl,rfl⟩
    subst b r
    exact realize_caps hh hd hs rfl members ![1,1,1] ![7,6,6]
      (by decide) (by decide) (by decide) (by decide)
  · exact (exception c).elim
  · rcases c with ⟨rfl,rfl,rfl,rfl⟩
    subst b r
    exact realize_caps hh hd hs rfl members ![4,3,3] ![41,31,31]
      (by decide) (by decide) (by decide) (by decide)
  · rcases c with ⟨rfl,rfl,rfl,rfl⟩
    subst b r
    exact realize_caps hh hd hs rfl members ![4,4,4] ![45,45,44]
      (by decide) (by decide) (by decide) (by decide)
  · rcases c with ⟨rfl,rfl,rfl,rfl⟩
    subst b r
    exact realize_caps hh hd hs rfl members ![6,4,4] ![73,48,48]
      (by decide) (by decide) (by decide) (by decide)

/-- At h=5, b=24, each independent component carries at most seven
marks per relation. Six relations therefore carry at most 42 of the 43 marks. -/
theorem obstructed_packing {C : ℕ} (rel marks : Fin C → ℕ)
    (q : (∑ i,rel i)=6)
    (parts : ∀ i, ∃ e : Fin 5→ℕ, (∑ j,e j)=marks i ∧ ∀ j,
      let g := if j.val<4 then 4 else 3
      e j≤2*g+1 ∧ marks i-e j≤rel i*(g+2)) :
    (∑ i,marks i) ≤ 42 := by
  have bound (i) : marks i≤7*rel i := by
    obtain ⟨_,width,ratio,_⟩ := (component_marks_iff (h:=5) (d:=4) (s:=4)
      (u:=rel i) (M:=marks i) (by decide) (by decide) (by decide)).mp (parts i)
    norm_num at width ratio
    by_cases small : rel i≤3
    · interval_cases v : rel i <;> omega
    · omega
  have sum := Finset.sum_le_sum (s:=Finset.univ) fun i _ => bound i
  rwa [← Finset.mul_sum,q] at sum

end CriticalThreeCubic

namespace CriticalThreeCubic

/-- Additional relations can be distributed among the existing marks. -/
theorem increase_relations {h r q₀ q : ℕ} (g : Fin h → ℕ) (more : q₀≤q) (limit : q≤r) :
    let packed (k : ℕ) := ∃ G : ℕ, ∃ rel marks : Fin G → ℕ,
      (∑ i,rel i)=k ∧ (∑ i,marks i)=r ∧ ∀ i, 0<rel i ∧ rel i≤ marks i ∧
        ∃ e : Fin h→ℕ, (∑ j,e j)=marks i ∧ ∀ j, e j≤2*g j+1 ∧ marks i-e j≤rel i*(g j+2)
    packed q₀ → packed q := by
  rintro packed ⟨G,u,M,t,tot,hit⟩
  obtain ⟨v,eq,fit⟩ := distribute u M (fun i => (hit i).2.1) (t.le.trans more)
    (limit.trans tot.ge)
  refine ⟨G,v,M,eq,tot,?_⟩
  intro i
  obtain ⟨pos,_,e,num,good⟩ := hit i
  exact ⟨pos.trans_le (fit i).1,(fit i).2,e,num,fun j => ⟨(good j).1,
    (good j).2.trans (Nat.mul_le_mul_right _ (fit i).1)⟩⟩

private theorem two_component_cutoff {h d s b r q : ℕ} (hd : 2≤d) (hs : s<h)
    (height : h=d+2) (high : d≤ s+1) (base : b=h*d+s) (points : r=2*b-h)
    (members : q≤r) (budget : (h-1)*r≤q*(b+h)) :
    let g (i : Fin h) := if i.val<s then d else d-1
    ∃ G : ℕ, ∃ rel marks : Fin G → ℕ, (∑ i,rel i)=q ∧ (∑ i,marks i)=r ∧
      ∀ i, 0<rel i ∧ rel i≤ marks i ∧ ∃ e : Fin h→ℕ,
        (∑ j,e j)=marks i ∧ ∀ j, e j≤2*g j+1 ∧ marks i-e j≤rel i*(g j+2) := by
  intro g
  subst h
  have den : d+2-1=d+1 := by omega
  rw [den] at budget
  have hdim : d+2≤b := by
    rw [base]
    nlinarith only [Nat.mul_le_mul_left (d+2) hd,Nat.zero_le s]
  have rk : r+(d+2)=2*b := by rw [points,Nat.sub_add_cancel (by omega)]
  have weighted := congrArg (fun k : ℕ => d*k) rk
  have rels : 2*d≤q := by
    by_contra! small
    have bad := Nat.mul_le_mul_right (b+(d+2)) (show q+1≤2*d by omega)
    nlinarith only [bad,budget,rk,weighted,base,show 0<s by omega]
  let K := b-2
  have Kval : K+2=b := by dsimp [K]; omega
  have covered : r≤2*K := by omega
  have Ksize : d≤K := by omega
  have Kr : K≤r := by omega
  have width : K≤d*(d+1)+2*d-1 := by
    have pos : K+1≤d*(d+1)+2*d := by nlinarith only [Kval,base,hs]
    omega
  have rate : (d+2-1)*K≤d*(b+(d+2)) := by
    rw [den]
    have z := congrArg (fun t : ℕ => d*t) Kval
    nlinarith only [z,Kval,base,hs,hd]
  have sum : d+2-s=1 ∨ d+2-s=2 ∨ d+2-s=3 := by omega
  have convex : 3*d≤d*d+2 := by
    obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hd
    nlinarith only [Nat.zero_le t,Nat.zero_le (t*t)]
  have short : (d+2-s-1)*K≤d*(d+2-s)*(d+1) := by
    rcases sum with t|t|t <;> rw [t] <;> norm_num <;> nlinarith only [Kval,base,hs,hd,convex]
  apply increase_relations g rels members
  apply realize_caps (by omega) hd hs (by simpa only [←base] using points) (rels.trans members)
    (C:=2) (fun _ => d) (fun _ => K) (by simp) (by simpa using covered)
    (fun _ => ⟨by omega,Ksize⟩)
  intro _
  rw [←base]
  exact ⟨Kr,width,rate,short⟩

/-- The dimension budget is sufficient for every width with d≥h−2,
apart from the explicitly obstructed balanced-hub case. -/
theorem threshold_packing {h d s b r q : ℕ} (hh : 2≤h) (hd : 2≤d) (hs : s<h)
    (base : b=h*d+s) (points : r=2*b-h) (members : q≤r) (budget : (h-1)*r≤q*(b+h))
    (range : h≤d+2) (exception : ¬(h=5 ∧ d=4 ∧ s=4 ∧ q=6)) :
    let g (i : Fin h) := if i.val<s then d else d-1
    ∃ G : ℕ, ∃ rel marks : Fin G → ℕ, (∑ i,rel i)=q ∧ (∑ i,marks i)=r ∧
      ∀ i, 0<rel i ∧ rel i≤ marks i ∧ ∃ e : Fin h→ℕ,
        (∑ j,e j)=marks i ∧ ∀ j, e j≤2*g j+1 ∧ marks i-e j≤rel i*(g j+2) := by
  by_cases higher : h≤d+1
  · exact component_packing hh hd hs base points members budget higher exception
  by_cases slope : s+2≤d
  · exact component_packing_of_slopes hh hd hs base points members budget (by omega) slope
  exact two_component_cutoff hd hs (by omega) (by omega) base points members budget

/-- Direct form for a third dimension at or below its clipped endpoint.
The natural threshold b≥h(h−2) applies to every residue class. -/
theorem endpoint_packing {h b r N : ℕ} (hh : 2≤h) (order : 2*h≤b)
    (wide : h*(h-2)≤b) (points : r=2*b-h) (endSize : N≤r*(b+1)/(b+h))
    (exception : ¬(h=5 ∧ b=24 ∧ N=37)) :
    let g (i : Fin h) := if i.val<b%h then b/h else b/h-1
    ∃ G : ℕ, ∃ rel marks : Fin G → ℕ, (∑ i,rel i)=r-N ∧ (∑ i,marks i)=r ∧
      ∀ i, 0<rel i ∧ rel i≤ marks i ∧ ∃ e : Fin h→ℕ,
        (∑ j,e j)=marks i ∧ ∀ j, e j≤2*g j+1 ∧ marks i-e j≤rel i*(g j+2) := by
  have pos : 0<h := by omega
  have base := (Nat.div_add_mod b h).symm
  have quotient : 2≤b/h := (Nat.le_div_iff_mul_le pos).mpr order
  have height : h-2≤b/h := (Nat.le_div_iff_mul_le pos).mpr (by simpa [Nat.mul_comm] using wide)
  have den : 0<b+h := by omega
  have count := (Nat.le_div_iff_mul_le den).mp endSize
  have nr : N≤r := Nat.le_of_mul_le_mul_right
    (count.trans (Nat.mul_le_mul_left r (show b+1≤b+h by omega))) den
  have qeq := congrArg (fun k : ℕ => k*(b+h)) (Nat.sub_add_cancel nr)
  have heq := congrArg (fun k : ℕ => k*r) (Nat.sub_add_cancel (show 1≤h by omega))
  have budget : (h-1)*r≤(r-N)*(b+h) := by nlinarith only [count,qeq,heq]
  apply threshold_packing hh quotient (Nat.mod_lt b pos) base points (Nat.sub_le _ _) budget
    (by omega)
  rintro ⟨hp,hd,hs,qn⟩
  rw [hd,hs,hp] at base
  norm_num at base
  exact exception ⟨hp,base,by rw [hp,base] at points; omega⟩

end CriticalThreeCubic

namespace CriticalThreeComponents

open Arxiv.«0805.3777»

/-- Each group of relations may use its own arrangement of paired physical
labels. The number of third coordinates for a group is its mark count
minus its relation count. After the common specialization those coordinates
exhaust the entire third factor. -/
theorem tangent_of_components {h b n r C : ℕ} (hb : h≤b) (hn : n≤r) (level : r+h=2*b)
    (rel marks : Fin C→ℕ) (rows : (∑ c,rel c)=r-n) (points : (∑ c,marks c)=r)
    (localCount : ∀ c,rel c ≤ marks c)
    (geometry : ∀ c,∃ g e : Fin h→ℕ, (∑ i,g i)=b-h ∧ (∑ i,e i)=marks c ∧
      ∀ i,e i ≤ 2*g i+1 ∧ marks c-e i ≤ rel c*(g i+2)) :
    ∃ X : Fin r→Fin 3→ℂ, ∃ Y : Fin r→Fin b→ℂ, ∃ Z : Fin r→Fin n→ℂ,
    ∀ T : Fin 3→Fin b→Fin n→ℂ, ∃ U : Fin r→Fin 3→ℂ, ∃ V : Fin r→Fin b→ℂ,
      ∃ W : Fin r→Fin n→ℂ, ∀ i j k,
        T i j k=∑ t,(U t i*(Y t j*Z t k)+X t i*(V t j*Z t k)+X t i*(Y t j*W t k)) := by
  let width (c : Fin C) := marks c-rel c
  have dimensions : (∑ c,width c)=n := by
    have total : (∑ c,width c)+(∑ c,rel c)=∑ c,marks c := by
      rw [←Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun c _ => Nat.sub_add_cancel (localCount c))
    rw [rows,points] at total
    omega
  rw [←dimensions]
  apply CriticalHigher.Blocks.different_block_tangent 3 b C r width marks points.le
  intro c
  obtain ⟨g,e,gSize,eSize,assign⟩ := geometry c
  have hit := CriticalThreeBatch.local_cubic_component (p:=b-h) (localCount c) g e
    gSize eSize (fun i => (assign i).1) (fun i => (assign i).2)
  dsimp only at hit
  rwa [Nat.sub_add_cancel hb,show 2*(b-h)+h=r by omega] at hit

/-- A component can be checked entirely by four integer inequalities;
the occupancy of each local hub is eliminated. -/
theorem rank_of_partition {h b n r C : ℕ} (hh : 2≤h) (hb : 3≤b) (order : b≤n) (hn : n≤r)
    (level : r+h=2*b) (decomp : 2*h≤b) (count : 3*b*n ⌈/⌉ (b+n+1)=r)
    (rel marks : Fin C→ℕ) (rows : (∑ c,rel c)=r-n) (points : (∑ c,marks c)=r)
    (each : ∀ c, let u := rel c; let M := marks c; let d := b/h; let s := b%h
      u ≤ M ∧ M ≤ r ∧ M ≤ u*(d+1)+2*d-1 ∧
        (h-1)*M ≤ u*(b+h) ∧ (h-s-1)*M ≤ u*(h-s)*(d+1)) :
    IsGenericRank [3,b,n] r := by
  let d := b/h
  let s := b%h
  have positive : 0<h := by omega
  have hd : 2≤d := (Nat.le_div_iff_mul_le positive).mpr decomp
  have hs : s<h := Nat.mod_lt _ positive
  have dim : h*d+s=b := Nat.div_add_mod b h
  let g (i : Fin h) := if i.val<s then d else d-1
  have gSize : (∑ i,g i)=b-h := by
    simpa only [dim] using (CriticalThreeCubic.hub_totals hs.le (by omega : 1≤d)).1
  refine CriticalLastSlice.TwoPlanes.generic_rank_of_witness (by decide) hb order ?_ ?_
  · rw [show 3+b+n-2=b+n+1 by omega]
    exact count.symm
  · apply tangent_of_components (by omega : h≤b) hn level rel marks rows points (fun c => (each c).1)
    intro c
    obtain ⟨_,bound,block,all,small⟩ := each c
    obtain ⟨e,tot,fit⟩ := (CriticalThreeCubic.component_marks_iff (M:=marks c) (u:=rel c) hh
      (by omega : 1≤d) hs).mpr (by
        rw [dim,show 2*b-h=r by omega]
        exact ⟨bound,block,all,small⟩)
    exact ⟨g,e,gSize,tot,fit⟩

end CriticalThreeComponents

namespace CriticalThreeComponents

open Arxiv.«0805.3777»

theorem component_length_bound {b n r h : ℕ} (hh : 2≤h) (level : r+h=2*b)
    (count : 3*b*n ⌈/⌉ (b+n+1)=r) :
    n ≤ r*(b+1)/(b+h) ∧ n ≤ r := by
  have mass := (ceilDiv_le_iff_le_mul (by omega : 0<b+n+1)).mp count.le
  have product := congrArg (fun t : ℕ => t*n) level
  have weighted : n*(b+h) ≤ r*(b+1) := by nlinarith only [mass,product]
  have pos : 0<b+h := by omega
  refine ⟨(Nat.le_div_iff_mul_le pos).mpr weighted, ?_⟩
  exact Nat.le_of_mul_le_mul_right
    (weighted.trans (Nat.mul_le_mul_left r (show b+1≤b+h by omega))) pos

/-- For all rank levels at once, the parameter count suffices from
width h(h−2) on. The one marked-allocation exception at 3×24×37 has an
independent finite certificate. -/
theorem rank_above_threshold {h b n r : ℕ} (hh : 2≤h) (ordered : b≤n) (minWidth : 2*h≤b)
    (wide : h*(h-2)≤b) (level : r+h=2*b)
    (count : 3*b*n ⌈/⌉ (b+n+1)=r) (except : ¬(h=5 ∧ b=24 ∧ n=37)) :
    IsGenericRank [3,b,n] r := by
  have positive : 0<h := by omega
  have dpos : 2≤b/h := (Nat.le_div_iff_mul_le positive).mpr minWidth
  have rem := Nat.mod_lt b positive
  have dim := Nat.div_add_mod b h
  have total := (CriticalThreeCubic.hub_totals rem.le (by omega : 1≤b/h)).1
  rw [dim] at total
  obtain ⟨clip,nr⟩ := component_length_bound hh level count
  obtain ⟨C,u,M,rows,marks,fit⟩ :=
    CriticalThreeCubic.endpoint_packing hh minWidth wide (by omega : r=2*b-h) clip except
  refine CriticalLastSlice.TwoPlanes.generic_rank_of_witness (by decide) (by omega) ordered ?_ ?_
  · simpa only [show 3+b+n-2=b+n+1 by omega] using count.symm
  · apply tangent_of_components (by omega : h≤b) nr level u M rows marks (fun c => (fit c).2.1)
    intro c
    obtain ⟨e,sum,localFit⟩ := (fit c).2.2
    exact ⟨_,e,total,sum,localFit⟩

end CriticalThreeComponents

namespace CriticalThreeComponents

open Arxiv.«0805.3777»

private theorem sixth_partition {b n C : ℕ} (u M : Fin C→ℕ) (ok :
    let r := 2*b-6
    let d := b/6
    let s := b%6
    12≤b ∧ b≤n ∧ n≤r ∧ 3*b*n ⌈/⌉ (b+n+1)=r ∧ (∑ c,u c)=r-n ∧ (∑ c,M c)=r ∧
    ∀ c, u c ≤ M c ∧ M c ≤ r ∧ M c ≤ u c*(d+1)+2*d-1 ∧
      5*M c ≤ u c*(b+6) ∧ (6-s-1)*M c ≤ u c*(6-s)*(d+1)) :
    IsGenericRank [3,b,n] (2*b-6) := by
  obtain ⟨width,order,third,count,rows,marks,each⟩ := ok
  exact rank_of_partition (h:=6) (by decide) (by omega) order third (by omega) width
    count u M rows marks each

set_option maxRecDepth 8192 in

private theorem sixth_small_cases (b n : ℕ) (hb : 3≤b) (order : b≤n) (small : b<24)
    (nr : n≤2*b-6) (exc : ¬(b=11 ∧ n=11))
    (count : 3*b*n ⌈/⌉ (b+n+1)=2*b-6) : (b,n) ∈ [(12,12),(12,13),(13,14),(14,16),(15,17),(15,18),(16,19),(16,20),(17,21),(18,23),(19,24),(19,25),(20,26),(20,27),(21,28),(21,29),(22,30),(22,31),(23,32),(23,33)] := by
  have finite : ∀ B : Fin 24, ∀ N : Fin 41, 3≤B.val → B.val≤N.val →
      ¬(B.val=11 ∧ N.val=11) → 3*B.val*N.val ⌈/⌉ (B.val+N.val+1)=2*B.val-6 →
      (B.val,N.val) ∈ [(12,12),(12,13),(13,14),(14,16),(15,17),(15,18),(16,19),(16,20),(17,21),(18,23),(19,24),(19,25),(20,26),(20,27),(21,28),(21,29),(22,30),(22,31),(23,32),(23,33)] := by decide
  exact finite ⟨b,small⟩ ⟨n,by omega⟩ hb order exc count

/-- The entire sixth rank level follows from its two exceptional finite
tangents. Every other shape is handled by the analytic component proof. -/
theorem sixth_rank_of_two_seeds
    (at16 : IsGenericRank [3,16,20] 26) (at23 : IsGenericRank [3,23,33] 40)
    {b n : ℕ} (hb : 3≤b) (ord : b≤n) (exc : ¬(b=11 ∧ n=11))
    (count : 3*b*n ⌈/⌉ (b+n+1)=2*b-6) : IsGenericRank [3,b,n] (2*b-6) := by
  have level : 2*b-6+6=2*b := by omega
  by_cases wide : 24≤b
  · exact rank_above_threshold (h:=6) (by decide) ord (by omega) wide level count (by omega)
  have nr := (component_length_bound (h:=6) (by decide) level count).2
  have mem := sixth_small_cases b n hb ord (by omega) nr exc count
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at mem
  rcases mem with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact sixth_partition (C:=2) ![5,1] ![17,1] (by decide)
  · exact sixth_partition (C:=1) ![5] ![18] (by decide)
  · exact sixth_partition (C:=2) ![4,2] ![15,5] (by decide)
  · exact sixth_partition (C:=2) ![3,3] ![12,10] (by decide)
  · exact sixth_partition (C:=3) ![3,3,1] ![12,11,1] (by decide)
  · exact sixth_partition (C:=2) ![3,3] ![12,12] (by decide)
  · exact sixth_partition (C:=3) ![3,3,1] ![12,12,2] (by decide)
  · exact at16
  · exact sixth_partition (C:=4) ![2,2,2,1] ![9,9,9,1] (by decide)
  · exact sixth_partition (C:=2) ![5,2] ![24,6] (by decide)
  · exact sixth_partition (C:=2) ![5,3] ![25,7] (by decide)
  · exact sixth_partition (C:=2) ![5,2] ![25,7] (by decide)
  · exact sixth_partition (C:=2) ![5,3] ![25,9] (by decide)
  · exact sixth_partition (C:=2) ![5,2] ![25,9] (by decide)
  · exact sixth_partition (C:=2) ![4,4] ![21,15] (by decide)
  · exact sixth_partition (C:=2) ![4,3] ![21,15] (by decide)
  · exact sixth_partition (C:=4) ![2,2,2,2] ![11,11,11,5] (by decide)
  · exact sixth_partition (C:=3) ![3,2,2] ![16,11,11] (by decide)
  · exact sixth_partition (C:=3) ![3,3,2] ![17,17,6] (by decide)
  · exact at23

end CriticalThreeComponents

namespace CriticalHigher.CauchyPulses

open Polynomial

/-- A Cauchy matrix with distinct row nodes, distinct column poles and at
least as many rows as columns has trivial kernel. -/
theorem cauchy_separates {K J L : Type*} [Field K] [Fintype J] [Fintype L]
    (row : J → K) (col : L → K) (row_inj : Function.Injective row) (col_inj : Function.Injective col)
    (disjoint : ∀ j l, row j ≠ col l) (room : Fintype.card L ≤ Fintype.card J)
    (f : L → K) (zero : ∀ j, (∑ l, f l/(row j-col l))=0) : f=0 := by
  classical
  funext p
  have positive : 0 < Fintype.card L := Fintype.card_pos_iff.mpr ⟨p⟩
  let Q (l : L) : K[X] := ∏ k ∈ Finset.univ.erase l, (X-C (col k))
  let N : K[X] := ∑ l, C (f l)*Q l
  have degree : N.natDegree ≤ Fintype.card L-1 := by
    apply natDegree_sum_le_of_forall_le
    intro l _
    apply (natDegree_C_mul_le _ _).trans
    change (∏ k ∈ Finset.univ.erase l, (X-C (col k))).natDegree ≤ _
    rw [natDegree_finsetProd_X_sub_C_eq_card, Finset.card_erase_of_mem (Finset.mem_univ l),Finset.card_univ]
  have evaluate (t : K) : N.eval t = ∑ l, f l*∏ k ∈ Finset.univ.erase l, (t-col k) := by
    simp only [N,Q,eval_finsetSum,eval_mul,eval_C,eval_prod,eval_sub,eval_X]
  have roots (j : J) : N.eval (row j)=0 := by
    rw [evaluate]
    calc
      _ = (∑ l, f l/(row j-col l))*(∏ k, (row j-col k)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l _
        let P := ∏ k ∈ Finset.univ.erase l, (row j-col k)
        have factor : P*(row j-col l) = ∏ k, (row j-col k) :=
          Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ l)
        rw [← factor]
        change f l*P=(f l/(row j-col l))*(P*(row j-col l))
        calc
          _ = (f l/(row j-col l)*(row j-col l))*P := by rw [div_mul_cancel₀ _ (sub_ne_zero.mpr (disjoint j l))]
          _ = _ := by ring
      _ = 0 := by rw [zero,zero_mul]
  have ident := eq_zero_of_natDegree_lt_card_of_eval_eq_zero N row_inj roots (by omega)
  have pole := congrArg (Polynomial.eval (col p)) ident
  rw [evaluate,eval_zero,Finset.sum_eq_single p] at pole
  · have product : (∏ k ∈ Finset.univ.erase p, (col p-col k)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro k hk
      exact sub_ne_zero.mpr (fun eq => Finset.ne_of_mem_erase hk (col_inj eq).symm)
    exact (mul_eq_zero.mp pole).resolve_right product
  · intro l _ hl
    have mem : p ∈ Finset.univ.erase l := Finset.mem_erase.mpr ⟨Ne.symm hl,Finset.mem_univ p⟩
    rw [Finset.prod_eq_zero mem (sub_self (col p)),mul_zero]
  · simp

end CriticalHigher.CauchyPulses

namespace CriticalThreeCubic

/-- Immediately below the quadratic cutoff, the actual endpoint has
three spare scalar equations and its predicted rank is 2b−h. -/
theorem preceding_endpoint (d : ℕ) (hd : 2≤d) :
    let h := d+3
    let b := h*d+(d+2)
    let r := 2*b-h
    let q := 2*d+1
    let N := r-q
    b+1=h*(h-2) ∧ (h-1)*r+3=q*(b+h) ∧ N=r*(b+1)/(b+h) ∧
      3*b*N ⌈/⌉ (b+N+1)=r := by
  intro h b r q N
  have hp : h=d+3 := rfl
  have bp : b=d*d+4*d+2 := by dsimp [b,h]; ring
  have rp : r=2*(d*d)+7*d+1 := by dsimp [r]; rw [bp,hp]; omega
  have np : N=2*(d*d)+5*d := by dsimp [N,q]; rw [rp]; omega
  have qp : q=2*d+1 := rfl
  have div : r*(b+1)=3+N*(b+h) := by rw [rp,bp,np,hp]; ring
  have raw : b+N+1>3 := by omega
  have den : b+h>3 := by omega
  have span : (b+N+1)*r=3*b*N+3 := by rw [bp,np,rp]; ring
  refine ⟨?_,?_,?_,le_antisymm ?_ ?_⟩
  · rw [hp,bp,show d+3-2=d+1 by omega]
    ring
  · rw [hp,bp,rp,qp,show d+3-1=d+2 by omega]
    ring
  · rw [div,Nat.add_mul_div_right _ _ (by omega : 0<b+h),Nat.div_eq_of_lt den]
    omega
  · exact (ceilDiv_le_iff_le_mul (by omega : 0<b+N+1)).mpr (by omega)
  · by_contra! small
    have inc := Nat.mul_le_mul_left (b+N+1) (show (3*b*N ⌈/⌉ (b+N+1))+1≤r by omega)
    have cover := (ceilDiv_le_iff_le_mul (by omega : 0<b+N+1)).mp
      (le_refl (3*b*N ⌈/⌉ (b+N+1)))
    nlinarith only [span,inc,cover,raw]

end CriticalThreeCubic

namespace CriticalConic

open Arxiv.«0805.3777»

/-- At the width immediately below the quadratic cutoff, the balanced cubic
block fills the first set of marks. A conic block at the remaining marks
therefore settles the exact generic rank at the endpoint. -/
lemma boundary_rank_of_local (h : ℕ) (hh : 5 ≤ h) :
    let b := h*(h-2)-1
    let r := 2*b-h
    let N := r-(2*h-5)
    (∃ x : Fin b → Fin 3 → ℂ, ∃ y : Fin b → Fin b → ℂ, ∃ z : Fin b → Fin (b-(h-2)) → ℂ,
      ∃ x' : Fin (b-h) → Fin 3 → ℂ, ∃ y' : Fin (b-h) → Fin b → ℂ,
      ∀ T : Fin 3 → Fin b → Fin (b-(h-2)) → ℂ,
        ∃ U : Fin b → Fin 3 → ℂ, ∃ V : Fin b → Fin b → ℂ,
        ∃ W : Fin b → Fin (b-(h-2)) → ℂ, ∃ W' : Fin (b-h) → Fin (b-(h-2)) → ℂ, ∀ i j k,
          T i j k=(∑ t, (U t i*(y t j*z t k)+x t i*(V t j*z t k)+x t i*(y t j*W t k))) +
            ∑ t, x' t i*(y' t j*W' t k)) → IsGenericRank [3,b,N] r := by
  classical
  obtain ⟨d,rfl⟩ : ∃ d, h=d+3 := ⟨h-3,by omega⟩
  intro b r N conic
  let h := d+3
  let s := d+2
  let p := b-h
  have hd : 2≤d := by omega
  have hs : s<h := by dsimp only [s,h]; omega
  have endpoint := CriticalThreeCubic.preceding_endpoint d hd
  have fitWidth : h*d+s=b := by
    have eq := endpoint.1
    change h*d+s+1=h*(h-2) at eq
    change h*d+s=h*(h-2)-1
    omega
  have bp : b = d*d+4*d+2 := by rw [←fitWidth]; dsimp only [h,s]; ring
  have pp : p+1 = d*d+3*d := by dsimp only [p,h]; rw [bp]; omega
  have rp : r = 2*(d*d)+7*d+1 := by change 2*b-(d+3)=_; rw [bp]; omega
  have np : N = 2*(d*d)+5*d := by change r-(2*(d+3)-5)=_; rw [rp]; omega
  have short : h-s-1=0 := by dsimp only [h,s]; omega
  let g (i : Fin h) := if i.val<s then d else d-1
  have gSize : (∑ i, g i)=p := by
    simpa only [g,p,fitWidth] using (CriticalThreeCubic.hub_totals hs.le (by omega : 1≤d)).1
  have cap : p≤d*(d+1)+2*d-1 := by rw [show d*(d+1)=d*d+d by ring]; omega
  have total : (h-1)*p+2=d*(b+h) := by
    have eq := congrArg (fun x : ℕ => (d+2)*x) pp
    rw [show h-1=d+2 by dsimp only [h]; omega,bp]
    dsimp only [h]
    nlinarith only [eq]
  obtain ⟨take,takeSize,bounds⟩ := (CriticalThreeCubic.component_marks_iff (h:=h) (d:=d)
    (s:=s) (u:=d) (M:=p) (by dsimp only [h]; omega) (by omega) hs).mpr (by
      rw [fitWidth,short,Nat.zero_mul]
      refine ⟨?_,cap,by omega,Nat.zero_le _⟩
      dsimp only [h]; omega)
  have cubic := CriticalThreeBatch.local_cubic_component (p:=p) (m:=p) (u:=d) (by omega) g take
    gSize takeSize (fun i => (bounds i).1) (fun i => (bounds i).2)
  dsimp only at cubic
  rw [show p+h=b by dsimp only [h]; omega,show 2*p+h=r by dsimp only [h]; omega] at cubic
  have count : 3*b*N ⌈/⌉ (b+N+1)=r := by
    have he := endpoint.2.2.2
    change 3*(h*d+s)*(2*(h*d+s)-h-(2*d+1)) ⌈/⌉
      ((h*d+s)+(2*(h*d+s)-h-(2*d+1))+1) = 2*(h*d+s)-h at he
    rw [fitWidth] at he
    have gap : 2*h-5=2*d+1 := by dsimp only [h]; omega
    change 3*b*(r-(2*h-5)) ⌈/⌉ (b+(r-(2*h-5))+1)=r
    rw [gap]
    exact he
  refine CriticalLastSlice.TwoPlanes.generic_rank_of_witness (by decide) (by omega) (by omega) ?_ ?_
  · simpa only [show 3+b+N-2=b+N+1 by omega] using count.symm
  · let width : Fin 2 → ℕ := ![p-d,b-(h-2)]
    let marks : Fin 2 → ℕ := ![p,b]
    have dimensions : (∑ q, width q)=N := by
      rw [Fin.sum_univ_two]
      change p-d+(b-(h-2))=N
      dsimp only [h]; omega
    have points : (∑ q, marks q)≤r := by rw [Fin.sum_univ_two]; change p+b≤r; omega
    rw [←dimensions]
    apply CriticalHigher.Blocks.different_block_tangent 3 b 2 r width marks points
    intro q
    fin_cases q
    · exact cubic
    · rw [show b-(d+3)=r-b by omega] at conic
      exact conic

end CriticalConic

namespace CriticalConic

/-- A basis of the quotient by the column span gives exactly its defining
exterior linear equations. -/
lemma exterior_rows {K : Type*} [Field K] {b h : ℕ}
    (L : Matrix (Fin b) (Fin h) K) (inject : Function.Injective L.mulVec) :
    ∃ P : Matrix (Fin (b-h)) (Fin b) K, ∀ v : Fin b → K,
      P.mulVec v=0 ↔ ∃ w : Fin h → K, L.mulVec w=v := by
  classical
  let W := LinearMap.range L.mulVecLin
  have dimW : Module.finrank K W=h := by
    simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using
      LinearMap.finrank_range_of_inj (f:=L.mulVecLin) inject
  have dimQ : Module.finrank K ((Fin b→K) ⧸ W)=b-h := by
    have total := W.finrank_quotient_add_finrank
    rw [dimW,Module.finrank_fintype_fun_eq_card,Fintype.card_fin] at total
    omega
  let coord := (Module.finBasisOfFinrankEq K ((Fin b→K) ⧸ W) dimQ).equivFun
  let π := coord.toLinearMap.comp W.mkQ
  refine ⟨LinearMap.toMatrix' π,fun v => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  change coord (W.mkQ v)=0 ↔ v∈W
  rw [← coord.map_zero,coord.injective.eq_iff]
  exact Submodule.Quotient.mk_eq_zero W

/-- Two distinct conic nodes determine the last row from the middle row.
The marked diagonals vanish by their own first-mode variations. -/
private lemma conic_normal_zero {K : Type*} [Field K] {b h u : ℕ}
    (t : Fin b → K) (distinct : Function.Injective t) (pole : ∀ i j, t i+t j≠0)
    (L : Matrix (Fin b) (Fin h) K) (inject : Function.Injective L.mulVec)
    (P : Matrix (Fin (b-h)) (Fin b) K)
    (cut : ∀ v : Fin b → K, P.mulVec v=0 ↔ ∃ w : Fin h → K, L.mulVec w=v)
    (Q : Matrix (Fin u) (Fin b) K)
    (test : ∀ f : Fin b → Fin h → K, (∀ i, L.mulVec (f i) i=0) →
      (∀ k l, (∑ i, Q k i*f i l)=0) →
      (∀ k j, (∑ i, Q k i*(L.mulVec (f i) j/(t i+t j)))=0) → f=0)
    (F : Fin b → Fin 3 × Fin b → K)
    (diag : ∀ i a, F i (a,i)=0)
    (sample : ∀ i j, F i (0,j)+t j*F i (1,j)+(t j)^2*F i (2,j)=0)
    (mark : ∀ i j, F i (0,j)+t i*F i (1,j)+(t i)^2*F i (2,j)=0)
    (exterior : ∀ i, P.mulVec (fun j => F i (1,j))=0)
    (coupled : ∀ k a j, (∑ i, Q k i*F i (a,j))=0) : F=0 := by
  classical
  choose f preimage using fun i => (cut _).mp (exterior i)
  have middle (i j : Fin b) : L.mulVec (f i) j=F i (1,j) := congrFun (preimage i) j
  have last (i j : Fin b) : F i (2,j)= -(L.mulVec (f i) j/(t i+t j)) := by
    rw [middle]
    by_cases eq : i=j
    · subst j
      simp only [diag,zero_div,neg_zero]
    · have prod : (t i-t j)*(F i (1,j)+(t i+t j)*F i (2,j))=0 := by
        linear_combination mark i j-sample i j
      have lin := (mul_eq_zero.mp prod).resolve_left (sub_ne_zero.mpr (distinct.ne eq))
      field_simp [pole i j]
      linear_combination lin
  have sumvec (k : Fin u) : (∑ i, Q k i • f i)=0 := by
    apply inject
    rw [Matrix.mulVec_zero]
    change L.mulVecLin (∑ i, Q k i • f i)=0
    rw [map_sum]
    funext j
    simpa only [Finset.sum_apply,map_smul,Pi.smul_apply,smul_eq_mul,Matrix.mulVecLin_apply,middle,Pi.zero_apply]
      using coupled k 1 j
  have hzero := test f (fun i => (middle i i).trans (diag i 1))
    (fun k l => by simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using congrFun (sumvec k) l)
    (fun k j => by simpa only [last,mul_neg,Finset.sum_neg_distrib,neg_eq_zero] using coupled k 2 j)
  have z₁ (i j : Fin b) : F i (1,j)=0 := by
    rw [← middle,hzero]
    exact congrFun (Matrix.mulVec_zero L) j
  have z₂ (i j : Fin b) : F i (2,j)=0 := by rw [last,middle,z₁,zero_div,neg_zero]
  funext i ⟨a,j⟩
  fin_cases a
  · change F i ((0 : Fin 3),j) = 0
    simpa only [z₁,z₂,mul_zero,add_zero] using mark i j
  · exact z₁ i j
  · exact z₂ i j

/-- Swap the contractions in a finite bilinear sum. -/
private lemma swap_sums {K J N : Type*} [Field K] [Fintype J] [Fintype N]
    (a : J → K) (v : N → K) (H : J → N → K) :
    (∑ j, a j*(∑ k, v k*H j k)) = ∑ k, v k*(∑ j, a j*H j k) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The marked vectors are the conic samples and their coordinate vectors.
The exterior first factors select only the middle slice. The exterior second
factors cut out the column span of the prescribed matrix `L`. -/
lemma fixed_component {K : Type*} [Field K] {b h u : ℕ}
    (t : Fin b → K) (distinct : Function.Injective t) (pole : ∀ i j, t i+t j≠0)
    (L : Matrix (Fin b) (Fin h) K) (inject : Function.Injective L.mulVec)
    (Q : Matrix (Fin u) (Fin b) K)
    (test : ∀ f : Fin b → Fin h → K, (∀ i, L.mulVec (f i) i=0) →
      (∀ k l, (∑ i, Q k i*f i l)=0) →
      (∀ k j, (∑ i, Q k i*(L.mulVec (f i) j/(t i+t j)))=0) → f=0) :
    let x (i : Fin b) : Fin 3 → K := ![1,t i,(t i)^2]
    let y (i : Fin b) : Fin b → K := Pi.single i 1
    let x' (_ : Fin (b-h)) : Fin 3 → K := ![0,1,0]
    ∃ P : Matrix (Fin (b-h)) (Fin b) K, (∀ v : Fin b → K,
      P.mulVec v=0 ↔ ∃ w : Fin h → K, L.mulVec w=v) ∧
    ∃ Z : Matrix (Fin b) (Fin (b-u)) K, Q*Z=0 ∧ Function.Injective Z.mulVec ∧
    ∀ T : Fin 3 → Fin b → Fin (b-u) → K,
      ∃ U : Fin b → Fin 3 → K, ∃ V : Fin b → Fin b → K,
      ∃ W : Fin b → Fin (b-u) → K, ∃ W' : Fin (b-h) → Fin (b-u) → K, ∀ i j k,
        T i j k=(∑ p, (U p i*(y p j*Z p k)+x p i*(V p j*Z p k)+x p i*(y p j*W p k))) +
          ∑ p, x' p i*(P p j*W' p k) := by
  classical
  intro x y x'
  obtain ⟨P,cut⟩ := exterior_rows L inject
  obtain ⟨Z,R,qZ,left⟩ := CriticalThreeQuotient.kernel_frame_finite (N:=Fin (b-u)) Q (by simp)
  have split (v : Fin (b-u) → K) : R.mulVec (Z.mulVec v)=v := by
    rw [Matrix.mulVec_mulVec,left,Matrix.one_mulVec]
  have frame : Function.Injective Z.mulVec := fun v w he =>
    (split v).symm.trans ((congrArg R.mulVec he).trans (split w))
  refine ⟨P,cut,Z,qZ,frame,HigherPencil.augmented_span_of_annihilator x y Z x' P ?_⟩
  intro H first second marked ext
  let F (i : Fin b) (aj : Fin 3 × Fin b) := ∑ k, Z i k*H aj.1 aj.2 k
  have diag (i : Fin b) (a : Fin 3) : F i (a,i)=0 := by
    simpa [F,y,Pi.single_apply,ite_mul,zero_mul] using first i a
  have markedH (j : Fin b) (k : Fin (b-u)) : (∑ a, x j a*H a j k)=0 := by
    simpa [y,Pi.single_apply,mul_ite,ite_mul,zero_mul] using marked j k
  have exteriorH (p : Fin (b-h)) (k : Fin (b-u)) : (∑ j, P p j*H 1 j k)=0 := by
    simpa [x',Fin.sum_univ_three,Matrix.cons_val_two] using ext p k
  have atSample (i j : Fin b) : (∑ a, x j a*F i (a,j))=0 := by
    change (∑ a, x j a*(∑ k, Z i k*H a j k))=0
    rw [swap_sums (x j) (Z i) (fun a k => H a j k)]
    simp [markedH]
  have atMark (i j : Fin b) : (∑ a, x i a*F i (a,j))=0 := by
    simpa only [F,Finset.mul_sum,mul_assoc] using second i j
  have exterior (i : Fin b) : P.mulVec (fun j => F i (1,j))=0 := by
    funext p
    change (∑ j, P p j*(∑ k, Z i k*H 1 j k))=0
    rw [swap_sums (P p) (Z i) (H 1)]
    simp [exteriorH]
  have coupled (q : Fin u) (a : Fin 3) (j : Fin b) : (∑ i, Q q i*F i (a,j))=0 := by
    have vanish (k : Fin (b-u)) : (∑ i, Q q i*Z i k)=0 := congrFun (congrFun qZ q) k
    calc
      _ = ∑ k, (∑ i, Q q i*Z i k)*H a j k := by
        simp only [F,Finset.mul_sum,Finset.sum_mul,mul_assoc]
        rw [Finset.sum_comm]
      _ = 0 := by simp [vanish]
  have zero := conic_normal_zero t distinct pole L inject P cut Q test F diag
    (fun i j => by simpa [x,Fin.sum_univ_three,Matrix.cons_val_two] using atSample i j)
    (fun i j => by simpa [x,Fin.sum_univ_three,Matrix.cons_val_two] using atMark i j) exterior coupled
  funext a j k
  apply congrFun (frame (a₁:=H a j) (a₂:=0) ?_) k
  rw [Matrix.mulVec_zero]
  funext i
  exact congrFun (congrFun zero i) (a,j)

/-- The grouped local witness used by the different-width block assembly. -/
lemma local_component {b h u : ℕ}
    (t : Fin b → ℂ) (distinct : Function.Injective t) (pole : ∀ i j, t i+t j≠0)
    (L : Matrix (Fin b) (Fin h) ℂ) (inject : Function.Injective L.mulVec)
    (Q : Matrix (Fin u) (Fin b) ℂ)
    (test : ∀ f : Fin b → Fin h → ℂ, (∀ i, L.mulVec (f i) i=0) →
      (∀ k l, (∑ i, Q k i*f i l)=0) →
      (∀ k j, (∑ i, Q k i*(L.mulVec (f i) j/(t i+t j)))=0) → f=0) :
    ∃ x : Fin b → Fin 3 → ℂ, ∃ y : Fin b → Fin b → ℂ, ∃ z : Fin b → Fin (b-u) → ℂ,
    ∃ x' : Fin (b-h) → Fin 3 → ℂ, ∃ y' : Fin (b-h) → Fin b → ℂ,
    ∀ T : Fin 3 → Fin b → Fin (b-u) → ℂ, ∃ U : Fin b → Fin 3 → ℂ, ∃ V : Fin b → Fin b → ℂ,
      ∃ W : Fin b → Fin (b-u) → ℂ, ∃ W' : Fin (b-h) → Fin (b-u) → ℂ, ∀ i j k,
        T i j k=(∑ p, (U p i*(y p j*z p k)+x p i*(V p j*z p k)+x p i*(y p j*W p k))) +
          ∑ p, x' p i*(y' p j*W' p k) := by
  obtain ⟨P,_,Z,_,_,span⟩ := fixed_component t distinct pole L inject Q test
  exact ⟨fun i => ![1,t i,(t i)^2], fun i => Pi.single i 1, Z, fun _ => ![0,1,0], P, span⟩

/-- The alternating geometric sum has the odd-power sum as its numerator. -/
theorem boundary_geometric {L : ℕ} (evenL : Even L) (x y : ℂ) :
    (x+y)*(∑ l : Fin (L+1), (-1 : ℂ)^l.val*x^(L-l.val)*y^l.val)=x^(L+1)+y^(L+1) := by
  rw [Fin.sum_univ_eq_sum_range (fun l : ℕ => (-1 : ℂ)^l*x^(L-l)*y^l)]
  have terms : (∑ l ∈ Finset.range (L+1), (-1 : ℂ)^l*x^(L-l)*y^l) =
      ∑ l ∈ Finset.range (L+1), (-y)^l*x^(L-l) := by
    apply Finset.sum_congr rfl
    intro l _
    rw [show -y=(-1 : ℂ)*y by ring,mul_pow]
    ring
  rw [terms]
  simpa only [Nat.add_sub_cancel,evenL.add_one.neg_pow,sub_neg_eq_add] using
    (Commute.all (-y) x).mul_neg_geom_sum₂ (L+1)

/-- At distinct roots of unity of odd order the geometric matrix is twice
a Cauchy matrix, so every square restriction of the stated form is nonsingular. -/
theorem boundary_root_specialization {L u : ℕ} (evenL : Even L) (room : u≤L+1) :
    ∃ z : Fin u → ℂ, Function.Injective z ∧ (∀ i,z i^(L+1)=1) ∧
      (Matrix.of (fun i j : Fin u => ∑ l : Fin (L+1), (-1 : ℂ)^l.val*z i^(L-l.val)*z j^l.val)).det≠0 := by
  let key := (Fin.castLEEmb room).trans (ZMod.finEquiv (L+1)).toEquiv.toEmbedding
  let z (i : Fin u) := ZMod.stdAddChar (key i)
  have injective : Function.Injective z := ZMod.injective_stdAddChar.comp key.injective
  have unity (i : Fin u) : z i^(L+1)=1 := by
    change ZMod.stdAddChar (key i)^(L+1)=1
    rw [← AddChar.map_nsmul_eq_pow,nsmul_eq_mul,ZMod.natCast_self,zero_mul,AddChar.map_zero_eq_one]
  have opposite (i j : Fin u) : z i≠ -z j := by
    intro eq
    have h := congrArg (fun t : ℂ => t^(L+1)) eq
    change z i^(L+1)=(-z j)^(L+1) at h
    rw [evenL.add_one.neg_pow,unity,unity] at h
    norm_num at h
  let G := Matrix.of (fun i j : Fin u => ∑ l : Fin (L+1), (-1 : ℂ)^l.val*z i^(L-l.val)*z j^l.val)
  have evalG (i j : Fin u) : G i j=2/(z i+z j) := by
    have nonzero : z i+z j≠0 := fun h => opposite i j (eq_neg_of_add_eq_zero_left h)
    apply (eq_div_iff nonzero).mpr
    rw [mul_comm]
    have e := boundary_geometric evenL (z i) (z j)
    rw [unity,unity] at e
    exact e.trans (by norm_num)
  have null (f : Fin u → ℂ) (zero : G.mulVec f=0) : f=0 := by
    apply CriticalHigher.CauchyPulses.cauchy_separates z (fun j => -z j) injective
      (neg_injective.comp injective) opposite le_rfl f
    intro i
    have eq := congrFun zero i
    change (∑ j,G i j*f j)=0 at eq
    have half : (∑ j,G i j*f j) = 2*(∑ j,f j/(z i-(-z j))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [evalG,sub_neg_eq_add]
      ring
    rw [half] at eq
    exact (mul_eq_zero.mp eq).resolve_left two_ne_zero
  have rank : Function.Injective G.mulVec := by
    intro f g eq
    apply sub_eq_zero.mp
    apply null
    rw [Matrix.mulVec_sub,eq,sub_self]
  exact ⟨z,injective,unity,((Matrix.isUnit_iff_isUnit_det G).mp (Matrix.mulVec_injective_iff_isUnit.mp rank)).ne_zero⟩

end CriticalConic

namespace CriticalConic

open MvPolynomial

/-- The determinant is also nonzero at some list of distinct, positive
integer nodes. Their positive powers are automatically distinct. -/
theorem boundary_positive_nodes {L u : ℕ} (evenL : Even L) (room : u≤L+1) :
    ∃ s : Fin u → ℕ, (∀ i,0<s i) ∧ Function.Injective s ∧
      (Matrix.of (fun i j : Fin u => ∑ l : Fin (L+1), (-1 : ℂ)^l.val*(s i : ℂ)^(L-l.val)*(s j : ℂ)^l.val)).det≠0 := by
  classical
  let R := MvPolynomial (Fin u) ℂ
  let M : Matrix (Fin u) (Fin u) R := Matrix.of (fun i j => ∑ l : Fin (L+1), (-1 : R)^l.val*X i^(L-l.val)*X j^l.val)
  have specialize (x : Fin u → ℂ) : eval x M.det =
      (Matrix.of (fun i j : Fin u => ∑ l : Fin (L+1), (-1 : ℂ)^l.val*x i^(L-l.val)*x j^l.val)).det := by
    rw [RingHom.map_det,RingHom.mapMatrix_apply]
    congr 1
    ext i j
    change eval x (∑ l : Fin (L+1), (-1 : R)^l.val*X i^(L-l.val)*X j^l.val)=_
    simp only [map_sum,map_mul,map_pow,map_neg,map_one,eval_X,Matrix.of_apply]
  obtain ⟨z,_,_,det⟩ := boundary_root_specialization (u:=u) evenL room
  have nonzero : M.det≠0 := fun h => det (by rw [← specialize z,h,map_zero])
  let P := {a : Fin u × Fin u // a.1≠a.2}
  let V : R := ∏ a : P, (X a.val.1-X a.val.2)
  have differences : V≠0 := Finset.prod_ne_zero_iff.mpr fun a _ =>
    sub_ne_zero.mpr (fun h => a.property (MvPolynomial.X_injective h))
  let positive (n : ℕ) : ℂ := ((n+1 : ℕ) : ℂ)
  have inj : Function.Injective positive := by
    intro a b e
    have eq : a+1=b+1 := by exact_mod_cast (show ((a+1 : ℕ) : ℂ)=((b+1 : ℕ) : ℂ) from e)
    omega
  let S := fun _ : Fin u => Set.range positive
  have large (i : Fin u) : (S i).Infinite := Set.infinite_range_of_injective inj
  obtain ⟨x,inside,good⟩ : ∃ x ∈ Set.pi Set.univ S, eval x (M.det*V)≠0 := by
    by_contra! vanish
    exact (mul_ne_zero nonzero differences) (MvPolynomial.funext_set S large (fun x hx => by rw [vanish x hx,map_zero]))
  choose n hn using fun i => inside i (Set.mem_univ i)
  let s (i : Fin u) := n i+1
  have node (i : Fin u) : (s i : ℂ)=x i := hn i
  rw [map_mul] at good
  obtain ⟨rank,ds⟩ := mul_ne_zero_iff.mp good
  have sinj : Function.Injective s := by
    intro i j eq
    by_contra ne
    simp only [V,map_prod,map_sub,eval_X] at ds
    have sep := Finset.prod_ne_zero_iff.mp ds (⟨(i,j),ne⟩ : P) (Finset.mem_univ _)
    exact sep (sub_eq_zero.mpr ((node i).symm.trans ((congrArg (fun a : ℕ => (a : ℂ)) eq).trans (node j))))
  refine ⟨s,fun i => Nat.succ_pos _,sinj,?_⟩
  simpa only [node] using (specialize x ▸ rank)

theorem boundary_nodes {L u : ℕ} (positive : 0<L) (evenL : Even L) (room : u≤L+1) :
    ∃ x : Fin u → ℂ, (∀ i,x i≠0) ∧ Function.Injective (fun i => x i^L) ∧
      Function.Injective (fun i => x i^(L+1)) ∧
      (Matrix.of (fun i j : Fin u => ∑ l : Fin (L+1), (-1 : ℂ)^l.val*x i^(L-l.val)*x j^l.val)).det≠0 := by
  obtain ⟨s,nonzero,inj,det⟩ := boundary_positive_nodes evenL room
  have powers (n : ℕ) (hn : 0<n) : Function.Injective (fun i => (s i : ℂ)^n) := by
    intro i j eq
    apply inj
    apply Nat.pow_left_injective hn.ne'
    exact_mod_cast (show (s i : ℂ)^n=(s j : ℂ)^n from eq)
  exact ⟨fun i => (s i : ℂ),fun i => Nat.cast_ne_zero.mpr (nonzero i).ne',powers L positive,powers (L+1) (by omega),det⟩

end CriticalConic

namespace CriticalThreeConic

/-- A zero sum of the weights supplies the coefficient at index −1.
The two rectangular power matrices combine into the alternating kernel. -/
theorem moment_factorization {L u : ℕ} (x w : Fin u → ℂ) (zero : (∑ i,w i)=0) :
    let d (j : ℕ) := ∑ i,w i*x i^(j+1)
    let V := Matrix.vandermonde (fun i => x i^L)
    let W := Matrix.vandermonde (fun i => x i^(L+1))
    let K := Matrix.of (fun i j : Fin u => ∑ l : Fin (L+1),
      (-1:ℂ)^l.val*x i^(L-l.val)*x j^l.val)
    Matrix.of (fun s k : Fin u => ∑ l : Fin (L+1),
      (-1:ℂ)^l.val*d ((L+1)*k.val+l.val)*
        (if l.val<L*(s.val+1) then d (L*(s.val+1)-(l.val+1)) else 0)) =
      (V.transpose * Matrix.diagonal w) * K * (Matrix.diagonal (fun i => w i*x i) * W) := by
  classical
  intro d V W K
  let P := Matrix.of (fun (i : Fin u) (l : Fin (L+1)) => x i^(L-l.val))
  let Q := Matrix.of (fun (l : Fin (L+1)) (i : Fin u) => x i^l.val)
  let S := Matrix.diagonal (fun l : Fin (L+1) => (-1:ℂ)^l.val)
  let A := Matrix.of (fun (s : Fin u) (l : Fin (L+1)) =>
    if l.val<L*(s.val+1) then d (L*(s.val+1)-(l.val+1)) else 0)
  let B := Matrix.of (fun (l : Fin (L+1)) (k : Fin u) => d ((L+1)*k.val+l.val))
  have row (s : Fin u) (l : Fin (L+1)) :
      A s l=∑ i,w i*x i^(L*s.val+(L-l.val)) := by
    have hl := l.isLt
    change (if l.val<L*(s.val+1) then d (L*(s.val+1)-(l.val+1)) else 0)=_
    by_cases good : l.val<L*(s.val+1)
    · rw [if_pos good]
      change (∑ i,w i*x i^(L*(s.val+1)-(l.val+1)+1))=_
      have exp : L*(s.val+1)-(l.val+1)+1=L*s.val+(L-l.val) := by
        rw [Nat.mul_add,Nat.mul_one] at good ⊢
        omega
      rw [exp]
    · rw [if_neg good]
      have exp : L*s.val+(L-l.val)=0 := by rw [Nat.mul_add,Nat.mul_one] at good; omega
      simp [exp,zero]
  have left : A=(V.transpose * Matrix.diagonal w)*P := by
    ext s l
    rw [row,Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.mul_diagonal]
    change w i*x i^(L*s.val+(L-l.val))=(x i^L)^s.val*w i*x i^(L-l.val)
    rw [pow_add,pow_mul]
    ring
  have right : B=Q*(Matrix.diagonal (fun i => w i*x i) * W) := by
    ext l k
    rw [Matrix.mul_apply]
    change (∑ i,w i*x i^((L+1)*k.val+l.val+1))=_
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.diagonal_mul]
    change w i*x i^((L+1)*k.val+l.val+1)=x i^l.val*((w i*x i)*(x i^(L+1))^k.val)
    rw [pow_succ,pow_add,pow_mul]
    ring
  have kernel : K=(P*S)*Q := by
    ext i j
    rw [Matrix.mul_apply]
    change (∑ l : Fin (L+1),(-1:ℂ)^l.val*x i^(L-l.val)*x j^l.val)=_
    apply Finset.sum_congr rfl
    intro l _
    rw [show S=Matrix.diagonal (fun l : Fin (L+1) => (-1:ℂ)^l.val) from rfl,Matrix.mul_diagonal]
    change (-1:ℂ)^l.val*x i^(L-l.val)*x j^l.val=x i^(L-l.val)*(-1:ℂ)^l.val*x j^l.val
    ring
  calc
    _ = (A*S)*B := by
      ext s k
      rw [Matrix.of_apply,Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro l _
      rw [show S=Matrix.diagonal (fun l : Fin (L+1) => (-1:ℂ)^l.val) from rfl,Matrix.mul_diagonal]
      change (-1:ℂ)^l.val*B l k*A s l=A s l*(-1:ℂ)^l.val*B l k
      ring
    _ = _ := by rw [left,right,kernel]; simp only [Matrix.mul_assoc]

/-- Both square Vandermonde determinants are nonzero at distinct power nodes. -/
theorem moment_det_of_nodes {L u : ℕ} (x w : Fin u → ℂ)
    (weights : ∀ i,w i≠0) (nonzero : ∀ i,x i≠0) (zero : (∑ i,w i)=0)
    (first : Function.Injective (fun i => x i^L)) (second : Function.Injective (fun i => x i^(L+1)))
    (kernel : (Matrix.of (fun i j : Fin u => ∑ l : Fin (L+1),
      (-1:ℂ)^l.val*x i^(L-l.val)*x j^l.val)).det≠0) :
    let d (j : ℕ) := ∑ i,w i*x i^(j+1)
    (Matrix.of (fun s k : Fin u => ∑ l : Fin (L+1),
      (-1:ℂ)^l.val*d ((L+1)*k.val+l.val)*
        (if l.val<L*(s.val+1) then d (L*(s.val+1)-(l.val+1)) else 0))).det≠0 := by
  intro d
  have fact := moment_factorization (L:=L) x w zero
  dsimp only at fact
  rw [fact]
  simp only [Matrix.det_mul,Matrix.det_transpose,Matrix.det_diagonal]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr first)
    (Finset.prod_ne_zero_iff.mpr (fun i _ => weights i))) kernel) (mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun i _ => mul_ne_zero (weights i) (nonzero i)))
    (Matrix.det_vandermonde_ne_zero_iff.mpr second))

private theorem zero_sum_weights {u : ℕ} (dim : 2≤u) :
    ∃ w : Fin u→ℂ, (∀ i,w i≠0) ∧ (∑ i,w i)=0 := by
  let j : Fin u := ⟨0,by omega⟩
  let w (i : Fin u) : ℂ := 1-(if i=j then (u:ℂ) else 0)
  refine ⟨w,?_,?_⟩
  · intro i
    by_cases hit : i=j
    · simp only [w,if_pos hit,sub_ne_zero]
      exact_mod_cast (show (1:ℕ)≠u by omega)
    · simp [w,hit]
  · simp [w,Finset.sum_sub_distrib]

/-- The moments only use coefficients up through L²−2. The second
index is used only on its nonnegative branch. -/
theorem moment_indices {L : ℕ} (four : 4≤L) (s k : Fin (L-1)) (l : Fin (L+1)) :
    (L+1)*k.val+l.val≤L^2-2 ∧ L*(s.val+1)-(l.val+1)≤L^2-2 := by
  have hl := l.isLt
  have kp : k.val+2≤L := by have := k.isLt; omega
  have sp : s.val+2≤L := by have := s.isLt; omega
  have first : (L+1)*k.val+l.val+2≤L^2 := by nlinarith only [hl,Nat.mul_le_mul_left (L+1) kp]
  have second : L*(s.val+1)+2≤L^2 := by nlinarith only [four,Nat.mul_le_mul_left L sp]
  omega

/-- Truncating a geometric coefficient sequence to the specified
degree keeps the determinant nonzero. -/
theorem bounded_moments_of_nodes {L : ℕ} (four : 4≤L) (x : Fin (L-1)→ℂ)
    (nonzero : ∀ i,x i≠0) (first : Function.Injective (fun i => x i^L))
    (second : Function.Injective (fun i => x i^(L+1)))
    (kernel : (Matrix.of (fun i j : Fin (L-1) => ∑ l : Fin (L+1),
      (-1:ℂ)^l.val*x i^(L-l.val)*x j^l.val)).det≠0) :
    ∃ d : ℕ→ℂ, (∀ j, L^2-2<j → d j=0) ∧
      (Matrix.of (fun s k : Fin (L-1) => ∑ l : Fin (L+1),
        (-1:ℂ)^l.val*d ((L+1)*k.val+l.val)*
          (if l.val<L*(s.val+1) then d (L*(s.val+1)-(l.val+1)) else 0))).det≠0 := by
  obtain ⟨w,weights,zero⟩ := zero_sum_weights (show 2≤L-1 by omega)
  let raw (j : ℕ) := ∑ i,w i*x i^(j+1)
  let d (j : ℕ) := if j≤L^2-2 then raw j else 0
  have det := moment_det_of_nodes (L:=L) x w weights nonzero zero first second kernel
  change (Matrix.of (fun s k : Fin (L-1) => ∑ l : Fin (L+1), (-1:ℂ)^l.val*raw ((L+1)*k.val+l.val)*
    (if l.val<L*(s.val+1) then raw (L*(s.val+1)-(l.val+1)) else 0))).det≠0 at det
  refine ⟨d,fun j above => if_neg (Nat.not_le_of_lt above),?_⟩
  convert det using 2
  ext s k
  simp only [Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro l _
  obtain ⟨a,b⟩ := moment_indices four s k l
  simp only [d,if_pos a,if_pos b]

/-- Finite coefficients witnessing the boundary moment determinant. -/
theorem moment_matrix_exists (L : ℕ) (four : 4≤L) (evenL : Even L) :
    ∃ d : ℕ→ℂ, (∀ j,L^2-2<j → d j=0) ∧
      (Matrix.of (fun s k : Fin (L-1) => ∑ l : Fin (L+1),
        (-1:ℂ)^l.val*d ((L+1)*k.val+l.val)*
          (if l.val<L*(s.val+1) then d (L*(s.val+1)-(l.val+1)) else 0))).det≠0 := by
  obtain ⟨x,hx,first,second,kernel⟩ := CriticalConic.boundary_nodes (L:=L) (u:=L-1)
    (by omega) evenL (by omega)
  exact bounded_moments_of_nodes four x hx first second kernel

end CriticalThreeConic

namespace CriticalHigher.ConicBoundary

/-- Scaling all variables of a homogeneous polynomial scales its value by
the corresponding power. -/
theorem homogeneous_scale {K σ : Type*} [CommSemiring K] {m : ℕ}
    {P : MvPolynomial σ K} (hom : P.IsHomogeneous m) (c : K) (x : σ → K) :
    MvPolynomial.eval (fun i => c*x i) P = c^m * MvPolynomial.eval x P := by
  classical
  change P.IsWeightedHomogeneous (1 : σ → ℕ) m at hom
  induction hom using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q _ _ hp hq => simp only [map_add,hp,hq,mul_add]
  | monomial d r degree =>
    have deg : ∑ i ∈ d.support, d i = m := by
      change Finsupp.degree d = m
      rw [Finsupp.degree_eq_weight_one]
      exact degree
    rw [MvPolynomial.eval_monomial,MvPolynomial.eval_monomial]
    simp only [Finsupp.prod,mul_pow,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,deg]
    ac_rfl

/-- Any nonzero homogeneous coefficient test can be made nonzero on the
monic affine chart, including when its first known witness is outside that chart. -/
theorem homogeneous_monic_chart {K : Type*} [Field K] [Infinite K] {b m : ℕ}
    (P : MvPolynomial (Fin (b+1)) K) (hom : P.IsHomogeneous m) (nonzero : P ≠ 0) :
    ∃ d : Fin (b+1) → K, d (Fin.last b)=1 ∧ MvPolynomial.eval d P ≠ 0 := by
  classical
  have nonzeroProduct : P*MvPolynomial.X (Fin.last b) ≠ 0 := mul_ne_zero nonzero (MvPolynomial.X_ne_zero _)
  obtain ⟨x,hx⟩ : ∃ x : Fin (b+1) → K, MvPolynomial.eval x (P*MvPolynomial.X (Fin.last b)) ≠ 0 := by
    by_contra! vanishes
    exact nonzeroProduct (MvPolynomial.funext fun x => by rw [vanishes x,map_zero])
  rw [map_mul,MvPolynomial.eval_X] at hx
  obtain ⟨good,last⟩ := mul_ne_zero_iff.mp hx
  refine ⟨fun i => (x (Fin.last b))⁻¹*x i,inv_mul_cancel₀ last,?_⟩
  rw [homogeneous_scale hom]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero last)) good

/-- Every monic coefficient vector occurs as the coefficients of a product
of exactly b linear factors, counted with multiplicity. -/
theorem monic_root_parameters {K : Type*} [Field K] [IsAlgClosed K] {b : ℕ}
    (d : Fin (b+1) → K) (top : d (Fin.last b)=1) :
    ∃ t : Fin b → K, ∀ i : Fin (b+1),
      (∏ j, (Polynomial.X-Polynomial.C (t j))).coeff i.val = d i := by
  classical
  let p := Polynomial.ofFn (b+1) d
  have coeff (i : Fin (b+1)) : p.coeff i.val=d i := Polynomial.ofFn_coeff_eq_val_of_lt d i.isLt
  have highest : p.coeff b=1 := (coeff (Fin.last b)).trans top
  have upper : p.natDegree ≤ b := Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) d)
  have degree := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero upper (ne_of_eq_of_ne highest one_ne_zero)
  have monic := Polynomial.monic_of_natDegree_le_of_coeff_eq_one b upper highest
  have splits := IsAlgClosed.splits p
  let l := p.roots.toList
  have len : l.length=b := (Multiset.length_toList _).trans (splits.natDegree_eq_card_roots.symm.trans degree)
  let e : Fin b ≃ Fin l.length := finCongr len.symm
  let t : Fin b → K := fun i => l[(e i).val]
  have prod : (∏ i : Fin b, (Polynomial.X-Polynomial.C (t i))) = p := by
    calc
      _ = ∏ j : Fin l.length, (Polynomial.X-Polynomial.C l[j.val]) :=
        e.prod_comp (fun j : Fin l.length => Polynomial.X-Polynomial.C l[j.val])
      _ = (l.map fun z => Polynomial.X - Polynomial.C z).prod :=
        Fin.prod_univ_fun_getElem l (fun z : K => (Polynomial.X : Polynomial K)-Polynomial.C z)
      _ = (p.roots.map fun z => Polynomial.X - Polynomial.C z).prod := Multiset.prod_map_toList _ _
      _ = p := (splits.eq_prod_roots_of_monic monic).symm
  exact ⟨t,fun i => (congrArg (fun q : Polynomial K => q.coeff i.val) prod).trans (coeff i)⟩

/-- Vanishing at all distinct, strictly positive integral tuples would imply
vanishing on a product of infinite grids. -/
theorem disjoint_natural_grid {K : Type*} [Field K] [CharZero K] {b : ℕ}
    (Q : MvPolynomial (Fin b) K) (nonzero : Q≠0) :
    ∃ v : Fin b → ℕ, (∀ i, 0<v i) ∧ Function.Injective v ∧
      MvPolynomial.eval (fun i => (v i : K)) Q≠0 := by
  classical
  let code (p : Fin b × ℕ) := Encodable.encode p+1
  have code_inj : Function.Injective code := fun p q h => Encodable.encode_injective (Nat.succ.inj h)
  let box (i : Fin b) : Set K := Set.range fun n : ℕ => (code (i,n) : K)
  have infinite (i : Fin b) : (box i).Infinite := by
    apply Set.infinite_range_of_injective
    intro n m equal
    have he : code (i,n)=code (i,m) := Nat.cast_injective equal
    exact congrArg Prod.snd (code_inj he)
  obtain ⟨x,within,good⟩ : ∃ x : Fin b → K, x∈Set.pi Set.univ box ∧ MvPolynomial.eval x Q≠0 := by
    by_contra! vanishes
    exact nonzero (MvPolynomial.funext_set box infinite fun x hx => by rw [vanishes x hx,map_zero])
  choose n agree using fun i => within i (Set.mem_univ _)
  let v (i : Fin b) := code (i,n i)
  have cast : (fun i => (v i : K))=x := funext agree
  exact ⟨v,fun i => Nat.succ_pos _,fun i j he => congrArg Prod.fst (code_inj he),cast ▸ good⟩

/-- A coefficient test nonzero at one monic polynomial is also nonzero on
the coefficients of a polynomial with distinct strictly positive integral roots. -/
theorem integral_roots_of_monic {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {b : ℕ}
    (P : MvPolynomial (Fin (b+1)) K) (d : Fin (b+1) → K)
    (top : d (Fin.last b)=1) (good : MvPolynomial.eval d P≠0) :
    ∃ v : Fin b → ℕ, (∀ i, 0<v i) ∧ Function.Injective v ∧
      MvPolynomial.eval (fun i : Fin (b+1) =>
        (∏ j, (Polynomial.X-Polynomial.C (v j : K))).coeff i.val) P≠0 := by
  classical
  let S := MvPolynomial (Fin b) K
  let universal : Polynomial S := ∏ j : Fin b, (Polynomial.X-Polynomial.C (MvPolynomial.X j : S))
  let coordinates (i : Fin (b+1)) := universal.coeff i.val
  let Q := MvPolynomial.aeval coordinates P
  have specialize (x : Fin b → K) :
      MvPolynomial.eval x Q = MvPolynomial.eval (fun i : Fin (b+1) =>
        (∏ j, (Polynomial.X-Polynomial.C (x j))).coeff i.val) P := by
    have mapped : universal.map (MvPolynomial.eval x) = ∏ j, (Polynomial.X-Polynomial.C (x j)) := by
      simp [universal,Polynomial.map_prod]
    have eq (i : Fin (b+1)) : MvPolynomial.eval x (coordinates i) =
        (∏ j, (Polynomial.X-Polynomial.C (x j))).coeff i.val := by
      rw [←mapped,Polynomial.coeff_map]
    have twice : (MvPolynomial.aeval x).comp (MvPolynomial.aeval coordinates) =
        MvPolynomial.aeval (fun j => MvPolynomial.eval x (coordinates j)) := by
      ext j
      simp [MvPolynomial.aeval_eq_eval]
    exact (DFunLike.congr_fun twice P).trans (congrArg (fun v : Fin (b+1) → K => MvPolynomial.eval v P) (funext eq))
  obtain ⟨t,factor⟩ := monic_root_parameters d top
  have nonzero : Q≠0 := by
    intro zero
    have atRoots := specialize t
    rw [zero,map_zero,funext factor] at atRoots
    exact good atRoots.symm
  obtain ⟨v,positive,distinct,hit⟩ := disjoint_natural_grid Q nonzero
  exact ⟨v,positive,distinct,(specialize (fun i => (v i : K))).symm ▸ hit⟩

/-- The same integral tuple is nonzero, avoids opposite pairs, and has
distinct L-th powers for every positive L. -/
theorem good_roots_of_monic {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {b L : ℕ}
    (hL : 0<L) (P : MvPolynomial (Fin (b+1)) K) (d : Fin (b+1) → K)
    (top : d (Fin.last b)=1) (good : MvPolynomial.eval d P≠0) :
    ∃ t : Fin b → K, (∀ i, t i≠0) ∧ (∀ i j, t i+t j≠0) ∧ Function.Injective (fun i => t i^L) ∧
      MvPolynomial.eval (fun i : Fin (b+1) => (∏ j : Fin b, (Polynomial.X-Polynomial.C (t j))).coeff i.val) P≠0 := by
  obtain ⟨v,positive,unique,hit⟩ := integral_roots_of_monic P d top good
  refine ⟨fun i => (v i : K),fun i => Nat.cast_ne_zero.mpr (positive i).ne',?_,?_,hit⟩
  · intro i j
    rw [←Nat.cast_add]
    exact Nat.cast_ne_zero.mpr (add_pos (positive i) (positive j)).ne'
  · intro i j eq
    change (v i : K)^L=(v j : K)^L at eq
    have he : v i^L=v j^L := by exact_mod_cast eq
    exact unique ((Nat.pow_left_inj hL.ne').mp he)

/-- Every nonzero homogeneous coefficient test admits distinct suitable
nodes, including the boundary chart of binary forms. -/
theorem good_roots_of_homogeneous {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {b m L : ℕ}
    (hL : 0<L) (P : MvPolynomial (Fin (b+1)) K) (hom : P.IsHomogeneous m) (nonzero : P≠0) :
    ∃ t : Fin b → K, (∀ i, t i≠0) ∧ (∀ i j, t i+t j≠0) ∧ Function.Injective (fun i => t i^L) ∧
      MvPolynomial.eval (fun i : Fin (b+1) => (∏ j : Fin b, (Polynomial.X-Polynomial.C (t j))).coeff i.val) P≠0 := by
  obtain ⟨d,top,good⟩ := homogeneous_monic_chart P hom nonzero
  exact good_roots_of_monic hL P d top good

end CriticalHigher.ConicBoundary

namespace CriticalConicBoundary

open Polynomial

private lemma block_sum {u L : ℕ} (v : ℕ→ℂ) :
    (∑ k : Fin u, ∑ l : Fin (L+1), v ((L+1)*k.val+l.val)) =
      ∑ j ∈ Finset.range (u*(L+1)), v j := by
  have reindex := (finProdFinEquiv : Fin u × Fin (L+1) ≃ Fin (u*(L+1))).sum_comp
    (fun j => v j.val)
  rw [Fintype.sum_prod_type] at reindex
  rw [←Fin.sum_univ_eq_sum_range]
  change (∑ k : Fin u, ∑ l : Fin (L+1), v (l.val+(L+1)*k.val))= _ at reindex
  simpa only [Nat.add_comm] using reindex

/-- The nodal polynomial supplies the one dependence between the b+1
ordinary moments in one row of the coefficient system. -/
private lemma nodal_relation {u L b : ℕ} (size : u*(L+1)=b+1) (t : Fin b→ℂ)
    (D : ℂ[X]) (deg : D.natDegree≤b) (roots : ∀ i,D.eval (t i)=0) (g : Fin b→ℂ) :
    (∑ k : Fin u, ∑ l : Fin (L+1),D.coeff ((L+1)*k.val+l.val)*
      (∑ i,t i^((L+1)*k.val+l.val)*g i))=0 := by
  rw [block_sum (u:=u) (L:=L) (fun n => D.coeff n * (∑ i,t i^n*g i)),size]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  have ev := congrArg (fun p : ℂ[X] => p.eval (t i))
    (D.as_sum_range_C_mul_X_pow' (by omega : D.natDegree < b+1))
  simp only [eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X] at ev
  simp_rw [←mul_assoc]
  rw [←Finset.sum_mul,←ev,roots,zero_mul]

/-- Coefficient comparisons from the conic packet reduce its physical
kernel to an (L−1)-square matrix. Once the common vector B vanishes,
the first b ordinary moments give an invertible Vandermonde system. -/
theorem zero_of_nodal_moments {L u b : ℕ} (size : u*(L+1)=b+1) (inside : u≤L)
    (t : Fin b→ℂ) (distinct : Function.Injective t)
    (D : ℂ[X]) (deg : D.natDegree≤b) (roots : ∀ i,D.eval (t i)=0)
    (g : Fin b→Fin L→ℂ) (B : Fin u→ℂ)
    (mom : ∀ (s : Fin L) (k : Fin u) (l : Fin (L+1)),
      (∑ i,t i^((L+1)*k.val+l.val)*g i s)=(-1:ℂ)^l.val*B k*
        (if l.val<L*(s.val+1) then D.coeff (L*(s.val+1)-(l.val+1)) else 0))
    (det : (Matrix.of (fun (s k : Fin u) => ∑ l : Fin (L+1),(-1:ℂ)^l.val*
      D.coeff ((L+1)*k.val+l.val)*
      (if l.val<L*(s.val+1) then D.coeff (L*(s.val+1)-(l.val+1)) else 0))).det≠0) :
    g=0 := by
  let M := Matrix.of (fun (s k : Fin u) => ∑ l : Fin (L+1),(-1:ℂ)^l.val*
      D.coeff ((L+1)*k.val+l.val)*
      (if l.val<L*(s.val+1) then D.coeff (L*(s.val+1)-(l.val+1)) else 0))
  have killed : M.mulVec B=0 := by
    funext s
    let j : Fin L := ⟨s.val,s.isLt.trans_le inside⟩
    have rel := nodal_relation size t D deg roots (fun i => g i j)
    change (∑ k,M s k*B k)=0
    calc
      _=∑ k : Fin u, ∑ l : Fin (L+1),D.coeff ((L+1)*k.val+l.val)*
            (∑ i,t i^((L+1)*k.val+l.val)*g i j) := by
        apply Finset.sum_congr rfl
        intro k _
        dsimp [M]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l _
        rw [mom]
        dsimp only [j]
        ring
      _=0 := rel
  have Bzero : B=0 := Matrix.eq_zero_of_mulVec_eq_zero det killed
  have column (s : Fin L) : (fun i => g i s)=0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero distinct
    intro j
    let k : Fin u := ⟨j.val/(L+1),(Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)⟩
    let l : Fin (L+1) := ⟨j.val%(L+1),Nat.mod_lt _ (by omega)⟩
    have ordinal : (L+1)*k.val+l.val=j.val := Nat.div_add_mod _ _
    have z := mom s k l
    rw [ordinal,Bzero] at z
    simpa only [mul_comm (g _ _),Pi.zero_apply,mul_zero,zero_mul] using z
  funext i s
  exact congrFun (column s) i

end CriticalConicBoundary

namespace CriticalConicBoundary

open MvPolynomial

/-- Model the determinant in the independent coefficients of the nodal
polynomial. Scaling those coefficients scales the determinant in degree 2u. -/
theorem moment_polynomial (L u b : ℕ) :
    let M (d : ℕ → ℂ) : Matrix (Fin u) (Fin u) ℂ :=
      Matrix.of (fun s k => ∑ l : Fin (L+1),(-1 : ℂ)^l.val*d ((L+1)*k.val+l.val)*
        (if l.val<L*(s.val+1) then d (L*(s.val+1)-(l.val+1)) else 0))
    ∃ P : MvPolynomial (Fin (b+1)) ℂ,
    P.IsHomogeneous (u*2) ∧ ∀ y : Fin (b+1)→ℂ,
    eval y P=(M (fun j => if h : j<b+1 then y ⟨j,h⟩ else 0)).det := by
  classical
  intro M
  let x (j : ℕ) : MvPolynomial (Fin (b+1)) ℂ := if h : j<b+1 then X ⟨j,h⟩ else 0
  let A : Matrix (Fin u) (Fin u) (MvPolynomial (Fin (b+1)) ℂ) := Matrix.of (fun s k =>
    ∑ l : Fin (L+1),C ((-1:ℂ)^l.val)*x ((L+1)*k.val+l.val)*
      (if l.val<L*(s.val+1) then x (L*(s.val+1)-(l.val+1)) else 0))
  have linear (j : ℕ) : (x j).IsHomogeneous 1 := by
    dsimp only [x]
    split
    · exact isHomogeneous_X _ _
    · exact isHomogeneous_zero _ _ _
  have quad (s k : Fin u) : (A s k).IsHomogeneous 2 := by
    dsimp only [A,Matrix.of_apply]
    apply IsHomogeneous.sum
    intro l _
    apply IsHomogeneous.mul (m:=1) (n:=1) ((linear _).C_mul _)
    split
    · exact linear _
    · exact isHomogeneous_zero _ _ _
  refine ⟨A.det,?_,?_⟩
  · rw [Matrix.det_apply']
    apply IsHomogeneous.sum
    intro σ _
    have prod := IsHomogeneous.prod (Finset.univ : Finset (Fin u)) (fun i => A (σ i) i)
      (fun _ => 2) (fun i _ => quad _ _)
    have card : (∑ _ : Fin u,2)=u*2 := by simp
    rw [card] at prod
    simpa only [map_intCast] using prod.C_mul (((Equiv.Perm.sign σ : ℤ) : ℂ))
  · intro y
    rw [RingHom.map_det,RingHom.mapMatrix_apply]
    congr 1
    ext s k
    simp only [Matrix.map_apply,A,Matrix.of_apply,M,map_sum,map_mul,eval_C]
    apply Finset.sum_congr rfl
    intro l _
    have hx (n : ℕ) : eval y (x n) = if h : n<b+1 then y ⟨n,h⟩ else 0 := by
      dsimp only [x]
      split <;> simp
    by_cases c : l.val<L*(s.val+1) <;> simp only [c,if_true,if_false,map_zero,hx]

end CriticalConicBoundary

namespace CriticalConicBoundary

open Polynomial

/-- Realize a nonzero coefficient determinant at the coefficients of the
actual nodal polynomial while keeping all its Cauchy denominators nonzero. -/
theorem physical_nodes {L : ℕ} (four : 4≤L) (evenL : Even L) :
    let b := L^2-2
    let M (d : ℕ → ℂ) : Matrix (Fin (L-1)) (Fin (L-1)) ℂ :=
      Matrix.of (fun s k => ∑ l : Fin (L+1),(-1 : ℂ)^l.val*d ((L+1)*k.val+l.val)*
        (if l.val<L*(s.val+1) then d (L*(s.val+1)-(l.val+1)) else 0))
    ∃ t : Fin b→ℂ, Function.Injective (fun i => t i^L) ∧ (∀ i j,t i+t j≠0) ∧
      (M (∏ i,(X-C (t i))).coeff).det≠0 := by
  intro b M
  obtain ⟨P,hom,ev⟩ := moment_polynomial L (L-1) b
  obtain ⟨d,support,det⟩ := CriticalThreeConic.moment_matrix_exists L four evenL
  have extend (d : ℕ→ℂ) (zero : ∀ j,b<j→d j=0) :
      (fun j => if h : j<b+1 then (fun i : Fin (b+1) => d i.val) ⟨j,h⟩ else 0)=d := by
    funext j
    split
    · rfl
    · exact (zero j (by omega)).symm
  have hit : MvPolynomial.eval (fun i : Fin (b+1) => d i.val) P ≠ 0 := by
    rw [ev,extend _ support]
    exact det
  have nz : P≠0 := fun eq => hit (by rw [eq,map_zero])
  obtain ⟨t,_,poles,diff,y⟩ := CriticalHigher.ConicBoundary.good_roots_of_homogeneous
    (by omega : 0<L) P hom nz
  let D : ℂ[X] := ∏ i,(X-C (t i))
  have deg : D.natDegree=b := by
    dsimp only [D]
    rw [natDegree_finsetProd_X_sub_C_eq_card,Finset.card_univ,Fintype.card_fin]
  rw [ev] at y
  change (M
    (fun j => if h : j<b+1 then (fun i : Fin (b+1) => D.coeff i.val) ⟨j,h⟩ else 0)).det≠0 at y
  rw [extend _ (fun j hj => coeff_eq_zero_of_natDegree_lt (deg.trans_lt hj))] at y
  exact ⟨t,diff,poles,y⟩

/-- Taking the first h rows gives a square Vandermonde matrix. -/
theorem powers_frame {b h L : ℕ} (room : h≤b) (t : Fin b→ℂ)
    (distinct : Function.Injective (fun i => t i^L)) :
    Function.Injective (Matrix.of (fun (i : Fin b) (j : Fin h) => t i^(L*j.val))).mulVec := by
  let a (i : Fin h) := t (Fin.castLE room i)^L
  have inj : Function.Injective a := by
    intro i j eq
    exact Fin.ext (congrArg (fun w : Fin b => w.val) (distinct eq))
  intro x y same
  have small : (Matrix.vandermonde a).mulVec x=(Matrix.vandermonde a).mulVec y := by
    funext i
    simpa only [Matrix.mulVec,dotProduct,Matrix.vandermonde_apply,a,←pow_mul,Matrix.of_apply]
      using congrFun same (Fin.castLE room i)
  apply sub_eq_zero.mp
  apply Matrix.eq_zero_of_mulVec_eq_zero (Matrix.det_vandermonde_ne_zero_iff.mpr inj)
  rw [Matrix.mulVec_sub,small,sub_self]

end CriticalConicBoundary

namespace CriticalConic

open Polynomial

/-- Divide one diagonal-vanishing row polynomial by Z−a, retaining all
coefficient identities, including the lower and upper boundary terms. -/
theorem boundary_row_factor {K : Type*} [Field K] {L : ℕ} (hL : 0<L) (a : K)
    (f : Fin (L+1)→K) (vanish : (∑ j,a^j.val*f j)=0) :
    ∃ g : Fin L→K,
      (g=0 → f=0) ∧
      (∀ z : K,(∑ j,z^j.val*f j)=(z-a)*(∑ s,z^s.val*g s)) ∧
      let padded (n : ℕ) := if h : n<L then g ⟨n,h⟩ else 0
      ∀ j : Fin (L+1),f j=(if j.val=0 then 0 else padded (j.val-1))-a*padded j.val := by
  classical
  let P : K[X] := ∑ j : Fin (L+1),monomial j.val (f j)
  have coef (j : Fin (L+1)) : P.coeff j.val=f j := by
    simp only [P,finsetSum_coeff,coeff_monomial,Fin.val_inj]
    simp
  have peval (z : K) : P.eval z=∑ j,z^j.val*f j := by
    simp only [P,eval_finsetSum,eval_monomial,mul_comm]
  have pdeg : P.natDegree≤L := by
    apply natDegree_sum_le_of_forall_le
    intro j _
    exact (natDegree_monomial_le _).trans (by have := j.isLt; omega)
  let G := P /ₘ (X-C a)
  have degg : G.natDegree<L := by
    change (P /ₘ (X-C a)).natDegree<L
    rw [natDegree_divByMonic P (monic_X_sub_C a),natDegree_X_sub_C]
    omega
  have factor : P=(X-C a)*G := by
    have id := modByMonic_add_div P (X-C a)
    rw [modByMonic_X_sub_C_eq_C_eval,peval,vanish,map_zero,zero_add] at id
    exact id.symm
  let g (s : Fin L) := G.coeff s.val
  let padded (n : ℕ) := if h : n<L then g ⟨n,h⟩ else 0
  have pad (n : ℕ) : padded n=G.coeff n := by
    by_cases h : n<L
    · simp [padded,h,g]
    · simp [padded,h,coeff_eq_zero_of_natDegree_lt (by omega : G.natDegree<n)]
  have ge (z : K) : G.eval z=∑ s : Fin L,z^s.val*g s := by
    calc
      _ = (∑ j ∈ Finset.range L,C (G.coeff j)*X^j).eval z :=
        congrArg (eval z) (G.as_sum_range_C_mul_X_pow' degg)
      _ = _ := by
        rw [eval_finsetSum,← Fin.sum_univ_eq_sum_range]
        simp only [g,eval_mul,eval_C,eval_pow,eval_X,mul_comm]
  have formula (j : Fin (L+1)) :
      f j=(if j.val=0 then 0 else padded (j.val-1))-a*padded j.val := by
    rw [← coef j,factor,pad]
    by_cases zero : j.val=0
    · rw [zero]
      simp [sub_mul,pad]
    · rw [if_neg zero,pad]
      have rec' := coeff_X_sub_C_mul (p:=G) (r:=a) (a:=j.val-1)
      rwa [show j.val-1+1=j.val by omega] at rec'
  refine ⟨g,?_,?_,formula⟩
  · intro hz
    funext j
    have zero (n : ℕ) : padded n=0 := by simp [padded,hz]
    simpa only [zero,ite_self,mul_zero,sub_zero,Pi.zero_apply] using formula j
  · intro z
    rw [← peval,factor,eval_mul,eval_sub,eval_X,eval_C,ge]

/-- The even difference of powers divided by x+a has the indicated
alternating coefficients in the second node. -/
theorem boundary_geometric_sum {K : Type*} [Field K] {L : ℕ} (even : Even L)
    (a z : K) (plus : a+z≠0) :
    (z^L-a^L)/(a+z)=∑ l : Fin L,(-a)^l.val*z^(L-1-l.val) := by
  apply (div_eq_iff plus).mpr
  rw [Fin.sum_univ_eq_sum_range (fun l : ℕ => (-a)^l*z^(L-1-l)) L]
  have eq := geom_sum₂_mul (-a) z L
  rw [even.neg_pow] at eq
  linear_combination eq

/-- The divided pole equations are the values at the physical nodes of
the polynomial whose coefficient slots are the signed weighted moments. -/
theorem boundary_tile_roots {K : Type*} [Field K] {L b : ℕ} (even : Even L)
    (t q : Fin b→K) (regular : ∀ i j,t i+t j≠0)
    (f : Fin b→Fin (L+1)→K) (g : Fin b→Fin L→K)
    (factor : ∀ i (x : K),(∑ j,x^j.val*f i j)=(x-t i^L)*(∑ s,x^s.val*g i s))
    (poles : ∀ j,(∑ i,q i*((∑ s,t j^(L*s.val)*f i s)/(t i+t j)))=0) :
    let c (s l : Fin L) := ∑ i,q i*(-t i)^l.val*g i s
    let P := ∑ s : Fin L,∑ l : Fin L,monomial (L*s.val+(L-1-l.val)) (c s l)
    ∀ j,P.eval (t j)=0 := by
  classical
  intro c P j
  let x := t j
  have row (i : Fin b) :
      (∑ s,x^(L*s.val)*f i s)/(t i+x)=
        (∑ s,x^(L*s.val)*g i s)*(∑ l : Fin L,(-t i)^l.val*x^(L-1-l.val)) := by
    have h := factor i (x^L)
    simp only [← pow_mul] at h
    rw [h,← boundary_geometric_sum even (t i) x (regular i j)]
    ring
  have commute3 (v : Fin L→Fin L→Fin b→K) :
      (∑ s,∑ l,∑ i,v s l i)=(∑ i,∑ s,∑ l,v s l i) := by
    calc
      _ = ∑ s,∑ i,∑ l,v s l i := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  change P.eval x=0
  simp only [P,c,eval_finsetSum,eval_monomial,pow_add,Finset.sum_mul]
  rw [commute3]
  calc
    _ = ∑ i,q i*((∑ s,x^(L*s.val)*g i s)*(∑ l : Fin L,(-t i)^l.val*x^(L-1-l.val))) := by
      simp only [Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = ∑ i,q i*((∑ s,x^(L*s.val)*f i s)/(t i+x)) := by simp_rw [row]
    _ = 0 := poles j

/-- The blocks of length L are disjoint; reversing an index inside a
block preserves uniqueness of the associated monomial exponent. -/
theorem boundary_index_eq {L : ℕ} (positive : 0 < L) (u v s l : Fin L) :
    L*u.val+(L-1-v.val) = L*s.val+(L-1-l.val) ↔ u=s ∧ v=l := by
  have quotient (x y : Fin L) :
      (L*x.val+(L-1-y.val))/L=x.val := by
    rw [Nat.mul_add_div positive,Nat.div_eq_of_lt (by omega : L-1-y.val<L),Nat.add_zero]
  constructor
  · intro eq
    have blocks := congrArg (fun n : ℕ => n/L) eq
    simp only [quotient] at blocks
    have first := Fin.ext blocks
    subst u
    have reversed := Nat.add_left_cancel eq
    exact ⟨rfl,Fin.ext (by omega)⟩
  · rintro ⟨rfl,rfl⟩
    rfl

/-- Read one of the L-by-L coefficients from the single encoded polynomial. -/
theorem boundary_monomial_coefficient {L : ℕ} (positive : 0 < L) (c : Fin L → Fin L → ℂ)
    (s l : Fin L) :
    (∑ u : Fin L, ∑ v : Fin L, Polynomial.monomial (L*u.val+(L-1-v.val)) (c u v)).coeff
        (L*s.val+(L-1-l.val)) = c s l := by
  classical
  simp only [finsetSum_coeff,coeff_monomial,boundary_index_eq positive]
  simp [ite_and,Finset.sum_ite_irrel]

/-- The unique would-be term of degree L²−1 is zero, leaving a polynomial
of degree at most the number b=L²−2 of distinct interpolation nodes. -/
theorem boundary_polynomial_degree {L b : ℕ} (positive : 0 < L) (hb : b=L^2-2)
    (c : Fin L → Fin L → ℂ)
    (top : ∀ s l : Fin L, s.val+1=L → l.val=0 → c s l=0) :
    (∑ s : Fin L, ∑ l : Fin L, Polynomial.monomial (L*s.val+(L-1-l.val)) (c s l)).natDegree ≤ b := by
  classical
  apply natDegree_sum_le_of_forall_le
  intro s _
  apply natDegree_sum_le_of_forall_le
  intro l _
  by_cases small : L*s.val+(L-1-l.val) ≤ b
  · exact (natDegree_monomial_le (c s l)).trans small
  have block : L*s.val+(L-1-l.val)+l.val+1=L*(s.val+1) := by
    rw [Nat.mul_add,Nat.mul_one]
    omega
  have last : s.val+1=L := by
    by_contra h
    have lt : s.val+1<L := by omega
    have upper := Nat.mul_lt_mul_of_pos_left lt positive
    rw [←block,←pow_two] at upper
    omega
  have high : L*s.val+(L-1-l.val)+l.val+1=L^2 := by rw [block,last,pow_two]
  have zero : l.val=0 := by omega
  rw [top s l last zero]
  simp

/-- Vanishing at all b nodes determines every coefficient up to the
single common multiple of the monic polynomial with these roots. -/
theorem boundary_polynomial_readout {L b : ℕ} (hL : 4 ≤ L) (hb : b=L^2-2)
    (t : Fin b → ℂ) (distinct : Function.Injective t) (c : Fin L → Fin L → ℂ)
    (top : ∀ s l : Fin L, s.val+1=L → l.val=0 → c s l=0) :
    let P := ∑ s : Fin L, ∑ l : Fin L, Polynomial.monomial (L*s.val+(L-1-l.val)) (c s l)
    (∀ i, P.eval (t i)=0) → ∃ B : ℂ, ∀ s l, c s l =
      B*(∏ i, (Polynomial.X-Polynomial.C (t i))).coeff (L*s.val+(L-1-l.val)) := by
  classical
  intro P vanish
  let D : Polynomial ℂ := ∏ i, (X-C (t i))
  have degree : P.natDegree ≤ b := boundary_polynomial_degree (by omega) hb c top
  have divisor : D ∣ P :=
    Fintype.prod_dvd_of_coprime (pairwise_coprime_X_sub_C distinct)
      (fun i => dvd_iff_isRoot.mpr (vanish i))
  have factor : P = C P.leadingCoeff * D := by
    apply eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (monic_prod_X_sub_C t _) divisor
    simpa [D] using degree
  refine ⟨P.leadingCoeff,?_⟩
  intro s l
  have atCoeff := congrArg (fun p : Polynomial ℂ => p.coeff (L*s.val+(L-1-l.val))) factor
  calc
    c s l = P.coeff (L*s.val+(L-1-l.val)) :=
      (boundary_monomial_coefficient (by omega) c s l).symm
    _ = _ := by simpa only [coeff_C_mul] using atCoeff

/-- The three conic tangent equations give the signed coefficient moments
of one common multiple of the node polynomial for each right row. The last
moment in each block follows from the unweighted column equations. -/
theorem sharp_boundary_interpolation (L : ℕ) (hL : 4≤L) (even : Even L) :
    let b := L^2-2
    let u := L-1
    ∀ t : Fin b→ℂ,Function.Injective t → (∀ i j,t i+t j≠0) →
    let M : Matrix (Fin b) (Fin (L+1)) ℂ := fun j s => t j^(L*s.val)
    let Q : Matrix (Fin u) (Fin b) ℂ := fun k i => t i^((L+1)*k.val)
    let D := ∏ i : Fin b,(X-C (t i))
    ∀ f : Fin b→Fin (L+1)→ℂ,(∀ i,M.mulVec (f i) i=0) →
      (∀ k j,(∑ i,Q k i*f i j)=0) →
      (∀ k j,(∑ i,Q k i*(M.mulVec (f i) j/(t i+t j)))=0) →
      ∃ g : Fin b→Fin L→ℂ,∃ B : Fin u→ℂ,(g=0 → f=0) ∧
        ∀ s : Fin L,∀ k : Fin u,∀ l : Fin (L+1),
          (∑ i,t i^((L+1)*k.val+l.val)*g i s)=(-1:ℂ)^l.val*B k*
            (if l.val<L*(s.val+1) then D.coeff (L*(s.val+1)-(l.val+1)) else 0) := by
  classical
  intro b u t distinct regular M Q D f diag mass poles
  have root (i : Fin b) : (∑ j,(t i^L)^j.val*f i j)=0 := by
    simp only [← pow_mul]
    exact diag i
  choose g kill factor rows using fun i => boundary_row_factor (by omega : 0<L) (t i^L) (f i) (root i)
  let pad (i : Fin b) (n : ℕ) := if h : n<L then g i ⟨n,h⟩ else 0
  have padAt (i : Fin b) (s : Fin L) : pad i s.val=g i s := by simp [pad,s.isLt]
  have padEnd (i : Fin b) : pad i L=0 := by simp [pad]
  have coeffRow (i : Fin b) (j : Fin (L+1)) :
      f i j=(if j.val=0 then 0 else pad i (j.val-1))-t i^L*pad i j.val := rows i j
  have topRow (s : Fin L) (hs : s.val+1=L) (i : Fin b) : f i (Fin.last L)=g i s := by
    have ce := coeffRow i (Fin.last L)
    simpa only [Fin.val_last,if_neg (by omega : L≠0),show L-1=s.val by omega,
      padAt,padEnd,mul_zero,sub_zero] using ce
  let tile (k : Fin u) (s l : Fin L) := ∑ i,Q k i*(-t i)^l.val*g i s
  have crest (k : Fin u) (s l : Fin L) (hs : s.val+1=L) (hl : l.val=0) : tile k s l=0 := by
    have z := mass k (Fin.last L)
    simpa only [tile,hl,pow_zero,mul_one,topRow s hs] using z
  have vanish (k : Fin u) := boundary_tile_roots even t (Q k) regular f g factor (fun j => poles k j)
  choose B lookup using fun k : Fin u =>
    boundary_polynomial_readout hL (show b=L^2-2 from rfl) t distinct (tile k) (crest k) (vanish k)
  let moment (k : Fin u) (s : Fin L) (l : ℕ) := ∑ i,t i^((L+1)*k.val+l)*g i s
  have signed (k : Fin u) (s l : Fin L) :
      moment k s l.val=(-1:ℂ)^l.val*B k*D.coeff (L*s.val+(L-1-l.val)) := by
    have untwist : (-1:ℂ)^l.val*tile k s l=moment k s l.val := by
      dsimp only [tile,moment]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have sq : (-1:ℂ)^l.val*(-1:ℂ)^l.val=1 := by rw [← mul_pow]; simp
      rw [show -t i=(-1:ℂ)*t i by ring,mul_pow,pow_add]
      change (-1:ℂ)^l.val*((t i^((L+1)*k.val))*((-1)^l.val*t i^l.val)*g i s)=_
      linear_combination (t i^((L+1)*k.val)*t i^l.val*g i s)*sq
    calc
      _ = (-1:ℂ)^l.val*tile k s l := untwist.symm
      _ = _ := by rw [lookup]; ring
  have lag (k : Fin u) (s : Fin L) :
      moment k s L=∑ i,Q k i*(if s.val=0 then 0 else pad i (s.val-1)) := by
    calc
      _ = (∑ i,Q k i*(if s.val=0 then 0 else pad i (s.val-1))) -
          (∑ i,Q k i*f i s.castSucc) := by
        change (∑ i,t i^((L+1)*k.val+L)*g i s)=_
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [coeffRow i s.castSucc,Fin.val_castSucc,padAt,pow_add]
        dsimp only [Q]
        ring
      _ = _ := by rw [mass,sub_zero]
  refine ⟨g,B,fun hz => funext fun i => kill i (congrFun hz i),?_⟩
  intro s k l
  change moment k s l.val=_
  by_cases low : l.val<L
  · let ell : Fin L := ⟨l.val,low⟩
    have index : L*s.val+(L-1-l.val)=L*(s.val+1)-(l.val+1) := by
      rw [Nat.mul_add,Nat.mul_one]
      omega
    have guard : l.val<L*(s.val+1) := by rw [Nat.mul_add,Nat.mul_one]; omega
    have h := signed k s ell
    change moment k s l.val=(-1:ℂ)^l.val*B k*D.coeff (L*s.val+(L-1-l.val)) at h
    simpa only [if_pos guard,index] using h
  · have endval : l.val=L := by have := l.isLt; omega
    rw [endval,even.neg_one_pow,one_mul,lag]
    by_cases zero : s.val=0
    · simp [zero]
    · let prev : Fin L := ⟨s.val-1,by have := s.isLt; omega⟩
      have pprev : prev.val+1=s.val := by dsimp [prev]; omega
      have index : L*prev.val+(L-1)=L*(s.val+1)-(L+1) := by
        have hmul := congrArg (L*·) pprev
        change L*(prev.val+1)=L*s.val at hmul
        rw [Nat.mul_add,Nat.mul_one] at hmul ⊢
        omega
      have guard : L<L*(s.val+1) := by
        simpa only [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left (show 1<s.val+1 by omega) (by omega : 0<L)
      rw [if_pos guard]
      simp only [if_neg zero]
      change (∑ i,Q k i*pad i prev.val)=_
      simp_rw [padAt]
      let z : Fin L := ⟨0,by omega⟩
      have row0 := signed k prev z
      simpa only [moment,Q,z,pow_zero,one_mul,Nat.add_zero,Nat.sub_zero,index] using row0

end CriticalConic

namespace CriticalConicBoundary

open Arxiv.«0805.3777» Polynomial

/-- Every odd level h≥5 attains its predicted generic rank at the
sharp boundary b=h(h−2)−1. This is the first middle width not covered
by the independent private-pair construction. -/
theorem odd_boundary_rank (h : ℕ) (five : 5≤h) (odd : Odd h) :
    let b := h*(h-2)-1
    let r := 2*b-h
    IsGenericRank [3,b,r-(2*h-5)] r := by
  obtain ⟨k,rfl⟩ := odd
  let L := 2*k
  have four : 4≤L := by dsimp [L]; omega
  have evenL : Even L := ⟨k,by dsimp [L]; omega⟩
  let b := L^2-2
  have tile : (L+1)*(L+1-2)-1=b := by
    have inc := congrArg (fun n : ℕ => (L+1)*n) (show (L+1-2)+1=L by omega)
    have e : (L+1)*(L+1-2)+1=L^2 := by nlinarith only [inc]
    dsimp only [b]
    omega
  have blocks : (L-1)*(L+1)=b+1 := by
    have inc := congrArg (fun n : ℕ => n*(L+1)) (Nat.sub_add_cancel (by omega : 1≤L))
    have e : (L-1)*(L+1)+1=L^2 := by nlinarith only [inc]
    have sq : 2≤L^2 := by nlinarith only [Nat.mul_le_mul_left L four,four]
    dsimp only [b]
    omega
  have room : L+1≤b := by
    have sq : 4*L≤L^2 := by nlinarith only [Nat.mul_le_mul_left L four]
    dsimp only [b]
    omega
  apply CriticalConic.boundary_rank_of_local (2*k+1) five
  rw [show (2*k+1)*(2*k+1-2)-1=b from tile,show 2*k+1-2=L-1 by dsimp [L]; omega]
  obtain ⟨t,powers,poles,det⟩ := physical_nodes four evenL
  have distinct : Function.Injective t := by
    intro i j same
    exact powers (congrArg (fun z : ℂ => z^L) same)
  let M : Matrix (Fin b) (Fin (L+1)) ℂ := fun i j => t i^(L*j.val)
  let Q : Matrix (Fin (L-1)) (Fin b) ℂ := fun j i => t i^((L+1)*j.val)
  apply CriticalConic.local_component t distinct poles M (powers_frame room t powers) Q
  intro f diag mass pole
  obtain ⟨g,B,recovers,mom⟩ := CriticalConic.sharp_boundary_interpolation L four evenL
    t distinct poles f diag mass pole
  let D : ℂ[X] := ∏ i,(X-C (t i))
  have degree : D.natDegree=b := by
    dsimp only [D]
    rw [natDegree_finsetProd_X_sub_C_eq_card,Finset.card_univ,Fintype.card_fin]
  have zero (i : Fin b) : D.eval (t i)=0 := by
    simp only [D,eval_prod,eval_sub,eval_X,eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
  exact recovers (zero_of_nodal_moments blocks (Nat.sub_le _ _) t distinct D degree.le zero g B mom det)

theorem boundary_h7 : IsGenericRank [3,34,52] 61 := odd_boundary_rank 7 (by decide) (by decide)

theorem boundary_h9 : IsGenericRank [3,62,102] 115 := odd_boundary_rank 9 (by decide) (by decide)

end CriticalConicBoundary

namespace ComponentFrontier

open Arxiv.«0805.3777»

/-- On the first width below the quadratic threshold, the parent's clipped
endpoint agrees exactly with the width used by the conic construction. -/
theorem clipped_preceding_endpoint {b h : ℕ} (large : 5 ≤ h) (edge : b+1=h*(h-2)) :
    let r := 2*b-h
    min (2*(b-1)) (r*(b+1)/(b+h))=r-(2*h-5) := by
  intro r
  let d := h-3
  have hd : 2 ≤ d := by dsimp only [d]; omega
  have hh : d+3=h := by dsimp only [d]; omega
  have preceding := CriticalThreeCubic.preceding_endpoint d hd
  dsimp only at preceding
  rw [hh] at preceding
  have bsize : h*d+(d+2)=b := by omega
  rw [bsize] at preceding
  have quotient : r-(2*d+1)=r*(b+1)/(b+h) := preceding.2.2.1
  have qsize : 2*d+1=2*h-5 := by dsimp only [d]; omega
  rw [qsize] at quotient
  rw [←quotient]
  apply Nat.min_eq_right
  dsimp only [r]
  omega

/-- The full odd sharp-boundary family at the exact clipped endpoint of the
registered R3.H2 problem. -/
theorem odd_rank_at_clipped_boundary {b h : ℕ} (large : 5 ≤ h)
    (parity : Odd h) (edge : b+1=h*(h-2)) :
    let r := 2*b-h
    let n := min (2*(b-1)) (r*(b+1)/(b+h))
    IsGenericRank [3,b,n] r := by
  intro r n
  have size : h*(h-2)-1=b := by omega
  have hit := CriticalConicBoundary.odd_boundary_rank h large parity
  dsimp only at hit
  rw [size] at hit
  have same : n=r-(2*h-5) := clipped_preceding_endpoint large edge
  rw [same]
  exact hit

end ComponentFrontier

namespace ComponentFrontier

open Arxiv.«0805.3777»

private theorem five_partition {b n C : ℕ} (u M : Fin C → ℕ)
    (ok : let r := 2*b-5
          10≤b ∧ b≤n ∧ n≤r ∧ 3*b*n ⌈/⌉ (b+n+1)=r ∧ (∑ i,u i)=r-n ∧ (∑ i,M i)=r ∧
          ∀ i, u i≤M i ∧ M i≤r ∧ M i≤u i*(b/5+1)+2*(b/5)-1 ∧
            4*M i≤u i*(b+5) ∧ (5-b%5-1)*M i≤u i*(5-b%5)*(b/5+1)) :
    IsGenericRank [3,b,n] (2*b-5) := by
  obtain ⟨width,ord,nr,count,rows,marks,localFit⟩ := ok
  exact CriticalThreeComponents.rank_of_partition (h:=5) (by decide) (by omega) ord nr (by omega) width
    count u M rows marks localFit

/-- Below the width threshold on level five there are only five possible
maxima. Four follow from explicit component partitions. -/
theorem fifth_below (seed : IsGenericRank [3,14,18] 23) (b : ℕ) (width : 10≤b) (small : b<15) :
    let r := 2*b-5
    IsGenericRank [3,b,min (2*(b-1)) (r*(b+1)/(b+5))] r := by
  interval_cases b
  · exact five_partition (b:=10) (n:=11) (C:=1) ![4] ![15] (by decide)
  · exact five_partition (b:=11) (n:=12) (C:=2) ![3,2] ![10,7] (by decide)
  · exact five_partition (b:=12) (n:=14) (C:=2) ![3,2] ![12,7] (by decide)
  · exact five_partition (b:=13) (n:=16) (C:=3) ![2,2,1] ![9,8,4] (by decide)
  · exact seed

end ComponentFrontier

namespace CriticalHigher.SevenEight

open Arxiv.«0805.3777»

private theorem partition_rank {h b n C : ℕ} (rel marks : Fin C→ℕ)
    (data : let r := 2*b-h
      let d := b/h
      let s := b%h
      2≤h ∧ 3≤b ∧ 2*h≤b ∧ b≤n ∧ n≤r ∧ 3*b*n ⌈/⌉ (b+n+1)=r ∧
      (∑ i, rel i)=r-n ∧ (∑ i,marks i)=r ∧ ∀ i, rel i ≤ marks i ∧ marks i≤r ∧
        marks i≤rel i*(d+1)+2*d-1 ∧ (h-1)*marks i≤rel i*(b+h) ∧
        (h-s-1)*marks i≤rel i*(h-s)*(d+1)) :
    IsGenericRank [3,b,n] (2*b-h) := by
  obtain ⟨hh,hb,width,ord,nr,count,rows,points,fit⟩ := data
  exact CriticalThreeComponents.rank_of_partition hh hb ord nr (by omega) width count
    rel marks rows points fit

private theorem sharp_budget {b n r : ℕ} (positive : 0<r)
    (count : 3*b*n ⌈/⌉ (b+n+1)=r) :
    (b+n+1)*(r-1)<3*b*n ∧ 3*b*n≤(b+n+1)*r := by
  have pos : 0<b+n+1 := by omega
  refine ⟨?_,(ceilDiv_le_iff_le_mul pos).mp count.le⟩
  by_contra! le
  have bad := (ceilDiv_le_iff_le_mul pos).mpr le
  omega

private theorem min_width_seven {b n : ℕ} (hb : 3≤b) (ord : b≤n)
    (exc : (b,n)≠(13,13)) (count : 3*b*n ⌈/⌉ (b+n+1)=2*b-7) : 14≤b := by
  by_contra! low
  have budget := (ceilDiv_le_iff_le_mul (by omega : 0<b+n+1)).mp count.le
  have : b≤13 := by omega
  interval_cases b <;> norm_num at budget exc ⊢ <;> omega

theorem seven_of_seeds
    (at18 : IsGenericRank [3,18,22] 29)
    (at24 : IsGenericRank [3,24,33] 41)
    (at34 : IsGenericRank [3,34,52] 61)
    {b n : ℕ} (hb : 3≤b) (ord : b≤n) (exc : (b,n)≠(13,13))
    (count : 3*b*n ⌈/⌉ (b+n+1)=2*b-7) :
    IsGenericRank [3,b,n] (2*b-7) := by
  have floor := min_width_seven hb ord exc count
  have size : 2*b-7+7=2*b := by omega
  by_cases wide : 35≤b
  · exact CriticalThreeComponents.rank_above_threshold (h:=7) (by decide) ord floor wide size count (by omega)
  obtain ⟨lower,higher⟩ := sharp_budget (show 0<2*b-7 by omega) count
  interval_cases b
  · have ns : n=14 ∨ n=15 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=7) (b:=14) (n:=14) (C:=4) ![1,2,2,2] ![3,7,7,4] (by decide)
    · exact partition_rank (h:=7) (b:=14) (n:=15) (C:=3) ![2,2,2] ![7,7,7] (by decide)
  · have ns : n=16 := by omega
    rcases ns with rfl
    exact partition_rank (h:=7) (b:=15) (n:=16) (C:=2) ![2,5] ![7,16] (by decide)
  · have ns : n=18 := by omega
    rcases ns with rfl
    exact partition_rank (h:=7) (b:=16) (n:=18) (C:=2) ![3,4] ![11,14] (by decide)
  · have ns : n=19 ∨ n=20 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=7) (b:=17) (n:=19) (C:=8) ![1,1,1,1,1,1,1,1] ![4,4,4,4,4,4,2,1] (by decide)
    · exact partition_rank (h:=7) (b:=17) (n:=20) (C:=7) ![1,1,1,1,1,1,1] ![4,4,4,4,4,4,3] (by decide)
  · have ns : n=21 ∨ n=22 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=7) (b:=18) (n:=21) (C:=8) ![1,1,1,1,1,1,1,1] ![4,4,4,4,4,4,4,1] (by decide)
    · exact at18
  · have ns : n=23 := by omega
    rcases ns with rfl
    exact partition_rank (h:=7) (b:=19) (n:=23) (C:=8) ![1,1,1,1,1,1,1,1] ![4,4,4,4,4,4,4,3] (by decide)
  · have ns : n=25 := by omega
    rcases ns with rfl
    exact partition_rank (h:=7) (b:=20) (n:=25) (C:=4) ![2,2,2,2] ![9,9,9,6] (by decide)
  · have ns : n=26 ∨ n=27 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=7) (b:=21) (n:=26) (C:=3) ![3,3,3] ![14,14,7] (by decide)
    · exact partition_rank (h:=7) (b:=21) (n:=27) (C:=3) ![2,3,3] ![9,14,12] (by decide)
  · have ns : n=28 ∨ n=29 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=7) (b:=22) (n:=28) (C:=2) ![4,5] ![19,18] (by decide)
    · exact partition_rank (h:=7) (b:=22) (n:=29) (C:=2) ![4,4] ![19,18] (by decide)
  · have ns : n=30 ∨ n=31 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=7) (b:=23) (n:=30) (C:=9) ![1,1,1,1,1,1,1,1,1] ![5,5,5,5,5,5,5,3,1] (by decide)
    · exact partition_rank (h:=7) (b:=23) (n:=31) (C:=8) ![1,1,1,1,1,1,1,1] ![5,5,5,5,5,5,5,4] (by decide)
  · have ns : n=32 ∨ n=33 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=7) (b:=24) (n:=32) (C:=9) ![1,1,1,1,1,1,1,1,1] ![5,5,5,5,5,5,5,5,1] (by decide)
    · exact at24
  · have ns : n=34 := by omega
    rcases ns with rfl
    exact partition_rank (h:=7) (b:=25) (n:=34) (C:=3) ![3,3,3] ![16,16,11] (by decide)
  · have ns : n=35 ∨ n=36 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=7) (b:=26) (n:=35) (C:=5) ![2,2,2,2,2] ![11,11,11,10,2] (by decide)
    · exact partition_rank (h:=7) (b:=26) (n:=36) (C:=5) ![1,2,2,2,2] ![5,11,11,11,7] (by decide)
  · have ns : n=37 ∨ n=38 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=7) (b:=27) (n:=37) (C:=4) ![2,2,3,3] ![11,11,17,8] (by decide)
    · exact partition_rank (h:=7) (b:=27) (n:=38) (C:=3) ![3,3,3] ![17,17,13] (by decide)
  · have ns : n=39 ∨ n=40 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=7) (b:=28) (n:=39) (C:=2) ![5,5] ![29,20] (by decide)
    · exact partition_rank (h:=7) (b:=28) (n:=40) (C:=2) ![4,5] ![23,26] (by decide)
  · have ns : n=41 ∨ n=42 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=7) (b:=29) (n:=41) (C:=10) ![1,1,1,1,1,1,1,1,1,1] ![6,6,6,6,6,6,6,6,2,1] (by decide)
    · exact partition_rank (h:=7) (b:=29) (n:=42) (C:=9) ![1,1,1,1,1,1,1,1,1] ![6,6,6,6,6,6,6,6,3] (by decide)
  · have ns : n=43 ∨ n=44 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=7) (b:=30) (n:=43) (C:=5) ![1,1,1,1,6] ![6,6,6,6,29] (by decide)
    · exact partition_rank (h:=7) (b:=30) (n:=44) (C:=4) ![1,1,1,6] ![6,6,6,35] (by decide)
  · have ns : n=45 ∨ n=46 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=7) (b:=31) (n:=45) (C:=4) ![1,3,3,3] ![6,19,19,11] (by decide)
    · exact partition_rank (h:=7) (b:=31) (n:=46) (C:=3) ![3,3,3] ![19,19,17] (by decide)
  · have ns : n=47 ∨ n=48 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=7) (b:=32) (n:=47) (C:=5) ![2,2,2,2,2] ![13,13,13,13,5] (by decide)
    · exact partition_rank (h:=7) (b:=32) (n:=48) (C:=5) ![1,2,2,2,2] ![6,13,13,13,12] (by decide)
  · have ns : n=49 ∨ n=50 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=7) (b:=33) (n:=49) (C:=4) ![2,2,3,3] ![13,13,20,13] (by decide)
    · exact partition_rank (h:=7) (b:=33) (n:=50) (C:=3) ![3,3,3] ![20,20,19] (by decide)
  · have ns : n=51 ∨ n=52 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=7) (b:=34) (n:=51) (C:=3) ![3,3,4] ![20,20,21] (by decide)
    · exact at34

private theorem min_width_eight {b n : ℕ} (hb : 3≤b) (ord : b≤n)
    (exc : (b,n)≠(15,15)) (count : 3*b*n ⌈/⌉ (b+n+1)=2*b-8) : 16≤b := by
  by_contra! low
  have budget := (ceilDiv_le_iff_le_mul (by omega : 0<b+n+1)).mp count.le
  have : b≤15 := by omega
  interval_cases b <;> norm_num at budget exc ⊢ <;> omega

theorem eight_of_seeds
    (at23 : IsGenericRank [3,23,29] 38)
    (at47 : IsGenericRank [3,47,75] 86)
    {b n : ℕ} (hb : 3≤b) (ord : b≤n) (exc : (b,n)≠(15,15))
    (count : 3*b*n ⌈/⌉ (b+n+1)=2*b-8) :
    IsGenericRank [3,b,n] (2*b-8) := by
  have floor := min_width_eight hb ord exc count
  have size : 2*b-8+8=2*b := by omega
  by_cases wide : 48≤b
  · exact CriticalThreeComponents.rank_above_threshold (h:=8) (by decide) ord floor wide size count (by omega)
  obtain ⟨lower,higher⟩ := sharp_budget (show 0<2*b-8 by omega) count
  interval_cases b
  · have ns : n=16 ∨ n=17 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=8) (b:=16) (n:=16) (C:=2) ![3,5] ![10,14] (by decide)
    · exact partition_rank (h:=8) (b:=16) (n:=17) (C:=1) ![7] ![24] (by decide)
  · have ns : n=18 := by omega
    rcases ns with rfl
    exact partition_rank (h:=8) (b:=17) (n:=18) (C:=4) ![2,2,2,2] ![7,7,7,5] (by decide)
  · have ns : n=20 := by omega
    rcases ns with rfl
    exact partition_rank (h:=8) (b:=18) (n:=20) (C:=4) ![2,2,2,2] ![7,7,7,7] (by decide)
  · have ns : n=21 ∨ n=22 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=8) (b:=19) (n:=21) (C:=3) ![3,3,3] ![11,11,8] (by decide)
    · exact partition_rank (h:=8) (b:=19) (n:=22) (C:=2) ![4,4] ![15,15] (by decide)
  · have ns : n=23 ∨ n=24 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=8) (b:=20) (n:=23) (C:=9) ![1,1,1,1,1,1,1,1,1] ![4,4,4,4,4,4,4,3,1] (by decide)
    · exact partition_rank (h:=8) (b:=20) (n:=24) (C:=8) ![1,1,1,1,1,1,1,1] ![4,4,4,4,4,4,4,4] (by decide)
  · have ns : n=25 := by omega
    rcases ns with rfl
    exact partition_rank (h:=8) (b:=21) (n:=25) (C:=9) ![1,1,1,1,1,1,1,1,1] ![4,4,4,4,4,4,4,4,2] (by decide)
  · have ns : n=26 ∨ n=27 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=8) (b:=22) (n:=26) (C:=10) ![1,1,1,1,1,1,1,1,1,1] ![4,4,4,4,4,4,4,4,3,1] (by decide)
    · exact partition_rank (h:=8) (b:=22) (n:=27) (C:=9) ![1,1,1,1,1,1,1,1,1] ![4,4,4,4,4,4,4,4,4] (by decide)
  · have ns : n=28 ∨ n=29 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=8) (b:=23) (n:=28) (C:=10) ![1,1,1,1,1,1,1,1,1,1] ![4,4,4,4,4,4,4,4,4,2] (by decide)
    · exact at23
  · have ns : n=30 ∨ n=31 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=8) (b:=24) (n:=30) (C:=5) ![2,2,2,2,2] ![9,9,9,9,4] (by decide)
    · exact partition_rank (h:=8) (b:=24) (n:=31) (C:=2) ![2,7] ![9,31] (by decide)
  · have ns : n=32 ∨ n=33 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=8) (b:=25) (n:=32) (C:=4) ![2,2,3,3] ![9,9,14,10] (by decide)
    · exact partition_rank (h:=8) (b:=25) (n:=33) (C:=3) ![3,3,3] ![14,14,14] (by decide)
  · have ns : n=34 := by omega
    rcases ns with rfl
    exact partition_rank (h:=8) (b:=26) (n:=34) (C:=2) ![5,5] ![24,20] (by decide)
  · have ns : n=36 := by omega
    rcases ns with rfl
    exact partition_rank (h:=8) (b:=27) (n:=36) (C:=10) ![1,1,1,1,1,1,1,1,1,1] ![5,5,5,5,5,5,5,5,5,1] (by decide)
  · have ns : n=37 ∨ n=38 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=8) (b:=28) (n:=37) (C:=11) ![1,1,1,1,1,1,1,1,1,1,1] ![5,5,5,5,5,5,5,5,5,2,1] (by decide)
    · exact partition_rank (h:=8) (b:=28) (n:=38) (C:=10) ![1,1,1,1,1,1,1,1,1,1] ![5,5,5,5,5,5,5,5,5,3] (by decide)
  · have ns : n=39 ∨ n=40 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=8) (b:=29) (n:=39) (C:=5) ![1,1,1,4,4] ![5,5,5,21,14] (by decide)
    · exact partition_rank (h:=8) (b:=29) (n:=40) (C:=4) ![1,1,4,4] ![5,5,21,19] (by decide)
  · have ns : n=41 ∨ n=42 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=8) (b:=30) (n:=41) (C:=5) ![1,1,3,3,3] ![5,5,16,16,10] (by decide)
    · exact partition_rank (h:=8) (b:=30) (n:=42) (C:=4) ![1,3,3,3] ![5,16,16,15] (by decide)
  · have ns : n=43 ∨ n=44 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=8) (b:=31) (n:=43) (C:=6) ![1,2,2,2,2,2] ![5,11,11,11,11,5] (by decide)
    · exact partition_rank (h:=8) (b:=31) (n:=44) (C:=5) ![2,2,2,2,2] ![11,11,11,11,10] (by decide)
  · have ns : n=45 ∨ n=46 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=8) (b:=32) (n:=45) (C:=4) ![2,3,3,3] ![11,17,17,11] (by decide)
    · exact partition_rank (h:=8) (b:=32) (n:=46) (C:=2) ![3,7] ![17,39] (by decide)
  · have ns : n=47 ∨ n=48 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=8) (b:=33) (n:=47) (C:=2) ![5,6] ![29,29] (by decide)
    · exact partition_rank (h:=8) (b:=33) (n:=48) (C:=2) ![5,5] ![29,29] (by decide)
  · have ns : n=49 ∨ n=50 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=8) (b:=34) (n:=49) (C:=11) ![1,1,1,1,1,1,1,1,1,1,1] ![6,6,6,6,6,6,6,6,6,5,1] (by decide)
    · exact partition_rank (h:=8) (b:=34) (n:=50) (C:=10) ![1,1,1,1,1,1,1,1,1,1] ![6,6,6,6,6,6,6,6,6,6] (by decide)
  · have ns : n=50 ∨ n=51 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=8) (b:=35) (n:=50) (C:=12) ![1,1,1,1,1,1,1,1,1,1,1,1] ![6,6,6,6,6,6,6,6,6,6,1,1] (by decide)
    · exact partition_rank (h:=8) (b:=35) (n:=51) (C:=11) ![1,1,1,1,1,1,1,1,1,1,1] ![6,6,6,6,6,6,6,6,6,6,2] (by decide)
  · have ns : n=52 ∨ n=53 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=8) (b:=36) (n:=52) (C:=3) ![4,4,4] ![25,25,14] (by decide)
    · exact partition_rank (h:=8) (b:=36) (n:=53) (C:=5) ![1,1,1,4,4] ![6,6,6,25,21] (by decide)
  · have ns : n=54 ∨ n=55 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=8) (b:=37) (n:=54) (C:=4) ![3,3,3,3] ![19,19,19,9] (by decide)
    · exact partition_rank (h:=8) (b:=37) (n:=55) (C:=3) ![3,3,5] ![19,19,28] (by decide)
  · have ns : n=56 ∨ n=57 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=8) (b:=38) (n:=56) (C:=6) ![2,2,2,2,2,2] ![13,13,13,13,13,3] (by decide)
    · exact partition_rank (h:=8) (b:=38) (n:=57) (C:=6) ![1,2,2,2,2,2] ![6,13,13,13,13,10] (by decide)
  · have ns : n=58 ∨ n=59 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=8) (b:=39) (n:=58) (C:=4) ![3,3,3,3] ![20,20,20,10] (by decide)
    · exact partition_rank (h:=8) (b:=39) (n:=59) (C:=4) ![2,3,3,3] ![13,20,20,17] (by decide)
  · have ns : n=60 ∨ n=61 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=8) (b:=40) (n:=60) (C:=2) ![6,6] ![41,31] (by decide)
    · exact partition_rank (h:=8) (b:=40) (n:=61) (C:=2) ![5,6] ![34,38] (by decide)
  · have ns : n=62 ∨ n=63 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=8) (b:=41) (n:=62) (C:=12) ![1,1,1,1,1,1,1,1,1,1,1,1] ![7,7,7,7,7,7,7,7,7,7,3,1] (by decide)
    · exact partition_rank (h:=8) (b:=41) (n:=63) (C:=11) ![1,1,1,1,1,1,1,1,1,1,1] ![7,7,7,7,7,7,7,7,7,7,4] (by decide)
  · have ns : n=64 ∨ n=65 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=8) (b:=42) (n:=64) (C:=6) ![1,1,1,1,1,7] ![7,7,7,7,7,41] (by decide)
    · exact partition_rank (h:=8) (b:=42) (n:=65) (C:=5) ![1,1,1,1,7] ![7,7,7,7,48] (by decide)
  · have ns : n=66 ∨ n=67 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=8) (b:=43) (n:=66) (C:=3) ![4,4,4] ![29,29,20] (by decide)
    · exact partition_rank (h:=8) (b:=43) (n:=67) (C:=2) ![4,7] ![29,49] (by decide)
  · have ns : n=68 ∨ n=69 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=8) (b:=44) (n:=68) (C:=4) ![3,3,3,3] ![22,22,22,14] (by decide)
    · exact partition_rank (h:=8) (b:=44) (n:=69) (C:=3) ![3,3,5] ![22,22,36] (by decide)
  · have ns : n=70 ∨ n=71 := by omega
    rcases ns with rfl | rfl
    · exact partition_rank (h:=8) (b:=45) (n:=70) (C:=6) ![2,2,2,2,2,2] ![15,15,15,15,15,7] (by decide)
    · exact partition_rank (h:=8) (b:=45) (n:=71) (C:=6) ![1,2,2,2,2,2] ![7,15,15,15,15,15] (by decide)
  · have ns : n=71 ∨ n=72 ∨ n=73 := by omega
    rcases ns with rfl | rfl | rfl
    · exact partition_rank (h:=8) (b:=46) (n:=71) (C:=5) ![2,2,3,3,3] ![15,15,23,23,8] (by decide)
    · exact partition_rank (h:=8) (b:=46) (n:=72) (C:=4) ![3,3,3,3] ![23,23,23,15] (by decide)
    · exact partition_rank (h:=8) (b:=46) (n:=73) (C:=4) ![2,3,3,3] ![15,23,23,23] (by decide)
  · have ns : n=73 ∨ n=74 ∨ n=75 := by omega
    rcases ns with rfl | rfl | rfl
    · exact partition_rank (h:=8) (b:=47) (n:=73) (C:=3) ![4,4,5] ![31,31,24] (by decide)
    · exact partition_rank (h:=8) (b:=47) (n:=74) (C:=3) ![4,4,4] ![31,31,24] (by decide)
    · exact at47

end CriticalHigher.SevenEight

namespace CriticalThreeCubic

/-- The concave quadratic attains its integer maximum at either of the two
integers adjacent to its real vertex. -/
private lemma adjacent_product_bound (l d : ℤ) : l*(2*d+1-l) ≤ d*(d+1) := by
  by_cases h : l ≤ d
  · nlinarith only [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ d+1-l by omega)]
  · nlinarith only [mul_nonneg (show 0 ≤ l-d by omega) (show 0 ≤ l-d-1 by omega)]

/-- Capacity inequalities for the two packets. In the last two residue
classes, one or two marks move from the second packet to the first. -/
private lemma bulk_integer_bounds {h d s : ℤ} (hh : 8 ≤ h) (hd : 2 ≤ d) (depth : d+3 ≤ h)
    (s0 : 0 ≤ s) (sh : s<h) (nextRow : s+2=h → d+4 ≤ h) (last : s+1=h → d+5 ≤ h) :
    let b := h*d+s
    let e := max 0 (s-(h-3))
    let ok (u m : ℤ) := u ≤ m ∧ m ≤ 2*b-h ∧ m ≤ u*(d+1)+2*d-1 ∧
      (h-1)*m ≤ u*(b+h) ∧ (h-s-1)*m ≤ u*(h-s)*(d+1)
    ok (h-3) (b-h+e) ∧ ok (h-2) (b-e) := by
  intro b e ok
  let l := h-s
  have lpos : 1 ≤ l := by dsimp only [l]; omega
  have shifts : (e=0 ∧ s+3 ≤ h) ∨ (e=1 ∧ s+2=h ∧ d+4 ≤ h) ∨ (e=2 ∧ s+1=h ∧ d+5 ≤ h) := by
    by_cases light : s+3 ≤ h
    · exact Or.inl ⟨max_eq_left (by omega),light⟩
    · have eq : e=s-(h-3) := max_eq_right (by omega)
      by_cases mid : s+2=h
      · exact Or.inr (Or.inl ⟨by omega,mid,nextRow mid⟩)
      · have edge : s+1=h := by omega
        exact Or.inr (Or.inr ⟨by omega,edge,last edge⟩)
  have small : 0 ≤ e ∧ e ≤ 2 := by rcases shifts with c|c|c <;> omega
  have width₁ : s+e ≤ 2*h-d-4 := by rcases shifts with c|c|c <;> omega
  have width₂ : s-e ≤ h-3 := by rcases shifts with c|c|c <;> omega
  have cost : (l-1)*e ≤ 2 := by
    rcases shifts with c|c|c
    · rw [c.1,mul_zero]; decide
    · rw [c.1,mul_one]; dsimp only [l]; omega
    · rw [c.1]; dsimp only [l]; omega
  have deep : 0 ≤ h*(h-d-3) := mul_nonneg (by omega) (by omega)
  have tail : h*(h-2)-b = h*(h-d-3)+l := by dsimp only [b,l]; ring
  have T₀ : 0 ≤ h*(h-2)-b := by omega
  have shift : e*(h-1) ≤ 2*(h*(h-2)-b) := by
    rw [tail]
    rcases shifts with c|c|c
    · rw [c.1,zero_mul]; omega
    · have big : h ≤ h*(h-d-3) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (by omega : 1 ≤ h-d-3) (by omega : 0 ≤ h)
      rw [c.1,one_mul]; omega
    · have big : h ≤ h*(h-d-3) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (by omega : 1 ≤ h-d-3) (by omega : 0 ≤ h)
      rw [c.1]; omega
  have delta₁ : (l-1)*e ≤ h*d+l*(l+h-4-3*d) := by
    have bound := adjacent_product_bound l d
    have spare : d*(d+1)+2 ≤ h*d := by
      nlinarith only [hd,mul_nonneg (show 0 ≤ h-d-3 by omega) (show 0 ≤ d by omega)]
    have extra : 0 ≤ l*(h-d-3) := mul_nonneg (by omega) (by omega)
    nlinarith only [bound,spare,extra,cost]
  have delta₂ : 0 ≤ h*(d+1)+l*(l-3-2*d) := by
    have bound := adjacent_product_bound l (d+1)
    nlinarith only [bound,mul_nonneg (show 0 ≤ h-d-2 by omega) (show 0 ≤ d+1 by omega)]
  have enough : 2*h ≤ b := by
    dsimp only [b]
    nlinarith only [s0,mul_nonneg (show 0 ≤ h by omega) (show 0 ≤ d-2 by omega)]
  refine ⟨⟨by omega,by omega,?_,?_,?_⟩,⟨by omega,by omega,?_,?_,?_⟩⟩
  · dsimp only [b]; nlinarith only [width₁]
  · nlinarith only [shift]
  · dsimp only [l] at delta₁
    dsimp only [b]
    nlinarith only [delta₁]
  · dsimp only [b]; nlinarith only [width₂]
  · nlinarith only [T₀,mul_nonneg (show 0 ≤ h-1 by omega) small.1]
  · have ez := mul_nonneg (show 0 ≤ l-1 by omega) small.1
    dsimp only [l] at delta₂ ez
    dsimp only [b]
    nlinarith only [delta₂,ez]

end CriticalThreeCubic

namespace CriticalThreeCubic

/-- Convert the five capacity inequalities to their natural-number versions
before applying the exact balanced-hub allocation criterion. -/
private lemma bulk_realizes_bounds {h d s b r : ℕ} (hh : 8 ≤ h) (hd : 2 ≤ d) (hs : s<h)
    (base : b=h*d+s) (points : r=2*b-h) (enough : 2*h ≤ b) (u M : ℕ)
    (bounds : (u:ℤ) ≤ M ∧ (M:ℤ) ≤ 2*(b:ℤ)-h ∧
      (M:ℤ) ≤ (u:ℤ)*((d:ℤ)+1)+2*d-1 ∧ ((h:ℤ)-1)*M ≤ (u:ℤ)*((b:ℤ)+h) ∧
      ((h:ℤ)-s-1)*M ≤ (u:ℤ)*((h:ℤ)-s)*((d:ℤ)+1)) :
    let g (j : Fin h) := if j.val<s then d else d-1
    u ≤ M ∧ ∃ take : Fin h → ℕ, (∑ j, take j)=M ∧
      ∀ j, take j ≤ 2*g j+1 ∧ M-take j ≤ u*(g j+2) := by
  intro g
  obtain ⟨low,hi,width,volume,short⟩ := bounds
  have rCast : (r:ℤ)=2*(b:ℤ)-h := by clear * - points enough; omega
  have maximum : (M:ℤ) ≤ r := hi.trans_eq rCast.symm
  refine ⟨by exact_mod_cast low,
    (component_marks_iff (h:=h) (d:=d) (s:=s) (u:=u) (M:=M) (by omega) (by omega) hs).mpr ?_⟩
  rw [←base,←points]
  refine ⟨by exact_mod_cast maximum,?_,?_,?_⟩
  · zify [show 1 ≤ u*(d+1)+2*d by clear * - hd; omega]
    exact width
  · zify [show 1 ≤ h by omega]
    exact volume
  · zify [show 1 ≤ h-s by omega,hs.le]
    exact short

/-- The two fixed packets and their balanced-hub allocations at the first
relation count. The shift is zero except in the top two residues. -/
lemma three_quarter_two_packets {h d s b r : ℕ} (hh : 8 ≤ h) (hd : 2 ≤ d) (range : d ≤ h-3)
    (hs : s<h) (base : b=h*d+s) (points : r=2*b-h)
    (ex₁ : ¬(d=h-3 ∧ s=h-2)) (ex₂ : ¬(d=h-3 ∧ s=h-1)) (ex₃ : ¬(d=h-4 ∧ s=h-1)) :
    let g (j : Fin h) := if j.val<s then d else d-1
    let e := s-(h-3)
    let rel : Fin 2 → ℕ := ![h-3,h-2]
    let marks : Fin 2 → ℕ := ![b-h+e,b-e]
    (∑ i, rel i)=2*h-5 ∧ (∑ i, marks i)=r ∧ ∀ i, 0<rel i ∧ rel i ≤ marks i ∧
      ∃ take : Fin h → ℕ, (∑ j, take j)=marks i ∧
        ∀ j, take j ≤ 2*g j+1 ∧ marks i-take j ≤ rel i*(g j+2) := by
  intro g e rel marks
  have room : 2*h ≤ b := by
    have t := Nat.mul_le_mul_left h hd
    omega
  have shift : e ≤ 2 := by dsimp only [e]; omega
  have ccB : (b:ℤ)=(h:ℤ)*d+s := by exact_mod_cast base
  have ccE : (e:ℤ)=max 0 ((s:ℤ)-((h:ℤ)-3)) := by
    dsimp only [e]
    by_cases light : s ≤ h-3
    · rw [max_eq_left (by omega)]; omega
    · rw [max_eq_right (by omega)]; omega
  have nextDepth : s+2=h → d+4 ≤ h := by clear * - range ex₁ hh; omega
  have lastDepth : s+1=h → d+5 ≤ h := by clear * - range ex₂ ex₃ hh; omega
  have raw := bulk_integer_bounds (h:=(h:ℤ)) (d:=(d:ℤ)) (s:=(s:ℤ))
    (by exact_mod_cast hh) (by exact_mod_cast hd) (by clear * - range hh; omega)
    (Int.natCast_nonneg s) (by exact_mod_cast hs)
    (fun he => by exact_mod_cast nextDepth (by exact_mod_cast he))
    (fun he => by exact_mod_cast lastDepth (by exact_mod_cast he))
  dsimp only at raw
  rw [←ccB,←ccE] at raw
  have first := bulk_realizes_bounds hh hd hs base points room (h-3) (b-h+e) (by
    have hu : ((h-3:ℕ):ℤ)=(h:ℤ)-3 := by clear * - hh; omega
    have hm : ((b-h+e:ℕ):ℤ)=(b:ℤ)-h+e := by clear * - room; omega
    simpa only [hu,hm] using raw.1)
  have second := bulk_realizes_bounds hh hd hs base points room (h-2) (b-e) (by
    have hu : ((h-2:ℕ):ℤ)=(h:ℤ)-2 := by clear * - hh; omega
    have hm : ((b-e:ℕ):ℤ)=(b:ℤ)-e := by clear * - hh shift room; omega
    simpa only [hu,hm] using raw.2)
  refine ⟨?_,?_,?_⟩
  · rw [Fin.sum_univ_two]
    change h-3+(h-2)=2*h-5
    clear * - hh
    omega
  · rw [Fin.sum_univ_two]
    change b-h+e+(b-e)=r
    clear * - room shift points hh
    omega
  · intro i
    fin_cases i
    · exact ⟨by change 0<h-3; clear * - hh; omega,first⟩
    · exact ⟨by change 0<h-2; clear * - hh; omega,second⟩

/-- For every admissible relation count at or above `2h-5`, the two balanced
packets cover the bulk of the first plateau. -/
lemma three_quarter_bulk {h d s b r q : ℕ} (hh : 8 ≤ h) (hd : 2 ≤ d) (range : d ≤ h-3)
    (hs : s<h) (base : b=h*d+s) (points : r=2*b-h) (more : 2*h-5 ≤ q) (limit : q ≤ r)
    (ex₁ : ¬(d=h-3 ∧ s=h-2)) (ex₂ : ¬(d=h-3 ∧ s=h-1)) (ex₃ : ¬(d=h-4 ∧ s=h-1)) :
    let g (j : Fin h) := if j.val<s then d else d-1
    ∃ G : ℕ, ∃ rel marks : Fin G → ℕ, (∑ i,rel i)=q ∧ (∑ i,marks i)=r ∧
      ∀ i, 0<rel i ∧ rel i ≤ marks i ∧ ∃ take : Fin h → ℕ,
        (∑ j,take j)=marks i ∧ ∀ j, take j ≤ 2*g j+1 ∧ marks i-take j ≤ rel i*(g j+2) := by
  intro g
  apply increase_relations g more limit
  exact ⟨2,![h-3,h-2],![b-h+(s-(h-3)),b-(s-(h-3))],
    three_quarter_two_packets hh hd range hs base points ex₁ ex₂ ex₃⟩

end CriticalThreeCubic

namespace CriticalThreeCubic

/-- The four relation counts differ by at most one and all stay below
the half-width cutoff. -/
theorem four_relation_counts {h : ℕ} (hh : 8≤h) :
    ∃ u : Fin 4 → ℕ, (∑ i,u i)=2*h-5 ∧ (∀ i,0<u i ∧ 2*u i≤h-1) ∧ ∀ i j,u i≤u j+1 := by
  let u (i : Fin 4) := (2*h-5+i.val)/4
  refine ⟨u,?_,?_,?_⟩
  · rw [Fin.sum_univ_four]
    change (2*h-5+0)/4+(2*h-5+1)/4+(2*h-5+2)/4+(2*h-5+3)/4=2*h-5
    omega
  · intro i
    dsimp only [u]
    have := i.isLt
    omega
  · intro i j
    dsimp only [u]
    have := i.isLt
    have := j.isLt
    omega

private theorem four_local {h d s u M : ℕ} (hh : 8≤h)
    (regime : (d=h-3 ∧ s=h-2) ∨ (d=h-4 ∧ s=h-1)) (small : 2*u≤h-1)
    (within : M≤2*(h*d+s)-h) (quota : M+1≤(d+3)*u) :
    let g (j : Fin h) := if j.val<s then d else d-1
    ∃ e : Fin h → ℕ, (∑ j,e j)=M ∧ ∀ j, e j≤2*g j+1 ∧ M-e j≤u*(g j+2) := by
  have params : 1≤d ∧ s<h ∧ u≤d ∧ d+s+5=2*h ∧ (h-s=1 ∨ h-s=2) := by
    rcases regime with ⟨d₀,s₀⟩ | ⟨d₀,s₀⟩ <;> omega
  obtain ⟨hd,hs,ud,ds,shorts⟩ := params
  apply (component_marks_iff (M:=M) (u:=u) (by omega : 2≤h) hd hs).mpr
  have width : (d+3)*u≤u*(d+1)+2*d := by nlinarith only [ud]
  have split := congrArg (fun k : ℕ => k*(d+3)) (show h-1+1=h by omega)
  have rate : (h-1)*(d+3)=h*d+s+h+2 := by nlinarith only [split,ds]
  have volume := Nat.mul_le_mul_left (h-1) quota
  have right : (h-1)*((d+3)*u)=u*(h*d+s+h)+2*u := by
    rw [← Nat.mul_assoc,rate]
    ring
  rw [right,Nat.mul_add,Nat.mul_one] at volume
  refine ⟨within,by omega,by omega,?_⟩
  rcases shorts with single | double
  · simp [single]
  · have ample := Nat.mul_le_mul_right u (show d+3≤2*(d+1) by omega)
    have cover : M≤u*2*(d+1) := by nlinarith only [quota,ample]
    simpa only [double,show 2-1=1 by decide,Nat.one_mul] using cover

/-- For either exceptional residue the base `2*h-5` relations fit in
exactly four near-equal groups. Each group uses balanced long and short hubs. -/
theorem four_packet_packing {h d s b r : ℕ} (hh : 8≤h) (base : b=h*d+s) (points : r=2*b-h)
    (regime : (d=h-3 ∧ s=h-2) ∨ (d=h-4 ∧ s=h-1)) :
    let g (j : Fin h) := if j.val<s then d else d-1
    ∃ rel marks : Fin 4 → ℕ, (∑ i,rel i)=2*h-5 ∧ (∑ i,marks i)=r ∧
      ∀ i, 0<rel i ∧ 2*rel i≤h-1 ∧ rel i ≤ marks i ∧ ∃ e : Fin h → ℕ,
        (∑ j,e j)=marks i ∧ ∀ j,e j≤2*g j+1 ∧ marks i-e j≤rel i*(g j+2) := by
  intro g
  obtain ⟨rel,total,size,_⟩ := four_relation_counts hh
  let fee (i : Fin 4) := if d=h-3 then 1 else if i=0 then 1 else 2
  let marks (i : Fin 4) := (d+3)*rel i-fee i
  have fee_range (i : Fin 4) : 1≤fee i ∧ fee i≤2 := by
    dsimp only [fee]
    split_ifs <;> decide
  have feasible (i : Fin 4) : rel i+fee i≤(d+3)*rel i := by
    have atLeast : 2≤2*rel i := by have := (size i).1; omega
    nlinarith only [(fee_range i).2,atLeast,Nat.zero_le (d*rel i)]
  have booked (i : Fin 4) : marks i+fee i=(d+3)*rel i := by
    exact Nat.sub_add_cancel (by have := feasible i; omega)
  have balanced : (∑ i,marks i)+(∑ i,fee i)=(d+3)*(2*h-5) := by
    rw [← Finset.sum_add_distrib,← total,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => booked i)
  have fees : (∑ i,fee i) = if d=h-3 then 4 else 7 := by
    by_cases first : d=h-3
    · simp [fee,first]
    · simp only [Fin.sum_univ_four,fee,if_neg first]
      decide
  have dpos : 1≤d := by rcases regime with ⟨_,_⟩ | ⟨_,_⟩ <;> omega
  have hb : h≤b := by
    have step := Nat.mul_le_mul_left h dpos
    rw [Nat.mul_one] at step
    omega
  have rk : r+h=2*b := by rw [points,Nat.sub_add_cancel (by omega)]
  have target : r+(if d=h-3 then 4 else 7)=(d+3)*(2*h-5) := by
    have sum := congrArg (fun n : ℕ => (d+3)*n) (show (2*h-5)+5=2*h by omega)
    rcases regime with ⟨d₀,s₀⟩ | ⟨d₀,s₀⟩
    · rw [if_pos d₀]
      have dh : d+3=h := by omega
      have sh : s+2=h := by omega
      nlinarith only [rk,base,dh,sh,sum]
    · rw [if_neg (show d≠h-3 by omega)]
      have dh : d+4=h := by omega
      have sh : s+1=h := by omega
      nlinarith only [rk,base,dh,sh,sum]
  rw [fees,← target] at balanced
  have marks_sum : (∑ i,marks i)=r := Nat.add_right_cancel balanced
  refine ⟨rel,marks,total,marks_sum,?_⟩
  intro i
  have fit := feasible i
  have cost := booked i
  have low := (fee_range i).1
  have within : marks i≤r := by
    rw [← marks_sum]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (marks j)) (Finset.mem_univ i)
  refine ⟨(size i).1,(size i).2,by omega,?_⟩
  apply four_local hh regime (size i).2 _ (by omega)
  simpa only [points,base] using within

/-- Lift the four-component base packing to every larger allowable number
of relations, in the form used by the component tangent construction. -/
theorem three_quarter_four_packets {h d s b r q : ℕ} (hh : 8≤h) (base : b=h*d+s)
    (points : r=2*b-h) (more : 2*h-5≤q) (limit : q≤r)
    (regime : (d=h-3 ∧ s=h-2) ∨ (d=h-4 ∧ s=h-1)) :
    let g (i : Fin h) := if i.val<s then d else d-1
    ∃ G : ℕ, ∃ rel marks : Fin G → ℕ, (∑ i,rel i)=q ∧ (∑ i,marks i)=r ∧
      ∀ i, 0<rel i ∧ rel i ≤ marks i ∧ ∃ e : Fin h → ℕ,
        (∑ j,e j)=marks i ∧ ∀ j,e j≤2*g j+1 ∧ marks i-e j≤rel i*(g j+2) := by
  intro g
  obtain ⟨rel,marks,rows,sum_marks,assign⟩ := four_packet_packing hh base points regime
  apply increase_relations g more limit
  exact ⟨4,rel,marks,rows,sum_marks,fun i => ⟨(assign i).1,(assign i).2.2.1,(assign i).2.2.2⟩⟩

end CriticalThreeCubic

namespace CriticalThreeQuarter

open Arxiv.«0805.3777»

/-- Above the first change in the relation count, every admissible third
width has at least 2h−5 relations. -/
theorem plate_budget {h b n r : ℕ} (hh : 8≤h) (level : r+h=2*b)
    (threshold : 3*h^2<4*b+7*h) (count : 3*b*n ⌈/⌉ (b+n+1)=r) :
    n≤r ∧ 2*h-5≤r-n := by
  have mass := (ceilDiv_le_iff_le_mul (by omega : 0<b+n+1)).mp count.le
  have product := congrArg (fun x : ℕ => x*n) level
  have bound : n*(b+h)≤r*(b+1) := by nlinarith only [mass,product]
  have nr := Nat.le_of_mul_le_mul_right
    (bound.trans (Nat.mul_le_mul_left r (show b+1≤b+h by omega))) (by omega : 0<b+h)
  refine ⟨nr,?_⟩
  have used := congrArg (fun x : ℕ => x*(b+h)) (Nat.sub_add_cancel nr)
  have smaller := congrArg (fun x : ℕ => x*r) (Nat.sub_add_cancel (by omega : 1≤h))
  have capacity : (h-1)*r≤(r-n)*(b+h) := by nlinarith only [bound,used,smaller]
  by_contra! low
  have bad := Nat.mul_le_mul_right (b+h) (show r-n≤2*h-6 by omega)
  have gap := congrArg (fun x : ℕ => x*(b+h)) (Nat.sub_add_cancel (by omega : 6≤2*h))
  have times := congrArg (fun x : ℕ => h*x) level
  nlinarith only [bad,capacity,smaller,gap,times,level,threshold]

/-- A packing certificate tested at the least permitted relation count
also works at the actual third dimension. -/
theorem rank_of_balanced_packing {h b d s n r : ℕ} (hh : 8≤h) (hd : 2≤d)
    (hs : s<h) (base : b=h*d+s) (size : 2*h≤b) (ord : b≤n) (nr : n≤r)
    (level : r+h=2*b) (count : 3*b*n ⌈/⌉ (b+n+1)=r)
    (plan : let g (i : Fin h) := if i.val<s then d else d-1
      ∃ G : ℕ, ∃ u M : Fin G→ℕ, (∑ c,u c)=r-n ∧ (∑ c,M c)=r ∧
      ∀ c,0<u c ∧ u c≤M c ∧ ∃ e : Fin h→ℕ, (∑ i,e i)=M c ∧
        ∀ i,e i≤2*g i+1 ∧ M c-e i≤u c*(g i+2)) : IsGenericRank [3,b,n] r := by
  obtain ⟨G,u,M,rows,marks,each⟩ := plan
  have total := (CriticalThreeCubic.hub_totals hs.le (by omega : 1≤d)).1
  rw [←base] at total
  refine CriticalLastSlice.TwoPlanes.generic_rank_of_witness (by decide) (by omega) ord ?_ ?_
  · simpa only [show 3+b+n-2=b+n+1 by omega] using count.symm
  · apply CriticalThreeComponents.tangent_of_components (by omega : h≤b) nr level u M
      rows marks (fun c => (each c).2.1)
    intro c
    obtain ⟨e,tot,fit⟩ := (each c).2.2
    exact ⟨_,e,total,tot,fit⟩

end CriticalThreeQuarter

namespace CriticalThreeQuarter

open Arxiv.«0805.3777»

/-- On the upper three quarters threshold, only the width immediately
below h(h−2) can obstruct the independent components. The conic theorem
already covers that width for odd h. -/
theorem rank_in_upper_range {h b n r : ℕ} (hh : 8≤h) (order : b≤n) (minWidth : 2*h≤b)
    (above : 3*h^2<4*b+7*h) (level : r+h=2*b)
    (count : 3*b*n ⌈/⌉ (b+n+1)=r) (edge : b+1≠h*(h-2)) :
    IsGenericRank [3,b,n] r := by
  by_cases wide : h*(h-2)≤b
  · exact CriticalThreeComponents.rank_above_threshold (by omega) order minWidth wide level count
      (by omega)
  let d := b/h
  let s := b%h
  have pos : 0<h := by omega
  have hd : 2≤d := (Nat.le_div_iff_mul_le pos).mpr minWidth
  have hs : s<h := Nat.mod_lt b pos
  have base : b=h*d+s := (Nat.div_add_mod b h).symm
  have low : d≤h-3 := by
    have small := (Nat.div_lt_iff_lt_mul pos).mpr
      (show b<(h-2)*h by rw [Nat.mul_comm]; omega)
    change d<h-2 at small
    omega
  have rank : r=2*b-h := by omega
  have budget := plate_budget hh level above count
  apply rank_of_balanced_packing hh hd hs base minWidth order budget.1 level count
  by_cases four₁ : d=h-3 ∧ s=h-2
  · exact CriticalThreeCubic.three_quarter_four_packets hh base rank budget.2 (Nat.sub_le _ _)
      (Or.inl four₁)
  by_cases four₂ : d=h-4 ∧ s=h-1
  · exact CriticalThreeCubic.three_quarter_four_packets hh base rank budget.2 (Nat.sub_le _ _)
      (Or.inr four₂)
  apply CriticalThreeCubic.three_quarter_bulk hh hd low hs base rank budget.2
    (Nat.sub_le _ _) four₁ _ four₂
  rintro ⟨dEq,sEq⟩
  apply edge
  have dec := congrArg (fun x : ℕ => h*x) (show h-3+1=h-2 by omega)
  rw [dEq,sEq] at base
  nlinarith only [base,dec,Nat.sub_add_cancel (by omega : 1≤h)]

end CriticalThreeQuarter

namespace CriticalThreeTop

theorem strict_width_at_least_twice {h b N : ℕ} (hb : 0<b) (ordered : b<N)
    (count : 3*b*N ⌈/⌉ (b+N+1)=2*b-h) : 2*h≤b := by
  let r := 2*b-h
  have bound := (ceilDiv_le_iff_le_mul (by omega : 0<b+N+1)).mp count.le
  change 3*b*N≤(b+N+1)*r at bound
  have hr : 0<r := by
    by_contra! zero
    have e : r=0 := by omega
    rw [e,Nat.mul_zero] at bound
    have pos := Nat.mul_pos (Nat.mul_pos (by decide : 0<3) hb) (by omega : 0<N)
    omega
  have level : r+h=2*b := Nat.sub_add_cancel (Nat.sub_pos_iff_lt.mp hr).le
  have eq := congrArg (fun t : ℕ => t*N) level
  have delta : N*(b+h)≤r*(b+1) := by nlinarith only [eq,bound]
  have mul := (Nat.mul_le_mul_right (b+h) (show b+1≤N by omega)).trans delta
  rw [Nat.mul_comm r (b+1)] at mul
  have := Nat.le_of_mul_le_mul_left mul (by omega)
  omega

end CriticalThreeTop

namespace CriticalHigher.Jacobian

open Polynomial

/-- Among the nonzero polynomial relations of an algebraic element in
characteristic zero, a least-degree relation has nonvanishing derivative
at that element. The coefficient domain need not be a field. -/
theorem separable_relation {R A : Type*} [CommRing R] [IsDomain R] [CharZero R]
    [CommRing A] [Algebra R A] (faithful : Function.Injective (algebraMap R A))
    (x : A) (hx : IsAlgebraic R x) :
    ∃ p : R[X], aeval x p=0 ∧ aeval x p.derivative≠0 := by
  classical
  let relation (n : ℕ) := ∃ p : R[X], p.natDegree=n ∧ p≠0 ∧ aeval x p=0
  obtain ⟨p,nonzero,vanishes⟩ := hx
  have exists_rel : ∃ n, relation n := ⟨p.natDegree,p,rfl,nonzero,vanishes⟩
  obtain ⟨q,degree,nz,zero⟩ := Nat.find_spec exists_rel
  have pos : q.natDegree≠0 := by
    intro const
    have eq := Polynomial.eq_C_of_natDegree_eq_zero const
    have atC : algebraMap R A (q.coeff 0)=0 := by
      calc
        _ = aeval x (C (q.coeff 0)) := (Polynomial.aeval_C _ _).symm
        _ = 0 := eq ▸ zero
    have c0 : q.coeff 0=0 := faithful (atC.trans (map_zero _).symm)
    exact nz (eq.trans (by rw [c0,map_zero]))
  refine ⟨q,zero,?_⟩
  intro repeated
  have least := Nat.find_min' exists_rel (show relation q.derivative.natDegree from
    ⟨q.derivative,rfl,Polynomial.derivative_ne_zero.mpr pos,repeated⟩)
  have strict := Polynomial.natDegree_derivative_lt pos
  omega

/-- A derivation on an integral domain vanishes on elements algebraic
over a subalgebra on which it vanishes. -/
theorem derivation_zero_of_algebraic {k A : Type*} [Field k] [CommRing A] [IsDomain A] [CharZero A]
    [Algebra k A] (D : Derivation k A A) (S : Subalgebra k A)
    (kill : ∀ c : S, D (c:A)=0) (x : A) (hx : IsAlgebraic S x) : D x=0 := by
  let d : Derivation S A A := {
    toFun := D
    map_add' := map_add D
    map_smul' := by
      intro a b
      change D ((a:A)*b) = (a:A)*D b
      rw [D.leibniz,kill,smul_zero,add_zero,smul_eq_mul]
    map_one_eq_zero' := D.map_one_eq_zero
    leibniz' := D.leibniz }
  have embedding : Function.Injective (algebraMap S A) := Subtype.val_injective
  obtain ⟨p,zero,nz⟩ := separable_relation embedding x hx
  have eq := d.map_aeval p x
  rw [zero,map_zero,smul_eq_mul] at eq
  exact (mul_eq_zero.mp eq.symm).resolve_left nz

end CriticalHigher.Jacobian

namespace CriticalHigher.Jacobian

open MvPolynomial

/-- The ordinary square Jacobian of any polynomial transcendence basis
has nonzero determinant already in the polynomial ring. -/
theorem basis_jacobian_det_ne_zero {k J : Type*} [Field k] [CharZero k]
    [Fintype J] [DecidableEq J] (y : J → MvPolynomial J k) (basis : IsTranscendenceBasis k y) :
    (Matrix.of (fun i j : J => MvPolynomial.pderiv j (y i))).det ≠ 0 := by
  classical
  let A := MvPolynomial J k
  let M : Matrix J J A := Matrix.of fun i j => MvPolynomial.pderiv j (y i)
  intro singular
  obtain ⟨v,nz,kernel⟩ := (Matrix.exists_mulVec_eq_zero_iff (M:=M)).mpr singular
  let D : Derivation k A A := ∑ j, v j • MvPolynomial.pderiv j
  have action (p : A) : D p = ∑ j, v j * MvPolynomial.pderiv j p := by
    have by_finset (s : Finset J) : (∑ j ∈ s, v j • MvPolynomial.pderiv j : Derivation k A A) p =
        ∑ j ∈ s, v j * MvPolynomial.pderiv j p := by
      induction s using Finset.induction_on with
      | empty => simp
      | insert j t hj ih => simp [hj,ih,smul_eq_mul]
    exact by_finset _
  let S := Algebra.adjoin k (Set.range y)
  have vanish (i : J) : D (y i)=0 := by
    rw [action]
    have he := congrFun kernel i
    simpa only [M,Matrix.mulVec, dotProduct,Matrix.of_apply,mul_comm,Pi.zero_apply] using he
  have killed : Set.EqOn D (0 : Derivation k A A) (Set.range y) := by
    rintro _ ⟨j,rfl⟩
    exact vanish j
  have kill (c : S) : D (c:A)=0 := Derivation.eqOn_adjoin killed c.property
  apply nz
  funext j
  have dx := derivation_zero_of_algebraic D S kill (MvPolynomial.X j) (basis.isAlgebraic.1 _)
  change v j = 0
  simpa [action,MvPolynomial.pderiv_X,Pi.single_apply,mul_ite] using dx

/-- Complete the specified output rows to the Jacobian of a polynomial
transcendence basis. The completion has a nonzero polynomial determinant. -/
theorem jacobian_completion {k I J : Type} [Field k] [CharZero k] [Fintype J] [DecidableEq J]
    (f : I → MvPolynomial J k) (hf : AlgebraicIndependent k f) :
    ∃ M : Matrix J J (MvPolynomial J k), M.det≠0 ∧ ∃ e : I ↪ J,
      ∀ i j, M (e i) j=MvPolynomial.pderiv j (f i) := by
  classical
  obtain ⟨s,incl,basis⟩ := exists_isTranscendenceBasis_superset hf.coe_range
  let q := Classical.choice (Cardinal.eq.mp (basis.cardinalMk_eq (IsTranscendenceBasis.mvPolynomial J k)))
  let y (j : J) : MvPolynomial J k := (q.symm j).val
  have hy : IsTranscendenceBasis k y := basis.comp_equiv q.symm
  let e : I ↪ J := ⟨fun i => q ⟨f i,incl (Set.mem_range_self i)⟩,by
    intro i j eq
    exact hf.injective (congrArg Subtype.val (q.injective eq))⟩
  have emb (i : I) : y (e i)=f i := by
    change (q.symm (q ⟨f i,incl (Set.mem_range_self i)⟩)).val = _
    rw [Equiv.symm_apply_apply]
  exact ⟨Matrix.of (fun i j : J => MvPolynomial.pderiv j (y i)),basis_jacobian_det_ne_zero y hy,
    e,fun i j => congrArg (MvPolynomial.pderiv j) (emb i)⟩

end CriticalHigher.Jacobian

namespace CriticalHigher.Jacobian

open MvPolynomial

/-- An injective map on the polynomial coefficients preserves the full row
rank of the Jacobian of algebraically independent outputs. -/
theorem jacobian_rows_independent_over {k I J L : Type} [Field k] [CharZero k] [Fintype J] [Field L]
    (f : I → MvPolynomial J k) (hf : AlgebraicIndependent k f)
    (φ : MvPolynomial J k →+* L) (injective : Function.Injective φ) :
    LinearIndependent L (M := J → L) (fun (i : I) (j : J) => φ (MvPolynomial.pderiv j (f i))) := by
  classical
  obtain ⟨M,hd,e,rows⟩ := jacobian_completion f hf
  have mapped : (M.map φ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply,← RingHom.map_det]
    exact fun eq => hd (injective (eq.trans φ.map_zero.symm))
  have lin : LinearIndependent L (fun i : J => M.map φ i) := Matrix.linearIndependent_rows_of_det_ne_zero mapped
  have smaller := lin.comp e e.injective
  have eq : (fun i : J => M.map φ i) ∘ e = (fun (i : I) (j : J) => φ (MvPolynomial.pderiv j (f i))) := by
    funext i j
    exact congrArg φ (rows i j)
  exact eq ▸ smaller

/-- The rows in particular are independent over the field of rational functions. -/
theorem jacobian_rows_independent {k I J : Type} [Field k] [CharZero k] [Fintype J]
    (f : I → MvPolynomial J k) (hf : AlgebraicIndependent k f) :
    let A := MvPolynomial J k
    let L := FractionRing A
    LinearIndependent L (M := J → L) (fun (i : I) (j : J) => algebraMap A L (MvPolynomial.pderiv j (f i))) := by
  intro A L
  exact jacobian_rows_independent_over f hf (algebraMap A L) (IsFractionRing.injective A L)

/-- Some actual scalar specialization has a surjective Jacobian. -/
theorem exists_surjective_jacobian {k I J : Type} [Field k] [CharZero k] [Fintype J]
    (f : I → MvPolynomial J k) (hf : AlgebraicIndependent k f) :
    ∃ x : J → k, Function.Surjective
      (Matrix.of (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (f i)))).mulVec := by
  classical
  obtain ⟨M,hd,e,rows⟩ := jacobian_completion f hf
  obtain ⟨x,hx⟩ : ∃ x : J → k, MvPolynomial.eval x M.det ≠ 0 := by
    by_contra! vanishes
    exact hd (MvPolynomial.funext fun x => by rw [vanishes x,map_zero])
  have good : (M.map (MvPolynomial.eval x)).det ≠ 0 := by
    rwa [← RingHom.mapMatrix_apply,← RingHom.map_det]
  have surj := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr good))
  refine ⟨x,?_⟩
  intro b
  let values : J → k := Function.extend e b (fun _ => 0)
  obtain ⟨v,hv⟩ := surj values
  refine ⟨v,funext fun i => ?_⟩
  have row := congrFun hv (e i)
  simpa only [Matrix.mulVec,dotProduct,Matrix.of_apply,Matrix.map_apply,rows,values,
    e.injective.extend_apply] using row

end CriticalHigher.Jacobian

namespace CriticalHigher.GenericTangent

open MvPolynomial Set Arxiv.«0805.3777»
open scoped Topology

/-- A polynomial relation among the coordinates vanishes on the whole image.
If the image contains an open set, the only such relation is zero. -/
private lemma independent_of_image_interior {I J : Type} (F : J → MvPolynomial I ℂ)
    (h : (interior (Set.range (fun x : I → ℂ => fun j => eval x (F j)))).Nonempty) :
    AlgebraicIndependent ℂ F := by
  apply algebraicIndependent_iff.mpr
  intro Q hQ
  by_contra hne
  have sub : Set.range (fun x : I → ℂ => fun j => eval x (F j)) ⊆
      {y : J → ℂ | eval y Q=0} := by
    rintro _ ⟨x,rfl⟩
    change eval (fun j => eval x (F j)) Q=0
    rw [← CriticalReduction.eval_substitution F x Q,hQ,map_zero]
  obtain ⟨y,hy⟩ := h
  have bad := interior_mono sub hy
  rw [CriticalReduction.interior_polynomial_zero_locus Q hne] at bad
  exact bad

/-- Contracting one Jacobian row with a variation differentiates each summand
in each of its three factors. The indices may repeat. -/
private lemma trilinear_jacobian_action {I J S : Type} [Fintype I] [Fintype S]
    (a b c : S → J → I) (base v : I → ℂ) (j : J) :
    let F (q : J) : MvPolynomial I ℂ := ∑ t, X (a t q) * (X (b t q) * X (c t q))
    (Matrix.of (fun q i => eval base (pderiv i (F q)))).mulVec v j =
      ∑ t : S, (v (a t j)*(base (b t j)*base (c t j)) +
        base (a t j)*(v (b t j)*base (c t j)) + base (a t j)*(base (b t j)*v (c t j))) := by
  classical
  intro F
  let D (p : MvPolynomial I ℂ) := ∑ i : I, eval base (pderiv i p) * v i
  have var (i : I) : D (X i) = v i := by
    have term (k : I) : eval base (pderiv k (X i : MvPolynomial I ℂ)) * v k =
        if k=i then v i else 0 := by
      by_cases eq : k=i
      · subst k
        simp
      · rw [pderiv_X_of_ne (Ne.symm eq),map_zero,zero_mul,if_neg eq]
    simp only [D,term]
    simp
  have prod (p q : MvPolynomial I ℂ) : D (p*q) = D p * eval base q + eval base p * D q := by
    dsimp only [D]
    rw [Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [pderiv_mul,map_add,map_mul]
    ring
  have sum (f : S → MvPolynomial I ℂ) : D (∑ t, f t) = ∑ t, D (f t) := by
    simp only [D,map_sum,Finset.sum_mul]
    exact Finset.sum_comm
  change D (F j) = _
  dsimp only [F]
  rw [sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [prod,var,map_mul,eval_X]
  ring

/-- A generic complex CP rank gives a spanning tangent at the same number of
summands. The parametrization uses all three vectors of every summand. -/
lemma of_generic {a b n r : ℕ} (h : IsGenericRank [a,b,n] r) :
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
      ∀ T : Fin a → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
  classical
  obtain ⟨U,hopen,hdense,hrank⟩ := h
  obtain ⟨E,hE⟩ := CriticalReduction.rectangular_indices a b n
  let P := Fin r × (Fin a ⊕ (Fin b ⊕ Fin n))
  let first (t : Fin r) (q : HolorIndex [a,b,n]) : P := (t,.inl (E q).1)
  let second (t : Fin r) (q : HolorIndex [a,b,n]) : P := (t,.inr (.inl (E q).2.1))
  let third (t : Fin r) (q : HolorIndex [a,b,n]) : P := (t,.inr (.inr (E q).2.2))
  let F (q : HolorIndex [a,b,n]) : MvPolynomial P ℂ :=
    ∑ t : Fin r, X (first t q) * (X (second t q) * X (third t q))
  have covered : U ⊆ Set.range (fun x : P → ℂ => fun q => eval x (F q)) := by
    intro T hT
    obtain ⟨x,y,z,decomp⟩ := CriticalReduction.sum_coordinates E hE T r (hrank T hT).le
    let pack (p : P) := p.2.elim (x p.1) (Sum.elim (y p.1) (z p.1))
    refine ⟨pack,funext fun q => ?_⟩
    simpa only [F,map_sum,map_mul,eval_X,pack,first,second,third,Sum.elim_inl,Sum.elim_inr,mul_assoc] using decomp q
  have independent := independent_of_image_interior F (hdense.nonempty.mono (interior_maximal covered hopen))
  obtain ⟨base,onto⟩ := CriticalHigher.Jacobian.exists_surjective_jacobian F independent
  refine ⟨fun t i => base (t,.inl i), fun t j => base (t,.inr (.inl j)),
    fun t k => base (t,.inr (.inr k)), ?_⟩
  intro T
  obtain ⟨v,hv⟩ := onto (fun q => T (E q).1 (E q).2.1 (E q).2.2)
  refine ⟨fun t i => v (t,.inl i), fun t j => v (t,.inr (.inl j)),
    fun t k => v (t,.inr (.inr k)), ?_⟩
  intro i j k
  let q := E.symm (i,j,k)
  have eq := (congrFun hv q).symm.trans (trilinear_jacobian_action first second third base v q)
  simpa only [first,second,third,q,Equiv.apply_symm_apply] using eq

/-- At the normalized parameter count the generic-rank statement and
existence of one spanning tangent are equivalent for all positive side lengths. -/
lemma iff_of_count {a b n r : ℕ} (ha : 0<a) (hb : 0<b) (hn : 0<n)
    (count : r = a*b*n ⌈/⌉ (a+b+n-2)) :
    IsGenericRank [a,b,n] r ↔
      ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
        ∀ T : Fin a → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin a → ℂ,
          ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
            T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
  refine ⟨of_generic,?_⟩
  intro witness
  have hd : 0 < a+b+n-2 := by omega
  have positive := Nat.mul_pos (Nat.mul_pos ha hb) hn
  have hr : 0<r := by
    by_contra! zero
    have hz := (ceilDiv_le_iff_le_mul hd).mp (count.symm.trans_le zero)
    rw [Nat.mul_zero] at hz
    omega
  have cost : (a+b+n-2)*(r-1) < a*b*n := by
    by_contra! he
    have small := count.trans_le ((ceilDiv_le_iff_le_mul hd).mpr he)
    omega
  obtain ⟨U,hU,dense,upper⟩ := CriticalReduction.upper_of_witness witness
  let Low := closure {T : Holor ℂ [a,b,n] | T.cprank ≤ r-1}
  have lower : Dense Lowᶜ :=
    interior_eq_empty_iff_dense_compl.mp (CriticalReduction.lower_of_count a b n (r-1) cost)
  refine ⟨U ∩ Lowᶜ,hU.inter isClosed_closure.isOpen_compl,dense.inter_of_isOpen_left lower hU,?_⟩
  intro T ht
  have hi := upper T ht.1
  have lo : ¬ T.cprank ≤ r-1 := fun h => ht.2 (subset_closure h)
  omega

end CriticalHigher.GenericTangent

namespace CriticalHigher.GapTwo

open Polynomial

private lemma clear_cauchy {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (u x : I → K) (regular : ∀ i, x i ≠ 0) :
    (∑ i, u i/x i)*(∏ i, x i) = ∑ i, u i*∏ j ∈ Finset.univ.erase i, x j := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  let E := ∏ j ∈ Finset.univ.erase i, x j
  have product : E*x i = ∏ j, x j := Finset.prod_erase_mul Finset.univ x (Finset.mem_univ i)
  rw [← product]
  change u i/x i*(E*x i)=u i*E
  calc
    _ = (u i/x i*x i)*E := by ring
    _ = _ := by rw [div_mul_cancel₀ _ (regular i)]

/-- A Cauchy sum taking the same value at every node has this explicit
cleared numerator at every argument, including at the reflected nodes. -/
theorem constant_cauchy_numerator {K : Type*} [Field K] {m : ℕ} (z w : Fin m → K)
    (distinct : Function.Injective z) (regular : ∀ j i, z j+z i≠0) (d : K)
    (samples : ∀ j, (∑ i, w i/(z j+z i))=d) (t : K) :
    (∑ i, w i*∏ j ∈ Finset.univ.erase i, (t+z j)) =
      d*((∏ i, (t+z i))-(∏ i, (t-z i))) := by
  classical
  by_cases empty : m=0
  · subst m; simp
  let L (i : Fin m) : K[X] := X-C (-z i)
  let D : K[X] := ∏ i, L i
  let P : K[X] := ∏ i, (X-C (z i))
  let E (i : Fin m) := ∏ j ∈ Finset.univ.erase i, L j
  let H : K[X] := ∑ i, C (w i)*E i
  have degree (S : Finset (Fin m)) : (∏ i ∈ S, L i).natDegree=S.card :=
    natDegree_finsetProd_X_sub_C_eq_card S (fun i => -z i)
  have degD : IsMonicOfDegree D m := ⟨(degree Finset.univ).trans (by simp),monic_prod_X_sub_C (fun i => -z i) _⟩
  have degP : IsMonicOfDegree P m := ⟨by simp [P],monic_prod_X_sub_C z _⟩
  have degH : H.natDegree ≤ m-1 := by
    apply natDegree_sum_le_of_forall_le
    intro i _
    apply (natDegree_C_mul_le _ _).trans
    change (∏ j ∈ Finset.univ.erase i, L j).natDegree ≤ m-1
    rw [degree,Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin]
  have lower : (C d*(D-P)).natDegree < m := (natDegree_C_mul_le _ _).trans_lt (degD.natDegree_sub_lt empty degP)
  have left (x : K) : D.eval x = ∏ i, (x+z i) := by
    simp only [D,L,eval_prod,eval_sub,eval_X,eval_C,sub_neg_eq_add]
  have right (x : K) : P.eval x = ∏ i, (x-z i) := by
    simp only [P,eval_prod,eval_sub,eval_X,eval_C]
  have numerator (x : K) : H.eval x = ∑ i, w i*∏ j ∈ Finset.univ.erase i, (x+z j) := by
    simp only [H,E,L,eval_finsetSum,eval_mul,eval_C,eval_prod,eval_sub,eval_X,sub_neg_eq_add]
  have atNodes (j : Fin m) : H.eval (z j) = (C d*(D-P)).eval (z j) := by
    have root : P.eval (z j)=0 := (right _).trans (Finset.prod_eq_zero (Finset.mem_univ j) (sub_self (z j)))
    rw [numerator,← clear_cauchy w (fun i => z j+z i) (regular j),samples j,eval_mul,eval_C,
      eval_sub,root,sub_zero,left]
  have identity : H = C d*(D-P) :=
    eq_of_natDegree_lt_card_of_eval_eq _ _ distinct atNodes (by rw [Fintype.card_fin]; omega)
  rw [← numerator,identity,eval_mul,eval_C,eval_sub,left,right]

/-- Evaluating the interpolant at zero fixes the reciprocal moment;
evaluating at every reflected node proves uniqueness when `d=0`. -/
theorem constant_cauchy {K : Type*} [Field K] {m : ℕ} (z w : Fin m → K)
    (distinct : Function.Injective z) (regular : ∀ j i, z j+z i≠0) (d : K)
    (samples : ∀ j, (∑ i, w i/(z j+z i))=d) :
    (∑ i, w i/z i) = d*(1-(-1 : K)^m) ∧ (d=0 → w=0) := by
  classical
  have identity := constant_cauchy_numerator z w distinct regular d samples
  have nz (i : Fin m) : z i≠0 := by
    intro zero
    exact regular i i (by rw [zero,zero_add])
  constructor
  · have zero := identity 0
    simp only [zero_add,zero_sub,Finset.prod_neg,Finset.card_univ,Fintype.card_fin] at zero
    apply mul_right_cancel₀ (Finset.prod_ne_zero_iff.mpr (fun i _ => nz i) : (∏ i, z i)≠0)
    rw [clear_cauchy w z nz,zero]
    ring
  · intro vanishes
    funext i
    have pole := identity (-z i)
    rw [vanishes,zero_mul,Finset.sum_eq_single i] at pole
    · have others : (∏ j ∈ Finset.univ.erase i, (-z i+z j)) ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro j hj eq
        exact Finset.ne_of_mem_erase hj (distinct (by linear_combination eq))
      exact (mul_eq_zero.mp pole).resolve_right others
    · intro j _ hji
      have mem : i ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨Ne.symm hji,Finset.mem_univ i⟩
      rw [Finset.prod_eq_zero mem (neg_add_cancel (z i)),mul_zero]
    · simp

end CriticalHigher.GapTwo

namespace CriticalHigher.GapTwo

private lemma divide_kernel (s t c : ℂ) (regular : t+s≠0) :
    c*(t-s)*(1+s^2+2*s*t)/(t+s) = 2*t*(s*c)+c-3*(s^2*c) - (2*s*(1-s^2)*c)/(t+s) := by
  field_simp [regular]
  ring

/-- The two scalar moments and the rational equations at the marked nodes
force every coefficient of the gap-two construction to vanish. -/
theorem interpolation {m : ℕ} (s : Fin m → ℝ) (distinct : Function.Injective s)
    (above : ∀ i, 1<s i) (c : Fin m → ℂ) (sum0 : ∑ i, c i=0) (sum1 : ∑ i, (s i : ℂ)*c i=0)
    (at_nodes : ∀ j, ∑ i, c i*((s j : ℂ)-(s i : ℂ))*(1+(s i : ℂ)^2+2*(s i : ℂ)*(s j : ℂ)) /
      ((s j : ℂ)+(s i : ℂ))=0) : c=0 := by
  let z (i : Fin m) : ℂ := s i
  let U := ∑ i, z i^2*c i
  let w (i : Fin m) := 2*z i*(1-z i^2)*c i
  have inj : Function.Injective z := fun _ _ eq => distinct (Complex.ofReal_injective eq)
  have nz (i : Fin m) : z i≠0 := Complex.ofReal_ne_zero.mpr (by linarith [above i])
  have regular (j i : Fin m) : z j+z i≠0 := by
    change (s j : ℂ)+(s i : ℂ)≠0
    rw [← Complex.ofReal_add,Complex.ofReal_ne_zero]
    linarith [above j,above i]
  have square (i : Fin m) : 1-z i^2≠0 := by
    change (1 : ℂ)-(s i : ℂ)^2≠0
    have real : (1 : ℝ)-s i^2≠0 := by nlinarith [above i,sq_nonneg (s i-1)]
    exact_mod_cast real
  have samples (j : Fin m) : (∑ i, w i/(z j+z i))= -3*U := by
    have eq := (Finset.sum_congr (s₁:=Finset.univ) rfl (fun i _ =>
      divide_kernel (z i) (z j) (c i) (regular j i))).symm.trans (at_nodes j)
    change (∑ i, (2*z j*(z i*c i)+c i-3*(z i^2*c i)-w i/(z j+z i)))=0 at eq
    rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
      ← Finset.mul_sum,sum0,show (∑ i,z i*c i)=0 from sum1] at eq
    dsimp only [U]
    linear_combination -eq
  have reciprocal : (∑ i, w i/z i)= -2*U := by
    calc
      _ = ∑ i, (2*c i-2*(z i^2*c i)) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [w]
        field_simp [nz i]
      _ = _ := by rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,sum0]; dsimp only [U]; ring
  obtain ⟨balance,unique⟩ := constant_cauchy z w inj regular (-3*U) samples
  have eq := reciprocal.symm.trans balance
  have moment : U=0 := by
    rcases neg_one_pow_eq_or ℂ m with plus|minus
    · rw [plus] at eq
      linear_combination (-1/2 : ℂ)*eq
    · rw [minus] at eq
      linear_combination (1/4 : ℂ)*eq
  have weights := unique (by rw [moment,mul_zero])
  funext i
  have term := congrFun weights i
  change 2*z i*(1-z i^2)*c i=0 at term
  exact (mul_eq_zero.mp term).resolve_left (mul_ne_zero (mul_ne_zero two_ne_zero (nz i)) (square i))

end CriticalHigher.GapTwo

namespace CriticalHigher.GapTwo

/-- Finite trilinear forms and coordinate arrays give the same normal test:
vanishing of a trilinear normal at every triple of coordinate vectors implies
that the tangent map at the specified points is onto. -/
theorem tangent_of_basis_vanishing {I J K P : Type*}
    [Fintype I] [Fintype J] [Fintype K] [Fintype P] [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (x : P → I → ℂ) (y : P → J → ℂ) (z : P → K → ℂ)
    (normal : ∀ F : (I → ℂ) →ₗ[ℂ] (J → ℂ) →ₗ[ℂ] (K → ℂ) →ₗ[ℂ] ℂ,
      (∀ p a, F a (y p) (z p)=0) → (∀ p b, F (x p) b (z p)=0) →
      (∀ p c, F (x p) (y p) c=0) →
      ∀ i j k, F (Pi.single i 1) (Pi.single j 1) (Pi.single k 1)=0) :
    ∀ T : I → J → K → ℂ, ∃ u : P → I → ℂ, ∃ v : P → J → ℂ, ∃ w : P → K → ℂ,
      ∀ i j k, T i j k =
        ∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k)) := by
  classical
  have detect (H : I → J → K → ℂ)
      (hx : ∀ t i, ∑ j,∑ k, (y t j*z t k)*H i j k=0)
      (hy : ∀ t j, ∑ i,∑ k, (x t i*z t k)*H i j k=0)
      (hz : ∀ t k, ∑ i,∑ j, (x t i*y t j)*H i j k=0) : H=0 := by
    let C (i : I) (j : J) : (K → ℂ) →ₗ[ℂ] ℂ := (Pi.basisFun ℂ K).constr ℂ (H i j)
    let B (i : I) := (Pi.basisFun ℂ J).constr ℂ (C i)
    let F := (Pi.basisFun ℂ I).constr ℂ B
    have expand (a : I → ℂ) (b : J → ℂ) (c : K → ℂ) :
        F a b c = ∑ i,∑ j,∑ k, (a i*b j*c k)*H i j k := by
      simp [F,B,C,LinearMap.sum_apply,LinearMap.smul_apply,Finset.mul_sum,mul_assoc]
    have left (t : P) (a : I → ℂ) : F a (y t) (z t)=0 := calc
      _ = ∑ i, a i*(∑ j,∑ k, (y t j*z t k)*H i j k) := by
        rw [expand]
        simp only [Finset.mul_sum,mul_assoc]
      _ = 0 := by simp [hx]
    have middle (t : P) (b : J → ℂ) : F (x t) b (z t)=0 := calc
      _ = ∑ i,∑ j, b j*(∑ k, (x t i*z t k)*H i j k) := by
        rw [expand]
        simp only [Finset.mul_sum,mul_assoc,mul_left_comm]
      _ = ∑ j, b j*(∑ i,∑ k, (x t i*z t k)*H i j k) := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ = 0 := by simp [hy]
    have right (t : P) (c : K → ℂ) : F (x t) (y t) c=0 := calc
      _ = ∑ i,∑ j,∑ k, c k*((x t i*y t j)*H i j k) := by
        rw [expand]
        simp only [mul_assoc,mul_left_comm]
      _ = ∑ i,∑ k,∑ j, c k*((x t i*y t j)*H i j k) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = ∑ k, c k*(∑ i,∑ j,(x t i*y t j)*H i j k) := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ = 0 := by simp [hz]
    funext i j k
    change H i j k=0
    simpa only [← Pi.basisFun_apply,F,B,C,Module.Basis.constr_basis] using
      normal F left middle right i j k
  have onto := HigherPencil.augmented_span_of_annihilator x y z
    (fun q : Empty => q.elim) (fun q : Empty => q.elim) (fun H hx hy hz _ => detect H hx hy hz)
  intro T
  obtain ⟨u,v,w,_,hit⟩ := onto T
  exact ⟨u,v,w,fun i j k => by simpa using hit i j k⟩

end CriticalHigher.GapTwo

namespace CriticalHigher.GapTwo.Mixed

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
/-- Three product points per two-coordinate block and one mixed point give
a spanning tangent at the even-width gap-two endpoint. The interpolation
test forces every trilinear normal coefficient to vanish. -/
theorem gap_two_even (m : ℕ) :
    ∃ x : Fin (3*m+1) → Fin 3 → ℂ, ∃ y : Fin (3*m+1) → Fin (2*m) → ℂ, ∃ z : Fin (3*m+1) → Fin (2*m+2) → ℂ,
        ∀ T : Fin 3 → Fin (2*m) → Fin (2*m+2) → ℂ, ∃ u : Fin (3*m+1) → Fin 3 → ℂ, ∃ v : Fin (3*m+1) → Fin (2*m) → ℂ,
          ∃ w : Fin (3*m+1) → Fin (2*m+2) → ℂ, ∀ i j k,
            T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
  classical
  let Spans (a b c r : ℕ) : Prop :=
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
        ∃ w : Fin r → Fin c → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))
  let weights (s t : ℂ) : Fin 3 → Fin 3 → ℂ :=
    let a := 1+s^2+2*s*t
    let b := (t-s)*(1-s)
    let d := -(t-s)*(1+s)
    ![![a,d,b], ![b,a,d], ![d,b,a]]
  let Rows (m : ℕ) := Fin m × Fin 2
  let Cols (m : ℕ) := (Fin m × Fin 2) ⊕ Fin 2
  let Pts (m : ℕ) := (Fin m × Fin 3) ⊕ Unit
  let Form (m : ℕ) := (Fin 3 → ℂ) →ₗ[ℂ] (Rows m → ℂ) →ₗ[ℂ] (Cols m → ℂ) →ₗ[ℂ] ℂ
  let unit {I : Type} [DecidableEq I] (i : I) : (I → ℂ) := Pi.single i 1
  let frame (s : ℂ) : Fin 3 → (Fin 3 → ℂ) := ![![1,-s,s],![s,1,-s],![-s,s,1]]
  let xStar : (Fin 3 → ℂ) := fun _ => 1
  let cov : Fin 3 → (Fin 2 → ℂ) := ![![0,1],![-1,0],![1,-1]]
  let yLoc {m : ℕ} (i : Fin m) : Fin 3 → (Rows m → ℂ) :=
    ![unit (i,0),unit (i,1),unit (i,0)+unit (i,1)]
  let yStar (m : ℕ) : (Rows m → ℂ) := ∑ i : Fin m, unit (i,0)
  let zLoc {m : ℕ} (s : ℂ) (i : Fin m) : Fin 3 → (Cols m → ℂ) :=
    ![unit (.inl (i,0)),unit (.inl (i,1)),
      -unit (.inl (i,0))-unit (.inl (i,1))+unit (.inr 0)+s • unit (.inr 1)]
  let zStar (m : ℕ) : (Cols m → ℂ) := unit (.inr 1)
  let xPts {m : ℕ} (s : Fin m → ℝ) : Pts m → (Fin 3 → ℂ) :=
    Sum.elim (fun q => frame (s q.1) q.2) (fun _ => xStar)
  let yPts (m : ℕ) : Pts m → (Rows m → ℂ) := Sum.elim (fun q => yLoc q.1 q.2) (fun _ => yStar m)
  let zPts {m : ℕ} (s : Fin m → ℝ) : Pts m → (Cols m → ℂ) :=
    Sum.elim (fun q => zLoc (s q.1) q.1 q.2) (fun _ => zStar m)
  have sum_frame (s : ℂ) : ∑ r,frame s r = xStar := by
    funext i
    change (∑ r : Fin 3,frame s r : Fin 3 → ℂ) i=1
    rw [Finset.sum_apply]
    fin_cases i <;> simp [Fin.sum_univ_three,frame]
  have frame_transfer (s t : ℂ) (l : Fin 3) :
      ∑ r, weights s t l r • frame s r = (1+3*s^2) • frame t l := by
    funext a
    rw [Finset.sum_apply]
    change (∑ r,weights s t l r * frame s r a)=(1+3*s^2)*frame t l a
    fin_cases l <;> fin_cases a <;> simp [weights,frame,Fin.sum_univ_three] <;> ring
  have cov_kernel (v : Fin 3 → ℂ)
      (h : ∀ k, ∑ r, v r*cov r k=0) : ∀ r, v r = v 0 := by
    have a := h 0
    have b := h 1
    simp [cov,Fin.sum_univ_three] at a b
    intro r
    fin_cases r
    · rfl
    · change v 1=v 0
      linear_combination -a-b
    · change v 2=v 0
      linear_combination -b
  have frame_zero (a : Fin 3) : frame 0 a = unit a := by
    funext i
    fin_cases a <;> fin_cases i <;> simp [frame,unit]
  let gamma {m : ℕ} (T : Form m) (s : Fin m → ℝ) (i : Fin m) :
      Fin 3 → ((Cols m → ℂ) →ₗ[ℂ] ℂ) :=
    ![T (frame (s i) 0) (unit (i,1)), -(T (frame (s i) 1) (unit (i,0))),
      T (frame (s i) 2) (unit (i,0))]
  have read_gamma {m : ℕ} (T : Form m) (s : Fin m → ℝ)
      (third : ∀ (p : Pts m) w, T (xPts s p) (yPts m p) w=0)
      (i : Fin m) (l : Fin 3) (h : Fin 2) (z : (Cols m → ℂ)) :
      T (frame (s i) l) (unit (i,h)) z = gamma T s i l z * cov l h := by
    have a := third (.inl (i,0)) z
    have b := third (.inl (i,1)) z
    have c := third (.inl (i,2)) z
    change T (frame (s i) 0) (unit (i,0)) z=0 at a
    change T (frame (s i) 1) (unit (i,1)) z=0 at b
    change T (frame (s i) 2) (unit (i,0)+unit (i,1)) z=0 at c
    rw [map_add,LinearMap.add_apply] at c
    fin_cases l <;> fin_cases h <;> simp [gamma,cov,a,b]
    linear_combination c
  have evaluate_y {m : ℕ} (T : Form m) (s : Fin m → ℝ) (third : ∀ p w, T (xPts s p) (yPts m p) w=0)
      (i : Fin m) (l t : Fin 3) (z : (Cols m → ℂ)) :
      T (frame (s i) l) (yLoc i t) z =
        gamma T s i l z * (![cov l 0,cov l 1,cov l 0+cov l 1] : Fin 3 → ℂ) t := by
    fin_cases t <;> simp [yLoc,read_gamma T s third,mul_add]
  have local_vanish {m : ℕ} (T : Form m) (s : Fin m → ℝ) (first : ∀ p x, T x (yPts m p) (zPts s p)=0)
      (second : ∀ p y, T (xPts s p) y (zPts s p)=0) (third : ∀ p w, T (xPts s p) (yPts m p) w=0)
      (i : Fin m) (t r : Fin 3) : gamma T s i r (zLoc (s i) i t)=0 := by
    let z := zLoc (s i) i t
    by_cases eq : r=t
    · subst r
      have h (k : Fin 2) : gamma T s i t z*cov t k=0 := by
        rw [←read_gamma T s third]
        exact second (.inl (i,t)) (unit (i,k))
      fin_cases t
      · simpa [cov,z] using h 1
      · simpa [cov,z] using h 0
      · simpa [cov,z] using h 0
    · have h := first (.inl (i,t)) (frame (s i) r)
      change T (frame (s i) r) (yLoc i t) z=0 at h
      rw [evaluate_y T s third] at h
      have nz : (![cov r 0,cov r 1,cov r 0+cov r 1] : Fin 3 → ℂ) t≠0 := by
        fin_cases r <;> fin_cases t <;> first | exact False.elim (eq rfl) | norm_num [cov]
      exact (mul_eq_zero.mp h).resolve_right nz
  have star_read {m : ℕ} (T : Form m) (s : Fin m → ℝ) (third : ∀ p w, T (xPts s p) (yPts m p) w=0)
      (i : Fin m) (h : Fin 2) (w : (Cols m → ℂ)) :
      T xStar (unit (i,h)) w = ∑ r, gamma T s i r w * cov r h := by
    rw [←sum_frame (s i), map_sum, LinearMap.sum_apply, LinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun r _ => read_gamma T s third i r h w)
  let lam {m : ℕ} (T : Form m) (s : Fin m → ℝ) (i : Fin m) : ℂ := gamma T s i 0 (zStar m)
  let coeff {m : ℕ} (T : Form m) (s : Fin m → ℝ) (i : Fin m) : ℂ := lam T s i / (1+3*(s i : ℂ)^2)
  have mixed_lambda {m : ℕ} (T : Form m) (s : Fin m → ℝ) (second : ∀ p y, T (xPts s p) y (zPts s p)=0)
      (third : ∀ p w, T (xPts s p) (yPts m p) w=0) (i : Fin m) (r : Fin 3) :
      gamma T s i r (zStar m) = lam T s i := by
    refine cov_kernel (fun l => gamma T s i l (zStar m)) ?_ r
    intro h
    rw [←star_read T s third]
    exact second (.inr ()) (unit (i,h))
  have sum_zLoc {m : ℕ} (u : ℂ) (i : Fin m) :
      ∑ l,zLoc u i l = unit (.inr 0) + u • unit (.inr 1) := by
    rw [Fin.sum_univ_three]
    let v : (Cols m → ℂ) := unit (.inl (i,0))
    let w : (Cols m → ℂ) := unit (.inl (i,1))
    let a : (Cols m → ℂ) := unit (.inr 0)
    let b : (Cols m → ℂ) := u • unit (.inr 1)
    change v+w+(-v-w+a+b)=a+b
    abel
  have column_balance {m : ℕ} (T : Form m) (s : Fin m → ℝ) (first : ∀ p x, T x (yPts m p) (zPts s p)=0)
      (second : ∀ p y, T (xPts s p) y (zPts s p)=0) (third : ∀ p w, T (xPts s p) (yPts m p) w=0)
      (i j : Fin m) (r : Fin 3) :
      ∑ l,gamma T s i r (zLoc (s j) j l) = ((s j : ℂ)-(s i : ℂ))*lam T s i := by
    have at_self : (gamma T s i r) (unit (.inr 0) + (s i : ℂ) • unit (.inr 1)) = 0 := by
      rw [←sum_zLoc (s i) i,map_sum]
      exact Finset.sum_eq_zero (fun l _ => local_vanish T s first second third i l r)
    rw [←map_sum,sum_zLoc,map_add,map_smul,smul_eq_mul]
    rw [map_add,map_smul,smul_eq_mul] at at_self
    have h := mixed_lambda T s second third i r
    change gamma T s i r (unit (.inr 1))=lam T s i at h
    rw [h] at at_self ⊢
    linear_combination at_self
  have foreign_constraints {m : ℕ} (T : Form m) (s : Fin m → ℝ) (second : ∀ p y, T (xPts s p) y (zPts s p)=0)
      (third : ∀ p w, T (xPts s p) (yPts m p) w=0) (i j : Fin m) (l : Fin 3) :
      ∃ d : ℂ, ∀ r, weights (s i) (s j) l r * gamma T s i r (zLoc (s j) j l)=d := by
    let z := zLoc (s j) j l
    let v (r : Fin 3) := weights (s i) (s j) l r * gamma T s i r z
    refine ⟨v 0,cov_kernel v ?_⟩
    intro h
    have zero := second (.inl (j,l)) (unit (i,h))
    change T (frame (s j) l) (unit (i,h)) z=0 at zero
    have eq := congrArg (fun b : (Fin 3 → ℂ) => T b (unit (i,h)) z) (frame_transfer (s i) (s j) l)
    simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,smul_eq_mul,zero,mul_zero] at eq
    simp_rw [read_gamma T s third] at eq
    simpa only [v,mul_assoc] using eq
  have nonzero_den {m : ℕ} (s : Fin m → ℝ) (i : Fin m) : (1+3*(s i : ℂ)^2) ≠ 0 := by
    exact_mod_cast (show (1+3*s i^2 : ℝ)≠0 by positivity)
  have mixed_read {m : ℕ} (T : Form m) (s : Fin m → ℝ) (second : ∀ p y, T (xPts s p) y (zPts s p)=0)
      (third : ∀ p w, T (xPts s p) (yPts m p) w=0) (i : Fin m) (a : Fin 3) :
      T (frame 0 a) (unit (i,0)) (zStar m) =
        coeff T s i * (weights (s i) 0 a 2 - weights (s i) 0 a 1) := by
    have eq := congrArg (fun b : (Fin 3 → ℂ) => T b (unit (i,0)) (zStar m)) (frame_transfer (s i) 0 a)
    simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,smul_eq_mul] at eq
    simp_rw [read_gamma T s third,mixed_lambda T s second third] at eq
    simp [Fin.sum_univ_three,cov] at eq
    simp [coeff]
    field_simp [nonzero_den s i]
    linear_combination -eq
  have mixed_moments {m : ℕ} (T : Form m) (s : Fin m → ℝ) (first : ∀ p x, T x (yPts m p) (zPts s p)=0)
      (second : ∀ p y, T (xPts s p) y (zPts s p)=0) (third : ∀ p w, T (xPts s p) (yPts m p) w=0) :
      (∑ i, coeff T s i)=0 ∧ (∑ i, (s i : ℂ)*coeff T s i)=0 := by
    have zero (a : Fin 3) :
        (∑ i, coeff T s i*(weights (s i) 0 a 2-weights (s i) 0 a 1))=0 := by
      have q := first (.inr ()) (frame 0 a)
      change T (frame 0 a) (∑ i : Fin m, unit (i,0)) (zStar m)=0 at q
      rw [map_sum,LinearMap.sum_apply] at q
      simpa only [mixed_read T s second third] using q
    have eq0 (i : Fin m) : weights (s i) 0 0 2-weights (s i) 0 0 1 = -2*(s i : ℂ) := by
      simp [weights];ring
    have eq1 (i : Fin m) : weights (s i) 0 1 2-weights (s i) 0 1 1 = (s i : ℂ)-1 := by
      simp [weights];ring
    have h0 := zero 0
    have h1 := zero 1
    simp_rw [eq0,show ∀ i : Fin m,coeff T s i*(-2*(s i:ℂ)) = -2*((s i:ℂ)*coeff T s i) from fun i=>by ring] at h0
    rw [←Finset.mul_sum] at h0
    have moment := (mul_eq_zero.mp h0).resolve_left (by norm_num : (-2:ℂ)≠0)
    simp_rw [eq1, mul_sub, mul_one, mul_comm (coeff T s _) (s _ : ℂ)] at h1
    rw [Finset.sum_sub_distrib,moment,zero_sub,neg_eq_zero] at h1
    exact ⟨h1,moment⟩
  have last_equation {m : ℕ} (T : Form m) (s : Fin m → ℝ) (third : ∀ p w, T (xPts s p) (yPts m p) w=0) (j : Fin m) :
      (∑ i,(gamma T s i 2 (unit (.inl (j,0)))-gamma T s i 1 (unit (.inl (j,0)))))=0 := by
    let z : (Cols m → ℂ) := unit (.inl (j,0))
    have h := third (.inr ()) z
    change T xStar (∑ i : Fin m,unit (i,0)) z=0 at h
    rw [map_sum,LinearMap.sum_apply] at h
    simp_rw [star_read T s third] at h
    simpa [Fin.sum_univ_three,cov,sub_eq_add_neg,add_comm,z] using h
  have circulant_solution (x y z : ℝ) (hsum : x+y+z ≠ 0) (hyz : y ≠ z)
      (D : Fin 3 → ℂ) (m : ℂ)
      (rows : (!![(x:ℂ),(y:ℂ),(z:ℂ);(z:ℂ),(x:ℂ),(y:ℂ);(y:ℂ),(z:ℂ),(x:ℂ)]).mulVec D =
        fun _ => m) :
      ∀ r, D r = m / ((x+y+z : ℝ) : ℂ) := by
    let Q : Matrix (Fin 3) (Fin 3) ℂ := !![↑x,↑y,↑z;↑z,↑x,↑y;↑y,↑z,↑x]
    have factor : Q.det = ((x+y+z)*(x^2+y^2+z^2-x*y-y*z-z*x) : ℝ) := by
      simp [Q,Matrix.det_fin_three]
      ring
    have hpositive : 0 < x^2+y^2+z^2-x*y-y*z-z*x := by
      nlinarith [sq_nonneg (x-y),sq_pos_of_ne_zero (sub_ne_zero.mpr hyz),sq_nonneg (z-x)]
    have hn : Q.det ≠ 0 := by
      rw [factor]
      exact_mod_cast mul_ne_zero hsum (ne_of_gt hpositive)
    have cu : IsUnit Q := (Matrix.isUnit_iff_isUnit_det Q).mpr (isUnit_iff_ne_zero.mpr hn)
    have hc : (↑(x+y+z) : ℂ) ≠ 0 := by exact_mod_cast hsum
    have total (r : Fin 3) : ∑ i, Q r i = ((x+y+z : ℝ) : ℂ) := by
      fin_cases r <;> simp [Q,Fin.sum_univ_three] <;> ring
    have other : Q.mulVec (fun _ => m / ((x+y+z : ℝ) : ℂ)) = fun _ => m := by
      funext r
      change (∑ i, Q r i * (m / ((x+y+z : ℝ) : ℂ))) = m
      rw [←Finset.sum_mul,total]
      field_simp
    exact congrFun (Matrix.mulVec_injective_of_isUnit cu (rows.trans other.symm))
  have foreign_transfer {s t : ℝ} (hs : 1<s) (ht : 1<t) (st : s≠t)
      (v : Fin 3 → Fin 3 → ℂ) (lam : ℂ)
      (normal : ∀ l, ∃ d : ℂ, ∀ r, weights (s:ℂ) (t:ℂ) l r * v l r = d)
      (balance : ∀ r, ∑ l, v l r = ((t:ℂ)-(s:ℂ))*lam) :
      v 0 2-v 0 1 = 2*((t:ℂ)-(s:ℂ))*lam*(1+(s:ℂ)^2+2*(s:ℂ)*(t:ℂ)) /
          ((1+3*(s:ℂ)^2)*((t:ℂ)+(s:ℂ))) ∧
        (lam=0 → v=0) := by
    let a : ℝ := 1+s^2+2*s*t
    let b : ℝ := (t-s)*(1-s)
    let c : ℝ := -(t-s)*(1+s)
    let x := b*c
    let y := a*c
    let z := a*b
    let K := a*b*c
    let m := ((t:ℂ)-(s:ℂ))*lam
    have ha : a ≠ 0 := by
      dsimp [a]
      have sp : 0 < s := by linarith
      have tp : 0 < t := by linarith
      positivity
    have hts : t-s ≠ 0 := sub_ne_zero.mpr st.symm
    have hb : b ≠ 0 := mul_ne_zero hts (by linarith)
    have hc : c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hts) (by linarith)
    have hK : (K:ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero (mul_ne_zero ha hb) hc
    have row_sum : x+y+z = -(t-s)*(1+3*s^2)*(t+s) := by dsimp [x,y,z,a,b,c]; ring
    have contrast : y-z = -2*(t-s)*a := by dsimp [y,z,b,c]; ring
    have hg : 0 < 1+3*s^2 := by positivity
    have hp : 0 < t+s := by linarith
    have nonzero : x+y+z ≠ 0 := by
      rw [row_sum]
      exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hts) hg.ne') hp.ne'
    have distinct : y ≠ z := by
      apply sub_ne_zero.mp
      rw [contrast]
      exact mul_ne_zero (mul_ne_zero (by norm_num) hts) ha
    let Q : Matrix (Fin 3) (Fin 3) ℂ := !![↑x,↑y,↑z;↑z,↑x,↑y;↑y,↑z,↑x]
    have weight_eq : weights (s:ℂ) (t:ℂ) =
        (![![(a:ℂ),(c:ℂ),(b:ℂ)],![(b:ℂ),(a:ℂ),(c:ℂ)],![(c:ℂ),(b:ℂ),(a:ℂ)]] :
          Fin 3 → Fin 3 → ℂ) := by
      simp [weights,a,b,c]
      ring
    have complement (l r : Fin 3) : Q r l * weights (s:ℂ) (t:ℂ) l r = (K:ℂ) := by
      rw [weight_eq]
      fin_cases l <;> fin_cases r <;> simp [Q,x,y,z,K] <;> ring
    choose D hD using normal
    have scaled (l r : Fin 3) : (K:ℂ)*v l r = Q r l*D l := by
      rw [←hD l r,←mul_assoc,complement]
    have rows : Q.mulVec D = fun _ => (K:ℂ)*m := by
      funext r
      change (∑ l, Q r l * D l) = (K:ℂ)*m
      simp_rw [←scaled]
      rw [←Finset.mul_sum,balance]
    have sol := circulant_solution x y z nonzero distinct D ((K:ℂ)*m) rows
    have nC : ((x+y+z : ℝ):ℂ) ≠ 0 := by exact_mod_cast nonzero
    have common : ((x+y+z : ℝ):ℂ)*D 0 = (K:ℂ)*m := by
      rw [sol]
      field_simp
    have left : (K:ℂ)*v 0 2 = (y:ℂ)*D 0 := scaled 0 2
    have right : (K:ℂ)*v 0 1 = (z:ℂ)*D 0 := scaled 0 1
    have product : ((x+y+z : ℝ):ℂ)*(v 0 2-v 0 1) = ((y-z:ℝ):ℂ)*m := by
      apply mul_left_cancel₀ hK
      calc
        _ = ((x+y+z:ℝ):ℂ)*((K:ℂ)*v 0 2-(K:ℂ)*v 0 1) := by ring
        _ = ((y:ℂ)-(z:ℂ))*(((x+y+z:ℝ):ℂ)*D 0) := by rw [left,right]; ring
        _ = _ := by rw [common]; push_cast; ring
    constructor
    · have den : (1+3*(s:ℂ)^2)*((t:ℂ)+(s:ℂ)) ≠ 0 := by exact_mod_cast mul_ne_zero hg.ne' hp.ne'
      have del : -((t:ℂ)-(s:ℂ)) ≠ 0 := by exact_mod_cast neg_ne_zero.mpr hts
      apply (eq_div_iff den).mpr
      apply mul_left_cancel₀ del
      rw [row_sum,contrast] at product
      dsimp [a,m] at product
      push_cast at product
      linear_combination product
    · intro h
      funext l r
      have zero : D l = 0 := by rw [sol]; simp [m,h]
      exact (mul_eq_zero.mp ((scaled l r).trans (by rw [zero,mul_zero]))).resolve_left hK
  have normal_vanish {m : ℕ} (T : Form m) (s : Fin m → ℝ) (distinct : Function.Injective s)
      (above : ∀ i, 1<s i)
      (first : ∀ p x, T x (yPts m p) (zPts s p)=0)
      (second : ∀ p y, T (xPts s p) y (zPts s p)=0)
      (third : ∀ p w, T (xPts s p) (yPts m p) w=0)
      (a : Fin 3) (i : Fin m) (h : Fin 2) (k : Cols m) : T (unit a) (unit (i,h)) (unit k)=0 := by
    classical
    let v (i j : Fin m) (l r : Fin 3) := gamma T s i r (zLoc (s j) j l)
    have transfer (i j : Fin m) (ij : i≠j) :=
      foreign_transfer (above i) (above j) (fun eq => ij (distinct eq)) (v i j) (lam T s i)
        (foreign_constraints T s second third i j) (column_balance T s first second third i j)
    have coefficient (i j : Fin m) :
        gamma T s i 2 (unit (.inl (j,0))) - gamma T s i 1 (unit (.inl (j,0))) =
          2*(coeff T s i*((s j : ℂ)-(s i : ℂ))*(1+(s i : ℂ)^2+2*(s i : ℂ)*(s j : ℂ))/
            ((s j : ℂ)+(s i : ℂ))) := by
      by_cases eq : i=j
      · subst j
        have h₁ := local_vanish T s first second third i 0 1
        have h₂ := local_vanish T s first second third i 0 2
        change gamma T s i 1 (unit (.inl (i,0)))=0 at h₁
        change gamma T s i 2 (unit (.inl (i,0)))=0 at h₂
        simp [h₁,h₂]
      · have given := (transfer i j eq).1
        change gamma T s i 2 (unit (.inl (j,0))) - gamma T s i 1 (unit (.inl (j,0))) = _ at given
        rw [given]
        dsimp only [coeff]
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
    have nodes (j : Fin m) : (∑ i, coeff T s i*((s j : ℂ)-(s i : ℂ))*
        (1+(s i : ℂ)^2+2*(s i : ℂ)*(s j : ℂ))/((s j : ℂ)+(s i : ℂ)))=0 := by
      have eq := last_equation T s third j
      simp_rw [coefficient] at eq
      rw [←Finset.mul_sum] at eq
      exact (mul_eq_zero.mp eq).resolve_left (by norm_num)
    obtain ⟨m₀,m₁⟩ := mixed_moments T s first second third
    have vanish := CriticalHigher.GapTwo.interpolation s distinct above (coeff T s) m₀ m₁ nodes
    have lamzero (i : Fin m) : lam T s i=0 := by
      have eq := congrFun vanish i
      change lam T s i / (1+3*(s i : ℂ)^2)=0 at eq
      exact (div_eq_zero_iff.mp eq).resolve_right (nonzero_den s i)
    have on_points (i j : Fin m) (l r : Fin 3) : gamma T s i r (zLoc (s j) j l)=0 := by
      by_cases eq : i=j
      · subst j; exact local_vanish T s first second third i l r
      · exact congrFun (congrFun ((transfer i j eq).2 (lamzero i)) l) r
    have shared1 (i : Fin m) (r : Fin 3) : gamma T s i r (unit (.inr 1))=0 :=
      (mixed_lambda T s second third i r).trans (lamzero i)
    have shared0 (i : Fin m) (r : Fin 3) : gamma T s i r (unit (.inr 0))=0 := by
      have eq : (gamma T s i r) (unit (.inr 0)+(s i : ℂ) • unit (.inr 1))=0 := by
        rw [←sum_zLoc _ i,map_sum]
        exact Finset.sum_eq_zero (fun l _ => on_points i i l r)
      simpa only [map_add,map_smul,smul_eq_mul,shared1,mul_zero,add_zero] using eq
    have all_gamma (r : Fin 3) : gamma T s i r (unit k)=0 := by
      rcases k with ⟨j,u⟩|u
      · fin_cases u
        · exact on_points i j 0 r
        · exact on_points i j 1 r
      · fin_cases u
        · exact shared0 i r
        · exact shared1 i r
    have small (r : Fin 3) : T (frame (s i) r) (unit (i,h)) (unit k)=0 := by
      rw [read_gamma T s third,all_gamma,zero_mul]
    have eq := congrArg (fun b : (Fin 3 → ℂ) => T b (unit (i,h)) (unit k)) (frame_transfer (s i) 0 a)
    simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,smul_eq_mul,small,mul_zero,
      Finset.sum_const_zero,frame_zero] at eq
    exact (mul_eq_zero.mp eq.symm).resolve_left (nonzero_den s i)
  have spans_of_normal {m : ℕ} (s : Fin m → ℝ)
      (normal : ∀ T : Form m,
        (∀ p x, T x (yPts m p) (zPts s p)=0) →
        (∀ p y, T (xPts s p) y (zPts s p)=0) →
        (∀ p w, T (xPts s p) (yPts m p) w=0) →
        ∀ a i h k, T (unit a) (unit (i,h)) (unit k)=0) :
      Spans 3 (2*m) (2*m+2) (3*m+1) := by
    classical
    let er : Rows m ≃ Fin (2*m) := finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))
    let ec : Cols m ≃ Fin (2*m+2) := (Equiv.sumCongr er (Equiv.refl _)).trans finSumFinEquiv
    let ep : Pts m ≃ Fin (3*m+1) := Fintype.equivOfCardEq (by simp [Pts,Nat.mul_comm])
    have spans := tangent_of_basis_vanishing (xPts s) (yPts m) (zPts s)
      (fun T hx hy hz a ⟨i,h⟩ k => normal T hx hy hz a i h k)
    refine ⟨fun t a => xPts s (ep.symm t) a,
      fun t j => yPts m (ep.symm t) (er.symm j),
      fun t k => zPts s (ep.symm t) (ec.symm k),?_⟩
    intro T
    obtain ⟨u,v,w,hit⟩ := spans (fun a j k => T a (er j) (ec k))
    refine ⟨fun t a => u (ep.symm t) a,fun t j => v (ep.symm t) (er.symm j),
      fun t k => w (ep.symm t) (ec.symm k),?_⟩
    intro a j k
    let summand (p : Pts m) := u p a*(yPts m p (er.symm j)*zPts s p (ec.symm k))+
      xPts s p a*(v p (er.symm j)*zPts s p (ec.symm k))+
      xPts s p a*(yPts m p (er.symm j)*w p (ec.symm k))
    have eq : T a j k=∑ p,summand p := by
      simpa only [summand,Equiv.apply_symm_apply] using hit a (er.symm j) (ec.symm k)
    exact eq.trans (ep.symm.sum_comp summand).symm
  have spans_of_node_theorem {m : ℕ}
      (normal : ∀ (T : Form m) (s : Fin m → ℝ), Function.Injective s → (∀ i, 1 < s i) →
        (∀ p x, T x (yPts m p) (zPts s p)=0) →
        (∀ p y, T (xPts s p) y (zPts s p)=0) →
        (∀ p w, T (xPts s p) (yPts m p) w=0) →
        ∀ a i h k, T (unit a) (unit (i,h)) (unit k)=0) :
      Spans 3 (2*m) (2*m+2) (3*m+1) := by
    let s (i : Fin m) : ℝ := i.val+2
    have inj : Function.Injective s := by
      intro i j h
      change (i.val:ℝ)+2=(j.val:ℝ)+2 at h
      exact Fin.ext (Nat.cast_injective (add_right_cancel h))
    have above (i : Fin m) : 1 < s i := by
      have nonneg : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
      dsimp [s]
      linarith
    exact spans_of_normal s (fun T => normal T s inj above)
  exact spans_of_node_theorem (normal_vanish (m:=m))

end CriticalHigher.GapTwo.Mixed

namespace HigherNormalFrontier

/-- The untruncated endpoint can coincide with the first registered
third dimension only at the even width b=2h+2. -/
theorem minimum_endpoint_even {b h r n : ℕ} (hh : 4≤h) (width : 2*h≤b) (level : r+h=2*b)
    (endpoint : n=r*(b+1)/(b+h)) (gap : n=b+2) : b=2*h+2 := by
  have pos : 0<b+h := by omega
  have lower := (Nat.le_div_iff_mul_le pos).mp (show b+2≤r*(b+1)/(b+h) by omega)
  have upper := (Nat.div_lt_iff_lt_mul pos).mp (show r*(b+1)/(b+h)<b+3 by omega)
  have product := congrArg (fun t : ℕ => t*(b+1)) level
  by_contra bad
  by_cases low : b≤2*h+1
  · have bound := Nat.mul_le_mul_right b low
    nlinarith only [product,lower,bound,low,hh]
  · have large : 2*h+3≤b := by omega
    have bound := Nat.mul_le_mul_right b large
    nlinarith only [product,upper,bound,width]

end HigherNormalFrontier

namespace HigherNormalFrontier

open Arxiv.«0805.3777»

/-- In a single component, taking every physical label as a mark proves
the strengthened Cauchy bound. The short hubs impose the tightest test. -/
theorem one_component {h b n r : ℕ} (hh : 2≤h) (width : 2*h≤b) (ord : b≤n)
    (level : r+h=2*b) (count : 3*b*n ⌈/⌉ (b+n+1)=r)
    (cap : r+1≤(r-n+2)*(b/h)+(r-n)) : IsGenericRank [3,b,n] r := by
  let d := b/h
  let s := b%h
  let q := r-n
  let g (i : Fin h) := if i.val<s then d else d-1
  let e (i : Fin h) := 2*g i+1
  have nr := (CriticalThreeComponents.component_length_bound hh level count).2
  have hd : 2≤d := (Nat.le_div_iff_mul_le (by omega : 0<h)).mpr width
  have hs : s<h := Nat.mod_lt _ (by omega)
  have base : h*d+s=b := Nat.div_add_mod b h
  have totals := CriticalThreeCubic.hub_totals hs.le (by omega : 1≤d)
  dsimp only at totals
  rw [base,show 2*b-h=r by omega] at totals
  have enough : r≤q*(d+1)+(2*(d-1)+1) := by
    change r+1≤(q+2)*d+q at cap
    rw [Nat.add_mul] at cap
    rw [Nat.mul_add,Nat.mul_one]
    omega
  refine CriticalLastSlice.TwoPlanes.generic_rank_of_witness (by decide) (by omega) ord ?_ ?_
  · simpa only [show 3+b+n-2=b+n+1 by omega] using count.symm
  · apply CriticalThreeComponents.tangent_of_components (by omega : h≤b) nr level
      (fun _ : Fin 1 => q) (fun _ => r) (by simp [q]) (by simp) (fun _ => Nat.sub_le _ _)
    intro _
    refine ⟨g,e,totals.1,totals.2,?_⟩
    intro i
    have low : d-1≤g i := by dsimp [g]; split <;> omega
    have qsize := Nat.mul_le_mul_left q (show d+1≤g i+2 by omega)
    change e i≤e i ∧ r-e i≤q*(g i+2)
    dsimp only [e]
    omega

/-- If h divides b, the dimension count already gives the single-component
capacity. Thus no divisible width reaches the remaining three-slice step. -/
theorem divisible_count {h b n r : ℕ} (hh : 2≤h) (width : 2*h≤b) (ord : b≤n)
    (level : r+h=2*b) (count : 3*b*n ⌈/⌉ (b+n+1)=r) (div : h∣b) :
    IsGenericRank [3,b,n] r := by
  obtain ⟨d,rfl⟩ := div
  have pos : 0<h := by omega
  have hd := Nat.le_of_mul_le_mul_left (by simpa only [Nat.mul_comm h 2] using width : h*2≤h*d) pos
  have twice : 2*d-1+1=2*d := by omega
  have pp := congrArg (fun t : ℕ => h*t) twice
  have rs : r=h*(2*d-1) := by nlinarith only [level,pp]
  have mass := (ceilDiv_le_iff_le_mul (by omega : 0<h*d+n+1)).mp count.le
  have nr := (CriticalThreeComponents.component_length_bound hh level count).2
  have weighted := congrArg (fun t : ℕ => t*n) level
  have scale := congrArg (fun t : ℕ => t*(h*d+h)) (Nat.sub_add_cancel nr)
  have budget : (h-1)*r≤(r-n)*(h*d+h) := by
    have rem := congrArg (fun t : ℕ => t*r) (Nat.sub_add_cancel (by omega : 1≤h))
    nlinarith only [mass,weighted,scale,rem]
  have bound : (h-1)*(2*d-1)≤(r-n)*(d+1) := by
    apply Nat.le_of_mul_le_mul_left _ pos
    calc
      h*((h-1)*(2*d-1)) = (h-1)*r := by rw [rs]; ring
      _ ≤ (r-n)*(h*d+h) := budget
      _ = h*((r-n)*(d+1)) := by ring
  apply one_component hh width ord level count
  rw [Nat.mul_div_cancel_left _ pos,Nat.add_mul]
  have add := congrArg (fun t : ℕ => t*(2*d-1)) (Nat.sub_add_cancel (by omega : 1≤h))
  rw [Nat.add_mul,Nat.one_mul,←rs] at add
  rw [Nat.mul_add,Nat.mul_one] at bound
  omega

end HigherNormalFrontier

namespace HigherNormalFrontier

open Arxiv.«0805.3777»

set_option maxRecDepth 4000 in
/-- Infinitely many actual level-ten endpoints miss both screens of the
earlier reduction. The unconditioned three-quarter theorem gives their
generic ranks. In this family the cyclic bound falls short by five. -/
theorem level_ten_progress (t : ℕ) :
    let b := 20*t+267
    let n := 40*t+506
    let r := 40*t+524
    let pencil (x y z : ℕ) := ∃ k m : ℕ, z=2*k ∧ k*m≤r ∧ 2 ≤ m ∧ m≤x ∧ m≤y ∧
      m≤r ∧ 2*(x*y-r)≤ m*(x+y-2)
    n=r*(b+1)/(b+10) ∧ 3*b*n ⌈/⌉ (b+n+1)=r ∧
      ¬(pencil 3 b n ∨ pencil b n 3 ∨ pencil 3 n b) ∧
      ¬(∃ j : ℕ,0<j ∧ 3*j≤b ∧ n≤r ∧ r+j=2*b ∧ r+1≤(r-n+2)*(b/j)) ∧
      IsGenericRank [3,b,n] r := by
  intro b n r pencil
  have level : r+10=2*b := by dsimp [r,b]; omega
  have offset : r*(b+1)=270+n*(b+10) := by dsimp [r,b,n]; ring
  have cost : (b+n+1)*r=3*b*n+270 := by dsimp [r,b,n]; ring
  have pos : 0<b+n+1 := by omega
  have endpoint : n=r*(b+1)/(b+10) := by
    have dp : 0<b+10 := by omega
    have left : n≤r*(b+1)/(b+10) := (Nat.le_div_iff_mul_le dp).mpr (by omega)
    have right : r*(b+1)/(b+10)<n+1 := (Nat.div_lt_iff_lt_mul dp).mpr (by
      have ample : 270<b+10 := by dsimp [b]; omega
      calc
        _ = 270+n*(b+10) := offset
        _ < (b+10)+n*(b+10) := Nat.add_lt_add_right ample _
        _ = (n+1)*(b+10) := by ring)
    omega
  have count : 3*b*n ⌈/⌉ (b+n+1)=r := by
    apply le_antisymm ((ceilDiv_le_iff_le_mul pos).mpr (by omega)) _
    by_contra! tooLow
    have cover := (ceilDiv_le_iff_le_mul (a:=b+n+1) (b:=3*b*n) pos).mp le_rfl
    have deficit := Nat.mul_le_mul_left (b+n+1) (show (3*b*n ⌈/⌉ (b+n+1))+1≤r by omega)
    rw [Nat.mul_add,Nat.mul_one] at deficit
    have ample : 270<b+n+1 := by dsimp [b,n]; omega
    omega
  refine ⟨endpoint,count,?_,?_,?_⟩
  · rintro (⟨k,m,e,slots,lo,hi,_,_,cap⟩|⟨k,m,e,_,_,_,_,_,_⟩|⟨k,m,e,_,_,_,_,_,_⟩)
    · obtain rfl|rfl : m=2 ∨ m=3 := by omega
      · dsimp [r,b] at cap
        omega
      · dsimp [n] at e
        dsimp [r] at slots
        omega
    · omega
    · dsimp [b] at e
      omega
  · rintro ⟨j,_,_,_,lev,cap⟩
    obtain rfl : j=10 := by omega
    have q : r-n+2=20 := by dsimp [r,n]; omega
    have d : b/10=2*t+26 := by dsimp [b]; omega
    rw [q,d] at cap
    dsimp [r] at cap
    omega
  · exact CriticalThreeQuarter.rank_in_upper_range (by decide : 8≤10) (by dsimp [b,n]; omega)
      (by dsimp [b]; omega) (by dsimp [b]; omega) level count (by dsimp [b]; omega)

end HigherNormalFrontier

namespace OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1_H2_R2

open Arxiv.«0805.3777»

/-- Eight explicit finite seed ranks in the level classifications. -/
def H1 : Prop :=
  IsGenericRank [3,14,18] 23 ∧ IsGenericRank [3,24,37] 43 ∧
  IsGenericRank [3,16,20] 26 ∧ IsGenericRank [3,23,33] 40 ∧
  IsGenericRank [3,18,22] 29 ∧ IsGenericRank [3,24,33] 41 ∧
  IsGenericRank [3,23,29] 38 ∧ IsGenericRank [3,47,75] 86

/-- The single sharp middle width on the even levels from ten upward.
The third dimension here is the actual upper endpoint of the rank interval. -/
def H2 : Prop :=
  ∀ h : ℕ, 10≤h → Even h →
    let b := h*(h-2)-1
    let r := 2*b-h
    IsGenericRank [3,b,r-(2*h-5)] r

/-- Strictly interior widths outside the pencil, single-component and
balanced-component tests. Only the largest third dimension at each
such width can be needed. -/
def H3 : Prop :=
  ∀ b h : ℕ, 9≤h → 2*h≤b → b%h≠0 → 4*b+7*h≤3*h^2 → b+1<h*(h-2) →
    let r := 2*b-h
    let n := r*(b+1)/(b+h)
    b+2<n → 3*b*n ⌈/⌉ (b+n+1)=r →
    let pencil (u v w : ℕ) := ∃ k m : ℕ, w=2*k ∧ k*m≤r ∧ 2≤ m ∧ m≤u ∧ m≤v ∧
      m≤r ∧ 2*(u*v-r)≤ m*(u+v-2)
    ¬(pencil 3 b n ∨ pencil b n 3 ∨ pencil 3 n b) →
    ¬(r+1≤(r-n+2)*(b/h)+(r-n)) →
    ¬(∃ C : ℕ, ∃ q M : Fin C → ℕ, (∑ c,q c)=r-n ∧ (∑ c,M c)=r ∧
        ∀ c, q c≤M c ∧ M c≤r ∧ M c≤q c*(b/h+1)+2*(b/h)-1 ∧
          (h-1)*M c≤q c*(b+h) ∧ (h-b%h-1)*M c≤q c*(h-b%h)*(b/h+1)) →
    IsGenericRank [3,b,n] r

/-- For every larger first dimension it suffices to check the single
largest admissible third dimension at ranks outside the three pencil families. -/
def H4 : Prop :=
  ∀ a b r : ℕ, 4 ≤ a → a ≤ b → 0<r → r+1<(a-1)*(b-1) →
    let A := a*b
    let d := a+b-2
    let N := r*d/(A-r)
    b+2 ≤ N → (r-1)*d/(A-(r-1))<N →
    let pencil (u v w : ℕ) := ∃ h m : ℕ, w=2*h ∧ h*m ≤ r ∧ 2 ≤ m ∧
      m ≤ u ∧ m ≤ v ∧ m ≤ r ∧ 2*(u*v-r) ≤ m*(u+v-2)
    ¬(pencil a b N ∨ pencil b N a ∨ pencil a N b) →
    let D := 2*(a*b*N)+1
    ∃ x : Fin r → Fin a → Fin D, ∃ y : Fin r → Fin b → Fin D, ∃ z : Fin r → Fin N → Fin D,
      ∀ T : Fin a → Fin b → Fin N → ℂ, ∃ u : Fin r → Fin a → ℂ,
      ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin N → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i*(((y t j).val : ℂ)*((z t k).val : ℂ)) +
          ((x t i).val : ℂ)*(v t j*((z t k).val : ℂ)) +
          ((x t i).val : ℂ)*(((y t j).val : ℂ)*w t k))

end OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1_H2_R2

namespace OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1_H2_R2

open Arxiv.«0805.3777»

/-- A proof at the even sharp endpoint together with the odd conic
theorem covers every admissible third dimension on this width. -/
theorem sharp_for_count (boundary : H2) {b h n r : ℕ} (high : 9≤h) (width : 2*h≤b)
    (order : b≤n) (level : r+h=2*b) (count : 3*b*n ⌈/⌉ (b+n+1)=r)
    (edge : b+1=h*(h-2)) : IsGenericRank [3,b,n] r := by
  have size : h*(h-2)-1=b := by omega
  have rsize : r=2*b-h := by omega
  have dims := CriticalThreeComponents.component_length_bound (by omega : 2≤h) level count
  have bound : n≤ min (2*(b-1)) (r*(b+1)/(b+h)) := le_min (by omega) dims.1
  have top := ComponentFrontier.clipped_preceding_endpoint (by omega : 5≤h) edge
  dsimp only at top
  rw [←rsize] at top
  have solved : IsGenericRank [3,b,r-(2*h-5)] r := by
    rcases Nat.even_or_odd h with even|odd
    · have ten : 10≤h := by obtain ⟨t,ht⟩ := even;omega
      have hit := boundary h ten even
      dsimp only at hit
      rwa [size,←rsize] at hit
    · have hit := CriticalConicBoundary.odd_boundary_rank h (by omega) odd
      dsimp only at hit
      rwa [size,←rsize] at hit
  apply CriticalLastSlice.TwoPlanes.generic_rank_of_witness (by decide) (by omega) order _
    (CriticalHigher.project (bound.trans_eq top) (CriticalHigher.GenericTangent.of_generic solved))
  simpa only [show 3+b+n-2=b+n+1 by omega] using count.symm

/-- A single family of even sharp boundaries suffices for the complete
upper width range, all levels h≥9 and every ordered third dimension
with the indicated rank count. -/
theorem all_upper_widths (boundary : H2) {b h n r : ℕ} (high : 9≤h) (order : b≤n)
    (upper : 3*h^2<4*b+7*h) (level : r+h=2*b)
    (count : 3*b*n ⌈/⌉ (b+n+1)=r) : IsGenericRank [3,b,n] r := by
  have width : 2*h≤b := by nlinarith only [Nat.mul_le_mul_left h high,upper]
  by_cases edge : b+1=h*(h-2)
  · exact sharp_for_count boundary high width order level count edge
  · exact CriticalThreeQuarter.rank_in_upper_range (by omega) order width upper level count edge

/-- Endpoint rank at every three-slice width from the four partial
families. The unbounded width theorem is used before the interior oracle. -/
theorem three_rank (seeds : H1) (boundary : H2) (interior : H3)
    (b h : ℕ) (hb : 3≤b) (hh : 4≤h) (width : 2*h≤b) :
    let r := 2*b-h
    let n := r*(b+1)/(b+h)
    b+2≤n → 3*b*n ⌈/⌉ (b+n+1)=r →
    let pencil (u v w : ℕ) := ∃ k m : ℕ, w=2*k ∧ k*m≤r ∧ 2≤ m ∧ m≤u ∧ m≤v ∧
      m≤r ∧ 2*(u*v-r)≤ m*(u+v-2)
    ¬(pencil 3 b n ∨ pencil b n 3 ∨ pencil 3 n b) → IsGenericRank [3,b,n] r := by
  intro r n start count pencil screened
  obtain ⟨s14,s24,s16,s23,s18,s24b,s23b,s47⟩ := seeds
  have level : r+h=2*b := Nat.sub_add_cancel (by omega : h≤2*b)
  have nr := (CriticalThreeComponents.component_length_bound (by omega : 2≤h) level count).2
  have order : b≤n := by omega
  have clip : min (2*(b-1)) (r*(b+1)/(b+h))=n := Nat.min_eq_right (by change n≤2*(b-1); omega)
  by_cases wide : h*(h-2)≤b
  · by_cases special : h=5 ∧ b=24 ∧ n=37
    · obtain ⟨eh,eb,en⟩ := special
      rw [eb,en,show r=43 by omega]
      exact s24
    · exact CriticalThreeComponents.rank_above_threshold (by omega) order width wide level count special
  by_cases five : h=5
  · subst h
    have small : b<15 := by norm_num at wide; omega
    have hit := ComponentFrontier.fifth_below s14 b width small
    dsimp only at hit
    rw [←clip]
    exact hit
  by_cases six : h=6
  · subst h
    exact CriticalThreeComponents.sixth_rank_of_two_seeds s16 s23 hb order (by omega) count
  by_cases seven : h=7
  · subst h
    exact CriticalHigher.SevenEight.seven_of_seeds s18 s24b CriticalConicBoundary.boundary_h7 hb order
      (by intro eq; have p : b=13 := congrArg Prod.fst eq; have q : n=13 := congrArg Prod.snd eq; omega) count
  by_cases eight : h=8
  · subst h
    exact CriticalHigher.SevenEight.eight_of_seeds s23b s47 hb order (by intro eq; have p : b=15 := congrArg Prod.fst eq; have q : n=15 := congrArg Prod.snd eq; omega) count
  have high : 9≤h := by
    by_contra! small
    interval_cases h <;> norm_num at wide width <;> omega
  by_cases edge : b+1=h*(h-2)
  · exact sharp_for_count boundary high width order level count edge
  by_cases upper : 3*h^2<4*b+7*h
  · exact all_upper_widths boundary high order upper level count
  by_cases firstEnd : n=b+2
  · have small := HigherNormalFrontier.minimum_endpoint_even hh width level (show n=r*(b+1)/(b+h) from rfl) firstEnd
    have ordSize : 2*(h+1)=b := by omega
    have rankSize : 3*(h+1)+1=r := by omega
    have tangent := CriticalHigher.GapTwo.Mixed.gap_two_even (h+1)
    rw [ordSize,←firstEnd,rankSize] at tangent
    apply CriticalLastSlice.TwoPlanes.generic_rank_of_witness (by decide) hb order _ tangent
    simpa only [show 3+b+n-2=b+n+1 by omega] using count.symm
  have deeper : b+2<n := by omega
  by_cases rem : b%h=0
  · exact HigherNormalFrontier.divisible_count (by omega) width order level count (Nat.dvd_of_mod_eq_zero rem)
  by_cases cap : r+1≤(r-n+2)*(b/h)+(r-n)
  · exact HigherNormalFrontier.one_component (by omega) width order level count cap
  by_cases packing : ∃ C : ℕ, ∃ q M : Fin C→ℕ, (∑ c,q c)=r-n ∧ (∑ c,M c)=r ∧
      ∀ c, q c≤M c ∧ M c≤r ∧ M c≤q c*(b/h+1)+2*(b/h)-1 ∧
        (h-1)*M c≤q c*(b+h) ∧ (h-b%h-1)*M c≤q c*(h-b%h)*(b/h+1)
  · obtain ⟨C,q,M,rows,marks,each⟩ := packing
    exact CriticalThreeComponents.rank_of_partition (by omega) hb order nr level width count q M rows marks each
  exact interior b h high width rem (by omega) (by omega) deeper count screened cap packing

/-- Spanning at a rank-interval endpoint suffices for every third dimension
covered by that interval. An attained complex rank supplies the spanning
tangent by the characteristic-zero Jacobian criterion. -/
theorem main : H1 → H2 → H3 → H4 → OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1.H2 := by
  intro seeds boundary interior larger
  apply CriticalHigher.higher_iff_endpoints.mpr
  intro a b r ha hab hr level A d N start present
  let pencil (u v w : ℕ) := ∃ k m : ℕ, w=2*k ∧ k*m≤r ∧ 2≤ m ∧ m≤u ∧ m≤v ∧
    m≤r ∧ 2*(u*v-r)≤ m*(u+v-2)
  by_cases screened : pencil a b N ∨ pencil b N a ∨ pencil a N b
  · exact CriticalHigher.tangent_of_pencil_screen screened
  by_cases first : a=3
  · subst a
    let h := 2*b-r
    change r+1<2*(b-1) at level
    have hi : 4≤h := by dsimp only [h]; omega
    have lev : r+h=2*b := by dsimp only [h]; omega
    have proper : r<3*b := by omega
    have number := (CriticalHigher.count_interval (by dsimp [d]; omega : 0<d) hr (show r<A from proper)).mpr
      (show (r-1)*d/(A-(r-1))<N ∧ N≤r*d/(A-r) from ⟨present,le_rfl⟩)
    have count : 3*b*N ⌈/⌉ (b+N+1)=r := by
      simpa only [A,d,show 3+b-2+N=b+N+1 by omega] using number
    have val : 2*b-h=r := by omega
    have shape : N=r*(b+1)/(b+h) := by
      dsimp only [N,A,d]
      rw [show 3+b-2=b+1 by omega,show 3*b-r=b+h by omega]
    have width := CriticalThreeTop.strict_width_at_least_twice (by omega : 0<b)
      (by omega : b<N) (count.trans val.symm)
    have hit := three_rank seeds boundary interior b h hab hi width
    dsimp only at hit
    rw [val,←shape] at hit
    exact CriticalHigher.GenericTangent.of_generic (hit start count screened)
  · obtain ⟨x,y,z,span⟩ := larger a b r (by omega) hab hr level start present screened
    exact ⟨fun t i => (x t i).val,fun t j => (y t j).val,fun t k => (z t k).val,span⟩

end OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1_H2_R2

namespace HigherNormalFrontier

open Arxiv.«0805.3777»

/-- Every attained rank of the registered three-slice portion follows
from its rational-function normal statement. -/
theorem registered_rank (higher : OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1.H2)
    (b n r : ℕ) (hb : 3≤b) (gap : b+2≤n) (level : r+1<2*(b-1))
    (count : 3*b*n ⌈/⌉ (b+n+1)=r) : IsGenericRank [3,b,n] r := by
  refine CriticalLastSlice.TwoPlanes.generic_rank_of_witness (by decide) hb (by omega) ?_ ?_
  · simpa only [show 3+b+n-2=b+n+1 by omega] using count.symm
  · apply CriticalHigher.witness_at_count higher (by decide) hb gap level
    simpa only [show 3+b-2+n=b+n+1 by omega] using count

/-- The sharp boundary at all levels from ten lies in the registered range
with its unclipped upper third dimension. -/
theorem sharp_registered (higher : OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1.H2)
    (h : ℕ) (high : 10≤h) :
    let b := h*(h-2)-1
    let r := 2*b-h
    IsGenericRank [3,b,r-(2*h-5)] r := by
  intro b r
  have big := Nat.mul_le_mul_left h (show 5≤h-2 by omega)
  have massive : 4*h≤b := by dsimp only [b]; omega
  have edge : b+1=h*(h-2) := Nat.sub_add_cancel (by omega)
  let d := h-3
  have dd : d+3=h := by dsimp [d]; omega
  have preceding := CriticalThreeCubic.preceding_endpoint d (by dsimp [d]; omega)
  dsimp only at preceding
  rw [dd] at preceding
  have tick := preceding.1
  have bs : h*d+(d+2)=b := by omega
  rw [bs,show 2*d+1=2*h-5 by dsimp [d]; omega] at preceding
  apply registered_rank higher b (r-(2*h-5)) r (by omega) _ _ preceding.2.2.2
  · dsimp only [r]; omega
  · dsimp only [r]; omega

end HigherNormalFrontier

namespace OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1_H2_R2

/-- Each of the eight numerical seed statements is in the registered
higher-normal problem, including the four widths on levels seven and eight. -/
theorem seeds_of_registered
    (higher : OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1.H2) : H1 := by
  unfold H1
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals apply HigherNormalFrontier.registered_rank higher <;> decide

theorem sharp_of_registered
    (higher : OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1.H2) : H2 :=
  fun h high _ => HigherNormalFrontier.sharp_registered higher h high

theorem interior_of_registered
    (higher : OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1.H2) : H3 := by
  intro b h high width _ _ _ r n start count pencil _ _ _
  exact HigherNormalFrontier.registered_rank higher b n r (by omega) (by omega) (by dsimp only [r]; omega) count

theorem larger_of_registered
    (higher : OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1.H2) : H4 := by
  intro a b r ha hab hr level A d N start present pencil unscreened D
  exact CriticalReduction.bounded_of_witness
    (CriticalHigher.higher_iff_endpoints.mp higher a b r (by omega) hab hr level start present)

theorem equivalent : H1 ∧ H2 ∧ H3 ∧ H4 ↔
    OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1.H2 :=
  ⟨fun h => main h.1 h.2.1 h.2.2.1 h.2.2.2,fun p =>
     ⟨seeds_of_registered p,sharp_of_registered p,interior_of_registered p,larger_of_registered p⟩⟩

end OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1_H2_R2
