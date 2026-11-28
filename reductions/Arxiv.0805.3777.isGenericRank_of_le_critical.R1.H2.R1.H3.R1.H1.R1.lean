import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1

/-! Consecutive tensor formats and a smaller generic tangent test.

For four slices, two points per middle coordinate span each fiber after a
common polynomial specialization. In larger formats, the independent
first-two-factor products span a subspace of dimension r. The third-factor
variations fill that subspace in every slice. Passing to the quotient and
removing two redundant scalar directions per point leaves a canonical
linear test with r*(a+b-2) scalar inputs and c*(ab-r) outputs for the actual
format a by b by c. Both directions of the equivalence are proved.

Direct sums of first factors give a quantitative upper bound from the
three- and five-slice cases. For fixed first dimension its excess over the
parameter-count prediction is bounded independently of the two larger
dimensions. Friedland, On the generic and typical ranks of 3-tensors,
Conjecture 5.1, gives the expected rank in this range.
https://arxiv.org/abs/0805.3777
-/

namespace CriticalJacobian

open MvPolynomial

/-- Complex spanning at some choice of factors is equivalent to spanning
at the single tuple of independent indeterminates over its rational function field. -/
theorem generic_tangent_iff (a b c r : ℕ) :
    (∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin c → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))) ↔
    let V := Fin r × (Fin a ⊕ (Fin b ⊕ Fin c))
    let R := MvPolynomial V ℂ
    let K := FractionRing R
    let coord : V → K := fun s => algebraMap R K (X s)
    let x (t : Fin r) (i : Fin a) := coord (t,.inl i)
    let y (t : Fin r) (j : Fin b) := coord (t,.inr (.inl j))
    let z (t : Fin r) (k : Fin c) := coord (t,.inr (.inr k))
    ∀ T : Fin a → Fin b → Fin c → K, ∃ u : Fin r → Fin a → K,
      ∃ v : Fin r → Fin b → K, ∃ w : Fin r → Fin c → K, ∀ i j k,
        T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
  let V := Fin r × (Fin a ⊕ (Fin b ⊕ Fin c))
  let R := MvPolynomial V ℂ
  let K := FractionRing R
  let φ : R →+* K := algebraMap R K
  let coord (s : V) : K := φ (X s)
  let P : Matrix ((Fin a × Fin b) × Fin c) V R := fun row col =>
    col.2.elim (fun i => if i=row.1.1 then X (col.1,.inr (.inl row.1.2))*X (col.1,.inr (.inr row.2)) else 0)
      (Sum.elim (fun j => if j=row.1.2 then X (col.1,.inl row.1.1)*X (col.1,.inr (.inr row.2)) else 0)
        (fun k => if k=row.2 then X (col.1,.inl row.1.1)*X (col.1,.inr (.inl row.1.2)) else 0))
  have specialized := restricted_tangent_iff (a:=a) (b:=b) (c:=c) (r:=r) id P (fun _ _ _ _ _ => rfl)
  have generic := CriticalTensor.Unrestricted.generic_surjective_iff P
  apply specialized.trans (generic.symm.trans ?_)
  have action (q : V → K) (i : Fin a) (j : Fin b) (k : Fin c) :
      (P.map φ).mulVec q ((i,j),k) = ∑ t : Fin r,
        (q (t,.inl i)*(coord (t,.inr (.inl j))*coord (t,.inr (.inr k))) +
         coord (t,.inl i)*(q (t,.inr (.inl j))*coord (t,.inr (.inr k))) +
         coord (t,.inl i)*(coord (t,.inr (.inl j))*q (t,.inr (.inr k)))) := by
    change (∑ s : V, φ (P ((i,j),k) s)*q s) = _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
    simp [P,coord,apply_ite,ite_mul,Finset.sum_ite_eq']
    ring
  let pack (u : Fin r → Fin a → K) (v : Fin r → Fin b → K) (w : Fin r → Fin c → K) : V → K :=
    fun (t,s) => s.elim (u t) (Sum.elim (v t) (w t))
  constructor
  · intro onto
    dsimp only
    intro T
    obtain ⟨q,hq⟩ := onto (fun s => T s.1.1 s.1.2 s.2)
    refine ⟨fun t i => q (t,.inl i),fun t j => q (t,.inr (.inl j)),fun t k => q (t,.inr (.inr k)),?_⟩
    intro i j k
    exact (congrFun hq ((i,j),k)).symm.trans (action q i j k)
  · intro spans T
    obtain ⟨u,v,w,hit⟩ := spans (fun i j k => T ((i,j),k))
    refine ⟨pack u v w,?_⟩
    funext ⟨⟨i,j⟩,k⟩
    exact (action (pack u v w) i j k).trans (hit i j k).symm

end CriticalJacobian

namespace ConsecutiveQuotient

/-- One independent family of coefficients on every slice realizes exactly
the functions whose individual values lie in the span of the generators. -/
theorem third_variations_iff {K E I C : Type*} [Field K] [AddCommGroup E] [Module K E]
    [Fintype I] (g : I → E) (D : C → E) :
    (∃ w : I → C → K, ∀ k, D k = ∑ t, w t k • g t) ↔
      ∀ k, D k ∈ Submodule.span K (Set.range g) := by
  classical
  constructor
  · rintro ⟨w,hw⟩ k
    exact (Submodule.mem_span_range_iff_exists_fun K).mpr ⟨fun t => w t k,(hw k).symm⟩
  · intro h
    choose w hw using fun k => (Submodule.mem_span_range_iff_exists_fun K).mp (h k)
    exact ⟨fun t k => w k t, fun k => (hw k).symm⟩

/-- Surjectivity after adjoining the generator directions on every slice is
equivalent to surjectivity of the remaining map modulo their common span. -/
theorem quotient_range_iff {K E I C U : Type*} [Field K] [AddCommGroup E] [Module K E]
    [Fintype I] (g : I → E) (L : U → C → E) :
    (∀ F : C → E, ∃ u : U, ∃ w : I → C → K, ∀ k, F k = L u k + ∑ t, w t k • g t) ↔
      Function.Surjective (fun (u : U) (k : C) =>
        (Submodule.span K (Set.range g)).mkQ (L u k)) := by
  classical
  let W := Submodule.span K (Set.range g)
  have lift_iff (F H : C → E) :
      (∃ w : I → C → K, ∀ k, F k = H k + ∑ t, w t k • g t) ↔
        ∀ k, W.mkQ (F k) = W.mkQ (H k) := by
    calc
      _ ↔ (∃ w : I → C → K, ∀ k, F k - H k = ∑ t, w t k • g t) := by
        simp only [sub_eq_iff_eq_add']
      _ ↔ (∀ k, F k - H k ∈ W) := third_variations_iff g (fun k => F k - H k)
      _ ↔ _ := forall_congr' fun k => (Submodule.Quotient.eq W).symm
  constructor
  · intro full y
    choose F hF using fun k => W.mkQ_surjective (y k)
    obtain ⟨u,w,hu⟩ := full F
    have same := (lift_iff F (L u)).mp ⟨w,hu⟩
    exact ⟨u,funext fun k => (same k).symm.trans (hF k)⟩
  · intro compressed F
    obtain ⟨u,hu⟩ := compressed (fun k => W.mkQ (F k))
    exact ⟨u,(lift_iff F (L u)).mpr (fun k => (congrFun hu k).symm)⟩

/-- In the tangent space to a sum of simple tensors, quotient out the span
of the fixed first-two-factor products on every third-axis slice. Only the
first and second variations remain in the resulting surjectivity test. -/
theorem tangent_iff_compressed {K : Type*} [Field K] {a b c r : ℕ}
    (x : Fin r → Fin a → K) (y : Fin r → Fin b → K) (z : Fin r → Fin c → K) :
    let g (t : Fin r) (ij : Fin a × Fin b) := x t ij.1 * y t ij.2
    let W := Submodule.span K (Set.range g)
    (∀ T : Fin a → Fin b → Fin c → K,
      ∃ u : Fin r → Fin a → K, ∃ v : Fin r → Fin b → K, ∃ w : Fin r → Fin c → K,
        ∀ i j k, T i j k = ∑ t,
          (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))) ↔
      Function.Surjective (fun (uv : (Fin r → Fin a → K) × (Fin r → Fin b → K)) (k : Fin c) =>
        W.mkQ (∑ t, z t k • (fun ij : Fin a × Fin b =>
          uv.1 t ij.1 * y t ij.2 + x t ij.1 * uv.2 t ij.2))) := by
  classical
  let g (t : Fin r) (ij : Fin a × Fin b) := x t ij.1 * y t ij.2
  let L (uv : (Fin r → Fin a → K) × (Fin r → Fin b → K)) (k : Fin c) : Fin a × Fin b → K :=
    ∑ t, z t k • (fun ij : Fin a × Fin b => uv.1 t ij.1 * y t ij.2 + x t ij.1 * uv.2 t ij.2)
  have entry (uv : (Fin r → Fin a → K) × (Fin r → Fin b → K)) (w : Fin r → Fin c → K)
      (i : Fin a) (j : Fin b) (k : Fin c) :
      (L uv k + ∑ t, w t k • g t) (i,j) = ∑ t,
        (uv.1 t i*(y t j*z t k) + x t i*(uv.2 t j*z t k) + x t i*(y t j*w t k)) := by
    simp only [L,g,Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  dsimp only
  rw [← quotient_range_iff g L]
  constructor
  · intro full F
    obtain ⟨u,v,w,hu⟩ := full (fun i j k => F k (i,j))
    refine ⟨(u,v),w,fun k => ?_⟩
    funext ⟨i,j⟩
    exact (hu i j k).trans (entry (u,v) w i j k).symm
  · intro full T
    obtain ⟨uv,w,hu⟩ := full (fun k ij => T ij.1 ij.2 k)
    exact ⟨uv.1,uv.2,w,fun i j k => (congrFun (hu k) (i,j)).trans (entry uv w i j k)⟩

end ConsecutiveQuotient

namespace ConsecutiveQuotient

/-- Distinct coordinate-grid points specialize an explicit minor to the
identity. The span of the canonical generic two-factor products therefore
removes exactly one matrix dimension for each product. -/
lemma generic_outer_independent (a b c r : ℕ) (hr : r≤a*b) :
    let V := Fin r × (Fin a ⊕ (Fin b ⊕ Fin c))
    let R := MvPolynomial V ℂ
    let K := FractionRing R
    let q : V → K := fun s => algebraMap R K (MvPolynomial.X s)
    let v : Fin r → Fin a × Fin b → K := fun t ij =>
      q (t,.inl ij.1) * q (t,.inr (.inl ij.2))
    LinearIndependent K v ∧
      Module.finrank K ((Fin a × Fin b → K) ⧸ Submodule.span K (Set.range v)) = a*b-r := by
  classical
  intro V R K q v
  let e : Fin r ↪ Fin a × Fin b := (Fin.castLEEmb hr).trans finProdFinEquiv.symm.toEmbedding
  let M : Matrix (Fin r) (Fin r) R := fun t s =>
    MvPolynomial.X (t,.inl (e s).1) * MvPolynomial.X (t,.inr (.inl (e s).2))
  let p : V → ℂ := fun s => s.2.elim (fun i => if i=(e s.1).1 then 1 else 0)
    (Sum.elim (fun j => if j=(e s.1).2 then 1 else 0) (fun _ => 0))
  have identity : M.map (MvPolynomial.eval p) = 1 := by
    ext t s
    rw [Matrix.map_apply]
    by_cases he : t=s
    · subst s
      simp [M,p]
    · have hd : (e s).1 ≠ (e t).1 ∨ (e s).2 ≠ (e t).2 := by
        by_contra! h
        exact he (e.injective (Prod.ext h.1 h.2)).symm
      rcases hd with hd | hd <;> simp [M,p,hd,he]
  have unit_det : MvPolynomial.eval p M.det = 1 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, identity, Matrix.det_one]
  have nonzero : M.det ≠ 0 := by
    intro hz
    rw [hz,map_zero] at unit_det
    exact zero_ne_one unit_det
  let φ := algebraMap R K
  have lifted : (M.map φ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact fun hz => nonzero (IsFractionRing.injective R K (hz.trans φ.map_zero.symm))
  let restrict : (Fin a × Fin b → K) →ₗ[K] (Fin r → K) :=
    LinearMap.pi (fun i => LinearMap.proj (R:=K) (e i))
  have hi : LinearIndependent K v := by
    apply LinearIndependent.of_comp restrict
    have hv : restrict ∘ v = fun t => (M.map φ) t := by
      funext t s
      change φ (MvPolynomial.X (t,.inl (e s).1)) * φ (MvPolynomial.X (t,.inr (.inl (e s).2))) =
        φ (MvPolynomial.X (t,.inl (e s).1) * MvPolynomial.X (t,.inr (.inl (e s).2)))
      exact (map_mul _ _ _).symm
    rw [hv]
    exact Matrix.linearIndependent_rows_of_det_ne_zero lifted
  refine ⟨hi,?_⟩
  have hdim := (Submodule.span K (Set.range v)).finrank_quotient_add_finrank
  rw [finrank_span_eq_card hi, Module.finrank_pi, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin, Fintype.card_fin] at hdim
  omega

end ConsecutiveQuotient

namespace ConsecutiveQuotient

set_option maxHeartbeats 1000000 in
/-- In the quotient by the fixed products, both first coordinates of each
variation may be set to zero when the corresponding fixed coordinates are
nonzero. The remaining inputs have exactly r*(a+b) entries. -/
theorem compress_gauges {K : Type*} [Field K] {a b c r : ℕ}
    (x : Fin r → Fin (a+1) → K) (y : Fin r → Fin (b+1) → K) (z : Fin r → Fin c → K)
    (hx : ∀ t, x t 0≠0) (hy : ∀ t, y t 0≠0) :
    let g (t : Fin r) (ij : Fin (a+1) × Fin (b+1)) := x t ij.1 * y t ij.2
    let W := Submodule.span K (Set.range g)
    let L (uv : (Fin r → Fin (a+1) → K) × (Fin r → Fin (b+1) → K)) (k : Fin c) :=
      W.mkQ (∑ t, z t k • fun ij : Fin (a+1) × Fin (b+1) =>
        uv.1 t ij.1 * y t ij.2 + x t ij.1 * uv.2 t ij.2)
    Function.Surjective L ↔ Function.Surjective
      (fun (uv : (Fin r → Fin a → K) × (Fin r → Fin b → K)) =>
        L (fun t => Fin.cases 0 (uv.1 t),fun t => Fin.cases 0 (uv.2 t))) := by
  classical
  intro g W L
  constructor
  · intro full target
    obtain ⟨⟨u,v⟩,covers⟩ := full target
    let u₀ (t : Fin r) := u t 0 / x t 0
    let v₀ (t : Fin r) := v t 0 / y t 0
    let u' (t : Fin r) (i : Fin (a+1)) := u t i-u₀ t*x t i
    let v' (t : Fin r) (j : Fin (b+1)) := v t j-v₀ t*y t j
    refine ⟨(fun t i => u' t i.succ, fun t j => v' t j.succ),?_⟩
    have eu (t : Fin r) : Fin.cases 0 (fun i => u' t i.succ) = u' t := by
      funext i
      refine Fin.cases ?_ (fun _ => rfl) i
      simp [u',u₀,hx t]
    have ev (t : Fin r) : Fin.cases 0 (fun j => v' t j.succ) = v' t := by
      funext j
      refine Fin.cases ?_ (fun _ => rfl) j
      simp [v',v₀,hy t]
    change L (fun t => Fin.cases 0 (fun i => u' t i.succ),
       fun t => Fin.cases 0 (fun j => v' t j.succ)) = target
    simp only [eu,ev]
    refine Eq.trans ?_ covers
    funext k
    apply (Submodule.Quotient.eq W).mpr
    rw [← Finset.sum_sub_distrib]
    apply Submodule.sum_mem
    intro t _
    have e : z t k • (fun ij : Fin (a+1) × Fin (b+1) =>
        u' t ij.1*y t ij.2+x t ij.1*v' t ij.2) -
        z t k • (fun ij : Fin (a+1) × Fin (b+1) =>
        u t ij.1*y t ij.2+x t ij.1*v t ij.2) =
        (-(z t k)*(u₀ t+v₀ t)) • g t := by
      funext ij
      simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul,g,u',v']
      ring
    rw [e]
    exact W.smul_mem _ (Submodule.subset_span ⟨t,rfl⟩)
  · intro small target
    obtain ⟨⟨u,v⟩,h⟩ := small target
    exact ⟨(fun t => Fin.cases 0 (u t),fun t => Fin.cases 0 (v t)),h⟩

end ConsecutiveQuotient

namespace ConsecutiveQuotient

open MvPolynomial

/-- One canonical rational-function test after eliminating the entire third
variation and the two redundant scalar directions at each point. -/
theorem generic_compressed_iff (a b c r : ℕ) :
    (∃ x : Fin r → Fin (a+1) → ℂ, ∃ y : Fin r → Fin (b+1) → ℂ, ∃ z : Fin r → Fin c → ℂ,
      ∀ T : Fin (a+1) → Fin (b+1) → Fin c → ℂ, ∃ u : Fin r → Fin (a+1) → ℂ,
        ∃ v : Fin r → Fin (b+1) → ℂ, ∃ w : Fin r → Fin c → ℂ, ∀ i j k, T i j k =
          ∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) ↔
    let V := Fin r × (Fin (a+1) ⊕ (Fin (b+1) ⊕ Fin c))
    let R := MvPolynomial V ℂ
    let K := FractionRing R
    let q : V → K := fun s => algebraMap R K (X s)
    let x (t : Fin r) (i : Fin (a+1)) := q (t,.inl i)
    let y (t : Fin r) (j : Fin (b+1)) := q (t,.inr (.inl j))
    let z (t : Fin r) (k : Fin c) := q (t,.inr (.inr k))
    let g (t : Fin r) (ij : Fin (a+1) × Fin (b+1)) := x t ij.1*y t ij.2
    let W := Submodule.span K (Set.range g)
    Function.Surjective (fun (uv : (Fin r → Fin a → K) × (Fin r → Fin b → K)) (k : Fin c) =>
      W.mkQ (∑ t, z t k • fun ij : Fin (a+1) × Fin (b+1) =>
        Fin.cases 0 (uv.1 t) ij.1 * y t ij.2 + x t ij.1 * Fin.cases 0 (uv.2 t) ij.2)) := by
  let V := Fin r × (Fin (a+1) ⊕ (Fin (b+1) ⊕ Fin c))
  let R := MvPolynomial V ℂ
  let K := FractionRing R
  let q (s : V) : K := algebraMap R K (X s)
  let x (t : Fin r) (i : Fin (a+1)) := q (t,.inl i)
  let y (t : Fin r) (j : Fin (b+1)) := q (t,.inr (.inl j))
  let z (t : Fin r) (k : Fin c) := q (t,.inr (.inr k))
  have nonzero (s : V) : q s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (X_ne_zero s)
  exact (CriticalJacobian.generic_tangent_iff (a+1) (b+1) c r).trans
    ((tangent_iff_compressed x y z).trans
      (compress_gauges x y z (fun _ => nonzero _) (fun _ => nonzero _)))

/-- The quotient output has c*(ab-r) coordinates when the r product
directions are independent. The dimension test is the original ceiling. -/
theorem compressed_dimensions (a b c r : ℕ) (hr : r≤(a+1)*(b+1)) :
    c*((a+1)*(b+1)-r) ≤ r*(a+b) ↔ (a+1)*(b+1)*c ≤ r*(a+b+c) := by
  have h : r+((a+1)*(b+1)-r)=(a+1)*(b+1) := by omega
  have e : c*((a+1)*(b+1)-r)+r*c=(a+1)*(b+1)*c := by
    calc
      _ = (r+((a+1)*(b+1)-r))*c := by ring
      _ = _ := by rw [h]
  rw [← e,Nat.mul_add r (a+b) c]
  omega

/-- Dimensions of the actual input and output spaces of the generic test. -/
theorem generic_space_dimensions (a b c r : ℕ) (hr : r≤(a+1)*(b+1)) :
    let V := Fin r × (Fin (a+1) ⊕ (Fin (b+1) ⊕ Fin c))
    let R := MvPolynomial V ℂ
    let K := FractionRing R
    let q : V → K := fun s => algebraMap R K (X s)
    let g (t : Fin r) (ij : Fin (a+1) × Fin (b+1)) := q (t,.inl ij.1)*q (t,.inr (.inl ij.2))
    let W := Submodule.span K (Set.range g)
    Module.finrank K ((Fin r → Fin a → K) × (Fin r → Fin b → K)) = r*(a+b) ∧
    Module.finrank K (Fin c → ((Fin (a+1) × Fin (b+1) → K) ⧸ W)) = c*((a+1)*(b+1)-r) := by
  intro V R K q g W
  have dim : Module.finrank K ((Fin (a+1) × Fin (b+1) → K) ⧸ W) = (a+1)*(b+1)-r :=
    (generic_outer_independent (a+1) (b+1) c r hr).2
  constructor
  · simp [Module.finrank_pi_fintype,Nat.mul_add]
  · rw [Module.finrank_pi_fintype]
    simp [dim]

end ConsecutiveQuotient

namespace CriticalTensor.ConsecutivePublic

open MvPolynomial

/-- A single surjective specialization gives a polynomial whose nonvanishing
guarantees surjectivity. Its determinant uses a fixed right inverse at that point. -/
private lemma rank_polynomial {I J V : Type} [Fintype I] [DecidableEq I] [Fintype J]
    (M : Matrix I J (MvPolynomial V ℂ)) (x₀ : V → ℂ)
    (h₀ : Function.Surjective (M.map (eval x₀)).mulVec) :
    ∃ Q : MvPolynomial V ℂ, Q ≠ 0 ∧ ∀ x : V → ℂ,
      eval x Q ≠ 0 → Function.Surjective (M.map (eval x)).mulVec := by
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp h₀
  let D := M * B.map (C : ℂ →+* MvPolynomial V ℂ)
  have specialize (x : V → ℂ) : eval x D.det = (M.map (eval x) * B).det := by
    have hconst : (B.map (C : ℂ →+* MvPolynomial V ℂ)).map (eval x) = B := by
      ext i j
      simp [Matrix.map_apply]
    rw [RingHom.map_det, RingHom.mapMatrix_apply, show D = _ from rfl, Matrix.map_mul, hconst]
  have hvalue : eval x₀ D.det = 1 := by rw [specialize, hB, Matrix.det_one]
  refine ⟨D.det, ?_, ?_⟩
  · intro he
    rw [he, map_zero] at hvalue
    exact zero_ne_one hvalue
  · intro x hx
    rw [specialize] at hx
    have hprod : Function.Surjective (M.map (eval x) * B).mulVec :=
      Matrix.mulVec_surjective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hx))
    intro y
    obtain ⟨z, hz⟩ := hprod y
    refine ⟨B.mulVec z, ?_⟩
    rw [Matrix.mulVec_mulVec]
    exact hz

/-- Independently spanning middle-coordinate fibers share a complex specialization.
Take the middle factor of point (g,t) to be the corresponding basis vector. -/
theorem spans_of_separate_fibers {a b c h : ℕ}
    (witness : ∀ g : Fin b, ∃ x : Fin b → Fin h → Fin a → ℂ, ∃ z : Fin b → Fin h → Fin c → ℂ,
      ∀ T : Fin a → Fin c → ℂ, ∃ u : Fin h → Fin a → ℂ, ∃ w : Fin h → Fin c → ℂ,
      ∃ v : Fin b → Fin h → ℂ, ∀ i k, T i k =
        (∑ t, (u t i*z g t k + x g t i*w t k)) + ∑ l,∑ t,v l t*(x l t i*z l t k)) :
    ∃ x : Fin (b*h) → Fin a → ℂ, ∃ y : Fin (b*h) → Fin b → ℂ, ∃ z : Fin (b*h) → Fin c → ℂ,
    ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin (b*h) → Fin a → ℂ,
      ∃ v : Fin (b*h) → Fin b → ℂ, ∃ w : Fin (b*h) → Fin c → ℂ, ∀ i j k, T i j k =
        ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
  classical
  let Fiber (x : Fin b → Fin h → Fin a → ℂ) (z : Fin b → Fin h → Fin c → ℂ) (g : Fin b) : Prop :=
    ∀ T : Fin a → Fin c → ℂ, ∃ u : Fin h → Fin a → ℂ, ∃ w : Fin h → Fin c → ℂ,
      ∃ v : Fin b → Fin h → ℂ, ∀ i k, T i k =
        (∑ t, (u t i*z g t k + x g t i*w t k)) + ∑ l,∑ t,v l t*(x l t i*z l t k)
  let Var := (Fin b × Fin h) × (Fin a ⊕ Fin c)
  let Col := (Fin h × (Fin a ⊕ Fin c)) ⊕ (Fin b × Fin h)
  let fstFactor {K : Type} (p : Var → K)
      (g : Fin b) (t : Fin h) (i : Fin a) := p ((g,t),.inl i)

  let thirdFactor {K : Type} (p : Var → K)
      (g : Fin b) (t : Fin h) (k : Fin c) := p ((g,t),.inr k)

  let matrix {K : Type} [CommSemiring K] (p : Var → K) (g : Fin b) :
      Matrix (Fin a × Fin c) (Col) K
    | (i,k),.inl (t,.inl j) => if j=i then thirdFactor p g t k else 0
    | (i,k),.inl (t,.inr j) => if j=k then fstFactor p g t i else 0
    | (i,k),.inr (l,t) => fstFactor p l t i * thirdFactor p l t k

  have action (p : Var → ℂ) (g : Fin b)
      (y : Col → ℂ) (i : Fin a) (k : Fin c) :
      (matrix p g).mulVec y (i,k) =
        (∑ t, (y (.inl (t,.inl i))*thirdFactor p g t k + fstFactor p g t i*y (.inl (t,.inr k)))) +
        ∑ l,∑ t,y (.inr (l,t))*(fstFactor p l t i*thirdFactor p l t k) := by
    change (∑ q : Col, matrix p g (i,k) q*y q)=_
    rw [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_prod_type]
    congr 1
    · apply Finset.sum_congr rfl
      intro t _
      rw [Fintype.sum_sum_type]
      simp [matrix,Finset.sum_ite_eq',mul_comm]
    · apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro t _
      exact mul_comm _ _

  have fiber_iff (p : Var → ℂ) (g : Fin b) :
      Fiber (fstFactor p) (thirdFactor p) g ↔ Function.Surjective (matrix p g).mulVec := by
    constructor
    · intro hl T
      obtain ⟨u,w,v,hv⟩ := hl fun i k => T (i,k)
      let y : Col → ℂ
        | .inl (t,.inl i) => u t i
        | .inl (t,.inr k) => w t k
        | .inr (l,t) => v l t
      refine ⟨y,?_⟩
      funext ⟨i,k⟩
      exact (action p g y i k).trans (hv i k).symm
    · intro hl T
      obtain ⟨y,hy⟩ := hl fun q => T q.1 q.2
      refine ⟨fun t i => y (.inl (t,.inl i)),fun t k => y (.inl (t,.inr k)),
        fun l t => y (.inr (l,t)),?_⟩
      intro i k
      exact (congrFun hy (i,k)).symm.trans (action p g y i k)

  have evaluate (p : Var → ℂ) (g : Fin b) :
      (matrix (MvPolynomial.X : Var → MvPolynomial (Var) ℂ) g).map (eval p)=matrix p g := by
    ext ⟨i,k⟩ col
    change eval p (matrix (MvPolynomial.X : Var → MvPolynomial Var ℂ) g (i,k) col) = matrix p g (i,k) col
    rcases col with ⟨t,j|j⟩|⟨l,t⟩
    · by_cases hj : j=i <;> simp [matrix,thirdFactor,hj]
    · by_cases hj : j=k <;> simp [matrix,fstFactor,hj]
    · simp [matrix,fstFactor,thirdFactor]
  have common : ∃ x : Fin b → Fin h → Fin a → ℂ, ∃ z : Fin b → Fin h → Fin c → ℂ, ∀ g, Fiber x z g := by
    let M (g : Fin b) := matrix (MvPolynomial.X : Var → MvPolynomial (Var) ℂ) g
    have h (g : Fin b) : ∃ p : Var → ℂ, Function.Surjective ((M g).map (eval p)).mulVec := by
      obtain ⟨x,z,hg⟩ := witness g
      let p (q : Var) := q.2.elim (x q.1.1 q.1.2) (z q.1.1 q.1.2)
      refine ⟨p,?_⟩
      dsimp only [M]
      rw [evaluate]
      exact (fiber_iff p g).mp hg
    choose u hu using h
    choose Q hQ good using fun g => rank_polynomial (M g) (u g) (hu g)
    have hn : (∏ g,Q g) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun g _ => hQ g
    have exists_pt : ∃ p : Var → ℂ, eval p (∏ g,Q g) ≠ 0 := by
      by_contra! off
      exact hn (MvPolynomial.funext fun p => by rw [off p,map_zero])
    obtain ⟨p,hp⟩ := exists_pt
    have hprod : (∏ g,eval p (Q g)) ≠ 0 := by simpa only [map_prod] using hp
    refine ⟨fstFactor p,thirdFactor p,?_⟩
    intro g
    apply (fiber_iff p g).mpr
    simpa only [M,evaluate] using good g p (Finset.prod_ne_zero_iff.mp hprod g (Finset.mem_univ g))
  obtain ⟨x,z,hf⟩ := common
  let E : Fin (b*h) ≃ Fin b × Fin h := finProdFinEquiv.symm
  let δ (l j : Fin b) : ℂ := if l=j then 1 else 0
  refine ⟨fun t => x (E t).1 (E t).2,fun t j => δ (E t).1 j,fun t => z (E t).1 (E t).2,?_⟩
  intro T
  choose U W V hh using fun j => hf j (fun i k => T i j k)
  refine ⟨fun t => U (E t).1 (E t).2, fun t j => V j (E t).1 (E t).2,
    fun t => W (E t).1 (E t).2,?_⟩
  intro i j k
  let F (p : Fin b × Fin h) := U p.1 p.2 i * (δ p.1 j*z p.1 p.2 k) +
    x p.1 p.2 i * (V j p.1 p.2*z p.1 p.2 k) + x p.1 p.2 i * (δ p.1 j*W p.1 p.2 k)
  have form (l : Fin b) (t : Fin h) : F (l,t) =
      (if l=j then U l t i*z l t k + x l t i*W l t k else 0) + V j l t*(x l t i*z l t k) := by
    by_cases hl : l=j <;> simp [F,δ,hl] <;> ring
  change T i j k = ∑ t : Fin (b*h), F (E t)
  rw [E.sum_comp F,Fintype.sum_prod_type,hh j i k]
  simp [form,Finset.sum_add_distrib,Finset.sum_ite_irrel]

end CriticalTensor.ConsecutivePublic

namespace CriticalTensor.ConsecutivePublic


/-- Assign the free scalar of a selected point, then sum its contribution at the selected coordinate. -/
private lemma distribute {P Q : Type} [Fintype P] [Fintype Q] [DecidableEq Q]
    (f : P → Q) (v : P → ℂ) (w : Q → ℂ) :
    (∑ j : Q, (∑ p : P, if f p=j then v p else 0)*w j) = ∑ p : P,v p*w (f p) := by
  simp_rw [Finset.sum_mul,ite_mul,zero_mul]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq]

/-- The `h` local points cover the first `h` rows and first `h` columns.
Each remaining coordinate pair is assigned one point outside the designated group. -/
private lemma fiber_witness {a b c h : ℕ} (ha : h≤a) (hc : h≤c)
    (room : (a-h)*(c-h) ≤ (b-1)*h) (g : Fin b) :
    ∃ x : Fin b → Fin h → Fin a → ℂ, ∃ z : Fin b → Fin h → Fin c → ℂ, ∀ T : Fin a → Fin c → ℂ, ∃ u : Fin h → Fin a → ℂ, ∃ w : Fin h → Fin c → ℂ,
      ∃ v : Fin b → Fin h → ℂ, ∀ i k, T i k =
        (∑ t, (u t i*z g t k + x g t i*w t k)) + ∑ l,∑ t,v l t*(x l t i*z l t k) := by
  classical
  let ea : Fin h ⊕ Fin (a-h) ≃ Fin a := Fintype.equivOfCardEq (by simp; omega)
  let ec : Fin h ⊕ Fin (c-h) ≃ Fin c := Fintype.equivOfCardEq (by simp; omega)
  let S := Fin (a-h) × Fin (c-h)
  let O := {l : Fin b // l≠g} × Fin h
  have hsize : Fintype.card S ≤ Fintype.card O := by
    simpa only [S,O,Fintype.card_prod,Fintype.card_subtype_compl,Fintype.card_subtype_eq,Fintype.card_fin] using room
  obtain ⟨alloc⟩ := Function.Embedding.nonempty_of_card_le hsize
  let pos (s : S) : Fin b × Fin h := ((alloc s).1.val,(alloc s).2)
  have hinj : Function.Injective pos := by
    intro i j hpos
    have h₁ : (pos i).1=(pos j).1 := congrArg Prod.fst hpos
    have h₂ : (pos i).2=(pos j).2 := congrArg Prod.snd hpos
    exact alloc.injective (Prod.ext (Subtype.ext h₁) h₂)
  have hout (s : S) : (pos s).1≠g := (alloc s).1.property
  let xx (s : S) (i : Fin a) : ℂ := if ea (.inr s.1)=i then 1 else 0
  let zz (s : S) (k : Fin c) : ℂ := if ec (.inr s.2)=k then 1 else 0
  let x (l : Fin b) (t : Fin h) (i : Fin a) : ℂ :=
    if l=g then (if ea (.inl t)=i then 1 else 0) else Function.extend pos xx 0 (l,t) i
  let z (l : Fin b) (t : Fin h) (k : Fin c) : ℂ :=
    if l=g then (if ec (.inl t)=k then 1 else 0) else Function.extend pos zz 0 (l,t) k
  have pickX (s : S) (i : Fin a) : x (pos s).1 (pos s).2 i = xx s i := by
    change (if (pos s).1=g then _ else Function.extend pos xx 0 (pos s) i) = _
    rw [if_neg (hout s),hinj.extend_apply]
  have pickZ (s : S) (k : Fin c) : z (pos s).1 (pos s).2 k = zz s k := by
    change (if (pos s).1=g then _ else Function.extend pos zz 0 (pos s) k) = _
    rw [if_neg (hout s),hinj.extend_apply]
  refine ⟨x,z,?_⟩
  intro T
  let U (t : Fin h) (i : Fin a) : ℂ := (ea.symm i).elim (fun _ => 0) (fun _ => T i (ec (.inl t)))
  let W (t : Fin h) (k : Fin c) := T (ea (.inl t)) k
  let val (s : S) := T (ea (.inr s.1)) (ec (.inr s.2))
  let V (l : Fin b) (t : Fin h) := ∑ s : S, if pos s=(l,t) then val s else 0
  refine ⟨U,W,V,?_⟩
  intro i k
  have hrest : (∑ l,∑ t,V l t*(x l t i*z l t k)) = ∑ s : S, val s*(xx s i*zz s k) := by
    let mulAt (p : Fin b × Fin h) := x p.1 p.2 i*z p.1 p.2 k
    have h := distribute pos val mulAt
    rw [Fintype.sum_prod_type] at h
    simpa only [V,mulAt,pickX,pickZ] using h
  rw [hrest]
  obtain ⟨j,rfl⟩ := ea.surjective i
  obtain ⟨l,rfl⟩ := ec.surjective k
  cases j <;> cases l <;>
    simp [S,U,W,val,xx,zz,x,z,Fintype.sum_prod_type,
      mul_ite,ite_mul,Finset.sum_ite_eq']

end CriticalTensor.ConsecutivePublic

namespace CriticalTensor.ConsecutivePublic

/-- Enlarging the point index set by zero triples preserves a spanning configuration. -/
private lemma pad_points {a b c r s : ℕ} (hr : r ≤ s) (h : ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin c → ℂ,
    ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ,
      ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin c → ℂ, ∀ i j k, T i j k =
        ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))) :
    ∃ x : Fin s → Fin a → ℂ, ∃ y : Fin s → Fin b → ℂ, ∃ z : Fin s → Fin c → ℂ,
    ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin s → Fin a → ℂ,
      ∃ v : Fin s → Fin b → ℂ, ∃ w : Fin s → Fin c → ℂ, ∀ i j k, T i j k =
        ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
  classical
  let e : Fin r ⊕ Fin (s-r) ≃ Fin s := Fintype.equivOfCardEq (by simp; omega)
  let pad {D : Type} (v : Fin r → D → ℂ) (t : Fin s) : D → ℂ := (e.symm t).elim v 0
  obtain ⟨x,y,z,ht⟩ := h
  refine ⟨pad x,pad y,pad z,?_⟩
  intro T
  obtain ⟨u,v,w,hu⟩ := ht T
  refine ⟨pad u,pad v,pad w,?_⟩
  intro i j k
  let f (t : Fin s) := pad u t i*(pad y t j*pad z t k) + pad x t i*(pad v t j*pad z t k) +
    pad x t i*(pad y t j*pad w t k)
  change T i j k=∑ t,f t
  rw [← e.sum_comp f,Fintype.sum_sum_type]
  simpa [f,pad] using hu i j k

/-- The complement can be filled whenever its coordinate cells fit in the other groups.
This includes zero-dimensional spaces and local groups larger than an axis. -/
lemma spans_of_pair_budget (a b c h : ℕ) (room : (a-h)*(c-h) ≤ (b-1)*h) :
    ∃ x : Fin (b*h) → Fin a → ℂ, ∃ y : Fin (b*h) → Fin b → ℂ, ∃ z : Fin (b*h) → Fin c → ℂ,
    ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin (b*h) → Fin a → ℂ,
      ∃ v : Fin (b*h) → Fin b → ℂ, ∃ w : Fin (b*h) → Fin c → ℂ, ∀ i j k, T i j k =
        ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
  let k := min h (min a c)
  have kh : k≤h := Nat.min_le_left _ _
  have ka : k≤a := (Nat.min_le_right h (min a c)).trans (Nat.min_le_left _ _)
  have kc : k≤c := (Nat.min_le_right h (min a c)).trans (Nat.min_le_right _ _)
  have hroom : (a-k)*(c-k) ≤ (b-1)*k := by
    by_cases ht : h ≤ min a c
    · simpa only [k,min_eq_left ht] using room
    · rw [show k=min a c from min_eq_right (by omega)]
      by_cases hac : a≤c
      · simp [min_eq_left hac]
      · simp [min_eq_right (le_of_not_ge hac)]
  exact pad_points (Nat.mul_le_mul_left b kh) (spans_of_separate_fibers (fiber_witness ka kc hroom))


/-- Four-by-b-by-(b+1) tensors admit a spanning tangent configuration at the
ceiling of the parameter count. For positive b this ceiling is 2b. -/
theorem four_consecutive (b : ℕ) :
    let r := 4*b*(b+1) ⌈/⌉ (4+b+(b+1)-2)
    ∃ x : Fin r → Fin 4 → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin (b+1) → ℂ,
      ∀ T : Fin 4 → Fin b → Fin (b+1) → ℂ, ∃ u : Fin r → Fin 4 → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin (b+1) → ℂ, ∀ i j k, T i j k =
          ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
  have count : 4*b*(b+1) ⌈/⌉ (4+b+(b+1)-2) = b*2 := by
    have hd : 4+b+(b+1)-2=2*b+3 := by omega
    rw [hd]
    have hp : 0<2*b+3 := by omega
    apply le_antisymm
    · apply (ceilDiv_le_iff_le_mul hp).mpr
      nlinarith
    · by_contra! hh
      have hle := (ceilDiv_le_iff_le_mul hp).mp (show 4*b*(b+1) ⌈/⌉ (2*b+3) ≤ 4*b*(b+1) ⌈/⌉ (2*b+3) from le_rfl)
      have hplus : (4*b*(b+1) ⌈/⌉ (2*b+3))+1 ≤ b*2 := by omega
      have hm := Nat.mul_le_mul_left (2*b+3) hplus
      nlinarith
  dsimp only
  rw [count]
  apply spans_of_pair_budget
  omega

end CriticalTensor.ConsecutivePublic

namespace CriticalTensor.ConsecutivePublic

/-- Two spanning configurations with common second and third axes can be
placed in complementary summands of the first axis. -/
theorem spans_first_direct_sum {a d b c r s : ℕ}
    (hA : ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin c → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))) (hD : ∃ x : Fin s → Fin d → ℂ, ∃ y : Fin s → Fin b → ℂ, ∃ z : Fin s → Fin c → ℂ,
      ∀ T : Fin d → Fin b → Fin c → ℂ, ∃ u : Fin s → Fin d → ℂ,
        ∃ v : Fin s → Fin b → ℂ, ∃ w : Fin s → Fin c → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))) :
    ∃ x : Fin (r+s) → Fin (a+d) → ℂ, ∃ y : Fin (r+s) → Fin b → ℂ, ∃ z : Fin (r+s) → Fin c → ℂ,
      ∀ T : Fin (a+d) → Fin b → Fin c → ℂ, ∃ u : Fin (r+s) → Fin (a+d) → ℂ,
        ∃ v : Fin (r+s) → Fin b → ℂ, ∃ w : Fin (r+s) → Fin c → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
  classical
  let axis : Fin a ⊕ Fin d ≃ Fin (a+d) := finSumFinEquiv
  let rank : Fin r ⊕ Fin s ≃ Fin (r+s) := finSumFinEquiv
  let pair {D : Type} (x : Fin r → D) (y : Fin s → D) (t : Fin (r+s)) :=
    (rank.symm t).elim x y
  let left (x : Fin a → ℂ) (i : Fin (a+d)) := (axis.symm i).elim x (fun _ => (0:ℂ))
  let right (x : Fin d → ℂ) (i : Fin (a+d)) := (axis.symm i).elim (fun _ => (0:ℂ)) x
  obtain ⟨x,y,z,h⟩ := hA
  obtain ⟨x',y',z',h'⟩ := hD
  refine ⟨pair (left ∘ x) (right ∘ x'), pair y y', pair z z', ?_⟩
  intro T
  obtain ⟨u,v,w,hu⟩ := h (fun i => T (axis (.inl i)))
  obtain ⟨u',v',w',hu'⟩ := h' (fun i => T (axis (.inr i)))
  refine ⟨pair (left ∘ u) (right ∘ u'), pair v v', pair w w', ?_⟩
  intro i j k
  obtain ⟨i,rfl⟩ := axis.surjective i
  rw [←rank.sum_comp, Fintype.sum_sum_type]
  cases i with
  | inl i => simpa [pair,left,right] using hu i j k
  | inr i => simpa [pair,left,right] using hu' i j k

private lemma dimension_count_le_half (a b : ℕ) (ha : 3≤a) :
    a*b*(b+1) ⌈/⌉ (a+b+(b+1)-2) ≤ a*b ⌈/⌉ 2 := by
  let D := a+b+(b+1)-2
  let q := a*b ⌈/⌉ 2
  have cover : a*b ≤ 2*q := (ceilDiv_le_iff_le_mul (by decide : 0<2)).mp le_rfl
  have den : 2*(b+1) ≤ D := by dsimp [D]; omega
  apply (ceilDiv_le_iff_le_mul (by dsimp [D]; omega : 0<D)).mpr
  calc
    a*b*(b+1) ≤ (2*q)*(b+1) := Nat.mul_le_mul_right _ cover
    _ = (2*(b+1))*q := by ring
    _ ≤ D*q := Nat.mul_le_mul_right _ den

/-- An even first dimension of at least four uses exactly half as many
points as the product of the first two dimensions. -/
lemma spans_even_half (h b : ℕ) (hh : 2≤h) :
    ∃ x : Fin (b*h) → Fin (2*h) → ℂ, ∃ y : Fin (b*h) → Fin b → ℂ, ∃ z : Fin (b*h) → Fin (b+1) → ℂ,
      ∀ T : Fin (2*h) → Fin b → Fin (b+1) → ℂ, ∃ u : Fin (b*h) → Fin (2*h) → ℂ,
        ∃ v : Fin (b*h) → Fin b → ℂ, ∃ w : Fin (b*h) → Fin (b+1) → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
  apply spans_of_pair_budget
  rw [show 2*h-h=h by omega, Nat.mul_comm h]
  exact Nat.mul_le_mul_right _ (by omega)

/-- The three- and five-slice cases, combined with complementary first-axis
summands and two-point coordinate groups, give the uniform half-product bound. -/
theorem uniform_half_bound
    (three : ∀ b : ℕ, 3≤b → ∃ x : Fin (3*b*(b+1) ⌈/⌉ (3+b+(b+1)-2)) → Fin 3 → ℂ, ∃ y : Fin (3*b*(b+1) ⌈/⌉ (3+b+(b+1)-2)) → Fin b → ℂ, ∃ z : Fin (3*b*(b+1) ⌈/⌉ (3+b+(b+1)-2)) → Fin (b+1) → ℂ,
      ∀ T : Fin 3 → Fin b → Fin (b+1) → ℂ, ∃ u : Fin (3*b*(b+1) ⌈/⌉ (3+b+(b+1)-2)) → Fin 3 → ℂ,
        ∃ v : Fin (3*b*(b+1) ⌈/⌉ (3+b+(b+1)-2)) → Fin b → ℂ, ∃ w : Fin (3*b*(b+1) ⌈/⌉ (3+b+(b+1)-2)) → Fin (b+1) → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)))
    (five : ∀ b : ℕ, 5≤b → ∃ x : Fin (5*b*(b+1) ⌈/⌉ (5+b+(b+1)-2)) → Fin 5 → ℂ, ∃ y : Fin (5*b*(b+1) ⌈/⌉ (5+b+(b+1)-2)) → Fin b → ℂ, ∃ z : Fin (5*b*(b+1) ⌈/⌉ (5+b+(b+1)-2)) → Fin (b+1) → ℂ,
      ∀ T : Fin 5 → Fin b → Fin (b+1) → ℂ, ∃ u : Fin (5*b*(b+1) ⌈/⌉ (5+b+(b+1)-2)) → Fin 5 → ℂ,
        ∃ v : Fin (5*b*(b+1) ⌈/⌉ (5+b+(b+1)-2)) → Fin b → ℂ, ∃ w : Fin (5*b*(b+1) ⌈/⌉ (5+b+(b+1)-2)) → Fin (b+1) → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)))
    (a b : ℕ) (ha : 3≤a) (hb : a≤b) :
    ∃ x : Fin (a*b ⌈/⌉ 2) → Fin a → ℂ, ∃ y : Fin (a*b ⌈/⌉ 2) → Fin b → ℂ, ∃ z : Fin (a*b ⌈/⌉ 2) → Fin (b+1) → ℂ,
      ∀ T : Fin a → Fin b → Fin (b+1) → ℂ, ∃ u : Fin (a*b ⌈/⌉ 2) → Fin a → ℂ,
        ∃ v : Fin (a*b ⌈/⌉ 2) → Fin b → ℂ, ∃ w : Fin (a*b ⌈/⌉ 2) → Fin (b+1) → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
  by_cases small₃ : a=3
  · subst a
    exact pad_points (dimension_count_le_half 3 b (by decide)) (three b hb)
  by_cases small₅ : a=5
  · subst a
    exact pad_points (dimension_count_le_half 5 b (by decide)) (five b hb)
  by_cases even : a%2=0
  · obtain ⟨h,rfl⟩ : ∃ h : ℕ, a=2*h := ⟨a/2,by omega⟩
    have count : (2*h)*b ⌈/⌉ 2 = b*h := by
      rw [show (2*h)*b = 2*(b*h) by ring, Nat.ceilDiv_eq_add_pred_div]
      omega
    rw [count]
    exact spans_even_half h b (by omega)
  obtain ⟨h,rfl⟩ : ∃ h : ℕ, a=3+2*h := ⟨(a-3)/2,by omega⟩
  have count : (3+2*h)*b ⌈/⌉ 2 = 3*b ⌈/⌉ 2 + b*h := by
    rw [show (3+2*h)*b=3*b+2*(b*h) by ring]
    simp only [Nat.ceilDiv_eq_add_pred_div]
    omega
  rw [count]
  apply spans_first_direct_sum
  · exact pad_points (dimension_count_le_half 3 b (by decide)) (three b (by omega))
  · exact spans_even_half h b (by omega)

/-- The half-product bound is at most the expected rank plus a constant
depending only on the first tensor dimension. -/
theorem half_bound_gap (a b : ℕ) (ha : 3≤a) :
    a*b ⌈/⌉ 2 ≤ a*b*(b+1) ⌈/⌉ (a+b+(b+1)-2) + (a*(a-3) ⌈/⌉ 4) := by
  let D := a+b+(b+1)-2
  let r := a*b*(b+1) ⌈/⌉ D
  let g := a*(a-3) ⌈/⌉ 4
  have Dpos : 0<D := by dsimp [D]; omega
  have floorR : a*b*(b+1) ≤ D*r := (ceilDiv_le_iff_le_mul Dpos).mp le_rfl
  have floorG : a*(a-3) ≤ 4*g := (ceilDiv_le_iff_le_mul (by decide : 0<4)).mp le_rfl
  have decomp : D*(a*b) = 2*(a*b*(b+1)) + b*(a*(a-3)) := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le ha
    have d : D = 2*b+k+2 := by dsimp [D]; omega
    rw [d,show 3+k-3=k by omega]
    ring
  apply (ceilDiv_le_iff_le_mul (by decide : 0<2)).mpr
  apply Nat.le_of_mul_le_mul_left (c:=D) _ Dpos
  calc
    D*(a*b) = _ := decomp
    _ ≤ 2*(D*r) + b*(4*g) := Nat.add_le_add (Nat.mul_le_mul_left _ floorR) (Nat.mul_le_mul_left _ floorG)
    _ ≤ D*(2*(r+g)) := by
      have larger : 4*b ≤ 2*D := by dsimp [D]; omega
      nlinarith only [Nat.mul_le_mul_right g larger]

end CriticalTensor.ConsecutivePublic

namespace CriticalTensor.ConsecutivePublic

/-- A five-slice block saves at least three in twice the parameter budget. -/
private lemma five_twice_le (b : ℕ) (hb : 8≤b) :
    2*(5*b*(b+1) ⌈/⌉ (5+b+(b+1)-2)) + 3 ≤ 5*b := by
  let q := (5*b-3)/2
  have lower : 5*b ≤ 2*q+4 := by dsimp [q]; omega
  have cover : 5*b*(b+1) ≤ (2*b+4)*q := by
    nlinarith only [Nat.mul_le_mul_left (b+2) lower, hb]
  have den : 5+b+(b+1)-2=2*b+4 := by omega
  rw [den]
  have upper := (ceilDiv_le_iff_le_mul (by omega : 0<2*b+4)).mpr cover
  dsimp [q] at upper
  omega

/-- Reusing five-slice configurations improves the half-product bound for
all first dimensions, with one exact finite tangent witness per format. -/
theorem uniform_block_bound
    (three : ∀ b : ℕ, 3≤b → ∃ x : Fin (3*b*(b+1) ⌈/⌉ (3+b+(b+1)-2)) → Fin 3 → ℂ, ∃ y : Fin (3*b*(b+1) ⌈/⌉ (3+b+(b+1)-2)) → Fin b → ℂ, ∃ z : Fin (3*b*(b+1) ⌈/⌉ (3+b+(b+1)-2)) → Fin (b+1) → ℂ,
      ∀ T : Fin 3 → Fin b → Fin (b+1) → ℂ, ∃ u : Fin (3*b*(b+1) ⌈/⌉ (3+b+(b+1)-2)) → Fin 3 → ℂ,
        ∃ v : Fin (3*b*(b+1) ⌈/⌉ (3+b+(b+1)-2)) → Fin b → ℂ, ∃ w : Fin (3*b*(b+1) ⌈/⌉ (3+b+(b+1)-2)) → Fin (b+1) → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)))
    (five : ∀ b : ℕ, 5≤b → ∃ x : Fin (5*b*(b+1) ⌈/⌉ (5+b+(b+1)-2)) → Fin 5 → ℂ, ∃ y : Fin (5*b*(b+1) ⌈/⌉ (5+b+(b+1)-2)) → Fin b → ℂ, ∃ z : Fin (5*b*(b+1) ⌈/⌉ (5+b+(b+1)-2)) → Fin (b+1) → ℂ,
      ∀ T : Fin 5 → Fin b → Fin (b+1) → ℂ, ∃ u : Fin (5*b*(b+1) ⌈/⌉ (5+b+(b+1)-2)) → Fin 5 → ℂ,
        ∃ v : Fin (5*b*(b+1) ⌈/⌉ (5+b+(b+1)-2)) → Fin b → ℂ, ∃ w : Fin (5*b*(b+1) ⌈/⌉ (5+b+(b+1)-2)) → Fin (b+1) → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)))
    (a b : ℕ) (ha : 3≤a) (hb : a≤b) :
    let k := (a-3)/5
    ∃ x : Fin (a*b ⌈/⌉ 2 - 3*k/2) → Fin a → ℂ, ∃ y : Fin (a*b ⌈/⌉ 2 - 3*k/2) → Fin b → ℂ, ∃ z : Fin (a*b ⌈/⌉ 2 - 3*k/2) → Fin (b+1) → ℂ,
      ∀ T : Fin a → Fin b → Fin (b+1) → ℂ, ∃ u : Fin (a*b ⌈/⌉ 2 - 3*k/2) → Fin a → ℂ,
        ∃ v : Fin (a*b ⌈/⌉ 2 - 3*k/2) → Fin b → ℂ, ∃ w : Fin (a*b ⌈/⌉ 2 - 3*k/2) → Fin (b+1) → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
  intro k
  by_cases small : b<8
  · have empty : k=0 := by dsimp [k]; omega
    apply pad_points _ (uniform_half_bound three five a b ha hb)
    omega
  let d := a-5*k
  have decomp : a=d+5*k := by dsimp [d,k]; omega
  have hd : 3≤d := by dsimp [d,k]; omega
  let q := d*b ⌈/⌉ 2
  let s := 5*b*(b+1) ⌈/⌉ (5+b+(b+1)-2)
  let P (f r : ℕ) : Prop := ∃ x : Fin r → Fin f → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin (b+1) → ℂ,
      ∀ T : Fin f → Fin b → Fin (b+1) → ℂ, ∃ u : Fin r → Fin f → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin (b+1) → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))
  have grow (t : ℕ) : P (d+5*t) (q+t*s) := by
    induction t with
    | zero =>
      simp only [Nat.mul_zero,Nat.zero_mul,Nat.add_zero]
      exact uniform_half_bound three five d b hd (by omega)
    | succ t ih =>
      have extra : P ((d+5*t)+5) ((q+t*s)+s) :=
        spans_first_direct_sum (a:=d+5*t) (d:=5) (r:=q+t*s) (s:=s) ih (five b (by omega))
      rw [show d+5*(t+1)=(d+5*t)+5 by omega, show q+(t+1)*s=(q+t*s)+s by ring]
      exact extra
  have h5 : 2*s+3 ≤ 5*b := five_twice_le b (by omega)
  have hdq : 2*q ≤ d*b+1 := by dsimp [q]; rw [Nat.ceilDiv_eq_add_pred_div]; omega
  have dim : a*b = d*b+5*k*b := by rw [decomp]; ring
  have total : 2*(q+k*s)+3*k ≤ a*b+1 := by
    nlinarith only [hdq,Nat.mul_le_mul_left k h5,dim]
  have room : q+k*s ≤ a*b ⌈/⌉ 2 - 3*k/2 := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    omega
  have hp := grow k
  rw [←decomp] at hp
  exact pad_points room hp

end CriticalTensor.ConsecutivePublic

namespace CriticalTensor.ConsecutivePublic

/-- The ceiling arithmetic for consecutive sides allows rounding the
quadratic error constant down for every first dimension. -/
theorem half_bound_gap_floor (a b : ℕ) (ha : 3≤a) :
    a*b ⌈/⌉ 2 ≤ a*b*(b+1) ⌈/⌉ (a+b+(b+1)-2) + a*(a-3)/4 := by
  let D := a+b+(b+1)-2
  let r := a*b*(b+1) ⌈/⌉ D
  let g := a*(a-3)/4
  have dpos : 0<D := by dsimp [D]; omega
  have cover : a*b*(b+1) ≤ D*r := (ceilDiv_le_iff_le_mul dpos).mp le_rfl
  have rem : (a*(a-3))%4≤2 := by
    rw [Nat.mul_mod]
    rcases (show a%4=0 ∨ a%4=1 ∨ a%4=2 ∨ a%4=3 by omega) with h|h|h|h
    · simp [h]
    · rw [h,show (a-3)%4=2 by omega]
    · rw [h,show (a-3)%4=3 by omega]
    · norm_num [h,show (a-3)%4=0 by omega]
  have gb : a*(a-3)≤4*g+2 := by dsimp only [g]; omega
  have decomp : D*(a*b) = 2*(a*b*(b+1)) + b*(a*(a-3)) := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le ha
    rw [show D=2*b+k+2 by dsimp [D]; omega,show 3+k-3=k by omega]
    ring
  apply (ceilDiv_le_iff_le_mul (by decide : 0<2)).mpr
  by_contra! bad
  have gap : 2*(r+g)+1≤a*b := bad
  have stric : (2*b)*(2*g+1)<D*(2*g+1) :=
    Nat.mul_lt_mul_of_pos_right (by dsimp [D]; omega) (by omega)
  nlinarith only [stric, decomp, cover, Nat.mul_le_mul_left D gap, Nat.mul_le_mul_left b gb]

end CriticalTensor.ConsecutivePublic

namespace OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H1_R1

open MvPolynomial

/-- The remaining low-dimensional cases after the unconditional four-slice construction. -/
def H1 : Prop :=
  ∀ a b : ℕ, (a=3 ∨ a=5) → a≤b → b+1 < (a-1)*(b-1) →
    let r := a*b*(b+1) ⌈/⌉ (a+b+(b+1)-2)
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin (b+1) → ℂ,
      ∀ T : Fin a → Fin b → Fin (b+1) → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin (b+1) → ℂ, ∀ i j k, T i j k =
          ∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))

section LargerFirstFactor

/-- For actual dimensions a+1,b+1,b+2, test only the two affine variations
at the generic point, with the common product span removed from every slice. -/
def H2 : Prop :=
  ∀ a b : ℕ, 5≤a → a≤b → b+2<a*b →
    let c := b+2
    let r := (a+1)*(b+1)*c ⌈/⌉ (a+b+c)
    let V := Fin r × (Fin (a+1) ⊕ (Fin (b+1) ⊕ Fin c))
    let R := MvPolynomial V ℂ
    let K := FractionRing R
    let q : V → K := fun s => algebraMap R K (X s)
    let x (t : Fin r) (i : Fin (a+1)) := q (t,.inl i)
    let y (t : Fin r) (j : Fin (b+1)) := q (t,.inr (.inl j))
    let z (t : Fin r) (k : Fin c) := q (t,.inr (.inr k))
    let g (t : Fin r) (ij : Fin (a+1) × Fin (b+1)) := x t ij.1*y t ij.2
    let W := Submodule.span K (Set.range g)
    Function.Surjective (fun (uv : (Fin r → Fin a → K) × (Fin r → Fin b → K)) (k : Fin c) =>
      W.mkQ (∑ t, z t k • fun ij : Fin (a+1) × Fin (b+1) =>
        Fin.cases 0 (uv.1 t) ij.1 * y t ij.2 + x t ij.1 * Fin.cases 0 (uv.2 t) ij.2))

end LargerFirstFactor

theorem main : H1 → H2 → OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1.H1 := by
  intro low large a b ha hab region
  by_cases small : a=3 ∨ a=5
  · exact low a b small hab region
  by_cases four : a=4
  · subst a
    exact CriticalTensor.ConsecutivePublic.four_consecutive b
  obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show a≠0 by omega)
  obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show b≠0 by omega)
  have den : a+1+(b+1)+(b+1+1)-2 = a+b+(b+2) := by omega
  dsimp only
  rw [den]
  exact (ConsecutiveQuotient.generic_compressed_iff a b (b+2) _).mpr
    (large a b (by omega) (by omega) (by simpa using region))

/-- The compressed tests retain both directions of the original tangent condition. -/
theorem iff_low_and_quotient :
    OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1.H1 ↔ H1 ∧ H2 := by
  refine ⟨fun parent => ⟨?_,?_⟩,fun h => main h.1 h.2⟩
  · intro a b small hab region
    exact parent a b (by omega) hab region
  · intro a b ha hab region
    apply (ConsecutiveQuotient.generic_compressed_iff a b (b+2) _).mp
    have item := parent (a+1) (b+1) (by omega) (by omega) (by simpa using region)
    dsimp only at item
    rw [show a+1+(b+1)+(b+1+1)-2 = a+b+(b+2) by omega] at item
    exact item

end OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H1_R1
