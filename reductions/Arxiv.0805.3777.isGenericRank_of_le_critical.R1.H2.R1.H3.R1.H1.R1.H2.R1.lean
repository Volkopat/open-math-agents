import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H1_R1

/-! # Consecutive tensor formats in affine coordinates

For six slices, the dimension count has two regimes. Four finite base cases
and one propagation law suffice for all longer sides.

In larger formats projectively normalize all first and second factors to
have first coordinate one. Change the third basis so the first c third
factors are the coordinate vectors. In each slice k, the anchored left and
right variations can then be removed by projecting to the matrix on the
remaining first- and second-factor coordinates. Every product becomes the
outer product of the differences from anchor k. Only r−c point variations
couple distinct slices. The ambient tangent test and the new one are proved
equivalent. For first dimensions a+1,b+1, exactly r−1 difference products
are independent in each generic a by b corner. This removes c(a+b) rows
and c(a+b) scalar inputs from the previous test without changing its slack.
Friedland's generic-rank conjecture is the motivating problem.
https://arxiv.org/abs/0805.3777
-/

namespace ConsecutiveAnchor

open MvPolynomial

/-- A surjective specialization persists after imposing a nonzero polynomial
condition on the same complex parameters. -/
theorem surjective_on_open {I J V : Type} [Fintype I] [Fintype J]
    (M : Matrix I J (MvPolynomial V ℂ)) (p₀ : V → ℂ)
    (onto : Function.Surjective (M.map (eval p₀)).mulVec)
    (F : MvPolynomial V ℂ) (hF : F ≠ 0) :
    ∃ p : V → ℂ, eval p F ≠ 0 ∧ Function.Surjective (M.map (eval p)).mulVec := by
  classical
  obtain ⟨B,right⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp onto
  let D := M * B.map (C : ℂ →+* MvPolynomial V ℂ)
  have determinant (p : V → ℂ) : eval p D.det = (M.map (eval p) * B).det := by
    have constant : (B.map (C : ℂ →+* MvPolynomial V ℂ)).map (eval p) = B := by
      ext i j
      simp [Matrix.map_apply]
    rw [RingHom.map_det, RingHom.mapMatrix_apply, show D = _ from rfl, Matrix.map_mul, constant]
  have nonzero : D.det ≠ 0 := by
    have value : eval p₀ D.det = 1 := by rw [determinant, right, Matrix.det_one]
    intro h
    exact zero_ne_one (by simpa only [h,map_zero] using value)
  obtain ⟨p,both⟩ : ∃ p : V → ℂ, eval p (D.det*F) ≠ 0 := by
    by_contra! vanish
    exact mul_ne_zero nonzero hF (MvPolynomial.funext fun p => by rw [vanish p,map_zero])
  rw [map_mul, determinant] at both
  obtain ⟨hdet,openAt⟩ := mul_ne_zero_iff.mp both
  refine ⟨p,openAt,?_⟩
  have surj : Function.Surjective (M.map (eval p)*B).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  intro T
  obtain ⟨u,hu⟩ := surj T
  exact ⟨B.mulVec u, (Matrix.mulVec_mulVec ..).trans hu⟩

/-- If the tangent spaces span somewhere, they span with any prescribed
nonzero polynomial in their factor coordinates also nonzero. -/
theorem tangent_on_open {a b c r : ℕ}
    (witness : ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin c → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)))
    (F : MvPolynomial (Fin r × (Fin a ⊕ (Fin b ⊕ Fin c))) ℂ) (hF : F ≠ 0) :
    ∃ p : (Fin r × (Fin a ⊕ (Fin b ⊕ Fin c))) → ℂ, eval p F ≠ 0 ∧
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin c → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(p (t,.inr (.inl j))*p (t,.inr (.inr k))) +
            p (t,.inl i)*(v t j*p (t,.inr (.inr k))) + p (t,.inl i)*(p (t,.inr (.inl j))*w t k)) := by
  classical
  let V := Fin r × (Fin a ⊕ (Fin b ⊕ Fin c))
  let M : Matrix ((Fin a × Fin b) × Fin c) V (MvPolynomial V ℂ) := fun row col =>
    col.2.elim (fun i => if i=row.1.1 then X (col.1,.inr (.inl row.1.2))*X (col.1,.inr (.inr row.2)) else 0)
      (Sum.elim (fun j => if j=row.1.2 then X (col.1,.inl row.1.1)*X (col.1,.inr (.inr row.2)) else 0)
        (fun k => if k=row.2 then X (col.1,.inl row.1.1)*X (col.1,.inr (.inl row.1.2)) else 0))
  obtain ⟨p₀,initial⟩ := (CriticalJacobian.restricted_tangent_iff (a:=a) (b:=b) (c:=c) (r:=r)
    id M (fun _ _ _ _ _ => rfl)).mp witness
  obtain ⟨p,openAt,onto⟩ := surjective_on_open M p₀ initial F hF
  refine ⟨p,openAt,?_⟩
  intro T
  obtain ⟨q,hq⟩ := onto (fun row => T row.1.1 row.1.2 row.2)
  refine ⟨fun t i => q (t,.inl i), fun t j => q (t,.inr (.inl j)), fun t k => q (t,.inr (.inr k)),?_⟩
  intro i j k
  refine (congrFun hq ((i,j),k)).symm.trans ?_
  change (∑ s : V, eval p (M ((i,j),k) s)*q s) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp [M,apply_ite,ite_mul,Finset.sum_ite_eq']
  ring

end ConsecutiveAnchor

namespace ConsecutiveAnchor

open MvPolynomial

/-- Any prescribed `c` distinct point labels can have independent third
factors while spanning and avoiding all first- and second-factor coordinate hyperplanes. -/
theorem spanning_with_basis {a b c r : ℕ} (first : Fin c ↪ Fin r)
    (witness : ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin c → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))) :
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin c → ℂ,
      (∀ t i, x t i ≠ 0) ∧ (∀ t j, y t j ≠ 0) ∧ (Matrix.of (fun k i => z (first i) k)).det ≠ 0 ∧
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin c → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k)) := by
  classical
  let V := Fin r × (Fin a ⊕ (Fin b ⊕ Fin c))
  let Z : Matrix (Fin c) (Fin c) (MvPolynomial V ℂ) := fun k i => X (first i,.inr (.inr k))
  let sample (q : V) : ℂ := q.2.elim (fun _ => 1) (Sum.elim (fun _ => 1) (fun k => if q.1=first k then 1 else 0))
  have ident : Z.map (eval sample) = 1 := by
    ext k i
    change eval sample (X (first i,.inr (.inr k))) = (1 : Matrix (Fin c) (Fin c) ℂ) k i
    rw [eval_X,Matrix.one_apply]
    change (if first i=first k then (1:ℂ) else 0) = if k=i then 1 else 0
    by_cases h : i=k
    · subst k; simp
    · rw [if_neg (fun eq => h (first.injective eq)),if_neg (Ne.symm h)]
  have independent : Z.det ≠ 0 := by
    intro vanish
    have evaluated := congrArg (eval sample) vanish
    rw [RingHom.map_det,RingHom.mapMatrix_apply,ident,Matrix.det_one,map_zero] at evaluated
    exact one_ne_zero evaluated
  let coordinates : MvPolynomial V ℂ := ∏ v : V, X v
  have coordinate_product : coordinates ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ => X_ne_zero v
  obtain ⟨p,hp,hit⟩ := tangent_on_open witness (Z.det*coordinates) (mul_ne_zero independent coordinate_product)
  simp only [map_mul,coordinates,map_prod,eval_X] at hp
  obtain ⟨det,nonzero⟩ := mul_ne_zero_iff.mp hp
  have every (v : V) : p v ≠ 0 := Finset.prod_ne_zero_iff.mp nonzero v (Finset.mem_univ v)
  refine ⟨fun t i => p (t,.inl i), fun t j => p (t,.inr (.inl j)), fun t k => p (t,.inr (.inr k)),
    fun t i => every (t,.inl i), fun t j => every (t,.inr (.inl j)), ?_, hit⟩
  rw [RingHom.map_det,RingHom.mapMatrix_apply] at det
  have eq : Z.map (eval p) = Matrix.of (fun k i => p (first i,.inr (.inr k))) := by
    ext k i
    exact eval_X _
  rwa [eq] at det

end ConsecutiveAnchor

namespace ConsecutiveAnchor

/-- A surjective linear change of coordinates in the third factor preserves
spanning. The third variations are transformed by the same map. -/
theorem change_third {K S : Type} [Field K] [Fintype S] {a b c : ℕ}
    (F : (Fin c → K) →ₗ[K] (Fin c → K)) (onto : Function.Surjective F)
    (x : S → Fin a → K) (y : S → Fin b → K) (z : S → Fin c → K)
    (span : ∀ T : Fin a → Fin b → Fin c → K, ∃ u : S → Fin a → K,
      ∃ v : S → Fin b → K, ∃ w : S → Fin c → K, ∀ i j k,
        T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))) :
    ∀ T : Fin a → Fin b → Fin c → K, ∃ u : S → Fin a → K,
      ∃ v : S → Fin b → K, ∃ w : S → Fin c → K, ∀ i j k,
        T i j k = ∑ t, (u t i*(y t j*F (z t) k) + x t i*(v t j*F (z t) k) + x t i*(y t j*w t k)) := by
  classical
  intro T
  choose Y lift using fun i j => onto (T i j)
  obtain ⟨u,v,w,hit⟩ := span Y
  refine ⟨u,v,fun t => F (w t),?_⟩
  intro i j k
  have split : Y i j = ∑ t, ((u t i*y t j + x t i*v t j) • z t + (x t i*y t j) • w t) := by
    funext l
    rw [hit i j l,Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro t _
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have eq := congrArg F split
  rw [lift i j] at eq
  simp only [map_sum,map_add,map_smul] at eq
  rw [congrFun eq k,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

/-- Reindex both the factors and the variations by the same point bijection. -/
theorem reindex {K S U : Type} [Field K] [Fintype S] [Fintype U] {a b c : ℕ}
    (e : S ≃ U) (x : U → Fin a → K) (y : U → Fin b → K) (z : U → Fin c → K)
    (span : ∀ T : Fin a → Fin b → Fin c → K, ∃ u : U → Fin a → K,
      ∃ v : U → Fin b → K, ∃ w : U → Fin c → K, ∀ i j k,
        T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))) :
    ∀ T : Fin a → Fin b → Fin c → K, ∃ u : S → Fin a → K,
      ∃ v : S → Fin b → K, ∃ w : S → Fin c → K, ∀ i j k,
        T i j k = ∑ t, (u t i*(y (e t) j*z (e t) k) + x (e t) i*(v t j*z (e t) k) +
          x (e t) i*(y (e t) j*w t k)) := by
  intro T
  obtain ⟨u,v,w,hit⟩ := span T
  refine ⟨fun t => u (e t),fun t => v (e t),fun t => w (e t),?_⟩
  intro i j k
  exact (hit i j k).trans (e.sum_comp (fun t => u t i*(y t j*z t k) +
    x t i*(v t j*z t k) + x t i*(y t j*w t k))).symm

end ConsecutiveAnchor

namespace ConsecutiveAnchor

/-- Choose a spanning witness whose first `c` third factors are the standard
basis, while keeping every coordinate of the other two factors nonzero. -/
theorem tangent_iff_anchored {a b c r : ℕ} (hc : c ≤ r) :
    let spans {S : Type} [Fintype S] (x : S → Fin a → ℂ) (y : S → Fin b → ℂ)
        (z : S → Fin c → ℂ) :=
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : S → Fin a → ℂ, ∃ v : S → Fin b → ℂ,
        ∃ w : S → Fin c → ℂ, ∀ i j k, T i j k =
          ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))
    let S := Fin c ⊕ Fin (r-c)
    (∃ x : Fin r → Fin a → ℂ, ∃ y z, spans x y z) ↔
      ∃ x : S → Fin a → ℂ, ∃ y : S → Fin b → ℂ, ∃ tail : Fin (r-c) → Fin c → ℂ,
        (∀ t i, x t i ≠ 0) ∧ (∀ t j, y t j ≠ 0) ∧ spans x y (Sum.elim (fun i => Pi.single i 1) tail) := by
  classical
  intro spans S
  let e : S ≃ Fin r := finSumFinEquiv.trans (finCongr (show c+(r-c)=r by omega))
  let first : Fin c ↪ Fin r := ⟨fun i => e (.inl i),e.injective.comp Sum.inl_injective⟩
  constructor
  · intro witness
    obtain ⟨x,y,z,hx,hy,regular,hit⟩ := spanning_with_basis first witness
    let B := Matrix.of (fun k i => z (first i) k)
    let F := (B⁻¹).mulVecLin
    have inverse (v : Fin c → ℂ) : F (B.mulVec v) = v := by
      change (B⁻¹).mulVec (B.mulVec v) = v
      rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr regular),Matrix.one_mulVec]
    have column (i : Fin c) : F (z (first i)) = Pi.single i 1 := by
      have eq : B.mulVec (Pi.single i 1) = z (first i) := by rw [Matrix.mulVec_single_one]; rfl
      rw [← eq]
      exact inverse _
    let tail (t : Fin (r-c)) := F (z (e (.inr t)))
    have anchored : (fun t : S => F (z (e t))) = Sum.elim (fun i => Pi.single i 1) tail := by
      funext t
      rcases t with i | t
      · exact column i
      · rfl
    refine ⟨fun t => x (e t),fun t => y (e t),tail,fun t => hx (e t),fun t => hy (e t),?_⟩
    rw [← anchored]
    exact reindex e x y (fun t => F (z t)) (change_third F (fun v => ⟨B.mulVec v,inverse v⟩) x y z hit)
  · rintro ⟨x,y,tail,_,_,hit⟩
    let z : S → Fin c → ℂ := Sum.elim (fun i => Pi.single i 1) tail
    exact ⟨fun t => x (e.symm t),fun t => y (e.symm t),fun t => z (e.symm t),reindex e.symm x y z hit⟩

end ConsecutiveAnchor

namespace ConsecutiveAnchor

/-- In the anchored chart both first coordinates of the remaining projective
factors may also be normalized to one, point by point. -/
theorem tangent_iff_anchored_affine (a b c d : ℕ) :
    let spans {S : Type} [Fintype S] (x : S → Fin (a+1) → ℂ) (y : S → Fin (b+1) → ℂ)
        (z : S → Fin c → ℂ) :=
      ∀ T : Fin (a+1) → Fin (b+1) → Fin c → ℂ, ∃ u : S → Fin (a+1) → ℂ, ∃ v : S → Fin (b+1) → ℂ,
        ∃ w : S → Fin c → ℂ, ∀ i j k, T i j k =
          ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))
    let P := Fin c ⊕ Fin d
    (∃ x : Fin (c+d) → Fin (a+1) → ℂ, ∃ y z, spans x y z) ↔
      ∃ x : P → Fin a → ℂ, ∃ y : P → Fin b → ℂ, ∃ tail : Fin d → Fin c → ℂ,
        spans (fun t => Fin.cases 1 (x t)) (fun t => Fin.cases 1 (y t)) (Sum.elim (fun i => Pi.single i 1) tail) := by
  classical
  intro spans P
  let e : P ≃ Fin (c+d) := finSumFinEquiv
  constructor
  · intro witness
    have chosen := (tangent_iff_anchored (a:=a+1) (b:=b+1) (c:=c) (r:=c+d) (by omega)).mp witness
    rw [Nat.add_sub_cancel_left] at chosen
    obtain ⟨x,y,tail,hx,hy,hit⟩ := chosen
    let X (t : P) (i : Fin (a+1)) := x t i / x t 0
    let Y (t : P) (j : Fin (b+1)) := y t j / y t 0
    have hx' : (fun t : P => Fin.cases 1 (fun i : Fin a => X t i.succ)) = X := by
      funext t i
      refine Fin.cases ?_ (fun _ => rfl) i
      simp [X,hx t 0]
    have hy' : (fun t : P => Fin.cases 1 (fun j : Fin b => Y t j.succ)) = Y := by
      funext t j
      refine Fin.cases ?_ (fun _ => rfl) j
      simp [Y,hy t 0]
    refine ⟨fun t i => X t i.succ,fun t j => Y t j.succ,tail,?_⟩
    rw [hx',hy']
    intro T
    obtain ⟨u,v,w,repr⟩ := hit T
    refine ⟨fun t i => y t 0*u t i,fun t j => x t 0*v t j,fun t k => (x t 0*y t 0)*w t k,?_⟩
    intro i j k
    rw [repr i j k]
    apply Finset.sum_congr rfl
    intro t _
    dsimp only [X,Y]
    field_simp [hx t 0,hy t 0]
  · rintro ⟨x,y,tail,hit⟩
    let X (t : P) : Fin (a+1) → ℂ := Fin.cases 1 (x t)
    let Y (t : P) : Fin (b+1) → ℂ := Fin.cases 1 (y t)
    let Z : P → Fin c → ℂ := Sum.elim (fun i => Pi.single i 1) tail
    exact ⟨fun t => X (e.symm t),fun t => Y (e.symm t),fun t => Z (e.symm t),reindex e.symm X Y Z hit⟩

end ConsecutiveAnchor

namespace ConsecutiveQuotient

/-- Slice-dependent local ranges and an independently variable common span can
both be eliminated before testing the remaining coupled map. -/
theorem anchored_range_iff {K E A I C U : Type*} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup A] [Module K A] [Fintype I]
    (g : I → E) (B : C → A →ₗ[K] E) (L : U → C → E) :
    (∀ F : C → E, ∃ u : U, ∃ v : C → A, ∃ w : I → C → K, ∀ k,
      F k = L u k + B k (v k) + ∑ t, w t k • g t) ↔
    Function.Surjective (fun (u : U) (k : C) =>
      (Submodule.span K (Set.range g) ⊔ (B k).range).mkQ (L u k)) := by
  classical
  let W := Submodule.span K (Set.range g)
  have fiber (k : C) (z : E) : z ∈ W ⊔ (B k).range ↔
      ∃ v : A, ∃ w : I → K, z = B k v + ∑ i, w i • g i := by
    constructor
    · intro h
      obtain ⟨z₁,h₁,z₂,⟨v,rfl⟩,hz⟩ := Submodule.mem_sup.mp h
      obtain ⟨w,hw⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp h₁
      exact ⟨v,w,by rw [hw,←hz,add_comm]⟩
    · rintro ⟨v,w,rfl⟩
      exact Submodule.mem_sup.mpr ⟨_,(Submodule.mem_span_range_iff_exists_fun K).mpr ⟨w,rfl⟩,
        _,⟨v,rfl⟩,add_comm _ _⟩
  have lift (F H : C → E) :
      (∃ v : C → A, ∃ w : I → C → K, ∀ k, F k = H k + B k (v k) + ∑ i, w i k • g i) ↔
      ∀ k, (W ⊔ (B k).range).mkQ (F k) = (W ⊔ (B k).range).mkQ (H k) := by
    constructor
    · rintro ⟨v,w,hw⟩ k
      apply (Submodule.Quotient.eq _).mpr
      apply (fiber k _).mpr
      exact ⟨v k, fun i => w i k, by rw [hw k]; abel⟩
    · intro h
      choose v w hv using fun k => (fiber k _).mp ((Submodule.Quotient.eq _).mp (h k))
      exact ⟨v,fun i k => w k i,fun k => by rw [(sub_eq_iff_eq_add).mp (hv k)]; abel⟩
  constructor
  · intro total q
    choose F hF using fun k => (W ⊔ (B k).range).mkQ_surjective (q k)
    obtain ⟨u,hu⟩ := total F
    exact ⟨u,funext fun k => ((lift F (L u)).mp hu k).symm.trans (hF k)⟩
  · intro reduced F
    obtain ⟨u,hu⟩ := reduced (fun k => (W ⊔ (B k).range).mkQ (F k))
    exact ⟨u,(lift F (L u)).mpr (fun k => (congrFun hu k).symm)⟩

/-- Anchor c third factors at the coordinate vectors. All third-factor
variations fill W in each slice, and the first/second variations of the
anchored point k fill D k in slice k. Only the d other points couple slices. -/
theorem anchored_tangent_iff {K : Type*} [Field K] {a b c d : ℕ}
    (x : Fin c ⊕ Fin d → Fin a → K) (y : Fin c ⊕ Fin d → Fin b → K)
    (z : Fin d → Fin c → K) :
    let Z : Fin c ⊕ Fin d → Fin c → K := Sum.elim (fun l k => if l=k then 1 else 0) z
    let g (t : Fin c ⊕ Fin d) (ij : Fin a × Fin b) := x t ij.1 * y t ij.2
    let B (t : Fin c ⊕ Fin d) (uv : (Fin a → K) × (Fin b → K)) (ij : Fin a × Fin b) :=
      uv.1 ij.1 * y t ij.2 + x t ij.1 * uv.2 ij.2
    let W := Submodule.span K (Set.range g)
    let D (k : Fin c) := Submodule.span K (Set.range (B (.inl k)))
    (∀ T : Fin a → Fin b → Fin c → K,
      ∃ u : Fin c ⊕ Fin d → Fin a → K, ∃ v : Fin c ⊕ Fin d → Fin b → K,
      ∃ w : Fin c ⊕ Fin d → Fin c → K, ∀ i j k,
        T i j k = ∑ t, (u t i*(y t j*Z t k) + x t i*(v t j*Z t k) + x t i*(y t j*w t k))) ↔
    Function.Surjective (fun (uv : (Fin d → Fin a → K) × (Fin d → Fin b → K)) (k : Fin c) =>
      (W ⊔ D k).mkQ (∑ t : Fin d, z t k • B (.inr t) (uv.1 t,uv.2 t))) := by
  classical
  intro Z g B W D
  let localMap (k : Fin c) : ((Fin a → K) × (Fin b → K)) →ₗ[K] (Fin a × Fin b → K) := {
    toFun := B (.inl k)
    map_add' := by
      intro p q; funext ⟨i,j⟩
      change (p.1 i+q.1 i)*y (.inl k) j+x (.inl k) i*(p.2 j+q.2 j) =
        (p.1 i*y (.inl k) j+x (.inl k) i*p.2 j)+(q.1 i*y (.inl k) j+x (.inl k) i*q.2 j)
      ring
    map_smul' := by
      intro s p; funext ⟨i,j⟩
      change (s*p.1 i)*y (.inl k) j+x (.inl k) i*(s*p.2 j) =
        s*(p.1 i*y (.inl k) j+x (.inl k) i*p.2 j)
      ring }
  have local_eq (k : Fin c) : D k = (localMap k).range := Submodule.span_eq (localMap k).range
  let L (uv : (Fin d → Fin a → K) × (Fin d → Fin b → K)) (k : Fin c) :=
    ∑ t : Fin d, z t k • B (.inr t) (uv.1 t,uv.2 t)
  change _ ↔ Function.Surjective (fun uv k => (W ⊔ D k).mkQ (L uv k))
  have space : D=fun k => (localMap k).range := funext local_eq
  rw [space, ← anchored_range_iff g localMap L]
  have entry (u : Fin c ⊕ Fin d → Fin a → K) (v : Fin c ⊕ Fin d → Fin b → K)
      (w : Fin c ⊕ Fin d → Fin c → K) (i : Fin a) (j : Fin b) (k : Fin c) :
      (L (fun t => u (.inr t),fun t => v (.inr t)) k +
        localMap k (u (.inl k),v (.inl k)) + ∑ t, w t k • g t) (i,j) =
        ∑ t, (u t i*(y t j*Z t k) + x t i*(v t j*Z t k) + x t i*(y t j*w t k)) := by
    calc
      _ = (∑ t, Z t k * B t (u t,v t) (i,j)) + ∑ t, w t k * g t (i,j) := by
        simp only [L,localMap,LinearMap.coe_mk,AddHom.coe_mk,Pi.add_apply,Finset.sum_apply,
          Pi.smul_apply,smul_eq_mul,Fintype.sum_sum_type,Z,Sum.elim_inl,Sum.elim_inr,
          ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
        abel
      _ = _ := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro t _
        dsimp only [B,g]
        ring
  constructor
  · intro full target
    obtain ⟨u,v,w,h⟩ := full (fun i j k => target k (i,j))
    refine ⟨(fun t => u (.inr t),fun t => v (.inr t)),fun k => (u (.inl k),v (.inl k)),w,?_⟩
    intro k; funext ⟨i,j⟩
    exact (h i j k).trans (entry u v w i j k).symm
  · intro full target
    obtain ⟨uv,s,w,h⟩ := full (fun k ij => target ij.1 ij.2 k)
    let u := Sum.elim (fun k => (s k).1) uv.1
    let v := Sum.elim (fun k => (s k).2) uv.2
    refine ⟨u,v,w,fun i j k => ?_⟩
    exact (congrFun (h k) (i,j)).trans (entry u v w i j k)

end ConsecutiveQuotient

namespace ConsecutiveQuotient

set_option maxHeartbeats 1000000 in
/-- Quotienting by variable subspaces that contain the point products permits both coordinate gauges. -/
theorem compress_slice_gauges {K : Type*} [Field K] {a b c r : ℕ}
    (x : Fin r → Fin (a+1) → K) (y : Fin r → Fin (b+1) → K) (z : Fin r → Fin c → K)
    (N : Fin c → Submodule K (Fin (a+1) × Fin (b+1) → K))
    (included : ∀ k t, (fun ij : Fin (a+1) × Fin (b+1) => x t ij.1*y t ij.2) ∈ N k)
    (hx : ∀ t, x t 0≠0) (hy : ∀ t, y t 0≠0) :
    let L (uv : (Fin r → Fin (a+1) → K) × (Fin r → Fin (b+1) → K)) (k : Fin c) :=
      (N k).mkQ (∑ t, z t k • fun ij : Fin (a+1) × Fin (b+1) =>
        uv.1 t ij.1 * y t ij.2 + x t ij.1 * uv.2 t ij.2)
    Function.Surjective L ↔ Function.Surjective
      (fun (uv : (Fin r → Fin a → K) × (Fin r → Fin b → K)) =>
        L (fun t => Fin.cases 0 (uv.1 t),fun t => Fin.cases 0 (uv.2 t))) := by
  classical
  intro L
  let g (t : Fin r) (ij : Fin (a+1) × Fin (b+1)) := x t ij.1 * y t ij.2
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
    apply (Submodule.Quotient.eq (N k)).mpr
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
    exact (N k).smul_mem _ (included k t)
  · intro small target
    obtain ⟨⟨u,v⟩,h⟩ := small target
    exact ⟨(fun t => Fin.cases 0 (u t),fun t => Fin.cases 0 (v t)),h⟩

/-- In the normalized coordinate chart the anchored test needs only d(a+b)
scalar variations, with both coordinates set to zero at the first basis position. -/
theorem anchored_tangent_iff_gauged {K : Type*} [Field K] {a b c d : ℕ}
    (x : Fin c ⊕ Fin d → Fin (a+1) → K) (y : Fin c ⊕ Fin d → Fin (b+1) → K)
    (z : Fin d → Fin c → K)
    (hx : ∀ t : Fin d, x (.inr t) 0 ≠ 0) (hy : ∀ t : Fin d, y (.inr t) 0 ≠ 0) :
    let Z : Fin c ⊕ Fin d → Fin c → K := Sum.elim (fun l k => if l=k then 1 else 0) z
    let g (t : Fin c ⊕ Fin d) (ij : Fin (a+1) × Fin (b+1)) := x t ij.1 * y t ij.2
    let B (t : Fin c ⊕ Fin d) (uv : (Fin (a+1) → K) × (Fin (b+1) → K)) (ij : Fin (a+1) × Fin (b+1)) :=
      uv.1 ij.1 * y t ij.2 + x t ij.1 * uv.2 ij.2
    let W := Submodule.span K (Set.range g)
    let D (k : Fin c) := Submodule.span K (Set.range (B (.inl k)))
    (∀ T : Fin (a+1) → Fin (b+1) → Fin c → K,
      ∃ u : Fin c ⊕ Fin d → Fin (a+1) → K, ∃ v : Fin c ⊕ Fin d → Fin (b+1) → K,
      ∃ w : Fin c ⊕ Fin d → Fin c → K, ∀ i j k,
        T i j k = ∑ t, (u t i*(y t j*Z t k) + x t i*(v t j*Z t k) + x t i*(y t j*w t k))) ↔
    Function.Surjective (fun (uv : (Fin d → Fin a → K) × (Fin d → Fin b → K)) (k : Fin c) =>
      (W ⊔ D k).mkQ (∑ t : Fin d, z t k • B (.inr t) (Fin.cases 0 (uv.1 t), Fin.cases 0 (uv.2 t)))) := by
  intro Z g B W D
  let N (k : Fin c) := W ⊔ D k
  have hin (k : Fin c) (t : Fin d) : g (.inr t) ∈ N k :=
    (le_sup_left : W ≤ N k) (Submodule.subset_span (Set.mem_range_self (f:=g) (Sum.inr t)))
  exact (anchored_tangent_iff x y z).trans (compress_slice_gauges (fun t => x (.inr t))
    (fun t => y (.inr t)) z N hin hx hy)

end ConsecutiveQuotient

namespace ConsecutiveChart

/-- Delete the row and column of an anchored point after subtracting their
affine multiples. This map kills exactly the two anchored variation spaces. -/
theorem corner {K : Type*} [Field K] {a b : ℕ} (x : Fin a → K) (y : Fin b → K) :
    let X : Fin (a+1) → K := Fin.cases 1 x
    let Y : Fin (b+1) → K := Fin.cases 1 y
    ∃ p : (Fin (a+1) × Fin (b+1) → K) →ₗ[K] (Fin a × Fin b → K),
      (∀ M i j, p M (i,j) = M (i.succ,j.succ) - x i*M (0,j.succ) -
        y j*M (i.succ,0) + x i*y j*M (0,0)) ∧
      Function.Surjective p ∧
      (∀ (u : Fin (a+1) → K) (v : Fin (b+1) → K) i j,
        p (fun ij => u ij.1*v ij.2) (i,j) =
          (u i.succ-x i*u 0)*(v j.succ-y j*v 0)) ∧
      LinearMap.ker p = Submodule.span K (Set.range
        (fun uv : (Fin (a+1) → K) × (Fin (b+1) → K) =>
          fun ij : Fin (a+1) × Fin (b+1) => uv.1 ij.1 * Y ij.2 + X ij.1 * uv.2 ij.2)) := by
  intro X Y
  let p : (Fin (a+1) × Fin (b+1) → K) →ₗ[K] (Fin a × Fin b → K) :=
    { toFun := fun M ij => M (ij.1.succ,ij.2.succ)-x ij.1*M (0,ij.2.succ)-
        y ij.2*M (ij.1.succ,0)+x ij.1*y ij.2*M (0,0)
      map_add' := by intro M N; funext ij; simp only [Pi.add_apply]; ring
      map_smul' := by intro k M; funext ij; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  refine ⟨p,fun _ _ _ => rfl,?_,?_,le_antisymm ?_ ?_⟩
  · intro F
    let M (ij : Fin (a+1) × Fin (b+1)) : K :=
      Fin.cases 0 (fun i => Fin.cases 0 (fun j => F (i,j)) ij.2) ij.1
    refine ⟨M,?_⟩
    funext ij
    simp [p,M]
  · intro u v i j
    change u i.succ*v j.succ - x i*(u 0*v j.succ) - y j*(u i.succ*v 0) +
      x i*y j*(u 0*v 0) = _
    ring
  · intro M hM
    have van : p M = 0 := hM
    let u (i : Fin (a+1)) := M (i,0)
    let v (j : Fin (b+1)) := M (0,j) - M (0,0)*Y j
    apply Submodule.subset_span
    refine ⟨(u,v),?_⟩
    funext ⟨i,j⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [u,v,X,Y]
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [u,v,X,Y]
      · have h := congrFun van (i,j)
        change M (i.succ,j.succ)-x i*M (0,j.succ)-y j*M (i.succ,0)+x i*y j*M (0,0)=0 at h
        change M (i.succ,0)*y j + x i*(M (0,j.succ)-M (0,0)*y j) = M (i.succ,j.succ)
        linear_combination -h
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨u,v⟩,rfl⟩
    apply LinearMap.mem_ker.mpr
    funext ⟨i,j⟩
    change (u i.succ*y j+x i*v j.succ) - x i*(u 0*y j+1*v j.succ) -
      y j*(u i.succ*1+x i*v 0) + x i*y j*(u 0*1+1*v 0) = 0
    ring

/-- A representative for every quotient value can be chosen separately
on each slice. This describes surjectivity by membership in the fiber. -/
theorem onto_quotient_iff {K E C U : Type*} [Field K] [AddCommGroup E] [Module K E]
    (S : C → Submodule K E) (L : U → C → E) :
    Function.Surjective (fun (u : U) (k : C) => (S k).mkQ (L u k)) ↔
      ∀ F : C → E, ∃ u, ∀ k, F k - L u k ∈ S k := by
  classical
  constructor
  · intro onto F
    obtain ⟨u,h⟩ := onto (fun k => (S k).mkQ (F k))
    exact ⟨u,fun k => (Submodule.Quotient.eq (S k)).mp (congrFun h k).symm⟩
  · intro fill f
    choose F hF using fun k => (S k).mkQ_surjective (f k)
    obtain ⟨u,hu⟩ := fill F
    exact ⟨u,funext fun k => ((Submodule.Quotient.eq (S k)).mpr (hu k)).symm.trans (hF k)⟩

/-- Projecting each output slice through its own surjection preserves
the quotient test when the inverse images of the denominator spaces match. -/
theorem quotient_projection {K E V C U : Type*} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup V] [Module K V] (p : C → E →ₗ[K] V) (surj : ∀ k, Function.Surjective (p k))
    (S : C → Submodule K E) (W : C → Submodule K V)
    (coincide : ∀ k, (W k).comap (p k) = S k) (L : U → C → E) :
    Function.Surjective (fun (u : U) (k : C) => (S k).mkQ (L u k)) ↔
    Function.Surjective (fun (u : U) (k : C) => (W k).mkQ (p k (L u k))) := by
  rw [onto_quotient_iff S L, onto_quotient_iff W (fun u k => p k (L u k))]
  constructor
  · intro fill f
    choose F hF using fun k => surj k (f k)
    obtain ⟨u,hu⟩ := fill F
    refine ⟨u,fun k => ?_⟩
    rw [← hF k, ← map_sub]
    change F k - L u k ∈ (W k).comap (p k)
    rw [coincide]
    exact hu k
  · intro fill F
    obtain ⟨u,hu⟩ := fill (fun k => p k (F k))
    refine ⟨u,fun k => ?_⟩
    rw [← coincide]
    change p k (F k - L u k) ∈ W k
    rw [map_sub]
    exact hu k

end ConsecutiveChart

namespace ConsecutiveChart

/-- Project each anchored slice to its bottom-right corner. For normalized
vectors the projected products contain only differences from that anchor. -/
theorem affine_difference_iff {K : Type*} [Field K] {a b c d : ℕ}
    (x : Fin c ⊕ Fin d → Fin a → K) (y : Fin c ⊕ Fin d → Fin b → K)
    (z : Fin d → Fin c → K) :
    let X (t : Fin c ⊕ Fin d) : Fin (a+1) → K := Fin.cases 1 (x t)
    let Y (t : Fin c ⊕ Fin d) : Fin (b+1) → K := Fin.cases 1 (y t)
    let g (t : Fin c ⊕ Fin d) (ij : Fin (a+1) × Fin (b+1)) := X t ij.1 * Y t ij.2
    let B (t : Fin c ⊕ Fin d) (uv : (Fin (a+1) → K) × (Fin (b+1) → K))
        (ij : Fin (a+1) × Fin (b+1)) := uv.1 ij.1*Y t ij.2+X t ij.1*uv.2 ij.2
    let W := Submodule.span K (Set.range g)
    let D (k : Fin c) := Submodule.span K (Set.range (B (.inl k)))
    let dx (k : Fin c) (t : Fin c ⊕ Fin d) (i : Fin a) := x t i - x (.inl k) i
    let dy (k : Fin c) (t : Fin c ⊕ Fin d) (j : Fin b) := y t j - y (.inl k) j
    let V (k : Fin c) := Submodule.span K (Set.range (fun (t : Fin c ⊕ Fin d) (ij : Fin a × Fin b) =>
      dx k t ij.1 * dy k t ij.2))
    Function.Surjective (fun (uv : (Fin d → Fin a → K) × (Fin d → Fin b → K)) (k : Fin c) =>
      (W ⊔ D k).mkQ (∑ t, z t k • B (.inr t) (Fin.cases 0 (uv.1 t),Fin.cases 0 (uv.2 t)))) ↔
    Function.Surjective (fun (uv : (Fin d → Fin a → K) × (Fin d → Fin b → K)) (k : Fin c) =>
      (V k).mkQ (∑ t, z t k • fun ij : Fin a × Fin b =>
        uv.1 t ij.1 * dy k (.inr t) ij.2 + dx k (.inr t) ij.1 * uv.2 t ij.2)) := by
  classical
  intro X Y g B W D dx dy V
  choose p entry surj outer ker using fun k : Fin c => corner (x (.inl k)) (y (.inl k))
  have image (k : Fin c) : W.map (p k) = V k := by
    rw [show W = Submodule.span K (Set.range g) from rfl, Submodule.map_span, ← Set.range_comp]
    apply congrArg (Submodule.span K)
    apply congrArg Set.range
    funext t ij
    rw [Function.comp_apply]
    exact (outer k (X t) (Y t) ij.1 ij.2).trans (by simp [X,Y,dx,dy])
  have denominator (k : Fin c) : (V k).comap (p k) = W ⊔ D k := by
    rw [← image, Submodule.comap_map_eq, ker k]
  let L (uv : (Fin d → Fin a → K) × (Fin d → Fin b → K)) (k : Fin c) :=
    ∑ t, z t k • B (.inr t) (Fin.cases 0 (uv.1 t),Fin.cases 0 (uv.2 t))
  have local_image (t : Fin d) (k : Fin c) (u : Fin a → K) (v : Fin b → K) :
      p k (B (.inr t) (Fin.cases 0 u,Fin.cases 0 v)) =
        fun ij : Fin a × Fin b => u ij.1*dy k (.inr t) ij.2+dx k (.inr t) ij.1*v ij.2 := by
    funext ⟨i,j⟩
    rw [entry k]
    dsimp [B,X,Y,dx,dy]
    ring
  have action (uv : (Fin d → Fin a → K) × (Fin d → Fin b → K)) (k : Fin c) :
      p k (L uv k) = ∑ t, z t k • fun ij : Fin a × Fin b =>
        uv.1 t ij.1 * dy k (.inr t) ij.2 + dx k (.inr t) ij.1 * uv.2 t ij.2 := by
    simp only [L, map_sum, map_smul, local_image]
  simpa only [action] using quotient_projection p surj (fun k => W ⊔ D k) V denominator L

end ConsecutiveChart

namespace ConsecutiveChart

/-- At generic affine coordinates exactly r−1 difference products survive
in each anchor quotient. Distinct interior coordinate entries give a minor
whose specialization is the identity, simultaneously over the common field. -/
theorem generic_difference_dimension (a b c d : ℕ) (k : Fin c) (room : c+d ≤ a*b+1) :
    let P := Fin c ⊕ Fin d
    let V := P × (Fin a ⊕ Fin b)
    let R := MvPolynomial V ℂ
    let K := FractionRing R
    let q : V → K := fun i => algebraMap R K (MvPolynomial.X i)
    let g (t : P) (ij : Fin a × Fin b) :=
      (q (t,.inl ij.1)-q (.inl k,.inl ij.1))*(q (t,.inr ij.2)-q (.inl k,.inr ij.2))
    let W := Submodule.span K (Set.range g)
    Module.finrank K ((Fin a × Fin b → K) ⧸ W) = a*b+1-(c+d) := by
  classical
  intro P V R K q g W
  let anchor : P := Sum.inl k
  let J := {t : P // t ≠ anchor}
  have size : Fintype.card J=c+d-1 := by
    change Fintype.card {t : P // t≠anchor} = _
    rw [Fintype.card_subtype_compl,Fintype.card_subtype_eq]
    simp [P]
  have enough : Fintype.card J ≤ a*b := by omega
  let cells : J ↪ Fin a × Fin b :=
    (Fintype.equivFin J).toEmbedding.trans ((Fin.castLEEmb enough).trans finProdFinEquiv.symm.toEmbedding)
  let X (t : P) (i : Fin a) : R := MvPolynomial.X (t,Sum.inl i)
  let Y (t : P) (j : Fin b) : R := MvPolynomial.X (t,Sum.inr j)
  let M : Matrix J J R := fun t s =>
    (X t (cells s).1-X anchor (cells s).1)*(Y t (cells s).2-Y anchor (cells s).2)
  let val (v : V) : ℂ := if h : v.1=anchor then 0 else
    v.2.elim (fun i => if i=(cells ⟨v.1,h⟩).1 then 1 else 0)
      (fun j => if j=(cells ⟨v.1,h⟩).2 then 1 else 0)
  have vx (t : J) (i : Fin a) : MvPolynomial.eval val (X t i-X anchor i) =
      if i=(cells t).1 then (1:ℂ) else 0 := by
    simp [X,val,t.property]
  have vy (t : J) (j : Fin b) : MvPolynomial.eval val (Y t j-Y anchor j) =
      if j=(cells t).2 then (1:ℂ) else 0 := by
    simp [Y,val,t.property]
  have idmat : M.map (MvPolynomial.eval val)=1 := by
    ext t s
    change MvPolynomial.eval val ((X t (cells s).1-X anchor (cells s).1)*
      (Y t (cells s).2-Y anchor (cells s).2)) = _
    rw [map_mul,vx,vy]
    by_cases eq : t=s
    · subst s
      simp
    · have ne : (cells s).1≠(cells t).1 ∨ (cells s).2≠(cells t).2 := by
        by_contra! both
        exact eq (cells.injective (Prod.ext both.1 both.2)).symm
      rcases ne with ne | ne <;> simp [ne,eq]
  have det_ne : M.det ≠ 0 := by
    have vdet : MvPolynomial.eval val M.det=1 := by
      rw [RingHom.map_det,RingHom.mapMatrix_apply,idmat,Matrix.det_one]
    intro h
    rw [h,map_zero] at vdet
    exact zero_ne_one vdet
  let φ := algebraMap R K
  have lifted : (M.map φ).det≠0 := by
    rw [← RingHom.mapMatrix_apply,← RingHom.map_det]
    exact fun h => det_ne (IsFractionRing.injective R K (h.trans φ.map_zero.symm))
  let restrict : (Fin a × Fin b → K) →ₗ[K] (J → K) :=
    LinearMap.pi fun j => LinearMap.proj (R:=K) (cells j)
  have independent : LinearIndependent K (fun t : J => g t.val) := by
    apply LinearIndependent.of_comp restrict
    have eq : restrict ∘ (fun t : J => g t.val) = fun t => (M.map φ) t := by
      funext t s
      change (φ (X t (cells s).1)-φ (X anchor (cells s).1))*
        (φ (Y t (cells s).2)-φ (Y anchor (cells s).2)) = φ _
      simp only [M, map_mul, map_sub]
    rw [eq]
    exact Matrix.linearIndependent_rows_of_det_ne_zero lifted
  have at_anchor : g anchor=0 := by funext ij; simp [g,anchor]
  have span_eq : W = Submodule.span K (Set.range (fun t : J => g t.val)) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨t,rfl⟩
      by_cases h : t=anchor
      · rw [h,at_anchor]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨⟨t,h⟩,rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨t,rfl⟩
      exact Submodule.subset_span ⟨t.val,rfl⟩
  have dim := W.finrank_quotient_add_finrank
  have span_dim : Module.finrank K W=Fintype.card J := span_eq ▸ finrank_span_eq_card independent
  rw [span_dim,Module.finrank_pi,Fintype.card_prod,Fintype.card_fin,Fintype.card_fin] at dim
  have positive : 0<c+d := by have := k.isLt; omega
  omega

/-- The anchored chart removes the same number of scalar rows and columns,
preserving the dimension slack in the expected-rank test. -/
theorem size_comparison (a b c r : ℕ) (hc : c≤r) (room : r≤a*b+1) :
    c*((a+1)*(b+1)-r)=c*(a*b+1-r)+c*(a+b) ∧
    r*(a+b)=(r-c)*(a+b)+c*(a+b) := by
  have ab : (a+1)*(b+1)=a*b+1+(a+b) := by ring
  have diff : (a+1)*(b+1)-r=(a*b+1-r)+(a+b) := by omega
  constructor
  · rw [diff, Nat.mul_add]
  · rw [← Nat.add_mul,Nat.sub_add_cancel hc]

end ConsecutiveChart

namespace ConsecutiveChart

/-- The reduced test uses only unanchored point variations and differences
of affine coordinates. Both directions hold, including the change of bases. -/
theorem witness_iff_difference (a b c d : ℕ) :
    (∃ x : Fin (c+d) → Fin (a+1) → ℂ, ∃ y : Fin (c+d) → Fin (b+1) → ℂ,
      ∃ z : Fin (c+d) → Fin c → ℂ,
      ∀ T : Fin (a+1) → Fin (b+1) → Fin c → ℂ, ∃ u : Fin (c+d) → Fin (a+1) → ℂ,
        ∃ v : Fin (c+d) → Fin (b+1) → ℂ, ∃ w : Fin (c+d) → Fin c → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) ↔
    let P := Fin c ⊕ Fin d
    ∃ x : P → Fin a → ℂ, ∃ y : P → Fin b → ℂ, ∃ z : Fin d → Fin c → ℂ,
      let dx (k : Fin c) (t : P) (i : Fin a) := x t i-x (.inl k) i
      let dy (k : Fin c) (t : P) (j : Fin b) := y t j-y (.inl k) j
      let V (k : Fin c) := Submodule.span ℂ (Set.range (fun (t : P) (ij : Fin a × Fin b) =>
        dx k t ij.1*dy k t ij.2))
      Function.Surjective (fun (uv : (Fin d → Fin a → ℂ) × (Fin d → Fin b → ℂ)) (k : Fin c) =>
        (V k).mkQ (∑ t : Fin d, z t k • fun ij : Fin a × Fin b =>
          uv.1 t ij.1*dy k (.inr t) ij.2 + dx k (.inr t) ij.1*uv.2 t ij.2)) := by
  classical
  apply (ConsecutiveAnchor.tangent_iff_anchored_affine a b c d).trans
  apply exists_congr
  intro x
  apply exists_congr
  intro y
  apply exists_congr
  intro z
  let X (t : Fin c ⊕ Fin d) : Fin (a+1) → ℂ := Fin.cases 1 (x t)
  let Y (t : Fin c ⊕ Fin d) : Fin (b+1) → ℂ := Fin.cases 1 (y t)
  have head : (fun l : Fin c => Pi.single l (1:ℂ)) =
      (fun l k : Fin c => if l=k then (1:ℂ) else 0) := by
    funext l k
    by_cases eq : l=k <;> simp [eq, eq_comm]
  rw [head]
  exact (ConsecutiveQuotient.anchored_tangent_iff_gauged X Y z (fun _ => one_ne_zero)
    (fun _ => one_ne_zero)).trans (affine_difference_iff x y z)

end ConsecutiveChart

namespace CriticalTensor.SixConsecutive

open Nat

theorem count_before_twenty (m : ℕ) (lo : 6 ≤ m) (hi : m < 20) :
    6*m*(m+1) ⌈/⌉ (2*m+5) = 3*m-3 := by
  interval_cases m <;> decide

theorem count_from_twenty (m : ℕ) (hm : 20 ≤ m) :
    6*m*(m+1) ⌈/⌉ (2*m+5) = 3*m-4 := by
  let r := 6*m*(m+1) ⌈/⌉ (2*m+5)
  have hden : 0 < 2*m+5 := by omega
  have hr : 3*m-4+4=3*m := by omega
  have hsum := congrArg (fun x : ℕ => x*(2*m+5)) hr
  apply le_antisymm
  · apply (ceilDiv_le_iff_le_mul hden).mpr
    nlinarith
  · by_contra! h
    have hpos : r+1 ≤ 3*m-4 := by dsimp [r]; omega
    have hmul := Nat.mul_le_mul_left (2*m+5) hpos
    have hcap : 6*m*(m+1) ≤ (2*m+5)*r := (ceilDiv_le_iff_le_mul hden).mp le_rfl
    nlinarith

end CriticalTensor.SixConsecutive

namespace CriticalTensor.SixConsecutive

/-- Four initial configurations and the width-two implication cover the
full range of expected counts, with separate starts at the one-step drop. -/
theorem propagate_counts (P : ℕ → ℕ → Prop)
    (bases : ∀ m : ℕ, (m=6 ∨ m=7 ∨ m=20) → P m (6*m*(m+1) ⌈/⌉ (2*m+5)))
    (last : P 21 59)
    (grow : ∀ m r : ℕ, 6 ≤ m → 3*m-4 ≤ r → P m r → P (m+2) (r+6)) :
    ∀ m : ℕ, 6 ≤ m → P m (6*m*(m+1) ⌈/⌉ (2*m+5)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m prior =>
    intro hm
    by_cases special : m=6 ∨ m=7 ∨ m=20
    · exact bases m special
    by_cases twentyOne : m=21
    · subst m
      exact last
    have prev : 6 ≤ m-2 := by omega
    have low : 3*(m-2)-4 ≤ 6*(m-2)*(m-2+1) ⌈/⌉ (2*(m-2)+5) := by
      by_cases before : m-2<20
      · rw [count_before_twenty _ prev before]
        omega
      · rw [count_from_twenty _ (by omega)]
    have step := grow (m-2) _ prev low (prior (m-2) (by omega) prev)
    have index : m-2+2=m := by omega
    rw [index] at step
    by_cases before : m<20
    · rw [count_before_twenty _ prev (by omega)] at step
      rw [count_before_twenty _ hm before]
      convert step using 1
      omega
    · rw [count_from_twenty _ (by omega)] at step
      rw [count_from_twenty _ (by omega)]
      convert step using 1
      omega

end CriticalTensor.SixConsecutive

namespace OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H1_R1_H2_R1

/-- The two smallest parity seeds and the perfect six-by-twenty-by-twenty-one seed. -/
def H1 : Prop :=
  ∀ m : ℕ, (m=6 ∨ m=7 ∨ m=20) →
    let r := 6*m*(m+1) ⌈/⌉ (2*m+5)
    ∃ x : Fin r → Fin 6 → ℂ, ∃ y : Fin r → Fin m → ℂ, ∃ z : Fin r → Fin (m+1) → ℂ,
      ∀ T : Fin 6 → Fin m → Fin (m+1) → ℂ, ∃ u : Fin r → Fin 6 → ℂ,
        ∃ v : Fin r → Fin m → ℂ, ∃ w : Fin r → Fin (m+1) → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))

/-- The first odd seed after the predicted six-slice count drops by one. -/
def H2 : Prop :=
  ∃ x : Fin 59 → Fin 6 → ℂ, ∃ y : Fin 59 → Fin 21 → ℂ, ∃ z : Fin 59 → Fin 22 → ℂ,
    ∀ T : Fin 6 → Fin 21 → Fin 22 → ℂ, ∃ u : Fin 59 → Fin 6 → ℂ,
      ∃ v : Fin 59 → Fin 21 → ℂ, ∃ w : Fin 59 → Fin 22 → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))

/-- Extend both long axes by two while adding six rank-one points. -/
def H3 : Prop :=
  let P (m r : ℕ) :=
    ∃ x : Fin r → Fin 6 → ℂ, ∃ y : Fin r → Fin m → ℂ, ∃ z : Fin r → Fin (m+1) → ℂ,
      ∀ T : Fin 6 → Fin m → Fin (m+1) → ℂ, ∃ u : Fin r → Fin 6 → ℂ,
        ∃ v : Fin r → Fin m → ℂ, ∃ w : Fin r → Fin (m+1) → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))
  ∀ m r : ℕ, 6 ≤ m → 3*m-4 ≤ r → P m r → P (m+2) (r+6)

/-- From seven slices upward, only the unanchored points vary. Each output
block uses affine differences from its own anchor in the smaller matrix space. -/
def H4 : Prop :=
  ∀ a b : ℕ, 6 ≤ a → a ≤ b → b+2<a*b →
    let c := b+2
    let r := (a+1)*(b+1)*c ⌈/⌉ (a+b+c)
    let d := r-c
    let P := Fin c ⊕ Fin d
    ∃ x : P → Fin a → ℂ, ∃ y : P → Fin b → ℂ, ∃ z : Fin d → Fin c → ℂ,
      let dx (k : Fin c) (t : P) (i : Fin a) := x t i-x (.inl k) i
      let dy (k : Fin c) (t : P) (j : Fin b) := y t j-y (.inl k) j
      let V (k : Fin c) := Submodule.span ℂ (Set.range (fun (t : P) (ij : Fin a × Fin b) =>
        dx k t ij.1*dy k t ij.2))
      Function.Surjective (fun (uv : (Fin d → Fin a → ℂ) × (Fin d → Fin b → ℂ)) (k : Fin c) =>
        (V k).mkQ (∑ t : Fin d, z t k • fun ij : Fin a × Fin b =>
          uv.1 t ij.1*dy k (.inr t) ij.2 + dx k (.inr t) ij.1*uv.2 t ij.2))

/-- There are enough points to choose c anchors, and there is room for all
the other difference products in each reduced corner. -/
theorem anchor_capacity (a b : ℕ) (ha : 5 ≤ a) (hab : a ≤ b) (region : b+2<a*b) :
    let c := b+2
    let r := (a+1)*(b+1)*c ⌈/⌉ (a+b+c)
    c≤r ∧ r≤a*b+1 := by
  intro c r
  have positive : 0<a+b+c := by dsimp [c]; omega
  have cap : (a+1)*(b+1)*c ≤ (a+b+c)*r := (ceilDiv_le_iff_le_mul positive).mp le_rfl
  have dim : a+b+c ≤ (a+1)*(b+1) := by dsimp [c]; nlinarith
  constructor
  · exact Nat.le_of_mul_le_mul_left ((Nat.mul_le_mul_right c dim).trans cap) positive
  · apply (ceilDiv_le_iff_le_mul positive).mpr
    have small : c≤a*b+1 := by dsimp [c]; omega
    nlinarith only [Nat.mul_le_mul_left (a+b) small]

theorem main : H1 → H2 → H3 → H4 → OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H1_R1.H2 := by
  intro bases last grow larger a b ha hab region
  let c := b+2
  let r := (a+1)*(b+1)*c ⌈/⌉ (a+b+c)
  apply (ConsecutiveQuotient.generic_compressed_iff a b c r).mp
  by_cases six : a=5
  · subst a
    let P (m s : ℕ) := ∃ x : Fin s → Fin 6 → ℂ, ∃ y : Fin s → Fin m → ℂ,
      ∃ z : Fin s → Fin (m+1) → ℂ, ∀ T : Fin 6 → Fin m → Fin (m+1) → ℂ,
        ∃ u : Fin s → Fin 6 → ℂ, ∃ v : Fin s → Fin m → ℂ, ∃ w : Fin s → Fin (m+1) → ℂ,
          ∀ i j k, T i j k = ∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))
    have hit := CriticalTensor.SixConsecutive.propagate_counts P bases last grow (b+1) (by omega)
    change P (b+1) (6*(b+1)*(b+2) ⌈/⌉ (5+b+(b+2)))
    simpa only [show 2*(b+1)+5=5+b+(b+2) by omega] using hit
  · have hlarge : 6 ≤ a := by omega
    have enough : c ≤ r := (anchor_capacity a b ha hab region).1
    have h := (ConsecutiveChart.witness_iff_difference a b c (r-c)).mpr (larger a b hlarge hab region)
    rw [show c+(r-c)=r by omega] at h
    exact h

/-- The anchored condition in the larger formats loses no witnesses
compared with the registered generic quotient test. -/
theorem larger_test_of_parent
    (proved : OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H1_R1.H2) : H4 := by
  intro a b ha hab region
  let c := b+2
  let r := (a+1)*(b+1)*c ⌈/⌉ (a+b+c)
  have enough : c≤r := (anchor_capacity a b (by omega) hab region).1
  have witness := (ConsecutiveQuotient.generic_compressed_iff a b c r).mpr (proved a b (by omega) hab region)
  have chart := ConsecutiveChart.witness_iff_difference a b c (r-c)
  rw [show c+(r-c)=r by omega] at chart
  exact chart.mp witness

end OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H1_R1_H2_R1
