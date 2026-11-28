import FormalConjectures.Arxiv.«2208.14736».ZariskiCancellation

/-!
# Two-dimensional Zariski cancellation over an arbitrary field

For every field `k` (any characteristic, possibly finite or imperfect) and every finitely
generated `k`-algebra `B` with `k[x, y][X] ≃ₐ[k] B[X]` we prove `k[x, y] ≃ₐ[k] B`. This is the
statement `Arxiv.«2208.14736».zariski_cancellation_problem.variants.dim_two`.

## Outline

* **Rulings give planes** (`plane_of_ruling`). For any nontrivial exponential map (a
  `G_a`-action) on the coefficient algebra, the file constructs a local slice in every
  characteristic and identifies its fixed ring with a polynomial ring in one variable. If,
  in the quotient by each prime of the fixed ring, every element algebraic over the residue
  field is a scalar (`HasRuling`), then `B` is a polynomial ring in one variable over the
  fixed ring.
* **Homogenization** (`ExpMap.exists_homogenization`). Some coordinate translation of the
  cylinder `B[X] ≃ k[x, y, z]` has an invariant of positive cylinder degree. Give the cylinder
  variable weight `Q` and the parameter of the action weight `-P`, where `P / Q` is the largest
  slope of the action on a finite generating set. The part of top weight is again a nontrivial
  exponential map. It fixes the leading term of every old invariant, hence the cylinder
  variable, and its coefficients on constants are monomials in the cylinder variable.
  Restricting to the fiber `X = 1` then gives a nontrivial exponential map on `B` over every
  field, including the finite ones (`exists_action`).
* **Fibers** (`prime_linear_of_action`, `fiber_condition_of_prime_linear`). Let `S ≃ k[t]` be
  the fixed ring and `K` an algebraic closure of `k`. By flatness the fixed ring of the base
  change is `K ⊗ S = K[t]`, and it is factorially closed in the factorial domain `K ⊗ B`.
  So `t - α` is prime in `K ⊗ B` for every `α : K`. For a prime `p` of `S` with residue field
  `L` and a root `α` of `p` in `K`, this says that `K ⊗[L] (B ⧸ p) = (K ⊗ B) ⧸ (t - α)` is a
  domain: every fiber is geometrically integral over its residue field, also when the residue
  field is inseparable over `k`. An `L`-linear retraction of `K` onto `L` descends scalars,
  which is the fiber condition of `HasRuling` for every nontrivial exponential map.

`cylinderHasRuling` combines the last two parts and `cancellation_of_ruling` concludes.

The homogenization follows Derksen–Hadas–Makar-Limanov and Crachiola–Makar-Limanov. The
theorem over arbitrary fields is due to Bhatwadekar–Gupta (2015),
https://doi.org/10.1142/S0219498815400071; see also Gupta, §2, https://arxiv.org/pdf/2208.14736.
-/

open Polynomial
open scoped TensorProduct

namespace OMA.ZariskiDimTwo

universe u v w

variable {k : Type u} [Field k] {B : Type v} [CommRing B] [Algebra k B]

abbrev Plane (k : Type*) [CommRing k] := MvPolynomial (Fin 2) k

/-- Write the cylinder in affine three-space coordinates. -/
noncomputable def threeVariables (e : (Plane k)[X] ≃ₐ[k] B[X]) :
    MvPolynomial (Fin 3) k ≃ₐ[k] B[X] :=
  (MvPolynomial.finSuccEquiv k 2).trans e

theorem isDomain (e : (Plane k)[X] ≃ₐ[k] B[X]) : IsDomain B := by
  let : IsDomain B[X] := e.symm.injective.isDomain e.symm.toRingHom
  exact Polynomial.C_injective.isDomain (C : B →+* B[X])

/-- Tensoring the entire cylinder identification up to any field extension
again supplies a cylinder identification over that extension. -/
noncomputable def baseChange (K : Type w) [Field K] [Algebra k K]
    (e : (Plane k)[X] ≃ₐ[k] B[X]) : (Plane K)[X] ≃ₐ[K] (K ⊗[k] B)[X] := by
  let convertB := (MvPolynomial.uniqueAlgEquiv B Unit).symm.restrictScalars k
  exact (MvPolynomial.finSuccEquiv K 2).symm |>.trans
    ((MvPolynomial.algebraTensorAlgEquiv k K).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) ((threeVariables e).trans convertB)).trans
    (MvPolynomial.rTensorAlgEquiv.trans
    ((MvPolynomial.uniqueAlgEquiv (K ⊗[k] B) Unit).restrictScalars K))))

theorem geometricallyIntegral (e : (Plane k)[X] ≃ₐ[k] B[X])
    (K : Type w) [Field K] [Algebra k K] : IsDomain (K ⊗[k] B) :=
  isDomain (baseChange K e)

/-- In the affine three-space model all units are nonzero scalars. -/
theorem isUnit_iff_scalar (e : (Plane k)[X] ≃ₐ[k] B[X]) (b : B) :
    IsUnit b ↔ ∃ c : k, c ≠ 0 ∧ algebraMap k B c = b := by
  constructor
  · intro hb
    let f := (threeVariables e).symm
    obtain ⟨c, hc, hfc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp
      ((hb.map (C : B →+* B[X])).map f.toRingHom)
    refine ⟨c, hc.ne_zero, C_injective (f.injective ?_)⟩
    exact (f.commutes c).trans hfc.symm
  · rintro ⟨c, hc, rfl⟩
    exact (isUnit_iff_ne_zero.mpr hc).map (algebraMap k B)

private theorem irreducible_constant {R : Type*} [CommRing R] [IsDomain R] {r : R}
    (hr : Irreducible r) : Irreducible (C r) := by
  refine ⟨fun h ↦ hr.not_isUnit (Polynomial.isUnit_C.mp h), ?_⟩
  intro a b hab
  have hne : (C r : R[X]) ≠ 0 := by simpa using hr.ne_zero
  have hdeg (p : R[X]) (hp : p ∣ C r) : p.natDegree = 0 :=
    Nat.eq_zero_of_le_zero (by simpa using Polynomial.natDegree_le_of_dvd hp hne)
  have ha := Polynomial.eq_C_of_natDegree_eq_zero (hdeg a ⟨b, hab⟩)
  have hb := Polynomial.eq_C_of_natDegree_eq_zero (hdeg b ⟨a, hab.trans (mul_comm _ _)⟩)
  have hcoeff : r = a.coeff 0 * b.coeff 0 := by
    simpa using congrArg (fun q : R[X] ↦ q.coeff 0) hab
  rcases hr.isUnit_or_isUnit hcoeff with h | h
  · exact Or.inl (ha ▸ Polynomial.isUnit_C.mpr h)
  · exact Or.inr (hb ▸ Polynomial.isUnit_C.mpr h)

theorem factorial [Algebra.FiniteType k B] (e : (Plane k)[X] ≃ₐ[k] B[X]) :
    UniqueFactorizationMonoid B := by
  let := isDomain e
  let := Algebra.FiniteType.isNoetherianRing k B
  let := e.toRingEquiv.toMulEquiv.uniqueFactorizationMonoid inferInstance
  exact { irreducible_iff_prime := ⟨fun h ↦
    Polynomial.prime_C_iff.mp (UniqueFactorizationMonoid.irreducible_iff_prime.mp
      (irreducible_constant h)), fun h ↦ h.irreducible⟩ }

theorem geometricallyFactorial [Algebra.FiniteType k B] (e : (Plane k)[X] ≃ₐ[k] B[X])
    (K : Type w) [Field K] [Algebra k K] : UniqueFactorizationMonoid (K ⊗[k] B) :=
  factorial (baseChange K e)

theorem krullDim [Algebra.FiniteType k B] (e : (Plane k)[X] ≃ₐ[k] B[X]) :
    ringKrullDim B = 2 := by
  let := Algebra.FiniteType.isNoetherianRing k B
  have hdim := ringKrullDim_eq_of_ringEquiv (threeVariables e).toRingEquiv
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
    Polynomial.ringKrullDim_of_isNoetherianRing] at hdim
  apply ENat.WithBot.add_one_cancel.mp
  convert hdim.symm using 1
  norm_num

/-- The lift of a square-zero extension for the polynomial algebra restricts
along the constant inclusion and zero evaluation to give a lift for `B`. -/
theorem smooth [Algebra.FiniteType k B] (e : (Plane k)[X] ≃ₐ[k] B[X]) :
    Algebra.Smooth k B := by
  let : Algebra.FormallySmooth k B[X] := Algebra.FormallySmooth.of_equiv (threeVariables e)
  refine ⟨Algebra.FormallySmooth.of_comp_surjective ?_,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  intro D _ _ I hI f
  let ev := (Polynomial.aeval (R := B) (0 : B)).restrictScalars k
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.comp_surjective k B[X] I hI (f.comp ev)
  refine ⟨g.comp (Polynomial.CAlgHom : B →ₐ[k] B[X]), ?_⟩
  ext b
  simpa [ev] using DFunLike.congr_fun hg (C b)

/-- A cylinder isomorphism forces the coordinate algebra to have transcendence degree two. -/
theorem trdeg (e : (Plane k)[X] ≃ₐ[k] B[X]) : Algebra.trdeg k B = 2 := by
  let := isDomain e
  have h₃ : Algebra.trdeg k B[X] = 3 := by
    apply Cardinal.lift_injective.{u,v}
    simpa using (threeVariables e).lift_trdeg_eq.symm
  apply Cardinal.add_one_inj.mp
  calc
    Algebra.trdeg k B + 1 = Algebra.trdeg k B[X] := by simpa using (trdeg_add_eq k B (A := B[X]))
    _ = 2 + 1 := by simpa only [show (2 + 1 : Cardinal.{v}) = 3 by norm_num] using h₃

/-- The same dimension computation for the rational function field. -/
theorem fractionRing_trdeg [IsDomain B] (e : (Plane k)[X] ≃ₐ[k] B[X]) :
    Algebra.trdeg k (FractionRing B) = 2 := by
  let := IsLocalization.isAlgebraic (FractionRing B) (nonZeroDivisors B)
  rw [← trdeg_add_eq k B, trdeg_eq_zero (R := B) (A := FractionRing B), add_zero, trdeg e]

/-- Finding any two algebra generators suffices: the stable isomorphism forces
algebraic independence of those generators. -/
noncomputable def equivOfGenerators (e : (Plane k)[X] ≃ₐ[k] B[X])
    (x : Fin 2 → B) (hx : Algebra.adjoin k (Set.range x) = ⊤) : Plane k ≃ₐ[k] B := by
  let := isDomain e
  have halg : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range x)) B := by
    rw [hx]
    exact ⟨fun b ↦ (isIntegral_algebraMap (x := (⟨b, trivial⟩ : (⊤ : Subalgebra k B)))).isAlgebraic⟩
  have htb := Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite k x
    (by simp [trdeg e])
  refine AlgEquiv.ofBijective (MvPolynomial.aeval x)
    ⟨algebraicIndependent_iff_injective_aeval.mp htb.1, ?_⟩
  rwa [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]

/-- The easy cancellation case: the extra variable is still affine-linear with
unit slope in the cylinder presentation. Evaluation at its root recovers `B`. -/
noncomputable def equivOfLinearCoordinate (e : (Plane k)[X] ≃ₐ[k] B[X])
    (u : Bˣ) (b : B) (hX : e X = C (u : B) * (X - C b)) : Plane k ≃ₐ[k] B := by
  let left := (Polynomial.quotientSpanXSubCAlgEquiv (0 : Plane k)).restrictScalars k
  let right := (Polynomial.quotientSpanXSubCAlgEquiv b).restrictScalars k
  refine left.symm.trans ((Ideal.quotientEquivAlg _ _ e ?_).trans right)
  simp [Ideal.map_span, hX, Ideal.span_singleton_mul_left_unit (u.isUnit.map C)]

end OMA.ZariskiDimTwo

namespace OMA.ZariskiDimTwo

universe u v w
variable {k : Type u} [Field k]

/-- Every nonconstant multivariate polynomial stays nonconstant on some polynomial
curve over its ground field. Multiples of `X` in `k[X]` provide infinitely many
choices with zero constant term, including when `k` is finite. -/
theorem exists_nonconstant_specialization {ι : Type*} {p : MvPolynomial ι k}
    (hp : p ∉ Set.range MvPolynomial.C) :
    ∃ x : ι → k[X], 0 < (MvPolynomial.aeval x p).natDegree := by
  classical
  by_contra! h
  let c := MvPolynomial.constantCoeff p
  apply hp
  refine ⟨c, (MvPolynomial.map_injective (C : k →+* k[X]) Polynomial.C_injective) ?_⟩
  let s : Set k[X] := Set.range fun q : k[X] ↦ X * q
  have hs : s.Infinite := Set.infinite_range_of_injective (mul_right_injective₀ X_ne_zero)
  apply MvPolynomial.funext_set (fun _ : ι ↦ s) (fun _ ↦ hs)
  intro x hx
  let ev : k[X] →ₐ[k] k := Polynomial.aeval 0
  have hx0 : (fun i ↦ ev (x i)) = 0 := by
    funext i
    obtain ⟨q, hq⟩ := hx i (Set.mem_univ i)
    simp [← hq, ev]
  have h₀ : ev (MvPolynomial.aeval x p) = c := by
    rw [MvPolynomial.comp_aeval_apply, hx0]
    simp [c, MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.eval₂Hom_zero]
  have hc := Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero (h x))
  have hcoeff : (MvPolynomial.aeval x p).coeff 0 = c := by
    simpa [ev, ← Polynomial.coeff_zero_eq_aeval_zero] using h₀
  rw [MvPolynomial.map_C, MvPolynomial.eval_C, MvPolynomial.eval_map]
  exact (hc.trans (congrArg C hcoeff)).symm

/-- In transcendence degree one, keeping one element transcendental makes the
whole curve map injective. -/
theorem injective_of_transcendental_image {R : Type v} [CommRing R] [IsDomain R] [Algebra k R]
    {D : Type w} [CommRing D] [Algebra k D] (f : R →ₐ[k] D)
    (hdeg : Algebra.trdeg k R = 1) {y : R} (hy : Transcendental k (f y)) :
    Function.Injective f := by
  have hyR : Transcendental k y := fun h ↦ hy (h.algHom f)
  have hi : AlgebraicIndependent k (fun _ : Unit ↦ y) := algebraicIndependent_unique_type_iff.mpr hyR
  have hb := hi.isTranscendenceBasis_of_lift_trdeg_le_of_finite (by simp [hdeg])
  let S := Algebra.adjoin k (Set.range fun _ : Unit ↦ y)
  have hRange : Set.range (fun _ : Unit ↦ y) = ({y} : Set R) := Set.range_const
  have halg : Algebra.IsAlgebraic S R := hb.isAlgebraic
  have hS : Function.Injective (fun a : S ↦ f a.val) := by
    intro a b hab
    have ha : (a : R) ∈ (Polynomial.aeval (R := k) y).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval, ← hRange]; exact a.property
    have hb' : (b : R) ∈ (Polynomial.aeval (R := k) y).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval, ← hRange]; exact b.property
    obtain ⟨p, hp⟩ := ha
    obtain ⟨q, hq⟩ := hb'
    change Polynomial.aeval (R := k) y p = a.val at hp
    change Polynomial.aeval (R := k) y q = b.val at hq
    apply Subtype.ext
    rw [← hp, ← hq]
    congr 1
    apply (transcendental_iff_injective.mp hy)
    rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_algHom_apply, hp, hq]
    exact hab
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra hne
  obtain ⟨s, hs, hd⟩ := (halg.1 a).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hne)
  have hz : f s.val = 0 := by simpa [ha] using (map_dvd f hd)
  exact hs (hS (by simpa using hz))

/- The univariate normal-subalgebra argument below is from the Open Math Agents
dimension-one cancellation proof (credited there to @Dugongue). -/
private noncomputable def swapPoly (k : Type u) [CommRing k] : k[X][X] ≃ₐ[k] k[X][X] := by
  let innerToOuter : k[X] →ₐ[k] k[X][X] := Polynomial.mapAlgHom (Algebra.ofId k k[X])
  let toFun : k[X][X] →ₐ[k] k[X][X] :=
    Polynomial.eval₂AlgHom innerToOuter (C (X : k[X])) (fun _ => Commute.all _ _)
  have hto_C : ∀ p : k[X], toFun (C p) = p.map C := fun p => by
    simp [toFun, innerToOuter]
  have hto_X : toFun X = C X := by
    simp [toFun]
  have hinv : toFun.comp toFun = AlgHom.id k k[X][X] := by
    apply Polynomial.algHom_ext'
    · apply Polynomial.algHom_ext
      simp [hto_C, hto_X]
    · simp [hto_X, hto_C]
  exact AlgEquiv.ofAlgHom toFun toFun hinv hinv

private lemma swapPoly_C {k : Type u} [CommRing k] (p : k[X]) :
    swapPoly k (C p) = p.map C := by
  simp [swapPoly]

private lemma swapPoly_X {k : Type u} [CommRing k] :
    swapPoly k (X : k[X][X]) = C X := by
  simp [swapPoly]

private lemma swapPoly_map_C {k : Type u} [CommRing k] (p : k[X]) :
    swapPoly k (p.map C) = C p := by
  rw [← swapPoly_C p]
  exact (swapPoly k).symm_apply_apply (C p)

private lemma swapPoly_coeff_coeff {k : Type u} [CommRing k] (F : k[X][X]) (i j : ℕ) :
    ((swapPoly k F).coeff j).coeff i = (F.coeff i).coeff j := by
  induction F using Polynomial.induction_on' with
  | add F₁ F₂ h₁ h₂ =>
    simp [map_add, h₁, h₂]
  | monomial n p =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, swapPoly_C, map_pow, swapPoly_X,
      ← map_pow, Polynomial.coeff_mul_C, Polynomial.coeff_map, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_mul_X_pow]
    split_ifs <;> simp

private lemma natDegree_coeff_le_natDegree_swapPoly {k : Type u} [CommRing k]
    (F : k[X][X]) (i : ℕ) :
    (F.coeff i).natDegree ≤ (swapPoly k F).natDegree := by
  rcases eq_or_ne (F.coeff i) 0 with h0 | hne
  · simp [h0]
  · refine Polynomial.le_natDegree_of_ne_zero ?_
    intro hzero
    have hc := congrArg (fun p : k[X] => p.coeff i) hzero
    rw [swapPoly_coeff_coeff, Polynomial.coeff_zero] at hc
    exact (Polynomial.leadingCoeff_ne_zero.mpr hne) hc

private lemma subalgebra_eq_poly_of_integrally_closed {k : Type u} [Field k]
    (S : Subalgebra k k[X]) [IsIntegrallyClosed S]
    (hnonconst : ∃ u : S, 0 < u.1.natDegree) : Nonempty (k[X] ≃ₐ[k] S) := by
  classical
  have hex_deg : ∃ d : ℕ, 0 < d ∧ ∃ u : S, u.1.natDegree = d := by
    obtain ⟨u, hu⟩ := hnonconst
    exact ⟨u.1.natDegree, hu, u, rfl⟩
  let d : ℕ := Nat.find hex_deg
  have hd_spec : 0 < d ∧ ∃ u : S, u.1.natDegree = d := Nat.find_spec hex_deg
  have hd_pos : 0 < d := hd_spec.1
  obtain ⟨u, hu_deg⟩ := hd_spec.2
  have hmin : ∀ s : S, 0 < s.1.natDegree → d ≤ s.1.natDegree := by
    intro s hs
    exact Nat.find_min' hex_deg ⟨hs, s, rfl⟩
  let diffPoly : S → S[X] := fun s => s.1.map (algebraMap k S) - C s
  have hdiff_aeval : ∀ s : S, Polynomial.aeval (R := S) (X : k[X]) (diffPoly s) = 0 := by
    intro s
    dsimp [diffPoly]
    rw [map_sub (Polynomial.aeval (R := S) (X : k[X])), Polynomial.aeval_C,
      Polynomial.aeval_map_algebraMap]
    change Polynomial.aeval (X : k[X]) s.1 - s.1 = 0
    simp
  have hu_ne : u.1 ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hu_deg
    omega
  have hu_lc_ne : u.1.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hu_ne
  have hdiff_u_deg : (diffPoly u).natDegree = d := by
    dsimp [diffPoly]
    have hmap_deg : (u.1.map (algebraMap k S)).natDegree = d := by
      rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective (algebraMap k S)), hu_deg]
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · exact hmap_deg
    · simp [hmap_deg, hd_pos]
  have hdiff_u_lc : (diffPoly u).leadingCoeff = algebraMap k S u.1.leadingCoeff := by
    dsimp [diffPoly]
    have hmap_deg : (u.1.map (algebraMap k S)).natDegree = d := by
      rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective (algebraMap k S)), hu_deg]
    have hmap_ne : u.1.map (algebraMap k S) ≠ 0 := by
      intro h0
      rw [h0, Polynomial.natDegree_zero] at hmap_deg
      omega
    have hdeg_lt : (C u).degree < (u.1.map (algebraMap k S)).degree := by
      refine lt_of_le_of_lt Polynomial.degree_C_le ?_
      rw [Polynomial.degree_eq_natDegree hmap_ne, hmap_deg]
      exact_mod_cast hd_pos
    rw [Polynomial.leadingCoeff_sub_of_degree_lt hdeg_lt,
      Polynomial.leadingCoeff_map_of_injective (RingHom.injective (algebraMap k S))]
  have hX_int : IsIntegral S (X : k[X]) := by
    refine ⟨C (algebraMap k S u.1.leadingCoeff⁻¹) * diffPoly u, ?_, ?_⟩
    · rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hdiff_u_lc,
        ← map_mul, inv_mul_cancel₀ hu_lc_ne, map_one]
    · rw [← Polynomial.aeval_def, map_mul, hdiff_aeval u, mul_zero]
  let m : S[X] := minpoly S (X : k[X])
  have hm_monic : m.Monic := minpoly.monic hX_int
  have hm_dvd_u : m ∣ diffPoly u := minpoly.isIntegrallyClosed_dvd hX_int (hdiff_aeval u)
  obtain ⟨q, hq⟩ := hm_dvd_u
  have hmap_diff : (diffPoly u).map S.val.toRingHom = u.1.map C - C u.1 := by
    dsimp [diffPoly]
    rw [Polynomial.map_sub, Polynomial.map_map, Polynomial.map_C]
    rfl
  let M : k[X][X] := swapPoly k (m.map S.val.toRingHom)
  let Q : k[X][X] := swapPoly k (q.map S.val.toRingHom)
  have hMQ : C u.1 - u.1.map C = M * Q := by
    have h1 := congrArg (fun p : S[X] => swapPoly k (p.map S.val.toRingHom)) hq
    rw [hmap_diff, map_sub, swapPoly_map_C, swapPoly_C, Polynomial.map_mul, map_mul] at h1
    exact h1
  have hLHS_deg : (C u.1 - u.1.map C).natDegree = d := by
    have hmap_deg : (u.1.map C).natDegree = d := by
      rw [Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective, hu_deg]
    rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt]
    · exact hmap_deg
    · simp [hmap_deg, hd_pos]
  have hLHS_lc : (C u.1 - u.1.map C).leadingCoeff = C (-u.1.leadingCoeff) := by
    have hmap_deg : (u.1.map C).natDegree = d := by
      rw [Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective, hu_deg]
    have hmap_ne : (u.1.map C : k[X][X]) ≠ 0 := by
      intro h0
      rw [h0, Polynomial.natDegree_zero] at hmap_deg
      omega
    have hlt : (C u.1 : k[X][X]).degree < (u.1.map C).degree := by
      refine lt_of_le_of_lt Polynomial.degree_C_le ?_
      rw [Polynomial.degree_eq_natDegree hmap_ne, hmap_deg]
      exact_mod_cast hd_pos
    rw [sub_eq_add_neg, Polynomial.leadingCoeff_add_of_degree_lt (by simpa using hlt),
      Polynomial.leadingCoeff_neg, Polynomial.leadingCoeff_map_of_injective Polynomial.C_injective,
      ← map_neg]
  have hLHS_ne : (C u.1 - u.1.map C : k[X][X]) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hLHS_deg
    omega
  have hM_ne : M ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hMQ
    exact hLHS_ne hMQ
  have hQ_ne : Q ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hMQ
    exact hLHS_ne hMQ
  have hM_ge_d : d ≤ M.natDegree := by
    have hex_nonconst : ∃ i : ℕ, 0 < (m.coeff i).1.natDegree := by
      by_contra hall
      push Not at hall
      have hcoeff_C : ∀ i : ℕ, (m.coeff i).1 = C ((m.coeff i).1.coeff 0) :=
        fun i => Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp (hall i))
      let m₀ : k[X] := ∑ i ∈ m.support, C ((m.coeff i).1.coeff 0) * X ^ i
      have hm_eq : m.map S.val.toRingHom = m₀.map C := by
        apply Polynomial.ext
        intro i
        rw [Polynomial.coeff_map, Polynomial.coeff_map]
        dsimp [m₀]
        rw [Polynomial.finsetSum_coeff]
        by_cases hi : i ∈ m.support
        · rw [Finset.sum_eq_single i]
          · simp only [Polynomial.coeff_C_mul_X_pow, ↓reduceIte]
            exact hcoeff_C i
          · intro j _ hne
            simp [hne.symm]
          · intro hmem
            exact absurd hi hmem
        · rw [Finset.sum_eq_zero]
          · have hm0 : m.coeff i = 0 := Polynomial.notMem_support_iff.mp hi
            simp [hm0]
          · intro j hj
            have hne : i ≠ j := fun h => hi (h ▸ hj)
            simp [hne]
      have hm₀_zero : m₀ = 0 := by
        have haeval : Polynomial.aeval (X : k[X]) m = 0 := minpoly.aeval S (X : k[X])
        have h1 : (m.map S.val.toRingHom).eval (X : k[X]) = 0 := by
          rw [Polynomial.eval_map]
          exact haeval
        rw [hm_eq, Polynomial.eval_map] at h1
        have h2 : Polynomial.eval₂ C (X : k[X]) m₀ = m₀ := Polynomial.eval₂_C_X
        exact h2.symm.trans h1
      have hm_zero : m = 0 := by
        apply Polynomial.ext
        intro i
        apply Subtype.ext
        rw [Polynomial.coeff_zero, ZeroMemClass.coe_zero, hcoeff_C i]
        have hi0 : m₀.coeff i = 0 := by rw [hm₀_zero, Polynomial.coeff_zero]
        dsimp [m₀] at hi0
        rw [Polynomial.finsetSum_coeff] at hi0
        by_cases hi : i ∈ m.support
        · rw [Finset.sum_eq_single i] at hi0
          · simp only [Polynomial.coeff_C_mul_X_pow, ↓reduceIte] at hi0
            simp [hi0]
          · intro j _ hne
            simp [hne.symm]
          · intro hmem
            exact absurd hi hmem
        · have : m.coeff i = 0 := Polynomial.notMem_support_iff.mp hi
          simp [this]
      exact hm_monic.ne_zero hm_zero
    obtain ⟨i, hi⟩ := hex_nonconst
    calc d ≤ (m.coeff i).1.natDegree := hmin (m.coeff i) hi
      _ = ((m.map S.val.toRingHom).coeff i).natDegree := by simp
      _ ≤ M.natDegree := natDegree_coeff_le_natDegree_swapPoly _ i
  have hQ_deg0 : Q.natDegree = 0 := by
    have hmul : (M * Q).natDegree = M.natDegree + Q.natDegree :=
      Polynomial.natDegree_mul hM_ne hQ_ne
    rw [← hMQ, hLHS_deg] at hmul
    omega
  have hQ_C : Q = C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hQ_deg0
  have hQ0_ne : Q.coeff 0 ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hQ_C
    exact hQ_ne hQ_C
  have hQ0_deg0 : (Q.coeff 0).natDegree = 0 := by
    have hlc := congrArg Polynomial.leadingCoeff hMQ
    rw [hLHS_lc, Polynomial.leadingCoeff_mul, hQ_C, Polynomial.leadingCoeff_C] at hlc
    have hMlc_ne : M.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hM_ne
    have hdeg := congrArg Polynomial.natDegree hlc
    rw [Polynomial.natDegree_C, Polynomial.natDegree_mul hMlc_ne hQ0_ne] at hdeg
    omega
  let c : k := (Q.coeff 0).coeff 0
  have hQ0_eq_Cc : Q.coeff 0 = C c := Polynomial.eq_C_of_natDegree_eq_zero hQ0_deg0
  have hc_ne : c ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hQ0_eq_Cc
    exact hQ0_ne hQ0_eq_Cc
  have hQ_CC : Q = C (C c) := by
    rw [hQ_C, hQ0_eq_Cc]
  have hq_C : q = C (algebraMap k S c) := by
    have h1 : q.map S.val.toRingHom = C (C c) := by
      have h2 := congrArg (swapPoly k).symm hQ_CC
      have h3 : (swapPoly k).symm (C (C c)) = C (C c) := by
        apply (swapPoly k).injective
        simp [swapPoly_C]
      simpa [Q, h3] using h2
    apply Polynomial.map_injective S.val.toRingHom Subtype.val_injective
    rw [h1, Polynomial.map_C]
    rfl
  have hu_dvd_m : diffPoly u ∣ m := by
    refine ⟨C (algebraMap k S c⁻¹), ?_⟩
    rw [hq, hq_C, mul_assoc, ← map_mul, ← map_mul, mul_inv_cancel₀ hc_ne, map_one, map_one,
      mul_one]
  have hmem_adjoin : ∀ n : ℕ, ∀ s : S, s.1.natDegree ≤ n →
      s.1 ∈ Algebra.adjoin k ({u.1} : Set k[X]) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hs_deg
      have hdiv_s : diffPoly u ∣ diffPoly s :=
        dvd_trans hu_dvd_m (minpoly.isIntegrallyClosed_dvd hX_int (hdiff_aeval s))
      obtain ⟨g, hg⟩ := hdiv_s
      have hg0 := congrArg (fun p : S[X] => p.coeff 0) hg
      simp only [diffPoly, Polynomial.coeff_sub, Polynomial.coeff_map, Polynomial.coeff_C_zero,
        Polynomial.mul_coeff_zero] at hg0
      have hg0_val := congrArg Subtype.val hg0
      simp only [Subalgebra.coe_sub, Subalgebra.coe_mul] at hg0_val
      have hs_eq : s.1 = C (s.1.coeff 0) + (u.1 - C (u.1.coeff 0)) * (g.coeff 0).1 := by
        change C (s.1.coeff 0) - s.1 = (C (u.1.coeff 0) - u.1) * (g.coeff 0).1 at hg0_val
        linear_combination -hg0_val
      rcases eq_or_ne (g.coeff 0).1 0 with h0 | hne
      · rw [h0, mul_zero, add_zero] at hs_eq
        rw [hs_eq]
        exact Subalgebra.algebraMap_mem _ (s.1.coeff 0)
      · have hu_sub_deg : (u.1 - C (u.1.coeff 0)).natDegree = d := by
          rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
          · exact hu_deg
          · simp [hu_deg, hd_pos]
        have hu_sub_ne : u.1 - C (u.1.coeff 0) ≠ 0 := by
          intro h0
          rw [h0, Polynomial.natDegree_zero] at hu_sub_deg
          omega
        have hprod_deg : ((u.1 - C (u.1.coeff 0)) * (g.coeff 0).1).natDegree =
            d + (g.coeff 0).1.natDegree := by
          rw [Polynomial.natDegree_mul hu_sub_ne hne, hu_sub_deg]
        have hs_deg_eq : s.1.natDegree = d + (g.coeff 0).1.natDegree := by
          rw [hs_eq, Polynomial.natDegree_add_eq_right_of_natDegree_lt]
          · exact hprod_deg
          · rw [hprod_deg]
            have : (C (s.1.coeff 0) : k[X]).natDegree = 0 := Polynomial.natDegree_C _
            omega
        have hg0_lt : (g.coeff 0).1.natDegree < n := by omega
        have hg0_mem : (g.coeff 0).1 ∈ Algebra.adjoin k ({u.1} : Set k[X]) :=
          ih (g.coeff 0).1.natDegree hg0_lt (g.coeff 0) le_rfl
        rw [hs_eq]
        refine Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _)
          (Subalgebra.mul_mem _ (Subalgebra.sub_mem _ (Algebra.subset_adjoin rfl)
            (Subalgebra.algebraMap_mem _ _)) hg0_mem)
  have hsurj : Function.Surjective (Polynomial.aeval (R := k) u) := by
    intro s
    have hmem := hmem_adjoin s.1.natDegree s le_rfl
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
    obtain ⟨p, hp⟩ := hmem
    refine ⟨p, Subtype.ext ?_⟩
    have hval : (Polynomial.aeval (R := k) u p).1 = Polynomial.aeval (R := k) u.1 p := by
      have := Polynomial.aeval_algHom_apply S.val u p
      exact this.symm
    exact hval.trans hp
  have hinj : Function.Injective (Polynomial.aeval (R := k) u) := by
    intro p₁ p₂ h
    have hval : Polynomial.aeval (R := k) u.1 p₁ = Polynomial.aeval (R := k) u.1 p₂ := by
      have h1 : Polynomial.aeval (R := k) u.1 p₁ = S.val (Polynomial.aeval (R := k) u p₁) :=
        Polynomial.aeval_algHom_apply S.val u p₁
      have h2 : Polynomial.aeval (R := k) u.1 p₂ = S.val (Polynomial.aeval (R := k) u p₂) :=
        Polynomial.aeval_algHom_apply S.val u p₂
      rw [h1, h2, h]
    have hsub : (p₁ - p₂).comp u.1 = 0 := by
      have hcomp : (p₁ - p₂).comp u.1 = Polynomial.aeval (R := k) u.1 (p₁ - p₂) := rfl
      rw [hcomp, map_sub, hval, sub_self]
    by_contra hne
    have hsub_ne : p₁ - p₂ ≠ 0 := sub_ne_zero.mpr hne
    have hdeg := Polynomial.natDegree_comp (p := p₁ - p₂) (q := u.1)
    rw [hsub, Polynomial.natDegree_zero, hu_deg] at hdeg
    have hdeg0 : (p₁ - p₂).natDegree = 0 :=
      (mul_eq_zero.mp hdeg.symm).resolve_right hd_pos.ne'
    have hC := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
    rw [hC, Polynomial.C_comp] at hsub
    exact hsub_ne (hC.trans hsub)
  exact ⟨AlgEquiv.ofBijective (Polynomial.aeval (R := k) u) ⟨hinj, hsurj⟩⟩


/-- A normal domain of transcendence degree one inside a multivariate polynomial
algebra over any field is itself a polynomial algebra. This applies to an action's
invariant ring once normality and the drop in transcendence degree are known. -/
theorem normal_curve_in_polynomial_ring {R : Type v} [CommRing R] [IsDomain R]
    [Algebra k R] [IsIntegrallyClosed R] {ι : Type w}
    (j : R →ₐ[k] MvPolynomial ι k) (hj : Function.Injective j)
    (hdeg : Algebra.trdeg k R = 1) : Nonempty (k[X] ≃ₐ[k] R) := by
  have hna : ¬ Algebra.IsAlgebraic k R := by
    intro h
    have hz := trdeg_eq_zero (R := k) (A := R)
    simp [hdeg] at hz
  obtain ⟨y, hy⟩ := (Algebra.transcendental_iff_not_isAlgebraic.mpr hna).transcendental
  have hnc : j y ∉ Set.range MvPolynomial.C := by
    rintro ⟨c, hc⟩
    have h : algebraMap k R c = y := hj ((j.commutes c).trans hc)
    exact hy (h ▸ (isAlgebraic_algebraMap (A := R) c))
  obtain ⟨x, hx⟩ := exists_nonconstant_specialization hnc
  let f := (MvPolynomial.aeval x).comp j
  have hyf : Transcendental k (f y) :=
    (f y).transcendental hx.ne' (mem_nonZeroDivisors_of_ne_zero
      (Polynomial.leadingCoeff_ne_zero.mpr (fun h ↦ by
        change 0 < (f y).natDegree at hx
        simp [h] at hx)))
  let e := AlgEquiv.ofInjective f (injective_of_transcendental_image f hdeg hyf)
  have : IsIntegrallyClosed f.range := IsIntegrallyClosed.of_equiv e.toRingEquiv
  obtain ⟨h⟩ := subalgebra_eq_poly_of_integrally_closed f.range ⟨e y, hx⟩
  exact ⟨h.trans e.symm⟩

section Fibers

variable {R A : Type*} [CommRing R] [UniqueFactorizationMonoid R]
    [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A]

/-- Every element becomes a polynomial in `z` upon clearing a scalar denominator. -/
def GenericGenerator (z : A) : Prop :=
  ∀ a : A, ∃ d : R, d ≠ 0 ∧ algebraMap R A d * a ∈ Algebra.adjoin R {z}

/-- If the polynomial subalgebra is saturated at every prime of the base, clearing
scalar denominators proves that a generic generator is an actual generator. -/
theorem adjoin_eq_top_of_saturated {z : A} (hgen : GenericGenerator (R := R) z)
    (hsat : ∀ p : R, Prime p → ∀ F : R[X],
      algebraMap R A p ∣ Polynomial.aeval z F → C p ∣ F) :
    Algebra.adjoin R ({z} : Set A) = ⊤ := by
  apply top_unique
  intro a _
  obtain ⟨d, hd, ha⟩ := hgen a
  let S := Algebra.adjoin R ({z} : Set A)
  have cancel (q : R) : q ≠ 0 → algebraMap R A q * a ∈ S → a ∈ S := by
    induction q using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => simp
    | h₂ q hunit =>
      intro _ h
      obtain ⟨u, rfl⟩ := hunit
      simpa [← mul_assoc, ← map_mul] using
        S.mul_mem (S.algebraMap_mem (↑u⁻¹ : R)) h
    | h₃ q p hq hprime ih =>
      intro _ h
      apply ih hq
      have hF : algebraMap R A (p * q) * a ∈ (Polynomial.aeval (R := R) z).range := by
        rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact h
      obtain ⟨F, hF⟩ := hF
      change Polynomial.aeval z F = algebraMap R A (p * q) * a at hF
      obtain ⟨G, rfl⟩ := hsat p hprime F ⟨_, hF.trans (by rw [map_mul, mul_assoc])⟩
      have hcancel : algebraMap R A p ≠ 0 :=
        (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R A)).mpr hprime.ne_zero
      rw [map_mul, Polynomial.aeval_C, map_mul, mul_assoc, mul_right_inj' hcancel] at hF
      exact hF ▸ Polynomial.aeval_mem_adjoin_singleton R z
  exact cancel d hd ha

/-- A local slice with a nonzero scalar derivative can be improved whenever its
residue is scalar. Factorization in the base makes the improvements terminate.
The fiber hypothesis says that every polynomial relation in a prime fiber either
vanishes coefficientwise or makes the residue of the chosen element a scalar. -/
theorem exists_generator_of_fiber_condition (D : A →ₗ[R] A) (hD₁ : D 1 = 0)
    (hstart : ∃ (c : R) (z : A), c ≠ 0 ∧ D z = algebraMap R A c ∧
      GenericGenerator (R := R) z)
    (hcontract : ∀ p : R, Prime p → ∀ c : R, algebraMap R A p ∣ algebraMap R A c → p ∣ c)
    (hfiber : ∀ p : R, Prime p → ∀ (z : A) (F : R[X]),
      algebraMap R A p ∣ Polynomial.aeval z F →
        C p ∣ F ∨ ∃ r : R, algebraMap R A p ∣ z - algebraMap R A r) :
    ∃ z : A, Algebra.adjoin R ({z} : Set A) = ⊤ := by
  classical
  let M : Set R := {c | ∃ z : A, c ≠ 0 ∧ D z = algebraMap R A c ∧ GenericGenerator (R := R) z}
  obtain ⟨c, ⟨z, hc, hDz, hgen⟩, hmin⟩ := wellFounded_dvdNotUnit.has_min M hstart
  refine ⟨z, adjoin_eq_top_of_saturated hgen (fun p hp F hF ↦ ?_)⟩
  rcases hfiber p hp z F hF with h | ⟨r, w, hw⟩
  · exact h
  exfalso
  have hrepr : z = algebraMap R A p * w + algebraMap R A r := sub_eq_iff_eq_add.mp hw
  have hDr : D (algebraMap R A r) = 0 := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hD₁, smul_zero]
  have hD : algebraMap R A c = algebraMap R A p * D w := by
    rw [← hDz, hrepr, map_add, hDr, add_zero, ← Algebra.smul_def, map_smul, Algebra.smul_def]
  obtain ⟨c', hpc⟩ := hcontract p hp c ⟨_, hD⟩
  have hc' : c' ≠ 0 := by intro h; simp [hpc, h] at hc
  have hp' : algebraMap R A p ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R A)).mpr hp.ne_zero
  have hDw : D w = algebraMap R A c' := by
    rw [hpc, map_mul, mul_right_inj' hp'] at hD
    exact hD.symm
  have hle : Algebra.adjoin R ({z} : Set A) ≤ Algebra.adjoin R ({w} : Set A) := by
    apply Algebra.adjoin_le
    rintro a (rfl : a = z)
    rw [hrepr]
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (Algebra.self_mem_adjoin_singleton R w)) (Subalgebra.algebraMap_mem _ _)
  apply hmin c' ⟨w, hc', hDw, fun a ↦ ?_⟩ ⟨hc', p, hp.not_isUnit, hpc.trans (mul_comm _ _)⟩
  obtain ⟨d, hd, hda⟩ := hgen a
  exact ⟨d, hd, hle hda⟩

end Fibers

private theorem scalar_of_algClosed_algebraic {F D : Type*} [Field F] [IsAlgClosed F]
    [CommRing D] [IsDomain D] [Algebra F D] {a : D} (h : IsAlgebraic F a) :
    ∃ c : F, algebraMap F D c = a := by
  have hint := h.isIntegral
  have hm := minpoly.monic hint
  have hd := IsAlgClosed.degree_eq_one_of_irreducible F (minpoly.irreducible hint)
  have he := minpoly.aeval F a
  rw [Polynomial.eq_X_add_C_of_degree_eq_one hd, hm.leadingCoeff, C_1, one_mul,
    Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_C, add_eq_zero_iff_eq_neg,
    ← map_neg] at he
  exact ⟨_, he.symm⟩

/-- An element algebraic over the ground field in a geometrically integral
algebra is a scalar, even if the ground field is imperfect. -/
theorem scalar_of_geometrically_integral {F D : Type*} [Field F] [CommRing D] [Algebra F D]
    [IsDomain (AlgebraicClosure F ⊗[F] D)] {a : D} (h : IsAlgebraic F a) :
    ∃ c : F, algebraMap F D c = a := by
  let L := AlgebraicClosure F
  let T := L ⊗[F] D
  let j : D →ₐ[F] T := Algebra.TensorProduct.includeRight
  have hint : IsIntegral L (j a) := ((h.algHom j).tower_top L).isIntegral
  obtain ⟨c, he⟩ := scalar_of_algClosed_algebraic hint.isAlgebraic
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one F (one_ne_zero : (1 : L) ≠ 0)
  have hTensor : (1 : L) ⊗ₜ[F] a = c ⊗ₜ[F] (1 : D) := he.symm
  refine ⟨ℓ c, ?_⟩
  have hscalar := congrArg (fun t ↦ TensorProduct.lid F D ((ℓ.rTensor D) t)) hTensor
  simpa [hℓ, Algebra.algebraMap_eq_smul_one] using hscalar.symm

private theorem fiber_condition_of_relatively_closed
    {R A F D : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Field F] [CommRing D] [Algebra F D]
    (hscalar : ∀ {a : D}, IsAlgebraic F a → ∃ c : F, algebraMap F D c = a)
    (p : R) (g : R →+* F) (f : A →+* D) (hg : Function.Surjective g)
    (hcomm : f.comp (algebraMap R A) = (algebraMap F D).comp g)
    (hg₀ : ∀ r : R, g r = 0 ↔ p ∣ r)
    (hf₀ : ∀ a : A, f a = 0 ↔ algebraMap R A p ∣ a)
    (z : A) (P : R[X]) (hz : algebraMap R A p ∣ Polynomial.aeval z P) :
    C p ∣ P ∨ ∃ r : R, algebraMap R A p ∣ z - algebraMap R A r := by
  by_cases hP : P.map g = 0
  · left
    exact (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr fun i ↦
      (hg₀ _).mp (by simpa using congrArg (fun q : F[X] ↦ q.coeff i) hP)
  · right
    have halg : IsAlgebraic F (f z) := by
      refine ⟨P.map g, hP, ?_⟩
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hcomm, ← Polynomial.hom_eval₂]
      exact (hf₀ _).mpr hz
    obtain ⟨c, hc⟩ := hscalar halg
    obtain ⟨r, rfl⟩ := hg c
    refine ⟨r, (hf₀ _).mp ?_⟩
    rw [map_sub, sub_eq_zero, ← hc]
    exact (DFunLike.congr_fun hcomm r).symm

/-- Suppose the residue field and the fiber are obtained via compatible maps
whose kernels are the principal ideals cut out by `p`. A geometric domain fiber
supplies precisely the scalar-residue alternative used in local-slice improvement. -/
theorem fiber_condition_of_geometrically_integral
    {R A F D : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Field F] [CommRing D] [Algebra F D] [IsDomain (AlgebraicClosure F ⊗[F] D)]
    (p : R) (g : R →+* F) (f : A →+* D) (hg : Function.Surjective g)
    (hcomm : f.comp (algebraMap R A) = (algebraMap F D).comp g)
    (hg₀ : ∀ r : R, g r = 0 ↔ p ∣ r)
    (hf₀ : ∀ a : A, f a = 0 ↔ algebraMap R A p ∣ a)
    (z : A) (P : R[X]) (hz : algebraMap R A p ∣ Polynomial.aeval z P) :
    C p ∣ P ∨ ∃ r : R, algebraMap R A p ∣ z - algebraMap R A r :=
  fiber_condition_of_relatively_closed (fun h ↦ scalar_of_geometrically_integral h)
    p g f hg hcomm hg₀ hf₀ z P hz

section FixedRing

variable {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]

/-- Factors of a nonzero member of a factorially closed subring lie in the subring. -/
def FactoriallyClosed (S : Subalgebra k A) : Prop :=
  ∀ x y : A, x * y ≠ 0 → x * y ∈ S → x ∈ S ∧ y ∈ S

theorem fixedRing_factoriallyClosed (φ : A →ₐ[k] A[X])
    (h₀ : ∀ x, (φ x).eval 0 = x) :
    FactoriallyClosed (AlgHom.equalizer φ Polynomial.CAlgHom) := by
  intro a b hne hab
  change φ (a * b) = C (a * b) at hab
  rw [map_mul] at hab
  have φne {x : A} (hx : x ≠ 0) : φ x ≠ 0 := fun e ↦ hx (by simpa [e] using (h₀ x).symm)
  obtain ⟨ha, hb⟩ := mul_ne_zero_iff.mp hne
  have hd := congrArg Polynomial.natDegree hab
  rw [Polynomial.natDegree_mul (φne ha) (φne hb), Polynomial.natDegree_C] at hd
  have fixed (x : A) (hx : (φ x).natDegree = 0) : φ x = C x := by
    have hcoeff : (φ x).coeff 0 = x := (Polynomial.coeff_zero_eq_eval_zero _).trans (h₀ x)
    exact (Polynomial.eq_C_of_natDegree_eq_zero hx).trans (congrArg C hcoeff)
  exact ⟨fixed a (by omega), fixed b (by omega)⟩

namespace FactoriallyClosed

variable {S : Subalgebra k A}

omit [IsDomain A] in
theorem dvd_iff (hS : FactoriallyClosed S) {a b : S} :
    ((a : A) ∣ (b : A)) ↔ a ∣ b := by
  refine ⟨?_, map_dvd S.val⟩
  by_cases hb : b = 0
  · simp [hb]
  rintro ⟨x, hx⟩
  have hn : (b : A) ≠ 0 := fun h ↦ hb (Subtype.ext h)
  have h := hS a x (hx ▸ hn) (hx ▸ b.property)
  exact ⟨⟨x,h.2⟩, Subtype.ext hx⟩

omit [IsDomain A] in
theorem isUnit_iff (hS : FactoriallyClosed S) {a : S} : IsUnit (a : A) ↔ IsUnit a := by
  simpa only [isUnit_iff_dvd_one, Subalgebra.coe_one] using (hS.dvd_iff (a := a) (b := 1))

omit [IsDomain A] in
theorem irreducible_val (hS : FactoriallyClosed S) {a : S} (ha : Irreducible a) :
    Irreducible (a : A) := by
  refine ⟨fun h ↦ ha.not_isUnit (hS.isUnit_iff.mp h), ?_⟩
  intro x y hxy
  have hn : (a : A) ≠ 0 := fun h ↦ ha.ne_zero (Subtype.ext h)
  obtain ⟨hx, hy⟩ := hS x y (hxy ▸ hn) (hxy ▸ a.property)
  have he : a = (⟨x,hx⟩ : S) * ⟨y,hy⟩ := Subtype.ext hxy
  exact (ha.isUnit_or_isUnit he).imp (fun h ↦ h.map S.val) (fun h ↦ h.map S.val)

theorem factorial [UniqueFactorizationMonoid A] (hS : FactoriallyClosed S) :
    UniqueFactorizationMonoid S := by
  have hwf : WfDvdMonoid S := ⟨InvImage.wf Subtype.val wellFounded_dvdNotUnit |>.mono
    (fun {a b} ⟨hn, u, hu, h⟩ ↦ ⟨fun h ↦ hn (Subtype.ext h), u.val,
      fun h ↦ hu (hS.isUnit_iff.mp h), congrArg Subtype.val h⟩)⟩
  refine { irreducible_iff_prime := ⟨fun ha ↦ ?_, fun h ↦ h.irreducible⟩ }
  have hprime := UniqueFactorizationMonoid.irreducible_iff_prime.mp (hS.irreducible_val ha)
  refine ⟨ha.ne_zero, ha.not_isUnit, fun x y h ↦ ?_⟩
  exact (hprime.dvd_or_dvd (hS.dvd_iff.mpr h)).imp hS.dvd_iff.mp hS.dvd_iff.mp

end FactoriallyClosed

/-- A generic generator moved by the action is transcendental over the fixed
ring. Clearing denominators then gives a transcendence basis with one element. -/
theorem trdeg_over_fixedRing (φ : A →ₐ[k] A[X]) (h₀ : ∀ x, (φ x).eval 0 = x)
    {z : A} (hz : z ∉ AlgHom.equalizer φ Polynomial.CAlgHom)
    (hgen : GenericGenerator (R := AlgHom.equalizer φ Polynomial.CAlgHom) z) :
    Algebra.trdeg (AlgHom.equalizer φ Polynomial.CAlgHom) A = 1 := by
  let S := AlgHom.equalizer φ Polynomial.CAlgHom
  have hpos : (φ z).natDegree ≠ 0 := by
    intro h
    exact hz ((Polynomial.eq_C_of_natDegree_eq_zero h).trans
      (congrArg C ((Polynomial.coeff_zero_eq_eval_zero _).trans (h₀ z))))
  have htrans : Transcendental A (φ z) := (φ z).transcendental hpos
    (mem_nonZeroDivisors_of_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr
      (fun h ↦ hpos (by simp [h]))))
  have hcomm : (C : A →+* A[X]).comp (algebraMap S A) =
      φ.toRingHom.comp (algebraMap S A) := RingHom.ext (fun r ↦ r.property.symm)
  have hztr : Transcendental S z := by
    rintro ⟨P, hP, hval⟩
    have h := Polynomial.map_aeval_eq_aeval_map hcomm P z
    rw [hval, map_zero] at h
    exact htrans ⟨_, (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective S A)).mpr hP, h.symm⟩
  let x : Unit → A := fun _ ↦ z
  let T := Algebra.adjoin S (Set.range x)
  have hi : AlgebraicIndependent S x := algebraicIndependent_unique_type_iff.mpr hztr
  have halg : Algebra.IsAlgebraic T A := by
    constructor
    intro a
    obtain ⟨d, hd, hda⟩ := hgen a
    let d' : T := ⟨algebraMap S A d, T.algebraMap_mem d⟩
    have hmem : algebraMap S A d * a ∈ T := by simpa [T, x, Set.range_const] using hda
    let a' : T := ⟨algebraMap S A d * a, hmem⟩
    refine ⟨C d' * X - C a', ?_, ?_⟩
    · intro he
      have he₁ := congrArg (fun P : T[X] ↦ P.coeff 1) he
      have he' : d' = 0 := by simpa using he₁
      exact hd (Subtype.ext (congrArg (fun q : T ↦ (q : A)) he'))
    · simp [d', a']
  have hb := hi.isTranscendenceBasis_iff_isAlgebraic.mpr halg
  apply Cardinal.lift_injective.{0,v}
  simpa [x] using hb.lift_cardinalMk_eq_trdeg.symm

/-- For a nontrivial surface action, the transcendence-degree drop to one
suffices to identify its fixed ring over the original field. -/
theorem fixedRing_isPolynomial [Algebra.FiniteType k A]
    (e : (Plane k)[X] ≃ₐ[k] A[X]) (φ : A →ₐ[k] A[X]) (h₀ : ∀ x, (φ x).eval 0 = x)
    (hd : Algebra.trdeg k (AlgHom.equalizer φ Polynomial.CAlgHom) = 1) :
    Nonempty (k[X] ≃ₐ[k] AlgHom.equalizer φ Polynomial.CAlgHom) := by
  let S := AlgHom.equalizer φ Polynomial.CAlgHom
  have : UniqueFactorizationMonoid A := factorial e
  have : UniqueFactorizationMonoid S := (fixedRing_factoriallyClosed φ h₀).factorial
  let j := (threeVariables e).symm.toAlgHom.comp (Polynomial.CAlgHom.comp S.val)
  exact normal_curve_in_polynomial_ring j
    ((threeVariables e).symm.injective.comp (C_injective.comp Subtype.val_injective)) hd

end FixedRing

/-- Given a polynomial subalgebra of dimension one, one further algebra generator
already gives the desired isomorphism, by the transcendence-degree calculation. -/
noncomputable def equivOfRulingGenerator {B : Type v} [CommRing B] [Algebra k B]
    (e : (Plane k)[X] ≃ₐ[k] B[X]) (S : Subalgebra k B) (u : k[X] ≃ₐ[k] S)
    (z : B) (hz : Algebra.adjoin S ({z} : Set B) = ⊤) : Plane k ≃ₐ[k] B := by
  let coord : Plane k ≃ₐ[k] S[X] := (MvPolynomial.finSuccEquiv k 1).trans
    (Polynomial.mapAlgEquiv ((MvPolynomial.uniqueAlgEquiv k (Fin 1)).trans u))
  let f := ((Polynomial.aeval (R := S) z).restrictScalars k).comp coord.toAlgHom
  have hsurj : Function.Surjective (Polynomial.aeval (R := S) z) := by
    rwa [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval]
  apply equivOfGenerators e (f ∘ MvPolynomial.X)
  rw [Algebra.adjoin_range_eq_range_aeval, ← MvPolynomial.aeval_unique, AlgHom.range_eq_top]
  exact hsurj.comp coord.surjective

/- The coefficient identities and the positive-characteristic binomial argument are
adapted from the Open Math Agents dimension-three positive-characteristic proof.
Here the local slice works uniformly, with the degree-one argument in characteristic zero. -/
noncomputable section

/-- An exponential map (`G_a`-action) on a `K`-algebra `D`. -/
structure ExpMap (K D : Type*) [CommSemiring K] [CommRing D] [Algebra K D] where
  toAlgHom : D →ₐ[K] Polynomial D
  eval_zero : ∀ a : D, (toAlgHom a).eval 0 = a
  coassoc : ∀ a : D,
    Polynomial.map toAlgHom.toRingHom (toAlgHom a) =
    Polynomial.eval₂RingHom (Polynomial.C.comp Polynomial.C)
      (Polynomial.C Polynomial.X + Polynomial.X) (toAlgHom a)

namespace ExpMap

variable {K D : Type*} [CommRing K] [CommRing D] [Algebra K D]

instance : CoeFun (ExpMap K D) (fun _ => D → Polynomial D) := ⟨fun φ => φ.toAlgHom⟩

lemma coeff_zero (φ : ExpMap K D) (a : D) : (φ a).coeff 0 = a := by
  rw [Polynomial.coeff_zero_eq_eval_zero]; exact φ.eval_zero a

lemma injective (φ : ExpMap K D) : Function.Injective φ := by
  intro a b h
  have := congrArg (fun q : Polynomial D => q.coeff 0) h
  simpa [φ.coeff_zero] using this

/-- The fixed ring is the equalizer with the constant-polynomial map. -/
abbrev invSubalg (φ : ExpMap K D) := AlgHom.equalizer φ.toAlgHom Polynomial.CAlgHom

def IsNontrivial (φ : ExpMap K D) : Prop :=
  ∃ a : D, a ∉ φ.invSubalg

lemma mem_invSubalg_iff_natDegree_eq_zero (φ : ExpMap K D) (a : D) :
    a ∈ φ.invSubalg ↔ (φ a).natDegree = 0 := by
  constructor
  · intro ha
    change φ a = Polynomial.C a at ha
    rw [ha, Polynomial.natDegree_C]
  · intro hdeg
    change φ a = Polynomial.C a
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg, φ.coeff_zero]

/-- Key coassociativity coefficient identity:
    `coeff r (φ (coeff i (φ a))) = ((i + r).choose i : D) * coeff (i + r) (φ a)`. -/
lemma coeff_coeff_coassoc (φ : ExpMap K D) (a : D) (i r : ℕ) :
    (φ ((φ a).coeff i)).coeff r = ((i + r).choose i : D) * (φ a).coeff (i + r) := by
  have h := congrArg (fun Q : Polynomial (Polynomial D) => (Q.coeff i).coeff r) (φ.coassoc a)
  rw [Polynomial.coeff_map] at h
  change (φ.toAlgHom.toRingHom ((φ.toAlgHom a).coeff i)).coeff r = _
  rw [h]
  -- Compute coefficient of `X^i` (outer) and `X^r` (inner) in `eval₂ (C ∘ C) (C X + X) P`
  generalize φ a = P
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, Polynomial.coeff_add, mul_add]
    rw [hp, hq]
  | monomial n c =>
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, RingHom.comp_apply]
    rw [add_pow, Finset.mul_sum, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
    have hterm : ∀ k ∈ Finset.range (n + 1),
        (((Polynomial.C (Polynomial.C c) *
          (Polynomial.C Polynomial.X ^ k * Polynomial.X ^ (n - k) *
            (n.choose k : Polynomial (Polynomial D)))).coeff i).coeff r) =
        if k = r ∧ n - k = i then (n.choose i : D) * c else 0 := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have h1 : Polynomial.C (Polynomial.C c) *
          (Polynomial.C Polynomial.X ^ k * Polynomial.X ^ (n - k) *
            (n.choose k : Polynomial (Polynomial D))) =
          Polynomial.C (Polynomial.C (c * (n.choose k : D)) * Polynomial.X ^ k) *
          Polynomial.X ^ (n - k) := by
        simp only [map_mul, map_natCast, Polynomial.C_pow]
        ring
      rw [h1, Polynomial.coeff_C_mul_X_pow]
      by_cases hni : i = n - k
      · rw [if_pos hni, Polynomial.coeff_C_mul_X_pow]
        by_cases hkr : r = k
        · rw [if_pos hkr, if_pos ⟨hkr.symm, hni.symm⟩]
          have hki : n.choose k = n.choose i := by
            rw [hni]; exact (Nat.choose_symm hkn).symm
          rw [hki, mul_comm]
        · rw [if_neg hkr, if_neg (fun h => hkr h.1.symm)]
      · rw [if_neg hni, Polynomial.coeff_zero, if_neg (fun h => hni h.2.symm)]
    rw [Finset.sum_congr rfl hterm]
    rw [Polynomial.coeff_monomial]
    by_cases hnir : n = i + r
    · subst hnir
      rw [if_pos rfl]
      rw [Finset.sum_eq_single r]
      · simp
      · intro k _ hkr
        rw [if_neg (fun h => hkr h.1)]
      · intro hr
        exfalso; apply hr; exact Finset.mem_range.mpr (by omega)
    · rw [if_neg hnir, mul_zero]
      apply Finset.sum_eq_zero
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [if_neg]
      rintro ⟨rfl, hsub⟩
      exact hnir (by omega)

/-- Leading coefficient of `φ a` is always `φ`-invariant. -/
lemma leadingCoeff_mem_invSubalg (φ : ExpMap K D) (a : D) :
    (φ a).leadingCoeff ∈ φ.invSubalg := by
  rw [mem_invSubalg_iff_natDegree_eq_zero]
  by_contra hne
  have hpos : 0 < (φ (φ a).leadingCoeff).natDegree := Nat.pos_of_ne_zero hne
  have hlc : (φ (φ a).leadingCoeff).coeff (φ (φ a).leadingCoeff).natDegree ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr (fun h => by rw [h, Polynomial.natDegree_zero] at hpos; omega)
  have hco := φ.coeff_coeff_coassoc a (φ a).natDegree (φ (φ a).leadingCoeff).natDegree
  rw [Polynomial.coeff_natDegree] at hco
  have h0 : (φ a).coeff ((φ a).natDegree + (φ (φ a).leadingCoeff).natDegree) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  rw [h0, mul_zero] at hco
  exact hlc hco

/-- Elementary char-`p` binomial lemma: if `(d.choose i : D) = 0` for all `0 < i < d`
    in a domain `D` of prime characteristic `p`, then `d = p ^ k` for some `k`. -/
lemma eq_prime_pow_of_choose_eq_zero {p : ℕ} [hp : Fact p.Prime] [IsDomain D] [CharP D p]
    {d : ℕ} (hd : 0 < d) (hchoose : ∀ i, 0 < i → i < d → (d.choose i : D) = 0) :
    ∃ k : ℕ, d = p ^ k := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    by_cases hd1 : d = 1
    · exact ⟨0, by simp [hd1]⟩
    · have hp_dvd : p ∣ d := by
        have h1 : (d.choose 1 : D) = 0 := hchoose 1 (by omega) (by omega)
        rw [Nat.choose_one_right, CharP.cast_eq_zero_iff D p] at h1
        exact h1
      obtain ⟨m, rfl⟩ := hp_dvd
      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | hpos
        · simp at hd
        · exact hpos
      have hm_lt : m < p * m := lt_mul_of_one_lt_left hm_pos hp.out.one_lt
      have hm_choose : ∀ j, 0 < j → j < m → (m.choose j : D) = 0 := by
        intro j hj hjm
        -- Compare coefficient of `X^(p*j)` in `(1 + X)^(p*m) = (1 + X^p)^m` in `D[X]`
        have hpoly : (1 + (Polynomial.X : Polynomial D)) ^ (p * m) =
            (1 + Polynomial.X ^ p) ^ m := by
          rw [pow_mul, add_pow_char (1 : Polynomial D) Polynomial.X p, one_pow]
        have hcoeff := congrArg (fun q : Polynomial D => q.coeff (p * j)) hpoly
        have hlhs : ((1 + (Polynomial.X : Polynomial D)) ^ (p * m)).coeff (p * j) =
            ((p * m).choose (p * j) : D) := by
          rw [add_comm, add_pow, Polynomial.finsetSum_coeff]
          rw [Finset.sum_eq_single (p * j)]
          · simp
          · intro b _ hne
            simp [Polynomial.coeff_X_pow, Ne.symm hne]
          · intro hnm
            exfalso; apply hnm; exact Finset.mem_range.mpr (by nlinarith [hp.out.pos])
        have hrhs : ((1 + (Polynomial.X : Polynomial D) ^ p) ^ m).coeff (p * j) =
            (m.choose j : D) := by
          rw [add_comm, add_pow, Polynomial.finsetSum_coeff]
          rw [Finset.sum_eq_single j]
          · simp [← pow_mul, mul_comm]
          · intro b _ hne
            have hne' : p * b ≠ p * j := fun h => hne (mul_left_cancel₀ hp.out.ne_zero h)
            simp [← pow_mul, Polynomial.coeff_X_pow, Ne.symm hne']
          · intro hnm
            exfalso; apply hnm; exact Finset.mem_range.mpr (by omega)
        rw [hlhs, hrhs] at hcoeff
        have h0 : ((p * m).choose (p * j) : D) = 0 :=
          hchoose (p * j) (by nlinarith [hp.out.pos]) (by nlinarith [hp.out.pos])
        rw [← hcoeff, h0]
      obtain ⟨k, hk⟩ := ih m hm_lt hm_pos hm_choose
      exact ⟨k + 1, by rw [hk, pow_succ']⟩

/-- In characteristic `p`, if `0 < r < p^k` and `n = q * p^k + r`, then `(n.choose r : D) ≠ 0`. -/
lemma choose_mod_prime_pow_ne_zero {p : ℕ} [hp : Fact p.Prime] [IsDomain D] [CharP D p]
    (k q r : ℕ) (hr : r < p ^ k) :
    (((q * p ^ k + r).choose r : ℕ) : D) ≠ 0 := by
  have hpoly : (1 + (Polynomial.X : Polynomial D)) ^ (q * p ^ k + r) =
      (1 + Polynomial.X ^ (p ^ k)) ^ q * (1 + Polynomial.X) ^ r := by
    rw [pow_add, mul_comm q (p ^ k), pow_mul, add_pow_char_pow (1 : Polynomial D) Polynomial.X p k,
      one_pow]
  have hcoeff := congrArg (fun f : Polynomial D => f.coeff r) hpoly
  have hlhs : ((1 + (Polynomial.X : Polynomial D)) ^ (q * p ^ k + r)).coeff r =
      ((q * p ^ k + r).choose r : D) := by
    rw [add_comm, add_pow, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single r]
    · simp
    · intro b _ hne; simp [Polynomial.coeff_X_pow, Ne.symm hne]
    · intro hnm; exfalso; apply hnm; exact Finset.mem_range.mpr (by omega)
  have hrhs : ((1 + (Polynomial.X : Polynomial D) ^ (p ^ k)) ^ q * (1 + Polynomial.X) ^ r).coeff r =
      1 := by
    rw [Polynomial.coeff_mul]
    rw [Finset.sum_eq_single (0, r)]
    · have h0 : ((1 + (Polynomial.X : Polynomial D) ^ (p ^ k)) ^ q).coeff 0 = 1 := by
        rw [Polynomial.coeff_zero_eq_eval_zero]
        simp [zero_pow (pow_ne_zero k hp.out.ne_zero)]
      have hr1 : ((1 + (Polynomial.X : Polynomial D)) ^ r).coeff r = 1 := by
        rw [add_comm, add_pow, Polynomial.finsetSum_coeff]
        rw [Finset.sum_eq_single r]
        · simp
        · intro b _ hne; simp [Polynomial.coeff_X_pow, Ne.symm hne]
        · intro hnm; exfalso; exact hnm (Finset.mem_range.mpr (Nat.lt_succ_self _))
      rw [h0, hr1, mul_one]
    · rintro ⟨a, b⟩ hab hne
      have hab_sum : a + b = r := by simpa using hab
      have ha_pos : 0 < a := by
        by_contra h
        have ha0 : a = 0 := Nat.eq_zero_of_le_zero (not_lt.mp h)
        exact hne (Prod.ext ha0 (by omega))
      have ha_lt : a < p ^ k := by omega
      have hca : ((1 + (Polynomial.X : Polynomial D) ^ (p ^ k)) ^ q).coeff a = 0 := by
        rw [add_comm, add_pow, Polynomial.finsetSum_coeff]
        apply Finset.sum_eq_zero
        intro j _
        have hne' : p ^ k * j ≠ a := by
          rcases Nat.eq_zero_or_pos j with rfl | hj
          · simp; omega
          · have : p ^ k ≤ p ^ k * j := Nat.le_mul_of_pos_right _ hj
            omega
        simp [← pow_mul, Polynomial.coeff_X_pow, Ne.symm hne']
      rw [hca, zero_mul]
    · intro hnm
      exfalso; exact hnm (by simp)
  rw [hlhs, hrhs] at hcoeff
  rw [hcoeff]
  exact one_ne_zero

/-- For any nontrivial exponential map on a domain, there exist `s ∈ D \ D^φ` and `c ∈ D^φ \ {0}` such that
    for every `a ∈ D`, there exists `N : ℕ` with `c ^ N * a ∈ (D^φ)[s]`. -/
lemma exists_local_slice [IsDomain D]
    (φ : ExpMap K D) (hnt : φ.IsNontrivial) :
    ∃ (s : D) (c : φ.invSubalg), (c : D) ≠ 0 ∧ s ∉ φ.invSubalg ∧
      ∀ a : D, ∃ (N : ℕ) (P : Polynomial φ.invSubalg), (c : D) ^ N * a = Polynomial.aeval s P := by
  classical
  have hex : ∃ d : ℕ, 0 < d ∧ ∃ s : D, (φ s).natDegree = d := by
    obtain ⟨a, ha⟩ := hnt
    exact ⟨(φ a).natDegree, Nat.pos_of_ne_zero (mt (φ.mem_invSubalg_iff_natDegree_eq_zero a).mpr ha),
      a, rfl⟩
  let d := Nat.find hex
  have hd_spec := Nat.find_spec hex
  have hd_pos : 0 < d := hd_spec.1
  obtain ⟨s, hs_deg0⟩ := hd_spec.2
  have hs_deg : (φ s).natDegree = d := hs_deg0
  have hd_min : ∀ a : D, 0 < (φ a).natDegree → d ≤ (φ a).natDegree := fun a ha =>
    Nat.find_min' hex ⟨ha, a, rfl⟩
  have hs_ne : φ s ≠ 0 := fun h => by rw [h, Polynomial.natDegree_zero] at hs_deg; omega
  have hchoose : ∀ i, 0 < i → i < d → (d.choose i : D) = 0 := by
    intro i hi hid
    have hcoeff_deg : (φ ((φ s).coeff i)).natDegree = 0 := by
      by_contra hne
      have hpos : 0 < (φ ((φ s).coeff i)).natDegree := Nat.pos_of_ne_zero hne
      have hge : d ≤ (φ ((φ s).coeff i)).natDegree := hd_min _ hpos
      have hco := φ.coeff_coeff_coassoc s i (φ ((φ s).coeff i)).natDegree
      have hlc : (φ ((φ s).coeff i)).coeff (φ ((φ s).coeff i)).natDegree ≠ 0 :=
        Polynomial.leadingCoeff_ne_zero.mpr (fun h => by rw [h, Polynomial.natDegree_zero] at hpos; omega)
      have hgt : d < i + (φ ((φ s).coeff i)).natDegree := by omega
      have h0 : (φ s).coeff (i + (φ ((φ s).coeff i)).natDegree) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [h0, mul_zero] at hco
      exact hlc hco
    have hco := φ.coeff_coeff_coassoc s i (d - i)
    rw [Nat.add_sub_cancel' (le_of_lt hid)] at hco
    have hlhs0 : (φ ((φ s).coeff i)).coeff (d - i) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hlhs0] at hco
    have hslc : (φ s).coeff d ≠ 0 := by
      rw [← hs_deg, Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hs_ne
    exact (mul_eq_zero.mp hco.symm).resolve_right hslc
  have hd_dvd : ∀ a : D, d ∣ (φ a).natDegree := by
    let p := ringChar D
    rcases CharP.char_is_prime_or_zero D p with hp | hp
    · have : Fact p.Prime := ⟨hp⟩
      obtain ⟨k, hk⟩ := eq_prime_pow_of_choose_eq_zero (p := p) (D := D) hd_pos hchoose
      intro a
      by_contra hndvd
      let n := (φ a).natDegree
      let r := n % d
      have hr_pos : 0 < r := Nat.pos_of_ne_zero (fun h => hndvd (Nat.dvd_of_mod_eq_zero h))
      have hr_lt : r < d := Nat.mod_lt n hd_pos
      have hn_eq : n = (n / d) * p ^ k + r := by
        rw [← hk, mul_comm]; exact (Nat.div_add_mod n d).symm
      have hch : ((n.choose r : ℕ) : D) ≠ 0 := by
        rw [hn_eq]; exact choose_mod_prime_pow_ne_zero (p := p) (D := D) k (n / d) r (hr_lt.trans_eq hk)
      have hco := φ.coeff_coeff_coassoc a (n - r) r
      have hsub : n - r + r = n := Nat.sub_add_cancel (by omega)
      rw [hsub] at hco
      have hch' : ((n.choose (n - r) : ℕ) : D) ≠ 0 := by
        rw [Nat.choose_symm (by omega)]; exact hch
      have halc : (φ a).coeff n ≠ 0 := by
        rw [Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr (fun h => by
          exact hndvd (by rw [h, Polynomial.natDegree_zero]; exact dvd_zero d))
      have hne0 : (φ ((φ a).coeff (n - r))).coeff r ≠ 0 := by
        rw [hco]; exact mul_ne_zero hch' halc
      have hdeg_ge : r ≤ (φ ((φ a).coeff (n - r))).natDegree :=
        Polynomial.le_natDegree_of_ne_zero hne0
      have hdeg_le : (φ ((φ a).coeff (n - r))).natDegree ≤ r := by
        by_contra hgt; push Not at hgt
        have hco2 := φ.coeff_coeff_coassoc a (n - r) (φ ((φ a).coeff (n - r))).natDegree
        have h0 : (φ a).coeff (n - r + (φ ((φ a).coeff (n - r))).natDegree) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        rw [h0, mul_zero] at hco2
        have hlc2 : (φ ((φ a).coeff (n - r))).coeff (φ ((φ a).coeff (n - r))).natDegree ≠ 0 :=
          Polynomial.leadingCoeff_ne_zero.mpr (fun h => by rw [h, Polynomial.natDegree_zero] at hgt; omega)
        exact hlc2 hco2
      have hmin := hd_min ((φ a).coeff (n - r)) (by omega)
      omega
    · have : CharP D 0 := hp ▸ inferInstanceAs (CharP D p)
      have : CharZero D := CharP.charP_to_charZero D
      have hd₁ : d = 1 := by
        by_contra hn
        have h := hchoose 1 (by decide) (by omega)
        simp [hd_pos.ne'] at h
      simp [hd₁]
  let c : φ.invSubalg := ⟨(φ s).leadingCoeff, φ.leadingCoeff_mem_invSubalg s⟩
  have hc_ne : (c : D) ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hs_ne
  have hs_not : s ∉ φ.invSubalg := by
    rw [mem_invSubalg_iff_natDegree_eq_zero]; omega
  refine ⟨s, c, hc_ne, hs_not, ?_⟩
  intro a
  generalize hn : (φ a).natDegree = n
  induction n using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    by_cases hn0 : n = 0
    · have ha_inv : a ∈ φ.invSubalg := (φ.mem_invSubalg_iff_natDegree_eq_zero a).mpr (by omega)
      exact ⟨0, Polynomial.C ⟨a, ha_inv⟩, by simp⟩
    · obtain ⟨q, hq⟩ := hd_dvd a
      rw [hn] at hq
      let an : φ.invSubalg := ⟨(φ a).leadingCoeff, φ.leadingCoeff_mem_invSubalg a⟩
      let b : D := (c : D) ^ q * a - (an : D) * s ^ q
      have hb_deg : (φ b).natDegree < n := by
        have hφb : φ b = Polynomial.C ((c : D) ^ q) * φ a -
            Polynomial.C (an : D) * (φ s) ^ q := by
          simp only [b, map_sub, map_mul, map_pow]
          have hc_inv : φ (c : D) = Polynomial.C (c : D) := c.2
          have han_inv : φ (an : D) = Polynomial.C (an : D) := an.2
          rw [hc_inv, han_inv, ← map_pow]
        have hφa_ne : φ a ≠ 0 := fun h => by rw [h, Polynomial.natDegree_zero] at hn; exact hn0 hn.symm
        have h1_deg : (Polynomial.C ((c : D) ^ q) * φ a).natDegree = n := by
          rw [Polynomial.natDegree_C_mul (pow_ne_zero q hc_ne), hn]
        have h2_deg : (Polynomial.C (an : D) * (φ s) ^ q).natDegree = n := by
          have han_ne : (an : D) ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hφa_ne
          rw [Polynomial.natDegree_C_mul han_ne, Polynomial.natDegree_pow, hs_deg, mul_comm, ← hq]
        have hle : (φ b).natDegree ≤ n := by
          rw [hφb]
          exact le_trans (Polynomial.natDegree_sub_le _ _) (max_le (le_of_eq h1_deg) (le_of_eq h2_deg))
        have hcn : (φ b).coeff n = 0 := by
          rw [hφb, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
          have hsq : ((φ s) ^ q).natDegree = n := by
            rw [Polynomial.natDegree_pow, hs_deg, mul_comm, ← hq]
          rw [← hn, Polynomial.coeff_natDegree, hn, ← hsq, Polynomial.coeff_natDegree,
            Polynomial.leadingCoeff_pow]
          change (φ s).leadingCoeff ^ q * (φ a).leadingCoeff -
            (φ a).leadingCoeff * (φ s).leadingCoeff ^ q = 0
          ring
        by_contra hge
        have heq : (φ b).natDegree = n := le_antisymm hle (not_lt.mp hge)
        have hne : (φ b).coeff n ≠ 0 := by
          rw [← heq, Polynomial.coeff_natDegree]
          exact Polynomial.leadingCoeff_ne_zero.mpr (fun h => by rw [h, Polynomial.natDegree_zero] at heq; exact hn0 heq.symm)
        exact hne hcn
      obtain ⟨N, P, hNP⟩ := ih (φ b).natDegree hb_deg b rfl
      refine ⟨N + q, P + Polynomial.C ((c ^ N : φ.invSubalg) * an) * Polynomial.X ^ q, ?_⟩
      simp only [map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
      change (c : D) ^ (N + q) * a =
        Polynomial.aeval s P + (c : D) ^ N * (an : D) * s ^ q
      rw [← hNP]
      simp only [b, pow_add]
      ring

/-- Transport an exponential map along a `K`-algebra isomorphism. -/
def compAlgEquiv {D' : Type*} [CommRing D'] [Algebra K D']
    (e : D ≃ₐ[K] D') (φ : ExpMap K D) : ExpMap K D' where
  toAlgHom := (Polynomial.mapAlgHom e.toAlgHom).comp (φ.toAlgHom.comp e.symm.toAlgHom)
  eval_zero a := by
    change (Polynomial.map e.toRingHom (φ (e.symm a))).eval 0 = a
    rw [Polynomial.eval_map, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero,
      φ.eval_zero]
    exact e.apply_symm_apply a
  coassoc a := by
    have h := congrArg (Polynomial.map (Polynomial.mapRingHom e.toRingHom)) (φ.coassoc (e.symm a))
    simp only [Polynomial.map_map] at h
    have hlhs : Polynomial.map ((Polynomial.mapAlgHom e.toAlgHom).comp
        (φ.toAlgHom.comp e.symm.toAlgHom)).toRingHom
        (Polynomial.map e.toRingHom (φ (e.symm a))) =
        Polynomial.map ((Polynomial.mapRingHom e.toRingHom).comp φ.toAlgHom.toRingHom)
          (φ (e.symm a)) := by
      rw [Polynomial.map_map]
      congr 1; ext x
      simp [e.symm_apply_apply]
    change Polynomial.map ((Polynomial.mapAlgHom e.toAlgHom).comp
        (φ.toAlgHom.comp e.symm.toAlgHom)).toRingHom
        (Polynomial.map e.toRingHom (φ (e.symm a))) =
      Polynomial.eval₂RingHom (Polynomial.C.comp Polynomial.C)
        (Polynomial.C Polynomial.X + Polynomial.X)
        (Polynomial.map e.toRingHom (φ (e.symm a)))
    rw [hlhs, h]
    generalize φ (e.symm a) = P
    induction P using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [Polynomial.map_add, map_add, map_add, Polynomial.map_add, hp, hq]
    | monomial n c =>
      simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, Polynomial.map_monomial,
        RingHom.comp_apply, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add,
        Polynomial.map_C, Polynomial.map_X, Polynomial.coe_mapRingHom]

/-- Coordinate translation exponential map on `MvPolynomial (Fin 3) K`:
    `X i ↦ C (X i) + X` and `X j ↦ C (X j)` for `j ≠ i`. -/
def mvPolyShift (K : Type*) [CommRing K] (i : Fin 3) : ExpMap K (MvPolynomial (Fin 3) K) where
  toAlgHom := MvPolynomial.aeval (fun j =>
    Polynomial.C (MvPolynomial.X j) + if j = i then Polynomial.X else 0)
  eval_zero a := by
    have hcomp : (Polynomial.evalRingHom (0 : MvPolynomial (Fin 3) K)).comp
        (MvPolynomial.aeval (fun j =>
          Polynomial.C (MvPolynomial.X j) + if j = i then Polynomial.X else 0)).toRingHom =
        RingHom.id (MvPolynomial (Fin 3) K) := by
      apply MvPolynomial.ringHom_ext
      · intro c; simp
      · intro j; by_cases hj : j = i <;> simp [hj]
    exact RingHom.congr_fun hcomp a
  coassoc a := by
    let ψ : MvPolynomial (Fin 3) K →ₐ[K] Polynomial (MvPolynomial (Fin 3) K) :=
      MvPolynomial.aeval (fun j =>
        Polynomial.C (MvPolynomial.X j) + if j = i then Polynomial.X else 0)
    let cc : MvPolynomial (Fin 3) K →+*
        Polynomial (Polynomial (MvPolynomial (Fin 3) K)) :=
      Polynomial.C.comp Polynomial.C
    let evVU : Polynomial (MvPolynomial (Fin 3) K) →+*
        Polynomial (Polynomial (MvPolynomial (Fin 3) K)) :=
      Polynomial.eval₂RingHom cc
        ((Polynomial.C Polynomial.X + Polynomial.X :
          Polynomial (Polynomial (MvPolynomial (Fin 3) K))))
    have hcomp : (Polynomial.mapRingHom ψ.toRingHom).comp ψ.toRingHom =
        evVU.comp ψ.toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c; simp [ψ, evVU, cc]
      · intro j
        by_cases hj : j = i
        · subst hj
          simp [ψ, evVU, cc, add_assoc]
        · simp [ψ, evVU, cc, hj]
    exact RingHom.congr_fun hcomp a

/-- Lemma 2.4: If every non-trivial exponential map `φ` on `D` has `D^φ ⊆ S` for some
    proper subalgebra `S < ⊤`, then `D ≇ₐ[K] MvPolynomial (Fin 3) K`. -/
lemma not_algEquiv_mvPoly3_of_invSubalg_le [Nontrivial K]
    (S : Subalgebra K D) (hS : S ≠ ⊤)
    (hinv : ∀ φ : ExpMap K D, φ.IsNontrivial → φ.invSubalg ≤ S) :
    ¬ Nonempty (D ≃ₐ[K] MvPolynomial (Fin 3) K) := by
  rintro ⟨e⟩
  apply hS
  rw [eq_top_iff]
  intro a _
  have hgen : ∀ j : Fin 3, e.symm (MvPolynomial.X j) ∈ S := by
    intro j
    -- Pick `i ≠ j`
    obtain ⟨i, hij⟩ : ∃ i : Fin 3, j ≠ i := by
      fin_cases j
      · exact ⟨1, by decide⟩
      · exact ⟨0, by decide⟩
      · exact ⟨0, by decide⟩
    let φ0 := mvPolyShift K i
    let φ := φ0.compAlgEquiv e.symm
    have hnt : φ.IsNontrivial := by
      refine ⟨e.symm (MvPolynomial.X i), ?_⟩
      intro hmem
      change φ (e.symm (MvPolynomial.X i)) = Polynomial.C (e.symm (MvPolynomial.X i)) at hmem
      have h1 : φ (e.symm (MvPolynomial.X i)) =
          Polynomial.C (e.symm (MvPolynomial.X i)) + Polynomial.X := by
        simp [φ, compAlgEquiv, φ0, mvPolyShift]
      rw [h1] at hmem
      have hX0 : (Polynomial.X : Polynomial D) = 0 := add_left_cancel (hmem.trans (add_zero _).symm)
      have h10 := congrArg (fun q : Polynomial D => q.coeff 1) hX0
      simp at h10
      have : Nontrivial D := e.symm.injective.nontrivial
      exact one_ne_zero h10
    have hj_mem : e.symm (MvPolynomial.X j) ∈ φ.invSubalg := by
      change φ (e.symm (MvPolynomial.X j)) = Polynomial.C (e.symm (MvPolynomial.X j))
      simp [φ, compAlgEquiv, φ0, mvPolyShift, hij]
    exact hinv φ hnt hj_mem
  have ha_eq : a = e.symm (e a) := (e.symm_apply_apply a).symm
  rw [ha_eq]
  generalize e a = P
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
    exact S.algebraMap_mem c
  | add p q hp hq =>
    rw [map_add]; exact S.add_mem hp hq
  | mul_X p j hp =>
    rw [map_mul]; exact S.mul_mem hp (hgen j)


end ExpMap
end

noncomputable section

/-- Helper algebra hom for `ExpMap.quotient`. -/
def ExpMap.quotientAlgHom {K D : Type*} [CommRing K] [CommRing D] [Algebra K D]
    (φ : ExpMap K D) (f : D) (hf : f ∈ φ.invSubalg) :
    (D ⧸ Ideal.span ({f} : Set D)) →ₐ[K] Polynomial (D ⧸ Ideal.span ({f} : Set D)) :=
  let I := Ideal.span ({f} : Set D)
  let mk := Ideal.Quotient.mkₐ K I
  Ideal.Quotient.liftₐ I ((Polynomial.mapAlgHom mk).comp φ.toAlgHom) (fun a ha => by
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨q, rfl⟩ := ha
    have hf' : φ f = Polynomial.C f := hf
    change Polynomial.map (Ideal.Quotient.mk I) (φ (f * q)) = 0
    rw [map_mul, hf', Polynomial.map_mul, Polynomial.map_C]
    have hmkf : Ideal.Quotient.mk I f = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    rw [hmkf, map_zero, zero_mul])

/-- Pushing an exponential map `φ` on `D` down to a quotient `D ⧸ I` when `I` is generated by
    a `φ`-invariant element `f ∈ D^φ`. -/
def ExpMap.quotient {K D : Type*} [CommRing K] [CommRing D] [Algebra K D]
    (φ : ExpMap K D) (f : D) (hf : f ∈ φ.invSubalg) :
    ExpMap K (D ⧸ Ideal.span ({f} : Set D)) where
  toAlgHom := φ.quotientAlgHom f hf
  eval_zero x := by
    let I := Ideal.span ({f} : Set D)
    refine Submodule.Quotient.induction_on I x fun d => ?_
    change (Polynomial.map (Ideal.Quotient.mk I) (φ d)).eval 0 = Ideal.Quotient.mk I d
    rw [Polynomial.eval_map, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero,
      φ.eval_zero]
  coassoc x := by
    let I := Ideal.span ({f} : Set D)
    refine Submodule.Quotient.induction_on I x fun d => ?_
    let mk := Ideal.Quotient.mk I
    let ψ := φ.quotientAlgHom f hf
    change Polynomial.map ψ.toRingHom (Polynomial.map mk (φ d)) =
      Polynomial.eval₂RingHom (Polynomial.C.comp Polynomial.C)
        (Polynomial.C Polynomial.X + Polynomial.X) (Polynomial.map mk (φ d))
    rw [Polynomial.map_map]
    have hcomp : ψ.toRingHom.comp mk = (Polynomial.mapRingHom mk).comp φ.toAlgHom.toRingHom := by
      ext r; rfl
    rw [hcomp, ← Polynomial.map_map, φ.coassoc d]
    generalize φ d = P
    induction P using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [Polynomial.map_add, map_add, map_add, Polynomial.map_add, hp, hq]
    | monomial n c =>
      simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, Polynomial.map_monomial,
        RingHom.comp_apply, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add,
        Polynomial.map_C, Polynomial.map_X, Polynomial.coe_mapRingHom]

end

/-- One of the coordinate translations on the three-dimensional cylinder fixes
a polynomial of positive degree in the cylinder variable. -/
theorem cylinder_action_with_nonconstant_invariant {B : Type v} [CommRing B] [Algebra k B]
    (e : (Plane k)[X] ≃ₐ[k] B[X]) :
    ∃ φ : ExpMap k B[X], φ.IsNontrivial ∧ ∃ f ∈ φ.invSubalg, 0 < f.natDegree := by
  let := isDomain e
  let S := (Polynomial.CAlgHom (R := k) (A := B)).range
  have hS : S ≠ ⊤ := by
    intro h
    have hx : (X : B[X]) ∈ S := by rw [h]; trivial
    obtain ⟨b, hb⟩ := hx
    have hd := congrArg Polynomial.natDegree hb
    change (C b).natDegree = (X : B[X]).natDegree at hd
    simp at hd
  by_contra! H
  refine ExpMap.not_algEquiv_mvPoly3_of_invSubalg_le S hS (fun φ hφ f hf ↦ ?_)
    ⟨(threeVariables e).symm⟩
  exact ⟨_, (Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero (H φ hφ f hf))).symm⟩

theorem ExpMap.isNontrivial_compAlgEquiv {A B : Type*} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] {φ : ExpMap k A} (hφ : φ.IsNontrivial) (e : A ≃ₐ[k] B) :
    (φ.compAlgEquiv e).IsNontrivial := by
  obtain ⟨x, hx⟩ := hφ
  refine ⟨e x, fun h ↦ hx ?_⟩
  change (φ.compAlgEquiv e) (e x) = C (e x) at h
  change φ x = C x
  apply Polynomial.map_injective e.toRingHom e.injective
  simpa [ExpMap.compAlgEquiv] using h

/-- A nontrivial action fixing the cylinder variable restricts to a nontrivial
action on some scalar fiber when the field is infinite. -/
theorem action_of_fixed_cylinder_variable [Infinite k]
    {B : Type v} [CommRing B] [Algebra k B] [IsDomain B]
    (φ : ExpMap k B[X]) (hφ : φ.IsNontrivial) (hX : X ∈ φ.invSubalg) :
    ∃ ψ : ExpMap k B, ψ.IsNontrivial := by
  classical
  have hmoved : ∃ b : B, φ (C b) ≠ C (C b) := by
    by_contra! h
    have hid : φ.toAlgHom = Polynomial.CAlgHom :=
      Polynomial.algHom_ext' (AlgHom.ext h) hX
    obtain ⟨p, hp⟩ := hφ
    exact hp (DFunLike.congr_fun hid p)
  obtain ⟨b, hb⟩ := hmoved
  let diff := φ (C b) - C (C b)
  have hd : diff ≠ 0 := sub_ne_zero.mpr hb
  obtain ⟨i, hi⟩ : ∃ i, diff.coeff i ≠ 0 := by
    by_contra! h
    exact hd (Polynomial.ext (by simpa using h))
  have hev : ∃ c : k, (diff.coeff i).eval (algebraMap k B c) ≠ 0 := by
    by_contra! h
    apply hi
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.infinite_range_of_injective (RingHom.injective (algebraMap k B))).mono
    rintro _ ⟨c, rfl⟩
    exact h c
  obtain ⟨c, hc⟩ := hev
  let r := algebraMap k B c
  let q : B[X] := X - C r
  have hq : q ∈ φ.invSubalg :=
    φ.invSubalg.sub_mem hX (φ.invSubalg.algebraMap_mem c)
  let I := Ideal.span {q}
  let mk := Ideal.Quotient.mk I
  let ψ := φ.quotient q hq
  have hψ : ψ.IsNontrivial := by
    refine ⟨mk (C b), fun he ↦ hc ?_⟩
    change (φ (C b)).map mk = C (mk (C b)) at he
    have hmap : diff.map mk = 0 := by simpa [diff] using sub_eq_zero.mpr he
    have hcoeff : mk (diff.coeff i) = 0 := by
      simpa using congrArg (fun P ↦ Polynomial.coeff P i) hmap
    have hdiv := Ideal.mem_span_singleton.mp ((Ideal.Quotient.eq_zero_iff_mem).mp hcoeff)
    exact Polynomial.dvd_iff_isRoot.mp hdiv
  let e := (Polynomial.quotientSpanXSubCAlgEquiv r).restrictScalars k
  exact ⟨ψ.compAlgEquiv e, ExpMap.isNontrivial_compAlgEquiv hψ e⟩

theorem ExpMap.exists_genericGenerator {B : Type v} [CommRing B] [Algebra k B] [IsDomain B]
    (ψ : ExpMap k B) (hψ : ψ.IsNontrivial) :
    ∃ z : B, z ∉ ψ.invSubalg ∧ GenericGenerator (R := ψ.invSubalg) z := by
  obtain ⟨z, d, hd, hz, hden⟩ := ψ.exists_local_slice hψ
  refine ⟨z, hz, fun b ↦ ?_⟩
  obtain ⟨n, P, hP⟩ := hden b
  refine ⟨d ^ n, pow_ne_zero _ (fun h ↦ hd (congrArg Subtype.val h)), ?_⟩
  change (d : B) ^ n * b ∈ Algebra.adjoin ψ.invSubalg {z}
  rw [hP]
  exact Polynomial.aeval_mem_adjoin_singleton ψ.invSubalg z

theorem ExpMap.fixedRing_isPolynomial_of_nontrivial
    {B : Type v} [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (e : (Plane k)[X] ≃ₐ[k] B[X]) (ψ : ExpMap k B) (hψ : ψ.IsNontrivial) :
    Nonempty (k[X] ≃ₐ[k] ψ.invSubalg) := by
  let := isDomain e
  obtain ⟨z, hz, hgen⟩ := ψ.exists_genericGenerator hψ
  have hrel := trdeg_over_fixedRing ψ.toAlgHom ψ.eval_zero hz hgen
  apply fixedRing_isPolynomial e ψ.toAlgHom ψ.eval_zero
  apply Cardinal.add_one_inj.mp
  rw [show (1 + 1 : Cardinal.{v}) = 2 by norm_num, ← hrel, trdeg_add_eq, trdeg e]

/-- A polynomial presentation of the fixed ring transports to the equalizer after
every field extension. This also applies to inseparable extensions. -/
noncomputable def ExpMap.fixedRingBaseChange {B : Type v} [CommRing B] [Algebra k B]
    (ψ : ExpMap k B) (u : k[X] ≃ₐ[k] ψ.invSubalg) (K : Type w) [Field K] [Algebra k K] :
    K[X] ≃ₐ[K] AlgHom.equalizer
      (Algebra.TensorProduct.map (AlgHom.id K K) ψ.toAlgHom)
      (Algebra.TensorProduct.map (AlgHom.id K K) Polynomial.CAlgHom) :=
  (polyEquivTensor' k K).trans ((Algebra.TensorProduct.congr AlgEquiv.refl u).trans
    (AlgHom.tensorEqualizerEquiv K K ψ.toAlgHom Polynomial.CAlgHom))

/-- The surface inputs expressed over the ground field: a nontrivial exponential map whose
fixed ring has relatively algebraically closed residue fields in the fibers. Both are
established for every cylinder in `hasRuling_of_action` and `exists_action` below. -/
def HasRuling (k B : Type*) [Field k] [CommRing B] [Algebra k B] : Prop :=
  ∃ φ : ExpMap k B, φ.IsNontrivial ∧
    let S := φ.invSubalg
    ∀ p : S, Prime p → ∀ (z : B) (P : S[X]), algebraMap S B p ∣ Polynomial.aeval z P →
        C p ∣ P ∨ ∃ r : S, algebraMap S B p ∣ z - algebraMap S B r

theorem plane_of_ruling {B : Type v} [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (e : (Plane k)[X] ≃ₐ[k] B[X]) (h : HasRuling k B) : Nonempty (Plane k ≃ₐ[k] B) := by
  let := isDomain e
  obtain ⟨ψ, hψ, hfiber⟩ := h
  let φ := ψ.toAlgHom
  have h₀ := ψ.eval_zero
  let S := AlgHom.equalizer φ Polynomial.CAlgHom
  obtain ⟨z, hz, hgen⟩ := ψ.exists_genericGenerator hψ
  have hlc := ψ.leadingCoeff_mem_invSubalg z
  obtain ⟨u⟩ := ψ.fixedRing_isPolynomial_of_nontrivial e hψ
  have : UniqueFactorizationMonoid B := factorial e
  have hS := fixedRing_factoriallyClosed φ h₀
  have : UniqueFactorizationMonoid S := hS.factorial
  let φ' : B →ₐ[S] B[X] := ⟨φ.toRingHom, fun s ↦ s.property⟩
  let n := (φ z).natDegree
  have hn : n ≠ 0 := by
    intro h
    exact hz ((Polynomial.eq_C_of_natDegree_eq_zero h).trans
      (congrArg C ((Polynomial.coeff_zero_eq_eval_zero _).trans (h₀ z))))
  let D := ((Polynomial.lcoeff B n).restrictScalars S).comp φ'.toLinearMap
  have hD₁ : D 1 = 0 := by
    change (φ 1).coeff n = 0
    simp [Polynomial.coeff_one, hn]
  let c : S := ⟨(φ z).leadingCoeff, hlc⟩
  have hc : c ≠ 0 := fun h ↦ hn (by
    have hz₀ : φ z = 0 := Polynomial.leadingCoeff_eq_zero.mp (congrArg Subtype.val h)
    simp [n, hz₀])
  have hDz : D z = algebraMap S B c := Polynomial.coeff_natDegree
  obtain ⟨w, hw⟩ := exists_generator_of_fiber_condition D hD₁ ⟨c, z, hc, hDz, hgen⟩
    (fun _ _ _ ↦ hS.dvd_iff.mp) hfiber
  exact ⟨equivOfRulingGenerator e S u w hw⟩

/-- Over an algebraically closed field, nontriviality of the action alone supplies
the fiber condition. The quotient by a prime of the fixed ring remains a domain
and the residue field of the fixed ring is the ground field. -/
theorem plane_of_action_of_isAlgClosed [IsAlgClosed k]
    {B : Type v} [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (e : (Plane k)[X] ≃ₐ[k] B[X]) (ψ : ExpMap k B) (hψ : ψ.IsNontrivial) :
    Nonempty (Plane k ≃ₐ[k] B) := by
  let := isDomain e
  have : UniqueFactorizationMonoid B := factorial e
  let S := ψ.invSubalg
  obtain ⟨u⟩ := ψ.fixedRing_isPolynomial_of_nontrivial e hψ
  have hS := fixedRing_factoriallyClosed ψ.toAlgHom ψ.eval_zero
  apply plane_of_ruling e
  refine ⟨ψ, hψ, fun p hp z P hz ↦ ?_⟩
  have hq : Irreducible (u.symm p) := (MulEquiv.irreducible_iff u.symm).mpr hp.irreducible
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root _ (Polynomial.degree_pos_of_irreducible hq).ne'
  have assoc := (Polynomial.irreducible_X_sub_C a).associated_of_dvd hq
    (Polynomial.dvd_iff_isRoot.mpr ha)
  let g : S →ₐ[k] k := (Polynomial.aeval a).comp u.symm.toAlgHom
  have hg₀ (r : S) : g r = 0 ↔ p ∣ r := by
    change (u.symm r).IsRoot a ↔ _
    rw [← Polynomial.dvd_iff_isRoot, assoc.dvd_iff_dvd_left]
    exact ⟨fun h ↦ by simpa using map_dvd u h, map_dvd u.symm⟩
  let J := Ideal.span {(p : B)}
  have : J.IsPrime := Ideal.isPrime_span_singleton_of_prime
    (hS.irreducible_val hp.irreducible).prime
  let f := Ideal.Quotient.mkₐ k J
  have hf₀ (b : B) : f b = 0 ↔ (p : B) ∣ b := by
    change Ideal.Quotient.mk J b = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have hcomm : f.toRingHom.comp (algebraMap S B) = (algebraMap k (B ⧸ J)).comp g.toRingHom := by
    ext r
    have hdvd : p ∣ r - algebraMap k S (g r) := (hg₀ _).mp (by simp)
    have h0 := (hf₀ ((r : B) - algebraMap k B (g r))).mpr (map_dvd S.val hdvd)
    exact sub_eq_zero.mp (by simpa using h0)
  exact fiber_condition_of_relatively_closed (fun h ↦ scalar_of_algClosed_algebraic h)
    p g.toRingHom f.toRingHom (fun c ↦ ⟨algebraMap k S c, g.commutes c⟩)
    hcomm hg₀ hf₀ z P hz

/-- For the algebraically closed case, it is enough to homogenize a single
cylinder action while preserving the leading term of its chosen invariant.
Factorial closure then fixes `X`, so a scalar fiber has a nontrivial action. -/
theorem plane_of_homogenization_of_isAlgClosed [IsAlgClosed k]
    {B : Type v} [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (e : (Plane k)[X] ≃ₐ[k] B[X])
    (homogenize : ∀ φ : ExpMap k B[X], φ.IsNontrivial → ∀ f ∈ φ.invSubalg, 0 < f.natDegree →
      ∃ ψ : ExpMap k B[X], ψ.IsNontrivial ∧ C f.leadingCoeff * X ^ f.natDegree ∈ ψ.invSubalg) :
    Nonempty (Plane k ≃ₐ[k] B) := by
  let := isDomain e
  obtain ⟨φ, hφ, f, hf, hdeg⟩ := cylinder_action_with_nonconstant_invariant e
  obtain ⟨ψ, hψ, hlead⟩ := homogenize φ hφ f hf hdeg
  have hfac := fixedRing_factoriallyClosed ψ.toAlgHom ψ.eval_zero
  have hfn : f ≠ 0 := by intro h; simp [h] at hdeg
  have hcn : C f.leadingCoeff ≠ 0 := by simpa using Polynomial.leadingCoeff_ne_zero.mpr hfn
  have hpow := (hfac _ _ (mul_ne_zero hcn (pow_ne_zero _ X_ne_zero)) hlead).2
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hdeg.ne'
  rw [hm, pow_succ] at hpow
  have hX := (hfac _ _ (mul_ne_zero (pow_ne_zero m X_ne_zero) X_ne_zero) hpow).2
  obtain ⟨τ, hτ⟩ := action_of_fixed_cylinder_variable ψ hψ hX
  exact plane_of_action_of_isAlgClosed e τ hτ

/-- The assertion for the cylinder, with independent universes for the field
and the affine algebra. It is proved as `cylinderHasRuling` below. -/
def CylinderHasRuling : Prop :=
  ∀ {k : Type u} [Field k] {B : Type v} [CommRing B] [Algebra k B] [Algebra.FiniteType k B],
    ((Plane k)[X] ≃ₐ[k] B[X]) → HasRuling k B

theorem cancellation_of_ruling (h : CylinderHasRuling.{u,v}) :
    ∀ {k : Type u} [Field k],
      Arxiv.«2208.14736».IsCancellative.{u,u,v} k (MvPolynomial (Fin 2) k) := by
  intro k _ B _ _ _ ⟨e⟩
  exact plane_of_ruling e (h e)

/-- Only the conclusion of this conditional bridge is the FC100 target. -/
example (h : CylinderHasRuling.{u,v}) :
    type_of% @Arxiv.«2208.14736».zariski_cancellation_problem.variants.dim_two.{u,v} :=
  @cancellation_of_ruling.{u,v} h

/- ### Weighted parts of one- and two-variable polynomials -/

noncomputable section Weighted

variable {R : Type*} [CommRing R] (Q : ℕ) (P : ℤ)

/-- Every exponent `n` occurring in `g` satisfies `Q * n ≤ μ`. -/
def WBound (μ : ℤ) (g : R[X]) : Prop := ∀ n, g.coeff n ≠ 0 → (Q : ℤ) * n ≤ μ

/-- The part of `g` supported on the exponents `n` with `Q * n = μ`. -/
def wpart (μ : ℤ) (g : R[X]) : R[X] :=
  ∑ n ∈ g.support, if (Q : ℤ) * n = μ then monomial n (g.coeff n) else 0

lemma coeff_wpart (μ : ℤ) (g : R[X]) (n : ℕ) :
    (wpart Q μ g).coeff n = if (Q : ℤ) * n = μ then g.coeff n else 0 := by
  classical
  unfold wpart
  rw [finsetSum_coeff]
  have h : ∀ b ∈ g.support,
      (if (Q : ℤ) * b = μ then monomial b (g.coeff b) else 0 : R[X]).coeff n =
        if b = n then (if (Q : ℤ) * n = μ then g.coeff n else 0) else 0 := by
    intro b _
    by_cases hb : b = n
    · subst hb
      by_cases hq : (Q : ℤ) * b = μ <;> simp [hq]
    · by_cases hq : (Q : ℤ) * b = μ <;> simp [hq, hb, coeff_monomial]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq']
  by_cases hn : n ∈ g.support
  · simp [hn]
  · have h0 : g.coeff n = 0 := notMem_support_iff.mp hn
    simp [h0]

lemma wpart_zero (μ : ℤ) : wpart Q μ (0 : R[X]) = 0 := by simp [wpart]

lemma wpart_add (μ : ℤ) (g h : R[X]) : wpart Q μ (g + h) = wpart Q μ g + wpart Q μ h := by
  ext n
  simp only [coeff_wpart, coeff_add]
  split_ifs <;> simp

/-- `wpart` as an additive map. -/
def wpartHom (μ : ℤ) : R[X] →+ R[X] where
  toFun := wpart Q μ
  map_zero' := wpart_zero Q μ
  map_add' := wpart_add Q μ

lemma wpartHom_apply (μ : ℤ) (g : R[X]) : wpartHom Q μ g = wpart Q μ g := rfl

lemma wpart_natCast_mul (μ : ℤ) (c : ℕ) (g : R[X]) :
    wpart Q μ ((c : R[X]) * g) = (c : R[X]) * wpart Q μ g := by
  ext n
  simp only [coeff_wpart, coeff_natCast_mul]
  split_ifs <;> simp

lemma wpart_C (r : R) : wpart Q 0 (C r) = C r := by
  ext n
  rw [coeff_wpart, coeff_C]
  by_cases hn : n = 0 <;> simp [hn]

lemma wpart_monomial (n : ℕ) (r : R) :
    wpart Q ((Q : ℤ) * n) (monomial n r) = monomial n r := by
  ext m
  rw [coeff_wpart, coeff_monomial]
  by_cases h : n = m
  · subst h; simp
  · simp [h]

lemma wpart_eq_monomial (hQ : 0 < Q) (μ : ℤ) (g : R[X]) :
    ∃ (n : ℕ) (β : R), wpart Q μ g = monomial n β := by
  have hQ' : (Q : ℤ) ≠ 0 := by exact_mod_cast hQ.ne'
  by_cases h : ∃ n : ℕ, (Q : ℤ) * n = μ
  · obtain ⟨n, hn⟩ := h
    refine ⟨n, g.coeff n, ?_⟩
    ext m
    rw [coeff_wpart, coeff_monomial]
    by_cases hm : n = m
    · subst hm; simp [hn]
    · have hne : (Q : ℤ) * m ≠ μ := by
        rw [← hn]
        intro h'
        exact hm (by exact_mod_cast (mul_left_cancel₀ hQ' h').symm)
      simp [hm, hne]
  · refine ⟨0, 0, ?_⟩
    ext m
    rw [coeff_wpart, if_neg (fun h' => h ⟨m, h'⟩)]
    simp

lemma wpart_natDegree (hQ : 0 < Q) (f : R[X]) :
    wpart Q ((Q : ℤ) * f.natDegree) f = C f.leadingCoeff * X ^ f.natDegree := by
  have hQ' : (Q : ℤ) ≠ 0 := by exact_mod_cast hQ.ne'
  rw [C_mul_X_pow_eq_monomial]
  ext n
  rw [coeff_wpart, coeff_monomial]
  by_cases hn : f.natDegree = n
  · subst hn; simp
  · have hne : (Q : ℤ) * n ≠ Q * f.natDegree := by
      intro h'
      exact hn (by exact_mod_cast (mul_left_cancel₀ hQ' h').symm)
    simp [hn, hne]

variable {Q}

lemma WBound.mono {μ μ' : ℤ} {g : R[X]} (h : WBound Q μ g) (hμ : μ ≤ μ') : WBound Q μ' g :=
  fun n hn => (h n hn).trans hμ

lemma WBound.add {μ : ℤ} {g h : R[X]} (hg : WBound Q μ g) (hh : WBound Q μ h) :
    WBound Q μ (g + h) := by
  intro n hn
  rw [coeff_add] at hn
  by_cases h0 : g.coeff n = 0
  · rw [h0, zero_add] at hn
    exact hh n hn
  · exact hg n h0

lemma WBound.mul {μ₁ μ₂ : ℤ} {g₁ g₂ : R[X]} (h₁ : WBound Q μ₁ g₁) (h₂ : WBound Q μ₂ g₂) :
    WBound Q (μ₁ + μ₂) (g₁ * g₂) := by
  intro n hn
  rw [coeff_mul] at hn
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hx' : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have e₁ := h₁ _ (left_ne_zero_of_mul hne)
  have e₂ := h₂ _ (right_ne_zero_of_mul hne)
  rw [← hx']
  push_cast
  linarith

variable (Q)

lemma WBound.zero (μ : ℤ) : WBound Q μ (0 : R[X]) := fun n hn => absurd (coeff_zero n) hn

lemma WBound.sum {ι : Type*} (s : Finset ι) (f : ι → R[X]) {μ : ℤ}
    (h : ∀ a ∈ s, WBound Q μ (f a)) : WBound Q μ (∑ a ∈ s, f a) :=
  Finset.sum_induction f (WBound Q μ) (fun _ _ ha hb => ha.add hb) (WBound.zero Q μ) h

lemma WBound.monomial (n : ℕ) (r : R) : WBound Q ((Q : ℤ) * n) (monomial n r) := by
  intro m hm
  rw [coeff_monomial] at hm
  by_cases h : n = m
  · rw [h]
  · rw [if_neg h] at hm
    exact absurd rfl hm

lemma WBound.C (r : R) : WBound Q 0 (C r) := by
  simpa using WBound.monomial Q 0 r

lemma WBound.of_natDegree_le {g : R[X]} {d : ℕ} (h : g.natDegree ≤ d) :
    WBound Q ((Q : ℤ) * d) g := by
  intro n hn
  have hnd : n ≤ d := (le_natDegree_of_ne_zero hn).trans h
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hnd) (by positivity)

lemma wpart_eq_zero {μ μ' : ℤ} {g : R[X]} (hg : WBound Q μ' g) (h : μ' < μ) :
    wpart Q μ g = 0 := by
  ext n
  rw [coeff_wpart, coeff_zero]
  by_cases hn : (Q : ℤ) * n = μ
  · rw [if_pos hn]
    by_contra hne
    have := hg n hne
    linarith
  · rw [if_neg hn]

lemma wpart_mul {μ₁ μ₂ : ℤ} {g₁ g₂ : R[X]} (h₁ : WBound Q μ₁ g₁) (h₂ : WBound Q μ₂ g₂) :
    wpart Q (μ₁ + μ₂) (g₁ * g₂) = wpart Q μ₁ g₁ * wpart Q μ₂ g₂ := by
  ext n
  rw [coeff_wpart, coeff_mul, coeff_mul]
  by_cases hn : (Q : ℤ) * n = μ₁ + μ₂
  · rw [if_pos hn]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    rw [coeff_wpart, coeff_wpart]
    by_cases ha : g₁.coeff x.1 = 0
    · simp [ha]
    by_cases hb : g₂.coeff x.2 = 0
    · simp [hb]
    have e₁ := h₁ _ ha
    have e₂ := h₂ _ hb
    have hsum : (Q : ℤ) * x.1 + (Q : ℤ) * x.2 = μ₁ + μ₂ := by
      rw [← hn, ← hx']
      push_cast
      ring
    rw [if_pos (by linarith), if_pos (by linarith)]
  · rw [if_neg hn]
    symm
    refine Finset.sum_eq_zero fun x hx => ?_
    have hx' : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    rw [coeff_wpart, coeff_wpart]
    by_cases ha : (Q : ℤ) * x.1 = μ₁
    · by_cases hb : (Q : ℤ) * x.2 = μ₂
      · exfalso
        apply hn
        rw [← hx', ← ha, ← hb]
        push_cast
        ring
      · simp [hb]
    · simp [ha]

/-- Weighted bound for two-variable polynomials: the outer variable has weight `-P`. -/
def WLe (m : ℤ) (x : R[X][X]) : Prop := ∀ i : ℕ, WBound Q (m + (i : ℤ) * P) (x.coeff i)

/-- The part of a two-variable polynomial of weight exactly `m`. -/
def wtop (m : ℤ) (x : R[X][X]) : R[X][X] :=
  ∑ i ∈ x.support, monomial i (wpart Q (m + (i : ℤ) * P) (x.coeff i))

lemma coeff_wtop (m : ℤ) (x : R[X][X]) (i : ℕ) :
    (wtop Q P m x).coeff i = wpart Q (m + (i : ℤ) * P) (x.coeff i) := by
  classical
  unfold wtop
  rw [finsetSum_coeff]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases hi : i ∈ x.support
  · rw [if_pos hi]
  · rw [if_neg hi, notMem_support_iff.mp hi, wpart_zero]

lemma wtop_zero (m : ℤ) : wtop Q P m (0 : R[X][X]) = 0 := by simp [wtop]

lemma wtop_add (m : ℤ) (x y : R[X][X]) :
    wtop Q P m (x + y) = wtop Q P m x + wtop Q P m y := by
  ext i : 1
  simp only [coeff_wtop, coeff_add, wpart_add]

/-- `wtop` as an additive map. -/
def wtopHom (m : ℤ) : R[X][X] →+ R[X][X] where
  toFun := wtop Q P m
  map_zero' := wtop_zero Q P m
  map_add' := wtop_add Q P m

lemma wtopHom_apply (m : ℤ) (x : R[X][X]) : wtopHom Q P m x = wtop Q P m x := rfl

lemma wtop_C (m : ℤ) (g : R[X]) : wtop Q P m (C g) = C (wpart Q m g) := by
  ext i : 1
  rw [coeff_wtop, coeff_C, coeff_C]
  by_cases hi : i = 0
  · subst hi; simp
  · rw [if_neg hi, if_neg hi, wpart_zero]

variable {Q P}

lemma WLe.mono {m m' : ℤ} {x : R[X][X]} (h : WLe Q P m x) (hm : m ≤ m') : WLe Q P m' x :=
  fun i => (h i).mono (by linarith)

lemma WLe.add {m : ℤ} {x y : R[X][X]} (hx : WLe Q P m x) (hy : WLe Q P m y) :
    WLe Q P m (x + y) := fun i => by
  rw [coeff_add]
  exact (hx i).add (hy i)

lemma WLe.mul {m₁ m₂ : ℤ} {x y : R[X][X]} (hx : WLe Q P m₁ x) (hy : WLe Q P m₂ y) :
    WLe Q P (m₁ + m₂) (x * y) := by
  intro i
  rw [coeff_mul]
  refine WBound.sum Q _ _ fun ab hab => ?_
  have hab' : ab.1 + ab.2 = i := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  have h := (hx ab.1).mul (hy ab.2)
  have he : m₁ + m₂ + (i : ℤ) * P = m₁ + (ab.1 : ℤ) * P + (m₂ + (ab.2 : ℤ) * P) := by
    rw [← hab']
    push_cast
    ring
  rw [he]
  exact h

variable (Q P)

lemma WLe.zero (m : ℤ) : WLe Q P m (0 : R[X][X]) := fun i => by
  rw [coeff_zero]
  exact WBound.zero Q _

lemma WLe.sum {ι : Type*} (s : Finset ι) (f : ι → R[X][X]) {m : ℤ}
    (h : ∀ a ∈ s, WLe Q P m (f a)) : WLe Q P m (∑ a ∈ s, f a) :=
  Finset.sum_induction f (WLe Q P m) (fun _ _ ha hb => ha.add hb) (WLe.zero Q P m) h

lemma WLe.C {m : ℤ} {g : R[X]} (hg : WBound Q m g) : WLe Q P m (C g) := by
  intro i
  rw [coeff_C]
  by_cases hi : i = 0
  · subst hi
    simpa using hg
  · rw [if_neg hi]
    exact WBound.zero Q _

lemma wtop_eq_zero {m m' : ℤ} {x : R[X][X]} (hx : WLe Q P m' x) (h : m' < m) :
    wtop Q P m x = 0 := by
  ext i : 1
  rw [coeff_wtop, coeff_zero]
  exact wpart_eq_zero Q (hx i) (by linarith)

lemma wtop_mul {m₁ m₂ : ℤ} {x y : R[X][X]} (hx : WLe Q P m₁ x) (hy : WLe Q P m₂ y) :
    wtop Q P (m₁ + m₂) (x * y) = wtop Q P m₁ x * wtop Q P m₂ y := by
  ext i : 1
  rw [coeff_wtop, coeff_mul, coeff_mul, ← wpartHom_apply, map_sum]
  refine Finset.sum_congr rfl fun ab hab => ?_
  have hab' : ab.1 + ab.2 = i := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  have he : m₁ + m₂ + (i : ℤ) * P = m₁ + (ab.1 : ℤ) * P + (m₂ + (ab.2 : ℤ) * P) := by
    rw [← hab']
    push_cast
    ring
  rw [coeff_wtop, coeff_wtop, wpartHom_apply, he]
  exact wpart_mul Q (hx ab.1) (hy ab.2)

end Weighted

/-- `ExpMap.coassoc` follows from the coefficient identity
`coeff r (f (coeff i (f a))) = (i + r).choose i * coeff (i + r) (f a)`.
(Adapted from the Open Math Agents dimension-three positive-characteristic proof.) -/
lemma coassoc_of_coeff_coeff {K D : Type*} [CommRing K] [CommRing D] [Algebra K D]
    (f : D →ₐ[K] Polynomial D)
    (hcoeff : ∀ (a : D) (i r : ℕ),
      (f ((f a).coeff i)).coeff r = ((i + r).choose i : D) * (f a).coeff (i + r))
    (a : D) :
    Polynomial.map f.toRingHom (f a) =
    Polynomial.eval₂RingHom (Polynomial.C.comp Polynomial.C)
      (Polynomial.C Polynomial.X + Polynomial.X) (f a) := by
  ext i r
  rw [Polynomial.coeff_map]
  change (f ((f a).coeff i)).coeff r = _
  rw [hcoeff a i r]
  generalize f a = P
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, Polynomial.coeff_add, mul_add]
    rw [hp, hq]
  | monomial n c =>
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, RingHom.comp_apply]
    rw [add_pow, Finset.mul_sum, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
    have hterm : ∀ k ∈ Finset.range (n + 1),
        (((Polynomial.C (Polynomial.C c) *
          (Polynomial.C Polynomial.X ^ k * Polynomial.X ^ (n - k) *
            (n.choose k : Polynomial (Polynomial D)))).coeff i).coeff r) =
        if k = r ∧ n - k = i then (n.choose i : D) * c else 0 := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have h1 : Polynomial.C (Polynomial.C c) *
          (Polynomial.C Polynomial.X ^ k * Polynomial.X ^ (n - k) *
            (n.choose k : Polynomial (Polynomial D))) =
          Polynomial.C (Polynomial.C (c * (n.choose k : D)) * Polynomial.X ^ k) *
          Polynomial.X ^ (n - k) := by
        simp only [map_mul, map_natCast, Polynomial.C_pow]; ring
      rw [h1, Polynomial.coeff_C_mul_X_pow]
      by_cases hni : i = n - k
      · rw [if_pos hni, Polynomial.coeff_C_mul_X_pow]
        by_cases hkr : r = k
        · rw [if_pos hkr, if_pos ⟨hkr.symm, hni.symm⟩]
          rw [show n.choose k = n.choose i by rw [hni]; exact (Nat.choose_symm hkn).symm, mul_comm]
        · rw [if_neg hkr, if_neg (fun h => hkr h.1.symm)]
      · rw [if_neg hni, Polynomial.coeff_zero, if_neg (fun h => hni h.2.symm)]
    rw [Finset.sum_congr rfl hterm, Polynomial.coeff_monomial]
    by_cases hnir : n = i + r
    · subst hnir
      rw [if_pos rfl, Finset.sum_eq_single r]
      · simp
      · intro k _ hkr; rw [if_neg (fun h => hkr h.1)]
      · intro hr; exfalso; exact hr (Finset.mem_range.mpr (by omega))
    · rw [if_neg hnir, mul_zero]
      symm
      apply Finset.sum_eq_zero; intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [if_neg]; rintro ⟨rfl, hsub⟩; exact hnir (by omega)

/- ### Homogenization of an exponential map on a cylinder with respect to the cylinder degree -/

noncomputable section Homogenize

variable {B : Type v} [CommRing B] [Algebra k B]
variable (φ : ExpMap k B[X]) (Q : ℕ) (P : ℤ)

/-- The weight-zero part of the action on the constants. -/
def homogConst (hB : ∀ b : B, WLe Q P 0 (φ (C b))) : B →+* B[X][X] where
  toFun b := wtop Q P 0 (φ (C b))
  map_one' := by
    have h1 : φ (C (1 : B)) = C (C (1 : B)) := by
      rw [C_1, C_1]
      exact map_one φ.toAlgHom
    show wtop Q P 0 (φ (C 1)) = 1
    rw [h1, wtop_C, wpart_C, C_1, C_1]
  map_mul' a b := by
    show wtop Q P 0 (φ (C (a * b))) = wtop Q P 0 (φ (C a)) * wtop Q P 0 (φ (C b))
    rw [C_mul, map_mul, ← wtop_mul Q P (hB a) (hB b), add_zero]
  map_zero' := by
    show wtop Q P 0 (φ (C 0)) = 0
    rw [C_0, map_zero, wtop_zero]
  map_add' a b := by
    show wtop Q P 0 (φ (C (a + b))) = wtop Q P 0 (φ (C a)) + wtop Q P 0 (φ (C b))
    rw [C_add, map_add, wtop_add]

lemma homogConst_apply (hB : ∀ b : B, WLe Q P 0 (φ (C b))) (b : B) :
    homogConst φ Q P hB b = wtop Q P 0 (φ (C b)) := rfl

/-- The homogenized algebra map: constants go to their weight-zero parts and the
cylinder variable to its part of weight `Q`. -/
def homogHom (hB : ∀ b : B, WLe Q P 0 (φ (C b))) : B[X] →ₐ[k] B[X][X] where
  toRingHom := Polynomial.eval₂RingHom (homogConst φ Q P hB) (wtop Q P Q (φ X))
  commutes' c := by
    show eval₂ (homogConst φ Q P hB) (wtop Q P Q (φ X)) (algebraMap k B[X] c) =
      algebraMap k B[X][X] c
    have h1 : φ (C (algebraMap k B c)) = C (C (algebraMap k B c)) := by
      have h := φ.toAlgHom.commutes c
      rwa [Polynomial.algebraMap_apply, Polynomial.algebraMap_apply,
        Polynomial.algebraMap_apply] at h
    rw [Polynomial.algebraMap_apply, eval₂_C, homogConst_apply, h1, wtop_C, wpart_C,
      Polynomial.algebraMap_apply, Polynomial.algebraMap_apply]

lemma homogHom_C (hB : ∀ b : B, WLe Q P 0 (φ (C b))) (b : B) :
    homogHom φ Q P hB (C b) = wtop Q P 0 (φ (C b)) := by
  show eval₂ (homogConst φ Q P hB) (wtop Q P Q (φ X)) (C b) = _
  rw [eval₂_C, homogConst_apply]

lemma homogHom_X (hB : ∀ b : B, WLe Q P 0 (φ (C b))) :
    homogHom φ Q P hB X = wtop Q P Q (φ X) := by
  show eval₂ (homogConst φ Q P hB) (wtop Q P Q (φ X)) X = _
  rw [eval₂_X]

variable {φ Q P}

lemma wle_X_pow (hX : WLe Q P Q (φ X)) (n : ℕ) :
    WLe Q P ((Q : ℤ) * n) (φ X ^ n) ∧
      wtop Q P ((Q : ℤ) * n) (φ X ^ n) = wtop Q P Q (φ X) ^ n := by
  induction n with
  | zero =>
    have h1 : (1 : B[X][X]) = C (C 1) := by rw [C_1, C_1]
    have h0 : (Q : ℤ) * ((0 : ℕ) : ℤ) = 0 := by simp
    rw [pow_zero, pow_zero, h0, h1]
    exact ⟨WLe.C Q P (WBound.C Q 1), by rw [wtop_C, wpart_C]⟩
  | succ n ih =>
    have he : (Q : ℤ) * ((n + 1 : ℕ) : ℤ) = (Q : ℤ) * n + Q := by
      push_cast
      ring
    rw [pow_succ, pow_succ, he]
    exact ⟨ih.1.mul hX, by rw [wtop_mul Q P ih.1 hX, ih.2]⟩

lemma wle_monomial (hB : ∀ b : B, WLe Q P 0 (φ (C b))) (hX : WLe Q P Q (φ X))
    (n : ℕ) (b : B) : WLe Q P ((Q : ℤ) * n) (φ (monomial n b)) := by
  rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
  have h := (hB b).mul (wle_X_pow hX n).1
  rwa [zero_add] at h

lemma homogHom_monomial (hB : ∀ b : B, WLe Q P 0 (φ (C b))) (hX : WLe Q P Q (φ X))
    (n : ℕ) (b : B) :
    homogHom φ Q P hB (monomial n b) = wtop Q P ((Q : ℤ) * n) (φ (monomial n b)) := by
  rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, map_mul, map_pow, homogHom_C, homogHom_X,
    ← (wle_X_pow hX n).2, ← wtop_mul Q P (hB b) (wle_X_pow hX n).1, zero_add]

lemma wle_of_wbound (hB : ∀ b : B, WLe Q P 0 (φ (C b))) (hX : WLe Q P Q (φ X))
    {μ : ℤ} {g : B[X]} (hg : WBound Q μ g) : WLe Q P μ (φ g) := by
  rw [g.as_sum_support, map_sum]
  refine WLe.sum Q P _ _ fun n hn => ?_
  exact (wle_monomial hB hX n _).mono (hg n (mem_support_iff.mp hn))

/-- Taking the top weighted part commutes with the action. -/
lemma wtop_eq_homogHom (hB : ∀ b : B, WLe Q P 0 (φ (C b))) (hX : WLe Q P Q (φ X))
    {μ : ℤ} {g : B[X]} (hg : WBound Q μ g) :
    wtop Q P μ (φ g) = homogHom φ Q P hB (wpart Q μ g) := by
  have h1 : φ g = ∑ n ∈ g.support, φ (monomial n (g.coeff n)) := by
    conv_lhs => rw [g.as_sum_support]
    exact map_sum φ.toAlgHom _ _
  rw [h1, ← wtopHom_apply, map_sum]
  unfold wpart
  rw [map_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hle := hg n (mem_support_iff.mp hn)
  rw [wtopHom_apply]
  by_cases h : (Q : ℤ) * n = μ
  · rw [if_pos h, homogHom_monomial hB hX, h]
  · rw [if_neg h, map_zero]
    exact wtop_eq_zero Q P (wle_monomial hB hX n _) (lt_of_le_of_ne hle h)

/-- The homogenized exponential map. -/
def homogExp (hB : ∀ b : B, WLe Q P 0 (φ (C b))) (hX : WLe Q P Q (φ X)) : ExpMap k B[X] where
  toAlgHom := homogHom φ Q P hB
  eval_zero a := by
    rw [← coeff_zero_eq_eval_zero]
    induction a using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add, coeff_add, hp, hq]
    | monomial n b =>
      rw [homogHom_monomial hB hX, coeff_wtop, φ.coeff_zero]
      simpa using wpart_monomial Q n b
  coassoc := coassoc_of_coeff_coeff _ (by
    intro a i r
    induction a using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, coeff_add, hp, hq, mul_add]
    | monomial n b =>
      have hw := wle_monomial hB hX n b
      rw [homogHom_monomial hB hX, coeff_wtop, coeff_wtop, ← wtop_eq_homogHom hB hX (hw i),
        coeff_wtop, φ.coeff_coeff_coassoc, wpart_natCast_mul]
      congr 2
      push_cast
      ring)

lemma homogExp_lead (hQ : 0 < Q) (hB : ∀ b : B, WLe Q P 0 (φ (C b))) (hX : WLe Q P Q (φ X))
    {f : B[X]} (hf : f ∈ φ.invSubalg) :
    C f.leadingCoeff * X ^ f.natDegree ∈ (homogExp hB hX).invSubalg := by
  have key := wtop_eq_homogHom hB hX (WBound.of_natDegree_le Q (le_refl f.natDegree))
  have hφf : φ f = C f := hf
  rw [hφf, wtop_C, wpart_natDegree Q hQ] at key
  exact key.symm

lemma homogExp_nontrivial (hB : ∀ b : B, WLe Q P 0 (φ (C b))) (hX : WLe Q P Q (φ X))
    (d : ℕ) (b : B) (i n : ℕ) (hi : 1 ≤ i)
    (hne : ((φ (monomial d b)).coeff i).coeff n ≠ 0)
    (heq : (Q : ℤ) * n = Q * d + i * P) : (homogExp hB hX).IsNontrivial := by
  refine ⟨monomial d b, fun hmem => hne ?_⟩
  have h1 : homogHom φ Q P hB (monomial d b) = C (monomial d b) := hmem
  rw [homogHom_monomial hB hX] at h1
  have h2 := congrArg (fun x : B[X][X] => (x.coeff i).coeff n) h1
  simp only [coeff_wtop, coeff_wpart] at h2
  rw [if_pos heq, coeff_C, if_neg (by omega), coeff_zero] at h2
  exact h2

lemma homogExp_coeff_C (hQ : 0 < Q) (hB : ∀ b : B, WLe Q P 0 (φ (C b)))
    (hX : WLe Q P Q (φ X)) (b : B) (i : ℕ) :
    ∃ (n : ℕ) (β : B), ((homogExp hB hX) (C b)).coeff i = monomial n β := by
  show ∃ (n : ℕ) (β : B), (homogHom φ Q P hB (C b)).coeff i = monomial n β
  rw [homogHom_C, coeff_wtop]
  exact wpart_eq_monomial Q hQ _ _

end Homogenize

section Weights

variable {B : Type v} [CommRing B] [Algebra k B]

/-- The slope of the homogenization: the largest ratio between the jump in cylinder degree
and the order in the parameter, taken over a finite generating set. -/
theorem exists_weights [Algebra.FiniteType k B] (φ : ExpMap k B[X]) (hφ : φ.IsNontrivial) :
    ∃ (Q : ℕ) (P : ℤ), 0 < Q ∧ (∀ b : B, WLe Q P 0 (φ (C b))) ∧ WLe Q P Q (φ X) ∧
      ∃ (d : ℕ) (b : B) (i n : ℕ), 1 ≤ i ∧ ((φ (monomial d b)).coeff i).coeff n ≠ 0 ∧
        (Q : ℤ) * n = Q * d + i * P := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k B).FG)
  let gens : Finset (ℕ × B) := insert (1, 1) (s.image fun b => (0, b))
  let T : Finset (ℕ × ℕ × ℕ) := gens.biUnion fun g =>
    ((φ (monomial g.1 g.2)).support.filter (1 ≤ ·)).biUnion fun i =>
      ((φ (monomial g.1 g.2)).coeff i).support.image fun n => (g.1, i, n)
  have hT : ∀ d i n, (d, i, n) ∈ T ↔
      ∃ b, (d, b) ∈ gens ∧ 1 ≤ i ∧ ((φ (monomial d b)).coeff i).coeff n ≠ 0 := by
    intro d i n
    simp only [T, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image, mem_support_iff,
      Prod.mk.injEq, Prod.exists]
    constructor
    · rintro ⟨d', b, hg, i', ⟨_, h1⟩, n', hn', rfl, rfl, rfl⟩
      exact ⟨b, hg, h1, hn'⟩
    · rintro ⟨b, hg, h1, hn⟩
      exact ⟨d, b, hg, i, ⟨fun h0 => hn (by rw [h0, coeff_zero]), h1⟩, n, hn, rfl, rfl, rfl⟩
  have hTne : T.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hinv : ∀ g ∈ gens, monomial g.1 g.2 ∈ φ.invSubalg := by
      intro g hg
      rw [φ.mem_invSubalg_iff_natDegree_eq_zero]
      by_contra hne
      have hpos : 0 < (φ (monomial g.1 g.2)).natDegree := Nat.pos_of_ne_zero hne
      have hlc : (φ (monomial g.1 g.2)).leadingCoeff ≠ 0 :=
        leadingCoeff_ne_zero.mpr (fun h => by simp [h] at hpos)
      have hmem : (g.1, (φ (monomial g.1 g.2)).natDegree,
          (φ (monomial g.1 g.2)).leadingCoeff.natDegree) ∈ T :=
        (hT _ _ _).mpr ⟨g.2, hg, hpos, leadingCoeff_ne_zero.mpr hlc⟩
      rw [hemp] at hmem
      exact Finset.notMem_empty _ hmem
    have hC : ∀ b : B, C b ∈ φ.invSubalg := by
      intro b
      have hb : b ∈ Algebra.adjoin k (s : Set B) := by rw [hs]; trivial
      induction hb using Algebra.adjoin_induction with
      | mem x hx =>
        have h := hinv (0, x) (by simp [gens, Finset.mem_coe.mp hx])
        simpa using h
      | algebraMap r => exact φ.invSubalg.algebraMap_mem r
      | add x y _ _ hx hy => rw [C_add]; exact φ.invSubalg.add_mem hx hy
      | mul x y _ _ hx hy => rw [C_mul]; exact φ.invSubalg.mul_mem hx hy
    have hXinv : (X : B[X]) ∈ φ.invSubalg := by
      have h := hinv (1, 1) (by simp [gens])
      simpa [monomial_one_one_eq_X] using h
    have hall : ∀ a : B[X], a ∈ φ.invSubalg := by
      intro a
      induction a using Polynomial.induction_on' with
      | add p q hp hq => exact φ.invSubalg.add_mem hp hq
      | monomial n b =>
        rw [← C_mul_X_pow_eq_monomial]
        exact φ.invSubalg.mul_mem (hC b) (φ.invSubalg.pow_mem hXinv n)
    obtain ⟨a, ha⟩ := hφ
    exact ha (hall a)
  obtain ⟨⟨d₀, i₀, n₀⟩, ht₀, hmax⟩ :=
    Finset.exists_max_image T (fun t => ((t.2.2 : ℚ) - t.1) / t.2.1) hTne
  obtain ⟨b₀, hg₀, hi₀, hne₀⟩ := (hT _ _ _).mp ht₀
  have hgen : ∀ d b, (d, b) ∈ gens → ∀ i n, 1 ≤ i →
      ((φ (monomial d b)).coeff i).coeff n ≠ 0 →
      (i₀ : ℤ) * n ≤ i₀ * d + i * ((n₀ : ℤ) - d₀) := by
    intro d b hg i n hi hne
    have h := hmax (d, i, n) ((hT _ _ _).mpr ⟨b, hg, hi, hne⟩)
    simp only at h
    have hi' : (0 : ℚ) < i := by exact_mod_cast hi
    have hi₀' : (0 : ℚ) < i₀ := by exact_mod_cast hi₀
    rw [div_le_div_iff₀ hi' hi₀'] at h
    have h' : ((n : ℤ) - d) * i₀ ≤ ((n₀ : ℤ) - d₀) * i := by exact_mod_cast h
    linarith
  refine ⟨i₀, (n₀ : ℤ) - d₀, hi₀, ?_, ?_, d₀, b₀, i₀, n₀, hi₀, hne₀, by ring⟩
  · intro b
    have hb : b ∈ Algebra.adjoin k (s : Set B) := by rw [hs]; trivial
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      intro i n hne
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · rw [φ.coeff_zero, coeff_C] at hne
        have hn : n = 0 := by
          by_contra h0
          exact hne (if_neg h0)
        simp [hn]
      · have h := hgen 0 x (by simp [gens, Finset.mem_coe.mp hx]) i n hi (by simpa using hne)
        simpa using h
    | algebraMap r =>
      have h1 : φ (C (algebraMap k B r)) = C (C (algebraMap k B r)) := by
        have h := φ.toAlgHom.commutes r
        rwa [Polynomial.algebraMap_apply, Polynomial.algebraMap_apply,
          Polynomial.algebraMap_apply] at h
      rw [h1]
      exact WLe.C _ _ (WBound.C _ _)
    | add x y _ _ hx hy =>
      rw [C_add, map_add]
      exact hx.add hy
    | mul x y _ _ hx hy =>
      rw [C_mul, map_mul]
      have h := hx.mul hy
      rwa [add_zero] at h
  · intro i n hne
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [φ.coeff_zero, coeff_X] at hne
      have hn : 1 = n := by
        by_contra h0
        exact hne (if_neg h0)
      simp [← hn]
    · have h := hgen 1 1 (by simp [gens]) i n hi (by simpa [monomial_one_one_eq_X] using hne)
      simpa using h

/-- **Homogenization** of a nontrivial exponential map on a cylinder with respect to the
cylinder degree. The result fixes the leading term of every old invariant, and its
coefficients on constants are monomials in the cylinder variable. -/
theorem ExpMap.exists_homogenization [Algebra.FiniteType k B]
    (φ : ExpMap k B[X]) (hφ : φ.IsNontrivial) :
    ∃ ψ : ExpMap k B[X], ψ.IsNontrivial ∧
      (∀ f ∈ φ.invSubalg, C f.leadingCoeff * X ^ f.natDegree ∈ ψ.invSubalg) ∧
      ∀ (b : B) (i : ℕ), ∃ (n : ℕ) (β : B), (ψ (C b)).coeff i = monomial n β := by
  obtain ⟨Q, P, hQ, hB, hX, d, b, i, n, hi, hne, heq⟩ := exists_weights φ hφ
  exact ⟨homogExp hB hX, homogExp_nontrivial hB hX d b i n hi hne heq,
    fun f hf => homogExp_lead hQ hB hX hf, homogExp_coeff_C hQ hB hX⟩

/-- A nontrivial action fixing the cylinder variable whose coefficients on constants are
monomials restricts to a nontrivial action on the fiber `X = 1`, over every field. -/
theorem action_of_homogeneous_fixed_variable
    (ψ : ExpMap k B[X]) (hψ : ψ.IsNontrivial) (hX : X ∈ ψ.invSubalg)
    (hhom : ∀ (b : B) (i : ℕ), ∃ (n : ℕ) (β : B), (ψ (C b)).coeff i = monomial n β) :
    ∃ τ : ExpMap k B, τ.IsNontrivial := by
  classical
  have hmoved : ∃ b : B, ψ (C b) ≠ C (C b) := by
    by_contra! h
    have hid : ψ.toAlgHom = Polynomial.CAlgHom :=
      Polynomial.algHom_ext' (AlgHom.ext h) hX
    obtain ⟨p, hp⟩ := hψ
    exact hp (DFunLike.congr_fun hid p)
  obtain ⟨b, hb⟩ := hmoved
  obtain ⟨i, hi⟩ : ∃ i, (ψ (C b)).coeff i ≠ (C (C b) : B[X][X]).coeff i := by
    by_contra! h
    exact hb (Polynomial.ext h)
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hi (by rw [ψ.coeff_zero, coeff_C_zero])
  obtain ⟨n, β, hβ⟩ := hhom b i
  have hβ0 : β ≠ 0 := by
    rintro rfl
    apply hi
    rw [hβ, coeff_C, if_neg hi0, monomial_zero_right]
  let q : B[X] := X - C 1
  have hq : q ∈ ψ.invSubalg :=
    ψ.invSubalg.sub_mem hX (by rw [C_1]; exact ψ.invSubalg.one_mem)
  let I := Ideal.span {q}
  let mk := Ideal.Quotient.mk I
  let τ := ψ.quotient q hq
  have hτ : τ.IsNontrivial := by
    refine ⟨mk (C b), fun he ↦ hβ0 ?_⟩
    change (ψ (C b)).map mk = C (mk (C b)) at he
    have hcoeff : mk ((ψ (C b)).coeff i) = 0 := by
      have h := congrArg (fun P ↦ Polynomial.coeff P i) he
      simpa [coeff_C, hi0] using h
    rw [hβ] at hcoeff
    have hdiv := Ideal.mem_span_singleton.mp ((Ideal.Quotient.eq_zero_iff_mem).mp hcoeff)
    have hroot := Polynomial.dvd_iff_isRoot.mp hdiv
    simpa using hroot
  let e := (Polynomial.quotientSpanXSubCAlgEquiv (1 : B)).restrictScalars k
  exact ⟨τ.compAlgEquiv e, ExpMap.isNontrivial_compAlgEquiv hτ e⟩

/-- A cylinder over the plane forces a nontrivial exponential map on the coefficient
algebra, over every field. -/
theorem exists_action [Algebra.FiniteType k B] (e : (Plane k)[X] ≃ₐ[k] B[X]) :
    ∃ τ : ExpMap k B, τ.IsNontrivial := by
  let := isDomain e
  obtain ⟨φ, hφ, f, hf, hdeg⟩ := cylinder_action_with_nonconstant_invariant e
  obtain ⟨ψ, hψ, hlead, hhom⟩ := ExpMap.exists_homogenization φ hφ
  have hlead := hlead f hf
  have hfac := fixedRing_factoriallyClosed ψ.toAlgHom ψ.eval_zero
  have hfn : f ≠ 0 := by intro h; simp [h] at hdeg
  have hcn : C f.leadingCoeff ≠ 0 := by simpa using Polynomial.leadingCoeff_ne_zero.mpr hfn
  have hpow := (hfac _ _ (mul_ne_zero hcn (pow_ne_zero _ X_ne_zero)) hlead).2
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hdeg.ne'
  rw [hm, pow_succ] at hpow
  have hX := (hfac _ _ (mul_ne_zero (pow_ne_zero m X_ne_zero) X_ne_zero) hpow).2
  exact action_of_homogeneous_fixed_variable ψ hψ hX hhom

end Weights

/- ### Base change of the fixed ring and the fibers of the quotient map -/

noncomputable section BaseChange

variable {B : Type v} [CommRing B] [Algebra k B]
variable (K : Type w) [Field K] [Algebra k K]

/-- The comparison map from the base change of a polynomial algebra to the polynomial
algebra over the base change. -/
def polyTensor : K ⊗[k] B[X] →ₐ[K] (K ⊗[k] B)[X] :=
  Algebra.TensorProduct.lift (Algebra.ofId K (K ⊗[k] B)[X])
    (Polynomial.mapAlgHom (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B))
    (fun _ _ => Commute.all _ _)

lemma polyTensor_tmul (c : K) (f : B[X]) :
    polyTensor K (c ⊗ₜ[k] f) = C (c ⊗ₜ[k] (1 : B)) *
      f.map (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B).toRingHom := by
  simp [polyTensor, Algebra.ofId_apply, Polynomial.algebraMap_apply,
    Algebra.TensorProduct.algebraMap_apply]

lemma polyTensor_injective : Function.Injective (polyTensor (k := k) (B := B) K) := by
  let g : (K ⊗[k] B)[X] →+* K ⊗[k] B[X] :=
    Polynomial.eval₂RingHom
      (Algebra.TensorProduct.map (AlgHom.id K K) (CAlgHom : B →ₐ[k] B[X])).toRingHom
      ((1 : K) ⊗ₜ[k] (X : B[X]))
  have hg : ∀ x, g (polyTensor K x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c f =>
      have h2 : g (f.map (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B).toRingHom) =
          (1 : K) ⊗ₜ[k] f := by
        induction f using Polynomial.induction_on' with
        | add p q hp hq => rw [Polynomial.map_add, map_add, hp, hq, TensorProduct.tmul_add]
        | monomial n b =>
          simp [g, ← C_mul_X_pow_eq_monomial, Algebra.TensorProduct.tmul_pow]
      rw [polyTensor_tmul, map_mul, h2]
      simp [g]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  exact Function.LeftInverse.injective hg

lemma polyTensor_map_C (x : K ⊗[k] B) :
    polyTensor K (Algebra.TensorProduct.map (AlgHom.id K K) (CAlgHom : B →ₐ[k] B[X]) x) =
      C x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c b =>
    rw [Algebra.TensorProduct.map_tmul, polyTensor_tmul]
    simp [← C_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, C_add]

variable (τ : ExpMap k B)

/-- The base change of an exponential map, as an algebra map into the polynomial algebra. -/
def ExpMap.baseChangeHom : K ⊗[k] B →ₐ[K] (K ⊗[k] B)[X] :=
  (polyTensor K).comp (Algebra.TensorProduct.map (AlgHom.id K K) τ.toAlgHom)

lemma ExpMap.baseChangeHom_eval_zero (x : K ⊗[k] B) :
    ((τ.baseChangeHom K) x).eval 0 = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c b =>
    have h : τ.baseChangeHom K (c ⊗ₜ[k] b) = C (c ⊗ₜ[k] (1 : B)) *
        (τ b).map (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B).toRingHom := by
      rw [ExpMap.baseChangeHom, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
        polyTensor_tmul]
      rfl
    rw [h, eval_mul, eval_C, eval_map, eval₂_at_zero, τ.coeff_zero]
    simp
  | add x y hx hy => rw [map_add, eval_add, hx, hy]

/-- The fixed ring after base change, written as an equalizer of tensored maps. -/
abbrev tensorFixed : Subalgebra K (K ⊗[k] B) :=
  AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id K K) τ.toAlgHom)
    (Algebra.TensorProduct.map (AlgHom.id K K) Polynomial.CAlgHom)

lemma tensorFixed_eq :
    tensorFixed K τ = AlgHom.equalizer (τ.baseChangeHom K) Polynomial.CAlgHom := by
  ext x
  constructor
  · intro h
    change Algebra.TensorProduct.map (AlgHom.id K K) τ.toAlgHom x =
      Algebra.TensorProduct.map (AlgHom.id K K) Polynomial.CAlgHom x at h
    change polyTensor K (Algebra.TensorProduct.map (AlgHom.id K K) τ.toAlgHom x) = C x
    rw [h, polyTensor_map_C]
  · intro h
    change polyTensor K (Algebra.TensorProduct.map (AlgHom.id K K) τ.toAlgHom x) = C x at h
    change Algebra.TensorProduct.map (AlgHom.id K K) τ.toAlgHom x =
      Algebra.TensorProduct.map (AlgHom.id K K) Polynomial.CAlgHom x
    apply polyTensor_injective K
    rw [h, polyTensor_map_C]

/-- After any field extension, the generator of the fixed ring minus a scalar stays prime
in the base change of the coefficient algebra. -/
theorem prime_linear_of_action [Algebra.FiniteType k B] (e : (Plane k)[X] ≃ₐ[k] B[X])
    (u : k[X] ≃ₐ[k] τ.invSubalg) (α : K) :
    Prime ((1 : K) ⊗ₜ[k] ((u X : τ.invSubalg) : B) - α ⊗ₜ[k] (1 : B)) := by
  have hdom : IsDomain (K ⊗[k] B) := geometricallyIntegral e K
  have hufd : UniqueFactorizationMonoid (K ⊗[k] B) := geometricallyFactorial e K
  have hfc : FactoriallyClosed (tensorFixed K τ) := by
    rw [tensorFixed_eq]
    exact fixedRing_factoriallyClosed (τ.baseChangeHom K) (τ.baseChangeHom_eval_zero K)
  let w := τ.fixedRingBaseChange u K
  have hw : ((w (X - C α) : tensorFixed K τ) : K ⊗[k] B) =
      (1 : K) ⊗ₜ[k] ((u X : τ.invSubalg) : B) - α ⊗ₜ[k] (1 : B) := by
    simp [w, ExpMap.fixedRingBaseChange]
  have hirr : Irreducible (w (X - C α)) :=
    (MulEquiv.irreducible_iff w).mpr (irreducible_X_sub_C α)
  have hval := hfc.irreducible_val hirr
  rw [hw] at hval
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp hval

end BaseChange

section FiberCondition

variable {B : Type v} [CommRing B] [Algebra k B]

/-- Let `S ≅ k[t]` be a subalgebra of `B` and suppose `t - α` stays prime in `K ⊗ B` for every
scalar `α` of an algebraically closed extension `K`. Then every fiber of `S → B` over a
prime `p` of `S` is geometrically integral over the residue field, also when the residue
field is an inseparable extension of `k`. Consequently an element of `B` which is algebraic
modulo `p` is congruent to an element of `S`. -/
theorem fiber_condition_of_prime_linear [IsDomain B]
    {K : Type w} [Field K] [IsAlgClosed K] [Algebra k K]
    (S : Subalgebra k B) (u : k[X] ≃ₐ[k] S)
    (hθ : ∀ α : K, Prime ((1 : K) ⊗ₜ[k] ((u X : S) : B) - α ⊗ₜ[k] (1 : B)))
    (p : S) (hp : Prime p) (z : B) (P : S[X])
    (hz : algebraMap S B p ∣ Polynomial.aeval z P) :
    C p ∣ P ∨ ∃ r : S, algebraMap S B p ∣ z - algebraMap S B r := by
  classical
  by_cases hP : C p ∣ P
  · exact Or.inl hP
  right
  let t : B := ((u X : S) : B)
  let q : k[X] := u.symm p
  have hq : Irreducible q := (MulEquiv.irreducible_iff u.symm).mpr hp.irreducible
  have huq : u q = p := u.apply_symm_apply p
  have hu : ∀ h : k[X], ((u h : S) : B) = aeval t h := by
    intro h
    have h1 := Polynomial.aeval_algHom_apply (S.val.comp u.toAlgHom) (X : k[X]) h
    rw [aeval_X_left_apply] at h1
    exact h1.symm
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_aeval_eq_zero K q (degree_pos_of_irreducible hq).ne'
  have : Fact (Irreducible q) := ⟨hq⟩
  -- the residue field, embedded into `K` through the root `α`
  let σ : AdjoinRoot q →ₐ[k] K := AdjoinRoot.liftAlgHom q (Algebra.ofId k K) α hα
  have hσ : ∀ h : k[X], σ (AdjoinRoot.mk q h) = aeval α h := fun h => rfl
  have hev0 : ∀ s : S, aeval α (u.symm s) = 0 → p ∣ s := by
    intro s hs
    have h1 : AdjoinRoot.mk q (u.symm s) = 0 :=
      σ.toRingHom.injective (by simpa [hσ] using hs)
    have h3 := map_dvd u (AdjoinRoot.mk_eq_zero.mp h1)
    rwa [huq, u.apply_symm_apply] at h3
  -- the geometric fiber over `α` is a domain
  let θ : K ⊗[k] B := (1 : K) ⊗ₜ[k] t - α ⊗ₜ[k] (1 : B)
  let I : Ideal (K ⊗[k] B) := Ideal.span {θ}
  have : I.IsPrime := Ideal.isPrime_span_singleton_of_prime (hθ α)
  let mkI : K ⊗[k] B →ₐ[K] (K ⊗[k] B) ⧸ I := Ideal.Quotient.mkₐ K I
  let ι : B →ₐ[k] (K ⊗[k] B) ⧸ I :=
    (mkI.restrictScalars k).comp Algebra.TensorProduct.includeRight
  have hmkα : ∀ c : K, mkI (c ⊗ₜ[k] (1 : B)) = algebraMap K ((K ⊗[k] B) ⧸ I) c :=
    fun c => mkI.commutes c
  have hcompat : ι.comp (S.val.comp u.toAlgHom) =
      (IsScalarTower.toAlgHom k K ((K ⊗[k] B) ⧸ I)).comp (Polynomial.aeval α) := by
    apply Polynomial.algHom_ext
    change mkI ((1 : K) ⊗ₜ[k] t) = algebraMap K ((K ⊗[k] B) ⧸ I) (aeval α (X : k[X]))
    rw [aeval_X, ← hmkα]
    exact Ideal.Quotient.eq.mpr (Ideal.subset_span rfl)
  have hιS : ∀ s : S, ι (s : B) = algebraMap K ((K ⊗[k] B) ⧸ I) (aeval α (u.symm s)) := by
    intro s
    have h1 := DFunLike.congr_fun hcompat (u.symm s)
    change ι ((u (u.symm s) : S) : B) = _ at h1
    rwa [u.apply_symm_apply] at h1
  -- the residue of `z` is algebraic over `K`, hence a scalar
  let evr : S →+* K := ((Polynomial.aeval α).comp u.symm.toAlgHom : S →ₐ[k] K).toRingHom
  have hne : P.map evr ≠ 0 := by
    intro h0
    apply hP
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    apply hev0
    have h1 := congrArg (fun f : K[X] => f.coeff i) h0
    simpa [evr] using h1
  have hroot : aeval (ι z) (P.map evr) = 0 := by
    have hc : (algebraMap K ((K ⊗[k] B) ⧸ I)).comp evr = ι.toRingHom.comp (algebraMap S B) := by
      ext s
      exact (hιS s).symm
    rw [aeval_def, eval₂_map, hc]
    refine (Polynomial.hom_eval₂ P (algebraMap S B) ι.toRingHom z).symm.trans ?_
    obtain ⟨y, hy⟩ := hz
    change ι (aeval z P) = 0
    rw [hy, map_mul]
    have h0 : ι (algebraMap S B p) = 0 := by
      change ι (p : B) = 0
      rw [hιS, hα, map_zero]
    rw [h0, zero_mul]
  obtain ⟨c, hc⟩ := scalar_of_algClosed_algebraic (⟨P.map evr, hne, hroot⟩ : IsAlgebraic K (ι z))
  have hmem : (1 : K) ⊗ₜ[k] z - c ⊗ₜ[k] (1 : B) ∈ I := by
    apply Ideal.Quotient.eq.mp
    change mkI ((1 : K) ⊗ₜ[k] z) = mkI (c ⊗ₜ[k] (1 : B))
    rw [hmkα, hc]
    rfl
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hmem
  -- descend along a retraction of `K` onto the residue field
  let : Algebra (AdjoinRoot q) K := σ.toRingHom.toAlgebra
  have : IsScalarTower k (AdjoinRoot q) K :=
    IsScalarTower.of_algebraMap_eq (fun c => (σ.commutes c).symm)
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one (AdjoinRoot q)
    (one_ne_zero : (1 : K) ≠ 0)
  let J : Ideal B := Ideal.span {(p : B)}
  let mkJ : B →ₐ[k] B ⧸ J := Ideal.Quotient.mkₐ k J
  have hJp : mkJ (p : B) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hJt : q.eval₂ (Algebra.ofId k (B ⧸ J)) (mkJ t) = 0 := by
    have h1 : aeval (mkJ t) q = mkJ (aeval t q) := Polynomial.aeval_algHom_apply mkJ t q
    rw [← hu, huq, hJp] at h1
    exact h1
  let ρ : AdjoinRoot q →ₐ[k] B ⧸ J := AdjoinRoot.liftAlgHom q (Algebra.ofId k (B ⧸ J)) (mkJ t) hJt
  have hρ : ∀ h : k[X], ρ (AdjoinRoot.mk q h) = mkJ ((u h : S) : B) := by
    intro h
    rw [hu]
    exact Polynomial.aeval_algHom_apply mkJ t h
  let π : K ⊗[k] B →ₗ[k] B ⧸ J :=
    (Algebra.TensorProduct.productMap ρ mkJ).toLinearMap ∘ₗ
      (LinearMap.rTensor B (ℓ.restrictScalars k))
  have hπt : ∀ (a : K) (b : B), π (a ⊗ₜ[k] b) = ρ (ℓ a) * mkJ b := fun a b => rfl
  have hπ : ∀ y : K ⊗[k] B, π (θ * y) = 0 := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have hαa : α * a = (AdjoinRoot.root q) • a := by
        rw [Algebra.smul_def]
        congr 1
        exact (AdjoinRoot.liftAlgHom_root q (Algebra.ofId k K) α hα).symm
      have hρroot : ρ (AdjoinRoot.root q) = mkJ t :=
        AdjoinRoot.liftAlgHom_root q (Algebra.ofId k (B ⧸ J)) (mkJ t) hJt
      have h1 : θ * (a ⊗ₜ[k] b) = a ⊗ₜ[k] (t * b) - (α * a) ⊗ₜ[k] b := by
        simp [θ, sub_mul, Algebra.TensorProduct.tmul_mul_tmul]
      rw [h1, map_sub, hπt, hπt, hαa, map_smul, smul_eq_mul, map_mul, map_mul, hρroot]
      ring
    | add x y hx hy => rw [mul_add, map_add, hx, hy, add_zero]
  have hfin : mkJ z = ρ (ℓ c) := by
    have h1 := congrArg π hy
    rw [hπ, map_sub, hπt, hπt, hℓ, map_one, one_mul, map_one, mul_one, sub_eq_zero] at h1
    exact h1
  obtain ⟨h, hh⟩ := AdjoinRoot.mk_surjective (ℓ c)
  refine ⟨u h, ?_⟩
  change (p : B) ∣ z - ((u h : S) : B)
  rw [← hh, hρ] at hfin
  have h2 : mkJ (z - ((u h : S) : B)) = 0 := by rw [map_sub, hfin, sub_self]
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h2)

end FiberCondition

/- ### The cancellation theorem -/

/-- Every nontrivial exponential map on the coefficient algebra of a cylinder over the plane
is a ruling: the fiber condition holds over every field, perfect or not. -/
theorem hasRuling_of_action {B : Type v} [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (e : (Plane k)[X] ≃ₐ[k] B[X]) (τ : ExpMap k B) (hτ : τ.IsNontrivial) : HasRuling k B := by
  let := isDomain e
  obtain ⟨u⟩ := τ.fixedRing_isPolynomial_of_nontrivial e hτ
  refine ⟨τ, hτ, fun p hp z P hz ↦ ?_⟩
  exact fiber_condition_of_prime_linear (K := AlgebraicClosure k) τ.invSubalg u
    (fun α ↦ prime_linear_of_action (AlgebraicClosure k) τ e u α) p hp z P hz

/-- The coefficient algebra of every cylinder over the plane has a ruling: homogenization
supplies a nontrivial exponential map and the fiber condition is automatic. -/
theorem cylinderHasRuling : CylinderHasRuling.{u, v} := by
  intro k _ B _ _ _ e
  obtain ⟨τ, hτ⟩ := exists_action e
  exact hasRuling_of_action e τ hτ

/-- Zariski cancellation for the affine plane over an arbitrary field. -/
theorem isCancellative_plane {k : Type u} [Field k] :
    Arxiv.«2208.14736».IsCancellative.{u, u, v} k (MvPolynomial (Fin 2) k) :=
  cancellation_of_ruling cylinderHasRuling

end OMA.ZariskiDimTwo

theorem OMA.solution :
    type_of% @Arxiv.«2208.14736».zariski_cancellation_problem.variants.dim_two :=
  @OMA.ZariskiDimTwo.isCancellative_plane
