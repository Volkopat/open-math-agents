import FormalConjectures.Arxiv.«0805.3777».TensorRank

-- Problem: Generic and maximal rank of 3-tensors — isGenericRank of gt critical
-- Upstream: formal-conjectures FormalConjectures/Arxiv/0805.3777/TensorRank.lean:191 (declaration Arxiv.«0805.3777».isGenericRank_of_gt_critical)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- REUSE AND CREDIT.
-- * The namespaces ThreeEven.Grid, ThreeEven.Dimension and ThreeEven.Dominance (polynomial
--   avoidance, the constructibility and Nullstellensatz argument that turns one surjective
--   differential of the sum map into a dense open set of tensors of bounded rank) are copied from
--   the merged proof proofs/Arxiv.0805.3777.isGenericRank_three_even.lean by mattdorman
--   (PR #2694). The theorem Critical.upper3 is the theorem ThreeEven.upper of that file, restated
--   for a general format and a general number of points.
-- * The section Critical.Bridge (holor indices, rank-one holors, passage between CP rank and
--   explicit sums) is the Bridge section of the merged proof
--   proofs/Arxiv.0805.3777.isMaxRank_two.lean (PR #3391, same owner), restated for a general
--   format; that section was adapted from proofs/Arxiv.0805.3777.isMaxRank_three_three_five_bounds.lean
--   (PR #2438, credited to DomTheDeveloper, a port of Kenta Kitamura's
--   https://github.com/KitaKen1/mrank-3-3-5-lean, Apache License 2.0).
-- * New: the spanning configuration (Critical.smat to Critical.spans3), the flattening lower
--   bound Critical.lower3, the bound Critical.cprank_le_mul, and the assembly Critical.main.

/-!
# Generic rank above the critical range

For `(m₁ - 1) (m₂ - 1) < m₃` the generic rank of a complex tensor of format `m₁ × m₂ × m₃` is
`min m₃ (m₁ m₂)` ([Friedland, (5.1)](https://arxiv.org/abs/0805.3777); Catalisano, Geramita,
Gimigliano 2002).

**Lower bound** (`Critical.lower3`). Flatten a tensor to the `m₃ × (m₁ m₂)` matrix of its slices.
A decomposition into `r` rank-one tensors factors every `N × N` submatrix through `ℂ^r`, so a
nonzero `N × N` minor forces `N ≤ r`. With `N = min m₃ (m₁ m₂)` the minor is a nonzero polynomial
in the entries, and the complement of its zero set is open and dense.

**Upper bound.** If `m₁ m₂ ≤ m₃` every tensor has rank at most `m₁ m₂` (`Critical.cprank_le_mul`).
Otherwise `(m₁ - 1) (m₂ - 1) < m₃ < m₁ m₂`, and by the differential criterion of the even case
(`Critical.upper3`) it is enough to find `m₃` points `(a t, b t, c t)` whose tangent spaces span
all tensors (`Critical.spans3`). Take `c t` the `t`-th basis vector. Then the tangent directions
`a t ⊗ b t ⊗ w` put the span of the `a t ⊗ b t` into every slice, and the directions
`u ⊗ b s ⊗ c s`, `a s ⊗ v ⊗ c s` add the tangent space `u ⊗ b s + a s ⊗ v` to the slice `s`. So
one needs, for every `s`, that the `a t ⊗ b t` together with that tangent space span all
`m₁ × m₂` matrices: surjectivity of a matrix `Critical.smat` whose entries are polynomials in the
`a t`, `b t`. For a single `s` this holds when `a s = b s = e₀` and the other points run through
the pairs `(e_i, e_j)` with `i, j ≥ 1`, of which there are `(m₁ - 1) (m₂ - 1) ≤ m₃ - 1`
(`Critical.witness`); a product of determinant polynomials then gives one choice of points that
works for all `s` at once (`ThreeEven.Grid.simultaneous_surjectivity`, `Critical.common3`).
-/

namespace ThreeEven.Grid
open MvPolynomial

/-- A single surjective specialization gives a polynomial whose nonvanishing
guarantees surjectivity. Its determinant uses a fixed right inverse at that point. -/
lemma surjectivity_polynomial {I J V : Type} [Fintype I] [DecidableEq I] [Fintype J]
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

lemma avoid_two {V : Type} {P Q : MvPolynomial V ℂ} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    ∃ x : V → ℂ, eval x P ≠ 0 ∧ eval x Q ≠ 0 := by
  by_contra! h
  apply (mul_ne_zero hP hQ)
  apply MvPolynomial.funext
  intro x
  rw [map_mul, map_zero]
  by_cases hx : eval x P = 0
  · exact mul_eq_zero.mpr (Or.inl hx)
  · exact mul_eq_zero.mpr (Or.inr (h x hx))

/-- Separate specializations can verify blocks depending on the same parameters:
the product of their certificate polynomials is nonzero over the complex numbers. -/
lemma simultaneous_surjectivity {K V : Type} [Fintype K] {I J : K → Type}
    [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)] [∀ k, Fintype (J k)]
    (M : ∀ k, Matrix (I k) (J k) (MvPolynomial V ℂ))
    (h : ∀ k, ∃ x : V → ℂ, Function.Surjective ((M k).map (eval x)).mulVec)
    (P : MvPolynomial V ℂ) (hP : P ≠ 0) :
    ∃ x : V → ℂ, eval x P ≠ 0 ∧ ∀ k, Function.Surjective ((M k).map (eval x)).mulVec := by
  classical
  choose z hz using h
  choose Q hQ hgood using fun k => surjectivity_polynomial (M k) (z k) (hz k)
  have hprod : (∏ k, Q k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hQ k
  obtain ⟨x, hx, hrest⟩ := avoid_two hP hprod
  have hvals : (∏ k, eval x (Q k)) ≠ 0 := by simpa only [map_prod] using hrest
  exact ⟨x, hx, fun k => hgood k x (Finset.prod_ne_zero_iff.mp hvals k (Finset.mem_univ k))⟩
end ThreeEven.Grid

namespace ThreeEven

open Arxiv.«0805.3777» Set Filter
open scoped Topology

namespace Dimension

lemma interior_polynomial_zero_locus {J : Type} (P : MvPolynomial J ℂ) (hP : P ≠ 0) :
    interior {y : J → ℂ | MvPolynomial.eval y P = 0} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hn := mem_interior_iff_mem_nhds.mp ha
  rw [nhds_pi, Filter.mem_pi] at hn
  obtain ⟨I, _, box, hin, hsub⟩ := hn
  apply hP
  apply MvPolynomial.funext_set box (fun j => infinite_of_mem_nhds (a j) (hin j))
  intro y hy
  have hyI : y ∈ I.pi box := fun j _ => hy j (Set.mem_univ _)
  have hzero : MvPolynomial.eval y P = 0 := hsub hyI
  simpa only [map_zero] using hzero

lemma eval_substitution {I J : Type} (F : J → MvPolynomial I ℂ) (x : I → ℂ)
    (P : MvPolynomial J ℂ) :
    MvPolynomial.eval x (MvPolynomial.aeval F P) =
      MvPolynomial.eval (fun j => MvPolynomial.eval x (F j)) P := by
  have he : (MvPolynomial.aeval x).comp (MvPolynomial.aeval F) =
      MvPolynomial.aeval (fun j => MvPolynomial.eval x (F j)) := by
    ext j
    simp [MvPolynomial.aeval_eq_eval]
  exact DFunLike.congr_fun he P

def index_cons_equiv (n : ℕ) (ds : List ℕ) : HolorIndex (n :: ds) ≃ Fin n × HolorIndex ds where
  toFun
    | ⟨i :: is, h⟩ => (⟨i, (List.forall₂_cons.mp h).1⟩, ⟨is, (List.forall₂_cons.mp h).2⟩)
    | ⟨[], h⟩ => nomatch h
  invFun q := ⟨q.1.val :: q.2.val, List.Forall₂.cons q.1.isLt q.2.property⟩
  left_inv := by
    rintro ⟨l, h⟩
    cases l with
    | nil => cases h
    | cons i is => rfl
  right_inv := by rintro ⟨⟨i, hi⟩, ⟨is, his⟩⟩; rfl

end Dimension

end ThreeEven

namespace ThreeEven.Dominance

open Set Filter
open ThreeEven.Dimension (interior_polynomial_zero_locus eval_substitution index_cons_equiv)
open scoped Topology Classical

lemma vector_is_simple {n : ℕ} (v : Holor ℂ [n]) : Holor.CPRankMax1 v := by
  let oneScalar : Holor ℂ [] := fun _ => 1
  have he : Holor.mul v oneScalar = v := by
    funext t
    change v t.take * (1 : ℂ) = v t
    rw [mul_one]
    congr 1
    apply Subtype.ext
    exact List.take_of_length_le t.property.length_eq.le
  rw [← he]
  exact Holor.CPRankMax1.cons _ _ (.nil _)

lemma tensor_sum_rank {d e f r : ℕ} (a : Fin r → Holor ℂ [d])
    (b : Fin r → Holor ℂ [e]) (c : Fin r → Holor ℂ [f]) :
    Holor.CPRankMax r (∑ i, Holor.mul (a i) (Holor.mul (b i) (c i))) := by
  have hs (i : Fin r) : Holor.CPRankMax1 (Holor.mul (a i) (Holor.mul (b i) (c i))) :=
    .cons _ _ (.cons _ _ (vector_is_simple (c i)))
  simpa using Holor.cprankMax_sum (n := 1) Finset.univ
    (fun i => Holor.mul (a i) (Holor.mul (b i) (c i))) (fun i _ => Holor.cprankMax_1 (hs i))

/-- A constructible spectral image containing the generic point contains a
principal open neighborhood of it. -/
lemma open_in_spectral_image {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    (φ : A →+* B) (hinj : Function.Injective φ) (hfp : φ.FinitePresentation) :
    ∃ f : A, f ≠ 0 ∧ ∀ q : PrimeSpectrum A, f ∉ q.asIdeal →
      q ∈ Set.range (PrimeSpectrum.comap φ) := by
  classical
  let z : PrimeSpectrum A := ⟨⊥, inferInstance⟩
  let w : PrimeSpectrum B := ⟨⊥, inferInstance⟩
  have hg : PrimeSpectrum.comap φ w = z := by
    apply PrimeSpectrum.ext
    change Ideal.comap φ ⊥ = ⊥
    rw [← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot φ).mp hinj
  obtain ⟨T, hT⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr
    (PrimeSpectrum.isConstructible_range_comap hfp)
  have hz : z ∈ T.toSet := by rw [hT]; exact ⟨w, hg⟩
  obtain ⟨C, hC, hzC⟩ := Set.mem_iUnion₂.mp hz
  change z ∈ PrimeSpectrum.zeroLocus (Set.range C.g) ∧
    z ∉ PrimeSpectrum.zeroLocus {C.f} at hzC
  have hg0 (i : Fin C.n) : C.g i = 0 := by
    have h := (PrimeSpectrum.mem_zeroLocus z _).mp hzC.1 (Set.mem_range_self i)
    exact (Ideal.mem_bot : C.g i ∈ (⊥ : Ideal A) ↔ _).mp h
  have hf0 : C.f ≠ 0 := by
    intro e
    apply hzC.2
    exact (PrimeSpectrum.mem_zeroLocus z _).mpr (Set.singleton_subset_iff.mpr (e ▸ z.asIdeal.zero_mem))
  refine ⟨C.f, hf0, ?_⟩
  intro q hq
  rw [← hT]
  apply Set.mem_iUnion₂.mpr
  refine ⟨C, hC, ?_⟩
  constructor
  · apply (PrimeSpectrum.mem_zeroLocus q _).mpr
    rintro _ ⟨i, rfl⟩
    rw [hg0 i]
    exact q.asIdeal.zero_mem
  · intro e
    exact hq ((PrimeSpectrum.mem_zeroLocus q _).mp e (Set.mem_singleton _))

/-- Hilbert's Nullstellensatz converts the principal open in the spectral image
to actual complex points in the image of the polynomial map. -/
lemma principal_open_in_image {I J : Type} [Finite I] [Finite J] (F : J → MvPolynomial I ℂ)
    (hinj : Function.Injective (MvPolynomial.aeval F : MvPolynomial J ℂ →ₐ[ℂ] MvPolynomial I ℂ)) :
    ∃ P : MvPolynomial J ℂ, P ≠ 0 ∧ ∀ y : J → ℂ, MvPolynomial.eval y P ≠ 0 →
      ∃ x : I → ℂ, ∀ j, MvPolynomial.eval x (F j) = y j := by
  classical
  let φ : MvPolynomial J ℂ →ₐ[ℂ] MvPolynomial I ℂ := MvPolynomial.aeval F
  have hfp : φ.toRingHom.FinitePresentation := by
    apply RingHom.FinitePresentation.of_finiteType.mp
    apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℂ (MvPolynomial J ℂ))
    have he : φ.toRingHom.comp (algebraMap ℂ (MvPolynomial J ℂ)) =
        algebraMap ℂ (MvPolynomial I ℂ) :=
      RingHom.ext (fun a => φ.commutes a)
    rw [he]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  obtain ⟨P, hP, hU⟩ := open_in_spectral_image φ.toRingHom hinj hfp
  refine ⟨P, hP, ?_⟩
  intro y hy
  let m := MvPolynomial.pointToPoint (k := ℂ) y
  have hy' : P ∉ m.asIdeal := fun h => hy ((MvPolynomial.mem_vanishingIdeal_singleton_iff y P).mp h)
  obtain ⟨q, hq⟩ := hU m hy'
  obtain ⟨M, hM, hle⟩ := q.asIdeal.exists_le_maximal q.isPrime.ne_top
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hM
  refine ⟨x, ?_⟩
  intro j
  let v : MvPolynomial J ℂ := MvPolynomial.X j - MvPolynomial.C (y j)
  have hv : v ∈ m.asIdeal := by
    apply (MvPolynomial.mem_vanishingIdeal_singleton_iff y _).mpr
    simp [v]
  have hvq : φ v ∈ q.asIdeal := by
    change v ∈ (PrimeSpectrum.comap φ.toRingHom q).asIdeal
    rwa [hq]
  have hMx := hle hvq
  rw [hx] at hMx
  have he := (MvPolynomial.mem_vanishingIdeal_singleton_iff x _).mp hMx
  simpa [φ, v, MvPolynomial.aeval_eq_eval, sub_eq_zero] using he

lemma dense_image_interior_of_nonempty {I J : Type} [Finite I] [Finite J] (F : J → MvPolynomial I ℂ)
    (h : (interior (Set.range (fun x : I → ℂ => fun j => MvPolynomial.eval x (F j)))).Nonempty) :
    Dense (interior (Set.range (fun x : I → ℂ => fun j => MvPolynomial.eval x (F j)))) := by
  classical
  let image := Set.range (fun x : I → ℂ => fun j => MvPolynomial.eval x (F j))
  have hinj : Function.Injective (MvPolynomial.aeval F : MvPolynomial J ℂ →ₐ[ℂ] MvPolynomial I ℂ) := by
    apply algebraicIndependent_iff_injective_aeval.mp
    apply algebraicIndependent_iff.mpr
    intro Q hQ
    by_contra hne
    have hs : image ⊆ {y : J → ℂ | MvPolynomial.eval y Q = 0} := by
      rintro _ ⟨x, rfl⟩
      change MvPolynomial.eval (fun j => MvPolynomial.eval x (F j)) Q = 0
      rw [← eval_substitution F x Q, hQ, map_zero]
    obtain ⟨y, hy⟩ := h
    have bad := interior_mono hs hy
    rw [interior_polynomial_zero_locus Q hne] at bad
    exact bad
  obtain ⟨P, hP, hsurj⟩ := principal_open_in_image F hinj
  let Z := {y : J → ℂ | MvPolynomial.eval y P = 0}
  have ho : IsOpen Zᶜ := (isClosed_eq (MvPolynomial.continuous_eval P) continuous_const).isOpen_compl
  have hd : Dense Zᶜ := interior_eq_empty_iff_dense_compl.mp (interior_polynomial_zero_locus P hP)
  apply hd.mono
  apply interior_maximal _ ho
  intro y hy
  obtain ⟨x, hx⟩ := hsurj y hy
  exact ⟨x, funext hx⟩

/-- The derivative of each coordinate is the sum of its three factor variations. -/
lemma trilinear_image_has_interior {I J S : Type} [Fintype I] [Fintype J] [Fintype S]
    (a b c : S → J → I) (base : I → ℂ)
    (hspan : ∀ y : J → ℂ, ∃ z : I → ℂ, ∀ j,
      y j = ∑ t : S, (z (a t j) * (base (b t j) * base (c t j)) +
        base (a t j) * (z (b t j) * base (c t j)) +
        base (a t j) * (base (b t j) * z (c t j)))) :
    (interior (Set.range (fun x : I → ℂ => fun j : J =>
      ∑ t : S, x (a t j) * (x (b t j) * x (c t j))))).Nonempty := by
  classical
  let φ (x : I → ℂ) (j : J) := ∑ t : S, x (a t j) * (x (b t j) * x (c t j))
  let pr (i : I) : (I → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj i
  let D : (I → ℂ) →L[ℂ] (J → ℂ) := ContinuousLinearMap.pi fun j =>
    ∑ t : S, (base (a t j) • (base (b t j) • pr (c t j) + base (c t j) • pr (b t j)) +
      (base (b t j) * base (c t j)) • pr (a t j))
  have hder : HasStrictFDerivAt φ D base := by
    apply hasStrictFDerivAt_pi.mpr
    intro j
    apply HasStrictFDerivAt.fun_sum
    intro t _
    exact (pr (a t j)).hasStrictFDerivAt.fun_mul
      ((pr (b t j)).hasStrictFDerivAt.fun_mul (pr (c t j)).hasStrictFDerivAt)
  have hsurj : Function.Surjective D := by
    intro y
    obtain ⟨z, hz⟩ := hspan y
    refine ⟨z, funext fun j => ?_⟩
    rw [hz j]
    simp only [D, ContinuousLinearMap.pi_apply, _root_.sum_apply,
      _root_.add_apply, _root_.smul_apply, smul_eq_mul, pr,
      ContinuousLinearMap.proj_apply]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hN : Set.range φ ∈ 𝓝 (φ base) := by
    rw [← hder.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hsurj)]
    exact Filter.range_mem_map
  exact ⟨φ base, mem_interior_iff_mem_nhds.mpr hN⟩

def index_nil_equiv : HolorIndex [] ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[], .nil⟩
  left_inv := by rintro ⟨l, h⟩; cases h; rfl
  right_inv := by intro x; cases x; rfl

lemma finite_index (ds : List ℕ) : Finite (HolorIndex ds) := by
  induction ds with
  | nil => exact Finite.of_equiv Unit index_nil_equiv.symm
  | cons n ds ih =>
    let _ : Finite (HolorIndex ds) := ih
    exact Finite.of_equiv (Fin n × HolorIndex ds) (index_cons_equiv n ds).symm

lemma eval_holor_sum {ds : List ℕ} {r : ℕ} (u : Fin r → Holor ℂ ds) (j : HolorIndex ds) :
    (∑ i, u i) j = ∑ i, u i j :=
  Finset.sum_apply (M := fun _ : HolorIndex ds => ℂ) j Finset.univ (fun i x => u i x)

def point {d e f : ℕ} (i : Fin d) (j : Fin e) (k : Fin f) : HolorIndex [d,e,f] :=
  ⟨[i.val,j.val,k.val], .cons i.isLt (.cons j.isLt (.cons k.isLt .nil))⟩

lemma point_surjective {d e f : ℕ} (z : HolorIndex [d,e,f]) :
    ∃ i j k, z = point i j k := by
  obtain ⟨⟨i,z⟩,rfl⟩ := (index_cons_equiv d [e,f]).symm.surjective z
  obtain ⟨⟨j,z⟩,rfl⟩ := (index_cons_equiv e [f]).symm.surjective z
  obtain ⟨⟨k,z⟩,rfl⟩ := (index_cons_equiv f []).symm.surjective z
  obtain ⟨⟨⟩,rfl⟩ := index_nil_equiv.symm.surjective z
  exact ⟨i,j,k,rfl⟩

def entry {n : ℕ} (i : HolorIndex [n]) : Fin n := (index_cons_equiv n [] i).1

end ThreeEven.Dominance

namespace Critical

open MvPolynomial ThreeEven

/-- The tangent spaces to the rank-one tensors at the points `(a t, b t, c t)` span the space of
all tensors of format `d × e × f`. -/
def SpansOn3 (d e f r : ℕ) : Prop :=
  ∃ a : Fin r → Fin d → ℂ, ∃ b : Fin r → Fin e → ℂ, ∃ c : Fin r → Fin f → ℂ,
    ∀ T : Fin d → Fin e → Fin f → ℂ, ∃ u : Fin r → Fin d → ℂ, ∃ v : Fin r → Fin e → ℂ,
      ∃ w : Fin r → Fin f → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i * (b t j * c t k) + a t i * (v t j * c t k) +
          a t i * (b t j * w t k))

abbrev Coord (d e f : ℕ) := HolorIndex [d, e, f]
abbrev Par (d e f r : ℕ) := Fin r × (Fin d ⊕ (Fin e ⊕ Fin f))

def gfirst {d e f r : ℕ} (t : Fin r) (z : Coord d e f) : Par d e f r :=
  (t, Sum.inl (Dominance.entry (HolorIndex.take (ds₁ := [d]) (ds₂ := [e, f]) z)))

def gsecond {d e f r : ℕ} (t : Fin r) (z : Coord d e f) : Par d e f r :=
  (t, Sum.inr (.inl (Dominance.entry (HolorIndex.take (ds₁ := [e]) (ds₂ := [f])
    (HolorIndex.drop (ds₁ := [d]) (ds₂ := [e, f]) z)))))

def gthird {d e f r : ℕ} (t : Fin r) (z : Coord d e f) : Par d e f r :=
  (t, Sum.inr (.inr (Dominance.entry (HolorIndex.drop (ds₁ := [e]) (ds₂ := [f])
    (HolorIndex.drop (ds₁ := [d]) (ds₂ := [e, f]) z)))))

def gpack {d e f r : ℕ} (a : Fin r → Fin d → ℂ) (b : Fin r → Fin e → ℂ) (c : Fin r → Fin f → ℂ)
    (q : Par d e f r) : ℂ :=
  q.2.elim (a q.1) (Sum.elim (b q.1) (c q.1))

open Set Arxiv.«0805.3777» in
/-- The theorem `ThreeEven.upper` for a general format and a general number of points:
surjectivity of the tangent map at one parameter gives a dense open set of tensors of rank at
most `r`. -/
theorem upper3 (d e f r : ℕ) (hs : SpansOn3 d e f r) :
    ∃ U : Set (Holor ℂ [d, e, f]), IsOpen U ∧ Dense U ∧ ∀ T ∈ U, T.cprank ≤ r := by
  classical
  obtain ⟨a,b,c,hspan⟩ := hs
  let _ : Finite (Coord d e f) := Dominance.finite_index _
  let _ : Fintype (Coord d e f) := Fintype.ofFinite _
  let φ (x : Par d e f r → ℂ) (j : Coord d e f) :=
    ∑ t : Fin r, x (gfirst t j) * (x (gsecond t j) * x (gthird t j))
  have hopen : (interior (Set.range φ)).Nonempty := by
    apply Dominance.trilinear_image_has_interior gfirst gsecond gthird (gpack a b c)
    intro y
    obtain ⟨u,v,w,h⟩ := hspan fun i j k => y (Dominance.point i j k)
    refine ⟨gpack u v w, ?_⟩
    intro z
    obtain ⟨i,j,k,rfl⟩ := Dominance.point_surjective z
    exact h i j k
  let F (j : Coord d e f) : MvPolynomial (Par d e f r) ℂ :=
    ∑ t : Fin r, MvPolynomial.X (gfirst t j) *
      (MvPolynomial.X (gsecond t j) * MvPolynomial.X (gthird t j))
  have he : (fun x : Par d e f r → ℂ => fun j => MvPolynomial.eval x (F j)) = φ := by
    funext x j
    simp [F, φ]
  have hd := Dominance.dense_image_interior_of_nonempty F (by rw [he]; exact hopen)
  rw [he] at hd
  refine ⟨interior (Set.range φ), isOpen_interior, hd, ?_⟩
  intro T hT
  obtain ⟨x,rfl⟩ := interior_subset hT
  let xa (t : Fin r) (i : HolorIndex [d]) := x (t, Sum.inl (Dominance.entry i))
  let xb (t : Fin r) (j : HolorIndex [e]) := x (t, Sum.inr (.inl (Dominance.entry j)))
  let xc (t : Fin r) (k : HolorIndex [f]) := x (t, Sum.inr (.inr (Dominance.entry k)))
  have hx : (φ x : Holor ℂ [d,e,f]) = ∑ t, Holor.mul (xa t) (Holor.mul (xb t) (xc t)) := by
    funext j
    rw [Dominance.eval_holor_sum]
    rfl
  rw [hx]
  exact Nat.find_min' _ (Dominance.tensor_sum_rank xa xb xc)

/-! ### A spanning configuration -/

abbrev SP (d e r : ℕ) := Fin r × (Fin d ⊕ Fin e)
abbrev SRow (d e : ℕ) := Fin d × Fin e
abbrev SCol (d e r : ℕ) := Fin r ⊕ (Fin d ⊕ Fin e)

/-- The matrix of the map `(l, u, v) ↦ ∑ t, l t • a t ⊗ b t + u ⊗ b s + a s ⊗ v`, where
`a t = z (t, inl ·)` and `b t = z (t, inr ·)`. -/
def smat {d e r : ℕ} {K : Type} [CommSemiring K] (z : SP d e r → K) (s : Fin r) :
    Matrix (SRow d e) (SCol d e r) K
  | (i, j), Sum.inl t => z (t, Sum.inl i) * z (t, Sum.inr j)
  | (i, j), Sum.inr (Sum.inl i') => if i' = i then z (s, Sum.inr j) else 0
  | (i, j), Sum.inr (Sum.inr j') => if j' = j then z (s, Sum.inl i) else 0

lemma saction {d e r : ℕ} (z : SP d e r → ℂ) (s : Fin r) (y : SCol d e r → ℂ)
    (i : Fin d) (j : Fin e) :
    (smat z s).mulVec y (i, j) =
      ∑ t, z (t, Sum.inl i) * z (t, Sum.inr j) * y (Sum.inl t) +
        y (Sum.inr (Sum.inl i)) * z (s, Sum.inr j) +
        z (s, Sum.inl i) * y (Sum.inr (Sum.inr j)) := by
  change (∑ q : SCol d e r, smat z s (i, j) q * y q) = _
  simp only [Fintype.sum_sum_type, smat, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  ring

lemma seval_matrix {d e r : ℕ} (z : SP d e r → ℂ) (s : Fin r) :
    (smat (MvPolynomial.X : SP d e r → MvPolynomial (SP d e r) ℂ) s).map (eval z) =
      smat z s := by
  ext ⟨i, j⟩ q
  rcases q with t | i' | j'
  · simp [Matrix.map_apply, smat]
  · by_cases hu : i' = i <;> simp [Matrix.map_apply, smat, hu]
  · by_cases hu : j' = j <;> simp [Matrix.map_apply, smat, hu]

/-- For a single index `s` the map is surjective at a suitable parameter: put the point `s` at
`(e₀, e₀)` and the other points on the pairs `(e_{i+1}, e_{j+1})`. -/
lemma witness {D E r : ℕ} (h : D * E < r) (s : Fin r) :
    ∃ z : SP (D + 1) (E + 1) r → ℂ, Function.Surjective (smat z s).mulVec := by
  classical
  obtain ⟨g, hg, hgs⟩ : ∃ g : Fin D × Fin E → Fin r, Function.Injective g ∧ ∀ q, g q ≠ s := by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have hle : D * E ≤ r' := by omega
    refine ⟨fun q => s.succAbove (Fin.castLE hle (finProdFinEquiv q)), ?_, fun q => ?_⟩
    · exact Fin.succAbove_right_injective.comp
        ((Fin.castLE_injective hle).comp finProdFinEquiv.injective)
    · exact Fin.succAbove_ne s _
  let φ : Fin r → Fin (D + 1) × Fin (E + 1) :=
    Function.extend g (fun q => (q.1.succ, q.2.succ)) (fun _ => (0, 0))
  have hφg : ∀ q, φ (g q) = (q.1.succ, q.2.succ) := fun q => hg.extend_apply _ _ q
  have hφs : φ s = (0, 0) :=
    Function.extend_apply' _ _ s (fun ⟨q, hq⟩ => hgs q hq)
  let z : SP (D + 1) (E + 1) r → ℂ := fun p =>
    Sum.elim (fun i => if i = (φ p.1).1 then (1 : ℂ) else 0)
      (fun j => if j = (φ p.1).2 then (1 : ℂ) else 0) p.2
  refine ⟨z, ?_⟩
  intro Y
  let y0 : Fin r → ℂ := Function.extend g (fun q => Y (q.1.succ, q.2.succ)) (fun _ => 0)
  let y : SCol (D + 1) (E + 1) r → ℂ := Sum.elim y0
    (Sum.elim (fun i => Y (i, 0)) (fun j => if j = 0 then 0 else Y (0, j)))
  refine ⟨y, ?_⟩
  funext ⟨i, j⟩
  rw [saction]
  have hsum : ∑ t, z (t, Sum.inl i) * z (t, Sum.inr j) * y (Sum.inl t) =
      ∑ q : Fin D × Fin E, (if i = q.1.succ then (1 : ℂ) else 0) *
        (if j = q.2.succ then (1 : ℂ) else 0) * Y (q.1.succ, q.2.succ) := by
    symm
    apply Fintype.sum_of_injective g hg
    · intro t ht
      have hy0 : y0 t = 0 := Function.extend_apply' _ _ t (fun ⟨q, hq⟩ => ht ⟨q, hq⟩)
      show z (t, Sum.inl i) * z (t, Sum.inr j) * y0 t = 0
      rw [hy0, mul_zero]
    · intro q
      show _ = z (g q, Sum.inl i) * z (g q, Sum.inr j) * y0 (g q)
      have hy0 : y0 (g q) = Y (q.1.succ, q.2.succ) := hg.extend_apply _ _ q
      rw [hy0]
      simp only [z, Sum.elim_inl, Sum.elim_inr, hφg]
  rw [hsum]
  simp only [z, y, Sum.elim_inl, Sum.elim_inr, hφs]
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => simp [(Fin.succ_ne_zero _).symm]
    | succ j' => simp [(Fin.succ_ne_zero _).symm, Fin.succ_ne_zero]
  | succ i' =>
    induction j using Fin.cases with
    | zero => simp [(Fin.succ_ne_zero _).symm, Fin.succ_ne_zero]
    | succ j' =>
      simp [Fintype.sum_prod_type, Fin.succ_ne_zero, Fin.succ_inj, Finset.sum_ite_eq]

/-- One choice of the points for which the map is surjective for every index. -/
lemma common3 {D E r : ℕ} (h : D * E < r) :
    ∃ z : SP (D + 1) (E + 1) r → ℂ, ∀ s, Function.Surjective (smat z s).mulVec := by
  classical
  have separate (s : Fin r) : ∃ z : SP (D + 1) (E + 1) r → ℂ, Function.Surjective
      ((smat (MvPolynomial.X : SP (D + 1) (E + 1) r → MvPolynomial (SP (D + 1) (E + 1) r) ℂ)
        s).map (eval z)).mulVec := by
    obtain ⟨z, hz⟩ := witness h s
    exact ⟨z, by rw [seval_matrix]; exact hz⟩
  obtain ⟨z, _, hz⟩ := Grid.simultaneous_surjectivity
    (fun s : Fin r => smat (MvPolynomial.X :
      SP (D + 1) (E + 1) r → MvPolynomial (SP (D + 1) (E + 1) r) ℂ) s) separate 1 one_ne_zero
  refine ⟨z, fun s => ?_⟩
  have h1 := hz s
  rwa [seval_matrix] at h1

/-- If `r ≥ f` and `r > D E`, there are `r` points of the format `(D+1) × (E+1) × f` whose
tangent spaces span: the first `f` points carry the basis vectors of the third factor. -/
theorem spans3 {D E f r : ℕ} (hfr : f ≤ r) (h : D * E < r) :
    SpansOn3 (D + 1) (E + 1) f r := by
  classical
  obtain ⟨z, hz⟩ := common3 (D := D) (E := E) h
  refine ⟨fun t i => z (t, Sum.inl i), fun t j => z (t, Sum.inr j),
    fun t k => if (k : ℕ) = (t : ℕ) then 1 else 0, ?_⟩
  intro T
  choose y hy using fun k : Fin f => hz (Fin.castLE hfr k)
    (fun p : SRow (D + 1) (E + 1) => T p.1 p.2 k)
  refine ⟨fun t i => if ht : (t : ℕ) < f then y ⟨t, ht⟩ (Sum.inr (Sum.inl i)) else 0,
    fun t j => if ht : (t : ℕ) < f then y ⟨t, ht⟩ (Sum.inr (Sum.inr j)) else 0,
    fun t k => y k (Sum.inl t), ?_⟩
  intro i j k
  have hk : (smat z (Fin.castLE hfr k)).mulVec (y k) (i, j) = T i j k := congrFun (hy k) (i, j)
  rw [saction] at hk
  have key : ∀ F : Fin r → ℂ,
      ∑ t, F t * (if (k : ℕ) = (t : ℕ) then (1 : ℂ) else 0) = F (Fin.castLE hfr k) := by
    intro F
    rw [Finset.sum_eq_single (Fin.castLE hfr k)]
    · simp
    · intro t _ ht
      have hne : (k : ℕ) ≠ (t : ℕ) := fun h' => ht (Fin.ext (by simp [h']))
      simp [hne]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  have hU : (if ht : ((Fin.castLE hfr k : Fin r) : ℕ) < f then
      y ⟨(Fin.castLE hfr k : Fin r), ht⟩ (Sum.inr (Sum.inl i)) else 0) =
      y k (Sum.inr (Sum.inl i)) := dif_pos k.2
  have hV : (if ht : ((Fin.castLE hfr k : Fin r) : ℕ) < f then
      y ⟨(Fin.castLE hfr k : Fin r), ht⟩ (Sum.inr (Sum.inr j)) else 0) =
      y k (Sum.inr (Sum.inr j)) := dif_pos k.2
  rw [← hk]
  simp only [Finset.sum_add_distrib, ← mul_assoc]
  rw [key (fun t => (if ht : (t : ℕ) < f then y ⟨t, ht⟩ (Sum.inr (Sum.inl i)) else 0) *
      z (t, Sum.inr j)),
    key (fun t => z (t, Sum.inl i) *
      (if ht : (t : ℕ) < f then y ⟨t, ht⟩ (Sum.inr (Sum.inr j)) else 0))]
  simp only [hU, hV]
  ring

end Critical

namespace Critical

section Bridge

variable {d₁ d₂ d₃ : ℕ}

/-- The index `(c, i, j)` of a `d₁ × d₂ × d₃` holor. -/
def ix (c : Fin d₁) (i : Fin d₂) (j : Fin d₃) : HolorIndex [d₁, d₂, d₃] :=
  ⟨[c.1, i.1, j.1], .cons c.2 (.cons i.2 (.cons j.2 .nil))⟩

theorem ix_surjective (t : HolorIndex [d₁, d₂, d₃]) : ∃ c i j, t = ix c i j := by
  obtain ⟨l, h⟩ := t
  cases h with
  | cons ha h =>
    cases h with
    | cons hb h =>
      cases h with
      | cons hc h =>
        cases h
        exact ⟨⟨_, ha⟩, ⟨_, hb⟩, ⟨_, hc⟩, rfl⟩

/-- Entry `(c, i, j)` of a `d₁ × d₂ × d₃` holor. -/
def ev (T : Holor ℂ [d₁, d₂, d₃]) (c : Fin d₁) (i : Fin d₂) (j : Fin d₃) : ℂ :=
  T (ix c i j)

theorem holor_ext {T T' : Holor ℂ [d₁, d₂, d₃]} (h : ∀ c i j, ev T c i j = ev T' c i j) :
    T = T' := by
  funext t
  obtain ⟨c, i, j, rfl⟩ := ix_surjective t
  exact h c i j

theorem ev_zero (c : Fin d₁) (i : Fin d₂) (j : Fin d₃) : ev (0 : Holor ℂ [d₁, d₂, d₃]) c i j = 0 :=
  rfl

theorem ev_add (T T' : Holor ℂ [d₁, d₂, d₃]) (c : Fin d₁) (i : Fin d₂) (j : Fin d₃) :
    ev (T + T') c i j = ev T c i j + ev T' c i j :=
  rfl

theorem ev_sum {ι : Type} (s : Finset ι) (f : ι → Holor ℂ [d₁, d₂, d₃]) (c : Fin d₁) (i : Fin d₂)
    (j : Fin d₃) : ev (∑ l ∈ s, f l) c i j = ∑ l ∈ s, ev (f l) c i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ev_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ev_add, ih]

theorem headI_lt {d : ℕ} {ds : List ℕ} (t : HolorIndex (d :: ds)) : t.1.headI < d := by
  obtain ⟨l, h⟩ := t
  cases h with
  | cons ha _ => exact ha

/-- The first coordinate of a holor index. -/
def idxHead {d : ℕ} {ds : List ℕ} (t : HolorIndex (d :: ds)) : Fin d :=
  ⟨t.1.headI, headI_lt t⟩

/-- A vector as a one-dimensional holor. -/
def vec {k : ℕ} (u : Fin k → ℂ) : Holor ℂ [k] := fun t => u (idxHead t)

/-- The scalar holor `1`. -/
def one0 : Holor ℂ [] := fun _ => 1

/-- The rank-one holor `u ⊗ v ⊗ w`. -/
def r1 (u : Fin d₁ → ℂ) (v : Fin d₂ → ℂ) (w : Fin d₃ → ℂ) : Holor ℂ [d₁, d₂, d₃] :=
  Holor.mul (vec u) (Holor.mul (vec v) (Holor.mul (vec w) one0))

theorem ev_r1 (u : Fin d₁ → ℂ) (v : Fin d₂ → ℂ) (w : Fin d₃ → ℂ) (c : Fin d₁) (i : Fin d₂)
    (j : Fin d₃) : ev (r1 u v w) c i j = u c * v i * w j := by
  show u c * (v i * (w j * 1)) = _
  ring

theorem cprankMax1_r1 (u : Fin d₁ → ℂ) (v : Fin d₂ → ℂ) (w : Fin d₃ → ℂ) :
    Holor.CPRankMax1 (r1 u v w) :=
  .cons _ _ (.cons _ _ (.cons _ _ (.nil _)))

theorem cprankMax1_cons {α : Type} [Mul α] {d : ℕ} {ds : List ℕ} {x : Holor α (d :: ds)}
    (h : Holor.CPRankMax1 x) :
    ∃ (u : Holor α [d]) (y : Holor α ds), Holor.CPRankMax1 y ∧ x = Holor.mul u y := by
  cases h with
  | cons u y hy => exact ⟨u, y, hy, rfl⟩

/-- The one-coordinate holor index `[i]`. -/
def ix1 {k : ℕ} (i : Fin k) : HolorIndex [k] :=
  ⟨[i.1], .cons i.2 .nil⟩

theorem cprankMax1_iff {x : Holor ℂ [d₁, d₂, d₃]} :
    Holor.CPRankMax1 x ↔ ∃ u v w, x = r1 u v w := by
  constructor
  · intro h
    obtain ⟨u₁, y₁, h₁, rfl⟩ := cprankMax1_cons h
    obtain ⟨u₂, y₂, h₂, rfl⟩ := cprankMax1_cons h₁
    obtain ⟨u₃, y₃, -, rfl⟩ := cprankMax1_cons h₂
    refine ⟨fun i => u₁ (ix1 i), fun j => u₂ (ix1 j), fun k => u₃ (ix1 k) * y₃ ⟨[], .nil⟩,
      holor_ext fun c i j => ?_⟩
    rw [ev_r1]
    show u₁ (ix1 c) * (u₂ (ix1 i) * (u₃ (ix1 j) * y₃ ⟨[], .nil⟩)) = _
    ring
  · rintro ⟨u, v, w, rfl⟩
    exact cprankMax1_r1 u v w

/-- A holor of CP rank at most `n` is a sum of `n` holors of rank at most one. -/
theorem exists_sum_of_cprankMax {α : Type} [Mul α] [AddCommMonoid α] {ds : List ℕ} {k : ℕ}
    {x : Holor α ds} (h : Holor.CPRankMax k x) :
    ∃ f : Fin k → Holor α ds, (∀ l, Holor.CPRankMax1 (f l)) ∧ x = ∑ l, f l := by
  induction h with
  | zero => exact ⟨Fin.elim0, fun l => l.elim0, by simp⟩
  | succ n x y hx _ ih =>
    obtain ⟨f, hf, rfl⟩ := ih
    refine ⟨Fin.cons x f, fun l => Fin.cases hx hf l, ?_⟩
    rw [Fin.sum_univ_succ]
    rfl

theorem cprankMax_cprank {ds : List ℕ} (x : Holor ℂ ds) : Holor.CPRankMax x.cprank x :=
  @Nat.find_spec (fun n => Holor.CPRankMax n x) (Classical.decPred _)
    ⟨ds.prod, Holor.cprankMax_upper_bound x⟩

theorem cprank_le_of_cprankMax {ds : List ℕ} {x : Holor ℂ ds} {k : ℕ}
    (h : Holor.CPRankMax k x) : x.cprank ≤ k :=
  @Nat.find_min' (fun n => Holor.CPRankMax n x) (Classical.decPred _)
    ⟨ds.prod, Holor.cprankMax_upper_bound x⟩ k h

theorem cprank_le_of_sum {ι : Type} [Fintype ι] (T : Holor ℂ [d₁, d₂, d₃]) (u : ι → Fin d₁ → ℂ)
    (v : ι → Fin d₂ → ℂ) (w : ι → Fin d₃ → ℂ)
    (h : ∀ c i j, ev T c i j = ∑ l, u l c * v l i * w l j) : T.cprank ≤ Fintype.card ι := by
  have hT : T = ∑ l, r1 (u l) (v l) (w l) := by
    refine holor_ext fun c i j => ?_
    rw [ev_sum, h]
    exact Finset.sum_congr rfl fun l _ => (ev_r1 _ _ _ _ _ _).symm
  have hr := Holor.cprankMax_sum (n := 1) Finset.univ (fun l => r1 (u l) (v l) (w l))
    fun l _ => Holor.cprankMax_1 (cprankMax1_r1 _ _ _)
  rw [Finset.card_univ, mul_one, ← hT] at hr
  exact cprank_le_of_cprankMax hr

theorem exists_sum_of_cprank (T : Holor ℂ [d₁, d₂, d₃]) :
    ∃ (u : Fin T.cprank → Fin d₁ → ℂ) (v : Fin T.cprank → Fin d₂ → ℂ)
      (w : Fin T.cprank → Fin d₃ → ℂ), ∀ c i j, ev T c i j = ∑ l, u l c * v l i * w l j := by
  obtain ⟨f, hf, hT⟩ := exists_sum_of_cprankMax (cprankMax_cprank T)
  choose u v w huvw using fun l => cprankMax1_iff.mp (hf l)
  refine ⟨u, v, w, fun c i j => ?_⟩
  conv_lhs => rw [hT]
  rw [ev_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [huvw, ev_r1]

theorem ix_injective {c c' : Fin d₁} {i i' : Fin d₂} {j j' : Fin d₃}
    (h : ix c i j = ix c' i' j') : c = c' ∧ i = i' ∧ j = j' := by
  have h1 := congrArg Subtype.val h
  simp only [ix, List.cons.injEq, and_true] at h1
  exact ⟨Fin.ext h1.1, Fin.ext h1.2.1, Fin.ext h1.2.2⟩

/-- Every tensor of format `d₁ × d₂ × d₃` has rank at most `d₁ d₂`. -/
theorem cprank_le_mul (T : Holor ℂ [d₁, d₂, d₃]) : T.cprank ≤ d₁ * d₂ := by
  classical
  have h := cprank_le_of_sum (ι := Fin d₁ × Fin d₂) T (fun p c => if c = p.1 then 1 else 0)
    (fun p i => if i = p.2 then 1 else 0) (fun p j => ev T p.1 p.2 j) (by
      intro c i j
      rw [Fintype.sum_prod_type]
      simp [Finset.sum_ite_eq])
  simpa using h

end Bridge

section Lower

open MvPolynomial ThreeEven

open Arxiv.«0805.3777» in
/-- A nonzero `N × N` minor of the flattening `d₃ × (d₁ d₂)` forces rank at least `N`, and the
minor is a nonzero polynomial. -/
theorem lower3 (d₁ d₂ d₃ N : ℕ) (hN3 : N ≤ d₃) (hN12 : N ≤ d₁ * d₂) :
    ∃ U : Set (Holor ℂ [d₁, d₂, d₃]), IsOpen U ∧ Dense U ∧ ∀ T ∈ U, N ≤ T.cprank := by
  classical
  let e₁ : Fin N → Fin d₃ := Fin.castLE hN3
  let e₂ : Fin N → Fin d₁ × Fin d₂ := fun a => finProdFinEquiv.symm (Fin.castLE hN12 a)
  have he₁ : Function.Injective e₁ := Fin.castLE_injective hN3
  have he₂ : Function.Injective e₂ :=
    finProdFinEquiv.symm.injective.comp (Fin.castLE_injective hN12)
  let S : Holor ℂ [d₁, d₂, d₃] → Matrix (Fin N) (Fin N) ℂ := fun T =>
    Matrix.of fun a b => ev T (e₂ b).1 (e₂ b).2 (e₁ a)
  let P : MvPolynomial (HolorIndex [d₁, d₂, d₃]) ℂ :=
    Matrix.det (Matrix.of fun a b : Fin N =>
      (X (ix (e₂ b).1 (e₂ b).2 (e₁ a)) : MvPolynomial (HolorIndex [d₁, d₂, d₃]) ℂ))
  have hP : ∀ T : Holor ℂ [d₁, d₂, d₃], eval T P = (S T).det := by
    intro T
    show eval T (Matrix.det _) = _
    rw [RingHom.map_det]
    congr 1
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, S, ev]
    exact eval_X _
  have hP0 : P ≠ 0 := by
    intro h0
    let T₀ : Holor ℂ [d₁, d₂, d₃] := fun t =>
      if ∃ a, t = ix (e₂ a).1 (e₂ a).2 (e₁ a) then 1 else 0
    have h1 : S T₀ = 1 := by
      ext a b
      show (if ∃ a', ix (e₂ b).1 (e₂ b).2 (e₁ a) = ix (e₂ a').1 (e₂ a').2 (e₁ a') then (1 : ℂ)
        else 0) = (1 : Matrix (Fin N) (Fin N) ℂ) a b
      rw [Matrix.one_apply]
      by_cases hab : a = b
      · subst hab
        rw [if_pos ⟨a, rfl⟩, if_pos rfl]
      · rw [if_neg hab, if_neg]
        rintro ⟨a', ha'⟩
        obtain ⟨h1, h2, h3⟩ := ix_injective ha'
        have hb : b = a' := he₂ (Prod.ext h1 h2)
        have ha : a = a' := he₁ h3
        exact hab (ha.trans hb.symm)
    have h2 := hP T₀
    rw [h0, map_zero, h1, Matrix.det_one] at h2
    exact zero_ne_one h2
  refine ⟨{T : Holor ℂ [d₁, d₂, d₃] | eval T P = 0}ᶜ, ?_, ?_, ?_⟩
  · exact (isClosed_eq (MvPolynomial.continuous_eval P) continuous_const).isOpen_compl
  · exact interior_eq_empty_iff_dense_compl.mp (Dimension.interior_polynomial_zero_locus P hP0)
  · intro T hT
    have hT' : eval T P ≠ 0 := hT
    obtain ⟨a, b, c, habc⟩ := exists_sum_of_cprank T
    have hprod : S T = (Matrix.of fun (x : Fin N) (l : Fin T.cprank) => c l (e₁ x)) *
        (Matrix.of fun (l : Fin T.cprank) (y : Fin N) => a l (e₂ y).1 * b l (e₂ y).2) := by
      ext x y
      simp only [S, Matrix.of_apply, Matrix.mul_apply, habc]
      exact Finset.sum_congr rfl fun l _ => by ring
    have hdet : (S T).det ≠ 0 := by
      rw [← hP]
      exact hT'
    have hunit : IsUnit (S T) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    have hrank : (S T).rank = N := by
      rw [Matrix.rank_of_isUnit _ hunit, Fintype.card_fin]
    have hle : (S T).rank ≤ T.cprank := by
      rw [hprod]
      exact (Matrix.rank_mul_le_left _ _).trans
        ((Matrix.rank_le_card_width _).trans_eq (Fintype.card_fin _))
    omega

end Lower

open Arxiv.«0805.3777» in
theorem main {m₁ m₂ m₃ : ℕ} (h₁ : 1 ≤ m₁) (h₁₂ : m₁ ≤ m₂) (h : (m₁ - 1) * (m₂ - 1) < m₃) :
    IsGenericRank [m₁, m₂, m₃] (min m₃ (m₁ * m₂)) := by
  obtain ⟨U, hUo, hUd, hU⟩ := lower3 m₁ m₂ m₃ (min m₃ (m₁ * m₂)) (min_le_left _ _)
    (min_le_right _ _)
  obtain ⟨V, hVo, hVd, hV⟩ : ∃ V : Set (Holor ℂ [m₁, m₂, m₃]), IsOpen V ∧ Dense V ∧
      ∀ T ∈ V, T.cprank ≤ min m₃ (m₁ * m₂) := by
    rcases le_or_gt (m₁ * m₂) m₃ with hle | hlt
    · refine ⟨Set.univ, isOpen_univ, dense_univ, fun T _ => ?_⟩
      rw [min_eq_right hle]
      exact cprank_le_mul T
    · rw [min_eq_left hlt.le]
      obtain ⟨D, rfl⟩ : ∃ D, m₁ = D + 1 := ⟨m₁ - 1, by omega⟩
      obtain ⟨E, rfl⟩ : ∃ E, m₂ = E + 1 := ⟨m₂ - 1, by omega⟩
      exact upper3 (D + 1) (E + 1) m₃ m₃ (spans3 le_rfl (by simpa using h))
  exact ⟨U ∩ V, hUo.inter hVo, hUd.inter_of_isOpen_left hVd hUo,
    fun T hT => le_antisymm (hV T hT.2) (hU T hT.1)⟩

end Critical

theorem OMA.solution : type_of% @Arxiv.«0805.3777».isGenericRank_of_gt_critical := by
  intro m₁ m₂ m₃ h₁ h₁₂ _ h
  exact Critical.main h₁ h₁₂ h
