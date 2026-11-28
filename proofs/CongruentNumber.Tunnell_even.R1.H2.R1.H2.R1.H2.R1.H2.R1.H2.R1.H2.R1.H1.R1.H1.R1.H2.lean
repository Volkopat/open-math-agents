import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1
import Mathlib

namespace TunnellGroupedPart1
open NumberField IsDedekindDomain
open scoped TensorProduct NumberField Classical
set_option maxHeartbeats 3000000 in
def Statement : Prop :=
∀ (D M:Type) [Field D] [NumberField D] [Field M] [NumberField M] [Algebra D M] [FiniteDimensional D M],
  let T:=AdeleRing (𝓞 D) D ⊗[D] M
  letI : Algebra M T:=Algebra.TensorProduct.rightAlgebra
  Nonempty (T≃ₐ[M]AdeleRing (𝓞 M) M)
end TunnellGroupedPart1

section

/-! Scalar extension of adèles decomposes into the local completion factors and respects the diagonal field embeddings. The integral lattices agree outside finitely many primes. -/
namespace TunnellSpectral
open Polynomial
theorem integral {K L:Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [NormedField L] [NormedAlgebra K L] [Algebra.IsAlgebraic K L]
    (V:ValuationSubring K) (hv:∀a:K, a∈V ↔ ‖a‖≤1) (x:L) (hx:‖x‖≤1) :
    letI : Algebra V L := Algebra.compHom L (algebraMap V K)
    IsIntegral V x := by
  classical
  letI : Algebra V L := Algebra.compHom L (algebraMap V K)
  letI : IsScalarTower V K L := .of_algebraMap_eq' rfl
  let p:=minpoly K x
  have hm : p.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have ht : ∀ i, p.coeff i∈V := by
    intro i
    apply (hv _).mpr
    rcases lt_trichotomy i p.natDegree with hi|hi|hi
    · have hval : spectralValueTerms p i ≤ 1 :=
        (le_ciSup (spectralValueTerms_bddAbove p) i).trans (show spectralNorm K L x≤1 by rw [←NormedAlgebra.norm_eq_spectralNorm K x];exact hx)
      rw [spectralValueTerms_of_lt_natDegree p hi] at hval
      by_contra! h
      exact (not_lt_of_ge hval) (Real.one_lt_rpow h (one_div_pos.mpr (sub_pos.mpr (by exact_mod_cast hi))))
    · rw [hi,hm.coeff_natDegree,norm_one]
    · rw [coeff_eq_zero_of_natDegree_lt hi,norm_zero];exact zero_le_one
  have hc : (p.coeffs : Set K) ⊆ V.toSubring := by
    intro y hy
    obtain ⟨i,_,rfl⟩ := Polynomial.mem_coeffs_iff.mp hy
    exact ht i
  let q : V[X] := p.toSubring V.toSubring hc
  have he : q.map (algebraMap V K) = p := Polynomial.map_toSubring _ _ _
  refine ⟨q,?_,?_⟩
  · exact (Polynomial.monic_toSubring _ _ _).mpr hm
  · change aeval x q=0
    rw [← Polynomial.aeval_map_algebraMap K x q,he]
    exact minpoly.aeval K x

end TunnellSpectral

/- ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.BaseChange -/
section
open scoped NumberField TensorProduct
open NumberField
noncomputable section
variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
 

abbrev RelativeAdeleRing :=
  NumberField.AdeleRing (𝓞 K) K ⊗[K] L
namespace RelativeIdeleGroup
end RelativeIdeleGroup
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.LocalComponent -/
section
open scoped NumberField TensorProduct
open NumberField IsDedekindDomain
noncomputable section
universe u v
variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
 

def infiniteAdeleComponentAlgHom
    (v : InfinitePlace K) :
    NumberField.AdeleRing (𝓞 K) K →ₐ[K]
      v.Completion :=
  (Pi.evalAlgHom K
      (fun w : InfinitePlace K => w.Completion) v).comp
    (AlgHom.fst K
      (NumberField.InfiniteAdeleRing K)
      (FiniteAdeleRing (𝓞 K) K))
@[simp]
theorem infiniteAdeleComponentAlgHom_apply
    (v : InfinitePlace K)
    (a : NumberField.AdeleRing (𝓞 K) K) :
    infiniteAdeleComponentAlgHom v a = a.1 v :=
  rfl
 

def relativeAdeleInfiniteComponent
    (v : InfinitePlace K) :
    RelativeAdeleRing K L →ₐ[K]
      v.Completion ⊗[K] L :=
  Algebra.TensorProduct.map
    (infiniteAdeleComponentAlgHom v)
    (AlgHom.id K L)
omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem relativeAdeleInfiniteComponent_tmul
    (v : InfinitePlace K)
    (a : NumberField.AdeleRing (𝓞 K) K) (x : L) :
    relativeAdeleInfiniteComponent
        (K := K) (L := L) v (a ⊗ₜ[K] x) =
      a.1 v ⊗ₜ[K] x := by
  simp [relativeAdeleInfiniteComponent]
 

def finiteAdeleComponentAlgHom
    (v : HeightOneSpectrum (𝓞 K)) :
    NumberField.AdeleRing (𝓞 K) K →ₐ[K]
      v.adicCompletion K :=
  { __ :=
      (RestrictedProduct.evalRingHom
        (fun w : HeightOneSpectrum (𝓞 K) =>
          w.adicCompletion K) v).comp
        (RingHom.snd
          (NumberField.InfiniteAdeleRing K)
          (FiniteAdeleRing (𝓞 K) K))
    commutes' := by
      intro x
      rfl }
@[simp]
theorem finiteAdeleComponentAlgHom_apply
    (v : HeightOneSpectrum (𝓞 K))
    (a : NumberField.AdeleRing (𝓞 K) K) :
    finiteAdeleComponentAlgHom v a = a.2 v :=
  rfl
omit [NumberField L] [FiniteDimensional K L] in
 

def relativeAdeleFiniteComponent
    (v : HeightOneSpectrum (𝓞 K)) :
    RelativeAdeleRing K L →ₐ[K]
      v.adicCompletion K ⊗[K] L :=
  Algebra.TensorProduct.map
    (finiteAdeleComponentAlgHom v)
    (AlgHom.id K L)
omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem relativeAdeleFiniteComponent_tmul
    (v : HeightOneSpectrum (𝓞 K))
    (a : NumberField.AdeleRing (𝓞 K) K) (x : L) :
    relativeAdeleFiniteComponent (K := K) (L := L) v
        (a ⊗ₜ[K] x) =
      a.2 v ⊗ₜ[K] x := by
  simp [relativeAdeleFiniteComponent]
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.Support -/
section
open scoped NumberField TensorProduct
open NumberField IsDedekindDomain
noncomputable section
universe u v
variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
 
abbrev RelativeAdeleBasisIndex :=
  Module.Free.ChooseBasisIndex K L
 

noncomputable def relativeExtensionBasis :
    Module.Basis (RelativeAdeleBasisIndex (K := K) (L := L)) K L :=
  Module.Free.chooseBasis K L
 
noncomputable def relativeAdeleBasis :
    Module.Basis (RelativeAdeleBasisIndex (K := K) (L := L))
      (NumberField.AdeleRing (𝓞 K) K)
      (RelativeAdeleRing K L) :=
  Algebra.TensorProduct.basis
    (NumberField.AdeleRing (𝓞 K) K)
    (relativeExtensionBasis (K := K) (L := L))
 
noncomputable def relativeAdeleCoefficient
    (z : RelativeAdeleRing K L)
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    NumberField.AdeleRing (𝓞 K) K :=
  (relativeAdeleBasis (K := K) (L := L)).repr z i
omit [NumberField L] in
 
theorem relativeAdele_eq_sum_tmul_coefficients
    (z : RelativeAdeleRing K L) :
    z =
      ∑ i : RelativeAdeleBasisIndex (K := K) (L := L),
        relativeAdeleCoefficient
            (K := K) (L := L) z i ⊗ₜ[K]
          relativeExtensionBasis (K := K) (L := L) i := by
  symm
  simpa [relativeAdeleCoefficient, relativeAdeleBasis,
    relativeExtensionBasis, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def] using
      (relativeAdeleBasis (K := K) (L := L)).sum_repr z
omit [NumberField L] in
 

theorem relativeAdeleFiniteComponent_eq_sum_tmul_coefficients
    (z : RelativeAdeleRing K L)
    (w : HeightOneSpectrum (𝓞 K)) :
    relativeAdeleFiniteComponent
        (K := K) (L := L) w z =
      ∑ i : RelativeAdeleBasisIndex (K := K) (L := L),
        (relativeAdeleCoefficient
            (K := K) (L := L) z i).2 w ⊗ₜ[K]
          relativeExtensionBasis (K := K) (L := L) i := by
  have h :=
    congrArg
      (relativeAdeleFiniteComponent
        (K := K) (L := L) w)
      (relativeAdele_eq_sum_tmul_coefficients
        (K := K) (L := L) z)
  simpa only [map_sum,
    relativeAdeleFiniteComponent_tmul] using h
omit [NumberField L] in
 

theorem relativeAdeleInfiniteComponent_eq_sum_tmul_coefficients
    (z : RelativeAdeleRing K L)
    (w : InfinitePlace K) :
    relativeAdeleInfiniteComponent
        (K := K) (L := L) w z =
      ∑ i : RelativeAdeleBasisIndex (K := K) (L := L),
        (relativeAdeleCoefficient
            (K := K) (L := L) z i).1 w ⊗ₜ[K]
          relativeExtensionBasis (K := K) (L := L) i := by
  have h :=
    congrArg
      (relativeAdeleInfiniteComponent
        (K := K) (L := L) w)
      (relativeAdele_eq_sum_tmul_coefficients
        (K := K) (L := L) z)
  simpa only [map_sum,
    relativeAdeleInfiniteComponent_tmul] using h
 

theorem finite_adeleNonIntegralPlaces
    (a : NumberField.AdeleRing (𝓞 K) K) :
    {w : HeightOneSpectrum (𝓞 K) |
      a.2 w ∉ w.adicCompletionIntegers K}.Finite :=
  Filter.eventually_cofinite.mp a.2.2
 

noncomputable def adeleNonIntegralPlaces
    (a : NumberField.AdeleRing (𝓞 K) K) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (finite_adeleNonIntegralPlaces (K := K) a).toFinset
@[simp]
theorem mem_adeleNonIntegralPlaces_iff
    (a : NumberField.AdeleRing (𝓞 K) K)
    (w : HeightOneSpectrum (𝓞 K)) :
    w ∈ adeleNonIntegralPlaces (K := K) a ↔
      a.2 w ∉ w.adicCompletionIntegers K := by
  exact
    Set.Finite.mem_toFinset
      (finite_adeleNonIntegralPlaces (K := K) a)
 

noncomputable def relativeAdeleCoefficientSupport
    (z : RelativeAdeleRing K L) :
    Finset (HeightOneSpectrum (𝓞 K)) := by
  classical
  exact Finset.univ.biUnion fun i =>
    adeleNonIntegralPlaces
      (K := K)
      (relativeAdeleCoefficient
        (K := K) (L := L) z i)
omit [NumberField L] in
@[simp]
theorem mem_relativeAdeleCoefficientSupport_iff
    (z : RelativeAdeleRing K L)
    (w : HeightOneSpectrum (𝓞 K)) :
    w ∈ relativeAdeleCoefficientSupport
        (K := K) (L := L) z ↔
      ∃ i : RelativeAdeleBasisIndex (K := K) (L := L),
        (relativeAdeleCoefficient
            (K := K) (L := L) z i).2 w ∉
          w.adicCompletionIntegers K := by
  classical
  simp [relativeAdeleCoefficientSupport]
omit [NumberField L] in
 


def RelativeBasisIntegralAt
    (w : HeightOneSpectrum (𝓞 K))
    (x : w.adicCompletion K ⊗[K] L) : Prop :=
  ∃ c :
      RelativeAdeleBasisIndex (K := K) (L := L) →
        w.adicCompletionIntegers K,
    x =
      ∑ i : RelativeAdeleBasisIndex (K := K) (L := L),
        ((c i : w.adicCompletionIntegers K) :
            w.adicCompletion K) ⊗ₜ[K]
          relativeExtensionBasis (K := K) (L := L) i
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.Adele.Coordinates -/
section
open scoped NumberField TensorProduct
open NumberField IsDedekindDomain
noncomputable section
universe u v
variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
 

noncomputable def relativeAdeleCoefficientLinearEquiv :
    RelativeAdeleRing K L ≃ₗ[
      NumberField.AdeleRing (𝓞 K) K]
      (RelativeAdeleBasisIndex (K := K) (L := L) →
        NumberField.AdeleRing (𝓞 K) K) :=
  (relativeAdeleBasis (K := K) (L := L)).equivFun
 
noncomputable def relativeAdeleOfCoefficients
    (a :
      RelativeAdeleBasisIndex (K := K) (L := L) →
        NumberField.AdeleRing (𝓞 K) K) :
    RelativeAdeleRing K L :=
  (relativeAdeleCoefficientLinearEquiv
    (K := K) (L := L)).symm a
omit [NumberField L] in
@[simp]
theorem relativeAdeleCoefficient_ofCoefficients
    (a :
      RelativeAdeleBasisIndex (K := K) (L := L) →
        NumberField.AdeleRing (𝓞 K) K)
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    relativeAdeleCoefficient
        (K := K) (L := L)
        (relativeAdeleOfCoefficients
          (K := K) (L := L) a) i =
      a i := by
  change
    relativeAdeleCoefficientLinearEquiv
        (K := K) (L := L)
        ((relativeAdeleCoefficientLinearEquiv
          (K := K) (L := L)).symm a) i =
      a i
  rw [LinearEquiv.apply_symm_apply]
end
end

/- ValuedFieldTheory.Valuation.AbsoluteValue.Extension -/
section
namespace AbsoluteValue
 
def Extends {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) : Prop :=
  ∀ x : K, w (algebraMap K L x) = v x
end AbsoluteValue
end

/- ValuedFieldTheory.Valuation.AbsoluteValue.Nonarchimedean -/
section
noncomputable section
open Filter
open scoped Topology
namespace AbsoluteValue
private theorem finset_sum_le
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    {ι : Type*} (s : Finset ι) (f : ι → K) :
    v (s.sum f) ≤ s.sum (fun i => v (f i)) := by
  classical
  refine Finset.induction_on s ?empty ?insert
  · simp
  · intro i s his ih
    rw [Finset.sum_insert his, Finset.sum_insert his]
    exact (v.add_le (f i) (s.sum f)).trans
      (by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left ih (v (f i)))
private theorem nat_bound_ge_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) {C : ℝ}
    (hC : ∀ n : ℕ, v (n : K) ≤ C) :
    1 ≤ C := by
  simpa using hC 1
 


private theorem add_pow_le_of_bounded_nat
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) {C : ℝ}
    (hC : ∀ n : ℕ, v (n : K) ≤ C) (x y : K) (n : ℕ) :
    v ((x + y) ^ n) ≤
      ((n + 1 : ℕ) : ℝ) * C * (max (v x) (v y)) ^ n := by
  classical
  let M : ℝ := max (v x) (v y)
  have hC_nonneg : 0 ≤ C :=
    (zero_le_one : (0 : ℝ) ≤ 1).trans
      (nat_bound_ge_one v hC)
  have hM_nonneg : 0 ≤ M :=
    (v.nonneg x).trans (le_max_left (v x) (v y))
  have hsum_le :
      v ((Finset.range (n + 1)).sum
          (fun m => x ^ m * y ^ (n - m) * (n.choose m : K))) ≤
        (Finset.range (n + 1)).sum
          (fun m => v (x ^ m * y ^ (n - m) * (n.choose m : K))) :=
    finset_sum_le v (Finset.range (n + 1))
      (fun m => x ^ m * y ^ (n - m) * (n.choose m : K))
  have hterm :
      ∀ m ∈ Finset.range (n + 1),
        v (x ^ m * y ^ (n - m) * (n.choose m : K)) ≤ C * M ^ n := by
    intro m hm
    have hmle : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hxpow : v (x ^ m) ≤ M ^ m := by
      rw [map_pow]
      exact pow_le_pow_left₀ (v.nonneg x) (le_max_left (v x) (v y)) m
    have hypow : v (y ^ (n - m)) ≤ M ^ (n - m) := by
      rw [map_pow]
      exact pow_le_pow_left₀ (v.nonneg y) (le_max_right (v x) (v y)) (n - m)
    have hxy :
        v (x ^ m) * v (y ^ (n - m)) ≤ M ^ m * M ^ (n - m) :=
      mul_le_mul hxpow hypow (v.nonneg (y ^ (n - m))) (pow_nonneg hM_nonneg m)
    have hchoose : v ((n.choose m : ℕ) : K) ≤ C := hC (n.choose m)
    calc
      v (x ^ m * y ^ (n - m) * (n.choose m : K))
          = v (x ^ m) * v (y ^ (n - m)) * v ((n.choose m : ℕ) : K) := by
              rw [map_mul, map_mul]
      _ ≤ (M ^ m * M ^ (n - m)) * C := by
              exact mul_le_mul hxy hchoose
                (v.nonneg ((n.choose m : ℕ) : K))
                (mul_nonneg (pow_nonneg hM_nonneg m)
                  (pow_nonneg hM_nonneg (n - m)))
      _ = C * M ^ n := by
              rw [← pow_add, Nat.add_sub_of_le hmle]
              ring
  calc
    v ((x + y) ^ n)
        = v ((Finset.range (n + 1)).sum
            (fun m => x ^ m * y ^ (n - m) * (n.choose m : K))) := by
            rw [add_pow]
    _ ≤ (Finset.range (n + 1)).sum
          (fun m => v (x ^ m * y ^ (n - m) * (n.choose m : K))) := hsum_le
    _ ≤ (Finset.range (n + 1)).sum (fun _m => C * M ^ n) :=
          Finset.sum_le_sum hterm
    _ = ((n + 1 : ℕ) : ℝ) * C * M ^ n := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
 

private theorem tendsto_linear_bound_rpow_inv
    {C : ℝ} (hC : 0 < C) :
    Tendsto
      (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)))
      atTop (𝓝 1) := by
  have hCroot :
      Tendsto (fun n : ℕ => C ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
    have hcont : ContinuousAt (fun t : ℝ => C ^ t) 0 :=
      Real.continuousAt_const_rpow hC.ne'
    have hzero : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hroot := hcont.tendsto.comp hzero
    change Tendsto (fun n : ℕ => C ^ ((n : ℝ)⁻¹)) atTop (𝓝 (C ^ (0 : ℝ))) at hroot
    simpa [Real.rpow_zero] using hroot
  have hshiftReal :
      Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / (1 * x + (-1)))) atTop (𝓝 1) :=
    tendsto_rpow_div_mul_add 1 1 (-1) zero_ne_one
  have hshiftNat :
      Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ ((n : ℝ)⁻¹)))
        atTop (𝓝 1) := by
    have hnatshift : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    refine (hshiftReal.comp hnatshift).congr' ?_
    exact Eventually.of_forall fun n => by
      simp [Nat.cast_add, Nat.cast_one, one_div, add_assoc]
  have htarget :
      Tendsto
        (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)))
        atTop (𝓝 (1 * 1)) := by
    refine (hshiftNat.mul hCroot).congr' ?_
    exact Eventually.of_forall fun n => by
      have hn_nonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
      have hmul :=
        (Real.mul_rpow (z := ((n : ℝ)⁻¹)) hn_nonneg (le_of_lt hC)).symm
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  simpa using htarget
 
private theorem add_le_root_bound_of_bounded_nat
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) {C : ℝ}
    (hC : ∀ n : ℕ, v (n : K) ≤ C) (x y : K)
    {n : ℕ} (hn : n ≠ 0) :
    v (x + y) ≤
      ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)) *
        max (v x) (v y) := by
  classical
  let M : ℝ := max (v x) (v y)
  have hC_pos : 0 < C :=
    zero_lt_one.trans_le (nat_bound_ge_one v hC)
  have hM_nonneg : 0 ≤ M :=
    (v.nonneg x).trans (le_max_left (v x) (v y))
  by_cases hMzero : M = 0
  · have hx_le_zero : v x ≤ 0 := by
      simpa [M, hMzero] using (le_max_left (v x) (v y))
    have hy_le_zero : v y ≤ 0 := by
      simpa [M, hMzero] using (le_max_right (v x) (v y))
    have hxzero : x = 0 := (v.eq_zero).mp (le_antisymm hx_le_zero (v.nonneg x))
    have hyzero : y = 0 := (v.eq_zero).mp (le_antisymm hy_le_zero (v.nonneg y))
    simp [hxzero, hyzero]
  · have hpow :
        (v (x + y)) ^ n ≤ ((n + 1 : ℕ) : ℝ) * C * M ^ n := by
      simpa [map_pow, M] using
        add_pow_le_of_bounded_nat v hC x y n
    have hright_nonneg :
        0 ≤ ((n + 1 : ℕ) : ℝ) * C * M ^ n := by
      exact mul_nonneg
        (mul_nonneg (by positivity) (le_of_lt hC_pos))
        (pow_nonneg hM_nonneg n)
    have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hroot :
        v (x + y) ≤
          (((n + 1 : ℕ) : ℝ) * C * M ^ n) ^ ((n : ℝ)⁻¹) := by
      rw [Real.le_rpow_inv_iff_of_pos (v.nonneg (x + y)) hright_nonneg hn_pos]
      simpa [Real.rpow_natCast] using hpow
    calc
      v (x + y)
          ≤ (((n + 1 : ℕ) : ℝ) * C * M ^ n) ^ ((n : ℝ)⁻¹) := hroot
      _ = ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)) * M := by
            have hcoef_nonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) * C :=
              mul_nonneg (by positivity) (le_of_lt hC_pos)
            rw [Real.mul_rpow hcoef_nonneg (pow_nonneg hM_nonneg n)]
            rw [Real.pow_rpow_inv_natCast hM_nonneg hn]
      _ = ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)) *
            max (v x) (v y) := by
            rfl
 
private theorem isNonarchimedean_of_bounded_nat
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : ∃ C : ℝ, ∀ n : ℕ, v (n : K) ≤ C) :
    IsNonarchimedean (v : K → ℝ) := by
  rcases hnonarch with ⟨C, hC⟩
  have hC_pos : 0 < C :=
    zero_lt_one.trans_le (nat_bound_ge_one v hC)
  intro x y
  let M : ℝ := max (v x) (v y)
  have hlim :
      Tendsto
        (fun n : ℕ =>
          ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)) * M)
        atTop (𝓝 M) := by
    simpa using
      (tendsto_linear_bound_rpow_inv hC_pos).mul
        (tendsto_const_nhds (x := M))
  have heventually :
      ∀ᶠ n : ℕ in atTop,
        v (x + y) ≤
          ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)) * M := by
    refine eventually_atTop.2 ⟨1, ?_⟩
    intro n hn
    exact add_le_root_bound_of_bounded_nat
      (v := v) hC x y (n := n) (by omega)
  have hle :
      v (x + y) ≤ M :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim heventually
  simpa [M] using hle
 

theorem isNonarchimedean_iff_bounded_nat
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    IsNonarchimedean (v : K → ℝ) ↔
      ∃ C : ℝ, ∀ n : ℕ, v (n : K) ≤ C := by
  constructor
  · intro h
    exact ⟨1, fun n => h.apply_natCast_le_one⟩
  · exact isNonarchimedean_of_bounded_nat v
end AbsoluteValue
end
end

/- ValuedFieldTheory.Valuation.AbsoluteValue.Completion -/
section
noncomputable section
open scoped Topology
namespace AbsoluteValue
universe u v w
 
noncomputable def completionAbsoluteValue
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ) :
    AbsoluteValue vK.Completion ℝ :=
  NormedField.toAbsoluteValue vK.Completion
 

@[simp]
theorem completionAbsoluteValue_coe
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ) (x : K) :
    completionAbsoluteValue vK (x : vK.Completion) = vK x := by
  change ‖(x : vK.Completion)‖ = vK x
  rw [UniformSpace.Completion.norm_coe]
  rfl
 
theorem completionAbsoluteValue_complete
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ) :
    CompleteSpace (WithAbs (completionAbsoluteValue vK)) := by
  let e := WithAbs.equiv (completionAbsoluteValue vK)
  have he : Isometry e :=
    AddMonoidHomClass.isometry_of_norm e.toRingHom fun _ ↦ rfl
  exact (completeSpace_congr (e := e.toEquiv) he.isUniformEmbedding).2 inferInstance
 
theorem completionAbsoluteValue_isNontrivial
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial) :
    (completionAbsoluteValue vK).IsNontrivial := by
  rcases hvK with ⟨x, hx0, hx1⟩
  refine ⟨(x : vK.Completion), ?_, ?_⟩
  · intro hx
    have hx' : (WithAbs.equiv vK).symm x = 0 :=
      UniformSpace.Completion.coe_injective (α := WithAbs vK) hx
    exact hx0 (by simpa using congrArg (WithAbs.equiv vK) hx')
  · simpa using hx1
 
noncomputable def toCompletion
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ) :
    K →+* vK.Completion :=
  UniformSpace.Completion.coeRingHom.comp
    (WithAbs.equiv vK).symm.toRingHom
 
@[simp]
theorem toCompletion_apply
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ) (x : K) :
    toCompletion vK x = ((WithAbs.equiv vK).symm x : vK.Completion) :=
  rfl
 
@[simp]
theorem toCompletion_eq_algebraMap
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ) (x : K) :
    toCompletion vK x = algebraMap K vK.Completion x :=
  rfl
 
theorem denseRange_toCompletion
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ) :
    DenseRange (toCompletion vK) := by
  change DenseRange
    (UniformSpace.Completion.coe' ∘ WithAbs.toAbs vK)
  exact
    (@UniformSpace.Completion.denseRange_coe (WithAbs vK) inferInstance).comp
      (WithAbs.toAbs_surjective vK).denseRange
      (@UniformSpace.Completion.continuous_coe (WithAbs vK) inferInstance)
private noncomputable def baseToExtensionCompletion
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ) :
    WithAbs vK →+* wL.Completion :=
  UniformSpace.Completion.coeRingHom.comp
    (algebraMap (WithAbs vK) (WithAbs wL))
private theorem baseToExtensionCompletion_norm
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) (x : WithAbs vK) :
    ‖baseToExtensionCompletion vK wL x‖ = ‖x‖ := by
  change
    ‖((algebraMap (WithAbs vK) (WithAbs wL)) x : wL.Completion)‖ = ‖x‖
  rw [UniformSpace.Completion.norm_coe, WithAbs.norm_eq_apply_ofAbs,
    WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_algebraMap]
  exact hw x.ofAbs
private theorem baseToExtensionCompletion_isometry
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) :
    Isometry (baseToExtensionCompletion vK wL) :=
  AddMonoidHomClass.isometry_of_norm _
    (baseToExtensionCompletion_norm vK wL hw)
 

noncomputable def completionMap
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) :
    vK.Completion →+* wL.Completion :=
  (baseToExtensionCompletion_isometry vK wL hw).extensionHom
private theorem completionMap_withAbs_coe
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) (x : WithAbs vK) :
    completionMap vK wL hw (x : vK.Completion) =
      baseToExtensionCompletion vK wL x :=
  (baseToExtensionCompletion_isometry vK wL hw).extensionHom_coe x
 

@[simp]
theorem completionMap_coe
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) (x : K) :
    completionMap vK wL hw (algebraMap K vK.Completion x) =
      toCompletion wL (algebraMap K L x) := by
  change completionMap vK wL hw
      (((WithAbs.equiv vK).symm x : WithAbs vK) : vK.Completion) =
    (((WithAbs.equiv wL).symm (algebraMap K L x) : WithAbs wL) :
      wL.Completion)
  rw [completionMap_withAbs_coe]
  rfl
 
theorem completionMap_isometry
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) :
    Isometry (completionMap vK wL hw) :=
  (baseToExtensionCompletion_isometry vK wL hw).completion_extension
 

noncomputable abbrev completionAlgebra
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) :
    Algebra vK.Completion wL.Completion :=
  (completionMap vK wL hw).toAlgebra
 
@[simp]
theorem completionAlgebra_algebraMap
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) (x : vK.Completion) :
    @algebraMap vK.Completion wL.Completion _ _
        (completionAlgebra vK wL hw) x = completionMap vK wL hw x :=
  rfl
 

noncomputable abbrev extensionCompletionAlgebra
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (wL : AbsoluteValue L ℝ) :
    Algebra K wL.Completion :=
  ((toCompletion wL).comp (algebraMap K L)).toAlgebra
 
noncomputable def toCompletionAlgHom
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (wL : AbsoluteValue L ℝ) :
    letI := extensionCompletionAlgebra (K := K) wL
    L →ₐ[K] wL.Completion := by
  letI := extensionCompletionAlgebra (K := K) wL
  exact
    { __ := toCompletion wL
      commutes' _ := rfl }
 
theorem completion_isScalarTower
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) :
    letI hK := extensionCompletionAlgebra (K := K) wL
    letI : SMul K wL.Completion := hK.toSMul
    letI := completionAlgebra vK wL hw
    IsScalarTower K vK.Completion wL.Completion := by
  let hK := extensionCompletionAlgebra (K := K) wL
  let : SMul K wL.Completion := hK.toSMul
  let := completionAlgebra vK wL hw
  exact IsScalarTower.of_algebraMap_eq fun x ↦
    (completionMap_coe vK wL hw x).symm
 
theorem completionAbsoluteValue_isNonarchimedean
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (hvK : IsNonarchimedean (vK : K → ℝ)) :
    IsNonarchimedean
      (completionAbsoluteValue vK : vK.Completion → ℝ) := by
  rw [isNonarchimedean_iff_bounded_nat]
  refine ⟨1, fun n ↦ ?_⟩
  rw [← map_natCast (algebraMap K vK.Completion) n,
    ← toCompletion_eq_algebraMap vK (n : K)]
  change completionAbsoluteValue vK
    (((WithAbs.equiv vK).symm (n : K) : WithAbs vK) :
      vK.Completion) ≤ 1
  rw [completionAbsoluteValue_coe]
  exact hvK.apply_natCast_le_one
section CompleteTarget
variable {K : Type u} {D : Type w} [Field K] [Field D]
end CompleteTarget
section CompleteTargetTower
variable {K : Type u} {L : Type v} {D : Type w}
variable [Field K] [Field L] [Field D] [Algebra K L]
end CompleteTargetTower
end AbsoluteValue
end
end

/- ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicLocalization -/
section
noncomputable section
namespace AbsoluteValue
universe u v
 


noncomputable def algebraicLocalization
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) :
    letI := completionAlgebra vK wL hw
    IntermediateField vK.Completion wL.Completion := by
  let := completionAlgebra vK wL hw
  exact IntermediateField.adjoin vK.Completion
    (Set.range (toCompletion wL))
private theorem toCompletion_mem_algebraicLocalization
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) (x : L) :
    letI := completionAlgebra vK wL hw
    toCompletion wL x ∈ algebraicLocalization vK wL hw := by
  let := completionAlgebra vK wL hw
  exact IntermediateField.subset_adjoin vK.Completion _ ⟨x, rfl⟩
 
noncomputable def toAlgebraicLocalization
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) :
    letI := completionAlgebra vK wL hw
    L →+* algebraicLocalization vK wL hw := by
  letI := completionAlgebra vK wL hw
  exact RingHom.codRestrict (toCompletion wL)
    (algebraicLocalization vK wL hw)
    (toCompletion_mem_algebraicLocalization vK wL hw)
 

theorem algebraicLocalization_isAlgebraic
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) :
    letI := completionAlgebra vK wL hw
    Algebra.IsAlgebraic vK.Completion
      (algebraicLocalization vK wL hw) := by
  let hK := extensionCompletionAlgebra (K := K) wL
  let : SMul K wL.Completion := hK.toSMul
  let := completionAlgebra vK wL hw
  let : IsScalarTower K vK.Completion wL.Completion :=
    completion_isScalarTower vK wL hw
  apply IntermediateField.isAlgebraic_adjoin
  intro z hz
  rcases hz with ⟨x, rfl⟩
  have hx : IsIntegral K x :=
    isAlgebraic_iff_isIntegral.mp (Algebra.IsAlgebraic.isAlgebraic x)
  let : IsScalarTower K K wL.Completion :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hx' : IsIntegral K (toCompletion wL x) :=
    hx.map (toCompletionAlgHom (K := K) wL)
  exact IsIntegral.tower_top (A := vK.Completion) hx'
 

noncomputable def algebraicLocalizationAbsoluteValue
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) :
    letI := completionAlgebra vK wL hw
    AbsoluteValue (algebraicLocalization vK wL hw) ℝ := by
  letI := completionAlgebra vK wL hw
  exact (completionAbsoluteValue wL).comp
    (algebraicLocalization vK wL hw).val.injective
 
theorem algebraicLocalizationAbsoluteValue_extends
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) :
    letI := completionAlgebra vK wL hw
    Extends (completionAbsoluteValue vK)
      (algebraicLocalizationAbsoluteValue vK wL hw) := by
  let := completionAlgebra vK wL hw
  intro x
  change ‖completionMap vK wL hw x‖ = ‖x‖
  exact (completionMap_isometry vK wL hw).norm_map_of_map_zero
    (map_zero _) x
 
@[simp]
theorem algebraicLocalizationAbsoluteValue_toAlgebraicLocalization
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) (x : L) :
    letI := completionAlgebra vK wL hw
    algebraicLocalizationAbsoluteValue vK wL hw
        (toAlgebraicLocalization vK wL hw x) = wL x := by
  let := completionAlgebra vK wL hw
  change ‖((WithAbs.equiv wL).symm x : wL.Completion)‖ = wL x
  rw [UniformSpace.Completion.norm_coe]
  rfl
 

@[simp]
theorem toAlgebraicLocalization_algebraMap
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) (x : K) :
    letI := completionAlgebra vK wL hw
    toAlgebraicLocalization vK wL hw (algebraMap K L x) =
      algebraMap vK.Completion (algebraicLocalization vK wL hw)
        (algebraMap K vK.Completion x) := by
  let := completionAlgebra vK wL hw
  apply Subtype.ext
  exact (completionMap_coe vK wL hw x).symm
end AbsoluteValue
end
end

/- ValuedFieldTheory.Valuation.AbsoluteValue.Ostrowski -/
section
noncomputable section
open Filter
namespace AbsoluteValue
private theorem ostrowski_isNonarchimedean_of_charP_pos
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) {p : ℕ}
    [CharP K p] (hp : p ≠ 0) :
    IsNonarchimedean (v : K → ℝ) := by
  rw [isNonarchimedean_iff_bounded_nat]
  refine ⟨(p : ℝ), fun n => ?_⟩
  have hp_pos : 0 < p := Nat.pos_of_ne_zero hp
  calc
    v (n : K) = v ((n % p : ℕ) : K) := by
      congr 1
      exact CharP.natCast_eq_natCast_mod K p n
    _ ≤ ((n % p : ℕ) : ℝ) := v.apply_nat_le_self (n % p)
    _ ≤ (p : ℝ) := by
      exact_mod_cast (Nat.mod_lt n hp_pos).le
 


theorem charZero_of_not_isNonarchimedean
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (harch : ¬ IsNonarchimedean (v : K → ℝ)) :
    CharZero K := by
  obtain ⟨p, hpchar⟩ := CharP.exists K
  have : CharP K p := hpchar
  rcases CharP.char_is_prime_or_zero K p with hprime | hp0
  · exact (harch
      (ostrowski_isNonarchimedean_of_charP_pos
        (K := K) v hprime.ne_zero)).elim
  · have : CharP K 0 := by
      simpa [hp0] using hpchar
    exact CharP.charP_to_charZero K
private instance ostrowski_withAbsCharZero
    {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ) :
    CharZero (WithAbs v) :=
  ((WithAbs.equiv v).toRingHom.charZero_iff
    (WithAbs.equiv v).injective).mpr inferInstance
 

private noncomputable def ostrowski_restrictRatAbsoluteValue
    {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ) :
    AbsoluteValue ℚ ℝ :=
  v.comp (f := Rat.castHom K) Rat.cast_injective
@[simp]
private theorem ostrowski_restrictRatAbsoluteValue_apply
    {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ) (q : ℚ) :
    ostrowski_restrictRatAbsoluteValue (K := K) v q = v (q : K) :=
  rfl
 

private theorem ostrowski_isNonarchimedean_of_restrictRat
    {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ)
    (h : IsNonarchimedean
      (ostrowski_restrictRatAbsoluteValue (K := K) v : ℚ → ℝ)) :
    IsNonarchimedean (v : K → ℝ) := by
  rw [isNonarchimedean_iff_bounded_nat] at h ⊢
  rcases h with ⟨C, hC⟩
  refine ⟨C, fun n => ?_⟩
  simpa using hC n
 

private theorem ostrowski_restrictRat_not_isNonarchimedean
    {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ)
    (harch : ¬ IsNonarchimedean (v : K → ℝ)) :
    ¬ IsNonarchimedean
      (ostrowski_restrictRatAbsoluteValue (K := K) v : ℚ → ℝ) := by
  intro hnonarch
  exact harch
    (ostrowski_isNonarchimedean_of_restrictRat
      (K := K) v hnonarch)
 
private theorem ostrowski_restrictRat_isEquiv_real_of_not_isNonarchimedean
    {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ)
    (harch : ¬ IsNonarchimedean (v : K → ℝ)) :
    (ostrowski_restrictRatAbsoluteValue (K := K) v).IsEquiv
      Rat.AbsoluteValue.real := by
  have harch_rat :=
    ostrowski_restrictRat_not_isNonarchimedean
      (K := K) v harch
  refine Rat.AbsoluteValue.equiv_real_of_unbounded ?_
  intro hbounded
  exact harch_rat ((isNonarchimedean_iff_bounded_nat _).2 ⟨1, hbounded⟩)
 


private theorem ostrowski_restrictRat_exists_rpow_eq_real_of_not_isNonarchimedean
    {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ)
    (harch : ¬ IsNonarchimedean (v : K → ℝ)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ q : ℚ,
        (ostrowski_restrictRatAbsoluteValue (K := K) v q) ^ c =
          Rat.AbsoluteValue.real q := by
  rcases (AbsoluteValue.isEquiv_iff_exists_rpow_eq).mp
      (ostrowski_restrictRat_isEquiv_real_of_not_isNonarchimedean
        (K := K) v harch) with
    ⟨c, hc_pos, hc⟩
  refine ⟨c, hc_pos, fun q => ?_⟩
  exact congrFun hc q
 


private theorem ostrowski_restrictRat_exists_real_rpow_eq_of_not_isNonarchimedean
    {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ)
    (harch : ¬ IsNonarchimedean (v : K → ℝ)) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧
      ∀ q : ℚ,
        ostrowski_restrictRatAbsoluteValue (K := K) v q =
          Rat.AbsoluteValue.real q ^ s := by
  rcases ostrowski_restrictRat_exists_rpow_eq_real_of_not_isNonarchimedean
      (K := K) v harch with
    ⟨c, hc_pos, hc⟩
  refine ⟨c⁻¹, inv_pos.mpr hc_pos, ?_, fun q => ?_⟩
  · have htwo_le :
        (2 : ℝ) ^ c⁻¹ ≤ (2 : ℝ) ^ (1 : ℝ) := by
      have happly :
          ostrowski_restrictRatAbsoluteValue (K := K) v (2 : ℚ) ≤ (2 : ℝ) :=
        (ostrowski_restrictRatAbsoluteValue (K := K) v).apply_nat_le_self 2
      have hq :=
        (Real.rpow_inv_eq
          ((Rat.AbsoluteValue.real).nonneg (2 : ℚ))
          ((ostrowski_restrictRatAbsoluteValue (K := K) v).nonneg (2 : ℚ))
          hc_pos.ne').2 (hc (2 : ℚ)).symm
      rw [← hq] at happly
      simpa [Rat.AbsoluteValue.real_eq_abs, Real.rpow_one] using happly
    exact (Real.rpow_le_rpow_left_iff one_lt_two).mp htwo_le
  · have hq :=
      (Real.rpow_inv_eq
        ((Rat.AbsoluteValue.real).nonneg q)
        ((ostrowski_restrictRatAbsoluteValue (K := K) v).nonneg q)
        hc_pos.ne').2 (hc q).symm
    exact hq.symm
 
private theorem ostrowski_exists_rat_pos_rpow_lt
    {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) :
    ∃ δ : ℚ, (0 : ℚ) < δ ∧ ((δ : ℝ) ^ s < ε) := by
  let η : ℝ := ε ^ s⁻¹
  have hη_pos : 0 < η := Real.rpow_pos_of_pos hε s⁻¹
  obtain ⟨δ, hδ0, hδη⟩ := exists_rat_btwn hη_pos
  refine ⟨δ, ?_, ?_⟩
  · exact_mod_cast hδ0
  · have hδ_nonneg : 0 ≤ (δ : ℝ) := le_of_lt hδ0
    have hlt : ((δ : ℝ) ^ s) < η ^ s :=
      Real.rpow_lt_rpow hδ_nonneg hδη hs
    have hηpow : η ^ s = ε := by
      dsimp [η]
      rw [← Real.rpow_mul (le_of_lt hε)]
      rw [inv_mul_cancel₀ hs.ne', Real.rpow_one]
    simpa [hηpow] using hlt
 


private theorem ostrowski_ratCast_withAbs_norm_eq_of_real_rpow
    {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ)
    (s : ℝ)
    (hnorm : ∀ q : ℚ,
      ostrowski_restrictRatAbsoluteValue (K := K) v q =
        Rat.AbsoluteValue.real q ^ s)
    (q : ℚ) :
    ‖Rat.castHom (WithAbs v) q‖ = ‖(q : ℝ)‖ ^ s := by
  change v (q : K) = ‖(q : ℝ)‖ ^ s
  rw [← ostrowski_restrictRatAbsoluteValue_apply (K := K) v q, hnorm q]
  rw [Rat.AbsoluteValue.real_eq_abs, Real.norm_eq_abs, Rat.cast_abs]
 


private def ostrowski_ratCauSeqMapWithAbs_of_real_rpow
    {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ)
    (s : ℝ) (hs : 0 < s)
    (hnorm : ∀ q : ℚ,
      ostrowski_restrictRatAbsoluteValue (K := K) v q =
        Rat.AbsoluteValue.real q ^ s)
    (u : CauSeq ℚ (abs : ℚ → ℚ)) :
    CauSeq (WithAbs v) (norm : WithAbs v → ℝ) where
  val n := Rat.castHom (WithAbs v) (u n)
  property := by
    intro ε hε
    obtain ⟨δ, hδ0, hδε⟩ := ostrowski_exists_rat_pos_rpow_lt hs hε
    obtain ⟨N, hN⟩ := u.2 δ hδ0
    refine ⟨N, fun j hj => ?_⟩
    have hsource : abs (u j - u N) < δ := hN j hj
    have hsource_real : ((abs (u j - u N) : ℚ) : ℝ) < (δ : ℝ) := by
      exact_mod_cast hsource
    have hpow :
        ((abs (u j - u N) : ℚ) : ℝ) ^ s < (δ : ℝ) ^ s :=
      Real.rpow_lt_rpow (by positivity) hsource_real hs
    calc
      ‖Rat.castHom (WithAbs v) (u j) -
          Rat.castHom (WithAbs v) (u N)‖
          = ‖Rat.castHom (WithAbs v) (u j - u N)‖ := by
            rw [map_sub]
      _ = ‖((u j - u N : ℚ) : ℝ)‖ ^ s :=
          ostrowski_ratCast_withAbs_norm_eq_of_real_rpow
            (K := K) v s hnorm (u j - u N)
      _ = ((abs (u j - u N) : ℚ) : ℝ) ^ s := by
          rw [Real.norm_eq_abs, Rat.cast_abs]
      _ < ε := hpow.trans hδε
@[simp]
private theorem ostrowski_ratCauSeqMapWithAbs_zero_of_real_rpow
    {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ)
    (s : ℝ) (hs : 0 < s)
    (hnorm : ∀ q : ℚ,
      ostrowski_restrictRatAbsoluteValue (K := K) v q =
        Rat.AbsoluteValue.real q ^ s) :
    ostrowski_ratCauSeqMapWithAbs_of_real_rpow
      (K := K) v s hs hnorm (0 : CauSeq ℚ (abs : ℚ → ℚ)) = 0 := by
  ext n
  simp [ostrowski_ratCauSeqMapWithAbs_of_real_rpow]
@[simp]
private theorem ostrowski_ratCauSeqMapWithAbs_one_of_real_rpow
    {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ)
    (s : ℝ) (hs : 0 < s)
    (hnorm : ∀ q : ℚ,
      ostrowski_restrictRatAbsoluteValue (K := K) v q =
        Rat.AbsoluteValue.real q ^ s) :
    ostrowski_ratCauSeqMapWithAbs_of_real_rpow
      (K := K) v s hs hnorm (1 : CauSeq ℚ (abs : ℚ → ℚ)) = 1 := by
  ext n
  simp [ostrowski_ratCauSeqMapWithAbs_of_real_rpow]
@[simp]
private theorem ostrowski_ratCauSeqMapWithAbs_add_of_real_rpow
    {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ)
    (s : ℝ) (hs : 0 < s)
    (hnorm : ∀ q : ℚ,
      ostrowski_restrictRatAbsoluteValue (K := K) v q =
        Rat.AbsoluteValue.real q ^ s)
    (u t : CauSeq ℚ (abs : ℚ → ℚ)) :
    ostrowski_ratCauSeqMapWithAbs_of_real_rpow
      (K := K) v s hs hnorm (u + t) =
        ostrowski_ratCauSeqMapWithAbs_of_real_rpow
          (K := K) v s hs hnorm u +
        ostrowski_ratCauSeqMapWithAbs_of_real_rpow
          (K := K) v s hs hnorm t := by
  ext n
  change Rat.castHom (WithAbs v) (u n + t n) =
    Rat.castHom (WithAbs v) (u n) + Rat.castHom (WithAbs v) (t n)
  exact (Rat.castHom (WithAbs v)).map_add (u n) (t n)
@[simp]
private theorem ostrowski_ratCauSeqMapWithAbs_mul_of_real_rpow
    {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ)
    (s : ℝ) (hs : 0 < s)
    (hnorm : ∀ q : ℚ,
      ostrowski_restrictRatAbsoluteValue (K := K) v q =
        Rat.AbsoluteValue.real q ^ s)
    (u t : CauSeq ℚ (abs : ℚ → ℚ)) :
    ostrowski_ratCauSeqMapWithAbs_of_real_rpow
      (K := K) v s hs hnorm (u * t) =
        ostrowski_ratCauSeqMapWithAbs_of_real_rpow
          (K := K) v s hs hnorm u *
        ostrowski_ratCauSeqMapWithAbs_of_real_rpow
          (K := K) v s hs hnorm t := by
  ext n
  change Rat.castHom (WithAbs v) (u n * t n) =
    Rat.castHom (WithAbs v) (u n) * Rat.castHom (WithAbs v) (t n)
  exact (Rat.castHom (WithAbs v)).map_mul (u n) (t n)
private theorem ostrowski_ratCauSeqMapWithAbs_equiv_of_real_rpow
    {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ)
    (s : ℝ) (hs : 0 < s)
    (hnorm : ∀ q : ℚ,
      ostrowski_restrictRatAbsoluteValue (K := K) v q =
        Rat.AbsoluteValue.real q ^ s)
    {u t : CauSeq ℚ (abs : ℚ → ℚ)} (hut : u ≈ t) :
    ostrowski_ratCauSeqMapWithAbs_of_real_rpow
      (K := K) v s hs hnorm u ≈
        ostrowski_ratCauSeqMapWithAbs_of_real_rpow
          (K := K) v s hs hnorm t := by
  intro ε hε
  obtain ⟨δ, hδ0, hδε⟩ := ostrowski_exists_rat_pos_rpow_lt hs hε
  obtain ⟨N, hN⟩ := hut δ hδ0
  refine ⟨N, fun j hj => ?_⟩
  have hsource : abs ((u - t) j) < δ := hN j hj
  have hsource_real : ((abs ((u - t) j) : ℚ) : ℝ) < (δ : ℝ) := by
    exact_mod_cast hsource
  have hpow :
      ((abs ((u - t) j) : ℚ) : ℝ) ^ s < (δ : ℝ) ^ s :=
    Real.rpow_lt_rpow (by positivity) hsource_real hs
  calc
    ‖((ostrowski_ratCauSeqMapWithAbs_of_real_rpow
        (K := K) v s hs hnorm u -
      ostrowski_ratCauSeqMapWithAbs_of_real_rpow
        (K := K) v s hs hnorm t) j)‖
        = ‖Rat.castHom (WithAbs v) ((u - t) j)‖ := by
          change ‖Rat.castHom (WithAbs v) (u j) - Rat.castHom (WithAbs v) (t j)‖ =
            ‖Rat.castHom (WithAbs v) (u j - t j)‖
          exact (congrArg (fun z : WithAbs v => ‖z‖)
            ((Rat.castHom (WithAbs v)).map_sub (u j) (t j))).symm
    _ = ‖(((u - t) j : ℚ) : ℝ)‖ ^ s :=
        ostrowski_ratCast_withAbs_norm_eq_of_real_rpow
          (K := K) v s hnorm ((u - t) j)
    _ = ((abs ((u - t) j) : ℚ) : ℝ) ^ s := by
        rw [Real.norm_eq_abs, Rat.cast_abs]
    _ < ε := hpow.trans hδε
 
private theorem ostrowski_cauSeq_isComplete_withAbs_of_complete
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v)) :
    CauSeq.IsComplete (WithAbs v) (norm : WithAbs v → ℝ) := by
  let : CompleteSpace (WithAbs v) :=
    hcomplete
  refine ⟨fun s => ?_⟩
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (CauSeq.cauchySeq s)
  refine ⟨a, ?_⟩
  rw [Metric.tendsto_atTop] at ha
  intro ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  refine ⟨N, fun j hj => ?_⟩
  simpa [dist_eq_norm] using hN j hj
 


private theorem ostrowski_real_mk_tendsto_ratCauSeq
    (s : CauSeq ℚ (abs : ℚ → ℚ)) :
    Tendsto (fun n => (s n : ℝ)) atTop (nhds (Real.mk s)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ0, hδε⟩ := exists_rat_btwn hε
  have hδq : (0 : ℚ) < δ := by exact_mod_cast hδ0
  obtain ⟨N, hN⟩ := s.cauchy₂ hδq
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, abs_sub_comm]
  have hnear :
      |Real.mk s - (s n : ℝ)| ≤ (δ : ℝ) :=
    Real.mk_near_of_forall_near
      (f := s) (x := (s n : ℝ)) (ε := (δ : ℝ))
      ⟨N, fun j hj => ?_⟩
  · exact hnear.trans_lt hδε
  · have hsource : abs (s j - s n) < δ := hN j hj n hn
    have hsource_real : ((abs (s j - s n) : ℚ) : ℝ) < (δ : ℝ) := by
      exact_mod_cast hsource
    rw [← Rat.cast_sub, ← Rat.cast_abs]
    exact hsource_real.le
 

private noncomputable def ostrowski_ratCauSeqCompletionEmbedding_of_real_rpow
    {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (s : ℝ) (hs : 0 < s)
    (hnorm : ∀ q : ℚ,
      ostrowski_restrictRatAbsoluteValue (K := K) v q =
        Rat.AbsoluteValue.real q ^ s) :
    CauSeq.Completion.Cauchy (abs : ℚ → ℚ) →+* WithAbs v := by
  letI : CauSeq.IsComplete (WithAbs v) (norm : WithAbs v → ℝ) :=
    ostrowski_cauSeq_isComplete_withAbs_of_complete v hcomplete
  exact
    { toFun := fun x =>
        Quotient.liftOn x
          (fun u =>
            CauSeq.lim
              (ostrowski_ratCauSeqMapWithAbs_of_real_rpow
                (K := K) v s hs hnorm u))
          (fun u t hut =>
            CauSeq.lim_eq_lim_of_equiv
              (ostrowski_ratCauSeqMapWithAbs_equiv_of_real_rpow
                (K := K) v s hs hnorm hut))
      map_zero' := by
        change CauSeq.lim
          (ostrowski_ratCauSeqMapWithAbs_of_real_rpow
            (K := K) v s hs hnorm (0 : CauSeq ℚ (abs : ℚ → ℚ))) = 0
        rw [ostrowski_ratCauSeqMapWithAbs_zero_of_real_rpow]
        change CauSeq.lim (CauSeq.const (norm : WithAbs v → ℝ) 0) = 0
        rw [CauSeq.lim_const]
      map_one' := by
        change CauSeq.lim
          (ostrowski_ratCauSeqMapWithAbs_of_real_rpow
            (K := K) v s hs hnorm (1 : CauSeq ℚ (abs : ℚ → ℚ))) = 1
        rw [ostrowski_ratCauSeqMapWithAbs_one_of_real_rpow]
        change CauSeq.lim (CauSeq.const (norm : WithAbs v → ℝ) 1) = 1
        rw [CauSeq.lim_const]
      map_add' := by
        intro x y
        refine Quotient.inductionOn₂ x y ?_
        intro u t
        change CauSeq.lim
          (ostrowski_ratCauSeqMapWithAbs_of_real_rpow
            (K := K) v s hs hnorm (u + t)) =
          CauSeq.lim
            (ostrowski_ratCauSeqMapWithAbs_of_real_rpow
              (K := K) v s hs hnorm u) +
          CauSeq.lim
            (ostrowski_ratCauSeqMapWithAbs_of_real_rpow
              (K := K) v s hs hnorm t)
        rw [ostrowski_ratCauSeqMapWithAbs_add_of_real_rpow,
          ← CauSeq.lim_add]
      map_mul' := by
        intro x y
        refine Quotient.inductionOn₂ x y ?_
        intro u t
        change CauSeq.lim
          (ostrowski_ratCauSeqMapWithAbs_of_real_rpow
            (K := K) v s hs hnorm (u * t)) =
          CauSeq.lim
            (ostrowski_ratCauSeqMapWithAbs_of_real_rpow
              (K := K) v s hs hnorm u) *
          CauSeq.lim
            (ostrowski_ratCauSeqMapWithAbs_of_real_rpow
              (K := K) v s hs hnorm t)
        rw [ostrowski_ratCauSeqMapWithAbs_mul_of_real_rpow,
          ← CauSeq.lim_mul_lim] }
 

private noncomputable def ostrowski_realEmbedding_of_real_rpow
    {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (s : ℝ) (hs : 0 < s)
    (hnorm : ∀ q : ℚ,
      ostrowski_restrictRatAbsoluteValue (K := K) v q =
        Rat.AbsoluteValue.real q ^ s) :
    ℝ →+* WithAbs v :=
  (ostrowski_ratCauSeqCompletionEmbedding_of_real_rpow
    (K := K) v hcomplete s hs hnorm).comp Real.ringEquivCauchy.toRingHom
@[simp]
private theorem ostrowski_ratCauSeqCompletionEmbedding_norm_mk_of_real_rpow
    {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (s : ℝ) (hs : 0 < s)
    (hnorm : ∀ q : ℚ,
      ostrowski_restrictRatAbsoluteValue (K := K) v q =
        Rat.AbsoluteValue.real q ^ s)
    (u : CauSeq ℚ (abs : ℚ → ℚ)) :
    ‖ostrowski_ratCauSeqCompletionEmbedding_of_real_rpow
      (K := K) v hcomplete s hs hnorm (CauSeq.Completion.mk u)‖ =
      ‖Real.mk u‖ ^ s := by
  let : CauSeq.IsComplete (WithAbs v) (norm : WithAbs v → ℝ) :=
    ostrowski_cauSeq_isComplete_withAbs_of_complete v hcomplete
  change ‖CauSeq.lim
      (ostrowski_ratCauSeqMapWithAbs_of_real_rpow
        (K := K) v s hs hnorm u)‖ = ‖Real.mk u‖ ^ s
  have hK :
      Tendsto
        (fun n =>
          ‖ostrowski_ratCauSeqMapWithAbs_of_real_rpow
            (K := K) v s hs hnorm u n‖)
        atTop
        (nhds ‖CauSeq.lim
          (ostrowski_ratCauSeqMapWithAbs_of_real_rpow
            (K := K) v s hs hnorm u)‖) :=
    tendsto_norm.comp
      (CauSeq.tendsto_limit
        (ostrowski_ratCauSeqMapWithAbs_of_real_rpow
          (K := K) v s hs hnorm u))
  have hK' :
      Tendsto (fun n => ‖(u n : ℝ)‖ ^ s) atTop
        (nhds ‖CauSeq.lim
          (ostrowski_ratCauSeqMapWithAbs_of_real_rpow
            (K := K) v s hs hnorm u)‖) := by
    convert hK using 1
    ext n
    change ‖(u n : ℝ)‖ ^ s = ‖Rat.castHom (WithAbs v) (u n)‖
    exact (ostrowski_ratCast_withAbs_norm_eq_of_real_rpow
      (K := K) v s hnorm (u n)).symm
  have hRnorm :
      Tendsto (fun n => ‖(u n : ℝ)‖) atTop (nhds ‖Real.mk u‖) :=
    tendsto_norm.comp (ostrowski_real_mk_tendsto_ratCauSeq u)
  have hR :
      Tendsto (fun n => ‖(u n : ℝ)‖ ^ s) atTop (nhds (‖Real.mk u‖ ^ s)) :=
    hRnorm.rpow_const (Or.inr hs.le)
  exact tendsto_nhds_unique hK' hR
private theorem ostrowski_realEmbedding_norm_eq_of_real_rpow
    {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (s : ℝ) (hs : 0 < s)
    (hnorm : ∀ q : ℚ,
      ostrowski_restrictRatAbsoluteValue (K := K) v q =
        Rat.AbsoluteValue.real q ^ s)
    (r : ℝ) :
    ‖ostrowski_realEmbedding_of_real_rpow
      (K := K) v hcomplete s hs hnorm r‖ = ‖r‖ ^ s := by
  induction r using Real.ind_mk with
  | h u =>
      change ‖ostrowski_ratCauSeqCompletionEmbedding_of_real_rpow
        (K := K) v hcomplete s hs hnorm (CauSeq.Completion.mk u)‖ =
        ‖Real.mk u‖ ^ s
      exact ostrowski_ratCauSeqCompletionEmbedding_norm_mk_of_real_rpow
        (K := K) v hcomplete s hs hnorm u
 



private noncomputable abbrev ostrowski_realAlgebra_of_real_rpow
    {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (s : ℝ) (hs : 0 < s)
    (hnorm : ∀ q : ℚ,
      ostrowski_restrictRatAbsoluteValue (K := K) v q =
        Rat.AbsoluteValue.real q ^ s) :
    Algebra ℝ (WithAbs v) :=
  (ostrowski_realEmbedding_of_real_rpow
    (K := K) v hcomplete s hs hnorm).toAlgebra
private theorem ostrowski_realAlgebra_norm_algebraMap_of_real_rpow
    {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (s : ℝ) (hs : 0 < s)
    (hnorm : ∀ q : ℚ,
      ostrowski_restrictRatAbsoluteValue (K := K) v q =
        Rat.AbsoluteValue.real q ^ s) :
    letI : Algebra ℝ (WithAbs v) :=
      ostrowski_realAlgebra_of_real_rpow (K := K) v hcomplete s hs hnorm
    ∀ r : ℝ, ‖algebraMap ℝ (WithAbs v) r‖ = ‖r‖ ^ s := by
  let : Algebra ℝ (WithAbs v) :=
    ostrowski_realAlgebra_of_real_rpow (K := K) v hcomplete s hs hnorm
  intro r
  change ‖ostrowski_realEmbedding_of_real_rpow
    (K := K) v hcomplete s hs hnorm r‖ = ‖r‖ ^ s
  exact ostrowski_realEmbedding_norm_eq_of_real_rpow
    (K := K) v hcomplete s hs hnorm r
section RealRpowGelfandMazur
open Polynomial
open Bornology Filter Set Topology
variable {F : Type*} [NormedField F] [Algebra ℝ F]
 


private theorem ostrowski_continuous_algebraMap_of_real_rpow
    {s : ℝ} (hs : 0 < s)
    (hnorm : ∀ r : ℝ, ‖algebraMap ℝ F r‖ = ‖r‖ ^ s) :
    Continuous (algebraMap ℝ F) := by
  rw [Metric.continuous_iff]
  intro r ε hε
  obtain ⟨δ, hδ0, hδε⟩ := ostrowski_exists_rat_pos_rpow_lt hs hε
  refine ⟨(δ : ℝ), by exact_mod_cast hδ0, fun y hy => ?_⟩
  have hdist : ‖y - r‖ < (δ : ℝ) := by
    simpa [Real.dist_eq, dist_eq_norm] using hy
  have hpow : ‖y - r‖ ^ s < (δ : ℝ) ^ s :=
    Real.rpow_lt_rpow (norm_nonneg _) hdist hs
  calc
    dist (algebraMap ℝ F y) (algebraMap ℝ F r)
        = ‖algebraMap ℝ F (y - r)‖ := by
          rw [dist_eq_norm, map_sub]
    _ = ‖y - r‖ ^ s := hnorm (y - r)
    _ < ε := hpow.trans hδε
private theorem ostrowski_tendsto_norm_rpow_cobounded_atTop
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun r : ℝ => ‖r‖ ^ s) (cobounded ℝ) atTop :=
  (tendsto_rpow_atTop hs).comp tendsto_norm_cobounded_atTop
private theorem ostrowski_tendsto_norm_rpow_fst_atTop
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun y : ℝ × ℝ => ‖y.1‖ ^ s) (cobounded ℝ ×ˢ ⊤) atTop :=
  (tendsto_rpow_atTop hs).comp
    (by
      rw [tendsto_norm_atTop_iff_cobounded]
      exact tendsto_fst)
private theorem ostrowski_tendsto_norm_rpow_snd_atTop
    {s : ℝ} (hs : 0 < s) (S : Set ℝ) :
    Tendsto (fun y : ℝ × ℝ => ‖y.2‖ ^ s) (𝓟 S ×ˢ cobounded ℝ) atTop :=
  (tendsto_rpow_atTop hs).comp
    (by
      rw [tendsto_norm_atTop_iff_cobounded]
      exact tendsto_snd)
 

private abbrev ostrowski_realRpowPhi (x : F) (u : ℝ × ℝ) : F :=
  x ^ 2 - algebraMap ℝ F u.1 * x + algebraMap ℝ F u.2
private theorem ostrowski_continuous_realRpowPhi
    {s : ℝ} (hs : 0 < s)
    (hnorm : ∀ r : ℝ, ‖algebraMap ℝ F r‖ = ‖r‖ ^ s)
    (x : F) :
    Continuous (ostrowski_realRpowPhi (F := F) x) := by
  have hcont_alg : Continuous (algebraMap ℝ F) :=
    ostrowski_continuous_algebraMap_of_real_rpow
      (F := F) hs hnorm
  exact ((continuous_const.pow 2).sub
    ((hcont_alg.comp continuous_fst).mul continuous_const)).add
      (hcont_alg.comp continuous_snd)
private theorem ostrowski_aeval_eq_realRpowPhi
    (x : F) (u : ℝ × ℝ) :
    aeval x (X ^ 2 - C u.1 * X + C u.2) =
      ostrowski_realRpowPhi (F := F) x u := by
  simp [ostrowski_realRpowPhi]
 
private theorem ostrowski_norm_eq_of_isMinOn_of_forall_le
    {X E : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [SeminormedAddCommGroup E] {f : X → E} {M : ℝ} {x : X}
    (hM : 0 < M) (hx : ‖f x‖ = M) (h : IsMinOn (‖f ·‖) univ x)
    (hf : Continuous f)
    (H : ∀ {y} z, ‖f y‖ = M →
      ∀ n > 0, ‖f z‖ ≤ M * (1 + (‖f z - f y‖ / M) ^ n))
    (y : X) :
    ‖f y‖ = M := by
  suffices {y | ‖f y‖ = M} = univ by
    simpa only [← this, hx] using! mem_univ y
  refine IsClopen.eq_univ ⟨isClosed_eq (by fun_prop) (by fun_prop), ?_⟩
    (nonempty_of_mem hx)
  rw [isOpen_iff_eventually]
  intro w hw
  filter_upwards [mem_map.mp <| hf.tendsto w (Metric.ball_mem_nhds (f w) hM)] with u hu
  simp only [mem_preimage, Metric.mem_ball, dist_eq_norm, ← div_lt_one₀ hM] at hu
  refine le_antisymm ?_ (hx ▸ isMinOn_univ_iff.mp h u)
  suffices Tendsto
      (fun n : ℕ => M * (1 + (‖f u - f w‖ / M) ^ n))
      atTop (𝓝 (M * (1 + 0))) by
    refine ge_of_tendsto (by simpa) ?_
    filter_upwards [Ioi_mem_atTop 0] with n hn
    exact H u hw n hn
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hu
    |>.const_add 1 |>.const_mul M
 

private theorem ostrowski_le_aeval_of_isMonicOfDegree_real_rpow
    {x : F} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ z : ℝ × ℝ, M ≤ ‖ostrowski_realRpowPhi (F := F) x z‖)
    {p : ℝ[X]} {n : ℕ} (hp : IsMonicOfDegree p (2 * n)) :
    M ^ n ≤ ‖aeval x p‖ := by
  induction n generalizing p with
  | zero => simp_all
  | succ n ih =>
      rw [mul_add, mul_one] at hp
      obtain ⟨f₁, f₂, hf₁, hf₂, H⟩ :=
        hp.eq_isMonicOfDegree_two_mul_isMonicOfDegree
      obtain ⟨a, b, hab⟩ := isMonicOfDegree_two_iff'.mp hf₁
      rw [H, aeval_mul, norm_mul, mul_comm, pow_succ, hab,
        ostrowski_aeval_eq_realRpowPhi (F := F) x (a, b)]
      exact mul_le_mul (ih hf₂) (h (a, b)) hM (norm_nonneg _)
 


private theorem ostrowski_norm_realRpowPhi_eq_of_isMinOn
    {s : ℝ} (hs : 0 < s)
    (hnorm : ∀ r : ℝ, ‖algebraMap ℝ F r‖ = ‖r‖ ^ s)
    {x : F} {z : ℝ × ℝ}
    (h : IsMinOn (‖ostrowski_realRpowPhi (F := F) x ·‖) univ z)
    (H : ‖ostrowski_realRpowPhi (F := F) x z‖ ≠ 0)
    (w : ℝ × ℝ) :
    ‖ostrowski_realRpowPhi (F := F) x w‖ =
      ‖ostrowski_realRpowPhi (F := F) x z‖ := by
  set M : ℝ := ‖ostrowski_realRpowPhi (F := F) x z‖ with hM
  have hM₀ : 0 < M := by positivity
  refine ostrowski_norm_eq_of_isMinOn_of_forall_le
    hM₀ hM.symm h
    (ostrowski_continuous_realRpowPhi (F := F) hs hnorm x)
    (fun {w} u hw n hn => ?_) w
  have HH :
      M * (1 + (‖ostrowski_realRpowPhi (F := F) x u -
        ostrowski_realRpowPhi (F := F) x w‖ / M) ^ n) =
        (M ^ n + ‖ostrowski_realRpowPhi (F := F) x u -
          ostrowski_realRpowPhi (F := F) x w‖ ^ n) / M ^ (n - 1) := by
    simp only [field, div_pow, ← pow_succ', Nat.sub_add_cancel hn]
  rw [HH, le_div_iff₀ (by positivity)]
  clear HH
  let q (y : ℝ × ℝ) : ℝ[X] := X ^ 2 - C y.1 * X + C y.2
  have hq (y : ℝ × ℝ) : IsMonicOfDegree (q y) 2 :=
    isMonicOfDegree_sub_add_two ..
  have hsub : q w - q u = (C u.1 - C w.1) * X + C w.2 - C u.2 := by
    simp only [q]
    ring
  have hdvd : q u ∣ q w ^ n - (q w - q u) ^ n := by
    nth_rewrite 1 [← sub_sub_self (q w) (q u)]
    exact sub_dvd_pow_sub_pow ..
  have H' : ((q w - q u) ^ n).natDegree < 2 * n := by
    rw [hsub]
    compute_degree
    grind
  obtain ⟨p, hp, hrel⟩ :=
    ((hq w).pow n).of_dvd_sub (by grind) (hq u) H' hdvd
  clear H' hdvd hsub
  rw [show 2 * n - 2 = 2 * (n - 1) by grind] at hp
  grw [ostrowski_le_aeval_of_isMonicOfDegree_real_rpow
    (F := F) hM₀.le (isMinOn_univ_iff.mp h) hp]
  rw [← sub_eq_iff_eq_add, eq_comm, mul_comm] at hrel
  apply_fun (‖aeval x ·‖) at hrel
  rw [map_mul, norm_mul, map_sub,
    ostrowski_aeval_eq_realRpowPhi (F := F) x u] at hrel
  rw [hrel, norm_sub_rev (ostrowski_realRpowPhi (F := F) x u)]
  exact (norm_sub_le ..).trans <| by
    simp [q, ostrowski_aeval_eq_realRpowPhi, hw]
 

private theorem ostrowski_exists_isMinOn_norm_sub_algebraMap_of_real_rpow
    {s : ℝ} (hs : 0 < s)
    (hnorm : ∀ r : ℝ, ‖algebraMap ℝ F r‖ = ‖r‖ ^ s)
    (x : F) :
    ∃ z : ℝ, IsMinOn (fun r : ℝ => ‖x - algebraMap ℝ F r‖) univ z := by
  have hcont_alg : Continuous (algebraMap ℝ F) :=
    ostrowski_continuous_algebraMap_of_real_rpow
      (F := F) hs hnorm
  have htend :
      Tendsto (fun r : ℝ => ‖x - algebraMap ℝ F r‖)
        (cobounded ℝ) atTop := by
    have hbase :
        Tendsto (fun r : ℝ => ‖r‖ ^ s - ‖x‖)
          (cobounded ℝ) atTop :=
      tendsto_atTop_add_const_right _ _
        (ostrowski_tendsto_norm_rpow_cobounded_atTop hs)
    refine tendsto_atTop_mono' _ ?_ hbase
    filter_upwards with r
    calc
      ‖r‖ ^ s - ‖x‖ = ‖algebraMap ℝ F r‖ - ‖x‖ := by
        rw [hnorm r]
      _ ≤ ‖algebraMap ℝ F r - x‖ := norm_sub_norm_le _ _
      _ = ‖x - algebraMap ℝ F r‖ := by rw [norm_sub_rev]
  simp only [isMinOn_univ_iff]
  refine (show Continuous fun r : ℝ => ‖x - algebraMap ℝ F r‖ from
    (continuous_const.sub hcont_alg).norm).exists_forall_le_of_isBounded 0 ?_
  simpa [isBounded_def, compl_ofPred, Ioi]
    using htend (Ioi_mem_atTop ‖x - algebraMap ℝ F (0 : ℝ)‖)
 

private theorem ostrowski_tendsto_realRpowPhi_cobounded
    {s : ℝ} (hs : 0 < s)
    (hnorm : ∀ r : ℝ, ‖algebraMap ℝ F r‖ = ‖r‖ ^ s)
    {x : F} {c : ℝ} (hc₀ : 0 < c)
    (hbd : ∀ r : ℝ, c ≤ ‖x - algebraMap ℝ F r‖) :
    Tendsto (ostrowski_realRpowPhi (F := F) x ·)
      (cobounded (ℝ × ℝ)) (cobounded F) := by
  simp_rw [ostrowski_realRpowPhi, sub_add]
  refine tendsto_const_sub_cobounded _ |>.comp ?_
  rw [← tendsto_norm_atTop_iff_cobounded]
  refine Tendsto.coprod_of_prod_top_right (α := ℝ) (fun S hS => ?_) ?_
  · rw [← isCobounded_def, ← isBounded_compl_iff] at hS
    obtain ⟨M, hM_pos, hM⟩ : ∃ M > 0, ∀ y ∈ Sᶜ, ‖y‖ ≤ M :=
      hS.exists_pos_norm_le
    suffices Tendsto
        (fun y : ℝ × ℝ => ‖y.2‖ ^ s - M ^ s * ‖x‖)
        (𝓟 Sᶜ ×ˢ cobounded ℝ) atTop by
      refine tendsto_atTop_mono' _ ?_ this
      filter_upwards [prod_mem_prod (mem_principal_self Sᶜ) univ_mem] with y hy
      rw [norm_sub_rev]
      refine le_trans ?_ (norm_sub_norm_le ..)
      have hy₁_le : ‖y.1‖ ≤ M := hM _ (Set.mem_prod.mp hy).1
      have hy₁_pow : ‖y.1‖ ^ s ≤ M ^ s :=
        Real.rpow_le_rpow (norm_nonneg _) hy₁_le hs.le
      calc
        ‖algebraMap ℝ F y.2‖ - ‖algebraMap ℝ F y.1 * x‖
            = ‖y.2‖ ^ s - ‖y.1‖ ^ s * ‖x‖ := by
              rw [hnorm y.2, norm_mul, hnorm y.1]
        _ ≥ ‖y.2‖ ^ s - M ^ s * ‖x‖ := by
              gcongr
    exact tendsto_atTop_add_const_right _ _
      (ostrowski_tendsto_norm_rpow_snd_atTop hs Sᶜ)
  · suffices Tendsto (fun y : ℝ × ℝ => ‖y.1‖ ^ s * c)
        (cobounded ℝ ×ˢ ⊤) atTop by
      refine tendsto_atTop_mono' _ ?_ this
      filter_upwards [prod_mem_prod (isBounded_singleton (x := 0)) univ_mem] with y hy
      have hy₁_ne : y.1 ≠ 0 := by
        simpa using (Set.mem_prod.mp hy).1
      calc
        ‖y.1‖ ^ s * c
            ≤ ‖y.1‖ ^ s * ‖x - algebraMap ℝ F (y.1⁻¹ * y.2)‖ := by
              gcongr
              exact hbd _
        _ = ‖algebraMap ℝ F y.1‖ *
              ‖x - algebraMap ℝ F (y.1⁻¹ * y.2)‖ := by
              rw [hnorm y.1]
        _ = ‖algebraMap ℝ F y.1 *
              (x - algebraMap ℝ F (y.1⁻¹ * y.2))‖ := by
              rw [norm_mul]
        _ = ‖algebraMap ℝ F y.1 * x - algebraMap ℝ F y.2‖ := by
              congr 1
              rw [mul_sub, ← map_mul]
              have hmul : y.1 * (y.1⁻¹ * y.2) = y.2 := by
                field_simp [hy₁_ne]
              rw [hmul]
    simpa [mul_comm] using
      Tendsto.const_mul_atTop hc₀
        (ostrowski_tendsto_norm_rpow_fst_atTop hs)
 
private theorem ostrowski_exists_isMinOn_norm_realRpowPhi
    {s : ℝ} (hs : 0 < s)
    (hnorm : ∀ r : ℝ, ‖algebraMap ℝ F r‖ = ‖r‖ ^ s)
    (x : F) :
    ∃ z : ℝ × ℝ,
      IsMinOn (‖ostrowski_realRpowPhi (F := F) x ·‖) univ z := by
  obtain ⟨u, hu⟩ :=
    ostrowski_exists_isMinOn_norm_sub_algebraMap_of_real_rpow
      (F := F) hs hnorm x
  rcases eq_or_lt_of_le (norm_nonneg (x - algebraMap ℝ F u)) with hc₀ | hc₀
  · rw [eq_comm, norm_eq_zero, sub_eq_zero] at hc₀
    exact ⟨(u, 0), fun y => by
      simp [ostrowski_realRpowPhi, hc₀, sq]⟩
  · simp only [isMinOn_univ_iff] at hu ⊢
    refine (ostrowski_continuous_realRpowPhi (F := F) hs hnorm x).norm
      |>.exists_forall_le_of_isBounded (0, 0) ?_
    simpa [isBounded_def, compl_ofPred, Ioi]
      using tendsto_norm_cobounded_atTop.comp
        (ostrowski_tendsto_realRpowPhi_cobounded
          (F := F) hs hnorm hc₀ hu)
        (Ioi_mem_atTop ‖ostrowski_realRpowPhi (F := F) x (0, 0)‖)
 

private theorem ostrowski_exists_isMonicOfDegree_two_and_aeval_eq_zero_real_rpow
    {s : ℝ} (hs : 0 < s)
    (hnorm : ∀ r : ℝ, ‖algebraMap ℝ F r‖ = ‖r‖ ^ s)
    (x : F) :
    ∃ p : ℝ[X], IsMonicOfDegree p 2 ∧ aeval x p = 0 := by
  obtain ⟨z, h⟩ :=
    ostrowski_exists_isMinOn_norm_realRpowPhi (F := F) hs hnorm x
  suffices ostrowski_realRpowPhi (F := F) x z = 0 from
    ⟨_, isMonicOfDegree_sub_add_two z.1 z.2, by
      rwa [ostrowski_aeval_eq_realRpowPhi]⟩
  by_contra! H
  set M := ‖ostrowski_realRpowPhi (F := F) x z‖
  have h' (r : ℝ) : √M ≤ ‖x - algebraMap ℝ F r‖ := by
    rw [← sq_le_sq₀ M.sqrt_nonneg (norm_nonneg _),
      Real.sq_sqrt (norm_nonneg _), ← norm_pow,
      Commute.sub_sq <| (Algebra.commutes r x).symm]
    have hcomm : x * algebraMap ℝ F r = algebraMap ℝ F r * x :=
      (Algebra.commutes r x).symm
    convert! isMinOn_univ_iff.mp h (2 * r, r ^ 2) using 4 <;>
      simp [two_mul, add_mul, sq, hcomm]
  have htend := tendsto_norm_atTop_iff_cobounded.mpr <|
    ostrowski_tendsto_realRpowPhi_cobounded
      (F := F) hs hnorm (by positivity) h'
  simp only [ostrowski_norm_realRpowPhi_eq_of_isMinOn
    (F := F) hs hnorm h (norm_ne_zero_iff.mpr H)] at htend
  exact Filter.not_tendsto_const_atTop _ _ htend
 

private theorem ostrowski_gelfandMazur_of_real_rpow_scalar
    (F : Type*) [NormedField F] [Algebra ℝ F]
    {s : ℝ} (hs : 0 < s)
    (hnorm : ∀ r : ℝ, ‖algebraMap ℝ F r‖ = ‖r‖ ^ s) :
    Nonempty (F ≃ₐ[ℝ] ℝ) ∨ Nonempty (F ≃ₐ[ℝ] ℂ) := by
  have : Algebra.IsAlgebraic ℝ F := by
    refine ⟨fun x => ?_⟩
    obtain ⟨p, hp, hpx⟩ :=
      ostrowski_exists_isMonicOfDegree_two_and_aeval_eq_zero_real_rpow
        (F := F) hs hnorm x
    exact ⟨p, hp.ne_zero, hpx⟩
  exact _root_.Real.nonempty_algEquiv_or F
end RealRpowGelfandMazur
private theorem ostrowski_gelfandMazur_of_real_rpow
    {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (s : ℝ) (hs : 0 < s)
    (hnorm : ∀ q : ℚ,
      ostrowski_restrictRatAbsoluteValue (K := K) v q =
        Rat.AbsoluteValue.real q ^ s) :
    letI : Algebra ℝ (WithAbs v) :=
      ostrowski_realAlgebra_of_real_rpow (K := K) v hcomplete s hs hnorm
    Nonempty (WithAbs v ≃ₐ[ℝ] ℝ) ∨
      Nonempty (WithAbs v ≃ₐ[ℝ] ℂ) := by
  let : Algebra ℝ (WithAbs v) :=
    ostrowski_realAlgebra_of_real_rpow (K := K) v hcomplete s hs hnorm
  exact ostrowski_gelfandMazur_of_real_rpow_scalar (WithAbs v) hs
    (ostrowski_realAlgebra_norm_algebraMap_of_real_rpow
      (K := K) v hcomplete s hs hnorm)
private theorem ostrowski_realAlgEquiv_norm_eq_of_real_rpow
    {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (s : ℝ) (hs : 0 < s)
    (hnorm : ∀ q : ℚ,
      ostrowski_restrictRatAbsoluteValue (K := K) v q =
        Rat.AbsoluteValue.real q ^ s) :
    letI : Algebra ℝ (WithAbs v) :=
      ostrowski_realAlgebra_of_real_rpow (K := K) v hcomplete s hs hnorm
    ∀ (e : WithAbs v ≃ₐ[ℝ] ℝ) (x : WithAbs v),
      ‖x‖ = ‖e x‖ ^ s := by
  let : Algebra ℝ (WithAbs v) :=
    ostrowski_realAlgebra_of_real_rpow (K := K) v hcomplete s hs hnorm
  intro e x
  have hx : x = algebraMap ℝ (WithAbs v) (e x) := by
    calc
      x = e.symm (e x) := by simp
      _ = algebraMap ℝ (WithAbs v) (e x) := by
        simpa using (AlgEquiv.commutes e.symm (e x))
  rw [hx]
  simp only [AlgEquiv.commutes, Algebra.algebraMap_self_apply]
  exact ostrowski_realAlgebra_norm_algebraMap_of_real_rpow
    (K := K) v hcomplete s hs hnorm (e x)
private theorem ostrowski_realBranch_abs_eq_of_real_rpow
    {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (s : ℝ) (hs : 0 < s)
    (hnorm : ∀ q : ℚ,
      ostrowski_restrictRatAbsoluteValue (K := K) v q =
        Rat.AbsoluteValue.real q ^ s) :
    letI : Algebra ℝ (WithAbs v) :=
      ostrowski_realAlgebra_of_real_rpow (K := K) v hcomplete s hs hnorm
    ∀ (e : WithAbs v ≃ₐ[ℝ] ℝ) (x : K),
      v x = ‖e ((WithAbs.equiv v).symm x)‖ ^ s := by
  let : Algebra ℝ (WithAbs v) :=
    ostrowski_realAlgebra_of_real_rpow (K := K) v hcomplete s hs hnorm
  intro e x
  change ‖((WithAbs.equiv v).symm x : WithAbs v)‖ =
    ‖e ((WithAbs.equiv v).symm x)‖ ^ s
  exact ostrowski_realAlgEquiv_norm_eq_of_real_rpow
    (K := K) v hcomplete s hs hnorm e ((WithAbs.equiv v).symm x)
end AbsoluteValue
namespace AlgEquiv
private theorem norm_symm_I_eq_one
    {F : Type*} [NormedField F] [Algebra ℝ F]
    (e : F ≃ₐ[ℝ] ℂ) :
    ‖e.symm Complex.I‖ = 1 := by
  have hsq : (e.symm Complex.I : F) ^ 2 = -1 := by
    apply e.injective
    simp [Complex.I_sq]
  have hsqnorm : ‖e.symm Complex.I‖ ^ 2 = (1 : ℝ) := by
    calc
      ‖e.symm Complex.I‖ ^ 2 = ‖(e.symm Complex.I : F) ^ 2‖ := by simp
      _ = ‖(-1 : F)‖ := by rw [hsq]
      _ = 1 := by simp
  nlinarith [norm_nonneg (e.symm Complex.I),
    sq_nonneg (‖e.symm Complex.I‖ - 1), hsqnorm]
private theorem norm_symm_le_re_add_im_rpow
    {F : Type*} [NormedField F] [Algebra ℝ F]
    {s : ℝ}
    (hnorm : ∀ r : ℝ, ‖algebraMap ℝ F r‖ = ‖r‖ ^ s)
    (e : F ≃ₐ[ℝ] ℂ) (z : ℂ) :
    ‖e.symm z‖ ≤ ‖z.re‖ ^ s + ‖z.im‖ ^ s := by
  let j : F := e.symm Complex.I
  have hj : ‖j‖ = 1 :=
    norm_symm_I_eq_one e
  have hzdecomp :
      e.symm z = algebraMap ℝ F z.re + algebraMap ℝ F z.im * j := by
    apply e.injective
    simp [j, Complex.re_add_im]
  calc
    ‖e.symm z‖ =
        ‖algebraMap ℝ F z.re + algebraMap ℝ F z.im * j‖ := by
          rw [hzdecomp]
    _ ≤ ‖algebraMap ℝ F z.re‖ + ‖algebraMap ℝ F z.im * j‖ :=
        norm_add_le _ _
    _ = ‖z.re‖ ^ s + ‖z.im‖ ^ s := by
        rw [norm_mul, hnorm z.re, hnorm z.im, hj, mul_one]
private theorem norm_symm_le_one_of_norm_eq_one
    {F : Type*} [NormedField F] [Algebra ℝ F]
    {s : ℝ} (hs : 0 < s)
    (hnorm : ∀ r : ℝ, ‖algebraMap ℝ F r‖ = ‖r‖ ^ s)
    (e : F ≃ₐ[ℝ] ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖e.symm z‖ ≤ 1 := by
  by_contra hnot
  have hlt : 1 < ‖e.symm z‖ := lt_of_not_ge hnot
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 : ℝ) hlt
  have hbound : ‖e.symm z‖ ^ n ≤ (2 : ℝ) := by
    calc
      ‖e.symm z‖ ^ n = ‖(e.symm z : F) ^ n‖ := by simp
      _ = ‖e.symm (z ^ n)‖ := by
          congr 1
          exact (map_pow e.symm z n).symm
      _ ≤ ‖(z ^ n).re‖ ^ s + ‖(z ^ n).im‖ ^ s :=
          norm_symm_le_re_add_im_rpow hnorm e (z ^ n)
      _ ≤ 1 + 1 := by
          have hzpow : ‖z ^ n‖ = (1 : ℝ) := by
            rw [norm_pow, hz, one_pow]
          have hre : ‖(z ^ n).re‖ ≤ (1 : ℝ) := by
            rw [Real.norm_eq_abs]
            exact (Complex.abs_re_le_norm (z ^ n)).trans_eq hzpow
          have him : ‖(z ^ n).im‖ ≤ (1 : ℝ) := by
            rw [Real.norm_eq_abs]
            exact (Complex.abs_im_le_norm (z ^ n)).trans_eq hzpow
          have hre_pow : ‖(z ^ n).re‖ ^ s ≤ (1 : ℝ) :=
            by simpa using
              Real.rpow_le_rpow (norm_nonneg _) hre hs.le
          have him_pow : ‖(z ^ n).im‖ ^ s ≤ (1 : ℝ) :=
            by simpa using
              Real.rpow_le_rpow (norm_nonneg _) him hs.le
          linarith
      _ = 2 := by norm_num
  exact not_lt_of_ge hbound hn
private theorem norm_symm_eq_one_of_norm_eq_one
    {F : Type*} [NormedField F] [Algebra ℝ F]
    {s : ℝ} (hs : 0 < s)
    (hnorm : ∀ r : ℝ, ‖algebraMap ℝ F r‖ = ‖r‖ ^ s)
    (e : F ≃ₐ[ℝ] ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖e.symm z‖ = 1 := by
  have hle : ‖e.symm z‖ ≤ 1 :=
    norm_symm_le_one_of_norm_eq_one
      hs hnorm e hz
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  have hle_inv : ‖e.symm z⁻¹‖ ≤ 1 := by
    exact norm_symm_le_one_of_norm_eq_one
      hs hnorm e (by simp [norm_inv, hz])
  have hprod : ‖e.symm z‖ * ‖e.symm z⁻¹‖ = 1 := by
    calc
      ‖e.symm z‖ * ‖e.symm z⁻¹‖ =
          ‖(e.symm z : F) * e.symm z⁻¹‖ := by
            rw [norm_mul]
      _ = ‖(1 : F)‖ := by
          congr 1
          rw [← map_mul]
          simp [hz0]
      _ = 1 := by simp
  have hpos_inv : 0 < ‖e.symm z⁻¹‖ := norm_pos_iff.mpr (by
    intro h
    apply hz0
    simpa using congrArg e h)
  have hge : 1 ≤ ‖e.symm z‖ := by
    nlinarith [hprod, hle_inv, hpos_inv]
  exact le_antisymm hle hge
 
theorem norm_symm_apply_eq_norm_rpow
    {F : Type*} [NormedField F] [Algebra ℝ F]
    {s : ℝ} (hs : 0 < s)
    (hnorm : ∀ r : ℝ, ‖algebraMap ℝ F r‖ = ‖r‖ ^ s)
    (e : F ≃ₐ[ℝ] ℂ) (z : ℂ) :
    ‖e.symm z‖ = ‖z‖ ^ s := by
  by_cases hz0 : z = 0
  · simp [hz0, hs.ne']
  · let r : ℝ := ‖z‖
    have hr_pos : 0 < r := by
      simpa [r] using norm_pos_iff.mpr hz0
    let u : ℂ := (r⁻¹ : ℂ) * z
    have hu_norm : ‖u‖ = 1 := by
      simp [u, r, hr_pos.ne']
    have hz_decomp : z = (r : ℂ) * u := by
      simp [u, r, hr_pos.ne']
    calc
      ‖e.symm z‖ = ‖e.symm ((r : ℂ) * u)‖ := by rw [hz_decomp]
      _ = ‖algebraMap ℝ F r * e.symm u‖ := by
          congr 1
          rw [map_mul]
          congr 1
          exact AlgEquiv.commutes e.symm r
      _ = ‖z‖ ^ s := by
          rw [norm_mul, hnorm r,
            norm_symm_eq_one_of_norm_eq_one
              hs hnorm e hu_norm, mul_one]
          simp [r]
end AlgEquiv
namespace AbsoluteValue
private theorem ostrowski_complexAlgEquiv_norm_eq_of_real_rpow
    {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (s : ℝ) (hs : 0 < s)
    (hnorm : ∀ q : ℚ,
      ostrowski_restrictRatAbsoluteValue (K := K) v q =
        Rat.AbsoluteValue.real q ^ s) :
    letI : Algebra ℝ (WithAbs v) :=
      ostrowski_realAlgebra_of_real_rpow (K := K) v hcomplete s hs hnorm
    ∀ (e : WithAbs v ≃ₐ[ℝ] ℂ) (x : WithAbs v),
      ‖x‖ = ‖e x‖ ^ s := by
  let : Algebra ℝ (WithAbs v) :=
    ostrowski_realAlgebra_of_real_rpow (K := K) v hcomplete s hs hnorm
  intro e x
  calc
    ‖x‖ = ‖e.symm (e x)‖ := by simp
    _ = ‖e x‖ ^ s :=
        AlgEquiv.norm_symm_apply_eq_norm_rpow hs
          (ostrowski_realAlgebra_norm_algebraMap_of_real_rpow
            (K := K) v hcomplete s hs hnorm) e (e x)
private theorem ostrowski_complexBranch_abs_eq_of_real_rpow
    {K : Type*} [Field K] [CharZero K] (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (s : ℝ) (hs : 0 < s)
    (hnorm : ∀ q : ℚ,
      ostrowski_restrictRatAbsoluteValue (K := K) v q =
        Rat.AbsoluteValue.real q ^ s) :
    letI : Algebra ℝ (WithAbs v) :=
      ostrowski_realAlgebra_of_real_rpow (K := K) v hcomplete s hs hnorm
    ∀ (e : WithAbs v ≃ₐ[ℝ] ℂ) (x : K),
      v x = ‖e ((WithAbs.equiv v).symm x)‖ ^ s := by
  let : Algebra ℝ (WithAbs v) :=
    ostrowski_realAlgebra_of_real_rpow (K := K) v hcomplete s hs hnorm
  intro e x
  change ‖((WithAbs.equiv v).symm x : WithAbs v)‖ =
    ‖e ((WithAbs.equiv v).symm x)‖ ^ s
  exact ostrowski_complexAlgEquiv_norm_eq_of_real_rpow
    (K := K) v hcomplete s hs hnorm e ((WithAbs.equiv v).symm x)
 



theorem ostrowski_of_complete
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (harch : ¬ IsNonarchimedean (v : K → ℝ)) :
    letI : CharZero K := charZero_of_not_isNonarchimedean v harch
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧
      ((∃ σ : K ≃+* ℝ, ∀ a : K, v a = ‖σ a‖ ^ s) ∨
        (∃ σ : K ≃+* ℂ, ∀ a : K, v a = ‖σ a‖ ^ s)) := by
  let : CharZero K := charZero_of_not_isNonarchimedean v harch
  obtain ⟨s, hs, hs_le, hnorm⟩ :=
    ostrowski_restrictRat_exists_real_rpow_eq_of_not_isNonarchimedean
      (K := K) v harch
  refine ⟨s, hs, hs_le, ?_⟩
  let : Algebra ℝ (WithAbs v) :=
    ostrowski_realAlgebra_of_real_rpow (K := K) v hcomplete s hs hnorm
  rcases ostrowski_gelfandMazur_of_real_rpow
      (K := K) v hcomplete s hs hnorm with hreal | hcomplex
  · rcases hreal with ⟨e⟩
    left
    let σ : K ≃+* ℝ := (WithAbs.equiv v).symm.trans e.toRingEquiv
    refine ⟨σ, fun a => ?_⟩
    change v a = ‖e ((WithAbs.equiv v).symm a)‖ ^ s
    exact ostrowski_realBranch_abs_eq_of_real_rpow
      (K := K) v hcomplete s hs hnorm e a
  · rcases hcomplex with ⟨e⟩
    right
    let σ : K ≃+* ℂ := (WithAbs.equiv v).symm.trans e.toRingEquiv
    refine ⟨σ, fun a => ?_⟩
    change v a = ‖e ((WithAbs.equiv v).symm a)‖ ^ s
    exact ostrowski_complexBranch_abs_eq_of_real_rpow
      (K := K) v hcomplete s hs hnorm e a
end AbsoluteValue
end
end

/- ValuedFieldTheory.Valuation.AbsoluteValue.SpectralExtension -/
section
noncomputable section
namespace AbsoluteValue
private abbrev spectral_withAbsNontriviallyNormedField
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (hv : v.IsNontrivial) :
    NontriviallyNormedField (WithAbs v) :=
  NontriviallyNormedField.ofNormNeOne
    (by
      rcases hv with ⟨x, hx0, hx1⟩
      refine ⟨WithAbs.toAbs v x, ?_, ?_⟩
      · intro hx
        apply hx0
        simpa using congrArg (WithAbs.equiv v) hx
      · simpa [WithAbs.norm_eq_apply_ofAbs] using hx1)
 

private instance withAbsAlgebra_isAlgebraic
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (v : AbsoluteValue K ℝ) :
    Algebra.IsAlgebraic (WithAbs v) L := by
  exact Algebra.IsAlgebraic.tower_top
    (K := K) (L := WithAbs v) (A := L)
 
private theorem withAbs_isUltrametricDist
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : IsNonarchimedean (v : K → ℝ)) :
    IsUltrametricDist (WithAbs v) := by
  refine IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm ?_
  intro x y
  simpa [WithAbs.norm_eq_apply_ofAbs] using
    hnonarch (WithAbs.equiv v x) (WithAbs.equiv v y)
 

private theorem spectral_spectralNorm_extends_base
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ) (x : K) :
    _root_.spectralNorm (WithAbs v) L (algebraMap K L x) = v x := by
  let : Algebra.IsAlgebraic (WithAbs v) L :=
    withAbsAlgebra_isAlgebraic v
  simpa [WithAbs.algebraMap_left_apply, WithAbs.norm_eq_apply_ofAbs] using
    (_root_.spectralNorm_extends
      (K := WithAbs v) (L := L) ((WithAbs.equiv v).symm x))
 

private theorem spectral_spectralNorm_strong_triangle
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ)
    (hnonarch : IsNonarchimedean (v : K → ℝ)) (x y : L) :
    _root_.spectralNorm (WithAbs v) L (x + y) ≤
      max (_root_.spectralNorm (WithAbs v) L x)
        (_root_.spectralNorm (WithAbs v) L y) := by
  let : IsUltrametricDist (WithAbs v) :=
    withAbs_isUltrametricDist v hnonarch
  let : Algebra.IsAlgebraic (WithAbs v) L :=
    withAbsAlgebra_isAlgebraic v
  exact _root_.isNonarchimedean_spectralNorm
    (K := WithAbs v) (L := L) x y
 

private theorem spectral_spectralNorm_eq_zero_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ) (x : L) :
    _root_.spectralNorm (WithAbs v) L x = 0 ↔ x = 0 := by
  let : Algebra.IsAlgebraic (WithAbs v) L :=
    withAbsAlgebra_isAlgebraic v
  constructor
  · intro hx
    exact _root_.eq_zero_of_map_spectralNorm_eq_zero
      (K := WithAbs v) (L := L) hx
      (Algebra.IsAlgebraic.isAlgebraic x)
  · intro hx
    rw [hx]
    exact _root_.spectralNorm_zero (K := WithAbs v) (L := L)
 

private theorem spectral_spectralNorm_mul
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (hnonarch : IsNonarchimedean (v : K → ℝ))
    (hv : v.IsNontrivial) (x y : L) :
    _root_.spectralNorm (WithAbs v) L (x * y) =
      _root_.spectralNorm (WithAbs v) L x *
        _root_.spectralNorm (WithAbs v) L y := by
  let : NontriviallyNormedField (WithAbs v) :=
    spectral_withAbsNontriviallyNormedField v hv
  let : Algebra (WithAbs v) L :=
    WithAbs.algebraLeft L v
  let : CompleteSpace (WithAbs v) :=
    hcomplete
  let : IsUltrametricDist (WithAbs v) :=
    withAbs_isUltrametricDist v hnonarch
  let : Algebra.IsAlgebraic (WithAbs v) L :=
    withAbsAlgebra_isAlgebraic v
  simpa [_root_.spectralAlgNorm_def] using
    (_root_.spectralAlgNorm_mul (K := WithAbs v) (L := L) x y)
 

noncomputable def spectralExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (hnonarch : IsNonarchimedean (v : K → ℝ))
    (hv : v.IsNontrivial) : AbsoluteValue L ℝ where
  toFun := _root_.spectralNorm (WithAbs v) L
  map_mul' x y :=
    spectral_spectralNorm_mul (K := K) (L := L)
      v hcomplete hnonarch hv x y
  nonneg' x := _root_.spectralNorm_nonneg (K := WithAbs v) (L := L) x
  eq_zero' x := spectral_spectralNorm_eq_zero_iff (K := K) (L := L) v x
  add_le' x y := by
    have hstrong :=
      spectral_spectralNorm_strong_triangle v hnonarch x y
    have hx_nonneg :
        0 ≤ _root_.spectralNorm (WithAbs v) L x :=
      _root_.spectralNorm_nonneg (K := WithAbs v) (L := L) x
    have hy_nonneg :
        0 ≤ _root_.spectralNorm (WithAbs v) L y :=
      _root_.spectralNorm_nonneg (K := WithAbs v) (L := L) y
    exact hstrong.trans
      (max_le
        (le_add_of_nonneg_right hy_nonneg)
        (le_add_of_nonneg_left hx_nonneg))
 

theorem spectralExtension_extends
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (hnonarch : IsNonarchimedean (v : K → ℝ))
    (hv : v.IsNontrivial) :
    Extends v (spectralExtension (K := K) (L := L)
      v hcomplete hnonarch hv) :=
  spectral_spectralNorm_extends_base v
 
private theorem spectral_unique_spectralNorm
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (hnonarch : IsNonarchimedean (v : K → ℝ))
    (hv : v.IsNontrivial)
    (w : AbsoluteValue L ℝ)
    (hw_ext : Extends v w)
    (x : L) :
    w x = _root_.spectralNorm (WithAbs v) L x := by
  let : NontriviallyNormedField (WithAbs v) :=
    spectral_withAbsNontriviallyNormedField v hv
  let : Algebra (WithAbs v) L :=
    WithAbs.algebraLeft L v
  let : CompleteSpace (WithAbs v) :=
    hcomplete
  let : IsUltrametricDist (WithAbs v) :=
    withAbs_isUltrametricDist v hnonarch
  let : Algebra.IsAlgebraic (WithAbs v) L :=
    withAbsAlgebra_isAlgebraic v
  refine _root_.spectralNorm_unique_field_norm_ext
    (K := WithAbs v) (L := L) (f := w) ?_ x
  intro a
  rw [WithAbs.algebraMap_left_apply, hw_ext]
  exact (WithAbs.norm_eq_apply_ofAbs v a).symm
 

theorem eq_spectralExtension_of_extends
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (hnonarch : IsNonarchimedean (v : K → ℝ))
    (hv : v.IsNontrivial)
    (w : AbsoluteValue L ℝ)
    (hw_ext : Extends v w) :
    w = spectralExtension (K := K) (L := L)
      v hcomplete hnonarch hv := by
  ext x
  exact spectral_unique_spectralNorm
    v hcomplete hnonarch hv w hw_ext x
end AbsoluteValue
end
end

/- ValuedFieldTheory.Valuation.AbsoluteValue.Theory.AbsoluteValues -/
section
noncomputable section
open Filter
open scoped BigOperators Topology
namespace LubinTate
namespace Valuations
 
theorem absoluteValue_finset_sum_le
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    {ι : Type*} (s : Finset ι) (f : ι → K) :
    v (s.sum f) ≤ s.sum (fun i => v (f i)) := by
  classical
  refine Finset.induction_on s ?empty ?insert
  · simp
  · intro i s his ih
    rw [Finset.sum_insert his, Finset.sum_insert his]
    exact (v.add_le (f i) (s.sum f)).trans
      (by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left ih (v (f i)))
 

def EquivalentAbsoluteValues {K : Type*} [Field K]
    (v w : AbsoluteValue K ℝ) : Prop :=
  IsHomeomorph (WithAbs.congr v w (.refl K))
 

theorem equivalentAbsoluteValues_iff_isEquiv
    {K : Type*} [Field K] (v w : AbsoluteValue K ℝ) :
    EquivalentAbsoluteValues v w ↔ v.IsEquiv w :=
  (AbsoluteValue.isEquiv_iff_isHomeomorph v w).symm
 

theorem equivalentAbsoluteValues_iff_exists_rpow_eq
    {K : Type*} [Field K] (v w : AbsoluteValue K ℝ) :
    EquivalentAbsoluteValues v w ↔ ∃ s : ℝ, 0 < s ∧ (v · ^ s) = w := by
  exact
    (equivalentAbsoluteValues_iff_isEquiv v w).trans
      (AbsoluteValue.isEquiv_iff_exists_rpow_eq (v := v) (w := w))
 

def NonarchimedeanAbsoluteValue {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, v (n : K) ≤ C
 
def StrongTriangle {K : Type*} [Field K] (v : AbsoluteValue K ℝ) : Prop :=
  ∀ x y : K, v (x + y) ≤ max (v x) (v y)
 

theorem nat_bound_ge_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) {C : ℝ}
    (hC : ∀ n : ℕ, v (n : K) ≤ C) :
    1 ≤ C := by
  simpa using hC 1
 


theorem add_pow_le_of_bounded_nat
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) {C : ℝ}
    (hC : ∀ n : ℕ, v (n : K) ≤ C) (x y : K) (n : ℕ) :
    v ((x + y) ^ n) ≤
      ((n + 1 : ℕ) : ℝ) * C * (max (v x) (v y)) ^ n := by
  classical
  let M : ℝ := max (v x) (v y)
  have hC_nonneg : 0 ≤ C :=
    (zero_le_one : (0 : ℝ) ≤ 1).trans
      (nat_bound_ge_one v hC)
  have hM_nonneg : 0 ≤ M :=
    (v.nonneg x).trans (le_max_left (v x) (v y))
  have hsum_le :
      v ((Finset.range (n + 1)).sum
          (fun m => x ^ m * y ^ (n - m) * (n.choose m : K))) ≤
        (Finset.range (n + 1)).sum
          (fun m => v (x ^ m * y ^ (n - m) * (n.choose m : K))) :=
    absoluteValue_finset_sum_le v (Finset.range (n + 1))
      (fun m => x ^ m * y ^ (n - m) * (n.choose m : K))
  have hterm :
      ∀ m ∈ Finset.range (n + 1),
        v (x ^ m * y ^ (n - m) * (n.choose m : K)) ≤ C * M ^ n := by
    intro m hm
    have hmle : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hxpow : v (x ^ m) ≤ M ^ m := by
      rw [map_pow]
      exact pow_le_pow_left₀ (v.nonneg x) (le_max_left (v x) (v y)) m
    have hypow : v (y ^ (n - m)) ≤ M ^ (n - m) := by
      rw [map_pow]
      exact pow_le_pow_left₀ (v.nonneg y) (le_max_right (v x) (v y)) (n - m)
    have hxy :
        v (x ^ m) * v (y ^ (n - m)) ≤ M ^ m * M ^ (n - m) :=
      mul_le_mul hxpow hypow (v.nonneg (y ^ (n - m))) (pow_nonneg hM_nonneg m)
    have hchoose : v ((n.choose m : ℕ) : K) ≤ C := hC (n.choose m)
    calc
      v (x ^ m * y ^ (n - m) * (n.choose m : K))
          = v (x ^ m) * v (y ^ (n - m)) * v ((n.choose m : ℕ) : K) := by
              rw [map_mul, map_mul]
      _ ≤ (M ^ m * M ^ (n - m)) * C := by
              exact mul_le_mul hxy hchoose
                (v.nonneg ((n.choose m : ℕ) : K))
                (mul_nonneg (pow_nonneg hM_nonneg m)
                  (pow_nonneg hM_nonneg (n - m)))
      _ = C * M ^ n := by
              rw [← pow_add, Nat.add_sub_of_le hmle]
              ring
  calc
    v ((x + y) ^ n)
        = v ((Finset.range (n + 1)).sum
            (fun m => x ^ m * y ^ (n - m) * (n.choose m : K))) := by
            rw [add_pow]
    _ ≤ (Finset.range (n + 1)).sum
          (fun m => v (x ^ m * y ^ (n - m) * (n.choose m : K))) := hsum_le
    _ ≤ (Finset.range (n + 1)).sum (fun _m => C * M ^ n) :=
          Finset.sum_le_sum hterm
    _ = ((n + 1 : ℕ) : ℝ) * C * M ^ n := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
 

theorem tendsto_linear_bound_rpow_inv
    {C : ℝ} (hC : 0 < C) :
    Tendsto
      (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)))
      atTop (𝓝 1) := by
  have hCroot :
      Tendsto (fun n : ℕ => C ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
    have hcont : ContinuousAt (fun t : ℝ => C ^ t) 0 :=
      Real.continuousAt_const_rpow hC.ne'
    have hzero : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    change Tendsto
      ((fun t : ℝ => C ^ t) ∘ fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 1)
    simpa only [Real.rpow_zero] using hcont.tendsto.comp hzero
  have hshiftReal :
      Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / (1 * x + (-1)))) atTop (𝓝 1) :=
    tendsto_rpow_div_mul_add 1 1 (-1) zero_ne_one
  have hshiftNat :
      Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ ((n : ℝ)⁻¹)))
        atTop (𝓝 1) := by
    have hnatshift : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    refine (hshiftReal.comp hnatshift).congr' ?_
    exact Eventually.of_forall fun n => by
      simp [Nat.cast_add, Nat.cast_one, one_div, add_assoc]
  have htarget :
      Tendsto
        (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)))
        atTop (𝓝 (1 * 1)) := by
    refine (hshiftNat.mul hCroot).congr' ?_
    exact Eventually.of_forall fun n => by
      have hn_nonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
      have hmul :=
        (Real.mul_rpow (z := ((n : ℝ)⁻¹)) hn_nonneg (le_of_lt hC)).symm
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  simpa using htarget
 
theorem add_le_root_bound_of_bounded_nat
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) {C : ℝ}
    (hC : ∀ n : ℕ, v (n : K) ≤ C) (x y : K)
    {n : ℕ} (hn : n ≠ 0) :
    v (x + y) ≤
      ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)) *
        max (v x) (v y) := by
  classical
  let M : ℝ := max (v x) (v y)
  have hC_pos : 0 < C :=
    zero_lt_one.trans_le (nat_bound_ge_one v hC)
  have hM_nonneg : 0 ≤ M :=
    (v.nonneg x).trans (le_max_left (v x) (v y))
  by_cases hMzero : M = 0
  · have hx_le_zero : v x ≤ 0 := by
      simpa [M, hMzero] using (le_max_left (v x) (v y))
    have hy_le_zero : v y ≤ 0 := by
      simpa [M, hMzero] using (le_max_right (v x) (v y))
    have hxzero : x = 0 := (v.eq_zero).mp (le_antisymm hx_le_zero (v.nonneg x))
    have hyzero : y = 0 := (v.eq_zero).mp (le_antisymm hy_le_zero (v.nonneg y))
    simp [hxzero, hyzero]
  · have hpow :
        (v (x + y)) ^ n ≤ ((n + 1 : ℕ) : ℝ) * C * M ^ n := by
      simpa [map_pow, M] using
        add_pow_le_of_bounded_nat v hC x y n
    have hright_nonneg :
        0 ≤ ((n + 1 : ℕ) : ℝ) * C * M ^ n := by
      exact mul_nonneg
        (mul_nonneg (by positivity) (le_of_lt hC_pos))
        (pow_nonneg hM_nonneg n)
    have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hroot :
        v (x + y) ≤
          (((n + 1 : ℕ) : ℝ) * C * M ^ n) ^ ((n : ℝ)⁻¹) := by
      rw [Real.le_rpow_inv_iff_of_pos (v.nonneg (x + y)) hright_nonneg hn_pos]
      simpa [Real.rpow_natCast] using hpow
    calc
      v (x + y)
          ≤ (((n + 1 : ℕ) : ℝ) * C * M ^ n) ^ ((n : ℝ)⁻¹) := hroot
      _ = ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)) * M := by
            have hcoef_nonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) * C :=
              mul_nonneg (by positivity) (le_of_lt hC_pos)
            rw [Real.mul_rpow hcoef_nonneg (pow_nonneg hM_nonneg n)]
            rw [Real.pow_rpow_inv_natCast hM_nonneg hn]
      _ = ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)) *
            max (v x) (v y) := by
            rfl
 

theorem strong_triangle_of_nonarchimedean
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : NonarchimedeanAbsoluteValue v) :
    StrongTriangle v := by
  rcases hnonarch with ⟨C, hC⟩
  have hC_pos : 0 < C :=
    zero_lt_one.trans_le (nat_bound_ge_one v hC)
  intro x y
  let M : ℝ := max (v x) (v y)
  have hlim :
      Tendsto
        (fun n : ℕ =>
          ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)) * M)
        atTop (𝓝 M) := by
    simpa using
      (tendsto_linear_bound_rpow_inv hC_pos).mul
        (tendsto_const_nhds (x := M))
  have heventually :
      ∀ᶠ n : ℕ in atTop,
        v (x + y) ≤
          ((((n + 1 : ℕ) : ℝ) * C) ^ ((n : ℝ)⁻¹)) * M := by
    refine eventually_atTop.2 ⟨1, ?_⟩
    intro n hn
    exact add_le_root_bound_of_bounded_nat
      (v := v) hC x y (n := n) (by omega)
  have hle :
      v (x + y) ≤ M :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim heventually
  simpa [M, StrongTriangle] using hle
end Valuations
end LubinTate
end
end

/- ValuedFieldTheory.Valuation.AbsoluteValue.ValuationSubring -/
section
noncomputable section
open scoped Polynomial
namespace AlgebraicNumberTheory
namespace Valuations
 

def absoluteValueUnitBallSubring
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) : Subring K where
  carrier := {x | v x ≤ 1}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy
    exact (LubinTate.Valuations.strong_triangle_of_nonarchimedean
      v hnonarch x y).trans (max_le hx hy)
  neg_mem' := by
    intro x hx
    simpa using hx
  mul_mem' := by
    intro x y hx hy
    change v (x * y) ≤ 1
    rw [v.map_mul]
    exact mul_le_one₀ hx (v.nonneg y) hy
 

theorem mem_absoluteValueUnitBallSubring_iff
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) (x : K) :
    x ∈ absoluteValueUnitBallSubring v hnonarch ↔ v x ≤ 1 :=
  Iff.rfl
 

theorem absoluteValueUnitBallSubring_mem_or_inv_mem
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) (x : K) :
    x ∈ absoluteValueUnitBallSubring v hnonarch ∨
      x⁻¹ ∈ absoluteValueUnitBallSubring v hnonarch := by
  by_cases hx : v x ≤ 1
  · exact Or.inl ((mem_absoluteValueUnitBallSubring_iff
      v hnonarch x).2 hx)
  · right
    have hx_gt : 1 < v x := lt_of_not_ge hx
    rw [mem_absoluteValueUnitBallSubring_iff, map_inv₀]
    exact inv_le_one_of_one_le₀ hx_gt.le
 

def absoluteValueValuationSubring
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) :
    ValuationSubring K :=
  ValuationSubring.ofSubring
    (absoluteValueUnitBallSubring v hnonarch)
    (absoluteValueUnitBallSubring_mem_or_inv_mem v hnonarch)
 

theorem mem_absoluteValueValuationSubring_iff
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) (x : K) :
    x ∈ absoluteValueValuationSubring v hnonarch ↔
      v x ≤ 1 := by
  exact (ValuationSubring.mem_ofSubring
    (absoluteValueUnitBallSubring v hnonarch)
    (absoluteValueUnitBallSubring_mem_or_inv_mem v hnonarch) x).trans
    (mem_absoluteValueUnitBallSubring_iff v hnonarch x)
 


theorem isUnit_iff_abs_eq_one_of_mem_iff_le_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    {C : Type*} [SetLike C K] [SubmonoidClass C K]
    (S : C) (hS : ∀ x : K, x ∈ S ↔ v x ≤ 1) (x : S) :
    IsUnit x ↔ v (x : K) = 1 := by
  constructor
  · intro hx
    have hx_inv :=
      (Submonoid.isUnit_iff_and (S := S) (a := x)).mp hx
    have hx_le : v (x : K) ≤ 1 := (hS (x : K)).1 x.property
    have hinv_le : v ((x : K)⁻¹) ≤ 1 :=
      (hS ((x : K)⁻¹)).1 hx_inv.2
    have hmul : v (x : K) * v ((x : K)⁻¹) = 1 := by
      rw [← v.map_mul, mul_inv_cancel₀ hx_inv.1]
      simp
    have hge : 1 ≤ v (x : K) := by
      calc
        1 = v (x : K) * v ((x : K)⁻¹) := hmul.symm
        _ ≤ v (x : K) * 1 :=
          mul_le_mul_of_nonneg_left hinv_le (v.nonneg (x : K))
        _ = v (x : K) := by simp
    exact le_antisymm hx_le hge
  · intro hx
    rw [Submonoid.isUnit_iff_and (S := S) (a := x)]
    constructor
    · intro hx_zero
      have hzero_one : (0 : ℝ) = 1 := by
        simp [hx_zero] at hx
      exact zero_ne_one hzero_one
    · exact (hS ((x : K)⁻¹)).2 <| by
        rw [map_inv₀, hx]
        simp
 

theorem not_isUnit_iff_abs_lt_one_of_mem_iff_le_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    {C : Type*} [SetLike C K] [SubmonoidClass C K]
    (S : C) (hS : ∀ x : K, x ∈ S ↔ v x ≤ 1) (x : S) :
    ¬ IsUnit x ↔ v (x : K) < 1 := by
  have hx_le : v (x : K) ≤ 1 := (hS (x : K)).1 x.property
  rw [isUnit_iff_abs_eq_one_of_mem_iff_le_one v S hS]
  exact hx_le.lt_iff_ne.symm
end Valuations
end AlgebraicNumberTheory
end
end

/- ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.Core -/
section
noncomputable section
namespace AbsoluteValue
private abbrev algebraicExtension_standardRealAbsoluteValue : AbsoluteValue ℝ ℝ :=
  NormedField.toAbsoluteValue ℝ
 

private abbrev algebraicExtension_standardComplexAbsoluteValue : AbsoluteValue ℂ ℝ :=
  NormedField.toAbsoluteValue ℂ
 


noncomputable def rpow
    {F : Type*} [Field F] (v : AbsoluteValue F ℝ)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) : AbsoluteValue F ℝ where
  toFun x := v x ^ s
  map_mul' x y := by
    rw [v.map_mul, Real.mul_rpow (v.nonneg x) (v.nonneg y)]
  nonneg' x := Real.rpow_nonneg (v.nonneg x) s
  eq_zero' x := by
    rw [Real.rpow_eq_zero (v.nonneg x) hs0.ne']
    exact v.eq_zero
  add_le' x y := by
    calc
      v (x + y) ^ s ≤ (v x + v y) ^ s :=
        Real.rpow_le_rpow (v.nonneg _) (v.add_le x y) hs0.le
      _ ≤ v x ^ s + v y ^ s :=
        Real.rpow_add_le_add_rpow (v.nonneg x) (v.nonneg y) hs0.le hs1
 
@[simp]
theorem rpow_apply
    {F : Type*} [Field F] (v : AbsoluteValue F ℝ)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) (x : F) :
    rpow v s hs0 hs1 x = v x ^ s :=
  rfl
 
private theorem algebraicExtension_standardComplexAbsoluteValue_extends_standardReal
    (x : ℝ) :
    algebraicExtension_standardComplexAbsoluteValue (algebraMap ℝ ℂ x) =
      algebraicExtension_standardRealAbsoluteValue x := by
  change ‖(algebraMap ℝ ℂ x)‖ = ‖x‖
  simp
 


noncomputable def compAlgEquiv
    {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] (e : L ≃ₐ[K] E)
    (w : AbsoluteValue E ℝ) : AbsoluteValue L ℝ :=
  w.comp (f := e.toRingHom) e.injective
 
@[simp]
theorem compAlgEquiv_extends_apply
    {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] (e : L ≃ₐ[K] E)
    (w : AbsoluteValue E ℝ) (v : AbsoluteValue K ℝ)
    (hw : ∀ x : K, w (algebraMap K E x) = v x)
    (x : K) :
    compAlgEquiv e w (algebraMap K L x) =
      v x := by
  change w (e (algebraMap K L x)) = v x
  rw [AlgEquiv.commutes, hw]
private theorem algebraicExtension_real_algEquiv_real_unique_rpow_extension
    {L : Type*} [Field L] [Algebra ℝ L] (e : L ≃ₐ[ℝ] ℝ)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (w : AbsoluteValue L ℝ)
    (hw : ∀ x : ℝ, w (algebraMap ℝ L x) =
      algebraicExtension_standardRealAbsoluteValue x ^ s) :
    w = rpow
      (compAlgEquiv
        e algebraicExtension_standardRealAbsoluteValue)
      s hs0 hs1 := by
  ext x
  have hx : x = algebraMap ℝ L (e x) := by
    calc
      x = e.symm (e x) := by simp
      _ = algebraMap ℝ L (e x) := by
        simpa using (AlgEquiv.commutes e.symm (e x))
  rw [hx, hw]
  exact congrArg (fun t : ℝ => t ^ s)
    (compAlgEquiv_extends_apply e
      algebraicExtension_standardRealAbsoluteValue algebraicExtension_standardRealAbsoluteValue
      (fun x => rfl) (e x)).symm
 


private theorem algebraicExtension_real_algEquiv_complex_unique_rpow_extension
    {L : Type*} [Field L] [Algebra ℝ L] (e : L ≃ₐ[ℝ] ℂ)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (w : AbsoluteValue L ℝ)
    (hw : ∀ x : ℝ, w (algebraMap ℝ L x) =
      algebraicExtension_standardRealAbsoluteValue x ^ s) :
    w = rpow
      (compAlgEquiv
        e algebraicExtension_standardComplexAbsoluteValue)
      s hs0 hs1 := by
  let e' : WithAbs w ≃ₐ[ℝ] ℂ :=
    (WithAbs.algEquiv ℝ w).trans e
  have hnorm :
      ∀ r : ℝ, ‖algebraMap ℝ (WithAbs w) r‖ = ‖r‖ ^ s := by
    intro r
    rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.algebraMap_right_apply]
    change w (algebraMap ℝ L r) =
      algebraicExtension_standardRealAbsoluteValue r ^ s
    exact hw r
  ext x
  let y : WithAbs w := WithAbs.toAbs w x
  change w x = ‖e x‖ ^ s
  calc
    w x = ‖y‖ := by
      simp [y, WithAbs.norm_eq_apply_ofAbs]
    _ = ‖e'.symm (e' y)‖ := by simp
    _ = ‖e' y‖ ^ s :=
      AlgEquiv.norm_symm_apply_eq_norm_rpow
        (F := WithAbs w) (s := s) hs0 hnorm e' (e' y)
    _ = ‖e x‖ ^ s := by simp [y, e']
 

private theorem algebraicExtension_complex_algEquiv_complex_unique_rpow_extension
    {L : Type*} [Field L] [Algebra ℂ L] (e : L ≃ₐ[ℂ] ℂ)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (w : AbsoluteValue L ℝ)
    (hw : ∀ z : ℂ, w (algebraMap ℂ L z) =
      algebraicExtension_standardComplexAbsoluteValue z ^ s) :
    w = rpow
      (compAlgEquiv
        e algebraicExtension_standardComplexAbsoluteValue)
      s hs0 hs1 := by
  ext x
  have hx : x = algebraMap ℂ L (e x) := by
    calc
      x = e.symm (e x) := by simp
      _ = algebraMap ℂ L (e x) := by
        simpa using (AlgEquiv.commutes e.symm (e x))
  rw [hx, hw]
  exact congrArg (fun t : ℝ => t ^ s)
    (compAlgEquiv_extends_apply e
      algebraicExtension_standardComplexAbsoluteValue algebraicExtension_standardComplexAbsoluteValue
      (fun z => rfl) (e x)).symm
 
structure UniqueExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ) where
   
  extension : AbsoluteValue L ℝ
   
  isExtension : Extends v extension
   
  unique :
    ∀ w : AbsoluteValue L ℝ,
      Extends v w → w = extension
private noncomputable def algebraicExtension_realRpow
    {L : Type*} [Field L] [Algebra ℝ L] [Algebra.IsAlgebraic ℝ L]
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    UniqueExtension (K := ℝ) (L := L)
      (rpow
        algebraicExtension_standardRealAbsoluteValue s hs0 hs1) :=
  Classical.choice <| by
    rcases Real.nonempty_algEquiv_or L with hreal | hcomplex
    · rcases hreal with ⟨e⟩
      exact ⟨
        { extension :=
            rpow
              (compAlgEquiv
                e algebraicExtension_standardRealAbsoluteValue)
              s hs0 hs1
          isExtension := by
            intro x
            simp only [rpow_apply]
            rw [compAlgEquiv_extends_apply e
              algebraicExtension_standardRealAbsoluteValue
              algebraicExtension_standardRealAbsoluteValue (fun x => rfl) x]
          unique :=
            algebraicExtension_real_algEquiv_real_unique_rpow_extension
              e s hs0 hs1 }⟩
    · rcases hcomplex with ⟨e⟩
      exact ⟨
        { extension :=
            rpow
              (compAlgEquiv
                e algebraicExtension_standardComplexAbsoluteValue)
              s hs0 hs1
          isExtension := by
            intro x
            simp only [rpow_apply]
            rw [compAlgEquiv_extends_apply e
              algebraicExtension_standardComplexAbsoluteValue
              algebraicExtension_standardRealAbsoluteValue
              algebraicExtension_standardComplexAbsoluteValue_extends_standardReal x]
          unique :=
            algebraicExtension_real_algEquiv_complex_unique_rpow_extension
              e s hs0 hs1 }⟩
 


private noncomputable def algebraicExtension_complexRpow
    {L : Type*} [Field L] [Algebra ℂ L] [Algebra.IsAlgebraic ℂ L]
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    UniqueExtension (K := ℂ) (L := L)
      (rpow
        algebraicExtension_standardComplexAbsoluteValue s hs0 hs1) := by
  letI : Algebra.IsIntegral ℂ L := Algebra.IsAlgebraic.isIntegral
  let e0 : ℂ ≃ₐ[ℂ] L :=
    AlgEquiv.ofBijective (Algebra.ofId ℂ L)
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := L))
  let e : L ≃ₐ[ℂ] ℂ := e0.symm
  exact
    { extension :=
        rpow
          (compAlgEquiv
            e algebraicExtension_standardComplexAbsoluteValue)
          s hs0 hs1
      isExtension := by
        intro z
        simp only [rpow_apply]
        rw [compAlgEquiv_extends_apply e
          algebraicExtension_standardComplexAbsoluteValue
          algebraicExtension_standardComplexAbsoluteValue (fun z => rfl) z]
      unique :=
        algebraicExtension_complex_algEquiv_complex_unique_rpow_extension
          e s hs0 hs1 }
 
private theorem algebraicExtension_isAlgebraic_of_base_ringEquiv
    {K E L : Type*} [Field K] [Field E] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (σ : K ≃+* E) :
    letI : Algebra E K := RingHom.toAlgebra σ.symm.toRingHom
    letI : Algebra E L :=
      RingHom.toAlgebra ((algebraMap K L).comp σ.symm.toRingHom)
    Algebra.IsAlgebraic E L := by
  let : Algebra E K := RingHom.toAlgebra σ.symm.toRingHom
  let : Algebra E L :=
    RingHom.toAlgebra ((algebraMap K L).comp σ.symm.toRingHom)
  have : IsScalarTower E K L :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      simp [RingHom.algebraMap_toAlgebra])
  let e : K ≃ₐ[E] E := AlgEquiv.ofRingEquiv (f := σ) (by
    intro r
    simp [RingHom.algebraMap_toAlgebra])
  have : Algebra.IsAlgebraic E K := e.symm.isAlgebraic
  exact Algebra.IsAlgebraic.trans E K L
 


private noncomputable def algebraicExtension_baseRingEquiv
    {K E L : Type*} [Field K] [Field E] [Field L] [Algebra K L]
    (σ : K ≃+* E) (vK : AbsoluteValue K ℝ) (vE : AbsoluteValue E ℝ)
    (hvσ : ∀ x : K, vE (σ x) = vK x)
    (R :
      letI : Algebra E L :=
        RingHom.toAlgebra ((algebraMap K L).comp σ.symm.toRingHom)
      UniqueExtension (K := E) (L := L) vE) :
    UniqueExtension (K := K) (L := L) vK := by
  letI : Algebra E L :=
    RingHom.toAlgebra ((algebraMap K L).comp σ.symm.toRingHom)
  exact
    { extension := R.extension
      isExtension := by
        intro x
        have hbase := R.isExtension (σ x)
        have hmap :
            algebraMap E L (σ x) = algebraMap K L x := by
          simp [RingHom.algebraMap_toAlgebra]
        calc
          R.extension (algebraMap K L x)
              = R.extension (algebraMap E L (σ x)) := by rw [hmap]
          _ = vE (σ x) := hbase
          _ = vK x := hvσ x
      unique := by
        intro w hw
        apply R.unique w
        intro z
        have hmap :
            algebraMap E L z = algebraMap K L (σ.symm z) := by
          simp [RingHom.algebraMap_toAlgebra]
        calc
          w (algebraMap E L z)
              = w (algebraMap K L (σ.symm z)) := by rw [hmap]
          _ = vK (σ.symm z) := hw (σ.symm z)
          _ = vE z := by
            simpa using (hvσ (σ.symm z)).symm }
 
private noncomputable def algebraicExtension_archimedean
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (harch : ¬ IsNonarchimedean (v : K → ℝ)) :
    UniqueExtension (K := K) (L := L) v :=
  Classical.choice <| by
  classical
  let : CharZero K := AbsoluteValue.charZero_of_not_isNonarchimedean v harch
  rcases AbsoluteValue.ostrowski_of_complete v hcomplete harch with
    ⟨s, hs0, hs1, hbranch⟩
  rcases hbranch with hreal | hcomplex
  · rcases hreal with ⟨σ, hσ⟩
    let : Algebra ℝ K := RingHom.toAlgebra σ.symm.toRingHom
    let : Algebra ℝ L :=
      RingHom.toAlgebra ((algebraMap K L).comp σ.symm.toRingHom)
    have : Algebra.IsAlgebraic ℝ L :=
      algebraicExtension_isAlgebraic_of_base_ringEquiv (K := K) (E := ℝ)
        (L := L) σ
    let R :=
      algebraicExtension_realRpow
        (L := L) s hs0 hs1
    exact ⟨
      algebraicExtension_baseRingEquiv
        (K := K) (E := ℝ) (L := L) σ v
        (rpow
          algebraicExtension_standardRealAbsoluteValue s hs0 hs1)
        (fun x => (hσ x).symm) R⟩
  · rcases hcomplex with ⟨σ, hσ⟩
    let : Algebra ℂ K := RingHom.toAlgebra σ.symm.toRingHom
    let : Algebra ℂ L :=
      RingHom.toAlgebra ((algebraMap K L).comp σ.symm.toRingHom)
    have : Algebra.IsAlgebraic ℂ L :=
      algebraicExtension_isAlgebraic_of_base_ringEquiv (K := K) (E := ℂ)
        (L := L) σ
    let R :=
      algebraicExtension_complexRpow
        (L := L) s hs0 hs1
    exact ⟨
      algebraicExtension_baseRingEquiv
        (K := K) (E := ℂ) (L := L) σ v
        (rpow
          algebraicExtension_standardComplexAbsoluteValue s hs0 hs1)
        (fun x => (hσ x).symm) R⟩
 

private noncomputable def algebraicExtension_nonarchimedean
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (hnonarch : IsNonarchimedean (v : K → ℝ))
    (hv : v.IsNontrivial) :
    UniqueExtension (K := K) (L := L) v where
  extension :=
    spectralExtension (K := K) (L := L)
      v hcomplete hnonarch hv
  isExtension :=
    spectralExtension_extends
      (K := K) (L := L) v hcomplete hnonarch hv
  unique :=
    eq_spectralExtension_of_extends
      (K := K) (L := L) v hcomplete hnonarch hv
 



noncomputable def uniqueAlgebraicExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (hv : v.IsNontrivial) :
    UniqueExtension (K := K) (L := L) v := by
  by_cases hnonarch : IsNonarchimedean (v : K → ℝ)
  · exact algebraicExtension_nonarchimedean
      v hcomplete hnonarch hv
  · exact algebraicExtension_archimedean
      v hcomplete hnonarch
end AbsoluteValue
end
end

/- ValuedFieldTheory.Valuation.Completion.AbsoluteValueExtensions -/
section
noncomputable section
open scoped Topology
namespace AlgebraicNumberTheory
namespace Valuations
universe u v
 

abbrev AbsoluteValueExtension
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (L : Type v) [Field L] [Algebra K L] :=
  {w : AbsoluteValue L ℝ // AbsoluteValue.Extends vK w}
 
theorem AbsoluteValueExtension.isNontrivial
    {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    {vK : AbsoluteValue K ℝ}
    (u : AbsoluteValueExtension vK L)
    (hvK : vK.IsNontrivial) :
    u.1.IsNontrivial := by
  rcases hvK with ⟨a, ha, hva⟩
  refine
    ⟨algebraMap K L a,
      (map_ne_zero (algebraMap K L)).2 ha, ?_⟩
  simpa only [u.2 a] using hva
 
abbrev absoluteValueExtension_algebraicCompletionClosure
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ) :=
  AlgebraicClosure vK.Completion
 

noncomputable def absoluteValueExtension_algebraicClosureAbsoluteValue
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial) :
    AbsoluteValue (absoluteValueExtension_algebraicCompletionClosure vK) ℝ :=
  (AbsoluteValue.uniqueAlgebraicExtension
    (AbsoluteValue.completionAbsoluteValue vK)
    (AbsoluteValue.completionAbsoluteValue_complete vK)
    (AbsoluteValue.completionAbsoluteValue_isNontrivial vK hvK)).extension
@[simp]
theorem absoluteValueExtension_algebraicClosureAbsoluteValue_algebraMap
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial) (x : vK.Completion) :
    absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK
        (algebraMap vK.Completion
          (absoluteValueExtension_algebraicCompletionClosure vK) x) =
      AbsoluteValue.completionAbsoluteValue vK x := by
  exact
    (AbsoluteValue.uniqueAlgebraicExtension
      (AbsoluteValue.completionAbsoluteValue vK)
      (AbsoluteValue.completionAbsoluteValue_complete vK)
      (AbsoluteValue.completionAbsoluteValue_isNontrivial vK hvK)).isExtension x
 
noncomputable def absoluteValueExtension_localizationEmbedding
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (vK : AbsoluteValue K ℝ) (w : AbsoluteValueExtension vK L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    AbsoluteValue.algebraicLocalization vK w.1 w.2 →ₐ[vK.Completion]
      absoluteValueExtension_algebraicCompletionClosure vK := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  letI : Algebra.IsAlgebraic vK.Completion
      (AbsoluteValue.algebraicLocalization vK w.1 w.2) :=
    AbsoluteValue.algebraicLocalization_isAlgebraic vK w.1 w.2
  letI : Module.IsTorsionFree vK.Completion
      (AbsoluteValue.algebraicLocalization vK w.1 w.2) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (algebraMap vK.Completion
        (AbsoluteValue.algebraicLocalization vK w.1 w.2)).injective
  letI : Module.IsTorsionFree vK.Completion
      (absoluteValueExtension_algebraicCompletionClosure vK) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (algebraMap vK.Completion
        (absoluteValueExtension_algebraicCompletionClosure vK)).injective
  exact IsAlgClosed.lift
 

theorem absoluteValueExtension_localizationAbsoluteValue_eq_pullback
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2 =
      (absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK).comp
        (absoluteValueExtension_localizationEmbedding vK w).injective := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let : Algebra.IsAlgebraic vK.Completion
      (AbsoluteValue.algebraicLocalization vK w.1 w.2) :=
    AbsoluteValue.algebraicLocalization_isAlgebraic vK w.1 w.2
  let R := AbsoluteValue.uniqueAlgebraicExtension
    (K := vK.Completion) (L := AbsoluteValue.algebraicLocalization vK w.1 w.2)
    (AbsoluteValue.completionAbsoluteValue vK)
    (AbsoluteValue.completionAbsoluteValue_complete vK)
    (AbsoluteValue.completionAbsoluteValue_isNontrivial vK hvK)
  have hleft : AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2 = R.extension :=
    R.unique _ (AbsoluteValue.algebraicLocalizationAbsoluteValue_extends vK w.1 w.2)
  have hright :
      (absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK).comp
          (absoluteValueExtension_localizationEmbedding vK w).injective = R.extension := by
    apply R.unique
    intro x
    change absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK
      (absoluteValueExtension_localizationEmbedding vK w
        (algebraMap vK.Completion (AbsoluteValue.algebraicLocalization vK w.1 w.2) x)) = _
    rw [(absoluteValueExtension_localizationEmbedding vK w).commutes]
    exact absoluteValueExtension_algebraicClosureAbsoluteValue_algebraMap vK hvK x
  exact hleft.trans hright.symm
 
noncomputable def absoluteValueExtension_pullback
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (tau : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK) :
    AbsoluteValue L ℝ :=
  (absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK).comp tau.injective
 
theorem absoluteValueExtension_pullback_extends
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (tau : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK) :
    AbsoluteValue.Extends vK (absoluteValueExtension_pullback vK hvK tau) := by
  intro x
  change absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK
    (tau (algebraMap K L x)) = vK x
  rw [tau.commutes,
    IsScalarTower.algebraMap_apply K vK.Completion
      (absoluteValueExtension_algebraicCompletionClosure vK),
    absoluteValueExtension_algebraicClosureAbsoluteValue_algebraMap]
  exact AbsoluteValue.completionAbsoluteValue_coe vK x
 
noncomputable def absoluteValueExtension_embeddingOfExtension
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (vK : AbsoluteValue K ℝ) (w : AbsoluteValueExtension vK L) :
    L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  let phi := absoluteValueExtension_localizationEmbedding vK w
  refine
    { __ := phi.toRingHom.comp (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2)
      commutes' := ?_ }
  intro x
  change phi (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
    (algebraMap K L x)) = algebraMap K
      (absoluteValueExtension_algebraicCompletionClosure vK) x
  rw [AbsoluteValue.toAlgebraicLocalization_algebraMap,
    phi.commutes]
  rfl
 

theorem absoluteValueExtension_extension_eq_pullback_embeddingOfExtension
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    w.1 = absoluteValueExtension_pullback vK hvK
      (absoluteValueExtension_embeddingOfExtension vK w) := by
  ext x
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  have h := congrArg
    (fun a : AbsoluteValue (AbsoluteValue.algebraicLocalization vK w.1 w.2) ℝ =>
      a (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x))
    (absoluteValueExtension_localizationAbsoluteValue_eq_pullback vK hvK w)
  calc
    w.1 x = AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2
        (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x) :=
      (AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization vK w.1 w.2 x).symm
    _ = absoluteValueExtension_pullback vK hvK
        (absoluteValueExtension_embeddingOfExtension vK w) x := by
      change AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2
          (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x) =
        (absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK).comp
          (absoluteValueExtension_localizationEmbedding vK w).injective
          (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x)
      exact h
 
def AbsoluteValueExtensionConjugateOverCompletion
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ)
    (tau tau' : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK) : Prop :=
  ∃ sigma : absoluteValueExtension_algebraicCompletionClosure vK ≃ₐ[vK.Completion]
      absoluteValueExtension_algebraicCompletionClosure vK,
    ∀ x : L, tau' x = sigma (tau x)
 

theorem absoluteValueExtension_algebraicClosureAbsoluteValue_algEquiv
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial)
    (sigma : absoluteValueExtension_algebraicCompletionClosure vK
      ≃ₐ[vK.Completion] absoluteValueExtension_algebraicCompletionClosure vK)
    (x : absoluteValueExtension_algebraicCompletionClosure vK) :
    absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK (sigma x) =
      absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK x := by
  let R := AbsoluteValue.uniqueAlgebraicExtension
    (K := vK.Completion)
    (L := absoluteValueExtension_algebraicCompletionClosure vK)
    (AbsoluteValue.completionAbsoluteValue vK)
    (AbsoluteValue.completionAbsoluteValue_complete vK)
    (AbsoluteValue.completionAbsoluteValue_isNontrivial vK hvK)
  let a : AbsoluteValue (absoluteValueExtension_algebraicCompletionClosure vK) ℝ :=
    (absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK).comp
      (f := sigma.toRingHom) sigma.injective
  have ha : a = absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK := by
    change a = R.extension
    apply R.unique
    intro y
    change absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK
      (sigma (algebraMap vK.Completion
        (absoluteValueExtension_algebraicCompletionClosure vK) y)) = _
    rw [sigma.commutes]
    exact absoluteValueExtension_algebraicClosureAbsoluteValue_algebraMap vK hvK y
  exact congrArg (fun b : AbsoluteValue _ ℝ => b x) ha
 
theorem absoluteValueExtension_pullback_eq_of_conjugate
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    {tau tau' : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK}
    (hconj : AbsoluteValueExtensionConjugateOverCompletion vK tau tau') :
    absoluteValueExtension_pullback vK hvK tau =
      absoluteValueExtension_pullback vK hvK tau' := by
  rcases hconj with ⟨sigma, hsigma⟩
  ext x
  change absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK (tau x) =
    absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK (tau' x)
  rw [hsigma x, absoluteValueExtension_algebraicClosureAbsoluteValue_algEquiv]
 
noncomputable def absoluteValueExtension_algebraicClosureToCompletionRingHom
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial) :
    absoluteValueExtension_algebraicCompletionClosure vK →+*
      (absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK).Completion :=
  UniformSpace.Completion.coeRingHom.comp
    (WithAbs.equiv
      (absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK)).symm.toRingHom
@[simp]
theorem absoluteValueExtension_algebraicClosureToCompletionRingHom_apply
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial)
    (x : absoluteValueExtension_algebraicCompletionClosure vK) :
    absoluteValueExtension_algebraicClosureToCompletionRingHom vK hvK x =
      ((WithAbs.equiv
        (absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK)).symm x :
          (absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK).Completion) :=
  rfl
 


noncomputable def absoluteValueExtension_algebraicClosureCompletionAlgebra
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial) :
    Algebra vK.Completion
      (absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK).Completion :=
  ((absoluteValueExtension_algebraicClosureToCompletionRingHom vK hvK).comp
    (algebraMap vK.Completion
      (absoluteValueExtension_algebraicCompletionClosure vK))).toAlgebra
 
noncomputable def absoluteValueExtension_algebraicClosureToCompletionAlgHom
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial) :
    letI := absoluteValueExtension_algebraicClosureCompletionAlgebra vK hvK
    absoluteValueExtension_algebraicCompletionClosure vK →ₐ[vK.Completion]
      (absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK).Completion := by
  letI := absoluteValueExtension_algebraicClosureCompletionAlgebra vK hvK
  exact
    { __ := absoluteValueExtension_algebraicClosureToCompletionRingHom vK hvK
      commutes' _ := rfl }
 

noncomputable def absoluteValueExtension_embeddingToAlgebraicClosureCompletionRingHom
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (tau : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK) :
    WithAbs w.1 →+*
      (absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK).Completion :=
  (absoluteValueExtension_algebraicClosureToCompletionRingHom vK hvK).comp
    (tau.toRingHom.comp (WithAbs.equiv w.1).toRingHom)
theorem absoluteValueExtension_embeddingToAlgebraicClosureCompletion_norm
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (tau : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK)
    (htau : w.1 = absoluteValueExtension_pullback vK hvK tau)
    (x : WithAbs w.1) :
    ‖absoluteValueExtension_embeddingToAlgebraicClosureCompletionRingHom
        vK hvK w tau x‖ = ‖x‖ := by
  change ‖absoluteValueExtension_algebraicClosureToCompletionRingHom vK hvK
    (tau (WithAbs.equiv w.1 x))‖ = ‖x‖
  rw [absoluteValueExtension_algebraicClosureToCompletionRingHom_apply,
    UniformSpace.Completion.norm_coe, WithAbs.norm_eq_apply_ofAbs,
    WithAbs.norm_eq_apply_ofAbs]
  have h := congrArg (fun a : AbsoluteValue L ℝ =>
    a (WithAbs.equiv w.1 x)) htau
  exact h.symm
 

theorem absoluteValueExtension_embeddingToAlgebraicClosureCompletion_isometry
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (tau : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK)
    (htau : w.1 = absoluteValueExtension_pullback vK hvK tau) :
    Isometry (absoluteValueExtension_embeddingToAlgebraicClosureCompletionRingHom
      vK hvK w tau) :=
  AddMonoidHomClass.isometry_of_norm _
    (absoluteValueExtension_embeddingToAlgebraicClosureCompletion_norm
      vK hvK w tau htau)
 
noncomputable def absoluteValueExtension_embeddingCompletionMap
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (tau : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK)
    (htau : w.1 = absoluteValueExtension_pullback vK hvK tau) :
    w.1.Completion →+*
      (absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK).Completion :=
  (absoluteValueExtension_embeddingToAlgebraicClosureCompletion_isometry
    vK hvK w tau htau).extensionHom
@[simp]
theorem absoluteValueExtension_embeddingCompletionMap_coe
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (tau : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK)
    (htau : w.1 = absoluteValueExtension_pullback vK hvK tau)
    (x : WithAbs w.1) :
    absoluteValueExtension_embeddingCompletionMap vK hvK w tau htau
        (x : w.1.Completion) =
      absoluteValueExtension_embeddingToAlgebraicClosureCompletionRingHom
        vK hvK w tau x :=
  (absoluteValueExtension_embeddingToAlgebraicClosureCompletion_isometry
    vK hvK w tau htau).extensionHom_coe x
 
theorem absoluteValueExtension_embeddingCompletionMap_isometry
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (tau : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK)
    (htau : w.1 = absoluteValueExtension_pullback vK hvK tau) :
    Isometry (absoluteValueExtension_embeddingCompletionMap vK hvK w tau htau) :=
  (absoluteValueExtension_embeddingToAlgebraicClosureCompletion_isometry
    vK hvK w tau htau).completion_extension
 

theorem absoluteValueExtension_completionToAlgebraicClosureCompletion_isometry
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial) :
    Isometry ((absoluteValueExtension_algebraicClosureToCompletionRingHom vK hvK).comp
      (algebraMap vK.Completion
        (absoluteValueExtension_algebraicCompletionClosure vK))) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  change ‖absoluteValueExtension_algebraicClosureToCompletionRingHom vK hvK
    (algebraMap vK.Completion
      (absoluteValueExtension_algebraicCompletionClosure vK) x)‖ = ‖x‖
  rw [absoluteValueExtension_algebraicClosureToCompletionRingHom_apply,
    UniformSpace.Completion.norm_coe, WithAbs.norm_eq_apply_ofAbs]
  change absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK
    (algebraMap vK.Completion
      (absoluteValueExtension_algebraicCompletionClosure vK) x) = ‖x‖
  rw [absoluteValueExtension_algebraicClosureAbsoluteValue_algebraMap]
  rfl
 


theorem absoluteValueExtension_embeddingCompletionMap_completionMap
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (tau : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK)
    (htau : w.1 = absoluteValueExtension_pullback vK hvK tau)
    (x : vK.Completion) :
    absoluteValueExtension_embeddingCompletionMap vK hvK w tau htau
        (AbsoluteValue.completionMap vK w.1 w.2 x) =
      absoluteValueExtension_algebraicClosureToCompletionRingHom vK hvK
        (algebraMap vK.Completion
          (absoluteValueExtension_algebraicCompletionClosure vK) x) := by
  let f := (absoluteValueExtension_embeddingCompletionMap vK hvK w tau htau).comp
    (AbsoluteValue.completionMap vK w.1 w.2)
  let g := (absoluteValueExtension_algebraicClosureToCompletionRingHom vK hvK).comp
    (algebraMap vK.Completion
      (absoluteValueExtension_algebraicCompletionClosure vK))
  change f x = g x
  refine UniformSpace.Completion.induction_on (α := WithAbs vK) x ?_ ?_
  · exact isClosed_eq
      ((absoluteValueExtension_embeddingCompletionMap_isometry
          vK hvK w tau htau).continuous.comp
        (AbsoluteValue.completionMap_isometry vK w.1 w.2).continuous)
      (absoluteValueExtension_completionToAlgebraicClosureCompletion_isometry
        vK hvK).continuous
  · intro a
    dsimp [f, g]
    change absoluteValueExtension_embeddingCompletionMap vK hvK w tau htau
        (AbsoluteValue.completionMap vK w.1 w.2
          (algebraMap K vK.Completion (WithAbs.equiv vK a))) =
      absoluteValueExtension_algebraicClosureToCompletionRingHom vK hvK
        (algebraMap vK.Completion
          (absoluteValueExtension_algebraicCompletionClosure vK)
          (algebraMap K vK.Completion (WithAbs.equiv vK a)))
    rw [AbsoluteValue.completionMap_coe]
    change absoluteValueExtension_embeddingCompletionMap vK hvK w tau htau
        (((algebraMap (WithAbs vK) (WithAbs w.1)) a : WithAbs w.1) :
          w.1.Completion) =
      absoluteValueExtension_algebraicClosureToCompletionRingHom vK hvK
        (algebraMap vK.Completion
          (absoluteValueExtension_algebraicCompletionClosure vK)
            (a : vK.Completion))
    rw [absoluteValueExtension_embeddingCompletionMap_coe]
    change absoluteValueExtension_algebraicClosureToCompletionRingHom vK hvK
        (tau (algebraMap K L (WithAbs.equiv vK a))) =
      absoluteValueExtension_algebraicClosureToCompletionRingHom vK hvK
        (algebraMap vK.Completion
          (absoluteValueExtension_algebraicCompletionClosure vK)
            (algebraMap K vK.Completion (WithAbs.equiv vK a)))
    congr 1
    rw [tau.commutes,
      IsScalarTower.algebraMap_apply K vK.Completion
        (absoluteValueExtension_algebraicCompletionClosure vK)]
 
noncomputable def absoluteValueExtension_embeddingCompletionAlgHom
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (tau : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK)
    (htau : w.1 = absoluteValueExtension_pullback vK hvK tau) :
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI := absoluteValueExtension_algebraicClosureCompletionAlgebra vK hvK
    w.1.Completion →ₐ[vK.Completion]
      (absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK).Completion := by
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  letI := absoluteValueExtension_algebraicClosureCompletionAlgebra vK hvK
  exact
    { __ := absoluteValueExtension_embeddingCompletionMap vK hvK w tau htau
      commutes' x :=
        absoluteValueExtension_embeddingCompletionMap_completionMap
          vK hvK w tau htau x }
 

theorem absoluteValueExtension_embeddingCompletionAlgHom_mem_range
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (tau : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK)
    (htau : w.1 = absoluteValueExtension_pullback vK hvK tau)
    (z : AbsoluteValue.algebraicLocalization vK w.1 w.2) :
    letI := absoluteValueExtension_algebraicClosureCompletionAlgebra vK hvK
    absoluteValueExtension_embeddingCompletionAlgHom vK hvK w tau htau (z : w.1.Completion)
      ∈ (absoluteValueExtension_algebraicClosureToCompletionAlgHom vK hvK).range := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let := absoluteValueExtension_algebraicClosureCompletionAlgebra vK hvK
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  let F := absoluteValueExtension_embeddingCompletionAlgHom vK hvK w tau htau
  let j := absoluteValueExtension_algebraicClosureToCompletionAlgHom vK hvK
  change F (z : w.1.Completion) ∈ j.range
  apply IntermediateField.adjoin_induction
      (F := vK.Completion)
      (s := Set.range (AbsoluteValue.toCompletion w.1))
      (p := fun x _ => F x ∈ j.range)
      (x := (z : w.1.Completion))
  · intro x hx
    rcases hx with ⟨y, rfl⟩
    refine ⟨tau y, ?_⟩
    symm
    change absoluteValueExtension_embeddingCompletionMap vK hvK w tau htau
      (AbsoluteValue.toCompletion w.1 y) =
        absoluteValueExtension_algebraicClosureToCompletionRingHom vK hvK (tau y)
    change absoluteValueExtension_embeddingCompletionMap vK hvK w tau htau
      (((WithAbs.equiv w.1).symm y : WithAbs w.1) : w.1.Completion) = _
    rw [absoluteValueExtension_embeddingCompletionMap_coe]
    rfl
  · intro x
    refine ⟨algebraMap vK.Completion
      (absoluteValueExtension_algebraicCompletionClosure vK) x, ?_⟩
    exact (absoluteValueExtension_embeddingCompletionMap_completionMap
      vK hvK w tau htau x).symm
  · intro x y _ _ hx hy
    simpa only [map_add] using j.range.add_mem hx hy
  · intro x _ hx
    rcases hx with ⟨a, ha⟩
    refine ⟨a⁻¹, ?_⟩
    simpa only [map_inv₀] using congrArg Inv.inv ha
  · intro x y _ _ hx hy
    simpa only [map_mul] using j.range.mul_mem hx hy
  · exact z.property
 



noncomputable def absoluteValueExtension_localizationEmbeddingOfPullback
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (tau : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK)
    (htau : w.1 = absoluteValueExtension_pullback vK hvK tau) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    AbsoluteValue.algebraicLocalization vK w.1 w.2 →ₐ[vK.Completion]
      absoluteValueExtension_algebraicCompletionClosure vK := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  letI := absoluteValueExtension_algebraicClosureCompletionAlgebra vK hvK
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  let F := absoluteValueExtension_embeddingCompletionAlgHom vK hvK w tau htau
  let j := absoluteValueExtension_algebraicClosureToCompletionAlgHom vK hvK
  let f : E →ₐ[vK.Completion] j.range :=
    (F.comp E.val).codRestrict j.range
      (absoluteValueExtension_embeddingCompletionAlgHom_mem_range
        vK hvK w tau htau)
  exact (AlgEquiv.ofInjectiveField j).symm.toAlgHom.comp f
 

theorem absoluteValueExtension_localizationEmbeddingOfPullback_toLocalization
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (tau : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK)
    (htau : w.1 = absoluteValueExtension_pullback vK hvK tau)
    (x : L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    absoluteValueExtension_localizationEmbeddingOfPullback vK hvK w tau htau
        (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x) = tau x := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let := absoluteValueExtension_algebraicClosureCompletionAlgebra vK hvK
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  let F := absoluteValueExtension_embeddingCompletionAlgHom vK hvK w tau htau
  let j := absoluteValueExtension_algebraicClosureToCompletionAlgHom vK hvK
  apply j.injective
  change j ((AlgEquiv.ofInjectiveField j).symm
      ⟨F (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x),
        absoluteValueExtension_embeddingCompletionAlgHom_mem_range
          vK hvK w tau htau _⟩) = j (tau x)
  rw [show j ((AlgEquiv.ofInjectiveField j).symm
      ⟨F (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x),
        absoluteValueExtension_embeddingCompletionAlgHom_mem_range
          vK hvK w tau htau _⟩) =
      F (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x) by
        exact congrArg Subtype.val
          ((AlgEquiv.ofInjectiveField j).apply_symm_apply _)]
  change absoluteValueExtension_embeddingCompletionMap vK hvK w tau htau
      (AbsoluteValue.toCompletion w.1 x) =
    absoluteValueExtension_algebraicClosureToCompletionRingHom vK hvK (tau x)
  change absoluteValueExtension_embeddingCompletionMap vK hvK w tau htau
      (((WithAbs.equiv w.1).symm x : WithAbs w.1) : w.1.Completion) = _
  rw [absoluteValueExtension_embeddingCompletionMap_coe]
  rfl
 


theorem absoluteValueExtension_algHom_conjugate_in_algClosure
    {F E A : Type*} [Field F] [Field E] [Field A]
    [Algebra F E] [Algebra F A] [Algebra.IsAlgebraic F E]
    [IsAlgClosure F A]
    (phi phi' : E →ₐ[F] A) :
    ∃ sigma : A ≃ₐ[F] A, ∀ x : E, sigma (phi x) = phi' x := by
  let : IsAlgClosed A := IsAlgClosure.isAlgClosed F
  let : Algebra E A := phi.toRingHom.toAlgebra
  let : IsScalarTower F E A :=
    IsScalarTower.of_algebraMap_eq' phi.comp_algebraMap.symm
  let : Algebra.IsAlgebraic E A :=
    Algebra.IsAlgebraic.tower_top (K := F) E
  obtain ⟨psi, hpsi⟩ :=
    IsAlgClosed.surjective_domRestrict_of_isAlgebraic
      (K := F) (L := E) (M := A) (E := A) phi'
  let sigma : A ≃ₐ[F] A := AlgEquiv.ofBijective psi
    (Algebra.IsAlgebraic.algHom_bijective psi)
  refine ⟨sigma, fun x => ?_⟩
  have hx := DFunLike.congr_fun hpsi x
  change psi (phi x) = phi' x
  change psi (algebraMap E A x) = phi' x at hx
  rw [RingHom.algebraMap_toAlgebra] at hx
  have hphi : phi.toRingHom x = phi x :=
    congrFun (AlgHom.coe_toRingHom phi) x
  rw [hphi] at hx
  exact hx
 

theorem absoluteValueExtension_conjugate_of_pullback_eq
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    {tau tau' : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK}
    (h : absoluteValueExtension_pullback vK hvK tau =
      absoluteValueExtension_pullback vK hvK tau') :
    AbsoluteValueExtensionConjugateOverCompletion vK tau tau' := by
  let w : AbsoluteValueExtension vK L :=
    ⟨absoluteValueExtension_pullback vK hvK tau,
      absoluteValueExtension_pullback_extends vK hvK tau⟩
  have htau : w.1 = absoluteValueExtension_pullback vK hvK tau := rfl
  have htau' : w.1 = absoluteValueExtension_pullback vK hvK tau' := h
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let phi := absoluteValueExtension_localizationEmbeddingOfPullback
    vK hvK w tau htau
  let phi' := absoluteValueExtension_localizationEmbeddingOfPullback
    vK hvK w tau' htau'
  let : Algebra.IsAlgebraic vK.Completion
      (AbsoluteValue.algebraicLocalization vK w.1 w.2) :=
    AbsoluteValue.algebraicLocalization_isAlgebraic vK w.1 w.2
  obtain ⟨sigma, hsigma⟩ :=
    absoluteValueExtension_algHom_conjugate_in_algClosure phi phi'
  refine ⟨sigma, fun x => ?_⟩
  rw [← absoluteValueExtension_localizationEmbeddingOfPullback_toLocalization
      vK hvK w tau htau x,
    ← absoluteValueExtension_localizationEmbeddingOfPullback_toLocalization
      vK hvK w tau' htau' x]
  exact (hsigma (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x)).symm
 

theorem absoluteValueExtension_pullback_eq_iff_conjugate
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (tau tau' : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK) :
    absoluteValueExtension_pullback vK hvK tau =
        absoluteValueExtension_pullback vK hvK tau' ↔
      AbsoluteValueExtensionConjugateOverCompletion vK tau tau' := by
  constructor
  · exact absoluteValueExtension_conjugate_of_pullback_eq vK hvK
  · exact absoluteValueExtension_pullback_eq_of_conjugate vK hvK
end Valuations
end AlgebraicNumberTheory
end
end

/- ValuedFieldTheory.Valuation.Completion.FiniteLocalization -/
section
noncomputable section
namespace AlgebraicNumberTheory
namespace Valuations
universe u v
open scoped TensorProduct
 

noncomputable abbrev absoluteValueExtension_completionNontriviallyNormedField
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial) :
    NontriviallyNormedField vK.Completion :=
  NontriviallyNormedField.ofNormNeOne (by
    rcases AbsoluteValue.completionAbsoluteValue_isNontrivial vK hvK with
      ⟨x, hx0, hx1⟩
    exact ⟨x, hx0, hx1⟩)
 

noncomputable abbrev absoluteValueExtension_completionNormedAlgebra
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (w : AbsoluteValueExtension vK L) :
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    NormedAlgebra vK.Completion w.1.Completion := by
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  refine
    { __ := AbsoluteValue.completionAlgebra vK w.1 w.2
      norm_smul_le := fun r x ↦ ?_ }
  rw [Algebra.smul_def, norm_mul,
    AbsoluteValue.completionAlgebra_algebraMap]
  rw [(AbsoluteValue.completionMap_isometry vK w.1 w.2).norm_map_of_map_zero
    (map_zero (AbsoluteValue.completionMap vK w.1 w.2))]
 
noncomputable def absoluteValueExtension_localizationTensorHom
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (w : AbsoluteValueExtension vK L) :
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    vK.Completion ⊗[K] L →ₐ[vK.Completion] w.1.Completion := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  letI : IsScalarTower K vK.Completion w.1.Completion :=
    AbsoluteValue.completion_isScalarTower vK w.1 w.2
  exact Algebra.TensorProduct.lift
    (Algebra.ofId vK.Completion w.1.Completion)
    (AbsoluteValue.toCompletionAlgHom (K := K) w.1)
    (fun _ _ ↦ Commute.all _ _)
@[simp]
theorem absoluteValueExtension_localizationTensorHom_tmul
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (w : AbsoluteValueExtension vK L)
    (b : vK.Completion) (a : L) :
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    absoluteValueExtension_localizationTensorHom vK w (b ⊗ₜ[K] a) =
      algebraMap vK.Completion w.1.Completion b *
        AbsoluteValue.toCompletionAlgHom (K := K) w.1 a := by
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  rfl
 

theorem absoluteValueExtension_localizationTensorHom_surjective
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    Function.Surjective (absoluteValueExtension_localizationTensorHom vK w) := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let : NontriviallyNormedField vK.Completion :=
    absoluteValueExtension_completionNontriviallyNormedField vK hvK
  let : NormedAlgebra vK.Completion w.1.Completion :=
    absoluteValueExtension_completionNormedAlgebra vK w
  let : Module.Finite vK.Completion (vK.Completion ⊗[K] L) :=
    inferInstance
  let f := absoluteValueExtension_localizationTensorHom vK w
  let : Module.Finite vK.Completion f.toLinearMap.range :=
    Module.Finite.range f.toLinearMap
  have hrangeClosed : IsClosed (f.toLinearMap.range : Set w.1.Completion) :=
    Submodule.closed_of_finiteDimensional
      (𝕜 := vK.Completion) f.toLinearMap.range
  have hdense : DenseRange
      (AbsoluteValue.toCompletion w.1) :=
    AbsoluteValue.denseRange_toCompletion w.1
  have hrange : Set.range
      (AbsoluteValue.toCompletion w.1) ⊆
      (f.toLinearMap.range : Set w.1.Completion) := by
    rintro _ ⟨x, rfl⟩
    refine ⟨1 ⊗ₜ[K] x, ?_⟩
    change f (1 ⊗ₜ[K] x) = _
    rw [absoluteValueExtension_localizationTensorHom_tmul]
    simp [AbsoluteValue.toCompletionAlgHom]
  change Function.Surjective f.toLinearMap
  rw [← f.toLinearMap.range_eq_top]
  apply top_unique
  intro x _
  have hx : x ∈ closure
      (Set.range (AbsoluteValue.toCompletion w.1)) := by
    rw [hdense.closure_range]
    trivial
  exact closure_minimal hrange hrangeClosed hx
 

theorem absoluteValueExtension_finiteLocalization_eq_top
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    AbsoluteValue.algebraicLocalization vK w.1 w.2 = ⊤ := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  apply top_unique
  intro y _
  obtain ⟨z, rfl⟩ :=
    absoluteValueExtension_localizationTensorHom_surjective vK hvK w y
  induction z using TensorProduct.induction_on with
  | zero => exact E.zero_mem
  | tmul b x =>
      rw [absoluteValueExtension_localizationTensorHom_tmul]
      exact E.mul_mem (E.algebraMap_mem b)
        (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x).property
  | add x y hx hy =>
      simpa only [map_add] using E.add_mem (hx trivial) (hy trivial)
end Valuations
end AlgebraicNumberTheory
namespace AlgebraicNumberTheory
namespace Valuations
universe u v
open scoped TensorProduct
variable {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
end Valuations
end AlgebraicNumberTheory
end
end

/- ValuedFieldTheory.Ramification.HilbertRamification.AbsoluteValueConjugacy -/
section
noncomputable section
universe u v
namespace AlgebraicNumberTheory
namespace Valuations
 

def absoluteValueConjugate
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[K] L) : AbsoluteValue L ℝ :=
  w.comp (f := σ.toRingEquiv.toRingHom) σ.injective
@[simp] theorem absoluteValueConjugate_apply
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[K] L) (x : L) :
    absoluteValueConjugate w σ x = w (σ x) :=
  rfl
 

theorem absoluteValueConjugate_extends
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L) :
    AbsoluteValue.Extends vK (absoluteValueConjugate w.1 σ) := by
  intro x
  rw [absoluteValueConjugate_apply, σ.commutes, w.2 x]
 
def absoluteValueExtensionConjugate
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L) : AbsoluteValueExtension vK L :=
  ⟨absoluteValueConjugate w.1 σ,
    absoluteValueConjugate_extends vK w σ⟩
 


theorem equivalent_exactExtensions_eq
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w w' : AbsoluteValueExtension vK L)
    (h : LubinTate.Valuations.EquivalentAbsoluteValues w.1 w'.1) :
    w = w' := by
  rcases (LubinTate.Valuations.equivalentAbsoluteValues_iff_exists_rpow_eq w.1 w'.1).mp h with
    ⟨s, hs, hpow⟩
  rcases hvK with ⟨a, ha, hva⟩
  have hbase : vK a ^ s = vK a := by
    have hpoint := congrFun hpow (algebraMap K L a)
    simpa [w.2 a, w'.2 a] using hpoint
  have hs_one : s = 1 :=
    (Real.rpow_right_inj (vK.pos ha) hva).mp (by simpa using hbase)
  apply Subtype.ext
  ext x
  have hpoint := congrFun hpow x
  simpa [hs_one] using hpoint
 


theorem absoluteValueConjugacy_exists_conjugatingAlgEquiv
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w w' : AbsoluteValueExtension vK L) :
    ∃ σ : L ≃ₐ[K] L, w'.1 = absoluteValueConjugate w.1 σ := by
  let A := absoluteValueExtension_algebraicCompletionClosure vK
  let τ : L →ₐ[K] A := absoluteValueExtension_embeddingOfExtension vK w
  let τ' : L →ₐ[K] A := absoluteValueExtension_embeddingOfExtension vK w'
  let : Algebra L A := τ.toRingHom.toAlgebra
  let : IsScalarTower K L A :=
    IsScalarTower.of_algebraMap_eq' τ.comp_algebraMap.symm
  let σ : L ≃ₐ[K] L := Normal.algHomEquivAut K A L τ'
  refine ⟨σ, ?_⟩
  rw [absoluteValueExtension_extension_eq_pullback_embeddingOfExtension vK hvK w',
    absoluteValueExtension_extension_eq_pullback_embeddingOfExtension vK hvK w]
  ext x
  change
    absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK (τ' x) =
      absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK (τ (σ x))
  congr 1
  simpa [σ, τ, AlgHom.restrictNormal', RingHom.algebraMap_toAlgebra] using
    (τ'.restrictNormal_commutes L x).symm
 



theorem absoluteValueConjugacy
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w w' : AbsoluteValueExtension vK L) :
    ∃ σ : L ≃ₐ[K] L,
      w' = absoluteValueExtensionConjugate vK w σ := by
  rcases absoluteValueConjugacy_exists_conjugatingAlgEquiv vK hvK w w' with
    ⟨σ, hσ⟩
  exact ⟨σ, Subtype.ext hσ⟩
end Valuations
end AlgebraicNumberTheory
end
end

/- ValuedFieldTheory.Valuation.Completion.PolynomialFactors -/
section
noncomputable section
open Polynomial
open UniqueFactorizationMonoid
namespace ValuationTheory
namespace Completion
universe u v
 



noncomputable def polynomialNormalizedFactors
    {F : Type u} [Field F] (p : F[X]) : Multiset F[X] := by
  letI : DecidableEq F := Classical.decEq F
  letI : NormalizationMonoid F := inferInstance
  letI : NormalizationMonoid F[X] := Polynomial.instNormalizationMonoid
  exact normalizedFactors p
 

noncomputable def polynomialDistinctNormalizedFactors
    {F : Type u} [Field F] (p : F[X]) : Finset F[X] := by
  classical
  exact (polynomialNormalizedFactors p).toFinset
 
theorem polynomialNormalizedFactors_eq_of_associated
    {F : Type u} [Field F] {p q : F[X]} (h : Associated p q) :
    polynomialNormalizedFactors p = polynomialNormalizedFactors q := by
  classical
  dsimp [polynomialNormalizedFactors]
  exact h.normalizedFactors_eq
 
theorem polynomialDistinctNormalizedFactors_eq_of_associated
    {F : Type u} [Field F] {p q : F[X]} (h : Associated p q) :
    polynomialDistinctNormalizedFactors p =
      polynomialDistinctNormalizedFactors q := by
  classical
  dsimp [polynomialDistinctNormalizedFactors]
  rw [polynomialNormalizedFactors_eq_of_associated h]
 


abbrev DistinctNormalizedFactors
    {F : Type u} [Field F] (p : F[X]) :=
  {g : F[X] // g ∈ polynomialDistinctNormalizedFactors p}
 
abbrev PolynomialRootsIn
    {F : Type u} [Field F] (E : Type v) [Field E] [Algebra F E]
    (p : F[X]) :=
  {x : E // x ∈ p.rootSet E}
 
def rootMinpoly
    {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
    (p : F[X]) : PolynomialRootsIn E p → F[X] :=
  fun x => minpoly F (x : E)
 

abbrev rootMinpolySetoid
    {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
    (p : F[X]) : Setoid (PolynomialRootsIn E p) :=
  Setoid.ker (rootMinpoly p)
 
theorem rootMinpoly_mem_normalizedFactors
    {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
    [Algebra.IsAlgebraic F E] {p : F[X]} (hp : p ≠ 0)
    (x : PolynomialRootsIn E p) :
    rootMinpoly p x ∈ polynomialDistinctNormalizedFactors p := by
  classical
  dsimp [polynomialDistinctNormalizedFactors, polynomialNormalizedFactors]
  rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff hp]
  have hxint : IsIntegral F (x : E) :=
    (Algebra.IsAlgebraic.isAlgebraic (x : E)).isIntegral
  refine ⟨minpoly.irreducible hxint, minpoly.monic hxint, ?_⟩
  exact minpoly.dvd F (x : E) (Polynomial.mem_rootSet.mp x.2).2
 
theorem range_rootMinpoly_eq_distinctNormalizedFactors
    {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
    [Algebra.IsAlgebraic F E] [IsAlgClosed E]
    {p : F[X]} (hp : p ≠ 0) :
    Set.range (rootMinpoly p : PolynomialRootsIn E p → F[X]) =
      {g : F[X] | g ∈ polynomialDistinctNormalizedFactors p} := by
  classical
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact rootMinpoly_mem_normalizedFactors hp x
  · intro hg
    have hg' : g ∈ normalizedFactors p := by
      simpa only [polynomialDistinctNormalizedFactors,
        polynomialNormalizedFactors, Multiset.mem_toFinset, Set.mem_ofPred_eq] using hg
    obtain ⟨hgirred, hgmonic, hgdvd⟩ :=
      (Polynomial.mem_normalizedFactors_iff hp).mp hg'
    have hgdegree : g.degree ≠ 0 :=
      (degree_pos_of_irreducible hgirred).ne'
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero E g hgdegree
    have hxp : Polynomial.aeval x p = 0 :=
      aeval_eq_zero_of_dvd_aeval_eq_zero hgdvd hx
    have hxroot : x ∈ p.rootSet E := by
      rw [Polynomial.mem_rootSet]
      exact ⟨hp, hxp⟩
    refine ⟨⟨x, hxroot⟩, ?_⟩
    exact (minpoly.eq_of_irreducible_of_monic hgirred hx hgmonic).symm
 

noncomputable def rootClassesEquivDistinctNormalizedFactors
    {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
    [Algebra.IsAlgebraic F E] [IsAlgClosed E]
    {p : F[X]} (hp : p ≠ 0) :
    Quotient (rootMinpolySetoid (E := E) p) ≃
      DistinctNormalizedFactors p :=
  (Setoid.quotientKerEquivRange (rootMinpoly p)).trans
    (Equiv.setCongr (range_rootMinpoly_eq_distinctNormalizedFactors hp))
 


noncomputable def simpleEmbeddingsEquivMappedMinpolyRoots
    {K : Type u} {L : Type v} {K' E : Type*}
    [Field K] [Field L] [Field K'] [Field E]
    [Algebra K L] [Algebra K K'] [Algebra K E] [Algebra K' E]
    [IsScalarTower K K' E]
    (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤) :
    (L →ₐ[K] E) ≃
      PolynomialRootsIn E
        ((minpoly K α).map (algebraMap K K')) := by
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop hα hgen
  let p : K'[X] := (minpoly K α).map (algebraMap K K')
  have hpbgen : pb.gen = α := by simp [pb]
  have hp : p ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap K K').injective).2
      (minpoly.ne_zero hα)
  have hroot (τ : L →ₐ[K] E) : τ α ∈ p.rootSet E := by
    rw [Polynomial.mem_rootSet]
    refine ⟨hp, ?_⟩
    change Polynomial.aeval (τ α)
      ((minpoly K α).map (algebraMap K K')) = 0
    rw [aeval_map_algebraMap]
    rw [aeval_algHom_apply τ α (minpoly K α), minpoly.aeval, map_zero]
  have hbaseRoot (x : PolynomialRootsIn E p) :
      Polynomial.aeval (x : E) (minpoly K pb.gen) = 0 := by
    rw [hpbgen]
    exact (Polynomial.aeval_map_algebraMap K' (x : E) (minpoly K α)).symm.trans
      (Polynomial.mem_rootSet.mp x.2).2
  let toRoot : (L →ₐ[K] E) → PolynomialRootsIn E p :=
    fun τ => ⟨τ α, hroot τ⟩
  let fromRoot : PolynomialRootsIn E p → (L →ₐ[K] E) :=
    fun x => pb.lift (x : E) (hbaseRoot x)
  refine
    { toFun := toRoot
      invFun := fromRoot
      left_inv := ?_
      right_inv := ?_ }
  · intro τ
    apply pb.algHom_ext
    change pb.lift (τ α) _ pb.gen = τ pb.gen
    rw [pb.lift_gen, hpbgen]
  · intro x
    apply Subtype.ext
    change pb.lift (x : E) _ α = x
    calc
      pb.lift (x : E) _ α = pb.lift (x : E) _ pb.gen :=
        congrArg (pb.lift (x : E) (hbaseRoot x)) hpbgen.symm
      _ = x := pb.lift_gen (x : E) (hbaseRoot x)
end Completion
end ValuationTheory
end
end

/- ValuedFieldTheory.Valuation.Completion.ExtensionFactorClassification -/
section
noncomputable section
open Polynomial
open scoped Topology
open ValuationTheory.Completion
namespace AlgebraicNumberTheory
namespace Valuations
universe u v
 
abbrev completionExtensionFactor_completionPolynomial
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ) (f : K[X]) :
    vK.Completion[X] :=
  f.map (algebraMap K vK.Completion)
 

abbrev CompletionExtensionFactorCompletionFactors
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ) (f : K[X]) :=
  DistinctNormalizedFactors (completionExtensionFactor_completionPolynomial vK f)
 


theorem completionExtensionFactor_root_isIntegral
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {α : L} {f : K[X]} (hf : Irreducible f)
    (hroot : Polynomial.aeval α f = 0) : IsIntegral K α :=
  (show IsAlgebraic K α from ⟨f, hf.ne_zero, hroot⟩).isIntegral
 

theorem completionExtensionFactor_definingPolynomial_associated_minpoly
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {α : L} {f : K[X]} (hf : Irreducible f)
    (hroot : Polynomial.aeval α f = 0) :
    Associated f (minpoly K α) := by
  have hlead : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf.ne_zero
  have hunit : IsUnit (C f.leadingCoeff⁻¹ : K[X]) :=
    isUnit_C.mpr (IsUnit.mk0 f.leadingCoeff⁻¹ (inv_ne_zero hlead))
  exact (associated_mul_unit_right f (C f.leadingCoeff⁻¹) hunit).trans
    (Associated.of_eq (minpoly.eq_of_irreducible hf hroot))
 

theorem completionExtensionFactor_completionFactors_eq_minpolyFactors
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) {α : L} {f : K[X]}
    (hf : Irreducible f) (hroot : Polynomial.aeval α f = 0) :
    polynomialDistinctNormalizedFactors
        (completionExtensionFactor_completionPolynomial vK f) =
      polynomialDistinctNormalizedFactors
        ((minpoly K α).map (algebraMap K vK.Completion)) := by
  exact polynomialDistinctNormalizedFactors_eq_of_associated
    (Polynomial.associated_map_map (algebraMap K vK.Completion)
      (completionExtensionFactor_definingPolynomial_associated_minpoly hf hroot))
 

noncomputable def completionExtensionFactor_minpolyFactorsEquivCompletionFactors
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) {α : L} {f : K[X]}
    (hf : Irreducible f) (hroot : Polynomial.aeval α f = 0) :
    DistinctNormalizedFactors
        ((minpoly K α).map (algebraMap K vK.Completion)) ≃
      CompletionExtensionFactorCompletionFactors vK f :=
  Equiv.setCongr (by
    ext g
    exact Finset.ext_iff.mp
      (completionExtensionFactor_completionFactors_eq_minpolyFactors
        vK hf hroot).symm g)
 

abbrev CompletionExtensionFactorEmbeddingSetoid
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤) :
    Setoid (L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK) :=
  Setoid.comap
    (simpleEmbeddingsEquivMappedMinpolyRoots
      (K' := vK.Completion)
      (E := absoluteValueExtension_algebraicCompletionClosure vK)
      α hα hgen)
    (rootMinpolySetoid
      ((minpoly K α).map (algebraMap K vK.Completion)))
 

noncomputable def completionExtensionFactor_embeddingClassesEquivMinpolyFactors
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤) :
    Quotient (CompletionExtensionFactorEmbeddingSetoid vK α hα hgen) ≃
      DistinctNormalizedFactors
        ((minpoly K α).map (algebraMap K vK.Completion)) :=
  let e := simpleEmbeddingsEquivMappedMinpolyRoots
    (K' := vK.Completion)
    (E := absoluteValueExtension_algebraicCompletionClosure vK)
    α hα hgen
  (Quotient.congr e (fun _ _ => Iff.rfl)).trans
    (rootClassesEquivDistinctNormalizedFactors
      (E := absoluteValueExtension_algebraicCompletionClosure vK)
      ((Polynomial.map_ne_zero_iff
        (algebraMap K vK.Completion).injective).2 (minpoly.ne_zero hα)))
 

theorem completionExtensionFactor_embeddingSetoid_rel_iff_conjugate
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (τ τ' : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK) :
    (CompletionExtensionFactorEmbeddingSetoid vK α hα hgen).r τ τ' ↔
      AbsoluteValueExtensionConjugateOverCompletion vK τ τ' := by
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop hα hgen
  have hpbgen : pb.gen = α := by simp [pb]
  change IsConjRoot vK.Completion (τ α) (τ' α) ↔ _
  constructor
  · intro hconj
    obtain ⟨σ, hσ⟩ := IsConjRoot.exists_algEquiv hconj.symm
    refine ⟨σ, ?_⟩
    let στ : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK :=
      (σ.toAlgHom.restrictScalars K).comp τ
    have heq : τ' = στ := by
      apply pb.algHom_ext
      rw [hpbgen]
      exact hσ.symm
    intro x
    exact DFunLike.congr_fun heq x
  · rintro ⟨σ, hσ⟩
    change minpoly vK.Completion (τ α) = minpoly vK.Completion (τ' α)
    rw [hσ α]
    exact (minpoly.algEquiv_eq σ (τ α)).symm
 


noncomputable def pullbackAbsoluteValueExtension
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (τ : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK) :
    AbsoluteValueExtension vK L :=
  ⟨absoluteValueExtension_pullback vK hvK τ,
    absoluteValueExtension_pullback_extends vK hvK τ⟩
 



theorem completionExtensionFactor_pullback_eq_iff_embeddingSetoid_rel
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (τ τ' : L →ₐ[K] absoluteValueExtension_algebraicCompletionClosure vK) :
    absoluteValueExtension_pullback vK hvK τ =
        absoluteValueExtension_pullback vK hvK τ' ↔
      (CompletionExtensionFactorEmbeddingSetoid vK α hα hgen).r τ τ' := by
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop hα hgen
  let : FiniteDimensional K L := pb.finite
  let : Algebra.IsAlgebraic K L := inferInstance
  rw [completionExtensionFactor_embeddingSetoid_rel_iff_conjugate
    vK α hα hgen τ τ']
  exact absoluteValueExtension_pullback_eq_iff_conjugate vK hvK τ τ'
 

theorem completionExtensionFactor_extension_eq_pullback_embeddingOfExtension
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    w.1 = absoluteValueExtension_pullback vK hvK
      (absoluteValueExtension_embeddingOfExtension vK w) := by
  exact absoluteValueExtension_extension_eq_pullback_embeddingOfExtension vK hvK w
 

noncomputable def completionExtensionFactor_extensionsEquivEmbeddingClasses
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤) :
    AbsoluteValueExtension vK L ≃
      Quotient (CompletionExtensionFactorEmbeddingSetoid vK α hα hgen) := by
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop hα hgen
  letI : FiniteDimensional K L := pb.finite
  letI : Algebra.IsAlgebraic K L := inferInstance
  let fromClass :
      Quotient (CompletionExtensionFactorEmbeddingSetoid vK α hα hgen) →
        AbsoluteValueExtension vK L :=
    Quotient.lift
      (pullbackAbsoluteValueExtension vK hvK)
      (by
        intro τ τ' hrel
        apply Subtype.ext
        exact (completionExtensionFactor_pullback_eq_iff_embeddingSetoid_rel
          vK hvK α hα hgen τ τ').2 hrel)
  refine
    { toFun := fun w => Quotient.mk
        (CompletionExtensionFactorEmbeddingSetoid vK α hα hgen)
        (absoluteValueExtension_embeddingOfExtension vK w)
      invFun := fromClass
      left_inv := ?_
      right_inv := ?_ }
  · intro w
    apply Subtype.ext
    exact (completionExtensionFactor_extension_eq_pullback_embeddingOfExtension
      vK hvK w).symm
  · intro q
    induction q using Quotient.inductionOn with
    | _ τ =>
      apply Quotient.sound
      let wτ : AbsoluteValueExtension vK L :=
        pullbackAbsoluteValueExtension vK hvK τ
      apply (completionExtensionFactor_pullback_eq_iff_embeddingSetoid_rel
        vK hvK α hα hgen
        (absoluteValueExtension_embeddingOfExtension vK wτ) τ).1
      exact (completionExtensionFactor_extension_eq_pullback_embeddingOfExtension
        vK hvK wτ).symm
 

noncomputable def completionExtensionFactor_extensionsEquivMinpolyFactors
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤) :
    AbsoluteValueExtension vK L ≃
      DistinctNormalizedFactors
        ((minpoly K α).map (algebraMap K vK.Completion)) :=
  (completionExtensionFactor_extensionsEquivEmbeddingClasses
      vK hvK α hα hgen).trans
    (completionExtensionFactor_embeddingClassesEquivMinpolyFactors
      vK α hα hgen)
 

noncomputable def completionExtensionFactor_extensionsEquivCompletionFactorsAux
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    {α : L} {f : K[X]} (hf : Irreducible f)
    (hroot : Polynomial.aeval α f = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤) :
    AbsoluteValueExtension vK L ≃
      CompletionExtensionFactorCompletionFactors vK f :=
  let hα := completionExtensionFactor_root_isIntegral hf hroot
  (completionExtensionFactor_extensionsEquivMinpolyFactors
      vK hvK α hα hgen).trans
    (completionExtensionFactor_minpolyFactorsEquivCompletionFactors
      vK hf hroot)
 

noncomputable def completionExtensionFactor_extensionFactor
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (α : L)
    (w : AbsoluteValueExtension vK L) : vK.Completion[X] := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  exact minpoly vK.Completion
    (AbsoluteValue.toCompletionAlgHom (K := K) w.1 α)
 

theorem completionExtensionFactor_extensionFactor_mem
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) {α : L} {f : K[X]}
    (hf : Irreducible f) (hroot : Polynomial.aeval α f = 0)
    (w : AbsoluteValueExtension vK L) :
    completionExtensionFactor_extensionFactor vK α w ∈
      polynomialDistinctNormalizedFactors
        (completionExtensionFactor_completionPolynomial vK f) := by
  classical
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let hKv := AbsoluteValue.completionAlgebra vK w.1 w.2
  let : IsScalarTower K vK.Completion w.1.Completion :=
    AbsoluteValue.completion_isScalarTower vK w.1 w.2
  let ι : L →ₐ[K] w.1.Completion :=
    AbsoluteValue.toCompletionAlgHom (K := K) w.1
  let a : w.1.Completion := ι α
  have hαalg : IsAlgebraic K α := ⟨f, hf.ne_zero, hroot⟩
  have hα : IsIntegral K α := hαalg.isIntegral
  have haK : IsIntegral K a := by
      exact IsIntegral.map_of_comp_eq (RingHom.id K) ι.toRingHom
        (by ext x; simp) hα
  have haKv : IsIntegral vK.Completion a :=
    IsIntegral.tower_top haK
  have hp0 : completionExtensionFactor_completionPolynomial vK f ≠ 0 :=
    (Polynomial.map_ne_zero_iff
      (algebraMap K vK.Completion).injective).2 hf.ne_zero
  have haf : Polynomial.aeval a
      (completionExtensionFactor_completionPolynomial vK f) = 0 := by
    change Polynomial.aeval (ι α)
      (f.map (algebraMap K vK.Completion)) = 0
    rw [Polynomial.aeval_map_algebraMap]
    rw [Polynomial.aeval_algHom_apply ι α f, hroot, map_zero]
  dsimp [completionExtensionFactor_extensionFactor,
    polynomialDistinctNormalizedFactors, polynomialNormalizedFactors]
  rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff hp0]
  exact ⟨minpoly.irreducible haKv, minpoly.monic haKv,
    minpoly.dvd vK.Completion a haf⟩
 
noncomputable def completionExtensionFactor_extensionToFactor
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) {α : L} {f : K[X]}
    (hf : Irreducible f) (hroot : Polynomial.aeval α f = 0) :
    AbsoluteValueExtension vK L →
      CompletionExtensionFactorCompletionFactors vK f :=
  fun w => ⟨completionExtensionFactor_extensionFactor vK α w,
    completionExtensionFactor_extensionFactor_mem vK hf hroot w⟩
 


theorem completionExtensionFactor_embeddingOfExtension_minpoly
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (vK : AbsoluteValue K ℝ) (α : L)
    (w : AbsoluteValueExtension vK L) :
    minpoly vK.Completion
        (absoluteValueExtension_embeddingOfExtension vK w α) =
      completionExtensionFactor_extensionFactor vK α w := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let a := AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 α
  calc
    minpoly vK.Completion
        (absoluteValueExtension_embeddingOfExtension vK w α) =
        minpoly vK.Completion a :=
      minpoly.algHom_eq
        (absoluteValueExtension_localizationEmbedding vK w)
        (absoluteValueExtension_localizationEmbedding vK w).injective a
    _ = minpoly vK.Completion
        (AbsoluteValue.toCompletionAlgHom (K := K) w.1 α) := by
      rw [← minpoly.algHom_eq
        (AbsoluteValue.algebraicLocalization vK w.1 w.2).val
        (AbsoluteValue.algebraicLocalization vK w.1 w.2).val.injective a]
      rfl
    _ = completionExtensionFactor_extensionFactor vK α w := rfl
 


theorem completionExtensionFactor_completion_adjoin_eq_top
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (w : AbsoluteValueExtension vK L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    Algebra.adjoin vK.Completion
        ({AbsoluteValue.toCompletionAlgHom (K := K) w.1 α} :
          Set w.1.Completion) = ⊤ := by
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop hα hgen
  let : FiniteDimensional K L := pb.finite
  let : Algebra.IsAlgebraic K L := inferInstance
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let : IsScalarTower K vK.Completion w.1.Completion :=
    AbsoluteValue.completion_isScalarTower vK w.1 w.2
  let ι : L →ₐ[K] w.1.Completion :=
    AbsoluteValue.toCompletionAlgHom (K := K) w.1
  let a : w.1.Completion := ι α
  have haK : IsIntegral K a := by
      exact IsIntegral.map_of_comp_eq (RingHom.id K) ι.toRingHom
        (by ext x; simp) hα
  have haKv : IsIntegral vK.Completion a :=
    IsIntegral.tower_top haK
  have hrange : Set.range
      (AbsoluteValue.toCompletion w.1) ⊆
      (IntermediateField.adjoin vK.Completion ({a} : Set w.1.Completion) :
        Set w.1.Completion) := by
    rintro _ ⟨x, rfl⟩
    change ι x ∈ IntermediateField.adjoin vK.Completion ({a} : Set _)
    have hx : x ∈ Algebra.adjoin K ({α} : Set L) := by
      rw [hgen]
      trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
        rw [Set.mem_singleton_iff.mp hx]
        exact IntermediateField.mem_adjoin_simple_self vK.Completion a
    | algebraMap x =>
        rw [ι.commutes,
          IsScalarTower.algebraMap_apply K vK.Completion w.1.Completion]
        exact (IntermediateField.adjoin vK.Completion ({a} : Set _)).algebraMap_mem _
    | add x y _ _ hx hy =>
        simpa only [map_add] using
          (IntermediateField.adjoin vK.Completion ({a} : Set _)).add_mem hx hy
    | mul x y _ _ hx hy =>
        simpa only [map_mul] using
          (IntermediateField.adjoin vK.Completion ({a} : Set _)).mul_mem hx hy
  have hloc_le : AbsoluteValue.algebraicLocalization vK w.1 w.2 ≤
      IntermediateField.adjoin vK.Completion ({a} : Set _) := by
    exact IntermediateField.adjoin_le_iff.mpr hrange
  have hsimple : IntermediateField.adjoin vK.Completion ({a} : Set _) = ⊤ := by
    apply top_unique
    rw [← absoluteValueExtension_finiteLocalization_eq_top vK hvK w]
    exact hloc_le
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      haKv.isAlgebraic,
    hsimple, IntermediateField.top_toSubalgebra]
 

noncomputable def completionExtensionFactor_adjoinRootEquivCompletion
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (w : AbsoluteValueExtension vK L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    AdjoinRoot (completionExtensionFactor_extensionFactor vK α w) ≃ₐ[vK.Completion]
      w.1.Completion := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  letI : IsScalarTower K vK.Completion w.1.Completion :=
    AbsoluteValue.completion_isScalarTower vK w.1 w.2
  let ι : L →ₐ[K] w.1.Completion :=
    AbsoluteValue.toCompletionAlgHom (K := K) w.1
  let a : w.1.Completion := ι α
  have haK : IsIntegral K a := by
      exact IsIntegral.map_of_comp_eq (RingHom.id K) ι.toRingHom
        (by ext x; simp) hα
  have haKv : IsIntegral vK.Completion a :=
    IsIntegral.tower_top haK
  have htop : Algebra.adjoin vK.Completion ({a} : Set w.1.Completion) = ⊤ :=
    completionExtensionFactor_completion_adjoin_eq_top
      vK hvK α hα hgen w
  change AdjoinRoot (minpoly vK.Completion a) ≃ₐ[vK.Completion]
    w.1.Completion
  exact (@minpoly.equivAdjoin vK.Completion w.1.Completion _ _ _ _ _ _
    (Module.isTorsionFree_iff_algebraMap_injective.mpr
      (algebraMap vK.Completion w.1.Completion).injective) a haKv).trans
    ((Subalgebra.equivOfEq _ _ htop).trans Subalgebra.topEquiv)
 

@[simp]
theorem completionExtensionFactor_adjoinRootEquivCompletion_root
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (w : AbsoluteValueExtension vK L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    completionExtensionFactor_adjoinRootEquivCompletion vK hvK α hα hgen w
        (AdjoinRoot.root (completionExtensionFactor_extensionFactor vK α w)) =
      AbsoluteValue.toCompletionAlgHom (K := K) w.1 α := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let : IsScalarTower K vK.Completion w.1.Completion :=
    AbsoluteValue.completion_isScalarTower vK w.1 w.2
  let ι : L →ₐ[K] w.1.Completion :=
    AbsoluteValue.toCompletionAlgHom (K := K) w.1
  let a : w.1.Completion := ι α
  change ((AdjoinRoot.Minpoly.toAdjoin vK.Completion a)
      (AdjoinRoot.root (minpoly vK.Completion a)) : w.1.Completion) = a
  exact AdjoinRoot.Minpoly.coe_toAdjoin_mk_X
    (R := vK.Completion) (x := a)
 

theorem completionExtensionFactor_extensionsEquivCompletionFactorsAux_apply
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    {α : L} {f : K[X]} (hf : Irreducible f)
    (hroot : Polynomial.aeval α f = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (w : AbsoluteValueExtension vK L) :
    (completionExtensionFactor_extensionsEquivCompletionFactorsAux
        vK hvK hf hroot hgen w).1 =
      completionExtensionFactor_extensionFactor vK α w := by
  let hα := completionExtensionFactor_root_isIntegral hf hroot
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop hα hgen
  let : FiniteDimensional K L := pb.finite
  let : Algebra.IsAlgebraic K L := inferInstance
  change minpoly vK.Completion
      (absoluteValueExtension_embeddingOfExtension vK w α) =
    completionExtensionFactor_extensionFactor vK α w
  exact completionExtensionFactor_embeddingOfExtension_minpoly vK α w
 



noncomputable def completionExtensionFactor_extensionEquivFactors
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    {α : L} {f : K[X]} (hf : Irreducible f)
    (hroot : Polynomial.aeval α f = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤) :
    AbsoluteValueExtension vK L ≃
      CompletionExtensionFactorCompletionFactors vK f := by
  let e := completionExtensionFactor_extensionsEquivCompletionFactorsAux
    vK hvK hf hroot hgen
  apply Equiv.ofBijective
    (completionExtensionFactor_extensionToFactor vK hf hroot)
  have heq : completionExtensionFactor_extensionToFactor vK hf hroot = e := by
    funext w
    apply Subtype.ext
    exact (completionExtensionFactor_extensionsEquivCompletionFactorsAux_apply
      vK hvK hf hroot hgen w).symm
  rw [heq]
  exact e.bijective
end Valuations
end AlgebraicNumberTheory
end
end

/- ValuedFieldTheory.Valuation.Completion.SeparablePolynomialFactors -/
section
noncomputable section
open Polynomial UniqueFactorizationMonoid
open scoped BigOperators
namespace ValuationTheory
namespace Completion
universe u
 

theorem separable_monic_eq_prod_distinctNormalizedFactors
    {F : Type u} [Field F] (p : F[X])
    (hpmonic : p.Monic) (hpsep : p.Separable) :
    p = ∏ g : DistinctNormalizedFactors p, (g.1 : F[X]) := by
  classical
  let : NormalizationMonoid F := inferInstance
  let : NormalizationMonoid F[X] := Polynomial.instNormalizationMonoid
  have hp0 : p ≠ 0 := hpmonic.ne_zero
  have hnodup : (normalizedFactors p).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hp0).1 hpsep.squarefree
  have hprod : (normalizedFactors p).prod = p := by
    simpa [hpmonic.leadingCoeff] using
      (Polynomial.leadingCoeff_mul_prod_normalizedFactors p)
  calc
    p = (normalizedFactors p).prod := hprod.symm
    _ = ∏ g : DistinctNormalizedFactors p, (g.1 : F[X]) := by
      change (normalizedFactors p).prod =
        ∏ g : {g : F[X] // g ∈ (normalizedFactors p).toFinset}, g.1
      rw [Finset.univ_eq_attach,
        Finset.prod_attach (f := fun x : F[X] ↦ x)]
      change (normalizedFactors p).prod =
        ((normalizedFactors p).toFinset.1.map id).prod
      rw [Multiset.toFinset_val, hnodup.dedup, Multiset.map_id]
 
theorem distinctNormalizedFactors_pairwise_coprime
    {F : Type u} [Field F] (p : F[X]) :
    ∀ i j : DistinctNormalizedFactors p, i ≠ j →
      IsCoprime (i.1 : F[X]) j.1 := by
  classical
  let : NormalizationMonoid F := inferInstance
  let : NormalizationMonoid F[X] := Polynomial.instNormalizationMonoid
  intro i j hij
  have hnorm : polynomialNormalizedFactors p = normalizedFactors p := by
    rfl
  have hi : i.1 ∈ normalizedFactors p := by
    rw [← hnorm]
    exact Multiset.mem_toFinset.mp i.2
  have hj : j.1 ∈ normalizedFactors p := by
    rw [← hnorm]
    exact Multiset.mem_toFinset.mp j.2
  rcases (prime_of_normalized_factor i.1 hi).irreducible.isCoprime_or_dvd j.1 with h | h
  · exact h
  · exfalso
    apply hij
    apply Subtype.ext
    exact normalizedFactors_eq_of_dvd p i.1 hi j.1 hj h
end Completion
end ValuationTheory
end
end

/- ValuedFieldTheory.Valuation.Completion.BaseChangeAdjoinRoot -/
section
noncomputable section
namespace ValuationTheory
namespace Completion
universe u v w
open scoped TensorProduct Polynomial
 
noncomputable def powerBasisBaseChange
    {K A L : Type*} [Field K] [Field A] [Field L]
    [Algebra K A] [Algebra K L]
    (pb : PowerBasis K L) : PowerBasis A (A ⊗[K] L) where
  gen := 1 ⊗ₜ[K] pb.gen
  dim := pb.dim
  basis := Algebra.TensorProduct.basis A pb.basis
  basis_eq_pow i := by
    rw [Algebra.TensorProduct.basis_apply, pb.basis_eq_pow]
    simp [Algebra.TensorProduct.tmul_pow]
 
@[simp]
theorem powerBasisBaseChange_gen
    {K A L : Type*} [Field K] [Field A] [Field L]
    [Algebra K A] [Algebra K L]
    (pb : PowerBasis K L) :
    (powerBasisBaseChange (A := A) pb).gen = 1 ⊗ₜ[K] pb.gen :=
  rfl
 
theorem minpoly_map_aeval_one_tmul
    {K A L : Type*} [Field K] [Field A] [Field L]
    [Algebra K A] [Algebra K L]
    (pb : PowerBasis K L) :
    Polynomial.aeval (1 ⊗ₜ[K] pb.gen : A ⊗[K] L)
      ((minpoly K pb.gen).map (algebraMap K A)) = 0 := by
  rw [Polynomial.aeval_map_algebraMap]
  show Polynomial.aeval
      ((Algebra.TensorProduct.includeRight : L →ₐ[K] A ⊗[K] L) pb.gen)
        (minpoly K pb.gen) = 0
  rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
 

noncomputable def adjoinRootToBaseChange
    {K A L : Type*} [Field K] [Field A] [Field L]
    [Algebra K A] [Algebra K L]
    (pb : PowerBasis K L) :
    AdjoinRoot ((minpoly K pb.gen).map (algebraMap K A)) →ₐ[A]
      A ⊗[K] L :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId A (A ⊗[K] L))
    (1 ⊗ₜ[K] pb.gen) (by
      change Polynomial.aeval (1 ⊗ₜ[K] pb.gen : A ⊗[K] L)
        ((minpoly K pb.gen).map (algebraMap K A)) = 0
      exact minpoly_map_aeval_one_tmul (A := A) pb)
 
@[simp]
theorem adjoinRootToBaseChange_root
    {K A L : Type*} [Field K] [Field A] [Field L]
    [Algebra K A] [Algebra K L]
    (pb : PowerBasis K L) :
    adjoinRootToBaseChange (A := A) pb
        (AdjoinRoot.root ((minpoly K pb.gen).map (algebraMap K A))) =
      1 ⊗ₜ[K] pb.gen := by
  simp [adjoinRootToBaseChange]
 
theorem adjoinRootToBaseChange_surjective
    {K A L : Type*} [Field K] [Field A] [Field L]
    [Algebra K A] [Algebra K L]
    (pb : PowerBasis K L) :
    Function.Surjective (adjoinRootToBaseChange (A := A) pb) := by
  let q := (minpoly K pb.gen).map (algebraMap K A)
  let e := adjoinRootToBaseChange (A := A) pb
  let b := (powerBasisBaseChange (A := A) pb).basis
  change Function.Surjective e.toLinearMap
  rw [← e.toLinearMap.range_eq_top]
  apply top_unique
  rw [← b.span_eq]
  apply Submodule.span_le.2
  rintro _ ⟨i, rfl⟩
  refine ⟨AdjoinRoot.root q ^ (i : ℕ), ?_⟩
  change e (AdjoinRoot.root q ^ (i : ℕ)) = b i
  rw [map_pow, (powerBasisBaseChange (A := A) pb).basis_eq_pow,
    adjoinRootToBaseChange_root]
  rw [powerBasisBaseChange_gen, Algebra.TensorProduct.tmul_pow, one_pow]
 
theorem adjoinRoot_baseChange_finrank_eq
    {K A L : Type*} [Field K] [Field A] [Field L]
    [Algebra K A] [Algebra K L]
    (pb : PowerBasis K L) :
    Module.finrank A
        (AdjoinRoot ((minpoly K pb.gen).map (algebraMap K A))) =
      Module.finrank A (A ⊗[K] L) := by
  let q := (minpoly K pb.gen).map (algebraMap K A)
  let hq : q.Monic :=
    (minpoly.monic pb.isIntegral_gen).map (algebraMap K A)
  let qpb : PowerBasis A (AdjoinRoot q) := AdjoinRoot.powerBasis' hq
  calc
    Module.finrank A (AdjoinRoot q) = q.natDegree := qpb.finrank
    _ = (minpoly K pb.gen).natDegree :=
      (minpoly.monic pb.isIntegral_gen).natDegree_map (algebraMap K A)
    _ = pb.dim := pb.natDegree_minpoly
    _ = Module.finrank A (A ⊗[K] L) :=
      (powerBasisBaseChange (A := A) pb).finrank.symm
 

noncomputable def adjoinRootEquivBaseChange
    {K A L : Type*} [Field K] [Field A] [Field L]
    [Algebra K A] [Algebra K L]
    (pb : PowerBasis K L) :
    AdjoinRoot ((minpoly K pb.gen).map (algebraMap K A)) ≃ₐ[A]
      A ⊗[K] L := by
  let q := (minpoly K pb.gen).map (algebraMap K A)
  let hq : q.Monic :=
    (minpoly.monic pb.isIntegral_gen).map (algebraMap K A)
  letI : Module.Finite A (AdjoinRoot q) := hq.finite_adjoinRoot
  letI : Module.Finite A (A ⊗[K] L) :=
    (powerBasisBaseChange (A := A) pb).finite
  exact AlgEquiv.ofBijective (adjoinRootToBaseChange (A := A) pb)
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (adjoinRoot_baseChange_finrank_eq (A := A) pb)
        (f := (adjoinRootToBaseChange (A := A) pb).toLinearMap)).2
      (adjoinRootToBaseChange_surjective (A := A) pb),
      adjoinRootToBaseChange_surjective (A := A) pb⟩
 
@[simp]
theorem adjoinRootEquivBaseChange_root
    {K A L : Type*} [Field K] [Field A] [Field L]
    [Algebra K A] [Algebra K L]
    (pb : PowerBasis K L) :
    adjoinRootEquivBaseChange (A := A) pb
        (AdjoinRoot.root ((minpoly K pb.gen).map (algebraMap K A))) =
      1 ⊗ₜ[K] pb.gen := by
  change adjoinRootToBaseChange (A := A) pb
      (AdjoinRoot.root ((minpoly K pb.gen).map (algebraMap K A))) = _
  exact adjoinRootToBaseChange_root (A := A) pb
 
noncomputable def baseChangeEquivAdjoinRoot
    {K A L : Type*} [Field K] [Field A] [Field L]
    [Algebra K A] [Algebra K L]
    (pb : PowerBasis K L) :
    A ⊗[K] L ≃ₐ[A]
      AdjoinRoot ((minpoly K pb.gen).map (algebraMap K A)) :=
  (adjoinRootEquivBaseChange (A := A) pb).symm
 
@[simp]
theorem baseChangeEquivAdjoinRoot_one_tmul_gen
    {K A L : Type*} [Field K] [Field A] [Field L]
    [Algebra K A] [Algebra K L]
    (pb : PowerBasis K L) :
    baseChangeEquivAdjoinRoot (A := A) pb (1 ⊗ₜ[K] pb.gen) =
      AdjoinRoot.root ((minpoly K pb.gen).map (algebraMap K A)) := by
  change (adjoinRootEquivBaseChange (A := A) pb).symm
      (1 ⊗ₜ[K] pb.gen) = _
  rw [← adjoinRootEquivBaseChange_root]
  exact (adjoinRootEquivBaseChange (A := A) pb).symm_apply_apply _
end Completion
end ValuationTheory
end
end

/- ValuedFieldTheory.Valuation.Completion.PolynomialCRT -/
section
noncomputable section
namespace ValuationTheory
namespace Completion
universe u v
open scoped Polynomial
open Function
 

noncomputable def quotientInfAlgEquivPiQuotient
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type*} [Finite ι]
    (I : ι → Ideal A) (hI : Pairwise (IsCoprime on I)) :
    (A ⧸ ⨅ i, I i) ≃ₐ[R] ∀ i, A ⧸ I i where
  __ := Ideal.quotientInfRingEquivPiQuotient I hI
  commutes' r := by
    ext i
    rfl
 


noncomputable def adjoinRootProdEquivPi
    {F : Type u} [Field F] {ι : Type v} [Fintype ι]
    (f : ι → F[X])
    (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j)) :
    AdjoinRoot (∏ i, f i) ≃ₐ[F] ∀ i, AdjoinRoot (f i) := by
  let I : ι → Ideal F[X] := fun i => Ideal.span ({f i} : Set F[X])
  have hI : Pairwise (IsCoprime on I) := by
    intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff (f i) (f j)).2
      (hf i j hij)
  have hInf : Ideal.span ({∏ i, f i} : Set F[X]) = ⨅ i, I i := by
    symm
    exact Ideal.iInf_span_singleton hf
  exact
    (Ideal.quotientEquivAlgOfEq F hInf).trans
      (quotientInfAlgEquivPiQuotient I hI)
 

@[simp]
theorem adjoinRootProdEquivPi_mk
    {F : Type u} [Field F] {ι : Type v} [Fintype ι]
    (f : ι → F[X])
    (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j))
    (g : F[X]) (i : ι) :
    adjoinRootProdEquivPi f hf (AdjoinRoot.mk (∏ i, f i) g) i =
      AdjoinRoot.mk (f i) g := by
  change Ideal.Quotient.mk (Ideal.span ({f i} : Set F[X])) g =
    Ideal.Quotient.mk (Ideal.span ({f i} : Set F[X])) g
  rfl
end Completion
end ValuationTheory
end
end

/- ValuedFieldTheory.Valuation.Completion.CanonicalTensorMap -/
section
noncomputable section
namespace AlgebraicNumberTheory
namespace Valuations
universe u v
open scoped TensorProduct
 
noncomputable def completionTensorMap_leftCanonicalHom
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) :
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    vK.Completion ⊗[K] L →ₐ[vK.Completion]
      ∀ w : AbsoluteValueExtension vK L, w.1.Completion := by
  letI : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  exact AlgHom.pi fun w ↦
    absoluteValueExtension_localizationTensorHom vK w
@[simp]
theorem completionTensorMap_leftCanonicalHom_tmul_apply
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (b : vK.Completion) (a : L)
    (w : AbsoluteValueExtension vK L) :
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    completionTensorMap_leftCanonicalHom vK (b ⊗ₜ[K] a) w =
      algebraMap vK.Completion w.1.Completion b *
        AbsoluteValue.toCompletionAlgHom (K := K) w.1 a := by
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  exact absoluteValueExtension_localizationTensorHom_tmul vK w b a
end Valuations
end AlgebraicNumberTheory
end
end

/- ValuedFieldTheory.Valuation.Completion.TensorProductDecomposition -/
section
noncomputable section
open Polynomial
open scoped BigOperators TensorProduct
open ValuationTheory.Completion
namespace AlgebraicNumberTheory
namespace Valuations
universe u v
 

noncomputable def completionTensorDecomposition_powerBasis
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] : PowerBasis K L :=
  Field.powerBasisOfFiniteOfSeparable K L
 
noncomputable abbrev completionTensorDecomposition_extensionFintype
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    Fintype (AbsoluteValueExtension vK L) := by
  let pb := completionTensorDecomposition_powerBasis K L
  let hf : Irreducible (minpoly K pb.gen) :=
    minpoly.irreducible pb.isIntegral_gen
  let e := completionExtensionFactor_extensionEquivFactors vK hvK hf
    (minpoly.aeval K pb.gen) pb.adjoin_gen_eq_top
  exact Fintype.ofEquiv _ e.symm
 

theorem completionTensorDecomposition_mapped_minpoly_eq_prod_extensionFactors
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    letI := completionTensorDecomposition_extensionFintype (K := K) (L := L) vK hvK
    (minpoly K (completionTensorDecomposition_powerBasis K L).gen).map
        (algebraMap K vK.Completion) =
      ∏ w : AbsoluteValueExtension vK L,
        completionExtensionFactor_extensionFactor vK
          (completionTensorDecomposition_powerBasis K L).gen w := by
  classical
  let := completionTensorDecomposition_extensionFintype (K := K) (L := L) vK hvK
  let pb := completionTensorDecomposition_powerBasis K L
  let p := (minpoly K pb.gen).map (algebraMap K vK.Completion)
  let hf : Irreducible (minpoly K pb.gen) :=
    minpoly.irreducible pb.isIntegral_gen
  let e := completionExtensionFactor_extensionEquivFactors vK hvK hf
    (minpoly.aeval K pb.gen) pb.adjoin_gen_eq_top
  have hpmonic : p.Monic :=
    (minpoly.monic pb.isIntegral_gen).map (algebraMap K vK.Completion)
  have hpsep : p.Separable :=
    Polynomial.Separable.map
      (Algebra.IsSeparable.isSeparable K (pb.gen : L))
  calc
    p = ∏ g : CompletionExtensionFactorCompletionFactors vK (minpoly K pb.gen),
        (g.1 : vK.Completion[X]) :=
      separable_monic_eq_prod_distinctNormalizedFactors p hpmonic hpsep
    _ = ∏ w : AbsoluteValueExtension vK L,
        completionExtensionFactor_extensionFactor vK pb.gen w := by
      symm
      exact Fintype.prod_equiv e _ _ (fun _ ↦ rfl)
 
theorem completionTensorDecomposition_extensionFactors_pairwise_coprime
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    letI := completionTensorDecomposition_extensionFintype (K := K) (L := L) vK hvK
    ∀ w w' : AbsoluteValueExtension vK L, w ≠ w' →
      IsCoprime
        (completionExtensionFactor_extensionFactor vK
          (completionTensorDecomposition_powerBasis K L).gen w)
        (completionExtensionFactor_extensionFactor vK
          (completionTensorDecomposition_powerBasis K L).gen w') := by
  classical
  let := completionTensorDecomposition_extensionFintype (K := K) (L := L) vK hvK
  let pb := completionTensorDecomposition_powerBasis K L
  let hf : Irreducible (minpoly K pb.gen) :=
    minpoly.irreducible pb.isIntegral_gen
  let e := completionExtensionFactor_extensionEquivFactors vK hvK hf
    (minpoly.aeval K pb.gen) pb.adjoin_gen_eq_top
  intro w w' hww'
  have he : e w ≠ e w' := fun h ↦ hww' (e.injective h)
  exact distinctNormalizedFactors_pairwise_coprime
    ((minpoly K pb.gen).map (algebraMap K vK.Completion))
    (e w) (e w') he
 

noncomputable def completionTensorDecomposition_factorEquiv
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    vK.Completion ⊗[K] L ≃ₐ[vK.Completion]
      ∀ w : AbsoluteValueExtension vK L, w.1.Completion := by
  classical
  letI := completionTensorDecomposition_extensionFintype (K := K) (L := L) vK hvK
  let pb := completionTensorDecomposition_powerBasis K L
  let hα := pb.isIntegral_gen
  let hgen := pb.adjoin_gen_eq_top
  letI hK : ∀ w : AbsoluteValueExtension vK L,
      Algebra K w.1.Completion :=
    fun w ↦ AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : ∀ w : AbsoluteValueExtension vK L, SMul K w.1.Completion :=
    fun w ↦ (hK w).toSMul
  letI : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  let ebase := baseChangeEquivAdjoinRoot (A := vK.Completion) pb
  let hprod := completionTensorDecomposition_mapped_minpoly_eq_prod_extensionFactors
    (K := K) (L := L) vK hvK
  let econgr := AdjoinRoot.algEquivOfEq vK.Completion _ _ hprod
  let ecrt := adjoinRootProdEquivPi
    (fun w : AbsoluteValueExtension vK L ↦
      completionExtensionFactor_extensionFactor vK pb.gen w)
    (completionTensorDecomposition_extensionFactors_pairwise_coprime
      (K := K) (L := L) vK hvK)
  let elocal := AlgEquiv.piCongrRight fun w ↦
    completionExtensionFactor_adjoinRootEquivCompletion
      vK hvK pb.gen hα hgen w
  exact ebase.trans (econgr.trans (ecrt.trans elocal))
 

@[simp]
theorem completionTensorDecomposition_factorEquiv_one_tmul_gen
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    completionTensorDecomposition_factorEquiv (K := K) (L := L) vK hvK
        (1 ⊗ₜ[K] (completionTensorDecomposition_powerBasis K L).gen) w =
      AbsoluteValue.toCompletionAlgHom (K := K) w.1
        (completionTensorDecomposition_powerBasis K L).gen := by
  classical
  let := completionTensorDecomposition_extensionFintype (K := K) (L := L) vK hvK
  let pb := completionTensorDecomposition_powerBasis K L
  let hK : ∀ w : AbsoluteValueExtension vK L,
      Algebra K w.1.Completion :=
    fun w ↦ AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : ∀ w : AbsoluteValueExtension vK L, SMul K w.1.Completion :=
    fun w ↦ (hK w).toSMul
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  let factors := fun w : AbsoluteValueExtension vK L ↦
    completionExtensionFactor_extensionFactor vK pb.gen w
  let hcop := completionTensorDecomposition_extensionFactors_pairwise_coprime
    (K := K) (L := L) vK hvK
  let ebase := baseChangeEquivAdjoinRoot (A := vK.Completion) pb
  let hprod := completionTensorDecomposition_mapped_minpoly_eq_prod_extensionFactors
    (K := K) (L := L) vK hvK
  let econgr := AdjoinRoot.algEquivOfEq vK.Completion _ _ hprod
  let ecrt := adjoinRootProdEquivPi factors hcop
  let elocal := AlgEquiv.piCongrRight fun w ↦
    completionExtensionFactor_adjoinRootEquivCompletion
      vK hvK pb.gen pb.isIntegral_gen pb.adjoin_gen_eq_top w
  change elocal (ecrt (econgr (ebase (1 ⊗ₜ[K] pb.gen)))) w = _
  rw [baseChangeEquivAdjoinRoot_one_tmul_gen,
    AdjoinRoot.algEquivOfEq_root]
  change
    (completionExtensionFactor_adjoinRootEquivCompletion
      vK hvK pb.gen pb.isIntegral_gen pb.adjoin_gen_eq_top w)
        (adjoinRootProdEquivPi factors hcop
          (AdjoinRoot.mk (∏ w, factors w) X) w) = _
  rw [adjoinRootProdEquivPi_mk]
  exact completionExtensionFactor_adjoinRootEquivCompletion_root
    vK hvK pb.gen pb.isIntegral_gen pb.adjoin_gen_eq_top w
 

theorem completionTensorDecomposition_factorEquiv_toAlgHom
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    (completionTensorDecomposition_factorEquiv (K := K) (L := L) vK hvK).toAlgHom =
      completionTensorMap_leftCanonicalHom vK := by
  classical
  let := completionTensorDecomposition_extensionFintype (K := K) (L := L) vK hvK
  let pb := completionTensorDecomposition_powerBasis K L
  let hK : ∀ w : AbsoluteValueExtension vK L,
      Algebra K w.1.Completion :=
    fun w ↦ AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : ∀ w : AbsoluteValueExtension vK L, SMul K w.1.Completion :=
    fun w ↦ (hK w).toSMul
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  apply (powerBasisBaseChange (A := vK.Completion) pb).algHom_ext
  funext w
  change
    completionTensorDecomposition_factorEquiv (K := K) (L := L) vK hvK
        (1 ⊗ₜ[K] (completionTensorDecomposition_powerBasis K L).gen) w =
      completionTensorMap_leftCanonicalHom (K := K) (L := L) vK
        (1 ⊗ₜ[K] (completionTensorDecomposition_powerBasis K L).gen) w
  rw [completionTensorDecomposition_factorEquiv_one_tmul_gen
      (K := K) (L := L) vK hvK w,
    completionTensorMap_leftCanonicalHom_tmul_apply]
  simp
 
theorem completionTensorDecomposition_leftCanonicalHom_bijective
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    Function.Bijective
      (completionTensorMap_leftCanonicalHom (K := K) (L := L) vK) := by
  classical
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  rw [← completionTensorDecomposition_factorEquiv_toAlgHom
    (K := K) (L := L) vK hvK]
  exact (completionTensorDecomposition_factorEquiv
    (K := K) (L := L) vK hvK).bijective
 

noncomputable def completionTensorDecomposition_left
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    vK.Completion ⊗[K] L ≃ₐ[vK.Completion]
      ∀ w : AbsoluteValueExtension vK L, w.1.Completion := by
  letI : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  exact AlgEquiv.ofBijective
    (completionTensorMap_leftCanonicalHom (K := K) (L := L) vK)
    (completionTensorDecomposition_leftCanonicalHom_bijective
      (K := K) (L := L) vK hvK)
@[simp]
theorem completionTensorDecomposition_left_tmul_apply
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (b : vK.Completion) (a : L)
    (w : AbsoluteValueExtension vK L) :
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    completionTensorDecomposition_left (K := K) (L := L) vK hvK (b ⊗ₜ[K] a) w =
      algebraMap vK.Completion w.1.Completion b *
        AbsoluteValue.toCompletionAlgHom (K := K) w.1 a := by
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  change completionTensorMap_leftCanonicalHom (K := K) (L := L) vK
    (b ⊗ₜ[K] a) w = _
  exact completionTensorMap_leftCanonicalHom_tmul_apply vK b a w
end Valuations
end AlgebraicNumberTheory
end
end

/- ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Tensor -/
section
open scoped TensorProduct
noncomputable section
namespace LocalClassFieldTheory
open AlgebraicNumberTheory.Valuations


universe u v
variable {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [IsGalois K L]
 

abbrev LocalTensorAlgebra (vK : AbsoluteValue K ℝ) :=
  vK.Completion ⊗[K] L
section RightCosetCoordinates
universe uG uB
variable {G : Type uG} {B : Type uB}
    [Group G] [CommGroup B]
    (H : Subgroup G) [MulDistribMulAction H B]
end RightCosetCoordinates
section ExtensionOrbit
variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
end ExtensionOrbit
section ProductEquivalences
variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
end ProductEquivalences
end LocalClassFieldTheory
end
end

/- ValuedFieldTheory.Ramification.HilbertRamification.LocalizationDensity -/
section
noncomputable section
universe u v
namespace HilbertRamification

open AlgebraicNumberTheory.Valuations
variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
section AbsoluteValuePrincipalUnits
variable {F : Type*} [Field F]
end AbsoluteValuePrincipalUnits
namespace ValuationSubring
end ValuationSubring
section Localization
variable (vK : AbsoluteValue K ℝ)
variable (w : AbsoluteValueExtension vK L)
local instance completionAlgebra : Algebra vK.Completion w.1.Completion :=
  AbsoluteValue.completionAlgebra vK w.1 w.2
end Localization
end HilbertRamification
end
end

/- ValuedFieldTheory.Valuation.Completion.FiniteProductNormTrace -/
section
noncomputable section
namespace ValuationTheory
namespace Completion
universe u v w
open Module
 

theorem moduleFiniteOfPi
    {R : Type u} [Semiring R]
    {ι : Type v} (M : ι → Type w)
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [Module.Finite R (∀ i, M i)] (i : ι) :
    Module.Finite R (M i) := by
  classical
  apply Module.Finite.of_surjective (LinearMap.proj i)
  intro x
  exact ⟨Pi.single i x, by simp⟩
 
noncomputable def piCongrLeftAlgEquiv
    {R : Type*} [CommSemiring R]
    {ι ι' : Type*} (A : ι' → Type*) [∀ i, Semiring (A i)]
    [∀ i, Algebra R (A i)] (e : ι ≃ ι') :
    ((i : ι) → A (e i)) ≃ₐ[R] ((i' : ι') → A i') where
  __ := RingEquiv.piCongrLeft A e
  commutes' r := by
    funext j
    obtain ⟨i, rfl⟩ := e.surjective j
    change (Equiv.piCongrLeft A e
      (fun i => algebraMap R (A (e i)) r)) (e i) =
        algebraMap R (A (e i)) r
    exact Equiv.piCongrLeft_apply_apply A e _ i
 

noncomputable def piOptionEquivProdAlgEquiv
    {R : Type*} [CommSemiring R]
    {ι : Type*} (A : Option ι → Type*) [∀ i, Semiring (A i)]
    [∀ i, Algebra R (A i)] :
    ((i : Option ι) → A i) ≃ₐ[R] (A none × ((i : ι) → A (some i))) where
  __ := RingEquiv.piOptionEquivProd
  commutes' _ := rfl
 

theorem algebra_trace_pi_apply
    {R : Type u} [CommRing R]
    {ι : Type v} [Fintype ι]
    (A : ι → Type w) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]
    (x : ∀ i, A i) :
    Algebra.trace R (∀ i, A i) x = ∑ i, Algebra.trace R (A i) (x i) := by
  classical
  let P : ∀ (ι : Type v) [Fintype ι], Prop :=
    fun ι _ =>
      ∀ (A : ι → Type w) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
        [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]
        (x : ∀ i, A i),
        Algebra.trace R (∀ i, A i) x =
          ∑ i, Algebra.trace R (A i) (x i)
  apply Fintype.induction_empty_option (P := P)
  · intro α β _ e h A _ _ _ _ x
    let : Fintype α := Fintype.ofEquiv β e.symm
    let E := piCongrLeftAlgEquiv (R := R) A e
    let x' : ∀ i : α, A (e i) := fun i => x (e i)
    have hEx : E x' = x := by
      apply E.symm.injective
      rw [E.symm_apply_apply]
      funext i
      rfl
    calc
      Algebra.trace R (∀ j : β, A j) x =
          Algebra.trace R (∀ i : α, A (e i)) x' := by
        rw [← Algebra.trace_eq_of_algEquiv E x']
        rw [hEx]
      _ = ∑ i : α, Algebra.trace R (A (e i)) (x' i) := h _ _
      _ = ∑ j : β, Algebra.trace R (A j) (x j) := by
        exact Fintype.sum_equiv e _ _ (fun i => rfl)
  · intro A _ _ _ _ x
    simp only [Fintype.sum_empty]
    rw [Algebra.trace_apply]
    let b : Basis (Fin 0) R ((i : PEmpty) → A i) := Basis.empty _
    rw [LinearMap.trace_eq_matrix_trace R b]
    simp [Matrix.trace]
  · intro α _ h A _ _ _ _ x
    let E := piOptionEquivProdAlgEquiv (R := R) A
    let y : A none × ((i : α) → A (some i)) := E x
    calc
      Algebra.trace R (∀ i : Option α, A i) x =
          Algebra.trace R (A none × ((i : α) → A (some i))) y :=
        (Algebra.trace_eq_of_algEquiv E x).symm
      _ = Algebra.trace R (A none) y.1 +
          Algebra.trace R ((i : α) → A (some i)) y.2 :=
        Algebra.trace_prod_apply y
      _ = Algebra.trace R (A none) (x none) +
          ∑ i : α, Algebra.trace R (A (some i)) (x (some i)) := by
        rw [h]
        rfl
      _ = ∑ i : Option α, Algebra.trace R (A i) (x i) := by
        rw [Fintype.sum_option]
end Completion
end ValuationTheory
end
end

/- ValuedFieldTheory.Valuation.Completion.DegreeNormTrace -/
section
noncomputable section
open scoped BigOperators TensorProduct
open ValuationTheory.Completion
namespace AlgebraicNumberTheory
namespace Valuations
universe u v
 

theorem completionModuleFinite
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    Module.Finite vK.Completion w.1.Completion := by
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  let : Module.Finite vK.Completion (vK.Completion ⊗[K] L) :=
    inferInstance
  let : Module.Finite vK.Completion
      (∀ w : AbsoluteValueExtension vK L, w.1.Completion) :=
    Module.Finite.equiv (completionTensorDecomposition_left vK hvK).toLinearEquiv
  exact moduleFiniteOfPi
    (fun w : AbsoluteValueExtension vK L ↦ w.1.Completion) w
end Valuations
end AlgebraicNumberTheory
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Tower -/
section
open scoped NumberField TensorProduct
open NumberField
noncomputable section
universe u
variable
    (K M L : Type u)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]
 

noncomputable instance (priority := 100)
    relativeAdeleRingTopIntermediateAlgebra :
    Algebra M (RelativeAdeleRing K L) :=
  ((Algebra.TensorProduct.includeRight
      (R := K)
      (A := NumberField.AdeleRing (𝓞 K) K)
      (B := L)).toRingHom.comp
        (algebraMap M L)).toAlgebra
namespace TowerRelativeIdeleGroup
end TowerRelativeIdeleGroup
section NormQuotientSequence
end NormQuotientSequence
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal -/
section
open scoped NumberField WithZero Classical
open NumberField IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace RayClass
theorem adicAbv_isNontrivial
    (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K v).IsNontrivial := by
  obtain ⟨x, hxv, hx0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  refine ⟨algebraMap (𝓞 K) K x, ?_, ?_⟩
  · exact (FaithfulSMul.algebraMap_eq_zero_iff (𝓞 K) K).not.mpr hx0
  · apply ne_of_lt
    rw [← FinitePlace.norm_embedding]
    exact (FinitePlace.norm_lt_one_iff_mem (K := K) v x).2 hxv
end RayClass
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.AbsoluteValue -/
section
open scoped NumberField TensorProduct NNReal
open NumberField IsDedekindDomain
noncomputable section
open AlgebraicNumberTheory.Valuations
universe u v
variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
 

noncomputable def realAbsoluteValueValuation
    {F : Type*} [Field F]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ)) :
    Valuation F NNReal where
  toFun x := ⟨vF x, vF.nonneg x⟩
  map_one' := by
    ext
    exact vF.map_one
  map_zero' := by
    ext
    exact vF.map_zero
  map_mul' x y := by
    ext
    exact vF.map_mul x y
  map_add_le_max' x y := by
    change vF (x + y) ≤ max (vF x) (vF y)
    exact hvF x y
 


theorem absoluteValueExtension_isNonarchimedean
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ))
    (w : AbsoluteValueExtension vF E) :
    IsNonarchimedean (w.1 : E → ℝ) := by
  rw [AbsoluteValue.isNonarchimedean_iff_bounded_nat]
  refine ⟨1, ?_⟩
  intro n
  calc
    w.1 (n : E) =
        w.1 (algebraMap F E (n : F)) := by simp
    _ = vF (n : F) := w.2 (n : F)
    _ ≤ 1 := hvF.apply_natCast_le_one
 

theorem absoluteValue_le_one_of_isIntegral
    {F : Type*} [Field F]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ))
    {x : F} (hx : IsIntegral ℤ x) :
    vF x ≤ 1 := by
  let ν : Valuation F NNReal :=
    realAbsoluteValueValuation vF hvF
  let V : ValuationSubring F := ν.valuationSubring
  let : IsIntegrallyClosedIn V F :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn F).1
      inferInstance
  let : IsScalarTower ℤ V F :=
    IsScalarTower.of_algebraMap_eq fun n => by
      simp
  have hxV : IsIntegral V x :=
    hx.tower_top
  obtain ⟨y, hy⟩ :=
    (IsIntegrallyClosedIn.isIntegral_iff).1 hxV
  have hν : x ∈ V := by
    rw [← hy, ValuationSubring.algebraMap_apply]
    exact y.property
  change
    realAbsoluteValueValuation vF hvF x ≤ 1 at hν
  exact_mod_cast hν
 

noncomputable def absoluteValueCompletionIntegers
    {F : Type*} [Field F]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ)) :
    ValuationSubring vF.Completion :=
  (realAbsoluteValueValuation
    (AbsoluteValue.completionAbsoluteValue vF)
    (AbsoluteValue.completionAbsoluteValue_isNonarchimedean
      vF hvF)).valuationSubring
 
@[simp]
theorem mem_absoluteValueCompletionIntegers_iff
    {F : Type*} [Field F]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ))
    (x : vF.Completion) :
    x ∈ absoluteValueCompletionIntegers vF hvF ↔
      ‖x‖ ≤ 1 :=
  Iff.rfl
omit [NumberField K] [NumberField L] in
 




theorem isIntegral_over_baseCompletionIntegers_of_mem
    [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ)
    (hvK : IsNonarchimedean (vK : K → ℝ))
    (hvK0 : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    {x : w.1.Completion}
    (hx : x ∈ absoluteValueCompletionIntegers w.1
      (absoluteValueExtension_isNonarchimedean vK hvK w)) :
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    IsIntegral (absoluteValueCompletionIntegers vK hvK) x := by
  letI : Algebra vK.Completion w.1.Completion := AbsoluteValue.completionAlgebra vK w.1 w.2
  letI : Module.Finite vK.Completion w.1.Completion := completionModuleFinite vK hvK0 w
  letI : NontriviallyNormedField vK.Completion := absoluteValueExtension_completionNontriviallyNormedField vK hvK0
  letI : NormedAlgebra vK.Completion w.1.Completion := absoluteValueExtension_completionNormedAlgebra vK w
  letI : IsUltrametricDist vK.Completion :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (AbsoluteValue.completionAbsoluteValue_isNonarchimedean vK hvK)
  exact TunnellSpectral.integral (absoluteValueCompletionIntegers vK hvK)
    (fun _ => Iff.rfl) x hx
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.Lattice -/
section
open scoped NumberField TensorProduct NNReal
open NumberField IsDedekindDomain
noncomputable section
open AlgebraicNumberTheory.Valuations
universe u v
variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
 

theorem exists_integral_relativeBasis_scale :
    ∃ d : ℤ, d ≠ 0 ∧
      ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
        IsIntegral ℤ
          (d • relativeExtensionBasis
            (K := K) (L := L) i) := by
  classical
  let : Algebra.IsAlgebraic ℤ L :=
    (IsFractionRing.isAlgebraic_iff' ℤ (𝓞 L) L).mp
      inferInstance
  let s : Finset L :=
    Finset.univ.image fun i :
      RelativeAdeleBasisIndex (K := K) (L := L) =>
        relativeExtensionBasis (K := K) (L := L) i
  obtain ⟨d, hd, hint⟩ :=
    Algebra.IsAlgebraic.exists_integral_multiples ℤ s
  refine ⟨d, hd, ?_⟩
  intro i
  exact
    hint
      (relativeExtensionBasis (K := K) (L := L) i)
      (Finset.mem_image.mpr
        ⟨i, Finset.mem_univ i, rfl⟩)
 
noncomputable def chosenRelativeBasisIntegralScale : ℤ :=
  Classical.choose
    (exists_integral_relativeBasis_scale
      (K := K) (L := L))
 
theorem chosenRelativeBasisIntegralScale_ne_zero :
    chosenRelativeBasisIntegralScale (K := K) (L := L) ≠ 0 :=
  (Classical.choose_spec
    (exists_integral_relativeBasis_scale
      (K := K) (L := L))).1
 
theorem chosenRelativeBasisIntegralScale_isIntegral
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    IsIntegral ℤ
      (chosenRelativeBasisIntegralScale (K := K) (L := L) •
        relativeExtensionBasis (K := K) (L := L) i) :=
  (Classical.choose_spec
    (exists_integral_relativeBasis_scale
      (K := K) (L := L))).2 i
 
noncomputable def relativeBasisIntegralScaleInK : K :=
  algebraMap ℤ K
    (chosenRelativeBasisIntegralScale (K := K) (L := L))
 
theorem relativeBasisIntegralScaleInK_ne_zero :
    relativeBasisIntegralScaleInK (K := K) (L := L) ≠ 0 := by
  intro h
  have hc :
      (chosenRelativeBasisIntegralScale
        (K := K) (L := L) : K) =
        ((0 : ℤ) : K) := by
    simpa [relativeBasisIntegralScaleInK] using h
  exact
    chosenRelativeBasisIntegralScale_ne_zero
      (K := K) (L := L)
      (Int.cast_injective hc)
 
noncomputable def relativeBasisIntegralScaleUnit : Kˣ :=
  Units.mk0
    (relativeBasisIntegralScaleInK (K := K) (L := L))
    (relativeBasisIntegralScaleInK_ne_zero
      (K := K) (L := L))
 

noncomputable def scaledRelativeExtensionBasis :
    Module.Basis
      (RelativeAdeleBasisIndex (K := K) (L := L)) K L :=
  (relativeExtensionBasis (K := K) (L := L)).unitsSMul
    fun _ => relativeBasisIntegralScaleUnit
      (K := K) (L := L)
 

@[simp]
theorem scaledRelativeExtensionBasis_apply
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    scaledRelativeExtensionBasis (K := K) (L := L) i =
      relativeBasisIntegralScaleInK
          (K := K) (L := L) •
        relativeExtensionBasis (K := K) (L := L) i := by
  rw [scaledRelativeExtensionBasis,
    Module.Basis.unitsSMul_apply]
  rfl
 
theorem scaledRelativeExtensionBasis_isIntegral
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    IsIntegral ℤ
      (scaledRelativeExtensionBasis
        (K := K) (L := L) i) := by
  simpa [scaledRelativeExtensionBasis_apply,
    relativeBasisIntegralScaleInK, Algebra.smul_def] using
      chosenRelativeBasisIntegralScale_isIntegral
        (K := K) (L := L) i
 

theorem scaledRelativeExtensionBasis_absoluteValue_le_one
    (vK : AbsoluteValue K ℝ)
    (hvK : IsNonarchimedean (vK : K → ℝ))
    (wL : AbsoluteValueExtension vK L)
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    wL.1
      (scaledRelativeExtensionBasis
        (K := K) (L := L) i) ≤ 1 :=
  absoluteValue_le_one_of_isIntegral
    wL.1
    (absoluteValueExtension_isNonarchimedean
      vK hvK wL)
    (scaledRelativeExtensionBasis_isIntegral
      (K := K) (L := L) i)
 
noncomputable def scaledRelativeExtensionInteger
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    𝓞 L :=
  ⟨scaledRelativeExtensionBasis (K := K) (L := L) i,
    scaledRelativeExtensionBasis_isIntegral
      (K := K) (L := L) i⟩
 
noncomputable def scaledRelativeIntegerLattice :
    Submodule (𝓞 K) (𝓞 L) :=
  Submodule.span (𝓞 K)
    (Set.range
      (scaledRelativeExtensionInteger
        (K := K) (L := L)))
 
noncomputable def scaledRelativeFieldLattice :
    Submodule (𝓞 K) L :=
  Submodule.span (𝓞 K)
    (Set.range
      (scaledRelativeExtensionBasis
        (K := K) (L := L)))
 
noncomputable def ringOfIntegersToFieldLinearMap :
    𝓞 L →ₗ[𝓞 K] L :=
  (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) L).toLinearMap
 

theorem scaledRelativeIntegerLattice_map_toField :
    (scaledRelativeIntegerLattice
      (K := K) (L := L)).map
        (ringOfIntegersToFieldLinearMap
          (K := K) (L := L)) =
      scaledRelativeFieldLattice
        (K := K) (L := L) := by
  rw [scaledRelativeIntegerLattice,
    scaledRelativeFieldLattice,
    Submodule.map_span]
  congr 1
  exact
    (Set.range_comp
      (ringOfIntegersToFieldLinearMap (K := K) (L := L))
      (scaledRelativeExtensionInteger (K := K) (L := L))).symm
omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
 
theorem ringOfIntegersToFieldLinearMap_injective :
    Function.Injective
      (ringOfIntegersToFieldLinearMap
        (K := K) (L := L)) := by
  intro x y h
  exact NumberField.RingOfIntegers.ext h
 



theorem exists_nonZeroDivisor_smul_mem_scaledRelativeIntegerLattice
    (x : 𝓞 L) :
    ∃ d : nonZeroDivisors (𝓞 K),
      (d : 𝓞 K) • x ∈
        scaledRelativeIntegerLattice
          (K := K) (L := L) := by
  let s : Set L :=
    Set.range
      (scaledRelativeExtensionBasis
        (K := K) (L := L))
  have hx :
      (x : L) ∈ Submodule.span K s := by
    change
      (x : L) ∈
        Submodule.span K
          (Set.range
            (scaledRelativeExtensionBasis
              (K := K) (L := L)))
    rw [(scaledRelativeExtensionBasis
      (K := K) (L := L)).span_eq]
    exact Submodule.mem_top
  obtain ⟨d, hd⟩ :=
    multiple_mem_span_of_mem_localization_span
      (nonZeroDivisors (𝓞 K)) K s (x : L) hx
  refine ⟨d, ?_⟩
  have hdmap :
      d • (x : L) ∈
        (scaledRelativeIntegerLattice
          (K := K) (L := L)).map
            (ringOfIntegersToFieldLinearMap
              (K := K) (L := L)) := by
    rw [scaledRelativeIntegerLattice_map_toField
      (K := K) (L := L)]
    exact hd
  obtain ⟨y, hy, hyx⟩ := hdmap
  have hyx' : y = (d : 𝓞 K) • x := by
    apply ringOfIntegersToFieldLinearMap_injective
      (K := K) (L := L)
    simpa [ringOfIntegersToFieldLinearMap,
      Submonoid.smul_def] using hyx
  rw [← hyx']
  exact hy
 

abbrev ScaledRelativeIntegerLatticeQuotient :=
  (𝓞 L) ⧸
    scaledRelativeIntegerLattice
      (K := K) (L := L)
 
noncomputable instance
    scaledRelativeIntegerLatticeQuotientFinite :
    Module.Finite (𝓞 K)
      (ScaledRelativeIntegerLatticeQuotient
        (K := K) (L := L)) :=
  Module.Finite.quotient (𝓞 K)
    (scaledRelativeIntegerLattice
      (K := K) (L := L))
 
theorem scaledRelativeIntegerLatticeQuotient_isTorsion :
    Module.IsTorsion (𝓞 K)
      (ScaledRelativeIntegerLatticeQuotient
        (K := K) (L := L)) := by
  intro q
  refine
    Submodule.Quotient.induction_on
      (p := scaledRelativeIntegerLattice
        (K := K) (L := L)) q ?_
  intro x
  obtain ⟨d, hd⟩ :=
    exists_nonZeroDivisor_smul_mem_scaledRelativeIntegerLattice
      (K := K) (L := L) x
  refine ⟨d, ?_⟩
  rw [Submonoid.smul_def,
    ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero]
  exact hd
 

noncomputable def chosenScaledRelativeIntegerLatticeAnnihilatorData :
    { r : 𝓞 K //
      r ∈
          (⊤ : Submodule (𝓞 K)
            (ScaledRelativeIntegerLatticeQuotient
              (K := K) (L := L))).annihilator ∧
        r ∈ nonZeroDivisors (𝓞 K) } := by
  let h :=
    Submodule.annihilator_top_inter_nonZeroDivisors
      (scaledRelativeIntegerLatticeQuotient_isTorsion
        (K := K) (L := L))
  exact
    ⟨Classical.choose h,
      (Classical.choose_spec h).1,
      (Classical.choose_spec h).2⟩
 
noncomputable def scaledRelativeIntegerLatticeAnnihilator :
    𝓞 K :=
  (chosenScaledRelativeIntegerLatticeAnnihilatorData
    (K := K) (L := L) : 𝓞 K)
 
theorem scaledRelativeIntegerLatticeAnnihilator_ne_zero :
    scaledRelativeIntegerLatticeAnnihilator
      (K := K) (L := L) ≠ 0 :=
  nonZeroDivisors.ne_zero
    (chosenScaledRelativeIntegerLatticeAnnihilatorData
      (K := K) (L := L)).2.2
 
noncomputable def relativeBasisIntegralScaleInRingOfIntegers :
    𝓞 K :=
  algebraMap ℤ (𝓞 K)
    (chosenRelativeBasisIntegralScale (K := K) (L := L))
 
theorem relativeBasisIntegralScaleInRingOfIntegers_ne_zero :
    relativeBasisIntegralScaleInRingOfIntegers
      (K := K) (L := L) ≠ 0 := by
  intro h
  have hc :
      (chosenRelativeBasisIntegralScale
        (K := K) (L := L) : 𝓞 K) =
        ((0 : ℤ) : 𝓞 K) := by
    simpa [relativeBasisIntegralScaleInRingOfIntegers] using h
  exact
    chosenRelativeBasisIntegralScale_ne_zero
      (K := K) (L := L)
      (Int.cast_injective hc)
 

noncomputable def integralTensorControlElement :
    𝓞 K :=
  relativeBasisIntegralScaleInRingOfIntegers
      (K := K) (L := L) *
    scaledRelativeIntegerLatticeAnnihilator
      (K := K) (L := L)
 
theorem integralTensorControlElement_ne_zero :
    integralTensorControlElement
      (K := K) (L := L) ≠ 0 :=
  mul_ne_zero
    (relativeBasisIntegralScaleInRingOfIntegers_ne_zero
      (K := K) (L := L))
    (scaledRelativeIntegerLatticeAnnihilator_ne_zero
      (K := K) (L := L))
 
noncomputable def integralTensorControlIdeal :
    Ideal (𝓞 K) :=
  Ideal.span
    ({integralTensorControlElement
      (K := K) (L := L)} : Set (𝓞 K))
 
theorem integralTensorControlIdeal_ne_bot :
    integralTensorControlIdeal
      (K := K) (L := L) ≠ ⊥ := by
  rw [integralTensorControlIdeal,
    ne_eq, Ideal.span_singleton_eq_bot]
  exact integralTensorControlElement_ne_zero
    (K := K) (L := L)
 

noncomputable def integralTensorBadPlaces :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (Ideal.finite_factors
    (integralTensorControlIdeal_ne_bot
      (K := K) (L := L))).toFinset
 

@[simp]
theorem mem_integralTensorBadPlaces_iff
    (w : HeightOneSpectrum (𝓞 K)) :
    w ∈ integralTensorBadPlaces
        (K := K) (L := L) ↔
      w.asIdeal ∣
        integralTensorControlIdeal
          (K := K) (L := L) :=
  Set.Finite.mem_toFinset
    (Ideal.finite_factors
      (integralTensorControlIdeal_ne_bot
        (K := K) (L := L)))
 

theorem integralTensorControlElement_not_mem_of_notMem
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ integralTensorBadPlaces
      (K := K) (L := L)) :
    integralTensorControlElement
        (K := K) (L := L) ∉ w.asIdeal := by
  intro hmem
  apply hw
  rw [mem_integralTensorBadPlaces_iff,
    integralTensorControlIdeal,
    Ideal.dvd_span_singleton]
  exact hmem
 

theorem relativeBasisIntegralScale_not_mem_of_notMem
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ integralTensorBadPlaces
      (K := K) (L := L)) :
    relativeBasisIntegralScaleInRingOfIntegers
        (K := K) (L := L) ∉ w.asIdeal := by
  intro hmem
  exact
    integralTensorControlElement_not_mem_of_notMem
      (K := K) (L := L) w hw
      (w.asIdeal.mul_mem_right
        (scaledRelativeIntegerLatticeAnnihilator
          (K := K) (L := L)) hmem)
 


theorem relativeExtensionBasis_absoluteValue_le_one_of_notMem
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ integralTensorBadPlaces
      (K := K) (L := L))
    (wL : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K w) L)
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    wL.1
      (relativeExtensionBasis
        (K := K) (L := L) i) ≤ 1 := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K w
  have hdnot :
      relativeBasisIntegralScaleInRingOfIntegers
          (K := K) (L := L) ∉ w.asIdeal :=
    relativeBasisIntegralScale_not_mem_of_notMem
      (K := K) (L := L) w hw
  have hnorm :
      ‖FinitePlace.embedding w
        (algebraMap (𝓞 K) K
          (relativeBasisIntegralScaleInRingOfIntegers
            (K := K) (L := L)))‖ = 1 :=
    (FinitePlace.norm_eq_one_iff_notMem
      (R := 𝓞 K) K w
      (relativeBasisIntegralScaleInRingOfIntegers
        (K := K) (L := L))).2 hdnot
  have hvscaleInteger :
      vK
        (algebraMap (𝓞 K) K
          (relativeBasisIntegralScaleInRingOfIntegers
            (K := K) (L := L))) = 1 := by
    simpa [vK, FinitePlace.norm_embedding] using hnorm
  have hscaleField :
      relativeBasisIntegralScaleInK
          (K := K) (L := L) =
        algebraMap (𝓞 K) K
          (relativeBasisIntegralScaleInRingOfIntegers
            (K := K) (L := L)) := by
    simp [relativeBasisIntegralScaleInK,
      relativeBasisIntegralScaleInRingOfIntegers]
  have hvscale :
      vK
        (relativeBasisIntegralScaleInK
          (K := K) (L := L)) = 1 := by
    rw [hscaleField]
    exact hvscaleInteger
  have hwscale :
      wL.1
        (algebraMap K L
          (relativeBasisIntegralScaleInK
            (K := K) (L := L))) = 1 := by
    rw [wL.2]
    exact hvscale
  have hscaled :=
    scaledRelativeExtensionBasis_absoluteValue_le_one
      (K := K) (L := L) vK
      (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv
        K w) wL i
  rw [scaledRelativeExtensionBasis_apply,
    Algebra.smul_def, map_mul, hwscale, one_mul] at hscaled
  exact hscaled
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.FinitePlaceCompletion -/
section
open scoped NumberField TensorProduct NNReal
open NumberField IsDedekindDomain
noncomputable section
open AlgebraicNumberTheory.Valuations
universe u v
variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
 


noncomputable def relativeFinitePlaceCompletionBaseMap
    (w : HeightOneSpectrum (𝓞 K)) :
    WithAbs (NumberField.HeightOneSpectrum.adicAbv K w) →+*
      w.adicCompletion K :=
  (FinitePlace.embedding w).comp
    (WithAbs.equiv
      (NumberField.HeightOneSpectrum.adicAbv K w)).toRingHom
 

@[simp]
theorem relativeFinitePlaceCompletionBaseMap_apply
    (w : HeightOneSpectrum (𝓞 K))
    (x : WithAbs
      (NumberField.HeightOneSpectrum.adicAbv K w)) :
    relativeFinitePlaceCompletionBaseMap w x =
      FinitePlace.embedding w
        (WithAbs.equiv
          (NumberField.HeightOneSpectrum.adicAbv K w) x) :=
  rfl
 
theorem relativeFinitePlaceCompletionBaseMap_norm
    (w : HeightOneSpectrum (𝓞 K))
    (x : WithAbs
      (NumberField.HeightOneSpectrum.adicAbv K w)) :
    ‖relativeFinitePlaceCompletionBaseMap w x‖ = ‖x‖ := by
  rw [relativeFinitePlaceCompletionBaseMap_apply,
    FinitePlace.norm_embedding]
  rfl
 
theorem relativeFinitePlaceCompletionBaseMap_isometry
    (w : HeightOneSpectrum (𝓞 K)) :
    Isometry (relativeFinitePlaceCompletionBaseMap w) :=
  AddMonoidHomClass.isometry_of_norm _
    (relativeFinitePlaceCompletionBaseMap_norm w)
 
noncomputable def relativeFinitePlaceCompletionRingHom
    (w : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K w).Completion →+*
      w.adicCompletion K :=
  (relativeFinitePlaceCompletionBaseMap_isometry w).extensionHom
 

@[simp]
theorem relativeFinitePlaceCompletionRingHom_coe
    (w : HeightOneSpectrum (𝓞 K))
    (x : WithAbs
      (NumberField.HeightOneSpectrum.adicAbv K w)) :
    relativeFinitePlaceCompletionRingHom w
        (x :
          (NumberField.HeightOneSpectrum.adicAbv K w).Completion) =
      relativeFinitePlaceCompletionBaseMap w x :=
  (relativeFinitePlaceCompletionBaseMap_isometry w).extensionHom_coe x
 
theorem relativeFinitePlaceCompletionRingHom_isometry
    (w : HeightOneSpectrum (𝓞 K)) :
    Isometry (relativeFinitePlaceCompletionRingHom w) :=
  (relativeFinitePlaceCompletionBaseMap_isometry w).completion_extension
 
theorem relativeFinitePlaceCompletionRingHom_surjective
    (w : HeightOneSpectrum (𝓞 K)) :
    Function.Surjective
      (relativeFinitePlaceCompletionRingHom w) := by
  let f := relativeFinitePlaceCompletionRingHom w
  have hrangeClosed : IsClosed (Set.range f) :=
    (relativeFinitePlaceCompletionRingHom_isometry w).isClosedEmbedding.isClosed_range
  have hdense :
      DenseRange (algebraMap K (w.adicCompletion K)) :=
    w.denseRange_algebraMap K
  have hrange :
      Set.range (algebraMap K (w.adicCompletion K)) ⊆
        Set.range f := by
    rintro _ ⟨x, rfl⟩
    let x' : WithAbs
        (NumberField.HeightOneSpectrum.adicAbv K w) :=
      (WithAbs.equiv
        (NumberField.HeightOneSpectrum.adicAbv K w)).symm x
    refine
      ⟨(x' :
          (NumberField.HeightOneSpectrum.adicAbv K w).Completion),
        ?_⟩
    rw [relativeFinitePlaceCompletionRingHom_coe]
    rfl
  intro x
  have hx :
      x ∈ closure
        (Set.range (algebraMap K (w.adicCompletion K))) := by
    rw [hdense.closure_range]
    trivial
  exact closure_minimal hrange hrangeClosed hx
 
noncomputable def relativeFinitePlaceCompletionRingEquiv
    (w : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K w).Completion ≃+*
      w.adicCompletion K :=
  RingEquiv.ofBijective
    (relativeFinitePlaceCompletionRingHom w)
    ⟨(relativeFinitePlaceCompletionRingHom_isometry w).injective,
      relativeFinitePlaceCompletionRingHom_surjective w⟩
 
noncomputable def relativeFinitePlaceCompletionAlgEquiv
    (w : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K w).Completion ≃ₐ[K]
      w.adicCompletion K where
  __ := relativeFinitePlaceCompletionRingEquiv w
  commutes' x := by
    change
      relativeFinitePlaceCompletionRingHom w
          (((WithAbs.equiv
            (NumberField.HeightOneSpectrum.adicAbv K w)).symm x :
              WithAbs
                (NumberField.HeightOneSpectrum.adicAbv K w)) :
            (NumberField.HeightOneSpectrum.adicAbv K w).Completion) =
        algebraMap K (w.adicCompletion K) x
    rw [relativeFinitePlaceCompletionRingHom_coe]
    rfl
 

noncomputable def relativeFinitePlaceLocalTensorAlgEquiv
    (w : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K w).Completion ⊗[K] L
        ≃ₐ[K]
      w.adicCompletion K ⊗[K] L :=
  Algebra.TensorProduct.congr
    (relativeFinitePlaceCompletionAlgEquiv w)
    (AlgEquiv.refl : L ≃ₐ[K] L)
 

theorem norm_le_one_of_mem_adicCompletionIntegers
    (w : HeightOneSpectrum (𝓞 K))
    {x : w.adicCompletion K}
    (hx : x ∈ w.adicCompletionIntegers K) :
    ‖x‖ ≤ 1 := by
  rw [FinitePlace.norm_def]
  exact_mod_cast
    (WithZeroMulInt.toNNReal_le_one_iff
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal w)).2 hx
 

theorem mem_adicCompletionIntegers_of_norm_le_one
    (w : HeightOneSpectrum (𝓞 K))
    {x : w.adicCompletion K}
    (hx : ‖x‖ ≤ 1) :
    x ∈ w.adicCompletionIntegers K := by
  rw [FinitePlace.norm_def] at hx
  exact_mod_cast
    (WithZeroMulInt.toNNReal_le_one_iff
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal w)).1 hx
 

theorem relativeFinitePlaceCompletionAlgEquiv_symm_norm
    (w : HeightOneSpectrum (𝓞 K))
    (x : w.adicCompletion K) :
    ‖(relativeFinitePlaceCompletionAlgEquiv w).symm x‖ =
      ‖x‖ := by
  let y :=
    (relativeFinitePlaceCompletionAlgEquiv w).symm x
  have h :=
    (relativeFinitePlaceCompletionRingHom_isometry w).norm_map_of_map_zero
      (map_zero
        (relativeFinitePlaceCompletionRingHom w)) y
  have hy :
      relativeFinitePlaceCompletionRingHom w y = x := by
    change
      relativeFinitePlaceCompletionAlgEquiv w y = x
    exact
      (relativeFinitePlaceCompletionAlgEquiv w).apply_symm_apply x
  rw [hy] at h
  exact h.symm
 


theorem basis_coord_isIntegral_of_integral_traces
    {R A B ι : Type*}
    [CommRing R] [Field A] [CommRing B]
    [Algebra R A] [Algebra A B]
    [Fintype ι] [DecidableEq ι]
    [Module.Free A B] [Module.Finite A B]
    (b : Module.Basis ι A B)
    {x : B}
    (hM : ∀ j k, IsIntegral R
      (Algebra.trace A B (b j * b k)))
    (ht : ∀ j, IsIntegral R
      (Algebra.trace A B (x * b j)))
    (hdiscInv : IsIntegral R (Algebra.discr A b)⁻¹)
    (hdiscne : Algebra.discr A b ≠ 0)
    (i : ι) :
    IsIntegral R (b.equivFun x i) := by
  let M : Matrix ι ι A := Algebra.traceMatrix A b
  let c : ι → A := b.equivFun x
  let t : ι → A := fun j => Algebra.trace A B (x * b j)
  have hM' : ∀ j k, IsIntegral R (M j k) := by
    intro j k
    exact hM j k
  have ht' : ∀ j, IsIntegral R (t j) := by
    intro j
    exact ht j
  have hcramer : IsIntegral R (M.cramer t i) := by
    rw [Matrix.cramer_apply]
    apply IsIntegral.det
    intro j k
    by_cases hki : k = i
    · simpa [Matrix.updateCol_apply, hki] using ht' j
    · simpa [Matrix.updateCol_apply, hki] using hM' j k
  have hmul : M.mulVec c = t :=
    Algebra.traceMatrix_of_basis_mulVec b x
  have hcramerEq : M.det • c = M.cramer t := by
    rw [Matrix.cramer_eq_adjugate_mulVec, ← hmul,
      Matrix.mulVec_mulVec, Matrix.adjugate_mul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hcoord :
      Algebra.discr A b * c i = M.cramer t i := by
    have hi := congrFun hcramerEq i
    simpa [M, Algebra.discr_def, Pi.smul_apply] using hi
  have hcEq :
      c i = (Algebra.discr A b)⁻¹ * M.cramer t i := by
    rw [← hcoord, ← mul_assoc, inv_mul_cancel₀ hdiscne, one_mul]
  change IsIntegral R (c i)
  rw [hcEq]
  exact hdiscInv.mul hcramer
omit [NumberField L] in
 

theorem trace_tensorProduct_basis_mul
    {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K L)
    (A : Type*) [Field A] [Algebra K A]
    (i j : ι) :
    Algebra.trace A (A ⊗[K] L)
        ((Algebra.TensorProduct.basis A b i) *
          (Algebra.TensorProduct.basis A b j)) =
      algebraMap K A (Algebra.trace K L (b i * b j)) := by
  simp only [Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  change LinearMap.trace A (A ⊗[K] L)
      (Algebra.lmul A (A ⊗[K] L) (1 ⊗ₜ[K] (b i * b j))) =
    _
  rw [← Algebra.baseChange_lmul]
  exact LinearMap.trace_baseChange (Algebra.lmul K L (b i * b j)) A
omit [NumberField L] in
 

theorem discr_tensorProduct_basis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L)
    (A : Type*) [Field A] [Algebra K A] :
    Algebra.discr A (Algebra.TensorProduct.basis A b) =
      algebraMap K A (Algebra.discr K b) := by
  rw [Algebra.discr_def, Algebra.discr_def]
  rw [(algebraMap K A).map_det]
  congr 1
  ext i j
  exact trace_tensorProduct_basis_mul b A i j
omit [NumberField K] [NumberField L] in
 

theorem isIntegral_trace_tensor_of_components
    [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ)
    (hvK : IsNonarchimedean (vK : K → ℝ))
    (hvK0 : vK.IsNontrivial)
    (x : vK.Completion ⊗[K] L)
    (hx : ∀ w : AbsoluteValueExtension vK L,
      completionTensorDecomposition_left
          (K := K) (L := L) vK hvK0 x w ∈
        absoluteValueCompletionIntegers w.1
          (absoluteValueExtension_isNonarchimedean vK hvK w)) :
    IsIntegral (absoluteValueCompletionIntegers vK hvK)
      (Algebra.trace vK.Completion
        (vK.Completion ⊗[K] L) x) := by
  classical
  let : Fintype (AbsoluteValueExtension vK L) :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK0
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w => AbsoluteValue.completionAlgebra vK w.1 w.2
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w.1.Completion :=
    fun w => completionModuleFinite vK hvK0 w
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Free vK.Completion w.1.Completion :=
    fun w => Module.Free.of_divisionRing
      vK.Completion w.1.Completion
  let y :
      ∀ w : AbsoluteValueExtension vK L, w.1.Completion :=
    completionTensorDecomposition_left
      (K := K) (L := L) vK hvK0 x
  have hy :
      ∀ w : AbsoluteValueExtension vK L,
        IsIntegral (absoluteValueCompletionIntegers vK hvK) (y w) := by
    intro w
    exact isIntegral_over_baseCompletionIntegers_of_mem
      (K := K) (L := L) vK hvK hvK0 w (hx w)
  have hsum :
      IsIntegral (absoluteValueCompletionIntegers vK hvK)
        (∑ w : AbsoluteValueExtension vK L,
          Algebra.trace vK.Completion w.1.Completion (y w)) := by
    apply IsIntegral.sum
    intro w _
    exact Algebra.isIntegral_trace (hy w)
  rw [← ValuationTheory.Completion.algebra_trace_pi_apply
    (fun w : AbsoluteValueExtension vK L => w.1.Completion) y] at hsum
  rw [Algebra.trace_eq_of_algEquiv
    (completionTensorDecomposition_left
      (K := K) (L := L) vK hvK0) x] at hsum
  exact hsum
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.LocalTensorDecomposition -/
section
open scoped NumberField TensorProduct NNReal
open NumberField IsDedekindDomain
noncomputable section
open AlgebraicNumberTheory.Valuations
universe u v
variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
section LocalTensorDecompositionIntegralComparison
 

noncomputable def finitePlaceLocalTensorDecompositionComponent
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K w) L)
    (x : w.adicCompletion K ⊗[K] L) :
    wL.1.Completion := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K w
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial w
  letI : ∀ u : AbsoluteValueExtension vK L,
      Algebra vK.Completion u.1.Completion :=
    fun u =>
      AbsoluteValue.completionAlgebra vK u.1 u.2
  exact
    completionTensorDecomposition_left
      (K := K) (L := L) vK hvK
      ((relativeFinitePlaceLocalTensorAlgEquiv
        (K := K) (L := L) w).symm x) wL
 

def RelativeLocalTensorDecompositionIntegralAt
    (w : HeightOneSpectrum (𝓞 K))
    (x : w.adicCompletion K ⊗[K] L) : Prop :=
  ∀ wL : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K w) L,
    finitePlaceLocalTensorDecompositionComponent
        (K := K) (L := L) w wL x ∈
      absoluteValueCompletionIntegers wL.1
        (absoluteValueExtension_isNonarchimedean
          (NumberField.HeightOneSpectrum.adicAbv K w)
          (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv
            K w) wL)
 

noncomputable def scaledRelativeBasisDiscriminantInteger :
    𝓞 K :=
  ⟨Algebra.discr K
      (scaledRelativeExtensionBasis (K := K) (L := L)),
    Algebra.discr_isIntegral K fun i =>
      scaledRelativeExtensionBasis_isIntegral
        (K := K) (L := L) i⟩
 
theorem scaledRelativeBasisDiscriminantInteger_ne_zero :
    scaledRelativeBasisDiscriminantInteger
      (K := K) (L := L) ≠ 0 := by
  intro h
  apply Algebra.discr_not_zero_of_basis K
    (scaledRelativeExtensionBasis (K := K) (L := L))
  exact congrArg (fun x : 𝓞 K => (x : K)) h
 
noncomputable def scaledRelativeBasisDiscriminantIdeal :
    Ideal (𝓞 K) :=
  Ideal.span
    ({scaledRelativeBasisDiscriminantInteger
      (K := K) (L := L)} : Set (𝓞 K))
 
theorem scaledRelativeBasisDiscriminantIdeal_ne_bot :
    scaledRelativeBasisDiscriminantIdeal
      (K := K) (L := L) ≠ ⊥ := by
  rw [scaledRelativeBasisDiscriminantIdeal,
    ne_eq, Ideal.span_singleton_eq_bot]
  exact scaledRelativeBasisDiscriminantInteger_ne_zero
    (K := K) (L := L)
 

noncomputable def scaledRelativeBasisDiscriminantBadPlaces :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (Ideal.finite_factors
    (scaledRelativeBasisDiscriminantIdeal_ne_bot
      (K := K) (L := L))).toFinset
 

@[simp]
theorem mem_scaledRelativeBasisDiscriminantBadPlaces_iff
    (w : HeightOneSpectrum (𝓞 K)) :
    w ∈ scaledRelativeBasisDiscriminantBadPlaces
        (K := K) (L := L) ↔
      w.asIdeal ∣
        scaledRelativeBasisDiscriminantIdeal
          (K := K) (L := L) :=
  Set.Finite.mem_toFinset
    (Ideal.finite_factors
      (scaledRelativeBasisDiscriminantIdeal_ne_bot
        (K := K) (L := L)))
 
theorem scaledRelativeBasisDiscriminantInteger_not_mem_of_notMem
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ scaledRelativeBasisDiscriminantBadPlaces
      (K := K) (L := L)) :
    scaledRelativeBasisDiscriminantInteger
        (K := K) (L := L) ∉ w.asIdeal := by
  intro hmem
  apply hw
  rw [mem_scaledRelativeBasisDiscriminantBadPlaces_iff,
    scaledRelativeBasisDiscriminantIdeal,
    Ideal.dvd_span_singleton]
  exact hmem
 
theorem adicAbv_scaledRelativeBasisDiscriminant_eq_one_of_notMem
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ scaledRelativeBasisDiscriminantBadPlaces
      (K := K) (L := L)) :
    NumberField.HeightOneSpectrum.adicAbv K w
        (Algebra.discr K
          (scaledRelativeExtensionBasis (K := K) (L := L))) = 1 := by
  have hnorm :
      ‖FinitePlace.embedding (K := K) w
        (scaledRelativeBasisDiscriminantInteger
          (K := K) (L := L))‖ = 1 :=
    (FinitePlace.norm_eq_one_iff_notMem
      (R := 𝓞 K) K w
      (scaledRelativeBasisDiscriminantInteger
        (K := K) (L := L))).2
      (scaledRelativeBasisDiscriminantInteger_not_mem_of_notMem
        (K := K) (L := L) w hw)
  exact (FinitePlace.norm_embedding w
    (scaledRelativeBasisDiscriminantInteger (K := K) (L := L) : K)).symm.trans hnorm
 

noncomputable def integralTensorComparisonBadPlaces :
    Finset (HeightOneSpectrum (𝓞 K)) := by
  classical
  exact
    integralTensorBadPlaces (K := K) (L := L) ∪
      scaledRelativeBasisDiscriminantBadPlaces
        (K := K) (L := L)
omit [NumberField L] in
 
@[simp]
theorem finitePlaceLocalTensorDecompositionComponent_tmul
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K w) L)
    (a : w.adicCompletion K) (b : L) :
    finitePlaceLocalTensorDecompositionComponent
        (K := K) (L := L) w wL (a ⊗ₜ[K] b) =
      AbsoluteValue.completionMap
          (NumberField.HeightOneSpectrum.adicAbv K w)
          wL.1 wL.2
          ((relativeFinitePlaceCompletionAlgEquiv w).symm a) *
        AbsoluteValue.toCompletion wL.1 b := by
  simp [finitePlaceLocalTensorDecompositionComponent,
    relativeFinitePlaceLocalTensorAlgEquiv,
    completionTensorDecomposition_left_tmul_apply,
    AbsoluteValue.toCompletionAlgHom]
omit [NumberField L] [FiniteDimensional K L] in
 

theorem finitePlaceLocalTensorDecomposition_coefficient_mem_integers
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K w) L)
    (c : w.adicCompletionIntegers K) :
    AbsoluteValue.completionMap
        (NumberField.HeightOneSpectrum.adicAbv K w)
        wL.1 wL.2
        ((relativeFinitePlaceCompletionAlgEquiv w).symm
          (c : w.adicCompletion K)) ∈
      absoluteValueCompletionIntegers wL.1
        (absoluteValueExtension_isNonarchimedean
          (NumberField.HeightOneSpectrum.adicAbv K w)
          (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv
            K w) wL) := by
  rw [mem_absoluteValueCompletionIntegers_iff]
  calc
    ‖AbsoluteValue.completionMap
        (NumberField.HeightOneSpectrum.adicAbv K w)
        wL.1 wL.2
        ((relativeFinitePlaceCompletionAlgEquiv w).symm
          (c : w.adicCompletion K))‖ =
      ‖(relativeFinitePlaceCompletionAlgEquiv w).symm
          (c : w.adicCompletion K)‖ :=
        (AbsoluteValue.completionMap_isometry
          (NumberField.HeightOneSpectrum.adicAbv K w)
          wL.1 wL.2).norm_map_of_map_zero
            (map_zero
              (AbsoluteValue.completionMap
                (NumberField.HeightOneSpectrum.adicAbv K w)
                wL.1 wL.2)) _
    _ = ‖(c : w.adicCompletion K)‖ :=
      relativeFinitePlaceCompletionAlgEquiv_symm_norm
        (K := K) w (c : w.adicCompletion K)
    _ ≤ 1 :=
      norm_le_one_of_mem_adicCompletionIntegers
        (K := K) w c.property
 

theorem finitePlaceLocalTensorDecomposition_basis_mem_integers_of_notMem
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ integralTensorBadPlaces
      (K := K) (L := L))
    (wL : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K w) L)
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    AbsoluteValue.toCompletion wL.1
        (relativeExtensionBasis
          (K := K) (L := L) i) ∈
      absoluteValueCompletionIntegers wL.1
        (absoluteValueExtension_isNonarchimedean
          (NumberField.HeightOneSpectrum.adicAbv K w)
          (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv
            K w) wL) := by
  rw [mem_absoluteValueCompletionIntegers_iff]
  simpa [AbsoluteValue.toCompletion_apply,
    WithAbs.norm_eq_apply_ofAbs] using
      relativeExtensionBasis_absoluteValue_le_one_of_notMem
        (K := K) (L := L) w hw wL i
 


theorem relativeBasisIntegralAt_imp_localTensorDecompositionIntegral_of_notMem
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ integralTensorBadPlaces
      (K := K) (L := L))
    {x : w.adicCompletion K ⊗[K] L}
    (hx : RelativeBasisIntegralAt
      (K := K) (L := L) w x) :
    RelativeLocalTensorDecompositionIntegralAt
      (K := K) (L := L) w x := by
  obtain ⟨c, rfl⟩ := hx
  intro wL
  have hsum :
      finitePlaceLocalTensorDecompositionComponent
          (K := K) (L := L) w wL
          (∑ i : RelativeAdeleBasisIndex
              (K := K) (L := L),
            ((c i : w.adicCompletionIntegers K) :
                w.adicCompletion K) ⊗ₜ[K]
              relativeExtensionBasis
                (K := K) (L := L) i) =
        ∑ i : RelativeAdeleBasisIndex
            (K := K) (L := L),
          finitePlaceLocalTensorDecompositionComponent
            (K := K) (L := L) w wL
            (((c i : w.adicCompletionIntegers K) :
                w.adicCompletion K) ⊗ₜ[K]
              relativeExtensionBasis
                (K := K) (L := L) i) := by
    simp [finitePlaceLocalTensorDecompositionComponent]
  rw [hsum]
  apply Subring.sum_mem
  intro i hi
  rw [finitePlaceLocalTensorDecompositionComponent_tmul]
  apply
    (absoluteValueCompletionIntegers wL.1
      (absoluteValueExtension_isNonarchimedean
        (NumberField.HeightOneSpectrum.adicAbv K w)
        (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv
          K w) wL)).mul_mem
  · exact
      finitePlaceLocalTensorDecomposition_coefficient_mem_integers
        (K := K) (L := L) w wL (c i)
  · exact
      finitePlaceLocalTensorDecomposition_basis_mem_integers_of_notMem
        (K := K) (L := L) w hw wL i
 


theorem scaledRelativeTensorCoordinates_isIntegral_of_localTensorDecompositionIntegral
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ scaledRelativeBasisDiscriminantBadPlaces
      (K := K) (L := L))
    {x : w.adicCompletion K ⊗[K] L}
    (hx : RelativeLocalTensorDecompositionIntegralAt
      (K := K) (L := L) w x) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K w
    let xA :=
      (relativeFinitePlaceLocalTensorAlgEquiv
        (K := K) (L := L) w).symm x
    let bA :=
      Algebra.TensorProduct.basis vK.Completion
        (scaledRelativeExtensionBasis (K := K) (L := L))
    ∀ i, IsIntegral (absoluteValueCompletionIntegers vK
        (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K w))
      (bA.equivFun xA i) := by
  classical
  let vK := NumberField.HeightOneSpectrum.adicAbv K w
  let hvK : IsNonarchimedean (vK : K → ℝ) :=
    NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K w
  let hvK0 : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial w
  let : Fintype (AbsoluteValueExtension vK L) :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK0
  let : ∀ wL : AbsoluteValueExtension vK L,
      Algebra vK.Completion wL.1.Completion :=
    fun wL => AbsoluteValue.completionAlgebra vK wL.1 wL.2
  let : ∀ wL : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion wL.1.Completion :=
    fun wL => completionModuleFinite vK hvK0 wL
  let : ∀ wL : AbsoluteValueExtension vK L,
      Module.Free vK.Completion wL.1.Completion :=
    fun wL => Module.Free.of_divisionRing
      vK.Completion wL.1.Completion
  let xA : vK.Completion ⊗[K] L :=
    (relativeFinitePlaceLocalTensorAlgEquiv
      (K := K) (L := L) w).symm x
  let bA :=
    Algebra.TensorProduct.basis vK.Completion
      (scaledRelativeExtensionBasis (K := K) (L := L))
  have hxA :
      ∀ wL : AbsoluteValueExtension vK L,
        completionTensorDecomposition_left
            (K := K) (L := L) vK hvK0 xA wL ∈
          absoluteValueCompletionIntegers wL.1
            (absoluteValueExtension_isNonarchimedean vK hvK wL) := by
    intro wL
    simpa [xA, vK, hvK, hvK0,
      finitePlaceLocalTensorDecompositionComponent] using hx wL
  have hbA :
      ∀ (i : RelativeAdeleBasisIndex (K := K) (L := L))
        (wL : AbsoluteValueExtension vK L),
        completionTensorDecomposition_left
            (K := K) (L := L) vK hvK0 (bA i) wL ∈
          absoluteValueCompletionIntegers wL.1
            (absoluteValueExtension_isNonarchimedean vK hvK wL) := by
    intro i wL
    have hbAi :
        bA i =
          1 ⊗ₜ[K]
            scaledRelativeExtensionBasis (K := K) (L := L) i := by
      simp [bA, Algebra.TensorProduct.basis_apply]
    rw [hbAi]
    rw [completionTensorDecomposition_left_tmul_apply]
    simp only [map_one, one_mul]
    rw [mem_absoluteValueCompletionIntegers_iff]
    simpa [AbsoluteValue.toCompletionAlgHom,
      AbsoluteValue.toCompletion_apply,
      WithAbs.norm_eq_apply_ofAbs] using
        scaledRelativeExtensionBasis_absoluteValue_le_one
          (K := K) (L := L) vK hvK wL i
  have hM :
      ∀ i j : RelativeAdeleBasisIndex (K := K) (L := L),
        IsIntegral (absoluteValueCompletionIntegers vK hvK)
          (Algebra.trace vK.Completion
            (vK.Completion ⊗[K] L) (bA i * bA j)) := by
    intro i j
    apply isIntegral_trace_tensor_of_components
      (K := K) (L := L) vK hvK hvK0
    intro wL
    rw [map_mul, Pi.mul_apply]
    change _ ∈
      (absoluteValueCompletionIntegers wL.1
        (absoluteValueExtension_isNonarchimedean
          vK hvK wL)).toSubring
    exact
      (absoluteValueCompletionIntegers wL.1
        (absoluteValueExtension_isNonarchimedean
          vK hvK wL)).toSubring.mul_mem (hbA i wL) (hbA j wL)
  have ht :
      ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
        IsIntegral (absoluteValueCompletionIntegers vK hvK)
          (Algebra.trace vK.Completion
            (vK.Completion ⊗[K] L) (xA * bA i)) := by
    intro i
    apply isIntegral_trace_tensor_of_components
      (K := K) (L := L) vK hvK hvK0
    intro wL
    rw [map_mul, Pi.mul_apply]
    change _ ∈
      (absoluteValueCompletionIntegers wL.1
        (absoluteValueExtension_isNonarchimedean
          vK hvK wL)).toSubring
    exact
      (absoluteValueCompletionIntegers wL.1
        (absoluteValueExtension_isNonarchimedean
          vK hvK wL)).toSubring.mul_mem (hxA wL) (hbA i wL)
  have hdiscInv :
      IsIntegral (absoluteValueCompletionIntegers vK hvK)
        (Algebra.discr vK.Completion bA)⁻¹ := by
    rw [discr_tensorProduct_basis]
    apply (IsIntegrallyClosedIn.isIntegral_iff).2
    refine ⟨⟨_, ?_⟩, rfl⟩
    rw [mem_absoluteValueCompletionIntegers_iff]
    have hdabs :=
      adicAbv_scaledRelativeBasisDiscriminant_eq_one_of_notMem
        (K := K) (L := L) w hw
    have hdnorm :
        ‖algebraMap K vK.Completion
          (Algebra.discr K
            (scaledRelativeExtensionBasis (K := K) (L := L)))‖ = 1 := by
      calc
        ‖algebraMap K vK.Completion
            (Algebra.discr K
              (scaledRelativeExtensionBasis (K := K) (L := L)))‖ =
            vK (Algebra.discr K
              (scaledRelativeExtensionBasis (K := K) (L := L))) := by
              exact AbsoluteValue.completionAbsoluteValue_coe _ _
        _ = 1 := hdabs
    change AbsoluteValue.completionAbsoluteValue vK
      ((algebraMap K vK.Completion
        (Algebra.discr K
          (scaledRelativeExtensionBasis (K := K) (L := L))))⁻¹) ≤ 1
    rw [map_inv₀]
    change
      ‖algebraMap K vK.Completion
        (Algebra.discr K
          (scaledRelativeExtensionBasis (K := K) (L := L)))‖⁻¹ ≤ 1
    rw [hdnorm, inv_one]
  have hdiscne :
      Algebra.discr vK.Completion bA ≠ 0 := by
    rw [discr_tensorProduct_basis]
    exact (algebraMap K vK.Completion).injective.ne
      (Algebra.discr_not_zero_of_basis K
        (scaledRelativeExtensionBasis (K := K) (L := L)))
  change ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
    IsIntegral (absoluteValueCompletionIntegers vK hvK)
      (bA.equivFun xA i)
  intro i
  exact basis_coord_isIntegral_of_integral_traces
    bA hM ht hdiscInv hdiscne i
 


theorem relativeFinitePlaceLocalTensorAlgEquiv_scaled_basis_smul
    (w : HeightOneSpectrum (𝓞 K))
    (a :
      (NumberField.HeightOneSpectrum.adicAbv K w).Completion)
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    relativeFinitePlaceLocalTensorAlgEquiv
        (K := K) (L := L) w
        (a •
          Algebra.TensorProduct.basis
            (NumberField.HeightOneSpectrum.adicAbv K w).Completion
            (scaledRelativeExtensionBasis (K := K) (L := L)) i) =
      relativeFinitePlaceCompletionAlgEquiv w
          (a * algebraMap K
            (NumberField.HeightOneSpectrum.adicAbv K w).Completion
            (relativeBasisIntegralScaleInK
              (K := K) (L := L))) ⊗ₜ[K]
        relativeExtensionBasis (K := K) (L := L) i := by
  simp [relativeFinitePlaceLocalTensorAlgEquiv,
    Algebra.TensorProduct.basis_apply,
    scaledRelativeExtensionBasis_apply,
    Algebra.smul_def, mul_comm]
  simpa [Algebra.smul_def] using
    (TensorProduct.smul_tmul
      (relativeBasisIntegralScaleInK (K := K) (L := L))
      (relativeFinitePlaceCompletionAlgEquiv w a)
      (relativeExtensionBasis (K := K) (L := L) i)).symm
 


theorem localTensorDecompositionIntegral_imp_relativeBasisIntegralAt_of_notMem
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ integralTensorComparisonBadPlaces
      (K := K) (L := L))
    {x : w.adicCompletion K ⊗[K] L}
    (hx : RelativeLocalTensorDecompositionIntegralAt
      (K := K) (L := L) w x) :
    RelativeBasisIntegralAt (K := K) (L := L) w x := by
  classical
  have hwdisc :
      w ∉ scaledRelativeBasisDiscriminantBadPlaces
        (K := K) (L := L) := by
    intro hw'
    exact hw (by
      simp [integralTensorComparisonBadPlaces, hw'])
  let vK := NumberField.HeightOneSpectrum.adicAbv K w
  let hvK : IsNonarchimedean (vK : K → ℝ) :=
    NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K w
  let xA : vK.Completion ⊗[K] L :=
    (relativeFinitePlaceLocalTensorAlgEquiv
      (K := K) (L := L) w).symm x
  let bA :=
    Algebra.TensorProduct.basis vK.Completion
      (scaledRelativeExtensionBasis (K := K) (L := L))
  have hscaled :
      ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
        IsIntegral (absoluteValueCompletionIntegers vK hvK)
          (bA.equivFun xA i) := by
    simpa [vK, hvK, xA, bA] using
      scaledRelativeTensorCoordinates_isIntegral_of_localTensorDecompositionIntegral
        (K := K) (L := L) w hwdisc hx
  have hscaledNorm :
      ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
        ‖bA.equivFun xA i‖ ≤ 1 := by
    intro i
    obtain ⟨ci, hci⟩ :=
      (IsIntegrallyClosedIn.isIntegral_iff).1 (hscaled i)
    rw [← hci]
    exact ci.property
  have hscaleIntegral :
      IsIntegral ℤ
        (relativeBasisIntegralScaleInK
          (K := K) (L := L)) := by
    change IsIntegral ℤ
      (algebraMap ℤ K
        (chosenRelativeBasisIntegralScale (K := K) (L := L)))
    exact isIntegral_algebraMap
  have hscaleAbs :
      vK (relativeBasisIntegralScaleInK
        (K := K) (L := L)) ≤ 1 :=
    absoluteValue_le_one_of_isIntegral vK hvK hscaleIntegral
  have hscaleNorm :
      ‖algebraMap K vK.Completion
        (relativeBasisIntegralScaleInK
          (K := K) (L := L))‖ ≤ 1 := by
    calc
      ‖algebraMap K vK.Completion
          (relativeBasisIntegralScaleInK
            (K := K) (L := L))‖ =
          vK (relativeBasisIntegralScaleInK
            (K := K) (L := L)) :=
        AbsoluteValue.completionAbsoluteValue_coe _ _
      _ ≤ 1 := hscaleAbs
  let cA :
      RelativeAdeleBasisIndex (K := K) (L := L) →
        vK.Completion :=
    fun i =>
      bA.equivFun xA i *
        algebraMap K vK.Completion
          (relativeBasisIntegralScaleInK
            (K := K) (L := L))
  have hcANorm :
      ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
        ‖cA i‖ ≤ 1 := by
    intro i
    change ‖bA.equivFun xA i *
      algebraMap K vK.Completion
        (relativeBasisIntegralScaleInK
          (K := K) (L := L))‖ ≤ 1
    rw [norm_mul]
    calc
      ‖bA.equivFun xA i‖ *
          ‖algebraMap K vK.Completion
            (relativeBasisIntegralScaleInK
              (K := K) (L := L))‖ ≤
          1 * 1 :=
        mul_le_mul (hscaledNorm i) hscaleNorm
          (norm_nonneg _) (by positivity)
      _ = 1 := one_mul 1
  have hmapNorm (y : vK.Completion) :
      ‖relativeFinitePlaceCompletionAlgEquiv w y‖ = ‖y‖ := by
    change ‖relativeFinitePlaceCompletionRingHom w y‖ = ‖y‖
    exact
      (relativeFinitePlaceCompletionRingHom_isometry w).norm_map_of_map_zero
        (map_zero (relativeFinitePlaceCompletionRingHom w)) y
  let c :
      RelativeAdeleBasisIndex (K := K) (L := L) →
        w.adicCompletionIntegers K :=
    fun i =>
      ⟨relativeFinitePlaceCompletionAlgEquiv w (cA i),
        mem_adicCompletionIntegers_of_norm_le_one w
          (by rw [hmapNorm]; exact hcANorm i)⟩
  refine ⟨c, ?_⟩
  let e :=
    relativeFinitePlaceLocalTensorAlgEquiv
      (K := K) (L := L) w
  calc
    x = e xA := (e.apply_symm_apply x).symm
    _ = e (∑ i : RelativeAdeleBasisIndex (K := K) (L := L),
        (bA.equivFun xA i) • bA i) :=
      congrArg e (bA.sum_repr xA).symm
    _ = ∑ i : RelativeAdeleBasisIndex (K := K) (L := L),
        e ((bA.equivFun xA i) • bA i) := by
      rw [map_sum]
    _ = ∑ i : RelativeAdeleBasisIndex (K := K) (L := L),
        ((c i : w.adicCompletionIntegers K) :
            w.adicCompletion K) ⊗ₜ[K]
          relativeExtensionBasis (K := K) (L := L) i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [relativeFinitePlaceLocalTensorAlgEquiv_scaled_basis_smul]
 

theorem relativeBasisIntegralAt_iff_localTensorDecompositionIntegral_of_notMem
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ integralTensorComparisonBadPlaces
      (K := K) (L := L))
    {x : w.adicCompletion K ⊗[K] L} :
    RelativeBasisIntegralAt (K := K) (L := L) w x ↔
      RelativeLocalTensorDecompositionIntegralAt (K := K) (L := L) w x := by
  have hwold : w ∉ integralTensorBadPlaces (K := K) (L := L) := by
    intro hw'
    exact hw (by
      simp [integralTensorComparisonBadPlaces, hw'])
  exact
    ⟨relativeBasisIntegralAt_imp_localTensorDecompositionIntegral_of_notMem
        (K := K) (L := L) w hwold,
      localTensorDecompositionIntegral_imp_relativeBasisIntegralAt_of_notMem
        (K := K) (L := L) w hw⟩
end LocalTensorDecompositionIntegralComparison
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.Adele.LocalComponents -/
section
open scoped NumberField TensorProduct
open NumberField IsDedekindDomain
noncomputable section
universe u v
variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
omit [NumberField L] in
 

@[simp]
theorem relativeAdeleFiniteComponent_basis_repr
    (z : RelativeAdeleRing K L)
    (w : HeightOneSpectrum (𝓞 K))
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    (Algebra.TensorProduct.basis
        (w.adicCompletion K)
        (relativeExtensionBasis
          (K := K) (L := L))).repr
        (relativeAdeleFiniteComponent
          (K := K) (L := L) w z) i =
      (relativeAdeleCoefficient
        (K := K) (L := L) z i).2 w := by
  classical
  rw [relativeAdeleFiniteComponent_eq_sum_tmul_coefficients]
  simp [relativeExtensionBasis, Finsupp.single_apply]
omit [NumberField L] in
 

@[simp]
theorem relativeAdeleInfiniteComponent_basis_repr
    (z : RelativeAdeleRing K L)
    (w : InfinitePlace K)
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    (Algebra.TensorProduct.basis
        w.Completion
        (relativeExtensionBasis
          (K := K) (L := L))).repr
        (relativeAdeleInfiniteComponent
          (K := K) (L := L) w z) i =
      (relativeAdeleCoefficient
        (K := K) (L := L) z i).1 w := by
  classical
  rw [relativeAdeleInfiniteComponent_eq_sum_tmul_coefficients]
  simp [relativeExtensionBasis, Finsupp.single_apply]
  change
    (relativeAdeleCoefficient
        (K := K) (L := L) z i).1 w *
        algebraMap K w.Completion (1 : K) =
      (relativeAdeleCoefficient
        (K := K) (L := L) z i).1 w
  rw [map_one, mul_one]
omit [NumberField L] in
 

theorem relativeAdele_ext_of_components
    {x y : RelativeAdeleRing K L}
    (hinfinite :
      ∀ w : InfinitePlace K,
        relativeAdeleInfiniteComponent
            (K := K) (L := L) w x =
          relativeAdeleInfiniteComponent
            (K := K) (L := L) w y)
    (hfinite :
      ∀ w : HeightOneSpectrum (𝓞 K),
        relativeAdeleFiniteComponent
            (K := K) (L := L) w x =
          relativeAdeleFiniteComponent
            (K := K) (L := L) w y) :
    x = y := by
  apply
    (relativeAdeleCoefficientLinearEquiv
      (K := K) (L := L)).injective
  funext i
  apply Prod.ext
  · funext w
    have h :=
      congrArg
        (fun z =>
          (Algebra.TensorProduct.basis
            w.Completion
            (relativeExtensionBasis
              (K := K) (L := L))).repr z i)
        (hinfinite w)
    change (relativeAdeleCoefficient (K := K) (L := L) x i).1 w =
      (relativeAdeleCoefficient (K := K) (L := L) y i).1 w
    simpa using h
  · apply DFunLike.coe_injective
    funext w
    have h :=
      congrArg
        (fun z =>
          (Algebra.TensorProduct.basis
            (w.adicCompletion K)
            (relativeExtensionBasis
              (K := K) (L := L))).repr z i)
        (hfinite w)
    change (relativeAdeleCoefficient (K := K) (L := L) x i).2 w =
      (relativeAdeleCoefficient (K := K) (L := L) y i).2 w
    simpa using h
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.Adele.RestrictedProduct -/
section
open scoped NumberField TensorProduct
open NumberField IsDedekindDomain
noncomputable section
universe u v
variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
 

structure RelativeLocalAdeleData where
   
  infinite :
    ∀ w : InfinitePlace K,
      w.Completion ⊗[K] L
   
  finite :
    ∀ w : HeightOneSpectrum (𝓞 K),
      w.adicCompletion K ⊗[K] L
   

  eventually_integral :
    ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        (Algebra.TensorProduct.basis
            (w.adicCompletion K)
            (relativeExtensionBasis
              (K := K) (L := L))).repr
            (finite w) i ∈
          w.adicCompletionIntegers K
 

noncomputable def relativeLocalAdeleCoefficient
    (a : RelativeLocalAdeleData (K := K) (L := L))
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    NumberField.AdeleRing (𝓞 K) K :=
  ⟨fun w =>
      (Algebra.TensorProduct.basis
          w.Completion
          (relativeExtensionBasis
            (K := K) (L := L))).repr
          (a.infinite w) i,
    ⟨fun w =>
        (Algebra.TensorProduct.basis
            (w.adicCompletion K)
            (relativeExtensionBasis
              (K := K) (L := L))).repr
            (a.finite w) i,
      a.eventually_integral i⟩⟩
 

noncomputable def relativeAdeleOfLocalData
    (a : RelativeLocalAdeleData (K := K) (L := L)) :
    RelativeAdeleRing K L :=
  relativeAdeleOfCoefficients
    (K := K) (L := L)
    (relativeLocalAdeleCoefficient
      (K := K) (L := L) a)
omit [NumberField L] in
@[simp]
theorem relativeAdeleOfLocalData_infiniteComponent
    (a : RelativeLocalAdeleData (K := K) (L := L))
    (w : InfinitePlace K) :
    relativeAdeleInfiniteComponent
        (K := K) (L := L) w
        (relativeAdeleOfLocalData
          (K := K) (L := L) a) =
      a.infinite w := by
  apply
    (Algebra.TensorProduct.basis
      w.Completion
      (relativeExtensionBasis
        (K := K) (L := L))).repr.injective
  apply Finsupp.ext
  intro i
  rw [relativeAdeleInfiniteComponent_basis_repr]
  have h :=
    relativeAdeleCoefficient_ofCoefficients
      (K := K) (L := L)
      (relativeLocalAdeleCoefficient
        (K := K) (L := L) a) i
  exact congrArg
    (fun q : NumberField.AdeleRing (𝓞 K) K =>
      q.1 w) h
omit [NumberField L] in
@[simp]
theorem relativeAdeleOfLocalData_finiteComponent
    (a : RelativeLocalAdeleData (K := K) (L := L))
    (w : HeightOneSpectrum (𝓞 K)) :
    relativeAdeleFiniteComponent
        (K := K) (L := L) w
        (relativeAdeleOfLocalData
          (K := K) (L := L) a) =
      a.finite w := by
  apply
    (Algebra.TensorProduct.basis
      (w.adicCompletion K)
      (relativeExtensionBasis
        (K := K) (L := L))).repr.injective
  apply Finsupp.ext
  intro i
  rw [relativeAdeleFiniteComponent_basis_repr]
  have h :=
    relativeAdeleCoefficient_ofCoefficients
      (K := K) (L := L)
      (relativeLocalAdeleCoefficient
        (K := K) (L := L) a) i
  exact congrArg
    (fun q : NumberField.AdeleRing (𝓞 K) K =>
      q.2.1 w) h
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.SUnit.GaloisAction -/
section
open scoped BigOperators Classical NumberField nonZeroDivisors
open IsDedekindDomain Module


noncomputable section
variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
 
noncomputable def finitePlaceEquiv
    (σ : L ≃ₐ[K] L) :
    HeightOneSpectrum (𝓞 L) ≃
      HeightOneSpectrum (𝓞 L) :=
  HeightOneSpectrum.equivOfRingEquiv
    (NumberField.RingOfIntegers.mapAlgEquiv σ).toRingEquiv
omit [NumberField K] [NumberField L] in
@[simp]
theorem finitePlaceEquiv_asIdeal
    (σ : L ≃ₐ[K] L)
    (v : HeightOneSpectrum (𝓞 L)) :
    (finitePlaceEquiv K L σ v).asIdeal =
      v.asIdeal.map
        (NumberField.RingOfIntegers.mapAlgEquiv σ).toRingEquiv := by
  ext x
  exact Ideal.symm_apply_mem_of_equiv_iff
section FinitePlaceAction
end FinitePlaceAction
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.NormalClosure -/
section
noncomputable section
universe u v
variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
 

abbrev finiteNormalClosure :=
  IntermediateField.normalClosure K L (AlgebraicClosure K)
noncomputable instance finiteNormalClosure_numberField :
    NumberField (finiteNormalClosure K L) :=
  NumberField.of_module_finite K (finiteNormalClosure K L)
noncomputable instance finiteNormalClosure_isGalois :
    IsGalois K (finiteNormalClosure K L) := by
  let f : L →ₐ[K] AlgebraicClosure K :=
    IsAlgClosed.lift
  let : Algebra L (AlgebraicClosure K) :=
    f.toRingHom.toAlgebra
  let : IsScalarTower K L (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq'
      f.comp_algebraMap.symm
  infer_instance
 
noncomputable def finiteNormalClosureEmbedding :
    L →ₐ[K] finiteNormalClosure K L :=
  let f : L →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  f.codRestrict
    (IntermediateField.normalClosure K L
      (AlgebraicClosure K)).toSubalgebra
    (fun x =>
      f.fieldRange_le_normalClosure
        (show f x ∈ f.fieldRange from ⟨x, rfl⟩))
end
end

/- ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Basic -/
section
noncomputable section
namespace HilbertRamification
namespace Dedekind
open scoped Pointwise
open Algebra Module
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
 

theorem exists_smul_eq_of_isGaloisGroup
    (p : Ideal A) (P Q : Ideal B)
    [P.IsPrime] [P.LiesOver p] [Q.IsPrime] [Q.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    ∃ σ : G, σ • P = Q := by
  exact Ideal.exists_smul_eq_of_isGaloisGroup p P Q G
end Dedekind
end HilbertRamification
end
end

/- ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.PrimeContractions -/
section
noncomputable section
namespace HilbertRamification
namespace Dedekind
open Algebra NumberField
open scoped Pointwise
variable {K L : Type*}
variable [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable (G : Type*) [Group G] [MulSemiringAction G L] [SMulCommClass G K L]
 

theorem ringOfIntegers_under_ne_bot
    {E F : Type*} [Field E] [Field F] [NumberField E] [NumberField F]
    [Algebra E F] (P : Ideal (𝓞 F)) [P.IsMaximal] :
    P.under (𝓞 E) ≠ ⊥ := by
  exact
    Ring.ne_bot_of_isMaximal_of_not_isField
      (M := P.under (𝓞 E)) inferInstance
      (RingOfIntegers.not_isField E)
 

abbrev basePrime
    (P : Ideal (𝓞 L)) :
    Ideal (𝓞 K) :=
  P.under (𝓞 K)
 
instance basePrime_isPrime
    (P : Ideal (𝓞 L)) [P.IsPrime] :
    (basePrime (K := K) P).IsPrime :=
  inferInstance
end Dedekind
end HilbertRamification
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.Completion.ExtensionIndex -/
section
open scoped NumberField Classical
open NumberField IsDedekindDomain
noncomputable section
open AlgebraicNumberTheory.Valuations
universe u v w
variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
 
noncomputable def finitePlaceBelow
    (W : HeightOneSpectrum (𝓞 L)) :
    HeightOneSpectrum (𝓞 K) where
  asIdeal := W.asIdeal.under (𝓞 K)
  isPrime := inferInstance
  ne_bot :=
    HilbertRamification.Dedekind.ringOfIntegers_under_ne_bot
      (E := K) (F := L) W.asIdeal
@[simp]
theorem finitePlaceBelow_asIdeal
    (W : HeightOneSpectrum (𝓞 L)) :
    (finitePlaceBelow (K := K) W).asIdeal =
      W.asIdeal.under (𝓞 K) :=
  rfl
section Tower
variable {M : Type w}
    [Field M] [NumberField M]
    [Algebra K M] [Algebra M L]
    [IsScalarTower K M L]
end Tower
section Centre
variable [FiniteDimensional K L]
omit [NumberField L] [FiniteDimensional K L] in
 

theorem finitePlaceExtension_nonarchimedean
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    LubinTate.Valuations.NonarchimedeanAbsoluteValue w.1 :=
  (AbsoluteValue.isNonarchimedean_iff_bounded_nat w.1).1
    (absoluteValueExtension_isNonarchimedean
      (HeightOneSpectrum.adicAbv K v)
      (HeightOneSpectrum.isNonarchimedean_adicAbv K v) w)
 

noncomputable def finitePlaceExtensionValuationSubring
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    ValuationSubring L :=
  absoluteValueValuationSubring w.1
    (finitePlaceExtension_nonarchimedean
      (K := K) (L := L) v w)
omit [NumberField L] [FiniteDimensional K L] in
 

theorem ringOfIntegers_mem_finitePlaceExtensionValuationSubring
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (x : 𝓞 L) :
    (x : L) ∈
      finitePlaceExtensionValuationSubring
        (K := K) (L := L) v w := by
  rw [finitePlaceExtensionValuationSubring,
    mem_absoluteValueValuationSubring_iff]
  exact
    absoluteValue_le_one_of_isIntegral w.1
      (absoluteValueExtension_isNonarchimedean
        (HeightOneSpectrum.adicAbv K v)
        (HeightOneSpectrum.isNonarchimedean_adicAbv K v) w)
      x.property
 

noncomputable def ringOfIntegersToFinitePlaceExtensionValuationSubring
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    𝓞 L →+*
      finitePlaceExtensionValuationSubring
        (K := K) (L := L) v w :=
  RingHom.codRestrict (algebraMap (𝓞 L) L)
    (finitePlaceExtensionValuationSubring
      (K := K) (L := L) v w).toSubring
    (ringOfIntegers_mem_finitePlaceExtensionValuationSubring
      (K := K) (L := L) v w)
 

noncomputable def finitePlaceExtensionCentreIdeal
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    Ideal (𝓞 L) :=
  (IsLocalRing.maximalIdeal
      (finitePlaceExtensionValuationSubring
        (K := K) (L := L) v w)).comap
    (ringOfIntegersToFinitePlaceExtensionValuationSubring
      (K := K) (L := L) v w)
omit [NumberField L] [FiniteDimensional K L] in
 
theorem mem_finitePlaceExtensionCentreIdeal_iff
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (x : 𝓞 L) :
    x ∈ finitePlaceExtensionCentreIdeal
        (K := K) (L := L) v w ↔
      w.1 (x : L) < 1 := by
  let A :=
    finitePlaceExtensionValuationSubring
      (K := K) (L := L) v w
  let f :=
    ringOfIntegersToFinitePlaceExtensionValuationSubring
      (K := K) (L := L) v w
  change
    f x ∈ IsLocalRing.maximalIdeal A ↔
      w.1 (((f x : A) : L)) < 1
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact
    not_isUnit_iff_abs_lt_one_of_mem_iff_le_one
      w.1 A
      (fun y => by
        change
          y ∈ finitePlaceExtensionValuationSubring
              (K := K) (L := L) v w ↔
            w.1 y ≤ 1
        rw [finitePlaceExtensionValuationSubring,
          mem_absoluteValueValuationSubring_iff])
      (f x)
omit [NumberField L] [FiniteDimensional K L] in
theorem finitePlaceExtensionCentreIdeal_isPrime
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    (finitePlaceExtensionCentreIdeal
      (K := K) (L := L) v w).IsPrime := by
  unfold finitePlaceExtensionCentreIdeal
  exact Ideal.comap_isPrime _ _
omit [NumberField L] [FiniteDimensional K L] in
 
theorem finitePlaceExtensionCentreIdeal_under
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    (finitePlaceExtensionCentreIdeal
        (K := K) (L := L) v w).under (𝓞 K) =
      v.asIdeal := by
  ext x
  change
    algebraMap (𝓞 K) (𝓞 L) x ∈
        finitePlaceExtensionCentreIdeal
          (K := K) (L := L) v w ↔
      x ∈ v.asIdeal
  rw [mem_finitePlaceExtensionCentreIdeal_iff]
  have hcoe :
      ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) =
        algebraMap K L (x : K) := by
    rfl
  rw [hcoe, w.2]
  rw [← FinitePlace.norm_embedding]
  exact FinitePlace.norm_lt_one_iff_mem (K := K) v x
omit [NumberField L] [FiniteDimensional K L] in
theorem finitePlaceExtensionCentreIdeal_ne_bot
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    finitePlaceExtensionCentreIdeal
        (K := K) (L := L) v w ≠ ⊥ := by
  intro hbot
  apply v.ne_bot
  rw [← finitePlaceExtensionCentreIdeal_under
    (K := K) (L := L) v w, hbot]
  simp
 

noncomputable def finitePlaceExtensionCentre
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    HeightOneSpectrum (𝓞 L) where
  asIdeal :=
    finitePlaceExtensionCentreIdeal
      (K := K) (L := L) v w
  isPrime :=
    finitePlaceExtensionCentreIdeal_isPrime
      (K := K) (L := L) v w
  ne_bot :=
    finitePlaceExtensionCentreIdeal_ne_bot
      (K := K) (L := L) v w
omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem finitePlaceExtensionCentre_asIdeal
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    (finitePlaceExtensionCentre
      (K := K) (L := L) v w).asIdeal =
      finitePlaceExtensionCentreIdeal
        (K := K) (L := L) v w :=
  rfl
omit [FiniteDimensional K L] in
@[simp]
theorem finitePlaceBelow_finitePlaceExtensionCentre
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    finitePlaceBelow (K := K)
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w) =
      v := by
  apply HeightOneSpectrum.ext
  exact
    finitePlaceExtensionCentreIdeal_under
      (K := K) (L := L) v w
omit [FiniteDimensional K L] in
 

theorem finitePlaceExtensionValuationSubring_eq_localization
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    finitePlaceExtensionValuationSubring
        (K := K) (L := L) v w =
      (finitePlaceExtensionCentre
        (K := K) (L := L) v w).valuationSubringAtPrime L := by
  let P :=
    finitePlaceExtensionCentreIdeal
      (K := K) (L := L) v w
  let : P.IsPrime :=
    finitePlaceExtensionCentreIdeal_isPrime
      (K := K) (L := L) v w
  let W :=
    finitePlaceExtensionCentre
      (K := K) (L := L) v w
  let V := W.valuationSubringAtPrime L
  let A :=
    finitePlaceExtensionValuationSubring
      (K := K) (L := L) v w
  have hVA : V ≤ A := by
    rintro x ⟨a, s, hs, rfl⟩
    have haA : (a : L) ∈ A :=
      ringOfIntegers_mem_finitePlaceExtensionValuationSubring
        (K := K) (L := L) v w a
    have hsA : (s : L) ∈ A :=
      ringOfIntegers_mem_finitePlaceExtensionValuationSubring
        (K := K) (L := L) v w s
    have haLe : w.1 (a : L) ≤ 1 := by
      change (a : L) ∈
        finitePlaceExtensionValuationSubring
          (K := K) (L := L) v w at haA
      rw [finitePlaceExtensionValuationSubring,
        mem_absoluteValueValuationSubring_iff] at haA
      exact haA
    have hsLe : w.1 (s : L) ≤ 1 := by
      change (s : L) ∈
        finitePlaceExtensionValuationSubring
          (K := K) (L := L) v w at hsA
      rw [finitePlaceExtensionValuationSubring,
        mem_absoluteValueValuationSubring_iff] at hsA
      exact hsA
    have hsNotLt : ¬ w.1 (s : L) < 1 := by
      intro hlt
      apply hs
      exact
        (mem_finitePlaceExtensionCentreIdeal_iff
          (K := K) (L := L) v w s).2 hlt
    have hsEq : w.1 (s : L) = 1 :=
      le_antisymm hsLe (not_lt.mp hsNotLt)
    change
      (a : L) * (s : L)⁻¹ ∈
        finitePlaceExtensionValuationSubring
          (K := K) (L := L) v w
    rw [finitePlaceExtensionValuationSubring,
      mem_absoluteValueValuationSubring_iff,
      map_mul, map_inv₀, hsEq, inv_one, mul_one]
    exact haLe
  have hAne : A ≠ ⊤ := by
    intro htop
    obtain ⟨x, hx0, hx1⟩ :=
      RayClass.adicAbv_isNontrivial v
    let y : L := algebraMap K L x
    have hy0 : y ≠ 0 := by
      change algebraMap K L x ≠ 0
      simpa only [map_zero] using
        (algebraMap K L).injective.ne hx0
    have hy1 : w.1 y ≠ 1 := by
      change w.1 (algebraMap K L x) ≠ 1
      rw [w.2]
      exact hx1
    have hle (z : L) : w.1 z ≤ 1 := by
      have hzA : z ∈ A := by
        rw [htop]
        trivial
      change
        z ∈ finitePlaceExtensionValuationSubring
          (K := K) (L := L) v w at hzA
      rw [finitePlaceExtensionValuationSubring,
        mem_absoluteValueValuationSubring_iff] at hzA
      exact hzA
    have honeLe : 1 ≤ w.1 y := by
      calc
        1 = w.1 y * w.1 y⁻¹ := by
          rw [← map_mul, mul_inv_cancel₀ hy0, map_one]
        _ ≤ w.1 y * 1 :=
          mul_le_mul_of_nonneg_left (hle y⁻¹) (w.1.nonneg y)
        _ = w.1 y := mul_one _
    exact hy1 (le_antisymm (hle y) honeLe)
  exact (V.eq_of_le_of_ne_top hVA hAne).symm
section CrossBaseEquivalence
variable {F M : Type*}
    [Field F] [NumberField F]
    [Field M] [NumberField M]
    [Algebra F L] [Algebra M L]
omit [Algebra K L] [FiniteDimensional K L] in
 


theorem finitePlaceExtensions_isEquiv_of_centres_eq
    (vF : HeightOneSpectrum (𝓞 F))
    (vM : HeightOneSpectrum (𝓞 M))
    (wF :
      AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv F vF) L)
    (wM :
      AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv M vM) L)
    (hcentre :
      finitePlaceExtensionCentre
          (K := F) (L := L) vF wF =
        finitePlaceExtensionCentre
          (K := M) (L := L) vM wM) :
    wF.1.IsEquiv wM.1 := by
  have hsubring :
      finitePlaceExtensionValuationSubring
          (K := F) (L := L) vF wF =
        finitePlaceExtensionValuationSubring
          (K := M) (L := L) vM wM := by
    rw [finitePlaceExtensionValuationSubring_eq_localization,
      finitePlaceExtensionValuationSubring_eq_localization,
      hcentre]
  have hle (x : L) :
      wF.1 x ≤ 1 ↔ wM.1 x ≤ 1 := by
    change
      x ∈
          finitePlaceExtensionValuationSubring
            (K := F) (L := L) vF wF ↔
        x ∈
          finitePlaceExtensionValuationSubring
            (K := M) (L := L) vM wM
    rw [hsubring]
  apply AbsoluteValue.isEquiv_iff_lt_one_iff.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    simp
  calc
    wF.1 x < 1 ↔ 1 < (wF.1 x)⁻¹ :=
      (one_lt_inv₀ (wF.1.pos hx)).symm
    _ ↔ 1 < wF.1 x⁻¹ := by
      rw [map_inv₀]
    _ ↔ ¬ wF.1 x⁻¹ ≤ 1 := not_le.symm
    _ ↔ ¬ wM.1 x⁻¹ ≤ 1 :=
      not_congr (hle x⁻¹)
    _ ↔ 1 < wM.1 x⁻¹ := not_le
    _ ↔ 1 < (wM.1 x)⁻¹ := by
      rw [map_inv₀]
    _ ↔ wM.1 x < 1 :=
      one_lt_inv₀ (wM.1.pos hx)
end CrossBaseEquivalence
omit [FiniteDimensional K L] in
 

theorem finitePlaceExtensionCentre_injective
    (v : HeightOneSpectrum (𝓞 K)) :
    Function.Injective
      (finitePlaceExtensionCentre
        (K := K) (L := L) v) := by
  intro w w' hcentre
  have hequiv : w.1.IsEquiv w'.1 :=
    finitePlaceExtensions_isEquiv_of_centres_eq
      (F := K) (M := K) v v w w' hcentre
  exact
    equivalent_exactExtensions_eq
      (HeightOneSpectrum.adicAbv K v)
      (RayClass.adicAbv_isNontrivial v) w w'
      ((LubinTate.Valuations.equivalentAbsoluteValues_iff_isEquiv
        w.1 w'.1).2 hequiv)
omit [NumberField L] [FiniteDimensional K L] in
 

theorem finitePlaceExtensionCentre_conjugate
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (σ : L ≃ₐ[K] L) :
    finitePlaceExtensionCentre
        (K := K) (L := L) v
        (absoluteValueExtensionConjugate
          (HeightOneSpectrum.adicAbv K v) w σ) =
      finitePlaceEquiv K L σ⁻¹
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w) := by
  apply HeightOneSpectrum.ext
  ext x
  change
    x ∈ finitePlaceExtensionCentreIdeal
        (K := K) (L := L) v
        (absoluteValueExtensionConjugate
          (HeightOneSpectrum.adicAbv K v) w σ) ↔
      NumberField.RingOfIntegers.mapRingHom
          σ.toRingHom x ∈
        finitePlaceExtensionCentreIdeal
          (K := K) (L := L) v w
  rw [mem_finitePlaceExtensionCentreIdeal_iff,
    mem_finitePlaceExtensionCentreIdeal_iff]
  rfl
 

noncomputable def finitePlaceExtensionCentreInFibre
    (v : HeightOneSpectrum (𝓞 K)) :
    AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv K v) L →
      {W : HeightOneSpectrum (𝓞 L) //
        finitePlaceBelow (K := K) W = v} :=
  fun w =>
    ⟨finitePlaceExtensionCentre (K := K) (L := L) v w,
      finitePlaceBelow_finitePlaceExtensionCentre
        (K := K) (L := L) v w⟩
omit [FiniteDimensional K L] in
@[simp]
theorem finitePlaceExtensionCentreInFibre_coe
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    (finitePlaceExtensionCentreInFibre
        (K := K) (L := L) v w :
      HeightOneSpectrum (𝓞 L)) =
      finitePlaceExtensionCentre (K := K) (L := L) v w :=
  rfl
omit [FiniteDimensional K L] in
theorem finitePlaceExtensionCentreInFibre_injective
    (v : HeightOneSpectrum (𝓞 K)) :
    Function.Injective
      (finitePlaceExtensionCentreInFibre
        (K := K) (L := L) v) := by
  intro w w' h
  apply finitePlaceExtensionCentre_injective
    (K := K) (L := L) v
  exact congrArg Subtype.val h
private theorem
    finitePlaceExtensionCentreInFibre_surjective_of_isGalois
    [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    Function.Surjective
      (finitePlaceExtensionCentreInFibre
        (K := K) (L := L) v) := by
  let w₀ : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L :=
    pullbackAbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v)
      (RayClass.adicAbv_isNontrivial v)
      IsAlgClosed.lift
  let W₀ :=
    finitePlaceExtensionCentre (K := K) (L := L) v w₀
  let : Finite (L ≃ₐ[K] L) :=
    IsGaloisGroup.finite (L ≃ₐ[K] L) K L
  let :
      IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing
      (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  intro W
  let : W₀.asIdeal.LiesOver v.asIdeal :=
    ⟨(finitePlaceExtensionCentreIdeal_under
      (K := K) (L := L) v w₀).symm⟩
  let : W.1.asIdeal.LiesOver v.asIdeal := ⟨by
    have h := congrArg HeightOneSpectrum.asIdeal W.2
    simpa only [finitePlaceBelow_asIdeal] using h.symm⟩
  obtain ⟨σ, hσ⟩ :=
    HilbertRamification.Dedekind.exists_smul_eq_of_isGaloisGroup
      v.asIdeal W₀.asIdeal W.1.asIdeal (L ≃ₐ[K] L)
  have hplace :
      finitePlaceEquiv K L σ W₀ = W.1 := by
    apply HeightOneSpectrum.ext
    rw [finitePlaceEquiv_asIdeal]
    exact hσ
  refine ⟨absoluteValueExtensionConjugate
      (HeightOneSpectrum.adicAbv K v) w₀ σ⁻¹, ?_⟩
  apply Subtype.ext
  rw [finitePlaceExtensionCentreInFibre_coe,
    finitePlaceExtensionCentre_conjugate]
  simpa only [inv_inv] using hplace
 

theorem finitePlaceExtensionCentreInFibre_surjective
    (v : HeightOneSpectrum (𝓞 K)) :
    Function.Surjective
      (finitePlaceExtensionCentreInFibre
        (K := K) (L := L) v) := by
  intro W
  let M := finiteNormalClosure K L
  let e : L →ₐ[K] M :=
    finiteNormalClosureEmbedding K L
  let : Algebra L M :=
    e.toRingHom.toAlgebra
  let : IsScalarTower K L M :=
    IsScalarTower.of_algebraMap_eq'
      e.comp_algebraMap.symm
  let : FiniteDimensional L M :=
    FiniteDimensional.right K L M
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := 𝓞 M) W.1.asIdeal
  let : Q.IsMaximal :=
    hQmax
  let U : HeightOneSpectrum (𝓞 M) :=
    { asIdeal := Q
      isPrime := hQmax.isPrime
      ne_bot :=
        Ideal.IsMaximal.ne_bot_of_isIntegral_int Q }
  have hUbelowL :
      finitePlaceBelow (K := L) U = W.1 := by
    apply HeightOneSpectrum.ext
    exact hQover.over.symm
  have hUbelowK :
      finitePlaceBelow (K := K) U = v := by
    have htrans :
        finitePlaceBelow (K := K)
            (finitePlaceBelow (K := L) U) =
          finitePlaceBelow (K := K) U := by
      apply HeightOneSpectrum.ext
      exact
        Ideal.under_under
          (A := 𝓞 K) (B := 𝓞 L) (C := 𝓞 M) Q
    rw [← htrans, hUbelowL, W.2]
  let Uv :
      {U : HeightOneSpectrum (𝓞 M) //
        finitePlaceBelow (K := K) U = v} :=
    ⟨U, hUbelowK⟩
  obtain ⟨uM, huM⟩ :=
    finitePlaceExtensionCentreInFibre_surjective_of_isGalois
      (K := K) (L := M) v Uv
  have hcentreM :
      finitePlaceExtensionCentre
          (K := K) (L := M) v uM = U :=
    congrArg Subtype.val huM
  have hcentreIdealM :
      finitePlaceExtensionCentreIdeal
          (K := K) (L := M) v uM = Q := by
    simpa only [finitePlaceExtensionCentre_asIdeal] using
      congrArg HeightOneSpectrum.asIdeal hcentreM
  let uL :
      AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv K v) L :=
    { val :=
        uM.1.comp (f := algebraMap L M)
          (algebraMap L M).injective
      property := by
        intro x
        change
          uM.1
              (algebraMap L M
                (algebraMap K L x)) =
            HeightOneSpectrum.adicAbv K v x
        rw [← IsScalarTower.algebraMap_apply K L M]
        exact uM.2 x }
  refine ⟨uL, ?_⟩
  apply Subtype.ext
  apply HeightOneSpectrum.ext
  ext x
  change
    x ∈ finitePlaceExtensionCentreIdeal
        (K := K) (L := L) v uL ↔
      x ∈ W.1.asIdeal
  rw [mem_finitePlaceExtensionCentreIdeal_iff]
  change
    uM.1 (algebraMap L M (x : L)) < 1 ↔
      x ∈ W.1.asIdeal
  have hmap :
      ((algebraMap (𝓞 L) (𝓞 M) x : 𝓞 M) : M) =
        algebraMap L M (x : L) :=
    rfl
  rw [← hmap]
  rw [← mem_finitePlaceExtensionCentreIdeal_iff
      (K := K) (L := M) v uM
      (algebraMap (𝓞 L) (𝓞 M) x),
    hcentreIdealM, hQover.over]
  rfl
 

noncomputable def finitePlaceExtensionEquivAbove
    (v : HeightOneSpectrum (𝓞 K)) :
    AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv K v) L ≃
      {W : HeightOneSpectrum (𝓞 L) //
        finitePlaceBelow (K := K) W = v} :=
  Equiv.ofBijective
    (finitePlaceExtensionCentreInFibre
      (K := K) (L := L) v)
    ⟨finitePlaceExtensionCentreInFibre_injective
        (K := K) (L := L) v,
      finitePlaceExtensionCentreInFibre_surjective
        (K := K) (L := L) v⟩
end Centre
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.Completion.Comparison -/
section
open scoped NumberField Classical
open NumberField IsDedekindDomain
noncomputable section
open AlgebraicNumberTheory.Valuations
universe u v
variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
omit [FiniteDimensional K L] in
 

theorem finitePlaceExtension_adicAbv_valuationSubring
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    absoluteValueValuationSubring
        (HeightOneSpectrum.adicAbv L
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w))
        (finitePlaceExtension_nonarchimedean
          (K := L) (L := L)
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w)
          ⟨HeightOneSpectrum.adicAbv L
              (finitePlaceExtensionCentre
                (K := K) (L := L) v w),
            fun _ => rfl⟩) =
      finitePlaceExtensionValuationSubring
        (K := K) (L := L) v w := by
  rw [finitePlaceExtensionValuationSubring_eq_localization,
    (finitePlaceExtensionCentre
      (K := K) (L := L) v w).valuationSubringAtPrime_eq_valuationSubring]
  ext x
  rw [mem_absoluteValueValuationSubring_iff]
  change
    HeightOneSpectrum.adicAbv L
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w) x ≤ 1 ↔
      (finitePlaceExtensionCentre
        (K := K) (L := L) v w).valuation L x ≤ 1
  rw [HeightOneSpectrum.adicAbv_def]
  exact_mod_cast
    WithZeroMulInt.toNNReal_le_one_iff
      (HeightOneSpectrum.one_lt_absNorm_nnreal
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w))
omit [FiniteDimensional K L] in
 

theorem finitePlaceExtension_isEquiv_adicAbv
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    w.1.IsEquiv
      (HeightOneSpectrum.adicAbv L
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w)) := by
  apply AbsoluteValue.isEquiv_iff_lt_one_iff.mpr
  intro x
  have hle (y : L) :
      w.1 y ≤ 1 ↔
        HeightOneSpectrum.adicAbv L
            (finitePlaceExtensionCentre
              (K := K) (L := L) v w) y ≤ 1 := by
    rw [← mem_absoluteValueValuationSubring_iff
        w.1 (finitePlaceExtension_nonarchimedean
          (K := K) (L := L) v w),
      ← mem_absoluteValueValuationSubring_iff
        (HeightOneSpectrum.adicAbv L
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w))
        (finitePlaceExtension_nonarchimedean
          (K := L) (L := L)
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w)
          ⟨HeightOneSpectrum.adicAbv L
              (finitePlaceExtensionCentre
                (K := K) (L := L) v w),
            fun _ => rfl⟩)]
    change
      y ∈ finitePlaceExtensionValuationSubring
          (K := K) (L := L) v w ↔
        y ∈ absoluteValueValuationSubring
          (HeightOneSpectrum.adicAbv L
            (finitePlaceExtensionCentre
              (K := K) (L := L) v w))
          (finitePlaceExtension_nonarchimedean
            (K := L) (L := L)
            (finitePlaceExtensionCentre
              (K := K) (L := L) v w)
            ⟨HeightOneSpectrum.adicAbv L
                (finitePlaceExtensionCentre
                  (K := K) (L := L) v w),
              fun _ => rfl⟩)
    rw [finitePlaceExtension_adicAbv_valuationSubring]
  by_cases hx : x = 0
  · subst x
    simp
  calc
    w.1 x < 1 ↔ 1 < (w.1 x)⁻¹ :=
      (one_lt_inv₀ (w.1.pos hx)).symm
    _ ↔ 1 < w.1 x⁻¹ := by rw [map_inv₀]
    _ ↔ ¬ w.1 x⁻¹ ≤ 1 := not_le.symm
    _ ↔ ¬ HeightOneSpectrum.adicAbv L
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w) x⁻¹ ≤ 1 :=
      not_congr (hle x⁻¹)
    _ ↔ 1 < HeightOneSpectrum.adicAbv L
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w) x⁻¹ := not_le
    _ ↔ 1 < (HeightOneSpectrum.adicAbv L
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w) x)⁻¹ := by
      rw [map_inv₀]
    _ ↔ HeightOneSpectrum.adicAbv L
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w) x < 1 :=
      one_lt_inv₀
        ((HeightOneSpectrum.adicAbv L
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w)).pos hx)
 

noncomputable def finitePlaceExtensionExponent
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) : ℝ :=
  (AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp
    (finitePlaceExtension_isEquiv_adicAbv
      (K := K) (L := L) v w)).choose
omit [FiniteDimensional K L] in
theorem finitePlaceExtensionExponent_pos
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    0 < finitePlaceExtensionExponent
      (K := K) (L := L) v w :=
  (AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp
    (finitePlaceExtension_isEquiv_adicAbv
      (K := K) (L := L) v w)).choose_spec.1
omit [FiniteDimensional K L] in
theorem finitePlaceExtension_adicAbv_eq_rpow
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (x : L) :
    HeightOneSpectrum.adicAbv L
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w) x =
      w.1 x ^ finitePlaceExtensionExponent
        (K := K) (L := L) v w :=
  (congrFun
    (AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp
      (finitePlaceExtension_isEquiv_adicAbv
        (K := K) (L := L) v w)).choose_spec.2 x).symm
 

noncomputable def finitePlaceExtensionWithAbsRingEquiv
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    WithAbs w.1 ≃+*
      WithAbs
        (HeightOneSpectrum.adicAbv L
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w)) :=
  WithAbs.congr w.1
    (HeightOneSpectrum.adicAbv L
      (finitePlaceExtensionCentre
        (K := K) (L := L) v w))
    (RingEquiv.refl L)
omit [FiniteDimensional K L] in
theorem finitePlaceExtensionWithAbsRingEquiv_continuous
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    Continuous
      (finitePlaceExtensionWithAbsRingEquiv
        (K := K) (L := L) v w) :=
  (AbsoluteValue.isEquiv_iff_isHomeomorph _ _).mp
    (finitePlaceExtension_isEquiv_adicAbv
      (K := K) (L := L) v w) |>.continuous
omit [FiniteDimensional K L] in
theorem finitePlaceExtensionWithAbsRingEquiv_symm_continuous
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    Continuous
      (finitePlaceExtensionWithAbsRingEquiv
        (K := K) (L := L) v w).symm := by
  rw [finitePlaceExtensionWithAbsRingEquiv,
    WithAbs.congr_symm]
  exact
    ((AbsoluteValue.isEquiv_iff_isHomeomorph _ _).mp
      (finitePlaceExtension_isEquiv_adicAbv
        (K := K) (L := L) v w).symm).continuous
 
noncomputable def finitePlaceExtensionCompletionRingEquiv
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    w.1.Completion ≃+*
      (HeightOneSpectrum.adicAbv L
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w)).Completion :=
  UniformSpace.Completion.mapRingEquiv
    (finitePlaceExtensionWithAbsRingEquiv
      (K := K) (L := L) v w)
    (finitePlaceExtensionWithAbsRingEquiv_continuous
      (K := K) (L := L) v w)
    (finitePlaceExtensionWithAbsRingEquiv_symm_continuous
      (K := K) (L := L) v w)
omit [FiniteDimensional K L] in
@[simp]
theorem finitePlaceExtensionCompletionRingEquiv_toCompletion
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (x : L) :
    finitePlaceExtensionCompletionRingEquiv
        (K := K) (L := L) v w
        (AbsoluteValue.toCompletion w.1 x) =
      AbsoluteValue.toCompletion
        (HeightOneSpectrum.adicAbv L
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w)) x := by
  change
    UniformSpace.Completion.mapRingEquiv
        (finitePlaceExtensionWithAbsRingEquiv
          (K := K) (L := L) v w)
        (finitePlaceExtensionWithAbsRingEquiv_continuous
          (K := K) (L := L) v w)
        (finitePlaceExtensionWithAbsRingEquiv_symm_continuous
          (K := K) (L := L) v w)
      (((WithAbs.equiv w.1).symm x : WithAbs w.1) :
        w.1.Completion) = _
  rw [UniformSpace.Completion.mapRingEquiv_apply,
    UniformSpace.Completion.map_coe
      (uniformContinuous_addMonoidHom_of_continuous
        (finitePlaceExtensionWithAbsRingEquiv_continuous
          (K := K) (L := L) v w))]
  rfl
omit [FiniteDimensional K L] in
 
theorem finitePlaceExtensionCompletionRingEquiv_continuous
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    Continuous
      (finitePlaceExtensionCompletionRingEquiv
        (K := K) (L := L) v w) :=
  UniformSpace.Completion.continuous_map
omit [FiniteDimensional K L] in
 

theorem finitePlaceExtensionCompletionRingEquiv_norm
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (x : w.1.Completion) :
    ‖finitePlaceExtensionCompletionRingEquiv
        (K := K) (L := L) v w x‖ =
      ‖x‖ ^ finitePlaceExtensionExponent
        (K := K) (L := L) v w := by
  refine UniformSpace.Completion.induction_on
    (α := WithAbs w.1) x ?_ ?_
  · exact isClosed_eq
      (continuous_norm.comp
        (finitePlaceExtensionCompletionRingEquiv_continuous
          (K := K) (L := L) v w))
      (continuous_norm.rpow_const
        (fun _ => Or.inr
          (finitePlaceExtensionExponent_pos
            (K := K) (L := L) v w).le))
  · intro a
    change
      ‖UniformSpace.Completion.map
          (finitePlaceExtensionWithAbsRingEquiv
            (K := K) (L := L) v w)
          (a : w.1.Completion)‖ =
        ‖(a : w.1.Completion)‖ ^
          finitePlaceExtensionExponent
            (K := K) (L := L) v w
    rw [UniformSpace.Completion.map_coe
        (uniformContinuous_addMonoidHom_of_continuous
          (finitePlaceExtensionWithAbsRingEquiv_continuous
            (K := K) (L := L) v w)),
      UniformSpace.Completion.norm_coe,
      UniformSpace.Completion.norm_coe,
      WithAbs.norm_eq_apply_ofAbs,
      WithAbs.norm_eq_apply_ofAbs]
    exact finitePlaceExtension_adicAbv_eq_rpow
      (K := K) (L := L) v w (WithAbs.equiv w.1 a)
 

theorem relativeFinitePlaceCompletionRingEquiv_norm
    (W : HeightOneSpectrum (𝓞 L))
    (x : (HeightOneSpectrum.adicAbv L W).Completion) :
    ‖relativeFinitePlaceCompletionRingEquiv W x‖ = ‖x‖ := by
  change ‖relativeFinitePlaceCompletionRingHom W x‖ = ‖x‖
  exact
    (relativeFinitePlaceCompletionRingHom_isometry W).norm_map_of_map_zero
      (map_zero (relativeFinitePlaceCompletionRingHom W)) x
 

noncomputable def finitePlaceExtensionAdicCompletionRingEquiv
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    w.1.Completion ≃+*
      (finitePlaceExtensionCentre
        (K := K) (L := L) v w).adicCompletion L :=
  (finitePlaceExtensionCompletionRingEquiv
    (K := K) (L := L) v w).trans
    (relativeFinitePlaceCompletionRingEquiv
      (finitePlaceExtensionCentre
        (K := K) (L := L) v w))
omit [FiniteDimensional K L] in
theorem finitePlaceExtensionAdicCompletionRingEquiv_norm
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (x : w.1.Completion) :
    ‖finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) v w x‖ =
      ‖x‖ ^ finitePlaceExtensionExponent
        (K := K) (L := L) v w := by
  rw [finitePlaceExtensionAdicCompletionRingEquiv,
    RingEquiv.trans_apply,
    relativeFinitePlaceCompletionRingEquiv_norm,
    finitePlaceExtensionCompletionRingEquiv_norm]
omit [FiniteDimensional K L] in
@[simp]
theorem finitePlaceExtensionAdicCompletionRingEquiv_toCompletion
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (x : L) :
    finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) v w
        (AbsoluteValue.toCompletion w.1 x) =
      FinitePlace.embedding
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w) x := by
  rw [finitePlaceExtensionAdicCompletionRingEquiv,
    RingEquiv.trans_apply,
    finitePlaceExtensionCompletionRingEquiv_toCompletion]
  change
    relativeFinitePlaceCompletionRingHom
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w)
        (((WithAbs.equiv
          (HeightOneSpectrum.adicAbv L
            (finitePlaceExtensionCentre
              (K := K) (L := L) v w))).symm x :
          WithAbs
            (HeightOneSpectrum.adicAbv L
              (finitePlaceExtensionCentre
                (K := K) (L := L) v w))) :
          (HeightOneSpectrum.adicAbv L
            (finitePlaceExtensionCentre
              (K := K) (L := L) v w)).Completion) = _
  rw [relativeFinitePlaceCompletionRingHom_coe]
  rfl
omit [FiniteDimensional K L] in
 

theorem finitePlaceExtensionAdicCompletionRingEquiv_mem_integers_iff
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (x : w.1.Completion) :
    finitePlaceExtensionAdicCompletionRingEquiv
          (K := K) (L := L) v w x ∈
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w).adicCompletionIntegers L ↔
      x ∈ absoluteValueCompletionIntegers w.1
        (absoluteValueExtension_isNonarchimedean
          (HeightOneSpectrum.adicAbv K v)
          (HeightOneSpectrum.isNonarchimedean_adicAbv K v) w) := by
  rw [mem_absoluteValueCompletionIntegers_iff]
  have hrpow :
      ‖x‖ ^ finitePlaceExtensionExponent
          (K := K) (L := L) v w ≤ 1 ↔
        ‖x‖ ≤ 1 := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow_iff (norm_nonneg x) zero_le_one
        (finitePlaceExtensionExponent_pos
          (K := K) (L := L) v w)
  constructor
  · intro hx
    have hnorm :=
      norm_le_one_of_mem_adicCompletionIntegers
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w) hx
    rw [finitePlaceExtensionAdicCompletionRingEquiv_norm] at hnorm
    exact hrpow.mp hnorm
  · intro hx
    apply mem_adicCompletionIntegers_of_norm_le_one
      (finitePlaceExtensionCentre
        (K := K) (L := L) v w)
    rw [finitePlaceExtensionAdicCompletionRingEquiv_norm]
    exact hrpow.mpr hx
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.SPlaces -/
section
open scoped NumberField TensorProduct
open NumberField IsDedekindDomain
noncomputable section

open AlgebraicNumberTheory.Valuations
universe u v
variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
omit [NumberField L] [IsGalois K L] in
 

theorem relativeBasisIntegralAt_repr_mem
    (w : HeightOneSpectrum (𝓞 K))
    (x : w.adicCompletion K ⊗[K] L)
    (hx : RelativeBasisIntegralAt
      (K := K) (L := L) w x)
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    (Algebra.TensorProduct.basis
        (w.adicCompletion K)
        (relativeExtensionBasis
          (K := K) (L := L))).repr x i ∈
      w.adicCompletionIntegers K := by
  classical
  rcases hx with ⟨c, rfl⟩
  simp
  rw [Finset.sum_eq_single i]
  · simpa only [Finsupp.single_eq_same] using (c i).property
  · intro j _ hji
    simp [hji]
  · simp
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.Adele.FiniteRestrictedProductBaseChange -/
section
open scoped NumberField TensorProduct RestrictedProduct
open NumberField IsDedekindDomain
noncomputable section
open AlgebraicNumberTheory.Valuations
universe u v
variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
 


theorem eventually_finitePlace_iff_eventually_all_above
    (P : ∀ _W : HeightOneSpectrum (𝓞 L), Prop) :
    (∀ᶠ W : HeightOneSpectrum (𝓞 L) in Filter.cofinite, P W) ↔
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        ∀ W : {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w},
          P W.1 := by
  constructor
  · intro h
    have hbad :
        {W : HeightOneSpectrum (𝓞 L) | ¬ P W}.Finite :=
      Filter.eventually_cofinite.mp h
    have himage :
        (finitePlaceBelow (K := K) ''
          {W : HeightOneSpectrum (𝓞 L) | ¬ P W}).Finite :=
      hbad.image _
    apply Filter.eventually_cofinite.mpr
    apply himage.subset
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw
    rw [Set.mem_image]
    push Not at hw
    rcases hw with ⟨W, hW⟩
    exact ⟨W.1, hW, W.2⟩
  · intro h
    have hfibre (w : HeightOneSpectrum (𝓞 K)) :
        Finite {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w} := by
      let : Fintype
          (AbsoluteValueExtension
            (HeightOneSpectrum.adicAbv K w) L) :=
        completionTensorDecomposition_extensionFintype
          (HeightOneSpectrum.adicAbv K w)
          (RayClass.adicAbv_isNontrivial w)
      exact
        Finite.of_equiv
          (AbsoluteValueExtension
            (HeightOneSpectrum.adicAbv K w) L)
          (finitePlaceExtensionEquivAbove
            (K := K) (L := L) w)
    have htendsto :
        Filter.Tendsto
          (finitePlaceBelow (K := K))
          Filter.cofinite Filter.cofinite :=
      Filter.Tendsto.cofinite_of_finite_preimage_singleton
        (f := finitePlaceBelow (K := K) (L := L))
        fun w => by
          change
            {W : HeightOneSpectrum (𝓞 L) |
              finitePlaceBelow (K := K) W = w}.Finite
          exact Set.finite_coe_iff.mp (hfibre w)
    filter_upwards [htendsto.eventually h] with W hW
    exact hW ⟨W, rfl⟩
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.Adele.InfinitePlaceTensorBlock -/
section
open scoped NumberField TensorProduct NumberField.LiesOver
open NumberField
noncomputable section
open LocalClassFieldTheory
open AlgebraicNumberTheory.Valuations

universe u v
variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
 

def infinitePlaceCompletionAlgEquiv
    (w : InfinitePlace K) :
    w.Completion ≃ₐ[K] w.1.Completion where
  __ := InfinitePlace.Completion.equiv w
  commutes' _ := rfl
 

noncomputable def infinitePlaceLocalTensorAlgEquiv
    (w : InfinitePlace K) :
    w.Completion ⊗[K] L ≃ₐ[K]
      LocalTensorAlgebra (L := L) w.1 :=
  Algebra.TensorProduct.congr
    (infinitePlaceCompletionAlgEquiv w)
    (AlgEquiv.refl : L ≃ₐ[K] L)
section Galois
variable [IsGalois K L]
section Equivariance
variable
    (w : InfinitePlace K)
    (hw : w.1.IsNontrivial)
    (u : AbsoluteValueExtension w.1 L)
end Equivariance
end Galois
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.Idele.BaseChange -/
section
open scoped NumberField TensorProduct RestrictedProduct
open NumberField IsDedekindDomain
noncomputable section
open AlgebraicNumberTheory.Valuations
universe u v
variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
 
def infinitePlaceBelow
    (W : InfinitePlace L) : InfinitePlace K :=
  W.comap (algebraMap K L)
section InfinitePlaceTower
variable {M : Type*}
    [Field M] [NumberField M]
    [Algebra K M] [Algebra M L]
    [IsScalarTower K M L]
end InfinitePlaceTower
 

def infinitePlaceAboveToExtension
    (w : InfinitePlace K)
    (W : {W : InfinitePlace L //
      infinitePlaceBelow (K := K) W = w}) :
    AbsoluteValueExtension w.1 L := by
  refine ⟨W.1.1, ?_⟩
  intro x
  have h :=
    congrArg (fun v : InfinitePlace K => v x) W.2
  exact h
omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
 


theorem
    infinitePlaceAboveToExtension_surjective_of_isGalois
    [IsGalois K L]
    (w : InfinitePlace K) :
    Function.Surjective
      (infinitePlaceAboveToExtension
        (K := K) (L := L) w) := by
  intro u
  obtain ⟨W₀, hW₀⟩ :=
    InfinitePlace.comap_surjective
      (k := K) (K := L) w
  let W₀' :
      {W : InfinitePlace L //
        infinitePlaceBelow (K := K) W = w} :=
    ⟨W₀, hW₀⟩
  let u₀ : AbsoluteValueExtension w.1 L :=
    infinitePlaceAboveToExtension
      (K := K) (L := L) w W₀'
  obtain ⟨σ, hσ⟩ :=
    absoluteValueConjugacy w.1 w.isNontrivial u₀ u
  let Wσ : InfinitePlace L :=
    W₀.comap σ.toRingEquiv.toRingHom
  have hWσ :
      infinitePlaceBelow (K := K) Wσ = w := by
    apply InfinitePlace.ext
    intro x
    change W₀ (σ (algebraMap K L x)) = w x
    rw [σ.commutes]
    exact congrArg (fun v : InfinitePlace K => v x) hW₀
  refine ⟨⟨Wσ, hWσ⟩, ?_⟩
  rw [hσ]
  apply Subtype.ext
  rfl
 

noncomputable def infinitePlaceAboveEquivExtension
    (w : InfinitePlace K) :
    {W : InfinitePlace L //
      infinitePlaceBelow (K := K) W = w} ≃
      AbsoluteValueExtension w.1 L := by
  apply Equiv.ofBijective
    (infinitePlaceAboveToExtension
      (K := K) (L := L) w)
  constructor
  · intro W W' h
    have habs : W.1.1 = W'.1.1 :=
      congrArg
        (fun u : AbsoluteValueExtension w.1 L => u.1) h
    apply Subtype.ext
    apply Subtype.ext
    exact habs
  · intro u
    let M := finiteNormalClosure K L
    let e : L →ₐ[K] M :=
      finiteNormalClosureEmbedding K L
    let : Algebra L M :=
      e.toRingHom.toAlgebra
    let : IsScalarTower K L M :=
      IsScalarTower.of_algebraMap_eq'
        e.comp_algebraMap.symm
    let : FiniteDimensional L M :=
      FiniteDimensional.right K L M
    let hu : u.1.IsNontrivial :=
      u.isNontrivial w.isNontrivial
    let uOverL : AbsoluteValueExtension u.1 M :=
      pullbackAbsoluteValueExtension
        u.1 hu IsAlgClosed.lift
    let uM : AbsoluteValueExtension w.1 M :=
      { val := uOverL.1
        property := by
          intro x
          rw [IsScalarTower.algebraMap_apply K L M,
            uOverL.2, u.2] }
    obtain ⟨WM, hWM⟩ :=
      infinitePlaceAboveToExtension_surjective_of_isGalois
        (K := K) (L := M) w uM
    let WL : InfinitePlace L :=
      WM.1.comap (algebraMap L M)
    have hWL :
        infinitePlaceBelow (K := K) WL = w := by
      apply InfinitePlace.ext
      intro x
      change
        WM.1
            (algebraMap L M
              (algebraMap K L x)) =
          w x
      rw [← IsScalarTower.algebraMap_apply K L M]
      exact congrArg (fun v : InfinitePlace K => v x) WM.2
    refine ⟨⟨WL, hWL⟩, ?_⟩
    apply Subtype.ext
    ext x
    have hWMval :
        WM.1.1 = uM.1 :=
      congrArg Subtype.val hWM
    change
      WM.1.1 (algebraMap L M x) = u.1 x
    rw [hWMval]
    exact uOverL.2 x
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.AdeleBaseChange -/
section
open scoped NumberField TensorProduct RestrictedProduct
open NumberField IsDedekindDomain
noncomputable section
open AlgebraicNumberTheory.Valuations
universe u v
variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
 

noncomputable def finitePlaceTensorRingEquivAboveAdic
    (w : HeightOneSpectrum (𝓞 K)) :
    (w.adicCompletion K ⊗[K] L) ≃+*
      ∀ W : {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w},
        W.1.adicCompletion L := by
  let vK := HeightOneSpectrum.adicAbv K w
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial w
  letI : ∀ u : AbsoluteValueExtension vK L,
      Algebra vK.Completion u.1.Completion :=
    fun u =>
      AbsoluteValue.completionAlgebra vK u.1 u.2
  let e₁ :
      (w.adicCompletion K ⊗[K] L) ≃+*
        (∀ u : AbsoluteValueExtension vK L,
          u.1.Completion) :=
    (relativeFinitePlaceLocalTensorAlgEquiv
      (K := K) (L := L) w).symm.toRingEquiv.trans
      (completionTensorDecomposition_left
        (K := K) (L := L) vK hvK).toRingEquiv
  let e₂ :
      (∀ u : AbsoluteValueExtension vK L,
          u.1.Completion) ≃+*
        (∀ u : AbsoluteValueExtension vK L,
          (finitePlaceExtensionCentre
            (K := K) (L := L) w u).adicCompletion L) :=
    RingEquiv.piCongrRight fun u =>
      finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) w u
  let e₃ :
      (∀ u : AbsoluteValueExtension vK L,
          (finitePlaceExtensionCentre
            (K := K) (L := L) w u).adicCompletion L) ≃+*
        (∀ W : {W : HeightOneSpectrum (𝓞 L) //
            finitePlaceBelow (K := K) W = w},
          W.1.adicCompletion L) :=
    RingEquiv.piCongrLeft
      (fun W : {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w} =>
        W.1.adicCompletion L)
      (finitePlaceExtensionEquivAbove
        (K := K) (L := L) w)
  exact e₁.trans (e₂.trans e₃)
 

@[simp]
theorem finitePlaceTensorRingEquivAboveAdic_apply_extension
    (w : HeightOneSpectrum (𝓞 K))
    (x : w.adicCompletion K ⊗[K] L)
    (u : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L) :
    finitePlaceTensorRingEquivAboveAdic
        (K := K) (L := L) w x
        (finitePlaceExtensionEquivAbove
          (K := K) (L := L) w u) =
      finitePlaceExtensionAdicCompletionRingEquiv
          (K := K) (L := L) w u
        (finitePlaceLocalTensorDecompositionComponent
          (K := K) (L := L) w u x) := by
  let P :=
    fun W : {W : HeightOneSpectrum (𝓞 L) //
        finitePlaceBelow (K := K) W = w} =>
      W.1.adicCompletion L
  let e := finitePlaceExtensionEquivAbove (K := K) (L := L) w
  let f : ∀ a, P (e a) := fun a =>
    finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) w a
      (finitePlaceLocalTensorDecompositionComponent
        (K := K) (L := L) w a x)
  exact Equiv.piCongrLeft_apply_apply P e f u
 

noncomputable def infiniteCompletionRingProductReindexAbove
    (w : InfinitePlace K) :
    (∀ u : AbsoluteValueExtension w.1 L,
      u.1.Completion) ≃+*
      ∀ W : {W : InfinitePlace L //
          infinitePlaceBelow (K := K) W = w},
        W.1.1.Completion := by
  let e :=
    Equiv.piCongrLeft'
      (fun u : AbsoluteValueExtension w.1 L =>
        u.1.Completion)
      (infinitePlaceAboveEquivExtension
        (K := K) (L := L) w).symm
  exact
    { e with
      map_add' := by
        intro x y
        funext W
        rfl
      map_mul' := by
        intro x y
        funext W
        rfl }
 

noncomputable def infinitePlaceTensorRingEquivAbove
    (w : InfinitePlace K) :
    (w.Completion ⊗[K] L) ≃+*
      ∀ W : {W : InfinitePlace L //
          infinitePlaceBelow (K := K) W = w},
        W.1.Completion := by
  letI : ∀ u : AbsoluteValueExtension w.1 L,
      Algebra w.1.Completion u.1.Completion :=
    fun u =>
      AbsoluteValue.completionAlgebra w.1 u.1 u.2
  exact
    (infinitePlaceLocalTensorAlgEquiv
      (K := K) (L := L) w).toRingEquiv.trans
    ((completionTensorDecomposition_left
        (K := K) (L := L) w.1
        w.isNontrivial).toRingEquiv.trans
      ((infiniteCompletionRingProductReindexAbove
          (K := K) (L := L) w).trans
        (RingEquiv.piCongrRight fun W =>
          (InfinitePlace.Completion.equiv W.1).symm)))
 

@[simp]
theorem infinitePlaceTensorRingEquivAbove_apply
    (w : InfinitePlace K)
    (z : w.Completion ⊗[K] L)
    (W : {W : InfinitePlace L //
      infinitePlaceBelow (K := K) W = w}) :
    infinitePlaceTensorRingEquivAbove
        (K := K) (L := L) w z W =
      (InfinitePlace.Completion.equiv W.1).symm
        (completionTensorDecomposition_left
          w.1 w.isNontrivial
          (infinitePlaceLocalTensorAlgEquiv
            (K := K) (L := L) w z)
          (infinitePlaceAboveEquivExtension
            (K := K) (L := L) w W)) :=
  rfl
 

noncomputable def finitePlaceAbovePiRingEquiv :
    (∀ w : HeightOneSpectrum (𝓞 K),
      ∀ W : {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w},
        W.1.adicCompletion L) ≃+*
      ∀ W : HeightOneSpectrum (𝓞 L),
        W.adicCompletion L where
  toFun f W :=
    f (finitePlaceBelow (K := K) W) ⟨W, rfl⟩
  invFun f w W := f W.1
  left_inv f := by
    funext w W
    rcases W with ⟨W, hW⟩
    subst w
    rfl
  right_inv f := by
    funext W
    rfl
  map_add' f g := by
    funext W
    rfl
  map_mul' f g := by
    funext W
    rfl
 

noncomputable def relativeFiniteTensorPiRingEquiv :
    (∀ w : HeightOneSpectrum (𝓞 K),
      w.adicCompletion K ⊗[K] L) ≃+*
      ∀ W : HeightOneSpectrum (𝓞 L),
        W.adicCompletion L :=
  (RingEquiv.piCongrRight fun w =>
      finitePlaceTensorRingEquivAboveAdic
        (K := K) (L := L) w).trans
    (finitePlaceAbovePiRingEquiv (K := K) (L := L))
 

@[simp]
theorem relativeFiniteTensorPiRingEquiv_symm_apply
    (y : ∀ W : HeightOneSpectrum (𝓞 L),
      W.adicCompletion L)
    (w : HeightOneSpectrum (𝓞 K)) :
    (relativeFiniteTensorPiRingEquiv
        (K := K) (L := L)).symm y w =
      (finitePlaceTensorRingEquivAboveAdic
        (K := K) (L := L) w).symm
        (fun W => y W.1) :=
  rfl
 

noncomputable def infinitePlaceAbovePiRingEquiv :
    (∀ w : InfinitePlace K,
      ∀ W : {W : InfinitePlace L //
          infinitePlaceBelow (K := K) W = w},
        W.1.Completion) ≃+*
      ∀ W : InfinitePlace L, W.Completion where
  toFun f W :=
    f (infinitePlaceBelow (K := K) W) ⟨W, rfl⟩
  invFun f w W := f W.1
  left_inv f := by
    funext w W
    rcases W with ⟨W, hW⟩
    subst w
    rfl
  right_inv f := by
    funext W
    rfl
  map_add' f g := by
    funext W
    rfl
  map_mul' f g := by
    funext W
    rfl
 

noncomputable def relativeInfiniteTensorPiRingEquiv :
    (∀ w : InfinitePlace K,
      w.Completion ⊗[K] L) ≃+*
      ∀ W : InfinitePlace L, W.Completion :=
  (RingEquiv.piCongrRight fun w =>
      infinitePlaceTensorRingEquivAbove
        (K := K) (L := L) w).trans
    (infinitePlaceAbovePiRingEquiv (K := K) (L := L))
 

theorem relativeLocalTensorDecompositionIntegralAt_iff_aboveAdicRing
    (w : HeightOneSpectrum (𝓞 K))
    (x : w.adicCompletion K ⊗[K] L) :
    RelativeLocalTensorDecompositionIntegralAt
        (K := K) (L := L) w x ↔
      ∀ W : {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w},
        finitePlaceTensorRingEquivAboveAdic
            (K := K) (L := L) w x W ∈
          W.1.adicCompletionIntegers L := by
  constructor
  · intro hx W
    let u :=
      (finitePlaceExtensionEquivAbove
        (K := K) (L := L) w).symm W
    have hW :
        finitePlaceExtensionEquivAbove
            (K := K) (L := L) w u = W :=
      (finitePlaceExtensionEquivAbove
        (K := K) (L := L) w).apply_symm_apply W
    rw [← hW,
      finitePlaceTensorRingEquivAboveAdic_apply_extension]
    exact
      (finitePlaceExtensionAdicCompletionRingEquiv_mem_integers_iff
        (K := K) (L := L) w u _).2 (hx u)
  · intro hx u
    have h :=
      hx (finitePlaceExtensionEquivAbove
        (K := K) (L := L) w u)
    rw [finitePlaceTensorRingEquivAboveAdic_apply_extension] at h
    exact
      (finitePlaceExtensionAdicCompletionRingEquiv_mem_integers_iff
        (K := K) (L := L) w u _).1 h
omit [NumberField L] in
 

theorem relativeAdele_finiteComponent_basisIntegral_of_notMem
    (z : RelativeAdeleRing K L)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ relativeAdeleCoefficientSupport
      (K := K) (L := L) z) :
    RelativeBasisIntegralAt
      (K := K) (L := L) w
      (relativeAdeleFiniteComponent
        (K := K) (L := L) w z) := by
  let c :
      ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
        w.adicCompletionIntegers K :=
    fun i =>
      ⟨(relativeAdeleCoefficient
          (K := K) (L := L) z i).2 w, by
        by_contra hi
        apply hw
        exact
          (mem_relativeAdeleCoefficientSupport_iff
            (K := K) (L := L) z w).2 ⟨i, hi⟩⟩
  refine ⟨c, ?_⟩
  simpa only [c, Subtype.coe_mk] using
    relativeAdeleFiniteComponent_eq_sum_tmul_coefficients
      (K := K) (L := L) z w
 

theorem relativeAdele_eventually_aboveAdicIntegral
    (z : RelativeAdeleRing K L) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ∀ W : {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w},
        finitePlaceTensorRingEquivAboveAdic
            (K := K) (L := L) w
            (relativeAdeleFiniteComponent
              (K := K) (L := L) w z) W ∈
          W.1.adicCompletionIntegers L := by
  classical
  filter_upwards [
    (relativeAdeleCoefficientSupport
      (K := K) (L := L) z).eventually_cofinite_notMem,
    (integralTensorComparisonBadPlaces
      (K := K) (L := L)).eventually_cofinite_notMem] with w hs hbad
  apply
    (relativeLocalTensorDecompositionIntegralAt_iff_aboveAdicRing
      (K := K) (L := L) w _).1
  apply
    (relativeBasisIntegralAt_iff_localTensorDecompositionIntegral_of_notMem
      (K := K) (L := L) w hbad).1
  exact relativeAdele_finiteComponent_basisIntegral_of_notMem
    (K := K) (L := L) z w hs
 
noncomputable def relativeAdeleToAdele
    (z : RelativeAdeleRing K L) :
    NumberField.AdeleRing (𝓞 L) L :=
  ⟨relativeInfiniteTensorPiRingEquiv
      (K := K) (L := L)
      (fun w =>
        relativeAdeleInfiniteComponent
          (K := K) (L := L) w z),
    ⟨relativeFiniteTensorPiRingEquiv
        (K := K) (L := L)
        (fun w =>
          relativeAdeleFiniteComponent
            (K := K) (L := L) w z),
      (eventually_finitePlace_iff_eventually_all_above
        (K := K) (L := L)
        (fun W =>
          relativeFiniteTensorPiRingEquiv
              (K := K) (L := L)
              (fun w =>
                relativeAdeleFiniteComponent
                  (K := K) (L := L) w z) W ∈
            W.adicCompletionIntegers L)).2 <| by
        filter_upwards [
          relativeAdele_eventually_aboveAdicIntegral
            (K := K) (L := L) z] with w hw
        intro W
        rcases W with ⟨W, hW⟩
        subst w
        exact hw ⟨W, rfl⟩⟩⟩
 
@[simp]
theorem relativeAdeleToAdele_infinite
    (z : RelativeAdeleRing K L)
    (W : InfinitePlace L) :
    (relativeAdeleToAdele
      (K := K) (L := L) z).1 W =
      infinitePlaceTensorRingEquivAbove
        (K := K) (L := L)
        (infinitePlaceBelow (K := K) W)
        (relativeAdeleInfiniteComponent
          (K := K) (L := L)
          (infinitePlaceBelow (K := K) W) z) ⟨W, rfl⟩ :=
  rfl
 
@[simp]
theorem relativeAdeleToAdele_finite
    (z : RelativeAdeleRing K L)
    (W : HeightOneSpectrum (𝓞 L)) :
    (relativeAdeleToAdele
      (K := K) (L := L) z).2 W =
      finitePlaceTensorRingEquivAboveAdic
        (K := K) (L := L)
        (finitePlaceBelow (K := K) W)
        (relativeAdeleFiniteComponent
          (K := K) (L := L)
          (finitePlaceBelow (K := K) W) z) ⟨W, rfl⟩ :=
  rfl
 

noncomputable def finiteAdeleRelativeTensorFamily
    (y : IsDedekindDomain.FiniteAdeleRing (𝓞 L) L) :
    ∀ w : HeightOneSpectrum (𝓞 K),
      w.adicCompletion K ⊗[K] L :=
  (relativeFiniteTensorPiRingEquiv
    (K := K) (L := L)).symm (fun W => y W)
 

theorem finiteAdeleRelativeTensorFamily_eventually_basisIntegral
    (y : IsDedekindDomain.FiniteAdeleRing (𝓞 L) L) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      RelativeBasisIntegralAt
        (K := K) (L := L) w
        (finiteAdeleRelativeTensorFamily
          (K := K) (L := L) y w) := by
  have habove :
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        ∀ W : {W : HeightOneSpectrum (𝓞 L) //
            finitePlaceBelow (K := K) W = w},
          y W.1 ∈ W.1.adicCompletionIntegers L :=
    (eventually_finitePlace_iff_eventually_all_above
      (K := K) (L := L)
      (fun W => y W ∈ W.adicCompletionIntegers L)).1 y.2
  filter_upwards [
    habove,
    (integralTensorComparisonBadPlaces
      (K := K) (L := L)).eventually_cofinite_notMem] with w hw hbad
  apply
    (relativeBasisIntegralAt_iff_localTensorDecompositionIntegral_of_notMem
      (K := K) (L := L) w hbad).2
  apply
    (relativeLocalTensorDecompositionIntegralAt_iff_aboveAdicRing
      (K := K) (L := L) w _).2
  intro W
  have hcomponent :=
    congrFun
      ((finitePlaceTensorRingEquivAboveAdic
        (K := K) (L := L) w).apply_symm_apply
          (fun W => y W.1)) W
  rw [finiteAdeleRelativeTensorFamily,
    relativeFiniteTensorPiRingEquiv_symm_apply,
    hcomponent]
  exact hw W
 
noncomputable def adeleToRelativeLocalAdeleData
    (y : NumberField.AdeleRing (𝓞 L) L) :
    RelativeLocalAdeleData (K := K) (L := L) where
  infinite :=
    (relativeInfiniteTensorPiRingEquiv
      (K := K) (L := L)).symm (fun W => y.1 W)
  finite :=
    finiteAdeleRelativeTensorFamily
      (K := K) (L := L) y.2
  eventually_integral i :=
    (finiteAdeleRelativeTensorFamily_eventually_basisIntegral
      (K := K) (L := L) y.2).mono fun w hw =>
        relativeBasisIntegralAt_repr_mem
          (K := K) (L := L) w _ hw i
 
noncomputable def adeleToRelativeAdele
    (y : NumberField.AdeleRing (𝓞 L) L) :
    RelativeAdeleRing K L :=
  relativeAdeleOfLocalData
    (K := K) (L := L)
    (adeleToRelativeLocalAdeleData
      (K := K) (L := L) y)
 

@[simp]
theorem adeleToRelativeAdele_infiniteComponent
    (y : NumberField.AdeleRing (𝓞 L) L)
    (w : InfinitePlace K) :
    relativeAdeleInfiniteComponent
        (K := K) (L := L) w
        (adeleToRelativeAdele
          (K := K) (L := L) y) =
      (relativeInfiniteTensorPiRingEquiv
        (K := K) (L := L)).symm
        (fun W => y.1 W) w := by
  rw [adeleToRelativeAdele,
    relativeAdeleOfLocalData_infiniteComponent]
  rfl
 

@[simp]
theorem adeleToRelativeAdele_finiteComponent
    (y : NumberField.AdeleRing (𝓞 L) L)
    (w : HeightOneSpectrum (𝓞 K)) :
    relativeAdeleFiniteComponent
        (K := K) (L := L) w
        (adeleToRelativeAdele
          (K := K) (L := L) y) =
      (relativeFiniteTensorPiRingEquiv
        (K := K) (L := L)).symm
        (fun W => y.2 W) w := by
  rw [adeleToRelativeAdele,
    relativeAdeleOfLocalData_finiteComponent]
  rfl
 

noncomputable def relativeAdeleBaseChangeRingEquiv :
    RelativeAdeleRing K L ≃+*
      NumberField.AdeleRing (𝓞 L) L where
  toFun :=
    relativeAdeleToAdele (K := K) (L := L)
  invFun :=
    adeleToRelativeAdele (K := K) (L := L)
  left_inv z := by
    apply relativeAdele_ext_of_components
    · intro w
      rw [adeleToRelativeAdele_infiniteComponent]
      change
        (relativeInfiniteTensorPiRingEquiv
          (K := K) (L := L)).symm
            (relativeInfiniteTensorPiRingEquiv
              (K := K) (L := L)
              (fun w =>
                relativeAdeleInfiniteComponent
                  (K := K) (L := L) w z)) w =
          relativeAdeleInfiniteComponent
            (K := K) (L := L) w z
      rw [(relativeInfiniteTensorPiRingEquiv
        (K := K) (L := L)).symm_apply_apply]
    · intro w
      rw [adeleToRelativeAdele_finiteComponent]
      change
        (relativeFiniteTensorPiRingEquiv
          (K := K) (L := L)).symm
            (relativeFiniteTensorPiRingEquiv
              (K := K) (L := L)
              (fun w =>
                relativeAdeleFiniteComponent
                  (K := K) (L := L) w z)) w =
          relativeAdeleFiniteComponent
            (K := K) (L := L) w z
      rw [(relativeFiniteTensorPiRingEquiv
        (K := K) (L := L)).symm_apply_apply]
  right_inv y := by
    apply Prod.ext
    · funext W
      rw [relativeAdeleToAdele_infinite,
        adeleToRelativeAdele_infiniteComponent]
      change
        relativeInfiniteTensorPiRingEquiv
            (K := K) (L := L)
            ((relativeInfiniteTensorPiRingEquiv
              (K := K) (L := L)).symm
              (fun W => y.1 W)) W =
          y.1 W
      rw [(relativeInfiniteTensorPiRingEquiv
        (K := K) (L := L)).apply_symm_apply]
    · apply DFunLike.coe_injective
      funext W
      change
        relativeFiniteTensorPiRingEquiv
            (K := K) (L := L)
            (fun w =>
              relativeAdeleFiniteComponent
                (K := K) (L := L) w
                (adeleToRelativeAdele
                  (K := K) (L := L) y)) W =
          y.2 W
      rw [show
        (fun w =>
          relativeAdeleFiniteComponent
            (K := K) (L := L) w
            (adeleToRelativeAdele
              (K := K) (L := L) y)) =
          (relativeFiniteTensorPiRingEquiv
            (K := K) (L := L)).symm
            (fun W => y.2 W) by
          funext w
          exact adeleToRelativeAdele_finiteComponent
            (K := K) (L := L) y w]
      rw [(relativeFiniteTensorPiRingEquiv
        (K := K) (L := L)).apply_symm_apply]
  map_add' x y := by
    apply Prod.ext
    · funext W
      change
        relativeInfiniteTensorPiRingEquiv
            (K := K) (L := L)
            (fun w =>
              relativeAdeleInfiniteComponent
                (K := K) (L := L) w (x + y)) W =
          relativeInfiniteTensorPiRingEquiv
              (K := K) (L := L)
              (fun w =>
                relativeAdeleInfiniteComponent
                  (K := K) (L := L) w x) W +
            relativeInfiniteTensorPiRingEquiv
              (K := K) (L := L)
              (fun w =>
                relativeAdeleInfiniteComponent
                  (K := K) (L := L) w y) W
      rw [show
        (fun w =>
          relativeAdeleInfiniteComponent
            (K := K) (L := L) w (x + y)) =
          (fun w =>
            relativeAdeleInfiniteComponent
              (K := K) (L := L) w x) +
          (fun w =>
            relativeAdeleInfiniteComponent
              (K := K) (L := L) w y) by
          funext w
          exact map_add _ _ _,
        map_add]
      rfl
    · apply Subtype.ext
      funext W
      change
        relativeFiniteTensorPiRingEquiv
            (K := K) (L := L)
            (fun w =>
              relativeAdeleFiniteComponent
                (K := K) (L := L) w (x + y)) W =
          relativeFiniteTensorPiRingEquiv
              (K := K) (L := L)
              (fun w =>
                relativeAdeleFiniteComponent
                  (K := K) (L := L) w x) W +
            relativeFiniteTensorPiRingEquiv
              (K := K) (L := L)
              (fun w =>
                relativeAdeleFiniteComponent
                  (K := K) (L := L) w y) W
      rw [show
        (fun w =>
          relativeAdeleFiniteComponent
            (K := K) (L := L) w (x + y)) =
          (fun w =>
            relativeAdeleFiniteComponent
              (K := K) (L := L) w x) +
          (fun w =>
            relativeAdeleFiniteComponent
              (K := K) (L := L) w y) by
          funext w
          exact map_add _ _ _,
        map_add]
      rfl
  map_mul' x y := by
    apply Prod.ext
    · funext W
      change
        relativeInfiniteTensorPiRingEquiv
            (K := K) (L := L)
            (fun w =>
              relativeAdeleInfiniteComponent
                (K := K) (L := L) w (x * y)) W =
          relativeInfiniteTensorPiRingEquiv
              (K := K) (L := L)
              (fun w =>
                relativeAdeleInfiniteComponent
                  (K := K) (L := L) w x) W *
            relativeInfiniteTensorPiRingEquiv
              (K := K) (L := L)
              (fun w =>
                relativeAdeleInfiniteComponent
                  (K := K) (L := L) w y) W
      rw [show
        (fun w =>
          relativeAdeleInfiniteComponent
            (K := K) (L := L) w (x * y)) =
          (fun w =>
            relativeAdeleInfiniteComponent
              (K := K) (L := L) w x) *
          (fun w =>
            relativeAdeleInfiniteComponent
              (K := K) (L := L) w y) by
          funext w
          exact map_mul _ _ _,
        map_mul]
      rfl
    · apply Subtype.ext
      funext W
      change
        relativeFiniteTensorPiRingEquiv
            (K := K) (L := L)
            (fun w =>
              relativeAdeleFiniteComponent
                (K := K) (L := L) w (x * y)) W =
          relativeFiniteTensorPiRingEquiv
              (K := K) (L := L)
              (fun w =>
                relativeAdeleFiniteComponent
                  (K := K) (L := L) w x) W *
            relativeFiniteTensorPiRingEquiv
              (K := K) (L := L)
              (fun w =>
                relativeAdeleFiniteComponent
                  (K := K) (L := L) w y) W
      rw [show
        (fun w =>
          relativeAdeleFiniteComponent
            (K := K) (L := L) w (x * y)) =
          (fun w =>
            relativeAdeleFiniteComponent
              (K := K) (L := L) w x) *
          (fun w =>
            relativeAdeleFiniteComponent
              (K := K) (L := L) w y) by
          funext w
          exact map_mul _ _ _,
        map_mul]
      rfl
 

theorem finitePlaceTensorRingEquivAboveAdic_tmul_one
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w})
    (x : L) :
    finitePlaceTensorRingEquivAboveAdic
        (K := K) (L := L) w
        ((1 : w.adicCompletion K) ⊗ₜ[K] x) W =
      algebraMap L (W.1.adicCompletion L) x := by
  obtain ⟨u, rfl⟩ :=
    (finitePlaceExtensionEquivAbove
      (K := K) (L := L) w).surjective W
  rw [finitePlaceTensorRingEquivAboveAdic_apply_extension,
    finitePlaceLocalTensorDecompositionComponent_tmul]
  simp only [map_one, one_mul,
    finitePlaceExtensionAdicCompletionRingEquiv_toCompletion]
  rfl
 

theorem infinitePlaceTensorRingEquivAbove_tmul_one
    (w : InfinitePlace K)
    (W : {W : InfinitePlace L //
      infinitePlaceBelow (K := K) W = w})
    (x : L) :
    infinitePlaceTensorRingEquivAbove
        (K := K) (L := L) w
        ((1 : w.Completion) ⊗ₜ[K] x) W =
      algebraMap L W.1.Completion x := by
  rw [infinitePlaceTensorRingEquivAbove_apply]
  change
    (InfinitePlace.Completion.equiv W.1).symm
        (completionTensorDecomposition_left
          w.1 w.isNontrivial
          ((1 : w.1.Completion) ⊗ₜ[K] x)
          (infinitePlaceAboveEquivExtension
            (K := K) (L := L) w W)) =
      algebraMap L W.1.Completion x
  rw [completionTensorDecomposition_left_tmul_apply]
  simp only [map_one, one_mul]
  apply InfinitePlace.Completion.ext
  rfl
 

theorem relativeAdeleBaseChangeRingEquiv_fieldInclusion
    (x : L) :
    relativeAdeleBaseChangeRingEquiv
        (K := K) (L := L)
        ((1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K] x) =
      algebraMap L (NumberField.AdeleRing (𝓞 L) L) x := by
  change
    relativeAdeleToAdele
        (K := K) (L := L)
        ((1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K] x) =
      algebraMap L (NumberField.AdeleRing (𝓞 L) L) x
  apply Prod.ext
  · funext W
    rw [relativeAdeleToAdele_infinite]
    change
      infinitePlaceTensorRingEquivAbove
          (K := K) (L := L)
          (infinitePlaceBelow (K := K) W)
          ((1 :
            (infinitePlaceBelow
              (K := K) W).Completion) ⊗ₜ[K] x)
          ⟨W, rfl⟩ =
        algebraMap L W.Completion x
    exact infinitePlaceTensorRingEquivAbove_tmul_one
      (K := K) (L := L)
      (infinitePlaceBelow (K := K) W) ⟨W, rfl⟩ x
  · apply DFunLike.coe_injective
    funext W
    rw [relativeAdeleToAdele_finite]
    change
      finitePlaceTensorRingEquivAboveAdic
          (K := K) (L := L)
          (finitePlaceBelow (K := K) W)
          ((1 :
            (finitePlaceBelow
              (K := K) W).adicCompletion K) ⊗ₜ[K] x)
          ⟨W, rfl⟩ =
        algebraMap L (W.adicCompletion L) x
    exact finitePlaceTensorRingEquivAboveAdic_tmul_one
      (K := K) (L := L)
      (finitePlaceBelow (K := K) W) ⟨W, rfl⟩ x
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerBaseChange -/
section
open scoped NumberField TensorProduct
open NumberField IsDedekindDomain
noncomputable section
open AlgebraicNumberTheory.Valuations
universe u
variable
    (K M L : Type u)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]
section RingComparison
 

noncomputable def intermediateRelativeAdeleBaseChangeAlgEquiv :
    RelativeAdeleRing K M ≃ₐ[M]
      NumberField.AdeleRing (𝓞 M) M :=
  AlgEquiv.ofRingEquiv
    (f := relativeAdeleBaseChangeRingEquiv
      (K := K) (L := M))
    (by
      intro m
      change
        relativeAdeleBaseChangeRingEquiv
            (K := K) (L := M)
            ((1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K] m) =
          algebraMap M
            (NumberField.AdeleRing (𝓞 M) M) m
      exact relativeAdeleBaseChangeRingEquiv_fieldInclusion
        (K := K) (L := M) m)
end RingComparison
section IdeleComparison
section ViaOrdinary
end ViaOrdinary
end IdeleComparison
section NormComparison
end NormComparison
section ClassNormComparison
end ClassNormComparison
section OrdinaryNormTower
end OrdinaryNormTower
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Spine -/
section
open scoped NumberField TensorProduct ValuativeRel NNReal
open NumberField IsDedekindDomain
noncomputable section
open AlgebraicNumberTheory.Valuations

open LocalClassFieldTheory

variable
    {K : Type} {L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
namespace LocalInductionInternal
variable (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L)
 

noncomputable abbrev completionAlgebra :
    Algebra vK.Completion w.1.Completion :=
  AbsoluteValue.completionAlgebra vK w.1 w.2
end LocalInductionInternal
end
end

theorem TunnellGroupedPart1.result : TunnellGroupedPart1.Statement := by
  intro K M _ _ _ _ _ _
  exact ⟨intermediateRelativeAdeleBaseChangeAlgEquiv K M⟩
end

namespace TunnellGroupedPart2
open NumberField IsDedekindDomain
open scoped NumberField TensorProduct Classical
set_option maxHeartbeats 3000000 in
def Statement : Prop :=
∀(D:Type)[Field D][NumberField D](p:ℕ),p.Prime → (primitiveRoots p D).Nonempty →
   let V:=HeightOneSpectrum (𝓞 D)
   let A:=AdeleRing (𝓞 D) D
   let U(S T:Finset V):=Subgroup.closure {a:Aˣ |
     (∀ w:InfinitePlace D,∃ y:w.Completion,y^p=a.val.1 w) ∧
     (∀ v∈S,∃ y:v.adicCompletion D,y^p=a.val.2 v) ∧
     ∀ v:V,v∉S∪T → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   let J(F:Finset V):=Subgroup.closure {a:Aˣ | ∀ v:V,v∉F → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   ∀ S T:Finset V,(∀ v:V,v.asIdeal ∣ Ideal.span {(p:𝓞 D)} → v∈S) →
      (U S T).relIndex (J (S∪T))=p^(2*(Nat.card (InfinitePlace D)+S.card))
end TunnellGroupedPart2

section

/-! The local pth-power map has derivative p at 1. Its exact image on small balls, and the product formula for principal ideals, compute the index on supported idèles. -/


/-! The power map has derivative n at 1. On sufficiently small ultrametric balls it acts by exact dilation, and the valuation and residue arithmetic give the local norm defect. -/
/- EllipticCurves.Mathlib.Basic -/
section
section Group
variable {G H : Type*} [Group G] [Group H]
end Group
section Units
variable {α : Type*} [Monoid α]
end Units
section modPow
namespace Units.modPow
variable {α β : Type*} [CommMonoid α] [CommMonoid β] {a b c : α}
open QuotientGroup
end Units.modPow
end modPow
section Ideal
end Ideal
section LinearAlgebra
end LinearAlgebra
section Valuation
open Polynomial
variable {L Γ : Type*} [CommRing L] [LinearOrderedCommGroupWithZero Γ] (ν : Valuation L Γ)
  {t a b : L}
end Valuation
section DedekindDomain
open IsDedekindDomain
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (R) (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra R B]
namespace IsDiscreteValuationRing
variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {A}
end IsDiscreteValuationRing
namespace IsDedekindDomain.HeightOneSpectrum
variable {B C : Type*} [CommRing B] [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C]
variable {L N : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
  [Field N] [Algebra C N] [IsFractionRing C N]
 

theorem comap_maximalIdeal_adicCompletionIntegers (v : HeightOneSpectrum R) :
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)).comap
      (algebraMap R (v.adicCompletionIntegers K)) = v.asIdeal := by
  ext x
  rw [Ideal.mem_comap, ← valuation_lt_one_iff_mem (K := K)]
  refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion K)
    (WithZero (Multiplicative ℤ))))).trans ?_
  rw [show ((algebraMap R (v.adicCompletionIntegers K) x : v.adicCompletionIntegers K) :
    v.adicCompletion K) = ((algebraMap R K x : K) : v.adicCompletion K) from rfl,
    valuedAdicCompletion_eq_valuation']
end IsDedekindDomain.HeightOneSpectrum
end DedekindDomain
namespace Polynomial
variable {R : Type*} [CommRing R] {g : R[X]}
section
variable [Nontrivial R] {q : R[X]} {n : ℕ}
end
section Sylvester
open Module LinearMap LinearEquiv
variable [Nontrivial R] {p : R[X]} {n : ℕ}
end Sylvester
end Polynomial
open Polynomial LinearMap LinearEquiv
namespace AdjoinRoot
variable {R : Type*} [CommRing R] {g : R[X]} {n : ℕ}
section Map
variable {S : Type*} [CommRing S] (σ : R →+* S)
end Map
end AdjoinRoot
section EtaleDecomposition
open Polynomial UniqueFactorizationMonoid
namespace Polynomial
variable {K : Type*} [Field K] {f : K[X]}
namespace Factors
end Factors
end Polynomial
namespace AdjoinRoot
variable {K : Type*} [Field K] {f : K[X]}
end AdjoinRoot
end EtaleDecomposition
section NumberField
open NumberField
variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable [NumberField K] [FiniteDimensional K L]
end NumberField
section Discriminant
open NumberField Module
variable {K : Type*} [Field K] [NumberField K]
end Discriminant
end

/- EllipticCurves.Mathlib.AdicCompletionExtension -/
section
open Polynomial IsDedekindDomain WithZero
namespace IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)
 
theorem valued_irreducible_adicCompletionIntegers {π : v.adicCompletionIntegers K}
    (hπ : Irreducible π) :
    Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π) = exp (-1) := by
  have hgen : IsLocalRing.maximalIdeal (Valued.v : Valuation (v.adicCompletion K)
      ℤᵐ⁰).valuationSubring = Ideal.span {π} := hπ.maximalIdeal_eq
  have huni := Valuation.isUniformizer_of_maximalIdeal_eq_span
    (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)) hgen
  rwa [Valuation.IsUniformizer.iff,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective K)] at huni
 

theorem span_singleton_eq_maximalIdeal_pow {x : v.adicCompletionIntegers K} {e : ℕ}
    (hx : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) x) =
      exp (-(e : ℤ))) :
    Ideal.span {x} = IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ e := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at hx
    exact absurd hx.symm exp_ne_zero
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ
  have hu2 : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
      (u : v.adicCompletionIntegers K)) = 1 :=
    (Valuation.valuationSubring.integers (v := Valued.v)).valuation_unit u
  have hval : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
      (↑u * π ^ n)) = exp (-(n : ℤ)) := by
    rw [map_mul, map_mul, hu2, one_mul, map_pow, map_pow,
      v.valued_irreducible_adicCompletionIntegers hπ, ← exp_nsmul]
    simp
  rw [hval, exp_inj, neg_inj, Int.natCast_inj] at hx
  subst hx
  rw [Ideal.span_singleton_eq_span_singleton.mpr (associated_unit_mul_left _ _ u.isUnit),
    ← Ideal.span_singleton_pow, hπ.maximalIdeal_eq]
 

theorem exists_valued_sub_lt_one (x : v.adicCompletionIntegers K) :
    ∃ a : R, Valued.v ((x : v.adicCompletion K) - algebraMap R (v.adicCompletion K) a) < 1 := by
  
  have hball : {y | Valued.v (y - (x : v.adicCompletion K)) < 1} ∈
      nhds (x : v.adicCompletion K) := by
    rw [Valued.mem_nhds]
    exact ⟨1, fun y hy ↦ by simpa using hy⟩
  obtain ⟨w, hwball, z, rfl⟩ :=
    mem_closure_iff_nhds.mp (denseRange_algebraMap (K := K) v _) _ hball
  rw [Set.mem_ofPred_eq] at hwball
  
  have hz1 : v.valuation K z ≤ 1 := by
    rw [show v.valuation K z = Valued.v (algebraMap K (v.adicCompletion K) z) from
      (v.valuedAdicCompletion_eq_valuation' z).symm]
    calc Valued.v (algebraMap K (v.adicCompletion K) z)
        = Valued.v (algebraMap K (v.adicCompletion K) z - (x : v.adicCompletion K)
            + (x : v.adicCompletion K)) := by ring_nf
      _ ≤ max (Valued.v (algebraMap K (v.adicCompletion K) z - (x : v.adicCompletion K)))
            (Valued.v (x : v.adicCompletion K)) := Valuation.map_add _ _ _
      _ ≤ 1 := max_le hwball.le x.2
  
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hz1 1
  refine ⟨a, ?_⟩
  have ha' : Valued.v (algebraMap K (v.adicCompletion K) z -
      algebraMap R (v.adicCompletion K) a) < 1 := by
    rw [IsScalarTower.algebraMap_apply R K (v.adicCompletion K), ← map_sub,
      show Valued.v (algebraMap K (v.adicCompletion K) (z - algebraMap R K a)) =
        v.valuation K (z - algebraMap R K a) from v.valuedAdicCompletion_eq_valuation' _,
      Valuation.map_sub_swap]
    simpa using ha
  calc Valued.v ((x : v.adicCompletion K) - algebraMap R (v.adicCompletion K) a)
      = Valued.v (((x : v.adicCompletion K) - algebraMap K (v.adicCompletion K) z)
          + (algebraMap K (v.adicCompletion K) z - algebraMap R (v.adicCompletion K) a)) := by
        ring_nf
    _ ≤ max _ _ := Valuation.map_add _ _ _
    _ < 1 := max_lt (by rwa [Valuation.map_sub_swap] at hwball) ha'
 

noncomputable def residueFieldEquivAdicCompletionIntegers :
    (R ⧸ v.asIdeal) ≃+*
      (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) := by
  refine RingEquiv.ofBijective (Ideal.quotientMap (IsLocalRing.maximalIdeal _)
    (algebraMap R (v.adicCompletionIntegers K))
    (le_of_eq (v.comap_maximalIdeal_adicCompletionIntegers (K := K)).symm)) ⟨?_, ?_⟩
  · exact Ideal.quotientMap_injective'
      (le_of_eq (v.comap_maximalIdeal_adicCompletionIntegers (K := K)))
  · intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := v.exists_valued_sub_lt_one (K := K) x
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Ideal.quotientMap_mk]
    refine (Ideal.Quotient.eq).mpr ?_
    refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion K)
      ℤᵐ⁰))).mpr ?_
    rw [show ((algebraMap R (v.adicCompletionIntegers K) a - x : v.adicCompletionIntegers K) :
      v.adicCompletion K) = algebraMap R (v.adicCompletion K) a - (x : v.adicCompletion K)
      from rfl, Valuation.map_sub_swap]
    exact ha
end IsDedekindDomain.HeightOneSpectrum
namespace IsDedekindDomain.HeightOneSpectrum
section Extension
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B] [Module.IsTorsionFree R B]
  {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]
variable (K L)
end Extension
end IsDedekindDomain.HeightOneSpectrum
end

/- ValuedFieldTheory.LocalField.GroupTheory.IntegerMultipleSubgroup -/
section
namespace LocalFieldTheory.DiscreteValuationField
 

def integerMultipleSubgroup (d : ℤ) : Subgroup (Multiplicative ℤ) where
  carrier := {n | d ∣ Multiplicative.toAdd n}
  one_mem' := by
    change d ∣ (0 : ℤ)
    exact dvd_zero d
  mul_mem' := by
    intro x y hx hy
    change d ∣ Multiplicative.toAdd (x * y)
    rw [toAdd_mul]
    exact dvd_add hx hy
  inv_mem' := by
    intro x hx
    change d ∣ Multiplicative.toAdd x⁻¹
    rw [toAdd_inv]
    exact dvd_neg.mpr hx
 
@[simp] theorem mem_integerMultipleSubgroup_iff
    (d : ℤ) (n : Multiplicative ℤ) :
    n ∈ integerMultipleSubgroup d ↔ d ∣ Multiplicative.toAdd n :=
  Iff.rfl
 

def multiplicativeIntToZModHom (d : ℤ) :
    Multiplicative ℤ →* Multiplicative (ZMod d.natAbs) :=
  AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod d.natAbs))
 
theorem multiplicativeIntToZModHom_ker_eq_integerMultipleSubgroup (d : ℤ) :
    (multiplicativeIntToZModHom d).ker = integerMultipleSubgroup d := by
  ext n
  change ((n.toAdd : ZMod d.natAbs) = 0) ↔ d ∣ n.toAdd
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact Int.natAbs_dvd
 
theorem multiplicativeIntToZModHom_surjective (d : ℤ) :
    Function.Surjective (multiplicativeIntToZModHom d) := by
  intro q
  rcases ZMod.intCast_surjective q.toAdd with ⟨n, hn⟩
  refine ⟨Multiplicative.ofAdd n, ?_⟩
  change Multiplicative.ofAdd ((n : ZMod d.natAbs)) = q
  rw [hn]
  rfl
 

noncomputable def valueModIntegerMultipleSubgroupEquivZMod (d : ℤ) :
    Multiplicative ℤ ⧸ integerMultipleSubgroup d ≃*
      Multiplicative (ZMod d.natAbs) :=
  (QuotientGroup.quotientMulEquivOfEq
      (multiplicativeIntToZModHom_ker_eq_integerMultipleSubgroup d).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (multiplicativeIntToZModHom d)
      (multiplicativeIntToZModHom_surjective d))
end LocalFieldTheory.DiscreteValuationField
end

/- ValuedFieldTheory.LocalField.GroupTheory.PowerIndex -/
section
noncomputable section
namespace LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open scoped Int
section NthPowers
universe uG uH uU
variable (G : Type uG) (H : Type uH) (U : Type uU)
variable [CommGroup G] [CommGroup H] [CommGroup U]
 

theorem powMonoidHom_range_map (n : ℕ) (e : G ≃* H) :
    ((powMonoidHom n : G →* G).range).map e.toMonoidHom = (powMonoidHom n : H →* H).range := by
  exact e.map_range_powMonoidHom n
 

theorem powMonoidHom_ker_units_eq_rootsOfUnity
    (R : Type*) [CommRing R] (n : ℕ) :
    (powMonoidHom n : Rˣ →* Rˣ).ker = rootsOfUnity n R := by
  ext x
  exact MonoidHom.mem_ker
 
def nthPowerQuotientEquivOfMulEquiv (n : ℕ) (e : G ≃* H) :
    G ⧸ (powMonoidHom n : G →* G).range ≃* H ⧸ (powMonoidHom n : H →* H).range :=
  QuotientGroup.congr ((powMonoidHom n : G →* G).range) ((powMonoidHom n : H →* H).range) e
    (powMonoidHom_range_map G H n e)
 

theorem finite_nthPowerQuotient_of_mulEquiv
    (n : ℕ) (e : G ≃* H)
    [Finite (H ⧸ (powMonoidHom n : H →* H).range)] :
    Finite (G ⧸ (powMonoidHom n : G →* G).range) :=
  Finite.of_equiv
    (H ⧸ (powMonoidHom n : H →* H).range)
    (nthPowerQuotientEquivOfMulEquiv G H n e).symm.toEquiv
 

def nthPowerProductQuotientHom (n : ℕ) :
    G × H →* (G ⧸ (powMonoidHom n : G →* G).range) × (H ⧸ (powMonoidHom n : H →* H).range) where
  toFun x :=
    (QuotientGroup.mk' ((powMonoidHom n : G →* G).range) x.1,
      QuotientGroup.mk' ((powMonoidHom n : H →* H).range) x.2)
  map_one' := rfl
  map_mul' _ _ := rfl
 
theorem nthPowerProductQuotientHom_surjective (n : ℕ) :
    Function.Surjective (nthPowerProductQuotientHom G H n) := by
  intro q
  rcases q with ⟨qG, qH⟩
  refine Quotient.inductionOn' qG ?_
  intro g
  refine Quotient.inductionOn' qH ?_
  intro h
  exact ⟨(g, h), rfl⟩
 
theorem nthPowerProductQuotientHom_ker (n : ℕ) :
    (nthPowerProductQuotientHom G H n).ker =
      (powMonoidHom n : (G × H) →* (G × H)).range := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    change
      (QuotientGroup.mk' ((powMonoidHom n : G →* G).range) x.1,
        QuotientGroup.mk' ((powMonoidHom n : H →* H).range) x.2) = 1 at hx
    have hxG :
        QuotientGroup.mk' ((powMonoidHom n : G →* G).range) x.1 = 1 :=
      congrArg Prod.fst hx
    have hxH :
        QuotientGroup.mk' ((powMonoidHom n : H →* H).range) x.2 = 1 :=
      congrArg Prod.snd hx
    have hxGmem : x.1 ∈ (powMonoidHom n : G →* G).range :=
      (QuotientGroup.eq_one_iff x.1).1 hxG
    have hxHmem : x.2 ∈ (powMonoidHom n : H →* H).range :=
      (QuotientGroup.eq_one_iff x.2).1 hxH
    rw [MonoidHom.mem_range] at hxGmem hxHmem ⊢
    rcases hxGmem with ⟨g, hg⟩
    rcases hxHmem with ⟨h, hh⟩
    refine ⟨(g, h), ?_⟩
    ext
    · change g ^ n = x.1
      simpa only [powMonoidHom_apply] using hg
    · change h ^ n = x.2
      simpa only [powMonoidHom_apply] using hh
  · intro hx
    rw [MonoidHom.mem_ker]
    rw [MonoidHom.mem_range] at hx
    rcases hx with ⟨y, rfl⟩
    apply Prod.ext
    · exact (QuotientGroup.eq_one_iff ((y.1) ^ n)).2
        ((MonoidHom.mem_range (G := G)).2 ⟨y.1, rfl⟩)
    · exact (QuotientGroup.eq_one_iff ((y.2) ^ n)).2
        ((MonoidHom.mem_range (G := H)).2 ⟨y.2, rfl⟩)
 

def nthPowerProductQuotientEquiv (n : ℕ) :
    (G × H) ⧸ (powMonoidHom n : (G × H) →* (G × H)).range ≃*
      (G ⧸ (powMonoidHom n : G →* G).range) × (H ⧸ (powMonoidHom n : H →* H).range) :=
  (QuotientGroup.quotientMulEquivOfEq
      (nthPowerProductQuotientHom_ker G H n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (nthPowerProductQuotientHom G H n)
      (nthPowerProductQuotientHom_surjective G H n))
 

noncomputable instance finite_powMonoidHom_rangeQuotient_prod (n : ℕ)
    [Finite (G ⧸ (powMonoidHom n : G →* G).range)]
    [Finite (H ⧸ (powMonoidHom n : H →* H).range)] :
    Finite ((G × H) ⧸ (powMonoidHom n : (G × H) →* (G × H)).range) :=
  Finite.of_equiv
    ((G ⧸ (powMonoidHom n : G →* G).range) × (H ⧸ (powMonoidHom n : H →* H).range))
    (nthPowerProductQuotientEquiv G H n).symm.toEquiv
 

theorem card_nthPowerProductQuotient (n : ℕ)
    [Finite (G ⧸ (powMonoidHom n : G →* G).range)]
    [Finite (H ⧸ (powMonoidHom n : H →* H).range)] :
    Nat.card ((G × H) ⧸ (powMonoidHom n : (G × H) →* (G × H)).range) =
      Nat.card (G ⧸ (powMonoidHom n : G →* G).range) *
        Nat.card (H ⧸ (powMonoidHom n : H →* H).range) := by
  rw [Nat.card_congr (nthPowerProductQuotientEquiv G H n).toEquiv,
    Nat.card_prod]
 

theorem powMonoidHom_range_multiplicativeInt_eq_integerMultipleSubgroup
    (n : ℕ) :
    (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range =
      integerMultipleSubgroup (n : ℤ) := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_range] at hx
    rcases hx with ⟨y, rfl⟩
    rw [mem_integerMultipleSubgroup_iff, powMonoidHom_apply, Int.toAdd_pow]
    exact ⟨y.toAdd, by ring⟩
  · intro hx
    rw [mem_integerMultipleSubgroup_iff] at hx
    rcases hx with ⟨k, hk⟩
    rw [MonoidHom.mem_range]
    refine ⟨Multiplicative.ofAdd k, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [powMonoidHom_apply, Int.toAdd_pow, toAdd_ofAdd, hk]
    ring
 
theorem finite_multiplicativeInt_nthPowerQuotient
    {n : ℕ} (hn : n ≠ 0) :
    Finite (Multiplicative ℤ ⧸ (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range) := by
  rw [powMonoidHom_range_multiplicativeInt_eq_integerMultipleSubgroup]
  have hnabs : (n : ℤ).natAbs ≠ 0 := by simpa using hn
  let : NeZero (n : ℤ).natAbs := ⟨hnabs⟩
  exact Finite.of_equiv
    (Multiplicative (ZMod (n : ℤ).natAbs))
    (valueModIntegerMultipleSubgroupEquivZMod (n : ℤ)).symm.toEquiv
 



theorem finite_nthPowerQuotient_of_mulEquiv_units_prod_int
    {n : ℕ} [NeZero n] (e : G ≃* U × Multiplicative ℤ)
    [Finite (U ⧸ (powMonoidHom n : U →* U).range)] :
    Finite (G ⧸ (powMonoidHom n : G →* G).range) := by
  let : Finite
      (Multiplicative ℤ ⧸
        (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range) :=
    finite_multiplicativeInt_nthPowerQuotient (NeZero.ne n)
  exact finite_nthPowerQuotient_of_mulEquiv
    G (U × Multiplicative ℤ) n e
 
theorem card_multiplicativeInt_nthPowerQuotient
    {n : ℕ} (hn : n ≠ 0)
    [Finite (Multiplicative ℤ ⧸ (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range)] :
    Nat.card
        (Multiplicative ℤ ⧸ (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range) = n := by
  rw [Nat.card_congr
    ((QuotientGroup.quotientMulEquivOfEq
      (powMonoidHom_range_multiplicativeInt_eq_integerMultipleSubgroup n)).trans
        (valueModIntegerMultipleSubgroupEquivZMod (n : ℤ))).toEquiv]
  rw [Nat.card_congr
    (Multiplicative.toAdd :
      Multiplicative (ZMod ((n : ℤ).natAbs)) ≃ ZMod ((n : ℤ).natAbs))]
  have hnabs : (n : ℤ).natAbs ≠ 0 := by simpa using hn
  let : NeZero (n : ℤ).natAbs := ⟨hnabs⟩
  have hcard : Nat.card (ZMod ((n : ℤ).natAbs)) = (n : ℤ).natAbs :=
    Nat.card_zmod ((n : ℤ).natAbs)
  simp at hcard ⊢
 

theorem card_nthPowerQuotient_eq_mul_of_mulEquiv_units_prod_int
    {n : ℕ} (hn : n ≠ 0) (e : G ≃* U × Multiplicative ℤ)
    [Finite (G ⧸ (powMonoidHom n : G →* G).range)]
    [Finite (U ⧸ (powMonoidHom n : U →* U).range)] :
    Nat.card (G ⧸ (powMonoidHom n : G →* G).range) =
      n * Nat.card (U ⧸ (powMonoidHom n : U →* U).range) := by
  let := finite_multiplicativeInt_nthPowerQuotient hn
  calc
    Nat.card (G ⧸ (powMonoidHom n : G →* G).range) =
        Nat.card ((U × Multiplicative ℤ) ⧸
          (powMonoidHom n : (U × Multiplicative ℤ) →* (U × Multiplicative ℤ)).range) := by
      rw [Nat.card_congr
        (nthPowerQuotientEquivOfMulEquiv G (U × Multiplicative ℤ) n e).toEquiv]
    _ =
        Nat.card (U ⧸ (powMonoidHom n : U →* U).range) *
          Nat.card (Multiplicative ℤ ⧸
            (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range) :=
      card_nthPowerProductQuotient U (Multiplicative ℤ) n
    _ = Nat.card (U ⧸ (powMonoidHom n : U →* U).range) * n := by
      rw [card_multiplicativeInt_nthPowerQuotient hn]
    _ = n * Nat.card (U ⧸ (powMonoidHom n : U →* U).range) := by
      rw [Nat.mul_comm]
end NthPowers
section AdditivePowers
universe uA uB uG
variable (A : Type uA) [AddCommGroup A]
section AdditiveProducts
variable (B : Type uB) [AddCommGroup B]
end AdditiveProducts
variable (G : Type uG) [CommGroup G]
end AdditivePowers
end LocalFieldTheory
end
end

namespace TunnellPowerBall
open Filter Topology Set
variable {K:Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
theorem linear_norm (n:ℕ) (hn:(n:K)≠0):
    ∀ᶠ x:K in 𝓝 1, ‖x^n-1‖=‖(n:K)‖*‖x-1‖ := by
  let s (x:K):=∑ i∈Finset.range n,x^i
  have hc:Continuous s:=by fun_prop
  have he:s 1=(n:K):=by simp [s]
  have hv:=hc.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (s 1) (norm_pos_iff.mpr hn))
  filter_upwards [hv] with x hx
  change dist (s x) (s 1)<‖(n:K)‖ at hx
  rw [he,dist_eq_norm] at hx
  have eq:‖s x‖=‖(n:K)‖:=by
    have hh:=IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x:=s x-(n:K)) (y:=(n:K)) hx.ne
    simpa only [sub_add_cancel,max_eq_right hx.le] using hh
  rw [←geom_sum_mul x n,norm_mul]
  exact congrArg (·*‖x-1‖) eq

theorem small_image (n:ℕ) (hn:(n:K)≠0) (c:ℝ) (hc:0<c) :
    ∃ r:K, 0<‖r‖ ∧ ‖r‖<c ∧
      (∀ x:K, ‖x-1‖≤‖r‖ → ‖x^n-1‖=‖(n:K)‖*‖x-1‖) ∧
      (fun x:K=>x^n) '' {x|‖x-1‖≤‖r‖}={y|‖y-1‖≤‖(n:K)‖*‖r‖} := by
  let f:K→K:=fun x=>x^n
  have df:HasStrictDerivAt f (n:K) 1:=by simpa [f] using hasStrictDerivAt_pow n (1:K)
  let B:Set K:={x|‖x^n-1‖=‖(n:K)‖*‖x-1‖}
  have hB:B∈𝓝 1:=linear_norm n hn
  have hF:f '' B∈𝓝 (1:K):=by
    have eq:Filter.map f (𝓝 1)=𝓝 (1:K):=by simpa [f] using df.map_nhds_eq hn
    rw [←eq];exact Filter.image_mem_map hB
  obtain ⟨a,ha,hba⟩:=Metric.mem_nhds_iff.mp hB
  obtain ⟨b,hb,hfb⟩:=Metric.mem_nhds_iff.mp hF
  have hp:=norm_pos_iff.mpr hn
  obtain ⟨r,hr,hr'⟩:=NormedField.exists_norm_lt K (lt_min hc (lt_min ha (div_pos hb hp)))
  have hrc:=lt_of_lt_of_le hr' (min_le_left _ _)
  have ht:=lt_of_lt_of_le hr' (min_le_right _ _)
  have hra:=lt_of_lt_of_le ht (min_le_left _ _)
  have hrb:=lt_of_lt_of_le ht (min_le_right _ _)
  have hlin(x:K)(hx:‖x-1‖≤‖r‖):x∈B:=hba (by simpa only [Metric.mem_ball,dist_eq_norm] using hx.trans_lt hra)
  refine ⟨r,hr,hrc,hlin,Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    change ‖x^n-1‖≤_
    rw [hlin x hx]
    exact mul_le_mul_of_nonneg_left hx hp.le
  · intro y hy
    change ‖y-1‖≤‖(n:K)‖*‖r‖ at hy
    have hyt:‖y-1‖<b:=hy.trans_lt (by simpa only [mul_comm] using (lt_div_iff₀ hp).mp hrb)
    obtain ⟨x,hx,hfx⟩:=hfb (by simpa only [Metric.mem_ball,dist_eq_norm] using hyt)
    refine ⟨x,?_,hfx⟩
    change ‖x-1‖≤‖r‖
    change x^n=y at hfx
    change ‖x^n-1‖=‖(n:K)‖*‖x-1‖ at hx
    rw [←hfx,hx] at hy
    exact (mul_le_mul_iff_right₀ hp).mp hy
end TunnellPowerBall

namespace TunnellIndexAtIdentity
theorem factor {G:Type} [CommGroup G] (f:G→*G) (H:Subgroup G)
    (he:H.map f≤H) (hk:Disjoint H f.ker) (hH:H.index≠0) :
    f.range.index=(H.map f).relIndex H * Nat.card f.ker := by
  have hq:H.relIndex (H⊔f.ker)=Nat.card f.ker:=by
    rw [Subgroup.relIndex_sup_left,←Subgroup.inf_relIndex_right,hk.eq_bot,Subgroup.relIndex_bot_left]
  have hN : (H⊔f.ker).index≠0:=fun h=>hH (by
    rw [←Subgroup.relIndex_mul_index (show H≤H⊔f.ker from le_sup_left),h,mul_zero])
  have hr:=Subgroup.relIndex_mul_index he
  rw [Subgroup.index_map,←Subgroup.relIndex_mul_index (show H≤H⊔f.ker from le_sup_left),hq] at hr
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hN) (by simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hr.symm)
end TunnellIndexAtIdentity

namespace TunnellUnitCongruence
open IsLocalRing
noncomputable section
variable {R:Type} [CommRing R] [IsDomain R]
def B (r:R):Subgroup Rˣ:=(Units.map (Ideal.Quotient.mk (Ideal.span {r})).toMonoidHom).ker
theorem mem (r:R) (x:Rˣ): x∈B r ↔ ∃ a:R,x.val=1+r*a := by
  change Units.map (Ideal.Quotient.mk (Ideal.span {r})).toMonoidHom x=1 ↔ _
  rw [Units.ext_iff]
  change Ideal.Quotient.mk (Ideal.span {r}) x.val=1 ↔ _
  rw [←map_one (Ideal.Quotient.mk (Ideal.span {r})),Ideal.Quotient.eq,Ideal.mem_span_singleton]
  constructor
  · rintro ⟨a,ha⟩;exact ⟨a,by linear_combination ha⟩
  · rintro ⟨a,ha⟩;exact ⟨a,by linear_combination ha⟩
theorem index (r n:R) (hr:r≠0) (hd:n∣r) (hu:∀ x:R,IsUnit (1+r*x)):
    (B (n*r)).relIndex (B r)=Nat.card (R⧸Ideal.span {n}) := by
  let c (x:B r):R:=Classical.choose ((mem r x.val).mp x.property)
  have hc(x:B r):x.val.val=1+r*c x:=Classical.choose_spec ((mem r x.val).mp x.property)
  have hmul(x y:B r): c (x*y)=c x+c y+r*c x*c y:=by
    apply mul_left_cancel₀ hr
    have h:(x.val.val*y.val.val)=1+r*c (x*y):=hc (x*y)
    rw [hc x,hc y] at h
    linear_combination -h
  have hone:c 1=0:=by
    apply mul_left_cancel₀ hr
    have h:1=1+r*c 1:=hc 1
    linear_combination -h
  let I:Ideal R:=Ideal.span {n}
  let F:B r→*Multiplicative (R⧸I):={
    toFun:=fun x=>Multiplicative.ofAdd (Ideal.Quotient.mk I (c x))
    map_one':=by change Ideal.Quotient.mk I (c 1)=0;rw [hone,map_zero]
    map_mul':=fun x y=>by
      change Ideal.Quotient.mk I (c (x*y))=Ideal.Quotient.mk I (c x)+Ideal.Quotient.mk I (c y)
      have hz:Ideal.Quotient.mk I r=0:=Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hd)
      simp [hmul,hz] }
  have sur:Function.Surjective F:=by
    intro y
    obtain ⟨a,ha⟩:=Ideal.Quotient.mk_surjective y.toAdd
    let u: Rˣ:=(hu a).unit
    let z:B r:=⟨u,(mem r u).mpr ⟨a,(hu a).unit_spec⟩⟩
    have eq:c z=a:=by
      apply mul_left_cancel₀ hr
      have q:=hc z
      change u.val=1+r*c z at q
      rw [(hu a).unit_spec] at q
      linear_combination -q
    refine ⟨z,?_⟩
    change Ideal.Quotient.mk I (c z)=y.toAdd
    rwa [eq]
  have ker:F.ker=(B (n*r)).subgroupOf (B r):=by
    ext x
    change Ideal.Quotient.mk I (c x)=0 ↔ x.val∈B (n*r)
    rw [Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_span_singleton,mem]
    constructor
    · rintro ⟨a,ha⟩
      exact ⟨a,by rw [hc,ha];ring⟩
    · rintro ⟨a,ha⟩
      refine ⟨a,mul_left_cancel₀ hr ?_⟩
      rw [hc] at ha
      linear_combination ha
  rw [Subgroup.relIndex,←ker,Subgroup.index_ker,F.range_eq_top.mpr sur,Nat.card_congr (Subgroup.topEquiv.toEquiv)]
  rfl
end
end TunnellUnitCongruence

namespace TunnellUnitPowerIndex
open TunnellUnitCongruence
open scoped Classical
noncomputable section
variable {K:Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (O:ValuationSubring K) (ball:∀ x:K,x∈O↔‖x‖≤1)
include ball
theorem unit_of_norm (x:K) (h:‖x‖=1) : ∃ a:Oˣ,(a.val:K)=x := by
  have hx:x≠0:=by rintro rfl;simpa using h
  have hxI:x⁻¹∈O:=(ball _).mpr (by simp [h])
  let u:Oˣ:={val:=⟨x,(ball _).mpr h.le⟩,inv:=⟨x⁻¹,hxI⟩,val_inv:=Subtype.ext (mul_inv_cancel₀ hx),inv_val:=Subtype.ext (inv_mul_cancel₀ hx)}
  exact ⟨u,rfl⟩
theorem unit_near (x:K) (h:‖x-1‖<1) : ∃ a:Oˣ,(a.val:K)=x := by
  apply unit_of_norm O ball
  have d:‖x-1‖<‖(1:K)‖:=by simpa using h
  simpa [max_eq_right h.le] using IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x:=x-1) (y:=(1:K)) d.ne
theorem mem_ball (r:O) (hr:(r:K)≠0) (u:Oˣ):
    u∈B r ↔ ‖(u.val:K)-1‖≤‖(r:K)‖ := by
  rw [mem]
  constructor
  · rintro ⟨a,ha⟩
    have h : (u.val:K)=1+(r:K)*(a:K):=congrArg Subtype.val ha
    rw [h,add_sub_cancel_left,norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) ((ball _).mp a.property))
  · intro h
    have hi:((u.val:K)-1)/(r:K) ∈ O:=(ball _).mpr (by rwa [norm_div,div_le_one (norm_pos_iff.mpr hr)])
    refine ⟨⟨_,hi⟩,Subtype.ext ?_⟩
    change (u.val:K)=1+r*(((u.val:K)-1)/(r:K))
    field_simp;ring

theorem calculate (n:ℕ) (hn:(n:K)≠0) (finiteQ:∀ r:O,r≠0→Finite (O⧸Ideal.span {r})) :
    (powMonoidHom n:Oˣ→*Oˣ).range.index=
      Nat.card (O⧸Ideal.span {(n:O)})*Nat.card (powMonoidHom n:Oˣ→*Oˣ).ker := by
  have hnorm:=norm_pos_iff.mpr hn
  obtain ⟨r,hr,hr',linear,image⟩:=TunnellPowerBall.small_image n hn (min 1 ‖(n:K)‖) (lt_min one_pos hnorm)
  let t:O:=⟨r,(ball r).mpr ((lt_min_iff.mp hr').1.le)⟩
  have rt:(t:K)≠0:=norm_pos_iff.mp hr
  have nt:((n:O)*(t:O):O)≠0:=mul_ne_zero (by intro h;exact hn (congrArg Subtype.val h)) (fun h=>rt (congrArg Subtype.val h))
  have ntr:(((n:O)*t:O):K)≠0:=fun h=>nt (Subtype.ext h)
  let f:Oˣ→*Oˣ:=powMonoidHom n
  let H:=B t
  have hd:(n:O)∣t:=by
    have hx:r/(n:K)∈O:=(ball _).mpr (by rw [norm_div,div_le_one hnorm];exact (lt_min_iff.mp hr').2.le)
    refine ⟨⟨_,hx⟩,Subtype.ext ?_⟩
    change r=(n:K)*(r/(n:K))
    field_simp
  have hu(a:O):IsUnit (1+t*a):=by
    have h:‖(1+r*(a:K))-1‖<1:=by
      rw [add_sub_cancel_left,norm_mul]
      exact (mul_le_of_le_one_right hr.le ((ball _).mp a.property)).trans_lt (lt_min_iff.mp hr').1
    obtain ⟨u,eq⟩:=unit_near O ball _ h
    exact ⟨u,Subtype.ext eq⟩
  have hmap:H.map f=B ((n:O)*t):=by
    ext u
    rw [mem_ball O ball _ ntr]
    have lim : ‖(((n:O)*t:O):K)‖=‖(n:K)‖*‖r‖:=norm_mul _ _
    rw [lim]
    constructor
    · rintro ⟨a,ha,rfl⟩
      have ha':‖(a.val:K)-1‖≤‖r‖:=(mem_ball O ball t rt a).mp ha
      change ‖(a.val:K)^n-1‖≤_
      rw [linear _ ha']
      exact mul_le_mul_of_nonneg_left ha' hnorm.le
    · intro h
      have hmem:(u.val:K)∈(fun x:K=>x^n) '' {x|‖x-1‖≤‖r‖}:=by rw [image];exact h
      obtain ⟨x,hx,hxpow⟩:=hmem
      obtain ⟨a,ha⟩:=unit_near O ball x (lt_of_le_of_lt hx (lt_min_iff.mp hr').1)
      exact ⟨a,(mem_ball O ball t rt a).mpr (ha ▸ hx),Units.ext (Subtype.ext (by change (a.val:K)^n=(u.val:K);rwa [ha]))⟩
  have he:H.map f≤H:=by
    rintro _ ⟨x,hx,rfl⟩
    exact H.pow_mem hx n
  have hk:Disjoint H f.ker:=by
    rw [Subgroup.disjoint_def]
    intro a ha hf
    have ha':‖(a.val:K)-1‖≤‖r‖:=(mem_ball O ball t rt a).mp ha
    have e:(a.val:K)^n=1:=congrArg (fun y:Oˣ=>(y.val:K)) hf
    have eq:=linear (a.val:K) ha'
    rw [e,sub_self,norm_zero] at eq
    exact Units.ext (Subtype.ext (sub_eq_zero.mp (norm_eq_zero.mp ((mul_eq_zero.mp eq.symm).resolve_left (ne_of_gt hnorm)))))
  haveI : Finite (O⧸Ideal.span {t}):=finiteQ t (fun h=>rt (congrArg Subtype.val h))
  have hH:H.index≠0:=by
    change (Units.map (Ideal.Quotient.mk (Ideal.span {t})).toMonoidHom).ker.index≠0
    rw [Subgroup.index_ker];exact Nat.card_pos.ne'
  rw [TunnellIndexAtIdentity.factor f H he hk hH,hmap]
  exact congrArg (·*Nat.card f.ker) (TunnellUnitCongruence.index t (n:O) (fun h=>rt (congrArg Subtype.val h)) hd hu)
end
end TunnellUnitPowerIndex

namespace TunnellCompletedPower
open NumberField IsDedekindDomain LocalFieldTheory IsLocalRing
open scoped NumberField Classical WithZero
noncomputable section
variable {K:Type} [Field K] [NumberField K]
abbrev V:=HeightOneSpectrum (𝓞 K)
abbrev W(v:V (K:=K)):=v.adicCompletion K
abbrev O(v:V (K:=K)):=v.adicCompletionIntegers K
theorem split (v:V (K:=K)) : Nonempty ((W v)ˣ ≃* (O v)ˣ × Multiplicative ℤ) := by
  obtain ⟨π,hπ⟩:=IsDiscreteValuationRing.exists_irreducible (O v)
  let z:(W v)ˣ:=Units.mk0 (π:W v) (fun h=>hπ.ne_zero (Subtype.ext h))
  let j:=Units.map (algebraMap (O v) (W v)).toMonoidHom
  let f:(O v)ˣ × Multiplicative ℤ →* (W v)ˣ:={
    toFun:=fun x=>j x.1*z^x.2.toAdd
    map_one':=by simp
    map_mul':=by rintro ⟨a,k⟩ ⟨b,l⟩;simp [zpow_add];ac_rfl }
  refine ⟨(MulEquiv.ofBijective f ⟨?_,?_⟩).symm⟩
  · apply (injective_iff_map_eq_one f).mpr
    rintro ⟨u,k⟩ hu
    have h : (u.val:W v)*(π:W v)^k.toAdd=1:=by
      have eq:=congrArg Units.val hu
      simpa [f,j,z,Units.val_zpow_eq_zpow_val] using eq
    have hπval: Valued.v (π:W v)=WithZero.exp (-1):=v.valued_irreducible_adicCompletionIntegers (K:=K) hπ
    have huval:Valued.v (u.val:W v)=1:=(Valuation.valuationSubring.integers (v:=(Valued.v:Valuation (W v) ℤᵐ⁰))).valuation_unit u
    have hv:=congrArg (Valued.v:Valuation (W v) ℤᵐ⁰) h
    simp only [map_mul,map_zpow₀,huval,map_one,one_mul] at hv
    have hneq:Valued.v (π:W v)≠1:=by rw [hπval];decide
    have hk:k=1:=Multiplicative.toAdd.injective ((zpow_eq_one_iff_right₀ zero_le hneq).mp hv)
    subst k
    have h₁:(u.val:W v)=1:=by simpa using h
    exact Prod.ext (Units.ext (Subtype.ext h₁)) rfl
  · intro x
    obtain ⟨n,u,h⟩:=IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ x.ne_zero
    refine ⟨(u,Multiplicative.ofAdd n),Units.ext ?_⟩
    simpa [f,j,z,Units.val_zpow_eq_zpow_val,Units.smul_def,Algebra.smul_def] using h.symm

theorem res (v:V (K:=K)): Nat.card (IsLocalRing.ResidueField (O v))=Ideal.absNorm v.asIdeal:=
  Nat.card_congr (v.residueFieldEquivAdicCompletionIntegers (K:=K)).toEquiv.symm
theorem quot (v:V (K:=K)) (n:ℕ) (hn:n≠0):
    Nat.card (O v ⧸ Ideal.span {(n:O v)})=Ideal.absNorm (v.maxPowDividing (Ideal.span {(n:𝓞 K)})):=by
  let a:𝓞 K:=n
  have ha:a≠0:=Nat.cast_ne_zero.mpr hn
  let k:ℕ:=(Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors
  have hv:Valued.v (n:W v)=WithZero.exp (-(k:ℤ)):=by
    have eq:=v.valuedAdicCompletion_eq_valuation (K:=K) a
    rw [v.valuation_of_algebraMap,v.intValuation_if_neg ha] at eq
    simpa [a] using eq
  have he:Ideal.span {(n:O v)}=IsLocalRing.maximalIdeal (O v)^k:=
    v.span_singleton_eq_maximalIdeal_pow hv
  rw [he,←Submodule.cardQuot_apply,cardQuot_pow_of_prime (P:=IsLocalRing.maximalIdeal (O v)) ((IsDiscreteValuationRing.maximalIdeal (O v)).ne_bot),Submodule.cardQuot_apply]
  change Nat.card (IsLocalRing.ResidueField (O v))^k=_
  rw [res]
  change Ideal.absNorm v.asIdeal^k=Ideal.absNorm (v.asIdeal^k)
  rw [map_pow]
theorem finiteQuot (v:V (K:=K)) (r:O v) (hr:r≠0):Finite (O v⧸Ideal.span {r}) := by
  obtain ⟨π,hπ⟩:=IsDiscreteValuationRing.exists_irreducible (O v)
  obtain ⟨i,u,eq⟩:=IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hπ
  have he:Ideal.span {r}=IsLocalRing.maximalIdeal (O v)^i:=by
    rw [eq,Ideal.span_singleton_eq_span_singleton.mpr (associated_unit_mul_left _ _ u.isUnit),←Ideal.span_singleton_pow,hπ.maximalIdeal_eq]
  apply Nat.finite_of_card_ne_zero
  rw [he,←Submodule.cardQuot_apply,cardQuot_pow_of_prime (P:=IsLocalRing.maximalIdeal (O v)) ((IsDiscreteValuationRing.maximalIdeal (O v)).ne_bot),Submodule.cardQuot_apply]
  change Nat.card (IsLocalRing.ResidueField (O v))^i≠0
  rw [res]
  exact pow_ne_zero _ (Ideal.absNorm_ne_zero_of_nonZeroDivisors ⟨v.asIdeal,mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩)
theorem result (n:ℕ) (hn:n.Prime) (hmu:(primitiveRoots n K).Nonempty) (v:V (K:=K)):
    (powMonoidHom n:(W v)ˣ→*(W v)ˣ).range.index=n*(n*Ideal.absNorm (v.maxPowDividing (Ideal.span {(n:𝓞 K)}))) := by
  letI : NeZero n:=⟨hn.ne_zero⟩
  letI : CharZero (W v):=charZero_of_injective_algebraMap (algebraMap K (W v)).injective
  letI : NontriviallyNormedField (W v):=Valued.toNontriviallyNormedField (W v) ℤᵐ⁰
  letI : IsUltrametricDist (W v):=by infer_instance
  have ball(x:W v): x∈O v ↔ ‖x‖≤1:=by
    change (Valued.v:Valuation (W v) ℤᵐ⁰) x≤1 ↔ _
    exact (Valued.toNormedField.norm_le_one_iff (x:=x)).symm
  obtain ⟨ζ,hζ⟩:=hmu
  have hroot: IsPrimitiveRoot (algebraMap K (W v) ζ) n:=((mem_primitiveRoots hn.pos).mp hζ).map_of_injective (algebraMap K (W v)).injective
  have hz:‖algebraMap K (W v) ζ‖=1:=by
    have h:=congrArg norm hroot.pow_eq_one
    rw [norm_pow,norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne_zero).mp h
  let t:O v:=⟨_,(ball _).mpr hz.le⟩
  have ht:IsPrimitiveRoot t n:=by
    exact IsPrimitiveRoot.of_map_of_injective (f:=(O v).subtype) (ζ:=t) hroot (O v).subtype_injective
  have hk:Nat.card (powMonoidHom n:(O v)ˣ→*(O v)ˣ).ker=n:=by
    rw [powMonoidHom_ker_units_eq_rootsOfUnity]
    exact ht.card_rootsOfUnity
  have co:=TunnellUnitPowerIndex.calculate (O v) ball n (Nat.cast_ne_zero.mpr hn.ne_zero) (finiteQuot v)
  rw [hk,quot v n hn.ne_zero,mul_comm] at co
  haveI :=finiteQuot v (n:O v) (fun eq=> (Nat.cast_ne_zero.mpr hn.ne_zero : (n:W v)≠0) (congrArg Subtype.val eq))
  haveI : Finite ((O v)ˣ ⧸(powMonoidHom n:(O v)ˣ→*(O v)ˣ).range):=
    Nat.finite_of_card_ne_zero (by rw [←Subgroup.index_eq_card,co]; rw [←quot v n hn.ne_zero];exact Nat.mul_ne_zero hn.ne_zero Nat.card_pos.ne')
  obtain ⟨e⟩:=split v
  letI : NeZero n:=⟨hn.ne_zero⟩
  haveI:=finite_nthPowerQuotient_of_mulEquiv_units_prod_int (W v)ˣ (O v)ˣ e (n:=n)
  change Nat.card ((W v)ˣ ⧸ (powMonoidHom n:(W v)ˣ→*(W v)ˣ).range)=_
  rw [card_nthPowerQuotient_eq_mul_of_mulEquiv_units_prod_int (W v)ˣ (O v)ˣ hn.ne_zero e]
  exact congrArg (n * ·) co
end
end TunnellCompletedPower




/-! The supported idèle quotient is the product of the local power-class quotients. -/
/- ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic -/
section
open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
 


abbrev FiniteIdeleGroupOf
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F] :=
  Πʳ v : HeightOneSpectrum R,
    [(v.adicCompletion F)ˣ, (v.adicCompletionIntegers F).units]
 
abbrev FiniteIdeleGroup :=
  FiniteIdeleGroupOf (𝓞 K) K
 
abbrev InfiniteIdeleGroup :=
  (NumberField.InfiniteAdeleRing K)ˣ
 
abbrev IdeleGroup :=
  InfiniteIdeleGroup K × FiniteIdeleGroup K
namespace FiniteIdeleGroup
variable {K}
 
def component (v : HeightOneSpectrum (𝓞 K)) :
    FiniteIdeleGroup K →* (v.adicCompletion K)ˣ where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
end FiniteIdeleGroup
namespace InfiniteIdeleGroup
variable {K}
 
def component (v : InfinitePlace K) :
    InfiniteIdeleGroup K →* v.Completionˣ :=
  (Pi.evalMonoidHom (fun w : InfinitePlace K ↦ w.Completionˣ) v).comp
    ContinuousMulEquiv.piUnits.toMonoidHom
end InfiniteIdeleGroup
namespace IdeleGroup
variable {K}
 

def finiteEquivFiniteAdeleUnitsOf
  (R : Type*) [CommRing R] [IsDedekindDomain R]
    (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F] :
    FiniteIdeleGroupOf R F ≃*
    (IsDedekindDomain.FiniteAdeleRing R F)ˣ :=
  (RestrictedProduct.unitsEquiv
    (ι := HeightOneSpectrum R)
    (S := fun v : HeightOneSpectrum R ↦ ValuationSubring (v.adicCompletion F))
    (B := fun v : HeightOneSpectrum R ↦ v.adicCompletionIntegers F)
    (𝓕 := Filter.cofinite)
    (fun v : HeightOneSpectrum R ↦ v.adicCompletion F)).symm
 
def infiniteComponent (v : InfinitePlace K) :
    IdeleGroup K →* v.Completionˣ :=
  (InfiniteIdeleGroup.component v).comp (MonoidHom.fst _ _)
 
def finiteComponent (v : HeightOneSpectrum (𝓞 K)) :
    IdeleGroup K →* (v.adicCompletion K)ˣ :=
  (FiniteIdeleGroup.component v).comp (MonoidHom.snd _ _)
 


def finiteEquivFiniteAdeleUnits :
    FiniteIdeleGroup K ≃*
      (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ :=
  finiteEquivFiniteAdeleUnitsOf (𝓞 K) K
 




def equivAdeleRingUnits :
    IdeleGroup K ≃* (NumberField.AdeleRing (𝓞 K) K)ˣ :=
  ((MulEquiv.refl (InfiniteIdeleGroup K)).prodCongr
      (finiteEquivFiniteAdeleUnits (K := K))).trans
    MulEquiv.prodUnits.symm
end IdeleGroup
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.Idele.SPlaces -/
section
open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace FiniteIdeleGroup
 
def supportedAt (S : Set (HeightOneSpectrum (𝓞 K))) :
    Subgroup (FiniteIdeleGroup K) where
  carrier := {a | ∀ v, v ∉ S →
    a v ∈ (v.adicCompletionIntegers K).units}
  one_mem' _ _ := Submonoid.one_mem _
  mul_mem' ha hb v hv := Submonoid.mul_mem _
    (ha v hv) (hb v hv)
  inv_mem' ha v hv := Subgroup.inv_mem _
    (ha v hv)
end FiniteIdeleGroup
namespace IdeleGroup
 

def supportedAt (S : Set (HeightOneSpectrum (𝓞 K))) :
    Subgroup (IdeleGroup K) :=
  Subgroup.comap (MonoidHom.snd _ _)
    (FiniteIdeleGroup.supportedAt S)
@[simp]
theorem mem_supportedAt_iff
    (S : Set (HeightOneSpectrum (𝓞 K)))
    (a : IdeleGroup K) :
    a ∈ supportedAt (K := K) S ↔
      ∀ v, v ∉ S →
        a.2 v ∈ (v.adicCompletionIntegers K).units :=
  Iff.rfl
end IdeleGroup
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.RayClass.Basic -/
section
open scoped NumberField
open NumberField IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace RayClass
 

def infinitePositiveSubgroup (v : InfinitePlace K) :
    Subgroup v.Completionˣ where
  carrier := {x | ∀ hv : v.IsReal,
    0 < NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
      hv (x : v.Completion)}
  one_mem' hv := by simp
  mul_mem' {x y} hx hy hv := by
    change 0 <
      NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
        hv ((x : v.Completion) * (y : v.Completion))
    rw [map_mul]
    exact mul_pos (hx hv) (hy hv)
  inv_mem' {x} hx hv := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact inv_pos.mpr (hx hv)
omit [NumberField K] in
@[simp]
theorem mem_infinitePositiveSubgroup_iff
    (v : InfinitePlace K) (x : v.Completionˣ) :
    x ∈ infinitePositiveSubgroup v ↔
      ∀ hv : v.IsReal,
        0 < NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
          hv (x : v.Completion) :=
  Iff.rfl
end RayClass
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.RayClass.Approximation -/
section
open scoped NumberField Classical
open NumberField IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace IdeleGroup
 
def finiteIdeleOfFinset
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ v : ↥S, (v.1.adicCompletion K)ˣ) :
    FiniteIdeleGroup K := by
  let f : ∀ v : HeightOneSpectrum (𝓞 K),
      (v.adicCompletion K)ˣ :=
    fun v => if hv : v ∈ S then a ⟨v, hv⟩ else 1
  refine ⟨f, ?_⟩
  have haway :
      ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        v ∉ S := by
    rw [Filter.eventually_cofinite]
    convert S.finite_toSet using 1
    ext v
    simp
  filter_upwards [haway] with v hv
  change f v ∈ (v.adicCompletionIntegers K).units
  simp [f, hv]
@[simp]
theorem finiteIdeleOfFinset_apply_mem
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ v : ↥S, (v.1.adicCompletion K)ˣ)
    (v : ↥S) :
    finiteIdeleOfFinset S a v.1 = a v := by
  classical
  change (if hv : v.1 ∈ S then a ⟨v.1, hv⟩ else 1) = a v
  exact dif_pos v.2
@[simp]
theorem finiteIdeleOfFinset_apply_notMem
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ v : ↥S, (v.1.adicCompletion K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    finiteIdeleOfFinset S a v = 1 := by
  classical
  change (if hmem : v ∈ S then a ⟨v, hmem⟩ else 1) =
    (1 : (v.adicCompletion K)ˣ)
  exact dif_neg hv
end IdeleGroup
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.InfinitePlaces -/
section
open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

variable {K : Type} [Field K] [NumberField K]
omit [NumberField K] in
 


theorem exists_infinitePositiveSubgroup_nthRoot
    (v : InfinitePlace K)
    (n : ℕ) (hn : 0 < n)
    (x : v.Completionˣ)
    (hx : x ∈ RayClass.infinitePositiveSubgroup v) :
    ∃ y : v.Completionˣ, y ^ n = x := by
  by_cases hv : v.IsReal
  · let e : v.Completion ≃+* ℝ :=
      InfinitePlace.Completion.ringEquivRealOfIsReal hv
    let eu : v.Completionˣ ≃* ℝˣ :=
      Units.mapEquiv e.toMulEquiv
    have hxpos : 0 < ((eu x : ℝˣ) : ℝ) := by
      exact
        ((RayClass.mem_infinitePositiveSubgroup_iff v x).mp hx) hv
    let yr : ℝ :=
      ((eu x : ℝˣ) : ℝ) ^ ((n : ℝ)⁻¹)
    have hyrpow :
        yr ^ n = ((eu x : ℝˣ) : ℝ) := by
      exact Real.rpow_inv_natCast_pow hxpos.le hn.ne'
    have hyrne : yr ≠ 0 := by
      intro hyr
      rw [hyr, zero_pow hn.ne'] at hyrpow
      exact (eu x).ne_zero hyrpow.symm
    let yu : ℝˣ := Units.mk0 yr hyrne
    refine ⟨eu.symm yu, ?_⟩
    apply eu.injective
    simp only [map_pow, eu.apply_symm_apply]
    apply Units.ext
    exact hyrpow
  · have hvc : v.IsComplex :=
      InfinitePlace.not_isReal_iff_isComplex.mp hv
    let e : v.Completion ≃+* ℂ :=
      InfinitePlace.Completion.ringEquivComplexOfIsComplex hvc
    let eu : v.Completionˣ ≃* ℂˣ :=
      Units.mapEquiv e.toMulEquiv
    obtain ⟨z, hz⟩ :=
      IsAlgClosed.exists_pow_nat_eq
        ((eu x : ℂˣ) : ℂ) hn
    have hz0 : z ≠ 0 := by
      intro hzero
      rw [hzero, zero_pow hn.ne'] at hz
      exact (eu x).ne_zero hz.symm
    let zu : ℂˣ := Units.mk0 z hz0
    refine ⟨eu.symm zu, ?_⟩
    apply eu.injective
    simp only [map_pow, eu.apply_symm_apply]
    apply Units.ext
    exact hz
variable {L : Type} [Field L] [Algebra K L]
    [FiniteDimensional K L]
end
end

/- ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdelePowerLocalUnitSubgroup -/
section
open scoped NumberField Classical NNReal IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section
namespace GlobalClassFieldTheory.ClassFieldAxiom
variable {K : Type*} [Field K] [NumberField K]
 

def idelePowerLocalUnitSubgroup
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (IdeleGroup K) :=
  (⨅ w : InfinitePlace K,
      ((powMonoidHom (n : ℕ) :
        w.Completionˣ →* w.Completionˣ).range).comap
        (IdeleGroup.infiniteComponent w)) ⊓
    (⨅ v : HeightOneSpectrum (𝓞 K),
      ⨅ (_ : v ∈ S),
        (powMonoidHom (n : ℕ) :
          (v.adicCompletion K)ˣ →*
            (v.adicCompletion K)ˣ).range.comap
          (IdeleGroup.finiteComponent v)) ⊓
    (⨅ v : HeightOneSpectrum (𝓞 K),
      ⨅ (_ : v ∉ S ∪ T),
        (v.adicCompletionIntegers K).units.comap
          (IdeleGroup.finiteComponent v))
 
theorem mem_idelePowerLocalUnitSubgroup_iff
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (a : IdeleGroup K) :
    a ∈ idelePowerLocalUnitSubgroup (K := K) n S T ↔
      (∀ w : InfinitePlace K,
        IdeleGroup.infiniteComponent w a ∈
          (powMonoidHom (n : ℕ) :
            w.Completionˣ →* w.Completionˣ).range) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∈ S →
        IdeleGroup.finiteComponent v a ∈
          (powMonoidHom (n : ℕ) :
            (v.adicCompletion K)ˣ →*
              (v.adicCompletion K)ˣ).range) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S ∪ T →
        IdeleGroup.finiteComponent v a ∈
          (v.adicCompletionIntegers K).units) := by
  simp only [idelePowerLocalUnitSubgroup, Subgroup.mem_inf,
    Subgroup.mem_iInf, Subgroup.mem_comap, and_assoc]
end GlobalClassFieldTheory.ClassFieldAxiom
end
end

/- ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.ArchimedeanPowerIndex -/
section
open scoped NumberField Classical NNReal ValuativeRel TensorProduct
open NumberField IsDedekindDomain

noncomputable section
namespace GlobalClassFieldTheory.ClassFieldAxiom
variable {K : Type} [Field K] [NumberField K]
omit [NumberField K] in
 

theorem nthPowerSubgroup_le_infinitePositiveSubgroup
    (n : ℕ+)
    (w : InfinitePlace K)
    (harch : Even (n : ℕ) ∨ ¬ w.IsReal) :
    (powMonoidHom (n : ℕ) :
        w.Completionˣ →* w.Completionˣ).range ≤
      RayClass.infinitePositiveSubgroup w := by
  intro x hx
  obtain ⟨y, hy⟩ :=
    (MonoidHom.mem_range
      (G := w.Completionˣ)).mp hx
  rw [powMonoidHom_apply] at hy
  subst x
  rw [RayClass.mem_infinitePositiveSubgroup_iff]
  intro hw
  rcases harch with hnEven | hwNotReal
  · rcases hnEven with ⟨m, hm⟩
    let emb :=
      NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
    have hyne : emb (y : w.Completion) ≠ 0 := by
      intro hzero
      apply y.ne_zero
      apply emb.injective
      simp at hzero
    change 0 < emb (((y ^ (n : ℕ) : w.Completionˣ) : w.Completion))
    rw [Units.val_pow_eq_pow_val, map_pow, hm, pow_add, ← pow_two]
    exact sq_pos_of_ne_zero (pow_ne_zero m hyne)
  · exact False.elim (hwNotReal hw)
 
def realInfinitePlaceSignHom
    (w : InfinitePlace K)
    (hw : w.IsReal) :
    w.Completionˣ →* SignTypeˣ :=
  (Units.map
      (signHom : ℝ →*₀ SignType).toMonoidHom).comp
    (Units.mapEquiv
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
        hw).toMulEquiv).toMonoidHom
omit [NumberField K] in
 

theorem realInfinitePlaceSignHom_ker
    (w : InfinitePlace K)
    (hw : w.IsReal) :
    (realInfinitePlaceSignHom w hw).ker =
      RayClass.infinitePositiveSubgroup w := by
  ext x
  change
    realInfinitePlaceSignHom w hw x = 1 ↔
      x ∈ RayClass.infinitePositiveSubgroup w
  rw [RayClass.mem_infinitePositiveSubgroup_iff]
  constructor
  · intro hx hw'
    have hxval := congrArg Units.val hx
    have hxsign :
        SignType.sign
          (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
            hw (x : w.Completion)) =
          1 := by
      simpa [realInfinitePlaceSignHom] using hxval
    have hproof : hw' = hw := Subsingleton.elim _ _
    subst hproof
    exact sign_eq_one_iff.mp hxsign
  · intro hx
    have hxsign :
        SignType.sign
            (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
              hw (x : w.Completion)) =
          1 :=
      sign_eq_one_iff.mpr (hx hw)
    apply Units.ext
    simpa [realInfinitePlaceSignHom] using hxsign
omit [NumberField K] in
 
theorem realInfinitePlaceSignHom_surjective
    (w : InfinitePlace K)
    (hw : w.IsReal) :
    Function.Surjective (realInfinitePlaceSignHom w hw) := by
  let eu : w.Completionˣ ≃* ℝˣ :=
    Units.mapEquiv
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
        hw).toMulEquiv
  intro s
  cases hs : (s : SignType) with
  | zero =>
      exact False.elim (s.ne_zero hs)
  | neg =>
      refine ⟨eu.symm (-1), ?_⟩
      apply Units.ext
      simp [realInfinitePlaceSignHom, eu, hs]
  | pos =>
      refine ⟨eu.symm 1, ?_⟩
      apply Units.ext
      simp [realInfinitePlaceSignHom, eu, hs]
 

noncomputable def realInfinitePositiveQuotientEquivSign
    (w : InfinitePlace K)
    (hw : w.IsReal) :
    w.Completionˣ ⧸ RayClass.infinitePositiveSubgroup w ≃*
      SignTypeˣ := by
  rw [← realInfinitePlaceSignHom_ker w hw]
  exact
    QuotientGroup.quotientKerEquivOfSurjective
      (realInfinitePlaceSignHom w hw)
      (realInfinitePlaceSignHom_surjective w hw)
omit [NumberField K] in
 
theorem card_realInfinitePositiveQuotient
    (w : InfinitePlace K)
    (hw : w.IsReal) :
    Nat.card
        (w.Completionˣ ⧸
          RayClass.infinitePositiveSubgroup w) =
      2 := by
  calc
    Nat.card
        (w.Completionˣ ⧸
          RayClass.infinitePositiveSubgroup w) =
        Nat.card SignTypeˣ :=
      Nat.card_congr
        (realInfinitePositiveQuotientEquivSign w hw).toEquiv
    _ = 2 := by
      rw [Nat.card_eq_fintype_card]
      decide
omit [NumberField K] in
 

theorem nthPowerSubgroup_eq_infinitePositiveSubgroup
    (n : ℕ+)
    (w : InfinitePlace K)
    (harch : Even (n : ℕ) ∨ ¬ w.IsReal) :
    (powMonoidHom (n : ℕ) :
        w.Completionˣ →* w.Completionˣ).range =
      RayClass.infinitePositiveSubgroup w := by
  apply le_antisymm
  · exact
      nthPowerSubgroup_le_infinitePositiveSubgroup
        n w harch
  · intro x hx
    obtain ⟨y, hy⟩ :=
      _root_.exists_infinitePositiveSubgroup_nthRoot
        w (n : ℕ) n.pos x hx
    exact
      (MonoidHom.mem_range
        (G := w.Completionˣ)).mpr ⟨y, by
          rw [powMonoidHom_apply]
          exact hy⟩
omit [NumberField K] in
 
theorem nthPowerSubgroup_eq_top_of_real_odd
    (n : ℕ+)
    (w : InfinitePlace K)
    (hw : w.IsReal)
    (hn : Odd (n : ℕ)) :
    (powMonoidHom (n : ℕ) :
        w.Completionˣ →* w.Completionˣ).range =
      ⊤ := by
  apply top_unique
  intro x hx
  apply
    (MonoidHom.mem_range
      (G := w.Completionˣ)).mpr
  let emb :=
    NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
  have hx0 : emb (x : w.Completion) ≠ 0 := by
    intro hzero
    apply x.ne_zero
    simp at hzero
  by_cases hxpos : 0 < emb (x : w.Completion)
  · have hxPositive :
        x ∈ RayClass.infinitePositiveSubgroup w := by
      rw [RayClass.mem_infinitePositiveSubgroup_iff]
      intro hw'
      have hproof : hw' = hw := Subsingleton.elim _ _
      subst hproof
      exact hxpos
    obtain ⟨y, hy⟩ :=
      _root_.exists_infinitePositiveSubgroup_nthRoot
        w (n : ℕ) n.pos x hxPositive
    exact ⟨y, by
      rw [powMonoidHom_apply]
      exact hy⟩
  · have hxneg : emb (x : w.Completion) < 0 :=
      lt_of_le_of_ne (le_of_not_gt hxpos) hx0
    have hnegPositive :
        -x ∈ RayClass.infinitePositiveSubgroup w := by
      rw [RayClass.mem_infinitePositiveSubgroup_iff]
      intro hw'
      have hproof : hw' = hw := Subsingleton.elim _ _
      subst hproof
      change 0 < emb ((-x : w.Completionˣ) : w.Completion)
      simp [hxneg]
    obtain ⟨y, hy⟩ :=
      _root_.exists_infinitePositiveSubgroup_nthRoot
        w (n : ℕ) n.pos (-x) hnegPositive
    refine ⟨-y, ?_⟩
    rw [powMonoidHom_apply, hn.neg_pow, hy]
    simp
omit [NumberField K] in
 

theorem card_infinitePlace_nthPowerQuotient
    (n : ℕ+)
    (w : InfinitePlace K) :
    Nat.card
        (w.Completionˣ ⧸
          (powMonoidHom (n : ℕ) :
            w.Completionˣ →* w.Completionˣ).range) =
      if w.IsReal ∧ Even (n : ℕ) then 2 else 1 := by
  classical
  by_cases hw : w.IsReal
  · by_cases hn : Even (n : ℕ)
    · rw [
        nthPowerSubgroup_eq_infinitePositiveSubgroup
          n w (Or.inl hn)]
      simpa [hw, hn] using
        card_realInfinitePositiveQuotient w hw
    · have hodd : Odd (n : ℕ) :=
        (Nat.even_or_odd (n : ℕ)).resolve_left hn
      rw [nthPowerSubgroup_eq_top_of_real_odd n w hw hodd]
      let :
          Subsingleton
            (w.Completionˣ ⧸ (⊤ : Subgroup w.Completionˣ)) :=
        QuotientGroup.subsingleton_quotient_top
      simp [hw, hn]
  · have hpower :
        (powMonoidHom (n : ℕ) :
            w.Completionˣ →* w.Completionˣ).range =
          RayClass.infinitePositiveSubgroup w :=
      nthPowerSubgroup_eq_infinitePositiveSubgroup
        n w (Or.inr hw)
    have hpositive :
        RayClass.infinitePositiveSubgroup w = ⊤ := by
      ext x
      simp [RayClass.mem_infinitePositiveSubgroup_iff, hw]
    rw [hpower, hpositive]
    let :
        Subsingleton
          (w.Completionˣ ⧸ (⊤ : Subgroup w.Completionˣ)) :=
      QuotientGroup.subsingleton_quotient_top
    simp [hw]
end GlobalClassFieldTheory.ClassFieldAxiom
end
end

/- ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SupportedIdelePowerLocalUnitQuotient -/
section
open scoped NumberField Classical NNReal IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section
namespace GlobalClassFieldTheory.ClassFieldAxiom
variable {K : Type*} [Field K] [NumberField K]
private noncomputable def quotientEquivOfSurjectiveWithKernel
    {G H : Type*} [Group G] [Group H]
    (f : G →* H)
    (N : Subgroup G) [N.Normal]
    (hf : Function.Surjective f)
    (hker : f.ker = N) :
    G ⧸ N ≃* H :=
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
 

def supportedIdelePowerLocalUnitSubgroup
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup
      (IdeleGroup.supportedAt
        (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K)))) :=
  (idelePowerLocalUnitSubgroup (K := K) n S T).comap
    (IdeleGroup.supportedAt
      (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K)))).subtype
 


def supportedIdelePowerClassMap
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    IdeleGroup.supportedAt
        (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) →*
      ((
        ∀ w : InfinitePlace K,
          w.Completionˣ ⧸
            (powMonoidHom (n : ℕ) :
              w.Completionˣ →* w.Completionˣ).range) ×
        (∀ v : ↥S,
          (v.1.adicCompletion K)ˣ ⧸
            (powMonoidHom (n : ℕ) :
              (v.1.adicCompletion K)ˣ →*
                (v.1.adicCompletion K)ˣ).range)) where
  toFun a :=
    (fun w =>
      QuotientGroup.mk'
        (powMonoidHom (n : ℕ) :
          w.Completionˣ →* w.Completionˣ).range
        (IdeleGroup.infiniteComponent w a.1),
     fun v =>
      QuotientGroup.mk'
        (powMonoidHom (n : ℕ) :
          (v.1.adicCompletion K)ˣ →*
            (v.1.adicCompletion K)ˣ).range
        (IdeleGroup.finiteComponent v.1 a.1))
  map_one' := by
    apply Prod.ext
    · funext w
      apply (QuotientGroup.eq_one_iff _).mpr
      apply
        (MonoidHom.mem_range
          (G := w.Completionˣ)).mpr
      refine ⟨1, ?_⟩
      rw [powMonoidHom_apply, one_pow]
      exact (IdeleGroup.infiniteComponent w).map_one.symm
    · funext v
      simp
  map_mul' a b := by
    apply Prod.ext
    · funext w
      change
        QuotientGroup.mk'
            (powMonoidHom (n : ℕ) :
              w.Completionˣ →* w.Completionˣ).range
            (IdeleGroup.infiniteComponent w (a.1 * b.1)) =
          QuotientGroup.mk'
              (powMonoidHom (n : ℕ) :
                w.Completionˣ →* w.Completionˣ).range
              (IdeleGroup.infiniteComponent w a.1) *
            QuotientGroup.mk'
              (powMonoidHom (n : ℕ) :
                w.Completionˣ →* w.Completionˣ).range
              (IdeleGroup.infiniteComponent w b.1)
      rw [map_mul, map_mul]
    · funext v
      simp
 

theorem supportedIdelePowerClassMap_ker
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    (supportedIdelePowerClassMap (K := K) n S T).ker =
      supportedIdelePowerLocalUnitSubgroup (K := K) n S T := by
  ext a
  rw [MonoidHom.mem_ker]
  constructor
  · intro ha
    rw [supportedIdelePowerLocalUnitSubgroup,
      Subgroup.mem_comap,
      mem_idelePowerLocalUnitSubgroup_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro w
      have hw := congrArg (fun q => q.1 w) ha
      rw [Prod.fst_one, Pi.one_apply] at hw
      exact (QuotientGroup.eq_one_iff _).mp hw
    · intro v hv
      let vS : ↥S := ⟨v, hv⟩
      have hvq := congrArg (fun q => q.2 vS) ha
      rw [Prod.snd_one, Pi.one_apply] at hvq
      exact (QuotientGroup.eq_one_iff _).mp hvq
    · intro v hv
      have hv' :
          v ∉ (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) := by
        simpa using hv
      exact
        (IdeleGroup.mem_supportedAt_iff
          (K := K)
          (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) a.1).mp
            a.2 v hv'
  · intro ha
    rw [supportedIdelePowerLocalUnitSubgroup,
      Subgroup.mem_comap,
      mem_idelePowerLocalUnitSubgroup_iff] at ha
    apply Prod.ext
    · funext w
      exact (QuotientGroup.eq_one_iff _).mpr (ha.1 w)
    · funext v
      exact (QuotientGroup.eq_one_iff _).mpr
        (ha.2.1 v.1 v.2)
 


theorem supportedIdelePowerClassMap_surjective
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective
      (supportedIdelePowerClassMap (K := K) n S T) := by
  intro q
  choose aInf hInf using fun w : InfinitePlace K =>
    QuotientGroup.mk_surjective (q.1 w)
  choose aS hS using fun v : ↥S =>
    QuotientGroup.mk_surjective (q.2 v)
  let alpha : IdeleGroup K :=
    (ContinuousMulEquiv.piUnits.symm aInf,
      IdeleGroup.finiteIdeleOfFinset S aS)
  have hAlpha :
      alpha ∈
        IdeleGroup.supportedAt
          (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) := by
    rw [IdeleGroup.mem_supportedAt_iff]
    intro v hv
    have hvS : v ∉ S := by
      intro hvS
      apply hv
      exact Or.inl hvS
    change
      IdeleGroup.finiteIdeleOfFinset S aS v ∈
        (v.adicCompletionIntegers K).units
    rw [IdeleGroup.finiteIdeleOfFinset_apply_notMem S aS v hvS]
    exact Subgroup.one_mem _
  refine ⟨⟨alpha, hAlpha⟩, ?_⟩
  apply Prod.ext
  · funext w
    calc
      QuotientGroup.mk'
          (powMonoidHom (n : ℕ) :
            w.Completionˣ →* w.Completionˣ).range
          (IdeleGroup.infiniteComponent w alpha) =
          QuotientGroup.mk'
            (powMonoidHom (n : ℕ) :
              w.Completionˣ →* w.Completionˣ).range
            (aInf w) := by
        apply congrArg
        change
          ContinuousMulEquiv.piUnits
              (ContinuousMulEquiv.piUnits.symm aInf) w =
            aInf w
        exact congrFun
          (ContinuousMulEquiv.piUnits.apply_symm_apply aInf) w
      _ = q.1 w := hInf w
  · funext v
    calc
      QuotientGroup.mk'
          (powMonoidHom (n : ℕ) :
            (v.1.adicCompletion K)ˣ →*
              (v.1.adicCompletion K)ˣ).range
          (IdeleGroup.finiteComponent v.1 alpha) =
          QuotientGroup.mk'
            (powMonoidHom (n : ℕ) :
              (v.1.adicCompletion K)ˣ →*
                (v.1.adicCompletion K)ˣ).range
            (aS v) := by
        apply congrArg
        exact IdeleGroup.finiteIdeleOfFinset_apply_mem S aS v
      _ = q.2 v := hS v
 



noncomputable def supportedIdeleQuotientEquivLocalPowerClasses
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    IdeleGroup.supportedAt
          (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) ⧸
        supportedIdelePowerLocalUnitSubgroup (K := K) n S T ≃*
      ((
        ∀ w : InfinitePlace K,
          w.Completionˣ ⧸
            (powMonoidHom (n : ℕ) :
              w.Completionˣ →* w.Completionˣ).range) ×
        (∀ v : ↥S,
          (v.1.adicCompletion K)ˣ ⧸
            (powMonoidHom (n : ℕ) :
              (v.1.adicCompletion K)ˣ →*
                (v.1.adicCompletion K)ˣ).range)) :=
  quotientEquivOfSurjectiveWithKernel
    (H :=
      ((
        ∀ w : InfinitePlace K,
          w.Completionˣ ⧸
            (powMonoidHom (n : ℕ) :
              w.Completionˣ →* w.Completionˣ).range) ×
        (∀ v : ↥S,
          (v.1.adicCompletion K)ˣ ⧸
            (powMonoidHom (n : ℕ) :
              (v.1.adicCompletion K)ˣ →*
                (v.1.adicCompletion K)ˣ).range)))
    (supportedIdelePowerClassMap (K := K) n S T)
    (supportedIdelePowerLocalUnitSubgroup (K := K) n S T)
    (supportedIdelePowerClassMap_surjective (K := K) n S T)
    (supportedIdelePowerClassMap_ker (K := K) n S T)
 


theorem card_supportedIdeleQuotient_eq_localPowerClasses
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Nat.card
        (IdeleGroup.supportedAt
              (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) ⧸
          supportedIdelePowerLocalUnitSubgroup (K := K) n S T) =
      Nat.card
        ((
          ∀ w : InfinitePlace K,
            w.Completionˣ ⧸
              (powMonoidHom (n : ℕ) :
                w.Completionˣ →* w.Completionˣ).range) ×
          (∀ v : ↥S,
            (v.1.adicCompletion K)ˣ ⧸
              (powMonoidHom (n : ℕ) :
                (v.1.adicCompletion K)ˣ →*
                  (v.1.adicCompletion K)ˣ).range)) :=
  Nat.card_congr
    (supportedIdeleQuotientEquivLocalPowerClasses
      (K := K) n S T).toEquiv
end GlobalClassFieldTheory.ClassFieldAxiom
end
end

namespace TunnellKummerSupportGroups
open NumberField IsDedekindDomain IdeleGroup GlobalClassFieldTheory.ClassFieldAxiom
open scoped NumberField Classical
noncomputable section
variable (K:Type) [Field K] [NumberField K]
abbrev V:=HeightOneSpectrum (𝓞 K)
abbrev A:=AdeleRing (𝓞 K) K
def U (n:ℕ) (S T : Finset (V K)):Subgroup (A K)ˣ:=Subgroup.closure {a:(A K)ˣ |
    (∀ w:InfinitePlace K,∃ y:w.Completion,y^n=a.val.1 w) ∧
    (∀ v∈S,∃ y:v.adicCompletion K,y^n=a.val.2 v) ∧
    ∀ v:V K,v∉S∪T → a.val.2 v∈v.adicCompletionIntegers K ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers K}
def J(F:Finset (V K)):Subgroup (A K)ˣ:=Subgroup.closure {a:(A K)ˣ | ∀ v:V K,v∉F → a.val.2 v∈v.adicCompletionIntegers K ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers K}
abbrev e:=equivAdeleRingUnits (K:=K)
theorem units_mem {W:Type} [Field W] (O:ValuationSubring W) (x:Wˣ):
     x∈O.units ↔ x.val∈O ∧ (x⁻¹).val∈O:=by
   exact Submonoid.mem_units_iff _ _
theorem powers_mem {W:Type} [Field W] (n:ℕ+) (x:Wˣ):
     x∈(powMonoidHom (n:ℕ):Wˣ→*Wˣ).range ↔ ∃ y:W,y^(n:ℕ)=x.val:=by
   constructor
   · rintro ⟨u,rfl⟩;exact ⟨u.val,rfl⟩
   · rintro ⟨y,hy⟩
     have h:y≠0:=by rintro rfl;rw [zero_pow n.ne_zero] at hy;exact x.ne_zero hy.symm
     exact ⟨Units.mk0 y h,Units.ext hy⟩
theorem closure_of_carrier {G:Type} [CommGroup G] (H:Subgroup G) (s:Set G)
    (h:∀ a, a∈s ↔ a∈H) : Subgroup.closure s=H := by
  have eq:s=(H:Set G):=Set.ext h
  rw [eq,Subgroup.closure_eq]
theorem supported (F:Finset (V K)): J K F=(supportedAt (K:=K) (F:Set (V K))).comap (e K).symm.toMonoidHom := by
  apply closure_of_carrier
  intro a
  change _ ↔ (e K).symm a∈supportedAt (F:Set _)
  rw [mem_supportedAt_iff,Set.mem_setOf_eq]
  apply forall_congr'
  intro v
  apply imp_congr_right
  intro _
  exact (units_mem (v.adicCompletionIntegers K) (finiteComponent v ((e K).symm a))).symm
theorem prescribed (n:ℕ+) (S T:Finset (V K)): U K n S T=(idelePowerLocalUnitSubgroup (K:=K) n S T).comap (e K).symm.toMonoidHom := by
  apply closure_of_carrier
  intro a
  change _ ↔ (e K).symm a∈idelePowerLocalUnitSubgroup n S T
  rw [mem_idelePowerLocalUnitSubgroup_iff,Set.mem_setOf_eq]
  apply and_congr (forall_congr' fun w=>(powers_mem n (infiniteComponent w ((e K).symm a))).symm)
  refine and_congr (forall_congr' fun v=>imp_congr_right fun _=>(powers_mem n (finiteComponent v ((e K).symm a))).symm) ?_
  exact forall_congr' fun v=>imp_congr_right fun _=>(units_mem (v.adicCompletionIntegers K) (finiteComponent v ((e K).symm a))).symm

theorem product (n:ℕ+) (S T:Finset (V K)):
    (U K n S T).relIndex (J K (S∪T))=
      (∏ w:InfinitePlace K,if w.IsReal ∧ Even (n:ℕ) then 2 else 1)*
      ∏ v:↥S,(powMonoidHom (n:ℕ):(v.val.adicCompletion K)ˣ→*(v.val.adicCompletion K)ˣ).range.index := by
  rw [prescribed,supported,Subgroup.relIndex_comap,Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr (e K).symm.surjective,top_inf_eq,Finset.coe_union]
  have eq:=card_supportedIdeleQuotient_eq_localPowerClasses (K:=K) n S T
  rw [Nat.card_prod,Nat.card_pi,Nat.card_pi] at eq
  rw [←Finset.prod_congr rfl (fun (w:InfinitePlace K) _=>card_infinitePlace_nthPowerQuotient (K:=K) n w)]
  exact eq
end
end TunnellKummerSupportGroups


namespace TunnellSupportedIndexEvaluation
open NumberField IsDedekindDomain
open scoped NumberField TensorProduct Classical
noncomputable section

variable {K:Type} [Field K] [NumberField K]
theorem prod_absNorm_maxPowDividing_natCast
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS :
      ∀ v : HeightOneSpectrum (𝓞 K),
        v.asIdeal ∣ Ideal.span {((n : ℕ) : 𝓞 K)} →
          v ∈ S) :
    (∏ v : ↥S,
        Ideal.absNorm
          (v.1.maxPowDividing
            (Ideal.span {((n : ℕ) : 𝓞 K)}))) =
      (n : ℕ) ^ Module.finrank ℚ K := by
  classical
  let I : Ideal (𝓞 K) :=
    Ideal.span {((n : ℕ) : 𝓞 K)}
  have hI : I ≠ 0 := by
    simp [I, n.ne_zero]
  let f : HeightOneSpectrum (𝓞 K) → ℕ :=
    fun v => Ideal.absNorm (v.maxPowDividing I)
  have hsupport : Function.mulSupport f ⊆ (S : Set _) := by
    intro v hv
    apply hS v
    have hcount :
        (Associates.mk v.asIdeal).count
            (Associates.mk I).factors ≠ 0 := by
      intro hzero
      apply hv
      simp [f, IsDedekindDomain.HeightOneSpectrum.maxPowDividing,
        hzero]
    exact
      (Associates.count_ne_zero_iff_dvd
        hI v.irreducible).mp hcount
  have hmap :
      Ideal.absNorm
          (∏ᶠ v : HeightOneSpectrum (𝓞 K),
            v.maxPowDividing I) =
        ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          Ideal.absNorm (v.maxPowDividing I) :=
    Ideal.absNorm.map_finprod
      (Ideal.hasFiniteMulSupport hI)
  calc
    (∏ v : ↥S,
        Ideal.absNorm
          (v.1.maxPowDividing
            (Ideal.span {((n : ℕ) : 𝓞 K)}))) =
        ∏ v ∈ S, f v := by
      simpa [f, I] using Finset.prod_coe_sort S f
    _ = ∏ᶠ v : HeightOneSpectrum (𝓞 K), f v :=
      (finprod_eq_prod_of_mulSupport_subset f hsupport).symm
    _ =
        Ideal.absNorm
          (∏ᶠ v : HeightOneSpectrum (𝓞 K),
            v.maxPowDividing I) := hmap.symm
    _ = Ideal.absNorm I := by
      rw [Ideal.finprod_heightOneSpectrum_factorization hI]
    _ = (n : ℕ) ^ Module.finrank ℚ K := by
      change
        Ideal.absNorm
            (Ideal.span {(((n : ℕ) : ℕ) : 𝓞 K)}) =
          (n : ℕ) ^ Module.finrank ℚ K
      rw [Ideal.absNorm_span_natCast,
        NumberField.RingOfIntegers.rank]


theorem prod_infinitePlace_nthPowerIndex
    (n : ℕ+) :
    (∏ w : InfinitePlace K,
        if w.IsReal ∧ Even (n : ℕ) then 2 else 1) =
      if Even (n : ℕ) then
        2 ^ InfinitePlace.nrRealPlaces K
      else 1 := by
  classical
  by_cases hn : Even (n : ℕ)
  · rw [if_pos hn]
    rw [InfinitePlace.prod_eq_prod_mul_prod]
    simp only [hn, and_true]
    have hr :
        (∏ w : {w : InfinitePlace K // w.IsReal},
            if w.1.IsReal then 2 else 1) =
          ∏ _w : {w : InfinitePlace K // w.IsReal}, 2 := by
      apply Finset.prod_congr rfl
      intro w _
      rw [if_pos w.2]
    have hc :
        (∏ w : {w : InfinitePlace K // w.IsComplex},
            if w.1.IsReal then 2 else 1) =
          ∏ _w : {w : InfinitePlace K // w.IsComplex}, 1 := by
      apply Finset.prod_congr rfl
      intro w _
      rw [if_neg
        (InfinitePlace.not_isReal_iff_isComplex.mpr w.2)]
    rw [hr, hc]
    simp [InfinitePlace.nrRealPlaces]
  · simp [hn]


theorem prod_infinitePlace_nthPowerIndex_mul_natDegree
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    (∏ w : InfinitePlace K,
        if w.IsReal ∧ Even (n : ℕ) then 2 else 1) *
        (n : ℕ) ^ Module.finrank ℚ K =
      (n : ℕ) ^
        (2 * Fintype.card (InfinitePlace K)) := by
  classical
  have harch :=
    prod_infinitePlace_nthPowerIndex (K := K) n
  obtain ⟨ζ, hζ⟩ := hmu
  have hζprim : IsPrimitiveRoot ζ (n : ℕ) :=
    (mem_primitiveRoots n.pos).mp hζ
  have hsignature :=
    InfinitePlace.card_add_two_mul_card_eq_rank K
  have hplaces :=
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
  by_cases hlarge : 2 < (n : ℕ)
  · have hreal :
        InfinitePlace.nrRealPlaces K = 0 :=
      InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt
        hlarge hζprim
    rw [hreal, zero_add] at hsignature hplaces
    have hdegree :
        Module.finrank ℚ K =
          2 * Fintype.card (InfinitePlace K) := by
      omega
    rw [harch, hreal, hdegree]
    simp
  · have hnle : (n : ℕ) ≤ 2 :=
      Nat.le_of_not_gt hlarge
    have hnpos : 0 < (n : ℕ) := n.pos
    have hone_or_two :
        (n : ℕ) = 1 ∨ (n : ℕ) = 2 := by
      omega
    rcases hone_or_two with hone | htwo
    · have hn : n = (1 : ℕ+) := Subtype.ext hone
      subst n
      rw [harch]
      simp
    · have hn : n = (2 : ℕ+) := Subtype.ext htwo
      subst n
      rw [harch]
      rw [if_pos (by decide :
        Even (((2 : ℕ+) : ℕ)))]
      change
        2 ^ InfinitePlace.nrRealPlaces K *
            2 ^ Module.finrank ℚ K =
          2 ^ (2 * Fintype.card (InfinitePlace K))
      rw [← pow_add]
      congr 1
      omega


theorem result : TunnellGroupedPart2.Statement := by
  intro K _ _ p hp hmu
  dsimp only
  intro S T hs
  change (TunnellKummerSupportGroups.U K p S T).relIndex (TunnellKummerSupportGroups.J K (S∪T))=_
  have groupEval:=TunnellKummerSupportGroups.product K ⟨p,hp.pos⟩ S T
  change (TunnellKummerSupportGroups.U K p S T).relIndex (TunnellKummerSupportGroups.J K (S∪T))= (∏ w:InfinitePlace K,if w.IsReal ∧ Even p then 2 else 1)*∏ v:↥S,(powMonoidHom p:(v.val.adicCompletion K)ˣ→*(v.val.adicCompletion K)ˣ).range.index at groupEval
  rw [groupEval]
  let n:ℕ+:=⟨p,hp.pos⟩
  have finiteNorm:(∏ v:↥S,Ideal.absNorm (v.val.maxPowDividing (Ideal.span {(p:𝓞 K)})))=p^Module.finrank ℚ K:=
    prod_absNorm_maxPowDividing_natCast (K:=K) n S hs
  have arch:(∏ w:InfinitePlace K,if w.IsReal ∧ Even p then 2 else 1)*p^Module.finrank ℚ K=p^(2*Fintype.card (InfinitePlace K)):=
    prod_infinitePlace_nthPowerIndex_mul_natDegree (K:=K) n hmu
  simp_rw [TunnellCompletedPower.result p hp hmu]
  simp_rw [←mul_assoc p p,←pow_two]
  rw [Finset.prod_mul_distrib,finiteNorm]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_coe]
  rw [mul_left_comm,arch,←pow_mul,←pow_add,Nat.card_eq_fintype_card (α:=InfinitePlace K)]
  congr 1
  omega
end
end TunnellSupportedIndexEvaluation

theorem TunnellGroupedPart2.result : TunnellGroupedPart2.Statement := TunnellSupportedIndexEvaluation.result
end

namespace TunnellGroupedPart3
open NumberField IsDedekindDomain
open scoped NumberField TensorProduct Classical
set_option maxHeartbeats 3000000 in
def Statement : Prop :=
∀(D:Type)[Field D][NumberField D](p:ℕ),p.Prime → (primitiveRoots p D).Nonempty →
   ∀ F:Finset (HeightOneSpectrum (𝓞 D)),
     let E:=(F:Set (HeightOneSpectrum (𝓞 D))).unit D
     (powMonoidHom p:E→*E).range.index=p^(Nat.card (InfinitePlace D)+F.card)
end TunnellGroupedPart3

section

/-! The rank of the S-unit logarithmic lattice and the roots of unity compute the index of pth powers. -/
/- ClassFieldTheory.AlgebraicNumberTheory.Idele.SPlaces -/
section
open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace FiniteIdeleGroup
end FiniteIdeleGroup
namespace IdeleGroup
end IdeleGroup
 

abbrev SUnitGroup
    (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  (S : Set (HeightOneSpectrum (𝓞 K))).unit K
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.SUnit.Rank -/
section
noncomputable section
open IsDedekindDomain
open scoped NumberField nonZeroDivisors
variable {K : Type*} [Field K] [NumberField K]
namespace SUnitGroup
 
noncomputable def emptyEquivNumberFieldUnits :
    ((∅ : Set (HeightOneSpectrum (𝓞 K))).unit K) ≃* (𝓞 K)ˣ :=
  let eInteger :
      ((∅ : Set (HeightOneSpectrum (𝓞 K))).integer K)ˣ ≃*
        (⊥ : Subalgebra (𝓞 K) K)ˣ :=
    Units.mapEquiv
      ((Subalgebra.equivOfEq
        ((∅ : Set (HeightOneSpectrum (𝓞 K))).integer K)
        (⊥ : Subalgebra (𝓞 K) K)
        (IsDedekindDomain.integer_empty (𝓞 K) K) : _ ≃ₐ[𝓞 K] _) : _ ≃* _)
  let eBot :
      (⊥ : Subalgebra (𝓞 K) K)ˣ ≃* (𝓞 K)ˣ :=
    Units.mapEquiv
      ((Algebra.botEquivOfInjective
        (IsFractionRing.injective (𝓞 K) K) : _ ≃ₐ[𝓞 K] _) : _ ≃* _)
  (Set.unitEquivUnitsInteger
    (∅ : Set (HeightOneSpectrum (𝓞 K))) K).trans
      (eInteger.trans eBot)
 
noncomputable def fromNumberFieldUnits
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (𝓞 K)ˣ →* SUnitGroup (K := K) S where
  toFun u :=
    ⟨((emptyEquivNumberFieldUnits (K := K)).symm u : Kˣ),
      fun v _ =>
        Set.unit_valuation_eq_one
          (∅ : Set (HeightOneSpectrum (𝓞 K))) K
          ((emptyEquivNumberFieldUnits (K := K)).symm u) (by simp)⟩
  map_one' := by
    ext
    simp
  map_mul' u v := by
    ext
    simp
theorem fromNumberFieldUnits_injective
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Injective (fromNumberFieldUnits (K := K) S) := by
  intro u v huv
  apply (emptyEquivNumberFieldUnits (K := K)).symm.injective
  ext
  exact congrArg (fun x : SUnitGroup (K := K) S => ((x : Kˣ) : K)) huv
 

theorem torsion_eq_rootsOfUnity_range
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    CommGroup.torsion (SUnitGroup (K := K) S) =
      Subgroup.map (fromNumberFieldUnits (K := K) S)
        (NumberField.Units.torsion K) := by
  ext x
  constructor
  · intro hx
    have hxfin : IsOfFinOrder x :=
      (CommGroup.mem_torsion (G := SUnitGroup (K := K) S) x).mp hx
    obtain ⟨n, hnpos, hxpow⟩ := hxfin.exists_pow_eq_one
    have hxK : (((x : Kˣ) : K) ^ n) = 1 := by
      simpa using congrArg
        (fun y : SUnitGroup (K := K) S => ((y : Kˣ) : K)) hxpow
    let y : ((∅ : Set (HeightOneSpectrum (𝓞 K))).unit K) :=
      ⟨(x : Kˣ), fun v _ => by
        have hvpow :
            (v.valuation K ((x : Kˣ) : K)) ^ n = 1 := by
          rw [← map_pow, hxK, map_one]
        exact (pow_eq_one_iff_left
          (a := v.valuation K ((x : Kˣ) : K))
          (Nat.ne_of_gt hnpos)).mp hvpow⟩
    let u : (𝓞 K)ˣ := emptyEquivNumberFieldUnits y
    have hufin : IsOfFinOrder u := by
      exact (emptyEquivNumberFieldUnits (K := K)).toMonoidHom.isOfFinOrder
        ((show IsOfFinOrder y from by
          refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hnpos, ?_⟩
          ext
          exact hxK))
    refine ⟨u, ?_, ?_⟩
    · exact (CommGroup.mem_torsion (G := (𝓞 K)ˣ) u).2 hufin
    · ext
      change
        (((emptyEquivNumberFieldUnits (K := K)).symm
          (emptyEquivNumberFieldUnits (K := K) y) : Kˣ) : K) =
            ((x : Kˣ) : K)
      rw [MulEquiv.symm_apply_apply]
  · rintro ⟨u, hu, rfl⟩
    exact (CommGroup.mem_torsion
      (G := SUnitGroup (K := K) S)
      (fromNumberFieldUnits (K := K) S u)).2
        ((fromNumberFieldUnits (K := K) S).isOfFinOrder
          ((CommGroup.mem_torsion (G := (𝓞 K)ˣ) u).1 hu))
section DivisorMap
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
 

noncomputable def divisorCoordinate
    (x : SUnitGroup (K := K) S) (v : S) : ℤ :=
  FractionalIdeal.count K (v : HeightOneSpectrum (𝓞 K))
    (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((x : Kˣ) : K))
 

theorem valuation_mk'_eq_exp_neg_count
    (v : HeightOneSpectrum (𝓞 K)) {n : 𝓞 K} (hn : n ≠ 0)
    (d : (𝓞 K)⁰) :
    v.valuation K (IsLocalization.mk' K n d) =
      WithZero.exp
        (-FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton (𝓞 K)⁰
            (IsLocalization.mk' K n d))) := by
  classical
  have hI :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (IsLocalization.mk' K n d) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰
            ((algebraMap (𝓞 K) K) (d : 𝓞 K))⁻¹ *
          ↑(Ideal.span {n} : Ideal (𝓞 K)) := by
    rw [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    apply congr_arg
    rw [IsFractionRing.mk'_eq_div, div_eq_mul_inv, mul_comm]
  have hx :
      FractionalIdeal.spanSingleton (𝓞 K)⁰
          (IsLocalization.mk' K n d) ≠ 0 := by
    rw [FractionalIdeal.spanSingleton_ne_zero_iff,
      IsFractionRing.mk'_eq_div, ne_eq, div_eq_zero_iff, not_or]
    exact
      ⟨(map_ne_zero_iff (algebraMap (𝓞 K) K)
          (IsFractionRing.injective (𝓞 K) K)).mpr hn,
        map_ne_zero_of_mem_nonZeroDivisors _
          (IsFractionRing.injective (𝓞 K) K) d.property⟩
  have hcount :
      FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton (𝓞 K)⁰
            (IsLocalization.mk' K n d)) =
        ((Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span {n} : Ideal (𝓞 K))).factors -
          (Associates.mk v.asIdeal).count
            (Associates.mk
              (Ideal.span {(d : 𝓞 K)} : Ideal (𝓞 K))).factors : ℤ) := by
    exact FractionalIdeal.count_well_defined (K := K) v hx hI
  rw [v.valuation_of_mk', v.intValuation_if_neg hn,
    v.intValuation_if_neg (nonZeroDivisors.coe_ne_zero d), hcount]
  rw [div_eq_mul_inv, ← WithZero.exp_neg, ← WithZero.exp_add]
  congr
  simp [sub_eq_add_neg, add_comm]
 

theorem valuation_eq_exp_neg_count
    (x : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    v.valuation K (x : K) =
      WithZero.exp
        (-FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K))) := by
  obtain ⟨n, d, hnd⟩ :=
    IsLocalization.exists_mk'_eq (𝓞 K)⁰ (x : K)
  have hn : n ≠ 0 := by
    intro hn0
    apply Units.ne_zero x
    rw [← hnd, hn0, IsFractionRing.mk'_eq_div, map_zero, zero_div]
  rw [← hnd]
  exact valuation_mk'_eq_exp_neg_count (K := K) v hn d
 

theorem valuation_eq_one_iff_count_eq_zero
    (x : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    v.valuation K (x : K) = 1 ↔
      FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) = 0 := by
  rw [valuation_eq_exp_neg_count (K := K) x v]
  constructor
  · intro h
    exact neg_eq_zero.mp (WithZero.exp_eq_one.mp h)
  · intro h
    simp [h]
theorem divisorCoordinate_eq_zero_iff
    (x : SUnitGroup (K := K) S) (v : S) :
    divisorCoordinate (K := K) S x v = 0 ↔
      (v : HeightOneSpectrum (𝓞 K)).valuation K ((x : Kˣ) : K) = 1 := by
  exact (valuation_eq_one_iff_count_eq_zero
    (K := K) (x : Kˣ) (v : HeightOneSpectrum (𝓞 K))).symm
theorem divisorCoordinate_mul
    (x y : SUnitGroup (K := K) S) (v : S) :
    divisorCoordinate (K := K) S (x * y) v =
      divisorCoordinate (K := K) S x v +
        divisorCoordinate (K := K) S y v := by
  change
    FractionalIdeal.count K (v : HeightOneSpectrum (𝓞 K))
        (FractionalIdeal.spanSingleton (𝓞 K)⁰
          ((((x : Kˣ) : K) * ((y : Kˣ) : K)))) =
      FractionalIdeal.count K (v : HeightOneSpectrum (𝓞 K))
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((x : Kˣ) : K)) +
        FractionalIdeal.count K (v : HeightOneSpectrum (𝓞 K))
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((y : Kˣ) : K))
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul]
  · exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr
      (Units.ne_zero (x : Kˣ))
  · exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr
      (Units.ne_zero (y : Kˣ))
theorem divisorCoordinate_one (v : S) :
    divisorCoordinate (K := K) S 1 v = 0 := by
  simp [divisorCoordinate, FractionalIdeal.count_one]
 
noncomputable def divisor :
    Additive (SUnitGroup (K := K) S) →+
      (S → ℤ) where
  toFun x v := divisorCoordinate (K := K) S (Additive.toMul x) v
  map_zero' := by
    ext v
    exact divisorCoordinate_one (K := K) S v
  map_add' x y := by
    ext v
    exact divisorCoordinate_mul (K := K) S
      (Additive.toMul x) (Additive.toMul y) v
 
noncomputable def divisorLinearMap :
    Additive (SUnitGroup (K := K) S) →ₗ[ℤ] (S → ℤ) :=
  (divisor (K := K) S).toIntLinearMap
 
noncomputable def fromNumberFieldUnitsLinearMap :
    Additive (𝓞 K)ˣ →ₗ[ℤ]
      Additive (SUnitGroup (K := K) S) :=
  (MonoidHom.toAdditive
    (fromNumberFieldUnits (K := K) S)).toIntLinearMap
theorem fromNumberFieldUnitsLinearMap_injective :
    Function.Injective (fromNumberFieldUnitsLinearMap (K := K) S) := by
  intro x y hxy
  apply Additive.toMul.injective
  exact fromNumberFieldUnits_injective (K := K) S
    (congrArg Additive.toMul hxy)
 

theorem valuation_eq_one_of_mem_ker_divisorLinearMap
    {x : Additive (SUnitGroup (K := K) S)}
    (hx : x ∈ LinearMap.ker (divisorLinearMap (K := K) S))
    (v : HeightOneSpectrum (𝓞 K)) :
    v.valuation K
      ((((Additive.toMul x :
        SUnitGroup (K := K) S) : Kˣ) : K)) = 1 := by
  by_cases hv : v ∈ S
  · let vv : S := ⟨v, hv⟩
    apply (divisorCoordinate_eq_zero_iff (K := K) S
      (Additive.toMul x) vv).1
    have hxzero :
        divisorLinearMap (K := K) S x = 0 :=
      LinearMap.mem_ker.mp hx
    simpa [divisorLinearMap, divisor] using congrFun hxzero vv
  · exact (Additive.toMul x :
      SUnitGroup (K := K) S).property v hv
 

noncomputable def kerDivisorToEmptySUnits
    (x : LinearMap.ker (divisorLinearMap (K := K) S)) :
    ((∅ : Set (HeightOneSpectrum (𝓞 K))).unit K) :=
  ⟨((Additive.toMul (x : Additive (SUnitGroup (K := K) S)) :
      SUnitGroup (K := K) S) : Kˣ),
    fun v _ =>
      valuation_eq_one_of_mem_ker_divisorLinearMap
        (K := K) S x.property v⟩
 
theorem range_fromNumberFieldUnitsLinearMap_eq_ker_divisorLinearMap :
    LinearMap.range (fromNumberFieldUnitsLinearMap (K := K) S) =
      LinearMap.ker (divisorLinearMap (K := K) S) := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    apply LinearMap.mem_ker.mpr
    ext v
    apply (divisorCoordinate_eq_zero_iff (K := K) S
      (fromNumberFieldUnits (K := K) S (Additive.toMul u)) v).2
    exact Set.unit_valuation_eq_one
      (∅ : Set (HeightOneSpectrum (𝓞 K))) K
      ((emptyEquivNumberFieldUnits (K := K)).symm (Additive.toMul u))
      (by simp)
  · intro hx
    let y := kerDivisorToEmptySUnits (K := K) S ⟨x, hx⟩
    let u : (𝓞 K)ˣ := emptyEquivNumberFieldUnits y
    refine ⟨Additive.ofMul u, ?_⟩
    apply Additive.toMul.injective
    change
      fromNumberFieldUnits (K := K) S u = Additive.toMul x
    apply Subtype.ext
    change
      ((emptyEquivNumberFieldUnits (K := K)).symm u : Kˣ) =
        ((Additive.toMul x : SUnitGroup (K := K) S) : Kˣ)
    dsimp [u]
    rw [MulEquiv.symm_apply_apply]
    rfl
end DivisorMap
section PrimePowerSources
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
 
theorem primeIdealPower_classNumber_isPrincipal (v : S) :
    ((v : HeightOneSpectrum (𝓞 K)).asIdeal ^
      NumberField.classNumber K).IsPrincipal := by
  have hv0 :
      (v : HeightOneSpectrum (𝓞 K)).asIdeal ^
          NumberField.classNumber K ≠ 0 :=
    pow_ne_zero _ (v : HeightOneSpectrum (𝓞 K)).ne_bot
  apply (ClassGroup.mk0_eq_one_iff
    (mem_nonZeroDivisors_iff_ne_zero.mpr hv0)).mp
  have hpow :
      (ClassGroup.mk0
        ⟨(v : HeightOneSpectrum (𝓞 K)).asIdeal,
          mem_nonZeroDivisors_iff_ne_zero.mpr
            (v : HeightOneSpectrum (𝓞 K)).ne_bot⟩) ^
          Fintype.card (ClassGroup (𝓞 K)) = 1 :=
    pow_card_eq_one
      (x := ClassGroup.mk0
        ⟨(v : HeightOneSpectrum (𝓞 K)).asIdeal,
          mem_nonZeroDivisors_iff_ne_zero.mpr
            (v : HeightOneSpectrum (𝓞 K)).ne_bot⟩)
  let I : (Ideal (𝓞 K))⁰ :=
    ⟨(v : HeightOneSpectrum (𝓞 K)).asIdeal,
      mem_nonZeroDivisors_iff_ne_zero.mpr
        (v : HeightOneSpectrum (𝓞 K)).ne_bot⟩
  have hsub :
      (⟨(v : HeightOneSpectrum (𝓞 K)).asIdeal ^
          NumberField.classNumber K,
        mem_nonZeroDivisors_iff_ne_zero.mpr hv0⟩ :
          (Ideal (𝓞 K))⁰) =
        I ^ NumberField.classNumber K := by
    rfl
  rw [hsub, map_pow]
  exact hpow
 
private noncomputable def primePowerGenerator (v : S) : 𝓞 K :=
  let I :=
    (v : HeightOneSpectrum (𝓞 K)).asIdeal ^
      NumberField.classNumber K
  letI : I.IsPrincipal :=
    primeIdealPower_classNumber_isPrincipal (K := K) S v
  Submodule.IsPrincipal.generator I
private theorem span_primePowerGenerator (v : S) :
    Ideal.span {primePowerGenerator (K := K) S v} =
      (v : HeightOneSpectrum (𝓞 K)).asIdeal ^
        NumberField.classNumber K := by
  let I :=
    (v : HeightOneSpectrum (𝓞 K)).asIdeal ^
      NumberField.classNumber K
  let : I.IsPrincipal :=
    primeIdealPower_classNumber_isPrincipal (K := K) S v
  simp [primePowerGenerator]
private theorem primePowerGenerator_ne_zero (v : S) :
    primePowerGenerator (K := K) S v ≠ 0 := by
  intro hzero
  have hv0 :
      (v : HeightOneSpectrum (𝓞 K)).asIdeal ^
          NumberField.classNumber K ≠ 0 :=
    pow_ne_zero _ (v : HeightOneSpectrum (𝓞 K)).ne_bot
  apply hv0
  rw [← span_primePowerGenerator (K := K) S v, hzero]
  simp
private theorem spanSingleton_primePowerGenerator (v : S) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰
        (algebraMap (𝓞 K) K (primePowerGenerator (K := K) S v)) =
      ((v : HeightOneSpectrum (𝓞 K)).asIdeal :
        FractionalIdeal (𝓞 K)⁰ K) ^ NumberField.classNumber K := by
  rw [← FractionalIdeal.coeIdeal_span_singleton,
    span_primePowerGenerator (K := K) S v,
    FractionalIdeal.coeIdeal_pow]
 

private noncomputable def primePowerSUnit (v : S) :
    SUnitGroup (K := K) S :=
  ⟨Units.mk0
      (algebraMap (𝓞 K) K (primePowerGenerator (K := K) S v))
      ((map_ne_zero_iff (algebraMap (𝓞 K) K)
        (IsFractionRing.injective (𝓞 K) K)).mpr
          (primePowerGenerator_ne_zero (K := K) S v)),
    fun w hw => by
      apply (valuation_eq_one_iff_count_eq_zero (K := K)
        (Units.mk0
          (algebraMap (𝓞 K) K (primePowerGenerator (K := K) S v))
          ((map_ne_zero_iff (algebraMap (𝓞 K) K)
            (IsFractionRing.injective (𝓞 K) K)).mpr
              (primePowerGenerator_ne_zero (K := K) S v))) w).2
      change
        FractionalIdeal.count K w
          (FractionalIdeal.spanSingleton (𝓞 K)⁰
            (algebraMap (𝓞 K) K
              (primePowerGenerator (K := K) S v))) = 0
      rw [spanSingleton_primePowerGenerator (K := K) S v,
        FractionalIdeal.count_pow]
      have hwv :
          (v : HeightOneSpectrum (𝓞 K)) ≠ w := by
        intro hvw
        exact hw (hvw ▸ v.property)
      rw [FractionalIdeal.count_maximal_coprime K w hwv]
      simp⟩
private noncomputable def classNumberBasisVector (v : S) : S → ℤ := by
  classical
  exact fun w =>
    if w = v then (NumberField.classNumber K : ℤ) else 0
private theorem divisorCoordinate_primePowerSUnit
    (v w : S) :
    divisorCoordinate (K := K) S (primePowerSUnit (K := K) S v) w =
      classNumberBasisVector (K := K) S v w := by
  classical
  change
    FractionalIdeal.count K (w : HeightOneSpectrum (𝓞 K))
        (FractionalIdeal.spanSingleton (𝓞 K)⁰
          (algebraMap (𝓞 K) K
            (primePowerGenerator (K := K) S v))) =
      classNumberBasisVector (K := K) S v w
  simp only [classNumberBasisVector]
  rw [spanSingleton_primePowerGenerator (K := K) S v]
  split_ifs with hwv
  · subst w
    simpa using
      FractionalIdeal.count_pow_self K
        (v : HeightOneSpectrum (𝓞 K))
        (NumberField.classNumber K)
  · rw [FractionalIdeal.count_pow]
    have hvw :
        (v : HeightOneSpectrum (𝓞 K)) ≠
          (w : HeightOneSpectrum (𝓞 K)) := by
      intro h
      exact hwv (Subtype.ext h.symm)
    rw [FractionalIdeal.count_maximal_coprime K
      (w : HeightOneSpectrum (𝓞 K)) hvw]
    simp
end PrimePowerSources
section Rank
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
private noncomputable def divisorRangeVector (v : S) :
    LinearMap.range (divisorLinearMap (K := K) S) :=
  ⟨classNumberBasisVector (K := K) S v,
    ⟨Additive.ofMul (primePowerSUnit (K := K) S v), by
      ext w
      exact divisorCoordinate_primePowerSUnit (K := K) S v w⟩⟩
private theorem divisorRangeVector_linearIndependent :
    LinearIndependent ℤ (divisorRangeVector (K := K) S) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg v
  have hv := congrArg
    (fun z : LinearMap.range (divisorLinearMap (K := K) S) =>
      ((z : S → ℤ) v)) hg
  simp [divisorRangeVector, classNumberBasisVector] at hv
  exact hv.resolve_right (NumberField.classNumber_ne_zero K)
 

theorem finrank_divisor_range :
    Module.finrank ℤ
        (LinearMap.range (divisorLinearMap (K := K) S)) =
      S.card := by
  let : Module.Finite ℤ (S → ℤ) := inferInstance
  let : Module.Finite ℤ
      (LinearMap.range (divisorLinearMap (K := K) S)) :=
    Module.Finite.of_fg
      (IsNoetherian.noetherian
        (LinearMap.range (divisorLinearMap (K := K) S)))
  apply le_antisymm
  · calc
      Module.finrank ℤ
          (LinearMap.range (divisorLinearMap (K := K) S)) ≤
          Module.finrank ℤ (S → ℤ) :=
        Submodule.finrank_le
          (LinearMap.range (divisorLinearMap (K := K) S))
      _ = S.card := by simp
  · simpa using
      (divisorRangeVector_linearIndependent (K := K) S).fintype_card_le_finrank
 
theorem moduleFinite :
    Module.Finite ℤ (Additive (SUnitGroup (K := K) S)) := by
  let : Module.Finite ℤ (S → ℤ) := inferInstance
  have : Module.Finite ℤ
      (LinearMap.range (divisorLinearMap (K := K) S)) :=
    Module.Finite.of_fg
      (IsNoetherian.noetherian
        (LinearMap.range (divisorLinearMap (K := K) S)))
  rw [Module.finite_def]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker
    (divisorLinearMap (K := K) S) ?_ ?_
  · rw [Submodule.map_top]
    exact IsNoetherian.noetherian
      (LinearMap.range (divisorLinearMap (K := K) S))
  · rw [inf_of_le_right le_top,
      ← range_fromNumberFieldUnitsLinearMap_eq_ker_divisorLinearMap
        (K := K) S]
    exact Submodule.fg_range
      (fromNumberFieldUnitsLinearMap (K := K) S)
 
theorem finrank_divisor_ker :
    Module.finrank ℤ
        (LinearMap.ker (divisorLinearMap (K := K) S)) =
      NumberField.Units.rank K := by
  calc
    Module.finrank ℤ
        (LinearMap.ker (divisorLinearMap (K := K) S)) =
        Module.finrank ℤ
          (LinearMap.range
            (fromNumberFieldUnitsLinearMap (K := K) S)) :=
      (LinearEquiv.ofEq _ _
        (range_fromNumberFieldUnitsLinearMap_eq_ker_divisorLinearMap
          (K := K) S).symm).finrank_eq
    _ = Module.finrank ℤ (Additive (𝓞 K)ˣ) :=
      (LinearEquiv.ofInjective
        (fromNumberFieldUnitsLinearMap (K := K) S)
        (fromNumberFieldUnitsLinearMap_injective (K := K) S)).symm.finrank_eq
    _ = NumberField.Units.rank K :=
      NumberField.Units.finrank_eq K
 

theorem finrank :
    Module.finrank ℤ (Additive (SUnitGroup (K := K) S)) =
      NumberField.Units.rank K + S.card := by
  let : Module.Finite ℤ
      (Additive (SUnitGroup (K := K) S)) :=
    moduleFinite (K := K) S
  let : Module.Finite ℤ (S → ℤ) := inferInstance
  let : Module.Finite ℤ
      (LinearMap.range (divisorLinearMap (K := K) S)) :=
    Module.Finite.of_fg
      (IsNoetherian.noetherian
        (LinearMap.range (divisorLinearMap (K := K) S)))
  let : Module.Finite ℤ
      (LinearMap.ker (divisorLinearMap (K := K) S)) :=
    Module.Finite.of_fg
      (IsNoetherian.noetherian
        (LinearMap.ker (divisorLinearMap (K := K) S)))
  have hrank :
      Module.rank ℤ (Additive (SUnitGroup (K := K) S)) =
        Module.rank ℤ
            (LinearMap.range (divisorLinearMap (K := K) S)) +
          Module.rank ℤ
            (LinearMap.ker (divisorLinearMap (K := K) S)) := by
    have h :=
      LinearMap.rank_eq_of_surjective
        (f := (divisorLinearMap (K := K) S).rangeRestrict)
        (divisorLinearMap (K := K) S).surjective_rangeRestrict
    rw [LinearMap.ker_rangeRestrict] at h
    exact h
  have hcard :
      (Module.finrank ℤ
          (Additive (SUnitGroup (K := K) S)) : Cardinal) =
        (Module.finrank ℤ
            (LinearMap.range (divisorLinearMap (K := K) S)) : Cardinal) +
          (Module.finrank ℤ
            (LinearMap.ker (divisorLinearMap (K := K) S)) : Cardinal) := by
    rw [Module.finrank_eq_rank, Module.finrank_eq_rank,
      (LinearMap.ker (divisorLinearMap (K := K) S)).finrank_eq_rank]
    exact hrank
  rw [← Nat.cast_inj (R := Cardinal), Nat.cast_add]
  calc
    (Module.finrank ℤ
        (Additive (SUnitGroup (K := K) S)) : Cardinal) =
      (Module.finrank ℤ
          (LinearMap.range (divisorLinearMap (K := K) S)) : Cardinal) +
        (Module.finrank ℤ
          (LinearMap.ker (divisorLinearMap (K := K) S)) : Cardinal) :=
      hcard
    _ = (S.card : Cardinal) +
        (NumberField.Units.rank K : Cardinal) := by
      rw [finrank_divisor_range (K := K) S,
        finrank_divisor_ker (K := K) S]
    _ = (NumberField.Units.rank K : Cardinal) +
        (S.card : Cardinal) := by rw [add_comm]
end Rank
end SUnitGroup
end
end

/- ClassFieldTheory.AlgebraicNumberTheory.SUnit.LogLattice -/
section
noncomputable section
open IsDedekindDomain Module
open scoped Classical NumberField nonZeroDivisors
variable {K : Type*} [Field K] [NumberField K]
namespace SUnitGroup
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
 


abbrev ReducedLogSpace :=
  NumberField.Units.dirichletUnitTheorem.logSpace K × (S → ℝ)
 



noncomputable def reducedLog :
    Additive (SUnitGroup (K := K) S) →+
      ReducedLogSpace (K := K) S where
  toFun x :=
    (fun w =>
      w.1.mult *
        Real.log
          (w.1
            (((Additive.toMul x :
              SUnitGroup (K := K) S) : Kˣ) : K)),
      fun v =>
        (divisorCoordinate (K := K) S
          (Additive.toMul x) v : ℝ))
  map_zero' := by
    apply Prod.ext
    · ext w
      simp
    · ext v
      change
        (divisorCoordinate (K := K) S 1 v : ℝ) = 0
      exact_mod_cast divisorCoordinate_one (K := K) S v
  map_add' x y := by
    apply Prod.ext
    · ext w
      simp [Real.log_mul, mul_add]
    · ext v
      change
        (divisorCoordinate (K := K) S
          (Additive.toMul x * Additive.toMul y) v : ℝ) =
          (divisorCoordinate (K := K) S
            (Additive.toMul x) v : ℝ) +
          (divisorCoordinate (K := K) S
            (Additive.toMul y) v : ℝ)
      exact_mod_cast
        divisorCoordinate_mul (K := K) S
          (Additive.toMul x) (Additive.toMul y) v
 
noncomputable def reducedLogLinearMap :
    Additive (SUnitGroup (K := K) S) →ₗ[ℤ]
      ReducedLogSpace (K := K) S :=
  (reducedLog (K := K) S).toIntLinearMap
section FullLogarithmicSpace
end FullLogarithmicSpace
section Decomposition
 

def logRank : ℕ :=
  Fintype.card (NumberField.InfinitePlace K) + S.card - 1
 
abbrev RootsOfUnityAdditive :=
  (NumberField.Units.torsion K).toAddSubgroup.toIntSubmodule
 
abbrev TorsionAdditive :=
  Submodule.torsion ℤ
    (Additive (SUnitGroup (K := K) S))
theorem torsionAdditive_eq :
    TorsionAdditive (K := K) S =
      (AddCommGroup.torsion
        (Additive
          (SUnitGroup (K := K) S))).toIntSubmodule := by
  apply Submodule.toAddSubgroup_injective
  rw [Submodule.torsion_int,
    AddSubgroup.toIntSubmodule_toAddSubgroup]
 
abbrev FreeQuotient :=
  Additive (SUnitGroup (K := K) S) ⧸
    TorsionAdditive (K := K) S
local instance instModuleFinite_additiveSUnit :
    Module.Finite ℤ (Additive (SUnitGroup (K := K) S)) :=
  moduleFinite (K := K) S
local instance instModule_freeQuotient :
    Module ℤ (FreeQuotient (K := K) S) :=
  Submodule.Quotient.module
    (TorsionAdditive (K := K) S)
local instance instModuleFinite_freeQuotient :
    Module.Finite ℤ (FreeQuotient (K := K) S) :=
  Module.Finite.quotient ℤ
    (TorsionAdditive (K := K) S)
local instance instModuleFree_freeQuotient :
    Module.Free ℤ (FreeQuotient (K := K) S) :=
  Module.free_of_finite_type_torsion_free'
 

theorem finrank_freeQuotient :
    Module.finrank ℤ (FreeQuotient (K := K) S) =
      logRank (K := K) S := by
  calc
    Module.finrank ℤ (FreeQuotient (K := K) S) =
        Module.finrank ℤ
          (Additive (SUnitGroup (K := K) S)) := by
      exact finrank_quotient_eq_of_le_torsion le_rfl
    _ = NumberField.Units.rank K + S.card :=
      finrank (K := K) S
    _ = logRank (K := K) S := by
      rw [NumberField.Units.rank]
      dsimp [logRank]
      have hpos :
          0 <
            Fintype.card
              (NumberField.InfinitePlace K) :=
        Fintype.card_pos
      omega
 
noncomputable def basisFreeQuotient :
    Basis (Fin (logRank (K := K) S)) ℤ
      (FreeQuotient (K := K) S) :=
  Basis.reindex
    (Module.Free.chooseBasis ℤ
      (FreeQuotient (K := K) S))
    (Fintype.equivOfCardEq <| by
      rw [← Module.finrank_eq_card_chooseBasisIndex,
        finrank_freeQuotient (K := K) S,
        Fintype.card_fin])
 

noncomputable def rootsOfUnityEquivTorsion :
    RootsOfUnityAdditive (K := K) ≃ₗ[ℤ]
      TorsionAdditive (K := K) S := by
  let f :
      RootsOfUnityAdditive (K := K) →ₗ[ℤ]
        TorsionAdditive (K := K) S :=
    ((fromNumberFieldUnitsLinearMap (K := K) S).domRestrict
      (RootsOfUnityAdditive (K := K))).codRestrict
        (TorsionAdditive (K := K) S) fun u => by
          rw [torsionAdditive_eq (K := K) S]
          change
            Additive.toMul
                (fromNumberFieldUnitsLinearMap (K := K) S
                  (u :
                    Additive (𝓞 K)ˣ)) ∈
              CommGroup.torsion
                (SUnitGroup (K := K) S)
          rw [torsion_eq_rootsOfUnity_range (K := K) S]
          refine
            ⟨Additive.toMul
                (u : Additive (𝓞 K)ˣ), ?_, rfl⟩
          exact u.property
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply fromNumberFieldUnitsLinearMap_injective
      (K := K) S
    exact congrArg Subtype.val hxy
  · intro y
    have hyadd :
        (y :
          Additive (SUnitGroup (K := K) S)) ∈
          AddCommGroup.torsion
            (Additive (SUnitGroup (K := K) S)) := by
      have hy' :
          (y :
            Additive (SUnitGroup (K := K) S)) ∈
            (AddCommGroup.torsion
              (Additive
                (SUnitGroup (K := K) S))).toIntSubmodule := by
        rw [← torsionAdditive_eq (K := K) S]
        exact y.property
      exact hy'
    have hy :
        Additive.toMul
            (y :
              Additive (SUnitGroup (K := K) S)) ∈
          CommGroup.torsion
            (SUnitGroup (K := K) S) :=
      hyadd
    rw [torsion_eq_rootsOfUnity_range (K := K) S] at hy
    obtain ⟨u, hu, huy⟩ := hy
    let x : RootsOfUnityAdditive (K := K) :=
      ⟨Additive.ofMul u, hu⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply Additive.toMul.injective
    exact huy
 

private noncomputable def torsionQuotientSection :
    FreeQuotient (K := K) S →ₗ[ℤ]
      Additive (SUnitGroup (K := K) S) :=
  (Module.projective_lifting_property
    (TorsionAdditive (K := K) S).mkQ
    LinearMap.id
    (TorsionAdditive (K := K) S).mkQ_surjective).choose
private theorem torsionQuotientSection_spec :
    (TorsionAdditive (K := K) S).mkQ.comp
        (torsionQuotientSection (K := K) S) =
      LinearMap.id :=
  (Module.projective_lifting_property
    (TorsionAdditive (K := K) S).mkQ
    LinearMap.id
    (TorsionAdditive (K := K) S).mkQ_surjective).choose_spec
 

private noncomputable def torsionProdFreeQuotientEquiv :
    Additive (SUnitGroup (K := K) S) ≃ₗ[ℤ]
      TorsionAdditive (K := K) S ×
        FreeQuotient (K := K) S :=
  (lequivProdOfRightSplitExact
    (TorsionAdditive (K := K) S).injective_subtype
    (by
      rw [Submodule.range_subtype, Submodule.ker_mkQ])
    (torsionQuotientSection_spec (K := K) S)).symm
 


noncomputable def decompositionLinearEquiv :
    Additive (SUnitGroup (K := K) S) ≃ₗ[ℤ]
      RootsOfUnityAdditive (K := K) ×
        (Fin (logRank (K := K) S) →₀ ℤ) :=
  (torsionProdFreeQuotientEquiv (K := K) S).trans
    ((rootsOfUnityEquivTorsion (K := K) S).symm.prodCongr
      (basisFreeQuotient (K := K) S).repr)
 

noncomputable def multiplicativeRootsOfUnityEquiv :
    Multiplicative (RootsOfUnityAdditive (K := K)) ≃*
      NumberField.Units.torsion K where
  toFun x :=
    ⟨Additive.toMul
      ((Multiplicative.toAdd x :
        RootsOfUnityAdditive (K := K)) :
        Additive (𝓞 K)ˣ),
      (Multiplicative.toAdd x :
        RootsOfUnityAdditive (K := K)).property⟩
  invFun u :=
    Multiplicative.ofAdd
      (⟨Additive.ofMul (u : (𝓞 K)ˣ), u.property⟩ :
        RootsOfUnityAdditive (K := K))
  left_inv x := by
    rfl
  right_inv u := by
    rfl
  map_mul' x y := by
    rfl
 



noncomputable def decomposition :
    SUnitGroup (K := K) S ≃*
      NumberField.Units.torsion K ×
        Multiplicative
          (Fin (logRank (K := K) S) →₀ ℤ) :=
  (AddEquiv.toMultiplicativeRight
      (decompositionLinearEquiv
        (K := K) S).toAddEquiv).trans
    (((MulEquiv.prodMultiplicative
        (RootsOfUnityAdditive (K := K))
        (Fin (logRank (K := K) S) →₀ ℤ)) :
        Multiplicative
            (RootsOfUnityAdditive (K := K) ×
              (Fin (logRank (K := K) S) →₀ ℤ)) ≃*
          Multiplicative (RootsOfUnityAdditive (K := K)) ×
            Multiplicative
              (Fin (logRank (K := K) S) →₀ ℤ)).trans
      ((multiplicativeRootsOfUnityEquiv
        (K := K)).prodCongr
          (MulEquiv.refl
            (Multiplicative
              (Fin (logRank (K := K) S) →₀ ℤ)))))
end Decomposition
end SUnitGroup
end
end

/- ValuedFieldTheory.LocalField.GroupTheory.PowerIndex -/
section
noncomputable section
namespace LocalFieldTheory

open scoped Int
section NthPowers
universe uG uH uU
variable (G : Type uG) (H : Type uH) (U : Type uU)
variable [CommGroup G] [CommGroup H] [CommGroup U]
 

 
 

 
 
 

end NthPowers
section AdditivePowers
universe uA uB uG
variable (A : Type uA) [AddCommGroup A]
 
abbrev nsmulAddSubgroup (n : ℕ) : AddSubgroup A :=
  (nsmulAddMonoidHom n).range
 

@[simp]
theorem mem_nsmulAddSubgroup_iff {n : ℕ} {x : A} :
    x ∈ nsmulAddSubgroup A n ↔ ∃ y : A, n • y = x := by
  simp [nsmulAddSubgroup, AddMonoidHom.mem_range]
 

theorem powMonoidHom_range_multiplicative_eq_nsmulAddSubgroup_toSubgroup
    (n : ℕ) :
    (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range =
      AddSubgroup.toSubgroup (nsmulAddSubgroup A n) := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_range] at hx
    rcases hx with ⟨y, rfl⟩
    simp
  · intro hx
    rw [MonoidHom.mem_range]
    have hxadd : Multiplicative.toAdd x ∈ nsmulAddSubgroup A n := by
      simpa using hx
    rw [mem_nsmulAddSubgroup_iff] at hxadd
    rcases hxadd with ⟨y, hy⟩
    refine ⟨Multiplicative.ofAdd y, ?_⟩
    apply Multiplicative.toAdd.injective
    simp [hy]
 

def multiplicativeNthPowerQuotientEquivAdditive (n : ℕ) :
    (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range) ≃
      (A ⧸ nsmulAddSubgroup A n) := by
  rw [powMonoidHom_range_multiplicative_eq_nsmulAddSubgroup_toSubgroup]
  exact Equiv.refl _
 

noncomputable instance finite_multiplicative_nthPowerQuotient
    (n : ℕ) [Finite (A ⧸ nsmulAddSubgroup A n)] :
    Finite
      (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range) :=
  Finite.of_equiv (A ⧸ nsmulAddSubgroup A n)
    (multiplicativeNthPowerQuotientEquivAdditive A n).symm
 

theorem card_multiplicative_nthPowerQuotient_eq_nsmulAddSubgroup_index
    (n : ℕ)
    [Finite (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range)] :
    Nat.card (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range) =
      (nsmulAddSubgroup A n).index := by
  rw [← Subgroup.index_eq_card
    (H := (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range)]
  rw [powMonoidHom_range_multiplicative_eq_nsmulAddSubgroup_toSubgroup]
  simp
 

theorem card_multiplicative_nthPowerQuotient_eq_additive_nsmulQuotient
    (n : ℕ)
    [Finite (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range)]
    [Finite (A ⧸ nsmulAddSubgroup A n)] :
    Nat.card (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range) =
      Nat.card (A ⧸ nsmulAddSubgroup A n) := by
  rw [card_multiplicative_nthPowerQuotient_eq_nsmulAddSubgroup_index]
  rw [AddSubgroup.index_eq_card]
section AdditiveProducts
variable (B : Type uB) [AddCommGroup B]
end AdditiveProducts
variable (G : Type uG) [CommGroup G]
end AdditivePowers
end LocalFieldTheory
end
end

/- ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.SUnitPowerQuotient -/
section
open scoped NumberField Classical IsMulCommutative NNReal ValuativeRel
open NumberField IsDedekindDomain

noncomputable section
namespace KummerTheory
variable {K : Type*} [Field K]
    [numberFieldK : NumberField K]
 
def totalPlaceCard
    (S : Finset (HeightOneSpectrum (𝓞 K))) : ℕ :=
  Fintype.card (InfinitePlace K) + S.card
 
def finsuppModHom (d n : ℕ) :
    (Fin d →₀ ℤ) →+ (Fin d → ZMod n) where
  toFun x i := x i
  map_zero' := by
    ext i
    simp
  map_add' x y := by
    ext i
    simp
 
theorem finsuppModHom_surjective (d n : ℕ) :
    Function.Surjective (finsuppModHom d n) := by
  intro y
  choose x hx using fun i => ZMod.intCast_surjective (y i)
  let x' : Fin d →₀ ℤ :=
    (Finsupp.equivFunOnFinite).symm x
  refine ⟨x', ?_⟩
  ext i
  exact hx i
 

theorem finsuppModHom_ker (d n : ℕ) :
    (finsuppModHom d n).ker =
      LocalFieldTheory.nsmulAddSubgroup (Fin d →₀ ℤ) n := by
  ext x
  constructor
  · intro hx
    rw [AddMonoidHom.mem_ker] at hx
    rw [LocalFieldTheory.mem_nsmulAddSubgroup_iff]
    let y : Fin d → ℤ := fun i => (x i) / n
    let y' : Fin d →₀ ℤ :=
      (Finsupp.equivFunOnFinite).symm y
    refine ⟨y', ?_⟩
    ext i
    have hdiv : (n : ℤ) ∣ x i := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact congrFun hx i
    change (n : ℤ) * (x i / n) = x i
    rw [mul_comm]
    exact Int.ediv_mul_cancel hdiv
  · intro hx
    rw [LocalFieldTheory.mem_nsmulAddSubgroup_iff] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [AddMonoidHom.mem_ker]
    ext i
    simp [finsuppModHom]
 
noncomputable def finsuppNsmulQuotientEquivPiZMod
    (d n : ℕ) :
    (Fin d →₀ ℤ) ⧸
        LocalFieldTheory.nsmulAddSubgroup (Fin d →₀ ℤ) n ≃+
      (Fin d → ZMod n) := by
  rw [← finsuppModHom_ker d n]
  exact QuotientAddGroup.quotientKerEquivOfSurjective
    (finsuppModHom d n)
    (finsuppModHom_surjective d n)
 

noncomputable instance finite_finsupp_nsmulQuotient
    (d : ℕ) (n : ℕ+) :
    Finite
      ((Fin d →₀ ℤ) ⧸
        LocalFieldTheory.nsmulAddSubgroup
          (Fin d →₀ ℤ) (n : ℕ)) := by
  let _ : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  exact Finite.of_equiv
    (Fin d → ZMod (n : ℕ))
    (finsuppNsmulQuotientEquivPiZMod d n).symm
 
theorem card_finsupp_nsmulQuotient
    (d : ℕ) (n : ℕ+) :
    Nat.card
        ((Fin d →₀ ℤ) ⧸
          LocalFieldTheory.nsmulAddSubgroup
            (Fin d →₀ ℤ) (n : ℕ)) =
      (n : ℕ) ^ d := by
  let _ : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  rw [Nat.card_congr
    (finsuppNsmulQuotientEquivPiZMod d n).toEquiv,
    Nat.card_pi]
  simp
omit [NumberField K] in
 

theorem n_dvd_numberField_torsionOrder
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    (n : ℕ) ∣ NumberField.Units.torsionOrder K := by
  let _ : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := hmu
  have hζprim : IsPrimitiveRoot ζ (n : ℕ) :=
    (mem_primitiveRoots n.pos).mp hζ
  let ζO : 𝓞 K := hζprim.toInteger
  have hζOprim : IsPrimitiveRoot ζO (n : ℕ) :=
    hζprim.toInteger_isPrimitiveRoot
  let hu : IsUnit ζO := hζOprim.isUnit n.ne_zero
  let u : (𝓞 K)ˣ := hu.unit
  have huval : (u : 𝓞 K) = ζO :=
    hu.unit_spec
  have huprim : IsPrimitiveRoot u (n : ℕ) := by
    rw [← IsPrimitiveRoot.coe_units_iff, huval]
    exact hζOprim
  have hutorsion : u ∈ NumberField.Units.torsion K := by
    rw [NumberField.Units.torsion,
      CommGroup.mem_torsion,
      isOfFinOrder_iff_pow_eq_one]
    exact ⟨n, n.pos, huprim.pow_eq_one⟩
  let ut : NumberField.Units.torsion K :=
    ⟨u, hutorsion⟩
  have hutprim : IsPrimitiveRoot ut (n : ℕ) := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact huprim
  rw [NumberField.Units.torsionOrder,
    hutprim.eq_orderOf]
  exact orderOf_dvd_natCard ut
include numberFieldK in
 

theorem card_numberField_torsion_nthPowerQuotient
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Nat.card
        (NumberField.Units.torsion K ⧸
          (powMonoidHom (n : ℕ) :
            NumberField.Units.torsion K →*
              NumberField.Units.torsion K).range) =
      (n : ℕ) := by
  let T := NumberField.Units.torsion K
  let P :=
    (powMonoidHom (n : ℕ) : T →* T).range
  have hcardP :
      Nat.card P =
        Nat.card T / (Nat.card T).gcd (n : ℕ) := by
    exact IsCyclic.card_powMonoidHom_range T (n : ℕ)
  have hgcd_dvd : (Nat.card T).gcd (n : ℕ) ∣ Nat.card T :=
    Nat.gcd_dvd_left _ _
  have hcard_factor :
      (Nat.card T).gcd (n : ℕ) *
          (Nat.card T / (Nat.card T).gcd (n : ℕ)) =
        Nat.card T :=
    Nat.mul_div_cancel' hgcd_dvd
  have hquotient :
      Nat.card (T ⧸ P) *
          (Nat.card T / (Nat.card T).gcd (n : ℕ)) =
        Nat.card T := by
    rw [← hcardP]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup P).symm
  have hfactor_pos :
      0 < Nat.card T / (Nat.card T).gcd (n : ℕ) := by
    rw [Nat.div_pos_iff]
    have hTpos : 0 < Nat.card T := Nat.card_pos
    exact ⟨Nat.gcd_pos_of_pos_left _ hTpos,
      Nat.gcd_le_left (m := Nat.card T) (n : ℕ) hTpos⟩
  have hcard :
      Nat.card (T ⧸ P) =
        (Nat.card T).gcd (n : ℕ) := by
    exact Nat.eq_of_mul_eq_mul_right hfactor_pos
      (hquotient.trans hcard_factor.symm)
  change Nat.card (T ⧸ P) = (n : ℕ)
  rw [hcard, Nat.gcd_eq_right]
  simpa [T, NumberField.Units.torsionOrder] using
    n_dvd_numberField_torsionOrder (K := K) n hmu
 



theorem card_sUnit_nthPowerQuotient
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Nat.card
        (SUnitGroup (K := K) S ⧸
          (powMonoidHom (n : ℕ) :
            SUnitGroup (K := K) S →*
              SUnitGroup (K := K) S).range) =
      (n : ℕ) ^ totalPlaceCard (K := K) S := by
  let F :=
    Fin (SUnitGroup.logRank (K := K) S) →₀ ℤ
  let _ : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have hfree :
      Nat.card
          (Multiplicative F ⧸
            (powMonoidHom (n : ℕ) :
              Multiplicative F →* Multiplicative F).range) =
        (n : ℕ) ^ SUnitGroup.logRank (K := K) S := by
    have htransport :=
      LocalFieldTheory.card_multiplicative_nthPowerQuotient_eq_additive_nsmulQuotient
        F (n : ℕ)
    rw [htransport]
    exact card_finsupp_nsmulQuotient
      (SUnitGroup.logRank (K := K) S) n
  have hplace :
      totalPlaceCard (K := K) S =
        SUnitGroup.logRank (K := K) S + 1 := by
    unfold totalPlaceCard SUnitGroup.logRank
    have hinfinite :
        0 < Fintype.card (InfinitePlace K) :=
      Fintype.card_pos
    omega
  calc
    Nat.card
        (SUnitGroup (K := K) S ⧸
          (powMonoidHom (n : ℕ) :
            SUnitGroup (K := K) S →*
              SUnitGroup (K := K) S).range) =
        Nat.card
          ((NumberField.Units.torsion K × Multiplicative F) ⧸
            (powMonoidHom (n : ℕ) :
              NumberField.Units.torsion K × Multiplicative F →*
                NumberField.Units.torsion K ×
                  Multiplicative F).range) := by
      exact Nat.card_congr
        (LocalFieldTheory.nthPowerQuotientEquivOfMulEquiv
          (SUnitGroup (K := K) S)
          (NumberField.Units.torsion K × Multiplicative F)
          (n : ℕ)
          (SUnitGroup.decomposition (K := K) S)).toEquiv
    _ =
        Nat.card
          ((NumberField.Units.torsion K ⧸
              (powMonoidHom (n : ℕ) :
                NumberField.Units.torsion K →*
                  NumberField.Units.torsion K).range) ×
            (Multiplicative F ⧸
              (powMonoidHom (n : ℕ) :
                Multiplicative F →* Multiplicative F).range)) := by
      exact Nat.card_congr
        (LocalFieldTheory.nthPowerProductQuotientEquiv
          (NumberField.Units.torsion K) (Multiplicative F)
          (n : ℕ)).toEquiv
    _ =
        (n : ℕ) *
          (n : ℕ) ^ SUnitGroup.logRank (K := K) S := by
      rw [Nat.card_prod,
        card_numberField_torsion_nthPowerQuotient (K := K) n hmu,
        hfree]
    _ = (n : ℕ) ^ totalPlaceCard (K := K) S := by
      rw [hplace, pow_succ']
end KummerTheory
end
end

open NumberField IsDedekindDomain
open scoped NumberField Classical
theorem TunnellGroupedPart3.result : TunnellGroupedPart3.Statement := by
  intro K _ _ p hp hmu F
  change Nat.card (SUnitGroup (K:=K) F ⧸ (powMonoidHom p : SUnitGroup (K:=K) F →* SUnitGroup (K:=K) F).range) = _
  have h:=KummerTheory.card_sUnit_nthPowerQuotient (K:=K) F ⟨p,hp.pos⟩ hmu
  change Nat.card (SUnitGroup (K:=K) F ⧸ (powMonoidHom p : SUnitGroup (K:=K) F →* SUnitGroup (K:=K) F).range) = p^(Fintype.card (InfinitePlace K)+F.card) at h
  rw [Nat.card_eq_fintype_card (α:=InfinitePlace K)]
  exact h
end

theorem OMA.solution : OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1.H2 :=
  ⟨TunnellGroupedPart1.result, TunnellGroupedPart2.result, TunnellGroupedPart3.result⟩
