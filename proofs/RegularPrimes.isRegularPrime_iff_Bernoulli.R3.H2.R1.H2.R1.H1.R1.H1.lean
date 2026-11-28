import OMAReductions.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1_H2_R1_H1_R1
import Mathlib

/-! Direct integral specialization proof for the Kummer jet formulation of the
parent reduction (following Hanan Beer and Brasca et al., KummerCriterion). -/
open NumberField Polynomial
open scoped NumberField BigOperators
noncomputable section
namespace KummerJetProof
variable (p : ℕ) [Fact p.Prime]
private abbrev F := (X : (ZMod p)[X]) ^ (p-1)
private abbrev J := AdjoinRoot (F p)
private abbrev x : J p := AdjoinRoot.root _
private theorem nilp : x p ^ (p-1) = 0 := by
  simpa only [F, map_pow, AdjoinRoot.mk_X] using (AdjoinRoot.mk_self (f:=F p))
private theorem nilp' : x p ^ p = 0 := by
  exact pow_eq_zero_of_le (Nat.sub_le ..) (nilp p)
private instance : CharP (J p) p :=
  charP_of_injective_ringHom (AdjoinRoot.of.injective_of_degree_ne_zero (f:=F p) (by
    have hp := (Fact.out : Nat.Prime p).two_le
    simp [F, show p-1 ≠ 0 by omega])) p
private theorem constant (a : J p) : ∃ c : ZMod p, a ^ p = algebraMap _ _ c := by
  obtain ⟨f,rfl⟩ := AdjoinRoot.mk_surjective a
  induction f using Polynomial.induction_on' with
  | add f g ih jh =>
    obtain ⟨c,hc⟩ := ih
    obtain ⟨d,hd⟩ := jh
    exact ⟨c+d, by rw [map_add, add_pow_char, hc, hd, map_add]⟩
  | monomial n c =>
    cases n with
    | zero => exact ⟨c^p, by rw [monomial_zero_left, AdjoinRoot.mk_C, map_pow]; rfl⟩
    | succ n => refine ⟨0, ?_⟩; simp [← C_mul_X_pow_eq_monomial, pow_succ, mul_pow, AdjoinRoot.mk_X, show AdjoinRoot.root (F p) ^ p = 0 from nilp' p] 
private theorem specialize {K : Type*} [Field K] [CharZero K] [IsCyclotomicExtension {p} ℚ K]
    {z : K} (hz : IsPrimitiveRoot z p) : ∃ q : 𝓞 K →+* J p, q hz.toInteger = 1 + x p := by
  let b := hz.integralPowerBasis
  have hm : minpoly ℤ b.gen = cyclotomic p ℤ := by
    rw [show b.gen = _ from hz.integralPowerBasis_gen, cyclotomic_eq_minpoly hz (Fact.out : Nat.Prime p).pos]
    exact (minpoly.algHom_eq (IsScalarTower.toAlgHom ℤ (𝓞 K) K) Subtype.val_injective hz.toInteger).symm
  have he : aeval (1 + x p) (minpoly ℤ b.gen) = 0 := by
    rw [hm, ← aeval_map_algebraMap (ZMod p)]
    change aeval (1 + x p) (Polynomial.map (Int.castRingHom (ZMod p)) (cyclotomic p ℤ)) = 0
    rw [map_cyclotomic_int]
    have heq := cyclotomic_mul_prime_eq_pow_of_not_dvd (ZMod p) (n:=1) (p:=p) (Nat.Prime.not_dvd_one Fact.out)
    rw [one_mul, cyclotomic_one] at heq
    simp [heq, nilp]
  exact ⟨(b.lift _ he).toRingHom, by change b.lift _ he _ = _; rw [← hz.integralPowerBasis_gen]; exact b.lift_gen _ he⟩
theorem solution : OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1_H2_R1_H1_R1.H1 := by
  classical
  intro p hp h5
  let K := CyclotomicField p ℚ
  let L := maximalRealSubfield K
  let _ : IsCyclotomicExtension {p} ℚ K := CyclotomicField.isCyclotomicExtension p ℚ
  let z := IsCyclotomicExtension.zeta p ℚ K
  have hz : IsPrimitiveRoot z p := IsCyclotomicExtension.zeta_spec p ℚ K
  let m := (p-3)/2
  let t := 1 + x p
  let G (a : Fin m) := (∑ i ∈ Finset.range (a.val + 2), t ^ i) *
    (∑ i ∈ Finset.range (a.val + 2), (t ^ (p - 1)) ^ i)
  dsimp only
  intro g hg s e u hu
  obtain ⟨q,hq⟩ := specialize p hz
  let f := q.comp (algebraMap (𝓞 L) (𝓞 K))
  have hinv : z ^ (p-1) = z⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, show p-1+1=p by omega, hz.pow_eq_one]
  have hg' (a : Fin m) : f (g a) = G a := by
    have hint : algebraMap (𝓞 L) (𝓞 K) (g a) =
        (∑ i ∈ Finset.range (a.val+2), hz.toInteger ^ i) *
        (∑ i ∈ Finset.range (a.val+2), (hz.toInteger ^ (p-1)) ^ i) := by
      apply (IsFractionRing.injective (𝓞 K) K)
      rw [← IsScalarTower.algebraMap_apply, map_mul, map_sum, map_sum]
      simpa only [map_pow, show algebraMap (𝓞 K) K hz.toInteger = z from rfl, hinv] using hg a
    change q _ = _
    rw [hint, map_mul, map_sum, map_sum]
    simp only [map_pow, hq, G, t]
  let P := ∏ a, g a ^ (e a).toNat
  let N := ∏ a, g a ^ (-e a).toNat
  have hc : (∏ a, g a ^ e a) * N = P := by
    rw [show N = _ from rfl, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro a _
    rw [← zpow_natCast, ← zpow_add, ← zpow_natCast]; congr 1; omega
  have hclear : P = (-1)^(-s) * u^p * N := by
    rw [hu, ← hc]; group
  obtain ⟨c, hc'⟩ := constant p (f u)
  have heq := congrArg (fun v : (𝓞 L)ˣ => f (v : 𝓞 L)) hclear
  by_cases hs : Even (-s)
  · refine ⟨c, ?_⟩
    simpa [P, N, hs.neg_one_zpow, hg', hc', G, t] using heq
  · refine ⟨-c, ?_⟩
    have hsign : (-1 : (𝓞 L)ˣ)^(-s) = -1 := by rw [neg_one_zpow_eq_ite, if_neg hs]
    simpa [P, N, hsign, hg', hc', G, t] using heq

end KummerJetProof

theorem OMA.solution : OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1_H2_R1_H1_R1.H1 := KummerJetProof.solution
