import OMAReductions.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1_H2_R1
import Mathlib

/-! A characteristic-p jet reduction of the weighted Kummer congruence.
The parent formulation follows Hanan Beer and Brasca et al. (KummerCriterion,
Apache-2.0).  The two interfaces here separate reduction of integral units
modulo p from the finite polynomial logarithmic-coefficient computation. -/
namespace OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1_H2_R1_H1_R1
open NumberField
open scoped NumberField BigOperators

/-- A cyclotomic power relation becomes constant modulo (zeta - 1)^(p-1).
Clear negative exponents so the equality needs no inverses in the jet ring. -/
def H1 : Prop := ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p →
  let K := CyclotomicField p ℚ
  let L := maximalRealSubfield K
  let _ : IsCyclotomicExtension {p} ℚ K := CyclotomicField.isCyclotomicExtension p ℚ
  let z := IsCyclotomicExtension.zeta p ℚ K
  let m := (p - 3) / 2
  let R := AdjoinRoot ((Polynomial.X : Polynomial (ZMod p)) ^ (p - 1))
  let t : R := 1 + AdjoinRoot.root _
  let G : Fin m → R := fun a =>
    (∑ i ∈ Finset.range (a.val + 2), t ^ i) *
    (∑ i ∈ Finset.range (a.val + 2), (t ^ (p - 1)) ^ i)
  ∀ g : Fin m → (𝓞 L)ˣ,
    (∀ a, algebraMap (𝓞 L) K (g a : 𝓞 L) =
      (∑ i ∈ Finset.range (a.val + 2), z ^ i) *
        (∑ i ∈ Finset.range (a.val + 2), (z⁻¹) ^ i)) →
    ∀ (s : ℤ) (e : Fin m → ℤ) (u : (𝓞 L)ˣ),
      u ^ p = (-1) ^ s * ∏ a, g a ^ e a →
      ∃ c : ZMod p, (∏ a, G a ^ (e a).toNat) =
        (algebraMap (ZMod p) R c) * ∏ a, G a ^ (-e a).toNat

/-- Finite jet identity: constancy of the signed product kills every even
logarithmic coefficient. In exponential coordinates those coefficients are
Bernoulli multiples of the even moments of the exponents. -/
def H2 : Prop := ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p →
  let m := (p - 3) / 2
  let R := AdjoinRoot ((Polynomial.X : Polynomial (ZMod p)) ^ (p - 1))
  let t : R := 1 + AdjoinRoot.root _
  let G : Fin m → R := fun a =>
    (∑ i ∈ Finset.range (a.val + 2), t ^ i) *
    (∑ i ∈ Finset.range (a.val + 2), (t ^ (p - 1)) ^ i)
  ∀ e : Fin m → ℤ,
    (∃ c : ZMod p, (∏ a, G a ^ (e a).toNat) =
        (algebraMap (ZMod p) R c) * ∏ a, G a ^ (-e a).toNat) → ∀ j : Fin m,
      ((bernoulli (2 * (j.val + 1))).num : ZMod p) *
        (∑ a : Fin m, (((a.val + 2 : ℕ) : ZMod p) ^ (2 * (j.val + 1)) - 1) *
          (e a : ZMod p)) = 0

theorem main : H1 → H2 → OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1_H2_R1.H1 := by
  intro hj hc p hp h5
  dsimp only
  intro g hg s e u hu
  exact hc p h5 e (hj p h5 g hg s e u hu)

end OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1_H2_R1_H1_R1
