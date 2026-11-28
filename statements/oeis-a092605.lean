import Mathlib

/-!
# OEIS A092605: Siegel's conjecture on the density of regular primes

Source: https://oeis.org/A092605 (decimal expansion of `e^(-1/2)`)
Siegel's conjecture: `e^(-1/2)` is the density of regular primes among all primes.

Conventions. An odd prime `p` is regular if it divides none of the numerators of the
Bernoulli numbers `B_2, B_4, …, B_{p-3}` (Kummer's criterion, equivalent to `p ∤ h(ℚ(ζ_p))`);
`2` is not counted. Bernoulli numbers are Mathlib's `bernoulli`. The density is the limit of
`#{regular p ≤ x} / π(x)`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a092605

open Filter Topology Real

/-- `p` is an odd regular prime (Kummer's criterion). -/
def IsRegularPrime (p : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ ∀ k ∈ Finset.Icc 1 ((p - 3) / 2), ¬ (p : ℤ) ∣ (bernoulli (2 * k)).num

theorem main :
    Tendsto (fun x : ℕ =>
        (Set.ncard {p : ℕ | p ≤ x ∧ IsRegularPrime p} : ℝ) /
          ((Finset.range (x + 1)).filter Nat.Prime).card) atTop (𝓝 (exp (-1 / 2))) := by
  sorry

end OMA.S_oeis_a092605
