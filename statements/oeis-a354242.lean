import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Nat.Totient

/-!
# Eventual periods of OEIS A354242 and integral exponential generating functions

Peter Bala proposed both assertions in the OEIS entry on July 7, 2022.
Source: https://oeis.org/A354242
Credit: @DomTheDeveloper
-/

namespace OMA.S_oeis_a354242

/-- The coefficient of `x^n / n!` in `G(exp(x) - 1)`, where `g j` is the
ordinary coefficient of `x^j` in the integral power series `G`. The
Stirling coefficient of `(exp(x) - 1)^j` is `j! * S(n,j)`. -/
def egfSequence (g : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1),
    g j * (j.factorial : ℤ) * (Nat.stirlingSecond n j : ℤ)

/-- OEIS A354242, with exponential generating function `1 / sqrt(5 - 4 * exp(x))`.
Its OEIS expansion uses the central binomial coefficients for `G`. -/
def a : ℕ → ℤ := egfSequence (fun j => (Nat.choose (2 * j) j : ℤ))

/-- For every positive modulus there is a positive period of the tail dividing its totient. -/
def totientPeriod (s : ℕ → ℤ) : Prop :=
  ∀ k : ℕ, 0 < k →
    ∃ d : ℕ, 0 < d ∧ d ∣ k.totient ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → s (n + d) % (k : ℤ) = s n % (k : ℤ)

theorem main :
    totientPeriod a ∧ ∀ g : ℕ → ℤ, totientPeriod (egfSequence g) := by
  sorry

end OMA.S_oeis_a354242
