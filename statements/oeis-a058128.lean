import Mathlib

/-!
# A058128: a(1) = 1, a(n) = (n^n-n)/(n-1)^2 for n >= 2.

Source: https://oeis.org/A058128
Credit: @eitanteperman

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a058128

/-- A058128: a(1) = 1, a(n) = (n^n - n)/(n-1)^2 for n >= 2 (exact division). -/
def a (n : ℕ) : ℕ := if n = 1 then 1 else (n ^ n - n) / (n - 1) ^ 2

/-- `m` is a weak Fermat pseudoprime to base `b`: `m` is composite and `b ^ m ≡ b (mod m)`. -/
def IsWeakFermatPseudoprime (b m : ℕ) : Prop :=
  1 < m ∧ ¬ m.Prime ∧ b ^ m ≡ b [MOD m]

/-- Conjecture (Davide Rotondo, Nov 2024): for even n, a(n) is prime or a weak Fermat pseudoprime to
base n. -/
theorem main : ∀ n : ℕ, 2 ≤ n → Even n → (a n).Prime ∨ IsWeakFermatPseudoprime n (a n) := by
  sorry

end OMA.S_oeis_a058128
