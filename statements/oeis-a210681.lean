import Mathlib

/-!
# A210681: Number of ways to write 2n = p+q+r (p<=q) with p, q, r-1, r+1 all prime and p-1, p+1, q-1, q+1, r all practical.

Source: https://oeis.org/A210681
Credit: @darealpandaboi

Conjecture (Zhi-Wei Sun): a(n) > 0 for all n > 4 (verified for n up to 10^7).

Translation notes.
* A practical number (A005153) is a positive integer x such that every smaller nonnegative
  integer is a sum of distinct divisors of x (0 is the empty sum).
* a(n) > 0 means there are p <= q and r with 2n = p + q + r, p, q, r - 1, r + 1 prime and
  p - 1, p + 1, q - 1, q + 1, r practical. Since r + 1 and r - 1 are prime, r >= 3, so r - 1 is
  exact; p, q >= 2 make p - 1, q - 1 exact.
* The further conjectures listed on the page are not included.
* This reading reproduces the listed data a(1..14) = 0, 0, 0, 0, 1, 2, 3, 3, 3, 2, 2, 3, 5, 6
  (checked by computer).
-/

namespace OMA.S_oeis_a210681

/-- x is practical: every m < x is a sum of distinct divisors of x. -/
def IsPractical (x : ℕ) : Prop :=
  0 < x ∧ ∀ m : ℕ, m < x → ∃ s ⊆ x.divisors, ∑ d ∈ s, d = m

theorem main : ∀ n : ℕ, 4 < n → ∃ p q r : ℕ, p ≤ q ∧ 2 * n = p + q + r ∧
    p.Prime ∧ q.Prime ∧ (r - 1).Prime ∧ (r + 1).Prime ∧
    IsPractical (p - 1) ∧ IsPractical (p + 1) ∧ IsPractical (q - 1) ∧ IsPractical (q + 1) ∧
    IsPractical r := by
  sorry

end OMA.S_oeis_a210681
