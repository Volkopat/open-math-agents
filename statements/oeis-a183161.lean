import Mathlib

/-!
# A183161: Self-convolution equals A183160.

Source: https://oeis.org/A183161
Credit: @luciusacarr

Data: 1, 1, 5, 26, 145, 841, 5006, 30350, 186537, 1158685, ... (offset 0).

Conjecture (Paul D. Hanna, Nov 03 2012): a(n) is never congruent to 3 modulo 4; see A218622.
`main` states it.

Reading of the source:
* A183160(n) = Sum_{k=0..n} C(n+k, n-k) * C(2n-k, k) (the entry's formula; 1, 2, 11, 62, ...).
* The sequence is the one whose self-convolution is A183160: Sum_{k=0..n} a(n-k) a(k) =
  A183160(n) for all n ≥ 0, with a(0) = 1 (the convolution identity determines a(0) only up to
  sign, and determines every later term from the earlier ones: 2 a(0) a(n) = A183160(n) - ...).
  `main` quantifies over every integer sequence with these two properties, so it says the claim
  of every such sequence; the listed data show that one exists.
* "Never congruent to 3 modulo 4" is required for every index n ≥ 0.
-/

namespace OMA.S_oeis_a183161

/-- A183160(n) = Sum_{k=0..n} C(n+k, n-k) C(2n-k, k). -/
def A183160 (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), Nat.choose (n + k) (n - k) * Nat.choose (2 * n - k) k

theorem main :
    -- a(n) is never congruent to 3 modulo 4.
    ∀ a : ℕ → ℤ, a 0 = 1 →
      (∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), a (n - k) * a k = (A183160 n : ℤ)) →
      ∀ n : ℕ, a n % 4 ≠ 3 := by
  sorry

end OMA.S_oeis_a183161
