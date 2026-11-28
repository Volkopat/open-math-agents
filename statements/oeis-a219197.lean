import Mathlib

/-!
# A219197: Self-convolution equals A199033.

Source: https://oeis.org/A219197
Credit: @luciusacarr

Data: 1, 2, 9, 46, 253, 1452, 8570, 51594, 315225, 1948010, ... (offset 0).

Conjecture (from the entry): a(n) is never congruent to 3 modulo 4. `main` states it.

Reading of the source:
* A199033(n) = Sum_{k=0..n} C(n+k+1, n-k) * C(2n-k+1, k) (the entry's formula; 1, 4, 22, 128,
  ...).
* The sequence is the one whose self-convolution is A199033: Sum_{k=0..n} a(n-k) a(k) =
  A199033(n) for all n ≥ 0, with a(0) = 1 (the convolution identity determines a(0) only up to
  sign, and determines every later term from the earlier ones). `main` quantifies over every
  integer sequence with these two properties; the listed data show that one exists (the first
  terms were recomputed from this definition).
* "Never congruent to 3 modulo 4" is required for every index n ≥ 0.
-/

namespace OMA.S_oeis_a219197

/-- A199033(n) = Sum_{k=0..n} C(n+k+1, n-k) C(2n-k+1, k). -/
def A199033 (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), Nat.choose (n + k + 1) (n - k) * Nat.choose (2 * n - k + 1) k

theorem main :
    -- a(n) is never congruent to 3 modulo 4.
    ∀ a : ℕ → ℤ, a 0 = 1 →
      (∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), a (n - k) * a k = (A199033 n : ℤ)) →
      ∀ n : ℕ, a n % 4 ≠ 3 := by
  sorry

end OMA.S_oeis_a219197
