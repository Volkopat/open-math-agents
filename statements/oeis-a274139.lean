import Mathlib

/-!
# A274139: a(n) = 2*A082392(n)^2 fails at n = 2

Source: https://oeis.org/A274139
Credit: @ivillar

A274139: a(n) = 2^A000265(n) = 2^numerator(n/2^n), a sequence related to Oresme numbers
(offset 1; data 2, 2, 8, 2, 32, 8, 128, 2, 512, 32, ...). The entry's formula section records
a(n) = 2*A082392(n)^2 (conjecture), where A082392 (offset 0; data 1, 1, 2, 1, 4, 2, 8, 1, ...) is
the expansion of (1/x) * Sum_{k>=0} x^(2^k) / (1 - 2*x^(2^(k+1))).

Status: false as stated (counterexample n = 2: a(2) = 2^1 = 2, while
2*A082392(2)^2 = 2*2^2 = 8); kept as the target of a disproof. The data agree with the shifted
identity a(n) = 2*A082392(n-1)^2 (n >= 1), which is not the statement recorded in the entry.

Formalization notes:
* A000265(n) is the odd part of n, written `n / 2 ^ (n.factorization 2)`; it equals
  numerator(n/2^n) for n >= 1.
* (1/x) * x^(2^k) / (1 - 2*x^(2^(k+1))) = Sum_{j>=0} 2^j * x^(2^k*(2j+1) - 1), so A082392(n) is the
  sum of 2^j over the pairs (k, j) with 2^k * (2j+1) = n + 1; both k and j are at most n + 1,
  which gives the finite double sum `b`.
* The identity is stated for every n >= 1 (the offset of A274139), in ℕ.
-/

namespace OMA.S_oeis_a274139

/-- A000265(n): the odd part of `n`. -/
def oddPart (n : ℕ) : ℕ := n / 2 ^ (n.factorization 2)

/-- A274139(n) = 2^A000265(n). -/
def a (n : ℕ) : ℕ := 2 ^ oddPart n

/-- A082392(n): the coefficient of `x^n` in `(1/x) * Σ_{k ≥ 0} x^(2^k) / (1 - 2 x^(2^(k+1)))`,
i.e. the sum of `2^j` over the ways to write `n + 1 = 2^k * (2j + 1)`. -/
def b (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 2), ∑ j ∈ Finset.range (n + 2),
    if 2 ^ k * (2 * j + 1) = n + 1 then 2 ^ j else 0

/-- The formula recorded (as a conjecture) in A274139: a(n) = 2*A082392(n)^2 for n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = 2 * b n ^ 2 := by
  sorry

end OMA.S_oeis_a274139
