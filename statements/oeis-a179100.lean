import Mathlib

/-!
# A179100: a(n) = (1/n) * Sum_{k=0..n-1} (8k+5) T_k^2

Source: https://oeis.org/A179100

`T_k` is the central trinomial coefficient (A002426), the coefficient of `x^k` in `(1 + x + x^2)^k`,
equal to `Sum_{j=0..floor(k/2)} C(k,2j) C(2j,j)`. Offset 1: `a(n) = (1/n) Sum_{k=0..n-1} (8k+5) T_k^2`.

Conjecture (Zhi-Wei Sun, Jun 17 2010): `a(n)` is an integer for every `n >= 1`, and
`a(p) == 3 (p/3) (mod p)` for every prime `p`, with `(p/3)` the Legendre symbol.
The further identity Sun observed in the same comment is not part of this target.

Formalized: `T k` is the finite sum above, in `ℤ`. `S n = Sum_{k<n} (8k+5) (T k)^2` in `ℤ`.
Integrality is `(n : ℤ) ∣ S n` for `n >= 1`. Then `a n = S n / n` (integer division, exact by the first
part), and the congruence is `(p : ℤ) ∣ a p - 3 * jacobiSym p 3`; for the prime `3` the Jacobi symbol
`jacobiSym p 3` is the Legendre symbol `(p/3)`, which is `0` at `p = 3`. The two claims form a conjunction.
-/

namespace OMA.S_oeis_a179100

/-- Central trinomial coefficient `T k = Sum_{j=0..k/2} C(k,2j) C(2j,j)` (A002426). -/
def T (k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k / 2 + 1), ((Nat.choose k (2 * j) * Nat.choose (2 * j) j : ℕ) : ℤ)

/-- `S n = Sum_{k=0..n-1} (8k+5) T_k^2`. -/
def S (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n, (8 * (k : ℤ) + 5) * T k ^ 2

/-- A179100: `a(n) = S(n) / n`. -/
def a (n : ℕ) : ℤ := S n / (n : ℤ)

/-- Sun's conjecture: `n ∣ S(n)` for all `n >= 1`, and `a(p) == 3 (p/3) (mod p)` for all primes `p`. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (n : ℤ) ∣ S n) ∧
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ a p - 3 * jacobiSym (p : ℤ) 3) := by
  sorry

end OMA.S_oeis_a179100
