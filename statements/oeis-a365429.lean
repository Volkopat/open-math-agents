import Mathlib

/-!
# A365429: a(n) = 1 if the divisors of n increase by a factor of at most 2, otherwise 0.

Source: https://oeis.org/A365429
Credit: @ceejcake

Conjecture (OEIS A365429, formula section; the entry is by Antti Karttunen, Oct 22 2023):
`a(n) <= A322860(n). [Conjectured, see comment in A174973]`. The comment in A174973 says that
every term of A174973 appears to be a practical number (A005153).

Formalization notes:
* Both sequences have offset `1`, so the claim is stated for `n : ℕ` with `1 ≤ n`.
* `IsDense n` says that the divisors of `n`, listed in increasing order, have consecutive ratios at
  most `2`. It is stated as: every divisor `d` of `n` with `d < n` has a divisor `e` of `n` with
  `d < e ≤ 2 * d`. This is equivalent, because the next divisor after `d` is the least divisor
  of `n` above `d`. This matches the PARI program of A365429.
* `IsPractical n` is the definition in the name of A005153: every `k ≤ σ(n)` is a sum of distinct
  divisors of `n`, that is, the sum of some subset of `n.divisors`. Here `σ(n)` is
  `ArithmeticFunction.sigma 1 n`, and the empty subset gives `k = 0`.
* `a n` is A365429 and `b n` is A322860, the characteristic function of A005153.
* Initial values for `n = 1, ..., 12`: `a(n) = 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1`, and
  `b(n)` agrees with these; the first `n` with `a(n) < b(n)` is `n = 78`.
-/

namespace OMA.S_oeis_a365429

/-- The divisors of `n` increase by a factor of at most `2`: every divisor `d < n` of `n` is
followed by a divisor `e` of `n` with `d < e ≤ 2 * d`. -/
def IsDense (n : ℕ) : Prop :=
  ∀ d ∈ n.divisors, d < n → ∃ e ∈ n.divisors, d < e ∧ e ≤ 2 * d

instance (n : ℕ) : Decidable (IsDense n) := by
  unfold IsDense; infer_instance

/-- `n` is practical (A005153): every `k ≤ σ(n)` is a sum of distinct divisors of `n`. -/
def IsPractical (n : ℕ) : Prop :=
  ∀ k ≤ ArithmeticFunction.sigma 1 n, ∃ s ∈ n.divisors.powerset, ∑ d ∈ s, d = k

instance (n : ℕ) : Decidable (IsPractical n) := by
  unfold IsPractical; infer_instance

/-- A365429: `a n = 1` if the divisors of `n` increase by a factor of at most `2`, else `0`. -/
def a (n : ℕ) : ℕ := if IsDense n then 1 else 0

/-- A322860: the characteristic function of the practical numbers A005153. -/
def b (n : ℕ) : ℕ := if IsPractical n then 1 else 0

/-- OEIS A365429 conjecture: `a(n) ≤ A322860(n)` for every `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n ≤ b n := by
  sorry

end OMA.S_oeis_a365429
