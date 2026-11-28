import Mathlib

/-!
# A392667: least modulus separating tau(k)*(tau(k)-1), k = 1..n

Source: https://oeis.org/A392667 (see also https://oeis.org/A000594)
Credit: @gblacher2

A392667 (Zhi-Wei Sun), offset 1: a(n) is the least positive integer m such that
tau(k)*(tau(k)-1) (k = 1..n) are incongruent modulo m, where tau(.) is Ramanujan's tau function.
Conjecture (in the entry): a(n) is prime except for n = 1, 37.

Conventions:
* Ramanujan's tau function is given by `q * ∏_{d ≥ 1} (1 - q^d)^24 = ∑_{k ≥ 1} tau(k) q^k`
  (A000594). So tau(k) is the coefficient of `X^(k-1)` in `∏_{d=1}^{k} (1 - X^d)^24`; the factors
  with `d ≥ k` do not change that coefficient, so the finite product is exact.
* "incongruent modulo m" means pairwise incongruent: for 1 ≤ i < j ≤ n,
  `c(i) ≢ c(j) (mod m)` with `c(k) = tau(k) * (tau(k) - 1)`.
* "a(n) is prime" is stated as: a least such positive m exists and it is prime.
  The exceptions n = 1 and n = 37 are excluded (a(1) = 1, a(37) = 5^4).
-/

namespace OMA.S_oeis_a392667

open Polynomial

/-- Ramanujan's tau function, `tau(k)` for `k ≥ 1`: the coefficient of `q^k` in
`q * ∏_{d ≥ 1} (1 - q^d)^24`. -/
noncomputable def tau (k : ℕ) : ℤ :=
  (∏ d ∈ Finset.Icc 1 k, ((1 : ℤ[X]) - X ^ d) ^ 24).coeff (k - 1)

/-- `c(k) = tau(k) * (tau(k) - 1)`. -/
noncomputable def c (k : ℕ) : ℤ := tau k * (tau k - 1)

/-- The values `c(1), ..., c(n)` are pairwise incongruent modulo `m`, and `m` is positive. -/
def Separates (n m : ℕ) : Prop :=
  0 < m ∧ ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ n → ¬ c i ≡ c j [ZMOD (m : ℤ)]

/-- For every `n ≥ 1` other than `n = 1` and `n = 37`, the least positive `m` such that
`c(1), ..., c(n)` are pairwise incongruent modulo `m` exists and is prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n → n ≠ 1 → n ≠ 37 →
    ∃ m : ℕ, IsLeast {d : ℕ | Separates n d} m ∧ m.Prime := by
  sorry

end OMA.S_oeis_a392667
