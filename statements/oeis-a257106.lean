import Mathlib

/-!
# A257106: denominators of the inverse binomial transform of the Bernoulli numbers with B(1)=2/3

Source: https://oeis.org/A257106 (conjectures in the entry, Paul Curtz, 2015)

Let `b(k)` be the Bernoulli numbers with `B(1)` replaced by `2/3`: `b(1) = 2/3` and
`b(k) = bernoulli k` otherwise (Mathlib's `bernoulli`, with `B(1) = -1/2`, is used only for
`k ≠ 1`, where the two conventions agree). Their inverse binomial transform is
`c(n) = Sum_{k=0..n} (-1)^(n-k) * binomial(n,k) * b(k)`, and `a(n)` (offset 0) is the
denominator of the rational number `c(n)` (in lowest terms, `Rat.den`). `A002445(n)` is the
denominator of `B(2n)`.

Conjecture 1: `a(2n+1)` is `3` followed by the period 3 sequence `2, 6, 6`, i.e. `a(1) = 3` and,
for `n >= 1`, `a(2n+1) = 2` if `n == 1 (mod 3)` and `6` otherwise.
Conjecture 2: `a(2n) = A002445(n)/(period 3: repeat 1, 1, 3)`, i.e. `a(2n) = A002445(n)/3` if
`n == 2 (mod 3)` and `a(2n) = A002445(n)` otherwise; the quotient is taken in `ℚ`.
-/

namespace OMA.S_oeis_a257106

/-- The Bernoulli numbers with `B(1) = 2/3`. -/
def b (k : ℕ) : ℚ := if k = 1 then 2 / 3 else bernoulli k

/-- The inverse binomial transform of `b`. -/
def c (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (n - k) * (n.choose k : ℚ) * b k

/-- A257106: the denominator of `c(n)`. -/
def a (n : ℕ) : ℕ := (c n).den

/-- A002445: the denominator of `B(2n)`. -/
def A002445 (n : ℕ) : ℕ := (bernoulli (2 * n)).den

theorem main :
    (∀ n : ℕ, a (2 * n + 1) = if n = 0 then 3 else if n % 3 = 1 then 2 else 6) ∧
    (∀ n : ℕ, (a (2 * n) : ℚ) = (A002445 n : ℚ) / (if n % 3 = 2 then 3 else 1)) := by
  sorry

end OMA.S_oeis_a257106
