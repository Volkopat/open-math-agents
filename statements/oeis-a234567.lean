import Mathlib

/-!
# A234567: Number of ways to write n = k + m with k > 0 and m > 0 such that p = phi(k) + phi(m)/2 + 1 and P(p-1) are both prime

Source: https://oeis.org/A234567
Credit: @gblacher2

The sequence: `a(n)` is the number of ways to write `n = k + m` with `k > 0` and `m > 0` such
that `p = phi(k) + phi(m)/2 + 1` and `P(p-1)` are both prime, where `phi` is Euler's totient
function and `P` is the partition function (A000041).

Conjecture (Zhi-Wei Sun, A234567): "(i) a(n) > 0 for all n > 727." This file states part (i),
the problem listed on the Left to Solve page; parts (ii) and (iii) of the OEIS comment are
separate assertions and are not included.

Conventions: `P(m)` is the number of partitions of `m`, `Fintype.card (Nat.Partition m)`
(1, 1, 2, 3, 5, 7, … for `m = 0, 1, 2, …`). Since `phi(k)` is an integer, `p` is an integer
(a necessary condition for being prime) exactly when `2 ∣ phi(m)`, and then
`p = phi(k) + phi(m) / 2 + 1` with natural-number division; this matches the OEIS Mathematica
program, where `PrimeQ` is false at non-integers. Since `p ≥ 1`, natural-number subtraction in
`p - 1` is exact. A representation `n = k + m` with `k, m > 0` is determined by `k ∈ (0, n)`
with `m = n - k`. With these conventions the values for `n = 1, …, 12` are
`0, 0, 0, 1, 2, 1, 1, 3, 2, 2, 3, 2`, the first 2500 values agree with the OEIS b-file, and
`727` is the largest `n ≤ 2500` with `a(n) = 0`.
-/

namespace OMA.S_oeis_a234567

/-- The partition function A000041: the number of partitions of `m`. -/
def P (m : ℕ) : ℕ := Fintype.card (Nat.Partition m)

/-- The condition on `k` for a given `n` (with `m = n - k`): `p = phi(k) + phi(m)/2 + 1` is an
integer (that is, `2 ∣ phi(m)`), and `p` and `P(p-1)` are both prime. -/
def Good (n k : ℕ) : Prop :=
  2 ∣ Nat.totient (n - k) ∧
    (Nat.totient k + Nat.totient (n - k) / 2 + 1).Prime ∧
    (P (Nat.totient k + Nat.totient (n - k) / 2 + 1 - 1)).Prime

open Classical in
/-- `a n = |{0 < k < n : Good n k}|`, the number of ways to write `n = k + m` with
`k > 0`, `m > 0` as required. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 n).filter (fun k => Good n k)).card

/-- Conjecture (i): `a(n) > 0` for all `n > 727`. -/
theorem main : ∀ n : ℕ, 727 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a234567
