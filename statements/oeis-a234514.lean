import Mathlib

/-!
# A234514: Number of ways to write n = k + m with k > 0 and m > 0 such that p = k + phi(m)/2 and q(p) + 1 are both prime

Source: https://oeis.org/A234514
Credit: @gblacher2

The sequence: `a(n)` is the number of ways to write `n = k + m` with `k > 0` and `m > 0` such
that `p = k + phi(m)/2` and `q(p) + 1` are both prime, where `phi` is Euler's totient function
and `q` is the strict partition function (A000009).

Conjecture (Zhi-Wei Sun, A234514):
(i) `a(n) > 0` for all `n > 12`.
(ii) For any integer `n > 4`, there is a prime `p < n - 2` such that `q(p + phi(n-p)/2) + 1` is
prime.

Conventions: `q(m)` is the cardinality of Mathlib's finset `Nat.Partition.distincts m`, the
number of partitions of `m` into distinct parts (1, 1, 1, 2, 2, 3, 4, 5, … for `m = 0, 1, 2, …`).
A way `n = k + m` is determined by `k` with `0 < k < n` and `m = n - k`. In (i), `p = k + phi(m)/2`
must be a prime, hence an integer, so `phi(m)` must be even; this is written `2 ∣ phi(m)`, and
then `phi(m) / 2` in `ℕ` is exact. (This excludes `m = 1, 2`, where `phi(m) = 1`; with this reading
`a(4) = 1`, as in the OEIS data, and the first 100 values agree with the OEIS data.) In (ii),
`p < n - 2` gives `n - p ≥ 3`, so `phi(n-p)` is even and `phi(n-p) / 2` in `ℕ` is exact.
-/

namespace OMA.S_oeis_a234514

/-- The strict partition function A000009: the number of partitions of `m` into distinct
parts. -/
def q (m : ℕ) : ℕ := (Nat.Partition.distincts m).card

/-- The condition on the way `n = k + m`: `p = k + phi(m)/2` is an integer prime and
`q(p) + 1` is prime. -/
def Good (k m : ℕ) : Prop :=
  2 ∣ Nat.totient m ∧ (k + Nat.totient m / 2).Prime ∧ (q (k + Nat.totient m / 2) + 1).Prime

open Classical in
/-- `a n`: the number of `k` with `0 < k < n` (so `m = n - k > 0`) such that `Good k (n - k)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 n).filter (fun k => Good k (n - k))).card

/-- Sun's conjecture, parts (i) and (ii). -/
theorem main :
    (∀ n : ℕ, 12 < n → 0 < a n) ∧
    (∀ n : ℕ, 4 < n → ∃ p : ℕ, p.Prime ∧ p < n - 2 ∧
      (q (p + Nat.totient (n - p) / 2) + 1).Prime) := by
  sorry

end OMA.S_oeis_a234514
