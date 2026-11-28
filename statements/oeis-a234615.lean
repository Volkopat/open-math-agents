import Mathlib

/-!
# A234615: Number of ways to write n = k + m with k > 0 and m > 0 such that p = prime(k) + phi(m) and q(p) - 1 are both prime

Source: https://oeis.org/A234615
Credit: @gblacher2

The sequence: `a(n)` is the number of ways to write `n = k + m` with `k > 0` and `m > 0` such
that `p = prime(k) + phi(m)` and `q(p) - 1` are both prime, where `phi` is Euler's totient
function and `q` is the strict partition function (A000009).

Conjecture (Zhi-Wei Sun, A234615): "(i) a(n) > 0 for all n > 7." This file states part (i),
the problem listed on the Left to Solve page; parts (ii) and (iii) of the OEIS comment are
separate assertions and are not included.

Conventions: `prime(k)` is the `k`-th prime with `prime(1) = 2` (OEIS convention), written
`Nat.nth Nat.Prime (k - 1)`. `q(m)` is the number of partitions of `m` into distinct parts,
the cardinality of Mathlib's finset `Nat.Partition.distincts m` (1, 1, 1, 2, 2, 3, 4, 5, … for
`m = 0, 1, 2, …`); since `q(m) ≥ 1`, natural-number subtraction in `q(p) - 1` is exact.
A representation `n = k + m` with `k, m > 0` is determined by `k ∈ (0, n)` with `m = n - k`.
With these conventions the values for `n = 1, …, 12` are `0, 0, 0, 0, 1, 1, 0, 2, 2, 2, 4, 3`,
and the first 2000 values agree with the OEIS b-file.
-/

namespace OMA.S_oeis_a234615

/-- `prime k`: the `k`-th prime, 1-indexed, so `prime 1 = 2`. -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- The strict partition function A000009: the number of partitions of `m` into distinct
parts. -/
def q (m : ℕ) : ℕ := (Nat.Partition.distincts m).card

/-- The condition on `k` for a given `n` (with `m = n - k`): `p = prime(k) + phi(m)` and
`q(p) - 1` are both prime. -/
def Good (n k : ℕ) : Prop :=
  (prime k + Nat.totient (n - k)).Prime ∧ (q (prime k + Nat.totient (n - k)) - 1).Prime

open Classical in
/-- `a n = |{0 < k < n : Good n k}|`, the number of ways to write `n = k + m` with
`k > 0`, `m > 0` as required. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 n).filter (fun k => Good n k)).card

/-- Conjecture (i): `a(n) > 0` for all `n > 7`. -/
theorem main : ∀ n : ℕ, 7 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a234615
