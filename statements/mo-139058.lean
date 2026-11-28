import Mathlib

/-!
# Does the given operation on pairs of primes always repeat?

Source: https://mathoverflow.net/questions/139058 (2013).
Credit: @jagraj28

For distinct primes `p, q`, the set `A(p, q) = {m + n : m p + n q = 1, m, n ∈ ℤ}` is an
arithmetic progression with step `p - q`, whose terms are coprime to `p - q`; by Dirichlet's
theorem it contains infinitely many primes. Let `f(p, q)` be the first two primes in
`A(p, q)` (for example `f(3, 5) = (3, 5)` and `f(3, 17) = (5, 19)`). The post asks whether
repeatedly applying `f` to a pair of primes always leads to a repetition; the author shows that
a repetition must be a fixed point or a 2-cycle, and tests many pairs. The post has no answer.

Formalization notes:
* The first two primes of `A(p, q)` are its two smallest primes: `first p q` is the least prime
  in `A(p, q)` and `second p q` the least prime in `A(p, q)` greater than it (as in the post's
  Mathematica code, which scans upward from the least positive term).
* `f` maps a pair `(p, q)` to `(first p q, second p q)`, again a pair of distinct primes.
* "Always repeat" is stated as: for distinct primes `p, q`, some two iterates `f^[i] (p, q)` and
  `f^[j] (p, q)` with `i < j` are equal.
* A direct computation reproduces the two examples and finds a repetition within `40` steps for
  every pair of distinct primes below `200`.
-/

namespace OMA.S_mo_139058

/-- `A(p, q) = {m + n : m p + n q = 1}`. -/
def A (p q : ℕ) : Set ℤ := {s | ∃ m n : ℤ, m * p + n * q = 1 ∧ s = m + n}

/-- The least prime in `A(p, q)`. -/
noncomputable def first (p q : ℕ) : ℕ := sInf {x : ℕ | x.Prime ∧ (x : ℤ) ∈ A p q}

/-- The least prime in `A(p, q)` greater than `first p q`. -/
noncomputable def second (p q : ℕ) : ℕ :=
  sInf {x : ℕ | x.Prime ∧ (x : ℤ) ∈ A p q ∧ first p q < x}

/-- The operation `f(p, q)`: the first two primes in `A(p, q)`. -/
noncomputable def f (pq : ℕ × ℕ) : ℕ × ℕ := (first pq.1 pq.2, second pq.1 pq.2)

/-- Iterating `f` on a pair of distinct primes always repeats. -/
theorem main :
    ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → ∃ i j : ℕ, i < j ∧ f^[i] (p, q) = f^[j] (p, q) := by
  sorry

end OMA.S_mo_139058
