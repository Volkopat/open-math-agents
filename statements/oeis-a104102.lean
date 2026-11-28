import Mathlib

/-!
# OEIS A104102: the number of primes in [p(n)#, p(n)# + p(n+1)^2) exceeds p(n+1)

Source: https://oeis.org/A104102 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Pierre CAMI, Mar 04 2005), offset 1: Number of primes >= p(n)# and < p(n)# + p(n+1)^2
where p(i) = i-th prime, p(i)# = i-th primorial. Comment: Conjecture: a(n) is always > p(n+1).
Data: 4, 7, 11, 21, 24, 29, 25, 38, 42, 37, 58, 54, 45, 60.

Formalization notes:
* p i is the i-th prime counted from 1, so p 1 = 2: in Lean Nat.nth Nat.Prime (i - 1).
* p(n)#, the n-th primorial, is the product of the first n primes, that is Mathlib's
  primorial (p n), the product of the primes up to p n.
* a n is the number of primes m with p(n)# ≤ m < p(n)# + p(n+1)^2, as the name says.
* main says: for every n ≥ 1 (the offset), a n > p (n + 1).
* Controls proved in the proof file: a 1 = 4 and a 2 = 7, the entry's first two terms.
* The listed terms a(4) = 21, a(10) = 37 and a(11) = 58 disagree with the name, which gives 20,
  35 and 57 (two independent programs; an inclusive right endpoint fixes a(4) but breaks a(1),
  a(2) and a(13)). No reading of the endpoint affects the conjecture at n = 36, where
  151# + 157^2 is composite.
-/

namespace OMA.S_oeis_a104102

/-- The `i`-th prime, counted from 1, so `p 1 = 2`. -/
noncomputable def p (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)

/-- `a n`: the number of primes `m` with `p(n)# ≤ m < p(n)# + p(n+1)^2`, where
`p(n)# = primorial (p n)` is the product of the primes up to `p n`, that is of the first `n` primes. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Ico (primorial (p n)) (primorial (p n) + p (n + 1) ^ 2)).filter Nat.Prime).card

/-- CAMI's conjecture: a(n) is always > p(n+1). -/
theorem main : ∀ n : ℕ, 1 ≤ n → p (n + 1) < a n := by
  sorry

end OMA.S_oeis_a104102
