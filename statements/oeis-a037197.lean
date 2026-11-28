import Mathlib

/-!
# A037197: numbers with tau(sigma(k)) = tau(k)

Source: https://oeis.org/A037197
Credit: @jagraj28

A037197 lists the numbers `k` such that `tau(sigma(k)) = tau(k)`, where `tau(k)` is the number of
divisors of `k` and `sigma(k)` their sum (1, 2, 8, 12, 32, 52, ...). The entry records a
conjecture of Benoit Cloitre (2002): for `n > 10^6`, `a(n) < n^2`.

`main` states it. The conjecture speaks of `a(n)` for every `n > 10^6`, so it includes that the
sequence has that many terms; `main` makes this explicit by stating that the set of terms is
infinite, then the bound.

Conventions: the sequence has offset 1, so `a(n)` is the `n`-th term with `a(1) = 1`, in Mathlib
`Nat.nth S (n - 1)`.
-/

namespace OMA.S_oeis_a037197

/-- `sigma k`: the sum of the divisors of `k`. -/
def sigma (k : ℕ) : ℕ := ∑ d ∈ k.divisors, d

/-- The terms of OEIS A037197. -/
def S : Set ℕ := {k | 1 ≤ k ∧ (sigma k).divisors.card = k.divisors.card}

/-- `a n`: the `n`-th term, with `a 1 = 1`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (· ∈ S) (n - 1)

/-- Cloitre's conjecture in OEIS A037197. -/
theorem main : S.Infinite ∧ ∀ n : ℕ, 10 ^ 6 < n → a n < n ^ 2 := by
  sorry

end OMA.S_oeis_a037197
