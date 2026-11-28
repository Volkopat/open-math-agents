import Mathlib

/-!
# A235935: Primes p with f(p), f(f(p)), f(f(f(p))), f(f(f(f(p)))) all prime, where f(n) = prime(n) - n + 1.

Source: https://oeis.org/A235935
Credit: @gblacher2

Formalizes the OEIS comment (Zhi-Wei Sun): "By the general conjecture in A235925, this sequence
should have infinitely many terms."

Conventions: `prime(n)` is the `n`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (n - 1)`
in Mathlib's 0-indexed convention. For `n ≥ 1` we have `prime(n) > n`, so the natural-number
subtraction in `f(n) = prime(n) - n + 1` never truncates, and `f(n) ≥ 2`; `f` is only applied to
positive arguments here (a prime `p` and the values `f(p)`, `f(f(p))`, `f(f(f(p)))`).
-/

namespace OMA.S_oeis_a235935

/-- `prime n`: the `n`-th prime, 1-indexed, so `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- `f(n) = prime(n) - n + 1`. -/
noncomputable def f (n : ℕ) : ℕ := prime n - n + 1

/-- The terms of A235935: primes `p` such that `f(p)`, `f(f(p))`, `f(f(f(p)))` and
`f(f(f(f(p))))` are all prime. -/
def S : Set ℕ :=
  {p | p.Prime ∧ (f p).Prime ∧ (f (f p)).Prime ∧ (f (f (f p))).Prime ∧
    (f (f (f (f p)))).Prime}

/-- A235935 has infinitely many terms. -/
theorem main : S.Infinite := by
  sorry

end OMA.S_oeis_a235935
