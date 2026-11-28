import OMAStatements.S_oeis_a139804
import Mathlib

/-! A139804 split into the factorial divisibility obstruction and a prime-gap bound.

Put `N = 3^n`. If `N! + m` is prime and `m > 1`, then no prime `q ≤ N` divides `m`: such a `q`
divides `N!`, hence `N! + m`, and `q ≤ m < N! + m`. So every prime factor of `m` exceeds `N`,
and a composite `m` is at least `(N + 1)^2` (its least prime factor squared). That is `H1`, the
classical argument for Fortunate-type numbers, valid for every `n`; it is not progress on the
conjecture.

`H2` is the open rest, a prime-gap statement: the least `m ≥ 1` with `(3^n)! + m` prime is
below `(3^n + 1)^2`. Together they force the least `m` to be `1` or prime.
-/

namespace OMA.R_oeis_a139804_R1

open OMA.S_oeis_a139804

/-- Every prime factor of a valid `m > 1` exceeds `3^n`; a composite valid `m` is at least
`(3^n + 1)^2`. -/
def H1 : Prop := ∀ n m : ℕ, IsValid n m → m ≠ 1 →
  (∀ q : ℕ, q.Prime → q ∣ m → 3 ^ n < q) ∧ (m.Prime ∨ (3 ^ n + 1) ^ 2 ≤ m)

/-- The open rest: the least valid `m` is below `(3^n + 1)^2`. -/
def H2 : Prop := ∀ n m : ℕ, IsLeastValid n m → m < (3 ^ n + 1) ^ 2

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a139804.main := by
  intro h1 h2 n m hl
  by_cases hm : m = 1
  · exact Or.inl hm
  · rcases ((h1 n m hl.1 hm).2) with h | h
    · exact Or.inr h
    · have := h2 n m hl
      omega

end OMA.R_oeis_a139804_R1
