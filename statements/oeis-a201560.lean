import Mathlib

/-!
# OEIS A201560: `a(n) = (Σ_{m=1..n-1} m^(n-1) + 1) mod n`

Source: https://oeis.org/A201560
Credit: @goncalomsdias (agent: Claude Code, model claude-opus-5-5)

`a(n) = (Sum(m^(n-1), m=1..n-1) + 1) modulo n`, offset 1 (`0, 0, 0, 1, 0, 4, 0, 1, 7, 6, …`).

The entry: "Equals 0 if n is 1 or a prime, by Fermat's little theorem. It is conjectured that the
converse is also true". This file states the conjecture, the converse: if `a(n) = 0` then `n` is `1`
or a prime. (The direction proved by Fermat's little theorem is not part of the conjecture.)

This is Giuga's conjecture in the form of this entry; formal-conjectures states the same problem in
other forms in `FormalConjectures/Wikipedia/AgohGiuga.lean` (`agoh_giuga.variants.giuga`).

Conventions:
* `a(n)` is defined for `n ≥ 1` (the offset); at `n = 1` the sum is empty and `a(1) = 1 mod 1 = 0`.
  The statement is for every `n ≥ 1`.
* `mod` is `Nat` `%`. A computation confirms that this definition reproduces the seventy-seven
  terms of the entry's data, and that the only `n ≤ 20000` with `a(n) = 0` are `1` and the primes.
-/

namespace OMA.S_oeis_a201560

/-- `A201560(n) = (Σ_{m=1..n-1} m^(n-1) + 1) mod n`. -/
def a (n : ℕ) : ℕ :=
  (∑ m ∈ Finset.Ico 1 n, m ^ (n - 1) + 1) % n

/-- Conjecture (Giuga, as stated in the entry): `a(n) = 0` only when `n` is `1` or a prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = 0 → n = 1 ∨ n.Prime := by
  sorry

end OMA.S_oeis_a201560
