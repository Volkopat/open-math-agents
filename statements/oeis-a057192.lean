import Mathlib

/-!
# A057192: Least m such that 1 + prime(n)*2^m is a prime, or -1 if no such m exists.

Source: https://oeis.org/A057192
Credit: @divmxnd0x

Conjecture (Aguirre, stated in A057192 by Lorenzo Sauras Altuzarra, Feb 12 2021): for every
`n > 1`, `a(n)` is even if and only if `prime(n) mod 3 = 1`.

Formalization notes:
* `prime(n)` is the `n`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (n - 1)`.
* `a(n)` is the least `m ≥ 0` with `1 + prime(n) * 2^m` prime (`a(1) = 0` since `1 + 2 = 3`), and
  `-1` if there is no such `m`, exactly as in the definition of the sequence (keyword "sign").
* With this definition `a(1), ..., a(14)` = 0, 1, 1, 2, 1, 2, 3, 6, 1, 1, 8, 2, 1, 2, matching the
  data of A057192.
-/

namespace OMA.S_oeis_a057192

open Classical in
/-- A057192(n): the least `m` with `1 + prime(n) 2^m` prime, or `-1` if there is none. -/
noncomputable def a (n : ℕ) : ℤ :=
  if h : ∃ m : ℕ, (1 + Nat.nth Nat.Prime (n - 1) * 2 ^ m).Prime then (Nat.find h : ℤ) else -1

/-- Aguirre's conjecture: for `n > 1`, `a(n)` is even iff `prime(n) ≡ 1 (mod 3)`. -/
theorem main : ∀ n : ℕ, 1 < n → (Even (a n) ↔ Nat.nth Nat.Prime (n - 1) % 3 = 1) := by
  sorry

end OMA.S_oeis_a057192
