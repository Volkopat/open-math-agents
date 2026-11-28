import Mathlib

/-!
# A363228: Exponent of 4 in 9^n - 1.

Source: https://oeis.org/A363228
Credit: @cj-55m (agent: Claude Code, model claude-opus-5-5)

The entry (offset 1, data 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, ...) records in its
FORMULA section:

  Conjecture: a(n) = A235127(A000045(6*n)), all other 4-adic 6-sections
  A235127(A000045(.)) = 0. - R. J. Mathar, Jun 28 2025

Conventions:
* A235127(m) is the greatest `k` such that `4^k` divides `m` (offset 1, so `m ≥ 1`). It is
  formalized as `exp4 m := Nat.findGreatest (fun k => 4 ^ k ∣ m) m`; for `m ≥ 1` every `k` with
  `4^k ∣ m` satisfies `k < m`, so the search bound `m` loses nothing.
* A000045 is the Fibonacci sequence, `Nat.fib` (`fib 0 = 0`, `fib 1 = 1`).
* The sequence is indexed from `1`: `a n = exp4 (9 ^ n - 1)` for `n ≥ 1` (the value at `0` plays
  no role).
* The conjecture has two parts: (1) `a(n) = A235127(fib (6 n))` for every `n ≥ 1`; (2) the other
  6-sections vanish: `A235127(fib m) = 0` for every `m ≥ 1` not divisible by `6`.
-/

namespace OMA.S_oeis_a363228

/-- A235127: the greatest `k` such that `4^k` divides `m` (for `m ≥ 1`). -/
def exp4 (m : ℕ) : ℕ := Nat.findGreatest (fun k => 4 ^ k ∣ m) m

/-- A363228: the exponent of `4` in `9^n - 1` (indexed from `1`). -/
def a (n : ℕ) : ℕ := exp4 (9 ^ n - 1)

/-- Mathar's conjecture for A363228: `a(n) = A235127(fib (6 n))` for `n ≥ 1`, and
`A235127(fib m) = 0` for all `m ≥ 1` with `m` not divisible by `6`. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → a n = exp4 (Nat.fib (6 * n))) ∧
    (∀ m : ℕ, 1 ≤ m → ¬ 6 ∣ m → exp4 (Nat.fib m) = 0) := by
  sorry

end OMA.S_oeis_a363228
