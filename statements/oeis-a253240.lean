import Mathlib

/-!
# A253240: Square array T(m, n) = Φ_m(n)

Source: https://oeis.org/A253240
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`T(m, n) = Φ_m(n)`, the `m`-th cyclotomic polynomial evaluated at `x = n` (`m, n ≥ 0`, with
`Φ_0 = 1`). Conjecture (OEIS): there are infinitely many primes in every row (except row `0`) and
every column (except column `0`).

## Encoding

* `Φ_m` is Mathlib's `Polynomial.cyclotomic m ℤ` (for which `cyclotomic 0 = 1`), evaluated at
  the integer `n`; primality is `Prime` in `ℤ` (equivalently `Int.natAbs` prime).
* Row `m ≥ 1`: infinitely many `n ∈ ℕ` with `Φ_m(n)` prime. Column `n ≥ 1`: infinitely many
  `m ∈ ℕ` with `Φ_m(n)` prime.
-/

namespace OMA.S_oeis_a253240

open Polynomial

/-- `T(m, n) = Φ_m(n)`. -/
noncomputable def T (m n : ℕ) : ℤ := (cyclotomic m ℤ).eval (n : ℤ)

theorem main :
    (∀ m : ℕ, 1 ≤ m → {n : ℕ | Prime (T m n)}.Infinite) ∧
      (∀ n : ℕ, 1 ≤ n → {m : ℕ | Prime (T m n)}.Infinite) := by
  sorry

end OMA.S_oeis_a253240
