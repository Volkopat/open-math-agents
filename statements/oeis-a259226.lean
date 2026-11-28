import Mathlib

/-!
# A259226: numbers `n` with `A157480(n) = A259232(n)`

Source: https://oeis.org/A259226
Credit: @avivorly

A259226 (Zak Seidov, Jun 2015) lists the numbers `n` such that `A157480(n) = A259232(n)`, where
- A157480: `a(n)` = least prime `p` such that `p + prime(n)` is a square;
- A259232: smallest prime `q > p` such that `q + p` is a square, where `p` is the `n`-th prime.
The entry adds: or numbers `n` such that `A157480(n) > A000040(n)`.

Conjecture (in the entry): "It is a strong conjecture that the sequence is complete, and the last term is
a(99)=9867."

Conventions:
- All three sequences have offset 1. `nthPrime n` is the `n`-th prime, `nthPrime 1 = 2`, that is
  `Nat.nth Nat.Prime (n - 1)`.
- "least" and "smallest" are `sInf` on `ℕ`; a square is `IsSquare` (`∃ r, x = r * r`).
- `n` is a term (`InA259226 n`) when `n ≥ 1`, `A157480(n)` exists (some prime `p` has `p + prime(n)` a square), and
  `A157480 n = A259232 n`. The existence clause keeps `sInf ∅ = 0` from making spurious terms (whether every prime
  has such a `p` is not known). The equality then makes `A259232(n)` exist too, as `A157480 n` is then a prime, so
  nonzero.
- "the sequence is complete, and the last term is a(99)=9867" is stated as: every term is `≤ 9867`, and `9867` is a
  term. The 98 smaller terms listed in the entry (its data) are not restated.
-/

namespace OMA.S_oeis_a259226

/-- The `n`-th prime, offset 1: `nthPrime 1 = 2`, `nthPrime 2 = 3`, `nthPrime 3 = 5`, ... -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A157480: `a(n)` = least prime `p` such that `p + prime(n)` is a square. -/
noncomputable def A157480 (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ IsSquare (p + nthPrime n)}

/-- A259232: smallest prime `q > p` such that `q + p` is a square, where `p` is the `n`-th prime. -/
noncomputable def A259232 (n : ℕ) : ℕ :=
  sInf {q : ℕ | q.Prime ∧ nthPrime n < q ∧ IsSquare (q + nthPrime n)}

/-- `n` is a term of A259226: `n ≥ 1`, `A157480(n)` exists, and `A157480(n) = A259232(n)`. -/
def InA259226 (n : ℕ) : Prop :=
  1 ≤ n ∧ (∃ p : ℕ, p.Prime ∧ IsSquare (p + nthPrime n)) ∧ A157480 n = A259232 n

/-- The conjecture: A259226 is complete with last term `a(99) = 9867`. -/
theorem main : (∀ n : ℕ, InA259226 n → n ≤ 9867) ∧ InA259226 9867 := by
  sorry

end OMA.S_oeis_a259226
