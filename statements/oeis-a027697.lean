import Mathlib

/-!
# OEIS A027697: odious primes versus evil primes

Source: https://oeis.org/A027697
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Odious primes (A027697) have an odd number of `1`s in binary; evil primes (A027699) an even
number. Conjecture (OEIS entry): `a(n) < A027699(n)` except for `n = 2`, and moreover
`A027699(n) - a(n) → ∞`.

Conventions:
* Offset `1`: `a(n)` is `Nat.nth` (from `0`) at `n - 1` of the odious primes, likewise for the
  evil primes; both sets are infinite (by Drmota–Mauduit–Rivat), so `Nat.nth` enumerates them.
* `n ≥ 1`, `n ≠ 2` in the inequality.
-/

namespace OMA.S_oeis_a027697

open Filter

/-- Binary weight. -/
def s2 (k : ℕ) : ℕ := ((Nat.digits 2 k).filter (· = 1)).length

/-- `n`-th odious prime (offset `1`). -/
noncomputable def odious (n : ℕ) : ℕ := Nat.nth (fun p => p.Prime ∧ Odd (s2 p)) (n - 1)

/-- `n`-th evil prime (offset `1`). -/
noncomputable def evil (n : ℕ) : ℕ := Nat.nth (fun p => p.Prime ∧ Even (s2 p)) (n - 1)

/-- `odious n < evil n` for `n ≥ 1`, `n ≠ 2`, and `evil n - odious n → ∞`. -/
theorem main : (∀ n : ℕ, 1 ≤ n → n ≠ 2 → odious n < evil n) ∧
    Tendsto (fun n : ℕ => (evil n : ℤ) - odious n) atTop atTop := by
  sorry

end OMA.S_oeis_a027697
