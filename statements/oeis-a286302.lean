import Mathlib

/-!
# A286302: Numbers n such that A133364(n) <= 1

Source: https://oeis.org/A286302

Conjecture (OEIS A286302):
Let `A133364(n)` be the number of representations of `n` as `m + p`, where `m` is a
powerful number (OEIS A001694: `m ≥ 1` and `p ∣ m → p ^ 2 ∣ m` for every prime `p`)
and `p` is prime. Then `10404` is the last integer with `A133364(n) ≤ 1`; that is,
every integer `n > 10404` has at least two representations as a powerful number plus a prime.

Conventions:
- `1` is powerful by convention (`A001694`: `1, 4, 8, 9, 16, 25, 27, 32, 36, ...`).
- `A133364(10404) = 1` (`10404 = 343 + 10061`, with `343 = 7 ^ 3` powerful and `10061` prime).
-/

namespace OMA.S_oeis_a286302

/-- Predicate stating that `m` is a powerful number (OEIS A001694). -/
def IsPowerful (m : ℕ) : Prop :=
  1 ≤ m ∧ ∀ p : ℕ, Nat.Prime p → p ∣ m → p ^ 2 ∣ m

/-- Number of representations of `n` as `m + p` with `m` powerful and `p` prime
(OEIS A133364). -/
noncomputable def a133364 (n : ℕ) : ℕ :=
  Set.ncard {m : ℕ | m < n ∧ IsPowerful m ∧ Nat.Prime (n - m)}

/-- Conjecture: `10404` is the last term of A286302 (every `n > 10404` satisfies
`A133364(n) ≥ 2`). -/
theorem main :
    ∀ n : ℕ, 10404 < n → 2 ≤ a133364 n := by
  sorry

end OMA.S_oeis_a286302
