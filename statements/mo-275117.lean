import Mathlib

/-!
# Is `699…998` a value of the Euler totient function?

Source: https://mathoverflow.net/questions/275117
Credit: @jagraj28

Let `n_l = 7 * 10 ^ (l + 1) - 2 = 699…998`. The question asks whether there is an `l` such that
`n_l = φ(m)` for some `m`. The asker checked that `n_l` is not a totient value for `l ≤ 100`
and expects that it never is. The question has no answer; one comment notes that a solution
needs `m = p ^ k` or `2 * p ^ k` with `p ≡ 2 (mod 3)` and `k` even.

`main` states the expected answer: no `n_l` is a value of `φ`. A proof of `main` answers the
question negatively, and a proof of `¬ main` (one `l` and one `m` with `φ m = n_l`) answers it
positively.

Conventions.
* `l` ranges over all natural numbers. For `l = 0`, `n_0 = 68`, which is not a totient value
  (a search over all `m ≤ 2 * 68 ^ 2` finds no `m` with `φ m = 68`, and `φ m ≥ √(m / 2)`),
  so including `l = 0` does not change the question.
* `φ` is Mathlib's `Nat.totient`; `m` ranges over all natural numbers (`φ 0 = 0`, which is not
  of the form `n_l`).
* `7 * 10 ^ (l + 1) - 2` is truncated subtraction on `ℕ`, which is exact here because
  `7 * 10 ^ (l + 1) ≥ 70`.
-/

namespace OMA.S_mo_275117

/-- No number `699…998 = 7 * 10 ^ (l + 1) - 2` is a value of Euler's totient function. -/
theorem main : ∀ l m : ℕ, Nat.totient m ≠ 7 * 10 ^ (l + 1) - 2 := by
  sorry

end OMA.S_mo_275117
