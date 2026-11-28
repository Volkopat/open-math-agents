import Mathlib

/-!
# `φ(m+n) ∣ n` for some positive integer `n`

Source: https://mathoverflow.net/questions/331984 (Zhi-Wei Sun, CC BY-SA 4.0).

If `p` is prime then `φ(1 + n) = n` for `n = p - 1`. Question: is it true that for each integer
`m > 1` there is a positive integer `n ≤ m² - m` such that `φ(m + n) ∣ n`? The asker conjectures
a positive answer (see OEIS A248568); for example `φ(10 + 40) = 20` divides `40`.

We state the affirmative answer.

Formalization notes:
* `φ` is Mathlib's `Nat.totient`; `m² - m` is computed in `ℕ` (no truncation, as `m² ≥ m`).
* Checked numerically: holds for every `1 < m < 3000`.
-/

namespace OMA.S_mo_331984

/-- For every `m > 1` there is `1 ≤ n ≤ m² - m` with `φ(m + n) ∣ n`. -/
theorem main : ∀ m : ℕ, 1 < m → ∃ n : ℕ, 1 ≤ n ∧ n ≤ m ^ 2 - m ∧ (m + n).totient ∣ n := by
  sorry

end OMA.S_mo_331984
