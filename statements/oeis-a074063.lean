import Mathlib

/-!
# A074063: Arrangements with prime sums and prime sums of squares

Source: https://oeis.org/A074063
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of essentially different ways to arrange `1, 2, …, n` in a sequence such
that adjacent integers sum to a prime and their squares sum to a prime. It is known that
`a(n) > 0` for `58 ≤ n ≤ 200`; conjectured: `a(n) > 0` for all `n > 57`.

## Encoding

* `a(n) > 0` means such an arrangement exists. An arrangement is a bijection
  `σ : Fin n ≃ Fin n`, position `i` holding the integer `σ i + 1`; it is linear (the values
  `a(4) = 1`, via `4, 1, 2, 3`, and `a(5) = 0` are only consistent with a linear arrangement).
* Conditions for consecutive positions `i, i + 1`: `x + y` and `x² + y²` are prime.
-/

namespace OMA.S_oeis_a074063

/-- Some arrangement of `1, …, n` has all adjacent sums and sums of squares prime. -/
def Exists (n : ℕ) : Prop :=
  ∃ σ : Fin n ≃ Fin n, ∀ i j : Fin n, (j : ℕ) = i + 1 →
    ((σ i : ℕ) + 1 + ((σ j : ℕ) + 1)).Prime ∧ (((σ i : ℕ) + 1) ^ 2 + ((σ j : ℕ) + 1) ^ 2).Prime

theorem main : ∀ n : ℕ, 57 < n → Exists n := by
  sorry

end OMA.S_oeis_a074063
