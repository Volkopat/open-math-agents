import Mathlib

/-!
# MathOverflow 380394: a sequence modified from the Catalan recurrence and 2-adic valuations

Source: https://mathoverflow.net/questions/380394
Credit: @OrangeHeadz (agent: Claude Code, model claude-fable-5-2)

Question (T. Amdeberhan): Let `ν₂(x)` denote the 2-adic valuation of `x` and let `s(x)` stand for
the number of 1's in the binary expansion of `x`. Consider the sequence `w₀ = 1` and
`w_{n+1} = ∑_{i=0}^{n} w_i² w_{n-i}²`. Is the following true? If `C_n = binom(2n, n) / (n + 1)`,
then `ν₂(w_n) = (C_n mod 2) + 2 s(n + 1) - 3`.

We state the affirmative answer, for every `n ≥ 0`; a disproof of `main` answers the question
negatively.

Conventions:
* `w` is the sequence of the question, with `w 0 = 1`; all its terms are positive integers.
* `ν₂` is `padicValNat 2`, `s(x)` is the digit sum of `x` in base 2, and `C_n` is Mathlib's
  `catalan n`.
* The identity is stated in `ℤ`, so that `- 3` is an honest subtraction.
-/

namespace OMA.S_mo_380394

/-- The sequence `w₀ = 1`, `w_{n+1} = ∑_{i=0}^{n} w_i² w_{n-i}²`. -/
def w : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ i : Fin n.succ, w i ^ 2 * w (n - i) ^ 2

/-- For every `n`, `ν₂(w_n) = (C_n mod 2) + 2 s(n + 1) - 3`. -/
theorem main : ∀ n : ℕ,
    (padicValNat 2 (w n) : ℤ) =
      ((catalan n % 2 : ℕ) : ℤ) + 2 * ((Nat.digits 2 (n + 1)).sum : ℤ) - 3 := by
  sorry

end OMA.S_mo_380394
