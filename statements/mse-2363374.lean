import Mathlib

/-!
# Number of monomials in `a_n = a_{n-1} + (a_{n-2})^2` with `a_1 = a`, `a_2 = b`

Source: https://math.stackexchange.com/questions/2363374
Credit: @koolkao

Question (Kai Williams, Mathematics Stack Exchange 2363374, 2017; CC BY-SA 3.0). I was playing
around with the sequence `a_1 = a`, `a_2 = b` and the recurrence `a_n = a_{n-1} + (a_{n-2})^2` and
just listed out a few general terms. For instance, `a_1 = a`, `a_2 = b`, `a_3 = b + a^2`,
`a_4 = b + b^2 + a^2`, `a_5 = a^4 + 2a^2b + a^2 + 2b^2 + b`, and
`a_6 = b^4 + 2b^3 + 3b^2 + 2a^2b^2 + 4a^2b + b + 2a^4 + a^2`. When I did that, I realized that the
number of terms in `a_n` appears to be `F_n` where `F` represents the Fibonacci numbers. I
conjecture that this is true, but I am not sure how to even approach this.

`main` states the conjecture: for every `n ≥ 1`, the number of terms of `a_n` is `F_n`. A disproof
is a counterexample.

Translation choices:
* `a` and `b` are independent indeterminates: `a_n` is a polynomial in `MvPolynomial (Fin 2) ℤ`
  with `a = X 0` and `b = X 1`. Every coefficient of every `a_n` is a positive integer (the
  recurrence only adds and squares), so no term cancels and the number of terms is the same over
  any ring of characteristic zero;
* "the number of terms" of `a_n` is the number of monomials with a nonzero coefficient,
  `(a_n).support.card`, after collecting like terms (as in the listed examples, e.g. `a_5` has the
  5 terms `a^4, 2a^2b, a^2, 2b^2, b`);
* `F_n` is Mathlib's `Nat.fib n`, with `F_1 = F_2 = 1` (the listed terms have `1, 1, 2, 3, 5, 8`
  terms for `n = 1, …, 6`);
* the sequence is indexed from `1` as in the source; the value `seq 0 = 0` is a placeholder that
  `main` never uses (it quantifies over `n ≥ 1`).
-/

namespace OMA.S_mse_2363374

open MvPolynomial

/-- The sequence `a_1 = a`, `a_2 = b`, `a_n = a_{n-1} + (a_{n-2})^2` in `ℤ[a, b]`, with
`a = X 0`, `b = X 1` (and the unused placeholder `seq 0 = 0`). -/
noncomputable def seq : ℕ → MvPolynomial (Fin 2) ℤ
  | 0 => 0
  | 1 => X 0
  | 2 => X 1
  | n + 3 => seq (n + 2) + seq (n + 1) ^ 2

/-- The conjecture: for every `n ≥ 1`, `a_n` has exactly `F_n` terms. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (seq n).support.card = Nat.fib n := by
  sorry

end OMA.S_mse_2363374
