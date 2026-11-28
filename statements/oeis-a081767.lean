import Mathlib

/-!
# A081767: Numbers k such that k^2 - 1 divides binomial(2k,k).

Source: https://oeis.org/A081767
Credit: @gblacher2

Question (comment section of A081767, entry by Benoit Cloitre, Apr 09 2003):
"Is a(n) asymptotic to c*n with 9 < c < 10?"
A later comment (Bill McEachen, Feb 26 2024) says: "The data does not appear to support the
conjectured asymptote statement (neither the constant nor being linear)." So the statement below
may well be false; it is the conjectured affirmative answer, as the question poses it.

The sequence has offset 1 and lists, in increasing order, the numbers `k` such that
`k^2 - 1` divides `binomial(2k, k)`: 2, 16, 21, 29, 43, 46, ...

Modelling choices:
* `a n` is the `n`-th term for `n ≥ 1` (offset 1), i.e. `Nat.nth p (n - 1)` where `p k` says
  `k ^ 2 - 1 ∣ Nat.choose (2 * k) k`.
* Subtraction is in `ℕ`. For `k = 0` and `k = 1` the divisor `k ^ 2 - 1` is `0`, and `0` divides
  only `0`, while `Nat.choose (2 * k) k` is `1` or `2`; so `0` and `1` are not terms, which matches
  the data (the first term is 2). For `k ≥ 2` the divisor is the integer `k^2 - 1` of the source.
* "a(n) asymptotic to c*n" is read as `a(n) ~ c * n` as `n → ∞` (`Asymptotics.IsEquivalent`).
* No `answer(...)` is used: the theorem states the affirmative answer, with some real `c` and
  `9 < c < 10`.
-/

namespace OMA.S_oeis_a081767

/-- The defining property of A081767: `k^2 - 1` divides `binomial(2k, k)`. -/
def IsTerm (k : ℕ) : Prop := k ^ 2 - 1 ∣ Nat.choose (2 * k) k

/-- A081767(n) for `n ≥ 1`: the `n`-th number `k` (in increasing order) with
`k^2 - 1 ∣ binomial(2k, k)`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- Cloitre's question, affirmative answer: `a(n)` is asymptotic to `c * n` for some
`c` with `9 < c < 10`. -/
theorem main : ∃ c : ℝ, 9 < c ∧ c < 10 ∧
    Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (a n : ℝ)) (fun n : ℕ => c * n) := by
  sorry

end OMA.S_oeis_a081767
