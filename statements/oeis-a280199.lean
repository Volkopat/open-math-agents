import Mathlib

/-!
# A280199: numbers n such that a^(n-1) == 1 (mod n^2) has solutions with 1 < a < n^2 - 1

Source: https://oeis.org/A280199 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A280199 (Robert Israel and Thomas Ordowski, Dec 28 2016), offset 1: numbers n such that
a^(n-1) == 1 (mod n^2) has solutions with 1 < a < n^2-1. Data
5, 7, 11, 13, 15, 17, 19, 21, 23, 25, 28, 29, 31, 33, 35, 37, 39, 41, 43, 45, 47, 49, 51, ...
Entry A181780: numbers n which are Fermat pseudoprimes to some base b, 2 <= b <= n-2. (A nonprime
number n is a Fermat pseudoprime to base b if b^(n-1) = 1 (mod n).) Data
15, 21, 25, 28, 33, 35, 39, 45, 49, 51, 52, 55, 57, 63, 65, 66, 69, 70, 75, 76, 77, 85, 87, ...

Comments of A280199: Conjecture: composite terms are A181780.

Formalization notes.
* `InA280199 n` says that n is a term of A280199: some a with 1 < a < n^2 - 1 satisfies
  a^(n-1) == 1 (mod n^2).
* `InA181780 n` says that n is a term of A181780: n is composite (n > 1 and n is not prime) and
  some b with 2 <= b <= n - 2 satisfies b^(n-1) == 1 (mod n).
* `main` says that the composite terms of A280199 are exactly the terms of A181780.
-/

namespace OMA.S_oeis_a280199

/-- n is a term of A280199. -/
def InA280199 (n : ℕ) : Prop :=
  ∃ a : ℕ, 1 < a ∧ a < n ^ 2 - 1 ∧ a ^ (n - 1) ≡ 1 [MOD n ^ 2]

/-- n is a term of A181780: a composite number that is a Fermat pseudoprime to some base b with
2 ≤ b ≤ n - 2. -/
def InA181780 (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∃ b : ℕ, 2 ≤ b ∧ b ≤ n - 2 ∧ b ^ (n - 1) ≡ 1 [MOD n]

/-- The composite terms of A280199 are exactly the terms of A181780. -/
theorem main : ∀ n : ℕ, (1 < n ∧ ¬ n.Prime ∧ InA280199 n) ↔ InA181780 n := by
  sorry

end OMA.S_oeis_a280199
