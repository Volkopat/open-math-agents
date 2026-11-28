import Mathlib

/-!
# OEIS A272101: the square part of prime(n+1)^2 - prime(n)^2 equals the gap exactly on A068361

Source: https://oeis.org/A272101 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Benedict W. J. Irwin, Apr 20 2016), offset 1: a(n) is the square root of the largest square
dividing A069482(n) = prime(n+1)^2 - prime(n)^2. Formula section: Conjectures:
a(A068361(n)) = A001223(A068361(n)). a(A068361(n)) = 2 for n>1. These are the only
a(n)=A001223(n).

Formalization notes:
* p i is the i-th prime, with p 1 = 2.
* a n is the greatest k ≤ A069482 n with k ^ 2 dividing A069482 n; for a positive argument this
  is the square root of its largest square divisor (A000188).
* g n = p (n + 1) - p n is A001223, the prime gap.
* InA068361 n says that the number of squarefree numbers strictly between p n and p (n + 1) is
  p (n + 1) - p n - 1, the definition of A068361.
* A068361 starts with 1, so its terms A068361(n) with n > 1 are exactly its members m ≥ 2; the
  second conjecture is stated for those members.
* main is the conjunction of the three conjectures, for indices n ≥ 1.
-/

namespace OMA.S_oeis_a272101

/-- The `i`-th prime, counted from `p 1 = 2`. -/
noncomputable def p (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)

/-- A069482: `prime(n+1)^2 - prime(n)^2`. -/
noncomputable def A069482 (n : ℕ) : ℕ := p (n + 1) ^ 2 - p n ^ 2

/-- A272101: the square root of the largest square dividing `A069482(n)`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.findGreatest (fun k => k ^ 2 ∣ A069482 n) (A069482 n)

/-- A001223: the prime gap `prime(n+1) - prime(n)`. -/
noncomputable def g (n : ℕ) : ℕ := p (n + 1) - p n

/-- A068361: the number of squarefree numbers strictly between `prime(n)` and `prime(n+1)` is
`prime(n+1) - prime(n) - 1`. -/
noncomputable def InA068361 (n : ℕ) : Prop :=
  ((Finset.Ioo (p n) (p (n + 1))).filter Squarefree).card = p (n + 1) - p n - 1

/-- Irwin's three conjectures: a = A001223 on A068361, a = 2 on its members after the first, and
a = A001223 nowhere else. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → InA068361 n → a n = g n) ∧
      (∀ n : ℕ, 2 ≤ n → InA068361 n → a n = 2) ∧
      (∀ n : ℕ, 1 ≤ n → a n = g n → InA068361 n) := by
  sorry

end OMA.S_oeis_a272101
