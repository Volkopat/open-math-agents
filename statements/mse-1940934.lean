import Mathlib

/-!
# Does a signed sum over the non-squarefree numbers change sign infinitely often?

Source: https://math.stackexchange.com/questions/1940934

Let `q_k` be the `k`-th positive integer divisible by a square larger than one
(`q_1 = 4, q_2 = 8, q_3 = 9, …`) and `Ω(n)` the number of prime factors of `n` counted with
multiplicity. The question asks for a proof that
`S_n = ∑_{k=1}^n (-1)^{Ω(q_k)} q_k` changes sign infinitely many times as `n` increases.

Formalization notes:
* `q k` is `Nat.nth` of the positive non-squarefree numbers, indexed from `0`, so `q 0 = 4`
  is the source's `q_1`, and `S n` sums `q 0, …, q (n - 1)`, i.e. the source's `S_n`.
* `Ω` is `ArithmeticFunction.cardFactors`.
* "Changes sign infinitely many times" is stated as: `S n > 0` for infinitely many `n` and
  `S n < 0` for infinitely many `n`.
-/

namespace OMA.S_mse_1940934

open ArithmeticFunction

/-- `m` is a positive integer divisible by a square larger than one. -/
def NonSqf (m : ℕ) : Prop := 0 < m ∧ ¬ Squarefree m

/-- The `k`-th (from `0`) positive non-squarefree number: `4, 8, 9, 12, …`. -/
noncomputable def q (k : ℕ) : ℕ := Nat.nth NonSqf k

/-- `S n = ∑_{k<n} (-1)^{Ω(q k)} q k`. -/
noncomputable def S (n : ℕ) : ℤ := ∑ k ∈ Finset.range n, (-1 : ℤ) ^ cardFactors (q k) * q k

/-- `S n` is positive for infinitely many `n` and negative for infinitely many `n`. -/
theorem main : {n : ℕ | 0 < S n}.Infinite ∧ {n : ℕ | S n < 0}.Infinite := by
  sorry

end OMA.S_mse_1940934
