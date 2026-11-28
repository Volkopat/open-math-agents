import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace OMA.S_oeis_a396804

/-- Cauchy product of two sequences `ℕ → ℚ`. -/
def mulSeq (f g : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (n + 1), f i * g (n - i)

/-- `k`-th Cauchy power of a sequence `ℕ → ℚ`. -/
def powSeq (f : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0, n => if n = 0 then 1 else 0
  | k + 1, n => mulSeq (powSeq f k) f n

/-- Formal power series composition `(f ∘ g)_n` assuming `g 0 = 0`. -/
def compSeq (f g : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), f k * powSeq g k n

/-- Exponential of a formal power series `f` with `f 0 = 0`:
`(exp f)_n = ∑_{k=0}^n (f^k)_n / k!`. -/
def expSeq (f : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), powSeq f k n / (k.factorial : ℚ)

/-- Prefix `[A_0, A_1, ..., A_n]` of the e.g.f. coefficients of `A(x) = x * exp(A^{[4]}(x))`,
where `A^{[4]}` is the 4-fold compositional iterate of `A`. -/
def egfPrefix : ℕ → List ℚ
  | 0 => [0]
  | m + 1 =>
      let prev := egfPrefix m
      let f : ℕ → ℚ := fun k => prev.getD k 0
      let p2 := compSeq f f
      let p4 := compSeq p2 p2
      prev ++ [expSeq p4 m]

/-- Rational term `a(n) = n! * [x^n] A(x)` of OEIS A396804. -/
def a396804 (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * (egfPrefix n).getD n 0

/-- OEIS A396804 mod-3 conjecture: for every `n ≥ 1`, `a(n)` is an integer congruent to
`n % 3` modulo `3` (i.e., `[1, 2, 0]` repeating). -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, a396804 n = (m : ℚ) ∧ m % 3 = n % 3 := by
  sorry

end OMA.S_oeis_a396804
