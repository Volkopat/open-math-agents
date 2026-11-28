import Mathlib

/-!
# A245688: n^2 + 1 as a product of three distinct Fibonacci numbers

Source: https://oeis.org/A245688 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A245688 (offset 1): numbers n such that n^2 + 1 is the product of three distinct Fibonacci
numbers > 1; data 47, 99, 123, 322, 843, 2207, 5778, 15075, 15127, 39603, ...
(for example 47^2 + 1 = 2210 = 5 * 13 * 34).

The entry records:

  Conjecture: except the numbers 99 and 15075, all the terms belong to A005248 (bisection of
  Lucas numbers).
  The above conjecture holds for the first 1000 terms. (Jens Kruse Andersen, Aug 10 2014)

Reading of the source:
* "three distinct Fibonacci numbers > 1": three pairwise different values `x < y < z`, each a
  Fibonacci number `Nat.fib i` and each greater than 1, with `n^2 + 1 = x * y * z`.
* The terms are positive (offset 1, first term 47); `n` ranges over positive naturals.
* A005248 is the bisection L(2k), k ≥ 0, of the Lucas numbers L(0) = 2, L(1) = 1,
  L(k+2) = L(k+1) + L(k): 2, 3, 7, 18, 47, 123, 322, 843, 2207, 5778, ...
-/

namespace OMA.S_oeis_a245688

/-- The Lucas numbers: L(0) = 2, L(1) = 1, L(k+2) = L(k+1) + L(k). -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | k + 2 => lucas (k + 1) + lucas k

/-- `n` is a term of A245688: `n > 0` and `n^2 + 1` is the product of three distinct
Fibonacci numbers, each greater than 1. -/
def IsTerm (n : ℕ) : Prop :=
  0 < n ∧ ∃ i j k : ℕ, 1 < Nat.fib i ∧ Nat.fib i < Nat.fib j ∧ Nat.fib j < Nat.fib k ∧
    n ^ 2 + 1 = Nat.fib i * Nat.fib j * Nat.fib k

/-- Every term other than 99 and 15075 is a Lucas number of even index (a term of A005248). -/
theorem main : ∀ n : ℕ, IsTerm n → n ≠ 99 → n ≠ 15075 → ∃ k : ℕ, n = lucas (2 * k) := by
  sorry

end OMA.S_oeis_a245688
