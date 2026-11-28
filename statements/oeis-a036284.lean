import Mathlib

/-!
# Polynomials formed from the binary digits of Fibonacci numbers

Antti Karttunen's two conjectures in https://oeis.org/A036284.
The factor X in the quotient also accounts for the binary division by 2
in the definition of the companion sequence A136384.
-/
namespace OMA.S_oeis_a036284
open Polynomial
abbrev R := (ZMod 2)[X]

def digit (n k : ℕ) : ZMod 2 := ((Nat.fib k / 2^n % 2 : ℕ) : ZMod 2)
noncomputable def column (n : ℕ) : R :=
  ∑ k ∈ Finset.range (3*2^n), C (digit n k)*X^k

noncomputable def factor (n : ℕ) : R := (X^3+1)^(2^(n-1)-1)

theorem main : ∀ n : ℕ, 1 ≤ n →
    factor n ∣ column n ∧
    column n = factor n * (column n / factor n) ∧
    X*(X+1) ∣ column n / factor n := by
  sorry

end OMA.S_oeis_a036284
