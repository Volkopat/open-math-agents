import Mathlib

/-!
# Binary columns of powers of three as polynomials over GF(2)

Source: https://oeis.org/A037096. The finite column has its bit from 3^k at
degree k. A037097 retains half the column; A136386 gives its polynomial quotient.
-/
namespace OMA.S_oeis_a037096
open Polynomial
abbrev R := (ZMod 2)[X]

def digit (n k : ℕ) : ZMod 2 := ((3^k / 2^n % 2 : ℕ) : ZMod 2)

noncomputable def column (n len : ℕ) : R :=
  ∑ k ∈ Finset.range len, C (digit n k)*X^k

noncomputable def quotient (n : ℕ) : R :=
  column n (2^(n-1)) / (X+1)^(2^(n-2)-1)

theorem main : ∀ n : ℕ, 3 ≤ n →
    (X+1)^(3*2^(n-2)-1) ∣ column n (2^n) ∧
    column n (2^n)=(X+1)^(3*2^(n-2)-1)*quotient n := by
  sorry

end OMA.S_oeis_a037096
