import Mathlib

/-!
# Binary columns of powers of three, taken over a half-period

Sources: https://oeis.org/A037097 and https://oeis.org/A136386.
The coefficient at degree k is the n-th bit of 3^k, counting from bit zero.
A136386 is the encoded polynomial quotient. We use the divisor exponent
corrected on 24 July 2026 in A037097, which also matches its tabulated quotients.
Credit: @jiyongparkphysics
-/

namespace OMA.S_oeis_a037097

open Polynomial

abbrev R := (ZMod 2)[X]

def digit (n k : ℕ) : ZMod 2 := ((3^k / 2^n % 2 : ℕ) : ZMod 2)

noncomputable def column (n len : ℕ) : R :=
  ∑ k ∈ Finset.range len, C (digit n k) * X^k

noncomputable def quotient (n : ℕ) : R :=
  column n (2^(n-1)) / (X+1)^(2^(n-2)-1)

theorem main : ∀ n : ℕ, 3 ≤ n →
    (X+1)^(2^(n-2)-1) ∣ column n (2^(n-1)) ∧
    column n (2^(n-1)) = (X+1)^(2^(n-2)-1) * quotient n := by
  sorry

end OMA.S_oeis_a037097
