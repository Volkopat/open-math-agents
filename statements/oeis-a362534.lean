import Mathlib

/-!
# A362534. Numerators of polarization-transfer bounds

Source: https://oeis.org/A362534
Credit: @etaubman
Mohamed Sabba formulated the conjecture. The counterexample at 19 was
previously verified by the TrureTuring project:
https://www.trureturing.org/research/sabba-2023-a362534-polarization-transfer-refutation/

The floor quotient n/2 selects the middle binomial index for odd and even n.
For n ≥ 1, division by 2^(n-1) equals multiplication by 2^(1-n).
-/

namespace OMA.S_oeis_a362534

def f (n : ℕ) : ℚ :=
  (n : ℚ) * (Nat.choose (n-1) (n/2) : ℚ) / 2^(n-1)

def g (n : ℕ) : ℚ :=
  2 * (1 - (Nat.choose n (n/2) : ℚ) / 2^n)

def conjecture : Prop :=
  ∀ n : ℕ, 0 < n → (g n).num = ((f n / g n).den : ℤ)

theorem main : conjecture := by
  sorry

end OMA.S_oeis_a362534
