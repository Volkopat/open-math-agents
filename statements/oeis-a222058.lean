import Mathlib

/-!
# The harmonic-geometric series for A222058

The original finite formula for the harmonic-geometric number uses the
Stirling numbers of the second kind and the unsigned numbers of the first
kind. Velin Yanev's July 2026 OEIS conjecture gives a different formula
as an infinite series involving harmonic numbers and log 2.

The generating-function formulas of Ayhan Dil and Veli Kurt specialize
to this identity at x = 1/2. See equations (33) and (53) in their paper,
https://arxiv.org/abs/0912.1834, and the sequence at https://oeis.org/A222058.
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a222058
open Finset

def geometricHarmonic (n : ℕ) : ℕ :=
  ∑ j ∈ range (n+1), Nat.stirlingSecond n j * Nat.stirlingFirst (j+1) 2

theorem main : ∀ n : ℕ,
    HasSum (fun k : ℕ => (k:ℝ)^n * ((harmonic k:ℝ)-Real.log 2) / 2^(k+1))
      (geometricHarmonic n:ℝ) := by
  sorry

end OMA.S_oeis_a222058
