import Mathlib

/-!
# A242172: a(n) = 2^n*binomial((n + 1 + (n mod 2))/2, 1/2)

Source: https://oeis.org/A242172
Credit: @ivillar

Peter Luschny's sequence (offset 0): a(n) = 2^n*binomial((n + 1 + (n mod 2))/2, 1/2), where the
first argument (n + 1 + (n mod 2))/2 is a half-integer and binomial(x, y) is the binomial
coefficient extended to real arguments by binomial(x, y) = Γ(x+1)/(Γ(y+1)*Γ(x-y+1)), as in the
entry's Mathematica program `2^n*Binomial[(n + 1 + Mod[n, 2])/2, 1/2]` (data 1, 3, 6, 15, 30, ...).

Conjecture (R. J. Mathar, May 11 2014): (n+1)*a(n) -2*a(n-1) +4*(-n-1)*a(n-2)=0,
stated for every n ≥ 2 (so that a(n-2) is defined).
-/

namespace OMA.S_oeis_a242172

/-- The binomial coefficient for real arguments, binomial(x, y) = Γ(x+1)/(Γ(y+1)Γ(x-y+1)), as used by
Mathematica's Binomial for non-integer arguments. -/
noncomputable def gbinom (x y : ℝ) : ℝ :=
  Real.Gamma (x + 1) / (Real.Gamma (y + 1) * Real.Gamma (x - y + 1))

/-- a(n) = 2^n*binomial((n + 1 + (n mod 2))/2, 1/2) (offset 0). -/
noncomputable def a (n : ℕ) : ℝ := 2 ^ n * gbinom (((n : ℝ) + 1 + ((n % 2 : ℕ) : ℝ)) / 2) (1 / 2)

/-- Mathar's conjecture: (n+1)*a(n) - 2*a(n-1) + 4*(-n-1)*a(n-2) = 0 for every n ≥ 2. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    ((n : ℝ) + 1) * a n - 2 * a (n - 1) + 4 * (-(n : ℝ) - 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a242172
