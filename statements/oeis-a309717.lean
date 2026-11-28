import Mathlib

/-!
# The Fibonacci, Pell and bronze Fibonacci convolution (OEIS A309717)

A073133 has entry `F_n(t)` with `F_0(t)=0`, `F_1(t)=1` and
`F_{n+2}(t)=t F_{n+1}(t)+F_n(t)`. Its values at 1, 2 and 3 give the
three sequences in A309717. Multiplication of ordinary generating functions
takes their Cauchy convolution. Row n of A117936 takes the inverse binomial
transform of `F_n(1), F_n(2), ...`, starting at column 1. The third column
exists for n ≥ 3. The conjecture says that its entry is twice A309717(n).

Sources: https://oeis.org/A309717, https://oeis.org/A117936, https://oeis.org/A073133
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a309717
open PowerSeries

def fibPoly (t : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => t * fibPoly t (n + 1) + fibPoly t n

noncomputable def series (t : ℤ) : ℤ⟦X⟧ := PowerSeries.mk (fibPoly t)

noncomputable def a (n : ℕ) : ℤ := coeff n (series 1 * series 2 * series 3)

def triangle (n k : ℕ) : ℤ := ∑ j ∈ Finset.range k,
  (-1 : ℤ) ^ (k - 1 - j) * ((k - 1).choose j : ℤ) * fibPoly (j + 1 : ℕ) n

theorem main : ∀ n : ℕ, 3 ≤ n → 2 * a n = triangle n 3 := by
  sorry

end OMA.S_oeis_a309717
