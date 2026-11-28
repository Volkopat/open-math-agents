import Mathlib

/-!
# A Viète-like limit for π

S. M. Abrarov and B. M. Quine proposed the limit in OEIS A282089. The entry
also records the resulting convergence of the series defining the constant
whose decimal digits it lists. Here the index `n = 0` denotes the source's
first term, `k = 1`, so its scale factor `2^(k+1)` becomes `2^(n+2)`.

Sources: https://oeis.org/A282089 (OEIS Foundation, CC BY-SA 4.0)
and https://arxiv.org/abs/1702.00901.
Credit: @connoranderson
-/

namespace OMA.S_oeis_a282089

noncomputable def a : ℕ → ℝ
  | 0 => Real.sqrt 2
  | n+1 => Real.sqrt (2 + a n)

noncomputable def b (n : ℕ) : ℝ := Real.sqrt (2 - a n) / a (n+1)

noncomputable def c : ℕ → ℝ
  | 0 => b 0
  | n+1 => (c n + b (n+1)) / (1 - c n * b (n+1))

theorem main :
    Filter.Tendsto (fun n : ℕ => (2:ℝ)^(n+2)*(1-c n)) Filter.atTop (nhds Real.pi) ∧
      Summable (fun n : ℕ => 1-c n) := by
  sorry

end OMA.S_oeis_a282089
