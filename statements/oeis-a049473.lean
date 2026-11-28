import Mathlib

/-!
# The zeta(3) tail and the differences of A049473

A049473 is the nearest integer to n/√2, with offset zero. For clarity the
tail ζ(3) − Σ_{k=1}^m 1/k³ is written as the convergent sum from m+1
onward. The differences are indexed by the left endpoint, starting
with a(1)-a(0)=1 at position zero. The two sets of positions are the
nonhomogeneous Beatty sequences A001954 and A001953, both indexed
from zero. This states both assertions in Clark Kimberling's 2014 comment.
Source: https://oeis.org/A049473
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a049473

noncomputable def nearest (n : ℕ) : ℕ := ⌊(n:ℝ) / Real.sqrt 2 + 1/2⌋₊

noncomputable def tail (m : ℕ) : ℝ := ∑' j : ℕ, 1 / ((m:ℝ) + j + 1)^3

noncomputable def beatty (s : ℝ) (k : ℕ) : ℕ := ⌊((k:ℝ)+1/2)*s⌋₊

theorem main :
    (∀ n : ℕ, 0 < n → tail (nearest n) < 1/(n:ℝ)^2 ∧ 1/(n:ℝ)^2 < tail (nearest n-1)) ∧
    (∀ n : ℕ, (nearest (n+1) = nearest n ∨ nearest (n+1) = nearest n+1) ∧
      (nearest (n+1) = nearest n ↔ ∃ k : ℕ, beatty (2+Real.sqrt 2) k = n) ∧
      (nearest (n+1) = nearest n+1 ↔ ∃ k : ℕ, beatty (Real.sqrt 2) k = n)) := by
  sorry

end OMA.S_oeis_a049473
