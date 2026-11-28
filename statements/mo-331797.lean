import Mathlib

/-!
# An odd-grid sine quotient sum

Source: https://mathoverflow.net/questions/331797
Write p = 4N+2 so the odd grid consists of 2j+1 with 0 ≤ j < N. To
read off both signs, write r/q modulo 2p as ±(2t+1) of magnitude < p.
This signed representative is unique under the stated coprimality and
parity conditions. The modular reduction was suggested by alpoge and
LSpice in the comments on the source question.

Credit: @connoranderson
-/

namespace OMA.S_mo_331797

noncomputable def sineSum (N q r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, Real.sin ((r:ℝ)*(2*j+1)*Real.pi/(4*N+2)) /
    Real.sin ((q:ℝ)*(2*j+1)*Real.pi/(4*N+2))

noncomputable def magnitude (N t : ℕ) : ℝ := (2*N+1-(-1:ℝ)^t)/2

theorem main : ∀ N q r : ℕ, let p := 4*N+2
    q.Coprime p → q < p → 1 ≤ r → r < p → Odd r →
    ∃ t : ℕ, t < 2*N+1 ∧
      ((r ≡ q*(2*t+1) [MOD 2*p] ∧ sineSum N q r = magnitude N t) ∨
       (r+q*(2*t+1) ≡ 0 [MOD 2*p] ∧ sineSum N q r = -magnitude N t)) := by
  sorry

end OMA.S_mo_331797
