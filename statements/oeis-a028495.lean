import Mathlib

/-!
# Two growth asymptotics for A028495

The coefficient sequence of (1-x²)/(1-x-2x²+x³) is defined by the
recurrence and initial values in the original entry. A160389 is the real
number 2 cos(π/7). A116425 is the real number 2 + 2 cos(2π/7).
Bill McEachen (February 2026) conjectured both asymptotic equivalents.
Writing n+1 in place of n makes the predecessor index valid for all n.

Sources: https://oeis.org/A028495, https://oeis.org/A160389,
https://oeis.org/A116425
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a028495
open Filter Topology

def a : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | n+3 => a (n+2) + 2*a (n+1) - a n

noncomputable def rho : ℝ := 2 * Real.cos (Real.pi/7)
noncomputable def beraha : ℝ := 2 + 2 * Real.cos (2*Real.pi/7)

theorem main :
    Tendsto (fun n : ℕ => (a (n+1) : ℝ)/(rho * (a n : ℝ))) atTop (𝓝 1) ∧
    Tendsto (fun n : ℕ => (a (n+1) : ℝ)/(Real.sqrt beraha * (a n : ℝ))) atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a028495
