import Mathlib

/-!
# McEachen's heptagon quotient (OEIS A160389)

The numerator A060557 has generating function (1-x)²/(1-5x+6x²-x³).
The denominator A052975 has generating function (1-2x)(1-x)/(1-5x+6x²-x³).
These give the same recurrence with independent initial triples, as in the
respective OEIS entries. Both start at index zero. A160389 is the decimal
expansion of the real constant 2 cos(π/7).

Bill McEachen conjectured this limit on February 17, 2026.
Sources: https://oeis.org/A160389, https://oeis.org/A060557, https://oeis.org/A052975
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a160389
open Filter Topology

def linearSequence (u v w : ℤ) : ℕ → ℤ
  | 0 => u
  | 1 => v
  | 2 => w
  | n+3 => 5*linearSequence u v w (n+2)-6*linearSequence u v w (n+1)+linearSequence u v w n

def numerator := linearSequence 1 3 10
def denominator := linearSequence 1 2 6
noncomputable def rho : ℝ := 2*Real.cos (Real.pi/7)

theorem main :
    Tendsto (fun n : ℕ => (numerator n : ℝ)/(denominator n : ℝ)) atTop (𝓝 rho) := by
  sorry

end OMA.S_oeis_a160389
