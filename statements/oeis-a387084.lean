import Mathlib.Data.Nat.Choose.Basic
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Mathar's conjecture for OEIS A387084

Source: https://oeis.org/A387084 (R. J. Mathar, August 19, 2025).
Credit: @NOELOO6

Manyama defines the generating function by dividing B by the normalized
square root of 1+4(B−1)/5. Squaring this quotient and clearing five gives
the equivalent normalized identity below. The recurrence starts at n = 4,
the first index at which all five terms are defined.
-/

namespace OMA.S_oeis_a387084
open PowerSeries
open scoped PowerSeries
noncomputable section

/-- The generating series B has coefficient binomial(5n,n), as in OEIS A001449. -/
def B : ℚ⟦X⟧ := mk fun n => (Nat.choose (5*n) n : ℚ)

/-- The squaring identity for the normalized quotient, with the factor five cleared. -/
def Normalized (S : ℚ⟦X⟧) : Prop :=
  constantCoeff S = 1 ∧ S^2*(1+4*B)=5*B^2

/-- The five polynomial coefficients in R. J. Mathar's recurrence. -/
def p0 (n : ℚ) := 3902464*n*(8*n-5)*(8*n-3)*(8*n-1)*(8*n+1)
def p1 (n : ℚ) := 80*(-12565760000*n^5+68448000000*n^4-163457516000*n^3
  +200475354000*n^2-122843089511*n+29804717943)
def p2 (n : ℚ) := 125000*(134055000*n^5-1109795000*n^4+3726971625*n^3
  -6307124125*n^2+5325821766*n-1769460798)
def p3 (n : ℚ) := 48828125*(-1556875*n^5+15845625*n^4-60659875*n^3
  +103818375*n^2-67764178*n+1391424)
def p4 (n : ℚ) := -152587890625*(5*n-16)*(n-3)*(5*n-19)*(5*n-18)*(5*n-17)

def recurrenceAt (S : ℚ⟦X⟧) (n : ℕ) : Prop :=
  p0 n*coeff n S + p1 n*coeff (n-1) S + p2 n*coeff (n-2) S +
    p3 n*coeff (n-3) S + p4 n*coeff (n-4) S=0

theorem main : ∃ S : ℚ⟦X⟧, Normalized S ∧
    (∀ T : ℚ⟦X⟧, Normalized T → T = S) ∧ ∀ n : ℕ, 4 ≤ n → recurrenceAt S n := by
  sorry

end
end OMA.S_oeis_a387084
