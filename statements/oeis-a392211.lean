import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Mathar's conjecture for OEIS A392211

Source: https://oeis.org/A392211 (R. J. Mathar, February 24, 2026).
Credit: @NOELOO6

Manyama's series starts at X¹. Formula (4.a) in the entry specifies the
zero-constant branch of a quartic. Formula (3.b) states the square-root
identity linking this series to its value at −X. The theorem includes
both characterizations and Mathar's recurrence wherever all coefficients
are defined, including the case n=5 with zero constant coefficient.
-/

namespace OMA.S_oeis_a392211
open PowerSeries
open scoped PowerSeries
noncomputable section

def quartic (S : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  25*S^4-35*S^3+(7+20*X)*S^2+(3-14*X)*S-(3*X-4*X^2)

/-- The six coefficients printed in OEIS A392211. -/
def p0 (n : ℚ) := 3840*n*(7977321*n-32086520)*(n-1)*(n-2)
def p1 (n : ℚ) := -64*(n-1)*(n-2)*(953294144*n^2-8954569952*n+20118837885)
def p2 (n : ℚ) := -15*(n-2)*(75138386499*n^3-602776477876*n^2
  +1515217257713*n-1239100034728)
def p3 (n : ℚ) := 8*(280596173198*n^4-4319298738497*n^3+24426073694308*n^2
  -60489429217342*n+55587559491135)
def p4 (n : ℚ) := 24000*(2*n-9)*(15954642*n^3-135968929*n^2+388189337*n-380277463)
def p5 (n : ℚ) := -12800*(29790442*n-101087659)*(n-5)*(2*n-9)*(2*n-11)

def recurrenceAt (S : ℚ⟦X⟧) (n : ℕ) : Prop :=
  p0 n*coeff n S + p1 n*coeff (n-1) S + p2 n*coeff (n-2) S + p3 n*coeff (n-3) S
    + p4 n*coeff (n-4) S + p5 n*coeff (n-5) S=0

theorem main : ∃ S : ℚ⟦X⟧, constantCoeff S=0 ∧ quartic S=0 ∧
    (∀ T : ℚ⟦X⟧, constantCoeff T=0 → quartic T=0 → T=S) ∧
    (∃ R : ℚ⟦X⟧, constantCoeff R=1 ∧ R^2=1+4*rescale (-1) S-4*(rescale (-1) S)^2 ∧
      2*S=1-R) ∧ ∀ n : ℕ, 5 ≤ n → recurrenceAt S n := by
  sorry

end
end OMA.S_oeis_a392211
