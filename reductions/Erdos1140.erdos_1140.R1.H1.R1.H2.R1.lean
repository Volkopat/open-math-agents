import OMAReductions.R_Erdos1140_erdos_1140_R1_H1_R1
import Mathlib

/-!
# Class-number-two classification split at t = 3045

Source: Dongho Byeon and Jungyun Lee, Class number 2 problem for certain real
quadratic fields of Richaud--Degert type, Theorem 1.2. Its large-parameter
bound is the substantive analytic input H1. The remaining H2 is a finite-range
class-number classification, not yet discharged. Neither is assumed to be
proved by this reduction.
-/

namespace OMA.R_Erdos1140_erdos_1140_R1_H1_R1_H2_R1

/-- Large-parameter case of the Byeon--Lee class-number-two bound. -/
def H1 : Prop :=
  ∀ (n t : ℕ), n.Prime → t.Prime → Odd t → 2 * n = t ^ 2 + 1 → 3045 < t →
    ∀ (K : Type) [Field K] [NumberField K] (s : K),
      s ^ 2 = ((t ^ 2 + 1 : ℕ) : K) →
      Algebra.adjoin ℚ ({s} : Set K) = ⊤ →
      NumberField.classNumber K ≠ 2

/-- Small-parameter remainder, suited to finite class-number certificates. -/
def H2 : Prop :=
  ∀ (n t : ℕ), n.Prime → t.Prime → Odd t → 2 * n = t ^ 2 + 1 → t ≤ 3045 →
    ∀ (K : Type) [Field K] [NumberField K] (s : K),
      s ^ 2 = ((t ^ 2 + 1 : ℕ) : K) →
      Algebra.adjoin ℚ ({s} : Set K) = ⊤ →
      NumberField.classNumber K = 2 → t ≤ 19

theorem main : H1 → H2 →
    OMA.R_Erdos1140_erdos_1140_R1_H1_R1.H2 := by
  intro large small n t hn ht hodd hshape K _ _ s hsq hgen hclass
  by_cases hbound : t ≤ 3045
  · exact small n t hn ht hodd hshape hbound K s hsq hgen hclass
  · exact False.elim ((large n t hn ht hodd hshape (by omega) K s hsq hgen) hclass)

end OMA.R_Erdos1140_erdos_1140_R1_H1_R1_H2_R1
