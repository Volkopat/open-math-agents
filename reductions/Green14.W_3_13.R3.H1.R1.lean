import OMAReductions.R_Green14_W_3_13_R3
import Mathlib.Tactic

/-!
Split the shared-endpoint case by the relative lengths of its two blue
runs. Equal gaps already give a red 3-progression. The two adjacent
largest gap sizes force a full blue progression of step two.

Credit: @justusklocke-cloud
-/

namespace OMA.R_Green14_W_3_13_R3_H1_R1

private theorem gap_twelve_then_thirteen {R : ℕ → Prop} {p q v : ℕ}
    (hp : 0 < p) (hq : q = p + 12) (hv : v = q + 13) (hvlt : v < 160)
    (hrq : R q) (hrv : R v)
    (hleft : ∀ x, p < x → x < q → ¬ R x)
    (hright : ∀ x, q < x → x < v → ¬ R x)
    (hfree : ∀ a d, 0 < d → a + 2*d < 160 → R a → R (a+d) → R (a+2*d) → False)
    (hmeets : ∀ a d, 0 < d → a + 12*d < 160 → ∃ i : Fin 13, R (a+i.val*d)) : False := by
  have hblue : ¬ R (p - 1) := by
    intro h
    refine hfree (p - 1) 13 (by decide) (by omega) h ?_ ?_
    · simpa only [show p - 1 + 13 = q by omega] using hrq
    · simpa only [show p - 1 + 2*13 = v by omega] using hrv
  obtain ⟨i, hi⟩ := hmeets (p - 1) 2 (by decide) (by omega)
  have hiBound := i.isLt
  by_cases hi0 : i.val = 0
  · exact hblue (by simpa [hi0] using hi)
  · by_cases hil : p - 1 + i.val*2 < q
    · exact hleft _ (by omega) hil hi
    · exact hright _ (by omega) (by omega) hi

private theorem gap_thirteen_then_twelve {R : ℕ → Prop} {p q v : ℕ}
    (hq : q = p + 13) (hv : v = q + 12) (hpq : p + q ≤ 159)
    (hrp : R p) (hrq : R q)
    (hleft : ∀ x, p < x → x < q → ¬ R x)
    (hright : ∀ x, q < x → x < v → ¬ R x)
    (hfree : ∀ a d, 0 < d → a + 2*d < 160 → R a → R (a+d) → R (a+2*d) → False)
    (hmeets : ∀ a d, 0 < d → a + 12*d < 160 → ∃ i : Fin 13, R (a+i.val*d)) : False := by
  have hblue : ¬ R (p + 26) := by
    intro h
    refine hfree p 13 (by decide) (by omega) hrp ?_ ?_
    · simpa only [show p + 13 = q by omega] using hrq
    · simpa only [show p + 2*13 = p + 26 by omega] using h
  obtain ⟨i, hi⟩ := hmeets (p + 2) 2 (by decide) (by omega)
  have hiBound := i.isLt
  by_cases hi12 : i.val = 12
  · exact hblue (by simpa [hi12, show p + 2 + 12*2 = p + 26 by omega] using hi)
  · by_cases hil : p + 2 + i.val*2 < q
    · exact hleft _ (by omega) hil hi
    · exact hright _ (by omega) (by omega) hi

/-- The left blue run is shorter, excluding gap sizes 12 and 13. -/
def H1 : Prop :=
  ∀ (R : ℕ → Prop) (p q v : ℕ),
    (17 ≤ p ∧ p+8 ≤ q ∧ q ≤ p+13 ∧ p+q ≤ 159 ∧ q+6 ≤ v ∧ v ≤ q+13 ∧
      v < 160 ∧ (q ≤ 62 → q+7 ≤ v) ∧ (q ≤ 41 → q+8 ≤ v)) →
    (R p ∧ R q ∧ ∀ x, p < x → x < q → ¬ R x) →
    (R q ∧ R v ∧ ∀ x, q < x → x < v → ¬ R x) →
    (∀ o h : ℕ, 0 < h → o+68*h < 160 →
      ∃ a, a+4 < 69 ∧ ∀ i : Fin 5, ¬ R (o+(a+i.val)*h)) →
    (∀ a d, 0 < d → a+2*d < 160 → R a → R (a+d) → R (a+2*d) → False) →
    (∀ a d, 0 < d → a+12*d < 160 → ∃ i : Fin 13, R (a+i.val*d)) →
    q-p < v-q → ¬ (q = p+12 ∧ v = q+13) → False

/-- The right blue run is shorter, excluding gap sizes 13 and 12. -/
def H2 : Prop :=
  ∀ (R : ℕ → Prop) (p q v : ℕ),
    (17 ≤ p ∧ p+8 ≤ q ∧ q ≤ p+13 ∧ p+q ≤ 159 ∧ q+6 ≤ v ∧ v ≤ q+13 ∧
      v < 160 ∧ (q ≤ 62 → q+7 ≤ v) ∧ (q ≤ 41 → q+8 ≤ v)) →
    (R p ∧ R q ∧ ∀ x, p < x → x < q → ¬ R x) →
    (R q ∧ R v ∧ ∀ x, q < x → x < v → ¬ R x) →
    (∀ o h : ℕ, 0 < h → o+68*h < 160 →
      ∃ a, a+4 < 69 ∧ ∀ i : Fin 5, ¬ R (o+(a+i.val)*h)) →
    (∀ a d, 0 < d → a+2*d < 160 → R a → R (a+d) → R (a+2*d) → False) →
    (∀ a d, 0 < d → a+12*d < 160 → ∃ i : Fin 13, R (a+i.val*d)) →
    v-q < q-p → ¬ (q = p+13 ∧ v = q+12) → False

theorem main : H1 → H2 → OMA.R_Green14_W_3_13_R3.H1 := by
  intro shorterLeft shorterRight R p q v widths leftGap rightGap five free meets
  have hw : 17 ≤ p ∧ p+8 ≤ q ∧ q ≤ p+13 ∧ p+q ≤ 159 ∧ q+6 ≤ v ∧
      v ≤ q+13 ∧ v < 160 ∧ (q ≤ 62 → q+7 ≤ v) ∧ (q ≤ 41 → q+8 ≤ v) := widths
  have hl : R p ∧ R q ∧ ∀ x, p < x → x < q → ¬ R x := leftGap
  have hr : R q ∧ R v ∧ ∀ x, q < x → x < v → ¬ R x := rightGap
  obtain ⟨hp, hpq, _, hsum, hqv, _, hv, _, _⟩ := hw
  rcases lt_trichotomy (q - p) (v - q) with h | h | h
  · by_cases hmax : q = p+12 ∧ v = q+13
    · exact gap_twelve_then_thirteen (by omega) hmax.1 hmax.2 hv hl.2.1 hr.2.1
        hl.2.2 hr.2.2 free meets
    · exact shorterLeft R p q v widths leftGap rightGap five free meets h hmax
  · refine free p (q - p) (by omega) (by omega) hl.1 ?_ ?_
    · simpa only [show p + (q - p) = q by omega] using hl.2.1
    · simpa only [show p + 2*(q - p) = v by omega] using hr.2.1
  · by_cases hmax : q = p+13 ∧ v = q+12
    · exact gap_thirteen_then_twelve hmax.1 hmax.2 hsum hl.1 hl.2.1 hl.2.2 hr.2.2 free meets
    · exact shorterRight R p q v widths leftGap rightGap five free meets h hmax

end OMA.R_Green14_W_3_13_R3_H1_R1
