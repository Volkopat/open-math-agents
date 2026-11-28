import OMAStatements.S_oeis_a002387
import Mathlib

/-!
# A002387 via bounds around the half-integer

Dean Hickerson's bounds in the OEIS entry put the conjectured threshold at
the rounded value or its predecessor. To exclude the predecessor, it is
enough that an integer threshold stay above the entire error interval there.

Source: https://oeis.org/A002387
-/

namespace OMA.R_oeis_a002387_R1

open Real

private theorem harmonic_mono : Monotone harmonic :=
  monotone_nat_of_le_succ fun k => by
    rw [harmonic_succ]
    exact le_add_of_nonneg_right (by positivity)

private theorem rounding_bounds (n : ℕ) (hn : 1 < n) :
    let x := exp ((n : ℝ) - eulerMascheroniConstant)
    let m := ⌊x + 1 / 2⌋₊
    0 < m ∧ (m : ℝ) ≤ x + 1 / 2 ∧ x + 1 / 2 < (m : ℝ) + 1 := by
  let x := exp ((n : ℝ) - eulerMascheroniConstant)
  let m := ⌊x + 1 / 2⌋₊
  have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hx : 1 < x := by
    change 1 < exp ((n : ℝ) - eulerMascheroniConstant)
    rw [← exp_zero, exp_lt_exp]
    linarith [eulerMascheroniConstant_lt_two_thirds]
  have hle : (m : ℝ) ≤ x + 1 / 2 := Nat.floor_le (by linarith)
  have hlt : x + 1 / 2 < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hm : 0 < m := by
    by_contra! h
    have hm0 : m = 0 := by omega
    simp [hm0] at hlt
    linarith
  exact ⟨hm, hle, hlt⟩

/-- The two analytic error bounds at the half-integer approximation. -/
def H1 : Prop :=
  ∀ k : ℕ, 0 < k →
    log ((k : ℝ) + 1 / 2) + eulerMascheroniConstant < (harmonic k : ℝ) ∧
    (harmonic k : ℝ) <
      log ((k : ℝ) + 1 / 2) + eulerMascheroniConstant + 1 / (24 * (k : ℝ) ^ 2)

/-- The upper error bound stays below the integer level at the candidate's predecessor. -/
def H2 : Prop :=
  ∀ n k : ℕ, 1 < n → 0 < k →
    (k : ℝ) + 1 / 2 ≤ exp ((n : ℝ) - eulerMascheroniConstant) →
    exp ((n : ℝ) - eulerMascheroniConstant) < (k : ℝ) + 3 / 2 →
    log ((k : ℝ) + 1 / 2) + eulerMascheroniConstant + 1 / (24 * (k : ℝ) ^ 2) ≤ (n : ℝ)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a002387.main := by
  intro sharp gap n hn
  let x := exp ((n : ℝ) - eulerMascheroniConstant)
  let m := ⌊x + 1 / 2⌋₊
  obtain ⟨hm, hle, hlt⟩ := rounding_bounds n hn
  change 0 < m at hm
  change (m : ℝ) ≤ x + 1 / 2 at hle
  change x + 1 / 2 < (m : ℝ) + 1 at hlt
  have hlog : (n : ℝ) - eulerMascheroniConstant < log ((m : ℝ) + 1 / 2) :=
    (lt_log_iff_exp_lt (by positivity)).mpr (by change x < (m : ℝ) + 1 / 2; linarith)
  have hgood : (n : ℚ) < harmonic m := by
    have hr : (n : ℝ) < (harmonic m : ℝ) := by linarith [(sharp m hm).1]
    exact_mod_cast hr
  have hprev : harmonic (m - 1) ≤ (n : ℚ) := by
    by_cases hk : m - 1 = 0
    · rw [hk, harmonic_zero]
      positivity
    have hkpos : 0 < m - 1 := Nat.pos_of_ne_zero hk
    have hcast : (((m - 1 : ℕ) : ℝ)) + 1 = (m : ℝ) := by
      exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ m))
    have hgap := gap n (m - 1) hn hkpos (by change _ ≤ x; linarith)
      (by change x < _; linarith)
    have hr : (harmonic (m - 1) : ℝ) ≤ (n : ℝ) :=
      (lt_of_lt_of_le (sharp (m - 1) hkpos).2 hgap).le
    exact_mod_cast hr
  refine ⟨hgood, ?_⟩
  intro j hj
  change m ≤ j
  change (n : ℚ) < harmonic j at hj
  by_contra! h
  exact (not_lt_of_ge ((harmonic_mono (show j ≤ m - 1 by omega)).trans hprev)) hj

end OMA.R_oeis_a002387_R1
