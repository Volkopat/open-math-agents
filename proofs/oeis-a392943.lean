import OMAStatements.S_oeis_a392943
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace OMA.A392943

/-- An integral leg of a rational right triangle with even integral hypotenuse is even. -/
theorem even_leg {r x : ℤ} (h : IsSquare (((2 * r) ^ 2 - x ^ 2 : ℤ) : ℚ)) :
    2 ∣ x := by
  obtain ⟨w, hw⟩ := Rat.isSquare_intCast_iff.mp h
  by_contra hx
  obtain ⟨u, hu⟩ := Int.not_even_iff_odd.mp (fun he => hx (even_iff_two_dvd.mp he))
  rcases Int.even_or_odd w with ⟨v, hv⟩ | ⟨v, hv⟩ <;>
    rw [hu, hv] at hw <;> ring_nf at hw <;> omega

/-- Heron's polynomial and the circumradius equation supply the rational complementary leg.
The third side is integral; the other two sides may be rational. -/
theorem even_side {a b : ℚ} {c r : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : (a * b * c) ^ 2 =
      (r : ℚ) ^ 2 * ((a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c))) :
    2 ∣ c := by
  apply even_leg (r := r)
  refine ⟨r * (a ^ 2 + b ^ 2 - c ^ 2) / (a * b), ?_⟩
  push_cast
  field_simp
  linear_combination -h

end OMA.A392943

open OMA.A392943 OMA.S_oeis_a392943 in
theorem OMA.solution : type_of% @OMA.S_oeis_a392943.main := by
  rintro ⟨a, b, c, K, R, ha, hb, hc, _, _, _, hg, _, hK, _, hR⟩
  dsimp [hasArea] at hK
  have area : (4 * (K : ℚ)) ^ 2 =
      (a + b + c : ℚ) * (- (a : ℚ) + b + c) * (a - b + c : ℚ) * (a + b - c : ℚ) := by
    have mapped := congrArg (fun t : ℤ => (t : ℚ)) hK
    push_cast at mapped
    exact mapped
  have radius : 4 * (R : ℚ) * K = a * b * c := by exact_mod_cast hR
  have h : ((a : ℚ) * b * c) ^ 2 =
      (R : ℚ) ^ 2 * ((a + b + c : ℚ) * (- (a : ℚ) + b + c) *
        (a - b + c : ℚ) * (a + b - c : ℚ)) := by
    rw [← radius, ← area]
    ring
  have evenC : 2 ∣ c := by
    exact_mod_cast even_side (c := (c : ℤ)) (r := (R : ℤ))
      (a := (a : ℚ)) (b := (b : ℚ)) (by positivity) (by positivity) (by push_cast; exact h)
  have evenA : 2 ∣ a := by
    exact_mod_cast even_side (c := (a : ℤ)) (r := (R : ℤ))
      (a := (b : ℚ)) (b := (c : ℚ)) (by positivity) (by positivity) (by push_cast; linear_combination h)
  have evenB : 2 ∣ b := by
    exact_mod_cast even_side (c := (b : ℤ)) (r := (R : ℤ))
      (a := (a : ℚ)) (b := (c : ℚ)) (by positivity) (by positivity) (by push_cast; linear_combination h)
  have hd := Nat.dvd_gcd (Nat.dvd_gcd evenA evenB) evenC
  omega
