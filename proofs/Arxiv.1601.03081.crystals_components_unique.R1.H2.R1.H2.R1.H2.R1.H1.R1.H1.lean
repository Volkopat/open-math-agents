import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H2_R1_H1_R1
import Mathlib

/-!
# Vieta jumping on `(a + 1)(b + 1) ∣ (a + b)²` for odd `a, b`

Writing `a + 1 = 2x` and `b + 1 = 2y` (`x, y ≥ 1`), the divisibility `(a + 1)(b + 1) ∣ (a + b)²`
is equivalent to `x * y ∣ (x + y - 1)²`. Writing `(x + y - 1)² = k * x * y` and assuming without
loss of generality `y ≤ x`:
* If `y = 1`, then `b + 1 = 2 * 1²`.
* `x = y ≥ 2` is impossible since `(2y - 1)² = k * y²` forces `y ∣ 1`.
* For `2 ≤ y < x`, the Vieta conjugate `x' = k * y + 2 - 2 * y - x` satisfies
  `x * x' = (y - 1)²`, `1 ≤ x' < y`, and `(x' + y - 1)² = k * x' * y`. By strong induction on
  `x + y`, either `y` or `x'` is a square; since `x * x' = (y - 1)²` preserves squareness, either
  `x` or `y` is a square.
-/

namespace CrystalsVietaProof

private lemma dvd_of_sq_dvd_sq {w m : ℕ} (hw : 0 < w) (h : w * w ∣ m * m) : w ∣ m := by
  let g := Nat.gcd w m
  have hg : 0 < g := Nat.gcd_pos_of_pos_left m hw
  have hcop : Nat.Coprime (w / g) (m / g) := Nat.coprime_div_gcd_div_gcd hg
  have hw_eq : g * (w / g) = w := Nat.mul_div_cancel' (Nat.gcd_dvd_left w m)
  have hm_eq : g * (m / g) = m := Nat.mul_div_cancel' (Nat.gcd_dvd_right w m)
  have hmul : (g * g) * ((w / g) * (w / g)) ∣ (g * g) * ((m / g) * (m / g)) := by
    have e1 : (g * g) * ((w / g) * (w / g)) = (g * (w / g)) * (g * (w / g)) := by ring
    have e2 : (g * g) * ((m / g) * (m / g)) = (g * (m / g)) * (g * (m / g)) := by ring
    rwa [e1, e2, hw_eq, hm_eq]
  have hdvd1 : (w / g) * (w / g) ∣ (m / g) * (m / g) :=
    (Nat.mul_dvd_mul_iff_left (Nat.mul_pos hg hg)).mp hmul
  have hdvd2 : w / g ∣ (m / g) * (m / g) := dvd_trans ⟨w / g, rfl⟩ hdvd1
  have hdvd3 : w / g ∣ m / g := hcop.dvd_of_dvd_mul_right hdvd2
  have hdvd4 : w / g ∣ 1 := by
    have h1 : w / g ∣ Nat.gcd (w / g) (m / g) := Nat.dvd_gcd dvd_rfl hdvd3
    rwa [hcop.gcd_eq_one] at h1
  have hw1 : w / g = 1 := Nat.eq_one_of_dvd_one hdvd4
  rw [hw1, mul_one] at hw_eq
  rw [← hw_eq]
  exact Nat.gcd_dvd_right w m

private lemma vieta_step {x y : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hyx : y ≤ x)
    (hdvd : x * y ∣ (x + y - 1) ^ 2)
    (ih : ∀ x' y' : ℕ, x' + y' < x + y → 1 ≤ x' → 1 ≤ y' →
      x' * y' ∣ (x' + y' - 1) ^ 2 → (∃ u : ℕ, x' = u ^ 2) ∨ (∃ v : ℕ, y' = v ^ 2)) :
    (∃ u : ℕ, x = u ^ 2) ∨ (∃ v : ℕ, y = v ^ 2) := by
  by_cases hy1 : y = 1
  · exact Or.inr ⟨1, by omega⟩
  have hy2 : 2 ≤ y := by omega
  obtain ⟨k, hk⟩ := hdvd
  have hne : x ≠ y := by
    rintro rfl
    have h_int : ((2 * (x : ℤ) - 1) ^ 2 : ℤ) = (x : ℤ) * (x : ℤ) * (k : ℤ) := by
      have hsub : x + x - 1 = 2 * x - 1 := by omega
      rw [hsub] at hk
      have hk_z : (((2 * x - 1 : ℕ) : ℤ) ^ 2) = ((x * x * k : ℕ) : ℤ) := by exact_mod_cast hk
      have hcast : ((2 * x - 1 : ℕ) : ℤ) = 2 * (x : ℤ) - 1 := by omega
      simpa [hcast, mul_assoc] using hk_z
    have hd1 : (x : ℤ) ∣ 1 := ⟨(x : ℤ) * (k : ℤ) + 4 - 4 * (x : ℤ), by linear_combination h_int⟩
    have hle1 : (x : ℤ) ≤ 1 := Int.le_of_dvd zero_lt_one hd1
    omega
  have hlt : y < x := lt_of_le_of_ne hyx hne.symm
  have hk_z : ((x : ℤ) + (y : ℤ) - 1) ^ 2 = (x : ℤ) * (y : ℤ) * (k : ℤ) := by
    have hcast : ((x + y - 1 : ℕ) : ℤ) = (x : ℤ) + (y : ℤ) - 1 := by omega
    have hk_nat : (((x + y - 1 : ℕ) : ℤ) ^ 2) = ((x * y * k : ℕ) : ℤ) := by exact_mod_cast hk
    simpa [hcast, mul_assoc] using hk_nat
  let X' : ℤ := (k : ℤ) * (y : ℤ) + 2 - 2 * (y : ℤ) - (x : ℤ)
  have hprod_z : (x : ℤ) * X' = ((y : ℤ) - 1) ^ 2 := by
    dsimp only [X']
    linear_combination -hk_z
  have hpos_rhs : (0 : ℤ) < ((y : ℤ) - 1) ^ 2 := by
    have : (0 : ℤ) < (y : ℤ) - 1 := by omega
    positivity
  have hX'_pos : 0 < X' := by
    by_contra hnp
    have hle0 : X' ≤ 0 := le_of_not_gt hnp
    have hx_pos : (0 : ℤ) < (x : ℤ) := by omega
    have hmul_le : (x : ℤ) * X' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx_pos.le hle0
    linarith
  let x' : ℕ := X'.toNat
  have hx'_cast : (x' : ℤ) = X' := Int.toNat_of_nonneg hX'_pos.le
  have hx'1 : 1 ≤ x' := by omega
  have hprod_nat : x * x' = (y - 1) * (y - 1) := by
    have hz : ((x * x' : ℕ) : ℤ) = (((y - 1) * (y - 1) : ℕ) : ℤ) := by
      have hy_cast : ((y - 1 : ℕ) : ℤ) = (y : ℤ) - 1 := by omega
      push_cast [hy_cast]
      rw [hx'_cast, hprod_z]
      ring
    exact_mod_cast hz
  have hx'_lt_y : x' < y := by
    have hym1_lt_x : y - 1 < x := by omega
    nlinarith
  have hvieta_z : ((x' : ℤ) + (y : ℤ) - 1) ^ 2 = (x' : ℤ) * (y : ℤ) * (k : ℤ) := by
    rw [hx'_cast]
    dsimp only [X']
    linear_combination hk_z
  have hdvd' : x' * y ∣ (x' + y - 1) ^ 2 := by
    refine ⟨k, ?_⟩
    have hz : (((x' + y - 1 : ℕ) : ℤ) ^ 2) = ((x' * y * k : ℕ) : ℤ) := by
      have hcast : ((x' + y - 1 : ℕ) : ℤ) = (x' : ℤ) + (y : ℤ) - 1 := by omega
      simpa [hcast, mul_assoc] using hvieta_z
    exact_mod_cast hz
  rcases ih x' y (by omega) hx'1 hy hdvd' with ⟨w, hw⟩ | hy_sq
  · left
    have hw_pos : 0 < w := by
      by_contra hw0
      have : w = 0 := by omega
      subst this
      omega
    have hww : x * (w * w) = (y - 1) * (y - 1) := by
      rw [sq] at hw
      rwa [← hw]
    have hd_wm : w ∣ y - 1 := dvd_of_sq_dvd_sq hw_pos ⟨x, by linarith⟩
    obtain ⟨u, hu⟩ := hd_wm
    refine ⟨u, ?_⟩
    have heq : x * (w * w) = (u ^ 2) * (w * w) := by
      rw [hww, hu]
      ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hw_pos hw_pos) heq
  · exact Or.inr hy_sq

theorem main_vieta : ∀ s : ℕ, ∀ x y : ℕ, x + y = s → 1 ≤ x → 1 ≤ y →
    x * y ∣ (x + y - 1) ^ 2 → (∃ u : ℕ, x = u ^ 2) ∨ (∃ v : ℕ, y = v ^ 2) := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro x y hsum hx hy hdvd
    rcases le_total y x with hyx | hxy
    · exact vieta_step hx hy hyx hdvd (fun x' y' hlt => ih (x' + y') (hsum ▸ hlt) x' y' rfl)
    · have hswap : y * x ∣ (y + x - 1) ^ 2 := by
        rwa [mul_comm, add_comm]
      exact (vieta_step hy hx hxy hswap
        (fun x' y' hlt => ih (x' + y') (by omega) x' y' rfl)).symm

end CrystalsVietaProof

theorem OMA.solution :
    OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H2_R1_H1_R1.H1 := by
  intro a b ⟨x₀, ha⟩ ⟨y₀, hb⟩ hdvd
  let x := x₀ + 1
  let y := y₀ + 1
  have ha1 : a + 1 = 2 * x := by omega
  have hb1 : b + 1 = 2 * y := by omega
  have hab : (a + b) ^ 2 = 4 * (x + y - 1) ^ 2 := by
    have h1 : a + b = 2 * (x + y - 1) := by omega
    rw [h1]
    ring
  have hprod : (a + 1) * (b + 1) = 4 * (x * y) := by
    rw [ha1, hb1]
    ring
  rw [hprod, hab] at hdvd
  have hdvd' : x * y ∣ (x + y - 1) ^ 2 :=
    (Nat.mul_dvd_mul_iff_left (by decide : 0 < 4)).mp hdvd
  rcases CrystalsVietaProof.main_vieta (x + y) x y rfl (by omega) (by omega) hdvd' with
    ⟨u, hu⟩ | ⟨v, hv⟩
  · exact Or.inl ⟨u, by rw [ha1, hu]⟩
  · exact Or.inr ⟨v, by rw [hb1, hv]⟩
