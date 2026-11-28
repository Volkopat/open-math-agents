import OMAStatements.S_oeis_a390583
import Mathlib

/-!
# A390583: two equal circles in a Descartes configuration

Descartes' relation with curvatures `1/x, 1/y, 1/R, 1/R` is `R (y - x)^2 = 4 x y (x + y)` (`key`).
Write `x = x' g`, `y = y' g` with `g = gcd x y`, `x'`, `y'` coprime, and `D = y' - x'`, so
`R D^2 = 4 g x' y' (x' + y')`. As `gcd g R = 1`, `g ∣ D^2`; put `D^2 = g q`, so
`R q = 4 x' y' (x' + y')`. Since `q` is coprime to `x'` and `y'` and `x' + y' = D + 2x'`, one gets
`q ∣ 4 (D + 2x')`, then `q ∣ 8D`, then `q ∣ 16`. Now `y - x = g D` and `q (y - x) = D^3`:
`q = 1, 4, 8` give `D^3`, `2 (D/2)^3`, `(D/2)^3`, while `q = 2` (then `2 ∣ g` and `2 ∣ R`) and
`q = 16` (then `2R` is a product of odd numbers) are impossible.
-/

namespace OMA.A390583Proof
open OMA.S_oeis_a390583

/-- Two equal circles: `R (y - x)^2 = 4 x y (x + y)`. -/
lemma key {x y R : ℕ} (hx : 0 < x) (hxy : x ≤ y) (hR : 0 < R) (hd : descartes x y R R) :
    R * (y - x) ^ 2 = 4 * x * y * (x + y) := by
  unfold descartes at hd
  have hx' : (x : ℚ) ≠ 0 := by positivity
  have hy0 : 0 < y := by omega
  have hy' : (y : ℚ) ≠ 0 := by positivity
  have hR' : (R : ℚ) ≠ 0 := by positivity
  have h2 : (1 / (x : ℚ) - 1 / y) ^ 2 = 4 * (1 / R) * (1 / x + 1 / y) := by
    linear_combination (-1 : ℚ) * hd
  have e1 : (y : ℚ) - x = x * y * (1 / x - 1 / y) := by field_simp
  have e2 : (x : ℚ) + y = x * y * (1 / x + 1 / y) := by field_simp; ring
  have hq : (R : ℚ) * ((y : ℚ) - x) ^ 2 = 4 * (x : ℚ) * y * (x + y) := by
    rw [e1]
    have h3 : (R : ℚ) * ((x : ℚ) * y * (1 / x - 1 / y)) ^ 2 =
        (R : ℚ) * ((x : ℚ) * y) ^ 2 * (1 / (x : ℚ) - 1 / y) ^ 2 := by ring
    rw [h3, h2]
    field_simp
    ring
  have : ((R * (y - x) ^ 2 : ℕ) : ℚ) = ((4 * x * y * (x + y) : ℕ) : ℚ) := by
    push_cast [Nat.cast_sub hxy]; exact hq
  exact_mod_cast this

theorem main' : ∀ x y R : ℕ, 0 < x → x ≤ y → y ≤ R →
    Nat.Coprime (Nat.gcd x y) R → descartes x y R R →
    ∃ k : ℕ, y - x = k ^ 3 ∨ y - x = 2 * k ^ 3 := by
  intro x y R hx hxy hyR hcop hd
  have hR : 0 < R := by omega
  have hE := key hx hxy hR hd
  obtain ⟨g, x', y', hg0, hco, hxe, hye⟩ := Nat.exists_coprime' (Nat.gcd_pos_of_pos_left y hx)
  have hgx : Nat.gcd x y = g := by rw [hxe, hye, Nat.gcd_mul_right, hco.gcd_eq_one, one_mul]
  rw [hgx] at hcop
  subst hxe hye
  have hx'y' : x' ≤ y' := Nat.le_of_mul_le_mul_right hxy hg0
  obtain ⟨D, hD⟩ : ∃ D, D = y' - x' := ⟨_, rfl⟩
  have hdiff : y' * g - x' * g = D * g := by rw [hD, Nat.sub_mul]
  have hsum : x' + y' = D + 2 * x' := by omega
  rw [hdiff] at hE ⊢
  have hE2 : R * D ^ 2 = 4 * x' * y' * (x' + y') * g := by
    have h : R * D ^ 2 * g ^ 2 = 4 * x' * y' * (x' + y') * g * g ^ 2 := by
      have := hE; ring_nf at this ⊢; linarith
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h
  -- `g` divides `D^2`
  have hdv : g ∣ R * D ^ 2 := ⟨4 * x' * y' * (x' + y'), by rw [hE2]; ring⟩
  obtain ⟨q, hq⟩ := hcop.dvd_of_dvd_mul_left hdv
  have hRq : R * q = 4 * x' * y' * (x' + y') := by
    have h : R * q * g = 4 * x' * y' * (x' + y') * g := by rw [← hE2, hq]; ring
    exact Nat.eq_of_mul_eq_mul_right hg0 h
  have hDx : Nat.Coprime D x' := by rw [hD]; exact (Nat.coprime_sub_self_left hx'y').mpr hco.symm
  have hDy : Nat.Coprime D y' := by rw [hD]; exact (Nat.coprime_self_sub_left hx'y').mpr hco
  have hqD : q ∣ D ^ 2 := ⟨g, by rw [hq]; ring⟩
  have hqx : Nat.Coprime q x' := Nat.Coprime.coprime_dvd_left hqD (hDx.pow_left 2)
  have hqy : Nat.Coprime q y' := Nat.Coprime.coprime_dvd_left hqD (hDy.pow_left 2)
  -- `q ∣ 16`
  have hq1 : q ∣ 4 * (D + 2 * x') := by
    have h : q ∣ x' * (y' * (4 * (x' + y'))) := ⟨R, by rw [mul_comm q R, hRq]; ring⟩
    rw [← hsum]
    exact hqy.dvd_of_dvd_mul_left (hqx.dvd_of_dvd_mul_left h)
  have hq2 : q ∣ x' * (8 * D) := by
    have h1 : q ∣ 4 * D ^ 2 + x' * (8 * D) := by
      have := Dvd.dvd.mul_left hq1 D
      have e : D * (4 * (D + 2 * x')) = 4 * D ^ 2 + x' * (8 * D) := by ring
      rwa [e] at this
    exact (Nat.dvd_add_right (Dvd.dvd.mul_left hqD 4)).mp h1
  have hq3 : q ∣ 8 * D := hqx.dvd_of_dvd_mul_left hq2
  have hq4 : q ∣ x' * 16 := by
    have h1 : q ∣ 8 * D + x' * 16 := by
      have := Dvd.dvd.mul_left hq1 2
      have e : 2 * (4 * (D + 2 * x')) = 8 * D + x' * 16 := by ring
      rwa [e] at this
    exact (Nat.dvd_add_right hq3).mp h1
  have hq16 : q ∣ 16 := hqx.dvd_of_dvd_mul_left hq4
  have hqle : q ≤ 16 := Nat.le_of_dvd (by norm_num) hq16
  have two_dvd_of_sq {n m : ℕ} (h : n ^ 2 = 2 * m) : 2 ∣ n :=
    Nat.Prime.dvd_of_dvd_pow Nat.prime_two ⟨m, h⟩
  interval_cases q <;> norm_num at hq16
  · -- q = 1
    exact ⟨D, Or.inl (by rw [show g = D ^ 2 by rw [hq]; ring]; ring)⟩
  · -- q = 2: impossible
    exfalso
    obtain ⟨E, rfl⟩ := two_dvd_of_sq (show D ^ 2 = 2 * g by rw [hq]; ring)
    have hg2 : 2 ∣ g := ⟨E ^ 2, by
      have h : g * 2 = 2 * E ^ 2 * 2 := by rw [← hq]; ring
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h⟩
    have ox : Odd x' := Nat.coprime_two_left.mp hqx
    have oy : Odd y' := Nat.coprime_two_left.mp hqy
    obtain ⟨s, hs⟩ : 2 ∣ x' + y' := by
      obtain ⟨a, ha⟩ := ox; obtain ⟨b, hb⟩ := oy; exact ⟨a + b + 1, by omega⟩
    have hR' : R = 4 * x' * y' * s := by
      have h : R * 2 = 4 * x' * y' * s * 2 := by rw [hRq, hs]; ring
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
    have hR2 : 2 ∣ R := ⟨2 * x' * y' * s, by rw [hR']; ring⟩
    exact Nat.not_coprime_of_dvd_of_dvd (by norm_num) hg2 hR2 hcop
  · -- q = 4
    obtain ⟨E, rfl⟩ := two_dvd_of_sq (show D ^ 2 = 2 * (2 * g) by rw [hq]; ring)
    have hg : g = E ^ 2 := by
      have h : g * 4 = E ^ 2 * 4 := by rw [← hq]; ring
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
    exact ⟨E, Or.inr (by rw [hg]; ring)⟩
  · -- q = 8
    obtain ⟨E, rfl⟩ := two_dvd_of_sq (show D ^ 2 = 2 * (4 * g) by rw [hq]; ring)
    have hE' : E ^ 2 = 2 * g := by
      have h : E ^ 2 * 4 = 2 * g * 4 := by rw [show E ^ 2 * 4 = (2 * E) ^ 2 by ring, hq]; ring
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
    obtain ⟨F, rfl⟩ := two_dvd_of_sq hE'
    have hg : g = 2 * F ^ 2 := by
      have h : g * 2 = 2 * F ^ 2 * 2 := by rw [show g * 2 = 2 * g by ring, ← hE']; ring
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
    exact ⟨2 * F, Or.inl (by rw [hg]; ring)⟩
  · -- q = 16: impossible
    exfalso
    obtain ⟨E, rfl⟩ := two_dvd_of_sq (show D ^ 2 = 2 * (8 * g) by rw [hq]; ring)
    have hE' : E ^ 2 = 2 * (2 * g) := by
      have h : E ^ 2 * 4 = 2 * (2 * g) * 4 := by rw [show E ^ 2 * 4 = (2 * E) ^ 2 by ring, hq]; ring
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
    obtain ⟨F, rfl⟩ := two_dvd_of_sq hE'
    have ox : Odd x' := Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_left (by norm_num) hqx)
    have oy : Odd y' := Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_left (by norm_num) hqy)
    have h2R : 2 * R = x' * y' * (2 * F + x') := by
      have h : 2 * R * 8 = x' * y' * (2 * F + x') * 8 := by
        calc 2 * R * 8 = R * 16 := by ring
          _ = 4 * x' * y' * (x' + y') := hRq
          _ = x' * y' * (2 * F + x') * 8 := by rw [hsum]; ring
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
    have hodd : Odd (x' * y' * (2 * F + x')) :=
      (ox.mul oy).mul (by obtain ⟨a, ha⟩ := ox; exact ⟨F + a, by omega⟩)
    rw [← h2R] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) ⟨R, by ring⟩

end OMA.A390583Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a390583.main := OMA.A390583Proof.main'
