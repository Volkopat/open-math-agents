import OMAReductions.R_oeis_a303233_R1
import Mathlib.NumberTheory.SumTwoSquares
-- Credit: @LordMike

theorem oeis303_tri_add (a b m : ℕ) (h : a * (a + 1) / 2 + b * (b + 1) / 2 = m) :
    2 * m = a * (a + 1) + b * (b + 1) := by
  have ha : 2 ∣ a * (a + 1) := even_iff_two_dvd.mp (Nat.even_mul_succ_self a)
  have hb : 2 ∣ b * (b + 1) := even_iff_two_dvd.mp (Nat.even_mul_succ_self b)
  omega

theorem oeis303_of_tri (a b m : ℕ) (h : 2 * m = a * (a + 1) + b * (b + 1)) :
    a * (a + 1) / 2 + b * (b + 1) / 2 = m := by
  have ha : 2 ∣ a * (a + 1) := even_iff_two_dvd.mp (Nat.even_mul_succ_self a)
  have hb : 2 ∣ b * (b + 1) := even_iff_two_dvd.mp (Nat.even_mul_succ_self b)
  omega

theorem oeis303_aux (k l m : ℕ) (h : 4 * m + 1 = (2 * k + 1) ^ 2 + (2 * l) ^ 2) :
    ∃ a b : ℕ, a * (a + 1) / 2 + b * (b + 1) / 2 = m := by
  by_cases hlk : l ≤ k
  · obtain ⟨j, rfl⟩ : ∃ j, k = l + j := Nat.exists_eq_add_of_le hlk
    refine ⟨2 * l + j, j, oeis303_of_tri _ _ _ ?_⟩
    nlinarith [h]
  · obtain ⟨j, rfl⟩ : ∃ j, l = k + j + 1 := ⟨l - k - 1, by omega⟩
    refine ⟨2 * k + j + 1, j, oeis303_of_tri _ _ _ ?_⟩
    nlinarith [h]

theorem oeis303_key (m : ℕ) :
    (∃ a b : ℕ, a * (a + 1) / 2 + b * (b + 1) / 2 = m) ↔
      ∃ x y : ℕ, 4 * m + 1 = x ^ 2 + y ^ 2 := by
  constructor
  · rintro ⟨a, b, h⟩
    have h2 := oeis303_tri_add a b m h
    rcases le_total a b with hab | hab
    · obtain ⟨k, rfl⟩ : ∃ k, b = a + k := Nat.exists_eq_add_of_le hab
      exact ⟨a + (a + k) + 1, k, by nlinarith [h2]⟩
    · obtain ⟨k, rfl⟩ : ∃ k, a = b + k := Nat.exists_eq_add_of_le hab
      exact ⟨b + k + b + 1, k, by nlinarith [h2]⟩
  · rintro ⟨x, y, hxy⟩
    rcases Nat.even_or_odd' x with ⟨k, rfl | rfl⟩ <;>
      rcases Nat.even_or_odd' y with ⟨l, rfl | rfl⟩
    · exfalso
      ring_nf at hxy
      omega
    · exact oeis303_aux l k m (by linarith [hxy])
    · exact oeis303_aux k l m (by linarith [hxy])
    · exfalso
      ring_nf at hxy
      omega

theorem OMA.solution : OMA.R_oeis_a303233_R1.H1 := by
  unfold OMA.R_oeis_a303233_R1.H1
  intro n c d hle
  dsimp only
  have hT : (∃ a b : ℕ, a * (a + 1) / 2 + b * (b + 1) / 2 + 2 ^ c + 2 ^ d = n) ↔
      ∃ a b : ℕ, a * (a + 1) / 2 + b * (b + 1) / 2 = n - (2 ^ c + 2 ^ d) := by
    constructor
    · rintro ⟨a, b, h⟩
      exact ⟨a, b, by omega⟩
    · rintro ⟨a, b, h⟩
      exact ⟨a, b, by omega⟩
  exact (hT.trans (oeis303_key _)).trans Nat.eq_sq_add_sq_iff
