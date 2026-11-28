import OMAStatements.S_oeis_a078703
import Mathlib

/-!
# A078703: Arndt's Lambert-type generating function

A representation n = x² − k(k+1) with x ≥ 1 forces x > k; writing x = k + j gives
n = j² + k(2j − 1) with j ≥ 1. Conversely each j ≥ 1 with j² ≤ n and (2j − 1) ∣ n − j² gives
k = (n − j²)/(2j − 1) and x = j + k. This bijection (x, k) ↦ x − k shows that the number of
representations is the coefficient of xⁿ in Σ_j x^(j²)/(1 − x^(2j−1)).
-/

namespace PA078703
open Finset OMA.S_oeis_a078703

theorem key (n k j : ℕ) (hj : 1 ≤ j) :
    (k + j) ^ 2 = n + k * (k + 1) ↔ n = j ^ 2 + k * (2 * j - 1) := by
  have h1 : k * (2 * j - 1) + k = 2 * (k * j) := by
    have : 2 * j - 1 + 1 = 2 * j := by omega
    calc k * (2 * j - 1) + k = k * (2 * j - 1 + 1) := by ring
      _ = 2 * (k * j) := by rw [this]; ring
  constructor
  · intro h
    have h2 : (k + j) ^ 2 = k ^ 2 + 2 * (k * j) + j ^ 2 := by ring
    have h3 : k * (k + 1) = k ^ 2 + k := by ring
    omega
  · intro h
    rw [h]
    have h2 : (k + j) ^ 2 = k ^ 2 + 2 * (k * j) + j ^ 2 := by ring
    have h3 : k * (k + 1) = k ^ 2 + k := by ring
    omega

end PA078703

open Finset in
theorem OMA.solution : type_of% @OMA.S_oeis_a078703.main := by
  ext n
  unfold OMA.S_oeis_a078703.lambert
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  unfold OMA.S_oeis_a078703.a
  apply Finset.card_nbij' (fun p => p.1 - p.2)
    (fun j => (j + (n - j ^ 2) / (2 * j - 1), (n - j ^ 2) / (2 * j - 1)))
  · intro p hp
    simp only [Finset.mem_coe, OMA.S_oeis_a078703.squareWays, OMA.S_oeis_a078703.rows, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc, Finset.mem_range] at hp ⊢
    obtain ⟨⟨⟨hx1, hxn⟩, hk⟩, he⟩ := hp
    have hxk : p.2 < p.1 := by
      by_contra h
      rw [not_lt] at h
      have : p.1 ^ 2 ≤ p.2 ^ 2 := Nat.pow_le_pow_left h 2
      nlinarith
    obtain ⟨j, hj⟩ : ∃ j, p.1 = p.2 + j := ⟨p.1 - p.2, by omega⟩
    have hj1 : 1 ≤ j := by omega
    rw [hj] at he
    have hn := (PA078703.key n p.2 j hj1).mp he
    rw [show p.1 - p.2 = j by omega]
    have hjj : j ≤ j ^ 2 := by nlinarith
    refine ⟨⟨hj1, by omega⟩, by omega, ?_⟩
    rw [show n - j ^ 2 = p.2 * (2 * j - 1) by omega]
    exact Dvd.intro_left _ rfl
  · intro j hj
    simp only [Finset.mem_coe, OMA.S_oeis_a078703.squareWays, OMA.S_oeis_a078703.rows, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc, Finset.mem_range] at hj ⊢
    obtain ⟨⟨hj1, hjn⟩, hsq, hdvd⟩ := hj
    obtain ⟨k, hk⟩ := hdvd
    have hpos : 0 < 2 * j - 1 := by omega
    have hkdef : (n - j ^ 2) / (2 * j - 1) = k := by
      rw [hk, Nat.mul_div_cancel_left _ hpos]
    rw [hkdef]
    have hn : n = j ^ 2 + k * (2 * j - 1) := by rw [mul_comm]; omega
    have hjj : j ≤ j ^ 2 := by nlinarith
    have hk2 : k ≤ k * (2 * j - 1) := Nat.le_mul_of_pos_right k hpos
    refine ⟨⟨⟨by omega, by omega⟩, by nlinarith⟩, ?_⟩
    rw [show j + k = k + j by ring]
    exact (PA078703.key n k j hj1).mpr hn
  · intro p hp
    simp only [Finset.mem_coe, OMA.S_oeis_a078703.squareWays, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc, Finset.mem_range] at hp
    obtain ⟨⟨⟨hx1, hxn⟩, hk⟩, he⟩ := hp
    have hxk : p.2 < p.1 := by
      by_contra h
      rw [not_lt] at h
      have : p.1 ^ 2 ≤ p.2 ^ 2 := Nat.pow_le_pow_left h 2
      nlinarith
    obtain ⟨j, hj⟩ : ∃ j, p.1 = p.2 + j := ⟨p.1 - p.2, by omega⟩
    have hj1 : 1 ≤ j := by omega
    rw [hj] at he
    have hn := (PA078703.key n p.2 j hj1).mp he
    have hpos : 0 < 2 * j - 1 := by omega
    have hq : (n - j ^ 2) / (2 * j - 1) = p.2 := by
      rw [show n - j ^ 2 = p.2 * (2 * j - 1) by omega, Nat.mul_div_cancel _ hpos]
    simp only [show p.1 - p.2 = j by omega, hq]
    ext
    · simp; omega
    · simp
  · intro j hj
    simp only [Finset.mem_coe, OMA.S_oeis_a078703.rows, Finset.mem_filter, Finset.mem_Icc] at hj
    simp only
    omega
