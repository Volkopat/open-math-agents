import OMAReductions.R_OeisA239957_conjecture_R1

/-!
# Step H1 of the reduction OeisA239957.conjecture.R1

For a safe prime `P = 2 q + 1` (`q` an odd prime) the order of a unit divides `2 q`. A quadratic
non-residue `g` has `g ^ q = -1 ≠ 1` (Euler's criterion), so if also `g ^ 2 ≠ 1` its order is
`2 q = P - 1`. If `P ≡ 3 (mod 8)` then `2 = 1 ^ 2 + 1` is a non-residue (second supplement); if
`P ≡ 2, 3 (mod 5)` then `5 = 2 ^ 2 + 1` is a non-residue (quadratic reciprocity with `5`).
-/

namespace OMA.H239957

theorem order_of_nonsquare {q : ℕ} (hq : q.Prime) (hP : (2 * q + 1).Prime) (g : ZMod (2 * q + 1))
    (hns : ¬ IsSquare g) (h2 : g ^ 2 ≠ 1) : orderOf g = 2 * q + 1 - 1 := by
  have := Fact.mk hP
  have hg0 : g ≠ 0 := by rintro rfl; exact hns ⟨0, by simp⟩
  have h1 : g ^ (2 * q) = 1 := by
    have := ZMod.pow_card_sub_one_eq_one hg0
    simpa using this
  have hqne : g ^ q ≠ 1 := by
    intro h
    apply hns
    rw [ZMod.euler_criterion (2 * q + 1) hg0]
    have : (2 * q + 1) / 2 = q := by omega
    rw [this]; exact h
  have ho : orderOf g ∣ 2 * q := orderOf_dvd_of_pow_eq_one h1
  obtain ⟨a, b, ha, hb, hab⟩ := Nat.dvd_mul.mp ho
  rcases (Nat.dvd_prime Nat.prime_two).1 ha with rfl | rfl <;>
    rcases (Nat.dvd_prime hq).1 hb with rfl | rfl
  · exact absurd (orderOf_dvd_iff_pow_eq_one.1 (by rw [← hab]; simp)) hqne
  · exact absurd (orderOf_dvd_iff_pow_eq_one.1 (by rw [← hab]; simp)) hqne
  · exact absurd (by have := pow_orderOf_eq_one g; rwa [← hab, mul_one] at this) h2
  · rw [← hab]; omega

theorem ns5 : ¬ IsSquare ((2 : ℕ) : ZMod 5) ∧ ¬ IsSquare ((3 : ℕ) : ZMod 5) := by decide

end OMA.H239957

open OMA.H239957 in
theorem OMA.solution : OMA.R_OeisA239957_conjecture_R1.H1 := by
  intro q hq hq2 hP hcase
  have := Fact.mk hP
  have hP7 : 7 ≤ 2 * q + 1 := by omega
  have hPne2 : 2 * q + 1 ≠ 2 := by omega
  -- if `(c : ZMod P) = 0` with `0 < c < 7` we get a contradiction
  have small : ∀ c : ℕ, 0 < c → c < 7 → ((c : ℕ) : ZMod (2 * q + 1)) ≠ 0 := by
    intro c hc0 hc7 h
    rw [CharP.cast_eq_zero_iff (ZMod (2 * q + 1)) (2 * q + 1)] at h
    have := Nat.le_of_dvd hc0 h
    omega
  rcases hcase with h8 | h5
  · refine ⟨1, by push_cast; omega, ?_⟩
    have hg : ((1 : ℤ) ^ 2 + 1 : ZMod (2 * q + 1)) = 2 := by norm_num
    rw [hg]
    apply order_of_nonsquare hq hP
    · rw [ZMod.exists_sq_eq_two_iff hPne2]; omega
    · intro h
      have : ((3 : ℕ) : ZMod (2 * q + 1)) = 0 := by
        push_cast; linear_combination h
      exact small 3 (by norm_num) (by norm_num) this
  · refine ⟨2, by push_cast; omega, ?_⟩
    have hg : ((2 : ℤ) ^ 2 + 1 : ZMod (2 * q + 1)) = ((5 : ℕ) : ZMod (2 * q + 1)) := by
      push_cast; norm_num
    rw [hg]
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    apply order_of_nonsquare hq hP
    · rw [← ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (by norm_num : 5 % 4 = 1) hPne2,
        ← ZMod.natCast_mod]
      rcases h5 with h | h <;> rw [h]
      exacts [ns5.1, ns5.2]
    · intro h
      have h24 : ((24 : ℕ) : ZMod (2 * q + 1)) = 0 := by
        push_cast at h ⊢; linear_combination h
      rw [CharP.cast_eq_zero_iff (ZMod (2 * q + 1)) (2 * q + 1)] at h24
      have hle := Nat.le_of_dvd (by norm_num) h24
      have hpr := hP
      interval_cases h : 2 * q + 1 <;> revert h24 hpr <;> norm_num
