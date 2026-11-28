import OMAReductions.R_mo_181683_R1

/-!
The two positive consecutive factors of the quartic difference each have a
prime in common with r, since neither factor is large enough to absorb r².
-/

private theorem commonPrime {r a b : ℕ} (h : r ^ 2 ∣ a * b)
    (hb : 0 < b) (hlt : b < r ^ 2) : ∃ p, p.Prime ∧ p ∣ r ∧ p ∣ a := by
  by_contra! hn
  have hc : Nat.Coprime r a := Nat.coprime_of_dvd hn
  have hdiv : r ^ 2 ∣ b := (hc.pow_left 2).dvd_of_dvd_mul_left h
  exact (not_le_of_gt hlt) (Nat.le_of_dvd hb hdiv)

theorem OMA.solution : OMA.R_mo_181683_R1.H1 := by
  intro r s hs hsr hdiff hdiv
  let t := r - s
  have ht : 1 < t := by dsimp [t]; omega
  have htr : t < r := by dsimp [t]; omega
  have ht4 : 1 ≤ t ^ 4 := by
    have h := Nat.pow_lt_pow_left ht (show 4 ≠ 0 by decide)
    omega
  have hcast : (t : ℤ) = (r : ℤ) - s := Int.ofNat_sub hsr.le
  have hn : 4 * r ^ 2 * s ∣ t ^ 4 - 1 := by
    apply Int.natCast_dvd_natCast.mp
    push_cast [Nat.cast_sub ht4, hcast]
    exact hdiv
  have hm : 4 * r ^ 2 ∣ t ^ 4 - 1 := (dvd_mul_right _ _).trans hn
  have he : 2 ∣ t ^ 4 - 1 :=
    ((show 2 ∣ 4 by decide).trans (dvd_mul_right _ _)).trans hm
  have hodd : t % 2 = 1 := by
    have hmod : t ^ 4 % 2 = 1 := by
      obtain ⟨k, hk⟩ := he
      omega
    by_contra h
    have hz : t % 2 = 0 := by omega
    have hp := Nat.pow_mod t 4 2
    norm_num [hz, hmod] at hp
  have hot : Odd t := ⟨t / 2, by omega⟩
  let a := t ^ 2 / 2
  have ha : t ^ 2 = 2 * a + 1 := by
    obtain ⟨k, hk⟩ := hot.pow (n := 2)
    dsimp [a]
    omega
  have hf : t ^ 4 - 1 = 4 * (a * (a + 1)) := by
    have h : 4 * (a * (a + 1)) + 1 = t ^ 4 := calc
      _ = (2 * a + 1) ^ 2 := by ring
      _ = (t ^ 2) ^ 2 := by rw [← ha]
      _ = t ^ 4 := by ring
    omega
  have hr : r ^ 2 ∣ a * (a + 1) := by
    rw [hf] at hm
    exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 4) hm
  have hsq : t ^ 2 < r ^ 2 := Nat.pow_lt_pow_left htr (by decide)
  have hsqpos := Nat.pow_lt_pow_left ht (show 2 ≠ 0 by decide)
  have hpa : 0 < a := by omega
  have hal : a < r ^ 2 := by omega
  have hsl : a + 1 < r ^ 2 := by omega
  obtain ⟨p, hp, hpr, hpa'⟩ := commonPrime hr (by omega) hsl
  obtain ⟨q, hq, hqr, hqa⟩ := commonPrime (by rwa [mul_comm] : r ^ 2 ∣ (a + 1) * a) hpa hal
  refine ⟨p, q, hp, hq, ?_, hpr, hqr, hpa', hqa⟩
  rintro rfl
  have hd := Nat.dvd_sub hqa hpa'
  exact hp.not_dvd_one (by simpa using hd)

