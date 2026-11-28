import OMAReductions.R_Erdos242_erdos_242_variants_schinzel_generalization_R1_H1_R1

/-!
Reduce the eventual Erdős–Straus prime case to the 34 classes modulo 9240
of Ionascu and Wilson, with an additional divisor exclusion at each shift
at most 107. The two remaining cases have different residues modulo five.
The explicit identities at 1201 and 6001 are from Ionascu and Wilson.
https://www.csm.ro/reviste/Revue_Mathematique/pdfs/2011/1/Ionascu.pdf
-/

open Filter

namespace OMA.R_Erdos242_erdos_242_variants_schinzel_generalization_R1_H1_R1_H1_R1

def H1 : Prop :=
  ∀ᶠ p : ℕ in atTop, p.Prime →
    p % 9240 ∈ ([1, 361, 841, 961, 1681, 2041, 2521, 2641, 3361, 3481, 3721, 4321,
      5041, 5161, 6241, 7561, 7681, 7921, 8761] : List ℕ) →
    (∀ q : ℕ, 2 ≤ q → q ≤ p → q ∣ p + 1 → ¬ (4 ∣ q + 1)) →
    (∀ s u v k : ℕ, s ≤ 107 → s % 4 = 3 → 0 < u → u < v →
      u + v = s * k → v < p * k → ¬ (u * v ∣ p * ((p + s) / 4))) →
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / p : ℚ) = 1 / x + 1 / y + 1 / z

def H2 : Prop :=
  ∀ᶠ p : ℕ in atTop, p.Prime →
    p % 9240 ∈ ([169, 289, 529, 1369, 1849, 2209, 2689, 2809, 3529, 4489, 5329,
      5569, 6169, 6889, 8089] : List ℕ) →
    (∀ q : ℕ, 2 ≤ q → q ≤ p → q ∣ p + 1 → ¬ (4 ∣ q + 1)) →
    (∀ s u v k : ℕ, s ≤ 107 → s % 4 = 3 → 0 < u → u < v →
      u + v = s * k → v < p * k → ¬ (u * v ∣ p * ((p + s) / 4))) →
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / p : ℚ) = 1 / x + 1 / y + 1 / z

section Proof
private theorem two_multiples {p a b c d : ℕ} (ha : 0 < a) (hab : a < b)
    (hc : 0 < c) (hd : 0 < d) (hp : 0 < p) (hbp : b < c * p)
    (he : c * p + a + b = 4 * a * b * c * d) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4 / p : ℚ) = 1 / x + 1 / y + 1 / z := by
  have hb : 0 < b := ha.trans hab
  refine ⟨a * b * d, a * c * d * p, b * c * d * p, Nat.one_le_of_lt (by positivity), ?_, ?_, ?_⟩
  · simpa only [mul_assoc, mul_left_comm, mul_comm] using
      Nat.mul_lt_mul_of_pos_right hbp (Nat.mul_pos ha hd)
  · exact Nat.mul_lt_mul_of_pos_right
      (Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right hab hc) hd) hp
  have he' : (c : ℚ) * p + a + b = 4 * a * b * c * d := by exact_mod_cast he
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  push_cast
  field_simp [ha', hb', hc', hd', hp']
  linear_combination -he'

private theorem one_multiple {p a b c d : ℕ} (ha : 0 < a) (hab : a < b)
    (hc : 0 < c) (hd : 0 < d) (hp : 0 < p) (hcp : c < a * p)
    (he : (a + b) * p + c = 4 * a * b * c * d) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4 / p : ℚ) = 1 / x + 1 / y + 1 / z := by
  have hb : 0 < b := ha.trans hab
  refine ⟨a * c * d, b * c * d, a * b * d * p, Nat.one_le_of_lt (by positivity), ?_, ?_, ?_⟩
  · exact Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right hab hc) hd
  · simpa only [mul_assoc, mul_left_comm, mul_comm] using
      Nat.mul_lt_mul_of_pos_right hcp (Nat.mul_pos hb hd)
  have he' : ((a : ℚ) + b) * p + c = 4 * a * b * c * d := by exact_mod_cast he
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  push_cast
  field_simp [ha', hb', hc', hd', hp']
  linear_combination -he'

private theorem shifted_pair {p s m u v k d : ℕ} (hp : 0 < p) (hm : 0 < m)
    (hu : 0 < u) (huv : u < v) (hk : 0 < k) (hd : 0 < d) (hvp : v < p * k)
    (hshift : p + s = 4 * m) (hsum : u + v = s * k) (hprod : p * m = u * v * d) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4 / p : ℚ) = 1 / x + 1 / y + 1 / z := by
  have hlt : m < u * d * k := by
    apply Nat.lt_of_mul_lt_mul_left (a := p)
    calc
      p * m = v * (u * d) := by rw [hprod]; ac_rfl
      _ < (p * k) * (u * d) := Nat.mul_lt_mul_of_pos_right hvp (Nat.mul_pos hu hd)
      _ = p * (u * d * k) := by ac_rfl
  refine ⟨m, u * d * k, v * d * k, hm, hlt, ?_, ?_⟩
  · exact Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right huv hd) hk
  have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hu' : (u : ℚ) ≠ 0 := by exact_mod_cast hu.ne'
  have hv' : (v : ℚ) ≠ 0 := by exact_mod_cast (hu.trans huv).ne'
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hshift' : (p : ℚ) + s = 4 * m := by exact_mod_cast hshift
  have hsum' : (u : ℚ) + v = s * k := by exact_mod_cast hsum
  have hprod' : (p : ℚ) * m = u * v * d := by exact_mod_cast hprod
  push_cast
  calc
    (4 / p : ℚ) = 1 / m + s / (p * m) := by
      field_simp [hp', hm']
      linear_combination -hshift'
    _ = 1 / m + (u + v) / (p * m * k) := by
      rw [hsum']
      field_simp [hp', hm', hk']
    _ = 1 / m + 1 / (u * d * k) + 1 / (v * d * k) := by
      rw [hprod']
      field_simp [hm', hu', hv', hk', hd']
      ring

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem residue_table : ∀ i : Fin 385,
    let r := 24 * i.val + 1
    r % 5 ≠ 0 → r % 7 ≠ 0 → r % 11 ≠ 0 →
    r % 20 = 13 ∨ r % 20 = 17 ∨ r % 56 = 41 ∨ r % 84 = 61 ∨ r % 84 = 73 ∨
    r % 44 = 29 ∨ r % 44 = 41 ∨ r % 88 = 65 ∨ r % 1320 = 409 ∨ r % 1320 = 1249 ∨
    r = 1201 ∨ r = 6001 ∨
    r ∈ ([1, 361, 841, 961, 1681, 2041, 2521, 2641, 3361, 3481, 3721, 4321,
      5041, 5161, 6241, 7561, 7681, 7921, 8761] : List ℕ) ∨
    r ∈ ([169, 289, 529, 1369, 1849, 2209, 2689, 2809, 3529, 4489, 5329,
      5569, 6169, 6889, 8089] : List ℕ) := by decide

private theorem class_1201 {p : ℕ} (h : p % 9240 = 1201) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4 / p : ℚ) = 1 / x + 1 / y + 1 / z := by
  obtain ⟨k, rfl⟩ : ∃ k, p = 9240 * k + 1201 := ⟨p / 9240, by omega⟩
  refine ⟨2310 * k + 308, 5 * (9240 * k + 1201) * (15 * k + 2),
    770 * (9240 * k + 1201) * (15 * k + 2), by omega, by nlinarith, ?_, ?_⟩
  · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  push_cast
  field_simp
  ring

private theorem class_6001 {p : ℕ} (h : p % 9240 = 6001) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4 / p : ℚ) = 1 / x + 1 / y + 1 / z := by
  obtain ⟨k, rfl⟩ : ∃ k, p = 9240 * k + 6001 := ⟨p / 9240, by omega⟩
  refine ⟨2310 * k + 1540, 22 * (3 * k + 2) * (2034 * k + 1321),
    385 * (9240 * k + 6001) * (2034 * k + 1321), by omega, by nlinarith, ?_, ?_⟩
  · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  push_cast
  field_simp
  ring

private theorem prime_mod_ne_zero {p m : ℕ} (hp : p.Prime) (hm : 1 < m) (hlt : m < p) :
    p % m ≠ 0 := by
  intro h
  rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero h) with he | he <;> omega

theorem main : H1 → H2 → OMA.R_Erdos242_erdos_242_variants_schinzel_generalization_R1_H1_R1.H1 := by
  intro hFirst hSecond
  filter_upwards [hFirst, hSecond, eventually_ge_atTop (108 : ℕ)]
    with p hFirst hSecond hp108 hp hp4 hNoQ
  by_cases hShift : ∃ s u v k : ℕ, s ≤ 107 ∧ s % 4 = 3 ∧ 0 < u ∧ u < v ∧
      u + v = s * k ∧ v < p * k ∧ u * v ∣ p * ((p + s) / 4)
  · obtain ⟨s, u, v, k, _, hs4, hu, huv, hsum, hvp, d, hprod⟩ := hShift
    have hk : 0 < k := by
      by_contra! h
      simp [Nat.eq_zero_of_le_zero h] at hvp
    have hd : 0 < d := by
      by_contra! h
      simp [Nat.eq_zero_of_le_zero h,
        Nat.ne_of_gt (by omega : 0 < (p + s) / 4), Nat.ne_of_gt (by omega : 0 < p)] at hprod
    exact shifted_pair (by omega) (by omega) hu huv hk hd hvp (by omega) hsum hprod
  have hNoShift (s u v k : ℕ) (hs : s ≤ 107) (hs4 : s % 4 = 3) (hu : 0 < u)
      (huv : u < v) (hsum : u + v = s * k) (hvp : v < p * k) :
      ¬ (u * v ∣ p * ((p + s) / 4)) :=
    fun hd => hShift ⟨s, u, v, k, hs, hs4, hu, huv, hsum, hvp, hd⟩
  have hp24 : p % 24 = 1 := by
    have hp3 := prime_mod_ne_zero hp (m := 3) (by decide) (by omega)
    have hp12 : p % 12 ≠ 5 := by
      intro h
      exact hNoQ 3 (by decide) (by omega) (by omega) (by decide)
    have hp13 : p % 24 ≠ 13 := by
      intro h
      have hd : 2 ∣ (p + 3) / 4 := by omega
      apply hNoShift 3 1 2 1 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by omega)
      simpa only [one_mul] using dvd_mul_of_dvd_right hd p
    omega
  let r := p % 9240
  have hr : r < 9240 := Nat.mod_lt _ (by decide)
  have hr24 : r % 24 = 1 := by
    simpa only [r, Nat.mod_mod_of_dvd p (by decide : 24 ∣ 9240)] using hp24
  let i : Fin 385 := ⟨r / 24, by omega⟩
  have hi : 24 * i.val + 1 = r := by dsimp [i]; omega
  have h5 : r % 5 ≠ 0 := by
    simpa only [r, Nat.mod_mod_of_dvd p (by decide : 5 ∣ 9240)] using
      (prime_mod_ne_zero hp (m := 5) (by decide) (by omega))
  have h7 : r % 7 ≠ 0 := by
    simpa only [r, Nat.mod_mod_of_dvd p (by decide : 7 ∣ 9240)] using
      (prime_mod_ne_zero hp (m := 7) (by decide) (by omega))
  have h11 : r % 11 ≠ 0 := by
    simpa only [r, Nat.mod_mod_of_dvd p (by decide : 11 ∣ 9240)] using
      (prime_mod_ne_zero hp (m := 11) (by decide) (by omega))
  have h := residue_table i
  dsimp only at h
  rw [hi] at h
  rcases h h5 h7 h11 with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · change (p % 9240) % 20 = 13 at h
    rw [Nat.mod_mod_of_dvd p (by decide : 20 ∣ 9240)] at h
    apply one_multiple (a := 1) (b := 5) (c := 2) (d := (6 * p + 2) / 40) <;> norm_num <;> omega
  · change (p % 9240) % 20 = 17 at h
    rw [Nat.mod_mod_of_dvd p (by decide : 20 ∣ 9240)] at h
    apply two_multiples (a := 1) (b := 5) (c := 2) (d := (p + 3) / 20) <;> norm_num <;> omega
  · change (p % 9240) % 56 = 41 at h
    rw [Nat.mod_mod_of_dvd p (by decide : 56 ∣ 9240)] at h
    apply two_multiples (a := 1) (b := 14) (c := 1) (d := (p + 15) / 56) <;> norm_num <;> omega
  · change (p % 9240) % 84 = 61 at h
    rw [Nat.mod_mod_of_dvd p (by decide : 84 ∣ 9240)] at h
    apply one_multiple (a := 1) (b := 21) (c := 2) (d := (22 * p + 2) / 168) <;> norm_num <;> omega
  · change (p % 9240) % 84 = 73 at h
    rw [Nat.mod_mod_of_dvd p (by decide : 84 ∣ 9240)] at h
    apply two_multiples (a := 1) (b := 21) (c := 2) (d := (p + 11) / 84) <;> norm_num <;> omega
  · change (p % 9240) % 44 = 29 at h
    rw [Nat.mod_mod_of_dvd p (by decide : 44 ∣ 9240)] at h
    apply one_multiple (a := 1) (b := 11) (c := 4) (d := (3 * p + 1) / 44) <;> norm_num <;> omega
  · change (p % 9240) % 44 = 41 at h
    rw [Nat.mod_mod_of_dvd p (by decide : 44 ∣ 9240)] at h
    apply two_multiples (a := 1) (b := 11) (c := 4) (d := (p + 3) / 44) <;> norm_num <;> omega
  · change (p % 9240) % 88 = 65 at h
    rw [Nat.mod_mod_of_dvd p (by decide : 88 ∣ 9240)] at h
    apply two_multiples (a := 1) (b := 22) (c := 1) (d := (p + 23) / 88) <;> norm_num <;> omega
  · change (p % 9240) % 1320 = 409 at h
    rw [Nat.mod_mod_of_dvd p (by decide : 1320 ∣ 9240)] at h
    apply one_multiple (a := 5) (b := 66) (c := 1) (d := (71 * p + 1) / 1320) <;> norm_num <;> omega
  · change (p % 9240) % 1320 = 1249 at h
    rw [Nat.mod_mod_of_dvd p (by decide : 1320 ∣ 9240)] at h
    apply two_multiples (a := 5) (b := 66) (c := 1) (d := (p + 71) / 1320) <;> norm_num <;> omega
  · exact class_1201 h
  · exact class_6001 h
  · exact hFirst hp h hNoQ hNoShift
  · exact hSecond hp h hNoQ hNoShift

end Proof

end OMA.R_Erdos242_erdos_242_variants_schinzel_generalization_R1_H1_R1_H1_R1
