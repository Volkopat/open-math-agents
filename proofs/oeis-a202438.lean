import OMAStatements.S_oeis_a202438
import Mathlib

namespace OMA.P_oeis_a202438

-- 1. Frobenius in PowerSeries (ZMod 7): coeff m (F ^ 7) = 0 whenever ¬(7 ∣ m)
private lemma add_pow_seven_zmod7 (f g : PowerSeries (ZMod 7)) :
    (f + g) ^ 7 = f ^ 7 + g ^ 7 := by
  have h1 : (f + g) ^ 7 = f ^ 7 + g ^ 7 +
      7 * (f ^ 6 * g + 3 * f ^ 5 * g ^ 2 + 5 * f ^ 4 * g ^ 3 +
           5 * f ^ 3 * g ^ 4 + 3 * f ^ 2 * g ^ 5 + f * g ^ 6) := by ring
  have h7z : (7 : ZMod 7) = 0 := by decide
  have h7 : (7 : PowerSeries (ZMod 7)) = 0 := by
    rw [show (7 : PowerSeries (ZMod 7)) = PowerSeries.C (7 : ZMod 7) from (map_ofNat _ 7).symm,
      h7z, map_zero]
  rw [h1, h7, zero_mul, add_zero]

private lemma coeff_pow_seven_eq_zero (F : PowerSeries (ZMod 7)) (m : ℕ) (hm : ¬(7 ∣ m)) :
    PowerSeries.coeff m (F ^ 7) = 0 := by
  have hpoly : ∀ P : Polynomial (ZMod 7), PowerSeries.coeff m ((P : PowerSeries (ZMod 7)) ^ 7) = 0 := by
    intro P
    induction P using Polynomial.induction_on' with
    | add p q ihp ihq =>
      rw [Polynomial.coe_add, add_pow_seven_zmod7, map_add, ihp, ihq, add_zero]
    | monomial k c =>
      rw [Polynomial.coe_monomial, PowerSeries.monomial_pow, PowerSeries.coeff_monomial]
      have hne : m ≠ 7 * k := by intro h; apply hm; exact ⟨k, h⟩
      simp [hne]
  let P : Polynomial (ZMod 7) := ∑ k ∈ Finset.range (m + 1), Polynomial.monomial k (PowerSeries.coeff k F)
  have hagree : ∀ r ≤ m, PowerSeries.coeff r F = PowerSeries.coeff r (P : PowerSeries (ZMod 7)) := by
    intro r hr
    rw [Polynomial.coeff_coe, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range,
      show r < m + 1 by omega, ↓reduceIte]
  have hpow_agree : ∀ t : ℕ, ∀ r ≤ m,
      PowerSeries.coeff r (F ^ t) = PowerSeries.coeff r ((P : PowerSeries (ZMod 7)) ^ t) := by
    intro t
    induction t with
    | zero => intro r _; simp
    | succ t iht =>
      intro r hr
      rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (f := fun i j => PowerSeries.coeff i (F ^ t) * PowerSeries.coeff j F),
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (f := fun i j => PowerSeries.coeff i ((P : PowerSeries (ZMod 7)) ^ t) *
            PowerSeries.coeff j (P : PowerSeries (ZMod 7)))]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkr : k ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [iht k (by omega), hagree (r - k) (by omega)]
  rw [hpow_agree 7 m le_rfl, hpoly P]

-- 2. Triangular numbers mod 7: if n*(n+1)/2 % 7 ∉ {0, 1, 3}, then 7 ∣ (2*n + 1)!
private lemma tri_mod7_dvd (n : ℕ) (h0 : (n * (n + 1) / 2) % 7 ≠ 0)
    (h1 : (n * (n + 1) / 2) % 7 ≠ 1) (h3 : (n * (n + 1) / 2) % 7 ≠ 3) :
    (7 : ℤ) ∣ (2 * (n : ℤ) + 1) := by
  set t := n * (n + 1) / 2
  have hev : 2 * t = n * (n + 1) := by
    have h2 : 2 ∣ n * (n + 1) := by
      rcases Nat.even_or_odd n with ⟨r, rfl⟩ | ⟨r, rfl⟩
      · exact ⟨r * (r + r + 1), by ring⟩
      · exact ⟨(2 * r + 1) * (r + 1), by ring⟩
    exact Nat.mul_div_cancel' h2
  obtain ⟨q, hq⟩ : ∃ q, n = 7 * q ∨ n = 7 * q + 1 ∨ n = 7 * q + 2 ∨ n = 7 * q + 3 ∨
      n = 7 * q + 4 ∨ n = 7 * q + 5 ∨ n = 7 * q + 6 := ⟨n / 7, by omega⟩
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso; apply h0
    have : 2 * t = 7 * (q * (7 * q + 1)) := by rw [hev]; ring
    omega
  · exfalso; apply h1
    have : 2 * t = 7 * (7 * q ^ 2 + 3 * q) + 2 := by rw [hev]; ring
    omega
  · exfalso; apply h3
    have : 2 * t = 7 * (7 * q ^ 2 + 5 * q) + 6 := by rw [hev]; ring
    omega
  · refine ⟨2 * (q : ℤ) + 1, by push_cast; ring⟩
  · exfalso; apply h3
    have : 2 * t = 7 * (7 * q ^ 2 + 9 * q + 2) + 6 := by rw [hev]; ring
    omega
  · exfalso; apply h1
    have : 2 * t = 7 * (7 * q ^ 2 + 11 * q + 4) + 2 := by rw [hev]; ring
    omega
  · exfalso; apply h0
    have : 2 * t = 7 * ((7 * q + 6) * (q + 1)) := by rw [hev]; ring
    omega

private theorem main_proved :
    ∀ a : ℕ → ℤ,
      (let A : PowerSeries ℤ := PowerSeries.mk a
       let B : PowerSeries ℤ :=
         PowerSeries.mk (fun m =>
           ∑ n ∈ Finset.range (m + 1),
             if n * (n + 1) / 2 = m then
               (9 : ℤ) ^ n * (2 * (n : ℤ) + 1) * (-1 : ℤ) ^ m
             else 0)
       A ^ 3 * B = 1) →
      ∀ n : ℕ, (7 : ℤ) ∣ a (7 * n + 5) := by
  intro a hAB n
  let b : ℕ → ℤ := fun m =>
    ∑ k ∈ Finset.range (m + 1),
      if k * (k + 1) / 2 = m then (9 : ℤ) ^ k * (2 * (k : ℤ) + 1) * (-1 : ℤ) ^ m else 0
  let A7 : PowerSeries (ZMod 7) := PowerSeries.map (Int.castRingHom (ZMod 7)) (PowerSeries.mk a)
  let B7 : PowerSeries (ZMod 7) := PowerSeries.map (Int.castRingHom (ZMod 7)) (PowerSeries.mk b)
  have hA7B7 : A7 ^ 3 * B7 = 1 := by
    have hmap := congr_arg (PowerSeries.map (Int.castRingHom (ZMod 7))) hAB
    simpa [A7, B7, b] using hmap
  -- Key identity: A7 = B7 ^ 2 * A7 ^ 7
  have hkey : A7 = B7 ^ 2 * A7 ^ 7 := by
    calc A7 = A7 * (A7 ^ 3 * B7) ^ 2 := by rw [hA7B7, one_pow, mul_one]
      _ = B7 ^ 2 * A7 ^ 7 := by ring
  -- B7 has zero coeff when m % 7 ∉ {0, 1, 3}
  have hB7_zero : ∀ m : ℕ, m % 7 ≠ 0 → m % 7 ≠ 1 → m % 7 ≠ 3 → PowerSeries.coeff m B7 = 0 := by
    intro m hm0 hm1 hm3
    simp only [B7, PowerSeries.coeff_map, PowerSeries.coeff_mk, eq_intCast]
    have hdvd : (7 : ℤ) ∣ b m := by
      refine Finset.dvd_sum fun k _ => ?_
      split_ifs with hk
      · subst hk
        have hd := tri_mod7_dvd k hm0 hm1 hm3
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _
      · exact dvd_zero _
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr hdvd
  -- B7 ^ 2 has zero coeff when m % 7 = 5!
  have hB7sq_zero : ∀ m : ℕ, m % 7 = 5 → PowerSeries.coeff m (B7 ^ 2) = 0 := by
    intro m hm5
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (f := fun i j => PowerSeries.coeff i B7 * PowerSeries.coeff j B7)]
    refine Finset.sum_eq_zero fun i hi => ?_
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases hi_ok : i % 7 = 0 ∨ i % 7 = 1 ∨ i % 7 = 3
    · have hj_bad : (m - i) % 7 ≠ 0 ∧ (m - i) % 7 ≠ 1 ∧ (m - i) % 7 ≠ 3 := by omega
      rw [hB7_zero (m - i) hj_bad.1 hj_bad.2.1 hj_bad.2.2, mul_zero]
    · push Not at hi_ok
      rw [hB7_zero i hi_ok.1 hi_ok.2.1 hi_ok.2.2, zero_mul]
  -- Evaluate coeff (7 * n + 5) A7 = coeff (7 * n + 5) (B7^2 * A7^7) = 0!
  have hzero : PowerSeries.coeff (7 * n + 5) A7 = 0 := by
    rw [hkey, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (f := fun i j => PowerSeries.coeff i (B7 ^ 2) * PowerSeries.coeff j (A7 ^ 7))]
    refine Finset.sum_eq_zero fun i hi => ?_
    have him : i ≤ 7 * n + 5 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases hj : 7 ∣ (7 * n + 5 - i)
    · have hi5 : i % 7 = 5 := by obtain ⟨q, hq⟩ := hj; omega
      rw [hB7sq_zero i hi5, zero_mul]
    · rw [coeff_pow_seven_eq_zero A7 (7 * n + 5 - i) hj, mul_zero]
  simp only [A7, PowerSeries.coeff_map, PowerSeries.coeff_mk, eq_intCast] at hzero
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hzero

end OMA.P_oeis_a202438

theorem OMA.solution : type_of% @OMA.S_oeis_a202438.main :=
  OMA.P_oeis_a202438.main_proved
