import OMAStatements.S_oeis_a276705
import Mathlib

open OMA.S_oeis_a276705
open PowerSeries

namespace P276705

theorem natAbs_sub (n : ℕ) (h : 3 ≤ n) : ((n : ℤ) - 3).natAbs = n - 3 := by
  have : ((n : ℤ) - 3) = ((n - 3 : ℕ) : ℤ) := by push_cast [Nat.cast_sub h]; ring
  rw [this, Int.natAbs_natCast]

/-- Coprime case: `n` even and not divisible by 3. -/
theorem L_good (n : ℕ) (h : 4 ≤ n) (hm : n % 6 = 2 ∨ n % 6 = 4) : L n = (n + 3) * (n - 3) := by
  rw [L, natAbs_sub n (by omega)]
  apply Nat.Coprime.lcm_eq_mul
  set d := Nat.gcd (n + 3) (n - 3) with hd
  have h1 : d ∣ n + 3 := Nat.gcd_dvd_left _ _
  have h2 : d ∣ n - 3 := Nat.gcd_dvd_right _ _
  have h6 : d ∣ 6 := by
    have := Nat.dvd_sub h1 h2
    rwa [show n + 3 - (n - 3) = 6 by omega] at this
  have hle : d ≤ 6 := Nat.le_of_dvd (by norm_num) h6
  have hpos : 0 < d := Nat.pos_of_dvd_of_pos h6 (by norm_num)
  have hodd : ¬ 2 ∣ d := fun h2d => by have := Nat.dvd_trans h2d h1; omega
  have h3 : ¬ 3 ∣ d := fun h3d => by have := Nat.dvd_trans h3d h1; omega
  show d = 1
  interval_cases d <;> omega

/-- Otherwise the gcd is at least 2. -/
theorem L_bad (n : ℕ) (h : 3 ≤ n) (hm : ¬ (n % 6 = 2 ∨ n % 6 = 4)) :
    2 * L n ≤ (n + 3) * (n - 3) := by
  rw [L, natAbs_sub n h]
  have hg := Nat.gcd_mul_lcm (n + 3) (n - 3)
  have hpos : 0 < Nat.gcd (n + 3) (n - 3) := Nat.gcd_pos_of_pos_left _ (by omega)
  have h2 : 2 ≤ Nat.gcd (n + 3) (n - 3) := by
    rcases Nat.mod_two_eq_zero_or_one n with he | ho
    · have h3 : 3 ∣ Nat.gcd (n + 3) (n - 3) := Nat.dvd_gcd (by omega) (by omega)
      have := Nat.le_of_dvd hpos h3; omega
    · have h2 : 2 ∣ Nat.gcd (n + 3) (n - 3) := Nat.dvd_gcd (by omega) (by omega)
      exact Nat.le_of_dvd hpos h2
  calc 2 * Nat.lcm (n + 3) (n - 3) ≤ Nat.gcd (n + 3) (n - 3) * Nat.lcm (n + 3) (n - 3) :=
        Nat.mul_le_mul_right _ h2
    _ = (n + 3) * (n - 3) := hg

theorem L_le (n : ℕ) (h : 3 ≤ n) : L n ≤ (n + 3) * (n - 3) := by
  by_cases hm : n % 6 = 2 ∨ n % 6 = 4
  · rw [L_good n (by omega) hm]
  · have := L_bad n h hm; omega

theorem L1 : L 1 = 4 := by decide
theorem L2 : L 2 = 5 := by decide

theorem L_lt (j n : ℕ) (hj : 1 ≤ j) (hjn : j < n) (hn : 9 ≤ n) (hm : n % 6 = 2 ∨ n % 6 = 4) :
    L j < L n := by
  rw [L_good n (by omega) hm]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
  rw [show k + 9 - 3 = k + 6 by omega]
  rcases Nat.lt_or_ge j 3 with h | h
  · interval_cases j
    · rw [L1]; nlinarith
    · rw [L2]; nlinarith
  · have := L_le j h
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 3 := ⟨j - 3, by omega⟩
    rw [show i + 3 - 3 = i by omega] at this
    nlinarith

theorem not_rec (n j : ℕ) (hn : 9 ≤ n) (hm : ¬ (n % 6 = 2 ∨ n % 6 = 4)) (hj : n - 3 ≤ j)
    (hjn : j < n) (hjm : j % 6 = 2 ∨ j % 6 = 4)
    (hq : (n + 3) * (n - 3) ≤ 2 * ((j + 3) * (j - 3))) : ¬ IsRecord n := by
  rintro ⟨-, -, hr⟩
  have h1 := hr j hjn (by omega)
  rw [L_good j (by omega) hjm] at h1
  have h2 := L_bad n (by omega) hm
  omega

theorem rec_iff (n : ℕ) :
    IsRecord n ↔ (n = 1 ∨ n = 2 ∨ (4 ≤ n ∧ n ≤ 8) ∨ (9 ≤ n ∧ (n % 6 = 2 ∨ n % 6 = 4))) := by
  rcases Nat.lt_or_ge n 9 with h | h
  · interval_cases n <;> decide
  · by_cases hm : n % 6 = 2 ∨ n % 6 = 4
    · constructor
      · intro _; right; right; right; exact ⟨h, hm⟩
      · intro _
        refine ⟨by omega, ?_, fun j hj h1 => L_lt j n h1 hj h hm⟩
        rw [L_good n (by omega) hm]
        exact Nat.mul_pos (by omega) (by omega)
    · constructor
      · intro hr
        exfalso
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
        have e : (k + 9) % 6 = 0 ∨ (k + 9) % 6 = 1 ∨ (k + 9) % 6 = 3 ∨ (k + 9) % 6 = 5 := by omega
        rcases e with e | e | e | e
        · refine not_rec (k + 9) (k + 7) (by omega) hm (by omega) (by omega) (by omega) ?_ hr
          rw [show k + 9 - 3 = k + 6 by omega, show k + 7 - 3 = k + 4 by omega]; nlinarith
        · have hk : 4 ≤ k := by omega
          refine not_rec (k + 9) (k + 6) (by omega) hm (by omega) (by omega) (by omega) ?_ hr
          rw [show k + 9 - 3 = k + 6 by omega, show k + 6 - 3 = k + 3 by omega]; nlinarith
        · refine not_rec (k + 9) (k + 8) (by omega) hm (by omega) (by omega) (by omega) ?_ hr
          rw [show k + 9 - 3 = k + 6 by omega, show k + 8 - 3 = k + 5 by omega]; nlinarith
        · refine not_rec (k + 9) (k + 8) (by omega) hm (by omega) (by omega) (by omega) ?_ hr
          rw [show k + 9 - 3 = k + 6 by omega, show k + 8 - 3 = k + 5 by omega]; nlinarith
      · intro hc; omega

theorem rec_t (n : ℕ) (h : 9 ≤ n) (hm : n % 6 = 2 ∨ n % 6 = 4) : IsRecord n :=
  (rec_iff n).mpr (Or.inr (Or.inr (Or.inr ⟨h, hm⟩)))

theorem rec_f (n : ℕ) (h : 9 ≤ n) (hm : ¬ (n % 6 = 2 ∨ n % 6 = 4)) : ¬ IsRecord n := by
  rw [rec_iff]; omega

theorem count_eq (m : ℕ) : Nat.count IsRecord (6 * m + 10) = 2 * m + 7 ∧
    Nat.count IsRecord (6 * m + 14) = 2 * m + 8 := by
  induction m with
  | zero => exact ⟨by decide, by decide⟩
  | succ m ih =>
    obtain ⟨-, ih2⟩ := ih
    have c1 : Nat.count IsRecord (6 * (m + 1) + 10) = 2 * (m + 1) + 7 := by
      rw [show 6 * (m + 1) + 10 = (6 * m + 14) + 1 + 1 by ring, Nat.count_succ, Nat.count_succ, ih2,
        if_pos (rec_t _ (by omega) (by omega)), if_neg (rec_f _ (by omega) (by omega))]
      omega
    refine ⟨c1, ?_⟩
    rw [show 6 * (m + 1) + 14 = (6 * (m + 1) + 10) + 1 + 1 + 1 + 1 by ring, Nat.count_succ,
      Nat.count_succ, Nat.count_succ, Nat.count_succ, c1,
      if_pos (rec_t _ (by omega) (by omega)), if_neg (rec_f _ (by omega) (by omega)),
      if_neg (rec_f _ (by omega) (by omega)), if_neg (rec_f _ (by omega) (by omega))]

theorem nth_even (m : ℕ) : Nat.nth IsRecord (2 * m + 7) = 6 * m + 10 := by
  have := Nat.nth_count (rec_t (6 * m + 10) (by omega) (by omega))
  rwa [(count_eq m).1] at this

theorem nth_odd (m : ℕ) : Nat.nth IsRecord (2 * m + 8) = 6 * m + 14 := by
  have := Nat.nth_count (rec_t (6 * m + 14) (by omega) (by omega))
  rwa [(count_eq m).2] at this

theorem a7 : a 7 = 55 := by
  have := Nat.nth_count (p := IsRecord) (n := 8) (by decide)
  have c : Nat.count IsRecord 8 = 6 := by decide
  rw [c] at this
  rw [a, show 7 - 1 = 6 from rfl, this]; decide

theorem closed (n : ℕ) (hn : 6 < n) :
    2 * (a n : ℤ) = (347 + 27 * (-1) ^ n) - 6 * (27 + (-1) ^ n) * n + 18 * (n : ℤ) ^ 2 := by
  rcases Nat.lt_or_ge n 8 with h | h
  · obtain rfl : n = 7 := by omega
    rw [a7]; norm_num
  · obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m + 8 ∨ n = 2 * m + 9 := ⟨(n - 8) / 2, by omega⟩
    · rw [a, show 2 * m + 8 - 1 = 2 * m + 7 by omega, nth_even, L_good _ (by omega) (by omega),
        show 6 * m + 10 - 3 = 6 * m + 7 by omega]
      have : (-1 : ℤ) ^ (2 * m + 8) = 1 := by rw [pow_add, pow_mul]; norm_num
      rw [this]; push_cast; ring
    · rw [a, show 2 * m + 9 - 1 = 2 * m + 8 by omega, nth_odd, L_good _ (by omega) (by omega),
        show 6 * m + 14 - 3 = 6 * m + 11 by omega]
      have : (-1 : ℤ) ^ (2 * m + 9) = -1 := by rw [pow_add, pow_mul]; norm_num
      rw [this]; push_cast; ring

theorem recur (n : ℕ) (hn : 11 < n) :
    (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5) := by
  have h0 := closed n (by omega)
  have h1 := closed (n - 1) (by omega)
  have h2 := closed (n - 2) (by omega)
  have h3 := closed (n - 3) (by omega)
  have h4 := closed (n - 4) (by omega)
  have h5 := closed (n - 5) (by omega)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
  simp only [show m + 12 - 1 = m + 11 by omega, show m + 12 - 2 = m + 10 by omega,
    show m + 12 - 3 = m + 9 by omega, show m + 12 - 4 = m + 8 by omega,
    show m + 12 - 5 = m + 7 by omega] at h1 h2 h3 h4 h5 ⊢
  have p : ∀ k : ℕ, (-1 : ℤ) ^ (m + k) = (-1) ^ m * (-1) ^ k := fun k => pow_add _ _ _
  rw [p] at h0 h1 h2 h3 h4 h5
  norm_num at h0 h1 h2 h3 h4 h5
  push_cast at h0 h1 h2 h3 h4 h5
  have : (2 : ℤ) * ((a (m + 12) : ℤ) - (a (m + 11) + 2 * a (m + 10) - 2 * a (m + 9) - a (m + 8) +
      a (m + 7))) = 0 := by
    linear_combination h0 - h1 - 2 * h2 + 2 * h3 + h4 - h5
  have := (mul_eq_zero.mp this).resolve_left (by norm_num)
  linarith

open PowerSeries in
theorem gf : mk (fun n => if n = 0 then 0 else (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 2) =
      (X * (4 + X - 6 * X ^ 2 - X ^ 3 + X ^ 4 + 10 * X ^ 5 + 35 * X ^ 6 + 15 * X ^ 7 + 27 * X ^ 8 -
        X ^ 9 - 13 * X ^ 10) : PowerSeries ℤ) := by
  have n0 : Nat.nth IsRecord 0 = 1 := by
    have := Nat.nth_count (p := IsRecord) (n := 1) (by decide)
    rwa [show Nat.count IsRecord 1 = 0 by decide] at this
  have n1 : Nat.nth IsRecord 1 = 2 := by
    have := Nat.nth_count (p := IsRecord) (n := 2) (by decide)
    rwa [show Nat.count IsRecord 2 = 1 by decide] at this
  have n2 : Nat.nth IsRecord 2 = 4 := by
    have := Nat.nth_count (p := IsRecord) (n := 4) (by decide)
    rwa [show Nat.count IsRecord 4 = 2 by decide] at this
  have n3 : Nat.nth IsRecord 3 = 5 := by
    have := Nat.nth_count (p := IsRecord) (n := 5) (by decide)
    rwa [show Nat.count IsRecord 5 = 3 by decide] at this
  have n4 : Nat.nth IsRecord 4 = 6 := by
    have := Nat.nth_count (p := IsRecord) (n := 6) (by decide)
    rwa [show Nat.count IsRecord 6 = 4 by decide] at this
  have n5 : Nat.nth IsRecord 5 = 7 := by
    have := Nat.nth_count (p := IsRecord) (n := 7) (by decide)
    rwa [show Nat.count IsRecord 7 = 5 by decide] at this
  have v1 : a 1 = 4 := by rw [a, show 1 - 1 = 0 from rfl, n0]; decide
  have v2 : a 2 = 5 := by rw [a, show 2 - 1 = 1 from rfl, n1]; decide
  have v3 : a 3 = 7 := by rw [a, show 3 - 1 = 2 from rfl, n2]; decide
  have v4 : a 4 = 8 := by rw [a, show 4 - 1 = 3 from rfl, n3]; decide
  have v5 : a 5 = 9 := by rw [a, show 5 - 1 = 4 from rfl, n4]; decide
  have v6 : a 6 = 20 := by rw [a, show 6 - 1 = 5 from rfl, n5]; decide
  have w : ∀ k, 6 < k → k ≤ 11 → (a k : ℤ) = ((347 + 27 * (-1) ^ k) - 6 * (27 + (-1) ^ k) * k +
      18 * (k : ℤ) ^ 2) / 2 := by
    intro k hk hk'
    rw [← closed k hk]; omega
  have v7 : (a 7 : ℤ) = 55 := by rw [w 7 (by norm_num) (by norm_num)]; norm_num
  have v8 : (a 8 : ℤ) = 91 := by rw [w 8 (by norm_num) (by norm_num)]; norm_num
  have v9 : (a 9 : ℤ) = 187 := by rw [w 9 (by norm_num) (by norm_num)]; norm_num
  have v10 : (a 10 : ℤ) = 247 := by rw [w 10 (by norm_num) (by norm_num)]; norm_num
  have v11 : (a 11 : ℤ) = 391 := by rw [w 11 (by norm_num) (by norm_num)]; norm_num
  set F : PowerSeries ℤ := mk (fun n => if n = 0 then 0 else (a n : ℤ)) with hF
  have product : F * ((1 - X) ^ 3 * (1 + X) ^ 2) = F + (-1 : ℤ) • (F * X ^ 1) + (-2 : ℤ) • (F * X ^ 2) +
      (2 : ℤ) • (F * X ^ 3) + (1 : ℤ) • (F * X ^ 4) + (-1 : ℤ) • (F * X ^ 5) := by
    simp only [zsmul_eq_mul]; push_cast; ring
  have rhs : (X * (4 + X - 6 * X ^ 2 - X ^ 3 + X ^ 4 + 10 * X ^ 5 + 35 * X ^ 6 + 15 * X ^ 7 + 27 * X ^ 8 -
        X ^ 9 - 13 * X ^ 10) : PowerSeries ℤ) = (4 : ℤ) • X ^ 1 + (1 : ℤ) • X ^ 2 + (-6 : ℤ) • X ^ 3 +
      (-1 : ℤ) • X ^ 4 + (1 : ℤ) • X ^ 5 + (10 : ℤ) • X ^ 6 + (35 : ℤ) • X ^ 7 + (15 : ℤ) • X ^ 8 +
      (27 : ℤ) • X ^ 9 + (-1 : ℤ) • X ^ 10 + (-13 : ℤ) • X ^ 11 := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [product, rhs]
  ext n
  simp only [map_add, map_zsmul, coeff_mul_X_pow', hF, coeff_mk, coeff_X_pow, smul_eq_mul]
  by_cases h : 11 < n
  · have hr := recur n h
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega,
      show 5 ≤ n by omega, show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega,
      show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega,
      show n ≠ 7 by omega, show n ≠ 8 by omega, show n ≠ 9 by omega, show n ≠ 10 by omega,
      show n ≠ 11 by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega,
      show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega, if_true, if_false]
    linarith
  · interval_cases n <;> simp [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11]

end P276705

theorem OMA.solution : type_of% @OMA.S_oeis_a276705.main :=
  ⟨P276705.closed, P276705.recur, P276705.gf⟩
