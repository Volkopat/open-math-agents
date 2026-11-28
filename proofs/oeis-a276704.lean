import OMAStatements.S_oeis_a276704
import Mathlib

open OMA.S_oeis_a276704
open PowerSeries

namespace P276704

theorem natAbs_sub (n : ℕ) (h : 2 ≤ n) : ((n : ℤ) - 2).natAbs = n - 2 := by
  have : ((n : ℤ) - 2) = ((n - 2 : ℕ) : ℤ) := by push_cast [Nat.cast_sub h]; ring
  rw [this, Int.natAbs_natCast]

theorem L_odd (n : ℕ) (h : 3 ≤ n) (ho : n % 2 = 1) : L n = (n + 2) * (n - 2) := by
  rw [L, natAbs_sub n (by omega)]
  apply Nat.Coprime.lcm_eq_mul
  set d := Nat.gcd (n + 2) (n - 2) with hd
  have h1 : d ∣ n + 2 := Nat.gcd_dvd_left _ _
  have h2 : d ∣ n - 2 := Nat.gcd_dvd_right _ _
  have h4 : d ∣ 4 := by
    have := Nat.dvd_sub h1 h2
    rwa [show n + 2 - (n - 2) = 4 by omega] at this
  have hle : d ≤ 4 := Nat.le_of_dvd (by norm_num) h4
  have hpos : 0 < d := Nat.pos_of_dvd_of_pos h4 (by norm_num)
  have hodd : ¬ 2 ∣ d := by
    intro h2d
    have := Nat.dvd_trans h2d h1
    omega
  show d = 1
  interval_cases d <;> omega

theorem L_even (n : ℕ) (h : 2 ≤ n) (he : n % 2 = 0) : 2 * L n ≤ (n + 2) * (n - 2) := by
  rw [L, natAbs_sub n h]
  have hg := Nat.gcd_mul_lcm (n + 2) (n - 2)
  have h2 : 2 ∣ Nat.gcd (n + 2) (n - 2) := Nat.dvd_gcd (by omega) (by omega)
  have hpos : 0 < Nat.gcd (n + 2) (n - 2) := Nat.gcd_pos_of_pos_left _ (by omega)
  have : 2 ≤ Nat.gcd (n + 2) (n - 2) := Nat.le_of_dvd hpos h2
  calc 2 * Nat.lcm (n + 2) (n - 2) ≤ Nat.gcd (n + 2) (n - 2) * Nat.lcm (n + 2) (n - 2) :=
        Nat.mul_le_mul_right _ this
    _ = (n + 2) * (n - 2) := hg

theorem L1 : L 1 = 3 := by decide

theorem L_lt (j n : ℕ) (hj : 1 ≤ j) (hjn : j < n) (hn : 5 ≤ n) (ho : n % 2 = 1) : L j < L n := by
  rw [L_odd n (by omega) ho]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  rw [show k + 5 - 2 = k + 3 by omega]
  rcases Nat.lt_or_ge j 2 with h | h
  · obtain rfl : j = 1 := by omega
    rw [L1]; nlinarith
  · rcases Nat.mod_two_eq_zero_or_one j with hje | hjo
    · have := L_even j h hje
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
      rw [show i + 2 - 2 = i by omega] at this
      nlinarith
    · have hj3 : 3 ≤ j := by omega
      rw [L_odd j hj3 hjo]
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 3 := ⟨j - 3, by omega⟩
      rw [show i + 3 - 2 = i + 1 by omega]
      nlinarith

theorem rec_iff (n : ℕ) : IsRecord n ↔ (n = 1 ∨ n = 3 ∨ n = 4 ∨ (n % 2 = 1 ∧ 5 ≤ n)) := by
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> decide
  · rcases Nat.mod_two_eq_zero_or_one n with he | ho
    · constructor
      · rintro ⟨-, -, hr⟩
        exfalso
        have h1 := hr (n - 1) (by omega) (by omega)
        rw [L_odd (n - 1) (by omega) (by omega)] at h1
        have h2 := L_even n (by omega) he
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
        rw [show k + 6 - 1 + 2 = k + 7 by omega, show k + 6 - 1 - 2 = k + 3 by omega] at h1
        rw [show k + 6 - 2 = k + 4 by omega] at h2
        nlinarith
      · intro hc; omega
    · constructor
      · intro _; right; right; right; exact ⟨ho, h⟩
      · intro _
        refine ⟨by omega, ?_, fun j hj h1 => L_lt j n h1 hj h ho⟩
        rw [L_odd n (by omega) ho]
        exact Nat.mul_pos (by omega) (by omega)

theorem count_eq (m : ℕ) : Nat.count IsRecord (2 * m + 5) = m + 3 := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [show 2 * (m + 1) + 5 = (2 * m + 5) + 1 + 1 by ring, Nat.count_succ, Nat.count_succ, ih]
    have p1 : IsRecord (2 * m + 5) := (rec_iff _).mpr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
    have p2 : ¬ IsRecord (2 * m + 5 + 1) := by rw [rec_iff]; omega
    rw [if_pos p1, if_neg p2]

theorem nth_eq (m : ℕ) : Nat.nth IsRecord (m + 3) = 2 * m + 5 := by
  have p1 : IsRecord (2 * m + 5) := (rec_iff _).mpr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
  have := Nat.nth_count p1
  rwa [count_eq] at this

theorem closed (n : ℕ) (hn : 3 < n) : (a n : ℤ) = 4 * n ^ 2 - 12 * n + 5 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [a, show m + 4 - 1 = m + 3 by omega, nth_eq, L_odd _ (by omega) (by omega),
    show 2 * m + 5 - 2 = 2 * m + 3 by omega]
  push_cast; ring

theorem recur (n : ℕ) (hn : 6 < n) : (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  rw [closed n (by omega), closed (n - 1) (by omega), closed (n - 2) (by omega),
    closed (n - 3) (by omega)]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega, show m + 7 - 3 = m + 4 by omega]
  push_cast; ring

theorem a1 : a 1 = 3 := by
  have := Nat.nth_count (p := IsRecord) (n := 1) (by decide)
  have c : Nat.count IsRecord 1 = 0 := by decide
  rw [c] at this
  rw [a, show 1 - 1 = 0 from rfl, this, L1]
theorem a2 : a 2 = 5 := by
  have := Nat.nth_count (p := IsRecord) (n := 3) (by decide)
  have c : Nat.count IsRecord 3 = 1 := by decide
  rw [c] at this
  rw [a, show 2 - 1 = 1 from rfl, this]; decide
theorem a3 : a 3 = 6 := by
  have := Nat.nth_count (p := IsRecord) (n := 4) (by decide)
  have c : Nat.count IsRecord 4 = 2 := by decide
  rw [c] at this
  rw [a, show 3 - 1 = 2 from rfl, this]; decide

open PowerSeries in
theorem gf : mk (fun n => if n = 0 then 0 else (a n : ℤ)) * (1 - X) ^ 3 =
      (X * (3 - 4 * X + 15 * X ^ 3 - 5 * X ^ 4 - X ^ 5) : PowerSeries ℤ) := by
  have v4 : (a 4 : ℤ) = 21 := by rw [closed 4 (by norm_num)]; norm_num
  have v5 : (a 5 : ℤ) = 45 := by rw [closed 5 (by norm_num)]; norm_num
  have v6 : (a 6 : ℤ) = 77 := by rw [closed 6 (by norm_num)]; norm_num
  set F : PowerSeries ℤ := mk (fun n => if n = 0 then 0 else (a n : ℤ)) with hF
  have product : F * (1 - X) ^ 3 = F + (-3 : ℤ) • (F * X ^ 1) + (3 : ℤ) • (F * X ^ 2) + (-1 : ℤ) • (F * X ^ 3) := by
    simp only [zsmul_eq_mul]; push_cast; ring
  have rhs : (X * (3 - 4 * X + 15 * X ^ 3 - 5 * X ^ 4 - X ^ 5) : PowerSeries ℤ) = (3 : ℤ) • X ^ 1 + (-4 : ℤ) • X ^ 2 + (15 : ℤ) • X ^ 4 + (-5 : ℤ) • X ^ 5 + (-1 : ℤ) • X ^ 6 := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [product, rhs]
  ext n
  simp only [map_add, map_zsmul, coeff_mul_X_pow', hF, coeff_mk, coeff_X_pow, smul_eq_mul]
  by_cases h : 6 < n
  · have hr := recur n h
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show n ≠ 0 by omega,
      show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega,
      show n ≠ 6 by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega,
      show n - 3 ≠ 0 by omega, if_true, if_false]
    linarith
  · interval_cases n <;> simp [a1, a2, a3, v4, v5, v6]

end P276704

theorem OMA.solution : type_of% @OMA.S_oeis_a276704.main :=
  ⟨P276704.closed, P276704.recur, P276704.gf⟩
