import OMAStatements.S_oeis_a309869
import Mathlib

/-!
Proof of A309869 (Israel's formula and conjecture: `a(n) = 5` iff `n = 14`, `n = 32`, or
`n = 26 - 6*(-1)^k + 132*k`).

Route: `b 3 = 0` unless `n = 2 mod 3`, and then `b 3 = 2(n+1)`. With `m = 4n+5` and `r = b 4`,
`64 r = 6 + t m` for some `0 ≤ t < 64`, so `r ≠ 0`; no triple repeats before `k = 5`, so `a n = 5` iff `b 5 = 0`
iff `S = 3n+4+r` divides `P = 2(n+1)(n+2) r`. One polynomial identity gives `S ∣ 2 (70+t) (122+3t) (18-t)`.
The feasible `t` are `50 - 8 (n mod 8)`. For `t ≠ 18` the divisor `S` is bounded; a check over the small `w`
(`n = 24 w + c`) and over the small cofactors leaves `n = 14, 32, 47, 698, 10733, 13283`, and only `14, 32` have
`S ∣ P`. For `t = 18`, `S = 11 (9v+8)` and `S ∣ P` iff `11 ∣ (24v+22)(24v+21)`, i.e. `n = 20, 164 mod 264`.
-/

namespace OMA.A309869Proof

open OMA.S_oeis_a309869

theorem b_zero' (n : ℕ) : b n 0 = n := rfl
theorem b_one' (n : ℕ) : b n 1 = n + 1 := rfl
theorem b_two' (n : ℕ) : b n 2 = n + 2 := rfl
theorem b_three (n : ℕ) : b n 3 = n * (n + 1) * (n + 2) % (n + (n + 1) + (n + 2)) := rfl
theorem b_four (n : ℕ) : b n 4 = (n + 1) * (n + 2) * b n 3 % (n + 1 + (n + 2) + b n 3) := rfl
theorem b_five (n : ℕ) : b n 5 = (n + 2) * b n 3 * b n 4 % (n + 2 + b n 3 + b n 4) := rfl

theorem mod_of_eq {x m q r : ℕ} (h : x = m * q + r) (hr : r < m) : x % m = r := by
  rw [h, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

theorem b3_zero (n : ℕ) (h : n % 3 ≠ 2) : b n 3 = 0 := by
  rw [b_three]
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1) with h0 | h1
  · obtain ⟨j, rfl⟩ : ∃ j, n = 3 * j := ⟨n / 3, by omega⟩
    refine mod_of_eq (q := j * (3 * j + 2)) ?_ (by omega)
    ring
  · obtain ⟨j, rfl⟩ : ∃ j, n = 3 * j + 1 := ⟨n / 3, by omega⟩
    refine mod_of_eq (q := (j + 1) * (3 * j + 1)) ?_ (by omega)
    ring

theorem b3_two (n : ℕ) (h : n % 3 = 2) : b n 3 = 2 * (n + 1) := by
  rw [b_three]
  obtain ⟨j, rfl⟩ : ∃ j, n = 3 * j + 2 := ⟨n / 3, by omega⟩
  refine mod_of_eq (q := 3 * j ^ 2 + 6 * j + 2) ?_ (by omega)
  ring

theorem a_of_least (n m : ℕ) (hm : Stop n m) (hmin : ∀ k < m, ¬ Stop n k) :
    a n = if b n m = 0 then (m : ℤ) else -(m : ℤ) := by
  have hex : ∃ k, Stop n k := ⟨m, hm⟩
  have hs : stopIdx n = m := by
    unfold stopIdx
    apply le_antisymm (Nat.sInf_le (s := {k | Stop n k}) hm)
    exact not_lt.mp fun hc => hmin _ hc (Nat.sInf_mem (s := {k | Stop n k}) hex)
  unfold a
  rw [if_pos hex, hs]

theorem a_five_imp (n : ℕ) (h : a n = 5) : b n 5 = 0 := by
  unfold a at h
  split_ifs at h with h1 h2
  · have h5 : stopIdx n = 5 := by exact_mod_cast h
    rw [h5] at h2
    exact h2
  · omega
  · norm_num at h

theorem a_three (n : ℕ) (h : b n 3 = 0) : a n = 3 := by
  have hs : Stop n 3 := by
    unfold Stop
    exact ⟨le_refl 3, Or.inl h⟩
  have hmin : ∀ k < 3, ¬ Stop n k := by
    intro k hk hs'
    unfold Stop at hs'
    exact absurd hs'.1 (by omega)
  have ha := a_of_least n 3 hs hmin
  rw [if_pos h] at ha
  exact_mod_cast ha

theorem not_stop3 (n : ℕ) (hb : b n 3 ≠ 0) : ¬ Stop n 3 := by
  unfold Stop
  rintro ⟨-, h0 | ⟨j, hj2, hj3, heq⟩⟩
  · exact hb h0
  · obtain rfl : j = 2 := by omega
    have h1 : b n 0 = b n 1 := congrArg Prod.fst heq
    rw [b_zero', b_one'] at h1
    omega

theorem not_stop4 (n : ℕ) (hb : b n 4 ≠ 0) : ¬ Stop n 4 := by
  unfold Stop
  rintro ⟨-, h0 | ⟨j, hj2, hj4, heq⟩⟩
  · exact hb h0
  · rcases (by omega : j = 2 ∨ j = 3) with rfl | rfl
    · have h1 : b n 0 = b n 2 := congrArg Prod.fst heq
      rw [b_zero', b_two'] at h1
      omega
    · have h1 : b n 1 = b n 2 := congrArg Prod.fst heq
      rw [b_one', b_two'] at h1
      omega

/-- `b n 4 = r` satisfies `64 r = 6 + t (4n+5)` with `0 ≤ t < 64`. -/
theorem exists_t (n : ℕ) (hn : 1 ≤ n) (r : ℕ)
    (hr : r = (n + 1) * (n + 2) * (2 * (n + 1)) % (n + 1 + (n + 2) + 2 * (n + 1))) :
    ∃ t : ℤ, 0 ≤ t ∧ t < 64 ∧ 64 * (r : ℤ) = 6 + t * (4 * n + 5) := by
  have hdm := Nat.div_add_mod ((n + 1) * (n + 2) * (2 * (n + 1))) (n + 1 + (n + 2) + 2 * (n + 1))
  rw [← hr] at hdm
  have hlt : r < n + 1 + (n + 2) + 2 * (n + 1) := by
    rw [hr]
    exact Nat.mod_lt _ (by omega)
  generalize (n + 1) * (n + 2) * (2 * (n + 1)) / (n + 1 + (n + 2) + 2 * (n + 1)) = q at hdm
  have hdmZ : ((n : ℤ) + 1 + (n + 2) + 2 * (n + 1)) * q + r = (n + 1) * (n + 2) * (2 * (n + 1)) := by
    exact_mod_cast hdm
  obtain ⟨t, ht⟩ : ∃ t : ℤ, t = 2 * (4 * (n : ℤ) + 5) ^ 2 + 2 * (4 * n + 5) - 10 - 64 * q := ⟨_, rfl⟩
  have h64 : 64 * (r : ℤ) = 6 + t * (4 * n + 5) := by
    rw [ht]
    linear_combination 64 * hdmZ
  have hrM : (r : ℤ) < 4 * n + 5 := by
    have : r < 4 * n + 5 := by omega
    exact_mod_cast this
  have hr0 : (0 : ℤ) ≤ r := by positivity
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
  refine ⟨t, ?_, ?_, h64⟩
  · by_contra hc
    have hm := mul_le_mul_of_nonneg_right (show t + 1 ≤ 0 by omega) (show (0 : ℤ) ≤ 4 * n + 5 by omega)
    nlinarith
  · by_contra hc
    have hm := mul_le_mul_of_nonneg_right (show (64 : ℤ) ≤ t by omega) (show (0 : ℤ) ≤ 4 * n + 5 by omega)
    nlinarith

set_option maxHeartbeats 4000000 in
/-- The key identity: `S ∣ P` forces `S ∣ 2 (70+t) (122+3t) (18-t)`. -/
theorem dvdD (n r : ℕ) (t : ℤ) (h64 : 64 * (r : ℤ) = 6 + t * (4 * n + 5))
    (hP : n + 2 + 2 * (n + 1) + r ∣ (n + 2) * (2 * (n + 1)) * r) :
    ((n + 2 + 2 * (n + 1) + r : ℕ) : ℤ) ∣ 2 * (70 + t) * (122 + 3 * t) * (18 - t) := by
  have hP' : ((n : ℤ) + 2 + 2 * (n + 1) + r) ∣ ((n : ℤ) + 2) * (2 * (n + 1)) * r := by
    exact_mod_cast hP
  push_cast
  have key : 2 * (70 + t) * (122 + 3 * t) * (18 - t) =
      ((n : ℤ) + 2 + 2 * (n + 1) + r) * ((192 + 4 * t) ^ 3 * 2 * (n + 1) * (n + 2) -
        64 * (6 * ((192 + 4 * t) * n) ^ 2 + (26 * (192 + 4 * t) - 6 * (262 + 5 * t)) * ((192 + 4 * t) * n) +
          36 * (192 + 4 * t) ^ 2 - 26 * (192 + 4 * t) * (262 + 5 * t) + 6 * (262 + 5 * t) ^ 2)) -
      (192 + 4 * t) ^ 3 * (((n : ℤ) + 2) * (2 * (n + 1)) * r) := by
    linear_combination (6 * ((192 + 4 * t) * n) ^ 2 + (26 * (192 + 4 * t) - 6 * (262 + 5 * t)) * ((192 + 4 * t) * n) +
          36 * (192 + 4 * t) ^ 2 - 26 * (192 + 4 * t) * (262 + 5 * t) + 6 * (262 + 5 * t) ^ 2) * h64
  rw [key]
  exact dvd_sub (dvd_mul_right _ _) (dvd_mul_of_dvd_right hP' _)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem c2 (n r : ℕ) (hn : n % 3 = 2) (h : 64 * r = 6 + 2 * (4 * n + 5))
    (hP : n + 2 + 2 * (n + 1) + r ∣ (n + 2) * (2 * (n + 1)) * r) : n = 14 := by
  have hZ := dvdD n r 2 (by omega) hP
  have hN : n + 2 + 2 * (n + 1) + r ∣ 294912 := by
    have e : (2 * (70 + 2) * (122 + 3 * 2) * (18 - 2) : ℤ) = ((294912 : ℕ) : ℤ) := by norm_num
    rw [e, Int.natCast_dvd_natCast] at hZ
    exact hZ
  obtain ⟨w, rfl⟩ : ∃ w, n = 24 * w + 14 := ⟨n / 24, by omega⟩
  obtain rfl : r = 3 * w + 2 := by omega
  have hS : 24 * w + 14 + 2 + 2 * (24 * w + 14 + 1) + (3 * w + 2) = 75 * w + 48 := by ring
  rw [hS] at hN
  have hw : w = 0 := by
    rcases Nat.lt_or_ge w 63 with hw | hw
    · exact (by decide : ∀ w < 63, 75 * w + 48 ∣ 294912 → w = 0) w hw hN
    · obtain ⟨e, he⟩ := hN
      have he' : e ≤ 61 := by nlinarith
      interval_cases e <;> omega
  omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem c10 (n r : ℕ) (hn : n % 3 = 2) (h : 64 * r = 6 + 10 * (4 * n + 5))
    (hP : n + 2 + 2 * (n + 1) + r ∣ (n + 2) * (2 * (n + 1)) * r) : False := by
  have hZ := dvdD n r 10 (by omega) hP
  have hN : n + 2 + 2 * (n + 1) + r ∣ 194560 := by
    have e : (2 * (70 + 10) * (122 + 3 * 10) * (18 - 10) : ℤ) = ((194560 : ℕ) : ℤ) := by norm_num
    rw [e, Int.natCast_dvd_natCast] at hZ
    exact hZ
  obtain ⟨w, rfl⟩ : ∃ w, n = 24 * w + 5 := ⟨n / 24, by omega⟩
  obtain rfl : r = 15 * w + 4 := by omega
  have hS : 24 * w + 5 + 2 + 2 * (24 * w + 5 + 1) + (15 * w + 4) = 87 * w + 23 := by ring
  rw [hS] at hN
  have hw : w = 447 := by
    rcases Nat.lt_or_ge w 48 with hw | hw
    · exact (by decide : ∀ w < 48, 87 * w + 23 ∣ 194560 → w = 447) w hw hN
    · obtain ⟨e, he⟩ := hN
      have he' : e ≤ 46 := by nlinarith
      interval_cases e <;> omega
  subst hw
  revert hP
  decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem c26 (n r : ℕ) (hn : n % 3 = 2) (h : 64 * r = 6 + 26 * (4 * n + 5))
    (hP : n + 2 + 2 * (n + 1) + r ∣ (n + 2) * (2 * (n + 1)) * r) : False := by
  have hZ := dvdD n r 26 (by omega) hP
  have hN : n + 2 + 2 * (n + 1) + r ∣ 307200 := by
    have e : (2 * (70 + 26) * (122 + 3 * 26) * (18 - 26) : ℤ) = -((307200 : ℕ) : ℤ) := by norm_num
    rw [e, dvd_neg, Int.natCast_dvd_natCast] at hZ
    exact hZ
  obtain ⟨w, rfl⟩ : ∃ w, n = 24 * w + 11 := ⟨n / 24, by omega⟩
  obtain rfl : r = 39 * w + 20 := by omega
  have hS : 24 * w + 11 + 2 + 2 * (24 * w + 11 + 1) + (39 * w + 20) = 111 * w + 57 := by ring
  rw [hS] at hN
  have hw : w = 553 := by
    rcases Nat.lt_or_ge w 53 with hw | hw
    · exact (by decide : ∀ w < 53, 111 * w + 57 ∣ 307200 → w = 553) w hw hN
    · obtain ⟨e, he⟩ := hN
      have he' : e ≤ 51 := by nlinarith
      interval_cases e <;> omega
  subst hw
  revert hP
  decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem c34 (n r : ℕ) (hn : n % 3 = 2) (h : 64 * r = 6 + 34 * (4 * n + 5))
    (hP : n + 2 + 2 * (n + 1) + r ∣ (n + 2) * (2 * (n + 1)) * r) : False := by
  have hZ := dvdD n r 34 (by omega) hP
  have hN : n + 2 + 2 * (n + 1) + r ∣ 745472 := by
    have e : (2 * (70 + 34) * (122 + 3 * 34) * (18 - 34) : ℤ) = -((745472 : ℕ) : ℤ) := by norm_num
    rw [e, dvd_neg, Int.natCast_dvd_natCast] at hZ
    exact hZ
  obtain ⟨w, rfl⟩ : ∃ w, n = 24 * w + 2 := ⟨n / 24, by omega⟩
  obtain rfl : r = 51 * w + 7 := by omega
  have hS : 24 * w + 2 + 2 + 2 * (24 * w + 2 + 1) + (51 * w + 7) = 123 * w + 17 := by ring
  rw [hS] at hN
  have hw : w = 29 := by
    rcases Nat.lt_or_ge w 78 with hw | hw
    · exact (by decide : ∀ w < 78, 123 * w + 17 ∣ 745472 → w = 29) w hw hN
    · obtain ⟨e, he⟩ := hN
      have he' : e ≤ 77 := by nlinarith
      interval_cases e <;> omega
  subst hw
  revert hP
  decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem c42 (n r : ℕ) (hn : n % 3 = 2) (h : 64 * r = 6 + 42 * (4 * n + 5))
    (hP : n + 2 + 2 * (n + 1) + r ∣ (n + 2) * (2 * (n + 1)) * r) : False := by
  have hZ := dvdD n r 42 (by omega) hP
  have hN : n + 2 + 2 * (n + 1) + r ∣ 1333248 := by
    have e : (2 * (70 + 42) * (122 + 3 * 42) * (18 - 42) : ℤ) = -((1333248 : ℕ) : ℤ) := by norm_num
    rw [e, dvd_neg, Int.natCast_dvd_natCast] at hZ
    exact hZ
  obtain ⟨w, rfl⟩ : ∃ w, n = 24 * w + 17 := ⟨n / 24, by omega⟩
  obtain rfl : r = 63 * w + 48 := by omega
  have hS : 24 * w + 17 + 2 + 2 * (24 * w + 17 + 1) + (63 * w + 48) = 135 * w + 103 := by ring
  rw [hS] at hN
  rcases Nat.lt_or_ge w 100 with hw | hw
  · exact (by decide : ∀ w < 100, 135 * w + 103 ∣ 1333248 → False) w hw hN
  · obtain ⟨e, he⟩ := hN
    have he' : e ≤ 98 := by nlinarith
    interval_cases e <;> omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem c50 (n r : ℕ) (hn : n % 3 = 2) (h : 64 * r = 6 + 50 * (4 * n + 5))
    (hP : n + 2 + 2 * (n + 1) + r ∣ (n + 2) * (2 * (n + 1)) * r) : n = 32 := by
  have hZ := dvdD n r 50 (by omega) hP
  have hN : n + 2 + 2 * (n + 1) + r ∣ 2088960 := by
    have e : (2 * (70 + 50) * (122 + 3 * 50) * (18 - 50) : ℤ) = -((2088960 : ℕ) : ℤ) := by norm_num
    rw [e, dvd_neg, Int.natCast_dvd_natCast] at hZ
    exact hZ
  obtain ⟨w, rfl⟩ : ∃ w, n = 24 * w + 8 := ⟨n / 24, by omega⟩
  obtain rfl : r = 75 * w + 29 := by omega
  have hS : 24 * w + 8 + 2 + 2 * (24 * w + 8 + 1) + (75 * w + 29) = 147 * w + 57 := by ring
  rw [hS] at hN
  have hw : w = 1 := by
    rcases Nat.lt_or_ge w 120 with hw | hw
    · exact (by decide : ∀ w < 120, 147 * w + 57 ∣ 2088960 → w = 1) w hw hN
    · obtain ⟨e, he⟩ := hN
      have he' : e ≤ 118 := by nlinarith
      interval_cases e <;> omega
  omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem c58 (n r : ℕ) (hn : n % 3 = 2) (h : 64 * r = 6 + 58 * (4 * n + 5))
    (hP : n + 2 + 2 * (n + 1) + r ∣ (n + 2) * (2 * (n + 1)) * r) : False := by
  have hZ := dvdD n r 58 (by omega) hP
  have hN : n + 2 + 2 * (n + 1) + r ∣ 3031040 := by
    have e : (2 * (70 + 58) * (122 + 3 * 58) * (18 - 58) : ℤ) = -((3031040 : ℕ) : ℤ) := by norm_num
    rw [e, dvd_neg, Int.natCast_dvd_natCast] at hZ
    exact hZ
  obtain ⟨w, rfl⟩ : ∃ w, n = 24 * w + 23 := ⟨n / 24, by omega⟩
  obtain rfl : r = 87 * w + 88 := by omega
  have hS : 24 * w + 23 + 2 + 2 * (24 * w + 23 + 1) + (87 * w + 88) = 159 * w + 161 := by ring
  rw [hS] at hN
  have hw : w = 1 := by
    rcases Nat.lt_or_ge w 139 with hw | hw
    · exact (by decide : ∀ w < 139, 159 * w + 161 ∣ 3031040 → w = 1) w hw hN
    · obtain ⟨e, he⟩ := hN
      have he' : e ≤ 136 := by nlinarith
      interval_cases e <;> omega
  subst hw
  revert hP
  decide

theorem c18 (n r : ℕ) (hn : n % 3 = 2) (h : 64 * r = 6 + 18 * (4 * n + 5)) :
    (n + 2 + 2 * (n + 1) + r ∣ (n + 2) * (2 * (n + 1)) * r) ↔
      (n = 14 ∨ n = 32 ∨ n % 264 = 20 ∨ n % 264 = 164) := by
  obtain ⟨v, rfl⟩ : ∃ v, n = 24 * v + 20 := ⟨n / 24, by omega⟩
  obtain rfl : r = 27 * v + 24 := by omega
  have hS : 24 * v + 20 + 2 + 2 * (24 * v + 20 + 1) + (27 * v + 24) = 11 * (9 * v + 8) := by ring
  have hPe : (24 * v + 20 + 2) * (2 * (24 * v + 20 + 1)) * (27 * v + 24) =
      6 * (24 * v + 22) * (24 * v + 21) * (9 * v + 8) := by ring
  rw [hS, hPe, Nat.mul_dvd_mul_iff_right (by omega : 0 < 9 * v + 8)]
  have p11 : Nat.Prime 11 := by norm_num
  rw [Nat.Prime.dvd_mul p11, Nat.Prime.dvd_mul p11]
  constructor
  · intro hd
    omega
  · intro hd
    omega

set_option maxHeartbeats 4000000 in
theorem core (n r : ℕ) (t : ℤ) (hn : n % 3 = 2) (ht0 : 0 ≤ t) (ht1 : t < 64)
    (h64 : 64 * (r : ℤ) = 6 + t * (4 * n + 5)) :
    (n + 2 + 2 * (n + 1) + r ∣ (n + 2) * (2 * (n + 1)) * r) ↔
      (n = 14 ∨ n = 32 ∨ n % 264 = 20 ∨ n % 264 = 164) := by
  have ht : t = 2 ∨ t = 10 ∨ t = 18 ∨ t = 26 ∨ t = 34 ∨ t = 42 ∨ t = 50 ∨ t = 58 := by
    interval_cases t <;> omega
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h : 64 * r = 6 + 2 * (4 * n + 5) := by omega
    constructor
    · intro hP
      exact Or.inl (c2 n r hn h hP)
    · rintro (rfl | rfl | h' | h')
      · obtain rfl : r = 2 := by omega
        decide
      all_goals omega
  · have h : 64 * r = 6 + 10 * (4 * n + 5) := by omega
    constructor
    · intro hP
      exact (c10 n r hn h hP).elim
    · rintro (rfl | rfl | h' | h') <;> omega
  · exact c18 n r hn (by omega)
  · have h : 64 * r = 6 + 26 * (4 * n + 5) := by omega
    constructor
    · intro hP
      exact (c26 n r hn h hP).elim
    · rintro (rfl | rfl | h' | h') <;> omega
  · have h : 64 * r = 6 + 34 * (4 * n + 5) := by omega
    constructor
    · intro hP
      exact (c34 n r hn h hP).elim
    · rintro (rfl | rfl | h' | h') <;> omega
  · have h : 64 * r = 6 + 42 * (4 * n + 5) := by omega
    constructor
    · intro hP
      exact (c42 n r hn h hP).elim
    · rintro (rfl | rfl | h' | h') <;> omega
  · have h : 64 * r = 6 + 50 * (4 * n + 5) := by omega
    constructor
    · intro hP
      exact Or.inr (Or.inl (c50 n r hn h hP))
    · rintro (rfl | rfl | h' | h')
      · omega
      · obtain rfl : r = 104 := by omega
        decide
      all_goals omega
  · have h : 64 * r = 6 + 58 * (4 * n + 5) := by omega
    constructor
    · intro hP
      exact (c58 n r hn h hP).elim
    · rintro (rfl | rfl | h' | h') <;> omega

theorem rhs_iff (n : ℕ) :
    (∃ k : ℕ, (n : ℤ) = 26 - 6 * (-1) ^ k + 132 * k) ↔ (n % 264 = 20 ∨ n % 264 = 164) := by
  constructor
  · rintro ⟨k, hk⟩
    rcases Nat.even_or_odd k with he | ho
    · rw [he.neg_one_pow] at hk
      obtain ⟨j, rfl⟩ := he
      omega
    · rw [ho.neg_one_pow] at hk
      obtain ⟨j, rfl⟩ := ho
      omega
  · rintro (h | h)
    · refine ⟨2 * (n / 264), ?_⟩
      rw [(even_two_mul _).neg_one_pow]
      omega
    · refine ⟨2 * (n / 264) + 1, ?_⟩
      rw [(odd_two_mul_add_one _).neg_one_pow]
      omega

theorem main_proof :
    ∀ n ≥ 1, a n = 5 ↔ (n = 14 ∨ n = 32 ∨ ∃ k : ℕ, (n : ℤ) = 26 - 6 * (-1) ^ k + 132 * k) := by
  intro n hn
  rw [rhs_iff n]
  by_cases h3 : n % 3 = 2
  · have hb3 := b3_two n h3
    obtain ⟨t, ht0, ht1, h64⟩ := exists_t n hn (b n 4) (by rw [b_four, hb3])
    have hb4 : b n 4 ≠ 0 := by
      intro h0
      rw [h0] at h64
      have hpos : 0 ≤ t * (4 * (n : ℤ) + 5) := mul_nonneg ht0 (by positivity)
      push_cast at h64
      linarith
    rw [← core n (b n 4) t h3 ht0 ht1 h64]
    constructor
    · intro ha
      have h5 := a_five_imp n ha
      rw [b_five, hb3] at h5
      exact Nat.dvd_of_mod_eq_zero h5
    · intro hd
      have h5 : b n 5 = 0 := by
        rw [b_five, hb3]
        exact Nat.dvd_iff_mod_eq_zero.mp hd
      have hstop : Stop n 5 := by
        unfold Stop
        exact ⟨by norm_num, Or.inl h5⟩
      have hmin : ∀ k < 5, ¬ Stop n k := by
        intro k hk hs
        rcases (by omega : k < 3 ∨ k = 3 ∨ k = 4) with hk' | rfl | rfl
        · unfold Stop at hs
          exact absurd hs.1 (by omega)
        · exact not_stop3 n (by rw [hb3]; omega) hs
        · exact not_stop4 n hb4 hs
      have ha := a_of_least n 5 hstop hmin
      rw [if_pos h5] at ha
      exact_mod_cast ha
  · have hb3 := b3_zero n h3
    rw [a_three n hb3]
    constructor
    · intro h
      norm_num at h
    · intro h
      omega

end OMA.A309869Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a309869.main := by
  exact OMA.A309869Proof.main_proof
