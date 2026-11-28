import OMAStatements.S_oeis_a204503
import Mathlib

/-!
Credit: @ivillar
Proof: if m = k^2 and floor(k^2/9) = j^2 then 3j ≤ k < 3j + 3, and k = 3j + 1 forces j ≤ 1,
k = 3j + 2 forces j = 0; so the terms are 1, 4, 16 and the numbers 9t^2. Hence below 36 the terms
are 0, 1, 4, 9, 16, and between 9t^2 and 9(t+1)^2 (t ≥ 2) the only term is 9t^2, so the term of
index t + 3 (from 0) is 9t^2 (this is the argument referred to by Jianing Song via A204502).
The g.f. then follows from the third difference of a quadratic.
-/

namespace OMAA204503Helpers
open PowerSeries OMA.S_oeis_a204503

noncomputable instance decIsTerm : DecidablePred IsTerm := Classical.decPred _

theorem char (m : ℕ) : IsTerm m ↔ m = 1 ∨ m = 4 ∨ m = 16 ∨ ∃ t, m = 9 * t ^ 2 := by
  constructor
  · rintro ⟨⟨k, rfl⟩, ⟨j, hj⟩⟩
    have hdm := Nat.div_add_mod (k * k) 9
    have hml := Nat.mod_lt (k * k) (show 9 > 0 by norm_num)
    rw [hj] at hdm
    have h1 : 9 * (j * j) ≤ k * k := by omega
    have h2 : k * k < 9 * (j * j) + 9 := by omega
    have h3 : 3 * j ≤ k := by
      by_contra hc
      have hle := Nat.mul_self_le_mul_self (show k + 1 ≤ 3 * j by omega)
      nlinarith
    have h4 : k < 3 * j + 3 := by
      by_contra hc
      have hle := Nat.mul_self_le_mul_self (show 3 * j + 3 ≤ k by omega)
      nlinarith
    have hr : k = 3 * j ∨ k = 3 * j + 1 ∨ k = 3 * j + 2 := by omega
    rcases hr with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr ⟨j, by ring⟩))
    · have hj1 : j ≤ 1 := by nlinarith
      interval_cases j <;> norm_num
    · have hj0 : j = 0 := by nlinarith
      subst hj0
      norm_num
  · rintro (rfl | rfl | rfl | ⟨t, rfl⟩)
    · exact ⟨⟨1, rfl⟩, ⟨0, rfl⟩⟩
    · exact ⟨⟨2, rfl⟩, ⟨0, rfl⟩⟩
    · exact ⟨⟨4, rfl⟩, ⟨1, rfl⟩⟩
    · refine ⟨⟨3 * t, by ring⟩, ⟨t, ?_⟩⟩
      rw [Nat.mul_div_cancel_left _ (by norm_num)]
      ring

theorem small (m : ℕ) (hm : m < 36) :
    IsTerm m ↔ (m = 0 ∨ m = 1 ∨ m = 4 ∨ m = 9 ∨ m = 16) := by
  rw [char]
  constructor
  · rintro (h | h | h | ⟨t, rfl⟩)
    · omega
    · omega
    · omega
    · have ht : t ≤ 1 := by nlinarith
      interval_cases t <;> norm_num
  · rintro (h | h | h | h | h)
    · exact Or.inr (Or.inr (Or.inr ⟨0, by rw [h]; norm_num⟩))
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr ⟨1, by rw [h]; norm_num⟩))
    · exact Or.inr (Or.inr (Or.inl h))

theorem count_small (N : ℕ) (hN : N ≤ 36) :
    Nat.count IsTerm N =
      ((Finset.range N).filter (fun m => m = 0 ∨ m = 1 ∨ m = 4 ∨ m = 9 ∨ m = 16)).card := by
  rw [Nat.count_eq_card_filter_range]
  rw [Finset.filter_congr (fun m hm => small m (by simp only [Finset.mem_range] at hm; omega))]

theorem count_block (t : ℕ) (ht : 2 ≤ t) :
    Nat.count (fun x => IsTerm (9 * t ^ 2 + x)) (18 * t + 9) = 1 := by
  rw [Nat.count_eq_card_filter_range, Finset.card_eq_one]
  refine ⟨0, ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hp⟩
    have h36 : 36 ≤ 9 * t ^ 2 := by nlinarith
    rcases (char _).1 hp with h | h | h | ⟨s, hs⟩
    · omega
    · omega
    · omega
    · have hst : s ≤ t := by
        by_contra hc
        have hle := Nat.mul_self_le_mul_self (show t + 1 ≤ s by omega)
        nlinarith
      have hts : t ≤ s := by
        by_contra hc
        have hle := Nat.mul_self_le_mul_self (show s + 1 ≤ t by omega)
        nlinarith
      have hst' : s = t := le_antisymm hst hts
      subst hst'
      omega
  · rintro rfl
    exact ⟨by omega, (char _).2 (Or.inr (Or.inr (Or.inr ⟨t, by ring⟩)))⟩

theorem count_eq (t : ℕ) (ht : 2 ≤ t) : Nat.count IsTerm (9 * t ^ 2) = t + 3 := by
  induction t, ht using Nat.le_induction with
  | base =>
    show Nat.count IsTerm 36 = 5
    rw [count_small 36 le_rfl]
    decide
  | succ k hk ih =>
    rw [show 9 * (k + 1) ^ 2 = 9 * k ^ 2 + (18 * k + 9) by ring, Nat.count_add, ih,
      count_block k hk]

theorem term_sq (t : ℕ) : IsTerm (9 * t ^ 2) := (char _).2 (Or.inr (Or.inr (Or.inr ⟨t, rfl⟩)))

theorem nth_eq (t : ℕ) (ht : 2 ≤ t) : Nat.nth IsTerm (t + 3) = 9 * t ^ 2 := by
  have h := Nat.nth_count (term_sq t)
  rwa [count_eq t ht] at h

theorem nth_small : Nat.nth IsTerm 0 = 0 ∧ Nat.nth IsTerm 1 = 1 ∧ Nat.nth IsTerm 2 = 4 ∧
    Nat.nth IsTerm 3 = 9 ∧ Nat.nth IsTerm 4 = 16 := by
  have p0 : IsTerm 0 := (small 0 (by norm_num)).2 (by norm_num)
  have p1 : IsTerm 1 := (small 1 (by norm_num)).2 (by norm_num)
  have p4 : IsTerm 4 := (small 4 (by norm_num)).2 (by norm_num)
  have p9 : IsTerm 9 := (small 9 (by norm_num)).2 (by norm_num)
  have p16 : IsTerm 16 := (small 16 (by norm_num)).2 (by norm_num)
  have c0 : Nat.count IsTerm 0 = 0 := Nat.count_zero _
  have c1 : Nat.count IsTerm 1 = 1 := by rw [count_small 1 (by norm_num)]; decide
  have c4 : Nat.count IsTerm 4 = 2 := by rw [count_small 4 (by norm_num)]; decide
  have c9 : Nat.count IsTerm 9 = 3 := by rw [count_small 9 (by norm_num)]; decide
  have c16 : Nat.count IsTerm 16 = 4 := by rw [count_small 16 (by norm_num)]; decide
  have e0 := Nat.nth_count p0
  have e1 := Nat.nth_count p1
  have e4 := Nat.nth_count p4
  have e9 := Nat.nth_count p9
  have e16 := Nat.nth_count p16
  rw [c0] at e0
  rw [c1] at e1
  rw [c4] at e4
  rw [c9] at e9
  rw [c16] at e16
  exact ⟨e0, e1, e4, e9, e16⟩

theorem a_large (n : ℕ) (hn : 5 < n) : a n = 9 * (n - 4) ^ 2 := by
  unfold a
  rw [show n - 1 = (n - 4) + 3 by omega]
  exact nth_eq (n - 4) (by omega)

noncomputable def c (n : ℕ) : ℤ := if n = 0 then 0 else (a n : ℤ)

theorem c_large (k : ℕ) (hk : 6 ≤ k) : c k = 9 * ((k : ℤ) - 4) ^ 2 := by
  unfold c
  rw [if_neg (by omega), a_large k (by omega)]
  have h4 : ((k - 4 : ℕ) : ℤ) = (k : ℤ) - 4 := by omega
  rw [Nat.cast_mul, Nat.cast_pow, h4]
  norm_num

theorem coeff_mk_mul_X_pow (n k : ℕ) :
    coeff n (PowerSeries.mk c * X ^ k) = if k ≤ n then c (n - k) else 0 := by
  rw [coeff_mul_X_pow', coeff_mk]

theorem coeff_mk_mul_C_X_pow (r : ℤ) (n k : ℕ) :
    coeff n (PowerSeries.mk c * (C r * X ^ k)) = r * (if k ≤ n then c (n - k) else 0) := by
  rw [mul_left_comm, coeff_C_mul, coeff_mk_mul_X_pow]

theorem coeff_at (n k j : ℕ) (h : n = j + k) : coeff n (PowerSeries.mk c * X ^ k) = c j := by
  rw [coeff_mk_mul_X_pow, if_pos (by omega), show n - k = j by omega]

theorem coeff_at_C (r : ℤ) (n k j : ℕ) (h : n = j + k) :
    coeff n (PowerSeries.mk c * (C r * X ^ k)) = r * c j := by
  rw [mul_left_comm, coeff_C_mul, coeff_at n k j h]

end OMAA204503Helpers

open PowerSeries OMAA204503Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a204503.main := by
  refine ⟨a_large, ?_⟩
  change PowerSeries.mk c * _ = _
  ext n
  have hD : ((X - 1) ^ 3 : PowerSeries ℤ) = X ^ 3 - C 3 * X ^ 2 + C 3 * X ^ 1 - X ^ 0 := by
    rw [map_ofNat C 3]; ring
  have hN : (X ^ 2 * (7 * X ^ 6 - 12 * X ^ 5 - 11 * X ^ 4 - X - 1) : PowerSeries ℤ) =
      C 7 * X ^ 8 - C 12 * X ^ 7 - C 11 * X ^ 6 - X ^ 3 - X ^ 2 := by
    rw [map_ofNat C 7, map_ofNat C 12, map_ofNat C 11]; ring
  rw [hD, hN]
  obtain ⟨e0, e1, e4, e9, e16⟩ := nth_small
  have v0 : c 0 = 0 := rfl
  have v1 : c 1 = 0 := by simp [c, OMA.S_oeis_a204503.a, e0]
  have v2 : c 2 = 1 := by simp [c, OMA.S_oeis_a204503.a, e1]
  have v3 : c 3 = 4 := by simp [c, OMA.S_oeis_a204503.a, e4]
  have v4 : c 4 = 9 := by simp [c, OMA.S_oeis_a204503.a, e9]
  have v5 : c 5 = 16 := by simp [c, OMA.S_oeis_a204503.a, e16]
  have v6 : c 6 = 36 := by rw [c_large 6 le_rfl]; norm_num
  have v7 : c 7 = 81 := by rw [c_large 7 (by norm_num)]; norm_num
  have v8 : c 8 = 144 := by rw [c_large 8 (by norm_num)]; norm_num
  rcases Nat.lt_or_ge n 9 with h | h
  · simp only [mul_add, mul_sub, map_add, map_sub, coeff_mk_mul_C_X_pow, coeff_mk_mul_X_pow,
      coeff_C_mul, coeff_X_pow]
    interval_cases n
    · norm_num [v0]
    · norm_num [v0, v1]
    · norm_num [v0, v1, v2]
    · norm_num [v0, v1, v2, v3]
    · norm_num [v1, v2, v3, v4]
    · norm_num [v2, v3, v4, v5]
    · norm_num [v3, v4, v5, v6]
    · norm_num [v4, v5, v6, v7]
    · norm_num [v5, v6, v7, v8]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    simp only [mul_add, mul_sub, map_add, map_sub]
    rw [coeff_at (m + 9) 3 (m + 6) (by omega), coeff_at_C 3 (m + 9) 2 (m + 7) (by omega),
      coeff_at_C 3 (m + 9) 1 (m + 8) (by omega), coeff_at (m + 9) 0 (m + 9) (by omega),
      coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_X_pow, coeff_X_pow, coeff_X_pow, coeff_X_pow,
      coeff_X_pow, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), c_large (m + 6) (by omega), c_large (m + 7) (by omega),
      c_large (m + 8) (by omega), c_large (m + 9) (by omega)]
    push_cast
    ring
