import OMAStatements.S_oeis_a272706
import Mathlib

namespace OMA.Helpers_a272706
open OMA.S_oeis_a272706

def P (t : ℕ) (x y : ℤ) : Prop :=
  ((t : ℤ) < x + y ∨ x + y < -(t : ℤ) ∨ (t : ℤ) < x - y ∨ x - y < -(t : ℤ)) ∨
  ((x + y) % 2 = 0 ∧ x + y + 2 ≤ t ∧ -(t : ℤ) + 2 ≤ x + y ∧ x - y + 2 ≤ t ∧ -(t : ℤ) + 2 ≤ x - y)

instance (t : ℕ) (x y : ℤ) : Decidable (P t x y) := by unfold P; infer_instance

def P1 (x y : ℤ) : Prop := ¬(((x = 1 ∨ x = -1) ∧ y = 0) ∨ (x = 0 ∧ (y = 1 ∨ y = -1)))

instance (x y : ℤ) : Decidable (P1 x y) := by unfold P1; infer_instance

lemma toNat_dec (p : Prop) [Decidable p] : (decide p).toNat = if p then 1 else 0 := by
  by_cases h : p <;> simp [h]

lemma state_succ (r t : ℕ) (x y : ℤ) : state r (t + 1) x y = Nat.testBit r
    ((state r t x y).toNat + 2 * ((state r t (x - 1) y).toNat + (state r t (x + 1) y).toNat +
      (state r t x (y - 1)).toNat + (state r t x (y + 1)).toNat)) := rfl

def TB (r : ℕ) : Prop := ∀ n < 10, (Nat.testBit r n = true ↔ (n = 0 ∨ n = 1 ∨ n = 9 ∨ (n = 3 ∧ r = 523)))

lemma tb515 : TB 515 := by unfold TB; decide
lemma tb523 : TB 523 := by unfold TB; decide

lemma s1 (r : ℕ) (htb : TB r) (x y : ℤ) : state r 1 x y = decide (P1 x y) := by
  rw [state_succ, Bool.eq_iff_iff, htb]
  · simp only [state]
    simp only [toNat_dec, decide_eq_true_iff]
    unfold P1; split_ifs <;>
      (try simp only [true_or, or_true, false_or, or_false, true_iff, iff_true, false_iff, iff_false, false_and, and_false, or_self, not_false_eq_true]) <;>
      omega
  · have h0 := Bool.toNat_le (state r 0 x y)
    have h1 := Bool.toNat_le (state r 0 (x - 1) y)
    have h2 := Bool.toNat_le (state r 0 (x + 1) y)
    have h3 := Bool.toNat_le (state r 0 x (y - 1))
    have h4 := Bool.toNat_le (state r 0 x (y + 1))
    omega

set_option maxHeartbeats 4000000 in
lemma s2 (r : ℕ) (htb : TB r) (x y : ℤ) : state r 2 x y = decide (P 2 x y) := by
  rw [state_succ, Bool.eq_iff_iff, htb]
  · rw [s1 r htb, s1 r htb, s1 r htb, s1 r htb, s1 r htb]
    simp only [toNat_dec, decide_eq_true_iff]
    by_cases c0 : P1 x y <;> by_cases c1 : P1 (x - 1) y <;> by_cases c2 : P1 (x + 1) y <;> by_cases c3 : P1 x (y - 1) <;> by_cases c4 : P1 x (y + 1) <;>
      simp only [c0, c1, c2, c3, c4, if_true, if_false] <;>
      (try simp only [true_or, or_true, false_or, or_false, true_iff, iff_true, false_iff, iff_false, false_and, and_false, or_self, not_false_eq_true]) <;>
      (try unfold P1 P at *) <;> omega
  · have h0 := Bool.toNat_le (state r 1 x y)
    have h1 := Bool.toNat_le (state r 1 (x - 1) y)
    have h2 := Bool.toNat_le (state r 1 (x + 1) y)
    have h3 := Bool.toNat_le (state r 1 x (y - 1))
    have h4 := Bool.toNat_le (state r 1 x (y + 1))
    omega

set_option maxHeartbeats 4000000 in
lemma sstep (r t : ℕ) (htb : TB r) (hA : ∀ x y, state r t x y = decide (P t x y)) (x y : ℤ) :
    state r (t + 1) x y = decide (P (t + 1) x y) := by
  rw [state_succ, Bool.eq_iff_iff, htb]
  · rw [hA, hA, hA, hA, hA]
    simp only [toNat_dec, decide_eq_true_iff]
    by_cases c0 : P t x y <;> by_cases c1 : P t (x - 1) y <;> by_cases c2 : P t (x + 1) y <;> by_cases c3 : P t x (y - 1) <;> by_cases c4 : P t x (y + 1) <;>
      simp only [c0, c1, c2, c3, c4, if_true, if_false] <;>
      (try simp only [true_or, or_true, false_or, or_false, true_iff, iff_true, false_iff, iff_false, false_and, and_false, or_self, not_false_eq_true]) <;>
      (try unfold P at *) <;> omega
  · have h0 := Bool.toNat_le (state r t x y)
    have h1 := Bool.toNat_le (state r t (x - 1) y)
    have h2 := Bool.toNat_le (state r t (x + 1) y)
    have h3 := Bool.toNat_le (state r t x (y - 1))
    have h4 := Bool.toNat_le (state r t x (y + 1))
    omega

noncomputable def S (T : ℕ) : Finset (ℤ × ℤ) := Finset.Icc (-(T : ℤ)) T ×ˢ Finset.Icc (-(T : ℤ)) T

def R (k : ℕ) (p : ℤ × ℤ) : Prop :=
  (p.1 + p.2) % 2 = (k : ℤ) % 2 ∧ -(k : ℤ) ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ k ∧ -(k : ℤ) ≤ p.1 - p.2 ∧
    p.1 - p.2 ≤ k

instance (k : ℕ) (p : ℤ × ℤ) : Decidable (R k p) := by unfold R; infer_instance

lemma cardS (T : ℕ) : (S T).card = (2 * T + 1) ^ 2 := by
  unfold S; rw [Finset.card_product, Int.card_Icc]
  have : ((T : ℤ) + 1 - -(T : ℤ)).toNat = 2 * T + 1 := by omega
  rw [this]; ring

lemma rot (k T : ℕ) (hk : k ≤ T) : ((S T).filter (R k)).card = (k + 1) ^ 2 := by
  rw [sq, ← Finset.card_range (k + 1), ← Finset.card_product]
  symm
  apply Finset.card_nbij' (fun uv : ℕ × ℕ => (((uv.1 : ℤ) + uv.2 - k, (uv.1 : ℤ) - uv.2) : ℤ × ℤ))
    (fun p : ℤ × ℤ => ((((p.1 + p.2 + k) / 2).toNat, ((p.1 - p.2 + k) / 2).toNat) : ℕ × ℕ))
  · rintro ⟨u, v⟩ h
    simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio] at h
    simp only [S, R, Finset.coe_filter, Finset.mem_product, Finset.mem_Icc, Set.mem_setOf_eq]
    omega
  · rintro ⟨x, y⟩ h
    simp only [S, R, Finset.coe_filter, Finset.mem_product, Finset.mem_Icc, Set.mem_setOf_eq] at h
    simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
    omega
  · rintro ⟨u, v⟩ h
    simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio] at h
    simp only [Prod.mk.injEq]
    omega
  · rintro ⟨x, y⟩ h
    simp only [S, R, Finset.coe_filter, Finset.mem_product, Finset.mem_Icc, Set.mem_setOf_eq] at h
    simp only [Prod.mk.injEq]
    omega


lemma countP (t : ℕ) (ht : 3 ≤ t) (hodd : t % 2 = 1) :
    (((S t).filter (fun p => P t p.1 p.2)).card : ℤ) = 3 * t ^ 2 - 2 * t + 4 := by
  have h1 := Finset.card_filter_add_card_filter_not (s := S t) (fun p => P t p.1 p.2)
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (S t).filter (fun p => ¬P t p.1 p.2)) (fun p => (p.1 + p.2) % 2 = 1)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have h3 := Finset.card_filter_add_card_filter_not
    (s := (S t).filter (R (t - 1))) (R (t - 3))
  rw [Finset.filter_filter, Finset.filter_filter] at h3
  have e1 : (S t).filter (fun p => ¬P t p.1 p.2 ∧ (p.1 + p.2) % 2 = 1) = (S t).filter (R t) :=
    Finset.filter_congr (fun p hp => by
      simp only [S, Finset.mem_product, Finset.mem_Icc] at hp; unfold P R; omega)
  have e2 : (S t).filter (fun p => R (t - 1) p ∧ R (t - 3) p) = (S t).filter (R (t - 3)) :=
    Finset.filter_congr (fun p hp => by
      simp only [S, Finset.mem_product, Finset.mem_Icc] at hp; unfold R; omega)
  have e3 : (S t).filter (fun p => R (t - 1) p ∧ ¬R (t - 3) p) =
      (S t).filter (fun p => ¬P t p.1 p.2 ∧ ¬(p.1 + p.2) % 2 = 1) :=
    Finset.filter_congr (fun p hp => by
      simp only [S, Finset.mem_product, Finset.mem_Icc] at hp; unfold P R; omega)
  rw [e1, rot t t le_rfl] at h2
  rw [e2, e3, rot (t - 3) t (by omega), rot (t - 1) t (by omega)] at h3
  rw [cardS] at h1
  have : ((t - 3 : ℕ) : ℤ) = t - 3 := by omega
  have : ((t - 1 : ℕ) : ℤ) = t - 1 := by omega
  zify at h1 h2 h3
  push_cast at h1 h2 h3
  nlinarith

lemma stateP (r : ℕ) (htb : TB r) (t : ℕ) (ht : 2 ≤ t) (x y : ℤ) :
    state r t x y = decide (P t x y) := by
  induction t, ht using Nat.le_induction generalizing x y with
  | base => exact s2 r htb x y
  | succ t ht ih => exact sstep r t htb ih x y

lemma count_eq (r t : ℕ) : count r t = ((S t).filter (fun p => state r t p.1 p.2 = true)).card := rfl

lemma count_big (r : ℕ) (htb : TB r) (t : ℕ) (ht : 3 ≤ t) (hodd : t % 2 = 1) :
    (count r t : ℤ) = 3 * t ^ 2 - 2 * t + 4 := by
  rw [count_eq, ← countP t ht hodd]
  congr 2
  exact Finset.filter_congr (fun p _ => by rw [stateP r htb t (by omega)]; simp)

lemma count1 (r : ℕ) (htb : TB r) : count r 1 = 5 := by
  rw [count_eq]
  have : (S 1).filter (fun p => state r 1 p.1 p.2 = true) = (S 1).filter (fun p => P1 p.1 p.2) :=
    Finset.filter_congr (fun p _ => by rw [s1 r htb]; simp)
  rw [this]
  decide +kernel

end OMA.Helpers_a272706

open OMA.S_oeis_a272706 OMA.Helpers_a272706 in
theorem OMA.solution : type_of% @OMA.S_oeis_a272706.main := by
  have hc0 : ∀ r, count r 0 = 1 := fun r => by
    rw [count_eq]
    have : (S 0).filter (fun p => state r 0 p.1 p.2 = true) = (S 0).filter (fun p => p.1 = 0 ∧ p.2 = 0) :=
      Finset.filter_congr (fun p _ => by simp [state])
    rw [this]; decide +kernel
  have hodd : ∀ n, 1 ≤ n → (2 ^ n - 1) % 2 = 1 := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have := Nat.one_le_two_pow (n := k)
    omega
  have hbig : ∀ n, 2 ≤ n → (a n : ℤ) = 3 * 4 ^ n - 8 * 2 ^ n + 9 := by
    intro n hn
    have h3 : 3 ≤ 2 ^ n - 1 := by
      have : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    unfold a
    rw [count_big 515 tb515 _ h3 (hodd n (by omega))]
    have : ((2 ^ n - 1 : ℕ) : ℤ) = 2 ^ n - 1 := by
      have := Nat.one_le_two_pow (n := n); push_cast [Nat.cast_sub this]; ring
    rw [this, show (4 : ℤ) ^ n = (2 ^ n) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
    ring
  have ha0 : a 0 = 1 := hc0 515
  have ha1 : a 1 = 5 := count1 515 tb515
  have hform : ∀ n : ℕ, 0 < n → (a n : ℤ) = 3 * 4 ^ n - 8 * 2 ^ n + 9 := by
    intro n hn
    rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn
    · rw [ha1]; norm_num
    · exact hbig n hn
  have hrec : ∀ n : ℕ, 4 < n → (a n : ℤ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega, show m + 3 - 3 = m by omega,
      hform _ (by omega), hform _ (by omega), hform _ (by omega), hform _ (by omega)]
    ring
  refine ⟨?_, hform, hrec, ?_⟩
  · intro n
    unfold a
    rcases (show n = 0 ∨ n = 1 ∨ 2 ≤ n by omega) with rfl | rfl | hn
    · rw [show 2 ^ 0 - 1 = 0 from rfl, hc0, hc0]
    · rw [show 2 ^ 1 - 1 = 1 by norm_num, count1 523 tb523, count1 515 tb515]
    · have h3 : 3 ≤ 2 ^ n - 1 := by
        have : 4 ≤ 2 ^ n := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
        omega
      have e1 := count_big 523 tb523 _ h3 (hodd n (by omega))
      have e2 := count_big 515 tb515 _ h3 (hodd n (by omega))
      exact_mod_cast e1.trans e2.symm
  · have ha2 : (a 2 : ℤ) = 25 := by rw [hbig 2 le_rfl]; norm_num
    have ha3 : (a 3 : ℤ) = 137 := by rw [hbig 3 (by norm_num)]; norm_num
    have ha4 : (a 4 : ℤ) = 649 := by rw [hbig 4 (by norm_num)]; norm_num
    set F : PowerSeries ℤ := PowerSeries.mk (fun n => (a n : ℤ)) with hF
    have hL : F * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 4 * PowerSeries.X)) =
        F - 7 * (F * PowerSeries.X ^ 1) + 14 * (F * PowerSeries.X ^ 2) - 8 * (F * PowerSeries.X ^ 3) := by
      ring
    have hR : ((1 + 2 * PowerSeries.X) * (1 - 4 * PowerSeries.X + 12 * PowerSeries.X ^ 2) : PowerSeries ℤ) =
        1 - 2 * PowerSeries.X ^ 1 + 4 * PowerSeries.X ^ 2 + 24 * PowerSeries.X ^ 3 := by ring
    rw [hL, hR]
    ext d
    simp only [map_add, map_sub, ← map_ofNat PowerSeries.C, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_C_mul_X_pow, hF, PowerSeries.coeff_mk,
      PowerSeries.coeff_one]
    rcases (show d ≤ 4 ∨ 5 ≤ d by omega) with hd | hd
    · interval_cases d <;> simp only [PowerSeries.coeff_C, ha2, ha3, ha4, ha0, ha1, Nat.cast_one, Nat.cast_ofNat] <;> norm_num
    · have h := hrec d (by omega)
      have c1 : 1 ≤ d := by omega
      have c2 : 2 ≤ d := by omega
      have c3 : 3 ≤ d := by omega
      have n0 : d ≠ 0 := by omega
      have n1 : d ≠ 1 := by omega
      have n2 : d ≠ 2 := by omega
      have n3 : d ≠ 3 := by omega
      have z1 : d - 1 ≠ 0 := by omega
      have z2 : d - 2 ≠ 0 := by omega
      have z3 : d - 3 ≠ 0 := by omega
      simp only [c1, c2, c3, n0, n1, n2, n3, z1, z2, z3, PowerSeries.coeff_C, if_true, if_false, ↓reduceIte]
      linear_combination h
