import OMAStatements.S_oeis_a393856
import Mathlib

namespace R393856
open OMA.S_oeis_a393856

theorem pow_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (g : ℕ → R) :
    ∀ k n, f (powSeq g k n) = powSeq (fun i => f (g i)) k n := by
  intro k
  induction k with
  | zero => intro n; simp only [powSeq]; split_ifs <;> simp
  | succ k ih => intro n; simp only [powSeq, map_sum, map_mul, ih]

theorem cmp_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (u g : ℕ → R) (n : ℕ) :
    f (comp u g n) = comp (fun i => f (u i)) (fun i => f (g i)) n := by
  simp only [comp, map_sum, map_mul, pow_map]

theorem pow_congr {R : Type*} [CommRing R] (g g' : ℕ → R) (N : ℕ) (h : ∀ j ≤ N, g j = g' j) :
    ∀ k n, n ≤ N → powSeq g k n = powSeq g' k n := by
  intro k
  induction k with
  | zero => intro n _; simp only [powSeq]
  | succ k ih =>
    intro n hn
    simp only [powSeq]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [h i (le_trans hi' hn), ih (n - i) (le_trans (Nat.sub_le n i) hn)]

theorem pow_low {R : Type*} [CommRing R] (g : ℕ → R) (hg : g 0 = 0) :
    ∀ k n, n < k → powSeq g k n = 0 := by
  intro k
  induction k with
  | zero => intro n hn; exact absurd hn (Nat.not_lt_zero n)
  | succ k ih =>
    intro n hn
    simp only [powSeq]
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; rw [hg, zero_mul]
    · rw [ih (n - i) (by omega), mul_zero]

def cm {R : Type*} [CommRing R] (m : R) (n : ℕ) : R := if n = 0 then 0 else m ^ (n - 1)

theorem cm_zero {R : Type*} [CommRing R] (m : R) : cm m 0 = 0 := by simp [cm]

theorem cm_succ {R : Type*} [CommRing R] (m : R) (i : ℕ) :
    cm m (i + 1) = (if i = 0 then 1 else 0) + m * cm m i := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h; simp [cm]
  · have hi : i ≠ 0 := Nat.pos_iff_ne_zero.mp h
    simp [cm, hi, mul_pow_sub_one hi]

theorem pow_rec {R : Type*} [CommRing R] (m : R) (c : ℕ → R) (h0 : c 0 = 0)
    (hs : ∀ i, c (i + 1) = (if i = 0 then 1 else 0) + m * c i) (k n : ℕ) :
    powSeq c (k + 1) (n + 1) = powSeq c k n + m * powSeq c (k + 1) n := by
  have e1 : powSeq c (k + 1) (n + 1) =
      ∑ i ∈ Finset.range (n + 1 + 1), c i * powSeq c k (n + 1 - i) := rfl
  have e2 : powSeq c (k + 1) n = ∑ i ∈ Finset.range (n + 1), c i * powSeq c k (n - i) := rfl
  rw [e1, e2, Finset.sum_range_succ' (fun i => c i * powSeq c k (n + 1 - i)) (n + 1), h0,
    zero_mul, add_zero]
  simp [hs, Nat.add_sub_add_right, add_mul, Finset.sum_add_distrib, mul_assoc, Finset.mul_sum]

theorem cmp_one {R : Type*} [CommRing R] (c : ℕ → R) (n : ℕ) :
    comp (cm (1 : R)) c n = ∑ k ∈ Finset.range n, powSeq c (k + 1) n := by
  rw [comp, Finset.sum_range_succ']
  simp [cm]

theorem cmp_cm_succ {R : Type*} [CommRing R] (m : R) (n : ℕ) :
    comp (cm (1 : R)) (cm m) (n + 1) =
      (if n = 0 then 1 else 0) + (m + 1) * comp (cm (1 : R)) (cm m) n := by
  have hrec := pow_rec m (cm m) (cm_zero m) (cm_succ m)
  have hord := pow_low (cm m) (cm_zero m)
  rw [cmp_one, cmp_one]
  simp only [hrec, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_range_succ' (fun k => powSeq (cm m) k n),
    Finset.sum_range_succ (fun k => powSeq (cm m) (k + 1) n), hord (n + 1) n (Nat.lt_succ_self n)]
  have h0 : powSeq (cm m) 0 n = if n = 0 then 1 else 0 := rfl
  rw [h0]
  ring

theorem cmp_cm {R : Type*} [CommRing R] (m : R) :
    ∀ n, comp (cm (1 : R)) (cm m) n = cm (m + 1) n := by
  intro n
  induction n with
  | zero => simp [comp, cm]
  | succ n ih => rw [cmp_cm_succ, ih, cm_succ]

theorem pow_diag {R : Type*} [CommRing R] (g : ℕ → R) (h0 : g 0 = 0) (h1 : g 1 = 1) :
    ∀ k, powSeq g k k = 1 := by
  intro k
  induction k with
  | zero => simp [powSeq]
  | succ k ih =>
    show ∑ i ∈ Finset.range (k + 1 + 1), g i * powSeq g k (k + 1 - i) = 1
    rw [Finset.sum_eq_single_of_mem 1 (Finset.mem_range.mpr (by omega))]
    · simp [h1, ih]
    · intro b hb hb1
      have hb' := Finset.mem_range.mp hb
      rcases Nat.eq_zero_or_pos b with hb0 | hbpos
      · subst hb0; simp [h0]
      · rw [pow_low g h0 k (k + 1 - b) (by omega), mul_zero]

theorem cm_s {R : Type*} [CommRing R] (m : R) (i : ℕ) : cm m (i + 1) = m ^ i := by
  simp [cm]

theorem uniq {R : Type*} [CommRing R] (A G B H : ℕ → R)
    (hE : ∀ n, comp A G n = comp B H n) (h0 : A 0 = B 0) (hH0 : H 0 = 0) (hH1 : H 1 = 1)
    (hG : ∀ m, (∀ j ≤ m, A j = B j) → ∀ j ≤ m + 1, G j = H j) : ∀ n, A n = B n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · exact h0
    · have hag : ∀ j ≤ m, A j = B j := fun j hj => ih j (by omega)
      have hP := pow_congr G H (m + 1) (hG m hag)
      have hd : powSeq H (m + 1) (m + 1) = 1 := pow_diag H hH0 hH1 (m + 1)
      have e1 : comp A G (m + 1) = ∑ k ∈ Finset.range (m + 1), A k * powSeq G k (m + 1) +
          A (m + 1) * powSeq G (m + 1) (m + 1) := Finset.sum_range_succ _ _
      have e2 : comp B H (m + 1) = ∑ k ∈ Finset.range (m + 1), B k * powSeq H k (m + 1) +
          B (m + 1) * powSeq H (m + 1) (m + 1) := Finset.sum_range_succ _ _
      have hS : ∑ k ∈ Finset.range (m + 1), A k * powSeq G k (m + 1) =
          ∑ k ∈ Finset.range (m + 1), B k * powSeq H k (m + 1) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hag k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)), hP k (m + 1) le_rfl]
      rw [hP (m + 1) (m + 1) le_rfl, hd] at e1
      rw [hd] at e2
      linear_combination -e1 + e2 + hE (m + 1) - hS

theorem cast_comp (N : ℕ) (a : ℕ → ℤ)
    (hc : ∀ n : ℕ, comp a (innerSeq a) n = if n = 1 then 1 else 0) (n : ℕ) :
    comp (fun i => ((a i : ℤ) : ZMod N)) (fun i => ((innerSeq a i : ℤ) : ZMod N)) n =
      if n = 1 then 1 else 0 := by
  have hh := congrArg (Int.castRingHom (ZMod N)) (hc n)
  rw [cmp_map] at hh
  simp only [eq_intCast] at hh
  rw [hh]
  split_ifs <;> simp

-- Modulo 5: 4 = -1, so the inner series is x / (1 + x) and A = x / (1 - x).

theorem tgt5 (n : ℕ) :
    comp (cm (1 : ZMod 5)) (cm (-1 : ZMod 5)) n = if n = 1 then 1 else 0 := by
  have h0 : (-1 : ZMod 5) + 1 = 0 := by ring
  rw [cmp_cm, h0]
  rcases n with _ | _ | k
  · simp [cm]
  · simp [cm]
  · simp [cm, zero_pow_eq]

theorem inner5 (a : ℕ → ℤ) (m : ℕ)
    (h : ∀ j ≤ m, ((a j : ℤ) : ZMod 5) = cm (1 : ZMod 5) j) :
    ∀ j ≤ m + 1, ((innerSeq a j : ℤ) : ZMod 5) = cm (-1 : ZMod 5) j := by
  intro j hj
  match j, hj with
  | 0, _ => simp [innerSeq, cm]
  | 1, _ => simp [innerSeq, cm]
  | i + 2, hj =>
    have h4 : (4 : ZMod 5) = -1 := by decide
    have hi : ((a (i + 1) : ℤ) : ZMod 5) = 1 := by
      rw [h (i + 1) (by omega), cm_s, one_pow]
    have hc : cm (-1 : ZMod 5) (i + 2) = (-1) ^ (i + 1) := cm_s (-1) (i + 1)
    have e : innerSeq a (i + 2) = -(4 : ℤ) ^ i * a (i + 1) := rfl
    rw [hc, e]
    push_cast
    rw [hi, h4]
    ring

theorem mod5 (a : ℕ → ℤ) (ha0 : a 0 = 0)
    (hc : ∀ n : ℕ, comp a (innerSeq a) n = if n = 1 then 1 else 0) :
    ∀ n, ((a n : ℤ) : ZMod 5) = cm (1 : ZMod 5) n :=
  uniq (fun i => ((a i : ℤ) : ZMod 5)) (fun i => ((innerSeq a i : ℤ) : ZMod 5)) (cm 1) (cm (-1))
    (fun n => by rw [cast_comp 5 a hc n, tgt5 n]) (by simp [ha0, cm])
    (cm_zero _) (by simp [cm]) (inner5 a)

-- Modulo 2: 4 = 0, so the inner series is x + x^2 and A = sum of x^(2^j).

theorem pow_ps {R : Type*} [CommRing R] (g : ℕ → R) :
    ∀ k n, powSeq g k n = PowerSeries.coeff n ((PowerSeries.mk g) ^ k) := by
  intro k
  induction k with
  | zero => intro n; rw [pow_zero, PowerSeries.coeff_one]; rfl
  | succ k ih =>
    intro n
    rw [pow_succ', PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    show ∑ i ∈ Finset.range (n + 1), g i * powSeq g k (n - i) = _
    apply Finset.sum_congr rfl
    intro i _
    simp only [PowerSeries.coeff_mk, ih]

def g2 (n : ℕ) : ZMod 2 := if n = 1 then 1 else if n = 2 then 1 else 0

theorem mk_g2 : PowerSeries.mk g2 = PowerSeries.X + PowerSeries.X ^ 2 := by
  ext n
  rw [PowerSeries.coeff_mk, map_add, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
  by_cases h1 : n = 1
  · subst h1; simp [g2]
  · by_cases h2 : n = 2
    · subst h2; simp [g2]
    · simp [g2, h1, h2]

theorem z2_add_self (c : ZMod 2) : c + c = 0 := by
  revert c; decide

theorem ps_add_self (w : PowerSeries (ZMod 2)) : w + w = 0 := by
  ext n
  rw [map_add, map_zero]
  exact z2_add_self _

theorem frob (j : ℕ) : (PowerSeries.X + PowerSeries.X ^ 2 : PowerSeries (ZMod 2)) ^ (2 ^ j) =
    PowerSeries.X ^ (2 ^ j) + PowerSeries.X ^ (2 ^ (j + 1)) := by
  induction j with
  | zero => ring
  | succ j ih =>
    have hs : ∀ u v : PowerSeries (ZMod 2), (u + v) ^ 2 = u ^ 2 + v ^ 2 := fun u v => by
      linear_combination ps_add_self (u * v)
    rw [pow_succ (2 : ℕ) j,
      pow_mul (PowerSeries.X + PowerSeries.X ^ 2 : PowerSeries (ZMod 2)) (2 ^ j) 2, ih, hs,
      pow_succ (2 : ℕ) (j + 1), pow_succ (2 : ℕ) j]
    generalize (2 : ℕ) ^ j = N
    ring

open Classical in
noncomputable def pw (n : ℕ) : ZMod 2 := if ∃ j, n = 2 ^ j then 1 else 0

theorem pw_one_iff (n : ℕ) : pw n = 1 ↔ ∃ j, n = 2 ^ j := by
  unfold pw
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (by decide) h

theorem pw_of {n : ℕ} (h : ∃ j, n = 2 ^ j) : pw n = 1 := by
  unfold pw; rw [if_pos h]

theorem pw_not {n : ℕ} (h : ¬ ∃ j, n = 2 ^ j) : pw n = 0 := by
  unfold pw; rw [if_neg h]

theorem pw_one : pw 1 = 1 := pw_of ⟨0, by norm_num⟩

theorem pw_zero : pw 0 = 0 :=
  pw_not (fun ⟨j, hj⟩ => (pow_pos (by norm_num : (0 : ℕ) < 2) j).ne hj)

theorem pw_double (m : ℕ) : pw (2 * m) = pw m := by
  have hiff : (∃ j, 2 * m = 2 ^ j) ↔ (∃ j, m = 2 ^ j) := by
    constructor
    · rintro ⟨j, hj⟩
      rcases j with _ | j
      · rw [pow_zero] at hj; omega
      · rw [pow_succ'] at hj; exact ⟨j, by omega⟩
    · rintro ⟨j, hj⟩
      exact ⟨j + 1, by rw [hj, pow_succ']⟩
  by_cases hm : ∃ j, m = 2 ^ j
  · rw [pw_of hm, pw_of (hiff.mpr hm)]
  · rw [pw_not hm, pw_not (fun h => hm (hiff.mp h))]

theorem pw_odd (m : ℕ) (hm : 0 < m) : pw (2 * m + 1) = 0 := by
  apply pw_not
  rintro ⟨j, hj⟩
  rcases j with _ | j
  · rw [pow_zero] at hj; omega
  · rw [pow_succ'] at hj; omega

theorem term (k n : ℕ) : pw k * powSeq g2 k n =
    (if n = k then pw k else 0) + (if n = 2 * k then pw k else 0) := by
  by_cases h : ∃ j, k = 2 ^ j
  · obtain ⟨j, rfl⟩ := h
    rw [pow_ps, mk_g2, frob, map_add, PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow,
      pow_succ']
    split_ifs <;> ring
  · rw [pw_not h]
    simp

theorem comp_pw (n : ℕ) : comp pw g2 n = if n = 1 then 1 else 0 := by
  have hs : comp pw g2 n = ∑ k ∈ Finset.range (n + 1),
      ((if n = k then pw k else 0) + (if n = 2 * k then pw k else 0)) :=
    Finset.sum_congr rfl (fun k _ => term k n)
  rw [hs, Finset.sum_add_distrib, Finset.sum_ite_eq,
    if_pos (Finset.self_mem_range_succ n)]
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have e : ∀ k, (if 2 * m = 2 * k then pw k else 0) = if m = k then pw k else 0 := by
      intro k
      by_cases hk : m = k
      · rw [if_pos (show 2 * m = 2 * k by omega), if_pos hk]
      · rw [if_neg (show ¬ (2 * m = 2 * k) by omega), if_neg hk]
    simp only [e]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (by omega : m < 2 * m + 1)), pw_double,
      if_neg (by omega : ¬ (2 * m = 1))]
    exact z2_add_self _
  · have e : ∀ k, (if 2 * m + 1 = 2 * k then pw k else 0) = 0 := fun k => if_neg (by omega)
    simp only [e, Finset.sum_const_zero, add_zero]
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp [pw_one]
    · rw [pw_odd m h, if_neg (by omega : ¬ (2 * m + 1 = 1))]

theorem inner2 (a : ℕ → ℤ) (m : ℕ) (h : ∀ j ≤ m, ((a j : ℤ) : ZMod 2) = pw j) :
    ∀ j ≤ m + 1, ((innerSeq a j : ℤ) : ZMod 2) = g2 j := by
  intro j hj
  match j, hj with
  | 0, _ => simp [innerSeq, g2]
  | 1, _ => simp [innerSeq, g2]
  | 2, hj =>
    have e : innerSeq a 2 = -(4 : ℤ) ^ 0 * a 1 := rfl
    rw [e]
    push_cast
    rw [h 1 (by omega), pw_one]
    decide
  | i + 3, hj =>
    have e : innerSeq a (i + 3) = -(4 : ℤ) ^ (i + 1) * a (i + 2) := rfl
    have h4 : (4 : ZMod 2) = 0 := by decide
    rw [e]
    push_cast
    rw [h4, zero_pow (by omega : i + 1 ≠ 0)]
    simp [g2]

theorem mod2 (a : ℕ → ℤ) (ha0 : a 0 = 0)
    (hc : ∀ n : ℕ, comp a (innerSeq a) n = if n = 1 then 1 else 0) :
    ∀ n, ((a n : ℤ) : ZMod 2) = pw n :=
  uniq (fun i => ((a i : ℤ) : ZMod 2)) (fun i => ((innerSeq a i : ℤ) : ZMod 2)) pw g2
    (fun n => by rw [cast_comp 2 a hc n, comp_pw n]) (by simp [ha0, pw_zero])
    (by simp [g2]) (by simp [g2]) (inner2 a)

end R393856

theorem OMA.solution : type_of% @OMA.S_oeis_a393856.main := by
  intro a ha0 hc n hn
  constructor
  · have h := R393856.mod5 a ha0 hc n
    have hn0 : n ≠ 0 := by omega
    have h1 : R393856.cm (1 : ZMod 5) n = 1 := by simp [R393856.cm, hn0]
    rw [h1, ← Int.cast_one] at h
    have h2 := (ZMod.intCast_eq_intCast_iff (a n) 1 5).mp h
    exact_mod_cast h2
  · rw [← ZMod.intCast_eq_one_iff_odd, R393856.mod2 a ha0 hc n]
    exact R393856.pw_one_iff n
