import OMAStatements.S_oeis_a393857
import Mathlib

namespace R393857
open OMA.S_oeis_a393857

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

theorem tgt_val (n : ℕ) :
    comp (cm (1 : ZMod 6)) (cm (-1 : ZMod 6)) n = if n = 1 then 1 else 0 := by
  have h0 : (-1 : ZMod 6) + 1 = 0 := by ring
  rw [cmp_cm, h0]
  rcases n with _ | _ | k
  · simp [cm]
  · simp [cm]
  · simp [cm, zero_pow_eq]

theorem inner_val (a : ℕ → ℤ) (m : ℕ)
    (h : ∀ j ≤ m, ((a j : ℤ) : ZMod 6) = cm (1 : ZMod 6) j) :
    ∀ j ≤ m + 1, ((innerSeq a j : ℤ) : ZMod 6) = cm (-1 : ZMod 6) j := by
  intro j hj
  match j, hj with
  | 0, _ => simp [innerSeq, cm]
  | 1, _ => simp [innerSeq, cm]
  | i + 2, hj =>
    have h5 : (5 : ZMod 6) = -1 := by decide
    have hi : ((a (i + 1) : ℤ) : ZMod 6) = 1 := by
      rw [h (i + 1) (by omega), cm_s, one_pow]
    have hc : cm (-1 : ZMod 6) (i + 2) = (-1) ^ (i + 1) := cm_s (-1) (i + 1)
    rw [hc]
    simp only [innerSeq]
    push_cast
    rw [hi, h5]
    ring

theorem cast_eq (a : ℕ → ℤ) (ha0 : a 0 = 0)
    (hc : ∀ n : ℕ, comp a (innerSeq a) n = if n = 1 then 1 else 0) :
    ∀ n, ((a n : ℤ) : ZMod 6) = cm (1 : ZMod 6) n := by
  have hE : ∀ n, comp (fun i => ((a i : ℤ) : ZMod 6)) (fun i => ((innerSeq a i : ℤ) : ZMod 6)) n
      = if n = 1 then 1 else 0 := by
    intro n
    have hh := congrArg (Int.castRingHom (ZMod 6)) (hc n)
    rw [cmp_map] at hh
    simp only [eq_intCast] at hh
    rw [hh]
    split_ifs <;> simp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · simp [ha0, cm]
    · have hag : ∀ j ≤ m, ((a j : ℤ) : ZMod 6) = cm (1 : ZMod 6) j :=
        fun j hj => ih j (by omega)
      have hg := inner_val a m hag
      have hP := pow_congr (fun i => ((innerSeq a i : ℤ) : ZMod 6)) (cm (-1 : ZMod 6)) (m + 1) hg
      have hd : powSeq (cm (-1 : ZMod 6)) (m + 1) (m + 1) = 1 :=
        pow_diag _ (cm_zero _) (by simp [cm]) (m + 1)
      have e1 : comp (fun i => ((a i : ℤ) : ZMod 6)) (fun i => ((innerSeq a i : ℤ) : ZMod 6))
          (m + 1) = ∑ k ∈ Finset.range (m + 1), ((a k : ℤ) : ZMod 6) *
            powSeq (fun i => ((innerSeq a i : ℤ) : ZMod 6)) k (m + 1) +
          ((a (m + 1) : ℤ) : ZMod 6) *
            powSeq (fun i => ((innerSeq a i : ℤ) : ZMod 6)) (m + 1) (m + 1) :=
        Finset.sum_range_succ _ _
      have e2 : comp (cm (1 : ZMod 6)) (cm (-1 : ZMod 6)) (m + 1) =
          ∑ k ∈ Finset.range (m + 1), cm (1 : ZMod 6) k * powSeq (cm (-1 : ZMod 6)) k (m + 1) +
          cm (1 : ZMod 6) (m + 1) * powSeq (cm (-1 : ZMod 6)) (m + 1) (m + 1) :=
        Finset.sum_range_succ _ _
      have hS : ∑ k ∈ Finset.range (m + 1), ((a k : ℤ) : ZMod 6) *
            powSeq (fun i => ((innerSeq a i : ℤ) : ZMod 6)) k (m + 1) =
          ∑ k ∈ Finset.range (m + 1), cm (1 : ZMod 6) k * powSeq (cm (-1 : ZMod 6)) k (m + 1) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hag k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)), hP k (m + 1) le_rfl]
      have h1 := hE (m + 1)
      have h2 := tgt_val (m + 1)
      rw [hP (m + 1) (m + 1) le_rfl, hd] at e1
      rw [hd] at e2
      linear_combination -e1 + e2 + h1 - h2 - hS

end R393857

theorem OMA.solution : type_of% @OMA.S_oeis_a393857.main := by
  intro a ha0 hc n hn
  have h := R393857.cast_eq a ha0 hc n
  have hn0 : n ≠ 0 := by omega
  have h1 : R393857.cm (1 : ZMod 6) n = 1 := by simp [R393857.cm, hn0]
  rw [h1, ← Int.cast_one] at h
  have h2 := (ZMod.intCast_eq_intCast_iff (a n) 1 6).mp h
  exact_mod_cast h2
