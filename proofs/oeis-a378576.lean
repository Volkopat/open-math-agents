import OMAStatements.S_oeis_a378576
import Mathlib

namespace R378576
open OMA.S_oeis_a378576

theorem pow_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (g : ℕ → R) :
    ∀ k n, f (powSeq g k n) = powSeq (fun i => f (g i)) k n := by
  intro k
  induction k with
  | zero => intro n; simp only [powSeq]; split_ifs <;> simp
  | succ k ih => intro n; simp only [powSeq, map_sum, map_mul, ih]

theorem cmp_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (u g : ℕ → R) (n : ℕ) :
    f (comp u g n) = comp (fun i => f (u i)) (fun i => f (g i)) n := by
  simp only [comp, map_sum, map_mul, pow_map]

theorem it_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (u : ℕ → R) :
    ∀ r n, f (iterComp u r n) = iterComp (fun i => f (u i)) r n := by
  intro r
  induction r with
  | zero => intro n; simp only [iterComp]; split_ifs <;> simp
  | succ r ih => intro n; simp only [iterComp, cmp_map, ih]

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

theorem cmp_congr {R : Type*} [CommRing R] (u u' g g' : ℕ → R) (N : ℕ)
    (hu : ∀ j ≤ N, u j = u' j) (hg : ∀ j ≤ N, g j = g' j) :
    ∀ n, n ≤ N → comp u g n = comp u' g' n := by
  intro n hn
  simp only [comp]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [hu k (le_trans hk' hn), pow_congr g g' N hg k n hn]

theorem it_congr {R : Type*} [CommRing R] (u u' : ℕ → R) (N : ℕ)
    (hu : ∀ j ≤ N, u j = u' j) : ∀ r n, n ≤ N → iterComp u r n = iterComp u' r n := by
  intro r
  induction r with
  | zero => intro n _; simp only [iterComp]
  | succ r ih =>
    intro n hn
    simp only [iterComp]
    exact cmp_congr u u' _ _ N hu ih n hn

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

theorem it_cm {R : Type*} [CommRing R] :
    ∀ (r : ℕ) n, iterComp (cm (1 : R)) r n = cm (r : R) n := by
  intro r
  induction r with
  | zero =>
    intro n
    rcases n with _ | n
    · simp [iterComp, cm]
    · simp [iterComp, cm, zero_pow_eq]
  | succ r ih =>
    intro n
    have hf : iterComp (cm (1 : R)) r = cm (r : R) := funext ih
    show comp (cm (1 : R)) (iterComp (cm (1 : R)) r) n = _
    rw [hf, cmp_cm, Nat.cast_succ]

theorem cast_eq (a : ℕ → ℤ) (ha0 : a 0 = 0)
    (hrec : ∀ n : ℕ, a (n + 1) = (if n = 0 then 1 else 0) + iterComp a 6 n) :
    ∀ n, ((a n : ℤ) : ZMod 5) = cm (1 : ZMod 5) n := by
  have hr : ((6 : ℕ) : ZMod 5) = 1 := by decide
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp [ha0, cm]
    · rw [hrec n]
      push_cast
      have hm := it_map (Int.castRingHom (ZMod 5)) a 6 n
      simp only [eq_intCast] at hm
      rw [hm, it_congr (fun i => ((a i : ℤ) : ZMod 5)) (cm 1) n (fun j hj => ih j (by omega))
        6 n le_rfl, it_cm, hr, cm_succ, one_mul]

end R378576

theorem OMA.solution : type_of% @OMA.S_oeis_a378576.main := by
  intro a ha0 hrec n hn
  have h := R378576.cast_eq a ha0 hrec n
  have hn0 : n ≠ 0 := by omega
  have h1 : R378576.cm (1 : ZMod 5) n = 1 := by simp [R378576.cm, hn0]
  rw [h1, ← Int.cast_one] at h
  have h2 := (ZMod.intCast_eq_intCast_iff (a n) 1 5).mp h
  exact_mod_cast h2
