import OMAStatements.S_oeis_a338184
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a338184

open OMA.S_oeis_a338184

/-! ### Part 1: Basic power-series & `Ring.inverse` helpers -/

private lemma four_eq_zero_ps : (4 : PowerSeries (ZMod 4)) = 0 := by
  change PowerSeries.C (4 : ZMod 4) = 0
  rw [show (4 : ZMod 4) = 0 by decide, map_zero]

private lemma isUnit_of_constantCoeff_one {R : Type*} [CommRing R] {f : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 1) : IsUnit f := by
  rw [PowerSeries.isUnit_iff_constantCoeff, hf]
  exact isUnit_one

private lemma isUnit_prod_one_add {R : Type*} [CommRing R] (A : PowerSeries R) (n : ℕ) :
    IsUnit (∏ k ∈ Finset.range n, (1 + PowerSeries.X ^ (k + 1) * A)) := by
  apply isUnit_of_constantCoeff_one
  rw [map_prod]
  apply Finset.prod_eq_one
  intro k _
  simp [map_add, map_mul, map_pow, PowerSeries.constantCoeff_X]

private lemma coeff_X_pow_mul_zero_of_lt {R : Type*} [CommRing R] (k : ℕ) (f : PowerSeries R)
    {m : ℕ} (hm : m < k) : PowerSeries.coeff m (PowerSeries.X ^ k * f) = 0 := by
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.mem_antidiagonal] at hp
  rw [PowerSeries.coeff_X_pow, if_neg (by omega), zero_mul]

private lemma coeff_mul_X_pow_zero_of_lt {R : Type*} [CommRing R] (k : ℕ) (f g : PowerSeries R)
    {m : ℕ} (hm : m < k) : PowerSeries.coeff m (f * PowerSeries.X ^ k * g) = 0 := by
  rw [show f * PowerSeries.X ^ k * g = PowerSeries.X ^ k * (f * g) by ring]
  exact coeff_X_pow_mul_zero_of_lt k (f * g) hm

/-! ### Part 2: Telescoping identity in `PowerSeries ℤ` -/

private noncomputable def Tterm {R : Type*} [CommRing R] (A : PowerSeries R) (n : ℕ) :
    PowerSeries R :=
  (-1 : PowerSeries R) ^ n * PowerSeries.X ^ (n * (n + 1) / 2) * A ^ n *
    Ring.inverse (∏ k ∈ Finset.range n, (1 + PowerSeries.X ^ (k + 1) * A))

private lemma Tterm_zero {R : Type*} [CommRing R] (A : PowerSeries R) :
    Tterm A 0 = 1 := by
  simp [Tterm]

private lemma Tterm_telescope {R : Type*} [CommRing R] (A : PowerSeries R) (n : ℕ) :
    A * (Tterm A n + Tterm A (n + 1)) =
      (-1 : PowerSeries R) ^ n * PowerSeries.X ^ (n * (n + 1) / 2) * A ^ (n + 1) *
        Ring.inverse (∏ k ∈ Finset.range (n + 1), (1 + PowerSeries.X ^ (k + 1) * A)) := by
  let P_n : PowerSeries R := ∏ k ∈ Finset.range n, (1 + PowerSeries.X ^ (k + 1) * A)
  let F : PowerSeries R := 1 + PowerSeries.X ^ (n + 1) * A
  let P_s : PowerSeries R := ∏ k ∈ Finset.range (n + 1), (1 + PowerSeries.X ^ (k + 1) * A)
  have hPs : P_s = P_n * F := Finset.prod_range_succ _ n
  have hPn_u : IsUnit P_n := isUnit_prod_one_add A n
  have hF_u : IsUnit F := by
    apply isUnit_of_constantCoeff_one
    simp [F, map_add, map_mul, map_pow, PowerSeries.constantCoeff_X]
  have hPs_u : IsUnit P_s := isUnit_prod_one_add A (n + 1)
  have hinv_n : Ring.inverse P_n = F * Ring.inverse P_s := by
    apply hPn_u.mul_left_cancel
    rw [Ring.mul_inverse_cancel _ hPn_u, ← mul_assoc, ← hPs, Ring.mul_inverse_cancel _ hPs_u]
  have htri : (n + 1) * (n + 1 + 1) / 2 = n * (n + 1) / 2 + (n + 1) := by
    have h1 : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
    rw [h1, Nat.add_mul_div_left _ _ (by omega)]
  have hTn : Tterm A n =
      (-1 : PowerSeries R) ^ n * PowerSeries.X ^ (n * (n + 1) / 2) * A ^ n *
        F * Ring.inverse P_s := by
    dsimp [Tterm]
    change (-1 : PowerSeries R) ^ n * PowerSeries.X ^ (n * (n + 1) / 2) * A ^ n * Ring.inverse P_n = _
    rw [hinv_n]; ring
  have hTs : Tterm A (n + 1) =
      -((-1 : PowerSeries R) ^ n * PowerSeries.X ^ (n * (n + 1) / 2) * A ^ n *
        (PowerSeries.X ^ (n + 1) * A) * Ring.inverse P_s) := by
    dsimp [Tterm]
    rw [htri, pow_add, pow_succ, pow_succ]
    ring
  rw [hTn, hTs]
  have hFsub : F - PowerSeries.X ^ (n + 1) * A = 1 := by dsimp [F]; ring
  calc A * ((-1 : PowerSeries R) ^ n * PowerSeries.X ^ (n * (n + 1) / 2) * A ^ n * F * Ring.inverse P_s +
            -((-1 : PowerSeries R) ^ n * PowerSeries.X ^ (n * (n + 1) / 2) * A ^ n *
              (PowerSeries.X ^ (n + 1) * A) * Ring.inverse P_s))
      = (-1 : PowerSeries R) ^ n * PowerSeries.X ^ (n * (n + 1) / 2) * A ^ (n + 1) *
          (F - PowerSeries.X ^ (n + 1) * A) * Ring.inverse P_s := by ring
    _ = (-1 : PowerSeries R) ^ n * PowerSeries.X ^ (n * (n + 1) / 2) * A ^ (n + 1) *
          Ring.inverse P_s := by rw [hFsub, mul_one]

private noncomputable def Sseries {R : Type*} [CommRing R] (A : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun m =>
    ∑ n ∈ Finset.Icc 1 m, PowerSeries.coeff m (Tterm A n)

private lemma coeff_Tterm_zero_of_lt {R : Type*} [CommRing R] (A : PowerSeries R) {n m : ℕ}
    (hm : m < n * (n + 1) / 2) : PowerSeries.coeff m (Tterm A n) = 0 := by
  dsimp [Tterm]
  rw [show (-1 : PowerSeries R) ^ n * PowerSeries.X ^ (n * (n + 1) / 2) * A ^ n *
      Ring.inverse (∏ k ∈ Finset.range n, (1 + PowerSeries.X ^ (k + 1) * A)) =
      PowerSeries.X ^ (n * (n + 1) / 2) *
        ((-1 : PowerSeries R) ^ n * A ^ n *
          Ring.inverse (∏ k ∈ Finset.range n, (1 + PowerSeries.X ^ (k + 1) * A))) by ring]
  exact coeff_X_pow_mul_zero_of_lt _ _ hm

private lemma rhsSeries_eq_mul_one_add_two_S (A : PowerSeries ℤ) :
    rhsSeries A = A * (1 + 2 * Sseries A) := by
  ext m
  rw [rhsSeries, PowerSeries.coeff_mk]
  have hsum :
      ∑ n ∈ Finset.range (m + 1),
        PowerSeries.coeff m
          ((-1 : PowerSeries ℤ) ^ n * PowerSeries.X ^ (n * (n + 1) / 2) * A ^ (n + 1) *
            Ring.inverse (∏ k ∈ Finset.range (n + 1), (1 + PowerSeries.X ^ (k + 1) * A))) =
      PowerSeries.coeff m (A * (∑ n ∈ Finset.range (m + 1), (Tterm A n + Tterm A (n + 1)))) := by
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Tterm_telescope]
  rw [hsum]
  have htel :
      ∑ n ∈ Finset.range (m + 1), (Tterm A n + Tterm A (n + 1)) =
      1 + 2 * (∑ n ∈ Finset.Icc 1 m, Tterm A n) + Tterm A (m + 1) := by
    rw [Finset.sum_add_distrib]
    have h1 : ∑ n ∈ Finset.range (m + 1), Tterm A n =
        Tterm A 0 + ∑ n ∈ Finset.Icc 1 m, Tterm A n := by
      have hr : Finset.range (m + 1) = insert 0 (Finset.Icc 1 m) := by
        ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      rw [hr, Finset.sum_insert (by simp)]
    have h2 : ∑ n ∈ Finset.range (m + 1), Tterm A (n + 1) =
        (∑ n ∈ Finset.Icc 1 m, Tterm A n) + Tterm A (m + 1) := by
      rw [Finset.sum_range_succ]
      congr 1
      have hr : Finset.Icc 1 m = (Finset.range m).image (fun n => n + 1) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
        constructor
        · intro ⟨h1, h2⟩; exact ⟨k - 1, by omega, by omega⟩
        · rintro ⟨a, ha, rfl⟩; omega
      rw [hr, Finset.sum_image (by intro a _ b _ h; dsimp at h; omega)]
    rw [h1, h2, Tterm_zero]; ring
  rw [htel, mul_add, map_add]
  have hlast : PowerSeries.coeff m (A * Tterm A (m + 1)) = 0 := by
    have htri : m < (m + 1) * (m + 1 + 1) / 2 := by
      have : 2 * m + 1 < (m + 1) * (m + 1 + 1) := by nlinarith
      omega
    rw [PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.mem_antidiagonal] at hp
    rw [coeff_Tterm_zero_of_lt A (by omega : p.2 < (m + 1) * (m + 1 + 1) / 2), mul_zero]
  rw [hlast, add_zero, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  congr 1
  rw [map_add, map_add,
    show (2 : PowerSeries ℤ) = PowerSeries.C (2 : ℤ) from rfl,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, Sseries, PowerSeries.coeff_mk, map_sum]
  congr 2
  symm
  refine Finset.sum_subset (Finset.Icc_subset_Icc_right (by omega : p.2 ≤ m)) fun n hn hnot => ?_
  simp only [Finset.mem_Icc] at hn hnot
  have hgt : p.2 < n := by omega
  have htri : p.2 < n * (n + 1) / 2 := by
    have : 2 * n ≤ n * (n + 1) := by nlinarith
    omega
  exact coeff_Tterm_zero_of_lt A htri

/-! ### Part 3: Reduction to `(ZMod 4)⟦X⟧` and collapse of `2 * Sseries` -/

private lemma map_ring_inverse {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {u : R} (hu : IsUnit u) : φ (Ring.inverse u) = Ring.inverse (φ u) := by
  have hfu : IsUnit (φ u) := hu.map φ
  apply hfu.mul_left_cancel
  rw [← map_mul, Ring.mul_inverse_cancel _ hu, map_one, Ring.mul_inverse_cancel _ hfu]

private lemma map_Tterm {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (A : PowerSeries R) (n : ℕ) :
    PowerSeries.map φ (Tterm A n) = Tterm (PowerSeries.map φ A) n := by
  dsimp [Tterm]
  rw [map_mul, map_mul, map_mul, map_pow, map_neg, map_one, map_pow, PowerSeries.map_X, map_pow,
    map_ring_inverse (PowerSeries.map φ) (isUnit_prod_one_add A n), map_prod]
  congr 2
  apply Finset.prod_congr rfl
  intro k _
  simp [map_add, map_mul, map_pow, PowerSeries.map_X]

private lemma map_Sseries {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (A : PowerSeries R) :
    PowerSeries.map φ (Sseries A) = Sseries (PowerSeries.map φ A) := by
  ext m
  rw [PowerSeries.coeff_map, Sseries, Sseries, PowerSeries.coeff_mk, PowerSeries.coeff_mk, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← PowerSeries.coeff_map, map_Tterm]

private lemma two_mul_inverse_add_two {u v : PowerSeries (ZMod 4)}
    (hu : IsUnit u) (huv : IsUnit (u + 2 * v)) :
    2 * Ring.inverse (u + 2 * v) = 2 * Ring.inverse u := by
  apply hu.mul_left_cancel
  have h1 : u * (2 * Ring.inverse (u + 2 * v)) = 2 * ((u + 2 * v) * Ring.inverse (u + 2 * v)) := by
    calc u * (2 * Ring.inverse (u + 2 * v))
        = 2 * ((u + 2 * v) * Ring.inverse (u + 2 * v)) - 4 * (v * Ring.inverse (u + 2 * v)) := by ring
      _ = 2 * ((u + 2 * v) * Ring.inverse (u + 2 * v)) - 0 * (v * Ring.inverse (u + 2 * v)) := by
            rw [four_eq_zero_ps]
      _ = 2 * ((u + 2 * v) * Ring.inverse (u + 2 * v)) := by ring
  rw [h1, Ring.mul_inverse_cancel _ huv, mul_one]
  calc (2 : PowerSeries (ZMod 4))
      = 2 * (u * Ring.inverse u) := by rw [Ring.mul_inverse_cancel _ hu, mul_one]
    _ = u * (2 * Ring.inverse u) := by ring

private lemma two_mul_Tterm_add_two (P : PowerSeries (ZMod 4)) (n : ℕ) :
    2 * Tterm (1 + 2 * P) n = 2 * Tterm (1 : PowerSeries (ZMod 4)) n := by
  have hpow : ∀ k : ℕ, 2 * (1 + 2 * P) ^ k = 2 * (1 : PowerSeries (ZMod 4)) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ r ih =>
      calc 2 * (1 + 2 * P) ^ (r + 1)
          = (2 * (1 + 2 * P) ^ r) * (1 + 2 * P) := by ring
        _ = (2 * (1 : PowerSeries (ZMod 4)) ^ r) * (1 + 2 * P) := by rw [ih]
        _ = 2 * (1 : PowerSeries (ZMod 4)) ^ (r + 1) + 4 * P := by ring
        _ = 2 * (1 : PowerSeries (ZMod 4)) ^ (r + 1) + 0 * P := by rw [four_eq_zero_ps]
        _ = 2 * (1 : PowerSeries (ZMod 4)) ^ (r + 1) := by ring
  have hprod : ∃ V : PowerSeries (ZMod 4),
      (∏ k ∈ Finset.range n, (1 + PowerSeries.X ^ (k + 1) * (1 + 2 * P))) =
      (∏ k ∈ Finset.range n, (1 + PowerSeries.X ^ (k + 1) * (1 : PowerSeries (ZMod 4)))) + 2 * V := by
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ r ih =>
      rcases ih with ⟨V, hV⟩
      rw [Finset.prod_range_succ, Finset.prod_range_succ, hV]
      refine ⟨V * (1 + PowerSeries.X ^ (r + 1)) +
        (∏ k ∈ Finset.range r, (1 + PowerSeries.X ^ (k + 1) * (1 : PowerSeries (ZMod 4)))) *
          (PowerSeries.X ^ (r + 1) * P) +
        2 * V * (PowerSeries.X ^ (r + 1) * P), ?_⟩
      ring
  rcases hprod with ⟨V, hV⟩
  have hinv :
      2 * Ring.inverse (∏ k ∈ Finset.range n, (1 + PowerSeries.X ^ (k + 1) * (1 + 2 * P))) =
      2 * Ring.inverse (∏ k ∈ Finset.range n, (1 + PowerSeries.X ^ (k + 1) * (1 : PowerSeries (ZMod 4)))) := by
    rw [hV]
    exact two_mul_inverse_add_two (isUnit_prod_one_add (1 : PowerSeries (ZMod 4)) n)
      (by rw [← hV]; exact isUnit_prod_one_add (1 + 2 * P) n)
  dsimp [Tterm]
  have h1 : 2 * ((1 + 2 * P) ^ n *
      Ring.inverse (∏ k ∈ Finset.range n, (1 + PowerSeries.X ^ (k + 1) * (1 + 2 * P)))) =
      2 * ((1 : PowerSeries (ZMod 4)) ^ n *
      Ring.inverse (∏ k ∈ Finset.range n, (1 + PowerSeries.X ^ (k + 1) * (1 : PowerSeries (ZMod 4))))) := by
    have hpow' : ∀ k : ℕ, ∃ W : PowerSeries (ZMod 4), (1 + 2 * P) ^ k = 1 + 2 * W := by
      intro k
      induction k with
      | zero => exact ⟨0, by simp⟩
      | succ r ih =>
        rcases ih with ⟨W, hW⟩
        rw [pow_succ, hW]
        exact ⟨W + P + 2 * W * P, by ring⟩
    rcases hpow' n with ⟨W, hW⟩
    rw [hW, one_pow, one_mul]
    calc 2 * ((1 + 2 * W) * Ring.inverse (∏ k ∈ Finset.range n, (1 + PowerSeries.X ^ (k + 1) * (1 + 2 * P))))
        = 2 * Ring.inverse (∏ k ∈ Finset.range n, (1 + PowerSeries.X ^ (k + 1) * (1 + 2 * P))) +
          4 * (W * Ring.inverse (∏ k ∈ Finset.range n, (1 + PowerSeries.X ^ (k + 1) * (1 + 2 * P)))) := by ring
      _ = 2 * Ring.inverse (∏ k ∈ Finset.range n, (1 + PowerSeries.X ^ (k + 1) * (1 + 2 * P))) +
          0 * (W * Ring.inverse (∏ k ∈ Finset.range n, (1 + PowerSeries.X ^ (k + 1) * (1 + 2 * P)))) := by
            rw [four_eq_zero_ps]
      _ = 2 * Ring.inverse (∏ k ∈ Finset.range n, (1 + PowerSeries.X ^ (k + 1) * (1 : PowerSeries (ZMod 4)))) := by
            rw [zero_mul, add_zero, hinv]
  calc 2 * ((-1 : PowerSeries (ZMod 4)) ^ n * PowerSeries.X ^ (n * (n + 1) / 2) * (1 + 2 * P) ^ n *
          Ring.inverse (∏ k ∈ Finset.range n, (1 + PowerSeries.X ^ (k + 1) * (1 + 2 * P))))
      = (-1 : PowerSeries (ZMod 4)) ^ n * PowerSeries.X ^ (n * (n + 1) / 2) *
          (2 * ((1 + 2 * P) ^ n *
            Ring.inverse (∏ k ∈ Finset.range n, (1 + PowerSeries.X ^ (k + 1) * (1 + 2 * P))))) := by ring
    _ = (-1 : PowerSeries (ZMod 4)) ^ n * PowerSeries.X ^ (n * (n + 1) / 2) *
          (2 * ((1 : PowerSeries (ZMod 4)) ^ n *
            Ring.inverse (∏ k ∈ Finset.range n, (1 + PowerSeries.X ^ (k + 1) * (1 : PowerSeries (ZMod 4)))))) := by
          rw [h1]
    _ = 2 * ((-1 : PowerSeries (ZMod 4)) ^ n * PowerSeries.X ^ (n * (n + 1) / 2) *
          (1 : PowerSeries (ZMod 4)) ^ n *
          Ring.inverse (∏ k ∈ Finset.range n, (1 + PowerSeries.X ^ (k + 1) * (1 : PowerSeries (ZMod 4))))) := by ring

private lemma two_mul_Sseries_add_two (P : PowerSeries (ZMod 4)) :
    2 * Sseries (1 + 2 * P) = 2 * Sseries (1 : PowerSeries (ZMod 4)) := by
  ext m
  change PowerSeries.coeff m (PowerSeries.C (2 : ZMod 4) * Sseries (1 + 2 * P)) =
         PowerSeries.coeff m (PowerSeries.C (2 : ZMod 4) * Sseries (1 : PowerSeries (ZMod 4)))
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, Sseries, Sseries,
    PowerSeries.coeff_mk, PowerSeries.coeff_mk, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have h := congrArg (PowerSeries.coeff m) (two_mul_Tterm_add_two P n)
  change PowerSeries.coeff m (PowerSeries.C (2 : ZMod 4) * Tterm (1 + 2 * P) n) =
         PowerSeries.coeff m (PowerSeries.C (2 : ZMod 4) * Tterm (1 : PowerSeries (ZMod 4)) n) at h
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul] at h
  exact h

/-! ### Part 4: Cauchy's `q`-binomial theorem in `(ZMod 2)⟦X⟧` and Euler's Pentagonal Theorem -/

private noncomputable def qFac (n : ℕ) : PowerSeries (ZMod 2) :=
  ∏ k ∈ Finset.range n, (1 - (PowerSeries.X : PowerSeries (ZMod 2)) ^ (k + 1))

private lemma isUnit_qFac (n : ℕ) : IsUnit (qFac n) := by
  apply isUnit_of_constantCoeff_one
  dsimp [qFac]
  rw [map_prod]
  apply Finset.prod_eq_one
  intro k _
  simp [map_sub, map_pow, PowerSeries.constantCoeff_X]

private noncomputable def qBinom (M n : ℕ) : PowerSeries (ZMod 2) :=
  if n ≤ M then qFac M * Ring.inverse (qFac n * qFac (M - n)) else 0

private lemma qBinom_zero (M : ℕ) : qBinom M 0 = 1 := by
  simp only [qBinom, Nat.zero_le, ↓reduceIte, Nat.sub_zero]
  have h0 : qFac 0 = 1 := by simp [qFac]
  rw [h0, one_mul, Ring.mul_inverse_cancel _ (isUnit_qFac M)]

private lemma qBinom_self (M : ℕ) : qBinom M M = 1 := by
  simp only [qBinom, le_refl, ↓reduceIte, Nat.sub_self]
  have h0 : qFac 0 = 1 := by simp [qFac]
  rw [h0, mul_one, Ring.mul_inverse_cancel _ (isUnit_qFac M)]

private lemma qBinom_pascal (M n : ℕ) (hn1 : 1 ≤ n) (hnM : n ≤ M) :
    qBinom (M + 1) n = qBinom M n + PowerSeries.X ^ (M + 1 - n) * qBinom M (n - 1) := by
  have h1 : n ≤ M + 1 := by omega
  have h2 : n - 1 ≤ M := by omega
  simp only [qBinom, h1, hnM, h2, ↓reduceIte]
  let X : PowerSeries (ZMod 2) := PowerSeries.X
  have hM1 : qFac (M + 1) = qFac M * (1 - X ^ (M + 1)) := Finset.prod_range_succ _ M
  have hMn : qFac (M + 1 - n) = qFac (M - n) * (1 - X ^ (M + 1 - n)) := by
    rw [show M + 1 - n = (M - n) + 1 by omega]
    exact Finset.prod_range_succ _ (M - n)
  have hnn : qFac n = qFac (n - 1) * (1 - X ^ n) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    dsimp [qFac]
    rw [Finset.prod_range_succ]
    simp [show n - 1 + 1 = n by omega, X]
  have hMn1 : M - (n - 1) = M + 1 - n := by omega
  have hu : IsUnit (qFac n * qFac (M + 1 - n)) := (isUnit_qFac n).mul (isUnit_qFac (M + 1 - n))
  apply hu.mul_right_cancel
  rw [mul_assoc, Ring.inverse_mul_cancel _ hu, mul_one, add_mul]
  have hterm1 : qFac M * Ring.inverse (qFac n * qFac (M - n)) * (qFac n * qFac (M + 1 - n)) =
      qFac M * (1 - X ^ (M + 1 - n)) := by
    rw [hMn]
    have hassoc : qFac M * Ring.inverse (qFac n * qFac (M - n)) *
        (qFac n * (qFac (M - n) * (1 - X ^ (M + 1 - n)))) =
        qFac M * (Ring.inverse (qFac n * qFac (M - n)) * (qFac n * qFac (M - n))) *
        (1 - X ^ (M + 1 - n)) := by ring
    rw [hassoc, Ring.inverse_mul_cancel _ ((isUnit_qFac n).mul (isUnit_qFac (M - n))), mul_one]
  have hterm2 : X ^ (M + 1 - n) * (qFac M * Ring.inverse (qFac (n - 1) * qFac (M - (n - 1)))) *
      (qFac n * qFac (M + 1 - n)) =
      X ^ (M + 1 - n) * qFac M * (1 - X ^ n) := by
    rw [hMn1]
    conv_lhs => rw [hnn]
    have hassoc : X ^ (M + 1 - n) * (qFac M * Ring.inverse (qFac (n - 1) * qFac (M + 1 - n))) *
        (qFac (n - 1) * (1 - X ^ n) * qFac (M + 1 - n)) =
        X ^ (M + 1 - n) * qFac M *
        (Ring.inverse (qFac (n - 1) * qFac (M + 1 - n)) * (qFac (n - 1) * qFac (M + 1 - n))) *
        (1 - X ^ n) := by ring
    rw [hassoc, Ring.inverse_mul_cancel _ ((isUnit_qFac (n - 1)).mul (isUnit_qFac (M + 1 - n))), mul_one]
  rw [hterm1, hterm2, hM1]
  have hexp : X ^ (M + 1 - n) * X ^ n = X ^ (M + 1) := by
    rw [← pow_add, show M + 1 - n + n = M + 1 by omega]
  calc qFac M * (1 - X ^ (M + 1))
      = qFac M * (1 - X ^ (M + 1 - n)) + X ^ (M + 1 - n) * qFac M -
          qFac M * (X ^ (M + 1 - n) * X ^ n) := by rw [hexp]; ring
    _ = qFac M * (1 - X ^ (M + 1 - n)) + X ^ (M + 1 - n) * qFac M * (1 - X ^ n) := by ring

private lemma cauchy_q_binom_poly (M : ℕ) :
    ∏ k ∈ Finset.range M,
      (1 + Polynomial.C ((PowerSeries.X : PowerSeries (ZMod 2)) ^ (k + 1)) * Polynomial.X) =
    ∑ n ∈ Finset.range (M + 1),
      Polynomial.C ((PowerSeries.X : PowerSeries (ZMod 2)) ^ (n * (n + 1) / 2) * qBinom M n) *
        Polynomial.X ^ n := by
  induction M with
  | zero => simp [qBinom_zero]
  | succ M ih =>
    rw [Finset.prod_range_succ, ih]
    apply Polynomial.ext
    intro n
    rw [mul_add, mul_one, Polynomial.coeff_add, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
    have hcoeff_sum : ∀ (K : ℕ) (f : ℕ → PowerSeries (ZMod 2)) (d : ℕ),
        ∑ i ∈ Finset.range (K + 1),
          (Polynomial.C (f i) * (Polynomial.X : Polynomial (PowerSeries (ZMod 2))) ^ i).coeff d =
        if d ≤ K then f d else 0 := by
      intro K f d
      simp_rw [Polynomial.coeff_C_mul_X_pow]
      by_cases hd : d ≤ K
      · rw [if_pos hd, Finset.sum_eq_single d]
        · simp
        · intro i _ hi; simp [Ne.symm hi]
        · intro hnot; exfalso; apply hnot; simp [Finset.mem_range]; omega
      · rw [if_neg hd]
        apply Finset.sum_eq_zero
        intro i hi
        rw [Finset.mem_range] at hi
        simp [show d ≠ i by omega]
    have h1 := hcoeff_sum M (fun i => (PowerSeries.X : PowerSeries (ZMod 2)) ^ (i * (i + 1) / 2) * qBinom M i) n
    have h2 :
        ((∑ i ∈ Finset.range (M + 1),
          Polynomial.C ((PowerSeries.X : PowerSeries (ZMod 2)) ^ (i * (i + 1) / 2) * qBinom M i) *
            Polynomial.X ^ i) *
         (Polynomial.C ((PowerSeries.X : PowerSeries (ZMod 2)) ^ (M + 1)) * Polynomial.X)).coeff n =
        if 1 ≤ n ∧ n ≤ M + 1 then
          (PowerSeries.X : PowerSeries (ZMod 2)) ^ (M + 1) *
            ((PowerSeries.X : PowerSeries (ZMod 2)) ^ ((n - 1) * n / 2) * qBinom M (n - 1))
        else 0 := by
      rw [Finset.sum_mul, Polynomial.finsetSum_coeff]
      have hterm : ∀ i : ℕ,
          Polynomial.C ((PowerSeries.X : PowerSeries (ZMod 2)) ^ (i * (i + 1) / 2) * qBinom M i) *
            Polynomial.X ^ i *
            (Polynomial.C ((PowerSeries.X : PowerSeries (ZMod 2)) ^ (M + 1)) * Polynomial.X) =
          Polynomial.C ((PowerSeries.X : PowerSeries (ZMod 2)) ^ (M + 1) *
            ((PowerSeries.X : PowerSeries (ZMod 2)) ^ (i * (i + 1) / 2) * qBinom M i)) *
            Polynomial.X ^ (i + 1) := by
        intro i; simp only [Polynomial.C_mul, pow_succ]; ring
      simp_rw [hterm, Polynomial.coeff_C_mul_X_pow]
      by_cases hn : 1 ≤ n ∧ n ≤ M + 1
      · rw [if_pos hn, Finset.sum_eq_single (n - 1)]
        · simp [show n - 1 + 1 = n by omega]
        · intro i _ hi; simp [show n ≠ i + 1 by omega]
        · intro hnot; exfalso; apply hnot; simp [Finset.mem_range]; omega
      · rw [if_neg hn]
        apply Finset.sum_eq_zero
        intro i hi
        rw [Finset.mem_range] at hi
        simp [show n ≠ i + 1 by omega]
    have h3 := hcoeff_sum (M + 1) (fun i => (PowerSeries.X : PowerSeries (ZMod 2)) ^ (i * (i + 1) / 2) * qBinom (M + 1) i) n
    rw [h1, h2, h3]
    by_cases hn0 : n = 0
    · subst hn0; simp [qBinom_zero]
    · by_cases hnM : n ≤ M
      · rw [if_pos hnM, if_pos ⟨by omega, by omega⟩, if_pos (by omega : n ≤ M + 1)]
        rw [qBinom_pascal M n (by omega) hnM,
          mul_add ((PowerSeries.X : PowerSeries (ZMod 2)) ^ (n * (n + 1) / 2))]
        congr 1
        have hexp : M + 1 + (n - 1) * n / 2 = n * (n + 1) / 2 + (M + 1 - n) := by
          have htri : n * (n + 1) / 2 = (n - 1) * n / 2 + n := by
            have h : n * (n + 1) = (n - 1) * n + 2 * n := by
              cases n with
              | zero => omega
              | succ r => simp only [Nat.add_sub_cancel]; ring
            rw [h, Nat.add_mul_div_left _ _ (by omega)]
          omega
        calc (PowerSeries.X : PowerSeries (ZMod 2)) ^ (M + 1) *
              (PowerSeries.X ^ ((n - 1) * n / 2) * qBinom M (n - 1))
            = PowerSeries.X ^ (M + 1 + (n - 1) * n / 2) * qBinom M (n - 1) := by
                rw [pow_add]; ring
          _ = PowerSeries.X ^ (n * (n + 1) / 2 + (M + 1 - n)) * qBinom M (n - 1) := by
                rw [hexp]
          _ = PowerSeries.X ^ (n * (n + 1) / 2) *
                (PowerSeries.X ^ (M + 1 - n) * qBinom M (n - 1)) := by
                rw [pow_add]; ring
      · by_cases hnEq : n = M + 1
        · subst hnEq
          rw [if_neg (by omega), zero_add, if_pos ⟨by omega, le_refl _⟩, if_pos (le_refl _),
            show M + 1 - 1 = M by omega, qBinom_self, qBinom_self, mul_one, mul_one]
          rw [← pow_add]
          congr 1
          have h : (M + 1) * (M + 1 + 1) = M * (M + 1) + 2 * (M + 1) := by ring
          rw [h, Nat.add_mul_div_left _ _ (by omega)]; omega
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), add_zero]

private lemma cauchy_q_binom_eval1 (M : ℕ) :
    qFac M = ∑ n ∈ Finset.range (M + 1),
      (PowerSeries.X : PowerSeries (ZMod 2)) ^ (n * (n + 1) / 2) * qBinom M n := by
  have h := congrArg (Polynomial.eval (1 : PowerSeries (ZMod 2))) (cauchy_q_binom_poly M)
  simp only [Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, mul_one, Polynomial.eval_finsetSum,
    Polynomial.eval_pow, one_pow] at h
  have hsign : ∀ k : ℕ,
      (1 : PowerSeries (ZMod 2)) + PowerSeries.X ^ (k + 1) =
      1 - PowerSeries.X ^ (k + 1) := by
    intro k
    ext m
    rw [map_add, map_sub]
    have h2 : ∀ a : ZMod 2, a = -a := by intro a; fin_cases a <;> rfl
    rw [sub_eq_add_neg, ← h2]
  dsimp [qFac]
  rw [← h]
  refine Finset.prod_congr rfl fun k _ => (hsign k).symm

private lemma coeff_qBinom_eq_inv_qFac {m M n : ℕ} (hM : m + n < M) :
    PowerSeries.coeff m (qBinom M n) = PowerSeries.coeff m (Ring.inverse (qFac n)) := by
  have hnM : n ≤ M := by omega
  simp only [qBinom, hnM, ↓reduceIte]
  have hfac : qFac M = qFac (M - n) * ∏ j ∈ Finset.range n,
      (1 - (PowerSeries.X : PowerSeries (ZMod 2)) ^ (M - n + j + 1)) := by
    dsimp [qFac]
    conv_lhs => rw [show M = (M - n) + n by omega]
    rw [Finset.prod_range_add]
  have hquot : qFac M * Ring.inverse (qFac n * qFac (M - n)) =
      Ring.inverse (qFac n) *
        ∏ j ∈ Finset.range n, (1 - (PowerSeries.X : PowerSeries (ZMod 2)) ^ (M - n + j + 1)) := by
    apply ((isUnit_qFac n).mul (isUnit_qFac (M - n))).mul_right_cancel
    rw [mul_assoc, Ring.inverse_mul_cancel _ ((isUnit_qFac n).mul (isUnit_qFac (M - n))), mul_one]
    have hassoc : Ring.inverse (qFac n) *
        (∏ j ∈ Finset.range n, (1 - (PowerSeries.X : PowerSeries (ZMod 2)) ^ (M - n + j + 1))) *
        (qFac n * qFac (M - n)) =
        (Ring.inverse (qFac n) * qFac n) *
        (qFac (M - n) * ∏ j ∈ Finset.range n,
          (1 - (PowerSeries.X : PowerSeries (ZMod 2)) ^ (M - n + j + 1))) := by ring
    rw [hassoc, Ring.inverse_mul_cancel _ (isUnit_qFac n), one_mul, ← hfac]
  rw [hquot]
  have hprod_id : ∀ r ≤ n, ∀ d ≤ m,
      PowerSeries.coeff d
        (∏ j ∈ Finset.range r, (1 - (PowerSeries.X : PowerSeries (ZMod 2)) ^ (M - n + j + 1))) =
      PowerSeries.coeff d (1 : PowerSeries (ZMod 2)) := by
    intro r
    induction r with
    | zero => intro _ d _; simp
    | succ r ihr =>
      intro hr d hd
      rw [Finset.prod_range_succ, mul_sub, mul_one, map_sub]
      have hzero : PowerSeries.coeff d
          ((∏ j ∈ Finset.range r, (1 - (PowerSeries.X : PowerSeries (ZMod 2)) ^ (M - n + j + 1))) *
            PowerSeries.X ^ (M - n + r + 1)) = 0 := by
        rw [mul_comm]
        exact coeff_X_pow_mul_zero_of_lt _ _ (by omega)
      rw [hzero, sub_zero]
      exact ihr (by omega) d hd
  rw [PowerSeries.coeff_mul]
  have h1 : ∑ p ∈ Finset.antidiagonal m,
      PowerSeries.coeff p.1 (Ring.inverse (qFac n)) *
      PowerSeries.coeff p.2
        (∏ j ∈ Finset.range n, (1 - (PowerSeries.X : PowerSeries (ZMod 2)) ^ (M - n + j + 1))) =
      ∑ p ∈ Finset.antidiagonal m,
      PowerSeries.coeff p.1 (Ring.inverse (qFac n)) *
      PowerSeries.coeff p.2 (1 : PowerSeries (ZMod 2)) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    rw [hprod_id n (le_refl _) p.2 (by omega)]
  rw [h1, ← PowerSeries.coeff_mul, mul_one]

private lemma coeff_Sseries_one_zmod2 (m : ℕ) (hm : 0 < m) :
    PowerSeries.coeff m (Sseries (1 : PowerSeries (ZMod 2))) =
    PowerSeries.coeff m (PowerSeries.pentagonalSeries (ZMod 2)) := by
  have hev := PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq (ZMod 2) m
  rw [Filter.eventually_atTop] at hev
  obtain ⟨s0, hs0⟩ := hev
  obtain ⟨M0, hM0⟩ : ∃ M0 : ℕ, s0 ⊆ Finset.range M0 := by
    refine ⟨s0.sup id + 1, fun x hx => ?_⟩
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hx)
  let M := max M0 (2 * m + 1)
  have hsub : s0 ⊆ Finset.range M := hM0.trans (Finset.range_mono (le_max_left _ _))
  have hpent : PowerSeries.coeff m (qFac M) =
      PowerSeries.coeff m (PowerSeries.pentagonalSeries (ZMod 2)) := hs0 (Finset.range M) hsub
  rw [← hpent, cauchy_q_binom_eval1 M, map_sum]
  rw [Sseries, PowerSeries.coeff_mk]
  have hzero0 : PowerSeries.coeff m ((PowerSeries.X : PowerSeries (ZMod 2)) ^ (0 * (0 + 1) / 2) * qBinom M 0) = 0 := by
    simp [qBinom_zero, PowerSeries.coeff_one, show m ≠ 0 by omega]
  have hsplit : Finset.range (M + 1) = insert 0 (Finset.Icc 1 M) := by
    ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hsplit, Finset.sum_insert (by simp), hzero0, zero_add]
  symm
  refine (Finset.sum_subset (Finset.Icc_subset_Icc_right (by omega : m ≤ M)) ?_).symm.trans ?_
  · intro n hn hnot
    simp only [Finset.mem_Icc] at hn hnot
    have htri : m < n * (n + 1) / 2 := by
      have : 2 * n ≤ n * (n + 1) := by nlinarith
      omega
    exact coeff_X_pow_mul_zero_of_lt _ _ htri
  · refine Finset.sum_congr rfl fun n hn => ?_
    simp only [Finset.mem_Icc] at hn
    dsimp [Tterm]
    have hsign : ∀ a : PowerSeries (ZMod 2), -a = a := by
      intro a; ext d; rw [map_neg]
      have h2 : ∀ c : ZMod 2, -c = c := by intro c; fin_cases c <;> rfl
      exact h2 _
    have hneg1 : (-1 : PowerSeries (ZMod 2)) ^ n = 1 := by
      rw [hsign, one_pow]
    have hprod : (∏ k ∈ Finset.range n, (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ (k + 1) * 1)) =
        qFac n := by
      dsimp [qFac]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [mul_one, sub_eq_add_neg, hsign]
    rw [hneg1, one_mul, one_pow, mul_one, hprod]
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    congr 1
    exact coeff_qBinom_eq_inv_qFac (by omega)

/-! ### Part 5: Bridge to `ℤ` mod 4 and `IsGenPentagonal` -/

private lemma isGenPentagonal_iff_mem_range (n : ℕ) :
    IsGenPentagonal n ↔ n ∈ Set.range pentagonal := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h2 := two_mul_natCast_pentagonal k
    omega
  · rintro ⟨k, rfl⟩
    exact ⟨k, two_mul_natCast_pentagonal k⟩

private lemma int_mod4_eq_of_zmod4 {x : ℤ} {r : ℤ} (hr0 : 0 ≤ r) (hr4 : r < 4)
    (h : (x : ZMod 4) = (r : ZMod 4)) : x % 4 = r := by
  have hdvd : ((4 : ℕ) : ℤ) ∣ (x - r) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact sub_eq_zero.mpr h
  obtain ⟨q, hq⟩ := hdvd
  push_cast at hq
  have hx : x = 4 * q + r := by linarith
  omega

end OMA.P_oeis_a338184

theorem OMA.solution : type_of% @OMA.S_oeis_a338184.main := by
  intro A hA n hn
  have hrel : A * (1 + 2 * OMA.P_oeis_a338184.Sseries A) = 1 := by
    rw [← OMA.P_oeis_a338184.rhsSeries_eq_mul_one_add_two_S, hA]
  let φ4 : ℤ →+* ZMod 4 := Int.castRingHom (ZMod 4)
  let Am : PowerSeries (ZMod 4) := PowerSeries.map φ4 A
  let Sm : PowerSeries (ZMod 4) := OMA.P_oeis_a338184.Sseries Am
  have hrel4 : Am * (1 + 2 * Sm) = 1 := by
    have hmap := congrArg (PowerSeries.map φ4) hrel
    simp only [map_mul, map_add, map_one, map_ofNat, OMA.P_oeis_a338184.map_Sseries] at hmap
    exact hmap
  have hAm_eq : Am = 1 + 2 * Sm := by
    have hinv : (1 + 2 * Sm) * (1 - 2 * Sm) = 1 := by
      calc (1 + 2 * Sm) * (1 - 2 * Sm) = 1 - 4 * Sm ^ 2 := by ring
        _ = 1 - 0 * Sm ^ 2 := by rw [OMA.P_oeis_a338184.four_eq_zero_ps]
        _ = 1 := by ring
    have h1 : Am = 1 - 2 * Sm := by
      calc Am = Am * 1 := by ring
        _ = Am * ((1 + 2 * Sm) * (1 - 2 * Sm)) := by rw [hinv]
        _ = (Am * (1 + 2 * Sm)) * (1 - 2 * Sm) := by ring
        _ = 1 * (1 - 2 * Sm) := by rw [hrel4]
        _ = 1 - 2 * Sm := by ring
    calc Am = 1 - 2 * Sm := h1
      _ = 1 + 2 * Sm - 4 * Sm := by ring
      _ = 1 + 2 * Sm - 0 * Sm := by rw [OMA.P_oeis_a338184.four_eq_zero_ps]
      _ = 1 + 2 * Sm := by ring
  have hAm_one : Am = 1 + 2 * OMA.P_oeis_a338184.Sseries (1 : PowerSeries (ZMod 4)) := by
    have hcoll := OMA.P_oeis_a338184.two_mul_Sseries_add_two Sm
    rw [← hAm_eq] at hcoll
    rw [hAm_eq, hcoll]
  -- Extract coefficient n > 0 in ZMod 4
  have hcoeff4 : ((PowerSeries.coeff n A : ℤ) : ZMod 4) =
      2 * PowerSeries.coeff n (OMA.P_oeis_a338184.Sseries (1 : PowerSeries (ZMod 4))) := by
    have h1 : ((PowerSeries.coeff n A : ℤ) : ZMod 4) = PowerSeries.coeff n Am := by
      rw [PowerSeries.coeff_map]; rfl
    rw [h1, hAm_one, map_add, PowerSeries.coeff_one, if_neg (by omega), zero_add]
    change PowerSeries.coeff n (PowerSeries.C (2 : ZMod 4) *
      OMA.P_oeis_a338184.Sseries (1 : PowerSeries (ZMod 4))) = _
    rw [PowerSeries.coeff_C_mul]
  -- Compare with mod-2 value via ZMod.castHom
  let π : ZMod 4 →+* ZMod 2 := ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)
  have hpi : ∀ x : ZMod 4, (2 : ZMod 4) * x = if π x = 0 then 0 else 2 := by
    intro x; fin_cases x <;> decide
  have hS2 : π (PowerSeries.coeff n (OMA.P_oeis_a338184.Sseries (1 : PowerSeries (ZMod 4)))) =
      PowerSeries.coeff n (PowerSeries.pentagonalSeries (ZMod 2)) := by
    rw [← PowerSeries.coeff_map, OMA.P_oeis_a338184.map_Sseries, map_one]
    exact OMA.P_oeis_a338184.coeff_Sseries_one_zmod2 n hn
  rw [hpi, hS2] at hcoeff4
  have hpent_iff : PowerSeries.coeff n (PowerSeries.pentagonalSeries (ZMod 2)) = 0 ↔
      ¬ OMA.S_oeis_a338184.IsGenPentagonal n := by
    rw [PowerSeries.coeff_pentagonalSeries_eq_zero_iff,
      OMA.P_oeis_a338184.isGenPentagonal_iff_mem_range]
  by_cases hp : OMA.S_oeis_a338184.IsGenPentagonal n
  · have hnz : PowerSeries.coeff n (PowerSeries.pentagonalSeries (ZMod 2)) ≠ 0 :=
      fun h => hpent_iff.mp h hp
    rw [if_neg hnz] at hcoeff4
    have hmod : PowerSeries.coeff n A % 4 = 2 :=
      OMA.P_oeis_a338184.int_mod4_eq_of_zmod4 (by omega) (by omega) hcoeff4
    exact ⟨⟨fun _ => hp, fun _ => hmod⟩, ⟨fun h0 => by omega, fun hnp => (hnp hp).elim⟩⟩
  · have hz : PowerSeries.coeff n (PowerSeries.pentagonalSeries (ZMod 2)) = 0 :=
      hpent_iff.mpr hp
    rw [if_pos hz] at hcoeff4
    have hmod : PowerSeries.coeff n A % 4 = 0 :=
      OMA.P_oeis_a338184.int_mod4_eq_of_zmod4 (by omega) (by omega) hcoeff4
    exact ⟨⟨fun h2 => by omega, fun h => (hp h).elim⟩, ⟨fun _ => hp, fun _ => hmod⟩⟩
