import OMAStatements.S_oeis_a363560
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OeisA363560Proof

open OMA.S_oeis_a363560

private lemma three_eq_zero_ps3 : (3 : PowerSeries (ZMod 3)) = 0 := by
  ext k; rw [show (3 : PowerSeries (ZMod 3)) = PowerSeries.C 3 from rfl, PowerSeries.coeff_C]
  split_ifs <;> simp [show (3 : ZMod 3) = 0 by decide]

private lemma coeff_X_mul_ps {R : Type*} [CommRing R] (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X * f) = if n = 0 then 0 else PowerSeries.coeff (n - 1) f := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (PowerSeries.X : PowerSeries R) * PowerSeries.coeff j f)]
  cases n with
  | zero => simp [PowerSeries.coeff_X]
  | succ n =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [Finset.sum_eq_single 1]
    · simp [PowerSeries.coeff_X]
    · intro i _ hne; simp [PowerSeries.coeff_X, hne]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

private lemma cancel_coeff0_one (U F G : PowerSeries (ZMod 3))
    (hU0 : PowerSeries.coeff 0 U = 1) (h : U * F = U * G) : F = G := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn := congrArg (PowerSeries.coeff n) h
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i U * PowerSeries.coeff j F),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i U * PowerSeries.coeff j G)] at hn
    conv at hn => lhs; rw [Finset.sum_range_succ']
    conv at hn => rhs; rw [Finset.sum_range_succ']
    simp only [Nat.sub_zero, hU0, one_mul] at hn
    have htail :
        ∑ k ∈ Finset.range n, PowerSeries.coeff (k + 1) U * PowerSeries.coeff (n - (k + 1)) F =
        ∑ k ∈ Finset.range n, PowerSeries.coeff (k + 1) U * PowerSeries.coeff (n - (k + 1)) G := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      rw [ih (n - (k + 1)) (by omega)]
    rw [htail] at hn
    exact add_left_cancel hn

private lemma cancel_X_pow (k : ℕ) (F G : PowerSeries (ZMod 3))
    (h : PowerSeries.X ^ k * F = PowerSeries.X ^ k * G) : F = G := by
  ext n
  have hn := congrArg (PowerSeries.coeff (n + k)) h
  rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul'] at hn
  simpa [show k ≤ n + k by omega] using hn

private lemma coeff_one_A {A : PowerSeries ℤ} (hA : IsA363560 A) :
    PowerSeries.coeff 1 A = 1 := by
  have h1 := congrArg (PowerSeries.coeff 1) hA.2
  rw [map_add, PowerSeries.coeff_one, if_neg (by decide : (1 : ℕ) ≠ 0), zero_add,
    coeff_X_mul_ps, if_neg (by decide : (1 : ℕ) ≠ 0)] at h1
  simp only [Nat.sub_self, map_add] at h1
  have h0 : PowerSeries.coeff 0 A = 1 := hA.1
  have hA20 : PowerSeries.coeff 0 (A ^ 2) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff, h0]
    norm_num
  have hA90 : PowerSeries.coeff 0 (A ^ 9) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff, h0]
    norm_num
  have hA31 : PowerSeries.coeff 1 (A ^ 3) = 3 * PowerSeries.coeff 1 A := by
    rw [show A ^ 3 = A * (A * A) by ring, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i A * PowerSeries.coeff j (A * A))]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.sub_zero, Nat.sub_self, h0, one_mul]
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i A * PowerSeries.coeff j A),
      PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.sub_zero, Nat.sub_self, h0]
    ring
  rw [hA31, h0, hA20, hA90] at h1
  omega

private lemma coeff_pow_zero_of_not_seven_dvd (z : PowerSeries (ZMod 3))
    {N : ℕ} (hz : ∀ j < N, ¬ (7 ∣ j) → PowerSeries.coeff j z = 0) :
    ∀ r : ℕ, ∀ m < N, ¬ (7 ∣ m) → PowerSeries.coeff m (z ^ r) = 0 := by
  intro r
  induction r with
  | zero =>
    intro m _ hnd
    rw [pow_zero, PowerSeries.coeff_one, if_neg]
    intro hm; subst hm; exact hnd (dvd_zero 7)
  | succ r ih =>
    intro m hm hnd
    rw [pow_succ, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (z ^ r) * PowerSeries.coeff j z)]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hi7 : 7 ∣ i
    · have hmi7 : ¬ (7 ∣ m - i) := by
        intro h
        apply hnd
        have : i + (m - i) = m := by omega
        rw [← this]
        exact dvd_add hi7 h
      rw [hz (m - i) (by omega) hmi7, mul_zero]
    · rw [ih i (by omega) hi7, zero_mul]

private lemma z_eq_one_add_X7_z7 {A : PowerSeries ℤ} (hA : IsA363560 A) :
    let Z : PowerSeries (ZMod 3) :=
      PowerSeries.mk fun n => ((PowerSeries.coeff (n + 1) A : ℤ) : ZMod 3)
    Z = 1 + PowerSeries.X ^ 7 * Z ^ 7 := by
  intro Z
  let phi : PowerSeries ℤ →+* PowerSeries (ZMod 3) := PowerSeries.map (Int.castRingHom (ZMod 3))
  have hA3_eq : phi A = 1 + PowerSeries.X * Z := by
    ext n
    cases n with
    | zero =>
      simp [phi, hA.1]
    | succ n =>
      simp [phi, Z]
  have hcube : ∀ f : PowerSeries (ZMod 3), (1 + f) ^ 3 = 1 + f ^ 3 := by
    intro f
    calc (1 + f) ^ 3 = 1 + f ^ 3 + 3 * (f + f ^ 2) := by ring
      _ = 1 + f ^ 3 := by rw [three_eq_zero_ps3, zero_mul, add_zero]
  have hpow9 : ∀ f : PowerSeries (ZMod 3), (1 + f) ^ 9 = 1 + f ^ 9 := by
    intro f
    rw [show (1 + f) ^ 9 = ((1 + f) ^ 3) ^ 3 by ring, hcube, hcube]
    ring
  have hphi_eq : (phi A) ^ 3 = 1 + PowerSeries.X * (phi A + (phi A) ^ 2 + (phi A) ^ 9) := by
    have h := congrArg phi hA.2
    simp only [map_pow, map_add, map_one, map_mul] at h
    dsimp only [phi] at h
    rw [PowerSeries.map_X] at h
    exact h
  rw [hA3_eq] at hphi_eq
  set Y : PowerSeries (ZMod 3) := PowerSeries.X * Z
  rw [hcube Y, hpow9 Y] at hphi_eq
  have hsum_id : (1 + Y) + (1 + Y) ^ 2 + (1 + Y ^ 9) = Y ^ 2 + Y ^ 9 := by
    calc (1 + Y) + (1 + Y) ^ 2 + (1 + Y ^ 9)
        = Y ^ 2 + Y ^ 9 + 3 * (1 + Y) := by ring
      _ = Y ^ 2 + Y ^ 9 := by rw [three_eq_zero_ps3, zero_mul, add_zero]
  rw [hsum_id] at hphi_eq
  have hY3 : Y ^ 3 = PowerSeries.X * (Y ^ 2 + Y ^ 9) := add_left_cancel hphi_eq
  have hZ0 : PowerSeries.coeff 0 Z = 1 := by
    simp [Z, coeff_one_A hA]
  have hZ20 : PowerSeries.coeff 0 (Z ^ 2) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff, hZ0]
    norm_num
  have hX3Z2 : PowerSeries.X ^ 3 * (Z ^ 2 * Z) =
      PowerSeries.X ^ 3 * (Z ^ 2 * (1 + PowerSeries.X ^ 7 * Z ^ 7)) := by
    calc PowerSeries.X ^ 3 * (Z ^ 2 * Z) = Y ^ 3 := by dsimp only [Y]; ring
      _ = PowerSeries.X * (Y ^ 2 + Y ^ 9) := hY3
      _ = PowerSeries.X ^ 3 * (Z ^ 2 * (1 + PowerSeries.X ^ 7 * Z ^ 7)) := by dsimp only [Y]; ring
  have hZ2 : Z ^ 2 * Z = Z ^ 2 * (1 + PowerSeries.X ^ 7 * Z ^ 7) :=
    cancel_X_pow 3 _ _ hX3Z2
  exact cancel_coeff0_one (Z ^ 2) _ _ hZ20 hZ2

private lemma coeff_Z_zero_of_not_seven_dvd {A : PowerSeries ℤ} (hA : IsA363560 A) :
    ∀ m : ℕ, ¬ (7 ∣ m) → ((PowerSeries.coeff (m + 1) A : ℤ) : ZMod 3) = 0 := by
  let Z : PowerSeries (ZMod 3) :=
    PowerSeries.mk fun n => ((PowerSeries.coeff (n + 1) A : ℤ) : ZMod 3)
  have hZeq : Z = 1 + PowerSeries.X ^ 7 * Z ^ 7 := z_eq_one_add_X7_z7 hA
  intro m
  suffices h : ¬ (7 ∣ m) → PowerSeries.coeff m Z = 0 by simpa [Z] using h
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hnd
    rw [hZeq, map_add, PowerSeries.coeff_one, PowerSeries.coeff_X_pow_mul']
    have hm0 : m ≠ 0 := fun h => hnd (h ▸ dvd_zero 7)
    rw [if_neg hm0, zero_add]
    by_cases h7 : 7 ≤ m
    · rw [if_pos h7]
      have hnd' : ¬ (7 ∣ m - 7) := by
        intro h; apply hnd
        have : m = (m - 7) + 7 := by omega
        rw [this]; exact dvd_add h (dvd_refl 7)
      exact coeff_pow_zero_of_not_seven_dvd Z (fun j hj => ih j hj) 7 (m - 7) (by omega) hnd'
    · rw [if_neg h7]

end OeisA363560Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a363560.main := by
  intro A hA n hn hmod7
  change PowerSeries.coeff n A ≡ 0 [ZMOD ((3 : ℕ) : ℤ)]
  rw [← ZMod.intCast_eq_intCast_iff, Int.cast_zero]
  have hnd : ¬ (7 ∣ n - 1) := by omega
  have h := OeisA363560Proof.coeff_Z_zero_of_not_seven_dvd hA (n - 1) hnd
  rwa [show n - 1 + 1 = n by omega] at h
