import OMAStatements.S_oeis_a363104
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a363104

open OMA.S_oeis_a363104

private lemma zmod16_ps_16 : (16 : PowerSeries (ZMod 16)) = 0 := by
  have h : (16 : ZMod 16) = 0 := by decide
  rw [← map_ofNat (PowerSeries.C (R := ZMod 16)), h, map_zero]

private lemma zmod16_four_mul_four (u v : PowerSeries (ZMod 16)) :
    (4 * u) * (4 * v) = 0 := by
  have h : (4 * u) * (4 * v) = 16 * (u * v) := by ring
  rw [h, zmod16_ps_16, zero_mul]

private lemma zmod16_add_four_pow (u v : PowerSeries (ZMod 16)) (m : ℕ) :
    (4 * u + v) ^ m = v ^ m + (m : PowerSeries (ZMod 16)) * (4 * u) * v ^ (m - 1) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    cases k with
    | zero => simp [add_comm]
    | succ j =>
      simp only [Nat.add_sub_cancel]
      have h1 : (v ^ (j + 1) + ((j + 1 : ℕ) : PowerSeries (ZMod 16)) * (4 * u) * v ^ j) *
          (4 * u + v) =
          v ^ (j + 2) + ((j + 2 : ℕ) : PowerSeries (ZMod 16)) * (4 * u) * v ^ (j + 1) +
          ((j + 1 : ℕ) : PowerSeries (ZMod 16)) * ((4 * u) * (4 * u)) * v ^ j := by
        push_cast; ring
      rw [h1, zmod16_four_mul_four, mul_zero, zero_mul, add_zero]

private lemma zmod16_one_sub_four_pow (u : PowerSeries (ZMod 16)) (m : ℕ) :
    (1 - 4 * u) ^ m = 1 - (m : PowerSeries (ZMod 16)) * (4 * u) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    have h1 : (1 - (k : PowerSeries (ZMod 16)) * (4 * u)) * (1 - 4 * u) =
        1 - ((k + 1 : ℕ) : PowerSeries (ZMod 16)) * (4 * u) +
        (k : PowerSeries (ZMod 16)) * ((4 * u) * (4 * u)) := by
      push_cast; ring
    rw [h1, zmod16_four_mul_four, mul_zero, add_zero]

theorem solution : type_of% @OMA.S_oeis_a363104.main := by
  intro A hA0 hEq
  let φ : PowerSeries ℤ →+* PowerSeries (ZMod 16) := PowerSeries.map (Int.castRingHom (ZMod 16))
  let a : PowerSeries (ZMod 16) := φ A
  have hterm : ∀ n : ℕ, 1 ≤ n →
      φ ((-PowerSeries.X) ^ n * (4 * A + PowerSeries.X ^ (n - 1)) ^ (n + 1) +
         (-1 : PowerSeries ℤ) ^ (n + 1) * PowerSeries.X ^ (n ^ 2 + n - 1) *
           (Ring.inverse (1 + 4 * PowerSeries.X ^ (n + 2) * A)) ^ n) =
      (-1 : PowerSeries (ZMod 16)) ^ n * ((n + 1 : ℕ) : PowerSeries (ZMod 16)) * (4 * a) *
        PowerSeries.X ^ (n ^ 2) +
      (-1 : PowerSeries (ZMod 16)) ^ n * (n : PowerSeries (ZMod 16)) * (4 * a) *
        PowerSeries.X ^ ((n + 1) ^ 2) := by
    intro n hn
    have hu : IsUnit (1 + 4 * PowerSeries.X ^ (n + 2) * A) := by
      apply PowerSeries.isUnit_iff_constantCoeff.mpr
      simp [map_add, map_mul, map_pow]
    have hmul : (1 + 4 * PowerSeries.X ^ (n + 2) * A) *
        Ring.inverse (1 + 4 * PowerSeries.X ^ (n + 2) * A) = 1 :=
      Ring.mul_inverse_cancel _ hu
    have hinv : φ (Ring.inverse (1 + 4 * PowerSeries.X ^ (n + 2) * A)) =
        1 - 4 * (PowerSeries.X ^ (n + 2) * a) := by
      have hm := congrArg φ hmul
      rw [map_mul, map_add, map_one, map_mul, map_mul, map_ofNat, map_pow,
          PowerSeries.map_X] at hm
      have hprod : (1 - 4 * (PowerSeries.X ^ (n + 2) * a)) *
          (1 + 4 * PowerSeries.X ^ (n + 2) * a) = 1 := by
        have h1 : (1 - 4 * (PowerSeries.X ^ (n + 2) * a)) *
            (1 + 4 * PowerSeries.X ^ (n + 2) * a) =
            1 - (4 * (PowerSeries.X ^ (n + 2) * a)) * (4 * (PowerSeries.X ^ (n + 2) * a)) := by
          ring
        rw [h1, zmod16_four_mul_four, sub_zero]
      have h2 := congrArg ((1 - 4 * (PowerSeries.X ^ (n + 2) * a)) * ·) hm
      rw [← mul_assoc, hprod, one_mul, mul_one] at h2
      exact h2
    have hXφ : φ PowerSeries.X = PowerSeries.X := PowerSeries.map_X _
    simp only [map_add, map_mul, map_pow, map_neg, map_one, map_ofNat, hXφ, hinv]
    rw [zmod16_add_four_pow, zmod16_one_sub_four_pow]
    have he1 : (n - 1) * (n + 1) + n = n ^ 2 + n - 1 := by
      rcases n with _ | m; · omega
      simp only [Nat.add_sub_cancel]; ring_nf; omega
    have he2 : (n - 1) * n + n = n ^ 2 := by
      rcases n with _ | m; · omega
      simp only [Nat.add_sub_cancel]; ring
    have he3 : (n ^ 2 + n - 1) + (n + 2) = (n + 1) ^ 2 := by
      have h1 : 1 ≤ n ^ 2 + n := by nlinarith
      have hsq : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
      omega
    have hX1 : (-PowerSeries.X : PowerSeries (ZMod 16)) ^ n =
        (-1 : PowerSeries (ZMod 16)) ^ n * PowerSeries.X ^ n := by
      rw [neg_eq_neg_one_mul, mul_pow]
    rw [hX1, Nat.add_sub_cancel, ← pow_mul, ← pow_mul]
    have hA1 : (-1 : PowerSeries (ZMod 16)) ^ n * PowerSeries.X ^ n *
        (PowerSeries.X ^ ((n - 1) * (n + 1)) +
          ((n + 1 : ℕ) : PowerSeries (ZMod 16)) * (4 * a) * PowerSeries.X ^ ((n - 1) * n)) =
        (-1 : PowerSeries (ZMod 16)) ^ n * PowerSeries.X ^ (n ^ 2 + n - 1) +
        (-1 : PowerSeries (ZMod 16)) ^ n * ((n + 1 : ℕ) : PowerSeries (ZMod 16)) * (4 * a) *
          PowerSeries.X ^ (n ^ 2) := by
      rw [mul_add]
      congr 1
      · rw [mul_assoc, ← pow_add, add_comm, he1]
      · rw [show (-1 : PowerSeries (ZMod 16)) ^ n * PowerSeries.X ^ n *
            (((n + 1 : ℕ) : PowerSeries (ZMod 16)) * (4 * a) * PowerSeries.X ^ ((n - 1) * n)) =
            (-1 : PowerSeries (ZMod 16)) ^ n * ((n + 1 : ℕ) : PowerSeries (ZMod 16)) * (4 * a) *
            (PowerSeries.X ^ ((n - 1) * n) * PowerSeries.X ^ n) by ring, ← pow_add, he2]
    have hA2 : (-1 : PowerSeries (ZMod 16)) ^ (n + 1) * PowerSeries.X ^ (n ^ 2 + n - 1) *
        (1 - (n : PowerSeries (ZMod 16)) * (4 * (PowerSeries.X ^ (n + 2) * a))) =
        -((-1 : PowerSeries (ZMod 16)) ^ n * PowerSeries.X ^ (n ^ 2 + n - 1)) +
        (-1 : PowerSeries (ZMod 16)) ^ n * (n : PowerSeries (ZMod 16)) * (4 * a) *
          PowerSeries.X ^ ((n + 1) ^ 2) := by
      rw [pow_succ, mul_neg_one, neg_mul, mul_sub, mul_one, sub_eq_add_neg, neg_mul, neg_neg]
      congr 1
      rw [show (-1 : PowerSeries (ZMod 16)) ^ n * PowerSeries.X ^ (n ^ 2 + n - 1) *
          ((n : PowerSeries (ZMod 16)) * (4 * (PowerSeries.X ^ (n + 2) * a))) =
          (-1 : PowerSeries (ZMod 16)) ^ n * (n : PowerSeries (ZMod 16)) * (4 * a) *
          (PowerSeries.X ^ (n ^ 2 + n - 1) * PowerSeries.X ^ (n + 2)) by ring, ← pow_add, he3]
    rw [hA1, hA2]
    ring
  -- Strong induction on r ≥ 1
  have hmain : ∀ r : ℕ, 0 < r →
      ((∃ k : ℕ, k ^ 2 = r) → PowerSeries.coeff r A % 4 = 2) ∧
      ((∀ k : ℕ, k ^ 2 ≠ r) → PowerSeries.coeff r A % 4 = 0) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro hr
      have h16 := congrArg (Int.castRingHom (ZMod 16)) (hEq r)
      rw [if_neg (by omega), map_zero, map_add, map_mul, map_ofNat, map_sum] at h16
      have hsum_eq :
          ∑ n ∈ Finset.Icc 1 r,
            (Int.castRingHom (ZMod 16))
              (PowerSeries.coeff r
                ((-PowerSeries.X) ^ n * (4 * A + PowerSeries.X ^ (n - 1)) ^ (n + 1) +
                 (-1 : PowerSeries ℤ) ^ (n + 1) * PowerSeries.X ^ (n ^ 2 + n - 1) *
                   (Ring.inverse (1 + 4 * PowerSeries.X ^ (n + 2) * A)) ^ n)) =
          ∑ k ∈ Finset.Icc 1 r,
            (8 : ZMod 16) * (if k ^ 2 ≤ r then PowerSeries.coeff (r - k ^ 2) a else 0) := by
        have h1 : ∀ n ∈ Finset.Icc 1 r,
            (Int.castRingHom (ZMod 16))
              (PowerSeries.coeff r
                ((-PowerSeries.X) ^ n * (4 * A + PowerSeries.X ^ (n - 1)) ^ (n + 1) +
                 (-1 : PowerSeries ℤ) ^ (n + 1) * PowerSeries.X ^ (n ^ 2 + n - 1) *
                   (Ring.inverse (1 + 4 * PowerSeries.X ^ (n + 2) * A)) ^ n)) =
            (-1 : ZMod 16) ^ n * ((n + 1 : ℕ) : ZMod 16) * 4 *
              (if n ^ 2 ≤ r then PowerSeries.coeff (r - n ^ 2) a else 0) +
            (-1 : ZMod 16) ^ n * (n : ZMod 16) * 4 *
              (if (n + 1) ^ 2 ≤ r then PowerSeries.coeff (r - (n + 1) ^ 2) a else 0) := by
          intro n hn
          rw [← PowerSeries.coeff_map, hterm n (Finset.mem_Icc.mp hn).1, map_add]
          have hc : ∀ (c : ZMod 16) (m : ℕ),
              PowerSeries.coeff r ((PowerSeries.C c) * a * PowerSeries.X ^ m) =
              c * (if m ≤ r then PowerSeries.coeff (r - m) a else 0) := by
            intro c m
            rw [mul_comm _ (PowerSeries.X ^ m), ← mul_assoc, mul_comm (PowerSeries.X ^ m),
                mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
          have hc1 : (-1 : PowerSeries (ZMod 16)) ^ n * ((n + 1 : ℕ) : PowerSeries (ZMod 16)) *
              (4 * a) * PowerSeries.X ^ (n ^ 2) =
              PowerSeries.C ((-1 : ZMod 16) ^ n * ((n + 1 : ℕ) : ZMod 16) * 4) * a *
                PowerSeries.X ^ (n ^ 2) := by
            simp only [map_mul, map_pow, map_neg, map_one, map_natCast, map_ofNat]; ring
          have hc2 : (-1 : PowerSeries (ZMod 16)) ^ n * (n : PowerSeries (ZMod 16)) *
              (4 * a) * PowerSeries.X ^ ((n + 1) ^ 2) =
              PowerSeries.C ((-1 : ZMod 16) ^ n * (n : ZMod 16) * 4) * a *
                PowerSeries.X ^ ((n + 1) ^ 2) := by
            simp only [map_mul, map_pow, map_neg, map_one, map_natCast, map_ofNat]; ring
          rw [hc1, hc2, hc, hc]
        rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
        have h2 : ∑ n ∈ Finset.Icc 1 r,
            (-1 : ZMod 16) ^ n * (n : ZMod 16) * 4 *
              (if (n + 1) ^ 2 ≤ r then PowerSeries.coeff (r - (n + 1) ^ 2) a else 0) =
            ∑ k ∈ Finset.Icc 1 r,
              (if k = 1 then (0 : ZMod 16)
               else (-1 : ZMod 16) ^ (k - 1) * ((k - 1 : ℕ) : ZMod 16) * 4 *
                 (if k ^ 2 ≤ r then PowerSeries.coeff (r - k ^ 2) a else 0)) := by
          cases r with
          | zero => omega
          | succ m =>
            have hlast : ¬ (m + 1 + 1) ^ 2 ≤ m + 1 := by nlinarith
            rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), if_neg hlast, mul_zero, add_zero]
            have hIcc : Finset.Icc 1 (m + 1) = Finset.Ico 1 (m + 2) := by
              ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
            rw [hIcc, Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < m + 2)]
            simp only [↓reduceIte, zero_add]
            refine Finset.sum_bij (fun n _ => n + 1) ?_ ?_ ?_ ?_
            · intro n hn; simp only [Finset.mem_Icc, Finset.mem_Ico] at hn ⊢; omega
            · intro n1 _ n2 _ h; omega
            · intro k hk; simp only [Finset.mem_Ico, Finset.mem_Icc] at hk ⊢
              exact ⟨k - 1, by omega, by omega⟩
            · intro n hn; simp only [Finset.mem_Icc] at hn
              rw [if_neg (by omega : n + 1 ≠ 1), Nat.add_sub_cancel]
        rw [h2, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        by_cases hkeq : k = 1
        · subst hkeq
          simp only [↓reduceIte, add_zero]
          have h8 : (-1 : ZMod 16) ^ 1 * ((1 + 1 : ℕ) : ZMod 16) * 4 = 8 := by decide
          rw [h8]
        · rw [if_neg hkeq, ← add_mul]
          congr 1
          have hk2 : k = (k - 1) + 1 := by omega
          have hsign : (-1 : ZMod 16) ^ k * ((k + 1 : ℕ) : ZMod 16) * 4 +
              (-1 : ZMod 16) ^ (k - 1) * ((k - 1 : ℕ) : ZMod 16) * 4 =
              (-1 : ZMod 16) ^ k * 8 := by
            conv_lhs => rw [hk2]
            conv_rhs => rw [hk2]
            rw [pow_succ, mul_neg_one]
            push_cast
            ring
          rw [hsign]
          have hneg : ∀ m : ℕ, (-1 : ZMod 16) ^ m * 8 = 8 := by
            intro m; induction m with
            | zero => decide
            | succ j ihj =>
              rw [pow_succ, mul_assoc, neg_one_mul, show (-8 : ZMod 16) = 8 by decide, ihj]
          exact hneg k
      rw [hsum_eq] at h16
      have hterm_zero : ∀ k ∈ Finset.Icc 1 r,
          (8 : ZMod 16) * (if k ^ 2 ≤ r then PowerSeries.coeff (r - k ^ 2) a else 0) =
          if k ^ 2 = r then (8 : ZMod 16) else 0 := by
        intro k hk
        by_cases hlt : k ^ 2 < r
        · rw [if_pos (by omega), if_neg (by omega)]
          have hih := ih (r - k ^ 2)
            (Nat.sub_lt (by omega) (by nlinarith [(Finset.mem_Icc.mp hk).1])) (by omega)
          have hev : (2 : ℤ) ∣ PowerSeries.coeff (r - k ^ 2) A := by
            by_cases hs : ∃ j : ℕ, j ^ 2 = r - k ^ 2
            · have := hih.1 hs; omega
            · have := hih.2 (fun j hj => hs ⟨j, hj⟩); omega
          rcases hev with ⟨q, hq⟩
          have hc : PowerSeries.coeff (r - k ^ 2) a = (2 : ZMod 16) * (q : ZMod 16) := by
            change (Int.castRingHom (ZMod 16)) (PowerSeries.coeff (r - k ^ 2) A) = _
            rw [hq, map_mul, map_ofNat]
            rfl
          rw [hc, ← mul_assoc, show (8 : ZMod 16) * 2 = 0 by decide, zero_mul]
        · by_cases heq : k ^ 2 = r
          · rw [if_pos (by omega), if_pos heq, heq, Nat.sub_self]
            have h0 : PowerSeries.coeff 0 a = 1 := by
              change (Int.castRingHom (ZMod 16)) (PowerSeries.coeff 0 A) = 1
              rw [PowerSeries.coeff_zero_eq_constantCoeff, hA0, map_one]
            rw [h0, mul_one]
          · rw [if_neg (by omega), if_neg heq, mul_zero]
      rw [Finset.sum_congr rfl hterm_zero] at h16
      constructor
      · rintro ⟨k0, hk0⟩
        have hk0_mem : k0 ∈ Finset.Icc 1 r := by
          rw [Finset.mem_Icc]; constructor <;> nlinarith
        rw [Finset.sum_eq_single k0] at h16
        · rw [if_pos hk0] at h16
          have h4 : (4 : ZMod 16) * ((PowerSeries.coeff r A : ℤ) : ZMod 16) + 8 = 0 := by
            simpa using h16.symm
          have hmod : (4 * PowerSeries.coeff r A + 8) % 16 = 0 := by
            have hcast : ((4 * PowerSeries.coeff r A + 8 : ℤ) : ZMod 16) = 0 := by
              push_cast; exact h4
            exact Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 16).mp hcast)
          omega
        · intro k _ hne; rw [if_neg]; intro h; apply hne; nlinarith
        · intro h; exact absurd hk0_mem h
      · intro hnsq
        have hzero : ∑ k ∈ Finset.Icc 1 r, (if k ^ 2 = r then (8 : ZMod 16) else 0) = 0 := by
          refine Finset.sum_eq_zero fun k _ => ?_
          rw [if_neg (hnsq k)]
        rw [hzero, add_zero] at h16
        have h4 : (4 : ZMod 16) * ((PowerSeries.coeff r A : ℤ) : ZMod 16) = 0 := by
          simpa using h16.symm
        have hmod : (4 * PowerSeries.coeff r A) % 16 = 0 := by
          have hcast : ((4 * PowerSeries.coeff r A : ℤ) : ZMod 16) = 0 := by
            push_cast; exact h4
          exact Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 16).mp hcast)
        omega
  exact ⟨fun k hk => (hmain (k ^ 2) (by positivity)).1 ⟨k, rfl⟩,
         fun r hr hnsq => (hmain r hr).2 hnsq⟩

end OMA.P_oeis_a363104

theorem OMA.solution : type_of% @OMA.S_oeis_a363104.main := OMA.P_oeis_a363104.solution
