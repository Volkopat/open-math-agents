import OMAStatements.S_oeis_a193236
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a193236

open OMA.S_oeis_a193236

private lemma charP_ps (p : ℕ) [Fact (Nat.Prime p)] : CharP (PowerSeries (ZMod p)) p := by
  constructor
  intro n
  constructor
  · intro h
    have hc := congrArg PowerSeries.constantCoeff h
    rw [map_natCast, map_zero] at hc
    exact (ZMod.natCast_eq_zero_iff n p).mp hc
  · intro hd
    have h0 : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr hd
    rw [← map_natCast (PowerSeries.C (R := ZMod p)), h0, map_zero]

private lemma coeff_pow_prime_eq_zero {p : ℕ} [Fact (Nat.Prime p)]
    (f : PowerSeries (ZMod p)) (n : ℕ) (hnd : ¬ p ∣ n) :
    PowerSeries.coeff n (f ^ p) = 0 := by
  have : CharP (PowerSeries (ZMod p)) p := charP_ps p
  let P : PowerSeries (ZMod p) :=
    ∑ k ∈ Finset.range (n + 1), PowerSeries.C (PowerSeries.coeff k f) * PowerSeries.X ^ k
  let R : PowerSeries (ZMod p) :=
    PowerSeries.mk fun k => PowerSeries.coeff (k + (n + 1)) f
  have hsplit : f = P + PowerSeries.X ^ (n + 1) * R := by
    ext k
    rw [map_add, map_sum, PowerSeries.coeff_X_pow_mul']
    by_cases hk : k < n + 1
    · rw [if_neg (by omega), add_zero, Finset.sum_eq_single k]
      · rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_pos rfl, mul_one]
      · intro j _ hj; rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg (Ne.symm hj), mul_zero]
      · intro h; exact absurd (Finset.mem_range.mpr hk) h
    · rw [if_pos (by omega)]
      have hP0 : ∑ x ∈ Finset.range (n + 1),
          PowerSeries.coeff k (PowerSeries.C (PowerSeries.coeff x f) * PowerSeries.X ^ x) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        rw [Finset.mem_range] at hj
        rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg (by omega), mul_zero]
      rw [hP0, zero_add]
      dsimp only [R]; rw [PowerSeries.coeff_mk, Nat.sub_add_cancel (by omega)]
  have hp_pos : 1 ≤ p := Nat.Prime.one_le (Fact.out : Nat.Prime p)
  rw [hsplit, add_pow_char, map_add, mul_pow, ← pow_mul, PowerSeries.coeff_X_pow_mul',
      if_neg (by nlinarith), add_zero]
  have hsum_pow : ∀ (s : Finset ℕ) (g : ℕ → PowerSeries (ZMod p)),
      (∑ k ∈ s, g k) ^ p = ∑ k ∈ s, g k ^ p := by
    intro s g
    induction s using Finset.cons_induction with
    | empty => simp [zero_pow (by omega : p ≠ 0)]
    | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, add_pow_char, ih]
  dsimp only [P]
  rw [hsum_pow, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [mul_pow, ← map_pow, ← pow_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
      if_neg (by intro heq; exact hnd ⟨k, by rw [heq, mul_comm]⟩), mul_zero]

private lemma coeff_inv_of_dvd_supp {p : ℕ} (_hp : 0 < p) {g h : PowerSeries (ZMod p)}
    (hg0 : PowerSeries.constantCoeff g = 1) (hgh : g * h = 1)
    (hsupp : ∀ n, ¬ p ∣ n → PowerSeries.coeff n g = 0) :
    ∀ n, ¬ p ∣ n → PowerSeries.coeff n h = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hnd
    have h0 := congrArg (PowerSeries.coeff n) hgh
    have hn0 : n ≠ 0 := by rintro rfl; exact hnd (dvd_zero p)
    rw [PowerSeries.coeff_one, if_neg hn0, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i g * PowerSeries.coeff j h),
        Finset.sum_range_succ'] at h0
    have htail : ∑ k ∈ Finset.range n,
        PowerSeries.coeff (k + 1) g * PowerSeries.coeff (n - (k + 1)) h = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [Finset.mem_range] at hk
      by_cases hd : p ∣ k + 1
      · have hnd' : ¬ p ∣ n - (k + 1) := by
          intro hd'
          have : p ∣ (n - (k + 1)) + (k + 1) := dvd_add hd' hd
          rw [Nat.sub_add_cancel (by omega)] at this
          exact hnd this
        rw [ih (n - (k + 1)) (by omega) hnd', mul_zero]
      · rw [hsupp (k + 1) hd, zero_mul]
    rw [htail, zero_add, Nat.sub_zero, PowerSeries.coeff_zero_eq_constantCoeff, hg0, one_mul] at h0
    exact h0

private lemma coeff_mul_of_dvd_supp {p : ℕ} {g h : PowerSeries (ZMod p)} {r : ℕ}
    (hg : ∀ n, ¬ p ∣ n → PowerSeries.coeff n g = 0)
    (hh : ∀ n, n % p = r → PowerSeries.coeff n h = 0) :
    ∀ n, n % p = r → PowerSeries.coeff n (g * h) = 0 := by
  intro n hnr
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun q hq => ?_
  rw [Finset.mem_antidiagonal] at hq
  by_cases hd : p ∣ q.1
  · have hq2 : q.2 % p = r := by
      rcases hd with ⟨t, ht⟩
      have : n = p * t + q.2 := by omega
      rw [this, Nat.mul_add_mod] at hnr
      exact hnr
    rw [hh q.2 hq2, mul_zero]
  · rw [hg q.1 hd, zero_mul]

private lemma tri_mod5_ne (n : ℕ) :
    (2 * n + 1) % 5 = 0 ∨ (n * (n + 1) / 2) % 5 = 0 ∨ (n * (n + 1) / 2) % 5 = 1 := by
  have htri : (n * (n + 1) / 2) % 5 = ((n % 10) * (n % 10 + 1) / 2) % 5 := by
    have h10 : 10 ∣ n * (n + 1) - (n % 10) * (n % 10 + 1) := by
      set q := n / 10
      set r := n % 10
      have heq : n = 10 * q + r := by omega
      rw [heq]
      refine ⟨10 * q ^ 2 + 2 * q * r + q, ?_⟩
      have hge : r * (r + 1) ≤ (10 * q + r) * (10 * q + r + 1) := by nlinarith
      zify [hge]; ring
    rcases h10 with ⟨t, ht⟩
    have hge : (n % 10) * (n % 10 + 1) ≤ n * (n + 1) :=
      Nat.mul_le_mul (Nat.mod_le n 10) (by have := Nat.mod_le n 10; omega)
    have heq2 : n * (n + 1) = (n % 10) * (n % 10 + 1) + 2 * (5 * t) := by omega
    rw [heq2, Nat.add_mul_div_left _ _ (by decide : 0 < 2), Nat.add_mul_mod_self_left]
  rw [htri, show (2 * n + 1) % 5 = (2 * (n % 10) + 1) % 5 by omega]
  have hr : n % 10 = 0 ∨ n % 10 = 1 ∨ n % 10 = 2 ∨ n % 10 = 3 ∨ n % 10 = 4 ∨
            n % 10 = 5 ∨ n % 10 = 6 ∨ n % 10 = 7 ∨ n % 10 = 8 ∨ n % 10 = 9 := by omega
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr <;>
    simp only [hr] <;> decide

private lemma tri_mod7_ne (n : ℕ) :
    (2 * n + 1) % 7 = 0 ∨ (n * (n + 1) / 2) % 7 = 0 ∨
    (n * (n + 1) / 2) % 7 = 1 ∨ (n * (n + 1) / 2) % 7 = 3 := by
  have htri : (n * (n + 1) / 2) % 7 = ((n % 14) * (n % 14 + 1) / 2) % 7 := by
    have h14 : 14 ∣ n * (n + 1) - (n % 14) * (n % 14 + 1) := by
      set q := n / 14
      set r := n % 14
      have heq : n = 14 * q + r := by omega
      rw [heq]
      refine ⟨14 * q ^ 2 + 2 * q * r + q, ?_⟩
      have hge : r * (r + 1) ≤ (14 * q + r) * (14 * q + r + 1) := by nlinarith
      zify [hge]; ring
    rcases h14 with ⟨t, ht⟩
    have hge : (n % 14) * (n % 14 + 1) ≤ n * (n + 1) :=
      Nat.mul_le_mul (Nat.mod_le n 14) (by have := Nat.mod_le n 14; omega)
    have heq2 : n * (n + 1) = (n % 14) * (n % 14 + 1) + 2 * (7 * t) := by omega
    rw [heq2, Nat.add_mul_div_left _ _ (by decide : 0 < 2), Nat.add_mul_mod_self_left]
  rw [htri, show (2 * n + 1) % 7 = (2 * (n % 14) + 1) % 7 by omega]
  have hr : n % 14 = 0 ∨ n % 14 = 1 ∨ n % 14 = 2 ∨ n % 14 = 3 ∨ n % 14 = 4 ∨
            n % 14 = 5 ∨ n % 14 = 6 ∨ n % 14 = 7 ∨ n % 14 = 8 ∨ n % 14 = 9 ∨
            n % 14 = 10 ∨ n % 14 = 11 ∨ n % 14 = 12 ∨ n % 14 = 13 := by omega
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr <;>
    simp only [hr] <;> decide

theorem solution : type_of% @OMA.S_oeis_a193236.main := by
  intro A S _hA0 hS hA3S n
  constructor
  · have : Fact (Nat.Prime 5) := ⟨by decide⟩
    let φ : PowerSeries ℤ →+* PowerSeries (ZMod 5) := PowerSeries.map (Int.castRingHom (ZMod 5))
    let a5 : PowerSeries (ZMod 5) := φ A
    let s5 : PowerSeries (ZMod 5) := φ S
    have ha5s5 : a5 ^ 3 * s5 = 1 := by
      dsimp only [a5, s5]; rw [← map_pow, ← map_mul, hA3S, map_one]
    have hs5_supp : ∀ m : ℕ, m % 5 ≠ 0 → m % 5 ≠ 1 → PowerSeries.coeff m s5 = 0 := by
      intro m hm0 hm1
      dsimp only [s5, φ]
      rw [PowerSeries.coeff_map, hS m, map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      split_ifs with htri
      · rcases tri_mod5_ne k with h2n | h0 | h1
        · rw [map_mul, map_natCast, ← ZMod.natCast_mod, h2n, Nat.cast_zero, zero_mul]
        · rw [htri] at h0; exact absurd h0 hm0
        · rw [htri] at h1; exact absurd h1 hm1
      · exact map_zero _
    have hs5_cube : ∀ m : ℕ, m % 5 = 4 → PowerSeries.coeff m (s5 ^ 3) = 0 := by
      intro m hm4
      rw [show s5 ^ 3 = s5 * (s5 * s5) by ring, PowerSeries.coeff_mul]
      refine Finset.sum_eq_zero fun p hp => ?_
      rw [Finset.mem_antidiagonal] at hp
      by_cases h1 : p.1 % 5 = 0 ∨ p.1 % 5 = 1
      · rw [PowerSeries.coeff_mul]
        have h2 : ∑ q ∈ Finset.antidiagonal p.2, PowerSeries.coeff q.1 s5 * PowerSeries.coeff q.2 s5 = 0 := by
          refine Finset.sum_eq_zero fun q hq => ?_
          rw [Finset.mem_antidiagonal] at hq
          by_cases hq1 : q.1 % 5 = 0 ∨ q.1 % 5 = 1
          · have hq2 : q.2 % 5 ≠ 0 ∧ q.2 % 5 ≠ 1 := by omega
            rw [hs5_supp q.2 hq2.1 hq2.2, mul_zero]
          · push Not at hq1
            rw [hs5_supp q.1 hq1.1 hq1.2, zero_mul]
        rw [h2, mul_zero]
      · push Not at h1
        rw [hs5_supp p.1 h1.1 h1.2, zero_mul]
    have ha5_eq : a5 = (a5 ^ 2) ^ 5 * s5 ^ 3 := by
      calc a5 = a5 * 1 := (mul_one _).symm
        _ = a5 * (a5 ^ 3 * s5) ^ 3 := by rw [ha5s5, one_pow]
        _ = (a5 ^ 2) ^ 5 * s5 ^ 3 := by ring
    have h0 : ((PowerSeries.coeff (5 * n + 4) A : ℤ) : ZMod 5) = 0 := by
      have h1 : ((PowerSeries.coeff (5 * n + 4) A : ℤ) : ZMod 5) = PowerSeries.coeff (5 * n + 4) a5 := by
        dsimp only [a5, φ]; rw [PowerSeries.coeff_map]; rfl
      rw [h1, ha5_eq]
      exact coeff_mul_of_dvd_supp (coeff_pow_prime_eq_zero (a5 ^ 2)) hs5_cube (5 * n + 4) (by omega)
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp h0
  · have : Fact (Nat.Prime 7) := ⟨by decide⟩
    let φ : PowerSeries ℤ →+* PowerSeries (ZMod 7) := PowerSeries.map (Int.castRingHom (ZMod 7))
    let a7 : PowerSeries (ZMod 7) := φ A
    let s7 : PowerSeries (ZMod 7) := φ S
    have ha7s7 : a7 ^ 3 * s7 = 1 := by
      dsimp only [a7, s7]; rw [← map_pow, ← map_mul, hA3S, map_one]
    have hs7_supp : ∀ m : ℕ, m % 7 ≠ 0 → m % 7 ≠ 1 → m % 7 ≠ 3 → PowerSeries.coeff m s7 = 0 := by
      intro m hm0 hm1 hm3
      dsimp only [s7, φ]
      rw [PowerSeries.coeff_map, hS m, map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      split_ifs with htri
      · rcases tri_mod7_ne k with h2n | h0 | h1 | h3
        · rw [map_mul, map_natCast, ← ZMod.natCast_mod, h2n, Nat.cast_zero, zero_mul]
        · rw [htri] at h0; exact absurd h0 hm0
        · rw [htri] at h1; exact absurd h1 hm1
        · rw [htri] at h3; exact absurd h3 hm3
      · exact map_zero _
    have hs7_sq : ∀ m : ℕ, m % 7 = 5 → PowerSeries.coeff m (s7 ^ 2) = 0 := by
      intro m hm5
      rw [sq, PowerSeries.coeff_mul]
      refine Finset.sum_eq_zero fun p hp => ?_
      rw [Finset.mem_antidiagonal] at hp
      by_cases h1 : p.1 % 7 = 0 ∨ p.1 % 7 = 1 ∨ p.1 % 7 = 3
      · have h2 : p.2 % 7 ≠ 0 ∧ p.2 % 7 ≠ 1 ∧ p.2 % 7 ≠ 3 := by omega
        rw [hs7_supp p.2 h2.1 h2.2.1 h2.2.2, mul_zero]
      · push Not at h1
        rw [hs7_supp p.1 h1.1 h1.2.1 h1.2.2, zero_mul]
    have ha7_eq : a7 = a7 ^ 7 * s7 ^ 2 := by
      calc a7 = a7 * 1 := (mul_one _).symm
        _ = a7 * (a7 ^ 3 * s7) ^ 2 := by rw [ha7s7, one_pow]
        _ = a7 ^ 7 * s7 ^ 2 := by ring
    have h0 : ((PowerSeries.coeff (7 * n + 5) A : ℤ) : ZMod 7) = 0 := by
      have h1 : ((PowerSeries.coeff (7 * n + 5) A : ℤ) : ZMod 7) = PowerSeries.coeff (7 * n + 5) a7 := by
        dsimp only [a7, φ]; rw [PowerSeries.coeff_map]; rfl
      rw [h1, ha7_eq]
      exact coeff_mul_of_dvd_supp (coeff_pow_prime_eq_zero a7) hs7_sq (7 * n + 5) (by omega)
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp h0

end OMA.P_oeis_a193236

theorem OMA.solution : type_of% @OMA.S_oeis_a193236.main := OMA.P_oeis_a193236.solution
