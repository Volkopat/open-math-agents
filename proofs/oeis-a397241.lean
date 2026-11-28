import OMAStatements.S_oeis_a397241
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a397241

open OMA.S_oeis_a397241

private lemma odd_of_zmod2_eq_one (z : ℤ) (h : (z : ZMod 2) = 1) : Odd z := by
  rcases Int.even_or_odd z with ⟨k, rfl⟩ | hodd
  · push_cast at h
    have h2 : (2 : ZMod 2) = 0 := by decide
    have hkk : (k : ZMod 2) + (k : ZMod 2) = 0 := by
      rw [← two_mul, h2, zero_mul]
    rw [hkk] at h
    exact absurd h (by decide)
  · exact hodd

private lemma coeff_pow_diff {R : Type*} [CommRing R] (f g : PowerSeries R) (n : ℕ)
    (h0 : PowerSeries.constantCoeff f = 1)
    (hagree : ∀ k < n, PowerSeries.coeff k f = PowerSeries.coeff k g) (hn : 0 < n) :
    ∀ m : ℕ, PowerSeries.coeff n (f ^ m) - PowerSeries.coeff n (g ^ m) =
      (m : R) * (PowerSeries.coeff n f - PowerSeries.coeff n g) := by
  have hg0 : PowerSeries.constantCoeff g = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, ← hagree 0 hn,
        PowerSeries.coeff_zero_eq_constantCoeff, h0]
  have hpow_agree : ∀ m : ℕ, ∀ k < n, PowerSeries.coeff k (f ^ m) = PowerSeries.coeff k (g ^ m) := by
    intro m
    induction m with
    | zero => intro k _; rfl
    | succ j ihj =>
      intro k hk
      rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp1 : p.1 < n := by
        have := Finset.mem_antidiagonal.mp hp; omega
      have hp2 : p.2 < n := by
        have := Finset.mem_antidiagonal.mp hp; omega
      rw [ihj p.1 hp1, hagree p.2 hp2]
  intro m
  induction m with
  | zero => simp
  | succ j ihj =>
    rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul, ← Finset.sum_sub_distrib]
    have hsplit : ∀ p ∈ Finset.antidiagonal n,
        PowerSeries.coeff p.1 (f ^ j) * PowerSeries.coeff p.2 f -
        PowerSeries.coeff p.1 (g ^ j) * PowerSeries.coeff p.2 g =
        (if p = (n, 0) then PowerSeries.coeff n (f ^ j) - PowerSeries.coeff n (g ^ j) else 0) +
        (if p = (0, n) then PowerSeries.coeff n f - PowerSeries.coeff n g else 0) := by
      intro p hp
      have hsum : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
      by_cases hp1 : p.1 = n
      · have hp2 : p.2 = 0 := by omega
        have hp_eq : p = (n, 0) := Prod.ext hp1 hp2
        have hp_ne : p ≠ (0, n) := by intro h; rw [hp_eq] at h; exact absurd (Prod.mk.inj h).1 (by omega)
        rw [if_pos hp_eq, if_neg hp_ne, add_zero, hp1, hp2,
            PowerSeries.coeff_zero_eq_constantCoeff, h0, hg0, mul_one, mul_one]
      · by_cases hp2 : p.2 = n
        · have hp1' : p.1 = 0 := by omega
          have hp_eq : p = (0, n) := Prod.ext hp1' hp2
          have hp_ne : p ≠ (n, 0) := by intro h; rw [hp_eq] at h; exact absurd (Prod.mk.inj h).1 (by omega)
          rw [if_neg hp_ne, if_pos hp_eq, zero_add, hp1', hp2,
              PowerSeries.coeff_zero_eq_constantCoeff, map_pow, map_pow, h0, hg0, one_pow, one_mul, one_mul]
        · have hne1 : p ≠ (n, 0) := fun h => hp1 (congrArg Prod.fst h)
          have hne2 : p ≠ (0, n) := fun h => hp2 (congrArg Prod.snd h)
          rw [if_neg hne1, if_neg hne2, add_zero, hpow_agree j p.1 (by omega), hagree p.2 (by omega), sub_self]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    have hmem1 : (n, 0) ∈ Finset.antidiagonal n := Finset.mem_antidiagonal.mpr (add_zero n)
    have hmem2 : (0, n) ∈ Finset.antidiagonal n := Finset.mem_antidiagonal.mpr (zero_add n)
    rw [Finset.sum_ite_eq' _ (n, 0), if_pos hmem1, Finset.sum_ite_eq' _ (0, n), if_pos hmem2, ihj]
    push_cast; ring

private lemma coeff_U_pow (m : ℕ) (hm : 1 ≤ m) :
    ∀ k : ℕ, PowerSeries.coeff k ((PowerSeries.mk (fun _ => (1 : ZMod 2))) ^ m) =
      (Nat.choose (k + m - 1) k : ZMod 2) := by
  let U : PowerSeries (ZMod 2) := PowerSeries.mk (fun _ => 1)
  have hU : ∀ k : ℕ, PowerSeries.coeff k U = 1 := fun k => PowerSeries.coeff_mk k _
  induction m with
  | zero => omega
  | succ j ihj =>
    cases j with
    | zero =>
      intro k
      simp only [Nat.add_sub_cancel, Nat.choose_self, Nat.cast_one]
      rw [show (PowerSeries.mk fun _ => (1 : ZMod 2)) ^ (0 + 1) = U by simp [U]]
      exact hU k
    | succ i =>
      intro k
      rw [pow_succ, PowerSeries.coeff_mul]
      have h1 : ∀ p ∈ Finset.antidiagonal k,
          PowerSeries.coeff p.1 (U ^ (i + 1)) * PowerSeries.coeff p.2 U =
          (Nat.choose (p.1 + i) p.1 : ZMod 2) := by
        intro p _
        rw [ihj (by omega) p.1, hU p.2, mul_one, show p.1 + (i + 1) - 1 = p.1 + i by omega]
      rw [Finset.sum_congr rfl h1]
      have hsum : ∑ p ∈ Finset.antidiagonal k, Nat.choose (p.1 + i) p.1 =
          Nat.choose (k + i + 1) k := by
        rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x _ => Nat.choose (x + i) x)]
        clear h1 ihj
        induction k with
        | zero => simp
        | succ t iht =>
          rw [Finset.sum_range_succ, iht]
          rw [show t + 1 + i = t + i + 1 by omega]
          exact (Nat.choose_succ_succ (t + i + 1) t).symm
      have hcast := congrArg (Nat.cast (R := ZMod 2)) hsum
      rw [Nat.cast_sum] at hcast
      rw [show k + (i + 1 + 1) - 1 = k + i + 1 by omega]
      exact hcast

private lemma even_central_binom (m : ℕ) (hm : 1 ≤ m) : Even (Nat.choose (2 * m) m) := by
  have h := Nat.add_one_mul_choose_eq (2 * m - 1) (m - 1)
  have h1 : 2 * m - 1 + 1 = 2 * m := by omega
  have h2 : m - 1 + 1 = m := by omega
  rw [h1, h2] at h
  -- h : 2 * m * C(2m-1, m-1) = C(2m, m) * m
  have h3 : Nat.choose (2 * m) m = 2 * Nat.choose (2 * m - 1) (m - 1) := by
    have : m * Nat.choose (2 * m) m = m * (2 * Nat.choose (2 * m - 1) (m - 1)) := by linarith
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  exact ⟨Nat.choose (2 * m - 1) (m - 1), by omega⟩

private lemma even_n_mul_choose (n : ℕ) (hn : 2 ≤ n) : Even (n * Nat.choose (2 * n - 1) n) := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · exact ⟨m * Nat.choose (2 * (m + m) - 1) (m + m), by ring⟩
  · have hm : 1 ≤ m := by omega
    have h := Nat.add_one_mul_choose_eq (4 * m) (2 * m)
    have h1 : 2 * (2 * m + 1) - 1 = 4 * m + 1 := by omega
    rw [h1]
    -- h : (4m+1) * C(4m, 2m) = C(4m+1, 2m+1) * (2m+1)
    have h2 : (2 * m + 1) * Nat.choose (4 * m + 1) (2 * m + 1) =
        (4 * m + 1) * Nat.choose (4 * m) (2 * m) := by linarith
    rw [h2]
    rcases even_central_binom (2 * m) (by omega) with ⟨q, hq⟩
    rw [show 2 * (2 * m) = 4 * m by ring] at hq
    exact ⟨(4 * m + 1) * q, by rw [hq]; ring⟩

theorem solution : type_of% @OMA.S_oeis_a397241.main := by
  intro A hA0 hA1 hEq n
  apply odd_of_zmod2_eq_one
  let φ : PowerSeries ℤ →+* PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2))
  let a : PowerSeries (ZMod 2) := φ A
  let U : PowerSeries (ZMod 2) := PowerSeries.mk (fun _ => 1)
  have hmain : ∀ k : ℕ, PowerSeries.coeff k a = 1 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      cases k with
      | zero =>
        change (Int.castRingHom (ZMod 2)) (PowerSeries.coeff 0 A) = 1
        rw [PowerSeries.coeff_zero_eq_constantCoeff, hA0, map_one]
      | succ m =>
        cases m with
        | zero =>
          change (Int.castRingHom (ZMod 2)) (PowerSeries.coeff 1 A) = 1
          rw [hA1, map_one]
        | succ j =>
          let r := j + 2
          have hr : 1 < r := by omega
          have hagree : ∀ t < r, PowerSeries.coeff t a = PowerSeries.coeff t U := by
            intro t ht
            rw [ih t ht, PowerSeries.coeff_mk]
          have ha0 : PowerSeries.constantCoeff a = 1 := by
            rw [← PowerSeries.coeff_zero_eq_constantCoeff]
            exact ih 0 (by omega)
          have hd1 := coeff_pow_diff a U r ha0 hagree (by omega) r
          have hd2 := coeff_pow_diff a U r ha0 hagree (by omega) (r + 1)
          have hrel := congrArg (Int.castRingHom (ZMod 2)) (hEq r hr)
          simp only [map_mul, map_sub, map_one, map_natCast, ← PowerSeries.coeff_map, map_pow] at hrel
          have hU1 : PowerSeries.coeff r (U ^ r) = (Nat.choose (2 * r - 1) r : ZMod 2) := by
            rw [coeff_U_pow r (by omega) r]; congr 2; omega
          have hU2 : PowerSeries.coeff r (U ^ (r + 1)) = (Nat.choose (2 * r) r : ZMod 2) := by
            rw [coeff_U_pow (r + 1) (by omega) r]; congr 2; omega
          have hzero1 : (r : ZMod 2) * PowerSeries.coeff r (U ^ r) = 0 := by
            rw [hU1, ← Nat.cast_mul]
            rcases even_n_mul_choose r (by omega) with ⟨q, hq⟩
            rw [hq, Nat.cast_add, ← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
          have hzero2 : PowerSeries.coeff r (U ^ (r + 1)) = 0 := by
            rw [hU2]
            rcases even_central_binom r (by omega) with ⟨q, hq⟩
            rw [hq, Nat.cast_add, ← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
          have ha_r : PowerSeries.coeff r (a ^ r) =
              PowerSeries.coeff r (U ^ r) + (r : ZMod 2) * (PowerSeries.coeff r a - 1) := by
            rw [PowerSeries.coeff_mk] at hd1; exact eq_add_of_sub_eq' hd1
          have ha_r1 : PowerSeries.coeff r (a ^ (r + 1)) =
              PowerSeries.coeff r (U ^ (r + 1)) + ((r + 1 : ℕ) : ZMod 2) * (PowerSeries.coeff r a - 1) := by
            rw [PowerSeries.coeff_mk] at hd2; exact eq_add_of_sub_eq' hd2
          change (r : ZMod 2) * PowerSeries.coeff r (a ^ r) =
            ((r : ZMod 2) - 1) * PowerSeries.coeff r (a ^ (r + 1)) at hrel
          rw [ha_r, ha_r1, mul_add, mul_add, hzero1, hzero2, zero_add, mul_zero, zero_add] at hrel
          have hdiff : ((r : ZMod 2) * (r : ZMod 2) - ((r : ZMod 2) - 1) * ((r + 1 : ℕ) : ZMod 2)) *
              (PowerSeries.coeff r a - 1) = 0 := by
            have : (r : ZMod 2) * ((r : ZMod 2) * (PowerSeries.coeff r a - 1)) -
                ((r : ZMod 2) - 1) * (((r + 1 : ℕ) : ZMod 2) * (PowerSeries.coeff r a - 1)) = 0 :=
              sub_eq_zero.mpr hrel
            linear_combination this
          have hcoef : (r : ZMod 2) * (r : ZMod 2) - ((r : ZMod 2) - 1) * ((r + 1 : ℕ) : ZMod 2) = 1 := by
            push_cast; ring
          rw [hcoef, one_mul] at hdiff
          exact sub_eq_zero.mp hdiff
  exact hmain n

end OMA.P_oeis_a397241

theorem OMA.solution : type_of% @OMA.S_oeis_a397241.main := OMA.P_oeis_a397241.solution
