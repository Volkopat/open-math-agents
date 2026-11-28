import OMAStatements.S_oeis_a360949
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a360949

open OMA.S_oeis_a360949

private lemma zmod2_ps_two : (2 : PowerSeries (ZMod 2)) = 0 := by
  have h : (2 : ZMod 2) = 0 := by decide
  rw [← map_ofNat (PowerSeries.C (R := ZMod 2)), h, map_zero]

private lemma zmod2_ps_add_self (f : PowerSeries (ZMod 2)) : f + f = 0 := by
  rw [← two_mul, zmod2_ps_two, zero_mul]

private lemma zmod2_ps_add_sq (f g : PowerSeries (ZMod 2)) : (f + g) ^ 2 = f ^ 2 + g ^ 2 := by
  calc (f + g) ^ 2 = f ^ 2 + 2 * (f * g) + g ^ 2 := by ring
    _ = f ^ 2 + 0 * (f * g) + g ^ 2 := by rw [zmod2_ps_two]
    _ = f ^ 2 + g ^ 2 := by ring

private lemma coeff_sq_zmod2 (f : PowerSeries (ZMod 2)) (n : ℕ) :
    PowerSeries.coeff n (f ^ 2) = if n % 2 = 0 then PowerSeries.coeff (n / 2) f else 0 := by
  rw [sq, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j f)]
  let t : ℕ → ZMod 2 := fun i => PowerSeries.coeff i f * PowerSeries.coeff (n - i) f
  have hsym : ∀ i ≤ n, t (n - i) = t i := by
    intro i hi; dsimp only [t]; rw [Nat.sub_sub_self hi, mul_comm]
  let L := (Finset.range (n + 1)).filter (fun i => i < n - i)
  let R := (Finset.range (n + 1)).filter (fun i => n - i < i)
  let M := (Finset.range (n + 1)).filter (fun i => i = n - i)
  have hpart : Finset.range (n + 1) = L ∪ (R ∪ M) := by
    ext i; simp only [L, R, M, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hi
      rcases lt_trichotomy i (n - i) with h | h | h
      · exact Or.inl ⟨hi, h⟩
      · exact Or.inr (Or.inr ⟨hi, h⟩)
      · exact Or.inr (Or.inl ⟨hi, h⟩)
    · rintro (⟨hi, _⟩ | ⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
  have hd1 : Disjoint L (R ∪ M) := by
    rw [Finset.disjoint_left]; intro i h1 h2
    simp only [L, R, M, Finset.mem_union, Finset.mem_filter] at h1 h2; omega
  have hd2 : Disjoint R M := by
    rw [Finset.disjoint_left]; intro i h1 h2
    simp only [R, M, Finset.mem_filter] at h1 h2; omega
  change ∑ i ∈ Finset.range (n + 1), t i = _
  rw [hpart, Finset.sum_union hd1, Finset.sum_union hd2]
  have hLR : ∑ i ∈ L, t i = ∑ i ∈ R, t i := by
    refine Finset.sum_bij (fun i _ => n - i) ?_ ?_ ?_ ?_
    · intro i hi; simp only [L, R, Finset.mem_filter, Finset.mem_range] at hi ⊢; omega
    · intro i hi j hj hij; simp only [L, Finset.mem_filter, Finset.mem_range] at hi hj; omega
    · intro j hj; simp only [L, R, Finset.mem_filter, Finset.mem_range] at hj ⊢
      exact ⟨n - j, ⟨by omega, by omega⟩, by omega⟩
    · intro i hi; simp only [L, Finset.mem_filter, Finset.mem_range] at hi
      exact (hsym i (by omega)).symm
  rw [← add_assoc, hLR, show ∀ x : ZMod 2, x + x = 0 from fun x => by
    rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul], zero_add]
  by_cases hev : n % 2 = 0
  · rw [if_pos hev]
    have hM : M = {n / 2} := by
      ext i; simp only [M, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]; omega
    rw [hM, Finset.sum_singleton]
    dsimp only [t]
    rw [show n - n / 2 = n / 2 by omega]
    have hsq : ∀ x : ZMod 2, x * x = x := by decide
    exact hsq _
  · rw [if_neg hev]
    have hM : M = ∅ := by
      ext i; simp only [M, Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
      omega
    rw [hM, Finset.sum_empty]

private lemma thueMorse_zero : thueMorse 0 = 0 := by
  rw [thueMorse]; simp

private lemma thueMorse_two_mul (k : ℕ) : thueMorse (2 * k) = thueMorse k := by
  cases k with
  | zero => simp [thueMorse_zero]
  | succ m =>
    conv_lhs => rw [thueMorse]
    rw [if_neg (by omega), show (2 * (m + 1)) % 2 = 0 by omega,
        show (2 * (m + 1)) / 2 = m + 1 by omega, zero_add]
    have hlt : thueMorse (m + 1) < 2 := by
      rw [thueMorse]; rw [if_neg (by omega)]; exact Nat.mod_lt _ (by omega)
    exact Nat.mod_eq_of_lt hlt

private lemma thueMorse_two_mul_add_one (k : ℕ) :
    thueMorse (2 * k + 1) = (thueMorse k + 1) % 2 := by
  conv_lhs => rw [thueMorse]
  rw [if_neg (by omega), show (2 * k + 1) % 2 = 1 by omega,
      show (2 * k + 1) / 2 = k by omega, add_comm]

private lemma thueMorse_lt_two (n : ℕ) : thueMorse n < 2 := by
  rw [thueMorse]
  split_ifs
  · omega
  · exact Nat.mod_lt _ (by omega)

private lemma thueMorse_zmod2 (n : ℕ) :
    ((thueMorse n : ℕ) : ZMod 2) ≠ ((thueMorse (n + 2) : ℕ) : ZMod 2) ↔
      thueMorse n ≠ thueMorse (n + 2) := by
  have h1 := thueMorse_lt_two n
  have h2 := thueMorse_lt_two (n + 2)
  constructor
  · intro h heq; exact h (congrArg _ heq)
  · intro h heq
    have : thueMorse n % 2 = thueMorse (n + 2) % 2 := by
      have hc := (ZMod.natCast_eq_natCast_iff' (thueMorse n) (thueMorse (n + 2)) 2).mp heq
      exact hc
    omega

private lemma pow_div_two_series (B : PowerSeries ℤ) (n : ℕ) (hn : 1 ≤ n) :
    ∃ Q : PowerSeries ℤ,
      (1 + 2 * B) ^ n + (-1 : PowerSeries ℤ) ^ n = 2 * Q ∧
      PowerSeries.map (Int.castRingHom (ZMod 2)) Q =
        if n % 2 = 0 then 1 else PowerSeries.map (Int.castRingHom (ZMod 2)) B := by
  let φ : PowerSeries ℤ →+* PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2))
  have h2 : (2 : PowerSeries (ZMod 2)) = 0 := zmod2_ps_two
  -- Expand (1 + 2*B)^n = 1 + 2*n*B + 4*R
  have hexp : ∃ R : PowerSeries ℤ, (1 + 2 * B) ^ n = 1 + 2 * (n : PowerSeries ℤ) * B + 4 * R := by
    clear hn
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      rcases ih with ⟨R, hR⟩
      refine ⟨(k : PowerSeries ℤ) * B ^ 2 + R * (1 + 2 * B), ?_⟩
      rw [pow_succ, hR]; push_cast; ring
  rcases hexp with ⟨R, hR⟩
  by_cases hev : n % 2 = 0
  · have hneg : (-1 : PowerSeries ℤ) ^ n = 1 := by
      rcases Nat.even_iff.mpr hev with ⟨m, rfl⟩
      rw [← two_mul, pow_mul, neg_one_sq, one_pow]
    refine ⟨1 + (n : PowerSeries ℤ) * B + 2 * R, ?_, ?_⟩
    · rw [hR, hneg]; ring
    · rw [if_pos hev, map_add, map_add, map_one, map_mul, map_mul, map_natCast, map_ofNat, h2,
          zero_mul, add_zero]
      have hn0 : (n : PowerSeries (ZMod 2)) = 0 := by
        rcases Nat.even_iff.mpr hev with ⟨m, rfl⟩
        rw [Nat.cast_add, ← two_mul, h2, zero_mul]
      rw [hn0, zero_mul, add_zero]
  · have hneg : (-1 : PowerSeries ℤ) ^ n = -1 := by
      have hodd : Odd n := Nat.odd_iff.mpr (by omega)
      exact Odd.neg_one_pow hodd
    refine ⟨(n : PowerSeries ℤ) * B + 2 * R, ?_, ?_⟩
    · rw [hR, hneg]; ring
    · rw [if_neg hev, map_add, map_mul, map_mul, map_natCast, map_ofNat, h2, zero_mul, add_zero]
      have hn1 : (n : PowerSeries (ZMod 2)) = 1 := by
        have hodd : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
        rcases hodd with ⟨m, rfl⟩
        rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, h2, zero_mul, zero_add, Nat.cast_one]
      rw [hn1, one_mul]

theorem solution : type_of% @OMA.S_oeis_a360949.main := by
  intro A hA0 hEq
  -- Step 1: Prove by strong induction that coeff k A is even for all k ≥ 1
  have heven : ∀ k : ℕ, 1 ≤ k → (2 : ℤ) ∣ PowerSeries.coeff k A := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      have hA_mod2 : ∀ j < k, PowerSeries.coeff j (A - 1) % 2 = 0 := by
        intro j hj
        cases j with
        | zero =>
          rw [map_sub, PowerSeries.coeff_zero_eq_constantCoeff, hA0, map_one, sub_self]; rfl
        | succ m =>
          rw [map_sub, PowerSeries.coeff_one, if_neg (by omega), sub_zero]
          exact Int.emod_eq_zero_of_dvd (ih (m + 1) hj (by omega))
      -- Every power A^n + (-1)^n has even coefficients for degrees < k!
      have hpow_even : ∀ n : ℕ, 1 ≤ n → ∀ j < k,
          (2 : ℤ) ∣ PowerSeries.coeff j (A ^ n + (-1 : PowerSeries ℤ) ^ n) := by
        intro n hn
        have hAn : ∀ m : ℕ, ∀ j < k, PowerSeries.coeff j (A ^ m - 1) % 2 = 0 := by
          intro m
          induction m with
          | zero => intro j _; simp
          | succ t iht =>
            intro j hj
            have hdecomp : A ^ (t + 1) - 1 = (A ^ t - 1) * A + (A - 1) := by ring
            rw [hdecomp, map_add, PowerSeries.coeff_mul]
            have h1 : (2 : ℤ) ∣ ∑ p ∈ Finset.antidiagonal j,
                PowerSeries.coeff p.1 (A ^ t - 1) * PowerSeries.coeff p.2 A := by
              refine Finset.dvd_sum fun p hp => ?_
              have hp1 : p.1 < k := by have := Finset.mem_antidiagonal.mp hp; omega
              exact dvd_mul_of_dvd_left (Int.dvd_of_emod_eq_zero (iht p.1 hp1)) _
            have h2 : (2 : ℤ) ∣ PowerSeries.coeff j (A - 1) :=
              Int.dvd_of_emod_eq_zero (hA_mod2 j hj)
            exact Int.emod_eq_zero_of_dvd (dvd_add h1 h2)
        intro j hj
        have hdecomp : A ^ n + (-1 : PowerSeries ℤ) ^ n = (A ^ n - 1) + (1 + (-1 : PowerSeries ℤ) ^ n) := by
          ring
        rw [hdecomp, map_add]
        refine dvd_add (Int.dvd_of_emod_eq_zero (hAn n j hj)) ?_
        rcases Nat.even_or_odd n with ⟨m, rfl⟩ | hodd
        · rw [← two_mul, pow_mul, neg_one_sq, one_pow, map_add, PowerSeries.coeff_one]
          split_ifs <;> decide
        · rw [Odd.neg_one_pow hodd, add_neg_cancel, map_zero]; exact dvd_zero 2
      -- Hence for n ≥ 2, 2^n divides coeff (k + 1 - n) ((A^n + (-1)^n)^n)
      have hdvd_pow : ∀ (f : PowerSeries ℤ) (m : ℕ), (∀ j < k, (2 : ℤ) ∣ PowerSeries.coeff j f) →
          ∀ (e : ℕ) (j : ℕ), j < k → (2 : ℤ) ^ e ∣ PowerSeries.coeff j (f ^ e) := by
        intro f _ hf e
        induction e with
        | zero => intro j _; simp
        | succ t iht =>
          intro j hj
          rw [pow_succ, pow_succ, PowerSeries.coeff_mul]
          refine Finset.dvd_sum fun p hp => ?_
          have hp1 : p.1 < k := by have := Finset.mem_antidiagonal.mp hp; omega
          have hp2 : p.2 < k := by have := Finset.mem_antidiagonal.mp hp; omega
          exact mul_dvd_mul (iht p.1 hp1) (hf p.2 hp2)
      have hr := hEq (k + 1)
      rw [if_neg (by omega), Finset.sum_range_succ', Finset.sum_range_succ'] at hr
      -- n = 0 term: coeff (k+1) 1 = 0; n = 1 term: 2^k * (-1) * coeff k (A - 1) = -2^k * coeff k A
      have hn0 : (2 : ℤ) ^ (k + 1 - 0) * (-1 : ℤ) ^ 0 *
          PowerSeries.coeff (k + 1) (PowerSeries.X ^ 0 * (A ^ 0 + (-1 : PowerSeries ℤ) ^ 0) ^ 0) = 0 := by
        simp [PowerSeries.coeff_one]
      have hn1 : (2 : ℤ) ^ (k + 1 - 1) * (-1 : ℤ) ^ 1 *
          PowerSeries.coeff (k + 1) (PowerSeries.X ^ 1 * (A ^ 1 + (-1 : PowerSeries ℤ) ^ 1) ^ 1) =
          -(2 : ℤ) ^ k * PowerSeries.coeff k A := by
        rw [Nat.add_sub_cancel, PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel,
            pow_one, pow_one, pow_one, pow_one, map_add, map_neg, PowerSeries.coeff_one,
            if_neg (by omega), neg_zero, add_zero]
        ring
      rw [hn0, add_zero, hn1] at hr
      have htail : (2 : ℤ) ^ (k + 1) ∣ ∑ x ∈ Finset.range k,
          (2 : ℤ) ^ (k + 1 - (x + 2)) * (-1 : ℤ) ^ (x + 2) *
            PowerSeries.coeff (k + 1)
              (PowerSeries.X ^ (x + 2) * (A ^ (x + 2) + (-1 : PowerSeries ℤ) ^ (x + 2)) ^ (x + 2)) := by
        refine Finset.dvd_sum fun x hx => ?_
        have hxk : x < k := Finset.mem_range.mp hx
        rw [PowerSeries.coeff_X_pow_mul']
        split_ifs with hle
        · have hd := hdvd_pow (A ^ (x + 2) + (-1 : PowerSeries ℤ) ^ (x + 2)) 0
            (hpow_even (x + 2) (by omega)) (x + 2) (k + 1 - (x + 2)) (by omega)
          rcases hd with ⟨q, hq⟩
          refine ⟨(-1 : ℤ) ^ (x + 2) * q, ?_⟩
          rw [hq, show (2 : ℤ) ^ (k + 1 - (x + 2)) * (-1 : ℤ) ^ (x + 2) * ((2 : ℤ) ^ (x + 2) * q) =
              ((2 : ℤ) ^ (k + 1 - (x + 2)) * (2 : ℤ) ^ (x + 2)) * ((-1 : ℤ) ^ (x + 2) * q) by ring,
              ← pow_add, Nat.sub_add_cancel hle]
        · rw [mul_zero]; exact dvd_zero _
      rcases htail with ⟨q, hq⟩
      rw [hq] at hr
      have hmul : (2 : ℤ) ^ k * PowerSeries.coeff k A = (2 : ℤ) ^ k * (2 * q) := by
        rw [pow_succ] at hr; linarith
      have hpos : (2 : ℤ) ^ k ≠ 0 := by positivity
      exact ⟨q, mul_left_cancel₀ hpos hmul⟩
  -- Step 2: Write A = 1 + 2 * B where B ∈ ℤ[[x]] with B(0) = 0
  let B : PowerSeries ℤ := PowerSeries.mk (fun k => if k = 0 then 0 else PowerSeries.coeff k A / 2)
  have hAB : A = 1 + 2 * B := by
    ext k
    rw [map_add, show (2 : PowerSeries ℤ) * B = PowerSeries.C 2 * B by simp,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_one, PowerSeries.coeff_mk]
    cases k with
    | zero =>
      simp only [↓reduceIte, mul_zero, add_zero]
      rw [PowerSeries.coeff_zero_eq_constantCoeff, hA0]
    | succ m =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, zero_add]
      exact (Int.mul_ediv_cancel' (heven (m + 1) (by omega))).symm
  -- Step 3: Reduce the equation mod 2 to get b = X + X^2 * b + X^3 * b^2 in ZMod 2[[x]]
  let φ : PowerSeries ℤ →+* PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2))
  let b : PowerSeries (ZMod 2) := φ B
  have hb0 : PowerSeries.coeff 0 b = 0 := by
    change (Int.castRingHom (ZMod 2)) (PowerSeries.coeff 0 B) = 0
    simp [B, PowerSeries.coeff_mk]
  have hbeq : ∀ r : ℕ, 1 ≤ r →
      PowerSeries.coeff r b =
        (if r = 1 then (1 : ZMod 2) else 0) +
        (if 2 ≤ r then PowerSeries.coeff (r - 2) b else 0) +
        (if 3 ≤ r then PowerSeries.coeff (r - 3) (b ^ 2) else 0) := by
    -- Actually prove from hEq (r + 1) by dividing by 2^(r+1) and reducing mod 2!
    -- Wait: let's prove b * (1 + X^2) = X * (1 + X^2 * b^2) directly from the sum!
    -- For any r ≥ 1, in hEq r:
    -- 0 = ∑_{n=1}^r (-1)^n * coeff r (X^n * Q_n^n), so in ZMod 2:
    -- 0 = ∑_{n=1}^r coeff (r - n) ((φ Q_n)^n)
    --   = ∑_{2≤n≤r, even} coeff (r - n) 1 + ∑_{1≤n≤r, odd} coeff (r - n) (b^n)
    --   = [r even, r ≥ 2] + ∑_{m, 2m+1 ≤ r} coeff (r - 2m - 1) (b^(2m+1)).
    -- Multiply by (1 + X^2 * b^2) and (1 + X^2)!
    -- Even cleaner: prove the power series identity in PowerSeries (ZMod 2) directly!
    intro r hr
    have hsum0 : ∀ m : ℕ, 1 ≤ m →
        ∑ n ∈ Finset.Icc 1 m,
          PowerSeries.coeff (m - n) (if n % 2 = 0 then (1 : PowerSeries (ZMod 2)) else b ^ n) = 0 := by
      intro m hm
      have hraw := hEq m
      rw [if_neg (by omega), Finset.sum_range_succ'] at hraw
      have hn0 : (2 : ℤ) ^ (m - 0) * (-1 : ℤ) ^ 0 *
          PowerSeries.coeff m (PowerSeries.X ^ 0 * (A ^ 0 + (-1 : PowerSeries ℤ) ^ 0) ^ 0) = 0 := by
        simp [PowerSeries.coeff_one, if_neg (by omega : m ≠ 0)]
      rw [hn0, add_zero] at hraw
      -- Factor out 2^m from each term n ∈ [1, m]
      have hchoose : ∀ n ∈ Finset.range m,
          ∃ q : ℤ,
            (2 : ℤ) ^ (m - (n + 1)) * (-1 : ℤ) ^ (n + 1) *
              PowerSeries.coeff m
                (PowerSeries.X ^ (n + 1) * (A ^ (n + 1) + (-1 : PowerSeries ℤ) ^ (n + 1)) ^ (n + 1)) =
            (2 : ℤ) ^ m * q ∧
            (Int.castRingHom (ZMod 2)) q =
              PowerSeries.coeff (m - (n + 1))
                (if (n + 1) % 2 = 0 then (1 : PowerSeries (ZMod 2)) else b ^ (n + 1)) := by
        intro n hn
        have hnm : n + 1 ≤ m := by have := Finset.mem_range.mp hn; omega
        rcases pow_div_two_series B (n + 1) (by omega) with ⟨Q, hQ1, hQ2⟩
        refine ⟨(-1 : ℤ) ^ (n + 1) * PowerSeries.coeff (m - (n + 1)) (Q ^ (n + 1)), ?_, ?_⟩
        · rw [hAB, hQ1, mul_pow, PowerSeries.coeff_X_pow_mul', if_pos hnm,
              show ((2 : PowerSeries ℤ) ^ (n + 1) * Q ^ (n + 1)) =
                  PowerSeries.C ((2 : ℤ) ^ (n + 1)) * Q ^ (n + 1) by simp,
              PowerSeries.coeff_C_mul]
          rw [show (2 : ℤ) ^ (m - (n + 1)) * (-1 : ℤ) ^ (n + 1) *
              ((2 : ℤ) ^ (n + 1) * PowerSeries.coeff (m - (n + 1)) (Q ^ (n + 1))) =
              ((2 : ℤ) ^ (m - (n + 1)) * (2 : ℤ) ^ (n + 1)) *
                ((-1 : ℤ) ^ (n + 1) * PowerSeries.coeff (m - (n + 1)) (Q ^ (n + 1))) by ring,
              ← pow_add, Nat.sub_add_cancel hnm]
        · rw [map_mul, map_pow, map_neg, map_one, show (-1 : ZMod 2) = 1 by decide, one_pow,
              one_mul, ← PowerSeries.coeff_map, map_pow, hQ2]
          split_ifs with hpar
          · rw [one_pow]
          · rfl
      choose q hq1 hq2 using hchoose
      have hsum_eq : ∑ n ∈ Finset.range m,
          (2 : ℤ) ^ (m - (n + 1)) * (-1 : ℤ) ^ (n + 1) *
            PowerSeries.coeff m
              (PowerSeries.X ^ (n + 1) * (A ^ (n + 1) + (-1 : PowerSeries ℤ) ^ (n + 1)) ^ (n + 1)) =
          (2 : ℤ) ^ m * ∑ n ∈ Finset.range m, if hn : n ∈ Finset.range m then q n hn else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [dif_pos hn, hq1 n hn]
      rw [hsum_eq] at hraw
      have hqzero : ∑ n ∈ Finset.range m, (if hn : n ∈ Finset.range m then q n hn else 0) = 0 := by
        have hpos : (2 : ℤ) ^ m ≠ 0 := by positivity
        exact mul_left_cancel₀ hpos (by linarith)
      have hcast := congrArg (Int.castRingHom (ZMod 2)) hqzero
      rw [map_sum, map_zero] at hcast
      rw [← hcast]
      refine Finset.sum_bij (fun n _ => n - 1) ?_ ?_ ?_ ?_
      · intro n hn; simp only [Finset.mem_Icc, Finset.mem_range] at hn ⊢; omega
      · intro n1 hn1 n2 hn2 h; simp only [Finset.mem_Icc] at hn1 hn2; omega
      · intro n hn; simp only [Finset.mem_range, Finset.mem_Icc] at hn ⊢
        exact ⟨n + 1, by omega, by omega⟩
      · intro n hn; simp only [Finset.mem_Icc] at hn
        have hmem : n - 1 ∈ Finset.range m := Finset.mem_range.mpr (by omega)
        rw [dif_pos hmem, hq2 (n - 1) hmem, Nat.sub_add_cancel hn.1]
    -- Now use hsum0 at m = r + 1 and m = r - 1 (when r ≥ 2), or directly the power series identity:
    -- Let S = ∑_{k≥1} (X^(2k) + X^(2k-1) * b^(2k-1)) = 0 in ZMod 2[[x]]!
    have hS : ∀ m : ℕ, 1 ≤ m →
        PowerSeries.coeff m (PowerSeries.X ^ 2 * PowerSeries.mk (fun k => if k % 2 = 0 then (1 : ZMod 2) else 0)) +
        ∑ k ∈ Finset.range ((m + 1) / 2), PowerSeries.coeff (m - (2 * k + 1)) (b ^ (2 * k + 1)) = 0 := by
      intro m hm
      have h0 := hsum0 m hm
      -- Split Icc 1 m into even and odd
      have hsplit : ∑ n ∈ Finset.Icc 1 m,
          PowerSeries.coeff (m - n) (if n % 2 = 0 then (1 : PowerSeries (ZMod 2)) else b ^ n) =
          (∑ n ∈ (Finset.Icc 1 m).filter (fun n => n % 2 = 0), PowerSeries.coeff (m - n) (1 : PowerSeries (ZMod 2))) +
          (∑ n ∈ (Finset.Icc 1 m).filter (fun n => n % 2 ≠ 0), PowerSeries.coeff (m - n) (b ^ n)) := by
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 m) (fun n => n % 2 = 0)]
        congr 1
        · refine Finset.sum_congr rfl fun n hn => ?_
          rw [if_pos (Finset.mem_filter.mp hn).2]
        · refine Finset.sum_congr rfl fun n hn => ?_
          rw [if_neg (Finset.mem_filter.mp hn).2]
      rw [hsplit] at h0
      conv_rhs => rw [← h0]
      congr 1
      · rw [PowerSeries.coeff_X_pow_mul']
        by_cases h2m : 2 ≤ m
        · rw [if_pos h2m, PowerSeries.coeff_mk]
          by_cases hmev : m % 2 = 0
          · rw [if_pos (by omega)]
            rw [Finset.sum_eq_single m]
            · simp [PowerSeries.coeff_one]
            · intro n hn hne
              have hn1 := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
              rw [PowerSeries.coeff_one, if_neg (by omega)]
            · intro h; exfalso; apply h
              simp only [Finset.mem_filter, Finset.mem_Icc]; omega
          · rw [if_neg (by omega)]
            symm; refine Finset.sum_eq_zero fun n hn => ?_
            have hnf := Finset.mem_filter.mp hn
            have hn1 := Finset.mem_Icc.mp hnf.1
            rw [PowerSeries.coeff_one, if_neg (by omega)]
        · rw [if_neg h2m]
          symm; refine Finset.sum_eq_zero fun n hn => ?_
          have hnf := Finset.mem_filter.mp hn
          have hn1 := Finset.mem_Icc.mp hnf.1
          omega
      · symm
        refine Finset.sum_bij (fun n _ => n / 2) ?_ ?_ ?_ ?_
        · intro n hn; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hn ⊢; omega
        · intro n1 hn1 n2 hn2 h; simp only [Finset.mem_filter, Finset.mem_Icc] at hn1 hn2; omega
        · intro k hk; simp only [Finset.mem_range, Finset.mem_filter, Finset.mem_Icc] at hk ⊢
          exact ⟨2 * k + 1, ⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩
        · intro n hn; simp only [Finset.mem_filter, Finset.mem_Icc] at hn
          have hne : 2 * (n / 2) + 1 = n := by omega
          rw [hne]
    -- Define G = ∑_{k≥0} X^(2k+1) * b^(2k+1) and E = ∑_{k≥1} X^(2k)
    -- Wait: G = X * b + X^2 * b^2 * G, and E + G = 0 => G = E = X^2 / (1 + X^2)!
    -- So (1 + X^2) * G = X^2 and (1 + X^2 * b^2) * G = X * b!
    -- Therefore X * b * (1 + X^2) = X^2 * (1 + X^2 * b^2), cancel X => b*(1+X^2) = X*(1+X^2*b^2)!
    let E : PowerSeries (ZMod 2) :=
      PowerSeries.X ^ 2 * PowerSeries.mk (fun k => if k % 2 = 0 then 1 else 0)
    let G : PowerSeries (ZMod 2) :=
      PowerSeries.mk (fun m => ∑ k ∈ Finset.range ((m + 1) / 2),
        PowerSeries.coeff (m - (2 * k + 1)) (b ^ (2 * k + 1)))
    have hGE : G = E := by
      ext m
      cases m with
      | zero =>
        simp [G, E, PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul']
      | succ t =>
        have h := hS (t + 1) (by omega)
        have hadd : PowerSeries.coeff (t + 1) E + PowerSeries.coeff (t + 1) G = 0 := by
          simpa [E, G, PowerSeries.coeff_mk] using h
        have h2 : ∀ x y : ZMod 2, x + y = 0 → y = x := by decide
        exact h2 _ _ hadd
    have hE_eq : (1 + PowerSeries.X ^ 2) * E = PowerSeries.X ^ 2 := by
      ext m
      rw [add_mul, one_mul, map_add, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul',
          PowerSeries.coeff_X_pow]
      dsimp only [E]
      rw [PowerSeries.coeff_X_pow_mul']
      split_ifs with h1 h2 h3 <;> simp_all [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk] <;>
        try omega
      all_goals
        split_ifs <;> first | decide | omega
    have hG_eq : G = PowerSeries.X * b + PowerSeries.X ^ 2 * b ^ 2 * G := by
      ext m
      rw [map_add]
      cases m with
      | zero =>
        simp [G, PowerSeries.coeff_mk]
      | succ t =>
        conv_rhs =>
          arg 1
          rw [← pow_one (PowerSeries.X : PowerSeries (ZMod 2)), PowerSeries.coeff_X_pow_mul',
              if_pos (by omega), Nat.add_sub_cancel]
        rw [show PowerSeries.X ^ 2 * b ^ 2 * G = PowerSeries.X ^ 2 * (b ^ 2 * G) by ring,
            PowerSeries.coeff_X_pow_mul']
        dsimp only [G]
        rw [PowerSeries.coeff_mk]
        cases t with
        | zero =>
          simp
        | succ s =>
          rw [if_pos (by omega : 2 ≤ s + 2), show s + 2 - 2 = s by omega]
          have hrange : (s + 2 + 1) / 2 = (s + 1) / 2 + 1 := by omega
          rw [hrange, Finset.sum_range_succ']
          conv_lhs => rw [add_comm]
          simp only [Nat.mul_zero, zero_add, pow_one, show s + 2 - 1 = s + 1 by omega]
          congr 1
          rw [PowerSeries.coeff_mul]
          have hswap : ∑ p ∈ Finset.antidiagonal s,
              PowerSeries.coeff p.1 (b ^ 2) *
                ∑ k ∈ Finset.range ((p.2 + 1) / 2),
                  PowerSeries.coeff (p.2 - (2 * k + 1)) (b ^ (2 * k + 1)) =
              ∑ k ∈ Finset.range ((s + 1) / 2),
                PowerSeries.coeff (s - (2 * k + 1)) (b ^ (2 * (k + 1) + 1)) := by
            have h1 : ∀ p ∈ Finset.antidiagonal s,
                PowerSeries.coeff p.1 (b ^ 2) *
                  ∑ k ∈ Finset.range ((p.2 + 1) / 2),
                    PowerSeries.coeff (p.2 - (2 * k + 1)) (b ^ (2 * k + 1)) =
                ∑ k ∈ Finset.range ((s + 1) / 2),
                  if 2 * k + 1 ≤ p.2 then
                    PowerSeries.coeff p.1 (b ^ 2) *
                      PowerSeries.coeff (p.2 - (2 * k + 1)) (b ^ (2 * k + 1))
                  else 0 := by
              intro p hp
              have hp2 : p.2 ≤ s := by have := Finset.mem_antidiagonal.mp hp; omega
              rw [Finset.mul_sum]
              rw [← Finset.sum_filter]
              have hfilt : (Finset.range ((s + 1) / 2)).filter (fun k => 2 * k + 1 ≤ p.2) =
                  Finset.range ((p.2 + 1) / 2) := by
                ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
              rw [hfilt]
            rw [Finset.sum_congr rfl h1, Finset.sum_comm]
            refine Finset.sum_congr rfl fun k hk => ?_
            have hk_le : 2 * k + 1 ≤ s := by have := Finset.mem_range.mp hk; omega
            rw [show 2 * (k + 1) + 1 = 2 + (2 * k + 1) by omega]
            conv_rhs => rw [pow_add, PowerSeries.coeff_mul]
            rw [← Finset.sum_filter]
            refine Finset.sum_bij (fun p _ => (p.1, p.2 - (2 * k + 1))) ?_ ?_ ?_ ?_
            · intro p hp
              simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp ⊢; omega
            · intro p1 hp1 p2 hp2 h
              simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp1 hp2
              have h1' := congrArg Prod.fst h
              have h2' := congrArg Prod.snd h
              exact Prod.ext h1' (by omega)
            · intro q hq
              simp only [Finset.mem_antidiagonal] at hq
              refine ⟨(q.1, q.2 + (2 * k + 1)), ?_, ?_⟩
              · simp only [Finset.mem_filter, Finset.mem_antidiagonal]; omega
              · simp
            · intro p _; rfl
          symm
          simp only [PowerSeries.coeff_mk]
          rw [hswap]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [show s + 1 + 1 - (2 * (k + 1) + 1) = s - (2 * k + 1) by omega]
    -- Derive b = X + X^2 * b + X^3 * b^2 from (1 + X^2) * G = X^2 and (1 + X^2 * b^2) * G = X * b
    have hG_lin : (1 + PowerSeries.X ^ 2 * b ^ 2) * G = PowerSeries.X * b := by
      have h1 : G + PowerSeries.X ^ 2 * b ^ 2 * G =
          PowerSeries.X * b + (PowerSeries.X ^ 2 * b ^ 2 * G + PowerSeries.X ^ 2 * b ^ 2 * G) := by
        calc G + PowerSeries.X ^ 2 * b ^ 2 * G
            = (PowerSeries.X * b + PowerSeries.X ^ 2 * b ^ 2 * G) + PowerSeries.X ^ 2 * b ^ 2 * G := by
              rw [← hG_eq]
          _ = PowerSeries.X * b + (PowerSeries.X ^ 2 * b ^ 2 * G + PowerSeries.X ^ 2 * b ^ 2 * G) := by
              ring
      rw [zmod2_ps_add_self, add_zero] at h1
      rw [add_mul, one_mul]; exact h1
    have hXmul : PowerSeries.X * b * (1 + PowerSeries.X ^ 2) =
        PowerSeries.X ^ 2 * (1 + PowerSeries.X ^ 2 * b ^ 2) := by
      calc PowerSeries.X * b * (1 + PowerSeries.X ^ 2)
          = (1 + PowerSeries.X ^ 2 * b ^ 2) * ((1 + PowerSeries.X ^ 2) * G) := by
            rw [← hG_lin]; ring
        _ = (1 + PowerSeries.X ^ 2 * b ^ 2) * PowerSeries.X ^ 2 := by rw [hGE, hE_eq]
        _ = PowerSeries.X ^ 2 * (1 + PowerSeries.X ^ 2 * b ^ 2) := by ring
    have hbeq_ps : b = PowerSeries.X + PowerSeries.X ^ 2 * b + PowerSeries.X ^ 3 * b ^ 2 := by
      have h1 : PowerSeries.X * (b * (1 + PowerSeries.X ^ 2)) =
          PowerSeries.X * (PowerSeries.X * (1 + PowerSeries.X ^ 2 * b ^ 2)) := by
        rw [← mul_assoc, hXmul]; ring
      have h2 : b * (1 + PowerSeries.X ^ 2) = PowerSeries.X * (1 + PowerSeries.X ^ 2 * b ^ 2) := by
        ext m
        have hm := congrArg (PowerSeries.coeff (m + 1)) h1
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul] at hm
        exact hm
      have h3 : b + PowerSeries.X ^ 2 * b = PowerSeries.X + PowerSeries.X ^ 3 * b ^ 2 := by
        calc b + PowerSeries.X ^ 2 * b = b * (1 + PowerSeries.X ^ 2) := by ring
          _ = PowerSeries.X * (1 + PowerSeries.X ^ 2 * b ^ 2) := h2
          _ = PowerSeries.X + PowerSeries.X ^ 3 * b ^ 2 := by ring
      calc b = (b + PowerSeries.X ^ 2 * b) + PowerSeries.X ^ 2 * b := by
            rw [add_assoc, zmod2_ps_add_self, add_zero]
        _ = (PowerSeries.X + PowerSeries.X ^ 3 * b ^ 2) + PowerSeries.X ^ 2 * b := by rw [h3]
        _ = PowerSeries.X + PowerSeries.X ^ 2 * b + PowerSeries.X ^ 3 * b ^ 2 := by ring
    have hc := congrArg (PowerSeries.coeff r) hbeq_ps
    rw [map_add, map_add, PowerSeries.coeff_X, PowerSeries.coeff_X_pow_mul',
        PowerSeries.coeff_X_pow_mul'] at hc
    exact hc
  -- Step 4: Define the Thue-Morse series B0 and verify B0 = X + X^2 * B0 + X^3 * B0^2
  let B0 : PowerSeries (ZMod 2) := PowerSeries.mk (fun k =>
    if k % 2 = 1 then ((thueMorse (k / 2) : ZMod 2) + (thueMorse (k / 2 + 2) : ZMod 2)) else 0)
  have hB0_eq : ∀ r : ℕ, 1 ≤ r →
      PowerSeries.coeff r B0 =
        (if r = 1 then (1 : ZMod 2) else 0) +
        (if 2 ≤ r then PowerSeries.coeff (r - 2) B0 else 0) +
        (if 3 ≤ r then PowerSeries.coeff (r - 3) (B0 ^ 2) else 0) := by
    intro r hr
    by_cases hpar : r % 2 = 0
    · -- Even r ≥ 2
      have h1 : PowerSeries.coeff r B0 = 0 := by simp [B0, PowerSeries.coeff_mk, hpar]
      rw [h1, if_neg (by omega), zero_add, if_pos (by omega)]
      have h2 : PowerSeries.coeff (r - 2) B0 = 0 := by
        simp [B0, PowerSeries.coeff_mk, show (r - 2) % 2 = 0 by omega]
      rw [h2, zero_add]
      split_ifs with h3
      · rw [coeff_sq_zmod2, if_neg (by omega)]
      · rfl
    · -- Odd r = 2*n + 1
      have hr_odd : r % 2 = 1 := by omega
      cases r with
      | zero => omega
      | succ m =>
        cases m with
        | zero =>
          simp only [B0, PowerSeries.coeff_mk, ↓reduceIte, Nat.zero_add]
          have htm0 : thueMorse 0 = 0 := thueMorse_zero
          have htm2 : thueMorse 2 = 1 := by
            rw [show (2 : ℕ) = 2 * 1 by rfl, thueMorse_two_mul,
                show (1 : ℕ) = 2 * 0 + 1 by rfl, thueMorse_two_mul_add_one, thueMorse_zero]
          simp [htm0, htm2]
        | succ m' =>
          have h2le : 2 ≤ m' + 2 := by omega
          have h3le : 3 ≤ m' + 2 := by omega
          rw [if_neg (by omega), zero_add, if_pos h2le, if_pos h3le, coeff_sq_zmod2]
          have hsub3_even : (m' + 2 - 3) % 2 = 0 := by omega
          rw [if_pos hsub3_even]
          set n := (m' + 2) / 2
          have hn1 : 1 ≤ n := by omega
          have hr_eq : m' + 2 = 2 * n + 1 := by omega
          simp only [B0, PowerSeries.coeff_mk, hr_eq]
          rw [show 2 * n + 1 - 2 = 2 * (n - 1) + 1 by omega,
              show (2 * n + 1 - 3) / 2 = n - 1 by omega]
          have hodd1 : (2 * n + 1) % 2 = 1 := by omega
          have hodd2 : (2 * (n - 1) + 1) % 2 = 1 := by omega
          have hdiv1 : (2 * n + 1) / 2 = n := by omega
          have hdiv2 : (2 * (n - 1) + 1) / 2 = n - 1 := by omega
          rw [if_pos hodd1, if_pos hodd2, hdiv1, hdiv2]
          -- Helper: tm(2*j) = tm(j) and tm(2*j+1) = tm(j) + 1 in ZMod 2
          have htm_even : ∀ j : ℕ, (thueMorse (2 * j) : ZMod 2) = (thueMorse j : ZMod 2) := by
            intro j; rw [thueMorse_two_mul]
          have htm_odd : ∀ j : ℕ, (thueMorse (2 * j + 1) : ZMod 2) = (thueMorse j : ZMod 2) + 1 := by
            intro j; rw [thueMorse_two_mul_add_one]
            have hlt := thueMorse_lt_two j
            rcases (show thueMorse j = 0 ∨ thueMorse j = 1 by omega) with h0 | h1
            · rw [h0]; decide
            · rw [h1]; decide
          rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
          · -- n = 2*j (j ≥ 1)
            have hj1 : 1 ≤ j := by omega
            have hn_eq : n = 2 * j := by omega
            have hnm1 : n - 1 = 2 * (j - 1) + 1 := by omega
            rw [if_pos (by omega : (n - 1) % 2 = 1)]
            have hdiv3 : (n - 1) / 2 = j - 1 := by omega
            rw [hdiv3, hnm1, hn_eq,
                show 2 * j + 2 = 2 * (j + 1) by omega,
                show 2 * (j - 1) + 1 + 2 = 2 * j + 1 by omega,
                show j - 1 + 2 = j + 1 by omega,
                htm_even, htm_even, htm_odd, htm_odd]
            have h2z : ∀ x : ZMod 2, x + x = 0 := by decide
            have h11 : (1 : ZMod 2) + 1 = 0 := by decide
            calc ((thueMorse j : ZMod 2) + (thueMorse (j + 1) : ZMod 2))
                = ((thueMorse (j - 1) : ZMod 2) + (thueMorse (j - 1) : ZMod 2)) +
                  ((1 : ZMod 2) + 1) +
                  ((thueMorse j : ZMod 2) + (thueMorse (j + 1) : ZMod 2)) := by
                  rw [h2z, h11, zero_add, zero_add]
              _ = (((thueMorse (j - 1) : ZMod 2) + 1) + ((thueMorse j : ZMod 2) + 1)) +
                  ((thueMorse (j - 1) : ZMod 2) + (thueMorse (j + 1) : ZMod 2)) := by ring
          · -- n = 2*j + 1
            have hn_eq : n = 2 * j + 1 := by omega
            have hnm1 : n - 1 = 2 * j := by omega
            rw [if_neg (by omega : ¬ (n - 1) % 2 = 1), add_zero, hnm1, hn_eq,
                show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by omega,
                show 2 * j + 2 = 2 * (j + 1) by omega,
                htm_odd, htm_odd, htm_even, htm_even]
            have h11 : (1 : ZMod 2) + 1 = 0 := by decide
            calc ((thueMorse j : ZMod 2) + 1) + ((thueMorse (j + 1) : ZMod 2) + 1)
                = (thueMorse j : ZMod 2) + (thueMorse (j + 1) : ZMod 2) + ((1 : ZMod 2) + 1) := by ring
              _ = (thueMorse j : ZMod 2) + (thueMorse (j + 1) : ZMod 2) := by rw [h11, add_zero]
  -- Step 5: By strong induction, coeff r b = coeff r B0 for all r
  have hb_eq_B0 : ∀ r : ℕ, PowerSeries.coeff r b = PowerSeries.coeff r B0 := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      cases r with
      | zero =>
        rw [hb0]; simp [B0, PowerSeries.coeff_mk]
      | succ m =>
        rw [hbeq (m + 1) (by omega), hB0_eq (m + 1) (by omega)]
        congr 1
        · congr 1
          split_ifs with h2
          · exact ih (m + 1 - 2) (by omega)
          · rfl
        · split_ifs with h3
          · rw [coeff_sq_zmod2, coeff_sq_zmod2]
            split_ifs with hev
            · exact ih ((m + 1 - 3) / 2) (by omega)
            · rfl
          · rfl
  -- Step 6: Translate coeff r b = coeff r B0 back to coeff r A % 4
  have hA_mod4 : ∀ r : ℕ, 1 ≤ r →
      PowerSeries.coeff r A % 4 = if PowerSeries.coeff r B0 = 1 then 2 else 0 := by
    intro r hr
    have hcoeff : PowerSeries.coeff r A = 2 * PowerSeries.coeff r B := by
      have h := congrArg (PowerSeries.coeff r) hAB
      rw [map_add, PowerSeries.coeff_one, if_neg (by omega), zero_add,
          show (2 : PowerSeries ℤ) * B = PowerSeries.C 2 * B by simp, PowerSeries.coeff_C_mul] at h
      exact h
    have hb_r : ((PowerSeries.coeff r B : ℤ) : ZMod 2) = PowerSeries.coeff r B0 := by
      exact hb_eq_B0 r
    rw [hcoeff]
    have hcase : PowerSeries.coeff r B0 = 0 ∨ PowerSeries.coeff r B0 = 1 := by
      have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
      exact h2 _
    rcases hcase with h0 | h1
    · rw [h0, if_neg (by decide)]
      rw [h0] at hb_r
      have hdvd : (2 : ℤ) ∣ PowerSeries.coeff r B :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hb_r
      rcases hdvd with ⟨q, hq⟩; omega
    · rw [h1, if_pos rfl]
      rw [h1] at hb_r
      have hdvd : (2 : ℤ) ∣ (PowerSeries.coeff r B - 1) := by
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
        push_cast; rw [hb_r, sub_self]
      rcases hdvd with ⟨q, hq⟩; omega
  constructor
  · intro k hk
    rw [hA_mod4 (2 * k) (by omega)]
    have h0 : PowerSeries.coeff (2 * k) B0 = 0 := by
      simp [B0, PowerSeries.coeff_mk, show (2 * k) % 2 = 0 by omega]
    rw [h0, if_neg (by decide)]
  · intro n
    rw [hA_mod4 (2 * n + 1) (by omega)]
    have hB0_val : PowerSeries.coeff (2 * n + 1) B0 =
        (thueMorse n : ZMod 2) + (thueMorse (n + 2) : ZMod 2) := by
      simp [B0, PowerSeries.coeff_mk, show (2 * n + 1) % 2 = 1 by omega,
            show (2 * n + 1) / 2 = n by omega]
    rw [hB0_val]
    have hiff : (thueMorse n : ZMod 2) + (thueMorse (n + 2) : ZMod 2) = 1 ↔
        thueMorse n ≠ thueMorse (n + 2) := by
      rw [← thueMorse_zmod2]
      have h2 : ∀ x y : ZMod 2, x + y = 1 ↔ x ≠ y := by decide
      exact h2 _ _
    by_cases hne : thueMorse n ≠ thueMorse (n + 2)
    · rw [if_pos hne, if_pos (hiff.mpr hne)]
    · rw [if_neg hne, if_neg (fun h => hne (hiff.mp h))]

end OMA.P_oeis_a360949

theorem OMA.solution : type_of% @OMA.S_oeis_a360949.main := OMA.P_oeis_a360949.solution
