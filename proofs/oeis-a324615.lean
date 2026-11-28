import OMAStatements.S_oeis_a324615
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a324615

open OMA.S_oeis_a324615

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
    PowerSeries.coeff n (f ^ 2) = if Even n then PowerSeries.coeff (n / 2) f else 0 := by
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
  have hLR : ∑ i ∈ L, t i = ∑ i ∈ R, t i := by
    refine Finset.sum_bij (fun i _ => n - i) ?_ ?_ ?_ ?_
    · intro i hi; simp only [L, R, Finset.mem_filter, Finset.mem_range] at hi ⊢; omega
    · intro i1 h1 i2 h2 heq; simp only [L, Finset.mem_filter, Finset.mem_range] at h1 h2; omega
    · intro j hj; simp only [L, R, Finset.mem_filter, Finset.mem_range] at hj ⊢
      exact ⟨n - j, ⟨by omega, by omega⟩, by omega⟩
    · intro i hi; simp only [L, Finset.mem_filter, Finset.mem_range] at hi
      exact (hsym i (by omega)).symm
  change ∑ i ∈ Finset.range (n + 1), t i = _
  rw [hpart, Finset.sum_union hd1, Finset.sum_union hd2, hLR, ← add_assoc]
  have hadd2 : ∀ x : ZMod 2, x + x = 0 := by decide
  rw [hadd2, zero_add]
  by_cases hev : Even n
  · rw [if_pos hev]
    have hM : M = {n / 2} := by
      ext i; simp only [M, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      rcases hev with ⟨m, rfl⟩; omega
    rw [hM, Finset.sum_singleton]
    dsimp only [t]
    have hsub : n - n / 2 = n / 2 := by rcases hev with ⟨m, rfl⟩; omega
    rw [hsub]
    have hsq : ∀ x : ZMod 2, x * x = x := by decide
    exact hsq _
  · rw [if_neg hev]
    have hM : M = ∅ := by
      ext i; simp only [M, Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
      rintro ⟨_, heq⟩; exact hev ⟨i, by omega⟩
    rw [hM, Finset.sum_empty]

private lemma prod_one_add_kX_mod2 (m : ℕ) :
    (∏ k ∈ Finset.Icc 1 m, ((1 : PowerSeries (ZMod 2)) + (k : PowerSeries (ZMod 2)) * PowerSeries.X)) =
      ((1 : PowerSeries (ZMod 2)) + PowerSeries.X) ^ ((m + 1) / 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.prod_insert (by simp), ih]
    by_cases hodd : (m + 1) % 2 = 1
    · have hk : ((m + 1 : ℕ) : PowerSeries (ZMod 2)) = 1 := by
        rw [← map_natCast (PowerSeries.C (R := ZMod 2)), ← ZMod.natCast_mod, hodd]; simp
      rw [hk, one_mul, show (m + 1 + 1) / 2 = (m + 1) / 2 + 1 by omega, pow_succ']
    · have hev : (m + 1) % 2 = 0 := by omega
      have hk : ((m + 1 : ℕ) : PowerSeries (ZMod 2)) = 0 := by
        rw [← map_natCast (PowerSeries.C (R := ZMod 2)), ← ZMod.natCast_mod, hev]; simp
      rw [hk, zero_mul, add_zero, one_mul, show (m + 1 + 1) / 2 = (m + 1) / 2 by omega]

private def isTarget (n : ℕ) : Prop :=
  (∃ k : ℕ, n = 2 ^ k) ∨ (∃ k : ℕ, n = 3 * 2 ^ k)

private noncomputable def u0 : PowerSeries (ZMod 2) :=
  letI := Classical.decPred isTarget
  PowerSeries.mk fun n => if isTarget n then 1 else 0

private lemma coeff_u0 (n : ℕ) :
    letI := Classical.decPred isTarget
    PowerSeries.coeff n u0 = if isTarget n then 1 else 0 := by
  classical
  simp [u0]

private lemma u0_const : PowerSeries.constantCoeff u0 = 0 := by
  classical
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_u0, if_neg]
  rintro (⟨k, hk⟩ | ⟨k, hk⟩)
  · have := Nat.one_le_pow k 2 (by decide); omega
  · have := Nat.one_le_pow k 2 (by decide); omega

private lemma u0_quad :
    u0 + u0 ^ 2 = (PowerSeries.X : PowerSeries (ZMod 2)) + PowerSeries.X ^ 3 := by
  classical
  ext n
  rw [map_add, map_add, coeff_u0, coeff_sq_zmod2, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
  by_cases hn0 : n = 0
  · subst hn0
    have hne : ¬ isTarget 0 := by
      rintro (⟨k, hk⟩ | ⟨k, hk⟩) <;> have := Nat.one_le_pow k 2 (by decide) <;> omega
    simp only [hne, show Even 0 by decide, Nat.zero_div, coeff_u0, ↓reduceIte,
      show (0 : ℕ) ≠ 1 by omega, show (0 : ℕ) ≠ 3 by omega, add_zero]
  · by_cases hn1 : n = 1
    · subst hn1
      have h1 : isTarget 1 := Or.inl ⟨0, by norm_num⟩
      simp only [h1, show ¬ Even 1 by decide, ↓reduceIte, show (1 : ℕ) ≠ 3 by omega, add_zero]
    · by_cases hn3 : n = 3
      · subst hn3
        have h3 : isTarget 3 := Or.inr ⟨0, by norm_num⟩
        simp only [h3, show ¬ Even 3 by decide, ↓reduceIte, show (3 : ℕ) ≠ 1 by omega, add_zero, zero_add]
      · rw [if_neg hn1, if_neg hn3, add_zero]
        by_cases hev : Even n
        · rw [if_pos hev, coeff_u0]
          have hiff : isTarget n ↔ isTarget (n / 2) := by
            rcases hev with ⟨m, rfl⟩
            rw [show (m + m) / 2 = m by omega]
            constructor
            · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
              · cases k with
                | zero => simp at hk; omega
                | succ k' => exact Or.inl ⟨k', by rw [pow_succ'] at hk; omega⟩
              · cases k with
                | zero => simp at hk; omega
                | succ k' => exact Or.inr ⟨k', by rw [pow_succ'] at hk; omega⟩
            · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
              · exact Or.inl ⟨k + 1, by rw [pow_succ']; omega⟩
              · exact Or.inr ⟨k + 1, by rw [pow_succ']; omega⟩
          by_cases h : isTarget n
          · rw [if_pos h, if_pos (hiff.mp h)]; decide
          · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]; decide
        · rw [if_neg hev, add_zero]
          have hnot : ¬ isTarget n := by
            rintro (⟨k, hk⟩ | ⟨k, hk⟩)
            · cases k with
              | zero => simp at hk; omega
              | succ k' => exact hev ⟨2 ^ k', by rw [pow_succ'] at hk; omega⟩
            · cases k with
              | zero => simp at hk; omega
              | succ k' => exact hev ⟨3 * 2 ^ k', by rw [pow_succ'] at hk; omega⟩
          rw [if_neg hnot]

private lemma odd_iff_zmod2_eq_one (z : ℤ) : Odd z ↔ (z : ZMod 2) = 1 := by
  constructor
  · rintro ⟨k, rfl⟩
    push_cast
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, zero_mul, zero_add]
  · intro h
    rw [Int.odd_iff]
    by_contra hne
    have h0 : z % 2 = 0 := by omega
    have hdiv : (2 : ℤ) ∣ z := Int.dvd_of_emod_eq_zero h0
    rcases hdiv with ⟨k, rfl⟩
    push_cast at h
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, zero_mul] at h
    exact absurd h (by decide)

theorem solution : type_of% @OMA.S_oeis_a324615.main := by
  intro A hA0 hSum
  let φ : PowerSeries ℤ →+* PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2))
  let B : PowerSeries ℤ := Ring.inverse A
  have hA_unit : IsUnit A := PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hA0]; exact isUnit_one)
  have hAB : A * B = 1 := Ring.mul_inverse_cancel A hA_unit
  let a2 : PowerSeries (ZMod 2) := φ A
  let b2 : PowerSeries (ZMod 2) := φ B
  have ha2b2 : a2 * b2 = 1 := by
    dsimp only [a2, b2]; rw [← map_mul, hAB, map_one]
  have ha2_0 : PowerSeries.constantCoeff a2 = 1 := by
    dsimp only [a2, φ]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff, hA0, map_one]
  -- Reduce the sum identity mod 2:
  -- For every n, ∑_{m=0}^n coeff n (X^m * b2^(m+1) * (1+X)^((m+1)/2)) = coeff n 1
  let T : ℕ → PowerSeries (ZMod 2) := fun m =>
    PowerSeries.X ^ m * b2 ^ (m + 1) * (1 + PowerSeries.X) ^ ((m + 1) / 2)
  have hT_lt : ∀ m n : ℕ, n < m → PowerSeries.coeff n (T m) = 0 := by
    intro m n hlt
    dsimp only [T]
    rw [mul_assoc, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  have hsum_mod2 : ∀ n : ℕ, ∑ m ∈ Finset.range (n + 1), PowerSeries.coeff n (T m) =
      PowerSeries.coeff n (1 : PowerSeries (ZMod 2)) := by
    intro n
    have h := congrArg (Int.castRingHom (ZMod 2)) (hSum n)
    rw [map_sum] at h
    have hrhs : Int.castRingHom (ZMod 2) (if n = 0 then (1 : ℤ) else 0) =
        PowerSeries.coeff n (1 : PowerSeries (ZMod 2)) := by
      rw [PowerSeries.coeff_one]
      split_ifs <;> simp
    rw [hrhs] at h
    rw [← h]
    refine Finset.sum_congr rfl fun m _ => ?_
    dsimp only [T]
    have hmap : φ (PowerSeries.X ^ m * B ^ (m + 1) *
        ∏ k ∈ Finset.Icc 1 m, (1 + (k : PowerSeries ℤ) * PowerSeries.X)) =
        PowerSeries.X ^ m * b2 ^ (m + 1) * (1 + PowerSeries.X) ^ ((m + 1) / 2) := by
      rw [map_mul, map_mul, map_pow, PowerSeries.map_X, map_pow, map_prod]
      congr 1
      have hprod : (∏ k ∈ Finset.Icc 1 m, φ (1 + (k : PowerSeries ℤ) * PowerSeries.X)) =
          ∏ k ∈ Finset.Icc 1 m, ((1 : PowerSeries (ZMod 2)) + (k : PowerSeries (ZMod 2)) * PowerSeries.X) := by
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [map_add, map_one, map_mul, map_natCast, PowerSeries.map_X]
      rw [hprod, prod_one_add_kX_mod2]
    rw [← hmap, PowerSeries.coeff_map]
  -- Define Q = X^2 * (1 + X) * b2^2; notice T (m + 2) = Q * T m!
  let Q : PowerSeries (ZMod 2) := PowerSeries.X ^ 2 * (1 + PowerSeries.X) * b2 ^ 2
  have hT_step : ∀ m : ℕ, T (m + 2) = Q * T m := by
    intro m
    dsimp only [T, Q]
    rw [show (m + 2 + 1) / 2 = (m + 1) / 2 + 1 by omega]
    ring
  -- Now prove (1 + Q) = T 0 + T 1!
  have hmain_eq : (1 : PowerSeries (ZMod 2)) + Q = T 0 + T 1 := by
    ext n
    rw [map_add, map_add, ← hsum_mod2 n]
    -- Compute coeff n Q = coeff n (Q * 1) = ∑_{i=0}^n coeff i Q * coeff (n - i) 1
    have hQ_mul : PowerSeries.coeff n Q =
        ∑ m ∈ Finset.range (n + 1), PowerSeries.coeff n (Q * T m) := by
      have h1 : Q = Q * 1 := (mul_one Q).symm
      conv_lhs => rw [h1, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i Q * PowerSeries.coeff j (1 : PowerSeries (ZMod 2)))]
      have hsub : ∀ i ∈ Finset.range (n + 1),
          PowerSeries.coeff i Q * PowerSeries.coeff (n - i) (1 : PowerSeries (ZMod 2)) =
            ∑ m ∈ Finset.range (n + 1), PowerSeries.coeff i Q * PowerSeries.coeff (n - i) (T m) := by
        intro i hi
        rw [Finset.mem_range] at hi
        rw [← hsum_mod2 (n - i), Finset.mul_sum]
        refine Finset.sum_subset (Finset.range_mono (by omega)) fun m _ hm => ?_
        rw [Finset.mem_range] at hm
        rw [hT_lt m (n - i) (by omega), mul_zero]
      rw [Finset.sum_congr rfl hsub, Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i Q * PowerSeries.coeff j (T m))]
    rw [hQ_mul]
    have hshift : (∑ m ∈ Finset.range (n + 1), PowerSeries.coeff n (Q * T m)) =
        ∑ m ∈ Finset.range (n + 1), PowerSeries.coeff n (T (m + 2)) := by
      refine Finset.sum_congr rfl fun m _ => by rw [hT_step]
    rw [hshift]
    rcases n with _ | _ | n'
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      rw [hT_lt 2 0 (by omega), hT_lt 1 0 (by omega), add_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      rw [hT_lt 2 1 (by omega), hT_lt 3 1 (by omega), add_zero, add_zero]
    · set N := n' + 2
      have hsplit1 : (∑ m ∈ Finset.range (N + 1), PowerSeries.coeff N (T m)) =
          PowerSeries.coeff N (T 0) + PowerSeries.coeff N (T 1) +
            ∑ m ∈ Finset.range (N - 1), PowerSeries.coeff N (T (m + 2)) := by
        rw [show N + 1 = (N - 1) + 2 by omega, Finset.sum_range_succ', Finset.sum_range_succ']
        ring
      have hsplit2 : (∑ m ∈ Finset.range (N + 1), PowerSeries.coeff N (T (m + 2))) =
          ∑ m ∈ Finset.range (N - 1), PowerSeries.coeff N (T (m + 2)) := by
        rw [show N + 1 = (N - 1) + 2 by omega, Finset.sum_range_succ, Finset.sum_range_succ]
        rw [hT_lt (N - 1 + 2) N (by omega), hT_lt (N - 1 + 1 + 2) N (by omega), add_zero, add_zero]
      rw [hsplit1, hsplit2, add_assoc]
      have hcancel : ∀ x : ZMod 2, x + x = 0 := by decide
      rw [hcancel, add_zero]
  -- Multiply (1 + Q = T 0 + T 1) by a2^2!
  have ha2_quad : a2 ^ 2 + a2 = PowerSeries.X + PowerSeries.X ^ 3 := by
    have hmul := congrArg (a2 ^ 2 * ·) hmain_eq
    dsimp only [Q, T] at hmul
    simp only [pow_zero, one_mul, pow_one, Nat.zero_add, Nat.div_self (by decide : 0 < 2)] at hmul
    have hlhs : a2 ^ 2 * (1 + PowerSeries.X ^ 2 * (1 + PowerSeries.X) * b2 ^ 2) =
        a2 ^ 2 + PowerSeries.X ^ 2 * (1 + PowerSeries.X) := by
      calc a2 ^ 2 * (1 + PowerSeries.X ^ 2 * (1 + PowerSeries.X) * b2 ^ 2)
          = a2 ^ 2 + PowerSeries.X ^ 2 * (1 + PowerSeries.X) * (a2 * b2) ^ 2 := by ring
        _ = a2 ^ 2 + PowerSeries.X ^ 2 * (1 + PowerSeries.X) := by rw [ha2b2, one_pow, mul_one]
    have hrhs : a2 ^ 2 * (b2 * (1 + PowerSeries.X) ^ 0 +
        PowerSeries.X * b2 ^ 2 * (1 + PowerSeries.X)) =
        a2 + PowerSeries.X * (1 + PowerSeries.X) := by
      rw [pow_zero, mul_one]
      calc a2 ^ 2 * (b2 + PowerSeries.X * b2 ^ 2 * (1 + PowerSeries.X))
          = a2 * (a2 * b2) + PowerSeries.X * (1 + PowerSeries.X) * (a2 * b2) ^ 2 := by ring
        _ = a2 + PowerSeries.X * (1 + PowerSeries.X) := by rw [ha2b2, one_pow, mul_one, mul_one]
    rw [hlhs, hrhs] at hmul
    have hadd := congrArg (· + (a2 + PowerSeries.X ^ 2 * (1 + PowerSeries.X))) hmul
    have h2 := zmod2_ps_two
    calc a2 ^ 2 + a2
        = (a2 ^ 2 + PowerSeries.X ^ 2 * (1 + PowerSeries.X)) +
            (a2 + PowerSeries.X ^ 2 * (1 + PowerSeries.X)) -
            2 * (PowerSeries.X ^ 2 * (1 + PowerSeries.X)) := by ring
      _ = (a2 + PowerSeries.X * (1 + PowerSeries.X)) +
            (a2 + PowerSeries.X ^ 2 * (1 + PowerSeries.X)) - 0 := by rw [hadd, h2, zero_mul]
      _ = PowerSeries.X + PowerSeries.X ^ 3 + 2 * (a2 + PowerSeries.X ^ 2) := by ring
      _ = PowerSeries.X + PowerSeries.X ^ 3 := by rw [h2, zero_mul, add_zero]
  -- Let u := a2 + 1; then u + u^2 = X + X^3 and constantCoeff u = 0, so u = u0!
  let u : PowerSeries (ZMod 2) := a2 + 1
  have hu0 : PowerSeries.constantCoeff u = 0 := by
    dsimp only [u]; rw [map_add, ha2_0, map_one]; decide
  have hu_quad : u + u ^ 2 = PowerSeries.X + PowerSeries.X ^ 3 := by
    dsimp only [u]
    rw [zmod2_ps_add_sq, one_pow]
    calc a2 + 1 + (a2 ^ 2 + 1) = (a2 ^ 2 + a2) + (1 + 1) := by ring
      _ = (PowerSeries.X + PowerSeries.X ^ 3) + 0 := by rw [ha2_quad, zmod2_ps_add_self]
      _ = PowerSeries.X + PowerSeries.X ^ 3 := add_zero _
  have hdiff : u + u0 = (u + u0) ^ 2 := by
    have hadd : (u + u ^ 2) + (u0 + u0 ^ 2) =
        (PowerSeries.X + PowerSeries.X ^ 3) + (PowerSeries.X + PowerSeries.X ^ 3) := by
      rw [hu_quad, u0_quad]
    rw [zmod2_ps_add_self] at hadd
    have hlhs : (u + u ^ 2) + (u0 + u0 ^ 2) = (u + u0) + (u + u0) ^ 2 := by
      rw [zmod2_ps_add_sq u u0]; ring
    rw [hlhs] at hadd
    have := congrArg (· + (u + u0) ^ 2) hadd
    rw [add_assoc, zmod2_ps_add_self, add_zero, zero_add] at this
    exact this
  have hu_eq : u = u0 := by
    have hzero : ∀ n, PowerSeries.coeff n (u + u0) = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        cases n with
        | zero => rw [PowerSeries.coeff_zero_eq_constantCoeff, map_add, hu0, u0_const, add_zero]
        | succ m =>
          have hc := congrArg (PowerSeries.coeff (m + 1)) hdiff
          rw [coeff_sq_zmod2] at hc
          rw [hc]
          split_ifs with hev
          · exact ih ((m + 1) / 2) (by omega)
          · rfl
    ext n
    have h0 := hzero n
    rw [map_add] at h0
    have heq : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
    exact heq _ _ h0
  have ha2_eq : a2 = 1 + u0 := by
    rw [← hu_eq]; dsimp only [u]; rw [add_comm a2 1, ← add_assoc, zmod2_ps_add_self, zero_add]
  intro n
  rw [odd_iff_zmod2_eq_one]
  have hc : ((PowerSeries.coeff n A : ℤ) : ZMod 2) = PowerSeries.coeff n (1 + u0) := by
    rw [← ha2_eq]; dsimp only [a2, φ]; rw [PowerSeries.coeff_map]; rfl
  rw [hc, map_add, PowerSeries.coeff_one]
  classical
  rw [coeff_u0]
  by_cases hn0 : n = 0
  · subst hn0
    have hne : ¬ isTarget 0 := by
      rintro (⟨k, hk⟩ | ⟨k, hk⟩) <;> have := Nat.one_le_pow k 2 (by decide) <;> omega
    simp [hne]
  · rw [if_neg hn0, zero_add]
    unfold isTarget
    by_cases h : (∃ k : ℕ, n = 2 ^ k) ∨ (∃ k : ℕ, n = 3 * 2 ^ k)
    · rw [if_pos h]; exact iff_of_true rfl (Or.inr h)
    · rw [if_neg h]; exact iff_of_false (by decide) (by rintro (rfl | h'); exact hn0 rfl; exact h h')

end OMA.P_oeis_a324615

theorem OMA.solution : type_of% @OMA.S_oeis_a324615.main := OMA.P_oeis_a324615.solution
