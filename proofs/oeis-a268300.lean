import OMAStatements.S_oeis_a268300
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a268300

open OMA.S_oeis_a268300

private lemma zmod4_ps_four : (4 : PowerSeries (ZMod 4)) = 0 := by
  have h : (4 : ZMod 4) = 0 := by decide
  rw [← map_ofNat (PowerSeries.C (R := ZMod 4)), h, map_zero]

private lemma zmod2_ps_two : (2 : PowerSeries (ZMod 2)) = 0 := by
  have h : (2 : ZMod 2) = 0 := by decide
  rw [← map_ofNat (PowerSeries.C (R := ZMod 2)), h, map_zero]

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

theorem solution : type_of% @OMA.S_oeis_a268300.main := by
  intro B hB0 hEq
  have hBu : IsUnit B := PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hB0]; exact isUnit_one)
  have hBinv : B * Ring.inverse B = 1 := Ring.mul_inverse_cancel B hBu
  -- Reduce the product mod 4: all factors with n ≥ 2 are 1 mod 4!
  let φ4 : PowerSeries ℤ →+* PowerSeries (ZMod 4) := PowerSeries.map (Int.castRingHom (ZMod 4))
  have hXφ4 : φ4 PowerSeries.X = PowerSeries.X := PowerSeries.map_X _
  have hmod4 : ∀ r : ℕ,
      (if r = 0 then (-1 : ZMod 4) else 0) =
      PowerSeries.coeff r (1 - 2 * φ4 B - 2 * PowerSeries.X * φ4 (Ring.inverse B)) := by
    intro r
    have h := congrArg (Int.castRingHom (ZMod 4)) (hEq r)
    have hIcc : Finset.Icc 1 (r + 1) = insert 1 (Finset.Icc 2 (r + 1)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.prod_insert (by simp)] at h
    rw [← PowerSeries.coeff_map, map_mul, map_prod] at h
    have htail : ∏ n ∈ Finset.Icc 2 (r + 1),
        φ4 ((1 - (4 : PowerSeries ℤ) ^ n * PowerSeries.X ^ n) *
          (1 - (2 : PowerSeries ℤ) ^ (2 * n - 1) * PowerSeries.X ^ n * Ring.inverse B) *
          (1 - (2 : PowerSeries ℤ) ^ (2 * n - 1) * PowerSeries.X ^ (n - 1) * B)) = 1 := by
      refine Finset.prod_eq_one fun n hn => ?_
      have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
      have h4n : (4 : PowerSeries (ZMod 4)) ^ n = 0 := by
        rw [zmod4_ps_four, zero_pow (by omega)]
      have h2n : (2 : PowerSeries (ZMod 4)) ^ (2 * n - 1) = 0 := by
        have hsub : 2 * n - 1 = 2 + (2 * n - 3) := by omega
        rw [hsub, pow_add, show (2 : PowerSeries (ZMod 4)) ^ 2 = 4 by norm_num, zmod4_ps_four, zero_mul]
      simp only [map_mul, map_sub, map_one, map_pow, map_ofNat, h4n, h2n, zero_mul, sub_zero, mul_one]
    rw [htail, mul_one] at h
    have hn1 : φ4 ((1 - (4 : PowerSeries ℤ) ^ 1 * PowerSeries.X ^ 1) *
        (1 - (2 : PowerSeries ℤ) ^ (2 * 1 - 1) * PowerSeries.X ^ 1 * Ring.inverse B) *
        (1 - (2 : PowerSeries ℤ) ^ (2 * 1 - 1) * PowerSeries.X ^ (1 - 1) * B)) =
        1 - 2 * φ4 B - 2 * PowerSeries.X * φ4 (Ring.inverse B) := by
      simp only [show 2 * 1 - 1 = 1 by rfl, pow_one, Nat.sub_self, pow_zero, mul_one,
                 map_mul, map_sub, map_one, map_ofNat, hXφ4, zmod4_ps_four, zero_mul, sub_zero, one_mul]
      have h4 : (1 - 2 * PowerSeries.X * φ4 (Ring.inverse B)) * (1 - 2 * φ4 B) =
          1 - 2 * φ4 B - 2 * PowerSeries.X * φ4 (Ring.inverse B) +
          4 * (PowerSeries.X * φ4 (Ring.inverse B) * φ4 B) := by ring
      rw [h4, zmod4_ps_four, zero_mul, add_zero]
    rw [hn1] at h
    rw [← h]
    split_ifs <;> simp
  -- Therefore 2 - 2*B - 2*X*B⁻¹ = 0 in ZMod 4[[X]], so multiplying by B gives 2*(B - B^2 - X) = 0 mod 4,
  -- hence B + B^2 = X in ZMod 2[[X]]!
  have hps4 : (2 : PowerSeries (ZMod 4)) * (1 - φ4 B - PowerSeries.X * φ4 (Ring.inverse B)) = 0 := by
    ext r
    have h := hmod4 r
    have hlin : (2 : PowerSeries (ZMod 4)) * (1 - φ4 B - PowerSeries.X * φ4 (Ring.inverse B)) =
        1 + (1 - 2 * φ4 B - 2 * PowerSeries.X * φ4 (Ring.inverse B)) := by ring
    rw [hlin, map_add, PowerSeries.coeff_one, ← h, map_zero]
    split_ifs <;> decide
  have hmul4 : (2 : PowerSeries (ZMod 4)) * (φ4 B - φ4 B ^ 2 - PowerSeries.X) = 0 := by
    have h1 := congrArg (· * φ4 B) hps4
    rw [zero_mul] at h1
    have hinv4 : φ4 (Ring.inverse B) * φ4 B = 1 := by
      rw [← map_mul, mul_comm, hBinv, map_one]
    have h2 : (2 : PowerSeries (ZMod 4)) * (1 - φ4 B - PowerSeries.X * φ4 (Ring.inverse B)) * φ4 B =
        2 * (φ4 B - φ4 B ^ 2 - PowerSeries.X * (φ4 (Ring.inverse B) * φ4 B)) := by ring
    rw [h2, hinv4, mul_one] at h1
    exact h1
  -- Extract mod 2 equation: b + b^2 = X in ZMod 2[[X]]
  let φ2 : PowerSeries ℤ →+* PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2))
  let b : PowerSeries (ZMod 2) := φ2 B
  have hb_eq : ∀ r : ℕ, PowerSeries.coeff r b + PowerSeries.coeff r (b ^ 2) =
      if r = 1 then (1 : ZMod 2) else 0 := by
    intro r
    have h4 := congrArg (PowerSeries.coeff r) hmul4
    have hcast : (2 : PowerSeries (ZMod 4)) * (φ4 B - φ4 B ^ 2 - PowerSeries.X) =
        φ4 (2 * (B - B ^ 2 - PowerSeries.X)) := by
      simp only [map_mul, map_sub, map_pow, map_ofNat, hXφ4]
    rw [hcast, PowerSeries.coeff_map, map_zero] at h4
    have hdiv4 : (4 : ℤ) ∣ PowerSeries.coeff r (2 * (B - B ^ 2 - PowerSeries.X)) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp h4
    rw [show (2 : PowerSeries ℤ) * (B - B ^ 2 - PowerSeries.X) =
        PowerSeries.C 2 * (B - B ^ 2 - PowerSeries.X) by simp, PowerSeries.coeff_C_mul] at hdiv4
    have hdiv2 : (2 : ℤ) ∣ PowerSeries.coeff r (B - B ^ 2 - PowerSeries.X) := by
      rcases hdiv4 with ⟨q, hq⟩; exact ⟨q, by omega⟩
    have h0 : (Int.castRingHom (ZMod 2)) (PowerSeries.coeff r (B - B ^ 2 - PowerSeries.X)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr hdiv2
    simp only [← PowerSeries.coeff_map, map_sub, map_pow, PowerSeries.coeff_X] at h0
    have h2 : ∀ x y z : ZMod 2, x - y - z = 0 → x + y = z := by decide
    by_cases hr : r = 1
    · rw [if_pos hr] at h0 ⊢
      rw [map_one] at h0
      exact h2 _ _ _ h0
    · rw [if_neg hr] at h0 ⊢
      rw [map_zero] at h0
      exact h2 _ _ _ h0
  -- Strong induction: coeff n b = 1 iff n = 0 or ∃ k, n = 2^k
  have hb_char : ∀ n : ℕ, PowerSeries.coeff n b = 1 ↔ n = 0 ∨ ∃ k : ℕ, n = 2 ^ k := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero =>
        have h0 : PowerSeries.coeff 0 b = 1 := by
          change (Int.castRingHom (ZMod 2)) (PowerSeries.coeff 0 B) = 1
          rw [PowerSeries.coeff_zero_eq_constantCoeff, hB0, map_one]
        simp [h0]
      | succ m =>
        have h := hb_eq (m + 1)
        rw [coeff_sq_zmod2] at h
        cases m with
        | zero =>
          simp only [Nat.zero_add, ↓reduceIte, show ¬ (1 : ℕ) % 2 = 0 by omega, add_zero] at h
          constructor
          · intro _; exact Or.inr ⟨0, by norm_num⟩
          · intro _; exact h
        | succ m' =>
          rw [if_neg (by omega : m' + 2 ≠ 1)] at h
          have heq : PowerSeries.coeff (m' + 2) b =
              if (m' + 2) % 2 = 0 then PowerSeries.coeff ((m' + 2) / 2) b else 0 := by
            have h2 : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
            exact h2 _ _ h
          rw [heq]
          by_cases hev : (m' + 2) % 2 = 0
          · rw [if_pos hev, ih ((m' + 2) / 2) (by omega)]
            constructor
            · rintro (h0 | ⟨k, hk⟩)
              · omega
              · exact Or.inr ⟨k + 1, by rw [pow_succ']; omega⟩
            · rintro (h0 | ⟨k, hk⟩)
              · omega
              · cases k with
                | zero => simp at hk
                | succ k' => exact Or.inr ⟨k', by rw [pow_succ'] at hk; omega⟩
          · rw [if_neg hev]
            constructor
            · intro h01; exact absurd h01 (by decide)
            · rintro (h0 | ⟨k, hk⟩)
              · omega
              · cases k with
                | zero => simp at hk
                | succ k' => rw [pow_succ'] at hk; omega
  intro n
  rw [← hb_char n]
  constructor
  · rintro ⟨m, hm⟩
    change (Int.castRingHom (ZMod 2)) (PowerSeries.coeff n B) = 1
    rw [hm, map_add, map_mul, map_ofNat, map_one, show (2 : ZMod 2) = 0 by decide, zero_mul, zero_add]
  · intro h
    rcases Int.even_or_odd (PowerSeries.coeff n B) with ⟨m, hm⟩ | hodd
    · exfalso
      change (Int.castRingHom (ZMod 2)) (PowerSeries.coeff n B) = 1 at h
      rw [hm, map_add, ← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul] at h
      exact absurd h (by decide)
    · exact hodd

end OMA.P_oeis_a268300

theorem OMA.solution : type_of% @OMA.S_oeis_a268300.main := OMA.P_oeis_a268300.solution
