import OMAStatements.S_oeis_a382122
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a382122

open OMA.S_oeis_a382122

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

private noncomputable def u0 : PowerSeries (ZMod 2) :=
  letI := Classical.decPred (fun n : ℕ => ∃ k : ℕ, n = 2 ^ k)
  PowerSeries.mk fun n => if ∃ k : ℕ, n = 2 ^ k then 1 else 0

private lemma coeff_u0 (n : ℕ) :
    letI := Classical.decPred (fun n : ℕ => ∃ k : ℕ, n = 2 ^ k)
    PowerSeries.coeff n u0 = if ∃ k : ℕ, n = 2 ^ k then 1 else 0 := by
  classical
  simp [u0]

private lemma u0_const : PowerSeries.constantCoeff u0 = 0 := by
  classical
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_u0]
  rw [if_neg]
  rintro ⟨k, hk⟩
  have := Nat.one_le_pow k 2 (by decide)
  omega

private lemma u0_quad : u0 + u0 ^ 2 = (PowerSeries.X : PowerSeries (ZMod 2)) := by
  classical
  ext n
  rw [map_add, coeff_u0, coeff_sq_zmod2, PowerSeries.coeff_X]
  by_cases hn0 : n = 0
  · subst hn0
    have hne : ¬ ∃ k : ℕ, (0 : ℕ) = 2 ^ k := by
      rintro ⟨k, hk⟩; have := Nat.one_le_pow k 2 (by decide); omega
    simp only [hne, show Even 0 by decide, Nat.zero_div, coeff_u0, ↓reduceIte,
      show (0 : ℕ) ≠ 1 by omega]
    decide
  · by_cases hn1 : n = 1
    · subst hn1
      have h1 : ∃ k : ℕ, (1 : ℕ) = 2 ^ k := ⟨0, by norm_num⟩
      simp only [h1, show ¬ Even 1 by decide, ↓reduceIte]
      decide
    · rw [if_neg hn1]
      by_cases hev : Even n
      · rw [if_pos hev, coeff_u0]
        have hiff : (∃ k : ℕ, n = 2 ^ k) ↔ (∃ k : ℕ, n / 2 = 2 ^ k) := by
          constructor
          · rintro ⟨k, hk⟩
            cases k with
            | zero => simp at hk; omega
            | succ k' => exact ⟨k', by rw [hk, pow_succ']; omega⟩
          · rintro ⟨k, hk⟩
            rcases hev with ⟨m, rfl⟩
            exact ⟨k + 1, by rw [pow_succ']; omega⟩
        by_cases h : ∃ k : ℕ, n = 2 ^ k
        · rw [if_pos h, if_pos (hiff.mp h)]; decide
        · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]; decide
      · rw [if_neg hev, add_zero]
        have hnot : ¬ ∃ k : ℕ, n = 2 ^ k := by
          rintro ⟨k, hk⟩
          cases k with
          | zero => simp at hk; omega
          | succ k' => exact hev ⟨2 ^ k', by rw [hk, pow_succ']; omega⟩
        rw [if_neg hnot]

private lemma zmod2_cast_abs (z : ℤ) : ((|z| : ℤ) : ZMod 2) = (z : ZMod 2) := by
  rcases abs_choice z with h | h
  · rw [h]
  · rw [h, Int.cast_neg]
    generalize (z : ZMod 2) = x
    revert x; decide

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

theorem solution : type_of% @OMA.S_oeis_a382122.main := by
  intro A C hA0 hC hSum
  let φ : PowerSeries ℤ →+* PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2))
  let B : PowerSeries ℤ := Ring.inverse A
  have hA_unit : IsUnit A := PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hA0]; exact isUnit_one)
  have hAB : A * B = 1 := Ring.mul_inverse_cancel A hA_unit
  let a2 : PowerSeries (ZMod 2) := φ A
  let b2 : PowerSeries (ZMod 2) := φ B
  let c2 : PowerSeries (ZMod 2) := φ C
  have ha2b2 : a2 * b2 = 1 := by
    dsimp only [a2, b2]; rw [← map_mul, hAB, map_one]
  have hc2_eq : c2 = 1 + PowerSeries.X * c2 ^ 2 := by
    have h := congrArg φ hC
    dsimp only [c2, φ] at h ⊢
    simpa only [map_add, map_one, map_mul, map_pow, PowerSeries.map_X] using h
  -- Define G = ∑_{m≥0} (X * b2)^m, i.e., coeff n G = ∑_{k=0}^n coeff k (b2^(n-k))
  have hc2_sum : ∀ n : ℕ, PowerSeries.coeff n c2 =
      ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k (b2 ^ (n - k)) := by
    intro n
    have h := congrArg (Int.castRingHom (ZMod 2)) (hSum n)
    rw [map_sum] at h
    have h1 : PowerSeries.coeff n c2 = Int.castRingHom (ZMod 2) (PowerSeries.coeff n C) := by
      dsimp only [c2, φ]; rw [PowerSeries.coeff_map]
    rw [h1, ← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    change ((|PowerSeries.coeff k (B ^ (n - k))| : ℤ) : ZMod 2) = _
    rw [zmod2_cast_abs]
    change Int.castRingHom (ZMod 2) (PowerSeries.coeff k (B ^ (n - k))) = _
    dsimp only [b2, φ]; rw [← PowerSeries.coeff_map, map_pow]
  -- Show (1 + X * b2) * c2 = 1!
  have hgeom : (1 + PowerSeries.X * b2) * c2 = 1 := by
    ext n
    rw [add_mul, one_mul, map_add, PowerSeries.coeff_one, hc2_sum]
    cases n with
    | zero =>
      rw [if_pos rfl, Finset.sum_range_one, Nat.sub_zero, pow_zero, PowerSeries.coeff_one,
          if_pos rfl, mul_assoc, ← pow_one (PowerSeries.X : PowerSeries (ZMod 2)),
          PowerSeries.coeff_X_pow_mul', if_neg (by omega), add_zero]
    | succ m =>
      rw [if_neg (by omega : m + 1 ≠ 0), mul_assoc,
          ← pow_one (PowerSeries.X : PowerSeries (ZMod 2)), PowerSeries.coeff_X_pow_mul',
          if_pos (by omega), Nat.add_sub_cancel]
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i b2 * PowerSeries.coeff j c2)]
      have hterm2 : ∑ i ∈ Finset.range (m + 1), PowerSeries.coeff i b2 * PowerSeries.coeff (m - i) c2 =
          ∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k (b2 ^ (m + 1 - k)) := by
        have hsub : ∀ i ∈ Finset.range (m + 1),
            PowerSeries.coeff i b2 * PowerSeries.coeff (m - i) c2 =
              ∑ j ∈ Finset.range (m - i + 1),
                PowerSeries.coeff i b2 * PowerSeries.coeff j (b2 ^ (m - i - j)) := by
          intro i _
          rw [hc2_sum (m - i), Finset.mul_sum]
        rw [Finset.sum_congr rfl hsub]
        -- Reindex by k = i + j (0 ≤ k ≤ m)
        have hbi : ∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k (b2 ^ (m + 1 - k)) =
            ∑ k ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (k + 1),
              PowerSeries.coeff i b2 * PowerSeries.coeff (k - i) (b2 ^ (m - k)) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.mem_range] at hk
          have hexp : m + 1 - k = (m - k) + 1 := by omega
          rw [hexp, pow_succ', PowerSeries.coeff_mul,
              Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (fun i j => PowerSeries.coeff i b2 * PowerSeries.coeff j (b2 ^ (m - k)))]
        rw [hbi]
        -- Both sides sum over {(i, j) | i + j ≤ m} of coeff i b2 * coeff j (b2 ^ (m - i - j))
        have hS1 : (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m - i + 1),
              PowerSeries.coeff i b2 * PowerSeries.coeff j (b2 ^ (m - i - j))) =
            ∑ p ∈ (Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter (fun p => p.1 + p.2 ≤ m),
              PowerSeries.coeff p.1 b2 * PowerSeries.coeff p.2 (b2 ^ (m - p.1 - p.2)) := by
          rw [Finset.sum_filter, Finset.sum_product]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.mem_range] at hi
          rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ fun j _ => rfl
          ext j; simp only [Finset.mem_range, Finset.mem_filter]; omega
        have hS2 : (∑ k ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (k + 1),
              PowerSeries.coeff i b2 * PowerSeries.coeff (k - i) (b2 ^ (m - k))) =
            ∑ p ∈ (Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter (fun p => p.1 + p.2 ≤ m),
              PowerSeries.coeff p.1 b2 * PowerSeries.coeff p.2 (b2 ^ (m - p.1 - p.2)) := by
          rw [Finset.sum_sigma']
          refine Finset.sum_bij (fun x _ => (x.2, x.1 - x.2)) ?_ ?_ ?_ ?_
          · intro ⟨k, i⟩ hx
            simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Finset.mem_product] at hx ⊢
            omega
          · intro ⟨k1, i1⟩ h1 ⟨k2, i2⟩ h2 heq
            simp only [Finset.mem_sigma, Finset.mem_range] at h1 h2
            simp only [Prod.mk.injEq] at heq
            rcases heq with ⟨hi, hsub⟩
            have hk : k1 = k2 := by omega
            subst hk; subst hi; rfl
          · intro ⟨i, j⟩ hp
            simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
            refine ⟨⟨i + j, i⟩, ?_, ?_⟩
            · simp only [Finset.mem_sigma, Finset.mem_range]; omega
            · simp
          · intro ⟨k, i⟩ hx
            simp only [Finset.mem_sigma, Finset.mem_range] at hx
            dsimp
            rw [show m - i - (k - i) = m - k by omega]
        rw [hS1, hS2]
      rw [hterm2, Finset.sum_range_succ, Nat.sub_self, pow_zero, PowerSeries.coeff_one,
          if_neg (by omega : m + 1 ≠ 0), add_zero]
      generalize ∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k (b2 ^ (m + 1 - k)) = x
      revert x; decide
  -- Now (1 + X * c2) * c2 = c2 + X * c2^2 = 1!
  have hc2_inv : (1 + PowerSeries.X * c2) * c2 = 1 := by
    calc (1 + PowerSeries.X * c2) * c2 = c2 + PowerSeries.X * c2 ^ 2 := by ring
      _ = (1 + PowerSeries.X * c2 ^ 2) + PowerSeries.X * c2 ^ 2 := by conv_lhs => lhs; rw [hc2_eq]
      _ = 1 + (PowerSeries.X * c2 ^ 2 + PowerSeries.X * c2 ^ 2) := by ring
      _ = 1 + 0 := by rw [zmod2_ps_add_self]
      _ = 1 := add_zero _
  -- Hence 1 + X * b2 = 1 + X * c2, so b2 = c2, and a2 = 1 + X * c2!
  have ha2_eq_1Xc2 : a2 = 1 + PowerSeries.X * c2 := by
    have h1 : 1 + PowerSeries.X * b2 = 1 + PowerSeries.X * c2 := by
      calc 1 + PowerSeries.X * b2
          = (1 + PowerSeries.X * b2) * 1 := (mul_one _).symm
        _ = (1 + PowerSeries.X * b2) * (c2 * (1 + PowerSeries.X * c2)) := by
            rw [mul_comm c2, hc2_inv]
        _ = ((1 + PowerSeries.X * b2) * c2) * (1 + PowerSeries.X * c2) := by ring
        _ = 1 * (1 + PowerSeries.X * c2) := by rw [hgeom]
        _ = 1 + PowerSeries.X * c2 := one_mul _
    have hXb : PowerSeries.X * b2 = PowerSeries.X * c2 := by
      have := congrArg (· + 1) h1
      simpa only [add_comm _ (1 : PowerSeries (ZMod 2)), ← add_assoc, zmod2_ps_add_self, zero_add] using this
    have hb2_eq_c2 : b2 = c2 := by
      ext n
      have := congrArg (PowerSeries.coeff (n + 1)) hXb
      rw [← pow_one (PowerSeries.X : PowerSeries (ZMod 2)), PowerSeries.coeff_X_pow_mul',
          PowerSeries.coeff_X_pow_mul', if_pos (by omega), if_pos (by omega),
          Nat.add_sub_cancel] at this
      exact this
    calc a2 = a2 * 1 := (mul_one _).symm
      _ = a2 * (c2 * (1 + PowerSeries.X * c2)) := by rw [mul_comm c2, hc2_inv]
      _ = (a2 * b2) * (1 + PowerSeries.X * c2) := by rw [hb2_eq_c2]; ring
      _ = 1 * (1 + PowerSeries.X * c2) := by rw [ha2b2]
      _ = 1 + PowerSeries.X * c2 := one_mul _
  -- And u := X * c2 satisfies u + u^2 = X with constantCoeff u = 0, so u = u0!
  let u : PowerSeries (ZMod 2) := PowerSeries.X * c2
  have hu0 : PowerSeries.constantCoeff u = 0 := by
    dsimp only [u]; rw [map_mul, PowerSeries.constantCoeff_X, zero_mul]
  have hu_quad : u + u ^ 2 = PowerSeries.X := by
    have h := congrArg (PowerSeries.X * ·) hc2_eq
    rw [mul_add, mul_one] at h
    have h1 : u = PowerSeries.X + u ^ 2 := by
      dsimp only [u]; calc PowerSeries.X * c2 = PowerSeries.X + PowerSeries.X * (PowerSeries.X * c2 ^ 2) := h
        _ = PowerSeries.X + (PowerSeries.X * c2) ^ 2 := by ring
    calc u + u ^ 2 = (PowerSeries.X + u ^ 2) + u ^ 2 := by conv_lhs => lhs; rw [h1]
      _ = PowerSeries.X + (u ^ 2 + u ^ 2) := by ring
      _ = PowerSeries.X + 0 := by rw [zmod2_ps_add_self]
      _ = PowerSeries.X := add_zero _
  have hdiff : u + u0 = (u + u0) ^ 2 := by
    have hadd : (u + u ^ 2) + (u0 + u0 ^ 2) = PowerSeries.X + PowerSeries.X := by rw [hu_quad, u0_quad]
    rw [zmod2_ps_add_self] at hadd
    have hlhs : (u + u ^ 2) + (u0 + u0 ^ 2) = (u + u0) + (u + u0) ^ 2 := by
      rw [zmod2_ps_add_sq]; ring
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
  intro n hn
  rw [odd_iff_zmod2_eq_one]
  have hc : ((PowerSeries.coeff n A : ℤ) : ZMod 2) = PowerSeries.coeff n u0 := by
    have h1 : PowerSeries.coeff n a2 = PowerSeries.coeff n (1 + u) := by rw [ha2_eq_1Xc2]
    rw [map_add, PowerSeries.coeff_one, if_neg (by omega), zero_add, hu_eq] at h1
    rw [← h1]; dsimp only [a2, φ]; rw [PowerSeries.coeff_map]; rfl
  rw [hc]
  classical
  rw [coeff_u0]
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (by decide) h

end OMA.P_oeis_a382122

theorem OMA.solution : type_of% @OMA.S_oeis_a382122.main := OMA.P_oeis_a382122.solution
