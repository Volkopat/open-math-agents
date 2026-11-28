import OMAStatements.S_oeis_a338633
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a338633

open OMA.S_oeis_a338633

private lemma zmod2_ps_two : (2 : PowerSeries (ZMod 2)) = 0 := by
  have h : (2 : ZMod 2) = 0 := by decide
  rw [← map_ofNat (PowerSeries.C (R := ZMod 2)), h, map_zero]

private lemma zmod2_ps_add_self (f : PowerSeries (ZMod 2)) : f + f = 0 := by
  rw [← two_mul, zmod2_ps_two, zero_mul]

private lemma zmod2_ps_sub (f g : PowerSeries (ZMod 2)) : f - g = f + g := by
  rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_right (zmod2_ps_add_self g)]

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

private lemma odd_iff_zmod2_eq_one (z : ℤ) : Odd z ↔ (z : ZMod 2) = 1 := by
  constructor
  · rintro ⟨k, rfl⟩; push_cast; have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, zero_mul, zero_add]
  · intro h
    rcases Int.even_or_odd z with ⟨k, rfl⟩ | hodd
    · push_cast at h
      have h2 : (k : ZMod 2) + (k : ZMod 2) = 0 := by
        generalize (k : ZMod 2) = x; revert x; decide
      rw [h2] at h; exact absurd h (by decide)
    · exact hodd

private theorem prove_main : type_of% @OMA.S_oeis_a338633.main := by
  classical
  intro A hA0 hCF
  obtain ⟨R, hR0, hRk⟩ := hCF
  let φ := PowerSeries.map (Int.castRingHom (ZMod 2))
  set a2 : PowerSeries (ZMod 2) := φ A
  have ha2_0 : PowerSeries.constantCoeff a2 = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, hA0, map_one]
  -- Reduce R 0 * (A - 8 * X * R 1) = 1 mod 2 => φ (R 0) * a2 = 1
  have hR0_mul : φ (R 0) * a2 = 1 := by
    have h0 := congrArg φ (hRk 0)
    have h8 : φ (((0 + 2) ^ 3 : ℕ) : PowerSeries ℤ) = 0 := by
      have h8c : (((0 + 2) ^ 3 : ℕ) : PowerSeries ℤ) = PowerSeries.C (8 : ℤ) := by norm_num
      rw [h8c, PowerSeries.map_C]
      have h8z : (Int.castRingHom (ZMod 2)) 8 = 0 := by decide
      rw [h8z, map_zero]
    rw [map_mul, map_sub, map_mul, map_mul, h8, zero_mul, zero_mul, sub_zero, map_one] at h0
    exact h0
  -- Reduce A - 1 = X * R 0 mod 2 => a2 + 1 = X * φ (R 0)
  have ha2_sub : a2 + 1 = PowerSeries.X * φ (R 0) := by
    have h := congrArg φ hR0
    have hX : φ PowerSeries.X = PowerSeries.X := PowerSeries.map_X _
    rw [map_sub, map_one, map_mul, zmod2_ps_sub, hX] at h
    exact h
  -- Multiply by a2: (a2 + 1) * a2 = X * (φ (R 0) * a2) = X
  set u : PowerSeries (ZMod 2) := a2 + 1
  have hu0 : PowerSeries.constantCoeff u = 0 := by
    dsimp only [u]; rw [map_add, ha2_0, map_one]; decide
  have hu_quad : u + u ^ 2 = PowerSeries.X := by
    have hmul : (a2 + 1) * a2 = PowerSeries.X := by
      calc (a2 + 1) * a2 = u * a2 := rfl
        _ = (PowerSeries.X * φ (R 0)) * a2 := by rw [ha2_sub]
        _ = PowerSeries.X * (φ (R 0) * a2) := by ring
        _ = PowerSeries.X * 1 := by rw [hR0_mul]
        _ = PowerSeries.X := mul_one _
    have h1 : a2 = u + 1 := by
      dsimp only [u]; rw [add_assoc, zmod2_ps_add_self, add_zero]
    rw [← hmul, h1]
    calc u + u ^ 2 = u * (u + 1) := by ring
      _ = (u + 1 + 1) * (u + 1) := by rw [add_assoc, zmod2_ps_add_self, add_zero]
  -- Uniqueness: (u + u0) = (u + u0)^2 with constantCoeff 0 => u = u0
  have hdiff : u + u0 = (u + u0) ^ 2 := by
    have hadd : (u + u ^ 2) + (u0 + u0 ^ 2) = PowerSeries.X + PowerSeries.X := by rw [hu_quad, u0_quad]
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
  intro n hn
  rw [odd_iff_zmod2_eq_one]
  have hc : ((PowerSeries.coeff n A : ℤ) : ZMod 2) = PowerSeries.coeff n u0 := by
    rw [← hu_eq]
    dsimp only [u]
    rw [map_add, PowerSeries.coeff_one, if_neg (by omega), add_zero, PowerSeries.coeff_map]
    rfl
  rw [hc, coeff_u0]
  by_cases h : ∃ k : ℕ, n = 2 ^ k
  · simp [h]
  · simp [h]

end OMA.P_oeis_a338633

theorem OMA.solution : type_of% @OMA.S_oeis_a338633.main :=
  OMA.P_oeis_a338633.prove_main
