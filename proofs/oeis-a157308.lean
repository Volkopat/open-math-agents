import OMAStatements.S_oeis_a157308
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace OMA.P_oeis_a157308

open PowerSeries

private lemma hasSubst_of_const_zero {R : Type*} [CommRing R]
    {g : PowerSeries R} (hg : g.constantCoeff = 0) : PowerSeries.HasSubst g :=
  PowerSeries.HasSubst.of_constantCoeff_zero hg

private lemma coeff_sq_odd_zmod2 (f : PowerSeries (ZMod 2)) (k : ℕ) :
    PowerSeries.coeff (2 * k + 1) (f * f) = 0 := by
  rw [PowerSeries.coeff_mul]
  have hsplit : Finset.antidiagonal (2 * k + 1) =
      (Finset.antidiagonal (2 * k + 1)).filter (fun p => p.1 ≤ k) ∪
      (Finset.antidiagonal (2 * k + 1)).filter (fun p => k < p.1) := by
    ext p; simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp; by_cases h : p.1 ≤ k
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr ⟨hp, by omega⟩
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  have hdisj : Disjoint ((Finset.antidiagonal (2 * k + 1)).filter (fun p => p.1 ≤ k))
      ((Finset.antidiagonal (2 * k + 1)).filter (fun p => k < p.1)) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter] at hp1 hp2; omega
  have hbij :
      ∑ p ∈ (Finset.antidiagonal (2 * k + 1)).filter (fun p => k < p.1),
        PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 f =
      ∑ p ∈ (Finset.antidiagonal (2 * k + 1)).filter (fun p => p.1 ≤ k),
        PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 f := by
    refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp ⊢; omega
    · intro p1 _ p2 _ h
      rcases p1 with ⟨a1, b1⟩; rcases p2 with ⟨a2, b2⟩
      simp only [Prod.mk.injEq] at h ⊢; exact ⟨h.2, h.1⟩
    · intro q hq
      refine ⟨(q.2, q.1), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hq ⊢; omega
    · intro p _; exact mul_comm _ _
  rw [hsplit, Finset.sum_union hdisj, hbij]
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  exact h2 _

private lemma coeff_even_pow_odd_zmod2 (g : PowerSeries (ZMod 2)) (m k : ℕ) :
    PowerSeries.coeff (2 * k + 1) (g ^ (2 * m)) = 0 := by
  have h : g ^ (2 * m) = (g ^ m) * (g ^ m) := by rw [← pow_add, two_mul]
  rw [h]
  exact coeff_sq_odd_zmod2 (g ^ m) k

private lemma coeff_pow_lt_zero {R : Type*} [CommRing R] {g : PowerSeries R}
    (hg : g.constantCoeff = 0) : ∀ k n : ℕ, n < k → PowerSeries.coeff n (g ^ k) = 0 := by
  intro k
  induction k with
  | zero => intro n hn; omega
  | succ k ih =>
    intro n hn
    rw [pow_succ, PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    have hsum := Finset.mem_antidiagonal.mp hp
    by_cases hp2 : p.2 = 0
    · rw [hp2, PowerSeries.coeff_zero_eq_constantCoeff, hg, mul_zero]
    · rw [ih p.1 (by omega), zero_mul]

private lemma coeff_subst_range {R : Type*} [CommRing R] {f g : PowerSeries R}
    (hg : g.constantCoeff = 0) (n : ℕ) :
    PowerSeries.coeff n (f.subst g) =
      ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k f * PowerSeries.coeff n (g ^ k) := by
  rw [PowerSeries.coeff_subst' (hasSubst_of_const_zero hg)]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro k hk
  rw [Function.mem_support] at hk
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hge
  exact hk (by rw [coeff_pow_lt_zero hg k n (by omega), mul_zero])

private lemma pow_two_pow_zmod2 (a b : PowerSeries (ZMod 2)) (k : ℕ) :
    (a + b) ^ (2 ^ k) = a ^ (2 ^ k) + b ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul, ih, pow_two]
    have h2 : (2 : PowerSeries (ZMod 2)) = 0 := by
      have hc : (2 : ZMod 2) = 0 := rfl
      rw [show (2 : PowerSeries (ZMod 2)) = PowerSeries.C (2 : ZMod 2) from rfl, hc, map_zero]
    have hexp : (a ^ (2 ^ k) + b ^ (2 ^ k)) * (a ^ (2 ^ k) + b ^ (2 ^ k)) =
        (a ^ (2 ^ k)) ^ 2 + (b ^ (2 ^ k)) ^ 2 + 2 * (a ^ (2 ^ k) * b ^ (2 ^ k)) := by ring
    rw [hexp, h2, zero_mul, add_zero, ← pow_mul, ← pow_mul]

private noncomputable def T2 : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun m =>
    open Classical in
    if m = 0 ∨ ∃ k : ℕ, m = 2 ^ k then 1 else 0

private lemma T2_subst_X_add_X_sq :
    T2.subst (PowerSeries.X + PowerSeries.X ^ 2) = (1 + PowerSeries.X : PowerSeries (ZMod 2)) := by
  have hg : (PowerSeries.X + PowerSeries.X ^ 2 : PowerSeries (ZMod 2)).constantCoeff = 0 := by simp
  ext n
  rw [coeff_subst_range hg n]
  have hT_coeff : ∀ k : ℕ, PowerSeries.coeff k T2 =
      open Classical in if k = 0 ∨ ∃ j : ℕ, k = 2 ^ j then (1 : ZMod 2) else 0 := by
    intro k; simp [T2]
  cases n with
  | zero =>
    simp [T2]
  | succ n =>
    classical
    have hterm : ∀ k ∈ Finset.range (n + 2),
        PowerSeries.coeff k T2 * PowerSeries.coeff (n + 1) ((PowerSeries.X + PowerSeries.X ^ 2) ^ k) =
        if k = 0 then 0
        else if ∃ j : ℕ, k = 2 ^ j then
          (if n + 1 = k then (1 : ZMod 2) else 0) + (if n + 1 = 2 * k then 1 else 0)
        else 0 := by
      intro k _
      rw [hT_coeff k]
      by_cases hk0 : k = 0
      · subst hk0; simp
      · rw [if_neg hk0]
        by_cases hpow : ∃ j : ℕ, k = 2 ^ j
        · rw [if_pos (Or.inr hpow), if_pos hpow, one_mul]
          rcases hpow with ⟨j, rfl⟩
          rw [pow_two_pow_zmod2, ← pow_mul, mul_comm 2 (2 ^ j), map_add,
              PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow, mul_comm (2 ^ j) 2]
        · rw [if_neg (by tauto), if_neg hpow, zero_mul]
    rw [Finset.sum_congr rfl hterm]
    by_cases hn1 : n + 1 = 1
    · have hn0 : n = 0 := by omega
      subst hn0
      have h1_pow : ∃ j : ℕ, (1 : ℕ) = 2 ^ j := ⟨0, rfl⟩
      simp [Finset.sum_range_succ, h1_pow]
    · have hrhs : PowerSeries.coeff (n + 1) (1 + PowerSeries.X : PowerSeries (ZMod 2)) = 0 := by
        have hn0 : n ≠ 0 := by omega
        simp [PowerSeries.coeff_one, PowerSeries.coeff_X, hn0]
      rw [hrhs]
      by_cases hex : ∃ j : ℕ, n + 1 = 2 ^ j
      · rcases hex with ⟨j, hj⟩
        cases j with
        | zero => simp at hj; omega
        | succ j =>
          have hpow_pos : 0 < 2 ^ j := by positivity
          have hj_lt : 2 ^ j < 2 ^ (j + 1) := by rw [pow_succ]; omega
          have hj1_mem : 2 ^ (j + 1) ∈ Finset.range (n + 2) := by rw [Finset.mem_range]; omega
          have hj0_mem : 2 ^ j ∈ Finset.range (n + 2) := by rw [Finset.mem_range]; omega
          have hne : 2 ^ j ≠ 2 ^ (j + 1) := by omega
          have hzero : ∀ k ∈ Finset.range (n + 2), k ≠ 2 ^ j → k ≠ 2 ^ (j + 1) →
              (if k = 0 then (0 : ZMod 2)
               else if ∃ m : ℕ, k = 2 ^ m then
                 (if n + 1 = k then (1 : ZMod 2) else 0) + (if n + 1 = 2 * k then 1 else 0)
               else 0) = 0 := by
            intro k _ hk1 hk2
            by_cases h0 : k = 0
            · rw [if_pos h0]
            · rw [if_neg h0]
              by_cases hpow : ∃ m : ℕ, k = 2 ^ m
              · rw [if_pos hpow, if_neg (by omega), if_neg (by rw [hj, pow_succ]; omega), add_zero]
              · rw [if_neg hpow]
          let f : ℕ → ZMod 2 := fun k =>
            if k = 0 then (0 : ZMod 2)
            else if ∃ m : ℕ, k = 2 ^ m then
              (if n + 1 = k then (1 : ZMod 2) else 0) + (if n + 1 = 2 * k then 1 else 0)
            else 0
          change ∑ k ∈ Finset.range (n + 2), f k = 0
          rw [← Finset.add_sum_erase _ _ hj1_mem]
          have hj0_er : 2 ^ j ∈ (Finset.range (n + 2)).erase (2 ^ (j + 1)) :=
            Finset.mem_erase.mpr ⟨hne, hj0_mem⟩
          rw [← Finset.add_sum_erase _ _ hj0_er]
          have hrest : ∑ k ∈ ((Finset.range (n + 2)).erase (2 ^ (j + 1))).erase (2 ^ j), f k = 0 := by
            apply Finset.sum_eq_zero
            intro k hk
            simp only [Finset.mem_erase] at hk
            exact hzero k hk.2.2 hk.1 hk.2.1
          rw [hrest, add_zero]
          have hv1 : f (2 ^ j) = 1 := by
            simp only [f]
            have hnz : 2 ^ j ≠ 0 := by positivity
            rw [if_neg hnz, if_pos ⟨j, rfl⟩, if_neg (by omega), if_pos (by rw [hj, pow_succ]; ring), zero_add]
          have hv2 : f (2 ^ (j + 1)) = 1 := by
            simp only [f]
            have hnz : 2 ^ (j + 1) ≠ 0 := by positivity
            rw [if_neg hnz, if_pos ⟨j + 1, rfl⟩, if_pos hj, if_neg (by omega), add_zero]
          rw [hv2, hv1]; decide
      · apply Finset.sum_eq_zero
        intro k _
        by_cases h0 : k = 0
        · rw [if_pos h0]
        · rw [if_neg h0]
          by_cases hpow : ∃ j : ℕ, k = 2 ^ j
          · rw [if_pos hpow]
            rcases hpow with ⟨j, rfl⟩
            have h1 : n + 1 ≠ 2 ^ j := fun h => hex ⟨j, h⟩
            have h2 : n + 1 ≠ 2 * 2 ^ j := fun h => hex ⟨j + 1, by rw [pow_succ]; linarith⟩
            rw [if_neg h1, if_neg h2, add_zero]
          · rw [if_neg hpow]

private lemma subst_X_add_X_sq_inj {f₁ f₂ : PowerSeries (ZMod 2)}
    (h : f₁.subst (PowerSeries.X + PowerSeries.X ^ 2 : PowerSeries (ZMod 2)) =
         f₂.subst (PowerSeries.X + PowerSeries.X ^ 2 : PowerSeries (ZMod 2))) : f₁ = f₂ := by
  have hg : (PowerSeries.X + PowerSeries.X ^ 2 : PowerSeries (ZMod 2)).constantCoeff = 0 := by simp
  have hg1 : ∀ n : ℕ, PowerSeries.coeff n ((PowerSeries.X + PowerSeries.X ^ 2 : PowerSeries (ZMod 2)) ^ n) = 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, PowerSeries.coeff_mul]
      rw [Finset.sum_eq_single (n, 1)]
      · rw [ih, one_mul]; simp [PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
      · intro p hp hne
        have hsum := Finset.mem_antidiagonal.mp hp
        by_cases hp1 : p.1 < n
        · rw [coeff_pow_lt_zero hg n p.1 hp1, zero_mul]
        · have hp2 : p.2 = 0 := by
            rcases p with ⟨a, b⟩
            simp only at hp1 hne ⊢
            by_contra hne0
            have ha : a = n := by omega
            have hb : b = 1 := by omega
            exact hne (Prod.ext ha hb)
          rw [hp2, PowerSeries.coeff_zero_eq_constantCoeff, hg, mul_zero]
      · intro hnot
        exact absurd (Finset.mem_antidiagonal.mpr rfl : (n, 1) ∈ Finset.antidiagonal (n + 1)) hnot
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hcoeff := congrArg (PowerSeries.coeff n) h
    rw [coeff_subst_range hg n, coeff_subst_range hg n,
        Finset.sum_range_succ, Finset.sum_range_succ] at hcoeff
    have hlow : ∑ k ∈ Finset.range n, PowerSeries.coeff k f₁ *
          PowerSeries.coeff n ((PowerSeries.X + PowerSeries.X ^ 2) ^ k) =
        ∑ k ∈ Finset.range n, PowerSeries.coeff k f₂ *
          PowerSeries.coeff n ((PowerSeries.X + PowerSeries.X ^ 2) ^ k) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [ih k hk]
    rw [hlow, hg1 n, mul_one, mul_one] at hcoeff
    exact add_left_cancel hcoeff

private lemma prove_main :
    ∀ A F : PowerSeries ℤ,
      PowerSeries.coeff 0 A = 1 →
      PowerSeries.coeff 1 A = 1 →
      PowerSeries.coeff 0 F = 1 →
      PowerSeries.coeff 1 F = 1 →
      (∀ k : ℕ, 1 ≤ k → PowerSeries.coeff (2 * k + 1) A = 0) →
      (∀ k : ℕ, 1 ≤ k → PowerSeries.coeff (2 * k + 1) F = 0) →
      F = A.subst (PowerSeries.X * F) →
      ∀ m : ℕ, PowerSeries.coeff m A % 2 = 1 ↔ (m = 0 ∨ ∃ k : ℕ, m = 2 ^ k) := by
  intro A F hA0 hA1 hF0 hF1 hAodd hFodd hEq
  let φ := Int.castRingHom (ZMod 2)
  let A2 : PowerSeries (ZMod 2) := PowerSeries.map φ A
  let F2 : PowerSeries (ZMod 2) := PowerSeries.map φ F
  have hXF0 : (PowerSeries.X * F).constantCoeff = 0 := by simp
  have hXF2_0 : (PowerSeries.X * F2).constantCoeff = 0 := by simp
  have hEq2 : F2 = A2.subst (PowerSeries.X * F2) := by
    have h := congrArg (PowerSeries.map φ) hEq
    have hmap : PowerSeries.map φ (A.subst (PowerSeries.X * F)) = A2.subst (PowerSeries.X * F2) := by
      ext n
      rw [PowerSeries.coeff_map, coeff_subst_range hXF0 n, coeff_subst_range hXF2_0 n, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hpow : (PowerSeries.X * F2) ^ k = PowerSeries.map φ ((PowerSeries.X * F) ^ k) := by
        simp [F2, map_pow, map_mul, PowerSeries.map_X]
      rw [hpow, map_mul, PowerSeries.coeff_map, PowerSeries.coeff_map]
    simpa [F2, hmap] using h
  have hA2_1 : PowerSeries.coeff 1 A2 = 1 := by simp [A2, φ, hA1]
  have hA2_odd : ∀ k : ℕ, 1 ≤ k → PowerSeries.coeff (2 * k + 1) A2 = 0 := by
    intro k hk; simp [A2, φ, hAodd k hk]
  have hF2_0 : PowerSeries.coeff 0 F2 = 1 := by simp [F2, φ, hF0]
  have hF2_1 : PowerSeries.coeff 1 F2 = 1 := by simp [F2, φ, hF1]
  have hF2_odd : ∀ k : ℕ, 1 ≤ k → PowerSeries.coeff (2 * k + 1) F2 = 0 := by
    intro k hk; simp [F2, φ, hFodd k hk]
  -- Step 1: F2 = 1 + X!
  have hF2_even_zero : ∀ k : ℕ, 1 ≤ k → PowerSeries.coeff (2 * k) F2 = 0 := by
    intro k hk
    have hcoeff := congrArg (PowerSeries.coeff (2 * k + 1)) hEq2
    rw [hF2_odd k hk, coeff_subst_range hXF2_0 (2 * k + 1)] at hcoeff
    rw [Finset.sum_eq_single 1] at hcoeff
    · rw [hA2_1, one_mul, pow_one, PowerSeries.coeff_succ_X_mul] at hcoeff
      exact hcoeff.symm
    · intro j _ hj1
      by_cases hj_ev : j % 2 = 0
      · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m := ⟨j / 2, by omega⟩
        rw [coeff_even_pow_odd_zmod2 (PowerSeries.X * F2) m k, mul_zero]
      · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m + 1 := ⟨j / 2, by omega⟩
        have hm1 : 1 ≤ m := by omega
        rw [hA2_odd m hm1, zero_mul]
    · intro hnot
      exact absurd (Finset.mem_range.mpr (by omega)) hnot
  have hF2_eq : F2 = (1 + PowerSeries.X : PowerSeries (ZMod 2)) := by
    ext n
    match n with
    | 0 => simp [hF2_0]
    | 1 => simp [hF2_1]
    | m + 2 =>
      rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_X,
          if_neg (by omega), if_neg (by omega), add_zero]
      by_cases hev : (m + 2) % 2 = 0
      · rw [show m + 2 = 2 * ((m + 2) / 2) by omega]
        exact hF2_even_zero ((m + 2) / 2) (by omega)
      · rw [show m + 2 = 2 * ((m + 2) / 2) + 1 by omega]
        exact hF2_odd ((m + 2) / 2) (by omega)
  -- Step 2: A2.subst (X + X^2) = 1 + X = T2.subst (X + X^2), hence A2 = T2!
  have hA2_subst : A2.subst (PowerSeries.X + PowerSeries.X ^ 2) =
      (1 + PowerSeries.X : PowerSeries (ZMod 2)) := by
    have hmul : PowerSeries.X * (1 + PowerSeries.X : PowerSeries (ZMod 2)) =
        PowerSeries.X + PowerSeries.X ^ 2 := by ring
    rw [hF2_eq, hmul] at hEq2
    exact hEq2.symm
  have hA2_eq_T2 : A2 = T2 := subst_X_add_X_sq_inj (hA2_subst.trans T2_subst_X_add_X_sq.symm)
  -- Step 3: Conclude coeff m A % 2 = 1 ↔ m = 0 ∨ ∃ k, m = 2^k
  intro m
  have hcoeff := congrArg (PowerSeries.coeff m) hA2_eq_T2
  simp only [A2, T2, PowerSeries.coeff_map, PowerSeries.coeff_mk, φ, Int.coe_castRingHom] at hcoeff
  have hmod2 : ∀ z : ℤ, ((z : ZMod 2) = 1 ↔ z % 2 = 1) := by
    intro z
    constructor
    · intro hz
      have h0 : ((z - 1 : ℤ) : ZMod 2) = 0 := by push_cast; rw [hz]; decide
      have hdvd : (2 : ℤ) ∣ z - 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h0
      omega
    · intro hz
      have hdvd : (2 : ℤ) ∣ z - 1 := by omega
      have h0 : ((z - 1 : ℤ) : ZMod 2) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr hdvd
      push_cast at h0
      exact sub_eq_zero.mp h0
  rw [← hmod2, hcoeff]
  by_cases h : m = 0 ∨ ∃ k : ℕ, m = 2 ^ k
  · simp [h]
  · simp [h]

end OMA.P_oeis_a157308

theorem OMA.solution : type_of% @OMA.S_oeis_a157308.main :=
  OMA.P_oeis_a157308.prove_main
