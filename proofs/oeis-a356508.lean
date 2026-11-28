import OMAStatements.S_oeis_a356508
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a356508

open OMA.S_oeis_a356508

private lemma zmod2_ps_two : (2 : PowerSeries (ZMod 2)) = 0 := by
  have h : (2 : ZMod 2) = 0 := by decide
  rw [← map_ofNat (PowerSeries.C (R := ZMod 2)), h, map_zero]

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

private lemma partition_prod_cancel_zmod2 (r : ℕ) :
    PowerSeries.coeff r
      ((PowerSeries.mk (fun n => (Fintype.card (Nat.Partition n) : ZMod 2))) *
        ∏ m ∈ Finset.Icc 1 r, (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ m)) =
    if r = 0 then 1 else 0 := by
  let _ : TopologicalSpace (ZMod 2) := ⊥
  have _ : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  open scoped PowerSeries.WithPiTopology in
  have hP_eq : PowerSeries.mk (fun n => (Fintype.card (Nat.Partition n) : ZMod 2)) =
      Nat.Partition.genFun (fun _ _ => (1 : ZMod 2)) := by
    ext n
    rw [PowerSeries.coeff_mk, Nat.Partition.coeff_genFun]
    simp [Finsupp.prod]
  rw [hP_eq]
  have hprod := Nat.Partition.hasProd_genFun (fun _ _ => (1 : ZMod 2))
  -- At coefficient r, the infinite product equals the finite product over range r!
  have hcoeff_eq : ∀ k ≤ r,
      PowerSeries.coeff k (Nat.Partition.genFun (fun _ _ => (1 : ZMod 2))) =
      PowerSeries.coeff k
        (∏ i ∈ Finset.range r,
          ((1 : PowerSeries (ZMod 2)) + ∑' j, (1 : ZMod 2) • PowerSeries.X ^ ((i + 1) * (j + 1)))) := by
    intro k hk
    rw [HasProd, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto] at hprod
    have ht := hprod k
    -- Also for any s ≥ range r, the product over s agrees with range r on coeff k
    have hev : ∀ᶠ s : Finset ℕ in Filter.atTop,
        PowerSeries.coeff k (∏ i ∈ s, ((1 : PowerSeries (ZMod 2)) +
            ∑' j, (1 : ZMod 2) • PowerSeries.X ^ ((i + 1) * (j + 1)))) =
        PowerSeries.coeff k (∏ i ∈ Finset.range r, ((1 : PowerSeries (ZMod 2)) +
            ∑' j, (1 : ZMod 2) • PowerSeries.X ^ ((i + 1) * (j + 1)))) := by
      refine Filter.eventually_atTop.mpr ⟨Finset.range r, fun s hs => ?_⟩
      rw [← Finset.prod_sdiff hs]
      have hdiff : ∀ i ∈ s \ Finset.range r,
          PowerSeries.constantCoeff ((1 : PowerSeries (ZMod 2)) +
              ∑' j, (1 : ZMod 2) • PowerSeries.X ^ ((i + 1) * (j + 1))) = 1 ∧
          ∀ t, 1 ≤ t → t ≤ k → PowerSeries.coeff t ((1 : PowerSeries (ZMod 2)) +
              ∑' j, (1 : ZMod 2) • PowerSeries.X ^ ((i + 1) * (j + 1))) = 0 := by
        intro i hi
        have hir : r ≤ i := by
          have := (Finset.mem_sdiff.mp hi).2
          rw [Finset.mem_range] at this; omega
        have hsum := Nat.Partition.summable_genFun_term (fun _ _ => (1 : ZMod 2)) i
        have htsum_zero : ∀ t ≤ k, PowerSeries.coeff t
            (∑' j, (1 : ZMod 2) • (PowerSeries.X : PowerSeries (ZMod 2)) ^ ((i + 1) * (j + 1))) = 0 := by
          intro t ht
          have hc := (hsum.hasSum.map (PowerSeries.coeff t)
            (PowerSeries.WithPiTopology.continuous_coeff (R := ZMod 2) t)).tsum_eq.symm
          rw [hc]
          have hfun : (PowerSeries.coeff t ∘ fun j : ℕ =>
              (1 : ZMod 2) • (PowerSeries.X : PowerSeries (ZMod 2)) ^ ((i + 1) * (j + 1))) = 0 := by
            funext j
            simp only [Function.comp_apply, one_smul, Pi.zero_apply, PowerSeries.coeff_X_pow]
            rw [if_neg]; nlinarith
          rw [hfun]; simp
        constructor
        · rw [← PowerSeries.coeff_zero_eq_constantCoeff, map_add, PowerSeries.coeff_one,
              if_pos rfl, htsum_zero 0 (Nat.zero_le k), add_zero]
        · intro t ht1 htk
          rw [map_add, PowerSeries.coeff_one, if_neg (by omega), zero_add, htsum_zero t htk]
      -- Multiplying by a product of series that are 1 + O(X^(k+1)) preserves coeff k
      have hmul_pres : ∀ (T : Finset ℕ) (g : PowerSeries (ZMod 2)),
          (∀ i ∈ T, PowerSeries.constantCoeff ((1 : PowerSeries (ZMod 2)) +
              ∑' j, (1 : ZMod 2) • PowerSeries.X ^ ((i + 1) * (j + 1))) = 1 ∧
            ∀ t, 1 ≤ t → t ≤ k → PowerSeries.coeff t ((1 : PowerSeries (ZMod 2)) +
              ∑' j, (1 : ZMod 2) • PowerSeries.X ^ ((i + 1) * (j + 1))) = 0) →
          PowerSeries.coeff k ((∏ i ∈ T, ((1 : PowerSeries (ZMod 2)) +
              ∑' j, (1 : ZMod 2) • PowerSeries.X ^ ((i + 1) * (j + 1)))) * g) =
          PowerSeries.coeff k g := by
        intro T
        induction T using Finset.cons_induction with
        | empty => intro g _; simp
        | cons a s ha ih =>
          intro g hT
          rw [Finset.prod_cons, mul_assoc]
          have h1 := hT a (Finset.mem_cons_self a s)
          have h2 := ih g (fun i hi => hT i (Finset.mem_cons_of_mem hi))
          rw [PowerSeries.coeff_mul, Finset.sum_eq_single (0, k)]
          · rw [PowerSeries.coeff_zero_eq_constantCoeff, h1.1, one_mul, h2]
          · intro p hp hne
            have hsum : p.1 + p.2 = k := Finset.mem_antidiagonal.mp hp
            have hp1 : 1 ≤ p.1 := by
              by_contra h0; apply hne; exact Prod.ext (by omega) (by omega)
            rw [h1.2 p.1 hp1 (by omega), zero_mul]
          · intro h; exact absurd (Finset.mem_antidiagonal.mpr (zero_add k)) h
      exact hmul_pres (s \ Finset.range r) _ hdiff
    have hlim : Filter.Tendsto (fun s : Finset ℕ =>
        PowerSeries.coeff k (∏ i ∈ s, ((1 : PowerSeries (ZMod 2)) +
            ∑' j, (1 : ZMod 2) • PowerSeries.X ^ ((i + 1) * (j + 1)))))
        Filter.atTop (nhds (PowerSeries.coeff k (∏ i ∈ Finset.range r, ((1 : PowerSeries (ZMod 2)) +
            ∑' j, (1 : ZMod 2) • PowerSeries.X ^ ((i + 1) * (j + 1)))))) :=
      tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm)
    exact tendsto_nhds_unique ht hlim
  -- Replace genFun by the finite product over range r inside coeff r
  have hmul_eq :
      PowerSeries.coeff r
        ((Nat.Partition.genFun (fun _ _ => (1 : ZMod 2))) *
          ∏ m ∈ Finset.Icc 1 r, (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ m)) =
      PowerSeries.coeff r
        ((∏ i ∈ Finset.range r,
          ((1 : PowerSeries (ZMod 2)) + ∑' j, (1 : ZMod 2) • PowerSeries.X ^ ((i + 1) * (j + 1)))) *
          ∏ m ∈ Finset.Icc 1 r, (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ m)) := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp1 : p.1 ≤ r := by have := Finset.mem_antidiagonal.mp hp; omega
    rw [hcoeff_eq p.1 hp1]
  rw [hmul_eq]
  -- Reindex Icc 1 r to range r via m = i + 1
  have hprod_reindex :
      ∏ m ∈ Finset.Icc 1 r, (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ m) =
      ∏ i ∈ Finset.range r, (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ (i + 1)) := by
    refine Finset.prod_bij (fun m _ => m - 1) ?_ ?_ ?_ ?_
    · intro m hm; simp only [Finset.mem_Icc, Finset.mem_range] at hm ⊢; omega
    · intro m1 hm1 m2 hm2 h; simp only [Finset.mem_Icc] at hm1 hm2; omega
    · intro i hi; simp only [Finset.mem_range, Finset.mem_Icc] at hi ⊢
      exact ⟨i + 1, by omega, by omega⟩
    · intro m hm; simp only [Finset.mem_Icc] at hm; rw [Nat.sub_add_cancel hm.1]
  rw [hprod_reindex, ← Finset.prod_mul_distrib]
  -- Each factor (1 + ∑' j, X^((i+1)*(j+1))) * (1 + X^(i+1)) = 1 in ZMod 2[[X]]!
  have hfac : ∀ i : ℕ,
      ((1 : PowerSeries (ZMod 2)) + ∑' j, (1 : ZMod 2) • PowerSeries.X ^ ((i + 1) * (j + 1))) *
        (1 + PowerSeries.X ^ (i + 1)) = 1 := by
    intro i
    have hsum := Nat.Partition.summable_genFun_term (fun _ _ => (1 : ZMod 2)) i
    have hcoeff_geom : ∀ k : ℕ,
        PowerSeries.coeff k
          ((1 : PowerSeries (ZMod 2)) + ∑' j, (1 : ZMod 2) • PowerSeries.X ^ ((i + 1) * (j + 1))) =
        if (i + 1) ∣ k then 1 else 0 := by
      intro k
      rw [map_add, PowerSeries.coeff_one]
      have hc := (hsum.hasSum.map (PowerSeries.coeff k)
        (PowerSeries.WithPiTopology.continuous_coeff (R := ZMod 2) k)).tsum_eq.symm
      rw [hc]
      cases k with
      | zero =>
        rw [if_pos rfl, if_pos (dvd_zero _)]
        have hfun : (PowerSeries.coeff 0 ∘ fun j : ℕ =>
            (1 : ZMod 2) • (PowerSeries.X : PowerSeries (ZMod 2)) ^ ((i + 1) * (j + 1))) = 0 := by
          funext j
          simp only [Function.comp_apply, one_smul, Pi.zero_apply, PowerSeries.coeff_X_pow]
          rw [if_neg (by positivity)]
        rw [hfun]; simp
      | succ t =>
        rw [if_neg (by omega), zero_add]
        by_cases hd : (i + 1) ∣ (t + 1)
        · rw [if_pos hd]
          rcases hd with ⟨q, hq⟩
          have hq1 : 1 ≤ q := by
            rcases q with _ | q'; · simp at hq
            omega
          rw [tsum_eq_single (q - 1)]
          · simp only [Function.comp_apply, one_smul, PowerSeries.coeff_X_pow]
            rw [if_pos (by rw [Nat.sub_add_cancel hq1, ← hq])]
          · intro j hj
            simp only [Function.comp_apply, one_smul, PowerSeries.coeff_X_pow]
            rw [if_neg]
            intro heq
            have : j + 1 = q := Nat.eq_of_mul_eq_mul_left (by omega : 0 < i + 1) (by linarith)
            omega
        · rw [if_neg hd]
          have hfun : (PowerSeries.coeff (t + 1) ∘ fun j : ℕ =>
              (1 : ZMod 2) • (PowerSeries.X : PowerSeries (ZMod 2)) ^ ((i + 1) * (j + 1))) = 0 := by
            funext j
            simp only [Function.comp_apply, one_smul, Pi.zero_apply, PowerSeries.coeff_X_pow]
            rw [if_neg]
            intro heq
            exact hd ⟨j + 1, heq⟩
          rw [hfun]; simp
    ext k
    rw [mul_add, mul_one, map_add, PowerSeries.coeff_one, mul_comm _ (PowerSeries.X ^ (i + 1)),
        PowerSeries.coeff_X_pow_mul', hcoeff_geom k]
    by_cases hle : i + 1 ≤ k
    · rw [if_pos hle, hcoeff_geom (k - (i + 1)), if_neg (by omega : k ≠ 0)]
      have hiff : (i + 1) ∣ k ↔ (i + 1) ∣ (k - (i + 1)) := by
        constructor
        · rintro ⟨q, hq⟩; refine ⟨q - 1, ?_⟩
          have hq1 : 1 ≤ q := by rcases q with _ | q' <;> nlinarith
          have : (i + 1) * (q - 1) + (i + 1) = (i + 1) * q := by
            rw [← mul_add_one, Nat.sub_add_cancel hq1]
          omega
        · rintro ⟨q, hq⟩; exact ⟨q + 1, by rw [mul_add_one]; omega⟩
      by_cases hd : (i + 1) ∣ k
      · rw [if_pos hd, if_pos (hiff.mp hd)]; decide
      · rw [if_neg hd, if_neg (fun h => hd (hiff.mpr h))]; decide
    · rw [if_neg hle, add_zero]
      cases k with
      | zero => simp
      | succ t =>
        rw [if_neg (by omega : t + 1 ≠ 0), if_neg]
        rintro ⟨q, hq⟩
        rcases q with _ | q'
        · simp at hq
        · nlinarith
  rw [Finset.prod_eq_one (fun i _ => hfac i), PowerSeries.coeff_one]

theorem solution : type_of% @OMA.S_oeis_a356508.main := by
  intro A hA0 hEq
  have hAu : IsUnit A := PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hA0]; exact isUnit_one)
  have hAinv : A * Ring.inverse A = 1 := Ring.mul_inverse_cancel A hAu
  have hAinv0 : PowerSeries.constantCoeff (Ring.inverse A) = 1 := by
    have h := congrArg PowerSeries.constantCoeff hAinv
    rw [map_mul, hA0, one_mul, map_one] at h; exact h
  -- Step 1: Prove by strong induction that 2 ∣ coeff r A and 2 ∣ coeff r (Ring.inverse A) for r ≥ 1
  have heven : ∀ r : ℕ, 1 ≤ r →
      (2 : ℤ) ∣ PowerSeries.coeff r A ∧ (2 : ℤ) ∣ PowerSeries.coeff r (Ring.inverse A) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro hr
      have h1 := hEq r
      rw [if_neg (by omega)] at h1
      have hIcc : Finset.Icc 1 (r + 1) = insert 1 (Finset.Icc 2 (r + 1)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.prod_insert (by simp)] at h1
      simp only [pow_one, Nat.sub_self, pow_zero, one_mul] at h1
      set U : PowerSeries ℤ := (1 + PowerSeries.X * A) *
          ∏ n ∈ Finset.Icc 2 (r + 1),
            (1 + PowerSeries.X ^ n * A) * (1 + PowerSeries.X ^ (n - 1) * Ring.inverse A)
      have hU0 : PowerSeries.constantCoeff U = 1 := by
        dsimp only [U]
        rw [map_mul, map_add, map_one, map_mul, PowerSeries.constantCoeff_X, zero_mul, add_zero,
            one_mul, map_prod]
        refine Finset.prod_eq_one fun n hn => ?_
        have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
        rw [map_mul, map_add, map_add, map_one, map_mul, map_mul, map_pow, map_pow,
            PowerSeries.constantCoeff_X, zero_pow (by omega), zero_pow (by omega),
            zero_mul, zero_mul, add_zero, mul_one]
      have hprod_rearr : (1 + PowerSeries.X * A) * (1 + Ring.inverse A) *
          (∏ n ∈ Finset.Icc 2 (r + 1),
            (1 + PowerSeries.X ^ n * A) * (1 + PowerSeries.X ^ (n - 1) * Ring.inverse A)) =
          U * (1 + Ring.inverse A) := by
        dsimp only [U]; ring
      rw [hprod_rearr, PowerSeries.coeff_mul] at h1
      have hdiv_inv : (2 : ℤ) ∣ PowerSeries.coeff r (Ring.inverse A) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_antidiagonal.mpr (zero_add r) : (0, r) ∈ Finset.antidiagonal r)] at h1
        rw [PowerSeries.coeff_zero_eq_constantCoeff, hU0, one_mul, map_add,
            PowerSeries.coeff_one, if_neg (by omega), zero_add] at h1
        have htail : (2 : ℤ) ∣ ∑ p ∈ (Finset.antidiagonal r).erase (0, r),
            PowerSeries.coeff p.1 U * PowerSeries.coeff p.2 (1 + Ring.inverse A) := by
          refine Finset.dvd_sum fun p hp => ?_
          have hmem := Finset.mem_erase.mp hp
          have hsum : p.1 + p.2 = r := Finset.mem_antidiagonal.mp hmem.2
          have hp2_lt : p.2 < r := by
            by_contra hge
            apply hmem.1; exact Prod.ext (by omega) (by omega)
          refine dvd_mul_of_dvd_right ?_ _
          cases h2 : p.2 with
          | zero =>
            rw [PowerSeries.coeff_zero_eq_constantCoeff, map_add, map_one, hAinv0]; decide
          | succ m =>
            rw [map_add, PowerSeries.coeff_one, if_neg (by omega), zero_add]
            exact (ih (m + 1) (by omega) (by omega)).2
        rcases htail with ⟨q, hq⟩
        exact ⟨-q, by linarith⟩
      have hdiv_A : (2 : ℤ) ∣ PowerSeries.coeff r A := by
        have hm := congrArg (PowerSeries.coeff r) hAinv
        rw [PowerSeries.coeff_mul, PowerSeries.coeff_one, if_neg (by omega)] at hm
        rw [← Finset.add_sum_erase _ _ (Finset.mem_antidiagonal.mpr (add_zero r) : (r, 0) ∈ Finset.antidiagonal r)] at hm
        rw [PowerSeries.coeff_zero_eq_constantCoeff, hAinv0, mul_one] at hm
        have htail : (2 : ℤ) ∣ ∑ p ∈ (Finset.antidiagonal r).erase (r, 0),
            PowerSeries.coeff p.1 A * PowerSeries.coeff p.2 (Ring.inverse A) := by
          refine Finset.dvd_sum fun p hp => ?_
          have hmem := Finset.mem_erase.mp hp
          have hsum : p.1 + p.2 = r := Finset.mem_antidiagonal.mp hmem.2
          have hp2_pos : 1 ≤ p.2 := by
            by_contra h0; apply hmem.1; exact Prod.ext (by omega) (by omega)
          by_cases hp2_eq : p.2 = r
          · rw [hp2_eq]; exact dvd_mul_of_dvd_right hdiv_inv _
          · exact dvd_mul_of_dvd_right (ih p.2 (by omega) hp2_pos).2 _
        rcases htail with ⟨q, hq⟩
        exact ⟨-q, by linarith⟩
      exact ⟨hdiv_A, hdiv_inv⟩
  -- Step 2: Write A = 1 + 2 * B and Ring.inverse A = 1 + 2 * B', show φ B' = φ B in ZMod 2
  let B : PowerSeries ℤ := PowerSeries.mk fun k => if k = 0 then 0 else PowerSeries.coeff k A / 2
  let B' : PowerSeries ℤ := PowerSeries.mk fun k => if k = 0 then 0 else PowerSeries.coeff k (Ring.inverse A) / 2
  have hAB : A = 1 + 2 * B := by
    ext k
    rw [map_add, PowerSeries.coeff_one,
        show (2 : PowerSeries ℤ) * B = PowerSeries.C 2 * B by simp,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    cases k with
    | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff, hA0]
    | succ m =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, zero_add]
      exact (Int.mul_ediv_cancel' (heven (m + 1) (by omega)).1).symm
  have hAinvB' : Ring.inverse A = 1 + 2 * B' := by
    ext k
    rw [map_add, PowerSeries.coeff_one,
        show (2 : PowerSeries ℤ) * B' = PowerSeries.C 2 * B' by simp,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    cases k with
    | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff, hAinv0]
    | succ m =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, zero_add]
      exact (Int.mul_ediv_cancel' (heven (m + 1) (by omega)).2).symm
  let φ : PowerSeries ℤ →+* PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2))
  let b : PowerSeries (ZMod 2) := φ B
  have hBB' : φ B' = b := by
    have hmul : (1 + 2 * B) * (1 + 2 * B') = 1 := by rw [← hAB, ← hAinvB']; exact hAinv
    have hlin : 2 * (B + B' + 2 * (B * B')) = 0 := by linear_combination hmul
    have h0 : B + B' + 2 * (B * B') = 0 := by
      ext k
      have hk := congrArg (PowerSeries.coeff k) hlin
      rw [show (2 : PowerSeries ℤ) * (B + B' + 2 * (B * B')) =
          PowerSeries.C 2 * (B + B' + 2 * (B * B')) by simp,
          PowerSeries.coeff_C_mul] at hk
      have hk0 : PowerSeries.coeff k (0 : PowerSeries ℤ) = 0 := map_zero _
      rw [hk0] at hk ⊢
      omega
    have hcast := congrArg φ h0
    rw [map_add, map_add, map_mul, map_ofNat, zmod2_ps_two, zero_mul, add_zero, map_zero] at hcast
    ext k
    have hk := congrArg (PowerSeries.coeff k) hcast
    rw [map_add, map_zero] at hk
    have h2 : ∀ x y : ZMod 2, x + y = 0 → y = x := by decide
    exact h2 _ _ hk
  -- Step 3: Divide hEq by 2 and reduce mod 2 to get (1 + b) * ∏_{m=1}^r (1 + X^(2*m)) = [r=0]
  have hA_mod2 : φ A = 1 := by
    rw [hAB, map_add, map_one, map_mul, map_ofNat, zmod2_ps_two, zero_mul, add_zero]
  have hAinv_mod2 : φ (Ring.inverse A) = 1 := by
    rw [hAinvB', map_add, map_one, map_mul, map_ofNat, zmod2_ps_two, zero_mul, add_zero]
  have hXφ : φ PowerSeries.X = PowerSeries.X := PowerSeries.map_X _
  have hprod_b : ∀ r : ℕ,
      PowerSeries.coeff r ((1 + b) * ∏ m ∈ Finset.Icc 1 r, (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ (2 * m))) =
      if r = 0 then 1 else 0 := by
    intro r
    have h1 := hEq r
    have hIcc : Finset.Icc 1 (r + 1) = insert 1 (Finset.Icc 2 (r + 1)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.prod_insert (by simp)] at h1
    simp only [pow_one, Nat.sub_self, pow_zero, one_mul] at h1
    have h2fac : 1 + Ring.inverse A = 2 * (1 + B') := by rw [hAinvB']; ring
    rw [h2fac] at h1
    have hrearr : (1 + PowerSeries.X * A) * (2 * (1 + B')) *
        (∏ n ∈ Finset.Icc 2 (r + 1),
          (1 + PowerSeries.X ^ n * A) * (1 + PowerSeries.X ^ (n - 1) * Ring.inverse A)) =
        PowerSeries.C 2 * ((1 + B') * (1 + PowerSeries.X * A) *
          (∏ n ∈ Finset.Icc 2 (r + 1),
            (1 + PowerSeries.X ^ n * A) * (1 + PowerSeries.X ^ (n - 1) * Ring.inverse A))) := by
      simp only [map_ofNat]; ring
    rw [hrearr, PowerSeries.coeff_C_mul] at h1
    have hdiv2 : (if r = 0 then (1 : ℤ) else 0) =
        PowerSeries.coeff r ((1 + B') * (1 + PowerSeries.X * A) *
          (∏ n ∈ Finset.Icc 2 (r + 1),
            (1 + PowerSeries.X ^ n * A) * (1 + PowerSeries.X ^ (n - 1) * Ring.inverse A))) := by
      split_ifs at h1 ⊢ <;> omega
    have hcast := congrArg (Int.castRingHom (ZMod 2)) hdiv2
    rw [← PowerSeries.coeff_map] at hcast
    have hmap_lhs : φ ((1 + B') * (1 + PowerSeries.X * A) *
        (∏ n ∈ Finset.Icc 2 (r + 1),
          (1 + PowerSeries.X ^ n * A) * (1 + PowerSeries.X ^ (n - 1) * Ring.inverse A))) =
        (1 + b) * (1 + PowerSeries.X) *
          ∏ n ∈ Finset.Icc 2 (r + 1),
            ((1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ n) * (1 + PowerSeries.X ^ (n - 1))) := by
      simp only [map_mul, map_add, map_one, map_pow, map_prod, hBB', hXφ, hA_mod2, hAinv_mod2, mul_one]
    change (Int.castRingHom (ZMod 2)) (if r = 0 then 1 else 0) = PowerSeries.coeff r (φ _) at hcast
    rw [hmap_lhs] at hcast
    -- Simplify (1 + X) * ∏_{n=2}^{r+1} (1 + X^n) * (1 + X^(n-1)) = (1 + X^(r+1)) * ∏_{m=1}^r (1 + X^(2*m))
    have hsimp : (1 + (PowerSeries.X : PowerSeries (ZMod 2))) *
        (∏ n ∈ Finset.Icc 2 (r + 1),
          ((1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ n) * (1 + PowerSeries.X ^ (n - 1)))) =
        (1 + PowerSeries.X ^ (r + 1)) *
          ∏ m ∈ Finset.Icc 1 r, (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ (2 * m)) := by
      rw [Finset.prod_mul_distrib]
      have hshift : ∏ n ∈ Finset.Icc 2 (r + 1), (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ (n - 1)) =
          ∏ m ∈ Finset.Icc 1 r, (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ m) := by
        refine Finset.prod_bij (fun n _ => n - 1) ?_ ?_ ?_ ?_
        · intro n hn; simp only [Finset.mem_Icc] at hn ⊢; omega
        · intro n1 hn1 n2 hn2 h; simp only [Finset.mem_Icc] at hn1 hn2; omega
        · intro m hm; simp only [Finset.mem_Icc] at hm ⊢; exact ⟨m + 1, by omega, by omega⟩
        · intro n _; rfl
      have htop : (1 + (PowerSeries.X : PowerSeries (ZMod 2))) *
          ∏ n ∈ Finset.Icc 2 (r + 1), (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ n) =
          (1 + PowerSeries.X ^ (r + 1)) *
            ∏ m ∈ Finset.Icc 1 r, (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ m) := by
        cases r with
        | zero => simp
        | succ k =>
          have h1' : Finset.Icc 2 (k + 2) = insert (k + 2) (Finset.Icc 2 (k + 1)) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          have h2' : Finset.Icc 1 (k + 1) = insert 1 (Finset.Icc 2 (k + 1)) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [h1', Finset.prod_insert (by simp), h2', Finset.prod_insert (by simp)]
          simp only [pow_one]; ring
      rw [hshift, ← mul_assoc, htop, mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun m _ => ?_
      rw [← sq, zmod2_ps_add_sq, one_pow, ← pow_mul, mul_comm m 2]
    rw [mul_assoc (1 + b), hsimp] at hcast
    -- Drop the (1 + X^(r+1)) factor at coeff r!
    have hdrop : PowerSeries.coeff r
        ((1 + b) * ((1 + PowerSeries.X ^ (r + 1)) *
          ∏ m ∈ Finset.Icc 1 r, (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ (2 * m)))) =
        PowerSeries.coeff r
          ((1 + b) * ∏ m ∈ Finset.Icc 1 r, (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ (2 * m))) := by
      rw [show (1 + b) * ((1 + PowerSeries.X ^ (r + 1)) *
            ∏ m ∈ Finset.Icc 1 r, (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ (2 * m))) =
          (1 + b) * (∏ m ∈ Finset.Icc 1 r, (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ (2 * m))) +
          PowerSeries.X ^ (r + 1) *
            ((1 + b) * ∏ m ∈ Finset.Icc 1 r, (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ (2 * m))) by ring]
      rw [map_add, PowerSeries.coeff_X_pow_mul', if_neg (by omega), add_zero]
    rw [hdrop] at hcast
    rw [← hcast]
    by_cases hr0 : r = 0
    · rw [if_pos hr0, map_one, if_pos hr0]
    · rw [if_neg hr0, map_zero, if_neg hr0]
  -- Step 4: P_part^2 satisfies the exact same product equation in ZMod 2!
  let Ppart : PowerSeries (ZMod 2) :=
    PowerSeries.mk fun n => (Fintype.card (Nat.Partition n) : ZMod 2)
  have hprod_P2 : ∀ r : ℕ,
      PowerSeries.coeff r (Ppart ^ 2 * ∏ m ∈ Finset.Icc 1 r, (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ (2 * m))) =
      if r = 0 then 1 else 0 := by
    intro r
    have hsq : Ppart ^ 2 * ∏ m ∈ Finset.Icc 1 r, (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ (2 * m)) =
        (Ppart * ∏ m ∈ Finset.Icc 1 r, (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ m)) ^ 2 := by
      rw [mul_pow, ← Finset.prod_pow]
      congr 1
      refine Finset.prod_congr rfl fun m _ => ?_
      rw [zmod2_ps_add_sq, one_pow, ← pow_mul, mul_comm m 2]
    rw [hsq, coeff_sq_zmod2]
    by_cases hr0 : r = 0
    · subst hr0
      rw [if_pos rfl, if_pos (by decide), show (0 : ℕ) / 2 = 0 by rfl,
          partition_prod_cancel_zmod2 0, if_pos rfl]
    · rw [if_neg hr0]
      split_ifs with hev
      · -- coeff (r / 2) of (Ppart * ∏_{m=1}^r (1 + X^m)) = coeff (r / 2) of (Ppart * ∏_{m=1}^{r/2} (1 + X^m)) = 0!
        have hsplit : Finset.Icc 1 r = Finset.Icc 1 (r / 2) ∪ Finset.Icc (r / 2 + 1) r := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega
        have hdisj : Disjoint (Finset.Icc 1 (r / 2)) (Finset.Icc (r / 2 + 1) r) := by
          rw [Finset.disjoint_left]; intro x h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
        rw [hsplit, Finset.prod_union hdisj, ← mul_assoc]
        have hdrop : ∀ (T : Finset ℕ) (g : PowerSeries (ZMod 2)),
            (∀ m ∈ T, r / 2 < m) →
            PowerSeries.coeff (r / 2) (g * ∏ m ∈ T, (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ m)) =
            PowerSeries.coeff (r / 2) g := by
          intro T
          induction T using Finset.cons_induction with
          | empty => intro g _; simp
          | cons a s ha ih =>
            intro g hT
            rw [Finset.prod_cons, ← mul_assoc, ih _ (fun m hm => hT m (Finset.mem_cons_of_mem hm))]
            rw [mul_add, mul_one, map_add, mul_comm g (PowerSeries.X ^ a),
                PowerSeries.coeff_X_pow_mul', if_neg (by have := hT a (Finset.mem_cons_self a s); omega),
                add_zero]
        rw [hdrop _ _ (fun m hm => by have := (Finset.mem_Icc.mp hm).1; omega),
            partition_prod_cancel_zmod2 (r / 2), if_neg (by omega)]
      · rfl
  -- Step 5: By strong induction on r, coeff r (1 + b) = coeff r (Ppart^2) for all r!
  have hb_eq_P2 : ∀ r : ℕ, PowerSeries.coeff r (1 + b) = PowerSeries.coeff r (Ppart ^ 2) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      have h1 := hprod_b r
      have h2 := hprod_P2 r
      set Q := ∏ m ∈ Finset.Icc 1 r, (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ (2 * m))
      have hQ0 : PowerSeries.constantCoeff Q = 1 := by
        dsimp only [Q]; rw [map_prod]
        refine Finset.prod_eq_one fun m hm => ?_
        have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        rw [map_add, map_one, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), add_zero]
      have hdiff : PowerSeries.coeff r ((1 + b - Ppart ^ 2) * Q) = 0 := by
        rw [sub_mul, map_sub, h1, h2, sub_self]
      rw [PowerSeries.coeff_mul, ← Finset.add_sum_erase _ _ (Finset.mem_antidiagonal.mpr (add_zero r) : (r, 0) ∈ Finset.antidiagonal r),
          PowerSeries.coeff_zero_eq_constantCoeff, hQ0, mul_one] at hdiff
      have hrest : ∑ p ∈ (Finset.antidiagonal r).erase (r, 0),
          PowerSeries.coeff p.1 (1 + b - Ppart ^ 2) * PowerSeries.coeff p.2 Q = 0 := by
        refine Finset.sum_eq_zero fun p hp => ?_
        have hmem := Finset.mem_erase.mp hp
        have hsum : p.1 + p.2 = r := Finset.mem_antidiagonal.mp hmem.2
        have hp1_lt : p.1 < r := by
          by_contra hge; apply hmem.1; exact Prod.ext (by omega) (by omega)
        rw [map_sub, ih p.1 hp1_lt, sub_self, zero_mul]
      rw [hrest, add_zero, map_sub] at hdiff
      exact sub_eq_zero.mp hdiff
  -- Step 6: Translate coeff r b to coeff r A % 4!
  have hA_mod4 : ∀ r : ℕ, 1 ≤ r →
      PowerSeries.coeff r A % 4 = if PowerSeries.coeff r (Ppart ^ 2) = 1 then 2 else 0 := by
    intro r hr
    have hcoeff : PowerSeries.coeff r A = 2 * PowerSeries.coeff r B := by
      have h := congrArg (PowerSeries.coeff r) hAB
      rw [map_add, PowerSeries.coeff_one, if_neg (by omega), zero_add,
          show (2 : PowerSeries ℤ) * B = PowerSeries.C 2 * B by simp, PowerSeries.coeff_C_mul] at h
      exact h
    have hb_r : ((PowerSeries.coeff r B : ℤ) : ZMod 2) = PowerSeries.coeff r (Ppart ^ 2) := by
      have h := hb_eq_P2 r
      rw [map_add, PowerSeries.coeff_one, if_neg (by omega), zero_add] at h
      exact h
    rw [hcoeff]
    have hcase : PowerSeries.coeff r (Ppart ^ 2) = 0 ∨ PowerSeries.coeff r (Ppart ^ 2) = 1 := by
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
    rw [hA_mod4 (2 * k) (by omega), coeff_sq_zmod2, if_pos (by omega : (2 * k) % 2 = 0),
        Nat.mul_div_cancel_left k (by omega)]
    simp only [Ppart, PowerSeries.coeff_mk]
    have hiff : ((Fintype.card (Nat.Partition k) : ZMod 2) = 1) ↔
        Odd (Fintype.card (Nat.Partition k)) := by
      constructor
      · intro h
        rcases Nat.even_or_odd (Fintype.card (Nat.Partition k)) with ⟨m, hm⟩ | hodd
        · rw [hm, Nat.cast_add, ← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul] at h
          exact absurd h (by decide)
        · exact hodd
      · rintro ⟨m, hm⟩
        rw [hm, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, show (2 : ZMod 2) = 0 by decide,
            zero_mul, zero_add, Nat.cast_one]
    by_cases hodd : Odd (Fintype.card (Nat.Partition k))
    · rw [if_pos hodd, if_pos (hiff.mpr hodd)]
    · rw [if_neg hodd, if_neg (fun h => hodd (hiff.mp h))]
  · intro k
    rw [hA_mod4 (2 * k + 1) (by omega), coeff_sq_zmod2, if_neg (by omega : ¬ (2 * k + 1) % 2 = 0),
        if_neg (by decide)]

end OMA.P_oeis_a356508

theorem OMA.solution : type_of% @OMA.S_oeis_a356508.main := OMA.P_oeis_a356508.solution
