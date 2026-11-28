import OMAStatements.S_oeis_a305123
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a305123

open OMA.S_oeis_a305123

private lemma zmod2_ps_two : (2 : PowerSeries (ZMod 2)) = 0 := by
  have h : (2 : ZMod 2) = 0 := by decide
  rw [← map_ofNat (PowerSeries.C (R := ZMod 2)), h, map_zero]

private lemma zmod2_ps_add_self (f : PowerSeries (ZMod 2)) : f + f = 0 := by
  rw [← two_mul, zmod2_ps_two, zero_mul]

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
  have hcoeff_eq : ∀ k ≤ r,
      PowerSeries.coeff k (Nat.Partition.genFun (fun _ _ => (1 : ZMod 2))) =
      PowerSeries.coeff k
        (∏ i ∈ Finset.range r,
          ((1 : PowerSeries (ZMod 2)) + ∑' j, (1 : ZMod 2) • PowerSeries.X ^ ((i + 1) * (j + 1)))) := by
    intro k hk
    rw [HasProd, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto] at hprod
    have ht := hprod k
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

private lemma log_deriv_prod_zmod2 (S : Finset ℕ) (hS : ∀ m ∈ S, 1 ≤ m) :
    PowerSeries.X * PowerSeries.derivative (ZMod 2) (∏ m ∈ S, (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ m)) =
      (∏ m ∈ S, (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ m)) *
        ∑ m ∈ S, (m : PowerSeries (ZMod 2)) * PowerSeries.X ^ m *
          Ring.inverse (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ m) := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have ha1 : 1 ≤ a := hS a (Finset.mem_cons_self a s)
    have hs1 : ∀ m ∈ s, 1 ≤ m := fun m hm => hS m (Finset.mem_cons_of_mem hm)
    have hu : IsUnit (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ a) := by
      apply PowerSeries.isUnit_iff_constantCoeff.mpr
      rw [map_add, map_one, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), add_zero]
      exact isUnit_one
    have hinv : (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ a) *
        Ring.inverse (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ a) = 1 :=
      Ring.mul_inverse_cancel _ hu
    have hda : PowerSeries.X * PowerSeries.derivative (ZMod 2) (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ a) =
        (a : PowerSeries (ZMod 2)) * PowerSeries.X ^ a := by
      rw [map_add, PowerSeries.derivative_one, zero_add, Derivation.leibniz_pow,
          PowerSeries.derivative_X, smul_eq_mul, nsmul_eq_mul, mul_one]
      rw [show PowerSeries.X * ((a : PowerSeries (ZMod 2)) * PowerSeries.X ^ (a - 1)) =
          (a : PowerSeries (ZMod 2)) * (PowerSeries.X ^ (a - 1) * PowerSeries.X) by ring,
          ← pow_succ, Nat.sub_add_cancel ha1]
    rw [Finset.prod_cons, Finset.sum_cons, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    set P := ∏ m ∈ s, (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ m)
    set T := ∑ m ∈ s, (m : PowerSeries (ZMod 2)) * PowerSeries.X ^ m *
        Ring.inverse (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ m)
    have hih := ih hs1
    calc PowerSeries.X *
          ((1 + PowerSeries.X ^ a) * PowerSeries.derivative (ZMod 2) P +
            P * PowerSeries.derivative (ZMod 2) (1 + PowerSeries.X ^ a))
        = (PowerSeries.X * PowerSeries.derivative (ZMod 2) (1 + PowerSeries.X ^ a)) * P +
          (1 + PowerSeries.X ^ a) * (PowerSeries.X * PowerSeries.derivative (ZMod 2) P) := by ring
      _ = ((a : PowerSeries (ZMod 2)) * PowerSeries.X ^ a) * P +
          (1 + PowerSeries.X ^ a) * (P * T) := by rw [hda, hih]
      _ = ((1 + PowerSeries.X ^ a) * Ring.inverse (1 + PowerSeries.X ^ a)) *
          ((a : PowerSeries (ZMod 2)) * PowerSeries.X ^ a * P) +
          (1 + PowerSeries.X ^ a) * (P * T) := by rw [hinv, one_mul]
      _ = (1 + PowerSeries.X ^ a) * P *
          ((a : PowerSeries (ZMod 2)) * PowerSeries.X ^ a * Ring.inverse (1 + PowerSeries.X ^ a) + T) := by
          ring

theorem solution : type_of% @OMA.S_oeis_a305123.main := by
  intro A hEq n
  let φ : PowerSeries ℤ →+* PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2))
  let Ppart : PowerSeries (ZMod 2) := PowerSeries.mk fun m => (Fintype.card (Nat.Partition m) : ZMod 2)
  have hXφ : φ PowerSeries.X = PowerSeries.X := PowerSeries.map_X _
  -- Reduce hEq n mod 2: coeff n (φ A) = coeff n ((∑_{k=1}^n X^(2k-1)/(1+X^(2k-1))) * Ppart)
  have hmod2 : (Int.castRingHom (ZMod 2)) (PowerSeries.coeff n A) =
      PowerSeries.coeff n
        ((∑ k ∈ Finset.Icc 1 n,
            (PowerSeries.X : PowerSeries (ZMod 2)) ^ (2 * k - 1) *
              Ring.inverse (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ (2 * k - 1))) * Ppart) := by
    have h := congrArg (Int.castRingHom (ZMod 2)) (hEq n)
    conv_rhs at h => rw [← PowerSeries.coeff_map, map_mul, map_sum]
    have hPmap : φ (PowerSeries.mk fun m => (Fintype.card (Nat.Partition m) : ℤ)) = Ppart := by
      ext m; simp [φ, Ppart, PowerSeries.coeff_map, PowerSeries.coeff_mk]
    have hSmap : ∑ k ∈ Finset.Icc 1 n,
        φ (PowerSeries.X ^ (2 * k - 1) * Ring.inverse (1 + PowerSeries.X ^ (2 * k - 1))) =
        ∑ k ∈ Finset.Icc 1 n,
          (PowerSeries.X : PowerSeries (ZMod 2)) ^ (2 * k - 1) *
            Ring.inverse (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ (2 * k - 1)) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      rw [map_mul, map_pow, hXφ]
      congr 1
      have hu : IsUnit (1 + (PowerSeries.X : PowerSeries ℤ) ^ (2 * k - 1)) := by
        apply PowerSeries.isUnit_iff_constantCoeff.mpr
        rw [map_add, map_one, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), add_zero]
        exact isUnit_one
      have hu2 : IsUnit (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ (2 * k - 1)) := by
        apply PowerSeries.isUnit_iff_constantCoeff.mpr
        rw [map_add, map_one, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), add_zero]
        exact isUnit_one
      have h1 : φ (1 + PowerSeries.X ^ (2 * k - 1)) * φ (Ring.inverse (1 + PowerSeries.X ^ (2 * k - 1))) = 1 := by
        rw [← map_mul, Ring.mul_inverse_cancel _ hu, map_one]
      rw [map_add, map_one, map_pow, hXφ] at h1
      have h2 := congrArg (Ring.inverse (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ (2 * k - 1)) * ·) h1
      rw [← mul_assoc, Ring.inverse_mul_cancel _ hu2, one_mul, mul_one] at h2
      exact h2
    rw [hPmap, hSmap] at h
    exact h
  -- Now prove coeff n ((∑_{k=1}^n X^(2k-1)/(1+X^(2k-1))) * Ppart) = (n : ZMod 2) * coeff n Ppart!
  have hkey : PowerSeries.coeff n
      ((∑ k ∈ Finset.Icc 1 n,
          (PowerSeries.X : PowerSeries (ZMod 2)) ^ (2 * k - 1) *
            Ring.inverse (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ (2 * k - 1))) * Ppart) =
      (n : ZMod 2) * PowerSeries.coeff n Ppart := by
    set Q : PowerSeries (ZMod 2) := ∏ m ∈ Finset.Icc 1 n, (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ m)
    have hQu : IsUnit Q := by
      apply PowerSeries.isUnit_iff_constantCoeff.mpr
      dsimp only [Q]; rw [map_prod]
      rw [Finset.prod_eq_one]
      · exact isUnit_one
      · intro m hm
        have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        rw [map_add, map_one, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), add_zero]
    have hQinv : Q * Ring.inverse Q = 1 := Ring.mul_inverse_cancel Q hQu
    -- Step A: Ppart agrees with Ring.inverse Q on all degrees ≤ n!
    have hPQ_cancel : ∀ k ≤ n, PowerSeries.coeff k (Ppart * Q) = if k = 0 then 1 else 0 := by
      intro k hk
      have hsplit : Finset.Icc 1 n = Finset.Icc 1 k ∪ Finset.Icc (k + 1) n := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      have hdisj : Disjoint (Finset.Icc 1 k) (Finset.Icc (k + 1) n) := by
        rw [Finset.disjoint_left]; intro x h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
      dsimp only [Q]
      rw [hsplit, Finset.prod_union hdisj, ← mul_assoc]
      have hdrop : ∀ (T : Finset ℕ) (g : PowerSeries (ZMod 2)),
          (∀ m ∈ T, k < m) →
          PowerSeries.coeff k (g * ∏ m ∈ T, (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ m)) =
          PowerSeries.coeff k g := by
        intro T
        induction T using Finset.cons_induction with
        | empty => intro g _; simp
        | cons a s ha ih =>
          intro g hT
          rw [Finset.prod_cons, ← mul_assoc, ih _ (fun m hm => hT m (Finset.mem_cons_of_mem hm))]
          rw [mul_add, mul_one, map_add, mul_comm g (PowerSeries.X ^ a),
              PowerSeries.coeff_X_pow_mul', if_neg (by have := hT a (Finset.mem_cons_self a s); omega),
              add_zero]
      rw [hdrop _ _ (fun m hm => by have := (Finset.mem_Icc.mp hm).1; omega)]
      exact partition_prod_cancel_zmod2 k
    have hP_eq_invQ : ∀ k ≤ n, PowerSeries.coeff k Ppart = PowerSeries.coeff k (Ring.inverse Q) := by
      intro k hk
      have h1 : PowerSeries.coeff k (Ppart * (Q * Ring.inverse Q)) = PowerSeries.coeff k (Ring.inverse Q) := by
        rw [← mul_assoc, PowerSeries.coeff_mul, Finset.sum_eq_single (0, k)]
        · rw [hPQ_cancel 0 (Nat.zero_le n), if_pos rfl, one_mul]
        · intro p hp hne
          have hsum : p.1 + p.2 = k := Finset.mem_antidiagonal.mp hp
          have hp1 : p.1 ≠ 0 := by intro h0; apply hne; exact Prod.ext h0 (by omega)
          rw [hPQ_cancel p.1 (by omega), if_neg hp1, zero_mul]
        · intro h; exact absurd (Finset.mem_antidiagonal.mpr (zero_add k)) h
      rw [hQinv, mul_one] at h1
      exact h1
    -- Step B: Differentiate Q * Ring.inverse Q = 1 and multiply by X * Ring.inverse Q!
    have hderiv_invQ :
        PowerSeries.X * PowerSeries.derivative (ZMod 2) (Ring.inverse Q) =
          Ring.inverse Q *
            ∑ m ∈ Finset.Icc 1 n, (m : PowerSeries (ZMod 2)) * PowerSeries.X ^ m *
              Ring.inverse (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ m) := by
      have hd := congrArg (PowerSeries.derivative (ZMod 2)) hQinv
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, PowerSeries.derivative_one] at hd
      have h1 := congrArg (PowerSeries.X * Ring.inverse Q * ·) hd
      rw [mul_zero] at h1
      have hld := log_deriv_prod_zmod2 (Finset.Icc 1 n) (fun m hm => (Finset.mem_Icc.mp hm).1)
      set S := ∑ m ∈ Finset.Icc 1 n, (m : PowerSeries (ZMod 2)) * PowerSeries.X ^ m *
          Ring.inverse (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ m)
      have h2 : PowerSeries.X * Ring.inverse Q *
          (Q * PowerSeries.derivative (ZMod 2) (Ring.inverse Q) +
            Ring.inverse Q * PowerSeries.derivative (ZMod 2) Q) =
          (Ring.inverse Q * Ring.inverse Q) * (PowerSeries.X * PowerSeries.derivative (ZMod 2) Q) +
          (Q * Ring.inverse Q) * (PowerSeries.X * PowerSeries.derivative (ZMod 2) (Ring.inverse Q)) := by ring
      rw [h2, hld, hQinv, one_mul] at h1
      have h3 : (Ring.inverse Q * Ring.inverse Q) * (Q * S) = Ring.inverse Q * S := by
        calc (Ring.inverse Q * Ring.inverse Q) * (Q * S)
            = (Q * Ring.inverse Q) * (Ring.inverse Q * S) := by ring
          _ = Ring.inverse Q * S := by rw [hQinv, one_mul]
      rw [h3] at h1
      -- Ring.inverse Q * S + X * derivative (Ring.inverse Q) = 0 in ZMod 2 => equal!
      calc PowerSeries.X * PowerSeries.derivative (ZMod 2) (Ring.inverse Q)
          = (Ring.inverse Q * S + PowerSeries.X * PowerSeries.derivative (ZMod 2) (Ring.inverse Q)) +
            Ring.inverse Q * S := by
            rw [add_comm (Ring.inverse Q * S), add_assoc, zmod2_ps_add_self, add_zero]
        _ = 0 + Ring.inverse Q * S := by rw [h1]
        _ = Ring.inverse Q * S := zero_add _
    -- Step C: Compare coeff n of both sides!
    have hcoeff_deriv : PowerSeries.coeff n (PowerSeries.X * PowerSeries.derivative (ZMod 2) (Ring.inverse Q)) =
        (n : ZMod 2) * PowerSeries.coeff n Ppart := by
      cases n with
      | zero =>
        simp [PowerSeries.coeff_zero_X_mul]
      | succ m =>
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, ← hP_eq_invQ (m + 1) le_rfl]
        push_cast; ring
    rw [← hcoeff_deriv, hderiv_invQ, mul_comm (Ring.inverse Q)]
    -- Replace Ring.inverse Q by Ppart in coeff n (S * Ring.inverse Q), and match sums!
    have hsum_eq :
        PowerSeries.coeff n
          ((∑ m ∈ Finset.Icc 1 n, (m : PowerSeries (ZMod 2)) * PowerSeries.X ^ m *
              Ring.inverse (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ m)) * Ring.inverse Q) =
        PowerSeries.coeff n
          ((∑ k ∈ Finset.Icc 1 n, (PowerSeries.X : PowerSeries (ZMod 2)) ^ (2 * k - 1) *
              Ring.inverse (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ (2 * k - 1))) * Ppart) := by
      have hreplace_P : ∀ F : PowerSeries (ZMod 2),
          PowerSeries.coeff n (F * Ring.inverse Q) = PowerSeries.coeff n (F * Ppart) := by
        intro F
        rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
        refine Finset.sum_congr rfl fun p hp => ?_
        have hp2 : p.2 ≤ n := by have := Finset.mem_antidiagonal.mp hp; omega
        rw [hP_eq_invQ p.2 hp2]
      rw [hreplace_P]
      rw [Finset.sum_mul, Finset.sum_mul, map_sum, map_sum]
      -- In the first sum, even m vanish; in the second sum, 2*k - 1 > n vanishes!
      have h1 : ∑ m ∈ Finset.Icc 1 n,
          PowerSeries.coeff n
            (((m : PowerSeries (ZMod 2)) * PowerSeries.X ^ m *
              Ring.inverse (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ m)) * Ppart) =
          ∑ m ∈ (Finset.Icc 1 n).filter (fun m => m % 2 = 1),
            PowerSeries.coeff n
              ((PowerSeries.X ^ m *
                Ring.inverse (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ m)) * Ppart) := by
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 n) (fun m => m % 2 = 1)]
        have heven_zero : ∑ m ∈ (Finset.Icc 1 n).filter (fun m => ¬ m % 2 = 1),
            PowerSeries.coeff n
              (((m : PowerSeries (ZMod 2)) * PowerSeries.X ^ m *
                Ring.inverse (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ m)) * Ppart) = 0 := by
          refine Finset.sum_eq_zero fun m hm => ?_
          have hpar : m % 2 = 0 := by have := (Finset.mem_filter.mp hm).2; omega
          have hm0 : (m : PowerSeries (ZMod 2)) = 0 := by
            rcases Nat.even_iff.mpr hpar with ⟨j, rfl⟩
            rw [Nat.cast_add, ← two_mul, zmod2_ps_two, zero_mul]
          rw [hm0, zero_mul, zero_mul, zero_mul, map_zero]
        rw [heven_zero, add_zero]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hpar : m % 2 = 1 := (Finset.mem_filter.mp hm).2
        have hm1 : (m : PowerSeries (ZMod 2)) = 1 := by
          have : ∃ j, m = 2 * j + 1 := ⟨m / 2, by omega⟩
          rcases this with ⟨j, rfl⟩
          rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, zmod2_ps_two, zero_mul, zero_add, Nat.cast_one]
        rw [hm1, one_mul]
      have h2 : ∑ k ∈ Finset.Icc 1 n,
          PowerSeries.coeff n
            (((PowerSeries.X : PowerSeries (ZMod 2)) ^ (2 * k - 1) *
              Ring.inverse (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ (2 * k - 1))) * Ppart) =
          ∑ k ∈ (Finset.Icc 1 n).filter (fun k => 2 * k - 1 ≤ n),
            PowerSeries.coeff n
              (((PowerSeries.X : PowerSeries (ZMod 2)) ^ (2 * k - 1) *
                Ring.inverse (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ (2 * k - 1))) * Ppart) := by
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 n) (fun k => 2 * k - 1 ≤ n)]
        have hbig_zero : ∑ k ∈ (Finset.Icc 1 n).filter (fun k => ¬ 2 * k - 1 ≤ n),
            PowerSeries.coeff n
              (((PowerSeries.X : PowerSeries (ZMod 2)) ^ (2 * k - 1) *
                Ring.inverse (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ (2 * k - 1))) * Ppart) = 0 := by
          refine Finset.sum_eq_zero fun k hk => ?_
          have hgt : n < 2 * k - 1 := by have := (Finset.mem_filter.mp hk).2; omega
          rw [mul_assoc, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
        rw [hbig_zero, add_zero]
      rw [h1, h2]
      refine Finset.sum_bij (fun m _ => (m + 1) / 2) ?_ ?_ ?_ ?_
      · intro m hm; simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢; omega
      · intro m1 hm1 m2 hm2 h; simp only [Finset.mem_filter, Finset.mem_Icc] at hm1 hm2; omega
      · intro k hk; simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
        exact ⟨2 * k - 1, ⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩
      · intro m hm; simp only [Finset.mem_filter, Finset.mem_Icc] at hm
        rw [show 2 * ((m + 1) / 2) - 1 = m by omega]
    exact hsum_eq.symm
  -- Combine hmod2 and hkey
  have hfin : (Int.castRingHom (ZMod 2)) (PowerSeries.coeff n A) =
      (n : ZMod 2) * (Fintype.card (Nat.Partition n) : ZMod 2) := by
    rw [hmod2, hkey]; simp [Ppart, PowerSeries.coeff_mk]
  have hodd_iff_int : ∀ z : ℤ, Odd z ↔ (Int.castRingHom (ZMod 2)) z = 1 := by
    intro z
    constructor
    · rintro ⟨m, rfl⟩
      rw [map_add, map_mul, map_ofNat, map_one, show (2 : ZMod 2) = 0 by decide, zero_mul, zero_add]
    · intro h
      rcases Int.even_or_odd z with ⟨m, rfl⟩ | hodd
      · rw [map_add, ← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul] at h
        exact absurd h (by decide)
      · exact hodd
  have hodd_iff_nat : ∀ k : ℕ, Odd k ↔ (k : ZMod 2) = 1 := by
    intro k
    constructor
    · rintro ⟨m, rfl⟩
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, show (2 : ZMod 2) = 0 by decide,
          zero_mul, zero_add, Nat.cast_one]
    · intro h
      rcases Nat.even_or_odd k with ⟨m, rfl⟩ | hodd
      · rw [Nat.cast_add, ← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul] at h
        exact absurd h (by decide)
      · exact hodd
  rw [hodd_iff_int, hodd_iff_nat, hodd_iff_nat, hfin]
  have h2 : ∀ x y : ZMod 2, x * y = 1 ↔ x = 1 ∧ y = 1 := by decide
  exact h2 _ _

end OMA.P_oeis_a305123

theorem OMA.solution : type_of% @OMA.S_oeis_a305123.main := OMA.P_oeis_a305123.solution
