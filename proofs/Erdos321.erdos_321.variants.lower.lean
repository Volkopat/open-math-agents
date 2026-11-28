import FormalConjectures.ErdosProblems.«321»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Lower bound for Erdős Problem 321 (`Erdos321.erdos_321.variants.lower`)

We formalize the Bleicher–Erdős prime-chain lower bound for `R N`, together with the
small-`N` / non-positive iterated-logarithm edge case arising from `Real.log` on `ℝ`.
-/

open scoped Finset Nat Nat.Prime
open Finset Real

namespace Erdos321LowerProof

/- Section 1: PrimeChain construction with base set `A0 = {1, 2, 3, 4}` -/

/-- The base set `{1, 2, 3, 4}` with harmonic sum `25 / 12` and `lcm = 12`. -/
def A0 : Finset ℕ := {1, 2, 3, 4}

lemma card_le_R {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N)
    (hinj : Set.InjOn (fun (S : Finset ℕ) ↦ ∑ n ∈ S, (1 : ℚ) / n) A.powerset) :
    #A ≤ Erdos321.R N := by
  unfold Erdos321.R
  refine le_csSup ⟨N, ?_⟩ ⟨A, hA, hinj, rfl⟩
  rintro _ ⟨B, hB, _, rfl⟩
  exact (Finset.card_le_card hB).trans (by simp)

lemma A0_dvd_twelve {a : ℕ} (ha : a ∈ A0) : a ∣ 12 := by
  simp only [A0, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> decide

lemma A0_le_four {a : ℕ} (ha : a ∈ A0) : a ≤ 4 := by
  simp only [A0, Finset.mem_insert, Finset.mem_singleton] at ha
  omega

lemma A0_injOn :
    Set.InjOn (fun (S : Finset ℕ) ↦ ∑ n ∈ S, (1 : ℚ) / n) A0.powerset := by
  have hnat : ∀ S ∈ A0.powerset, ∀ T ∈ A0.powerset,
      (∑ n ∈ S, (12 / n : ℕ)) = (∑ n ∈ T, (12 / n : ℕ)) → S = T := by
    decide
  have hmul : ∀ S ⊆ A0, (12 : ℚ) * ∑ n ∈ S, (1 : ℚ) / n =
      ((∑ n ∈ S, (12 / n : ℕ) : ℕ) : ℚ) := by
    intro S hS
    rw [Finset.mul_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnA : n ∈ A0 := hS hn
    have hndvd : n ∣ 12 := A0_dvd_twelve hnA
    have hn0 : (n : ℚ) ≠ 0 := by
      simp only [A0, Finset.mem_insert, Finset.mem_singleton] at hnA
      rcases hnA with rfl | rfl | rfl | rfl <;> norm_num
    field_simp [hn0]
    exact_mod_cast (Nat.mul_div_cancel' hndvd).symm
  intro S hS T hT hEq
  dsimp only at hEq
  apply hnat S hS T hT
  have hq : ((∑ n ∈ S, (12 / n : ℕ) : ℕ) : ℚ) = ((∑ n ∈ T, (12 / n : ℕ) : ℕ) : ℚ) := by
    rw [← hmul S (Finset.mem_powerset.mp hS), ← hmul T (Finset.mem_powerset.mp hT), hEq]
  exact_mod_cast hq

/-- Threshold `T q = 25 * ∏_{25 < r ≤ q, r prime} (r + 1)`. -/
def chainThresh (q : ℕ) : ℕ :=
  25 * ∏ r ∈ (Finset.Ioc 25 q).filter Nat.Prime, (r + 1)

lemma chainThresh_pos (q : ℕ) : 0 < chainThresh q := by
  unfold chainThresh
  positivity

lemma chainThresh_mono {q₁ q₂ : ℕ} (h : q₁ ≤ q₂) : chainThresh q₁ ≤ chainThresh q₂ := by
  unfold chainThresh
  gcongr
  exact fun r _ _ => Nat.succ_le_succ (Nat.zero_le r)

lemma prod_primesLE_add_one_le_six_pow (q : ℕ) :
    ∏ r ∈ Nat.primesLE q, (r + 1) ≤ 6 ^ q := by
  have hcard : #(Nat.primesLE q) ≤ q := by
    calc #(Nat.primesLE q)
        ≤ #(Finset.Icc 1 q) := Finset.card_le_card (fun p hp => by
          rw [Nat.mem_primesLE] at hp
          exact Finset.mem_Icc.mpr ⟨hp.2.one_le, hp.1⟩)
      _ = q := by simp
  have h1 : 2 ^ #(Nat.primesLE q) * ∏ r ∈ Nat.primesLE q, (r + 1) ≤
      3 ^ #(Nat.primesLE q) * primorial q := by
    rw [primorial_eq_prod_primesLE, ← Finset.prod_const, ← Finset.prod_const,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod' fun p hp => ?_
    have hp2 : 2 ≤ p := Nat.two_le_of_mem_primesLE hp
    omega
  have h2 : 2 ^ q * ∏ r ∈ Nat.primesLE q, (r + 1) ≤ 2 ^ q * 6 ^ q := by
    have hmul : 2 ^ (q - #(Nat.primesLE q)) *
        (2 ^ #(Nat.primesLE q) * ∏ r ∈ Nat.primesLE q, (r + 1)) ≤
        2 ^ (q - #(Nat.primesLE q)) * (3 ^ #(Nat.primesLE q) * primorial q) :=
      Nat.mul_le_mul_left _ h1
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hcard] at hmul
    refine hmul.trans ?_
    calc 2 ^ (q - #(Nat.primesLE q)) * (3 ^ #(Nat.primesLE q) * primorial q)
        ≤ 3 ^ (q - #(Nat.primesLE q)) * (3 ^ #(Nat.primesLE q) * 4 ^ q) := by
          gcongr
          · norm_num
          · exact primorial_le_four_pow q
      _ = 3 ^ q * 4 ^ q := by
          rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hcard]
      _ = 2 ^ q * 6 ^ q := by
          rw [← mul_pow, ← mul_pow]; norm_num
  exact Nat.le_of_mul_le_mul_left h2 (by positivity)

lemma chainThresh_lt_six_pow {q : ℕ} (hq : 2 ≤ q) : chainThresh q < 6 ^ q := by
  by_cases hq25 : q ≤ 25
  · have hemp : (Finset.Ioc 25 q).filter Nat.Prime = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro r hr
      simp only [Finset.mem_Ioc] at hr
      omega
    rw [chainThresh, hemp, Finset.prod_empty, mul_one]
    calc 25 < 6 ^ 2 := by norm_num
      _ ≤ 6 ^ q := Nat.pow_le_pow_right (by norm_num) hq
  · push Not at hq25
    have hsub : {2, 3, 5} ⊆ Nat.primesLE 25 := by decide
    have h25 : 25 < ∏ r ∈ Nat.primesLE 25, (r + 1) := by
      calc 25 < ∏ r ∈ ({2, 3, 5} : Finset ℕ), (r + 1) := by decide
        _ ≤ ∏ r ∈ Nat.primesLE 25, (r + 1) :=
          Finset.prod_le_prod_of_subset_of_one_le' hsub (fun r _ _ => by omega)
    have hsplit : Nat.primesLE q = Nat.primesLE 25 ∪ (Finset.Ioc 25 q).filter Nat.Prime := by
      ext r
      simp only [Nat.mem_primesLE, Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc]
      by_cases hr : r.Prime
      · simp only [hr, and_true]; omega
      · simp [hr]
    have hdisj : Disjoint (Nat.primesLE 25) ((Finset.Ioc 25 q).filter Nat.Prime) := by
      rw [Finset.disjoint_left]
      intro r hr1 hr2
      rw [Nat.mem_primesLE] at hr1
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hr2
      omega
    have hpos : 0 < ∏ r ∈ (Finset.Ioc 25 q).filter Nat.Prime, (r + 1) := by positivity
    calc chainThresh q
        = 25 * ∏ r ∈ (Finset.Ioc 25 q).filter Nat.Prime, (r + 1) := rfl
      _ < (∏ r ∈ Nat.primesLE 25, (r + 1)) * ∏ r ∈ (Finset.Ioc 25 q).filter Nat.Prime, (r + 1) :=
          Nat.mul_lt_mul_of_pos_right h25 hpos
      _ = ∏ r ∈ Nat.primesLE q, (r + 1) := by
          rw [hsplit, Finset.prod_union hdisj]
      _ ≤ 6 ^ q := prod_primesLE_add_one_le_six_pow q

/-- A finite set of primes `> 25` forming a Bleicher-Erdos prime chain above `A0`. -/
def IsPrimeChain (S : Finset ℕ) : Prop :=
  (∀ p ∈ S, p.Prime ∧ 25 < p) ∧ (∀ q ∈ S, ∀ p ∈ S, q < p → chainThresh q < p)

instance instDecidablePredIsPrimeChain : DecidablePred IsPrimeChain := fun S =>
  inferInstanceAs (Decidable ((∀ p ∈ S, p.Prime ∧ 25 < p) ∧
    (∀ q ∈ S, ∀ p ∈ S, q < p → chainThresh q < p)))

lemma isPrimeChain_empty : IsPrimeChain ∅ := by
  refine ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩

lemma isPrimeChain_subset {S T : Finset ℕ} (hT : IsPrimeChain T) (hST : S ⊆ T) :
    IsPrimeChain S :=
  ⟨fun p hp => hT.1 p (hST hp), fun q hq p hp hqp => hT.2 q (hST hq) p (hST hp) hqp⟩

/-- Elements of our construction: `a * ∏ p ∈ S, p` with `a ∈ A0` and `IsPrimeChain S`. -/
def IsValidElem (n : ℕ) : Prop :=
  ∃ a ∈ A0, ∃ S : Finset ℕ, IsPrimeChain S ∧ n = a * ∏ p ∈ S, p

lemma isValidElem_pos {n : ℕ} (hn : IsValidElem n) : 0 < n := by
  obtain ⟨a, ha, S, hS, rfl⟩ := hn
  have ha0 : 0 < a := by
    simp only [A0, Finset.mem_insert, Finset.mem_singleton] at ha
    omega
  have hS0 : 0 < ∏ p ∈ S, p := Finset.prod_pos fun p hp => (hS.1 p hp).1.pos
  exact Nat.mul_pos ha0 hS0

lemma prime_dvd_validElem_mem {a p : ℕ} {S : Finset ℕ} (ha : a ∈ A0)
    (hS : IsPrimeChain S) (hp : p.Prime) (hp25 : 25 < p) (hdvd : p ∣ a * ∏ r ∈ S, r) :
    p ∈ S := by
  rcases hp.dvd_mul.mp hdvd with hpa | hpS
  · have ha0 : 0 < a := by
      simp only [A0, Finset.mem_insert, Finset.mem_singleton] at ha; omega
    have hle := Nat.le_of_dvd ha0 hpa
    have := A0_le_four ha
    omega
  · rw [hp.prime.dvd_finsetProd_iff] at hpS
    obtain ⟨r, hrS, hpr⟩ := hpS
    have hr := (hS.1 r hrS).1
    have := (Nat.prime_dvd_prime_iff_eq hp hr).mp hpr
    rwa [this]

lemma sum_powerset_sdiff_prod (Q : Finset ℕ) :
    ∑ U ∈ Q.powerset, ∏ r ∈ Q \ U, r = ∏ r ∈ Q, (r + 1) := by
  have hbij : ∑ U ∈ Q.powerset, ∏ r ∈ Q \ U, r = ∑ V ∈ Q.powerset, ∏ r ∈ V, r := by
    refine Finset.sum_nbij (fun U => Q \ U) ?_ ?_ ?_ ?_
    · intro U _
      exact Finset.mem_powerset.mpr Finset.sdiff_subset
    · intro U₁ hU₁ U₂ hU₂ hEq
      have h1 := Finset.mem_powerset.mp hU₁
      have h2 := Finset.mem_powerset.mp hU₂
      have := congrArg (fun W => Q \ W) hEq
      simpa [Finset.sdiff_sdiff_eq_self h1, Finset.sdiff_sdiff_eq_self h2] using this
    · intro V hV
      refine ⟨Q \ V, Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
      exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hV)
    · intro U _
      rfl
  rw [hbij]
  simpa [add_comm] using (Finset.prod_add_one (f := fun r : ℕ => r) Q).symm

private lemma primeChain_disjoint_eq_empty :
    ∀ N_max : ℕ, ∀ X Y : Finset ℕ,
      (∀ n ∈ X, IsValidElem n) →
      (∀ n ∈ Y, IsValidElem n) →
      Disjoint X Y →
      (∀ n ∈ X ∪ Y, n ≤ N_max) →
      (∑ n ∈ X, (1 : ℚ) / n = ∑ n ∈ Y, (1 : ℚ) / n) →
      X = ∅ ∧ Y = ∅ := by
  intro N_max
  induction N_max using Nat.strong_induction_on with
  | h N_max ih =>
    intro X Y hX hY hdisj hle hsum
    by_contra hne
    have hXY_ne : (X ∪ Y).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      apply hne
      rw [Finset.union_eq_empty] at hemp
      exact hemp
    have hXY_valid : ∀ n ∈ X ∪ Y, IsValidElem n := fun n hn =>
      (Finset.mem_union.mp hn).elim (hX n) (hY n)
    let Pset : Finset ℕ := ((X ∪ Y).biUnion Nat.primeFactors).filter (25 < ·)
    by_cases hP : Pset.Nonempty
    · let p := Pset.max' hP
      have hp_mem : p ∈ Pset := Finset.max'_mem Pset hP
      have hp_25 : 25 < p := (Finset.mem_filter.mp hp_mem).2
      have hp_bi : p ∈ (X ∪ Y).biUnion Nat.primeFactors := (Finset.mem_filter.mp hp_mem).1
      obtain ⟨n₀, hn₀, hp_n₀⟩ := Finset.mem_biUnion.mp hp_bi
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_n₀
      have hp_dvd_n₀ : p ∣ n₀ := Nat.dvd_of_mem_primeFactors hp_n₀
      have hp_max : ∀ n ∈ X ∪ Y, ∀ q ∈ n.primeFactors, q ≤ p := by
        intro n hn q hq
        by_cases hq25 : 25 < q
        · exact Finset.le_max' Pset q (Finset.mem_filter.mpr
            ⟨Finset.mem_biUnion.mpr ⟨n, hn, hq⟩, hq25⟩)
        · omega
      let Xp := X.filter (p ∣ ·)
      let Xnp := X.filter (¬ p ∣ ·)
      let Yp := Y.filter (p ∣ ·)
      let Ynp := Y.filter (¬ p ∣ ·)
      let BX := Xp.image (· / p)
      let BY := Yp.image (· / p)
      have hBX_inj : Set.InjOn (· / p) (Xp : Set ℕ) := by
        intro x hx y hy hxy
        dsimp only at hxy
        have hpx : p ∣ x := (Finset.mem_filter.mp hx).2
        have hpy : p ∣ y := (Finset.mem_filter.mp hy).2
        rw [← Nat.mul_div_cancel' hpx, ← Nat.mul_div_cancel' hpy, hxy]
      have hBY_inj : Set.InjOn (· / p) (Yp : Set ℕ) := by
        intro x hx y hy hxy
        dsimp only at hxy
        have hpx : p ∣ x := (Finset.mem_filter.mp hx).2
        have hpy : p ∣ y := (Finset.mem_filter.mp hy).2
        rw [← Nat.mul_div_cancel' hpx, ← Nat.mul_div_cancel' hpy, hxy]
      have hB_disj : Disjoint BX BY := by
        rw [Finset.disjoint_left]
        intro b hbX hbY
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hbX
        obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hbY
        have hpx : p ∣ x := (Finset.mem_filter.mp hx).2
        have hpy : p ∣ y := (Finset.mem_filter.mp hy).2
        have heq : x = y := by
          rw [← Nat.mul_div_cancel' hpx, ← Nat.mul_div_cancel' hpy, hxy]
        exact Finset.disjoint_left.mp hdisj (Finset.mem_filter.mp hx).1
          (heq ▸ (Finset.mem_filter.mp hy).1)
      have hB_ne : (BX ∪ BY).Nonempty := by
        rcases Finset.mem_union.mp hn₀ with h0 | h0
        · exact ⟨n₀ / p, Finset.mem_union_left _ (Finset.mem_image.mpr
            ⟨n₀, Finset.mem_filter.mpr ⟨h0, hp_dvd_n₀⟩, rfl⟩)⟩
        · exact ⟨n₀ / p, Finset.mem_union_right _ (Finset.mem_image.mpr
            ⟨n₀, Finset.mem_filter.mpr ⟨h0, hp_dvd_n₀⟩, rfl⟩)⟩
      let Q : Finset ℕ := (Finset.Ioo 25 p).filter (fun r => r.Prime ∧ chainThresh r < p)
      have hB_struct : ∀ b ∈ BX ∪ BY, ∃ a ∈ A0, ∃ U ⊆ Q,
          IsPrimeChain U ∧ b = a * ∏ r ∈ U, r := by
        intro b hb
        have hpb : p * b ∈ X ∪ Y ∧ p ∣ p * b := by
          rcases Finset.mem_union.mp hb with hbX | hbY
          · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hbX
            have hpx := (Finset.mem_filter.mp hx).2
            rw [Nat.mul_div_cancel' hpx]
            exact ⟨Finset.mem_union_left _ (Finset.mem_filter.mp hx).1, hpx⟩
          · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hbY
            have hpy := (Finset.mem_filter.mp hy).2
            rw [Nat.mul_div_cancel' hpy]
            exact ⟨Finset.mem_union_right _ (Finset.mem_filter.mp hy).1, hpy⟩
        obtain ⟨a, ha, S, hS, hEq⟩ := hXY_valid (p * b) hpb.1
        have hpS : p ∈ S := prime_dvd_validElem_mem ha hS hp_prime hp_25 (hEq ▸ hpb.2)
        let U := S.erase p
        have hU_chain : IsPrimeChain U := isPrimeChain_subset hS (Finset.erase_subset p S)
        have hU_sub : U ⊆ Q := by
          intro r hr
          have hrS : r ∈ S := Finset.mem_of_mem_erase hr
          have hrne : r ≠ p := Finset.ne_of_mem_erase hr
          have hrp : r.Prime := (hS.1 r hrS).1
          have hr25 : 25 < r := (hS.1 r hrS).2
          have hrdvd : r ∣ p * b := by
            rw [hEq]
            exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hrS) a
          have hrle : r ≤ p := hp_max (p * b) hpb.1 r
            (Nat.mem_primeFactors.mpr ⟨hrp, hrdvd, (isValidElem_pos (hXY_valid _ hpb.1)).ne'⟩)
          have hrlt : r < p := lt_of_le_of_ne hrle hrne
          exact Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨hr25, hrlt⟩, hrp, hS.2 r hrS p hpS hrlt⟩
        have hb_eq : b = a * ∏ r ∈ U, r := by
          have hprod : ∏ r ∈ S, r = p * ∏ r ∈ U, r := (Finset.mul_prod_erase S id hpS).symm
          rw [hprod] at hEq
          have hEq' : p * b = p * (a * ∏ r ∈ U, r) := by linarith
          exact Nat.eq_of_mul_eq_mul_left hp_prime.pos hEq'
        exact ⟨a, ha, U, hU_sub, hU_chain, hb_eq⟩
      have hBX_valid : ∀ b ∈ BX, IsValidElem b := fun b hb => by
        obtain ⟨a, ha, U, _, hU, rfl⟩ := hB_struct b (Finset.mem_union_left _ hb)
        exact ⟨a, ha, U, hU, rfl⟩
      have hBY_valid : ∀ b ∈ BY, IsValidElem b := fun b hb => by
        obtain ⟨a, ha, U, _, hU, rfl⟩ := hB_struct b (Finset.mem_union_right _ hb)
        exact ⟨a, ha, U, hU, rfl⟩
      have hN_pos : 0 < N_max := by
        have := isValidElem_pos (hXY_valid n₀ hn₀)
        have := hle n₀ hn₀
        omega
      have hB_le : ∀ b ∈ BX ∪ BY, b ≤ N_max - 1 := by
        intro b hb
        have hpb : p * b ∈ X ∪ Y := by
          rcases Finset.mem_union.mp hb with hbX | hbY
          · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hbX
            rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hx).2]
            exact Finset.mem_union_left _ (Finset.mem_filter.mp hx).1
          · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hbY
            rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hy).2]
            exact Finset.mem_union_right _ (Finset.mem_filter.mp hy).1
        have h1 : p * b ≤ N_max := hle _ hpb
        have hb0 : 0 < b := by
          have := isValidElem_pos (hXY_valid _ hpb)
          exact Nat.pos_of_mul_pos_left this
        have : b < p * b := lt_mul_of_one_lt_left hb0 hp_prime.one_lt
        omega
      let L : ℕ := 12 * ∏ r ∈ Q, r
      let M : ℕ := ∏ n ∈ (Xnp ∪ Ynp), n
      have hL_pos : 0 < L :=
        Nat.mul_pos (by norm_num) (Finset.prod_pos fun r hr => (Finset.mem_filter.mp hr).2.1.pos)
      have hM_pos : 0 < M := Finset.prod_pos fun n hn => by
        have hmem : n ∈ X ∪ Y := by
          rcases Finset.mem_union.mp hn with h1 | h1
          · exact Finset.mem_union_left _ (Finset.mem_filter.mp h1).1
          · exact Finset.mem_union_right _ (Finset.mem_filter.mp h1).1
        exact isValidElem_pos (hXY_valid n hmem)
      have hp_ndvd_M : ¬ p ∣ M := by
        intro hdiv
        rw [hp_prime.prime.dvd_finsetProd_iff] at hdiv
        obtain ⟨n, hn, hpn⟩ := hdiv
        rcases Finset.mem_union.mp hn with h1 | h1
        · exact (Finset.mem_filter.mp h1).2 hpn
        · exact (Finset.mem_filter.mp h1).2 hpn
      have hb_dvd_L : ∀ b ∈ BX ∪ BY, b ∣ L := by
        intro b hb
        obtain ⟨a, ha, U, hU, _, rfl⟩ := hB_struct b hb
        exact mul_dvd_mul (A0_dvd_twelve ha) (Finset.prod_dvd_prod_of_subset _ _ _ hU)
      -- Clear denominators to obtain M * K = p * R_int in ℤ
      let K : ℤ := ∑ b ∈ BX, ((L / b : ℕ) : ℤ) - ∑ b ∈ BY, ((L / b : ℕ) : ℤ)
      let Rint : ℤ := ∑ y ∈ Ynp, ((L * (M / y) : ℕ) : ℤ) - ∑ x ∈ Xnp, ((L * (M / x) : ℕ) : ℤ)
      have h_mul_eq : (M : ℤ) * K = (p : ℤ) * Rint := by
        have hXsplit : ∑ x ∈ X, (1 : ℚ) / x =
            ∑ x ∈ Xp, (1 : ℚ) / x + ∑ x ∈ Xnp, (1 : ℚ) / x := by
          exact (Finset.sum_filter_add_sum_filter_not X (p ∣ ·) _).symm
        have hYsplit : ∑ y ∈ Y, (1 : ℚ) / y =
            ∑ y ∈ Yp, (1 : ℚ) / y + ∑ y ∈ Ynp, (1 : ℚ) / y := by
          exact (Finset.sum_filter_add_sum_filter_not Y (p ∣ ·) _).symm
        have hq : ((p * L * M : ℕ) : ℚ) * (∑ x ∈ Xp, (1 : ℚ) / x + ∑ x ∈ Xnp, (1 : ℚ) / x) =
            ((p * L * M : ℕ) : ℚ) * (∑ y ∈ Yp, (1 : ℚ) / y + ∑ y ∈ Ynp, (1 : ℚ) / y) := by
          rw [← hXsplit, ← hYsplit, hsum]
        have hXp_eval : ((p * L * M : ℕ) : ℚ) * ∑ x ∈ Xp, (1 : ℚ) / x =
            (M : ℚ) * ∑ b ∈ BX, ((L / b : ℕ) : ℚ) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_image hBX_inj]
          refine Finset.sum_congr rfl fun x hx => ?_
          have hpx : p ∣ x := (Finset.mem_filter.mp hx).2
          have hb_mem : x / p ∈ BX := Finset.mem_image.mpr ⟨x, hx, rfl⟩
          have hbdvd : x / p ∣ L := hb_dvd_L _ (Finset.mem_union_left _ hb_mem)
          have hxpos : (x : ℚ) ≠ 0 := by
            exact_mod_cast (isValidElem_pos (hX x (Finset.mem_filter.mp hx).1)).ne'
          have hxb : x = p * (x / p) := (Nat.mul_div_cancel' hpx).symm
          have hLb : L = (x / p) * (L / (x / p)) := (Nat.mul_div_cancel' hbdvd).symm
          push_cast
          field_simp [hxpos]
          have hnat : p * L = x * (L / (x / p)) := by
            calc p * L = p * ((x / p) * (L / (x / p))) := by rw [← hLb]
              _ = (p * (x / p)) * (L / (x / p)) := by ring
              _ = x * (L / (x / p)) := by rw [← hxb]
          exact_mod_cast hnat
        have hYp_eval : ((p * L * M : ℕ) : ℚ) * ∑ y ∈ Yp, (1 : ℚ) / y =
            (M : ℚ) * ∑ b ∈ BY, ((L / b : ℕ) : ℚ) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_image hBY_inj]
          refine Finset.sum_congr rfl fun y hy => ?_
          have hpy : p ∣ y := (Finset.mem_filter.mp hy).2
          have hb_mem : y / p ∈ BY := Finset.mem_image.mpr ⟨y, hy, rfl⟩
          have hbdvd : y / p ∣ L := hb_dvd_L _ (Finset.mem_union_right _ hb_mem)
          have hypos : (y : ℚ) ≠ 0 := by
            exact_mod_cast (isValidElem_pos (hY y (Finset.mem_filter.mp hy).1)).ne'
          have hyb : y = p * (y / p) := (Nat.mul_div_cancel' hpy).symm
          have hLb : L = (y / p) * (L / (y / p)) := (Nat.mul_div_cancel' hbdvd).symm
          push_cast
          field_simp [hypos]
          have hnat : p * L = y * (L / (y / p)) := by
            calc p * L = p * ((y / p) * (L / (y / p))) := by rw [← hLb]
              _ = (p * (y / p)) * (L / (y / p)) := by ring
              _ = y * (L / (y / p)) := by rw [← hyb]
          exact_mod_cast hnat
        have hXnp_eval : ((p * L * M : ℕ) : ℚ) * ∑ x ∈ Xnp, (1 : ℚ) / x =
            (p : ℚ) * ∑ x ∈ Xnp, ((L * (M / x) : ℕ) : ℚ) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x hx => ?_
          have hxdvd : x ∣ M := Finset.dvd_prod_of_mem _ (Finset.mem_union_left _ hx)
          have hxpos : (x : ℚ) ≠ 0 := by
            exact_mod_cast (isValidElem_pos (hX x (Finset.mem_filter.mp hx).1)).ne'
          have hMx : M = x * (M / x) := (Nat.mul_div_cancel' hxdvd).symm
          push_cast
          field_simp [hxpos]
          exact_mod_cast hMx
        have hYnp_eval : ((p * L * M : ℕ) : ℚ) * ∑ y ∈ Ynp, (1 : ℚ) / y =
            (p : ℚ) * ∑ y ∈ Ynp, ((L * (M / y) : ℕ) : ℚ) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun y hy => ?_
          have hydvd : y ∣ M := Finset.dvd_prod_of_mem _ (Finset.mem_union_right _ hy)
          have hypos : (y : ℚ) ≠ 0 := by
            exact_mod_cast (isValidElem_pos (hY y (Finset.mem_filter.mp hy).1)).ne'
          have hMy : M = y * (M / y) := (Nat.mul_div_cancel' hydvd).symm
          push_cast
          field_simp [hypos]
          exact_mod_cast hMy
        rw [mul_add, mul_add, hXp_eval, hXnp_eval, hYp_eval, hYnp_eval] at hq
        have hq2 : (((M : ℤ) * K : ℤ) : ℚ) = (((p : ℤ) * Rint : ℤ) : ℚ) := by
          simp only [K, Rint, Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_sum]
          linarith
        exact Rat.intCast_injective hq2
      have hp_dvd_K : (p : ℤ) ∣ K := by
        have h1 : (p : ℤ) ∣ (M : ℤ) * K := ⟨Rint, h_mul_eq⟩
        have hpcop : IsCoprime (p : ℤ) (M : ℤ) := by
          have : Nat.Coprime p M := hp_prime.coprime_iff_not_dvd.mpr hp_ndvd_M
          exact_mod_cast this.isCoprime
        exact hpcop.dvd_of_dvd_mul_left h1
      have hK_abs_lt : K.natAbs < p := by
        have hK_le1 : K.natAbs ≤ ∑ b ∈ BX ∪ BY, (L / b) := by
          have hsub_le : (K.natAbs : ℤ) ≤
              (∑ b ∈ BX, ((L / b : ℕ) : ℤ)) + (∑ b ∈ BY, ((L / b : ℕ) : ℤ)) := by
            have h1 : 0 ≤ ∑ b ∈ BX, ((L / b : ℕ) : ℤ) := by positivity
            have h2 : 0 ≤ ∑ b ∈ BY, ((L / b : ℕ) : ℤ) := by positivity
            rw [Int.natCast_natAbs]
            exact (abs_sub _ _).trans (by rw [abs_of_nonneg h1, abs_of_nonneg h2])
          rw [Finset.sum_union hB_disj]
          exact_mod_cast hsub_le
        let fmap : ℕ × Finset ℕ → ℕ := fun x => x.1 * ∏ r ∈ x.2, r
        have hB_sub_img : BX ∪ BY ⊆ (A0 ×ˢ Q.powerset).image fmap := by
          intro b hb
          obtain ⟨a, ha, U, hU, _, rfl⟩ := hB_struct b hb
          exact Finset.mem_image.mpr ⟨(a, U), Finset.mem_product.mpr
            ⟨ha, Finset.mem_powerset.mpr hU⟩, rfl⟩
        have hsum_le_prod : ∑ b ∈ BX ∪ BY, (L / b) ≤ 25 * ∏ r ∈ Q, (r + 1) := by
          calc ∑ b ∈ BX ∪ BY, (L / b)
              ≤ ∑ b ∈ (A0 ×ˢ Q.powerset).image fmap, (L / b) :=
                Finset.sum_le_sum_of_subset hB_sub_img
            _ ≤ ∑ x ∈ A0 ×ˢ Q.powerset, (L / fmap x) :=
                Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
            _ = ∑ x ∈ A0 ×ˢ Q.powerset, ((12 / x.1) * ∏ r ∈ Q \ x.2, r) := by
                refine Finset.sum_congr rfl fun ⟨a, U⟩ hx => ?_
                have ha : a ∈ A0 := (Finset.mem_product.mp hx).1
                have hU : U ⊆ Q := Finset.mem_powerset.mp (Finset.mem_product.mp hx).2
                have ha0 : 0 < a := by
                  simp only [A0, Finset.mem_insert, Finset.mem_singleton] at ha; omega
                have hU0 : 0 < ∏ r ∈ U, r :=
                  Finset.prod_pos fun r hr => (Finset.mem_filter.mp (hU hr)).2.1.pos
                have hQsplit : ∏ r ∈ Q, r = (∏ r ∈ U, r) * ∏ r ∈ Q \ U, r :=
                  (Finset.prod_sdiff hU).symm.trans (mul_comm _ _)
                have h12 : 12 = a * (12 / a) := (Nat.mul_div_cancel' (A0_dvd_twelve ha)).symm
                have hLeq : L = (a * ∏ r ∈ U, r) * ((12 / a) * ∏ r ∈ Q \ U, r) := by
                  calc L = 12 * ∏ r ∈ Q, r := rfl
                    _ = (a * (12 / a)) * ((∏ r ∈ U, r) * ∏ r ∈ Q \ U, r) := by
                        rw [← h12, ← hQsplit]
                    _ = (a * ∏ r ∈ U, r) * ((12 / a) * ∏ r ∈ Q \ U, r) := by ring
                show L / (a * ∏ r ∈ U, r) = (12 / a) * ∏ r ∈ Q \ U, r
                rw [hLeq, Nat.mul_div_cancel_left _ (Nat.mul_pos ha0 hU0)]
            _ = (∑ a ∈ A0, (12 / a)) * (∑ U ∈ Q.powerset, ∏ r ∈ Q \ U, r) := by
                rw [Finset.sum_product, Finset.sum_mul]
                refine Finset.sum_congr rfl fun a _ => ?_
                dsimp only
                rw [← Finset.mul_sum]
            _ = 25 * ∏ r ∈ Q, (r + 1) := by
                rw [sum_powerset_sdiff_prod]
                have hA0_sum : ∑ a ∈ A0, (12 / a) = 25 := by decide
                rw [hA0_sum]
        have h25_lt_p : 25 * ∏ r ∈ Q, (r + 1) < p := by
          by_cases hQ : Q.Nonempty
          · let q := Q.max' hQ
            have hq_mem : q ∈ Q := Finset.max'_mem Q hQ
            have hq_thresh : chainThresh q < p := (Finset.mem_filter.mp hq_mem).2.2
            have hQ_sub : Q ⊆ (Finset.Ioc 25 q).filter Nat.Prime := by
              intro r hr
              have hrm := Finset.mem_filter.mp hr
              exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
                ⟨(Finset.mem_Ioo.mp hrm.1).1, Finset.le_max' Q r hr⟩, hrm.2.1⟩
            calc 25 * ∏ r ∈ Q, (r + 1)
                ≤ 25 * ∏ r ∈ (Finset.Ioc 25 q).filter Nat.Prime, (r + 1) := by
                  gcongr
                  exact fun r _ _ => Nat.succ_le_succ (Nat.zero_le r)
              _ = chainThresh q := rfl
              _ < p := hq_thresh
          · rw [Finset.not_nonempty_iff_eq_empty] at hQ
            rw [hQ, Finset.prod_empty, mul_one]
            exact hp_25
        exact lt_of_le_of_lt (hK_le1.trans hsum_le_prod) h25_lt_p
      have hK_zero : K = 0 := by
        have hdvd_nat : p ∣ K.natAbs := Int.natCast_dvd.mp hp_dvd_K
        have habs0 : K.natAbs = 0 := Nat.eq_zero_of_dvd_of_lt hdvd_nat hK_abs_lt
        exact Int.natAbs_eq_zero.mp habs0
      have hB_sum : ∑ b ∈ BX, (1 : ℚ) / b = ∑ b ∈ BY, (1 : ℚ) / b := by
        have hL_ne : (L : ℚ) ≠ 0 := by exact_mod_cast hL_pos.ne'
        have hKq : (∑ b ∈ BX, ((L / b : ℕ) : ℚ)) = ∑ b ∈ BY, ((L / b : ℕ) : ℚ) := by
          have : (K : ℚ) = 0 := by exact_mod_cast hK_zero
          simp only [K, Int.cast_sub, Int.cast_sum, Int.cast_natCast] at this
          linarith
        have hrewrite : ∀ B : Finset ℕ, (∀ b ∈ B, b ∣ L ∧ 0 < b) →
            ∑ b ∈ B, ((L / b : ℕ) : ℚ) = (L : ℚ) * ∑ b ∈ B, (1 : ℚ) / b := by
          intro B hB
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b hb => ?_
          have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast (hB b hb).2.ne'
          field_simp [hb0]
          exact_mod_cast Nat.div_mul_cancel (hB b hb).1
        rw [hrewrite BX (fun b hb => ⟨hb_dvd_L _ (Finset.mem_union_left _ hb),
            isValidElem_pos (hBX_valid b hb)⟩),
          hrewrite BY (fun b hb => ⟨hb_dvd_L _ (Finset.mem_union_right _ hb),
            isValidElem_pos (hBY_valid b hb)⟩)] at hKq
        exact mul_left_cancel₀ hL_ne hKq
      have hB_emp := ih (N_max - 1) (by omega) BX BY hBX_valid hBY_valid hB_disj hB_le hB_sum
      rw [hB_emp.1, hB_emp.2, Finset.union_empty] at hB_ne
      exact Finset.not_nonempty_empty hB_ne
    · -- Case 1: no prime > 25 divides any element of X ∪ Y, so X, Y ⊆ A0
      have hX_sub : X ⊆ A0 := by
        intro n hn
        obtain ⟨a, ha, S, hS, rfl⟩ := hX n hn
        have hSemp : S = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro p hpS
          have hp_pr := (hS.1 p hpS).1
          have hp_25 := (hS.1 p hpS).2
          have hp_dvd : p ∣ a * ∏ r ∈ S, r :=
            dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hpS) a
          have hp_pf : p ∈ (a * ∏ r ∈ S, r).primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hp_pr, hp_dvd, (isValidElem_pos (hX _ hn)).ne'⟩
          exact hP ⟨p, Finset.mem_filter.mpr
            ⟨Finset.mem_biUnion.mpr ⟨_, Finset.mem_union_left _ hn, hp_pf⟩, hp_25⟩⟩
        simpa [hSemp] using ha
      have hY_sub : Y ⊆ A0 := by
        intro n hn
        obtain ⟨a, ha, S, hS, rfl⟩ := hY n hn
        have hSemp : S = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro p hpS
          have hp_pr := (hS.1 p hpS).1
          have hp_25 := (hS.1 p hpS).2
          have hp_dvd : p ∣ a * ∏ r ∈ S, r :=
            dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hpS) a
          have hp_pf : p ∈ (a * ∏ r ∈ S, r).primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hp_pr, hp_dvd, (isValidElem_pos (hY _ hn)).ne'⟩
          exact hP ⟨p, Finset.mem_filter.mpr
            ⟨Finset.mem_biUnion.mpr ⟨_, Finset.mem_union_right _ hn, hp_pf⟩, hp_25⟩⟩
        simpa [hSemp] using ha
      have hXY_eq : X = Y :=
        A0_injOn (Finset.mem_powerset.mpr hX_sub) (Finset.mem_powerset.mpr hY_sub) hsum
      have hY_emp : Y = ∅ := by
        rw [hXY_eq] at hdisj
        exact disjoint_self.mp hdisj
      exact hne ⟨hXY_eq.trans hY_emp, hY_emp⟩

theorem primeChain_injOn {A : Finset ℕ} (hA : ∀ n ∈ A, IsValidElem n) :
    Set.InjOn (fun (S : Finset ℕ) ↦ ∑ n ∈ S, (1 : ℚ) / n) A.powerset := by
  intro X hX Y hY hsum
  have hX' : X ⊆ A := Finset.mem_powerset.mp hX
  have hY' : Y ⊆ A := Finset.mem_powerset.mp hY
  have hsum_diff : ∑ n ∈ X \ Y, (1 : ℚ) / n = ∑ n ∈ Y \ X, (1 : ℚ) / n := by
    have h1 : ∑ n ∈ X \ Y, (1 : ℚ) / n + ∑ n ∈ X ∩ Y, (1 : ℚ) / n = ∑ n ∈ X, (1 : ℚ) / n := by
      rw [← Finset.sum_union (Finset.disjoint_left.mpr fun a ha1 ha2 =>
        (Finset.mem_sdiff.mp ha1).2 (Finset.mem_inter.mp ha2).2), Finset.sdiff_union_inter]
    have h2 : ∑ n ∈ Y \ X, (1 : ℚ) / n + ∑ n ∈ Y ∩ X, (1 : ℚ) / n = ∑ n ∈ Y, (1 : ℚ) / n := by
      rw [← Finset.sum_union (Finset.disjoint_left.mpr fun a ha1 ha2 =>
        (Finset.mem_sdiff.mp ha1).2 (Finset.mem_inter.mp ha2).2), Finset.sdiff_union_inter]
    rw [Finset.inter_comm] at h2
    linarith
  have hemp := primeChain_disjoint_eq_empty (((X \ Y) ∪ (Y \ X)).sup id) (X \ Y) (Y \ X)
    (fun n hn => hA n (hX' (Finset.mem_sdiff.mp hn).1))
    (fun n hn => hA n (hY' (Finset.mem_sdiff.mp hn).1))
    disjoint_sdiff_sdiff
    (fun n hn => Finset.le_sup (f := id) hn)
    hsum_diff
  exact Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp hemp.1)
    (Finset.sdiff_eq_empty_iff_subset.mp hemp.2)

/- Section 2: Factorial log bounds and Chebyshev's 30n lower bound on π(x) -/

lemma log_factorial_ge (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n + 1 ≤ Real.log (n ! : ℕ) := by
  have hsum : Real.log (n ! : ℕ) = ∑ k ∈ Finset.Icc 1 n, Real.log (k : ℝ) := by
    rw [← Finset.prod_Ico_id_eq_factorial, Nat.cast_prod, Real.log_prod]
    · congr 1
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      exact_mod_cast (show k ≠ 0 by omega)
  rw [hsum]
  have hI : ∫ t in (1 : ℝ)..(n : ℝ), Real.log t = (n : ℝ) * Real.log n - n + 1 := by
    rw [integral_log]
    simp
  rw [← hI]
  have h_aux : ∀ m : ℕ, 1 ≤ m →
      ∫ t in (1 : ℝ)..(m : ℝ), Real.log t ≤ ∑ k ∈ Finset.Icc 1 m, Real.log (k : ℝ) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Nat.cast_add, Nat.cast_one]
      have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
        (f := Real.log) (a := (1 : ℝ)) (b := (m : ℝ)) (c := (m : ℝ) + 1)
        (ContinuousOn.intervalIntegrable (fun t ht => by
          rw [Set.uIcc_of_le (by exact_mod_cast hm)] at ht
          exact (Real.continuousAt_log (by linarith [ht.1])).continuousWithinAt))
        (ContinuousOn.intervalIntegrable (fun t ht => by
          rw [Set.uIcc_of_le (by linarith)] at ht
          have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
          exact (Real.continuousAt_log (by linarith [ht.1])).continuousWithinAt))
      rw [← hsplit]
      gcongr
      calc ∫ t in (m : ℝ)..((m : ℝ) + 1), Real.log t
          ≤ ∫ _ in (m : ℝ)..((m : ℝ) + 1), Real.log ((m : ℝ) + 1) := by
            refine intervalIntegral.integral_mono_on (by linarith) ?_ (by simp) fun t ht => ?_
            · refine ContinuousOn.intervalIntegrable fun t ht => ?_
              rw [Set.uIcc_of_le (by linarith)] at ht
              have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
              exact (Real.continuousAt_log (by linarith [ht.1])).continuousWithinAt
            · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
              exact Real.log_le_log (by linarith [ht.1]) ht.2
        _ = Real.log ((m : ℝ) + 1) := by simp
  exact h_aux n hn

lemma log_factorial_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n ! : ℕ) ≤ (n : ℝ) * Real.log n - n + Real.log n + 1 := by
  have hsum : Real.log (n ! : ℕ) = ∑ k ∈ Finset.Icc 1 n, Real.log (k : ℝ) := by
    rw [← Finset.prod_Ico_id_eq_factorial, Nat.cast_prod, Real.log_prod]
    · congr 1
    · intro k hk; simp only [Finset.mem_Ico] at hk; exact_mod_cast (show k ≠ 0 by omega)
  rw [hsum]
  have hI : ∫ t in (1 : ℝ)..(n : ℝ), Real.log t = (n : ℝ) * Real.log n - n + 1 := by
    rw [integral_log]; simp
  have h_aux : ∀ m : ℕ, 1 ≤ m →
      ∑ k ∈ Finset.Ico 1 m, Real.log (k : ℝ) ≤ ∫ t in (1 : ℝ)..(m : ℝ), Real.log t := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      rw [Finset.sum_Ico_succ_top hm, Nat.cast_add, Nat.cast_one]
      have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
        (f := Real.log) (a := (1 : ℝ)) (b := (m : ℝ)) (c := (m : ℝ) + 1)
        (ContinuousOn.intervalIntegrable (fun t ht => by
          rw [Set.uIcc_of_le (by exact_mod_cast hm)] at ht
          exact (Real.continuousAt_log (by linarith [ht.1])).continuousWithinAt))
        (ContinuousOn.intervalIntegrable (fun t ht => by
          rw [Set.uIcc_of_le (by linarith)] at ht
          have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
          exact (Real.continuousAt_log (by linarith [ht.1])).continuousWithinAt))
      rw [← hsplit]
      gcongr
      calc Real.log (m : ℝ)
          = ∫ _ in (m : ℝ)..((m : ℝ) + 1), Real.log (m : ℝ) := by simp
        _ ≤ ∫ t in (m : ℝ)..((m : ℝ) + 1), Real.log t := by
            refine intervalIntegral.integral_mono_on (by linarith) (by simp) ?_ fun t ht => ?_
            · refine ContinuousOn.intervalIntegrable fun t ht => ?_
              rw [Set.uIcc_of_le (by linarith)] at ht
              have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
              exact (Real.continuousAt_log (by linarith [ht.1])).continuousWithinAt
            · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
              exact Real.log_le_log (by linarith) ht.1
  have hsplit_sum : ∑ k ∈ Finset.Icc 1 n, Real.log (k : ℝ) =
      (∑ k ∈ Finset.Ico 1 n, Real.log (k : ℝ)) + Real.log (n : ℝ) := by
    have hIcc : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hIcc, Finset.sum_Ico_succ_top hn]
  linarith [h_aux n hn]

lemma nat_div_thirty (d : ℕ) (hd : d < 30) : d ≤ d / 2 + d / 3 + d / 5 + 1 := by
  interval_cases d <;> decide

lemma div_thirty_ineq (a b : ℕ) :
    30 * a / b + a / b ≤ 15 * a / b + 10 * a / b + 6 * a / b + 1 := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  let q := a / b
  let r := a % b
  have ha : a = b * q + r := (Nat.div_add_mod a b).symm
  have hr : r < b := Nat.mod_lt a hb
  have h1 : 30 * a / b = 30 * q + 30 * r / b := by
    rw [ha, mul_add, ← mul_assoc, mul_comm 30 b, mul_assoc,
      Nat.mul_add_div hb]
  have h2 : a / b = q := rfl
  have h3 : 15 * a / b = 15 * q + 15 * r / b := by
    rw [ha, mul_add, ← mul_assoc, mul_comm 15 b, mul_assoc, Nat.mul_add_div hb]
  have h4 : 10 * a / b = 10 * q + 10 * r / b := by
    rw [ha, mul_add, ← mul_assoc, mul_comm 10 b, mul_assoc, Nat.mul_add_div hb]
  have h5 : 6 * a / b = 6 * q + 6 * r / b := by
    rw [ha, mul_add, ← mul_assoc, mul_comm 6 b, mul_assoc, Nat.mul_add_div hb]
  rw [h1, h2, h3, h4, h5]
  let d := 30 * r / b
  have hd_lt : d < 30 := by
    rw [Nat.div_lt_iff_lt_mul hb]
    omega
  have hd_le : d * b ≤ 30 * r := Nat.div_mul_le_self (30 * r) b
  have hd2 : d / 2 ≤ 15 * r / b := by
    rw [Nat.le_div_iff_mul_le hb]
    have : 2 * (d / 2) ≤ d := Nat.mul_div_le d 2
    nlinarith
  have hd3 : d / 3 ≤ 10 * r / b := by
    rw [Nat.le_div_iff_mul_le hb]
    have : 3 * (d / 3) ≤ d := Nat.mul_div_le d 3
    nlinarith
  have hd5 : d / 5 ≤ 6 * r / b := by
    rw [Nat.le_div_iff_mul_le hb]
    have : 5 * (d / 5) ≤ d := Nat.mul_div_le d 5
    nlinarith
  have hd_omega := nat_div_thirty d hd_lt
  omega

lemma factorial_30_dvd_lcmUpto (m : ℕ) :
    (30 * m)! * m ! ∣ (15 * m)! * (10 * m)! * (6 * m)! * Nat.lcmUpto (30 * m) := by
  have hlhs_ne : (30 * m)! * m ! ≠ 0 := by positivity
  have hrhs_ne : (15 * m)! * (10 * m)! * (6 * m)! * Nat.lcmUpto (30 * m) ≠ 0 :=
    mul_ne_zero (by positivity) (Nat.lcmUpto_ne_zero _)
  rw [← Nat.factorization_prime_le_iff_dvd hlhs_ne hrhs_ne]
  intro p hp
  simp only [Nat.factorization_mul, Finsupp.coe_add, Pi.add_apply,
    Nat.factorial_ne_zero, Nat.lcmUpto_ne_zero, ne_eq, mul_eq_zero, or_self, not_false_eq_true]
  let B := Nat.log p (30 * m) + 1
  have hB30 : Nat.log p (30 * m) < B := Nat.lt_succ_self _
  have hB1 : Nat.log p m < B := (Nat.log_mono_right (by omega)).trans_lt hB30
  have hB15 : Nat.log p (15 * m) < B := (Nat.log_mono_right (by omega)).trans_lt hB30
  have hB10 : Nat.log p (10 * m) < B := (Nat.log_mono_right (by omega)).trans_lt hB30
  have hB6 : Nat.log p (6 * m) < B := (Nat.log_mono_right (by omega)).trans_lt hB30
  rw [Nat.factorization_factorial hp hB30, Nat.factorization_factorial hp hB1,
    Nat.factorization_factorial hp hB15, Nat.factorization_factorial hp hB10,
    Nat.factorization_factorial hp hB6, Nat.factorization_lcmUpto (30 * m) hp]
  have hcard : Nat.log p (30 * m) = ∑ _ ∈ Finset.Ico 1 B, 1 := by simp [B]
  rw [hcard, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => div_thirty_ineq m (p ^ k)

lemma psi_thirty_mul_ge (m : ℕ) (hm : 1 ≤ m) :
    0.921 * (30 * m : ℝ) - 3 * Real.log (30 * m : ℝ) - 3 ≤ Chebyshev.psi (30 * m : ℕ) := by
  have hdvd := factorial_30_dvd_lcmUpto m
  have hpos_r : 0 < (15 * m)! * (10 * m)! * (6 * m)! * Nat.lcmUpto (30 * m) :=
    Nat.mul_pos (by positivity) (Nat.lcmUpto_pos _)
  have hle_nat : (30 * m)! * m ! ≤ (15 * m)! * (10 * m)! * (6 * m)! * Nat.lcmUpto (30 * m) :=
    Nat.le_of_dvd hpos_r hdvd
  have hlog_le : Real.log (((30 * m)! * m ! : ℕ) : ℝ) ≤
      Real.log (((15 * m)! * (10 * m)! * (6 * m)! * Nat.lcmUpto (30 * m) : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hle_nat)
  simp only [Nat.cast_mul] at hlog_le
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by exact_mod_cast (Nat.lcmUpto_ne_zero _)),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    ← Chebyshev.psi_eq_log_lcmUpto] at hlog_le
  have h30 := log_factorial_ge (30 * m) (by omega)
  have h1 := log_factorial_ge m hm
  have h15 := log_factorial_le (15 * m) (by omega)
  have h10 := log_factorial_le (10 * m) (by omega)
  have h6 := log_factorial_le (6 * m) (by omega)
  have hlog30 : Real.log ((30 * m : ℕ) : ℝ) = Real.log 30 + Real.log m := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) (by positivity)]
  have hlog15 : Real.log ((15 * m : ℕ) : ℝ) = Real.log 15 + Real.log m := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) (by positivity)]
  have hlog10 : Real.log ((10 * m : ℕ) : ℝ) = Real.log 10 + Real.log m := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) (by positivity)]
  have hlog6 : Real.log ((6 * m : ℕ) : ℝ) = Real.log 6 + Real.log m := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) (by positivity)]
  have hconst : 30 * Real.log 30 - 15 * Real.log 15 - 10 * Real.log 10 - 6 * Real.log 6 =
      14 * Real.log 2 + 9 * Real.log 3 + 5 * Real.log 5 := by
    have h30' : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
      rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
        Real.log_mul (by norm_num) (by norm_num)]
    have h15' : Real.log 15 = Real.log 3 + Real.log 5 := by
      rw [show (15 : ℝ) = 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    have h10' : Real.log 10 = Real.log 2 + Real.log 5 := Real.log_ten_eq
    have h6' : Real.log 6 = Real.log 2 + Real.log 3 := by
      rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith
  have hconst_ge : 27.63 ≤ 14 * Real.log 2 + 9 * Real.log 3 + 5 * Real.log 5 := by
    linarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]
  have h15_le : Real.log ((15 * m : ℕ) : ℝ) ≤ Real.log ((30 * m : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (show 15 * m ≤ 30 * m by omega))
  have h10_le : Real.log ((10 * m : ℕ) : ℝ) ≤ Real.log ((30 * m : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (show 10 * m ≤ 30 * m by omega))
  have h6_le : Real.log ((6 * m : ℕ) : ℝ) ≤ Real.log ((30 * m : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (show 6 * m ≤ 30 * m by omega))
  push_cast at h30 h15 h10 h6 hlog30 hlog15 hlog10 hlog6 h15_le h10_le h6_le hlog_le ⊢
  have hm_nonneg : (0 : ℝ) ≤ m := by positivity
  nlinarith

lemma primeCounting_ge_chebyshev30 {x : ℝ} (hx : Real.exp 100 ≤ x) :
    0.919 * x / Real.log x ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hx_big : 1000000 ≤ x := by
    calc (1000000 : ℝ) ≤ 1 + 100 + 100 ^ 2 / 2 + 100 ^ 3 / 6 + 100 ^ 4 / 24 := by norm_num
      _ = ∑ i ∈ Finset.range 5, (100 : ℝ) ^ i / i ! := by
          simp [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 100 := Real.sum_le_exp_of_nonneg (by norm_num) 5
      _ ≤ x := hx
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogx_le : Real.log x ≤ x / 10000 := by
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < x / 100000 by linarith)
    have h2 : Real.log (x / 100000) = Real.log x - Real.log 100000 :=
      Real.log_div (by linarith) (by norm_num)
    have h3 : Real.log 100000 ≤ 12 := by
      have : (100000 : ℝ) ≤ Real.exp 12 := by
        have he := Real.exp_one_gt_d9
        have : (2.718 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := by gcongr; linarith
        rw [← Real.exp_nat_mul] at this
        norm_num at this ⊢
        linarith
      exact (Real.log_le_iff_le_exp (by norm_num)).mpr this
    linarith
  let m : ℕ := ⌊x / 30⌋₊
  have hm1 : 1 ≤ m := by
    rw [Nat.one_le_floor_iff]
    linarith
  have h30m_le : (30 * m : ℝ) ≤ x := by
    have := Nat.floor_le (show (0 : ℝ) ≤ x / 30 by linarith)
    linarith
  have h30m_gt : x - 30 ≤ (30 * m : ℝ) := by
    have := Nat.lt_floor_add_one (x / 30)
    linarith
  have hpsi_mono : Chebyshev.psi (30 * m : ℕ) ≤ Chebyshev.psi x :=
    Chebyshev.psi_mono (by exact_mod_cast h30m_le)
  have hpsi_lb := psi_thirty_mul_ge m hm1
  have hlog30m_le : Real.log (30 * m : ℝ) ≤ Real.log x :=
    Real.log_le_log (by positivity) h30m_le
  have hpsi_x : 0.919 * x ≤ Chebyshev.psi x := by
    push_cast at hpsi_lb hpsi_mono
    linarith
  have hpi := Chebyshev.psi_le_primeCounting_mul_log' x
  rw [div_le_iff₀ hlogx_pos]
  exact hpsi_x.trans hpi

/- Section 3: Mertens' first theorem and sign-positive Abel summation -/

/-- Mertens sum `M(x) = ∑_{p ≤ x} log p / p`. -/
noncomputable def mertensM (x : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log (p : ℝ) / p

lemma log_div_sq_antitone : AntitoneOn (fun t : ℝ => Real.log t / t ^ 2) (Set.Ici 3) := by
  intro x hx y hy hxy
  have hx3 : 3 ≤ x := hx
  have hderiv : ∀ t ∈ Set.Icc x y,
      HasDerivAt (fun u : ℝ => Real.log u / u ^ 2) ((1 - 2 * Real.log t) / t ^ 3) t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [hx3, ht.1]
    have h1 := (Real.hasDerivAt_log ht0).div (hasDerivAt_pow 2 t) (pow_ne_zero 2 ht0)
    refine h1.congr_deriv ?_
    norm_num
    field_simp [ht0]
  have hneg : ∀ t ∈ Set.Ioo x y, (1 - 2 * Real.log t) / t ^ 3 ≤ 0 := by
    intro t ht
    have ht3 : 3 ≤ t := le_trans hx3 ht.1.le
    have hlogt : 1 ≤ Real.log t := by
      have h3 : Real.exp 1 ≤ t := (Real.exp_one_lt_three.le).trans ht3
      exact (Real.le_log_iff_exp_le (by linarith)).mpr h3
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  exact antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc x y)
    (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht => by
      rw [interior_Icc] at ht
      exact (hderiv t (Set.Ioo_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => by
      rw [interior_Icc] at ht
      exact hneg t ht)
    (Set.left_mem_Icc.mpr hxy) (Set.right_mem_Icc.mpr hxy) hxy

lemma integral_log_div_sq (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, Real.log t / t ^ 2 = (Real.log a + 1) / a - (Real.log b + 1) / b := by
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun u : ℝ => -((Real.log u + 1) / u)) (Real.log t / t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have h1 := (((Real.hasDerivAt_log ht0).add_const 1).div (hasDerivAt_id t) ht0).neg
    refine h1.congr_deriv ?_
    dsimp only [id]
    field_simp [ht0]
    ring
  have hint : IntervalIntegrable (fun t : ℝ => Real.log t / t ^ 2) MeasureTheory.volume a b := by
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact ((Real.continuousAt_log ht0).div ((continuous_pow 2).continuousAt)
      (pow_ne_zero 2 ht0)).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

lemma sum_log_div_p_mul_pred_le (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, Real.log (p : ℝ) / ((p : ℝ) * (p - 1)) ≤ 0.9 := by
  have hsplit : Nat.primesLE n =
      (Nat.primesLE n \ Nat.primesLE 13) ∪ (Nat.primesLE n ∩ Nat.primesLE 13) :=
    (Finset.sdiff_union_inter _ _).symm
  have hdisj : Disjoint (Nat.primesLE n \ Nat.primesLE 13) (Nat.primesLE n ∩ Nat.primesLE 13) :=
    Finset.disjoint_left.mpr fun p hp1 hp2 =>
      (Finset.mem_sdiff.mp hp1).2 (Finset.mem_inter.mp hp2).2
  rw [hsplit, Finset.sum_union hdisj]
  have hsmall : ∑ p ∈ Nat.primesLE n ∩ Nat.primesLE 13,
      Real.log (p : ℝ) / ((p : ℝ) * (p - 1)) ≤ 0.75 := by
    calc ∑ p ∈ Nat.primesLE n ∩ Nat.primesLE 13, Real.log (p : ℝ) / ((p : ℝ) * (p - 1))
        ≤ ∑ p ∈ Nat.primesLE 13, Real.log (p : ℝ) / ((p : ℝ) * (p - 1)) :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
            (fun p hp _ => div_nonneg (Real.log_natCast_nonneg p)
              (mul_nonneg (Nat.cast_nonneg p) (by
                have : (2 : ℝ) ≤ p := by exact_mod_cast Nat.two_le_of_mem_primesLE hp
                linarith)))
      _ ≤ 0.75 := by
          have hp13 : Nat.primesLE 13 = {2, 3, 5, 7, 11, 13} := by decide
          rw [hp13]
          simp only [Finset.sum_insert (by decide : (2 : ℕ) ∉ ({3, 5, 7, 11, 13} : Finset ℕ)),
            Finset.sum_insert (by decide : (3 : ℕ) ∉ ({5, 7, 11, 13} : Finset ℕ)),
            Finset.sum_insert (by decide : (5 : ℕ) ∉ ({7, 11, 13} : Finset ℕ)),
            Finset.sum_insert (by decide : (7 : ℕ) ∉ ({11, 13} : Finset ℕ)),
            Finset.sum_insert (by decide : (11 : ℕ) ∉ ({13} : Finset ℕ)),
            Finset.sum_singleton, Nat.cast_ofNat]
          have hl2 := Real.log_two_lt_d9
          have hl3 := Real.log_three_lt_d9
          have hl5 := Real.log_five_lt_d9
          have hl7 : Real.log 7 ≤ 2 := by
            have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7 / 8 by norm_num)
            rw [Real.log_div (by norm_num) (by norm_num),
              show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at h
            push_cast at h; linarith
          have hl11 : Real.log 11 ≤ 2.5 := by
            have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 11 / 8 by norm_num)
            rw [Real.log_div (by norm_num) (by norm_num),
              show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at h
            push_cast at h; linarith
          have hl13 : Real.log 13 ≤ 2.7 := by
            have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 13 / 16 by norm_num)
            rw [Real.log_div (by norm_num) (by norm_num),
              show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at h
            push_cast at h; linarith
          linarith
  have htail : ∑ p ∈ Nat.primesLE n \ Nat.primesLE 13,
      Real.log (p : ℝ) / ((p : ℝ) * (p - 1)) ≤ 0.15 := by
    by_cases hn17 : n < 17
    · have hemp : Nat.primesLE n \ Nat.primesLE 13 = ∅ := by
        ext p
        simp only [Finset.mem_sdiff, Nat.mem_primesLE, Finset.notMem_empty, iff_false]
        rintro ⟨⟨hpn, hpp⟩, hnot13⟩
        have hp14 : 14 ≤ p := by by_contra hle; exact hnot13 ⟨by omega, hpp⟩
        have : p = 14 ∨ p = 15 ∨ p = 16 := by omega
        rcases this with rfl | rfl | rfl <;> exact absurd hpp (by decide)
      rw [hemp, Finset.sum_empty]; norm_num
    · push Not at hn17
      have hterm : ∀ p ∈ Nat.primesLE n \ Nat.primesLE 13,
          Real.log (p : ℝ) / ((p : ℝ) * (p - 1)) ≤
            (17 / 32 : ℝ) * ∫ t in ((p : ℝ) - 2)..(p : ℝ), Real.log t / t ^ 2 := by
        intro p hp
        have hpm := Finset.mem_sdiff.mp hp
        have hpp : p.Prime := Nat.prime_of_mem_primesLE hpm.1
        have hp14 : 14 ≤ p := by
          by_contra h; exact hpm.2 (Nat.mem_primesLE.mpr ⟨by omega, hpp⟩)
        have hp17 : 17 ≤ p := by
          by_contra h
          have : p = 14 ∨ p = 15 ∨ p = 16 := by omega
          rcases this with rfl | rfl | rfl <;> exact absurd hpp (by decide)
        have hpR : (17 : ℝ) ≤ p := by exact_mod_cast hp17
        have h1 : Real.log (p : ℝ) / ((p : ℝ) * (p - 1)) ≤
            (17 / 16 : ℝ) * (Real.log (p : ℝ) / (p : ℝ) ^ 2) := by
          have hpos : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
          have hden : (16 / 17 : ℝ) * (p : ℝ) ≤ (p : ℝ) - 1 := by linarith
          rw [show (17 / 16 : ℝ) * (Real.log (p : ℝ) / (p : ℝ) ^ 2) =
              Real.log (p : ℝ) / ((p : ℝ) * ((16 / 17 : ℝ) * (p : ℝ))) by field_simp]
          exact div_le_div_of_nonneg_left hpos (by positivity)
            (mul_le_mul_of_nonneg_left hden (by positivity))
        have h2 : 2 * (Real.log (p : ℝ) / (p : ℝ) ^ 2) ≤
            ∫ t in ((p : ℝ) - 2)..(p : ℝ), Real.log t / t ^ 2 := by
          calc 2 * (Real.log (p : ℝ) / (p : ℝ) ^ 2)
              = ∫ _ in ((p : ℝ) - 2)..(p : ℝ), Real.log (p : ℝ) / (p : ℝ) ^ 2 := by
                rw [intervalIntegral.integral_const]; simp
            _ ≤ ∫ t in ((p : ℝ) - 2)..(p : ℝ), Real.log t / t ^ 2 := by
                refine intervalIntegral.integral_mono_on (by linarith) (by simp) ?_ fun t ht => ?_
                · refine ContinuousOn.intervalIntegrable fun t ht => ?_
                  rw [Set.uIcc_of_le (by linarith)] at ht
                  have ht0 : t ≠ 0 := by linarith [ht.1]
                  exact ((Real.continuousAt_log ht0).div ((continuous_pow 2).continuousAt)
                    (pow_ne_zero 2 ht0)).continuousWithinAt
                · exact log_div_sq_antitone (show (3 : ℝ) ≤ t by linarith [ht.1])
                    (show (3 : ℝ) ≤ p by linarith) ht.2
        linarith
      let M := n / 2
      have hM8 : 8 ≤ M := by omega
      have hsub_odd : Nat.primesLE n \ Nat.primesLE 13 ⊆
          (Finset.Icc 8 M).image (fun j : ℕ => 2 * j + 1) := by
        intro p hp
        have hpm := Finset.mem_sdiff.mp hp
        have hpp : p.Prime := Nat.prime_of_mem_primesLE hpm.1
        have hpn : p ≤ n := Nat.le_of_mem_primesLE hpm.1
        have hp17 : 17 ≤ p := by
          by_contra h
          have hp14 : 14 ≤ p := by
            by_contra h2; exact hpm.2 (Nat.mem_primesLE.mpr ⟨by omega, hpp⟩)
          have : p = 14 ∨ p = 15 ∨ p = 16 := by omega
          rcases this with rfl | rfl | rfl <;> exact absurd hpp (by decide)
        have hodd : Odd p := hpp.odd_of_ne_two (by omega)
        obtain ⟨j, rfl⟩ := hodd
        exact Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩
      have hsum_odd_all : ∀ K : ℕ, 8 ≤ K →
          ∑ j ∈ Finset.Icc 8 K,
            ∫ t in (((2 * j + 1 : ℕ) : ℝ) - 2)..((2 * j + 1 : ℕ) : ℝ), Real.log t / t ^ 2 =
          ∫ t in (15 : ℝ)..((2 * K + 1 : ℕ) : ℝ), Real.log t / t ^ 2 := by
        intro K hK
        induction K, hK using Nat.le_induction with
        | base => simp; norm_num
        | succ m hm ih =>
          rw [Finset.sum_Icc_succ_top (by omega), ih]
          have hstep : ((2 * (m + 1) + 1 : ℕ) : ℝ) - 2 = ((2 * m + 1 : ℕ) : ℝ) := by
            push_cast; ring
          rw [hstep]
          exact intervalIntegral.integral_add_adjacent_intervals
            (ContinuousOn.intervalIntegrable fun t ht => by
              rw [Set.uIcc_of_le (by push_cast; linarith [show (8 : ℝ) ≤ m by exact_mod_cast hm])] at ht
              have ht0 : t ≠ 0 := by linarith [ht.1]
              exact ((Real.continuousAt_log ht0).div ((continuous_pow 2).continuousAt)
                (pow_ne_zero 2 ht0)).continuousWithinAt)
            (ContinuousOn.intervalIntegrable fun t ht => by
              rw [Set.uIcc_of_le (by push_cast; linarith)] at ht
              have ht0 : t ≠ 0 := by
                have : (8 : ℝ) ≤ m := by exact_mod_cast hm
                push_cast at ht; linarith [ht.1]
              exact ((Real.continuousAt_log ht0).div ((continuous_pow 2).continuousAt)
                (pow_ne_zero 2 ht0)).continuousWithinAt)
      have h_int_nonneg : ∀ p : ℕ, p ∈ (Finset.Icc 8 M).image (fun j : ℕ => 2 * j + 1) →
          0 ≤ (17 / 32 : ℝ) * ∫ t in ((p : ℝ) - 2)..(p : ℝ), Real.log t / t ^ 2 := by
        intro p hp
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
        have hj8 : (8 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
        refine mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg (by linarith) fun t ht => ?_)
        have ht1 : 1 ≤ t := by push_cast at ht; linarith [ht.1]
        exact div_nonneg (Real.log_nonneg ht1) (sq_nonneg t)
      calc ∑ p ∈ Nat.primesLE n \ Nat.primesLE 13, Real.log (p : ℝ) / ((p : ℝ) * (p - 1))
          ≤ ∑ p ∈ Nat.primesLE n \ Nat.primesLE 13,
              (17 / 32 : ℝ) * ∫ t in ((p : ℝ) - 2)..(p : ℝ), Real.log t / t ^ 2 :=
            Finset.sum_le_sum hterm
        _ ≤ ∑ p ∈ (Finset.Icc 8 M).image (fun j : ℕ => 2 * j + 1),
              (17 / 32 : ℝ) * ∫ t in ((p : ℝ) - 2)..(p : ℝ), Real.log t / t ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub_odd (fun p hp _ => h_int_nonneg p hp)
        _ = (17 / 32 : ℝ) * ∑ j ∈ Finset.Icc 8 M,
              ∫ t in (((2 * j + 1 : ℕ) : ℝ) - 2)..((2 * j + 1 : ℕ) : ℝ), Real.log t / t ^ 2 := by
            rw [Finset.sum_image (fun a _ b _ h => by omega), ← Finset.mul_sum]
        _ = (17 / 32 : ℝ) * ∫ t in (15 : ℝ)..((2 * M + 1 : ℕ) : ℝ), Real.log t / t ^ 2 := by
            rw [hsum_odd_all M hM8]
        _ = (17 / 32 : ℝ) * ((Real.log 15 + 1) / 15 -
              (Real.log ((2 * M + 1 : ℕ) : ℝ) + 1) / ((2 * M + 1 : ℕ) : ℝ)) := by
            rw [integral_log_div_sq 15 _ (by norm_num) (by
              have : (8 : ℝ) ≤ M := by exact_mod_cast hM8
              push_cast; linarith)]
        _ ≤ (17 / 32 : ℝ) * ((Real.log 15 + 1) / 15) := by
            have hpos : 0 ≤ (Real.log ((2 * M + 1 : ℕ) : ℝ) + 1) / ((2 * M + 1 : ℕ) : ℝ) :=
              div_nonneg (by linarith [Real.log_natCast_nonneg (2 * M + 1)]) (by positivity)
            linarith
        _ ≤ 0.15 := by
            have hlog15 : Real.log 15 = Real.log 3 + Real.log 5 := by
              rw [show (15 : ℝ) = 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
            linarith [Real.log_three_lt_d9, Real.log_five_lt_d9]
  linarith

lemma mertensM_nat_ge (n : ℕ) (hn : 1 ≤ n) : Real.log n - 1.9 ≤ mertensM n := by
  have hfac_eq : Real.log (n ! : ℕ) =
      ∑ p ∈ Nat.primesLE n, ((n !).factorization p : ℝ) * Real.log p := by
    have hne : n ! ≠ 0 := Nat.factorial_ne_zero n
    have hprod := Nat.prod_factorization_pow_eq_self hne
    have hsub : (n !).primeFactors = Nat.primesLE n := by
      ext p
      simp only [Nat.mem_primeFactors, Nat.mem_primesLE, ne_eq, Nat.factorial_ne_zero,
        not_false_eq_true, and_true]
      exact ⟨fun ⟨hp, hd⟩ => ⟨hp.dvd_factorial.mp hd, hp⟩,
        fun ⟨hle, hp⟩ => ⟨hp, hp.dvd_factorial.mpr hle⟩⟩
    conv_lhs => rw [← hprod, Nat.prod_factorization_eq_prod_primeFactors, hsub]
    rw [Nat.cast_prod, Real.log_prod]
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [Nat.cast_pow, Real.log_pow]
    · intro p hp
      exact_mod_cast pow_ne_zero _ (Nat.prime_of_mem_primesLE hp).ne_zero
  have hfac_le : Real.log (n ! : ℕ) ≤
      (n : ℝ) * (mertensM n + ∑ p ∈ Nat.primesLE n, Real.log (p : ℝ) / ((p : ℝ) * (p - 1))) := by
    rw [hfac_eq, mertensM, Nat.floor_natCast, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primesLE hp
    have hle_nat := Nat.factorization_factorial_le_div_pred hpp n
    have hle_real : ((n !).factorization p : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) := by
      calc ((n !).factorization p : ℝ) ≤ ((n / (p - 1) : ℕ) : ℝ) := by exact_mod_cast hle_nat
        _ ≤ (n : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
        _ = (n : ℝ) / ((p : ℝ) - 1) := by rw [Nat.cast_sub hpp.one_le, Nat.cast_one]
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hident : (n : ℝ) * (Real.log (p : ℝ) / (p : ℝ) + Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) =
        ((n : ℝ) / ((p : ℝ) - 1)) * Real.log (p : ℝ) := by
      have hp0 : (p : ℝ) ≠ 0 := by linarith
      have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
      field_simp [hp0, hp1]
      ring
    rw [hident]
    exact mul_le_mul_of_nonneg_right hle_real (Real.log_natCast_nonneg p)
  have hlog_ge := log_factorial_ge n hn
  have herr := sum_log_div_p_mul_pred_le n
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith

lemma mertensM_ge {x : ℝ} (hx : 15 ≤ x) : Real.log x - 2 ≤ mertensM x := by
  let n := ⌊x⌋₊
  have hn15 : 15 ≤ n := Nat.le_floor hx
  have hMn : mertensM x = mertensM n := by simp [mertensM, n]
  rw [hMn]
  have h1 := mertensM_nat_ge n (by omega)
  have hxn : x ≤ (n : ℝ) + 1 := (Nat.lt_floor_add_one x).le
  have hdiff : Real.log x - Real.log n ≤ 1 / 15 := by
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hn15R : (15 : ℝ) ≤ n := by exact_mod_cast hn15
    rw [← Real.log_div (by linarith) hn_pos.ne']
    calc Real.log (x / n) ≤ x / n - 1 := Real.log_le_sub_one_of_pos (by positivity)
      _ ≤ ((n : ℝ) + 1) / n - 1 := by gcongr
      _ = 1 / n := by field_simp; ring
      _ ≤ 1 / 15 := by gcongr
  linarith

lemma mertensM_25_le : mertensM 25 ≤ 2.3 := by
  have hfl : ⌊(25 : ℝ)⌋₊ = 25 := by norm_num
  have hp25 : Nat.primesLE 25 = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by decide
  rw [mertensM, hfl, hp25]
  simp only [Finset.sum_insert (by decide : (2 : ℕ) ∉ ({3, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ)),
    Finset.sum_insert (by decide : (3 : ℕ) ∉ ({5, 7, 11, 13, 17, 19, 23} : Finset ℕ)),
    Finset.sum_insert (by decide : (5 : ℕ) ∉ ({7, 11, 13, 17, 19, 23} : Finset ℕ)),
    Finset.sum_insert (by decide : (7 : ℕ) ∉ ({11, 13, 17, 19, 23} : Finset ℕ)),
    Finset.sum_insert (by decide : (11 : ℕ) ∉ ({13, 17, 19, 23} : Finset ℕ)),
    Finset.sum_insert (by decide : (13 : ℕ) ∉ ({17, 19, 23} : Finset ℕ)),
    Finset.sum_insert (by decide : (17 : ℕ) ∉ ({19, 23} : Finset ℕ)),
    Finset.sum_insert (by decide : (19 : ℕ) ∉ ({23} : Finset ℕ)),
    Finset.sum_singleton, Nat.cast_ofNat]
  have hl2 := Real.log_two_lt_d9
  have hl3 := Real.log_three_lt_d9
  have hl5 := Real.log_five_lt_d9
  have hl7 : Real.log 7 ≤ 1.98 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7 / 8 by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num),
      show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at h
    push_cast at h; linarith
  have hl11 : Real.log 11 ≤ 2.48 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 11 / 8 by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num),
      show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at h
    push_cast at h; linarith
  have hl13 : Real.log 13 ≤ 2.62 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 13 / 16 by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at h
    push_cast at h; linarith
  have hl17 : Real.log 17 ≤ 2.87 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 17 / 16 by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at h
    push_cast at h; linarith
  have hl19 : Real.log 19 ≤ 2.99 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 19 / 16 by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at h
    push_cast at h; linarith
  have hl23 : Real.log 23 ≤ 3.24 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 23 / 16 by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at h
    push_cast at h; linarith
  linarith

lemma mertensM_le {x : ℝ} (hx : 2 ≤ x) : mertensM x ≤ Real.log 4 * Real.log x + 1 := by
  let c : ℕ → ℝ := fun n => if n.Prime then Real.log (n : ℝ) else 0
  have hc0 : c 0 = 0 := by simp [c, Nat.not_prime_zero]
  have hc1 : c 1 = 0 := by simp [c, Nat.not_prime_one]
  have hM : mertensM x = ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, (k : ℝ)⁻¹ * c k := by
    rw [mertensM, Nat.primesLE_eq_filter_Icc_zero, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [c]
    split_ifs <;> ring
  have hsum_c : ∀ t : ℝ, ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k = Chebyshev.theta t := by
    intro t
    rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  rw [hM, sum_mul_eq_sub_integral_mul₁ c hc0 hc1 x (f := fun t : ℝ => t⁻¹)
    (fun t ht => (differentiableAt_id.inv (by linarith [ht.1])))
    (by
      have hderiv_eq : Set.EqOn (deriv (fun t : ℝ => t⁻¹)) (fun t : ℝ => -(t ^ 2)⁻¹) (Set.Icc 2 x) :=
        fun t ht => by
          have := (hasDerivAt_inv (by linarith [ht.1] : t ≠ 0)).deriv
          simp [this]
      refine (ContinuousOn.integrableOn_Icc ?_).congr_fun hderiv_eq.symm measurableSet_Icc
      exact fun t ht => ((((continuous_pow 2).continuousAt).inv₀
        (pow_ne_zero 2 (by linarith [ht.1]))).neg).continuousWithinAt)]
  rw [← intervalIntegral.integral_of_le hx]
  have h1 : x⁻¹ * ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, c k ≤ Real.log 4 := by
    rw [hsum_c]
    have hth := Chebyshev.theta_le_log4_mul_x (x := x) (by linarith)
    calc x⁻¹ * Chebyshev.theta x ≤ x⁻¹ * (Real.log 4 * x) := by gcongr
      _ = Real.log 4 := by field_simp
  have h2 : -∫ t in (2 : ℝ)..x, deriv (fun u : ℝ => u⁻¹) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k ≤
      Real.log 4 * (Real.log x - Real.log 2) := by
    have heq : -∫ t in (2 : ℝ)..x, deriv (fun u : ℝ => u⁻¹) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k =
        ∫ t in (2 : ℝ)..x, Chebyshev.theta t / t ^ 2 := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hx] at ht
      have hdt : deriv (fun u : ℝ => u⁻¹) t = -(t ^ 2)⁻¹ := by
        have := (hasDerivAt_inv (by linarith [ht.1] : t ≠ 0)).deriv
        simp [this]
      rw [hdt, hsum_c]
      ring
    rw [heq]
    have h_int_th : IntervalIntegrable (fun t : ℝ => Chebyshev.theta t / t ^ 2)
        MeasureTheory.volume 2 x := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
      have : (fun t : ℝ => Chebyshev.theta t / t ^ 2) =
          (fun t : ℝ => (t ^ 2)⁻¹ * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) := by
        ext t; rw [hsum_c]; ring
      rw [this]
      refine integrableOn_mul_sum_Icc c (by norm_num) ?_
      exact ContinuousOn.integrableOn_Icc fun t ht =>
        (((continuous_pow 2).continuousAt).inv₀ (pow_ne_zero 2 (by linarith [ht.1]))).continuousWithinAt
    have h_int_ub : IntervalIntegrable (fun t : ℝ => Real.log 4 / t) MeasureTheory.volume 2 x := by
      refine ContinuousOn.intervalIntegrable fun t ht => ?_
      rw [Set.uIcc_of_le hx] at ht
      exact (continuousAt_const.div continuousAt_id (by dsimp; linarith [ht.1])).continuousWithinAt
    calc ∫ t in (2 : ℝ)..x, Chebyshev.theta t / t ^ 2
        ≤ ∫ t in (2 : ℝ)..x, Real.log 4 / t := by
          refine intervalIntegral.integral_mono_on hx h_int_th h_int_ub fun t ht => ?_
          have hth := Chebyshev.theta_le_log4_mul_x (x := t) (by linarith [ht.1])
          calc Chebyshev.theta t / t ^ 2 ≤ (Real.log 4 * t) / t ^ 2 := by gcongr
            _ = Real.log 4 / t := by field_simp
      _ = Real.log 4 * ∫ t in (2 : ℝ)..x, t⁻¹ := by
          simp_rw [div_eq_mul_inv, intervalIntegral.integral_const_mul]
      _ = Real.log 4 * (Real.log x - Real.log 2) := by
          rw [integral_inv_of_pos (by norm_num) (by linarith), Real.log_div (by linarith) (by norm_num)]
  have hconst : Real.log 4 - Real.log 4 * Real.log 2 ≤ 1 := by
    rw [Real.log_four_eq]
    have hl2_lo := Real.log_two_gt_d9
    have hl2_hi := Real.log_two_lt_d9
    nlinarith
  linarith

/-- Sign-positive Abel summation for sums over primes:
when `g t = f t / log t` is decreasing on `[a, b]` and `f b ≥ 0`,
`∑_{a < p ≤ b} f p / p ≥ ∫_a^b f t / (t * log t) dt - (f a / log a) * (M a - log a + 2)`. -/
lemma abel_prime_recip_ge {a b : ℝ} (ha : 15 ≤ a) (hab : a ≤ b)
    {f g' : ℝ → ℝ}
    (hf_deriv : ∀ t ∈ Set.Icc a b, HasDerivAt (fun u => f u / Real.log u) (g' t) t)
    (hg'_cont : ContinuousOn g' (Set.Icc a b))
    (hg'_nonpos : ∀ t ∈ Set.Icc a b, g' t ≤ 0)
    (hfb : 0 ≤ f b) :
    (∫ t in a..b, f t / (t * Real.log t)) -
      (f a / Real.log a) * (mertensM a - Real.log a + 2) ≤
      ∑ p ∈ Nat.primesLE ⌊b⌋₊ \ Nat.primesLE ⌊a⌋₊, f p / p := by
  let c : ℕ → ℝ := fun n => if n.Prime then Real.log (n : ℝ) / n else 0
  let g : ℝ → ℝ := fun u => f u / Real.log u
  have hsum_eq : ∑ p ∈ Nat.primesLE ⌊b⌋₊ \ Nat.primesLE ⌊a⌋₊, f p / p =
      ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, g k * c k := by
    have hset : Nat.primesLE ⌊b⌋₊ \ Nat.primesLE ⌊a⌋₊ = (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime := by
      ext p
      simp only [Finset.mem_sdiff, Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ioc]
      by_cases hp : p.Prime
      · simp only [hp, and_true]; omega
      · simp [hp]
    rw [hset, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [c, g]
    split_ifs with hkp
    · have hlog_ne : Real.log (k : ℝ) ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (by exact_mod_cast hkp.pos) (by exact_mod_cast hkp.ne_one)
      field_simp [hlog_ne]
    · simp
  have hsum_c : ∀ t : ℝ, ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k = mertensM t := by
    intro t
    rw [mertensM, Nat.primesLE_eq_filter_Icc_zero, Finset.sum_filter]
  have hderiv_eq : Set.EqOn (deriv g) g' (Set.Icc a b) := fun t ht => (hf_deriv t ht).deriv
  have habel := sum_mul_eq_sub_sub_integral_mul c (f := g) (by linarith) hab
    (fun t ht => (hf_deriv t ht).differentiableAt)
    (hg'_cont.integrableOn_Icc.congr_fun hderiv_eq.symm measurableSet_Icc)
  rw [hsum_eq, habel, ← intervalIntegral.integral_of_le hab]
  simp_rw [hsum_c]
  have hgb_nonneg : 0 ≤ g b := div_nonneg hfb (Real.log_nonneg (by linarith))
  have hM_b : Real.log b - 2 ≤ mertensM b := mertensM_ge (by linarith)
  have h_int_ge : ∫ t in a..b, deriv g t * (Real.log t - 2) ≥
      ∫ t in a..b, deriv g t * mertensM t := by
    refine intervalIntegral.integral_mono_on hab ?_ ?_ fun t ht => ?_
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
      have h1 : MeasureTheory.IntegrableOn
          (fun t => g' t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) (Set.Icc a b) :=
        integrableOn_mul_sum_Icc c (by linarith) hg'_cont.integrableOn_Icc
      refine h1.congr_fun (fun t ht => ?_) measurableSet_Icc
      dsimp only
      rw [hderiv_eq ht, hsum_c]
    · refine ContinuousOn.intervalIntegrable fun t ht => ?_
      rw [Set.uIcc_of_le hab] at ht
      have hcont_g' : ContinuousWithinAt (deriv g) (Set.Icc a b) t :=
        (hg'_cont t ht).congr (fun s hs => hderiv_eq hs) (hderiv_eq ht)
      exact (hcont_g'.mul (((Real.continuousAt_log (by linarith [ht.1])).sub
        continuousAt_const).continuousWithinAt)).mono (by rw [Set.uIcc_of_le hab])
    · rw [hderiv_eq ht]
      exact mul_le_mul_of_nonpos_left (mertensM_ge (by linarith [ht.1])) (hg'_nonpos t ht)
  have hibp : ∫ t in a..b, g' t * (Real.log t - 2) =
      g b * (Real.log b - 2) - g a * (Real.log a - 2) - ∫ t in a..b, g t * t⁻¹ := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := g) (u' := g') (v := fun t => Real.log t - 2) (v' := fun t => t⁻¹)
      (fun t ht => by rw [Set.uIcc_of_le hab] at ht; exact hf_deriv t ht)
      (fun t ht => by
        rw [Set.uIcc_of_le hab] at ht
        exact (Real.hasDerivAt_log (by linarith [ht.1])).sub_const 2)
      (by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
        exact hg'_cont.integrableOn_Icc)
      (ContinuousOn.intervalIntegrable fun t ht => by
        rw [Set.uIcc_of_le hab] at ht
        exact (continuousAt_id.inv₀ (by dsimp; linarith [ht.1])).continuousWithinAt)
    linarith
  have h_congr1 : ∫ t in a..b, deriv g t * (Real.log t - 2) =
      ∫ t in a..b, g' t * (Real.log t - 2) :=
    intervalIntegral.integral_congr fun t ht => by
      rw [Set.uIcc_of_le hab] at ht; rw [hderiv_eq ht]
  have h_congr2 : ∫ t in a..b, g t * t⁻¹ = ∫ t in a..b, f t / (t * Real.log t) :=
    intervalIntegral.integral_congr fun t _ => by
      simp only [g]; ring
  rw [h_congr1, hibp, h_congr2] at h_int_ge
  have hgb_mul : g b * (Real.log b - 2) ≤ g b * mertensM b :=
    mul_le_mul_of_nonneg_left hM_b hgb_nonneg
  dsimp only [g] at hgb_mul h_int_ge ⊢
  linarith

/- Section 4: Harmonic sum `G(x)` lower bounds and main-regime theorem -/

/-- Convenience abbreviation for iterated natural logarithm. -/
noncomputable def iterLog (i : ℕ) (x : ℝ) : ℝ := Real.log^[i] x

lemma iterLog_zero (x : ℝ) : iterLog 0 x = x := rfl

lemma iterLog_succ (i : ℕ) (x : ℝ) : iterLog (i + 1) x = Real.log (iterLog i x) :=
  Function.iterate_succ_apply' Real.log i x

lemma iterLog_succ_inner (i : ℕ) (x : ℝ) : iterLog (i + 1) x = iterLog i (Real.log x) :=
  Function.iterate_succ_apply Real.log i x

lemma iterLog_add (i j : ℕ) (x : ℝ) : iterLog i (iterLog j x) = iterLog (i + j) x :=
  (Function.iterate_add_apply Real.log i j x).symm

lemma bernoulli_sub {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    1 - (n : ℝ) * x ≤ (1 - x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    have hmul : (1 - (n : ℝ) * x) * (1 - x) ≤ (1 - x) ^ n * (1 - x) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    nlinarith [sq_nonneg x, mul_nonneg (Nat.cast_nonneg n) (sq_nonneg x)]

lemma continuousAt_sum_finset {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (t : ℝ)
    (hf : ∀ i ∈ s, ContinuousAt (f i) t) :
    ContinuousAt (fun u => ∑ i ∈ s, f i u) t := by
  classical
  induction s using Finset.induction with
  | empty => simpa using continuousAt_const
  | @insert a s ha ih =>
    have heq : (fun u => ∑ i ∈ insert a s, f i u) = fun u => f a u + ∑ i ∈ s, f i u := by
      ext u; exact Finset.sum_insert ha
    rw [heq]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma continuousAt_prod_finset {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (t : ℝ)
    (hf : ∀ i ∈ s, ContinuousAt (f i) t) :
    ContinuousAt (fun u => ∏ i ∈ s, f i u) t := by
  classical
  induction s using Finset.induction with
  | empty => simpa using continuousAt_const
  | @insert a s ha ih =>
    have heq : (fun u => ∏ i ∈ insert a s, f i u) = fun u => f a u * ∏ i ∈ s, f i u := by
      ext u; exact Finset.prod_insert ha
    rw [heq]
    exact (hf a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma iterLog_mono {n : ℕ} {x y : ℝ} (hx : ∀ j ≤ n, 1 ≤ iterLog j x) (hxy : x ≤ y) :
    ∀ j ≤ n, iterLog j x ≤ iterLog j y := by
  intro j hj
  induction j with
  | zero => exact hxy
  | succ j ih =>
    rw [iterLog_succ, iterLog_succ]
    have hx_j : 1 ≤ iterLog j x := hx j (by omega)
    exact Real.log_le_log (by linarith) (ih (by omega))

lemma iterLog_antitone {n : ℕ} {x : ℝ} (hx : ∀ j ≤ n, 1 ≤ iterLog j x) :
    ∀ {i j}, i ≤ j → j ≤ n → iterLog j x ≤ iterLog i x := by
  intro i j hij hjn
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    rw [iterLog_succ]
    have hj_pos : 0 < iterLog j x := by linarith [hx j (by omega)]
    exact (Real.log_le_sub_one_of_pos hj_pos).trans (by linarith [ih (by omega)])

lemma iterLog_exp_step {n : ℕ} {x : ℝ} (hx : ∀ j ≤ n, 1 ≤ iterLog j x) {i : ℕ} (hi : i < n) :
    Real.exp (iterLog (i + 1) x) = iterLog i x := by
  rw [iterLog_succ]
  exact Real.exp_log (by linarith [hx i (by omega)])

lemma iterLog_eq_iterExp {n : ℕ} {x : ℝ} (hx : ∀ j ≤ n, 1 ≤ iterLog j x) {j : ℕ} (hj : j ≤ n) :
    iterLog j x = Real.exp^[n - j] (iterLog n x) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = j + d := ⟨n - j, (Nat.add_sub_cancel' hj).symm⟩
  rw [Nat.add_sub_cancel_left]
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Function.iterate_succ_apply]
    have hstep := iterLog_exp_step hx (i := j + d) (by omega)
    rw [← hstep] at ih
    exact ih (fun i hi => hx i (by omega)) (by omega)

lemma iterExp_mono (m : ℕ) : Monotone (Real.exp^[m]) := by
  induction m with
  | zero => exact monotone_id
  | succ m ih =>
    intro x y hxy
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact Real.exp_le_exp.mpr (ih hxy)

lemma iterExp_ge_self (m : ℕ) (y : ℝ) : y ≤ Real.exp^[m] y := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (by linarith [Real.add_one_le_exp (Real.exp^[m] y)])

lemma iterLog_iterExp (m : ℕ) (y : ℝ) :
    ∀ j ≤ m, iterLog j (Real.exp^[m] y) = Real.exp^[m - j] y := by
  intro j hj
  induction j with
  | zero => simp [iterLog_zero]
  | succ j ih =>
    rw [iterLog_succ, ih (by omega)]
    have hsub : m - j = (m - (j + 1)) + 1 := by omega
    rw [hsub, Function.iterate_succ_apply', Real.log_exp]

lemma exp_399_gt : (54 : ℝ) < Real.exp 3.99 := by
  have he := Real.exp_one_gt_d9
  have h1 : (2.71828 : ℝ) ^ 4 ≤ (Real.exp 1) ^ 4 := by gcongr; linarith
  rw [← Real.exp_nat_mul] at h1
  have h2 : Real.exp 0.01 ≤ 1.011 := by
    have h := Real.exp_bound (x := (0.01 : ℝ)) (n := 3) (by norm_num) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
    norm_num at h
    linarith [(abs_le.mp h).2]
  have hmul : Real.exp 3.99 * Real.exp 0.01 = Real.exp 4 := by
    rw [← Real.exp_add]; norm_num
  have h4 : (54.59 : ℝ) < Real.exp 4 := by norm_num at h1 ⊢; linarith
  nlinarith [Real.exp_pos 3.99]

lemma iterExp_add_one_ge {m : ℕ} (hm : 2 ≤ m) {y : ℝ} (hy : 3.99 ≤ y) :
    1000 * Real.exp y * Real.exp^[m] y ≤ Real.exp^[m] (y + 1) := by
  induction m, hm using Nat.le_induction with
  | base =>
    simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq]
    have hexp_y : 54 < Real.exp y := exp_399_gt.trans_le (Real.exp_le_exp.mpr hy)
    have hdiff : Real.exp (y + 1) - Real.exp y ≥ 1.7 * Real.exp y := by
      rw [Real.exp_add]
      nlinarith [Real.exp_one_gt_d9]
    have hprod : Real.exp (Real.exp (y + 1)) =
        Real.exp (Real.exp (y + 1) - Real.exp y) * Real.exp (Real.exp y) := by
      rw [← Real.exp_add, sub_add_cancel]
    rw [hprod]
    have hfactor : 1000 * Real.exp y ≤ Real.exp (Real.exp (y + 1) - Real.exp y) := by
      calc 1000 * Real.exp y
          ≤ Real.exp (0.7 * 54) * Real.exp y := by
            gcongr
            have h37 : (1000 : ℝ) ≤ (2 : ℝ) ^ 10 := by norm_num
            calc (1000 : ℝ) ≤ (2 : ℝ) ^ 10 := h37
              _ ≤ (Real.exp 1) ^ 10 := by gcongr; linarith [Real.exp_one_gt_two]
              _ = Real.exp 10 := by rw [← Real.exp_nat_mul]; norm_num
              _ ≤ Real.exp (0.7 * 54) := Real.exp_le_exp.mpr (by norm_num)
        _ ≤ Real.exp (0.7 * Real.exp y) * Real.exp (Real.exp y) := by
            exact mul_le_mul (Real.exp_le_exp.mpr (by linarith))
              (Real.exp_le_exp.mpr (by linarith [Real.add_one_le_exp y]))
              (Real.exp_pos y).le (Real.exp_pos _).le
        _ = Real.exp (1.7 * Real.exp y) := by rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp (Real.exp (y + 1) - Real.exp y) := Real.exp_le_exp.mpr hdiff
    exact mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le
  | succ m hm ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hA : 2 ≤ Real.exp^[m] y := by linarith [iterExp_ge_self m y]
    have hK : 1000 * Real.exp y ≥ 54000 := by
      linarith [exp_399_gt.trans_le (Real.exp_le_exp.mpr hy)]
    have hdiff : Real.exp^[m] (y + 1) - Real.exp^[m] y ≥ 1000 * Real.exp y := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1000 * Real.exp y - 1)
        (by linarith : 0 ≤ Real.exp^[m] y - 2)]
    have hprod : Real.exp (Real.exp^[m] (y + 1)) =
        Real.exp (Real.exp^[m] (y + 1) - Real.exp^[m] y) * Real.exp (Real.exp^[m] y) := by
      rw [← Real.exp_add, sub_add_cancel]
    rw [hprod]
    have hfac : 1000 * Real.exp y ≤ Real.exp (Real.exp^[m] (y + 1) - Real.exp^[m] y) := by
      calc 1000 * Real.exp y ≤ Real.exp (1000 * Real.exp y) := by
            linarith [Real.add_one_le_exp (1000 * Real.exp y)]
        _ ≤ Real.exp (Real.exp^[m] (y + 1) - Real.exp^[m] y) := Real.exp_le_exp.mpr hdiff
    exact mul_le_mul_of_nonneg_right hfac (Real.exp_pos _).le

lemma hasDerivAt_iterLog (n : ℕ) {x : ℝ} (hx : ∀ j < n, 1 < iterLog j x) :
    HasDerivAt (iterLog n) (∏ j ∈ Finset.range n, (iterLog j x)⁻¹) x := by
  induction n with
  | zero =>
    rw [Finset.range_zero, Finset.prod_empty]
    change HasDerivAt id 1 x
    exact hasDerivAt_id x
  | succ n ih =>
    have hprev := ih (fun j hj => hx j (by omega))
    have hne : iterLog n x ≠ 0 := by linarith [hx n (Nat.lt_succ_self n)]
    have hlog := hprev.log hne
    have hfun : (fun t => Real.log (iterLog n t)) = iterLog (n + 1) := by
      ext t; exact (iterLog_succ n t).symm
    rw [hfun] at hlog
    refine hlog.congr_deriv ?_
    rw [Finset.prod_range_succ, div_eq_mul_inv]

/-- `phi m v = ∏ j ∈ range (m + 1), iterLog j v = v * log v * ... * log^[m] v`. -/
noncomputable def phi (m : ℕ) (v : ℝ) : ℝ :=
  ∏ j ∈ Finset.range (m + 1), iterLog j v

/-- `prodIterLog m v = ∏ j ∈ Icc 1 m, iterLog j v`. -/
noncomputable def prodIterLog (m : ℕ) (v : ℝ) : ℝ :=
  ∏ j ∈ Finset.Icc 1 m, iterLog j v

lemma phi_eq_mul_prodIterLog (m : ℕ) (v : ℝ) : phi m v = v * prodIterLog m v := by
  unfold phi prodIterLog
  have hsplit : Finset.range (m + 1) = insert 0 (Finset.Icc 1 m) := by
    ext j; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hsplit, Finset.prod_insert (by simp), iterLog_zero]

lemma hasDerivAt_phi (m : ℕ) {v : ℝ} (hv : ∀ j ≤ m, 2 ≤ iterLog j v) :
    HasDerivAt (phi m) (∑ r ∈ Finset.range (m + 1), ∏ j ∈ Finset.Icc (r + 1) m, iterLog j v) v := by
  induction m with
  | zero =>
    have h0 : phi 0 = id := by ext t; simp [phi, iterLog_zero]
    rw [h0]
    simpa using hasDerivAt_id v
  | succ m ih =>
    have hphi_eq : phi (m + 1) = fun t => phi m t * iterLog (m + 1) t := by
      ext t; unfold phi; rw [Finset.prod_range_succ]
    rw [hphi_eq]
    have hd1 := ih (fun j hj => hv j (by omega))
    have hd2 := hasDerivAt_iterLog (m + 1) (fun j hj => by linarith [hv j (by omega)])
    refine (hd1.mul hd2).congr_deriv ?_
    have hprod_inv : phi m v * ∏ j ∈ Finset.range (m + 1), (iterLog j v)⁻¹ = 1 := by
      unfold phi
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun j hj => ?_
      have hjv : iterLog j v ≠ 0 := by linarith [hv j (by simp only [Finset.mem_range] at hj; omega)]
      exact mul_inv_cancel₀ hjv
    rw [hprod_inv, Finset.sum_mul]
    rw [Finset.sum_range_succ (f := fun r => ∏ j ∈ Finset.Icc (r + 1) (m + 1), iterLog j v) (m + 1)]
    congr 1
    · refine Finset.sum_congr rfl fun r hr => ?_
      have hrle : r + 1 ≤ m + 1 := by simp only [Finset.mem_range] at hr; omega
      rw [Finset.prod_Icc_succ_top hrle]
    · have hemp : Finset.Icc (m + 1 + 1) (m + 1) = ∅ := by
        ext j; simp only [Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
      rw [hemp, Finset.prod_empty]

lemma phi_deriv_le {m : ℕ} (hm : 1 ≤ m) {v : ℝ} (hv : ∀ j ≤ m, 2 ≤ iterLog j v) :
    ∑ r ∈ Finset.range (m + 1), ∏ j ∈ Finset.Icc (r + 1) m, iterLog j v ≤
      (1 + 2 / iterLog 1 v) * prodIterLog m v := by
  have hsplit : Finset.range (m + 1) = insert 0 (Finset.Icc 1 m) := by
    ext r; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hsplit, Finset.sum_insert (by simp)]
  have h0 : ∏ j ∈ Finset.Icc (0 + 1) m, iterLog j v = prodIterLog m v := rfl
  rw [h0, add_mul, one_mul]
  gcongr
  have hP_pos : 0 < prodIterLog m v :=
    Finset.prod_pos fun j hj => by
      linarith [hv j (Finset.mem_Icc.mp hj).2]
  have hterm : ∀ r ∈ Finset.Icc 1 m,
      ∏ j ∈ Finset.Icc (r + 1) m, iterLog j v ≤
        prodIterLog m v * ((iterLog 1 v)⁻¹ * (1 / 2 : ℝ) ^ (r - 1)) := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hrm : r ≤ m := (Finset.mem_Icc.mp hr).2
    have hfac : prodIterLog m v =
        (∏ j ∈ Finset.Icc 1 r, iterLog j v) * ∏ j ∈ Finset.Icc (r + 1) m, iterLog j v := by
      unfold prodIterLog
      have hunion : Finset.Icc 1 m = Finset.Icc 1 r ∪ Finset.Icc (r + 1) m := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      have hdisj : Disjoint (Finset.Icc 1 r) (Finset.Icc (r + 1) m) := by
        rw [Finset.disjoint_left]
        intro j hj1 hj2
        simp only [Finset.mem_Icc] at hj1 hj2; omega
      rw [hunion, Finset.prod_union hdisj]
    have hL1_pos : 0 < iterLog 1 v := by linarith [hv 1 (by omega)]
    have hprefix_ge : iterLog 1 v * (2 : ℝ) ^ (r - 1) ≤ ∏ j ∈ Finset.Icc 1 r, iterLog j v := by
      have hsplit2 : Finset.Icc 1 r = insert 1 (Finset.Icc 2 r) := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsplit2, Finset.prod_insert (by simp)]
      have h2 : (2 : ℝ) ^ (r - 1) ≤ ∏ j ∈ Finset.Icc 2 r, iterLog j v := by
        have h := Finset.prod_le_prod (s := Finset.Icc 2 r) (f := fun _ => (2 : ℝ))
          (g := fun j => iterLog j v) (fun _ _ => by norm_num)
          (fun j hj => hv j ((Finset.mem_Icc.mp hj).2.trans hrm))
        simpa [Finset.prod_const, Nat.card_Icc] using h
      exact mul_le_mul_of_nonneg_left h2 hL1_pos.le
    have htail_nonneg : 0 ≤ ∏ j ∈ Finset.Icc (r + 1) m, iterLog j v :=
      Finset.prod_nonneg fun j hj => by linarith [hv j (Finset.mem_Icc.mp hj).2]
    have hmul : (iterLog 1 v * (2 : ℝ) ^ (r - 1)) * ∏ j ∈ Finset.Icc (r + 1) m, iterLog j v ≤
        prodIterLog m v := by
      rw [hfac]
      exact mul_le_mul_of_nonneg_right hprefix_ge htail_nonneg
    have hpos_d : 0 < iterLog 1 v * (2 : ℝ) ^ (r - 1) := by positivity
    calc ∏ j ∈ Finset.Icc (r + 1) m, iterLog j v
        ≤ prodIterLog m v / (iterLog 1 v * (2 : ℝ) ^ (r - 1)) :=
          (le_div_iff₀' hpos_d).mpr hmul
      _ = prodIterLog m v * ((iterLog 1 v)⁻¹ * (1 / 2 : ℝ) ^ (r - 1)) := by
          rw [one_div, inv_pow, div_eq_mul_inv, mul_inv]
  have hgeom : ∑ r ∈ Finset.Icc 1 m, (1 / 2 : ℝ) ^ (r - 1) ≤ 2 := by
    have hshift : ∑ r ∈ Finset.Icc 1 m, (1 / 2 : ℝ) ^ (r - 1) =
        ∑ i ∈ Finset.range m, (1 / 2 : ℝ) ^ i := by
      refine Finset.sum_nbij (· - 1) ?_ ?_ ?_ ?_
      · intro r hr; simp only [Finset.mem_Icc, Finset.mem_range] at hr ⊢; omega
      · intro a ha b hb h; simp only [Finset.mem_coe, Finset.mem_Icc] at ha hb; dsimp only at h; omega
      · intro i hi; simp only [Finset.mem_coe, Finset.mem_range] at hi
        exact ⟨i + 1, Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), by dsimp only; omega⟩
      · intro r _; rfl
    rw [hshift, geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
    have hpos : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ m := by positivity
    have hrew : ((1 / 2 : ℝ) ^ m - 1) / (1 / 2 - 1) = 2 - 2 * (1 / 2 : ℝ) ^ m := by ring
    linarith
  calc ∑ r ∈ Finset.Icc 1 m, ∏ j ∈ Finset.Icc (r + 1) m, iterLog j v
      ≤ ∑ r ∈ Finset.Icc 1 m, prodIterLog m v * ((iterLog 1 v)⁻¹ * (1 / 2 : ℝ) ^ (r - 1)) :=
        Finset.sum_le_sum hterm
    _ = prodIterLog m v * (iterLog 1 v)⁻¹ * ∑ r ∈ Finset.Icc 1 m, (1 / 2 : ℝ) ^ (r - 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => by ring
    _ ≤ prodIterLog m v * (iterLog 1 v)⁻¹ * 2 :=
        mul_le_mul_of_nonneg_left hgeom (mul_nonneg hP_pos.le (inv_nonneg.mpr (by linarith [hv 1 (by omega)])))
    _ = 2 / iterLog 1 v * prodIterLog m v := by ring

lemma hasDerivAt_prodIterLog (m : ℕ) {v : ℝ} (hv : ∀ j ≤ m, 2 ≤ iterLog j v) :
    HasDerivAt (prodIterLog m)
      (prodIterLog m v * ∑ r ∈ Finset.Icc 1 m, (∏ j ∈ Finset.range (r + 1), (iterLog j v)⁻¹)) v := by
  induction m with
  | zero =>
    have h0 : prodIterLog 0 = fun _ => 1 := by
      ext t; simp [prodIterLog]
    rw [h0]
    simpa using hasDerivAt_const v (1 : ℝ)
  | succ m ih =>
    have hpeq : prodIterLog (m + 1) = fun t => prodIterLog m t * iterLog (m + 1) t := by
      ext t; unfold prodIterLog; rw [Finset.prod_Icc_succ_top (by omega)]
    rw [hpeq]
    have hd1 := ih (fun j hj => hv j (by omega))
    have hd2 := hasDerivAt_iterLog (m + 1) (fun j hj => by linarith [hv j (by omega)])
    refine (hd1.mul hd2).congr_deriv ?_
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, Finset.prod_range_succ (n := m + 1)]
    dsimp only
    have hne : iterLog (m + 1) v ≠ 0 := by linarith [hv (m + 1) le_rfl]
    field_simp [hne]

lemma prodIterLog_deriv_le (m : ℕ) {v : ℝ} (hv : ∀ j ≤ m, 2 ≤ iterLog j v) :
    ∑ r ∈ Finset.Icc 1 m, (∏ j ∈ Finset.range (r + 1), (iterLog j v)⁻¹) ≤ 2 / v := by
  have hv0 : 0 < v := by linarith [hv 0 (Nat.zero_le m), iterLog_zero v]
  have hterm : ∀ r ∈ Finset.Icc 1 m,
      ∏ j ∈ Finset.range (r + 1), (iterLog j v)⁻¹ ≤ v⁻¹ * (1 / 2 : ℝ) ^ r := by
    intro r hr
    have hrm : r ≤ m := (Finset.mem_Icc.mp hr).2
    have hsplit : Finset.range (r + 1) = insert 0 (Finset.Icc 1 r) := by
      ext j; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hsplit, Finset.prod_insert (by simp), iterLog_zero]
    gcongr
    have hprod := Finset.prod_le_prod (s := Finset.Icc 1 r)
      (f := fun j => (iterLog j v)⁻¹) (g := fun _ => (1 / 2 : ℝ))
      (fun j hj => inv_nonneg.mpr (by linarith [hv j ((Finset.mem_Icc.mp hj).2.trans hrm)]))
      (fun j hj => by
        rw [one_div]
        exact inv_anti₀ (by norm_num) (hv j ((Finset.mem_Icc.mp hj).2.trans hrm)))
    simpa [Finset.prod_const, Nat.card_Icc] using hprod
  have hgeom : ∑ r ∈ Finset.Icc 1 m, (1 / 2 : ℝ) ^ r ≤ 1 := by
    have hshift : ∑ r ∈ Finset.Icc 1 m, (1 / 2 : ℝ) ^ r =
        (1 / 2 : ℝ) * ∑ i ∈ Finset.range m, (1 / 2 : ℝ) ^ i := by
      rw [Finset.mul_sum]
      refine Finset.sum_nbij (· - 1) ?_ ?_ ?_ ?_
      · intro r hr; simp only [Finset.mem_Icc, Finset.mem_range] at hr ⊢; omega
      · intro a ha b hb h; simp only [Finset.mem_coe, Finset.mem_Icc] at ha hb; dsimp only at h; omega
      · intro i hi; simp only [Finset.mem_coe, Finset.mem_range] at hi
        exact ⟨i + 1, Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), by dsimp only; omega⟩
      · intro r hr
        have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
        rw [← pow_succ', Nat.sub_add_cancel hr1]
    rw [hshift, geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
    have hpos : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ m := by positivity
    have hrew : (1 / 2 : ℝ) * (((1 / 2 : ℝ) ^ m - 1) / (1 / 2 - 1)) = 1 - (1 / 2 : ℝ) ^ m := by ring
    linarith
  calc ∑ r ∈ Finset.Icc 1 m, ∏ j ∈ Finset.range (r + 1), (iterLog j v)⁻¹
      ≤ ∑ r ∈ Finset.Icc 1 m, v⁻¹ * (1 / 2 : ℝ) ^ r := Finset.sum_le_sum hterm
    _ = v⁻¹ * ∑ r ∈ Finset.Icc 1 m, (1 / 2 : ℝ) ^ r := (Finset.mul_sum _ _ _).symm
    _ ≤ v⁻¹ * 1 := by gcongr
    _ ≤ 2 / v := by rw [div_eq_mul_inv]; linarith [inv_pos.mpr hv0]

/-- Harmonic sum of prime chains above `25` with all primes `≤ x`. -/
noncomputable def G_above (x : ℝ) : ℝ :=
  ∑ S ∈ (Nat.primesLE ⌊x⌋₊).powerset.filter IsPrimeChain, (1 : ℝ) / ∏ p ∈ S, (p : ℝ)

/-- Harmonic sum of valid elements `(a, S)` with `a ∈ A0` and all primes in `S` at most `x`. -/
noncomputable def G_total (x : ℝ) : ℝ := (25 / 12 : ℝ) * G_above x

lemma G_above_mono {x y : ℝ} (hxy : x ≤ y) : G_above x ≤ G_above y := by
  unfold G_above
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun S _ _ => by positivity)
  exact Finset.filter_subset_filter _ (Finset.powerset_mono.mpr (Nat.primesLE_mono (Nat.floor_mono hxy)))

lemma G_total_mono {x y : ℝ} (hxy : x ≤ y) : G_total x ≤ G_total y :=
  mul_le_mul_of_nonneg_left (G_above_mono hxy) (by norm_num)

lemma G_above_ge_one (x : ℝ) : 1 ≤ G_above x := by
  unfold G_above
  have hmem : (∅ : Finset ℕ) ∈ (Nat.primesLE ⌊x⌋₊).powerset.filter IsPrimeChain :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), isPrimeChain_empty⟩
  have hle := Finset.single_le_sum (f := fun S : Finset ℕ => (1 : ℝ) / ∏ p ∈ S, (p : ℝ))
    (fun _ _ => by positivity) hmem
  simpa using hle

lemma six_pow_lt_of_le_log_div_two {q p : ℕ} (hq : 2 ≤ q) (hp : 2 ≤ p)
    (hle : (q : ℝ) ≤ Real.log p / 2) : chainThresh q < p := by
  have h1 : chainThresh q < 6 ^ q := chainThresh_lt_six_pow hq
  have h2 : ((6 ^ q : ℕ) : ℝ) < (p : ℝ) := by
    have hlog6 : Real.log 6 < 2 := by
      have : Real.log 6 = Real.log 2 + Real.log 3 := by
        rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      linarith [Real.log_two_lt_d9, Real.log_three_lt_d9]
    have hlogp_pos : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < p by omega))
    have hexp : (q : ℝ) * Real.log 6 < Real.log (p : ℝ) := by
      calc (q : ℝ) * Real.log 6 ≤ (Real.log (p : ℝ) / 2) * Real.log 6 := by
            exact mul_le_mul_of_nonneg_right hle (Real.log_nonneg (by norm_num))
        _ < (Real.log (p : ℝ) / 2) * 2 := by nlinarith
        _ = Real.log (p : ℝ) := by ring
    calc ((6 ^ q : ℕ) : ℝ) = (6 : ℝ) ^ q := by push_cast; rfl
      _ = Real.exp ((q : ℝ) * Real.log 6) := by
          rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), mul_comm]
      _ < Real.exp (Real.log (p : ℝ)) := Real.exp_lt_exp.mpr hexp
      _ = (p : ℝ) := Real.exp_log (by exact_mod_cast (show 0 < p by omega))
  have h2nat : 6 ^ q < p := by exact_mod_cast h2
  exact h1.trans h2nat

set_option maxHeartbeats 800000 in
lemma G_above_recursion {x : ℝ} (_hx : 25 ≤ x) :
    1 + ∑ p ∈ Nat.primesLE ⌊x⌋₊ \ Nat.primesLE 25, G_above (Real.log p / 2) / p ≤ G_above x := by
  let P := Nat.primesLE ⌊x⌋₊ \ Nat.primesLE 25
  let F (p : ℕ) : Finset (Finset ℕ) := (Nat.primesLE ⌊Real.log p / 2⌋₊).powerset.filter IsPrimeChain
  let D : Finset (Σ p : ℕ, Finset ℕ) := P.sigma F
  let ins : (Σ _ : ℕ, Finset ℕ) → Finset ℕ := fun u => insert u.1 u.2
  have hins_mem : ∀ u ∈ D, ins u ∈ ((Nat.primesLE ⌊x⌋₊).powerset.filter IsPrimeChain).erase ∅ := by
    intro ⟨p, S⟩ hu
    rw [Finset.mem_sigma] at hu
    have hpP : p ∈ P := hu.1
    have hp_le : p ∈ Nat.primesLE ⌊x⌋₊ := (Finset.mem_sdiff.mp hpP).1
    have hp_pr : p.Prime := Nat.prime_of_mem_primesLE hp_le
    have hp_25 : 25 < p := by
      by_contra h
      exact (Finset.mem_sdiff.mp hpP).2 (Nat.mem_primesLE.mpr ⟨by omega, hp_pr⟩)
    have hS_sub : S ⊆ Nat.primesLE ⌊Real.log p / 2⌋₊ :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hu.2).1
    have hS_ch : IsPrimeChain S := (Finset.mem_filter.mp hu.2).2
    have hq_lt_p : ∀ q ∈ S, chainThresh q < p ∧ q < p := by
      intro q hq
      have hq_le : q ≤ ⌊Real.log p / 2⌋₊ := Nat.le_of_mem_primesLE (hS_sub hq)
      have hq_25 : 25 < q := (hS_ch.1 q hq).2
      have hq_real : (q : ℝ) ≤ Real.log p / 2 := by
        calc (q : ℝ) ≤ (⌊Real.log p / 2⌋₊ : ℝ) := by exact_mod_cast hq_le
          _ ≤ Real.log p / 2 := Nat.floor_le (by
              have : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
              linarith)
      have hT := six_pow_lt_of_le_log_div_two (by omega) hp_pr.two_le hq_real
      have hq_lt_T : q < chainThresh q := by
        have hq_mem : q ∈ (Finset.Ioc 25 q).filter Nat.Prime :=
          Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hq_25, le_rfl⟩, (hS_ch.1 q hq).1⟩
        have hprod : q + 1 ≤ ∏ r ∈ (Finset.Ioc 25 q).filter Nat.Prime, (r + 1) :=
          Finset.single_le_prod' (f := fun r => r + 1) (fun r _ => Nat.succ_le_succ (Nat.zero_le r)) hq_mem
        unfold chainThresh; omega
      exact ⟨hT, hq_lt_T.trans hT⟩
    have hins_sub : insert p S ⊆ Nat.primesLE ⌊x⌋₊ := by
      intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hrS
      · exact hp_le
      · exact Nat.mem_primesLE.mpr ⟨(hq_lt_p r hrS).2.le.trans (Nat.le_of_mem_primesLE hp_le),
          (hS_ch.1 r hrS).1⟩
    have hins_ch : IsPrimeChain (insert p S) := by
      refine ⟨fun r hr => ?_, fun q hq r hr hqr => ?_⟩
      · rcases Finset.mem_insert.mp hr with rfl | hrS
        · exact ⟨hp_pr, hp_25⟩
        · exact hS_ch.1 r hrS
      · rcases Finset.mem_insert.mp hq with rfl | hqS <;> rcases Finset.mem_insert.mp hr with rfl | hrS
        · omega
        · have := (hq_lt_p r hrS).2; omega
        · exact (hq_lt_p q hqS).1
        · exact hS_ch.2 q hqS r hrS hqr
    exact Finset.mem_erase.mpr ⟨Finset.insert_ne_empty p S,
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hins_sub, hins_ch⟩⟩
  have hins_inj : Set.InjOn ins (D : Set (Σ _ : ℕ, Finset ℕ)) := by
    intro ⟨p₁, S₁⟩ h1 ⟨p₂, S₂⟩ h2 hEq
    dsimp only [ins] at hEq
    have hlt1 : ∀ q ∈ S₁, q < p₁ := by
      intro q hq
      have hu := Finset.mem_sigma.mp h1
      have hq_le : q ≤ ⌊Real.log p₁ / 2⌋₊ :=
        Nat.le_of_mem_primesLE ((Finset.mem_powerset.mp (Finset.mem_filter.mp hu.2).1) hq)
      have hp1_pr : p₁.Prime := Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hu.1).1
      have hq25 : 25 < q := ((Finset.mem_filter.mp hu.2).2.1 q hq).2
      have hqR : (q : ℝ) ≤ Real.log p₁ / 2 := (Nat.cast_le.mpr hq_le).trans
        (Nat.floor_le (by linarith [Real.log_natCast_nonneg p₁]))
      have hT := six_pow_lt_of_le_log_div_two (by omega) hp1_pr.two_le hqR
      have hqT : q < chainThresh q := by
        have hm : q ∈ (Finset.Ioc 25 q).filter Nat.Prime :=
          Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hq25, le_rfl⟩, ((Finset.mem_filter.mp hu.2).2.1 q hq).1⟩
        have := Finset.single_le_prod' (f := fun r => r + 1) (fun r _ => Nat.succ_le_succ (Nat.zero_le r)) hm
        unfold chainThresh; omega
      exact hqT.trans hT
    have hlt2 : ∀ q ∈ S₂, q < p₂ := by
      intro q hq
      have hu := Finset.mem_sigma.mp h2
      have hq_le : q ≤ ⌊Real.log p₂ / 2⌋₊ :=
        Nat.le_of_mem_primesLE ((Finset.mem_powerset.mp (Finset.mem_filter.mp hu.2).1) hq)
      have hp2_pr : p₂.Prime := Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hu.1).1
      have hq25 : 25 < q := ((Finset.mem_filter.mp hu.2).2.1 q hq).2
      have hqR : (q : ℝ) ≤ Real.log p₂ / 2 := (Nat.cast_le.mpr hq_le).trans
        (Nat.floor_le (by linarith [Real.log_natCast_nonneg p₂]))
      have hT := six_pow_lt_of_le_log_div_two (by omega) hp2_pr.two_le hqR
      have hqT : q < chainThresh q := by
        have hm : q ∈ (Finset.Ioc 25 q).filter Nat.Prime :=
          Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hq25, le_rfl⟩, ((Finset.mem_filter.mp hu.2).2.1 q hq).1⟩
        have := Finset.single_le_prod' (f := fun r => r + 1) (fun r _ => Nat.succ_le_succ (Nat.zero_le r)) hm
        unfold chainThresh; omega
      exact hqT.trans hT
    have hp_eq : p₁ = p₂ := by
      have h12 : p₁ ∈ insert p₂ S₂ := hEq ▸ Finset.mem_insert_self p₁ S₁
      have h21 : p₂ ∈ insert p₁ S₁ := hEq.symm ▸ Finset.mem_insert_self p₂ S₂
      rcases Finset.mem_insert.mp h12 with h | h
      · exact h
      · rcases Finset.mem_insert.mp h21 with h' | h'
        · exact h'.symm
        · have := hlt2 p₁ h; have := hlt1 p₂ h'; omega
    subst hp_eq
    have hS_eq : S₁ = S₂ := by
      have hp1_not : p₁ ∉ S₁ := fun h => (hlt1 p₁ h).false
      have hp2_not : p₁ ∉ S₂ := fun h => (hlt2 p₁ h).false
      have := congrArg (fun W => W.erase p₁) hEq
      simpa [Finset.erase_insert hp1_not, Finset.erase_insert hp2_not] using this
    subst hS_eq
    rfl
  have hmem_empty : (∅ : Finset ℕ) ∈ (Nat.primesLE ⌊x⌋₊).powerset.filter IsPrimeChain :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), isPrimeChain_empty⟩
  have hsum_split : G_above x =
      1 + ∑ S ∈ ((Nat.primesLE ⌊x⌋₊).powerset.filter IsPrimeChain).erase ∅,
        (1 : ℝ) / ∏ p ∈ S, (p : ℝ) := by
    unfold G_above
    rw [← Finset.add_sum_erase _ _ hmem_empty]
    simp
  rw [hsum_split]
  gcongr
  calc ∑ p ∈ P, G_above (Real.log p / 2) / p
      = ∑ u ∈ D, (1 : ℝ) / ∏ r ∈ ins u, (r : ℝ) := by
        rw [Finset.sum_sigma]
        refine Finset.sum_congr rfl fun p hp => ?_
        unfold G_above
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun S hS => ?_
        have hp_not : p ∉ S := by
          intro hmem
          have hq_le : p ≤ ⌊Real.log p / 2⌋₊ :=
            Nat.le_of_mem_primesLE ((Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1) hmem)
          have hp_pr : p.Prime := Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hp).1
          have hqR : (p : ℝ) ≤ Real.log p / 2 := (Nat.cast_le.mpr hq_le).trans
            (Nat.floor_le (by linarith [Real.log_natCast_nonneg p]))
          have hlog_le : Real.log (p : ℝ) ≤ (p : ℝ) - 1 :=
            Real.log_le_sub_one_of_pos (by exact_mod_cast hp_pr.pos)
          linarith
        dsimp only [ins]
        rw [Finset.prod_insert hp_not]
        ring
    _ = ∑ S ∈ D.image ins, (1 : ℝ) / ∏ r ∈ S, (r : ℝ) :=
        (Finset.sum_image (f := fun S : Finset ℕ => (1 : ℝ) / ∏ r ∈ S, (r : ℝ)) hins_inj).symm
    _ ≤ ∑ S ∈ ((Nat.primesLE ⌊x⌋₊).powerset.filter IsPrimeChain).erase ∅,
          (1 : ℝ) / ∏ r ∈ S, (r : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hins_mem)
          (fun _ _ _ => by positivity)

/-- Level 1 bound: `log (log x) - 0.56 ≤ G_above x` for all `x ≥ 25`. -/
lemma G_above_ge_L2 {x : ℝ} (hx : 25 ≤ x) : Real.log (Real.log x) - 0.56 ≤ G_above x := by
  have hrec := G_above_recursion hx
  have h1 : 1 + ∑ p ∈ Nat.primesLE ⌊x⌋₊ \ Nat.primesLE 25, (1 : ℝ) / p ≤ G_above x := by
    refine le_trans ?_ hrec
    gcongr with p _
    exact G_above_ge_one _
  have habel := abel_prime_recip_ge (a := 25) (b := x) (by norm_num) hx
    (f := fun _ => (1 : ℝ)) (g' := fun t => -(t * (Real.log t) ^ 2)⁻¹)
    (fun t ht => by
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have hlog0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
      have hd := (hasDerivAt_const t (1 : ℝ)).div (Real.hasDerivAt_log ht0) hlog0
      refine hd.congr_deriv ?_
      field_simp [ht0, hlog0]
      ring)
    (fun t ht => by
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have hlog0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
      exact (((continuousAt_id.mul ((Real.continuousAt_log ht0).pow 2)).inv₀
        (mul_ne_zero ht0 (pow_ne_zero 2 hlog0))).neg).continuousWithinAt)
    (fun t ht => by
      have ht0 : 0 < t := by linarith [ht.1]
      have hlog0 : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
      exact neg_nonpos.mpr (inv_nonneg.mpr (mul_nonneg ht0.le (sq_nonneg _))))
    (by norm_num)
  have hint : ∫ t in (25 : ℝ)..x, (1 : ℝ) / (t * Real.log t) =
      Real.log (Real.log x) - Real.log (Real.log 25) := by
    have hderiv : ∀ t ∈ Set.uIcc (25 : ℝ) x,
        HasDerivAt (fun u => Real.log (Real.log u)) (1 / (t * Real.log t)) t := by
      intro t ht
      rw [Set.uIcc_of_le hx] at ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have hlog0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
      refine ((Real.hasDerivAt_log ht0).log hlog0).congr_deriv ?_
      field_simp [ht0, hlog0]
    have hci : IntervalIntegrable (fun t => (1 : ℝ) / (t * Real.log t)) MeasureTheory.volume 25 x := by
      refine ContinuousOn.intervalIntegrable fun t ht => ?_
      rw [Set.uIcc_of_le hx] at ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have hlog0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
      exact (continuousAt_const.div (continuousAt_id.mul (Real.continuousAt_log ht0))
        (mul_ne_zero ht0 hlog0)).continuousWithinAt
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => Real.log (Real.log u)) hderiv hci
  rw [hint] at habel
  have hlog25_lo : 3.218 ≤ Real.log 25 := by
    have : Real.log 25 = 2 * Real.log 5 := by
      rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_five_gt_d9]
  have hlog25_hi : Real.log 25 ≤ 3.22 := by
    have : Real.log 25 = 2 * Real.log 5 := by
      rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_five_lt_d9]
  have hloglog25 : Real.log (Real.log 25) ≤ 1.18 := by
    have h1' := Real.log_le_sub_one_of_pos (show (0 : ℝ) < Real.log 25 / 3 by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at h1'
    linarith [Real.log_three_lt_d9]
  have herr : 1 / Real.log 25 * (mertensM 25 - Real.log 25 + 2) ≤ 0.38 := by
    have hnum : mertensM 25 - Real.log 25 + 2 ≤ 1.09 := by linarith [mertensM_25_le]
    have hnum_nonneg : 0 ≤ mertensM 25 - Real.log 25 + 2 := by
      linarith [mertensM_ge (x := 25) (by norm_num)]
    calc 1 / Real.log 25 * (mertensM 25 - Real.log 25 + 2)
        ≤ 1 / 3.218 * 1.09 := by
          gcongr
      _ ≤ 0.38 := by norm_num
  have hfl25 : ⌊(25 : ℝ)⌋₊ = 25 := by norm_num
  rw [hfl25] at habel
  linarith

set_option maxHeartbeats 800000 in
/-- Level 2 (base case `m = 2`): for `iterLog 3 x ≥ 3.99`, `1.23 * (iterLog 2 x * iterLog 3 x) ≤ G_total x`. -/
lemma G_total_ge_base {x : ℝ} (hpos : ∀ j ≤ 3, 1 ≤ iterLog j x) (h3 : 3.99 ≤ iterLog 3 x) :
    1.23 * (iterLog 2 x * iterLog 3 x) ≤ G_total x := by
  let a : ℝ := Real.exp 50
  have hU_ge : 54 < iterLog 2 x := by
    have h2 : iterLog 2 x = Real.exp (iterLog 3 x) := (iterLog_exp_step hpos (i := 2) (by omega)).symm
    rw [h2]
    exact exp_399_gt.trans_le (Real.exp_le_exp.mpr h3)
  have hL1_ge : Real.exp 54 < iterLog 1 x := by
    have h1 : iterLog 1 x = Real.exp (iterLog 2 x) := (iterLog_exp_step hpos (i := 1) (by omega)).symm
    rw [h1]
    exact Real.exp_lt_exp.mpr hU_ge
  have h50_lt : 50 < iterLog 1 x := by
    have : (50 : ℝ) < Real.exp 54 := by linarith [Real.add_one_le_exp (54 : ℝ)]
    linarith
  have ha_le_x : a ≤ x := by
    have hx_eq : x = Real.exp (iterLog 1 x) := (iterLog_exp_step hpos (i := 0) (by omega)).symm
    rw [hx_eq]
    exact Real.exp_le_exp.mpr h50_lt.le
  have ha_ge_25 : 25 ≤ a := by
    unfold a
    linarith [Real.add_one_le_exp (50 : ℝ)]
  have hrec := G_above_recursion (by linarith)
  let f : ℝ → ℝ := fun t => Real.log (iterLog 2 t - Real.log 2) - 0.56
  have hlog2_lt : Real.log 2 < 0.7 := by linarith [Real.log_two_lt_d9]
  have hlog25_lo : 3.218 ≤ Real.log 25 := by
    have : Real.log 25 = 2 * Real.log 5 := by
      rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_five_gt_d9]
  have hv_ge : ∀ t ∈ Set.Icc a x, 3.218 ≤ iterLog 2 t - Real.log 2 := by
    intro t ht
    have hlogt : 50 ≤ Real.log t := by
      have := Real.log_le_log (Real.exp_pos 50) ht.1
      rwa [Real.log_exp] at this
    have hlog2t : Real.log 50 ≤ iterLog 2 t := by
      rw [iterLog_succ, iterLog_succ, iterLog_zero]
      exact Real.log_le_log (by norm_num) hlogt
    have h50 : Real.log 50 - Real.log 2 = Real.log 25 := by
      rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
    linarith
  have hsum_ge : ∑ p ∈ Nat.primesLE ⌊x⌋₊ \ Nat.primesLE ⌊a⌋₊, f p / p ≤
      ∑ p ∈ Nat.primesLE ⌊x⌋₊ \ Nat.primesLE 25, G_above (Real.log p / 2) / p := by
    have hsub : Nat.primesLE ⌊x⌋₊ \ Nat.primesLE ⌊a⌋₊ ⊆ Nat.primesLE ⌊x⌋₊ \ Nat.primesLE 25 := by
      intro p hp
      have hpm := Finset.mem_sdiff.mp hp
      exact Finset.mem_sdiff.mpr ⟨hpm.1, fun h25 =>
        hpm.2 (Nat.primesLE_mono (Nat.le_floor ha_ge_25) h25)⟩
    calc ∑ p ∈ Nat.primesLE ⌊x⌋₊ \ Nat.primesLE ⌊a⌋₊, f p / p
        ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊ \ Nat.primesLE ⌊a⌋₊, G_above (Real.log p / 2) / p := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hp_gt : a < (p : ℝ) := by
            have hpm := Finset.mem_sdiff.mp hp
            have hpp := Nat.prime_of_mem_primesLE hpm.1
            have hnot : ¬ p ≤ ⌊a⌋₊ := fun hle => hpm.2 (Nat.mem_primesLE.mpr ⟨hle, hpp⟩)
            exact (Nat.floor_lt (by linarith [ha_ge_25])).mp (by omega)
          have hp_le : (p : ℝ) ≤ x :=
            (Nat.cast_le.mpr (Nat.le_of_mem_primesLE (Finset.mem_sdiff.mp hp).1)).trans
              (Nat.floor_le (by linarith))
          have hlogp_ge : 50 ≤ Real.log (p : ℝ) := by
            have := Real.log_le_log (Real.exp_pos 50) hp_gt.le
            rwa [Real.log_exp] at this
          have hL2 := G_above_ge_L2 (x := Real.log (p : ℝ) / 2) (by linarith)
          have heq : Real.log (Real.log (Real.log (p : ℝ) / 2)) - 0.56 = f p := by
            simp only [f, iterLog_succ, iterLog_zero]
            rw [Real.log_div (by linarith) (by norm_num)]
          rw [heq] at hL2
          exact div_le_div_of_nonneg_right hL2 (Nat.cast_nonneg p)
      _ ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊ \ Nat.primesLE 25, G_above (Real.log p / 2) / p :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ =>
            div_nonneg (by linarith [G_above_ge_one (Real.log p / 2)]) (Nat.cast_nonneg p))
  -- Apply abel_prime_recip_ge to f on [a, x]
  let g' : ℝ → ℝ := fun t =>
    (1 / (iterLog 2 t - Real.log 2) - f t) / (t * (Real.log t) ^ 2)
  have hf_deriv : ∀ t ∈ Set.Icc a x, HasDerivAt (fun u => f u / Real.log u) (g' t) t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1, ha_ge_25]
    have hlogt0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1, ha_ge_25])).ne'
    have hv0 : iterLog 2 t - Real.log 2 ≠ 0 := by linarith [hv_ge t ht]
    have hd_L2 : HasDerivAt (fun u => iterLog 2 u - Real.log 2) (1 / (t * Real.log t)) t := by
      have h := ((Real.hasDerivAt_log ht0).log hlogt0).sub_const (Real.log 2)
      refine h.congr_deriv ?_
      field_simp [ht0, hlogt0]
    have hd_f : HasDerivAt f (1 / (t * Real.log t * (iterLog 2 t - Real.log 2))) t := by
      have h := (hd_L2.log hv0).sub_const (0.56 : ℝ)
      refine h.congr_deriv ?_
      field_simp [ht0, hlogt0, hv0]
    have hd_g := hd_f.div (Real.hasDerivAt_log ht0) hlogt0
    refine hd_g.congr_deriv ?_
    dsimp only [g']
    field_simp [ht0, hlogt0, hv0]
  have hg'_cont : ContinuousOn g' (Set.Icc a x) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1, ha_ge_25]
    have hlogt0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1, ha_ge_25])).ne'
    have hv0 : iterLog 2 t - Real.log 2 ≠ 0 := by linarith [hv_ge t ht]
    have hcont_L2 : ContinuousAt (fun u => iterLog 2 u - Real.log 2) t :=
      ((Real.continuousAt_log ht0).log hlogt0).sub continuousAt_const
    have hcont_f : ContinuousAt f t := (hcont_L2.log hv0).sub continuousAt_const
    have hcont_num : ContinuousAt (fun u => 1 / (iterLog 2 u - Real.log 2) - f u) t :=
      (continuousAt_const.div hcont_L2 hv0).sub hcont_f
    have hcont_den : ContinuousAt (fun u => u * (Real.log u) ^ 2) t :=
      continuousAt_id.mul ((Real.continuousAt_log ht0).pow 2)
    exact (hcont_num.div hcont_den (mul_ne_zero ht0 (pow_ne_zero 2 hlogt0))).continuousWithinAt
  have hg'_nonpos : ∀ t ∈ Set.Icc a x, g' t ≤ 0 := by
    intro t ht
    have hv := hv_ge t ht
    have hlogv : 1.1 < Real.log (iterLog 2 t - Real.log 2) := by
      have h1 : Real.exp 1.1 ≤ 3.1 := by
        have h := Real.exp_bound (x := (0.1 : ℝ)) (n := 4) (by norm_num) (by norm_num)
        simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
        norm_num at h
        have h01 : Real.exp 0.1 ≤ 1.11 := by linarith [(abs_le.mp h).2]
        have he := Real.exp_one_lt_d9
        have hadd : Real.exp 1.1 = Real.exp 1 * Real.exp 0.1 := by
          rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos 0.1]
      exact (Real.lt_log_iff_exp_lt (by linarith)).mpr (by linarith)
    have hinv : 1 / (iterLog 2 t - Real.log 2) ≤ 0.32 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hnum : 1 / (iterLog 2 t - Real.log 2) - f t ≤ 0 := by
      dsimp only [f]; linarith
    have hden : 0 < t * (Real.log t) ^ 2 :=
      mul_pos (by linarith [ht.1, ha_ge_25]) (sq_pos_of_pos (Real.log_pos (by linarith [ht.1, ha_ge_25])))
    exact div_nonpos_of_nonpos_of_nonneg hnum hden.le
  have hfx_nonneg : 0 ≤ f x := by
    have hv := hv_ge x (Set.right_mem_Icc.mpr ha_le_x)
    have h1 : 1 ≤ Real.log (iterLog 2 x - Real.log 2) :=
      (Real.le_log_iff_exp_le (by linarith)).mpr (by linarith [Real.exp_one_lt_three])
    dsimp only [f]; linarith
  have habel := abel_prime_recip_ge (by linarith) ha_le_x hf_deriv hg'_cont hg'_nonpos hfx_nonneg
  -- Evaluate the integral explicitly via FTC
  let Fanti : ℝ → ℝ := fun t =>
    (iterLog 2 t - Real.log 2) * (Real.log (iterLog 2 t - Real.log 2) - 1.56)
  have hint_eq : ∫ t in a..x, f t / (t * Real.log t) = Fanti x - Fanti a := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := Fanti) ?_ ?_
    · intro t ht
      rw [Set.uIcc_of_le ha_le_x] at ht
      have ht0 : t ≠ 0 := by linarith [ht.1, ha_ge_25]
      have hlogt0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1, ha_ge_25])).ne'
      have hv0 : iterLog 2 t - Real.log 2 ≠ 0 := by linarith [hv_ge t ht]
      have hd_v : HasDerivAt (fun u => iterLog 2 u - Real.log 2) (1 / (t * Real.log t)) t := by
        have h := ((Real.hasDerivAt_log ht0).log hlogt0).sub_const (Real.log 2)
        refine h.congr_deriv ?_; field_simp [ht0, hlogt0]
      have hd_lv : HasDerivAt (fun u => Real.log (iterLog 2 u - Real.log 2) - 1.56)
          (1 / (t * Real.log t * (iterLog 2 t - Real.log 2))) t := by
        have h := (hd_v.log hv0).sub_const (1.56 : ℝ)
        refine h.congr_deriv ?_; field_simp [ht0, hlogt0, hv0]
      refine (hd_v.mul hd_lv).congr_deriv ?_
      dsimp only [f]
      field_simp [ht0, hlogt0, hv0]
      ring
    · refine ContinuousOn.intervalIntegrable fun t ht => ?_
      rw [Set.uIcc_of_le ha_le_x] at ht
      have ht0 : t ≠ 0 := by linarith [ht.1, ha_ge_25]
      have hlogt0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1, ha_ge_25])).ne'
      have hv0 : iterLog 2 t - Real.log 2 ≠ 0 := by linarith [hv_ge t ht]
      have hcont_v : ContinuousAt (fun u => iterLog 2 u - Real.log 2) t :=
        ((Real.continuousAt_log ht0).log hlogt0).sub continuousAt_const
      have hcont_f : ContinuousAt f t := (hcont_v.log hv0).sub continuousAt_const
      exact (hcont_f.div (continuousAt_id.mul (Real.continuousAt_log ht0))
        (mul_ne_zero ht0 hlogt0)).continuousWithinAt
  rw [hint_eq] at habel
  -- Bound the constant terms at `a = exp 50`
  have hva : iterLog 2 a - Real.log 2 = Real.log 25 := by
    simp only [a, iterLog_succ, iterLog_zero, Real.log_exp]
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  have hlog25_hi : Real.log 25 ≤ 3.22 := by
    have : Real.log 25 = 2 * Real.log 5 := by
      rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_five_lt_d9]
  have hloglog25 : Real.log (Real.log 25) ≤ 1.18 := by
    have h1' := Real.log_le_sub_one_of_pos (show (0 : ℝ) < Real.log 25 / 3 by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at h1'
    linarith [Real.log_three_lt_d9]
  have hFa_le : Fanti a ≤ -1.2 := by
    dsimp only [Fanti]
    rw [hva]
    nlinarith only [hlog25_lo, hloglog25]
  have hfa_nonneg : 0 ≤ f a := by
    dsimp only [f]
    rw [hva]
    have h1 : 1 ≤ Real.log (Real.log 25) :=
      (Real.le_log_iff_exp_le (by linarith)).mpr (by linarith [Real.exp_one_lt_three])
    linarith
  have hfa_le : f a ≤ 0.62 := by dsimp only [f]; rw [hva]; linarith only [hloglog25]
  have hbdy_le : (f a / Real.log a) * (mertensM a - Real.log a + 2) ≤ 0.3 := by
    have hloga : Real.log a = 50 := Real.log_exp 50
    have hMa : mertensM a ≤ Real.log 4 * 50 + 1 := by
      have h := mertensM_le (x := a) (by linarith)
      rwa [hloga] at h
    have hlog4 : Real.log 4 ≤ 1.39 := by rw [Real.log_four_eq]; linarith [Real.log_two_lt_d9]
    have hMdiff : mertensM a - Real.log a + 2 ≤ 22.5 := by rw [hloga]; nlinarith only [hMa, hlog4]
    have hMdiff_nn : 0 ≤ mertensM a - Real.log a + 2 := by
      linarith [mertensM_ge (x := a) (by linarith)]
    rw [hloga] at hMdiff hMdiff_nn ⊢
    nlinarith only [hfa_nonneg, hfa_le, hMdiff, hMdiff_nn]
  have hGab_lb : Fanti x + 1.9 ≤ G_above x := by
    linarith only [hrec, hsum_ge, habel, hFa_le, hbdy_le]
  -- Compare `(25/12) * (Fanti x + 1.9)` with `1.23 * U * log U` for `U = iterLog 2 x ≥ exp 3.99`
  let U := iterLog 2 x
  let V := U - Real.log 2
  have hV_ge : (53.3 / 54.05 : ℝ) * U ≤ V := by
    dsimp only [V, U]; linarith only [Real.log_two_lt_d9, hU_ge]
  have hlogV_ge : Real.log U - 0.014 ≤ Real.log V := by
    have hU_pos : 0 < U := by linarith only [hU_ge]
    have hV_pos : 0 < V := by dsimp only [V, U]; linarith only [Real.log_two_lt_d9, hU_ge]
    have hratio : Real.log (U / V) ≤ U / V - 1 := Real.log_le_sub_one_of_pos (div_pos hU_pos hV_pos)
    rw [Real.log_div hU_pos.ne' hV_pos.ne'] at hratio
    have hdiff : U / V - 1 = Real.log 2 / V := by
      field_simp [hV_pos.ne']; dsimp only [V]; ring
    rw [hdiff] at hratio
    have hdiv_le : Real.log 2 / V ≤ 0.014 := by
      rw [div_le_iff₀ hV_pos]
      dsimp only [V, U]; linarith only [Real.log_two_lt_d9, hU_ge]
    linarith only [hratio, hdiv_le]
  have hlogU_eq : Real.log U = iterLog 3 x := (iterLog_succ 2 x).symm
  have hlogU_ge : 3.99 ≤ Real.log U := hlogU_eq ▸ h3
  have hFx_lb : V * (Real.log V - 1.56) = Fanti x := rfl
  have h1 : (53.3 / 54.05 : ℝ) * U * (Real.log U - 1.574) ≤ Fanti x := by
    rw [← hFx_lb]
    have hpos_fac : 0 ≤ Real.log U - 1.574 := by linarith only [hlogU_ge]
    calc (53.3 / 54.05 : ℝ) * U * (Real.log U - 1.574)
        ≤ V * (Real.log U - 1.574) := mul_le_mul_of_nonneg_right hV_ge hpos_fac
      _ ≤ V * (Real.log V - 1.56) := mul_le_mul_of_nonneg_left (by linarith only [hlogV_ge]) (by linarith only [hV_ge, hU_ge])
  have h2 : (1 - 1.574 / 3.99 : ℝ) * Real.log U ≤ Real.log U - 1.574 := by
    have : 1.574 ≤ (1.574 / 3.99 : ℝ) * Real.log U := by nlinarith only [hlogU_ge]
    linarith only [this]
  have hprod : (53.3 / 54.05 : ℝ) * (1 - 1.574 / 3.99 : ℝ) * (U * Real.log U) ≤ Fanti x := by
    nlinarith only [h1, h2, hU_ge]
  unfold G_total
  rw [← hlogU_eq]
  nlinarith only [hprod, hGab_lb, hU_ge, hlogU_ge]

/-- Coefficient sequence `C_m = 1.13 + 0.1 / 2^(m - 2)` for `m ≥ 2`. -/
noncomputable def coeffC (m : ℕ) : ℝ := 1.13 + 0.1 / (2 : ℝ) ^ (m - 2)

lemma coeffC_gt (m : ℕ) : 1.13 < coeffC m := by
  unfold coeffC; linarith [show (0 : ℝ) < 0.1 / (2 : ℝ) ^ (m - 2) by positivity]

lemma coeffC_le (m : ℕ) : coeffC m ≤ 1.23 := by
  unfold coeffC
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (m - 2) := one_le_pow₀ (by norm_num)
  have h2 : 0.1 / (2 : ℝ) ^ (m - 2) ≤ 0.1 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  linarith

/-- Perturbation bound: subtracting `δ ≤ 3` from `u ≥ 10^6` changes every iterated log by at most `6 / u`. -/
lemma iterLog_sub_ge {m : ℕ} {u δ : ℝ} (hu : 1000000 ≤ u) (_hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 3)
    (hpos : ∀ j ≤ m, 2 ≤ iterLog j u) :
    ∀ j ∈ Finset.Icc 1 m, iterLog j u - 6 / u ≤ iterLog j (u - δ) ∧ 1 ≤ iterLog j (u - δ) := by
  intro j hj
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjm : j ≤ m := (Finset.mem_Icc.mp hj).2
  clear hj
  revert hjm
  induction j, hj1 using Nat.le_induction with
  | base =>
    intro hjm
    rw [iterLog_succ, iterLog_zero, iterLog_succ, iterLog_zero]
    have hud_pos : 0 < u - δ := by linarith
    have hlog : Real.log (u / (u - δ)) ≤ u / (u - δ) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (by linarith) hud_pos)
    rw [Real.log_div (by linarith) hud_pos.ne'] at hlog
    have hdiff : u / (u - δ) - 1 ≤ 6 / u := by
      have : u / (u - δ) - 1 = δ / (u - δ) := by field_simp [hud_pos.ne']; ring
      rw [this, div_le_div_iff₀ hud_pos (by linarith)]
      nlinarith
    have hlb : Real.log u - 6 / u ≤ Real.log (u - δ) := by linarith
    have hge1 : 1 ≤ Real.log (u - δ) := by
      have h2 := hpos 1 (by omega)
      rw [iterLog_succ, iterLog_zero] at h2
      have h6u : 6 / u ≤ 1 := by rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    exact ⟨hlb, hge1⟩
  | succ j hj ih =>
    intro hjm
    obtain ⟨hlb, hge1⟩ := ih (by omega)
    rw [iterLog_succ, iterLog_succ]
    have hLj : 2 ≤ iterLog j u := hpos j (by omega)
    have h6u : 6 / u ≤ 0.001 := by rw [div_le_iff₀ (by linarith)]; linarith
    have hrat : Real.log (iterLog j u / iterLog j (u - δ)) ≤
        iterLog j u / iterLog j (u - δ) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (by linarith) (by linarith))
    rw [Real.log_div (by linarith) (by linarith)] at hrat
    have hstep : iterLog j u / iterLog j (u - δ) - 1 ≤ 6 / u := by
      have : iterLog j u / iterLog j (u - δ) - 1 =
          (iterLog j u - iterLog j (u - δ)) / iterLog j (u - δ) := by
        field_simp [show iterLog j (u - δ) ≠ 0 by linarith]
      rw [this, div_le_iff₀ (by linarith)]
      have hge15 : 1.5 ≤ iterLog j (u - δ) := by linarith
      have h6u_nn : 0 ≤ 6 / u := by positivity
      nlinarith
    have hlb' : Real.log (iterLog j u) - 6 / u ≤ Real.log (iterLog j (u - δ)) := by linarith
    have h2 : 2 ≤ Real.log (iterLog j u) := by
      have := hpos (j + 1) hjm; rwa [iterLog_succ] at this
    exact ⟨hlb', by linarith⟩

set_option maxHeartbeats 1200000 in
/-- Main induction on `m ≥ 2`: for `iterLog (m + 1) x ≥ m + 1.99`,
`coeffC m * ∏_{j=2}^{m+1} iterLog j x ≤ G_total x`. -/
lemma G_total_ge_ind (m : ℕ) (hm : 2 ≤ m) :
    ∀ x : ℝ, (∀ j ≤ m + 1, 1 ≤ iterLog j x) → (m : ℝ) + 1.99 ≤ iterLog (m + 1) x →
      coeffC m * ∏ j ∈ Finset.Icc 2 (m + 1), iterLog j x ≤ G_total x := by
  induction m, hm using Nat.le_induction with
  | base =>
    intro x hpos h3
    have hC2 : coeffC 2 = 1.23 := by unfold coeffC; norm_num
    have hIcc : Finset.Icc 2 3 = {2, 3} := by decide
    rw [hC2, hIcc, Finset.prod_pair (by decide)]
    exact G_total_ge_base hpos (by push_cast at h3; linarith)
  | succ m hm ih =>
    intro x hpos htop
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    let y₀ : ℝ := (m : ℝ) + 1.99
    let v₀ : ℝ := Real.exp^[m] y₀
    let a : ℝ := Real.exp (Real.exp (v₀ + Real.log 2))
    have hy₀_ge : 3.99 ≤ y₀ := by dsimp only [y₀]; linarith
    have hv₀_logs : ∀ j ≤ m, iterLog j v₀ = Real.exp^[m - j] y₀ :=
      iterLog_iterExp m y₀
    have hv₀_ge2 : ∀ j ≤ m, 2 ≤ iterLog j v₀ := by
      intro j hj
      rw [hv₀_logs j hj]
      linarith [iterExp_ge_self (m - j) y₀]
    have hL1_v₀ : Real.exp y₀ ≤ iterLog 1 v₀ := by
      rw [hv₀_logs 1 (by omega)]
      have hsub : m - 1 = (m - 2) + 1 := by omega
      rw [hsub, Function.iterate_succ_apply]
      exact iterExp_ge_self (m - 2) (Real.exp y₀)
    have hL1_v₀_54 : 54 < Real.exp y₀ :=
      exp_399_gt.trans_le (Real.exp_le_exp.mpr hy₀_ge)
    have hv₀_ge_54 : 54 < v₀ := by
      have := hv₀_logs 0 (Nat.zero_le m)
      rw [iterLog_zero, Nat.sub_zero] at this
      have hm_eq : m = (m - 1) + 1 := by omega
      have h1 : Real.exp y₀ ≤ Real.exp^[m] y₀ := by
        rw [hm_eq, Function.iterate_succ_apply]
        exact iterExp_ge_self (m - 1) (Real.exp y₀)
      linarith
    have ha_ge_25 : 25 ≤ a := by
      have h1 : 54 ≤ Real.exp (v₀ + Real.log 2) := by
        linarith [Real.add_one_le_exp (v₀ + Real.log 2), Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
      linarith [Real.add_one_le_exp (Real.exp (v₀ + Real.log 2))]
    -- Compare `V = iterLog 2 x - log 2` with `v₀`
    let U := iterLog 2 x
    let V := U - Real.log 2
    have hU_eq : U = Real.exp^[m] (iterLog (m + 2) x) := by
      dsimp only [U]
      have h := iterLog_eq_iterExp hpos (j := 2) (by omega)
      simpa [show m + 2 - 2 = m by omega] using h
    have hU_ge_big : 1000 * Real.exp y₀ * v₀ ≤ U := by
      rw [hU_eq]
      have h1 : y₀ + 1 ≤ iterLog (m + 2) x := by
        dsimp only [y₀]; push_cast at htop; linarith
      exact (iterExp_add_one_ge hm hy₀_ge).trans (iterExp_mono m h1)
    have hU_ge_1e6 : 1000000 ≤ U := by nlinarith
    have hV_ge_v0 : 999 * Real.exp y₀ * v₀ ≤ V := by
      dsimp only [V]
      have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
      nlinarith
    have hv0_lt_V : v₀ < V := by nlinarith
    have ha_le_x : a ≤ x := by
      have hL2a : iterLog 2 a = v₀ + Real.log 2 := by
        simp only [a, iterLog_succ, iterLog_zero, Real.log_exp]
      have hL1_le : iterLog 1 a ≤ iterLog 1 x := by
        have h1a : iterLog 1 a = Real.exp (iterLog 2 a) := by
          simp only [a, iterLog_succ, iterLog_zero, Real.log_exp]
        have h1x : iterLog 1 x = Real.exp (iterLog 2 x) :=
          (iterLog_exp_step hpos (i := 1) (by omega)).symm
        rw [h1a, h1x]
        exact Real.exp_le_exp.mpr (by dsimp only [V, U] at hv0_lt_V; linarith)
      have h0a : a = Real.exp (iterLog 1 a) := by
        simp only [a, iterLog_succ, iterLog_zero, Real.log_exp]
      have h0x : x = Real.exp (iterLog 1 x) :=
        (iterLog_exp_step hpos (i := 0) (by omega)).symm
      rw [h0a, h0x]
      exact Real.exp_le_exp.mpr hL1_le
    -- Define `f t = coeffC m * prodIterLog m (iterLog 2 t - log 2)`
    let vfun : ℝ → ℝ := fun t => iterLog 2 t - Real.log 2
    let f : ℝ → ℝ := fun t => coeffC m * prodIterLog m (vfun t)
    have hvfun_ge_v0 : ∀ t ∈ Set.Icc a x, v₀ ≤ vfun t := by
      intro t ht
      have h1 : Real.exp (v₀ + Real.log 2) ≤ Real.log t := by
        have := Real.log_le_log (Real.exp_pos _) ht.1
        rwa [Real.log_exp] at this
      have h2 : v₀ + Real.log 2 ≤ iterLog 2 t := by
        rw [iterLog_succ, iterLog_succ, iterLog_zero]
        have := Real.log_le_log (Real.exp_pos _) h1
        rwa [Real.log_exp] at this
      dsimp only [vfun]; linarith
    have hvfun_ge2 : ∀ t ∈ Set.Icc a x, ∀ j ≤ m, 2 ≤ iterLog j (vfun t) := by
      intro t ht j hj
      have h1 := hv₀_ge2 j hj
      have h2 := iterLog_mono (fun i hi => by linarith [hv₀_ge2 i hi]) (hvfun_ge_v0 t ht) j hj
      linarith
    -- Relate `G_total x` to `∑_{a < p ≤ x} f p / p`
    have hrec_total : ∑ p ∈ Nat.primesLE ⌊x⌋₊ \ Nat.primesLE ⌊a⌋₊, f p / p ≤ G_total x := by
      have hrec := G_above_recursion (by linarith)
      have hmul : (25 / 12 : ℝ) * (1 + ∑ p ∈ Nat.primesLE ⌊x⌋₊ \ Nat.primesLE 25,
          G_above (Real.log p / 2) / p) ≤ G_total x :=
        mul_le_mul_of_nonneg_left hrec (by norm_num)
      have hsub : Nat.primesLE ⌊x⌋₊ \ Nat.primesLE ⌊a⌋₊ ⊆ Nat.primesLE ⌊x⌋₊ \ Nat.primesLE 25 := by
        intro p hp
        have hpm := Finset.mem_sdiff.mp hp
        exact Finset.mem_sdiff.mpr ⟨hpm.1, fun h25 =>
          hpm.2 (Nat.primesLE_mono (Nat.le_floor ha_ge_25) h25)⟩
      calc ∑ p ∈ Nat.primesLE ⌊x⌋₊ \ Nat.primesLE ⌊a⌋₊, f p / p
          ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊ \ Nat.primesLE ⌊a⌋₊, G_total (Real.log p / 2) / p := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hp_gt : a < (p : ℝ) := by
              have hpm := Finset.mem_sdiff.mp hp
              have hpp := Nat.prime_of_mem_primesLE hpm.1
              have hnot : ¬ p ≤ ⌊a⌋₊ := fun hle => hpm.2 (Nat.mem_primesLE.mpr ⟨hle, hpp⟩)
              dsimp only [a] at hnot ⊢
              exact (Nat.floor_lt (Real.exp_pos _).le).mp (by omega)
            have hp_le : (p : ℝ) ≤ x :=
              (Nat.cast_le.mpr (Nat.le_of_mem_primesLE (Finset.mem_sdiff.mp hp).1)).trans
                (Nat.floor_le (by linarith))
            have hp_mem : (p : ℝ) ∈ Set.Icc a x := ⟨hp_gt.le, hp_le⟩
            have hlogp_half : Real.log (Real.log (p : ℝ) / 2) = vfun p := by
              have hlogp_pos : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
              dsimp only [vfun]
              rw [iterLog_succ, iterLog_succ, iterLog_zero, Real.log_div hlogp_pos.ne' (by norm_num)]
            have hiter_shift : ∀ j ≤ m, iterLog (j + 1) (Real.log (p : ℝ) / 2) = iterLog j (vfun p) := by
              intro j _
              rw [iterLog_succ_inner, hlogp_half]
            have hpos_p : ∀ j ≤ m + 1, 1 ≤ iterLog j (Real.log (p : ℝ) / 2) := by
              intro j hj
              cases j with
              | zero =>
                rw [iterLog_zero]
                have hlogp : Real.exp (v₀ + Real.log 2) ≤ Real.log (p : ℝ) := by
                  have := Real.log_le_log (Real.exp_pos _) hp_gt.le
                  rwa [Real.log_exp] at this
                linarith [Real.add_one_le_exp (v₀ + Real.log 2),
                  Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
              | succ j =>
                rw [hiter_shift j (by omega)]
                linarith [hvfun_ge2 p hp_mem j (by omega)]
            have htop_p : (m : ℝ) + 1.99 ≤ iterLog (m + 1) (Real.log (p : ℝ) / 2) := by
              rw [hiter_shift m le_rfl]
              have h1 := iterLog_mono (fun i hi => by linarith [hv₀_ge2 i hi])
                (hvfun_ge_v0 p hp_mem) m le_rfl
              have h2 := hv₀_logs m le_rfl
              simp only [Nat.sub_self, Function.iterate_zero, id_eq] at h2
              dsimp only [y₀] at h2
              linarith
            have hIH := ih (Real.log (p : ℝ) / 2) hpos_p htop_p
            have hprod_eq : ∏ j ∈ Finset.Icc 2 (m + 1), iterLog j (Real.log (p : ℝ) / 2) =
                prodIterLog m (vfun p) := by
              unfold prodIterLog
              refine Finset.prod_nbij (· - 1) ?_ ?_ ?_ ?_
              · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
              · intro j₁ h1 j₂ h2 h; simp only [Finset.mem_coe, Finset.mem_Icc] at h1 h2; dsimp only at h; omega
              · intro j hj; simp only [Finset.mem_coe, Finset.mem_Icc] at hj
                exact ⟨j + 1, Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), by dsimp only; omega⟩
              · intro j hj
                have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
                have hjm : j ≤ m + 1 := (Finset.mem_Icc.mp hj).2
                have h := hiter_shift (j - 1) (by omega)
                rwa [Nat.sub_add_cancel (by omega)] at h
            rw [hprod_eq] at hIH
            exact div_le_div_of_nonneg_right hIH (Nat.cast_nonneg p)
        _ ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊ \ Nat.primesLE 25, G_total (Real.log p / 2) / p :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ =>
              div_nonneg (by unfold G_total; linarith [G_above_ge_one (Real.log p / 2)])
                (Nat.cast_nonneg p))
        _ = (25 / 12 : ℝ) * ∑ p ∈ Nat.primesLE ⌊x⌋₊ \ Nat.primesLE 25,
              G_above (Real.log p / 2) / p := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun p _ => by unfold G_total; ring
        _ ≤ G_total x := by linarith
    -- Apply abel_prime_recip_ge to f on [a, x]
    let S_sum (v : ℝ) : ℝ := ∑ r ∈ Finset.Icc 1 m, ∏ j ∈ Finset.range (r + 1), (iterLog j v)⁻¹
    let g' : ℝ → ℝ := fun t =>
      f t * (S_sum (vfun t) - 1) / (t * (Real.log t) ^ 2)
    have hf_deriv : ∀ t ∈ Set.Icc a x, HasDerivAt (fun u => f u / Real.log u) (g' t) t := by
      intro t ht
      have ht0 : t ≠ 0 := by linarith [ht.1, ha_ge_25]
      have hlogt0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1, ha_ge_25])).ne'
      have hd_v : HasDerivAt vfun (1 / (t * Real.log t)) t := by
        have h := ((Real.hasDerivAt_log ht0).log hlogt0).sub_const (Real.log 2)
        refine h.congr_deriv ?_; field_simp [ht0, hlogt0]
      have hd_P := (hasDerivAt_prodIterLog m (hvfun_ge2 t ht)).comp t hd_v
      have hd_f : HasDerivAt f (f t * S_sum (vfun t) / (t * Real.log t)) t := by
        have h := hd_P.const_mul (coeffC m)
        refine h.congr_deriv ?_
        dsimp only [f, S_sum]; ring
      have hd_g := hd_f.div (Real.hasDerivAt_log ht0) hlogt0
      refine hd_g.congr_deriv ?_
      dsimp only [g']
      field_simp [ht0, hlogt0]
    have hg'_cont : ContinuousOn g' (Set.Icc a x) := by
      intro t ht
      have ht0 : t ≠ 0 := by linarith [ht.1, ha_ge_25]
      have hlogt0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1, ha_ge_25])).ne'
      have hcont_v : ContinuousAt vfun t :=
        ((Real.continuousAt_log ht0).log hlogt0).sub continuousAt_const
      have hcont_L : ∀ j ≤ m, ContinuousAt (fun u => iterLog j (vfun u)) t := by
        intro j hj
        exact ((hasDerivAt_iterLog j (fun i hi => by linarith [hvfun_ge2 t ht i (by omega)])).continuousAt).comp hcont_v
      have hcont_f : ContinuousAt f t := by
        refine continuousAt_const.mul ?_
        exact continuousAt_prod_finset _ _ t fun j hj => hcont_L j (Finset.mem_Icc.mp hj).2
      have hcont_S : ContinuousAt (fun u => S_sum (vfun u)) t := by
        refine continuousAt_sum_finset _ _ t fun r hr => ?_
        refine continuousAt_prod_finset _ _ t fun j hj => ?_
        have hjm : j ≤ m := by
          have := (Finset.mem_Icc.mp hr).2
          have := Finset.mem_range.mp hj
          omega
        exact (hcont_L j hjm).inv₀ (by linarith [hvfun_ge2 t ht j hjm])
      exact ((hcont_f.mul (hcont_S.sub continuousAt_const)).div
        (continuousAt_id.mul ((Real.continuousAt_log ht0).pow 2))
        (mul_ne_zero ht0 (pow_ne_zero 2 hlogt0))).continuousWithinAt
    have hg'_nonpos : ∀ t ∈ Set.Icc a x, g' t ≤ 0 := by
      intro t ht
      have hS_le : S_sum (vfun t) ≤ 2 / vfun t := prodIterLog_deriv_le m (hvfun_ge2 t ht)
      have hv54 : 54 < vfun t := lt_of_lt_of_le hv₀_ge_54 (hvfun_ge_v0 t ht)
      have hS_lt1 : S_sum (vfun t) ≤ 1 := by
        have : 2 / vfun t ≤ 1 := by rw [div_le_iff₀ (by linarith)]; linarith
        linarith
      have hf_nn : 0 ≤ f t := mul_nonneg (by linarith [coeffC_gt m])
        (Finset.prod_nonneg fun j hj => by linarith [hvfun_ge2 t ht j (Finset.mem_Icc.mp hj).2])
      have hden : 0 < t * (Real.log t) ^ 2 :=
        mul_pos (by linarith [ht.1, ha_ge_25])
          (sq_pos_of_pos (Real.log_pos (by linarith [ht.1, ha_ge_25])))
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hf_nn (by linarith)) hden.le
    have hfx_nn : 0 ≤ f x := mul_nonneg (by linarith [coeffC_gt m])
      (Finset.prod_nonneg fun j hj => by
        linarith [hvfun_ge2 x (Set.right_mem_Icc.mpr ha_le_x) j (Finset.mem_Icc.mp hj).2])
    have habel := abel_prime_recip_ge (by linarith) ha_le_x hf_deriv hg'_cont hg'_nonpos hfx_nn
    -- Lower bound `∫_a^x f t / (t * log t) dt` directly via FTC on `phi m ∘ vfun`
    have hint_lb : coeffC m * (phi m V - phi m v₀) / (1 + 2 / iterLog 1 v₀) ≤
        ∫ t in a..x, f t / (t * Real.log t) := by
      let Dphi : ℝ → ℝ := fun t =>
        (∑ r ∈ Finset.range (m + 1), ∏ j ∈ Finset.Icc (r + 1) m, iterLog j (vfun t)) / (t * Real.log t)
      have hftc : ∫ t in a..x, Dphi t = phi m V - phi m v₀ := by
        have hvx : vfun x = V := rfl
        have hva : vfun a = v₀ := by
          simp only [vfun, a, iterLog_succ, iterLog_zero, Real.log_exp]; ring
        rw [← hvx, ← hva]
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => phi m (vfun t)) ?_ ?_
        · intro t ht
          rw [Set.uIcc_of_le ha_le_x] at ht
          have ht0 : t ≠ 0 := by linarith [ht.1, ha_ge_25]
          have hlogt0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1, ha_ge_25])).ne'
          have hd_v : HasDerivAt vfun (1 / (t * Real.log t)) t := by
            have h := ((Real.hasDerivAt_log ht0).log hlogt0).sub_const (Real.log 2)
            refine h.congr_deriv ?_; field_simp [ht0, hlogt0]
          have hd := (hasDerivAt_phi m (hvfun_ge2 t ht)).comp t hd_v
          refine hd.congr_deriv ?_
          dsimp only [Dphi]; ring
        · refine ContinuousOn.intervalIntegrable fun t ht => ?_
          rw [Set.uIcc_of_le ha_le_x] at ht
          have ht0 : t ≠ 0 := by linarith [ht.1, ha_ge_25]
          have hlogt0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1, ha_ge_25])).ne'
          have hcont_v : ContinuousAt vfun t :=
            ((Real.continuousAt_log ht0).log hlogt0).sub continuousAt_const
          have hcont_L : ∀ j ≤ m, ContinuousAt (fun u => iterLog j (vfun u)) t := fun j hj =>
            ((hasDerivAt_iterLog j (fun i hi => by linarith [hvfun_ge2 t ht i (by omega)])).continuousAt).comp hcont_v
          have hcont_num : ContinuousAt (fun u => ∑ r ∈ Finset.range (m + 1),
              ∏ j ∈ Finset.Icc (r + 1) m, iterLog j (vfun u)) t :=
            continuousAt_sum_finset _ _ t fun r _ =>
              continuousAt_prod_finset _ _ t fun j hj => hcont_L j (Finset.mem_Icc.mp hj).2
          exact (hcont_num.div (continuousAt_id.mul (Real.continuousAt_log ht0))
            (mul_ne_zero ht0 hlogt0)).continuousWithinAt
      have hK_pos : 0 < 1 + 2 / iterLog 1 v₀ := by
        have : 0 < iterLog 1 v₀ := by linarith [hv₀_ge2 1 (by omega)]
        positivity
      rw [div_le_iff₀ hK_pos, ← hftc, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_mul_const]
      refine intervalIntegral.integral_mono_on ha_le_x ?_ ?_ fun t ht => ?_
      · refine ContinuousOn.intervalIntegrable fun t ht => ?_
        rw [Set.uIcc_of_le ha_le_x] at ht
        have ht0 : t ≠ 0 := by linarith [ht.1, ha_ge_25]
        have hlogt0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1, ha_ge_25])).ne'
        have hcont_v : ContinuousAt vfun t :=
          ((Real.continuousAt_log ht0).log hlogt0).sub continuousAt_const
        have hcont_L : ∀ j ≤ m, ContinuousAt (fun u => iterLog j (vfun u)) t := fun j hj =>
          ((hasDerivAt_iterLog j (fun i hi => by linarith [hvfun_ge2 t ht i (by omega)])).continuousAt).comp hcont_v
        have hcont_num : ContinuousAt (fun u => ∑ r ∈ Finset.range (m + 1),
            ∏ j ∈ Finset.Icc (r + 1) m, iterLog j (vfun u)) t :=
          continuousAt_sum_finset _ _ t fun r _ =>
            continuousAt_prod_finset _ _ t fun j hj => hcont_L j (Finset.mem_Icc.mp hj).2
        exact (continuousAt_const.mul (hcont_num.div
          (continuousAt_id.mul (Real.continuousAt_log ht0))
          (mul_ne_zero ht0 hlogt0))).continuousWithinAt
      · refine ContinuousOn.intervalIntegrable fun t ht => ?_
        rw [Set.uIcc_of_le ha_le_x] at ht
        have ht0 : t ≠ 0 := by linarith [ht.1, ha_ge_25]
        have hlogt0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1, ha_ge_25])).ne'
        have hcont_v : ContinuousAt vfun t :=
          ((Real.continuousAt_log ht0).log hlogt0).sub continuousAt_const
        have hcont_L : ∀ j ≤ m, ContinuousAt (fun u => iterLog j (vfun u)) t := fun j hj =>
          ((hasDerivAt_iterLog j (fun i hi => by linarith [hvfun_ge2 t ht i (by omega)])).continuousAt).comp hcont_v
        have hcont_f : ContinuousAt f t :=
          continuousAt_const.mul (continuousAt_prod_finset _ _ t fun j hj =>
            hcont_L j (Finset.mem_Icc.mp hj).2)
        exact ((hcont_f.div (continuousAt_id.mul (Real.continuousAt_log ht0))
          (mul_ne_zero ht0 hlogt0)).mul continuousAt_const).continuousWithinAt
      · have hpd := phi_deriv_le (by omega) (hvfun_ge2 t ht)
        have hL1_mono : iterLog 1 v₀ ≤ iterLog 1 (vfun t) :=
          iterLog_mono (fun j hj => by linarith [hv₀_ge2 j hj]) (hvfun_ge_v0 t ht) 1 (by omega)
        have hK_le : 1 + 2 / iterLog 1 (vfun t) ≤ 1 + 2 / iterLog 1 v₀ := by
          gcongr
          linarith [hv₀_ge2 1 (by omega)]
        have hP_nn : 0 ≤ prodIterLog m (vfun t) :=
          Finset.prod_nonneg fun j hj => by linarith [hvfun_ge2 t ht j (Finset.mem_Icc.mp hj).2]
        have hden_pos : 0 < t * Real.log t :=
          mul_pos (by linarith [ht.1, ha_ge_25]) (Real.log_pos (by linarith [ht.1, ha_ge_25]))
        have hC_pos : 0 ≤ coeffC m := by linarith [coeffC_gt m]
        have hnum : coeffC m * (∑ r ∈ Finset.range (m + 1),
              ∏ j ∈ Finset.Icc (r + 1) m, iterLog j (vfun t)) ≤
            f t * (1 + 2 / iterLog 1 v₀) := by
          dsimp only [f]
          calc coeffC m * (∑ r ∈ Finset.range (m + 1),
                ∏ j ∈ Finset.Icc (r + 1) m, iterLog j (vfun t))
              ≤ coeffC m * ((1 + 2 / iterLog 1 (vfun t)) * prodIterLog m (vfun t)) :=
                mul_le_mul_of_nonneg_left hpd hC_pos
            _ ≤ coeffC m * ((1 + 2 / iterLog 1 v₀) * prodIterLog m (vfun t)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK_le hP_nn) hC_pos
            _ = coeffC m * prodIterLog m (vfun t) * (1 + 2 / iterLog 1 v₀) := by ring
        dsimp only [Dphi]
        rw [mul_div_assoc', div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right hnum hden_pos.le
    -- Combine bounds on `phi m v₀`, boundary term, and `phi m V` vs `phi m U`
    have hphi_V_pos : 0 < phi m V := by
      rw [phi_eq_mul_prodIterLog]
      exact mul_pos (by linarith) (Finset.prod_pos fun j hj => by
        linarith [hvfun_ge2 x (Set.right_mem_Icc.mpr ha_le_x) j (Finset.mem_Icc.mp hj).2])
    have hphi_v0_le : phi m v₀ ≤ (1 / (999 * Real.exp y₀)) * phi m V := by
      rw [phi_eq_mul_prodIterLog, phi_eq_mul_prodIterLog]
      have hP_le : prodIterLog m v₀ ≤ prodIterLog m V :=
        Finset.prod_le_prod (fun j hj => by linarith [hv₀_ge2 j (Finset.mem_Icc.mp hj).2])
          (fun j hj => iterLog_mono (fun i hi => by linarith [hv₀_ge2 i hi]) hv0_lt_V.le j
            (Finset.mem_Icc.mp hj).2)
      have hP_nn : 0 ≤ prodIterLog m V :=
        Finset.prod_nonneg fun j hj => by
          linarith [hvfun_ge2 x (Set.right_mem_Icc.mpr ha_le_x) j (Finset.mem_Icc.mp hj).2]
      have hfac_pos : 0 < 999 * Real.exp y₀ := by positivity
      rw [one_div, inv_mul_eq_div, le_div_iff₀' hfac_pos]
      calc 999 * Real.exp y₀ * (v₀ * prodIterLog m v₀)
          = (999 * Real.exp y₀ * v₀) * prodIterLog m v₀ := by ring
        _ ≤ V * prodIterLog m V := mul_le_mul hV_ge_v0 hP_le
            (Finset.prod_nonneg fun j hj => by linarith [hv₀_ge2 j (Finset.mem_Icc.mp hj).2])
            (by linarith)
    have hbdy_le : (f a / Real.log a) * (mertensM a - Real.log a + 2) ≤
        coeffC m * (1 / (999 * Real.exp y₀)) * phi m V := by
      have hfa_eq : f a = coeffC m * prodIterLog m v₀ := by
        dsimp only [f, vfun, a]; simp [iterLog_succ, iterLog_zero]
      have hloga_ge : 54 ≤ Real.log a := by
        dsimp only [a]; rw [Real.log_exp]
        linarith [Real.add_one_le_exp (v₀ + Real.log 2),
          Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
      have hM_ratio : (mertensM a - Real.log a + 2) / Real.log a ≤ 1 := by
        rw [div_le_iff₀ (by linarith)]
        have hMa := mertensM_le (x := a) (by linarith)
        have hl4 : Real.log 4 ≤ 1.39 := by rw [Real.log_four_eq]; linarith [Real.log_two_lt_d9]
        nlinarith
      have hfa_nn : 0 ≤ f a := by
        rw [hfa_eq]
        exact mul_nonneg (by linarith [coeffC_gt m])
          (Finset.prod_nonneg fun j hj => by linarith [hv₀_ge2 j (Finset.mem_Icc.mp hj).2])
      have hP_le_phi : prodIterLog m v₀ ≤ phi m v₀ := by
        rw [phi_eq_mul_prodIterLog]
        have hP_nn : 0 ≤ prodIterLog m v₀ :=
          Finset.prod_nonneg fun j hj => by linarith [hv₀_ge2 j (Finset.mem_Icc.mp hj).2]
        nlinarith
      calc (f a / Real.log a) * (mertensM a - Real.log a + 2)
          = f a * ((mertensM a - Real.log a + 2) / Real.log a) := by ring
        _ ≤ f a * 1 := mul_le_mul_of_nonneg_left hM_ratio hfa_nn
        _ = coeffC m * prodIterLog m v₀ := by rw [mul_one, hfa_eq]
        _ ≤ coeffC m * phi m v₀ := mul_le_mul_of_nonneg_left hP_le_phi (by linarith [coeffC_gt m])
        _ ≤ coeffC m * ((1 / (999 * Real.exp y₀)) * phi m V) :=
            mul_le_mul_of_nonneg_left hphi_v0_le (by linarith [coeffC_gt m])
        _ = coeffC m * (1 / (999 * Real.exp y₀)) * phi m V := by ring
    -- Compare `phi m V` with `phi m U = ∏_{j=2}^{m+2} iterLog j x`
    have hU_logs_ge2 : ∀ j ≤ m, 2 ≤ iterLog j U := by
      intro j hj
      rw [show iterLog j U = iterLog (j + 2) x from iterLog_add j 2 x]
      have h1 := iterLog_antitone hpos (show j + 2 ≤ m + 2 by omega) le_rfl
      push_cast at htop
      linarith only [h1, htop, hmR]
    have hsub_V := iterLog_sub_ge hU_ge_1e6 (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
      (by linarith [Real.log_two_lt_d9]) hU_logs_ge2
    have hphi_V_ge_U : (1 - (6 * (m : ℝ) + 1) / U) * phi m U ≤ phi m V := by
      rw [phi_eq_mul_prodIterLog, phi_eq_mul_prodIterLog]
      have hV_fac : (1 - 1 / U) * U ≤ V := by
        dsimp only [V]
        have : (1 - 1 / U) * U = U - 1 := by field_simp [show U ≠ 0 by linarith only [hU_ge_1e6]]
        rw [this]; linarith [Real.log_two_lt_d9]
      have hP_fac : (1 - 6 / U) ^ m * prodIterLog m U ≤ prodIterLog m V := by
        unfold prodIterLog
        have hprod := Finset.prod_le_prod (s := Finset.Icc 1 m)
          (f := fun j => (1 - 6 / U) * iterLog j U) (g := fun j => iterLog j V)
          (fun j hj => by
            have h6U : 6 / U ≤ 1 := by rw [div_le_iff₀ (by linarith only [hU_ge_1e6])]; linarith only [hU_ge_1e6]
            exact mul_nonneg (by linarith only [h6U]) (by linarith [hU_logs_ge2 j (Finset.mem_Icc.mp hj).2]))
          (fun j hj => by
            have h1 := (hsub_V j hj).1
            have h2 := hU_logs_ge2 j (Finset.mem_Icc.mp hj).2
            have h6U_nn : 0 ≤ 6 / U := by positivity
            nlinarith only [h1, h2, h6U_nn])
        rw [Finset.prod_mul_distrib, Finset.prod_const] at hprod
        simpa [Nat.card_Icc] using hprod
      have hbern : 1 - 6 * (m : ℝ) / U ≤ (1 - 6 / U) ^ m := by
        have h6U_nn : 0 ≤ 6 / U := by positivity
        have h6U_le1 : 6 / U ≤ 1 := by rw [div_le_iff₀ (by linarith only [hU_ge_1e6])]; linarith only [hU_ge_1e6]
        have h := bernoulli_sub h6U_nn h6U_le1 m
        have heq : (m : ℝ) * (6 / U) = 6 * (m : ℝ) / U := by ring
        linarith only [h, heq]
      have hprod_fac : 1 - (6 * (m : ℝ) + 1) / U ≤ (1 - 1 / U) * (1 - 6 * (m : ℝ) / U) := by
        have hpos_m : 0 ≤ (m : ℝ) := by positivity
        have h1 : (1 - 1 / U) * (1 - 6 * (m : ℝ) / U) =
            1 - (6 * (m : ℝ) + 1) / U + 6 * (m : ℝ) / U ^ 2 := by
          field_simp [show U ≠ 0 by linarith only [hU_ge_1e6]]; ring
        rw [h1]
        linarith only [show 0 ≤ 6 * (m : ℝ) / U ^ 2 by positivity]
      have hPU_nn : 0 ≤ prodIterLog m U :=
        Finset.prod_nonneg fun j hj => by linarith [hU_logs_ge2 j (Finset.mem_Icc.mp hj).2]
      calc (1 - (6 * (m : ℝ) + 1) / U) * (U * prodIterLog m U)
          ≤ ((1 - 1 / U) * (1 - 6 * (m : ℝ) / U)) * (U * prodIterLog m U) :=
            mul_le_mul_of_nonneg_right hprod_fac (mul_nonneg (by linarith only [hU_ge_1e6]) hPU_nn)
        _ = ((1 - 1 / U) * U) * ((1 - 6 * (m : ℝ) / U) * prodIterLog m U) := by ring
        _ ≤ V * ((1 - 6 / U) ^ m * prodIterLog m U) := by
            have h2le : (1 - 6 * (m : ℝ) / U) * prodIterLog m U ≤ (1 - 6 / U) ^ m * prodIterLog m U :=
              mul_le_mul_of_nonneg_right hbern hPU_nn
            have h6mU : 6 * (m : ℝ) / U ≤ 1 := by
              rw [div_le_iff₀ (by linarith only [hU_ge_1e6])]
              have hm_le_e : (m : ℝ) ≤ Real.exp y₀ := by
                dsimp only [y₀]; linarith [Real.add_one_le_exp ((m : ℝ) + 1.99)]
              nlinarith only [hU_ge_big, hv₀_ge_54, hm_le_e, hL1_v₀_54]
            exact mul_le_mul hV_fac h2le (mul_nonneg (by linarith only [h6mU]) hPU_nn)
              (by linarith only [hv0_lt_V, hv₀_ge_54])
        _ ≤ V * prodIterLog m V := mul_le_mul_of_nonneg_left hP_fac (by linarith only [hv0_lt_V, hv₀_ge_54])
    -- Show `(6*m + 1) / U ≤ 1 / (999 * exp y₀)`
    have h6m_le : (6 * (m : ℝ) + 1) / U ≤ 1 / (999 * Real.exp y₀) := by
      rw [div_le_div_iff₀ (by linarith only [hU_ge_1e6]) (by positivity)]
      have hm_le_v0 : (6 * (m : ℝ) + 1) ≤ v₀ := by
        have h1 : Real.exp y₀ ≤ v₀ := by
          have := hv₀_logs 0 (Nat.zero_le m)
          rw [iterLog_zero, Nat.sub_zero] at this
          have hm_eq : m = (m - 1) + 1 := by omega
          have h2 : Real.exp y₀ ≤ Real.exp^[m] y₀ := by
            rw [hm_eq, Function.iterate_succ_apply]
            exact iterExp_ge_self (m - 1) (Real.exp y₀)
          linarith only [this, h2]
        have h2 : 6 * (m : ℝ) + 1 ≤ Real.exp y₀ := by
          have hexp2 := Real.sum_le_exp_of_nonneg (x := y₀) (by linarith only [hy₀_ge]) 4
          simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at hexp2
          norm_num at hexp2
          dsimp only [y₀] at hexp2 ⊢
          have hy3 : (m : ℝ) ^ 2 ≤ ((m : ℝ) + 1.99) ^ 2 := by nlinarith only [hmR]
          nlinarith only [hexp2, hy3, hmR]
        linarith only [h1, h2]
      nlinarith only [hU_ge_big, hm_le_v0, hL1_v₀_54]
    -- Now assemble the final coefficient comparison
    have hG_lb_phiV : coeffC m * ((1 - 1 / (999 * Real.exp y₀)) / (1 + 2 / Real.exp y₀) -
        1 / (999 * Real.exp y₀)) * phi m V ≤ G_total x := by
      have hK1 : 1 + 2 / iterLog 1 v₀ ≤ 1 + 2 / Real.exp y₀ := by
        gcongr
      have hK_pos1 : 0 < 1 + 2 / iterLog 1 v₀ := by
        have : 0 < iterLog 1 v₀ := by linarith only [hL1_v₀, hL1_v₀_54]
        positivity
      have hnum_ge : (1 - 1 / (999 * Real.exp y₀)) * phi m V ≤ phi m V - phi m v₀ := by
        linarith only [hphi_v0_le]
      have h1 : coeffC m * ((1 - 1 / (999 * Real.exp y₀)) * phi m V) / (1 + 2 / Real.exp y₀) ≤
          coeffC m * (phi m V - phi m v₀) / (1 + 2 / iterLog 1 v₀) := by
        calc coeffC m * ((1 - 1 / (999 * Real.exp y₀)) * phi m V) / (1 + 2 / Real.exp y₀)
            ≤ coeffC m * ((1 - 1 / (999 * Real.exp y₀)) * phi m V) / (1 + 2 / iterLog 1 v₀) := by
              refine div_le_div_of_nonneg_left ?_ hK_pos1 hK1
              have : 1 / (999 * Real.exp y₀) ≤ 1 := by
                rw [div_le_iff₀ (by positivity)]; linarith only [hL1_v₀_54]
              exact mul_nonneg (by linarith [coeffC_gt m]) (mul_nonneg (by linarith only [this]) hphi_V_pos.le)
          _ ≤ coeffC m * (phi m V - phi m v₀) / (1 + 2 / iterLog 1 v₀) :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left hnum_ge (by linarith [coeffC_gt m])) hK_pos1.le
      have h2 : coeffC m * ((1 - 1 / (999 * Real.exp y₀)) / (1 + 2 / Real.exp y₀) -
            1 / (999 * Real.exp y₀)) * phi m V =
          coeffC m * ((1 - 1 / (999 * Real.exp y₀)) * phi m V) / (1 + 2 / Real.exp y₀) -
            coeffC m * (1 / (999 * Real.exp y₀)) * phi m V := by ring
      linarith only [h2, h1, hint_lb, habel, hrec_total, hbdy_le]
    -- Show `coeffC (m + 1) ≤ coeffC m * (...) * (1 - 1 / (999 * exp y₀))`
    have hcoeff_step : coeffC (m + 1) ≤
        coeffC m * ((1 - 1 / (999 * Real.exp y₀)) / (1 + 2 / Real.exp y₀) -
          1 / (999 * Real.exp y₀)) * (1 - 1 / (999 * Real.exp y₀)) := by
      have hE_ge : 54 * (2 : ℝ) ^ (m - 2) ≤ Real.exp y₀ := by
        have hdecomp : y₀ = 3.99 + ((m - 2 : ℕ) : ℝ) * 1 := by
          dsimp only [y₀]; rw [Nat.cast_sub hm]; push_cast; ring
        rw [hdecomp, Real.exp_add, Real.exp_nat_mul]
        exact mul_le_mul exp_399_gt.le (pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le _)
          (by positivity) (Real.exp_pos _).le
      have hE_pos : 0 < Real.exp y₀ := Real.exp_pos y₀
      have h2m_pos : (0 : ℝ) < (2 : ℝ) ^ (m - 2) := by positivity
      have hdiff_C : coeffC m - coeffC (m + 1) = 0.05 / (2 : ℝ) ^ (m - 2) := by
        unfold coeffC
        have hsub : m + 1 - 2 = (m - 2) + 1 := by omega
        rw [hsub, pow_succ]
        field_simp [h2m_pos.ne']
        ring
      have hfac_lb : 1 - 2.1 / Real.exp y₀ ≤
          ((1 - 1 / (999 * Real.exp y₀)) / (1 + 2 / Real.exp y₀) -
            1 / (999 * Real.exp y₀)) * (1 - 1 / (999 * Real.exp y₀)) := by
        have h1 : 1 - 2 / Real.exp y₀ ≤ 1 / (1 + 2 / Real.exp y₀) := by
          rw [le_div_iff₀ (by positivity)]
          have : 0 ≤ (2 / Real.exp y₀) ^ 2 := sq_nonneg _
          nlinarith only [this]
        have h1_999_nn : 0 ≤ 1 - 1 / (999 * Real.exp y₀) := by
          have : 1 / (999 * Real.exp y₀) ≤ 1 := by
            rw [div_le_iff₀ (by positivity)]; linarith only [hL1_v₀_54]
          linarith only [this]
        have h2 : (1 - 1 / (999 * Real.exp y₀)) * (1 - 2 / Real.exp y₀) ≤
            (1 - 1 / (999 * Real.exp y₀)) / (1 + 2 / Real.exp y₀) := by
          rw [div_eq_mul_inv (1 - 1 / (999 * Real.exp y₀)), ← one_div (1 + 2 / Real.exp y₀)]
          exact mul_le_mul_of_nonneg_left h1 h1_999_nn
        have h1_999 : 1 / (999 * Real.exp y₀) = (1 / 999) * (1 / Real.exp y₀) := by ring
        have h2_E : 2 / Real.exp y₀ = 2 * (1 / Real.exp y₀) := by ring
        have h21_E : 2.1 / Real.exp y₀ = 2.1 * (1 / Real.exp y₀) := by ring
        have hinv_pos : 0 < 1 / Real.exp y₀ := by positivity
        have hstep1 : 1 - 2.01 * (1 / Real.exp y₀) ≤
            (1 - 1 / (999 * Real.exp y₀)) / (1 + 2 / Real.exp y₀) - 1 / (999 * Real.exp y₀) := by
          nlinarith only [h2, h1_999, h2_E, hinv_pos]
        have hstep2 : (1 - 2.01 * (1 / Real.exp y₀)) * (1 - 1 / (999 * Real.exp y₀)) ≤
            ((1 - 1 / (999 * Real.exp y₀)) / (1 + 2 / Real.exp y₀) -
              1 / (999 * Real.exp y₀)) * (1 - 1 / (999 * Real.exp y₀)) :=
          mul_le_mul_of_nonneg_right hstep1 h1_999_nn
        nlinarith only [hstep2, h1_999, h21_E, hinv_pos]
      have hloss_le : coeffC m * (2.1 / Real.exp y₀) ≤ 0.05 / (2 : ℝ) ^ (m - 2) := by
        have hCm : coeffC m ≤ 1.23 := coeffC_le m
        have hdiv : 2.1 / Real.exp y₀ ≤ 2.1 / (54 * (2 : ℝ) ^ (m - 2)) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hE_ge
        calc coeffC m * (2.1 / Real.exp y₀)
            ≤ 1.23 * (2.1 / (54 * (2 : ℝ) ^ (m - 2))) :=
              mul_le_mul hCm hdiv (by positivity) (by norm_num)
          _ = (1.23 * 2.1 / 54) / (2 : ℝ) ^ (m - 2) := by ring
          _ ≤ 0.05 / (2 : ℝ) ^ (m - 2) := by gcongr; norm_num
      have hCm_pos : 0 < coeffC m := by linarith [coeffC_gt m]
      nlinarith only [hdiff_C, hfac_lb, hloss_le, hCm_pos]
    have hphi_U_eq : phi m U = ∏ j ∈ Finset.Icc 2 (m + 2), iterLog j x := by
      unfold phi
      refine Finset.prod_nbij (· + 2) ?_ ?_ ?_ ?_
      · intro j hj; simp only [Finset.mem_range, Finset.mem_Icc] at hj ⊢; omega
      · intro a _ b _ h; dsimp only at h; omega
      · intro j hj; simp only [Finset.mem_coe, Finset.mem_Icc] at hj
        exact ⟨j - 2, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), by dsimp only; omega⟩
      · intro j _; exact iterLog_add j 2 x
    have hphi_U_nn : 0 ≤ phi m U := by
      rw [hphi_U_eq]
      exact Finset.prod_nonneg fun j hj => by linarith [hpos j (Finset.mem_Icc.mp hj).2]
    have hmid_nn : 0 ≤ coeffC m * ((1 - 1 / (999 * Real.exp y₀)) / (1 + 2 / Real.exp y₀) -
        1 / (999 * Real.exp y₀)) := by
      have hCm_pos : 0 < coeffC m := by linarith [coeffC_gt m]
      have h1 : 0.99 < 1 - 1 / (999 * Real.exp y₀) := by
        have : 1 / (999 * Real.exp y₀) < 0.01 := by
          rw [div_lt_iff₀ (by positivity)]; linarith only [hL1_v₀_54]
        linarith only [this]
      have h2 : 1 + 2 / Real.exp y₀ < 1.05 := by
        have : 2 / Real.exp y₀ < 0.05 := by
          rw [div_lt_iff₀ (by positivity)]; linarith only [hL1_v₀_54]
        linarith only [this]
      have h3 : 0.9 < (1 - 1 / (999 * Real.exp y₀)) / (1 + 2 / Real.exp y₀) := by
        rw [lt_div_iff₀ (by positivity)]; linarith only [h1, h2]
      have h4 : 1 / (999 * Real.exp y₀) < 0.01 := by
        rw [div_lt_iff₀ (by positivity)]; linarith only [hL1_v₀_54]
      nlinarith only [hCm_pos, h3, h4]
    rw [← hphi_U_eq]
    calc coeffC (m + 1) * phi m U
        ≤ coeffC m * ((1 - 1 / (999 * Real.exp y₀)) / (1 + 2 / Real.exp y₀) -
            1 / (999 * Real.exp y₀)) * (1 - 1 / (999 * Real.exp y₀)) * phi m U :=
          mul_le_mul_of_nonneg_right hcoeff_step hphi_U_nn
      _ = coeffC m * ((1 - 1 / (999 * Real.exp y₀)) / (1 + 2 / Real.exp y₀) -
            1 / (999 * Real.exp y₀)) * ((1 - 1 / (999 * Real.exp y₀)) * phi m U) := by ring
      _ ≤ coeffC m * ((1 - 1 / (999 * Real.exp y₀)) / (1 + 2 / Real.exp y₀) -
            1 / (999 * Real.exp y₀)) * phi m V := by
          refine mul_le_mul_of_nonneg_left ?_ hmid_nn
          exact le_trans (mul_le_mul_of_nonneg_right (by linarith only [h6m_le]) hphi_U_nn) hphi_V_ge_U
      _ ≤ G_total x := hG_lb_phiV

set_option maxHeartbeats 1200000 in
/-- Main regime theorem: when all `iterLog i N ≥ 1` for `i ≤ k`, `k ≥ 4`, and `iterLog k N ≥ k`. -/
theorem main_regime (N k : ℕ) (hk : 4 ≤ k)
    (hpos : ∀ i ≤ k, 1 ≤ iterLog i (N : ℝ)) (hkN : (k : ℝ) ≤ iterLog k (N : ℝ)) :
    (N : ℝ) / Real.log N * ∏ i ∈ Finset.Icc 3 k, iterLog i (N : ℝ) ≤ Erdos321.R N := by
  have hL4 : 4 ≤ iterLog 4 (N : ℝ) := by
    have := iterLog_antitone hpos hk le_rfl
    have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hL3 : 54 < iterLog 3 (N : ℝ) := by
    have h := (iterLog_exp_step hpos (i := 3) (by omega)).symm
    rw [h]
    exact exp_399_gt.trans_le (Real.exp_le_exp.mpr (by linarith))
  have hL3_ge_k : (k : ℝ) ≤ iterLog 3 (N : ℝ) := by
    exact hkN.trans (iterLog_antitone hpos (by omega) le_rfl)
  have hL2_eq : iterLog 2 (N : ℝ) = Real.exp (iterLog 3 (N : ℝ)) :=
    (iterLog_exp_step hpos (i := 2) (by omega)).symm
  have hL2_ge : 1000000000 ≤ iterLog 2 (N : ℝ) := by
    rw [hL2_eq]
    calc (1000000000 : ℝ) ≤ (2 : ℝ) ^ 30 := by norm_num
      _ ≤ (Real.exp 1) ^ 30 := by gcongr; linarith [Real.exp_one_gt_two]
      _ = Real.exp 30 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ Real.exp (iterLog 3 (N : ℝ)) := Real.exp_le_exp.mpr (by linarith)
  have hL2_ge_k : 10000 * (k : ℝ) ≤ iterLog 2 (N : ℝ) := by
    rw [hL2_eq]
    have hsplit : Real.exp (iterLog 3 (N : ℝ)) =
        Real.exp (iterLog 3 (N : ℝ) / 2) * Real.exp (iterLog 3 (N : ℝ) / 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [hsplit]
    have h1 : 20000 ≤ Real.exp (iterLog 3 (N : ℝ) / 2) := by
      calc (20000 : ℝ) ≤ (2 : ℝ) ^ 15 := by norm_num
        _ ≤ (Real.exp 1) ^ 15 := by gcongr; linarith [Real.exp_one_gt_two]
        _ = Real.exp 15 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ Real.exp (iterLog 3 (N : ℝ) / 2) := Real.exp_le_exp.mpr (by linarith)
    have h2 : (k : ℝ) / 2 ≤ Real.exp (iterLog 3 (N : ℝ) / 2) := by
      linarith [Real.add_one_le_exp (iterLog 3 (N : ℝ) / 2)]
    nlinarith
  have hL1_eq : Real.log (N : ℝ) = Real.exp (iterLog 2 (N : ℝ)) := by
    have := (iterLog_exp_step hpos (i := 1) (by omega)).symm
    simpa [iterLog_succ, iterLog_zero] using this
  have hlogN_ge : 1000000000 ≤ Real.log (N : ℝ) := by
    rw [hL1_eq]; linarith [Real.add_one_le_exp (iterLog 2 (N : ℝ))]
  have hN_eq : (N : ℝ) = Real.exp (Real.log (N : ℝ)) := by
    have := (iterLog_exp_step hpos (i := 0) (by omega)).symm
    simpa [iterLog_succ, iterLog_zero] using this
  have hN_pos : 0 < (N : ℝ) := by rw [hN_eq]; exact Real.exp_pos _
  -- Set `X = log N / 8` and lower-bound `G_total X`
  let X : ℝ := Real.log (N : ℝ) / 8
  have hL1_X : Real.log X = iterLog 2 (N : ℝ) - Real.log 8 := by
    dsimp only [X]
    rw [Real.log_div (by linarith) (by norm_num)]
    rfl
  have hlog8_le : Real.log 8 ≤ 3 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast; linarith [Real.log_two_lt_d9]
  have hL2_logs_ge2 : ∀ j ≤ k - 2, 2 ≤ iterLog j (iterLog 2 (N : ℝ)) := by
    intro j hj
    rw [iterLog_add]
    have := iterLog_antitone hpos (show j + 2 ≤ k by omega) le_rfl
    have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast hk
    linarith only [this, hkN, hk4]
  have hsub_X := iterLog_sub_ge (m := k - 2) (u := iterLog 2 (N : ℝ)) (δ := Real.log 8)
    (by linarith only [hL2_ge]) (Real.log_nonneg (by norm_num)) hlog8_le hL2_logs_ge2
  have hiter_X_shift : ∀ j ≤ k - 2, iterLog (j + 1) X = iterLog j (iterLog 2 (N : ℝ) - Real.log 8) := by
    intro j _
    rw [iterLog_succ_inner, hL1_X]
  have hiter_N_shift : ∀ j ≤ k - 2, iterLog j (iterLog 2 (N : ℝ)) = iterLog (j + 2) (N : ℝ) := by
    intro j _; exact iterLog_add j 2 (N : ℝ)
  have hX_pos : ∀ j ≤ k - 1, 1 ≤ iterLog j X := by
    intro j hj
    cases j with
    | zero => rw [iterLog_zero]; dsimp only [X]; linarith only [hlogN_ge]
    | succ j =>
      rw [hiter_X_shift j (by omega)]
      cases j with
      | zero => rw [iterLog_zero]; linarith only [hL2_ge, hlog8_le]
      | succ j => exact (hsub_X (j + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)).2
  have hX_top : ((k - 2 : ℕ) : ℝ) + 1.99 ≤ iterLog (k - 1) X := by
    have hk1 : k - 1 = (k - 2) + 1 := by omega
    rw [hk1, hiter_X_shift (k - 2) le_rfl]
    have h1 := (hsub_X (k - 2) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)).1
    rw [hiter_N_shift (k - 2) le_rfl, Nat.sub_add_cancel (by omega)] at h1
    have h6u : 6 / iterLog 2 (N : ℝ) ≤ 0.01 := by
      rw [div_le_iff₀ (by linarith only [hL2_ge])]; linarith only [hL2_ge]
    rw [Nat.cast_sub (by omega)]; push_cast; linarith only [h1, hkN, h6u]
  have hG_ind := G_total_ge_ind (k - 2) (by omega) X (by
    have hk1 : k - 2 + 1 = k - 1 := by omega
    rw [hk1]; exact hX_pos) (by
    have hk1 : k - 2 + 1 = k - 1 := by omega
    rw [hk1]; exact hX_top)
  have hprod_X_ge : (1 - 0.001) * ∏ i ∈ Finset.Icc 3 k, iterLog i (N : ℝ) ≤
      ∏ j ∈ Finset.Icc 2 (k - 2 + 1), iterLog j X := by
    have hrew : ∏ j ∈ Finset.Icc 2 (k - 2 + 1), iterLog j X =
        ∏ i ∈ Finset.Icc 3 k, iterLog (i - 1) X := by
      refine Finset.prod_nbij (· + 1) ?_ ?_ ?_ ?_
      · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
      · intro a _ b _ h; dsimp only at h; omega
      · intro i hi; simp only [Finset.mem_coe, Finset.mem_Icc] at hi
        exact ⟨i - 1, Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), by dsimp only; omega⟩
      · intro j _; rfl
    rw [hrew]
    let eps : ℝ := 6 / iterLog 2 (N : ℝ)
    have heps_nn : 0 ≤ eps := by positivity
    have heps_le : eps ≤ 1 := by dsimp only [eps]; rw [div_le_iff₀ (by linarith only [hL2_ge])]; linarith only [hL2_ge]
    have hpow_le : (1 - eps) ^ (k - 2) * ∏ i ∈ Finset.Icc 3 k, iterLog i (N : ℝ) ≤
        ∏ i ∈ Finset.Icc 3 k, iterLog (i - 1) X := by
      have hprod := Finset.prod_le_prod (s := Finset.Icc 3 k)
        (f := fun i => (1 - eps) * iterLog i (N : ℝ)) (g := fun i => iterLog (i - 1) X)
        (fun i hi => mul_nonneg (by linarith only [heps_le]) (by linarith [hpos i (Finset.mem_Icc.mp hi).2]))
        (fun i hi => by
          have hi3 : 3 ≤ i := (Finset.mem_Icc.mp hi).1
          have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
          have h1 := (hsub_X (i - 2) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)).1
          rw [hiter_N_shift (i - 2) (by omega), Nat.sub_add_cancel (by omega)] at h1
          have h2 := hiter_X_shift (i - 2) (by omega)
          rw [show i - 2 + 1 = i - 1 by omega] at h2
          rw [h2]
          have hLi1 : 1 ≤ iterLog i (N : ℝ) := hpos i hik
          dsimp only [eps]
          nlinarith only [h1, hLi1, heps_nn])
      rw [Finset.prod_mul_distrib, Finset.prod_const] at hprod
      have hcard : #(Finset.Icc 3 k) = k - 2 := by simp
      rwa [hcard] at hprod
    have hbern : 1 - ((k - 2 : ℕ) : ℝ) * eps ≤ (1 - eps) ^ (k - 2) :=
      bernoulli_sub heps_nn heps_le (k - 2)
    have hkeps : ((k - 2 : ℕ) : ℝ) * eps ≤ 0.001 := by
      dsimp only [eps]
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]
      have : ((k - 2 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 2
      nlinarith
    have hP_nn : 0 ≤ ∏ i ∈ Finset.Icc 3 k, iterLog i (N : ℝ) :=
      Finset.prod_nonneg fun i hi => by linarith [hpos i (Finset.mem_Icc.mp hi).2]
    calc (1 - 0.001) * ∏ i ∈ Finset.Icc 3 k, iterLog i (N : ℝ)
        ≤ (1 - ((k - 2 : ℕ) : ℝ) * eps) * ∏ i ∈ Finset.Icc 3 k, iterLog i (N : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) hP_nn
      _ ≤ (1 - eps) ^ (k - 2) * ∏ i ∈ Finset.Icc 3 k, iterLog i (N : ℝ) :=
          mul_le_mul_of_nonneg_right hbern hP_nn
      _ ≤ ∏ i ∈ Finset.Icc 3 k, iterLog (i - 1) X := hpow_le
  have hGX_ge : 1.12 * ∏ i ∈ Finset.Icc 3 k, iterLog i (N : ℝ) ≤ G_total X := by
    have hP_nn : 0 ≤ ∏ i ∈ Finset.Icc 3 k, iterLog i (N : ℝ) :=
      Finset.prod_nonneg fun i hi => by linarith [hpos i (Finset.mem_Icc.mp hi).2]
    have hC := coeffC_gt (k - 2)
    nlinarith
  -- Construct witness `A ⊆ Finset.Icc 1 N`
  let Cset : Finset (ℕ × Finset ℕ) :=
    A0 ×ˢ ((Nat.primesLE ⌊X⌋₊).powerset.filter IsPrimeChain)
  let dval : ℕ × Finset ℕ → ℕ := fun c => c.1 * ∏ p ∈ c.2, p
  let Pcut : ℕ := max 25 (chainThresh ⌊X⌋₊)
  let block (c : ℕ × Finset ℕ) : Finset ℕ :=
    (Nat.primesLE (N / dval c) \ Nat.primesLE Pcut).image (fun p => p * dval c)
  let A : Finset ℕ := Cset.biUnion block
  have hX_ge_2 : 2 ≤ ⌊X⌋₊ := Nat.le_floor (by dsimp only [X]; linarith)
  have hd_pos : ∀ c ∈ Cset, 0 < dval c := by
    intro ⟨a, S⟩ hc
    have ha := (Finset.mem_product.mp hc).1
    have hS := (Finset.mem_filter.mp (Finset.mem_product.mp hc).2).2
    exact isValidElem_pos ⟨a, ha, S, hS, rfl⟩
  have hA_sub : A ⊆ Finset.Icc 1 N := by
    intro n hn
    obtain ⟨c, hc, hnc⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hnc
    have hpp := Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hp).1
    have hple := Nat.le_of_mem_primesLE (Finset.mem_sdiff.mp hp).1
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos hpp.pos (hd_pos c hc),
      (Nat.mul_le_mul_right (dval c) hple).trans (Nat.div_mul_le_self N (dval c))⟩
  have hA_valid : ∀ n ∈ A, IsValidElem n := by
    intro n hn
    obtain ⟨⟨a, S⟩, hc, hnc⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hnc
    have ha := (Finset.mem_product.mp hc).1
    have hSf := Finset.mem_filter.mp (Finset.mem_product.mp hc).2
    have hSsub : S ⊆ Nat.primesLE ⌊X⌋₊ := Finset.mem_powerset.mp hSf.1
    have hSch : IsPrimeChain S := hSf.2
    have hpp := Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hp).1
    have hp_gt_Pcut : Pcut < p := by
      by_contra h
      exact (Finset.mem_sdiff.mp hp).2 (Nat.mem_primesLE.mpr ⟨by omega, hpp⟩)
    have hp_25 : 25 < p := lt_of_le_of_lt (le_max_left _ _) hp_gt_Pcut
    have hq_lt : ∀ q ∈ S, chainThresh q < p ∧ q < p := by
      intro q hq
      have hq_le : q ≤ ⌊X⌋₊ := Nat.le_of_mem_primesLE (hSsub hq)
      have hT : chainThresh q < p :=
        (chainThresh_mono hq_le).trans_lt (lt_of_le_of_lt (le_max_right _ _) hp_gt_Pcut)
      have hq25 : 25 < q := (hSch.1 q hq).2
      have hqT : q < chainThresh q := by
        have hm : q ∈ (Finset.Ioc 25 q).filter Nat.Prime :=
          Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hq25, le_rfl⟩, (hSch.1 q hq).1⟩
        have := Finset.single_le_prod' (f := fun r => r + 1) (fun r _ => Nat.succ_le_succ (Nat.zero_le r)) hm
        unfold chainThresh; omega
      exact ⟨hT, hqT.trans hT⟩
    have hp_notS : p ∉ S := fun h => (hq_lt p h).2.false
    have hins_ch : IsPrimeChain (insert p S) := by
      refine ⟨fun r hr => ?_, fun q hq r hr hqr => ?_⟩
      · rcases Finset.mem_insert.mp hr with rfl | hrS
        · exact ⟨hpp, hp_25⟩
        · exact hSch.1 r hrS
      · rcases Finset.mem_insert.mp hq with rfl | hqS <;> rcases Finset.mem_insert.mp hr with rfl | hrS
        · omega
        · have := (hq_lt r hrS).2; omega
        · exact (hq_lt q hqS).1
        · exact hSch.2 q hqS r hrS hqr
    refine ⟨a, ha, insert p S, hins_ch, ?_⟩
    dsimp only [dval]
    rw [Finset.prod_insert hp_notS]
    ring
  -- Blocks are pairwise disjoint and each has size `#(primesLE (N / d c) \ primesLE Pcut)`
  have hdisj : Set.PairwiseDisjoint (Cset : Set (ℕ × Finset ℕ)) block := by
    intro ⟨a₁, S₁⟩ h1 ⟨a₂, S₂⟩ h2 hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    obtain ⟨p₁, hp₁, hEq1⟩ := Finset.mem_image.mp hn1
    obtain ⟨p₂, hp₂, hEq2⟩ := Finset.mem_image.mp hn2
    have hEq : p₁ * dval (a₁, S₁) = p₂ * dval (a₂, S₂) := hEq1.trans hEq2.symm
    have hp1_pr := Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hp₁).1
    have hp2_pr := Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hp₂).1
    have hp1_gt : Pcut < p₁ := by
      by_contra h; exact (Finset.mem_sdiff.mp hp₁).2 (Nat.mem_primesLE.mpr ⟨by omega, hp1_pr⟩)
    have hp2_gt : Pcut < p₂ := by
      by_contra h; exact (Finset.mem_sdiff.mp hp₂).2 (Nat.mem_primesLE.mpr ⟨by omega, hp2_pr⟩)
    have hS1_lt : ∀ r ∈ S₁, r < p₂ := by
      intro r hr
      have hSf := Finset.mem_filter.mp (Finset.mem_product.mp h1).2
      have hrle := Nat.le_of_mem_primesLE (Finset.mem_powerset.mp hSf.1 hr)
      have hr25 := (hSf.2.1 r hr).2
      have hm : r ∈ (Finset.Ioc 25 r).filter Nat.Prime :=
        Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hr25, le_rfl⟩, (hSf.2.1 r hr).1⟩
      have h1' := Finset.single_le_prod' (f := fun q => q + 1) (fun q _ => Nat.succ_le_succ (Nat.zero_le q)) hm
      have h2' : r < chainThresh r := by unfold chainThresh; omega
      exact h2'.trans_le ((chainThresh_mono hrle).trans (le_max_right _ _)) |>.trans hp2_gt
    have hS2_lt : ∀ r ∈ S₂, r < p₁ := by
      intro r hr
      have hSf := Finset.mem_filter.mp (Finset.mem_product.mp h2).2
      have hrle := Nat.le_of_mem_primesLE (Finset.mem_powerset.mp hSf.1 hr)
      have hr25 := (hSf.2.1 r hr).2
      have hm : r ∈ (Finset.Ioc 25 r).filter Nat.Prime :=
        Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hr25, le_rfl⟩, (hSf.2.1 r hr).1⟩
      have h1' := Finset.single_le_prod' (f := fun q => q + 1) (fun q _ => Nat.succ_le_succ (Nat.zero_le q)) hm
      have h2' : r < chainThresh r := by unfold chainThresh; omega
      exact h2'.trans_le ((chainThresh_mono hrle).trans (le_max_right _ _)) |>.trans hp1_gt
    have hp_eq : p₁ = p₂ := by
      have hdvd : p₁ ∣ p₂ * dval (a₂, S₂) := hEq ▸ dvd_mul_right p₁ _
      rcases hp1_pr.dvd_mul.mp hdvd with h12 | h1d
      · exact (Nat.prime_dvd_prime_iff_eq hp1_pr hp2_pr).mp h12
      · have hSf := Finset.mem_filter.mp (Finset.mem_product.mp h2).2
        have hmem := prime_dvd_validElem_mem (Finset.mem_product.mp h2).1 hSf.2 hp1_pr
          (lt_of_le_of_lt (le_max_left _ _) hp1_gt) h1d
        exact absurd (hS2_lt p₁ hmem) (lt_irrefl p₁)
    subst hp_eq
    have hd_eq : dval (a₁, S₁) = dval (a₂, S₂) := Nat.eq_of_mul_eq_mul_left hp1_pr.pos hEq
    have hS_eq : S₁ = S₂ := by
      ext r
      have hmem1 : r ∈ S₁ ↔ r.Prime ∧ 25 < r ∧ r ∣ dval (a₁, S₁) := by
        have hSf := Finset.mem_filter.mp (Finset.mem_product.mp h1).2
        refine ⟨fun hr => ⟨(hSf.2.1 r hr).1, (hSf.2.1 r hr).2,
          dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hr) _⟩, fun ⟨hrp, hr25, hrd⟩ =>
          prime_dvd_validElem_mem (Finset.mem_product.mp h1).1 hSf.2 hrp hr25 hrd⟩
      have hmem2 : r ∈ S₂ ↔ r.Prime ∧ 25 < r ∧ r ∣ dval (a₂, S₂) := by
        have hSf := Finset.mem_filter.mp (Finset.mem_product.mp h2).2
        refine ⟨fun hr => ⟨(hSf.2.1 r hr).1, (hSf.2.1 r hr).2,
          dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hr) _⟩, fun ⟨hrp, hr25, hrd⟩ =>
          prime_dvd_validElem_mem (Finset.mem_product.mp h2).1 hSf.2 hrp hr25 hrd⟩
      rw [hmem1, hmem2, hd_eq]
    subst hS_eq
    have hPpos : 0 < ∏ r ∈ S₁, r :=
      Finset.prod_pos fun r hr => ((Finset.mem_filter.mp (Finset.mem_product.mp h1).2).2.1 r hr).1.pos
    have ha_eq : a₁ = a₂ := Nat.eq_of_mul_eq_mul_right hPpos hd_eq
    subst ha_eq
    exact hne rfl
  have hcard_A : #A = ∑ c ∈ Cset, #(Nat.primesLE (N / dval c) \ Nat.primesLE Pcut) := by
    rw [Finset.card_biUnion hdisj]
    refine Finset.sum_congr rfl fun c hc => ?_
    exact Finset.card_image_of_injective _ (mul_left_injective₀ (hd_pos c hc).ne')
  -- Bound `dval c ≤ N ^ (1/4)` and `Pcut ≤ N ^ (1/4)`
  have hN_pow_quarter : Real.exp (Real.log (N : ℝ) / 4) = (N : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [Real.rpow_def_of_pos hN_pos]; ring_nf
  have hPcut_le : (Pcut : ℝ) ≤ Real.exp (Real.log (N : ℝ) / 4) := by
    have h1 : (25 : ℝ) ≤ Real.exp (Real.log (N : ℝ) / 4) := by
      linarith [Real.add_one_le_exp (Real.log (N : ℝ) / 4)]
    have h2 : (chainThresh ⌊X⌋₊ : ℝ) ≤ Real.exp (Real.log (N : ℝ) / 4) := by
      have hlt : chainThresh ⌊X⌋₊ < 6 ^ ⌊X⌋₊ := chainThresh_lt_six_pow hX_ge_2
      have hlog6 : Real.log 6 < 2 := by
        rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
        linarith [Real.log_two_lt_d9, Real.log_three_lt_d9]
      calc (chainThresh ⌊X⌋₊ : ℝ) ≤ ((6 ^ ⌊X⌋₊ : ℕ) : ℝ) := by exact_mod_cast hlt.le
        _ = Real.exp ((⌊X⌋₊ : ℝ) * Real.log 6) := by
            push_cast; rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), mul_comm]
        _ ≤ Real.exp (X * 2) := by
            refine Real.exp_le_exp.mpr ?_
            have hfl : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le (by dsimp only [X]; linarith)
            nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 6)]
        _ = Real.exp (Real.log (N : ℝ) / 4) := by dsimp only [X]; ring_nf
    dsimp only [Pcut]
    push_cast
    exact max_le h1 h2
  have hd_le : ∀ c ∈ Cset, (dval c : ℝ) ≤ Real.exp (Real.log (N : ℝ) / 4) := by
    intro ⟨a, S⟩ hc
    have ha4 : a ≤ 4 := A0_le_four (Finset.mem_product.mp hc).1
    have hSsub : S ⊆ Nat.primesLE ⌊X⌋₊ :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp (Finset.mem_product.mp hc).2).1
    have hprod_le : ∏ p ∈ S, p ≤ 4 ^ ⌊X⌋₊ := by
      calc ∏ p ∈ S, p ≤ ∏ p ∈ Nat.primesLE ⌊X⌋₊, p :=
            Finset.prod_le_prod_of_subset_of_one_le' hSsub
              (fun p hp _ => (Nat.prime_of_mem_primesLE hp).one_le)
        _ = primorial ⌊X⌋₊ := (primorial_eq_prod_primesLE _).symm
        _ ≤ 4 ^ ⌊X⌋₊ := primorial_le_four_pow _
    have hlog4 : Real.log 4 < 1.4 := by rw [Real.log_four_eq]; linarith [Real.log_two_lt_d9]
    calc (dval (a, S) : ℝ) ≤ (4 : ℝ) * ((4 ^ ⌊X⌋₊ : ℕ) : ℝ) := by
          dsimp only [dval]; exact_mod_cast Nat.mul_le_mul ha4 hprod_le
      _ = Real.exp (Real.log 4 + (⌊X⌋₊ : ℝ) * Real.log 4) := by
          push_cast
          rw [Real.exp_add, Real.exp_log (by norm_num), ← Real.rpow_natCast,
            Real.rpow_def_of_pos (by norm_num), mul_comm (Real.log 4) (⌊X⌋₊ : ℝ)]
      _ ≤ Real.exp (Real.log (N : ℝ) / 4) := by
          refine Real.exp_le_exp.mpr ?_
          have hfl : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le (by dsimp only [X]; linarith)
          dsimp only [X] at hfl ⊢
          nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  -- Lower bound each summand in `#A`
  have hterm_ge : ∀ c ∈ Cset,
      0.91 * ((N : ℝ) / Real.log (N : ℝ)) * (1 / (dval c : ℝ)) ≤
        (#(Nat.primesLE (N / dval c) \ Nat.primesLE Pcut) : ℝ) := by
    intro c hc
    have hd_posR : (0 : ℝ) < dval c := by exact_mod_cast hd_pos c hc
    have hd_ub := hd_le c hc
    have hq_ge : Real.exp (3 * Real.log (N : ℝ) / 4) ≤ (N : ℝ) / dval c := by
      rw [le_div_iff₀ hd_posR]
      calc Real.exp (3 * Real.log (N : ℝ) / 4) * dval c
          ≤ Real.exp (3 * Real.log (N : ℝ) / 4) * Real.exp (Real.log (N : ℝ) / 4) :=
            mul_le_mul_of_nonneg_left hd_ub (Real.exp_pos _).le
        _ = Real.exp (Real.log (N : ℝ)) := by rw [← Real.exp_add]; ring_nf
        _ = N := hN_eq.symm
    have hq_exp100 : Real.exp 100 ≤ (N : ℝ) / dval c :=
      (Real.exp_le_exp.mpr (by linarith)).trans hq_ge
    have hpi := primeCounting_ge_chebyshev30 hq_exp100
    have hfl_eq : ⌊(N : ℝ) / dval c⌋₊ = N / dval c := by
      rw [Nat.floor_div_eq_div]
    rw [hfl_eq] at hpi
    have hlog_le : Real.log ((N : ℝ) / dval c) ≤ Real.log (N : ℝ) := by
      refine Real.log_le_log (div_pos hN_pos hd_posR) ?_
      exact div_le_self hN_pos.le (by exact_mod_cast hd_pos c hc)
    have hlog_pos : 0 < Real.log ((N : ℝ) / dval c) := by
      have h1 : (100 : ℝ) ≤ Real.log ((N : ℝ) / dval c) :=
        (Real.le_log_iff_exp_le (div_pos hN_pos hd_posR)).mpr hq_exp100
      linarith
    have hpi_ge : 0.919 * ((N : ℝ) / dval c) / Real.log (N : ℝ) ≤ (Nat.primeCounting (N / dval c) : ℝ) := by
      exact (div_le_div_of_nonneg_left (by positivity) hlog_pos hlog_le).trans hpi
    have hcard_sdiff : (Nat.primeCounting (N / dval c) : ℝ) - (Pcut : ℝ) ≤
        (#(Nat.primesLE (N / dval c) \ Nat.primesLE Pcut) : ℝ) := by
      have h1 : #(Nat.primesLE (N / dval c)) ≤
          #(Nat.primesLE (N / dval c) \ Nat.primesLE Pcut) + #(Nat.primesLE Pcut) := by
        have hunion : Nat.primesLE (N / dval c) ⊆
            (Nat.primesLE (N / dval c) \ Nat.primesLE Pcut) ∪ Nat.primesLE Pcut := by
          intro p hp; by_cases h : p ∈ Nat.primesLE Pcut <;> simp [Finset.mem_union, hp, h]
        exact (Finset.card_le_card hunion).trans (Finset.card_union_le _ _)
      have h2 : #(Nat.primesLE Pcut) ≤ Pcut := by
        calc #(Nat.primesLE Pcut) ≤ #(Finset.Icc 1 Pcut) :=
              Finset.card_le_card fun p hp =>
                Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hp).one_le, Nat.le_of_mem_primesLE hp⟩
          _ = Pcut := by simp
      rw [Nat.primesLE_card_eq_primeCounting] at h1
      have h3 : (Nat.primeCounting (N / dval c) : ℝ) ≤
          (#(Nat.primesLE (N / dval c) \ Nat.primesLE Pcut) : ℝ) + (Pcut : ℝ) := by
        exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)
      linarith
    have hPcut_tiny : (Pcut : ℝ) ≤ 0.009 * ((N : ℝ) / dval c) / Real.log (N : ℝ) := by
      rw [le_div_iff₀ (by linarith only [hlogN_ge])]
      have hhalf : Real.log (N : ℝ) ≤ 0.009 * Real.exp (Real.log (N : ℝ) / 2) := by
        have h1 : Real.log (N : ℝ) / 2 ≤ Real.exp (Real.log (N : ℝ) / 4) := by
          have := Real.sum_le_exp_of_nonneg (x := Real.log (N : ℝ) / 4) (by linarith only [hlogN_ge]) 3
          simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at this
          norm_num at this
          nlinarith only [this, hlogN_ge]
        have h2 : 1000 ≤ Real.exp (Real.log (N : ℝ) / 4) := by
          linarith only [Real.add_one_le_exp (Real.log (N : ℝ) / 4), hlogN_ge]
        have hmul : Real.exp (Real.log (N : ℝ) / 2) =
            Real.exp (Real.log (N : ℝ) / 4) * Real.exp (Real.log (N : ℝ) / 4) := by
          rw [← Real.exp_add]; ring_nf
        rw [hmul]
        nlinarith only [h1, h2]
      calc (Pcut : ℝ) * Real.log (N : ℝ)
          ≤ Real.exp (Real.log (N : ℝ) / 4) * (0.009 * Real.exp (Real.log (N : ℝ) / 2)) :=
            mul_le_mul hPcut_le hhalf (by linarith only [hlogN_ge]) (Real.exp_pos _).le
        _ = 0.009 * Real.exp (3 * Real.log (N : ℝ) / 4) := by
            rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]; ring_nf
        _ ≤ 0.009 * ((N : ℝ) / dval c) := mul_le_mul_of_nonneg_left hq_ge (by norm_num)
    have hrew : 0.91 * ((N : ℝ) / Real.log (N : ℝ)) * (1 / (dval c : ℝ)) =
        0.91 * ((N : ℝ) / dval c) / Real.log (N : ℝ) := by ring
    have hsub_eq : 0.919 * ((N : ℝ) / dval c) / Real.log (N : ℝ) -
        0.009 * ((N : ℝ) / dval c) / Real.log (N : ℝ) =
        0.91 * ((N : ℝ) / dval c) / Real.log (N : ℝ) := by ring
    linarith only [hrew, hsub_eq, hpi_ge, hPcut_tiny, hcard_sdiff]
  have hsum_dval : ∑ c ∈ Cset, (1 : ℝ) / (dval c : ℝ) = G_total X := by
    dsimp only [Cset, dval]
    rw [Finset.sum_product]
    have hA0_recip : ∑ a ∈ A0, (1 : ℝ) / (a : ℝ) = 25 / 12 := by
      unfold A0
      simp only [Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2, 3, 4} : Finset ℕ)),
        Finset.sum_insert (by decide : (2 : ℕ) ∉ ({3, 4} : Finset ℕ)),
        Finset.sum_insert (by decide : (3 : ℕ) ∉ ({4} : Finset ℕ)),
        Finset.sum_singleton, Nat.cast_ofNat]
      norm_num
    calc ∑ a ∈ A0, ∑ S ∈ (Nat.primesLE ⌊X⌋₊).powerset.filter IsPrimeChain,
            (1 : ℝ) / ((a * ∏ p ∈ S, p : ℕ) : ℝ)
        = ∑ a ∈ A0, ((1 : ℝ) / (a : ℝ)) * G_above X := by
          refine Finset.sum_congr rfl fun a _ => ?_
          unfold G_above
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun S _ => ?_
          push_cast; ring
      _ = (∑ a ∈ A0, (1 : ℝ) / (a : ℝ)) * G_above X := (Finset.sum_mul _ _ _).symm
      _ = G_total X := by rw [hA0_recip]; rfl
  have hcard_R : (#A : ℝ) ≤ (Erdos321.R N : ℝ) := by
    exact_mod_cast card_le_R hA_sub (primeChain_injOn hA_valid)
  have hcard_lb : 0.91 * ((N : ℝ) / Real.log (N : ℝ)) * G_total X ≤ (#A : ℝ) := by
    rw [hcard_A, Nat.cast_sum, ← hsum_dval, Finset.mul_sum]
    exact Finset.sum_le_sum hterm_ge
  have hprod_nn : 0 ≤ ∏ i ∈ Finset.Icc 3 k, iterLog i (N : ℝ) :=
    Finset.prod_nonneg fun i hi => by linarith [hpos i (Finset.mem_Icc.mp hi).2]
  have hN_div_nn : 0 ≤ (N : ℝ) / Real.log (N : ℝ) := div_nonneg hN_pos.le (by linarith only [hlogN_ge])
  nlinarith only [hcard_R, hcard_lb, hGX_ge, hprod_nn, hN_div_nn]

/- Section 5: Non-positive iterated-logarithm edge case and `OMA.solution` -/

lemma iter_log_prod_le {n : ℕ} (hn : 1 ≤ n) :
    ∀ x : ℝ, (∀ j < n, 1 < iterLog j x) →
      ∏ j ∈ Finset.range n, iterLog j x ≤ Real.exp (3 * x / 4) := by
  induction n, hn using Nat.le_induction with
  | base =>
    intro x hx
    simp only [Finset.range_one, Finset.prod_singleton, iterLog_zero]
    have hx1 : 1 < x := hx 0 (by omega)
    have hlog : Real.log x ≤ 3 * x / 4 := by
      have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 * x / 4 by linarith)
      rw [Real.log_div (by linarith) (by norm_num), Real.log_mul (by norm_num) (by linarith)] at h1
      have h43 : Real.log 4 - Real.log 3 < 1 := by
        rw [Real.log_four_eq]
        linarith [Real.log_two_lt_d9, Real.log_three_gt_d9]
      linarith
    calc x = Real.exp (Real.log x) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp (3 * x / 4) := Real.exp_le_exp.mpr hlog
  | succ n hn ih =>
    intro x hx
    have hx1 : 1 < x := hx 0 (by omega)
    have hsplit : ∏ j ∈ Finset.range (n + 1), iterLog j x =
        x * ∏ j ∈ Finset.range n, iterLog j (Real.log x) := by
      rw [Finset.prod_range_succ', iterLog_zero, mul_comm]
      congr 1
    rw [hsplit]
    have hih := ih (Real.log x) (fun j hj => by
      rw [← iterLog_succ_inner]; exact hx (j + 1) (by omega))
    have h73 : 7 * Real.log x ≤ 3 * x := by
      have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 * x / 7 by linarith)
      rw [Real.log_div (by linarith) (by norm_num), Real.log_mul (by norm_num) (by linarith)] at h1
      have hlog73 : Real.log 7 - Real.log 3 < 1 := by
        have hlt : (7 : ℝ) / 3 < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        have h := (Real.log_lt_iff_lt_exp (by norm_num)).mpr hlt
        rwa [Real.log_div (by norm_num) (by norm_num)] at h
      linarith
    calc x * ∏ j ∈ Finset.range n, iterLog j (Real.log x)
        ≤ x * Real.exp (3 * Real.log x / 4) := mul_le_mul_of_nonneg_left hih (by linarith)
      _ = Real.exp (Real.log x) * Real.exp (3 * Real.log x / 4) := by
          rw [Real.exp_log (by linarith)]
      _ = Real.exp (7 * Real.log x / 4) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (3 * x / 4) := Real.exp_le_exp.mpr (by linarith)

lemma excursion_prod_le {u : ℕ → ℝ} (hu_nn : ∀ t, 0 ≤ u t)
    (hu_step : ∀ t, u (t + 1) = |Real.log (u t)|)
    {a b : ℕ} (hab : a < b) (ha : u a ≤ 1) (hmid : ∀ t ∈ Finset.Ioo a b, 1 < u t) :
    (b = a + 1 → ∏ i ∈ Finset.Ico a b, u i ≤ 1) ∧
    (a + 2 ≤ b → ∏ i ∈ Finset.Ico a b, u i ≤ Real.exp (-u (a + 1) / 4)) := by
  constructor
  · rintro rfl
    rw [Nat.Ico_succ_singleton, Finset.prod_singleton]
    exact ha
  · intro hab2
    have hu1_gt : 1 < u (a + 1) := hmid (a + 1) (Finset.mem_Ioo.mpr ⟨by omega, by omega⟩)
    have hua_ne : u a ≠ 0 := by
      intro h0
      have := hu_step a
      rw [h0, Real.log_zero, abs_zero] at this
      linarith
    have hua_pos : 0 < u a := lt_of_le_of_ne (hu_nn a) (Ne.symm hua_ne)
    have hlog_ua : Real.log (u a) ≤ 0 := Real.log_nonpos hua_pos.le ha
    have hua_eq : u a = Real.exp (-u (a + 1)) := by
      have h1 : u (a + 1) = -Real.log (u a) := by rw [hu_step a, abs_of_nonpos hlog_ua]
      rw [h1, neg_neg, Real.exp_log hua_pos]
    have hu_iter : ∀ j < b - (a + 1), u (a + 1 + j) = iterLog j (u (a + 1)) ∧
        1 < iterLog j (u (a + 1)) := by
      intro j hj
      induction j with
      | zero =>
        exact ⟨by simp [iterLog_zero], hu1_gt⟩
      | succ j ih =>
        obtain ⟨heq, hgt⟩ := ih (by omega)
        have hstep := hu_step (a + 1 + j)
        rw [heq] at hstep
        have hpos_log : 0 < Real.log (iterLog j (u (a + 1))) := Real.log_pos hgt
        have heq' : u (a + 1 + (j + 1)) = iterLog (j + 1) (u (a + 1)) := by
          rw [show a + 1 + (j + 1) = a + 1 + j + 1 by omega, hstep, abs_of_pos hpos_log, iterLog_succ]
        have hmem : a + 1 + (j + 1) ∈ Finset.Ioo a b := Finset.mem_Ioo.mpr ⟨by omega, by omega⟩
        exact ⟨heq', heq' ▸ hmid _ hmem⟩
    have hsplit : Finset.Ico a b = insert a (Finset.Ico (a + 1) b) := by
      ext i; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [hsplit, Finset.prod_insert (by simp)]
    have htail_eq : ∏ i ∈ Finset.Ico (a + 1) b, u i =
        ∏ j ∈ Finset.range (b - (a + 1)), iterLog j (u (a + 1)) := by
      refine Finset.prod_nbij (· - (a + 1)) ?_ ?_ ?_ ?_
      · intro i hi; simp only [Finset.mem_Ico, Finset.mem_range] at hi ⊢; omega
      · intro i₁ h1 i₂ h2 h; simp only [Finset.mem_coe, Finset.mem_Ico] at h1 h2; dsimp only at h; omega
      · intro j hj; simp only [Finset.mem_coe, Finset.mem_range] at hj
        exact ⟨a + 1 + j, Finset.mem_coe.mpr (Finset.mem_Ico.mpr ⟨by omega, by omega⟩), by dsimp only; omega⟩
      · intro i hi
        have hi1 : a + 1 ≤ i := (Finset.mem_Ico.mp hi).1
        have hib : i < b := (Finset.mem_Ico.mp hi).2
        have h := (hu_iter (i - (a + 1)) (by omega)).1
        rwa [Nat.add_sub_cancel' hi1] at h
    rw [htail_eq]
    have hprod_le := iter_log_prod_le (n := b - (a + 1)) (by omega) (u (a + 1))
      (fun j hj => (hu_iter j hj).2)
    calc u a * ∏ j ∈ Finset.range (b - (a + 1)), iterLog j (u (a + 1))
        ≤ Real.exp (-u (a + 1)) * Real.exp (3 * u (a + 1) / 4) := by
          rw [hua_eq]; exact mul_le_mul_of_nonneg_left hprod_le (Real.exp_pos _).le
      _ = Real.exp (-u (a + 1) / 4) := by rw [← Real.exp_add]; ring_nf

lemma small_to_small_prod_le {u : ℕ → ℝ} (hu_nn : ∀ t, 0 ≤ u t)
    (hu_step : ∀ t, u (t + 1) = |Real.log (u t)|) :
    ∀ d a b : ℕ, b - a = d → a ≤ b → u a ≤ 1 → u b ≤ 1 →
      ∏ i ∈ Finset.Ico a b, u i ≤ 1 := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro a b hd hab ha hb
    rcases eq_or_lt_of_le hab with rfl | hlt
    · simp
    · let S := (Finset.Ioc a b).filter (fun t => u t ≤ 1)
      have hS_ne : S.Nonempty := ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hlt, le_rfl⟩, hb⟩⟩
      let c := S.min' hS_ne
      have hc_mem : c ∈ S := Finset.min'_mem S hS_ne
      have hc_Ioc := (Finset.mem_filter.mp hc_mem).1
      have hc_le1 : u c ≤ 1 := (Finset.mem_filter.mp hc_mem).2
      have hac : a < c := (Finset.mem_Ioc.mp hc_Ioc).1
      have hcb : c ≤ b := (Finset.mem_Ioc.mp hc_Ioc).2
      have hmid : ∀ t ∈ Finset.Ioo a c, 1 < u t := by
        intro t ht
        by_contra h
        push Not at h
        have htS : t ∈ S := Finset.mem_filter.mpr
          ⟨Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioo.mp ht).1, (Finset.mem_Ioo.mp ht).2.le.trans hcb⟩, h⟩
        have := Finset.min'_le S t htS
        have := (Finset.mem_Ioo.mp ht).2
        omega
      have hfirst : ∏ i ∈ Finset.Ico a c, u i ≤ 1 := by
        have hex := excursion_prod_le hu_nn hu_step hac ha hmid
        by_cases hc1 : c = a + 1
        · exact hex.1 hc1
        · have hle := hex.2 (by omega)
          have hpos : 0 ≤ u (a + 1) := hu_nn (a + 1)
          exact hle.trans (Real.exp_le_one_iff.mpr (by linarith))
      have hrest : ∏ i ∈ Finset.Ico c b, u i ≤ 1 :=
        ih (b - c) (by omega) c b rfl hcb hc_le1 hb
      have hunion : Finset.Ico a b = Finset.Ico a c ∪ Finset.Ico c b := by
        ext i; simp only [Finset.mem_Ico, Finset.mem_union]; omega
      have hdisj : Disjoint (Finset.Ico a c) (Finset.Ico c b) := by
        rw [Finset.disjoint_left]; intro i h1 h2
        simp only [Finset.mem_Ico] at h1 h2; omega
      rw [hunion, Finset.prod_union hdisj]
      have h1nn : 0 ≤ ∏ i ∈ Finset.Ico a c, u i := Finset.prod_nonneg fun i _ => hu_nn i
      have h2nn : 0 ≤ ∏ i ∈ Finset.Ico c b, u i := Finset.prod_nonneg fun i _ => hu_nn i
      nlinarith

lemma primesLE_injOn (N : ℕ) :
    Set.InjOn (fun (S : Finset ℕ) ↦ ∑ n ∈ S, (1 : ℚ) / n) (Nat.primesLE N).powerset := by
  intro X hX Y hY hsum
  have hX' : X ⊆ Nat.primesLE N := Finset.mem_powerset.mp hX
  have hY' : Y ⊆ Nat.primesLE N := Finset.mem_powerset.mp hY
  have hdiff : ∑ n ∈ X \ Y, (1 : ℚ) / n = ∑ n ∈ Y \ X, (1 : ℚ) / n := by
    have h1 : ∑ n ∈ X \ Y, (1 : ℚ) / n + ∑ n ∈ X ∩ Y, (1 : ℚ) / n = ∑ n ∈ X, (1 : ℚ) / n := by
      rw [← Finset.sum_union (Finset.disjoint_left.mpr fun a h1 h2 =>
        (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp h2).2), Finset.sdiff_union_inter]
    have h2 : ∑ n ∈ Y \ X, (1 : ℚ) / n + ∑ n ∈ Y ∩ X, (1 : ℚ) / n = ∑ n ∈ Y, (1 : ℚ) / n := by
      rw [← Finset.sum_union (Finset.disjoint_left.mpr fun a h1 h2 =>
        (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp h2).2), Finset.sdiff_union_inter]
    rw [Finset.inter_comm] at h2
    linarith
  by_contra hne
  have hU_ne : ((X \ Y) ∪ (Y \ X)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    rw [Finset.union_eq_empty, Finset.sdiff_eq_empty_iff_subset,
      Finset.sdiff_eq_empty_iff_subset] at hemp
    exact hne (Finset.Subset.antisymm hemp.1 hemp.2)
  obtain ⟨p, hpU⟩ := hU_ne
  have hp_pr : p.Prime := by
    rcases Finset.mem_union.mp hpU with h | h
    · exact Nat.prime_of_mem_primesLE (hX' (Finset.mem_sdiff.mp h).1)
    · exact Nat.prime_of_mem_primesLE (hY' (Finset.mem_sdiff.mp h).1)
  let U := (X \ Y) ∪ (Y \ X)
  let M : ℕ := ∏ q ∈ U.erase p, q
  have hp_ndvd_M : ¬ p ∣ M := by
    intro hdiv
    rw [hp_pr.prime.dvd_finsetProd_iff] at hdiv
    obtain ⟨q, hq, hpq⟩ := hdiv
    have hq_pr : q.Prime := by
      rcases Finset.mem_union.mp (Finset.mem_of_mem_erase hq) with h | h
      · exact Nat.prime_of_mem_primesLE (hX' (Finset.mem_sdiff.mp h).1)
      · exact Nat.prime_of_mem_primesLE (hY' (Finset.mem_sdiff.mp h).1)
    exact Finset.ne_of_mem_erase hq ((Nat.prime_dvd_prime_iff_eq hp_pr hq_pr).mp hpq).symm
  -- Multiply `hdiff` by `p * M` to get `± M = p * (integer)`
  have hmul : ((p * M : ℕ) : ℚ) * ∑ n ∈ X \ Y, (1 : ℚ) / n =
      ((p * M : ℕ) : ℚ) * ∑ n ∈ Y \ X, (1 : ℚ) / n := congrArg (((p * M : ℕ) : ℚ) * ·) hdiff
  have heval : ∀ S ⊆ U,
      ((p * M : ℕ) : ℚ) * ∑ n ∈ S, (1 : ℚ) / n =
        (if p ∈ S then (M : ℚ) else 0) +
          (p : ℚ) * ∑ q ∈ S.erase p, ((M / q : ℕ) : ℚ) := by
    intro S hS
    have hsplit : ∑ n ∈ S, (1 : ℚ) / n =
        (if p ∈ S then (1 : ℚ) / p else 0) + ∑ q ∈ S.erase p, (1 : ℚ) / q := by
      by_cases hpS : p ∈ S
      · rw [if_pos hpS, Finset.add_sum_erase S (fun q => (1 : ℚ) / q) hpS]
      · rw [if_neg hpS, zero_add, Finset.erase_eq_of_notMem hpS]
    rw [hsplit, mul_add]
    congr 1
    · split_ifs
      · have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp_pr.ne_zero
        push_cast; field_simp [hp0]
      · simp
    · rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q hq => ?_
      have hqU : q ∈ U.erase p :=
        Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hq, hS (Finset.mem_of_mem_erase hq)⟩
      have hqdvd : q ∣ M := Finset.dvd_prod_of_mem _ hqU
      have hq_pr : q.Prime := by
        rcases Finset.mem_union.mp (Finset.mem_of_mem_erase hqU) with h | h
        · exact Nat.prime_of_mem_primesLE (hX' (Finset.mem_sdiff.mp h).1)
        · exact Nat.prime_of_mem_primesLE (hY' (Finset.mem_sdiff.mp h).1)
      have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq_pr.ne_zero
      push_cast; field_simp [hq0]
      have hnat : p * M = p * q * (M / q) := by
        calc p * M = p * (q * (M / q)) := by rw [Nat.mul_div_cancel' hqdvd]
          _ = p * q * (M / q) := by ring
      exact_mod_cast hnat
  rw [heval (X \ Y) Finset.subset_union_left, heval (Y \ X) Finset.subset_union_right] at hmul
  have hp_xor : (p ∈ X \ Y ∧ p ∉ Y \ X) ∨ (p ∉ X \ Y ∧ p ∈ Y \ X) := by
    rcases Finset.mem_union.mp hpU with h | h
    · exact Or.inl ⟨h, fun h' => Finset.disjoint_left.mp disjoint_sdiff_sdiff h h'⟩
    · exact Or.inr ⟨fun h' => Finset.disjoint_left.mp disjoint_sdiff_sdiff h' h, h⟩
  have hp_dvd_M : (p : ℤ) ∣ (M : ℤ) := by
    rcases hp_xor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_pos h1, if_neg h2] at hmul
      let Rint : ℤ := ∑ q ∈ (Y \ X).erase p, ((M / q : ℕ) : ℤ) -
        ∑ q ∈ (X \ Y).erase p, ((M / q : ℕ) : ℤ)
      have heqZ : ((M : ℤ) : ℚ) = (((p : ℤ) * Rint : ℤ) : ℚ) := by
        simp only [Rint, Int.cast_mul, Int.cast_sub, Int.cast_sum, Int.cast_natCast]
        linarith
      exact ⟨Rint, Rat.intCast_injective heqZ⟩
    · rw [if_neg h1, if_pos h2] at hmul
      let Rint : ℤ := ∑ q ∈ (X \ Y).erase p, ((M / q : ℕ) : ℤ) -
        ∑ q ∈ (Y \ X).erase p, ((M / q : ℕ) : ℤ)
      have heqZ : ((M : ℤ) : ℚ) = (((p : ℤ) * Rint : ℤ) : ℚ) := by
        simp only [Rint, Int.cast_mul, Int.cast_sub, Int.cast_sum, Int.cast_natCast]
        linarith
      exact ⟨Rint, Rat.intCast_injective heqZ⟩
  exact hp_ndvd_M (Int.natCast_dvd_natCast.mp hp_dvd_M)

lemma primeCounting_le_R (N : ℕ) : Nat.primeCounting N ≤ Erdos321.R N := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  refine card_le_R ?_ (primesLE_injOn N)
  intro p hp
  exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hp).one_le, Nat.le_of_mem_primesLE hp⟩

lemma N_div_log_le_four_R {N : ℕ} (hN : 2 ≤ N) :
    (N : ℝ) / Real.log N ≤ 4 * (Erdos321.R N : ℝ) := by
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  by_cases hN10 : N < 10
  · have hA0_sub : ∀ S : Finset ℕ, S ⊆ A0 → S ⊆ Finset.Icc 1 N → #S ≤ Erdos321.R N := by
      intro S hSA hSN
      exact card_le_R hSN (A0_injOn.mono (Finset.powerset_mono.mpr hSA))
    by_cases hN4 : 4 ≤ N
    · have hR4 : (4 : ℝ) ≤ Erdos321.R N := by
        have h := hA0_sub A0 Finset.Subset.rfl (fun a ha =>
          Finset.mem_Icc.mpr ⟨by simp only [A0, Finset.mem_insert, Finset.mem_singleton] at ha; omega,
            (A0_le_four ha).trans hN4⟩)
        have hcard : #A0 = 4 := by decide
        rw [hcard] at h; exact_mod_cast h
      have hlog4 : 1.38 ≤ Real.log (N : ℝ) := by
        have h1 : Real.log 4 ≤ Real.log (N : ℝ) :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hN4)
        rw [Real.log_four_eq] at h1
        linarith [Real.log_two_gt_d9]
      rw [div_le_iff₀ hlogN_pos]
      have hN9 : (N : ℝ) ≤ 9 := by exact_mod_cast (show N ≤ 9 by omega)
      nlinarith
    · have hN23 : N = 2 ∨ N = 3 := by omega
      rcases hN23 with rfl | rfl
      · have hR2 : (2 : ℝ) ≤ Erdos321.R 2 := by
          have h := hA0_sub {1, 2} (by decide) (by decide)
          have hcard : #({1, 2} : Finset ℕ) = 2 := by decide
          rw [hcard] at h; exact_mod_cast h
        rw [div_le_iff₀ hlogN_pos]
        have hl2 := Real.log_two_gt_d9
        push_cast at hlogN_pos ⊢
        nlinarith
      · have hR3 : (3 : ℝ) ≤ Erdos321.R 3 := by
          have h := hA0_sub {1, 2, 3} (by decide) (by decide)
          have hcard : #({1, 2, 3} : Finset ℕ) = 3 := by decide
          rw [hcard] at h; exact_mod_cast h
        rw [div_le_iff₀ hlogN_pos]
        have hl3 := Real.log_three_gt_d9
        push_cast at hlogN_pos ⊢
        nlinarith
  · push Not at hN10
    have hpi := Chebyshev.pi_ge N
    have hR_ge : (Nat.primeCounting N : ℝ) ≤ Erdos321.R N := by exact_mod_cast primeCounting_le_R N
    have hlogN1 : Real.log ((N : ℝ) + 1) ≤ (N : ℝ) / 4 + 0.65 := by
      have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((N : ℝ) + 1) / 4 by positivity)
      rw [Real.log_div (by positivity) (by norm_num), Real.log_four_eq] at h1
      linarith [Real.log_two_lt_d9]
    have hNR : (10 : ℝ) ≤ N := by exact_mod_cast hN10
    have hnum : (N : ℝ) / 4 ≤ (N : ℝ) * Real.log 2 - Real.log ((N : ℝ) + 1) := by
      nlinarith [Real.log_two_gt_d9]
    have hdiv : (N : ℝ) / 4 / Real.log N ≤ Erdos321.R N :=
      (div_le_div_of_nonneg_right hnum hlogN_pos.le).trans (hpi.trans hR_ge)
    have hrew : (N : ℝ) / 4 / Real.log N = (N : ℝ) / Real.log N / 4 := by ring
    linarith

lemma abs_iterLog_two_gt {N : ℕ} (hN : 2 ≤ N) : 1 / 12 < |iterLog 2 (N : ℝ)| := by
  have hexp12 : Real.exp (1 / 12) < 1.09 := by
    have h := Real.exp_bound (x := (1 / 12 : ℝ)) (n := 4) (by norm_num) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
    norm_num at h
    linarith [(abs_le.mp h).2]
  rcases (show N = 2 ∨ N = 3 ∨ 4 ≤ N by omega) with rfl | rfl | hN4
  · rw [iterLog_succ, iterLog_succ, iterLog_zero]
    have hl2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hl2_lt : Real.log (2 : ℝ) < 0.7 := by linarith [Real.log_two_lt_d9]
    have hll2 : Real.log (Real.log (2 : ℝ)) ≤ -0.3 := by
      have h := Real.log_le_sub_one_of_pos hl2_pos
      linarith
    push_cast
    rw [abs_of_neg (by linarith)]
    linarith
  · rw [iterLog_succ, iterLog_succ, iterLog_zero]
    push_cast
    have hl3 : Real.exp (1 / 12) < Real.log 3 := by linarith [Real.log_three_gt_d9]
    have hll3 : 1 / 12 < Real.log (Real.log 3) := (Real.lt_log_iff_exp_lt (by linarith [Real.exp_pos (1 / 12)])).mpr hl3
    rw [abs_of_pos (by linarith)]
    exact hll3
  · rw [iterLog_succ, iterLog_succ, iterLog_zero]
    have hlN : Real.exp (1 / 12) < Real.log (N : ℝ) := by
      have h1 : Real.log 4 ≤ Real.log (N : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hN4)
      rw [Real.log_four_eq] at h1
      linarith [Real.log_two_gt_d9]
    have hllN : 1 / 12 < Real.log (Real.log (N : ℝ)) :=
      (Real.lt_log_iff_exp_lt (by linarith [Real.exp_pos (1 / 12)])).mpr hlN
    rw [abs_of_pos (by linarith)]
    exact hllN

lemma abs_iterLog_three_lt_exp_one {N : ℕ} (hN2 : 2 ≤ N) (hN15 : N ≤ 15) :
    |iterLog 3 (N : ℝ)| < Real.exp 1 := by
  have h12 := abs_iterLog_two_gt hN2
  have hlt1 : |iterLog 2 (N : ℝ)| < 1 := by
    rw [iterLog_succ, iterLog_succ, iterLog_zero]
    rcases (show N = 2 ∨ 3 ≤ N by omega) with rfl | hN3
    · push_cast
      have hl2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      have hl2_gt : Real.exp (-1) < Real.log (2 : ℝ) := by
        linarith [Real.exp_neg_one_lt_d9, Real.log_two_gt_d9]
      have hl2_lt : Real.log (2 : ℝ) < 1 := by linarith [Real.log_two_lt_d9]
      have hll_gt : -1 < Real.log (Real.log (2 : ℝ)) :=
        (Real.lt_log_iff_exp_lt hl2_pos).mpr hl2_gt
      have hll_lt : Real.log (Real.log (2 : ℝ)) < 0 := Real.log_neg hl2_pos hl2_lt
      rw [abs_of_neg hll_lt]; linarith
    · have hlN_gt : 1 < Real.log (N : ℝ) := by
        have h := Real.log_le_log (by norm_num) (by exact_mod_cast hN3 : (3 : ℝ) ≤ N)
        linarith [Real.log_three_gt_d9]
      have hlN_lt : Real.log (N : ℝ) < Real.exp 1 := by
        have h1 : Real.log (N : ℝ) ≤ Real.log 15 :=
          Real.log_le_log (by positivity) (by exact_mod_cast hN15)
        have h15 : Real.log 15 = Real.log 3 + Real.log 5 := by
          rw [show (15 : ℝ) = 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
        linarith [Real.log_three_lt_d9, Real.log_five_lt_d9, Real.exp_one_gt_d9]
      have hll_pos : 0 < Real.log (Real.log (N : ℝ)) := Real.log_pos hlN_gt
      have hll_lt : Real.log (Real.log (N : ℝ)) < 1 := by
        calc Real.log (Real.log (N : ℝ)) < Real.log (Real.exp 1) :=
              Real.log_lt_log (by linarith) hlN_lt
          _ = 1 := Real.log_exp 1
      rw [abs_of_pos hll_pos]; exact hll_lt
  rw [iterLog_succ, ← Real.log_abs]
  have hneg : Real.log |iterLog 2 (N : ℝ)| < 0 := Real.log_neg (by linarith) hlt1
  rw [abs_of_neg hneg]
  have hlog12 : -Real.log |iterLog 2 (N : ℝ)| < Real.log 12 := by
    have h1 : Real.log (1 / 12) < Real.log |iterLog 2 (N : ℝ)| := Real.log_lt_log (by norm_num) h12
    rw [one_div, Real.log_inv] at h1
    linarith
  have h12_lt : Real.log 12 < Real.exp 1 := by
    have h12' : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
      rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]; norm_num
    linarith [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.exp_one_gt_d9]
  linarith

lemma edge_exp_dominates {k : ℕ} (hk : 5 ≤ k) :
    4 * Real.exp 5 * (k : ℝ) ^ k * Real.exp (-Real.exp k / 4) ≤ 1 := by
  have hkR : (5 : ℝ) ≤ k := by exact_mod_cast hk
  have hlogk : Real.log (k : ℝ) ≤ (k : ℝ) / 5 + 1 := by
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (k : ℝ) / 5 by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    linarith [Real.log_five_lt_d9]
  have hexp_lb : 7 + (k : ℝ) + (k : ℝ) ^ 2 / 5 ≤ Real.exp (k : ℝ) / 4 := by
    have hsum := Real.sum_le_exp_of_nonneg (x := (k : ℝ)) (by linarith) 6
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at hsum
    norm_num at hsum
    have hk2 : 5 * (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    have hk3 : 5 * (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 := by nlinarith
    have hk4 : 25 * (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 4 := by nlinarith
    have hk5 : 125 * (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 5 := by nlinarith
    linarith
  have hlog4 : Real.log 4 < 2 := by rw [Real.log_four_eq]; linarith [Real.log_two_lt_d9]
  have h1 : Real.log (4 * Real.exp 5 * (k : ℝ) ^ k) ≤ Real.exp (k : ℝ) / 4 := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (Real.exp_pos 5).ne', Real.log_exp, Real.log_pow]
    nlinarith
  have h2 : 4 * Real.exp 5 * (k : ℝ) ^ k ≤ Real.exp (Real.exp (k : ℝ) / 4) := by
    calc 4 * Real.exp 5 * (k : ℝ) ^ k
        = Real.exp (Real.log (4 * Real.exp 5 * (k : ℝ) ^ k)) :=
          (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (Real.exp (k : ℝ) / 4) := Real.exp_le_exp.mpr h1
  calc 4 * Real.exp 5 * (k : ℝ) ^ k * Real.exp (-Real.exp (k : ℝ) / 4)
      ≤ Real.exp (Real.exp (k : ℝ) / 4) * Real.exp (-Real.exp (k : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = Real.exp 0 := by rw [← Real.exp_add]; ring_nf
    _ = 1 := Real.exp_zero

set_option maxHeartbeats 1200000 in
/-- Edge regime theorem: handles the case where some intermediate `Real.log^[i] N < 1`. -/
theorem edge_regime (N k : ℕ) (hk : 4 ≤ k)
    (hkN : (k : ℝ) ≤ iterLog k (N : ℝ)) (hnot : ¬ ∀ i ≤ k, 1 ≤ iterLog i (N : ℝ)) :
    (N : ℝ) / Real.log N * ∏ i ∈ Finset.Icc 3 k, iterLog i (N : ℝ) ≤ Erdos321.R N := by
  let x : ℕ → ℝ := fun i => iterLog i (N : ℝ)
  let u : ℕ → ℝ := fun i => |x i|
  have hu_nn : ∀ t, 0 ≤ u t := fun t => abs_nonneg _
  have hu_step : ∀ t, u (t + 1) = |Real.log (u t)| := by
    intro t; dsimp only [u, x]; rw [iterLog_succ, Real.log_abs]
  have hN2 : 2 ≤ N := by
    by_contra hlt
    have hN01 : N = 0 ∨ N = 1 := by omega
    have hx_zero : ∀ i ≥ 1, x i = 0 := by
      intro i hi
      induction i, hi using Nat.le_induction with
      | base =>
        dsimp only [x]; rw [iterLog_succ, iterLog_zero]
        rcases hN01 with rfl | rfl <;> simp
      | succ i hi ih =>
        dsimp only [x] at ih ⊢; rw [iterLog_succ, ih, Real.log_zero]
    have hxk := hx_zero k (by omega)
    have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast hk
    dsimp only [x] at hxk
    linarith
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let Slt : Finset ℕ := (Finset.range (k + 1)).filter (fun i => x i < 1)
  have hSlt_ne : Slt.Nonempty := by
    push Not at hnot
    obtain ⟨i, hik, hi⟩ := hnot
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hi⟩⟩
  let r := Slt.max' hSlt_ne
  let m := Slt.min' hSlt_ne
  have hr_mem : r ∈ Slt := Finset.max'_mem Slt hSlt_ne
  have hr_lt1 : x r < 1 := (Finset.mem_filter.mp hr_mem).2
  have hr_le_k : r ≤ k := by
    have := Finset.mem_range.mp (Finset.mem_filter.mp hr_mem).1; omega
  have hr_lt_k : r < k := by
    rcases eq_or_lt_of_le hr_le_k with heq | hlt
    · exfalso
      have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast hk
      have : x k < 1 := heq ▸ hr_lt1
      dsimp only [x] at this; linarith
    · exact hlt
  have htail_ge1 : ∀ t ∈ Finset.Icc (r + 1) k, 1 ≤ x t := by
    intro t ht
    by_contra hlt
    push Not at hlt
    have htS : t ∈ Slt := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp ht).2; omega), hlt⟩
    have := Finset.le_max' Slt t htS
    have := (Finset.mem_Icc.mp ht).1
    omega
  have hxr1_ge_k : (k : ℝ) ≤ x (r + 1) := by
    have haux : ∀ j ≤ k - (r + 1), x (r + 1 + j) ≤ x (r + 1) := by
      intro j hj
      induction j with
      | zero => simp
      | succ j ih =>
        have hstep : x (r + 1 + (j + 1)) = Real.log (x (r + 1 + j)) := by
          dsimp only [x]; rw [show r + 1 + (j + 1) = r + 1 + j + 1 by omega, iterLog_succ]
        have hpos_j : 1 ≤ x (r + 1 + j) := htail_ge1 _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        rw [hstep]
        exact (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith [ih (by omega)])
    have h := haux (k - (r + 1)) le_rfl
    rw [Nat.add_sub_cancel' (by omega)] at h
    exact hkN.trans h
  have hur_ge : Real.exp (k : ℝ) ≤ u r := by
    have h1 : Real.log (u r) = x (r + 1) := by
      dsimp only [u, x]; rw [iterLog_succ, Real.log_abs]
    have hur_pos : 0 < u r := by
      by_contra h0
      have : u r = 0 := le_antisymm (not_lt.mp h0) (hu_nn r)
      rw [this, Real.log_zero] at h1
      have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    calc Real.exp (k : ℝ) ≤ Real.exp (x (r + 1)) := Real.exp_le_exp.mpr hxr1_ge_k
      _ = Real.exp (Real.log (u r)) := by rw [h1]
      _ = u r := Real.exp_log hur_pos
  have hxr_neg : x r ≤ -Real.exp (k : ℝ) := by
    have hexp_gt1 : 1 < Real.exp (k : ℝ) := by
      have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast hk
      linarith [Real.add_one_le_exp (k : ℝ)]
    have hxr_lt0 : x r < 0 := by
      by_contra hge
      push Not at hge
      have : u r = x r := abs_of_nonneg hge
      linarith
    have : u r = -x r := abs_of_neg hxr_lt0
    linarith
  have hr_ge1 : 1 ≤ r := by
    by_contra h0
    have hr0 : r = 0 := by omega
    have : x 0 = (N : ℝ) := rfl
    have hN2R : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    rw [hr0] at hr_lt1; linarith
  have hur_prev_le : u (r - 1) ≤ Real.exp (-Real.exp (k : ℝ)) := by
    have h1 : Real.log (u (r - 1)) = x r := by
      dsimp only [u, x]
      rw [Real.log_abs, ← iterLog_succ, Nat.sub_add_cancel hr_ge1]
    have hpos_prev : 0 < u (r - 1) := by
      by_contra h0
      have : u (r - 1) = 0 := le_antisymm (not_lt.mp h0) (hu_nn _)
      rw [this, Real.log_zero] at h1
      linarith [Real.exp_pos (k : ℝ)]
    calc u (r - 1) = Real.exp (Real.log (u (r - 1))) := (Real.exp_log hpos_prev).symm
      _ = Real.exp (x r) := by rw [h1]
      _ ≤ Real.exp (-Real.exp (k : ℝ)) := Real.exp_le_exp.mpr hxr_neg
  have hexp_neg_lt : Real.exp (-Real.exp (k : ℝ)) < 1 / 12 := by
    have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast hk
    have h1 : (12 : ℝ) < Real.exp (Real.exp (k : ℝ)) := by
      have h2 : (5 : ℝ) ≤ Real.exp (k : ℝ) := by linarith [Real.add_one_le_exp (k : ℝ)]
      calc (12 : ℝ) < (2 : ℝ) ^ 4 := by norm_num
        _ ≤ (Real.exp 1) ^ 4 := by gcongr; linarith [Real.exp_one_gt_two]
        _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ Real.exp (Real.exp (k : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith
  have hr_ge4 : 4 ≤ r := by
    by_contra hlt
    rcases (show r = 1 ∨ r = 2 ∨ r = 3 by omega) with hr1 | hr2 | hr3
    · have : x 1 = Real.log (N : ℝ) := by dsimp only [x]; rw [iterLog_succ, iterLog_zero]
      rw [hr1] at hxr_neg; linarith [Real.exp_pos (k : ℝ)]
    · have hu1 : u 1 = Real.log (N : ℝ) := by
        dsimp only [u, x]; rw [iterLog_succ, iterLog_zero, abs_of_pos hlogN_pos]
      have hl2 : 1 / 12 < Real.log (N : ℝ) := by
        have h := Real.log_le_log (by norm_num) (by exact_mod_cast hN2 : (2 : ℝ) ≤ N)
        linarith [Real.log_two_gt_d9]
      rw [hr2] at hur_prev_le; norm_num at hur_prev_le; linarith
    · have h2 := abs_iterLog_two_gt hN2
      rw [hr3] at hur_prev_le; norm_num at hur_prev_le
      dsimp only [u, x] at hur_prev_le; linarith
  have hk_ge5 : 5 ≤ k := by omega
  have hm_mem : m ∈ Slt := Finset.min'_mem Slt hSlt_ne
  have hm_lt1 : x m < 1 := (Finset.mem_filter.mp hm_mem).2
  have hm_le_r : m ≤ r := Finset.min'_le Slt r hr_mem
  have hm_ge1 : 1 ≤ m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    have hN2R : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    rw [hm0] at hm_lt1; dsimp only [x] at hm_lt1; rw [iterLog_zero] at hm_lt1; linarith
  have hpre_ge1 : ∀ i < m, 1 ≤ x i := by
    intro i hi
    by_contra hlt
    push Not at hlt
    have hiS : i ∈ Slt := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), hlt⟩
    have := Finset.min'_le Slt i hiS
    omega
  have hm_lt_r : m < r := by
    rcases eq_or_lt_of_le hm_le_r with heq | hlt
    · exfalso
      have hprev : 1 ≤ x (r - 1) := hpre_ge1 (r - 1) (by omega)
      have hxr0 : 0 ≤ x r := by
        dsimp only [x]
        rw [← Nat.sub_add_cancel hr_ge1, iterLog_succ]
        exact Real.log_nonneg hprev
      linarith [Real.exp_pos (k : ℝ)]
    · exact hlt
  let s := max m 3
  have hs_ge3 : 3 ≤ s := le_max_right m 3
  have hs_le_r1 : s ≤ r - 1 := max_le (by omega) (by omega)
  have hus_lt_e : u s < Real.exp 1 := by
    by_cases hm3 : 3 ≤ m
    · have hs_eq : s = m := max_eq_left hm3
      rw [hs_eq]
      have hprev : 1 ≤ x (m - 1) := hpre_ge1 (m - 1) (by omega)
      have hxm_nn : 0 ≤ x m := by
        dsimp only [x]; rw [← Nat.sub_add_cancel hm_ge1, iterLog_succ]
        exact Real.log_nonneg hprev
      have : u m = x m := abs_of_nonneg hxm_nn
      linarith [Real.exp_one_gt_two]
    · have hs_eq : s = 3 := max_eq_right (by omega)
      rw [hs_eq]
      have hN15 : N ≤ 15 := by
        by_contra h16
        push Not at h16
        have h16R : (16 : ℝ) ≤ N := by exact_mod_cast h16
        have hlog16 : Real.exp 1 < Real.log (N : ℝ) := by
          have h1 : Real.log 16 ≤ Real.log (N : ℝ) := Real.log_le_log (by norm_num) h16R
          have h16' : Real.log 16 = 4 * Real.log 2 := by
            rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
          linarith [Real.log_two_gt_d9, Real.exp_one_lt_d9]
        have hx1 : 1 ≤ x 1 := by
          dsimp only [x]; rw [iterLog_succ, iterLog_zero]; linarith [Real.exp_one_gt_two]
        have hx2 : 1 ≤ x 2 := by
          dsimp only [x]; rw [iterLog_succ, iterLog_succ, iterLog_zero]
          exact (Real.le_log_iff_exp_le (by linarith [Real.exp_pos 1])).mpr hlog16.le
        have : m = 1 ∨ m = 2 := by omega
        rcases this with hm1 | hm2
        · rw [hm1] at hm_lt1; linarith
        · rw [hm2] at hm_lt1; linarith
      exact abs_iterLog_three_lt_exp_one hN2 hN15
  -- Tail product bound: `∏_{i ∈ Icc s k} u i ≤ exp 1 * exp (-exp k / 4)`
  have htail_prod : ∏ i ∈ Finset.Icc s k, u i ≤ Real.exp 1 * Real.exp (-Real.exp (k : ℝ) / 4) := by
    have hunion : Finset.Icc s k = Finset.Ico s (r - 1) ∪ Finset.Ico (r - 1) (k + 1) := by
      ext i; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ico]; omega
    have hdisj : Disjoint (Finset.Ico s (r - 1)) (Finset.Ico (r - 1) (k + 1)) := by
      rw [Finset.disjoint_left]; intro i h1 h2
      simp only [Finset.mem_Ico] at h1 h2; omega
    rw [hunion, Finset.prod_union hdisj]
    have hfirst_part : ∏ i ∈ Finset.Ico s (r - 1), u i ≤ Real.exp 1 := by
      rcases eq_or_lt_of_le hs_le_r1 with heq | hlt
      · rw [heq, Finset.Ico_self, Finset.prod_empty]; linarith [Real.exp_one_gt_two]
      · by_cases hus1 : u s ≤ 1
        · exact (small_to_small_prod_le hu_nn hu_step _ s (r - 1) rfl hlt.le hus1
            (by linarith)).trans (by linarith [Real.exp_one_gt_two])
        · push Not at hus1
          have hus1_le1 : u (s + 1) ≤ 1 := by
            rw [hu_step s, abs_of_pos (Real.log_pos hus1)]
            calc Real.log (u s) ≤ Real.log (Real.exp 1) :=
                  Real.log_le_log (by linarith) hus_lt_e.le
              _ = 1 := Real.log_exp 1
          have hsp : Finset.Ico s (r - 1) = insert s (Finset.Ico (s + 1) (r - 1)) := by
            ext i; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
          rw [hsp, Finset.prod_insert (by simp)]
          have hrest := small_to_small_prod_le hu_nn hu_step _ (s + 1) (r - 1) rfl (by omega)
            hus1_le1 (by linarith)
          have hrest_nn : 0 ≤ ∏ i ∈ Finset.Ico (s + 1) (r - 1), u i :=
            Finset.prod_nonneg fun i _ => hu_nn i
          nlinarith
    have hsecond_part : ∏ i ∈ Finset.Ico (r - 1) (k + 1), u i ≤ Real.exp (-Real.exp (k : ℝ) / 4) := by
      have hex := excursion_prod_le hu_nn hu_step (a := r - 1) (b := k + 1) (by omega) (by linarith)
        (fun t ht => by
          have ht1 : r ≤ t := by have := (Finset.mem_Ioo.mp ht).1; omega
          have ht2 : t ≤ k := by have := (Finset.mem_Ioo.mp ht).2; omega
          rcases eq_or_lt_of_le ht1 with rfl | htr
          · have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast hk
            linarith [Real.add_one_le_exp (k : ℝ)]
          · have hx_ge : 1 ≤ x t := htail_ge1 t (Finset.mem_Icc.mpr ⟨by omega, ht2⟩)
            have hxt_gt : 1 < x t := by
              rcases eq_or_lt_of_le ht2 with htk_eq | htk
              · rw [htk_eq]
                have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast hk
                dsimp only [x]; linarith
              · have hnext : 1 ≤ x (t + 1) := htail_ge1 (t + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
                have hstep : x (t + 1) = Real.log (x t) := by dsimp only [x]; rw [iterLog_succ]
                rw [hstep] at hnext
                have := (Real.le_log_iff_exp_le (by linarith)).mp hnext
                linarith [Real.exp_one_gt_two]
            dsimp only [u]; rwa [abs_of_pos (by linarith)])
      have hle := hex.2 (by omega)
      rw [Nat.sub_add_cancel hr_ge1] at hle
      exact hle.trans (Real.exp_le_exp.mpr (by linarith))
    exact mul_le_mul hfirst_part hsecond_part
      (Finset.prod_nonneg fun i _ => hu_nn i) (Real.exp_pos 1).le
  -- Split the product `∏_{i ∈ Icc 3 k} x i` at `s`
  have hprod_le_abs : ∏ i ∈ Finset.Icc 3 k, x i ≤
      (∏ i ∈ Finset.Ico 3 s, x i) * ∏ i ∈ Finset.Icc s k, u i := by
    have hunion : Finset.Icc 3 k = Finset.Ico 3 s ∪ Finset.Icc s k := by
      ext i; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ico]; omega
    have hdisj : Disjoint (Finset.Ico 3 s) (Finset.Icc s k) := by
      rw [Finset.disjoint_left]; intro i h1 h2
      simp only [Finset.mem_Ico, Finset.mem_Icc] at h1 h2; omega
    rw [hunion, Finset.prod_union hdisj]
    have hpre_nn : 0 ≤ ∏ i ∈ Finset.Ico 3 s, x i := Finset.prod_nonneg fun i hi => by
      have his : i < s := (Finset.mem_Ico.mp hi).2
      have him : i < m := by
        by_cases hm3 : 3 ≤ m
        · have : s = m := max_eq_left hm3; omega
        · have : s = 3 := max_eq_right (by omega); have := (Finset.mem_Ico.mp hi).1; omega
      linarith [hpre_ge1 i him]
    have htail_le : ∏ i ∈ Finset.Icc s k, x i ≤ ∏ i ∈ Finset.Icc s k, u i := by
      calc ∏ i ∈ Finset.Icc s k, x i ≤ |∏ i ∈ Finset.Icc s k, x i| := le_abs_self _
        _ = ∏ i ∈ Finset.Icc s k, u i := Finset.abs_prod _ _
    exact mul_le_mul_of_nonneg_left htail_le hpre_nn
  have hN_div_nn : 0 ≤ (N : ℝ) / Real.log N := div_nonneg (Nat.cast_nonneg N) hlogN_pos.le
  -- Case split on whether some `j ∈ Ico 4 s` satisfies `j ≤ x j`
  let Jgood : Finset ℕ := (Finset.Ico 4 s).filter (fun j : ℕ => (j : ℝ) ≤ x j)
  by_cases hJ : Jgood.Nonempty
  · -- Subcase B1: reduce to `main_regime N k'` at `k' = Jgood.max' hJ`
    let k' := Jgood.max' hJ
    have hk'_mem : k' ∈ Jgood := Finset.max'_mem Jgood hJ
    have hk'_4 : 4 ≤ k' := (Finset.mem_Ico.mp (Finset.mem_filter.mp hk'_mem).1).1
    have hk'_s : k' < s := (Finset.mem_Ico.mp (Finset.mem_filter.mp hk'_mem).1).2
    have hk'_ge : (k' : ℝ) ≤ x k' := (Finset.mem_filter.mp hk'_mem).2
    have hk'_m : k' < m := by
      by_cases hm3 : 3 ≤ m
      · have : s = m := max_eq_left hm3; omega
      · have : s = 3 := max_eq_right (by omega); omega
    have hmain := main_regime N k' hk'_4 (fun i hi => hpre_ge1 i (by omega)) hk'_ge
    have hpre_split : ∏ i ∈ Finset.Ico 3 s, x i =
        (∏ i ∈ Finset.Icc 3 k', x i) * ∏ i ∈ Finset.Ioo k' s, x i := by
      have hun : Finset.Ico 3 s = Finset.Icc 3 k' ∪ Finset.Ioo k' s := by
        ext i; simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioo]; omega
      have hd : Disjoint (Finset.Icc 3 k') (Finset.Ioo k' s) := by
        rw [Finset.disjoint_left]; intro i h1 h2
        simp only [Finset.mem_Icc, Finset.mem_Ioo] at h1 h2; omega
      rw [hun, Finset.prod_union hd]
    have hmid_le : ∏ i ∈ Finset.Ioo k' s, x i ≤ (k : ℝ) ^ k := by
      have hcard : #(Finset.Ioo k' s) ≤ k := by simp; omega
      calc ∏ i ∈ Finset.Ioo k' s, x i
          ≤ ∏ _ ∈ Finset.Ioo k' s, (k : ℝ) := by
            refine Finset.prod_le_prod (fun i hi => by
              have : i < m := by
                have := (Finset.mem_Ioo.mp hi).2
                have hs_eq : s = m := by dsimp only [s] at hk'_s ⊢; exact max_eq_left (by omega)
                omega
              linarith [hpre_ge1 i this]) fun i hi => ?_
            have hik' : k' < i := (Finset.mem_Ioo.mp hi).1
            have his : i < s := (Finset.mem_Ioo.mp hi).2
            have hi_lt : x i < (i : ℝ) := by
              by_contra hge
              push Not at hge
              have hiJ : i ∈ Jgood := Finset.mem_filter.mpr
                ⟨Finset.mem_Ico.mpr ⟨by omega, his⟩, hge⟩
              have := Finset.le_max' Jgood i hiJ
              omega
            exact hi_lt.le.trans (by exact_mod_cast (show i ≤ k by omega))
        _ = (k : ℝ) ^ #(Finset.Ioo k' s) := Finset.prod_const _
        _ ≤ (k : ℝ) ^ k := pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ k by omega)) hcard
    have hsmall_fac : (k : ℝ) ^ k * (Real.exp 1 * Real.exp (-Real.exp (k : ℝ) / 4)) ≤ 1 := by
      have hdom := edge_exp_dominates hk_ge5
      have h4e4 : (1 : ℝ) ≤ 4 * Real.exp 4 := by
        have := Real.exp_pos (4 : ℝ); linarith [Real.add_one_le_exp (4 : ℝ)]
      have h5 : Real.exp 5 = Real.exp 4 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [h5] at hdom
      have hnn : 0 ≤ (k : ℝ) ^ k * Real.exp 1 * Real.exp (-Real.exp (k : ℝ) / 4) := by positivity
      nlinarith
    have hpk'_nn : 0 ≤ (N : ℝ) / Real.log N * ∏ i ∈ Finset.Icc 3 k', x i :=
      mul_nonneg hN_div_nn (Finset.prod_nonneg fun i hi => by
        linarith [hpre_ge1 i (by have := (Finset.mem_Icc.mp hi).2; omega)])
    calc (N : ℝ) / Real.log N * ∏ i ∈ Finset.Icc 3 k, x i
        ≤ (N : ℝ) / Real.log N * ((∏ i ∈ Finset.Ico 3 s, x i) * ∏ i ∈ Finset.Icc s k, u i) :=
          mul_le_mul_of_nonneg_left hprod_le_abs hN_div_nn
      _ = ((N : ℝ) / Real.log N * ∏ i ∈ Finset.Icc 3 k', x i) *
            ((∏ i ∈ Finset.Ioo k' s, x i) * ∏ i ∈ Finset.Icc s k, u i) := by
          rw [hpre_split]; ring
      _ ≤ ((N : ℝ) / Real.log N * ∏ i ∈ Finset.Icc 3 k', x i) *
            ((k : ℝ) ^ k * (Real.exp 1 * Real.exp (-Real.exp (k : ℝ) / 4))) := by
          refine mul_le_mul_of_nonneg_left ?_ hpk'_nn
          exact mul_le_mul hmid_le htail_prod (Finset.prod_nonneg fun i _ => hu_nn i) (by positivity)
      _ ≤ ((N : ℝ) / Real.log N * ∏ i ∈ Finset.Icc 3 k', x i) * 1 :=
          mul_le_mul_of_nonneg_left hsmall_fac hpk'_nn
      _ ≤ Erdos321.R N := by rw [mul_one]; exact hmain
  · -- Subcase B2: no `j ∈ Ico 4 s` satisfies `j ≤ x j`
    have hno_good : ∀ j ∈ Finset.Ico 4 s, x j < (j : ℝ) := by
      intro j hj
      by_contra hge
      push Not at hge
      exact hJ ⟨j, Finset.mem_filter.mpr ⟨hj, hge⟩⟩
    have hpre_le : ∏ i ∈ Finset.Ico 3 s, x i ≤ Real.exp 4 * (k : ℝ) ^ k := by
      rcases eq_or_lt_of_le hs_ge3 with hs3 | hs4
      · rw [← hs3, Finset.Ico_self, Finset.prod_empty]
        have h1 : (1 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
        have h2 : (1 : ℝ) ≤ (k : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast (show 1 ≤ k by omega))
        nlinarith
      · have hs_eq_m : s = m := by dsimp only [s] at hs4 ⊢; exact max_eq_left (by omega)
        have hsplit3 : Finset.Ico 3 s = insert 3 (Finset.Ico 4 s) := by
          ext i; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
        rw [hsplit3, Finset.prod_insert (by simp)]
        have hx3_le : x 3 ≤ Real.exp 4 := by
          have hx3_ge1 : 1 ≤ x 3 := hpre_ge1 3 (by omega)
          have hstep : x 3 = Real.exp (x 4) := by
            have : x 4 = Real.log (x 3) := by dsimp only [x]; rw [iterLog_succ]
            rw [this, Real.exp_log (by linarith)]
          rw [hstep]
          refine Real.exp_le_exp.mpr ?_
          by_cases hs5 : 5 ≤ s
          · exact (hno_good 4 (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)).le
          · have hm4 : m = 4 := by omega
            have : x 4 < 1 := hm4 ▸ hm_lt1
            linarith
        have hrest_le : ∏ i ∈ Finset.Ico 4 s, x i ≤ (k : ℝ) ^ k := by
          have hcard : #(Finset.Ico 4 s) ≤ k := by simp; omega
          calc ∏ i ∈ Finset.Ico 4 s, x i
              ≤ ∏ _ ∈ Finset.Ico 4 s, (k : ℝ) := by
                refine Finset.prod_le_prod (fun i hi => by
                  linarith [hpre_ge1 i (by have := (Finset.mem_Ico.mp hi).2; omega)]) fun i hi => ?_
                have hlt := hno_good i hi
                exact hlt.le.trans (by exact_mod_cast (show i ≤ k by
                  have := (Finset.mem_Ico.mp hi).2; omega))
            _ = (k : ℝ) ^ #(Finset.Ico 4 s) := Finset.prod_const _
            _ ≤ (k : ℝ) ^ k := pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ k by omega)) hcard
        exact mul_le_mul hx3_le hrest_le
          (Finset.prod_nonneg fun i hi => by
            linarith [hpre_ge1 i (by have := (Finset.mem_Ico.mp hi).2; omega)])
          (Real.exp_pos 4).le
    have hNR := N_div_log_le_four_R hN2
    have hdom := edge_exp_dominates hk_ge5
    have hR_nn : (0 : ℝ) ≤ Erdos321.R N := Nat.cast_nonneg _
    have h5 : Real.exp 4 * Real.exp 1 = Real.exp 5 := by rw [← Real.exp_add]; norm_num
    calc (N : ℝ) / Real.log N * ∏ i ∈ Finset.Icc 3 k, x i
        ≤ (N : ℝ) / Real.log N * ((∏ i ∈ Finset.Ico 3 s, x i) * ∏ i ∈ Finset.Icc s k, u i) :=
          mul_le_mul_of_nonneg_left hprod_le_abs hN_div_nn
      _ ≤ (4 * (Erdos321.R N : ℝ)) *
            ((Real.exp 4 * (k : ℝ) ^ k) * (Real.exp 1 * Real.exp (-Real.exp (k : ℝ) / 4))) := by
          refine mul_le_mul hNR ?_ (mul_nonneg
            (Finset.prod_nonneg fun i hi => by
              have his := (Finset.mem_Ico.mp hi).2
              have him : i < m := by
                by_cases hm3 : 3 ≤ m
                · have : s = m := max_eq_left hm3; omega
                · have : s = 3 := max_eq_right (by omega); have := (Finset.mem_Ico.mp hi).1; omega
              linarith [hpre_ge1 i him])
            (Finset.prod_nonneg fun i _ => hu_nn i)) (by positivity)
          exact mul_le_mul hpre_le htail_prod (Finset.prod_nonneg fun i _ => hu_nn i) (by positivity)
      _ = (Erdos321.R N : ℝ) * (4 * Real.exp 5 * (k : ℝ) ^ k * Real.exp (-Real.exp (k : ℝ) / 4)) := by
          rw [← h5]; ring
      _ ≤ (Erdos321.R N : ℝ) * 1 := mul_le_mul_of_nonneg_left hdom hR_nn
      _ = (Erdos321.R N : ℝ) := mul_one _

end Erdos321LowerProof

theorem OMA.solution : type_of% @Erdos321.erdos_321.variants.lower := by
  intro N k hk hkN
  by_cases hpos : ∀ i ≤ k, 1 ≤ Real.log^[i] (N : ℝ)
  · exact Erdos321LowerProof.main_regime N k hk hpos hkN
  · exact Erdos321LowerProof.edge_regime N k hk hkN hpos


