import FormalConjectures.ErdosProblems.«142»
import Mathlib

/-! Temporary formalization of the explicit partition-function answer. -/

open Asymptotics Filter
open scoped BigOperators Topology

namespace OMA

noncomputable def edges (k N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact if 1 < k then
    (((Finset.Icc 1 N : Finset ℕ).powerset.filter
      fun T : Finset ℕ => (T : Set ℕ).IsAPOfLength k))
  else ∅

def edgeFree (k N : ℕ) (A : Finset ℕ) : Prop :=
  ∀ T ∈ edges k N, ¬ T ⊆ A

noncomputable def validSets (k N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.Icc 1 N).powerset.filter (edgeFree k N)

noncomputable def partition (k N : ℕ) : ℝ :=
  let U := Finset.Icc 1 N
  let q : ℝ := Real.exp (((N : ℝ) + 1) ^ 2)
  ∑ A ∈ U.powerset, q ^ (A.card : ℝ) *
    ∏ T ∈ edges k N, (if T ⊆ A then (0 : ℝ) else 1)

end OMA

noncomputable def OMA.answer : ℕ → ℕ → ℝ := fun k N =>
  Real.log (OMA.partition k N) / (((N : ℝ) + 1) ^ 2)

theorem edgeFree_iff_free {k N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) :
    OMA.edgeFree k N A ↔ (A : Set ℕ).IsAPOfLengthFree k := by
  classical
  by_cases hk : 1 < k
  · change (∀ T ∈ OMA.edges k N, ¬ T ⊆ A) ↔
      (A : Set ℕ).IsAPOfLengthFree k
    constructor
    · intro hfree
      change ∀ t ⊆ (A : Set ℕ), t.IsAPOfLength k → (k : ℕ∞) ≤ 1
      intro t htA ht
      have htfin : t.Finite := (Finset.finite_toSet A).subset htA
      let T := htfin.toFinset
      have hTcoe : (T : Set ℕ) = t := htfin.coe_toFinset
      have hTU : T ⊆ Finset.Icc 1 N := by
        intro x hx
        have hxt : x ∈ t := by
          have hx' : x ∈ (T : Set ℕ) := by simpa using hx
          rw [hTcoe] at hx'
          exact hx' 
        have hxA := htA hxt
        exact hA hxA
      have hTE : T ∈ OMA.edges k N := by
        simp only [OMA.edges, if_pos hk, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨hTU, by simpa [hTcoe] using ht⟩
      have hTA : T ⊆ A := by
        intro x hx
        have hxt : x ∈ t := by
          have hx' : x ∈ (T : Set ℕ) := by simpa using hx
          rw [hTcoe] at hx'
          exact hx' 
        exact htA hxt
      have hgt : (1 : ℕ∞) < k := by exact_mod_cast hk
      exact False.elim (hfree T hTE hTA)
    · intro hfree T hTE hTA
      change ∀ t ⊆ (A : Set ℕ), t.IsAPOfLength k → (k : ℕ∞) ≤ 1 at hfree
      have hTE' : T ∈ (((Finset.Icc 1 N : Finset ℕ).powerset.filter
          fun U : Finset ℕ => (U : Set ℕ).IsAPOfLength k)) := by
        simpa [OMA.edges, hk] using hTE
      have hTAP : (T : Set ℕ).IsAPOfLength k := (Finset.mem_filter.mp hTE').2
      have hgt : (1 : ℕ∞) < k := by exact_mod_cast hk
      exact (not_le_of_gt hgt) (hfree (T : Set ℕ) (by exact fun x hx => hTA hx) hTAP)
  · have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl
    · simp [OMA.edgeFree, OMA.edges, Set.isAPOfLengthFree_zero]
    · simp [OMA.edgeFree, OMA.edges, Set.isAPOfLengthFree_one]

namespace OMA

lemma mem_validSets_iff {k N : ℕ} {A : Finset ℕ} :
    A ∈ validSets k N ↔
      A ⊆ Finset.Icc 1 N ∧ (A : Set ℕ).IsAPOfLengthFree k := by
  classical
  unfold validSets
  rw [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hA, hfree⟩
    exact ⟨hA, (edgeFree_iff_free hA).mp hfree⟩
  · rintro ⟨hA, hfree⟩
    exact ⟨hA, (edgeFree_iff_free hA).mpr hfree⟩

lemma maxCard_mem_validSets (k N : ℕ) :
    ∃ A ∈ validSets k N, A.card = Set.IsAPOfLengthFree.maxCard k N := by
  classical
  let B : Set ℕ := {n | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    (A : Set ℕ).IsAPOfLengthFree k ∧ A.card = n}
  have hB : B = {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N)
      (_ : (S : Set ℕ).IsAPOfLengthFree k)} := by
    ext n
    simp only [B, Set.mem_setOf_eq]
    constructor
    · rintro ⟨A, hA, hfree, hcard⟩
      exact ⟨A, hA, hfree, hcard⟩
    · rintro ⟨A, hfree, hA, hcard⟩
      exact ⟨A, hfree, hA, hcard⟩
  have hne : B.Nonempty := by
    refine ⟨0, ?_⟩
    simp only [B, Set.mem_setOf_eq]
    refine ⟨∅, by simp, ?_, by simp⟩
    intro t ht hAP
    have ht' : t ⊆ (∅ : Set ℕ) := by simpa using ht
    have ht0 : t = ∅ := Set.subset_empty_iff.mp ht'
    subst t
    by_contra hnot
    have hkgt : (1 : ℕ∞) < k := lt_of_not_ge hnot
    have hkpos : (0 : ℕ∞) < k := lt_trans (by norm_num) hkgt
    exact Set.not_isAPOfLength_empty hkpos hAP
  have hbdd : BddAbove B := by
    refine ⟨N, ?_⟩
    intro n hn
    rcases hn with ⟨A, hA, _, rfl⟩
    calc
      A.card ≤ (Finset.Icc 1 N).card := Finset.card_mono hA
      _ = N := by rw [Nat.card_Icc]; omega
  have hrmem : Set.IsAPOfLengthFree.maxCard k N ∈ B := by
    rw [Set.IsAPOfLengthFree.maxCard, ← hB]
    exact Nat.sSup_mem hne hbdd
  rcases hrmem with ⟨A, hA, hfree, hcard⟩
  refine ⟨A, (mem_validSets_iff).2 ⟨hA, hfree⟩, ?_⟩
  exact hcard

lemma validSets_card_le_maxCard (k N : ℕ) {A : Finset ℕ}
    (hA : A ∈ validSets k N) : A.card ≤ Set.IsAPOfLengthFree.maxCard k N := by
  classical
  let B : Set ℕ := {n | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    (A : Set ℕ).IsAPOfLengthFree k ∧ A.card = n}
  have hB : B = {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N)
      (_ : (S : Set ℕ).IsAPOfLengthFree k)} := by
    ext n
    simp only [B, Set.mem_setOf_eq]
    constructor
    · rintro ⟨S, hS, hfree, hcard⟩
      exact ⟨S, hS, hfree, hcard⟩
    · rintro ⟨S, hfree, hS, hcard⟩
      exact ⟨S, hfree, hS, hcard⟩
  have hbdd : BddAbove B := by
    refine ⟨N, ?_⟩
    intro n hn
    rcases hn with ⟨S, hS, _, rfl⟩
    calc
      S.card ≤ (Finset.Icc 1 N).card := Finset.card_mono hS
      _ = N := by rw [Nat.card_Icc]; omega
  have hmem : A.card ∈ B := by
    rcases (mem_validSets_iff).mp hA with ⟨hsub, hfree⟩
    exact ⟨A, hsub, hfree, rfl⟩
  rw [Set.IsAPOfLengthFree.maxCard, ← hB]
  exact le_csSup hbdd hmem

lemma singleton_free {k : ℕ} (hk : 1 < k) :
    ({1} : Set ℕ).IsAPOfLengthFree k := by
  intro t ht hAP
  have hcardle : t.encard ≤ 1 := by
    calc
      t.encard ≤ ({1} : Set ℕ).encard := Set.encard_mono ht
      _ = 1 := by simp
  have hk' : (1 : ℕ∞) < k := by exact_mod_cast hk
  have hcontra : (k : ℕ∞) ≤ 1 := by
    rw [← hAP.card]
    exact hcardle
  exact False.elim ((not_le_of_gt hk') hcontra)

lemma maxCard_pos_of_pos {k N : ℕ} (hN : 1 ≤ N) :
    1 ≤ Set.IsAPOfLengthFree.maxCard k N := by
  by_cases hk0 : k = 0
  · rw [hk0, Set.IsAPOfLengthFree.maxCard_zero]
    exact hN
  by_cases hk1 : k = 1
  · rw [hk1, Set.IsAPOfLengthFree.maxCard_one]
    exact hN
  have hk : 1 < k := by omega
  have hsub : ({1} : Finset ℕ) ⊆ Finset.Icc 1 N := by
    intro x hx
    simp only [Finset.mem_singleton] at hx
    subst x
    simp [hN]
  have hA : ({1} : Finset ℕ) ∈ validSets k N :=
    (mem_validSets_iff).2 ⟨hsub, by simpa using singleton_free hk⟩
  have := validSets_card_le_maxCard k N hA
  simpa using this

lemma prod_indicator {α : Type*} [DecidableEq α]
    (E : Finset α) (P : α → Prop) [DecidablePred P] :
    (∏ x ∈ E, (if P x then (0 : ℝ) else 1)) =
      (if ∀ x ∈ E, ¬ P x then 1 else 0) := by
  classical
  induction E using Finset.induction_on with
  | empty => simp
  | @insert a E ha ih =>
    by_cases h : P a <;> simp [ha, h, ih]

lemma weighted_card_bounds
    {α : Type*} (valid : Finset (Finset α)) (s : ℕ) (q : ℝ)
    (hq : 1 < q)
    (hattain : ∃ A ∈ valid, A.card = s)
    (hmax : ∀ A ∈ valid, A.card ≤ s) :
    q ^ (s : ℝ) ≤ (∑ A ∈ valid, q ^ (A.card : ℝ)) ∧
      (∑ A ∈ valid, q ^ (A.card : ℝ)) ≤
        (valid.card : ℝ) * q ^ (s : ℝ) := by
  classical
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  obtain ⟨A, hA, hAs⟩ := hattain
  constructor
  · calc
      q ^ (s : ℝ) = q ^ (A.card : ℝ) := by rw [hAs]
      _ ≤ ∑ B ∈ valid, q ^ (B.card : ℝ) :=
        Finset.single_le_sum
          (fun (B : Finset α) (_ : B ∈ valid) =>
            Real.rpow_nonneg hq0.le (B.card : ℝ)) hA
  · calc
      (∑ A ∈ valid, q ^ (A.card : ℝ)) ≤ ∑ _A ∈ valid, q ^ (s : ℝ) := by
        apply Finset.sum_le_sum
        intro A hA
        apply Real.rpow_le_rpow_of_exponent_le hq.le
        exact_mod_cast hmax A hA
      _ = (valid.card : ℝ) * q ^ (s : ℝ) := by
        simp only [Finset.sum_const, nsmul_eq_mul]

lemma partition_eq_filtered_sum (k N : ℕ) :
    partition k N =
      (∑ A ∈ validSets k N,
        (Real.exp (((N : ℝ) + 1) ^ 2)) ^ (A.card : ℝ)) := by
  classical
  unfold partition validSets
  simp_rw [prod_indicator, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_filter]
  simp [edgeFree]

lemma partition_weight_bounds (k N s : ℕ)
    (hattain : ∃ A ∈ validSets k N, A.card = s)
    (hmax : ∀ A ∈ validSets k N, A.card ≤ s) :
    Real.exp (((N : ℝ) + 1) ^ 2) ^ (s : ℝ) ≤ partition k N ∧
      partition k N ≤ ((validSets k N).card : ℝ) *
        Real.exp (((N : ℝ) + 1) ^ 2) ^ (s : ℝ) := by
  rw [partition_eq_filtered_sum]
  apply weighted_card_bounds
  · exact Real.one_lt_exp_iff.mpr (by positivity)
  · exact hattain
  · exact hmax

lemma validSets_card_le_pow (k N : ℕ) :
    (validSets k N).card ≤ 2 ^ N := by
  classical
  have hsub : validSets k N ⊆ (Finset.Icc 1 N).powerset := by
    intro A hA
    exact Finset.mem_powerset.mpr (mem_validSets_iff.mp hA).1
  calc
    (validSets k N).card ≤ ((Finset.Icc 1 N).powerset).card :=
      Finset.card_mono hsub
    _ = 2 ^ N := by
      rw [Finset.card_powerset, Nat.card_Icc]
      simp

lemma partition_maxCard_bounds (k N : ℕ) :
    Real.exp (((N : ℝ) + 1) ^ 2) ^
        (Set.IsAPOfLengthFree.maxCard k N : ℝ) ≤ partition k N ∧
      partition k N ≤ ((2 ^ N : ℕ) : ℝ) *
        Real.exp (((N : ℝ) + 1) ^ 2) ^
          (Set.IsAPOfLengthFree.maxCard k N : ℝ) := by
  have ⟨A, hA, hcard⟩ := maxCard_mem_validSets k N
  have h := partition_weight_bounds k N
      (Set.IsAPOfLengthFree.maxCard k N) ⟨A, hA, hcard⟩
      (fun B hB => validSets_card_le_maxCard k N hB)
  constructor
  · exact h.1
  · exact h.2.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast validSets_card_le_pow k N) (Real.rpow_nonneg (by positivity) _))

lemma log_partition_bounds (k N : ℕ) :
    (Set.IsAPOfLengthFree.maxCard k N : ℝ) * (((N : ℝ) + 1) ^ 2) ≤
        Real.log (partition k N) ∧
      Real.log (partition k N) ≤
        (Set.IsAPOfLengthFree.maxCard k N : ℝ) * (((N : ℝ) + 1) ^ 2) +
          (N : ℝ) * Real.log 2 := by
  let L : ℝ := ((N : ℝ) + 1) ^ 2
  let s : ℝ := Set.IsAPOfLengthFree.maxCard k N
  have hb := partition_maxCard_bounds k N
  have hqpos : 0 < Real.exp L := Real.exp_pos L
  have hpowpos : 0 < Real.exp L ^ s := Real.rpow_pos_of_pos hqpos s
  have hfactorpos : 0 < ((2 ^ N : ℕ) : ℝ) * Real.exp L ^ s :=
    mul_pos (by positivity) hpowpos
  have hleft : Real.log (Real.exp L ^ s) ≤ Real.log (partition k N) :=
    Real.log_le_log hpowpos hb.1
  have hright :
      Real.log (partition k N) ≤
        Real.log (((2 ^ N : ℕ) : ℝ) * Real.exp L ^ s) :=
    Real.log_le_log (by
      exact lt_of_lt_of_le hpowpos hb.1) hb.2
  have hleft' : L * s ≤ Real.log (partition k N) := by
    simpa [← Real.exp_mul, Real.log_exp, L, s, mul_comm] using hleft
  constructor
  · nlinarith [hleft']
  · have hcast : ((2 ^ N : ℕ) : ℝ) = (2 : ℝ) ^ N := by norm_num
    rw [Real.log_mul (by positivity) (ne_of_gt hpowpos), hcast,
      Real.log_pow] at hright
    have hright'' :
        Real.log (partition k N) ≤ (N : ℝ) * Real.log 2 + L * s := by
      simpa [← Real.exp_mul, Real.log_exp, L, s, mul_comm] using hright
    nlinarith [hright'']

lemma partition_error_tendsto_zero :
    Tendsto (fun N : ℕ =>
      ((N : ℝ) / (((N : ℝ) + 1) ^ 2)) * Real.log 2) atTop (𝓝 0) := by
  have hplus : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hplus
  have hmajor : Tendsto (fun N : ℕ =>
      ((N : ℝ) + 1)⁻¹ * Real.log 2) atTop (𝓝 0) := by
    simpa using hinv.mul_const (Real.log 2)
  apply squeeze_zero (fun N => by positivity) (fun N => ?_) hmajor
  have hden : 0 < (N : ℝ) + 1 := by positivity
  have hsq : 0 < ((N : ℝ) + 1) ^ 2 := sq_pos_of_pos hden
  have hN : (N : ℝ) ≤ (N : ℝ) + 1 := by linarith
  have hfrac : (N : ℝ) / (((N : ℝ) + 1) ^ 2) ≤
      ((N : ℝ) + 1)⁻¹ := by
    have hfrac' : (N : ℝ) / (((N : ℝ) + 1) ^ 2) ≤
        1 / ((N : ℝ) + 1) := by
      apply (div_le_div_iff₀ hsq hden).2
      nlinarith
    simpa [one_div] using hfrac'
  exact mul_le_mul_of_nonneg_right hfrac
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))

lemma partition_equiv (k : ℕ) :
    (fun N => (Set.IsAPOfLengthFree.maxCard k N : ℝ)) ~[atTop] answer k := by
  let R : ℕ → ℝ := fun N => (Set.IsAPOfLengthFree.maxCard k N : ℝ)
  let A : ℕ → ℝ := fun N => answer k N
  have hL (N : ℕ) : 0 < (((N : ℝ) + 1) ^ 2) := by positivity
  have herror (N : ℕ) :
      A N - R N =
        (Real.log (partition k N) -
          R N * (((N : ℝ) + 1) ^ 2)) / (((N : ℝ) + 1) ^ 2) := by
    dsimp [A, R, answer]
    field_simp
    <;> ring
  have hlo (N : ℕ) : 0 ≤ A N - R N := by
    rw [herror]
    exact div_nonneg
      (sub_nonneg.mpr (log_partition_bounds k N).1) (le_of_lt (hL N))
  have hhi (N : ℕ) : A N - R N ≤
      ((N : ℝ) / (((N : ℝ) + 1) ^ 2)) * Real.log 2 := by
    rw [herror]
    have hnum : Real.log (partition k N) -
        R N * (((N : ℝ) + 1) ^ 2) ≤ (N : ℝ) * Real.log 2 := by
      have := (log_partition_bounds k N).2
      nlinarith
    calc
      (Real.log (partition k N) -
          R N * (((N : ℝ) + 1) ^ 2)) / (((N : ℝ) + 1) ^ 2) ≤
          ((N : ℝ) * Real.log 2) / (((N : ℝ) + 1) ^ 2) :=
        div_le_div_of_nonneg_right hnum (le_of_lt (hL N))
      _ = ((N : ℝ) / (((N : ℝ) + 1) ^ 2)) * Real.log 2 := by ring
  have herr : Tendsto (fun N => A N - R N) atTop (𝓝 0) :=
    squeeze_zero hlo hhi partition_error_tendsto_zero
  have hRpos : ∀ᶠ N in atTop, 1 ≤ R N := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    change (1 : ℝ) ≤ (Set.IsAPOfLengthFree.maxCard k N : ℝ)
    exact_mod_cast maxCard_pos_of_pos (k := k) hN
  apply Asymptotics.IsEquivalent.symm
  change (A - R) =o[atTop] R
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hsmall : ∀ᶠ N in atTop, A N - R N < c := by
    simpa only [Set.mem_Iio] using herr.eventually_lt_const hc
  filter_upwards [hsmall, hRpos] with N hsmall hpos
  change ‖A N - R N‖ ≤ c * ‖R N‖
  rw [Real.norm_eq_abs, abs_of_nonneg (hlo N),
      Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ R N)]
  nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hpos)]

end OMA

theorem OMA.solution :
    Erdos142.erdos_142.answer = OMA.answer →
      type_of% @Erdos142.erdos_142 := by
  intro hanswer
  rw [hanswer]
  intro k
  simpa [OMA.answer] using OMA.partition_equiv k
