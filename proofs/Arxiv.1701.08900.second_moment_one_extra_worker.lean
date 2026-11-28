import FormalConjectures.Arxiv.«1701.08900».SecondMoment

-- Problem: Pittel's second-moment conjecture for nearly balanced stable matching markets.
-- Upstream: formal-conjectures FormalConjectures/Arxiv/1701.08900/SecondMoment.lean (declaration Arxiv.«1701.08900».second_moment_one_extra_worker)
-- Credit: @tatashbar (the owner of the agent is credited as the solver)

/-!
A disproof. With `n` firms and `n + 1` workers and uniform random preferences, let `S` be the
number of stable matchings. This file proves, for `n = 16 P ^ 4` with `P` large,

* `E[S] <= 10 n / log n` (`OMA.expected_le`), and
* `E[S ^ 2] >= e ^ (-75) n ^ 2 / (115200 log n)` (`OMA.second_moment_lower`),

so `E[S ^ 2] / E[S] ^ 2` is unbounded and no constant `C` works.

Route (paper version: a note of the same owner, written and second-read by AI sessions):
1. a counting lemma for rankings (a marked element is ahead of a set `T` in a fraction
   `1 / (|T| + 1)` of the rankings) turns the count of profiles for which a matching is stable
   into the Knuth-Pittel integral over the unit cube, without a continuous score model;
2. for a pair of matchings that differ by a permutation with a type on each moved firm, an
   explicit sufficient event gives a lower bound of the same form;
3. the cube integrals are reduced to one-dimensional integrals by the identity
   `a ^ (-p) = (1 / (p - 1)!) * integral of l ^ (p - 1) * exp (-(l a))`, with pointwise
   comparisons for the second-order corrections;
4. typed pairs are counted through pairs of derangements on disjoint sets.
-/

/-
# Part 1. Counting: a marked element is first, and stability as conditions on the firms' lists

Formalises Lemma K and the first half of Step A of `Q\sm2_lean_route.md`.
-/

namespace OMA

open StableMarriage.Unbalanced
open Finset
open Classical

section Counting

/-- **Lemma K.** Among the rankings of `Fin N`, exactly `N! / (|T| + 1)` put `a` ahead of every
element of `T`. -/
theorem card_first {N : ℕ} (a : Fin N) (T : Finset (Fin N)) (ha : a ∉ T) :
    (T.card + 1) * (univ.filter fun π : Equiv.Perm (Fin N) => ∀ j ∈ T, π a < π j).card =
      N.factorial := by
  set S := insert a T with hS
  have haS : a ∈ S := mem_insert_self a T
  let R : Fin N → Finset (Equiv.Perm (Fin N)) := fun b =>
    univ.filter fun π => ∀ j ∈ S, j ≠ b → π b < π j
  have hkey : ∀ π : Equiv.Perm (Fin N),
      (S.filter fun b => ∀ j ∈ S, j ≠ b → π b < π j).card = 1 := by
    intro π
    obtain ⟨b, hb, hmin⟩ := S.exists_min_image (fun j => π j) ⟨a, haS⟩
    rw [card_eq_one]
    refine ⟨b, ?_⟩
    ext c
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hc, hcmin⟩
      by_contra hne
      have h1 := hcmin b hb (fun h => hne h.symm)
      have h2 := hmin c hc
      exact absurd h1 (not_lt.mpr h2)
    · rintro rfl
      exact ⟨hb, fun j hj hjb =>
        lt_of_le_of_ne (hmin j hj) (fun h => hjb (π.injective h).symm)⟩
  have hswap : ∀ b ∈ S, ∀ c ∈ S, ∀ π, π ∈ R b → π * Equiv.swap b c ∈ R c := by
    intro b hb c hc π hπ
    simp only [R, mem_filter, mem_univ, true_and] at hπ ⊢
    intro j hj hjc
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    by_cases hjb : j = b
    · subst hjb
      rw [Equiv.swap_apply_left]
      exact hπ c hc (fun h => hjc h.symm)
    · rw [Equiv.swap_apply_of_ne_of_ne hjb hjc]
      exact hπ j hj hjb
  have hcard : ∀ b ∈ S, (R b).card = (R a).card := by
    intro b hb
    refine card_equiv (Equiv.mulRight (Equiv.swap b a)) ?_
    intro π
    show π ∈ R b ↔ π * Equiv.swap b a ∈ R a
    constructor
    · intro h
      exact hswap b hb a haS π h
    · intro h
      have h1 := hswap a haS b hb _ h
      rwa [mul_assoc, Equiv.swap_comm a b, Equiv.swap_mul_self, mul_one] at h1
  have htot : ∑ b ∈ S, (R b).card = N.factorial := by
    have h1 : ∑ b ∈ S, (R b).card = ∑ π : Equiv.Perm (Fin N),
        (S.filter fun b => ∀ j ∈ S, j ≠ b → π b < π j).card := by
      simp only [R, card_filter]
      rw [sum_comm]
    rw [h1]
    simp only [hkey]
    simp [Fintype.card_perm]
  have hRa : R a = univ.filter fun π : Equiv.Perm (Fin N) => ∀ j ∈ T, π a < π j := by
    ext π
    simp only [R, mem_filter, mem_univ, true_and, hS]
    constructor
    · intro h j hj
      exact h j (mem_insert_of_mem hj) (fun h' => ha (h' ▸ hj))
    · intro h j hj hja
      rcases mem_insert.mp hj with h' | h'
      · exact absurd h' hja
      · exact h j h'
  rw [← hRa, ← htot, sum_congr rfl hcard, sum_const, smul_eq_mul, hS, card_insert_of_notMem ha]

/-- Lemma K with the order reversed: `a` is behind every element of `T`. -/
theorem card_last {N : ℕ} (a : Fin N) (T : Finset (Fin N)) (ha : a ∉ T) :
    (T.card + 1) * (univ.filter fun π : Equiv.Perm (Fin N) => ∀ j ∈ T, π j < π a).card =
      N.factorial := by
  rw [← card_first a T ha]
  congr 1
  refine card_equiv (Equiv.mulLeft Fin.revPerm) ?_
  intro π
  simp only [mem_filter, mem_univ, true_and]
  show (∀ j ∈ T, π j < π a) ↔
    ∀ j ∈ T, (Fin.revPerm : Equiv.Perm (Fin N)) (π a) < (Fin.revPerm : Equiv.Perm (Fin N)) (π j)
  simp [Fin.rev_lt_rev]

end Counting

section Stability

variable {n m : ℕ}

/-- The workers that firm `i` must rank behind its partner: every worker other than the partner
who is unmatched or prefers `i` to its own firm. -/
noncomputable def threat (μ : Matching n m) (w : Fin m → Equiv.Perm (Fin n)) (i : Fin n) :
    Finset (Fin m) :=
  univ.filter fun j => μ i ≠ j ∧ ∀ k, μ k = j → w j i < w j k

theorem partner_notMem_threat (μ : Matching n m) (w : Fin m → Equiv.Perm (Fin n)) (i : Fin n) :
    μ i ∉ threat μ w i := by
  simp [threat]

/-- A matching is stable iff every firm ranks its partner ahead of its threat set. -/
theorem isStable_iff (p : Profile n m) (μ : Matching n m) :
    IsStable p μ ↔ ∀ i, ∀ j ∈ threat μ p.workerRank i, p.firmRank i (μ i) < p.firmRank i j := by
  constructor
  · intro h i j hj
    simp only [threat, mem_filter, mem_univ, true_and] at hj
    have h1 := h i j
    have h2 : ¬ p.firmRank i j < p.firmRank i (μ i) := fun hlt => h1 ⟨hj.1, hlt, hj.2⟩
    rcases lt_or_ge (p.firmRank i (μ i)) (p.firmRank i j) with h3 | h3
    · exact h3
    · exfalso
      rcases h3.lt_or_eq with h4 | h4
      · exact h2 h4
      · exact hj.1 ((p.firmRank i).injective h4).symm
  · intro h i j hb
    obtain ⟨hne, hlt, hw⟩ := hb
    have h1 := h i j (by
      simp only [threat, mem_filter, mem_univ, true_and]
      exact ⟨hne, hw⟩)
    exact absurd hlt (not_lt.mpr h1.le)

/-- The number of profiles for which `μ` is stable: sum over the workers' lists of the product
over firms of the number of admissible lists. -/
theorem card_stable (μ : Matching n m) :
    (univ.filter fun p : Profile n m => IsStable p μ).card =
      ∑ w : Fin m → Equiv.Perm (Fin n), ∏ i : Fin n,
        (univ.filter fun π : Equiv.Perm (Fin m) => ∀ j ∈ threat μ w i, π (μ i) < π j).card := by
  let e : Profile n m ≃ (Fin n → Equiv.Perm (Fin m)) × (Fin m → Equiv.Perm (Fin n)) :=
    { toFun := fun p => (p.firmRank, p.workerRank)
      invFun := fun q => ⟨q.1, q.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 : (univ.filter fun p : Profile n m => IsStable p μ).card =
      ∑ q : (Fin n → Equiv.Perm (Fin m)) × (Fin m → Equiv.Perm (Fin n)),
        if IsStable (e.symm q) μ then 1 else 0 := by
    rw [card_filter]
    exact (e.symm.sum_comp (fun p => if IsStable p μ then 1 else 0)).symm
  rw [h1, Fintype.sum_prod_type_right]
  refine sum_congr rfl fun w _ => ?_
  rw [← card_filter, ← Fintype.card_piFinset]
  congr 1
  ext f
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
  exact isStable_iff (e.symm (f, w)) μ

end Stability

end OMA

/-
# Part 2. The workers' side: from counts to one-dimensional integrals
-/

namespace OMA

open StableMarriage.Unbalanced
open Finset
open Classical
open MeasureTheory unitInterval

section Integrals

/-- Integrals over the unit interval as interval integrals. -/
theorem integral_I (f : ℝ → ℝ) : ∫ t : I, f t = ∫ t in (0 : ℝ)..1, f t := by
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  exact unitInterval.measurePreserving_coe.integral_comp unitInterval.measurableEmbedding_coe f

theorem integral_I_one_sub_pow (N : ℕ) : ∫ t : I, (1 - (t : ℝ)) ^ N = 1 / ((N : ℝ) + 1) := by
  rw [integral_I (fun t => (1 - t) ^ N),
    intervalIntegral.integral_comp_sub_left (fun t => t ^ N) 1, integral_pow]
  simp

theorem integral_I_pow (N : ℕ) : ∫ t : I, (t : ℝ) ^ N = 1 / ((N : ℝ) + 1) := by
  rw [integral_I (fun t => t ^ N), integral_pow]
  simp

/-- Continuous functions on a compact space are integrable for a finite measure. -/
theorem integrable_of_continuous {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {ν : Measure X} [IsFiniteMeasure ν]
    {f : X → ℝ} (hf : Continuous f) : Integrable f ν :=
  integrableOn_univ.mp (hf.continuousOn.integrableOn_compact isCompact_univ)

end Integrals

section Workers

variable {n m : ℕ}

/-- The weight of worker `j`'s list `ρ`: a factor `1 - x i` for every firm `i` threatened by `j`. -/
noncomputable def Q (μ : Matching n m) (x : Fin n → ℝ) (j : Fin m) (ρ : Equiv.Perm (Fin n)) : ℝ :=
  ∏ i : Fin n, if (μ i ≠ j ∧ ∀ k, μ k = j → ρ i < ρ k) then 1 - x i else 1

theorem prod_pow_threat (μ : Matching n m) (x : Fin n → ℝ) (w : Fin m → Equiv.Perm (Fin n)) :
    ∏ i : Fin n, (1 - x i) ^ (threat μ w i).card = ∏ j : Fin m, Q μ x j (w j) := by
  unfold Q
  rw [prod_comm]
  refine prod_congr rfl fun i _ => ?_
  rw [← prod_const, threat, prod_filter]

theorem sum_Q_unmatched (μ : Matching n m) (x : Fin n → ℝ) (j : Fin m) (hj : ∀ k, μ k ≠ j) :
    ∑ ρ : Equiv.Perm (Fin n), Q μ x j ρ = (n.factorial : ℝ) * ∏ i, (1 - x i) := by
  have h : ∀ ρ : Equiv.Perm (Fin n), Q μ x j ρ = ∏ i, (1 - x i) := by
    intro ρ
    unfold Q
    refine prod_congr rfl fun i _ => ?_
    rw [if_pos]
    exact ⟨hj i, fun k hk => absurd hk (hj k)⟩
  simp only [h, sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

theorem sum_Q_matched (μ : Matching n m) (x : Fin n → ℝ) (k : Fin n) :
    ∑ ρ : Equiv.Perm (Fin n), Q μ x (μ k) ρ =
      (n.factorial : ℝ) * ∫ y : I, ∏ i ∈ univ.erase k, (1 - x i * (y : ℝ)) := by
  have hQ : ∀ ρ : Equiv.Perm (Fin n), Q μ x (μ k) ρ =
      ∑ T ∈ (univ.erase k).powerset,
        (∏ i ∈ T, (-x i)) * (if ∀ i ∈ T, ρ i < ρ k then 1 else 0) := by
    intro ρ
    have h1 : Q μ x (μ k) ρ = ∏ i ∈ univ.erase k, (1 + (if ρ i < ρ k then -x i else 0)) := by
      unfold Q
      rw [← mul_prod_erase univ _ (mem_univ k), if_neg (by simp), one_mul]
      refine prod_congr rfl fun i hi => ?_
      have hik : i ≠ k := ne_of_mem_erase hi
      have hcond : (μ i ≠ μ k ∧ ∀ k', μ k' = μ k → ρ i < ρ k') ↔ ρ i < ρ k := by
        constructor
        · intro h
          exact h.2 k rfl
        · intro h
          exact ⟨fun h' => hik (μ.injective h'), fun k' hk' => by rw [μ.injective hk']; exact h⟩
      by_cases h : ρ i < ρ k
      · rw [if_pos (hcond.mpr h), if_pos h]
        ring
      · rw [if_neg (fun h' => h (hcond.mp h')), if_neg h]
        ring
    rw [h1, prod_one_add]
    refine sum_congr rfl fun T _ => ?_
    rw [prod_ite_zero]
    split_ifs <;> simp
  have hint : ∫ y : I, ∏ i ∈ univ.erase k, (1 - x i * (y : ℝ)) =
      ∑ T ∈ (univ.erase k).powerset, (∏ i ∈ T, (-x i)) * (1 / ((T.card : ℝ) + 1)) := by
    have h2 : ∀ y : I, ∏ i ∈ univ.erase k, (1 - x i * (y : ℝ)) =
        ∑ T ∈ (univ.erase k).powerset, (∏ i ∈ T, (-x i)) * (y : ℝ) ^ T.card := by
      intro y
      have h3 : ∀ i, 1 - x i * (y : ℝ) = 1 + (-x i) * y := fun i => by ring
      simp only [h3]
      rw [prod_one_add]
      refine sum_congr rfl fun T _ => ?_
      rw [prod_mul_distrib, prod_const]
    simp only [h2]
    rw [integral_finsetSum]
    · refine sum_congr rfl fun T _ => ?_
      rw [integral_const_mul, integral_I_pow]
    · intro T _
      exact integrable_of_continuous (by fun_prop)
  simp only [hQ]
  rw [sum_comm, hint, mul_sum]
  refine sum_congr rfl fun T hT => ?_
  rw [← mul_sum, sum_boole]
  have hk : k ∉ T := fun h => (mem_erase.mp (mem_powerset.mp hT h)).1 rfl
  have hc := card_last k T hk
  have h4 : ((univ.filter fun ρ : Equiv.Perm (Fin n) => ∀ i ∈ T, ρ i < ρ k).card : ℝ) =
      (n.factorial : ℝ) / ((T.card : ℝ) + 1) := by
    rw [eq_div_iff (by positivity)]
    have h5 : ((univ.filter fun ρ : Equiv.Perm (Fin n) => ∀ i ∈ T, ρ i < ρ k).card : ℝ) *
        ((T.card : ℝ) + 1) = ((T.card + 1) * (univ.filter fun ρ : Equiv.Perm (Fin n) =>
          ∀ i ∈ T, ρ i < ρ k).card : ℕ) := by
      push_cast
      ring
    rw [h5, hc]
  rw [h4]
  ring

end Workers

end OMA

/-
# Part 3. The Knuth–Pittel formula for the probability that a matching is stable
-/

namespace OMA

open StableMarriage.Unbalanced
open Finset
open Classical
open MeasureTheory unitInterval

section Formula

variable {n m : ℕ}

/-- The inner integral attached to the worker of firm `k`. -/
noncomputable def A (x : Fin n → I) (k : Fin n) : ℝ :=
  ∫ y : I, ∏ i ∈ univ.erase k, (1 - (x i : ℝ) * (y : ℝ))

/-- The Knuth–Pittel integrand, firms' variables outside. -/
noncomputable def KP (n m : ℕ) (x : Fin n → I) : ℝ :=
  (∏ i, (1 - (x i : ℝ))) ^ (m - n) * ∏ k, A x k

theorem card_profile : Fintype.card (Profile n m) = m.factorial ^ n * n.factorial ^ m := by
  let e : Profile n m ≃ (Fin n → Equiv.Perm (Fin m)) × (Fin m → Equiv.Perm (Fin n)) :=
    { toFun := fun p => (p.firmRank, p.workerRank)
      invFun := fun q => ⟨q.1, q.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e]
  simp [Fintype.card_perm]

/-- The product over workers of the sums of the weights. -/
theorem prod_sum_Q (μ : Matching n m) (x : Fin n → I) :
    ∏ j : Fin m, ∑ ρ : Equiv.Perm (Fin n), Q μ (fun i => (x i : ℝ)) j ρ =
      (n.factorial : ℝ) ^ m * KP n m x := by
  have hnm : n ≤ m := by
    simpa using Fintype.card_le_of_embedding μ
  set s : Finset (Fin m) := univ.map μ with hs
  have hsplit := prod_mul_prod_compl s
    (fun j : Fin m => ∑ ρ : Equiv.Perm (Fin n), Q μ (fun i => (x i : ℝ)) j ρ)
  have h1 : ∏ j ∈ s, ∑ ρ : Equiv.Perm (Fin n), Q μ (fun i => (x i : ℝ)) j ρ =
      (n.factorial : ℝ) ^ n * ∏ k, A x k := by
    rw [hs, prod_map]
    simp only [sum_Q_matched, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
    rfl
  have h2 : ∏ j ∈ sᶜ, ∑ ρ : Equiv.Perm (Fin n), Q μ (fun i => (x i : ℝ)) j ρ =
      ((n.factorial : ℝ) * ∏ i, (1 - (x i : ℝ))) ^ (m - n) := by
    have hc : sᶜ.card = m - n := by
      rw [card_compl, hs, card_map, card_univ, Fintype.card_fin, Fintype.card_fin]
    rw [← hc, ← prod_const]
    refine prod_congr rfl fun j hj => ?_
    refine sum_Q_unmatched μ _ j fun k hk => ?_
    rw [mem_compl, hs, mem_map] at hj
    exact hj ⟨k, mem_univ k, hk⟩
  rw [← hsplit, h1, h2, KP, mul_pow]
  have h3 : (n.factorial : ℝ) ^ m = (n.factorial : ℝ) ^ n * (n.factorial : ℝ) ^ (m - n) := by
    rw [← pow_add, Nat.add_sub_cancel' hnm]
  rw [h3]
  ring

/-- The number of profiles for which `μ` is stable, as an integral. -/
theorem card_stable_eq_integral (μ : Matching n m) :
    ((univ.filter fun p : Profile n m => IsStable p μ).card : ℝ) =
      (m.factorial : ℝ) ^ n * (n.factorial : ℝ) ^ m * ∫ x : Fin n → I, KP n m x := by
  have hfirm : ∀ (w : Fin m → Equiv.Perm (Fin n)) (i : Fin n),
      ((univ.filter fun π : Equiv.Perm (Fin m) =>
        ∀ j ∈ threat μ w i, π (μ i) < π j).card : ℝ) =
        (m.factorial : ℝ) * ∫ t : I, (1 - (t : ℝ)) ^ (threat μ w i).card := by
    intro w i
    have hc := card_first (μ i) (threat μ w i) (partner_notMem_threat μ w i)
    rw [integral_I_one_sub_pow, mul_one_div, eq_div_iff (by positivity)]
    have h5 : ((univ.filter fun π : Equiv.Perm (Fin m) =>
        ∀ j ∈ threat μ w i, π (μ i) < π j).card : ℝ) * (((threat μ w i).card : ℝ) + 1) =
        (((threat μ w i).card + 1) * (univ.filter fun π : Equiv.Perm (Fin m) =>
          ∀ j ∈ threat μ w i, π (μ i) < π j).card : ℕ) := by
      push_cast
      ring
    rw [h5, hc]
  have hprod : ∀ w : Fin m → Equiv.Perm (Fin n),
      ∏ i : Fin n, ((univ.filter fun π : Equiv.Perm (Fin m) =>
        ∀ j ∈ threat μ w i, π (μ i) < π j).card : ℝ) =
        (m.factorial : ℝ) ^ n * ∫ x : Fin n → I,
          ∏ j : Fin m, Q μ (fun i => (x i : ℝ)) j (w j) := by
    intro w
    simp only [hfirm, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
    congr 1
    rw [← integral_fintype_prod_volume_eq_prod (fun i (t : I) => (1 - (t : ℝ)) ^ (threat μ w i).card)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact prod_pow_threat μ (fun i => (x i : ℝ)) w
  rw [card_stable]
  push_cast
  simp only [hprod]
  rw [← mul_sum, ← integral_finsetSum]
  · rw [mul_assoc]
    congr 1
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ∑ w : Fin m → Equiv.Perm (Fin n), ∏ j : Fin m, Q μ (fun i => (x i : ℝ)) j (w j) =
      (n.factorial : ℝ) ^ m * KP n m x
    rw [← prod_sum_Q μ x, Fintype.prod_sum]
  · intro w _
    have h6 : (fun x : Fin n → I => ∏ j : Fin m, Q μ (fun i => (x i : ℝ)) j (w j)) =
        fun x => ∏ i : Fin n, (1 - (x i : ℝ)) ^ (threat μ w i).card := by
      funext x
      exact (prod_pow_threat μ (fun i => (x i : ℝ)) w).symm
    rw [h6]
    exact integrable_of_continuous (by fun_prop)

end Formula

end OMA

/-
# Part 4. The expected number of stable matchings, and the formula with the workers' variables outside
-/

namespace OMA

open StableMarriage.Unbalanced
open Finset
open Classical
open MeasureTheory unitInterval

section Expectation

variable {n m : ℕ}

theorem numStableMatchings_eq (p : Profile n m) :
    numStableMatchings p = (univ.filter fun μ : Matching n m => IsStable p μ).card := by
  unfold numStableMatchings
  exact Fintype.card_subtype _

/-- **The Knuth–Pittel formula** for the expected number of stable matchings. -/
theorem expected_eq (n m : ℕ) :
    expectedNumStableMatchings n m =
      (m.descFactorial n : ℝ) * ∫ x : Fin n → I, KP n m x := by
  have hP : (0 : ℝ) < (Fintype.card (Profile n m) : ℝ) := by
    rw [card_profile]
    positivity
  have h1 : expectedNumStableMatchings n m =
      (Fintype.card (Profile n m) : ℝ)⁻¹ * ∑ p : Profile n m, (numStableMatchings p : ℝ) := by
    unfold expectedNumStableMatchings uniformProfile
    rw [PMF.integral_eq_sum, mul_sum]
    refine sum_congr rfl fun p _ => ?_
    simp [PMF.uniformOfFintype_apply]
  have h2 : ∑ p : Profile n m, (numStableMatchings p : ℝ) =
      ∑ μ : Matching n m, ((univ.filter fun p : Profile n m => IsStable p μ).card : ℝ) := by
    simp only [numStableMatchings_eq, card_filter]
    push_cast
    rw [sum_comm]
  rw [h1, h2]
  simp only [card_stable_eq_integral, sum_const, card_univ, nsmul_eq_mul]
  rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin, card_profile]
  push_cast
  field_simp

end Expectation

section Swap

variable {n : ℕ}

/-- The firm-side integral for fixed workers' variables `y`. -/
noncomputable def h (d : ℕ) (y : Fin n → I) (i : Fin n) : ℝ :=
  ∫ t : I, (1 - (t : ℝ)) ^ d * ∏ k ∈ univ.erase i, (1 - (t : ℝ) * (y k : ℝ))

/-- The Knuth–Pittel integral with the workers' variables outside. -/
theorem integral_KP_eq (n m : ℕ) :
    ∫ x : Fin n → I, KP n m x = ∫ y : Fin n → I, ∏ i, h (m - n) y i := by
  set d := m - n with hd
  let F : (Fin n → I) → (Fin n → I) → ℝ := fun x y =>
    ∏ i, ((1 - (x i : ℝ)) ^ d * ∏ k ∈ univ.erase i, (1 - (x i : ℝ) * (y k : ℝ)))
  have hKP : ∀ x : Fin n → I, KP n m x = ∫ y : Fin n → I, F x y := by
    intro x
    have h1 : ∀ y : Fin n → I, F x y =
        (∏ i, (1 - (x i : ℝ))) ^ d * ∏ k, ∏ i ∈ univ.erase k, (1 - (x i : ℝ) * (y k : ℝ)) := by
      intro y
      show ∏ i, ((1 - (x i : ℝ)) ^ d * ∏ k ∈ univ.erase i, (1 - (x i : ℝ) * (y k : ℝ))) = _
      rw [prod_mul_distrib, prod_pow]
      congr 1
      refine prod_comm' fun i k => ?_
      simp only [mem_univ, mem_erase, ne_eq, true_and, and_true]
      exact ⟨fun h1 h2 => h1 h2.symm, fun h1 h2 => h1 h2.symm⟩
    simp only [h1]
    rw [integral_const_mul, KP]
    congr 1
    unfold A
    exact (integral_fintype_prod_volume_eq_prod
      (fun k (t : I) => ∏ i ∈ univ.erase k, (1 - (x i : ℝ) * (t : ℝ)))).symm
  have hint : Integrable (Function.uncurry F) (volume.prod volume) := by
    refine integrable_of_continuous ?_
    show Continuous fun z : (Fin n → I) × (Fin n → I) =>
      ∏ i, ((1 - (z.1 i : ℝ)) ^ d * ∏ k ∈ univ.erase i, (1 - (z.1 i : ℝ) * (z.2 k : ℝ)))
    fun_prop
  simp only [hKP]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ∫ x : Fin n → I, F x y = ∏ i, h d y i
  exact integral_fintype_prod_volume_eq_prod
    (fun i (t : I) => (1 - (t : ℝ)) ^ d * ∏ k ∈ univ.erase i, (1 - (t : ℝ) * (y k : ℝ)))

end Swap

end OMA

/-
# Part 5. Step C1: the pointwise upper bound for one extra worker
-/

namespace OMA

open StableMarriage.Unbalanced
open Finset
open Classical
open MeasureTheory unitInterval

section Upper

variable {n : ℕ}

/-- One plus the sum of the workers' variables. -/
noncomputable def aa (y : Fin n → I) : ℝ := 1 + ∑ k, (y k : ℝ)

theorem aa_sub (y : Fin n → I) (i : Fin n) :
    aa y - (y i : ℝ) = 1 + ∑ k ∈ univ.erase i, (y k : ℝ) := by
  unfold aa
  rw [← add_sum_erase univ _ (mem_univ i)]
  ring

theorem one_le_aa_sub (y : Fin n → I) (i : Fin n) : 1 ≤ aa y - (y i : ℝ) := by
  rw [aa_sub]
  have h1 : 0 ≤ ∑ k ∈ univ.erase i, (y k : ℝ) := sum_nonneg fun k _ => (y k).2.1
  linarith

theorem one_le_aa (y : Fin n → I) : 1 ≤ aa y := by
  have h1 := one_le_aa_sub y
  unfold aa
  have h2 : 0 ≤ ∑ k, (y k : ℝ) := sum_nonneg fun k _ => (y k).2.1
  linarith

theorem integral_I_exp_neg_le (c : ℝ) (hc : 0 < c) :
    ∫ t : I, Real.exp (-(t : ℝ) * c) ≤ 1 / c := by
  rw [integral_I (fun t => Real.exp (-t * c))]
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => -(Real.exp (-t * c) / c)) (Real.exp (-t * c)) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => -t * c) (-c) t := by
      simpa using (hasDerivAt_id t).neg.mul_const c
    have h2 : HasDerivAt (fun t : ℝ => -(Real.exp (-t * c) / c))
        (-(Real.exp (-t * c) * -c / c)) t := ((h1.exp).div_const c).neg
    refine h2.congr_deriv ?_
    rw [mul_neg, neg_div, neg_neg, mul_div_assoc, div_self hc.ne', mul_one]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [show -(1 : ℝ) * c = -c by ring, show -(0 : ℝ) * c = 0 by ring, Real.exp_zero]
  have h3 : 0 ≤ Real.exp (-c) / c := by positivity
  linarith

theorem h_nonneg (d : ℕ) (y : Fin n → I) (i : Fin n) : 0 ≤ h d y i := by
  unfold h
  refine integral_nonneg fun t => ?_
  have ht1 := t.2.2
  refine mul_nonneg (pow_nonneg (by linarith) _) (prod_nonneg fun k _ => ?_)
  have h1 := mul_le_one₀ ht1 (y k).2.1 (y k).2.2
  linarith

theorem h_one_le (y : Fin n → I) (i : Fin n) : h 1 y i ≤ 1 / (aa y - (y i : ℝ)) := by
  have hcpos : 0 < aa y - (y i : ℝ) := by
    have h1 := one_le_aa_sub y i
    linarith
  refine le_trans ?_ (integral_I_exp_neg_le _ hcpos)
  unfold h
  refine integral_mono (integrable_of_continuous (by fun_prop))
    (integrable_of_continuous (by fun_prop)) fun t => ?_
  have ht0 := t.2.1
  have ht1 := t.2.2
  have hf0 : ∀ k : Fin n, 0 ≤ 1 - (t : ℝ) * (y k : ℝ) := by
    intro k
    have h1 := mul_le_one₀ ht1 (y k).2.1 (y k).2.2
    linarith
  have h1 : (1 - (t : ℝ)) ^ 1 ≤ Real.exp (-(t : ℝ)) := by
    rw [pow_one]
    have h3 := Real.add_one_le_exp (-(t : ℝ))
    linarith
  have h2 : ∏ k ∈ univ.erase i, (1 - (t : ℝ) * (y k : ℝ)) ≤
      ∏ k ∈ univ.erase i, Real.exp (-(t : ℝ) * (y k : ℝ)) := by
    refine prod_le_prod (fun k _ => hf0 k) (fun k _ => ?_)
    have h3 := Real.add_one_le_exp (-(t : ℝ) * (y k : ℝ))
    linarith
  rw [← Real.exp_sum] at h2
  calc (1 - (t : ℝ)) ^ 1 * ∏ k ∈ univ.erase i, (1 - (t : ℝ) * (y k : ℝ))
      ≤ Real.exp (-(t : ℝ)) * Real.exp (∑ k ∈ univ.erase i, -(t : ℝ) * (y k : ℝ)) :=
        mul_le_mul h1 h2 (prod_nonneg fun k _ => hf0 k) (Real.exp_pos _).le
    _ = Real.exp (-(t : ℝ) * (aa y - (y i : ℝ))) := by
        rw [← Real.exp_add, aa_sub, ← mul_sum]
        congr 1
        ring

/-- **Step C1.** For every `y`, the product of the firm-side integrals is at most `e / a ^ n`. -/
theorem prod_h_one_le (y : Fin n → I) : ∏ i, h 1 y i ≤ Real.exp 1 / aa y ^ n := by
  have ha := one_le_aa y
  have hapos : 0 < aa y := by linarith
  have hcpos : ∀ i, 0 < aa y - (y i : ℝ) := fun i => by
    have h1 := one_le_aa_sub y i
    linarith
  have h1 : ∏ i, h 1 y i ≤ ∏ i, (1 / (aa y - (y i : ℝ))) :=
    prod_le_prod (fun i _ => h_nonneg 1 y i) (fun i _ => h_one_le y i)
  have h2 : ∀ i, 1 / (aa y - (y i : ℝ)) ≤
      (1 / aa y) * Real.exp ((y i : ℝ) / (aa y - (y i : ℝ))) := by
    intro i
    have h3 := Real.add_one_le_exp ((y i : ℝ) / (aa y - (y i : ℝ)))
    have hc := hcpos i
    have h4 : 1 / (aa y - (y i : ℝ)) =
        (1 / aa y) * ((y i : ℝ) / (aa y - (y i : ℝ)) + 1) := by
      field_simp
      ring
    rw [h4]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have h5 : ∑ i, (y i : ℝ) / (aa y - (y i : ℝ)) ≤ 1 := by
    rcases le_total (∑ k, (y k : ℝ)) 1 with hs | hs
    · calc ∑ i, (y i : ℝ) / (aa y - (y i : ℝ)) ≤ ∑ i, (y i : ℝ) :=
            sum_le_sum fun i _ => div_le_self (y i).2.1 (one_le_aa_sub y i)
        _ ≤ 1 := hs
    · have hspos : 0 < ∑ k, (y k : ℝ) := by linarith
      calc ∑ i, (y i : ℝ) / (aa y - (y i : ℝ)) ≤ ∑ i, (y i : ℝ) / (∑ k, (y k : ℝ)) :=
            sum_le_sum fun i _ => div_le_div_of_nonneg_left (y i).2.1 hspos (by
              unfold aa
              have h6 := (y i).2.2
              linarith)
        _ = 1 := by rw [← sum_div, div_self hspos.ne']
  calc ∏ i, h 1 y i ≤ ∏ i, (1 / (aa y - (y i : ℝ))) := h1
    _ ≤ ∏ i, ((1 / aa y) * Real.exp ((y i : ℝ) / (aa y - (y i : ℝ)))) :=
        prod_le_prod (fun i _ => by have hc := hcpos i; positivity) (fun i _ => h2 i)
    _ = (1 / aa y) ^ n * Real.exp (∑ i, (y i : ℝ) / (aa y - (y i : ℝ))) := by
        rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, Real.exp_sum]
    _ ≤ (1 / aa y) ^ n * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h5) (by positivity)
    _ = Real.exp 1 / aa y ^ n := by
        rw [one_div, inv_pow]
        ring

end Upper

end OMA

/-
# Part 6. Step C2: the Laplace identity on the cube
-/

namespace OMA

open StableMarriage.Unbalanced
open Finset
open Classical
open MeasureTheory unitInterval

section Laplace

variable {n : ℕ}

theorem integral_pow_mul_exp_Ioi (q : ℕ) {r : ℝ} (hr : 0 < r) :
    ∫ t in Set.Ioi (0 : ℝ), t ^ q * Real.exp (-(r * t)) = (q.factorial : ℝ) / r ^ (q + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := ((q + 1 : ℕ) : ℝ)) (by positivity) hr
  have h1 : (((q + 1 : ℕ) : ℝ) - 1) = (q : ℝ) := by
    push_cast
    ring
  rw [h1] at h
  simp only [Real.rpow_natCast] at h
  rw [h]
  push_cast
  rw [Real.Gamma_nat_eq_factorial, one_div, inv_pow]
  ring

theorem integrableOn_pow_mul_exp (q : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ q * Real.exp (-t)) (Set.Ioi 0) := by
  have h := integral_pow_mul_exp_Ioi q one_pos
  simp only [one_mul] at h
  refine Integrable.of_integral_ne_zero ?_
  rw [h]
  positivity

/-- **Step C2 (Laplace identity).** A negative power of `a = 1 + Σ y` against a product weight on
the cube is a one-dimensional integral of a product of one-dimensional integrals. -/
theorem laplace (p : ℕ) (hp : 1 ≤ p) (θ : ℝ) (hθ : 0 ≤ θ) (f : Fin n → I → ℝ)
    (hf : ∀ j, Continuous (f j)) :
    ∫ y : Fin n → I, (∏ j, f j (y j)) * Real.exp (-(θ * aa y)) / aa y ^ p =
      (1 / ((p - 1).factorial : ℝ)) * ∫ l in Set.Ioi (0 : ℝ),
        l ^ (p - 1) * Real.exp (-(l + θ)) *
          ∏ j, ∫ t : I, f j t * Real.exp (-((l + θ) * (t : ℝ))) := by
  have hfact : ((p - 1).factorial : ℝ) ≠ 0 := by positivity
  let Φ : (Fin n → I) → ℝ → ℝ := fun y l =>
    (∏ j, f j (y j)) * Real.exp (-(θ * aa y)) * (l ^ (p - 1) * Real.exp (-(aa y * l)))
  have hcontf : Continuous fun y : Fin n → I => ∏ j, f j (y j) :=
    continuous_finsetProd _ fun j _ => (hf j).comp (continuous_apply j)
  have hconta : Continuous fun y : Fin n → I => aa y := by
    unfold aa
    fun_prop
  have hpt : ∀ y : Fin n → I, (∏ j, f j (y j)) * Real.exp (-(θ * aa y)) / aa y ^ p =
      (1 / ((p - 1).factorial : ℝ)) * ∫ l in Set.Ioi (0 : ℝ), Φ y l := by
    intro y
    have ha : 0 < aa y := lt_of_lt_of_le one_pos (one_le_aa y)
    show _ = _ * ∫ l in Set.Ioi (0 : ℝ),
      (∏ j, f j (y j)) * Real.exp (-(θ * aa y)) * (l ^ (p - 1) * Real.exp (-(aa y * l)))
    rw [integral_const_mul, integral_pow_mul_exp_Ioi (p - 1) ha, Nat.sub_add_cancel hp]
    field_simp
  have hint : Integrable (Function.uncurry Φ)
      ((volume : Measure (Fin n → I)).prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    have hg1 : Integrable (fun y : Fin n → I => |∏ j, f j (y j)|) volume :=
      integrable_of_continuous hcontf.abs
    have hdom := hg1.mul_prod (integrableOn_pow_mul_exp (p - 1))
    have hae : ∀ᵐ z ∂((volume : Measure (Fin n → I)).prod (volume.restrict (Set.Ioi (0 : ℝ)))),
        z.2 ∈ Set.Ioi (0 : ℝ) := by
      have h1 : (volume : Measure (Fin n → I)).prod (volume.restrict (Set.Ioi (0 : ℝ))) =
          ((volume : Measure (Fin n → I)).prod volume).restrict
            (Set.univ ×ˢ Set.Ioi (0 : ℝ)) := by
        rw [← Measure.prod_restrict, Measure.restrict_univ]
      rw [h1]
      exact (ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ioi)).mono fun z hz => hz.2
    refine hdom.mono' ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      show Continuous fun z : (Fin n → I) × ℝ =>
        (∏ j, f j (z.1 j)) * Real.exp (-(θ * aa z.1)) *
          (z.2 ^ (p - 1) * Real.exp (-(aa z.1 * z.2)))
      have h2 : Continuous fun z : (Fin n → I) × ℝ => ∏ j, f j (z.1 j) :=
        hcontf.comp continuous_fst
      have h3 : Continuous fun z : (Fin n → I) × ℝ => aa z.1 := hconta.comp continuous_fst
      fun_prop
    · filter_upwards [hae] with z hz
      have hl : 0 < z.2 := hz
      have ha := one_le_aa z.1
      have h4 : Function.uncurry Φ z = (∏ j, f j (z.1 j)) *
          (Real.exp (-(θ * aa z.1)) * (z.2 ^ (p - 1) * Real.exp (-(aa z.1 * z.2)))) := by
        show (∏ j, f j (z.1 j)) * Real.exp (-(θ * aa z.1)) *
          (z.2 ^ (p - 1) * Real.exp (-(aa z.1 * z.2))) = _
        ring
      rw [h4, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [abs_of_nonneg (by positivity)]
      have h5 : Real.exp (-(θ * aa z.1)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have h6 : 0 ≤ θ * aa z.1 := mul_nonneg hθ (by linarith)
        linarith
      have h7 : Real.exp (-(aa z.1 * z.2)) ≤ Real.exp (-z.2) := by
        rw [Real.exp_le_exp]
        nlinarith
      have h8 : 0 ≤ z.2 ^ (p - 1) := pow_nonneg hl.le _
      calc Real.exp (-(θ * aa z.1)) * (z.2 ^ (p - 1) * Real.exp (-(aa z.1 * z.2)))
          ≤ 1 * (z.2 ^ (p - 1) * Real.exp (-z.2)) :=
            mul_le_mul h5 (mul_le_mul_of_nonneg_left h7 h8) (by positivity) zero_le_one
        _ = z.2 ^ (p - 1) * Real.exp (-z.2) := one_mul _
  simp only [hpt]
  rw [integral_const_mul]
  congr 1
  rw [integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioi fun l _ => ?_
  show ∫ y : Fin n → I, Φ y l = l ^ (p - 1) * Real.exp (-(l + θ)) *
    ∏ j, ∫ t : I, f j t * Real.exp (-((l + θ) * (t : ℝ)))
  rw [← integral_fintype_prod_volume_eq_prod
    (fun j (t : I) => f j t * Real.exp (-((l + θ) * (t : ℝ)))), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show (∏ j, f j (y j)) * Real.exp (-(θ * aa y)) * (l ^ (p - 1) * Real.exp (-(aa y * l))) =
    l ^ (p - 1) * Real.exp (-(l + θ)) * ∏ j, (f j (y j) * Real.exp (-((l + θ) * (y j : ℝ))))
  have e1 : Real.exp (-(θ * aa y)) * Real.exp (-(aa y * l)) =
      Real.exp (-(l + θ)) * ∏ j, Real.exp (-((l + θ) * (y j : ℝ))) := by
    rw [← Real.exp_sum, ← Real.exp_add, ← Real.exp_add, sum_neg_distrib, ← mul_sum]
    congr 1
    unfold aa
    ring
  rw [prod_mul_distrib]
  linear_combination ((∏ j, f j (y j)) * l ^ (p - 1)) * e1

end Laplace

end OMA

/-
# Part 7. Step C3: the one-dimensional integral
-/

namespace OMA

open StableMarriage.Unbalanced
open Finset
open Classical
open MeasureTheory unitInterval
open Filter Topology

section OneDim

theorem integral_I_exp_neg (c : ℝ) (hc : 0 < c) :
    ∫ t : I, Real.exp (-(c * (t : ℝ))) = (1 - Real.exp (-c)) / c := by
  rw [integral_I (fun t => Real.exp (-(c * t)))]
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => -(Real.exp (-(c * t)) / c)) (Real.exp (-(c * t))) t := by
    intro t _
    have h0 : HasDerivAt (fun t : ℝ => -t * c) (-c) t := by
      simpa using (hasDerivAt_id t).neg.mul_const c
    have hfun : (fun t : ℝ => -(c * t)) = fun t : ℝ => -t * c := by
      funext s
      ring
    have h1 : HasDerivAt (fun t : ℝ => -(c * t)) (-c) t := by
      rw [hfun]
      exact h0
    have h2 : HasDerivAt (fun t : ℝ => -(Real.exp (-(c * t)) / c))
        (-(Real.exp (-(c * t)) * -c / c)) t := ((h1.exp).div_const c).neg
    refine h2.congr_deriv ?_
    rw [mul_neg, neg_div, neg_neg, mul_div_assoc, div_self hc.ne', mul_one]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [mul_one, mul_zero, neg_zero, Real.exp_zero]
  ring

theorem integrableOn_exp_neg : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Ioi 0) := by
  simpa using integrableOn_pow_mul_exp 0

theorem integral_exp_neg_Ioi : ∫ l in Set.Ioi (0 : ℝ), Real.exp (-l) = 1 := by
  simpa using integral_pow_mul_exp_Ioi 0 one_pos

theorem one_sub_exp_neg_mem {l : ℝ} (hl : 0 < l) :
    0 ≤ 1 - Real.exp (-l) ∧ 1 - Real.exp (-l) ≤ 1 := by
  have h1 : Real.exp (-l) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have h2 := Real.exp_pos (-l)
  constructor <;> linarith

theorem integrableOn_exp_mul_pow (N : ℕ) :
    IntegrableOn (fun l : ℝ => Real.exp (-l) * (1 - Real.exp (-l)) ^ N) (Set.Ioi 0) := by
  refine Integrable.mono' integrableOn_exp_neg
    (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  refine (ae_restrict_mem measurableSet_Ioi).mono fun l hl => ?_
  have h := one_sub_exp_neg_mem (show (0 : ℝ) < l from hl)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg h.1 _))]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (pow_le_one₀ h.1 h.2)

theorem integral_exp_mul_pow_Ioi (N : ℕ) :
    ∫ l in Set.Ioi (0 : ℝ), Real.exp (-l) * (1 - Real.exp (-l)) ^ N = 1 / ((N : ℝ) + 1) := by
  have hN : ((N : ℝ) + 1) ≠ 0 := by positivity
  have hderiv : ∀ l ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun l : ℝ => (1 - Real.exp (-l)) ^ (N + 1) / ((N : ℝ) + 1))
        (Real.exp (-l) * (1 - Real.exp (-l)) ^ N) l := by
    intro l _
    have h1 : HasDerivAt (fun l : ℝ => 1 - Real.exp (-l)) (Real.exp (-l)) l := by
      have h2 := ((hasDerivAt_neg l).exp).const_sub 1
      simpa using h2
    have h3 := (h1.pow (N + 1)).div_const ((N : ℝ) + 1)
    refine h3.congr_deriv ?_
    push_cast
    field_simp
  have htend : Tendsto (fun l : ℝ => (1 - Real.exp (-l)) ^ (N + 1) / ((N : ℝ) + 1)) atTop
      (𝓝 (1 / ((N : ℝ) + 1))) := by
    have h1 : Tendsto (fun l : ℝ => Real.exp (-l)) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero
    have h2 := (((tendsto_const_nhds (x := (1 : ℝ))).sub h1).pow (N + 1)).div_const ((N : ℝ) + 1)
    simpa using h2
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (Continuous.continuousWithinAt (by fun_prop)) hderiv (integrableOn_exp_mul_pow N) htend
  rw [h]
  simp

/-- **Step C3.** The integral that controls the mean. -/
theorem I0_le (N : ℕ) (hN : 1 ≤ N) (L : ℝ) (hL : 0 < L) :
    ∫ l in Set.Ioi (0 : ℝ), Real.exp (-l) * (1 - Real.exp (-l)) ^ N / l ≤
      2 / L * (1 / ((N : ℝ) + 1)) + (1 - Real.exp (-(L / 2))) ^ (N - 1) := by
  have hc0 : 0 ≤ 1 - Real.exp (-(L / 2)) := (one_sub_exp_neg_mem (by positivity)).1
  have hrhs : ∫ l in Set.Ioi (0 : ℝ), (2 / L * (Real.exp (-l) * (1 - Real.exp (-l)) ^ N) +
      Real.exp (-l) * (1 - Real.exp (-(L / 2))) ^ (N - 1)) =
      2 / L * (1 / ((N : ℝ) + 1)) + (1 - Real.exp (-(L / 2))) ^ (N - 1) := by
    rw [integral_add ((integrableOn_exp_mul_pow N).const_mul _)
      (integrableOn_exp_neg.mul_const _), integral_const_mul, integral_mul_const,
      integral_exp_mul_pow_Ioi, integral_exp_neg_Ioi, one_mul]
  rw [← hrhs]
  refine integral_mono_of_nonneg ?_ ?_ ?_
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun l hl => ?_
    have h := one_sub_exp_neg_mem (show (0 : ℝ) < l from hl)
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg h.1 _)) (le_of_lt hl)
  · exact ((integrableOn_exp_mul_pow N).const_mul _).add (integrableOn_exp_neg.mul_const _)
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun l hl => ?_
    have hl0 : (0 : ℝ) < l := hl
    have h := one_sub_exp_neg_mem hl0
    have he := Real.exp_pos (-l)
    have hpow : 0 ≤ (1 - Real.exp (-l)) ^ N := pow_nonneg h.1 _
    show Real.exp (-l) * (1 - Real.exp (-l)) ^ N / l ≤
      2 / L * (Real.exp (-l) * (1 - Real.exp (-l)) ^ N) +
        Real.exp (-l) * (1 - Real.exp (-(L / 2))) ^ (N - 1)
    rcases le_or_gt (L / 2) l with hcase | hcase
    · have h1 : Real.exp (-l) * (1 - Real.exp (-l)) ^ N / l ≤
          2 / L * (Real.exp (-l) * (1 - Real.exp (-l)) ^ N) := by
        rw [div_eq_mul_inv, mul_comm (2 / L)]
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg he.le hpow)
        rw [inv_le_comm₀ hl0 (by positivity)]
        rw [inv_div]
        exact hcase
      have h2 : 0 ≤ Real.exp (-l) * (1 - Real.exp (-(L / 2))) ^ (N - 1) :=
        mul_nonneg he.le (pow_nonneg hc0 _)
      linarith
    · have h1 : (1 - Real.exp (-l)) ^ N / l ≤ (1 - Real.exp (-(L / 2))) ^ (N - 1) := by
        have h3 : 1 - Real.exp (-l) ≤ l := by
          have h4 := Real.add_one_le_exp (-l)
          linarith
        have h5 : (1 - Real.exp (-l)) ^ N = (1 - Real.exp (-l)) ^ (N - 1) * (1 - Real.exp (-l)) := by
          rw [← pow_succ, Nat.sub_add_cancel hN]
        have h6 : (1 - Real.exp (-l)) ^ (N - 1) ≤ (1 - Real.exp (-(L / 2))) ^ (N - 1) := by
          refine pow_le_pow_left₀ h.1 ?_ _
          have h7 : Real.exp (-(L / 2)) ≤ Real.exp (-l) := by
            rw [Real.exp_le_exp]
            linarith
          linarith
        rw [h5, mul_div_assoc]
        calc (1 - Real.exp (-l)) ^ (N - 1) * ((1 - Real.exp (-l)) / l)
            ≤ (1 - Real.exp (-l)) ^ (N - 1) * 1 :=
              mul_le_mul_of_nonneg_left ((div_le_one hl0).mpr h3) (pow_nonneg h.1 _)
          _ = (1 - Real.exp (-l)) ^ (N - 1) := mul_one _
          _ ≤ _ := h6
      have h2 : 0 ≤ 2 / L * (Real.exp (-l) * (1 - Real.exp (-l)) ^ N) := by positivity
      have h8 : Real.exp (-l) * (1 - Real.exp (-l)) ^ N / l =
          Real.exp (-l) * ((1 - Real.exp (-l)) ^ N / l) := by ring
      rw [h8]
      have h9 := mul_le_mul_of_nonneg_left h1 he.le
      linarith

end OneDim

end OMA

/-
# Part 8. Step C: the mean is at most `10 n / log n` with one extra worker
-/

namespace OMA

open StableMarriage.Unbalanced
open Finset
open Classical
open MeasureTheory unitInterval

section Mean

/-- The integral of `a ^ (-n)` over the cube. -/
theorem integral_inv_aa_pow (n : ℕ) (hn : 1 ≤ n) :
    ∫ y : Fin n → I, 1 / aa y ^ n = (1 / ((n - 1).factorial : ℝ)) *
      ∫ l in Set.Ioi (0 : ℝ), Real.exp (-l) * (1 - Real.exp (-l)) ^ n / l := by
  have h := laplace (n := n) n hn 0 le_rfl (fun _ _ => 1) (fun _ => continuous_const)
  simp only [prod_const_one, zero_mul, neg_zero, Real.exp_zero, one_mul, add_zero] at h
  rw [h]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun l hl => ?_
  have hl0 : (0 : ℝ) < l := hl
  simp only [integral_I_exp_neg l hl0, prod_const, card_univ, Fintype.card_fin]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_sub_cancel_left, div_pow]
  field_simp
  ring

/-- The mean as an explicit expression (before the numerical simplification). -/
theorem expected_le_aux (n : ℕ) (hn : 2 ≤ n) :
    expectedNumStableMatchings n (n + 1) ≤
      Real.exp 1 * n * (n + 1) * (2 / Real.log n * (1 / ((n : ℝ) + 1)) +
        (1 - Real.exp (-(Real.log n / 2))) ^ (n - 1)) := by
  have hn1 : 1 ≤ n := by omega
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hconta : Continuous fun y : Fin n → I => aa y := by
    unfold aa
    fun_prop
  have hint : Integrable (fun y : Fin n → I => Real.exp 1 / aa y ^ n) volume := by
    refine integrable_of_continuous ?_
    refine Continuous.div continuous_const (hconta.pow n) fun y => ?_
    have h1 := one_le_aa y
    positivity
  have h1 : ∫ y : Fin n → I, ∏ i, h 1 y i ≤ ∫ y : Fin n → I, Real.exp 1 / aa y ^ n :=
    integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun y => prod_nonneg fun i _ => h_nonneg 1 y i) hint
      (Filter.Eventually.of_forall fun y => prod_h_one_le y)
  have h2 : ∫ y : Fin n → I, Real.exp 1 / aa y ^ n =
      Real.exp 1 * ∫ y : Fin n → I, 1 / aa y ^ n := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show Real.exp 1 / aa y ^ n = Real.exp 1 * (1 / aa y ^ n)
    ring
  have h3 := I0_le n hn1 (Real.log n) hL
  have hdf : (n + 1).descFactorial n = (n + 1).factorial := by
    have h4 := Nat.factorial_mul_descFactorial (show n ≤ n + 1 by omega)
    rw [Nat.add_sub_cancel_left, Nat.factorial_one, one_mul] at h4
    exact h4
  have hfact : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * n * ((n - 1).factorial : ℝ) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn1
    rw [Nat.add_sub_cancel_left, Nat.factorial_succ, show 1 + k = k + 1 by ring,
      Nat.factorial_succ]
    push_cast
    ring
  have hfpos : (0 : ℝ) < ((n - 1).factorial : ℝ) := by positivity
  rw [expected_eq, integral_KP_eq, Nat.add_sub_cancel_left, hdf]
  calc ((n + 1).factorial : ℝ) * ∫ y : Fin n → I, ∏ i, h 1 y i
      ≤ ((n + 1).factorial : ℝ) * (Real.exp 1 * ((1 / ((n - 1).factorial : ℝ)) *
          ∫ l in Set.Ioi (0 : ℝ), Real.exp (-l) * (1 - Real.exp (-l)) ^ n / l)) := by
        rw [← integral_inv_aa_pow n hn1, ← h2]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = Real.exp 1 * n * (n + 1) *
          ∫ l in Set.Ioi (0 : ℝ), Real.exp (-l) * (1 - Real.exp (-l)) ^ n / l := by
        rw [hfact]
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)

/-- The exponentially small term. -/
theorem tail_small (n : ℕ) (hn : 200000 ≤ n) :
    Real.exp 1 * n * (n + 1) * (1 - Real.exp (-(Real.log n / 2))) ^ (n - 1) ≤
      4 * n / Real.log n := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (200000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hL : 0 < Real.log n := Real.log_pos (by linarith)
  have hLn : Real.log n ≤ n := by
    have h1 := Real.log_le_sub_one_of_pos hn0
    linarith
  set x := Real.exp (-(Real.log n / 2)) with hx
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x ≤ 1 := by
    rw [hx, Real.exp_le_one_iff]
    linarith
  have hxx : x * x = 1 / n := by
    rw [hx, ← Real.exp_add, show -(Real.log n / 2) + -(Real.log n / 2) = -Real.log n by ring,
      Real.exp_neg, Real.exp_log hn0, one_div]
  have hxn : x * n = 1 / x := by
    field_simp
    have h1 : x * x * n = 1 := by
      rw [hxx]
      field_simp
    linarith
  have h1 : (1 - x) ^ (n - 1) ≤ Real.exp (-(x * ((n - 1 : ℕ) : ℝ))) := by
    have h2 : 1 - x ≤ Real.exp (-x) := by
      have h3 := Real.add_one_le_exp (-x)
      linarith
    have h4 := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 - x) h2 (n - 1)
    rw [← Real.exp_nat_mul] at h4
    rw [show -(x * ((n - 1 : ℕ) : ℝ)) = ((n - 1 : ℕ) : ℝ) * -x by ring]
    exact h4
  have h5 : 1 / x - 1 ≤ x * ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn1, Nat.cast_one, mul_sub, hxn]
    linarith
  have hs0 : 0 < 1 / x := by positivity
  have h6 : (1 / x) ^ 6 / 46656 ≤ Real.exp (1 / x) := by
    have h7 := Real.add_one_le_exp (1 / x / 6)
    have h8 : (1 / x / 6) ^ 6 ≤ Real.exp (1 / x / 6) ^ 6 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 6
    rw [← Real.exp_nat_mul] at h8
    have h9 : ((6 : ℕ) : ℝ) * (1 / x / 6) = 1 / x := by
      push_cast
      ring
    rw [h9] at h8
    have h10 : (1 / x / 6) ^ 6 = (1 / x) ^ 6 / 46656 := by
      rw [div_pow]
      norm_num
    linarith
  have hs6 : (1 / x) ^ 6 = (n : ℝ) ^ 3 := by
    have h7 : (1 / x) ^ 2 = n := by
      rw [div_pow, one_pow, pow_two, hxx]
      field_simp
    calc (1 / x) ^ 6 = ((1 / x) ^ 2) ^ 3 := by ring
      _ = (n : ℝ) ^ 3 := by rw [h7]
  rw [hs6] at h6
  have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  have h11 : (1 - x) ^ (n - 1) ≤ Real.exp 1 * 46656 / (n : ℝ) ^ 3 := by
    have h12 : Real.exp (-(x * ((n - 1 : ℕ) : ℝ))) ≤ Real.exp (1 - 1 / x) := by
      rw [Real.exp_le_exp]
      linarith
    have h13 : Real.exp (1 - 1 / x) = Real.exp 1 / Real.exp (1 / x) := by
      rw [Real.exp_sub]
    have h14 : Real.exp 1 / Real.exp (1 / x) ≤ Real.exp 1 / ((n : ℝ) ^ 3 / 46656) :=
      div_le_div_of_nonneg_left (Real.exp_pos 1).le (by positivity) h6
    have h15 : Real.exp 1 / ((n : ℝ) ^ 3 / 46656) = Real.exp 1 * 46656 / (n : ℝ) ^ 3 := by
      field_simp
    linarith
  have he : Real.exp 1 * Real.exp 1 ≤ 8 := by
    have h16 := Real.exp_one_lt_d9
    have h17 := Real.exp_pos 1
    nlinarith
  have h18 : Real.exp 1 * n * (n + 1) * (1 - x) ^ (n - 1) ≤
      Real.exp 1 * n * (n + 1) * (Real.exp 1 * 46656 / (n : ℝ) ^ 3) :=
    mul_le_mul_of_nonneg_left h11 (by positivity)
  have h19 : Real.exp 1 * n * (n + 1) * (Real.exp 1 * 46656 / (n : ℝ) ^ 3) ≤
      4 * n / Real.log n := by
    rw [← mul_div_assoc, div_le_div_iff₀ hn3 hL]
    have h20 : Real.exp 1 * n * (n + 1) * (Real.exp 1 * 46656) * Real.log n ≤
        8 * n * (2 * n) * 46656 * n := by
      have h21 : Real.exp 1 * n * (n + 1) * (Real.exp 1 * 46656) * Real.log n =
          (Real.exp 1 * Real.exp 1) * (n * (n + 1) * 46656 * Real.log n) := by ring
      rw [h21]
      have h22 : (n : ℝ) * (n + 1) * 46656 * Real.log n ≤ n * (2 * n) * 46656 * n := by
        have h23 : (n : ℝ) + 1 ≤ 2 * n := by linarith
        have h24 : (n : ℝ) * (n + 1) * 46656 ≤ n * (2 * n) * 46656 := by nlinarith
        calc (n : ℝ) * (n + 1) * 46656 * Real.log n ≤ n * (2 * n) * 46656 * Real.log n :=
              mul_le_mul_of_nonneg_right h24 hL.le
          _ ≤ n * (2 * n) * 46656 * n := mul_le_mul_of_nonneg_left hLn (by positivity)
      calc Real.exp 1 * Real.exp 1 * (n * (n + 1) * 46656 * Real.log n)
          ≤ 8 * (n * (2 * n) * 46656 * n) :=
            mul_le_mul he h22 (by positivity) (by norm_num)
        _ = 8 * n * (2 * n) * 46656 * n := by ring
    have h25 : 8 * (n : ℝ) * (2 * n) * 46656 * n ≤ 4 * n * (n : ℝ) ^ 3 := by
      have h26 : (746496 : ℝ) ≤ 4 * n := by linarith
      nlinarith [hn3]
    linarith
  linarith

/-- **Step C.** With `n` firms and `n + 1` workers the expected number of stable matchings is at
most `10 n / log n`, for `n ≥ 200000`. -/
theorem expected_le (n : ℕ) (hn : 200000 ≤ n) :
    expectedNumStableMatchings n (n + 1) ≤ 10 * n / Real.log n := by
  have hnR : (200000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hL : 0 < Real.log n := Real.log_pos (by linarith)
  have h1 := expected_le_aux n (by omega)
  have h2 := tail_small n hn
  have he := Real.exp_one_lt_d9
  have h3 : Real.exp 1 * n * (n + 1) * (2 / Real.log n * (1 / ((n : ℝ) + 1))) =
      2 * Real.exp 1 * n / Real.log n := by
    field_simp
  have h4 : 2 * Real.exp 1 * n / Real.log n ≤ 6 * n / Real.log n := by
    rw [div_le_div_iff_of_pos_right hL]
    nlinarith
  have h5 : 6 * (n : ℝ) / Real.log n + 4 * n / Real.log n = 10 * n / Real.log n := by ring
  rw [mul_add] at h1
  linarith

end Mean

end OMA

/-
# Part 9. Counting with two marked elements, and the general worker expansion

Corollary K2 of `Q\sm2_lean_route.md`, and the worker-side sums of Step B.
-/

namespace OMA

open StableMarriage.Unbalanced
open Finset
open Classical
open MeasureTheory unitInterval

section Counting2

/-- **Corollary K2.** The rankings with `b` ahead of `a` and `a` ahead of all of `T`. -/
theorem card_first_two {N : ℕ} (a b : Fin N) (T : Finset (Fin N)) (ha : a ∉ T) (hb : b ∉ T)
    (hab : a ≠ b) :
    ((univ.filter fun π : Equiv.Perm (Fin N) => π b < π a ∧ ∀ j ∈ T, π a < π j).card : ℝ) =
      (N.factorial : ℝ) / (((T.card : ℝ) + 1) * ((T.card : ℝ) + 2)) := by
  have h1 := card_first a T ha
  have h2 := card_first a (insert b T) (by
    rw [mem_insert]
    rintro (h | h)
    · exact hab h
    · exact ha h)
  rw [card_insert_of_notMem hb] at h2
  have hpart : (univ.filter fun π : Equiv.Perm (Fin N) => ∀ j ∈ T, π a < π j).card =
      (univ.filter fun π : Equiv.Perm (Fin N) => π b < π a ∧ ∀ j ∈ T, π a < π j).card +
      (univ.filter fun π : Equiv.Perm (Fin N) => ∀ j ∈ insert b T, π a < π j).card := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext π
      simp only [mem_filter, mem_univ, true_and, mem_union, mem_insert, forall_eq_or_imp]
      constructor
      · intro h
        rcases lt_or_gt_of_ne (fun h' : π b = π a => hab (π.injective h').symm) with h3 | h3
        · exact Or.inl ⟨h3, h⟩
        · exact Or.inr ⟨h3, h⟩
      · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
    · rw [disjoint_left]
      intro π h3 h4
      simp only [mem_filter, mem_univ, true_and, mem_insert, forall_eq_or_imp] at h3 h4
      exact absurd h3.1 (not_lt.mpr h4.1.le)
  have h1' : ((T.card : ℝ) + 1) *
      ((univ.filter fun π : Equiv.Perm (Fin N) => ∀ j ∈ T, π a < π j).card : ℝ) =
      (N.factorial : ℝ) := by exact_mod_cast h1
  have h2' : ((T.card : ℝ) + 2) *
      ((univ.filter fun π : Equiv.Perm (Fin N) => ∀ j ∈ insert b T, π a < π j).card : ℝ) =
      (N.factorial : ℝ) := by
    have h3 : (((T.card + 1 + 1 : ℕ) : ℝ)) *
        ((univ.filter fun π : Equiv.Perm (Fin N) => ∀ j ∈ insert b T, π a < π j).card : ℝ) =
        (N.factorial : ℝ) := by exact_mod_cast h2
    rw [← h3]
    push_cast
    ring
  have hp' : ((univ.filter fun π : Equiv.Perm (Fin N) => ∀ j ∈ T, π a < π j).card : ℝ) =
      ((univ.filter fun π : Equiv.Perm (Fin N) => π b < π a ∧ ∀ j ∈ T, π a < π j).card : ℝ) +
      ((univ.filter fun π : Equiv.Perm (Fin N) => ∀ j ∈ insert b T, π a < π j).card : ℝ) := by
    exact_mod_cast hpart
  have ht1 : (0 : ℝ) < (T.card : ℝ) + 1 := by positivity
  have ht2 : (0 : ℝ) < (T.card : ℝ) + 2 := by positivity
  rw [eq_div_iff (by positivity)]
  rw [hp'] at h1'
  nlinarith

theorem integral_I_mul_one_sub_pow (N : ℕ) :
    ∫ t : I, (t : ℝ) * (1 - (t : ℝ)) ^ N = 1 / (((N : ℝ) + 1) * ((N : ℝ) + 2)) := by
  have h1 : ∀ t : I, (t : ℝ) * (1 - (t : ℝ)) ^ N = (1 - (t : ℝ)) ^ N - (1 - (t : ℝ)) ^ (N + 1) := by
    intro t
    ring
  simp only [h1]
  rw [integral_sub (integrable_of_continuous (by fun_prop))
    (integrable_of_continuous (by fun_prop)), integral_I_one_sub_pow, integral_I_one_sub_pow]
  have ht1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  push_cast
  field_simp
  ring

end Counting2

section WorkerSums

variable {n : ℕ}

/-- The worker expansion, one marked firm: the firms of `S` ranked ahead of `a` each contribute a
factor `1 - c i`. -/
theorem sum_perm_prod (S : Finset (Fin n)) (a : Fin n) (ha : a ∉ S) (c : Fin n → ℝ) :
    ∑ ρ : Equiv.Perm (Fin n), ∏ i ∈ S, (if ρ i < ρ a then 1 - c i else 1) =
      (n.factorial : ℝ) * ∫ y : I, ∏ i ∈ S, (1 - c i * (y : ℝ)) := by
  have hQ : ∀ ρ : Equiv.Perm (Fin n), ∏ i ∈ S, (if ρ i < ρ a then 1 - c i else 1) =
      ∑ T ∈ S.powerset, (∏ i ∈ T, (-c i)) * (if ∀ i ∈ T, ρ i < ρ a then 1 else 0) := by
    intro ρ
    have h1 : ∏ i ∈ S, (if ρ i < ρ a then 1 - c i else 1) =
        ∏ i ∈ S, (1 + (if ρ i < ρ a then -c i else 0)) := by
      refine prod_congr rfl fun i _ => ?_
      split_ifs <;> ring
    rw [h1, prod_one_add]
    refine sum_congr rfl fun T _ => ?_
    rw [prod_ite_zero]
    split_ifs <;> simp
  have hint : ∫ y : I, ∏ i ∈ S, (1 - c i * (y : ℝ)) =
      ∑ T ∈ S.powerset, (∏ i ∈ T, (-c i)) * (1 / ((T.card : ℝ) + 1)) := by
    have h2 : ∀ y : I, ∏ i ∈ S, (1 - c i * (y : ℝ)) =
        ∑ T ∈ S.powerset, (∏ i ∈ T, (-c i)) * (y : ℝ) ^ T.card := by
      intro y
      have h3 : ∀ i, 1 - c i * (y : ℝ) = 1 + (-c i) * y := fun i => by ring
      simp only [h3]
      rw [prod_one_add]
      refine sum_congr rfl fun T _ => ?_
      rw [prod_mul_distrib, prod_const]
    simp only [h2]
    rw [integral_finsetSum]
    · refine sum_congr rfl fun T _ => ?_
      rw [integral_const_mul, integral_I_pow]
    · intro T _
      exact integrable_of_continuous (by fun_prop)
  simp only [hQ]
  rw [sum_comm, hint, mul_sum]
  refine sum_congr rfl fun T hT => ?_
  rw [← mul_sum, sum_boole]
  have hk : a ∉ T := fun h => ha (mem_powerset.mp hT h)
  have hc := card_last a T hk
  have h4 : ((univ.filter fun ρ : Equiv.Perm (Fin n) => ∀ i ∈ T, ρ i < ρ a).card : ℝ) =
      (n.factorial : ℝ) / ((T.card : ℝ) + 1) := by
    rw [eq_div_iff (by positivity)]
    have h5 : ((univ.filter fun ρ : Equiv.Perm (Fin n) => ∀ i ∈ T, ρ i < ρ a).card : ℝ) *
        ((T.card : ℝ) + 1) = ((T.card + 1) * (univ.filter fun ρ : Equiv.Perm (Fin n) =>
          ∀ i ∈ T, ρ i < ρ a).card : ℕ) := by
      push_cast
      ring
    rw [h5, hc]
  rw [h4]
  ring

/-- The worker expansion, two marked firms: `b` must be ahead of `a`. -/
theorem sum_perm_prod_two (S : Finset (Fin n)) (a b : Fin n) (ha : a ∉ S) (hb : b ∉ S)
    (hab : a ≠ b) (c : Fin n → ℝ) :
    ∑ ρ : Equiv.Perm (Fin n), (if ρ b < ρ a then (1 : ℝ) else 0) *
        ∏ i ∈ S, (if ρ i < ρ a then 1 - c i else 1) =
      (n.factorial : ℝ) * ∫ y : I, (y : ℝ) * ∏ i ∈ S, (1 - c i * (y : ℝ)) := by
  have hQ : ∀ ρ : Equiv.Perm (Fin n), (if ρ b < ρ a then (1 : ℝ) else 0) *
        ∏ i ∈ S, (if ρ i < ρ a then 1 - c i else 1) =
      ∑ T ∈ S.powerset, (∏ i ∈ T, (-c i)) *
        (if ∀ i ∈ insert b T, ρ i < ρ a then 1 else 0) := by
    intro ρ
    have h1 : ∏ i ∈ S, (if ρ i < ρ a then 1 - c i else 1) =
        ∏ i ∈ S, (1 + (if ρ i < ρ a then -c i else 0)) := by
      refine prod_congr rfl fun i _ => ?_
      split_ifs <;> ring
    rw [h1, prod_one_add, mul_sum]
    refine sum_congr rfl fun T _ => ?_
    rw [prod_ite_zero]
    simp only [mem_insert, forall_eq_or_imp]
    by_cases h2 : ρ b < ρ a
    · by_cases h3 : ∀ i ∈ T, ρ i < ρ a
      · simp [h2, h3]
      · simp [h2, h3]
    · simp [h2]
  have hint : ∫ y : I, (y : ℝ) * ∏ i ∈ S, (1 - c i * (y : ℝ)) =
      ∑ T ∈ S.powerset, (∏ i ∈ T, (-c i)) * (1 / ((T.card : ℝ) + 2)) := by
    have h2 : ∀ y : I, (y : ℝ) * ∏ i ∈ S, (1 - c i * (y : ℝ)) =
        ∑ T ∈ S.powerset, (∏ i ∈ T, (-c i)) * (y : ℝ) ^ (T.card + 1) := by
      intro y
      have h3 : ∀ i, 1 - c i * (y : ℝ) = 1 + (-c i) * y := fun i => by ring
      simp only [h3]
      rw [prod_one_add, mul_sum]
      refine sum_congr rfl fun T _ => ?_
      rw [prod_mul_distrib, prod_const]
      ring
    simp only [h2]
    rw [integral_finsetSum]
    · refine sum_congr rfl fun T _ => ?_
      rw [integral_const_mul, integral_I_pow]
      push_cast
      ring
    · intro T _
      exact integrable_of_continuous (by fun_prop)
  simp only [hQ]
  rw [sum_comm, hint, mul_sum]
  refine sum_congr rfl fun T hT => ?_
  rw [← mul_sum, sum_boole]
  have hTS := mem_powerset.mp hT
  have hbT : b ∉ T := fun h => hb (hTS h)
  have hk : a ∉ insert b T := by
    rw [mem_insert]
    rintro (h | h)
    · exact hab h
    · exact ha (hTS h)
  have hc := card_last a (insert b T) hk
  rw [card_insert_of_notMem hbT] at hc
  have h4 : ((univ.filter fun ρ : Equiv.Perm (Fin n) => ∀ i ∈ insert b T, ρ i < ρ a).card : ℝ) =
      (n.factorial : ℝ) / ((T.card : ℝ) + 2) := by
    rw [eq_div_iff (by positivity)]
    have h5 : ((univ.filter fun ρ : Equiv.Perm (Fin n) =>
        ∀ i ∈ insert b T, ρ i < ρ a).card : ℝ) * ((T.card : ℝ) + 2) =
        ((T.card + 1 + 1) * (univ.filter fun ρ : Equiv.Perm (Fin n) =>
          ∀ i ∈ insert b T, ρ i < ρ a).card : ℕ) := by
      push_cast
      ring
    rw [h5, hc]
  rw [h4]
  ring

end WorkerSums

end OMA

/-
# Part 10. Step B: typed pairs of matchings and the sufficient event (Lemma B1)
-/

namespace OMA

open StableMarriage.Unbalanced
open Finset
open Classical

section Pairs

variable {n m : ℕ}

/-- A permutation with a type split: `σ` deranges `A` (type A) and `B` (type B) and fixes the
rest. -/
structure Typed (A B : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) : Prop where
  disj : Disjoint A B
  mapA : ∀ i ∈ A, σ i ∈ A ∧ σ i ≠ i
  mapB : ∀ i ∈ B, σ i ∈ B ∧ σ i ≠ i
  fix : ∀ i, i ∉ A → i ∉ B → σ i = i

theorem Typed.symm_fix {A B : Finset (Fin n)} {σ : Equiv.Perm (Fin n)} (h : Typed A B σ)
    {i : Fin n} (hiA : i ∉ A) (hiB : i ∉ B) : σ.symm i = i := by
  rw [Equiv.symm_apply_eq]
  exact (h.fix i hiA hiB).symm

theorem Typed.symm_memA {A B : Finset (Fin n)} {σ : Equiv.Perm (Fin n)} (h : Typed A B σ)
    {i : Fin n} (hi : i ∈ A) : σ.symm i ∈ A := by
  by_contra hc
  by_cases hB : σ.symm i ∈ B
  · have h1 := (h.mapB _ hB).1
    rw [Equiv.apply_symm_apply] at h1
    exact (Finset.disjoint_left.mp h.disj hi) h1
  · have h1 := h.fix _ hc hB
    rw [Equiv.apply_symm_apply] at h1
    rw [← h1] at hc
    exact hc hi

theorem Typed.symm_memB {A B : Finset (Fin n)} {σ : Equiv.Perm (Fin n)} (h : Typed A B σ)
    {i : Fin n} (hi : i ∈ B) : σ.symm i ∈ B := by
  by_contra hc
  by_cases hA : σ.symm i ∈ A
  · have h1 := (h.mapA _ hA).1
    rw [Equiv.apply_symm_apply] at h1
    exact (Finset.disjoint_left.mp h.disj h1) hi
  · have h1 := h.fix _ hA hc
    rw [Equiv.apply_symm_apply] at h1
    rw [← h1] at hc
    exact hc hi

theorem Typed.ne_of_mem {A B : Finset (Fin n)} {σ : Equiv.Perm (Fin n)} (h : Typed A B σ)
    {i : Fin n} (hi : i ∈ A ∪ B) : σ i ≠ i := by
  rcases mem_union.mp hi with h1 | h1
  · exact (h.mapA i h1).2
  · exact (h.mapB i h1).2

theorem Typed.symm_ne_of_mem {A B : Finset (Fin n)} {σ : Equiv.Perm (Fin n)} (h : Typed A B σ)
    {i : Fin n} (hi : i ∈ A ∪ B) : σ.symm i ≠ i := by
  intro h1
  rw [Equiv.symm_apply_eq] at h1
  exact h.ne_of_mem hi h1.symm

/-- The second matching: firm `i` gets the worker of firm `σ i`. -/
def secondMatching (μ : Matching n m) (σ : Equiv.Perm (Fin n)) : Matching n m :=
  σ.toEmbedding.trans μ

theorem secondMatching_apply (μ : Matching n m) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    secondMatching μ σ i = μ (σ i) := rfl

/-- Index of the worse partner of firm `i`. -/
noncomputable def wk (A : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) (i : Fin n) : Fin n :=
  if i ∈ A then σ i else i

/-- Index of the better partner of firm `i`. -/
noncomputable def bk (A : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) (i : Fin n) : Fin n :=
  if i ∈ A then i else σ i

/-- The worse firm of the worker of firm `k`. -/
noncomputable def phi (B : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) (k : Fin n) : Fin n :=
  if k ∈ B then σ.symm k else k

/-- The better firm of the worker of firm `k`. -/
noncomputable def psi (B : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) (k : Fin n) : Fin n :=
  if k ∈ B then k else σ.symm k

/-- The workers that firm `i` must rank behind its worse partner. -/
noncomputable def threat2 (μ : Matching n m) (B : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (w : Fin m → Equiv.Perm (Fin n)) (i : Fin n) : Finset (Fin m) :=
  univ.filter fun j => (∀ k, μ k ≠ j) ∨
    ∃ k, μ k = j ∧ k ≠ i ∧ k ≠ σ i ∧ w j i < w j (phi B σ k)

/-- The firm-side condition of the sufficient event. -/
def FirmOK (μ : Matching n m) (A B : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (w : Fin m → Equiv.Perm (Fin n)) (i : Fin n) (π : Equiv.Perm (Fin m)) : Prop :=
  (∀ j ∈ threat2 μ B σ w i, π (μ (wk A σ i)) < π j) ∧
    (i ∈ A ∪ B → π (μ (bk A σ i)) < π (μ (wk A σ i)))

/-- The worker-side condition of the sufficient event. -/
def WorkerOK (μ : Matching n m) (A B : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (w : Fin m → Equiv.Perm (Fin n)) : Prop :=
  ∀ k ∈ A ∪ B, w (μ k) (psi B σ k) < w (μ k) (phi B σ k)

/-- The sufficient event of Lemma B1. -/
def Suff (p : Profile n m) (μ : Matching n m) (A B : Finset (Fin n))
    (σ : Equiv.Perm (Fin n)) : Prop :=
  (∀ i, FirmOK μ A B σ p.workerRank i (p.firmRank i)) ∧ WorkerOK μ A B σ p.workerRank

/-- **Lemma B1.** The sufficient event implies that both matchings are stable. -/
theorem suff_stable {A B : Finset (Fin n)} {σ : Equiv.Perm (Fin n)} (h : Typed A B σ)
    (p : Profile n m) (μ : Matching n m) (hs : Suff p μ A B σ) :
    IsStable p μ ∧ IsStable p (secondMatching μ σ) := by
  obtain ⟨hF, hW⟩ := hs
  constructor
  · intro i j hb
    obtain ⟨hne, hlt, hw⟩ := hb
    have hle : p.firmRank i (μ i) ≤ p.firmRank i (μ (wk A σ i)) := by
      by_cases hiA : i ∈ A
      · have h1 := (hF i).2 (mem_union_left B hiA)
        simp only [bk, wk, if_pos hiA] at h1 ⊢
        exact h1.le
      · simp only [wk, if_neg hiA]
        exact le_rfl
    have hlt2 := lt_of_lt_of_le hlt hle
    have hmem : j ∈ threat2 μ B σ p.workerRank i := by
      simp only [threat2, mem_filter, mem_univ, true_and]
      by_cases hj : ∀ k, μ k ≠ j
      · exact Or.inl hj
      · right
        push Not at hj
        obtain ⟨k, hk⟩ := hj
        have hki : k ≠ i := fun h' => hne (h' ▸ hk)
        have h3 := hw k hk
        refine ⟨k, hk, hki, ?_, ?_⟩
        · intro hkσ
          have hσi : σ i ≠ i := fun h' => hki (hkσ.trans h')
          by_cases hiA : i ∈ A
          · simp only [wk, if_pos hiA] at hlt2
            rw [← hk, hkσ] at hlt2
            exact lt_irrefl _ hlt2
          · have hiB : i ∈ B := by
              by_contra hiB
              exact hσi (h.fix i hiA hiB)
            have hkB : k ∈ B := hkσ ▸ (h.mapB i hiB).1
            have h1 := hW k (mem_union_right A hkB)
            simp only [psi, phi, if_pos hkB] at h1
            have h2 : σ.symm k = i := by rw [hkσ, Equiv.symm_apply_apply]
            rw [h2, hk] at h1
            exact lt_asymm h1 h3
        · by_cases hkB : k ∈ B
          · have h1 := hW k (mem_union_right A hkB)
            simp only [psi, phi, if_pos hkB] at h1 ⊢
            rw [hk] at h1
            exact lt_trans h3 h1
          · simp only [phi, if_neg hkB]
            exact h3
    exact absurd hlt2 (not_lt.mpr ((hF i).1 j hmem).le)
  · intro i j hb
    obtain ⟨hne, hlt, hw⟩ := hb
    rw [secondMatching_apply] at hne hlt
    have hle : p.firmRank i (μ (σ i)) ≤ p.firmRank i (μ (wk A σ i)) := by
      by_cases hiA : i ∈ A
      · simp only [wk, if_pos hiA]
        exact le_rfl
      · by_cases hiB : i ∈ B
        · have h1 := (hF i).2 (mem_union_right A hiB)
          simp only [bk, wk, if_neg hiA] at h1 ⊢
          exact h1.le
        · simp only [wk, if_neg hiA]
          rw [h.fix i hiA hiB]
    have hlt2 := lt_of_lt_of_le hlt hle
    have hmem : j ∈ threat2 μ B σ p.workerRank i := by
      simp only [threat2, mem_filter, mem_univ, true_and]
      by_cases hj : ∀ k, μ k ≠ j
      · exact Or.inl hj
      · right
        push Not at hj
        obtain ⟨k, hk⟩ := hj
        have hkσ : k ≠ σ i := fun h' => hne (h' ▸ hk)
        have h3 := hw (σ.symm k) (by
          rw [secondMatching_apply, Equiv.apply_symm_apply]
          exact hk)
        refine ⟨k, hk, ?_, hkσ, ?_⟩
        · intro hki
          have hσi : σ i ≠ i := fun h' => hkσ (hki.trans h'.symm)
          by_cases hiA : i ∈ A
          · have hiB : i ∉ B := Finset.disjoint_left.mp h.disj hiA
            have h1 := hW i (mem_union_left B hiA)
            simp only [psi, phi, if_neg hiB] at h1
            rw [hki] at hk h3
            rw [hk] at h1
            exact lt_asymm h1 h3
          · simp only [wk, if_neg hiA] at hlt2
            rw [← hk, hki] at hlt2
            exact lt_irrefl _ hlt2
        · by_cases hkB : k ∈ B
          · simp only [phi, if_pos hkB]
            exact h3
          · by_cases hkA : k ∈ A
            · have h1 := hW k (mem_union_left B hkA)
              simp only [psi, phi, if_neg hkB] at h1 ⊢
              rw [hk] at h1
              exact lt_trans h3 h1
            · simp only [phi, if_neg hkB]
              rw [h.symm_fix hkA hkB] at h3
              exact h3
    exact absurd hlt2 (not_lt.mpr ((hF i).1 j hmem).le)

end Pairs

end OMA

/-
# Part 11. Step B: counting the sufficient event (firms)
-/

namespace OMA

open StableMarriage.Unbalanced
open Finset
open Classical
open MeasureTheory unitInterval

section PairCount

variable {n m : ℕ}

/-- The number of profiles in the sufficient event. -/
theorem card_suff (μ : Matching n m) (A B : Finset (Fin n)) (τ : Equiv.Perm (Fin n)) :
    (univ.filter fun p : Profile n m => Suff p μ A B τ).card =
      ∑ w : Fin m → Equiv.Perm (Fin n), (if WorkerOK μ A B τ w then 1 else 0) *
        ∏ i : Fin n, (univ.filter fun π : Equiv.Perm (Fin m) => FirmOK μ A B τ w i π).card := by
  let e : Profile n m ≃ (Fin n → Equiv.Perm (Fin m)) × (Fin m → Equiv.Perm (Fin n)) :=
    { toFun := fun p => (p.firmRank, p.workerRank)
      invFun := fun q => ⟨q.1, q.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 : (univ.filter fun p : Profile n m => Suff p μ A B τ).card =
      ∑ q : (Fin n → Equiv.Perm (Fin m)) × (Fin m → Equiv.Perm (Fin n)),
        if Suff (e.symm q) μ A B τ then 1 else 0 := by
    rw [card_filter]
    exact (e.symm.sum_comp (fun p => if Suff p μ A B τ then 1 else 0)).symm
  rw [h1, Fintype.sum_prod_type_right]
  refine sum_congr rfl fun w _ => ?_
  by_cases hW : WorkerOK μ A B τ w
  · rw [if_pos hW, one_mul, ← card_filter, ← Fintype.card_piFinset]
    congr 1
    ext f
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    show ((∀ i, FirmOK μ A B τ w i (f i)) ∧ WorkerOK μ A B τ w) ↔ _
    exact ⟨fun h2 => h2.1, fun h2 => ⟨h2, hW⟩⟩
  · rw [if_neg hW, zero_mul]
    refine sum_eq_zero fun f _ => ?_
    rw [if_neg]
    exact fun h2 => hW h2.2

theorem notMem_threat2 (μ : Matching n m) (B : Finset (Fin n)) (τ : Equiv.Perm (Fin n))
    (w : Fin m → Equiv.Perm (Fin n)) (i k₀ : Fin n) (hk₀ : k₀ = i ∨ k₀ = τ i) :
    μ k₀ ∉ threat2 μ B τ w i := by
  intro hmem
  rcases (mem_filter.mp hmem).2 with h1 | ⟨k, hk, hki, hkτ, _⟩
  · exact h1 k₀ rfl
  · have h2 := μ.injective hk
    subst h2
    rcases hk₀ with h3 | h3
    · exact hki h3
    · exact hkτ h3

/-- The number of admissible lists of firm `i`, as an integral. -/
theorem card_firmOK {A B : Finset (Fin n)} {τ : Equiv.Perm (Fin n)} (h : Typed A B τ)
    (μ : Matching n m) (w : Fin m → Equiv.Perm (Fin n)) (i : Fin n) :
    ((univ.filter fun π : Equiv.Perm (Fin m) => FirmOK μ A B τ w i π).card : ℝ) =
      (m.factorial : ℝ) * ∫ t : I, (t : ℝ) ^ (if i ∈ A ∪ B then 1 else 0) *
        (1 - (t : ℝ)) ^ (threat2 μ B τ w i).card := by
  have hwk : wk A τ i = i ∨ wk A τ i = τ i := by
    unfold wk
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hbk : bk A τ i = i ∨ bk A τ i = τ i := by
    unfold bk
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have ha := notMem_threat2 μ B τ w i (wk A τ i) hwk
  have hb := notMem_threat2 μ B τ w i (bk A τ i) hbk
  by_cases hi : i ∈ A ∪ B
  · have hne : wk A τ i ≠ bk A τ i := by
      have h1 := h.ne_of_mem hi
      unfold wk bk
      split_ifs
      · exact h1
      · exact fun h2 => h1 h2.symm
    have hab : μ (wk A τ i) ≠ μ (bk A τ i) := fun h2 => hne (μ.injective h2)
    have hset : (univ.filter fun π : Equiv.Perm (Fin m) => FirmOK μ A B τ w i π) =
        univ.filter fun π : Equiv.Perm (Fin m) => π (μ (bk A τ i)) < π (μ (wk A τ i)) ∧
          ∀ j ∈ threat2 μ B τ w i, π (μ (wk A τ i)) < π j := by
      ext π
      rw [mem_filter, mem_filter]
      simp only [mem_univ, true_and]
      show ((∀ j ∈ threat2 μ B τ w i, π (μ (wk A τ i)) < π j) ∧
        (i ∈ A ∪ B → π (μ (bk A τ i)) < π (μ (wk A τ i)))) ↔ _
      exact ⟨fun h2 => ⟨h2.2 hi, h2.1⟩, fun h2 => ⟨h2.2, fun _ => h2.1⟩⟩
    rw [hset, card_first_two _ _ _ ha hb hab, if_pos hi]
    simp only [pow_one]
    rw [integral_I_mul_one_sub_pow]
    ring
  · have hset : (univ.filter fun π : Equiv.Perm (Fin m) => FirmOK μ A B τ w i π) =
        univ.filter fun π : Equiv.Perm (Fin m) =>
          ∀ j ∈ threat2 μ B τ w i, π (μ (wk A τ i)) < π j := by
      ext π
      rw [mem_filter, mem_filter]
      simp only [mem_univ, true_and]
      show ((∀ j ∈ threat2 μ B τ w i, π (μ (wk A τ i)) < π j) ∧
        (i ∈ A ∪ B → π (μ (bk A τ i)) < π (μ (wk A τ i)))) ↔ _
      exact ⟨fun h2 => h2.1, fun h2 => ⟨h2, fun h3 => absurd h3 hi⟩⟩
    have hc := card_first (μ (wk A τ i)) (threat2 μ B τ w i) ha
    rw [hset, if_neg hi]
    simp only [pow_zero, one_mul]
    rw [integral_I_one_sub_pow, mul_one_div, eq_div_iff (by positivity)]
    have h5 : ((univ.filter fun π : Equiv.Perm (Fin m) =>
        ∀ j ∈ threat2 μ B τ w i, π (μ (wk A τ i)) < π j).card : ℝ) *
        (((threat2 μ B τ w i).card : ℝ) + 1) =
        (((threat2 μ B τ w i).card + 1) * (univ.filter fun π : Equiv.Perm (Fin m) =>
          ∀ j ∈ threat2 μ B τ w i, π (μ (wk A τ i)) < π j).card : ℕ) := by
      push_cast
      ring
    rw [h5, hc]

/-- The weight of worker `j`'s list in the pair computation. -/
noncomputable def Q2 (μ : Matching n m) (B : Finset (Fin n)) (τ : Equiv.Perm (Fin n))
    (x : Fin n → ℝ) (j : Fin m) (ρ : Equiv.Perm (Fin n)) : ℝ :=
  ∏ i : Fin n, if ((∀ k, μ k ≠ j) ∨
    ∃ k, μ k = j ∧ k ≠ i ∧ k ≠ τ i ∧ ρ i < ρ (phi B τ k)) then 1 - x i else 1

theorem prod_pow_threat2 (μ : Matching n m) (B : Finset (Fin n)) (τ : Equiv.Perm (Fin n))
    (x : Fin n → ℝ) (w : Fin m → Equiv.Perm (Fin n)) :
    ∏ i : Fin n, (1 - x i) ^ (threat2 μ B τ w i).card = ∏ j : Fin m, Q2 μ B τ x j (w j) := by
  unfold Q2
  rw [prod_comm]
  refine prod_congr rfl fun i _ => ?_
  rw [← prod_const, threat2, prod_filter]

/-- The worker-side condition, worker by worker. -/
def WOK (μ : Matching n m) (A B : Finset (Fin n)) (τ : Equiv.Perm (Fin n)) (j : Fin m)
    (ρ : Equiv.Perm (Fin n)) : Prop :=
  ∀ k, μ k = j → k ∈ A ∪ B → ρ (psi B τ k) < ρ (phi B τ k)

theorem workerOK_iff (μ : Matching n m) (A B : Finset (Fin n)) (τ : Equiv.Perm (Fin n))
    (w : Fin m → Equiv.Perm (Fin n)) :
    WorkerOK μ A B τ w ↔ ∀ j, WOK μ A B τ j (w j) := by
  constructor
  · intro h1 j k hk hkD
    subst hk
    exact h1 k hkD
  · intro h1 k hkD
    exact h1 (μ k) k rfl hkD

/-- The number of profiles in the sufficient event, as an integral of a product over workers. -/
theorem card_suff_eq {A B : Finset (Fin n)} {τ : Equiv.Perm (Fin n)} (h : Typed A B τ)
    (μ : Matching n m) :
    ((univ.filter fun p : Profile n m => Suff p μ A B τ).card : ℝ) =
      (m.factorial : ℝ) ^ n * ∫ x : Fin n → I,
        (∏ i, (x i : ℝ) ^ (if i ∈ A ∪ B then 1 else 0)) *
          ∏ j : Fin m, ∑ ρ : Equiv.Perm (Fin n),
            (if WOK μ A B τ j ρ then (1 : ℝ) else 0) * Q2 μ B τ (fun i => (x i : ℝ)) j ρ := by
  have hprod : ∀ w : Fin m → Equiv.Perm (Fin n),
      ∏ i : Fin n, ((univ.filter fun π : Equiv.Perm (Fin m) => FirmOK μ A B τ w i π).card : ℝ) =
        (m.factorial : ℝ) ^ n * ∫ x : Fin n → I,
          (∏ i, (x i : ℝ) ^ (if i ∈ A ∪ B then 1 else 0)) *
            ∏ j : Fin m, Q2 μ B τ (fun i => (x i : ℝ)) j (w j) := by
    intro w
    simp only [card_firmOK h, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
    congr 1
    rw [← integral_fintype_prod_volume_eq_prod (fun i (t : I) =>
      (t : ℝ) ^ (if i ∈ A ∪ B then 1 else 0) * (1 - (t : ℝ)) ^ (threat2 μ B τ w i).card)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ∏ i, ((x i : ℝ) ^ (if i ∈ A ∪ B then 1 else 0) *
      (1 - (x i : ℝ)) ^ (threat2 μ B τ w i).card) = _
    rw [prod_mul_distrib, prod_pow_threat2 μ B τ (fun i => (x i : ℝ)) w]
  have hcont : ∀ w : Fin m → Equiv.Perm (Fin n), Continuous fun x : Fin n → I =>
      (∏ i, (x i : ℝ) ^ (if i ∈ A ∪ B then 1 else 0)) *
        ∏ j : Fin m, Q2 μ B τ (fun i => (x i : ℝ)) j (w j) := by
    intro w
    have h6 : (fun x : Fin n → I => (∏ i, (x i : ℝ) ^ (if i ∈ A ∪ B then 1 else 0)) *
        ∏ j : Fin m, Q2 μ B τ (fun i => (x i : ℝ)) j (w j)) =
        fun x => (∏ i, (x i : ℝ) ^ (if i ∈ A ∪ B then 1 else 0)) *
          ∏ i : Fin n, (1 - (x i : ℝ)) ^ (threat2 μ B τ w i).card := by
      funext x
      rw [prod_pow_threat2 μ B τ (fun i => (x i : ℝ)) w]
    rw [h6]
    fun_prop
  rw [card_suff]
  push_cast
  have hterm : ∀ w : Fin m → Equiv.Perm (Fin n),
      (if WorkerOK μ A B τ w then (1 : ℝ) else 0) *
        ∏ i : Fin n, ((univ.filter fun π : Equiv.Perm (Fin m) => FirmOK μ A B τ w i π).card : ℝ) =
      (m.factorial : ℝ) ^ n * ∫ x : Fin n → I,
        (if WorkerOK μ A B τ w then (1 : ℝ) else 0) *
          ((∏ i, (x i : ℝ) ^ (if i ∈ A ∪ B then 1 else 0)) *
            ∏ j : Fin m, Q2 μ B τ (fun i => (x i : ℝ)) j (w j)) := by
    intro w
    rw [hprod w, integral_const_mul]
    ring
  simp only [hterm]
  rw [← mul_sum, ← integral_finsetSum]
  · congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ∑ w : Fin m → Equiv.Perm (Fin n), (if WorkerOK μ A B τ w then (1 : ℝ) else 0) *
        ((∏ i, (x i : ℝ) ^ (if i ∈ A ∪ B then 1 else 0)) *
          ∏ j : Fin m, Q2 μ B τ (fun i => (x i : ℝ)) j (w j)) =
      (∏ i, (x i : ℝ) ^ (if i ∈ A ∪ B then 1 else 0)) *
        ∏ j : Fin m, ∑ ρ : Equiv.Perm (Fin n),
          (if WOK μ A B τ j ρ then (1 : ℝ) else 0) * Q2 μ B τ (fun i => (x i : ℝ)) j ρ
    rw [Fintype.prod_sum, mul_sum]
    refine sum_congr rfl fun w _ => ?_
    rw [prod_mul_distrib, prod_boole]
    have h7 : (∀ j ∈ (univ : Finset (Fin m)), WOK μ A B τ j (w j)) ↔ WorkerOK μ A B τ w := by
      rw [workerOK_iff]
      simp
    by_cases hW : WorkerOK μ A B τ w
    · rw [if_pos hW, if_pos (h7.mpr hW)]
      ring
    · rw [if_neg hW, if_neg (fun h8 => hW (h7.mp h8))]
      ring
  · intro w _
    exact integrable_of_continuous (continuous_const.mul (hcont w))

end PairCount

end OMA

/-
# Part 12. Step B: the workers' sums for a typed pair, and the assembled integral
-/

namespace OMA

open StableMarriage.Unbalanced
open Finset
open Classical
open MeasureTheory unitInterval

section PairWorkers

variable {n m : ℕ}

/-- The sum of the weights of one worker's lists. -/
noncomputable def RR (μ : Matching n m) (A B : Finset (Fin n)) (τ : Equiv.Perm (Fin n))
    (c : Fin n → ℝ) (j : Fin m) : ℝ :=
  ∑ ρ : Equiv.Perm (Fin n), (if WOK μ A B τ j ρ then (1 : ℝ) else 0) * Q2 μ B τ c j ρ

theorem RR_unmatched (μ : Matching n m) (A B : Finset (Fin n)) (τ : Equiv.Perm (Fin n))
    (c : Fin n → ℝ) (j : Fin m) (hj : ∀ k, μ k ≠ j) :
    RR μ A B τ c j = (n.factorial : ℝ) * ∏ i, (1 - c i) := by
  have h1 : ∀ ρ : Equiv.Perm (Fin n),
      (if WOK μ A B τ j ρ then (1 : ℝ) else 0) * Q2 μ B τ c j ρ = ∏ i, (1 - c i) := by
    intro ρ
    have hW : WOK μ A B τ j ρ := fun k hk => absurd hk (hj k)
    rw [if_pos hW, one_mul]
    unfold Q2
    refine prod_congr rfl fun i _ => ?_
    rw [if_pos (Or.inl hj)]
  unfold RR
  simp only [h1, sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

theorem RR_out {A B : Finset (Fin n)} {τ : Equiv.Perm (Fin n)} (h : Typed A B τ)
    (μ : Matching n m) (c : Fin n → ℝ) (k : Fin n) (hk : k ∉ A ∪ B) :
    RR μ A B τ c (μ k) =
      (n.factorial : ℝ) * ∫ y : I, ∏ i ∈ univ.erase k, (1 - c i * (y : ℝ)) := by
  have hkA : k ∉ A := fun h1 => hk (mem_union_left B h1)
  have hkB : k ∉ B := fun h1 => hk (mem_union_right A h1)
  rw [← sum_perm_prod (univ.erase k) k (notMem_erase k univ) c]
  unfold RR
  refine sum_congr rfl fun ρ _ => ?_
  have hW : WOK μ A B τ (μ k) ρ := by
    intro k' hk' hk'D
    rw [μ.injective hk'] at hk'D
    exact absurd hk'D hk
  rw [if_pos hW, one_mul]
  unfold Q2
  rw [← mul_prod_erase univ _ (mem_univ k)]
  rw [if_neg (by
    rintro (h1 | ⟨k', hk', hk'k, _⟩)
    · exact h1 k rfl
    · exact hk'k (μ.injective hk')), one_mul]
  refine prod_congr rfl fun i hi => ?_
  have hik : i ≠ k := ne_of_mem_erase hi
  have hcond : ((∀ k', μ k' ≠ μ k) ∨
      ∃ k', μ k' = μ k ∧ k' ≠ i ∧ k' ≠ τ i ∧ ρ i < ρ (phi B τ k')) ↔ ρ i < ρ k := by
    constructor
    · rintro (h1 | ⟨k', hk', _, _, h2⟩)
      · exact absurd rfl (h1 k)
      · have h3 := μ.injective hk'
        subst h3
        simpa only [phi, if_neg hkB] using h2
    · intro h2
      refine Or.inr ⟨k, rfl, fun h3 => hik h3.symm, ?_, ?_⟩
      · intro h3
        have h4 : τ.symm k = i := by rw [h3, Equiv.symm_apply_apply]
        rw [h.symm_fix hkA hkB] at h4
        exact hik h4.symm
      · simpa only [phi, if_neg hkB] using h2
  by_cases h2 : ρ i < ρ k
  · rw [if_pos (hcond.mpr h2), if_pos h2]
  · rw [if_neg (fun h3 => h2 (hcond.mp h3)), if_neg h2]

theorem RR_in {A B : Finset (Fin n)} {τ : Equiv.Perm (Fin n)} (h : Typed A B τ)
    (μ : Matching n m) (c : Fin n → ℝ) (k : Fin n) (hk : k ∈ A ∪ B) :
    RR μ A B τ c (μ k) = (n.factorial : ℝ) * ∫ y : I, (y : ℝ) *
      ∏ i ∈ (univ.erase k).erase (τ.symm k), (1 - c i * (y : ℝ)) := by
  have hsk : τ.symm k ≠ k := h.symm_ne_of_mem hk
  have hphi : phi B τ k = k ∨ phi B τ k = τ.symm k := by
    unfold phi
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hpsi : psi B τ k = k ∨ psi B τ k = τ.symm k := by
    unfold psi
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hne : phi B τ k ≠ psi B τ k := by
    unfold phi psi
    split_ifs
    · exact hsk
    · exact fun h1 => hsk h1.symm
  have hnot : ∀ k₀ : Fin n, (k₀ = k ∨ k₀ = τ.symm k) →
      k₀ ∉ (univ.erase k).erase (τ.symm k) := by
    intro k₀ h1 h2
    rw [mem_erase, mem_erase] at h2
    rcases h1 with h3 | h3
    · exact h2.2.1 h3
    · exact h2.1 h3
  rw [← sum_perm_prod_two _ (phi B τ k) (psi B τ k) (hnot _ hphi) (hnot _ hpsi) hne c]
  unfold RR
  refine sum_congr rfl fun ρ _ => ?_
  have hW : WOK μ A B τ (μ k) ρ ↔ ρ (psi B τ k) < ρ (phi B τ k) := by
    constructor
    · intro h1
      exact h1 k rfl hk
    · intro h1 k' hk' _
      rw [μ.injective hk']
      exact h1
  have hQ : Q2 μ B τ c (μ k) ρ = ∏ i ∈ (univ.erase k).erase (τ.symm k),
      (if ρ i < ρ (phi B τ k) then 1 - c i else 1) := by
    unfold Q2
    rw [← prod_subset (subset_univ ((univ.erase k).erase (τ.symm k)))]
    · refine prod_congr rfl fun i hi => ?_
      rw [mem_erase, mem_erase] at hi
      have hcond : ((∀ k', μ k' ≠ μ k) ∨
          ∃ k', μ k' = μ k ∧ k' ≠ i ∧ k' ≠ τ i ∧ ρ i < ρ (phi B τ k')) ↔
          ρ i < ρ (phi B τ k) := by
        constructor
        · rintro (h1 | ⟨k', hk', _, _, h2⟩)
          · exact absurd rfl (h1 k)
          · rw [μ.injective hk'] at h2
            exact h2
        · intro h2
          refine Or.inr ⟨k, rfl, fun h3 => hi.2.1 h3.symm, ?_, h2⟩
          intro h3
          apply hi.1
          rw [h3, Equiv.symm_apply_apply]
      by_cases h2 : ρ i < ρ (phi B τ k)
      · rw [if_pos (hcond.mpr h2), if_pos h2]
      · rw [if_neg (fun h3 => h2 (hcond.mp h3)), if_neg h2]
    · intro i _ hi
      rw [if_neg]
      rintro (h1 | ⟨k', hk', hk'i, hk'τ, _⟩)
      · exact h1 k rfl
      · have h3 := μ.injective hk'
        subst h3
        apply hi
        rw [mem_erase, mem_erase]
        refine ⟨?_, fun h4 => hk'i h4.symm, mem_univ i⟩
        intro h4
        apply hk'τ
        rw [h4, Equiv.apply_symm_apply]
  rw [hQ]
  by_cases h1 : ρ (psi B τ k) < ρ (phi B τ k)
  · rw [if_pos (hW.mpr h1), if_pos h1]
  · rw [if_neg (fun h2 => h1 (hW.mp h2)), if_neg h1]

/-- The inner integral of a worker whose firm is moved, before the missing factor is added. -/
noncomputable def A2 (τ : Equiv.Perm (Fin n)) (x : Fin n → I) (k : Fin n) : ℝ :=
  ∫ y : I, (y : ℝ) * ∏ i ∈ (univ.erase k).erase (τ.symm k), (1 - (x i : ℝ) * (y : ℝ))

/-- The product over all workers. -/
theorem prod_RR {A B : Finset (Fin n)} {τ : Equiv.Perm (Fin n)} (h : Typed A B τ)
    (μ : Matching n m) (x : Fin n → I) :
    ∏ j : Fin m, RR μ A B τ (fun i => (x i : ℝ)) j =
      (n.factorial : ℝ) ^ m * ((∏ i, (1 - (x i : ℝ))) ^ (m - n) *
        ∏ k, (if k ∈ A ∪ B then A2 τ x k else OMA.A x k)) := by
  have hnm : n ≤ m := by
    simpa using Fintype.card_le_of_embedding μ
  set s : Finset (Fin m) := univ.map μ with hs
  have hsplit := prod_mul_prod_compl s (fun j : Fin m => RR μ A B τ (fun i => (x i : ℝ)) j)
  have h1 : ∏ j ∈ s, RR μ A B τ (fun i => (x i : ℝ)) j =
      (n.factorial : ℝ) ^ n * ∏ k, (if k ∈ A ∪ B then A2 τ x k else OMA.A x k) := by
    rw [hs, prod_map]
    have h2 : ∀ k : Fin n, RR μ A B τ (fun i => (x i : ℝ)) (μ k) =
        (n.factorial : ℝ) * (if k ∈ A ∪ B then A2 τ x k else OMA.A x k) := by
      intro k
      by_cases hk : k ∈ A ∪ B
      · rw [if_pos hk, RR_in h μ _ k hk]
        rfl
      · rw [if_neg hk, RR_out h μ _ k hk]
        rfl
    simp only [h2, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
  have h2 : ∏ j ∈ sᶜ, RR μ A B τ (fun i => (x i : ℝ)) j =
      ((n.factorial : ℝ) * ∏ i, (1 - (x i : ℝ))) ^ (m - n) := by
    have hc : sᶜ.card = m - n := by
      rw [card_compl, hs, card_map, card_univ, Fintype.card_fin, Fintype.card_fin]
    rw [← hc, ← prod_const]
    refine prod_congr rfl fun j hj => ?_
    refine RR_unmatched μ A B τ _ j fun k hk => ?_
    rw [mem_compl, hs, mem_map] at hj
    exact hj ⟨k, mem_univ k, hk⟩
  rw [← hsplit, h1, h2, mul_pow]
  have h3 : (n.factorial : ℝ) ^ m = (n.factorial : ℝ) ^ n * (n.factorial : ℝ) ^ (m - n) := by
    rw [← pow_add, Nat.add_sub_cancel' hnm]
  rw [h3]
  ring

/-- The number of profiles in the sufficient event, as an explicit integral. -/
theorem card_suff_integral {A B : Finset (Fin n)} {τ : Equiv.Perm (Fin n)} (h : Typed A B τ)
    (μ : Matching n m) :
    ((univ.filter fun p : Profile n m => Suff p μ A B τ).card : ℝ) =
      (m.factorial : ℝ) ^ n * (n.factorial : ℝ) ^ m * ∫ x : Fin n → I,
        (∏ i, (x i : ℝ) ^ (if i ∈ A ∪ B then 1 else 0)) *
          ((∏ i, (1 - (x i : ℝ))) ^ (m - n) *
            ∏ k, (if k ∈ A ∪ B then A2 τ x k else OMA.A x k)) := by
  rw [card_suff_eq h μ, mul_assoc]
  congr 1
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have h1 := prod_RR h μ x
  unfold RR at h1
  show (∏ i, (x i : ℝ) ^ (if i ∈ A ∪ B then 1 else 0)) *
      ∏ j : Fin m, ∑ ρ : Equiv.Perm (Fin n),
        (if WOK μ A B τ j ρ then (1 : ℝ) else 0) * Q2 μ B τ (fun i => (x i : ℝ)) j ρ = _
  rw [h1]
  ring

end PairWorkers

end OMA

/-
# Part 13. Step B: the lower bound `J` for a typed pair, workers' variables outside
-/

namespace OMA

open StableMarriage.Unbalanced
open Finset
open Classical
open MeasureTheory unitInterval

section PairSwap

variable {n m : ℕ}

/-- The pair integrand with exponents `e` (1 on moved firms, 0 elsewhere), firms outside. -/
noncomputable def KPe (n d : ℕ) (e : Fin n → ℕ) (x : Fin n → I) : ℝ :=
  (∏ i, (x i : ℝ) ^ e i) * ((∏ i, (1 - (x i : ℝ))) ^ d *
    ∏ k, ∫ y : I, (y : ℝ) ^ e k * ∏ i ∈ univ.erase k, (1 - (x i : ℝ) * (y : ℝ)))

/-- The firm-side integral with an extra power of the variable. -/
noncomputable def hh (d e' : ℕ) (y : Fin n → I) (i : Fin n) : ℝ :=
  ∫ t : I, (t : ℝ) ^ e' * (1 - (t : ℝ)) ^ d * ∏ k ∈ univ.erase i, (1 - (t : ℝ) * (y k : ℝ))

theorem integral_KPe_eq (n d : ℕ) (e : Fin n → ℕ) :
    ∫ x : Fin n → I, KPe n d e x =
      ∫ y : Fin n → I, (∏ k, (y k : ℝ) ^ e k) * ∏ i, hh d (e i) y i := by
  let F : (Fin n → I) → (Fin n → I) → ℝ := fun x y =>
    (∏ k, (y k : ℝ) ^ e k) * ∏ i, ((x i : ℝ) ^ e i * (1 - (x i : ℝ)) ^ d *
      ∏ k ∈ univ.erase i, (1 - (x i : ℝ) * (y k : ℝ)))
  have hKP : ∀ x : Fin n → I, KPe n d e x = ∫ y : Fin n → I, F x y := by
    intro x
    have h1 : ∀ y : Fin n → I, F x y = (∏ i, (x i : ℝ) ^ e i) *
        ((∏ i, (1 - (x i : ℝ))) ^ d * ∏ k, ((y k : ℝ) ^ e k *
          ∏ i ∈ univ.erase k, (1 - (x i : ℝ) * (y k : ℝ)))) := by
      intro y
      have hL : ∏ i, ((x i : ℝ) ^ e i * (1 - (x i : ℝ)) ^ d *
          ∏ k ∈ univ.erase i, (1 - (x i : ℝ) * (y k : ℝ))) =
          (∏ i, (x i : ℝ) ^ e i) * (∏ i, (1 - (x i : ℝ))) ^ d *
            ∏ i, ∏ k ∈ univ.erase i, (1 - (x i : ℝ) * (y k : ℝ)) := by
        rw [prod_mul_distrib, prod_mul_distrib, prod_pow]
      have hR : ∏ k, ((y k : ℝ) ^ e k * ∏ i ∈ univ.erase k, (1 - (x i : ℝ) * (y k : ℝ))) =
          (∏ k, (y k : ℝ) ^ e k) * ∏ k, ∏ i ∈ univ.erase k, (1 - (x i : ℝ) * (y k : ℝ)) :=
        prod_mul_distrib
      have h2 : ∏ i, ∏ k ∈ univ.erase i, (1 - (x i : ℝ) * (y k : ℝ)) =
          ∏ k, ∏ i ∈ univ.erase k, (1 - (x i : ℝ) * (y k : ℝ)) := by
        refine prod_comm' fun i k => ?_
        simp only [mem_univ, mem_erase, ne_eq, true_and, and_true]
        exact ⟨fun h1 h2 => h1 h2.symm, fun h1 h2 => h1 h2.symm⟩
      show (∏ k, (y k : ℝ) ^ e k) * ∏ i, ((x i : ℝ) ^ e i * (1 - (x i : ℝ)) ^ d *
        ∏ k ∈ univ.erase i, (1 - (x i : ℝ) * (y k : ℝ))) = _
      rw [hL, hR, h2]
      ring
    simp only [h1]
    rw [integral_const_mul, integral_const_mul, KPe]
    congr 2
    exact (integral_fintype_prod_volume_eq_prod
      (fun k (t : I) => (t : ℝ) ^ e k * ∏ i ∈ univ.erase k, (1 - (x i : ℝ) * (t : ℝ)))).symm
  have hint : Integrable (Function.uncurry F) (volume.prod volume) := by
    refine integrable_of_continuous ?_
    show Continuous fun z : (Fin n → I) × (Fin n → I) =>
      (∏ k, (z.2 k : ℝ) ^ e k) * ∏ i, ((z.1 i : ℝ) ^ e i * (1 - (z.1 i : ℝ)) ^ d *
        ∏ k ∈ univ.erase i, (1 - (z.1 i : ℝ) * (z.2 k : ℝ)))
    fun_prop
  simp only [hKP]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ∫ x : Fin n → I, (∏ k, (y k : ℝ) ^ e k) * ∏ i, ((x i : ℝ) ^ e i *
    (1 - (x i : ℝ)) ^ d * ∏ k ∈ univ.erase i, (1 - (x i : ℝ) * (y k : ℝ))) =
      (∏ k, (y k : ℝ) ^ e k) * ∏ i, hh d (e i) y i
  rw [integral_const_mul]
  congr 1
  exact integral_fintype_prod_volume_eq_prod
    (fun i (t : I) => (t : ℝ) ^ e i * (1 - (t : ℝ)) ^ d *
      ∏ k ∈ univ.erase i, (1 - (t : ℝ) * (y k : ℝ)))

/-- The lower bound for a typed pair: `D` is the set of moved firms. -/
noncomputable def JJ (n d : ℕ) (D : Finset (Fin n)) : ℝ :=
  ∫ y : Fin n → I, (∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0)) *
    ∏ i, hh d (if i ∈ D then 1 else 0) y i

theorem continuous_Q2 (μ : Matching n m) (B : Finset (Fin n)) (τ : Equiv.Perm (Fin n))
    (j : Fin m) (ρ : Equiv.Perm (Fin n)) :
    Continuous fun x : Fin n → I => Q2 μ B τ (fun i => (x i : ℝ)) j ρ := by
  unfold Q2
  refine continuous_finsetProd _ fun i _ => ?_
  by_cases hc : ((∀ k, μ k ≠ j) ∨ ∃ k, μ k = j ∧ k ≠ i ∧ k ≠ τ i ∧ ρ i < ρ (phi B τ k))
  · simp only [if_pos hc]
    fun_prop
  · simp only [if_neg hc]
    fun_prop

theorem prod_factor_nonneg (x : Fin n → I) (y : I) (S : Finset (Fin n)) :
    0 ≤ ∏ i ∈ S, (1 - (x i : ℝ) * (y : ℝ)) := by
  refine prod_nonneg fun i _ => ?_
  have h1 := mul_le_one₀ (x i).2.2 y.2.1 y.2.2
  linarith

/-- **Lemma B (lower bound for a typed pair).** -/
theorem card_suff_ge {A B : Finset (Fin n)} {τ : Equiv.Perm (Fin n)} (h : Typed A B τ)
    (μ : Matching n m) :
    (m.factorial : ℝ) ^ n * (n.factorial : ℝ) ^ m * JJ n (m - n) (A ∪ B) ≤
      ((univ.filter fun p : Profile n m => Suff p μ A B τ).card : ℝ) := by
  rw [card_suff_integral h μ, JJ, ← integral_KPe_eq]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hfact : ((n.factorial : ℝ) ^ m) ≠ 0 := by positivity
  have hEq : (fun x : Fin n → I => (∏ i, (x i : ℝ) ^ (if i ∈ A ∪ B then 1 else 0)) *
      ((∏ i, (1 - (x i : ℝ))) ^ (m - n) *
        ∏ k, (if k ∈ A ∪ B then A2 τ x k else OMA.A x k))) =
      fun x => ((n.factorial : ℝ) ^ m)⁻¹ *
        ((∏ i, (x i : ℝ) ^ (if i ∈ A ∪ B then 1 else 0)) *
          ∏ j : Fin m, RR μ A B τ (fun i => (x i : ℝ)) j) := by
    funext x
    rw [prod_RR h μ x]
    field_simp
  refine integral_mono_of_nonneg ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun x => ?_
    unfold KPe
    refine mul_nonneg (prod_nonneg fun i _ => pow_nonneg (x i).2.1 _)
      (mul_nonneg (pow_nonneg (prod_nonneg fun i _ => by have := (x i).2.2; linarith) _)
        (prod_nonneg fun k _ => integral_nonneg fun y =>
          mul_nonneg (pow_nonneg y.2.1 _) (prod_factor_nonneg x y _)))
  · rw [hEq]
    refine integrable_of_continuous (continuous_const.mul (Continuous.mul (by fun_prop) ?_))
    refine continuous_finsetProd _ fun j _ => ?_
    unfold RR
    exact continuous_finsetSum _ fun ρ _ => continuous_const.mul (continuous_Q2 μ B τ j ρ)
  · refine Filter.Eventually.of_forall fun x => ?_
    unfold KPe
    refine mul_le_mul_of_nonneg_left ?_ (prod_nonneg fun i _ => pow_nonneg (x i).2.1 _)
    refine mul_le_mul_of_nonneg_left ?_
      (pow_nonneg (prod_nonneg fun i _ => by have := (x i).2.2; linarith) _)
    refine prod_le_prod (fun k _ => integral_nonneg fun y =>
      mul_nonneg (pow_nonneg y.2.1 _) (prod_factor_nonneg x y _)) fun k _ => ?_
    by_cases hk : k ∈ A ∪ B
    · simp only [if_pos hk]
      unfold A2
      refine integral_mono (integrable_of_continuous (by fun_prop))
        (integrable_of_continuous (by fun_prop)) fun y => ?_
      show (y : ℝ) ^ 1 * ∏ i ∈ univ.erase k, (1 - (x i : ℝ) * (y : ℝ)) ≤
        (y : ℝ) * ∏ i ∈ (univ.erase k).erase (τ.symm k), (1 - (x i : ℝ) * (y : ℝ))
      rw [pow_one]
      refine mul_le_mul_of_nonneg_left ?_ y.2.1
      rw [← prod_sdiff (erase_subset (τ.symm k) (univ.erase k))]
      refine mul_le_of_le_one_left (prod_factor_nonneg x y _) ?_
      refine prod_le_one (fun i _ => ?_) (fun i _ => ?_)
      · have h1 := mul_le_one₀ (x i).2.2 y.2.1 y.2.2
        linarith
      · have h1 := mul_nonneg (x i).2.1 y.2.1
        linarith
    · simp only [if_neg hk]
      unfold OMA.A
      simp only [pow_zero, one_mul]
      exact le_rfl

end PairSwap

end OMA

/-
# Part 14. Step B: the second moment dominates the sum over typed pairs (Lemma B3)
-/

namespace OMA

open StableMarriage.Unbalanced
open Finset
open Classical
open MeasureTheory unitInterval

section SecondMoment

variable {n m : ℕ}

/-- The permutations that derange `C` and fix everything else. -/
noncomputable def Der (C : Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  univ.filter fun τ => (∀ i ∈ C, τ i ∈ C ∧ τ i ≠ i) ∧ ∀ i, i ∉ C → τ i = i

theorem typed_mul {A B : Finset (Fin n)} {τA τB : Equiv.Perm (Fin n)} (hd : Disjoint A B)
    (hA : τA ∈ Der A) (hB : τB ∈ Der B) : Typed A B (τA * τB) := by
  simp only [Der, mem_filter, mem_univ, true_and] at hA hB
  refine ⟨hd, ?_, ?_, ?_⟩
  · intro i hi
    have hiB : i ∉ B := Finset.disjoint_left.mp hd hi
    rw [Equiv.Perm.mul_apply, hB.2 i hiB]
    exact hA.1 i hi
  · intro i hi
    have h1 := hB.1 i hi
    have h2 : τB i ∉ A := Finset.disjoint_right.mp hd h1.1
    rw [Equiv.Perm.mul_apply, hA.2 _ h2]
    exact h1
  · intro i hiA hiB
    rw [Equiv.Perm.mul_apply, hB.2 i hiB, hA.2 i hiA]

theorem typeA_sub {A B A' B' : Finset (Fin n)} {τ : Equiv.Perm (Fin n)} {p : Profile n m}
    {μ : Matching n m} (T : Typed A B τ) (T' : Typed A' B' τ) (s : Suff p μ A B τ)
    (s' : Suff p μ A' B' τ) : A ⊆ A' := by
  intro i hi
  by_contra hi'
  have hne := (T.mapA i hi).2
  have hiB' : i ∈ B' := by
    by_contra hb
    exact hne (T'.fix i hi' hb)
  have f1 := (s.1 i).2 (mem_union_left B hi)
  simp only [bk, wk, if_pos hi] at f1
  have f2 := (s'.1 i).2 (mem_union_right A' hiB')
  simp only [bk, wk, if_neg hi'] at f2
  exact lt_asymm f1 f2

theorem typeB_sub {A B B' : Finset (Fin n)} {τ : Equiv.Perm (Fin n)} (T : Typed A B τ)
    (T' : Typed A B' τ) : B ⊆ B' := by
  intro i hi
  by_contra hi'
  have hne := (T.mapB i hi).2
  have hiA : i ∉ A := Finset.disjoint_right.mp T.disj hi
  exact hne (T'.fix i hiA hi')

/-- Two typed pairs with the same second matching and both sufficient events are equal. -/
theorem obj_inj {p : Profile n m} {μ : Matching n m} {A1 B1 A2 B2 : Finset (Fin n)}
    {a1 b1 a2 b2 : Equiv.Perm (Fin n)} (d1 : Disjoint A1 B1) (ha1 : a1 ∈ Der A1)
    (hb1 : b1 ∈ Der B1) (d2 : Disjoint A2 B2) (ha2 : a2 ∈ Der A2) (hb2 : b2 ∈ Der B2)
    (s1 : Suff p μ A1 B1 (a1 * b1)) (s2 : Suff p μ A2 B2 (a2 * b2))
    (heq : secondMatching μ (a1 * b1) = secondMatching μ (a2 * b2)) :
    A1 = A2 ∧ B1 = B2 ∧ a1 = a2 ∧ b1 = b2 := by
  have hτ : a1 * b1 = a2 * b2 := by
    refine Equiv.ext fun i => μ.injective ?_
    have h1 := DFunLike.congr_fun heq i
    rw [secondMatching_apply, secondMatching_apply] at h1
    exact h1
  have T1 := typed_mul d1 ha1 hb1
  have T2 := typed_mul d2 ha2 hb2
  rw [← hτ] at T2 s2
  have hA : A1 = A2 := Finset.Subset.antisymm (typeA_sub T1 T2 s1 s2) (typeA_sub T2 T1 s2 s1)
  subst hA
  have hB : B1 = B2 := Finset.Subset.antisymm (typeB_sub T1 T2) (typeB_sub T2 T1)
  subst hB
  simp only [Der, mem_filter, mem_univ, true_and] at ha1 hb1 ha2 hb2
  have hb : b1 = b2 := by
    refine Equiv.ext fun i => ?_
    by_cases hi : i ∈ B1
    · have h1 := DFunLike.congr_fun hτ i
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at h1
      have h2 : b1 i ∉ A1 := Finset.disjoint_right.mp d1 (hb1.1 i hi).1
      have h3 : b2 i ∉ A1 := Finset.disjoint_right.mp d1 (hb2.1 i hi).1
      rw [ha1.2 _ h2, ha2.2 _ h3] at h1
      exact h1
    · rw [hb1.2 i hi, hb2.2 i hi]
  subst hb
  refine ⟨rfl, rfl, ?_, rfl⟩
  exact mul_right_cancel hτ

/-- The index set of typed pairs. -/
abbrev Obj (n : ℕ) :=
  Finset (Fin n) × Finset (Fin n) × Equiv.Perm (Fin n) × Equiv.Perm (Fin n)

/-- Validity of an index. -/
def IsObj (o : Obj n) : Prop :=
  Disjoint o.1 o.2.1 ∧ o.2.2.1 ∈ Der o.1 ∧ o.2.2.2 ∈ Der o.2.1

/-- Per profile: the number of (matching, typed pair) with the sufficient event is at most the
square of the number of stable matchings. -/
theorem sum_suff_le_sq (p : Profile n m) :
    ∑ μ : Matching n m, ((univ : Finset (Obj n)).filter fun o =>
      IsObj o ∧ Suff p μ o.1 o.2.1 (o.2.2.1 * o.2.2.2)).card ≤ numStableMatchings p ^ 2 := by
  rw [numStableMatchings_eq, pow_two]
  have h1 : (univ.filter fun μ : Matching n m => IsStable p μ).card *
      (univ.filter fun μ : Matching n m => IsStable p μ).card =
      ∑ μ : Matching n m, if IsStable p μ then
        (univ.filter fun μ : Matching n m => IsStable p μ).card else 0 := by
    rw [← sum_filter, sum_const, smul_eq_mul]
  rw [h1]
  refine sum_le_sum fun μ _ => ?_
  by_cases hst : IsStable p μ
  · rw [if_pos hst]
    refine card_le_card_of_injOn (fun o => secondMatching μ (o.2.2.1 * o.2.2.2)) ?_ ?_
    · intro o ho
      rw [mem_coe, mem_filter] at ho
      rw [mem_coe, mem_filter]
      exact ⟨mem_univ _, (suff_stable (typed_mul ho.2.1.1 ho.2.1.2.1 ho.2.1.2.2) p μ ho.2.2).2⟩
    · intro o1 ho1 o2 ho2 heq
      rw [mem_coe, mem_filter] at ho1 ho2
      obtain ⟨A1, B1, a1, b1⟩ := o1
      obtain ⟨A2, B2, a2, b2⟩ := o2
      obtain ⟨hA, hB, ha, hb⟩ := obj_inj ho1.2.1.1 ho1.2.1.2.1 ho1.2.1.2.2 ho2.2.1.1
        ho2.2.1.2.1 ho2.2.1.2.2 ho1.2.2 ho2.2.2 heq
      exact Prod.ext hA (Prod.ext hB (Prod.ext ha hb))
  · rw [if_neg hst]
    rw [Nat.le_zero, card_eq_zero, filter_eq_empty_iff]
    intro o _ ho
    exact hst (suff_stable (typed_mul ho.1.1 ho.1.2.1 ho.1.2.2) p μ ho.2).1

/-- **Lemma B3.** The second moment is at least the number of matchings times the sum over typed
pairs of the lower bounds `J`. -/
theorem second_moment_ge (n m : ℕ) :
    (m.descFactorial n : ℝ) * ∑ A : Finset (Fin n), ∑ B : Finset (Fin n),
        (if Disjoint A B then ((Der A).card : ℝ) * ((Der B).card : ℝ) * JJ n (m - n) (A ∪ B)
          else 0) ≤
      secondMomentNumStableMatchings n m := by
  have hP : (0 : ℝ) < (Fintype.card (Profile n m) : ℝ) := by
    rw [card_profile]
    positivity
  have h1 : secondMomentNumStableMatchings n m =
      (Fintype.card (Profile n m) : ℝ)⁻¹ *
        ∑ p : Profile n m, (numStableMatchings p : ℝ) ^ 2 := by
    unfold secondMomentNumStableMatchings uniformProfile
    rw [PMF.integral_eq_sum, mul_sum]
    refine sum_congr rfl fun p _ => ?_
    simp [PMF.uniformOfFintype_apply]
  -- sum over profiles of the per-profile inequality, with the sums exchanged
  have h2 : ∑ μ : Matching n m, ∑ o : Obj n,
      (if IsObj o then ((univ.filter fun p : Profile n m =>
        Suff p μ o.1 o.2.1 (o.2.2.1 * o.2.2.2)).card : ℝ) else 0) ≤
      ∑ p : Profile n m, (numStableMatchings p : ℝ) ^ 2 := by
    have h3 : ∀ p : Profile n m, (∑ μ : Matching n m, ∑ o : Obj n,
        (if IsObj o ∧ Suff p μ o.1 o.2.1 (o.2.2.1 * o.2.2.2) then (1 : ℝ) else 0)) ≤
        (numStableMatchings p : ℝ) ^ 2 := by
      intro p
      have h4 := sum_suff_le_sq p
      have h5 : ((∑ μ : Matching n m, ((univ : Finset (Obj n)).filter fun o =>
          IsObj o ∧ Suff p μ o.1 o.2.1 (o.2.2.1 * o.2.2.2)).card : ℕ) : ℝ) ≤
          ((numStableMatchings p ^ 2 : ℕ) : ℝ) := by exact_mod_cast h4
      simp only [card_filter] at h5
      push_cast at h5
      exact h5
    have e1 : ∀ (μ : Matching n m) (o : Obj n),
        (if IsObj o then ((univ.filter fun p : Profile n m =>
          Suff p μ o.1 o.2.1 (o.2.2.1 * o.2.2.2)).card : ℝ) else 0) =
        ∑ p : Profile n m,
          (if IsObj o ∧ Suff p μ o.1 o.2.1 (o.2.2.1 * o.2.2.2) then (1 : ℝ) else 0) := by
      intro μ o
      by_cases ho : IsObj o
      · rw [if_pos ho, card_filter]
        push_cast
        refine sum_congr rfl fun p _ => ?_
        by_cases hs : Suff p μ o.1 o.2.1 (o.2.2.1 * o.2.2.2)
        · rw [if_pos hs, if_pos ⟨ho, hs⟩]
        · rw [if_neg hs, if_neg (fun h7 => hs h7.2)]
      · rw [if_neg ho]
        refine (sum_eq_zero fun p _ => ?_).symm
        rw [if_neg (fun h7 => ho h7.1)]
    have h7 : ∑ μ : Matching n m, ∑ o : Obj n,
        (if IsObj o then ((univ.filter fun p : Profile n m =>
          Suff p μ o.1 o.2.1 (o.2.2.1 * o.2.2.2)).card : ℝ) else 0) =
        ∑ p : Profile n m, ∑ μ : Matching n m, ∑ o : Obj n,
          (if IsObj o ∧ Suff p μ o.1 o.2.1 (o.2.2.1 * o.2.2.2) then (1 : ℝ) else 0) := by
      simp only [e1]
      exact (sum_congr rfl fun μ _ => sum_comm).trans sum_comm
    rw [h7]
    exact sum_le_sum fun p _ => h3 p
  -- lower bound each count
  have h8 : ∀ (μ : Matching n m) (o : Obj n),
      (if IsObj o then (m.factorial : ℝ) ^ n * (n.factorial : ℝ) ^ m *
        JJ n (m - n) (o.1 ∪ o.2.1) else 0) ≤
      (if IsObj o then ((univ.filter fun p : Profile n m =>
        Suff p μ o.1 o.2.1 (o.2.2.1 * o.2.2.2)).card : ℝ) else 0) := by
    intro μ o
    by_cases ho : IsObj o
    · rw [if_pos ho, if_pos ho]
      exact card_suff_ge (typed_mul ho.1 ho.2.1 ho.2.2) μ
    · rw [if_neg ho, if_neg ho]
  have h9 : ∑ μ : Matching n m, ∑ o : Obj n,
      (if IsObj o then (m.factorial : ℝ) ^ n * (n.factorial : ℝ) ^ m *
        JJ n (m - n) (o.1 ∪ o.2.1) else 0) ≤
      ∑ p : Profile n m, (numStableMatchings p : ℝ) ^ 2 :=
    le_trans (sum_le_sum fun μ _ => sum_le_sum fun o _ => h8 μ o) h2
  -- reorganise the sum over typed pairs
  have h10 : ∑ o : Obj n, (if IsObj o then (m.factorial : ℝ) ^ n * (n.factorial : ℝ) ^ m *
        JJ n (m - n) (o.1 ∪ o.2.1) else 0) =
      (m.factorial : ℝ) ^ n * (n.factorial : ℝ) ^ m * ∑ A : Finset (Fin n),
        ∑ B : Finset (Fin n), (if Disjoint A B then ((Der A).card : ℝ) * ((Der B).card : ℝ) *
          JJ n (m - n) (A ∪ B) else 0) := by
    rw [Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun A _ => ?_
    rw [Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun B _ => ?_
    rw [Fintype.sum_prod_type]
    by_cases hd : Disjoint A B
    · rw [if_pos hd]
      have h11 : ∀ a b : Equiv.Perm (Fin n),
          (if IsObj (A, B, a, b) then (m.factorial : ℝ) ^ n * (n.factorial : ℝ) ^ m *
            JJ n (m - n) (A ∪ B) else 0) =
          (if a ∈ Der A then (1 : ℝ) else 0) * ((if b ∈ Der B then (1 : ℝ) else 0) *
            ((m.factorial : ℝ) ^ n * (n.factorial : ℝ) ^ m * JJ n (m - n) (A ∪ B))) := by
        intro a b
        by_cases ha : a ∈ Der A
        · by_cases hb : b ∈ Der B
          · rw [if_pos (show IsObj (A, B, a, b) from ⟨hd, ha, hb⟩), if_pos ha, if_pos hb]
            ring
          · rw [if_neg (fun h12 : IsObj (A, B, a, b) => hb h12.2.2), if_pos ha, if_neg hb]
            ring
        · rw [if_neg (fun h12 : IsObj (A, B, a, b) => ha h12.2.1), if_neg ha]
          ring
      simp only [h11]
      simp only [← mul_sum, ← sum_mul, sum_boole]
      have h13 : (univ.filter fun a : Equiv.Perm (Fin n) => a ∈ Der A) = Der A := by
        ext a
        simp
      have h14 : (univ.filter fun b : Equiv.Perm (Fin n) => b ∈ Der B) = Der B := by
        ext b
        simp
      rw [h13, h14]
      ring
    · rw [if_neg hd, mul_zero]
      refine sum_eq_zero fun a _ => sum_eq_zero fun b _ => ?_
      rw [if_neg (fun h12 : IsObj (A, B, a, b) => hd h12.1)]
  simp only [h10, sum_const, card_univ, nsmul_eq_mul] at h9
  rw [h1, Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin] at *
  rw [card_profile] at hP ⊢
  push_cast at hP ⊢
  rw [inv_mul_eq_div, le_div_iff₀ hP]
  linarith

end SecondMoment

end OMA

/-
# Part 15. Step D1: one-dimensional integrals and the pointwise lower bound
-/

namespace OMA

open StableMarriage.Unbalanced
open Finset
open Classical
open MeasureTheory unitInterval

section Eints

/-- The integral of `t ^ j * exp (-(l t))` over the unit interval. -/
noncomputable def Eint (j : ℕ) (l : ℝ) : ℝ :=
  ∫ t : I, (t : ℝ) ^ j * Real.exp (-(l * (t : ℝ)))

theorem Eint_nonneg (j : ℕ) (l : ℝ) : 0 ≤ Eint j l :=
  integral_nonneg fun t => mul_nonneg (pow_nonneg t.2.1 _) (Real.exp_pos _).le

theorem Eint_le_one (j : ℕ) {l : ℝ} (hl : 0 ≤ l) : Eint j l ≤ 1 := by
  unfold Eint
  have h : ∫ _t : I, (1 : ℝ) = 1 := by simp
  rw [← h]
  refine integral_mono (integrable_of_continuous (by fun_prop))
    (integrable_of_continuous (by fun_prop)) fun t => ?_
  show (t : ℝ) ^ j * Real.exp (-(l * (t : ℝ))) ≤ 1
  have h1 : (t : ℝ) ^ j ≤ 1 := pow_le_one₀ t.2.1 t.2.2
  have h2 : Real.exp (-(l * (t : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have h3 := mul_nonneg hl t.2.1
    linarith
  calc (t : ℝ) ^ j * Real.exp (-(l * (t : ℝ))) ≤ 1 * 1 :=
        mul_le_mul h1 h2 (Real.exp_pos _).le zero_le_one
    _ = 1 := one_mul 1

/-- Integration by parts. -/
theorem Eint_succ (j : ℕ) (l : ℝ) :
    ((j : ℝ) + 1) * Eint j l - l * Eint (j + 1) l = Real.exp (-l) := by
  unfold Eint
  rw [integral_I (fun t => t ^ j * Real.exp (-(l * t))),
    integral_I (fun t => t ^ (j + 1) * Real.exp (-(l * t)))]
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => t ^ (j + 1) * Real.exp (-(l * t)))
        (((j : ℝ) + 1) * (t ^ j * Real.exp (-(l * t))) -
          l * (t ^ (j + 1) * Real.exp (-(l * t)))) t := by
    intro t _
    have h0 : HasDerivAt (fun t : ℝ => -t * l) (-l) t := by
      simpa using (hasDerivAt_id t).neg.mul_const l
    have hfun : (fun t : ℝ => -(l * t)) = fun t : ℝ => -t * l := by
      funext s
      ring
    have h1 : HasDerivAt (fun t : ℝ => -(l * t)) (-l) t := by
      rw [hfun]
      exact h0
    have h2 := (hasDerivAt_pow (j + 1) t).mul h1.exp
    refine h2.congr_deriv ?_
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hF
  rw [hF]
  simp

theorem Eint_zero {l : ℝ} (hl : 0 < l) : Eint 0 l = (1 - Real.exp (-l)) / l := by
  unfold Eint
  simp only [pow_zero, one_mul]
  exact integral_I_exp_neg l hl

theorem Eint_zero_le {l : ℝ} (hl : 0 < l) : Eint 0 l ≤ 1 / l := by
  rw [Eint_zero hl, div_le_div_iff_of_pos_right hl]
  have h := Real.exp_pos (-l)
  linarith

theorem Eint_succ_le (j : ℕ) {l : ℝ} (hl : 0 < l) :
    Eint (j + 1) l ≤ ((j : ℝ) + 1) / l * Eint j l := by
  have h := Eint_succ j l
  have he := Real.exp_pos (-l)
  rw [div_mul_eq_mul_div, le_div_iff₀ hl]
  linarith

theorem Eint_one {l : ℝ} (hl : 0 < l) :
    Eint 1 l = (1 - (1 + l) * Real.exp (-l)) / l ^ 2 := by
  have h := Eint_succ 0 l
  rw [Eint_zero hl] at h
  simp only [Nat.cast_zero, zero_add, one_mul] at h
  field_simp
  field_simp at h
  linarith

theorem Eint_one_le {l : ℝ} (hl : 0 < l) : Eint 1 l ≤ 1 / l ^ 2 := by
  have h1 := Eint_succ_le 0 hl
  have h2 := Eint_zero_le hl
  simp only [Nat.cast_zero, zero_add] at h1
  calc Eint 1 l ≤ 1 / l * Eint 0 l := h1
    _ ≤ 1 / l * (1 / l) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 1 / l ^ 2 := by ring

/-- Two extra powers of `t` cost at most `6 / l ^ 2`. -/
theorem Eint_add_two_le (e : ℕ) (he : e ≤ 1) {l : ℝ} (hl : 0 < l) :
    Eint (e + 2) l ≤ 6 / l ^ 2 * Eint e l := by
  have h1 := Eint_succ_le (e + 1) hl
  have h2 := Eint_succ_le e hl
  have h0 := Eint_nonneg e l
  have hE : (e : ℝ) ≤ 1 := by exact_mod_cast he
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  push_cast at h1
  have h3 : ((e : ℝ) + 1 + 1) / l * Eint (e + 1) l ≤
      ((e : ℝ) + 1 + 1) / l * (((e : ℝ) + 1) / l * Eint e l) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : ((e : ℝ) + 1 + 1) / l * (((e : ℝ) + 1) / l * Eint e l) =
      (((e : ℝ) + 1 + 1) * ((e : ℝ) + 1)) / l ^ 2 * Eint e l := by
    field_simp
  have h5 : (((e : ℝ) + 1 + 1) * ((e : ℝ) + 1)) / l ^ 2 * Eint e l ≤ 6 / l ^ 2 * Eint e l := by
    refine mul_le_mul_of_nonneg_right ?_ h0
    rw [div_le_div_iff_of_pos_right (by positivity)]
    nlinarith
  linarith

end Eints

section Pointwise

variable {n : ℕ}

/-- The sum of the squares of the workers' variables. -/
noncomputable def qq (y : Fin n → I) : ℝ := ∑ k, (y k : ℝ) ^ 2

theorem qq_nonneg (y : Fin n → I) : 0 ≤ qq y := sum_nonneg fun k _ => by positivity

theorem one_sub_sum_le_prod {ι : Type*} (s : Finset ι) (u : ι → ℝ) (h0 : ∀ k ∈ s, 0 ≤ u k)
    (h1 : ∀ k ∈ s, u k ≤ 1) : 1 - ∑ k ∈ s, u k ≤ ∏ k ∈ s, (1 - u k) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [sum_insert hk, prod_insert hk]
    have ih' := ih (fun j hj => h0 j (mem_insert_of_mem hj))
      (fun j hj => h1 j (mem_insert_of_mem hj))
    have hk0 := h0 k (mem_insert_self k s)
    have hk1 := h1 k (mem_insert_self k s)
    have hs0 : 0 ≤ ∑ j ∈ s, u j := sum_nonneg fun j hj => h0 j (mem_insert_of_mem hj)
    nlinarith [mul_le_mul_of_nonneg_left ih' (by linarith : (0 : ℝ) ≤ 1 - u k),
      mul_nonneg hk0 hs0]

theorem exp_mul_one_sub_sq_le {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1) :
    Real.exp (-z) * (1 - z ^ 2) ≤ 1 - z := by
  have h2 : Real.exp (-z) * (1 + z) ≤ 1 := by
    have h3 := Real.add_one_le_exp z
    have h4 : Real.exp (-z) * Real.exp z = 1 := by rw [← Real.exp_add]; simp
    have h5 := Real.exp_pos (-z)
    nlinarith
  have h6 : Real.exp (-z) * (1 - z ^ 2) = Real.exp (-z) * (1 + z) * (1 - z) := by ring
  rw [h6]
  exact mul_le_of_le_one_left (by linarith) h2

/-- The pointwise bound behind Step D1. -/
theorem prod_lower (y : Fin n → I) (i : Fin n) (t : I) :
    Real.exp (-(aa y * (t : ℝ))) * (1 - (t : ℝ) ^ 2 * (1 + qq y)) ≤
      (1 - (t : ℝ)) * ∏ k ∈ univ.erase i, (1 - (t : ℝ) * (y k : ℝ)) := by
  have ht0 := t.2.1
  have ht1 := t.2.2
  have hz0 : ∀ k : Fin n, 0 ≤ (t : ℝ) * (y k : ℝ) := fun k => mul_nonneg ht0 (y k).2.1
  have hz1 : ∀ k : Fin n, (t : ℝ) * (y k : ℝ) ≤ 1 := fun k => mul_le_one₀ ht1 (y k).2.1 (y k).2.2
  have hf0 : ∀ k : Fin n, 0 ≤ 1 - (t : ℝ) * (y k : ℝ) := fun k => by have := hz1 k; linarith
  -- drop the factor of index `i`
  have h1 : ∏ k, (1 - (t : ℝ) * (y k : ℝ)) ≤ ∏ k ∈ univ.erase i, (1 - (t : ℝ) * (y k : ℝ)) := by
    rw [← mul_prod_erase univ _ (mem_univ i)]
    exact mul_le_of_le_one_left (prod_nonneg fun k _ => hf0 k) (by have := hz0 i; linarith)
  -- each factor from below
  have h2 : ∏ k, (Real.exp (-((t : ℝ) * (y k : ℝ))) * (1 - ((t : ℝ) * (y k : ℝ)) ^ 2)) ≤
      ∏ k, (1 - (t : ℝ) * (y k : ℝ)) := by
    refine prod_le_prod (fun k _ => ?_) (fun k _ => exp_mul_one_sub_sq_le (hz0 k) (hz1 k))
    refine mul_nonneg (Real.exp_pos _).le ?_
    have h3 : ((t : ℝ) * (y k : ℝ)) ^ 2 ≤ 1 := pow_le_one₀ (hz0 k) (hz1 k)
    linarith
  rw [prod_mul_distrib, ← Real.exp_sum] at h2
  have h3 : 1 - ∑ k, ((t : ℝ) * (y k : ℝ)) ^ 2 ≤ ∏ k, (1 - ((t : ℝ) * (y k : ℝ)) ^ 2) :=
    one_sub_sum_le_prod univ _ (fun k _ => by positivity)
      (fun k _ => pow_le_one₀ (hz0 k) (hz1 k))
  have h4 : ∑ k, ((t : ℝ) * (y k : ℝ)) ^ 2 = (t : ℝ) ^ 2 * qq y := by
    unfold qq
    rw [mul_sum]
    exact sum_congr rfl fun k _ => by ring
  have h5 := exp_mul_one_sub_sq_le ht0 ht1
  have hP0 : 0 ≤ ∏ k, (1 - ((t : ℝ) * (y k : ℝ)) ^ 2) := prod_nonneg fun k _ => by
    have h6 : ((t : ℝ) * (y k : ℝ)) ^ 2 ≤ 1 := pow_le_one₀ (hz0 k) (hz1 k)
    linarith
  have hS0 : 0 ≤ ∑ k, ((t : ℝ) * (y k : ℝ)) ^ 2 := sum_nonneg fun k _ => by positivity
  have ht2 : (t : ℝ) ^ 2 ≤ 1 := pow_le_one₀ ht0 ht1
  -- (1 - t^2) * prod >= 1 - t^2 - t^2 q
  have h7 : 1 - (t : ℝ) ^ 2 * (1 + qq y) ≤
      (1 - (t : ℝ) ^ 2) * ∏ k, (1 - ((t : ℝ) * (y k : ℝ)) ^ 2) := by
    rw [show (t : ℝ) ^ 2 * (1 + qq y) = (t : ℝ) ^ 2 + ∑ k, ((t : ℝ) * (y k : ℝ)) ^ 2 by
      rw [h4]
      ring]
    nlinarith [mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ 1 - (t : ℝ) ^ 2),
      mul_nonneg (by positivity : (0 : ℝ) ≤ (t : ℝ) ^ 2) hS0]
  have hexp : Real.exp (-(aa y * (t : ℝ))) =
      Real.exp (-(t : ℝ)) * Real.exp (∑ k, -((t : ℝ) * (y k : ℝ))) := by
    rw [← Real.exp_add, sum_neg_distrib, ← mul_sum]
    congr 1
    unfold aa
    ring
  have he0 : 0 < Real.exp (-(t : ℝ)) * Real.exp (∑ k, -((t : ℝ) * (y k : ℝ))) := by positivity
  calc Real.exp (-(aa y * (t : ℝ))) * (1 - (t : ℝ) ^ 2 * (1 + qq y))
      ≤ Real.exp (-(aa y * (t : ℝ))) *
          ((1 - (t : ℝ) ^ 2) * ∏ k, (1 - ((t : ℝ) * (y k : ℝ)) ^ 2)) := by
        rw [hexp]
        exact mul_le_mul_of_nonneg_left h7 he0.le
    _ = (Real.exp (-(t : ℝ)) * (1 - (t : ℝ) ^ 2)) *
          (Real.exp (∑ k, -((t : ℝ) * (y k : ℝ))) *
            ∏ k, (1 - ((t : ℝ) * (y k : ℝ)) ^ 2)) := by
        rw [hexp]
        ring
    _ ≤ (1 - (t : ℝ)) * ∏ k, (1 - (t : ℝ) * (y k : ℝ)) := by
        refine mul_le_mul h5 h2 ?_ (by linarith)
        exact mul_nonneg (Real.exp_pos _).le hP0
    _ ≤ (1 - (t : ℝ)) * ∏ k ∈ univ.erase i, (1 - (t : ℝ) * (y k : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)

/-- **Step D1**, integral form. -/
theorem hh_lower (y : Fin n → I) (i : Fin n) (e' : ℕ) :
    Eint e' (aa y) - (1 + qq y) * Eint (e' + 2) (aa y) ≤ hh 1 e' y i := by
  have h1 : Eint e' (aa y) - (1 + qq y) * Eint (e' + 2) (aa y) =
      ∫ t : I, (t : ℝ) ^ e' * (Real.exp (-(aa y * (t : ℝ))) *
        (1 - (t : ℝ) ^ 2 * (1 + qq y))) := by
    unfold Eint
    rw [← integral_const_mul, ← integral_sub (integrable_of_continuous (by fun_prop))
      (integrable_of_continuous (by fun_prop))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show (t : ℝ) ^ e' * Real.exp (-(aa y * (t : ℝ))) -
      (1 + qq y) * ((t : ℝ) ^ (e' + 2) * Real.exp (-(aa y * (t : ℝ)))) = _
    ring
  rw [h1]
  unfold hh
  refine integral_mono (integrable_of_continuous (by fun_prop))
    (integrable_of_continuous (by fun_prop)) fun t => ?_
  show (t : ℝ) ^ e' * (Real.exp (-(aa y * (t : ℝ))) * (1 - (t : ℝ) ^ 2 * (1 + qq y))) ≤
    (t : ℝ) ^ e' * (1 - (t : ℝ)) ^ 1 * ∏ k ∈ univ.erase i, (1 - (t : ℝ) * (y k : ℝ))
  rw [pow_one, mul_assoc]
  exact mul_le_mul_of_nonneg_left (prod_lower y i t) (pow_nonneg t.2.1 _)

/-- The relative error of Step D1. -/
noncomputable def eps (y : Fin n → I) : ℝ :=
  (1 + aa y) * Real.exp (-aa y) + 6 * (1 + qq y) / aa y ^ 2

/-- **Step D1.** -/
theorem hh_ge (y : Fin n → I) (i : Fin n) (e' : ℕ) (he : e' ≤ 1) :
    (1 - eps y) / aa y ^ (1 + e') ≤ hh 1 e' y i := by
  have ha : 0 < aa y := lt_of_lt_of_le one_pos (one_le_aa y)
  have hq := qq_nonneg y
  have hexp := Real.exp_pos (-aa y)
  refine le_trans ?_ (hh_lower y i e')
  have h2 := Eint_add_two_le e' he ha
  have h3 : (1 + qq y) * Eint (e' + 2) (aa y) ≤ (1 + qq y) * (6 / aa y ^ 2 * Eint e' (aa y)) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  interval_cases e'
  · have h4 := Eint_zero_le ha
    have h5 : (1 + qq y) * (6 / aa y ^ 2 * Eint 0 (aa y)) ≤
        (1 + qq y) * (6 / aa y ^ 2 * (1 / aa y)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 (by positivity)) (by linarith)
    have h6 : (1 - eps y) / aa y ^ (1 + 0) =
        (1 - Real.exp (-aa y)) / aa y - aa y * Real.exp (-aa y) / aa y -
          (1 + qq y) * (6 / aa y ^ 2 * (1 / aa y)) := by
      unfold eps
      field_simp
      ring
    have h7 : 0 ≤ aa y * Real.exp (-aa y) / aa y := by positivity
    rw [h6, Eint_zero ha]
    linarith
  · have h4 := Eint_one_le ha
    have h5 : (1 + qq y) * (6 / aa y ^ 2 * Eint 1 (aa y)) ≤
        (1 + qq y) * (6 / aa y ^ 2 * (1 / aa y ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 (by positivity)) (by linarith)
    have h6 : (1 - eps y) / aa y ^ (1 + 1) =
        (1 - (1 + aa y) * Real.exp (-aa y)) / aa y ^ 2 -
          (1 + qq y) * (6 / aa y ^ 2 * (1 / aa y ^ 2)) := by
      unfold eps
      field_simp
      ring
    rw [h6, Eint_one ha]
    linarith

end Pointwise

end OMA

/-
# Part 16. Step D2: the tangent-line bound and its integrated form
-/

namespace OMA

open StableMarriage.Unbalanced
open Finset
open Classical
open MeasureTheory unitInterval

section D2

variable {n : ℕ}

theorem aa_pos (y : Fin n → I) : 0 < aa y := lt_of_lt_of_le one_pos (one_le_aa y)

theorem continuous_aa : Continuous fun y : Fin n → I => aa y := by
  unfold aa
  fun_prop

theorem continuous_qq : Continuous fun y : Fin n → I => qq y := by
  unfold qq
  fun_prop

theorem continuous_eps : Continuous fun y : Fin n → I => eps y := by
  unfold eps
  refine Continuous.add (Continuous.mul (continuous_const.add continuous_aa)
    (Real.continuous_exp.comp continuous_aa.neg)) ?_
  exact Continuous.div (continuous_const.mul (continuous_const.add continuous_qq))
    (continuous_aa.pow 2) fun y => (pow_pos (aa_pos y) 2).ne'

theorem eps_nonneg (y : Fin n → I) : 0 ≤ eps y := by
  unfold eps
  have h1 := aa_pos y
  have h2 := qq_nonneg y
  positivity

theorem hh_nonneg (d e' : ℕ) (y : Fin n → I) (i : Fin n) : 0 ≤ hh d e' y i := by
  unfold hh
  refine integral_nonneg fun t => ?_
  have ht1 := t.2.2
  refine mul_nonneg (mul_nonneg (pow_nonneg t.2.1 _) (pow_nonneg (by linarith) _))
    (prod_nonneg fun k _ => ?_)
  have h1 := mul_le_one₀ ht1 (y k).2.1 (y k).2.2
  linarith

theorem exp_neg_two_mul_le {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1 / 2) :
    Real.exp (-(2 * z)) ≤ 1 - z := by
  have h2 := Real.add_one_le_exp (2 * z)
  have h3 : Real.exp (-(2 * z)) * Real.exp (2 * z) = 1 := by
    rw [← Real.exp_add]
    simp
  by_contra hc
  rw [not_le] at hc
  have h5 : (1 - z) * Real.exp (2 * z) < Real.exp (-(2 * z)) * Real.exp (2 * z) :=
    mul_lt_mul_of_pos_right hc (Real.exp_pos _)
  have h6 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 1 - z)
  nlinarith

theorem sum_indicator (D : Finset (Fin n)) :
    ∑ i : Fin n, (1 + (if i ∈ D then 1 else 0)) = n + D.card := by
  rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one,
    sum_boole]
  simp [Finset.filter_mem_eq_inter]

/-- **Step D2.** -/
theorem prod_hh_ge (y : Fin n → I) (D : Finset (Fin n)) (K : ℝ) (hK : 0 ≤ K) :
    Real.exp (-K) * ((1 + K) - (2 * n + 2 + 2 * K) * eps y) / aa y ^ (n + D.card) ≤
      ∏ i, hh 1 (if i ∈ D then 1 else 0) y i := by
  have ha := aa_pos y
  have he := eps_nonneg y
  have haN : 0 < aa y ^ (n + D.card) := pow_pos ha _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases le_or_gt (eps y) (1 / 2) with hcase | hcase
  · have h1 : ∏ i : Fin n, ((1 - eps y) / aa y ^ (1 + (if i ∈ D then 1 else 0))) ≤
        ∏ i, hh 1 (if i ∈ D then 1 else 0) y i := by
      refine prod_le_prod (fun i _ => div_nonneg (by linarith) (pow_nonneg ha.le _))
        (fun i _ => ?_)
      refine hh_ge y i _ ?_
      split_ifs <;> omega
    have h2 : ∏ i : Fin n, ((1 - eps y) / aa y ^ (1 + (if i ∈ D then 1 else 0))) =
        (1 - eps y) ^ n / aa y ^ (n + D.card) := by
      rw [prod_div_distrib, prod_const, card_univ, Fintype.card_fin, prod_pow_eq_pow_sum,
        sum_indicator]
    have h3 : Real.exp (-(2 * eps y)) ^ n ≤ (1 - eps y) ^ n :=
      pow_le_pow_left₀ (Real.exp_pos _).le (exp_neg_two_mul_le he hcase) n
    rw [← Real.exp_nat_mul] at h3
    have h4 : Real.exp (-K) * ((1 + K) - (2 * n + 2 + 2 * K) * eps y) ≤
        Real.exp ((n : ℝ) * -(2 * eps y)) := by
      have h5 := Real.add_one_le_exp (K - 2 * n * eps y)
      have h6 : Real.exp ((n : ℝ) * -(2 * eps y)) =
          Real.exp (-K) * Real.exp (K - 2 * n * eps y) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [h6]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 + 2 * K) he]
    rw [h2] at h1
    refine le_trans ?_ h1
    rw [div_le_div_iff_of_pos_right haN]
    linarith
  · have h1 : Real.exp (-K) * ((1 + K) - (2 * n + 2 + 2 * K) * eps y) ≤ 0 := by
      refine mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le ?_
      nlinarith
    exact le_trans (div_nonpos_of_nonpos_of_nonneg h1 haN.le)
      (prod_nonneg fun i _ => hh_nonneg _ _ y i)

/-- The main term on the cube. -/
noncomputable def TT (n : ℕ) (D : Finset (Fin n)) : ℝ :=
  ∫ y : Fin n → I, (∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0)) / aa y ^ (n + D.card)

/-- The correction term on the cube. -/
noncomputable def RRr (n : ℕ) (D : Finset (Fin n)) : ℝ :=
  ∫ y : Fin n → I, (∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0)) * eps y / aa y ^ (n + D.card)

/-- The integrand of `JJ` is integrable (it is an integral over the firms' variables). -/
theorem integrable_JJ (d : ℕ) (e : Fin n → ℕ) :
    Integrable (fun y : Fin n → I => (∏ k, (y k : ℝ) ^ e k) * ∏ i, hh d (e i) y i) volume := by
  let F : (Fin n → I) × (Fin n → I) → ℝ := fun z =>
    (∏ k, (z.2 k : ℝ) ^ e k) * ∏ i, ((z.1 i : ℝ) ^ e i * (1 - (z.1 i : ℝ)) ^ d *
      ∏ k ∈ univ.erase i, (1 - (z.1 i : ℝ) * (z.2 k : ℝ)))
  have hint : Integrable F (volume.prod volume) := by
    refine integrable_of_continuous ?_
    show Continuous fun z : (Fin n → I) × (Fin n → I) =>
      (∏ k, (z.2 k : ℝ) ^ e k) * ∏ i, ((z.1 i : ℝ) ^ e i * (1 - (z.1 i : ℝ)) ^ d *
        ∏ k ∈ univ.erase i, (1 - (z.1 i : ℝ) * (z.2 k : ℝ)))
    fun_prop
  have h1 := hint.integral_prod_right
  refine h1.congr (Filter.Eventually.of_forall fun y => ?_)
  show ∫ x : Fin n → I, (∏ k, (y k : ℝ) ^ e k) * ∏ i, ((x i : ℝ) ^ e i *
    (1 - (x i : ℝ)) ^ d * ∏ k ∈ univ.erase i, (1 - (x i : ℝ) * (y k : ℝ))) =
      (∏ k, (y k : ℝ) ^ e k) * ∏ i, hh d (e i) y i
  rw [integral_const_mul]
  congr 1
  exact integral_fintype_prod_volume_eq_prod
    (fun i (t : I) => (t : ℝ) ^ e i * (1 - (t : ℝ)) ^ d *
      ∏ k ∈ univ.erase i, (1 - (t : ℝ) * (y k : ℝ)))

/-- **Step D2, integrated.** -/
theorem JJ_ge (D : Finset (Fin n)) (K : ℝ) (hK : 0 ≤ K) :
    Real.exp (-K) * ((1 + K) * TT n D - (2 * n + 2 + 2 * K) * RRr n D) ≤ JJ n 1 D := by
  have hcP : Continuous fun y : Fin n → I => ∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0) := by
    fun_prop
  have hcT : Continuous fun y : Fin n → I =>
      (∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0)) / aa y ^ (n + D.card) :=
    Continuous.div hcP (continuous_aa.pow _) fun y => (pow_pos (aa_pos y) _).ne'
  have hcR : Continuous fun y : Fin n → I =>
      (∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0)) * eps y / aa y ^ (n + D.card) :=
    Continuous.div (hcP.mul continuous_eps) (continuous_aa.pow _)
      fun y => (pow_pos (aa_pos y) _).ne'
  have h1 : Real.exp (-K) * ((1 + K) * TT n D - (2 * n + 2 + 2 * K) * RRr n D) =
      ∫ y : Fin n → I, (∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0)) *
        (Real.exp (-K) * ((1 + K) - (2 * n + 2 + 2 * K) * eps y) / aa y ^ (n + D.card)) := by
    unfold TT RRr
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub
      ((integrable_of_continuous hcT).const_mul _) ((integrable_of_continuous hcR).const_mul _),
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have ha := (pow_pos (aa_pos y) (n + D.card)).ne'
    show Real.exp (-K) * ((1 + K) * ((∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0)) /
        aa y ^ (n + D.card)) - (2 * n + 2 + 2 * K) *
        ((∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0)) * eps y / aa y ^ (n + D.card))) = _
    field_simp
  rw [h1]
  unfold JJ
  refine integral_mono ?_ (integrable_JJ 1 _) fun y => ?_
  · refine integrable_of_continuous (hcP.mul ?_)
    refine Continuous.div ?_ (continuous_aa.pow _) fun y => (pow_pos (aa_pos y) _).ne'
    exact continuous_const.mul (continuous_const.sub (continuous_const.mul continuous_eps))
  · exact mul_le_mul_of_nonneg_left (prod_hh_ge y D K hK)
      (prod_nonneg fun k _ => pow_nonneg (y k).2.1 _)

end D2

end OMA

/-
# Part 17. The main term as a one-dimensional integral, and the weight `ww`
-/

namespace OMA

open StableMarriage.Unbalanced
open Finset
open Classical
open MeasureTheory unitInterval

section Wfun

variable {n : ℕ}

/-- The one-dimensional weight: `TT n D = (1 / (n + k - 1)!) ∫ ww`. -/
noncomputable def ww (n : ℕ) (D : Finset (Fin n)) (l : ℝ) : ℝ :=
  l ^ (n + D.card - 1) * Real.exp (-l) * ∏ j : Fin n, Eint (if j ∈ D then 1 else 0) l

theorem ww_nonneg (D : Finset (Fin n)) {l : ℝ} (hl : 0 ≤ l) : 0 ≤ ww n D l :=
  mul_nonneg (mul_nonneg (pow_nonneg hl _) (Real.exp_pos _).le)
    (prod_nonneg fun j _ => Eint_nonneg _ _)

theorem TT_eq (hn : 1 ≤ n) (D : Finset (Fin n)) :
    TT n D = 1 / ((n + D.card - 1).factorial : ℝ) * ∫ l in Set.Ioi (0 : ℝ), ww n D l := by
  have h := laplace (n := n) (n + D.card) (by omega) 0 le_rfl
    (fun j t => (t : ℝ) ^ (if j ∈ D then 1 else 0)) (fun j => by fun_prop)
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one, add_zero] at h
  unfold TT
  rw [h]
  rfl

theorem Eint_le_inv_pow (e : ℕ) (he : e ≤ 1) {l : ℝ} (hl : 0 < l) :
    Eint e l ≤ 1 / l ^ (1 + e) := by
  interval_cases e
  · simpa using Eint_zero_le hl
  · simpa using Eint_one_le hl

theorem prod_Eint_le (D : Finset (Fin n)) {l : ℝ} (hl : 0 < l) :
    ∏ j : Fin n, Eint (if j ∈ D then 1 else 0) l ≤ 1 / l ^ (n + D.card) := by
  have h1 : ∏ j : Fin n, Eint (if j ∈ D then 1 else 0) l ≤
      ∏ j : Fin n, (1 / l ^ (1 + (if j ∈ D then 1 else 0))) := by
    refine prod_le_prod (fun j _ => Eint_nonneg _ _) (fun j _ => Eint_le_inv_pow _ ?_ hl)
    split_ifs <;> omega
  have h2 : ∏ j : Fin n, (1 / l ^ (1 + (if j ∈ D then 1 else 0))) = 1 / l ^ (n + D.card) := by
    rw [prod_div_distrib, prod_const_one, prod_pow_eq_pow_sum, sum_indicator]
  rw [h2] at h1
  exact h1

theorem ww_le_inv (hn : 1 ≤ n) (D : Finset (Fin n)) {l : ℝ} (hl : 0 < l) :
    ww n D l ≤ Real.exp (-l) / l := by
  unfold ww
  have h1 := prod_Eint_le D hl
  have h2 : l ^ (n + D.card - 1) * Real.exp (-l) * (1 / l ^ (n + D.card)) =
      Real.exp (-l) / l := by
    obtain ⟨N, hN⟩ : ∃ N, n + D.card = N + 1 := ⟨n + D.card - 1, by omega⟩
    rw [hN, Nat.add_sub_cancel, pow_succ]
    field_simp
  rw [← h2]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

theorem ww_le_pow (D : Finset (Fin n)) {l : ℝ} (hl : 0 ≤ l) :
    ww n D l ≤ l ^ (n + D.card - 1) * Real.exp (-l) := by
  unfold ww
  refine mul_le_of_le_one_right (by positivity) ?_
  exact prod_le_one (fun j _ => Eint_nonneg _ _) (fun j _ => Eint_le_one _ hl)

theorem aa_le (y : Fin n → I) : aa y ≤ n + 1 := by
  unfold aa
  have h1 : ∑ k, (y k : ℝ) ≤ ∑ _k : Fin n, (1 : ℝ) := sum_le_sum fun k _ => (y k).2.2
  simp at h1
  linarith

theorem TT_pos (D : Finset (Fin n)) : 0 < TT n D := by
  have h1 : ∫ y : Fin n → I, (∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0)) /
      ((n : ℝ) + 1) ^ (n + D.card) ≤ TT n D := by
    unfold TT
    refine integral_mono (integrable_of_continuous (by fun_prop))
      (integrable_of_continuous (Continuous.div (by fun_prop) (continuous_aa.pow _)
        fun y => (pow_pos (aa_pos y) _).ne')) fun y => ?_
    exact div_le_div_of_nonneg_left (prod_nonneg fun k _ => pow_nonneg (y k).2.1 _)
      (pow_pos (aa_pos y) _) (pow_le_pow_left₀ (aa_pos y).le (aa_le y) _)
  have h2 : ∫ y : Fin n → I, (∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0)) /
      ((n : ℝ) + 1) ^ (n + D.card) =
      (∏ k : Fin n, (1 / (((if k ∈ D then 1 else 0 : ℕ) : ℝ) + 1))) /
        ((n : ℝ) + 1) ^ (n + D.card) := by
    rw [integral_div, integral_fintype_prod_volume_eq_prod
      (fun k (t : I) => (t : ℝ) ^ (if k ∈ D then 1 else 0))]
    simp only [integral_I_pow]
  rw [h2] at h1
  exact lt_of_lt_of_le (div_pos (prod_pos fun k _ => by positivity) (by positivity)) h1

theorem integrableOn_ww (hn : 1 ≤ n) (D : Finset (Fin n)) :
    IntegrableOn (ww n D) (Set.Ioi 0) := by
  refine Integrable.of_integral_ne_zero ?_
  have h := TT_eq hn D
  have hp := TT_pos D
  intro h0
  rw [h0, mul_zero] at h
  linarith

theorem integral_ww_pos (hn : 1 ≤ n) (D : Finset (Fin n)) :
    0 < ∫ l in Set.Ioi (0 : ℝ), ww n D l := by
  have h := TT_eq hn D
  have hp := TT_pos D
  rw [h] at hp
  have hf : (0 : ℝ) < 1 / ((n + D.card - 1).factorial : ℝ) := by positivity
  exact (mul_pos_iff_of_pos_left hf).mp hp

end Wfun

end OMA

/-
# Part 18. Steps D4 and D5: the correction term
-/

namespace OMA

open StableMarriage.Unbalanced
open Finset
open Classical
open MeasureTheory unitInterval

section Correction

variable {n : ℕ}

theorem one_add_mul_exp_neg_le {a : ℝ} (ha : 0 < a) : (1 + a) * Real.exp (-a) ≤ 16 / a ^ 2 := by
  have h1 := Real.add_one_le_exp (a / 4)
  have h2 : (a / 4 + 1) ^ 4 ≤ Real.exp (a / 4) ^ 4 := pow_le_pow_left₀ (by positivity) h1 4
  rw [← Real.exp_nat_mul] at h2
  have h3 : ((4 : ℕ) : ℝ) * (a / 4) = a := by
    push_cast
    ring
  rw [h3] at h2
  have h4 : a ^ 2 * (1 + a) / 16 ≤ (a / 4 + 1) ^ 4 := by nlinarith [sq_nonneg a, pow_pos ha 3, pow_pos ha 4]
  have h5 : Real.exp (-a) * Real.exp a = 1 := by
    rw [← Real.exp_add]
    simp
  have he := Real.exp_pos (-a)
  rw [le_div_iff₀ (by positivity)]
  have h6 : a ^ 2 * (1 + a) ≤ 16 * Real.exp a := by linarith
  calc (1 + a) * Real.exp (-a) * a ^ 2 = Real.exp (-a) * (a ^ 2 * (1 + a)) := by ring
    _ ≤ Real.exp (-a) * (16 * Real.exp a) := mul_le_mul_of_nonneg_left h6 he.le
    _ = 16 := by rw [mul_comm 16, ← mul_assoc, h5, one_mul]

theorem eps_le (y : Fin n → I) : eps y ≤ (22 + 6 * qq y) / aa y ^ 2 := by
  have ha := aa_pos y
  have h1 := one_add_mul_exp_neg_le ha
  unfold eps
  have h2 : (22 + 6 * qq y) / aa y ^ 2 = 16 / aa y ^ 2 + 6 * (1 + qq y) / aa y ^ 2 := by
    field_simp
    ring
  rw [h2]
  linarith

theorem integrableOn_id_mul_exp :
    IntegrableOn (fun l : ℝ => l * Real.exp (-(l / 2))) (Set.Ioi 0) := by
  have h := integral_pow_mul_exp_Ioi 1 (show (0 : ℝ) < 1 / 2 by norm_num)
  have hfun : (fun l : ℝ => l * Real.exp (-(l / 2))) =
      fun l : ℝ => l ^ 1 * Real.exp (-(1 / 2 * l)) := by
    funext l
    rw [pow_one]
    congr 2
    ring
  rw [hfun]
  refine Integrable.of_integral_ne_zero ?_
  rw [h]
  norm_num

theorem integral_id_mul_exp : ∫ l in Set.Ioi (0 : ℝ), l * Real.exp (-(l / 2)) = 4 := by
  have h := integral_pow_mul_exp_Ioi 1 (show (0 : ℝ) < 1 / 2 by norm_num)
  have hfun : (fun l : ℝ => l * Real.exp (-(l / 2))) =
      fun l : ℝ => l ^ 1 * Real.exp (-(1 / 2 * l)) := by
    funext l
    rw [pow_one]
    congr 2
    ring
  rw [hfun, h]
  norm_num

/-- **Step D4a.** The integral of `l ^ 2 * ww`. -/
theorem integral_sq_ww_le (hn : 1 ≤ n) (D : Finset (Fin n)) (Λ : ℝ) (hΛ : 0 < Λ) :
    ∫ l in Set.Ioi (0 : ℝ), l ^ 2 * ww n D l ≤
      Λ ^ 2 * (∫ l in Set.Ioi (0 : ℝ), ww n D l) + 4 * Real.exp (-(Λ / 2)) := by
  have hrhs : ∫ l in Set.Ioi (0 : ℝ), (Λ ^ 2 * ww n D l +
      Real.exp (-(Λ / 2)) * (l * Real.exp (-(l / 2)))) =
      Λ ^ 2 * (∫ l in Set.Ioi (0 : ℝ), ww n D l) + 4 * Real.exp (-(Λ / 2)) := by
    rw [integral_add ((integrableOn_ww hn D).const_mul _) (integrableOn_id_mul_exp.const_mul _),
      integral_const_mul, integral_const_mul, integral_id_mul_exp]
    ring
  rw [← hrhs]
  refine integral_mono_of_nonneg ?_ ?_ ?_
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun l hl => ?_
    exact mul_nonneg (by positivity) (ww_nonneg D (le_of_lt hl))
  · exact ((integrableOn_ww hn D).const_mul _).add (integrableOn_id_mul_exp.const_mul _)
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun l hl => ?_
    have hl0 : (0 : ℝ) < l := hl
    have hw := ww_nonneg D hl0.le
    show l ^ 2 * ww n D l ≤ Λ ^ 2 * ww n D l + Real.exp (-(Λ / 2)) * (l * Real.exp (-(l / 2)))
    rcases le_or_gt l Λ with hcase | hcase
    · have h1 : l ^ 2 * ww n D l ≤ Λ ^ 2 * ww n D l :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hl0.le hcase 2) hw
      have h2 : 0 ≤ Real.exp (-(Λ / 2)) * (l * Real.exp (-(l / 2))) := by positivity
      linarith
    · have h1 := ww_le_inv hn D hl0
      have h2 : l ^ 2 * ww n D l ≤ l ^ 2 * (Real.exp (-l) / l) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h3 : l ^ 2 * (Real.exp (-l) / l) = l * Real.exp (-l) := by
        field_simp
      have h4 : Real.exp (-l) = Real.exp (-(l / 2)) * Real.exp (-(l / 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have h5 : Real.exp (-(l / 2)) ≤ Real.exp (-(Λ / 2)) := by
        rw [Real.exp_le_exp]
        linarith
      have h6 : l * Real.exp (-l) ≤ Real.exp (-(Λ / 2)) * (l * Real.exp (-(l / 2))) := by
        rw [h4]
        have h7 : 0 ≤ l * Real.exp (-(l / 2)) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h5 h7]
      have h8 : 0 ≤ Λ ^ 2 * ww n D l := by positivity
      linarith

/-- The cube integral with two extra powers of `a`, as an integral of `l ^ 2 * ww`. -/
theorem integral_div_add_two (hn : 1 ≤ n) (D : Finset (Fin n)) :
    ∫ y : Fin n → I, (∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0)) / aa y ^ (n + D.card + 2) =
      1 / ((n + D.card + 1).factorial : ℝ) * ∫ l in Set.Ioi (0 : ℝ), l ^ 2 * ww n D l := by
  have h := laplace (n := n) (n + D.card + 2) (by omega) 0 le_rfl
    (fun j t => (t : ℝ) ^ (if j ∈ D then 1 else 0)) (fun j => by fun_prop)
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one, add_zero] at h
  rw [h, show n + D.card + 2 - 1 = n + D.card + 1 by omega]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun l _ => ?_
  show l ^ (n + D.card + 1) * Real.exp (-l) * ∏ j : Fin n, Eint (if j ∈ D then 1 else 0) l =
    l ^ 2 * (l ^ (n + D.card - 1) * Real.exp (-l) *
      ∏ j : Fin n, Eint (if j ∈ D then 1 else 0) l)
  have h1 : l ^ (n + D.card + 1) = l ^ 2 * l ^ (n + D.card - 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [h1]
  ring

/-- **Step D4b.** One extra square `y j0 ^ 2` costs a factor 6. -/
theorem integral_sq_div_le (hn : 1 ≤ n) (D : Finset (Fin n)) (j0 : Fin n) :
    ∫ y : Fin n → I, (∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0)) * (y j0 : ℝ) ^ 2 /
        aa y ^ (n + D.card + 2) ≤
      1 / ((n + D.card + 1).factorial : ℝ) * (6 * ∫ l in Set.Ioi (0 : ℝ), ww n D l) := by
  have h := laplace (n := n) (n + D.card + 2) (by omega) 0 le_rfl
    (fun j t => (t : ℝ) ^ ((if j ∈ D then 1 else 0) + (if j = j0 then 2 else 0)))
    (fun j => by fun_prop)
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one, add_zero] at h
  have hprod : ∀ y : Fin n → I,
      ∏ j, (y j : ℝ) ^ ((if j ∈ D then 1 else 0) + (if j = j0 then 2 else 0)) =
      (∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0)) * (y j0 : ℝ) ^ 2 := by
    intro y
    simp only [pow_add, prod_mul_distrib]
    congr 1
    rw [prod_eq_single j0]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h1
      exact absurd (mem_univ j0) h1
  simp only [hprod] at h
  rw [h, show n + D.card + 2 - 1 = n + D.card + 1 by omega]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg ?_ ((integrableOn_ww hn D).const_mul _) ?_
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun l hl => ?_
    have hl0 : (0 : ℝ) < l := hl
    exact mul_nonneg (by positivity) (prod_nonneg fun j _ =>
      integral_nonneg fun t => mul_nonneg (pow_nonneg t.2.1 _) (Real.exp_pos _).le)
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun l hl => ?_
    have hl0 : (0 : ℝ) < l := hl
    show l ^ (n + D.card + 1) * Real.exp (-l) *
        ∏ j : Fin n, Eint ((if j ∈ D then 1 else 0) + (if j = j0 then 2 else 0)) l ≤
      6 * (l ^ (n + D.card - 1) * Real.exp (-l) *
        ∏ j : Fin n, Eint (if j ∈ D then 1 else 0) l)
    have h1 : ∏ j : Fin n, Eint ((if j ∈ D then 1 else 0) + (if j = j0 then 2 else 0)) l ≤
        6 / l ^ 2 * ∏ j : Fin n, Eint (if j ∈ D then 1 else 0) l := by
      rw [← mul_prod_erase univ _ (mem_univ j0), ← mul_prod_erase univ
        (fun j : Fin n => Eint (if j ∈ D then 1 else 0) l) (mem_univ j0), ← mul_assoc]
      have h2 : ∏ j ∈ univ.erase j0,
          Eint ((if j ∈ D then 1 else 0) + (if j = j0 then 2 else 0)) l =
          ∏ j ∈ univ.erase j0, Eint (if j ∈ D then 1 else 0) l := by
        refine prod_congr rfl fun j hj => ?_
        rw [if_neg (ne_of_mem_erase hj), add_zero]
      rw [h2, if_pos rfl]
      refine mul_le_mul_of_nonneg_right ?_ (prod_nonneg fun j _ => Eint_nonneg _ _)
      refine Eint_add_two_le _ ?_ hl0
      split_ifs <;> omega
    have h3 : l ^ (n + D.card + 1) = l ^ 2 * l ^ (n + D.card - 1) := by
      rw [← pow_add]
      congr 1
      omega
    have h4 : 0 ≤ l ^ (n + D.card + 1) * Real.exp (-l) := by positivity
    calc l ^ (n + D.card + 1) * Real.exp (-l) *
          ∏ j : Fin n, Eint ((if j ∈ D then 1 else 0) + (if j = j0 then 2 else 0)) l
        ≤ l ^ (n + D.card + 1) * Real.exp (-l) *
          (6 / l ^ 2 * ∏ j : Fin n, Eint (if j ∈ D then 1 else 0) l) :=
          mul_le_mul_of_nonneg_left h1 h4
      _ = 6 * (l ^ (n + D.card - 1) * Real.exp (-l) *
          ∏ j : Fin n, Eint (if j ∈ D then 1 else 0) l) := by
          rw [h3]
          field_simp

/-- **Steps D4 and D5.** The correction term against the main integral. -/
theorem RRr_le (hn : 1 ≤ n) (D : Finset (Fin n)) (Λ : ℝ) (hΛ : 0 < Λ) :
    RRr n D ≤ 1 / ((n + D.card + 1).factorial : ℝ) *
      ((22 * Λ ^ 2 + 36 * n) * (∫ l in Set.Ioi (0 : ℝ), ww n D l) +
        88 * Real.exp (-(Λ / 2))) := by
  have hcP : Continuous fun y : Fin n → I => ∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0) := by
    fun_prop
  have hc0 : Continuous fun y : Fin n → I =>
      (∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0)) / aa y ^ (n + D.card + 2) :=
    Continuous.div hcP (continuous_aa.pow _) fun y => (pow_pos (aa_pos y) _).ne'
  have hcj : ∀ j0 : Fin n, Continuous fun y : Fin n → I =>
      (∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0)) * (y j0 : ℝ) ^ 2 /
        aa y ^ (n + D.card + 2) := fun j0 =>
    Continuous.div (hcP.mul (by fun_prop)) (continuous_aa.pow _)
      fun y => (pow_pos (aa_pos y) _).ne'
  have h1 : RRr n D ≤ ∫ y : Fin n → I,
      (22 * ((∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0)) / aa y ^ (n + D.card + 2)) +
        ∑ j0 : Fin n, 6 * ((∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0)) * (y j0 : ℝ) ^ 2 /
          aa y ^ (n + D.card + 2))) := by
    unfold RRr
    refine integral_mono ?_ ?_ fun y => ?_
    · exact integrable_of_continuous (Continuous.div (hcP.mul continuous_eps)
        (continuous_aa.pow _) fun y => (pow_pos (aa_pos y) _).ne')
    · exact integrable_of_continuous ((hc0.const_mul 22).add
        (continuous_finsetSum _ fun j0 _ => (hcj j0).const_mul 6))
    · have ha := aa_pos y
      have hP : 0 ≤ ∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0) :=
        prod_nonneg fun k _ => pow_nonneg (y k).2.1 _
      have he := eps_le y
      show (∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0)) * eps y / aa y ^ (n + D.card) ≤
        22 * ((∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0)) / aa y ^ (n + D.card + 2)) +
          ∑ j0 : Fin n, 6 * ((∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0)) * (y j0 : ℝ) ^ 2 /
            aa y ^ (n + D.card + 2))
      have h2 : ∑ j0 : Fin n, 6 * ((∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0)) *
          (y j0 : ℝ) ^ 2 / aa y ^ (n + D.card + 2)) =
          6 * ((∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0)) * qq y /
            aa y ^ (n + D.card + 2)) := by
        unfold qq
        rw [mul_sum, sum_div, mul_sum]
      rw [h2]
      have h3 : 22 * ((∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0)) / aa y ^ (n + D.card + 2)) +
          6 * ((∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0)) * qq y /
            aa y ^ (n + D.card + 2)) =
          (∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0)) * ((22 + 6 * qq y) / aa y ^ 2) /
            aa y ^ (n + D.card) := by
        rw [pow_add]
        field_simp
      rw [h3]
      refine div_le_div_of_nonneg_right ?_ (pow_pos ha _).le
      exact mul_le_mul_of_nonneg_left he hP
  rw [integral_add ((integrable_of_continuous hc0).const_mul _)
    (integrable_finsetSum _ fun j0 _ => (integrable_of_continuous (hcj j0)).const_mul _),
    integral_const_mul, integral_finsetSum _
      (fun j0 _ => (integrable_of_continuous (hcj j0)).const_mul _)] at h1
  have h4 : ∑ j0 : Fin n, ∫ y : Fin n → I,
      6 * ((∏ k, (y k : ℝ) ^ (if k ∈ D then 1 else 0)) * (y j0 : ℝ) ^ 2 /
        aa y ^ (n + D.card + 2)) ≤
      ∑ _j0 : Fin n, 6 * (1 / ((n + D.card + 1).factorial : ℝ) *
        (6 * ∫ l in Set.Ioi (0 : ℝ), ww n D l)) := by
    refine sum_le_sum fun j0 _ => ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_sq_div_le hn D j0) (by norm_num)
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h4
  have h5 := integral_sq_ww_le hn D Λ hΛ
  rw [integral_div_add_two hn D] at h1
  have hf : (0 : ℝ) ≤ 1 / ((n + D.card + 1).factorial : ℝ) := by positivity
  have h6 : 22 * (1 / ((n + D.card + 1).factorial : ℝ) *
      ∫ l in Set.Ioi (0 : ℝ), l ^ 2 * ww n D l) ≤
      22 * (1 / ((n + D.card + 1).factorial : ℝ) *
        (Λ ^ 2 * (∫ l in Set.Ioi (0 : ℝ), ww n D l) + 4 * Real.exp (-(Λ / 2)))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 hf) (by norm_num)
  have h7 : 22 * (1 / ((n + D.card + 1).factorial : ℝ) *
        (Λ ^ 2 * (∫ l in Set.Ioi (0 : ℝ), ww n D l) + 4 * Real.exp (-(Λ / 2)))) +
      (n : ℝ) * (6 * (1 / ((n + D.card + 1).factorial : ℝ) *
        (6 * ∫ l in Set.Ioi (0 : ℝ), ww n D l))) =
      1 / ((n + D.card + 1).factorial : ℝ) *
        ((22 * Λ ^ 2 + 36 * n) * (∫ l in Set.Ioi (0 : ℝ), ww n D l) +
          88 * Real.exp (-(Λ / 2))) := by ring
  linarith

end Correction

end OMA

/-
# Part 19. Steps D3, D6 and D7: the window bound and the lower bound for `JJ`
-/

namespace OMA

open StableMarriage.Unbalanced
open Finset
open Classical
open MeasureTheory unitInterval

section Window

variable {n : ℕ}

theorem one_add_mul_exp_neg_anti {L l : ℝ} (hL : 0 ≤ L) (hl : L ≤ l) :
    (1 + l) * Real.exp (-l) ≤ (1 + L) * Real.exp (-L) := by
  have h1 := Real.add_one_le_exp (l - L)
  have h2 : Real.exp (-L) = Real.exp (l - L) * Real.exp (-l) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h2, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  nlinarith [mul_nonneg hL (sub_nonneg.mpr hl)]

theorem exp_three_le : Real.exp 3 ≤ 21 := by
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_pos 1
  have h3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    norm_num
  rw [h3]
  have h4 : Real.exp 1 * Real.exp 1 ≤ 7.4 := by nlinarith
  nlinarith

/-- **Step D3.** The window `[L, L + 1]` carries mass at least `1 / (100 n L)`. -/
theorem integral_ww_ge (hn : 2 ≤ n) (D : Finset (Fin n)) (L : ℝ) (hL1 : 1 ≤ L)
    (hLn : Real.exp (-L) = 1 / n) (hL2 : 1 + L ≤ n / 2)
    (hk : (D.card : ℝ) * (1 + L) ≤ n / 2) :
    1 / (100 * n * L) ≤ ∫ l in Set.Ioi (0 : ℝ), ww n D l := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  set c0 : ℝ := 1 - 1 / n with hc0
  set c1 : ℝ := 1 - (1 + L) / n with hc1
  have hc0_le : c0 ≤ 1 := by
    rw [hc0]
    have : (0 : ℝ) ≤ 1 / n := by positivity
    linarith
  have hc0_nonneg : 0 ≤ c0 := by
    rw [hc0, sub_nonneg, div_le_one hn0]
    linarith
  have hc1_half : 1 / 2 ≤ c1 := by
    rw [hc1]
    have h1 : (1 + L) / n ≤ 1 / 2 := by
      rw [div_le_iff₀ hn0]
      linarith
    linarith
  have hc1_nonneg : 0 ≤ c1 := by linarith
  have hc1_le : c1 ≤ 1 := by
    rw [hc1]
    have : (0 : ℝ) ≤ (1 + L) / n := by positivity
    linarith
  -- the product of the constants
  have hprodc : Real.exp (-2) / 2 ≤ ∏ j : Fin n, (if j ∈ D then c1 else c0) := by
    rw [prod_ite, prod_const, prod_const]
    have hcardD : (univ.filter fun j : Fin n => j ∈ D).card = D.card := by
      congr 1
      ext j
      simp
    rw [hcardD]
    have h1 : 1 / 2 ≤ c1 ^ D.card := by
      have h2 := one_add_mul_le_pow (show (-2 : ℝ) ≤ -((1 + L) / n) by
        have : (1 + L) / n ≤ 1 / 2 := by
          rw [div_le_iff₀ hn0]
          linarith
        linarith) D.card
      have h3 : 1 + (D.card : ℝ) * -((1 + L) / n) ≥ 1 / 2 := by
        have h4 : (D.card : ℝ) * ((1 + L) / n) ≤ 1 / 2 := by
          rw [← mul_div_assoc, div_le_iff₀ hn0]
          linarith
        linarith
      have h5 : (1 + -((1 + L) / n)) = c1 := by
        rw [hc1]
        ring
      rw [h5] at h2
      linarith
    have h6 : Real.exp (-2) ≤ c0 ^ (univ.filter fun j : Fin n => ¬ j ∈ D).card := by
      have h7 : Real.exp (-(2 * (1 / (n : ℝ)))) ≤ c0 := by
        refine exp_neg_two_mul_le (by positivity) ?_
        rw [div_le_div_iff₀ hn0 (by norm_num)]
        linarith
      have h8 : Real.exp (-(2 * (1 / (n : ℝ)))) ^ n ≤ c0 ^ n :=
        pow_le_pow_left₀ (Real.exp_pos _).le h7 n
      rw [← Real.exp_nat_mul] at h8
      have h9 : (n : ℝ) * -(2 * (1 / (n : ℝ))) = -2 := by
        field_simp
      rw [h9] at h8
      have h10 : c0 ^ n ≤ c0 ^ (univ.filter fun j : Fin n => ¬ j ∈ D).card := by
        refine pow_le_pow_of_le_one hc0_nonneg hc0_le ?_
        calc (univ.filter fun j : Fin n => ¬ j ∈ D).card ≤ (univ : Finset (Fin n)).card :=
              card_le_card (filter_subset _ _)
          _ = n := by simp
      linarith
    have h11 : (0 : ℝ) ≤ Real.exp (-2) := (Real.exp_pos _).le
    calc Real.exp (-2) / 2 = 1 / 2 * Real.exp (-2) := by ring
      _ ≤ c1 ^ D.card * c0 ^ (univ.filter fun j : Fin n => ¬ j ∈ D).card :=
          mul_le_mul h1 h6 h11 (pow_nonneg hc1_nonneg _)
  -- pointwise lower bound on the window
  have hpt : ∀ l ∈ Set.Icc L (L + 1), Real.exp (-3) / (2 * n * (L + 1)) ≤ ww n D l := by
    intro l hl
    have hlL : L ≤ l := hl.1
    have hl0 : 0 < l := by linarith
    have hexp : Real.exp (-l) ≤ 1 / n := by
      rw [← hLn, Real.exp_le_exp]
      linarith
    have hE : ∀ j : Fin n, (if j ∈ D then c1 else c0) / l ^ (1 + (if j ∈ D then 1 else 0)) ≤
        Eint (if j ∈ D then 1 else 0) l := by
      intro j
      by_cases hj : j ∈ D
      · simp only [if_pos hj]
        rw [Eint_one hl0, show (1 + 1 : ℕ) = 2 by norm_num,
          div_le_div_iff_of_pos_right (by positivity)]
        have h1 := one_add_mul_exp_neg_anti hL0.le hlL
        rw [hLn] at h1
        rw [hc1]
        have h2 : (1 + L) * (1 / (n : ℝ)) = (1 + L) / n := by ring
        linarith
      · simp only [if_neg hj]
        rw [Eint_zero hl0, add_zero, pow_one, div_le_div_iff_of_pos_right hl0, hc0]
        linarith
    have hprod : (∏ j : Fin n, (if j ∈ D then c1 else c0)) / l ^ (n + D.card) ≤
        ∏ j : Fin n, Eint (if j ∈ D then 1 else 0) l := by
      have h1 : ∏ j : Fin n, ((if j ∈ D then c1 else c0) /
          l ^ (1 + (if j ∈ D then 1 else 0))) ≤
          ∏ j : Fin n, Eint (if j ∈ D then 1 else 0) l := by
        refine prod_le_prod (fun j _ => ?_) (fun j _ => hE j)
        refine div_nonneg ?_ (pow_nonneg hl0.le _)
        split_ifs
        · exact hc1_nonneg
        · exact hc0_nonneg
      rw [prod_div_distrib, prod_pow_eq_pow_sum, sum_indicator] at h1
      exact h1
    have h3 : Real.exp (-(L + 1)) ≤ Real.exp (-l) := by
      rw [Real.exp_le_exp]
      linarith [hl.2]
    have h4 : Real.exp (-(L + 1)) = 1 / n * Real.exp (-1) := by
      rw [neg_add, Real.exp_add, hLn]
    unfold ww
    obtain ⟨N, hN⟩ : ∃ N, n + D.card = N + 1 := ⟨n + D.card - 1, by omega⟩
    have h5 : l ^ (n + D.card - 1) * Real.exp (-l) *
        ((∏ j : Fin n, (if j ∈ D then c1 else c0)) / l ^ (n + D.card)) =
        Real.exp (-l) * (∏ j : Fin n, (if j ∈ D then c1 else c0)) / l := by
      rw [hN, Nat.add_sub_cancel, pow_succ]
      field_simp
    have h6 : l ^ (n + D.card - 1) * Real.exp (-l) *
        ((∏ j : Fin n, (if j ∈ D then c1 else c0)) / l ^ (n + D.card)) ≤
        l ^ (n + D.card - 1) * Real.exp (-l) *
          ∏ j : Fin n, Eint (if j ∈ D then 1 else 0) l :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    rw [h5] at h6
    refine le_trans ?_ h6
    have hP0 : 0 ≤ ∏ j : Fin n, (if j ∈ D then c1 else c0) := by
      have h7 : (0 : ℝ) ≤ Real.exp (-2) / 2 := by positivity
      linarith
    have h8 : Real.exp (-3) / (2 * n * (L + 1)) =
        (1 / n * Real.exp (-1)) * (Real.exp (-2) / 2) / (L + 1) := by
      have h9 : Real.exp (-3) = Real.exp (-1) * Real.exp (-2) := by
        rw [← Real.exp_add]
        norm_num
      rw [h9]
      field_simp
    rw [h8, ← h4]
    have h10 : Real.exp (-(L + 1)) * (Real.exp (-2) / 2) ≤
        Real.exp (-l) * ∏ j : Fin n, (if j ∈ D then c1 else c0) :=
      mul_le_mul h3 hprodc (by positivity) (Real.exp_pos _).le
    calc Real.exp (-(L + 1)) * (Real.exp (-2) / 2) / (L + 1)
        ≤ Real.exp (-l) * (∏ j : Fin n, (if j ∈ D then c1 else c0)) / (L + 1) :=
          div_le_div_of_nonneg_right h10 (by linarith)
      _ ≤ Real.exp (-l) * (∏ j : Fin n, (if j ∈ D then c1 else c0)) / l :=
          div_le_div_of_nonneg_left (mul_nonneg (Real.exp_pos _).le hP0) hl0 hl.2
  -- integrate over the window
  have hsub : Set.Icc L (L + 1) ⊆ Set.Ioi (0 : ℝ) := fun l hl => lt_of_lt_of_le hL0 hl.1
  have h1 : ∫ l in Set.Icc L (L + 1), ww n D l ≤ ∫ l in Set.Ioi (0 : ℝ), ww n D l :=
    setIntegral_mono_set (integrableOn_ww hn1 D)
      ((ae_restrict_mem measurableSet_Ioi).mono fun l hl => ww_nonneg D (le_of_lt hl))
      hsub.eventuallyLE
  have h2 := setIntegral_ge_of_const_le_real (μ := volume) measurableSet_Icc
    (measure_Icc_lt_top (a := L) (b := L + 1)).ne hpt ((integrableOn_ww hn1 D).mono_set hsub)
  have h3 : (volume : Measure ℝ).real (Set.Icc L (L + 1)) = 1 := by
    simp [Measure.real, Real.volume_Icc]
  rw [h3, mul_one] at h2
  refine le_trans ?_ (le_trans h2 h1)
  have he3 := exp_three_le
  have he3' : Real.exp (-3) * Real.exp 3 = 1 := by
    rw [← Real.exp_add]
    simp
  have he3pos := Real.exp_pos (-3)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h4 : 2 * (n : ℝ) * (L + 1) * Real.exp 3 ≤ 100 * n * L := by
    have h5 : 2 * (n : ℝ) * (L + 1) * Real.exp 3 ≤ 2 * n * (L + 1) * 21 :=
      mul_le_mul_of_nonneg_left he3 (by positivity)
    nlinarith
  have h6 := mul_le_mul_of_nonneg_left h4 he3pos.le
  have h7 : Real.exp (-3) * (2 * (n : ℝ) * (L + 1) * Real.exp 3) = 2 * n * (L + 1) := by
    rw [show Real.exp (-3) * (2 * (n : ℝ) * (L + 1) * Real.exp 3) =
      (Real.exp (-3) * Real.exp 3) * (2 * n * (L + 1)) by ring, he3', one_mul]
  linarith

/-- **Steps D6 and D7.** The lower bound for `JJ`, under explicit size conditions. -/
theorem JJ_lower (hn : 76 ≤ n) (D : Finset (Fin n)) (L : ℝ) (hL1 : 1 ≤ L)
    (hLn : Real.exp (-L) = 1 / n) (hL2 : 1 + L ≤ n / 2)
    (hk : (D.card : ℝ) * (1 + L) ≤ n / 2)
    (H1 : 5472 * (n : ℝ) + 5632 * n * L ^ 2 + 428032 * L ^ 2 ≤ 2 * n ^ 2)
    (H2 : 35200 * L ≤ (n : ℝ) ^ 2) :
    Real.exp (-75) / (100 * n * L * ((n + D.card - 1).factorial : ℝ)) ≤ JJ n 1 D := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (76 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  set W := ∫ l in Set.Ioi (0 : ℝ), ww n D l with hW
  have hWge := integral_ww_ge (by omega) D L hL1 hLn hL2 hk
  have hWpos : 0 < W := lt_of_lt_of_le (by positivity) hWge
  have hT := TT_eq hn1 D
  have hR := RRr_le hn1 D (4 * L) (by linarith)
  have hexp : Real.exp (-(4 * L / 2)) = 1 / (n : ℝ) ^ 2 := by
    rw [show -(4 * L / 2) = -L + -L by ring, Real.exp_add, hLn]
    field_simp
  rw [hexp] at hR
  have hJ := JJ_ge D 75 (by norm_num)
  obtain ⟨N, hN⟩ : ∃ N, n + D.card = N + 1 := ⟨n + D.card - 1, by omega⟩
  rw [hN] at hT hR ⊢
  simp only [Nat.add_sub_cancel] at hT ⊢
  have hNn : (n : ℝ) ≤ (N : ℝ) + 1 := by
    have h1 : n ≤ N + 1 := by omega
    exact_mod_cast h1
  have hfN : (0 : ℝ) < (N.factorial : ℝ) := by positivity
  have hfact : ((N + 1 + 1).factorial : ℝ) = ((N : ℝ) + 2) * ((N : ℝ) + 1) * (N.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  -- the correction is at most 75 / (2n + 152) of the main term
  have hkey : (2 * (n : ℝ) + 2 + 2 * 75) * RRr n D ≤ 75 * TT n D := by
    rw [hT]
    refine le_trans (mul_le_mul_of_nonneg_left hR (by positivity)) ?_
    rw [hfact]
    have hN2 : (n : ℝ) ^ 2 ≤ ((N : ℝ) + 2) * ((N : ℝ) + 1) := by nlinarith
    have hnum : (2 * (n : ℝ) + 2 + 2 * 75) *
        ((22 * (4 * L) ^ 2 + 36 * n) * W + 88 * (1 / (n : ℝ) ^ 2)) ≤ 75 * (n : ℝ) ^ 2 * W := by
      have h1 : (2 * (n : ℝ) + 2 + 2 * 75) * (22 * (4 * L) ^ 2 + 36 * n) =
          72 * (n : ℝ) ^ 2 + (5472 * n + 704 * n * L ^ 2 + 53504 * L ^ 2) := by ring
      have h2 : 5472 * (n : ℝ) + 704 * n * L ^ 2 + 53504 * L ^ 2 ≤ 2 * (n : ℝ) ^ 2 := by
        nlinarith [sq_nonneg L, mul_nonneg hn0.le (sq_nonneg L)]
      have h3 : (2 * (n : ℝ) + 2 + 2 * 75) * (88 * (1 / (n : ℝ) ^ 2)) ≤ (n : ℝ) ^ 2 * W := by
        have h4 : (2 * (n : ℝ) + 2 + 2 * 75) * (88 * (1 / (n : ℝ) ^ 2)) ≤ 352 / n := by
          rw [show (2 * (n : ℝ) + 2 + 2 * 75) * (88 * (1 / (n : ℝ) ^ 2)) =
            (2 * (n : ℝ) + 152) * 88 / (n : ℝ) ^ 2 by ring]
          rw [div_le_div_iff₀ (by positivity) hn0]
          nlinarith
        have h5 : 352 / (n : ℝ) ≤ (n : ℝ) ^ 2 * (1 / (100 * n * L)) := by
          rw [show (n : ℝ) ^ 2 * (1 / (100 * n * L)) = n / (100 * L) by
            field_simp]
          rw [div_le_div_iff₀ hn0 (by positivity)]
          nlinarith
        have h6 : (n : ℝ) ^ 2 * (1 / (100 * n * L)) ≤ (n : ℝ) ^ 2 * W :=
          mul_le_mul_of_nonneg_left hWge (by positivity)
        linarith
      have h7 : (2 * (n : ℝ) + 2 + 2 * 75) * ((22 * (4 * L) ^ 2 + 36 * n) * W) =
          (72 * (n : ℝ) ^ 2 + (5472 * n + 704 * n * L ^ 2 + 53504 * L ^ 2)) * W := by
        rw [← h1]
        ring
      have h8 : (72 * (n : ℝ) ^ 2 + (5472 * n + 704 * n * L ^ 2 + 53504 * L ^ 2)) * W ≤
          74 * (n : ℝ) ^ 2 * W := by
        have h9 : 72 * (n : ℝ) ^ 2 + (5472 * n + 704 * n * L ^ 2 + 53504 * L ^ 2) ≤
            74 * (n : ℝ) ^ 2 := by linarith
        exact mul_le_mul_of_nonneg_right h9 hWpos.le
      rw [mul_add, h7]
      linarith
    have hden : (0 : ℝ) < ((N : ℝ) + 2) * ((N : ℝ) + 1) * (N.factorial : ℝ) := by positivity
    rw [show (2 * (n : ℝ) + 2 + 2 * 75) *
        (1 / (((N : ℝ) + 2) * ((N : ℝ) + 1) * (N.factorial : ℝ)) *
          ((22 * (4 * L) ^ 2 + 36 * n) * W + 88 * (1 / (n : ℝ) ^ 2))) =
        (2 * (n : ℝ) + 2 + 2 * 75) *
          ((22 * (4 * L) ^ 2 + 36 * n) * W + 88 * (1 / (n : ℝ) ^ 2)) /
          (((N : ℝ) + 2) * ((N : ℝ) + 1) * (N.factorial : ℝ)) by ring]
    rw [div_le_iff₀ hden]
    have h10 : 75 * (1 / (N.factorial : ℝ) * W) *
        (((N : ℝ) + 2) * ((N : ℝ) + 1) * (N.factorial : ℝ)) =
        75 * W * (((N : ℝ) + 2) * ((N : ℝ) + 1)) := by
      field_simp
    rw [h10]
    have h11 : 75 * (n : ℝ) ^ 2 * W ≤ 75 * W * (((N : ℝ) + 2) * ((N : ℝ) + 1)) := by
      nlinarith [mul_le_mul_of_nonneg_left hN2 (by positivity : (0 : ℝ) ≤ 75 * W)]
    linarith
  have hfinal : Real.exp (-75) * TT n D ≤ JJ n 1 D := by
    refine le_trans ?_ hJ
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    linarith
  refine le_trans ?_ hfinal
  rw [hT]
  have h12 : Real.exp (-75) / (100 * n * L * (N.factorial : ℝ)) =
      Real.exp (-75) * (1 / (N.factorial : ℝ) * (1 / (100 * n * L))) := by
    field_simp
  rw [h12]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hWge (by positivity)) (Real.exp_pos _).le

end Window

end OMA

/-
# Part 20. Step E: counting the typed pairs
-/

namespace OMA

open StableMarriage.Unbalanced
open Finset
open Classical
open MeasureTheory unitInterval

section Summation

variable {n : ℕ}

/-- There are at least `numDerangements |C|` permutations deranging `C` and fixing the rest. -/
theorem card_Der_ge (C : Finset (Fin n)) : numDerangements C.card ≤ (Der C).card := by
  have h1 : numDerangements C.card = Fintype.card (derangements C) := by
    rw [card_derangements_eq_numDerangements, Fintype.card_coe]
  rw [h1, ← Finset.card_univ]
  refine card_le_card_of_injOn (fun g => Equiv.Perm.ofSubtype g.1) ?_ ?_
  · intro g _
    rw [mem_coe, Der, mem_filter]
    refine ⟨mem_univ _, fun i hi => ?_, fun i hi => ?_⟩
    · rw [Equiv.Perm.ofSubtype_apply_of_mem g.1 hi]
      refine ⟨(g.1 ⟨i, hi⟩).2, fun h => ?_⟩
      exact g.2 ⟨i, hi⟩ (Subtype.ext h)
    · exact Equiv.Perm.ofSubtype_apply_of_not_mem g.1 hi
  · intro g1 _ g2 _ h
    exact Subtype.ext (Equiv.Perm.ofSubtype_injective h)

/-- **Lemma B2.** `D_a ≥ a! / 3` for `a ≥ 2`. -/
theorem numDerangements_ge (a : ℕ) (ha : 2 ≤ a) : a.factorial ≤ 3 * numDerangements a := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    match a, ha with
    | 2, _ => decide
    | 3, _ => decide
    | (a + 4), _ =>
      have h1 := ih (a + 2) (by omega) (by omega)
      have h2 := ih (a + 3) (by omega) (by omega)
      have h3 : numDerangements (a + 4) =
          (a + 3) * (numDerangements (a + 2) + numDerangements (a + 3)) :=
        numDerangements_add_two (a + 2)
      have h4 : (a + 4).factorial = (a + 3) * ((a + 2).factorial + (a + 3).factorial) := by
        rw [Nat.factorial_succ (a + 3), Nat.factorial_succ (a + 2)]
        ring
      rw [h3, h4]
      calc (a + 3) * ((a + 2).factorial + (a + 3).factorial)
          ≤ (a + 3) * (3 * numDerangements (a + 2) + 3 * numDerangements (a + 3)) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = 3 * ((a + 3) * (numDerangements (a + 2) + numDerangements (a + 3))) := by ring

theorem factorial_add_le (m k : ℕ) : (m + k).factorial ≤ m.factorial * (m + k) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, Nat.factorial_succ, pow_succ]
    calc (m + k + 1) * (m + k).factorial ≤ (m + k + 1) * (m.factorial * (m + k) ^ k) :=
          Nat.mul_le_mul_left _ ih
      _ ≤ (m + k + 1) * (m.factorial * (m + k + 1) ^ k) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) k))
      _ = m.factorial * ((m + k + 1) ^ k * (m + k + 1)) := by ring

theorem JJ_nonneg (d : ℕ) (D : Finset (Fin n)) : 0 ≤ JJ n d D := by
  unfold JJ
  refine integral_nonneg fun y => ?_
  exact mul_nonneg (prod_nonneg fun k _ => pow_nonneg (y k).2.1 _)
    (prod_nonneg fun i _ => hh_nonneg _ _ y i)

/-- The sum over typed pairs dominates the sum over the sizes `(a, b)` in a square. -/
theorem sum_pairs_ge (M : ℕ) (hM : 2 * M ≤ n) (β : ℕ → ℝ) (hβ0 : ∀ k, 0 ≤ β k)
    (hβ : ∀ D : Finset (Fin n), D.card ≤ 2 * M → β D.card ≤ JJ n 1 D) :
    ∑ a ∈ Icc 2 M, ∑ b ∈ Icc 2 M, ((n.choose a : ℝ) * ((n - a).choose b : ℝ) *
        (numDerangements a : ℝ) * (numDerangements b : ℝ) * β (a + b)) ≤
      ∑ A : Finset (Fin n), ∑ B : Finset (Fin n),
        (if Disjoint A B then ((Der A).card : ℝ) * ((Der B).card : ℝ) * JJ n 1 (A ∪ B)
          else 0) := by
  have hG0 : ∀ A B : Finset (Fin n), (0 : ℝ) ≤
      (if Disjoint A B then ((Der A).card : ℝ) * ((Der B).card : ℝ) * JJ n 1 (A ∪ B)
        else 0) := by
    intro A B
    split_ifs
    · exact mul_nonneg (by positivity) (JJ_nonneg 1 _)
    · exact le_rfl
  -- inner sum for a fixed A of size a
  have hinner : ∀ a ∈ Icc 2 M, ∀ A ∈ powersetCard a (univ : Finset (Fin n)),
      ∑ b ∈ Icc 2 M, (((n - a).choose b : ℝ) * (numDerangements a : ℝ) *
        (numDerangements b : ℝ) * β (a + b)) ≤
      ∑ B : Finset (Fin n),
        (if Disjoint A B then ((Der A).card : ℝ) * ((Der B).card : ℝ) * JJ n 1 (A ∪ B)
          else 0) := by
    intro a ha A hA
    rw [mem_Icc] at ha
    have hAcard : A.card = a := (mem_powersetCard.mp hA).2
    have hAc : Aᶜ.card = n - a := by
      rw [card_compl, hAcard, Fintype.card_fin]
    have h1 : ∑ B ∈ Aᶜ.powerset,
        (if Disjoint A B then ((Der A).card : ℝ) * ((Der B).card : ℝ) * JJ n 1 (A ∪ B)
          else 0) ≤
        ∑ B : Finset (Fin n),
          (if Disjoint A B then ((Der A).card : ℝ) * ((Der B).card : ℝ) * JJ n 1 (A ∪ B)
            else 0) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) fun B _ _ => hG0 A B
    refine le_trans ?_ h1
    rw [sum_powerset]
    have h2 : Icc 2 M ⊆ range (Aᶜ.card + 1) := by
      intro b hb
      rw [mem_Icc] at hb
      rw [mem_range, hAc]
      omega
    refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg h2 fun b _ _ =>
      sum_nonneg fun B _ => hG0 A B)
    refine sum_le_sum fun b hb => ?_
    rw [mem_Icc] at hb
    have h3 : ∀ B ∈ powersetCard b Aᶜ,
        (numDerangements a : ℝ) * (numDerangements b : ℝ) * β (a + b) ≤
        (if Disjoint A B then ((Der A).card : ℝ) * ((Der B).card : ℝ) * JJ n 1 (A ∪ B)
          else 0) := by
      intro B hB
      rw [mem_powersetCard] at hB
      have hd : Disjoint A B := by
        rw [Finset.disjoint_left]
        intro i hiA hiB
        exact (mem_compl.mp (hB.1 hiB)) hiA
      have hcard : (A ∪ B).card = a + b := by
        rw [card_union_of_disjoint hd, hAcard, hB.2]
      rw [if_pos hd]
      have hJ := hβ (A ∪ B) (by rw [hcard]; omega)
      rw [hcard] at hJ
      have hDA : (numDerangements a : ℝ) ≤ ((Der A).card : ℝ) := by
        have h4 := card_Der_ge A
        rw [hAcard] at h4
        exact_mod_cast h4
      have hDB : (numDerangements b : ℝ) ≤ ((Der B).card : ℝ) := by
        have h4 := card_Der_ge B
        rw [hB.2] at h4
        exact_mod_cast h4
      exact mul_le_mul (mul_le_mul hDA hDB (by positivity) (by positivity)) hJ (hβ0 _)
        (by positivity)
    have h5 := sum_le_sum h3
    rw [sum_const, card_powersetCard, hAc, nsmul_eq_mul] at h5
    refine le_trans (le_of_eq ?_) h5
    ring
  -- outer sum
  have h6 : ∑ A : Finset (Fin n), ∑ B : Finset (Fin n),
      (if Disjoint A B then ((Der A).card : ℝ) * ((Der B).card : ℝ) * JJ n 1 (A ∪ B)
        else 0) =
      ∑ a ∈ range (n + 1), ∑ A ∈ powersetCard a (univ : Finset (Fin n)),
        ∑ B : Finset (Fin n),
          (if Disjoint A B then ((Der A).card : ℝ) * ((Der B).card : ℝ) * JJ n 1 (A ∪ B)
            else 0) := by
    rw [← powerset_univ, sum_powerset, card_univ, Fintype.card_fin]
  rw [h6]
  have h7 : Icc 2 M ⊆ range (n + 1) := by
    intro a ha
    rw [mem_Icc] at ha
    rw [mem_range]
    omega
  refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg h7 fun a _ _ =>
    sum_nonneg fun A _ => sum_nonneg fun B _ => hG0 A B)
  refine sum_le_sum fun a ha => ?_
  have h8 := sum_le_sum (hinner a ha)
  rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul] at h8
  refine le_trans (le_of_eq ?_) h8
  rw [mul_sum]
  exact sum_congr rfl fun b _ => by ring

end Summation

end OMA

/-
# Part 21. Step E: the second moment along `n = 16 P ^ 4`, and the refutation
-/

namespace OMA

open StableMarriage.Unbalanced
open Finset
open Classical
open MeasureTheory unitInterval

section Final

/-- The arithmetic of one pair of sizes `(a, b)`. -/
theorem term_ge (M n a b : ℕ) (hn : n = 16 * M ^ 2) (hM : 2 ≤ M) (ha2 : 2 ≤ a) (haM : a ≤ M)
    (hb2 : 2 ≤ b) (hbM : b ≤ M) :
    (n : ℝ) * (n + 1) / 18 * ((n + (a + b) - 1).factorial : ℝ) ≤
      ((n + 1).factorial : ℝ) * ((n.choose a : ℝ) * ((n - a).choose b : ℝ) *
        (numDerangements a : ℝ) * (numDerangements b : ℝ)) := by
  have hMn : 2 * M ≤ n := by
    rw [hn]
    nlinarith
  have hn1 : 1 ≤ n := by omega
  have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hnR : (n : ℝ) = 16 * (M : ℝ) ^ 2 := by
    rw [hn]
    push_cast
    ring
  have hn0 : (0 : ℝ) < n := by
    rw [hnR]
    positivity
  set u : ℝ := (n : ℝ) - 2 * M with hu
  set v : ℝ := (n : ℝ) + 2 * M with hv
  have hu0 : 0 ≤ u := by
    rw [hu, hnR]
    nlinarith
  have hv0 : 0 < v := by
    rw [hv]
    positivity
  -- descending factorials
  have hA : u ^ a ≤ (a.factorial : ℝ) * (n.choose a : ℝ) := by
    have h1 := Nat.pow_sub_le_descFactorial n a
    rw [Nat.descFactorial_eq_factorial_mul_choose] at h1
    have h2 : ((n + 1 - a : ℕ) : ℝ) ^ a ≤ (a.factorial : ℝ) * (n.choose a : ℝ) := by
      exact_mod_cast h1
    refine le_trans (pow_le_pow_left₀ hu0 ?_ a) h2
    rw [Nat.cast_sub (by omega), hu]
    push_cast
    have : (a : ℝ) ≤ M := by exact_mod_cast haM
    linarith
  have hB : u ^ b ≤ (b.factorial : ℝ) * ((n - a).choose b : ℝ) := by
    have h1 := Nat.pow_sub_le_descFactorial (n - a) b
    rw [Nat.descFactorial_eq_factorial_mul_choose] at h1
    have h2 : ((n - a + 1 - b : ℕ) : ℝ) ^ b ≤ (b.factorial : ℝ) * ((n - a).choose b : ℝ) := by
      exact_mod_cast h1
    refine le_trans (pow_le_pow_left₀ hu0 ?_ b) h2
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_sub (by omega), hu]
    push_cast
    have h3 : (a : ℝ) ≤ M := by exact_mod_cast haM
    have h4 : (b : ℝ) ≤ M := by exact_mod_cast hbM
    linarith
  have hDa : (a.factorial : ℝ) ≤ 3 * (numDerangements a : ℝ) := by
    exact_mod_cast numDerangements_ge a ha2
  have hDb : (b.factorial : ℝ) ≤ 3 * (numDerangements b : ℝ) := by
    exact_mod_cast numDerangements_ge b hb2
  have hX : u ^ (a + b) ≤ 9 * ((n.choose a : ℝ) * ((n - a).choose b : ℝ) *
      (numDerangements a : ℝ) * (numDerangements b : ℝ)) := by
    rw [pow_add]
    have h1 : u ^ a * u ^ b ≤ ((a.factorial : ℝ) * (n.choose a : ℝ)) *
        ((b.factorial : ℝ) * ((n - a).choose b : ℝ)) :=
      mul_le_mul hA hB (pow_nonneg hu0 _) (by positivity)
    have h2 : ((a.factorial : ℝ) * (n.choose a : ℝ)) *
        ((b.factorial : ℝ) * ((n - a).choose b : ℝ)) ≤
        ((3 * (numDerangements a : ℝ)) * (n.choose a : ℝ)) *
          ((3 * (numDerangements b : ℝ)) * ((n - a).choose b : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hDa (by positivity))
        (mul_le_mul_of_nonneg_right hDb (by positivity)) (by positivity) (by positivity)
    have h3 : ((3 * (numDerangements a : ℝ)) * (n.choose a : ℝ)) *
        ((3 * (numDerangements b : ℝ)) * ((n - a).choose b : ℝ)) =
        9 * ((n.choose a : ℝ) * ((n - a).choose b : ℝ) *
          (numDerangements a : ℝ) * (numDerangements b : ℝ)) := by ring
    linarith
  -- the factorial in the denominator
  have hF : ((n + (a + b) - 1).factorial : ℝ) ≤ ((n - 1).factorial : ℝ) * v ^ (a + b) := by
    have h1 := factorial_add_le (n - 1) (a + b)
    have h2 : n - 1 + (a + b) = n + (a + b) - 1 := by omega
    rw [h2] at h1
    have h3 : ((n + (a + b) - 1).factorial : ℝ) ≤
        ((n - 1).factorial : ℝ) * ((n + (a + b) - 1 : ℕ) : ℝ) ^ (a + b) := by
      exact_mod_cast h1
    refine le_trans h3 (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ _)
      (by positivity))
    have h4 : n + (a + b) - 1 ≤ n + 2 * M := by omega
    have h5 : ((n + (a + b) - 1 : ℕ) : ℝ) ≤ ((n + 2 * M : ℕ) : ℝ) := by exact_mod_cast h4
    rw [hv]
    push_cast at h5
    exact h5
  have hfact : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * n * ((n - 1).factorial : ℝ) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn1
    rw [Nat.add_sub_cancel_left, Nat.factorial_succ, show 1 + k = k + 1 by ring,
      Nat.factorial_succ]
    push_cast
    ring
  -- Bernoulli
  have hratio : v ^ (a + b) ≤ 2 * u ^ (a + b) := by
    have h1 : (-2 : ℝ) ≤ -(4 * M / v) := by
      have h2 : 4 * (M : ℝ) / v ≤ 2 := by
        rw [div_le_iff₀ hv0, hv]
        nlinarith
      linarith
    have h3 := one_add_mul_le_pow h1 (a + b)
    have h4 : 1 + -(4 * (M : ℝ) / v) = u / v := by
      rw [hu, hv]
      field_simp
      ring
    rw [h4, div_pow] at h3
    have h5 : ((a + b : ℕ) : ℝ) * (4 * (M : ℝ) / v) ≤ 1 / 2 := by
      have h6 : ((a + b : ℕ) : ℝ) ≤ 2 * M := by
        have : a + b ≤ 2 * M := by omega
        exact_mod_cast this
      rw [← mul_div_assoc, div_le_iff₀ hv0, hv, hnR]
      nlinarith
    have h7 : (1 : ℝ) / 2 ≤ u ^ (a + b) / v ^ (a + b) := by
      have h8 : (1 : ℝ) + ((a + b : ℕ) : ℝ) * -(4 * (M : ℝ) / v) ≥ 1 / 2 := by linarith
      linarith
    rw [le_div_iff₀ (pow_pos hv0 _)] at h7
    linarith
  have hfn : (0 : ℝ) < ((n - 1).factorial : ℝ) := by positivity
  rw [hfact]
  have h9 : (n : ℝ) * (n + 1) / 18 * ((n + (a + b) - 1).factorial : ℝ) ≤
      (n : ℝ) * (n + 1) / 18 * (((n - 1).factorial : ℝ) * (2 * u ^ (a + b))) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact le_trans hF (mul_le_mul_of_nonneg_left hratio hfn.le)
  have h10 : (n : ℝ) * (n + 1) / 18 * (((n - 1).factorial : ℝ) * (2 * u ^ (a + b))) ≤
      ((n : ℝ) + 1) * n * ((n - 1).factorial : ℝ) *
        ((n.choose a : ℝ) * ((n - a).choose b : ℝ) *
          (numDerangements a : ℝ) * (numDerangements b : ℝ)) := by
    have h11 : (0 : ℝ) ≤ ((n : ℝ) + 1) * n * ((n - 1).factorial : ℝ) / 9 := by positivity
    have h12 := mul_le_mul_of_nonneg_left hX h11
    have h13 : (n : ℝ) * (n + 1) / 18 * (((n - 1).factorial : ℝ) * (2 * u ^ (a + b))) =
        ((n : ℝ) + 1) * n * ((n - 1).factorial : ℝ) / 9 * u ^ (a + b) := by ring
    have h14 : ((n : ℝ) + 1) * n * ((n - 1).factorial : ℝ) / 9 *
        (9 * ((n.choose a : ℝ) * ((n - a).choose b : ℝ) *
          (numDerangements a : ℝ) * (numDerangements b : ℝ))) =
        ((n : ℝ) + 1) * n * ((n - 1).factorial : ℝ) *
          ((n.choose a : ℝ) * ((n - a).choose b : ℝ) *
            (numDerangements a : ℝ) * (numDerangements b : ℝ)) := by ring
    linarith
  linarith

/-- Size facts along `n = 16 P ^ 4`. -/
theorem log_facts (P n : ℕ) (hP : 200 ≤ P) (hn : n = 16 * P ^ 4) :
    1 ≤ Real.log n ∧ Real.log n ≤ 8 * P ∧ Real.exp (-Real.log n) = 1 / n := by
  have hPR : (200 : ℝ) ≤ P := by exact_mod_cast hP
  have hnR : (n : ℝ) = (2 * (P : ℝ)) ^ 4 := by
    rw [hn]
    push_cast
    ring
  have hn0 : (0 : ℝ) < n := by
    rw [hnR]
    positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.le_log_iff_exp_le hn0]
    have h1 := Real.exp_one_lt_d9
    have h2 : (3 : ℝ) ≤ n := by
      rw [hnR]
      nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 400) (by linarith : (400 : ℝ) ≤ 2 * P) 4]
    linarith
  · rw [hnR, Real.log_pow]
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * P by positivity)
    push_cast
    linarith
  · rw [Real.exp_neg, Real.exp_log hn0, one_div]

theorem expected_nonneg (n m : ℕ) : 0 ≤ expectedNumStableMatchings n m := by
  unfold expectedNumStableMatchings
  exact integral_nonneg fun p => Nat.cast_nonneg _

set_option maxHeartbeats 1600000 in
/-- **Step E.** The second moment along `n = 16 P ^ 4`. -/
theorem second_moment_lower (P n : ℕ) (hP : 200 ≤ P) (hn : n = 16 * P ^ 4) :
    Real.exp (-75) * (n : ℝ) ^ 2 / (115200 * Real.log n) ≤
      secondMomentNumStableMatchings n (n + 1) := by
  obtain ⟨hL1, hL8, hLn⟩ := log_facts P n hP hn
  set L := Real.log n with hL
  set M := P ^ 2 with hM
  have hPR : (200 : ℝ) ≤ P := by exact_mod_cast hP
  have hMR : (M : ℝ) = (P : ℝ) ^ 2 := by
    rw [hM]
    push_cast
    ring
  have hM4 : (40000 : ℝ) ≤ M := by
    rw [hMR]
    nlinarith
  have hPM : (P : ℝ) ≤ M := by
    rw [hMR]
    nlinarith
  have hnM : n = 16 * M ^ 2 := by
    rw [hn, hM]
    ring
  have hnR : (n : ℝ) = 16 * (M : ℝ) ^ 2 := by
    rw [hnM]
    push_cast
    ring
  have hn0 : (0 : ℝ) < n := by
    rw [hnR]
    positivity
  have hM2 : 2 ≤ M := by
    have : (2 : ℝ) ≤ M := by linarith
    exact_mod_cast this
  have hMn : 2 * M ≤ n := by
    rw [hnM]
    nlinarith
  have hn76 : 76 ≤ n := by
    have : (76 : ℝ) ≤ n := by
      rw [hnR]
      nlinarith
    exact_mod_cast this
  have hL0 : (0 : ℝ) < L := by linarith
  have hL8M : L ≤ 8 * M := by linarith
  have hLsq : L ^ 2 ≤ 64 * (M : ℝ) := by
    have h1 : L ^ 2 ≤ (8 * (P : ℝ)) ^ 2 := pow_le_pow_left₀ hL0.le hL8 2
    rw [hMR]
    nlinarith
  have hL2 : 1 + L ≤ (n : ℝ) / 2 := by
    rw [hnR]
    nlinarith
  have hL4 : 1 + L ≤ 4 * (M : ℝ) := by
    rw [hMR]
    nlinarith
  have H1 : 5472 * (n : ℝ) + 5632 * n * L ^ 2 + 428032 * L ^ 2 ≤ 2 * (n : ℝ) ^ 2 := by
    have h1 : 5632 * (n : ℝ) * L ^ 2 ≤ 5632 * n * (64 * M) :=
      mul_le_mul_of_nonneg_left hLsq (by positivity)
    have h2 : 428032 * L ^ 2 ≤ 428032 * (64 * (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hLsq (by norm_num)
    rw [hnR] at h1 ⊢
    have h3 : (M : ℝ) ^ 2 ≥ 40000 * M := by nlinarith
    have h4 : (M : ℝ) ^ 3 ≥ 40000 * (M : ℝ) ^ 2 := by nlinarith
    have h5 : (M : ℝ) ^ 4 ≥ 40000 * (M : ℝ) ^ 3 := by nlinarith
    nlinarith
  have H2 : 35200 * L ≤ (n : ℝ) ^ 2 := by
    rw [hnR]
    have h3 : (M : ℝ) ^ 2 ≥ 40000 * M := by nlinarith
    nlinarith [sq_nonneg ((M : ℝ) ^ 2)]
  -- the lower bound for JJ, as a function of the number of moved firms
  let β : ℕ → ℝ := fun k =>
    Real.exp (-75) / (100 * n * L * ((n + k - 1).factorial : ℝ))
  have hβ0 : ∀ k, 0 ≤ β k := fun k => by positivity
  have hβ : ∀ D : Finset (Fin n), D.card ≤ 2 * M → β D.card ≤ JJ n 1 D := by
    intro D hD
    refine JJ_lower hn76 D L hL1 hLn hL2 ?_ H1 H2
    have h1 : (D.card : ℝ) ≤ 2 * M := by exact_mod_cast hD
    rw [hnR]
    nlinarith
  have hsum := sum_pairs_ge M hMn β hβ0 hβ
  have hsm := second_moment_ge n (n + 1)
  rw [Nat.add_sub_cancel_left] at hsm
  have hdf : (n + 1).descFactorial n = (n + 1).factorial := by
    have h4 := Nat.factorial_mul_descFactorial (show n ≤ n + 1 by omega)
    rw [Nat.add_sub_cancel_left, Nat.factorial_one, one_mul] at h4
    exact h4
  rw [hdf] at hsm
  refine le_trans ?_ hsm
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hsum (by positivity))
  -- every term of the double sum
  have hterm : ∀ a ∈ Icc 2 M, ∀ b ∈ Icc 2 M,
      ((n : ℝ) + 1) * Real.exp (-75) / (1800 * L) ≤
      ((n + 1).factorial : ℝ) * ((n.choose a : ℝ) * ((n - a).choose b : ℝ) *
        (numDerangements a : ℝ) * (numDerangements b : ℝ) * β (a + b)) := by
    intro a ha b hb
    rw [mem_Icc] at ha hb
    have h1 := term_ge M n a b hnM hM2 ha.1 ha.2 hb.1 hb.2
    have hf : (0 : ℝ) < ((n + (a + b) - 1).factorial : ℝ) := by positivity
    have h2 : ((n + 1).factorial : ℝ) * ((n.choose a : ℝ) * ((n - a).choose b : ℝ) *
        (numDerangements a : ℝ) * (numDerangements b : ℝ) * β (a + b)) =
        (((n + 1).factorial : ℝ) * ((n.choose a : ℝ) * ((n - a).choose b : ℝ) *
          (numDerangements a : ℝ) * (numDerangements b : ℝ))) *
          (Real.exp (-75) / (100 * n * L * ((n + (a + b) - 1).factorial : ℝ))) := by
      ring
    rw [h2]
    have h3 : (0 : ℝ) ≤ Real.exp (-75) / (100 * n * L * ((n + (a + b) - 1).factorial : ℝ)) := by
      positivity
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right h1 h3)
    field_simp
    ring
  have hcard : ((Icc 2 M).card : ℝ) = (M : ℝ) - 1 := by
    rw [Nat.card_Icc, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hdouble : ((M : ℝ) - 1) * (((M : ℝ) - 1) *
      (((n : ℝ) + 1) * Real.exp (-75) / (1800 * L))) ≤
      ((n + 1).factorial : ℝ) * ∑ a ∈ Icc 2 M, ∑ b ∈ Icc 2 M,
        ((n.choose a : ℝ) * ((n - a).choose b : ℝ) *
          (numDerangements a : ℝ) * (numDerangements b : ℝ) * β (a + b)) := by
    rw [mul_sum]
    have h1 : ∀ a ∈ Icc 2 M, ((M : ℝ) - 1) * (((n : ℝ) + 1) * Real.exp (-75) / (1800 * L)) ≤
        ((n + 1).factorial : ℝ) * ∑ b ∈ Icc 2 M,
          ((n.choose a : ℝ) * ((n - a).choose b : ℝ) *
            (numDerangements a : ℝ) * (numDerangements b : ℝ) * β (a + b)) := by
      intro a ha
      rw [mul_sum]
      have h2 := sum_le_sum (hterm a ha)
      rw [sum_const, nsmul_eq_mul, hcard] at h2
      exact h2
    have h3 := sum_le_sum h1
    rw [sum_const, nsmul_eq_mul, hcard] at h3
    exact h3
  refine le_trans ?_ hdouble
  -- (M - 1)^2 >= M^2 / 4 = n / 64
  have hM1 : (M : ℝ) / 2 ≤ (M : ℝ) - 1 := by linarith
  have hsq : (n : ℝ) / 64 ≤ ((M : ℝ) - 1) * ((M : ℝ) - 1) := by
    rw [hnR]
    nlinarith
  have hpos : (0 : ℝ) ≤ ((n : ℝ) + 1) * Real.exp (-75) / (1800 * L) := by positivity
  have h4 : (n : ℝ) / 64 * (((n : ℝ) + 1) * Real.exp (-75) / (1800 * L)) ≤
      ((M : ℝ) - 1) * (((M : ℝ) - 1) * (((n : ℝ) + 1) * Real.exp (-75) / (1800 * L))) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hsq hpos
  refine le_trans ?_ h4
  rw [div_le_iff₀ (by positivity)]
  have h5 : (n : ℝ) / 64 * (((n : ℝ) + 1) * Real.exp (-75) / (1800 * L)) * (115200 * L) =
      Real.exp (-75) * (n * (n + 1)) := by
    field_simp
    ring
  rw [h5]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  nlinarith

end Final

end OMA

/-
# Part 22. The refutation
-/

namespace OMA

open StableMarriage.Unbalanced
open Filter

/-- Pittel's second-moment bound fails with one extra worker: the ratio of the second moment to
the squared mean is unbounded. -/
theorem not_second_moment : ¬ ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    secondMomentNumStableMatchings n (n + 1) ≤
      C * (expectedNumStableMatchings n (n + 1)) ^ 2 := by
  rintro ⟨C, hC, hev⟩
  rw [eventually_atTop] at hev
  obtain ⟨N0, hN0⟩ := hev
  set K : ℝ := 100 * C * 115200 * Real.exp 75 with hK
  set P : ℕ := max 200 (max N0 (⌈Real.exp K⌉₊ + 1)) with hP
  have hP200 : 200 ≤ P := le_max_left _ _
  have hPN : N0 ≤ P := le_trans (le_max_left _ _) (le_max_right _ _)
  have hPK : ⌈Real.exp K⌉₊ + 1 ≤ P := le_trans (le_max_right _ _) (le_max_right _ _)
  have hPn : P ≤ 16 * P ^ 4 := by
    have h1 : P ≤ P ^ 4 := Nat.le_self_pow (by norm_num) P
    omega
  have hn2 : 200000 ≤ 16 * P ^ 4 := by
    have h1 : 200 ^ 4 ≤ P ^ 4 := Nat.pow_le_pow_left hP200 4
    norm_num at h1
    omega
  obtain ⟨hL1, hL8, hLn⟩ := log_facts P (16 * P ^ 4) hP200 rfl
  have h2 := second_moment_lower P (16 * P ^ 4) hP200 rfl
  have h1 := expected_le (16 * P ^ 4) hn2
  have h0 := expected_nonneg (16 * P ^ 4) (16 * P ^ 4 + 1)
  have h3 := hN0 (16 * P ^ 4) (le_trans hPN hPn)
  have hnR0 : (0 : ℝ) < ((16 * P ^ 4 : ℕ) : ℝ) := by
    have h4 : 0 < 16 * P ^ 4 := by omega
    exact_mod_cast h4
  generalize hndef : ((16 * P ^ 4 : ℕ) : ℝ) = x at *
  generalize hLdef : Real.log x = L at *
  have hL0 : 0 < L := by linarith
  have hLK : K < L := by
    have h4 : Real.exp K < (P : ℝ) := by
      have h5 := Nat.le_ceil (Real.exp K)
      have h6 : ((⌈Real.exp K⌉₊ + 1 : ℕ) : ℝ) ≤ P := by exact_mod_cast hPK
      push_cast at h6
      linarith
    have h7 : (P : ℝ) ≤ x := by
      rw [← hndef]
      exact_mod_cast hPn
    rw [← hLdef, Real.lt_log_iff_exp_lt hnR0]
    linarith
  have h7 : (expectedNumStableMatchings (16 * P ^ 4) (16 * P ^ 4 + 1)) ^ 2 ≤
      (10 * x / L) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h8 : Real.exp (-75) * x ^ 2 / (115200 * L) ≤ C * (10 * x / L) ^ 2 :=
    le_trans h2 (le_trans h3 (mul_le_mul_of_nonneg_left h7 hC.le))
  have h10 : C * (10 * x / L) ^ 2 = 100 * C * x ^ 2 / L ^ 2 := by
    field_simp
    ring
  rw [h10, div_le_div_iff₀ (by positivity) (by positivity)] at h8
  have hX : (0 : ℝ) < x ^ 2 * L := by positivity
  have h12 : (Real.exp (-75) * L) * (x ^ 2 * L) ≤ (100 * C * 115200) * (x ^ 2 * L) := by
    calc (Real.exp (-75) * L) * (x ^ 2 * L) = Real.exp (-75) * x ^ 2 * L ^ 2 := by ring
      _ ≤ 100 * C * x ^ 2 * (115200 * L) := h8
      _ = (100 * C * 115200) * (x ^ 2 * L) := by ring
  have h11 : Real.exp (-75) * L ≤ 100 * C * 115200 := le_of_mul_le_mul_right h12 hX
  have h13 : Real.exp 75 * Real.exp (-75) = 1 := by
    rw [← Real.exp_add]
    simp
  have h14 : L ≤ K := by
    calc L = Real.exp 75 * (Real.exp (-75) * L) := by rw [← mul_assoc, h13, one_mul]
      _ ≤ Real.exp 75 * (100 * C * 115200) :=
          mul_le_mul_of_nonneg_left h11 (Real.exp_pos _).le
      _ = K := by
          rw [hK]
          ring
  linarith

/-- The general statement fails too: take the constant sequence `d n = 1`. -/
theorem not_second_moment_general :
    ¬ ∀ (d : ℕ → ℕ), (∀ n, 1 ≤ d n) →
      Tendsto (fun n ↦ (d n : ℝ) / n) atTop (nhds 0) →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
        secondMomentNumStableMatchings n (n + d n) ≤
          C * (expectedNumStableMatchings n (n + d n)) ^ 2 := by
  intro h
  refine not_second_moment (h (fun _ => 1) (fun _ => le_rfl) ?_)
  simpa using tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)

end OMA

theorem OMA.disproof :
    ¬ (type_of% @Arxiv.«1701.08900».second_moment_one_extra_worker) :=
  OMA.not_second_moment
