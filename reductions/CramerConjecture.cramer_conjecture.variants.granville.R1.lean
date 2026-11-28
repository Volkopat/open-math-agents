import FormalConjectures.Wikipedia.CramerConjecture

/-!
The two hypotheses separate the residue-class model from its comparison with
prime tuples, following the argument for Theorem 1.6 of Banks, Ford, and Tao,
Large prime gaps and probabilistic models (Invent. Math. 233, 2023).
-/

namespace OMA.R_CramerConjecture_cramer_conjecture_variants_granville_R1

open CramerConjecture Filter
open scoped BigOperators Classical

private lemma odd_alternating_choose_nonpos {K a : ℕ} (hK : Odd K) (ha : 0 < a) :
    (∑ k ∈ Finset.range (K + 1), (-1 : ℝ) ^ k * (a.choose k : ℝ)) ≤ 0 := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  have heq :
      (∑ k ∈ Finset.range (K + 1), (-1 : ℝ) ^ k * ((b + 1).choose k : ℝ)) =
        (-1 : ℝ) ^ K * (b.choose K : ℝ) := by
    exact_mod_cast (Int.alternating_sum_range_choose_eq_choose (n := b) (m := K))
  rw [heq, hK.neg_one_pow, neg_one_mul]
  exact neg_nonpos.mpr (Nat.cast_nonneg _)

private lemma exists_zero_of_odd_moment {s : Finset ℕ} {a : ℕ → ℕ} {K : ℕ} (hK : Odd K)
    (h : 0 < ∑ k ∈ Finset.range (K + 1), (-1 : ℝ) ^ k * ∑ m ∈ s, ((a m).choose k : ℝ)) :
    ∃ m ∈ s, a m = 0 := by
  by_contra! hn
  simp_rw [Finset.mul_sum] at h
  rw [Finset.sum_comm] at h
  exact h.not_ge (Finset.sum_nonpos fun m hm =>
    odd_alternating_choose_nonpos hK (Nat.pos_of_ne_zero (hn m hm)))

private lemma actual_moment_pos {E A : ℕ → ℝ} {K : ℕ} {B : ℝ}
    (hE : B < ∑ k ∈ Finset.range (K + 1), (-1 : ℝ) ^ k * E k)
    (hA : (∑ k ∈ Finset.range (K + 1), (-1 : ℝ) ^ k * (E k - A k)) ≤ B) :
    0 < ∑ k ∈ Finset.range (K + 1), (-1 : ℝ) ^ k * A k := by
  simp_rw [mul_sub, Finset.sum_sub_distrib] at hA
  linarith only [hE, hA]

private lemma ratio_of_empty_interval {n₀ m x y : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hfirst : Nat.nth Nat.Prime n₀ ≤ m) (hupper : m ≤ 2 * x)
    (hy : c * (Real.log (2 * (x : ℝ))) ^ 2 ≤ (y : ℝ))
    (hfree : ∀ j ∈ Finset.Icc 1 y, ¬ (m + j).Prime) :
    ∃ n, n₀ ≤ n ∧ c ≤ cramerRatio n := by
  have hinf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  have hcount : n₀ < Nat.count Nat.Prime (m + 1) := by
    rw [← Nat.count_nth_of_infinite hinf n₀]
    exact Nat.count_strict_mono (Nat.nth_mem_of_infinite hinf n₀) (by omega)
  let n := Nat.count Nat.Prime (m + 1) - 1
  have hsucc : n + 1 = Nat.count Nat.Prime (m + 1) := by dsimp [n]; omega
  have hleft : Nat.nth Nat.Prime n ≤ m := by
    have h := Nat.nth_lt_of_lt_count (show n < Nat.count Nat.Prime (m + 1) by omega)
    omega
  have hright : m + 1 ≤ Nat.nth Nat.Prime (n + 1) := by
    rw [hsucc]
    exact Nat.le_nth_count hinf (m + 1)
  have hright' : m + y < Nat.nth Nat.Prime (n + 1) := by
    by_contra! h
    let j := Nat.nth Nat.Prime (n + 1) - m
    have hj : j ∈ Finset.Icc 1 y := Finset.mem_Icc.mpr ⟨by dsimp [j]; omega, by dsimp [j]; omega⟩
    have heq : m + j = Nat.nth Nat.Prime (n + 1) := by dsimp [j]; omega
    exact hfree j hj (heq.symm ▸ Nat.nth_mem_of_infinite hinf (n + 1))
  have hgap : y ≤ primeGap n := by unfold primeGap; omega
  have hp : (Nat.nth Nat.Prime n).Prime := Nat.nth_mem_of_infinite hinf n
  have hlog_pos : 0 < Real.log (Nat.nth Nat.Prime n : ℝ) :=
    Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlog_le : Real.log (Nat.nth Nat.Prime n : ℝ) ≤ Real.log (2 * (x : ℝ)) :=
    Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hleft.trans hupper)
  have hpow := pow_le_pow_left₀ hlog_pos.le hlog_le 2
  refine ⟨n, by omega, ?_⟩
  unfold cramerRatio
  exact (le_div_iff₀ (sq_pos_of_pos hlog_pos)).mpr
    ((mul_le_mul_of_nonneg_left hpow hc).trans (hy.trans (by exact_mod_cast hgap)))

/-- An odd truncated binomial moment in the calibrated random sieve is large
enough to tolerate a power-saving error in its transfer to primes. -/
def H1 : Prop :=
  let z (t : ℝ) := (Finset.range (Nat.floor t + 1)).filter
    (fun q => q.Prime ∧ (∏ p ∈ (Finset.Icc 2 q).filter Nat.Prime, (1 - 1 / (p : ℝ)))⁻¹ ≤ Real.log t)
    |>.sup id
  let E (x y k : ℕ) : ℝ := ∑ S ∈ (Finset.Icc 1 y).powersetCard k,
    ∫ t in (x : ℝ)..(2 * (x : ℝ)),
      ∏ p ∈ (Finset.Icc 2 (z t)).filter Nat.Prime, (1 - ((S.image (fun j => j % p)).card : ℝ) / p)
  ∀ c : ℝ, 0 < c → c < 2 * Real.exp (-Real.eulerMascheroniConstant) →
    ∃ (d : ℝ) (D : ℕ), 0 < d ∧ 0 < D ∧ ∀ N : ℕ, ∃ x y K : ℕ,
      N ≤ x ∧ 3 ≤ x ∧ y = Nat.ceil (c * (Real.log (2 * (x : ℝ))) ^ 2) ∧
      K = 2 * Nat.ceil ((D : ℝ) * (y : ℝ) / Real.log (x : ℝ)) + 1 ∧
      (x : ℝ) ^ d < ∑ k ∈ Finset.range (K + 1), (-1 : ℝ) ^ k * E x y k

/-- The signed prime-tuple discrepancy is small at the truncation order used
in the model certificate. The hypothesis only asks for transfer at scales
where the model has a positive margin. -/
def H2 : Prop :=
  let z (t : ℝ) := (Finset.range (Nat.floor t + 1)).filter
    (fun q => q.Prime ∧ (∏ p ∈ (Finset.Icc 2 q).filter Nat.Prime, (1 - 1 / (p : ℝ)))⁻¹ ≤ Real.log t)
    |>.sup id
  let E (x y k : ℕ) : ℝ := ∑ S ∈ (Finset.Icc 1 y).powersetCard k,
    ∫ t in (x : ℝ)..(2 * (x : ℝ)),
      ∏ p ∈ (Finset.Icc 2 (z t)).filter Nat.Prime, (1 - ((S.image (fun j => j % p)).card : ℝ) / p)
  ∀ c : ℝ, 0 < c → c < 2 * Real.exp (-Real.eulerMascheroniConstant) →
    ∀ d : ℝ, 0 < d → ∀ D : ℕ, 0 < D → ∃ N : ℕ, ∀ x y K : ℕ,
    N ≤ x → 3 ≤ x → y = Nat.ceil (c * (Real.log (2 * (x : ℝ))) ^ 2) →
    K = 2 * Nat.ceil ((D : ℝ) * (y : ℝ) / Real.log (x : ℝ)) + 1 →
    (x : ℝ) ^ d < (∑ k ∈ Finset.range (K + 1), (-1 : ℝ) ^ k * E x y k) →
    (∑ k ∈ Finset.range (K + 1), (-1 : ℝ) ^ k * (E x y k - ∑ m ∈ Finset.Ioc x (2 * x),
      (((Finset.Icc 1 y).filter fun j => (m + j).Prime).card.choose k : ℝ))) ≤ (x : ℝ) ^ d

theorem main : H1 → H2 → type_of% @CramerConjecture.cramer_conjecture.variants.granville := by
  classical
  intro hmodel htransfer c hc
  apply Filter.frequently_atTop.mpr
  intro n₀
  by_cases hcpos : 0 < c
  · obtain ⟨d, D, hd, hD, hmodel⟩ := hmodel c hcpos hc
    obtain ⟨N, htransfer⟩ := htransfer c hcpos hc d hd D hD
    obtain ⟨x, y, K, hx, hx3, hy_eq, hK_eq, hmargin⟩ :=
      hmodel (max N (Nat.nth Nat.Prime n₀))
    have hy : c * (Real.log (2 * (x : ℝ))) ^ 2 ≤ (y : ℝ) := by
      rw [hy_eq]
      exact Nat.le_ceil _
    have hodd : Odd K := ⟨_, hK_eq⟩
    have herror := htransfer x y K ((le_max_left _ _).trans hx) hx3 hy_eq hK_eq hmargin
    let a (m : ℕ) := ((Finset.Icc 1 y).filter fun j => (m + j).Prime).card
    have hpositive :
        0 < ∑ k ∈ Finset.range (K + 1), (-1 : ℝ) ^ k *
          ∑ m ∈ Finset.Ioc x (2 * x), ((a m).choose k : ℝ) :=
      actual_moment_pos hmargin herror
    obtain ⟨m, hm, hz⟩ := exists_zero_of_odd_moment hodd hpositive
    have hm' := Finset.mem_Ioc.mp hm
    refine ratio_of_empty_interval hcpos.le (((le_max_right _ _).trans hx).trans hm'.1.le) hm'.2 hy ?_
    intro j hj hp
    have hmem : j ∈ (Finset.Icc 1 y).filter (fun j => (m + j).Prime) := Finset.mem_filter.mpr ⟨hj, hp⟩
    have hcard := Finset.card_pos.mpr ⟨j, hmem⟩
    exact (Nat.ne_of_gt hcard) hz
  · refine ⟨n₀, le_rfl, (le_of_not_gt hcpos).trans ?_⟩
    unfold cramerRatio
    exact div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

end OMA.R_CramerConjecture_cramer_conjecture_variants_granville_R1
