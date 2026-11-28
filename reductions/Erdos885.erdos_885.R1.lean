import FormalConjectures.ErdosProblems.«885»

/-!
# Erdős problem 885: large intersections of factor-difference sets

For `k = 2, 3, 4` the pinned module proves explicit witnesses `k_eq_2`, `k_eq_3`, `k_eq_4`;
the `k = 1` case is immediate from `mem_factorDifferenceSet_of_eq` applied to `n = 2`.
The genuinely open content is `k ≥ 5`. This reduction splits the proved small cases from
that open core; `main` discharges `k = 1` inline and uses both hypotheses for `k ≥ 2`.
-/

-- Reduction Erdos885.erdos_885.R1
-- Credit: @PetrouilFan
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos885_erdos_885_R1

open Erdos885 Nat Set Finset

/-- Open core: the large-`k` case. -/
def H1 : Prop := ∀ k : ℕ, 5 ≤ k →
  ∃ Ns : Finset ℕ, (∀ n ∈ Ns, 1 ≤ n) ∧ Ns.card = k ∧
    (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ k

/-- Upstream-proved bridge: the explicit small witnesses for `k = 2, 3, 4`. -/
def H2 : Prop := ∀ k : ℕ, 2 ≤ k → k ≤ 4 →
  ∃ Ns : Finset ℕ, (∀ n ∈ Ns, 1 ≤ n) ∧ Ns.card = k ∧
    (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ k

theorem main : H1 → H2 → type_of% @Erdos885.erdos_885 := by
  intro h1 h2 k hk
  by_cases hk1 : k = 1
  · subst k
    refine ⟨{2}, by simp, by simp, ?_⟩
    have hsub : ({1} : Set ℕ) ⊆ ⋂ n ∈ ({2} : Finset ℕ), factorDifferenceSet n := by
      intro d hd
      simp only [Set.mem_singleton_iff] at hd
      subst d
      simp only [Set.mem_iInter, Finset.mem_singleton]
      intro n hn
      subst n
      exact mem_factorDifferenceSet_of_eq (b := 1) (d := 1) (by norm_num : (2 : ℕ) = 1 * (1 + 1))
    have hfin : (⋂ n ∈ ({2} : Finset ℕ), factorDifferenceSet n).Finite :=
      (factorDifferenceSet_finite (by norm_num : 1 ≤ (2 : ℕ))).subset (Set.iInter₂_subset 2 (by simp))
    have hc := Set.ncard_le_ncard hsub hfin
    simpa using hc
  · by_cases hle : k ≤ 4
    · exact h2 k (by omega) hle
    · exact h1 k (by omega)

end OMA.R_Erdos885_erdos_885_R1
