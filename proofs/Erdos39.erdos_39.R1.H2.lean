import OMAReductions.R_Erdos39_erdos_39_R1
import Mathlib

-- Step Erdos39.erdos_39.R1.H2: hypothesis H2 of reduction Erdos39.erdos_39.R1
-- Credit: @ivillar

/-!
Compactness for finite Sidon prefixes: the indicator functions of the finite sets `B K` have a
cluster point `g` in the compact space `ℕ → Bool`; every finite window of `g` agrees with
`B K` for arbitrarily large `K`, so `{i | g i}` is Sidon and has the required counts.
-/
namespace F2E39

theorem compact : ∀ f : ℕ → ℕ, (∀ k, ∃ n, k ≤ f n) →
    (∀ K : ℕ, ∃ B : Finset ℕ, IsSidon (B : Set ℕ) ∧
      ∀ n ≤ K, f n ≤ ((Set.Icc 1 n) ∩ (B : Set ℕ)).ncard) →
    ∃ A : Set ℕ, A.Infinite ∧ IsSidon A ∧ ∀ n, f n ≤ ((Set.Icc 1 n) ∩ A).ncard := by
  intro f hf h
  classical
  choose B hBS hBf using h
  obtain ⟨g, hg⟩ := exists_clusterPt_of_compactSpace
    (Filter.map (fun K : ℕ => (fun i : ℕ => decide (i ∈ B K))) Filter.atTop)
  have key : ∀ N M : ℕ, ∃ K ≥ M, ∀ i ≤ N, decide (i ∈ B K) = g i := by
    intro N M
    have hU : {h : ℕ → Bool | ∀ i ≤ N, h i = g i} ∈ nhds g := by
      have hpi := set_pi_mem_nhds (Set.finite_Iic N)
        (fun i _ => (show ({g i} : Set Bool) ∈ nhds (g i) from by simp))
      refine Filter.mem_of_superset hpi ?_
      intro h hh i hi
      exact hh i hi
    have hfr := hg.frequently hU
    rw [Filter.frequently_map, Filter.frequently_atTop] at hfr
    exact hfr M
  have hcount : ∀ n, f n ≤ ((Set.Icc 1 n) ∩ {i | g i = true}).ncard := by
    intro n
    obtain ⟨K, hK, hag⟩ := key n n
    have h1 := hBf K n hK
    have hset : Set.Icc 1 n ∩ {i | g i = true} = Set.Icc 1 n ∩ (B K : Set ℕ) := by
      ext i
      constructor
      · rintro ⟨hi, hgi⟩
        exact ⟨hi, Finset.mem_coe.mpr (of_decide_eq_true ((hag i hi.2).trans hgi))⟩
      · rintro ⟨hi, hmem⟩
        exact ⟨hi, (hag i hi.2).symm.trans (decide_eq_true (Finset.mem_coe.mp hmem))⟩
    rw [hset]
    exact h1
  refine ⟨{i | g i = true}, ?_, ?_, hcount⟩
  · intro hfin
    obtain ⟨n, hn⟩ := hf (({i | g i = true} : Set ℕ).ncard + 1)
    have h1 := hcount n
    have h2 : ((Set.Icc 1 n) ∩ {i | g i = true}).ncard ≤ ({i | g i = true} : Set ℕ).ncard :=
      Set.ncard_le_ncard Set.inter_subset_right hfin
    omega
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
    obtain ⟨K, -, hag⟩ := key (max (max i₁ j₁) (max i₂ j₂)) 0
    have mem : ∀ i, i ≤ max (max i₁ j₁) (max i₂ j₂) → g i = true → i ∈ (B K : Set ℕ) :=
      fun i hi hgi => Finset.mem_coe.mpr (of_decide_eq_true ((hag i hi).trans hgi))
    exact hBS K i₁ (mem i₁ (by omega) hi₁) j₁ (mem j₁ (by omega) hj₁) i₂ (mem i₂ (by omega) hi₂)
      j₂ (mem j₂ (by omega) hj₂) hsum

end F2E39

theorem OMA.solution : OMA.R_Erdos39_erdos_39_R1.H2 :=
  F2E39.compact
