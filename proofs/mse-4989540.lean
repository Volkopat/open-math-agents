import OMAStatements.S_mse_4989540
import Mathlib

-- Problem: mse-4989540, a strictly increasing sequence of subsets of the integers, each a
-- finite union of cosets of nonzero subgroups.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Take S n to be the union of the cosets 2^j + 2^(j+1) Z for j <= n (the integers of 2-adic
-- valuation at most n). The chain is increasing, and 2^(n+1) lies in S (n+1) but not in S n.

open OMA.S_mse_4989540 in
theorem OMA.solution : type_of% @OMA.S_mse_4989540.main := by
  let C : ℕ → Finset (ℤ × ℤ) := fun n =>
    (Finset.range (n + 1)).image (fun j => ((2 : ℤ) ^ j, (2 : ℤ) ^ (j + 1)))
  have hC : ∀ n, ∀ c ∈ C n, c.2 ≠ 0 := by
    intro n c hc
    simp only [C, Finset.mem_image, Finset.mem_range] at hc
    obtain ⟨j, _, rfl⟩ := hc
    show (2 : ℤ) ^ (j + 1) ≠ 0
    positivity
  refine ⟨fun n => {x | ∃ c ∈ C n, c.2 ∣ x - c.1}, ?_, ?_, ?_⟩
  · refine strictMono_nat_of_lt_succ (fun n => ?_)
    have hle : ({x | ∃ c ∈ C n, c.2 ∣ x - c.1} : Set ℤ) ≤
        {x | ∃ c ∈ C (n + 1), c.2 ∣ x - c.1} := by
      rintro x ⟨c, hc, hdiv⟩
      refine ⟨c, ?_, hdiv⟩
      exact Finset.image_subset_image (Finset.range_mono (by omega)) hc
    have hnot : ¬ ({x | ∃ c ∈ C (n + 1), c.2 ∣ x - c.1} : Set ℤ) ≤
        {x | ∃ c ∈ C n, c.2 ∣ x - c.1} := by
      intro hsub
      have hmem : (2 : ℤ) ^ (n + 1) ∈ ({x | ∃ c ∈ C (n + 1), c.2 ∣ x - c.1} : Set ℤ) := by
        refine ⟨((2 : ℤ) ^ (n + 1), (2 : ℤ) ^ (n + 1 + 1)), ?_, ?_⟩
        · exact Finset.mem_image.mpr ⟨n + 1, Finset.mem_range.mpr (by omega), rfl⟩
        · simp
      obtain ⟨c, hc, hdiv⟩ := hsub hmem
      simp only [C, Finset.mem_image, Finset.mem_range] at hc
      obtain ⟨j, hj, rfl⟩ := hc
      have hdiv' : (2 : ℤ) ^ (j + 1) ∣ (2 : ℤ) ^ (n + 1) - (2 : ℤ) ^ j := hdiv
      have hpow : (2 : ℤ) ^ (j + 1) ∣ (2 : ℤ) ^ (n + 1) := pow_dvd_pow 2 (by omega)
      have h2 : (2 : ℤ) ^ (j + 1) ∣ (2 : ℤ) ^ j := by
        have h3 := dvd_sub hpow hdiv'
        rwa [sub_sub_cancel] at h3
      have hpos : (0 : ℤ) < (2 : ℤ) ^ j := by positivity
      have h4 := Int.le_of_dvd hpos h2
      have h5 : (2 : ℤ) ^ (j + 1) = 2 * (2 : ℤ) ^ j := by ring
      linarith
    exact lt_of_le_of_ne hle (fun heq => hnot heq.ge)
  · intro n
    exact ⟨C n, hC n, rfl⟩
  · intro n
    refine ⟨↑(C n), fun c hc => hC n c (Finset.mem_coe.mp hc), ?_⟩
    ext x
    simp
