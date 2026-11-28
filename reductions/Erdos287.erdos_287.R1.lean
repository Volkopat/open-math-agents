import FormalConjectures.ErdosProblems.«287»
import Mathlib

-- Reduction Erdos287.erdos_287.R1 of Erdős Problem 287: if 1 < n_1 < ... < n_k (k ≥ 2) and
-- 1/n_1 + ... + 1/n_k = 1, is the largest gap n_{i+1} - n_i at least 3?
-- Credit: @marcusbuffett
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- This is a classical slice, not progress on the conjecture itself. H1 is Erdős's 1932 theorem
-- that the largest gap is at least 2, that is, 1 is never the sum of the reciprocals of two or
-- more consecutive integers greater than 1 (the catalogue records it as
-- erdos_287.variants.gap_at_least_two). A short run sums to less than 1, and a long run
-- n, ..., m has m ≥ 2n, so a power of two lies in it and the 2-adic valuations of the harmonic
-- numbers H(m) and H(n - 1) + 1 disagree. H2, that no representation of 1 has largest gap exactly
-- 2, carries the whole open difficulty.

namespace OMA.R_Erdos287_erdos_287_R1

open Erdos287

/-- Erdős (1932): the largest gap of an Egyptian-fraction representation of 1 is at least 2. -/
def H1 : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) (s : Fin k → ℕ),
    StrictMono s → 1 < s ⟨0, by omega⟩ →
    ∑ i : Fin k, 1 / (s i : ℝ) = 1 →
    2 ≤ max_gap k s

/-- No Egyptian-fraction representation of 1 has largest gap exactly 2 (open). -/
def H2 : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) (s : Fin k → ℕ),
    StrictMono s → 1 < s ⟨0, by omega⟩ →
    ∑ i : Fin k, 1 / (s i : ℝ) = 1 →
    max_gap k s ≠ 2

theorem main : H1 → H2 → type_of% @Erdos287.erdos_287 := by
  intro h1 h2 k hk s hs h0 hsum
  have a := h1 k hk s hs h0 hsum
  have b := h2 k hk s hs h0 hsum
  omega

end OMA.R_Erdos287_erdos_287_R1
