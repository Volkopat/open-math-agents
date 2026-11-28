import Mathlib

/-!
# Simultaneous omissions by the two binary digit-sum maps

Amiram Eldar's conjecture in OEIS A227359 (2022). A242403 is the natural
density of binary self-numbers, the integers missed by k + digitSum(k).
-/
namespace OMA.S_oeis_a227359
open Filter Topology

def weight (k : ℕ) := k.bitIndices.length

def self (n : ℕ) := ¬ ∃ k : ℕ, k + weight k = n

def missed (n : ℕ) := self n ∧ ¬ ∃ k : ℕ, k - weight k = n

noncomputable def frequency (p : ℕ → Prop) (N : ℕ) : ℝ := by
  classical
  exact ((Finset.range N).filter p).card / (N : ℝ)

theorem main : ∃ c : ℝ, Tendsto (frequency self) atTop (𝓝 c) ∧
    Tendsto (frequency missed) atTop (𝓝 (c/2)) := by
  sorry

end OMA.S_oeis_a227359
