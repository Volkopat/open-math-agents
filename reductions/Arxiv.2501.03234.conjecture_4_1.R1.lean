import FormalConjectures.Arxiv.«2501.03234».ArithmeticSumS
import Mathlib

-- Reduction Arxiv.2501.03234.conjecture_4_1.R1 of Conjecture 4.1
-- Credit: @rickmanelius
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# `S(p) > p` for primes `p > 5`

The target says `p < S p` for every prime `p > 5`.

Let `M(p) = p * (sum of 1 / a over odd a < p)`. The merged reduction
`Arxiv.2501.03234.conjecture_1_1.R1` isolates, as its hypothesis `H2`, the deep lower bound
`M(p) ≤ 2 S(p)` for every prime `p ≥ 100000` (there `S(p)` is written as an explicit floor sum).
The merged reduction `Arxiv.2501.03234.conjecture_4_3.R1` uses the same main term.

This file proves, with no hypothesis, that the odd harmonic sum `1 + 1/3 + ... + 1/23` already
exceeds `2`, so `M(p) > 2 p` for every odd `p ≥ 25`. Hence the target holds for every prime
`p ≥ 100000` with `M(p) ≤ 2 S(p)`.

What is left:

* `H1` (finite computation): the target for the primes `5 < p < 100000`;
* `H2`: the target for the primes `p ≥ 100000` with `2 S(p) < M(p)`. This is a special case of
  the target, and it holds vacuously under `H2` of `Arxiv.2501.03234.conjecture_1_1.R1`.
-/

open Finset

namespace OMA.R_Arxiv_2501_03234_conjecture_4_1_R1

/-- Finite range: `p < S p` for every prime `5 < p < 100000`. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → 5 < p → p < 100000 → (p : ℤ) < Arxiv.«2501.03234».S p

/-- The target for the primes `p ≥ 100000` where `2 S(p)` is below the main term
`p * (sum of 1 / a over odd a < p)`. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → 100000 ≤ p →
    2 * ((Arxiv.«2501.03234».S p : ℤ) : ℚ) < ∑ a ∈ (Ico 1 p).filter Odd, (p : ℚ) / a →
      (p : ℤ) < Arxiv.«2501.03234».S p

/-- The odd numbers in `[1, 2 n]` are the `2 k + 1` with `k < n`. -/
lemma odd_filter_eq (n : ℕ) :
    (Ico 1 (2 * n + 1)).filter Odd = (range n).image (fun k => 2 * k + 1) := by
  ext a
  simp only [mem_filter, mem_Ico, mem_image, mem_range]
  constructor
  · rintro ⟨⟨-, ha⟩, ⟨k, rfl⟩⟩
    exact ⟨k, by omega, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨by omega, by omega⟩, ⟨k, rfl⟩⟩

/-- The main term `M(2 n + 1)` is `(2 n + 1)` times the odd harmonic sum with `n` terms. -/
lemma main_term (n : ℕ) :
    ∑ a ∈ (Ico 1 (2 * n + 1)).filter Odd, ((2 * n + 1 : ℕ) : ℚ) / a =
      ((2 * n + 1 : ℕ) : ℚ) * ∑ k ∈ range n, (1 : ℚ) / (2 * (k : ℚ) + 1) := by
  rw [odd_filter_eq, sum_image (fun x _ y _ h => by omega), mul_sum]
  apply sum_congr rfl
  intro k _
  push_cast
  ring

/-- `1 + 1/3 + ... + 1/23 > 2`, so the odd harmonic sum with at least `12` terms exceeds `2`. -/
lemma odd_harmonic_gt_two (n : ℕ) (hn : 12 ≤ n) :
    (2 : ℚ) < ∑ k ∈ range n, (1 : ℚ) / (2 * (k : ℚ) + 1) := by
  have h12 : (2 : ℚ) < ∑ k ∈ range 12, (1 : ℚ) / (2 * (k : ℚ) + 1) := by
    norm_num [sum_range_succ]
  have hmono : ∑ k ∈ range 12, (1 : ℚ) / (2 * (k : ℚ) + 1) ≤
      ∑ k ∈ range n, (1 : ℚ) / (2 * (k : ℚ) + 1) :=
    sum_le_sum_of_subset_of_nonneg (range_mono hn) (fun k _ _ => by positivity)
  linarith

theorem main : H1 → H2 → type_of% @Arxiv.«2501.03234».conjecture_4_1 := by
  intro h1 h2 k hk hodd hgt
  by_cases hlt : k < 100000
  · exact h1 k hk hgt hlt
  · have hbig : 100000 ≤ k := by omega
    by_cases hex : 2 * ((Arxiv.«2501.03234».S k : ℤ) : ℚ) <
        ∑ a ∈ (Ico 1 k).filter Odd, (k : ℚ) / a
    · exact h2 k hk hbig hex
    · rw [not_lt] at hex
      obtain ⟨n, rfl⟩ := hodd
      rw [main_term] at hex
      have hh := odd_harmonic_gt_two n (by omega)
      have hP : (0 : ℚ) < ((2 * n + 1 : ℕ) : ℚ) := by positivity
      have h3 : ((2 * n + 1 : ℕ) : ℚ) < ((Arxiv.«2501.03234».S (2 * n + 1) : ℤ) : ℚ) := by
        have h4 := mul_lt_mul_of_pos_left hh hP
        linarith
      exact_mod_cast h3

end OMA.R_Arxiv_2501_03234_conjecture_4_1_R1
