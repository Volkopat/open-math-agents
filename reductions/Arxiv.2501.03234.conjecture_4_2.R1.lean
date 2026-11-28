import FormalConjectures.Arxiv.«2501.03234».ArithmeticSumS
import Mathlib

-- Reduction Arxiv.2501.03234.conjecture_4_2.R1 of Conjecture 4.2
-- Credit: @rickmanelius
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# `S(p) > 2 p` for primes `p > 233`

The target says `2 * p < S p` for every prime `p > 233`.

Let `M(p) = p * (sum of 1 / a over odd a < p)`. The merged reduction
`Arxiv.2501.03234.conjecture_1_1.R1` isolates, as its hypothesis `H2`, the deep lower bound
`M(p) ≤ 2 S(p)` for every prime `p ≥ 100000` (there `S(p)` is written as an explicit floor sum).
The merged reductions of Conjectures 4.1 and 4.3 use the same main term.

This file proves, with no hypothesis, that the odd harmonic sum
`1 + 1/3 + ... + 1/(2 n - 1)` exceeds `4` once `n ≥ 3 * 2 ^ 10`: the first three terms give
`23 / 15`, and each block of `m` consecutive terms starting at index `m` adds at least
`m * 1 / (4 m) = 1 / 4`, since every such term is at least `1 / (4 m)`. Hence `M(p) > 4 p` for
every odd `p ≥ 6145`, and the target holds for every prime `p ≥ 100000` with `M(p) ≤ 2 S(p)`.

What is left:

* `H1` (finite computation): the target for the primes `233 < p < 100000`;
* `H2`: the target for the primes `p ≥ 100000` with `2 S(p) < M(p)`. This is a special case of
  the target, and it holds vacuously under `H2` of `Arxiv.2501.03234.conjecture_1_1.R1`.
-/

open Finset

namespace OMA.R_Arxiv_2501_03234_conjecture_4_2_R1

/-- Finite range: `2 p < S p` for every prime `233 < p < 100000`. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → 233 < p → p < 100000 → 2 * (p : ℤ) < Arxiv.«2501.03234».S p

/-- The target for the primes `p ≥ 100000` where `2 S(p)` is below the main term
`p * (sum of 1 / a over odd a < p)`. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → 100000 ≤ p →
    2 * ((Arxiv.«2501.03234».S p : ℤ) : ℚ) < ∑ a ∈ (Ico 1 p).filter Odd, (p : ℚ) / a →
      2 * (p : ℤ) < Arxiv.«2501.03234».S p

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

/-- A block of `m` consecutive terms of the odd harmonic sum, starting at index `m`, is at least
`1 / 4`: each term `1 / (2 (m + k) + 1)` with `k < m` is at least `1 / (4 m)`. -/
lemma block_ge_quarter (m : ℕ) (hm : 0 < m) :
    (1 : ℚ) / 4 ≤ ∑ k ∈ range m, (1 : ℚ) / (2 * ((m + k : ℕ) : ℚ) + 1) := by
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have hterm : ∀ k ∈ range m, (1 : ℚ) / (4 * m) ≤ (1 : ℚ) / (2 * ((m + k : ℕ) : ℚ) + 1) := by
    intro k hk
    have hk' : (k : ℚ) + 1 ≤ m := by
      have := mem_range.mp hk
      exact_mod_cast this
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    linarith
  have hsum := sum_le_sum hterm
  rw [sum_const, card_range, nsmul_eq_mul] at hsum
  have h4 : (m : ℚ) * (1 / (4 * m)) = 1 / 4 := by
    field_simp
  linarith

/-- Doubling: the odd harmonic sum with `3 * 2 ^ j` terms is at least `23 / 15 + j / 4`. -/
lemma odd_harmonic_doubling (j : ℕ) :
    (23 : ℚ) / 15 + (j : ℚ) / 4 ≤ ∑ k ∈ range (3 * 2 ^ j), (1 : ℚ) / (2 * (k : ℚ) + 1) := by
  induction j with
  | zero => norm_num [sum_range_succ]
  | succ j ih =>
    rw [show 3 * 2 ^ (j + 1) = 3 * 2 ^ j + 3 * 2 ^ j by ring, sum_range_add]
    have hb := block_ge_quarter (3 * 2 ^ j) (by positivity)
    have hc : ((j + 1 : ℕ) : ℚ) = (j : ℚ) + 1 := by push_cast; ring
    rw [hc]
    have hb' : (1 : ℚ) / 4 ≤ ∑ k ∈ range (3 * 2 ^ j),
        (1 : ℚ) / (2 * ((3 * 2 ^ j + k : ℕ) : ℚ) + 1) := hb
    simp only [Nat.cast_add] at hb'
    linarith

/-- The odd harmonic sum with at least `3 * 2 ^ 10 = 3072` terms exceeds `4`. -/
lemma odd_harmonic_gt_four (n : ℕ) (hn : 3 * 2 ^ 10 ≤ n) :
    (4 : ℚ) < ∑ k ∈ range n, (1 : ℚ) / (2 * (k : ℚ) + 1) := by
  have h := odd_harmonic_doubling 10
  generalize hN : 3 * 2 ^ 10 = N at h hn
  have hmono : ∑ k ∈ range N, (1 : ℚ) / (2 * (k : ℚ) + 1) ≤
      ∑ k ∈ range n, (1 : ℚ) / (2 * (k : ℚ) + 1) :=
    sum_le_sum_of_subset_of_nonneg (range_mono hn) (fun k _ _ => by positivity)
  have h4 : (4 : ℚ) < 23 / 15 + ((10 : ℕ) : ℚ) / 4 := by norm_num
  linarith

theorem main : H1 → H2 → type_of% @Arxiv.«2501.03234».conjecture_4_2 := by
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
      have hh := odd_harmonic_gt_four n (by norm_num; omega)
      have hP : (0 : ℚ) < ((2 * n + 1 : ℕ) : ℚ) := by positivity
      have h3 : 2 * ((2 * n + 1 : ℕ) : ℚ) <
          ((Arxiv.«2501.03234».S (2 * n + 1) : ℤ) : ℚ) := by
        have h4 := mul_lt_mul_of_pos_left hh hP
        linarith
      exact_mod_cast h3

end OMA.R_Arxiv_2501_03234_conjecture_4_2_R1
