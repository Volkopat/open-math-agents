import FormalConjectures.Arxiv.«2501.03234».ArithmeticSumS

-- Reduction Arxiv.2501.03234.conjecture_4_3.R1 of Conjecture 4.3 of arXiv 2501.03234
-- (B. C. Berndt, S. Bhat, J. L. Meyer, L. Xie, A. Zaharescu).
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# `S(p) > 3p` for primes `p > 3119`

The target says `3 * p < S p` for every prime `p > 3119`.

Let `M(p) = p * (sum of 1 / a over odd a < p)`. This is the main term of `S(p)` in the merged
reduction `Arxiv.2501.03234.conjecture_1_1.R1`, whose hypothesis `H2` says `M(p) ≤ 2 * S(p)` for
every prime `p ≥ 100000` (there `S(p)` is written as the floor sum `T(p)`).

* `H1` (finite computation): the target for the primes `3119 < p < 100000`.
* `H2` (open): the target for the primes `p ≥ 100000` with `2 * S(p) < M(p)`. This is a special
  case of the target. It holds vacuously if `M(p) ≤ 2 * S(p)` for every prime `p ≥ 100000`, which
  is `H2` of `Arxiv.2501.03234.conjecture_1_1.R1`. That is the deep input.

`main` proves the remaining case, a prime `p = 2 * n + 1 ≥ 100000` with `M(p) ≤ 2 * S(p)`. There
`M(p) = p * (1 + 1 / 3 + ... + 1 / (2 * n - 1))` and the odd harmonic sum exceeds `6`. The proof
of that bound: the tangent line of `1 / x` at `x = 3 * m` gives
`1 / (2 * m + 1) + ... + 1 / (4 * m - 1) ≥ 1 / 3`, so fourteen doublings from `1 + 1 / 3 + 1 / 5`
give `23 / 15 + 14 / 3 > 6` at `n = 49152`.
-/

open Finset

namespace OMA.R_Arxiv_2501_03234_conjecture_4_3_R1

/-- Finite range: `3 * p < S p` for every prime `3119 < p < 100000`. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → 3119 < p → p < 100000 → 3 * (p : ℤ) < Arxiv.«2501.03234».S p

/-- The target for the primes `p ≥ 100000` where `S p` is below half of the main term
`p * (sum of 1 / a over odd a < p)`. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → 100000 ≤ p →
    2 * ((Arxiv.«2501.03234».S p : ℤ) : ℚ) < ∑ a ∈ (Ico 1 p).filter Odd, (p : ℚ) / a →
      3 * (p : ℤ) < Arxiv.«2501.03234».S p

/-- The tangent line of `1 / x` at `c` lies below the graph. -/
lemma tangent (x c : ℚ) (hx : 0 < x) (hc : 0 < c) : 2 / c - x / c ^ 2 ≤ 1 / x := by
  have h : 2 / c - x / c ^ 2 = (2 * c - x) / c ^ 2 := by
    field_simp
  rw [h, div_le_div_iff₀ (by positivity) hx]
  nlinarith [sq_nonneg (x - c)]

lemma lin_sum (c : ℚ) (n : ℕ) :
    ∑ k ∈ range n, (2 * (c + k) + 1) = 2 * c * n + (n : ℚ) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- The odd harmonic sum over the block `m ≤ k < 2 * m` is at least `1 / 3`. -/
lemma block (m : ℕ) (hm : 0 < m) :
    (1 : ℚ) / 3 ≤ ∑ k ∈ range m, (1 : ℚ) / (2 * ((m + k : ℕ) : ℚ) + 1) := by
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have h1 : ∀ k ∈ range m,
      2 / (3 * (m : ℚ)) - (2 * ((m : ℚ) + k) + 1) / (3 * (m : ℚ)) ^ 2 ≤
        (1 : ℚ) / (2 * ((m + k : ℕ) : ℚ) + 1) := by
    intro k _
    have h := tangent (2 * ((m : ℚ) + k) + 1) (3 * m) (by positivity) (by positivity)
    push_cast
    exact h
  have h2 := sum_le_sum h1
  rw [sum_sub_distrib, ← sum_div, ← sum_div, lin_sum, sum_const, card_range, nsmul_eq_mul] at h2
  have h3 : (m : ℚ) * 2 / (3 * (m : ℚ)) - (2 * (m : ℚ) * m + (m : ℚ) ^ 2) / (3 * (m : ℚ)) ^ 2 =
      1 / 3 := by
    field_simp
    ring
  linarith

lemma harm_pow (j : ℕ) :
    (23 : ℚ) / 15 + (j : ℚ) / 3 ≤ ∑ k ∈ range (3 * 2 ^ j), (1 : ℚ) / (2 * (k : ℚ) + 1) := by
  induction j with
  | zero => norm_num [sum_range_succ]
  | succ j ih =>
    rw [show 3 * 2 ^ (j + 1) = 3 * 2 ^ j + 3 * 2 ^ j by ring, sum_range_add]
    have hb := block (3 * 2 ^ j) (by positivity)
    have hc : ((j + 1 : ℕ) : ℚ) = (j : ℚ) + 1 := by push_cast; ring
    rw [hc]
    linarith

lemma harm_mono (N n : ℕ) (hn : N ≤ n) :
    ∑ k ∈ range N, (1 : ℚ) / (2 * (k : ℚ) + 1) ≤ ∑ k ∈ range n, (1 : ℚ) / (2 * (k : ℚ) + 1) :=
  sum_le_sum_of_subset_of_nonneg (range_mono hn) (fun k _ _ => by positivity)

/-- The odd harmonic sum with at least `49152` terms exceeds `6`. -/
lemma harm_big (n : ℕ) (hn : 3 * 2 ^ 14 ≤ n) :
    (6 : ℚ) < ∑ k ∈ range n, (1 : ℚ) / (2 * (k : ℚ) + 1) := by
  have h := harm_pow 14
  generalize 3 * 2 ^ 14 = N at h hn
  have hmono := harm_mono N n hn
  have h6 : (6 : ℚ) < 23 / 15 + ((14 : ℕ) : ℚ) / 3 := by norm_num
  linarith

lemma split_rows (f : ℕ → ℚ) (n : ℕ) :
    ∑ a ∈ Ico 1 (2 * n + 1), f a =
      (∑ k ∈ range n, f (2 * k + 1)) + ∑ k ∈ range n, f (2 * k + 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by ring, sum_Ico_succ_top (by omega),
      sum_Ico_succ_top (by omega), ih, sum_range_succ, sum_range_succ]
    ac_rfl

/-- The main term as a multiple of the odd harmonic sum. -/
lemma odd_sum (n : ℕ) :
    ∑ a ∈ (Ico 1 (2 * n + 1)).filter Odd, ((2 * n + 1 : ℕ) : ℚ) / a =
      ((2 * n + 1 : ℕ) : ℚ) * ∑ k ∈ range n, (1 : ℚ) / (2 * (k : ℚ) + 1) := by
  rw [sum_filter, split_rows]
  have odd1 (k : ℕ) : Odd (2 * k + 1) := ⟨k, rfl⟩
  have even2 (k : ℕ) : ¬ Odd (2 * k + 2) := by rintro ⟨t, ht⟩; omega
  simp only [odd1, even2, if_true, if_false, sum_const_zero, add_zero]
  rw [mul_sum]
  apply sum_congr rfl
  intro k _
  push_cast
  ring

theorem main : H1 → H2 → type_of% @Arxiv.«2501.03234».conjecture_4_3 := by
  intro h1 h2 k hk hodd hgt
  by_cases hlt : k < 100000
  · exact h1 k hk hgt hlt
  · have hbig : 100000 ≤ k := by omega
    by_cases hex : 2 * ((Arxiv.«2501.03234».S k : ℤ) : ℚ) <
        ∑ a ∈ (Ico 1 k).filter Odd, (k : ℚ) / a
    · exact h2 k hk hbig hex
    · rw [not_lt] at hex
      obtain ⟨n, rfl⟩ := hodd
      rw [odd_sum] at hex
      have hh := harm_big n (by norm_num; omega)
      have hP : (0 : ℚ) < ((2 * n + 1 : ℕ) : ℚ) := by positivity
      have h3 : 3 * ((2 * n + 1 : ℕ) : ℚ) < ((Arxiv.«2501.03234».S (2 * n + 1) : ℤ) : ℚ) := by
        have h4 := mul_lt_mul_of_pos_left hh hP
        linarith
      exact_mod_cast h3

end OMA.R_Arxiv_2501_03234_conjecture_4_3_R1
