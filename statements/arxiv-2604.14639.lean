import Mathlib

/-!
# Unimodality and log-concavity of generalized Glasby-Paseman sequences

Seok Hyun Byun and Svetlana Poznanović, arXiv:2604.14639, Conjecture 1.1.
Source: https://arxiv.org/abs/2604.14639

For positive integers m, l and a positive real a, the sequence (1.4) is, for 0 ≤ r ≤ m,
  x_r = (∑_{i=0}^r (C(m,i) a^i)^l) / (∑_{i=0}^r (C(r,i) a^i)^l).
Conjecture 1.1:
(a) the sequence is unimodal for all m, l ∈ ℤ⁺ and a ∈ ℝ⁺;
(b) for l ∈ ℤ⁺ and a ∈ ℝ⁺ it is log-concave for all but finitely many m ∈ ℤ⁺;
(c) for l, a ∈ ℤ⁺ and m ≥ 2 it attains its unique maximum at an index r equal to one of
    ⌊(am+a+2)/(2a+1)⌋ - 1, ⌊(am+a+2)/(2a+1)⌋, ⌊(am+a+2)/(2a+1)⌋ + 1;
(d) for l ∈ ℤ⁺ and a ∈ ℝ⁺ the maximum value is asymptotically (ratio tending to 1 as m → ∞)
    l^(1/2)/√(2πm) · (1+2a)^(1/2)(1+a)a^((l-2)/2)/((1+a)^l - 1) · ((1+2a)/(1+a))^((m+1/2)l).
`main` states the four parts as a conjunction.

Unimodal means x_0 ≤ ⋯ ≤ x_j ≥ ⋯ ≥ x_m for some j; log-concave means x_i² ≥ x_{i-1}x_{i+1}
for 0 < i < m. The integer floor in (c) is natural-number division, and r lying in the three
consecutive values is written as c ≤ r + 1 ∧ r ≤ c + 1.

Known cases: l = 1, a = 1 (Glasby–Paseman), l = 1 (Byun–Poznanović, arXiv:2305.16631),
l = 2, a = 1 (this paper, Theorem 1.2). Searches found no proof of the general case. Exact
rational computation (a ∈ {1/10,…,50}, l ≤ 6, m ≤ 45) found no failure of (a) or (c); (d) was
checked numerically for several (l, a).
-/

namespace OMA.S_arxiv_2604_14639

open Filter Topology

/-- The `r`-th term of the sequence (1.4). -/
noncomputable def x (m l : ℕ) (a : ℝ) (r : ℕ) : ℝ :=
  (∑ i ∈ Finset.range (r + 1), ((m.choose i : ℝ) * a ^ i) ^ l) /
    ∑ i ∈ Finset.range (r + 1), ((r.choose i : ℝ) * a ^ i) ^ l

/-- The sequence `f 0, …, f m` is unimodal. -/
def Unimodal (f : ℕ → ℝ) (m : ℕ) : Prop :=
  ∃ j ≤ m, (∀ i < j, f i ≤ f (i + 1)) ∧ ∀ i, j ≤ i → i < m → f (i + 1) ≤ f i

/-- The sequence `f 0, …, f m` is log-concave. -/
def LogConcave (f : ℕ → ℝ) (m : ℕ) : Prop :=
  ∀ i, 0 < i → i < m → f (i - 1) * f (i + 1) ≤ f i ^ 2

/-- The maximum value of the sequence `x m l a 0, …, x m l a m`. -/
noncomputable def maxValue (m l : ℕ) (a : ℝ) : ℝ :=
  (Finset.range (m + 1)).sup' Finset.nonempty_range_add_one (x m l a)

/-- The conjectured asymptotic size of the maximum value. -/
noncomputable def asymptotic (m l : ℕ) (a : ℝ) : ℝ :=
  Real.sqrt l / Real.sqrt (2 * Real.pi * m) *
    ((1 + 2 * a) ^ (1 / 2 : ℝ) * (1 + a) * a ^ (((l : ℝ) - 2) / 2) / ((1 + a) ^ l - 1)) *
    ((1 + 2 * a) / (1 + a)) ^ (((m : ℝ) + 1 / 2) * l)

theorem main :
    (∀ m l : ℕ, 0 < m → 0 < l → ∀ a : ℝ, 0 < a → Unimodal (x m l a) m) ∧
    (∀ l : ℕ, 0 < l → ∀ a : ℝ, 0 < a → ∀ᶠ m in atTop, LogConcave (x m l a) m) ∧
    (∀ l a m : ℕ, 0 < l → 0 < a → 2 ≤ m →
      ∃ r ≤ m, (∀ s ≤ m, s ≠ r → x m l a s < x m l a r) ∧
        (a * m + a + 2) / (2 * a + 1) ≤ r + 1 ∧ r ≤ (a * m + a + 2) / (2 * a + 1) + 1) ∧
    (∀ l : ℕ, 0 < l → ∀ a : ℝ, 0 < a →
      Tendsto (fun m : ℕ => maxValue m l a / asymptotic m l a) atTop (𝓝 1)) := by
  sorry

end OMA.S_arxiv_2604_14639
