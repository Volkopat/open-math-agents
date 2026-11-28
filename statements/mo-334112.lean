import Mathlib

/-!
# How much of the mean of a Bernoulli sum survives truncation?

Source: Melika, https://mathoverflow.net/questions/334112 (2019).
Formalization: Hengzhi He (@hehz2020), assisted by Codex.

The question asks for a positive lower bound depending only on the cap and a
strict upper bound on the overflow probability. The summands are Bernoulli
and may have different parameters. The question does not assume independence.
We use the distribution of their sum, since this determines all three quantities.
Every Bernoulli sum has a finitely supported law on the natural numbers.
Conversely, if a random count has finite support with maximum N, it is the
sum of its N Bernoulli indicators for reaching levels 1 through N.
The positive mean condition ensures the ratio in the question is defined.
-/

namespace OMA.S_mo_334112

def expect (s : Finset ℕ) (w : ℕ → ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑ x ∈ s, w x * f x

theorem main : ∀ k : ℕ, 0 < k → ∀ α : ℝ, 0 < α → α ≤ 1 →
    ∃ c : ℝ, 0 < c ∧ ∀ (s : Finset ℕ) (w : ℕ → ℝ),
      (∀ x ∈ s, 0 ≤ w x) → ∑ x ∈ s, w x = 1 →
      0 < expect s w (fun x => (x : ℝ)) →
      expect s w (fun x => if k < x then 1 else 0) < α →
      c * expect s w (fun x => (x : ℝ)) ≤
        expect s w (fun x => (min x k : ℕ)) := by
  sorry

end OMA.S_mo_334112
