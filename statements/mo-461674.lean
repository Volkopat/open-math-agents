import Mathlib

/-!
# Common convex-order bounds at Wasserstein distance at most the original distance

Source: Fawen90, https://mathoverflow.net/questions/461674, CC BY-SA 4.0.
Credit: @connoranderson.

We use quantile coordinates on the uniform unit interval. Every probability law
on the real line admits a nondecreasing quantile there. The p-th power of the
Wasserstein distance of two laws is the integral of the p-th power of their
quantile difference. Output coordinates may be arbitrary: two variables on the
same unit interval display a coupling and hence an upper bound on its cost.
Equal means and comparison of all put prices characterize the convex order.
The constructed coupling has exactly the input quantile cost, giving g(d)=d.
-/

namespace OMA.S_mo_461674
open Set MeasureTheory
open scoped Interval

abbrev Moment (p : ℝ) (f : ℝ → ℝ) : Prop :=
  IntervalIntegrable f volume 0 1 ∧
  IntervalIntegrable (fun t => |f t| ^ p) volume 0 1

def below (f g : ℝ → ℝ) : Prop :=
  (∫ t in (0:ℝ)..1, f t) = (∫ t in (0:ℝ)..1, g t) ∧
  ∀ c : ℝ, (∫ t in (0:ℝ)..1, max (c - f t) 0) ≤
    (∫ t in (0:ℝ)..1, max (c - g t) 0)

theorem main : ∀ (p : ℝ), 1 ≤ p → ∀ (f g : ℝ → ℝ),
    MonotoneOn f (Ioo 0 1) → MonotoneOn g (Ioo 0 1) →
    Moment p f → Moment p g →
    (∫ t in (0:ℝ)..1, f t) = (∫ t in (0:ℝ)..1, g t) →
    ∃ l r : ℝ → ℝ, Moment p l ∧ Moment p r ∧
      below l f ∧ below l g ∧ below f r ∧ below g r ∧
      (∫ t in (0:ℝ)..1, |l t - r t| ^ p) =
      (∫ t in (0:ℝ)..1, |f t - g t| ^ p) := by
  sorry

end OMA.S_mo_461674
