import Mathlib

/-!
# Log-Sobolev inequality for Lebesgue measure on $[0, 1]$

Source: https://math.stackexchange.com/questions/4948679/is-there-a-log-sobolev-inequality-for-lebesgue-measure-on-0-1-on-compact-sub
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Is there a universal constant $C > 0$ such that
$$\int_0^1 f(x)^2 \log(f(x)^2) \, dx \le C \int_0^1 |f'(x)|^2 \, dx$$
for all weakly differentiable $f \in W^{1,2}([0, 1])$ satisfying $\int_0^1 f(x)^2 \, dx = 1$,
where $dx$ is Lebesgue measure on $[0, 1]$?

Conventions:
- Weak differentiability in $W^{1,2}([0, 1])$ is expressed via absolute continuity: there
  exists $f' \in L^2([0, 1])$ such that $f(x) - f(0) = \int_0^x f'(t) \, dt$ for all
  $x \in [0, 1]$.
- Mathlib's `Real.log 0 = 0` matches the standard convention $0 \log 0 = 0$.
-/

namespace OMA.S_mse_4948679

open MeasureTheory

theorem main :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f f' : ℝ → ℝ),
        IntervalIntegrable (fun x => (f' x) ^ 2) volume 0 1 →
        (∀ x ∈ Set.Icc (0 : ℝ) 1, f x - f 0 = ∫ t in (0 : ℝ)..x, f' t) →
        (∫ x in (0 : ℝ)..1, (f x) ^ 2) = 1 →
        (∫ x in (0 : ℝ)..1, (f x) ^ 2 * Real.log ((f x) ^ 2)) ≤
          C * (∫ x in (0 : ℝ)..1, (f' x) ^ 2) := by
  sorry

end OMA.S_mse_4948679
