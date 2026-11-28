import Mathlib

/-!
# Morton–Silverman uniform boundedness conjecture

Source: https://en.wikipedia.org/wiki/Arithmetic_dynamics
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Morton–Silverman): for every `d ≥ 2` and `D ≥ 1` there is a constant `C(d, D)` such
that every rational map `φ` of degree `d` on `ℙ¹` defined over a number field `K` of degree `D`
has at most `C(d, D)` `K`-rational preperiodic points.

Conventions:
* `ℙ¹(K)` is `Option K` (`none` is the point at infinity). A rational map of degree `d` over `K`
  is `φ = p / q` with `p, q ∈ K[X]` coprime and `max (deg p) (deg q) = d`. It acts on `ℙ¹(K)` by
  `x ↦ p(x)/q(x)` when `q(x) ≠ 0` and `x ↦ ∞` when `q(x) = 0`; at infinity, `∞ ↦ ∞` if
  `deg p > deg q`, `∞ ↦ lc(p)/lc(q)` if the degrees are equal, and `∞ ↦ 0` if `deg p < deg q`.
* A point `P` is preperiodic if its forward orbit is finite, i.e. `φ^[m] P = φ^[m+k] P` for some
  `m` and `k ≥ 1`.
* Number fields of degree `D` over `ℚ`; the constant depends only on `d` and `D`.
-/

namespace OMA.S_wpc_morton_silverman

open Polynomial

open Classical in
/-- The action on `ℙ¹(K) = Option K` of the rational map `p / q`. -/
noncomputable def act {K : Type} [Field K] (p q : K[X]) : Option K → Option K
  | some x => if q.eval x = 0 then none else some (p.eval x / q.eval x)
  | none =>
      if q.natDegree < p.natDegree then none
      else if p.natDegree = q.natDegree then some (p.leadingCoeff / q.leadingCoeff)
      else some 0

/-- `P` is a preperiodic point of `f`. -/
def IsPreperiodic {α : Type} (f : α → α) (P : α) : Prop :=
  ∃ m k : ℕ, 0 < k ∧ f^[m] P = f^[m + k] P

theorem main :
    ∀ d D : ℕ, 2 ≤ d → 1 ≤ D → ∃ C : ℕ,
      ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = D →
        ∀ p q : K[X], IsCoprime p q → max p.natDegree q.natDegree = d →
          {P : Option K | IsPreperiodic (act p q) P}.ncard ≤ C ∧
            {P : Option K | IsPreperiodic (act p q) P}.Finite := by
  sorry

end OMA.S_wpc_morton_silverman
