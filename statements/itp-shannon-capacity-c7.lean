import Mathlib

/-!
# Shannon capacity of the 7-cycle

Source: Open problems in information theory (gokhanmergen),
https://github.com/gokhanmergen/information-theory-problems/blob/main/problems/shannon-capacity-c7.md
Credit: @Jott2121

The source: for a graph `G` let `α(G)` be its independence number and `G^⊠k` its `k`-fold strong
product; the Shannon (zero-error) capacity is `Θ(G) = lim_{k → ∞} α(G^⊠k)^{1/k}`. Determine
`Θ(C₇)`, and more generally `Θ(C_{2k+1})` for all odd cycles with `2k + 1 ≥ 7`. Known:
`Θ(C₅) = √5` and `Θ(G) ≤ ϑ(G)` for every graph (Lovász 1979), where for odd `n` the Lovász
number of the `n`-cycle is `ϑ(C_n) = n cos(π/n) / (1 + cos(π/n))` (Lovász 1979, Corollary 5).
No odd cycle of length at least 7 is known to have `Θ(C_n) = ϑ(C_n)`, nor `Θ(C_n) < ϑ(C_n)`.

Reading chosen. The source asks to determine a value and names no conjectured answer. Its own
Lean file (`lean/InfoTheory/Problems/ShannonCapacityC7.lean` in the same repository) states the
core question as the separation `Θ(C₇) < ϑ(C₇)`. We state that separation for every odd cycle of
length at least 7, as the source asks for all of them; a disproof (`OMA.disproof`) would show
`Θ(C_n) = ϑ(C_n)` for some odd `n ≥ 7`. For `C₇` alone the same separation is already in
formal-conjectures as `Green38.green_38.upper` (phrased with subsets of `𝔽₇ⁿ`); the statement
here is the general odd-cycle question, stated with Mathlib's graphs.

Conventions.
* The strong product: distinct `x, y : Fin k → V` are adjacent in `G^⊠k` when in every
  coordinate they are equal or adjacent in `G`.
* `Θ(G)` is defined as `sup_{k ≥ 1} α(G^⊠k)^{1/k}`. Because `α` is supermultiplicative on strong
  powers, Fekete's lemma shows that the limit in the source exists and equals this supremum
  (Shannon 1956); for a finite graph every term is at most `|V|`, so the supremum is finite.
* `cycleGraph n` is Mathlib's cycle on `Fin n`.
-/

namespace OMA.S_itp_shannon_capacity_c7

open SimpleGraph

/-- The `k`-fold strong power `G^⊠k` of a simple graph `G`. -/
def strongPow {V : Type*} (G : SimpleGraph V) (k : ℕ) : SimpleGraph (Fin k → V) where
  Adj x y := x ≠ y ∧ ∀ i, x i = y i ∨ G.Adj (x i) (y i)
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun i => (h.2 i).imp Eq.symm (fun a => a.symm)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The Shannon capacity `Θ(G) = sup_{k ≥ 1} α(G^⊠k)^{1/k}`. -/
noncomputable def shannonCapacity {V : Type*} (G : SimpleGraph V) : ℝ :=
  ⨆ k : ℕ, ((strongPow G (k + 1)).indepNum : ℝ) ^ ((1 : ℝ) / ((k : ℝ) + 1))

/-- The Lovász number of the odd cycle `C_n`: `n cos(π/n) / (1 + cos(π/n))`. -/
noncomputable def lovaszThetaOddCycle (n : ℕ) : ℝ :=
  (n : ℝ) * Real.cos (Real.pi / n) / (1 + Real.cos (Real.pi / n))

/-- For every odd cycle of length `2k + 1 ≥ 7`, the Shannon capacity is strictly below the
Lovász bound: `Θ(C_{2k+1}) < ϑ(C_{2k+1})`. -/
theorem main : ∀ k : ℕ, 3 ≤ k →
    shannonCapacity (cycleGraph (2 * k + 1)) < lovaszThetaOddCycle (2 * k + 1) := by
  sorry

end OMA.S_itp_shannon_capacity_c7
