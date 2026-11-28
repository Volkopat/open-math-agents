import Mathlib

/-!
# Erdős Problem 1220

Source: https://www.erdosproblems.com/1220
Credit: @mgv27

Let $\lambda$ be a singular cardinal such that both $\lambda$ and $\mathrm{cf}(\lambda)$ are
$\aleph_0$-inaccessible. Does\[\lambda \to (\lambda,\aleph_1)^2\]hold?

Formalization notes:
* Cardinals live in `Cardinal.{0}`; `λ` is the cardinality of an arbitrary `V : Type`.
* A cardinal `κ` is `ℵ₀`-inaccessible (as defined on the source page) if `μ ^ ℵ₀ < κ` for all
  `μ < κ`.
* "Singular" is: infinite and not regular (`ℵ₀ ≤ λ ∧ ¬ λ.IsRegular`); `cf(λ)` is
  `λ.ord.cof`.
* The partition relation `λ → (λ, ℵ₁)^2` is: for every 2-colouring of the pairs from a set `V`
  of size `λ` — encoded as a simple graph `G` on `V`, edges having the first colour — there is
  either a set of size `λ` all of whose pairs are edges, or a set of size `ℵ₁` none of whose
  pairs are edges.
* The source notes that the answer is positive under GCH or other additional assumptions; the
  question is whether it holds in ZFC. The simplest case is `λ = ℵ_{𝔠⁺}`, so the hypotheses are
  satisfiable in ZFC.
-/

namespace OMA.S_erdos_1220

open Cardinal

/-- `κ` is `ℵ₀`-inaccessible: `μ ^ ℵ₀ < κ` for every `μ < κ`. -/
def Aleph0Inaccessible (κ : Cardinal.{0}) : Prop :=
  ∀ μ : Cardinal.{0}, μ < κ → μ ^ ℵ₀ < κ

/-- The partition relation `#V → (#V, ℵ₁)^2`: every graph on `V` has a clique of size `#V` or
an independent set of size `ℵ₁`. -/
def Arrows (V : Type) : Prop :=
  ∀ G : SimpleGraph V, (∃ s : Set V, G.IsClique s ∧ #s = #V) ∨
    (∃ s : Set V, Gᶜ.IsClique s ∧ #s = ℵ₁)

/-- Erdős Problem 1220: if `λ` is singular and both `λ` and `cf(λ)` are `ℵ₀`-inaccessible, does
`λ → (λ, ℵ₁)^2` hold? -/
theorem main : ∀ V : Type, ℵ₀ ≤ #V → ¬ (#V).IsRegular → Aleph0Inaccessible (#V) →
    Aleph0Inaccessible (#V).ord.cof → Arrows V := by
  sorry

end OMA.S_erdos_1220
