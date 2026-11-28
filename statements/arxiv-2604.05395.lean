import Mathlib

namespace OMA.S_arxiv_2604_05395

/-- A finite poset `P` is *integral* (in the sense of Hibi 1987 and De Concini–Eisenbud–Procesi 1982)
if there exist a field `K`, a commutative `K`-algebra `R` that is an integral domain, and an embedding
`ι : P → R` making `R` a homogeneous algebra with straightening laws (ASL) on `P` over `K`:
1. (ASL-1) The standard monomials `ι(x₁) * ⋯ * ι(xₘ)` indexed by nondecreasing chains
   `x₁ ≤ ⋯ ≤ xₘ` in `P` form a `K`-basis of `R` (linearly independent and spanning `R`).
2. (ASL-2) For every incomparable pair `x, y ∈ P`, the product `ι x * ι y` lies in the `K`-linear
   span of degree-2 standard monomials `ι u * ι v` with `u ≤ v`, `u < x`, and `u < y`. -/
def IsIntegralPoset (P : Type) [Fintype P] [PartialOrder P] : Prop :=
  ∃ (K : Type) (_ : Field K) (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : Algebra K R)
    (ι : P → R),
    LinearIndependent K (fun l : { l : List P // l.Pairwise (· ≤ ·) } => (l.1.map ι).prod) ∧
    Submodule.span K (Set.range (fun l : { l : List P // l.Pairwise (· ≤ ·) } => (l.1.map ι).prod)) = ⊤ ∧
    ∀ x y : P, ¬ x ≤ y → ¬ y ≤ x →
      ι x * ι y ∈ Submodule.span K { r : R | ∃ u v : P, u ≤ v ∧ u < x ∧ u < y ∧ r = ι u * ι v }

/-- Conjecture (Hibi; disproved in arXiv:2604.05395):
Every finite modular lattice is integral. -/
theorem main :
    ∀ (P : Type) [Fintype P] [Lattice P], IsModularLattice P → IsIntegralPoset P := by
  sorry

end OMA.S_arxiv_2604_05395
