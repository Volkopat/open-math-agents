import Mathlib

namespace OMA.S_arxiv_2608_07262

/-- A polynomial `f ∈ K[X]` over a finite field `K` is primitive if it is monic, irreducible,
and its root in `AdjoinRoot f` has multiplicative order `|K|^(deg f) - 1`. -/
def IsPrimitivePoly {K : Type} [Field K] [Fintype K] (f : Polynomial K) : Prop :=
  f.Monic ∧ Irreducible f ∧
    orderOf (AdjoinRoot.root f) = (Fintype.card K) ^ f.natDegree - 1

/-- Conjecture 1.2 of Awasthi and Sharma (disproved in arXiv:2608.07262, "Primitive Polynomials
of the Form `g(x)+λ` over Finite Fields: Non-Existence Results and Conjectures"): for every
finite field `K` of cardinality `q^2` (`q = p^r` a prime power), there exists a primitive element
`α ∈ K` (i.e., `orderOf α = |K| - 1`) such that `X^3 + X^2 + X + α` is a primitive polynomial
over `K`. -/
theorem main :
    ∀ (K : Type) [Field K] [Fintype K] (p r : ℕ),
      Nat.Prime p → 1 ≤ r → Fintype.card K = (p ^ r) ^ 2 →
      ∃ α : K, orderOf α = Fintype.card K - 1 ∧
        IsPrimitivePoly (Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + Polynomial.C α) := by
  sorry

end OMA.S_arxiv_2608_07262
