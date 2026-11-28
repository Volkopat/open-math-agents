import Mathlib

/-!
# The additive basis conjecture

Source: https://www.openproblemgarden.org/op/the_additive_basis_conjecture
Credit: @ishaanzee

**Conjecture** (Jaeger, Linial, Payan, Tarsi). For every prime `p`, there is a constant `c(p)`
(possibly `c(p) = p`) so that the union (as multisets) of any `c(p)` bases of the vector space
`(ℤ_p)^n` contains an additive basis.

Definition: a multiset `B` of elements of a finite-dimensional vector space `V` over `ℤ_p` is an
additive basis if for every `v ∈ V` there is a subset of `B` which sums to `v`.

Formalization:
* `c(p)` may depend on `p` only, not on `n`: `∃ c, ∀ n, …`.
* The vector space is `Fin n → ZMod p`; a basis of it is a `Module.Basis (Fin n) (ZMod p) _` (every
  basis has `n` elements, so indexing by `Fin n` loses nothing). The `c` bases are
  `b : Fin c → Module.Basis …`, and their multiset union has the elements `b i j` indexed by
  `(i, j) : Fin c × Fin n`.
* A sub-multiset of the union is a `Finset (Fin c × Fin n)` of indices. Since any multiset
  containing an additive basis is itself an additive basis, "the union contains an additive
  basis" is the same as "the union is an additive basis": every vector is the sum of the elements
  indexed by some finite set of indices.
-/

namespace OMA.S_opg_the_additive_basis_conjecture

/-- **Additive basis conjecture**: for every prime `p` there is `c` such that, for every `n`, the
multiset union of any `c` bases of `(ℤ_p)^n` is an additive basis. -/
theorem main : ∀ p : ℕ, p.Prime → ∃ c : ℕ, ∀ (n : ℕ)
    (b : Fin c → Module.Basis (Fin n) (ZMod p) (Fin n → ZMod p)) (v : Fin n → ZMod p),
      ∃ S : Finset (Fin c × Fin n), ∑ x ∈ S, b x.1 x.2 = v := by
  sorry

end OMA.S_opg_the_additive_basis_conjecture
