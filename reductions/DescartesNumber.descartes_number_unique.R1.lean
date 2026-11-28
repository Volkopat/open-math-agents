import FormalConjectures.Wikipedia.DescartesNumber

-- Reduction DescartesNumber.descartes_number_unique.R1 of the Descartes number uniqueness question
-- Credit: @marcusbuffett

/-!
# Descartes numbers: the square shape of the cofactor, and the open rest

A Descartes factorization is `(m, w)` with `w` composite, `m w` odd, `gcd(m, w) = 1` and
`σ(m) (w + 1) = 2 m w`.

* `H1` (classical, provable): in every Descartes factorization `m` is a perfect square and
  `w ≡ 1 (mod 4)`. Writing `w + 1 = 2 t` the equation becomes `σ(m) t = m w`, which is odd, so
  `σ(m)` and `t` are odd. An odd `m` with `σ(m)` odd is a square, because `σ(p^k)` has the parity
  of `k + 1` for odd `p` and `σ` is multiplicative.
* `H2` (open): every Descartes factorization with `m` a square and `w ≡ 1 (mod 4)` has product
  `198585576189`. This is the uniqueness question restricted to the shape forced by `H1`.

This is a classical necessary condition, not progress on the uniqueness question.
-/

namespace OMA.R_DescartesNumber_descartes_number_unique_R1

/-- Classical: the cofactor `m` is a square and `w ≡ 1 (mod 4)`. -/
def H1 : Prop :=
  ∀ m w : ℕ, DescartesNumber.IsDescartesFactorization m w → IsSquare m ∧ w % 4 = 1

/-- Open: uniqueness among factorizations of the shape given by `H1`. -/
def H2 : Prop :=
  ∀ m w : ℕ, DescartesNumber.IsDescartesFactorization m w → IsSquare m → w % 4 = 1 →
    m * w = DescartesNumber.descartesExample

theorem main : H1 → H2 → type_of% @DescartesNumber.descartes_number_unique := by
  intro h1 h2 n hn
  obtain ⟨m, w, rfl, h⟩ := hn
  exact h2 m w h (h1 m w h).1 (h1 m w h).2

end OMA.R_DescartesNumber_descartes_number_unique_R1
