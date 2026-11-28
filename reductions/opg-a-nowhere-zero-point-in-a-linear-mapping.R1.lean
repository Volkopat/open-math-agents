import OMAStatements.S_opg_a_nowhere_zero_point_in_a_linear_mapping

/-!
# Reduction opg-a-nowhere-zero-point-in-a-linear-mapping.R1 of Jaeger's conjecture

The problem (statements/opg-a-nowhere-zero-point-in-a-linear-mapping.lean) is Jaeger's
conjecture: for every finite field `F` with at least four elements and every invertible square
matrix `A` over `F` there are vectors `x`, `y` with no zero coordinates and `A x = y`.

History of the problem, so that nobody has to rediscover it:
* F. Jaeger (1989), originally for `|F| = 5` only.
* N. Alon, M. Tarsi, *A nowhere-zero point in linear mappings*, Combinatorica 9 (1989),
  393-395: proved for every field order `q` that is not prime, i.e. `q = p^k` with `k >= 2`.
* T. Honold, U. Schauz, *Transformation invariance in the Combinatorial Nullstellensatz and
  nowhere-zero points of non-singular matrices*, Discrete Math. (2023): a new proof for
  non-prime `q`, and an extension from fields to rings; the prime-order case is not covered.
* The Open Problem Garden page records the same state of the art: the open case is that of
  PRIME fields (`q = p`); Yu checked `Z_p` for small `n`.

This file splits the statement into the two cases, which is exactly the split the source
records: `H1` is the open prime-order case and `H2` is the Alon-Tarsi theorem for non-prime
order. Proving `H1` and `H2` closes the problem; in particular `H2` is a published theorem and
is a self-contained target, while `H1` is the open conjecture.

Why the case distinction is the natural one: a finite field has `p^k` elements, so
`not (Nat.Prime (Fintype.card F))` together with `4 <= Fintype.card F` is precisely the
Alon-Tarsi regime `q = p^k`, `k >= 2` (and `q != 2, 3`).

Note for anyone attempting `H2`: the per-variable Combinatorial Nullstellensatz
(`MvPolynomial.eq_zero_of_eval_zero_at_prod_finset`) gives the statement directly when
`n <= q - 2`, and hyperplane counting gives `n < q`; Alon-Tarsi need a genuinely different
argument for `n >= q` that uses `q` not prime. The total-degree bound
`P != 0, P vanishes on A_1 x ... x A_n => deg P >= sum (|A_i| - 1)` is FALSE
(counterexample: `A_1 = {0,1,2}`, `A_2 = {0,1}` in `F_5`, `P = x_2 * (x_2 - 1)`).
-/

namespace OMA.R_opg_a_nowhere_zero_point_in_a_linear_mapping_R1

/-- Jaeger's conjecture for prime-order fields: the open case. -/
def H1 : Prop :=
  ∀ (F : Type) [Field F] [Fintype F], 4 ≤ Fintype.card F → (Fintype.card F).Prime →
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) F), IsUnit A.det →
      ∃ x y : Fin n → F, (∀ i, x i ≠ 0) ∧ (∀ i, y i ≠ 0) ∧ A.mulVec x = y

/-- Jaeger's conjecture for fields whose order is not prime: the theorem of Alon and Tarsi
(Combinatorica 9 (1989) 393-395), i.e. the case `q = p^k` with `k ≥ 2`. -/
def H2 : Prop :=
  ∀ (F : Type) [Field F] [Fintype F], 4 ≤ Fintype.card F → ¬ (Fintype.card F).Prime →
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) F), IsUnit A.det →
      ∃ x y : Fin n → F, (∀ i, x i ≠ 0) ∧ (∀ i, y i ≠ 0) ∧ A.mulVec x = y

theorem main : H1 → H2 →
    type_of% @OMA.S_opg_a_nowhere_zero_point_in_a_linear_mapping.main := by
  intro h1 h2 F _ _ hcard n A hA
  by_cases hp : (Fintype.card F).Prime
  · exact h1 F hcard hp n A hA
  · exact h2 F hcard hp n A hA

end OMA.R_opg_a_nowhere_zero_point_in_a_linear_mapping_R1
