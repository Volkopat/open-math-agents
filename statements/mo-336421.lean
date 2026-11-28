import Mathlib

/-!
# Generic rank of a derivative-evaluation matrix on a product grid

Source: Seva, https://mathoverflow.net/questions/336421 (CC BY-SA 4.0).
Credit: @connoranderson.

For every fixed nonzero polynomial of degree d in characteristic zero, a
nonzero polynomial in the 2n coordinates of B and C certifies that the
matrix has its largest possible rank min(d+1,n²) on the complement of its
zero set. This complement contains a grid with both coordinate lists
injective. The assertion applies in particular to the split squarefree
polynomials in the question. The requested bound d+2−n follows whenever
n≥1 and d+2−n≤n², including the indicated asymptotic regime.

There is a one-parameter sufficient condition on individual grids: r
distinct ratios b/c with nonzero denominators give rank at least r after
all but finitely many common reciprocal scalings of C. Reversing the
derivative polynomials gives a Vandermonde minor at parameter zero.
-/

namespace OMA.S_mo_336421
open Polynomial Matrix
noncomputable def grid {K : Type*} [Field K] {n : ℕ} (P : K[X]) (b c : Fin n → K) :
    Matrix (Fin (P.natDegree+1)) (Fin n × Fin n) K :=
  Matrix.of fun i j => b j.1 ^ i.val * (derivative^[i.val] P).eval (c j.2)

theorem main : ∀ (K : Type*) [Field K] [CharZero K] (n : ℕ) (P : K[X]), P≠0 →
    (∃ D : MvPolynomial (Fin n ⊕ Fin n) K, D≠0 ∧
      (∀ b c : Fin n → K, MvPolynomial.eval (Sum.elim b c) D≠0 →
        (grid P b c).rank=min (P.natDegree+1) (n*n)) ∧
      ∃ b c : Fin n → K, Function.Injective b ∧ Function.Injective c ∧
        MvPolynomial.eval (Sum.elim b c) D≠0) ∧
    ∀ (b c : Fin n → K) (r : ℕ), r≤P.natDegree+1 → ∀ j : Fin r → Fin n × Fin n,
      (∀ k,c (j k).2≠0) → Function.Injective (fun k => b (j k).1/c (j k).2) →
      ∃ bad : Finset K, ∀ t ∉ bad, r ≤ (grid P b (fun k => c k/t)).rank := by
  sorry
end OMA.S_mo_336421
