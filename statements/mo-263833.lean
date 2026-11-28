import Mathlib

/-!
# Quantum coupon collection: positivity of an alternating sum of matrices

Source: https://mathoverflow.net/questions/263833
Credit: @JamesSlash (agent: Claude Code, model claude-opus-5-5)

For symmetric positive definite real `d × d` matrices `X₁, …, Xₙ` the question considers

  `Qₙ(X₁, …, Xₙ) = ∑_{k=1}^{n} (-1)^{k+1} ∑_{i₁ < ⋯ < i_k} (X_{i₁} + ⋯ + X_{i_k})⁻¹`,

the matrix analogue of the expected waiting time of the coupon collector, and conjectures:
for `n ≥ 1` and `X₁, …, Xₙ ∈ S₊₊^d`, `Qₙ(X₁, …, Xₙ) ≻ 0`.

Encoding.
* `S₊₊^d` is `Matrix.PosDef` on `Matrix (Fin d) (Fin d) ℝ` (symmetric and positive definite);
  `≻ 0` is `Matrix.PosDef` as well.
* The inner sum over `i₁ < ⋯ < i_k` together with the outer sum over `k` is the sum over the
  nonempty subsets `S` of `Fin n`, with sign `(-1)^(|S|+1)`; the sum of the `X_i` over a
  nonempty subset is positive definite, hence invertible, so `⁻¹` is the matrix inverse.
* The source fixes the dimension `d` implicitly (`S₊₊^d`); the statement is for every `d`.
-/

namespace OMA.S_mo_263833

open Matrix

/-- The alternating sum `Qₙ(X₁, …, Xₙ)` over the nonempty subsets of `Fin n`. -/
noncomputable def couponMatrix {d n : ℕ} (X : Fin n → Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun S => S.Nonempty),
    ((-1 : ℝ) ^ (S.card + 1)) • (∑ i ∈ S, X i)⁻¹

/-- Sra's quantum coupon collection conjecture. -/
theorem main : ∀ (d n : ℕ), 1 ≤ n → ∀ X : Fin n → Matrix (Fin d) (Fin d) ℝ,
    (∀ i, (X i).PosDef) → (couponMatrix X).PosDef := by
  sorry

end OMA.S_mo_263833
