import Mathlib

/-!
# Two conjectures on a special type of graph: the second conjecture

Source: https://mathoverflow.net/questions/401217
Credit: @koolkao

Question (zhjzwlys, MathOverflow 401217, 2021; CC BY-SA 4.0). `n ∈ Z` and `n ≥ 3`. Set
`x_n = (1,1,…,1)^T ∈ ℝ^n` […]. 2. The second conjecture is more complex (vertices have a varying
weight). Define function `θ` (`ℝ^n → ℝ^n`) as following:
`(θ((a_i)_{1≤i≤n}))_k = 1 if a_k = max({a_i}_{1≤i≤n}), 0 else`. `Y_k ∈ ℝ^n` is a sequence. Given a
matrix `A = (a_ij) ∈ ℝ^{n×n}, A^T = −A, A x_n = 0`. If `Y_k` satisfy that `Y_{k+1} = Y_k + θ(A Y_k)`
then I guess: `lim_k Y_k / ‖Y_k‖ = x_n / ‖x_n‖`. I have verified it with the help of computer under
many conditions. It is easy to prove the condition `n = 3`, and I think I can prove `n = 4`. […]

`main` states the second conjecture for every `n ≥ 3`, every real antisymmetric `A` with zero row
sums and every real sequence `Y` that satisfies the recursion; a disproof is a counterexample.

Translation choices:
* vectors in `ℝ^n` are `Fin n → ℝ`, matrices are `Matrix (Fin n) (Fin n) ℝ`, `A Y` is
  `A.mulVec Y` and `x_n` is the constant function `1`;
* `θ` is the source's function: `a_k = max_i a_i` is written `∀ i, a i ≤ a k`, so every coordinate
  that attains the maximum gets `1` (ties are not broken);
* the start `Y_0 ∈ ℝ^n` is arbitrary, as in the source, which puts no condition on it;
* `‖·‖` is the Euclidean norm `√(∑ v_i²)`; the source does not name a norm. For any other norm the
  statement is equivalent, because `v ↦ v / ‖v‖` and `v ↦ v / ‖v‖₂` are continuous functions of each
  other away from `0`, and the coordinate sum of `Y_k` grows by at least `1` per step, so `Y_k ≠ 0`
  for all large `k`. For the same reason Lean's convention `0⁻¹ = 0`, which matters only at the at
  most one `k` with `Y_k = 0`, does not change the limit;
* the limit is in the usual topology of `ℝ^n` (the product topology on `Fin n → ℝ`);
* `n ≥ 3` is the standing assumption of the source;
* not stated: the first conjecture (`γ_{2k} = (k+1)/(k−1)` for the matrices with zero row sums and
  off-diagonal entries of absolute value at least `1`), and the request for related work.

Status: MathOverflow 401217 had no answers in November 2026.
-/

namespace OMA.S_mo_401217

open Filter Topology

/-- The source's `θ`: `θ(a)_k = 1` if `a_k = max_i a_i`, else `0`. -/
noncomputable def θ {n : ℕ} (a : Fin n → ℝ) : Fin n → ℝ :=
  fun k => if ∀ i, a i ≤ a k then 1 else 0

/-- The Euclidean norm `√(∑ v_i²)` of `v ∈ ℝ^n`. -/
noncomputable def norm2 {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The second conjecture of MathOverflow 401217: `Y_k / ‖Y_k‖ → x_n / ‖x_n‖`. -/
theorem main :
    ∀ n : ℕ, 3 ≤ n → ∀ A : Matrix (Fin n) (Fin n) ℝ, A.transpose = -A →
      A.mulVec (fun _ => 1) = 0 →
      ∀ Y : ℕ → Fin n → ℝ, (∀ k, Y (k + 1) = Y k + θ (A.mulVec (Y k))) →
        Tendsto (fun k => (norm2 (Y k))⁻¹ • Y k) atTop
          (𝓝 ((norm2 (fun _ : Fin n => (1 : ℝ)))⁻¹ • fun _ : Fin n => (1 : ℝ))) := by
  sorry

end OMA.S_mo_401217
