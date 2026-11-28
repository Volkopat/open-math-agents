import Mathlib

/-!
# When a unitary matrix times its complex conjugate is diagonal

Source: https://mathoverflow.net/questions/247291
Credit: @koolkao

Question (batconjurer, MathOverflow 247291, 2016; CC BY-SA 3.0). Suppose you have a unitary
matrix `U` such that `Ū U = D` for some diagonal unitary matrix `D` (everything is taking place
over `ℂ`). This is equivalent to a couple of other conditions: 1) `DU = Uᵀ`, 2) `DUD = U`.
Furthermore, this implies that `U^2` is symmetric. So most unitary matrices do not satisfy this
property. But when they do, is it true that `D^2 = I`, which is equivalent to saying that `D`
commutes with `U`?

`main` states that the answer is yes: for every `n`, every unitary `U ∈ U(n)` and every diagonal
unitary `D` with `Ū U = D`, `D^2 = I`. A disproof is a counterexample.

Translation choices:
* matrices are `n × n` complex matrices indexed by `Fin n`; `U` is unitary when it lies in
  `Matrix.unitaryGroup (Fin n) ℂ`;
* `Ū` is the entrywise complex conjugate, `U.map star`;
* a diagonal unitary matrix is `Matrix.diagonal d` with `‖d i‖ = 1` for every `i` (a diagonal
  matrix is unitary exactly when its diagonal entries have modulus `1`);
* `I` is the identity matrix `1`; the equivalent reformulation "`D` commutes with `U`" given in
  the source is not stated separately.
-/

namespace OMA.S_mo_247291

open Matrix

/-- If `U` is unitary and `Ū U = D` is diagonal unitary, then `D^2 = I`. -/
theorem main :
    ∀ (n : ℕ) (U : Matrix (Fin n) (Fin n) ℂ), U ∈ Matrix.unitaryGroup (Fin n) ℂ →
      ∀ d : Fin n → ℂ, (∀ i, ‖d i‖ = 1) → U.map star * U = diagonal d →
        diagonal d ^ 2 = 1 := by
  sorry

end OMA.S_mo_247291
