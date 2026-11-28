import Mathlib

/-!
# OEIS A005573: walks on the cubic lattice staying above the xy-plane

Source: https://oeis.org/A005573
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of `n`-step walks on the cubic lattice `ℤ³` starting at the origin and never
going below the xy-plane: `1, 5, 26, 139, …`. Conjecture (OEIS entry):
`a(n) = 6ⁿ · ₂F₁(1/2, -n; 2; 2/3)`.

Conventions:
* A walk is a sequence of `n` unit steps `±e₁, ±e₂, ±e₃`; steps `0–3` are horizontal, `4` is
  `+e₃` and `5` is `-e₃`. It never goes below the plane iff every partial sum of the
  `e₃`-components is `≥ 0`.
* The hypergeometric series terminates: `₂F₁(1/2, -n; 2; z) = ∑_{k=0}^{n} (1/2)_k (-n)_k /
  ((2)_k k!) z^k`, with rising factorials `(x)_k` (`ascPochhammer`).
-/

namespace OMA.S_oeis_a005573

/-- Vertical component of a step. -/
def dz (s : Fin 6) : ℤ := if s = 4 then 1 else if s = 5 then -1 else 0

/-- `a(n)`: walks whose height never becomes negative. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin 6)).filter fun w =>
    ∀ m ≤ n, 0 ≤ ∑ i : Fin n, if (i : ℕ) < m then dz (w i) else 0).card

/-- Rising factorial `(x)_k`. -/
noncomputable def rf (x : ℚ) (k : ℕ) : ℚ := (ascPochhammer ℚ k).eval x

/-- `6ⁿ ₂F₁(1/2, -n; 2; 2/3)`. -/
noncomputable def hyp (n : ℕ) : ℚ :=
  6 ^ n * ∑ k ∈ Finset.range (n + 1),
    rf (1 / 2) k * rf (-(n : ℚ)) k / (rf 2 k * k.factorial) * (2 / 3) ^ k

/-- `a(n) = 6ⁿ ₂F₁(1/2, -n; 2; 2/3)`. -/
theorem main : ∀ n : ℕ, (a n : ℚ) = hyp n := by
  sorry

end OMA.S_oeis_a005573
