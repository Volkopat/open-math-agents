import Mathlib

/-!
# A question on simultaneous conjugation of permutations

Source: MathOverflow question 267191, https://mathoverflow.net/questions/267191
Credit: @aroth01

The question: given $a, b \in S_n$ such that their commutator has at least $n - 4$ fixed points,
is there an element $z \in S_n$ such that $a^z = a^{-1}$ and $b^z = b^{-1}$? Here
$a^z := z^{-1} a z$. The source reports that Magma confirms this for $n \le 11$ and that it holds
when $a$ and $b$ commute. The question has no answer, so the problem is open. This file states
the positive answer.

Reading of the source:
* $S_n$ is `Equiv.Perm (Fin n)`.
* A permutation of `Fin n` has at least $n - 4$ fixed points exactly when it moves at most $4$
  points, that is, when its `support` has at most $4$ elements. This form also covers $n < 4$,
  where the condition holds for every pair.
* The commutator is written out as $a^{-1} b^{-1} a b$. The other convention $a b a^{-1} b^{-1}$
  is conjugate to it (by $ab$), so both move the same number of points.
-/

namespace OMA.S_mo_267191

/-- If the commutator of `a b : Equiv.Perm (Fin n)` moves at most four points (it has at least
`n - 4` fixed points), then some `z` inverts both: `z⁻¹ * a * z = a⁻¹` and `z⁻¹ * b * z = b⁻¹`. -/
theorem main :
    ∀ (n : ℕ) (a b : Equiv.Perm (Fin n)), (a⁻¹ * b⁻¹ * a * b).support.card ≤ 4 →
      ∃ z : Equiv.Perm (Fin n), z⁻¹ * a * z = a⁻¹ ∧ z⁻¹ * b * z = b⁻¹ := by
  sorry

end OMA.S_mo_267191
