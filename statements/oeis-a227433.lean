import Mathlib

/-!
# A227433: pairs of 2 X 2 matrices over Z/pZ that do not commute

Source: https://oeis.org/A227433 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry (José María Grau Ribas, Jul 11 2013), offset 1: Number of pairs of 2 X 2 matrices over
Z/nZ that do not commute. Data
0, 168, 5616, 59136, 372000, 1596456, 5630688, 16343040, 42305328, 98361000, ...

Formula section: Conjecturally, a(p) = p^3(p^3-1)(p^2-1), for p prime. - Giovanni Resta,
Jul 13 2013

Formalization notes.
* A pair is an ordered pair (A, B) of matrices in `Matrix (Fin 2) (Fin 2) (ZMod p)`, and the
  pair does not commute when A * B ≠ B * A. The count is `Nat.card` of the subtype.
* The data agree: p = 2 gives 8 * 7 * 3 = 168 and p = 3 gives 27 * 26 * 8 = 5616.
-/

namespace OMA.S_oeis_a227433

/-- Resta's conjecture: a(p) = p^3 (p^3 - 1) (p^2 - 1) for every prime p. -/
theorem main : ∀ p : ℕ, p.Prime →
    Nat.card {P : Matrix (Fin 2) (Fin 2) (ZMod p) × Matrix (Fin 2) (Fin 2) (ZMod p) //
      P.1 * P.2 ≠ P.2 * P.1} = p ^ 3 * (p ^ 3 - 1) * (p ^ 2 - 1) := by
  sorry

end OMA.S_oeis_a227433
