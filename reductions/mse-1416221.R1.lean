import OMAStatements.S_mse_1416221
import Mathlib

/-!
# Reduction of Math.SE 1416221 (Reix's Mersenne test): the prime direction and the converse

`S q 0 = 9 + 9⁻¹` and `S q (i + 1) = S q i ^ 2 - 2` in `ZMod (2 ^ q - 1)`.

* `H1` (the classical direction, every odd prime exponent): if `M_q = 2 ^ q - 1` is prime then
  `S q (q - 1) = S q 0`. Writing `a = 9 ^ (2 ^ i)`, induction gives `S q i = a + a⁻¹`, and Fermat's
  little theorem for the base `3` gives `9 ^ (2 ^ (q - 1)) = 3 ^ (M_q + 1) = 9`.
* `H2` (the open converse): `S q (q - 1) = S q 0` forces `M_q` to be prime.

This separates the proved direction from the open one; it is not progress on the converse.
-/

namespace OMA.R_mse_1416221_R1

/-- If `2 ^ q - 1` is prime (with `q` an odd prime), the sequence returns to its seed. -/
def H1 : Prop :=
  ∀ q : ℕ, q.Prime → 2 < q → (mersenne q).Prime →
    OMA.S_mse_1416221.S q (q - 1) = OMA.S_mse_1416221.S q 0

/-- The open converse: a return to the seed at step `q - 1` certifies that `2 ^ q - 1` is prime. -/
def H2 : Prop :=
  ∀ q : ℕ, q.Prime → 2 < q →
    OMA.S_mse_1416221.S q (q - 1) = OMA.S_mse_1416221.S q 0 → (mersenne q).Prime

theorem main : H1 → H2 → type_of% @OMA.S_mse_1416221.main := by
  intro h1 h2 q hq hq2
  exact ⟨h1 q hq hq2, h2 q hq hq2⟩

end OMA.R_mse_1416221_R1
