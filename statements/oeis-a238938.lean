import Mathlib

/-!
# A238938: Powers of 2 without the digit '0' in their decimal expansion.

Source: https://oeis.org/A238938
Credit: @clementtrecourt

Conjecture (from the entry): Conjectured to be finite and complete. See the OEIS wiki page for further information, references and links.

Formalization notes:
* The sequence lists the powers 2^e (e ≥ 0) whose decimal expansion has no digit 0.
* 'Finite and complete' is stated as: this set is exactly the set of the 31 listed terms.
-/

namespace OMA.S_oeis_a238938

theorem main :
    {m : ℕ | (∃ e : ℕ, m = 2 ^ e) ∧ 0 ∉ Nat.digits 10 m} = ({1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 8192, 16384, 32768, 65536, 262144, 524288, 16777216, 33554432, 134217728, 268435456, 2147483648, 4294967296, 8589934592, 17179869184, 34359738368, 68719476736, 137438953472, 549755813888, 562949953421312, 2251799813685248, 147573952589676412928} : Set ℕ) := by
  sorry

end OMA.S_oeis_a238938
