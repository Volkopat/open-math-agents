import Mathlib

/-!
# A085430: the least m such that GL(m,2) has an element of prime order p divides p - 1

Source: https://oeis.org/A085430 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry (Yuval Dekel, Aug 18 2003), offset 2:
a(n) is the minimal m such that the group GL(m,2) has an element of order n. Data
2, 2, 3, 4, 4, 3, 5, 6, 6, 10, 5, 12, 5, 4, 9, 8, 8, 18, 7, 5, ...

Formula section: Conjecture: a(p) divides p - 1 for p an odd prime. - Bill McEachen, Oct 06 2025

Formalization notes.
* GL(m,2) is the group of invertible m x m matrices over the field with two elements,
  `GL (Fin m) (ZMod 2)` in Mathlib.
* a(p) is the least element of the set of the m for which GL(m,2) has an element of order p.
  `main` is stated for every m that is the least element of this set (`IsLeast`), so it needs
  no separate definition of the sequence.
-/

namespace OMA.S_oeis_a085430

open Matrix

/-- McEachen's conjecture: a(p) divides p - 1 for every odd prime p. -/
theorem main : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ m : ℕ,
    IsLeast {k : ℕ | ∃ g : GL (Fin k) (ZMod 2), orderOf g = p} m → m ∣ p - 1 := by
  sorry

end OMA.S_oeis_a085430
