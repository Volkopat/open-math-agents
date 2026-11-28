import Mathlib

/-!
# Four-color bead strings up to reversal

Ralf Stephan's conjecture 72 gives the number of four-color strings up to
reversal after excluding palindromes for lengths greater than one. Following
A032087, all four one-bead strings are counted. For longer strings, the
lexicographically smaller orientation represents each two-element orbit.
Elizabeth Wilmer proved the formula by counting all words and all palindromes.

Sources: https://oeis.org/A032087 (OEIS Foundation, CC BY-SA 4.0),
https://arxiv.org/abs/math/0409509 and https://oeis.org/A032087/a032087.pdf.
Credit: @connoranderson
-/

namespace OMA.S_oeis_a032087

abbrev Word (n : ℕ) := Fin n → Fin 4

def reverseWord {n : ℕ} (w : Word n) : Word n := fun i => w i.rev

noncomputable def beadCount (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun w : Word n =>
    n = 1 ∨ List.ofFn w < List.ofFn (reverseWord w)).card

theorem main : beadCount 1 = 4 ∧ ∀ n : ℕ, 1 < n →
    beadCount n = (4^n - (if Even n then 2^n else 2^(n+1))) / 2 := by
  sorry

end OMA.S_oeis_a032087
