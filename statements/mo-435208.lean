import Mathlib

/-!
# Non-Wieferich numbers if the set of non-Wieferich primes is finite

Source: https://mathoverflow.net/questions/435208
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

An integer `n` is a Wieferich number if `2^φ(n) ≡ 1 (mod n²)`. Question Q1: assuming there are
only finitely many non-Wieferich primes, are there only finitely many squarefree non-Wieferich
numbers? `main` states Q1 with the answer yes, as an implication.

Conventions:
* Wieferich numbers (A077816) are odd, and the source's non-Wieferich numbers are the odd
  positive integers that are not Wieferich numbers (otherwise every even squarefree number would
  qualify and Q1 would be trivially false); primes are odd primes accordingly.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_mo_435208

/-- `n` is a Wieferich number: `n² ∣ 2^φ(n) - 1`. -/
def IsWieferich (n : ℕ) : Prop := n ^ 2 ∣ 2 ^ Nat.totient n - 1

/-- If only finitely many odd primes are non-Wieferich, only finitely many odd squarefree
numbers are non-Wieferich. -/
theorem main : {p : ℕ | p.Prime ∧ p ≠ 2 ∧ ¬ IsWieferich p}.Finite →
    {n : ℕ | Odd n ∧ Squarefree n ∧ ¬ IsWieferich n}.Finite := by
  sorry

end OMA.S_mo_435208
