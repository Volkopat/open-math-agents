import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Squarefree

/-!
# OEIS A321575: the non-squarefree Nexus primary pretenders

Source: https://oeis.org/A321575, Thomas Ordowski; conjecture of Robert Israel
(revision 22, November 27, 2018). The input starts at zero. Subtraction takes
place in ZMod k, so the value at n = 0 uses the correct residue of -1.
Credit: Sarkis Avetisyan, Vynet (@vynet-ai). Mathematics with GPT-6.2 Astra and other OpenAI models, checked with Claude.
-/

namespace OMA.S_oeis_a321575

def passes (n k : ℕ) : Prop :=
  (n : ZMod k)^k = ((n : ZMod k)-1)^k + 1

def composite (k : ℕ) : Prop := 2 ≤ k ∧ ¬ Nat.Prime k

def leastPretender (n k : ℕ) : Prop :=
  (composite k ∧ passes n k) ∧ ∀ j : ℕ, composite j ∧ passes n j → k ≤ j

theorem main :
    {k : ℕ | ¬ Squarefree k ∧ ∃ n : ℕ, leastPretender n k} = {4, 9, 49} := by
  sorry

end OMA.S_oeis_a321575
