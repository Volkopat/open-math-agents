import Mathlib

/-!
# P vs. BPP

Open Problem Garden: https://www.openproblemgarden.org/op/p_vs_bpp
Conjecture (folklore): every problem decidable by a probabilistic polynomial-time Turing
machine with error probability at most 1/3 is decidable in deterministic polynomial time.

Conventions. A decision problem is a predicate `L : ℕ → Bool` on binary-encoded naturals;
polynomial time is Mathlib's `Turing.TM2ComputableInPolyTime` with the binary encoding
`Computability.finEncodingNatBool.encode`. `L ∈ BPP` is stated in the standard verifier form: there
are a polynomial `p` and a deterministic polynomial-time `V` such that for every `x`, with
`m = p (bit length of x)`, at least two thirds of the random strings `r < 2 ^ m` satisfy
`V (Nat.pair x r) = L x`. (`Nat.pair` and its inverse are polynomial-time, so this is the
usual class.) The inclusion `P ⊆ BPP` is trivial; `main` is the open inclusion `BPP ⊆ P`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_opg_p_vs_bpp

open Computability

/-- `BPP ⊆ P`. -/
theorem main :
    ∀ L : ℕ → Bool,
      (∃ (p : Polynomial ℕ) (V : ℕ → Bool),
          Nonempty (Turing.TM2ComputableInPolyTime finEncodingNatBool.encode finEncodingBoolBool.encode V) ∧
          ∀ x : ℕ,
            2 * 2 ^ p.eval (encodeNat x).length ≤
              3 * ((Finset.range (2 ^ p.eval (encodeNat x).length)).filter
                    fun r => V (Nat.pair x r) = L x).card) →
      Nonempty (Turing.TM2ComputableInPolyTime finEncodingNatBool.encode finEncodingBoolBool.encode L) := by
  sorry

end OMA.S_opg_p_vs_bpp
