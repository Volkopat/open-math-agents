import Mathlib

/-!
# Unconditional derandomization of Arthur-Merlin games

Source: https://www.openproblemgarden.org/op/unconditional_derandomization_of_mathcal_am
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Problem: prove unconditionally that `AM ⊆ Σ₂` (`AM ⊆ Π₂` is easy).

Conventions:
* A decision problem is a predicate `L : ℕ → Bool` on binary-encoded naturals; polynomial time is
  Mathlib's `Turing.TM2ComputableInPolyTime` with `Computability.finEncodingNatBool`, as in the
  `P vs. BPP` statement of this repository. Tuples are encoded with `Nat.pair`, which is
  polynomial-time with polynomial-time inverse; strings of length `m` are the numbers `< 2 ^ m`,
  with `m = p (bit length of x)` for a polynomial `p`.
* `AM` (two-round Arthur–Merlin, public coins) in the standard verifier form: there are `p` and a
  polynomial-time `V` such that if `L x` then at least `2/3` of Arthur's strings `r` admit a
  Merlin reply `y` with `V ⟨x, r, y⟩`, and if `¬ L x` then at most `1/3` of them do.
* `Σ₂`: there are `q` and a polynomial-time `W` with `L x ↔ ∃ y, ∀ z, W ⟨x, y, z⟩`, quantifiers
  over strings of length `q (bit length of x)`.
-/

namespace OMA.S_opg_unconditional_derandomization_of_mathcal_am

open Classical

open Computability

/-- `L ∈ P`. -/
def InP (L : ℕ → Bool) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime encodingNatBool.encode encodingBoolBool.encode L)

/-- Number of Arthur strings `r < 2 ^ m` for which Merlin has a reply `y < 2 ^ m`. -/
noncomputable def goodCoins (V : ℕ → Bool) (x m : ℕ) : ℕ :=
  ((Finset.range (2 ^ m)).filter fun r =>
    ∃ y ∈ Finset.range (2 ^ m), V (Nat.pair x (Nat.pair r y)) = true).card

/-- `L ∈ AM`. -/
def InAM (L : ℕ → Bool) : Prop :=
  ∃ (p : Polynomial ℕ) (V : ℕ → Bool), InP V ∧ ∀ x : ℕ,
    (L x = true → 2 * 2 ^ p.eval (encodeNat x).length ≤
        3 * goodCoins V x (p.eval (encodeNat x).length)) ∧
    (L x = false → 3 * goodCoins V x (p.eval (encodeNat x).length) ≤
        2 ^ p.eval (encodeNat x).length)

/-- `L ∈ Σ₂`. -/
def InSigma2 (L : ℕ → Bool) : Prop :=
  ∃ (q : Polynomial ℕ) (W : ℕ → Bool), InP W ∧ ∀ x : ℕ,
    (L x = true ↔ ∃ y < 2 ^ q.eval (encodeNat x).length, ∀ z < 2 ^ q.eval (encodeNat x).length,
      W (Nat.pair x (Nat.pair y z)) = true)

/-- `AM ⊆ Σ₂`. -/
theorem main : ∀ L : ℕ → Bool, InAM L → InSigma2 L := by
  sorry

end OMA.S_opg_unconditional_derandomization_of_mathcal_am
