import Mathlib

/-!
# P vs. PSPACE

Source: https://www.openproblemgarden.org/op/p_vs_pspace
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Problem (folklore): is there a problem computable by a Turing machine in polynomial space (and
unbounded time) but not in polynomial time? `main` states the expected answer: `P ≠ PSPACE`.

Conventions:
* A decision problem is a predicate `L : ℕ → Bool` on binary-encoded naturals; polynomial time is
  Mathlib's `Turing.TM2ComputableInPolyTime` with `Computability.finEncodingNatBool`, as in the
  `P vs. BPP` statement of this repository.
* Mathlib has no space-bounded machines, so `PSPACE` is given by its standard alternating
  characterisation (Chandra–Kozen–Stockmeyer, `PSPACE = AP`; equivalently, polynomial-time
  reducibility to TQBF): `L ∈ PSPACE` iff there are a polynomial `p` and a polynomial-time `V`
  such that `L x` is the value of the game in which two players alternately choose
  `m = p (bit length of x)` bits `b₁, …, bₘ` (the first player moves first) and the first player
  wins iff `V (Nat.pair x r)` holds, where `r = ∑ bᵢ 2^(i-1)` codes the chosen bits.
* `gameVal V m bs` is that value with the bits `bs` already chosen, written with negation: the
  player to move wins iff some choice leaves the opponent in a losing position. With an even
  number `m = 2 p(|x|)` of moves this is `∃ b₁ ∀ b₂ … ∃ bₘ₋₁ ∀ bₘ, V`.
-/

namespace OMA.S_opg_p_vs_pspace

open Computability

/-- The bits `bs` (most recent first) read as a binary number, last-chosen bit most significant. -/
def bitsVal : List Bool → ℕ
  | [] => 0
  | b :: bs => bitsVal bs + (if b then 2 ^ bs.length else 0)

/-- Value of the alternating bit game with `m` moves left after the moves `bs`, for the player to
move: at the end the first player wins iff `V (code of the bits)` holds. -/
def gameVal (V : ℕ → Bool) : ℕ → List Bool → Bool
  | 0, bs => V (bitsVal bs)
  | m + 1, bs => !(gameVal V m (false :: bs)) || !(gameVal V m (true :: bs))

/-- `L ∈ P`. -/
def InP (L : ℕ → Bool) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime encodingNatBool.encode encodingBoolBool.encode L)

/-- `L ∈ PSPACE`, via polynomially long alternating games with a polynomial-time referee.
With `2 * p` moves the first player moves first and the second player moves last, and the
referee's verdict is taken as is. -/
def InPSPACE (L : ℕ → Bool) : Prop :=
  ∃ (p : Polynomial ℕ) (V : ℕ → Bool), InP V ∧
    ∀ x : ℕ, L x = gameVal (fun r => V (Nat.pair x r)) (2 * p.eval (encodeNat x).length) []

/-- `P ≠ PSPACE`: some problem in polynomial space is not in polynomial time. -/
theorem main : ∃ L : ℕ → Bool, InPSPACE L ∧ ¬ InP L := by
  sorry

end OMA.S_opg_p_vs_pspace
