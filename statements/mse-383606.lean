import Mathlib

/-!
# A Problem on Time Complexity of Algorithms

Source: https://math.stackexchange.com/questions/383606/a-problem-on-time-complexity-of-algorithms
Credit: @eltociear

The question (Shayan, 2013): for every integer `t`, is there a problem that can be *verified*
in time `O(n^s)` (given a candidate solution `y`, decide whether `y` is correct in time `O(n^s)`)
but whose solution can not be found in time `O(n^{st})`?

Reading used here (the standard one, spelled out in the answer by aws on the same page):
for all positive integers `s` and `t` there is a decision problem in `NTIME(n^s)` that is not in
`DTIME(n^{st})`, i.e. `NTIME(n^s) ⊄ DTIME(n^{st})`. Comments on the choices made:

* `s` is left free in the question; as in the answer it is quantified universally. Both `s` and
  `t` range over positive integers (for `t = 0` or `s = 0` the bound `n^{st}` is constant and the
  question degenerates).
* "Its solution can be found" is read for decision problems (`L x` is decided), as in the answer;
  a search algorithm would in particular decide `L`, so this is the weaker hardness requirement,
  hence the stronger and standard statement.
* Machine model: Mathlib's multi-stack Turing machines `Turing.FinTM2` with their step count
  `Turing.TM2OutputsInTime`, the model Mathlib uses for `TM2ComputableInTime`
  (a multi-stack machine simulates a multitape machine with constant-factor overhead and vice
  versa, so `O(n^k)` classes are the usual multitape ones).
* `O(n^k)` on inputs of length `n` is written `≤ c * n ^ k + c` for some constant `c`
  (the `+ c` covers `n = 0`).
* Verifier: a deterministic machine reading `x`, a separator, then the candidate `y`
  (alphabet `Option Bool`, `none` = separator). Its running time is bounded in `n = |x|` only,
  as in the question, for every candidate `y`; so it can only look at an `O(n^s)` prefix of `y`,
  and `L x` holds iff some candidate is accepted. This is the usual certificate definition of
  `NTIME(n^s)`.
* Decider: a deterministic machine reading `x` (alphabet `Bool`) and writing `[L x]`.

Partial knowledge: for `s = t = 1` this is `NTIME(n) ≠ DTIME(n)`, proved for multitape machines
by Paul, Pippenger, Szemerédi and Trotter (1983); the general case is open (it would follow from
`P ≠ NP` by padding, as the answer explains).
-/

namespace OMA.S_mse_383606

open Turing

/-- Encoding of an instance `x` together with a candidate solution `y`: `x`, a separator, `y`. -/
def encPair (x y : List Bool) : List (Option Bool) :=
  x.map some ++ none :: y.map some

/-- `L` can be verified in time `O(n^s)`: some deterministic multi-stack Turing machine, given
`x` and any candidate `y`, outputs `R x y` within `c * |x|^s + c` steps, and `L x` holds iff some
candidate `y` is accepted. -/
def VerifiableInTime (s : ℕ) (L : List Bool → Bool) : Prop :=
  ∃ (M : TM2ComputableAux (Option Bool) Bool) (R : List Bool → List Bool → Bool) (c : ℕ),
    (∀ x y : List Bool,
      Nonempty (TM2OutputsInTime M.tm ((encPair x y).map M.inputAlphabet.invFun)
        (some ([R x y].map M.outputAlphabet.invFun)) (c * x.length ^ s + c))) ∧
    ∀ x : List Bool, L x = true ↔ ∃ y : List Bool, R x y = true

/-- `L` can be decided in time `O(n^k)` by a deterministic multi-stack Turing machine. -/
def DecidableInTime (k : ℕ) (L : List Bool → Bool) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (c : ℕ),
    ∀ x : List Bool,
      Nonempty (TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun)
        (some ([L x].map M.outputAlphabet.invFun)) (c * x.length ^ k + c))

/-- For all positive integers `s`, `t` there is a problem verifiable in time `O(n^s)` whose
solution can not be found in time `O(n^{st})`, i.e. `NTIME(n^s) ⊄ DTIME(n^{st})`. -/
theorem main :
    ∀ s t : ℕ, 1 ≤ s → 1 ≤ t →
      ∃ L : List Bool → Bool, VerifiableInTime s L ∧ ¬ DecidableInTime (s * t) L := by
  sorry

end OMA.S_mse_383606
