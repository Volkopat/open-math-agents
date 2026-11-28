import Mathlib

/-!
# Linear-size circuits for stable 0,1 < 2 sorting

Source: https://www.openproblemgarden.org/op/linear_size_circuits_for_stable_0_1_2_sorting
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Problem (Regan): can `O(n)`-size circuits compute the function `f` on `{0,1,2}*` defined by
`f(λ) = λ`, `f(0x) = 0 f(x)`, `f(1x) = 1 f(x)`, `f(2x) = f(x) 2`?

Conventions:
* Circuits are Boolean circuits over the basis `{AND, OR, NOT}` (fan-in at most 2, unbounded
  fan-out); size is the number of gates. Any other finite complete basis changes sizes by a
  constant factor only, so "`O(n)` size" does not depend on this choice.
* A circuit is a straight-line program: wire `k < m` is the `k`-th input bit and wire `m + j` is
  gate `j`, whose arguments are wire indices (an index that is not yet defined reads `false`).
  The outputs are a list of wire indices.
* A symbol of `{0,1,2}` is encoded by two bits: `0 ↦ 00`, `1 ↦ 01`, `2 ↦ 10`; a string of length
  `n` is encoded by `2n` input bits and `f` of it by `2n` output bits.
* A circuit family of size `O(n)`: a constant `c` and, for every input length `n`, a circuit
  with at most `c n + c` gates computing `f` on all strings of length `n`.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_opg_linear_size_circuits_for_stable_0_1_2_sorting

/-- The function `f` of the source. -/
def f : List (Fin 3) → List (Fin 3)
  | [] => []
  | a :: x => if a = 2 then f x ++ [2] else a :: f x

/-- Gate operations. -/
inductive Op
  | and
  | or
  | not

/-- A Boolean circuit as a straight-line program. -/
structure Circuit where
  gates : List (Op × ℕ × ℕ)
  outs : List ℕ

/-- Apply one gate to the current list of wire values. -/
def step (vals : List Bool) (g : Op × ℕ × ℕ) : List Bool :=
  let a := vals.getD g.2.1 false
  let b := vals.getD g.2.2 false
  vals ++ [match g.1 with
    | Op.and => a && b
    | Op.or => a || b
    | Op.not => !a]

/-- Evaluate a circuit on an input bit string. -/
def Circuit.eval (C : Circuit) (input : List Bool) : List Bool :=
  let vals := C.gates.foldl step input
  C.outs.map (fun k => vals.getD k false)

/-- Two-bit encoding of a symbol. -/
def encSym (a : Fin 3) : List Bool := [decide (a = 2), decide (a = 1)]

/-- Encoding of a string. -/
def enc (x : List (Fin 3)) : List Bool := x.flatMap encSym

theorem main :
    ∃ c : ℕ, ∀ n : ℕ, ∃ C : Circuit, C.gates.length ≤ c * n + c ∧
      ∀ x : List (Fin 3), x.length = n → C.eval (enc x) = enc (f x) := by
  sorry

end OMA.S_opg_linear_size_circuits_for_stable_0_1_2_sorting
