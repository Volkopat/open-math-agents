import Mathlib

/-!
# Log-rank conjecture

Source: https://en.wikipedia.org/wiki/Log-rank_conjecture
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Lovász–Saks: the deterministic communication complexity of every Boolean function
`f(x, y)` is at most a polynomial in `log rank(M_f)`, where `M_f` is its communication matrix
over the reals.

## Encoding

* Inputs come from arbitrary finite types `X` (Alice) and `Y` (Bob); `f : X → Y → Bool`.
* A deterministic protocol is a binary tree whose internal nodes are owned by Alice (the
  branch is a function of `x`) or by Bob (a function of `y`) and whose leaves are labelled by
  the output. Its cost is the depth. `D(f)` is the least depth of a protocol computing `f`.
* `M_f` is the `0/1` real matrix `M_f x y = 1 ↔ f x y`, and `rank` is `Matrix.rank`.
* "At most a polynomial in `log rank`" is: there are `k : ℕ` and `C : ℝ` with
  `D(f) ≤ C · (log₂ rank M_f)^k + C` for all `f`.
-/

namespace OMA.S_wpc_log_rank_conjecture

/-- Deterministic two-party protocols. -/
inductive Protocol (X Y : Type) : Type
  | leaf : Bool → Protocol X Y
  | alice : (X → Bool) → Protocol X Y → Protocol X Y → Protocol X Y
  | bob : (Y → Bool) → Protocol X Y → Protocol X Y → Protocol X Y

namespace Protocol

variable {X Y : Type}

/-- Output of a protocol on inputs `x`, `y` (branch `true` goes to the second subtree). -/
def eval : Protocol X Y → X → Y → Bool
  | leaf b, _, _ => b
  | alice a p q, x, y => if a x then q.eval x y else p.eval x y
  | bob b p q, x, y => if b y then q.eval x y else p.eval x y

/-- Depth (number of bits communicated in the worst case). -/
def depth : Protocol X Y → ℕ
  | leaf _ => 0
  | alice _ p q => max p.depth q.depth + 1
  | bob _ p q => max p.depth q.depth + 1

end Protocol

/-- Deterministic communication complexity of `f`. -/
noncomputable def commComplexity {X Y : Type} (f : X → Y → Bool) : ℕ :=
  sInf {d | ∃ P : Protocol X Y, P.depth = d ∧ ∀ x y, P.eval x y = f x y}

/-- The communication matrix of `f` over `ℝ`. -/
def commMatrix {X Y : Type} (f : X → Y → Bool) : Matrix X Y ℝ :=
  fun x y => if f x y then 1 else 0

theorem main :
    ∃ (k : ℕ) (C : ℝ), ∀ (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
      (f : X → Y → Bool),
      (commComplexity f : ℝ) ≤ C * Real.logb 2 (commMatrix f).rank ^ k + C := by
  sorry

end OMA.S_wpc_log_rank_conjecture
