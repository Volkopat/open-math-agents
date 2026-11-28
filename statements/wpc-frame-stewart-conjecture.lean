import Mathlib

/-!
# Frame–Stewart conjecture for five or more pegs

Source: https://en.wikipedia.org/wiki/Tower_of_Hanoi#Frame%E2%80%93Stewart_algorithm
Credit: @mgv27

For the Tower of Hanoi with p ≥ 5 pegs and n discs, the Frame–Stewart algorithm uses the
minimum possible number of moves. The four-peg case was proved by Thierry Bousch (2014).

Formalization notes:
* A configuration of `n` discs on `p` pegs is `Fin n → Fin p` (disc `0` is the smallest);
  within a peg discs are stacked in size order, so this determines the position.
* A move takes a disc `d` from peg `a` to peg `b ≠ a`, allowed when no smaller disc is on `a`
  (so `d` is on top) or on `b` (so `d` lands on larger discs).
* `optMoves p n` is the least number of moves taking all discs from peg `0` to peg `p - 1`.
* `fs p n` is the Frame–Stewart number: `fs 3 n = 2^n - 1`, and for `p ≥ 4`,
  `fs p n = n` for `n ≤ 1`, otherwise `min_{1 ≤ k < n} (2 · fs p k + fs (p-1) (n-k))`.
* `main` asserts `optMoves p n = fs p n` for all `p ≥ 5` and all `n`.
-/

namespace OMA.S_wpc_frame_stewart_conjecture

/-- A legal single move from configuration `c` to `c'`. -/
def Move {n p : ℕ} (c c' : Fin n → Fin p) : Prop :=
  ∃ d : Fin n, ∃ b : Fin p, b ≠ c d ∧ c' = Function.update c d b ∧
    ∀ e : Fin n, e < d → c e ≠ c d ∧ c e ≠ b

/-- `c'` is reachable from `c` in exactly `m` legal moves. -/
def ReachIn {n p : ℕ} (c c' : Fin n → Fin p) (m : ℕ) : Prop :=
  ∃ l : List (Fin n → Fin p), l.length = m + 1 ∧ l.head? = some c ∧ l.getLast? = some c' ∧
    l.IsChain Move

/-- The minimum number of moves to transfer `n` discs from peg `0` to peg `p - 1`. -/
noncomputable def optMoves (p n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ (h : 0 < p), ReachIn (fun _ : Fin n => (⟨0, h⟩ : Fin p))
    (fun _ : Fin n => (⟨p - 1, by omega⟩ : Fin p)) m}

/-- The Frame–Stewart number (values for `p < 3` are irrelevant and set to `0`). -/
noncomputable def fs : ℕ → ℕ → ℕ
  | 0, _ => 0
  | 1, _ => 0
  | 2, _ => 0
  | 3, n => 2 ^ n - 1
  | p + 4, n =>
    if n ≤ 1 then n else
      sInf (Set.range fun k : Finset.Ico 1 n =>
        2 * fs (p + 4) k.1 + fs (p + 3) (n - k.1))
termination_by p n => (p, n)
decreasing_by
  all_goals simp_wf
  · have := (Finset.mem_Ico.mp k.2).2
    exact Prod.Lex.right _ this
  · exact Prod.Lex.left _ _ (by omega)

/-- Frame–Stewart conjecture: for `p ≥ 5` pegs the Frame–Stewart algorithm is optimal. -/
theorem main : ∀ p : ℕ, 5 ≤ p → ∀ n : ℕ, optMoves p n = fs p n := by
  sorry

end OMA.S_wpc_frame_stewart_conjecture
