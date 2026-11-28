import Mathlib

/-!
# Erdős Problem 809

Source: https://www.erdosproblems.com/809
Credit: @mgv27

Define the anti-Ramsey number $\chi_S(n,e,G)$ as the smallest $r$ such that there is a graph
with $n$ vertices and $e$ edges with an $r$-colouring of its edges in which every copy of $G$ has
entirely distinct edge colours. Is it true that, for all $k\geq 3$,
\[\chi_S(n, \lfloor n^2/4\rfloor+1,C_{2k+1})\sim n^2/8?\]

Formalization notes:
* The source records that the question was answered affirmatively for all `k ≥ 4` by Bucić,
  Chen and Ma, so `main` states the remaining open case `k = 3`, i.e. `G = C_7`.
* `χ_S(n, e, C_L)` is defined literally as on the page: the least `r` for which some simple graph
  on `Fin n` with exactly `e` edges has an edge colouring with `r` colours (a map
  `Sym2 (Fin n) → Fin r`; its values off the edge set are irrelevant) such that every copy of
  `C_L` is rainbow.
* A copy of `C_L` is an injective map `f : Fin L → Fin n` with `f i` adjacent to `f (i + 1)` for
  every `i` (addition in `Fin L` wraps around); it is rainbow if the `L` edges
  `s(f i, f (i + 1))` receive pairwise distinct colours.
* The set of admissible `r` is nonempty once `e ≤ n(n-1)/2` (give every edge its own colour),
  which holds for `e = ⌊n²/4⌋ + 1` and all `n ≥ 3`, so `sInf` is meaningful for large `n`.
* `∼ n²/8` is stated as `χ_S(n, ⌊n²/4⌋+1, C_7) / (n²/8) → 1` as `n → ∞`.
* Burr, Erdős, Graham and Sós proved the lower bound `≫_k n²`.
-/

namespace OMA.S_erdos_809

open Filter Topology

/-- The `L` edges of the cycle traced by `f : Fin L → Fin n` get pairwise distinct colours
under `c`. -/
def RainbowCycle {n L r : ℕ} [NeZero L] (c : Sym2 (Fin n) → Fin r) (f : Fin L → Fin n) :
    Prop :=
  Function.Injective (fun i : Fin L => c s(f i, f (i + 1)))

/-- `f` is a copy of the cycle `C_L` in `G`. -/
def IsCycleCopy {n L : ℕ} [NeZero L] (G : SimpleGraph (Fin n)) (f : Fin L → Fin n) : Prop :=
  Function.Injective f ∧ ∀ i : Fin L, G.Adj (f i) (f (i + 1))

/-- The anti-Ramsey number `χ_S(n, e, C_L)`: the least `r` such that some graph on `n` vertices
with `e` edges has an `r`-colouring of its edges in which every copy of `C_L` is rainbow. -/
noncomputable def chiS (n e L : ℕ) [NeZero L] : ℕ :=
  sInf {r : ℕ | ∃ G : SimpleGraph (Fin n), G.edgeSet.ncard = e ∧
    ∃ c : Sym2 (Fin n) → Fin r, ∀ f : Fin L → Fin n, IsCycleCopy G f → RainbowCycle c f}

/-- Erdős Problem 809, case `k = 3`: is `χ_S(n, ⌊n²/4⌋+1, C_7) ∼ n²/8`? -/
theorem main :
    Tendsto (fun n : ℕ => (chiS n (n ^ 2 / 4 + 1) 7 : ℝ) / ((n : ℝ) ^ 2 / 8)) atTop (𝓝 1) := by
  sorry

end OMA.S_erdos_809
