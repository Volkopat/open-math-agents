import Mathlib

/-!
# Erdős Problem 811

Source: https://www.erdosproblems.com/811
Credit: @mgv27

Suppose $n\equiv 1\pmod{m}$. We say that an edge-colouring of $K_n$ using $m$ colours is
balanced if every vertex sees exactly $\lfloor n/m\rfloor$ many edges of each colours. For which
graphs $G$ is it true that, if $m=e(G)$, for all large $n\equiv 1\pmod{m}$, every balanced
edge-colouring of $K_n$ with $m$ colours contains a rainbow copy of $G$? (That is, a subgraph
isomorphic to $G$ where each edge receives a different colour.)

Formalization notes:
* The general question ("for which graphs") is a characterisation, so `main` states the specific
  challenge recorded on the source page from [Er91] and [Er96]: must every balanced edge-colouring
  of `K_n` (`n ≡ 1 mod 6`, `n` large) with `6` colours contain a rainbow `C_6`? The other half of
  that challenge, `K_4`, was settled negatively by Clemen and Wagner, so it is not stated.
* `K_n` has vertex set `Fin n`; a colouring is a map `Sym2 (Fin n) → Fin 6`, of which only the
  values on non-diagonal pairs matter.
* Balanced: for every vertex `v` and colour `j`, exactly `⌊n/6⌋` vertices `w ≠ v` have
  `s(v, w)` coloured `j` (with `n ≡ 1 mod 6` these account for all `n - 1` edges at `v`).
* A rainbow `C_6` is an injective `f : Fin 6 → Fin n` such that the six edges
  `s(f i, f (i + 1))` (indices mod 6) receive six distinct colours.
* "For all large `n`" is: there is `N₀` such that the conclusion holds for every `n ≥ N₀` with
  `n % 6 = 1`.
-/

namespace OMA.S_erdos_811

/-- The colouring `c` of `K_n` with `6` colours is balanced: every vertex sees exactly
`⌊n/6⌋` edges of each colour. -/
def Balanced {n : ℕ} (c : Sym2 (Fin n) → Fin 6) : Prop :=
  ∀ v : Fin n, ∀ j : Fin 6,
    (Finset.univ.filter (fun w : Fin n => w ≠ v ∧ c s(v, w) = j)).card = n / 6

/-- `f` traces a rainbow `6`-cycle in `K_n` under `c`. -/
def RainbowC6 {n : ℕ} (c : Sym2 (Fin n) → Fin 6) (f : Fin 6 → Fin n) : Prop :=
  Function.Injective f ∧ Function.Injective (fun i : Fin 6 => c s(f i, f (i + 1)))

/-- Erdős Problem 811 (the `C_6` challenge): for all large `n ≡ 1 (mod 6)`, every balanced
edge-colouring of `K_n` with `6` colours contains a rainbow `C_6`. -/
theorem main : ∃ N₀ : ℕ, ∀ n ≥ N₀, n % 6 = 1 →
    ∀ c : Sym2 (Fin n) → Fin 6, Balanced c → ∃ f : Fin 6 → Fin n, RainbowC6 c f := by
  sorry

end OMA.S_erdos_811
