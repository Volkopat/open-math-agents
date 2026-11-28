import Mathlib

/-!
# Unique games conjecture

Source: https://en.wikipedia.org/wiki/Unique_games_conjecture
Credit: @my-other-github-account

The source (section Unique label cover) states: for every sufficiently small pair of constants
`ε, δ > 0`, there exists a natural number `k` such that the `(1 - δ, ε)`-gap label-cover problem with
unique constraints with `k` colors is NP-hard.

Conventions chosen here, each stated because the source leaves it implicit.

* Instance. A finite directed graph on the vertices `Fin n`, given as a nonempty list of edges with
  no repeated ordered pair, each edge `e = (u, v)` carrying a permutation `π_e` of the colors
  `Fin k`. A coloring `a` satisfies the edge when `a v = π_e (a u)`, as in the source. The graph is
  required to have at least one edge so that the fraction of satisfied constraints is defined.
* Value. The value is the largest fraction of edges satisfied by a coloring. In `main`, value at
  least `c` is written as the existence of a coloring satisfying at least that fraction, and value
  at most `s` as every coloring satisfying at most that fraction.
* Sufficiently small. Read as: there is `ε₀ > 0` such that the claim holds for all `ε, δ` in
  `(0, ε₀)`.
* NP-hard. Every language in NP has a polynomial-time many-one reduction to the promise problem:
  members are sent to instances of value at least `1 - δ`, non-members to instances of value at
  most `ε`. Machines are Mathlib Turing machines `Turing.FinTM2` running within a polynomial bound
  in the input length (`Turing.TM2ComputableInPolyTime`), with every stack alphabet finite
  (Mathlib only requires this of the input stack).
* NP. A language of bit strings is in NP when it has a polynomial-time verifier with polynomially
  bounded witnesses (Arora-Barak, Definition 2.1). The verifier reads the input and the witness as
  one bit string: the length of the input in unary, a separator, the input, then the witness.
* Encoding of an instance. A natural number `m` is written in unary as `m` ones followed by a zero.
  An instance is the list of numbers `n, k`, the number of edges, then for each edge in order its
  source, its target and the images `π_e 0, ..., π_e (k - 1)`, each written in this way. Numbers
  in an instance are bounded by its size up to the fixed `k`, so unary costs only a polynomial.

The definitions of the instance encoding and of the verifier follow the Lean development of
OpenAI, The Unique Games Theorem (2026), https://github.com/openai/math (lean/ComparatorChallenges/
UniqueGamesTheorem.lean and lean/OAI/Computability/UniqueGames/Machines/MachineLemmas.lean at
commit 3344da59991ed94f9ba711217b29c1d760badfa6), whose formalization claims this result.
-/

namespace OMA.S_wp_unique_games_conjecture

open Turing

/-- An instance of label cover with unique constraints with `k` colors. -/
structure Instance (k : ℕ) where
  /-- number of vertices -/
  n : ℕ
  /-- the edges `(u, v)` with their permutations of the colors -/
  edges : List (Fin n × Fin n × Equiv.Perm (Fin k))
  nonempty : edges ≠ []
  /-- no ordered pair of vertices carries two edges -/
  simple : (edges.map fun e => (e.1, e.2.1)).Nodup

/-- The number of edges `(u, v)` with permutation `π` such that `a v = π (a u)`. -/
def Instance.satisfied {k : ℕ} (G : Instance k) (a : Fin G.n → Fin k) : ℕ :=
  (G.edges.filter fun e => decide (a e.2.1 = e.2.2 (a e.1))).length

/-- The fraction of the edges satisfied by the coloring `a`. -/
noncomputable def Instance.fraction {k : ℕ} (G : Instance k) (a : Fin G.n → Fin k) : ℝ :=
  (G.satisfied a : ℝ) / G.edges.length

/-- `m` in unary: `m` ones and a zero. -/
def unary (m : ℕ) : List Bool := List.replicate m true ++ [false]

/-- The bit string of an instance. -/
def Instance.bits {k : ℕ} (G : Instance k) : List Bool :=
  ([G.n, k, G.edges.length] ++
      G.edges.flatMap fun e => [e.1.val, e.2.1.val] ++ List.ofFn fun i : Fin k => (e.2.2 i).val).flatMap
    unary

/-- A machine with every stack alphabet finite. -/
def FiniteStacks (M : FinTM2) : Prop := ∀ s, Finite (M.Γ s)

/-- A function computable in polynomial time by a machine with finite stack alphabets. -/
def PolyTime {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (f : α → β) : Prop :=
  ∃ c : TM2ComputableInPolyTime ea eb f, FiniteStacks c.tm

/-- The input and the witness given to a verifier as one bit string. -/
def pairBits (x : List Bool × List Bool) : List Bool := unary x.1.length ++ x.1 ++ x.2

/-- The class NP of languages of bit strings. -/
def InNP (L : List Bool → Prop) : Prop :=
  ∃ (p : Polynomial ℕ) (V : List Bool × List Bool → Bool),
    PolyTime pairBits (fun b => [b]) V ∧
      ∀ x, L x ↔ ∃ w : List Bool, w.length ≤ p.eval x.length ∧ V (x, w) = true

/-- The `(c, s)`-gap label-cover problem with unique constraints with `k` colors is NP-hard. -/
def GapNPHard (k : ℕ) (c s : ℝ) : Prop :=
  ∀ L : List Bool → Prop, InNP L →
    ∃ f : List Bool → Instance k, PolyTime id Instance.bits f ∧
      ∀ x, (L x → ∃ a, c ≤ (f x).fraction a) ∧ (¬ L x → ∀ a, (f x).fraction a ≤ s)

theorem main : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε δ : ℝ, 0 < ε → ε < ε₀ → 0 < δ → δ < ε₀ →
    ∃ k : ℕ, GapNPHard k (1 - δ) ε := by
  sorry

end OMA.S_wp_unique_games_conjecture
