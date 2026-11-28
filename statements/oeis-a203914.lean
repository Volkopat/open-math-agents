import Mathlib

/-!
# A203914: better than Goemans–Williamson Max Cut approximation under the Unique Games Conjecture

Source: https://oeis.org/A203914 (comment by Charles R Greathouse IV, Mar 06 2014)
Credit: @my-other-github-account

The entry records: On the Unique Games Conjecture, a Turing machine can approximate the Max Cut
problem in polynomial time with a better approximation ratio if and only if P = NP.
Here the better ratio means a better ratio than the Goemans–Williamson constant `alphaGW`, the
number whose decimal expansion is A203914 (the entry also quotes their algorithm: a polynomial
time algorithm finding a bipartition that cuts at least `alphaGW * opt` edges).

`main` states: the Unique Games Conjecture implies that (some real `α > alphaGW` admits a
polynomial-time Max Cut `α`-approximation algorithm) if and only if P = NP. The Unique Games
Conjecture is kept as a genuine hypothesis, stated in its usual form (Khot, 2002) below; it is not
replaced by any of its consequences for Max Cut.

Conventions, each fixed explicitly.

* Machines. Polynomial time is Mathlib's `Turing.TM2ComputableInPolyTime` (deterministic
  multi-stack machines with a finite input alphabet, finitely many states and labels; since the
  state type is finite, a run only ever writes finitely many distinct stack symbols).
* Bit strings. A natural number is written in binary (`Nat.bits`) inside a self-delimiting
  block `delimit` (each payload bit `b` becomes `true, b`, then `false`), as in the
  `BitstringEncoding` of formal-conjectures.
* P and NP are the usual classes of decision problems `List Bool → Bool`, following
  `ComplexityTheory.P` and `ComplexityTheory.NP` of formal-conjectures (Arora–Barak, Def. 2.1):
  NP uses a polynomial witness bound and a polynomial-time verifier reading the pair
  `delimit x ++ w`. P = NP is equality of the two classes.
* Max Cut. The input is a finite simple unweighted graph on `Fin n`, given by its full row-major
  adjacency matrix (`n * n` bits; the vertex count is determined by the length). The algorithm
  must output a bipartition `c : Fin n → Bool` (as the `n` bits `c 0, …, c (n-1)`) cutting at
  least `α * opt` edges, where `opt` is the maximum cut. This is the notion of approximation used
  for the Goemans–Williamson algorithm in the entry.
* `alphaGW` is the infimum of `2 arccos ρ / (π (1 - ρ))` over `-1 ≤ ρ < 1`, which equals the usual
  `min_{0 < θ ≤ π} (2 / π) θ / (1 - cos θ) = 0.8785672…` (A203914).
* Unique Games. An instance has `vertices` vertices, label set `Fin labels`, and a list of
  constraints, each an ordered pair of vertices `(u, v)` with a permutation `π` of the labels; a
  labeling `σ` satisfies it when `σ v = π (σ u)`. Repeated constraints are allowed (multiplicity
  counts). The conjecture: for all `ε, δ > 0` there is a label count `q` such that every NP
  language reduces in polynomial time to Unique Games instances with `q` labels so that YES inputs
  give a nonempty instance with a labeling satisfying at least a `1 - ε` fraction of the
  constraints, and NO inputs give instances where every labeling satisfies at most a `δ`
  fraction. Equivalently, Gap-Unique-Games(1 - ε, δ) on `q` labels is NP-hard.
-/

namespace OMA.S_oeis_a203914

open Turing

/-! ## Bit strings -/

/-- Self-delimiting block: each payload bit `b` becomes `true, b`, terminated by `false`. -/
def delimit : List Bool → List Bool
  | [] => [false]
  | b :: l => true :: b :: delimit l

/-- A natural number in binary, as a self-delimiting block. -/
def natBits (n : ℕ) : List Bool := delimit n.bits

/-! ## P and NP -/

/-- A decision problem on bit strings. -/
abbrev DecisionProblem := List Bool → Bool

/-- Decision problems decidable in polynomial time by a deterministic machine. -/
def P : Set DecisionProblem :=
  {L | Nonempty (TM2ComputableInPolyTime id (fun b : Bool => [b]) L)}

/-- The input-witness pair read by an NP verifier. -/
def pairBits (p : List Bool × List Bool) : List Bool := delimit p.1 ++ p.2

/-- Decision problems with polynomially bounded witnesses checked in polynomial time. -/
def NP : Set DecisionProblem :=
  {L | ∃ (p : Polynomial ℕ) (R : List Bool × List Bool → Bool),
    Nonempty (TM2ComputableInPolyTime pairBits (fun b : Bool => [b]) R) ∧
    ∀ x, L x = true ↔ ∃ w : List Bool, w.length ≤ p.eval x.length ∧ R (x, w) = true}

/-! ## Max Cut -/

/-- The Goemans–Williamson constant (A203914). -/
noncomputable def alphaGW : ℝ :=
  sInf ((fun ρ : ℝ => 2 * Real.arccos ρ / (Real.pi * (1 - ρ))) '' Set.Ico (-1 : ℝ) 1)

open Classical in
/-- The number of edges of `G` crossing the bipartition `c`, each edge counted once. -/
noncomputable def cutSize {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.Adj p.1 p.2 ∧ c p.1 ≠ c p.2).card

/-- The maximum cut of `G`. -/
noncomputable def maxCut {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  Finset.univ.sup (cutSize G)

open Classical in
/-- The row-major adjacency matrix of `G`. -/
noncomputable def graphBits {n : ℕ} (G : SimpleGraph (Fin n)) : List Bool :=
  (List.finRange n).flatMap fun u => (List.finRange n).map fun v => decide (G.Adj u v)

/-- A polynomial-time algorithm that, on every graph, outputs a bipartition cutting at least
`α` times the maximum number of edges. -/
def ApproximatesMaxCut (α : ℝ) : Prop :=
  ∃ algorithm : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime id id algorithm) ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), ∃ c : Fin n → Bool,
      algorithm (graphBits G) = List.ofFn c ∧ α * (maxCut G : ℝ) ≤ (cutSize G c : ℝ)

/-! ## Unique Games -/

/-- A constraint `σ v = π (σ u)` between two vertices. -/
structure UGConstraint (n q : ℕ) where
  u : Fin n
  v : Fin n
  perm : Equiv.Perm (Fin q)

/-- A Unique Games instance with label set `Fin labels`. -/
structure UGInstance where
  vertices : ℕ
  labels : ℕ
  constraints : List (UGConstraint vertices labels)

/-- The number of constraints satisfied by the labeling `σ`. -/
def UGInstance.satisfied (I : UGInstance) (σ : Fin I.vertices → Fin I.labels) : ℕ :=
  (I.constraints.filter fun c => decide (σ c.v = c.perm (σ c.u))).length

/-- Vertex count, label count, constraint count, then each constraint as its two endpoints
and the table of its permutation. -/
def ugBits (I : UGInstance) : List Bool :=
  natBits I.vertices ++ natBits I.labels ++ natBits I.constraints.length ++
    I.constraints.flatMap fun c =>
      natBits c.u ++ natBits c.v ++ (List.finRange I.labels).flatMap fun a => natBits (c.perm a)

/-- The Unique Games Conjecture (Khot, 2002): for all `ε, δ > 0` there is a number of labels `q`
such that Gap-Unique-Games(1 - ε, δ) with `q` labels is NP-hard under polynomial-time
reductions. -/
def UniqueGamesConjecture : Prop :=
  ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∃ q : ℕ, ∀ L ∈ NP,
    ∃ f : List Bool → UGInstance, Nonempty (TM2ComputableInPolyTime id ugBits f) ∧
      ∀ x, (f x).labels = q ∧
        (L x = true → 0 < (f x).constraints.length ∧
          ∃ σ, (1 - ε) * ((f x).constraints.length : ℝ) ≤ ((f x).satisfied σ : ℝ)) ∧
        (L x = false → ∀ σ, ((f x).satisfied σ : ℝ) ≤ δ * ((f x).constraints.length : ℝ))

/-- A203914: under the Unique Games Conjecture, Max Cut has a polynomial-time approximation
algorithm with a ratio better than `alphaGW` if and only if P = NP. -/
theorem main : UniqueGamesConjecture →
    ((∃ α : ℝ, alphaGW < α ∧ ApproximatesMaxCut α) ↔ P = NP) := by
  sorry

end OMA.S_oeis_a203914
