import FormalConjectures.ErdosProblems.«1158»

-- Reduction Erdos1158.erdos_1158.R1 of Erdős Problem 1158
-- Credit: @sntntHb
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Sketch: the target asks for ex_t(n, K_t(r)) ≥ n^(t - r^(1-t) - ε) for all t, r ≥ 2.
-- Different pairs (t, r) forbid different hypergraphs with different exponents, so no case
-- implies another. We split off the two graph cases that are known theorems (not in Mathlib):
--   H1: t = 2, r = 2, exponent 3/2: ex(n, C4) ≫ n^(3/2) (Erdős-Rényi-Sós, Brown 1966),
--   H2: t = 2, r = 3, exponent 5/3: ex(n, K_{3,3}) ≫ n^(5/3) (Brown 1966),
--   H3: every other pair: t = 2 with r ≥ 4, or t ≥ 3 (open).
-- main: case analysis on (t, r). No computer search was used.

namespace OMA.R_Erdos1158_erdos_1158_R1

open Filter Asymptotics

/-- The case t = 2, r = 2 (four-cycle-free graphs). -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ (((2 : ℕ) : ℝ) - ((2 : ℕ) : ℝ) ^ (1 - ((2 : ℕ) : ℝ)) - ε) ≤
      (Hypergraph.partiteExtremalNumber n 2 2 : ℝ)

/-- The case t = 2, r = 3 (K_{3,3}-free graphs). -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ (((2 : ℕ) : ℝ) - ((3 : ℕ) : ℝ) ^ (1 - ((2 : ℕ) : ℝ)) - ε) ≤
      (Hypergraph.partiteExtremalNumber n 2 3 : ℝ)

/-- All remaining pairs: t = 2 with r ≥ 4, or t ≥ 3. -/
def H3 : Prop :=
  ∀ t r : ℕ, 2 ≤ t → 2 ≤ r → (3 ≤ t ∨ 4 ≤ r) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ ((t : ℝ) - (r : ℝ) ^ (1 - (t : ℝ)) - ε) ≤
        (Hypergraph.partiteExtremalNumber n t r : ℝ)

theorem main : H1 → H2 → H3 → type_of% @Erdos1158.erdos_1158 := by
  intro h1 h2 h3 t r ht hr
  rcases (by omega : (t = 2 ∧ r = 2) ∨ (t = 2 ∧ r = 3) ∨ (3 ≤ t ∨ 4 ≤ r)) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
  · exact h1
  · exact h2
  · exact h3 t r ht hr h

end OMA.R_Erdos1158_erdos_1158_R1
