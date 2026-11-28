import OMAReductions.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R1

-- Reduction Arxiv.2610.08796.exists_isPolyTime_bayesNash.R1.H2.R2 of step Arxiv.2610.08796.exists_isPolyTime_bayesNash.R1.H2
-- Credit: @tatashbar
-- Each H becomes its own step once this file is accepted. Proving all of them closes R1.H2.

/-!
One rational linear system for the equilibria with a fixed exact pattern `S`.

As in the description of `R1.H2`, the outputs `e = (c, p)` with pattern `S` that are Bayes–Nash
equilibria are the points of one polyhedron in the `m + n * m` variables `c_t`, `p_{θ,t}`
(`m` targets, `n` types): bounds `0 ≤ c_t ≤ 1`, pins `c_t = 0` and `c_t = 1` off the pattern,
`∑ c_t = g.1`, `p_{θ,t} ≥ 0`, pins `p_{θ,t} = 0` off the pattern, `∑_t p_{θ,t} = 1`, the attacker
inequalities on the supports (linear in `c`) and the defender exchange inequalities between
positive and non-full targets (linear in `p`).

A linear system is a pair `(d, cons)`. The number of variables is `d.length`; a row `(a, b)` of
`cons` reads `∑_j a_j x_j ≤ b`. The number of variables is given in unary because a solution is a
list of that length, and a polynomial-time machine can only write an output whose length is
polynomial in the length of its input.

* `H1`: exact rational linear feasibility in polynomial time (Khachiyan), for systems in this form.
* `H2`: a polynomial-time map `build` from `(g, S)` to such a system and a polynomial-time map
  `dec` from a solution to an output, complete (an equilibrium with pattern `S` gives a solution)
  and sound (every solution decodes to an equilibrium, for every `S`).
* `H3`: polynomial time is closed under `x ↦ dec (x.1, lpSolve (build x))`.
-/

namespace OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R1_H2_R2

open ComplexityTheory Arxiv.«2610.08796»

/-- Exact rational linear feasibility: if the system `(d, cons)` in `d.length` variables has a
rational solution, `lpSolve (d, cons)` is one. -/
def H1 : Prop :=
  ∃ lpSolve : List Bool × List (List ℚ × ℚ) → List ℚ,
    IsPolyTime lpSolve ∧
    ∀ (d : List Bool) (cons : List (List ℚ × ℚ)),
      (∃ x : List ℚ, x.length = d.length ∧
        ∀ r ∈ cons, (∑ j : Fin d.length, r.1[j.val]?.getD 0 * x[j.val]?.getD 0) ≤ r.2) →
      (lpSolve (d, cons)).length = d.length ∧
      ∀ r ∈ cons,
        (∑ j : Fin d.length, r.1[j.val]?.getD 0 * (lpSolve (d, cons))[j.val]?.getD 0) ≤ r.2

/-- The linear system of a pattern: polynomial-time construction and decoding, completeness for
equilibria with exactly that pattern, soundness for every pattern. -/
def H2 : Prop :=
  ∃ (build : GameInput × (List Bool × List Bool × List (List Bool)) →
      List Bool × List (List ℚ × ℚ))
    (dec : GameInput × List ℚ → EquilibriumOutput),
    IsPolyTime build ∧ IsPolyTime dec ∧
    ∀ (g : GameInput) (S : List Bool × List Bool × List (List Bool)), g.Valid →
      ((∃ e : EquilibriumOutput, g.IsBayesNash e ∧
        ∀ t : Fin g.numTargets,
          (S.1[t.val]?.getD false = true ↔ 0 < e.1[t.val]?.getD 0) ∧
          (S.2.1[t.val]?.getD false = true ↔ e.1[t.val]?.getD 0 < 1) ∧
          ∀ θ : Fin g.numTypes,
            ((S.2.2[θ.val]?.getD [])[t.val]?.getD false = true ↔
              0 < (e.2[θ.val]?.getD [])[t.val]?.getD 0)) →
        ∃ x : List ℚ, x.length = (build (g, S)).1.length ∧
          ∀ r ∈ (build (g, S)).2,
            (∑ j : Fin (build (g, S)).1.length, r.1[j.val]?.getD 0 * x[j.val]?.getD 0) ≤ r.2) ∧
      ∀ x : List ℚ, x.length = (build (g, S)).1.length →
        (∀ r ∈ (build (g, S)).2,
          (∑ j : Fin (build (g, S)).1.length, r.1[j.val]?.getD 0 * x[j.val]?.getD 0) ≤ r.2) →
        g.IsBayesNash (dec (g, x))

/-- Polynomial time is closed under `x ↦ dec (x.1, lpSolve (build x))`. -/
def H3 : Prop :=
  ∀ (build : GameInput × (List Bool × List Bool × List (List Bool)) →
      List Bool × List (List ℚ × ℚ))
    (lpSolve : List Bool × List (List ℚ × ℚ) → List ℚ)
    (dec : GameInput × List ℚ → EquilibriumOutput),
    IsPolyTime build → IsPolyTime lpSolve → IsPolyTime dec →
    IsPolyTime (fun x : GameInput × (List Bool × List Bool × List (List Bool)) =>
      dec (x.1, lpSolve (build x)))

theorem main : H1 → H2 → H3 → OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R1.H2 := by
  intro h1 h2 h3
  obtain ⟨lpSolve, hlp, hlpspec⟩ := h1
  obtain ⟨build, dec, hb, hd, hspec⟩ := h2
  refine ⟨fun x => dec (x.1, lpSolve (build x)), h3 build lpSolve dec hb hlp hd, ?_⟩
  intro g S hg hpat
  obtain ⟨hcomp, hsound⟩ := hspec g S hg
  obtain ⟨hlen, hsat⟩ := hlpspec (build (g, S)).1 (build (g, S)).2 (hcomp hpat)
  exact hsound (lpSolve (build (g, S))) hlen hsat

end OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R1_H2_R2
