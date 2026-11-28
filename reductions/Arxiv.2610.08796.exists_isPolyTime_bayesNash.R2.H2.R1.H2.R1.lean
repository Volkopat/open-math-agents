import OMAReductions.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2_H2_R1

-- Reduction Arxiv.2610.08796.exists_isPolyTime_bayesNash.R2.H2.R1.H2.R1 of step R2.H2.R1.H2
-- Credit: @paynebrowning
-- Each H becomes its own step once this file is accepted. Proving all of them closes R2.H2.R1.H2.

/-!
Rational LP reduction of `R2.H2.R1.H2` (computing an equilibrium attacker strategy profile `p`
given `(g, lam, x)` where `x` extends to a fixed-`lam` equilibrium).

Once `(g, lam, x)` is fixed, every attacker type's expected utility `uA θ t` at every target `t`
is fixed, so finding a matching attacker strategy profile `p_{θ,t}` reduces to a single rational
linear inequality system `A y ≤ b` in `n * m` variables:
- `y_{θ,t} ≥ 0` and `∑_t y_{θ,t} = 1` for each attacker type `θ`;
- `y_{θ,t} = 0` whenever `t` is strictly suboptimal for type `θ` under `x`;
- `gain(t, y) ≥ lam` whenever `x_t > 0`, and `gain(t, y) ≤ lam` whenever `x_t < 1`.

* `H1`: General exact rational LP feasibility in `IsPolyTime` (Khachiyan's theorem) for
  well-formed systems `(n, cons)` whose constraint rows have length `n` (with `n = 0 ∨ cons ≠ []`,
  ensuring `n` is bounded by the input bit-length).
* `H2`: Polynomial-time construction of the fixed-coverage attacker-strategy rational LP from
  `((g, lam), x)`, with row-length well-formedness, completeness, and soundness.
* `H3`: Polynomial-time composition and flat-to-2D list reshaping of the `n * m` LP solution into
  `n` rows of length `m`.
-/

namespace OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2_H2_R1_H2_R1

open ComplexityTheory Arxiv.«2610.08796»

/-- Exact rational linear programming feasibility is computable in polynomial time:
given `(n, cons)` representing `∑_j a_j x_j ≤ b` for `(a, b) ∈ cons`, where every row has
length `n` and `n = 0 ∨ cons ≠ []` (so `n` is bounded by the bit-length of the input), if a
feasible `x ∈ ℚ^n` exists, `lpSolve (n, cons)` returns one. -/
def H1 : Prop :=
  ∃ lpSolve : (ℕ × List (List ℚ × ℚ)) → List ℚ,
    IsPolyTime lpSolve ∧
    ∀ (n : ℕ) (cons : List (List ℚ × ℚ)),
      (∀ r ∈ cons, r.1.length = n) → (n = 0 ∨ cons ≠ []) →
      (∃ x : List ℚ, x.length = n ∧
        ∀ r ∈ cons, (∑ j : Fin n, r.1[j.val]?.getD 0 * x[j.val]?.getD 0) ≤ r.2) →
      (lpSolve (n, cons)).length = n ∧
      ∀ r ∈ cons, (∑ j : Fin n, r.1[j.val]?.getD 0 * (lpSolve (n, cons))[j.val]?.getD 0) ≤ r.2

/-- Polynomial-time construction of the fixed-coverage attacker-strategy rational LP from
`((g, lam), x)`, with row-length well-formedness, completeness from any fixed-`lam` attacker
profile for `x`, and soundness from any feasible flat solution vector `y`. -/
def H2 : Prop :=
  ∃ bP : (GameInput × ℚ) × List ℚ → ℕ × List (List ℚ × ℚ),
    IsPolyTime bP ∧
    ∀ (g : GameInput) (lam : ℚ) (x : List ℚ), g.Valid →
      let lp := bP ((g, lam), x)
      let cov (t : Fin g.numTargets) := x[t.val]?.getD 0
      let uA (θ : Fin g.numTypes) (t : Fin g.numTargets) :=
        (1 - cov t) * (g.attackerPayoff θ t).1 + cov t * (g.attackerPayoff θ t).2
      let gain (atk : Fin g.numTypes → Fin g.numTargets → ℚ) (t : Fin g.numTargets) :=
        (∑ θ : Fin g.numTypes, g.prior θ * atk θ t) *
          ((g.defenderPayoff t).2 - (g.defenderPayoff t).1)
      (∀ r ∈ lp.2, r.1.length = lp.1) ∧ (lp.1 = 0 ∨ lp.2 ≠ []) ∧
      ((∃ atk : Fin g.numTypes → Fin g.numTargets → ℚ,
        (∀ θ, (∑ t, atk θ t) = 1 ∧ ∀ t, 0 ≤ atk θ t) ∧
        (∀ θ t s, 0 < atk θ t → uA θ s ≤ uA θ t) ∧
        (∀ t, 0 < cov t → lam ≤ gain atk t) ∧
        (∀ t, cov t < 1 → gain atk t ≤ lam)) →
        ∃ y : List ℚ, y.length = lp.1 ∧
          ∀ r ∈ lp.2, (∑ j : Fin lp.1, r.1[j.val]?.getD 0 * y[j.val]?.getD 0) ≤ r.2) ∧
      (∀ y : List ℚ, y.length = lp.1 →
        (∀ r ∈ lp.2, (∑ j : Fin lp.1, r.1[j.val]?.getD 0 * y[j.val]?.getD 0) ≤ r.2) →
        let atk (θ : Fin g.numTypes) (t : Fin g.numTargets) :=
          y[θ.val * g.numTargets + t.val]?.getD 0
        (∀ θ, (∑ t, atk θ t) = 1 ∧ ∀ t, 0 ≤ atk θ t) ∧
        (∀ θ t s, 0 < atk θ t → uA θ s ≤ uA θ t) ∧
        (∀ t, 0 < cov t → lam ≤ gain atk t) ∧
        (∀ t, cov t < 1 → gain atk t ≤ lam))

/-- Polynomial-time composition and flat-to-2D list reshaping for the attack LP solver. -/
def H3 : Prop :=
  ∀ (bP : (GameInput × ℚ) × List ℚ → ℕ × List (List ℚ × ℚ))
    (lpSolve : ℕ × List (List ℚ × ℚ) → List ℚ),
    IsPolyTime bP → IsPolyTime lpSolve →
    IsPolyTime (fun z : (GameInput × ℚ) × List ℚ =>
      List.ofFn fun θ : Fin z.1.1.numTypes =>
        List.ofFn fun t : Fin z.1.1.numTargets =>
          (lpSolve (bP z))[θ.val * z.1.1.numTargets + t.val]?.getD 0)

theorem main : H1 → H2 → H3 → OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2_H2_R1.H2 := by
  intro h1 h2 h3
  obtain ⟨lpSolve, hlp_pt, hlp_spec⟩ := h1
  obtain ⟨bP, hbP_pt, hspec⟩ := h2
  refine ⟨fun z =>
    List.ofFn fun θ : Fin z.1.1.numTypes =>
      List.ofFn fun t : Fin z.1.1.numTargets =>
        (lpSolve (bP z))[θ.val * z.1.1.numTargets + t.val]?.getD 0,
    h3 bP lpSolve hbP_pt hlp_pt, ?_⟩
  intro g lam x hg hex
  obtain ⟨p0, hxlen, _, hcov_sum, hcov_bnds, hp0_rows, hp0_br, hp0_lo, hp0_hi⟩ := hex
  obtain ⟨hrow_len, hnonempty, hcomp, hsound⟩ := hspec g lam x hg
  have hfeas := hcomp ⟨fun θ t => (p0[θ.val]?.getD [])[t.val]?.getD 0,
    fun θ => ⟨(hp0_rows θ).2.1, (hp0_rows θ).2.2⟩, hp0_br, hp0_lo, hp0_hi⟩
  obtain ⟨hlen, hsat⟩ := hlp_spec (bP ((g, lam), x)).1 (bP ((g, lam), x)).2 hrow_len hnonempty hfeas
  obtain ⟨hrows, hbr, hlo, hhi⟩ := hsound (lpSolve (bP ((g, lam), x))) hlen hsat
  have hget : ∀ (θ : Fin g.numTypes) (t : Fin g.numTargets),
      (((List.ofFn fun θ : Fin g.numTypes =>
          List.ofFn fun t : Fin g.numTargets =>
            (lpSolve (bP ((g, lam), x)))[θ.val * g.numTargets + t.val]?.getD 0)[θ.val]?.getD
          [])[t.val]?.getD 0) =
      (lpSolve (bP ((g, lam), x)))[θ.val * g.numTargets + t.val]?.getD 0 := by
    intro θ t
    simp
  refine ⟨hxlen, by simp, hcov_sum, hcov_bnds, ?_, ?_, ?_, ?_⟩
  · intro θ
    refine ⟨by simp, ?_, ?_⟩
    · simpa [hget] using (hrows θ).1
    · intro t
      simpa [hget] using (hrows θ).2 t
  · intro θ t s hpos
    exact hbr θ t s (by simpa [hget] using hpos)
  · intro t hpos
    simpa [hget] using hlo t hpos
  · intro t hlt
    simpa [hget] using hhi t hlt

end OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2_H2_R1_H2_R1
