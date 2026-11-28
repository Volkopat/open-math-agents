import FormalConjectures.Arxiv.«2610.08796».BayesianSecurityGames

-- Reduction Arxiv.2610.08796.exists_isPolyTime_bayesNash.R3 of Computing Bayes–Nash equilibria in Bayesian simple security games
-- Credit: @paynebrowning (formalizing the algorithm of Shiva Kintali, SecurityGames-short.pdf, Nov 24, 2026)
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
Modular reduction of `Arxiv.2610.08796.exists_isPolyTime_bayesNash` formalizing the deterministic
polynomial-time algorithm of Shiva Kintali,
*A Polynomial-Time Algorithm for Exact Equilibria in Bayesian Simple Security Games*
(`SecurityGames-short.pdf`, November 24, 2026).

Kintali's algorithm computes an exact rational Bayes–Nash equilibrium in polynomial bit time via
four cleanly separated components:

* `H1` (Exact Rational LP Feasibility): General polynomial-time exact rational linear programming
  feasibility (Khachiyan / Schrijver) for well-formed systems `(n, cons)` with row length `n` and
  `n = 0 ∨ cons ≠ []`.
* `H2` (Pattern LP, Exact Recovery & Decoding — Section 1 & Lemma 2 of Kintali): Polynomial-time
  computation of the exact-recovery tolerance `eta g = 1 / (4 H)` (via Cramér's rule and Hadamard's
  determinant bound `H = (n C)^n`), the exact pattern linear system `patLP (g, x)` of a trial
  coverage `x`, and equilibrium decoding `decode (g, y)` (recovering `q_{ij} / π_i` for retained
  types and assigning best responses for zero-prior types). Any feasible LP solution decodes to an
  exact Bayes–Nash equilibrium, and any `eta g`-relaxed equilibrium coverage yields a feasible
  pattern LP (Lemma 2).
* `H3` (Grouped Quota-Sweep & Fixed-Witness Blocker Oracle — Section 2 & Lemmas 3–6 of Kintali):
  For any valid game `g` and tolerance `η > 0`, polynomial-time computation of the coverage grid
  size `G = grid (g, η) ≥ 1` and the grouped ordinal-transportation quota sweep `sweep ((g, η), Q)`
  returning a trial coverage `x` and blocker intervals `B[i][j] = (lo, hi)`. There exists a fixed
  sparse witness `W` of size at most `g.numTypes + g.numTargets` (the positive optional bids of the
  full-market first-contact allocation) such that for every quote selection `Q`, either `x` admits
  an `η`-relaxed equilibrium (Lemma 4) or the blocker intervals `B` avoid all selected quotes in
  `Q` and capture at least one witness triple in `W` (Lemmas 5–6).
* `H4` (Quantile Multiplicative-Weight Search Engine — Section 3 of Kintali): For any target
  property `Good` and any polynomial-time LP solver, pattern-LP/decoder, and fixed-witness blocker
  oracle, iteratively querying `J - 1` quantiles (`J = 4(k + m + 1)`) per pair `(i, j)` and
  doubling blocker intervals on infeasible LP trials terminates within `O((k + m) log(G + 1))`
  rounds at a feasible LP, yielding a polynomial-time solver satisfying `Good`.
-/

namespace OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R3

open ComplexityTheory Arxiv.«2610.08796»

/-- Exact rational linear programming feasibility in polynomial time for well-formed systems
`(n, cons)` whose constraint rows have length `n` with `n = 0 ∨ cons ≠ []`. -/
def H1 : Prop :=
  ∃ lp : ℕ × List (List ℚ × ℚ) → List ℚ,
    IsPolyTime lp ∧
    ∀ (n : ℕ) (cons : List (List ℚ × ℚ)),
      (∀ r ∈ cons, r.1.length = n) → (n = 0 ∨ cons ≠ []) →
      (∃ y : List ℚ, y.length = n ∧
        ∀ r ∈ cons, (∑ j : Fin n, r.1[j.val]?.getD 0 * y[j.val]?.getD 0) ≤ r.2) →
      (lp (n, cons)).length = n ∧
      ∀ r ∈ cons, (∑ j : Fin n, r.1[j.val]?.getD 0 * (lp (n, cons))[j.val]?.getD 0) ≤ r.2

/-- Exact-recovery tolerance, pattern LP construction, and equilibrium decoding (Kintali,
Section 1 & Lemma 2): every feasible pattern LP solution decodes to an exact Bayes–Nash
equilibrium, and every `eta g`-relaxed equilibrium coverage yields a feasible pattern LP. -/
def H2 : Prop :=
  ∃ (eta : GameInput → ℚ)
    (patLP : GameInput × List ℚ → ℕ × List (List ℚ × ℚ))
    (decode : GameInput × List ℚ → EquilibriumOutput),
    IsPolyTime eta ∧ IsPolyTime patLP ∧ IsPolyTime decode ∧
    ∀ (g : GameInput), g.Valid →
      0 < eta g ∧
      ∀ (x : List ℚ),
        let L := patLP (g, x)
        (∀ r ∈ L.2, r.1.length = L.1) ∧ (L.1 = 0 ∨ L.2 ≠ []) ∧
        (∀ y : List ℚ, y.length = L.1 →
          (∀ r ∈ L.2, (∑ j : Fin L.1, r.1[j.val]?.getD 0 * y[j.val]?.getD 0) ≤ r.2) →
          g.IsBayesNash (decode (g, y))) ∧
        ((∃ (q : Fin g.numTypes → Fin g.numTargets → ℚ) (lam : ℚ),
            let c (t : Fin g.numTargets) := x[t.val]?.getD 0
            let u (θ : Fin g.numTypes) (t : Fin g.numTargets) :=
              (1 - c t) * (g.attackerPayoff θ t).1 + c t * (g.attackerPayoff θ t).2
            let p (t : Fin g.numTargets) :=
              (∑ θ : Fin g.numTypes, q θ t) * ((g.defenderPayoff t).2 - (g.defenderPayoff t).1)
            x.length = g.numTargets ∧ (∑ t, c t) = (g.1 : ℚ) ∧
            (∀ t, 0 ≤ c t ∧ c t ≤ 1) ∧ 0 ≤ lam ∧
            (∀ θ, (∑ t, q θ t) = g.prior θ ∧ ∀ t, 0 ≤ q θ t) ∧
            (∀ θ t s, 0 < q θ t → u θ s ≤ u θ t + eta g) ∧
            (∀ t, 0 < c t → lam ≤ p t + eta g) ∧ (∀ t, c t < 1 → p t ≤ lam + eta g)) →
          ∃ y : List ℚ, y.length = L.1 ∧
            ∀ r ∈ L.2, (∑ j : Fin L.1, r.1[j.val]?.getD 0 * y[j.val]?.getD 0) ≤ r.2)

/-- Grouped quota-sweep and fixed-witness blocker oracle (Kintali, Section 2 & Lemmas 3–6):
for any valid game `g` and `η > 0`, a fixed sparse witness `W` of size `≤ numTypes + numTargets`
certifies that every failed quote selection produces blocker intervals disjoint from `Q` that
capture some witness bid in `W`. -/
def H3 : Prop :=
  ∃ (grid : GameInput × ℚ → ℕ)
    (sweep : (GameInput × ℚ) × List (List (List ℕ)) → List ℚ × List (List (ℕ × ℕ))),
    IsPolyTime grid ∧ IsPolyTime sweep ∧
    ∀ (g : GameInput) (η : ℚ), g.Valid → 0 < η →
      let G := grid (g, η)
      1 ≤ G ∧
      ∃ W : List (ℕ × ℕ × ℕ),
        W.length ≤ g.numTypes + g.numTargets ∧
        (∀ w ∈ W, w.1 < g.numTypes ∧ w.2.1 < g.numTargets ∧ w.2.2 < G) ∧
        ∀ Q : List (List (List ℕ)),
          let (x, B) := sweep ((g, η), Q)
          (∃ (q : Fin g.numTypes → Fin g.numTargets → ℚ) (lam : ℚ),
            let c (t : Fin g.numTargets) := x[t.val]?.getD 0
            let u (θ : Fin g.numTypes) (t : Fin g.numTargets) :=
              (1 - c t) * (g.attackerPayoff θ t).1 + c t * (g.attackerPayoff θ t).2
            let p (t : Fin g.numTargets) :=
              (∑ θ : Fin g.numTypes, q θ t) * ((g.defenderPayoff t).2 - (g.defenderPayoff t).1)
            x.length = g.numTargets ∧ (∑ t, c t) = (g.1 : ℚ) ∧
            (∀ t, 0 ≤ c t ∧ c t ≤ 1) ∧ 0 ≤ lam ∧
            (∀ θ, (∑ t, q θ t) = g.prior θ ∧ ∀ t, 0 ≤ q θ t) ∧
            (∀ θ t s, 0 < q θ t → u θ s ≤ u θ t + η) ∧
            (∀ t, 0 < c t → lam ≤ p t + η) ∧ (∀ t, c t < 1 → p t ≤ lam + η)) ∨
          ((∀ i < g.numTypes, ∀ j < g.numTargets,
              let b := (B[i]?.getD [])[j]?.getD (0, 0)
              b.1 ≤ b.2 ∧ b.2 ≤ G ∧
              ∀ z ∈ (Q[i]?.getD [])[j]?.getD [], ¬(b.1 ≤ z ∧ z < b.2)) ∧
            ∃ w ∈ W,
              let b := (B[w.1]?.getD [])[w.2.1]?.getD (0, 0)
              b.1 ≤ w.2.2 ∧ w.2.2 < b.2)

/-- Quantile multiplicative-weight search engine (Kintali, Section 3): combining any poly-time
LP solver, sound well-formed pattern-LP/decoder, and fixed-witness blocker oracle yields a
poly-time solver for `Good` in `O((numTypes + numTargets) log(G + 1))` rounds. -/
def H4 : Prop :=
  ∀ (Good : GameInput → EquilibriumOutput → Prop)
    (lp : ℕ × List (List ℚ × ℚ) → List ℚ)
    (eta : GameInput → ℚ)
    (patLP : GameInput × List ℚ → ℕ × List (List ℚ × ℚ))
    (decode : GameInput × List ℚ → EquilibriumOutput)
    (grid : GameInput × ℚ → ℕ)
    (sweep : (GameInput × ℚ) × List (List (List ℕ)) → List ℚ × List (List (ℕ × ℕ))),
    IsPolyTime lp → IsPolyTime eta → IsPolyTime patLP → IsPolyTime decode →
    IsPolyTime grid → IsPolyTime sweep →
    (∀ n cons, (∀ r ∈ cons, r.1.length = n) → (n = 0 ∨ cons ≠ []) →
      (∃ y : List ℚ, y.length = n ∧
        ∀ r ∈ cons, (∑ j : Fin n, r.1[j.val]?.getD 0 * y[j.val]?.getD 0) ≤ r.2) →
      (lp (n, cons)).length = n ∧
      ∀ r ∈ cons, (∑ j : Fin n, r.1[j.val]?.getD 0 * (lp (n, cons))[j.val]?.getD 0) ≤ r.2) →
    (∀ g, g.Valid →
      let G := grid (g, eta g)
      1 ≤ G ∧
      (∀ x, let L := patLP (g, x)
        (∀ r ∈ L.2, r.1.length = L.1) ∧ (L.1 = 0 ∨ L.2 ≠ []) ∧
        ∀ y : List ℚ, y.length = L.1 →
          (∀ r ∈ L.2, (∑ j : Fin L.1, r.1[j.val]?.getD 0 * y[j.val]?.getD 0) ≤ r.2) →
          Good g (decode (g, y))) ∧
      ∃ W : List (ℕ × ℕ × ℕ), W.length ≤ g.numTypes + g.numTargets ∧
        (∀ w ∈ W, w.1 < g.numTypes ∧ w.2.1 < g.numTargets ∧ w.2.2 < G) ∧
        ∀ Q, let (x, B) := sweep ((g, eta g), Q); let L := patLP (g, x)
          (∃ y : List ℚ, y.length = L.1 ∧
            ∀ r ∈ L.2, (∑ j : Fin L.1, r.1[j.val]?.getD 0 * y[j.val]?.getD 0) ≤ r.2) ∨
          ((∀ i < g.numTypes, ∀ j < g.numTargets, let b := (B[i]?.getD [])[j]?.getD (0, 0)
              b.1 ≤ b.2 ∧ b.2 ≤ G ∧ ∀ z ∈ (Q[i]?.getD [])[j]?.getD [], ¬(b.1 ≤ z ∧ z < b.2)) ∧
            ∃ w ∈ W, let b := (B[w.1]?.getD [])[w.2.1]?.getD (0, 0); b.1 ≤ w.2.2 ∧ w.2.2 < b.2)) →
    ∃ solve : GameInput → EquilibriumOutput,
      IsPolyTime solve ∧ ∀ g, g.Valid → Good g (solve g)

theorem main : H1 → H2 → H3 → H4 → type_of% @Arxiv.«2610.08796».exists_isPolyTime_bayesNash := by
  intro h1 h2 h3 h4
  obtain ⟨lp, hlp_pt, hlp_spec⟩ := h1
  obtain ⟨eta, patLP, decode, heta_pt, hpat_pt, hdec_pt, h2_spec⟩ := h2
  obtain ⟨grid, sweep, hgrid_pt, hsweep_pt, h3_spec⟩ := h3
  apply h4 GameInput.IsBayesNash lp eta patLP decode grid sweep
    hlp_pt heta_pt hpat_pt hdec_pt hgrid_pt hsweep_pt hlp_spec
  intro g hg
  obtain ⟨heta_pos, hpat_spec⟩ := h2_spec g hg
  obtain ⟨hG_pos, W, hW_len, hW_bnd, hW_spec⟩ := h3_spec g (eta g) hg heta_pos
  refine ⟨hG_pos, ?_, W, hW_len, hW_bnd, ?_⟩
  · intro x
    obtain ⟨hlen, hne, hsound, _⟩ := hpat_spec x
    exact ⟨hlen, hne, hsound⟩
  · intro Q
    rcases hW_spec Q with hrel | hblk
    · left
      exact (hpat_spec (sweep ((g, eta g), Q)).1).2.2.2 hrel
    · right
      exact hblk

end OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R3
