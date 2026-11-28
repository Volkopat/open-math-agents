import OMAReductions.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2

-- Reduction Arxiv.2610.08796.exists_isPolyTime_bayesNash.R2.H3.R1 of step R2.H3
-- Credit: @paynebrowning
-- Each H becomes its own step once this file is accepted. Proving all of them closes R2.H3.

/-!
Binary-search reduction of `R2.H3` (computing an achievable rational equilibrium defender
threshold `Λ g : ℚ` in polynomial time) to the unconstrained fixed-threshold LTU decision oracle.

For a valid game `g` and rational threshold `lam ≥ 0`, let `HasEqGe g lam` assert the existence
of an unconstrained fixed-`lam` equilibrium `e` whose total coverage satisfies `g.1 ≤ ∑ t, cov t`.
- `H1` (Open decision core): `HasEqGe g lam` is decidable in `IsPolyTime` (a single `Bool`
  threshold query on the unconstrained fixed-`lam` LTU matching lattice).
- `H2` (Pure mathematical structure, no Turing machines): There is a polynomial bit-bound `p`
  such that every valid `g` admits an achievable rational equilibrium threshold `q ∈ [0, M]`
  with `q.den ≤ M` (`M = 2 ^ p.eval |g|`) that is the exact cutoff of `HasEqGe g` on `[0, M]`
  (`q = max Λ*(g)` when `0 < g.1`, and `q = M` when `g.1 = 0`).
- `H3` (Generic polytime binary search + continued-fraction rounding): For any `[BitstringEncoding α]`,
  any `IsPolyTime` oracle `dec : α × ℚ → Bool`, and any polynomial `p`, binary search on `[0, M]`
  for `3 * B + 2` iterations followed by continued-fraction convergent rounding recovers the unique
  rational cutoff `q ∈ [0, M]` with `q.den ≤ M` in `IsPolyTime`.
-/

namespace OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2_H3_R1

open ComplexityTheory Arxiv.«2610.08796»

/-- Fixed-threshold LTU matching decision oracle: given `(g, lam)`, decide in polynomial time
whether `g` admits an unconstrained fixed-`lam` equilibrium with total coverage at least `g.1`. -/
def H1 : Prop :=
  ∃ dec : GameInput × ℚ → Bool,
    IsPolyTime dec ∧
    ∀ (g : GameInput) (lam : ℚ), g.Valid →
      (dec (g, lam) = true ↔
        ∃ e : EquilibriumOutput,
          let cov (t : Fin g.numTargets) := e.1[t.val]?.getD 0
          let row (θ : Fin g.numTypes) := e.2[θ.val]?.getD []
          let atk (θ : Fin g.numTypes) (t : Fin g.numTargets) := (row θ)[t.val]?.getD 0
          let uA (θ : Fin g.numTypes) (t : Fin g.numTargets) :=
            (1 - cov t) * (g.attackerPayoff θ t).1 + cov t * (g.attackerPayoff θ t).2
          let gain (t : Fin g.numTargets) :=
            (∑ θ : Fin g.numTypes, g.prior θ * atk θ t) *
              ((g.defenderPayoff t).2 - (g.defenderPayoff t).1)
          e.1.length = g.numTargets ∧ e.2.length = g.numTypes ∧
          (g.1 : ℚ) ≤ (∑ t, cov t) ∧ (∀ t, 0 ≤ cov t ∧ cov t ≤ 1) ∧
          (∀ θ, (row θ).length = g.numTargets ∧ (∑ t, atk θ t) = 1 ∧ ∀ t, 0 ≤ atk θ t) ∧
          (∀ θ t s, 0 < atk θ t → uA θ s ≤ uA θ t) ∧
          (∀ t, 0 < cov t → lam ≤ gain t) ∧ (∀ t, cov t < 1 → gain t ≤ lam))

/-- Pure mathematical structure: every valid game admits an achievable rational equilibrium
threshold `q` of polynomial bit-length (`0 ≤ q ≤ M` and `q.den ≤ M` for `M = 2 ^ p.eval |g|`)
that serves as the exact monotone cutoff of unconstrained fixed-threshold coverage on `[0, M]`. -/
def H2 : Prop :=
  ∃ p : Polynomial ℕ,
    ∀ g : GameInput, g.Valid →
      let M : ℕ := 2 ^ p.eval (BitstringEncoding.bitEncode g).length
      let isEq (lam : ℚ) (e : EquilibriumOutput) : Prop :=
        let cov (t : Fin g.numTargets) := e.1[t.val]?.getD 0
        let row (θ : Fin g.numTypes) := e.2[θ.val]?.getD []
        let atk (θ : Fin g.numTypes) (t : Fin g.numTargets) := (row θ)[t.val]?.getD 0
        let uA (θ : Fin g.numTypes) (t : Fin g.numTargets) :=
          (1 - cov t) * (g.attackerPayoff θ t).1 + cov t * (g.attackerPayoff θ t).2
        let gain (t : Fin g.numTargets) :=
          (∑ θ : Fin g.numTypes, g.prior θ * atk θ t) *
            ((g.defenderPayoff t).2 - (g.defenderPayoff t).1)
        e.1.length = g.numTargets ∧ e.2.length = g.numTypes ∧
        (∀ t, 0 ≤ cov t ∧ cov t ≤ 1) ∧
        (∀ θ, (row θ).length = g.numTargets ∧ (∑ t, atk θ t) = 1 ∧ ∀ t, 0 ≤ atk θ t) ∧
        (∀ θ t s, 0 < atk θ t → uA θ s ≤ uA θ t) ∧
        (∀ t, 0 < cov t → lam ≤ gain t) ∧ (∀ t, cov t < 1 → gain t ≤ lam)
      ∃ q : ℚ,
        0 ≤ q ∧ q ≤ (M : ℚ) ∧ q.den ≤ M ∧
        (∃ e : EquilibriumOutput, isEq q e ∧
          (∑ t : Fin g.numTargets, e.1[t.val]?.getD 0) = (g.1 : ℚ)) ∧
        ∀ lam : ℚ, 0 ≤ lam → lam ≤ (M : ℚ) →
          ((∃ e : EquilibriumOutput, isEq lam e ∧
            (g.1 : ℚ) ≤ (∑ t : Fin g.numTargets, e.1[t.val]?.getD 0)) ↔ lam ≤ q)

/-- Generic polynomial-time binary search with continued-fraction exact rational recovery:
given any polynomial-time threshold oracle `dec : α × ℚ → Bool` and polynomial bit-bound `p`,
a polynomial-time procedure recovers every exact rational cutoff `q ∈ [0, M]` with `q.den ≤ M`
(`M = 2 ^ p.eval |x|`) characterized on `[0, M]` by `dec (x, lam) = true ↔ lam ≤ q`. -/
def H3 : Prop :=
  ∀ {α : Type} [BitstringEncoding α] (dec : α × ℚ → Bool) (p : Polynomial ℕ),
    IsPolyTime dec →
    ∃ search : α → ℚ, IsPolyTime search ∧
      ∀ (x : α) (q : ℚ),
        let M : ℕ := 2 ^ p.eval (BitstringEncoding.bitEncode x).length
        0 ≤ q → q ≤ (M : ℚ) → q.den ≤ M →
        (∀ lam : ℚ, 0 ≤ lam → lam ≤ (M : ℚ) → (dec (x, lam) = true ↔ lam ≤ q)) →
        search x = q

theorem main : H1 → H2 → H3 → OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2.H3 := by
  intro h1 h2 h3
  obtain ⟨dec, hdec_pt, hdec_spec⟩ := h1
  obtain ⟨p, hp⟩ := h2
  obtain ⟨search, hsearch_pt, hsearch_spec⟩ := h3 dec p hdec_pt
  refine ⟨search, hsearch_pt, fun g hg => ?_⟩
  obtain ⟨q, hq0, hqM, hqden, ⟨e, ⟨hl1, hl2, hcov, hatk, hbrA, hge, hle⟩, hsum⟩, hcut⟩ := hp g hg
  have hsearch_eq : search g = q := by
    refine hsearch_spec g q hq0 hqM hqden (fun lam hlam0 hlamM => ?_)
    rw [hdec_spec g lam hg, ← hcut lam hlam0 hlamM]
    constructor
    · rintro ⟨e', hl1', hl2', hsum', hcov', hatk', hbrA', hge', hle'⟩
      exact ⟨e', ⟨hl1', hl2', hcov', hatk', hbrA', hge', hle'⟩, hsum'⟩
    · rintro ⟨e', ⟨hl1', hl2', hcov', hatk', hbrA', hge', hle'⟩, hsum'⟩
      exact ⟨e', hl1', hl2', hsum', hcov', hatk', hbrA', hge', hle'⟩
  rw [hsearch_eq]
  exact ⟨e, hl1, hl2, hsum, hcov, hatk, hbrA, hge, hle⟩

end OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2_H3_R1
