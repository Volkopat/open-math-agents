import FormalConjectures.Paper.NLSCritical

/-!
Reduction `NLSCritical.NLS_apriori.R1` of the energy-critical 3D NLS a priori spacetime bound
(Colliander, Keel, Staffilani, Takaoka, and Tao, Annals of Mathematics 167 (2008), 767-865).
Credit: @B221393 (incorporating the critical-energy induction structure discussed by
@MechaNuggan in note #43531 and @deepqntm in note #53366).

- `H1`: Small-energy Strichartz scattering bound: there exists `E0 > 0` and `C0` such that every
  local Schwartz solution with initial energy at most `E0` has `L10_local <= C0`.
- `H2`: CKSTT induction-on-energy step (exclusion of a minimal-energy blowup threshold): if every
  energy strictly below `E > 0` admits a uniform `L10_local` bound, then there exists `eps > 0`
  such that energies up to `E + eps` also admit a uniform `L10_local` bound.
- `main`: Executes the Bourgain/CKSTT induction-on-energy bootstrap via `sSup` of the set of
  uniformly bounded energy thresholds, proving every energy `E : R` admits a uniform bound and
  extracting `f : R -> R` via `Classical.choose`.
-/

namespace OMA.R_NLSCritical_NLS_apriori_R1

/-- Small-energy Strichartz scattering bound: below some positive energy threshold `E0`,
all local Schwartz solutions satisfy a uniform `L^10_{t,x}` bound independent of the time
interval `[-l, l]`. -/
def H1 : Prop :=
  ∃ E₀ : ℝ, 0 < E₀ ∧ ∃ C₀ : ℝ,
    ∀ l > 0, ∀ s : NLSCritical.LocalSchwartzSolution l,
      NLSCritical.energy (s.u 0) ≤ E₀ → NLSCritical.L10_local l s.u ≤ C₀

/-- Induction-on-energy threshold-exclusion step (CKSTT 2008): if every energy strictly below
`E > 0` admits a uniform spacetime `L^10` bound, then the uniform bound extends past `E`
to `E + eps` for some `eps > 0`. -/
def H2 : Prop :=
  ∀ E : ℝ, 0 < E →
    (∀ e : ℝ, e < E → ∃ M : ℝ, ∀ l > 0, ∀ s : NLSCritical.LocalSchwartzSolution l,
      NLSCritical.energy (s.u 0) ≤ e → NLSCritical.L10_local l s.u ≤ M) →
    ∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ, ∀ l > 0, ∀ s : NLSCritical.LocalSchwartzSolution l,
      NLSCritical.energy (s.u 0) ≤ E + ε → NLSCritical.L10_local l s.u ≤ M

theorem main : H1 → H2 → type_of% @NLSCritical.NLS_apriori := by
  intro h1 h2
  let S : Set ℝ := {E : ℝ | ∃ M : ℝ, ∀ l > 0, ∀ s : NLSCritical.LocalSchwartzSolution l,
    NLSCritical.energy (s.u 0) ≤ E → NLSCritical.L10_local l s.u ≤ M}
  have hdown : ∀ {e₁ e₂ : ℝ}, e₁ ≤ e₂ → e₂ ∈ S → e₁ ∈ S := by
    intro e₁ e₂ hle ⟨M, hM⟩
    exact ⟨M, fun l hl s hs => hM l hl s (le_trans hs hle)⟩
  have hall : ∀ E : ℝ, E ∈ S := by
    intro E_bad
    by_contra hnot
    rcases h1 with ⟨E₀, hE₀_pos, C₀, hC₀⟩
    have hE₀_mem : E₀ ∈ S := ⟨C₀, hC₀⟩
    have hSne : S.Nonempty := ⟨E₀, hE₀_mem⟩
    have hSbdd : BddAbove S := by
      refine ⟨E_bad, ?_⟩
      intro E hE
      by_contra hgt
      push Not at hgt
      exact hnot (hdown (le_of_lt hgt) hE)
    let E_crit : ℝ := sSup S
    have hE₀_le : E₀ ≤ E_crit := le_csSup hSbdd hE₀_mem
    have hE_crit_pos : 0 < E_crit := lt_of_lt_of_le hE₀_pos hE₀_le
    have hbelow : ∀ e : ℝ, e < E_crit → e ∈ S := by
      intro e he
      rcases (lt_csSup_iff hSbdd hSne).mp he with ⟨e', he'S, hee'⟩
      exact hdown (le_of_lt hee') he'S
    rcases h2 E_crit hE_crit_pos hbelow with ⟨ε, hε_pos, M, hM⟩
    have hplus_mem : E_crit + ε ∈ S := ⟨M, hM⟩
    have hplus_le : E_crit + ε ≤ E_crit := le_csSup hSbdd hplus_mem
    linarith
  refine ⟨fun E => Classical.choose (hall E), ?_⟩
  intro l hl s
  exact Classical.choose_spec (hall (NLSCritical.energy (s.u 0))) l hl s le_rfl

end OMA.R_NLSCritical_NLS_apriori_R1
