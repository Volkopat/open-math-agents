import FormalConjectures.Books.BugeaudDistributionModuloOne.Problem10_8
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
Reduction `Bugeaud08.problem_10_8.variants.exceptional_set_dimH_zero.R1` of the claim that the
exceptional set of the p-adic Littlewood conjecture has Hausdorff dimension zero, due to
Einsiedler and Kleinbock [EK07, Compositio Math. 143 (2007), 689--702].

- `H1`: the Einsiedler-Kleinbock fixed-threshold dimension bound. For every prime p and every k,
  the set of xi such that q * |q|_p * ||q xi|| stays at least 1/(k+1) for all sufficiently large
  q has Hausdorff dimension zero. This is the deep measure-rigidity input of [EK07] (entropy for
  higher-rank diagonal actions on quotients of SL(2,R) x SL(2,Q_p)), which Mathlib does not have.
- `H2`: countable threshold covering of the exceptional set. Since every term
  q * |q|_p * ||q xi|| is nonnegative, a liminf different from zero is positive, hence exceeds
  some 1/(k+1) by the Archimedean property, hence the fixed-threshold inequality holds
  eventually. So the exceptional set is covered by the countably many sets of `H1`.
- `main`: `H1` and `H2` turn the exceptional set into a countable union of dimension-zero sets;
  `dimH_mono` with the countable stability lemma `dimH_iUnion` gives dimension zero.
-/

namespace OMA.R_Bugeaud08_problem_10_8_variants_exceptional_set_dimH_zero_R1

/-- Einsiedler-Kleinbock [EK07]: for each fixed threshold, the uniformly badly approximable set
of the p-adic Littlewood problem has Hausdorff dimension zero. -/
def H1 : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ k : ℕ,
    dimH {ξ : ℝ | ∃ N : ℕ, ∀ q ≥ N,
      (1 : ℝ) / (k + 1) ≤ q * padicNorm p q * distToNearestInt (q * ξ)} = 0

/-- The exceptional set of the liminf is covered by the countably many fixed-threshold sets:
a nonzero liminf of nonnegative terms is positive, so it clears some threshold 1/(k+1)
eventually. -/
def H2 : Prop :=
  ∀ (p : ℕ), p.Prime →
    {ξ : ℝ | Filter.atTop.liminf
      (fun q : ℕ ↦ q * padicNorm p q * distToNearestInt (q * ξ)) ≠ 0} ⊆
    ⋃ k : ℕ, {ξ : ℝ | ∃ N : ℕ, ∀ q ≥ N,
      (1 : ℝ) / (k + 1) ≤ q * padicNorm p q * distToNearestInt (q * ξ)}

theorem main : H1 → H2 → type_of% @Bugeaud08.problem_10_8.variants.exceptional_set_dimH_zero := by
  intro h1 h2 p hp
  have hzero : ∀ k : ℕ,
      dimH {ξ : ℝ | ∃ N : ℕ, ∀ q ≥ N,
        (1 : ℝ) / (k + 1) ≤ q * padicNorm p q * distToNearestInt (q * ξ)} = 0 := h1 p hp
  have hle : dimH {ξ : ℝ | Filter.atTop.liminf
      (fun q : ℕ ↦ q * padicNorm p q * distToNearestInt (q * ξ)) ≠ 0} ≤ 0 := by
    calc dimH {ξ : ℝ | Filter.atTop.liminf
          (fun q : ℕ ↦ q * padicNorm p q * distToNearestInt (q * ξ)) ≠ 0}
        ≤ dimH (⋃ k : ℕ, {ξ : ℝ | ∃ N : ℕ, ∀ q ≥ N,
            (1 : ℝ) / (k + 1) ≤ q * padicNorm p q * distToNearestInt (q * ξ)}) :=
          dimH_mono (h2 p hp)
      _ = ⨆ k : ℕ, dimH {ξ : ℝ | ∃ N : ℕ, ∀ q ≥ N,
            (1 : ℝ) / (k + 1) ≤ q * padicNorm p q * distToNearestInt (q * ξ)} := by
          rw [dimH_iUnion]
      _ = 0 := by simp only [hzero, iSup_const]
  exact le_antisymm hle zero_le

end OMA.R_Bugeaud08_problem_10_8_variants_exceptional_set_dimH_zero_R1
