import FormalConjectures.ErdosProblems.«186»
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Reduction of the Pham--Zakharov bound

Pham and Zakharov [PhZa24, Theorem 1] prove that every non-averaging subset of
`{1, ..., N}` has at most `N^(1/4 + o(1))` elements. The reduction below splits
that theorem into its extremal and analytic halves.

* `H1` is the theorem in exponent form: a single error function `f` with
  `f N -> 0` such that every non-averaging `A` inside `{1, ..., N}` satisfies
  `|A| <= N^(1/4 + f N)`. This is the surviving additive-combinatorial
  content (the inverse-sumset and zero-sum-in-subset-sums machinery of
  [PhZa24]) and does not by itself give the uniform epsilon statement.
* `H2` records that the maximum defining `F` is attained by an actual finite
  set, so the pointwise bound on sets can be read back on `F N`.

`main` performs only the uniformisation: the error function falls below any
positive `ε` eventually, and `x ^ (1/4 + f N) <= x ^ (1/4 + ε)` because the
base `N` is at least two.
-/

open Filter

namespace OMA.R_Erdos186_erdos_186_variants_pham_zakharov_R1

/-- Exponent form of [PhZa24, Theorem 1]: one error function tending to zero
controls every non-averaging set in every initial interval. -/
def H1 : Prop :=
  ∃ f : ℕ → ℝ, Tendsto f atTop (nhds (0 : ℝ)) ∧
    ∀ (N : ℕ), 1 ≤ N → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
      Erdos186.NonAveraging A → (A.card : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4 + f N)

/-- The extremal cardinality `F N` is attained inside the initial interval. -/
def H2 : Prop :=
  ∀ N : ℕ, ∃ A : Finset ℕ,
    A ⊆ Finset.Icc 1 N ∧ Erdos186.NonAveraging A ∧ A.card = Erdos186.F N

theorem main : H1 → H2 → type_of% @Erdos186.erdos_186.variants.pham_zakharov := by
  intro h1 h2 ε hε
  obtain ⟨f, hf, hfbound⟩ := h1
  have hsmall : ∀ᶠ N : ℕ in atTop, f N < ε := by
    have hmem : Set.Iio ε ∈ nhds (0 : ℝ) := isOpen_Iio.mem_nhds hε
    have h := hf.eventually hmem
    simpa only [Set.mem_Iio] using h
  filter_upwards [hsmall, eventually_ge_atTop 2] with N hN hN2
  obtain ⟨A, hA, hna, hcard⟩ := h2 N
  have hN1 : 1 ≤ N := by omega
  have hbase : (1 : ℝ) ≤ (N : ℝ) := by
    have : (1 : ℕ) ≤ N := by omega
    exact_mod_cast this
  have hexp : (1 : ℝ) / 4 + f N ≤ (1 : ℝ) / 4 + ε := by linarith
  calc (Erdos186.F N : ℝ) = (A.card : ℝ) := by exact_mod_cast hcard.symm
    _ ≤ (N : ℝ) ^ ((1 : ℝ) / 4 + f N) := hfbound N hN1 A hA hna
    _ ≤ (N : ℝ) ^ ((1 : ℝ) / 4 + ε) :=
        Real.rpow_le_rpow_of_exponent_le hbase hexp

end OMA.R_Erdos186_erdos_186_variants_pham_zakharov_R1
