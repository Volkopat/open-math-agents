import FormalConjectures.ErdosProblems.«1132»
import Mathlib

open Filter

-- Reduction Erdos1132.erdos_1132.parts.i.R1 of Erdős Problem 1132 — i
-- Credit: @PetrouilFan
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Split of the difficulty:
--   H1 is the hard analytic input: in every tail of the node sequence there is a *dense* set of
--      points where the Lebesgue function beats (2/pi) log n up to one fixed additive loss.
--      This is a local Bernstein-type lower bound; it is much stronger than merely finding one
--      point, and it is where the real work on the interpolation polynomials lives.
--   H2 is a soft but genuine Baire-category lemma for an arbitrary sequence of continuous
--      functions: density of one such limsup set already forces a single point at which the
--      inequality holds frequently. It says nothing about Lebesgue functions.
--   main only converts H1's shape into H2's input and reads off the constant.

namespace OMA.R_Erdos1132_erdos_1132_parts_i_R1

def H1 : Prop :=
  ∀ x : ℕ → ℝ, (∀ k, x k ∈ Set.Icc (-1 : ℝ) 1) → Function.Injective x →
    ∃ k : ℕ, ∀ m : ℕ,
      Dense {t : {t : ℝ // t ∈ Set.Ioo (-1 : ℝ) 1} |
        ∃ n : ℕ, m ≤ n ∧ -(k : ℝ) <
          (Erdos1132.lebesgueFunction n x t.1 - 2 / Real.pi * Real.log n)}

def H2 : Prop :=
  ∀ f : ℕ → ℝ → ℝ, (∀ n : ℕ, Continuous (f n)) →
    (∃ k : ℕ, ∀ m : ℕ,
      Dense {t : {t : ℝ // t ∈ Set.Ioo (-1 : ℝ) 1} |
        ∃ n : ℕ, m ≤ n ∧ -(k : ℝ) < f n t.1}) →
    ∃ t ∈ Set.Ioo (-1 : ℝ) 1, ∃ C : ℝ,
      ∃ᶠ n : ℕ in atTop, C < f n t

lemma continuous_lagrangeBasis_of_injective {n : ℕ} {x : ℕ → ℝ}
    (hx : Function.Injective x) (k : ℕ) :
    Continuous (Erdos1132.lagrangeBasis n x k) := by
  unfold Erdos1132.lagrangeBasis
  apply Continuous.div
  · apply continuous_finset_prod
    intro i hi
    exact continuous_id.sub continuous_const
  · exact continuous_const
  · intro t
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    rw [Finset.mem_erase] at hi
    exact sub_ne_zero.mpr (fun h => hi.1 (hx h).symm)

lemma continuous_lebesgueFunction_of_injective {n : ℕ} {x : ℕ → ℝ}
    (hx : Function.Injective x) :
    Continuous (Erdos1132.lebesgueFunction n x) := by
  unfold Erdos1132.lebesgueFunction
  apply continuous_finset_sum
  intro k hk
  exact (continuous_lagrangeBasis_of_injective hx k).abs

lemma baire_extract (f : ℕ → ℝ → ℝ) (hfcont : ∀ n : ℕ, Continuous (f n))
    (hden : ∃ k : ℕ, ∀ m : ℕ,
      Dense {t : {t : ℝ // t ∈ Set.Ioo (-1 : ℝ) 1} |
        ∃ n : ℕ, m ≤ n ∧ -(k : ℝ) < f n t.1}) :
    ∃ t ∈ Set.Ioo (-1 : ℝ) 1, ∃ C : ℝ,
      ∃ᶠ n : ℕ in atTop, C < f n t := by
  rcases hden with ⟨k, hd⟩
  let U := {t : ℝ // t ∈ Set.Ioo (-1 : ℝ) 1}
  letI : BaireSpace U := (isOpen_Ioo : IsOpen (Set.Ioo (-1 : ℝ) 1)).baireSpace
  haveI : Nonempty U := ⟨⟨0, by norm_num⟩⟩
  let E : ℕ → Set U := fun m => {t | ∃ n : ℕ, m ≤ n ∧ -(k : ℝ) < f n t.1}
  have hEopen : ∀ m, IsOpen (E m) := by
    intro m
    have hEq : E m = ⋃ n : ℕ, ⋃ _ : m ≤ n, {t : U | -(k : ℝ) < f n t.1} := by
      ext t
      simp [E]
    rw [hEq]
    apply isOpen_iUnion
    intro n
    apply isOpen_iUnion
    intro hmn
    exact isOpen_lt continuous_const ((hfcont n).comp continuous_subtype_val)
  have hEdense : ∀ m, Dense (E m) := by
    intro m
    exact hd m
  have hInter : Dense (⋂ m : ℕ, E m) :=
    dense_iInter_of_Gδ (fun m => (hEopen m).isGδ) hEdense
  have hne : (⋂ m : ℕ, E m).Nonempty := hInter.nonempty
  rcases hne with ⟨t, ht⟩
  have ht' : ∀ m : ℕ, t ∈ E m := by simpa using ht
  refine ⟨t.1, t.2, -(k : ℝ), Filter.frequently_atTop.2 ?_⟩
  intro m
  exact ht' m

theorem main : H1 → H2 → type_of% @Erdos1132.erdos_1132.parts.i := by
  intro hH1 hH2 x hxrange hxinj
  let f : ℕ → ℝ → ℝ := fun n t =>
    Erdos1132.lebesgueFunction n x t - 2 / Real.pi * Real.log n
  have hfcont : ∀ n : ℕ, Continuous (f n) := by
    intro n
    dsimp [f]
    exact (continuous_lebesgueFunction_of_injective hxinj).sub continuous_const
  have hden : ∃ k : ℕ, ∀ m : ℕ,
      Dense {t : {t : ℝ // t ∈ Set.Ioo (-1 : ℝ) 1} |
        ∃ n : ℕ, m ≤ n ∧ -(k : ℝ) < f n t.1} := by
    simpa [f] using hH1 x hxrange hxinj
  rcases hH2 f hfcont hden with ⟨t, htmem, C, hfreq⟩
  have hfreq' : ∀ m : ℕ, ∃ n : ℕ, m ≤ n ∧ C < f n t :=
    Filter.frequently_atTop.1 hfreq
  refine ⟨t, htmem, -C, Filter.frequently_atTop.2 ?_⟩
  intro m
  rcases hfreq' m with ⟨n, hmn, hn⟩
  refine ⟨n, hmn, ?_⟩
  dsimp [f] at hn
  linarith

end OMA.R_Erdos1132_erdos_1132_parts_i_R1
