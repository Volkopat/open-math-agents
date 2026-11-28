import OMAStatements.S_wp_falconer_s_conjecture

/- Adapted from OpenAI, openai/math@3344da59991ed94f9ba711217b29c1d760badfa6,
   OAI.MeasureTheory.Falconer.Estimates.SixInputsMain (strong dimension induction). -/
namespace OMA.R_wp_falconer_s_conjecture_R1
open MeasureTheory
open scoped ENNReal

def H1 : Prop :=
  ∀ E : Set (EuclideanSpace ℝ (Fin 2)), IsCompact E → 1 < dimH E →
    0 < volume {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}

def H2 : Prop :=
  ∀ d : ℕ, 3 ≤ d →
    (∀ k : ℕ, k < d → 2 ≤ k → ∀ E : Set (EuclideanSpace ℝ (Fin k)), IsCompact E →
      (k : ℝ≥0∞)/2 < dimH E → 0 < volume {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}) →
    ∀ E : Set (EuclideanSpace ℝ (Fin d)), IsCompact E → (d : ℝ≥0∞)/2 < dimH E →
      0 < volume {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}

theorem main : H1 → H2 → type_of% @OMA.S_wp_falconer_s_conjecture.main := by
  intro base step d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd E hE hdim
    by_cases h : d = 2
    · subst d
      have he : (2 : ℝ≥0∞)/2 = 1 := ENNReal.div_self (by norm_num) (by norm_num)
      exact (base E hE (by simpa only [Nat.cast_ofNat, he] using hdim)).ne'
    · exact (step d (by omega) (fun k hk hk2 K hK hdimK =>
        pos_iff_ne_zero.mpr (ih k hk hk2 K hK hdimK)) E hE hdim).ne'

end OMA.R_wp_falconer_s_conjecture_R1
