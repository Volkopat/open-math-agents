import FormalConjectures.ErdosProblems.«525»
import Mathlib

/- Split the uniform small-value estimate into its even and odd degree cases. -/
open Filter Real

namespace OMA.R_Erdos525_erdos_525_variants_konyagin_schlag_R1

def H1 : Prop := ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
  Erdos525.prob (2 * n) (fun f ↦ Erdos525.m f ≤ ε / √(2 * n : ℕ)) ≤ C * ε

def H2 : Prop := ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
  Erdos525.prob (2 * n + 1) (fun f ↦ Erdos525.m f ≤ ε / √(2 * n + 1 : ℕ)) ≤ C * ε

theorem main : H1 → H2 → type_of% @Erdos525.erdos_525.variants.konyagin_schlag := by
  rintro ⟨Ce, he⟩ ⟨Co, ho⟩
  refine ⟨max Ce Co, ?_⟩
  intro ε hε
  obtain ⟨Ne, hNe⟩ := eventually_atTop.1 (he ε hε)
  obtain ⟨No, hNo⟩ := eventually_atTop.1 (ho ε hε)
  have hbound : ∀ᶠ N : ℕ in atTop,
      Erdos525.prob N (fun f ↦ Erdos525.m f ≤ ε / √N) ≤ max Ce Co * ε := by
    refine eventually_atTop.2 ⟨2 * max Ne No + 1, ?_⟩
    intro N hN
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' N
    · exact (hNe k (by omega)).trans (mul_le_mul_of_nonneg_right (le_max_left Ce Co) hε.le)
    · exact (hNo k (by omega)).trans (mul_le_mul_of_nonneg_right (le_max_right Ce Co) hε.le)
  exact limsup_le_of_le (isCoboundedUnder_le_of_le atTop (x := (0 : ℝ))
    (fun n ↦ by unfold Erdos525.prob; positivity)) hbound

end OMA.R_Erdos525_erdos_525_variants_konyagin_schlag_R1
