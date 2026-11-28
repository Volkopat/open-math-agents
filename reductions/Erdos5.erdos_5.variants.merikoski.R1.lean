import FormalConjectures.ErdosProblems.«5»

-- Reduction Erdos5.erdos_5.variants.merikoski.R1 of Erdős Problem 5 — merikoski
-- Credit: @B221393
-- Separates the degenerate equal-entry case (Goldston-Pintz-Yildirim: 0 in limitPointSet)
-- from the translation-normalized strictly increasing positive quadruple core of Merikoski [Me20].

namespace OMA.R_Erdos5_erdos_5_variants_merikoski_R1

/-- Goldston-Pintz-Yildirim: zero is a limit point of normalized prime gaps. -/
def H1 : Prop :=
  (0 : ℝ) ∈ Erdos5.limitPointSet

/-- Normalized Merikoski core: for any strictly increasing quadruple starting at 0,
some pairwise difference lies in `limitPointSet`. -/
def H2 : Prop :=
  ∀ γ : Fin 4 → ℝ, StrictMono γ → γ 0 = 0 →
    ∃ i j : Fin 4, i < j ∧ γ j - γ i ∈ Erdos5.limitPointSet

theorem main : H1 → H2 → type_of% @Erdos5.erdos_5.variants.merikoski := by
  intro h1 h2 β hβmono
  by_cases hstrict : StrictMono β
  · let γ : Fin 4 → ℝ := fun k => β k - β 0
    have hγstrict : StrictMono γ := fun i j hij => sub_lt_sub_right (hstrict hij) (β 0)
    have hγ0 : γ 0 = 0 := sub_self (β 0)
    obtain ⟨i, j, hij, hmem⟩ := h2 γ hγstrict hγ0
    refine ⟨i, j, hij, ?_⟩
    simpa [γ] using hmem
  · unfold StrictMono at hstrict
    push_neg at hstrict
    obtain ⟨i, j, hij, hle⟩ := hstrict
    have heq : β j = β i := le_antisymm hle (hβmono hij.le)
    refine ⟨i, j, hij, ?_⟩
    rw [heq, sub_self]
    exact h1

end OMA.R_Erdos5_erdos_5_variants_merikoski_R1
