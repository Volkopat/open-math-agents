import OMAReductions.R_Erdos1057_erdos_1057_variants_agp_infinite_R2
import Mathlib

-- Step Erdos1057.erdos_1057.variants.agp_infinite.R2.H2: hypothesis H2 of reduction Erdos1057.erdos_1057.variants.agp_infinite.R2
-- Credit: @ivillar. Repeatedly extracting product-one subsets maps each t-subset S to a product-one I ⊆ S with |S| <= |I| + n; the fibre over I injects (S -> S \ I) into the (t - |I|)-subsets of P \ I, and C(N - |I|, t - |I|) <= C(N - t + n, n) <= C(N, n).

/-! Step Erdos1057.erdos_1057.variants.agp_infinite.R2.H2. -/

open Finset

namespace P8E1057

/-- Repeatedly extract product-one subsets until at most `n` elements remain. -/
lemma extract (P : Finset ℕ) (M n : ℕ)
    (hext : ∀ S ⊆ P, n < S.card → ∃ I ⊆ S, I.Nonempty ∧ (∏ p ∈ I, p) ≡ 1 [MOD M]) :
    ∀ S ⊆ P, ∃ I ⊆ S, (∏ p ∈ I, p) ≡ 1 [MOD M] ∧ S.card ≤ I.card + n := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hSP
    by_cases hS : S.card ≤ n
    · exact ⟨∅, Finset.empty_subset _, by simp [Nat.ModEq.refl], by simpa using hS⟩
    · obtain ⟨J, hJS, hJne, hJ⟩ := hext S hSP (by omega)
      have hlt : S \ J ⊂ S := Finset.sdiff_ssubset hJS hJne
      obtain ⟨I', hI'S, hI', hcard⟩ := ih (S \ J) hlt ((Finset.sdiff_subset).trans hSP)
      have hdisj : Disjoint J I' := by
        rw [Finset.disjoint_left]
        intro a haJ haI
        exact (Finset.mem_sdiff.mp (hI'S haI)).2 haJ
      refine ⟨J ∪ I', Finset.union_subset hJS (hI'S.trans Finset.sdiff_subset), ?_, ?_⟩
      · rw [Finset.prod_union hdisj]
        simpa using Nat.ModEq.mul hJ hI'
      · rw [Finset.card_union_of_disjoint hdisj]
        have := Finset.card_sdiff_add_card_eq_card hJS
        omega

theorem h2 : OMA.R_Erdos1057_erdos_1057_variants_agp_infinite_R2.H2 := by
  intro P M n t hnt htP hext
  classical
  suffices key : ∀ F : Finset (Finset ℕ), (∀ I, I ∈ F ↔ I ∈ P.powerset ∧ t - n ≤ I.card ∧
      I.card ≤ t ∧ (∏ p ∈ I, p) ≡ 1 [MOD M]) → P.card.choose t ≤ F.card * P.card.choose n by
    apply key
    intro I
    simp only [Finset.mem_filter]
  intro F hF
  have hchoice : ∀ S : Finset ℕ, ∃ I : Finset ℕ, S ⊆ P → (I ⊆ S ∧ (∏ p ∈ I, p) ≡ 1 [MOD M] ∧
      S.card ≤ I.card + n) := by
    intro S
    by_cases hS : S ⊆ P
    · obtain ⟨I, h1, h2, h3⟩ := extract P M n hext S hS
      exact ⟨I, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨∅, fun h => absurd h hS⟩
  choose φ hφ using hchoice
  let T := P.powersetCard t
  have hT : T.card = P.card.choose t := Finset.card_powersetCard t P
  have hmaps : ∀ S ∈ T, φ S ∈ F := by
    intro S hS
    obtain ⟨hSP, hSc⟩ := Finset.mem_powersetCard.mp hS
    obtain ⟨h1, h2, h3⟩ := hφ S hSP
    rw [hF]
    refine ⟨Finset.mem_powerset.mpr (h1.trans hSP), by omega, ?_, h2⟩
    have := Finset.card_le_card h1
    omega
  have hfib : ∀ I ∈ F, (T.filter (fun S => φ S = I)).card ≤ P.card.choose n := by
    intro I hI
    obtain ⟨hIP, hlo, hhi, -⟩ := (hF I).mp hI
    rw [Finset.mem_powerset] at hIP
    -- fibre ⊆ supersets of I, injected into (t - |I|)-subsets of P \ I
    have h1 : (T.filter (fun S => φ S = I)).card ≤ ((P \ I).powersetCard (t - I.card)).card := by
      apply Finset.card_le_card_of_injOn (fun S => S \ I)
      · intro S hS
        simp only [Finset.mem_coe, Finset.mem_filter, T, Finset.mem_powersetCard] at hS ⊢
        obtain ⟨⟨hSP, hSc⟩, hφS⟩ := hS
        have hIS : I ⊆ S := hφS ▸ (hφ S hSP).1
        refine ⟨Finset.sdiff_subset_sdiff hSP le_rfl, ?_⟩
        have := Finset.card_sdiff_add_card_eq_card hIS
        omega
      · intro S hS S' hS' heq
        simp only [Finset.mem_coe, Finset.mem_filter, T, Finset.mem_powersetCard] at hS hS'
        have hIS : I ⊆ S := hS.2 ▸ (hφ S hS.1.1).1
        have hIS' : I ⊆ S' := hS'.2 ▸ (hφ S' hS'.1.1).1
        have e1 : S = (S \ I) ∪ I := (Finset.sdiff_union_of_subset hIS).symm
        have e2 : S' = (S' \ I) ∪ I := (Finset.sdiff_union_of_subset hIS').symm
        simp only at heq
        rw [e1, e2, heq]
    have hsd := Finset.card_sdiff_add_card_eq_card hIP
    rw [Finset.card_powersetCard, show (P \ I).card = P.card - I.card by omega] at h1
    have hi : I.card ≤ t := hhi
    have hN : t ≤ P.card := htP
    -- C(N - i, t - i) ≤ C(N, n)
    have h2 : (P.card - I.card).choose (t - I.card) ≤ P.card.choose n := by
      have e : (P.card - I.card).choose (t - I.card) =
          (P.card - I.card).choose (P.card - t) := by
        rw [← Nat.choose_symm (by omega)]
        congr 1
        omega
      rw [e]
      calc (P.card - I.card).choose (P.card - t)
          ≤ (P.card - t + n).choose (P.card - t) := Nat.choose_le_choose _ (by omega)
        _ = (P.card - t + n).choose n := by
            rw [← Nat.choose_symm (by omega)]
            congr 1
            omega
        _ ≤ P.card.choose n := Nat.choose_le_choose _ (by omega)
    exact h1.trans h2
  have := Finset.card_le_mul_card_image_of_maps_to hmaps _ hfib
  rw [hT] at this
  linarith

end P8E1057

theorem OMA.solution : OMA.R_Erdos1057_erdos_1057_variants_agp_infinite_R2.H2 :=
  P8E1057.h2
