import FormalConjectures.ErdosProblems.«692»

namespace OMA.R_Erdos692_erdos_692_variants_cambie_local_maxima_R1

open Filter Erdos692

-- Cambie's alternating intervals, with a rise at the left endpoint.
def H1 : Prop :=
  ∀ (k : ℕ) (δ : ℕ → ℕ → ℝ), (∀ a b, IsDelta₁ a b (δ a b)) →
    ∀ᶠ n : ℕ in atTop, ∃ p q : Fin (n ^ k) → ℕ,
      (∀ i, n + 1 ≤ p i ∧ n < q i ∧ (q i).Prime ∧ p i < 2 * q i ∧
        δ n (p i) < δ n (p i + 1)) ∧ (∀ i j, i < j → 2 * q i ≤ p j)

-- Adding twice an odd prime loses a positive-density residue class.
def H2 : Prop :=
  ∀ (δ : ℕ → ℕ → ℝ), (∀ a b, IsDelta₁ a b (δ a b)) →
    ∀ n q : ℕ, 2 ≤ n → n < q → q.Prime → δ n (2 * q + 1) < δ n (2 * q)

lemma plateau (f : ℕ → ℝ) (a l r m b : ℕ) (ha : a ≤ l)
    (hl : l < m) (hm : m ≤ b) (hb : b ≤ r) (hr : f (r + 1) < f r)
    (hu : f (m - 1) < f m) (he : ∀ j ∈ Set.Icc m b, f j = f m) :
    ∃ x, l < x ∧ x ≤ r ∧ x ∈ localMaxima f a := by
  have hval := he b ⟨hm, le_rfl⟩
  by_cases hd : f (b + 1) < f b
  · exact ⟨m, hl, le_trans hm hb, lt_of_le_of_lt ha hl, hu, b, hm, he, hd.trans_eq hval⟩
  have hbr : b < r := lt_of_le_of_ne hb (by rintro rfl; exact hd hr)
  by_cases hup : f b < f (b + 1)
  · apply plateau f a l r (b + 1) (b + 1) ha (by omega) le_rfl (by omega) hr
    · simpa using hup
    · intro j hj
      obtain ⟨h₁, h₂⟩ := hj
      rw [le_antisymm h₂ h₁]
  · apply plateau f a l r m (b + 1) ha hl (by omega) (by omega) hr hu
    intro j hj
    obtain ⟨h₁, h₂⟩ := hj
    by_cases hjb : j ≤ b
    · exact he j ⟨h₁, hjb⟩
    · have hj' : j = b + 1 := by omega
      exact hj' ▸ (le_antisymm (le_of_not_gt hup) (le_of_not_gt hd)).trans hval
termination_by r - b
decreasing_by all_goals omega

theorem main : H1 → H2 → type_of% @Erdos692.erdos_692.variants.cambie_local_maxima := by
  intro h₁ h₂ k δ hδ
  filter_upwards [h₁ k δ hδ, eventually_ge_atTop 2] with n hn htwo
  obtain ⟨p, q, h, hsep⟩ := hn
  have pick (i : Fin (n ^ k)) : ∃ x, p i < x ∧ x ≤ 2 * q i ∧ x ∈ localMaxima (δ n) (n + 1) := by
    obtain ⟨ha, hq, hprime, hpq, hup⟩ := h i
    apply plateau (δ n) (n + 1) (p i) (2 * q i) (p i + 1) (p i + 1) ha
      (by omega) le_rfl (by omega) (h₂ δ hδ n (q i) htwo hq hprime)
    · simpa using hup
    · intro j hj
      exact congrArg (δ n) (le_antisymm hj.2 hj.1)
  choose x hx using pick
  let g (i : Fin (n ^ k)) : localMaxima (δ n) (n + 1) := ⟨x i, (hx i).2.2⟩
  have hmono : StrictMono x := fun i j hij =>
    lt_of_le_of_lt ((hx i).2.1.trans (hsep i j hij)) (hx j).1
  have hg : Function.Injective g := fun _ _ e => hmono.injective (congrArg Subtype.val e)
  simpa [ENat.card_coe_set_eq] using ENat.card_le_card_of_injective hg

end OMA.R_Erdos692_erdos_692_variants_cambie_local_maxima_R1
