import OMAReductions.R_Erdos561_erdos_561_R1_H2_R2

-- Reduction Erdos561.erdos_561.R1.H2.R2.H2.R1 of step Erdos561.erdos_561.R1.H2.R2.H2
-- Credit: @ehsanmok
/-!
# Splitting off hosts without a large matching

The first hypothesis is a matching-number bound for the size Ramsey lower bound:
a host with fewer than the diagonal sum of edges and no matching of size t+1
avoids the pair of star forests whenever the first list has at least two stars,
one of which has at least two edges. For two stars it already covers the whole step,
since then s+t−1 = t+1. The second hypothesis is the remaining case: at least three
stars in the first list and a matching of size t+1 in the host.
The definitions of edges, matchings, the diagonal sum and avoiding colourings are
those of the parent reduction.
-/

open private edges Matching total avoiding enoughPairs from OMAReductions.R_Erdos561_erdos_561_R1_H2_R2

namespace OMA.R_Erdos561_erdos_561_R1_H2_R2_H2_R1

/-- Hosts below the diagonal sum without a matching of size t+1 are avoiding. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] {s t : ℕ}, 2 ≤ s → 1 ≤ t →
    ∀ (n : Fin s → ℕ) (m : Fin t → ℕ), Antitone n → Antitone m →
      (∀ i, 1 ≤ n i) → (∃ i, 2 ≤ n i) → (∀ j, 1 ≤ m j) →
      ∀ G : SimpleGraph V, edges G < total n m →
        (¬ ∃ M ≤ G, Matching M ∧ t + 1 ≤ edges M) → avoiding G n m

/-- The parent step with at least three stars in the first list and a matching of size t+1. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] {s t : ℕ}, 3 ≤ s → 1 ≤ t →
    ∀ (n : Fin s → ℕ) (m : Fin t → ℕ), Antitone n → Antitone m →
      (∀ i, 2 ≤ n i) → (∀ j, 1 ≤ m j) → (∃ j, m j = 1) → (∃ j, 2 ≤ m j) →
      (∀ a, 2 ≤ a → (∀ i, a ≤ n i) → (a - 1) * s + 1 < t) →
      ¬ enoughPairs n m →
      ∀ G : SimpleGraph V, edges G < total n m →
        (¬ ∃ M ≤ G, Matching M ∧ s + t - 1 ≤ edges M) →
        (∃ M ≤ G, Matching M ∧ t + 1 ≤ edges M) → avoiding G n m

theorem main : H1 → H2 → OMA.R_Erdos561_erdos_561_R1_H2_R2.H2 := by
  intro ha hb V _ s t hs ht n m hna hma hn2 hm hm1 hmBig hf hp G hG hno
  by_cases hex : ∃ M ≤ G, Matching M ∧ t + 1 ≤ edges M
  · by_cases h3 : 3 ≤ s
    · exact hb h3 ht n m hna hma hn2 hm hm1 hmBig hf hp G hG hno hex
    · exfalso
      obtain ⟨M, hM, hmatch, hsize⟩ := hex
      exact hno ⟨M, hM, hmatch, by omega⟩
  · exact ha hs ht n m hna hma (fun i => by have := hn2 i; omega)
      ⟨⟨0, by omega⟩, hn2 _⟩ hm G hG hex

end OMA.R_Erdos561_erdos_561_R1_H2_R2_H2_R1
