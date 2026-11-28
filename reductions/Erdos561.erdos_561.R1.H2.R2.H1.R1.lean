import OMAReductions.R_Erdos561_erdos_561_R1_H2_R2

-- Reduction Erdos561.erdos_561.R1.H2.R2.H1.R1 of step Erdos561.erdos_561.R1.H2.R2.H1
-- Credit: @ehsanmok
/-!
# Splitting off hosts without a large matching

The first hypothesis is a matching-number bound for the size Ramsey lower bound:
a host with fewer than the diagonal sum of edges and no matching of size t+1
avoids the pair of star forests whenever the first list has at least two stars,
one of which has at least two edges. Both lists of the step contain a one-edge star
and a star with at least two edges, so both have length at least two, and applying
the bound to the list pair in either order handles hosts without a matching of
size max(s,t)+1. The second hypothesis is the remaining case: the step together with
a matching of size max(s,t)+1 in the host.
The definitions of edges, matchings, the diagonal sum, trimming and avoiding
colourings are those of the parent reduction.
-/

open private edges Matching total avoiding enoughPairs canTrim affordableTrim total_swap
  avoiding_swap from OMAReductions.R_Erdos561_erdos_561_R1_H2_R2

namespace OMA.R_Erdos561_erdos_561_R1_H2_R2_H1_R1

private theorem two_le_length {s : ℕ} {n : Fin s → ℕ} (h1 : ∃ i, n i = 1)
    (h2 : ∃ i, 2 ≤ n i) : 2 ≤ s := by
  obtain ⟨i, hi⟩ := h1
  obtain ⟨i', hi'⟩ := h2
  have hne : i ≠ i' := by
    rintro rfl
    omega
  have hv : i.val ≠ i'.val := Fin.val_ne_of_ne hne
  have := i.isLt
  have := i'.isLt
  omega

/-- Hosts below the diagonal sum without a matching of size t+1 are avoiding. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] {s t : ℕ}, 2 ≤ s → 1 ≤ t →
    ∀ (n : Fin s → ℕ) (m : Fin t → ℕ), Antitone n → Antitone m →
      (∀ i, 1 ≤ n i) → (∃ i, 2 ≤ n i) → (∀ j, 1 ≤ m j) →
      ∀ G : SimpleGraph V, edges G < total n m →
        (¬ ∃ M ≤ G, Matching M ∧ t + 1 ≤ edges M) → avoiding G n m

/-- The parent step for hosts with a matching of size max(s,t)+1. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] {s t : ℕ}, 1 ≤ s → 1 ≤ t →
    ∀ (n : Fin s → ℕ) (m : Fin t → ℕ), Antitone n → Antitone m →
      (∀ i, 1 ≤ n i) → (∀ j, 1 ≤ m j) →
      (∃ i, n i = 1) → (∃ j, m j = 1) →
      (∃ i, 2 ≤ n i) → (∃ j, 2 ≤ m j) →
      ¬ (enoughPairs n m ∧ (canTrim n m (s + t - 1) ∨ canTrim m n (s + t - 1))) →
      ∀ G : SimpleGraph V, edges G < total n m →
        ¬ affordableTrim G n m → ¬ affordableTrim G m n →
        (∃ M ≤ G, Matching M ∧ max s t + 1 ≤ edges M) → avoiding G n m

theorem main : H1 → H2 → OMA.R_Erdos561_erdos_561_R1_H2_R2.H1 := by
  intro ha hb V _ s t hs ht n m hna hma hn hm hn1 hm1 hn2 hm2 hp G hG hnt hmt
  have hs2 : 2 ≤ s := two_le_length hn1 hn2
  have ht2 : 2 ≤ t := two_le_length hm1 hm2
  by_cases hex : ∃ M ≤ G, Matching M ∧ max s t + 1 ≤ edges M
  · exact hb hs ht n m hna hma hn hm hn1 hm1 hn2 hm2 hp G hG hnt hmt hex
  · by_cases hst : s ≤ t
    · refine ha hs2 ht n m hna hma hn hn2 hm G hG ?_
      rintro ⟨M, hM, hmatch, hsize⟩
      exact hex ⟨M, hM, hmatch, by rw [max_eq_right hst]; exact hsize⟩
    · have hts : t ≤ s := by omega
      refine avoiding_swap (ha ht2 hs m n hma hna hm hm2 hn G
        (by rw [total_swap m n]; exact hG) ?_)
      rintro ⟨M, hM, hmatch, hsize⟩
      exact hex ⟨M, hM, hmatch, by rw [max_eq_left hts]; exact hsize⟩

end OMA.R_Erdos561_erdos_561_R1_H2_R2_H1_R1
