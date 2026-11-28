import OMAReductions.R_oeis_a236102_R1
import Mathlib

-- Step oeis-a236102.R1.H3: hypothesis H3 of reduction oeis-a236102.R1
-- Credit: @Raimo33

namespace RaimoPart

def gen : ℕ → ℕ → ℕ → List (Multiset ℕ)
  | 0, _, n => if n = 0 then [0] else []
  | f+1, b, n => if n = 0 then [0] else
      (List.range' 1 (min b n)).flatMap (fun k => (gen f k (n-k)).map (fun t => k ::ₘ t))

lemma zero_iff (s : Multiset ℕ) (b : ℕ) :
    ((∀ i ∈ s, 0 < i ∧ i ≤ b) ∧ s.sum = 0) ↔ s = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [Multiset.sum_eq_zero_iff] at h2
    apply Multiset.eq_zero_of_forall_notMem
    intro x hx
    have := h1 x hx; have := h2 x hx; omega
  · rintro rfl; simp

lemma mem_gen : ∀ f b n s, n ≤ f →
    (s ∈ gen f b n ↔ (∀ i ∈ s, 0 < i ∧ i ≤ b) ∧ s.sum = n) := by
  intro f
  induction f with
  | zero =>
    intro b n s hn
    have : n = 0 := by omega
    subst this
    simp [gen, zero_iff]
  | succ f ih =>
    intro b n s hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [gen, zero_iff]
    have hn0 : n ≠ 0 := by omega
    simp only [gen, hn0, if_false, List.mem_flatMap, List.mem_map, List.mem_range'_1]
    constructor
    · rintro ⟨k, ⟨hk1, hk2⟩, t, ht, rfl⟩
      rw [ih k (n-k) t (by omega)] at ht
      obtain ⟨ht1, ht2⟩ := ht
      refine ⟨?_, ?_⟩
      · intro i hi
        rw [Multiset.mem_cons] at hi
        rcases hi with rfl | hi
        · constructor <;> omega
        · have := ht1 i hi
          constructor <;> omega
      · rw [Multiset.sum_cons, ht2]; omega
    · rintro ⟨h1, h2⟩
      have hne : s ≠ 0 := by
        rintro rfl; simp at h2; omega
      obtain ⟨k, hk, hmax⟩ := Multiset.exists_max_image id hne
      have hkn : k ≤ n := h2 ▸ Multiset.le_sum_of_mem hk
      have hkb := h1 k hk
      refine ⟨k, ⟨by omega, by omega⟩, s.erase k, ?_, Multiset.cons_erase hk⟩
      rw [ih k (n-k) _ (by omega)]
      refine ⟨?_, ?_⟩
      · intro i hi
        have hi' := Multiset.mem_of_mem_erase hi
        exact ⟨(h1 i hi').1, hmax i hi'⟩
      · have := Multiset.sum_cons k (s.erase k)
        rw [Multiset.cons_erase hk] at this
        omega

lemma card_eq (n : ℕ) : Fintype.card (Nat.Partition n) = (gen n n n).toFinset.card := by
  classical
  rw [← Finset.card_univ, ← Finset.card_image_of_injective _ (fun p q h => Nat.Partition.ext h)]
  congr 1
  ext s
  simp only [Finset.mem_image, Finset.mem_univ, true_and, List.mem_toFinset]
  rw [mem_gen n n n s le_rfl]
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨fun i hi => ⟨p.parts_pos hi, ?_⟩, p.parts_sum⟩
    rw [← p.parts_sum]; exact Multiset.le_sum_of_mem hi
  · rintro ⟨h1, h2⟩
    exact ⟨⟨s, fun hi => (h1 _ hi).1, h2⟩, rfl⟩

end RaimoPart

theorem OMA.solution : OMA.R_oeis_a236102_R1.H3 := by
  unfold OMA.R_oeis_a236102_R1.H3
  simp only [RaimoPart.card_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
