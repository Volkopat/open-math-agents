import OMAStatements.S_mo_366028
import Mathlib

namespace OMA.P_mo_366028

/-- For every `n` there are `n` positive integers such that the difference of
any two of them divides the smaller one. -/
lemma exists_set (n : ℕ) : ∃ S : Finset ℕ, S.card = n ∧ (∀ a ∈ S, 0 < a) ∧
    ∀ a ∈ S, ∀ b ∈ S, a < b → (b - a) ∣ a := by
  induction n with
  | zero => exact ⟨∅, by simp, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨S, hc, hpos, hdiv⟩ := ih
    set L := ∏ s ∈ S, s with hL
    have hLpos : 0 < L := Finset.prod_pos hpos
    have hdvdL : ∀ s ∈ S, s ∣ L := fun s hs => Finset.dvd_prod_of_mem _ hs
    have hnot : L ∉ S.map (addLeftEmbedding L) := by
      intro h
      rw [Finset.mem_map] at h
      obtain ⟨s, hs, hs'⟩ := h
      have := hpos s hs
      simp at hs'
      omega
    refine ⟨insert L (S.map (addLeftEmbedding L)), ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hnot, Finset.card_map, hc]
    · intro a ha
      rw [Finset.mem_insert, Finset.mem_map] at ha
      rcases ha with rfl | ⟨s, hs, rfl⟩
      · exact hLpos
      · simp only [addLeftEmbedding_apply]; omega
    · intro a ha b hb hab
      rw [Finset.mem_insert, Finset.mem_map] at ha hb
      rcases ha with rfl | ⟨s, hs, rfl⟩ <;> rcases hb with rfl | ⟨t, ht, rfl⟩
      · omega
      · simp only [addLeftEmbedding_apply] at hab ⊢
        rw [show L + t - L = t by omega]
        exact hdvdL t ht
      · simp only [addLeftEmbedding_apply] at hab
        omega
      · simp only [addLeftEmbedding_apply] at hab ⊢
        have hst : s < t := by omega
        rw [show L + t - (L + s) = t - s by omega]
        have h1 := hdiv s hs t ht hst
        exact Nat.dvd_add (h1.trans (hdvdL s hs)) h1

end OMA.P_mo_366028

theorem OMA.solution : type_of% @OMA.S_mo_366028.main := by
  obtain ⟨S, hc, hpos, hdiv⟩ := OMA.P_mo_366028.exists_set 9
  let f := S.orderEmbOfFin hc
  have hf : ∀ i, f i ∈ S := fun i => S.orderEmbOfFin_mem hc i
  refine ⟨fun i => ((f i : ℕ) : ℝ), ?_, ?_, ?_⟩
  · intro i j h
    exact f.injective (Nat.cast_injective h)
  · intro i
    have := hpos _ (hf i)
    simp only [Nat.cast_pos]
    exact this
  · intro i j hij t _ ⟨k, hk⟩
    have hne : (f i : ℕ) ≠ f j := fun h => hij (f.injective h)
    -- the difference divides the speed of horse `i`
    have hd : ((f i : ℤ) - (f j : ℤ)) ∣ (f i : ℤ) := by
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have h1 := hdiv _ (hf i) _ (hf j) h
        have h2 : ((f j - f i : ℕ) : ℤ) ∣ (f i : ℤ) := by exact_mod_cast h1
        rw [Nat.cast_sub h.le] at h2
        rw [← neg_dvd, neg_sub]
        exact h2
      · have h1 := hdiv _ (hf j) _ (hf i) h
        have h2 : ((f i - f j : ℕ) : ℤ) ∣ (f j : ℤ) := by exact_mod_cast h1
        rw [Nat.cast_sub h.le] at h2
        have h3 : ((f i : ℤ) - (f j : ℤ)) ∣ ((f i : ℤ) - f j) + f j :=
          dvd_add (dvd_refl _) h2
        simpa using h3
    obtain ⟨c, hcd⟩ := hd
    refine ⟨c * k, ?_⟩
    have hcd' : ((f i : ℕ) : ℝ) = (((f i : ℤ) - (f j : ℤ)) * c : ℤ) := by
      rw [← hcd]; simp
    push_cast at hcd' ⊢
    rw [hcd', ← hk]
    ring
