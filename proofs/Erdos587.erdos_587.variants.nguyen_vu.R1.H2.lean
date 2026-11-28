import OMAReductions.R_Erdos587_erdos_587_variants_nguyen_vu_R1

namespace E587Descent

theorem card_le_of_image {p : ℕ} (hp : 0 < p) {A B : Finset ℕ}
    (h : B.image (fun b => p * b) ⊆ A) : B.card ≤ A.card := by
  have := Finset.card_le_card h
  rwa [Finset.card_image_of_injective _ (fun x y e => Nat.eq_of_mul_eq_mul_left hp e)] at this

theorem descent (N : ℕ) (A : Finset ℕ) : ∀ k : ℕ, ∀ (p j : ℕ) (B : Finset ℕ), 0 < p →
    N / p < k → B ⊆ Finset.Icc 1 (N / p) → B.image (fun b => p * b) ⊆ A →
    2 * (N.log2 + 1) * A.card ≤ 2 * (N.log2 + 1) * B.card + j * A.card →
    2 ^ j ≤ p → (B.Nonempty ∨ A = ∅) →
    ∃ p : ℕ, 0 < p ∧ ∃ B : Finset ℕ, B ⊆ Finset.Icc 1 (N / p) ∧
      B.image (fun b => p * b) ⊆ A ∧ A.card ≤ 2 * B.card ∧
      ∀ d : ℕ, 2 ≤ d → B.card ≤ 2 * (N.log2 + 1) * (B.filter (fun b => ¬ d ∣ b)).card := by
  intro k
  induction k with
  | zero => intro p j B _ hk; exact absurd hk (Nat.not_lt_zero _)
  | succ k ih =>
    intro p j B hp hk hB hBA hinv hpow hne
    set L := N.log2 + 1 with hL
    have hBle := card_le_of_image hp hBA
    by_cases hall : ∀ d : ℕ, 2 ≤ d → B.card ≤ 2 * L * (B.filter (fun b => ¬ d ∣ b)).card
    · refine ⟨p, hp, B, hB, hBA, ?_, hall⟩
      rcases hne with ⟨b, hb⟩ | hA
      · have hb' := Finset.mem_Icc.mp (hB hb)
        have hpN : p ≤ N := by
          have h1 : 1 ≤ N / p := hb'.1.trans hb'.2
          have := (Nat.le_div_iff_mul_le hp).mp h1
          omega
        have hj : j ≤ N.log2 := (Nat.le_log2 (by omega)).mpr (hpow.trans hpN)
        have hjL : j ≤ L := by omega
        have : j * A.card ≤ L * A.card := Nat.mul_le_mul_right _ hjL
        have hLpos : 0 < L := by omega
        by_contra hc
        push Not at hc
        have : L * (2 * B.card) < L * A.card := Nat.mul_lt_mul_of_pos_left hc hLpos
        nlinarith
      · subst hA; simp
    · push Not at hall
      obtain ⟨d, hd, hlt⟩ := hall
      let B' := (B.filter (fun b => d ∣ b)).image (fun b => b / d)
      have hinj : Set.InjOn (fun b => b / d) (B.filter (fun b => d ∣ b) : Set ℕ) := by
        intro x hx y hy e
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
        have := Nat.div_mul_cancel hx.2
        have := Nat.div_mul_cancel hy.2
        simp only at e
        rw [← Nat.div_mul_cancel hx.2, ← Nat.div_mul_cancel hy.2, e]
      have hcard' : B'.card = (B.filter (fun b => d ∣ b)).card := Finset.card_image_of_injOn hinj
      have hsplit := Finset.card_filter_add_card_filter_not (s := B) (fun b => d ∣ b)
      have hBne : B.Nonempty := by
        rcases hne with h | h
        · exact h
        · subst h
          simp at hBle
          subst hBle
          simp at hlt
      have hNp : 0 < N / p := by
        obtain ⟨b, hb⟩ := hBne
        have := Finset.mem_Icc.mp (hB hb)
        omega
      have hpd : 0 < p * d := by positivity
      refine ih (p * d) (j + 1) B' hpd ?_ ?_ ?_ ?_ ?_ ?_
      · rw [← Nat.div_div_eq_div_mul]
        have := Nat.div_lt_self hNp (show 1 < d by omega)
        omega
      · intro c hc
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hc
        obtain ⟨hbB, hdb⟩ := Finset.mem_filter.mp hb
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp (hB hbB)
        obtain ⟨c, rfl⟩ := hdb
        rw [Nat.mul_div_cancel_left _ (by omega)]
        refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
        · rcases Nat.eq_zero_or_pos c with e | e
          · subst e; omega
          · exact e
        · rw [← Nat.div_div_eq_div_mul]
          exact (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact h2)
      · intro x hx
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hc
        obtain ⟨hbB, hdb⟩ := Finset.mem_filter.mp hb
        have : p * d * (b / d) = p * b := by rw [mul_assoc, Nat.mul_div_cancel' hdb]
        rw [this]
        exact hBA (Finset.mem_image_of_mem _ hbB)
      · rw [hcard']
        have hc2 : 2 * L * (B.filter (fun b => ¬ d ∣ b)).card < A.card := lt_of_lt_of_le hlt hBle
        nlinarith
      · rw [pow_succ]; exact Nat.mul_le_mul hpow hd
      · left
        by_contra hem
        rw [Finset.not_nonempty_iff_eq_empty, Finset.image_eq_empty] at hem
        rw [hem] at hsplit
        simp at hsplit
        rw [← hsplit] at hlt
        have : 0 < (B.filter (fun b => ¬ d ∣ b)).card := by
          rw [hsplit]; exact Finset.card_pos.mpr hBne
        nlinarith

end E587Descent

theorem OMA.solution : OMA.R_Erdos587_erdos_587_variants_nguyen_vu_R1.H2 := by
  intro N A hA
  apply E587Descent.descent N A (N / 1 + 1) 1 0 A one_pos (by omega) (by simpa using hA)
    (by simp) (by simp) (by simp)
  rcases A.eq_empty_or_nonempty with h | h
  · exact Or.inr h
  · exact Or.inl h
