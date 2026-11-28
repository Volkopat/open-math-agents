import OMAReductions.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1_H1_R1

/-!
Proof of `Erdos3.erdos_3.variants.leng_sah_sawhney.R1.H1.R1.H2`.

Method:
1. Since `A` is `k`-AP-free (`k ≥ 2`), every `(a, d)` with `a + i * d ∈ A` for all `i < k`
   must satisfy `d = 0`, so `count A ≤ A.card`, hence `(count A : ℝ) / total ≤ δ / N`.
2. Every `(a, d) ∈ Icc 1 (N / 2) ×ˢ range (N / (2 * k) + 1)` satisfies `a + i * d ∈ Icc 1 N`
   for all `i < k`, giving `count (Icc 1 N) ≥ (N / 2) * (N / (2 * k) + 1) ≥ (N + 1)^2 / (9 * k)`.
3. Since `128 * k ≤ N * δ ^ (k - 1)`, we have `δ / N ≤ δ ^ k / (128 * k)`, so
   `δ ^ k * count (Icc 1 N) / total - count A / total ≥ (1/9 - 1/128) * δ ^ k / k ≥ δ ^ k / (128 * k)`.
-/

section Erdos3LSSH2

open Finset

private lemma no_pos_ap {A : Finset ℕ} {k a d : ℕ}
    (hfree : (A : Set ℕ).IsAPOfLengthFree k) (hk : 2 ≤ k) (hd : 0 < d)
    (hmem : ∀ i < k, a + i * d ∈ A) : False := by
  classical
  let T := (range k).image (fun i : ℕ => a + i * d)
  have hinj : Function.Injective (fun i : ℕ => a + i * d) := by
    intro i j he
    exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel he)
  have hcard : T.card = k := by
    simp only [T, card_image_of_injective _ hinj, card_range]
  have hsubset : (T : Set ℕ) ⊆ A := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    exact hmem i (mem_range.mp hi)
  have hp : (T : Set ℕ).IsAPOfLength k := by
    refine ⟨a, d, ?_, ?_⟩
    · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard, hcard]
    · ext x
      constructor
      · intro hx
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
        exact ⟨i, by exact_mod_cast (mem_range.mp hi), by simp⟩
      · rintro ⟨i, hi, rfl⟩
        have hi' : i < k := by exact_mod_cast hi
        exact mem_image.mpr ⟨i, mem_range.mpr hi', by simp⟩
  have hle : (k : ENat) ≤ 1 := hfree T hsubset hp
  have hle' : k ≤ 1 := by exact_mod_cast hle
  omega

theorem OMA.solution :
    OMA.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1_H1_R1.H2 := by
  classical
  intro N k A hk hkN hAsub hfree count δ total hdens
  have hN4 : 4 ≤ N := by omega
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
  have htot_pos : 0 < total := by dsimp only [total]; positivity
  -- Step 1: count A ≤ A.card
  have hcountA : count A ≤ A.card := by
    have hsub : ((range (N + 1) ×ˢ range (N + 1)).filter
        (fun p => ∀ i < k, p.1 + i * p.2 ∈ A)) ⊆ A.image (fun a => (a, 0)) := by
      intro p hp
      obtain ⟨_, hall⟩ := mem_filter.mp hp
      have hp2 : p.2 = 0 := by
        by_contra hne
        exact no_pos_ap hfree hk (Nat.pos_of_ne_zero hne) hall
      have hp1 : p.1 ∈ A := by simpa using hall 0 (by omega)
      exact mem_image.mpr ⟨p.1, hp1, Prod.ext rfl hp2.symm⟩
    exact (card_le_card hsub).trans card_image_le
  -- Step 2: (N + 1)^2 ≤ 9 * k * count (Icc 1 N)
  have hcountIcc : (N + 1) ^ 2 ≤ 9 * k * count (Icc 1 N) := by
    let B := Icc 1 (N / 2) ×ˢ range (N / (2 * k) + 1)
    have hsub : B ⊆ (range (N + 1) ×ˢ range (N + 1)).filter
        (fun p => ∀ i < k, p.1 + i * p.2 ∈ Icc 1 N) := by
      intro p hp
      obtain ⟨h1, h2⟩ := mem_product.mp hp
      obtain ⟨ha1, ha2⟩ := mem_Icc.mp h1
      have hd : p.2 ≤ N / (2 * k) := Nat.lt_succ_iff.mp (mem_range.mp h2)
      refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (by omega),
        mem_range.mpr (by have := Nat.div_le_self N (2 * k); omega)⟩, ?_⟩
      intro i hi
      refine mem_Icc.mpr ⟨by omega, ?_⟩
      have hmul : i * p.2 ≤ N / 2 := by
        have h1' : 2 * k * p.2 ≤ N :=
          (Nat.mul_le_mul_left (2 * k) hd).trans (Nat.mul_div_le N (2 * k))
        have h2' : 2 * (i * p.2) ≤ 2 * k * p.2 := by
          have : 2 * i ≤ 2 * k := by omega
          calc 2 * (i * p.2) = (2 * i) * p.2 := by ring
            _ ≤ (2 * k) * p.2 := Nat.mul_le_mul_right _ this
        omega
      omega
    have hcardB : B.card = (N / 2) * (N / (2 * k) + 1) := by
      simp [B, Nat.card_Icc]
    have hle1 : N + 1 ≤ 3 * (N / 2) := by omega
    have hle2 : N + 1 ≤ 3 * k * (N / (2 * k) + 1) := by
      have hdiv : N < 2 * k * (N / (2 * k) + 1) := by
        have := Nat.div_add_mod N (2 * k)
        have := Nat.mod_lt N (show 0 < 2 * k by omega)
        nlinarith
      nlinarith
    have hprod : (N + 1) ^ 2 ≤ 9 * k * B.card := by
      rw [hcardB]
      calc (N + 1) ^ 2 = (N + 1) * (N + 1) := sq (N + 1)
        _ ≤ (3 * (N / 2)) * (3 * k * (N / (2 * k) + 1)) := Nat.mul_le_mul hle1 hle2
        _ = 9 * k * ((N / 2) * (N / (2 * k) + 1)) := by ring
    exact hprod.trans (Nat.mul_le_mul_left _ (card_le_card hsub))
  -- Step 3: δ > 0 and compare the two terms
  have hδ_nonneg : 0 ≤ δ := by dsimp only [δ]; positivity
  have hδ_pos : 0 < δ := by
    by_contra hle
    have hδ0 : δ = 0 := le_antisymm (not_lt.mp hle) hδ_nonneg
    have hpow0 : δ ^ (k - 1) = 0 := by
      rw [hδ0, zero_pow (by omega : k - 1 ≠ 0)]
    rw [hpow0, mul_zero] at hdens
    linarith
  have hterm1 : (count A : ℝ) / total ≤ δ ^ k / (128 * (k : ℝ)) := by
    have h1 : (count A : ℝ) / total ≤ (A.card : ℝ) / (N : ℝ) ^ 2 := by
      have hNsq : (N : ℝ) ^ 2 ≤ total := by
        dsimp only [total]; nlinarith
      calc (count A : ℝ) / total
          ≤ (A.card : ℝ) / total := div_le_div_of_nonneg_right (by exact_mod_cast hcountA) htot_pos.le
        _ ≤ (A.card : ℝ) / (N : ℝ) ^ 2 := div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hNsq
    have h2 : (A.card : ℝ) / (N : ℝ) ^ 2 = δ / (N : ℝ) := by
      dsimp only [δ]; field_simp [hN_pos.ne']
    have h3 : δ / (N : ℝ) ≤ δ ^ k / (128 * (k : ℝ)) := by
      rw [div_le_div_iff₀ hN_pos (by positivity)]
      have hpow : δ ^ k = δ * δ ^ (k - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k)]
      rw [hpow]
      have hmul := mul_le_mul_of_nonneg_left hdens hδ_nonneg
      linarith
    exact h1.trans (h2.le.trans h3)
  have hterm2 : δ ^ k / (9 * (k : ℝ)) ≤ δ ^ k * (count (Icc 1 N) : ℝ) / total := by
    have hIccR : total ≤ 9 * (k : ℝ) * (count (Icc 1 N) : ℝ) := by
      dsimp only [total]
      exact_mod_cast hcountIcc
    rw [mul_div_assoc, div_le_iff₀ (by positivity)]
    have h1 : 1 / (9 * (k : ℝ)) ≤ (count (Icc 1 N) : ℝ) / total := by
      rw [div_le_div_iff₀ (by positivity) htot_pos]
      linarith
    calc δ ^ k = δ ^ k * (1 / (9 * (k : ℝ))) * (9 * (k : ℝ)) := by field_simp [hk_pos.ne']
      _ ≤ δ ^ k * ((count (Icc 1 N) : ℝ) / total) * (9 * (k : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) (by positivity)
  have hdiff : δ ^ k / (128 * (k : ℝ)) ≤
      δ ^ k * (count (Icc 1 N) : ℝ) / total - (count A : ℝ) / total := by
    have hdk_pos : 0 < δ ^ k / (k : ℝ) := by positivity
    have hgap : δ ^ k / (128 * (k : ℝ)) + δ ^ k / (128 * (k : ℝ)) ≤ δ ^ k / (9 * (k : ℝ)) := by
      have : (2 / 128 : ℝ) ≤ 1 / 9 := by norm_num
      calc δ ^ k / (128 * (k : ℝ)) + δ ^ k / (128 * (k : ℝ))
          = (2 / 128 : ℝ) * (δ ^ k / (k : ℝ)) := by ring
        _ ≤ (1 / 9 : ℝ) * (δ ^ k / (k : ℝ)) := mul_le_mul_of_nonneg_right this hdk_pos.le
        _ = δ ^ k / (9 * (k : ℝ)) := by ring
    linarith
  exact hdiff.trans (by rw [abs_sub_comm]; exact le_abs_self _)

end Erdos3LSSH2
