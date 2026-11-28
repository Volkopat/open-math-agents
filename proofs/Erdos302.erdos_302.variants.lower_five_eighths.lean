import FormalConjectures.ErdosProblems.«302»

/-! Cambie: odd numbers up to N/4 together with (N/2, N]. A small odd a forces b, c even by parity, hence both above N/2. -/

open Filter Finset

theorem OMA.solution : type_of% @Erdos302.erdos_302.variants.lower_five_eighths := by
  intro f hf ε hε
  obtain ⟨M, hM⟩ := exists_nat_ge (1 / ε)
  refine eventually_atTop.2 ⟨M, fun N hMN => ?_⟩
  let S := (range ((N / 4 + 1) / 2)).image (2 * · + 1)
  let B := Ioc (N / 2) N
  have hA {a} (ha : a ∈ S ∪ B) : 0 < a ∧ 4 * a ≤ N ∧ a % 2 = 1 ∨ N < 2 * a ∧ a ≤ N := by
    rcases mem_union.1 ha with ha | ha
    · obtain ⟨i, hi, rfl⟩ := mem_image.1 ha; rw [mem_range] at hi; omega
    · have := mem_Ioc.1 ha; omega
  have hsub : S ∪ B ⊆ Icc 1 N := fun a ha => mem_Icc.2 (by have := hA ha; omega)
  have hno : Erdos302.NoUnitFractionTriple (S ∪ B) := by
    intro a ha b hb c hc _ _ _ h
    have := hA ha; have := hA hb; have := hA hc
    obtain ⟨_, _, _, _, _⟩ : 0 < a ∧ 0 < b ∧ 0 < c ∧ b ≤ N ∧ c ≤ N := by omega
    have hn : b * c = a * (c + b) := by
      field_simp at h; exact_mod_cast (by linarith : (b : ℚ) * c = a * (c + b))
    rcases hA ha with ⟨_, _, haO⟩ | _
    · have h := congrArg (· % 2) hn
      rcases Nat.mod_two_eq_zero_or_one b with h1 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one c with h2 | h2 <;>
        simp [Nat.mul_mod, Nat.add_mod, haO, h1, h2] at h
      have : N < 2 * b ∧ N < 2 * c := by omega
      nlinarith
    · nlinarith
  have hc : 5 * N ≤ 8 * (S ∪ B).card + 8 := by
    rw [card_union_of_disjoint (disjoint_left.2 fun a ha hb => by
        obtain ⟨i, hi, rfl⟩ := mem_image.1 ha; rw [mem_range] at hi; have := mem_Ioc.1 hb; omega),
      card_image_of_injective _ (fun _ _ h => by omega), card_range, Nat.card_Ioc]
    omega
  have : ((S ∪ B).card : ℝ) ≤ f N := by exact_mod_cast (hf N).2 ⟨_, hsub, hno, rfl⟩
  have : (5 : ℝ) * N ≤ 8 * (S ∪ B).card + 8 := by exact_mod_cast hc
  have : 1 ≤ ε * N := by rw [← div_le_iff₀' hε]; exact hM.trans (by exact_mod_cast hMN)
  linarith
