import OMAStatements.S_oeis_a104385

namespace ThreeDistinctParts

open Finset OMA.S_oeis_a104385

private def triples (m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((range (m + 1) ×ˢ range (m + 1) ×ˢ range (m + 1)).filter fun t =>
    0 < t.1 ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.1 + t.2.1 + t.2.2 = m)

private theorem mem_triples (m x y z : ℕ) :
    (x, y, z) ∈ triples m ↔ 0 < x ∧ x < y ∧ y < z ∧ x + y + z = m := by
  simp only [triples, mem_filter, mem_product, mem_range]
  omega

private theorem high_card (m : ℕ) : ((triples (m + 6)).filter (fun t => 3 ≤ t.1)).card = p3 m := by
  change ((triples (m + 6)).filter (fun t => 3 ≤ t.1)).card = (triples m).card
  apply card_bij (fun t _ => (t.1 - 2, t.2.1 - 2, t.2.2 - 2))
  · rintro ⟨x, y, z⟩ ht
    simp only [mem_filter, mem_triples] at ht ⊢
    omega
  · rintro ⟨x, y, z⟩ ht ⟨x', y', z'⟩ ht' he
    simp only [mem_filter, mem_triples] at ht ht'
    simp only [Prod.mk.injEq] at he ⊢
    omega
  · rintro ⟨x, y, z⟩ ht
    simp only [mem_triples] at ht
    refine ⟨(x + 2, y + 2, z + 2), ?_, ?_⟩
    · simp only [mem_filter, mem_triples]
      omega
    · simp

private theorem fixed_first (m a : ℕ) (ha : 0 < a) :
    ((triples m).filter (fun t => t.1 = a)).card = ((m - a - 1) / 2 + 1 - (a + 1)) := by
  rw [← Nat.card_Icc]
  apply card_bij (fun t _ => t.2.1)
  · rintro ⟨x, y, z⟩ ht
    simp only [mem_filter, mem_triples, mem_Icc] at ht ⊢
    omega
  · rintro ⟨x, y, z⟩ ht ⟨x', y', z'⟩ ht' he
    simp only [mem_filter, mem_triples] at ht ht'
    simp only [Prod.mk.injEq] at he ⊢
    omega
  · intro y hy
    simp only [mem_Icc] at hy
    refine ⟨(a, y, m - a - y), ?_, rfl⟩
    simp only [mem_filter, mem_triples]
    have hbalance : a + 2 * y + 1 ≤ m := by omega
    exact ⟨⟨ha, by omega, by omega, by omega⟩, trivial⟩

private theorem step (m : ℕ) (hm : 1 ≤ m) : p3 (m + 6) = p3 m + m := by
  let S := triples (m + 6)
  have he : S.filter (fun t => ¬ 3 ≤ t.1) =
      S.filter (fun t => t.1 = 1) ∪ S.filter (fun t => t.1 = 2) := by
    ext t
    rcases t with ⟨x, y, z⟩
    simp only [S, mem_union, mem_filter, mem_triples]
    omega
  have hd : Disjoint (S.filter (fun t => t.1 = 1)) (S.filter (fun t => t.1 = 2)) := by
    rw [Finset.disjoint_left]
    intro t ht₁ ht₂
    have h₁ := (mem_filter.mp ht₁).2
    have h₂ := (mem_filter.mp ht₂).2
    omega
  have hs := card_filter_add_card_filter_not (s := S) (fun t => 3 ≤ t.1)
  rw [he, card_union_of_disjoint hd, high_card, fixed_first _ _ (by decide : 0 < 1),
    fixed_first _ _ (by decide : 0 < 2)] at hs
  change p3 m + _ = p3 (m + 6) at hs
  omega

private theorem formula (m : ℕ) (hm : 1 ≤ m) :
    (p3 m : ℤ) = round (((m : ℝ) - 3) ^ 2 / 12 + 1 / 72) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hsmall : m ≤ 6
    · interval_cases m <;> norm_num [show p3 1 = 0 by decide, show p3 2 = 0 by decide,
        show p3 3 = 0 by decide, show p3 4 = 0 by decide, show p3 5 = 0 by decide,
        show p3 6 = 1 by decide, round_eq_iff]
    · let j := m - 6
      have hj : 1 ≤ j := by dsimp [j]; omega
      have hjm : j < m := by dsimp [j]; omega
      rw [show m = j + 6 by dsimp [j]; omega, step j hj, Nat.cast_add, ih j hjm hj]
      have he : (((j + 6 : ℕ) : ℝ) - 3) ^ 2 / 12 + 1 / 72 =
          ((j : ℝ) - 3) ^ 2 / 12 + 1 / 72 + ((j : ℤ) : ℝ) := by push_cast; ring
      rw [he, round_add_intCast]

private theorem solution : type_of% @OMA.S_oeis_a104385.main := by
  intro n hn
  have hm : 1 ≤ n * (n + 1) / 2 := by
    have h := Nat.mul_le_mul hn (show 2 ≤ n + 1 by omega)
    omega
  have hd : 2 ∣ n * (n + 1) := Nat.two_dvd_mul_add_one n
  rw [formula _ hm, Nat.cast_div hd (by norm_num : (2 : ℝ) ≠ 0)]
  push_cast
  congr 1
  ring

end ThreeDistinctParts

theorem OMA.solution : type_of% @OMA.S_oeis_a104385.main := ThreeDistinctParts.solution
