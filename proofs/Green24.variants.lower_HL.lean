import FormalConjectures.GreensOpenProblems.«24»

/-! Shorter proof of `Green24.variants.lower_HL`. -/

open Green24 Green24.variants Filter Finset

theorem OMA.solution : type_of% @Green24.variants.lower_HL := by
  unfold gamma
  refine le_limsup_of_frequently_le (frequently_atTop.mpr fun n => ?_)
    ⟨1, eventually_map.mpr (.of_forall fun n => by
      by_cases hn : n = 0
      · simp [hn]
      · exact (div_le_one (by positivity)).mpr (by exact_mod_cast upper_trivial (n := n)))⟩
  let m := n + 1
  refine ⟨6 * m, by omega, ?_⟩
  let A : Finset ℤ := Ico 0 (6 * m)
  let P := (A ×ˢ A).filter fun p => p.1 ≠ p.2 ∧ p.1 + 3 * (p.2 - p.1) ∈ A
  let f (u : Fin (3 * m) × Fin m) : ℤ × ℤ := (u.1.val, (u.1.val : ℤ) + u.2.val + 1)
  have hlo : 3 * m * m ≤ P.card := by
    simpa using Fintype.card_le_of_embedding (⟨fun u => ⟨f u, by
      have := u.1.isLt; have := u.2.isLt; simp [P, A, f]; omega⟩, fun u v h => by
      have hv : f u = f v := congrArg Subtype.val h
      simp only [f, Prod.mk.injEq] at hv
      ext <;> omega⟩ :
      Fin (3 * m) × Fin m ↪ P)
  have hhi : P.card ≤ max013AffineTranslates (6 * m) := le_csSup
    ⟨(6 * m) ^ 2, by rintro _ ⟨B, hB, rfl⟩; exact (card_filter_le ..).trans_eq (by simp [hB, sq])⟩
    ⟨A, by simp [A, Int.card_Ico]; omega, rfl⟩
  have hh : 3 * (m : ℝ) * m ≤ max013AffineTranslates (6 * m) := by exact_mod_cast hlo.trans hhi
  have : (0 : ℝ) < m := by positivity
  push_cast; exact (le_div_iff₀ (by positivity)).mpr (by nlinarith)
