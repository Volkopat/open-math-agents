import OMAStatements.S_oeis_a000105

-- Credit: @siddsg7
namespace OMA.R_oeis_a000105_R1

open OMA.S_oeis_a000105

/-- Pattern-theorem input for translation classes. An empty cell surrounded by four
occupied neighbors is compatible with a polyomino, as witnessed by the 3 × 3 ring.
The pattern theorem of Madras (1999) implies vanishing frequency for animals avoiding it. -/
def H1 : Prop :=
  let fixed (n : ℕ) (P : Finset (ℤ × ℤ) → Prop) :=
    Nat.card (Quot (fun S T : {S : Finset (ℤ × ℤ) // IsPolyomino n S ∧ P S} =>
      ∃ d : ℤ × ℤ, T.1 = S.1.image (fun p => p + d)))
  let avoids (S : Finset (ℤ × ℤ)) :=
    ∀ c : ℤ × ℤ, c ∉ S → ∃ q : ℤ × ℤ, q ∉ S ∧ gridAdj c q
  Filter.Tendsto (fun n => (fixed n avoids : ℝ) / fixed n (fun _ => True)) Filter.atTop (nhds 0)

/-- Counting input for forgetting orientations. Each free shape has at most eight
orientations up to translation. The bounds also allow enlarging the predicate on shapes. -/
def H2 : Prop :=
  let fixed (n : ℕ) (P : Finset (ℤ × ℤ) → Prop) :=
    Nat.card (Quot (fun S T : {S : Finset (ℤ × ℤ) // IsPolyomino n S ∧ P S} =>
      ∃ d : ℤ × ℤ, T.1 = S.1.image (fun p => p + d)))
  let free (n : ℕ) (P : Finset (ℤ × ℤ) → Prop) :=
    Nat.card (Quot (fun S T : {S : Finset (ℤ × ℤ) // IsPolyomino n S ∧ P S} =>
      GridSymEq S.1 T.1))
  ∀ n (P Q : Finset (ℤ × ℤ) → Prop), (∀ S, P S → Q S) →
    free n P ≤ fixed n Q ∧ fixed n P ≤ 8 * free n Q

lemma holeFree_has_neighbor (S : Finset (ℤ × ℤ)) (h : IsHoleFree S)
    (c : ℤ × ℤ) (hc : c ∉ S) : ∃ q : ℤ × ℤ, q ∉ S ∧ gridAdj c q := by
  obtain ⟨b, hb⟩ := Infinite.exists_notMem_finset (insert c S)
  rw [Finset.mem_insert, not_or] at hb
  rcases (h c hc b hb.2).cases_head with heq | ⟨q, hq, _⟩
  · exact (hb.1 heq.symm).elim
  · exact ⟨q, hq.2⟩

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a000105.main := by
  intro hp ho
  let fixed (n : ℕ) (P : Finset (ℤ × ℤ) → Prop) :=
    Nat.card (Quot (fun S T : {S : Finset (ℤ × ℤ) // IsPolyomino n S ∧ P S} =>
      ∃ d : ℤ × ℤ, T.1 = S.1.image (fun p => p + d)))
  let free (n : ℕ) (P : Finset (ℤ × ℤ) → Prop) :=
    Nat.card (Quot (fun S T : {S : Finset (ℤ × ℤ) // IsPolyomino n S ∧ P S} =>
      GridSymEq S.1 T.1))
  let avoids (S : Finset (ℤ × ℤ)) :=
    ∀ c : ℤ × ℤ, c ∉ S → ∃ q : ℤ × ℤ, q ∉ S ∧ gridAdj c q
  change Filter.Tendsto (fun n => (fixed n avoids : ℝ) / fixed n (fun _ => True)) Filter.atTop (nhds 0) at hp
  change ∀ n (P Q : Finset (ℤ × ℤ) → Prop), (∀ S, P S → Q S) →
    free n P ≤ fixed n Q ∧ fixed n P ≤ 8 * free n Q at ho
  have limit : Filter.Tendsto (fun n => (8 : ℝ) * ((fixed n avoids : ℝ) /
      fixed n (fun _ => True))) Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (8 : ℝ))).mul hp
  apply squeeze_zero (fun n => by positivity) _ limit
  intro n
  have hbad := (ho n IsHoleFree avoids holeFree_has_neighbor).1
  change holeFreePolyominoCount n ≤ fixed n avoids at hbad
  have hall := ho n (fun _ => True) (fun _ => True) (fun _ h => h)
  have heq : free n (fun _ => True) = freePolyominoCount n := by
    have hpred : (fun S => IsPolyomino n S ∧ True) = IsPolyomino n := by
      funext S
      simp
    unfold free freePolyominoCount
    rw [hpred]
  rw [heq] at hall
  by_cases hz : freePolyominoCount n = 0
  · simp only [hz, Nat.cast_zero, div_zero]
    positivity
  have hden : (0 : ℝ) < freePolyominoCount n := by exact_mod_cast Nat.pos_of_ne_zero hz
  have htNat := lt_of_lt_of_le (Nat.pos_of_ne_zero hz) hall.1
  have ht : (0 : ℝ) < fixed n (fun _ => True) := by exact_mod_cast htNat
  rw [← mul_div_assoc, div_le_div_iff₀ hden ht]
  have hA : (holeFreePolyominoCount n : ℝ) ≤ fixed n avoids := by exact_mod_cast hbad
  have hB : (fixed n (fun _ => True) : ℝ) ≤ 8 * (freePolyominoCount n : ℝ) := by
    exact_mod_cast hall.2
  calc
    _ ≤ (fixed n avoids : ℝ) * (8 * freePolyominoCount n) := by gcongr
    _ = _ := by ring

end OMA.R_oeis_a000105_R1
