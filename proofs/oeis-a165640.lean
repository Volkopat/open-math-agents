import OMAStatements.S_oeis_a165640

namespace OMA.S_oeis_a165640



/-- The conjecture. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 1 ≤ n → (a n : ℤ) = ((4 * (n + 4) / 5 : ℕ) : ℤ) - ((2 * (n + 4) / 3 : ℕ) : ℤ)

/-- The allowed values of `z`. -/
def C (n z : ℕ) : Prop := 3 ≤ n + 2 * z ∧ 3 ∣ n + 2 * z ∧ 5 * z ≤ 2 * n + 3

instance (n : ℕ) : DecidablePred (C n) := fun z => by unfold C; infer_instance

theorem mem_S (n : ℕ) (t : ℕ × ℕ × ℕ) :
    t ∈ S n ↔ t.1 + t.2.1 + t.2.2 = n ∧ (t.2.1 : ℤ) + 3 * t.2.2 - 2 * t.1 = 3 := by
  unfold S
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product, Finset.mem_range,
    Finset.mem_range, Finset.mem_range]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by omega, by omega, by omega⟩, h1, h2⟩

theorem mem_T (n z : ℕ) : z ∈ (Finset.range (n + 1)).filter (C n) ↔ z < n + 1 ∧ C n z := by
  rw [Finset.mem_filter, Finset.mem_range]

theorem a_eq_count (n : ℕ) : a n = Nat.count (C n) (n + 1) := by
  rw [Nat.count_eq_card_filter_range, a]
  refine Finset.card_nbij' (fun t => t.2.2)
    (fun z => ((n + 2 * z) / 3 - 1, n - ((n + 2 * z) / 3 - 1) - z, z)) ?_ ?_ ?_ ?_
  · rintro ⟨x, y, z⟩ ht
    obtain ⟨h1, h2⟩ := (mem_S n (x, y, z)).mp ht
    dsimp only at h1 h2
    refine (mem_T n z).mpr ⟨by omega, by omega, ⟨x + 1, by omega⟩, by omega⟩
  · intro z hz
    obtain ⟨hz1, h3, ⟨k, hk⟩, h5⟩ := (mem_T n z).mp hz
    refine (mem_S n _).mpr ⟨?_, ?_⟩ <;> dsimp only <;> omega
  · rintro ⟨x, y, z⟩ ht
    obtain ⟨h1, h2⟩ := (mem_S n (x, y, z)).mp ht
    dsimp only at h1 h2
    have hx : (n + 2 * z) / 3 = x + 1 := by omega
    show ((n + 2 * z) / 3 - 1, n - ((n + 2 * z) / 3 - 1) - z, z) = (x, y, z)
    rw [hx, Nat.add_sub_cancel]
    have hy : n - x - z = y := by omega
    rw [hy]
  · intro z _
    rfl

theorem count_congr_lt {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] :
    ∀ n, (∀ i, i < n → (p i ↔ q i)) → Nat.count p n = Nat.count q n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro h
    rw [Nat.count_succ, Nat.count_succ, ih (fun i hi => h i (by omega))]
    have hn := h n (by omega)
    by_cases hp : p n
    · rw [if_pos hp, if_pos (hn.mp hp)]
    · rw [if_neg hp, if_neg (fun hq => hp (hn.mpr hq))]

theorem count_zero_of {p : ℕ → Prop} [DecidablePred p] :
    ∀ n, (∀ i, i < n → ¬ p i) → Nat.count p n = 0 := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro h
    rw [Nat.count_succ, ih (fun i hi => h i (by omega)), if_neg (h n (by omega))]

theorem step (n : ℕ) (hn : 1 ≤ n) :
    Nat.count (C (n + 15)) (n + 15 + 1) = Nat.count (C n) (n + 1) + 2 := by
  rw [show n + 15 + 1 = 6 + (n + 10) by omega, Nat.count_add]
  have h6 : Nat.count (C (n + 15)) 6 = 2 := by
    rw [Nat.count_eq_card_filter_range]
    have hcase : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hcase with h | h | h
    · rw [show (Finset.range 6).filter (C (n + 15)) = {0, 3} by
        ext z
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton, C]
        omega]
      rfl
    · rw [show (Finset.range 6).filter (C (n + 15)) = {1, 4} by
        ext z
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton, C]
        omega]
      rfl
    · rw [show (Finset.range 6).filter (C (n + 15)) = {2, 5} by
        ext z
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton, C]
        omega]
      rfl
  have hshift : Nat.count (fun z => C (n + 15) (6 + z)) (n + 10) = Nat.count (C n) (n + 10) :=
    count_congr_lt _ (fun z _ => by unfold C; omega)
  have htail : Nat.count (C n) (n + 10) = Nat.count (C n) (n + 1) := by
    rw [show n + 10 = (n + 1) + 9 by omega, Nat.count_add,
      count_zero_of 9 (fun i _ => by unfold C; omega), add_zero]
  rw [h6, hshift, htail]
  ring

theorem base : ∀ n, 1 ≤ n → n ≤ 15 →
    (Nat.count (C n) (n + 1) : ℤ) = ((4 * (n + 4) / 5 : ℕ) : ℤ) - ((2 * (n + 4) / 3 : ℕ) : ℤ) := by
  decide +kernel

theorem conjecture_true : Conjecture := by
  intro n hn
  rw [a_eq_count]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h15 : n ≤ 15
    · exact base n hn h15
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 15 := ⟨n - 15, by omega⟩
      rw [step m (by omega), Nat.cast_add, ih m (by omega) (by omega)]
      have e1 : 4 * (m + 15 + 4) / 5 = 4 * (m + 4) / 5 + 12 := by omega
      have e2 : 2 * (m + 15 + 4) / 3 = 2 * (m + 4) / 3 + 10 := by omega
      rw [e1, e2]
      push_cast
      ring

/-- Control: the first terms listed in the entry, `a(1..12) = 1, 0, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2`,
from the definition by multiplicities. -/
theorem first_terms : a 1 = 1 ∧ a 2 = 0 ∧ a 3 = 1 ∧ a 4 = 1 ∧ a 5 = 1 ∧ a 6 = 2 ∧ a 7 = 1 ∧
    a 8 = 1 ∧ a 9 = 2 ∧ a 10 = 2 ∧ a 11 = 2 ∧ a 12 = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end OMA.S_oeis_a165640

theorem OMA.solution : type_of% @OMA.S_oeis_a165640.main :=
  OMA.S_oeis_a165640.conjecture_true
