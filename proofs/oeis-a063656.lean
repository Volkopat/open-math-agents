import OMAStatements.S_oeis_a063656

namespace OMA.S_oeis_a063656




lemma isTerm_iff (k : ℕ) : IsTerm k ↔ k ≤ Nat.sqrt k * Nat.sqrt k + Nat.sqrt k := by
  unfold IsTerm
  rw [round_eq, Int.floor_eq_iff]
  set s := Nat.sqrt k with hsdef
  have hs : s * s ≤ k := Nat.sqrt_le k
  have hsq : (s : ℝ) ≤ Real.sqrt k := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    exact_mod_cast (by nlinarith : s ^ 2 ≤ k)
  have hpos : (0 : ℝ) < (s : ℝ) + 1 / 2 := by positivity
  have key : Real.sqrt k < (s : ℝ) + 1 / 2 ↔ k ≤ s * s + s := by
    rw [Real.sqrt_lt' hpos]
    constructor
    · intro h
      have h' : (k : ℝ) < ((s * s + s + 1 : ℕ) : ℝ) := by push_cast; nlinarith
      have := Nat.cast_lt.mp h'
      omega
    · intro h
      have h' : (k : ℝ) ≤ ((s * s + s : ℕ) : ℝ) := Nat.cast_le.mpr h
      push_cast at h'
      nlinarith
  push_cast
  constructor
  · rintro ⟨_, h2⟩
    exact key.mp (by linarith)
  · intro h
    have := key.mpr h
    constructor <;> linarith

instance decIsTerm : DecidablePred IsTerm := fun k => decidable_of_iff _ (isTerm_iff k).symm

lemma sqrt_block (m j : ℕ) (hj : j ≤ m + m) : Nat.sqrt (m * m + j) = m := Nat.sqrt_add_eq m hj

lemma isTerm_block (m j : ℕ) (hj : j ≤ m + m) : IsTerm (m * m + j) ↔ j ≤ m := by
  rw [isTerm_iff, sqrt_block m j hj]
  omega

lemma tri_succ (m : ℕ) : (m + 1) * (m + 1 + 1) / 2 = m * (m + 1) / 2 + (m + 1) := by
  have : (m + 1) * (m + 1 + 1) = m * (m + 1) + (m + 1) * 2 := by ring
  rw [this, Nat.add_mul_div_right _ _ (by norm_num)]

lemma count_in_block (m : ℕ) (h0 : Nat.count IsTerm (m * m) = m * (m + 1) / 2) :
    ∀ j, j ≤ m + 1 → Nat.count IsTerm (m * m + j) = m * (m + 1) / 2 + j := by
  intro j
  induction j with
  | zero => intro _; simpa using h0
  | succ j ih =>
    intro hj
    rw [← Nat.add_assoc, Nat.count_succ, ih (by omega),
      if_pos ((isTerm_block m j (by omega)).mpr (by omega))]
    ring

lemma count_gap (m : ℕ) (h1 : Nat.count IsTerm (m * m + (m + 1)) = (m + 1) * (m + 1 + 1) / 2) :
    ∀ i, i ≤ m → Nat.count IsTerm (m * m + (m + 1) + i) = (m + 1) * (m + 1 + 1) / 2 := by
  intro i
  induction i with
  | zero => intro _; simpa using h1
  | succ i ih =>
    intro hi
    have hnot : ¬ IsTerm (m * m + (m + 1) + i) := by
      intro h
      rw [Nat.add_assoc] at h
      have := (isTerm_block m (m + 1 + i) (by omega)).mp h
      omega
    rw [← Nat.add_assoc, Nat.count_succ, ih (by omega), if_neg hnot, Nat.add_zero]

lemma count_square (m : ℕ) : Nat.count IsTerm (m * m) = m * (m + 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 := count_in_block m ih (m + 1) le_rfl
    rw [← tri_succ] at h1
    have h2 := count_gap m h1 m le_rfl
    rw [show (m + 1) * (m + 1) = m * m + (m + 1) + m by ring]
    exact h2

lemma a_block (m j : ℕ) (hj : j ≤ m) : a (m * (m + 1) / 2 + j) = m * m + j := by
  unfold a
  rw [← count_in_block m (count_square m) j (by omega)]
  exact Nat.nth_count ((isTerm_block m j (by omega)).mpr hj)

lemma decompose (n : ℕ) : ∃ m j, j ≤ m ∧ n = m * (m + 1) / 2 + j := by
  induction n with
  | zero => exact ⟨0, 0, le_rfl, by simp⟩
  | succ n ih =>
    obtain ⟨m, j, hj, rfl⟩ := ih
    rcases Nat.lt_or_ge j m with h | h
    · exact ⟨m, j + 1, by omega, by ring⟩
    · have hjm : j = m := le_antisymm hj h
      subst hjm
      exact ⟨j + 1, 0, Nat.zero_le _, by rw [tri_succ]; ring⟩

lemma tri_mono {s t : ℕ} (h : s ≤ t) : s * (s + 1) / 2 ≤ t * (t + 1) / 2 :=
  Nat.div_le_div_right (Nat.mul_le_mul h (by omega))

lemma not_tri (m j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ m) : ¬ IsTri (m * (m + 1) / 2 + j) := by
  rintro ⟨t, ht⟩
  rcases Nat.lt_or_ge t (m + 1) with h | h
  · have := tri_mono (show t ≤ m by omega)
    omega
  · have := tri_mono h
    rw [tri_succ] at this
    omega

lemma not_square_between (m x : ℕ) (h1 : m * m < x) (h2 : x < (m + 1) * (m + 1)) : ¬ IsSquare x := by
  rintro ⟨r, rfl⟩
  rcases Nat.lt_or_ge r (m + 1) with h | h
  · have : r ≤ m := by omega
    have := Nat.mul_le_mul this this
    omega
  · have := Nat.mul_le_mul h h
    omega

theorem conjecture : a 1 = 1 ∧ ∀ n, 2 ≤ n →
    a (n - 1) < a n ∧ (IsSquare (a n) ↔ IsTri n) ∧
      ∀ m, a (n - 1) < m → m < a n → ¬ (IsSquare m ↔ IsTri n) := by
  refine ⟨?_, ?_⟩
  · have := a_block 1 0 (Nat.zero_le 1)
    simpa using this
  intro n hn
  obtain ⟨m, j, hj, rfl⟩ := decompose n
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · -- n = T(m), a triangular index, m >= 2
    subst h0
    have hm : 2 ≤ m := by
      by_contra hlt
      interval_cases m <;> simp at hn
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hprev : k + 1 + 0 = k + 1 := rfl
    have hidx : (k + 1) * (k + 1 + 1) / 2 + 0 - 1 = k * (k + 1) / 2 + k := by
      rw [tri_succ]; omega
    have hcur := a_block (k + 1) 0 (by omega)
    have hpr := a_block k k le_rfl
    rw [hidx, hpr, hcur]
    have htri : IsTri ((k + 1) * (k + 1 + 1) / 2 + 0) := ⟨k + 1, by ring⟩
    refine ⟨by nlinarith, ⟨fun _ => htri, fun _ => ⟨k + 1, by ring⟩⟩, ?_⟩
    intro x hx1 hx2 hiff
    have hsq : IsSquare x := hiff.mpr htri
    exact not_square_between k x (by omega) (by nlinarith) hsq
  · -- inside a block: n = T(m) + j with 1 <= j <= m
    have hidx : m * (m + 1) / 2 + j - 1 = m * (m + 1) / 2 + (j - 1) := by omega
    rw [hidx, a_block m (j - 1) (by omega), a_block m j hj]
    have hnt := not_tri m j hpos hj
    have hns : ¬ IsSquare (m * m + j) :=
      not_square_between m _ (by omega) (by nlinarith)
    refine ⟨by omega, ⟨fun h => absurd h hns, fun h => absurd h hnt⟩, ?_⟩
    intro x hx1 hx2
    omega

/-- Control: the first terms 0, 1, 2, 4, 5, 6, 9. -/
theorem control : a 0 = 0 ∧ a 3 = 4 ∧ a 6 = 9 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using a_block 0 0 (Nat.zero_le 0)
  · simpa using a_block 2 0 (by norm_num)
  · simpa using a_block 3 0 (by norm_num)

end OMA.S_oeis_a063656

theorem OMA.solution : type_of% @OMA.S_oeis_a063656.main :=
  OMA.S_oeis_a063656.conjecture
