import OMAStatements.S_oeis_a351652

namespace OMA.S_oeis_a351652

private theorem periodicCoeffs_square (t : ℕ) : periodicCoeffs (t ^ 2) = ∅ := by
  have hs : Real.sqrt (↑(t ^ 2) : ℝ) = ((t : ℤ) : ℝ) := by
    push_cast
    exact Real.sqrt_sq (by positivity)
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro b hb
  obtain ⟨j, _, p, hj, _⟩ := hb 0
  rw [hs, GenContFract.of_s_of_int] at hj
  simp at hj

private theorem next_spec (n : ℕ) :
    eligible (a n) (state n).2 (a (n + 1)) ∧
    (state (n + 1)).2 = insert (a (n + 1)) (state n).2 ∧
    ∀ m, eligible (a n) (state n).2 m → a (n + 1) ≤ m := by
  classical
  let t := (state n).2.sup id + 1
  have ht : 0 < t := by dsimp [t]; omega
  have h : ∃ m, eligible (state n).1 (state n).2 m := by
    refine ⟨t ^ 2, by positivity, ?_, by simp [periodicCoeffs_square]⟩
    intro hm
    have hb : t ^ 2 ≤ (state n).2.sup id := Finset.le_sup (f := id) hm
    have ht' := Nat.le_self_pow (by decide : 2 ≠ 0) t
    dsimp [t] at ht' hb
    omega
  have hn : state (n + 1) = (Nat.find h, insert (Nat.find h) (state n).2) := by
    simp only [state, dif_pos h]
  change eligible (state n).1 (state n).2 (state (n + 1)).1 ∧
    (state (n + 1)).2 = insert (state (n + 1)).1 (state n).2 ∧
    ∀ m, eligible (state n).1 (state n).2 m → (state (n + 1)).1 ≤ m
  rw [hn]
  exact ⟨Nat.find_spec h, rfl, fun _ hm => Nat.find_min' h hm⟩

private theorem seen_iff (n m : ℕ) :
    m ∈ (state n).2 ↔ ∃ i ≤ n, a i = m := by
  induction n with
  | zero => simp [state, a, eq_comm]
  | succ n ih =>
    rw [(next_spec n).2.1, Finset.mem_insert, ih]
    constructor
    · rintro (rfl | ⟨i, hi, he⟩)
      · exact ⟨n + 1, le_rfl, rfl⟩
      · exact ⟨i, by omega, he⟩
    · rintro ⟨i, hi, he⟩
      by_cases h : i = n + 1
      · exact Or.inl (by simpa only [h] using he.symm)
      · exact Or.inr ⟨i, by omega, he⟩

private theorem a_pos (n : ℕ) : 0 < a n := by
  cases n with
  | zero => decide
  | succ n => exact (next_spec n).1.1

private theorem a_ne_of_lt {i j : ℕ} (hij : i < j) : a i ≠ a j := by
  intro he
  cases j with
  | zero => omega
  | succ j =>
    exact (next_spec j).1.2.1 ((seen_iff j _).mpr ⟨i, by omega, he⟩)

private theorem a_injective : Function.Injective a := by
  intro i j he
  rcases lt_trichotomy i j with hij | hij | hji
  · exact (a_ne_of_lt hij he).elim
  · exact hij
  · exact (a_ne_of_lt hji he.symm).elim

private theorem no_bounded_injection (f : ℕ → ℕ) (hf : Function.Injective f) (b : ℕ)
    (hb : ∀ n, f n ≤ b) : False := by
  apply Set.infinite_range_of_injective hf
  apply (Set.finite_Iic b).subset
  rintro _ ⟨n, rfl⟩
  exact hb n

private theorem hits_square (t : ℕ) (ht : 0 < t) : ∃ n, a n = t ^ 2 := by
  by_contra! h
  apply no_bounded_injection a a_injective (t ^ 2)
  intro n
  cases n with
  | zero =>
    change 1 ≤ t ^ 2
    exact Nat.succ_le_of_lt (pow_pos ht _)
  | succ n =>
    apply (next_spec n).2.2
    refine ⟨by positivity, ?_, by simp [periodicCoeffs_square]⟩
    intro hm
    obtain ⟨i, _, hi⟩ := (seen_iff n _).mp hm
    exact h i hi

private theorem hits_positive (m : ℕ) (hm : 0 < m) : ∃ n, a n = m := by
  classical
  by_contra! h
  choose idx hidx using fun t : ℕ => hits_square (t + 1) (by omega)
  have hs : StrictMono (fun t : ℕ => (t + 1) ^ 2) :=
    fun _ _ hlt => Nat.pow_lt_pow_left (by omega) (by decide)
  have hf : Function.Injective idx := by
    intro i j he
    apply hs.injective
    change (i + 1) ^ 2 = (j + 1) ^ 2
    rw [← hidx i, ← hidx j, he]
  refine no_bounded_injection (fun t => a (idx t + 1)) ?_ m ?_
  · intro i j he
    exact hf (Nat.add_right_cancel (a_injective he))
  · intro t
    apply (next_spec (idx t)).2.2
    refine ⟨hm, ?_, by rw [hidx, periodicCoeffs_square]; simp⟩
    intro hseen
    obtain ⟨i, _, hi⟩ := (seen_iff (idx t) _).mp hseen
    exact h i hi

end OMA.S_oeis_a351652

open OMA.S_oeis_a351652 in
theorem OMA.solution : type_of% @OMA.S_oeis_a351652.main := by
  refine ⟨a_injective, fun m => ⟨hits_positive m, ?_⟩⟩
  rintro ⟨n, rfl⟩
  exact a_pos n
