import OMAStatements.S_oeis_a290198

namespace OMA.S_oeis_a290198

open PowerSeries



/-- The pattern: stages 0 to 3 explicitly, and from stage 4 on every cell but the origin is ON. -/
def P : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | 1, x, y => decide (2 ≤ x.natAbs + y.natAbs)
  | 2, x, y => !decide (x.natAbs = 1 ∧ y.natAbs = 1)
  | 3, x, y => !decide (x.natAbs ≤ 1 ∧ y.natAbs ≤ 1 ∧ ¬(x = 0 ∧ y = 0))
  | _ + 4, x, y => !decide (x = 0 ∧ y = 0)

theorem P_four (m : ℕ) (x y : ℤ) : P (m + 4) x y = !decide (x = 0 ∧ y = 0) := rfl

/-- Away from the origin every stage t >= 1 is ON. -/
theorem P_far (t : ℕ) (ht : 0 < t) (u v : ℤ) (h : 3 ≤ u.natAbs + v.natAbs) : P t u v = true := by
  rcases (by omega : t = 1 ∨ t = 2 ∨ t = 3 ∨ 4 ≤ t) with rfl | rfl | rfl | h4
  · exact decide_eq_true (by omega)
  · show (!decide (u.natAbs = 1 ∧ v.natAbs = 1)) = true
    rw [decide_eq_false (by omega)]; rfl
  · show (!decide (u.natAbs ≤ 1 ∧ v.natAbs ≤ 1 ∧ ¬(u = 0 ∧ v = 0))) = true
    rw [decide_eq_false (by omega)]; rfl
  · obtain ⟨m, rfl⟩ : ∃ m, t = m + 4 := ⟨t - 4, by omega⟩
    show (!decide (u = 0 ∧ v = 0)) = true
    rw [decide_eq_false (by omega)]; rfl

/-- One step of Rule 721 maps the pattern at stage t to the pattern at stage t + 1. -/
theorem step (t : ℕ) (x y : ℤ) :
    Nat.testBit 721 ((P t x y).toNat + 2 * ((P t (x - 1) y).toNat + (P t (x + 1) y).toNat +
      (P t x (y - 1)).toNat + (P t x (y + 1)).toNat)) = P (t + 1) x y := by
  rcases (by omega : x.natAbs + y.natAbs ≤ 3 ∨ 4 ≤ x.natAbs + y.natAbs) with h | h
  · have hx1 : -3 ≤ x := by omega
    have hx2 : x ≤ 3 := by omega
    have hy1 : -3 ≤ y := by omega
    have hy2 : y ≤ 3 := by omega
    rcases (by omega : t < 4 ∨ 4 ≤ t) with ht | ht
    · interval_cases t <;> interval_cases x <;> interval_cases y <;> rfl
    · obtain ⟨m, rfl⟩ : ∃ m, t = m + 4 := ⟨t - 4, by omega⟩
      rw [show m + 4 + 1 = m + 1 + 4 by ring]
      simp only [P_four]
      interval_cases x <;> interval_cases y <;> rfl
  · rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht
      have e : ∀ u v : ℤ, 3 ≤ u.natAbs + v.natAbs → P 0 u v = false := fun u v huv =>
        decide_eq_false (by omega)
      rw [e x y (by omega), e (x - 1) y (by omega), e (x + 1) y (by omega),
        e x (y - 1) (by omega), e x (y + 1) (by omega),
        P_far 1 (by omega) x y (by omega)]
      rfl
    · rw [P_far t ht x y (by omega), P_far t ht (x - 1) y (by omega),
        P_far t ht (x + 1) y (by omega), P_far t ht x (y - 1) (by omega),
        P_far t ht x (y + 1) (by omega), P_far (t + 1) (by omega) x y (by omega)]
      rfl

/-- Stage t is the pattern `P t`. -/
theorem state_eq (t : ℕ) : ∀ x y, state t x y = P t x y := by
  induction t with
  | zero => intro x y; rfl
  | succ t ih =>
    intro x y
    show Nat.testBit 721 _ = _
    rw [ih, ih, ih, ih, ih]
    exact step t x y

/-- From stage 4 on, a diagonal cell (k, k) is ON exactly when k is not 0. -/
theorem diag (n k : ℕ) (hn : 4 ≤ n) : state n (k : ℤ) (k : ℤ) = decide (k ≠ 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [state_eq]
  show (!decide ((k : ℤ) = 0 ∧ (k : ℤ) = 0)) = decide (k ≠ 0)
  by_cases hk : k = 0
  · subst hk; rfl
  · rw [decide_eq_false (by omega), decide_eq_true hk]; rfl
theorem a_eq (n : ℕ) (hn : 4 ≤ n) : a n = ∑ k ∈ Finset.range n, 2 ^ (k + 1) := by
  have e : ∀ k ∈ Finset.range n, (if state n ((k + 1 : ℕ) : ℤ) ((k + 1 : ℕ) : ℤ) then
      2 ^ (k + 1) else 0) = 2 ^ (k + 1) := fun k _ => by
    rw [diag n (k + 1) hn, decide_eq_true (by omega : k + 1 ≠ 0), if_pos rfl]
  unfold a
  rw [Finset.sum_range_succ', Finset.sum_congr rfl e, diag n 0 hn]
  simp

/-- Controls: the entry's terms a(0..15). -/
theorem controls : (List.range 16).map a =
    [1, 2, 5, 13, 30, 62, 126, 254, 510, 1022, 2046, 4094, 8190, 16382, 32766, 65534] := by
  rw [show a = fun n => ∑ k ∈ Finset.range (n + 1), if P n (k : ℤ) (k : ℤ) then 2 ^ k else 0
    from funext (fun n => by simp only [a, state_eq])]
  decide

theorem geom (n : ℕ) : ∑ k ∈ Finset.range n, (2 : ℤ) ^ (k + 1) = 2 ^ (n + 1) - 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

/-- Corneth's conjecture, both parts. -/
theorem conjecture :
    (∀ n : ℕ, n ≤ 3 → a n = Nat.fib (2 * n + 1)) ∧
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 2 ^ (n + 1) - 2) := by
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · have c := controls
    simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, List.cons.injEq] at c
    obtain ⟨v0, v1, v2, v3, -⟩ := c
    interval_cases n
    · rw [v0]; rfl
    · rw [v1]; rfl
    · rw [v2]; rfl
    · rw [v3]; rfl
  · rw [a_eq n hn, ← geom]
    push_cast
    rfl

end OMA.S_oeis_a290198

theorem OMA.solution : type_of% @OMA.S_oeis_a290198.main :=
  OMA.S_oeis_a290198.conjecture
