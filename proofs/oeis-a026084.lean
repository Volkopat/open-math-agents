import OMAStatements.S_oeis_a026084

/-!
# Mathar's recurrence for walks ending at one

The trinomial coefficient identities and the walk-counting lemmas using `Fin.snoc`
are adapted from @mbilenko03's proof for A026083 in
https://github.com/lefttosolve2/open-math-agents/pull/13751 .
For endpoint one the count is `T m 4 + 4 * T m 2 + 3 * T m 0`.
Its recurrence follows from the coefficient relations at 6, 4 and 2.
-/

namespace OMA.S_oeis_a026084

def T : ℕ → ℤ → ℤ
  | 0, k => if k = 0 then 1 else 0
  | m+1, k => T m (k-1) + T m k + T m (k+1)

lemma T_symm : ∀ m k, T m (-k) = T m k
  | 0, k => by simp [T]
  | m+1, k => by
    simp only [T]
    rw [show -k - 1 = -(k+1) by ring, show -k + 1 = -(k-1) by ring, T_symm m (k+1),
      T_symm m k, T_symm m (k-1)]
    ring

lemma R : ∀ m (k : ℤ), (k-1-m) * T m (k-1) + k * T m k + (k+1+m) * T m (k+1) = 0
  | 0, k => by
    simp only [T, Nat.cast_zero, sub_zero, add_zero]
    have h1 : (k-1) * (if k - 1 = 0 then (1:ℤ) else 0) = 0 := by split_ifs with h <;> simp [h]
    have h2 : k * (if k = 0 then (1:ℤ) else 0) = 0 := by split_ifs with h <;> simp [h]
    have h3 : (k+1) * (if k + 1 = 0 then (1:ℤ) else 0) = 0 := by split_ifs with h <;> simp [h]
    linear_combination h1 + h2 + h3
  | m+1, k => by
    have h1 := R m (k-1)
    have h2 := R m k
    have h3 := R m (k+1)
    simp only [T]
    rw [show k - 1 - 1 = k - 2 by ring, show k - 1 + 1 = k by ring,
      show k + 1 - 1 = k by ring, show k + 1 + 1 = k + 2 by ring] at *
    push_cast
    linear_combination h1 + h2 + h3

lemma endpoint_recurrence (m : ℕ) :
    let b := fun k => T k 4 + 4 * T k 2 + 3 * T k 0
    ((m : ℤ) + 7) * b (m+3) - 3 * (m+5 : ℤ) * b (m+2) -
      (m+15 : ℤ) * b (m+1) + 3 * (m+1 : ℤ) * b m = 0 := by
  have step : ∀ (i : ℕ) (k : ℤ), T (i+1) k = T i (k-1) + T i k + T i (k+1) :=
    fun _ _ => rfl
  dsimp only
  simp only [step (m+2), step (m+1), step m]
  norm_num
  have r2 := R m 2
  have r4 := R m 4
  have r6 := R m 6
  norm_num at r2 r4 r6
  rw [T_symm m 1, T_symm m 2, T_symm m 3]
  linear_combination r6 + 4 * r4 + 5 * r2

def W (n : ℕ) (P : ℤ → Prop) : Set (Fin (n+1) → ℤ) :=
  {s | s 0 = 0 ∧ P (s (Fin.last _)) ∧ ∀ i : Fin n,
    (i.val < 3 → |s i.succ - s i.castSucc| = 1) ∧ (3 ≤ i.val → |s i.succ - s i.castSucc| ≤ 1)}

lemma step_iff (n : ℕ) (d : ℤ) :
    ((n < 3 → |d| = 1) ∧ (3 ≤ n → |d| ≤ 1)) ↔ (d = 1 ∨ d = -1 ∨ (3 ≤ n ∧ d = 0)) := by
  rw [abs_eq (by norm_num), abs_le]; omega

lemma W_succ (n : ℕ) (y : ℤ) :
    W (n+1) (· = y) = (fun t : Fin (n+1) → ℤ => (Fin.snoc t y : Fin (n+2) → ℤ)) ''
      W n (fun v => y - v = 1 ∨ y - v = -1 ∨ (3 ≤ n ∧ y - v = 0)) := by
  ext s
  simp only [W, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨h0, hl, hs⟩
    refine ⟨Fin.init s, ⟨?_, ?_, ?_⟩, ?_⟩
    · simpa [Fin.init] using h0
    · have := hs (Fin.last n)
      simp only [Fin.succ_last, hl, Fin.val_last] at this
      rw [step_iff] at this
      exact this
    · intro i
      have := hs i.castSucc
      rw [Fin.succ_castSucc, Fin.val_castSucc] at this
      exact this
    · rw [← hl]; exact Fin.snoc_init_self s
  · rintro ⟨t, ⟨h0, hl, hs⟩, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · have : (0 : Fin (n+2)) = Fin.castSucc (0 : Fin (n+1)) := rfl
      rw [this, Fin.snoc_castSucc]; exact h0
    · simp
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc, Fin.val_last]
        rw [step_iff]; exact hl
      · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.val_castSucc]
        exact hs j

lemma W_zero (y : ℤ) : W 0 (· = y) = if y = 0 then {fun _ => 0} else ∅ := by
  ext s
  split_ifs with h
  · subst h
    simp only [W, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h0, -, -⟩; funext i; fin_cases i; exact h0
    · rintro rfl; exact ⟨rfl, rfl, fun i => i.elim0⟩
  · simp only [W, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h0, hl, -⟩
    have : s (Fin.last 0) = s 0 := rfl
    omega

def D : ℕ → ℤ → ℕ
  | 0, y => if y = 0 then 1 else 0
  | n+1, y => D n (y-1) + D n (y+1) + (if 3 ≤ n then D n y else 0)

lemma W_count : ∀ n y, (W n (· = y)).Finite ∧ (W n (· = y)).ncard = D n y
  | 0, y => by rw [W_zero]; split_ifs with h <;> simp [D, h]
  | n+1, y => by
    have inj : Function.Injective (fun t : Fin (n+1) → ℤ => (Fin.snoc t y : Fin (n+2) → ℤ)) := by
      intro a b h
      have := congrArg Fin.init h
      simpa using this
    obtain ⟨f1, c1⟩ := W_count n (y-1)
    obtain ⟨f2, c2⟩ := W_count n (y+1)
    obtain ⟨f3, c3⟩ := W_count n y
    have d12 : Disjoint (W n (· = y-1)) (W n (· = y+1)) := by
      rw [Set.disjoint_left]; rintro s ⟨-, a, -⟩ ⟨-, b, -⟩; omega
    rw [W_succ, Set.ncard_image_of_injective _ inj]
    by_cases h : 3 ≤ n
    · have e : W n (fun v => y - v = 1 ∨ y - v = -1 ∨ (3 ≤ n ∧ y - v = 0)) =
          (W n (· = y-1) ∪ W n (· = y+1)) ∪ W n (· = y) := by
        ext s; simp only [W, Set.mem_ofPred_eq, Set.mem_union]
        constructor
        · rintro ⟨a, b, c⟩
          rcases b with b | b | b
          · exact Or.inl (Or.inl ⟨a, by omega, c⟩)
          · exact Or.inl (Or.inr ⟨a, by omega, c⟩)
          · exact Or.inr ⟨a, by omega, c⟩
        · rintro ((⟨a, b, c⟩ | ⟨a, b, c⟩) | ⟨a, b, c⟩)
          · exact ⟨a, by omega, c⟩
          · exact ⟨a, by omega, c⟩
          · exact ⟨a, by omega, c⟩
      have d3 : Disjoint (W n (· = y-1) ∪ W n (· = y+1)) (W n (· = y)) := by
        rw [Set.disjoint_left]; rintro s (⟨-, a, -⟩ | ⟨-, a, -⟩) ⟨-, b, -⟩ <;> omega
      rw [e]
      refine ⟨((f1.union f2).union f3).image _, ?_⟩
      rw [Set.ncard_union_eq d3 (f1.union f2) f3, Set.ncard_union_eq d12 f1 f2, c1, c2, c3]
      simp [D, h]
    · have e : W n (fun v => y - v = 1 ∨ y - v = -1 ∨ (3 ≤ n ∧ y - v = 0)) =
          W n (· = y-1) ∪ W n (· = y+1) := by
        ext s; simp only [W, Set.mem_ofPred_eq, Set.mem_union]
        constructor
        · rintro ⟨a, b, c⟩
          rcases b with b | b | b
          · exact Or.inl ⟨a, by omega, c⟩
          · exact Or.inr ⟨a, by omega, c⟩
          · exact absurd b.1 h
        · rintro (⟨a, b, c⟩ | ⟨a, b, c⟩)
          · exact ⟨a, by omega, c⟩
          · exact ⟨a, by omega, c⟩
      rw [e]
      refine ⟨(f1.union f2).image _, ?_⟩
      rw [Set.ncard_union_eq d12 f1 f2, c1, c2]
      simp [D, h]

lemma D_far : ∀ (n : ℕ) (y : ℤ), (n:ℤ) < |y| → D n y = 0
  | 0, y, h => by
    simp only [D]; rw [if_neg]; intro hy; simp [hy] at h
  | n+1, y, h => by
    simp only [D]
    rw [D_far n (y-1) (by rw [lt_abs] at h ⊢; push_cast at h; omega),
      D_far n (y+1) (by rw [lt_abs] at h ⊢; push_cast at h; omega),
      D_far n y (by rw [lt_abs] at h ⊢; push_cast at h; omega)]
    simp

lemma D_T : ∀ (m : ℕ) (y : ℤ),
    (D (m+3) y : ℤ) = T m (y-3) + 3 * T m (y-1) + 3 * T m (y+1) + T m (y+3)
  | 0, y => by
    by_cases hy : -3 ≤ y ∧ y ≤ 3
    · obtain ⟨h1, h2⟩ := hy
      interval_cases y <;> decide
    · rw [D_far 3 y (by rw [lt_abs]; push_cast; omega)]
      simp only [T]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp
  | m+1, y => by
    have e : D (m+1+3) y = D (m+3) (y-1) + D (m+3) (y+1) + D (m+3) y := by
      have : D (m+3+1) y = D (m+3) (y-1) + D (m+3) (y+1) +
          (if 3 ≤ m+3 then D (m+3) y else 0) := rfl
      rw [this, if_pos (by omega)]
    rw [e]; push_cast
    rw [D_T m (y-1), D_T m (y+1), D_T m y]
    simp only [T]
    ring_nf

lemma walks_eq (n : ℕ) : walks n = W n (· = 1) := by
  ext s
  simp only [walks, W, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h0, he, hstrict, hweak⟩
    refine ⟨h0 0 rfl, he (Fin.last n) rfl, ?_⟩
    intro i
    constructor
    · intro h
      exact hstrict i.castSucc i.succ rfl (by change i.val + 1 ≤ 3; omega)
    · intro h
      exact hweak i.castSucc i.succ rfl (by change 3 < i.val + 1; omega)
  · rintro ⟨h0, he, hs⟩
    constructor
    · intro i h
      have hi : i = 0 := Fin.ext h
      rw [hi]
      exact h0
    constructor
    · intro i h
      have hi : i = Fin.last n := Fin.ext h
      rw [hi]
      exact he
    have adj (i j : Fin (n+1)) (h : j.val = i.val+1) :
        (j.val ≤ 3 → |s j - s i| = 1) ∧ (3 < j.val → |s j - s i| ≤ 1) := by
      have hi : i.val < n := by have := j.isLt; omega
      let k : Fin n := ⟨i.val, hi⟩
      have hil : k.castSucc = i := Fin.ext rfl
      have hju : k.succ = j := Fin.ext h.symm
      have hk := hs k
      rw [hil, hju] at hk
      constructor
      · intro small
        apply hk.1
        change i.val < 3
        omega
      · intro large
        apply hk.2
        change 3 ≤ i.val
        omega
    exact ⟨fun i j h => (adj i j h).1, fun i j h => (adj i j h).2⟩

lemma a_eq (m : ℕ) : a (m+3) = T m 4 + 4 * T m 2 + 3 * T m 0 := by
  unfold a
  rw [walks_eq, (W_count _ _).2, D_T]
  norm_num
  rw [T_symm m 2]
  ring

theorem solution_main : type_of% @main := by
  intro n hn
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 6 := ⟨n - 6, by omega⟩
  rw [show M + 6 - 1 = M + 2 + 3 by omega, show M + 6 - 2 = M + 1 + 3 by omega,
    show M + 6 - 3 = M + 3 by omega, show M + 6 = M + 3 + 3 by omega,
    a_eq, a_eq, a_eq, a_eq]
  push_cast
  have hk := endpoint_recurrence M
  dsimp only at hk
  linear_combination hk

end OMA.S_oeis_a026084

theorem OMA.solution : type_of% @OMA.S_oeis_a026084.main := OMA.S_oeis_a026084.solution_main
