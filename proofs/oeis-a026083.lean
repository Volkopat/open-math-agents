import OMAStatements.S_oeis_a026083

/-! Proof: `a (m+3) = 2 T(m,3) + 6 T(m,1)` with `T` the trinomial coefficients
(walk-count DP via `Fin.snoc`); the recurrence is `2 R(5) + 6 R(3) + 4 R(1)` for the
k-relation `(k-1-m) T(m,k-1) + k T(m,k) + (k+1+m) T(m,k+1) = 0`. -/

namespace OMA.S_oeis_a026083

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

lemma T_far : ∀ (m : ℕ) (k : ℤ), (m:ℤ) < |k| → T m k = 0
  | 0, k, h => by
    simp only [T]; rw [if_neg]; intro hk; simp [hk] at h
  | m+1, k, h => by
    simp only [T]
    rw [T_far m (k-1) (by rw [lt_abs] at h ⊢; push_cast at h; omega),
      T_far m k (by rw [lt_abs] at h ⊢; push_cast at h; omega),
      T_far m (k+1) (by rw [lt_abs] at h ⊢; push_cast at h; omega)]
    simp

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

lemma key (M : ℕ) :
    ((M:ℤ)+6) * (2 * T (M+3) 3 + 6 * T (M+3) 1) + (-3*((M:ℤ)+6)+5) * (2 * T (M+2) 3 + 6 * T (M+2) 1)
    + (-((M:ℤ)+6)-6) * (2 * T (M+1) 3 + 6 * T (M+1) 1)
    + 3*((M:ℤ)+6-5) * (2 * T M 3 + 6 * T M 1) = 0 := by
  have h3 : ∀ k, T (M+3) k = T (M+2) (k-1) + T (M+2) k + T (M+2) (k+1) := fun k => rfl
  have h2 : ∀ k, T (M+2) k = T (M+1) (k-1) + T (M+1) k + T (M+1) (k+1) := fun k => rfl
  have h1 : ∀ k, T (M+1) k = T M (k-1) + T M k + T M (k+1) := fun k => rfl
  simp only [h3, h2, h1]
  norm_num
  have s1 := T_symm M 1
  have s2 := T_symm M 2
  have r1 := R M 1
  have r3 := R M 3
  have r5 := R M 5
  norm_num at s1 s2 r1 r3 r5
  rw [s1, s2]
  linear_combination 2 * r5 + 6 * r3 + 4 * r1

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

lemma a_eq (m : ℕ) : (a (m+3) : ℤ) = 2 * T m 3 + 6 * T m 1 := by
  have h : a (m+3) = (W (m+3) (· = 0)).ncard := rfl
  rw [h, (W_count _ _).2, D_T]
  norm_num
  rw [T_symm m 3, T_symm m 1]
  ring

theorem solution_main :
    ∀ n : ℕ, 7 ≤ n →
      (n : ℤ) * a n + (-3 * n + 5) * a (n - 1) + (-(n : ℤ) - 6) * a (n - 2) +
        3 * ((n : ℤ) - 5) * a (n - 3) = 0 := by
  intro n hn
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 6 := ⟨n - 6, by omega⟩
  rw [show M + 6 - 1 = M + 2 + 3 by omega, show M + 6 - 2 = M + 1 + 3 by omega,
    show M + 6 - 3 = M + 3 by omega, show M + 6 = M + 3 + 3 by omega,
    a_eq, a_eq, a_eq, a_eq]
  push_cast
  linear_combination key M

end OMA.S_oeis_a026083

theorem OMA.solution : type_of% @OMA.S_oeis_a026083.main := OMA.S_oeis_a026083.solution_main
