import OMAStatements.S_oeis_a026086

/-! After the three compulsory moves, the displacements have multiplicities
1, 3, 3, 1. The remaining moves are counted by trinomial coefficients.
The walk-counting and trinomial lemmas are adapted from mbilenko03's
A026083 proof in this repository. -/

namespace OMA.S_oeis_a026086

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

/-- Rewrite the index conditions in the statement using consecutive indices. -/
lemma walks_eq (n : ℕ) : walks n = W n (· = 3) := by
  ext s
  constructor
  · rintro ⟨start, finish, first, rest⟩
    refine ⟨start 0 rfl, finish (Fin.last n) rfl, fun i => ?_⟩
    exact ⟨fun hi => first i.castSucc i.succ rfl (by change i.val + 1 ≤ 3; omega),
      fun hi => rest i.castSucc i.succ rfl (by change 3 < i.val + 1; omega)⟩
  · rintro ⟨start, finish, step⟩
    have adjacent (i j : Fin (n + 1)) (hij : j.val = i.val + 1) :
        (j.val ≤ 3 → |s j - s i| = 1) ∧ (3 < j.val → |s j - s i| ≤ 1) := by
      let t : Fin n := ⟨i.val, by have := j.isLt; omega⟩
      have hi : t.castSucc = i := Fin.ext rfl
      have hj : t.succ = j := Fin.ext hij.symm
      obtain ⟨hfirst, hrest⟩ := step t
      rw [hi, hj] at hfirst hrest
      exact ⟨fun h => hfirst (by change i.val < 3; omega),
        fun h => hrest (by change 3 ≤ i.val; omega)⟩
    refine ⟨?_, ?_, fun i j h => (adjacent i j h).1, fun i j h => (adjacent i j h).2⟩
    · intro i hi
      simpa only [show i = 0 from Fin.ext hi] using start
    · intro i hi
      simpa only [show i = Fin.last n from Fin.ext hi] using finish

/-- Weight the four possible displacements at time three for a walk ending at 3. -/
def endpointCount (m : ℕ) : ℤ := T m 0 + 3 * T m 2 + 3 * T m 4 + T m 6

lemma count_eq (m : ℕ) : a (m + 3) = endpointCount m := by
  rw [a, walks_eq, (W_count _ _).2, D_T]
  norm_num [endpointCount]

set_option maxHeartbeats 4000000 in
/-- The residual of the time recurrence is the sum of the spatial identities
at displacements 2, 8, and 10, with respective weights 3, 2, and 1. -/
lemma endpoint_recurrence (m : ℕ) :
    ((m : ℤ) + 11) * endpointCount (m + 5) - (5 * (m : ℤ) + 45) * endpointCount (m + 4) +
      (3 * (m : ℤ) + 9) * endpointCount (m + 3) + (11 * (m : ℤ) + 79) * endpointCount (m + 2) +
      (12 - 4 * (m : ℤ)) * endpointCount (m + 1) - (6 * (m : ℤ) + 6) * endpointCount m = 0 := by
  have step (j : ℕ) (k : ℤ) :
      T (m + j + 1) k = T (m + j) (k - 1) + T (m + j) k + T (m + j) (k + 1) := rfl
  have h₂ := R m 2
  have h₈ := R m 8
  have h₁₀ := R m 10
  norm_num at h₂ h₈ h₁₀
  simp only [endpointCount, step 4, step 3, step 2, step 1, step 0, Nat.add_zero]
  norm_num
  simp only [T_symm]
  linear_combination 3 * h₂ + 2 * h₈ + h₁₀

end OMA.S_oeis_a026086

open OMA.S_oeis_a026086 in
theorem OMA.solution : type_of% @OMA.S_oeis_a026086.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  have h₀ : a (m + 8) = endpointCount (m + 5) := count_eq _
  have h₁ : a (m + 8 - 1) = endpointCount (m + 4) := count_eq _
  have h₂ : a (m + 8 - 2) = endpointCount (m + 3) := count_eq _
  have h₃ : a (m + 8 - 3) = endpointCount (m + 2) := count_eq _
  have h₄ : a (m + 8 - 4) = endpointCount (m + 1) := count_eq _
  have h₅ : a (m + 8 - 5) = endpointCount m := count_eq _
  rw [h₀, h₁, h₂, h₃, h₄, h₅]
  push_cast
  linear_combination endpoint_recurrence m
