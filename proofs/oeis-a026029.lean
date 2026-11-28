import OMAStatements.S_oeis_a026029

/-! Proof via the reflection principle: walk counts satisfy a Pascal-type
DP, which equals `C(L,k) - C(L,k+4)`; so `a n = C(2n,n) - C(2n,n+4)`. -/

namespace OMA.S_oeis_a026029

def W (L : ℕ) (P : ℕ → Prop) : Set (Fin (L+1) → ℕ) :=
  {s | s 0 = 3 ∧ P (s (Fin.last _)) ∧ ∀ i : Fin L,
    (s i.succ : ℤ) - s i.castSucc = 1 ∨ (s i.succ : ℤ) - s i.castSucc = -1}

lemma W_succ (L y : ℕ) :
    W (L+1) (· = y) = (fun t : Fin (L+1) → ℕ => (Fin.snoc t y : Fin (L+2) → ℕ)) ''
      W L (fun v => v = y + 1 ∨ v + 1 = y) := by
  ext s
  simp only [W, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨h0, hl, hs⟩
    refine ⟨Fin.init s, ⟨?_, ?_, ?_⟩, ?_⟩
    · simpa [Fin.init] using h0
    · have := hs (Fin.last L)
      simp only [Fin.succ_last, hl] at this
      simp only [Fin.init]
      omega
    · intro i
      have := hs i.castSucc
      rw [Fin.succ_castSucc] at this
      exact this
    · rw [← hl]; exact Fin.snoc_init_self s
  · rintro ⟨t, ⟨h0, hl, hs⟩, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · have : (0 : Fin (L+2)) = Fin.castSucc (0 : Fin (L+1)) := rfl
      rw [this, Fin.snoc_castSucc]; exact h0
    · simp
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]
        omega
      · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact hs j

lemma W_zero (y : ℕ) : W 0 (· = y) = if y = 3 then {fun _ => 3} else ∅ := by
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

def N : ℕ → ℕ → ℕ
  | 0, y => if y = 3 then 1 else 0
  | L+1, y => N L (y+1) + (if y = 0 then 0 else N L (y-1))

lemma W_count : ∀ L y, (W L (· = y)).Finite ∧ (W L (· = y)).ncard = N L y
  | 0, y => by rw [W_zero]; split_ifs with h <;> simp [N, h]
  | L+1, y => by
    have e : W L (fun v => v = y + 1 ∨ v + 1 = y) =
        W L (· = y+1) ∪ (if y = 0 then ∅ else W L (· = y-1)) := by
      ext s
      by_cases h : y = 0
      · simp only [h, if_true, Set.union_empty]
        simp only [W, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨a, b, c⟩; exact ⟨a, by omega, c⟩
        · rintro ⟨a, b, c⟩; exact ⟨a, by omega, c⟩
      · simp only [h, if_false]
        simp only [W, Set.mem_ofPred_eq, Set.mem_union]
        constructor
        · rintro ⟨a, b, c⟩
          rcases b with b | b
          · exact Or.inl ⟨a, b, c⟩
          · exact Or.inr ⟨a, by omega, c⟩
        · rintro (⟨a, b, c⟩ | ⟨a, b, c⟩)
          · exact ⟨a, Or.inl b, c⟩
          · exact ⟨a, Or.inr (by omega), c⟩
    have inj : Function.Injective (fun t : Fin (L+1) → ℕ => (Fin.snoc t y : Fin (L+2) → ℕ)) := by
      intro a b h
      have := congrArg Fin.init h
      simpa using this
    obtain ⟨f1, c1⟩ := W_count L (y+1)
    rw [W_succ, e, Set.ncard_image_of_injective _ inj]
    by_cases h : y = 0
    · simp only [h, if_true, Set.union_empty, N, zero_add, add_zero] at c1 f1 ⊢
      exact ⟨f1.image _, c1⟩
    · obtain ⟨f2, c2⟩ := W_count L (y-1)
      simp only [h, if_false, N]
      refine ⟨(f1.union f2).image _, ?_⟩
      rw [Set.ncard_union_eq _ f1 f2, c1, c2]
      rw [Set.disjoint_left]
      rintro s ⟨-, a, -⟩ ⟨-, b, -⟩
      omega


def cz (L : ℕ) (k : ℤ) : ℤ := if 0 ≤ k then (L.choose k.toNat : ℤ) else 0

lemma cz_neg (L : ℕ) (k : ℤ) (h : k < 0) : cz L k = 0 := by simp [cz]; omega

lemma cz_big (L : ℕ) (k : ℤ) (h : (L:ℤ) < k) : cz L k = 0 := by
  unfold cz
  rw [if_pos (by omega), Nat.choose_eq_zero_of_lt (by omega)]; simp

lemma cz_pascal (L : ℕ) (k : ℤ) : cz (L+1) k = cz L k + cz L (k-1) := by
  rcases lt_trichotomy k 0 with h | h | h
  · rw [cz_neg _ _ h, cz_neg _ _ h, cz_neg _ _ (by omega)]; simp
  · subst h; simp [cz]
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = (m:ℤ) + 1 := ⟨(k-1).toNat, by omega⟩
    unfold cz
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    rw [show ((m:ℤ)+1).toNat = m+1 by omega, show ((m:ℤ)+1-1).toNat = m by omega,
      Nat.choose_succ_succ']
    push_cast; ring

lemma cz_symm (L : ℕ) (k : ℤ) : cz L k = cz L (L - k) := by
  rcases lt_or_ge k 0 with h | h
  · rw [cz_neg _ _ h, cz_big _ _ (by omega)]
  rcases lt_or_ge (L:ℤ) k with h' | h'
  · rw [cz_big _ _ h', cz_neg _ _ (by omega)]
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = (m:ℤ) := ⟨k.toNat, by omega⟩
  unfold cz
  rw [if_pos (by omega), if_pos (by omega), show ((m:ℤ)).toNat = m by omega,
    show ((L:ℤ) - m).toNat = L - m by omega, Nat.choose_symm (by omega)]

lemma N_closed : ∀ L : ℕ, ∀ k : ℤ, 0 ≤ 3 + 2*k - L →
    (N L (3 + 2*k - L).toNat : ℤ) = cz L k - cz L (k+4)
  | 0, k, hk => by
    simp only [N, Nat.cast_zero, sub_zero]
    by_cases h0 : k = 0
    · subst h0; simp [cz]
    · rw [if_neg (by omega)]
      rcases lt_or_ge k 0 with h | h
      · rw [cz_neg _ _ h, cz_big _ _ (by push_cast; omega)]; simp
      · rw [cz_big _ _ (by push_cast; omega), cz_big _ _ (by push_cast; omega)]; simp
  | L+1, k, hk => by
    simp only [N]
    rw [cz_pascal, cz_pascal]
    have e1 : (3 + 2*k - ((L+1:ℕ):ℤ)).toNat + 1 = (3 + 2*k - L).toNat := by push_cast; omega
    rw [e1]
    push_cast
    rw [N_closed L k (by push_cast at hk; omega)]
    split_ifs with h
    · have hL : (L:ℤ) = 2*k + 2 := by push_cast at h; omega
      have := cz_symm L (k-1)
      rw [show (L:ℤ) - (k-1) = k + 4 - 1 by omega] at this
      rw [this]; ring
    · have e2 : (3 + 2*k - ((L:ℤ)+1)).toNat - 1 = (3 + 2*(k-1) - L).toNat := by omega
      rw [e2, N_closed L (k-1) (by push_cast at hk; omega)]
      rw [show k - 1 + 4 = k + 4 - 1 by ring]; ring
lemma alg (j : ℕ) : ((j:ℚ)+10) * ((Nat.choose (2*j+12) (j+6) : ℚ) - Nat.choose (2*j+12) (j+10))
   - 6*((j:ℚ)+8) * ((Nat.choose (2*j+10) (j+5) : ℚ) - Nat.choose (2*j+10) (j+9))
   + 4*(2*(j:ℚ)+11) * ((Nat.choose (2*j+8) (j+4) : ℚ) - Nat.choose (2*j+8) (j+8)) = 0 := by
  have h1 := Nat.cast_add_choose ℚ (a := j+6) (b := j+6)
  have h2 := Nat.cast_add_choose ℚ (a := j+10) (b := j+2)
  have h3 := Nat.cast_add_choose ℚ (a := j+5) (b := j+5)
  have h4 := Nat.cast_add_choose ℚ (a := j+9) (b := j+1)
  have h5 := Nat.cast_add_choose ℚ (a := j+4) (b := j+4)
  have h6 := Nat.cast_add_choose ℚ (a := j+8) (b := j)
  rw [show j+6+(j+6) = 2*j+12 by ring] at h1
  rw [show j+10+(j+2) = 2*j+12 by ring] at h2
  rw [show j+5+(j+5) = 2*j+10 by ring] at h3
  rw [show j+9+(j+1) = 2*j+10 by ring] at h4
  rw [show j+4+(j+4) = 2*j+8 by ring] at h5
  rw [show j+8+j = 2*j+8 by ring] at h6
  rw [h1, h2, h3, h4, h5, h6]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
    show 2*j+12 = (2*j+11)+1 from rfl, show 2*j+11 = (2*j+10)+1 from rfl,
    show 2*j+10 = (2*j+9)+1 from rfl, show 2*j+9 = (2*j+8)+1 from rfl]
  have hf : ((2*j+8).factorial : ℚ) ≠ 0 := by positivity
  have hg : ((j).factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring

lemma a_eq (n : ℕ) : (a n : ℤ) = (Nat.choose (2*n) n : ℤ) - Nat.choose (2*n) (n+4) := by
  have h : a n = (W (2*n) (· = 3)).ncard := rfl
  rw [h, (W_count _ _).2]
  have := N_closed (2*n) n (by push_cast; omega)
  rw [show (3 + 2*(n:ℤ) - ((2*n:ℕ):ℤ)).toNat = 3 by push_cast; omega] at this
  rw [this]
  unfold cz
  rw [if_pos (by omega), if_pos (by omega), show ((n:ℤ)).toNat = n by omega,
    show ((n:ℤ)+4).toNat = n+4 by omega]

theorem solution_main :
    ∀ n : ℕ, 2 ≤ n →
      ((n : ℤ) + 4) * a n + 6 * (-(n : ℤ) - 2) * a (n - 1) + 4 * (2 * n - 1) * a (n - 2) = 0 := by
  intro n hn
  by_cases h6 : n < 6
  · interval_cases n <;> rw [a_eq, a_eq, a_eq] <;> decide
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 6 := ⟨n - 6, by omega⟩
    rw [show j+6-1 = j+5 by omega, show j+6-2 = j+4 by omega, a_eq, a_eq, a_eq]
    rw [show 2*(j+6) = 2*j+12 by ring, show 2*(j+5) = 2*j+10 by ring,
      show 2*(j+4) = 2*j+8 by ring, show j+6+4 = j+10 by ring, show j+5+4 = j+9 by ring,
      show j+4+4 = j+8 by ring]
    have := alg j
    qify
    push_cast
    linear_combination this

end OMA.S_oeis_a026029

theorem OMA.solution : type_of% @OMA.S_oeis_a026029.main := OMA.S_oeis_a026029.solution_main
