import OMAStatements.S_oeis_a198900

-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)

open OMA.S_oeis_a198900 Finset

def gg (L : ℕ) : ℕ → ℕ → ℤ
  | 0, _ => 1
  | n+1, t => ((t:ℤ)*t+t+1) * gg L n t + (if t+2 < L then 2*((t:ℤ)+1) * gg L n (t+1) else 0) +
      (if t+3 < L then gg L n (t+2) else 0)

theorem ext_eq (L : ℕ) : ∀ n t a b, a < t+2 → b < t+2 → a ≠ b → extensions L n t a b = gg L n t := by
  intro n
  induction n with
  | zero => intro t a b _ _ _; simp [extensions, gg]
  | succ n ih =>
    intro t a b ha hb hab
    have hbo : b ∈ range (t+2) := mem_range.2 hb
    have hao : a ∈ range (t+2) := mem_range.2 ha
    simp only [extensions, gg]
    have s1 : ∑ y ∈ (range (t+2)).erase b, extensions L n t b y = ((t:ℤ)+1) * gg L n t := by
      rw [Finset.sum_congr rfl (g := fun _ => gg L n t)]
      · rw [Finset.sum_const, Finset.card_erase_of_mem hbo]; simp
      · intro y hy
        simp only [mem_erase, mem_range] at hy
        exact ih t b y hb hy.2 (Ne.symm hy.1)
    have s2 : ∑ x ∈ ((range (t+2)).erase a).erase b, ∑ y ∈ ((range (t+2)).erase b).erase x, extensions L n t x y
        = (t:ℤ) * t * gg L n t := by
      rw [Finset.sum_congr rfl (g := fun _ => (t:ℤ) * gg L n t)]
      · rw [Finset.sum_const, Finset.card_erase_of_mem, Finset.card_erase_of_mem hao]
        · simp; ring
        · simp [mem_erase, mem_range, hb, Ne.symm hab]
      · intro x hx
        simp only [mem_erase, mem_range] at hx
        rw [Finset.sum_congr rfl (g := fun _ => gg L n t)]
        · rw [Finset.sum_const, Finset.card_erase_of_mem, Finset.card_erase_of_mem hbo]
          · simp
          · simp [mem_erase, mem_range, hx.2.2, hx.1]
        · intro y hy
          simp only [mem_erase, mem_range] at hy
          exact ih t x y hx.2.2 hy.2.2 (Ne.symm hy.1)
    have s3 : ∑ y ∈ (range (t+2)).erase b, extensions L n (t+1) (t+2) y = ((t:ℤ)+1) * gg L n (t+1) := by
      rw [Finset.sum_congr rfl (g := fun _ => gg L n (t+1))]
      · rw [Finset.sum_const, Finset.card_erase_of_mem hbo]; simp
      · intro y hy
        simp only [mem_erase, mem_range] at hy
        exact ih (t+1) (t+2) y (by omega) (by omega) (by omega)
    have s4 : ∑ x ∈ (range (t+2)).erase a, extensions L n (t+1) x (t+2) = ((t:ℤ)+1) * gg L n (t+1) := by
      rw [Finset.sum_congr rfl (g := fun _ => gg L n (t+1))]
      · rw [Finset.sum_const, Finset.card_erase_of_mem hao]; simp
      · intro x hx
        simp only [mem_erase, mem_range] at hx
        exact ih (t+1) x (t+2) (by omega) (by omega) (by omega)
    have s5 : ∀ c : ℤ, True := fun _ => trivial
    rw [s1, s2]
    by_cases h1 : t+2 < L
    · by_cases h2 : t+3 < L
      · simp only [h1, h2, if_true, s3, s4]
        rw [ih (t+2) (t+2) (t+3) (by omega) (by omega) (by omega)]
        ring
      · simp only [h1, h2, if_true, if_false, s3, s4]
        ring
    · have h2 : ¬ t+3 < L := by omega
      simp only [h1, h2, if_false]
      ring

theorem gg_closed : ∀ n : ℕ,
6 * gg 5 n 0 = 2 * 1^n + 3 * 3^n + 1 * 13^n ∧
    2 * gg 5 n 1 = 1 * 3^n + 1 * 13^n ∧
    1 * gg 5 n 2 = 1 * 13^n ∧
    1 * gg 5 n 3 = 1 * 13^n := by
  intro n
  induction n with
  | zero => simp [gg]
  | succ n ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih
    simp only [one_pow] at h0
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [gg, pow_succ, one_pow] <;> linarith


theorem seq_eq (m : ℕ) : 6 * OMA.S_oeis_a198900.sequence (m+1) = 2 + 3 * 3^m + 13^m := by
  have : OMA.S_oeis_a198900.sequence (m+1) = gg 5 m 0 := by
    show extensions 5 m 0 0 1 = _
    exact ext_eq 5 m 0 0 1 (by omega) (by omega) (by omega)
  rw [this]
  have := (gg_closed m).1
  simpa using this

theorem OMA.solution : type_of% @OMA.S_oeis_a198900.main := by
  have hs : ∀ m : ℕ, 78 * OMA.S_oeis_a198900.sequence (m+1) = 26 + 13*3^(m+1) + 13^(m+1) := by
    intro m
    have := seq_eq m
    rw [pow_succ, pow_succ]
    linarith
  refine ⟨hs, ?_⟩
  have s0 : OMA.S_oeis_a198900.sequence 0 = 0 := rfl
  have s1 : OMA.S_oeis_a198900.sequence 1 = 1 := by have := hs 0; norm_num at this; omega
  have s2 : OMA.S_oeis_a198900.sequence 2 = 4 := by have := hs 1; norm_num at this; omega
  have s3 : OMA.S_oeis_a198900.sequence 3 = 33 := by have := hs 2; norm_num at this; omega
  intro n
  rcases n with _ | _ | _ | _ | n
  · simp [delayed, numerator, s0]
  · simp [delayed, numerator, s0, s1]
  · simp [delayed, numerator, s0, s1, s2]
  · simp [delayed, numerator, s0, s1, s2, s3]
  · simp only [delayed, numerator]
    have e : ∀ d, d ≤ 3 → d ≤ n + 4 := by intro d h; omega
    simp only [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), if_true]
    have h3 := hs (n+3)
    have h2 := hs (n+2)
    have h1 := hs (n+1)
    have h0 := hs n
    have e0 : n + 4 - 0 = (n+3)+1 := by omega
    have e1 : n + 4 - 1 = (n+2)+1 := by omega
    have e2 : n + 4 - 2 = (n+1)+1 := by omega
    have e3 : n + 4 - 3 = n+1 := by omega
    rw [e0, e1, e2, e3]
    have : 78 * (OMA.S_oeis_a198900.sequence (n+3+1) - 17 * OMA.S_oeis_a198900.sequence (n+2+1) + 55 * OMA.S_oeis_a198900.sequence (n+1+1) - 39 * OMA.S_oeis_a198900.sequence (n+1)) = 78 * (if n + 4 = 1 then 1 else if n + 4 = 2 then -13 else if n + 4 = 3 then 20 else 0) := by
      have : (if n + 4 = 1 then (1:ℤ) else if n + 4 = 2 then -13 else if n + 4 = 3 then 20 else 0) = 0 := by
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [this]
      simp only [pow_succ] at h3 h2 h1 h0
      linarith
    omega
