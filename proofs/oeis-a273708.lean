import OMAStatements.S_oeis_a273708

open OMA.S_oeis_a273708

lemma window_value (t : ℕ) (b : Bool) (f : ℤ → ℤ → Bool) (x y : ℤ) :
    cell t b (fill t f) x y =
      if -(t : ℤ) ≤ x ∧ x ≤ t ∧ -(t : ℤ) ≤ y ∧ y ≤ t then f x y else b := by
  unfold cell fill
  split_ifs with h
  · simp [Vector.get, Int.toNat_of_nonneg (show 0 ≤ y+t by omega),
      Int.toNat_of_nonneg (show 0 ≤ x+t by omega)]
  · rfl

lemma uniform_on (n : ℕ) : background 873 (n+1) = true ∧ background 889 (n+1) = true := by
  induction n with
  | zero => decide
  | succ n ih =>
    constructor <;> rw [background] <;> simp only [ih.1, ih.2] <;> decide

lemma step_value (r t : ℕ) (x y : ℤ) : stage r (t+1) x y =
    if -((t+1 : ℕ) : ℤ) ≤ x ∧ x ≤ (t+1 : ℕ) ∧ -((t+1 : ℕ) : ℤ) ≤ y ∧ y ≤ (t+1 : ℕ) then
      bit r (stage r t x y) (stage r t (x-1) y) (stage r t (x+1) y)
        (stage r t x (y-1)) (stage r t x (y+1))
    else background r (t+1) := by
  change cell (t+1) _ (fill (t+1) _) x y = _
  rw [window_value]
  rfl

lemma one_eq (x y : ℤ) : stage 873 1 x y = stage 889 1 x y := by
  by_cases h : -1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1
  · obtain ⟨h₀,h₁,h₂,h₃⟩ := h
    interval_cases x <;> interval_cases y <;> decide
  · rw [step_value 873 0,step_value 889 0,show ((0+1 : ℕ) : ℤ) = 1 by decide,if_neg h,if_neg h]
    decide

lemma checkerboard_base (x y : ℤ) :
    stage 873 2 x y = stage 889 2 x y ∧
      ((x+y-2)%2 ≠ 0 → stage 873 2 x y = true) := by
  by_cases h : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2
  · obtain ⟨h₀,h₁,h₂,h₃⟩ := h
    interval_cases x <;> interval_cases y <;> decide
  · simp only [step_value 873 1,step_value 889 1,show ((1+1 : ℕ) : ℤ) = 2 by decide,if_neg h,
      (uniform_on 1).1,(uniform_on 1).2,implies_true,and_self]

lemma odd_bits (l r d u : Bool) : bit 873 true l r d u = bit 889 true l r d u := by
  cases l <;> cases r <;> cases d <;> cases u <;> decide

lemma surrounded (c : Bool) : bit 873 c true true true true = true ∧
    bit 889 c true true true true = true := by
  cases c <;> decide

lemma checkerboard (k : ℕ) (x y : ℤ) :
    stage 873 (k+2) x y = stage 889 (k+2) x y ∧
      ((x+y-(k+2 : ℕ))%2 ≠ 0 → stage 873 (k+2) x y = true) := by
  induction k generalizing x y with
  | zero => exact checkerboard_base x y
  | succ k ih =>
    have same (i j : ℤ) := (ih i j).1.symm
    change stage 873 ((k+2)+1) x y = stage 889 ((k+2)+1) x y ∧
      ((x+y-((k+2)+1 : ℕ))%2 ≠ 0 → stage 873 ((k+2)+1) x y = true)
    simp only [step_value 873 (k+2), step_value 889 (k+2), same]
    split_ifs with inside
    · by_cases parity : (x+y-(k+2 : ℕ))%2 = 0
      · have h₁ := (ih (x-1) y).2 (by omega)
        have h₂ := (ih (x+1) y).2 (by omega)
        have h₃ := (ih x (y-1)).2 (by omega)
        have h₄ := (ih x (y+1)).2 (by omega)
        simp only [h₁,h₂,h₃,h₄, (surrounded _).1, (surrounded _).2]
        simp
      · rw [(ih x y).2 parity]
        exact ⟨odd_bits _ _ _ _, fun h => by omega⟩
    · simp [(uniform_on _).1, (uniform_on _).2]

theorem OMA.solution : type_of% @OMA.S_oeis_a273708.main := by
  have eq (t : ℕ) : stage 873 t = stage 889 t := by
    funext x y
    rcases t with _ | (_ | k)
    · rfl
    · exact one_eq x y
    · exact (checkerboard k x y).1
  intro n
  unfold a sampled total
  change (∑ j ∈ Finset.range _, ∑ i ∈ Finset.range _,
    (stage 873 (2^n-1) ((i : ℤ)-(2^n-1 : ℕ)) ((j : ℤ)-(2^n-1 : ℕ))).toNat) = _
  rw [eq]
  rfl

