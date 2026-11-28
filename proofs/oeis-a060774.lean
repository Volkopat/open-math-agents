import OMAStatements.S_oeis_a060774
import Mathlib

open OMA.S_oeis_a060774

theorem OMA.solution : type_of% @OMA.S_oeis_a060774.main := by
  set X : ℕ → ℚ := fun k => ((3 * k).choose k : ℚ) with hXdef
  set Y : ℕ → ℚ := fun k => ((2 * k).choose k : ℚ) with hYdef
  have hX : ∀ k : ℕ, X (k + 1) = (3 * (k : ℚ) + 1) * (3 * (k : ℚ) + 2) * (3 * (k : ℚ) + 3) /
      (((k : ℚ) + 1) * (2 * (k : ℚ) + 1) * (2 * (k : ℚ) + 2)) * X k := by
    intro k
    simp only [hXdef]
    rw [Nat.cast_choose ℚ (by omega : k + 1 ≤ 3 * (k + 1)), Nat.cast_choose ℚ (by omega : k ≤ 3 * k),
      show 3 * (k + 1) - (k + 1) = (2 * k + 1) + 1 by omega, show 3 * k - k = 2 * k by omega,
      show 3 * (k + 1) = (3 * k + 2) + 1 by ring, Nat.factorial_succ (3 * k + 2), Nat.factorial_succ (3 * k + 1),
      Nat.factorial_succ (3 * k), Nat.factorial_succ (2 * k + 1), Nat.factorial_succ (2 * k), Nat.factorial_succ k]
    have h1 : ((3 * k).factorial : ℚ) ≠ 0 := by positivity
    have h2 : (k.factorial : ℚ) ≠ 0 := by positivity
    have h3 : ((2 * k).factorial : ℚ) ≠ 0 := by positivity
    have h4 : (k : ℚ) + 1 ≠ 0 := by positivity
    have h5 : 2 * (k : ℚ) + 1 ≠ 0 := by positivity
    have h6 : 2 * (k : ℚ) + 2 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  have hY : ∀ k : ℕ, Y (k + 1) = 2 * (2 * (k : ℚ) + 1) / ((k : ℚ) + 1) * Y k := by
    intro k
    simp only [hYdef]
    rw [Nat.cast_choose ℚ (by omega : k + 1 ≤ 2 * (k + 1)), Nat.cast_choose ℚ (by omega : k ≤ 2 * k),
      show 2 * (k + 1) - (k + 1) = k + 1 by omega, show 2 * k - k = k by omega,
      show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ (2 * k + 1),
      Nat.factorial_succ (2 * k), Nat.factorial_succ k]
    have h2 : (k.factorial : ℚ) ≠ 0 := by positivity
    have h3 : ((2 * k).factorial : ℚ) ≠ 0 := by positivity
    have h4 : (k : ℚ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  have ha : ∀ k : ℕ, 1 ≤ k → (a k : ℚ) = 6 * X k - 6 * Y k := by
    intro k hk
    simp only [a, hXdef, hYdef, show k ≠ 0 by omega, if_false]
    push_cast; ring
  have hpos : ∀ m : ℕ, (m : ℚ) + 1 ≠ 0 ∧ 2 * (m : ℚ) + 1 ≠ 0 ∧ 2 * (m : ℚ) + 2 ≠ 0 := by
    intro m; refine ⟨by positivity, by positivity, by positivity⟩
  have r1 : ∀ Z : ℕ → ℚ, ∀ m : ℕ, Z = X ∨ Z = Y →
      2 * ((m + 5 : ℕ) : ℚ) * (2 * ((m + 5 : ℕ) : ℚ) - 1) * (((m + 5 : ℕ) : ℚ) - 1) * Z (m + 5)
      + (((m + 5 : ℕ) : ℚ) - 1) * (13 * ((m + 5 : ℕ) : ℚ) ^ 2 - 209 * ((m + 5 : ℕ) : ℚ) + 258) * Z (m + 4)
      + 2 * (-259 * ((m + 5 : ℕ) : ℚ) ^ 3 + 1785 * ((m + 5 : ℕ) : ℚ) ^ 2 - 3728 * ((m + 5 : ℕ) : ℚ) + 2460) * Z (m + 3)
      + 6 * (295 * ((m + 5 : ℕ) : ℚ) ^ 3 - 2068 * ((m + 5 : ℕ) : ℚ) ^ 2 + 4833 * ((m + 5 : ℕ) : ℚ) - 3780) * Z (m + 2)
      - 36 * (3 * ((m + 5 : ℕ) : ℚ) - 10) * (2 * ((m + 5 : ℕ) : ℚ) - 7) * (3 * ((m + 5 : ℕ) : ℚ) - 11) * Z (m + 1) = 0 := by
    intro Z m hZ
    have p1 := hpos (m + 1); have p2 := hpos (m + 2); have p3 := hpos (m + 3); have p4 := hpos (m + 4)
    have p0 := hpos m
    push_cast at p0 p1 p2 p3 p4
    rcases hZ with rfl | rfl
    · simp only [hX]
      push_cast
      field_simp
      ring
    · simp only [hY]
      push_cast
      field_simp
      ring
  have r2 : ∀ Z : ℕ → ℚ, ∀ m : ℕ, Z = X ∨ Z = Y →
      2 * ((m + 3 : ℕ) : ℚ) * (((m + 3 : ℕ) : ℚ) - 1) * (2 * ((m + 3 : ℕ) : ℚ) - 1) * (11 * ((m + 3 : ℕ) : ℚ) ^ 2 - 33 * ((m + 3 : ℕ) : ℚ) + 24) * Z (m + 3)
      - (((m + 3 : ℕ) : ℚ) - 1) * (473 * ((m + 3 : ℕ) : ℚ) ^ 4 - 1892 * ((m + 3 : ℕ) : ℚ) ^ 3 + 2561 * ((m + 3 : ℕ) : ℚ) ^ 2 - 1338 * ((m + 3 : ℕ) : ℚ) + 216) * Z (m + 2)
      + 6 * (3 * ((m + 3 : ℕ) : ℚ) - 5) * (3 * ((m + 3 : ℕ) : ℚ) - 4) * (2 * ((m + 3 : ℕ) : ℚ) - 3) * (11 * ((m + 3 : ℕ) : ℚ) ^ 2 - 11 * ((m + 3 : ℕ) : ℚ) + 2) * Z (m + 1) = 0 := by
    intro Z m hZ
    have p1 := hpos (m + 1); have p2 := hpos (m + 2)
    have p0 := hpos m
    push_cast at p0 p1 p2
    rcases hZ with rfl | rfl
    · simp only [hX]
      push_cast
      field_simp
      ring
    · simp only [hY]
      push_cast
      field_simp
      ring
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
    have key := congrArg₂ (fun u v : ℚ => 6 * u - 6 * v) (r1 X m (Or.inl rfl)) (r1 Y m (Or.inr rfl))
    rw [← @Int.cast_inj ℚ]
    push_cast at key ⊢
    rw [ha (m + 5) (by omega), ha (m + 4) (by omega), ha (m + 3) (by omega),
      ha (m + 2) (by omega), ha (m + 1) (by omega)]
    linear_combination key
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
    have key := congrArg₂ (fun u v : ℚ => 6 * u - 6 * v) (r2 X m (Or.inl rfl)) (r2 Y m (Or.inr rfl))
    rw [← @Int.cast_inj ℚ]
    push_cast at key ⊢
    rw [ha (m + 3) (by omega), ha (m + 2) (by omega), ha (m + 1) (by omega)]
    linear_combination key
