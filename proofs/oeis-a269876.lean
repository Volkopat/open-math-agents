import OMAStatements.S_oeis_a269876

/-! Exact alternating checkerboard squares for the two-dimensional Rule 43. -/

namespace Rule43Shape

open OMA.S_oeis_a269876

def inBox (r i j : ℤ) : Prop := -r ≤ i ∧ i ≤ r ∧ -r ≤ j ∧ j ≤ r

def evenCell (i j : ℤ) : Prop := (i + j) % 2 = 0

private theorem rule_bits : ∀ b l r d u : Bool,
    rule 43 b (l.toNat + r.toNat + d.toNat + u.toNat) = true ↔
      (l = false ∧ r = false ∧ d = false ∧ u = false) ∨
      (b = true ∧ l.toNat + r.toNat + d.toNat + u.toNat ≤ 2) := by
  decide

private theorem false_iff_not_true (b : Bool) : b = false ↔ ¬ b = true := by
  cases b <;> decide

private theorem even_step {f : ℤ → ℤ → Bool} (r : ℤ) (hr : 0 ≤ r)
    (hf : ∀ i j, f i j = true ↔ inBox r i j ∧ evenCell i j) (i j : ℤ) :
    rule 43 (f i j) ((f (i - 1) j).toNat + (f (i + 1) j).toNat +
      (f i (j - 1)).toNat + (f i (j + 1)).toNat) = false ↔
        inBox (r + 1) i j ∧ (i + j) % 2 = 1 := by
  rw [false_iff_not_true, rule_bits]
  have hc := hf i j
  have hl := hf (i - 1) j
  have hh := hf (i + 1) j
  have hd := hf i (j - 1)
  have hu := hf i (j + 1)
  cases c : f i j <;> cases l : f (i - 1) j <;> cases h : f (i + 1) j <;>
    cases d : f i (j - 1) <;> cases u : f i (j + 1) <;>
    simp [c, l, h, d, u, inBox, evenCell, Bool.toNat] at hc hl hh hd hu ⊢ <;> omega

private theorem odd_step {f : ℤ → ℤ → Bool} (r : ℤ) (hr : 1 ≤ r)
    (hf : ∀ i j, f i j = false ↔ inBox r i j ∧ (i + j) % 2 = 1) (i j : ℤ) :
    rule 43 (f i j) ((f (i - 1) j).toNat + (f (i + 1) j).toNat +
      (f i (j - 1)).toNat + (f i (j + 1)).toNat) = true ↔
        inBox r i j ∧ evenCell i j := by
  rw [rule_bits]
  have hc := hf i j
  have hl := hf (i - 1) j
  have hh := hf (i + 1) j
  have hd := hf i (j - 1)
  have hu := hf i (j + 1)
  cases c : f i j <;> cases l : f (i - 1) j <;> cases h : f (i + 1) j <;>
    cases d : f i (j - 1) <;> cases u : f i (j + 1) <;>
    simp [c, l, h, d, u, inBox, evenCell, Bool.toNat] at hc hl hh hd hu ⊢ <;> omega

theorem even_shape (m : ℕ) (i j : ℤ) :
    grid 43 (2 * m) i j = true ↔ inBox m i j ∧ evenCell i j := by
  induction m generalizing i j with
  | zero =>
    simp only [grid, decide_eq_true_eq, Nat.cast_zero, inBox, evenCell, neg_zero]
    constructor
    · rintro ⟨rfl, rfl⟩
      decide
    · omega
  | succ m ih =>
    have hm : 0 ≤ (m : ℤ) := by omega
    have hi (x y : ℤ) : grid 43 (2 * m + 1) x y = false ↔
        inBox ((m : ℤ) + 1) x y ∧ (x + y) % 2 = 1 := by
      rw [grid]
      exact even_step m hm ih x y
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, grid, Nat.cast_succ]
    exact odd_step ((m : ℤ) + 1) (by omega) hi i j

theorem odd_shape (m : ℕ) (i j : ℤ) :
    grid 43 (2 * m + 1) i j = false ↔ inBox ((m : ℤ) + 1) i j ∧ (i + j) % 2 = 1 := by
  rw [grid]
  exact even_step m (by omega) (even_shape m) i j

end Rule43Shape

namespace OMA.S_oeis_a269876

open Finset

private def rule43ParityLine (lo m r : ℕ) : Finset ℕ :=
  (range (m + 1 - r)).map ⟨fun x => lo + 2 * x + r, by
    intro a b h
    change lo + 2 * a + r = lo + 2 * b + r at h
    omega⟩

private theorem mem_rule43ParityLine {lo m r x : ℕ} (hr : r ≤ 1) :
    x ∈ rule43ParityLine lo m r ↔
      lo ≤ x ∧ x < lo + 2 * m + 1 ∧ (x - lo) % 2 = r := by
  unfold rule43ParityLine
  rw [mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' := mem_range.mp hk
    change lo ≤ lo + 2 * k + r ∧ lo + 2 * k + r < lo + 2 * m + 1 ∧
      (lo + 2 * k + r - lo) % 2 = r
    omega
  · rintro ⟨hlo, hhi, hm⟩
    refine ⟨(x - lo) / 2, mem_range.mpr (by omega), ?_⟩
    change lo + 2 * ((x - lo) / 2) + r = x
    omega

private theorem rule43ParityLine_card (lo m r : ℕ) :
    (rule43ParityLine lo m r).card = m + 1 - r := by
  simp [rule43ParityLine]

private theorem rule43ParityLine_disjoint (lo m : ℕ) :
    Disjoint (rule43ParityLine lo m 0) (rule43ParityLine lo m 1) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  have hx' := (mem_rule43ParityLine (by decide)).mp hx
  have hy' := (mem_rule43ParityLine (by decide)).mp hy
  omega

theorem a_even_of_shape (m : ℕ)
    (shape : ∀ i j : ℤ, grid 43 (2 * m) i j = true ↔
      |i| ≤ (m : ℤ) ∧ |j| ≤ (m : ℤ) ∧ (i + j) % 2 = 0) :
    a (2 * m) = 2 * m ^ 2 + 2 * m + 1 := by
  have hs :
      ((range (2 * (2 * m) + 1) ×ˢ range (2 * (2 * m) + 1)).filter
          (fun p : ℕ × ℕ => grid 43 (2 * m) ((p.1 : ℤ) - (2 * m : ℕ))
            ((p.2 : ℤ) - (2 * m : ℕ)) = true)) =
        (rule43ParityLine m m 0 ×ˢ rule43ParityLine m m 0) ∪
          (rule43ParityLine m m 1 ×ˢ rule43ParityLine m m 1) := by
    ext ⟨x, y⟩
    simp only [mem_filter, mem_product, mem_range, mem_union,
      mem_rule43ParityLine (by decide : (0 : ℕ) ≤ 1),
      mem_rule43ParityLine (by decide : (1 : ℕ) ≤ 1), shape, abs_le]
    omega
  unfold a
  rw [hs, card_union_of_disjoint (disjoint_product.mpr
    (Or.inl (rule43ParityLine_disjoint m m))), card_product, card_product]
  simp only [rule43ParityLine_card, Nat.sub_zero, Nat.add_sub_cancel]
  ring

theorem a_odd_of_shape (m : ℕ)
    (shape : ∀ i j : ℤ, grid 43 (2 * m + 1) i j = false ↔
      |i| ≤ (m : ℤ) + 1 ∧ |j| ≤ (m : ℤ) + 1 ∧ (i + j) % 2 = 1) :
    a (2 * m + 1) = 14 * m ^ 2 + 18 * m + 5 := by
  let n := 2 * m + 1
  let square := range (2 * n + 1) ×ˢ range (2 * n + 1)
  let on (p : ℕ × ℕ) := grid 43 n ((p.1 : ℤ) - n) ((p.2 : ℤ) - n)
  have hs : square.filter (fun p => on p = false) =
      (rule43ParityLine m (m + 1) 0 ×ˢ rule43ParityLine m (m + 1) 1) ∪
        (rule43ParityLine m (m + 1) 1 ×ˢ rule43ParityLine m (m + 1) 0) := by
    ext ⟨x, y⟩
    simp only [square, on, n, mem_filter, mem_product, mem_range, mem_union,
      mem_rule43ParityLine (by decide : (0 : ℕ) ≤ 1),
      mem_rule43ParityLine (by decide : (1 : ℕ) ≤ 1), shape, abs_le]
    omega
  have hcount := square.card_filter_add_card_filter_not (fun p => on p = true)
  have hnot (p : ℕ × ℕ) : (¬ on p = true) ↔ on p = false := by cases on p <;> simp
  simp only [hnot, hs, card_union_of_disjoint (disjoint_product.mpr
    (Or.inl (rule43ParityLine_disjoint m (m + 1)))), card_product, rule43ParityLine_card,
    Nat.sub_zero, Nat.add_sub_cancel, square, card_range] at hcount
  change a n + ((m + 1 + 1) * (m + 1) + (m + 1) * (m + 1 + 1)) =
      (2 * n + 1) * (2 * n + 1) at hcount
  change a n = 14 * m ^ 2 + 18 * m + 5
  apply Nat.add_right_cancel (m := (m + 1 + 1) * (m + 1) + (m + 1) * (m + 1 + 1))
  rw [hcount]
  dsimp [n]
  ring

end OMA.S_oeis_a269876

/-! The two parity counts imply the closed forms, recurrence and generating function. -/

namespace OMA.S_oeis_a269876

open PowerSeries

private theorem count_recurrence
    (evenCount : ∀ m : ℕ, a (2*m) = 2*m^2+2*m+1)
    (oddCount : ∀ m : ℕ, a (2*m+1) = 14*m^2+18*m+5)
    (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 3*a (n-2) - 3*a (n-4) + a (n-6) := by
  let k := n / 2 - 3
  by_cases he : n % 2 = 0
  · rw [show n = 2*(k+3) by dsimp [k]; omega,
      show 2*(k+3)-2 = 2*(k+2) by omega, show 2*(k+3)-4 = 2*(k+1) by omega,
      show 2*(k+3)-6 = 2*k by omega, evenCount, evenCount, evenCount, evenCount]
    push_cast
    ring
  · rw [show n = 2*(k+3)+1 by dsimp [k]; omega,
      show 2*(k+3)+1-2 = 2*(k+2)+1 by omega, show 2*(k+3)+1-4 = 2*(k+1)+1 by omega,
      show 2*(k+3)+1-6 = 2*k+1 by omega, oddCount, oddCount, oddCount, oddCount]
    push_cast
    ring

private theorem count_gf
    (evenCount : ∀ m : ℕ, a (2*m) = 2*m^2+2*m+1)
    (oddCount : ∀ m : ℕ, a (2*m+1) = 14*m^2+18*m+5) :
    mk (fun n ↦ (a n : ℤ)) * ((1 - X)^3*(1 + X)^3) =
      1 + 5*X + 2*X^2 + 22*X^3 + X^4 + X^5 := by
  let A := mk (fun n ↦ (a n : ℤ))
  change A * _ = _
  have hleft : A * ((1 - X)^3*(1 + X)^3) =
      A - C 3 * (A*X^2) + C 3 * (A*X^4) - A*X^6 := by
    rw [show C (3 : ℤ) = (3 : ℤ⟦X⟧) by norm_num]
    ring
  have hright : (1 : ℤ⟦X⟧) + 5*X + 2*X^2 + 22*X^3 + X^4 + X^5 =
      1 + C 5*X^1 + C 2*X^2 + C 22*X^3 + X^4 + X^5 := by norm_num
  rw [hleft, hright]
  ext n
  simp only [map_add, map_sub, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', A, coeff_mk, coeff_one, coeff_X_pow]
  by_cases hn : n < 6
  · have h0 := evenCount 0
    have h1 := oddCount 0
    have h2 := evenCount 1
    have h3 := oddCount 1
    have h4 := evenCount 2
    have h5 := oddCount 2
    norm_num at h0 h1 h2 h3 h4 h5
    interval_cases n <;> norm_num [h0, h1, h2, h3, h4, h5]
  · have hrec := count_recurrence evenCount oddCount n (by omega)
    simp only [if_pos (show 2 ≤ n by omega), if_pos (show 4 ≤ n by omega),
      if_pos (show 6 ≤ n by omega), if_neg (show n ≠ 0 by omega),
      if_neg (show n ≠ 1 by omega), if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 5 by omega), add_zero]
    linarith

theorem main_of_counts
    (evenCount : ∀ m : ℕ, a (2*m) = 2*m^2+2*m+1)
    (oddCount : ∀ m : ℕ, a (2*m+1) = 14*m^2+18*m+5) : type_of% @main := by
  refine ⟨?_, ?_, ?_, count_recurrence evenCount oddCount, count_gf evenCount oddCount⟩
  · intro n
    let m := n / 2
    by_cases he : n % 2 = 0
    · rw [show n = 2*m by dsimp [m]; omega, evenCount, pow_mul]
      push_cast
      norm_num
      have h : 4 + 4 * (2 * (m : ℤ)) + 2 * (2 * (m : ℤ)) ^ 2 =
          4 * (2 * (m : ℤ)^2 + 2 * m + 1) := by ring
      rw [h]
      omega
    · rw [show n = 2*m+1 by dsimp [m]; omega, oddCount, pow_add, pow_mul]
      push_cast
      norm_num
      have h : (1 - 3 - 2 * (-3 - 1) * (2 * (m : ℤ) + 1) +
          (8 + 6) * (2 * (m : ℤ) + 1)^2) = 4 * (14 * (m : ℤ)^2 + 18 * m + 5) := by ring
      omega
  · intro n he
    let m := n / 2
    rw [show n = 2*m by dsimp [m]; omega, evenCount]
    push_cast
    have h : (2 * (m : ℤ))^2 + 2 * (2*m) + 2 = 2 * (2 * (m : ℤ)^2 + 2*m + 1) := by ring
    omega
  · intro n ho
    let m := n / 2
    rw [show n = 2*m+1 by dsimp [m]; omega, oddCount]
    push_cast
    have h : 7 * (2 * (m : ℤ) + 1)^2 + 4 * (2*m+1) - 1 =
        2 * (14 * (m : ℤ)^2 + 18*m + 5) := by ring
    omega

end OMA.S_oeis_a269876

open OMA.S_oeis_a269876

theorem OMA.solution : type_of% @OMA.S_oeis_a269876.main := by
  apply main_of_counts
  · intro m
    apply a_even_of_shape m
    intro i j
    simpa [Rule43Shape.inBox, Rule43Shape.evenCell, abs_le, and_assoc] using
      Rule43Shape.even_shape m i j
  · intro m
    apply a_odd_of_shape m
    intro i j
    simpa [Rule43Shape.inBox, abs_le, and_assoc] using Rule43Shape.odd_shape m i j
