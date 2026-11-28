import OMAStatements.S_oeis_a368635

/-!
# The parity conjecture for OEIS A368635

In the Cauchy product for A(x)^2, terms appear in equal pairs except
for the middle term in even degree. Reducing modulo two gives the two
recurrences for parity used in the induction below.
-/

namespace OMA.S_oeis_a368635

private theorem coeff_congr (a b : Nat → Int) (n : Nat)
    (h : ∀ i, i ≤ n → a i = b i) : squareCoeff a 0 n = squareCoeff b 0 n := by
  unfold squareCoeff
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  simp only [Nat.zero_add]
  rw [h i (by omega), h (n - i) (by omega)]

private theorem next_congr (a b : Nat → Int) (n : Nat)
    (h : ∀ i, i ≤ n → a i = b i) : next a n = next b n := by
  unfold next
  rw [coeff_congr a b n h, coeff_congr (fun i => (-1 : Int) ^ i * a i)
    (fun i => (-1 : Int) ^ i * b i) n (fun i hi => by rw [h i hi])]

private theorem coeff_step (n : Nat) : coeff (n + 1) = next coeff n := by
  rw [coeff]
  apply next_congr
  intro i hi
  simp [hi]

private theorem peel (a : Nat → Int) (s n : Nat) :
    squareCoeff a s (n + 2) =
      2 * (a s * a (s + (n + 2))) + squareCoeff a (s + 1) n := by
  unfold squareCoeff
  rw [List.range_succ, List.map_append, List.sum_append_int, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Function.comp_def, List.sum_cons,
    List.map_nil, List.sum_nil, Int.add_zero, Nat.add_zero, Nat.sub_zero, Nat.sub_self]
  have middle : ((List.range (n + 1)).map (fun i =>
      a (s + (i + 1)) * a (s + (n + 2 - (i + 1))))).sum =
      ((List.range (n + 1)).map (fun i =>
      a (s + 1 + i) * a (s + 1 + (n - i)))).sum := by
    congr 1
    apply List.map_congr_left
    intro i hi
    have h := List.mem_range.mp hi
    congr 2 <;> omega
  rw [middle, Int.mul_comm (a (s + (n + 2))) (a s)]
  omega

private theorem square_mod_two (z : Int) : (z * z) % 2 = z % 2 := by
  rw [Int.mul_emod]
  have h : z % 2 = 0 ∨ z % 2 = 1 := by omega
  rcases h with h | h <;> simp [h]

private theorem evenWidth (a : Nat → Int) (m s : Nat) :
    squareCoeff a s (2 * m) % 2 = a (s + m) % 2 := by
  induction m generalizing s with
  | zero => simp [squareCoeff, List.range_succ, square_mod_two]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 by omega, peel]
    have h := ih (s + 1)
    rw [show s + 1 + m = s + (m + 1) by omega] at h
    omega

private theorem oddWidth (a : Nat → Int) (m s : Nat) :
    squareCoeff a s (2 * m + 1) % 2 = 0 := by
  induction m generalizing s with
  | zero =>
    simp [squareCoeff, List.range_succ, Int.mul_comm (a (s + 1)) (a s)]
    omega
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega, peel]
    have h := ih (s + 1)
    omega

private theorem doublePower (m : Nat) :
    (∃ k : Nat, 2 * m + 2 = 2 ^ k) ↔ (∃ k : Nat, m + 1 = 2 ^ k) := by
  constructor
  · rintro ⟨k, h⟩
    cases k with
    | zero => simp at h
    | succ k =>
      exact ⟨k, by rw [Nat.pow_succ] at h; omega⟩
  · rintro ⟨k, h⟩
    exact ⟨k + 1, by rw [Nat.pow_succ]; omega⟩

private theorem noOddPower (m : Nat) : ¬ ∃ k : Nat, 2 * m + 3 = 2 ^ k := by
  rintro ⟨k, h⟩
  cases k with
  | zero => simp at h
  | succ k => rw [Nat.pow_succ] at h; omega

/-- Every integer sequence satisfying the original generating function,
written coefficient by coefficient, is odd exactly at the claimed indices. -/
theorem parity (a : Nat → Int) (initial : a 0 = 1)
    (step : ∀ n : Nat, a (n + 1) = next a n) (n : Nat) :
    a n % 2 = 1 ↔ ∃ k : Nat, n + 1 = 2 ^ k := by
  have stepMod (j : Nat) : a (j + 1) % 2 = squareCoeff a 0 j % 2 := by
    rw [step, next]
    omega
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => exact ⟨fun _ => ⟨0, rfl⟩, fun _ => by rw [initial]; decide⟩
    | succ j =>
      obtain ⟨m, hj | hj⟩ : ∃ m, j = 2 * m ∨ j = 2 * m + 1 := by
        exact ⟨j / 2, by omega⟩
      · subst j
        rw [stepMod, evenWidth, Nat.zero_add]
        exact (ih m (by omega)).trans (doublePower m).symm
      · subst j
        rw [stepMod, oddWidth]
        exact ⟨fun h => by omega, fun h => False.elim (noOddPower m h)⟩

end OMA.S_oeis_a368635

open OMA.S_oeis_a368635

theorem OMA.solution : type_of% @OMA.S_oeis_a368635.main := by
  exact parity coeff (by rw [coeff]) OMA.S_oeis_a368635.coeff_step
