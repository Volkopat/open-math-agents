import OMAStatements.S_oeis_a061100
import Mathlib

-- Problem: A061100, squares with digital root 4; Barker's closed forms.
-- Upstream: formal-conjectures statements/oeis-a061100.lean (declaration OMA.S_oeis_a061100.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: x^2 has digital root 4 exactly when x is congruent to 2 or 7 modulo 9, so the terms are
-- (9j+2)^2 and (9j+7)^2 in increasing order; the closed forms follow by expanding.

namespace OMA.P_oeis_a061100

open OMA.S_oeis_a061100

/-- The predicate of the sequence. -/
def P (m : ℕ) : Prop := IsSquare m ∧ digitalRoot m = 4

/-- The base of the (i+1)-st term. -/
def k (i : ℕ) : ℕ := 9 * (i / 2) + (if i % 2 = 0 then 2 else 7)

/-- The claimed enumeration (zero-based). -/
def f (i : ℕ) : ℕ := k i ^ 2

theorem k_mono : StrictMono k := by
  apply strictMono_nat_of_lt_succ
  intro i
  unfold k
  split_ifs <;> omega

theorem f_mono : StrictMono f := by
  intro i j h
  unfold f
  exact Nat.pow_lt_pow_left (k_mono h) (by norm_num)

theorem sq_mod9 (x : ℕ) : x ^ 2 % 9 = (x % 9) ^ 2 % 9 := Nat.pow_mod x 2 9

theorem dr_eq (m : ℕ) (hm : 0 < m) : digitalRoot m = 4 ↔ m % 9 = 4 := by
  unfold digitalRoot
  rw [if_neg (by omega)]
  omega

theorem f_maps (i : ℕ) : P (f i) := by
  have hk : k i % 9 = 2 ∨ k i % 9 = 7 := by unfold k; split_ifs <;> omega
  have hpos : 0 < f i := by unfold f; have : 2 ≤ k i := by unfold k; split_ifs <;> omega
                            positivity
  refine ⟨⟨k i, by unfold f; ring⟩, (dr_eq _ hpos).mpr ?_⟩
  unfold f
  rw [sq_mod9]
  rcases hk with h | h <;> rw [h] <;> norm_num

theorem f_surj (m : ℕ) (hm : P m) : ∃ i, f i = m := by
  obtain ⟨⟨x, rfl⟩, hd⟩ := hm
  have hpos : 0 < x * x := by
    rcases Nat.eq_zero_or_pos (x * x) with h | h
    · rw [h] at hd; simp [digitalRoot] at hd
    · exact h
  rw [dr_eq _ hpos, ← sq] at hd
  rw [sq_mod9] at hd
  have hx : x % 9 = 2 ∨ x % 9 = 7 := by
    have : x % 9 < 9 := Nat.mod_lt _ (by norm_num)
    generalize x % 9 = r at hd this
    interval_cases r <;> simp_all
  rcases hx with h | h
  · exact ⟨2 * (x / 9), by unfold f k; rw [if_pos (by omega), sq]; congr 1 <;> omega⟩
  · exact ⟨2 * (x / 9) + 1, by unfold f k; rw [if_neg (by omega), sq]; congr 1 <;> omega⟩

theorem nth_eq (i : ℕ) : Nat.nth P i = f i := by
  have hinf : (Set.ofPred P).Infinite :=
    Set.infinite_of_injective_forall_mem f_mono.injective f_maps
  have hU : ∀ j, j ∈ {j : ℕ | ∀ hf : (Set.ofPred P).Finite, j < hf.toFinset.card} :=
    fun j hf => absurd hf hinf
  refine (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn f ?_ ?_ ?_ (hU i)).symm
  · intro x hx
    obtain ⟨j, hj⟩ := f_surj x hx
    exact ⟨j, hU j, hj⟩
  · intro j _
    exact f_maps j
  · exact f_mono.strictMonoOn _

theorem main' : ∀ n : ℕ, 1 ≤ n →
    (Even n → 4 * (a n : ℤ) = 16 - 72 * n + 81 * n ^ 2) ∧
    (Odd n → 4 * (a n : ℤ) = 25 - 90 * n + 81 * n ^ 2) := by
  intro n hn
  have ha : a n = f (n - 1) := nth_eq (n - 1)
  rw [ha]
  constructor
  · rintro ⟨j, rfl⟩
    obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
    unfold f k
    rw [show t + 1 + (t + 1) - 1 = 2 * t + 1 by omega, if_neg (by omega),
      show (2 * t + 1) / 2 = t by omega]
    push_cast
    ring
  · rintro ⟨j, rfl⟩
    unfold f k
    rw [show 2 * j + 1 - 1 = 2 * j by omega, if_pos (by omega), show 2 * j / 2 = j by omega]
    push_cast
    ring

end OMA.P_oeis_a061100

theorem OMA.solution : type_of% @OMA.S_oeis_a061100.main := OMA.P_oeis_a061100.main'
