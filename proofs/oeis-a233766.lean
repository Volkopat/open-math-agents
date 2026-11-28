import OMAStatements.S_oeis_a233766
import Mathlib

namespace OMA.Helpers_a233766

open OMA.S_oeis_a233766

/-- linear-time pairs of consecutive terms of A030133 -/
def cp : ℕ → ℕ × ℕ
  | 0 => (2, 1)
  | k + 1 => ((cp k).2, (Nat.digits 10 ((cp k).1 + (cp k).2)).sum)

lemma cp_eq : ∀ k, cp k = (A030133 k, A030133 (k + 1)) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [cp, ih]
    simp only [Prod.mk.injEq, true_and]
    rfl

lemma v90 : A030133 90 = 9 := by
  have h := cp_eq 90
  have : cp 90 = (9, 7) := by decide +kernel
  rw [this, Prod.mk.injEq] at h
  exact h.1.symm

/-- the predicate of A007775 -/
def P (m : ℕ) : Prop := ¬ 2 ∣ m ∧ ¬ 3 ∣ m ∧ ¬ 5 ∣ m

instance : DecidablePred P := fun m => by unfold P; infer_instance

lemma nth24 : A007775 25 = 91 := by
  unfold A007775
  have hc : Nat.count P 91 = 24 := by decide +kernel
  have h := Nat.nth_count (p := P) (n := 91) (by decide)
  rw [hc] at h
  exact h

lemma nth0 : A007775 1 = 1 := by
  unfold A007775
  have hc : Nat.count P 1 = 0 := by decide +kernel
  have h := Nat.nth_count (p := P) (n := 1) (by decide)
  rw [hc] at h
  exact h

end OMA.Helpers_a233766

open OMA.Helpers_a233766 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a233766.main) := by
  rintro ⟨-, h⟩
  have h25 := h 25 (by norm_num)
  simp only [OMA.S_oeis_a233766.a, show (25 : ℕ) ≠ 0 by norm_num, show (25 - 24 : ℕ) = 1 by norm_num,
    show (1 : ℕ) ≠ 0 by norm_num, if_false, nth24, nth0] at h25
  rw [show (91 - 1 : ℕ) = 90 by norm_num, v90] at h25
  have : OMA.S_oeis_a233766.A030133 (1 - 1) = 2 := rfl
  rw [this] at h25
  exact absurd h25 (by norm_num)

