import OMAStatements.S_oeis_a061101
import Mathlib

/-! Proof for OEIS A061101: the digital root of `m` is `≡ m (mod 9)` and below 10, so the
condition is a congruence mod 9; a square `x^2` qualifies iff `x ≡ 4 or 5 (mod 9)`, whose increasing
enumeration is `4, 5, 13, 14, …`; `Nat.nth` is identified with the strictly increasing enumeration of the
squares. Credit: Sudharsan Rajendiran -/

namespace OMA.P061101
open OMA.S_oeis_a061101

/-- the squares with digital root 7 (the predicate of the statement). -/
def P (m : ℕ) : Prop := IsSquare m ∧ digitalRoot m = 7

lemma dr_eq_iff (m r : ℕ) (hr : r < 9) (hr0 : 0 < r) : digitalRoot m = r ↔ m % 9 = r := by
  unfold digitalRoot
  split_ifs with h
  · subst h; omega
  · omega

lemma sq_mod (x : ℕ) : x ^ 2 % 9 = 7 ↔ x % 9 = 4 ∨ x % 9 = 5 := by
  rw [Nat.pow_mod]
  have : x % 9 < 9 := Nat.mod_lt _ (by norm_num)
  interval_cases x % 9 <;> simp

/-- The enumeration `4, 5, 13, 14, 22, 23, …` of the `x` with `x ≡ 4, 5 (mod 9)`. -/
def g (k : ℕ) : ℕ := 9 * (k / 2) + 4 + k % 2

lemma g_strictMono : StrictMono g := by
  apply strictMono_nat_of_lt_succ
  intro k; unfold g; omega

lemma P_iff (m : ℕ) : P m ↔ ∃ k, g k ^ 2 = m := by
  unfold P
  rw [dr_eq_iff _ _ (by norm_num) (by norm_num)]
  constructor
  · rintro ⟨⟨x, rfl⟩, h⟩
    rw [← pow_two, sq_mod] at h
    rcases h with h | h
    · exact ⟨2 * (x / 9), by unfold g; rw [← pow_two]; congr 1; omega⟩
    · exact ⟨2 * (x / 9) + 1, by unfold g; rw [← pow_two]; congr 1; omega⟩
  · rintro ⟨k, rfl⟩
    refine ⟨⟨g k, sq _⟩, ?_⟩
    rw [sq_mod]; unfold g; omega

lemma nth_eq (k : ℕ) : Nat.nth P k = g k ^ 2 := by
  have hmono : StrictMono (fun k => g k ^ 2) :=
    fun a b h => Nat.pow_lt_pow_left (g_strictMono h) (by norm_num)
  have hinf : (Set.ofPred P).Infinite := by
    have : Set.range (fun k => g k ^ 2) ⊆ Set.ofPred P := by
      rintro _ ⟨k, rfl⟩; exact (P_iff _).2 ⟨k, rfl⟩
    exact Set.Infinite.mono this (Set.infinite_range_of_injective hmono.injective)
  have hall : ∀ n : ℕ, n ∈ { n : ℕ | ∀ hf : Set.Finite (Set.ofPred P), n < hf.toFinset.card } :=
    fun n hf => (hinf hf).elim
  refine (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (fun k => g k ^ 2) ?_ ?_ ?_ (hall k)).symm
  · intro m hm
    obtain ⟨j, hj⟩ := (P_iff m).1 hm
    exact ⟨j, hall j, hj⟩
  · intro j _; exact (P_iff _).2 ⟨j, rfl⟩
  · exact fun a _ b _ h => hmono h

end OMA.P061101

theorem OMA.solution : type_of% @OMA.S_oeis_a061101.main := by
  intro n hn
  change (Even n → 4 * ((Nat.nth OMA.P061101.P (n - 1) : ℕ) : ℤ) = (9 * n - 8) ^ 2) ∧
    (Odd n → 4 * ((Nat.nth OMA.P061101.P (n - 1) : ℕ) : ℤ) = (9 * n - 1) ^ 2)
  rw [OMA.P061101.nth_eq]
  unfold OMA.P061101.g
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  refine ⟨fun he => ?_, fun ho => ?_⟩
  · obtain ⟨j, hj⟩ := he
    have hz : 2 * (((9 * (m / 2) + 4 + m % 2 : ℕ)) : ℤ) = 9 * ((m + 1 : ℕ) : ℤ) - 8 := by omega
    push_cast at hz ⊢
    rw [show (4 : ℤ) * ((9 * ((m : ℤ) / 2) + 4 + (m : ℤ) % 2) ^ 2) =
      (2 * (9 * ((m : ℤ) / 2) + 4 + (m : ℤ) % 2)) ^ 2 by ring, hz]
  · obtain ⟨j, hj⟩ := ho
    have hz : 2 * (((9 * (m / 2) + 4 + m % 2 : ℕ)) : ℤ) = 9 * ((m + 1 : ℕ) : ℤ) - 1 := by omega
    push_cast at hz ⊢
    rw [show (4 : ℤ) * ((9 * ((m : ℤ) / 2) + 4 + (m : ℤ) % 2) ^ 2) =
      (2 * (9 * ((m : ℤ) / 2) + 4 + (m : ℤ) % 2)) ^ 2 by ring, hz]
