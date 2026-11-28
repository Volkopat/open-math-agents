import OMAStatements.S_oeis_a256007

-- Proof of the statement in #22643 (statement by @Haruzame0). Credit for the proof: @bnb9001
-- The good numbers are 0..3 and the blocks 2F_k - 2, 2F_k - 1, 2F_k (k >= 4), so the n-th one is
-- g(n) = 2F_k - 2 + i for n + 8 = 3k + i (n >= 4); then F_k = 2F_(k-1) - F_(k-3) gives the recurrence.

namespace OMA_OEIS_A256007_Proof

open OMA.S_oeis_a256007

open Finset

/-- the explicit enumeration -/
def g (n : ℕ) : ℕ := if n < 4 then n else 2 * Nat.fib ((n + 8) / 3) - 2 + (n + 8) % 3

theorem fib_ge (k : ℕ) (hk : 4 ≤ k) : 3 ≤ Nat.fib k := by
  have : Nat.fib 4 ≤ Nat.fib k := Nat.fib_mono hk
  have h4 : Nat.fib 4 = 3 := by decide
  omega

theorem fib_gap (k : ℕ) (hk : 4 ≤ k) : Nat.fib k + 2 ≤ Nat.fib (k + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show j + 1 + 1 = j + 2 by ring, Nat.fib_add_two]
  have : Nat.fib 3 ≤ Nat.fib j := Nat.fib_mono (by omega)
  have h3 : Nat.fib 3 = 2 := by decide
  omega

theorem g_strictMono : StrictMono g := by
  apply strictMono_nat_of_lt_succ
  intro n
  unfold g
  rcases (show n + 1 < 4 ∨ n = 3 ∨ 4 ≤ n by omega) with h | h | h
  · rw [if_pos (by omega), if_pos h]; omega
  · subst h; rw [if_pos (by omega), if_neg (by omega)]; decide
  · rw [if_neg (by omega), if_neg (by omega)]
    have hk : 4 ≤ (n + 8) / 3 := by omega
    have hF := fib_ge _ hk
    rcases (show (n + 8) % 3 < 2 ∨ (n + 8) % 3 = 2 by omega) with hi | hi
    · rw [show (n + 1 + 8) / 3 = (n + 8) / 3 by omega, show (n + 1 + 8) % 3 = (n + 8) % 3 + 1 by omega]
      omega
    · rw [show (n + 1 + 8) / 3 = (n + 8) / 3 + 1 by omega, show (n + 1 + 8) % 3 = 0 by omega]
      have := fib_gap _ hk
      omega

theorem good_iff (m : ℕ) : good m ↔ ∃ n, g n = m := by
  constructor
  · rintro ⟨f, ⟨i, hi, rfl⟩, hm⟩
    rcases (show i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i by omega) with h | h | h | h
    · subst h
      have h1 : Nat.fib 1 = 1 := by decide
      rw [h1] at hm
      exact ⟨m, by unfold g; rw [if_pos (by omega)]⟩
    · subst h
      have h1 : Nat.fib 2 = 1 := by decide
      rw [h1] at hm
      exact ⟨m, by unfold g; rw [if_pos (by omega)]⟩
    · subst h
      have h1 : Nat.fib 3 = 2 := by decide
      rw [h1] at hm
      rcases (show m < 4 ∨ m = 4 by omega) with h | h
      · exact ⟨m, by unfold g; rw [if_pos h]⟩
      · exact ⟨4, by rw [h]; decide⟩
    · have hF := fib_ge i h
      obtain ⟨j, hj, hmj⟩ : ∃ j, j < 3 ∧ m = 2 * Nat.fib i - 2 + j := by
        rcases hm with h | h | h
        · exact ⟨0, by omega, by omega⟩
        · exact ⟨1, by omega, by omega⟩
        · exact ⟨2, by omega, by omega⟩
      refine ⟨3 * i - 8 + j, ?_⟩
      unfold g
      rw [if_neg (by omega), show (3 * i - 8 + j + 8) / 3 = i by omega,
        show (3 * i - 8 + j + 8) % 3 = j by omega, hmj]
  · rintro ⟨n, rfl⟩
    unfold g
    split_ifs with h
    · refine ⟨if n = 3 then 2 else 1, ?_, ?_⟩
      · split_ifs
        · exact ⟨3, by omega, by decide⟩
        · exact ⟨1, by omega, by decide⟩
      · split_ifs with h3 <;> omega
    · refine ⟨Nat.fib ((n + 8) / 3), ⟨(n + 8) / 3, by omega, rfl⟩, ?_⟩
      have hF := fib_ge ((n + 8) / 3) (by omega)
      have : (n + 8) % 3 < 3 := Nat.mod_lt _ (by omega)
      omega

theorem nth_eq (j : ℕ) : Nat.nth good j = g j := by
  classical
  have hp : good (g j) := (good_iff _).mpr ⟨j, rfl⟩
  have hc : Nat.count good (g j) = j := by
    rw [Nat.count_eq_card_filter_range]
    have : (range (g j)).filter good = (range j).image g := by
      ext v
      simp only [mem_filter, mem_range, mem_image]
      constructor
      · rintro ⟨hv, ht⟩
        obtain ⟨i, rfl⟩ := (good_iff v).mp ht
        exact ⟨i, g_strictMono.lt_iff_lt.mp hv, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨g_strictMono hi, (good_iff _).mpr ⟨i, rfl⟩⟩
    rw [this, card_image_of_injective _ g_strictMono.injective, card_range]
  have := Nat.nth_count hp
  rwa [hc] at this

theorem g_big (n : ℕ) (hn : 4 ≤ n) :
    (g n : ℤ) = 2 * (Nat.fib ((n + 8) / 3) : ℤ) - 2 + ((n + 8) % 3 : ℕ) := by
  unfold g
  rw [if_neg (by omega)]
  have hF := fib_ge ((n + 8) / 3) (by omega)
  push_cast [Nat.cast_add, Nat.cast_sub (by omega : 2 ≤ 2 * Nat.fib ((n + 8) / 3))]
  ring

theorem stmt' : ∀ n : ℕ, 12 < n →
    (term n : ℤ) = 2 * (term (n - 3) : ℤ) - (term (n - 9) : ℤ) := by
  intro n hn
  unfold term
  rw [nth_eq, nth_eq, nth_eq, g_big n (by omega), g_big (n - 3) (by omega), g_big (n - 9) (by omega)]
  obtain ⟨k, hk⟩ : ∃ k, (n + 8) / 3 = k + 7 := ⟨(n + 8) / 3 - 7, by omega⟩
  rw [hk, show (n - 3 + 8) / 3 = k + 6 by omega, show (n - 9 + 8) / 3 = k + 4 by omega,
    show (n - 3 + 8) % 3 = (n + 8) % 3 by omega, show (n - 9 + 8) % 3 = (n + 8) % 3 by omega]
  have e1 : Nat.fib (k + 7) = Nat.fib (k + 6) + Nat.fib (k + 5) := by
    rw [show k + 7 = (k + 5) + 2 by ring, Nat.fib_add_two]; ring
  have e2 : Nat.fib (k + 6) = Nat.fib (k + 5) + Nat.fib (k + 4) := by
    rw [show k + 6 = (k + 4) + 2 by ring, Nat.fib_add_two]; ring
  push_cast [e1, e2]
  ring

end OMA_OEIS_A256007_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a256007.main := OMA_OEIS_A256007_Proof.stmt'
