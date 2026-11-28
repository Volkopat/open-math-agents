import OMAStatements.S_oeis_a191107

-- Proof of the statement in #27859 (statement by @ivillar). Credit for the proof: @bnb9001
-- With g(m) = binary digits of m read in base 3 (g(2m) = 3g(m), g(2m+1) = 3g(m)+1), the generated
-- set is exactly {3 g(m) + 1}; g is strictly increasing, so the n-th term is 3 g(n-1) + 1.

namespace OMA_OEIS_A191107_Proof

open OMA.S_oeis_a191107

open Finset

/-- binary digits read in base 3 -/
def g (m : ℕ) : ℕ := Nat.ofDigits 3 (Nat.digits 2 m)

theorem g_even (m : ℕ) : g (2 * m) = 3 * g m := by
  unfold g
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp
  · rw [Nat.digits_def' (by norm_num) (by omega), show 2 * m % 2 = 0 by omega,
      show 2 * m / 2 = m by omega, Nat.ofDigits_cons]
    ring

theorem g_odd (m : ℕ) : g (2 * m + 1) = 3 * g m + 1 := by
  unfold g
  rw [Nat.digits_def' (by norm_num) (by omega), show (2 * m + 1) % 2 = 1 by omega,
    show (2 * m + 1) / 2 = m by omega, Nat.ofDigits_cons]
  ring

theorem g_succ (m : ℕ) : g m < g (m + 1) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
    · rw [g_even, g_odd]; omega
    · rw [g_odd, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, g_even]
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; simp [g]
      · have := ih k (by omega); omega

theorem f_strictMono : StrictMono (fun m => 3 * g m + 1) := by
  apply strictMono_nat_of_lt_succ
  intro m; have := g_succ m; show 3 * g m + 1 < 3 * g (m + 1) + 1; omega

theorem mem_iff (x : ℕ) : InA191107 x ↔ ∃ m, x = 3 * g m + 1 := by
  constructor
  · intro h
    induction h with
    | base => exact ⟨0, by simp [g]⟩
    | step1 _ ih =>
      obtain ⟨m, rfl⟩ := ih
      exact ⟨2 * m, by rw [g_even]; omega⟩
    | step2 _ ih =>
      obtain ⟨m, rfl⟩ := ih
      exact ⟨2 * m + 1, by rw [g_odd]⟩
  · rintro ⟨m, rfl⟩
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
      · rcases Nat.eq_zero_or_pos k with h | h
        · subst h; simpa [g] using InA191107.base
        · rw [g_even]
          have := InA191107.step1 (ih k (by omega))
          rwa [show 3 * (3 * g k + 1) - 2 = 3 * (3 * g k) + 1 by omega] at this
      · rw [g_odd]
        have := InA191107.step2 (ih k (by omega))
        rwa [show 3 * (3 * g k + 1) + 1 = 3 * (3 * g k + 1) + 1 from rfl] at this

theorem nth_eq (j : ℕ) : Nat.nth InA191107 j = 3 * g j + 1 := by
  classical
  have hp : InA191107 (3 * g j + 1) := (mem_iff _).mpr ⟨j, rfl⟩
  have hc : Nat.count InA191107 (3 * g j + 1) = j := by
    rw [Nat.count_eq_card_filter_range]
    have : (range (3 * g j + 1)).filter InA191107 = (range j).image (fun m => 3 * g m + 1) := by
      ext v
      simp only [mem_filter, mem_range, mem_image]
      constructor
      · rintro ⟨hv, ht⟩
        obtain ⟨i, rfl⟩ := (mem_iff v).mp ht
        exact ⟨i, f_strictMono.lt_iff_lt.mp hv, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨f_strictMono hi, (mem_iff _).mpr ⟨i, rfl⟩⟩
    rw [this, card_image_of_injective _ f_strictMono.injective, card_range]
  have := Nat.nth_count hp
  rwa [hc] at this

theorem stmt' :
    (∀ n : ℕ, 1 ≤ n → Nat.nth InA191107 (n - 1) = 3 * A003278 n - 2) ∧
    (∀ n : ℕ, 1 ≤ n → Nat.nth InA191107 (n - 1) = A003278 (2 * n - 1)) := by
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · rw [nth_eq]; unfold A003278; rw [show g (n - 1) = Nat.ofDigits 3 (Nat.digits 2 (n - 1)) from rfl]
    omega
  · rw [nth_eq]; unfold A003278
    rw [show 2 * n - 1 - 1 = 2 * (n - 1) by omega]
    have := g_even (n - 1)
    unfold g at this
    rw [this]; unfold g; ring

end OMA_OEIS_A191107_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a191107.main := OMA_OEIS_A191107_Proof.stmt'
