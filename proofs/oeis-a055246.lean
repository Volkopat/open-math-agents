import OMAStatements.S_oeis_a055246
import Mathlib

namespace OMA.S_oeis_a055246

def f (t : ℕ) : ℕ := Nat.ofDigits 3 (Nat.digits 2 t)

lemma f_zero : f 0 = 0 := by simp [f]

lemma f_double (s : ℕ) : f (2 * s) = 3 * f s := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp [f_zero]
  · unfold f
    rw [Nat.digits_def' (by norm_num) (by omega)]
    simp [Nat.ofDigits_cons]

lemma f_succ_double (s : ℕ) : f (2 * s + 1) = 3 * f s + 1 := by
  unfold f
  rw [Nat.digits_def' (by norm_num) (by omega)]
  have : (2 * s + 1) / 2 = s := by omega
  simp [Nat.ofDigits_cons, this]
  ring

lemma gen_f (t : ℕ) : Gen (6 * f t + 1) := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simpa [f_zero] using Gen.one
    · obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' t
      · rw [f_double]
        have := Gen.f _ (ih s (by omega))
        have e : 3 * (6 * f s + 1) - 2 = 6 * (3 * f s) + 1 := by omega
        rwa [e] at this
      · rw [f_succ_double]
        have := Gen.g _ (ih s (by omega))
        have e : 3 * (6 * f s + 1) + 4 = 6 * (3 * f s + 1) + 1 := by omega
        rwa [e] at this

theorem sol : type_of% @main := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hn, rfl⟩
    have : a n = 6 * f (n - 1) + 1 := rfl
    rw [this]
    exact gen_f _
  · intro h
    have : ∃ t, x = 6 * f t + 1 := by
      induction h with
      | one => exact ⟨0, by simp [f_zero]⟩
      | f x _ ih =>
        obtain ⟨t, rfl⟩ := ih
        exact ⟨2 * t, by rw [f_double]; omega⟩
      | g x _ ih =>
        obtain ⟨t, rfl⟩ := ih
        exact ⟨2 * t + 1, by rw [f_succ_double]; omega⟩
    obtain ⟨t, rfl⟩ := this
    exact ⟨t + 1, by omega, by show 6 * f (t + 1 - 1) + 1 = _; simp⟩

end OMA.S_oeis_a055246

theorem OMA.solution : type_of% @OMA.S_oeis_a055246.main := OMA.S_oeis_a055246.sol
