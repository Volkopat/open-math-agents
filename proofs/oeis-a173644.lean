import OMAStatements.S_oeis_a173644

-- Original Lean proof: @jleguina.

namespace OMA.S_oeis_a173644

lemma exists_m (n : ℕ) : ∃ m, 0 < m ∧ IsSquare (n ^ 2 + 7 * m) :=
  ⟨2 * n + 7, by omega, ⟨n + 7, by ring⟩⟩


/-- The least `d ≥ 1` with `7 ∣ 2n + d`. -/
def d (n : ℕ) : ℕ := 7 - (2 * n) % 7

lemma d_dvd (n : ℕ) : 7 ∣ 2 * n + d n := by
  unfold d; omega

lemma d_pos (n : ℕ) : 0 < d n := by unfold d; omega

lemma lower (n m : ℕ) (hm : 0 < m) (hsq : IsSquare (n ^ 2 + 7 * m)) :
    d n * (2 * n + d n) ≤ 7 * m := by
  obtain ⟨s, hs⟩ := hsq
  have hsn : n < s := by nlinarith
  obtain ⟨e, rfl⟩ : ∃ e, s = n + e := ⟨s - n, by omega⟩
  have h7 : 7 * m = e * (2 * n + e) := by nlinarith
  have hdvd : 7 ∣ e * (2 * n + e) := ⟨m, h7.symm⟩
  have hed : d n ≤ e := by
    unfold d
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp hdvd with h | h <;> omega
  rw [h7]
  exact Nat.mul_le_mul hed (by omega)

/-- The closed form `7 a(n) = d(n) (2n + d(n))`. -/
lemma closed (n : ℕ) : 7 * a n = d n * (2 * n + d n) := by
  obtain ⟨q, hq⟩ := d_dvd n
  have hq0 : 0 < q := by have := d_pos n; omega
  have hsq : IsSquare (n ^ 2 + 7 * (d n * q)) := ⟨n + d n, by nlinarith⟩
  have hle : a n ≤ d n * q := Nat.find_min' (exists_m n) ⟨Nat.mul_pos (d_pos n) hq0, hsq⟩
  have hspec := Nat.find_spec (exists_m n)
  have hge := lower n (a n) hspec.1 hspec.2
  rw [hq] at hge ⊢
  have : 7 * a n ≤ 7 * (d n * q) := Nat.mul_le_mul_left 7 hle
  nlinarith

lemma d_periodic (N : ℕ) : d (N + 7) = d N := by unfold d; omega

/-- The conjectured recurrence, for every `n ≥ 15`. -/
theorem conjecture (n : ℕ) (hn : 15 ≤ n) : (a n : ℤ) = 2 * a (n - 7) - a (n - 14) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 14 := ⟨n - 14, by omega⟩
  simp only [show N + 14 - 7 = N + 7 by omega, Nat.add_sub_cancel]
  have c0 := closed N
  have c7 := closed (N + 7)
  have c14 := closed (N + 7 + 7)
  rw [d_periodic] at c7 c14
  rw [d_periodic] at c14
  zify at c0 c7 c14
  linarith

/-- Controls: the first listed terms 5, 3, 1, 12, 8, 4, 21 (`7 a(n) = d (2n + d)`). -/
example : d 1 * (2 * 1 + d 1) = 7 * 5 ∧ d 2 * (2 * 2 + d 2) = 7 * 3 ∧
    d 3 * (2 * 3 + d 3) = 7 * 1 ∧ d 4 * (2 * 4 + d 4) = 7 * 12 ∧
    d 7 * (2 * 7 + d 7) = 7 * 21 := by
  decide

end OMA.S_oeis_a173644

theorem OMA.solution : type_of% @OMA.S_oeis_a173644.main :=
  fun n hn => OMA.S_oeis_a173644.conjecture n hn
