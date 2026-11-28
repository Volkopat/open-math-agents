import OMAStatements.S_oeis_a249969

namespace OMA.A249969Proof

lemma pron_mod (j : ℕ) : (j * j + j) % 100 ∈ [0, 2, 6, 10, 12, 20, 22, 30, 32, 40, 42, 50, 52, 56, 60, 62, 70, 72, 80, 82, 90, 92] := by
  have h : (j * j + j) % 100 = ((j % 100) * (j % 100) + j % 100) % 100 := by
    simp [Nat.add_mod, Nat.mul_mod]
  have hall : ∀ x < 100, (x * x + x) % 100 ∈ [0, 2, 6, 10, 12, 20, 22, 30, 32, 40, 42, 50, 52, 56, 60, 62, 70, 72, 80, 82, 90, 92] := by
    decide
  rw [h]
  exact hall _ (Nat.mod_lt _ (by norm_num))

lemma sq_mod (t : ℕ) : (t * t) % 100 ∈ [0, 1, 4, 9, 16, 21, 24, 25, 29, 36, 41, 44, 49, 56, 61, 64, 69, 76, 81, 84, 89, 96] := by
  have h : (t * t) % 100 = ((t % 100) * (t % 100)) % 100 := by
    simp [Nat.mul_mod]
  have hall : ∀ x < 100, (x * x) % 100 ∈ [0, 1, 4, 9, 16, 21, 24, 25, 29, 36, 41, 44, 49, 56, 61, 64, 69, 76, 81, 84, 89, 96] := by
    decide
  rw [h]
  exact hall _ (Nat.mod_lt _ (by norm_num))

lemma m_mod (m : ℕ) (h : (m * m) % 100 = 25) : m % 10 = 5 := by
  have h' : (m * m) % 100 = ((m % 100) * (m % 100)) % 100 := by simp [Nat.mul_mod]
  have hall : ∀ x < 100, (x * x) % 100 = 25 → x % 10 = 5 := by decide
  have := hall (m % 100) (Nat.mod_lt _ (by norm_num)) (by rw [← h', h])
  omega

lemma extend_eq (c s : ℕ) :
    Nat.ofDigits 10 ([5, 2] ++ Nat.digits 10 s ++ [c]) = 25 + 100 * (s + 10 ^ (Nat.digits 10 s).length * c) := by
  rw [Nat.ofDigits_append, Nat.ofDigits_append, Nat.ofDigits_digits]
  simp [Nat.ofDigits, pow_succ]
  ring

lemma key (c s : ℕ) (hc : c = 1 ∨ c = 3) (hs : IsSquare s)
    (he : IsSquare (Nat.ofDigits 10 ([5, 2] ++ Nat.digits 10 s ++ [c]))) :
    s % 100 = 0 ∨ s % 100 = 56 := by
  rw [extend_eq] at he
  obtain ⟨t, rfl⟩ := hs
  obtain ⟨m, hm⟩ := he
  have hlt : t * t < 10 ^ (Nat.digits 10 (t * t)).length :=
    Nat.lt_base_pow_length_digits (by norm_num)
  by_cases h0 : t * t = 0
  · left; rw [h0]
  by_cases hsmall : t * t < 10
  · have hdig : Nat.digits 10 (t * t) = [t * t] := Nat.digits_of_lt 10 (t * t) h0 hsmall
    rw [hdig] at hm
    simp only [List.length_singleton, pow_one] at hm
    have hm10 := m_mod m (by omega)
    obtain ⟨j, rfl⟩ : ∃ j, m = 10 * j + 5 := ⟨m / 10, by omega⟩
    have hXj : t * t + 10 * c = j * j + j := by nlinarith
    have ht : t < 4 := by nlinarith
    have hj7 : j < 7 := by rcases hc with rfl | rfl <;> nlinarith
    rcases hc with rfl | rfl <;> interval_cases t <;> interval_cases j <;> omega
  · have hd2 : 2 ≤ (Nat.digits 10 (t * t)).length := by
      by_contra h
      have h1 : (Nat.digits 10 (t * t)).length ≤ 1 := by omega
      have : 10 ^ (Nat.digits 10 (t * t)).length ≤ 10 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
      omega
    obtain ⟨e, he⟩ : ∃ e, (Nat.digits 10 (t * t)).length = e + 2 := ⟨_ - 2, (Nat.sub_add_cancel hd2).symm⟩
    rw [he, pow_add] at hm
    have hm10 := m_mod m (by omega)
    obtain ⟨j, rfl⟩ : ∃ j, m = 10 * j + 5 := ⟨m / 10, by omega⟩
    have hXj : t * t + 100 * (10 ^ e * c) = j * j + j := by nlinarith
    have hmod : (t * t) % 100 = (j * j + j) % 100 := by
      rw [← hXj]
      omega
    have h1 := pron_mod j
    have h2 := sq_mod t
    rw [← hmod] at h1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2
    omega

end OMA.A249969Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a249969.main := by
  intro k ⟨_, he⟩
  exact OMA.A249969Proof.key 3 (k ^ 2) (Or.inr rfl) ⟨k, sq k⟩ he
