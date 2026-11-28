import OMAStatements.S_oeis_a007755

-- Problem: OEIS A007755, Shapiro's conjecture that the least start of a totient
-- trajectory of given length is prime.
-- Disproof: the least start for n = 13 is 2329 = 17 * 137, which is composite
-- (C. R. Greathouse IV, OEIS A007755, Oct 28 2011: a(13) is composite).
-- Lower bound: an even v below 2^(s+1) reaches 1 after s steps, since the totient of an
-- even number is at most half of it and is again even or 1; this settles all m < 2329
-- except the odd m in [2049, 2328], which are evaluated directly.

namespace OMA.A007755Proof

open OMA.S_oeis_a007755

lemma half : ∀ n : ℕ, Nat.totient (2 * n) ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd n with he | ho
    · rw [Nat.totient_two_mul_of_even he]
      obtain ⟨k, rfl⟩ := he
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        simp
      · have := ih k (by omega)
        rw [← two_mul] at *
        omega
    · rw [Nat.totient_two_mul_of_odd ho]
      exact Nat.totient_le n

lemma reach : ∀ s v : ℕ, 0 < v → (v = 1 ∨ Even v) → v < 2 ^ (s + 1) →
    (Nat.totient^[s]) v = 1
  | 0, v, h0, _, h => by
    simp only [zero_add, pow_one] at h
    simp only [Function.iterate_zero, id_eq]
    omega
  | s + 1, v, h0, hv, h => by
    rw [Function.iterate_succ_apply]
    rcases hv with rfl | ⟨k, rfl⟩
    · rw [Nat.totient_one]
      exact reach s 1 one_pos (Or.inl rfl) (Nat.one_lt_two_pow (by omega))
    · have hk : Nat.totient (k + k) ≤ k := by
        rw [← two_mul]
        exact half k
      have hpos : 0 < Nat.totient (k + k) := Nat.totient_pos.2 h0
      have hlt : Nat.totient (k + k) < 2 ^ (s + 1) := by
        rw [pow_succ] at h
        omega
      apply reach s _ hpos _ hlt
      by_cases h2 : 2 < k + k
      · exact Or.inr (Nat.totient_even h2)
      · left
        have : k = 1 := by omega
        subst this
        decide

lemma odd_big : ∀ m < 2329, 2049 ≤ m → m % 2 = 1 → (Nat.totient^[11]) m = 1 := by
  decide +kernel

lemma below (m : ℕ) (h0 : 0 < m) (h : m < 2329) : (Nat.totient^[11]) m = 1 := by
  rcases Nat.even_or_odd m with he | ho
  · exact reach 11 m h0 (Or.inr he) (by norm_num; omega)
  · by_cases h1 : m = 1
    · subst h1
      exact reach 11 1 h0 (Or.inl rfl) (by norm_num)
    · by_cases hb : 2049 ≤ m
      · exact odd_big m h hb (Nat.odd_iff.1 ho)
      · rw [Function.iterate_succ_apply]
        have hlt : Nat.totient m < m := Nat.totient_lt m (by omega)
        have hmod := Nat.odd_iff.1 ho
        have h3 : 2 < m := by omega
        exact reach 10 (Nat.totient m) (Nat.totient_pos.2 h0)
          (Or.inr (Nat.totient_even h3)) (by norm_num; omega)

lemma mem : 2329 ∈ starts 13 := by
  refine ⟨by norm_num, ?_, ?_⟩ <;> decide +kernel

lemma least : IsLeast (starts 13) 2329 := by
  refine ⟨mem, fun m hm => ?_⟩
  by_contra hlt
  exact hm.2.2 (below m hm.1 (by omega))

end OMA.A007755Proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a007755.main) := by
  intro h
  have hp := h 13 (by norm_num) 2329 OMA.A007755Proof.least
  exact absurd hp (by norm_num)
