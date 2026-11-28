import OMAStatements.S_oeis_a088987

-- Problem: A088987, primes between consecutive prime-indexed primes.
-- Credit: @bnb9001
-- Idea: the primes strictly between nth m and nth m' are exactly m' - m - 1 primes (prime
-- counting), so between k = prime (k + 1) - prime k - 1, which is odd once both primes are odd.

namespace OMA_A088987_Proof

open Finset OMA.S_oeis_a088987

lemma card_primes_between {m m' : ℕ} (h : m < m') :
    {p : ℕ | p.Prime ∧ Nat.nth Nat.Prime m < p ∧ p < Nat.nth Nat.Prime m'}.ncard = m' - m - 1 := by
  set a := Nat.nth Nat.Prime m
  set b := Nat.nth Nat.Prime m'
  have hab : a < b := Nat.nth_strictMono Nat.infinite_setOfPred_prime h
  have hset : {p : ℕ | p.Prime ∧ a < p ∧ p < b} = ↑((Ico (a + 1) b).filter Nat.Prime) := by
    ext p
    simp only [Set.mem_ofPred_eq, coe_filter, mem_Ico]
    constructor
    · rintro ⟨hp, h1, h2⟩; exact ⟨⟨h1, h2⟩, hp⟩
    · rintro ⟨⟨h1, h2⟩, hp⟩; exact ⟨hp, h1, h2⟩
  rw [hset, Set.ncard_coe_finset]
  have hsplit : (range b).filter Nat.Prime =
      (range (a + 1)).filter Nat.Prime ∪ (Ico (a + 1) b).filter Nat.Prime := by
    rw [← filter_union, range_eq_Ico, range_eq_Ico, Ico_union_Ico_eq_Ico (Nat.zero_le _) hab]
  have hdisj : Disjoint ((range (a + 1)).filter Nat.Prime) ((Ico (a + 1) b).filter Nat.Prime) := by
    apply disjoint_filter_filter
    rw [range_eq_Ico]
    exact Ico_disjoint_Ico_consecutive 0 (a + 1) b
  have hcb : Nat.count Nat.Prime b = m' := Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime m'
  have hca : Nat.count Nat.Prime (a + 1) = m + 1 := by
    rw [Nat.count_succ, Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime m,
      if_pos (Nat.prime_nth_prime m)]
  rw [Nat.count_eq_card_filter_range, hsplit, card_union_of_disjoint hdisj] at hcb
  rw [Nat.count_eq_card_filter_range] at hca
  have e1 : #((range (a + 1)).filter Nat.Prime) = m + 1 := by convert hca using 2
  omega

lemma prime_two_le (k : ℕ) : 2 ≤ prime k := (Nat.prime_nth_prime _).two_le

lemma prime_lt {k : ℕ} (hk : 1 ≤ k) : prime k < prime (k + 1) := by
  unfold prime
  apply Nat.nth_strictMono Nat.infinite_setOfPred_prime
  omega

lemma odd_prime {k : ℕ} (hk : 2 ≤ k) : Odd (prime k) := by
  unfold prime
  rcases (Nat.prime_nth_prime (k - 1)).eq_two_or_odd' with h | h
  · exfalso
    have := Nat.nth_strictMono Nat.infinite_setOfPred_prime (show 0 < k - 1 by omega)
    rw [h, Nat.nth_prime_zero_eq_two] at this
    omega
  · exact h

lemma between_eq {k : ℕ} (hk : 1 ≤ k) : between k = prime (k + 1) - prime k - 1 := by
  unfold between ppi
  have h1 := prime_two_le k
  have h2 := prime_lt hk
  conv_lhs => rw [show prime (prime k) = Nat.nth Nat.Prime (prime k - 1) from rfl,
    show prime (prime (k + 1)) = Nat.nth Nat.Prime (prime (k + 1) - 1) from rfl]
  rw [card_primes_between (by omega)]
  omega

end OMA_A088987_Proof

open OMA_A088987_Proof OMA.S_oeis_a088987 in
theorem OMA.solution : type_of% @OMA.S_oeis_a088987.main := by
  have p1 : prime 1 = 2 := by simp [prime, Nat.nth_prime_zero_eq_two]
  have p2 : prime 2 = 3 := by simp [prime, Nat.nth_prime_one_eq_three]
  have p3 : prime 3 = 5 := by simp [prime, Nat.nth_prime_two_eq_five]
  refine ⟨by simp [ppi, p1, p2], by simp [ppi, p2, p3], ?_, ?_⟩
  · rw [between_eq le_rfl, p1, p2]
  · intro k hk
    rw [between_eq (by omega)]
    have ho1 := odd_prime hk
    have ho2 := odd_prime (show 2 ≤ k + 1 by omega)
    have hlt := prime_lt (show 1 ≤ k by omega)
    obtain ⟨x, hx⟩ := ho1
    obtain ⟨y, hy⟩ := ho2
    refine ⟨y - x - 1, ?_⟩
    omega
