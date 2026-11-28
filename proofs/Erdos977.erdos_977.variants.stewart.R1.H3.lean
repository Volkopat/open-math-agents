import OMAReductions.R_Erdos977_erdos_977_variants_stewart_R1
import Mathlib

-- Credit: @dries
-- n / phi(n) = prod p/(p-1) over the distinct prime factors, and that product is at most
-- omega(n) + 1 (the i-th prime factor is at least i + 1). Each prime is at least 2, so
-- omega(n) is at most the base-two logarithm.
theorem OMA.solution : OMA.R_Erdos977_erdos_977_variants_stewart_R1.H3 := by
  intro n hn
  have h : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → ∏ p ∈ s, p ≤ (s.card + 1) * ∏ p ∈ s, (p - 1) := by
    intro s
    induction s using Finset.induction_on_max with
    | empty => simp
    | insert a s ha ih =>
      intro hp
      have hs := Finset.card_le_card fun q hq =>
        Finset.mem_Ico.2 ⟨(hp q (by simp [hq])).two_le, ha q hq⟩
      have h1 := ih fun q hq => hp q (by simp [hq])
      have h2 := (hp a (by simp)).two_le
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      have hn : b + 1 ∉ s := fun h => (ha _ h).false
      simp only [Finset.prod_insert hn, Finset.card_insert_of_notMem hn, Nat.card_Ico,
        Nat.add_sub_cancel] at *
      have : s.card + 1 ≤ b := by omega
      nlinarith [Nat.mul_le_mul_right (∏ p ∈ s, (p - 1)) this]
  have h3 := Nat.totient_mul_prod_primeFactors n
  have h4 : n.primeFactors.card ≤ Nat.log 2 n := Nat.le_log_of_pow_le one_lt_two
    (((Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le).trans'
      (by simp)).trans (Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)))
  refine Nat.le_of_mul_le_mul_right ?_ (Finset.prod_pos (s := n.primeFactors) fun p hp =>
    Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt)
  rw [← h3, mul_assoc]
  exact Nat.mul_le_mul_left _ ((h _ fun p => Nat.prime_of_mem_primeFactors).trans
    (Nat.mul_le_mul_right _ (by omega)))
