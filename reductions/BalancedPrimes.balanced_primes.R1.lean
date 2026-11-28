import FormalConjectures.Wikipedia.BalancedPrimes

/-!
Compare the number of prime triples with gap six with the number of those
triples that have another prime between the endpoints.
-/

namespace OMA.R_BalancedPrimes_balanced_primes_R1

-- The number of prime triples with gap six, scaled by k^4 / 2^k, is unbounded.
def H1 : Prop :=
  ∀ B K : ℕ, ∃ k ≥ K, B * 2 ^ k ≤ k ^ 4 *
    ((Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
      (fun p => Nat.Prime p ∧ Nat.Prime (p + 6) ∧ Nat.Prime (p + 12))).card

-- An upper-bound sieve for four prime shifts bounds the number with an extra prime.
def H2 : Prop :=
  ∃ B K : ℕ, ∀ k ≥ K, k ^ 4 *
    ((Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
      (fun p => Nat.Prime p ∧ Nat.Prime (p + 6) ∧ Nat.Prime (p + 12) ∧
        ((Finset.Ioo p (p + 12)).filter
          (fun q => q ≠ p + 6 ∧ Nat.Prime q)).Nonempty)).card ≤ B * 2 ^ k

theorem consecutiveIndex (p : ℕ) (hp : Nat.Prime p)
    (h6 : Nat.Prime (p + 6)) (h12 : Nat.Prime (p + 12))
    (hbetween : ∀ q : ℕ, p < q → q < p + 12 → Nat.Prime q → q = p + 6) :
    ∃ n : ℕ, Nat.nth Nat.Prime n = p ∧
      Nat.Prime ((Nat.nth Nat.Prime n + Nat.nth Nat.Prime (n + 2)) / 2) := by
  have hinf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  let n := Nat.count Nat.Prime p
  have heq : Nat.nth Nat.Prime n = p := Nat.nth_count hp
  have hleast (a b : ℕ) (hb : Nat.Prime b) (hab : Nat.nth Nat.Prime a < b) :
      Nat.nth Nat.Prime (a + 1) ≤ b := by
    apply le_of_not_gt
    intro hlt
    exact (not_le_of_gt hab) (Nat.le_nth_of_lt_nth_succ hlt hb)
  have hn1_lower : p < Nat.nth Nat.Prime (n + 1) := by
    rw [← heq]
    exact (Nat.nth_lt_nth hinf).2 (by omega)
  have hn1_upper : Nat.nth Nat.Prime (n + 1) ≤ p + 6 :=
    hleast n (p + 6) h6 (by omega)
  have hn1 : Nat.nth Nat.Prime (n + 1) = p + 6 :=
    hbetween _ hn1_lower (by omega) (Nat.nth_mem_of_infinite hinf _)
  have hn2_lower : p + 6 < Nat.nth Nat.Prime (n + 2) := by
    rw [← hn1]
    exact (Nat.nth_lt_nth hinf).2 (by omega)
  have hn2_upper : Nat.nth Nat.Prime (n + 2) ≤ p + 12 := by
    exact hleast (n + 1) (p + 12) h12 (by omega)
  have hn2 : Nat.nth Nat.Prime (n + 2) = p + 12 := by
    refine le_antisymm hn2_upper (le_of_not_gt ?_)
    intro hlt
    have hm := hbetween (Nat.nth Nat.Prime (n + 2)) (by omega) hlt
      (Nat.nth_mem_of_infinite hinf _)
    omega
  have hmid : (p + (p + 12)) / 2 = p + 6 := by omega
  refine ⟨n, heq, ?_⟩
  rw [heq, hn2, hmid]
  exact h6

theorem main : H1 → H2 → type_of% @BalancedPrimes.balanced_primes := by
  intro lower upper
  obtain ⟨B, K, upper⟩ := upper
  have prime_eq : (Prime : ℕ → Prop) = Nat.Prime :=
    funext fun _ => propext Nat.prime_iff.symm
  rw [prime_eq]
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  let cutoff := Nat.nth Nat.Prime N + 1
  obtain ⟨k, hk, hlower⟩ := lower (B + 1) (max K cutoff)
  let window := Finset.Ico (2 ^ k) (2 ^ (k + 1))
  let triples := window.filter
    (fun p => Nat.Prime p ∧ Nat.Prime (p + 6) ∧ Nat.Prime (p + 12))
  let spoiled := window.filter
    (fun p => Nat.Prime p ∧ Nat.Prime (p + 6) ∧ Nat.Prime (p + 12) ∧
      ((Finset.Ioo p (p + 12)).filter
        (fun q => q ≠ p + 6 ∧ Nat.Prime q)).Nonempty)
  have hupper : k ^ 4 * spoiled.card ≤ B * 2 ^ k :=
    upper k ((le_max_left K cutoff).trans hk)
  have hnsub : ¬ triples ⊆ spoiled := by
    intro hsub
    have hcards := Nat.mul_le_mul_left (k ^ 4) (Finset.card_le_card hsub)
    have hbound : (B + 1) * 2 ^ k ≤ B * 2 ^ k :=
      hlower.trans (hcards.trans hupper)
    have hpos : 0 < (2 : ℕ) ^ k := Nat.two_pow_pos k
    rw [Nat.add_mul, Nat.one_mul] at hbound
    omega
  obtain ⟨p, hp, hnot⟩ := Finset.not_subset.mp hnsub
  obtain ⟨hwindow, hprime, h6, h12⟩ := Finset.mem_filter.mp hp
  have hbetween : ∀ q : ℕ, p < q → q < p + 12 → Nat.Prime q → q = p + 6 := by
    intro q hleft hright hprimeq
    by_contra hne
    apply hnot
    dsimp only [spoiled]
    exact Finset.mem_filter.mpr
      ⟨hwindow, hprime, h6, h12, q,
        Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨hleft, hright⟩, hne, hprimeq⟩⟩
  obtain ⟨n, hn, hmid⟩ := consecutiveIndex p hprime h6 h12 hbetween
  have hcutoff : cutoff ≤ p :=
    ((le_max_right K cutoff).trans hk).trans
      (Nat.lt_two_pow_self.le.trans (Finset.mem_Ico.mp hwindow).1)
  have hbefore : Nat.nth Nat.Prime N < Nat.nth Nat.Prime n := by
    rw [hn]
    exact hcutoff
  have hNn := (Nat.nth_lt_nth Nat.infinite_setOfPred_prime).1 hbefore
  exact (not_le_of_gt hNn) (hN hmid)

end OMA.R_BalancedPrimes_balanced_primes_R1
