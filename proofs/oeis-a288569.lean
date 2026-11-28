import OMAStatements.S_oeis_a288569
import Mathlib.Tactic

namespace OMA.P_oeis_a288569

open OMA.S_oeis_a288569

private lemma a087207_one : a087207 1 = 0 := by
  simp [a087207]

private lemma count_prime_two : Nat.count Nat.Prime 2 = 0 := by
  decide

private lemma count_prime_pos_of_gt_two {p : ℕ} (hp : 2 < p) :
    0 < Nat.count Nat.Prime p := by
  rw [Nat.count_eq_card_filter_range]
  apply Finset.card_pos.mpr
  refine ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp, Nat.prime_two⟩⟩

private lemma a087207_two_pow (k : ℕ) (hk : 1 ≤ k) : a087207 (2 ^ k) = 1 := by
  unfold a087207
  rw [Nat.primeFactors_pow 2 (by omega), Nat.Prime.primeFactors Nat.prime_two]
  simp [count_prime_two]

private lemma a087207_prime (p : ℕ) (hp : p.Prime) :
    a087207 p = 2 ^ (Nat.count Nat.Prime p) := by
  unfold a087207
  rw [hp.primeFactors]
  simp

private lemma a087207_opposite_parity (n : ℕ) (hn : 1 ≤ n) :
    a087207 n % 2 = 1 - n % 2 := by
  have hn0 : n ≠ 0 := by omega
  have heven_sum : ∀ s : Finset ℕ, (∀ p ∈ s, 2 < p) → Even (∑ p ∈ s, 2 ^ (Nat.count Nat.Prime p)) := by
    intro s hs
    have h2dvd : 2 ∣ ∑ p ∈ s, 2 ^ (Nat.count Nat.Prime p) := by
      apply Finset.dvd_sum
      intro p hp
      have hpos := count_prime_pos_of_gt_two (hs p hp)
      exact dvd_pow_self 2 hpos.ne'
    exact even_iff_two_dvd.mpr h2dvd
  by_cases h2 : 2 ∣ n
  · have hmem : 2 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, hn0⟩
    have hsplit : a087207 n = 1 + ∑ p ∈ n.primeFactors.erase 2, 2 ^ (Nat.count Nat.Prime p) := by
      unfold a087207
      rw [← Finset.add_sum_erase _ _ hmem, count_prime_two, pow_zero]
    have hgt : ∀ p ∈ n.primeFactors.erase 2, 2 < p := by
      intro p hp
      rw [Finset.mem_erase] at hp
      have hpr := Nat.prime_of_mem_primeFactors hp.2
      have hge := hpr.two_le
      omega
    rcases heven_sum _ hgt with ⟨t, ht⟩
    rw [hsplit, ht]
    rcases h2 with ⟨q, rfl⟩
    omega
  · have hgt : ∀ p ∈ n.primeFactors, 2 < p := by
      intro p hp
      have hpr := Nat.prime_of_mem_primeFactors hp
      have hge := hpr.two_le
      have hne : p ≠ 2 := fun h => by
        subst h
        exact h2 (Nat.dvd_of_mem_primeFactors hp)
      omega
    rcases heven_sum _ hgt with ⟨t, ht⟩
    have ha : a087207 n = t + t := ht
    omega

private lemma iter_parity (n : ℕ) :
    ∀ s : ℕ, (∀ r < s, a087207^[r] n ≠ 0) → (a087207^[s] n) % 2 = (n + s) % 2 := by
  intro s
  induction s with
  | zero =>
    intro _
    simp
  | succ s ih =>
    intro hne
    have hprev_nz : a087207^[s] n ≠ 0 := hne s (Nat.lt_succ_self s)
    have hprev_par := ih (fun r hr => hne r (Nat.lt_succ_of_lt hr))
    rw [Function.iterate_succ_apply', a087207_opposite_parity _ (Nat.pos_of_ne_zero hprev_nz), hprev_par]
    omega

private lemma prove_main :
    (∀ k : ℕ, 1 ≤ k → ReachesZeroIn (2 ^ k) 2) ∧
    (∀ p : ℕ, p.Prime → Odd p → ReachesZeroIn p 3) ∧
    (∀ n t : ℕ, 1 < n → Odd n → ¬ n.Prime → ReachesZeroIn n t → Odd t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    refine ⟨?_, ?_⟩
    · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      rw [a087207_two_pow k hk, a087207_one]
    · intro s hs
      have hcases : s = 0 ∨ s = 1 := by omega
      rcases hcases with rfl | rfl
      · simp
      · simp only [Function.iterate_one]
        rw [a087207_two_pow k hk]
        decide
  · intro p hp hodd
    have hp2 : 2 < p := by
      have := hp.two_le
      rcases hodd with ⟨m, hm⟩
      omega
    have hcnt : 1 ≤ Nat.count Nat.Prime p := count_prime_pos_of_gt_two hp2
    refine ⟨?_, ?_⟩
    · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      rw [a087207_prime p hp, a087207_two_pow _ hcnt, a087207_one]
    · intro s hs
      have hcases : s = 0 ∨ s = 1 ∨ s = 2 := by omega
      rcases hcases with rfl | rfl | rfl
      · simp [hp.ne_zero]
      · simp only [Function.iterate_one]
        rw [a087207_prime p hp]
        exact pow_ne_zero _ (by decide)
      · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
        rw [a087207_prime p hp, a087207_two_pow _ hcnt]
        decide
  · intro n t _ hodd _ ⟨ht0, hne⟩
    have hpar := iter_parity n t hne
    rw [ht0] at hpar
    rcases hodd with ⟨m, rfl⟩
    rw [Nat.odd_iff]
    omega

end OMA.P_oeis_a288569

theorem OMA.solution : type_of% @OMA.S_oeis_a288569.main :=
  OMA.P_oeis_a288569.prove_main
