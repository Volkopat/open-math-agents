import OMAStatements.S_oeis_a389591

-- Problem: A389591: Sum of the divisors r of n such that r is not greater than twice the adjacent previous divisor of n.
-- Credit: original proof by @agchua (#19239).
-- Rewrite the complementary divisor predicate before combining the two filtered sums.
-- Proof idea: for a divisor r of n with previous divisor p (p = 0 for r = 1), r is not counted
-- in a(n) iff r = 1 or r > 2p, and this holds iff r is odd and no divisor d has d < r < 2d:
-- an even r with r > 2p would have the divisor r/2 strictly between p and r, and an odd r with
-- r <= 2p has r < 2p. So sigma(n) splits into the sums defining a(n) and A379379(n).

open OMA.S_oeis_a389591 in
theorem OMA.solution : type_of% @OMA.S_oeis_a389591.main := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have key : ∀ r ∈ Nat.divisors n,
      (¬ (1 < r ∧ r ≤ 2 * prevDiv n r) ↔
        (Odd r ∧ ∀ d ∈ Nat.divisors n, ¬ (d < r ∧ r < 2 * d))) := by
    intro r hr
    have hrpos : 0 < r := Nat.pos_of_mem_divisors hr
    have hle : ∀ d ∈ Nat.divisors n, d < r → d ≤ prevDiv n r := by
      intro d hd hdr
      unfold prevDiv
      exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨hd, hdr⟩)
    constructor
    · intro h
      by_cases h1 : r = 1
      · subst h1
        refine ⟨odd_one, ?_⟩
        rintro d hd ⟨hd1, _⟩
        have hdpos := Nat.pos_of_mem_divisors hd
        omega
      · have h2 : 2 * prevDiv n r < r := by
          by_contra hc
          exact h ⟨by omega, by omega⟩
        refine ⟨?_, ?_⟩
        · rcases Nat.even_or_odd r with ⟨m, hm⟩ | ho
          · exfalso
            have hmr : m ∣ r := ⟨2, by omega⟩
            have hmd : m ∈ Nat.divisors n :=
              Nat.mem_divisors.mpr ⟨Nat.dvd_trans hmr (Nat.mem_divisors.mp hr).1, hn0⟩
            have h3 := hle m hmd (by omega)
            omega
          · exact ho
        · rintro d hd ⟨hd1, hd2⟩
          have h3 := hle d hd hd1
          omega
    · rintro ⟨ho, hno⟩ ⟨h1, h2⟩
      have hne : ((Nat.divisors n).filter (fun d => d < r)).Nonempty :=
        ⟨1, Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr hn0, h1⟩⟩
      obtain ⟨p, hp, hpeq⟩ := Finset.exists_mem_eq_sup _ hne id
      rw [Finset.mem_filter] at hp
      have hpv : prevDiv n r = p := hpeq
      rw [hpv] at h2
      have h3 := hno p hp.1
      have h4 : ¬ r < 2 * p := fun h => h3 ⟨hp.2, h⟩
      rcases ho with ⟨k, hk⟩
      omega
  have hsig : (ArithmeticFunction.sigma 1 n : ℕ) = a n + a379379 n := by
    rw [ArithmeticFunction.sigma_one_apply]
    unfold a a379379
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    simp_rw [← key r hr]
    by_cases hP : 1 < r ∧ r ≤ 2 * prevDiv n r <;> simp [hP]
  rw [hsig, Nat.cast_add]
  ring
