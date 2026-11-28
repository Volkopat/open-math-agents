import OMAReductions.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H2_R1_H2_R1

-- An odd perfect number not divisible by 3 has at least seven distinct prime factors.
-- Original Lean proof of a classical bound (Sylvester 1888 proves eight by a finer argument). The divisor sum
-- satisfies sigma(n) * prod (p - 1) <= n * prod p over the primes dividing n, so a perfect n needs
-- 2 * prod (p - 1) <= prod p; the primes are coprime to 6, and for at most six distinct numbers >= 5 coprime
-- to 6 the product of p / (p - 1) is at most (5/4)(7/6)(11/10)(13/12)(17/16)(19/18) < 2.
-- A classical case of the odd perfect number problem, not progress on it.

namespace OMA.OPN7

open ArithmeticFunction Finset

lemma geom' (c : ℕ) : ∀ i : ℕ, (∑ k ∈ range (i + 1), (c + 1) ^ k) * c + 1 = (c + 1) ^ (i + 1) := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    have e : (c + 1) ^ (i + 1 + 1) = (c + 1) ^ (i + 1) * (c + 1) := pow_succ _ _
    rw [Finset.sum_range_succ, e]
    nlinarith [ih]

lemma geom (p : ℕ) (hp : 1 ≤ p) (i : ℕ) : (∑ k ∈ range (i + 1), p ^ k) * (p - 1) + 1 = p ^ (i + 1) := by
  obtain ⟨c, rfl⟩ : ∃ c, p = c + 1 := ⟨p - 1, by omega⟩
  simpa using geom' c i

/-- The abundancy bound: `σ(n) * ∏ (p - 1) ≤ n * ∏ p` over the primes dividing `n`. -/
lemma sigma_bound (n : ℕ) :
    sigma 1 n * ∏ p ∈ n.primeFactors, (p - 1) ≤ n * ∏ p ∈ n.primeFactors, p := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    rw [Nat.primeFactors_prime_pow hk.ne' hp, Finset.prod_singleton, Finset.prod_singleton,
      sigma_one_apply_prime_pow hp]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h := geom p hp.one_lt.le (j + 1)
    have h2 : p ^ (j + 1 + 1) = p ^ (j + 1) * p := pow_succ p (j + 1)
    omega
  | zero => simp
  | one => simp
  | coprime a b ha hb hab iha ihb =>
    rw [isMultiplicative_sigma.map_mul_of_coprime hab, hab.primeFactors_mul,
      Finset.prod_union hab.disjoint_primeFactors, Finset.prod_union hab.disjoint_primeFactors]
    calc sigma 1 a * sigma 1 b * ((∏ p ∈ a.primeFactors, (p - 1)) * ∏ p ∈ b.primeFactors, (p - 1))
        = (sigma 1 a * ∏ p ∈ a.primeFactors, (p - 1)) *
            (sigma 1 b * ∏ p ∈ b.primeFactors, (p - 1)) := by ring
      _ ≤ (a * ∏ p ∈ a.primeFactors, p) * (b * ∏ p ∈ b.primeFactors, p) :=
          Nat.mul_le_mul iha ihb
      _ = a * b * ((∏ p ∈ a.primeFactors, p) * ∏ p ∈ b.primeFactors, p) := by ring

/-- For distinct numbers `≥ 5` coprime to `6`: `∏ p / (p - 1)` is at most the product over the first
`r` such numbers `5, 7, 11, 13, 17, 19, ...`, the `j`-th being `6 * (j / 2) + 5 + 2 * (j % 2)`. -/
lemma six_prod_bound (s : Finset ℕ) :
    (∀ p ∈ s, 5 ≤ p ∧ (p % 6 = 1 ∨ p % 6 = 5)) →
    (∏ j ∈ range s.card, (6 * (j / 2) + 4 + 2 * (j % 2))) * ∏ p ∈ s, p ≤
      (∏ j ∈ range s.card, (6 * (j / 2) + 4 + 2 * (j % 2) + 1)) * ∏ p ∈ s, (p - 1) := by
  induction s using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a s ha ih =>
    intro hs
    have hans : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hs' : ∀ p ∈ s, 5 ≤ p ∧ (p % 6 = 1 ∨ p % 6 = 5) :=
      fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have ha3 := hs a (Finset.mem_insert_self a s)
    have ih' := ih hs'
    have hmap : ∀ x ∈ s, 2 * ((x - 5) / 6) + x % 6 % 5 ∈ range (2 * ((a - 5) / 6) + a % 6 % 5) := by
      intro x hx
      have h1 := hs' x hx
      have h2 := ha x hx
      rw [Finset.mem_range]
      omega
    have hinj : Set.InjOn (fun x : ℕ => 2 * ((x - 5) / 6) + x % 6 % 5) (s : Set ℕ) := by
      intro x hx y hy hxy
      have h1 := hs' x hx
      have h2 := hs' y hy
      simp only at hxy
      omega
    have hcard : s.card ≤ 2 * ((a - 5) / 6) + a % 6 % 5 := by
      have h := Finset.card_le_card_of_injOn (fun x : ℕ => 2 * ((x - 5) / 6) + x % 6 % 5) hmap hinj
      rwa [Finset.card_range] at h
    have hstep : (6 * (s.card / 2) + 4 + 2 * (s.card % 2)) * a ≤
        (6 * (s.card / 2) + 4 + 2 * (s.card % 2) + 1) * (a - 1) := by
      obtain ⟨d, rfl⟩ : ∃ d, a = d + 1 := ⟨a - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have h3 : 6 * (s.card / 2) + 4 + 2 * (s.card % 2) ≤ d := by omega
      nlinarith
    rw [Finset.card_insert_of_notMem hans, Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_insert hans, Finset.prod_insert hans]
    calc (∏ j ∈ range s.card, (6 * (j / 2) + 4 + 2 * (j % 2))) *
          (6 * (s.card / 2) + 4 + 2 * (s.card % 2)) * (a * ∏ p ∈ s, p)
        = ((∏ j ∈ range s.card, (6 * (j / 2) + 4 + 2 * (j % 2))) * ∏ p ∈ s, p) *
            ((6 * (s.card / 2) + 4 + 2 * (s.card % 2)) * a) := by ring
      _ ≤ ((∏ j ∈ range s.card, (6 * (j / 2) + 4 + 2 * (j % 2) + 1)) * ∏ p ∈ s, (p - 1)) *
            ((6 * (s.card / 2) + 4 + 2 * (s.card % 2) + 1) * (a - 1)) := Nat.mul_le_mul ih' hstep
      _ = (∏ j ∈ range s.card, (6 * (j / 2) + 4 + 2 * (j % 2) + 1)) *
            (6 * (s.card / 2) + 4 + 2 * (s.card % 2) + 1) * ((a - 1) * ∏ p ∈ s, (p - 1)) := by
          ring

/-- An odd perfect number not divisible by `3` has at least seven distinct prime factors. -/
theorem seven (n : ℕ) (hperf : Nat.Perfect n) (hodd : Odd n) (h3 : ¬ 3 ∣ n)
    (hc : n.primeFactors.card ≤ 6) : False := by
  have hpos : 0 < n := hperf.2
  have hs : sigma 1 n = 2 * n := by
    rw [sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul hpos).mp hperf
  have hbound := sigma_bound n
  rw [hs] at hbound
  have hkey : 2 * ∏ p ∈ n.primeFactors, (p - 1) ≤ ∏ p ∈ n.primeFactors, p := by
    have h2 : n * (2 * ∏ p ∈ n.primeFactors, (p - 1)) ≤ n * ∏ p ∈ n.primeFactors, p := by
      calc n * (2 * ∏ p ∈ n.primeFactors, (p - 1)) = 2 * n * ∏ p ∈ n.primeFactors, (p - 1) := by ring
        _ ≤ _ := hbound
    exact Nat.le_of_mul_le_mul_left h2 hpos
  have hge : ∀ p ∈ n.primeFactors, 5 ≤ p ∧ (p % 6 = 1 ∨ p % 6 = 5) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hpo : p % 2 = 1 := by
      obtain ⟨e, hcb⟩ := hodd
      obtain ⟨d, hd⟩ := hpd
      by_contra hne
      have hpe : p % 2 = 0 := by omega
      have : (p * d) % 2 = 0 := by rw [Nat.mul_mod, hpe]; simp
      omega
    have hp3 : p % 3 ≠ 0 := by
      intro h0
      exact h3 ((Nat.dvd_of_mod_eq_zero h0).trans hpd)
    have h2 := hpp.two_le
    have hp3' : p ≠ 3 := fun e => hp3 (by rw [e])
    exact ⟨by omega, by omega⟩
  have hsix := six_prod_bound n.primeFactors hge
  have hQ : 0 < ∏ p ∈ n.primeFactors, (p - 1) :=
    Finset.prod_pos fun p hp => by have := (hge p hp).1; omega
  have hfinal : 2 * (∏ j ∈ range n.primeFactors.card, (6 * (j / 2) + 4 + 2 * (j % 2))) ≤
      ∏ j ∈ range n.primeFactors.card, (6 * (j / 2) + 4 + 2 * (j % 2) + 1) := by
    have h6 : (∏ q ∈ n.primeFactors, (q - 1)) *
        (2 * ∏ j ∈ range n.primeFactors.card, (6 * (j / 2) + 4 + 2 * (j % 2))) ≤
        (∏ q ∈ n.primeFactors, (q - 1)) *
          ∏ j ∈ range n.primeFactors.card, (6 * (j / 2) + 4 + 2 * (j % 2) + 1) := by
      calc (∏ q ∈ n.primeFactors, (q - 1)) *
            (2 * ∏ j ∈ range n.primeFactors.card, (6 * (j / 2) + 4 + 2 * (j % 2)))
          = (∏ j ∈ range n.primeFactors.card, (6 * (j / 2) + 4 + 2 * (j % 2))) *
              (2 * ∏ q ∈ n.primeFactors, (q - 1)) := by ring
        _ ≤ (∏ j ∈ range n.primeFactors.card, (6 * (j / 2) + 4 + 2 * (j % 2))) *
              ∏ q ∈ n.primeFactors, q := Nat.mul_le_mul_left _ hkey
        _ ≤ (∏ j ∈ range n.primeFactors.card, (6 * (j / 2) + 4 + 2 * (j % 2) + 1)) *
              ∏ q ∈ n.primeFactors, (q - 1) := hsix
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left h6 hQ
  generalize n.primeFactors.card = r at hc hfinal
  interval_cases r <;> simp [Finset.prod_range_succ] at hfinal

end OMA.OPN7

theorem OMA.solution : OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H2_R1_H2_R1.H1 := by
  intro n hperf hodd hc hmem
  have h3 : ¬ 3 ∣ n := by
    intro h3
    have hle : n.minFac ≤ 3 := Nat.minFac_le_of_dvd (by norm_num) h3
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    omega
  exact OMA.OPN7.seven n hperf hodd h3 (by omega)
