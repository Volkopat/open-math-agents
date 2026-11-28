import OMAReductions.R_OeisA108569_conjecture_R2_H1_R1_H2_R1

-- For an odd prime p with phi(2p - 1) = p - 1, the number m = 2p - 1 has at least seven distinct prime factors.
-- This is the case k = 2 of Lehmer's 1932 theorem; original Lean proof. The equation 2 phi(m) = m - 1 makes m
-- squarefree and composite, and then:
-- (Lehmer 1932) a composite n with phi(n) dividing n - 1 has at least seven distinct prime factors.
-- Original Lean proof of the classical theorem, for squarefree n (the non-squarefree case is immediate). Such an n
-- is odd and k = (n - 1) / phi(n) is at least 2. From phi(n) * prod p = n * prod (p - 1) one gets
-- k * prod (p - 1) < prod p over the primes dividing n. If 3 divides n, then n - 1 = 2 mod 3 and phi(n / 3) is
-- 0 or 1 mod 3, which forces k = 1 mod 3, so k >= 4, and the product of p / (p - 1) over at most six distinct odd
-- numbers is below 4. If 3 does not divide n, every prime factor is coprime to 6, and the product over at most
-- six such numbers is at most (5/4)(7/6)(11/10)(13/12)(17/16)(19/18) < 2.
-- A classical theorem, not progress on Lehmer's totient problem (fourteen prime factors are known to be needed).

namespace OMA.Lehmer7

open Finset

/-- For distinct numbers `≥ c + 1` of the parity of `c + 1`:
`∏ p / (p - 1) ≤ ∏_{j < r} (c + 2j + 1) / (c + 2j)`. -/
lemma odd_prod_bound_from (c : ℕ) (s : Finset ℕ) :
    (∀ p ∈ s, c + 1 ≤ p ∧ p % 2 = (c + 1) % 2) →
    (∏ j ∈ range s.card, (c + 2 * j)) * ∏ p ∈ s, p ≤
      (∏ j ∈ range s.card, (c + 2 * j + 1)) * ∏ p ∈ s, (p - 1) := by
  induction s using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a s ha ih =>
    intro hs
    have hans : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hs' : ∀ p ∈ s, c + 1 ≤ p ∧ p % 2 = (c + 1) % 2 :=
      fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have ha3 := hs a (Finset.mem_insert_self a s)
    have ih' := ih hs'
    have hmap : ∀ x ∈ s, (x - (c + 1)) / 2 ∈ range ((a - (c + 1)) / 2) := by
      intro x hx
      have h1 := hs' x hx
      have h2 := ha x hx
      rw [Finset.mem_range]
      omega
    have hinj : Set.InjOn (fun x : ℕ => (x - (c + 1)) / 2) (s : Set ℕ) := by
      intro x hx y hy hxy
      have h1 := hs' x hx
      have h2 := hs' y hy
      simp only at hxy
      omega
    have hcard : s.card ≤ (a - (c + 1)) / 2 := by
      have h := Finset.card_le_card_of_injOn (fun x : ℕ => (x - (c + 1)) / 2) hmap hinj
      rwa [Finset.card_range] at h
    have hstep : (c + 2 * s.card) * a ≤ (c + 2 * s.card + 1) * (a - 1) := by
      obtain ⟨d, rfl⟩ : ∃ d, a = d + 1 := ⟨a - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have h3 : c + 2 * s.card ≤ d := by omega
      nlinarith
    rw [Finset.card_insert_of_notMem hans, Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_insert hans, Finset.prod_insert hans]
    calc (∏ j ∈ range s.card, (c + 2 * j)) * (c + 2 * s.card) * (a * ∏ p ∈ s, p)
        = ((∏ j ∈ range s.card, (c + 2 * j)) * ∏ p ∈ s, p) * ((c + 2 * s.card) * a) := by ring
      _ ≤ ((∏ j ∈ range s.card, (c + 2 * j + 1)) * ∏ p ∈ s, (p - 1)) *
            ((c + 2 * s.card + 1) * (a - 1)) := Nat.mul_le_mul ih' hstep
      _ = (∏ j ∈ range s.card, (c + 2 * j + 1)) * (c + 2 * s.card + 1) *
            ((a - 1) * ∏ p ∈ s, (p - 1)) := by ring

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

/-- For a squarefree `m` not divisible by `3`, `φ(m)` is `0` or `1` modulo `3`. -/
lemma tot_mod_three (m : ℕ) (hsq : Squarefree m) (h3 : ¬ 3 ∣ m) :
    m.totient % 3 = 0 ∨ m.totient % 3 = 1 := by
  have hm0 : m ≠ 0 := hsq.ne_zero
  have hprod := Nat.prod_primeFactors_of_squarefree hsq
  have htot := Nat.totient_mul_prod_primeFactors m
  rw [hprod] at htot
  have hφ : m.totient = ∏ p ∈ m.primeFactors, (p - 1) := by
    have h : m * m.totient = m * ∏ p ∈ m.primeFactors, (p - 1) := by rw [mul_comm]; exact htot
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm0) h
  rw [hφ]
  apply Finset.prod_induction (fun p => p - 1) (fun x => x % 3 = 0 ∨ x % 3 = 1)
  · intro a b ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [Nat.mul_mod, ha, hb]
  · right; rfl
  · intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqd := Nat.dvd_of_mem_primeFactors hq
    have hq3 : q % 3 ≠ 0 := by
      intro h0
      have h3q : 3 ∣ q := Nat.dvd_of_mod_eq_zero h0
      have hq3' : q = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hqp).mp h3q).symm
      exact h3 (hq3' ▸ hqd)
    have h2 := hqp.two_le
    omega

/-- Lehmer 1932: a composite squarefree `n` with `φ(n) ∣ n - 1` has at least seven prime factors. -/
theorem lehmer_seven (n : ℕ) (hn : 1 < n) (hsq : Squarefree n) (hnp : ¬ n.Prime)
    (hc : n.primeFactors.card ≤ 6) : ¬ n.totient ∣ n - 1 := by
  intro hdvd
  have hn2 : n ≠ 2 := fun h => hnp (h ▸ Nat.prime_two)
  have hodd : n % 2 = 1 := by
    by_contra hne
    have heven : 2 ∣ n := by omega
    have h1 : 2 ∣ n.totient := (Nat.totient_even (by omega)).two_dvd
    have h2 : 2 ∣ n - 1 := h1.trans hdvd
    omega
  obtain ⟨k, hk⟩ := hdvd
  have hne : n.totient ≠ n - 1 := fun h => hnp ((Nat.totient_eq_iff_prime (by omega)).mp h)
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k
      · omega
      · omega
    · exact h
  have htot := Nat.totient_mul_prod_primeFactors n
  have hge : ∀ q ∈ n.primeFactors, q.Prime ∧ 3 ≤ q ∧ q % 2 = 1 := by
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqd := Nat.dvd_of_mem_primeFactors hq
    have hqo : q % 2 = 1 := by
      obtain ⟨d, hd⟩ := hqd
      by_contra hne
      have hqe : q % 2 = 0 := by omega
      have : (q * d) % 2 = 0 := by rw [Nat.mul_mod, hqe]; simp
      omega
    have h2 := hqp.two_le
    exact ⟨hqp, by omega, hqo⟩
  have hP : 0 < ∏ q ∈ n.primeFactors, q :=
    Finset.prod_pos fun q hq => by have := (hge q hq).2.1; omega
  have hQ : 0 < ∏ q ∈ n.primeFactors, (q - 1) :=
    Finset.prod_pos fun q hq => by have := (hge q hq).2.1; omega
  -- from j * φ(n) < n one gets j * ∏ (q - 1) < ∏ q
  have hbound : ∀ j : ℕ, j * n.totient < n →
      j * ∏ q ∈ n.primeFactors, (q - 1) < ∏ q ∈ n.primeFactors, q := by
    intro j hj
    have h1 : n * (j * ∏ q ∈ n.primeFactors, (q - 1)) = (j * n.totient) * ∏ q ∈ n.primeFactors, q := by
      calc n * (j * ∏ q ∈ n.primeFactors, (q - 1)) = j * (n * ∏ q ∈ n.primeFactors, (q - 1)) := by ring
        _ = j * (n.totient * ∏ q ∈ n.primeFactors, q) := by rw [htot]
        _ = _ := by ring
    have h3 : (j * n.totient) * ∏ q ∈ n.primeFactors, q < n * ∏ q ∈ n.primeFactors, q :=
      Nat.mul_lt_mul_of_pos_right hj hP
    rw [← h1] at h3
    exact Nat.lt_of_mul_lt_mul_left h3
  by_cases h3 : 3 ∣ n
  · -- then the quotient is 1 modulo 3, so at least 4
    obtain ⟨m, rfl⟩ := h3
    have hm3 : ¬ 3 ∣ m := by
      intro h
      obtain ⟨c, rfl⟩ := h
      have h9 : 3 * 3 ∣ 3 * (3 * c) := ⟨c, by ring⟩
      exact (Nat.squarefree_iff_prime_squarefree.mp hsq) 3 Nat.prime_three h9
    have hmsq : Squarefree m := hsq.of_mul_right
    have hφ : (3 * m).totient = 2 * m.totient := by
      rw [Nat.totient_mul_of_prime_of_not_dvd Nat.prime_three hm3]
    rw [hφ] at hk hbound
    have ht := tot_mod_three m hmsq hm3
    have hk4 : 4 ≤ k := by
      have hmod : (2 * m.totient * k) % 3 = 2 := by omega
      have e : 2 * m.totient * k = 2 * (m.totient * k) := by ring
      rw [e] at hmod
      have hmk : (m.totient * k) % 3 = 1 := by omega
      rw [Nat.mul_mod] at hmk
      rcases ht with ht | ht
      · rw [ht] at hmk
        simp at hmk
      · rw [ht] at hmk
        have hk3 : k % 3 = 1 := by
          have hlt : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
          interval_cases hkm : k % 3 <;> simp_all
        omega
    have hlt4 : 4 * (2 * m.totient) < 3 * m := by
      have h5 : 2 * m.totient * 4 ≤ 2 * m.totient * k := Nat.mul_le_mul_left _ hk4
      omega
    have hb := hbound 4 hlt4
    have hodd' := odd_prod_bound_from 2 (3 * m).primeFactors (fun p hp => by
      have h := hge p hp
      exact ⟨by omega, by omega⟩)
    have hfinal : 4 * (∏ j ∈ range (3 * m).primeFactors.card, (2 + 2 * j)) <
        ∏ j ∈ range (3 * m).primeFactors.card, (2 + 2 * j + 1) := by
      have hA : 0 < ∏ j ∈ range (3 * m).primeFactors.card, (2 + 2 * j) :=
        Finset.prod_pos fun j _ => by omega
      have h6 : (∏ q ∈ (3 * m).primeFactors, (q - 1)) *
          (4 * ∏ j ∈ range (3 * m).primeFactors.card, (2 + 2 * j)) <
          (∏ q ∈ (3 * m).primeFactors, (q - 1)) *
            ∏ j ∈ range (3 * m).primeFactors.card, (2 + 2 * j + 1) := by
        calc (∏ q ∈ (3 * m).primeFactors, (q - 1)) *
              (4 * ∏ j ∈ range (3 * m).primeFactors.card, (2 + 2 * j))
            = (∏ j ∈ range (3 * m).primeFactors.card, (2 + 2 * j)) *
                (4 * ∏ q ∈ (3 * m).primeFactors, (q - 1)) := by ring
          _ < (∏ j ∈ range (3 * m).primeFactors.card, (2 + 2 * j)) *
                ∏ q ∈ (3 * m).primeFactors, q := Nat.mul_lt_mul_of_pos_left hb hA
          _ ≤ (∏ j ∈ range (3 * m).primeFactors.card, (2 + 2 * j + 1)) *
                ∏ q ∈ (3 * m).primeFactors, (q - 1) := hodd'
          _ = _ := by ring
      exact Nat.lt_of_mul_lt_mul_left h6
    generalize (3 * m).primeFactors.card = r at hc hfinal
    interval_cases r <;> simp [Finset.prod_range_succ] at hfinal
  · -- all prime factors are coprime to 6
    have hlt2 : 2 * n.totient < n := by
      have h5 : n.totient * 2 ≤ n.totient * k := Nat.mul_le_mul_left _ hk2
      omega
    have hb := hbound 2 hlt2
    have hsix := six_prod_bound n.primeFactors (fun p hp => by
      have h := hge p hp
      have hp3 : p % 3 ≠ 0 := by
        intro h0
        have h3p : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
        exact h3 (h3p.trans (Nat.dvd_of_mem_primeFactors hp))
      have hp3' : p ≠ 3 := fun e => hp3 (by rw [e])
      exact ⟨by omega, by omega⟩)
    have hfinal : 2 * (∏ j ∈ range n.primeFactors.card, (6 * (j / 2) + 4 + 2 * (j % 2))) <
        ∏ j ∈ range n.primeFactors.card, (6 * (j / 2) + 4 + 2 * (j % 2) + 1) := by
      have hA : 0 < ∏ j ∈ range n.primeFactors.card, (6 * (j / 2) + 4 + 2 * (j % 2)) :=
        Finset.prod_pos fun j _ => by omega
      have h6 : (∏ q ∈ n.primeFactors, (q - 1)) *
          (2 * ∏ j ∈ range n.primeFactors.card, (6 * (j / 2) + 4 + 2 * (j % 2))) <
          (∏ q ∈ n.primeFactors, (q - 1)) *
            ∏ j ∈ range n.primeFactors.card, (6 * (j / 2) + 4 + 2 * (j % 2) + 1) := by
        calc (∏ q ∈ n.primeFactors, (q - 1)) *
              (2 * ∏ j ∈ range n.primeFactors.card, (6 * (j / 2) + 4 + 2 * (j % 2)))
            = (∏ j ∈ range n.primeFactors.card, (6 * (j / 2) + 4 + 2 * (j % 2))) *
                (2 * ∏ q ∈ n.primeFactors, (q - 1)) := by ring
          _ < (∏ j ∈ range n.primeFactors.card, (6 * (j / 2) + 4 + 2 * (j % 2))) *
                ∏ q ∈ n.primeFactors, q := Nat.mul_lt_mul_of_pos_left hb hA
          _ ≤ (∏ j ∈ range n.primeFactors.card, (6 * (j / 2) + 4 + 2 * (j % 2) + 1)) *
                ∏ q ∈ n.primeFactors, (q - 1) := hsix
          _ = _ := by ring
      exact Nat.lt_of_mul_lt_mul_left h6
    generalize n.primeFactors.card = r at hc hfinal
    interval_cases r <;> simp [Finset.prod_range_succ] at hfinal

theorem collision (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hc : (p + p.totient).primeFactors.card ≤ 6) : p.totient ≠ (p + p.totient).totient := by
  intro heq
  rw [Nat.totient_prime hp] at heq hc
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    obtain ⟨c, hcc⟩ := hodd
    omega
  obtain ⟨m, hm⟩ : ∃ m, m = p + (p - 1) := ⟨_, rfl⟩
  rw [← hm] at heq hc
  have hm5 : 5 ≤ m := by omega
  have h2phi : 2 * m.totient + 1 = m := by omega
  have hsq : Squarefree m := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro q hq hqq
    obtain ⟨c, hcq⟩ := hqq
    have hqt : q ∣ m.totient := by
      rw [hcq, mul_assoc, Nat.totient_mul_of_prime_of_dvd hq (dvd_mul_right q c)]
      exact dvd_mul_right q _
    have hqm : q ∣ m := by
      rw [hcq, mul_assoc]
      exact dvd_mul_right q _
    have h1 : q ∣ m - 2 * m.totient := Nat.dvd_sub hqm (hqt.mul_left 2)
    rw [show m - 2 * m.totient = 1 by omega] at h1
    have h2 := Nat.le_of_dvd Nat.one_pos h1
    have h3 := hq.one_lt
    omega
  have hnp : ¬ m.Prime := by
    intro hmp
    have h := Nat.totient_prime hmp
    omega
  have hdvd : m.totient ∣ m - 1 := ⟨2, by omega⟩
  exact lehmer_seven m (by omega) hsq hnp hc hdvd

end OMA.Lehmer7

theorem OMA.solution : OMA.R_OeisA108569_conjecture_R2_H1_R1_H2_R1.H1 := by
  intro p hp hodd hc
  exact OMA.Lehmer7.collision p hp hodd hc
