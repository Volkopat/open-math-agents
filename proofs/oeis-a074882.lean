import OMAStatements.S_oeis_a074882

namespace OMA.S_oeis_a074882

open Finset



/-- The number of integers in (t, t + L] coprime to n. -/
def cnt (n t L : ℕ) : ℕ := ((Ioc t (t + L)).filter (fun x => Nat.Coprime x n)).card

lemma cnt_add (n t L₁ L₂ : ℕ) : cnt n t (L₁ + L₂) ≤ cnt n t L₁ + cnt n (t + L₁) L₂ := by
  unfold cnt
  have h : Ioc t (t + (L₁ + L₂)) = Ioc t (t + L₁) ∪ Ioc (t + L₁) (t + L₁ + L₂) := by
    rw [Finset.Ioc_union_Ioc_eq_Ioc (by omega) (by omega), add_assoc]
  rw [h, Finset.filter_union]
  exact Finset.card_union_le _ _

lemma mod_coprime {n d x : ℕ} (hd : d ∣ n) (hx : Nat.Coprime x n) : Nat.Coprime d (x % d) := by
  have h1 : Nat.Coprime x d := Nat.Coprime.coprime_dvd_right hd hx
  rw [Nat.Coprime, Nat.gcd_comm, ← Nat.gcd_rec]
  exact Nat.Coprime.symm h1

lemma mod_inj {t d x y : ℕ} (hx : x ∈ Ioc t (t + d)) (hy : y ∈ Ioc t (t + d))
    (h : x % d = y % d) : x = y := by
  rw [Finset.mem_Ioc] at hx hy
  rcases le_total x y with hxy | hxy
  · have hdvd : d ∣ y - x := (Nat.modEq_iff_dvd' hxy).1 h
    have := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega
  · have hdvd : d ∣ x - y := (Nat.modEq_iff_dvd' hxy).1 h.symm
    have := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega

/-- A block of d consecutive integers, d a divisor of n, holds at most phi(d) integers coprime
to n. -/
lemma cnt_le_totient {n d : ℕ} (hd : d ∣ n) (t : ℕ) : cnt n t d ≤ Nat.totient d := by
  unfold cnt
  rw [Nat.totient]
  apply Finset.card_le_card_of_injOn (fun x => x % d)
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
    have hx1 := Finset.mem_Ioc.1 hx.1
    exact ⟨Nat.mod_lt _ (by omega), mod_coprime hd hx.2⟩
  · intro x hx y hy hxy
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
    exact mod_inj hx.1 hy.1 hxy

/-- The block (n, n + m] loses the integer n + p. -/
lemma cnt_special {n p m : ℕ} (hm : m ∣ n) (hp : p ∣ n) (hp1 : 1 < p) (hpm : p < m)
    (hcop : Nat.Coprime m p) : cnt n n m + 1 ≤ Nat.totient m := by
  have hpU : p ∈ (range m).filter (fun r => m.Coprime r) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hpm, hcop⟩
  have hle : cnt n n m ≤ (((range m).filter (fun r => m.Coprime r)).erase p).card := by
    unfold cnt
    apply Finset.card_le_card_of_injOn (fun x => x % m)
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
      simp only [Finset.coe_erase, Finset.coe_filter, Finset.mem_range, Set.mem_diff,
        Set.mem_setOf_eq, Set.mem_singleton_iff]
      have hx1 := Finset.mem_Ioc.1 hx.1
      refine ⟨⟨Nat.mod_lt _ (by omega), mod_coprime hm hx.2⟩, ?_⟩
      intro hxp
      obtain ⟨k, hk⟩ := hm
      have hr : x % m = (x - n) % m := by
        have : x = (x - n) + m * k := by omega
        rw [this, Nat.add_mul_mod_self_left, show x - n + m * k - n = x - n by omega]
      rcases Nat.lt_or_ge (x - n) m with hlt | hge
      · rw [hr, Nat.mod_eq_of_lt hlt] at hxp
        have hpx : p ∣ x := by
          have : x = n + p := by omega
          rw [this]
          exact dvd_add hp dvd_rfl
        have hg : p ∣ Nat.gcd x n := Nat.dvd_gcd hpx hp
        rw [hx.2] at hg
        exact absurd (Nat.le_of_dvd one_pos hg) (by omega)
      · have : x - n = m := by omega
        rw [hr, this, Nat.mod_self] at hxp
        omega
    · intro x hx y hy hxy
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
      exact mod_inj hx.1 hy.1 hxy
  rw [Finset.card_erase_of_mem hpU] at hle
  have hpos : 1 ≤ ((range m).filter (fun r => m.Coprime r)).card :=
    Finset.card_pos.2 ⟨p, hpU⟩
  have ht : Nat.totient m = ((range m).filter (fun r => m.Coprime r)).card := rfl
  omega

/-- Blocks for a set of divisors: an interval whose length is the sum of the divisors in R
holds at most the sum of their totients of integers coprime to n. -/
lemma cnt_tile {n : ℕ} (R : Finset ℕ) (hR : ∀ d ∈ R, d ∣ n) (t : ℕ) :
    cnt n t (∑ d ∈ R, d) ≤ ∑ d ∈ R, Nat.totient d := by
  induction R using Finset.induction_on generalizing t with
  | empty => simp [cnt]
  | insert d R hdR ih =>
    rw [Finset.sum_insert hdR, Finset.sum_insert hdR]
    have h1 := cnt_add n t d (∑ x ∈ R, x)
    have h2 := cnt_le_totient (hR d (Finset.mem_insert_self d R)) t
    have h3 := ih (fun x hx => hR x (Finset.mem_insert_of_mem hx)) (t + d)
    omega

/-- Israel's conjecture: a(n) < n for every n >= 1 that is not in A000961. -/
theorem conjecture : ∀ n : ℕ, 1 ≤ n → ¬ InA000961 n → a n < n := by
  intro n hn hnot
  have hn1 : n ≠ 1 := fun h => hnot (Or.inl h)
  have hn0 : n ≠ 0 := by omega
  set p := n.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime hn1
  have hpn : p ∣ n := Nat.minFac_dvd n
  set m := n / p ^ n.factorization p with hmdef
  have hmn : m ∣ n := Nat.ordCompl_dvd n p
  have hcop : Nat.Coprime p m := Nat.coprime_ordCompl hp hn0
  have hm0 : m ≠ 0 := by
    intro h
    rw [h] at hmn
    exact hn0 (Nat.eq_zero_of_zero_dvd hmn)
  have hm1 : m ≠ 1 := by
    intro h
    apply hnot
    right
    refine ⟨p, n.factorization p, hp, ?_, ?_⟩
    · exact (hp.factorization_pos_of_dvd hn0 hpn)
    · have := Nat.ordProj_mul_ordCompl_eq_self n p
      rw [← hmdef, h, mul_one] at this
      exact this.symm
  have hpm : p < m := by
    have hq : (m.minFac).Prime := Nat.minFac_prime hm1
    have hqm : m.minFac ∣ m := Nat.minFac_dvd m
    have hqn : m.minFac ∣ n := dvd_trans hqm hmn
    have hle : p ≤ m.minFac := Nat.minFac_le_of_dvd hq.two_le hqn
    have hne : p ≠ m.minFac := by
      intro h
      rw [← h] at hqm
      have := Nat.Coprime.eq_one_of_dvd hcop hqm
      exact hp.one_lt.ne' this
    have hq_le : m.minFac ≤ m := Nat.minFac_le (Nat.pos_of_ne_zero hm0)
    omega
  have hmne : m ≠ n := by
    intro h
    rw [h] at hcop
    have := Nat.Coprime.eq_one_of_dvd hcop hpn
    exact hp.one_lt.ne' this
  -- the divisors: n, m and the rest
  set D := n.divisors with hD
  have hnD : n ∈ D := Nat.mem_divisors_self n hn0
  have hmD : m ∈ D.erase n := Finset.mem_erase.2 ⟨hmne, Nat.mem_divisors.2 ⟨hmn, hn0⟩⟩
  set Rest := (D.erase n).erase m with hRest
  have hRestdvd : ∀ d ∈ Rest, d ∣ n := by
    intro d hd
    exact Nat.dvd_of_mem_divisors (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd))
  have hsig : ArithmeticFunction.sigma 1 n = n + (m + ∑ d ∈ Rest, d) := by
    rw [ArithmeticFunction.sigma_one_apply, ← hD, ← Finset.add_sum_erase D (fun d => d) hnD,
      ← Finset.add_sum_erase (D.erase n) (fun d => d) hmD]
  have htot : n = Nat.totient n + (Nat.totient m + ∑ d ∈ Rest, Nat.totient d) := by
    conv_lhs => rw [← Nat.sum_totient n]
    rw [← hD, ← Finset.add_sum_erase D Nat.totient hnD,
      ← Finset.add_sum_erase (D.erase n) Nat.totient hmD]
  have ha : a n = cnt n 0 (n + (m + ∑ d ∈ Rest, d)) := by
    unfold a cnt
    rw [hsig, zero_add]
    congr 1
  have h1 := cnt_add n 0 n (m + ∑ d ∈ Rest, d)
  have h2 := cnt_add n (0 + n) m (∑ d ∈ Rest, d)
  have h3 := cnt_le_totient (dvd_refl n) 0
  have h4 := cnt_special hmn hpn hp.one_lt hpm hcop.symm
  have h5 := cnt_tile Rest hRestdvd (0 + n + m)
  simp only [zero_add] at h1 h2 h5
  rw [ha]
  omega

/-- Controls from the entry: a(6) = 4, a(10) = 7, a(12) = 9 (not prime powers), a(8) = 8. -/
example : a 6 = 4 ∧ a 10 = 7 ∧ a 12 = 9 ∧ a 8 = 8 := by
  simp only [a, ArithmeticFunction.sigma_one_apply]
  decide

end OMA.S_oeis_a074882

theorem OMA.solution : type_of% @OMA.S_oeis_a074882.main :=
  OMA.S_oeis_a074882.conjecture
