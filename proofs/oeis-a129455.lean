import OMAStatements.S_oeis_a129455

-- Problem: A129455: an analog of Pascal's triangle based on A129454 (products of gcds over triples).
-- Upstream: statements/oeis-a129455.lean (declaration OMA.S_oeis_a129455.main)
-- Credit: @rgoldman73-dev (the owner of the agent is credited as the solver)
--
-- Proof that T(n,k) is an integer, divisible by C(n,k), with T(n,k)/C(n,k) a perfect sixth power.
-- For a prime p, the exponent of p in table 3 m is the sum over e >= 1 of floor(m/p^e)^3
-- (val_table: count the triples all of whose coordinates are multiples of p^e), and the
-- exponent of p in m! is the sum of floor(m/p^e) (Legendre). Writing a, b, c for the floors
-- of (n-k)/p^e, k/p^e, n/p^e we have a + b <= c, and x^3 - x is a multiple of 6, so
-- c^3 + a + b - (a^3 + b^3 + c) is a nonnegative multiple of 6 (term_lemma). Hence
-- table 3 n * k! * (n-k)! equals table 3 (n-k) * table 3 k * n! times a sixth power (sixth).

namespace A129455H

open OMA.S_oeis_a129455

theorem tupleGCD_ne_zero {m : ℕ} (v : Fin 3 → Fin m) : tupleGCD v ≠ 0 := by
  unfold tupleGCD
  intro h
  rw [Finset.gcd_eq_zero_iff] at h
  have h0 := h 0 (Finset.mem_univ 0)
  omega

theorem tupleGCD_le {m : ℕ} (v : Fin 3 → Fin m) : tupleGCD v ≤ m := by
  have h1 : tupleGCD v ∣ (v 0).val + 1 := by
    unfold tupleGCD
    exact Finset.gcd_dvd (Finset.mem_univ 0)
  have h2 := Nat.le_of_dvd (Nat.succ_pos _) h1
  have h3 := (v 0).isLt
  omega

theorem card_mult (m q : ℕ) :
    ((Finset.univ : Finset (Fin m)).filter (fun x => q ∣ x.val + 1)).card = m / q := by
  rw [Finset.card_filter, ← Nat.card_multiples m q, Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun i => if q ∣ i + 1 then 1 else 0) m

theorem card_tuples (m q : ℕ) :
    ((Finset.univ : Finset (Fin 3 → Fin m)).filter (fun v => ∀ i, q ∣ (v i).val + 1)).card =
      (m / q) ^ 3 := by
  have h : (Finset.univ : Finset (Fin 3 → Fin m)).filter (fun v => ∀ i, q ∣ (v i).val + 1) =
      Fintype.piFinset (fun _ : Fin 3 =>
        (Finset.univ : Finset (Fin m)).filter (fun x => q ∣ x.val + 1)) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
  rw [h, Fintype.card_piFinset_const, card_mult]

theorem val_table (p : ℕ) (hp : p.Prime) (m N : ℕ) (hmN : m ≤ N) :
    (table 3 m).factorization p = ∑ e ∈ Finset.Ico 1 (N + 1), (m / p ^ e) ^ 3 := by
  unfold table
  rw [Nat.factorization_prod (fun v _ => tupleGCD_ne_zero v), Finsupp.finsetSum_apply]
  have h1 : ∀ v : Fin 3 → Fin m, (tupleGCD v).factorization p =
      ∑ e ∈ Finset.Ico 1 (N + 1), if (∀ i, p ^ e ∣ (v i).val + 1) then 1 else 0 := by
    intro v
    have hlt : tupleGCD v < p ^ (N + 1) :=
      lt_of_le_of_lt ((tupleGCD_le v).trans hmN)
        (lt_trans (Nat.lt_succ_self N) (Nat.lt_pow_self hp.one_lt))
    rw [Nat.factorization_eq_card_pow_dvd_of_lt hp (Nat.pos_of_ne_zero (tupleGCD_ne_zero v)) hlt,
      Finset.card_filter]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    have hd : (p ^ e ∣ tupleGCD v) ↔ ∀ i, p ^ e ∣ (v i).val + 1 := by
      unfold tupleGCD
      rw [Finset.dvd_gcd_iff]
      simp
    simp only [hd]
  rw [Finset.sum_congr rfl (fun v _ => h1 v), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [← Finset.card_filter, card_tuples]

theorem val_fact (p : ℕ) (hp : p.Prime) (m N : ℕ) (hmN : m ≤ N) :
    (m.factorial).factorization p = ∑ e ∈ Finset.Ico 1 (N + 1), m / p ^ e :=
  Nat.factorization_factorial hp (Nat.lt_succ_of_le ((Nat.log_le_self p m).trans hmN))

theorem cube_eq (x : ℕ) : ∃ t, x ^ 3 = x + 6 * t := by
  induction x with
  | zero => exact ⟨0, by norm_num⟩
  | succ x ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨s, hs⟩ := Nat.even_mul_succ_self x
    refine ⟨t + s, ?_⟩
    have h : (x + 1) ^ 3 = x ^ 3 + 3 * (x * (x + 1)) + 1 := by ring
    rw [h, ht, hs]
    ring

theorem term_lemma (a b c : ℕ) (h : a + b ≤ c) :
    ∃ τ, c ^ 3 + b + a = a ^ 3 + b ^ 3 + c + 6 * τ := by
  obtain ⟨ta, ha⟩ := cube_eq a
  obtain ⟨tb, hb⟩ := cube_eq b
  obtain ⟨tc, hc⟩ := cube_eq c
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 : (a + b + d) ^ 3 = a ^ 3 + b ^ 3 + d ^ 3 + 3 * ((a + b) * (b + d) * (a + d)) := by ring
  have h2 : d ≤ d ^ 3 := Nat.le_self_pow (by norm_num) d
  refine ⟨tc - ta - tb, ?_⟩
  generalize (a + b) * (b + d) * (a + d) = w at h1
  omega

theorem sum_lemma (s : Finset ℕ) (F G : ℕ → ℕ) (h : ∀ e ∈ s, ∃ τ, F e = G e + 6 * τ) :
    ∃ τ, ∑ e ∈ s, F e = ∑ e ∈ s, G e + 6 * τ := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨t1, h1⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨t2, h2⟩ := ih (fun e he => h e (Finset.mem_insert_of_mem he))
    refine ⟨t1 + t2, ?_⟩
    rw [Finset.sum_insert ha, Finset.sum_insert ha, h1, h2]
    ring

theorem sixth (A B : ℕ) (hA : A ≠ 0) (hB : B ≠ 0)
    (h : ∀ p : ℕ, p.Prime → ∃ τ, A.factorization p = B.factorization p + 6 * τ) :
    ∃ z, A = B * z ^ 6 := by
  have hle : B.factorization ≤ A.factorization := by
    intro p
    by_cases hp : p.Prime
    · obtain ⟨τ, hτ⟩ := h p hp
      omega
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  have hdvd : B ∣ A := (Nat.factorization_le_iff_dvd hB hA).mp hle
  obtain ⟨Q, rfl⟩ := hdvd
  have hQ : Q ≠ 0 := by
    rintro rfl
    simp at hA
  refine ⟨Q.factorization.prod (fun p e => p ^ (e / 6)), ?_⟩
  congr 1
  have h6 : ∀ p ∈ Q.factorization.support, 6 ∣ Q.factorization p := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
    obtain ⟨τ, hτ⟩ := h p hpp
    rw [Nat.factorization_mul hB hQ] at hτ
    simp only [Finsupp.add_apply] at hτ
    exact ⟨τ, by omega⟩
  calc Q = Q.factorization.prod (fun p e => p ^ e) := (Nat.prod_factorization_pow_eq_self hQ).symm
    _ = Q.factorization.prod (fun p e => (p ^ (e / 6)) ^ 6) := by
        refine Finsupp.prod_congr (fun p hp => ?_)
        rw [← pow_mul, Nat.div_mul_cancel (h6 p hp)]
    _ = (Q.factorization.prod (fun p e => p ^ (e / 6))) ^ 6 := by
        simp only [Finsupp.prod, Finset.prod_pow]

theorem main_thm (n k : ℕ) (hk : k ≤ n) :
    ∃ z : ℕ, table 3 n = (table 3 (n - k) * table 3 k * n.choose k) * z ^ 6 := by
  have tpos : ∀ m, table 3 m ≠ 0 := fun m => by
    unfold table
    exact Finset.prod_ne_zero_iff.mpr (fun v _ => tupleGCD_ne_zero v)
  have hfact : n.choose k * k.factorial * (n - k).factorial = n.factorial :=
    Nat.choose_mul_factorial_mul_factorial hk
  have key : ∃ z, table 3 n * (k.factorial * (n - k).factorial) =
      (table 3 (n - k) * table 3 k * n.factorial) * z ^ 6 := by
    apply sixth
    · exact mul_ne_zero (tpos n) (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
    · exact mul_ne_zero (mul_ne_zero (tpos _) (tpos _)) (Nat.factorial_ne_zero _)
    · intro p hp
      rw [Nat.factorization_mul (tpos n)
          (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)),
        Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
        Nat.factorization_mul (mul_ne_zero (tpos _) (tpos _)) (Nat.factorial_ne_zero _),
        Nat.factorization_mul (tpos _) (tpos _)]
      simp only [Finsupp.add_apply]
      rw [val_table p hp n n le_rfl, val_table p hp (n - k) n (Nat.sub_le n k),
        val_table p hp k n hk, val_fact p hp k n hk, val_fact p hp (n - k) n (Nat.sub_le n k),
        val_fact p hp n n le_rfl]
      simp only [← Finset.sum_add_distrib]
      apply sum_lemma
      intro e _
      obtain ⟨τ, hτ⟩ := term_lemma ((n - k) / p ^ e) (k / p ^ e) (n / p ^ e) (by
        have h := Nat.div_add_div_le_add_div (x := n - k) (y := k) (z := p ^ e)
        rwa [Nat.sub_add_cancel hk] at h)
      exact ⟨τ, by omega⟩
  obtain ⟨z, hz⟩ := key
  refine ⟨z, ?_⟩
  have hpos : 0 < k.factorial * (n - k).factorial :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [hz, ← hfact]
  ring

end A129455H

theorem OMA.solution : type_of% @OMA.S_oeis_a129455.main :=
  fun n k hk => A129455H.main_thm n k hk
