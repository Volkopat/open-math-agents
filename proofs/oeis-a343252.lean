import OMAStatements.S_oeis_a343252

/-!
Proof of the OEIS A343252 conjecture (and the general theorem for any prime `p`):
For every prime `p` and `n ≥ 1`, let `k₀ = maxOtherPrimePow p n`. Then `k₀` is the least
positive integer `≤ n` such that `L p k₀ n * p ^ (n.factorization p) = n`.

Proof:
1. From `k * C(n, k) = n * C(n - 1, k - 1)`, the reduced denominator `d(k) := ((C(n, k) : ℚ) / n).den`
   divides both `n` and `k`, hence divides `Nat.gcd n k`.
2. Consequently, for every `k` with `¬ p ∣ k`, `d(k)` divides `m := n / p ^ (n.factorization p)`
   (the `p`-free part of `n`), so `L p k₀ n ∣ m` for all `k₀`.
3. For any prime `q ≠ p` with `q ∣ n` and `e := n.factorization q ≥ 1`:
   - If `k < q^e`, then `q^e ∤ k`, so `q^e ∤ d(k)`. Hence if `k < k₀`, some prime power `q^e ‖ m`
     fails to divide `L p k n`, so `L p k n ≠ m`.
   - At `k = q^e ≤ k₀`, we have `¬ p ∣ q^e` and `¬ q ∣ C(n - 1, q^e - 1)` because for every
     `1 ≤ j < q^e`, `q^e ∣ n` implies `v_q(n - j) = v_q(j)`, so
     `v_q(∏_{j=1}^{q^e - 1} (n - j)) = v_q((q^e - 1)!)`.
     Hence `q^e = d(q^e) ∣ L p k₀ n`.
4. Since every prime power `q^e ‖ m` divides `L p k₀ n`, we have `m ∣ L p k₀ n`, giving `L p k₀ n = m`.
-/

namespace A343252Proof

open Finset

private lemma rat_den_dvd_of_nat_div (a b : ℕ) :
    ((a : ℚ) / (b : ℚ)).den ∣ b := by
  have h : (a : ℚ) / (b : ℚ) = Rat.divInt (a : ℤ) (b : ℤ) := by
    rw [Rat.divInt_eq_div]; simp
  rw [h]
  exact Int.ofNat_dvd.mp (Rat.den_dvd (a : ℤ) (b : ℤ))

private lemma den_choose_div_dvd_gcd {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ((Nat.choose n k : ℚ) / (n : ℚ)).den ∣ Nat.gcd n k := by
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hdvd_n : ((Nat.choose n k : ℚ) / (n : ℚ)).den ∣ n :=
    rat_den_dvd_of_nat_div _ _
  have hdvd_k : ((Nat.choose n k : ℚ) / (n : ℚ)).den ∣ k := by
    have hid : k * Nat.choose n k = n * Nat.choose (n - 1) (k - 1) := by
      cases n with
      | zero => omega
      | succ n' =>
        cases k with
        | zero => omega
        | succ k' =>
          have h := Nat.add_one_mul_choose_eq n' k'
          simp only [Nat.add_sub_cancel]
          rw [mul_comm, ← h]
    have hq : ((Nat.choose n k : ℚ) / (n : ℚ)) = ((Nat.choose (n - 1) (k - 1) : ℕ) : ℚ) / (k : ℚ) := by
      have hidQ : (k : ℚ) * (Nat.choose n k : ℚ) = (n : ℚ) * (Nat.choose (n - 1) (k - 1) : ℚ) := by
        exact_mod_cast hid
      rw [div_eq_div_iff hn0 hk0, mul_comm, hidQ, mul_comm]
    rw [hq]
    exact rat_den_dvd_of_nat_div _ _
  exact Nat.dvd_gcd hdvd_n hdvd_k

private lemma padicValNat_sub_eq {q e n j : ℕ} (hq : q.Prime) (hn : 1 ≤ n) (hdvd : q ^ e ∣ n)
    (hj1 : 1 ≤ j) (hj2 : j < q ^ e) :
    padicValNat q (n - j) = padicValNat q j := by
  have : Fact q.Prime := ⟨hq⟩
  have hle : j < n := lt_of_lt_of_le hj2 (Nat.le_of_dvd (by omega) hdvd)
  have h1 : padicValNat q j < e := by
    by_contra! hge
    have hd : q ^ e ∣ j := (padicValNat_dvd_iff_le (by omega : j ≠ 0)).mpr hge
    have := Nat.le_of_dvd (by omega) hd
    omega
  apply le_antisymm
  · by_contra! hgt
    have hd_sub : q ^ (padicValNat q j + 1) ∣ n - j :=
      (padicValNat_dvd_iff_le (by omega : n - j ≠ 0)).mpr hgt
    have hd_n : q ^ (padicValNat q j + 1) ∣ n :=
      dvd_trans (Nat.pow_dvd_pow q (by omega)) hdvd
    have hd_j : q ^ (padicValNat q j + 1) ∣ j := by
      have hsum : n = (n - j) + j := by omega
      exact (Nat.dvd_add_right hd_sub).mp (hsum ▸ hd_n)
    have := (padicValNat_dvd_iff_le (by omega : j ≠ 0)).mp hd_j
    omega
  · have hd_j : q ^ padicValNat q j ∣ j := pow_padicValNat_dvd
    have hd_n : q ^ padicValNat q j ∣ n := dvd_trans (Nat.pow_dvd_pow q h1.le) hdvd
    have hd_sub : q ^ padicValNat q j ∣ n - j := Nat.dvd_sub hd_n hd_j
    exact (padicValNat_dvd_iff_le (by omega : n - j ≠ 0)).mp hd_sub

private lemma not_dvd_choose_pred_prime_pow {q e n : ℕ} (hq : q.Prime) (hn : 1 ≤ n)
    (hdvd : q ^ e ∣ n) : ¬ q ∣ Nat.choose (n - 1) (q ^ e - 1) := by
  have : Fact q.Prime := ⟨hq⟩
  have hqe_pos : 1 ≤ q ^ e := Nat.one_le_pow e q hq.pos
  have hqe_le : q ^ e ≤ n := Nat.le_of_dvd (by omega) hdvd
  have hmul : Nat.choose (n - 1) (q ^ e - 1) * (q ^ e - 1).factorial =
      ∏ j ∈ Finset.Ico 1 (q ^ e), (n - j) := by
    have hdesc := Nat.descFactorial_eq_factorial_mul_choose (n - 1) (q ^ e - 1)
    rw [mul_comm] at hdesc
    rw [← hdesc, Nat.descFactorial_eq_prod_range]
    have hbij : ∏ i ∈ Finset.range (q ^ e - 1), (n - 1 - i) =
        ∏ j ∈ Finset.Ico 1 (q ^ e), (n - j) := by
      apply Finset.prod_bij (fun i _ => i + 1)
      · intro i hi; rw [Finset.mem_range] at hi; rw [Finset.mem_Ico]; omega
      · intro i₁ _ i₂ _ h; omega
      · intro j hj; rw [Finset.mem_Ico] at hj; exact ⟨j - 1, Finset.mem_range.mpr (by omega), by omega⟩
      · intro i _; omega
    exact hbij
  have hfac_prod : (q ^ e - 1).factorial = ∏ j ∈ Finset.Ico 1 (q ^ e), j := by
    have h1 : ∀ m : ℕ, m.factorial = ∏ j ∈ Finset.Ico 1 (m + 1), j := by
      intro m
      induction m with
      | zero => simp
      | succ r ih =>
        rw [Finset.prod_Ico_succ_top (by omega : 1 ≤ r + 1), ← ih, Nat.factorial_succ, mul_comm]
    have := h1 (q ^ e - 1)
    rwa [Nat.sub_add_cancel hqe_pos] at this
  have hval_finset_prod : ∀ (s : Finset ℕ) (f : ℕ → ℕ),
      (∀ x ∈ s, f x ≠ 0) → padicValNat q (∏ x ∈ s, f x) = ∑ x ∈ s, padicValNat q (f x) := by
    intro s f
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simp
    | @insert a s ha ih =>
      intro hne
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have ha0 : f a ≠ 0 := hne a (Finset.mem_insert_self _ _)
      have hs0 : ∏ x ∈ s, f x ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun x hx => hne x (Finset.mem_insert_of_mem hx))
      rw [padicValNat.mul ha0 hs0, ih (fun x hx => hne x (Finset.mem_insert_of_mem hx))]
  have hval_prod : padicValNat q (∏ j ∈ Finset.Ico 1 (q ^ e), (n - j)) =
      padicValNat q (∏ j ∈ Finset.Ico 1 (q ^ e), j) := by
    rw [hval_finset_prod _ _ (fun j hj => by rw [Finset.mem_Ico] at hj; omega),
        hval_finset_prod _ _ (fun j hj => by rw [Finset.mem_Ico] at hj; omega)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Ico] at hj
    exact padicValNat_sub_eq hq hn hdvd hj.1 hj.2
  have hch_ne : Nat.choose (n - 1) (q ^ e - 1) ≠ 0 :=
    (Nat.choose_pos (by omega)).ne'
  have hfac_ne : (q ^ e - 1).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hval_eq : padicValNat q (Nat.choose (n - 1) (q ^ e - 1)) +
      padicValNat q (q ^ e - 1).factorial = padicValNat q (q ^ e - 1).factorial := by
    rw [← padicValNat.mul hch_ne hfac_ne, hmul, hval_prod, ← hfac_prod]
  have hval0 : padicValNat q (Nat.choose (n - 1) (q ^ e - 1)) = 0 := by omega
  intro hqdvd
  have hge1 : 1 ≤ padicValNat q (Nat.choose (n - 1) (q ^ e - 1)) :=
    (padicValNat_dvd_iff_le hch_ne).mp (by simpa using hqdvd)
  omega

private lemma den_choose_div_at_prime_pow {q e n : ℕ} (hq : q.Prime) (hn : 1 ≤ n)
    (hdvd : q ^ e ∣ n) : ((Nat.choose n (q ^ e) : ℚ) / (n : ℚ)).den = q ^ e := by
  have hqe_pos : 1 ≤ q ^ e := Nat.one_le_pow e q hq.pos
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hqe0 : ((q ^ e : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hid : q ^ e * Nat.choose n (q ^ e) = n * Nat.choose (n - 1) (q ^ e - 1) := by
    cases n with
    | zero => omega
    | succ n' =>
      cases h : q ^ e with
      | zero => omega
      | succ k' =>
        have h1 := Nat.add_one_mul_choose_eq n' k'
        simp only [Nat.add_sub_cancel]
        rw [mul_comm, ← h1]
  have hq_eq : ((Nat.choose n (q ^ e) : ℚ) / (n : ℚ)) =
      ((Nat.choose (n - 1) (q ^ e - 1) : ℕ) : ℚ) / ((q ^ e : ℕ) : ℚ) := by
    have hidQ : ((q ^ e : ℕ) : ℚ) * (Nat.choose n (q ^ e) : ℚ) =
        (n : ℚ) * (Nat.choose (n - 1) (q ^ e - 1) : ℚ) := by exact_mod_cast hid
    rw [div_eq_div_iff hn0 hqe0, mul_comm, hidQ, mul_comm]
  have hcop : Nat.Coprime (Nat.choose (n - 1) (q ^ e - 1)) (q ^ e) := by
    apply Nat.Coprime.pow_right
    exact (hq.coprime_iff_not_dvd.mpr (not_dvd_choose_pred_prime_pow hq hn hdvd)).symm
  rw [hq_eq]
  set r : ℚ := ((Nat.choose (n - 1) (q ^ e - 1) : ℕ) : ℚ) / ((q ^ e : ℕ) : ℚ)
  have hd_dvd : r.den ∣ q ^ e := rat_den_dvd_of_nat_div _ _
  have hqe_dvd : q ^ e ∣ r.den := by
    have hmulQ : ((Nat.choose (n - 1) (q ^ e - 1) : ℕ) : ℚ) * (r.den : ℚ) =
        ((q ^ e : ℕ) : ℚ) * (r.num : ℚ) := by
      have h1 : r * (r.den : ℚ) = (r.num : ℚ) := Rat.mul_den_eq_num r
      have h2 : ((q ^ e : ℕ) : ℚ) * r = ((Nat.choose (n - 1) (q ^ e - 1) : ℕ) : ℚ) := by
        dsimp [r]; field_simp [hqe0]
      calc ((Nat.choose (n - 1) (q ^ e - 1) : ℕ) : ℚ) * (r.den : ℚ)
          = ((q ^ e : ℕ) : ℚ) * (r * (r.den : ℚ)) := by rw [← mul_assoc, h2]
        _ = ((q ^ e : ℕ) : ℚ) * (r.num : ℚ) := by rw [h1]
    have hmulZ : ((Nat.choose (n - 1) (q ^ e - 1) * r.den : ℕ) : ℤ) =
        ((q ^ e : ℕ) : ℤ) * r.num := by
      exact_mod_cast hmulQ
    have hdvdN : q ^ e ∣ Nat.choose (n - 1) (q ^ e - 1) * r.den :=
      Int.ofNat_dvd.mp ⟨r.num, hmulZ⟩
    exact hcop.symm.dvd_of_dvd_mul_left hdvdN
  exact Nat.dvd_antisymm hd_dvd hqe_dvd

private lemma solve_prime (p : ℕ) (hp : p.Prime) : ∀ n : ℕ, 1 ≤ n →
    let k₀ := OMA.S_oeis_a343252.maxOtherPrimePow p n
    1 ≤ k₀ ∧ k₀ ≤ n ∧
    OMA.S_oeis_a343252.L p k₀ n * p ^ (n.factorization p) = n ∧
    ∀ k : ℕ, 1 ≤ k → k < k₀ → OMA.S_oeis_a343252.L p k n * p ^ (n.factorization p) ≠ n := by
  intro n hn
  dsimp only
  set k₀ := OMA.S_oeis_a343252.maxOtherPrimePow p n
  set m := n / p ^ (n.factorization p)
  have hpe_dvd : p ^ (n.factorization p) ∣ n := Nat.ordProj_dvd n p
  have hm_mul : m * p ^ (n.factorization p) = n := Nat.div_mul_cancel hpe_dvd
  have hm_pos : 1 ≤ m := by
    by_contra! h0
    have hm0 : m = 0 := Nat.lt_one_iff.mp h0
    rw [hm0, zero_mul] at hm_mul
    omega
  have hp_ndvd_m : ¬ p ∣ m := by
    have : Fact p.Prime := ⟨hp⟩
    intro hd
    have hpe1 : p ^ (n.factorization p + 1) ∣ n := by
      obtain ⟨r, hr⟩ := hd
      refine ⟨r, ?_⟩
      calc n = m * p ^ (n.factorization p) := hm_mul.symm
        _ = (p * r) * p ^ (n.factorization p) := by rw [hr]
        _ = p ^ (n.factorization p + 1) * r := by rw [pow_succ]; ring
    have := (hp.pow_dvd_iff_le_factorization (by omega : n ≠ 0)).mp hpe1
    omega
  have h1_le_k₀ : 1 ≤ k₀ := le_sup_right
  have hk₀_le_n : k₀ ≤ n := by
    apply sup_le _ hn
    rw [Finset.sup_le_iff]
    intro q hq
    have hq_dvd : q ^ (n.factorization q) ∣ n := Nat.ordProj_dvd n q
    exact Nat.le_of_dvd (by omega) hq_dvd
  have hL_dvd_m : ∀ k : ℕ, OMA.S_oeis_a343252.L p k n ∣ m := by
    intro k
    unfold OMA.S_oeis_a343252.L
    rw [Finset.lcm_dvd_iff]
    intro j hj
    rw [Finset.mem_filter, Finset.mem_Icc] at hj
    have hd_gcd : ((Nat.choose n j : ℚ) / (n : ℚ)).den ∣ Nat.gcd n j :=
      den_choose_div_dvd_gcd hn hj.1.1
    have hd_n : ((Nat.choose n j : ℚ) / (n : ℚ)).den ∣ n :=
      dvd_trans hd_gcd (Nat.gcd_dvd_left n j)
    have hd_j : ((Nat.choose n j : ℚ) / (n : ℚ)).den ∣ j :=
      dvd_trans hd_gcd (Nat.gcd_dvd_right n j)
    have hcop_p : Nat.Coprime ((Nat.choose n j : ℚ) / (n : ℚ)).den (p ^ (n.factorization p)) := by
      apply Nat.Coprime.pow_right
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hp_d
      exact hj.2 (dvd_trans hp_d hd_j)
    have hd_n' : ((Nat.choose n j : ℚ) / (n : ℚ)).den ∣ m * p ^ (n.factorization p) := by
      rwa [hm_mul]
    exact hcop_p.dvd_of_dvd_mul_right hd_n'
  have hm_dvd_Lk₀ : m ∣ OMA.S_oeis_a343252.L p k₀ n := by
    have hL_ne : OMA.S_oeis_a343252.L p k₀ n ≠ 0 := by
      intro h0
      have := hL_dvd_m k₀
      rw [h0, zero_dvd_iff] at this
      omega
    rw [← Nat.factorization_le_iff_dvd (by omega : m ≠ 0) hL_ne]
    intro q
    by_cases hqm : q ∈ m.primeFactors
    · have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hqm
      have hq_dvd_m : q ∣ m := Nat.dvd_of_mem_primeFactors hqm
      have hq_ne_p : q ≠ p := fun heq => hp_ndvd_m (heq ▸ hq_dvd_m)
      have hq_dvd_n : q ∣ n := dvd_trans hq_dvd_m (by rw [← hm_mul]; exact dvd_mul_right _ _)
      have hq_mem : q ∈ n.primeFactors.erase p :=
        Finset.mem_erase.mpr ⟨hq_ne_p, Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd_n, by omega⟩⟩
      have hqe_le_k₀ : q ^ (n.factorization q) ≤ k₀ :=
        le_trans (Finset.le_sup (f := fun r => r ^ (n.factorization r)) hq_mem) le_sup_left
      have hqe_pos : 1 ≤ q ^ (n.factorization q) := Nat.one_le_pow _ _ hq_prime.pos
      have hp_ndvd_qe : ¬ p ∣ q ^ (n.factorization q) := by
        intro hd
        have hpq := hp.dvd_of_dvd_pow hd
        exact hq_ne_p ((Nat.prime_dvd_prime_iff_eq hp hq_prime).mp hpq).symm
      have hqe_mem_S : q ^ (n.factorization q) ∈
          (Finset.Icc 1 k₀).filter (fun k => ¬ p ∣ k) := by
        rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hqe_pos, hqe_le_k₀⟩, hp_ndvd_qe⟩
      have hqe_dvd_L : q ^ (n.factorization q) ∣ OMA.S_oeis_a343252.L p k₀ n := by
        have hden := den_choose_div_at_prime_pow hq_prime hn (Nat.ordProj_dvd n q)
        rw [← hden]
        exact Finset.dvd_lcm hqe_mem_S
      have hval_le : n.factorization q ≤ (OMA.S_oeis_a343252.L p k₀ n).factorization q :=
        (hq_prime.pow_dvd_iff_le_factorization hL_ne).mp hqe_dvd_L
      have hm_le_n : m.factorization q ≤ n.factorization q :=
        Nat.factorization_le_iff_dvd (by omega) (by omega) |>.mpr
          (by rw [← hm_mul]; exact dvd_mul_right _ _) q
      exact hm_le_n.trans hval_le
    · have : m.factorization q = 0 := by
        by_contra h0
        have hmem : q ∈ m.factorization.support := Finsupp.mem_support_iff.mpr h0
        rw [Nat.support_factorization] at hmem
        exact hqm hmem
      omega
  have hLk₀_eq : OMA.S_oeis_a343252.L p k₀ n = m := Nat.dvd_antisymm (hL_dvd_m k₀) hm_dvd_Lk₀
  refine ⟨h1_le_k₀, hk₀_le_n, by rw [hLk₀_eq, hm_mul], ?_⟩
  intro k hk1 hk_lt heq
  have hLk_eq : OMA.S_oeis_a343252.L p k n = m := by
    have hpe_pos : 0 < p ^ (n.factorization p) := pow_pos hp.pos _
    exact Nat.eq_of_mul_eq_mul_right hpe_pos (heq.trans hm_mul.symm)
  have hsup_gt : 1 < k₀ := by omega
  have hsup_eq : (n.primeFactors.erase p).sup (fun q => q ^ (n.factorization q)) = k₀ := by
    have hk₀_def : k₀ = (n.primeFactors.erase p).sup (fun q => q ^ (n.factorization q)) ⊔ 1 := rfl
    rw [hk₀_def]
    symm
    apply sup_eq_left.mpr
    by_contra! hlt
    have hle1 : (n.primeFactors.erase p).sup (fun q => q ^ (n.factorization q)) ≤ 1 := by omega
    have : k₀ ≤ 1 := by rw [hk₀_def]; exact sup_le hle1 le_rfl
    omega
  have hne_set : (n.primeFactors.erase p).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.sup_empty, Nat.bot_eq_zero] at hsup_eq
    omega
  obtain ⟨q, hq_mem, hq_eq⟩ := Finset.exists_mem_eq_sup (n.primeFactors.erase p) hne_set
    (fun q => q ^ (n.factorization q))
  have hq_lt : k < q ^ (n.factorization q) := by omega
  have hq_ne_p : q ≠ p := (Finset.mem_erase.mp hq_mem).1
  have hq_pf : q ∈ n.primeFactors := Finset.mem_of_mem_erase hq_mem
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_pf
  have hqe_dvd_m : q ^ (n.factorization q) ∣ m := by
    have hcop : Nat.Coprime (q ^ (n.factorization q)) (p ^ (n.factorization p)) :=
      (hq_prime.coprime_iff_not_dvd.mpr fun hd =>
        hq_ne_p ((Nat.prime_dvd_prime_iff_eq hq_prime hp).mp hd)).pow _ _
    have hndvd : q ^ (n.factorization q) ∣ m * p ^ (n.factorization p) := by
      rw [hm_mul]; exact Nat.ordProj_dvd n q
    exact hcop.dvd_of_dvd_mul_right hndvd
  have hqe_dvd_L : q ^ (n.factorization q) ∣ OMA.S_oeis_a343252.L p k n := by
    rw [hLk_eq]; exact hqe_dvd_m
  -- Yet every term in L p k n has index j ≤ k < q^(n.factorization q), so q^(n.factorization q) ∤ den(j)!
  have hnot_dvd : ¬ q ^ (n.factorization q) ∣ OMA.S_oeis_a343252.L p k n := by
    have hL_ne : OMA.S_oeis_a343252.L p k n ≠ 0 := by rw [hLk_eq]; omega
    intro hd
    -- Wait: for a prime power q^e ∣ lcm(S), there exists j ∈ S with q^e ∣ f(j)!
    have hex : ∃ j ∈ (Finset.Icc 1 k).filter (fun j => ¬ p ∣ j),
        q ^ (n.factorization q) ∣ ((Nat.choose n j : ℚ) / (n : ℚ)).den := by
      have hpp : ∀ (T : Finset ℕ) (f : ℕ → ℕ),
          q ^ (n.factorization q) ∣ T.lcm f → ∃ j ∈ T, q ^ (n.factorization q) ∣ f j := by
        intro T f
        induction T using Finset.induction_on with
        | empty =>
          simp only [Finset.lcm_empty]
          intro h1
          have := Nat.le_of_dvd (by decide) h1
          omega
        | @insert a T ha ih =>
          rw [Finset.lcm_insert]
          intro hdiv
          by_cases ha0 : f a = 0
          · exact ⟨a, Finset.mem_insert_self _ _, by simp [ha0]⟩
          by_cases hT0 : T.lcm f = 0
          · obtain ⟨j, hj, hjd⟩ := ih (by simp [hT0])
            exact ⟨j, Finset.mem_insert_of_mem hj, hjd⟩
          have hval := (hq_prime.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero ha0 hT0)).mp hdiv
          rw [Nat.factorization_lcm ha0 hT0, Finsupp.sup_apply] at hval
          rcases le_max_iff.mp hval with h1 | h2
          · exact ⟨a, Finset.mem_insert_self _ _,
              (hq_prime.pow_dvd_iff_le_factorization ha0).mpr h1⟩
          · obtain ⟨j, hj, hjd⟩ := ih ((hq_prime.pow_dvd_iff_le_factorization hT0).mpr h2)
            exact ⟨j, Finset.mem_insert_of_mem hj, hjd⟩
      exact hpp _ _ hd
    obtain ⟨j, hj, hjd⟩ := hex
    rw [Finset.mem_filter, Finset.mem_Icc] at hj
    have hd_j : q ^ (n.factorization q) ∣ j :=
      dvd_trans hjd (dvd_trans (den_choose_div_dvd_gcd hn hj.1.1) (Nat.gcd_dvd_right n j))
    have := Nat.le_of_dvd (by omega) hd_j
    omega
  exact hnot_dvd hqe_dvd_L

end A343252Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a343252.main :=
  A343252Proof.solve_prime 7 (by decide)
