import OMAStatements.S_oeis_a133910
import Mathlib

open Finset OMA.S_oeis_a133910

/- Pascal differences relate shifts of the entire row to the first k binomial coefficients of t. -/
private lemma oma_binom_period_rows (q k t : ℕ) :
    (∀ m : ℕ, (m+t+k).choose k % q = (m+k).choose k % q) ↔
      ∀ j : ℕ, 1 ≤ j → j ≤ k → q ∣ t.choose j := by
  let P (x j : ℕ) := (x+t).choose j ≡ x.choose j [MOD q]
  have zero (x : ℕ) : P x 0 := by simp [P, Nat.ModEq]
  have pascal (x j : ℕ) : P (x+1) (j+1) ↔
      (x+t).choose j + (x+t).choose (j+1) ≡ x.choose j + x.choose (j+1) [MOD q] := by
    unfold P
    rw [show x+1+t = (x+t)+1 by omega, Nat.choose_succ_succ', Nat.choose_succ_succ']
  have initial (j : ℕ) (hj : 1 ≤ j) : P 0 j ↔ q ∣ t.choose j := by
    simpa [P, Nat.choose_eq_zero_of_lt (show 0 < j by omega)] using
      (Nat.modEq_zero_iff_dvd (n := q) (a := t.choose j))
  constructor
  · intro htop
    have top (x : ℕ) (hx : k ≤ x) : P x k := by
      obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hx
      simpa [P, Nat.ModEq, add_comm, add_left_comm, add_assoc] using htop m
    -- Taking successive differences proves periodicity below column k for all x ≥ k.
    have lower (b : ℕ) (hb : ∀ x, k ≤ x → P x b) : ∀ j ≤ b, ∀ x, k ≤ x → P x j := by
      induction b with
      | zero =>
        intro j hj x _
        obtain rfl : j = 0 := by omega
        exact zero x
      | succ b ih =>
        intro j hj
        rcases Nat.eq_or_lt_of_le hj with rfl | hj'
        · exact hb
        · apply ih (fun x hx => ?_) j (by omega)
          exact (hb x hx).add_right_cancel ((pascal x b).mp (hb (x+1) (by omega)))
    -- One complete row determines the preceding row, working across it from column zero.
    have retreat (x : ℕ) (h : ∀ j ≤ k, P (x+1) j) : ∀ j ≤ k, P x j := by
      intro j
      induction j with
      | zero => exact fun _ => zero x
      | succ j ih =>
        intro hj
        exact (ih (by omega)).add_left_cancel ((pascal x j).mp (h (j+1) hj))
    have to_zero (x : ℕ) (h : ∀ j ≤ k, P x j) : ∀ j ≤ k, P 0 j := by
      induction x with
      | zero => exact h
      | succ x ih => exact ih (retreat x h)
    intro j hj hjk
    exact (initial j hj).mp (to_zero k (fun i hi => lower k top i hi k (by omega)) j hjk)
  · intro hd
    have all_rows (x : ℕ) : ∀ j ≤ k, P x j := by
      induction x with
      | zero =>
        rintro (_ | j) hj
        · exact zero 0
        · exact (initial (j+1) (by omega)).mpr (hd (j+1) (by omega) hj)
      | succ x ih =>
        rintro (_ | j) hj
        · exact zero _
        · exact (pascal x j).mpr ((ih j (by omega)).add (ih (j+1) hj))
    intro m
    simpa [P, Nat.ModEq, add_comm, add_left_comm, add_assoc] using all_rows (m+k) k (by omega)

/- For each prime power in the modulus, determine the exact power of the prime that divides every period. -/
private theorem binom_period_prime_power {n p v t : ℕ} (hp : p.Prime)
    (hv : 0 < v) (hn : 0 < n) :
    (∀ j : ℕ, 1 ≤ j → j ≤ n → p ^ v ∣ t.choose j) ↔ p ^ (v + Nat.log p n) ∣ t := by
  constructor
  · intro hrow
    cases t with
    | zero => exact dvd_zero _
    | succ u =>
      have hprev : ∀ j ≤ n, ¬ p ∣ u.choose j := by
        intro j
        induction j with
        | zero => simpa using hp.not_dvd_one
        | succ j ih =>
          intro hj hdiv
          have hsum := (dvd_pow_self p hv.ne').trans (hrow (j + 1) (by omega) hj)
          rw [Nat.choose_succ_succ] at hsum
          exact ih (by omega) ((Nat.dvd_add_left hdiv).mp hsum)
      let J := p ^ Nat.log p n
      have hJ : 0 < J := pow_pos hp.pos _
      have hJn : J ≤ n := Nat.pow_log_le_self _ hn.ne'
      have hcop := (hp.coprime_iff_not_dvd.mpr (hprev (J - 1) (by omega))).pow_left
        (v + Nat.log p n)
      apply hcop.dvd_of_dvd_mul_right
      have hstep := Nat.add_one_mul_choose_eq u (J - 1)
      rw [Nat.sub_one_add_one_eq_of_pos hJ] at hstep
      rw [hstep, pow_add]
      exact Nat.mul_dvd_mul_right (hrow J hJ hJn) J
  · intro ht j hj hjn
    by_cases hjt : j ≤ t
    · have ht0 : t ≠ 0 := by omega
      have hle := (hp.pow_dvd_iff_le_factorization ht0).mp ht
      have hjfac : j.factorization p ≤ Nat.log p n := by
        apply Nat.le_log_of_pow_le hp.one_lt
        exact (Nat.le_of_dvd hj (Nat.ordProj_dvd j p)).trans hjn
      apply (hp.pow_dvd_iff_le_factorization (Nat.choose_ne_zero hjt)).mpr
      have := Nat.factorization_le_factorization_choose_add (p := p) hjt (by omega)
      omega
    · simp [Nat.choose_eq_zero_of_lt (by omega : t < j)]

/- Combine the local conditions using coprimality, then take the least positive shift. -/
private lemma binom_product_dvd {s : Finset ℕ} (prime : ∀ p ∈ s, p.Prime)
    (f : ℕ → ℕ) (b : ℕ) : (∏ p ∈ s, p ^ f p) ∣ b ↔ ∀ p ∈ s, p ^ f p ∣ b := by
  refine ⟨fun h p hp => (Finset.dvd_prod_of_mem _ hp).trans h, ?_⟩
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
    intro h
    rw [Finset.prod_insert hp]
    have hpp := prime p (mem_insert_self _ _)
    have cps : (p ^ f p).Coprime (∏ q ∈ s, q ^ f q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      exact Nat.coprime_pow_primes _ _ hpp (prime q (mem_insert_of_mem hq)) (by rintro rfl; contradiction)
    exact cps.mul_dvd_of_dvd_of_dvd (h p (mem_insert_self _ _))
      (ih (fun q hq => prime q (mem_insert_of_mem hq)) (fun q hq => h q (mem_insert_of_mem hq)))

private lemma binom_period_formula
    (rows : ∀ {q k t : ℕ}, (∀ m, (m+t+k).choose k % q = (m+k).choose k % q) ↔
        ∀ j, 1 ≤ j → j ≤ k → q ∣ t.choose j)
    (localPow : ∀ {n p v t : ℕ}, p.Prime → 0 < v → 0 < n →
        ((∀ j, 1 ≤ j → j ≤ n → p^v ∣ t.choose j) ↔ p^(v+Nat.log p n) ∣ t))
    (n : ℕ) (hn : 1 ≤ n) :
    period n = ∏ p ∈ n.primeFactors, p^(n.factorization p + Nat.log p n) := by
  let M := ∏ p ∈ n.primeFactors, p^(n.factorization p + Nat.log p n)
  have hM : 0 < M := Finset.prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  have hp {p : ℕ} (h : p ∈ n.primeFactors) := Nat.prime_of_mem_primeFactors h
  have hv {p : ℕ} (h : p ∈ n.primeFactors) : 0 < n.factorization p :=
    (hp h).factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors h)
  have splitN (b : ℕ) : n ∣ b ↔ ∀ p ∈ n.primeFactors, p ^ n.factorization p ∣ b := by
    calc
      _ ↔ (∏ p ∈ n.primeFactors, p ^ n.factorization p) ∣ b :=
        Iff.of_eq (congrArg (fun k : ℕ => k ∣ b) (Nat.prod_primeFactors_pow_factorization (by omega)))
      _ ↔ _ := binom_product_dvd (fun _ h => hp h) _ _
  have characterize (t : ℕ) : (∀ m, (m+t+n).choose n % n = (m+n).choose n % n) ↔ M ∣ t := by
    rw [rows]
    change _ ↔ (∏ p ∈ n.primeFactors, p^(n.factorization p+Nat.log p n)) ∣ t
    rw [binom_product_dvd (fun _ h => hp h)]
    constructor
    · intro h p hm
      exact (localPow (hp hm) (hv hm) hn).mp fun j hj hjn => (splitN _).mp (h j hj hjn) p hm
    · intro h j hj hjn
      apply (splitN _).mpr
      intro p hm
      exact (localPow (hp hm) (hv hm) hn).mpr (h p hm) j hj hjn
  have hmem : M ∈ {t : ℕ | 0 < t ∧ ∀ m, (m+t+n).choose n % n = (m+n).choose n % n} :=
    ⟨hM, (characterize M).mpr dvd_rfl⟩
  apply le_antisymm (Nat.sInf_le hmem)
  have hleast := Nat.sInf_mem ⟨M, hmem⟩
  exact Nat.le_of_dvd hleast.1 ((characterize _).mp hleast.2)

/- Read off the exponents in the quotient by n² and compare them with those in n. -/
private lemma binom_period_finish
    (formula : ∀ n : ℕ, 1 ≤ n →
      period n = ∏ p ∈ n.primeFactors, p ^ (n.factorization p + Nat.log p n)) :
    ∀ n : ℕ, 1 ≤ n → (n ∣ a n ↔ n = 1 ∨ inA051283 n) := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have factor_ne (p : ℕ) (hp : p ∈ n.primeFactors) :
      p ^ (n.factorization p + Nat.log p n) ≠ 0 :=
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hper : period n ≠ 0 := by
    rw [formula n hn]
    exact prod_ne_zero_iff.mpr factor_ne
  have vperiod (p : ℕ) (hp : p ∈ n.primeFactors) :
      (period n).factorization p = n.factorization p + Nat.log p n := by
    rw [formula n hn, Nat.factorization_prod_apply factor_ne,
      sum_eq_single_of_mem p hp, Nat.factorization_pow_self (Nat.prime_of_mem_primeFactors hp)]
    intro q hq hne
    simp [(Nat.prime_of_mem_primeFactors hq).factorization_pow, hne]
  have powcrit (k : ℕ) : n^k ∣ period n ↔ ∀ p ∈ n.primeFactors,
      k * n.factorization p ≤ n.factorization p + Nat.log p n := by
    rw [← Nat.factorization_le_iff_dvd (pow_ne_zero _ hn0) hper, Finsupp.le_def]
    simp only [Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul, Nat.cast_id]
    constructor
    · intro h p hp
      simpa only [vperiod p hp] using h p
    · intro h p
      by_cases hp : p ∈ n.primeFactors
      · exact (h p hp).trans_eq (vperiod p hp).symm
      · have hz : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
        simp [hz]
  have square_dvd : n^2 ∣ period n := by
    apply (powcrit 2).2
    intro p hp
    have := (Nat.le_log_iff_pow_le (Nat.prime_of_mem_primeFactors hp).one_lt hn0).2
      (Nat.ordProj_le p hn0)
    omega
  rw [a, Nat.dvd_div_iff_mul_dvd square_dvd, ← pow_succ, powcrit]
  by_cases none : n = 1
  · simp [none]
  · rw [or_iff_right none]
    refine ⟨fun h => ⟨by omega, ?_⟩, ?_⟩
    · intro p e hp he hd hexact
      have ve : e = n.factorization p := by
        rw [hp.pow_dvd_iff_le_factorization hn0] at hd hexact
        omega
      have hmem := Nat.mem_primeFactors.mpr ⟨hp, (dvd_pow_self p he.ne').trans hd, hn0⟩
      have hv := h p hmem
      have hl : 2*e ≤ Nat.log p n := by omega
      have hb := (Nat.le_log_iff_pow_le hp.one_lt hn0).mp hl
      rw [Nat.mul_comm 2 e, pow_mul] at hb
      apply lt_of_le_of_ne hb
      intro hEq
      apply hexact
      rw [← hEq, ← pow_mul]
      exact pow_dvd_pow _ (by omega)
    · rintro ⟨_, h⟩ p hm
      obtain ⟨hp, hd, _⟩ := Nat.mem_primeFactors.mp hm
      have he := hp.factorization_pos_of_dvd hn0 hd
      have hb := h p (n.factorization p) hp he
        ((hp.pow_dvd_iff_le_factorization hn0).2 le_rfl)
        (fun h => (by have := (hp.pow_dvd_iff_le_factorization hn0).1 h; omega))
      rw [← pow_mul] at hb
      have hl := (Nat.le_log_iff_pow_le hp.one_lt hn0).2 hb.le
      omega

theorem OMA.solution : type_of% @OMA.S_oeis_a133910.main := by
  apply binom_period_finish
  exact binom_period_formula (fun {q k t} => oma_binom_period_rows q k t) binom_period_prime_power
