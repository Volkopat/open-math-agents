import OMAReductions.R_Erdos1052_erdos_1052_R2_H2_R3

/-!
# Seed factors and shift branching for simple Mersenne primes

Reduction of `Erdos1052.erdos_1052.R2.H2.R3.H1` (bounding the number of simple
Mersenne primes `q ∈ S` with `ordCompl[2] (1 + q) = 1` uniformly in the 2-adic
exponent `a` for a fixed odd powerful core `c`).

From the balance equation `(2^a + 1) * σ*(c) * ∏ (1 + p) = 2^(a+1) * c * ∏ p`,
taking odd parts (`ordCompl[2]`) and total prime-factor multiplicity (`Ω = cardFactors`)
yields the exact conservation law (`omega_conservation`):

  |M| + Ω(c) = Ω(2^a + 1) + Ω(ordCompl[2] (σ*(c))) + ∑_{p ∈ S} (Ω(ordCompl[2] (1 + p)) - 1),

where `M = {q ∈ S | ordCompl[2] (1 + q) = 1}`. Thus a uniform bound on `|M|` is
equivalent (up to the core constants `Ω(c)` and `ω(σ*(c))`) to uniformly bounding:
  - `H1`: the number of prime factors of `2^a + 1` occurring in `S`, and
  - `H2`: the total excess number of `S`-children of shifts `1 + p`, summed over `p ∈ S`.

Both `H1` and `H2` eliminate `ordCompl[2]` and Mersenne primes from their statements.
We also include `@witeg4`'s verified `mersenne_not_dvd_seed` and `mersenne_trace_factor`
lemmas (from desk note #128653) and the exact odd-part balance and conservation law for
downstream use.

Credit: @Progren (building on desk note #128653 by @witeg4 and reduction R3 by @ubuwaits)
-/

namespace OMA.R_Erdos1052_erdos_1052_R2_H2_R3_H1_R1

open scoped BigOperators
open ArithmeticFunction

/-- Uniform bound on the number of prime factors of `2 ^ a + 1` occurring in `S`. -/
def H1 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∃ K : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2 ^ a * c
      let u := ∏ p ∈ b.primeFactors, (1 + p ^ b.factorization p)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬ p ∣ b) →
      u * (∏ p ∈ S, (1 + p)) = (2 * b) * (∏ p ∈ S, p) →
      (S.filter (fun p => p ∣ 2 ^ a + 1)).card ≤ K

/-- Uniform bound on total shift branching inside `S`: the excess number of primes in `S`
dividing `1 + p`, summed over `p ∈ S`. -/
def H2 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∃ K : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2 ^ a * c
      let u := ∏ p ∈ b.primeFactors, (1 + p ^ b.factorization p)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬ p ∣ b) →
      u * (∏ p ∈ S, (1 + p)) = (2 * b) * (∏ p ∈ S, p) →
      (∑ p ∈ S, ((S.filter (fun r => r ∣ 1 + p)).card - 1)) ≤ K

/-- Factorization of `σ*(2^a * c)` for positive `a` and odd `c`. -/
theorem sigma_power_two_times {a c : ℕ} (ha : 0 < a) (hc : Odd c) :
    (∏ p ∈ (2 ^ a * c).primeFactors, (1 + p ^ (2 ^ a * c).factorization p)) =
      (2 ^ a + 1) * (∏ p ∈ c.primeFactors, (1 + p ^ c.factorization p)) := by
  have hb : (2 : ℕ) ^ a ≠ 0 := pow_ne_zero _ (by decide)
  have hc0 : c ≠ 0 := hc.pos.ne'
  have h2c : ¬ 2 ∣ c := by obtain ⟨i, hi⟩ := hc; omega
  have h2 : 2 ∉ c.primeFactors := fun h => h2c (Nat.dvd_of_mem_primeFactors h)
  have hfac (p : ℕ) : (2 ^ a * c).factorization p =
      (if 2 = p then a else 0) + c.factorization p := by
    rw [Nat.factorization_mul hb hc0, Nat.prime_two.factorization_pow]
    simp only [Finsupp.add_apply, Finsupp.single_apply, eq_comm]
  have h2val : c.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd h2c
  rw [Nat.primeFactors_mul hb hc0, Nat.primeFactors_prime_pow ha.ne' Nat.prime_two,
    Finset.singleton_union, Finset.prod_insert h2, hfac]
  simp only [if_true, h2val, add_zero, Nat.add_comm 1 (2 ^ a)]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have he : 2 ≠ p := fun e => h2 (e ▸ hp)
  rw [hfac, if_neg he, zero_add]

/-- A Mersenne prime `q > 3` cannot divide `2 ^ a + 1` (from desk note #128653 by `@witeg4`). -/
theorem mersenne_not_dvd_seed {q k a : ℕ} (hq : q.Prime) (hq3 : 3 < q)
    (hk : q + 1 = 2 ^ k) : ¬ q ∣ 2 ^ a + 1 := by
  have hform : q = mersenne k := by unfold mersenne; omega
  have hkp : k.Prime := Nat.Prime.of_mersenne (hform ▸ hq)
  have hk2 : k ≠ 2 := by rintro rfl; norm_num at hk; omega
  have hko := hkp.odd_of_ne_two hk2
  intro hd
  have hqz := ZMod.natCast_self q
  have he : (2 : ZMod q) ^ k = 1 := by
    simpa [hqz] using congrArg (fun t : ℕ => (t : ZMod q)) hk.symm
  have hz : (2 : ZMod q) ^ a + 1 = 0 := by
    simpa using (ZMod.natCast_eq_zero_iff _ q).mpr hd
  have hn : (2 : ZMod q) ^ a = -1 := by linear_combination hz
  have bad : (1 : ZMod q) = -1 := calc
    1 = ((2 : ZMod q) ^ k) ^ a := by simp [he]
    _ = ((2 : ZMod q) ^ a) ^ k := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = -1 := by rw [hn, hko.neg_one_pow]
  have two : (2 : ZMod q) = 0 := by linear_combination bad
  have hdiv : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp (by simpa using two)
  have := Nat.le_of_dvd (by decide : 0 < 2) hdiv
  omega

/-- Every Mersenne prime `q > 3` in `S` divides either `σ*(c)` or `1 + p` for a strictly larger
non-Mersenne prime `p ∈ S` (from desk note #128653 by `@witeg4`). -/
theorem mersenne_trace_factor {q k a σ b : ℕ} {S : Finset ℕ} (hq : q.Prime) (hq3 : 3 < q)
    (hk : q + 1 = 2 ^ k) (hqS : q ∈ S) (hodd : ∀ p ∈ S, Odd p)
    (hbal : ((2 ^ a + 1) * σ) * (∏ p ∈ S, (1 + p)) = (2 * b) * (∏ p ∈ S, p)) :
    q ∣ σ ∨ ∃ p ∈ S, q < p ∧ q ∣ (1 + p) ∧ ordCompl[2] (1 + p) ≠ 1 := by
  have hprod : q ∣ ∏ p ∈ S, p := Finset.dvd_prod_of_mem id hqS
  have hd := dvd_mul_of_dvd_right hprod (2 * b)
  rw [← hbal] at hd
  rcases hq.dvd_mul.mp hd with hleft | hright
  · exact Or.inl ((hq.dvd_mul.mp hleft).resolve_left (mersenne_not_dvd_seed hq hq3 hk))
  · obtain ⟨p, hp, hdp⟩ := (hq.prime.dvd_finsetProd_iff _).mp hright
    have hlo := Nat.le_of_dvd (by omega : 0 < 1 + p) hdp
    have hqo := hq.odd_of_ne_two (by omega)
    have hpo := hodd p hp
    have hlt : q < p := by
      by_contra! h
      have eq : q = p ∨ q = 1 + p := by omega
      rcases eq with rfl | h'
      · have : q ∣ 1 := (Nat.dvd_add_iff_left (dvd_refl q)).mpr hdp
        exact hq.not_dvd_one this
      · obtain ⟨i, hi⟩ := hpo
        obtain ⟨j, hj⟩ := hqo
        omega
    refine Or.inr ⟨p, hp, hlt, hdp, ?_⟩
    intro h1
    have hpow := Nat.ordProj_mul_ordCompl_eq_self (1 + p) 2
    rw [h1, mul_one] at hpow
    rw [← hpow] at hdp
    have hq2 := hq.dvd_of_dvd_pow hdp
    have := Nat.le_of_dvd (by decide : 0 < 2) hq2
    omega

/-- Exact odd-part balance identity obtained by cancelling powers of `2` from the balance equation. -/
theorem odd_balance_eq {a c : ℕ} {S : Finset ℕ} (ha : 0 < a) (hc : Odd c)
    (hp : ∀ p ∈ S, p.Prime ∧ p ≠ 2)
    (hbal : (∏ p ∈ (2 ^ a * c).primeFactors, (1 + p ^ (2 ^ a * c).factorization p)) *
        (∏ p ∈ S, (1 + p)) = (2 * (2 ^ a * c)) * (∏ p ∈ S, p)) :
    (2 ^ a + 1) * ordCompl[2] (∏ p ∈ c.primeFactors, (1 + p ^ c.factorization p)) *
      (∏ p ∈ S, ordCompl[2] (1 + p)) = c * (∏ p ∈ S, p) := by
  let σ := ∏ p ∈ c.primeFactors, (1 + p ^ c.factorization p)
  have hσ0 : σ ≠ 0 := (Finset.prod_pos fun _ _ => by omega).ne'
  rw [sigma_power_two_times ha hc] at hbal
  change ((2 ^ a + 1) * σ) * (∏ p ∈ S, (1 + p)) = (2 * (2 ^ a * c)) * (∏ p ∈ S, p) at hbal
  let vL := σ.factorization 2 + ∑ p ∈ S, (1 + p).factorization 2
  let oddL := (2 ^ a + 1) * ordCompl[2] σ * (∏ p ∈ S, ordCompl[2] (1 + p))
  let oddR := c * (∏ p ∈ S, p)
  have hprod_split :
      (∏ p ∈ S, (1 + p)) =
        2 ^ (∑ p ∈ S, (1 + p).factorization 2) * (∏ p ∈ S, ordCompl[2] (1 + p)) := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => (Nat.ordProj_mul_ordCompl_eq_self (1 + p) 2).symm
  have hL : 2 ^ vL * oddL = ((2 ^ a + 1) * σ) * (∏ p ∈ S, (1 + p)) := by
    have hσ_split : 2 ^ σ.factorization 2 * ordCompl[2] σ = σ :=
      Nat.ordProj_mul_ordCompl_eq_self σ 2
    calc 2 ^ vL * oddL
        = (2 ^ a + 1) * (2 ^ σ.factorization 2 * ordCompl[2] σ) *
            (2 ^ (∑ p ∈ S, (1 + p).factorization 2) * (∏ p ∈ S, ordCompl[2] (1 + p))) := by
          dsimp [vL, oddL]; rw [pow_add]; ring
      _ = ((2 ^ a + 1) * σ) * (∏ p ∈ S, (1 + p)) := by rw [hσ_split, ← hprod_split]
  have hR : 2 ^ (a + 1) * oddR = (2 * (2 ^ a * c)) * (∏ p ∈ S, p) := by
    dsimp [oddR]; rw [pow_succ]; ring
  have heq : 2 ^ vL * oddL = 2 ^ (a + 1) * oddR := hL.trans (hbal.trans hR.symm)
  have hoddL : ¬ 2 ∣ oddL := by
    have h1 : ¬ 2 ∣ 2 ^ a + 1 := by
      have : Odd (2 ^ a + 1) := (even_two.pow_of_ne_zero ha.ne').add_odd odd_one
      obtain ⟨k, hk⟩ := this; omega
    have h2 : ¬ 2 ∣ ordCompl[2] σ := Nat.not_dvd_ordCompl Nat.prime_two hσ0
    have h3 : ¬ 2 ∣ ∏ p ∈ S, ordCompl[2] (1 + p) := by
      intro hd
      obtain ⟨p, _, hdp⟩ := (Nat.prime_two.prime.dvd_finsetProd_iff _).mp hd
      exact Nat.not_dvd_ordCompl Nat.prime_two (by omega : 1 + p ≠ 0) hdp
    intro hd
    rcases Nat.prime_two.dvd_mul.mp hd with h12 | h3'
    · rcases Nat.prime_two.dvd_mul.mp h12 with h1' | h2'
      · exact h1 h1'
      · exact h2 h2'
    · exact h3 h3'
  have hoddR : ¬ 2 ∣ oddR := by
    have h1 : ¬ 2 ∣ c := by obtain ⟨k, hk⟩ := hc; omega
    have h2 : ¬ 2 ∣ ∏ p ∈ S, p := by
      intro hd
      obtain ⟨p, hpS, hdp⟩ := (Nat.prime_two.prime.dvd_finsetProd_iff _).mp hd
      have hpe := ((hp p hpS).1.dvd_iff_eq (by decide : 2 ≠ 1)).mp hdp
      exact (hp p hpS).2 hpe
    intro hd
    rcases Nat.prime_two.dvd_mul.mp hd with h1' | h2'
    · exact h1 h1'
    · exact h2 h2'
  have hoddL0 : oddL ≠ 0 := by intro h; rw [h] at hoddL; exact hoddL (dvd_zero 2)
  have hoddR0 : oddR ≠ 0 := by intro h; rw [h] at hoddR; exact hoddR (dvd_zero 2)
  have hv : vL = a + 1 := by
    have hf := congrArg (fun n : ℕ => n.factorization 2) heq
    rw [Nat.factorization_mul (pow_ne_zero _ (by decide)) hoddL0,
      Nat.factorization_mul (pow_ne_zero _ (by decide)) hoddR0,
      Finsupp.add_apply, Finsupp.add_apply,
      Nat.prime_two.factorization_pow, Nat.prime_two.factorization_pow,
      Finsupp.single_eq_same, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hoddL,
      Nat.factorization_eq_zero_of_not_dvd hoddR,
      add_zero, add_zero] at hf
    exact hf
  rw [hv] at heq
  exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos (a + 1)) heq

private theorem cardFactors_prod {s : Finset ℕ} {f : ℕ → ℕ} (hf : ∀ x ∈ s, f x ≠ 0) :
    cardFactors (∏ x ∈ s, f x) = ∑ x ∈ s, cardFactors (f x) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx,
      cardFactors_mul (hf x (Finset.mem_insert_self x s))
        (Finset.prod_ne_zero_iff.mpr fun y hy => hf y (Finset.mem_insert_of_mem hy)),
      ih (fun y hy => hf y (Finset.mem_insert_of_mem hy))]

/-- Exact prime-factor multiplicity conservation law relating simple Mersenne primes to
seed prime factors and shift branching. -/
theorem omega_conservation {a c : ℕ} {S : Finset ℕ} (ha : 0 < a) (hc : Odd c)
    (hp : ∀ p ∈ S, p.Prime ∧ p ≠ 2)
    (hbal : (∏ p ∈ (2 ^ a * c).primeFactors, (1 + p ^ (2 ^ a * c).factorization p)) *
        (∏ p ∈ S, (1 + p)) = (2 * (2 ^ a * c)) * (∏ p ∈ S, p)) :
    (S.filter (fun q => ordCompl[2] (1 + q) = 1)).card + cardFactors c =
      cardFactors (2 ^ a + 1) +
        cardFactors (ordCompl[2] (∏ p ∈ c.primeFactors, (1 + p ^ c.factorization p))) +
        ∑ p ∈ S, (cardFactors (ordCompl[2] (1 + p)) - 1) := by
  let σ := ∏ p ∈ c.primeFactors, (1 + p ^ c.factorization p)
  have hσ0 : σ ≠ 0 := (Finset.prod_pos fun _ _ => by omega).ne'
  have hσodd0 : ordCompl[2] σ ≠ 0 := (Nat.ordCompl_pos 2 hσ0).ne'
  have hd0 : ∀ p ∈ S, ordCompl[2] (1 + p) ≠ 0 := fun p _ =>
    (Nat.ordCompl_pos 2 (by omega : 1 + p ≠ 0)).ne'
  have hS0 : (∏ p ∈ S, p) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p h => (hp p h).1.ne_zero
  have hD0 : (∏ p ∈ S, ordCompl[2] (1 + p)) ≠ 0 := Finset.prod_ne_zero_iff.mpr hd0
  have hodd := odd_balance_eq ha hc hp hbal
  have hcf := congrArg cardFactors hodd
  rw [cardFactors_mul (mul_ne_zero (by positivity) hσodd0) hD0,
    cardFactors_mul (by positivity) hσodd0,
    cardFactors_mul hc.pos.ne' hS0,
    cardFactors_prod hd0,
    cardFactors_prod (fun p h => (hp p h).1.ne_zero)] at hcf
  have hSones : ∑ p ∈ S, cardFactors p = S.card :=
    (Finset.sum_congr rfl fun p h => cardFactors_apply_prime (hp p h).1).trans (by simp)
  rw [hSones] at hcf
  have hpt : ∀ p ∈ S,
      (if ordCompl[2] (1 + p) = 1 then 1 else 0) + cardFactors (ordCompl[2] (1 + p)) =
        1 + (cardFactors (ordCompl[2] (1 + p)) - 1) := by
    intro p hpS
    have h0 := hd0 p hpS
    have hzero := @cardFactors_eq_zero_iff_eq_zero_or_one (ordCompl[2] (1 + p))
    split_ifs with h1
    · rw [h1]; simp
    · have hpos : cardFactors (ordCompl[2] (1 + p)) ≠ 0 := fun hz => by
        rcases hzero.mp hz with h | h
        · exact h0 h
        · exact h1 h
      omega
  have hsum := Finset.sum_congr rfl hpt
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
    ← Finset.card_filter] at hsum
  change (S.filter (fun q => ordCompl[2] (1 + q) = 1)).card +
      ∑ p ∈ S, cardFactors (ordCompl[2] (1 + p)) =
      S.card + ∑ p ∈ S, (cardFactors (ordCompl[2] (1 + p)) - 1) at hsum
  dsimp only [σ] at hcf
  omega

/-- Every prime in `S` is fed by `2 ^ a + 1`, by `σ*(c)`, or by `1 + p` for some non-Mersenne
`p ∈ S`. -/
theorem feeding_cover {a c : ℕ} {S : Finset ℕ} (ha : 0 < a) (hc : Odd c)
    (hp : ∀ p ∈ S, p.Prime ∧ ¬ p ∣ 2 ^ a * c)
    (hbal : (∏ p ∈ (2 ^ a * c).primeFactors, (1 + p ^ (2 ^ a * c).factorization p)) *
        (∏ p ∈ S, (1 + p)) = (2 * (2 ^ a * c)) * (∏ p ∈ S, p)) :
    S ⊆ S.filter (fun p => p ∣ 2 ^ a + 1) ∪
        S.filter (fun p => p ∣ ∏ q ∈ c.primeFactors, (1 + q ^ c.factorization q)) ∪
        (S.filter (fun p => ordCompl[2] (1 + p) ≠ 1)).biUnion
          (fun p => S.filter (fun r => r ∣ 1 + p)) := by
  let σ := ∏ q ∈ c.primeFactors, (1 + q ^ c.factorization q)
  rw [sigma_power_two_times ha hc] at hbal
  intro r hrS
  have hrp : r.Prime := (hp r hrS).1
  have hr2 : r ≠ 2 := fun h => (hp r hrS).2 (h ▸ dvd_mul_of_dvd_left (dvd_pow_self 2 ha.ne') c)
  have hd : r ∣ ((2 ^ a + 1) * σ) * (∏ p ∈ S, (1 + p)) := by
    rw [hbal]
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem id hrS) (2 * (2 ^ a * c))
  rcases hrp.dvd_mul.mp hd with hleft | hright
  · rcases hrp.dvd_mul.mp hleft with hseed | hsig
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hrS, hseed⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hrS, hsig⟩))
  · obtain ⟨p, hpS, hrp1⟩ := (hrp.prime.dvd_finsetProd_iff _).mp hright
    refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p, ?_, Finset.mem_filter.mpr ⟨hrS, hrp1⟩⟩)
    refine Finset.mem_filter.mpr ⟨hpS, fun h1 => ?_⟩
    have hpow := Nat.ordProj_mul_ordCompl_eq_self (1 + p) 2
    rw [h1, mul_one] at hpow
    rw [← hpow] at hrp1
    have hr2' := hrp.dvd_of_dvd_pow hrp1
    have := Nat.le_of_dvd (by decide : 0 < 2) hr2'
    have := hrp.two_le
    omega

/-- Counting the feeding cover bounds the number of simple Mersenne primes by the seed factors
in `S`, the fixed core constant `ω(σ*(c))`, and total shift branching inside `S`. -/
theorem mersenne_count_le {a c : ℕ} {S : Finset ℕ} (ha : 0 < a) (hc : Odd c)
    (hp : ∀ p ∈ S, p.Prime ∧ ¬ p ∣ 2 ^ a * c)
    (hbal : (∏ p ∈ (2 ^ a * c).primeFactors, (1 + p ^ (2 ^ a * c).factorization p)) *
        (∏ p ∈ S, (1 + p)) = (2 * (2 ^ a * c)) * (∏ p ∈ S, p)) :
    (S.filter (fun q => ordCompl[2] (1 + q) = 1)).card ≤
      (S.filter (fun p => p ∣ 2 ^ a + 1)).card +
      (∏ q ∈ c.primeFactors, (1 + q ^ c.factorization q)).primeFactors.card +
      ∑ p ∈ S, ((S.filter (fun r => r ∣ 1 + p)).card - 1) := by
  let σ := ∏ q ∈ c.primeFactors, (1 + q ^ c.factorization q)
  let M := S.filter (fun q => ordCompl[2] (1 + q) = 1)
  let N := S.filter (fun p => ordCompl[2] (1 + p) ≠ 1)
  let Rseed := S.filter (fun p => p ∣ 2 ^ a + 1)
  let Rsig := S.filter (fun p => p ∣ σ)
  let C (p : ℕ) := S.filter (fun r => r ∣ 1 + p)
  have hσ0 : σ ≠ 0 := (Finset.prod_pos fun _ _ => by omega).ne'
  have hcov := feeding_cover ha hc hp hbal
  have hcard1 : S.card ≤ (Rseed ∪ Rsig ∪ N.biUnion C).card := Finset.card_le_card hcov
  have hcard2 : (Rseed ∪ Rsig ∪ N.biUnion C).card ≤ Rseed.card + Rsig.card + (N.biUnion C).card :=
    (Finset.card_union_le (Rseed ∪ Rsig) (N.biUnion C)).trans
      (Nat.add_le_add_right (Finset.card_union_le Rseed Rsig) _)
  have hcard3 : (N.biUnion C).card ≤ ∑ p ∈ N, (C p).card := Finset.card_biUnion_le
  have hsig_sub : Rsig ⊆ σ.primeFactors := by
    intro p hpR
    obtain ⟨hpS, hpσ⟩ := Finset.mem_filter.mp hpR
    exact Nat.mem_primeFactors.mpr ⟨(hp p hpS).1, hpσ, hσ0⟩
  have hsig_le : Rsig.card ≤ σ.primeFactors.card := Finset.card_le_card hsig_sub
  have hN_sum : ∑ p ∈ N, (C p).card ≤ N.card + ∑ p ∈ N, ((C p).card - 1) := by
    have hpt : ∀ p ∈ N, (C p).card ≤ 1 + ((C p).card - 1) := fun p _ => by omega
    calc ∑ p ∈ N, (C p).card
        ≤ ∑ p ∈ N, (1 + ((C p).card - 1)) := Finset.sum_le_sum hpt
      _ = N.card + ∑ p ∈ N, ((C p).card - 1) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  have hbranch_le : ∑ p ∈ N, ((C p).card - 1) ≤ ∑ p ∈ S, ((C p).card - 1) :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ S)
  have hpart : M.card + N.card = S.card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
    congr 1
    ext q
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  change M.card ≤ Rseed.card + σ.primeFactors.card + ∑ p ∈ S, ((C p).card - 1)
  omega

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R2_H2_R3.H1 := by
  intro h1 h2 c hc powerful
  obtain ⟨K1, hK1⟩ := h1 c hc powerful
  obtain ⟨K2, hK2⟩ := h2 c hc powerful
  refine ⟨K1 + (∏ q ∈ c.primeFactors, (1 + q ^ c.factorization q)).primeFactors.card + K2, ?_⟩
  intro a S b u ha hS hsub hp hbal
  have hbound := mersenne_count_le (by omega : 0 < a) hc hp hbal
  have h1' := hK1 a S ha hS hsub hp hbal
  have h2' := hK2 a S ha hS hsub hp hbal
  omega

end OMA.R_Erdos1052_erdos_1052_R2_H2_R3_H1_R1
