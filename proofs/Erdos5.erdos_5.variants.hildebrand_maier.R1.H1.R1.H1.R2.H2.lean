import OMAReductions.R_Erdos5_erdos_5_variants_hildebrand_maier_R1_H1_R1_H1_R2

/-!
# Second-Moment Upper Bound for Primes in Logarithmic Intervals

We prove `OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_R1_H1_R1_H1_R2.H2`: for every `C > 0`,
there exists `b > 0` such that for all sufficiently large `x`, with `h = ⌈C * log x⌉₊`,
`∑ r ∈ range x, (#{p ∈ (r - h, r] : p prime})^2 ≤ b * x`.

## Proof outline
1. Expand the squared prime count into a diagonal term `≤ h * π(x)` and off-diagonal prime-pair
   terms `≤ 2 * h * (h + ∑_{0 < d < h, Even d} #{p < x : p, p + d prime})`.
2. For each positive even `d`, apply the two-dimensional Selberg upper-bound sieve on squarefree
   divisors `m ≤ Z` of `n * (n + d)` with optimal weights `λ_m`, obtaining
   `#{p < x : p, p + d prime} ≤ Z + x / S_d + Z^4`.
3. Bound the Selberg denominator `S_d` from below by `((φ(d) / d) * log (M + 1))^2` (for
   `M^2 ≤ Z`) via finite geometric-series expansion grouped by the squarefree radical `rad(a * b)`.
4. Bound `∑_{1 ≤ d ≤ h} (d / φ(d))^2 ≤ exp 3 * h` by expanding into squarefree divisors and
   applying `1 + u ≤ exp u` to a telescoping upper bound.
5. Choose `M = ⌊x^(1/10)⌋₊`, `Z = M^2`, and combine with `Chebyshev.eventually_primeCounting_le`.
-/

namespace OMA.PrimeShortIntervalSecondMoment

open Finset Filter Real
open scoped BigOperators Classical

/- ### Step 1: Combinatorial expansion of the second moment -/

private lemma card_odd_diff_prime_pairs_le_one (x d : ℕ) (hd : ¬ Even d) :
    ((range x).filter fun p => p.Prime ∧ (p + d).Prime).card ≤ 1 := by
  have hsub : ((range x).filter fun p => p.Prime ∧ (p + d).Prime) ⊆ {2} := by
    intro p hp
    simp only [mem_filter, mem_range, mem_singleton] at hp ⊢
    obtain ⟨_, hp_prime, hpd_prime⟩ := hp
    rcases hp_prime.eq_two_or_odd with rfl | hp_odd
    · rfl
    · exfalso
      have hd_odd : d % 2 = 1 := by
        rw [Nat.even_iff] at hd
        omega
      have heven : 2 ∣ p + d := by omega
      have hge : 4 ≤ p + d := by
        have hp3 : 3 ≤ p := by have := hp_prime.two_le; omega
        omega
      have h2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hpd_prime).mp heven
      omega
  exact (card_le_card hsub).trans (by simp)

private lemma second_moment_nat_le (x h : ℕ) :
    ∑ r ∈ range x, ((Ioc (r - h) r).filter Nat.Prime).card ^ 2 ≤
      h * Nat.primeCounting x + 2 * h * h +
        2 * h * ∑ d ∈ (Ioo 0 h).filter Even,
          ((range x).filter fun p => p.Prime ∧ (p + d).Prime).card := by
  have hsq_split : ∀ r : ℕ,
      ((Ioc (r - h) r).filter Nat.Prime).card ^ 2 =
        ((Ioc (r - h) r).filter Nat.Prime).card +
          2 * ∑ p ∈ (Ioc (r - h) r).filter Nat.Prime,
            (((Ioc (r - h) r).filter Nat.Prime).filter (fun q => p < q)).card := by
    intro r
    set S := (Ioc (r - h) r).filter Nat.Prime
    have h1 : S.card ^ 2 = ∑ p ∈ S, ∑ q ∈ S, 1 := by simp [sq]
    rw [h1]
    have hpart : ∀ p ∈ S,
        (∑ q ∈ S, (1 : ℕ)) = 1 + (S.filter (fun q => p < q)).card +
          (S.filter (fun q => q < p)).card := by
      intro p hp
      have hU : S = {p} ∪ (S.filter (fun q => p < q) ∪ S.filter (fun q => q < p)) := by
        ext q
        simp only [mem_union, mem_singleton, mem_filter]
        constructor
        · intro hq
          rcases lt_trichotomy p q with hlt | rfl | hgt
          · right; left; exact ⟨hq, hlt⟩
          · left; rfl
          · right; right; exact ⟨hq, hgt⟩
        · rintro (rfl | ⟨hq, _⟩ | ⟨hq, _⟩) <;> assumption
      have hd1 : Disjoint ({p} : Finset ℕ)
          (S.filter (fun q => p < q) ∪ S.filter (fun q => q < p)) := by
        rw [disjoint_singleton_left]
        simp only [mem_union, mem_filter]
        rintro (⟨_, hlt⟩ | ⟨_, hgt⟩) <;> omega
      have hd2 : Disjoint (S.filter (fun q => p < q)) (S.filter (fun q => q < p)) := by
        rw [disjoint_left]
        intro q hq1 hq2
        simp only [mem_filter] at hq1 hq2
        omega
      conv_lhs => rw [hU]
      rw [sum_union hd1, sum_union hd2]
      simp [add_assoc]
    rw [sum_congr rfl hpart]
    simp only [sum_add_distrib, sum_const, smul_eq_mul, mul_one]
    have hsym : (∑ p ∈ S, (S.filter (fun q => q < p)).card) =
        ∑ p ∈ S, (S.filter (fun q => p < q)).card := by
      have hL : (∑ p ∈ S, (S.filter (fun q => q < p)).card) =
          ∑ p ∈ S, ∑ q ∈ S, if q < p then 1 else 0 :=
        sum_congr rfl fun p _ => by rw [card_filter]
      have hR : (∑ p ∈ S, (S.filter (fun q => p < q)).card) =
          ∑ p ∈ S, ∑ q ∈ S, if p < q then 1 else 0 :=
        sum_congr rfl fun p _ => by rw [card_filter]
      rw [hL, hR, sum_comm]
    omega
  simp_rw [hsq_split, sum_add_distrib, ← mul_sum]
  have hdiag : ∑ r ∈ range x, ((Ioc (r - h) r).filter Nat.Prime).card ≤
      h * Nat.primeCounting x := by
    calc ∑ r ∈ range x, ((Ioc (r - h) r).filter Nat.Prime).card
        = ∑ r ∈ range x, ∑ p ∈ (range x).filter Nat.Prime,
            if r - h < p ∧ p ≤ r then 1 else 0 := by
          refine sum_congr rfl fun r hr => ?_
          rw [card_eq_sum_ones, ← sum_filter]
          refine sum_congr ?_ fun _ _ => rfl
          ext p
          simp only [mem_filter, mem_Ioc, mem_range]
          have hrx := mem_range.mp hr
          constructor
          · rintro ⟨⟨h1, h2⟩, hp⟩; exact ⟨⟨by omega, hp⟩, h1, h2⟩
          · rintro ⟨⟨_, hp⟩, h1, h2⟩; exact ⟨⟨h1, h2⟩, hp⟩
      _ = ∑ p ∈ (range x).filter Nat.Prime, ∑ r ∈ range x,
            if r - h < p ∧ p ≤ r then 1 else 0 := sum_comm
      _ ≤ ∑ p ∈ (range x).filter Nat.Prime, h := by
          refine sum_le_sum fun p _ => ?_
          rw [← card_filter]
          have hsub : (range x).filter (fun r => r - h < p ∧ p ≤ r) ⊆ Ico p (p + h) := by
            intro r hr
            simp only [mem_filter, mem_range, mem_Ico] at hr ⊢
            omega
          exact (card_le_card hsub).trans (by simp)
      _ = ((range x).filter Nat.Prime).card * h := by simp
      _ ≤ Nat.primeCounting x * h := by
          refine Nat.mul_le_mul_right h ?_
          rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
          exact card_le_card (filter_subset_filter _ (range_mono (Nat.le_succ x)))
      _ = h * Nat.primeCounting x := mul_comm _ _
  have hoff : ∑ r ∈ range x, ∑ p ∈ (Ioc (r - h) r).filter Nat.Prime,
        (((Ioc (r - h) r).filter Nat.Prime).filter (fun q => p < q)).card ≤
      h * h + h * ∑ d ∈ (Ioo 0 h).filter Even,
        ((range x).filter fun p => p.Prime ∧ (p + d).Prime).card := by
    have hstep1 : ∑ r ∈ range x, ∑ p ∈ (Ioc (r - h) r).filter Nat.Prime,
          (((Ioc (r - h) r).filter Nat.Prime).filter (fun q => p < q)).card ≤
        ∑ d ∈ Ioo 0 h, h * ((range x).filter fun p => p.Prime ∧ (p + d).Prime).card := by
      have hrew : ∀ r ∈ range x,
          ∑ p ∈ (Ioc (r - h) r).filter Nat.Prime,
            (((Ioc (r - h) r).filter Nat.Prime).filter (fun q => p < q)).card =
          ∑ d ∈ Ioo 0 h, ∑ p ∈ (range x).filter (fun p => p.Prime ∧ (p + d).Prime),
            if r - h < p ∧ p + d ≤ r then 1 else 0 := by
        intro r hr
        have hrx := mem_range.mp hr
        calc ∑ p ∈ (Ioc (r - h) r).filter Nat.Prime,
              (((Ioc (r - h) r).filter Nat.Prime).filter (fun q => p < q)).card
            = ∑ p ∈ (range x).filter Nat.Prime,
                if r - h < p ∧ p ≤ r then
                  ∑ d ∈ Ioo 0 h, if (p + d).Prime ∧ p + d ≤ r then 1 else 0
                else 0 := by
              rw [← sum_filter]
              refine sum_congr ?_ fun p hp => ?_
              · ext p
                simp only [mem_filter, mem_Ioc, mem_range]
                constructor
                · rintro ⟨⟨h1, h2⟩, hp⟩; exact ⟨⟨by omega, hp⟩, h1, h2⟩
                · rintro ⟨⟨_, hp⟩, h1, h2⟩; exact ⟨⟨h1, h2⟩, hp⟩
              · simp only [mem_filter] at hp
                rw [card_eq_sum_ones, ← sum_filter]
                refine sum_bij (fun q _ => q - p) ?_ ?_ ?_ (fun _ _ => rfl)
                · intro q hq
                  simp only [mem_filter, mem_Ioc, mem_Ioo] at hq ⊢
                  refine ⟨⟨by omega, by omega⟩, ?_, by omega⟩
                  rw [Nat.add_sub_of_le (le_of_lt hq.2)]
                  exact hq.1.2
                · intro q₁ hq₁ q₂ hq₂ heq
                  simp only [mem_filter] at hq₁ hq₂
                  omega
                · intro d hd
                  simp only [mem_filter, mem_Ioo] at hd
                  refine ⟨p + d, ?_, by omega⟩
                  simp only [mem_filter, mem_Ioc]
                  exact ⟨⟨⟨by omega, hd.2.2⟩, hd.2.1⟩, by omega⟩
          _ = ∑ p ∈ (range x).filter Nat.Prime, ∑ d ∈ Ioo 0 h,
                if r - h < p ∧ (p + d).Prime ∧ p + d ≤ r then 1 else 0 := by
              refine sum_congr rfl fun p _ => ?_
              by_cases hc : r - h < p ∧ p ≤ r
              · rw [if_pos hc]
                refine sum_congr rfl fun d hd => ?_
                have hd0 := (mem_Ioo.mp hd).1
                by_cases h2 : (p + d).Prime ∧ p + d ≤ r
                · rw [if_pos h2, if_pos ⟨hc.1, h2⟩]
                · rw [if_neg h2, if_neg (fun h' => h2 h'.2)]
              · rw [if_neg hc]
                symm
                refine sum_eq_zero fun d hd => ?_
                have hd0 := (mem_Ioo.mp hd).1
                rw [if_neg]
                intro h'
                exact hc ⟨h'.1, by omega⟩
          _ = ∑ d ∈ Ioo 0 h, ∑ p ∈ (range x).filter Nat.Prime,
                if r - h < p ∧ (p + d).Prime ∧ p + d ≤ r then 1 else 0 := sum_comm
          _ = ∑ d ∈ Ioo 0 h, ∑ p ∈ (range x).filter (fun p => p.Prime ∧ (p + d).Prime),
                if r - h < p ∧ p + d ≤ r then 1 else 0 := by
              refine sum_congr rfl fun d _ => ?_
              rw [← sum_filter, ← sum_filter]
              refine sum_congr ?_ fun _ _ => rfl
              ext p
              simp only [mem_filter, mem_range]
              tauto
      rw [sum_congr rfl hrew, sum_comm]
      refine sum_le_sum fun d hd => ?_
      rw [sum_comm]
      calc ∑ p ∈ (range x).filter (fun p => p.Prime ∧ (p + d).Prime),
            ∑ r ∈ range x, (if r - h < p ∧ p + d ≤ r then 1 else 0)
          ≤ ∑ p ∈ (range x).filter (fun p => p.Prime ∧ (p + d).Prime), h := by
            refine sum_le_sum fun p _ => ?_
            rw [← card_filter]
            have hsub : (range x).filter (fun r => r - h < p ∧ p + d ≤ r) ⊆ Ico p (p + h) := by
              intro r hr
              simp only [mem_filter, mem_range, mem_Ico] at hr ⊢
              omega
            exact (card_le_card hsub).trans (by simp)
        _ = h * ((range x).filter fun p => p.Prime ∧ (p + d).Prime).card := by
            simp [mul_comm]
    calc ∑ r ∈ range x, ∑ p ∈ (Ioc (r - h) r).filter Nat.Prime,
          (((Ioc (r - h) r).filter Nat.Prime).filter (fun q => p < q)).card
        ≤ ∑ d ∈ Ioo 0 h, h * ((range x).filter fun p => p.Prime ∧ (p + d).Prime).card := hstep1
      _ = (∑ d ∈ (Ioo 0 h).filter Even,
            h * ((range x).filter fun p => p.Prime ∧ (p + d).Prime).card) +
          (∑ d ∈ (Ioo 0 h).filter (fun d => ¬ Even d),
            h * ((range x).filter fun p => p.Prime ∧ (p + d).Prime).card) := by
          rw [sum_filter_add_sum_filter_not]
      _ ≤ (h * ∑ d ∈ (Ioo 0 h).filter Even,
            ((range x).filter fun p => p.Prime ∧ (p + d).Prime).card) +
          (∑ d ∈ (Ioo 0 h).filter (fun d => ¬ Even d), h) := by
          rw [mul_sum]
          refine Nat.add_le_add_left ?_ _
          refine sum_le_sum fun d hd => ?_
          have h1 := card_odd_diff_prime_pairs_le_one x d (mem_filter.mp hd).2
          exact (Nat.mul_le_mul_left h h1).trans (by simp)
      _ ≤ h * ∑ d ∈ (Ioo 0 h).filter Even,
            ((range x).filter fun p => p.Prime ∧ (p + d).Prime).card + h * h := by
          refine Nat.add_le_add_left ?_ _
          rw [sum_const, smul_eq_mul, mul_comm]
          refine Nat.mul_le_mul_left h ?_
          calc ((Ioo 0 h).filter (fun d => ¬ Even d)).card
              ≤ (Ioo 0 h).card := card_filter_le _ _
            _ ≤ h := by simp [Nat.card_Ioo]
      _ = h * h + h * ∑ d ∈ (Ioo 0 h).filter Even,
            ((range x).filter fun p => p.Prime ∧ (p + d).Prime).card := add_comm _ _
  calc ∑ r ∈ range x, ((Ioc (r - h) r).filter Nat.Prime).card +
        2 * ∑ r ∈ range x, ∑ p ∈ (Ioc (r - h) r).filter Nat.Prime,
          (((Ioc (r - h) r).filter Nat.Prime).filter (fun q => p < q)).card
      ≤ h * Nat.primeCounting x + 2 * (h * h + h * ∑ d ∈ (Ioo 0 h).filter Even,
          ((range x).filter fun p => p.Prime ∧ (p + d).Prime).card) :=
        Nat.add_le_add hdiag (Nat.mul_le_mul_left 2 hoff)
    _ = h * Nat.primeCounting x + 2 * h * h +
        2 * h * ∑ d ∈ (Ioo 0 h).filter Even,
          ((range x).filter fun p => p.Prime ∧ (p + d).Prime).card := by ring

/- ### Step 2: Squarefree arithmetic, Möbius inversion, and local congruence counts -/

private lemma prod_primeFactors_eq_of_squarefree {m : ℕ} (hm : Squarefree m) :
    ∏ p ∈ m.primeFactors, p = m := by
  have hm0 : m ≠ 0 := hm.ne_zero
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hm0]
  rw [Finsupp.prod, Nat.support_factorization]
  refine prod_congr rfl fun p hp => ?_
  have hle : m.factorization p ≤ 1 := hm.natFactorization_le_one p
  have hpos : 0 < m.factorization p :=
    Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hm0
      (Nat.dvd_of_mem_primeFactors hp)
  have heq : m.factorization p = 1 := by omega
  rw [heq, pow_one]

private lemma primeFactors_prod_primes {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    (∏ p ∈ s, p).primeFactors = s := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have ha_prime : a.Prime := hs a (mem_insert_self a s)
    have hs_prime : ∀ p ∈ s, p.Prime := fun p hp => hs p (mem_insert_of_mem hp)
    have hprod_ne : ∏ p ∈ s, p ≠ 0 :=
      prod_ne_zero_iff.mpr fun p hp => (hs_prime p hp).ne_zero
    rw [prod_insert ha, Nat.primeFactors_mul ha_prime.ne_zero hprod_ne,
      ha_prime.primeFactors, ih hs_prime]
    simp

private lemma squarefree_prod_primes {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have ha_prime : a.Prime := hs a (mem_insert_self a s)
    have hs_prime : ∀ p ∈ s, p.Prime := fun p hp => hs p (mem_insert_of_mem hp)
    rw [prod_insert ha, Nat.squarefree_mul_iff]
    refine ⟨?_, ha_prime.squarefree, ih hs_prime⟩
    refine Nat.Coprime.prod_right fun p hp => ?_
    have hp_prime := hs_prime p hp
    have hne : a ≠ p := fun h => ha (h ▸ hp)
    exact (Nat.coprime_primes ha_prime hp_prime).mpr hne

private lemma sum_sqfree_divisors_prod_primeFactors {d : ℕ} (hd : d ≠ 0) (ψ : ℕ → ℝ) :
    ∑ k ∈ d.divisors.filter Squarefree, (∏ p ∈ k.primeFactors, ψ p) =
      ∏ p ∈ d.primeFactors, (1 + ψ p) := by
  rw [Finset.prod_one_add]
  refine Finset.sum_bij (fun k _ => k.primeFactors) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro k hk
    rw [mem_powerset]
    have hkd : k ∣ d := (Nat.mem_divisors.mp (mem_filter.mp hk).1).1
    exact Nat.primeFactors_mono hkd hd
  · intro k₁ hk₁ k₂ hk₂ heq
    have hsq1 : Squarefree k₁ := (mem_filter.mp hk₁).2
    have hsq2 : Squarefree k₂ := (mem_filter.mp hk₂).2
    rw [← prod_primeFactors_eq_of_squarefree hsq1, ← prod_primeFactors_eq_of_squarefree hsq2, heq]
  · intro s hs
    have hs' : s ⊆ d.primeFactors := mem_powerset.mp hs
    have hprimes : ∀ p ∈ s, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hs' hp)
    refine ⟨∏ p ∈ s, p, ?_, primeFactors_prod_primes hprimes⟩
    rw [mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, hd⟩, squarefree_prod_primes hprimes⟩
    exact (Finset.prod_dvd_prod_of_subset s d.primeFactors id hs').trans
      (Nat.prod_primeFactors_dvd d)

private lemma sum_divisors_of_squarefree {m : ℕ} (hm : Squarefree m) (ψ : ℕ → ℝ) :
    ∑ r ∈ m.divisors, (∏ p ∈ r.primeFactors, ψ p) = ∏ p ∈ m.primeFactors, (1 + ψ p) := by
  have hfilt : m.divisors.filter Squarefree = m.divisors := by
    ext r
    simp only [mem_filter, Nat.mem_divisors, and_iff_left_iff_imp]
    intro hr
    exact hm.squarefree_of_dvd hr.1
  rw [← hfilt]
  exact sum_sqfree_divisors_prod_primeFactors hm.ne_zero ψ

private noncomputable def sqMu (m : ℕ) : ℝ :=
  ∏ _p ∈ m.primeFactors, (-1 : ℝ)

private lemma sqMu_one : sqMu 1 = 1 := by
  simp [sqMu]

private lemma sqMu_sq (m : ℕ) : (sqMu m) ^ 2 = 1 := by
  unfold sqMu
  rw [← prod_pow]
  simp

private lemma abs_sqMu (m : ℕ) : |sqMu m| = 1 := by
  have h : |sqMu m| ^ 2 = 1 := by rw [sq_abs, sqMu_sq]
  nlinarith [abs_nonneg (sqMu m)]

private lemma sqMu_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hcop : a.Coprime b) :
    sqMu (a * b) = sqMu a * sqMu b := by
  unfold sqMu
  rw [Nat.primeFactors_mul ha hb, prod_union hcop.disjoint_primeFactors]

private lemma sum_divisors_sqMu {m : ℕ} (hm : Squarefree m) :
    ∑ t ∈ m.divisors, sqMu t = if m = 1 then 1 else 0 := by
  unfold sqMu
  rw [sum_divisors_of_squarefree hm (fun _ => (-1 : ℝ))]
  simp only [add_neg_cancel]
  by_cases hm1 : m = 1
  · subst hm1; simp
  · rw [if_neg hm1]
    have hne : m.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by
      have := hm.ne_zero; omega)
    obtain ⟨p, hp⟩ := hne
    exact prod_eq_zero hp rfl

private def omega (d m : ℕ) : ℕ :=
  ∏ p ∈ m.primeFactors, if p ∣ d then 1 else 2

private lemma omega_pos (d m : ℕ) : 0 < omega d m := by
  unfold omega
  exact prod_pos fun p _ => by split_ifs <;> omega

private lemma omega_le_self {d m : ℕ} (hm : Squarefree m) : omega d m ≤ m := by
  unfold omega
  conv_rhs => rw [← prod_primeFactors_eq_of_squarefree hm]
  refine prod_le_prod' fun p hp => ?_
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  split_ifs <;> omega

private lemma card_zmod_prime_mul_add_eq_zero (d p : ℕ) [NeZero p] (hp : p.Prime) :
    ((Finset.univ : Finset (ZMod p)).filter fun a : ZMod p => a * (a + (d : ZMod p)) = 0).card =
      if p ∣ d then 1 else 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hset : ((Finset.univ : Finset (ZMod p)).filter fun a : ZMod p => a * (a + (d : ZMod p)) = 0) =
      ({0, -(d : ZMod p)} : Finset (ZMod p)) := by
    ext a
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, mul_eq_zero]
    constructor
    · rintro (rfl | h)
      · left; rfl
      · right; exact eq_neg_of_add_eq_zero_left h
    · rintro (rfl | rfl)
      · left; rfl
      · right; simp
  rw [hset]
  by_cases hpd : p ∣ d
  · rw [if_pos hpd]
    have hd0 : (d : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff d p).mpr hpd
    simp [hd0]
  · rw [if_neg hpd]
    have hd0 : (d : ZMod p) ≠ 0 := mt (ZMod.natCast_eq_zero_iff d p).mp hpd
    have hne : (0 : ZMod p) ≠ -(d : ZMod p) := by
      intro h
      exact hd0 (neg_eq_zero.mp h.symm)
    rw [card_pair hne]

private lemma card_zmod_mul_add_eq_zero (d : ℕ) :
    ∀ m : ℕ, [NeZero m] → Squarefree m →
      ((Finset.univ : Finset (ZMod m)).filter fun a : ZMod m => a * (a + (d : ZMod m)) = 0).card =
        omega d m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hneZ hm
    by_cases hm1 : m = 1
    · subst hm1
      have hcard : ((Finset.univ : Finset (ZMod 1)).filter
          fun a : ZMod 1 => a * (a + (d : ZMod 1)) = 0) = {0} := by
        ext a
        simp only [mem_filter, mem_univ, true_and, mem_singleton]
        exact ⟨fun _ => Subsingleton.elim a 0, fun _ => Subsingleton.elim _ _⟩
      rw [hcard]
      simp [omega]
    · have hne : m.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by
        have := hm.ne_zero; omega)
      obtain ⟨p, hp⟩ := hne
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpdvd : p ∣ m := Nat.dvd_of_mem_primeFactors hp
      obtain ⟨m', rfl⟩ := hpdvd
      have hm'_ne : m' ≠ 0 := right_ne_zero_of_mul hm.ne_zero
      have hsq_mul := (Nat.squarefree_mul_iff).mp hm
      have hcop : p.Coprime m' := hsq_mul.1
      have hm'_sq : Squarefree m' := hsq_mul.2.2
      have : NeZero p := ⟨hp_prime.ne_zero⟩
      have : NeZero m' := ⟨hm'_ne⟩
      have hm'_lt : m' < p * m' := by
        have hp2 := hp_prime.two_le
        have hm'1 : 0 < m' := Nat.pos_of_ne_zero hm'_ne
        nlinarith
      let e := ZMod.chineseRemainder hcop
      have hbij : ((Finset.univ : Finset (ZMod (p * m'))).filter
            fun a : ZMod (p * m') => a * (a + (d : ZMod (p * m'))) = 0).card =
          (((Finset.univ : Finset (ZMod p)).filter fun a : ZMod p => a * (a + (d : ZMod p)) = 0) ×ˢ
            ((Finset.univ : Finset (ZMod m')).filter fun a : ZMod m' => a * (a + (d : ZMod m')) = 0)).card := by
        refine Finset.card_bij (fun a _ => e a) ?_ ?_ ?_
        · intro a ha
          simp only [mem_filter, mem_univ, true_and, mem_product] at ha ⊢
          have hmap := congrArg e ha
          simp only [map_mul, map_add, map_natCast, map_zero] at hmap
          exact ⟨congrArg Prod.fst hmap, congrArg Prod.snd hmap⟩
        · intro a₁ _ a₂ _ h; exact e.injective h
        · intro x hx
          simp only [mem_product, mem_filter, mem_univ, true_and] at hx
          refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
          simp only [mem_filter, mem_univ, true_and]
          apply e.injective
          simp only [map_mul, map_add, map_natCast, map_zero, e.apply_symm_apply]
          exact Prod.ext hx.1 hx.2
      rw [hbij, card_product, card_zmod_prime_mul_add_eq_zero d p hp_prime, ih m' hm'_lt hm'_sq]
      unfold omega
      rw [Nat.primeFactors_mul hp_prime.ne_zero hm'_ne, hp_prime.primeFactors,
        singleton_union, prod_insert]
      intro hp_mem
      have := Nat.dvd_of_mem_primeFactors hp_mem
      have hgcd : p ∣ Nat.gcd p m' := Nat.dvd_gcd dvd_rfl this
      rw [hcop.gcd_eq_one] at hgcd
      exact hp_prime.not_dvd_one hgcd

private lemma card_block_dvd_mul_add {d m : ℕ} (hm : Squarefree m) (k : ℕ) :
    ((Ico (k * m) ((k + 1) * m)).filter fun n => m ∣ n * (n + d)).card = omega d m := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  have : NeZero m := ⟨hm.ne_zero⟩
  rw [← card_zmod_mul_add_eq_zero d m hm]
  refine Finset.card_bij (fun n _ => (n : ZMod m)) ?_ ?_ ?_
  · intro n hn
    simp only [mem_filter, mem_Ico, mem_univ, true_and] at hn ⊢
    have hcast := (ZMod.natCast_eq_zero_iff (n * (n + d)) m).mpr hn.2
    simpa [Nat.cast_mul, Nat.cast_add] using hcast
  · intro n₁ hn₁ n₂ hn₂ hcast
    simp only [mem_filter, mem_Ico] at hn₁ hn₂
    have hmod : n₁ % m = n₂ % m := (ZMod.natCast_eq_natCast_iff' n₁ n₂ m).mp hcast
    have hq1 : n₁ / m = k := Nat.div_eq_of_lt_le hn₁.1.1 (by linarith [hn₁.1.2])
    have hq2 : n₂ / m = k := Nat.div_eq_of_lt_le hn₂.1.1 (by linarith [hn₂.1.2])
    rw [← Nat.div_add_mod n₁ m, ← Nat.div_add_mod n₂ m, hq1, hq2, hmod]
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    let n := k * m + a.val
    refine ⟨n, ?_, ?_⟩
    · simp only [mem_filter, mem_Ico]
      refine ⟨⟨by omega, by dsimp only [n]; have := a.val_lt; nlinarith⟩, ?_⟩
      rw [← ZMod.natCast_eq_zero_iff]
      have hn : (n : ZMod m) = a := by simp [n]
      simpa [Nat.cast_mul, Nat.cast_add, hn] using ha
    · simp [n]

private lemma card_range_dvd_mul_add_approx {d m : ℕ} (hm : Squarefree m) (x : ℕ) :
    |(((range x).filter fun n => m ∣ n * (n + d)).card : ℝ) -
        (x : ℝ) * ((omega d m : ℝ) / (m : ℝ))| ≤ (omega d m : ℝ) := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  have hm_rpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
  set q := x / m
  have hlo_sub : ((range q).biUnion fun k =>
      (Ico (k * m) ((k + 1) * m)).filter fun n => m ∣ n * (n + d)) ⊆
      (range x).filter fun n => m ∣ n * (n + d) := by
    intro n hn
    simp only [mem_biUnion, mem_range, mem_filter, mem_Ico] at hn ⊢
    obtain ⟨k, hk, ⟨_, hhi⟩, hdvd⟩ := hn
    have hqm : q * m ≤ x := Nat.div_mul_le_self x m
    have hk1 : (k + 1) * m ≤ q * m := Nat.mul_le_mul_right m (by omega)
    exact ⟨by omega, hdvd⟩
  have hhi_sub : ((range x).filter fun n => m ∣ n * (n + d)) ⊆
      (range (q + 1)).biUnion fun k =>
        (Ico (k * m) ((k + 1) * m)).filter fun n => m ∣ n * (n + d) := by
    intro n hn
    simp only [mem_filter, mem_range, mem_biUnion, mem_Ico] at hn ⊢
    refine ⟨n / m, ?_, ⟨Nat.div_mul_le_self n m, ?_⟩, hn.2⟩
    · have : n / m ≤ x / m := Nat.div_le_div_right hn.1.le
      omega
    · have := Nat.lt_div_mul_add hm_pos (a := n)
      linarith
  have hdisj : ∀ s : ℕ, (Set.PairwiseDisjoint (range s : Set ℕ) fun k =>
      (Ico (k * m) ((k + 1) * m)).filter fun n => m ∣ n * (n + d)) := by
    intro s k₁ _ k₂ _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro n hn₁ hn₂
    simp only [mem_filter, mem_Ico] at hn₁ hn₂
    have hq1 : n / m = k₁ := Nat.div_eq_of_lt_le hn₁.1.1 (by linarith [hn₁.1.2])
    have hq2 : n / m = k₂ := Nat.div_eq_of_lt_le hn₂.1.1 (by linarith [hn₂.1.2])
    exact hne (hq1.symm.trans hq2)
  have hlo_nat : q * omega d m ≤ ((range x).filter fun n => m ∣ n * (n + d)).card := by
    calc q * omega d m
        = ∑ k ∈ range q, ((Ico (k * m) ((k + 1) * m)).filter fun n => m ∣ n * (n + d)).card := by
          simp [card_block_dvd_mul_add hm]
      _ = ((range q).biUnion fun k =>
            (Ico (k * m) ((k + 1) * m)).filter fun n => m ∣ n * (n + d)).card :=
          (card_biUnion (hdisj q)).symm
      _ ≤ ((range x).filter fun n => m ∣ n * (n + d)).card := card_le_card hlo_sub
  have hhi_nat : ((range x).filter fun n => m ∣ n * (n + d)).card ≤ (q + 1) * omega d m := by
    calc ((range x).filter fun n => m ∣ n * (n + d)).card
        ≤ ((range (q + 1)).biUnion fun k =>
            (Ico (k * m) ((k + 1) * m)).filter fun n => m ∣ n * (n + d)).card :=
          card_le_card hhi_sub
      _ = ∑ k ∈ range (q + 1),
            ((Ico (k * m) ((k + 1) * m)).filter fun n => m ∣ n * (n + d)).card :=
          card_biUnion (hdisj (q + 1))
      _ = (q + 1) * omega d m := by simp [card_block_dvd_mul_add hm]
  have hqm1 : (q : ℝ) * (m : ℝ) ≤ (x : ℝ) := by exact_mod_cast Nat.div_mul_le_self x m
  have hqm2 : (x : ℝ) ≤ ((q : ℝ) + 1) * (m : ℝ) := by
    have : x < (q + 1) * m := by
      have := Nat.lt_div_mul_add hm_pos (a := x)
      dsimp only [q]
      linarith
    exact_mod_cast this.le
  have hq_le : (q : ℝ) ≤ (x : ℝ) / (m : ℝ) := (le_div_iff₀ hm_rpos).mpr hqm1
  have hq_ge : (x : ℝ) / (m : ℝ) - 1 ≤ (q : ℝ) := by
    have : (x : ℝ) / (m : ℝ) ≤ (q : ℝ) + 1 := (div_le_iff₀ hm_rpos).mpr hqm2
    linarith
  have hlo_r : (q : ℝ) * (omega d m : ℝ) ≤
      (((range x).filter fun n => m ∣ n * (n + d)).card : ℝ) := by exact_mod_cast hlo_nat
  have hhi_r : (((range x).filter fun n => m ∣ n * (n + d)).card : ℝ) ≤
      ((q : ℝ) + 1) * (omega d m : ℝ) := by exact_mod_cast hhi_nat
  have hom_nn : (0 : ℝ) ≤ (omega d m : ℝ) := Nat.cast_nonneg _
  rw [abs_le]
  constructor
  · have : ((x : ℝ) / (m : ℝ) - 1) * (omega d m : ℝ) ≤ (q : ℝ) * (omega d m : ℝ) :=
      mul_le_mul_of_nonneg_right hq_ge hom_nn
    have hmul : (x : ℝ) * ((omega d m : ℝ) / (m : ℝ)) = (x : ℝ) / (m : ℝ) * (omega d m : ℝ) := by
      ring
    linarith
  · have : ((q : ℝ) + 1) * (omega d m : ℝ) ≤ ((x : ℝ) / (m : ℝ) + 1) * (omega d m : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hom_nn
    have hmul : (x : ℝ) * ((omega d m : ℝ) / (m : ℝ)) = (x : ℝ) / (m : ℝ) * (omega d m : ℝ) := by
      ring
    linarith

/- ### Step 3: Selberg sieve weights and prime-pair upper bound -/

private noncomputable def selbergF (d m : ℕ) : ℝ :=
  ∏ p ∈ m.primeFactors, (p : ℝ) / (if p ∣ d then (1 : ℝ) else 2)

private noncomputable def selbergG (d m : ℕ) : ℝ :=
  ∏ p ∈ m.primeFactors, ((p : ℝ) - (if p ∣ d then (1 : ℝ) else 2)) /
    (if p ∣ d then (1 : ℝ) else 2)

private lemma selbergF_eq_div_omega {d m : ℕ} (hm : Squarefree m) :
    selbergF d m = (m : ℝ) / (omega d m : ℝ) := by
  unfold selbergF omega
  rw [prod_div_distrib]
  congr 1
  · rw [← Nat.cast_prod, prod_primeFactors_eq_of_squarefree hm]
  · rw [Nat.cast_prod]
    refine prod_congr rfl fun p _ => by split_ifs <;> simp

private lemma selbergF_pos (d m : ℕ) : 0 < selbergF d m := by
  unfold selbergF
  refine prod_pos fun p hp => div_pos ?_ (by split_ifs <;> positivity)
  exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos

private lemma selbergG_pos {d : ℕ} (hd_even : Even d) (m : ℕ) : 0 < selbergG d m := by
  unfold selbergG
  refine prod_pos fun p hp => ?_
  have hp_prime := Nat.prime_of_mem_primeFactors hp
  by_cases hpd : p ∣ d
  · rw [if_pos hpd]
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_prime.two_le
    linarith
  · rw [if_neg hpd]
    have hp_ne2 : p ≠ 2 := by
      intro h2; subst h2
      exact hpd (even_iff_two_dvd.mp hd_even)
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
      have := hp_prime.two_le
      exact_mod_cast (show 3 ≤ p by omega)
    linarith

private lemma selbergG_mul {d a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hcop : a.Coprime b) :
    selbergG d (a * b) = selbergG d a * selbergG d b := by
  unfold selbergG
  rw [Nat.primeFactors_mul ha hb, prod_union hcop.disjoint_primeFactors]

private lemma selbergF_eq_sum_divisors_G {d m : ℕ} (hm : Squarefree m) :
    selbergF d m = ∑ r ∈ m.divisors, selbergG d r := by
  unfold selbergG selbergF
  rw [sum_divisors_of_squarefree hm]
  refine prod_congr rfl fun p _ => ?_
  split_ifs <;> ring

private lemma selbergF_div_G_eq_sum_inv_G {d : ℕ} (hd_even : Even d) {m : ℕ} (hm : Squarefree m) :
    selbergF d m / selbergG d m = ∑ t ∈ m.divisors, (selbergG d t)⁻¹ := by
  have hinv : ∀ t : ℕ, (selbergG d t)⁻¹ =
      ∏ p ∈ t.primeFactors,
        (if p ∣ d then (1 : ℝ) else 2) / ((p : ℝ) - (if p ∣ d then (1 : ℝ) else 2)) := by
    intro t
    unfold selbergG
    rw [← prod_inv_distrib]
    refine prod_congr rfl fun p _ => by rw [inv_div]
  simp_rw [hinv]
  rw [sum_divisors_of_squarefree hm]
  unfold selbergF selbergG
  rw [← prod_div_distrib]
  refine prod_congr rfl fun p hp => ?_
  have hp_prime := Nat.prime_of_mem_primeFactors hp
  by_cases hpd : p ∣ d
  · rw [if_pos hpd]
    have hp1 : (p : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp_prime.two_le
      linarith
    field_simp
    ring
  · rw [if_neg hpd]
    have hp_ne2 : p ≠ 2 := fun h2 => hpd (h2 ▸ even_iff_two_dvd.mp hd_even)
    have hp2 : (p : ℝ) - 2 ≠ 0 := by
      have : (3 : ℝ) ≤ p := by have := hp_prime.two_le; exact_mod_cast (show 3 ≤ p by omega)
      linarith
    field_simp
    ring

private lemma selbergF_lcm_mul_gcd {d m₁ m₂ : ℕ} (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0) :
    selbergF d (Nat.lcm m₁ m₂) * selbergF d (Nat.gcd m₁ m₂) = selbergF d m₁ * selbergF d m₂ := by
  unfold selbergF
  have hlcm : (Nat.lcm m₁ m₂).primeFactors = m₁.primeFactors ∪ m₂.primeFactors := by
    ext p
    simp only [Nat.mem_primeFactors, mem_union]
    constructor
    · rintro ⟨hp, hdvd, _⟩
      rcases hp.dvd_mul.mp (hdvd.trans (Nat.lcm_dvd_mul m₁ m₂)) with h | h
      · left; exact ⟨hp, h, hm₁⟩
      · right; exact ⟨hp, h, hm₂⟩
    · rintro (⟨hp, hdvd, _⟩ | ⟨hp, hdvd, _⟩)
      · exact ⟨hp, hdvd.trans (Nat.dvd_lcm_left m₁ m₂), Nat.lcm_ne_zero hm₁ hm₂⟩
      · exact ⟨hp, hdvd.trans (Nat.dvd_lcm_right m₁ m₂), Nat.lcm_ne_zero hm₁ hm₂⟩
  have hgcd : (Nat.gcd m₁ m₂).primeFactors = m₁.primeFactors ∩ m₂.primeFactors := by
    ext p
    simp only [Nat.mem_primeFactors, mem_inter, Nat.dvd_gcd_iff, ne_eq, Nat.gcd_eq_zero_iff, not_and]
    constructor
    · rintro ⟨hp, ⟨h1, h2⟩, _⟩; exact ⟨⟨hp, h1, hm₁⟩, ⟨hp, h2, hm₂⟩⟩
    · rintro ⟨⟨hp, h1, _⟩, ⟨_, h2, _⟩⟩; exact ⟨hp, ⟨h1, h2⟩, fun h => (hm₁ h).elim⟩
  rw [hlcm, hgcd, prod_union_inter]

private lemma selberg_pair_bound {d x Z : ℕ} (hd_even : Even d) (hZ : 1 ≤ Z) :
    let D := (Icc 1 Z).filter Squarefree
    let S := ∑ r ∈ D, (selbergG d r)⁻¹
    (((range x).filter fun p => p.Prime ∧ (p + d).Prime).card : ℝ) ≤
      (Z : ℝ) + (x : ℝ) / S + (Z : ℝ) ^ 4 := by
  intro D S
  have h1D : 1 ∈ D := mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl, hZ⟩, squarefree_one⟩
  have hS_pos : 0 < S := by
    have h1 : 0 < (selbergG d 1)⁻¹ := inv_pos.mpr (selbergG_pos hd_even 1)
    have hle : (selbergG d 1)⁻¹ ≤ S :=
      single_le_sum (fun r _ => (inv_pos.mpr (selbergG_pos hd_even r)).le) h1D
    linarith
  let lam : ℕ → ℝ := fun m =>
    sqMu m * selbergF d m * S⁻¹ * ∑ r ∈ D.filter (m ∣ ·), (selbergG d r)⁻¹
  have hlam1 : lam 1 = 1 := by
    have hfilt : D.filter (1 ∣ ·) = D := by
      ext r; simp
    simp only [lam, sqMu_one, selbergF, Nat.primeFactors_one, prod_empty, one_mul, hfilt]
    exact inv_mul_cancel₀ hS_pos.ne'
  have hlam_abs : ∀ m ∈ D, |lam m| ≤ 1 := by
    intro m hm
    have hm_sq : Squarefree m := (mem_filter.mp hm).2
    have hm_pos : 1 ≤ m := (mem_Icc.mp (mem_filter.mp hm).1).1
    have hsum_nn : 0 ≤ ∑ r ∈ D.filter (m ∣ ·), (selbergG d r)⁻¹ :=
      sum_nonneg fun r _ => (inv_pos.mpr (selbergG_pos hd_even r)).le
    have hstep : |lam m| = selbergF d m * S⁻¹ * ∑ r ∈ D.filter (m ∣ ·), (selbergG d r)⁻¹ := by
      dsimp only [lam]
      rw [abs_mul, abs_mul, abs_mul, abs_sqMu, one_mul,
        abs_of_pos (selbergF_pos d m), abs_of_pos (inv_pos.mpr hS_pos), abs_of_nonneg hsum_nn]
    rw [hstep]
    have hgoal : selbergF d m * ∑ r ∈ D.filter (m ∣ ·), (selbergG d r)⁻¹ ≤ S := by
      let Km := D.filter fun k => m.Coprime k ∧ m * k ≤ Z
      have hfactor : ∑ r ∈ D.filter (m ∣ ·), (selbergG d r)⁻¹ =
          (selbergG d m)⁻¹ * ∑ k ∈ Km, (selbergG d k)⁻¹ := by
        rw [mul_sum]
        refine Finset.sum_bij (fun r _ => r / m) ?_ ?_ ?_ ?_
        · intro r hr
          simp only [mem_filter, mem_Icc, D, Km] at hr ⊢
          obtain ⟨⟨⟨hr1, hrZ⟩, hr_sq⟩, hmr⟩ := hr
          have hmul : m * (r / m) = r := Nat.mul_div_cancel' hmr
          have hsq' := (Nat.squarefree_mul_iff).mp (hmul.symm ▸ hr_sq)
          have hpos : 1 ≤ r / m :=
            Nat.pos_of_ne_zero (right_ne_zero_of_mul (hmul.symm ▸ hr_sq.ne_zero))
          exact ⟨⟨⟨hpos, le_trans (Nat.div_le_self r m) hrZ⟩, hsq'.2.2⟩, hsq'.1, by rw [hmul]; exact hrZ⟩
        · intro r₁ hr₁ r₂ hr₂ heq
          have h1 : m ∣ r₁ := (mem_filter.mp hr₁).2
          have h2 : m ∣ r₂ := (mem_filter.mp hr₂).2
          rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, heq]
        · intro k hk
          simp only [mem_filter, mem_Icc, D, Km] at hk
          obtain ⟨⟨⟨hk1, _⟩, hk_sq⟩, hcop, hle⟩ := hk
          refine ⟨m * k, ?_, Nat.mul_div_cancel_left k (by omega)⟩
          simp only [mem_filter, mem_Icc, D]
          exact ⟨⟨⟨by nlinarith, hle⟩, Nat.squarefree_mul_iff.mpr ⟨hcop, hm_sq, hk_sq⟩⟩,
            dvd_mul_right m k⟩
        · intro r hr
          simp only [mem_filter, D] at hr
          have hmul : m * (r / m) = r := Nat.mul_div_cancel' hr.2
          have hsq' := (Nat.squarefree_mul_iff).mp (hmul.symm ▸ hr.1.2)
          have hk_ne : r / m ≠ 0 := right_ne_zero_of_mul (hmul.symm ▸ hr.1.2.ne_zero)
          conv_lhs => rw [← hmul]
          rw [selbergG_mul hm_sq.ne_zero hk_ne hsq'.1, mul_inv]
      calc selbergF d m * ∑ r ∈ D.filter (m ∣ ·), (selbergG d r)⁻¹
          = (selbergF d m / selbergG d m) * ∑ k ∈ Km, (selbergG d k)⁻¹ := by
            rw [hfactor]; ring
        _ = (∑ t ∈ m.divisors, (selbergG d t)⁻¹) * ∑ k ∈ Km, (selbergG d k)⁻¹ := by
            rw [selbergF_div_G_eq_sum_inv_G hd_even hm_sq]
        _ = ∑ tk ∈ m.divisors ×ˢ Km, (selbergG d (tk.1 * tk.2))⁻¹ := by
            rw [sum_mul_sum, ← sum_product']
            refine sum_congr rfl fun tk htk => ?_
            simp only [mem_product, Nat.mem_divisors, mem_filter, D, Km] at htk
            have htm : tk.1 ∣ m := htk.1.1
            have ht_ne : tk.1 ≠ 0 := ne_zero_of_dvd_ne_zero hm_sq.ne_zero htm
            have hk_ne : tk.2 ≠ 0 := htk.2.1.2.ne_zero
            have hcop : tk.1.Coprime tk.2 := htk.2.2.1.coprime_dvd_left htm
            rw [selbergG_mul ht_ne hk_ne hcop, mul_inv]
        _ ≤ ∑ u ∈ D, (selbergG d u)⁻¹ := by
            have hinj : Set.InjOn (fun tk : ℕ × ℕ => tk.1 * tk.2) ↑(m.divisors ×ˢ Km) := by
              intro a ha b hb heq
              dsimp only at heq
              rw [mem_coe, mem_product, Nat.mem_divisors] at ha hb
              have ha_cop : m.Coprime a.2 := (mem_filter.mp ha.2).2.1
              have hb_cop : m.Coprime b.2 := (mem_filter.mp hb.2).2.1
              have ht1 : a.1 = Nat.gcd (a.1 * a.2) m := by
                rw [ha_cop.symm.gcd_mul_right_cancel a.1, Nat.gcd_eq_left ha.1.1]
              have ht2 : b.1 = Nat.gcd (b.1 * b.2) m := by
                rw [hb_cop.symm.gcd_mul_right_cancel b.1, Nat.gcd_eq_left hb.1.1]
              have h1eq : a.1 = b.1 := by rw [ht1, heq, ← ht2]
              have ha1_pos : 0 < a.1 :=
                Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hm_sq.ne_zero ha.1.1)
              have h2eq : a.2 = b.2 := Nat.eq_of_mul_eq_mul_left ha1_pos (h1eq ▸ heq)
              exact Prod.ext h1eq h2eq
            rw [← Finset.sum_image (f := fun u => (selbergG d u)⁻¹) hinj]
            refine sum_le_sum_of_subset_of_nonneg ?_
              fun u _ _ => (inv_pos.mpr (selbergG_pos hd_even u)).le
            intro u hu
            obtain ⟨⟨t, k⟩, htk, rfl⟩ := mem_image.mp hu
            simp only [mem_product, Nat.mem_divisors, mem_filter, mem_Icc, D, Km] at htk ⊢
            have ht_le : t ≤ m := Nat.le_of_dvd (by omega) htk.1.1
            have ht_pos : 1 ≤ t := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hm_sq.ne_zero htk.1.1)
            have ht_sq : Squarefree t := hm_sq.squarefree_of_dvd htk.1.1
            have hcop : t.Coprime k := htk.2.2.1.coprime_dvd_left htk.1.1
            refine ⟨⟨by nlinarith, le_trans (Nat.mul_le_mul_right k ht_le) htk.2.2.2⟩,
              Nat.squarefree_mul_iff.mpr ⟨hcop, ht_sq, htk.2.1.2⟩⟩
    have : selbergF d m * S⁻¹ * ∑ r ∈ D.filter (m ∣ ·), (selbergG d r)⁻¹ =
        (selbergF d m * ∑ r ∈ D.filter (m ∣ ·), (selbergG d r)⁻¹) * S⁻¹ := by ring
    rw [this, mul_inv_le_iff₀ hS_pos, one_mul]
    exact hgoal
  have hy_eq : ∀ r ∈ D,
      ∑ m ∈ D.filter (r ∣ ·), lam m / selbergF d m = sqMu r / (selbergG d r * S) := by
    intro r hr
    have hr_sq : Squarefree r := (mem_filter.mp hr).2
    have hsimp : ∀ m ∈ D.filter (r ∣ ·),
        lam m / selbergF d m = sqMu m * S⁻¹ * ∑ u ∈ D.filter (m ∣ ·), (selbergG d u)⁻¹ := by
      intro m _
      dsimp only [lam]
      have hf := (selbergF_pos d m).ne'
      field_simp
    rw [sum_congr rfl hsimp]
    calc ∑ m ∈ D.filter (r ∣ ·), sqMu m * S⁻¹ * ∑ u ∈ D.filter (m ∣ ·), (selbergG d u)⁻¹
        = S⁻¹ * ∑ m ∈ D.filter (r ∣ ·), ∑ u ∈ D.filter (m ∣ ·), sqMu m * (selbergG d u)⁻¹ := by
          rw [mul_sum]
          refine sum_congr rfl fun m _ => ?_
          rw [mul_sum, mul_sum]
          refine sum_congr rfl fun u _ => by ring
      _ = S⁻¹ * ∑ u ∈ D.filter (r ∣ ·),
            (selbergG d u)⁻¹ * ∑ m ∈ u.divisors.filter (r ∣ ·), sqMu m := by
          congr 1
          have hL : ∑ m ∈ D.filter (r ∣ ·), ∑ u ∈ D.filter (m ∣ ·), sqMu m * (selbergG d u)⁻¹ =
              ∑ m ∈ D, ∑ u ∈ D, if r ∣ m ∧ m ∣ u then sqMu m * (selbergG d u)⁻¹ else 0 := by
            rw [Finset.sum_filter (s := D)]
            refine sum_congr rfl fun m _ => ?_
            by_cases hrm : r ∣ m
            · rw [if_pos hrm, Finset.sum_filter (s := D)]
              refine sum_congr rfl fun u _ => by simp [hrm]
            · rw [if_neg hrm]
              symm
              refine sum_eq_zero fun u _ => by simp [hrm]
          rw [hL, sum_comm, Finset.sum_filter (s := D)]
          refine sum_congr rfl fun u hu => ?_
          by_cases hru : r ∣ u
          · rw [if_pos hru, mul_sum, Finset.sum_filter (s := u.divisors)]
            have hu_sq : Squarefree u := (mem_filter.mp hu).2
            have huZ : u ≤ Z := (mem_Icc.mp (mem_filter.mp hu).1).2
            have hsub : u.divisors ⊆ D := by
              intro m hm
              rw [Nat.mem_divisors] at hm
              refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_, le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hu_sq.ne_zero) hm.1) huZ⟩,
                hu_sq.squarefree_of_dvd hm.1⟩
              exact Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hu_sq.ne_zero hm.1)
            rw [← sum_subset hsub]
            · refine sum_congr rfl fun m hm => ?_
              have hmu : m ∣ u := (Nat.mem_divisors.mp hm).1
              by_cases hrm : r ∣ m
              · rw [if_pos ⟨hrm, hmu⟩, if_pos hrm]; ring
              · rw [if_neg (fun h => hrm h.1), if_neg hrm]
            · intro m _ hnot
              rw [if_neg]
              rintro ⟨_, hmu⟩
              exact hnot (Nat.mem_divisors.mpr ⟨hmu, hu_sq.ne_zero⟩)
          · rw [if_neg hru]
            refine sum_eq_zero fun m _ => ?_
            rw [if_neg]
            rintro ⟨hrm, hmu⟩
            exact hru (hrm.trans hmu)
      _ = S⁻¹ * ∑ u ∈ D.filter (r ∣ ·), (selbergG d u)⁻¹ * (if u = r then sqMu r else 0) := by
          congr 1
          refine sum_congr rfl fun u hu => ?_
          congr 1
          have hu_sq : Squarefree u := (mem_filter.mp (mem_filter.mp hu).1).2
          have hru : r ∣ u := (mem_filter.mp hu).2
          have hmul : r * (u / r) = u := Nat.mul_div_cancel' hru
          have hsq' := (Nat.squarefree_mul_iff).mp (hmul.symm ▸ hu_sq)
          have hbij : ∑ m ∈ u.divisors.filter (r ∣ ·), sqMu m =
              sqMu r * ∑ t ∈ (u / r).divisors, sqMu t := by
            rw [mul_sum]
            refine Finset.sum_bij (fun m _ => m / r) ?_ ?_ ?_ ?_
            · intro m hm
              simp only [mem_filter, Nat.mem_divisors] at hm ⊢
              exact ⟨Nat.div_dvd_div hm.2 hm.1.1, right_ne_zero_of_mul (hmul.symm ▸ hu_sq.ne_zero)⟩
            · intro m₁ hm₁ m₂ hm₂ heq
              have h1 := (mem_filter.mp hm₁).2
              have h2 := (mem_filter.mp hm₂).2
              rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, heq]
            · intro t ht
              rw [Nat.mem_divisors] at ht
              refine ⟨r * t, ?_, Nat.mul_div_cancel_left t (Nat.pos_of_ne_zero hr_sq.ne_zero)⟩
              simp only [mem_filter, Nat.mem_divisors]
              exact ⟨⟨by rw [← hmul]; exact Nat.mul_dvd_mul_left r ht.1, hu_sq.ne_zero⟩,
                dvd_mul_right r t⟩
            · intro m hm
              simp only [mem_filter, Nat.mem_divisors] at hm
              have hm_eq : r * (m / r) = m := Nat.mul_div_cancel' hm.2
              have hm_sq : Squarefree m := hu_sq.squarefree_of_dvd hm.1.1
              have hsq_m := (Nat.squarefree_mul_iff).mp (hm_eq.symm ▸ hm_sq)
              have ht_ne : m / r ≠ 0 := right_ne_zero_of_mul (hm_eq.symm ▸ hm_sq.ne_zero)
              conv_lhs => rw [← hm_eq]
              exact sqMu_mul hr_sq.ne_zero ht_ne hsq_m.1
          rw [hbij, sum_divisors_sqMu hsq'.2.2]
          by_cases hur : u = r
          · subst hur
            rw [Nat.div_self (Nat.pos_of_ne_zero hr_sq.ne_zero), if_pos rfl, if_pos rfl, mul_one]
          · have hne1 : u / r ≠ 1 := by
              intro h1
              rw [h1, mul_one] at hmul
              exact hur hmul.symm
            rw [if_neg hne1, if_neg hur, mul_zero]
      _ = sqMu r / (selbergG d r * S) := by
          rw [sum_eq_single r]
          · rw [if_pos rfl]; ring
          · intro u _ hne; rw [if_neg hne, mul_zero]
          · intro hnot; exact (hnot (mem_filter.mpr ⟨hr, dvd_rfl⟩)).elim
  have hpoint : (((range x).filter fun p => p.Prime ∧ (p + d).Prime).card : ℝ) ≤
      (Z : ℝ) + ∑ n ∈ range x, (∑ m ∈ D.filter (· ∣ n * (n + d)), lam m) ^ 2 := by
    have hsplit : ((range x).filter fun p => p.Prime ∧ (p + d).Prime).card ≤
        Z + ((range x).filter fun p => Z < p ∧ p.Prime ∧ (p + d).Prime).card := by
      rw [← card_filter_add_card_filter_not (s := (range x).filter fun p => p.Prime ∧ (p + d).Prime)
        (p := fun p => p ≤ Z)]
      refine Nat.add_le_add ?_ ?_
      · have hsub : (((range x).filter fun p => p.Prime ∧ (p + d).Prime).filter (· ≤ Z)) ⊆ Icc 1 Z := by
          intro p hp
          simp only [mem_filter, mem_range, mem_Icc] at hp ⊢
          exact ⟨hp.1.2.1.pos, hp.2⟩
        exact (card_le_card hsub).trans (by simp)
      · refine card_le_card fun p hp => ?_
        simp only [mem_filter, mem_range, not_le] at hp ⊢
        exact ⟨hp.1.1, hp.2, hp.1.2⟩
    have hgt : (((range x).filter fun p => Z < p ∧ p.Prime ∧ (p + d).Prime).card : ℝ) ≤
        ∑ n ∈ range x, (∑ m ∈ D.filter (· ∣ n * (n + d)), lam m) ^ 2 := by
      rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      rw [sum_filter]
      refine sum_le_sum fun n _ => ?_
      by_cases hn : Z < n ∧ n.Prime ∧ (n + d).Prime
      · rw [if_pos hn]
        have honly1 : D.filter (· ∣ n * (n + d)) = {1} := by
          ext m
          simp only [mem_filter, mem_Icc, mem_singleton, D]
          constructor
          · rintro ⟨⟨⟨hm1, hmZ⟩, hm_sq⟩, hmdvd⟩
            by_contra hm_ne1
            have hne : m.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
            obtain ⟨q, hq⟩ := hne
            have hq_prime := Nat.prime_of_mem_primeFactors hq
            have hqm : q ∣ m := Nat.dvd_of_mem_primeFactors hq
            have hqle : q ≤ Z := le_trans (Nat.le_of_dvd (by omega) hqm) hmZ
            rcases hq_prime.dvd_mul.mp (hqm.trans hmdvd) with hqp | hqpd
            · have := (Nat.prime_dvd_prime_iff_eq hq_prime hn.2.1).mp hqp
              omega
            · have := (Nat.prime_dvd_prime_iff_eq hq_prime hn.2.2).mp hqpd
              omega
          · rintro rfl
            exact ⟨⟨⟨le_rfl, hZ⟩, squarefree_one⟩, one_dvd _⟩
        rw [honly1, sum_singleton, hlam1, one_pow]
      · rw [if_neg hn]
        exact sq_nonneg _
    have hsplit_r : (((range x).filter fun p => p.Prime ∧ (p + d).Prime).card : ℝ) ≤
        (Z : ℝ) + (((range x).filter fun p => Z < p ∧ p.Prime ∧ (p + d).Prime).card : ℝ) := by
      exact_mod_cast hsplit
    linarith
  have hexpand : ∑ n ∈ range x, (∑ m ∈ D.filter (· ∣ n * (n + d)), lam m) ^ 2 =
      ∑ m₁ ∈ D, ∑ m₂ ∈ D, lam m₁ * lam m₂ *
        (((range x).filter fun n => Nat.lcm m₁ m₂ ∣ n * (n + d)).card : ℝ) := by
    have h1 : ∀ n ∈ range x,
        (∑ m ∈ D.filter (· ∣ n * (n + d)), lam m) ^ 2 =
        ∑ m₁ ∈ D, ∑ m₂ ∈ D,
          if Nat.lcm m₁ m₂ ∣ n * (n + d) then lam m₁ * lam m₂ else 0 := by
      intro n _
      rw [sq, sum_mul_sum]
      rw [sum_filter]
      refine sum_congr rfl fun m₁ _ => ?_
      by_cases h1 : m₁ ∣ n * (n + d)
      · rw [if_pos h1, sum_filter]
        refine sum_congr rfl fun m₂ _ => ?_
        by_cases h2 : m₂ ∣ n * (n + d)
        · rw [if_pos h2, if_pos (Nat.lcm_dvd h1 h2)]
        · rw [if_neg h2, if_neg (fun hlcm => h2 ((Nat.dvd_lcm_right m₁ m₂).trans hlcm))]
      · rw [if_neg h1]
        symm
        refine sum_eq_zero fun m₂ _ => ?_
        rw [if_neg (fun hlcm => h1 ((Nat.dvd_lcm_left m₁ m₂).trans hlcm))]
    rw [sum_congr rfl h1, sum_comm]
    refine sum_congr rfl fun m₁ _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun m₂ _ => ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  have hmain : ∑ m₁ ∈ D, ∑ m₂ ∈ D,
        lam m₁ * lam m₂ * ((omega d (Nat.lcm m₁ m₂) : ℝ) / (Nat.lcm m₁ m₂ : ℝ)) = S⁻¹ := by
    have hterm : ∀ m₁ ∈ D, ∀ m₂ ∈ D,
        lam m₁ * lam m₂ * ((omega d (Nat.lcm m₁ m₂) : ℝ) / (Nat.lcm m₁ m₂ : ℝ)) =
        ∑ r ∈ D, if r ∣ m₁ ∧ r ∣ m₂ then
          selbergG d r * (lam m₁ / selbergF d m₁) * (lam m₂ / selbergF d m₂)
        else 0 := by
      intro m₁ hm₁ m₂ hm₂
      have hsq1 : Squarefree m₁ := (mem_filter.mp hm₁).2
      have hsq2 : Squarefree m₂ := (mem_filter.mp hm₂).2
      have hlcm_sq : Squarefree (Nat.lcm m₁ m₂) := by
        rw [Nat.squarefree_iff_prime_squarefree]
        intro p hp hp2
        rw [← sq] at hp2
        have hne : Nat.lcm m₁ m₂ ≠ 0 := Nat.lcm_ne_zero hsq1.ne_zero hsq2.ne_zero
        have hle : (Nat.lcm m₁ m₂).factorization p ≤ 1 := by
          rw [Nat.factorization_lcm hsq1.ne_zero hsq2.ne_zero, Finsupp.sup_apply]
          exact sup_le (hsq1.natFactorization_le_one p) (hsq2.natFactorization_le_one p)
        have hge : 2 ≤ (Nat.lcm m₁ m₂).factorization p :=
          (hp.pow_dvd_iff_le_factorization hne).mp hp2
        omega
      have hgcd_sq : Squarefree (Nat.gcd m₁ m₂) := hsq1.squarefree_of_dvd (Nat.gcd_dvd_left m₁ m₂)
      have hratio : ((omega d (Nat.lcm m₁ m₂) : ℝ) / (Nat.lcm m₁ m₂ : ℝ)) =
          (selbergF d m₁)⁻¹ * (selbergF d m₂)⁻¹ * selbergF d (Nat.gcd m₁ m₂) := by
        have hF := selbergF_eq_div_omega (d := d) hlcm_sq
        have hlg := selbergF_lcm_mul_gcd (d := d) hsq1.ne_zero hsq2.ne_zero
        have hf1 := (selbergF_pos d m₁).ne'
        have hf2 := (selbergF_pos d m₂).ne'
        have hfl := (selbergF_pos d (Nat.lcm m₁ m₂)).ne'
        have hom_ne : (omega d (Nat.lcm m₁ m₂) : ℝ) ≠ 0 := by
          exact_mod_cast (omega_pos d (Nat.lcm m₁ m₂)).ne'
        have hlcm_ne : (Nat.lcm m₁ m₂ : ℝ) ≠ 0 := by
          exact_mod_cast Nat.lcm_ne_zero hsq1.ne_zero hsq2.ne_zero
        have hinv : (omega d (Nat.lcm m₁ m₂) : ℝ) / (Nat.lcm m₁ m₂ : ℝ) =
            (selbergF d (Nat.lcm m₁ m₂))⁻¹ := by
          rw [hF, inv_div]
        rw [hinv]
        field_simp at hlg ⊢
        linarith
      rw [hratio, selbergF_eq_sum_divisors_G hgcd_sq, mul_sum, mul_sum]
      have hsub : (Nat.gcd m₁ m₂).divisors ⊆ D := by
        intro r hr
        rw [Nat.mem_divisors] at hr
        have hr1 : r ∣ m₁ := hr.1.trans (Nat.gcd_dvd_left m₁ m₂)
        have hm1Z : m₁ ≤ Z := (mem_Icc.mp (mem_filter.mp hm₁).1).2
        refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hsq1.ne_zero hr1),
          le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hsq1.ne_zero) hr1) hm1Z⟩,
          hsq1.squarefree_of_dvd hr1⟩
      rw [← sum_subset hsub]
      · refine sum_congr rfl fun r hr => ?_
        have hrgcd : r ∣ Nat.gcd m₁ m₂ := (Nat.mem_divisors.mp hr).1
        rw [if_pos ⟨hrgcd.trans (Nat.gcd_dvd_left m₁ m₂), hrgcd.trans (Nat.gcd_dvd_right m₁ m₂)⟩]
        ring
      · intro r _ hnot
        rw [if_neg]
        rintro ⟨h1, h2⟩
        exact hnot (Nat.mem_divisors.mpr ⟨Nat.dvd_gcd h1 h2, hgcd_sq.ne_zero⟩)
    calc ∑ m₁ ∈ D, ∑ m₂ ∈ D,
          lam m₁ * lam m₂ * ((omega d (Nat.lcm m₁ m₂) : ℝ) / (Nat.lcm m₁ m₂ : ℝ))
        = ∑ m₁ ∈ D, ∑ m₂ ∈ D, ∑ r ∈ D,
            if r ∣ m₁ ∧ r ∣ m₂ then
              selbergG d r * (lam m₁ / selbergF d m₁) * (lam m₂ / selbergF d m₂)
            else 0 := by
          refine sum_congr rfl fun m₁ hm₁ => sum_congr rfl fun m₂ hm₂ => hterm m₁ hm₁ m₂ hm₂
      _ = ∑ r ∈ D, ∑ m₁ ∈ D, ∑ m₂ ∈ D,
            if r ∣ m₁ ∧ r ∣ m₂ then
              selbergG d r * (lam m₁ / selbergF d m₁) * (lam m₂ / selbergF d m₂)
            else 0 := by
          calc ∑ m₁ ∈ D, ∑ m₂ ∈ D, ∑ r ∈ D,
                (if r ∣ m₁ ∧ r ∣ m₂ then
                  selbergG d r * (lam m₁ / selbergF d m₁) * (lam m₂ / selbergF d m₂)
                else 0)
              = ∑ m₁ ∈ D, ∑ r ∈ D, ∑ m₂ ∈ D,
                  (if r ∣ m₁ ∧ r ∣ m₂ then
                    selbergG d r * (lam m₁ / selbergF d m₁) * (lam m₂ / selbergF d m₂)
                  else 0) := sum_congr rfl fun m₁ _ => sum_comm
            _ = ∑ r ∈ D, ∑ m₁ ∈ D, ∑ m₂ ∈ D,
                  (if r ∣ m₁ ∧ r ∣ m₂ then
                    selbergG d r * (lam m₁ / selbergF d m₁) * (lam m₂ / selbergF d m₂)
                  else 0) := sum_comm
      _ = ∑ r ∈ D, selbergG d r * (∑ m ∈ D.filter (r ∣ ·), lam m / selbergF d m) ^ 2 := by
          refine sum_congr rfl fun r _ => ?_
          rw [sq, sum_mul_sum, mul_sum, Finset.sum_filter (s := D)]
          refine sum_congr rfl fun m₁ _ => ?_
          by_cases h1 : r ∣ m₁
          · rw [if_pos h1, mul_sum, Finset.sum_filter (s := D)]
            refine sum_congr rfl fun m₂ _ => ?_
            by_cases h2 : r ∣ m₂
            · rw [if_pos h2, if_pos ⟨h1, h2⟩]; ring
            · rw [if_neg h2, if_neg (fun h => h2 h.2)]
          · rw [if_neg h1]
            refine sum_eq_zero fun m₂ _ => by rw [if_neg (fun h => h1 h.1)]
      _ = ∑ r ∈ D, selbergG d r * (sqMu r / (selbergG d r * S)) ^ 2 := by
          refine sum_congr rfl fun r hr => by rw [hy_eq r hr]
      _ = S⁻¹ ^ 2 * ∑ r ∈ D, (selbergG d r)⁻¹ := by
          rw [mul_sum]
          refine sum_congr rfl fun r _ => ?_
          have hg := (selbergG_pos hd_even r).ne'
          have hs := hS_pos.ne'
          rw [div_pow, sqMu_sq]
          field_simp
      _ = S⁻¹ := by
          change S⁻¹ ^ 2 * S = S⁻¹
          have hs := hS_pos.ne'
          field_simp
  have herr : ∑ m₁ ∈ D, ∑ m₂ ∈ D,
        lam m₁ * lam m₂ *
          ((((range x).filter fun n => Nat.lcm m₁ m₂ ∣ n * (n + d)).card : ℝ) -
            (x : ℝ) * ((omega d (Nat.lcm m₁ m₂) : ℝ) / (Nat.lcm m₁ m₂ : ℝ))) ≤
      (Z : ℝ) ^ 4 := by
    have hD_card : (D.card : ℝ) ≤ (Z : ℝ) := by
      have : D.card ≤ Z := (card_filter_le _ _).trans (by simp)
      exact_mod_cast this
    calc ∑ m₁ ∈ D, ∑ m₂ ∈ D,
          lam m₁ * lam m₂ *
            ((((range x).filter fun n => Nat.lcm m₁ m₂ ∣ n * (n + d)).card : ℝ) -
              (x : ℝ) * ((omega d (Nat.lcm m₁ m₂) : ℝ) / (Nat.lcm m₁ m₂ : ℝ)))
        ≤ ∑ m₁ ∈ D, ∑ m₂ ∈ D, (Z : ℝ) ^ 2 := by
          refine sum_le_sum fun m₁ hm₁ => sum_le_sum fun m₂ hm₂ => ?_
          have hsq1 : Squarefree m₁ := (mem_filter.mp hm₁).2
          have hsq2 : Squarefree m₂ := (mem_filter.mp hm₂).2
          have hlcm_sq : Squarefree (Nat.lcm m₁ m₂) := by
            rw [Nat.squarefree_iff_prime_squarefree]
            intro p hp hp2
            rw [← sq] at hp2
            have hne : Nat.lcm m₁ m₂ ≠ 0 := Nat.lcm_ne_zero hsq1.ne_zero hsq2.ne_zero
            have hle : (Nat.lcm m₁ m₂).factorization p ≤ 1 := by
              rw [Nat.factorization_lcm hsq1.ne_zero hsq2.ne_zero, Finsupp.sup_apply]
              exact sup_le (hsq1.natFactorization_le_one p) (hsq2.natFactorization_le_one p)
            have hge : 2 ≤ (Nat.lcm m₁ m₂).factorization p :=
              (hp.pow_dvd_iff_le_factorization hne).mp hp2
            omega
          have happrox := card_range_dvd_mul_add_approx (d := d) hlcm_sq x
          have hl1 := hlam_abs m₁ hm₁
          have hl2 := hlam_abs m₂ hm₂
          have hom_le : (omega d (Nat.lcm m₁ m₂) : ℝ) ≤ (Z : ℝ) ^ 2 := by
            have hm1Z : m₁ ≤ Z := (mem_Icc.mp (mem_filter.mp hm₁).1).2
            have hm2Z : m₂ ≤ Z := (mem_Icc.mp (mem_filter.mp hm₂).1).2
            have hnat : omega d (Nat.lcm m₁ m₂) ≤ Z ^ 2 := by
              calc omega d (Nat.lcm m₁ m₂)
                  ≤ Nat.lcm m₁ m₂ := omega_le_self hlcm_sq
                _ ≤ m₁ * m₂ := Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero hsq1.ne_zero)
                    (Nat.pos_of_ne_zero hsq2.ne_zero)) (Nat.lcm_dvd_mul m₁ m₂)
                _ ≤ Z * Z := Nat.mul_le_mul hm1Z hm2Z
                _ = Z ^ 2 := (sq Z).symm
            exact_mod_cast hnat
          calc lam m₁ * lam m₂ *
                ((((range x).filter fun n => Nat.lcm m₁ m₂ ∣ n * (n + d)).card : ℝ) -
                  (x : ℝ) * ((omega d (Nat.lcm m₁ m₂) : ℝ) / (Nat.lcm m₁ m₂ : ℝ)))
              ≤ |lam m₁ * lam m₂ *
                  ((((range x).filter fun n => Nat.lcm m₁ m₂ ∣ n * (n + d)).card : ℝ) -
                    (x : ℝ) * ((omega d (Nat.lcm m₁ m₂) : ℝ) / (Nat.lcm m₁ m₂ : ℝ)))| :=
                le_abs_self _
            _ = |lam m₁| * |lam m₂| *
                  |(((range x).filter fun n => Nat.lcm m₁ m₂ ∣ n * (n + d)).card : ℝ) -
                    (x : ℝ) * ((omega d (Nat.lcm m₁ m₂) : ℝ) / (Nat.lcm m₁ m₂ : ℝ))| := by
                rw [abs_mul, abs_mul]
            _ ≤ 1 * 1 * (omega d (Nat.lcm m₁ m₂) : ℝ) := by
                refine mul_le_mul (mul_le_mul hl1 hl2 (abs_nonneg _) zero_le_one) happrox
                  (abs_nonneg _) (by positivity)
            _ ≤ (Z : ℝ) ^ 2 := by linarith
      _ = (D.card : ℝ) ^ 2 * (Z : ℝ) ^ 2 := by simp [sq]; ring
      _ ≤ (Z : ℝ) ^ 2 * (Z : ℝ) ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          exact pow_le_pow_left₀ (Nat.cast_nonneg _) hD_card 2
      _ = (Z : ℝ) ^ 4 := by ring
  have hcombine : ∑ m₁ ∈ D, ∑ m₂ ∈ D, lam m₁ * lam m₂ *
        (((range x).filter fun n => Nat.lcm m₁ m₂ ∣ n * (n + d)).card : ℝ) =
      (x : ℝ) * S⁻¹ +
      ∑ m₁ ∈ D, ∑ m₂ ∈ D, lam m₁ * lam m₂ *
        ((((range x).filter fun n => Nat.lcm m₁ m₂ ∣ n * (n + d)).card : ℝ) -
          (x : ℝ) * ((omega d (Nat.lcm m₁ m₂) : ℝ) / (Nat.lcm m₁ m₂ : ℝ))) := by
    rw [← hmain, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun m₁ _ => ?_
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun m₂ _ => by ring
  rw [hexpand, hcombine, ← div_eq_mul_inv] at hpoint
  linarith

/- ### Step 4: Lower bound on the Selberg denominator `S` -/

private lemma harmonic_ge_log (M : ℕ) :
    Real.log ((M : ℝ) + 1) ≤ ∑ n ∈ Icc 1 M, ((n : ℝ))⁻¹ := by
  have htele : Real.log ((M : ℝ) + 1) =
      ∑ k ∈ range M, (Real.log ((k : ℝ) + 1 + 1) - Real.log ((k : ℝ) + 1)) := by
    have h := Finset.sum_range_sub (fun k : ℕ => Real.log ((k : ℝ) + 1)) M
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, Real.log_one, sub_zero] at h
    exact h.symm
  rw [htele]
  have hsum : ∑ n ∈ Icc 1 M, ((n : ℝ))⁻¹ = ∑ k ∈ range M, ((k : ℝ) + 1)⁻¹ := by
    refine Finset.sum_bij (fun n _ => n - 1) ?_ ?_ ?_ ?_
    · intro n hn; simp only [mem_Icc, mem_range] at hn ⊢; omega
    · intro n₁ hn₁ n₂ hn₂ heq; simp only [mem_Icc] at hn₁ hn₂; omega
    · intro k hk; refine ⟨k + 1, ?_, by omega⟩
      simp only [mem_range, mem_Icc] at hk ⊢; omega
    · intro n hn
      have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
      congr 1; exact_mod_cast (show n = n - 1 + 1 by omega)
  rw [hsum]
  refine sum_le_sum fun k _ => ?_
  have hk_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hdiv : ((k : ℝ) + 1 + 1) / ((k : ℝ) + 1) = 1 + ((k : ℝ) + 1)⁻¹ := by
    field_simp
  rw [← Real.log_div (by positivity) hk_pos.ne', hdiv]
  have hle := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + ((k : ℝ) + 1)⁻¹ by positivity)
  linarith

private lemma totient_real_eq_mul_prod_factors (d : ℕ) :
    (d.totient : ℝ) = (d : ℝ) * ∏ p ∈ d.primeFactors, (1 - ((p : ℝ))⁻¹) := by
  have hq := Nat.totient_eq_mul_prod_factors d
  have hr := congrArg (fun q : ℚ => (q : ℝ)) hq
  simpa [Rat.cast_mul, Rat.cast_prod, Rat.cast_sub, Rat.cast_inv, Rat.cast_natCast] using hr

private lemma geom_sum_inv_prime_le (p M : ℕ) (hp : p.Prime) :
    ∑ k ∈ range (M + 1), (((p : ℝ))⁻¹) ^ k ≤ (1 - ((p : ℝ))⁻¹)⁻¹ := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hr_pos : (0 : ℝ) < ((p : ℝ))⁻¹ := by positivity
  have hr_lt1 : ((p : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have h1r_pos : (0 : ℝ) < 1 - ((p : ℝ))⁻¹ := by linarith
  rw [geom_sum_eq hr_lt1.ne]
  have hflip : ((((p : ℝ))⁻¹) ^ (M + 1) - 1) / (((p : ℝ))⁻¹ - 1) =
      (1 - (((p : ℝ))⁻¹) ^ (M + 1)) * (1 - ((p : ℝ))⁻¹)⁻¹ := by
    have hneg : ((p : ℝ))⁻¹ - 1 = -(1 - ((p : ℝ))⁻¹) := by ring
    rw [hneg, div_neg, neg_div', neg_sub, div_eq_mul_inv]
  rw [hflip]
  have hle : 1 - (((p : ℝ))⁻¹) ^ (M + 1) ≤ 1 := by
    have : 0 ≤ (((p : ℝ))⁻¹) ^ (M + 1) := by positivity
    linarith
  calc (1 - (((p : ℝ))⁻¹) ^ (M + 1)) * (1 - ((p : ℝ))⁻¹)⁻¹
      ≤ 1 * (1 - ((p : ℝ))⁻¹)⁻¹ := mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr h1r_pos.le)
    _ = (1 - ((p : ℝ))⁻¹)⁻¹ := one_mul _

private lemma harmonic_le_div_totient_mul_coprime (d M : ℕ) (hd : 0 < d) :
    ∑ n ∈ Icc 1 M, ((n : ℝ))⁻¹ ≤
      ((d : ℝ) / (d.totient : ℝ)) *
        ∑ a ∈ (Icc 1 M).filter (fun a => a.Coprime d), ((a : ℝ))⁻¹ := by
  have htot_pos : (0 : ℝ) < (d.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd
  have hdt : (d : ℝ) / (d.totient : ℝ) = ∏ p ∈ d.primeFactors, (1 - ((p : ℝ))⁻¹)⁻¹ := by
    rw [totient_real_eq_mul_prod_factors d, prod_inv_distrib]
    have hd_ne : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    have hprod_ne : (∏ p ∈ d.primeFactors, (1 - ((p : ℝ))⁻¹)) ≠ 0 := by
      refine prod_ne_zero_iff.mpr fun p hp => ?_
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have : ((p : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
      linarith
    field_simp
  let G : ℝ := ∏ p ∈ d.primeFactors, ∑ k ∈ range (M + 1), (((p : ℝ))⁻¹) ^ k
  have hG_le : G ≤ (d : ℝ) / (d.totient : ℝ) := by
    rw [hdt]
    refine prod_le_prod (fun p _ => sum_nonneg fun _ _ => by positivity) fun p hp =>
      geom_sum_inv_prime_le p M (Nat.prime_of_mem_primeFactors hp)
  have hcop_nn : 0 ≤ ∑ a ∈ (Icc 1 M).filter (fun a => a.Coprime d), ((a : ℝ))⁻¹ :=
    sum_nonneg fun _ _ => by positivity
  suffices hmain : ∑ n ∈ Icc 1 M, ((n : ℝ))⁻¹ ≤
      G * ∑ a ∈ (Icc 1 M).filter (fun a => a.Coprime d), ((a : ℝ))⁻¹ by
    exact hmain.trans (mul_le_mul_of_nonneg_right hG_le hcop_nn)
  have hG_eq' : G = ∑ e ∈ d.primeFactors.pi (fun _ => range (M + 1)),
      ∏ p ∈ d.primeFactors.attach, (((p.1 : ℝ))⁻¹) ^ (e p.1 p.2) := by
    dsimp only [G]
    rw [Finset.prod_sum]
  rw [hG_eq', sum_mul_sum, ← sum_product']
  -- Map each `n ∈ Icc 1 M` injectively into `(pi ...) ×ˢ (coprime a)` with identical summand!
  let splitB : ℕ → ℕ := fun n => ∏ p ∈ d.primeFactors, p ^ (n.factorization p)
  let splitA : ℕ → ℕ := fun n => n / splitB n
  let phi : ℕ → (∀ p : ℕ, p ∈ d.primeFactors → ℕ) × ℕ :=
    fun n => (fun p _ => n.factorization p, splitA n)
  have hphi_mem : ∀ n ∈ Icc 1 M,
      phi n ∈ (d.primeFactors.pi fun _ => range (M + 1)) ×ˢ
        (Icc 1 M).filter (fun a => a.Coprime d) := by
    intro n hn
    obtain ⟨hn1, hnM⟩ := mem_Icc.mp hn
    have hn0 : n ≠ 0 := by omega
    rw [mem_product]
    constructor
    · rw [Finset.mem_pi]
      intro p hp
      rw [mem_range]
      have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
      have hdvd : p ^ (n.factorization p) ∣ n := Nat.ordProj_dvd n p
      have hle : p ^ (n.factorization p) ≤ n := Nat.le_of_dvd (by omega) hdvd
      have hlt : n.factorization p < 2 ^ (n.factorization p) := Nat.lt_two_pow_self
      have hpow : 2 ^ (n.factorization p) ≤ p ^ (n.factorization p) := Nat.pow_le_pow_left hp2 _
      dsimp only [phi]
      omega
    · rw [mem_filter, mem_Icc]
      have hBdvd : splitB n ∣ n := by
        dsimp only [splitB]
        conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
        rw [Finsupp.prod]
        have hsub : d.primeFactors ∩ n.factorization.support ⊆ n.factorization.support :=
          inter_subset_right
        have heq : ∏ p ∈ d.primeFactors, p ^ (n.factorization p) =
            ∏ p ∈ d.primeFactors ∩ n.factorization.support, p ^ (n.factorization p) := by
          symm
          refine prod_subset inter_subset_left fun p _ hnot => ?_
          have h0 : n.factorization p = 0 := by
            by_contra hne
            exact hnot (mem_inter.mpr ⟨‹_›, Finsupp.mem_support_iff.mpr hne⟩)
          rw [h0, pow_zero]
        rw [heq]
        exact Finset.prod_dvd_prod_of_subset _ _ _ hsub
      have hBpos : 0 < splitB n := by
        dsimp only [splitB]
        exact prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
      have hmul : splitB n * splitA n = n := Nat.mul_div_cancel' hBdvd
      have hApos : 1 ≤ splitA n := by
        have : splitA n ≠ 0 := right_ne_zero_of_mul (hmul.symm ▸ hn0)
        omega
      refine ⟨⟨hApos, le_trans (Nat.div_le_self n _) hnM⟩, ?_⟩
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hgcd
      have hprime_dvd := Nat.exists_prime_and_dvd hgcd
      obtain ⟨p, hp_prime, hpd⟩ := hprime_dvd
      have hpA : p ∣ splitA n := hpd.trans (Nat.gcd_dvd_left _ _)
      have hpD : p ∣ d := hpd.trans (Nat.gcd_dvd_right _ _)
      have hp_mem : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hp_prime, hpD, hd.ne'⟩
      have hB_fac : (splitB n).factorization p = n.factorization p := by
        dsimp only [splitB]
        rw [Nat.factorization_prod fun q hq => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).ne_zero]
        rw [Finsupp.finsetSum_apply, sum_eq_single p]
        · rw [hp_prime.factorization_pow, Finsupp.single_eq_same]
        · intro q hq hne
          rw [(Nat.prime_of_mem_primeFactors hq).factorization_pow, Finsupp.single_eq_of_ne hne.symm]
        · intro hnot; exact (hnot hp_mem).elim
      have hA_pos : 0 < (splitA n).factorization p :=
        hp_prime.factorization_pos_of_dvd (by omega) hpA
      have hsum_fac : n.factorization p = (splitB n).factorization p + (splitA n).factorization p := by
        conv_lhs => rw [← hmul]
        rw [Nat.factorization_mul hBpos.ne' (by omega), Finsupp.add_apply]
      omega
  have hphi_inj : Set.InjOn phi (Icc 1 M : Set ℕ) := by
    intro n₁ hn₁ n₂ hn₂ heq
    have h1 : 1 ≤ n₁ := (mem_Icc.mp hn₁).1
    have h2 : 1 ≤ n₂ := (mem_Icc.mp hn₂).1
    have hAeq : splitA n₁ = splitA n₂ := congrArg Prod.snd heq
    have hEeq : ∀ p (hp : p ∈ d.primeFactors), n₁.factorization p = n₂.factorization p := by
      intro p hp
      have := congrArg (fun f => f p hp) (congrArg Prod.fst heq)
      exact this
    have hBeq : splitB n₁ = splitB n₂ := by
      dsimp only [splitB]
      exact prod_congr rfl fun p hp => by rw [hEeq p hp]
    have hBdvd : ∀ n : ℕ, 1 ≤ n → splitB n ∣ n := by
      intro n hn
      dsimp only [splitB]
      conv_rhs => rw [← Nat.prod_factorization_pow_eq_self (by omega : n ≠ 0)]
      rw [Finsupp.prod]
      have heq' : ∏ p ∈ d.primeFactors, p ^ (n.factorization p) =
          ∏ p ∈ d.primeFactors ∩ n.factorization.support, p ^ (n.factorization p) := by
        symm
        refine prod_subset inter_subset_left fun p _ hnot => ?_
        have h0 : n.factorization p = 0 := by
          by_contra hne
          exact hnot (mem_inter.mpr ⟨‹_›, Finsupp.mem_support_iff.mpr hne⟩)
        rw [h0, pow_zero]
      rw [heq']
      exact Finset.prod_dvd_prod_of_subset _ _ _ inter_subset_right
    rw [← Nat.mul_div_cancel' (hBdvd n₁ h1), ← Nat.mul_div_cancel' (hBdvd n₂ h2)]
    change splitB n₁ * splitA n₁ = splitB n₂ * splitA n₂
    rw [hBeq, hAeq]
  have hphi_val : ∀ n ∈ Icc 1 M,
      ((n : ℝ))⁻¹ =
        (∏ p ∈ d.primeFactors.attach, (((p.1 : ℝ))⁻¹) ^ ((phi n).1 p.1 p.2)) *
          (((phi n).2 : ℝ))⁻¹ := by
    intro n hn
    have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
    have hBdvd : splitB n ∣ n := by
      dsimp only [splitB]
      conv_rhs => rw [← Nat.prod_factorization_pow_eq_self (by omega : n ≠ 0)]
      rw [Finsupp.prod]
      have heq' : ∏ p ∈ d.primeFactors, p ^ (n.factorization p) =
          ∏ p ∈ d.primeFactors ∩ n.factorization.support, p ^ (n.factorization p) := by
        symm
        refine prod_subset inter_subset_left fun p _ hnot => ?_
        have h0 : n.factorization p = 0 := by
          by_contra hne
          exact hnot (mem_inter.mpr ⟨‹_›, Finsupp.mem_support_iff.mpr hne⟩)
        rw [h0, pow_zero]
      rw [heq']
      exact Finset.prod_dvd_prod_of_subset _ _ _ inter_subset_right
    have hmul : (n : ℝ) = (splitB n : ℝ) * (splitA n : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' hBdvd).symm
    rw [hmul, mul_inv]
    congr 1
    dsimp only [splitB, phi]
    rw [Nat.cast_prod, ← prod_inv_distrib, ← prod_attach]
    refine prod_congr rfl fun p _ => by rw [Nat.cast_pow, inv_pow]
  calc ∑ n ∈ Icc 1 M, ((n : ℝ))⁻¹
      = ∑ n ∈ Icc 1 M,
          (∏ p ∈ d.primeFactors.attach, (((p.1 : ℝ))⁻¹) ^ ((phi n).1 p.1 p.2)) *
            (((phi n).2 : ℝ))⁻¹ := sum_congr rfl hphi_val
    _ = ∑ y ∈ (Icc 1 M).image phi,
          (∏ p ∈ d.primeFactors.attach, (((p.1 : ℝ))⁻¹) ^ (y.1 p.1 p.2)) * ((y.2 : ℝ))⁻¹ := by
        rw [Finset.sum_image hphi_inj]
    _ ≤ ∑ y ∈ (d.primeFactors.pi fun _ => range (M + 1)) ×ˢ
          (Icc 1 M).filter (fun a => a.Coprime d),
          (∏ p ∈ d.primeFactors.attach, (((p.1 : ℝ))⁻¹) ^ (y.1 p.1 p.2)) * ((y.2 : ℝ))⁻¹ := by
        refine sum_le_sum_of_subset_of_nonneg ?_ fun y _ _ => ?_
        · intro y hy
          obtain ⟨n, hn, rfl⟩ := mem_image.mp hy
          exact hphi_mem n hn
        · exact mul_nonneg (prod_nonneg fun _ _ => by positivity) (by positivity)

private lemma selberg_S_ge {d M Z : ℕ} (hd_even : Even d) (hd_pos : 0 < d)
    (hM : 1 ≤ M) (hMZ : M ^ 2 ≤ Z) :
    let D := (Icc 1 Z).filter Squarefree
    ((d.totient : ℝ) / (d : ℝ) * Real.log ((M : ℝ) + 1)) ^ 2 ≤
      ∑ r ∈ D, (selbergG d r)⁻¹ := by
  intro D
  let SA := (Icc 1 M).filter fun a => a.Coprime d
  have hlog_nn : 0 ≤ Real.log ((M : ℝ) + 1) := by
    apply Real.log_nonneg
    have hMr : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have htot_pos : (0 : ℝ) < (d.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd_pos
  have hd_rpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
  have hA_ge : (d.totient : ℝ) / (d : ℝ) * Real.log ((M : ℝ) + 1) ≤
      ∑ a ∈ SA, ((a : ℝ))⁻¹ := by
    have h1 := (harmonic_ge_log M).trans (harmonic_le_div_totient_mul_coprime d M hd_pos)
    have hinv : (d.totient : ℝ) / (d : ℝ) * ((d : ℝ) / (d.totient : ℝ)) = 1 := by
      field_simp
    calc (d.totient : ℝ) / (d : ℝ) * Real.log ((M : ℝ) + 1)
        ≤ (d.totient : ℝ) / (d : ℝ) * (((d : ℝ) / (d.totient : ℝ)) * ∑ a ∈ SA, ((a : ℝ))⁻¹) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ∑ a ∈ SA, ((a : ℝ))⁻¹ := by rw [← mul_assoc, hinv, one_mul]
  have hsq_le : ((d.totient : ℝ) / (d : ℝ) * Real.log ((M : ℝ) + 1)) ^ 2 ≤
      (∑ a ∈ SA, ((a : ℝ))⁻¹) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hA_ge 2
  refine hsq_le.trans ?_
  rw [sq, sum_mul_sum, ← sum_product']
  -- Group `(a, b) ∈ SA ×ˢ SA` by the squarefree radical `rad(a * b) = ∏ p ∈ (a * b).primeFactors, p`
  let rad : ℕ × ℕ → ℕ := fun ab => ∏ p ∈ (ab.1 * ab.2).primeFactors, p
  let DC : Finset ℕ := D.filter fun r => r.Coprime d
  have hrad_mem : ∀ ab ∈ SA ×ˢ SA, rad ab ∈ DC := by
    intro ab hab
    simp only [mem_product, mem_filter, mem_Icc, SA] at hab
    obtain ⟨⟨⟨ha1, haM⟩, ha_cop⟩, ⟨⟨hb1, hbM⟩, hb_cop⟩⟩ := hab
    have hab_pos : 0 < ab.1 * ab.2 := Nat.mul_pos (by omega) (by omega)
    have hprimes : ∀ p ∈ (ab.1 * ab.2).primeFactors, p.Prime :=
      fun p hp => Nat.prime_of_mem_primeFactors hp
    simp only [mem_filter, mem_Icc, D, DC]
    refine ⟨⟨⟨?_, ?_⟩, squarefree_prod_primes hprimes⟩, ?_⟩
    · exact prod_pos fun p hp => (hprimes p hp).pos
    · calc rad ab ≤ ab.1 * ab.2 := Nat.le_of_dvd hab_pos (Nat.prod_primeFactors_dvd (ab.1 * ab.2))
        _ ≤ M * M := Nat.mul_le_mul haM hbM
        _ = M ^ 2 := (sq M).symm
        _ ≤ Z := hMZ
    · refine Nat.Coprime.prod_left fun p hp => ?_
      have hp_prime := hprimes p hp
      have hpdvd : p ∣ ab.1 * ab.2 := Nat.dvd_of_mem_primeFactors hp
      have hcop_ab : (ab.1 * ab.2).Coprime d := ha_cop.mul_left hb_cop
      exact hcop_ab.coprime_dvd_left hpdvd
  rw [← Finset.sum_fiberwise_of_maps_to hrad_mem]
  calc ∑ r ∈ DC, ∑ ab ∈ (SA ×ˢ SA).filter (fun ab => rad ab = r), ((ab.1 : ℝ))⁻¹ * ((ab.2 : ℝ))⁻¹
      ≤ ∑ r ∈ DC, (selbergG d r)⁻¹ := by
        refine sum_le_sum fun r hr => ?_
        have hr_sq : Squarefree r := (mem_filter.mp (mem_filter.mp hr).1).2
        have hr_cop : r.Coprime d := (mem_filter.mp hr).2
        let E2 : Finset (ℕ × ℕ) := (range (M + 1) ×ˢ range (M + 1)).erase (0, 0)
        let psi : ℕ × ℕ → (∀ p : ℕ, p ∈ r.primeFactors → ℕ × ℕ) :=
          fun ab p _ => (ab.1.factorization p, ab.2.factorization p)
        have hpsi_mem : ∀ ab ∈ (SA ×ˢ SA).filter (fun ab => rad ab = r),
            psi ab ∈ r.primeFactors.pi fun _ => E2 := by
          intro ab hab
          simp only [mem_filter, mem_product, mem_Icc, SA] at hab
          obtain ⟨⟨⟨⟨ha1, haM⟩, _⟩, ⟨⟨hb1, hbM⟩, _⟩⟩, hrad⟩ := hab
          have hpf : (ab.1 * ab.2).primeFactors = r.primeFactors := by
            rw [← hrad]
            exact (primeFactors_prod_primes fun p hp => Nat.prime_of_mem_primeFactors hp).symm
          rw [Finset.mem_pi]
          intro p hp
          have hp_ab : p ∈ (ab.1 * ab.2).primeFactors := hpf.symm ▸ hp
          have hp_prime := Nat.prime_of_mem_primeFactors hp
          have hp2 : 2 ≤ p := hp_prime.two_le
          rw [mem_erase, mem_product, mem_range, mem_range]
          refine ⟨?_, ?_, ?_⟩
          · intro h00
            have h1 : ab.1.factorization p = 0 := congrArg Prod.fst h00
            have h2 : ab.2.factorization p = 0 := congrArg Prod.snd h00
            have hpos := hp_prime.factorization_pos_of_dvd (by positivity)
              (Nat.dvd_of_mem_primeFactors hp_ab)
            rw [Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply, h1, h2] at hpos
            omega
          · have hle : p ^ (ab.1.factorization p) ≤ ab.1 :=
              Nat.le_of_dvd (by omega) (Nat.ordProj_dvd ab.1 p)
            have hlt := Nat.lt_two_pow_self (n := ab.1.factorization p)
            have hpow := Nat.pow_le_pow_left hp2 (ab.1.factorization p)
            dsimp only [psi]
            omega
          · have hle : p ^ (ab.2.factorization p) ≤ ab.2 :=
              Nat.le_of_dvd (by omega) (Nat.ordProj_dvd ab.2 p)
            have hlt := Nat.lt_two_pow_self (n := ab.2.factorization p)
            have hpow := Nat.pow_le_pow_left hp2 (ab.2.factorization p)
            dsimp only [psi]
            omega
        have hpsi_inj : Set.InjOn psi (((SA ×ˢ SA).filter (fun ab => rad ab = r)) : Set (ℕ × ℕ)) := by
          intro ab₁ h1 ab₂ h2 heq
          simp only [mem_coe, mem_filter, mem_product, mem_Icc, SA] at h1 h2
          have hpf1 : (ab₁.1 * ab₁.2).primeFactors = r.primeFactors := by
            rw [← h1.2]
            exact (primeFactors_prod_primes fun p hp => Nat.prime_of_mem_primeFactors hp).symm
          have hpf2 : (ab₂.1 * ab₂.2).primeFactors = r.primeFactors := by
            rw [← h2.2]
            exact (primeFactors_prod_primes fun p hp => Nat.prime_of_mem_primeFactors hp).symm
          have hfac_eq : ∀ p : ℕ, ab₁.1.factorization p = ab₂.1.factorization p ∧
              ab₁.2.factorization p = ab₂.2.factorization p := by
            intro p
            by_cases hp : p ∈ r.primeFactors
            · have h := congrArg (fun f => f p hp) heq
              exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
            · have hnot1 : p ∉ (ab₁.1 * ab₁.2).primeFactors := hpf1.symm ▸ hp
              have hnot2 : p ∉ (ab₂.1 * ab₂.2).primeFactors := hpf2.symm ▸ hp
              have h0_1 : (ab₁.1 * ab₁.2).factorization p = 0 :=
                Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
              have h0_2 : (ab₂.1 * ab₂.2).factorization p = 0 :=
                Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
              rw [Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply] at h0_1 h0_2
              omega
          have h1eq : ab₁.1 = ab₂.1 := by
            apply Nat.eq_of_factorization_eq (by omega) (by omega)
            intro p; exact (hfac_eq p).1
          have h2eq : ab₁.2 = ab₂.2 := by
            apply Nat.eq_of_factorization_eq (by omega) (by omega)
            intro p; exact (hfac_eq p).2
          exact Prod.ext h1eq h2eq
        have hpsi_val : ∀ ab ∈ (SA ×ˢ SA).filter (fun ab => rad ab = r),
            ((ab.1 : ℝ))⁻¹ * ((ab.2 : ℝ))⁻¹ =
              ∏ p ∈ r.primeFactors.attach,
                (((p.1 : ℝ))⁻¹) ^ ((psi ab p.1 p.2).1 + (psi ab p.1 p.2).2) := by
          intro ab hab
          simp only [mem_filter, mem_product, mem_Icc, SA] at hab
          have hpf : (ab.1 * ab.2).primeFactors = r.primeFactors := by
            rw [← hab.2]
            exact (primeFactors_prod_primes fun p hp => Nat.prime_of_mem_primeFactors hp).symm
          have hprod_eq : ab.1 * ab.2 = ∏ p ∈ r.primeFactors, p ^ (ab.1.factorization p + ab.2.factorization p) := by
            conv_lhs => rw [← Nat.prod_factorization_pow_eq_self (Nat.mul_ne_zero (by omega) (by omega))]
            rw [Finsupp.prod, Nat.support_factorization, hpf]
            refine prod_congr rfl fun p _ => ?_
            rw [Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply]
          rw [← mul_inv, ← Nat.cast_mul, hprod_eq, Nat.cast_prod, ← prod_inv_distrib, ← prod_attach]
          refine prod_congr rfl fun p _ => by rw [Nat.cast_pow, inv_pow]
        calc ∑ ab ∈ (SA ×ˢ SA).filter (fun ab => rad ab = r), ((ab.1 : ℝ))⁻¹ * ((ab.2 : ℝ))⁻¹
            = ∑ ab ∈ (SA ×ˢ SA).filter (fun ab => rad ab = r),
                ∏ p ∈ r.primeFactors.attach,
                  (((p.1 : ℝ))⁻¹) ^ ((psi ab p.1 p.2).1 + (psi ab p.1 p.2).2) :=
              sum_congr rfl hpsi_val
          _ = ∑ f ∈ ((SA ×ˢ SA).filter (fun ab => rad ab = r)).image psi,
                ∏ p ∈ r.primeFactors.attach, (((p.1 : ℝ))⁻¹) ^ ((f p.1 p.2).1 + (f p.1 p.2).2) := by
              rw [Finset.sum_image hpsi_inj]
          _ ≤ ∑ f ∈ r.primeFactors.pi (fun _ => E2),
                ∏ p ∈ r.primeFactors.attach, (((p.1 : ℝ))⁻¹) ^ ((f p.1 p.2).1 + (f p.1 p.2).2) := by
              refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => prod_nonneg fun _ _ => by positivity
              intro f hf
              obtain ⟨ab, hab, rfl⟩ := mem_image.mp hf
              exact hpsi_mem ab hab
          _ = ∏ p ∈ r.primeFactors, ∑ e ∈ E2, (((p : ℝ))⁻¹) ^ (e.1 + e.2) := by
              rw [Finset.prod_sum]
          _ ≤ (selbergG d r)⁻¹ := by
              unfold selbergG
              rw [← prod_inv_distrib]
              refine prod_le_prod (fun _ _ => sum_nonneg fun _ _ => by positivity) fun p hp => ?_
              have hp_prime := Nat.prime_of_mem_primeFactors hp
              have hpd : ¬ p ∣ d := by
                intro hpdvd
                have hpr := Nat.dvd_of_mem_primeFactors hp
                have hgcd := Nat.dvd_gcd hpr hpdvd
                rw [hr_cop.gcd_eq_one] at hgcd
                exact hp_prime.not_dvd_one hgcd
              have hp_ne2 : p ≠ 2 := fun h2 => hpd (h2 ▸ even_iff_two_dvd.mp hd_even)
              have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
                have := hp_prime.two_le
                exact_mod_cast (show 3 ≤ p by omega)
              rw [if_neg hpd, inv_div]
              have hE2_sum : ∑ e ∈ E2, (((p : ℝ))⁻¹) ^ (e.1 + e.2) =
                  (∑ k ∈ range (M + 1), (((p : ℝ))⁻¹) ^ k) ^ 2 - 1 := by
                have h00 : (0, 0) ∈ range (M + 1) ×ˢ range (M + 1) := by
                  simp [mem_product, mem_range]
                have := Finset.add_sum_erase (range (M + 1) ×ˢ range (M + 1))
                  (fun e : ℕ × ℕ => (((p : ℝ))⁻¹) ^ (e.1 + e.2)) h00
                have hprod : ∑ e ∈ range (M + 1) ×ˢ range (M + 1), (((p : ℝ))⁻¹) ^ (e.1 + e.2) =
                    (∑ k ∈ range (M + 1), (((p : ℝ))⁻¹) ^ k) ^ 2 := by
                  simp_rw [pow_add]
                  rw [Finset.sum_product, ← sum_mul_sum, sq]
                simp only [add_zero, pow_zero] at this
                linarith
              rw [hE2_sum]
              have hgeom := geom_sum_inv_prime_le p M hp_prime
              have hsq := pow_le_pow_left₀ (sum_nonneg fun _ _ => by positivity) hgeom 2
              have halg : ((1 - ((p : ℝ))⁻¹)⁻¹) ^ 2 - 1 ≤ 2 / ((p : ℝ) - 2) := by
                have hp0 : (p : ℝ) ≠ 0 := by linarith
                have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
                have hp2 : (p : ℝ) - 2 > 0 := by linarith
                have hsimp : (1 - ((p : ℝ))⁻¹)⁻¹ = (p : ℝ) / ((p : ℝ) - 1) := by
                  field_simp
                rw [hsimp, div_pow, sub_le_iff_le_add]
                rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((p : ℝ) - 1) ^ 2)]
                have hmul : (2 / ((p : ℝ) - 2) + 1) * ((p : ℝ) - 1) ^ 2 =
                    ((p : ℝ) ^ 2 * ((p : ℝ) - 2) + (p : ℝ)) / ((p : ℝ) - 2) := by
                  field_simp; ring
                rw [hmul, le_div_iff₀ hp2]
                nlinarith
              linarith
    _ ≤ ∑ r ∈ D, (selbergG d r)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          fun r _ _ => (inv_pos.mpr (selbergG_pos hd_even r)).le

/- ### Step 5: Average of `(d / φ(d)) ^ 2` -/

private lemma sum_div_totient_sq_le (h : ℕ) :
    ∑ d ∈ Icc 1 h, ((d : ℝ) / (d.totient : ℝ)) ^ 2 ≤ Real.exp 3 * (h : ℝ) := by
  let ψ : ℕ → ℝ := fun p => (2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2
  have hterm : ∀ d ∈ Icc 1 h,
      ((d : ℝ) / (d.totient : ℝ)) ^ 2 =
        ∑ k ∈ d.divisors.filter Squarefree, ∏ p ∈ k.primeFactors, ψ p := by
    intro d hd
    have hd1 : 1 ≤ d := (mem_Icc.mp hd).1
    have hd_pos : 0 < d := by omega
    rw [sum_sqfree_divisors_prod_primeFactors hd_pos.ne' ψ]
    have hdt : (d : ℝ) / (d.totient : ℝ) = ∏ p ∈ d.primeFactors, (1 - ((p : ℝ))⁻¹)⁻¹ := by
      rw [totient_real_eq_mul_prod_factors d, prod_inv_distrib]
      have hd_ne : (d : ℝ) ≠ 0 := by exact_mod_cast hd_pos.ne'
      have hprod_ne : (∏ p ∈ d.primeFactors, (1 - ((p : ℝ))⁻¹)) ≠ 0 := by
        refine prod_ne_zero_iff.mpr fun p hp => ?_
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        have : ((p : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
        linarith
      field_simp
    rw [hdt, ← prod_pow]
    refine prod_congr rfl fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    dsimp only [ψ]
    field_simp
    ring
  rw [sum_congr rfl hterm]
  let K := (Icc 1 h).filter Squarefree
  have hswap : ∑ d ∈ Icc 1 h, ∑ k ∈ d.divisors.filter Squarefree, (∏ p ∈ k.primeFactors, ψ p) =
      ∑ k ∈ K, (∏ p ∈ k.primeFactors, ψ p) * (((Icc 1 h).filter (k ∣ ·)).card : ℝ) := by
    calc ∑ d ∈ Icc 1 h, ∑ k ∈ d.divisors.filter Squarefree, (∏ p ∈ k.primeFactors, ψ p)
        = ∑ d ∈ Icc 1 h, ∑ k ∈ K, if k ∣ d then ∏ p ∈ k.primeFactors, ψ p else 0 := by
          refine sum_congr rfl fun d hd => ?_
          have hd1 : 1 ≤ d := (mem_Icc.mp hd).1
          have hdh : d ≤ h := (mem_Icc.mp hd).2
          have hsub : d.divisors.filter Squarefree ⊆ K := by
            intro k hk
            simp only [mem_filter, Nat.mem_divisors, mem_Icc, K] at hk ⊢
            exact ⟨⟨Nat.pos_of_ne_zero hk.2.ne_zero, le_trans (Nat.le_of_dvd (by omega) hk.1.1) hdh⟩, hk.2⟩
          rw [← sum_subset hsub]
          · refine sum_congr rfl fun k hk => ?_
            rw [if_pos (Nat.mem_divisors.mp (mem_filter.mp hk).1).1]
          · intro k hk hnot
            rw [if_neg]
            intro hkd
            exact hnot (mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hkd, by omega⟩, (mem_filter.mp hk).2⟩)
      _ = ∑ k ∈ K, ∑ d ∈ Icc 1 h, if k ∣ d then ∏ p ∈ k.primeFactors, ψ p else 0 := sum_comm
      _ = ∑ k ∈ K, (∏ p ∈ k.primeFactors, ψ p) * (((Icc 1 h).filter (k ∣ ·)).card : ℝ) := by
          refine sum_congr rfl fun k _ => ?_
          rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  rw [hswap]
  have hmult_card : ∀ k ∈ K, (((Icc 1 h).filter (k ∣ ·)).card : ℝ) ≤ (h : ℝ) / (k : ℝ) := by
    intro k hk
    have hk1 : 1 ≤ k := (mem_Icc.mp (mem_filter.mp hk).1).1
    have hnat : ((Icc 1 h).filter (k ∣ ·)).card ≤ h / k := by
      have hsub : ((Icc 1 h).filter (k ∣ ·)) ⊆ (Icc 1 (h / k)).image (fun j => k * j) := by
        intro d hd
        simp only [mem_filter, mem_Icc, mem_image] at hd ⊢
        obtain ⟨⟨hd1, hdh⟩, hkd⟩ := hd
        refine ⟨d / k, ⟨?_, Nat.div_le_div_right hdh⟩, Nat.mul_div_cancel' hkd⟩
        have hmul := Nat.mul_div_cancel' hkd
        exact Nat.pos_of_ne_zero (right_ne_zero_of_mul (hmul.symm ▸ (by omega : d ≠ 0)))
      exact (card_le_card hsub).trans (card_image_le.trans (by simp))
    have hdiv : ((h / k : ℕ) : ℝ) ≤ (h : ℝ) / (k : ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast (show 0 < k by omega) : (0 : ℝ) < k)]
      exact_mod_cast Nat.div_mul_le_self h k
    exact le_trans (by exact_mod_cast hnat) hdiv
  let φ : ℕ → ℝ := fun p => (2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)
  have hφ_nn : ∀ p : ℕ, 2 ≤ p → 0 ≤ φ p := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
    have hnum : (0 : ℝ) ≤ 2 * (p : ℝ) - 1 := by linarith
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    dsimp only [φ]
    positivity
  have hstep1 : ∑ k ∈ K, (∏ p ∈ k.primeFactors, ψ p) * (((Icc 1 h).filter (k ∣ ·)).card : ℝ) ≤
      (h : ℝ) * ∑ k ∈ K, ∏ p ∈ k.primeFactors, φ p := by
    rw [mul_sum]
    refine sum_le_sum fun k hk => ?_
    have hk_sq : Squarefree k := (mem_filter.mp hk).2
    have hψ_nn : 0 ≤ ∏ p ∈ k.primeFactors, ψ p := by
      refine prod_nonneg fun p hp => ?_
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have hnum : (0 : ℝ) ≤ 2 * (p : ℝ) - 1 := by linarith
      dsimp only [ψ]; positivity
    have hmul : (∏ p ∈ k.primeFactors, ψ p) * ((h : ℝ) / (k : ℝ)) =
        (h : ℝ) * ∏ p ∈ k.primeFactors, φ p := by
      have hk_eq : (k : ℝ) = ∏ p ∈ k.primeFactors, (p : ℝ) := by
        rw [← Nat.cast_prod, prod_primeFactors_eq_of_squarefree hk_sq]
      rw [hk_eq]
      have hdiv : (∏ p ∈ k.primeFactors, ψ p) / (∏ p ∈ k.primeFactors, (p : ℝ)) =
          ∏ p ∈ k.primeFactors, φ p := by
        rw [← prod_div_distrib]
        refine prod_congr rfl fun p _ => ?_
        dsimp only [ψ, φ]
        rw [div_div, mul_comm (((p : ℝ) - 1) ^ 2) (p : ℝ)]
      calc (∏ p ∈ k.primeFactors, ψ p) * ((h : ℝ) / ∏ p ∈ k.primeFactors, (p : ℝ))
          = (h : ℝ) * ((∏ p ∈ k.primeFactors, ψ p) / ∏ p ∈ k.primeFactors, (p : ℝ)) := by ring
        _ = (h : ℝ) * ∏ p ∈ k.primeFactors, φ p := by rw [hdiv]
    calc (∏ p ∈ k.primeFactors, ψ p) * (((Icc 1 h).filter (k ∣ ·)).card : ℝ)
        ≤ (∏ p ∈ k.primeFactors, ψ p) * ((h : ℝ) / (k : ℝ)) :=
          mul_le_mul_of_nonneg_left (hmult_card k hk) hψ_nn
      _ = (h : ℝ) * ∏ p ∈ k.primeFactors, φ p := hmul
  let P := (Icc 2 h).filter Nat.Prime
  have hstep2 : ∑ k ∈ K, ∏ p ∈ k.primeFactors, φ p ≤ ∏ p ∈ P, (1 + φ p) := by
    rw [Finset.prod_one_add]
    have hinj : Set.InjOn (fun k : ℕ => k.primeFactors) (K : Set ℕ) := by
      intro k₁ hk₁ k₂ hk₂ heq
      dsimp only at heq
      rw [← prod_primeFactors_eq_of_squarefree (mem_filter.mp hk₁).2,
        ← prod_primeFactors_eq_of_squarefree (mem_filter.mp hk₂).2, heq]
    rw [← Finset.sum_image (f := fun s => ∏ p ∈ s, φ p) hinj]
    refine sum_le_sum_of_subset_of_nonneg ?_ fun s hs _ => ?_
    · intro s hs
      obtain ⟨k, hk, rfl⟩ := mem_image.mp hs
      rw [mem_powerset]
      intro p hp
      simp only [mem_filter, mem_Icc, P]
      have hkh : k ≤ h := (mem_Icc.mp (mem_filter.mp hk).1).2
      have hkpos : 0 < k := (mem_Icc.mp (mem_filter.mp hk).1).1
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      exact ⟨⟨hp_prime.two_le, le_trans (Nat.le_of_dvd hkpos (Nat.dvd_of_mem_primeFactors hp)) hkh⟩,
        hp_prime⟩
    · refine prod_nonneg fun p hp => hφ_nn p ?_
      have hsub := mem_powerset.mp hs hp
      exact (mem_Icc.mp (mem_filter.mp hsub).1).1
  have hstep3 : ∏ p ∈ P, (1 + φ p) ≤ Real.exp 3 := by
    calc ∏ p ∈ P, (1 + φ p)
        ≤ ∏ p ∈ P, Real.exp (φ p) := by
          refine prod_le_prod (fun p hp => by
            have := hφ_nn p (mem_Icc.mp (mem_filter.mp hp).1).1; linarith) fun p _ => by
              linarith [Real.add_one_le_exp (φ p)]
      _ = Real.exp (∑ p ∈ P, φ p) := (Real.exp_sum P φ).symm
      _ ≤ Real.exp 3 := by
          refine Real.exp_le_exp.mpr ?_
          calc ∑ p ∈ P, φ p
              ≤ ∑ n ∈ Icc 2 h, φ n :=
                sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
                  fun n hn _ => hφ_nn n (mem_Icc.mp hn).1
            _ ≤ ∑ n ∈ Icc 2 h, 3 * (((n : ℝ) - 1)⁻¹ - ((n : ℝ))⁻¹) := by
                refine sum_le_sum fun n hn => ?_
                have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
                have hn0 : (n : ℝ) > 0 := by linarith
                have hn1 : (n : ℝ) - 1 > 0 := by linarith
                dsimp only [φ]
                have hdiff : ((n : ℝ) - 1)⁻¹ - ((n : ℝ))⁻¹ = 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
                  field_simp; ring
                rw [hdiff, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
                nlinarith
            _ ≤ 3 := by
                rw [← mul_sum]
                have htele : ∑ n ∈ Icc 2 h, (((n : ℝ) - 1)⁻¹ - ((n : ℝ))⁻¹) ≤ 1 := by
                  by_cases hh : h < 2
                  · have hemp : Icc 2 h = ∅ := Icc_eq_empty (by omega)
                    rw [hemp, sum_empty]; norm_num
                  · push Not at hh
                    have hrew : ∑ n ∈ Icc 2 h, (((n : ℝ) - 1)⁻¹ - ((n : ℝ))⁻¹) =
                        ∑ k ∈ range (h - 1),
                          ((((k + 1 : ℕ) : ℝ))⁻¹ - (((k + 2 : ℕ) : ℝ))⁻¹) := by
                      refine Finset.sum_bij (fun n _ => n - 2) ?_ ?_ ?_ ?_
                      · intro n hn; simp only [mem_Icc, mem_range] at hn ⊢; omega
                      · intro n₁ hn₁ n₂ hn₂ heq; simp only [mem_Icc] at hn₁ hn₂; omega
                      · intro k hk; refine ⟨k + 2, ?_, by omega⟩
                        simp only [mem_range, mem_Icc] at hk ⊢; omega
                      · intro n hn
                        have hn2 : 2 ≤ n := (mem_Icc.mp hn).1
                        have h1 : (n : ℝ) - 1 = ((n - 2 + 1 : ℕ) : ℝ) := by
                          have : n = n - 2 + 1 + 1 := by omega
                          have : (n : ℝ) = ((n - 2 + 1 : ℕ) : ℝ) + 1 := by exact_mod_cast this
                          linarith
                        have h2 : (n : ℝ) = ((n - 2 + 2 : ℕ) : ℝ) := by
                          exact_mod_cast (show n = n - 2 + 2 by omega)
                        rw [h1, ← h2]
                    rw [hrew]
                    have hsub := Finset.sum_range_sub' (fun k : ℕ => (((k + 1 : ℕ) : ℝ))⁻¹) (h - 1)
                    have hmatch : ∑ k ∈ range (h - 1),
                          ((((k + 1 : ℕ) : ℝ))⁻¹ - (((k + 2 : ℕ) : ℝ))⁻¹) =
                        ∑ k ∈ range (h - 1),
                          ((((k + 1 : ℕ) : ℝ))⁻¹ - ((((k + 1) + 1 : ℕ) : ℝ))⁻¹) := rfl
                    rw [hmatch, hsub]
                    simp only [zero_add, Nat.cast_one, inv_one]
                    have : (0 : ℝ) ≤ (((h - 1 + 1 : ℕ) : ℝ))⁻¹ := by positivity
                    linarith
                linarith
  calc ∑ k ∈ K, (∏ p ∈ k.primeFactors, ψ p) * (((Icc 1 h).filter (k ∣ ·)).card : ℝ)
      ≤ (h : ℝ) * ∑ k ∈ K, ∏ p ∈ k.primeFactors, φ p := hstep1
    _ ≤ (h : ℝ) * ∏ p ∈ P, (1 + φ p) := mul_le_mul_of_nonneg_left hstep2 (Nat.cast_nonneg h)
    _ ≤ (h : ℝ) * Real.exp 3 := mul_le_mul_of_nonneg_left hstep3 (Nat.cast_nonneg h)
    _ = Real.exp 3 * (h : ℝ) := mul_comm _ _

/- ### Step 6: Asymptotic assembly -/

private lemma eventually_log_sq_mul_rpow_le (C : ℝ) (hC : 0 < C) :
    ∀ᶠ x : ℕ in atTop,
      2 * ((C + 1) * Real.log (x : ℝ)) ^ 2 * (1 + 2 * (x : ℝ) ^ ((4 : ℝ) / 5)) ≤ (x : ℝ) := by
  have ho := isLittleO_log_rpow_atTop (show (0 : ℝ) < (1 : ℝ) / 20 by norm_num)
  have h1 : ∀ᶠ t : ℝ in atTop, Real.log t ≤ t ^ ((1 : ℝ) / 20) := by
    filter_upwards [ho.bound (show (0 : ℝ) < 1 by norm_num), eventually_ge_atTop (1 : ℝ)] with t ht h1
    rw [one_mul, Real.norm_of_nonneg (Real.log_nonneg h1),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at ht
    exact ht
  have h2 : ∀ᶠ t : ℝ in atTop, 6 * (C + 1) ^ 2 ≤ t ^ ((1 : ℝ) / 10) := by
    have htend : Tendsto (fun t : ℝ => t ^ ((1 : ℝ) / 10)) atTop atTop :=
      tendsto_rpow_atTop (by norm_num)
    exact htend.eventually_ge_atTop _
  have hreal : ∀ᶠ t : ℝ in atTop,
      2 * ((C + 1) * Real.log t) ^ 2 * (1 + 2 * t ^ ((4 : ℝ) / 5)) ≤ t := by
    filter_upwards [h1, h2, eventually_ge_atTop (1 : ℝ)] with t hlog hbig ht1
    have ht0 : 0 < t := by linarith
    have hlog_nn : 0 ≤ Real.log t := Real.log_nonneg ht1
    have hlog_sq : (Real.log t) ^ 2 ≤ t ^ ((1 : ℝ) / 10) := by
      calc (Real.log t) ^ 2
          ≤ (t ^ ((1 : ℝ) / 20)) ^ 2 := pow_le_pow_left₀ hlog_nn hlog 2
        _ = t ^ ((1 : ℝ) / 20 * 2) := by rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
        _ = t ^ ((1 : ℝ) / 10) := by norm_num
    have h1_le : (1 : ℝ) ≤ t ^ ((4 : ℝ) / 5) := Real.one_le_rpow ht1 (by norm_num)
    have hrpow_mul : t ^ ((1 : ℝ) / 10) * t ^ ((1 : ℝ) / 10) * t ^ ((4 : ℝ) / 5) = t := by
      rw [← Real.rpow_add ht0, ← Real.rpow_add ht0]
      norm_num
    calc 2 * ((C + 1) * Real.log t) ^ 2 * (1 + 2 * t ^ ((4 : ℝ) / 5))
        ≤ 2 * ((C + 1) ^ 2 * t ^ ((1 : ℝ) / 10)) * (3 * t ^ ((4 : ℝ) / 5)) := by
          have hA : ((C + 1) * Real.log t) ^ 2 ≤ (C + 1) ^ 2 * t ^ ((1 : ℝ) / 10) := by
            rw [mul_pow]
            exact mul_le_mul_of_nonneg_left hlog_sq (sq_nonneg _)
          have hB : 1 + 2 * t ^ ((4 : ℝ) / 5) ≤ 3 * t ^ ((4 : ℝ) / 5) := by linarith
          exact mul_le_mul (mul_le_mul_of_nonneg_left hA (by norm_num)) hB
            (by positivity) (by positivity)
      _ = (6 * (C + 1) ^ 2) * (t ^ ((1 : ℝ) / 10) * t ^ ((4 : ℝ) / 5)) := by ring
      _ ≤ t ^ ((1 : ℝ) / 10) * (t ^ ((1 : ℝ) / 10) * t ^ ((4 : ℝ) / 5)) := by
          exact mul_le_mul_of_nonneg_right hbig (by positivity)
      _ = t := by rw [← mul_assoc, hrpow_mul]
  exact tendsto_natCast_atTop_atTop.eventually hreal

end OMA.PrimeShortIntervalSecondMoment

theorem OMA.solution :
    OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_R1_H1_R1_H1_R2.H2 := by
  open Finset Filter Real in
  intro C hC
  refine ⟨(C + 1) * (Real.log 4 + 1) + 1 + 200 * Real.exp 3 * (C + 1) ^ 2, by positivity, ?_⟩
  have hcheb : ∀ᶠ x : ℕ in atTop,
      (Nat.primeCounting x : ℝ) ≤ (Real.log 4 + 1) * (x : ℝ) / Real.log (x : ℝ) := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually
      (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1))] with x hx
    simpa [Nat.floor_natCast] using hx
  have hlog_ge : ∀ᶠ x : ℕ in atTop, (1 : ℝ) ≤ Real.log (x : ℝ) := by
    have : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact this.eventually_ge_atTop 1
  have hrpow_ge : ∀ᶠ x : ℕ in atTop, (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) := by
    filter_upwards [eventually_ge_atTop 2] with x hx
    exact Real.one_le_rpow (by exact_mod_cast (show 1 ≤ x by omega)) (by norm_num)
  have hsmall := OMA.PrimeShortIntervalSecondMoment.eventually_log_sq_mul_rpow_le C hC
  filter_upwards [hcheb, hlog_ge, hrpow_ge, hsmall, eventually_ge_atTop 2] with
    x hpi hlog1 hx10 hsm hx2
  dsimp only
  set h : ℕ := ⌈C * Real.log (x : ℝ)⌉₊
  have hlog_pos : 0 < Real.log (x : ℝ) := by linarith
  have hh_le : (h : ℝ) ≤ (C + 1) * Real.log (x : ℝ) := by
    have hlt : (h : ℝ) < C * Real.log (x : ℝ) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    nlinarith
  have h2nd_r : ∑ r ∈ range x, (((Ioc (r - h) r).filter Nat.Prime).card : ℝ) ^ 2 ≤
      (h : ℝ) * (Nat.primeCounting x : ℝ) + 2 * (h : ℝ) * (h : ℝ) +
        2 * (h : ℝ) * ∑ d ∈ (Ioo 0 h).filter Even,
          (((range x).filter fun p => p.Prime ∧ (p + d).Prime).card : ℝ) := by
    exact_mod_cast OMA.PrimeShortIntervalSecondMoment.second_moment_nat_le x h
  set M : ℕ := ⌊(x : ℝ) ^ ((1 : ℝ) / 10)⌋₊
  set Z : ℕ := M ^ 2
  have hM1 : 1 ≤ M := Nat.le_floor (by simpa using hx10)
  have hZ1 : 1 ≤ Z := by dsimp only [Z]; nlinarith
  have hM_le : (M : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) := Nat.floor_le (by positivity)
  have hM_gt : (x : ℝ) ^ ((1 : ℝ) / 10) ≤ (M : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  have hZ_le : (Z : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 5) := by
    have : (Z : ℝ) = (M : ℝ) ^ 2 := by exact_mod_cast rfl
    rw [this]
    calc (M : ℝ) ^ 2
        ≤ ((x : ℝ) ^ ((1 : ℝ) / 10)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hM_le 2
      _ = (x : ℝ) ^ ((1 : ℝ) / 10 * 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
      _ = (x : ℝ) ^ ((1 : ℝ) / 5) := by norm_num
  have hZ4_le : (Z : ℝ) ^ 4 ≤ (x : ℝ) ^ ((4 : ℝ) / 5) := by
    calc (Z : ℝ) ^ 4
        ≤ ((x : ℝ) ^ ((1 : ℝ) / 5)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hZ_le 4
      _ = (x : ℝ) ^ ((1 : ℝ) / 5 * 4) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
      _ = (x : ℝ) ^ ((4 : ℝ) / 5) := by norm_num
  have hlogM_ge : (1 : ℝ) / 10 * Real.log (x : ℝ) ≤ Real.log ((M : ℝ) + 1) := by
    have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
    calc (1 : ℝ) / 10 * Real.log (x : ℝ)
        = Real.log ((x : ℝ) ^ ((1 : ℝ) / 10)) := (Real.log_rpow hx_pos _).symm
      _ ≤ Real.log ((M : ℝ) + 1) := Real.log_le_log (by positivity) hM_gt
  have hpair_sum : ∑ d ∈ (Ioo 0 h).filter Even,
        (((range x).filter fun p => p.Prime ∧ (p + d).Prime).card : ℝ) ≤
      (h : ℝ) * (2 * (x : ℝ) ^ ((4 : ℝ) / 5)) +
        100 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 * (Real.exp 3 * (h : ℝ)) := by
    have hZ_le_Z4 : (Z : ℝ) ≤ (x : ℝ) ^ ((4 : ℝ) / 5) := by
      have : (Z : ℝ) ≤ (Z : ℝ) ^ 4 := by
        have hZr : (1 : ℝ) ≤ Z := by exact_mod_cast hZ1
        nlinarith [sq_nonneg ((Z : ℝ) - 1)]
      linarith
    have hper_d : ∀ d ∈ (Ioo 0 h).filter Even,
        (((range x).filter fun p => p.Prime ∧ (p + d).Prime).card : ℝ) ≤
          2 * (x : ℝ) ^ ((4 : ℝ) / 5) +
            100 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 * ((d : ℝ) / (d.totient : ℝ)) ^ 2 := by
      intro d hd
      have hd_pos : 0 < d := (mem_Ioo.mp (mem_filter.mp hd).1).1
      have hd_even : Even d := (mem_filter.mp hd).2
      have hsieve := OMA.PrimeShortIntervalSecondMoment.selberg_pair_bound (x := x) hd_even hZ1
      have hSge := OMA.PrimeShortIntervalSecondMoment.selberg_S_ge hd_even hd_pos hM1 le_rfl
      have htot_pos : (0 : ℝ) < (d.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd_pos
      have hd_rpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
      have hL_pos : (0 : ℝ) < ((d.totient : ℝ) / (d : ℝ) * Real.log ((M : ℝ) + 1)) ^ 2 := by
        have : 0 < Real.log ((M : ℝ) + 1) := by linarith
        positivity
      have hx_div_S : (x : ℝ) / (∑ r ∈ (Icc 1 Z).filter Squarefree,
            (OMA.PrimeShortIntervalSecondMoment.selbergG d r)⁻¹) ≤
          100 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 * ((d : ℝ) / (d.totient : ℝ)) ^ 2 := by
        have h1 : (x : ℝ) / (∑ r ∈ (Icc 1 Z).filter Squarefree,
              (OMA.PrimeShortIntervalSecondMoment.selbergG d r)⁻¹) ≤
            (x : ℝ) / ((d.totient : ℝ) / (d : ℝ) * Real.log ((M : ℝ) + 1)) ^ 2 :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg x) hL_pos hSge
        have h2 : ((1 : ℝ) / 10 * Real.log (x : ℝ)) ^ 2 ≤ (Real.log ((M : ℝ) + 1)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hlogM_ge 2
        have h3 : (x : ℝ) / ((d.totient : ℝ) / (d : ℝ) * Real.log ((M : ℝ) + 1)) ^ 2 =
            (x : ℝ) / (Real.log ((M : ℝ) + 1)) ^ 2 * ((d : ℝ) / (d.totient : ℝ)) ^ 2 := by
          field_simp
        have h4 : (x : ℝ) / (Real.log ((M : ℝ) + 1)) ^ 2 ≤
            100 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 := by
          have hden : (0 : ℝ) < ((1 : ℝ) / 10 * Real.log (x : ℝ)) ^ 2 := by positivity
          calc (x : ℝ) / (Real.log ((M : ℝ) + 1)) ^ 2
              ≤ (x : ℝ) / ((1 : ℝ) / 10 * Real.log (x : ℝ)) ^ 2 :=
                div_le_div_of_nonneg_left (Nat.cast_nonneg x) hden h2
            _ = 100 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 := by ring
        calc (x : ℝ) / (∑ r ∈ (Icc 1 Z).filter Squarefree,
              (OMA.PrimeShortIntervalSecondMoment.selbergG d r)⁻¹)
            ≤ (x : ℝ) / (Real.log ((M : ℝ) + 1)) ^ 2 * ((d : ℝ) / (d.totient : ℝ)) ^ 2 :=
              h3 ▸ h1
          _ ≤ 100 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 * ((d : ℝ) / (d.totient : ℝ)) ^ 2 :=
              mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
      linarith
    calc ∑ d ∈ (Ioo 0 h).filter Even,
          (((range x).filter fun p => p.Prime ∧ (p + d).Prime).card : ℝ)
        ≤ ∑ d ∈ (Ioo 0 h).filter Even,
            (2 * (x : ℝ) ^ ((4 : ℝ) / 5) +
              100 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 * ((d : ℝ) / (d.totient : ℝ)) ^ 2) :=
          sum_le_sum hper_d
      _ = (((Ioo 0 h).filter Even).card : ℝ) * (2 * (x : ℝ) ^ ((4 : ℝ) / 5)) +
            100 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 *
              ∑ d ∈ (Ioo 0 h).filter Even, ((d : ℝ) / (d.totient : ℝ)) ^ 2 := by
          rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
      _ ≤ (h : ℝ) * (2 * (x : ℝ) ^ ((4 : ℝ) / 5)) +
            100 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 * (Real.exp 3 * (h : ℝ)) := by
          refine add_le_add ?_ ?_
          · refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have hcard : ((Ioo 0 h).filter Even).card ≤ h :=
              (card_filter_le _ _).trans (by simp [Nat.card_Ioo])
            exact_mod_cast hcard
          · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hsub : (Ioo 0 h).filter Even ⊆ Icc 1 h := by
              intro d hd
              simp only [mem_filter, mem_Ioo, mem_Icc] at hd ⊢
              omega
            exact (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _).trans
              (OMA.PrimeShortIntervalSecondMoment.sum_div_totient_sq_le h)
  have hterm1 : (h : ℝ) * (Nat.primeCounting x : ℝ) ≤ (C + 1) * (Real.log 4 + 1) * (x : ℝ) := by
    calc (h : ℝ) * (Nat.primeCounting x : ℝ)
        ≤ ((C + 1) * Real.log (x : ℝ)) * ((Real.log 4 + 1) * (x : ℝ) / Real.log (x : ℝ)) :=
          mul_le_mul hh_le hpi (Nat.cast_nonneg _) (by positivity)
      _ = (C + 1) * (Real.log 4 + 1) * (x : ℝ) := by
          field_simp
  have hterm2 : 2 * (h : ℝ) * (h : ℝ) +
        2 * (h : ℝ) * ((h : ℝ) * (2 * (x : ℝ) ^ ((4 : ℝ) / 5))) ≤ (x : ℝ) := by
    have hh_sq : (h : ℝ) ^ 2 ≤ ((C + 1) * Real.log (x : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg h) hh_le 2
    calc 2 * (h : ℝ) * (h : ℝ) + 2 * (h : ℝ) * ((h : ℝ) * (2 * (x : ℝ) ^ ((4 : ℝ) / 5)))
        = 2 * (h : ℝ) ^ 2 * (1 + 2 * (x : ℝ) ^ ((4 : ℝ) / 5)) := by ring
      _ ≤ 2 * ((C + 1) * Real.log (x : ℝ)) ^ 2 * (1 + 2 * (x : ℝ) ^ ((4 : ℝ) / 5)) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh_sq (by norm_num))
            (by positivity)
      _ ≤ (x : ℝ) := hsm
  have hterm3 : 2 * (h : ℝ) * (100 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 * (Real.exp 3 * (h : ℝ))) ≤
      200 * Real.exp 3 * (C + 1) ^ 2 * (x : ℝ) := by
    have hh_sq : (h : ℝ) ^ 2 ≤ ((C + 1) * Real.log (x : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg h) hh_le 2
    calc 2 * (h : ℝ) * (100 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 * (Real.exp 3 * (h : ℝ)))
        = 200 * Real.exp 3 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 * (h : ℝ) ^ 2 := by ring
      _ ≤ 200 * Real.exp 3 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 *
            ((C + 1) * Real.log (x : ℝ)) ^ 2 := by
          exact mul_le_mul_of_nonneg_left hh_sq (by positivity)
      _ = 200 * Real.exp 3 * (C + 1) ^ 2 * (x : ℝ) := by
          field_simp
  have hpair_mul := mul_le_mul_of_nonneg_left hpair_sum (show (0 : ℝ) ≤ 2 * (h : ℝ) by positivity)
  linarith
