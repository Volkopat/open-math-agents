import FormalConjectures.OEIS.«63880»

-- Reduction OeisA63880.unique_primitive_108.R1 of Conjectures associated with A063880 — unique primitive 108
-- Credit: @PanPapag
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

open OeisA63880
open scoped ArithmeticFunction.sigma

namespace OMA.R_OeisA63880_unique_primitive_108_R1

-- The unitary-divisor decomposition below is adapted from desenyon, PR 1353.
-- The prime-power bound and odd two-prime exclusion come from our earlier A063880 work.
-- For the even two-prime case, clearing the two geometric series forces the odd prime to divide 3.
private theorem splitUnitary {m q : ℕ} (hm : 0 < m) (hq : IsPrimePow q)
    (hc : q.Coprime m) :
    unitaryDivisors (m*q) = unitaryDivisors m ∪ (unitaryDivisors m).image (· * q) := by
  have hq0 := hq.pos
  ext d
  simp only [unitaryDivisors, Finset.mem_filter, Nat.mem_divisors, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro ⟨⟨hd, -⟩, hcd⟩
    obtain ⟨t, ht⟩ := hd
    have hd0 : 0 < d := Nat.pos_of_mul_pos_right (ht ▸ Nat.mul_pos hm hq0)
    rw [ht, Nat.mul_div_cancel_left _ hd0] at hcd
    have hqt : q ∣ d*t := ht ▸ dvd_mul_left q m
    rcases (hcd.isPrimePow_dvd_mul hq).1 hqt with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · have he : m = b*t := Nat.eq_of_mul_eq_mul_right hq0 (by linear_combination ht)
      subst m
      have hb : 0 < b := Nat.pos_of_mul_pos_left hd0
      exact Or.inr ⟨b, ⟨⟨dvd_mul_right _ _, hm.ne'⟩, by
        simpa [Nat.mul_div_cancel_left _ hb] using (Nat.coprime_mul_iff_left.1 hcd).2⟩, mul_comm ..⟩
    · have he : m = d*b := Nat.eq_of_mul_eq_mul_right hq0 (by linear_combination ht)
      subst m
      exact Or.inl ⟨⟨dvd_mul_right _ _, hm.ne'⟩, by
        simpa [Nat.mul_div_cancel_left _ hd0] using (Nat.coprime_mul_iff_right.1 hcd).2⟩
  · rintro (⟨⟨⟨t, rfl⟩, -⟩, hcd⟩ | ⟨b, ⟨⟨⟨t, rfl⟩, -⟩, hcd⟩, rfl⟩)
    · have hd := Nat.pos_of_mul_pos_right hm
      rw [Nat.mul_div_cancel_left _ hd] at hcd
      refine ⟨⟨dvd_mul_of_dvd_left (dvd_mul_right d t) q, (Nat.mul_pos hm hq0).ne'⟩, ?_⟩
      rw [mul_assoc, Nat.mul_div_cancel_left _ hd]
      exact hcd.mul_right (Nat.coprime_mul_iff_right.1 hc).1.symm
    · have hb := Nat.pos_of_mul_pos_right hm
      rw [Nat.mul_div_cancel_left _ hb] at hcd
      refine ⟨⟨mul_dvd_mul (dvd_mul_right b t) dvd_rfl, (Nat.mul_pos hm hq0).ne'⟩, ?_⟩
      rw [mul_right_comm b t q, Nat.mul_div_cancel_left _ (Nat.mul_pos hb hq0)]
      exact hcd.mul_left (Nat.coprime_mul_iff_right.1 hc).2

private theorem unitarySum {m q : ℕ} (hm : 0 < m) (hq : IsPrimePow q)
    (hc : q.Coprime m) : usigma (m*q) = usigma m * (q+1) := by
  have dis : Disjoint (unitaryDivisors m) ((unitaryDivisors m).image (· * q)) := by
    rw [Finset.disjoint_left]
    intro d hd hd'
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hd'
    have dvd : b*q ∣ m := (Nat.mem_divisors.1 (Finset.mem_filter.1 hd).1).1
    exact hq.ne_one (hc.eq_one_of_dvd ((dvd_mul_left q b).trans dvd))
  unfold usigma
  rw [splitUnitary hm hq hc, Finset.sum_union dis,
    Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_right hq.pos h),
    ← Finset.sum_mul, mul_add, mul_one, add_comm]

theorem even_pair_arithmetic {x q b : ℕ} (hq : q.Prime) (hb : 2 ≤ b)
    (eqn : 2*x*q^b + 2*q^b + 3 = 2*x*q + 3*q*q^b + 2*q) :
    x * q^b = 108 := by
  have hd : q ∣ q^b := dvd_pow_self _ (by omega)
  have hleft : q ∣ 2*x*q^b + 2*q^b := dvd_add (dvd_mul_of_dvd_right hd _) (dvd_mul_of_dvd_right hd _)
  have hsum : q ∣ 2*x*q^b + 2*q^b + 3 := by rw [eqn]; exact dvd_add (dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_right hd _)) (dvd_mul_left _ _)
  have h3 : q ∣ 3 := by
    obtain ⟨s, hs⟩ := hleft
    rw [hs] at hsum
    simpa using hsum
  have := (Nat.dvd_prime Nat.prime_three).1 h3
  have : q = 3 := by have := hq.two_le; omega
  subst q
  rcases eq_or_lt_of_le hb with he|hlt
  · subst b; norm_num at eqn; omega
  have hy : 27 ≤ 3^b := Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 3 ≤ b)
  have hx : x = 4 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with h|h
    · nlinarith only [eqn, Nat.mul_le_mul (by omega : x ≤ 3) (by omega : 3^b - 3 ≤ 3^b - 3), Nat.sub_add_cancel (by omega : 3 ≤ 3^b), hy, congrArg (x * ·) (Nat.sub_add_cancel (by omega : 3 ≤ 3^b))]
    · nlinarith only [eqn, Nat.mul_le_mul (by omega : 5 ≤ x) (by omega : 3^b - 3 ≤ 3^b - 3), Nat.sub_add_cancel (by omega : 3 ≤ 3^b), hy, congrArg (x * ·) (Nat.sub_add_cancel (by omega : 3 ≤ 3^b))]
  subst x
  omega

theorem sigma_geom {p a : ℕ} (hp : p.Prime) :
    σ 1 (p^a) * p + 1 = σ 1 (p^a) + p * p^a := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp, hk]
  have h := geom_sum_mul_add k (a+1)
  rw [pow_succ] at h
  nlinarith only [h]

theorem even_two {a q b : ℕ} (hq : q.Prime) (hq2 : 2 ≠ q)
    (ha : 0 < a) (hb : 2 ≤ b) (h : A (2^a*q^b)) : 2^a*q^b = 108 := by
  have pq := ((Nat.coprime_primes Nat.prime_two hq).2 hq2).pow a b
  have t := unitarySum (m := 1) (q := 2^a) (by decide)
    ((isPrimePow_nat_iff _).2 ⟨2,a,Nat.prime_two,ha,rfl⟩) (Nat.coprime_one_right _)
  have one : usigma 1 = 1 := by decide
  simp only [one_mul, one] at t
  have E := h.2
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime pq,
    unitarySum (by positivity : 0 < 2^a) ((isPrimePow_nat_iff _).2 ⟨q,b,hq,by omega,rfl⟩) pq.symm,
    t] at E
  apply even_pair_arithmetic hq hb
  have S := sigma_geom (a := a) Nat.prime_two
  have T := sigma_geom (a := b) hq
  generalize 2^a = x at *
  generalize q^b = y at *
  generalize σ 1 x = s at *
  generalize σ 1 y = v at *
  zify at S T E ⊢
  linear_combination (q-1)*E - (q*y-1)*S - s*T
theorem local_bound {p k a : ℕ} (hp : p.Prime) (hk : k+1 ≤ p) :
    k * σ 1 (p^a) < (k+1)*(p^a+1) := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  induction a with
  | zero => simp; omega
  | succ a ih =>
    rw [Finset.sum_range_succ, Nat.pow_succ p a, Nat.mul_add]
    have h := Nat.mul_le_mul_right (p^a) hk
    nlinarith

theorem two_prime_exclusion {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp3 : 3 ≤ p) (hq5 : 5 ≤ q) (hne : p ≠ q) (ha : 0 < a) (hb : 0 < b) :
    ¬ A (p^a*q^b) := by
  intro h
  have hc := ((Nat.coprime_primes hp hq).2 hne).pow a b
  have U {r e : ℕ} (hr : r.Prime) (he : 0 < e) : usigma (r^e) = r^e+1 := by
    have t := unitarySum (m := 1) (q := r^e) (by decide)
      ((isPrimePow_nat_iff _).2 ⟨r,e,hr,he,rfl⟩) (Nat.coprime_one_right _)
    have one : usigma 1 = 1 := by decide
    simpa [one] using t
  have eqn := h.2
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc,
    unitarySum (pow_pos hp.pos a) ((isPrimePow_nat_iff _).2 ⟨q,b,hq,hb,rfl⟩) hc.symm,
    U hp ha] at eqn
  have lim := Nat.mul_lt_mul_of_lt_of_lt (local_bound (a := a) hp hp3)
    (local_bound (a := b) hq hq5)
  nlinarith only [lim, eqn, Nat.zero_le ((p^a+1)*(q^b+1))]

private theorem ordered_pair {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hlt : p < q)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (h : A (p^a*q^b)) : p^a*q^b = 108 := by
  by_cases he : p = 2
  · subst p; exact even_two hq (by omega) (by omega) hb h
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq5 : 5 ≤ q := by
    by_contra! hsmall
    have : q = 4 := by omega
    subst q
    exact (by decide : ¬ Nat.Prime 4) hq
  exact False.elim (two_prime_exclusion hp hq hp3 hq5 hlt.ne (by omega) (by omega) h)

def H1 : Prop := ∀ n : ℕ, n.primeFactors.card = 3 → ¬ IsPrimitiveTerm n

def H2 : Prop := ∀ n : ℕ, 4 ≤ n.primeFactors.card → ¬ IsPrimitiveTerm n

theorem main : H1 → H2 → type_of% @OeisA63880.unique_primitive_108 := by
  intro h1 h2 n hn
  have hA := hn.mem
  have hn0 := hA.1.ne'
  have fac := Nat.prod_primeFactors_pow_factorization hn0
  have expon {p : ℕ} (hp : p ∈ n.primeFactors) : 2 ≤ n.factorization p :=
    ((Nat.prime_of_mem_primeFactors hp).pow_dvd_iff_le_factorization hn0).1
      (powerful_of_isPrimitiveTerm hn p hp)
  have hsmall : n.primeFactors.card ≤ 2 := by
    by_contra! h
    by_cases he : n.primeFactors.card = 3
    · exact h1 n he hn
    · exact h2 n (by omega) hn
  interval_cases hcard : n.primeFactors.card
  · rw [Finset.card_eq_zero.1 hcard] at fac
    simp only [Finset.prod_empty] at fac
    have bad : A 1 := fac ▸ hA
    have eqn := bad.2
    have one : usigma 1 = 1 := by decide
    simp [one] at eqn
  · obtain ⟨p,hs⟩ := Finset.card_eq_one.1 hcard
    have hm : p ∈ n.primeFactors := by simp [hs]
    have hp := Nat.prime_of_mem_primeFactors hm
    have he := expon hm
    rw [hs, Finset.prod_singleton] at fac
    rw [fac] at hA
    have U := unitarySum (m := 1) (q := p^(n.factorization p)) (by decide)
      ((isPrimePow_nat_iff _).2 ⟨p,_,hp,by omega,rfl⟩) (Nat.coprime_one_right _)
    have one : usigma 1 = 1 := by decide
    simp only [one_mul, one] at U
    have eqn := hA.2
    rw [U] at eqn
    have lim := local_bound (a := n.factorization p) (k := 1) hp hp.two_le
    omega
  · obtain ⟨p,q,hne,hs⟩ := Finset.card_eq_two.1 hcard
    have pm : p ∈ n.primeFactors := by simp [hs]
    have qm : q ∈ n.primeFactors := by simp [hs]
    rw [hs, Finset.prod_pair hne] at fac
    rw [fac] at hA ⊢
    rcases lt_or_gt_of_ne hne with hlt|hlt
    · exact ordered_pair (Nat.prime_of_mem_primeFactors pm) (Nat.prime_of_mem_primeFactors qm)
        hlt (expon pm) (expon qm) hA
    · rw [mul_comm] at hA ⊢
      exact ordered_pair (Nat.prime_of_mem_primeFactors qm) (Nat.prime_of_mem_primeFactors pm)
        hlt (expon qm) (expon pm) hA

end OMA.R_OeisA63880_unique_primitive_108_R1
