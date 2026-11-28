import FormalConjectures.OEIS.«245211»

/-!
Jaroslav Krizek's A245211 fixed-point conjecture. For distinct primes p,q
and any positive e, the only fixed point of the form p^e*q is 21 and
there are no fixed points of the form p^e*q^2. On arbitrary two-prime
support the ratio of the positive exponents lies between 1/3 and 3.
If the smaller of the two primes is at most 439, 21 is the only fixed point.
Every fixed point with prime divisor p also satisfies n ≤ p^(τ(n)-1).

The full divisor moment factors on coprime arguments, as in desenyon's
Left to Solve reduction #733. Sugui used the cofactor divisor-count budget
in formal-conjectures #8119. The two-prime gap builds on the fixed-exponent
calculation in umaia1234/agentic-conjectures, A245211, section 7.
@DomTheDeveloper's two exact searches through least prime 433 are indexed
in ProofPlaygrond #121. The finite classification there is a separate result.
-/

namespace OMA.R_OeisA245211_conjecture_R3

open Finset
open OeisA245211

private theorem moment_eq {x : ℕ} (hx : x ≠ 0) :
    (∑ d ∈ x.divisors, d * d.divisors.card) = a x + x * x.divisors.card := by
  conv_lhs => rw [← Nat.insert_self_properDivisors hx, sum_insert Nat.self_notMem_properDivisors]
  simp [a, add_comm]

private theorem moment_mul {x y : ℕ} (h : x.Coprime y) :
    (∑ d ∈ (x*y).divisors, d * d.divisors.card) = (∑ d ∈ x.divisors, d * d.divisors.card) * (∑ d ∈ y.divisors, d * d.divisors.card) := by
  rw [h.divisors_mul, sum_map]
  change (∑ z ∈ (x.divisors ×ˢ y.divisors).attach,
    z.val.1 * z.val.2 * (z.val.1 * z.val.2).divisors.card) = _
  rw [sum_attach (f := fun z : ℕ × ℕ => z.1*z.2*(z.1*z.2).divisors.card),
    sum_product, sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [((h.coprime_dvd_left (Nat.dvd_of_mem_divisors hi)).coprime_dvd_right
    (Nat.dvd_of_mem_divisors hj)).card_divisors_mul]
  ring

private theorem a_pos {x : ℕ} (hx : 1 < x) : 0 < a x := by
  have h := Finset.single_le_sum (f := fun d : ℕ => d*d.divisors.card)
    (fun _ _ => Nat.zero_le _) (Nat.one_mem_properDivisors_iff_one_lt.mpr hx)
  change 1 ≤ _
  simpa [a] using h

private theorem card_pos {x : ℕ} (hx : 0 < x) : 0 < x.divisors.card :=
  Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hx.ne'⟩

private theorem card_two {x : ℕ} (hx : 1 < x) : 2 ≤ x.divisors.card := by
  have h := card_pos (by omega : 0 < x)
  have h' : x.divisors.card ≠ 1 := fun e => (by omega : x ≠ 1) ((Nat.divisors_card_eq_one_iff x).mp e)
  omega

private theorem card_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (p^e).divisors.card = e+1 := by simp [Nat.divisors_prime_pow hp]

private theorem cofactor_budget {p m : ℕ} (hp : 1 < p) (hm : 1 < m)
    (hfix : a (p*m) = p*m) : m.divisors.card < p := by
  let f := fun d : ℕ => d * d.divisors.card
  have hlt : m < p*m := by nlinarith
  have hm' : m ∈ (p*m).properDivisors :=
    Nat.mem_properDivisors.mpr ⟨dvd_mul_left _ _, hlt⟩
  have h1 : 1 ∈ (p*m).properDivisors := Nat.one_mem_properDivisors_iff_one_lt.mpr (by omega)
  have h1' : 1 ∈ (p*m).properDivisors.erase m :=
    mem_erase.mpr ⟨by omega, h1⟩
  have hs := single_le_sum (f := f) (fun _ _ => Nat.zero_le _) h1'
  have ht := sum_erase_add (p*m).properDivisors f hm'
  change (∑ d ∈ (p*m).properDivisors, f d) = p*m at hfix
  rw [hfix] at ht
  have hf : f 1 = 1 := by simp [f]
  rw [hf] at hs
  change _ + m * m.divisors.card = p*m at ht
  have hstrict : m * m.divisors.card < p*m := by omega
  rw [Nat.mul_comm p m] at hstrict
  exact (Nat.mul_lt_mul_left (by omega : 0 < m)).mp hstrict

/-- Every prime divisor gives an upper bound for the total divisor count. -/
theorem divisor_count_bound {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hd : p ∣ n) (hfix : a n = n) : n.divisors.card ≤ 2*(p-1) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (hp.factorization_pos_of_dvd hn.ne' hd).ne'
  let b := ordCompl[p] n
  have hbp : 0 < b := Nat.ordCompl_pos p hn.ne'
  have hc : p.Coprime b := Nat.coprime_ordCompl hp hn.ne'
  have he : p^(k+1) * b = n := by
    exact (congrArg (fun j => p^j*b) hk.symm).trans (Nat.ordProj_mul_ordCompl_eq_self n p)
  have he' : p * (p^k*b) = n := by rw [← he, pow_succ']; ac_rfl
  have hpos : 0 < p^k*b := Nat.mul_pos (pow_pos hp.pos _) hbp
  have hgt : 1 < p^k*b := by
    by_contra! h
    have hm : p^k*b = 1 := by omega
    rw [hm, mul_one] at he'
    have hprime : a p = 1 := by simp [a, hp.properDivisors]
    have := hp.one_lt
    rw [← he', hprime] at hfix
    omega
  have hb := cofactor_budget hp.one_lt hgt (by simpa only [he'] using hfix)
  rw [(hc.pow_left k).card_divisors_mul, card_pow hp] at hb
  rw [← he, (hc.pow_left (k+1)).card_divisors_mul, card_pow hp]
  have hp1 := hp.one_lt
  have hh : (k+1+1)*b.divisors.card ≤ 2*((k+1)*b.divisors.card) := by
    nlinarith only [Nat.zero_le (k*b.divisors.card)]
  omega

private theorem cut_balance {x y : ℕ} (hx : 0 < x) (hy : 0 < y)
    (hc : x.Coprime y) (hf : a (x*y) = x*y) :
    (∑ d ∈ x.divisors, d * d.divisors.card) * a y + y * y.divisors.card * a x = x*y := by
  have h := moment_mul hc
  rw [moment_eq (Nat.mul_pos hx hy).ne', hf, hc.card_divisors_mul, moment_eq hy.ne'] at h
  rw [moment_eq hx.ne'] at h ⊢
  nlinarith only [h]

private theorem cut_small {x y : ℕ} (hx : 1 < x) (hy : 1 < y)
    (hc : x.Coprime y) (hf : a (x*y) = x*y) : x.divisors.card * a y < y := by
  have he := cut_balance (by omega : 0 < x) (by omega : 0 < y) hc hf
  rw [moment_eq (by omega : x ≠ 0)] at he
  have hapos := Nat.mul_pos (a_pos hx) (a_pos hy)
  have hlt : x * (x.divisors.card * a y) < x*y := by
    nlinarith only [he, hapos, Nat.zero_le (y*y.divisors.card*a x)]
  exact (Nat.mul_lt_mul_left (by omega : 0 < x)).mp hlt

/-- Every nontrivial coprime cut forces a common divisor larger than the
divisor count on the first side of the cut. -/
theorem cut_gcd {x y : ℕ} (hx : 1 < x) (hy : 1 < y)
    (hc : x.Coprime y) (hf : a (x*y) = x*y) :
    x.divisors.card < Nat.gcd y ((∑ d ∈ x.divisors, d * d.divisors.card)) := by
  have h := cut_balance (by omega : 0 < x) (by omega : 0 < y) hc hf
  have hd : y ∣ (∑ d ∈ x.divisors, d * d.divisors.card) * a y := by
    apply (Nat.dvd_add_iff_left (show y ∣ y*y.divisors.card*a x from by
      rw [Nat.mul_assoc]; exact dvd_mul_right _ _)).mpr
    rw [h]
    exact dvd_mul_left _ _
  have hgd : y ∣ Nat.gcd y ((∑ d ∈ x.divisors, d * d.divisors.card)) * a y := dvd_gcd_mul_of_dvd_mul hd
  have huv := cut_small hx hy hc hf
  have hle := Nat.le_of_dvd (Nat.mul_pos (Nat.gcd_pos_of_pos_left _ (by omega : 0 < y)) (a_pos hy)) hgd
  by_contra! hg
  have ha := Nat.mul_le_mul_right (a y) hg
  omega

private theorem prime_moment {p : ℕ} (hp : p.Prime) : (∑ d ∈ p.divisors, d * d.divisors.card) = 2*p+1 := by
  simp [hp.divisors, Ne.symm hp.ne_one, mul_comm, add_comm]

/-- If the least prime occurs exactly once, its first Cunningham successor
must itself be a prime divisor of the complementary factor. -/
theorem first_successor {p m : ℕ} (hp : p.Prime) (hm : 1 < m) (hc : p.Coprime m)
    (hmin : ∀ q : ℕ, q.Prime → q ∣ m → p ≤ q) (hf : a (p*m) = p*m) :
    (2*p+1).Prime ∧ (2*p+1) ∣ m := by
  have hg := cut_gcd hp.one_lt hm hc hf
  have hcard := card_pos hp.pos
  obtain ⟨q,hq,hqd⟩ := Nat.exists_prime_and_dvd (show Nat.gcd m ((∑ d ∈ p.divisors, d * d.divisors.card)) ≠ 1 by omega)
  have hqm := hqd.trans (Nat.gcd_dvd_left _ _)
  have hqt := hqd.trans (Nat.gcd_dvd_right _ _)
  rw [prime_moment hp] at hqt
  have hl := hmin q hq hqm
  have hn : p ≠ q := fun e => (hp.coprime_iff_not_dvd.mp hc) (e ▸ hqm)
  obtain ⟨k,hk⟩ := hqt
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hk1 : k = 1 := by
    by_contra h
    have hh := Nat.mul_le_mul_left q (show 2 ≤ k by omega)
    omega
  rw [hk1, mul_one] at hk
  exact hk.symm ▸ ⟨hq,hqm⟩

/-- If twice the least prime plus one is composite, that least prime is
repeated in the input. -/
theorem least_prime_square {n : ℕ} (hn : 1 < n) (hf : a n = n)
    (hbad : ¬ (2*n.minFac+1).Prime) : n.minFac^2 ∣ n := by
  let p := n.minFac
  let m := n / p
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpn : p ∣ n := Nat.minFac_dvd n
  have he : p*m = n := Nat.mul_div_cancel' hpn
  by_contra h
  have hc : p.Coprime m := hp.coprime_iff_not_dvd.mpr (fun d =>
    h (show p^2 ∣ n by rw [← he, pow_two]; exact Nat.mul_dvd_mul_left p d))
  have hm0 : m ≠ 0 := by rintro hm; rw [hm, mul_zero] at he; omega
  have hm : 1 < m := by
    apply lt_of_not_ge
    intro hb
    have hm1 : m = 1 := Nat.le_antisymm hb (Nat.pos_of_ne_zero hm0)
    rw [hm1,mul_one] at he
    have ha : a p = 1 := by simp [a, hp.properDivisors]
    rw [← he,ha] at hf
    have := hp.one_lt
    omega
  have hh := first_successor hp hm hc (fun q hq hd =>
    Nat.minFac_le_of_dvd hq.two_le (hd.trans (show m ∣ n by rw [← he]; exact dvd_mul_left _ _)))
    (by simpa only [he] using hf)
  exact hbad hh.1

theorem least_prime_one_mod_three {n : ℕ} (hn : 1 < n) (hf : a n = n)
    (hmod : n.minFac % 3 = 1) : n.minFac^2 ∣ n := by
  apply least_prime_square hn hf
  intro hh
  have hp := Nat.minFac_prime (show n ≠ 1 by omega)
  have h3 : 3 ∣ 2*n.minFac+1 := by omega
  have eq := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hh).mp h3
  have htwo := hp.two_le
  omega

private theorem crossing {x y p : ℕ} (hx : 1 < x) (hy : 1 < y)
    (hc : x.Coprime y) (hf : a (x*y) = x*y)
    (hb : (x*y).divisors.card ≤ 2*(p-1)) :
    ∃ q : ℕ, q.Prime ∧ q ∣ y ∧ q < x*p := by
  have h := cut_gcd hx hy hc hf
  have hpos := card_pos (by omega : 0 < x)
  have hg : Nat.gcd y ((∑ d ∈ x.divisors, d * d.divisors.card)) ≠ 1 := by omega
  obtain ⟨q,hq,hqd⟩ := Nat.exists_prime_and_dvd hg
  have hqx := hqd.trans (Nat.gcd_dvd_right _ _)
  have hqy := hqd.trans (Nat.gcd_dvd_left _ _)
  have hy2 := card_two hy
  rw [hc.card_divisors_mul] at hb
  have hmul := Nat.mul_le_mul_left x.divisors.card hy2
  have hxcp : x.divisors.card + 1 ≤ p := by
    have hlarge : 0 < x.divisors.card * 2 := by omega
    omega
  have hs := cut_small hy hx hc.symm (by simpa [Nat.mul_comm] using hf)
  have hax : a x < x := by
    have hle : a x ≤ y.divisors.card * a x := by
      simpa using Nat.mul_le_mul_right (a x) (show 1 ≤ y.divisors.card by omega)
    omega
  rw [moment_eq (by omega : x ≠ 0)] at hqx
  have hqle := Nat.le_of_dvd (Nat.add_pos_left (a_pos hx) _) hqx
  refine ⟨q,hq,hqy,?_⟩
  have hxp := Nat.mul_le_mul_left x hxcp
  nlinarith only [hax, hqle, hxp]

private theorem grow {n p : ℕ} (hf : a n = n)
    (hb : n.divisors.card ≤ 2*(p-1)) (m : ℕ) :
    ∀ A : ℕ, 1 < A → 0 < m → A.Coprime m → A*m = n →
      A*p ≤ p^A.divisors.card → n*p ≤ p^n.divisors.card := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro A hA hm hc he hAheight
    by_cases hm1 : m = 1
    · subst m
      rw [mul_one] at he
      simpa only [← he] using hAheight
    have hms : 1 < m := by omega
    obtain ⟨q, hq, hqm, hql⟩ := crossing hA hms hc (he ▸ hf) (he ▸ hb)
    let e := m.factorization q
    let b := ordCompl[q] m
    have hbp : 0 < b := Nat.ordCompl_pos q hm.ne'
    have hqpos : 0 < e := hq.factorization_pos_of_dvd hm.ne' hqm
    have hsplit : q^e*b = m := Nat.ordProj_mul_ordCompl_eq_self _ _
    have hqc : (q^e).Coprime b := (Nat.coprime_ordCompl hq hm.ne').pow_left _
    have hbc : A.Coprime b := hc.coprime_dvd_right (Nat.ordCompl_dvd m q)
    have hAc : A.Coprime (q^e) := hc.coprime_dvd_right (Nat.ordProj_dvd m q)
    have ht : 1 < q^e := Nat.one_lt_pow hqpos.ne' hq.one_lt
    have hbm : b < m := by rw [← hsplit]; nlinarith only [ht, hbp]
    apply ih b hbm (A*q^e) (by nlinarith only [hA,ht]) hbp
      (Nat.coprime_mul_iff_left.mpr ⟨hbc,hqc⟩) (by rwa [mul_assoc,hsplit])
    rw [hAc.card_divisors_mul, card_pow hq]
    have hpq : q ≤ p^A.divisors.card := hql.le.trans hAheight
    calc
      A*q^e*p = (A*p)*q^e := by ac_rfl
      _ ≤ p^A.divisors.card * (p^A.divisors.card)^e :=
        Nat.mul_le_mul hAheight (Nat.pow_le_pow_left hpq e)
      _ = p^(A.divisors.card*(e+1)) := by rw [pow_mul, pow_succ']

/-- The whole fixed point is bounded in terms of any one prime divisor and
the total divisor count. -/
theorem height {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (hd : p ∣ n)
    (hf : a n = n) : n ≤ p^(n.divisors.card-1) := by
  let e := n.factorization p
  let b := ordCompl[p] n
  have hpos : 0 < e := hp.factorization_pos_of_dvd hn.ne' hd
  have hb := divisor_count_bound hn hp hd hf
  have hg := grow hf hb b (p^e) (Nat.one_lt_pow hpos.ne' hp.one_lt)
    (Nat.ordCompl_pos p hn.ne') ((Nat.coprime_ordCompl hp hn.ne').pow_left e)
    (Nat.ordProj_mul_ordCompl_eq_self n p) (by rw [card_pow hp, pow_succ])
  have hc := card_pos hn
  have hD : n.divisors.card = (n.divisors.card-1)+1 := by omega
  conv_rhs at hg => rw [hD, pow_succ]
  exact Nat.le_of_mul_le_mul_right hg hp.pos

/-- Uniform effective height for a fixed point having a prime divisor at
most the given cutoff, with no hypothesis on the other prime factors. -/
theorem height_of_small_prime {n p P : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hd : p ∣ n) (hle : p ≤ P) (hf : a n = n) : n ≤ P^(2*P-3) := by
  have h := height hn hp hd hf
  have hb := divisor_count_bound hn hp hd hf
  have hpp := hp.two_le
  exact h.trans ((Nat.pow_le_pow_left hle _).trans
    (Nat.pow_le_pow_right (by omega : 0 < P) (by omega)))

/-- A divisor-count cutoff also gives a height bound without specifying any prime. -/
theorem height_of_divisor_count {n : ℕ} (hn : 1 < n) (hf : a n = n) :
    n ≤ (n.divisors.card^2)^(n.divisors.card-1) := by
  let p := n.minFac
  have hpos : 0 < n := by omega
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hsum : p * a n ≤ (n.divisors.card*n.divisors.card)*n := by
    unfold a
    rw [mul_sum]
    calc
      (∑ d ∈ n.properDivisors, p*(d*d.divisors.card)) ≤
          ∑ _d ∈ n.properDivisors, n*n.divisors.card := by
        apply sum_le_sum
        intro d hd
        obtain ⟨k,hk,he⟩ := (Nat.mem_properDivisors_iff_exists hpos.ne').mp hd
        have hkdiv : k ∣ n := ⟨d, by simpa [mul_comm] using he⟩
        have hpk : p ≤ k := Nat.minFac_le_of_dvd hk hkdiv
        have hpd : p*d ≤ n := by rw [he, Nat.mul_comm d k]; exact Nat.mul_le_mul_right d hpk
        have hdc := Finset.card_le_card (Nat.divisors_subset_of_dvd hpos.ne' (Nat.mem_properDivisors.mp hd).1)
        rw [← mul_assoc]
        exact Nat.mul_le_mul hpd hdc
      _ ≤ (n.divisors.card*n.divisors.card)*n := by
        rw [sum_const, nsmul_eq_mul]
        have hc := Finset.card_le_card (Nat.properDivisors_subset_divisors (n := n))
        calc
          _ ≤ n.divisors.card*(n*n.divisors.card) := Nat.mul_le_mul_right _ hc
          _ = _ := by ac_rfl
  rw [hf] at hsum
  have hpD : p ≤ n.divisors.card^2 := by
    rw [pow_two]
    exact Nat.le_of_mul_le_mul_right hsum hpos
  exact (height hpos hp (Nat.minFac_dvd n) hf).trans (Nat.pow_le_pow_left hpD _)

private theorem pow_step {p : ℕ} (hp : p.Prime) (k : ℕ) :
    a (p^(k+1)) = a (p^k) + p^k*(k+1) := by
  simp only [a, Nat.properDivisors_prime_pow hp, sum_map, Function.Embedding.coeFn_mk, card_pow hp, sum_range_succ]

private theorem pow_one_mod {p : ℕ} (hp : p.Prime) (k : ℕ) :
    a (p^(k+1)) % p = 1 := by
  induction k with
  | zero => simp [a, hp.properDivisors, Nat.mod_eq_of_lt hp.one_lt]
  | succ k ih =>
    rw [pow_step hp, Nat.add_mod]
    have hd : p ∣ p^(k+1)*(k+1+1) := (dvd_pow_self p (by omega : k+1 ≠ 0)).trans (dvd_mul_right _ _)
    simp only [Nat.mod_eq_zero_of_dvd hd, Nat.add_zero, ih, Nat.mod_eq_of_lt hp.one_lt]

private theorem gap_lift {p : ℕ} (hp : p.Prime) (k C t : ℕ)
    (hC : 2*a (p^k)+C ≤ p^k) (hs : 2*(k+1)+1+t ≤ p) :
    2*a (p^(k+1))+C+t*p^k ≤ p^(k+1) := by
  rw [pow_step hp, pow_succ]
  nlinarith only [hC, Nat.mul_le_mul_right (p^k) hs]

private theorem gap_one {p : ℕ} (hp : p.Prime) (e : ℕ) (hb : 2*e+1 ≤ p) :
    2*a (p^e)+1 ≤ p^e := by
  induction e with
  | zero => simp [a]
  | succ k ih =>
    simpa using gap_lift hp k 1 0 (ih (by omega)) (by omega)

private theorem pq_budget {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (k : ℕ) (hf : a (p^(k+1)*q) = p^(k+1)*q) : 2*(k+1) < p := by
  have hc := (Nat.coprime_primes hp hq).mpr hpq
  have hpos := pow_pos hp.pos k
  have hq1 := hq.one_lt
  have hh : p*(p^k*q) = p^(k+1)*q := by rw [pow_succ']; ac_rfl
  have h := cofactor_budget hp.one_lt (show 1 < p^k*q by nlinarith)
    (show a (p*(p^k*q)) = p*(p^k*q) by simpa only [hh] using hf)
  have hq2 : q.divisors.card = 2 := by simp [hq.divisors, Ne.symm hq.ne_one]
  rw [(hc.pow_left k).card_divisors_mul, card_pow hp, hq2, mul_comm] at h
  exact h

/-- The gap between the leading power and twice its proper moment divides 2e+3. -/
private theorem pq_gap {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (k : ℕ) (hf : a (p^(k+1)*q) = p^(k+1)*q) :
    p^(k+1)-2*a (p^(k+1)) ∣ 2*(k+1)+3 := by
  let e := k+1
  let P := p^e
  let A := a P
  let T := A+P*(e+1)
  let g := P-2*A
  have hpos : 0 < P := pow_pos hp.pos _
  have hbudget := pq_budget hp hq hpq k hf
  have hgap : 2*A+1 ≤ P := gap_one hp e (by dsimp [e]; omega)
  have hg : g + 2*A = P := Nat.sub_add_cancel (by omega)
  have hc := ((Nat.coprime_primes hp hq).mpr hpq).pow_left e
  have he := cut_balance hpos hq.pos hc hf
  rw [moment_eq hpos.ne', card_pow hp] at he
  have haq : a q = 1 := by simp [a, hq.properDivisors]
  have htq : q.divisors.card = 2 := by simp [hq.divisors, Ne.symm hq.ne_one]
  rw [haq, htq, mul_one] at he
  have hbal : T + q*2*A = P*q := he
  have hqg : q*g = T := by nlinarith only [hbal, congrArg (q*·) hg]
  have hmul : (2*q+1)*g = (2*e+3)*P := by
    dsimp only [T] at hqg
    nlinarith only [hqg,hg]
  have hmult : P ∣ T*(2*q+1) := by
    refine ⟨q*(2*e+3), ?_⟩
    calc
      T*(2*q+1) = q*((2*q+1)*g) := by rw [← hqg]; ring
      _ = P*(q*(2*e+3)) := by rw [hmul]; ring
  have hpP : p ∣ P := dvd_pow_self p (by simp [e])
  have hpT : p.Coprime T := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    have hdA : p ∣ A := (Nat.dvd_add_iff_left (hpP.trans (dvd_mul_right P (e+1)))).mpr hd
    have hmA : A % p = 1 := pow_one_mod hp k
    rw [Nat.mod_eq_zero_of_dvd hdA] at hmA
    omega
  have hdiv : P ∣ 2*q+1 := (hpT.pow_left e).dvd_of_dvd_mul_left hmult
  obtain ⟨w,hw⟩ := hdiv
  refine ⟨w, ?_⟩
  change 2*e+3 = g*w
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc
    P*(2*e+3) = (2*q+1)*g := by simpa only [Nat.mul_comm P] using hmul.symm
    _ = P*(g*w) := by rw [hw]; ring

/-- On every support with two distinct primes and one exponent equal to one,
21 is the only fixed point. Both primes and the other exponent are unrestricted. -/
theorem prime_power_times_prime {p q e : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (he : 0 < e) (hf : a (p^e*q) = p^e*q) : p^e*q = 21 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
  have hb := pq_budget hp hq hpq k hf
  have hd := pq_gap hp hq hpq k hf
  have hu := Nat.le_of_dvd (show 0 < 2*(k+1)+3 by omega) hd
  cases k with
  | zero =>
    have hap : a p = 1 := by simp [a, hp.properDivisors]
    have haq : a q = 1 := by simp [a, hq.properDivisors]
    have hq2 : q.divisors.card = 2 := by simp [hq.divisors, Ne.symm hq.ne_one]
    simp only [zero_add, pow_one] at hf hd ⊢
    rw [hap] at hd
    have h5 : p-2 = 1 ∨ p-2 = 5 := (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd
    have h := cut_balance hp.pos hq.pos ((Nat.coprime_primes hp hq).mpr hpq) hf
    rw [prime_moment hp, hap, haq, hq2] at h
    rcases (show p = 3 ∨ p = 7 by omega) with rfl | rfl <;> omega
  | succ k =>
    cases k with
    | zero =>
      have hap : a p = 1 := by simp [a, hp.properDivisors]
      have hap2 : a (p^2) = 1+2*p := by
        simpa only [pow_one, hap, Nat.mul_comm p 2] using pow_step hp 1
      change p^2-2*a (p^2) ≤ 7 at hu
      change p^2-2*a (p^2) ∣ 7 at hd
      rw [hap2] at hu hd
      have hle : p*p ≤ 7+2*(1+2*p) := by rw [← pow_two]; omega
      have hple : p ≤ 5 := by
        by_contra! h
        nlinarith only [hle, Nat.mul_le_mul_right p (show 6 ≤ p by omega), h]
      have hp5 : p = 5 := by omega
      subst p
      norm_num at hd
    | succ k =>
      have hb' : 2*(k+3)+1 ≤ p := by omega
      have h0 := gap_one hp (k+1) (by omega)
      have h1 := gap_lift hp (k+1) 1 2 h0 (by omega)
      have h2 := gap_lift hp (k+2) (1+2*p^(k+1)) 0 (by simpa only [Nat.add_assoc] using h1) (by omega)
      have hl : p ≤ p^(k+1) := by
        calc
          p = p^1 := by simp
          _ ≤ p^(k+1) := Nat.pow_le_pow_right hp.pos (by omega)
      simp only [zero_mul, add_zero] at h2
      change 2*a (p^(k+3))+(1+2*p^(k+1)) ≤ p^(k+3) at h2
      change p^(k+3)-2*a (p^(k+3)) ≤ 2*(k+3)+3 at hu
      omega

private theorem two_budget {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hneq : p ≠ q)
    (j b : ℕ) (hb : 0 < b) (hf : a (p^(j+1)*q^b) = p^(j+1)*q^b) :
    (j+1)*(b+1) < p := by
  have hq1 := Nat.one_lt_pow hb.ne' hq.one_lt
  have hp0 := pow_pos hp.pos j
  have hh : p*(p^j*q^b) = p^(j+1)*q^b := by rw [pow_succ']; ac_rfl
  have h := cofactor_budget hp.one_lt (show 1 < p^j*q^b by nlinarith)
    (show a (p*(p^j*q^b)) = p*(p^j*q^b) by simpa only [hh] using hf)
  rwa [(Nat.coprime_pow_primes j b hp hq hneq).card_divisors_mul, card_pow hp, card_pow hq] at h

private theorem scaled_gap_step {p : ℕ} (hp : p.Prime) (k c C t : ℕ)
    (hC : c*a (p^k)+C ≤ p^k) (hs : c*(k+1)+1+t ≤ p) :
    c*a (p^(k+1))+C+t*p^k ≤ p^(k+1) := by
  rw [pow_step hp, pow_succ]
  nlinarith only [hC, Nat.mul_le_mul_right (p^k) hs]

private theorem scaled_gap_one {p : ℕ} (hp : p.Prime) (k c : ℕ)
    (hb : c*k < p) : c*a (p^k)+1 ≤ p^k := by
  induction k with
  | zero => simp [a]
  | succ k ih =>
    have hck : c*k < p := (Nat.mul_le_mul_left c (by omega : k ≤ k+1)).trans_lt hb
    simpa using scaled_gap_step hp k c 1 0 (ih hck) (by omega)

private theorem scaled_gap_large {p : ℕ} (hp : p.Prime) (k c : ℕ)
    (hb : c*(k+2) < p) :
    c*a (p^(k+2)) + (1+c*p^k) ≤ p^(k+2) := by
  have hk := scaled_gap_one hp k c ((Nat.mul_le_mul_left c (by omega : k ≤ k+2)).trans_lt hb)
  have h1 := scaled_gap_step hp k c 1 c hk (by nlinarith only [hb])
  have h2 := scaled_gap_step hp (k+1) c (1+c*p^k) 0 (by simpa only [Nat.add_assoc] using h1)
    (by change c*(k+2)+1+0 ≤ p; omega)
  simpa only [zero_mul, add_zero] using h2

private theorem prime_times_proper {q : ℕ} (hq : q.Prime) (b : ℕ) (h : b ≤ q) :
    q*a (q^b) ≤ (b+1)*q^b := by
  induction b with
  | zero => simp [a]
  | succ b ih =>
    have hi := ih (by omega)
    rw [pow_step hq, pow_succ]
    nlinarith only [hi, Nat.mul_le_mul_right (q^b) h]

private theorem prime_power_cross_dvd {p q a' b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hneq : p ≠ q) (ha : 0 < a') (hf : a (p^a'*q^b) = p^a'*q^b) :
    p^a' ∣ a (q^b)+q^b*(b+1) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  let P := p^(k+1)
  let Q := q^b
  have hP : 0 < P := pow_pos hp.pos _
  have hQ : 0 < Q := pow_pos hq.pos _
  have hc := Nat.coprime_pow_primes (k+1) b hp hq hneq
  have hwork := moment_mul hc
  rw [moment_eq (Nat.mul_pos hP hQ).ne', hf, hc.card_divisors_mul,
      moment_eq hP.ne', moment_eq hQ.ne', card_pow hp, card_pow hq] at hwork
  have hmult : P ∣ (a P+P*(k+1+1))*(a Q+Q*(b+1)) := by
    rw [← hwork]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)
  have hd : p ∣ P := dvd_pow_self p (by omega : k+1 ≠ 0)
  have hcT : p.Coprime (a P+P*(k+1+1)) := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hdT
    have hdA := (Nat.dvd_add_iff_left (hd.trans (dvd_mul_right P (k+1+1)))).mpr hdT
    have hm : a P % p = 1 := pow_one_mod hp k
    rw [Nat.mod_eq_zero_of_dvd hdA] at hm
    omega
  exact (hcT.pow_left _).dvd_of_dvd_mul_left hmult

/-- On two-prime support, neither exponent can exceed three times the other. -/
theorem exponent_ratio {p q a' b : ℕ} (hp : p.Prime) (hq : q.Prime) (hneq : p ≠ q)
    (ha : 0 < a') (hb : 0 < b) (hf : a (p^a'*q^b) = p^a'*q^b) : a' ≤ 3*b := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  cases k with
  | zero => omega
  | succ k =>
    let e := k+2
    let P := p^e
    let Q := q^b
    let A := a P
    let B := a Q
    let c := b+1
    let g := P-c*A
    have hP : 0 < P := pow_pos hp.pos _
    have hQ : 0 < Q := pow_pos hq.pos _
    have hPP : 1 < P := Nat.one_lt_pow (by simp [e]) hp.one_lt
    have hQQ : 1 < Q := Nat.one_lt_pow hb.ne' hq.one_lt
    have hc : P.Coprime Q := Nat.coprime_pow_primes _ _ hp hq hneq
    have hpB : c*e < p := by
      simpa only [Nat.mul_comm (k+1+1)] using two_budget hp hq hneq (k+1) b hb hf
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
    have hbudgetQ : b*(e+1) < q := by
      subst b
      exact two_budget hq hp (Ne.symm hneq) j e (by simp [e])
        (by simpa only [Nat.mul_comm (q^(j+1))] using hf)
    have hbq : b ≤ q := (Nat.le_mul_of_pos_right b (by omega : 0 < e+1)).trans hbudgetQ.le
    have hsmallA : A < P := (Nat.le_mul_of_pos_left A (card_pos hQ)).trans_lt
      (cut_small hQQ hPP hc.symm (by simpa only [Nat.mul_comm Q] using hf))
    have hsmallB : B < Q := (Nat.le_mul_of_pos_left B (card_pos hP)).trans_lt
      (cut_small hPP hQQ hc hf)
    have hgap : c*A+(1+c*p^k) ≤ P := scaled_gap_large hp k c hpB
    have hPe : c*A+g = P := Nat.add_sub_of_le (by omega)
    have hdiv := prime_power_cross_dvd hp hq hneq (by dsimp [e]; omega : 0 < e) hf
    have hPcut : P ≤ B+Q*c := Nat.le_of_dvd (by dsimp [c]; positivity) hdiv
    have heq := cut_balance hP hQ hc hf
    rw [moment_eq hP.ne', card_pow hp, card_pow hq] at heq
    have heq' : (A+P*(e+1))*B+Q*c*A=P*Q := heq
    have hQg : Q*g=(A+P*(e+1))*B := by nlinarith only [heq', congrArg (Q*·) hPe]
    have hqB : q*B ≤ c*Q := prime_times_proper hq b hbq
    have hfirst : q*g ≤ c*(A+P*(e+1)) := by
      refine Nat.le_of_mul_le_mul_left ?_ hQ
      calc
        Q*(q*g) = (A+P*(e+1))*(q*B) := by rw [← Nat.mul_assoc, Nat.mul_comm Q q, Nat.mul_assoc, hQg]; ring
        _ ≤ (A+P*(e+1))*(c*Q) := Nat.mul_le_mul_left _ hqB
        _ = Q*(c*(A+P*(e+1))) := by ring
    have hglo : c*p^k < g := by omega
    have hqsmall : q < (e+2)*p^2 := by
      have hc0 : 0 < c := by simp [c]
      have hp0 := pow_pos hp.pos k
      have hh : q*(c*p^k) < q*g := (Nat.mul_lt_mul_left hq.pos).mpr hglo
      have hterm : A+P*(e+1) ≤ (e+2)*P := by nlinarith only [hsmallA]
      have hchain := hh.trans_le (hfirst.trans (Nat.mul_le_mul_left c hterm))
      have hx : P = p^k*p^2 := pow_add p k 2
      rw [hx] at hchain
      apply (Nat.mul_lt_mul_right (Nat.mul_pos hc0 hp0)).mp
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hchain
    have hc2 : 2 ≤ c := by dsimp [c]; omega
    have hpe : e+2 ≤ p := by
      have he2 : 2 ≤ e := by simp [e]
      nlinarith only [hpB, Nat.mul_le_mul_right e hc2, he2]
    have hpc : b+2 ≤ p := by
      have he2 : 2 ≤ e := by simp [e]
      have h := Nat.mul_le_mul_left c he2
      dsimp only [c] at h hpB
      omega
    have hq3 : q < p^3 := by
      calc
        q < (e+2)*p^2 := hqsmall
        _ ≤ p*p^2 := Nat.mul_le_mul_right _ hpe
        _ = p^3 := by ring
    have hend : P < p^(3*b+1) := by
      calc
        P ≤ B+Q*c := hPcut
        _ < Q*(b+2) := by dsimp only [c]; nlinarith only [hsmallB]
        _ ≤ (p^3)^b*p := Nat.mul_le_mul (Nat.pow_le_pow_left hq3.le b) hpc
        _ = p^(3*b+1) := by rw [pow_succ p (3*b), pow_mul p 3 b]
    have := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hend
    change k+2 < 3*b+1 at this
    omega

private theorem proper_pow_sum {p : ℕ} (hp : p.Prime) (e : ℕ) :
    a (p^e) = ∑ j ∈ range e, p^j*(j+1) := by
  simp only [a, Nat.properDivisors_prime_pow hp, sum_map, Function.Embedding.coeFn_mk, card_pow hp]

/-- For one specified exponent, the entire two-prime equality set is effectively bounded. -/
theorem fixed_exponent_height {p q e b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hneq : p ≠ q) (he : 0 < e) (hb : 0 < b) (hf : a (p^e*q^b) = p^e*q^b) :
    let K := (3*b+1)*(b+1)
    p^e*q^b ≤ (K^2)^(K-1) := by
  have hP := Nat.one_lt_pow he.ne' hp.one_lt
  have hQ := Nat.one_lt_pow hb.ne' hq.one_lt
  have h := height_of_divisor_count (show 1 < p^e*q^b by nlinarith) hf
  rw [(Nat.coprime_pow_primes e b hp hq hneq).card_divisors_mul, card_pow hp, card_pow hq] at h
  have hd := Nat.mul_le_mul_right (b+1) (Nat.succ_le_succ (exponent_ratio hp hq hneq he hb hf))
  dsimp only
  exact h.trans ((Nat.pow_le_pow_left (Nat.pow_le_pow_left hd 2) _).trans
    (Nat.pow_le_pow_right (by positivity) (Nat.sub_le_sub_right hd 1)))

private theorem square_table : ∀ p : Fin 46, ∀ e : Fin 7,
    2 ≤ e.val → 3*e.val < p.val →
    let P := p.val^e.val
    let A := ∑ j ∈ range e.val, p.val^j*(j+1)
    let T := A+P*(e.val+1)
    let g := P-3*A
    let z := 2*T/g+1
    z^2*g ≠ T*(2*z+1) := by decide +kernel

private theorem no_square_ordered {p q e : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hneq : p ≠ q) (he : 2 ≤ e) (hpq : p ≤ q) (hf : a (p^e*q^2) = p^e*q^2) : False := by
  let P := p^e
  let Q := q^2
  let A := a P
  let B := a Q
  let T := A+P*(e+1)
  let g := P-3*A
  have hP : 0 < P := pow_pos hp.pos _
  have hQ : 0 < Q := pow_pos hq.pos _
  have hPP : 1 < P := Nat.one_lt_pow (by omega) hp.one_lt
  have hQQ : 1 < Q := Nat.one_lt_pow (by decide : 2 ≠ 0) hq.one_lt
  have hc : P.Coprime Q := Nat.coprime_pow_primes e 2 hp hq hneq
  have hbase : 3*e < p := by
    obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
    subst e
    simpa only [Nat.mul_comm 3] using two_budget hp hq hneq i 2 (by decide) hf
  have hb := exponent_ratio hp hq hneq (by omega : 0 < e) (by decide : 0 < 2) hf
  have hgap : 3*A+1 ≤ P := scaled_gap_one hp e 3 hbase
  have hPe : 3*A+g = P := Nat.add_sub_of_le (by omega)
  have hsm : A < P := by omega
  have ht : T ≤ (e+2)*P := by dsimp only [T]; nlinarith only [hsm]
  have hpA : p*A ≤ (e+1)*P := prime_times_proper hp e (by omega)
  have hpB : p*B ≤ 3*Q := (Nat.mul_le_mul_right B hpq).trans (prime_times_proper hq 2 hq.two_le)
  have hbal := cut_balance hP hQ hc hf
  rw [moment_eq hP.ne', card_pow hp, card_pow hq] at hbal
  have hbal' : T*B+Q*3*A=P*Q := hbal
  have hc1 := Nat.mul_le_mul ht hpB
  have hc2 := Nat.mul_le_mul_left (Q*3) hpA
  have hpc : (P*Q)*p ≤ (P*Q)*(3*(2*e+3)) := by
    nlinarith only [hc1,hc2,congrArg (p*·) hbal']
  have hlimit := Nat.le_of_mul_le_mul_left hpc (Nat.mul_pos hP hQ)
  have ha1 : a q = 1 := by simp [a, hq.properDivisors]
  have hBQ : B = 2*q+1 := by
    simpa only [pow_one,ha1, Nat.mul_comm q 2, Nat.add_comm 1] using pow_step hq 1
  have hgQ : Q*g=T*(2*q+1) := by
    rw [← hBQ]
    nlinarith only [hbal', congrArg (Q*·) hPe]
  have hd : Q ∣ T := prime_power_cross_dvd hq hp hneq.symm (by decide : 0 < 2)
    (by simpa only [Nat.mul_comm (q^2)] using hf)
  obtain ⟨u,hu⟩ := hd
  have hu0 : 0 < u := by
    by_contra! h
    have huZ : u = 0 := by omega
    rw [huZ,mul_zero] at hu
    dsimp only [T] at hu
    have hh := Nat.mul_pos hP (show 0 < e+1 by omega)
    omega
  have hgu : g=(2*q+1)*u := by
    apply Nat.eq_of_mul_eq_mul_left hQ
    rw [hgQ,hu]; ring
  have hq0 := hq.pos
  have hm : q-1+1=q := Nat.sub_add_cancel (by omega)
  have hlow : (q-1)*g ≤ 2*T := by
    have hh := congrArg (·*g) hm
    dsimp only [Q] at hu
    nlinarith only [hh,hu,hgu,congrArg (q*·) hgu, Nat.zero_le (q*u),Nat.zero_le u]
  have hhigh : 2*T < (q-1+1)*g := by
    rw [hm,hgu,hu]
    dsimp only [Q]
    nlinarith only [Nat.mul_pos hq0 hu0]
  have hz : 2*T/g+1=q := by rw [Nat.div_eq_of_lt_le hlow hhigh, hm]
  have htst := square_table ⟨p,by omega⟩ ⟨e,by omega⟩ he hbase
  have hA : A = ∑ j ∈ range e, p^j*(j+1) := proper_pow_sum hp e
  dsimp only at htst
  rw [← hA] at htst
  change (2*T/g+1)^2*g ≠ T*(2*(2*T/g+1)+1) at htst
  rw [hz] at htst
  exact htst hgQ

/-- No fixed point has the shape p^e*q^2 for distinct primes p,q and positive e. -/
theorem prime_power_times_prime_square {p q e : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hneq : p ≠ q) (he : 0 < e) : a (p^e*q^2) ≠ p^e*q^2 := by
  intro hf
  by_cases he1 : e = 1
  · subst e
    have h := prime_power_times_prime hq hp hneq.symm (by decide : 0 < 2)
      (by simpa only [pow_one, Nat.mul_comm (q^2)] using hf)
    have hdiv : q^2 ∣ 21 := ⟨p,h.symm⟩
    have hq21 : q ∣ 21 := (dvd_pow_self q (by decide : 2 ≠ 0)).trans hdiv
    have hh : q = 3 ∨ q = 7 := by
      have hd : q ∣ 3*7 := hq21
      rcases hq.dvd_mul.mp hd with h | h
      · exact Or.inl ((Nat.dvd_prime_two_le (by decide : Nat.Prime 3) hq.two_le).mp h)
      · exact Or.inr ((Nat.dvd_prime_two_le (by decide : Nat.Prime 7) hq.two_le).mp h)
    rcases hh with rfl | rfl <;> norm_num at hdiv
  have he2 : 2 ≤ e := by omega
  by_cases hor : p ≤ q
  · exact no_square_ordered hp hq hneq he2 hor hf
  by_cases heq : e = 2
  · subst e
    exact no_square_ordered (e := 2) hq hp hneq.symm (by decide) (by omega)
      (by simpa only [Nat.mul_comm (q^2)] using hf)
  have hpdvd := prime_power_cross_dvd hp hq hneq he hf
  have hpos := pow_pos hq.pos 2
  have hle := Nat.le_of_dvd (show 0 < a (q^2)+q^2*(2+1) by positivity) hpdvd
  have hq1 := hq.one_lt
  have hp3 : 3 ≤ e := by omega
  have hp5 : 5 ≤ p := by
    obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
    subst e
    have := two_budget hp hq hneq i 2 (by decide) hf
    omega
  have hQ : a (q^2) < q^2 := (Nat.le_mul_of_pos_left _ (card_pos (pow_pos hp.pos e))).trans_lt
    (cut_small (Nat.one_lt_pow he.ne' hp.one_lt) (Nat.one_lt_pow (by decide : 2 ≠ 0) hq.one_lt)
      (Nat.coprime_pow_primes e 2 hp hq hneq) hf)
  have h3 : p^3 ≤ p^e := Nat.pow_le_pow_right hp.pos hp3
  have hqp := Nat.pow_le_pow_left (by omega : q ≤ p) 2
  have hh := Nat.mul_le_mul_right (p^2) hp5
  nlinarith only [hle, hQ, h3, hqp, hh, pow_pos hp.pos 2]

private theorem strict_tail_upper {q : ℕ} (hq : q.Prime) (k : ℕ) :
    q*a (q^(k+1)) < (k+1)*q^(k+1)+a (q^(k+1)) := by
  induction k with
  | zero => simp [a, hq.properDivisors]
  | succ k ih =>
    rw [pow_step hq (k+1), pow_succ q (k+1)]
    nlinarith only [ih, pow_pos hq.pos (k+1)]

private theorem strict_tail_lower {q : ℕ} (hq : q.Prime) (k : ℕ) :
    (k+2)*q^(k+2) < q*a (q^(k+2)) := by
  have hA := a_pos (Nat.one_lt_pow (by omega : k+1 ≠ 0) hq.one_lt)
  rw [show k+2=k+1+1 by rfl, pow_step hq (k+1), pow_succ q (k+1)]
  nlinarith only [Nat.mul_pos hq.pos hA]

/-- The other prime is determined by the first prime and the two exponents.
This is the integer form of the interval in umaia1234's two-prime calculation. -/
theorem candidate_for_second_prime {p q e b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hneq : p ≠ q) (he : 0 < e) (hb : 2 ≤ b) (hf : a (p^e*q^b)=p^e*q^b) :
    let P := p^e
    let A := a P
    let T := A+P*(e+1)
    let g := P-(b+1)*A
    b*T/g+1=q := by
  let P := p^e
  let Q := q^b
  let A := a P
  let B := a Q
  let T := A+P*(e+1)
  let c := b+1
  let g := P-c*A
  have hP : 0<P := pow_pos hp.pos _
  have hQ : 0<Q := pow_pos hq.pos _
  have hT : 0<T := by dsimp only [T]; positivity
  have hbgt : 0 < b := by omega
  have hbgt' : c*e < p := by
    obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
    subst e
    dsimp only [c]
    simpa only [Nat.mul_comm (b+1)] using two_budget hp hq hneq i b hbgt hf
  have hpA : c*A+1 ≤ P := scaled_gap_one hp e c hbgt'
  have hPe : c*A+g = P := Nat.add_sub_of_le (by omega)
  have hc := Nat.coprime_pow_primes e b hp hq hneq
  have hbal := cut_balance hP hQ hc hf
  rw [moment_eq hP.ne',card_pow hp,card_pow hq] at hbal
  have heq : T*B+Q*c*A=P*Q := hbal
  have hQg : Q*g=T*B := by nlinarith only [heq,congrArg (Q*·) hPe]
  have hex : b = (b-2)+2 := by omega
  have hlow : b*Q < q*B := by
    change b*q^b<q*a (q^b)
    simpa only [← hex] using strict_tail_lower hq (b-2)
  have hupp : q*B < b*Q+B := by
    change q*a (q^b)<b*q^b+a (q^b)
    simpa only [show b-1+1=b by omega] using strict_tail_upper hq (b-1)
  have h1 : b*T < q*g := by
    apply (Nat.mul_lt_mul_left hQ).mp
    calc
      Q*(b*T) = T*(b*Q) := by ring
      _ < T*(q*B) := (Nat.mul_lt_mul_left hT).mpr hlow
      _ = Q*(q*g) := by nlinarith only [congrArg (q*·) hQg]
  have h2 : q*g < b*T+g := by
    apply (Nat.mul_lt_mul_left hQ).mp
    calc
      Q*(q*g) = T*(q*B) := by rw [← Nat.mul_assoc, Nat.mul_comm Q q, Nat.mul_assoc, hQg]; ring
      _ < T*(b*Q+B) := (Nat.mul_lt_mul_left hT).mpr hupp
      _ = Q*(b*T+g) := by rw [Nat.mul_add Q, hQg]; ring
  have hq1 : q-1+1=q := Nat.sub_add_cancel (by have := hq.pos; omega)
  have hh := congrArg (·*g) hq1
  have hleft : (q-1)*g ≤ b*T := by nlinarith only [h2,hh]
  have hright : b*T<(q-1+1)*g := by rwa [hq1]
  change b*T/g+1=q
  rw [Nat.div_eq_of_lt_le hleft hright,hq1]

-- Exact integer rejection after choosing the smaller prime and both exponents.
set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
private theorem table_439 :
    (List.range 440).all (fun p =>
      if p.Prime then (List.range ((p-1)/4+1)).all (fun e =>
        if 3 ≤ e then
          let P := p^e
          let A := ∑ j ∈ range e, p^j*(j+1)
          let T := A+P*(e+1)
          (List.range ((p-1)/e)).all (fun b =>
            if 3 ≤ b ∧ e ≤ 3*b ∧ b ≤ 3*e then
              let g := P-(b+1)*A
              let z := b*T/g+1
              decide (z ≤ p ∨ ¬ z^b ∣ T)
            else true)
        else true)
      else true) = true := by decide +kernel

/-- For any two-prime input with smaller prime at most 439, without a size
cutoff on the number or either exponent, the only fixed point is 21. -/
theorem two_prime_through_439 {p q e b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hord : p<q) (h439 : p≤439) (he : 0<e) (hb : 0<b)
    (hf : a (p^e*q^b)=p^e*q^b) : p^e*q^b=21 := by
  have hr := exponent_ratio hp hq hord.ne he hb hf
  have hf' : a (q^b*p^e)=q^b*p^e := by simpa only [Nat.mul_comm (q^b)] using hf
  have hr' := exponent_ratio hq hp hord.ne' hb he hf'
  by_cases hb1 : b=1
  · subst b; simp only [pow_one] at hf ⊢
    exact prime_power_times_prime hp hq hord.ne he hf
  by_cases he1 : e=1
  · subst e; simp only [pow_one] at hf' ⊢
    simpa only [Nat.mul_comm p] using prime_power_times_prime hq hp hord.ne' hb hf'
  by_cases hb2 : b=2
  · subst b; exact (prime_power_times_prime_square hp hq hord.ne he hf).elim
  by_cases he2 : e=2
  · subst e; exact (prime_power_times_prime_square hq hp hord.ne' hb hf').elim
  have h3b : 3 ≤ b := by omega
  have h3e : 3 ≤ e := by omega
  have hbudget : e*(b+1)<p := by
    obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
    subst e; exact two_budget hp hq hord.ne i b hb hf
  have he4 : e ≤ (p-1)/4 := (Nat.le_div_iff_mul_le (by decide : 0<4)).mpr (by
    have hh := Nat.mul_le_mul_left e (show 4≤b+1 by omega); omega)
  have hbb : b+1 ≤ (p-1)/e := (Nat.le_div_iff_mul_le he).mpr (by
    rw [Nat.mul_comm]; omega)
  have hA := proper_pow_sum hp e
  have hcand := candidate_for_second_prime hp hq hord.ne he (by omega : 2≤b) hf
  dsimp only at hcand
  rw [hA] at hcand
  have ht0 := List.all_eq_true.mp table_439 p (List.mem_range.mpr (show p<440 by omega))
  rw [if_pos hp] at ht0
  have ht1 := List.all_eq_true.mp ht0 e (List.mem_range.mpr (show e<(p-1)/4+1 by omega))
  rw [if_pos h3e] at ht1
  have ht2 := List.all_eq_true.mp ht1 b (List.mem_range.mpr (show b<(p-1)/e by omega))
  dsimp only at ht2
  rw [if_pos ⟨h3b,hr,hr'⟩, hcand] at ht2
  have hd := prime_power_cross_dvd hq hp hord.ne' hb hf'
  rw [hA] at hd
  rcases of_decide_eq_true ht2 with h | h
  · omega
  · exact (h hd).elim

/-- The published least-prime computations address these finite ranges. -/
def H1 : Prop := ∀ n : ℕ, 1 < n → n.minFac ≤ 433 →
  n ≤ n.minFac^(2*n.minFac-3) → (n.minFac % 3 = 1 → n.minFac^2 ∣ n) →
  (¬ ∃ p q e b : ℕ, p.Prime ∧ q.Prime ∧ p<q ∧ p≤439 ∧ 0<e ∧ 0<b ∧ n=p^e*q^b) →
  (¬ ∃ p q e : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ 0 < e ∧ (n = p^e*q ∨ n = p^e*q^2)) →
  a n = n → n = 21

/-- The remaining least primes each have a finite height bound. Every
nontrivial coprime cut must also pass the strict gcd inequality. -/
def H2 : Prop := ∀ n : ℕ, 1 < n → 433 < n.minFac →
  n.divisors.card ≤ 2*(n.minFac-1) → n ≤ n.minFac^(n.divisors.card-1) →
  (∀ x y : ℕ, 1 < x → 1 < y → x.Coprime y → x*y = n →
    x.divisors.card < Nat.gcd y (∑ d ∈ x.divisors, d * d.divisors.card)) →
  (¬ ∃ p q e b : ℕ, p.Prime ∧ q.Prime ∧ p<q ∧ p≤439 ∧ 0<e ∧ 0<b ∧ n=p^e*q^b) →
  (¬ ∃ p q e : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ 0 < e ∧ (n = p^e*q ∨ n = p^e*q^2)) →
  a n ≠ n

theorem main : H1 → H2 → type_of% @OeisA245211.conjecture := by
  intro h1 h2 n hn
  constructor
  · intro hf
    have hgt : 1 < n := by
      by_contra! hle
      have hn1 : n = 1 := by omega
      subst n
      have hzero : a 1 = 0 := by decide
      omega
    have hp := Nat.minFac_prime (show n ≠ 1 by omega)
    have hd := Nat.minFac_dvd n
    by_cases hs : ∃ p q e : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ 0 < e ∧ (n = p^e*q ∨ n = p^e*q^2)
    · obtain ⟨p,q,e,hp',hq,hpq,he,heq⟩ := hs
      rcases heq with rfl | rfl
      · exact prime_power_times_prime hp' hq hpq he hf
      · exact (prime_power_times_prime_square hp' hq hpq he hf).elim
    by_cases hz : ∃ p q e b : ℕ, p.Prime ∧ q.Prime ∧ p<q ∧ p≤439 ∧ 0<e ∧ 0<b ∧ n=p^e*q^b
    · obtain ⟨p,q,e,b,hp',hq,ho,hp439,he,hb,rfl⟩ := hz
      exact two_prime_through_439 hp' hq ho hp439 he hb hf
    by_cases hlo : n.minFac ≤ 433
    · exact h1 n hgt hlo (height_of_small_prime hn hp hd le_rfl hf)
        (least_prime_one_mod_three hgt hf) hz hs hf
    · exact (h2 n hgt (by omega) (divisor_count_bound hn hp hd hf) (height hn hp hd hf)
        (fun _ _ hx hy hc he => cut_gcd hx hy hc (by simpa only [he] using hf)) hz hs hf).elim
  · rintro rfl
    decide

end OMA.R_OeisA245211_conjecture_R3
