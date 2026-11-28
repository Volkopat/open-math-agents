import FormalConjectures.Wikipedia.AgohGiuga

/-!
# Recovering the largest prime from its cofactor

A counterexample has the form m*q, where q is its largest prime. Write D for
the sum of m/r over the prime factors of m and g for m - D % m. The only
possible q is (m-1)/g. This eliminates the search over completions of m.

The first step is an integer reconstruction lemma for a general reciprocal-sum
numerator. The second asks whether the computed candidate can pass the remaining
Korselt test on the old primes. It has just one input, the squarefree cofactor.
-/

namespace OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R3

open AgohGiuga

def H1 : Prop :=
  ∀ m D q k : ℕ, 1 < m → 1 < q → q * D + m = (m * q) * k + 1 →
    q * (m - D % m) = m - 1

def H2 : Prop :=
  ∀ m : ℕ, 1 < m → Odd m → Squarefree m →
    let D := ∑ r ∈ m.primeFactors, m / r
    let g := m - D % m
    let q := (m - 1) / g
    q.Prime → (∀ r ∈ m.primeFactors, r < q) →
    q * g = m - 1 → q - 1 ∣ g →
    ¬ (m.primeFactors.lcm (fun r => r - 1) ∣ m * q - 1)

/- The finite-field power sums, local Giuga and Korselt conditions, squarefreeness,
and parity arguments below are adapted from the merged R2 by subham-n. -/

lemma prime_dvd_sum_pow (p : ℕ) (hp : p.Prime) :
    p ∣ 1 + ∑ i ∈ Finset.Ioo 0 p, i ^ (p - 1 : ℕ) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one, Nat.cast_sum]
  have hsum : ∑ i ∈ Finset.Ioo 0 p, ((i ^ (p - 1 : ℕ) : ℕ) : ZMod p) =
      ∑ _i ∈ Finset.Ioo 0 p, (1 : ZMod p) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Nat.cast_pow]
    rw [Finset.mem_Ioo] at hi
    have hi0 : (i : ZMod p) ≠ 0 := by
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      exact absurd (Nat.le_of_dvd hi.1 h) (not_le_of_gt hi.2)
    exact ZMod.pow_card_sub_one_eq_one hi0
  rw [hsum, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Ioo, Nat.sub_zero]
  rw [← Nat.cast_one, ← Nat.cast_add, Nat.add_sub_of_le hp.one_le, ZMod.natCast_self]

lemma sum_pow_zmod_eq_zero_of_not_dvd {p k : ℕ} [Fact p.Prime] (hk : ¬ (p - 1 ∣ k)) :
    ∑ x : ZMod p, x ^ k = 0 := by
  have hp : p.Prime := Fact.out
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime hp]
  have hgk_ne : (g : ZMod p) ^ k ≠ 1 := by
    intro h
    have h1 : g ^ k = 1 := by
      ext
      simpa [Units.val_pow_eq_pow_val] using h
    rw [← orderOf_dvd_iff_pow_eq_one, hord] at h1
    exact hk h1
  have hmul : (g : ZMod p) ^ k * ∑ x : ZMod p, x ^ k = ∑ x : ZMod p, x ^ k := by
    rw [Finset.mul_sum]
    have hbij : ∑ x : ZMod p, ((g : ZMod p) * x) ^ k = ∑ x : ZMod p, x ^ k := by
      refine Fintype.sum_bijective (fun x : ZMod p => (g : ZMod p) * x) ?_ _ _ (fun _ => rfl)
      exact (Units.mulLeft g).bijective
    simpa [mul_pow] using hbij
  have hsub : ((g : ZMod p) ^ k - 1) * ∑ x : ZMod p, x ^ k = 0 := by
    rw [sub_mul, one_mul, hmul, sub_self]
  exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hgk_ne)

lemma sum_pow_zmod_eq_neg_one_of_dvd {p k : ℕ} [Fact p.Prime] (hk0 : 0 < k) (hk : p - 1 ∣ k) :
    ∑ x : ZMod p, x ^ k = -1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨m, rfl⟩ := hk
  have hterm : ∀ x : ZMod p, x ^ ((p - 1) * m) = if x = 0 then 0 else 1 := by
    intro x
    split_ifs with hx
    · subst hx
      exact zero_pow (Nat.ne_of_gt hk0)
    · rw [pow_mul, ZMod.pow_card_sub_one_eq_one hx, one_pow]
  simp_rw [hterm, Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  have hcard : (Finset.univ.filter (fun x : ZMod p => ¬ x = 0)).card = p - 1 := by
    have h1 : Finset.univ.filter (fun x : ZMod p => ¬ x = 0) = Finset.univ.erase (0 : ZMod p) := by
      ext x
      simp
    rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  rw [hcard, Nat.cast_sub hp.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub]

lemma sum_range_pow_zmod_mul (q p k : ℕ) :
    ((∑ i ∈ Finset.range (q * p), i ^ k : ℕ) : ZMod p) =
      (q : ZMod p) * ∑ r ∈ Finset.range p, (r : ZMod p) ^ k := by
  induction q with
  | zero =>
    simp
  | succ q ih =>
    rw [add_mul, one_mul, Finset.sum_range_add, Nat.cast_add, ih]
    have hblock : ((∑ r ∈ Finset.range p, (q * p + r) ^ k : ℕ) : ZMod p) =
        ∑ r ∈ Finset.range p, (r : ZMod p) ^ k := by
      rw [Nat.cast_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      push_cast
      rw [ZMod.natCast_self, mul_zero, zero_add]
    rw [hblock]
    push_cast
    ring

lemma sum_range_eq_sum_univ_zmod {p k : ℕ} [Fact p.Prime] :
    ∑ r ∈ Finset.range p, (r : ZMod p) ^ k = ∑ x : ZMod p, x ^ k := by
  refine Finset.sum_bij (fun r _ => (r : ZMod p)) ?_ ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro a ha b hb hab
    rw [Finset.mem_range] at ha hb
    have ha' : (a : ZMod p).val = a := ZMod.val_natCast_of_lt ha
    have hb' : (b : ZMod p).val = b := ZMod.val_natCast_of_lt hb
    rw [← ha', ← hb', hab]
  · intro x _
    exact ⟨x.val, Finset.mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
  · intro _ _; rfl

lemma sum_Ioo_eq_sum_range_pow {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    ∑ i ∈ Finset.Ioo 0 n, i ^ k = ∑ i ∈ Finset.range n, i ^ k := by
  have hset : Finset.range n = insert 0 (Finset.Ioo 0 n) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [hset, Finset.sum_insert (by simp), zero_pow (Nat.ne_of_gt hk), zero_add]

/- ### Section 2: Giuga's characterization, squarefreeness, oddness, normal-set property -/

lemma strongGiuga_korselt_and_giuga {n : ℕ} (hsg : IsStrongGiuga n) :
    ∀ p ∈ n.primeFactors, (p - 1) ∣ (n - 1) ∧ p ∣ (n / p - 1) := by
  rcases hsg with ⟨hcomp, hdvd_n⟩
  have hn2 : 2 ≤ n := hcomp.1
  have hn0 : 0 < n := by omega
  have hnm1 : 0 < n - 1 := by omega
  intro p hp
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have : Fact p.Prime := ⟨hp_prime⟩
  have hp_dvd_sum : p ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1 : ℕ) :=
    dvd_trans hp_dvd hdvd_n
  have hz : ((1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1 : ℕ) : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ p).mpr hp_dvd_sum
  rw [Nat.cast_add, Nat.cast_one, sum_Ioo_eq_sum_range_pow hn0 hnm1] at hz
  have hrange : Finset.range n = Finset.range ((n / p) * p) := by
    rw [Nat.div_mul_cancel hp_dvd]
  rw [hrange, sum_range_pow_zmod_mul, sum_range_eq_sum_univ_zmod] at hz
  have hkorselt : (p - 1) ∣ (n - 1) := by
    by_contra hndvd
    rw [sum_pow_zmod_eq_zero_of_not_dvd hndvd, mul_zero, add_zero] at hz
    exact one_ne_zero hz
  have hgiuga : p ∣ (n / p - 1) := by
    rw [sum_pow_zmod_eq_neg_one_of_dvd hnm1 hkorselt, mul_neg_one] at hz
    have hq1 : ((n / p : ℕ) : ZMod p) = 1 := by
      have h1 : (1 : ZMod p) + -((n / p : ℕ) : ZMod p) = 0 := hz
      exact (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h1)).symm
    have hge1 : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd hn0 hp_dvd) hp_prime.pos
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hge1, hq1, Nat.cast_one, sub_self]
  exact ⟨hkorselt, hgiuga⟩

lemma strongGiuga_squarefree {n : ℕ} (hsg : IsStrongGiuga n) : Squarefree n := by
  have hn0 : n ≠ 0 := by have := hsg.1.1; omega
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hpn : p ∣ n := dvd_trans (dvd_mul_right p p) hpp
  have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, hn0⟩
  have hdvd1 : p ∣ n / p - 1 := (strongGiuga_korselt_and_giuga hsg p hmem).2
  rcases hpp with ⟨k, hk⟩
  have hdiv : n / p = p * k := by
    rw [hk, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
  have hdvd2 : p ∣ n / p := ⟨k, hdiv⟩
  have hge1 : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn) hp.pos
  have h1 : p ∣ 1 := by
    have hadd : n / p - 1 + 1 = n / p := Nat.sub_add_cancel hge1
    exact (Nat.dvd_add_right hdvd1).mp (hadd.symm ▸ hdvd2)
  exact hp.not_dvd_one h1

lemma strongGiuga_div_p_mul_pred {n : ℕ} (hsg : IsStrongGiuga n) :
    ∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1) := by
  intro p hp
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hn0 : 0 < n := by have := hsg.1.1; omega
  have hge1 : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd hn0 hp_dvd) hp_prime.pos
  rcases strongGiuga_korselt_and_giuga hsg p hp with ⟨hkorselt, hgiuga⟩
  have hident : n - 1 = p * (n / p - 1) + (p - 1) := by
    have hmul : p * (n / p) = n := Nat.mul_div_cancel' hp_dvd
    have hp1 : 1 ≤ p := hp_prime.one_le
    zify [hp1, hge1, show 1 ≤ n by omega]
    have hmulZ : (p : ℤ) * ((n / p : ℕ) : ℤ) = (n : ℤ) := by exact_mod_cast hmul
    linarith
  have hdvd_pmul : (p - 1) ∣ p * (n / p - 1) := by
    rw [hident] at hkorselt
    exact (Nat.dvd_add_left (dvd_refl (p - 1))).mp hkorselt
  have hcop : Nat.Coprime (p - 1) p := by
    have h1 : p - 1 + 1 = p := Nat.sub_add_cancel hp_prime.one_le
    rw [← h1]
    exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  have hpred : (p - 1) ∣ (n / p - 1) := hcop.dvd_of_dvd_mul_left hdvd_pmul
  exact hcop.symm.mul_dvd_of_dvd_of_dvd hgiuga hpred

lemma dvd_of_squarefree_forall_primeFactors_dvd {n m : ℕ} (hsq : Squarefree n)
    (h : ∀ p ∈ n.primeFactors, p ∣ m) : n ∣ m := by
  rw [← Nat.prod_primeFactors_of_squarefree hsq]
  have haux : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ p ∣ m) → ∏ p ∈ s, p ∣ m := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | @insert a s ha ih =>
      intro hs
      rw [Finset.prod_insert ha]
      have ha_p : a.Prime := (hs a (Finset.mem_insert_self a s)).1
      have ha_d : a ∣ m := (hs a (Finset.mem_insert_self a s)).2
      have hs_d : ∏ p ∈ s, p ∣ m := ih fun p hp => hs p (Finset.mem_insert_of_mem hp)
      have hcop : Nat.Coprime a (∏ p ∈ s, p) := Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes ha_p (hs p (Finset.mem_insert_of_mem hp)).1).mpr
          (fun hEq => ha (hEq ▸ hp))
      exact hcop.mul_dvd_of_dvd_of_dvd ha_d hs_d
  exact haux n.primeFactors fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, h p hp⟩

lemma two_le_primeFactors_card_of_composite_squarefree {n : ℕ} (hcomp : n.Composite)
    (hsq : Squarefree n) : 2 ≤ n.primeFactors.card := by
  have hn0 : n ≠ 0 := by have := hcomp.1; omega
  have hprod := Nat.prod_primeFactors_of_squarefree hsq
  by_contra hlt
  have hle : n.primeFactors.card ≤ 1 := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
  · rw [Finset.card_eq_zero.mp h0, Finset.prod_empty] at hprod
    have := hcomp.1; omega
  · rcases Finset.card_eq_one.mp h1 with ⟨p, hp⟩
    have hmem : p ∈ n.primeFactors := by rw [hp]; simp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hmem
    rw [hp, Finset.prod_singleton] at hprod
    exact hcomp.2 (hprod ▸ hp_prime)

lemma strongGiuga_odd {n : ℕ} (hsg : IsStrongGiuga n) : Odd n := by
  have hsq := strongGiuga_squarefree hsg
  have hcard := two_le_primeFactors_card_of_composite_squarefree hsg.1 hsq
  have hne : (n.primeFactors.erase 2).Nonempty := by
    have hle : n.primeFactors.card - 1 ≤ (n.primeFactors.erase 2).card :=
      Finset.pred_card_le_card_erase
    exact Finset.card_pos.mp (by omega)
  rcases hne with ⟨q, hq⟩
  have hq_ne2 : q ≠ 2 := (Finset.mem_erase.mp hq).1
  have hq_mem : q ∈ n.primeFactors := (Finset.mem_erase.mp hq).2
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
  have hq_odd : q % 2 = 1 := by
    rcases hq_prime.eq_two_or_odd with rfl | hodd
    · exact absurd rfl hq_ne2
    · exact hodd
  have h2_dvd_q1 : 2 ∣ q - 1 := by omega
  have h2_dvd_n1 : 2 ∣ n - 1 := dvd_trans h2_dvd_q1 (strongGiuga_korselt_and_giuga hsg q hq_mem).1
  have hn2 : 2 ≤ n := hsg.1.1
  rcases h2_dvd_n1 with ⟨k, hk⟩
  exact ⟨k, by omega⟩


lemma numerator_eq_one_mod {n : ℕ} (hsg : IsStrongGiuga n) :
    ∃ k : ℕ, (∑ r ∈ n.primeFactors, n / r) = n * k + 1 := by
  have hn2 : 2 ≤ n := hsg.1.1
  have hn0 : n ≠ 0 := by omega
  have hsq := strongGiuga_squarefree hsg
  have hcard := two_le_primeFactors_card_of_composite_squarefree hsg.1 hsq
  set S : ℕ := ∑ p ∈ n.primeFactors, n / p
  have hS_ge2 : 2 ≤ S := by
    have h1 : ∀ p ∈ n.primeFactors, 1 ≤ n / p := fun p hp =>
      Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp))
        (Nat.prime_of_mem_primeFactors hp).pos
    have hsum_ge : n.primeFactors.card ≤ S := by
      simpa using Finset.sum_le_sum h1
    omega
  have hn_dvd : n ∣ S - 1 := by
    refine dvd_of_squarefree_forall_primeFactors_dvd hsq fun p hp => ?_
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hsplit : S = n / p + ∑ q ∈ n.primeFactors.erase p, n / q :=
      (Finset.add_sum_erase _ _ hp).symm
    have hge1 : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hp_dvd) hp_prime.pos
    have hsub_eq : S - 1 = (n / p - 1) + ∑ q ∈ n.primeFactors.erase p, n / q := by omega
    rw [hsub_eq]
    refine dvd_add (strongGiuga_korselt_and_giuga hsg p hp).2 ?_
    refine Finset.dvd_sum fun q hq => ?_
    have hq_ne : q ≠ p := (Finset.mem_erase.mp hq).1
    have hq_mem : q ∈ n.primeFactors := (Finset.mem_erase.mp hq).2
    have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
    have hq_dvd : q ∣ n := Nat.dvd_of_mem_primeFactors hq_mem
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hp_prime hq_prime).mpr (Ne.symm hq_ne)
    rcases hcop.mul_dvd_of_dvd_of_dvd hp_dvd hq_dvd with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [hm, mul_comm p q, mul_assoc, Nat.mul_div_cancel_left _ hq_prime.pos]
  rcases hn_dvd with ⟨k, hk⟩
  exact ⟨k, by omega⟩

theorem weight_mul_prime {m q : ℕ} (hm : 0 < m) (hq : q.Prime) (hc : m.Coprime q) :
    (∑ r ∈ (m * q).primeFactors, m * q / r) = q * (∑ r ∈ m.primeFactors, m / r) + m := by
  have hnot : q ∉ m.primeFactors := fun h =>
    (hq.coprime_iff_not_dvd.mp hc.symm) (Nat.dvd_of_mem_primeFactors h)
  rw [Nat.primeFactors_mul hm.ne' hq.ne_zero, hq.primeFactors, Finset.union_comm]
  simp only [Finset.singleton_union, Finset.sum_insert hnot, Nat.mul_div_cancel _ hq.pos,
    Finset.mul_sum]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [mul_comm m q, Nat.mul_div_assoc q (Nat.dvd_of_mem_primeFactors hr)]


theorem main : H1 → H2 → type_of% @AgohGiuga.agoh_giuga.variants.giuga := by
  intro reconstruct exclude n hn
  constructor
  · exact prime_dvd_sum_pow n
  · intro hsum
    by_contra hnp
    have hs : IsStrongGiuga n := ⟨⟨hn, hnp⟩, hsum⟩
    have hnon : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn
    let q := n.primeFactors.max' hnon
    have hmem : q ∈ n.primeFactors := Finset.max'_mem _ _
    have hq := Nat.prime_of_mem_primeFactors hmem
    let m := n / q
    have he : m * q = n := Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hmem)
    have hm : 1 < m := by
      by_contra! h
      interval_cases m <;> simp_all
    have hsq := strongGiuga_squarefree hs
    rw [← he, Nat.squarefree_mul_iff] at hsq
    have hodd := strongGiuga_odd hs
    rw [← he] at hodd
    have hfac : n.primeFactors = m.primeFactors ∪ q.primeFactors := by
      rw [← he, Nat.primeFactors_mul (by omega) hq.ne_zero]
    have hlt : ∀ r ∈ m.primeFactors, r < q := by
      intro r hr
      have hrn : r ∈ n.primeFactors := hfac ▸ Finset.mem_union_left _ hr
      apply lt_of_le_of_ne (Finset.le_max' _ _ hrn)
      intro h
      change r = q at h
      have hrq : q ∈ m.primeFactors := by rwa [← h]
      exact (hq.coprime_iff_not_dvd.mp hsq.1.symm) (Nat.dvd_of_mem_primeFactors hrq)
    let D := ∑ r ∈ m.primeFactors, m / r
    let g := m - D % m
    obtain ⟨k, hk⟩ := numerator_eq_one_mod hs
    rw [← he, weight_mul_prime (by omega) hq hsq.1] at hk
    have hrec : q * g = m - 1 := reconstruct m D q k hm hq.one_lt hk
    have hg : 0 < g := by
      dsimp [g]; have := Nat.mod_lt D (show 0 < m by omega); omega
    have hrecover : (m - 1) / g = q := by rw [← hrec, Nat.mul_div_cancel _ hg]
    have hd := strongGiuga_div_p_mul_pred hs q hmem
    change q * (q - 1) ∣ m - 1 at hd
    rw [← hrec] at hd
    have hgap : q - 1 ∣ g := (Nat.mul_dvd_mul_iff_left hq.pos).mp hd
    have htest := exclude m hm (Nat.odd_mul.mp hodd).1 hsq.2.1
    change ((m - 1) / g).Prime → (∀ r ∈ m.primeFactors, r < (m - 1) / g) →
      (m - 1) / g * g = m - 1 → (m - 1) / g - 1 ∣ g →
      ¬ (m.primeFactors.lcm (fun r => r - 1) ∣ m * ((m - 1) / g) - 1) at htest
    rw [hrecover] at htest
    apply htest hq hlt hrec hgap
    rw [he, Finset.lcm_dvd_iff]
    intro r hr
    exact (strongGiuga_korselt_and_giuga hs r (hfac ▸ Finset.mem_union_left _ hr)).1

end OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R3
