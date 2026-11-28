import OMAStatements.S_oeis_a046528

-- Credit: @grp06
namespace A046528Proof

open Finset
open OMA.S_oeis_a046528

private def geom (p m : ℕ) : ℕ := ∑ i ∈ range m, p ^ i

private lemma geom_dvd {p m n : ℕ} (h : m ∣ n) : geom p m ∣ geom p n := by
  obtain ⟨k, rfl⟩ := h
  induction k with
  | zero => simp [geom]
  | succ k ih =>
    change geom p m ∣ ∑ i ∈ range (m * (k + 1)), p^i
    rw [Nat.mul_succ, sum_range_add]
    apply dvd_add ih
    simp_rw [pow_add]
    rw [← mul_sum]
    exact dvd_mul_left _ _

private lemma sigma_prod {n : ℕ} (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, d) = ∏ p ∈ n.primeFactors, geom p (n.factorization p + 1) := by
  rw [← ArithmeticFunction.sigma_one_apply,
      ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
  simp [geom]

private lemma small_prime {r p q : ℕ} (hr : r.Prime) (hq : q.Prime) (hle : q ≤ r)
    (hdiv : q ∣ geom p r) : q = r ∧ (p : ZMod q) = 1 := by
  let : Fact q.Prime := ⟨hq⟩
  have hzero := (ZMod.natCast_eq_zero_iff _ _).2 hdiv
  simp only [geom, Nat.cast_sum, Nat.cast_pow] at hzero
  have hpow : (p : ZMod q)^r = 1 := by
    have h := geom_sum_mul (p : ZMod q) r
    rw [hzero, zero_mul] at h
    exact sub_eq_zero.mp h.symm
  have hp0 : (p : ZMod q) ≠ 0 := by
    intro hp
    simp [hp, hr.ne_zero] at hpow
  have ho := hr.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hpow)
  have hp1 : (p : ZMod q) = 1 := by
    rcases ho with ho | ho
    · exact orderOf_eq_one_iff.mp ho
    · have h := ZMod.orderOf_dvd_card_sub_one hp0
      rw [ho] at h
      have hbound : r ≤ q - 1 := Nat.le_of_dvd (by have := hq.two_le; omega) h
      exact False.elim ((not_lt_of_ge hle) (hbound.trans_lt (Nat.sub_lt hq.pos (by decide))))
  simp [hp1] at hzero
  exact ⟨(Nat.prime_dvd_prime_iff_eq hq hr).1 ((ZMod.natCast_eq_zero_iff _ _).1 hzero), hp1⟩

private lemma larger_prime {r p : ℕ} (hr : r.Prime) (hr2 : 2 < r) (hp : 1 < p) :
    ∃ q : ℕ, q.Prime ∧ r < q ∧ q ∣ geom p r := by
  by_contra! h
  have bound : r < geom p r := by
    calc
      r = ∑ _i ∈ range r, (1 : ℕ) := by simp
      _ < geom p r := by
        apply sum_lt_sum (fun i _ => Nat.one_le_pow i p (by omega))
        exact ⟨1, mem_range.mpr (by omega), by simpa using hp⟩
  have only : ∀ {q : ℕ}, q.Prime → q ∣ geom p r → q = r := by
    intro q hq hd
    exact (small_prime hr hq (le_of_not_gt (fun hg => h q hq hg hd)) hd).1
  have he := Nat.eq_prime_pow_of_unique_prime_dvd (by omega : geom p r ≠ 0) only
  generalize hk : (geom p r).primeFactorsList.length = k at he
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := by
    cases k with
    | zero => simp at he; omega
    | succ k =>
      cases k with
      | zero => simp at he; omega
      | succ k => exact ⟨k,rfl⟩
  have hs : r^2 ∣ geom p r := by rw [he, pow_add]; exact dvd_mul_left _ _
  have hrS : r ∣ geom p r := dvd_trans (dvd_pow_self _ (by decide : 2 ≠ 0)) hs
  have hp1 := (small_prime hr hr le_rfl hrS).2
  have had : (r : ℤ) ∣ (p : ℤ) - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp [hp1]
  obtain ⟨j, hj⟩ := had
  have hz := odd_sq_dvd_geom_sum₂_sub (1 : ℤ) j (hr.odd_of_ne_two (by omega))
  have hbase : (1 : ℤ) + r * j = p := by omega
  simp only [hbase, one_pow, mul_one] at hz
  have hsi : (r : ℤ)^2 ∣ (geom p r : ℕ) := by exact_mod_cast hs
  push_cast [geom] at hsi
  have bad : (r : ℤ)^2 ∣ (r : ℤ) := (dvd_sub hsi hz) |> fun z => by simpa using z
  have badn : r^2 ∣ r := by exact_mod_cast bad
  have := Nat.le_of_dvd hr.pos badn
  nlinarith


private lemma classify_factor {n p K L : ℕ} (hn : n ≠ 0) (hp : p ∈ n.primeFactors)
    (ht : n.divisors.card = 2^K) (hs : (∑ d ∈ n.divisors, d) = 2^L) :
    n.factorization p = 1 ∧ ∃ k : ℕ, p = 2^k - 1 := by
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hepos := (hpr.dvd_iff_one_le_factorization hn).1 (Nat.dvd_of_mem_primeFactors hp)
  have hτ : n.factorization p + 1 ∣ 2^K := by
    rw [← ht, Nat.card_divisors hn]
    exact dvd_prod_of_mem _ hp
  have hσ : geom p (n.factorization p + 1) ∣ 2^L := by
    rw [← hs, sigma_prod hn]
    exact dvd_prod_of_mem _ hp
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hτ
  have hk1 : k = 1 := by
    cases k with
    | zero => simp at hk; omega
    | succ k =>
      cases k with
      | zero => rfl
      | succ k =>
        exfalso
        have h4 : 4 ∣ n.factorization p + 1 := by
          rw [hk]
          exact pow_dvd_pow 2 (by omega : 2 ≤ k + 1 + 1)
        have hpd : p^2+1 ∣ geom p 4 := by
          use p+1
          simp [geom, sum_range_succ]
          ring
        obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
          (hpd.trans ((geom_dvd h4).trans hσ))
        have hgt : 2 < p ^ 2 + 1 := by nlinarith [hpr.two_le]
        cases j with
        | zero => rw [hj] at hgt; norm_num at hgt
        | succ j =>
          cases j with
          | zero => rw [hj] at hgt; norm_num at hgt
          | succ j =>
            have hbad : 4 ∣ p^2 + 1 := by
              rw [hj]
              exact pow_dvd_pow 2 (by omega : 2 ≤ j + 1 + 1)
            have hz := Nat.mod_eq_zero_of_dvd hbad
            rw [Nat.add_mod, Nat.pow_mod] at hz
            have hlt := Nat.mod_lt p (by decide : 0 < 4)
            interval_cases p % 4 <;> norm_num at hz
  have he : n.factorization p = 1 := by rw [hk1] at hk; simp at hk; omega
  rw [he] at hσ
  have hpd : p+1 ∣ 2^L := by simpa [geom, sum_range_succ, add_comm] using hσ
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hpd
  exact ⟨he, j, by omega⟩

private lemma backward {n : ℕ} (hn : n ≠ 0) {a b : ℕ} (_ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : (∑ d ∈ n.divisors, d)^b = n.divisors.card^a) : IsProdDistinctMersenne n := by
  classical
  let T := n.divisors.card
  let S := ∑ d ∈ n.divisors, d
  have hT : 0 < T := card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr hn⟩
  have hS : 0 < S := by
    dsimp [S]
    rw [← ArithmeticFunction.sigma_one_apply, ArithmeticFunction.sigma_pos_iff]
    exact Nat.pos_of_ne_zero hn
  have transfer {q : ℕ} (hq : q.Prime) : q ∣ S → q ∣ T := by
    intro hd
    apply hq.dvd_of_dvd_pow (n := a)
    rw [← h]
    exact hd.trans (dvd_pow_self S (by omega))
  have unique : ∀ {q : ℕ}, q.Prime → q ∣ T → q = 2 := by
    intro q hq hqT
    by_contra hq2
    have hqmem := (Nat.mem_primeFactors.mpr ⟨hq,hqT,hT.ne'⟩)
    let F := T.primeFactors
    have hF : F.Nonempty := ⟨q,hqmem⟩
    let r := F.max' hF
    have hrmem : r ∈ T.primeFactors := max'_mem _ _
    have hr := Nat.prime_of_mem_primeFactors hrmem
    have hr2 : 2 < r := by have := le_max' F q hqmem; have := hq.two_le; dsimp [r]; omega
    have hd : r ∣ n.divisors.card := Nat.dvd_of_mem_primeFactors hrmem
    rw [Nat.card_divisors hn] at hd
    obtain ⟨p,hp,hrp⟩ := (hr.prime.dvd_finsetProd_iff _).1 hd
    obtain ⟨s,hs,hrs,hds⟩ := larger_prime hr hr2 (Nat.prime_of_mem_primeFactors hp).one_lt
    have hdiv : s ∣ S := by
      dsimp [S]
      rw [sigma_prod hn]
      exact hds.trans ((geom_dvd hrp).trans (dvd_prod_of_mem _ hp))
    have hsF : s ∈ F := Nat.mem_primeFactors.mpr ⟨hs,transfer hs hdiv,hT.ne'⟩
    exact (not_lt_of_ge (le_max' F s hsF)) hrs
  have htwoT := Nat.eq_prime_pow_of_unique_prime_dvd hT.ne' unique
  have htwoS := Nat.eq_prime_pow_of_unique_prime_dvd hS.ne' (p := 2)
    (fun hq hd => unique hq (transfer hq hd))
  have hp (p : ℕ) (hp : p ∈ n.primeFactors) := classify_factor hn hp htwoT htwoS
  refine ⟨n.primeFactors, fun p hm => ⟨Nat.prime_of_mem_primeFactors hm,(hp p hm).2⟩, ?_⟩
  apply Nat.prod_primeFactors_of_squarefree
  apply Nat.squarefree_of_factorization_le_one hn
  intro p
  by_cases hm : p ∈ n.primeFactors
  · exact (hp p hm).1.le
  · rw [← n.support_factorization, Finsupp.notMem_support_iff] at hm
    omega

private lemma forward {n : ℕ} (hn : n ≠ 0) (h : IsProdDistinctMersenne n) :
    ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ (∑ d ∈ n.divisors, d)^b = n.divisors.card^a := by
  classical
  obtain ⟨s, hs, rfl⟩ := h
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1,1,by decide,by decide,by simp⟩
  have primes (q : ℕ) (hq : q ∈ s) := (hs q hq).1
  have expone (q : ℕ) (hq : q ∈ s) : (∏ p ∈ s, p).factorization q = 1 := by
    rw [Nat.factorization_prod_apply (fun p hp => (primes p hp).ne_zero)]
    rw [sum_eq_single q]
    · simp [primes q hq]
    · intro p hp hpq
      exact Nat.factorization_eq_zero_of_not_dvd fun hd => hpq
        ((Nat.prime_dvd_prime_iff_eq (primes q hq) (primes p hp)).mp hd).symm
    · simp [hq]
  let k (p : ℕ) := if hp : p ∈ s then ((hs p hp).2).choose else 0
  have hk (p : ℕ) (hp : p ∈ s) : p + 1 = 2 ^ k p := by
    have h := ((hs p hp).2).choose_spec
    have hpos := Nat.two_pow_pos ((hs p hp).2).choose
    simp only [k, dif_pos hp]
    omega
  have ht : (∏ p ∈ s, p).divisors.card = 2 ^ s.card := by
    rw [Nat.card_divisors hn, Nat.primeFactors_prod primes]
    calc
      _ = ∏ _p ∈ s, (2 : ℕ) := by
        apply prod_congr rfl
        intro p hp
        rw [expone p hp]
      _ = _ := Finset.prod_const 2
  have hσ : (∑ d ∈ (∏ p ∈ s, p).divisors, d) = 2 ^ (∑ p ∈ s, k p) := by
    rw [sigma_prod hn, Nat.primeFactors_prod primes, ← prod_pow_eq_pow_sum]
    apply prod_congr rfl
    intro p hp
    rw [expone p hp, ← hk p hp]
    simp [geom, sum_range_succ, add_comm]
  refine ⟨∑ p ∈ s, k p,s.card,?_,card_pos.mpr hne,?_⟩
  · obtain ⟨p,hp⟩ := hne
    have hh := hk p hp
    have hpos : k p ≠ 0 := by intro hz; rw [hz,pow_zero] at hh; have := (primes p hp).two_le; omega
    exact (Nat.pos_of_ne_zero hpos).trans_le (single_le_sum (f := k) (fun _ _ => Nat.zero_le _) hp)
  · rw [hσ, ht, ← pow_mul, ← pow_mul, Nat.mul_comm]

end A046528Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a046528.main := by
  intro n hn
  exact ⟨A046528Proof.forward (by omega), fun ⟨_,_,ha,hb,h⟩ => A046528Proof.backward (by omega) ha hb h⟩
