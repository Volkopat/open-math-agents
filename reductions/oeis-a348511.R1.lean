import OMAStatements.S_oeis_a348511

-- Reduction oeis-a348511.R1
-- Credit: @RiverMint78

namespace OMA.S_oeis_a348511

theorem nextPrime_spec_bounds (p : ℕ) : p < nextPrime p ∧ (nextPrime p).Prime :=
  Nat.find_spec (Nat.exists_infinite_primes (p + 1))

theorem primeShift_mul_of_ne_zero {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    primeShift (a * b) = primeShift a * primeShift b := by
  change (a * b).factorization.prod (fun p e => nextPrime p ^ e) =
    a.factorization.prod (fun p e => nextPrime p ^ e) *
    b.factorization.prod (fun p e => nextPrime p ^ e)
  rw [Nat.factorization_mul ha hb]
  exact Finsupp.prod_add_index' (fun p => pow_zero (nextPrime p)) (fun p => pow_add (nextPrime p))

theorem self_le_primeShift {k : ℕ} (hk : k ≠ 0) : k ≤ primeShift k := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hk]
  rw [Nat.prod_factorization_eq_prod_primeFactors, primeShift]
  exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    (fun p _ => Nat.pow_le_pow_left (nextPrime_spec_bounds p).1.le _)

theorem primeShift_ne_zero_of_ne_zero {k : ℕ} (hk : k ≠ 0) :
    primeShift k ≠ 0 :=
  (Nat.pos_of_ne_zero hk).trans_le (self_le_primeShift hk) |>.ne'

theorem primeShift_le_iterate_succ {k : ℕ} (hk : k ≠ 0) (r : ℕ) :
    primeShift k ≤ (primeShift^[r + 1]) k := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (self_le_primeShift ((Nat.pos_of_ne_zero
      (primeShift_ne_zero_of_ne_zero hk)).trans_le ih).ne')

theorem primeShift_mul_le_of_hit {d m r : ℕ} (hd : d ≠ 0) (hm : m ≠ 0)
    (hit : (primeShift^[r]) (d * m) = 2 * (d * m) + 1) :
    primeShift d * m ≤ 2 * (d * m) + 1 := by
  cases r with
  | zero =>
    simp only [Function.iterate_zero, id_eq] at hit
    omega
  | succ r =>
    calc
      primeShift d * m ≤ primeShift d * primeShift m :=
        Nat.mul_le_mul_left _ (self_le_primeShift hm)
      _ = primeShift (d * m) := (primeShift_mul_of_ne_zero hd hm).symm
      _ ≤ (primeShift^[r + 1]) (d * m) := primeShift_le_iterate_succ (mul_ne_zero hd hm) r
      _ = 2 * (d * m) + 1 := hit

theorem primeShift_pow_prime {p : ℕ} (hp : p.Prime) (e : ℕ) :
    primeShift (p ^ e) = nextPrime p ^ e := by
  rw [primeShift, ← Nat.prod_factorization_eq_prod_primeFactors, hp.factorization_pow]
  exact Finsupp.prod_single_index (pow_zero (nextPrime p))

theorem primeShift_prime {p : ℕ} (hp : p.Prime) :
    primeShift p = nextPrime p := by
  simpa using primeShift_pow_prime hp 1

theorem nextPrime_le_of_prime {p q : ℕ} (hpq : p < q) (hq : q.Prime) :
    nextPrime p ≤ q :=
  Nat.find_min' (Nat.exists_infinite_primes (p + 1)) ⟨hpq, hq⟩

theorem nextPrime_two : nextPrime 2 = 3 :=
  le_antisymm (nextPrime_le_of_prime (by decide) (by decide)) (nextPrime_spec_bounds 2).1

theorem nextPrime_three : nextPrime 3 = 5 := by
  have hu : nextPrime 3 ≤ 5 := nextPrime_le_of_prime (by decide) (by decide)
  obtain ⟨hl, hp⟩ := nextPrime_spec_bounds 3
  interval_cases nextPrime 3 <;> first | rfl | norm_num at hp

theorem nextPrime_five : nextPrime 5 = 7 := by
  have hu : nextPrime 5 ≤ 7 := nextPrime_le_of_prime (by decide) (by decide)
  obtain ⟨hl, hp⟩ := nextPrime_spec_bounds 5
  interval_cases nextPrime 5 <;> first | rfl | norm_num at hp

theorem nextPrime_seven : nextPrime 7 = 11 := by
  have hu : nextPrime 7 ≤ 11 := nextPrime_le_of_prime (by decide) (by decide)
  obtain ⟨hl, hp⟩ := nextPrime_spec_bounds 7
  interval_cases nextPrime 7 <;> first | rfl | norm_num at hp

theorem not_dvd_of_primeShift_ge {d k : ℕ} (hk : 0 < k)
    (h : 2 * d + 2 ≤ primeShift d) (hit : ∃ r, (primeShift^[r]) k = 2 * k + 1) :
    ¬ d ∣ k := by
  rintro ⟨m, rfl⟩
  obtain ⟨r, hr⟩ := hit
  have hd := (Nat.pos_of_ne_zero (left_ne_zero_of_mul hk.ne')).ne'
  have hm := right_ne_zero_of_mul hk.ne'
  have hbound := primeShift_mul_le_of_hit hd hm hr
  have hdl := Nat.mul_le_mul_right m h
  rw [Nat.add_mul, Nat.mul_assoc] at hdl
  have hpos := Nat.pos_of_ne_zero hm
  omega

theorem not_prime_mul_twentyfive_dvd {k p : ℕ} (hk : 0 < k) (hp : p.Prime)
    (hle : p ≤ 97) (hit : ∃ r, (primeShift^[r]) k = 2 * k + 1) : ¬ (25 * p) ∣ k := by
  apply not_dvd_of_primeShift_ge hk ?_ hit
  have hs : primeShift 25 = 49 := by
    change primeShift (5 ^ 2) = 49
    rw [primeShift_pow_prime (by decide), nextPrime_five]
    decide
  rw [primeShift_mul_of_ne_zero (by decide) hp.ne_zero, hs, primeShift_prime hp]
  rcases hp.eq_two_or_odd with rfl | hodd
  · rw [nextPrime_two]
    decide
  obtain ⟨hinc, hprime⟩ := nextPrime_spec_bounds p
  have hnextOdd := (hprime.eq_two_or_odd).resolve_left (by have := hp.two_le; omega)
  have hgap : p + 2 ≤ nextPrime p := by omega
  by_cases heq : p = 97
  · subst p
    have hl : 101 ≤ nextPrime 97 := by
      by_contra! ht
      interval_cases nextPrime 97 <;> norm_num at hprime
    omega
  · omega

end OMA.S_oeis_a348511

namespace A348511

theorem square_bound {p q m m' : ℕ} (hm : 0 < m) (hgrow : m ≤ m')
    (heq : q ^ 2 * m' = 2 * (p ^ 2 * m) + 1) : q ^ 2 ≤ 2 * p ^ 2 + 1 := by
  by_contra! h
  have hδ : 2 * p ^ 2 + 2 ≤ q ^ 2 := by omega
  have hprod : (2 * p ^ 2 + 2) * m ≤ q ^ 2 * m' := Nat.mul_le_mul hδ hgrow
  rw [heq] at hprod
  have he : (2 * p ^ 2 + 2) * m = 2 * (p ^ 2 * m) + 2 * m := by ring
  rw [he] at hprod
  omega

theorem square_bound_of_one_lt {p q m m' : ℕ} (hm : 1 < m) (hgrow : m ≤ m')
    (heq : q ^ 2 * m' = 2 * (p ^ 2 * m) + 1) : q ^ 2 ≤ 2 * p ^ 2 := by
  by_contra! h
  have hprod : (2 * p ^ 2 + 1) * m ≤ q ^ 2 * m' := Nat.mul_le_mul h hgrow
  rw [heq] at hprod
  have he : (2 * p ^ 2 + 1) * m = 2 * (p ^ 2 * m) + m := by ring
  rw [he] at hprod
  omega

end A348511

namespace OMA.S_oeis_a348511

theorem self_le_iterate_primeShift {k : ℕ} (hk : k ≠ 0) (r : ℕ) :
    k ≤ (primeShift^[r]) k := by
  cases r with
  | zero => rfl
  | succ r => exact (self_le_primeShift hk).trans (primeShift_le_iterate_succ hk r)

theorem iterate_primeShift_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (r : ℕ) :
    (primeShift^[r]) (a * b) = (primeShift^[r]) a * (primeShift^[r]) b := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [Function.iterate_succ_apply', ih]
    apply primeShift_mul_of_ne_zero
    · exact (ha.bot_lt.trans_le (self_le_iterate_primeShift ha r)).ne'
    · exact (hb.bot_lt.trans_le (self_le_iterate_primeShift hb r)).ne'

theorem iterate_nextPrime_prime {p : ℕ} (hp : p.Prime) (r : ℕ) :
    ((nextPrime^[r]) p).Prime := by
  cases r with
  | zero => exact hp
  | succ r =>
    rw [Function.iterate_succ_apply']
    exact (nextPrime_spec_bounds _).2

theorem strictMono_nextPrime_iterates (p : ℕ) : StrictMono (fun r => (nextPrime^[r]) p) := by
  apply strictMono_nat_of_lt_succ
  intro r
  rw [Function.iterate_succ_apply']
  exact (nextPrime_spec_bounds _).1

theorem iterate_primeShift_pow_prime {p : ℕ} (hp : p.Prime) (e r : ℕ) :
    (primeShift^[r]) (p ^ e) = ((nextPrime^[r]) p) ^ e := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [Function.iterate_succ_apply', ih]
    exact primeShift_pow_prime (iterate_nextPrime_prime hp r) e

theorem nonsquarefree_hit_has_crt_witness {k r : ℕ} (hk : 0 < k)
    (hn : ¬ Squarefree k) (hr : (primeShift^[r]) k = 2 * k + 1) :
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ k = p ^ 2 * m ∧
      let q := (nextPrime^[r]) p
      q.Prime ∧ p < q ∧ q ^ 2 ≤ 2 * p ^ 2 + 1 ∧
        (1 < m → q ^ 2 ≤ 2 * p ^ 2) ∧
        q ^ 2 ∣ 2 * k + 1 ∧ (primeShift^[r]) m = (2 * k + 1) / q ^ 2 := by
  rw [Nat.squarefree_iff_prime_squarefree] at hn
  push Not at hn
  obtain ⟨p, hp, ⟨m, hkm⟩⟩ := hn
  rw [← pow_two] at hkm
  have hm : 0 < m := Nat.pos_of_ne_zero (right_ne_zero_of_mul (hkm ▸ hk.ne'))
  have hrpos : 0 < r := by
    by_contra! h
    have : r = 0 := by omega
    subst r
    simp only [Function.iterate_zero, id_eq] at hr
    omega
  let q := (nextPrime^[r]) p
  have hq : q.Prime := iterate_nextPrime_prime hp r
  have hgrow : m ≤ (primeShift^[r]) m := self_le_iterate_primeShift hm.ne' r
  have hprod : q ^ 2 * (primeShift^[r]) m = 2 * k + 1 := by
    rw [hkm, iterate_primeShift_mul (pow_ne_zero _ hp.ne_zero) hm.ne',
      iterate_primeShift_pow_prime hp] at hr
    simpa only [hkm, q] using hr
  have hprod' : q ^ 2 * (primeShift^[r]) m = 2 * (p ^ 2 * m) + 1 := by
    simpa only [hkm] using hprod
  refine ⟨p, m, hp, hm, hkm, hq, strictMono_nextPrime_iterates p hrpos,
    A348511.square_bound hm hgrow hprod', fun h => A348511.square_bound_of_one_lt h hgrow hprod',
    ⟨_, hprod.symm⟩, ?_⟩
  rw [← hprod, Nat.mul_div_cancel_left _ (pow_pos hq.pos _)]

end OMA.S_oeis_a348511

namespace OMA.S_oeis_a348511

theorem nextPrime_eleven : nextPrime 11 = 13 := by
  have hu : nextPrime 11 ≤ 13 := nextPrime_le_of_prime (by decide) (by decide)
  obtain ⟨hl, hp⟩ := nextPrime_spec_bounds 11
  interval_cases nextPrime 11 <;> first | rfl | norm_num at hp

theorem nextPrime_thirteen : nextPrime 13 = 17 := by
  have hu : nextPrime 13 ≤ 17 := nextPrime_le_of_prime (by decide) (by decide)
  obtain ⟨hl, hp⟩ := nextPrime_spec_bounds 13
  interval_cases nextPrime 13 <;> first | rfl | norm_num at hp

theorem nextPrime_seventeen : nextPrime 17 = 19 := by
  have hu : nextPrime 17 ≤ 19 := nextPrime_le_of_prime (by decide) (by decide)
  obtain ⟨hl, hp⟩ := nextPrime_spec_bounds 17
  interval_cases nextPrime 17 <;> first | rfl | norm_num at hp

theorem square_image_ge_seventeen {p r : ℕ} (hp : p.Prime) (hr : 2 ≤ r)
    (hq : ((nextPrime^[r]) p) ^ 2 ≤ 2 * p ^ 2 + 1) : 17 ≤ p := by
  have hmono := (strictMono_nextPrime_iterates p).monotone hr
  have hs := (Nat.pow_le_pow_left hmono 2).trans hq
  have hl := hp.two_le
  by_contra! ht
  interval_cases p <;> try norm_num at hp
  all_goals norm_num [Function.iterate_succ_apply', nextPrime_two,
    nextPrime_three, nextPrime_five, nextPrime_seven, nextPrime_eleven,
    nextPrime_thirteen, nextPrime_seventeen] at hs

theorem first_shift_square_prime {p m : ℕ} (hp : p.Prime) (hm : 0 < m)
    (hk : p ^ 2 * m ≠ 4) (hq : (nextPrime p) ^ 2 ≤ 2 * p ^ 2 + 1)
    (hstrong : 1 < m → (nextPrime p) ^ 2 ≤ 2 * p ^ 2) : p = 5 ∨ 11 ≤ p := by
  have hpl := hp.two_le
  by_contra! hn
  obtain ⟨hfive, hu⟩ := hn
  interval_cases p <;> try norm_num at hp
  all_goals (try norm_num [nextPrime_two, nextPrime_three, nextPrime_seven] at hq)
  all_goals (try norm_num at hfive)
  norm_num [nextPrime_two] at hstrong hk
  have he : m = 1 := by omega
  omega

theorem cofactor_five {m : ℕ} (hm : 0 < m) (shift : primeShift (25 * m) = 2 * (25 * m) + 1) :
    ∃ u : ℕ, 0 < u ∧ m = 98 * u - 1 ∧ primeShift m = 100 * u - 1 ∧
      ∀ p : ℕ, p.Prime → p ≤ 97 → ¬ p ∣ m := by
  have hshift : (primeShift^[1]) (25 * m) = 2 * (25 * m) + 1 := by simpa using shift
  have hrough (p : ℕ) (hp : p.Prime) (hp97 : p ≤ 97) : ¬ p ∣ m := by
    intro hpdm
    have hpos : 0 < 25 * m := by omega
    exact not_prime_mul_twentyfive_dvd hpos hp hp97 ⟨1, hshift⟩ (Nat.mul_dvd_mul_left 25 hpdm)
  have hshift25 : primeShift 25 = 49 := by
    change primeShift (5 ^ 2) = 49
    rw [primeShift_pow_prime (by decide), nextPrime_five]
    decide
  rw [primeShift_mul_of_ne_zero (by decide) hm.ne', hshift25] at shift
  have hodd : ¬ 2 ∣ m := hrough 2 (by decide) (by decide)
  have h98 : 98 ∣ m + 1 := by omega
  obtain ⟨u, hu⟩ := h98
  exact ⟨u, by omega, by omega, by omega, hrough⟩

end OMA.S_oeis_a348511

namespace OMA.R_oeis_a348511_R1

open OMA.S_oeis_a348511

/-- If 25 divides a candidate, the shift count is one and its cofactor has
    the form `98*u-1` with no prime factor at most 97. -/
def H1 : Prop :=
  ∀ u : ℕ, 0 < u → (∀ p : ℕ, p.Prime → p ≤ 97 → ¬ p ∣ 98 * u - 1) →
    primeShift (98 * u - 1) ≠ 100 * u - 1

/-- Single shift with a repeated prime at least 11. Test only cofactors in
    the single congruence class giving exact divisibility by the shifted square. -/
def H2 : Prop :=
  ∀ p m : ℕ, p.Prime → 11 ≤ p → 0 < m →
    let q := nextPrime p
    q ^ 2 ≤ 2 * p ^ 2 + 1 → (1 < m → q ^ 2 ≤ 2 * p ^ 2) →
    q ^ 2 ∣ 2 * (p ^ 2 * m) + 1 →
    primeShift m ≠ (2 * (p ^ 2 * m) + 1) / q ^ 2

/-- Two or more shifts force every repeated prime to be at least 17.
    The shifted repeated prime and the cofactor satisfy the same divisor test. -/
def H3 : Prop :=
  ∀ p m r : ℕ, p.Prime → 17 ≤ p → 0 < m → 2 ≤ r →
    let q := (nextPrime^[r]) p
    q ^ 2 ≤ 2 * p ^ 2 + 1 → (1 < m → q ^ 2 ≤ 2 * p ^ 2) →
    q ^ 2 ∣ 2 * (p ^ 2 * m) + 1 →
    (primeShift^[r]) m ≠ (2 * (p ^ 2 * m) + 1) / q ^ 2

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a348511.main := by
  intro h1 h2 h3 k hk h4 ⟨r, hr⟩
  by_contra hsf
  obtain ⟨p, m, hp, hm, hkm, hqp, hpq, hbound, hstrong, hdiv, hcofactor⟩ :=
    nonsquarefree_hit_has_crt_witness hk hsf hr
  have rpos : 0 < r := by
    by_contra! hn
    have hzero : r = 0 := by omega
    subst r
    simp only [Function.iterate_zero, id_eq] at hr
    omega
  by_cases hone : r = 1
  · subst r
    simp only [Function.iterate_one] at hbound hstrong hdiv hcofactor hr
    have hkm4 : p ^ 2 * m ≠ 4 := hkm ▸ h4
    rcases first_shift_square_prime hp hm hkm4 hbound hstrong with hfive | hlarge
    · subst p
      have hkm' : k = 25 * m := hkm
      rw [hkm'] at hr
      obtain ⟨u, hu, hm_eq, hs_eq, hrough⟩ := cofactor_five hm hr
      rw [hm_eq] at hs_eq hrough
      exact h1 u hu hrough hs_eq
    · rw [hkm] at hdiv hcofactor
      exact h2 p m hp hlarge hm hbound hstrong hdiv hcofactor
  · have htwo : 2 ≤ r := by omega
    have hlarge : 17 ≤ p := square_image_ge_seventeen hp htwo hbound
    rw [hkm] at hdiv hcofactor
    exact h3 p m r hp hlarge hm htwo hbound hstrong hdiv hcofactor

end OMA.R_oeis_a348511_R1
