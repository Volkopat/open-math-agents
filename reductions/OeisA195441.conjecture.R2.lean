import FormalConjectures.OEIS.«195441»

/-!
# Cube-root witnesses for Bernoulli polynomial denominators

The Bernoulli coefficient lemmas, small cases and even exclusion are adapted from
@desenyon's reduction OeisA195441.conjecture.R1. The witness implication uses the
digit-sum characterization of Kellner and Sondow (arXiv:1705.03857, Theorem 2).

For the large range we use Pierre Dusart's explicit Chebyshev theta estimate
(Explicit estimates of some functions over primes, Theorem 4.2 for k = 2).
The prime-counting estimate is a hypothesis.
-/

-- Credit: @MrSeizy
namespace OMA.R_OeisA195441_conjecture_R2

namespace BernoulliWitness

private theorem digit_sum_split (p n : ℕ) (hp : 1 < p) :
    (p.digits n).sum = n%p + (p.digits (n/p)).sum := by
  rcases Nat.eq_zero_or_pos n with rfl | hl
  · simp
  · rw [Nat.digits_eq_cons_digits_div hp hl.ne', List.sum_cons]

/-- Select exactly s units of digit mass from n, without a borrow.
Lucas's theorem keeps the resulting binomial coefficient prime to p. -/
theorem choose_digit_mass {p : ℕ} (hp : p.Prime) (n s : ℕ)
    (hs : s ≤ (p.digits n).sum) :
    ∃ m ≤ n, (p.digits m).sum = s ∧ ¬ p ∣ n.choose m := by
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp at hs
      exact ⟨0, by simp [hs, hp.not_dvd_one]⟩
    let a := min s (n%p)
    have ha : a ≤ n%p := min_le_right ..
    have ha' : a ≤ s := min_le_left ..
    have hap : a < p := ha.trans_lt (Nat.mod_lt _ hp.pos)
    rw [digit_sum_split p n hp.one_lt] at hs
    obtain ⟨b,hb,hbs,hbc⟩ := ih (n/p) (Nat.div_lt_self hn hp.one_lt) (s-a) (by dsimp [a]; omega)
    let m := a+p*b
    have hm : m%p = a := by simp [m, Nat.mod_eq_of_lt hap]
    have hdiv : m/p = b := by simp [m, Nat.add_mul_div_left, hp.pos, Nat.div_eq_of_lt hap]
    have : Fact p.Prime := ⟨hp⟩
    refine ⟨m, ?_, ?_, ?_⟩
    · exact (Nat.add_le_add ha (Nat.mul_le_mul_left p hb)).trans_eq (Nat.mod_add_div n p)
    · rw [digit_sum_split p m hp.one_lt, hm, hdiv, hbs]
      omega
    · have hl := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := n) (k := m)
      rw [hm,hdiv] at hl
      intro hd
      have hmul := (hl.dvd_iff (dvd_refl p)).mp hd
      exact (hp.dvd_mul.mp hmul).elim
        ((hp.coprime_iff_not_dvd).mp (hp.coprime_choose_of_lt (Nat.mod_lt _ hp.pos) ha)) hbc

/-- In the von Staudt--Clausen sum all reciprocal primes other than p
have a common denominator coprime to p. -/
theorem prime_dvd_bernoulli_den {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hd : p-1 ∣ 2*k) : p ∣ (bernoulli (2*k)).den := by
  classical
  let S := (Finset.range (2*k+2)).filter (fun q : ℕ => q.Prime ∧ q-1 ∣ 2*k)
  have mem : p ∈ S := by
    have hle := Nat.le_of_dvd (show 0 < 2*k by omega) hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp, hd⟩
  let rest := ∑ q ∈ S.erase p, (1:ℚ)/q
  have hc : rest.den.Coprime p := by
    apply Nat.Coprime.of_dvd_left (Finset.Rat.den_sum_dvd_prod_den _ _)
    apply Nat.Coprime.prod_left
    intro q hq
    obtain ⟨hne,hq'⟩ := Finset.mem_erase.mp hq
    change q ∈ (Finset.range (2*k+2)).filter (fun q : ℕ => q.Prime ∧ q-1 ∣ 2*k) at hq'
    have hprime : q.Prime := (Finset.mem_filter.mp hq').2.1
    rw [show ((1:ℚ)/q).den = q by simp [hprime.ne_zero]]
    exact (Nat.coprime_primes hprime hp).mpr hne
  obtain ⟨z,hz⟩ := Bernoulli.vonStaudt_clausen k
  change (z:ℚ) = bernoulli (2*k) + ∑ q ∈ S, (1:ℚ)/q at hz
  rw [← Finset.sum_erase_add _ _ mem] at hz
  have hrat : (1:ℚ)/p = z - (bernoulli (2*k) + rest) := by dsimp [rest]; linarith
  have hdvd := Rat.add_den_dvd (bernoulli (2*k)) rest
  have hden := congrArg Rat.den hrat
  simp [hp.ne_zero] at hden
  rw [← hden] at hdvd
  exact (hp.dvd_mul.mp hdvd).resolve_right (hp.coprime_iff_not_dvd.mp hc.symm)

private theorem prime_dvd_scaled_den {c p : ℕ} (q : ℚ) (hp : p.Prime)
    (hc : ¬p ∣ c) (hd : p ∣ q.den) : p ∣ ((c:ℚ)*q).den := by
  have hc0 : c ≠ 0 := fun he => hc (he ▸ dvd_zero _)
  have hh := Rat.mul_den_dvd ((c:ℚ)*q) (1/(c:ℚ))
  have hx : (c:ℚ)*q*(1/(c:ℚ)) = q := by field_simp
  rw [hx, show ((1:ℚ)/(c:ℚ)).den = c by simp [hc0]] at hh
  exact (hp.dvd_mul.mp (hd.trans hh)).resolve_right hc

/-- A prime detected by the digit sum occurs in a nonconstant coefficient. -/
theorem digit_sum_dvd_denominator {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hs : p ≤ (p.digits n).sum) : p ∣ OeisA195441.a (n-1) := by
  have hp2 := hp.two_le
  obtain ⟨m,hm,hmass,hunit⟩ := choose_digit_mass hp n (p-1) (by omega)
  have hlt : m < n := by
    by_contra! hh
    have eqn : m = n := by omega
    rw [eqn] at hmass
    omega
  have hmpos : 0 < m := by
    by_contra! hz
    simp [Nat.eq_zero_of_le_zero hz] at hmass
    omega
  have hden : p ∣ (bernoulli m).den := by
    by_cases htwo : p = 2
    · subst p
      by_cases hm1 : m = 1
      · subst m
        decide +kernel
      · have hme : 2 ∣ m := by
          by_contra hh
          have hmod : m % 2 = 1 := by omega
          rw [digit_sum_split 2 m (by decide), hmod] at hmass
          have hz : (Nat.digits 2 (m/2)).sum = 0 := by omega
          by_cases hq : m/2 = 0
          · omega
          · have he := Nat.getLast_digit_ne_zero 2 hq
            have hall := List.sum_eq_zero_iff.mp hz
            exact he (hall _ (List.getLast_mem _))
        obtain ⟨k,hk⟩ := hme
        rw [hk]
        exact prime_dvd_bernoulli_den hp (by omega) (by simp)
    · have h3 : 2 < p := by omega
      have hbase : p % (p-1) = 1 := by
        conv_lhs => lhs; rw [show p = 1+(p-1) by omega]
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hc := Nat.modEq_digits_sum (p-1) p hbase m
      rw [hmass] at hc
      have hd : p-1 ∣ m := Nat.dvd_of_mod_eq_zero (Eq.trans hc (Nat.mod_self _))
      have hpar := hp.eq_two_or_odd.resolve_left htwo
      have heven : 2 ∣ m := dvd_trans (show 2 ∣ p-1 by omega) hd
      obtain ⟨k,hk⟩ := heven
      rw [hk] at hd ⊢
      exact prime_dvd_bernoulli_den hp (by omega) hd
  rw [OeisA195441.a, show n-1+1 = n by omega]
  have hcoeff := Finset.dvd_lcm (f := fun k =>
    ((n.choose k : ℚ) * bernoulli (n-k)).den) (Finset.mem_Icc.mpr
      (show 1 ≤ n-m ∧ n-m ≤ n by omega))
  apply Dvd.dvd.trans _ hcoeff
  rw [Nat.choose_symm hm, show n-(n-m) = m by omega]
  exact prime_dvd_scaled_den _ hp hunit hden

private theorem ofDigits_zero_sum {b : ℕ} (L : List ℕ) (h : L.sum = 0) :
    Nat.ofDigits b L = 0 := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    simp only [List.sum_cons, Nat.add_eq_zero_iff] at h
    simp [Nat.ofDigits_cons, h.1, ih h.2]

private theorem power_of_one_digit_sum {b n : ℕ} (h : (b.digits n).sum = 1) :
    ∃ e : ℕ, n = b ^ e := by
  suffices aux : ∀ L : List ℕ, L.sum = 1 → ∃ e : ℕ, Nat.ofDigits b L = b ^ e by
    simpa only [Nat.ofDigits_digits] using aux (b.digits n) h
  intro L
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.sum_cons, Nat.ofDigits_cons]
    intro hx
    by_cases h0 : x = 0
    · obtain ⟨e, he⟩ := ih (by omega)
      exact ⟨e + 1, by simp [h0, he, pow_succ']⟩
    · exact ⟨0, by rw [ofDigits_zero_sum L (by omega)]; simp; omega⟩

/-- With digit sum at most two and a nonzero units digit, a multi-digit
number is one more than a power of the base. -/
private theorem one_add_power {p n : ℕ} (hp : 1 < p) (hn : p ≤ n)
    (hu : n % p ≠ 0) (hs : (p.digits n).sum ≤ 2) :
    ∃ j : ℕ, n = 1 + p ^ j := by
  rw [Nat.digits_eq_cons_digits_div hp (by omega), List.sum_cons] at hs
  have hq : 0 < n / p := Nat.div_pos hn (by omega)
  have nz : (p.digits (n / p)).sum ≠ 0 := by
    intro hz
    have hh := ofDigits_zero_sum (b := p) _ hz
    rw [Nat.ofDigits_digits] at hh
    omega
  obtain ⟨e, he⟩ := power_of_one_digit_sum (show (p.digits (n/p)).sum = 1 by omega)
  refine ⟨e+1, ?_⟩
  have hh := Nat.mod_add_div n p
  rw [pow_succ', ← he]
  omega

private theorem two_pow_mod_seven (e : ℕ) :
    2 ^ e % 7 = 1 ∨ 2 ^ e % 7 = 2 ∨ 2 ^ e % 7 = 4 := by
  induction e with
  | zero => decide
  | succ e ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h | h <;> rw [h] <;> decide

private theorem three_pow_mod_eight (e : ℕ) :
    3 ^ e % 8 = 1 ∨ 3 ^ e % 8 = 3 := by
  induction e with
  | zero => decide
  | succ e ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> decide

private theorem seven_pow_mod_sixteen (e : ℕ) :
    7 ^ e % 16 = 1 ∨ 7 ^ e % 16 = 7 := by
  induction e with
  | zero => decide
  | succ e ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> decide

/-- No even integer above eight can pass the three prime tests. -/
theorem exclude_even {n : ℕ} (hn : 8 < n) (he : 2 ∣ n)
    (h : ∀ p : ℕ, p.Prime → p ≤ (p.digits n).sum → p ∣ n+1) : False := by
  have h2 : (Nat.digits 2 n).sum < 2 := by
    by_contra! hge
    have := h 2 (by decide) hge
    omega
  have hpos : (Nat.digits 2 n).sum ≠ 0 := by
    intro hz
    have hh := ofDigits_zero_sum (b := 2) _ hz
    rw [Nat.ofDigits_digits] at hh
    omega
  obtain ⟨e, rfl⟩ := power_of_one_digit_sum (show (Nat.digits 2 n).sum = 1 by omega)
  have ee : 4 ≤ e := by
    by_contra! hsmall
    interval_cases e <;> contradiction
  have h16 : 16 ∣ 2 ^ e := by exact pow_dvd_pow 2 ee
  by_cases h3 : 3 ∣ 2 ^ e + 1
  · have hm := two_pow_mod_seven e
    have h7 : (Nat.digits 7 (2 ^ e)).sum < 7 := by
      by_contra! hh
      have hd := h 7 (by decide) hh
      omega
    have hc := Nat.modEq_digits_sum 6 7 (by decide) (2 ^ e)
    change 2 ^ e % 6 = _ at hc
    obtain ⟨j, hj⟩ := one_add_power (p := 7) (n := 2^e) (by decide) (by omega)
      (by omega) (by omega)
    have := seven_pow_mod_sixteen j
    omega
  · have hsmall : (Nat.digits 3 (2^e)).sum < 3 := by
      by_contra! hh
      exact h3 (h 3 (by decide) hh)
    have hu : 2 ^ e % 3 ≠ 0 := by
      exact fun hh => (by decide : ¬3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero hh))
    obtain ⟨j, hj⟩ := one_add_power (p := 3) (n := 2^e) (by decide) (by omega) hu (by omega)
    have := three_pow_mod_eight j
    omega


set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
/-- Compute the bounded classification with the pinned coefficient LCM. The
lookup table uses the positive B₁ convention of bernoulli'. The kernel checks
its recurrence before the table is used for any coefficient. -/
theorem finite_cases (n : ℕ) (hn : n ≤ 59) :
    (1 ≤ n ∧ OeisA195441.a (n-1) = UniqueFactorizationMonoid.radical (n+1)) ↔
      n ∈ ({3,5,8,9,11,27,29,35,59} : Finset ℕ) := by
  let B : ℕ → ℚ := fun j => ([1, 1/2, 1/6, 0, -1/30, 0,
    1/42, 0, -1/30, 0, 5/66, 0,
    -691/2730, 0, 7/6, 0, -3617/510, 0,
    43867/798, 0, -174611/330, 0, 854513/138, 0,
    -236364091/2730, 0, 8553103/6, 0, -23749461029/870, 0,
    8615841276005/14322, 0, -7709321041217/510, 0, 2577687858367/6, 0,
    -26315271553053477373/1919190, 0, 2929993913841559/6, 0, -261082718496449122051/13530, 0,
    1520097643918070802691/1806, 0, -27833269579301024235023/690, 0, 596451111593912163277961/282, 0,
    -5609403368997817686249127547/46410, 0, 495057205241079648212477525/66, 0, -801165718135489957347924991853/1590, 0,
    29149963634884862421418123812691/798, 0, -2479392929313226753685415739663229/870, 0, 84483613348880041862046775994036021/354] : List ℚ).getD j 0
  have recurrence : ∀ j : Fin 59, B j = 1 - ∑ k : Fin j.val,
      (Nat.fast_choose j k : ℚ) / (j.val - k.val + 1) * B k := by
    dsimp only [B]
    decide +kernel
  have correct (j : ℕ) (hj : j < 59) : bernoulli' j = B j := by
    induction j using Nat.strong_induction_on with
    | h j ih =>
      rw [bernoulli'_def', recurrence ⟨j,hj⟩]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [Nat.choose_eq_fast_choose, ih k k.isLt (by omega)]
  have tableCheck : ∀ i : Fin 60,
      (1 ≤ i.val ∧ (Finset.Icc 1 i.val).lcm (fun k =>
        ((Nat.fast_choose i k : ℚ) * ((-1)^(i.val-k) * B (i.val-k))).den) =
          ∏ p ∈ (i.val+1).primeFactors, p) ↔
      i.val ∈ ({3,5,8,9,11,27,29,35,59} : Finset ℕ) := by
    dsimp only [B]
    decide +kernel
  by_cases hn0 : n = 0
  · subst n
    simp
  have hh : n-1+1 = n := by omega
  rw [OeisA195441.a, hh, Nat.radical_eq_prod_primeFactors]
  have hlcm : (Finset.Icc 1 n).lcm (fun k => ((n.choose k : ℚ) * bernoulli (n-k)).den) =
      (Finset.Icc 1 n).lcm (fun k =>
        ((Nat.fast_choose n k : ℚ) * ((-1)^(n-k) * B (n-k))).den) := by
    apply Finset.lcm_congr rfl
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    simp only [Nat.choose_eq_fast_choose, bernoulli, correct (n-k) (by omega)]
  rw [hlcm]
  exact tableCheck ⟨n,by omega⟩

theorem solution_forces_prime_divisors {n : ℕ} (hn : 0 < n)
    (eqn : OeisA195441.a (n-1) = UniqueFactorizationMonoid.radical (n+1))
    {p : ℕ} (hp : p.Prime) (hs : p ≤ (p.digits n).sum) : p ∣ n+1 := by
  have hd := digit_sum_dvd_denominator hn hp hs
  rw [eqn] at hd
  exact hd.trans UniqueFactorizationMonoid.radical_dvd_self

end BernoulliWitness

namespace DigitSieve

private theorem digitSum_step {p : ℕ} (hp : 1 < p) (n : ℕ) :
    (p.digits n).sum = n % p + (p.digits (n / p)).sum := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [Nat.digits_eq_cons_digits_div hp hn, List.sum_cons]

private theorem mass_div_pow_le {p : ℕ} (hp : 1 < p) (n k : ℕ) :
    (p.digits (n / p^k)).sum ≤ (p.digits n).sum := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Nat.div_div_eq_div_mul]
    have h := ih (n / p)
    rw [digitSum_step hp n]
    omega

private def mass (p : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k+1, n => if n = 0 then 0 else n % p + mass p k (n / p)

private theorem mass_eq {p : ℕ} (hp : 1 < p) (k n : ℕ) (hn : n < p^k) :
    mass p k n = (p.digits n).sum := by
  induction k generalizing n with
  | zero =>
    have : n = 0 := by simpa using hn
    simp [this, mass]
  | succ k ih =>
    by_cases hz : n = 0
    · simp [hz, mass]
    · rw [mass, if_neg hz, digitSum_step hp n, ih]
      exact (Nat.div_lt_iff_lt_mul (by omega)).mpr (by simpa [pow_succ] using hn)

private def checkSparse (p : ℕ) (ok : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, value, _ => ok value
  | k+1, budget, bound, value, place =>
      if bound = 0 then ok value else
        (List.range (min p (min (budget+1) (bound+1)))).all fun d =>
          checkSparse p ok k (budget-d) ((bound-d)/p) (value+place*d) (place*p)

private theorem checkSparse_sound {p : ℕ} (hp : 1 < p) (ok : ℕ → Bool)
    (k budget bound value place j : ℕ) (hj : j ≤ bound) (hlen : j < p^k)
    (hd : (p.digits j).sum ≤ budget)
    (hc : checkSparse p ok k budget bound value place = true) :
    ok (value+place*j) = true := by
  induction k generalizing budget bound value place j with
  | zero =>
    have : j = 0 := by simpa using hlen
    simpa [checkSparse, this] using hc
  | succ k ih =>
    by_cases hb : bound = 0
    · have : j = 0 := by omega
      simpa [checkSparse, hb, this] using hc
    simp only [checkSparse, if_neg hb, List.all_eq_true, List.mem_range] at hc
    rw [digitSum_step hp j] at hd
    have he := Nat.mod_add_div j p
    have hm := Nat.mod_lt j (by omega : 0 < p)
    have hmj := Nat.mod_le j p
    have he' : j/p < p^k :=
      (Nat.div_lt_iff_lt_mul (by omega)).mpr (by simpa [pow_succ] using hlen)
    have hnext := ih (budget-j%p) ((bound-j%p)/p) (value+place*(j%p)) (place*p)
      (j/p) ((Nat.le_div_iff_mul_le (by omega)).mpr (by rw [Nat.mul_comm]; omega))
      he' (by omega)
      (hc (j%p) (by omega))
    have heq : value+place*j = value+place*(j%p)+(place*p)*(j/p) := by
      conv_lhs => rw [← he]
      ring
    exact heq ▸ hnext

private def witnessPrimes : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53]

private theorem witnessPrimes_prime : ∀ p ∈ witnessPrimes, p.Prime ∧ 3 ≤ p := by
  simp only [witnessPrimes, List.mem_cons, List.not_mem_nil, or_false]
  intro p h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private def hasWitness (fuel n : ℕ) : Bool :=
  witnessPrimes.any fun p => n.succ % p != 0 && decide (p ≤ mass p fuel n)

private theorem hasWitness_sound {fuel n : ℕ}
    (hn : n < 3^fuel) (h : hasWitness fuel n = true) :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ n+1 ∧ p ≤ (p.digits n).sum := by
  obtain ⟨p, hmem, htest⟩ := List.any_eq_true.mp h
  obtain ⟨hp, hp3⟩ := witnessPrimes_prime p hmem
  simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at htest
  exact ⟨p, hp, fun hdiv => htest.1 (Nat.mod_eq_zero_of_dvd hdiv),
    (mass_eq hp.one_lt fuel n (hn.trans_le (Nat.pow_le_pow_left hp3 fuel))) ▸ htest.2⟩

private def checkBlock (N fuel M W p j : ℕ) : Bool :=
  let lo := (j*W)/M
  let hi := min ((N+1)/M) (((j+1)*W)/M)
  (List.range (hi-lo)).all fun k =>
    let n := M*(lo+k+1)-1
    decide (n ≤ 59) || n.succ % p == 0 || decide (p ≤ mass p fuel n) ||
      hasWitness fuel n

private theorem checkBlock_sound {N fuel M W p j n : ℕ}
    (hM : 0 < M) (hW : 0 < W) (hp : p.Prime) (hf : N < 3^fuel)
    (hp3 : 3 ≤ p) (hn : 59 < n) (hN : n ≤ N) (hMdiv : M ∣ n+1)
    (hmiss : ¬ p ∣ n+1) (hj : j = n/W) (hc : checkBlock N fuel M W p j = true) :
    ∃ r : ℕ, r.Prime ∧ ¬r ∣ n+1 ∧ r ≤ (r.digits n).sum := by
  let t := (n+1)/M
  let lo := (j*W)/M
  let hi := min ((N+1)/M) (((j+1)*W)/M)
  have ht : M*t = n+1 := by rw [Nat.mul_comm]; exact Nat.div_mul_cancel hMdiv
  have hl : j*W ≤ n := by rw [hj]; exact Nat.div_mul_le_self _ _
  have hu : n+1 ≤ (j+1)*W := by
    rw [hj]
    exact (Nat.div_lt_iff_lt_mul hW).mp (Nat.lt_succ_self (n/W))
  have hlo : lo < t := by apply (Nat.div_lt_iff_lt_mul hM).mpr; rw [Nat.mul_comm t M, ht]; omega
  have hhi : t ≤ hi := by
    apply le_min (Nat.div_le_div_right (Nat.succ_le_succ hN))
    exact Nat.div_le_div_right hu
  have hm : t-lo-1 ∈ List.range (hi-lo) := by simp only [List.mem_range]; omega
  have htest := List.all_eq_true.mp hc (t-lo-1) hm
  have he : lo+(t-lo-1)+1 = t := by omega
  change (decide (M*(lo+(t-lo-1)+1)-1 ≤ 59) ||
      (M*(lo+(t-lo-1)+1)-1).succ % p == 0 ||
      decide (p ≤ mass p fuel (M*(lo+(t-lo-1)+1)-1)) ||
      hasWitness fuel (M*(lo+(t-lo-1)+1)-1)) = true at htest
  rw [he, ht, Nat.add_sub_cancel] at htest
  simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at htest
  rcases htest with ((hlt | hd) | hm) | hw
  · omega
  · exact (hmiss (Nat.dvd_of_mod_eq_zero hd)).elim
  · exact ⟨p, hp, hmiss, (mass_eq hp.one_lt fuel n
      (hN.trans_lt (hf.trans_le (Nat.pow_le_pow_left hp3 fuel)))) ▸ hm⟩
  · exact hasWitness_sound (hN.trans_lt hf) hw

private theorem sparseStage {N fuel M W p k n : ℕ} (hM : 0 < M)
    (hp : p.Prime) (hp3 : 3 ≤ p) (hf : N < 3^fuel) (hN : n ≤ N)
    (hn : 59 < n) (hodd : n % 2 = 1) (hMdiv : M ∣ n+1) (hmiss : ¬p ∣ n+1)
    (u : ℕ) (hW : W = p^u) (hk : N/W < p^k)
    (hc : checkSparse p (checkBlock N fuel M W p) k (p-2) (N/W) 0 1 = true) :
    ∃ r : ℕ, r.Prime ∧ ¬r ∣ n+1 ∧ r ≤ (r.digits n).sum := by
  by_cases hs : p ≤ (p.digits n).sum
  · exact ⟨p, hp, hmiss, hs⟩
  have hpodd := hp.eq_two_or_odd.resolve_left (by omega)
  have hpar := Nat.modEq_digits_sum 2 p hpodd (n := n)
  change n % 2 = (p.digits n).sum % 2 at hpar
  have hbudget : (p.digits (n/W)).sum ≤ p-2 := by
    rw [hW]
    have h := mass_div_pow_le hp.one_lt n u
    omega
  have hj := Nat.div_le_div_right (c := W) hN
  have htest := checkSparse_sound hp.one_lt _ _ _ _ _ _ _ hj (hj.trans_lt hk) hbudget hc
  simp only [Nat.one_mul, Nat.zero_add] at htest
  exact checkBlock_sound (n := n) hM (hW ▸ pow_pos hp.pos u) hp hf hp3 hn hN hMdiv hmiss rfl htest

private def checkTail (N fuel M : ℕ) : Bool :=
  (List.range ((N+1)/M)).all fun j =>
    let n := M*(j+1)-1
    decide (n ≤ 59) || hasWitness fuel n

private theorem checkTail_sound {N fuel M n : ℕ}
    (hf : N < 3^fuel) (hN : n ≤ N) (hn : 59 < n) (hMdiv : M ∣ n+1)
    (hc : checkTail N fuel M = true) :
    ∃ r : ℕ, r.Prime ∧ ¬r ∣ n+1 ∧ r ≤ (r.digits n).sum := by
  let t := (n+1)/M
  have he : M*t = n+1 := by rw [Nat.mul_comm]; exact Nat.div_mul_cancel hMdiv
  have ht : 0 < t := by
    exact Nat.pos_of_ne_zero (fun ht0 => by simp [ht0] at he)
  have ht' : t ≤ (N+1)/M := Nat.div_le_div_right (Nat.succ_le_succ hN)
  have htmem : t-1 ∈ List.range ((N+1)/M) := List.mem_range.mpr (by omega)
  have htest := List.all_eq_true.mp hc (t-1) htmem
  change (decide (M*((t-1)+1)-1 ≤ 59) || hasWitness fuel (M*((t-1)+1)-1)) = true at htest
  rw [show t-1+1=t by omega, he, Nat.add_sub_cancel] at htest
  simp only [Bool.or_eq_true, decide_eq_true_eq] at htest
  exact hasWitness_sound (hN.trans_lt hf) (htest.resolve_left (by omega))

private theorem stageOrNext {N fuel M p k n : ℕ}
    (hM : 0 < M) (hp : p.Prime) (hp3 : 3 ≤ p) (hcop : M.Coprime p)
    (hf : N < 3^fuel) (hN : n ≤ N) (hn : 59 < n) (hodd : n % 2 = 1)
    (hMdiv : M ∣ n+1) (u : ℕ) (hk : N/p^u < p^k)
    (hc : checkSparse p (checkBlock N fuel M (p^u) p) k (p-2) (N/p^u) 0 1 = true)
    (next : M*p ∣ n+1 → ∃ r : ℕ, r.Prime ∧ ¬r ∣ n+1 ∧ r ≤ (r.digits n).sum) :
    ∃ r : ℕ, r.Prime ∧ ¬r ∣ n+1 ∧ r ≤ (r.digits n).sum := by
  by_cases h : p ∣ n+1
  · exact next (hcop.mul_dvd_of_dvd_of_dvd hMdiv h)
  · exact sparseStage hM hp hp3 hf hN hn hodd hMdiv h u rfl hk hc

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem cert3 :
    checkSparse 3 (checkBlock 100000000 17 2 (3^1) 3) 16 (3-2)
      (100000000/3^1) 0 1 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem cert5 :
    checkSparse 5 (checkBlock 100000000 17 6 (5^2) 5) 10 (5-2)
      (100000000/5^2) 0 1 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem cert7 :
    checkSparse 7 (checkBlock 100000000 17 30 (7^2) 7) 8 (7-2)
      (100000000/7^2) 0 1 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem cert11 :
    checkSparse 11 (checkBlock 100000000 17 210 (11^3) 11) 5 (11-2)
      (100000000/11^3) 0 1 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem cert13 :
    checkSparse 13 (checkBlock 100000000 17 2310 (13^4) 13) 4 (13-2)
      (100000000/13^4) 0 1 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem certTail : checkTail 100000000 17 30030 = true := by
  decide +kernel

theorem boundedWitness {n : ℕ} (hn : 59 < n) (hN : n ≤ 100000000)
    (hodd : n % 2 = 1) : ∃ p : ℕ, p.Prime ∧ ¬p ∣ n+1 ∧ p ≤ (p.digits n).sum := by
  have hf : 100000000 < 3^17 := by decide
  have hd : 2 ∣ n+1 := by omega

  apply stageOrNext (M := 2) (p := 3) (k := 16) (n := n)
    (by decide) (by decide) (by decide) (by decide) hf hN hn hodd hd 1 (by decide) cert3
  intro hd3
  clear hd
  have hd : 6 ∣ n+1 := hd3
  apply stageOrNext (M := 6) (p := 5) (k := 10) (n := n)
    (by decide) (by decide) (by decide) (by decide) hf hN hn hodd hd 2 (by decide) cert5
  intro hd5
  clear hd
  have hd : 30 ∣ n+1 := hd5
  apply stageOrNext (M := 30) (p := 7) (k := 8) (n := n)
    (by decide) (by decide) (by decide) (by decide) hf hN hn hodd hd 2 (by decide) cert7
  intro hd7
  clear hd
  have hd : 210 ∣ n+1 := hd7
  apply stageOrNext (M := 210) (p := 11) (k := 5) (n := n)
    (by decide) (by decide) (by decide) (by decide) hf hN hn hodd hd 3 (by decide) cert11
  intro hd11
  clear hd
  have hd : 2310 ∣ n+1 := hd11
  apply stageOrNext (M := 2310) (p := 13) (k := 4) (n := n)
    (by decide) (by decide) (by decide) (by decide) hf hN hn hodd hd 4 (by decide) cert13
  intro hd13
  clear hd
  have hd : 30030 ∣ n+1 := hd13
  exact checkTail_sound hf hN hn hd certTail

end DigitSieve

namespace CubeWitness

private theorem digitSum_step {p : ℕ} (hp : 1 < p) (n : ℕ) :
    (p.digits n).sum = n % p + (p.digits (n / p)).sum := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [Nat.digits_eq_cons_digits_div hp hn, List.sum_cons]

private theorem phase_lower {n m p : ℕ} (hn : m^3 ≤ n) (hmp : m ≤ p) (hp : 0 < p) :
    0 ≤ (n : ℝ)/(p : ℝ)^2 + 2*p - 3*m := by
  have hn' : (m : ℝ)^3 ≤ n := by exact_mod_cast hn
  have hmp' : (m : ℝ) ≤ p := by exact_mod_cast hmp
  have h0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hx : 0 ≤ (n : ℝ) + (p-m)^2*(2*p+m) - (m : ℝ)^3 := by
    have : 0 ≤ ((p:ℝ)-m)^2*(2*p+m) := by positivity
    linarith
  apply (nonneg_of_mul_nonneg_right ?_ (sq_pos_of_pos h0))
  rw [mul_comm]
  calc
    ((n : ℝ)/(p : ℝ)^2 + 2*p - 3*m)*(p : ℝ)^2 =
      (n : ℝ) + (p-m)^2*(2*p+m) - (m : ℝ)^3 := by field_simp; ring
    _ ≥ 0 := hx

private theorem real_div_bounds (n p : ℕ) (hp : 0 < p) :
    ((n/p^2 : ℕ) : ℝ) ≤ (n : ℝ)/(p : ℝ)^2 ∧
    (n : ℝ)/(p : ℝ)^2 < ((n/p^2 : ℕ) : ℝ) + 1 := by
  have hpos : (0 : ℝ) < p := by exact_mod_cast hp
  constructor
  · apply (le_div_iff₀ (sq_pos_of_pos hpos)).mpr
    exact_mod_cast Nat.div_mul_le_self n (p^2)
  · apply (div_lt_iff₀ (sq_pos_of_pos hpos)).mpr
    exact_mod_cast (Nat.div_lt_iff_lt_mul (pow_pos hp 2)).mp (Nat.lt_succ_self (n/p^2))

private noncomputable def phase (n m p : ℕ) : ℝ := (n : ℝ)/(p : ℝ)^2 + 2*p - 3*m

private def phaseIndex (n m p : ℕ) : ℕ := n/p^2 + 2*p - 3*m

private theorem phaseIndex_cast {n m p : ℕ} (hn : m^3 ≤ n) (hmp : m ≤ p) (hp : 0 < p) :
    (phaseIndex n m p : ℝ) = ((n/p^2 : ℕ) : ℝ) + 2*p - 3*m := by
  have hge : 3*m ≤ n/p^2 + 2*p := by
    by_contra! hx
    have hy : (↑(n/p^2) : ℝ) + 2*p + 1 ≤ 3*m := by exact_mod_cast hx
    linarith [phase_lower hn hmp hp, (real_div_bounds n p hp).2]
  unfold phaseIndex
  rw [Nat.cast_sub hge]
  push_cast
  rfl

private theorem phaseIndex_le {n m p : ℕ} (hn : m^3 ≤ n) (hmp : m ≤ p) (hp : 0 < p) :
    (phaseIndex n m p : ℝ) ≤ phase n m p := by
  rw [phaseIndex_cast hn hmp hp, phase]
  linarith [(real_div_bounds n p hp).1]

private theorem phaseIndex_bound {n m p L : ℕ} (hm : 0 < m)
    (hn : m^3 ≤ n) (hn' : n < (m+1)^3) (hmp : m+1 ≤ p) (hpL : p ≤ m+L) :
    phaseIndex n m p ≤ 3 + 3*L^2/m := by
  have hp : 0 < p := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hmpR : (m : ℝ)+1 ≤ p := by exact_mod_cast hmp
  have hnR : (n : ℝ) < ((m : ℝ)+1)^3 := by exact_mod_cast hn'
  have hpLR : (p : ℝ) ≤ m+L := by exact_mod_cast hpL
  have hsq : ((m:ℝ)+1)^2 ≤ (p:ℝ)^2 := by gcongr
  have hpart₁ : ((n:ℝ)-(m:ℝ)^3)/(p:ℝ)^2 ≤ 3 := by
    apply (div_le_iff₀ (sq_pos_of_pos hp0)).mpr
    linarith only [hnR, (show ((m:ℝ)+1)^3-(m:ℝ)^3 ≤ 3*((m:ℝ)+1)^2 by nlinarith), hsq]
  have hpart₂ : ((p:ℝ)-m)^2*(2*p+m)/(p:ℝ)^2 ≤ 3*(L:ℝ)^2/m := by
    calc
      _ ≤ (L:ℝ)^2*(3*p)/(p:ℝ)^2 := by
        have hh : 0 ≤ (p:ℝ)-m := by linarith
        gcongr <;> linarith
      _ = 3*(L:ℝ)^2/p := by field_simp
      _ ≤ 3*(L:ℝ)^2/m := by
        apply div_le_div_of_nonneg_left (by positivity) hm0
        linarith
  have hx : phase n m p = ((n:ℝ)-(m:ℝ)^3)/(p:ℝ)^2 +
      ((p:ℝ)-m)^2*(2*p+m)/(p:ℝ)^2 := by
    unfold phase
    field_simp
    ring
  have hbound := phaseIndex_le hn (show m ≤ p by omega) hp
  have hr : (phaseIndex n m p : ℝ) ≤ 3 + 3*(L:ℝ)^2/m := by linarith
  let w : ℕ := 3*L^2/m
  have hd : 3*(L:ℝ)^2/m < (w : ℝ)+1 := by
    apply (div_lt_iff₀ hm0).mpr
    exact_mod_cast (Nat.div_lt_iff_lt_mul hm).mp (show 3*L^2/m < w+1 by exact Nat.lt_succ_self w)
  have hh : phaseIndex n m p < 3 + w + 1 := by
    exact_mod_cast (show (phaseIndex n m p : ℝ) < 3 + (w : ℝ)+1 by linarith)
  change phaseIndex n m p ≤ 3 + w
  omega

private theorem phase_close_of_bad {n m p : ℕ}
    (hn : m^3 ≤ n) (hn' : n < (m+1)^3) (hmp : m+1 ≤ p) (hp : 1 < p)
    (hbad : (p.digits n).sum < p) :
    phase n m p < (phaseIndex n m p : ℝ) + 3*((p:ℝ)-m)/p := by
  let a := n/p^2
  let b := (n/p)%p
  let c := n%p
  have hlt : n < p^3 := hn'.trans_le (Nat.pow_le_pow_left hmp 3)
  have ha : a < p := (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by
    simpa [pow_succ'] using hlt)
  have hc : c < p := Nat.mod_lt _ (by omega)
  have hval : n = a*p^2 + b*p + c := by
    have hn₁ := Nat.mod_add_div n p
    have hn₂ := Nat.mod_add_div (n/p) p
    rw [Nat.div_div_eq_div_mul, ← pow_two] at hn₂
    change b + p*a = n/p at hn₂
    rw [← hn₂] at hn₁
    change c + p*(b + p*a) = n at hn₁
    rw [← hn₁]
    ring
  have hdigs : (p.digits n).sum = c+b+a := by
    rw [digitSum_step hp n, digitSum_step hp (n/p), Nat.div_div_eq_div_mul, ← pow_two]
    have ht : (p.digits a).sum = a := by
      by_cases ha0 : a = 0
      · simp [ha0]
      · rw [Nat.digits_of_lt p a ha0 ha, List.sum_singleton]
    change c+(b+(p.digits a).sum) = _
    rw [ht, Nat.add_assoc]
  rw [hdigs] at hbad
  have hp0 : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hf := phaseIndex_cast hn (show m ≤ p by omega) (show 0 < p by omega)
  have haR : (0:ℝ) ≤ (phaseIndex n m p : ℝ) := by positivity
  have hbr : (b:ℝ)+1 ≤ (p:ℝ)-a := by
    have h : b+1+a ≤ p := by omega
    have h' : (b:ℝ)+1+a ≤ p := by exact_mod_cast h
    linarith
  have hcR : (c:ℝ) < p := by exact_mod_cast hc
  have hvR : (n:ℝ) = a*(p:ℝ)^2 + b*p + c := by exact_mod_cast hval
  have he : (n:ℝ) < a*(p:ℝ)^2 + (p-a)*p := by
    nlinarith [mul_le_mul_of_nonneg_right hbr hp0.le]
  have hfrac : (n:ℝ)/(p:ℝ)^2 < (a:ℝ)+((p:ℝ)-a)/p := by
    apply (div_lt_iff₀ (sq_pos_of_pos hp0)).mpr
    have heq : ((a:ℝ)+((p:ℝ)-a)/p)*(p:ℝ)^2 = a*(p:ℝ)^2+(p-a)*p := by
      field_simp
    rwa [heq]
  have hbnd : ((p:ℝ)-a)/p ≤ 3*((p:ℝ)-m)/p := by
    apply div_le_div_of_nonneg_right _ hp0.le
    change _ = (a:ℝ) + 2*p - 3*m at hf
    linarith
  rw [phase, hf]
  change (n:ℝ)/(p:ℝ)^2 + 2*p - 3*m < (a:ℝ) + 2*p - 3*m + _
  linarith

private theorem phase_separation {n m q p : ℕ}
    (hn' : n < (m+1)^3) (hq : m+1 ≤ q) (hp : m+4 ≤ p) (hgap : q+2 ≤ p) :
    phase n m q + 3*((p:ℝ)-m)/p ≤ phase n m p := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hq0 : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqR : (m:ℝ)+1 ≤ q := by exact_mod_cast hq
  have hpR : (m:ℝ)+4 ≤ p := by exact_mod_cast hp
  have hgapR : (q:ℝ)+2 ≤ p := by exact_mod_cast hgap
  have hnR : (n:ℝ) < ((m:ℝ)+1)^3 := by exact_mod_cast hn'
  have hnq : (n:ℝ)/(q:ℝ)^2 ≤ (m:ℝ)+1 := by
    apply (div_le_iff₀ (sq_pos_of_pos hq0)).mpr
    calc
      _ ≤ ((m:ℝ)+1)^3 := hnR.le
      _ = ((m:ℝ)+1)*((m:ℝ)+1)^2 := by ring
      _ ≤ _ := by gcongr
  have hratio : ((p:ℝ)+q)/(p:ℝ)^2 ≤ 2/p := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hp0) hp0).mpr
    have hle : (q:ℝ) ≤ p := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hle hp0.le]
  have he : phase n m p - phase n m q =
      2*((p:ℝ)-q) - ((n:ℝ)/(q:ℝ)^2)*(((p:ℝ)+q)/(p:ℝ)^2)*((p:ℝ)-q) := by
    unfold phase
    field_simp
    ring
  have hprod : ((n:ℝ)/(q:ℝ)^2)*(((p:ℝ)+q)/(p:ℝ)^2)*((p:ℝ)-q) ≤
      ((m:ℝ)+1)*(2/(p:ℝ))*((p:ℝ)-q) := by
    have hle : (0:ℝ) ≤ (p:ℝ)-q := by linarith
    gcongr
  have hdiff : phase n m p - phase n m q ≥ 2*((p:ℝ)-q)*((p:ℝ)-m-1)/p := by
    rw [he]
    have hcalc : 2*((p:ℝ)-q) - ((m:ℝ)+1)*(2/(p:ℝ))*((p:ℝ)-q) =
        2*((p:ℝ)-q)*((p:ℝ)-m-1)/p := by field_simp; ring
    linarith
  have ht : (3*((p:ℝ)-m)/p) ≤ 2*((p:ℝ)-q)*((p:ℝ)-m-1)/p := by
    apply div_le_div_of_nonneg_right _ hp0.le
    have ht' : 4*((p:ℝ)-m-1) ≤ 2*((p:ℝ)-q)*((p:ℝ)-m-1) := by
      apply mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  linarith

private theorem bad_bases_bound {n m L : ℕ} (hm : 0 < m)
    (hn : m^3 ≤ n) (hn' : n < (m+1)^3) :
    ((Finset.Icc (m+4) (m+L)).filter fun p =>
      p%2 = 1 ∧ (p.digits n).sum < p).card ≤ 3*L^2/m+4 := by
  let S := (Finset.Icc (m+4) (m+L)).filter fun p =>
    p%2 = 1 ∧ (p.digits n).sum < p
  change S.card ≤ _
  rw [← Finset.card_range (3*L^2/m+4)]
  apply Finset.card_le_card_of_injOn (phaseIndex n m) (t := Finset.range (3*L^2/m+4))
  · intro p hp
    obtain ⟨hpL, _⟩ := Finset.mem_filter.mp hp
    obtain ⟨hplo, hphi⟩ := Finset.mem_Icc.mp hpL
    exact Finset.mem_range.mpr (by
      have := phaseIndex_bound hm hn hn' (by omega) hphi
      omega)
  · intro q hq p hp he
    suffices hneq : ∀ a ∈ S, ∀ b ∈ S, a < b → phaseIndex n m a < phaseIndex n m b by
      rcases lt_trichotomy q p with hlt | heq | hgt
      · exact ((hneq q hq p hp hlt).ne he).elim
      · exact heq
      · exact ((hneq p hp q hq hgt).ne he.symm).elim
    intro a ha b hb hab
    obtain ⟨hal, hao, _⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbl, hbo, hbad⟩ := Finset.mem_filter.mp hb
    have hamin := (Finset.mem_Icc.mp hal).1
    have hbmin := (Finset.mem_Icc.mp hbl).1
    have hs := phase_separation hn' (show m+1 ≤ a by omega) hbmin (show a+2 ≤ b by omega)
    have hclose := phase_close_of_bad hn hn' (show m+1 ≤ b by omega) (show 1 < b by omega) hbad
    have hlo := phaseIndex_le hn (show m ≤ a by omega) (show 0 < a by omega)
    exact_mod_cast (show (phaseIndex n m a : ℝ) < phaseIndex n m b by linarith)

private def intervalPrimes (m L : ℕ) : Finset ℕ := (Finset.Icc (m+4) (m+L)).filter Nat.Prime

private theorem dividing_primes_bound {n m L : ℕ} (hn' : n < (m+1)^3) :
    ((intervalPrimes m L).filter fun p => p ∣ n+1).card ≤ 2 := by
  let D := (intervalPrimes m L).filter fun p => p ∣ n+1
  change D.card ≤ 2
  have hlower : (m+4)^D.card ≤ ∏ p ∈ D, p := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod'
    intro p hp
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
  have hdvd : (∏ p ∈ D, p) ∣ n+1 := by
    apply dvd_trans _ (Nat.prod_primeFactors_dvd (n+1))
    apply Finset.prod_dvd_prod_of_subset
    intro p hp
    obtain ⟨hprime, hpd⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(Finset.mem_filter.mp hprime).2, hpd, by omega⟩
  by_contra! hmore
  have ht : (m+4)^3 ≤ (m+4)^D.card := Nat.pow_le_pow_right (by omega) (by omega)
  have hle : (m+4)^3 ≤ n+1 := ht.trans (hlower.trans (Nat.le_of_dvd (by omega) hdvd))
  have hlt : (m+1)^3 < (m+4)^3 := Nat.pow_lt_pow_left (by omega) (by decide)
  omega

/-- A prime count in one interval above the cube root supplies a digit-sum witness. -/
theorem witness_of_interval {n m L : ℕ} (hm : 0 < m)
    (hn : m^3 ≤ n) (hn' : n < (m+1)^3)
    (hc : 3*L^2/m+6 < (intervalPrimes m L).card) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ n+1 ∧ p ≤ (p.digits n).sum := by
  classical
  let D := (intervalPrimes m L).filter fun p => p ∣ n+1
  let B := (Finset.Icc (m+4) (m+L)).filter fun p => p%2 = 1 ∧ (p.digits n).sum < p
  by_contra! hw
  have hsub : intervalPrimes m L ⊆ D ∪ B := by
    intro p hp
    obtain ⟨hI, hprime⟩ := Finset.mem_filter.mp hp
    by_cases hd : p ∣ n+1
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, hd⟩)
    · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hI, ?_, hw p hprime hd⟩)
      have hpl := (Finset.mem_Icc.mp hI).1
      exact hprime.eq_two_or_odd.resolve_left (by omega)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le D B)
  have hB := bad_bases_bound (L := L) hm hn hn'
  have hD := dividing_primes_bound (L := L) hn'
  change B.card ≤ _ at hB
  change D.card ≤ _ at hD
  omega

private def smallDivisors : ℕ :=
  24872285099749040599537371369701141279048012274214516507995965818329962629332420394596883556744271522710290763644754987759037347414192906763489676264754484656816179822802674593063420604260063599461054368745269239572484153094880589441368478540524298595183491412891701290475039370921694676144420940072183560827692604359928161050714924038629197492056031257037327034939648119083120698468535967497318922830655372447326977436359113786113401687082580840869232012463907114182706975087415237441445244499151599804566624539191571808442791315481653327782000259843536245728728465971203560476837821304546241611579610685540504357834666144352714321603519444818701950099118054464534854391428903526499389040514090322008441579570637426388876754358022214600847078887291908480019239531833665294097555109194041272676974506292297352044290048640000

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem dvd_smallDivisors (q : ℕ) (hq : 0 < q) (hbound : q ≤ 1900) :
    q ∣ smallDivisors := by
  have h : ∀ i : Fin 1901, 0 < i.val → i.val ∣ smallDivisors := by decide +kernel
  exact h ⟨q, by omega⟩ hq

private theorem prime_of_coprime_smallDivisors {p : ℕ} (hp : 2 ≤ p)
    (hbound : p < 1901^2) (hc : p.gcd smallDivisors = 1) : p.Prime := by
  by_contra h
  have hs := Nat.minFac_sq_le_self (by omega : 0 < p) h
  have hq : p.minFac ≤ 1900 := by
    by_contra! hq
    have hle : 1901^2 ≤ p.minFac^2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hprime := Nat.minFac_prime (show p ≠ 1 by omega)
  have hdiv : p.minFac ∣ p.gcd smallDivisors :=
    Nat.dvd_gcd (Nat.minFac_dvd _) (dvd_smallDivisors _ hprime.pos hq)
  rw [hc] at hdiv
  exact hprime.not_dvd_one hdiv

/-- The table stores the first prime as b+4 and packs the subsequent gaps in base 256.
A number below 1901² that is coprime to the common multiple of 1 through 1900 is prime. -/
private def primesFromGaps (b gaps : ℕ) : List ℕ :=
  (Nat.digits 256 gaps).scanl (·+·) (b+4)

private def blockGood (a b gaps : ℕ) : Bool :=
  let candidates := primesFromGaps b gaps
  let upper := candidates.getLastD 0
  decide (3*(upper-a)^2/a+6 < candidates.length) &&
    decide candidates.Nodup &&
    candidates.all (fun p => decide (b+4 ≤ p ∧ p ≤ upper ∧ p < 1901^2) &&
      p.gcd smallDivisors == 1)

private theorem blockGood_sound {a b gaps m : ℕ} (ha0 : 0 < a) (hlo : a ≤ m) (hhi : m ≤ b)
    (hc : blockGood a b gaps = true) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card := by
  let candidates := primesFromGaps b gaps
  let upper := candidates.getLastD 0
  let L := upper-a
  change (decide (3*L^2/a+6 < candidates.length) && decide candidates.Nodup &&
      candidates.all (fun p => decide (b+4 ≤ p ∧ p ≤ upper ∧ p < 1901^2) &&
        p.gcd smallDivisors == 1)) = true at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hcount, hdistinct⟩, hprimes⟩ := hc
  have hsub : candidates.toFinset ⊆ intervalPrimes m L := by
    intro p hp
    have hmem := List.mem_toFinset.mp hp
    obtain ⟨⟨hpl, hph, hbound⟩, hgcd⟩ := hprimes p hmem
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by dsimp [L]; omega⟩, ?_⟩
    exact prime_of_coprime_smallDivisors (by omega) hbound hgcd
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hdistinct] at hcard
  have hmon := Nat.div_le_div_left (a := 3*L^2) hlo ha0
  exact ⟨L, by omega⟩

private def checkBlocks (stop : ℕ) : ℕ → List (ℕ × ℕ) → Bool
  | a, [] => decide (stop < a)
  | a, (b,gaps)::rest => blockGood a b gaps && checkBlocks stop (b+1) rest

private theorem checkBlocks_sound {stop : ℕ} (blocks : List (ℕ × ℕ)) {a m : ℕ}
    (ha0 : 0 < a) (ha : a ≤ m) (hm : m ≤ stop) (hc : checkBlocks stop a blocks = true) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card := by
  induction blocks generalizing a with
  | nil =>
    have h : stop < a := of_decide_eq_true hc
    omega
  | cons bgp blocks ih =>
    obtain ⟨b,gaps⟩ := bgp
    change (blockGood a b gaps && checkBlocks stop (b+1) blocks) = true at hc
    simp only [Bool.and_eq_true] at hc
    by_cases he : m ≤ b
    · exact blockGood_sound ha0 ha he hc.1
    · exact ih (by omega) (by omega) hc.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk0 (m : ℕ) (ha : 10000 ≤ m) (hb : m ≤ 13747) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (10057, 2446592244089355902779910), (10099, 19037473364371468326408),
    (10135, 1134721837304322), (10173, 2436889113152224842877956),
    (10243, 317543747298443000986269648390), (10285, 433473706242212364),
    (10309, 149162612777231190536), (10333, 1240377149614246633180761606),
    (10353, 18926653283908792620556), (10387, 633524611686109226050133000),
    (10423, 724520996758094850), (10449, 576187277771268),
    (10473, 477230759033137131388678573066), (10509, 5348188411967226544674930063771959824),
    (10555, 1864220430109682861548770824), (10593, 435732077456262660),
    (10647, 7272555929357583019935238), (10683, 47556716721613633098244),
    (10705, 725657908960168962), (10735, 10507557684648149677967521392235022),
    (10777, 626299243250378947136850440), (10833, 28555705647758311818762),
    (10879, 794148235238054443599864267270), (10899, 111258631671134690310),
    (10933, 722273612371331586), (10975, 1861802468218961483960813064),
    (11023, 2437110473526878153083412), (11079, 1240405152208582069877736964),
    (11113, 288804329980300290), (11155, 4864185346874727945341442),
    (11193, 1871473985170920675763034640), (11247, 37853154575744548733958),
    (11275, 150316450937834504), (11307, 56779802793069198705670),
    (11349, 41043906932731614405944586931728), (11395, 7263111196956992471960588),
    (11439, 295581941818435310596), (11467, 2269417870329356),
    (11485, 587173837800962), (11499, 19258690741095170967568),
    (11515, 75229260707403011592), (11545, 41359581643118750797094248258562),
    (11583, 163410550408842093146735379462), (11613, 9740027809670096227332),
    (11677, 175593718359727372610556943687695238040072), (11739, 1859346911291851842410250786),
    (11785, 432912938131916300), (11859, 41358972259170594586857103299588),
    (11919, 184614377323581801988), (11965, 2521854527586525602253314),
    (12033, 7272481710605262421099012), (12093, 9519098118050408433156),
    (12153, 81765332723667268530232283496964), (12207, 74365136900876012560),
    (12247, 112269118024219757058), (12297, 82082857118523967528260479092246),
    (12369, 480328054985429918266623263236), (12447, 476002499549987540604067123206),
    (12507, 28445460332634933299718), (12573, 7282000090352966737593862),
    (12633, 1259738667872364501192279556), (12685, 41518661726535425779450291815944),
    (12735, 28371959900082857709060), (12795, 160318108680645908236647664650),
    (12885, 477235585107929003926846178820), (12949, 37182301282014464006),
    (12997, 1010501781043676162), (13059, 477235575588404763599663531550),
    (13117, 74221019522333414406), (13155, 721171892962461700),
    (13213, 1254884112025955249286810114), (13255, 37326975022097897480),
    (13305, 7310261365863307507142148), (13363, 7282000523259299108098062),
    (13407, 578156225172341766), (13447, 724529827277047302),
    (13519, 762915540626350409916860111684092072302939206455310), (13609, 202986271026885320375630591035398),
    (13677, 146932188473066502), (13747, 40886086455424795939298267628038)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk1 (m : ℕ) (ha : 13748 ≤ m) (hb : m ≤ 19537) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (13825, 7272482575272210076928514), (13873, 2258414098056194),
    (13897, 2242107540482), (13959, 317543775560005593813219417604),
    (14005, 73933921651916018178), (14047, 16953369902978991991164422),
    (14077, 74797475885651067906), (14103, 626327725603627974816695844),
    (14139, 1011643073945797638), (14169, 317553428188641158880622679044),
    (14239, 762938287388494605556179767917558818234409177448966), (14317, 635072930560968667941695259650),
    (14383, 434601796515007490), (14457, 623834094447572891972012562),
    (14529, 38911668154284770820), (14623, 31235388641751440404576529440703490),
    (14713, 37853296995477070678022), (14793, 1861783725754460258708097040),
    (14863, 19037762177471636572674), (14919, 31235864030116379310630441809611270),
    (14979, 10507084796407772011765327933080606), (15057, 12098814334099703502078988),
    (15117, 111116763902005872138), (15223, 203301331640329055836338495031302),
    (15303, 28408851138663577945606), (15369, 47371530404806871483908),
    (15423, 258548283530627515404), (15523, 1369167184103131148957803073946436241934),
    (15615, 19037329816497065954314), (15723, 1864182762000154349122355716),
    (15769, 1697671824147470), (15855, 162196807701768115386231161874),
    (15903, 185765053668595598854), (15987, 477230787034855534264772593162),
    (16053, 1141310283317764), (16123, 122804911607369614249145089524236),
    (16179, 1297606265878610436), (16213, 1704260505044486),
    (16297, 2679509609969171915967827515911048722), (16377, 1864182946178803942023235102),
    (16447, 1864201504757965642438809602), (16549, 1369115586287536437981649460322674017800),
    (16627, 19000295590869915013122), (16687, 160327855977101182514965513730),
    (16755, 5348431009841155927817422682489100292), (16819, 37759872558611300870),
    (16897, 28372250942992338522626), (16977, 111258053319429588486),
    (17017, 6622974050822), (17095, 623862428649289291982572040),
    (17155, 149159787058084319240), (17253, 20810071044705358570913902461583906),
    (17379, 10506765405497527217386358401401348), (17445, 866382203209516050),
    (17515, 4902001025280441391909908), (17565, 3951653648729604),
    (17653, 41047011369344613218046307994114), (17725, 2465445392430575313357320),
    (17823, 1859375171561350851145237002), (17917, 9555703362610591827458),
    (18037, 159701528473872934650903659522), (18115, 185337768005138122242),
    (18207, 9777640178370824504838), (18285, 37853731036531144263180),
    (18367, 28482062775690960572936), (18447, 9740026127442941051910),
    (18489, 3379967497080330), (18517, 1693376957255682),
    (18579, 122648916702607700612605420242436), (18667, 318786560783333440583029623816),
    (18727, 433478121602680332), (18783, 2436778871795343725822982),
    (18865, 34299070174184075838875904215674799014180686878), (18955, 475995217882664243254030370318),
    (19009, 432915128733533714), (19117, 8017110126283206086478196307118785042),
    (19203, 111259753164438897156), (19369, 8006725057806441105998708006812254726),
    (19453, 435729886888461830), (19537, 111116757279200119298)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk2 (m : ℕ) (ha : 19538 ≤ m) (hb : m ≤ 28383) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (19657, 2256615664466640718463182333636645010066798029702676), (19735, 111547425022909219340),
    (19837, 162184699627897513155339225602), (19957, 1259729075855349962225617410),
    (20085, 476621478940290241618153702924), (20139, 5073164032541188),
    (20245, 792905459311022040361764784140), (20319, 567373870925316),
    (20389, 73940663874430961670), (20473, 37328661707128046594),
    (20589, 2047021580186580164157258078423438330886), (20703, 9666527368304344695306),
    (20853, 22880913716786663519560563669636579242285729296), (20955, 37852864082582257668612),
    (21063, 319400647839281772953604590614), (21153, 111406109148555380230),
    (21273, 62429575539290292630103564801547782), (21463, 1499557815282521787525258336827917770178555696907790),
    (21553, 146932179950502914), (21643, 7310260933500219880639490),
    (21747, 12099035262680833456474630), (21835, 38112273681705880521218),
    (21973, 243866146021557742173673864168974), (22087, 9518956232672047927298),
    (22185, 1252485001984838415743591428), (22267, 1139128473355266),
    (22363, 633552798456879848088013826), (22465, 2437073579473659067761164),
    (22609, 81766561011226934553888607437318), (22705, 111262002748049458184),
    (22779, 111401610084379530244), (22957, 3413478303248546243518376016076571150850),
    (23035, 2823563073817602), (23127, 110825714395153698828),
    (23247, 162191934256452416721430252050), (23307, 576221503424010),
    (23469, 89378585135881027691474859060889849506958360), (23589, 7263112493973894079054854),
    (23737, 159703965030799999948827264002), (23853, 56779225195438817018892),
    (24019, 162576813313438799408508847918598), (24093, 1139128473355270),
    (24165, 579282185141355018), (24243, 477245284736853706030023187972),
    (24355, 19221653135509279867404), (24435, 111403303255010449924),
    (24505, 38001596042991494367752), (24607, 8037959812011260858612280725352482828),
    (24687, 47335213929375284595718), (24795, 1240405447500598047883398154),
    (24903, 47260991803744453919242), (25009, 7272556075720224402571794),
    (25113, 111545725160787281412), (25215, 9518675325043203246090),
    (25353, 160320507643101806850286421514), (25519, 524728774845809715052131400164813569262606),
    (25617, 185477942543741355532), (25713, 37332034974608918544),
    (25837, 7263221446758174832067078), (25935, 74796910779221280772),
    (26079, 122805516089242815228802570127376), (26179, 37614640275143396870),
    (26305, 1869037207173408703617565704), (26413, 56742764068266035251206),
    (26623, 2044383933310353162292592076072639924230), (26773, 202985649705090710321193907130886),
    (26877, 110825727546545013258), (27013, 2436963476028460756896782),
    (27069, 4523399494503940), (27187, 19352332069506013516795398),
    (27237, 2216304576012), (27357, 1859431951070259846274752006),
    (27445, 37614646923551184392), (27685, 5880439423952974009625076799741238895187713066498),
    (27789, 293864299636851718), (27913, 19148874967686911759874),
    (28027, 56706012432494582564372), (28147, 41359583985009293679883720987148),
    (28273, 3102273697382554729955329026), (28383, 295726059256906385926)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk3 (m : ℕ) (ha : 28384 ≤ m) (hb : m ≤ 41109) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (28543, 2474594258047622961695234), (28645, 578160674690171912),
    (28747, 369224816110848443906), (28855, 56963979747258052117512),
    (29005, 203300091339512645084677075502088), (29125, 185333827372711544322),
    (29283, 161553612237937348012986074634), (29385, 722273612304351754),
    (29523, 2480801006673228396249351684), (29629, 2446408497818338247185928),
    (29749, 7272666754495816700527110), (29829, 569572860890628),
    (30007, 10466834411533669158302037587398658), (30157, 631087834699085746016750600),
    (30249, 289925883580516870), (30385, 953228356287523456735797316610),
    (30489, 145256524297014276), (30633, 28408420484096828638726),
    (30799, 12098887829472286188767238), (31009, 34298900697552264346405463017540037561423367686),
    (31177, 7272481999381004997101058), (31315, 18926649926077188015618),
    (31473, 3102198174394717498259146756), (31623, 3716256897443456485115299344),
    (31719, 438540290216428036), (31843, 479094922425484053311742937602),
    (31999, 7282037124011271892636166), (32137, 16944220599373626279333890),
    (32295, 28408421612187034584580), (32475, 635687074249144125501676586508),
    (32565, 2816974829127172), (32703, 2436889112593681826841606),
    (32883, 477230777553953034026617274902), (33009, 148295111288600135178),
    (33115, 147864445769650668062), (33283, 7272481568717727584619522),
    (33517, 7996178047591777138822329828861936648), (33699, 162177483777833108278957180938),
    (33847, 1881107576046617177396610566), (33993, 62551112776147138844235855676181526),
    (34207, 41660862231397694647549795108783106), (34399, 31519340524118725649180969501591570),
    (34579, 477852137348570477838037942790), (34689, 288804355749450250),
    (34837, 12183817363136904398242818), (35049, 122013860715934854782232463936006),
    (35217, 1112912959467158656192396793862), (35415, 122011994106245709520638843686404),
    (35529, 433473740535891460), (35725, 31398121430730534437056681393655810),
    (35907, 623843613255749665872284172), (36057, 1269419592953146617751012870),
    (36213, 7282037127395568515681292), (36447, 1377121823774614204398612161993793210886),
    (36673, 10466199357965033288325436293908486), (36853, 14516665538738160587638286),
    (36993, 47703570667861325515270), (37167, 162576844736323778896023385671690),
    (37305, 184900353726667032580), (37503, 7263073873355315232900612),
    (37615, 332474332653182913038), (37777, 12127222173617257697775618),
    (37947, 4959052008509840328650655238), (38163, 21013054208849333943225365576418826),
    (38283, 1298164817450632204), (38553, 8826144684363514194701532034995792230686098851332),
    (38695, 146938759873692680), (38835, 37185672444794767884),
    (39099, 176271593565084006712866359729759644419588), (39289, 4344888914795885916387019784),
    (39439, 7310409226891803274643976), (39699, 134330555716399062576199552667022795653777926),
    (39835, 289928047976121858), (39967, 442867681615690466312),
    (40119, 74653925863161463300), (40339, 177643387929225244298270450271378169136648),
    (40467, 146943166443291660), (40695, 5327419223914079546846557800814616074),
    (40825, 1009945470774150668), (41109, 871808772280260826225516749990130606542340)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk4 (m : ℕ) (ha : 41110 ≤ m) (hb : m ≤ 58107) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (41217, 1695507227476998), (41463, 1369115342423262022524515137091770780684),
    (41605, 577593309510501890), (41845, 40883596087383100775836576386050),
    (42009, 56779799408841094070788), (42175, 221649735456366396930),
    (42387, 2436852363779282510808582), (42637, 122489227244760815700624756835842),
    (42783, 74222701800895022086), (42919, 723960271697479686),
    (43045, 148875508318535420930), (43197, 12098815197108579435679750),
    (43387, 42471880373709660467689611854342), (43573, 9740317161539349384194),
    (43717, 147862750322486281760), (43957, 479097311868984838607775991298),
    (44185, 951364192672381776803624387084), (44479, 22970467858277499417225691730103356341962933768),
    (44679, 2490406116065983389914762244), (44863, 9690407715508000232179724),
    (45049, 640834613785342812606566408), (45255, 2436889400263272252838404),
    (45477, 52289164249842380155579722407216650), (45663, 14526110418090713236243462),
    (45813, 435173542594871812), (46045, 41362678844661621832976591227394),
    (46225, 14554665687425826316490760), (46435, 14526147599219915753784834),
    (46615, 56742617696897178273294), (46803, 56853299856734892983812),
    (47037, 159701556512634572629868676618), (47275, 160335043013639018168359061000),
    (47487, 14535813691425663928894470), (47707, 3097315285063264554768925698),
    (47899, 19037475611764713326088), (48075, 4864186205947308999840268),
    (48333, 5348106807590887017409796756881935364), (48477, 145810652622357510),
    (48747, 41364530909571099579051904730118), (48969, 3728393451791547555379937808),
    (49153, 221650850335588483596), (49363, 4873814543329482432976386),
    (49599, 121856647176278665117696109448714), (49779, 185334396876785189380),
    (50017, 2488007227102079582001302018), (50257, 479706686076824452540448770562),
    (50493, 1859346912875992977079405062), (50737, 18692310683520549303767990261766295052),
    (50947, 3097324692910594867509464070), (51127, 73932243822741160962),
    (51403, 475995255550626272298701817350), (51595, 37853155138703092483592),
    (51813, 7291446115856214376710666), (52047, 159711237365076814025661221382),
    (52245, 7263738100265918820517380), (52485, 1247630446567970981970053644),
    (52663, 258688462449929490950), (52879, 9699814976840430935739398),
    (53085, 9630065680397611304964), (53265, 19221946993177319834122),
    (53545, 82240694464013901234413331943938), (53779, 626242576149060487605523976),
    (53983, 3738046007219424998250383366), (54283, 2689691378376443051582137039671792134),
    (54499, 9519529887470510539790), (54675, 56816405799134873256990),
    (54937, 122646440775637506425395899927048), (55203, 81289335182936868706200913576966),
    (55497, 2047021944791498838256930826477321851402), (55759, 1864201503746883336872003096),
    (55983, 3716266414814971809984022026), (56167, 9519531565419743285768),
    (56413, 2474704649712176537667086), (56655, 1881135910963266832535521284),
    (56889, 28445603321906056006660), (57127, 2503038850861177109873672),
    (57325, 66408856825977737711618), (57597, 122013853424711974491502032716836),
    (57783, 111115072887415505412), (58107, 8006563273279645329819079878662951442)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk5 (m : ℕ) (ha : 58108 ≤ m) (hb : m ≤ 79345) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (58359, 2474704939072799136940548), (58569, 7282037988728839965120006),
    (58885, 10628461729635047417361225665086472), (59137, 1245250300215500578956511752),
    (59347, 185045596979413516806), (59607, 2483237562878039959210951686),
    (59967, 2957525701401764055361636432160399445843411603978), (60205, 794145855312635062195463128584),
    (60489, 10587895665243299457426155161521156), (60685, 184612703832591831054),
    (60895, 148296232790292433922), (61117, 477871489717528425231943339016),
    (61327, 37891198175036397848066), (61605, 4959051602393809886267051524),
    (61923, 20891522533023106221359022522241030), (62125, 111401623244092212738),
    (62463, 524728774886373922580896095112035393995782), (62649, 56816695709556336236550),
    (62893, 2436778719820803014529542), (63295, 8792292156549620434224824138402809502711987569164),
    (63583, 1247658707701035158921677314), (63789, 110972074786107556870),
    (63993, 85188074093211864663562), (64213, 7291629146642082196490246),
    (64479, 477849728831699813456344386054), (64777, 52044827082171355545580595238275586),
    (65085, 318771997226461192875978392074), (65319, 16943962057300180509923844),
    (65629, 161553611978960672805129421838), (65805, 1013318729465201682),
    (66033, 132263447186171988542980), (66333, 81607505115624098522796160451590),
    (66529, 222516108854759001096), (66817, 159708810032531693592448731668),
    (67125, 951361765744800352421259510282), (67395, 9690739180996901647024650),
    (67705, 952609395785824793186500348430), (67927, 111260309508766041602),
    (68137, 104114001706026114092550), (68433, 3111803578500204103249036294),
    (68679, 19221941368084287458308), (68875, 722834354476550658),
    (69139, 9699963415473085433512454), (69423, 2436778721483238893815812),
    (69733, 365244940984745079537660208485890), (70107, 10665302741991491813601427183311651846),
    (70377, 1871426725762712811558280716), (70567, 866382229180647938),
    (70897, 160325333975719680596716422668), (71245, 122171685953314308698780473623560),
    (71449, 37761020499887260178), (71773, 203776693371378388235788044341772),
    (72027, 28371813537467278427148), (72219, 722267058017272324),
    (72457, 37853736096432283976198), (72657, 579845100801491466),
    (72889, 110972079149760644616), (73177, 52044824618343051385330644671672328),
    (73513, 123597173927514965771041465566726), (73815, 244183677736045743081130729543684),
    (74139, 3725937747435167894890220038), (74359, 74369636102758859790),
    (74683, 1428594904260772373607475447820), (74853, 1695464345044996),
    (75145, 14526110414697629042738700), (75499, 41048861044811587147705679743496),
    (75727, 94670421101057210193932), (75963, 149592132596542080012),
    (76203, 66225397061250429227526), (76459, 9519819234984902134280),
    (76729, 12117630014196154511524884), (76945, 111546851077975179788),
    (77209, 56853010478511484568088), (77485, 28445025183316155044354),
    (77695, 1009945445004608012), (78037, 51964486006688366087975409649191432),
    (78423, 3410830232801431488340896310623519638026), (78777, 162576820633070389537404317205510),
    (79083, 2483162373948628111017248784), (79345, 28408853944557323946504)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk6 (m : ℕ) (ha : 79346 ≤ m) (hb : m ≤ 104647) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (79617, 9518665202965263025158), (79807, 1128150570763266),
    (80143, 1859375355741691449812321282), (80523, 2679347035639095597038063983637697546),
    (80773, 295295409088270566402), (81009, 145243330090107396),
    (81279, 9666527372736952010250), (81607, 1240414781116824117607664136),
    (81895, 9519531569723300516354), (82179, 94521551235458588869638),
    (82459, 85041077705292588515846), (82723, 9666527935712339303426),
    (82993, 19111261462177126417926), (83217, 288804381518857222),
    (83533, 3716323046458883132400731156), (83809, 7310408362781208501684756),
    (84133, 2487997708583254686012806150), (84397, 74221580281820352006),
    (84645, 221796656572581938692), (84987, 952606959007254198170360876050),
    (85195, 865823659892804610), (85545, 160335014863469591021835519510),
    (85813, 28595049080908947786242), (86167, 322490662270965603677728801800),
    (86437, 28372679915289352472588), (86673, 74798612797384164364),
    (86923, 38193915777046546946), (87219, 16953370470986699201839644),
    (87505, 37183413979359610370), (87873, 81291206533805873918876956755460),
    (88165, 161558523352368595318443090440), (88639, 11507360116129007330676187542346310342880265736),
    (88989, 1252456815649832770342356484), (89389, 31275635936620556304951630696287750),
    (89755, 41047637630624602776694314765320), (90013, 295293155089567974402),
    (90393, 81289347243785347934210255749636), (90627, 406262423835799979530),
    (90897, 56816838153460968195078), (91135, 435182321507895810),
    (91365, 723969050543523844), (91687, 3097286951443057907640698892),
    (91939, 443155922978133509640), (92343, 952609377006318189467390051334),
    (92623, 184614372925669507596), (93043, 15992478578211314319606706128314041862),
    (93373, 1861755281159397224297011206), (93847, 177646025656440070789414915868865268420628),
    (94197, 951983200471824403038726654982), (94527, 9718741913844441336250890),
    (94785, 442867666265209049604), (95185, 635689492137245060241665166338),
    (95503, 4901928245991186117428244), (95853, 3716285525635633203496092684),
    (96175, 9728185930735640818487810), (96447, 185909725149358720006),
    (96733, 37616326908599339522), (96969, 1300981749060733446),
    (97363, 43418278308301258467566831404034), (97767, 81766561029931496199916192139782),
    (98203, 693898999973409272011435552193718388742), (98463, 38193355034840532486),
    (98845, 3097343545331037321723904530), (99085, 721143297171129870),
    (99345, 149161475882376102930), (99703, 1866657135472049370845021186),
    (100045, 479706629519970138019732786184), (100443, 792912750607545763902088153612),
    (100737, 28666676024812500030982), (101085, 12145964210280813014680594),
    (101425, 2437000080729879207350804), (101829, 284434686283498548039362633269764),
    (102177, 7263184695694157980763658), (102493, 113411160160640565511170),
    (102825, 4968789048725754644846613004), (103063, 1303798697851095554),
    (103545, 1377111601755843942199881002160442705924), (103947, 3728355672859682364901688332),
    (104283, 7300816346910204476132362), (104647, 7282000086977500265320968)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk7 (m : ℕ) (ha : 104648 ≤ m) (hb : m ≤ 134335) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (104907, 369804089422284460038), (105315, 1247658780621627137494222852),
    (105649, 2446371604321386246047246), (105925, 111837333219445705230),
    (106257, 47261424140495274247180), (106657, 623843723651357033651504642),
    (107017, 4337710880991429525839811596), (107265, 369368361803374790148),
    (107599, 2436999793629878319057926), (107919, 47260848818854331813380),
    (108183, 1011627689272541700), (108493, 75816409759835604517890),
    (108877, 12098777726590132521665538), (109129, 151998729598403078),
    (109513, 631116094244068198889820674), (109825, 148298480183503096322),
    (110217, 1589517475887390044572235990028), (110563, 56780088760684511757314),
    (110913, 56817269918439972274692), (111223, 19148157230668409608194),
    (111589, 631173168614910325687061510), (112093, 1363819159698409726136863910549156136966),
    (112455, 633505574646233937243149334), (112905, 81289339999675454800501707769348),
    (113145, 1128116210763268), (113433, 47555857105822196043280),
    (113727, 185336076922129615378), (114139, 636956455840645363995918074894),
    (114589, 161560893794579626844014510598), (114993, 476614254052187051270030625796),
    (115299, 38192220304312502790), (115729, 1254912261608223378122344968),
    (116095, 12098925012888490206430722), (116419, 9888610010050064549390),
    (116899, 21053623970079459491901613554273288), (117219, 9630072429191459635728),
    (117667, 478471107442140875161578374658), (117973, 74221580273833871874),
    (118339, 4949151619776955740850194), (118795, 82240694445087546318447256015362),
    (119065, 150314243391095822), (119547, 10587896898338485878676059586954758),
    (119977, 477240401884847484342981757442), (120289, 56742619381383553618950),
    (120673, 14526258276880577557824012), (120993, 73937303732301989380),
    (121317, 184614377280699500038), (121879, 176271593484114057802924542946191606551558),
    (122199, 111113949186632581636), (122497, 38195595890910168578),
    (122815, 75084582586251871752), (123285, 52045140902360869583487999092196370),
    (123649, 18926649915022278002184), (124117, 41838057491188642353146621200898),
    (124455, 28666387801110592882188), (124749, 435162530298595846),
    (125097, 19150172569554307515910), (125617, 31276586664918061804388572905737222),
    (126007, 12174483596611984445146626), (126429, 1886009392021225328026586634),
    (126709, 1442284412162412038), (127185, 405966964107780835343733161593362),
    (127639, 3102113209412076764140013574), (128107, 365246790669583722271361594033666),
    (128445, 37619700210239669772), (128919, 953842500084075224535833117200),
    (129435, 122012001369208463862442756670980), (129889, 122333242021329379444160880316424),
    (130345, 637551247565112021160902657038), (130635, 434041114337609220),
    (131005, 17000556960847873445071874), (131409, 7272592678741528654644754),
    (131835, 3721083228624681916023311370), (132229, 19352554006893485737248264),
    (132607, 37964265699108786275336), (133009, 4873593325961640757954068),
    (133317, 259120242976682150406), (133653, 184901477401848054796),
    (134043, 12127482445068528071607814), (134335, 151998712284318722)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk8 (m : ℕ) (ha : 134336 ≤ m) (hb : m ≤ 169309) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (134773, 159704040625123179622152671756), (135177, 2436852798957128562508812),
    (135585, 9630210906066694309380), (136053, 122491076929821826515913137455626),
    (136477, 16981740842791725865505282), (136885, 7263074015790458030403080),
    (137337, 1245307189687112825731024396), (137773, 635701563095261170815022402574),
    (138153, 19000298968578292584454), (138543, 57001305572164680156172),
    (138865, 149163166982664881678), (139263, 19001588680307230773766),
    (139693, 5585303916693224279308502534), (140139, 4347344582691127374551189520),
    (140589, 1859347058581519060772980746), (141153, 8068951648310283478878224546588135940),
    (141597, 2446260635048216096933388), (142003, 14563817290079236830792716),
    (142525, 792907895978916689868239406600), (142893, 56705724760704665256966),
    (143457, 20811024248864127681597506511571462), (143775, 145247719513523724),
    (144157, 28445316795893085766658), (144493, 74221019531158101006),
    (144879, 47334783279258019693060), (145413, 284271278226756314924773634738694),
    (145945, 81289973457620170980256481674254), (146293, 37761007322961283586),
    (146797, 244026459313131435681095678299142), (147289, 794762369518676986998733409286),
    (147723, 19399592626696923221459980), (148119, 28371530938789382064144),
    (148605, 1585803655732067893281521272338), (149017, 9666816733367772644870),
    (149485, 2465223599160438785705474), (149833, 184614377358008653314),
    (150189, 148727441468086945284), (150529, 110973763584395053074),
    (150925, 66187066357499749073438), (151467, 365562465351451328178837173306886),
    (151813, 110825720975311635992), (152199, 66187355731367926957578),
    (152773, 51964966327442460235602371460335622), (153255, 3721121008417875894137651722),
    (153619, 37889902262096107145234), (154023, 66298031116049249996304),
    (154483, 626327504238756301970475014), (154837, 74227781527366931976),
    (155265, 4845222241448804424615958), (155649, 37616322502164219396),
    (156055, 28556137421593975589378), (156615, 122332001634661532390773691648004),
    (157203, 243548611983519010115632383526404), (157729, 244189248343403819266695193036806),
    (158227, 635065686524577668812747442690), (158559, 289934645112866308),
    (159069, 794141009906221719378268787206), (159667, 10466359042558915329375652667066882),
    (160075, 66224104548034414904834), (160587, 1871445724470204244747751436),
    (160993, 28630213189007070726156), (161517, 162189544776768566302551573510),
    (161919, 28408566844487514196504), (162435, 1111056134335886271300894721548),
    (162817, 221943588709280122370), (163305, 4959023268200537795787884044),
    (163749, 12098814043635111367805458), (164169, 75595479481145629476874),
    (164577, 28593181212946283498502), (164983, 28409429842368097681932),
    (165445, 2465223311495340359026184), (165795, 258544358351325365772),
    (166293, 2483152635798267522846818820), (166777, 7291407781770391632482306),
    (167307, 159703964993473610030225427462), (167773, 1871455022060445821187921410),
    (168189, 56742762931353967136260), (168595, 28630789113214812295170),
    (168973, 37185692201577090062), (169309, 290501984556286470)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk9 (m : ℕ) (ha : 169310 ≤ m) (hb : m ≤ 209617) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (169813, 1254893410043491292859992070), (170295, 4864258984099660794564124),
    (170737, 66187500957045532789256), (171157, 37963548518520509826050),
    (171633, 16953407079615564395973636), (172143, 4975957600185424169109554182),
    (172585, 47334923453796320544264), (172969, 111693776652029265416),
    (173535, 82081007461909711856888212882948), (174057, 3723519970450981569054508038),
    (174565, 1873863429254944122398051330), (174985, 103929677256861942418434),
    (175399, 19258836556050980541960), (175957, 1429204212208054756694022688770),
    (176457, 2474631441443992753411590), (176883, 28446757932268979880972),
    (177375, 5578012213916666749382302212), (177879, 16943962633189169587028484),
    (178477, 121854183338049443289737020047878), (178885, 221793848445385311752),
    (179379, 4873667257605095688506890), (179893, 14526036485294970152289282),
    (180285, 148298480200850998290), (180727, 14621111579009611812176402),
    (181197, 2436999793071266583675402), (181707, 2465333847274961618076678),
    (182103, 37616335721804991492), (182557, 56706158803871827626002),
    (183255, 2730265539207465916658563597760880579588), (183867, 93583362258802321839598227135529990),
    (184255, 258546038379456627212), (184645, 111115633595396526594),
    (185095, 28445601635263842748440), (185647, 1240405373709681112027104282),
    (186145, 7291518465632264823899144), (186685, 1881135836170861886727915020),
    (187119, 74221597856826130948), (187593, 12146149254169151190336034),
    (188257, 13323678715583468492409636157523625996), (188763, 7263074449253092114959372),
    (189349, 476635938863930737388667277320), (189847, 14516887766049239487088130),
    (190309, 28555853125270393850376), (190807, 9690444317959903557191180),
    (191455, 41361438467953576557844114048514), (191995, 2487997784386150348927010312),
    (192525, 2465333847279368153729034), (192945, 332331325798496995852),
    (193369, 74221584782945812998), (193795, 73933908483346530828),
    (194079, 2276015041152516), (194643, 6196982159768442132820133382),
    (195225, 478466299888888850105321786380), (195705, 19001590371364670538262),
    (196155, 28780237662735365964298), (196657, 2503076464364513944539650),
    (197265, 792912741199712480932857251332), (197887, 284283647917852711826650070519810),
    (198393, 14563963133543435129979916), (198819, 39778054712557044228),
    (199395, 631068798233408482799126532), (199927, 6818360623207508445009157122),
    (200347, 112843900913222944262), (200887, 6194620939487193956480320520),
    (201399, 7310260497783570047965194), (201889, 28556137986759863043086),
    (202305, 184901497158830918674), (202903, 1269514820732268487043046312462),
    (203305, 146932205619512834), (203905, 318776851635168794501990451714),
    (204423, 4864075957821868293096964), (205027, 478473515812441885333253261826),
    (205549, 2436853084359569431207430), (206179, 160325381051810004748487493128),
    (206775, 476002499590051558499664794628), (207459, 243707706574119736435247071496710),
    (207937, 132337087252277243020806), (208453, 28371813530870208660482),
    (209143, 10466201219710684668016372450987532), (209617, 9629636712524648288258)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk10 (m : ℕ) (ha : 209618 ≤ m) (hb : m ≤ 256489) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (210123, 75595049389537389447172), (210715, 951992871914982067740983298060),
    (211173, 184614372891376879114), (211653, 28592744942125645431300),
    (212127, 19112124464489946289162), (212787, 122330147161343709492076008315402),
    (213277, 103929680073758958813702), (213915, 795997882260724933564809088522),
    (214459, 2503039568626757211917318), (215059, 244194202530784120782712450845198),
    (215443, 1009938873839125004), (216033, 480330482318406810267454540312),
    (216649, 318772063044442928603316359688), (217305, 953854570452805450309689017860),
    (217683, 1731640679732610564), (218353, 365243693401854650121123359492102),
    (218959, 1871464613937831144422638086), (219643, 81289342436157872642263789739010),
    (220275, 319410309837710997360703048204), (220869, 7263221877401643553260036),
    (221449, 1873920207618817327628683784), (222003, 4845775635337727132961796),
    (222507, 14526442458903583734892048), (223213, 122490462766986075352770426964482),
    (223743, 7263073870545101185483782), (224235, 113521841183643553630732),
    (224859, 1270148260193639827929733663750), (225423, 2436999793055890499967492),
    (225937, 66224246954504347190786), (226543, 1866609910799522648873370626),
    (227149, 3102188693489404692482623494), (227605, 112267994314980855810),
    (228195, 6194564272101544023156328452), (228825, 3097315432060732237278479884),
    (229515, 41041443104242697921973568279050), (230209, 41520511364039576320887151265288),
    (230763, 12098925444660118122004996), (231285, 56816692903542399305220),
    (231805, 38074515511200463454732), (232359, 2446407635911130552602116),
    (232815, 111404987672464594948), (233289, 258544342906588895748),
    (234063, 10665059036770535403093817821116630544), (234723, 321272046118291626582671231494),
    (235437, 31357720019561157072757402253009926), (236013, 4344945841161001660962185220),
    (236677, 1902721103787975455224292049426), (237139, 296163473535378130440),
    (237669, 19148586194152116585994), (238153, 111402735915634263042),
    (238825, 476628685641195739015080051720), (239485, 955082867567884341240624712724),
    (240013, 19037909094232486052376), (240697, 122648931219493881372682456927238),
    (241225, 28482496825480863679508), (241863, 3109414024741725364751303686),
    (242395, 37853587475436867552782), (243097, 122175404609615345167998059153928),
    (243517, 145247788366956038), (244287, 41619983591963136092300523872584710),
    (244809, 19037905714299617281048), (245467, 159723289249160643004421637122),
    (246115, 1866609984587618280706017794), (246709, 7263111053389378334099474),
    (247335, 3728355784120539447436907524), (247987, 3721111562821325161161163778),
    (248529, 28556425649762346862084), (249103, 4892483224792983320790036),
    (249723, 1240377149762287120616918026), (250669, 23015764893817813013241876370456574216548779528),
    (251173, 37614644638595288066), (251805, 6825623585964687005766517270),
    (252379, 33935036804528560774056456), (252873, 222659656677721507332),
    (253527, 623900244183617192157906438), (254137, 3097371992084457195016687110),
    (254727, 2437184693968048813901322), (255409, 2220252751866834686243561674758),
    (255957, 38074226700402431361546), (256489, 28593174464161360908806)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk11 (m : ℕ) (ha : 256490 ≤ m) (hb : m ≤ 307519) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (257167, 1110439497276401171829624802310), (257857, 317539005970438288128977536002),
    (258517, 2483152560143429896504085510), (259147, 12117630014180778527949318),
    (259635, 184905422441112276484), (260313, 477859466203237079512960731660),
    (260979, 3721120934488460058321226756), (261525, 28556859121217789888028),
    (262075, 9519098098259299796504), (262623, 47482785076054067381776),
    (263179, 18927085075370296740360), (263859, 1240405262600242225507729924),
    (264483, 1864220614434132163026223656), (265087, 17038409384703583033104386),
    (265699, 7348114660015456131613190), (266287, 7301148384910429877699586),
    (266917, 21789183853451104643581446), (267553, 4864186204803808383863820),
    (268129, 14526258715968347187581460), (268773, 21770441816220124318138884),
    (269347, 47261280603641557026330), (270093, 41358965034172533753115456965144),
    (270655, 9666963663331518974984), (271347, 161558485498502466312134198790),
    (272167, 62672805376840395609984545042334728), (272875, 161558438311732236243740135432),
    (273499, 3097324839903046603811193870), (274119, 16972406647866298230376464),
    (274807, 6211479861904514646559296518), (275443, 7310409083339659605836802),
    (275983, 37182285949014640652), (276483, 37332593620972078092),
    (277159, 1871426836012520505424087046), (277783, 7281926449187375725937666),
    (278455, 5573167065906931343252654612), (279105, 3104597210648842661081252362),
    (279609, 38193361623185625606), (280179, 113411018857994676341764),
    (280879, 3718684303629720562157489166), (281527, 4845371390546341575920136),
    (282235, 160320621532863990313812495362), (282823, 18926652725399667346950),
    (283497, 6811116734239032817485219850), (284145, 7272481572667199221532164),
    (284703, 184612684041382135312), (285447, 792905497090241588328619443718),
    (285975, 37759894557097725444), (286669, 3721111636322327268883302926),
    (287253, 28482206910635852302860), (287779, 74221013028343385094),
    (288457, 1864220430685013410421935622), (289059, 47261279473335080853508),
    (289885, 10506764784071987684635769895266312), (290607, 1885952650124680669905945606),
    (291327, 1905813535962923297855800740870), (291967, 12098888266884417412006920),
    (292623, 12117629723707390065778180), (293077, 149188403580503558),
    (293599, 369228187247657616398), (294265, 7281964201165337332550664),
    (294747, 289925848986551302), (295315, 9555705044957972011022),
    (295857, 112699768218725909002), (296665, 486937541696707139868984275764238),
    (297355, 1871426799265975498175284748), (297927, 28556282678040726867478),
    (298585, 2436851933135745238042124), (299307, 638350686774656355780529158),
    (299887, 66298032818110464525836), (300657, 1427354565111021973088162678278),
    (301359, 1240433596653915930334991890), (301897, 37766630165296580102),
    (302559, 19428185511230845835675140), (303289, 3097296358276532980412712966),
    (304005, 8675299126725593062854887428), (304719, 4973549488714159293419227654),
    (305407, 9699814688618807961060866), (306087, 2512223449502254535213976606),
    (306817, 1873863539503063000293704198), (307519, 3721083192596443449501550598)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk12 (m : ℕ) (ha : 307520 ≤ m) (hb : m ≤ 363525) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (308077, 74364571794849269772), (308895, 122647054919029533063754461348888),
    (309489, 75668979933420596630026), (310023, 37615774945173833232),
    (310693, 14545074965759164431075854), (311289, 66519827205273530139654),
    (312003, 4340100472215942911188141584), (312669, 7329371471010852314153476),
    (313293, 28483360379680070698500), (313929, 28408131121206520187920),
    (314545, 47482213110010809551892), (315417, 52085550348003984848136299314547728),
    (316027, 28777788276284324709378), (316755, 5573176475320995365253416970),
    (317583, 243867388844450911196181126578692), (318277, 33859553159554958359134726),
    (319023, 1240405483819314292892370436), (319635, 66187069741770668639778),
    (320233, 47446037380923664768002), (320839, 56706157112857740053000),
    (321607, 477857001312263672062098014726), (322509, 10466834426021889815969879594763270),
    (323335, 40889162019452655091945816330754), (324063, 6211508233286821462621556742),
    (324927, 324994553730643305086169561434122), (325687, 623843797146177695860392962),
    (326493, 476002471326900886079073821190), (327243, 1245222149908702665827552260),
    (327819, 148295109080987075076), (328575, 2539041711685689286760234484234),
    (329205, 47260849938122641639960), (329953, 1866609910657648308041811980),
    (330583, 28409285173009214866452), (331273, 26606145527024256616370694),
    (331905, 9629351283704157573132), (332463, 37339348994676228612),
    (333205, 1245231816722619007499503122), (333919, 3723520080700224165349821446),
    (334689, 1861774207952272869694902790), (335413, 3116667579811400873844937740),
    (336109, 4845333348642488200992264), (336757, 132263448872797323133446),
    (337323, 296164595020226495500), (338157, 159708838402759385595968750598),
    (338989, 203775465074558460071357630257158), (339579, 110972079175396756486),
    (340317, 623891095318545433358107152), (340905, 407125973670950340100),
    (341553, 56779944645513615905292), (342277, 7263221877401643721691138),
    (343189, 20891992326413460469314780042236934), (344157, 31194823203602340071409076188349446),
    (344869, 21789072887577633105118734), (345703, 477235613551801817684540261396),
    (346389, 28445025170130539250180), (347125, 9690554710743631188331010),
    (347929, 1869037169988299294809130514), (348555, 47556140832710321768452),
    (349287, 7263110622741451502651916), (349903, 74798603966863640070),
    (350695, 4340100436044134622245292044), (351343, 94632809286570203283980),
    (352297, 10587578131262186799933590046380552), (353065, 645594944099303215435223564),
    (353773, 7310407936623704204250630), (354367, 147867271548725756930),
    (354975, 184613249250421771780), (355503, 867514726022775814),
    (356089, 38911668162942077960), (356865, 3104540542534220839380977170),
    (357547, 28372391115357453419528), (358219, 56742617690248537050630),
    (358843, 37182305671538147852), (359535, 7329261226263077202299914),
    (360193, 66187064673065316386330), (360943, 24225777818117522026005506),
    (361765, 794141066463945276876763955730), (362373, 184903166243218787332),
    (362979, 110827961754172136964), (363525, 290488798906288132)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk13 (m : ℕ) (ha : 363526 ≤ m) (hb : m ≤ 424543) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (364299, 3102132320381950613217085450), (365059, 3740445079208491633813361670),
    (365695, 9962108193001618145840), (366429, 31451072470262356846707204),
    (367177, 4892409726042546362518536), (368025, 319403094024832238549023722514),
    (368685, 9629346221638388550684), (369249, 149162617183969084938),
    (369943, 56890192764365842809356), (370605, 141782253111137987724804),
    (371299, 9520251026343730088456), (372259, 41621090931756126351243185228218886),
    (373123, 163410522074783348434184046104), (373933, 1859375503890970130151901190),
    (374635, 28556569760535162129410), (375447, 1861774465773792288444385798),
    (376035, 111690990403833695754), (376797, 7263664167479040214041606),
    (377473, 85039782357466979243534), (378145, 56706013580419081178114),
    (378897, 4845333922847034088098322), (379645, 29033147328339967426167822),
    (380263, 73935597324648845826), (380925, 47556285517342375282198),
    (381655, 2559596999969446818355214), (382537, 162177455555612275154602558472),
    (383515, 10507716143419291124718217489417730), (384199, 9629347356214095647768),
    (385009, 631069056200153656129096718), (385807, 1252541707424757395872943622),
    (386617, 4961450565287125140373900296), (387147, 1730510399025186826),
    (388063, 487095366981309976567505310323214), (388809, 4845664665506056785759754),
    (389509, 56853010478554434110478), (390355, 4347316358306877579098850824),
    (390987, 110970392541839624722), (391675, 151189661927677172515340),
    (392247, 148621029709971978), (393079, 3718684524560555725275137550),
    (393843, 17000556957494379924292614), (394723, 1903963879197781852546245460994),
    (395403, 94522422684194031010326), (396153, 29061665279177293328025616),
    (396915, 12155667487015479431005708), (397669, 43540256154363817455258126),
    (398437, 9699816709600327202244626), (399133, 9666533013214188012044),
    (399937, 1878680464859628574028864012), (400639, 66408425604182846080520),
    (401307, 28408998068627257952266), (402259, 405967592702167260539285076973070),
    (402943, 9519098098379425196546), (403813, 796002784409177786396768862732),
    (404457, 110825720949340898838), (405175, 38074513804801266551828),
    (405943, 7395411392931123687852546), (406509, 145254290914545156),
    (407229, 19001013343307451205648), (408133, 637551266269679283381779039264),
    (408909, 7282148096653362547266570), (409819, 636949202285150661348731128328),
    (410647, 1885971539592314132525747208), (411553, 320657921504913102051419358726),
    (412189, 221654793287196871176), (413065, 2495232558931993503381981698),
    (413977, 160318137015701606513403626528), (414639, 37183414004927830026),
    (415563, 321250313861813786474692483594), (416385, 17000557817653312893355524),
    (417115, 66334781617098968532488), (417895, 21770294968470792443398688),
    (418783, 3718684377128479674883376646), (419533, 28408131690796391990292),
    (420303, 28482063343013056349190), (421089, 21798518481848048019444234),
    (422053, 319407882578089283621302568454), (422857, 50793996115933316462019078),
    (423703, 7451875605116745992214285830), (424543, 1866638246159213925709515266)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk14 (m : ℕ) (ha : 424544 ≤ m) (hb : m ≤ 490833) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (425269, 66666824699309925728774), (425973, 56706157113020479832586),
    (426727, 56816406909555851919878), (427413, 369368361760255771140),
    (428143, 9777064326687866883074), (428793, 480339308395993630212),
    (429463, 332620671053736841730), (430273, 6197029643847733481193736706),
    (431137, 631087871590887268503782918), (432003, 638426612708574848920979472),
    (432979, 365564319853029564139699353554438), (433635, 112127810997464467980),
    (434379, 37963549618014858117636), (435127, 9998425209453089915912),
    (435853, 113375421280682848556546), (436689, 3725966192757012582161844760),
    (437463, 19000581004314424115716), (438207, 56927087385001782151692),
    (438865, 111260307395642657288), (439689, 14535629079306857524104196),
    (440497, 2465113351037179789443590), (441165, 111113955852253661194),
    (442135, 477859409608917297675943412744), (442969, 4845443309643730205804550),
    (443863, 9299067255616345123454321666), (444807, 642500580204089757197346017286),
    (445737, 635689548842540853013134841350), (446385, 479906969411656876554),
    (447129, 66334781623696137528324), (447813, 148296237248636126214),
    (448737, 318771997005099709914879105052), (449559, 4864185778648512002916868),
    (450387, 12117703221336265135229452), (451273, 4345002509698979414019282434),
    (452155, 1254912778261185850043009538), (453115, 637551247453714932354404189198),
    (453945, 2521854529260042227945484), (454843, 1240471449802279442475518466),
    (455593, 47482208063295623529474), (456519, 3097287208688666415161281030),
    (457359, 12212261808461933934546436), (458005, 77391551460945693714),
    (458955, 1859356429669930462473488388), (460035, 41742311277694731841201080313187340),
    (460903, 4864074804335146125362694), (461565, 186200776915229610508),
    (462543, 477852155980503694150773902346), (463243, 37328655084389010434),
    (464077, 4949078985715542468992520), (464937, 26624739414396023454958090),
    (465883, 794148254201601226530563819526), (466549, 37763263520821347848),
    (467413, 4864149023078662275728910), (468109, 147866141233693068296),
    (468817, 110969262226706795028), (469713, 2497697596767228492761143302),
    (470575, 7300815769871143382680590), (471483, 631125466058691560466023952),
    (472249, 94742625066489731877896), (473097, 19352332071194846363523088),
    (473883, 47555853725914794560524), (474775, 2483162042062615568827160072),
    (475689, 4968704230452925093605021700), (476599, 1878699280538583723445458440),
    (477507, 4337748917890039889714480646), (478399, 2521854529255592608138760),
    (479185, 94522558920307652430338), (480043, 16972554508360474360416770),
    (480915, 14535481795280022410627082), (481783, 4892483221975897326618126),
    (482659, 7301000808706048975307796), (483723, 203936387655262604074130883351046),
    (484483, 37852865791326308140034), (485307, 12155482445915571496944676),
    (486309, 800340353028008049090507179530), (487383, 365718443368994234010144232572420),
    (488193, 9666816161630549836806), (489105, 4954282270213998037071957508),
    (489897, 9666963091619665674762), (490833, 3102113319947306767159003660)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk15 (m : ℕ) (ha : 490834 ≤ m) (hb : m ≤ 563353) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (491623, 28556432970344989197830), (492625, 159725744400556616192828508674),
    (493389, 38554993850651255243268), (494263, 2474704940203131751762946),
    (495273, 954459071105370020251974372364), (496207, 1245288226434202819232530962),
    (496995, 18927663231526615123468), (497767, 122855464162922119044098),
    (498685, 9299076404769623069252004354), (499587, 7272555211589795204433418),
    (500439, 9728813403758793163148304), (501169, 74221019530889921550),
    (501963, 9740317161642462026244), (502725, 66224678743775652741672),
    (503739, 796002812263041889882343870986), (504813, 284430348658099196696902955572740),
    (505629, 75595910722731429987334), (506503, 24225850886778506751246872),
    (507309, 94780238558839906110468), (508239, 6196972900363128857532959760),
    (509019, 9630215420704421714436), (510043, 1749221393472439761510798330882),
    (511147, 366511353673268509545157162830338), (511929, 57148734292462902842886),
    (512895, 1252456779190952973457165828), (513997, 81609352325794552150386044044296),
    (514815, 66408713269341367961604), (515635, 19554126874348773573132),
    (516613, 1866600503392384075364041730), (517453, 9518952863768386865666),
    (518695, 23946913993940105550080815490834893842), (519517, 38222087218587396473858),
    (520359, 66224102834961106733574), (521247, 9699814694800262199119376),
    (522153, 9728185923986881364100612), (522853, 37759331701566343694),
    (523593, 147862756988241189894), (524337, 295298215093517550598),
    (525309, 1859432024426577167760098856), (526045, 332338083362601438210),
    (526933, 2446296822588420322101254), (527877, 8680125274734202232054221840),
    (528925, 160320507643963120347471156242), (529923, 1861830986597064630034630150),
    (530749, 19000724550032886859278), (531795, 636949192914206919288865161750),
    (532705, 14554555294052700591490584), (533965, 13365054355798623220515219527914754562),
    (534835, 26624924170649860785441282), (535659, 66224535761050394821638),
    (536419, 222227317676136727058), (537129, 148445405757794160138),
    (538069, 4845258985752980637617670), (539043, 1247640002271320355069494314),
    (540097, 1272002761550368497334668624402), (541125, 951997707655302072364832655364),
    (542067, 4873667255351088262021642), (543139, 479092495018421260841268807686),
    (544093, 11170550242224723308699322882), (544857, 185048411720556741136),
    (545823, 3723519933265324569365451792), (546583, 111406120177930341900),
    (547437, 38074945028837830562316), (548437, 3111822504862434115396437516),
    (549505, 164046483059218442800711337474), (550435, 14554555300253894733071874),
    (551403, 3723519933844602270493316112), (552213, 57112277653487527002646),
    (553063, 85224106261333277938694), (553897, 28482640375486039720466),
    (554775, 28408131127872242188810), (555673, 2437774560245514127149062),
    (556785, 638784323455955847808004392452), (557725, 33859589768748981286996482),
    (558493, 75234322849945097730), (559519, 660101979716482797714934790),
    (560455, 12127260507124720312911372), (561303, 47593465533830636248582),
    (562279, 4864075236682926454474248), (563353, 162196826555924697644482957826)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk16 (m : ℕ) (ha : 563354 ≤ m) (hb : m ≤ 642787) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (564303, 2446371603171288461216262), (565329, 3109367280116338176705037828),
    (566413, 475995217587677895906558345740), (567315, 19352444621785622265867268),
    (568173, 28924784653216772260362), (569043, 19258841042032652059654),
    (570025, 2493557365707780047241740), (570945, 29108888797080476121956874),
    (571797, 122855460778625127030282), (572593, 37182294693501995522),
    (573475, 57222091726973531719170), (574473, 1245203448368424500404421644),
    (575575, 952599752750648516109704235522), (576633, 1245278634559634452337263114),
    (577513, 56890915598711727982086), (578473, 7291520191641228348491270),
    (579517, 4954291420228576294270796808), (580627, 161568175758058525140343850498),
    (581635, 1873882465580431539816367634), (582685, 3723519932549808572671859714),
    (583533, 56780522227733488083462), (584557, 1876319061267186028065981978),
    (585835, 176578975555565963736850477110134274), (586789, 7282370319454253472680456),
    (587673, 9777063163413390296586), (588615, 7272999229914769854433804),
    (589707, 162191990888533190359193362950), (590563, 47261280597104751154182),
    (591705, 122175416698580557404098563277854), (592593, 57000586687264863291396),
    (593475, 66740899903756122195468), (594363, 9629783066352590000652),
    (595257, 56780088765091282289670), (596223, 29127594226221308833172484),
    (597345, 1747357267452336171765691975684), (598365, 3716351417694264357261412362),
    (599317, 12117703655350853687446548), (600229, 28408995812386716123654),
    (601215, 7272666179163128932469260), (602193, 2474852799567009493160964),
    (603099, 31573927350070059010621980), (603903, 738016699517721773062),
    (604797, 113632376426788735420426), (605845, 7434960125990859843603662348),
    (606993, 951978355544308084033330610692), (607885, 9887889997042257890324),
    (608853, 12202706115245625637210630), (609567, 145247710856217618),
    (610783, 123441193482749184810567258738702), (611935, 475992847143865260880022471180),
    (613165, 203779174049491266606290541478920), (614047, 66224103413286977275916),
    (615229, 41518666628056545803485319923220), (616137, 28408563488795206091788),
    (617035, 75595481189735326941708), (618225, 325469922705766217519447302472728),
    (619185, 21779666629408902567307282), (620325, 481563549060238107538362730518),
    (621297, 4874036913064700457391120), (622515, 486941241019122574517304960356874),
    (623613, 640806279442889018293357572), (624703, 1864192023130385855789009922),
    (625605, 10072067520752431400460), (626617, 12098887974706854813107202),
    (627607, 14564442749993321315303942), (628683, 3097324692187760530482268684),
    (629683, 29042665992397198388235266), (630573, 56891068714519135126534),
    (631503, 66224103406689872646150), (632323, 74366260635985252866),
    (633375, 3111793986336281736763544068), (634195, 111114514275345763340),
    (635287, 648003239605087068595163138), (636207, 56926942146112789026822),
    (637293, 633618986383961386597353996), (638313, 3740454376654609440060478474),
    (639543, 163052184791452270967090231773200), (640525, 2437000659438110586974210),
    (641787, 243867388768819831327415033268748), (642787, 9756483373511174519390726)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk17 (m : ℕ) (ha : 642788 ≤ m) (hb : m ≤ 727687) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (643629, 110969268849545972230), (644545, 28667110050439285310984),
    (645477, 19003173384494830978060), (646533, 5602190693841094335526209030),
    (647547, 4873667689392142167840262), (648613, 9918075017584527706939329026),
    (649735, 4352189656337986450108846604), (650755, 4864075096492994925302274),
    (651799, 4873593324270583284367878), (652827, 4845333056458380106009606),
    (653937, 1878699132246291617220529162), (655177, 124075023618345509207592753432606),
    (656287, 5585266064550280596308887046), (657465, 1427966366836884649739922051588),
    (658575, 6830497104923820696495849994), (659607, 12183780610392833680607242),
    (660553, 113374411344034005648386), (661873, 41904252411158885258470552481694722),
    (662893, 7263774702702360096281090), (663955, 29061665131110451904906754),
    (664963, 24254111439999867959515142), (665989, 21770294387532846004962836),
    (666979, 14516629799858417552463878), (667983, 21779924452054281185003524),
    (668995, 7282037127388997484807704), (669853, 111259753198899299330),
    (670947, 1864248691673406020845312012), (671907, 85187214446634034004998),
    (672763, 74221019522400649740), (673743, 36325219192336166980815894),
    (674707, 85076816587492277617158), (675735, 4920743634462029333268484),
    (676887, 1859384690944290705625449996), (678073, 635070531561616457549383336472),
    (679107, 7272667477310345406186508), (680323, 792912750645014589109751383566),
    (681357, 7395264393191884247270406), (682407, 9775410166965162865984518),
    (683697, 41357734394689176870964358284812), (684747, 19399851168777043368348166),
    (685983, 792936891455687775108716694532), (686967, 47371527579036285144070),
    (687999, 7357705959251144016662026), (689037, 31479627452493028141697046),
    (689899, 111978629260009538574), (691105, 802192418012142500534448294402),
    (692343, 479094922425471653028060729862), (693655, 447323450758651047693183873323010),
    (694947, 41043914148913284476357032023558), (696235, 122645826660062600716618884842510),
    (697375, 8075643475609546357830452738), (698247, 185768422503504019978),
    (699207, 19259121969512802681862), (700327, 3745271191474812359182259720),
    (701409, 2465223600297350788547076), (702465, 2559634181692291126134300),
    (703653, 2384903669610892982082339211782), (704743, 7319889842863709106866702),
    (705963, 802204497899676955912635682822), (706825, 37327533617357128712),
    (707919, 4949077835608770616886278), (708895, 28371818608423395264008),
    (709867, 66187358532914897229320), (710859, 85077250050151829865988),
    (711835, 47371673957036438195208), (712803, 19221653168442921193996),
    (713857, 7367187008685769130904066), (714847, 19332765391318854406146),
    (715845, 37963835600911932459018), (716703, 185910321067347022342),
    (717547, 221939102839210513928), (718327, 289921519659124230),
    (719655, 243870478839955940603963111508492), (720895, 1904578032478115611803665959938),
    (721957, 19380703884716920176774162), (723049, 29042701877078977737262094),
    (724455, 21053935324079227158169337079401482), (725323, 259985501375994925070),
    (726595, 476616634124894426238496016898), (727687, 21779812765035322075908108)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk18 (m : ℕ) (ha : 727688 ≤ m) (hb : m ≤ 816837) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (728805, 12127111063613144757047812), (729873, 14563817289514096477472286),
    (731169, 476614178235927051412455949834), (732183, 66445605638185883010564),
    (733285, 2437000948229143247324684), (734385, 21770183425015049528019468),
    (735415, 56779512304321631357442), (736383, 188933139767665531159564),
    (737493, 2502965211938486772434436), (738369, 222375947450500776966),
    (739365, 28777362672916573718020), (740517, 3721084003241003134277912070),
    (741409, 295295404681433061906), (742503, 14582890504005792834520582),
    (743653, 4966323974434432721230103052), (744645, 28740893662237133111818),
    (745693, 18926649347674143328770), (746773, 4873814547268035995633166),
    (747807, 85039925353317858017808), (748815, 151226841961731949987332),
    (750117, 479709132226199740926585471498), (751135, 47371672259356426241538),
    (752203, 9898154367984009338293292), (753543, 41357741620094790937677633162774),
    (754899, 488046112156701860666962600398340), (755785, 75230949531829146114),
    (756663, 628056252455514933766), (757899, 956323244606238295939944681990),
    (758889, 85262004599763216637446), (760075, 7432542163524236222435035662),
    (761385, 477233195663122733299539641860), (762475, 19371258571356358733334540),
    (763575, 31479554816184230617550340), (764845, 476621450607396823143209508360),
    (765855, 85077685777822245980182), (766863, 47482208072065778320390),
    (768069, 623815573628312268112659996), (768975, 148731947301264954372),
    (769993, 151300340140276598971394), (771007, 85224396723743871469058),
    (771913, 295293172664373609492), (772839, 147862750468581492228),
    (774067, 2490443968205538300836448770), (775075, 19369514755568305570824),
    (776095, 85076528924498418860562), (777139, 56853442828456545095688),
    (778057, 553549254399793693202), (779517, 20812605714855907706213222258445322),
    (780805, 1747386225004044840707430155784), (782049, 626242612035428977786752516),
    (783243, 1871427019902937668843602442), (784375, 9718778229737234941220360),
    (785497, 4958596353862032194934786), (786609, 24235258722311076638236176),
    (787747, 16953406646148515387018246), (788887, 2446592534571557538235910),
    (790167, 159737796063849259135100127762), (791187, 9778937219461588060170),
    (792237, 47334491108197766924806), (793443, 9294250221161213367190430214),
    (794487, 28482496810079178069522), (795643, 12155445552996945230169090),
    (796777, 14535518831183598627586578), (798097, 317558226001011396737015220756),
    (799213, 21808257786247202434450434), (800469, 4961478824548365294912800260),
    (801483, 28410580523068140424720), (802717, 640787463907490479243133960),
    (803923, 1254940780996280748449077260), (804985, 37890051432769791727112),
    (806019, 38111267146980473177604), (807147, 26634332873118735766259230),
    (808303, 21798776016241077097210370), (809373, 37889902262087414059014),
    (810345, 148295102483883493380), (811557, 1864192391920010866081929238),
    (812623, 28518813276732355905030), (813987, 951361765560622830884439197190),
    (815397, 81606874056346261377458997821962), (816837, 284432829345141305751407293499910)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk19 (m : ℕ) (ha : 816838 ≤ m) (hb : m ≤ 912795) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (818277, 122490467602725669719439601042438), (819439, 16953369893391293680584710),
    (820593, 24225778538134919021333004), (821755, 9690408002047335922277900),
    (822709, 37619132913779738120), (823675, 111545722927369946648),
    (824935, 3097353174532585073833280520), (826285, 636922615325681998984222345742),
    (827799, 62348450228934084577216781026593798), (828855, 66335790432203034855948),
    (830289, 121860346517399094318230387294736), (831555, 5573176473594423434428548120),
    (832635, 37853296999875150480930), (833869, 3102141840057046126565787150),
    (834943, 28592889048543598348802), (836127, 17000740845087843166718982),
    (837369, 3721102560810221648775873028), (838549, 29023996735596774728403464),
    (839605, 38334068073301520156162), (840963, 478466290372810987185337666060),
    (842043, 28850858041144162781200), (843285, 14253254340051073372065759754),
    (844365, 28445169289708070635060), (845845, 249271131575091404120368600188063758),
    (847027, 12183816643686855269156358), (848083, 47262582691525118136846),
    (849043, 221651428678672190466), (850327, 1864211096198482037485734918),
    (851289, 111978635934120936964), (852559, 4954225602679190572358568966),
    (854029, 203461642467193784970331021509126), (855303, 1247696522662255929297077764),
    (856689, 162182244367699641675347657220), (857863, 4901890341438368501864454),
    (858939, 28371958796155837220874), (860025, 19001444006584494852118),
    (861009, 110974330958063733766), (862225, 14554481509330353117465090),
    (863767, 20932239623690907907657249469895180), (864949, 9690444040407915682334726),
    (866025, 19222085478814555832854), (867207, 21846037007468599847421456),
    (868287, 56963692651594811444758), (869367, 85076821086736741175818),
    (870819, 203940101456563481977928185941514), (872137, 1864182947045735900878865922),
    (873415, 3716285232223302653466772994), (874633, 7263185128039696573271042),
    (875623, 185333822991811482114), (876717, 28703567269981933670922),
    (877819, 9887744744950770304526), (878997, 12155482729644616132857862),
    (880279, 1240415334521384951682433554), (881365, 9518670262951831932440),
    (882435, 28704722452091205452298), (883623, 29042776528742020364506636),
    (885087, 243867386464562231070133315700230), (886383, 626308983131254306740766242),
    (887625, 7291555931629510864799748), (888927, 2480725412924257709907640860),
    (890103, 7301591392753440897762820), (891517, 1112927476021005302204073384962),
    (893019, 41836186073909629680007049118726), (894163, 28445314524199084231182),
    (895273, 19000725686841909577734), (896475, 16981704237531764198478348),
    (897567, 94853307232967331677190), (898657, 85114005061492732593666),
    (899745, 85224106828732986165252), (901059, 3102132026243412509915483140),
    (902257, 14658336535487070510125570), (903363, 104002888915861841379862),
    (904615, 4892409435560404656064008), (905625, 221939082910797136914),
    (906745, 38074514383153073358338), (908037, 4337748918034726901112505356),
    (909285, 4873998866087717578473994), (910557, 640872688297456513014040080),
    (911779, 4864296167507077141761060), (912795, 37615755188389678602)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk20 (m : ℕ) (ha : 912796 ≤ m) (hb : m ≤ 1013829) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (914185, 954459156329185790544474150402), (915523, 3104568766052640532657079814),
    (917037, 122805523399392055488940687098378), (918255, 21808036425892262753473540),
    (919333, 94521261883640740971020), (920649, 626327614918105813432011288),
    (922017, 3721083228476063162711542278), (923143, 47334784396378777978392),
    (924357, 7395705962682362624216598), (925573, 21808000110558081083642370),
    (926665, 28703859990875175916034), (927765, 28519100381216990039050),
    (929007, 31451072034530288282764812), (930109, 85224103429008572556806),
    (931119, 258690153515960500740), (932469, 1866638208104368803362639370),
    (933793, 3723633382037279888413950476), (934827, 37615755162821332998),
    (936147, 645595091241484151760753162), (937587, 955704227104531659920043806230),
    (938917, 13008061040993656459449731090), (940153, 9728260001997350020451852),
    (941437, 7272555929357582785315848), (942783, 4954225344137666779258556440),
    (944119, 623890839228121242115769870), (945363, 2446370745255367834471434),
    (946779, 479097387758887701659869516306), (948025, 2465189011528511765350412),
    (949377, 11148798948697442152061469702), (950635, 12117851086879269744941064),
    (952083, 953233239287535389454643891722), (953433, 4961450786215697371223432710),
    (954753, 1864352546264380365491814406), (955915, 47260852181143474930194),
    (957055, 38185196529796547744780), (958329, 19484706334509733425710086),
    (959769, 478492877293371352610083706374), (961069, 12098814331850102610985998),
    (962427, 5578116069081865508233152010), (963697, 14535703442185335679353350),
    (965085, 1859375171560792290681424908), (966343, 29052220686383919185269766),
    (967695, 3723511004612222813098609674), (969033, 633609504611714474349824004),
    (970213, 28667106672773689641986), (971367, 19002455627702399534602),
    (972399, 221938544175635104260), (973753, 1245373340288956587829499394),
    (974817, 74365132511285873680), (976143, 623815574064035592390707742),
    (977163, 222370867801202886672), (978199, 74221606670166263814),
    (979333, 66446330730920062489094), (980589, 2465112636086358514079238),
    (982057, 320650667840182998853968200706), (983115, 148296239387463256068),
    (984303, 38074657922171152107024), (985459, 113632090446004784204808),
    (986733, 7263222310321230226917900), (987993, 21770406363886090973875722),
    (989247, 4949151190802451181604380), (990319, 111114509860220305926),
    (991599, 7319854681003047279266820), (992857, 21855407668044668612379650),
    (994243, 1885934018626624585333347842), (995323, 110970953284112747010),
    (997015, 93502701180701844652743862274887682), (998377, 631125687998895946916695058),
    (999525, 66519538407549881158668), (1000903, 4337654433523909468294349324),
    (1002399, 318776851634736462106132088344), (1003675, 19380703016087323724091918),
    (1004973, 7263406058872608960808452), (1006297, 29042739202347540573979650),
    (1007725, 2483162079237572095518183938), (1009149, 3718684709168733899421123076),
    (1010415, 21902520794285470748903428), (1011583, 94558303427600440232450),
    (1012633, 221653104342948906516), (1013829, 47262145275013599069190)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk21 (m : ℕ) (ha : 1013830 ≤ m) (hb : m ≤ 1120477) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (1015039, 19369372894292865189384), (1016299, 14592187516673979084440100),
    (1017603, 2446371749560241113924614), (1018899, 29042664986410003900798980),
    (1020289, 3721102118520715963934448648), (1021239, 432915162958267914),
    (1022439, 56779367056610910802438), (1023693, 7310334875294348845122070),
    (1024897, 47666820729692976974856), (1026289, 3730773524932948279614901766),
    (1027689, 3718684487520133224786955786), (1029175, 318779307413316102051104163852),
    (1030699, 635689511099638345618119856148), (1032295, 487890750700808591490410483420168),
    (1033383, 111114509911658208262), (1034779, 7442166272197572212877824520),
    (1036225, 1247668299145511968847430162), (1037397, 160671720166411538274826),
    (1038597, 75596062138685303554576), (1040025, 3740445042025095221104215574),
    (1041235, 56779371562409594457090), (1042515, 2474704651409788066465284),
    (1043835, 26624740709763631582545412), (1045147, 4986893371062656565904386),
    (1046343, 47263012222305386500612), (1047667, 7301000956764111250260498),
    (1049113, 2497725856889804091902263820), (1050277, 47778801612934273698330),
    (1051587, 9728703154509617046488586), (1052793, 9519386909289193538052),
    (1054209, 1861774318199300963571079174), (1055835, 244184920389116884614221496847372),
    (1057113, 9775520990440857855728652), (1058667, 952602179972084173415434028550),
    (1060309, 284434686255310481940663178237448), (1061619, 26634369047152470805189126),
    (1062843, 9741178475071062540822), (1064265, 1266982926494028211048291852),
    (1065805, 635106771038762120951051584520), (1067325, 164031929021733088895133287442),
    (1068673, 21779667061756631357587992), (1070227, 794141028722336397791632689666),
    (1071333, 221799469114668484612), (1072759, 10532209075261979147832526878),
    (1074057, 67860628297354640615801862), (1075405, 14544999741569465422709780),
    (1076713, 9756704736155219528652302), (1078023, 7272555214971884651547652),
    (1079229, 9777498319363463582226), (1080793, 794145798976418829096542668806),
    (1082139, 12099109624437800994079750), (1083363, 47445171574907834598916),
    (1084693, 7282221594834140915043342), (1086145, 4337635396491339359371137548),
    (1087713, 162184680812501163272030260236), (1088913, 85225688702717358511120),
    (1090369, 3109366837402920301678822920), (1091587, 113448774237922435663890),
    (1092825, 47371528709334406660630), (1094055, 66187782997239873013782),
    (1095399, 31488813932739372861752856), (1096737, 12098815195419729407121430),
    (1097865, 258978940244893764618), (1099455, 1112915433949292266093830871044),
    (1100827, 14563963134678148342481922), (1102177, 7357595420647899154091526),
    (1103557, 7272592247499917017612818), (1104699, 38046979216262961156),
    (1106173, 4347344619008163531500818946), (1107415, 19111405020994938340878),
    (1108699, 56779512862856324974088), (1109835, 111114503280363309580),
    (1110969, 111547979142511068166), (1112545, 955082839528977466597929256460),
    (1113777, 56742621061557478753798), (1115233, 5585341216014238382641257474),
    (1116457, 103930543087092732396552), (1117737, 9518667441622174925328),
    (1118857, 74224962431428461570), (1120477, 324342727071635789002446340626)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk22 (m : ℕ) (ha : 1120478 ≤ m) (hb : m ≤ 1232385) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (1122037, 165286765428020464842653700620), (1123299, 19037909652750369033220),
    (1124643, 9813262601519103514904070), (1125867, 85372399087845103634460),
    (1127235, 9756594486310125624757770), (1128637, 7272592392738780542800386),
    (1130233, 794793792217743941211450377742), (1131723, 5582828991982452296076364810),
    (1132975, 85113859818145362084872), (1134109, 111259746592971163160),
    (1135815, 608632613490785960059117821888012), (1137159, 29099370998261981812100100),
    (1138663, 1873863539646613082609944070), (1140127, 2504913446402656717234898438),
    (1141263, 553550954201887147524), (1142755, 3116667689910346836080985102),
    (1144135, 14535813838923001378506242), (1145289, 37622510553504678918),
    (1146709, 2436778288570335324275726), (1148163, 3733229118039710099856557572),
    (1149555, 21855187170118036820986890), (1150833, 56779951400861483535882),
    (1152075, 28666385540549011969548), (1153453, 14526369825402921594127362),
    (1154815, 2522113793600443235834882), (1156213, 7348076468377910263284236),
    (1157709, 3716256898742162270875423248), (1158987, 19037475059852792563210),
    (1160137, 110826275197724003846), (1161435, 56853010482883963258372),
    (1162855, 7291445256227228932508168), (1164457, 635687055617217675549238235666),
    (1165857, 2446296810201236424757260), (1167135, 47372393393908775259652),
    (1168753, 1426747712720953238995902531590), (1170045, 9518667445925934663180),
    (1171417, 9690665391808441053615110), (1172917, 4988084748572592794637829128),
    (1174437, 6830487771160655901525150730), (1175725, 56705725321446870620174),
    (1177149, 4864296023387525513740804), (1178655, 11158432981575522209806029834),
    (1179973, 66334782177850064767490), (1181469, 4959155531348799732774077980),
    (1183099, 2219019619455312812932041146898), (1184407, 28518813270118005869058),
    (1185813, 2522002246201894304744454), (1187229, 14516886899656135818745350),
    (1188507, 28556570345466691584528), (1189797, 28408421605693211545606),
    (1191093, 37854452182001500947462), (1192827, 41836814772040976986719698422278),
    (1194325, 9301503665401834130817024524), (1195705, 14629965591709497907347980),
    (1197253, 2483152560576907966163715590), (1198399, 39058613476901916680),
    (1199809, 7319852952199116305600006), (1200985, 222227326480820470284),
    (1202767, 284272513711091530469104870229000), (1203915, 297457132502671557130),
    (1205443, 1866628726767847336703166476), (1206739, 66446472013757561572358),
    (1208017, 85261146116503315547138), (1209195, 110970966461072936458),
    (1210389, 332188903815445217796), (1211715, 47371962741609264973828),
    (1213023, 19259268325505474498566), (1214575, 1252456704822996933693282318),
    (1216389, 31478461879914762425860240284845080), (1217827, 7291444963502049047092226),
    (1219603, 243865539197538768628701411411462), (1221015, 38742406461106930563421194),
    (1222557, 3716294933620378194219503622), (1224105, 1861802689586078394012011020),
    (1225537, 7320075177234206101474322), (1226707, 73934475797087263746),
    (1228269, 623815501285848013106580996), (1229893, 328680381467541146210133608454),
    (1231227, 28408418801844037750288), (1232385, 295728876188584249348)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk23 (m : ℕ) (ha : 1232386 ≤ m) (hb : m ≤ 1350019) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (1233573, 111119011269380015626), (1234773, 184612701642292855306),
    (1236655, 31236339377293093268200049290118658), (1238083, 21779702514130298728483842),
    (1239513, 29071036077673910381053446), (1240969, 7272777867860011236461574),
    (1242147, 332907236752171467280), (1243467, 9777641880389456888838),
    (1244875, 21770405211523241554477598), (1246473, 1871502282620444959960598532),
    (1247919, 12145963920907073720157208), (1249359, 12098813910198414345639946),
    (1250775, 12117706679539976620478980), (1252119, 9556136264562062661126),
    (1253905, 82082242974652341865075873948674), (1255119, 73934482394055182854),
    (1256815, 1269514801732120973966654967810), (1258405, 7432532645148413774327317512),
    (1259599, 222227878427134659608), (1260793, 111113964536845179906),
    (1262457, 159730561509079097527304193042), (1263927, 4864371682178960906650636),
    (1265515, 4959042194268916710995527170), (1266865, 19001011661020368079374),
    (1268665, 81606866746049013114846647033868), (1270227, 5578002732427579325720955910),
    (1271787, 3097382283205926884607396358), (1273377, 2495279708098259571752175126),
    (1274767, 2465224468913778739650050), (1276099, 94632809293201564632590),
    (1277653, 1869056539503611103860495892), (1279119, 46024257961936795223853066),
    (1280689, 1252532373228690606616092174), (1282395, 951978327099575085014483994130),
    (1283835, 2474742551476641623836194), (1285195, 28408852829678168705550),
    (1286557, 19000580997734969248776), (1287913, 19000580999924999917086),
    (1289593, 317551047931759646586060281346), (1291159, 1866780212148482729812561934),
    (1292505, 56742330020666264128030), (1293973, 19371517833449417700803586),
    (1295539, 9318428700949376372803502598), (1297143, 645594980993917237258750986),
    (1298695, 4354607655984083418278790164), (1300047, 28445025170104970516502),
    (1301385, 47703570663454890660868), (1303005, 1247668226218727618164167172),
    (1304473, 7272592686600846394003482), (1306047, 9918074685975473407220519442),
    (1307413, 56853875174038221096462), (1308973, 623834316098986117015149092),
    (1310325, 66445894420534051341342), (1311685, 9887743636694556215810),
    (1313235, 12393945355557210335501747254), (1315147, 62429417109590148784472784976089608),
    (1316643, 7338595275956290056227850), (1317985, 19369514775273447754254),
    (1319367, 75816840975110300634118), (1320877, 12146186001848862761550342),
    (1322277, 9740458459787158228998), (1323495, 111835096830041135620),
    (1324833, 47445458705703940395532), (1326193, 28445315658895218314282),
    (1327779, 9287025036476851493611766790), (1329265, 12174409233188209054451208),
    (1330489, 111980885483438866950), (1331707, 369801265876524867080),
    (1333087, 56890912218778625115162), (1334337, 111115086004245365772),
    (1335949, 10544260554813375754755247128), (1337323, 56817558709601380602374),
    (1338727, 9556134573496200203270), (1340359, 633562353874233052764180998),
    (1341979, 638341315250517351747683858), (1343589, 1262147406962999657189875204),
    (1345203, 1905276611674877713447518742), (1346947, 1116663047468985542131393102850),
    (1348503, 7272666322137015215457796), (1350019, 7291667911936616624689670)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk24 (m : ℕ) (ha : 1350020 ≤ m) (hb : m ≤ 1474243) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (1351743, 952029130207369291753534397956), (1353253, 7282665179696378870761986),
    (1355257, 41660393673501084463428899630088710), (1356655, 66224533498221004591628),
    (1358179, 4845444458061703938313230), (1359909, 951378785301468475417546197528),
    (1361275, 56705585149228018566152), (1362633, 9999002796053795965446),
    (1364295, 4954263417785661088968082948), (1365865, 3097315653421711682080873992),
    (1367503, 9313621220040932572187591180), (1369009, 16953849364661570246541830),
    (1370385, 75779804504254737160210), (1371985, 9918112537832425328433177602),
    (1373757, 318779288375553381514911550480), (1375017, 37329242249366864400),
    (1376439, 19000580452342439870980), (1377997, 21798554798888585769124358),
    (1379419, 19001011667617304019480), (1381209, 796621716170270446297060346884),
    (1382445, 295727187313121433628), (1383849, 9666818417828310554628),
    (1385389, 33859479232401909184332294), (1386775, 85040788925203538909192),
    (1388289, 9756631380924164527626756), (1389807, 29023776382917922513356822),
    (1391457, 3111803467819179012773905426), (1392979, 2502966216265401354424340),
    (1394665, 7432485569921096282018023938), (1396203, 4949078989102055663470084),
    (1398007, 477852184424807705539573583366), (1399423, 75669122357576735654412),
    (1400859, 28372252071082711975434), (1402387, 12174409524800656835215878),
    (1403803, 47334924590699833198086), (1405093, 148296224011447306754),
    (1406493, 38074233462295728884760), (1407993, 33907034648739873387446794),
    (1409655, 1864173169985407046182511634), (1410927, 150024478143724520460),
    (1412749, 159703993218001405354994960390), (1414287, 16981704526364689767860742),
    (1415985, 7430077088076060880366863378), (1417267, 221796658762813150728),
    (1418913, 1245260113740371715722445346), (1420579, 2480810783739188966983074836),
    (1422103, 19399518843661269803601420), (1423395, 221796091440517221892),
    (1424677, 75085708494849311250), (1426125, 9668112076829727263244),
    (1427517, 47704005852304446721042), (1429279, 1434789458901363166667186507796),
    (1430847, 12117851951581401806144518), (1432423, 16953628005390800570941964),
    (1434103, 1871474096575910504200017410), (1435539, 19148155517689355960848),
    (1437235, 626280354362605841276077580), (1438929, 6194564676773614405945786884),
    (1440507, 4873888183934399992304662), (1442169, 2483162042777001293035737618),
    (1443577, 28408854509800657132038), (1445397, 1111063303405437798945313261062),
    (1447219, 160325334197513520168833518088), (1448775, 29042849598524481045924874),
    (1450465, 11146306018958445103582152204), (1452189, 640749685123133552376547338),
    (1453893, 2497669741897683221904491532), (1455355, 9557000408107755898370),
    (1456915, 9728186502734652178564610), (1458619, 2502542670703452683655315974),
    (1460085, 28408420481983637488138), (1461667, 12146038288302250918153740),
    (1463113, 9777066534498927385094), (1464709, 7281927599285334505032200),
    (1466287, 12174372349822088169915906), (1467835, 21845963796387994202014740),
    (1469523, 5587674066349317825052806672), (1471339, 162218530661375735653286159378),
    (1472955, 2446518170021796038445060), (1474243, 149593823722903044620)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk25 (m : ℕ) (ha : 1474244 ≤ m) (hb : m ≤ 1604979) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (1476063, 1110439478460431180247973761030), (1477765, 1864182984948034780323254274),
    (1479475, 8675299126725584258775778818), (1480903, 37890049752939362391554),
    (1482735, 479709066040291945495183102980), (1484203, 56854598564693772995586),
    (1486015, 476021851735058422240182147110), (1488115, 10508031825411307543617794138703362),
    (1489717, 26691110656590513251419650), (1491567, 1431065976821969046639250507270),
    (1493185, 2465112634404182562310664), (1494639, 19259121962915564227600),
    (1496355, 4954225269780989547085432348), (1498315, 365559994316447415350906699384328),
    (1500043, 7434931643782858535703022094), (1501777, 2480753856940610511719110658),
    (1503237, 113521408860112206562822), (1504965, 2483152560150196299516873228),
    (1506559, 9841486118808361197900824), (1508137, 14516850581533584206076422),
    (1509883, 4983211229176053629918252556), (1511203, 74796937115859026964),
    (1513065, 644971634172407862459497583108), (1514545, 19149883208854801615362),
    (1516003, 9888177116937603123212), (1517607, 7291518465630056875559952),
    (1519435, 953840195716809479553152975880), (1521129, 2483162191069267002122700348),
    (1522977, 796626532910151888474536805910), (1524583, 4845222376596349760180250),
    (1526335, 5592528842554589608405633538), (1527937, 14705560773952956258194952),
    (1529397, 9777495530993453237772), (1530843, 66298037304246653028870),
    (1532599, 2480800932890760116330434568), (1534069, 85334783334890433811976),
    (1535685, 12146185138283642736738844), (1537143, 151227711725981118368262),
    (1538595, 57224977410590943609354), (1540075, 75668691687651183433224),
    (1541689, 2465297099588627879954438), (1543015, 147867264925953819662),
    (1544475, 47703570113638779717124), (1546113, 2465112633280498892149764),
    (1547589, 9521115717472354698756), (1549363, 2480781969633922688354096642),
    (1550989, 7338670647058343480001030), (1552513, 37890478151059378407950),
    (1554273, 3104540616176505956768678404), (1555633, 221793850670212580354),
    (1557283, 9728186504372856086596610), (1558803, 66187357411387367621124),
    (1560403, 26634331866590650446515202), (1562047, 33859700013501111797418498),
    (1563417, 111545725169543808006), (1565047, 7281963913502352030705672),
    (1566807, 4968826863830523237982536202), (1568419, 2503039568626749092004890),
    (1570039, 79817770480664532060866066), (1571707, 21789110788726405838146056),
    (1573075, 37614633729345848834), (1574559, 56963983679128679352838),
    (1576033, 179856189322646756264450), (1577937, 1271988292293108408772713776146),
    (1579575, 36371888157805933761400324), (1581073, 9850995398439802113026),
    (1582959, 796619421099872669466284920324), (1584895, 317560691039134844450297224194),
    (1586523, 29023740354125267403408900), (1588039, 38000588345025567130118),
    (1589809, 2488026226961386419891078158), (1591263, 94559740643238096405510),
    (1592775, 9629345649892409608722), (1594833, 203934535533866601909793319160844),
    (1596337, 85814686904577273496070), (1598127, 1878680353891485684787846662),
    (1600173, 81606873999676568232895376395786), (1601559, 37183416212609172486),
    (1603233, 2436778869539111104022532), (1604979, 7456749456549057771774151698)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk26 (m : ℕ) (ha : 1604980 ≤ m) (hb : m ≤ 1742965) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (1606639, 9718667836379408326460948), (1608433, 669820794406227807977604614),
    (1610079, 53211664152991292342011914), (1611687, 2616708119621600152521222),
    (1613319, 14649297483945613535486470), (1614943, 7282221594834166717877262),
    (1616617, 14611039514334412753208322), (1618429, 3109385801658448530720818196),
    (1620213, 7439757865734915464693810704), (1621717, 28778800447158076179458),
    (1623759, 203305059939407303563753233845764), (1625703, 160325381051235817777574707722),
    (1627533, 626299464610740517976019984), (1629073, 28593323082931648464902),
    (1630437, 76818475022578484746), (1632105, 21808000108858330461899788),
    (1634043, 478480807257116572074382459396), (1635969, 798485879710762699773375287818),
    (1637673, 4902223247529343287952390), (1639719, 204252683772113755711280876622346),
    (1641535, 5575594362269013032873236500), (1643593, 284909433861267253938896115208706),
    (1645413, 1866723358564923493717379076), (1646943, 38001450793141845886980),
    (1648479, 28408854529488785640976), (1650037, 19332333597709497013266),
    (1651549, 9630222173887625564690), (1653379, 2480725669597352720560428038),
    (1655073, 9718667839763704547117580), (1656769, 4864186638266484949910034),
    (1658305, 56742335080584750443010), (1659967, 12127149538988548167698970),
    (1661785, 5578012545806074592369053208), (1663459, 24226293606388848077571086),
    (1665019, 56706449272853654277638), (1666725, 24235259587002136341125124),
    (1668433, 14592186797217298659021324), (1670395, 159704012253743153287727809544),
    (1671937, 56928671519607899557382), (1673625, 7282000519881599723767330),
    (1675303, 7395558965197096719484430), (1676977, 14545331931585960765163532),
    (1678689, 7263184263337590349237764), (1680243, 10109104550271705550854),
    (1681803, 19111692118848443520010), (1683463, 7395447857477871919830530),
    (1685443, 641260269574591531128296704514), (1687527, 41041443094725043785972820216338),
    (1689597, 122013249037249204667282854775302), (1691293, 7272555211029104371831302),
    (1692835, 37963551874230031746578), (1694365, 28410585015664196325384),
    (1696195, 1873939061771456762717799944), (1698039, 8672843348868220090602359314),
    (1699777, 2446519034723902429725698), (1701499, 4864370385170846936337414),
    (1702897, 38480459528029870082), (1704883, 953225976324633543776374757894),
    (1706455, 9961675862847531649550), (1707883, 73933919452691696130),
    (1709905, 479090067980012987436872763918), (1711885, 1905192166757154570515239143938),
    (1713733, 6201818232555993318172265996), (1715445, 9784818582342764599577610),
    (1716835, 37183422835447833614), (1718425, 66334780486818226898444),
    (1720159, 50812737288481930333128200), (1721713, 19221659327915919411714),
    (1723519, 5585246916252912884595826706), (1725075, 85114867496337629382148),
    (1726939, 633505869938267447070819848), (1728907, 635687197066846159581659661350),
    (1730785, 2480782005952054036362167810), (1732807, 952597325453268057936997912070),
    (1734669, 1245278633988235868647195684), (1736365, 14781044421739100995060242),
    (1738063, 4949261582473610282535474), (1739803, 12155482874879106643002894),
    (1741369, 37963976912414378951174), (1742965, 38001447971760582038018)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk27 (m : ℕ) (ha : 1742966 ≤ m) (hb : m ≤ 1887495) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (1744539, 28594041972272697444870), (1746283, 4873595774785184862700044),
    (1748025, 7291518751052400555590154), (1750033, 162182262961006046968642537496),
    (1751635, 104114001706042891830792), (1753533, 633590577244058095853110794),
    (1755367, 8058727996045111329272763422), (1757217, 7442166383743842851656827916),
    (1758789, 28777357619569789512196), (1760665, 4968704045700068738682192414),
    (1762387, 16953518621402248828296200), (1764147, 12099108902725034243919382),
    (1765887, 21779591835321738130099210), (1767483, 113521699333440572621836),
    (1769095, 38111263184409386420738), (1770837, 14564332217026113461553162),
    (1772575, 2578966800710024885832194), (1774309, 7320223613630539813750280),
    (1776219, 1240386410459031761261300740), (1777969, 33859553448911251597301256),
    (1779567, 9555853659347293570590), (1781313, 5034190683799209427080196),
    (1782897, 132449498763680165268496), (1784529, 28482066148983943988754),
    (1786257, 12174372772030147102901770), (1788135, 2483152781931628999706158092),
    (1790145, 160325334012908154511004272182), (1791897, 2437000945425405709517352),
    (1793925, 2378092543764256797573577180684), (1795539, 47445463171971309765136),
    (1797277, 7385818361527008005721612), (1798909, 18927085629550061289990),
    (1800537, 19221943617685279080970), (1802605, 635072940005131347708607075340),
    (1804395, 9690517961931448478601732), (1806187, 14535665685136288871354370),
    (1807983, 7282442664715691963449866), (1809897, 6204254751865636568314414602),
    (1811643, 29052294184562618722158084), (1813519, 5580430434917508982695398936),
    (1815319, 7291444966873151628903950), (1817059, 19437593210562486674392590),
    (1818643, 56779950285974108247572), (1820569, 645594760353562076753695238),
    (1822165, 142004336307045922899468), (1824367, 365245547856211096426389625898498),
    (1826419, 318779259968575203769006034964), (1828239, 14582705315421775882619398),
    (1830315, 953835303308962001052827387404), (1832115, 2446481995966199951134212),
    (1833745, 57296165260162288978434), (1835919, 366034737067921405647080080934418),
    (1837833, 2483162300162786546839586334), (1839907, 954478395139989430157936166402),
    (1841817, 5575594436058241205002570768), (1843863, 477252491031934211445263698966),
    (1845517, 47555851478521684296210), (1847337, 9718852162526303511381510),
    (1849143, 21807926178892695882175492), (1851199, 796005164002266994273713267726),
    (1853077, 7437415572380489906950379522), (1854879, 4864408437174805601846278),
    (1856797, 1885962169084288747994874386), (1858579, 12174299273295240176470548),
    (1860513, 3718665340243952218764089872), (1862119, 9556135701577551580178),
    (1863889, 5005745660911733881572870), (1865529, 28629924956431962342916),
    (1867179, 28408563466813629927946), (1868673, 73937851289260525066),
    (1870303, 104039929881461011910676), (1872235, 16110164473199015356109948430),
    (1873975, 12240448143500659240604184), (1876053, 1902716315012787204177347217424),
    (1878135, 476623868937486663677718693418), (1880205, 477245237624010631279282886680),
    (1882137, 3721102340312308176830992390), (1883607, 185765051426522531338),
    (1885563, 9313640183433449734965560326), (1887495, 4959098752278417687624944140)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk28 (m : ℕ) (ha : 1887496 ≤ m) (hb : m ≤ 2034685) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (1889343, 7310407929855102167943172), (1891143, 7272887543463184650209296),
    (1892779, 85113857001162380281388), (1894683, 4340213809589125083492918276),
    (1896199, 110972079166772873736), (1898007, 9747334078369762949465100),
    (1899637, 57333491096090038111238), (1901295, 28888034134557622278174),
    (1903375, 1268281725693852921799934084610), (1905013, 122966869720081174759430),
    (1906639, 47371672833344042832414), (1908597, 3742862747245532000360990218),
    (1910253, 141782402855893846983172), (1912059, 41160294272124797947347460),
    (1913913, 7263111055641160933442070), (1915915, 1240471302377499802950959628),
    (1917883, 2483181337490889995932665350), (1919373, 148295111314204394502),
    (1921173, 9728628646968325674507780), (1923013, 7338596138382390266169356),
    (1924965, 3750116411976182754235001860), (1926787, 7282000381967682562820108),
    (1928445, 9556711621413181589010), (1930423, 3097371880540994940695348226),
    (1932219, 14535592475746775159672856), (1934037, 7348187151076577495091222),
    (1935739, 19111693253595747452424), (1937875, 321250285859512165145021913612),
    (1939695, 5005967883125459861770252), (1941385, 47261281177612396922382),
    (1943233, 29042777394561273217680386), (1945039, 19409664694213243513865736),
    (1946557, 111545725135151960066), (1948225, 28519678541805479921154),
    (1950067, 7291444965749459738824706), (1952169, 1269514971737177551622061296146),
    (1954339, 1110446816870948050255028160518), (1956157, 16972224199740238197164552),
    (1957845, 85041220694692526687748), (1959693, 26653296272386917151802884),
    (1961407, 56780232884651568137730), (1962937, 332331338975523636738),
    (1964787, 21817445273608874627957766), (1966813, 1861783726038767542978874370),
    (1968337, 442868796597488452616), (1970355, 1864173575235055302270256644),
    (1972045, 66187350656030741892638), (1973719, 122966582046092165776904),
    (1975539, 2521854816377669628994590), (1977715, 317536494113899642340361504258),
    (1979247, 295293161712206481418), (1981389, 1586425090606225682938951370250),
    (1983379, 6201799121876621436303709190), (1985209, 55676885735095484805679110),
    (1987053, 14658337973802271465147914), (1989015, 3133583280298218131796396574),
    (1990867, 7291408502920251379418636), (1992709, 2522002393692557207670278),
    (1994437, 9777066534498625390610), (1996297, 12117740836521854794207746),
    (1998325, 1871436317641791417830476290), (2000205, 14535628648656671608276492),
    (2002245, 3725918894717485657556391442), (2003923, 28593320826734157498392),
    (2005765, 19456187095101946221693960), (2007483, 151190526623195083309572),
    (2009167, 57554419103283379573250), (2011029, 29099259452552248681565208),
    (2013223, 477864226422296914129538386946), (2015083, 12099035259316327776653826),
    (2016915, 7470932072123841782486020), (2018983, 1885952687162849051265337350),
    (2020995, 1878765466303963889293329924), (2023023, 1240433818017081247270313476),
    (2025165, 2701830760480193695145823700492), (2026723, 148300164678367577090),
    (2028585, 7272482865774177251233804), (2030613, 3725937932196470706627942922),
    (2032503, 7263223464920520825113100), (2034685, 794155479312064571081302087188)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk29 (m : ℕ) (ha : 2034686 ≤ m) (hb : m ≤ 2185857) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (2036535, 9699926243333532564982302), (2038399, 14573518692236780657837576),
    (2040429, 626270838149626153289647626), (2042167, 47703571791510703573512),
    (2044033, 21846073326756711094424070), (2045899, 2437000225410242333250566),
    (2047875, 11148733056934364130512348164), (2049607, 85446185505562466976770),
    (2051319, 28482494026184657470980), (2053009, 75596055396454200510984),
    (2054575, 184612688456709311490), (2056315, 56779371575620946626062),
    (2058187, 36325292546960292032939010), (2059747, 369223685855810946572),
    (2061963, 1744878922372536573100250242564), (2063539, 258689592782074677254),
    (2065575, 1240405228296889072731168274), (2067423, 7414448285900690315675140),
    (2069125, 28519534422193787644428), (2071339, 635687159251167173308861255688),
    (2073259, 7263110619915792820078094), (2075163, 7300815771577568148851212),
    (2076877, 66225830567933261909000), (2078955, 1859413024282995997091956740),
    (2080663, 28777930726811628213260), (2082565, 4892519975874454817605134),
    (2084913, 122015101073789605349243574163972), (2086813, 12118072448956078791722502),
    (2088399, 112271372014433075716), (2090155, 56890336883943408534542),
    (2091873, 9851576903768666806284), (2093779, 14563890789953254380145670),
    (2095675, 12202927901212737214480914), (2097445, 28519102628644258974210),
    (2099187, 47446759111282567808518), (2101107, 4864148737104578372830732),
    (2103003, 2465445104778516743590404), (2104737, 19037473925209136433670),
    (2106825, 3109413913775284570949291524), (2108593, 141892645340857183636482),
    (2110807, 164039201464813492157681109530), (2112703, 9690333356578967945481734),
    (2115069, 365877518881197765954268286943748), (2116969, 24282851323705802073835016),
    (2119143, 792908009388496654387496750602), (2120887, 28447042237414456692762),
    (2122645, 57000586119951022557704), (2124397, 38112559097332298947586),
    (2126325, 14535628652043158931901450), (2128249, 7480339768612145383343624),
    (2130303, 3740426779748451262289674786), (2132227, 43530958852361362660394498),
    (2133987, 104040071782224145679878), (2136115, 4954197010225887231703515660),
    (2137917, 56779224067339853892618), (2139855, 14544999882869895007314450),
    (2141799, 16943888269765351079805444), (2143729, 2474704937412656703605768),
    (2145627, 12118367735883559835140618), (2147227, 222514419953425976838),
    (2149147, 7414152999492264225146388), (2151247, 7432532755688138520716772876),
    (2152843, 333051347550823910402), (2154787, 7291666616588799673766402),
    (2156715, 7263185992726444430071308), (2158689, 12098813899517715411239428),
    (2160729, 2488111046388775885739005968), (2162503, 94559163617336512356866),
    (2164437, 14705781991881566179165702), (2166519, 1910178463973305921938785286),
    (2168653, 3102132319518372147780258306), (2170599, 24207146317255638195639300),
    (2172729, 2487978855720892103170067484), (2174529, 56779224073919710241286),
    (2176633, 3116677061001018790939858434), (2178595, 14582889210907550736058380),
    (2180523, 2437665176270121795585546), (2182437, 2531262655831166902871562),
    (2184219, 37852865784626056922658), (2185857, 37327529210384876550)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk30 (m : ℕ) (ha : 2185858 ≤ m) (hb : m ≤ 2346085) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (2187955, 3759816189049046459637434882), (2190073, 3097353027104992969465007106),
    (2192055, 21817370480080201798389252), (2193849, 37890333479655723762204),
    (2195649, 47555852032701281602066), (2197585, 7395336884279445227439630),
    (2199175, 554701615136290899458), (2200795, 112410420678697943564),
    (2202915, 2526702334668529829796775428), (2204697, 19001016734166919022110),
    (2206653, 16972406934970809170265606), (2208753, 1240518562646471314373743126),
    (2210559, 9777496652486688375300), (2212347, 28666676581191454562826),
    (2214069, 170227713997995533015044), (2216017, 7291520191628068536322586),
    (2218117, 1864437622216265802683515398), (2220259, 4959099048139578267193312776),
    (2222247, 21789109922924779295738380), (2224513, 161553621388098332849250764324),
    (2226505, 2437111625885467300465160), (2228653, 1864248727558094397466215426),
    (2230453, 75779803950101010451980), (2232757, 164039201390595291860705609228),
    (2234559, 19003175093075737577488), (2236663, 2495345857830913089714521114),
    (2238643, 14526110566128933432723462), (2240653, 14535518255870625196672002),
    (2242779, 5616688358226838061146314246), (2244607, 19110977174606420772876),
    (2246395, 47335212255909797561868), (2248527, 638322462822189337609772550),
    (2250333, 104040357732213049395724), (2252145, 85040211325305951490572),
    (2254107, 24197775660637880112121866), (2255955, 56706157115047670710794),
    (2257777, 28408419910220612242962), (2260063, 952621513377355712915900466702),
    (2262349, 2537162974700877287143358596616), (2264539, 4337654285803587759853670408),
    (2266693, 2509796188872321653287551500), (2268835, 3716370306587697774716390402),
    (2270673, 18927235937187490038790), (2272489, 75671285195922064412166),
    (2274475, 7273146085538786760328200), (2276265, 47261280597079585458712),
    (2278245, 21846221185550896388375050), (2280397, 8051512184463969675540562946),
    (2282379, 9690886610836519619399178), (2284353, 9690333359961151543837194),
    (2286507, 3119057060641417432752587788), (2288677, 626355839301234055384143878),
    (2290507, 37964701409255904642566), (2292355, 19037763853144672176642),
    (2294655, 637551275824957049264704590348), (2296657, 4845775635324533261992986),
    (2298667, 29023887065066739509756936), (2300829, 3728355600514423177309853190),
    (2303125, 476643239790085554966400208904), (2305287, 638454540934430869829719050),
    (2307153, 66189225272752996614660), (2309299, 6818474292911996529575461908),
    (2311467, 6818398623357311058344019472), (2313343, 37890045801105728083970),
    (2314995, 221794402625149867012), (2316969, 4845370239867866527833124),
    (2318803, 28814682316446810376706), (2320975, 4966277266270179285988541448),
    (2323363, 317553437483784813327325202946), (2325673, 796005145076052809095679184396),
    (2327697, 9728186933351732587659786), (2329683, 36296219906916944111208972),
    (2331349, 405975319402236216840), (2333373, 4901927379611379567298564),
    (2335557, 633533909423832771741748752), (2337549, 12127148536372482167150098),
    (2339577, 2436851933124715795710492), (2341939, 1585818134214138355803205274648),
    (2344113, 1245203150494706876296073734), (2346085, 7263185421901788664962578)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk31 (m : ℕ) (ha : 2346086 ≤ m) (hb : m ≤ 2512719) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (2348115, 14516629223960391999170052), (2349955, 56889905668702971632654),
    (2352007, 7282221447910817186188812), (2354055, 7291555502663939837003268),
    (2356087, 7319890710930329803298828), (2358123, 7319780032728699622523910),
    (2359959, 56706600145631805047838), (2362149, 623815573631705360995845126),
    (2364195, 19380665978514843240105988), (2366419, 1869027800482909741985958420),
    (2368447, 12098889562234476437177868), (2370477, 19409148473037921018840082),
    (2372367, 28518811585674479932438), (2374387, 2446296958857399001547270),
    (2376075, 73937292805872027658), (2378439, 1586425118940137468980328402436),
    (2380483, 2446297829142834060598274), (2382693, 3721111858401017344312083972),
    (2384557, 28446612123910372723718), (2386759, 1864182724826899840393020936),
    (2388793, 19371258140699635742148132), (2391019, 2483162152587701442973139474),
    (2393019, 12098999811485911271088646), (2395353, 319410347657287835950875283984),
    (2397399, 14535665975044528557788718), (2399625, 1900450315661703186410244100),
    (2401513, 85371822066350460109844), (2403585, 4864075091987231001942532),
    (2405437, 66297748521821344633346), (2407495, 16943888559673581773391368),
    (2409373, 28666392856708006674956), (2411563, 2512176742346262196041156110),
    (2413465, 28409286290130208427010), (2415499, 26606219607869171761155090),
    (2417913, 2378704278933544582797987546630), (2419789, 28888322362923830346246),
    (2421837, 21817629166834010489892358), (2423707, 47482208052300573184020),
    (2425425, 222083767628481302020), (2427643, 4954206418069294486823637540),
    (2429505, 94558735766601925658634), (2431389, 47446471426264183867408),
    (2433429, 19484522301662048224413706), (2435515, 7282221598207425341687304),
    (2437603, 9728148892562775613772300), (2440173, 83190818279868709619064151083544),
    (2442379, 6209099715559356047645347334), (2444107, 221506739562570975752),
    (2445969, 9557577981677463014406), (2448045, 16953371196618296889836562),
    (2449923, 141819001918956844353030), (2451807, 19221941381235611666980),
    (2454039, 1861783873900930726623582724), (2456299, 640749685842576978633036308),
    (2458567, 631068796509092801071682060), (2460483, 28740604862339592882700),
    (2462733, 3116648616554002660614210052), (2464845, 14516849863185220192306692),
    (2466919, 12127222029486625489431048), (2469153, 652848313979845029341431812),
    (2471067, 28703432148790349660688), (2473317, 3097315505706414828316658182),
    (2475717, 1902116687807403951218821043742), (2477635, 19148446004229343806978),
    (2479545, 18926656103202266156548), (2481807, 3109366838259173769244707340),
    (2483703, 47778515062611990544900), (2485623, 29073366264232840399876),
    (2487553, 104040070066986006481422), (2489809, 4344945841589962902696628754),
    (2491857, 14545553138831750270293002), (2493939, 14544964284204023854006788),
    (2496195, 1861840431618267308153638924), (2498319, 12117740404732600533911050),
    (2500737, 161589879865532794278104139270), (2503323, 162737757607804820070068964953100),
    (2505249, 37963838978706175951878), (2507997, 135243426009155825114158892021061648),
    (2510445, 162189497625881357845537754652), (2512719, 1240376892371433118140991504)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk32 (m : ℕ) (ha : 2512720 ≤ m) (hb : m ≤ 2686209) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (2514787, 2465112489169674436219970), (2517045, 11146334131071896889902895628),
    (2518977, 18928092184092414447622), (2521027, 21789664335170410894590470),
    (2523135, 26624813349999901787423242), (2525587, 952607015896725260635653145608),
    (2527485, 151301493631311183086640), (2529597, 16972295969103900240643590),
    (2531695, 2465409220087880837763074), (2533939, 3133592467059926207818236948),
    (2536027, 9775409736301920149309978), (2538327, 626299244115067919718027270),
    (2540605, 3721168673794612585657403912), (2542527, 132263876158408939409938),
    (2544289, 37615766209208648198), (2546227, 47371533780316460286978),
    (2548533, 1247630448152679464371225606), (2550987, 323107195734259340821922710546),
    (2553115, 9699814977394704887450132), (2555077, 9519101480339821300232),
    (2557347, 631088497915492464364093968), (2559457, 16953408374976618671901716),
    (2561745, 8058728291338822745617204740), (2563863, 33972815448154544579942410),
    (2565997, 36287033713207761726211596), (2568115, 4864296174258044447099394),
    (2570605, 321252741084253766237163360258), (2572689, 58085292784332916119962116),
    (2575015, 1864276988257673950402057730), (2576989, 18926654414214967591950),
    (2579269, 2490434449688993757502252046), (2581579, 6811135549921372237787828238),
    (2583715, 26625035139883516832384520), (2585835, 2465112632708658390895164),
    (2587965, 7291445252293194112306698), (2590075, 48385515427203656447166984),
    (2592205, 21874186594246959907473420), (2594869, 40882362973343817115039817407496),
    (2596833, 28519107136590526420492), (2598937, 2465297682241915267189790),
    (2601235, 1869084541519823309995640334), (2603349, 31451183866799243102650896),
    (2605299, 103930254289308552660490), (2607427, 12155483594342298372802590),
    (2609203, 369223688046076758530), (2611555, 623900244473514444983502350),
    (2613715, 7272669205003718330156040), (2615899, 12117630009681551145045006),
    (2618035, 7518118411120956858435080), (2620195, 7282221447912965005643784),
    (2622349, 12127369461019473517089816), (2624307, 28704864860854147484166),
    (2626629, 1254912263054444016678863878), (2628775, 9776221390782689074879490),
    (2630917, 16943962055609140285676546), (2633439, 480942151854903682464530041860),
    (2635935, 796619373876065431954982834698), (2638263, 2502533152621463697285716484),
    (2640757, 477849728831412702451113528326), (2643057, 3735713379823794802962597388),
    (2645389, 1859385095624822955872357894), (2647527, 38714257024071067713014790),
    (2649865, 1240443078863568376871389704), (2652027, 4864075672958128865150470),
    (2654355, 1240376929555440798982736908), (2656357, 19111838501255030639106),
    (2658345, 28371970037545471576068), (2660523, 21808147105789339595708422),
    (2662693, 2521780886950838729449496), (2664885, 14611260876371579319747082),
    (2667195, 631097463176675563661560332), (2669197, 56705581217228208342530),
    (2671585, 3716294711827073028005300744), (2673747, 14563819738911534246789642),
    (2676297, 159718500327401618366404756998), (2678107, 74223266915477490696),
    (2680423, 3111831802885034543652934680), (2682213, 111113403751724221956),
    (2684017, 184614940247799370242), (2686209, 12117814335254528237240836)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk33 (m : ℕ) (ha : 2686210 ≤ m) (hb : m ≤ 2865493) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (2688753, 477852128383739381966514816516), (2690953, 7291518462252383025504770),
    (2693325, 1240584638880356854764013078), (2695827, 317551057558939647669984042502),
    (2698189, 3116724136947207997785638418), (2700373, 4864369955055083768775180),
    (2702719, 6830440842500758506666591246), (2704935, 38742368846475520333188612),
    (2706949, 37963551882991596996614), (2708749, 110972074742990250510),
    (2710929, 24225889222001250188264964), (2712919, 28519679663333042553876),
    (2715277, 2480895306575863189227045890), (2717085, 74798599603210032658),
    (2719107, 66225112767151608038406), (2721115, 19369376830604622169608),
    (2723329, 12118146375541754331529734), (2725689, 1861783652107687046762073094),
    (2728023, 2509739559392385561862866960), (2730573, 318784105115871668527247525386),
    (2732917, 4352217992265705182551607840), (2735089, 29061554163548182113290778),
    (2737099, 28373113377949105656326), (2739333, 4892409292021309100266000),
    (2741557, 2437110905874658483765778), (2743927, 1240499784003993592325999106),
    (2746107, 14554444327607474583771148), (2748439, 4961450565290537938969561614),
    (2750805, 1262147443568846715216987154), (2752983, 4864148307054794222347270),
    (2755207, 4845370964382231753393666), (2757207, 85113565956242419746826),
    (2759439, 9718778234803732881737226), (2761473, 19037473922940991703044),
    (2763487, 75595478357376195498516), (2765685, 7300927313335647931864618),
    (2767507, 443154777312854936582), (2769537, 75779373282451589300746),
    (2771943, 3721139898170903147426611722), (2774137, 7291444965182274579340802),
    (2776695, 476017034920378961121428506140), (2778859, 21817556111131869775796238),
    (2781069, 2446260064232339311957008), (2783643, 794141057093571798713380373002),
    (2785855, 12155555953666447498806798), (2788399, 1431680102358263493893128849934),
    (2790975, 162184671184168262605079975964), (2793009, 66187069735173935465988),
    (2795427, 1254893631550769547341860870), (2797449, 85482647213294534004234),
    (2799895, 631068944655572013473464844), (2801913, 113558445348491774264836),
    (2804139, 19371368820609924239333380), (2806183, 37890334605392657779214),
    (2808423, 29042628092350153353069574), (2810649, 12202632175712126837982724),
    (2813049, 4961488638503886514583635474), (2815243, 9690851302065710923123724),
    (2817477, 16953482017263848849673222), (2819713, 31451219321952355372634630),
    (2821953, 43625258895711618998602252), (2824173, 7281963777316816043509252),
    (2826555, 631182392274608069821477380), (2828967, 4337654434819290295962043410),
    (2831599, 1110439497165429653413949474318), (2833633, 28409429846800804878342),
    (2836237, 951369075968549319273244397570), (2838457, 7300926593894413081383426),
    (2840677, 26605924314720731306525190), (2842933, 9728370247873181648815622),
    (2845353, 5592519619618273861336171012), (2847213, 147862756945425734154),
    (2849659, 1245203594359920287033723910), (2851869, 17095300295218075785764358),
    (2854305, 4369076949851674979745532428), (2856349, 56891058577004882428440),
    (2858569, 12099589095661923573568518), (2860635, 132265317868824291184132),
    (2862879, 12146038578766851877903876), (2865493, 1427975953129587947726524910604)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk34 (m : ℕ) (ha : 2865494 ≤ m) (hb : m ≤ 3052645) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (2867929, 7444593642499726359596238344), (2870553, 479709047408360974419281317392),
    (2872977, 8672871941757813939925031440), (2875023, 57000876052397110854166),
    (2877267, 21779997375461009524135948), (2879695, 4340128990308067550080402958),
    (2882145, 3721121118665974980959011870), (2884623, 3109366837828528032914736646),
    (2886895, 2465112924879770416842242), (2889147, 12212114523865646488489996),
    (2891215, 85372255546585119065102), (2893305, 47334492797073263955460),
    (2895739, 4340100545432637786314379278), (2897985, 12184037860502759287163932),
    (2900059, 38001592649941594277894), (2902317, 7319742271163022491129862),
    (2904595, 12184001107752126026876430), (2907213, 1590146098276405102730869345290),
    (2909515, 7282147804480120585723394), (2911755, 29024107561311109684801548),
    (2914023, 9690444030292391460089862), (2916489, 5599763324835948457328643076),
    (2918955, 4337663805189918499639791108), (2921025, 47334494499177391982098),
    (2923087, 9668689661283182973452), (2925355, 2437110475224541320056840),
    (2927593, 12202632180785256310770690), (2929863, 14592297046446691956304396),
    (2932339, 6201874494837189929339586056), (2934783, 1254893409616190270901591574),
    (2937433, 1427352260559570268984912777734), (2939529, 9558009205653897348618),
    (2941827, 9747077263411432686749190), (2944099, 14516739618448525593805850),
    (2946363, 38732887941162714657858054), (2948475, 28519534980754117756420),
    (2950995, 631087759902179442252973590), (2953813, 122019429113299492750008884004870),
    (2955903, 37889912395195165704714), (2958165, 24377040397261565202149892),
    (2960263, 113448200580959143200774), (2962377, 9851140624108751031312),
    (2965033, 1903340073807186921273605103110), (2967357, 19371368818907888694330892),
    (2969817, 1252485003714220724058854446), (2972265, 640778573153877293616465930),
    (2974575, 26634331577762096918303242), (2976687, 19111845239079565396486),
    (2978973, 19428074686086126722354710), (2981259, 2474594689267338889006128),
    (2983363, 141708323160964953675782), (2985463, 57000584437689842404376),
    (2987965, 6811116476129296156830074382), (2990419, 9291898371686862102242525714),
    (2992729, 7272592251458124652615686), (2994825, 56707032491221601094162),
    (2997297, 3104540763604691771846300170), (2999815, 3725947266963351105364427784),
    (3002113, 4873668840066193568962566), (3004227, 28629779724131683665448),
    (3006715, 1262137484055279139869426702), (3009367, 3967005490148080115888501687810),
    (3011883, 3102160654147921776260548630), (3014185, 4920854319988580307569154),
    (3016675, 1900450610086769716453704204), (3018589, 221796654390571304456),
    (3020493, 110830778728531234320), (3022819, 19456188535682071873587726),
    (3024937, 56854598008332601394178), (3027283, 2465186131467771317454854),
    (3030145, 122175419144653411455114905914370), (3032449, 7263405627650745619712006),
    (3034947, 4975957710867007905949287958), (3037627, 2061794169509800802721607196678),
    (3039927, 4958706606499842820278790), (3042603, 159704021699194412407028455446),
    (3044745, 28445174360690058462724), (3047247, 3726089158453514156767842310),
    (3049947, 476621620611284732105825061382), (3052645, 792915159272994103092045023244)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk35 (m : ℕ) (ha : 3052646 ≤ m) (hb : m ≤ 3244917) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (3055327, 161558495090088806544279209498), (3057447, 19443301168853228718610),
    (3059383, 258543227984954262530), (3061927, 623844019372360727401857542),
    (3064587, 797876581170746704620727042570), (3066513, 184616068338374149132),
    (3068869, 7300816197150149305569294), (3071203, 7395336740137834679634956),
    (3073959, 951983153321509699248230367760), (3076365, 4845258985187840216010244),
    (3078717, 7310629723140537503319568), (3080883, 47260994044531669603864),
    (3082995, 28521694459086166688278), (3085543, 10529753665907700646141102086),
    (3087897, 14592150046700881784868870), (3090225, 14668002772922912054054404),
    (3092559, 12099035846490712756191748), (3094705, 28445744620196915192834),
    (3097047, 4864186351179566797951516), (3099399, 14535704739224167255902726),
    (3101725, 16944073743795763327009292), (3104413, 1908306341000231037650653413930),
    (3106765, 7319853813499539744752648), (3109303, 3111850876239691973728538124),
    (3112233, 527661428973727829848698323863050), (3114363, 56742619374846413114902),
    (3116745, 7263222311436143506884108), (3118885, 66521700700476810986504),
    (3121225, 14535962708232169807283220), (3123595, 9690665393484045234867212),
    (3125775, 28851140650799794097674), (3127933, 19148158888774960808490),
    (3130293, 2465223311510622255055902), (3132627, 14592333940522090521563142),
    (3135019, 17085632762990727423984134), (3137563, 7449457682138816340810793986),
    (3139719, 28409715842986374858244), (3142269, 1866685468807365941268972060),
    (3144817, 3097353137497792107439593480), (3147199, 14705634130822301099625480),
    (3149767, 1240575157542700692239813652), (3152149, 12145964213086835710493190),
    (3154369, 9555703351658324559878), (3156925, 4340063394405013144659691532),
    (3159645, 1586427461713528322681865637404), (3161575, 74371885772000596494),
    (3163557, 184901481782680094218), (3166165, 3721177713131563028995770882),
    (3168907, 953218722991652682688191661082), (3171667, 952602236898876554980583280140),
    (3174025, 16944847500441807992784392), (3176415, 16953702079467199377052164),
    (3178833, 7291444965182163244155396), (3181569, 480961513188836249355277441030),
    (3183949, 14582781838897820071627278), (3186345, 14554555008091708016690194),
    (3188925, 645604573732050875248149522), (3191323, 7291445252299790780335106),
    (3194065, 3012532006344180077523326470688), (3196855, 165272305579030503990001272332),
    (3199029, 113374122568411788217860), (3201795, 792907877162805982856648986642),
    (3203737, 77394935757669925890), (3206167, 7272592391056536040903176),
    (3208777, 1869027799764592189732165638), (3211359, 655285055224614992722532868),
    (3213769, 7301221451878132301174790), (3215973, 85150459444218106484742),
    (3218565, 623872279496044591348717074), (3220539, 148727441519627209734),
    (3222925, 7263221453500380368474120), (3225135, 113447911233427704251908),
    (3227757, 3735628043889805583954609158), (3230359, 3721102524066475912666808838),
    (3232959, 3726003898178872872064517650), (3235377, 7272481568728706090927638),
    (3237589, 18927658156215434348040), (3239965, 14535667421265157888542222),
    (3242335, 14592998023295515499301890), (3244917, 1876338133331570995487311882)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk36 (m : ℕ) (ha : 3244918 ≤ m) (hb : m ≤ 3441897) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (3247509, 8675270719316743286728955914), (3250119, 1869065541801278278565233156),
    (3252325, 103929389596023888024084), (3254755, 7348408653303709550251010),
    (3257163, 2446592536262692621910532), (3259983, 954471151103158773720657298444),
    (3262383, 29052406307869853449847814), (3265015, 1861812061248703077529295874),
    (3267607, 3119085357802141879506831372), (3270183, 9316029958983533855031560196),
    (3272583, 14535628941381851395003414), (3275377, 1903340083104200130599997016596),
    (3278035, 3718712748075615164754560520), (3280473, 9690628936257991080151044),
    (3283093, 7430115273555750053864413190), (3285295, 9518952863871466873364),
    (3287715, 14516665682305800295026204), (3289957, 47261284535520975389190),
    (3292365, 4864260715172984070343702), (3294823, 14516629220591497029092354),
    (3297055, 66225974084944297462274), (3299263, 28703575723018771891202),
    (3302103, 159701547104941451021912640012), (3304537, 4873557008925518066878512),
    (3306553, 37330343917034806274), (3308989, 17000667346350729465039368),
    (3311827, 794762350480629981091830303750), (3314233, 16944516326020005080466434),
    (3316875, 638341278646394319629059602), (3319537, 623834167947453506456262668),
    (3321969, 21779923590740852214994948), (3324607, 9306320478492652800498206210),
    (3327225, 1869037169992288280347020298), (3329655, 14639373856207733243774512),
    (3332287, 1881173651849294117034137606), (3335095, 477228350553308595871540446734),
    (3337347, 94558876512817351102986), (3339567, 66224244711526295277072),
    (3342019, 14516629799297469120781838), (3344269, 28704000171881933047814),
    (3346503, 94631949668571251346954), (3348949, 9690628209504968673985556),
    (3351187, 56707024062374186714630), (3353209, 74660681245555819014),
    (3355639, 24225888067929682590695954), (3358033, 5043820170767123605754370),
    (3360685, 1254940817599278044035417608), (3363115, 24292259594405128540660748),
    (3365593, 9699926093580074597749250), (3367825, 28482928034115778904588),
    (3370257, 41216851851527594634777100), (3372727, 2503260212911546237850630),
    (3375387, 3716285525349102637927893522), (3377857, 21836666205600957786884610),
    (3380085, 66224101152845621364258), (3382335, 9777211795395030946314),
    (3384589, 37853156851733718763526), (3386853, 19001447384267003527684),
    (3389335, 19409037213863091374262804), (3391609, 19258689617299964953614),
    (3394047, 7367152419356161865418246), (3396673, 8058756551607767454294738452),
    (3399295, 4352275065340636611093857288), (3401545, 19591165040642945975304),
    (3403839, 9740027814059317527558), (3406657, 2379985683819413398866214520850),
    (3409135, 14516998014154949246983682), (3411595, 4920743922136035186051114),
    (3414283, 3097315395030440637264692226), (3416949, 1245231447074493170788472338),
    (3419403, 14563963999916833521671686), (3422095, 6201817826438291566709050388),
    (3424377, 56853016116781341871120), (3426649, 28703425413182218699790),
    (3429295, 6832952736218303602153364994), (3431995, 2480829155828217630897735170),
    (3434275, 56779368778463165023752), (3436537, 9630070753518525484550),
    (3439197, 1245306968614418852887661062), (3441897, 11787064631288435533242568716)] (by decide) ha hb (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem intervalChunk37 (m : ℕ) (ha : 3441898 ≤ m) (hb : m ≤ 3595587) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card :=
  checkBlocks_sound [
    (3444795, 476000043919998558440125892100), (3447459, 8668083572244253765752332806),
    (3450147, 1859432135253978153621261318), (3453013, 170843007790406586494415670274),
    (3455515, 4986892943761634807120904), (3458197, 4959080121781843110187109382),
    (3460657, 7319852948808334016257538), (3462943, 9555848619134652910094),
    (3465847, 1427347311557545454708749238790), (3468553, 631144502233871331797370392),
    (3471237, 2488007338216013306650563606), (3473727, 7414263676579006762058758),
    (3476155, 7367003116573253407481358), (3478659, 12127111492600886507080708),
    (3481143, 7291666759017371472628746), (3483429, 28372252642889022440964),
    (3486123, 3742862783273772734992221712), (3488595, 14667781987898426858280964),
    (3491095, 4864591889643173648401428), (3493347, 170706891929530263143946),
    (3495619, 28518817219597899006996), (3497887, 37964409805578481830920),
    (3500145, 132374562826295633118748), (3503035, 167138962528591684702482859022),
    (3505543, 9775667846610318025690124), (3507817, 19039926132903868763142),
    (3510543, 9918055943218805537478804486), (3513447, 476614178863405154248425604108),
    (3515709, 132337954175483325058564), (3518223, 4949077256340071875086340),
    (3520495, 28408423318663708804104), (3522769, 19111694944756334594574),
    (3525487, 4369114913247607494244958726), (3528247, 1869037280672706585697321986),
    (3530995, 1252485113102721534719821314), (3533527, 24207184652460772467279362),
    (3535813, 75816558372052040681496), (3538123, 56705726456100490055174),
    (3540417, 19038338059966723000342), (3542959, 24197443185212338408392710),
    (3545269, 19332340359783216580104), (3547563, 123077542842019108754436),
    (3549643, 112843324794832427010), (3551937, 85113714579256570681360),
    (3554665, 4973530343443208212351946754), (3557163, 29033221259431450442469910),
    (3559899, 1861840284767698837323257350), (3562419, 16953518187928714318318608),
    (3565143, 6194649386099836741616799750), (3567877, 4340091137592599366101896212),
    (3570579, 7432542163534938834662195728), (3572875, 56816697978922432595474),
    (3575835, 1430446987949469638734044202500), (3578187, 56742762933544165312012),
    (3580693, 2465408644192311903519794), (3583635, 318786570412388062821143938582),
    (3586815, 40882355700973222160930719663620), (3589717, 1114786794893247857411878552082),
    (3592825, 487109608117983980144078268533778), (3595587, 8053882737499591714925577738)] (by decide) ha hb (by decide +kernel)

theorem medium_count (m : ℕ) (ha : 10000 ≤ m) (hb : m ≤ 3595587) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card := by
  by_cases h0 : m ≤ 13747
  · exact intervalChunk0 m (by omega) h0
  by_cases h1 : m ≤ 19537
  · exact intervalChunk1 m (by omega) h1
  by_cases h2 : m ≤ 28383
  · exact intervalChunk2 m (by omega) h2
  by_cases h3 : m ≤ 41109
  · exact intervalChunk3 m (by omega) h3
  by_cases h4 : m ≤ 58107
  · exact intervalChunk4 m (by omega) h4
  by_cases h5 : m ≤ 79345
  · exact intervalChunk5 m (by omega) h5
  by_cases h6 : m ≤ 104647
  · exact intervalChunk6 m (by omega) h6
  by_cases h7 : m ≤ 134335
  · exact intervalChunk7 m (by omega) h7
  by_cases h8 : m ≤ 169309
  · exact intervalChunk8 m (by omega) h8
  by_cases h9 : m ≤ 209617
  · exact intervalChunk9 m (by omega) h9
  by_cases h10 : m ≤ 256489
  · exact intervalChunk10 m (by omega) h10
  by_cases h11 : m ≤ 307519
  · exact intervalChunk11 m (by omega) h11
  by_cases h12 : m ≤ 363525
  · exact intervalChunk12 m (by omega) h12
  by_cases h13 : m ≤ 424543
  · exact intervalChunk13 m (by omega) h13
  by_cases h14 : m ≤ 490833
  · exact intervalChunk14 m (by omega) h14
  by_cases h15 : m ≤ 563353
  · exact intervalChunk15 m (by omega) h15
  by_cases h16 : m ≤ 642787
  · exact intervalChunk16 m (by omega) h16
  by_cases h17 : m ≤ 727687
  · exact intervalChunk17 m (by omega) h17
  by_cases h18 : m ≤ 816837
  · exact intervalChunk18 m (by omega) h18
  by_cases h19 : m ≤ 912795
  · exact intervalChunk19 m (by omega) h19
  by_cases h20 : m ≤ 1013829
  · exact intervalChunk20 m (by omega) h20
  by_cases h21 : m ≤ 1120477
  · exact intervalChunk21 m (by omega) h21
  by_cases h22 : m ≤ 1232385
  · exact intervalChunk22 m (by omega) h22
  by_cases h23 : m ≤ 1350019
  · exact intervalChunk23 m (by omega) h23
  by_cases h24 : m ≤ 1474243
  · exact intervalChunk24 m (by omega) h24
  by_cases h25 : m ≤ 1604979
  · exact intervalChunk25 m (by omega) h25
  by_cases h26 : m ≤ 1742965
  · exact intervalChunk26 m (by omega) h26
  by_cases h27 : m ≤ 1887495
  · exact intervalChunk27 m (by omega) h27
  by_cases h28 : m ≤ 2034685
  · exact intervalChunk28 m (by omega) h28
  by_cases h29 : m ≤ 2185857
  · exact intervalChunk29 m (by omega) h29
  by_cases h30 : m ≤ 2346085
  · exact intervalChunk30 m (by omega) h30
  by_cases h31 : m ≤ 2512719
  · exact intervalChunk31 m (by omega) h31
  by_cases h32 : m ≤ 2686209
  · exact intervalChunk32 m (by omega) h32
  by_cases h33 : m ≤ 2865493
  · exact intervalChunk33 m (by omega) h33
  by_cases h34 : m ≤ 3052645
  · exact intervalChunk34 m (by omega) h34
  by_cases h35 : m ≤ 3244917
  · exact intervalChunk35 m (by omega) h35
  by_cases h36 : m ≤ 3441897
  · exact intervalChunk36 m (by omega) h36
  exact intervalChunk37 m (by omega) hb

open Real

private theorem logarithm_bounds {x : ℝ} (hx : 1000000 ≤ x) :
    10 ≤ log x ∧ (log x)^2 ≤ x/1000 := by
  have hx0 : 0 < x := by linarith
  have hlower : 10 ≤ log x := by
    calc
      _ ≤ log ((2:ℝ)^19) := by rw [log_pow]; norm_num; linarith [log_two_gt_d9]
      _ ≤ _ := log_le_log (by positivity) (by norm_num; linarith)
  have hsmall : log (1000000:ℝ) ≤ 20 := by
    calc
      _ ≤ log ((2:ℝ)^20) := log_le_log (by norm_num) (by norm_num)
      _ ≤ _ := by
        rw [log_pow]
        norm_num
        linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  let z := Real.sqrt (x/1000000)
  have hz2 : z^2 = x/1000000 := Real.sq_sqrt (by positivity)
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have hzone : 1 ≤ z := by
    by_contra! hlt
    have hsq : z^2 < 1^2 := (sq_lt_sq₀ hz0 zero_le_one).2 hlt
    linarith
  have he : log x = log 1000000 + 2*log z := by
    have heq : x = 1000000*z^2 := by linarith
    conv_lhs => rw [heq]
    rw [log_mul (by norm_num) (by positivity), log_pow]
    norm_num
  have hlu : log x ≤ 20*z := by
    linarith [log_le_sub_one_of_pos (show 0 < z by linarith)]
  have hsq : (log x)^2 ≤ (20*z)^2 := by gcongr
  exact ⟨hlower, by nlinarith⟩

private theorem theta_diff_le (m L : ℕ) :
    Chebyshev.theta (↑(m+L) : ℝ) - Chebyshev.theta (m : ℝ) ≤
      ((intervalPrimes m L).card + 3 : ℝ)*log (↑(m+L) : ℝ) := by
  classical
  let S := Nat.primesLE (m+L) \ Nat.primesLE m
  have hs : Nat.primesLE m ⊆ Nat.primesLE (m+L) := by
    intro p hp
    obtain ⟨hpm, hpr⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨by omega, hpr⟩
  have he : Chebyshev.theta (↑(m+L) : ℝ) - Chebyshev.theta (m:ℝ) = ∑ p ∈ S, log p := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
    exact (eq_sub_of_add_eq (Finset.sum_sdiff hs)).symm
  have hsub : S ⊆ intervalPrimes m L ∪ Finset.Icc (m+1) (m+3) := by
    intro p hp
    obtain ⟨hpl, hpm⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpl, hprime⟩ := Nat.mem_primesLE.mp hpl
    have hm' : m < p := by
      by_contra! hm'
      exact hpm (Nat.mem_primesLE.mpr ⟨hm', hprime⟩)
    by_cases h : m+4 ≤ p
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h,hpl⟩,hprime⟩)
    · exact Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
  have hcard := (Finset.card_le_card hsub).trans
    (Finset.card_union_le (intervalPrimes m L) (Finset.Icc (m+1) (m+3)))
  simp only [Nat.card_Icc] at hcard
  have hcard' : (S.card : ℝ) ≤ (intervalPrimes m L).card+3 := by
    exact_mod_cast (show S.card ≤ (intervalPrimes m L).card+3 by omega)
  rw [he]
  calc
    _ ≤ ∑ _p ∈ S, log (↑(m+L) : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpl, hprime⟩ := Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1
      exact log_le_log (by exact_mod_cast hprime.pos) (by exact_mod_cast hpl)
    _ = (S.card : ℝ)*log (↑(m+L) : ℝ) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard' (log_natCast_nonneg _)

/-- Dusart's explicit theta estimate gives the prime count required by the cube-root argument. -/
theorem interval_of_theta
    (thetaBound : ∀ x : ℝ, 3594641 ≤ x →
      |Chebyshev.theta x - x| ≤ x/(5*(log x)^2))
    (m : ℕ) (hm : 3594641 ≤ m) :
    ∃ L : ℕ, 3*L^2/m+6 < (intervalPrimes m L).card := by
  let x : ℝ := m
  let t : ℝ := log x
  let L : ℕ := ⌊x/(6*t)⌋₊
  let l : ℝ := L
  let y := x+l
  have hmx : 3594641 ≤ x := by
    dsimp [x]
    exact_mod_cast hm
  have hx : 0 < x := by linarith
  have hxy : x ≤ y := by
    dsimp [y,l]
    exact le_add_of_nonneg_right (Nat.cast_nonneg L)
  have hy : 0 < y := hx.trans_le hxy
  obtain ⟨ht, htsq⟩ := logarithm_bounds (show 1000000 ≤ x by linarith)
  change 10 ≤ t at ht
  change t^2 ≤ x/1000 at htsq
  have ht0 : 0 < t := by linarith
  have hl0 : 0 ≤ l := by dsimp [l]; positivity
  have hl : l ≤ x/(6*t) := Nat.floor_le (by positivity)
  have hl' : x/(6*t) < l+1 := Nat.lt_floor_add_one _
  have h60 : l ≤ x/60 := hl.trans (div_le_div_of_nonneg_left hx.le (by norm_num) (by linarith))
  have hlog₁ : t ≤ log y := log_le_log hx hxy
  have hlog₂ : log y ≤ (11/10)*t := by
    have heq : log (y/x) = log y - t := log_div hy.ne' hx.ne'
    have hb : y/x ≤ 61/60 := (div_le_iff₀ hx).mpr (by dsimp [y]; linarith)
    linarith [log_le_sub_one_of_pos (div_pos hy hx)]
  have herr : x/(5*t^2)+y/(5*(log y)^2) ≤ x/(24*t) := by
    calc
      _ ≤ x/(5*t^2)+y/(5*t^2) := by gcongr
      _ = (x+y)/(5*t^2) := by ring
      _ ≤ ((25/12)*x)/(5*t^2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        dsimp [y]
        linarith
      _ = (x/(24*t))*(10/t) := by field_simp; ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) ((div_le_iff₀ ht0).mpr (by simpa using ht))
  have hcount : (3*l^2/x+9)*log y ≤ 11/120*(x/t)+99/10*t := by
    have hlog0 : 0 ≤ log y := by linarith
    calc
      _ ≤ (3*(x/(6*t))^2/x+9)*((11/10)*t) := by gcongr
      _ = _ := by field_simp; ring
  have ht_small : t ≤ x/(1000*t) := by
    apply (le_div_iff₀ (by positivity : 0 < 1000*t)).mpr
    linarith only [show t*(1000*t) = 1000*t^2 by ring, htsq]
  have hdiff : (3*l^2/x+9)*log y < Chebyshev.theta y-Chebyshev.theta x := by
    have ha := (abs_le.mp (thetaBound x hmx)).2
    have hb := (abs_le.mp (thetaBound y (hmx.trans hxy))).1
    have hlo : l-x/(24*t) ≤ Chebyshev.theta y-Chebyshev.theta x := by
      change Chebyshev.theta x-x ≤ x/(5*t^2) at ha
      dsimp [y] at hb ⊢
      linarith
    have he : x/(6*t) = (x/t)/6 := by ring
    have he' : x/(24*t) = (x/t)/24 := by ring
    have he'' : x/(1000*t) = (x/t)/1000 := by ring
    linarith
  have hc := theta_diff_le m L
  rw [Nat.cast_add] at hc
  change Chebyshev.theta y-Chebyshev.theta x ≤ _ at hc
  change _ ≤ ((intervalPrimes m L).card + 3 : ℝ)*log y at hc
  have hr : 3*l^2/x+9 < ((intervalPrimes m L).card + 3 : ℝ) :=
    lt_of_mul_lt_mul_right (hdiff.trans_le hc) (show 0 ≤ log y by linarith)
  have hq : (↑(3*L^2/m : ℕ) : ℝ) ≤ 3*l^2/x := by
    apply (le_div_iff₀ hx).mpr
    change (↑(3*L^2/m : ℕ) : ℝ)*(m : ℝ) ≤ 3*(L : ℝ)^2
    exact_mod_cast Nat.div_mul_le_self (3*L^2) m
  refine ⟨L, ?_⟩
  exact_mod_cast (show (↑(3*L^2/m : ℕ) : ℝ)+6 < (intervalPrimes m L).card by linarith)

end CubeWitness

private theorem exists_cube_root (n : ℕ) : ∃ m : ℕ, m^3 ≤ n ∧ n < (m+1)^3 := by
  induction n with
  | zero => exact ⟨0, by decide, by decide⟩
  | succ n ih =>
    obtain ⟨m, hlo, hhi⟩ := ih
    by_cases h : n+1 < (m+1)^3
    · exact ⟨m, by omega, h⟩
    · have hlt : (m+1)^3 < (m+1+1)^3 := Nat.pow_lt_pow_left (by omega) (by decide)
      exact ⟨m+1, by omega, by omega⟩

/-- The portion of the odd digit-sum sieve above the kernel-checked cutoff. -/
def H1 : Prop :=
  ∀ n : ℕ, 100000000 < n → n < 10000^3 → n % 2 = 1 →
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ n+1 ∧ p ≤ (p.digits n).sum

/-- Dusart's explicit bound for the Chebyshev theta function. -/
def H2 : Prop :=
  ∀ x : ℝ, 3594641 ≤ x → |Chebyshev.theta x - x| ≤ x/(5*(Real.log x)^2)

theorem main : H1 → H2 → type_of% @OeisA195441.conjecture := by
  intro finiteRange thetaBound
  ext n
  change (1 ≤ n ∧ OeisA195441.a (n-1) = UniqueFactorizationMonoid.radical (n+1)) ↔
    n ∈ ({3,5,8,9,11,27,29,35,59} : Finset ℕ)
  by_cases hs : n ≤ 59
  · exact BernoulliWitness.finite_cases n hs
  constructor
  · rintro ⟨hn, heq⟩
    exfalso
    have forces (p : ℕ) := @BernoulliWitness.solution_forces_prime_divisors n hn heq p
    by_cases ho : n % 2 = 1
    · have hw : ∃ p : ℕ, p.Prime ∧ ¬p ∣ n+1 ∧ p ≤ (p.digits n).sum := by
        by_cases hbounded : n ≤ 100000000
        · exact DigitSieve.boundedWitness (by omega) hbounded ho
        by_cases hlower : n < 10000^3
        · exact finiteRange n (by omega) hlower ho
        obtain ⟨m, hlo, hhi⟩ := exists_cube_root n
        have hm : 10000 ≤ m := by
          by_contra! h
          have hpow := Nat.pow_le_pow_left (show m+1 ≤ 10000 by omega) 3
          omega
        obtain ⟨L, hL⟩ : ∃ L : ℕ, 3*L^2/m+6 < (CubeWitness.intervalPrimes m L).card := by
          by_cases h : m < 3594641
          · exact CubeWitness.medium_count m hm (by omega)
          · exact CubeWitness.interval_of_theta thetaBound m (by omega)
        exact CubeWitness.witness_of_interval (by omega) hlo hhi hL
      obtain ⟨p, hp, hmiss, hd⟩ := hw
      exact hmiss (forces p hp hd)
    · exact BernoulliWitness.exclude_even (by omega) (by omega) forces
  · intro hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    omega

end OMA.R_OeisA195441_conjecture_R2
