import FormalConjectures.ErdosProblems.«373»

-- Reduction Erdos373.erdos_373.R1 of Erdős problem 373
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 373 from a weak abc bound for consecutive integers

The equation `n! = a₁! a₂! ⋯ a_k!` with `n - 1 > a₁ ≥ a₂ ≥ ⋯ ≥ a_k ≥ 2` has finitely many
solutions (F. Luca, *On factorials which are products of factorials*, Math. Proc. Cambridge
Philos. Soc. 143 (2007), proved this under the abc conjecture).

* `H1` (weak abc for consecutive integers, open): for some exponent `E`, all large `m` satisfy
  `m + 1 ≤ rad(m (m + 1)) ^ E`. The abc conjecture gives this with `E = 2`; `H1` only asks for
  some power, so it is much weaker than abc.
* `H2` (primes in short intervals, known): for every `δ > 0` and all large `n` there is a prime in
  `(n, (1 + δ) n]`. This follows from the prime number theorem. It is word for word `H1` of
  `Erdos30.erdos_30.variants.singer.R1`, which is proved upstream.

Write `k = n - a₁`, so `(a₁ + 1) ⋯ n = a₂! ⋯ a_k!`.

* Large gap, `k > log n`: impossible for large `n`. This is Erdős's argument (a 2-adic bound, the
  smooth binomial coefficient and `H2`); the lemmas `prod_prime` to `large_gap` are taken from the
  merged proof of `Erdos373.erdos_373.variants.of_lower_bound` (namespace `Fact373` there), with
  the prime factor hypothesis replaced by the case assumption `k > log n`.
* Small gap, `k ≤ log n`: every prime dividing a number in the block `(a₁, n]` is at most `a₂`, so
  the product of the radicals of the block divides `k! · a₂#` (lemma `rad_prod_dvd`). `H1` for the
  `k - 1` pairs of neighbours in the block gives `a₁ ^ (k - 1) ≤ (k! · 4 ^ a₂) ^ (2E)` (lemma
  `pair_bound`), hence `a₂ ≥ k log n / (12 E)`. But `a₂! ≤ n ^ k`, so `a₂ (log a₂ - 1) ≤ k log n`
  and `a₂` is bounded, which bounds `n` (lemma `endgame`).
-/

namespace OMA.R_Erdos373_erdos_373_R1

open Finset Filter
open scoped Nat Topology

/-- Weak abc for consecutive integers: for some `E`, only finitely many `m` have
`rad(m (m + 1)) ^ E < m + 1`. -/
def H1 : Prop :=
  ∃ E : ℕ, {m : ℕ | (∏ p ∈ (m * (m + 1)).primeFactors, p) ^ E < m + 1}.Finite

/-- Primes in short intervals (a consequence of the prime number theorem). -/
def H2 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ p : ℕ, p.Prime ∧ n < p ∧ (p : ℝ) ≤ (1 + δ) * (n : ℝ)

/- ## Large gap: lemmas from the merged proof of `variants.of_lower_bound` -/

lemma prod_prime {p : ℕ} (hp : p.Prime) (l : List ℕ)
    (hd : p ∣ (l.map Nat.factorial).prod) : ∃ a ∈ l, p ≤ a := by
  induction l with
  | nil => simp [hp.not_dvd_one] at hd
  | cons a l ih =>
    simp only [List.map_cons,List.prod_cons,hp.dvd_mul] at hd
    rcases hd with h | h
    · exact ⟨a,by simp,hp.dvd_factorial.mp h⟩
    · obtain ⟨b,hb,hp⟩ := ih h
      exact ⟨b,by simp [hb],hp⟩

lemma twor (r : ℕ) : 2^r ∣ (2*r)! := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, show 2*(r+1) = 2*r+2 by omega]
    simpa using (Nat.mul_dvd_mul ih (dvd_refl 2)).trans (Nat.factorial_mul_factorial_dvd_factorial_add (2*r) 2)

lemma le_tail {n k b : ℕ} (hk : k ≤ n) (hd : b ! ∣ n.choose k * k !) :
    b ≤ k + 2*(Nat.log 2 n) + 1 := by
  by_contra! h
  let r := Nat.log 2 n + 1
  have hb : k+2*r ≤ b := by dsimp [r]; omega
  have hdiv : (2^r)*k ! ∣ n.choose k * k ! := by
    apply dvd_trans _ hd
    refine (Nat.mul_dvd_mul (twor r) (dvd_refl (k !))).trans ?_
    exact (Nat.factorial_mul_factorial_dvd_factorial_add (2*r) k).trans
      (Nat.factorial_dvd_factorial (by omega))
  have hpow : 2^r ∣ n.choose k := (Nat.dvd_of_mul_dvd_mul_right k.factorial_pos hdiv)
  have hm := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (Nat.choose_pos hk).ne').mp hpow
  have hsm : (n.choose k).factorization 2 ≤ Nat.log 2 n := Nat.factorization_choose_le_log
  dsimp [r] at hm
  omega

lemma two_log : ∀ᶠ n : ℕ in atTop, 2*(Nat.log 2 n : ℝ)+1 ≤ 3*Real.log n := by
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_gt_atTop 20
  filter_upwards [hlog] with n hn
  have h := Real.natLog_le_logb n 2
  simp only [Real.logb,Nat.cast_ofNat] at h
  have h' := (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mp h
  change (20:ℝ) < Real.log n at hn
  nlinarith [Real.log_two_gt_d9,mul_le_mul_of_nonneg_left (le_of_lt Real.log_two_gt_d9)
    (Nat.cast_nonneg (Nat.log 2 n) : (0:ℝ) ≤ Nat.log 2 n)]

lemma choose_smooth {n k z : ℕ} (hn : 0 < n) (hk : k ≤ n)
    (h : ∀ p ∈ (n.choose k).primeFactors, p ≤ z) :
    n.choose k ≤ n ^ z.primeCounting := by
  have hs : (n.choose k).primeFactors ⊆ z.primesLE := fun p hp =>
    Nat.mem_primesLE.mpr ⟨h p hp,Nat.prime_of_mem_primeFactors hp⟩
  calc n.choose k = ∏ p ∈ (n.choose k).primeFactors, p ^ (n.choose k).factorization p :=
         Nat.prod_primeFactors_pow_factorization (Nat.choose_pos hk).ne'
       _ ≤ ∏ _p ∈ (n.choose k).primeFactors, n :=
         prod_le_prod' fun _ _ => Nat.pow_factorization_choose_le hn
       _ ≤ _ := by
         simp only [prod_const]
         apply Nat.pow_le_pow_right hn
         simpa using card_le_card hs

lemma log_choose {a k n : ℕ} (heq : k+a=n) (hk : 0 < k) (ha : 0<a)
    (hc : n.choose k ≤ n ^ (4*k).primeCounting) :
    (k:ℝ)*(Real.log a - Real.log k) ≤ ((4*k).primeCounting:ℝ)*Real.log n := by
  have hkN : k ≤ n := by omega
  have hp : 0 < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hkN
  have hpow : a^k ≤ n.choose k * k^k := by
    calc a^k ≤ (n+1-k)^k := Nat.pow_le_pow_left (by omega) _
         _ ≤ n.descFactorial k := Nat.pow_sub_le_descFactorial ..
         _ = k !*n.choose k := Nat.descFactorial_eq_factorial_mul_choose ..
         _ ≤ _ := by nlinarith [Nat.mul_le_mul_right (n.choose k) k.factorial_le_pow]
  have hposA : 0 < (a:ℝ) := by exact_mod_cast ha
  have hposK : 0 < (k:ℝ) := by exact_mod_cast hk
  have h1 := Real.log_le_log (pow_pos hposA k) (show (a:ℝ)^k ≤ (n.choose k:ℝ)*(k:ℝ)^k by exact_mod_cast hpow)
  have h2 := Real.log_le_log hp (show (n.choose k:ℝ) ≤ (n:ℝ)^(4*k).primeCounting by exact_mod_cast hc)
  rw [Real.log_mul hp.ne' (pow_pos hposK k).ne',Real.log_pow,Real.log_pow] at h1
  rw [Real.log_pow] at h2
  linarith

lemma pi_est : ∀ᶠ k : ℕ in atTop,
    ((4*k).primeCounting:ℝ)*Real.log k ≤ 12*k := by
  have hcast : Tendsto (fun k : ℕ => (4*k : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num)
  filter_upwards [hcast.eventually (Chebyshev.eventually_primeCounting_le (ε := 1) zero_lt_one),
    eventually_gt_atTop 1] with k h hk
  have hpos : 1 < (4*(k:ℝ)) := by
    have : (1:ℝ)<k := by exact_mod_cast hk
    linarith
  have h' : ((4*k).primeCounting:ℝ) ≤ (Real.log 4+1)*(4*k)/Real.log (4*k) := by
    have he : 4*(k:ℝ) = ((4*k:ℕ):ℝ) := by push_cast; rfl
    rwa [he,Nat.floor_natCast,← he] at h
  have hlow : Real.log k ≤ Real.log (4*(k:ℝ)) := by
    apply Real.log_le_log (by positivity)
    linarith [(Nat.cast_nonneg k : 0 ≤ (k:ℝ))]
  have h4 : Real.log 4 ≤ 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9]
  calc ((4*k).primeCounting:ℝ)*Real.log k ≤ ((4*k).primeCounting:ℝ)*Real.log (4*k) :=
         mul_le_mul_of_nonneg_left hlow (by positivity)
       _ ≤ _ := by nlinarith [(le_div_iff₀ (Real.log_pos hpos)).mp h',
          mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg k : 0 ≤ (k:ℝ))]

lemma analytic_impossible {a k n P : ℝ} (hk : 0 < k) (hP : 0 ≤ P) (hn : 0 ≤ n.log)
    (hπ : P * Real.log k ≤ 12*k) (h48 : 48 ≤ Real.log k)
    (hbound : k*(Real.log a - Real.log k) ≤ P*Real.log n)
    (hnle : Real.log n ≤ Real.log a + 1) (hgap : 100 + Real.log k ≤ Real.log a) : False := by
  have hquarter : P ≤ k/4 := by nlinarith [mul_le_mul_of_nonneg_left h48 hP]
  have hsmall : Real.log a - Real.log k ≤ Real.log n / 4 := by
    apply le_of_mul_le_mul_left (a := k) (by nlinarith [mul_le_mul_of_nonneg_right hquarter hn]) hk
  have hnk : Real.log n ≤ 2*Real.log k := by linarith
  nlinarith only [mul_le_mul_of_nonneg_left hnk hP,hπ,hbound,
    mul_le_mul_of_nonneg_left hgap hk.le,hk]

lemma prime_le_head {n a : ℕ} {l : List ℕ} (hp : n ! = ((a::l).map Nat.factorial).prod)
    (hs : (a::l).Pairwise (· ≥ ·)) {p : ℕ} (hpr : p.Prime) (hle : p ≤ n) : p ≤ a := by
  obtain ⟨b,hb,hpb⟩ := prod_prime hpr (a::l) (hp ▸ hpr.dvd_factorial.mpr hle)
  rcases List.mem_cons.mp hb with rfl | hb
  · exact hpb
  · exact hpb.trans ((List.pairwise_cons.mp hs).1 _ hb)

lemma tail_eq {n k a : ℕ} {l : List ℕ} (heq : k+a=n)
    (hprod : n ! = ((a::l).map Nat.factorial).prod) :
    n.choose k * k ! = (l.map Nat.factorial).prod := by
  have h := Nat.choose_mul_factorial_mul_factorial (show k ≤ n by omega)
  rw [show n-k=a by omega,hprod] at h
  simp only [List.map_cons,List.prod_cons] at h
  exact Nat.eq_of_mul_eq_mul_right a.factorial_pos (h.trans (mul_comm ..))

/-- For large `n`, a solution has `n - a₁ ≤ log n`. -/
lemma large_gap (primes : H2) :
    ∀ᶠ n : ℕ in atTop, ∀ (a : ℕ) (l : List ℕ), n ! = ((a::l).map Nat.factorial).prod →
      (a::l).Pairwise (· ≥ ·) → a < n - 1 → ((n - a : ℕ) : ℝ) ≤ Real.log n := by
  have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨K,hK⟩ := eventually_atTop.mp (pi_est.and (ht.eventually_ge_atTop 48))
  obtain ⟨X,hX⟩ := primes ((Real.exp 100)⁻¹) (by positivity)
  obtain ⟨p₀,hX₀,hprime₀⟩ := Nat.exists_infinite_primes X
  filter_upwards [two_log,ht.eventually_ge_atTop (K:ℝ),eventually_ge_atTop p₀,
    eventually_ge_atTop 3] with n htwo hlogN hp₀n hn a l hprod hs ha
  by_contra hcon
  have hlogk : Real.log n < ((n - a : ℕ) : ℝ) := not_le.mp hcon
  generalize hkdef : n - a = k at hlogk
  have heq : k+a=n := by omega
  have hk2 : 2 ≤ k := by omega
  have hap := prime_le_head hprod hs hprime₀ hp₀n
  obtain ⟨p,hp,hpa,hple⟩ := hX a (hX₀.trans hap)
  have hnp : n < p := by
    by_contra! hc
    exact hpa.not_ge (prime_le_head hprod hs hp hc)
  have hnR : (n:ℝ) < p := by exact_mod_cast hnp
  have heR : (k:ℝ)+a=n := by exact_mod_cast heq
  have hepos : 0 < Real.exp 100 := Real.exp_pos _
  have hgapN : (k:ℝ) ≤ a/(Real.exp 100) := by
    rw [div_eq_inv_mul]
    nlinarith
  have hkgap := (le_div_iff₀ hepos).mp hgapN
  have hkp : 0 < (k:ℝ) := by positivity
  have hap' : 0 < a := hprime₀.pos.trans_le hap
  have har : 0 < (a:ℝ) := by exact_mod_cast hap'
  have hgap := Real.log_le_log (mul_pos hkp hepos) hkgap
  rw [Real.log_mul hkp.ne' hepos.ne', Real.log_exp] at hgap
  have hone : 1 ≤ Real.exp 100 := Real.one_le_exp (by norm_num)
  have hnle : (n:ℝ) ≤ 2*a := by nlinarith [mul_le_mul_of_nonneg_left hone hkp.le]
  have hlogle := Real.log_le_log (show 0 < (n:ℝ) by positivity) hnle
  rw [Real.log_mul (by norm_num) har.ne'] at hlogle
  have htail := tail_eq heq hprod
  have hfac {p : ℕ} (hp : p.Prime) (hd : p ∣ n.choose k * k !) :
      (p:ℝ) ≤ (k:ℝ)+3*Real.log n := by
    obtain ⟨b,hb,hle⟩ := prod_prime hp l (htail ▸ hd)
    have hd' : b ! ∣ n.choose k * k ! := htail ▸ List.dvd_prod (List.mem_map.mpr ⟨b,hb,rfl⟩)
    have hnat := hle.trans (le_tail (by omega) hd')
    have hcast : (p:ℝ) ≤ k+2*(Nat.log 2 n : ℝ)+1 := by exact_mod_cast hnat
    linarith
  have hKk : K ≤ k := by
    change (K:ℝ) ≤ Real.log n at hlogN
    exact_mod_cast hlogN.trans hlogk.le
  obtain ⟨hpi,h48⟩ := hK k hKk
  have hchoose := choose_smooth (by omega : 0 < n) (by omega : k ≤ n) (z := 4*k) (by
    intro q hq
    have h := hfac (Nat.prime_of_mem_primeFactors hq)
      ((Nat.dvd_of_mem_primeFactors hq).trans (dvd_mul_right (n.choose k) (k !)))
    exact_mod_cast (show (q:ℝ) ≤ 4*k by linarith))
  apply analytic_impossible hkp (Nat.cast_nonneg (4*k).primeCounting) (Real.log_natCast_nonneg n)
    hpi h48 (log_choose heq (by omega) hap' hchoose) <;> linarith [Real.log_two_lt_d9]

/- ## Small gap: the radicals of the block -/

/-- The radical of `m` has `p`-adic valuation at most `1`, and `0` unless `p ∣ m`. -/
lemma rad_factorization_le (m p : ℕ) :
    (∏ q ∈ m.primeFactors, q).factorization p ≤ if p ∣ m then 1 else 0 := by
  rw [Nat.factorization_prod (fun q hq => (Nat.prime_of_mem_primeFactors hq).ne_zero),
    Finsupp.finsetSum_apply]
  have h : ∀ q ∈ m.primeFactors, q.factorization p = if q = p then 1 else 0 := by
    intro q hq
    rw [(Nat.prime_of_mem_primeFactors hq).factorization, Finsupp.single_apply]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq']
  by_cases hp : p ∈ m.primeFactors
  · simp [hp, Nat.dvd_of_mem_primeFactors hp]
  · simp [hp]

/-- A block of `k` consecutive integers has at most `k / p + 1` multiples of `p`. -/
lemma card_multiples_le (a k p : ℕ) (hp : 0 < p) :
    #{m ∈ Ioc a (a + k) | p ∣ m} ≤ k / p + 1 := by
  have h1 := Nat.Ioc_filter_dvd_card_eq_div (a + k) p
  have h2 := Nat.Ioc_filter_dvd_card_eq_div a p
  have hU : Ioc 0 (a + k) = Ioc 0 a ∪ Ioc a (a + k) :=
    (Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) (Nat.le_add_right _ _)).symm
  have hD : Disjoint ({m ∈ Ioc 0 a | p ∣ m}) ({m ∈ Ioc a (a + k) | p ∣ m}) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [mem_filter, mem_Ioc] at hx hx'
    omega
  rw [hU, Finset.filter_union, Finset.card_union_of_disjoint hD, h2] at h1
  have h3 := Nat.add_div (a := a) (b := k) hp
  split_ifs at h3 <;> omega

lemma pow_dvd_mul_factorial (p r : ℕ) (hp : 0 < p) : p ^ r ∣ (p * r)! := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, Nat.mul_succ]
    exact (Nat.mul_dvd_mul ih (Nat.dvd_factorial hp le_rfl)).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add (p * r) p)

lemma div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (k : ℕ) :
    k / p ≤ (k !).factorization p := by
  have h : p ^ (k / p) ∣ k ! :=
    (pow_dvd_mul_factorial p (k / p) hp.pos).trans
      (Nat.factorial_dvd_factorial (Nat.mul_div_le k p))
  exact (hp.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero k)).mp h

/-- If every prime dividing a member of the block `(a, a + k]` is at most `z`, then the product of
the radicals of the block divides `k! · z#`. -/
lemma rad_prod_dvd (a k z : ℕ)
    (hz : ∀ m ∈ Ioc a (a + k), ∀ q : ℕ, q.Prime → q ∣ m → q ≤ z) :
    (∏ m ∈ Ioc a (a + k), ∏ q ∈ m.primeFactors, q) ∣ k ! * primorial z := by
  have hrad : ∀ m ∈ Ioc a (a + k), (∏ q ∈ m.primeFactors, q) ≠ 0 := fun m _ =>
    Finset.prod_ne_zero_iff.mpr fun q hq => (Nat.prime_of_mem_primeFactors hq).ne_zero
  have hQ0 : (∏ m ∈ Ioc a (a + k), ∏ q ∈ m.primeFactors, q) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hrad
  have hR0 : k ! * primorial z ≠ 0 :=
    mul_ne_zero (Nat.factorial_ne_zero k) (primorial_pos z).ne'
  rw [← Nat.factorization_prime_le_iff_dvd hQ0 hR0]
  intro p hp
  rw [Nat.factorization_prod hrad, Finsupp.finsetSum_apply,
    Nat.factorization_mul (Nat.factorial_ne_zero k) (primorial_pos z).ne', Finsupp.add_apply]
  have hle : ∑ m ∈ Ioc a (a + k), (∏ q ∈ m.primeFactors, q).factorization p
      ≤ #{m ∈ Ioc a (a + k) | p ∣ m} := by
    rw [Finset.card_filter]
    exact Finset.sum_le_sum fun m _ => rad_factorization_le m p
  refine hle.trans ?_
  by_cases hc : #{m ∈ Ioc a (a + k) | p ∣ m} = 0
  · rw [hc]
    exact Nat.zero_le _
  · obtain ⟨m, hm⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc)
    rw [Finset.mem_filter] at hm
    have hpz := hz m hm.1 p hp hm.2
    have hdvd : p ∣ primorial z := by
      unfold primorial
      exact Finset.dvd_prod_of_mem (fun q => q)
        (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩)
    have h1 : 0 < (primorial z).factorization p :=
      hp.factorization_pos_of_dvd (primorial_pos z).ne' hdvd
    have h2 := div_le_factorization_factorial hp k
    have h3 := card_multiples_le a k p hp.pos
    omega

lemma rad_mul_succ (m : ℕ) (hm : m ≠ 0) :
    ∏ p ∈ (m * (m + 1)).primeFactors, p
      = (∏ p ∈ m.primeFactors, p) * ∏ p ∈ (m + 1).primeFactors, p := by
  have hco : Nat.Coprime m (m + 1) := by simp
  rw [Nat.primeFactors_mul hm (Nat.succ_ne_zero m), Finset.prod_union hco.disjoint_primeFactors]

/-- The weak abc bound for the `k - 1` pairs of neighbours of the block `(a, a + k]`. -/
lemma pair_bound {E N : ℕ}
    (hN : ∀ m, N ≤ m → m + 1 ≤ (∏ p ∈ (m * (m + 1)).primeFactors, p) ^ E)
    (a j z : ℕ) (haN : N ≤ a)
    (hz : ∀ m ∈ Ioc a (a + (j + 1)), ∀ q : ℕ, q.Prime → q ∣ m → q ≤ z) :
    a ^ j ≤ ((j + 1) ! * 4 ^ z) ^ (2 * E) := by
  have f1 : ∀ m : ℕ, 1 ≤ ∏ q ∈ m.primeFactors, q := fun m =>
    Finset.prod_pos fun q hq => (Nat.prime_of_mem_primeFactors hq).pos
  have hQ : (∏ m ∈ Ioc a (a + (j + 1)), ∏ q ∈ m.primeFactors, q) ≤ (j + 1) ! * 4 ^ z :=
    (Nat.le_of_dvd (Nat.mul_pos (Nat.factorial_pos _) (primorial_pos z))
      (rad_prod_dvd a (j + 1) z hz)).trans (Nat.mul_le_mul_left _ (primorial_le_four_pow z))
  have hA : (∏ m ∈ Ioc a (a + j), ∏ q ∈ m.primeFactors, q)
      ≤ ∏ m ∈ Ioc a (a + (j + 1)), ∏ q ∈ m.primeFactors, q :=
    Finset.prod_le_prod_of_subset_of_one_le' (Finset.Ioc_subset_Ioc_right (by omega))
      (fun m _ _ => f1 m)
  have hB : (∏ m ∈ Ioc a (a + j), ∏ q ∈ (m + 1).primeFactors, q)
      ≤ ∏ m ∈ Ioc a (a + (j + 1)), ∏ q ∈ m.primeFactors, q := by
    have hsh : (∏ m ∈ Ioc a (a + j), ∏ q ∈ (m + 1).primeFactors, q)
        = ∏ m ∈ Ioc (a + 1) (a + j + 1), ∏ q ∈ m.primeFactors, q := by
      rw [← Finset.image_add_right_Ioc, Finset.prod_image]
      intro x _ y _ h
      simpa using h
    rw [hsh]
    exact Finset.prod_le_prod_of_subset_of_one_le' (Finset.Ioc_subset_Ioc_left (by omega))
      (fun m _ _ => f1 m)
  calc a ^ j = ∏ _m ∈ Ioc a (a + j), a := by simp
    _ ≤ ∏ m ∈ Ioc a (a + j),
          ((∏ q ∈ m.primeFactors, q) * ∏ q ∈ (m + 1).primeFactors, q) ^ E := by
        apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
        intro m hm
        rw [mem_Ioc] at hm
        have h := hN m (by omega)
        rw [rad_mul_succ m (by omega)] at h
        omega
    _ = ((∏ m ∈ Ioc a (a + j), ∏ q ∈ m.primeFactors, q)
          * ∏ m ∈ Ioc a (a + j), ∏ q ∈ (m + 1).primeFactors, q) ^ E := by
        rw [Finset.prod_pow, Finset.prod_mul_distrib]
    _ ≤ ((∏ m ∈ Ioc a (a + (j + 1)), ∏ q ∈ m.primeFactors, q)
          * ∏ m ∈ Ioc a (a + (j + 1)), ∏ q ∈ m.primeFactors, q) ^ E :=
        Nat.pow_le_pow_left (Nat.mul_le_mul hA hB) E
    _ ≤ (((j + 1) ! * 4 ^ z) * ((j + 1) ! * 4 ^ z)) ^ E :=
        Nat.pow_le_pow_left (Nat.mul_le_mul hQ hQ) E
    _ = ((j + 1) ! * 4 ^ z) ^ (2 * E) := by rw [← pow_two, ← pow_mul]

/- ## Small gap: the size comparison -/

lemma log_le_half {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / 2 := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < x / 2 by positivity)
  rw [Real.log_div hx.ne' (by norm_num)] at h
  linarith [Real.log_two_lt_d9]

/-- The two bounds on `b = a₂` contradict each other once `log n` is large. -/
lemma endgame {E n a k b : ℕ} (hE : 1 ≤ E) (hka : k + a = n) (hk2 : 2 ≤ k)
    (hklog : (k : ℝ) ≤ Real.log n)
    (h1 : a ^ (k - 1) ≤ (k ! * 4 ^ b) ^ (2 * E))
    (h2 : b ! ≤ n ^ k)
    (hT1 : 16 * (E : ℝ) * Real.log (Real.log n) + 8 ≤ Real.log n)
    (hT2 : 6 * (E : ℝ) * Real.exp (12 * (E : ℝ) + 1) < Real.log n) : False := by
  have hER : (1:ℝ) ≤ E := by exact_mod_cast hE
  have hkR : (2:ℝ) ≤ k := by exact_mod_cast hk2
  have hexp1 : 1 ≤ Real.exp (12 * (E:ℝ) + 1) := Real.one_le_exp (by positivity)
  have hLpos : 6 < Real.log n := by
    nlinarith [one_le_mul_of_one_le_of_one_le hER hexp1]
  have hn0 : 0 < n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  have hkaR : (k:ℝ) + a = n := by exact_mod_cast hka
  have hna : (n:ℝ) ≤ 2 * a := by linarith [log_le_half hnR]
  have ha0 : (0:ℝ) < a := by linarith
  have hloga : Real.log n - Real.log 2 ≤ Real.log a := by
    have h := Real.log_le_log hnR hna
    rw [Real.log_mul (by norm_num) ha0.ne'] at h
    linarith
  have hk0 : (0:ℝ) < k := by linarith
  have hfk : (0:ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hb0 : (0:ℝ) ≤ b := Nat.cast_nonneg b
  -- logarithm of `h1`
  have h1L : ((k:ℝ) - 1) * Real.log a
      ≤ 2 * (E:ℝ) * (Real.log (k ! : ℝ) + b * Real.log 4) := by
    have h1R : (a:ℝ) ^ (k - 1) ≤ ((k ! : ℝ) * 4 ^ b) ^ (2 * E) := by exact_mod_cast h1
    have h := Real.log_le_log (pow_pos ha0 _) h1R
    have e1 : Real.log ((a:ℝ) ^ (k - 1)) = ((k:ℝ) - 1) * Real.log a := by
      rw [Real.log_pow, Nat.cast_sub (by omega)]
      simp
    have e2 : Real.log (((k ! : ℝ) * 4 ^ b) ^ (2 * E))
        = 2 * (E:ℝ) * (Real.log (k ! : ℝ) + b * Real.log 4) := by
      rw [Real.log_pow, Real.log_mul hfk.ne' (by positivity), Real.log_pow]
      push_cast
      ring
    rwa [e1, e2] at h
  have hfk_le : Real.log (k ! : ℝ) ≤ k * Real.log k := by
    have h : (k ! : ℝ) ≤ (k:ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
    have h' := Real.log_le_log hfk h
    rwa [Real.log_pow] at h'
  have hlogk : Real.log k ≤ Real.log (Real.log n) := Real.log_le_log hk0 hklog
  have hlog4 : Real.log 4 ≤ 1.4 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    push_cast
    linarith [Real.log_two_lt_d9]
  have hlog2 : Real.log 2 ≤ 0.7 := by linarith [Real.log_two_lt_d9]
  have hE0 : (0:ℝ) ≤ 2 * E := by positivity
  -- lower bound for `b`
  have key : (k:ℝ) * Real.log n ≤ 12 * E * b := by
    have s1 : ((k:ℝ) - 1) * (Real.log n - Real.log 2) ≤ ((k:ℝ) - 1) * Real.log a :=
      mul_le_mul_of_nonneg_left hloga (by linarith)
    have s2 : (k:ℝ) * Real.log k ≤ k * Real.log (Real.log n) :=
      mul_le_mul_of_nonneg_left hlogk hk0.le
    have s3 : (b:ℝ) * Real.log 4 ≤ b * 1.4 := mul_le_mul_of_nonneg_left hlog4 hb0
    have s4 : 2 * (E:ℝ) * Real.log (Real.log n) ≤ Real.log n / 8 - 1 := by linarith
    have s5 : (k:ℝ) * (2 * E * Real.log (Real.log n)) ≤ k * (Real.log n / 8 - 1) :=
      mul_le_mul_of_nonneg_left s4 hk0.le
    have s6 : 2 * (E:ℝ) * (Real.log (k ! : ℝ) + b * Real.log 4)
        ≤ 2 * (E:ℝ) * (k * Real.log (Real.log n) + b * 1.4) :=
      mul_le_mul_of_nonneg_left (by linarith) hE0
    have s7 : (k:ℝ) / 2 * (Real.log n - 0.7) ≤ ((k:ℝ) - 1) * (Real.log n - Real.log 2) := by
      nlinarith
    have s8 : (0:ℝ) ≤ E * b := by positivity
    nlinarith
  have hbpos : (0:ℝ) < b := by
    rcases hb0.lt_or_eq with h | h
    · exact h
    · rw [← h] at key
      nlinarith
  -- upper bound for `b`
  have hfb : (0:ℝ) < (b ! : ℝ) := by exact_mod_cast Nat.factorial_pos b
  have h2R : (b ! : ℝ) ≤ (n:ℝ) ^ k := by exact_mod_cast h2
  have h4 : (b:ℝ) ^ b ≤ Real.exp b * (n:ℝ) ^ k :=
    ((div_le_iff₀ hfb).mp (Real.pow_div_factorial_le_exp (b:ℝ) hb0 b)).trans
      (mul_le_mul_of_nonneg_left h2R (Real.exp_pos _).le)
  have h5 := Real.log_le_log (pow_pos hbpos b) h4
  rw [Real.log_pow, Real.log_mul (Real.exp_pos _).ne' (pow_pos hnR k).ne', Real.log_exp,
    Real.log_pow] at h5
  have h6 : Real.log b ≤ 12 * E + 1 := by
    by_contra hc
    have hc' := mul_lt_mul_of_pos_left (not_le.mp hc) hbpos
    nlinarith
  have h7 : (b:ℝ) ≤ Real.exp (12 * E + 1) := by
    have h := Real.exp_le_exp.mpr h6
    rwa [Real.exp_log hbpos] at h
  nlinarith [mul_le_mul_of_nonneg_left h7 (show (0:ℝ) ≤ 12 * E by positivity),
    mul_le_mul_of_nonneg_right hkR (show (0:ℝ) ≤ Real.log n by linarith)]

lemma loglog_small (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, c * Real.log (Real.log n) + 8 ≤ Real.log n := by
  have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h0 : ∀ᶠ x : ℝ in atTop, c * Real.log x + 8 ≤ x := by
    have hb := Real.isLittleO_log_id_atTop.bound (show (0:ℝ) < 1 / (2 * c) by positivity)
    filter_upwards [hb, eventually_ge_atTop (16:ℝ)] with x hx h16
    simp only [id, Real.norm_eq_abs] at hx
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x)] at hx
    have h1 : Real.log x ≤ 1 / (2 * c) * x := (le_abs_self _).trans hx
    have h2 : c * Real.log x ≤ x / 2 := by
      calc c * Real.log x ≤ c * (1 / (2 * c) * x) := mul_le_mul_of_nonneg_left h1 hc.le
        _ = x / 2 := by field_simp
    linarith
  filter_upwards [ht.eventually h0] with n hn
  exact hn

/- ## Assembly -/

/-- With `H1` and `H2`, large `n` admit no solution. -/
lemma no_solutions (h1 : H1) (h2 : H2) : ∀ᶠ n : ℕ in atTop, ∀ l, (n,l) ∉ Erdos373.S := by
  obtain ⟨E0, hfin⟩ := h1
  obtain ⟨N, hNmax⟩ := hfin.bddAbove
  have hN : ∀ m, N + 1 ≤ m →
      m + 1 ≤ (∏ p ∈ (m * (m + 1)).primeFactors, p) ^ (E0 + 1) := by
    intro m hm
    by_contra hc
    have hpos : 0 < ∏ p ∈ (m * (m + 1)).primeFactors, p :=
      Finset.prod_pos fun q hq => (Nat.prime_of_mem_primeFactors hq).pos
    have hlt : (∏ p ∈ (m * (m + 1)).primeFactors, p) ^ E0 < m + 1 :=
      lt_of_le_of_lt (Nat.pow_le_pow_right hpos (Nat.le_succ E0)) (not_le.mp hc)
    have hmN : m ≤ N := hNmax hlt
    omega
  have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [large_gap h2, loglog_small (16 * ((E0 + 1 : ℕ) : ℝ)) (by positivity),
    ht.eventually_gt_atTop (6 * ((E0 + 1 : ℕ) : ℝ) * Real.exp (12 * ((E0 + 1 : ℕ) : ℝ) + 1)),
    eventually_ge_atTop (2 * N + 4)] with n hgap hT1 hT2 hn l hl
  obtain ⟨hprod,hs,ha,hmin⟩ := hl
  cases l with
  | nil =>
    simp only [List.map_nil,List.prod_nil] at hprod
    have := n.self_le_factorial
    omega
  | cons a l =>
    change a < n-1 at ha
    have hklog := hgap a l hprod hs ha
    generalize hkdef : n - a = k at hklog
    have heq : k+a=n := by omega
    have hk2 : 2 ≤ k := by omega
    have htail := tail_eq heq hprod
    cases l with
    | nil =>
      simp only [List.map_nil,List.prod_nil] at htail
      have hc1 := Nat.choose_pos (show k ≤ n by omega)
      have hc2 : 2 ≤ k ! := hk2.trans k.self_le_factorial
      nlinarith
    | cons b t =>
      have hbmax : ∀ c ∈ b :: t, c ≤ b := by
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact le_rfl
        · exact (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1 c hc
      have hdesc : n.descFactorial k = ((b :: t).map Nat.factorial).prod := by
        rw [← htail, Nat.descFactorial_eq_factorial_mul_choose, mul_comm]
      have hz : ∀ m ∈ Ioc a (a + (k - 1 + 1)), ∀ q : ℕ, q.Prime → q ∣ m → q ≤ b := by
        intro m hm q hq hqm
        rw [mem_Ioc] at hm
        have hmd : m ∣ n.descFactorial k := by
          rw [Nat.descFactorial_eq_prod_range]
          have hmm : m = n - (n - m) := by omega
          rw [hmm]
          exact Finset.dvd_prod_of_mem (fun i => n - i) (Finset.mem_range.mpr (by omega))
        obtain ⟨c, hc, hqc⟩ := prod_prime hq (b :: t) (hdesc ▸ hqm.trans hmd)
        exact hqc.trans (hbmax c hc)
      have hbfact : b ! ≤ n ^ k := by
        have hd : b ! ∣ n.descFactorial k :=
          hdesc ▸ List.dvd_prod (List.mem_map.mpr ⟨b, by simp, rfl⟩)
        exact (Nat.le_of_dvd (Nat.descFactorial_pos.mpr (by omega)) hd).trans
          (Nat.descFactorial_le_pow n k)
      have hnR : (0:ℝ) < n := by
        have : 0 < n := by omega
        exact_mod_cast this
      have h2k : 2 * k ≤ n := by
        have h := log_le_half hnR
        have h' : (2:ℝ) * k ≤ n := by linarith
        exact_mod_cast h'
      have hpb := pair_bound hN a (k - 1) b (by omega) hz
      rw [show k - 1 + 1 = k by omega] at hpb
      exact endgame (E := E0 + 1) (by omega) heq hk2 hklog hpb hbfact hT1 hT2

lemma length_le_prod {l : List ℕ} (h : ∀ a ∈ l, 1 < a) :
    l.length+1 ≤ (l.map Nat.factorial).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : 2 ≤ a ! := (h a (by simp)).trans_le a.self_le_factorial
    have hh := ih (fun b hb => h b (by simp [hb]))
    simp only [List.length_cons,List.map_cons,List.prod_cons]
    nlinarith [Nat.mul_le_mul ha hh]

lemma finite_lists (A : ℕ) :
    ∀ L : ℕ, {l : List ℕ | l.length ≤ L ∧ ∀ x ∈ l, x ≤ A}.Finite := by
  intro L
  induction L with
  | zero =>
    apply (Set.finite_singleton ([] : List ℕ)).subset
    rintro l ⟨hl, -⟩
    exact List.length_eq_zero_iff.mp (by omega)
  | succ L ih =>
    apply ((Set.finite_singleton ([] : List ℕ)).union
      (Set.Finite.image2 List.cons (Set.finite_Iic A) ih)).subset
    rintro l ⟨hl, hx⟩
    cases l with
    | nil => exact Or.inl rfl
    | cons x t =>
      exact Or.inr ⟨x, hx x (by simp), t,
        ⟨by simpa using hl, fun y hy => hx y (by simp [hy])⟩, rfl⟩

theorem main : H1 → H2 → type_of% @Erdos373.erdos_373 := by
  intro h1 h2
  obtain ⟨N,hN⟩ := eventually_atTop.mp (no_solutions h1 h2)
  have hfin : {p : ℕ × List ℕ | p.1 ≤ N ∧ p.2.length ≤ N ! ∧ ∀ x ∈ p.2, x ≤ N !}.Finite :=
    ((Set.finite_Iic N).prod (finite_lists (N !) (N !))).subset (fun p hp => ⟨hp.1, hp.2⟩)
  apply hfin.subset
  rintro ⟨n,l⟩ hl
  have hn : n ≤ N := by
    by_contra! hh
    exact hN _ hh.le _ hl
  obtain ⟨hprod,hs,ha,hmin⟩ := hl
  have hb := Nat.factorial_le hn
  refine ⟨hn, ?_, ?_⟩
  · have := length_le_prod hmin
    change l.length ≤ (N !)
    omega
  · intro a he
    have hd : a ! ∣ (l.map Nat.factorial).prod := List.dvd_prod (List.mem_map.mpr ⟨a,he,rfl⟩)
    rw [← hprod] at hd
    exact a.self_le_factorial.trans ((Nat.le_of_dvd n.factorial_pos hd).trans hb)

end OMA.R_Erdos373_erdos_373_R1
