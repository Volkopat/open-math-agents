import OMAStatements.S_oeis_a335976

/-!
# Fibonacci nontotients at prime indices

For a prime `p ≡ 1 (mod 20)`, `F_(6p)` is a totient if and only if its odd part
is a product `d * e` of distinct factors for which both `2*d+1` and `2*e+1` are prime.
The reverse implication has the explicit preimage `4 * (2*d+1) * (2*e+1)`.
The finite certificate below also proves that 41 belongs to the sequence.

The first step is the classical Fibonacci prime divisibility law, proved below using
Frobenius. The second asks for infinitely many failures of the binary divisor test.
The original sequence is https://oeis.org/A335976. Max Alekseyev discussed the role of
the 2-adic valuation at https://mathoverflow.net/a/472161.

Credit: @yuka30240
-/

namespace OMA.R_oeis_a335976_R1

/-- The Fibonacci prime divisibility law, with the split case distinguished. -/
def H1 : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ 5 →
    q ∣ Nat.fib (q - 1) ∨ (¬ IsSquare (5 : ZMod q) ∧ q ∣ Nat.fib (q + 1))

/-- The remaining sieve question. For arbitrarily large primes in this progression, no
complementary pair of distinct divisors of the odd part yields two shifted primes. -/
def H2 : Prop :=
  ∀ B : ℕ, ∃ p : ℕ, B < p ∧ p.Prime ∧ p % 20 = 1 ∧
    ∀ d e : ℕ, Nat.fib (6 * p) = 8 * d * e → d ≠ e →
      ¬ ((2 * d + 1).Prime ∧ (2 * e + 1).Prime)

lemma root_power_fib {K : Type*} [Field K] (a : K) (ha : a ^ 2 = a + 1) (n : ℕ) :
    a ^ (n + 1) = (Nat.fib (n + 1) : K) * a + Nat.fib n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, show n.succ + 1 = n + 2 by omega, Nat.fib_add_two]
    push_cast
    linear_combination (Nat.fib (n + 1) : K) * ha

lemma fib_eq_zero_of_powers {K : Type*} [Field K] {a b : K} (ha : a ^ 2 = a + 1)
    (hb : b ^ 2 = b + 1) (hne : a ≠ b) {n : ℕ} (heq : a ^ n = b ^ n) :
    (Nat.fib n : K) = 0 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [root_power_fib a ha, root_power_fib b hb] at heq
    exact (mul_eq_zero.mp (show (Nat.fib (n + 1) : K) * (a - b) = 0 by
      linear_combination heq)).resolve_right (sub_ne_zero.mpr hne)

lemma fib_prime_from_sqrt {K : Type*} [Field K] {q : ℕ} [Fact q.Prime] [CharP K q]
    (h2 : (2 : K) ≠ 0) (h5 : (5 : K) ≠ 0) {z : K} (hz : z ^ 2 = 5) :
    ((frobenius K q) z = z → q ∣ Nat.fib (q - 1)) ∧
    ((frobenius K q) z = -z → q ∣ Nat.fib (q + 1)) := by
  let a := (1 + z) / 2
  let b := (1 - z) / 2
  have ha : a ^ 2 = a + 1 := by dsimp [a]; field_simp; linear_combination hz
  have hb : b ^ 2 = b + 1 := by dsimp [b]; field_simp; linear_combination hz
  have hn : a ≠ b := by
    intro h
    have hz0 : z = 0 := by
      have hh := (div_left_inj' h2).mp h
      exact (mul_eq_zero.mp (show (2 : K) * z = 0 by linear_combination hh)).resolve_left h2
    simp [hz0, h5.symm] at hz
  have htwo : frobenius K q 2 = 2 := map_natCast (frobenius K q) 2
  have hq := (Fact.out : q.Prime).two_le
  constructor
  · intro h
    have he (x : K) (hfixed : (frobenius K q) x = x) (hquad : x ^ 2 = x + 1) :
        x ^ (q - 1) = 1 := by
      have hx : x ≠ 0 := by rintro rfl; simp at hquad
      apply mul_right_cancel₀ hx
      rw [← pow_succ, show q - 1 + 1 = q by omega, one_mul]
      exact hfixed
    have haf : (frobenius K q) a = a := by simp [a, h, htwo]
    have hbf : (frobenius K q) b = b := by simp [b, h, htwo]
    exact (CharP.cast_eq_zero_iff K q _).mp
      (fib_eq_zero_of_powers ha hb hn ((he a haf ha).trans (he b hbf hb).symm))
  · intro h
    have haf : a ^ q = b := by
      change frobenius K q a = b
      simp [a, b, h, htwo, sub_eq_add_neg]
    have hbf : b ^ q = a := by
      change frobenius K q b = a
      simp [a, b, h, htwo]
    exact (CharP.cast_eq_zero_iff K q _).mp
      (fib_eq_zero_of_powers ha hb hn (show a ^ (q + 1) = b ^ (q + 1) by
        simp only [pow_succ, haf, hbf, mul_comm]))

lemma fibonacci_prime_law (q : ℕ) (hq : q.Prime) (hn2 : q ≠ 2) (hn5 : q ≠ 5) :
    q ∣ Nat.fib (q - 1) ∨ (¬ IsSquare (5 : ZMod q) ∧ q ∣ Nat.fib (q + 1)) := by
  let : Fact q.Prime := ⟨hq⟩
  have h2 (K : Type) [Field K] [CharP K q] : (2 : K) ≠ 0 :=
    (CharP.cast_eq_zero_iff K q 2).not.mpr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).not.mpr hn2)
  have h5 (K : Type) [Field K] [CharP K q] : (5 : K) ≠ 0 :=
    (CharP.cast_eq_zero_iff K q 5).not.mpr ((Nat.prime_dvd_prime_iff_eq hq (by decide)).not.mpr hn5)
  by_cases hs : IsSquare (5 : ZMod q)
  · obtain ⟨z, hz⟩ := hs
    have hr : z ^ 2 = 5 := by simpa [sq] using hz.symm
    exact Or.inl ((fib_prime_from_sqrt (q := q) (h2 _) (h5 _) hr).1 (ZMod.pow_card z))
  · let K := AlgebraicClosure (ZMod q)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (5 : K) (by decide : 0 < 2)
    have hfr : (frobenius K q z) ^ 2 = z ^ 2 := by
      rw [← map_pow, hz]
      exact map_natCast (frobenius K q) 5
    have law := fib_prime_from_sqrt (q := q) (h2 _) (h5 _) hz
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp hfr).elim (fun h => Or.inl (law.1 h))
      (fun h => Or.inr ⟨hs, law.2 h⟩)

lemma index_dvd_of_common_fib_factor {p q k : ℕ} (hp : p.Prime)
    (hq : q.Prime) (ho : q ≠ 2) (hf : q ∣ Nat.fib (6 * p)) (hk : q ∣ Nat.fib k) :
    p ∣ k := by
  by_contra hn
  have hc := hp.coprime_iff_not_dvd.mpr hn
  have h := Nat.dvd_gcd hk hf
  rw [← Nat.fib_gcd, Nat.Coprime.gcd_mul_right_cancel_right 6 hc] at h
  have h8 : q ∣ 8 := h.trans (Nat.fib_dvd _ _ (Nat.gcd_dvd_right k 6))
  have hpow : q ∣ 2 ^ 3 := h8
  exact ho ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hpow))

lemma eight_and_not_sixteen {p : ℕ} (hp : Odd p) :
    8 ∣ Nat.fib (6 * p) ∧ ¬ 16 ∣ Nat.fib (6 * p) := by
  have hg : Nat.gcd (6 * p) 12 = 6 := by
    change Nat.gcd (6 * p) (6 * 2) = 6
    rw [Nat.gcd_mul_left, Nat.coprime_two_right.mpr hp |>.gcd_eq_one, mul_one]
  refine ⟨Nat.fib_dvd 6 (6 * p) (dvd_mul_right _ _), ?_⟩
  intro h
  have hc := Nat.dvd_gcd h (show 16 ∣ Nat.fib 12 by decide)
  rw [← Nat.fib_gcd, hg] at hc
  exact (by decide : ¬ 16 ∣ Nat.fib 6) hc

lemma signed_prime_residue (h : H1) {p q : ℕ} (hp : p.Prime) (hlarge : 10 < p)
    (hq : q.Prime) (ho : q ≠ 2) (hf : q ∣ Nat.fib (6 * p)) :
    (q : ZMod p) = 1 ∨ (q : ZMod p) = -1 := by
  have hn5 : q ≠ 5 := by
    rintro rfl
    have hk := index_dvd_of_common_fib_factor hp hq ho hf (show 5 ∣ Nat.fib 5 by decide)
    have := Nat.le_of_dvd (by decide : 0 < 5) hk
    omega
  rcases h q hq ho hn5 with hminus | ⟨_, hplus⟩
  · have hd := index_dvd_of_common_fib_factor hp hq ho hf hminus
    have hz := (ZMod.natCast_eq_zero_iff _ _).2 hd
    rw [Nat.cast_sub (by have := hq.two_le; omega)] at hz
    exact Or.inl (by linear_combination hz)
  · have hd := index_dvd_of_common_fib_factor hp hq ho hf hplus
    have hz := (ZMod.natCast_eq_zero_iff _ _).2 hd
    push_cast at hz
    exact Or.inr (by linear_combination hz)

lemma signed_odd_divisor (h : H1) {p : ℕ} (hp : p.Prime) (hlarge : 10 < p) (d : ℕ)
    (hd : d ∣ Nat.fib (6 * p)) (ho : Odd d) : (d : ZMod p) = 1 ∨ (d : ZMod p) = -1 := by
  induction d using induction_on_primes with
  | zero => simp at ho
  | one => simp
  | prime_mul q d hq ih =>
    have hodd := Nat.odd_mul.mp ho
    have hq' := signed_prime_residue h hp hlarge hq (by rintro rfl; exact (by decide : ¬ Odd 2) hodd.1)
      ((dvd_mul_right q d).trans hd)
    have hd' := ih ((dvd_mul_left d q).trans hd) hodd.2
    rcases hq' with hq' | hq' <;> rcases hd' with hd' | hd' <;> simp [hq', hd']

/-- The Cassini invariant of a pair of consecutive Fibonacci numbers. -/
lemma cassini_cast (q n : ℕ) :
    (Nat.fib (n + 1) : ZMod q) ^ 2 - Nat.fib n * (Nat.fib (n + 1) : ZMod q) -
      (Nat.fib n : ZMod q) ^ 2 = (-1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n.succ + 1 = n + 2 by omega, Nat.fib_add_two, pow_succ]
    push_cast
    linear_combination -ih

/-- For an index twice an odd number, a prime divisor congruent to three modulo four
must see 5 as a square. -/
lemma five_square_of_three_mod_four {q k : ℕ} (hq : q.Prime) (hfour : q % 4 = 3)
    (hk : Odd k) (hf : q ∣ Nat.fib (2 * k)) : IsSquare (5 : ZMod q) := by
  let : Fact q.Prime := ⟨hq⟩
  have he := (ZMod.natCast_eq_zero_iff _ _).2 hf
  rw [Nat.fib_two_mul, Nat.cast_mul, Nat.cast_sub (by have := @Nat.fib_le_fib_succ k; omega)] at he
  push_cast at he
  have hc := cassini_cast q k
  rw [hk.neg_one_pow] at hc
  rcases mul_eq_zero.mp he with hx | hl
  · rw [hx] at hc
    have hs : (Nat.fib (k + 1) : ZMod q) ^ 2 = -1 := by linear_combination hc
    exact False.elim (ZMod.mod_four_ne_three_of_sq_eq_neg_one hs hfour)
  · refine ⟨5 * (Nat.fib (k + 1) : ZMod q), ?_⟩
    have hx : (Nat.fib k : ZMod q) = 2 * Nat.fib (k + 1) := by linear_combination -hl
    rw [hx] at hc
    linear_combination 5 * hc

lemma index_not_dvd_fib (h : H1) {p : ℕ} (hp : p.Prime) (hlarge : 10 < p) :
    ¬ p ∣ Nat.fib (6 * p) := by
  let : Fact p.Prime := ⟨hp⟩
  intro hf
  have hh := signed_prime_residue h hp hlarge hp (by omega) hf
  simp at hh

/-- The odd part of a totient preimage is squarefree. An odd prime dividing the Fibonacci
number cannot also have its predecessor dividing that number. -/
lemma no_consecutive_divisors (h : H1) {p q : ℕ} (hp : p.Prime) (hlarge : 10 < p)
    (hq : q.Prime) (ho : q ≠ 2) (hf : q ∣ Nat.fib (6 * p)) :
    ¬ q - 1 ∣ Nat.fib (6 * p) := by
  intro hd
  have hqpos := hq.two_le
  have hpodd := hp.odd_of_ne_two (by omega)
  have hval := (eight_and_not_sixteen hpodd).2
  have hindex := index_not_dvd_fib h hp hlarge
  have hsign := signed_prime_residue h hp hlarge hq ho hf
  have hminus : (q : ZMod p) = -1 := by
    rcases hsign with he | he
    · have hz : ((q - 1 : ℕ) : ZMod p) = 0 := by
        rw [Nat.cast_sub (by omega), he]
        simp
      exact False.elim (hindex (((ZMod.natCast_eq_zero_iff _ _).mp hz).trans hd))
    · exact he
  by_cases hthree : q % 4 = 3
  · have hs := five_square_of_three_mod_four hq hthree ((by decide : Odd 3).mul hpodd)
      (by rwa [← Nat.mul_assoc])
    have hn5 : q ≠ 5 := by omega
    rcases h q hq ho hn5 with hsplit | ⟨hn, _⟩
    · exact hindex ((index_dvd_of_common_fib_factor hp hq ho hf hsplit).trans hd)
    · exact hn hs
  have hqodd := hq.odd_of_ne_two ho
  have hfour : 4 ∣ q - 1 := by
    have := Nat.odd_iff.mp hqodd
    omega
  obtain ⟨t, ht⟩ := hfour
  obtain ⟨c, u, hc, hu, he⟩ : ∃ c u : ℕ, (c = 4 ∨ c = 8) ∧ Odd u ∧ q - 1 = c * u := by
    by_cases hut : Odd t
    · exact ⟨4, t, Or.inl rfl, hut, ht⟩
    · obtain ⟨u, hu⟩ : Even t := Nat.not_odd_iff_even.mp hut
      have he : q - 1 = 8 * u := by omega
      refine ⟨8, u, Or.inr rfl, ?_, he⟩
      by_contra huodd
      apply hval
      apply dvd_trans _ hd
      obtain ⟨v, hv⟩ := Nat.not_odd_iff_even.mp huodd
      exact ⟨v, by omega⟩
  have husign := signed_odd_divisor h hp hlarge u ((dvd_mul_left u c).trans (he ▸ hd)) hu
  have heq : (q : ZMod p) = (c : ZMod p) * u + 1 := by
    have eqn : q = c * u + 1 := by omega
    simpa using congrArg (fun n : ℕ => (n : ZMod p)) eqn
  have impossible (j : ℕ) (hj : j = 4 ∨ j = 8)
      (heq : (j : ZMod p) = 2 ∨ (j : ZMod p) = -2) : False := by
    rcases hj with rfl | rfl <;> rcases heq with heq | heq
    all_goals
      have hn : p ∣ 2 ∨ p ∣ 6 ∨ p ∣ 10 := by
        first
        | exact Or.inl ((ZMod.natCast_eq_zero_iff 2 p).mp (by linear_combination heq))
        | exact Or.inr (Or.inl ((ZMod.natCast_eq_zero_iff 6 p).mp (by linear_combination heq)))
        | exact Or.inr (Or.inr ((ZMod.natCast_eq_zero_iff 10 p).mp (by linear_combination heq)))
      rcases hn with hn | hn | hn <;> have := Nat.le_of_dvd (by decide) hn <;> omega
  apply impossible c hc
  rw [hminus] at heq
  rcases husign with hu | hu
  · right
    rw [hu, mul_one] at heq
    linear_combination -heq
  · left
    rw [hu, mul_neg_one] at heq
    linear_combination heq

/-- Euler's product formula after removing the prime 2 and excluding an odd square
factor of the preimage. -/
lemma preimage_product {m n : ℕ} (hm : 0 < m) (heq : m.totient = n)
    (hno : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ n → ¬ q - 1 ∣ n) :
    n = 2 ^ (m.factorization 2 - 1) * ∏ q ∈ m.primeFactors.erase 2, (q - 1) := by
  have hpred {q : ℕ} (hq : q.Prime) (hdiv : q ∣ m) : q - 1 ∣ n := by
    simpa [← heq, Nat.totient_prime hq] using Nat.totient_dvd_of_dvd hdiv
  have hsimp {q : ℕ} (hqmem : q ∈ m.primeFactors.erase 2) :
      q ^ (m.factorization q - 1) * (q - 1) = q - 1 := by
    obtain ⟨hne, hqm⟩ := Finset.mem_erase.mp hqmem
    have hq := Nat.prime_of_mem_primeFactors hqm
    have hdiv := Nat.dvd_of_mem_primeFactors hqm
    have hlow : m.factorization q ≤ 1 := by
      by_contra! hhigh
      have hsquare := (hq.pow_dvd_iff_le_factorization hm.ne').mpr (show 2 ≤ _ from hhigh)
      have htot := Nat.totient_dvd_of_dvd hsquare
      rw [show (2 : ℕ) = 1 + 1 by rfl, Nat.totient_prime_pow_succ hq, pow_one, heq] at htot
      exact hno q hq hne ((dvd_mul_right q (q - 1)).trans htot) (hpred hq hdiv)
    simp [Nat.sub_eq_zero_of_le hlow]
  have htot := Nat.totient_eq_prod_factorization hm.ne'
  rw [Nat.prod_factorization_eq_prod_primeFactors] at htot
  rw [← heq, htot]
  by_cases htwo : 2 ∈ m.primeFactors
  · rw [← Finset.mul_prod_erase _ _ htwo]
    simpa using (Finset.prod_congr rfl fun q hq => hsimp hq)
  · have hf : m.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (fun hd =>
        htwo (Nat.prime_two.mem_primeFactors hd hm.ne'))
    rw [hf, Nat.zero_sub, pow_zero, one_mul]
    have hsame := Finset.erase_eq_of_notMem htwo
    rw [hsame]
    exact Finset.prod_congr rfl fun q hq => hsimp (hsame.symm ▸ hq)

/-- Each odd prime predecessor is even. The power of 2 outside their product and the
number of distinct predecessors together cannot exceed three. -/
lemma product_budget {s : Finset ℕ} {b n : ℕ} (hval : ¬ 16 ∣ n)
    (heq : n = 2 ^ b * ∏ q ∈ s, (q - 1))
    (hodd : ∀ q ∈ s, Odd q) : b + s.card ≤ 3 := by
  have hdiv : 2 ^ s.card ∣ ∏ q ∈ s, (q - 1) := by
    rw [← Finset.prod_const]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun q hq => by
      obtain ⟨k, hk⟩ := hodd q hq
      exact ⟨k, by omega⟩
  by_contra! hlt
  apply hval
  calc
    16 = 2 ^ 4 := rfl
    _ ∣ 2 ^ (b + s.card) := pow_dvd_pow 2 hlt
    _ ∣ n := by rw [heq, pow_add]; exact Nat.mul_dvd_mul_left _ hdiv

lemma fib_six_residue {p : ℕ} (hp : p % 20 = 1) : Nat.fib (6 * p) % 15 = 8 := by
  have h0 : (Nat.fib 120 : ZMod 15) = 0 := by decide
  have h1 : (Nat.fib 121 : ZMod 15) = 1 := by decide
  have shift (n : ℕ) : (Nat.fib (n + 120) : ZMod 15) = Nat.fib n := by
    cases n with
    | zero => exact h0
    | succ n =>
      rw [show n.succ + 120 = n + 120 + 1 by omega, Nat.fib_add]
      push_cast
      rw [h0, h1]
      ring
  have h (k : ℕ) : (Nat.fib (6 * (20 * k + 1)) : ZMod 15) = 8 := by
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show 6 * (20 * (k + 1) + 1) = 6 * (20 * k + 1) + 120 by omega, shift, ih]
  have heq := h (p / 20)
  rw [show 20 * (p / 20) + 1 = p by omega] at heq
  exact (ZMod.natCast_eq_natCast_iff' _ 8 15).mp heq

/-- When n is 8 modulo 15, every admissible odd prime above 3 has predecessor
1 modulo 3. Moving the prime 3 into the power of 2 leaves exactly two primes. -/
lemma binary_product {n b : ℕ} {s : Finset ℕ} (hbig : 8 < n) (hres : n % 15 = 8)
    (hbudget : b + s.card ≤ 3)
    (hs : ∀ q ∈ s, q.Prime ∧ 2 < q ∧ q - 1 ∣ n)
    (heq : n = 2 ^ b * ∏ q ∈ s, (q - 1)) :
    ∃ d e : ℕ, d ≠ e ∧ (2 * d + 1).Prime ∧ (2 * e + 1).Prime ∧ n = 8 * d * e := by
  have h3 : n % 3 = 2 := by omega
  have h5 : n % 5 = 3 := by omega
  obtain ⟨c, t, hsize, hmem, hprod⟩ : ∃ (c : ℕ) (t : Finset ℕ),
      c + t.card ≤ 3 ∧ (∀ q ∈ t, q ∈ s ∧ q ≠ 3) ∧ n = 2 ^ c * ∏ q ∈ t, (q - 1) := by
    by_cases hm : 3 ∈ s
    · refine ⟨b + 1, s.erase 3, ?_, fun q h => ⟨Finset.mem_of_mem_erase h, (Finset.mem_erase.mp h).1⟩, ?_⟩
      · have := Finset.card_erase_add_one hm
        omega
      · rw [heq, ← Finset.mul_prod_erase s (fun q : ℕ => q - 1) hm, pow_succ]
        simp [mul_assoc]
    · exact ⟨b, s, hbudget, fun q hq => ⟨hq, fun he => hm (he ▸ hq)⟩, heq⟩
  have hunit (q : ℕ) (hq : q ∈ t) : (q - 1) % 3 = 1 := by
    obtain ⟨hqs, hne⟩ := hmem q hq
    obtain ⟨hqprime, hgt, hd⟩ := hs q hqs
    have hnq : ¬ 3 ∣ q := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hqprime).not.mpr hne.symm
    have hnp : ¬ 3 ∣ q - 1 := fun hd' => (by omega : ¬ 3 ∣ n) (hd'.trans hd)
    omega
  have hones : (∏ q ∈ t, (q - 1)) % 3 = 1 := by
    rw [Finset.prod_nat_mod]
    rw [Finset.prod_eq_one (fun q hq => hunit q hq)]
    decide
  have hcmod : 2 ^ c % 3 = 2 := by
    rw [hprod, Nat.mul_mod, hones] at h3
    simpa using h3
  have hc : c = 1 := by
    have hle : c ≤ 3 := by omega
    have hodd : c = 1 ∨ c = 3 := by
      interval_cases c <;> first | decide | contradiction
    rcases hodd with hc | rfl
    · exact hc
    have ht : t = ∅ := Finset.card_eq_zero.mp (by omega)
    simp [ht] at hprod
    omega
  subst c
  have htwo : t.card = 2 := by
    by_contra hn
    have hsmall : t.card = 0 ∨ t.card = 1 := by omega
    rcases hsmall with hzero | hone
    · simp [Finset.card_eq_zero.mp hzero] at hprod
      omega
    · obtain ⟨q, hsingleton⟩ := Finset.card_eq_one.mp hone
      have hq := (hs q (hmem q (hsingleton ▸ Finset.mem_singleton_self q)).1).1
      simp [hsingleton] at hprod
      have hd : 5 ∣ q := by have := hq.two_le; omega
      have hq5 := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 5) hq).mp hd
      omega
  obtain ⟨q, r, hne, ht⟩ := Finset.card_eq_two.mp htwo
  have hq := hs q (hmem q (ht ▸ by simp)).1
  have hr := hs r (hmem r (ht ▸ by simp)).1
  obtain ⟨d, hd⟩ := hq.1.odd_of_ne_two hq.2.1.ne'
  obtain ⟨e, he⟩ := hr.1.odd_of_ne_two hr.2.1.ne'
  refine ⟨d, e, by omega, hd ▸ hq.1, he ▸ hr.1, ?_⟩
  simp [ht, hne] at hprod
  rw [hprod, hd, he]
  simp
  ring

lemma pair_of_fibonacci_totient (h₁ : H1) {p : ℕ} (hp : p.Prime) (hmod : p % 20 = 1)
    (ht : OMA.S_oeis_a335976.IsTotient (Nat.fib (6 * p))) :
    ∃ d e : ℕ, d ≠ e ∧ (2 * d + 1).Prime ∧ (2 * e + 1).Prime ∧ Nat.fib (6 * p) = 8 * d * e := by
  have hlarge : 10 < p := by have := hp.two_le; omega
  obtain ⟨m, hm, heq⟩ := ht
  have hprod := preimage_product hm heq (fun _ => no_consecutive_divisors h₁ hp hlarge)
  have hdata (q : ℕ) (hq : q ∈ m.primeFactors.erase 2) :
      q.Prime ∧ 2 < q ∧ q - 1 ∣ Nat.fib (6 * p) := by
    obtain ⟨hne, hqm⟩ := Finset.mem_erase.mp hq
    have hprime := Nat.prime_of_mem_primeFactors hqm
    refine ⟨hprime, lt_of_le_of_ne hprime.two_le (Ne.symm hne), ?_⟩
    simpa [← heq, Nat.totient_prime hprime] using Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hqm)
  have hval := (eight_and_not_sixteen (hp.odd_of_ne_two (by omega))).2
  have hbound := product_budget hval hprod fun q hq =>
    (hdata q hq).1.odd_of_ne_two (hdata q hq).2.1.ne'
  have hbig : 8 < Nat.fib (6 * p) := by
    have := Nat.le_fib_self (show 5 ≤ 6 * p by omega)
    omega
  exact binary_product hbig (fib_six_residue hmod) hbound hdata hprod

lemma totient_of_pair {n d e : ℕ} (hne : d ≠ e) (hq : (2 * d + 1).Prime)
    (hr : (2 * e + 1).Prime) (hn : n = 8 * d * e) : OMA.S_oeis_a335976.IsTotient n := by
  let q := 2 * d + 1
  let r := 2 * e + 1
  have hoddq : Odd q := ⟨d, rfl⟩
  have hoddr : Odd r := ⟨e, rfl⟩
  have hqr : q.Coprime r := hq.coprime_iff_not_dvd.mpr
    ((Nat.prime_dvd_prime_iff_eq hq hr).not.mpr (fun he => hne (by omega)))
  have hfour : Nat.Coprime 4 (q * r) := (Nat.coprime_two_left.mpr (hoddq.mul hoddr)).pow_left 2
  refine ⟨4 * (q * r), by dsimp [q, r]; positivity, ?_⟩
  rw [Nat.totient_mul hfour, Nat.totient_mul hqr, Nat.totient_prime hq, Nat.totient_prime hr,
    show Nat.totient 4 = 2 by decide, hn]
  simp
  ring

/-- Exact finite divisor test on the chosen progression. -/
theorem fibonacci_totient_iff_pair {p : ℕ} (hp : p.Prime) (hmod : p % 20 = 1) :
    OMA.S_oeis_a335976.IsTotient (Nat.fib (6 * p)) ↔
      ∃ d e : ℕ, d ≠ e ∧ (2 * d + 1).Prime ∧ (2 * e + 1).Prime ∧ Nat.fib (6 * p) = 8 * d * e := by
  refine ⟨pair_of_fibonacci_totient fibonacci_prime_law hp hmod, ?_⟩
  rintro ⟨d, e, hne, hq, hr, he⟩
  exact totient_of_pair hne hq hr he

open scoped Pointwise

/-- Lucas primality using a supplied prime factorization of the group order candidate. -/
lemma prime_from_factor_list {n : ℕ} (g : ZMod n) (L : List ℕ) (hL : L.prod = n - 1)
    (hpr : ∀ r ∈ L, Nat.Prime r) (hg : g ^ (n - 1) = 1)
    (hex : ∀ r ∈ L, g ^ ((n - 1) / r) ≠ 1) : n.Prime := by
  apply lucas_primality n g hg
  intro q hq hd
  rw [← hL] at hd
  obtain ⟨r, hr, hqr⟩ := hq.prime.dvd_prod_iff.mp hd
  obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (hpr r hr)).mp hqr
  exact hex _ hr

/-- A list of proper divisors certifies that each complementary pair has a composite shift. -/
lemma no_pair_of_cover {N d e : ℕ} {s : Finset ℕ} {w : List ℕ}
    (hN : 0 < N) (hde : N = d * e) (hs : N.divisors = s)
    (hcover : ∀ k ∈ s, ∃ z ∈ w, (1 < z ∧ z < 2 * k + 1 ∧ z ∣ 2 * k + 1) ∨
      (1 < z ∧ z < 2 * (N / k) + 1 ∧ z ∣ 2 * (N / k) + 1)) :
    ¬ ((2 * d + 1).Prime ∧ (2 * e + 1).Prime) := by
  have hd : d ∈ N.divisors := Nat.mem_divisors.mpr ⟨⟨e, hde⟩, hN.ne'⟩
  have hpos : 0 < d * e := hde ▸ hN
  have hquot : N / d = e := by rw [hde, Nat.mul_div_cancel_left _ (Nat.pos_of_mul_pos_right hpos)]
  obtain ⟨z, _, hz | hz⟩ := hcover d (hs ▸ hd)
  · intro h
    rcases h.1.eq_one_or_self_of_dvd z hz.2.2 with hh | hh <;> omega
  · intro h
    rw [hquot] at hz
    rcases h.2.eq_one_or_self_of_dvd z hz.2.2 with hh | hh <;> omega

/- The odd part of F_246 has six distinct prime factors. Nine trial divisors suffice
to rule out both shifts being prime for all 32 unordered factor pairs. -/
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma fib_246_no_pair {d e : ℕ} (heq : Nat.fib (6 * 41) = 8 * d * e) :
    ¬ ((2 * d + 1).Prime ∧ (2 * e + 1).Prime) := by
  let N : ℕ := 144007301485556848537824129275821096556584254665641
  let divisorSet : Finset ℕ := ({1, 2789} : Finset ℕ) * {1, 59369} * {1, 4767481} *
    {1, 370248451} * {1, 7188487771} * {1, 68541957733949701}
  have hn : Nat.fib (6 * 41) = 8 * N := by norm_num [N]
  have h370248451 : Nat.Prime 370248451 := by
    refine prime_from_factor_list (3 : ZMod 370248451) [2, 3, 5, 5, 11, 13, 41, 421]
      (by decide) (by norm_num [List.forall_mem_cons]) (by reduce_mod_char) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num1 <;> reduce_mod_char <;> decide
  have h7188487771 : Nat.Prime 7188487771 := by
    refine prime_from_factor_list (2 : ZMod 7188487771) [2, 3, 5, 41, 5844299]
      (by decide) (by norm_num [List.forall_mem_cons]) (by reduce_mod_char) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> norm_num1 <;> reduce_mod_char <;> decide
  have h68541957733949701 : Nat.Prime 68541957733949701 := by
    refine prime_from_factor_list (2 : ZMod 68541957733949701) [2, 2, 3, 5, 5, 7, 11, 13, 29, 41, 211, 421, 2161]
      (by decide) (by norm_num [List.forall_mem_cons]) (by reduce_mod_char) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num1 <;> reduce_mod_char <;> decide
  have hdivisors : N.divisors = divisorSet := by
    change (2789 * 59369 * 4767481 * 370248451 * 7188487771 * 68541957733949701 : ℕ).divisors = _
    simp only [Nat.divisors_mul, Nat.Prime.divisors (by norm_num : Nat.Prime 2789),
      Nat.Prime.divisors (by norm_num : Nat.Prime 59369), Nat.Prime.divisors (by norm_num : Nat.Prime 4767481),
      h370248451.divisors, h7188487771.divisors, h68541957733949701.divisors, divisorSet]
  have hde : N = d * e := Nat.mul_left_cancel (by decide : 0 < 8)
    (hn.symm.trans (heq.trans (Nat.mul_assoc 8 d e)))
  have hcover : ∀ k ∈ divisorSet, ∃ z ∈ [3, 7, 13, 17, 19, 37, 347, 41189, 16862077],
      (1 < z ∧ z < 2 * k + 1 ∧ z ∣ 2 * k + 1) ∨
      (1 < z ∧ z < 2 * (N / k) + 1 ∧ z ∣ 2 * (N / k) + 1) := by decide
  exact no_pair_of_cover (by decide : 0 < N) hde hdivisors hcover

theorem index_41 : OMA.S_oeis_a335976.IsTerm 41 := by
  intro ht
  obtain ⟨d, e, _, hq, hr, he⟩ :=
    (fibonacci_totient_iff_pair (p := 41) (by norm_num) (by decide)).mp ht
  exact fib_246_no_pair he ⟨hq, hr⟩

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a335976.main := by
  intro h₁ h₂
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨p, hB, hp, hmod, havoid⟩ := h₂ B
  refine ⟨p, ⟨?_, hp⟩, hB⟩
  intro ht
  obtain ⟨d, e, hne, hq, hr, he⟩ := pair_of_fibonacci_totient h₁ hp hmod ht
  exact havoid d e he hne ⟨hq, hr⟩

end OMA.R_oeis_a335976_R1
