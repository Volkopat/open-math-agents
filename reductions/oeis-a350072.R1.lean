import OMAStatements.S_oeis_a350072

-- Reduction oeis-a350072.R1 of A350072: a(n) = sigma(n^2) / gcd(sigma(n^2), A003961(n^2)), where A003961 shifts the prime factorization of n one step towards larger prime
-- Credit: @yuka30240
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a350072_R1
open Finset OMA.S_oeis_a350072

lemma next_spec (p : ℕ) : p < nextPrime p ∧ (nextPrime p).Prime :=
  Nat.find_spec (Nat.exists_infinite_primes (p + 1))

lemma next_le {p q : ℕ} (hlt : p < q) (hq : q.Prime) : nextPrime p ≤ q :=
  Nat.find_min' _ ⟨hlt, hq⟩

lemma geom_blocks (p a b : ℕ) :
    (∑ i ∈ range (a * b), p ^ i) =
      (∑ i ∈ range a, p ^ i) * ∑ j ∈ range b, (p ^ a) ^ j := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ, mul_add]
    simp_rw [pow_add, ← mul_sum, ← pow_mul]
    ring

lemma geom_mono_length (p : ℕ) {a b : ℕ} (hab : a ≤ b) :
    (∑ i ∈ range a, p ^ i) ≤ ∑ i ∈ range b, p ^ i :=
  sum_le_sum_of_subset (range_mono hab)

lemma geom_large {p r : ℕ} (hp : 1 < p) (hr : 1 < r) :
    1 < ∑ i ∈ range r, p ^ i := by
  have h := geom_mono_length p (show 2 ≤ r by omega)
  simp [sum_range_succ] at h
  omega

lemma prime_dvd_factor {x q k : ℕ} (hq : q.Prime) (hx : 1 < x) (h : x ∣ q ^ k) :
    q ∣ x := by
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hq).mp h
  exact dvd_pow_self _ (by rintro rfl; simp at hx)

lemma geom_mod_pow {p q d : ℕ} (h : q ∣ ∑ i ∈ range d, p ^ i) :
    (p : ZMod q) ^ d = 1 := by
  have hz := (ZMod.natCast_eq_zero_iff _ _).2 h
  push_cast at hz
  have he := geom_sum_mul (p : ZMod q) d
  rw [hz, zero_mul] at he
  exact sub_eq_zero.mp he.symm

/-- If every prime in a geometric sum equals a larger prime q, the length
is prime and is the multiplicative order of the base modulo q. -/
lemma prime_length {p q m k : ℕ} (hp : 1 < p) (hpq : p < q) (hq : q.Prime)
    (hm : 1 < m) (h : (∑ i ∈ range m, p ^ i) ∣ q ^ k) :
    m.Prime ∧ m ∣ q - 1 := by
  let : Fact q.Prime := ⟨hq⟩
  have hp0 : (p : ZMod q) ≠ 0 := by
    intro hz
    exact (Nat.not_dvd_of_pos_of_lt (by omega) hpq) ((ZMod.natCast_eq_zero_iff _ _).mp hz)
  have hp1 : (p : ZMod q) ≠ 1 := by
    intro he
    rw [← Nat.cast_one (R := ZMod q)] at he
    have hv := (ZMod.natCast_eq_natCast_iff _ _ _).mp he
    change p % q = 1 % q at hv
    rw [Nat.mod_eq_of_lt hpq, Nat.mod_eq_of_lt hq.one_lt] at hv
    omega
  have pow_at_divisor (d : ℕ) (hd : 1 < d) (hdm : d ∣ m) : (p : ZMod q) ^ d = 1 := by
    obtain ⟨b, rfl⟩ := hdm
    rw [geom_blocks] at h
    exact geom_mod_pow (prime_dvd_factor hq (geom_large hp hd) ((dvd_mul_right _ _).trans h))
  let r := m.minFac
  have hr : r.Prime := Nat.minFac_prime (by omega)
  let : Fact r.Prime := ⟨hr⟩
  have hrd : r ∣ m := Nat.minFac_dvd _
  have hord : orderOf (p : ZMod q) = r := orderOf_eq_prime (pow_at_divisor r hr.one_lt hrd) hp1
  have hrq : r ∣ q - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hp0
  have hqm : ¬ q ∣ m := by
    intro hqm
    have hz := pow_at_divisor q hq.one_lt hqm
    rw [ZMod.pow_card] at hz
    exact hp1 hz
  obtain ⟨b, hb⟩ := hrd
  have hb1 : b = 1 := by
    by_contra! hb1
    have hb2 : 1 < b := by
      have hb0 : b ≠ 0 := by rintro rfl; simp_all
      omega
    have hblock := h
    rw [hb, geom_blocks] at hblock
    have hbase : 1 < p ^ r := one_lt_pow₀ hp hr.ne_zero
    have hqb := prime_dvd_factor hq (geom_large hbase hb2) ((dvd_mul_left _ _).trans hblock)
    have hz := (ZMod.natCast_eq_zero_iff _ _).2 hqb
    push_cast at hz
    rw [← hord, pow_orderOf_eq_one] at hz
    simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at hz
    exact hqm (hb ▸ dvd_mul_of_dvd_right ((ZMod.natCast_eq_zero_iff _ _).mp hz) _)
  rw [hb1, mul_one] at hb
  exact hb ▸ ⟨hr, hrq⟩


/-- A geometric sum of odd prime length cannot be a power of the next prime
in the indicated exponent range. The necessary congruence is modulo the cube of the successor prime. -/
def H1 : Prop :=
  ∀ p r b : ℕ, p.Prime → r.Prime → 5 ≤ r → Odd r →
    r ∣ nextPrime p - 1 → r - 1 < 2 * b → b < r - 1 →
    nextPrime p ^ 3 ∣ p ^ (nextPrime p - 1) - 1 →
    (∑ j ∈ range r, p ^ j) ≠ nextPrime p ^ b

/-- For a squarefree strongly connected component, consider at least three
vertices that are 5 modulo 6 with successors 1 modulo 6. Some successor must divide
the product of the quadratic factors to at least the third power. -/
def H2 : Prop :=
  ∀ S : Finset ℕ, 3 ≤ S.card →
    (∀ p ∈ S, p.Prime ∧ p % 6 = 5 ∧ nextPrime p % 6 = 1) →
    (∀ p ∈ S, ∀ q : ℕ, q.Prime → q ∣ p ^ 2 + p + 1 → ∃ u ∈ S, nextPrime u = q) →
    (∀ T : Finset ℕ, T ⊂ S → T.Nonempty →
      ∃ p ∈ T, ∃ u ∈ S, u ∉ T ∧ nextPrime u ∣ p ^ 2 + p + 1) →
    ∃ u ∈ S, 2 < ∑ p ∈ S, (p ^ 2 + p + 1).factorization (nextPrime u)

/-- An edge from p to u means that the successor of u divides the local
divisor sum at p. In a closed strongly connected set with at least two
vertices and a repeated prime factor, some shifted prime must occur more often than its available exponent. -/
def H3 : Prop :=
  ∀ (S : Finset ℕ) (e : ℕ → ℕ), 2 ≤ S.card →
    (∀ p ∈ S, p.Prime ∧ 0 < e p) →
    (∃ p ∈ S, 2 ≤ e p) →
    let G := fun p => ∑ j ∈ range (2 * e p + 1), p ^ j
    (∀ p ∈ S, ∀ q : ℕ, q.Prime → q ∣ G p → ∃ u ∈ S, nextPrime u = q) →
    (∀ T : Finset ℕ, T ⊂ S → T.Nonempty →
      ∃ p ∈ T, ∃ u ∈ S, u ∉ T ∧ nextPrime u ∣ G p) →
    ∃ u ∈ S, 2 * e u < ∑ p ∈ S, (G p).factorization (nextPrime u)

lemma geom_lt_succ_pow (p k : ℕ) (hp : 1 < p) :
    (∑ i ∈ range (k + 3), p ^ i) < (p + 1) ^ (k + 2) := by
  induction k with
  | zero =>
    simp [sum_range_succ]
    nlinarith
  | succ k ih =>
    rw [show k + 1 + 3 = (k + 3) + 1 by omega, sum_range_succ',
      show k + 1 + 2 = (k + 2) + 1 by omega, pow_succ]
    simp only [pow_succ p, ← sum_mul, pow_zero]
    have hpos : 0 < (p + 1) ^ (k + 2) := by positivity
    nlinarith [Nat.mul_le_mul_right p ih.le]

lemma singleton_obstruction (h₁ : H1) {p e : ℕ} (hp : p.Prime) (he : 0 < e)
    (hdvd : (∑ j ∈ range (2 * e + 1), p ^ j) ∣ nextPrime p ^ (2 * e)) : False := by
  let r := 2 * e + 1
  let q := nextPrime p
  have hr3 : 3 ≤ r := by dsimp [r]; omega
  obtain ⟨hpq, hq⟩ := next_spec p
  obtain ⟨hr, hrq⟩ := prime_length hp.one_lt hpq hq (m := r) (by omega) hdvd
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hq).mp hdvd
  change (∑ j ∈ range r, p ^ j) = q ^ b at hb
  obtain ⟨P, hP, hpP, hP2⟩ := Nat.exists_prime_lt_and_le_two_mul p hp.ne_zero
  have hq2p : q ≤ 2 * p := (next_le hpP hP).trans hP2
  have hlow := geom_mono_length p hr3
  rw [hb] at hlow
  simp [sum_range_succ] at hlow
  have hb2 : 2 ≤ b := by
    by_contra! h
    interval_cases b <;> simp_all <;> nlinarith [hp.two_le]
  have hbu : b < r - 1 := by
    by_contra! h
    have hu := geom_lt_succ_pow p (r - 3) hp.one_lt
    rw [show r - 3 + 3 = r by omega, show r - 3 + 2 = r - 1 by omega, hb] at hu
    exact hu.not_ge ((Nat.pow_le_pow_left hpq _).trans (Nat.pow_le_pow_right hq.pos h))
  have hr5 : 5 ≤ r := by dsimp [r] at hbu ⊢; omega
  have hbl : r - 1 < 2 * b := by
    by_contra! h
    have hq_sq : q ≤ p ^ 2 := by nlinarith [hp.two_le]
    have hpow : q ^ b ≤ p ^ (r - 1) := calc
      q ^ b ≤ (p ^ 2) ^ b := Nat.pow_le_pow_left hq_sq _
      _ = p ^ (2 * b) := (pow_mul _ _ _).symm
      _ ≤ p ^ (r - 1) := Nat.pow_le_pow_right hp.pos h
    have hpos := geom_large hp.one_lt (show 1 < 2 * e by omega)
    rw [← hb] at hpow
    change (∑ i ∈ range (2 * e + 1), p ^ i) ≤ p ^ (2 * e + 1 - 1) at hpow
    rw [sum_range_succ] at hpow
    simp only [Nat.add_sub_cancel] at hpow
    omega
  have hwie : q ^ 3 ∣ p ^ (q - 1) - 1 := by
    apply dvd_trans (pow_dvd_pow q (by omega : 3 ≤ b))
    apply dvd_trans _ (Nat.pow_sub_one_dvd_pow_sub_one p hrq)
    rw [← hb, ← geom_sum_mul_of_one_le hp.one_le r]
    exact dvd_mul_right _ _
  exact h₁ p r b hp hr hr5 ⟨e, rfl⟩ hrq hbl hbu hwie hb

lemma successor_injective {p u : ℕ} (hp : p.Prime) (hu : u.Prime)
    (he : nextPrime p = nextPrime u) : p = u := by
  rcases lt_trichotomy p u with h | h | h
  · have := next_le h hu
    have := (next_spec u).1
    omega
  · exact h
  · have := next_le h hp
    have := (next_spec p).1
    omega

lemma closed_subset_dvd {T S : Finset ℕ} {G B : ℕ → ℕ} (hTS : T ⊆ S)
    (hclosed : ∀ p ∈ T, ∀ u ∈ S, u ∉ T → ¬nextPrime u ∣ G p)
    (hd : (∏ p ∈ S, G p) ∣ ∏ u ∈ S, nextPrime u ^ B u) :
    (∏ p ∈ T, G p) ∣ ∏ u ∈ T, nextPrime u ^ B u := by
  have ht := (prod_dvd_prod_of_subset T S G hTS).trans hd
  rw [← prod_sdiff (f := fun u => nextPrime u ^ B u) hTS] at ht
  apply Nat.Coprime.dvd_of_dvd_mul_left _ ht
  apply Nat.coprime_prod_left_iff.mpr
  intro p hp
  apply Nat.coprime_prod_right_iff.mpr
  intro u hu
  obtain ⟨huS, huT⟩ := mem_sdiff.mp hu
  exact (((next_spec u).2.coprime_iff_not_dvd.mpr (hclosed p hp u huS huT)).symm).pow_right _

lemma shift_exponent (S : Finset ℕ) (B : ℕ → ℕ) (hS : ∀ p ∈ S, p.Prime)
    {u : ℕ} (hu : u ∈ S) :
    (∏ v ∈ S, nextPrime v ^ B v).factorization (nextPrime u) = B u := by
  rw [Nat.factorization_prod_apply (fun v _ => pow_ne_zero _ (next_spec v).2.ne_zero),
    sum_eq_single u]
  · exact Nat.factorization_pow_self (next_spec u).2
  · intro v hv hvu
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hd
    have he := (Nat.prime_dvd_prime_iff_eq (next_spec u).2 (next_spec v).2).mp
      ((next_spec u).2.dvd_of_dvd_pow hd)
    exact hvu (successor_injective (hS v hv) (hS u hu) he.symm)
  · exact fun hn => (hn hu).elim

lemma cubic_sum (p : ℕ) : (∑ j ∈ range 3, p ^ j) = p ^ 2 + p + 1 := by
  simp [sum_range_succ]
  omega

lemma next_value {p q : ℕ} (hpq : p < q) (hq : q.Prime)
    (hgap : ∀ k ∈ Ioo p q, ¬ k.Prime) : nextPrime p = q := by
  apply le_antisymm (next_le hpq hq)
  by_contra! h
  exact hgap _ (mem_Ioo.mpr ⟨(next_spec p).1, h⟩) (next_spec p).2

/-- The squares of squarefree integers can only give a counterexample if
every prime in the input is 5 modulo 6. -/
lemma squarefree_residues (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hd : (∏ p ∈ S, (p ^ 2 + p + 1)) ∣ ∏ u ∈ S, nextPrime u ^ 2) :
    ∀ p ∈ S, p % 6 = 5 := by
  have force {p u q : ℕ} (hp : p ∈ S) (hu : u.Prime) (huq : u < q)
      (hq : q.Prime) (hgap : ∀ k ∈ Ioo u q, ¬ k.Prime)
      (hfactor : q ∣ p ^ 2 + p + 1) : u ∈ S := by
    have h := (hfactor.trans (dvd_prod_of_mem (fun v => v ^ 2 + v + 1) hp)).trans hd
    obtain ⟨v, hv, hqv⟩ := (hq.prime.dvd_finsetProd_iff _).mp h
    have hnext := (Nat.prime_dvd_prime_iff_eq hq (next_spec v).2).mp (hq.dvd_of_dvd_pow hqv)
    rwa [successor_injective hu (hS v hv) ((next_value huq hq hgap).trans hnext)]
  have forceFive {p : ℕ} (hp : p ∈ S) (hf : 7 ∣ p ^ 2 + p + 1) : 5 ∈ S :=
    force hp (by decide) (by decide) (by decide) (by decide) hf
  have forceEleven {p : ℕ} (hp : p ∈ S) (hf : 13 ∣ p ^ 2 + p + 1) : 11 ∈ S :=
    force hp (by decide) (by decide) (by decide) (by decide) hf
  have forceTwentyNine (hp : 5 ∈ S) : 29 ∈ S :=
    force (q := 31) hp (by decide) (by decide) (by decide) (by decide) (by decide)
  have forceSixtyOne (hp : 29 ∈ S) : 61 ∈ S :=
    force (q := 67) hp (by decide) (by decide) (by decide) (by decide) (by decide)
  have noTwo : 2 ∉ S := by
    intro h2
    have h5 := forceFive h2 (by decide)
    have h29 := forceTwentyNine h5
    have h11 := forceEleven h29 (by decide)
    have h61 := forceSixtyOne h29
    have h89 : 89 ∈ S :=
      force (q := 97) h61 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h8009 : 8009 ∈ S :=
      force (q := 8011) h89 (by norm_num1) (by decide) (by norm_num1)
        (by intro k hk; obtain ⟨hl, hr⟩ := mem_Ioo.mp hk; interval_cases k; norm_num1)
        (by norm_num1)
    have h6659 : 6659 ∈ S :=
      force (q := 6661) h8009 (by norm_num1) (by decide) (by norm_num1)
        (by intro k hk; obtain ⟨hl, hr⟩ := mem_Ioo.mp hk; interval_cases k; norm_num1)
        (by norm_num1)
    have hs : ({2, 11, 6659} : Finset ℕ) ⊆ S := by
      intro a ha
      simp only [mem_insert, mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> assumption
    have hsmall : 7 ^ 3 ∣ ∏ p ∈ ({2, 11, 6659} : Finset ℕ), (p ^ 2 + p + 1) := by decide
    have hbig := (hsmall.trans (prod_dvd_prod_of_subset _ _ _ hs)).trans hd
    have hn : (∏ u ∈ S, nextPrime u ^ 2) ≠ 0 :=
      prod_ne_zero_iff.mpr (fun u _ => pow_ne_zero _ (next_spec u).2.ne_zero)
    have hv := (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 7) hn).mp hbig
    have hn5 : nextPrime 5 = 7 := next_value (by decide) (by decide) (by decide)
    rw [← hn5, shift_exponent S (fun _ => 2) hS h5] at hv
    omega
  have noOneModThree {p : ℕ} (hp : p ∈ S) (hr : p % 3 = 1) : False := by
    have hr' : p ≡ 1 [MOD 3] := hr
    have hd3 : 3 ∣ p ^ 2 + p + 1 := Nat.modEq_zero_iff_dvd.mp
      ((((hr'.pow 2).add hr').add (Nat.ModEq.refl 1)).trans (by decide))
    exact noTwo (force hp (by decide) (by decide) (by decide) (by decide) hd3)
  have noThree : 3 ∉ S := by
    intro h3
    have h11 := forceEleven h3 (by decide)
    have h61 := forceSixtyOne (forceTwentyNine (forceFive h11 (by decide)))
    exact noOneModThree h61 (by decide)
  intro p hp
  have hprime := hS p hp
  have hodd := hprime.eq_two_or_odd.resolve_left (fun h => noTwo (h ▸ hp))
  have h3 : ¬ 3 ∣ p := fun h => noThree
    (((Nat.prime_dvd_prime_iff_eq Nat.prime_three hprime).mp h).symm ▸ hp)
  have h1 : p % 3 ≠ 1 := noOneModThree hp
  have h0 : p % 3 ≠ 0 := fun h => h3 (Nat.dvd_of_mod_eq_zero h)
  have hm2 := Nat.mod_mod_of_dvd p (by decide : 2 ∣ 6)
  have hm3 := Nat.mod_mod_of_dvd p (by decide : 3 ∣ 6)
  have hb := Nat.mod_lt p (by decide : 0 < 6)
  generalize hres : p % 6 = v at hm2 hm3 hb ⊢
  interval_cases v <;> norm_num at hm2 hm3 ⊢ <;> first | exact h1 hm3.symm | omega

lemma cubic_prime_residue {p q : ℕ} (hq : q.Prime) (h3 : 3 < q)
    (hd : q ∣ p ^ 2 + p + 1) : q % 6 = 1 := by
  let : Fact q.Prime := ⟨hq⟩
  have hz := (ZMod.natCast_eq_zero_iff _ _).2 hd
  push_cast at hz
  have hp0 : (p : ZMod q) ≠ 0 := by
    intro h
    simp [h] at hz
  have hp1 : (p : ZMod q) ≠ 1 := by
    intro h
    rw [h] at hz
    have hz3 : ((3 : ℕ) : ZMod q) = 0 := by linear_combination hz
    exact Nat.not_dvd_of_pos_of_lt (by decide) h3 ((ZMod.natCast_eq_zero_iff _ _).mp hz3)
  have hp3 : (p : ZMod q) ^ 3 = 1 := by linear_combination ((p : ZMod q) - 1) * hz
  have hord : orderOf (p : ZMod q) = 3 := orderOf_eq_prime hp3 hp1
  have hd3 := ZMod.orderOf_dvd_card_sub_one hp0
  rw [hord] at hd3
  have hodd := hq.eq_two_or_odd.resolve_left (by omega)
  omega

/-- For the least vertex p, every possible prime divisor of its quadratic
factor exceeds p. A composite factor would therefore be at least (p+1)^2. -/
lemma least_cubic {S : Finset ℕ} {p : ℕ} (hprime : p.Prime)
    (hle : ∀ u ∈ S, p ≤ u)
    (hs : ∀ q : ℕ, q.Prime → q ∣ p ^ 2 + p + 1 → ∃ u ∈ S, nextPrime u = q) :
    ∃ u ∈ S, p < u ∧ nextPrime u = p ^ 2 + p + 1 := by
  let c := p ^ 2 + p + 1
  have hc : 1 < c := by dsimp [c]; nlinarith [hprime.two_le]
  have hcprime : c.Prime := by
    by_contra h
    have hm := Nat.minFac_sq_le_self (by omega : 0 < c) h
    obtain ⟨v, hv, hvm⟩ := hs c.minFac (Nat.minFac_prime (by omega)) (Nat.minFac_dvd _)
    have hlt : p < c.minFac := (hle v hv).trans_lt (hvm ▸ (next_spec v).1)
    have hsq := Nat.pow_le_pow_left (show p + 1 ≤ c.minFac by omega) 2
    have hshort := hsq.trans hm
    change (p + 1) ^ 2 ≤ p ^ 2 + p + 1 at hshort
    nlinarith only [hshort, hprime.two_le]
  obtain ⟨u, hu, huc⟩ := hs c hcprime dvd_rfl
  have hne : p ≠ u := by
    rintro rfl
    obtain ⟨v, hv, huv, hv2⟩ := Nat.exists_prime_lt_and_le_two_mul p hprime.ne_zero
    have := (next_le huv hv).trans hv2
    dsimp [c] at huc
    nlinarith [hprime.two_le]
  exact ⟨u, hu, lt_of_le_of_ne (hle u hu) hne, huc⟩

/-- If the least vertex p has successor-prime Q = p^2+p+1 at vertex u,
that same Q cannot divide u^2+u+1. The other root modulo Q is p^2. -/
lemma successor_not_factor {p u : ℕ} (hp : p.Prime) (hu : u.Prime) (hpu : p < u)
    (he : nextPrime u = p ^ 2 + p + 1) : ¬nextPrime u ∣ u ^ 2 + u + 1 := by
  intro hd
  let q := nextPrime u
  have huq : u < q := (next_spec u).1
  have hq : q.Prime := (next_spec u).2
  have hdif : q ∣ (u - p) * (u + p + 1) := by
    have hsub := Nat.sub_add_cancel hpu.le
    have hid : (u - p) * (u + p + 1) + q = u ^ 2 + u + 1 := by
      change (u - p) * (u + p + 1) + nextPrime u = _
      rw [he]
      nlinarith only [congrArg (fun t : ℕ => t * (u + p + 1)) hsub]
    exact (Nat.dvd_add_left (dvd_refl q)).mp (hid ▸ hd)
  rcases hq.dvd_mul.mp hdif with h | h
  · exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) h
  · obtain ⟨k, hk⟩ := h
    have hk1 : k = 1 := by
      by_contra! hk1
      rcases k with _ | k
      · simp at hk
      · have h2 : 2 ≤ k + 1 := by omega
        have := Nat.mul_le_mul_left q h2
        omega
    rw [hk1, mul_one] at hk
    have husq : u = p ^ 2 := by change u + p + 1 = nextPrime u at hk; omega
    have hpd : p ∣ u := husq ▸ dvd_pow_self p (by decide : 2 ≠ 0)
    exact hpu.ne ((Nat.prime_dvd_prime_iff_eq hp hu).mp hpd)

/-- Two squarefree vertices do not have enough capacity. After the larger
successor is excluded from the larger quadratic, only the smaller successor
squared remains, which is at most u^2. -/
lemma squarefree_card {S : Finset ℕ} (hc : 2 ≤ S.card) (hS : ∀ p ∈ S, p.Prime)
    (hs : ∀ p ∈ S, ∀ q : ℕ, q.Prime → q ∣ p ^ 2 + p + 1 → ∃ u ∈ S, nextPrime u = q)
    (hd : (∏ p ∈ S, (p ^ 2 + p + 1)) ∣ ∏ v ∈ S, nextPrime v ^ 2) : 3 ≤ S.card := by
  by_contra! h
  have hne : S.Nonempty := card_pos.mp (by omega)
  let p := S.min' hne
  have hp : p ∈ S := min'_mem _ _
  obtain ⟨u, hu, hpu, he⟩ := least_cubic (hS p hp) (fun v hv => min'_le _ _ hv) (hs p hp)
  have hsub : ({p, u} : Finset ℕ) ⊆ S := by
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl <;> assumption
  have hpair : ({p, u} : Finset ℕ) = S := eq_of_subset_of_card_le hsub (by simp [hpu.ne]; omega)
  have hd' := (dvd_prod_of_mem (fun v => v ^ 2 + v + 1) hu).trans hd
  rw [← hpair] at hd'
  simp only [prod_insert (by simpa using hpu.ne : p ∉ ({u} : Finset ℕ)), prod_singleton] at hd'
  have hn := successor_not_factor (hS p hp) (hS u hu) hpu he
  have hcop := ((next_spec u).2.coprime_iff_not_dvd.mpr hn).symm.pow_right 2
  have hdsmall := hcop.dvd_of_dvd_mul_right hd'
  have hle := Nat.le_of_dvd (pow_pos (next_spec p).2.pos 2) hdsmall
  have hsq := Nat.pow_le_pow_left (next_le hpu (hS u hu)) 2
  omega

lemma factor_obstruction (h₁ : H1) (h₂ : H2) (h₃ : H3) (S : Finset ℕ) (e : ℕ → ℕ) :
    S.Nonempty → (∀ p ∈ S, p.Prime ∧ 0 < e p) →
    ¬ (∏ p ∈ S, ∑ j ∈ range (2 * e p + 1), p ^ j) ∣
      ∏ u ∈ S, nextPrime u ^ (2 * e u) := by
  let G := fun p => ∑ j ∈ range (2 * e p + 1), p ^ j
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hne hS hd
    change (∏ p ∈ S, G p) ∣ _ at hd
    by_cases hsingle : S.card = 1
    · obtain ⟨p, rfl⟩ := card_eq_one.mp hsingle
      obtain ⟨hp, he⟩ := hS p (mem_singleton_self _)
      exact singleton_obstruction h₁ hp he (by simpa [G] using hd)
    have hc : 2 ≤ S.card := by have := hne.card_pos; omega
    by_cases hconn : ∀ T : Finset ℕ, T ⊂ S → T.Nonempty →
      ∃ p ∈ T, ∃ u ∈ S, u ∉ T ∧ nextPrime u ∣ G p
    · have hsupport : ∀ p ∈ S, ∀ q : ℕ, q.Prime → q ∣ G p → ∃ u ∈ S, nextPrime u = q := by
        intro p hp q hq hqp
        have hdiv := (hqp.trans (dvd_prod_of_mem G hp)).trans hd
        obtain ⟨u, hu, hqu⟩ := (hq.prime.dvd_finsetProd_iff _).mp hdiv
        exact ⟨u, hu, ((Nat.prime_dvd_prime_iff_eq hq (next_spec u).2).mp
          (hq.dvd_of_dvd_pow hqu)).symm⟩
      have overflow : ∃ u ∈ S, 2 * e u < ∑ p ∈ S, (G p).factorization (nextPrime u) := by
        by_cases hrepeated : ∃ p ∈ S, 2 ≤ e p
        · exact h₃ S e hc hS hrepeated hsupport hconn
        push Not at hrepeated
        have he (p : ℕ) (hp : p ∈ S) : e p = 1 := by
          have := hrepeated p hp
          have := (hS p hp).2
          omega
        have hg (p : ℕ) (hp : p ∈ S) : G p = p ^ 2 + p + 1 := by
          simp only [G, he p hp]
          exact cubic_sum p
        have hleft := prod_congr (s₁ := S) rfl hg
        have hright : (∏ u ∈ S, nextPrime u ^ (2 * e u)) = ∏ u ∈ S, nextPrime u ^ 2 := by
          exact prod_congr rfl (fun u hu => by rw [he u hu, mul_one])
        have hsquares := hd
        rw [hleft, hright] at hsquares
        have hr := squarefree_residues S (fun p hp => (hS p hp).1) hsquares
        have hres (u : ℕ) (hu : u ∈ S) : nextPrime u % 6 = 1 := by
          have ht := (Finset.one_lt_card_iff_nontrivial.mp hc).erase_nonempty (a := u)
          obtain ⟨p, hp, v, hv, hve, hvp⟩ := hconn (S.erase u) (erase_ssubset hu) ht
          obtain rfl := eq_of_mem_of_notMem_erase hv hve
          rw [hg p (mem_of_mem_erase hp)] at hvp
          have := hr v hv
          have := (next_spec v).1
          exact cubic_prime_residue (next_spec v).2 (by omega) hvp
        have hs (p : ℕ) (hp : p ∈ S) (q : ℕ) (hq : q.Prime) (hqg : q ∣ p ^ 2 + p + 1) :=
          hsupport p hp q hq ((hg p hp).symm ▸ hqg)
        have hcard := squarefree_card hc (fun p hp => (hS p hp).1) hs hsquares
        obtain ⟨u, hu, ho⟩ := h₂ S hcard (fun p hp => ⟨(hS p hp).1, hr p hp, hres p hp⟩) hs
          (fun T hTS hT => by
            obtain ⟨p, hp, u, hu, hout, hdiv⟩ := hconn T hTS hT
            exact ⟨p, hp, u, hu, hout, hg p (hTS.subset hp) ▸ hdiv⟩)
        refine ⟨u, hu, ?_⟩
        rwa [he u hu, mul_one, sum_congr rfl (fun p hp => congrArg
          (fun k : ℕ => k.factorization (nextPrime u)) (hg p hp))]
      obtain ⟨u, hu, hover⟩ := overflow
      change 2 * e u < ∑ p ∈ S, (G p).factorization (nextPrime u) at hover
      have hg0 (p : ℕ) (hp : p ∈ S) : G p ≠ 0 := by
        have := (hS p hp).2
        exact (lt_trans Nat.zero_lt_one (geom_large (hS p hp).1.one_lt (by omega : 1 < 2 * e p + 1))).ne'
      have hle := (Nat.factorization_le_iff_dvd
        (Finset.prod_ne_zero_iff.mpr hg0)
        (Finset.prod_ne_zero_iff.mpr (fun v _ => pow_ne_zero _ (next_spec v).2.ne_zero))).mpr hd
      have hval := hle (nextPrime u)
      rw [Nat.factorization_prod_apply hg0,
        shift_exponent S _ (fun p hp => (hS p hp).1) hu] at hval
      exact hover.not_ge hval
    · push Not at hconn
      obtain ⟨T, hTS, hTne, hn⟩ := hconn
      apply ih T hTS hTne (fun p hp => hS p (hTS.subset hp))
      exact closed_subset_dvd hTS.subset hn hd

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a350072.main := by
  intro h₁ h₂ h₃ n hn ha
  have hn0 : n ≠ 0 := by omega
  have hg := Nat.div_mul_cancel (Nat.gcd_dvd_left (ArithmeticFunction.sigma 1 (n ^ 2))
    (shift (n ^ 2)))
  unfold a at ha
  rw [ha, one_mul] at hg
  have hd := Nat.gcd_dvd_right (ArithmeticFunction.sigma 1 (n ^ 2)) (shift (n ^ 2))
  rw [hg] at hd
  rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
    (pow_ne_zero _ hn0), shift, Nat.primeFactors_pow n (by decide : 2 ≠ 0),
    Nat.factorization_pow] at hd
  simp only [mul_one, Finsupp.smul_apply, smul_eq_mul] at hd
  exact factor_obstruction h₁ h₂ h₃ n.primeFactors (fun p => n.factorization p)
    (Nat.nonempty_primeFactors.mpr hn) (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp,
      (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hp)⟩) hd

end OMA.R_oeis_a350072_R1
