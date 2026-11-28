import OMAStatements.S_oeis_a007850
import Mathlib

/-!
# A reduction of Lava's arithmetic - derivative conjecture

Grau and Oller - Marcén characterized Giuga numbers by `n′ = a * n + 1` with `a > 0`
and discuss the earlier 59 - factor bound. We prove their characterization, use
explicit reciprocal - sum estimates and a congruence modulo a primorial to exclude
at most 59 factors, and split the odd case by the parity of the number of factors.

Source: https://oeis.org/A007850
Reference: https://cs.uwaterloo.ca/journals/JIS/VOL15/Oller/oller5.pdf
Credit: @frido22
-/

namespace OMA.GiugaDeriv

open Finset OMA.S_oeis_a007850

/-- All prime - factor summands except the `p` term vanish modulo `p`. -/
lemma derivative_at_prime {n p : ℕ} (hp : p ∈ n.primeFactors) :
    arithDeriv n ≡ n.factorization p * (n / p) [MOD p] := by
  let f := fun q => n.factorization q * (n / q)
  have div : p ∣ ∑ q ∈ n.primeFactors.erase p, f q := by
    apply Finset.dvd_sum
    intro q hq
    obtain ⟨ne, mem⟩ := Finset.mem_erase.mp hq
    have pq := Nat.Prime.dvd_mul_of_dvd_ne ne.symm (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors mem) (Nat.dvd_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors mem)
    apply dvd_mul_of_dvd_right _ (n.factorization q)
    exact (Nat.dvd_div_iff_mul_dvd (Nat.dvd_of_mem_primeFactors mem)).mpr (by simpa [Nat.mul_comm] using pq)
  change (∑ q ∈ n.primeFactors, f q) ≡ f p [MOD p]
  rw [← Finset.sum_erase_add _ f hp]
  simpa only [zero_add] using (Nat.modEq_zero_iff_dvd.mpr div).add_right (f p)

lemma giuga_squarefree {n : ℕ} (h : IsGiuga n) : Squarefree n := by
  obtain ⟨hn, _, cond⟩ := h
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro p prime repeated
  have dp : p ∣ n := (dvd_mul_right p p).trans repeated
  have dn := (Nat.dvd_div_iff_mul_dvd dp).mpr repeated
  have pos : 0 < n / p := Nat.div_pos (Nat.le_of_dvd (by omega) dp) prime.pos
  have gap := cond p (Nat.mem_primeFactors.mpr ⟨prime, dp, by omega⟩)
  have d := Nat.dvd_sub dn gap
  have : p ∣ 1 := by rwa [show n / p - (n / p - 1) = 1 by omega] at d
  exact prime.not_dvd_one this

lemma squarefree_of_residue {n a : ℕ} (hn : 0 < n) (eq : arithDeriv n = a * n + 1) : Squarefree n := by
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro p prime repeated
  have dp : p ∣ n := (dvd_mul_right p p).trans repeated
  have dn := (Nat.dvd_div_iff_mul_dvd dp).mpr repeated
  have res := derivative_at_prime (Nat.mem_primeFactors.mpr ⟨prime, dp, hn.ne'⟩)
  have zd := (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right dn (n.factorization p)))
  have dz := Nat.modEq_zero_iff_dvd.mp (res.trans zd)
  have da : p ∣ a * n := dvd_mul_of_dvd_right dp a
  rw [eq] at dz
  exact prime.not_dvd_one (by simpa using (Nat.dvd_sub dz da))

private lemma derivative_of_squarefree {n : ℕ} (sf : Squarefree n) :
    arithDeriv n = ∑ p ∈ n.primeFactors, n / p := by
  apply sum_congr rfl
  intro p mem
  simp [Nat.factorization_eq_one_of_squarefree sf (Nat.prime_of_mem_primeFactors mem)
    (Nat.dvd_of_mem_primeFactors mem)]

private lemma derivative_at_prime_of_squarefree {n p : ℕ} (sf : Squarefree n) (mem : p ∈ n.primeFactors) :
    arithDeriv n ≡ n / p [MOD p] := by
  simpa [Nat.factorization_eq_one_of_squarefree sf (Nat.prime_of_mem_primeFactors mem)
    (Nat.dvd_of_mem_primeFactors mem)] using derivative_at_prime mem

/-- The positive - multiplier characterization of Grau and Oller - Marcén. -/
lemma giuga_iff_multiplier {n : ℕ} (hn : 0 < n) :
    IsGiuga n ↔ ∃ a : ℕ, 0 < a ∧ arithDeriv n = a * n + 1 := by
  constructor
  · intro h
    have sf := giuga_squarefree h
    obtain ⟨large, composite, cond⟩ := h
    obtain ⟨p, mem⟩ := Nat.nonempty_primeFactors.mpr large
    have prime := Nat.prime_of_mem_primeFactors mem
    have dp := Nat.dvd_of_mem_primeFactors mem
    have qpos := Nat.div_pos (Nat.le_of_mem_primeFactors mem) prime.pos
    have qbig : 1 < n / p := by
      by_contra! hq
      have eq := Nat.div_mul_cancel dp
      rw [show n / p = 1 by omega, one_mul] at eq
      exact composite (eq ▸ prime)
    have big : 1 < arithDeriv n := by
      rw [derivative_of_squarefree sf]
      exact qbig.trans_le (single_le_sum (fun _ _ => Nat.zero_le _) mem)
    have div : n ∣ arithDeriv n - 1 := by
      have pos : arithDeriv n - 1 ≠ 0 := by omega
      nth_rw 1 [← Nat.prod_primeFactors_of_squarefree sf]
      rw [Nat.prod_primeFactors_dvd_iff pos]
      intro q hq
      have qp := Nat.prime_of_mem_primeFactors hq
      apply Nat.mem_primeFactors.mpr
      refine ⟨qp, ?_, pos⟩
      have qpos := Nat.div_pos (Nat.le_of_mem_primeFactors hq) qp.pos
      have rem := (Nat.modEq_iff_dvd' (show 1 ≤ n / q by omega)).mpr (cond q hq)
      exact (rem.trans (derivative_at_prime_of_squarefree sf hq).symm).dvd'
    obtain ⟨a, eq⟩ := div
    refine ⟨a, ?_, ?_⟩
    · by_contra! ha
      simp [show a = 0 by omega] at eq
      omega
    · rw [Nat.mul_comm] at eq
      omega
  · rintro ⟨a, ha, eq⟩
    have large : 1 < n := by
      by_contra! hn'
      simp_all [show n = 1 by omega, arithDeriv]
    have composite : ¬ n.Prime := by
      intro prime
      have val : arithDeriv n = 1 := by simp [arithDeriv, prime, prime.pos]
      have := Nat.mul_pos ha hn
      omega
    refine ⟨large, composite, ?_⟩
    intro p mem
    have atp := derivative_at_prime_of_squarefree (squarefree_of_residue hn eq) mem
    have da : p ∣ a * n := dvd_mul_of_dvd_right (Nat.dvd_of_mem_primeFactors mem) a
    rw [eq] at atp
    have res : 1 ≡ a * n + 1 [MOD p] := by
      simpa using ((Nat.modEq_zero_iff_dvd.mpr da).symm.add_right 1)
    exact (res.trans atp).dvd'

lemma derivative_ratio {n : ℕ} (sf : Squarefree n) :
    (arithDeriv n : ℚ) = (∑ p ∈ n.primeFactors, (1 / (p : ℚ))) * n := by
  rw [derivative_of_squarefree sf, Nat.cast_sum, sum_mul]
  apply sum_congr rfl
  intro p mem
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_primeFactors mem).ne'
  rw [Nat.cast_div (Nat.dvd_of_mem_primeFactors mem) hp]
  ring

/-- An integer upper bound for the excess of `cutoff * scale / p` over `scale`. -/
private def extra (cutoff scale p : ℕ) := cutoff * scale / p + 1 - scale

/-- A finite sieve used only for upper bounds. Its being a superset of the primes
is enough for all the estimates below. -/
private def passesSieve (p : ℕ) : Bool := decide (2 ≤ p) &&
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107].all
    (fun d : ℕ => decide (d ≤ 1 ∨ d = p ∨ p % d ≠ 0))

private lemma prime_passes {p : ℕ} (hp : p.Prime) : passesSieve p = true := by
  unfold passesSieve
  rw [Bool.and_eq_true]
  refine ⟨decide_eq_true hp.two_le, List.all_eq_true.mpr ?_⟩
  intro d _
  apply decide_eq_true
  by_contra! fail
  have div : d ∣ p := Nat.dvd_iff_mod_eq_zero.mpr fail.2.2
  obtain eq | eq := (Nat.dvd_prime hp).mp div <;> omega

private def primeBudget (cutoff scale skip : ℕ) : ℕ :=
  ∑ p ∈ (range cutoff).filter (fun p => passesSieve p = true ∧ p ≠ skip), extra cutoff scale p

private lemma weight_bound (cutoff scale p : ℕ) (hp : 0 < p) :
    cutoff * scale ≤ p * (scale + if p < cutoff then extra cutoff scale p else 0) := by
  by_cases h : p < cutoff
  · rw [if_pos h]
    have round : cutoff * scale < p * (cutoff * scale / p + 1) := calc
      _ = p * (cutoff * scale / p) + cutoff * scale % p := (Nat.div_add_mod _ _).symm
      _ < p * (cutoff * scale / p) + p := Nat.add_lt_add_left (Nat.mod_lt _ hp) _
      _ = _ := by ring
    exact round.le.trans (Nat.mul_le_mul_left p (by unfold extra; omega))
  · simpa [h] using Nat.mul_le_mul_right scale (Nat.le_of_not_gt h)

private lemma reciprocal_budget (S : Finset ℕ) {cutoff scale skip : ℕ}
    (primes : ∀ p ∈ S, p.Prime) (except : ∀ p ∈ S, p ≠ skip) :
    (∑ p ∈ S, (1 / (p : ℚ))) * (cutoff * scale : ℕ) ≤ (S.card * scale + primeBudget cutoff scale skip : ℕ) := by
  let f := fun p => if p < cutoff then extra cutoff scale p else 0
  have total : ∑ p ∈ S, f p ≤ primeBudget cutoff scale skip := by
    unfold primeBudget
    dsimp [f]
    rw [← sum_filter]
    apply sum_le_sum_of_subset
    intro p mem
    obtain ⟨fac, small⟩ := mem_filter.mp mem
    exact mem_filter.mpr ⟨mem_range.mpr small, prime_passes (primes p fac), except p fac⟩
  rw [sum_mul]
  calc
    _ ≤ ∑ p ∈ S, ((scale + f p : ℕ) : ℚ) := by
      apply sum_le_sum
      intro p hp
      have pp : 0 < (p : ℚ) := by exact_mod_cast (primes p hp).pos
      rw [one_div_mul_eq_div]
      apply (div_le_iff₀ pp).mpr
      exact_mod_cast (show cutoff * scale ≤ (scale + f p) * p by simpa only [Nat.mul_comm _ p] using weight_bound cutoff scale p (primes p hp).pos)
    _ ≤ _ := by
      rw [← Nat.cast_sum, sum_add_distrib]
      simpa using (Nat.cast_le (α:=ℚ)).mpr (Nat.add_le_add_left total (S.card * scale))

private lemma derivative_lt_of_sum_lt {n rate : ℕ} (sf : Squarefree n)
    (bound : (∑ p ∈ n.primeFactors, (1 / (p : ℚ))) < rate) : arithDeriv n < rate * n := by
  have positive : (0 : ℚ) < n := by exact_mod_cast sf.ne_zero.bot_lt
  have scaled := mul_lt_mul_of_pos_right bound positive
  rw [← derivative_ratio sf] at scaled
  exact_mod_cast scaled

private lemma derivative_lt_budget {n cutoff scale skip rate : ℕ} (sf : Squarefree n)
    (except : ∀ p ∈ n.primeFactors, p ≠ skip)
    (cert : n.primeFactors.card * scale + primeBudget cutoff scale skip < rate * (cutoff * scale)) :
    arithDeriv n < rate * n := by
  have bound := reciprocal_budget n.primeFactors (fun _ hp => Nat.prime_of_mem_primeFactors hp) except
    (cutoff := cutoff) (scale := scale)
  have pos : 0 < cutoff * scale := by
    by_contra! zero
    rw [show cutoff * scale = 0 by omega, Nat.mul_zero] at cert
    omega
  have pos' : (0 : ℚ) < (cutoff * scale : ℕ) := by exact_mod_cast pos
  apply derivative_lt_of_sum_lt sf
  apply (mul_lt_mul_iff_left₀ pos').mp
  exact bound.trans_lt (by exact_mod_cast cert)

private def smallPrimes := (range 168).filter Nat.Prime
private def primorial := ∏ p ∈ smallPrimes, p
private def residue : ℕ := 241154391290894464663467115463743362761848622423921060203644724609

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma missing_budget : ∀ p ∈ smallPrimes,
    59 * 10000 + primeBudget 281 10000 p < 2 * (281 * 10000) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma rest_budget : 1000 * (58 * 10000 + primeBudget 277 10000 1) <
    1999 * (277 * 10000) := by decide +kernel

private lemma small_forced {n : ℕ} (h : IsGiuga n) (count : n.primeFactors.card ≤ 59)
    (large : 2 * n ≤ arithDeriv n) : smallPrimes ⊆ n.primeFactors := by
  intro p hp
  by_contra absent
  have cert := (Nat.add_le_add_right (Nat.mul_le_mul_right 10000 count) _).trans_lt (missing_budget p hp)
  exact large.not_gt (derivative_lt_budget (cutoff := 281) (scale := 10000) (skip := p)
    (giuga_squarefree h) (by rintro q mem rfl; exact absent mem) cert)

private lemma primes_below_thousand {n : ℕ} (h : IsGiuga n) (count : n.primeFactors.card ≤ 59)
    (large : 2 * n ≤ arithDeriv n) {p : ℕ} (mem : p ∈ n.primeFactors) : p < 1000 := by
  by_contra! big
  let S := n.primeFactors.erase p
  have Ssize : S.card ≤ 58 := by dsimp [S]; rw [card_erase_of_mem mem]; omega
  have pr : ∀ q ∈ S, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors (mem_erase.mp hq).2
  have budget := reciprocal_budget S (cutoff:=277) (scale:=10000) pr (fun q hq => (pr q hq).ne_one)
  have ub : 1000 * (S.card * 10000 + primeBudget 277 10000 1) < 1999 * (277 * 10000) :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_right _ Ssize) _)) rest_budget
  have qbound : (∑ q ∈ S, (1 / (q:ℚ))) < 1999 / 1000 := by
    have ub' := (Nat.cast_lt (α:=ℚ)).mpr ub
    push_cast at budget ub'
    linarith
  have pbig : (1000:ℚ) ≤ (p:ℚ) := by exact_mod_cast big
  have frac : 1 / (p:ℚ) ≤ 1 / 1000 := one_div_le_one_div_of_le (by norm_num) pbig
  have all : (∑ q ∈ n.primeFactors, (1 / (q:ℚ))) < 2 := by
    rw [← sum_erase_add _ _ mem]
    change (∑ q ∈ S, (1 / (q:ℚ))) + _ < _
    linarith
  have nn : (0:ℚ) < n := by exact_mod_cast (Nat.zero_lt_of_lt h.1)
  have dl := mul_lt_mul_of_pos_right all nn
  rw [← derivative_ratio (giuga_squarefree h)] at dl
  exact (not_lt_of_ge large) (by exact_mod_cast dl)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma fixed_data : smallPrimes.card = 39 ∧ 1000 ^ 20 < residue ∧ residue < primorial ∧
    ∀ p ∈ smallPrimes, (primorial / p) * residue ≡ 1 [MOD p] := by decide +kernel

/-- For the 39 forced primes, the cofactor has a single residue modulo their
product. That residue is larger than any possible product of the other 20 primes. -/
lemma lt_two_of_card_le_59 {n : ℕ} (h : IsGiuga n) (count : n.primeFactors.card ≤ 59) :
    arithDeriv n < 2 * n := by
  by_contra! large
  have forced := small_forced h count large
  have below {q : ℕ} (hq : q ∈ n.primeFactors) := primes_below_thousand h count large hq
  let S := n.primeFactors \ smallPrimes
  let m := ∏ p ∈ S, p
  obtain ⟨c39, bigR, rm, residues⟩ := fixed_data
  have size : S.card ≤ 20 := by dsimp [S]; rw [card_sdiff_of_subset forced, c39]; omega
  have upper : m ≤ 1000 ^ 20 := calc
    m ≤ ∏ _p ∈ S, 1000 := by exact Finset.prod_le_prod' fun p hp => (below (mem_sdiff.mp hp).1).le
    _ = 1000 ^ S.card := by simp
    _ ≤ _ := Nat.pow_le_pow_right (by decide) size
  have split : m * primorial = n := by
    change (∏ p ∈ n.primeFactors \ smallPrimes, p) * (∏ p ∈ smallPrimes, p) = n
    rw [prod_sdiff forced, Nat.prod_primeFactors_of_squarefree (giuga_squarefree h)]
  have small_prime : ∀ p ∈ smallPrimes, p.Prime := fun _ hp => (mem_filter.mp hp).2
  have pf : primorial.primeFactors = smallPrimes := Nat.primeFactors_prod small_prime
  have rid : primorial ∣ residue - m := by
    have dif : residue - m ≠ 0 := by omega
    have div : (∏ p ∈ primorial.primeFactors, p) ∣ residue - m := by
      apply (Nat.prod_primeFactors_dvd_iff dif).mpr
      intro p hp
      rw [pf] at hp
      have prime := small_prime p hp
      have dp : p ∣ primorial := Finset.dvd_prod_of_mem (fun p : ℕ => p) hp
      have dN := forced hp
      have pos := Nat.div_pos (Nat.le_of_mem_primeFactors dN) prime.pos
      have gm := ((Nat.modEq_iff_dvd' pos).mpr (h.2.2 p dN)).symm
      have factor : n / p = m * (primorial / p) := by rw [← split, Nat.mul_div_assoc _ dp]
      rw [factor] at gm
      have res := residues p hp
      have mod : m ≡ residue [MOD p] := calc
        m ≡ m * ((primorial / p) * residue) [MOD p] := by simpa using res.symm.mul_left m
        _ = (m * (primorial / p)) * residue := by ring
        _ ≡ residue [MOD p] := by simpa using gm.mul_right residue
      exact Nat.mem_primeFactors.mpr ⟨prime, mod.dvd', dif⟩
    rw [pf] at div
    exact div
  have lb := Nat.le_of_dvd (by omega : 0 < residue - m) rid
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma odd_budget : 1411 * 10000 + primeBudget 11789 10000 2 < 2 * (11789 * 10000) := by
  decide +kernel

lemma lt_two_of_odd_card_le {n : ℕ} (h : IsGiuga n) (odd : Odd n) (count : n.primeFactors.card ≤ 1411) :
    arithDeriv n < 2 * n := by
  apply derivative_lt_budget (skip := 2) (cutoff := 11789) (scale := 10000) (giuga_squarefree h)
  · rintro p mem rfl
    exact (Nat.not_even_iff_odd.mpr odd) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors mem))
  · exact (Nat.add_le_add_right (Nat.mul_le_mul_right _ count) _).trans_lt odd_budget

lemma lava_of_bound {n : ℕ} (h : IsGiuga n) (bound : arithDeriv n < 2 * n) : arithDeriv n = n + 1 := by
  have hn : 0 < n := Nat.zero_lt_of_lt h.1
  obtain ⟨a, ha, eq⟩ := (giuga_iff_multiplier hn).mp h
  have one : a = 1 := by
    by_contra! ne
    have lb := Nat.mul_le_mul_right n (show 2 ≤ a by omega)
    omega
  simpa [one] using eq

/-- For odd `n`, each summand `n / p` is odd. An even number of factors thus
forces the multiplier in `n′ = a * n + 1` to be odd. -/
lemma lava_of_even_card {n : ℕ} (h : IsGiuga n) (odd : Odd n) (ec : Even n.primeFactors.card)
    (bound : arithDeriv n < 3 * n) : arithDeriv n = n + 1 := by
  have sf := giuga_squarefree h
  have all : n.primeFactors.filter (fun p => Odd (n / p)) = n.primeFactors := by
    apply filter_eq_self.mpr
    intro p hp
    have prod_odd : Odd ((n / p) * p) := by rwa [Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp)]
    exact (Nat.odd_mul.mp prod_odd).1
  have evenD : Even (arithDeriv n) := by
    rwa [derivative_of_squarefree sf, even_sum_iff_even_card_odd, all]
  obtain ⟨a, ha, eq⟩ := (giuga_iff_multiplier (Nat.zero_lt_of_lt h.1)).mp h
  have one : a = 1 := by
    have small : a < 3 := by
      by_contra! big
      have := Nat.mul_le_mul_right n big
      omega
    by_contra! ne
    have two : a = 2 := by omega
    rw [two] at eq
    rw [Nat.even_iff] at evenD
    omega
  simpa [one] using eq

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma odd_even_budget : 13200 * 10000 + primeBudget 11789 10000 2 < 3 * (11789 * 10000) := by
  decide +kernel

lemma lt_three_of_odd_card_le {n : ℕ} (h : IsGiuga n) (odd : Odd n) (count : n.primeFactors.card ≤ 13200) :
    arithDeriv n < 3 * n := by
  apply derivative_lt_budget (skip := 2) (cutoff := 11789) (scale := 10000) (giuga_squarefree h)
  · rintro p mem rfl
    exact (Nat.not_even_iff_odd.mpr odd) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors mem))
  · exact (Nat.add_le_add_right (Nat.mul_le_mul_right 10000 count) _).trans_lt odd_even_budget

end OMA.GiugaDeriv

namespace OMA.R_oeis_a007850_R1

open OMA.S_oeis_a007850 OMA.GiugaDeriv Finset

/-- The remaining even inputs have at least 60 prime factors. -/
def H1 : Prop := ∀ n : ℕ, IsGiuga n → Even n → 60 ≤ n.primeFactors.card →
  (∑ p ∈ n.primeFactors, (1 / (p : ℚ))) < 2

/-- Odd inputs with an odd number of prime factors. -/
def H2 : Prop := ∀ n : ℕ, IsGiuga n → Odd n → Odd n.primeFactors.card → 1413 ≤ n.primeFactors.card →
  (∑ p ∈ n.primeFactors, (1 / (p : ℚ))) < 2

/-- Odd inputs with an even number of prime factors admit the weaker upper bound 3. -/
def H3 : Prop := ∀ n : ℕ, IsGiuga n → Odd n → Even n.primeFactors.card → 13202 ≤ n.primeFactors.card →
  (∑ p ∈ n.primeFactors, (1 / (p : ℚ))) < 3

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a007850.main := by
  intro even_case odd_card even_card n hn
  constructor
  · intro h
    have sf := giuga_squarefree h
    rcases Nat.even_or_odd n with ev | od
    · apply lava_of_bound h
      by_cases few : n.primeFactors.card ≤ 59
      · exact lt_two_of_card_le_59 h few
      · exact derivative_lt_of_sum_lt sf (even_case n h ev (by omega))
    rcases Nat.even_or_odd n.primeFactors.card with ec | oc
    · apply lava_of_even_card h od ec
      by_cases few : n.primeFactors.card ≤ 13200
      · exact lt_three_of_odd_card_le h od few
      · exact derivative_lt_of_sum_lt sf (even_card n h od ec (by rw [Nat.even_iff] at ec; omega))
    · apply lava_of_bound h
      by_cases few : n.primeFactors.card ≤ 1411
      · exact lt_two_of_odd_card_le h od few
      · exact derivative_lt_of_sum_lt sf (odd_card n h od oc (by rw [Nat.odd_iff] at oc; omega))
  · intro eq
    exact (giuga_iff_multiplier hn).mpr ⟨1, by decide, by simpa using eq⟩

end OMA.R_oeis_a007850_R1
