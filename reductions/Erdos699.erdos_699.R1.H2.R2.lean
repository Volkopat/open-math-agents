import OMAReductions.R_Erdos699_erdos_699_R1
import Mathlib.NumberTheory.SmoothNumbers

/-!
# Erdős 699, far range: symmetric cancellation and the index three

Credit: @huurou

Write `A = C(n,i)`, `B = C(n,j)` and `c = gcd(A, C(j,i), C(n-j,i))`.
Both binomial cancellation identities imply `A/c ∣ gcd(A,B)`. Thus any prime
at least `i` in this single quotient settles the problem. If the quotient is
`i`-smooth (all prime factors strictly below `i`), only `gcd(c,B)` remains to
inspect, not the full coefficients. This test uses the complementary column
`n-j` and not just `j`. For example at `(n,i,j)=(57,4,22)` cancellation with
`j` alone leaves 54; the other column supplies the prime 19.

At `i=3` we prove more without hypotheses: a failure would require `16 ∣ n`,
`16 ∣ C(n,j)` and `j ∤ n`. First the gcd is larger than eight, so if it has no
odd prime, sixteen divides both coefficients. The cubic polynomial for C(n,3)
restricts n modulo 32. Odd n would force n=3j and a prime of n-2 then works.
In the remaining even classes not divisible by 16, n/2 is odd and divides 3j,
which forces j to divide n. This too is impossible by cancellation at n-1.

The two hypotheses below concern just the smooth residual: index three on the
multiples of sixteen, and indices at least four. No smoothness or distribution
claim about arbitrary binomial coefficients is assumed in the lemmas.
-/

namespace OMA.R_Erdos699_erdos_699_R1_H2_R2

private theorem symmetric_quotient {n i j : ℕ} (hi : i ≤ j) (hj : 2*j ≤ n) :
    n.choose i / Nat.gcd (n.choose i) (Nat.gcd (j.choose i) ((n-j).choose i)) ∣
      Nat.gcd (n.choose i) (n.choose j) := by
  let s := Nat.gcd (j.choose i) ((n-j).choose i)
  have hc : 0 < Nat.gcd (n.choose i) s := Nat.gcd_pos_of_pos_left _ (Nat.choose_pos (by omega))
  have hcol {k : ℕ} (hk : i ≤ k) : n.choose i ∣ k.choose i * n.choose k := by
    rw [Nat.mul_comm, Nat.choose_mul (n := n) hk]
    exact Nat.dvd_mul_right _ _
  have hs : n.choose i ∣ s * n.choose j := by
    dsimp [s]
    rw [← Nat.gcd_mul_right]
    refine Nat.dvd_gcd (hcol hi) ?_
    simpa only [Nat.choose_symm (by omega : j ≤ n)] using (hcol (k := n-j) (by omega))
  apply Nat.dvd_gcd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
  apply (Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left _ _) hc).2
  rw [← Nat.gcd_mul_right]
  exact Nat.dvd_gcd (Nat.dvd_mul_right _ _) hs

/-- A prime divisor gives a carry by Kummer's factorization formula (also used in PR 21566). -/
private theorem digit {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ n) (hd : p ∣ n.choose k) :
    ∃ a, 0 < a ∧ n % p^a < k % p^a := by
  have hpos := hp.factorization_pos_of_dvd (Nat.choose_pos hkn).ne' hd
  rw [Nat.factorization_choose hp hkn (Nat.lt_succ_self _)] at hpos
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter, Finset.mem_Ico] at ha
  obtain ⟨⟨ha, _⟩, hc⟩ := ha
  refine ⟨a, ha, ?_⟩
  have hq := pow_pos hp.pos a
  have h1 := Nat.mod_lt k hq
  have h2 := Nat.mod_lt (n-k) hq
  have hs := Nat.add_mod k (n-k) (p^a)
  rw [Nat.add_sub_of_le hkn, Nat.mod_eq_sub_mod hc,
    Nat.mod_eq_of_lt (by omega : k % p^a + (n-k) % p^a - p^a < p^a)] at hs
  omega

private theorem six_choose (t : ℕ) : 6 * (t+3).choose 3 = (t+3)*(t+2)*(t+1) := by
  calc 6 * (t+3).choose 3 = (t+3).descFactorial 3 :=
          (Nat.descFactorial_eq_factorial_mul_choose (t+3) 3).symm
       _ = _ := by
         change (t+1)*((t+2)*((t+3)*1)) = (t+3)*(t+2)*(t+1)
         ring

private theorem strict_ratio {n j : ℕ} (hj : 3 ≤ j) (hn : 2*j ≤ n) : 8*j.choose 3 < n.choose 3 := by
  refine lt_of_lt_of_le ?_ (Nat.choose_le_choose _ hn)
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le' hj
  have h1 := six_choose t
  have h2 := six_choose (2*t+3)
  rw [show 2*t+3+3 = 2*(t+3) by omega] at h2
  nlinarith only [h1, h2, Nat.zero_le (t^2), Nat.zero_le t]

/-- Without an odd common prime the gcd is a power of two strictly above eight. -/
private theorem sixteen {n j : ℕ} (hj : 3 ≤ j) (hn : 2*j ≤ n)
    (no : ¬ ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ p ∣ Nat.gcd (n.choose 3) (n.choose j)) :
    16 ∣ Nat.gcd (n.choose 3) (n.choose j) := by
  let g := Nat.gcd (n.choose 3) (n.choose j)
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (Nat.choose_pos (by omega))
  have hd : n.choose 3 ∣ g * j.choose 3 := by
    change n.choose 3 ∣ Nat.gcd (n.choose 3) (n.choose j) * j.choose 3
    rw [← Nat.gcd_mul_right]
    refine Nat.dvd_gcd (Nat.dvd_mul_right _ _) ?_
    rw [Nat.choose_mul (n := n) hj]
    exact Nat.dvd_mul_right _ _
  have hlarge : 8 < g := by
    have h := (strict_ratio hj hn).trans_le (Nat.le_of_dvd (Nat.mul_pos hg (Nat.choose_pos hj)) hd)
    by_contra! hsmall
    exact (not_lt_of_ge (Nat.mul_le_mul_right (j.choose 3) hsmall)) h
  have hp : g = 2 ^ g.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd hg.ne' (by
    intro p pp pd
    by_contra hne
    have := pp.two_le
    exact no ⟨p, pp, by omega, pd⟩)
  have hk : 4 ≤ g.primeFactorsList.length := by
    by_contra! h
    have hpow : 2 ^ g.primeFactorsList.length ≤ (2:ℕ)^3 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  calc (16 : ℕ) ∣ 2 ^ g.primeFactorsList.length := pow_dvd_pow 2 hk
       _ = g := hp.symm

private theorem exceptional {n : ℕ} (hn : 3 ≤ n) (hd : 16 ∣ n.choose 3) :
    n % 32 ∈ ([0,1,2,16,18] : List ℕ) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨k, hk⟩ := hd
  have hprod := six_choose t
  rw [hk] at hprod
  have h32 : 32 ∣ (t+3)*(t+2)*(t+1) := ⟨3*k, by nlinarith only [hprod]⟩
  let r : Fin 32 := ⟨t % 32, Nat.mod_lt _ (by decide)⟩
  have h : t ≡ r.val [MOD 32] := by change t % 32 = t % 32 % 32; simp
  have he := ((h.add_right 3).mul (h.add_right 2)).mul (h.add_right 1)
  have h32' : 32 ∣ (r.val+3)*(r.val+2)*(r.val+1) :=
    Nat.dvd_of_mod_eq_zero (Eq.trans (Eq.symm he) (Nat.mod_eq_zero_of_dvd h32))
  have tab : ∀ s : Fin 32, 32 ∣ (s.val+3)*(s.val+2)*(s.val+1) →
      (s.val+3)%32 ∈ ([0,1,2,16,18] : List ℕ) := by decide +kernel
  rw [show (t+3)%32 = (r.val+3)%32 from h.add_right 3]
  exact tab r h32'

/-- An odd d can be cancelled past the gcd if neither coefficient has a common odd prime with the other. -/
private theorem odd_cancel {d A B x y : ℕ} (ho : ¬ 2 ∣ d)
    (no : ¬ ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ p ∣ Nat.gcd A B)
    (ha : d ∣ A*x) (hb : d ∣ B*y) : d ∣ x*y := by
  have cop : d.Coprime (Nat.gcd A B) := by
    by_contra hn
    obtain ⟨p, pp, hpd, hpg⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    have hne : p ≠ 2 := fun e => ho (e ▸ hpd)
    have := pp.two_le
    exact no ⟨p, pp, by omega, hpg⟩
  apply cop.dvd_of_dvd_mul_left
  rw [← Nat.gcd_mul_right]
  apply Nat.dvd_gcd
  · rw [← Nat.mul_assoc]; exact dvd_mul_of_dvd_left ha _
  · rw [Nat.mul_comm x y, ← Nat.mul_assoc]; exact dvd_mul_of_dvd_left hb _

private theorem index_dvd (n k : ℕ) : n ∣ n.choose k * k := by
  cases n <;> cases k <;> try simp
  rename_i n k
  rw [← Nat.add_one_mul_choose_eq]
  exact Nat.dvd_mul_right _ _

/-- At n=3j odd, any prime of n-2 is at least five and works in the first digit. -/
private theorem odd_triple {n j : ℕ} (hj : 3 ≤ j) (hn : n = 3*j) (ho : ¬ 2 ∣ n) :
    ∃ p a b : ℕ, p.Prime ∧ 3 ≤ p ∧ 0 < a ∧ 0 < b ∧
      n % p^a < 3 % p^a ∧ n % p^b < j % p^b := by
  obtain ⟨p, pp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : n-2 ≠ 1)
  have hp : 5 ≤ p := by
    have := pp.two_le
    by_contra! h
    interval_cases p <;> omega
  obtain ⟨k, hk⟩ := hpd
  have hmod : n % p = 2 := by
    have h : n = 2 + p*k := by omega
    rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  refine ⟨p,1,1,pp,by omega,by decide,by decide,?_⟩
  simp only [pow_one, hmod, Nat.mod_eq_of_lt (by omega : 3 < p)]
  refine ⟨by decide, ?_⟩
  have he : (3*(j%p)) % p = 2 := by rw [Nat.mul_mod_mod, ← hn, hmod]
  by_contra! hh
  interval_cases j%p
  · simp at he
  · simp [Nat.mod_eq_of_lt (by omega : 3 < p)] at he
  · change 6 % p = 2 at he
    by_cases h : 6 < p
    · rw [Nat.mod_eq_of_lt h] at he; contradiction
    · interval_cases p <;> norm_num at he

private theorem even_multiple {n j : ℕ} (hj : 3 ≤ j) (hn : 2*j ≤ n) (he : 2 ∣ n) (hjdn : j ∣ n) :
    ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ p ∣ Nat.gcd (n.choose 3) (n.choose j) := by
  let d := n-1
  have ho : ¬ 2 ∣ d := by dsimp [d]; omega
  have hD {k : ℕ} (h : 2 ≤ k) : d ∣ n.choose k * (k*(k-1)) := by
    have e := Nat.choose_mul (n := n) (k := k) h
    have two (x : ℕ) : 2 * x.choose 2 = x*(x-1) := by
      simpa [Nat.mul_comm, Nat.choose_one_right] using Nat.choose_succ_right_eq x 1
    rw [← two k, ← Nat.mul_left_comm, e, ← Nat.mul_assoc, two]
    exact dvd_mul_of_dvd_left (Nat.dvd_mul_left _ _) _
  by_contra no
  have hc : d ∣ 6*(j*(j-1)) := odd_cancel ho no (hD (k:=3) (by decide)) (hD (by omega))
  have hc2 : d.Coprime 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr ho).symm
  have hdj : d.Coprime j := by
    apply Nat.Coprime.coprime_dvd_right hjdn
    change (n-1).Coprime n
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 1 ≤ n)
    simp
  have hshort : d ∣ 3*(j-1) := by
    apply (hc2.mul_right hdj).dvd_of_dvd_mul_left
    convert hc using 1; ring
  have eq := Nat.eq_of_dvd_of_lt_two_mul (by omega : 3*(j-1) ≠ 0) hshort (by dsimp [d]; omega)
  obtain ⟨k, hk⟩ := hjdn
  change 3*(j-1) = n-1 at eq
  have hlt : n < 3*j := by omega
  have hklt : k < 3 := by
    by_contra! h
    have := Nat.mul_le_mul_left j h
    omega
  interval_cases k <;> omega

/-- Necessary restrictions on a failure in column three. -/
private theorem three_restrictions {n j : ℕ} (hj : 3 ≤ j) (hn : 2*j ≤ n)
    (no : ¬ ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ p ∣ Nat.gcd (n.choose 3) (n.choose j))
    (nd : ¬ ∃ p a b : ℕ, p.Prime ∧ 3 ≤ p ∧ 0 < a ∧ 0 < b ∧
      n % p^a < 3 % p^a ∧ n % p^b < j % p^b) :
    16 ∣ n ∧ ¬ j ∣ n ∧ 16 ∣ n.choose j := by
  have part {d : ℕ} (hd : d ∣ n) (ho : ¬ 2 ∣ d) : d ∣ 3*j :=
    odd_cancel ho no (hd.trans (index_dvd n 3)) (hd.trans (index_dvd n j))
  by_cases he : 2 ∣ n
  · have hnj : ¬ j ∣ n := fun h => no (even_multiple hj hn he h)
    have hg := sixteen hj hn no
    refine ⟨?_, hnj, hg.trans (Nat.gcd_dvd_right _ _)⟩
    by_contra hn16
    have hres := exceptional (by omega) (hg.trans (Nat.gcd_dvd_left _ _))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hres
    have ho : ¬ 2 ∣ (n/2) := by omega
    obtain ⟨k, hk⟩ := part (Nat.div_dvd_of_dvd he) ho
    have hk4 : k ≤ 3 := by
      by_contra! h
      have := Nat.mul_le_mul_left (n/2) h
      omega
    apply hnj
    interval_cases k
    · omega
    · exact ⟨6, by omega⟩
    · exact ⟨3, by omega⟩
    · exact ⟨2, by omega⟩
  · have heq := Nat.eq_of_dvd_of_lt_two_mul (by omega : 3*j ≠ 0) (part (dvd_refl n) he) (by omega)
    exact (nd (odd_triple hj heq.symm he)).elim

/-- A possible exceptional cubic column, on multiples of sixteen only. -/
def H1 : Prop := ∀ n j : ℕ, 3 < j → 2*j ≤ n → n ≤ j^2 → 9 < 2*j →
    16 ∣ n → ¬ j ∣ n → 16 ∣ n.choose j →
    let c := Nat.gcd (n.choose 3) (Nat.gcd (j.choose 3) ((n-j).choose 3))
    n.choose 3 / c ∈ Nat.smoothNumbers 3 → Nat.gcd c (n.choose j) ∉ Nat.smoothNumbers 3

/-- Higher columns: only when both symmetric cancellations leave a smooth quotient
must a large prime be found in the cancelled part. -/
def H2 : Prop := ∀ n i j : ℕ, 4 ≤ i → i < j → 2*j ≤ n → n ≤ j^2 → 3*i < 2*j →
    let c := Nat.gcd (n.choose i) (Nat.gcd (j.choose i) ((n-j).choose i))
    n.choose i / c ∈ Nat.smoothNumbers i → Nat.gcd c (n.choose j) ∉ Nat.smoothNumbers i

theorem main : H1 → H2 → OMA.R_Erdos699_erdos_699_R1.H2 := by
  intro three higher n i j hi hij hj hs hf
  have hnj : 2*j ≤ n := by omega
  by_contra nd
  have no : ¬ ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.gcd (n.choose i) (n.choose j) := by
    rintro ⟨p, pp, hpi, pd⟩
    obtain ⟨a, ha, hia⟩ := digit pp (by omega : i ≤ n) (pd.trans (Nat.gcd_dvd_left _ _))
    obtain ⟨b, hb, hjb⟩ := digit pp (by omega : j ≤ n) (pd.trans (Nat.gcd_dvd_right _ _))
    exact nd ⟨p,a,b,pp,hpi,ha,hb,hia,hjb⟩
  have sm : Nat.gcd (n.choose i) (n.choose j) ∈ Nat.smoothNumbers i :=
    Nat.mem_smoothNumbers'.2 fun p pp hd => by by_contra! h; exact no ⟨p,pp,h,hd⟩
  let c := Nat.gcd (n.choose i) (Nat.gcd (j.choose i) ((n-j).choose i))
  have qsm : n.choose i / c ∈ Nat.smoothNumbers i :=
    Nat.mem_smoothNumbers_of_dvd sm (symmetric_quotient hij.le hnj)
  have csm : Nat.gcd c (n.choose j) ∈ Nat.smoothNumbers i :=
    Nat.mem_smoothNumbers_of_dvd sm (Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _))
      (Nat.gcd_dvd_right _ _))
  by_cases eq : i = 3
  · subst i
    obtain ⟨hn16, hnot, hj16⟩ := three_restrictions (by omega) hnj no nd
    exact three n j hij hnj hs hf hn16 hnot hj16 qsm csm
  · exact higher n i j (by omega) hij hnj hs hf qsm csm

end OMA.R_Erdos699_erdos_699_R1_H2_R2
