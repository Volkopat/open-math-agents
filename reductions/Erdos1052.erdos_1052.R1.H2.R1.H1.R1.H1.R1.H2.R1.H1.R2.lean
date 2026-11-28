import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1

/-!
A refinement of the exponent-eleven branch of Erdős problem 1052.
The balance forces the simple prime 5. For an odd two-adic exponent, the
three-adic budget now counts every factor with multiplicity, yielding a
uniform bound for the indicated smooth exponents. Additional finite
factor chains rule out 80 more odd-multiple classes.

The normalization and squarefree-source lemmas are from the canonical
work of @Dugongue and @adammcarter. The reserved factors in the odd budget
refine @adammcarter's distinct-prime count. The proof forcing 5 applies
the leaf product argument of Graham's unitary perfect number analysis.
-/

namespace E1052Strip

open scoped BigOperators

/-- Prime divisors of the kernel and their successors force six fixed primes. -/
theorem forced_fixed {P : Finset ℕ}
    (step : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ ({3} : Finset ℕ) →
      ∀ p ∈ P, c ∣ p+1 → c ∈ P)
    (seed : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ ({3} : Finset ℕ) →
      c ∣ 1+3^11 → c ∈ P) :
    ({7,17,67,83,331,661} : Finset ℕ) ⊆ P := by
  have h67 := seed 67 (by norm_num) (by decide) (by decide) (by decide)
  have h661 := seed 661 (by norm_num) (by decide) (by decide) (by decide)
  have h331 := step 331 (by norm_num) (by decide) (by decide) 661 h661 (by decide)
  have h83 := step 83 (by norm_num) (by decide) (by decide) 331 h331 (by decide)
  have h7 := step 7 (by norm_num) (by decide) (by decide) 83 h83 (by decide)
  have h17 := step 17 (by norm_num) (by decide) (by decide) 67 h67 (by decide)
  simp [Finset.insert_subset_iff, h7, h17, h67, h83, h331, h661]

/-- Strip the arithmetic contribution of the six forced primes from the balance. -/
theorem strip_eleven {a : ℕ} {P : Finset ℕ}
    (hF : ({7,17,67,83,331,661} : Finset ℕ) ⊆ P)
    (hbal : (2^a+1)*(1+3^11)*(∏ p ∈ P, (p+1)) =
      2^(a+1)*3^11*(∏ p ∈ P,p)) :
    (2^a+1)*8192*(∏ p ∈ P \ {7,17,67,83,331,661}, (p+1)) =
      2^(a+1)*6561*(∏ p ∈ P \ {7,17,67,83,331,661},p) := by
  rw [← Finset.prod_sdiff (f := fun p : ℕ => p+1) hF,
      ← Finset.prod_sdiff (f := fun p : ℕ => p) hF] at hbal
  have hnum : (∏ p ∈ ({7,17,67,83,331,661} : Finset ℕ), (p+1)) = 180778493952 := by decide
  have hden : (∏ p ∈ ({7,17,67,83,331,661} : Finset ℕ), p) = 144786913369 := by decide
  rw [hnum,hden] at hbal
  nlinarith only [hbal]

end E1052Strip

namespace ElevenLeaves

open Finset

private lemma small_roots : ∀ q : Fin 139, q.val.Prime → q.val ≠ 2 → q.val ≠ 5 → q.val ≠ 17 →
    3 ∣ q.val + 1 → (∀ r ∈ (q.val+1).primeFactors, r = 2 ∨ r = 3) →
    q.val = 11 ∨ q.val = 23 ∨ q.val = 47 ∨ q.val = 53 ∨ q.val = 71 ∨ q.val = 107 := by
  decide +kernel

private lemma regular_leaf {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2) (h5 : q ≠ 5) (h17 : q ≠ 17)
    (h3 : 3 ∣ q+1) (hs : ∀ r ∈ (q+1).primeFactors, r = 2 ∨ r = 3)
    (a : q ≠ 11) (b : q ≠ 23) (c : q ≠ 47) :
    ((q:ℚ)+1)/(q-1:ℚ) ≤ (70/69:ℚ)^((q+1).factorization 3) := by
  by_cases hbig : 139 ≤ q
  · have hq' : (139:ℚ) ≤ q := by exact_mod_cast hbig
    have hv := (show Nat.Prime 3 by decide).factorization_pos_of_dvd (by omega) h3
    calc _ ≤ 70/69 := by apply (div_le_iff₀ (by linarith : (0:ℚ) < q-1)).mpr; linarith
         _ = (70/69:ℚ)^1 := by ring
         _ ≤ _ := pow_le_pow_right₀ (by norm_num) hv
  · have h := small_roots ⟨q,by omega⟩ hq h2 h5 h17 h3 hs
    change q = 11 ∨ q = 23 ∨ q = 47 ∨ q = 53 ∨ q = 71 ∨ q = 107 at h
    rcases h with h | h | h | rfl | rfl | rfl
    · contradiction
    · contradiction
    · contradiction
    · decide +kernel
    · decide +kernel
    · decide +kernel

/-- The eight available factors of three pay for all non-Mersenne leaves. The
three small leaves have individual corrections to the common per-factor charge. -/
theorem three_leaf_bound (S : Finset ℕ)
    (roots : ∀ q ∈ S, q.Prime ∧ q ≠ 2 ∧ q ≠ 5 ∧ q ≠ 17 ∧ 3 ∣ q+1 ∧
      ∀ r ∈ (q+1).primeFactors, r=2 ∨ r=3)
    (budget : ∑ q ∈ S, (q+1).factorization 3 ≤ 8) :
    ∏ q ∈ S, (((q:ℚ)+1)/(q-1:ℚ)) ≤ (12/10:ℚ)*(24/22)*(48/46)*(70/69)^5 := by
  let t : ℚ := 70/69
  let v (q : ℕ) := (q+1).factorization 3
  let correction (p : ℕ) : ℚ := (((p:ℚ)+1)/(p-1:ℚ))/t
  have hunit : 1 ≤ t := by norm_num [t]
  have hfix : ∀ p ∈ ({11,23,47} : Finset ℕ), 1 ≤ correction p := by
    intro p hp
    simp only [mem_insert,mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> norm_num [correction,t]
  have hq (q : ℕ) (hq : q ∈ S) : (((q:ℚ)+1)/(q-1:ℚ)) ≤
      t^(v q)*(if q=11 then correction 11 else 1)*(if q=23 then correction 23 else 1)*
        (if q=47 then correction 47 else 1) := by
    obtain ⟨hp,h2,h5,h17,h3,hs⟩ := roots q hq
    by_cases a : q=11
    · subst q; decide +kernel
    by_cases b : q=23
    · subst q; decide +kernel
    by_cases c : q=47
    · subst q; decide +kernel
    simpa [a,b,c] using regular_leaf hp h2 h5 h17 h3 hs a b c
  have factor (p : ℕ) (hp : p ∈ ({11,23,47} : Finset ℕ)) :
      (∏ q ∈ S, if q=p then correction p else 1) ≤ correction p := by
    rw [prod_ite_eq']
    split <;> first | exact le_rfl | exact hfix p hp
  have ha := factor 11 (by decide)
  have hb := factor 23 (by decide)
  have hc := factor 47 (by decide)
  have hsum : (∏ q ∈ S, t^(v q)) ≤ t^8 := by rw [prod_pow_eq_pow_sum]; exact pow_le_pow_right₀ hunit budget
  have posB (q : ℕ) (h : q ∈ S) : 0 ≤ (((q:ℚ)+1)/(q-1:ℚ)) := by
    obtain ⟨hp,h2,h5,h17,h3,hs⟩ := roots q h
    have pos : (2:ℚ) ≤ q := by exact_mod_cast hp.two_le
    exact div_nonneg (by linarith) (by linarith)
  have bound := Finset.prod_le_prod posB hq
  simp only [prod_mul_distrib] at bound
  have pos (p : ℕ) (hp : p ∈ ({11,23,47} : Finset ℕ)) : 0 ≤ ∏ q ∈ S, if q=p then correction p else 1 := by
    apply prod_nonneg; intro x hx; split <;> first | exact (zero_le_one.trans (hfix p hp)) | norm_num
  have p11 := pos 11 (by decide)
  have p23 := pos 23 (by decide)
  have p47 := pos 47 (by decide)
  have pT : 0 ≤ ∏ q ∈ S, t^(v q) := prod_nonneg fun _ _ => pow_nonneg (zero_le_one.trans hunit) _
  calc _ ≤ _ := bound
       _ ≤ t^8*correction 11*correction 23*correction 47 := by gcongr
       _ = _ := by norm_num [t,correction]

end ElevenLeaves

/- Graham's leaf products after stripping the forced factors of the exponent-eleven balance. -/

namespace ElevenLeaves

open Finset OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1

private theorem three_budget {a : ℕ} {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime ∧ q ≠ 3)
    (E : (2^a+1)*8192*∏ p ∈ Q,(p+1) = 2^(a+1)*6561*∏ p ∈ Q,p) :
    ∑ q ∈ Q,(q+1).factorization 3 ≤ 8 := by
  have dn : (∏ p ∈ Q, (p+1)) ∣ 2^(a+1)*6561*∏ p ∈ Q,p := E ▸ dvd_mul_left _ _
  have hnq : ∀ p ∈ Q, p ≠ 0 := fun p hp => (hQ p hp).1.ne_zero
  have hnp : (∏ p ∈ Q, p) ≠ 0 := prod_ne_zero_iff.mpr hnq
  have hd : ∀ p ∈ Q, p+1 ≠ 0 := fun p _ => by omega
  have v := (Nat.factorization_le_iff_dvd (prod_ne_zero_iff.mpr hd) (by positivity)).mpr dn 3
  have hq0 (q : ℕ) (hq : q ∈ Q) : q.factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun h => (hQ q hq).2 ((Nat.prime_dvd_prime_iff_eq
      (show Nat.Prime 3 by decide) (hQ q hq).1).mp h).symm)
  have htwo : (2^(a+1)).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd
    (fun h => (by decide : ¬3 ∣ 2) ((show Nat.Prime 3 by decide).dvd_of_dvd_pow h))
  have hkernel : Nat.factorization 6561 3 = 8 := by decide +kernel
  rw [Nat.factorization_prod_apply hd,Nat.factorization_mul (by positivity) hnp,
      Nat.factorization_mul (by positivity) (by decide), Finsupp.add_apply, Finsupp.add_apply,
      Nat.factorization_prod_apply hnq, htwo, hkernel] at v
  have hz : ∑ q ∈ Q, q.factorization 3 = 0 := sum_eq_zero hq0
  simpa [hz] using v

/-- The stripped factor 8192 guarantees that the two-adic exponent is at least twelve. -/
theorem twelve_after_strip {a : ℕ} {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime ∧ q ≠ 2)
    (E : (2^a+1)*8192*∏ p ∈ Q,(p+1) = 2^(a+1)*6561*∏ p ∈ Q,p) : 12 ≤ a := by
  have dn : 8192 ∣ 2^(a+1)*6561*∏ p ∈ Q,p := by
    rw [← E]
    exact (dvd_mul_left _ _).trans (dvd_mul_right _ _)
  have hnq : ∀ p ∈ Q, p ≠ 0 := fun p hp => (hQ p hp).1.ne_zero
  have hnp : (∏ p ∈ Q, p) ≠ 0 := prod_ne_zero_iff.mpr hnq
  have v := (Nat.factorization_le_iff_dvd (by decide : 8192 ≠ 0) (by positivity)).mpr dn 2
  have hq0 (q : ℕ) (hq : q ∈ Q) : q.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun h => (hQ q hq).2
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (hQ q hq).1).mp h).symm)
  have hz : ∑ q ∈ Q, q.factorization 2 = 0 := sum_eq_zero hq0
  have hu : Nat.factorization 8192 2 = 13 := by decide +kernel
  have hv : Nat.factorization 6561 2 = 0 := by decide +kernel
  rw [hu,Nat.factorization_mul (by positivity) hnp,Nat.factorization_mul (by positivity)
    (by decide),Finsupp.add_apply,Finsupp.add_apply,Nat.factorization_pow_self Nat.prime_two,
    hv,Nat.factorization_prod_apply hnq,hz] at v
  omega

/-- Every admissible balanced kernel after stripping the six forced primes must contain five. -/
theorem five_after_strip {a : ℕ} {Q : Finset ℕ} (ha : 10 ≤ a)
    (hQ : ∀ q ∈ Q, q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 7 ∧ q ≠ 17)
    (E : (2^a+1)*8192*∏ p ∈ Q,(p+1) = 2^(a+1)*6561*∏ p ∈ Q,p) : 5 ∈ Q := by
  classical
  by_contra h5
  let β (p : ℕ) : ℚ := if p = 3 ∨ p = 7 then 1 else ((p:ℚ)+1)/(p-1:ℚ)
  have eqB (p : ℕ) (hp : p ∈ Q) : β p = ((p:ℚ)+1)/(p-1:ℚ) := by
    simp [β,(hQ p hp).2.2.1,(hQ p hp).2.2.2.1]
  have hb (p : ℕ) (hp : p ∈ Q) : 1+1/(p:ℚ) ≤ β p ∧ β p ≤ ((p:ℚ)+1)/(p-1:ℚ) := by
    rw [eqB p hp]
    exact ⟨one_add_le_B (hQ p hp).1.two_le,le_rfl⟩
  have bk := prime_dvd_prime_pow (e:=8) (show Nat.Prime 3 by decide)
  change ∀ c, c.Prime → c ∣ 6561 → c ∈ ({3} : Finset ℕ) at bk
  obtain ⟨L,hL,leaf,main⟩ := master_gen (fun p hp => ⟨(hQ p hp).1,(hQ p hp).2.1⟩) bk (by decide) E β hb
    (fun _ _ c hc _ _ hbad => False.elim (hbad (eqB c hc)))
  let T := L.filter (fun q => 3 ∣ q+1)
  let M := L.filter (fun q => ¬3 ∣ q+1)
  have hm (q : ℕ) (hq : q ∈ M) : ∃ i, q+1=2^i := by
    obtain ⟨hql,hnd⟩ := mem_filter.mp hq
    apply two_pow_of_no_odd_prime
    intro c hcp hc2 hc
    exact hnd ((mem_singleton.mp (leaf q hql c hcp hc2 hc)) ▸ hc)
  have mB := mersenne_bound β M (fun q h => (hQ q (hL (mem_filter.mp h).1)).1) hm
    (fun q h => by
      have hq := hL (mem_filter.mp h).1
      have pos : (0:ℚ) ≤ 1 / (q:ℚ) := by positivity
      exact ⟨lt_of_lt_of_le (by linarith) (hb q hq).1, (hb q hq).2⟩)
    (by norm_num [β])
  have sub : T ⊆ Q := (filter_subset _ _).trans hL
  have tb := three_budget (fun q h => ⟨(hQ q h).1,(hQ q h).2.2.1⟩) E
  have sm : ∑ q ∈ T, (q+1).factorization 3 ≤ 8 :=
    (sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => Nat.zero_le _)).trans tb
  have bound := three_leaf_bound T (fun q h => by
    have p := hQ q (sub h)
    exact ⟨p.1,p.2.1,fun he => h5 (he ▸ sub h),p.2.2.2.2,(mem_filter.mp h).2,
      fun t ht => or_iff_not_imp_left.mpr (fun ht2 => mem_singleton.mp
        (leaf q (mem_filter.mp h).1 t (Nat.prime_of_mem_primeFactors ht) ht2
          (Nat.dvd_of_mem_primeFactors ht)))⟩) sm
  have tB : ∏ q ∈ T, β q ≤ (12/10:ℚ)*(24/22)*(48/46)*(70/69)^5 := by
    rwa [prod_congr rfl (fun q hq => eqB q (sub hq))]
  have eq : (∏ q ∈ T, β q)*(∏ q ∈ M, β q) = ∏ q ∈ L, β q :=
    prod_filter_mul_prod_filter_not _ _ _
  rw [← eq] at main
  have mpos : 0 ≤ ∏ q ∈ M, β q := prod_nonneg (fun q h => by
    have p := hb q (hL (mem_filter.mp h).1)
    exact (by positivity : (0:ℚ) ≤ 1+1/(q:ℚ)).trans p.1)
  have tpos : 0 ≤ ∏ q ∈ T, β q := prod_nonneg (fun q h =>
    (by positivity : (0:ℚ) ≤ 1+1/(q:ℚ)).trans (hb q (sub h)).1)
  have powlb : (2:ℚ)^10 ≤ (2:ℚ)^a := pow_le_pow_right₀ (by norm_num) ha
  have ap : 1+1/(2:ℚ)^a ≤ 1025/1024 := by
    norm_num at powlb
    rw [le_div_iff₀ (by norm_num)]
    field_simp
    linarith
  have upper := calc
    (1+1/(2:ℚ)^a)*(8192/6561)*((∏ q ∈ T, β q)*(∏ q ∈ M, β q)) ≤
        (1025/1024)*(8192/6561)*(((12/10)*(24/22)*(48/46)*(70/69)^5)*
          ((β 3*β 7*β 31*β 127)*(2048/2047))) := by gcongr
    _ < 2 := by norm_num [β]
  exact (not_lt_of_ge main) upper

/-- Five belongs to the odd simple-prime factors in every exponent-eleven balance
after stripping the fixed primes. -/
theorem five_in_simple_primes {a : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3 : 3 ∉ P)
    (E : (2^a+1)*(1+3^11)*∏ p ∈ P, (p+1) = 2^(a+1)*3^11*∏ p ∈ P,p) : 5 ∈ P := by
  obtain ⟨s1, _, _, _, _, _, s7, _⟩ := facts hP
    (prime_dvd_prime_pow (e:=11) (by decide : Nat.Prime 3)) E
  have hF := E1052Strip.forced_fixed s1 s7
  have E' := E1052Strip.strip_eleven hF E
  have lower := twelve_after_strip (fun q hq => hP q (sdiff_subset hq)) E'
  have ha : 10 ≤ a := by omega
  apply (sdiff_subset : P \ {7,17,67,83,331,661} ⊆ P)
  apply five_after_strip ha _ E'
  intro q hq
  obtain ⟨hq,hn⟩ := mem_sdiff.mp hq
  exact ⟨(hP q hq).1, (hP q hq).2, fun e => h3 (e ▸ hq),
    fun e => hn (by simp [e]), fun e => hn (by simp [e])⟩

/-- Five divides every unitary-perfect integer in the exponent-eleven case
of the three-adic valuation. -/
theorem five_dvd_unitary (n : ℕ) (h : Erdos1052.IsUnitaryPerfect n)
    (hiff : ∀ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p^2 ∣ n ↔ p=3) (he : n.factorization 3 = 11) : 5 ∣ n := by
  have hn0 : n ≠ 0 := h.2.ne'
  have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
    intro r hr hr2 hr3
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hpos := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have : ¬ 2 ≤ n.factorization r := fun he =>
      hr3 ((hiff r).mp ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr he⟩)
    omega
  have h3n : 3 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  have h3pf : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3n, hn0⟩
  have ha : n.factorization 2 = padicValNat 2 n := Nat.factorization_def n Nat.prime_two
  obtain ⟨hP, E⟩ := kernel_balance_one h h3pf (by norm_num) hs
  have h3P : 3 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({3} : Finset ℕ)) := by simp
  rw [he] at E
  rw [ha] at E
  have h5 := five_in_simple_primes hP h3P E
  exact Nat.dvd_of_mem_primeFactors (mem_of_mem_erase (mem_filter.mp h5).1)

end ElevenLeaves

/- For odd a in the exponent-eleven unitary-perfect case, the factors of a
congruent to 2 modulo 3 and all its factors of 3 use at most seven units of
3-adic valuation, counted with multiplicity. The reservation of the three
factors consumed by 17+1 and 83+1 is due to @adammcarter (odd_count in the
accepted 3^11 R1 reduction), using @Dugongue's and @adammcarter's earlier
balance-equation and squarefree-source restrictions. -/

namespace E1052Multiplicity

private lemma odd_power_mod_three (x k : ℕ) (hx : x%3=2) : x^(2*k+1)%3=2 := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [show 2*(k+1)+1=(2*k+1)+2 by omega, pow_add, Nat.mul_mod, ih]
    have h2 : x^2%3=1 := by rw [Nat.pow_mod,hx]
    rw [h2]

/-- For odd r and x ≡ −1 modulo three, the odd geometric quotient
(x^r + 1)/(x+1) is congruent to r modulo three. -/
theorem odd_quotient (x r : ℕ) (hx : x%3=2) (hr : r%2=1) :
    ∃ c, x^r+1=(x+1)*c ∧ c%3=r%3 := by
  obtain ⟨k,rfl⟩ : ∃ k, r=2*k+1 := ⟨r/2,by omega⟩
  induction k with
  | zero => exact ⟨1,by simp,by decide⟩
  | succ k ih =>
    obtain ⟨c,hc,hm⟩ := ih (by omega)
    refine ⟨c+x^(2*k+1)*(x-1),?_,?_⟩
    · have hsub : x-1+1=x := by omega
      rw [show 2*(k+1)+1=(2*k+1)+2 by omega,pow_add,mul_add,←hc]
      nlinarith [congrArg (fun v => x^(2*k+1)*x*v) hsub,
        congrArg (fun v => x^(2*k+1)*v) hsub]
    · rw [Nat.add_mod, Nat.mul_mod,odd_power_mod_three x k hx,hm]
      have hx' : (x-1)%3=1 := by omega
      rw [hx']
      omega

/-- The mod-three prime witness from the existing Erdos1052 reductions. -/
private theorem exists_two (n : ℕ) : n%3=2 → ∃ p, p.Prime ∧ p∣n ∧ p%3=2 := by
  induction n using Nat.recOnMul with
  | zero => norm_num
  | one => norm_num
  | prime p hp => intro h; exact ⟨p,hp,dvd_rfl,h⟩
  | mul a b ha hb =>
    intro h
    rw [Nat.mul_mod] at h
    have am := Nat.mod_lt a (by decide : 0<3)
    have bm := Nat.mod_lt b (by decide : 0<3)
    have e : a%3=2 ∨ b%3=2 := by
      by_contra! hn
      have a01 : a%3=0 ∨ a%3=1 := by omega
      have b01 : b%3=0 ∨ b%3=1 := by omega
      rcases a01 with aa | aa <;> rcases b01 with bb | bb <;> simp [aa,bb] at h
    rcases e with ea | eb
    · obtain ⟨p,hp,dv,ep⟩ := ha ea
      exact ⟨p,hp,dv.trans (dvd_mul_right _ _),ep⟩
    · obtain ⟨p,hp,dv,ep⟩ := hb eb
      exact ⟨p,hp,dv.trans (dvd_mul_left _ _),ep⟩

/-- Every occurrence of a factor 2 modulo 3 creates a new prime 2 modulo 3.
Every occurrence of a multiple of three contributes a further factor three
directly to 2^a+1. -/
theorem extract (L : List ℕ) (odd : L.prod%2=1)
    (fresh : ∀ q : ℕ, q.Prime → q%3=2 → ¬q*q ∣ 2^L.prod+1) :
    (3^(1+(L.filter (fun p => p%3=0)).length) ∣ 2^L.prod+1) ∧
    ∃ Q : Finset ℕ, Q.card=(L.filter (fun p => p%3=2)).length ∧
      ∀ q∈Q, q.Prime ∧ q∣2^L.prod+1 ∧ q%3=2 := by
  classical
  induction L with
  | nil => exact ⟨by decide,∅,by simp,by simp⟩
  | cons p L ih =>
    simp only [List.prod_cons] at odd fresh ⊢
    have hp : p%2=1 := by
      by_contra! he
      rw [Nat.mul_mod,show p%2=0 by omega] at odd
      simp at odd
    have hL : L.prod%2=1 := by
      by_contra! he
      rw [Nat.mul_mod,show L.prod%2=0 by omega] at odd
      simp at odd
    have hbase : (2^L.prod)%3=2 := by
      rw [show L.prod=2*(L.prod/2)+1 by omega]
      exact odd_power_mod_three 2 _ (by decide)
    obtain ⟨c,hc,hm⟩ := odd_quotient (2^L.prod) p hbase hp
    have step : 2^(p*L.prod)+1=(2^L.prod+1)*c := by simpa only [←pow_mul,mul_comm L.prod p] using hc
    have sub : (2^L.prod+1)∣2^(p*L.prod)+1 := ⟨c,step⟩
    obtain ⟨three,Q,qsize,qprop⟩ := ih hL (fun q hq hr dv => fresh q hq hr (dv.trans sub))
    constructor
    · by_cases h3 : p%3=0
      · simp [h3]
        rw [step,show 1+((L.filter (fun v => v%3=0)).length+1)=
          (1+(L.filter (fun v => v%3=0)).length)+1 by omega,pow_succ]
        exact mul_dvd_mul three (Nat.dvd_iff_mod_eq_zero.mpr (hm.trans h3))
      · simpa [h3] using three.trans sub
    · by_cases h2 : p%3=2
      · obtain ⟨q,pr,dv,res⟩ := exists_two c (hm.trans h2)
        have outside : q∉Q := by
          intro hq
          apply fresh q pr res
          rw [step]
          exact mul_dvd_mul (qprop q hq).2.1 dv
        refine ⟨insert q Q,by simp [outside,h2,qsize],?_⟩
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hvm
        · exact ⟨pr,dv.trans ⟨_,step.trans (Nat.mul_comm _ _)⟩,res⟩
        · exact ⟨(qprop v hvm).1,(qprop v hvm).2.1.trans sub,(qprop v hvm).2.2⟩
      · exact ⟨Q,by simpa [h2] using qsize,fun v hv =>
          ⟨(qprop v hv).1,(qprop v hv).2.1.trans sub,(qprop v hv).2.2⟩⟩

end E1052Multiplicity

namespace E1052Multiplicity

theorem count_from_sources (m e j : ℕ) (P X : Finset ℕ) (hm : m%2=1)
    (sqf : ∀ q : ℕ, q.Prime → q%3=2 → ¬q*q ∣ 2^m+1)
    (mem : ∀ q : ℕ, q.Prime → q∣2^m+1 → q%3=2 → q∈P)
    (hX : X⊆P) (notroot : ∀ q∈X, ¬q∣2^m+1)
    (reserved : 3^j ∣ ∏ q∈X,(q+1))
    (budget : ∀ S ⊆ P, ¬ 3^(e+1) ∣ (2^m+1)*∏ q∈S,(q+1)) :
    1 + (m.primeFactorsList.filter (fun p => p%3=0)).length +
      (m.primeFactorsList.filter (fun p => p%3=2)).length + j ≤ e := by
  classical
  have hp := Nat.prod_primeFactorsList (show m≠0 by omega)
  have h := extract m.primeFactorsList (by simpa only [hp] using hm)
    (by simpa only [hp] using sqf)
  rw [hp] at h
  obtain ⟨hthree,Q,sz,hq⟩ := h
  have hQP : Q ⊆ P := fun q hq' => mem q (hq q hq').1 (hq q hq').2.1 (hq q hq').2.2
  have hd : Disjoint Q X := Finset.disjoint_left.mpr fun q hQ hX' => notroot q hX' (hq q hQ).2.1
  have hdiv : 3 ^ Q.card ∣ ∏ q ∈ Q, (q+1) := by
    rw [← Finset.prod_const]
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun q hq' => by have := (hq q hq').2.2; omega)
  by_contra! big
  apply budget (Q∪X) (Finset.union_subset hQP hX)
  rw [Finset.prod_union hd, ← mul_assoc]
  have aq := mul_dvd_mul (mul_dvd_mul hthree hdiv) reserved
  rw [←pow_add,←pow_add] at aq
  apply Dvd.dvd.trans _ aq
  exact pow_dvd_pow 3 (by omega)

end E1052Multiplicity

namespace E1052Multiplicity

private theorem bounded_list (L : List ℕ) (B : ℕ)
    (h : ∀ p∈L, p≤B ∧ p%3≠1) :
    L.prod ≤ B^((L.filter (fun p => p%3=0)).length+
      (L.filter (fun p => p%3=2)).length) := by
  induction L with
  | nil => simp
  | cons p L ih =>
    obtain ⟨hp,hr⟩ := h p (by simp)
    have hind := Nat.mul_le_mul hp (ih fun a ha => h a (List.mem_cons_of_mem _ ha))
    have hres : p%3=0 ∨ p%3=2 := by omega
    have form : ((p::L).filter (fun x => x%3=0)).length +
        ((p::L).filter (fun x => x%3=2)).length =
        ((L.filter (fun x => x%3=0)).length + (L.filter (fun x => x%3=2)).length) + 1 := by
      rcases hres with h0 | h2
      · simp [h0]; omega
      · simp [h2]; omega
    rw [form,pow_succ']
    exact hind

theorem smooth_bound {K : ℕ} (m B : ℕ) (hm : m≠0) (hB : 0<B)
    (weights : (m.primeFactorsList.filter (fun p => p%3=0)).length+
      (m.primeFactorsList.filter (fun p => p%3=2)).length ≤ K)
    (h : ∀ p∈m.primeFactors, p≤B ∧ p%3≠1) : m ≤ B^K := by
  have b := bounded_list m.primeFactorsList B (fun p hp => h p (by simpa using hp))
  rw [Nat.prod_primeFactorsList hm] at b
  exact b.trans (Nat.pow_le_pow_right hB weights)

end E1052Multiplicity

namespace E1052Multiplicity
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1 hiding H1 H2 H3 main

theorem exponent_budget {m : ℕ} {P : Finset ℕ} (hP : ∀ p∈P,p.Prime ∧ p≠2) (h3P : 3∉P)
    (E : (2^m+1)*(1+3^11)*∏ p∈P,(p+1) = 2^(m+1)*3^11*∏ p∈P,p)
    (hm : m%2=1) : (m.primeFactorsList.filter (fun p => p%3=0)).length +
      (m.primeFactorsList.filter (fun p => p%3=2)).length ≤ 7 := by
  classical
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := by simp
  obtain ⟨S1,S2,_,S4,S5,_,S7,_⟩ := facts hP hK E
  have g67 : 67 ∈ P := S7 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 67 g67 (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have not_two : ¬2 ∣ 2^m+1 := by
    have h : 2∣2^m := dvd_pow_self _ (by omega : m≠0)
    omega
  have h := count_from_sources m 11 3 P {17,83} hm
    (fun q pr res h => S5 q pr (by rintro rfl; exact not_two ((dvd_mul_right 2 2).trans h))
      (hnz (by omega)) h)
    (fun q pr d res => S2 q pr (by rintro rfl; exact not_two d) (hnz (by omega)) d)
    (by simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro g17 g83)
    (by
      intro x hx hd
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) hd 67 g67 (by norm_num)
      · exact S4 83 (by norm_num) (by norm_num) (hnz (by norm_num)) hd 331 g331 (by norm_num))
    (by norm_num [Finset.prod_insert]) (fun _ hS h => budget_kernel3 hP h3P E hS h)
  omega

end E1052Multiplicity

namespace E1052Multiplicity
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main

theorem unitary_exponent_budget (n : ℕ) (h : Erdos1052.IsUnitaryPerfect n)
    (hiff : ∀ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p^2 ∣ n ↔ p=3) (he : n.factorization 3 = 11)
    (odd : padicValNat 2 n % 2 = 1) :
    ((padicValNat 2 n).primeFactorsList.filter (fun p => p%3=0)).length +
      ((padicValNat 2 n).primeFactorsList.filter (fun p => p%3=2)).length ≤ 7 := by
  have hn0 : n ≠ 0 := h.2.ne'
  have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
    intro r hr hr2 hr3
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hpos := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have : ¬ 2 ≤ n.factorization r := fun he =>
      hr3 ((hiff r).mp ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr he⟩)
    omega
  have h3n : 3 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  have h3pf : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3n, hn0⟩
  have ha : n.factorization 2 = padicValNat 2 n := Nat.factorization_def n Nat.prime_two
  obtain ⟨hP, E⟩ := kernel_balance_one h h3pf (by norm_num) hs
  have h3P : 3 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({3} : Finset ℕ)) := by simp
  rw [he] at E
  rw [ha] at E
  exact exponent_budget hP h3P E odd

theorem smooth_unitary (n B : ℕ) (h : Erdos1052.IsUnitaryPerfect n)
    (hiff : ∀ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p^2 ∣ n ↔ p=3) (he : n.factorization 3 = 11)
    (odd : padicValNat 2 n % 2 = 1) (hB : 0<B)
    (hs : ∀ p ∈ (padicValNat 2 n).primeFactors, p ≤ B ∧ p%3≠1) :
    padicValNat 2 n ≤ B^7 :=
  smooth_bound (padicValNat 2 n) B (by omega) hB (unitary_exponent_budget n h hiff he odd) hs

end E1052Multiplicity

/- The reservation of the three factors of 3 from 17+1 and 83+1 follows
@adammcarter's odd_count proof in the accepted 3^11 R1 reduction.
The prime-multiset extraction and the valuation contribution for each 3 in the
exponent sharpen the previous distinct-prime count. -/
namespace E1052Multiplicity
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1 hiding H1 H2 H3 main

theorem sharpened_exponent_budget {m : ℕ} {P : Finset ℕ} (hP : ∀ p∈P,p.Prime ∧ p≠2) (h3P : 3∉P)
    (E : (2^m+1)*(1+3^11)*∏ p∈P,(p+1) = 2^(m+1)*3^11*∏ p∈P,p)
    (hm : m%2=1) : (m.primeFactorsList.filter (fun p => p%3=0)).length +
      (m.primeFactorsList.filter (fun p => p%3=2)).length ≤ 6 := by
  classical
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := by simp
  obtain ⟨S1,S2,_,S4,S5,_,S7,_⟩ := facts hP hK E
  have g67 : 67 ∈ P := S7 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 67 g67 (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have not_two : ¬2 ∣ 2^m+1 := by
    have h : 2∣2^m := dvd_pow_self _ (by omega : m≠0)
    omega
  have g5 := ElevenLeaves.five_in_simple_primes hP h3P E
  have pow4 (k : ℕ) : 2^(4*k)%5=1 := by
    induction k with
    | zero => decide
    | succ k ih =>
      rw [Nat.mul_succ, pow_add, Nat.mul_mod, ih]
      decide
  have not5 : ¬5 ∣ 2^m+1 := by
    obtain h | h : m=4*(m/4)+1 ∨ m=4*(m/4)+3 := by omega
    all_goals
      intro hd
      rw [Nat.dvd_iff_mod_eq_zero, h, pow_add, Nat.add_mod, Nat.mul_mod, pow4] at hd
      norm_num at hd
  have h := count_from_sources m 11 4 P {5,17,83} hm
    (fun q pr res h => S5 q pr (by rintro rfl; exact not_two ((dvd_mul_right 2 2).trans h))
      (hnz (by omega)) h)
    (fun q pr d res => S2 q pr (by rintro rfl; exact not_two d) (hnz (by omega)) d)
    (by simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro g5 (And.intro g17 g83))
    (by
      intro x hx hd
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact not5 hd
      · exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) hd 67 g67 (by norm_num)
      · exact S4 83 (by norm_num) (by norm_num) (hnz (by norm_num)) hd 331 g331 (by norm_num))
    (by norm_num [Finset.prod_insert]) (fun _ hS h => budget_kernel3 hP h3P E hS h)
  omega

end E1052Multiplicity

/- Additional finite obstructions for the exponent-eleven balance. -/

namespace E1052NewSieve

open Finset
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (facts prime_dvd_prime_pow)

private theorem binary_power {M : Type*} [Monoid M] (n : ℕ) (a : M) :
    npowBinRec n a = a^n := by
  induction n with
  | zero => simp [npowBinRec_zero]
  | succ n ih => rw [npowBinRec_succ, ih, pow_succ]

private theorem power_plus_one_dvd (d q : ℕ)
    (cert : npowBinRec d (2 : ZMod q) + 1 = 0) : q ∣ 2^d+1 := by
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, binary_power] using cert

/-- The factor 5867 of `2^419+1` forces an incompatible chain of divisors. -/
theorem block_419 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^419+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g5867 : 5867 ∈ P := start 5867 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 419 5867 (by decide)).trans hd)
  have g163 : 163 ∈ P := step 163 (by norm_num) (by decide) (by decide) 5867 g5867 (by norm_num)
  have g41 : 41 ∈ P := step 41 (by norm_num) (by decide) (by decide) 163 g163 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 41 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 41 g41 83 g83
    (by norm_num) (by norm_num))

/-- The factor 4211 of `2^421+1` forces an incompatible chain of divisors. -/
theorem block_421 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^421+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g4211 : 4211 ∈ P := start 4211 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 421 4211 (by decide)).trans hd)
  have g13 : 13 ∈ P := step 13 (by norm_num) (by decide) (by decide) 4211 g4211 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 13 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 13 g13 83 g83
    (by norm_num) (by norm_num))

/-- The factor 11597 of `2^446+1` forces an incompatible chain of divisors. -/
theorem block_446 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^446+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g11597 : 11597 ∈ P := start 11597 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 446 11597 (by decide)).trans hd)
  have g1933 : 1933 ∈ P := step 1933 (by norm_num) (by decide) (by decide) 11597 g11597 (by norm_num)
  have g967 : 967 ∈ P := step 967 (by norm_num) (by decide) (by decide) 1933 g1933 (by norm_num)
  exact square 11 (by norm_num) (by decide) (by decide) 967 g967 (by norm_num)

/-- The factor 5449 of `2^454+1` forces an incompatible chain of divisors. -/
theorem block_454 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^454+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g5449 : 5449 ∈ P := start 5449 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 454 5449 (by decide)).trans hd)
  exact square 5 (by norm_num) (by decide) (by decide) 5449 g5449 (by norm_num)

/-- The factor 2749 of `2^458+1` forces an incompatible chain of divisors. -/
theorem block_458 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^458+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g2749 : 2749 ∈ P := start 2749 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 458 2749 (by decide)).trans hd)
  exact square 5 (by norm_num) (by decide) (by decide) 2749 g2749 (by norm_num)

/-- The factor 99577 of `2^461+1` forces an incompatible chain of divisors. -/
theorem block_461 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^461+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g99577 : 99577 ∈ P := start 99577 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 461 99577 (by decide)).trans hd)
  have g49789 : 49789 ∈ P := step 49789 (by norm_num) (by decide) (by decide) 99577 g99577 (by norm_num)
  have g13 : 13 ∈ P := step 13 (by norm_num) (by decide) (by decide) 49789 g49789 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 13 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 13 g13 83 g83
    (by norm_num) (by norm_num))

/-- The factor 30757 of `2^466+1` forces an incompatible chain of divisors. -/
theorem block_466 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^466+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g30757 : 30757 ∈ P := start 30757 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 466 30757 (by decide)).trans hd)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 30757 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 30757 g30757 83 g83
    (by norm_num) (by norm_num))

/-- The factor 163673 of `2^499+1` forces an incompatible chain of divisors. -/
theorem block_499 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^499+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g163673 : 163673 ∈ P := start 163673 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 499 163673 (by decide)).trans hd)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 163673 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 163673 g163673 83 g83
    (by norm_num) (by norm_num))

/-- The factor 1912621 of `2^502+1` forces an incompatible chain of divisors. -/
theorem block_502 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^502+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g1912621 : 1912621 ∈ P := start 1912621 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 502 1912621 (by decide)).trans hd)
  have g956311 : 956311 ∈ P := step 956311 (by norm_num) (by decide) (by decide) 1912621 g1912621 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 956311 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 956311 g956311 83 g83
    (by norm_num) (by norm_num))

/-- The factor 1019 of `2^509+1` forces an incompatible chain of divisors. -/
theorem block_509 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^509+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g1019 : 1019 ∈ P := start 1019 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 509 1019 (by decide)).trans hd)
  have g67 : 67 ∈ P := fixed 67 (by norm_num) (by decide) (by decide) (by norm_num)
  exact (by decide : 1019 ≠ 67) (duplicate 17 (by norm_num) (by decide) (by decide) 1019 g1019 67 g67
    (by norm_num) (by norm_num))

/-- The factor 119929 of `2^526+1` forces an incompatible chain of divisors. -/
theorem block_526 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^526+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g119929 : 119929 ∈ P := start 119929 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 526 119929 (by decide)).trans hd)
  exact conflict 67 (by norm_num) (by decide) (by decide) (by norm_num) 119929 g119929 (by norm_num)

/-- The factor 4289 of `2^536+1` forces an incompatible chain of divisors. -/
theorem block_536 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^536+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g4289 : 4289 ∈ P := start 4289 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 536 4289 (by decide)).trans hd)
  have g13 : 13 ∈ P := step 13 (by norm_num) (by decide) (by decide) 4289 g4289 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 13 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 13 g13 83 g83
    (by norm_num) (by norm_num))

/-- The factor 3229 of `2^538+1` forces an incompatible chain of divisors. -/
theorem block_538 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^538+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g3229 : 3229 ∈ P := start 3229 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 538 3229 (by decide)).trans hd)
  have g67 : 67 ∈ P := fixed 67 (by norm_num) (by decide) (by decide) (by norm_num)
  exact (by decide : 3229 ≠ 67) (duplicate 17 (by norm_num) (by decide) (by decide) 3229 g3229 67 g67
    (by norm_num) (by norm_num))

/-- The factor 86561 of `2^541+1` forces an incompatible chain of divisors. -/
theorem block_541 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^541+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g86561 : 86561 ∈ P := start 86561 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 541 86561 (by decide)).trans hd)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 86561 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 86561 g86561 83 g83
    (by norm_num) (by norm_num))

/-- The factor 97561 of `2^542+1` forces an incompatible chain of divisors. -/
theorem block_542 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^542+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g97561 : 97561 ∈ P := start 97561 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 542 97561 (by decide)).trans hd)
  have g48781 : 48781 ∈ P := step 48781 (by norm_num) (by decide) (by decide) 97561 g97561 (by norm_num)
  have g24391 : 24391 ∈ P := step 24391 (by norm_num) (by decide) (by decide) 48781 g48781 (by norm_num)
  have g3049 : 3049 ∈ P := step 3049 (by norm_num) (by decide) (by decide) 24391 g24391 (by norm_num)
  exact square 5 (by norm_num) (by decide) (by decide) 3049 g3049 (by norm_num)

/-- The factor 1109 of `2^554+1` forces an incompatible chain of divisors. -/
theorem block_554 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^554+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g1109 : 1109 ∈ P := start 1109 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 554 1109 (by decide)).trans hd)
  have g37 : 37 ∈ P := step 37 (by norm_num) (by decide) (by decide) 1109 g1109 (by norm_num)
  have g19 : 19 ∈ P := step 19 (by norm_num) (by decide) (by decide) 37 g37 (by norm_num)
  exact (by decide : 19 ≠ 1109) (duplicate 5 (by norm_num) (by decide) (by decide) 19 g19 1109 g1109
    (by norm_num) (by norm_num))

/-- The factor 124769 of `2^557+1` forces an incompatible chain of divisors. -/
theorem block_557 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^557+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g124769 : 124769 ∈ P := start 124769 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 557 124769 (by decide)).trans hd)
  have g4159 : 4159 ∈ P := step 4159 (by norm_num) (by decide) (by decide) 124769 g124769 (by norm_num)
  exact (by decide : 4159 ≠ 124769) (duplicate 5 (by norm_num) (by decide) (by decide) 4159 g4159 124769 g124769
    (by norm_num) (by norm_num))

/-- The factor 3373 of `2^562+1` forces an incompatible chain of divisors. -/
theorem block_562 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^562+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g3373 : 3373 ∈ P := start 3373 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 562 3373 (by decide)).trans hd)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 3373 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 3373 g3373 83 g83
    (by norm_num) (by norm_num))

/-- The factor 10243 of `2^569+1` forces an incompatible chain of divisors. -/
theorem block_569 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^569+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g10243 : 10243 ∈ P := start 10243 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 569 10243 (by decide)).trans hd)
  have g13 : 13 ∈ P := step 13 (by norm_num) (by decide) (by decide) 10243 g10243 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 13 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 13 g13 83 g83
    (by norm_num) (by norm_num))

/-- The factor 75011 of `2^577+1` forces an incompatible chain of divisors. -/
theorem block_577 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^577+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g75011 : 75011 ∈ P := start 75011 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 577 75011 (by decide)).trans hd)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 75011 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 75011 g75011 83 g83
    (by norm_num) (by norm_num))

/-- The factor 5861 of `2^586+1` forces an incompatible chain of divisors. -/
theorem block_586 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^586+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g5861 : 5861 ∈ P := start 5861 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 586 5861 (by decide)).trans hd)
  have g977 : 977 ∈ P := step 977 (by norm_num) (by decide) (by decide) 5861 g5861 (by norm_num)
  have g163 : 163 ∈ P := step 163 (by norm_num) (by decide) (by decide) 977 g977 (by norm_num)
  have g41 : 41 ∈ P := step 41 (by norm_num) (by decide) (by decide) 163 g163 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 41 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 41 g41 83 g83
    (by norm_num) (by norm_num))

/-- The factor 115331 of `2^607+1` forces an incompatible chain of divisors. -/
theorem block_607 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^607+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g115331 : 115331 ∈ P := start 115331 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 607 115331 (by decide)).trans hd)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 115331 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 115331 g115331 83 g83
    (by norm_num) (by norm_num))

/-- The factor 1229 of `2^614+1` forces an incompatible chain of divisors. -/
theorem block_614 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^614+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g1229 : 1229 ∈ P := start 1229 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 614 1229 (by decide)).trans hd)
  have g41 : 41 ∈ P := step 41 (by norm_num) (by decide) (by decide) 1229 g1229 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 41 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 41 g41 83 g83
    (by norm_num) (by norm_num))

/-- The factor 4937 of `2^617+1` forces an incompatible chain of divisors. -/
theorem block_617 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^617+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g4937 : 4937 ∈ P := start 4937 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 617 4937 (by decide)).trans hd)
  have g823 : 823 ∈ P := step 823 (by norm_num) (by decide) (by decide) 4937 g4937 (by norm_num)
  have g103 : 103 ∈ P := step 103 (by norm_num) (by decide) (by decide) 823 g823 (by norm_num)
  have g13 : 13 ∈ P := step 13 (by norm_num) (by decide) (by decide) 103 g103 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 13 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 13 g13 83 g83
    (by norm_num) (by norm_num))

/-- The factor 6221 of `2^622+1` forces an incompatible chain of divisors. -/
theorem block_622 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^622+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g6221 : 6221 ∈ P := start 6221 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 622 6221 (by decide)).trans hd)
  have g67 : 67 ∈ P := fixed 67 (by norm_num) (by decide) (by decide) (by norm_num)
  exact (by decide : 6221 ≠ 67) (duplicate 17 (by norm_num) (by decide) (by decide) 6221 g6221 67 g67
    (by norm_num) (by norm_num))

/-- The factor 42569 of `2^626+1` forces an incompatible chain of divisors. -/
theorem block_626 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^626+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g42569 : 42569 ∈ P := start 42569 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 626 42569 (by decide)).trans hd)
  have g43 : 43 ∈ P := step 43 (by norm_num) (by decide) (by decide) 42569 g42569 (by norm_num)
  exact (by decide : 43 ≠ 42569) (duplicate 11 (by norm_num) (by decide) (by decide) 43 g43 42569 g42569
    (by norm_num) (by norm_num))

/-- The factor 32051 of `2^641+1` forces an incompatible chain of divisors. -/
theorem block_641 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^641+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g32051 : 32051 ∈ P := start 32051 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 641 32051 (by decide)).trans hd)
  have g2671 : 2671 ∈ P := step 2671 (by norm_num) (by decide) (by decide) 32051 g32051 (by norm_num)
  have g167 : 167 ∈ P := step 167 (by norm_num) (by decide) (by decide) 2671 g2671 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 167 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 167 g167 83 g83
    (by norm_num) (by norm_num))

/-- The factor 67219 of `2^659+1` forces an incompatible chain of divisors. -/
theorem block_659 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^659+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g67219 : 67219 ∈ P := start 67219 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 659 67219 (by decide)).trans hd)
  have g3361 : 3361 ∈ P := step 3361 (by norm_num) (by decide) (by decide) 67219 g67219 (by norm_num)
  exact square 41 (by norm_num) (by decide) (by decide) 3361 g3361 (by norm_num)

/-- The factor 206233 of `2^661+1` forces an incompatible chain of divisors. -/
theorem block_661 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^661+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g206233 : 206233 ∈ P := start 206233 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 661 206233 (by decide)).trans hd)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 206233 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 206233 g206233 83 g83
    (by norm_num) (by norm_num))

/-- The factor 589181 of `2^662+1` forces an incompatible chain of divisors. -/
theorem block_662 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^662+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g589181 : 589181 ∈ P := start 589181 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 662 589181 (by decide)).trans hd)
  have g113 : 113 ∈ P := step 113 (by norm_num) (by decide) (by decide) 589181 g589181 (by norm_num)
  have g19 : 19 ∈ P := step 19 (by norm_num) (by decide) (by decide) 113 g113 (by norm_num)
  have g79 : 79 ∈ P := step 79 (by norm_num) (by decide) (by decide) 589181 g589181 (by norm_num)
  exact (by decide : 19 ≠ 79) (duplicate 5 (by norm_num) (by decide) (by decide) 19 g19 79 g79
    (by norm_num) (by norm_num))

/-- The factor 32353 of `2^674+1` forces an incompatible chain of divisors. -/
theorem block_674 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^674+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g32353 : 32353 ∈ P := start 32353 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 674 32353 (by decide)).trans hd)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 32353 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 32353 g32353 83 g83
    (by norm_num) (by norm_num))

/-- The factor 1676083 of `2^683+1` forces an incompatible chain of divisors. -/
theorem block_683 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^683+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g1676083 : 1676083 ∈ P := start 1676083 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 683 1676083 (by decide)).trans hd)
  have g14449 : 14449 ∈ P := step 14449 (by norm_num) (by decide) (by decide) 1676083 g1676083 (by norm_num)
  have g29 : 29 ∈ P := step 29 (by norm_num) (by decide) (by decide) 1676083 g1676083 (by norm_num)
  exact (by decide : 14449 ≠ 29) (duplicate 5 (by norm_num) (by decide) (by decide) 14449 g14449 29 g29
    (by norm_num) (by norm_num))

/-- The factor 763613 of `2^698+1` forces an incompatible chain of divisors. -/
theorem block_698 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^698+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g763613 : 763613 ∈ P := start 763613 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 698 763613 (by decide)).trans hd)
  have g179 : 179 ∈ P := step 179 (by norm_num) (by decide) (by decide) 763613 g763613 (by norm_num)
  have g79 : 79 ∈ P := step 79 (by norm_num) (by decide) (by decide) 763613 g763613 (by norm_num)
  exact (by decide : 179 ≠ 79) (duplicate 5 (by norm_num) (by decide) (by decide) 179 g179 79 g79
    (by norm_num) (by norm_num))

/-- The factor 290497 of `2^712+1` forces an incompatible chain of divisors. -/
theorem block_712 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^712+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g290497 : 290497 ∈ P := start 290497 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 712 290497 (by decide)).trans hd)
  have g13 : 13 ∈ P := step 13 (by norm_num) (by decide) (by decide) 290497 g290497 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 13 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 13 g13 83 g83
    (by norm_num) (by norm_num))

/-- The factor 585889 of `2^718+1` forces an incompatible chain of divisors. -/
theorem block_718 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^718+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g585889 : 585889 ∈ P := start 585889 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 718 585889 (by decide)).trans hd)
  have g41 : 41 ∈ P := step 41 (by norm_num) (by decide) (by decide) 585889 g585889 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 41 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 41 g41 83 g83
    (by norm_num) (by norm_num))

/-- The factor 11633 of `2^727+1` forces an incompatible chain of divisors. -/
theorem block_727 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^727+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g11633 : 11633 ∈ P := start 11633 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 727 11633 (by decide)).trans hd)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 11633 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 11633 g11633 83 g83
    (by norm_num) (by norm_num))

/-- The factor 1493 of `2^746+1` forces an incompatible chain of divisors. -/
theorem block_746 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^746+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g1493 : 1493 ∈ P := start 1493 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 746 1493 (by decide)).trans hd)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  exact (by decide : 1493 ≠ 331) (duplicate 83 (by norm_num) (by decide) (by decide) 1493 g1493 331 g331
    (by norm_num) (by norm_num))

/-- The factor 274867 of `2^751+1` forces an incompatible chain of divisors. -/
theorem block_751 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^751+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g274867 : 274867 ∈ P := start 274867 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 751 274867 (by decide)).trans hd)
  have g6247 : 6247 ∈ P := step 6247 (by norm_num) (by decide) (by decide) 274867 g274867 (by norm_num)
  exact (by decide : 6247 ≠ 274867) (duplicate 11 (by norm_num) (by decide) (by decide) 6247 g6247 274867 g274867
    (by norm_num) (by norm_num))

/-- The factor 4549 of `2^758+1` forces an incompatible chain of divisors. -/
theorem block_758 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^758+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g4549 : 4549 ∈ P := start 4549 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 758 4549 (by decide)).trans hd)
  exact square 5 (by norm_num) (by decide) (by decide) 4549 g4549 (by norm_num)

/-- The factor 4597 of `2^766+1` forces an incompatible chain of divisors. -/
theorem block_766 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^766+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g4597 : 4597 ∈ P := start 4597 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 766 4597 (by decide)).trans hd)
  exact square 11 (by norm_num) (by decide) (by decide) 4597 g4597 (by norm_num)

/-- The factor 36913 of `2^769+1` forces an incompatible chain of divisors. -/
theorem block_769 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^769+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g36913 : 36913 ∈ P := start 36913 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 769 36913 (by decide)).trans hd)
  have g18457 : 18457 ∈ P := step 18457 (by norm_num) (by decide) (by decide) 36913 g36913 (by norm_num)
  have g839 : 839 ∈ P := step 839 (by norm_num) (by decide) (by decide) 18457 g18457 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 839 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 839 g839 83 g83
    (by norm_num) (by norm_num))

/-- The factor 533371 of `2^773+1` forces an incompatible chain of divisors. -/
theorem block_773 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^773+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g533371 : 533371 ∈ P := start 533371 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 773 533371 (by decide)).trans hd)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 533371 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 533371 g533371 83 g83
    (by norm_num) (by norm_num))

/-- The factor 782209 of `2^776+1` forces an incompatible chain of divisors. -/
theorem block_776 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^776+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g782209 : 782209 ∈ P := start 782209 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 776 782209 (by decide)).trans hd)
  have g13 : 13 ∈ P := step 13 (by norm_num) (by decide) (by decide) 782209 g782209 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 13 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 13 g13 83 g83
    (by norm_num) (by norm_num))

/-- The factor 51349 of `2^778+1` forces an incompatible chain of divisors. -/
theorem block_778 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^778+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g51349 : 51349 ∈ P := start 51349 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 778 51349 (by decide)).trans hd)
  exact square 5 (by norm_num) (by decide) (by decide) 51349 g51349 (by norm_num)

/-- The factor 942827 of `2^787+1` forces an incompatible chain of divisors. -/
theorem block_787 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^787+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g942827 : 942827 ∈ P := start 942827 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 787 942827 (by decide)).trans hd)
  have g78569 : 78569 ∈ P := step 78569 (by norm_num) (by decide) (by decide) 942827 g942827 (by norm_num)
  have g97 : 97 ∈ P := step 97 (by norm_num) (by decide) (by decide) 78569 g78569 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 97 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 97 g97 83 g83
    (by norm_num) (by norm_num))

/-- The factor 11117 of `2^794+1` forces an incompatible chain of divisors. -/
theorem block_794 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^794+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g11117 : 11117 ∈ P := start 11117 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 794 11117 (by decide)).trans hd)
  have g67 : 67 ∈ P := fixed 67 (by norm_num) (by decide) (by decide) (by norm_num)
  exact (by decide : 11117 ≠ 67) (duplicate 17 (by norm_num) (by decide) (by decide) 11117 g11117 67 g67
    (by norm_num) (by norm_num))

/-- The factor 875107 of `2^797+1` forces an incompatible chain of divisors. -/
theorem block_797 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^797+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g875107 : 875107 ∈ P := start 875107 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 797 875107 (by decide)).trans hd)
  have g13 : 13 ∈ P := step 13 (by norm_num) (by decide) (by decide) 875107 g875107 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 13 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 13 g13 83 g83
    (by norm_num) (by norm_num))

/-- The factor 11299 of `2^807+1` forces an incompatible chain of divisors. -/
theorem block_807 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^807+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g11299 : 11299 ∈ P := start 11299 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 807 11299 (by decide)).trans hd)
  exact square 5 (by norm_num) (by decide) (by decide) 11299 g11299 (by norm_num)

/-- The factor 203617 of `2^808+1` forces an incompatible chain of divisors. -/
theorem block_808 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^808+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g203617 : 203617 ∈ P := start 203617 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 808 203617 (by decide)).trans hd)
  have g1669 : 1669 ∈ P := step 1669 (by norm_num) (by decide) (by decide) 203617 g203617 (by norm_num)
  have g167 : 167 ∈ P := step 167 (by norm_num) (by decide) (by decide) 1669 g1669 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 167 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 167 g167 83 g83
    (by norm_num) (by norm_num))

/-- The factor 14563 of `2^809+1` forces an incompatible chain of divisors. -/
theorem block_809 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^809+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g14563 : 14563 ∈ P := start 14563 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 809 14563 (by decide)).trans hd)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  exact (by decide : 14563 ≠ 661) (duplicate 331 (by norm_num) (by decide) (by decide) 14563 g14563 661 g661
    (by norm_num) (by norm_num))

/-- The factor 450403 of `2^813+1` forces an incompatible chain of divisors. -/
theorem block_813 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^813+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g450403 : 450403 ∈ P := start 450403 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 813 450403 (by decide)).trans hd)
  have g112601 : 112601 ∈ P := step 112601 (by norm_num) (by decide) (by decide) 450403 g450403 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 112601 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 112601 g112601 83 g83
    (by norm_num) (by norm_num))

/-- The factor 1637 of `2^818+1` forces an incompatible chain of divisors. -/
theorem block_818 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^818+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g1637 : 1637 ∈ P := start 1637 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 818 1637 (by decide)).trans hd)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 1637 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 1637 g1637 83 g83
    (by norm_num) (by norm_num))

/-- The factor 6569 of `2^821+1` forces an incompatible chain of divisors. -/
theorem block_821 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^821+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g6569 : 6569 ∈ P := start 6569 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 821 6569 (by decide)).trans hd)
  have g73 : 73 ∈ P := step 73 (by norm_num) (by decide) (by decide) 6569 g6569 (by norm_num)
  have g37 : 37 ∈ P := step 37 (by norm_num) (by decide) (by decide) 73 g73 (by norm_num)
  have g19 : 19 ∈ P := step 19 (by norm_num) (by decide) (by decide) 37 g37 (by norm_num)
  exact (by decide : 19 ≠ 6569) (duplicate 5 (by norm_num) (by decide) (by decide) 19 g19 6569 g6569
    (by norm_num) (by norm_num))

/-- The factor 316033 of `2^823+1` forces an incompatible chain of divisors. -/
theorem block_823 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^823+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g316033 : 316033 ∈ P := start 316033 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 823 316033 (by decide)).trans hd)
  have g158017 : 158017 ∈ P := step 158017 (by norm_num) (by decide) (by decide) 316033 g316033 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 158017 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 158017 g158017 83 g83
    (by norm_num) (by norm_num))

/-- The factor 88993 of `2^824+1` forces an incompatible chain of divisors. -/
theorem block_824 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^824+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g88993 : 88993 ∈ P := start 88993 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 824 88993 (by decide)).trans hd)
  have g44497 : 44497 ∈ P := step 44497 (by norm_num) (by decide) (by decide) 88993 g88993 (by norm_num)
  have g1171 : 1171 ∈ P := step 1171 (by norm_num) (by decide) (by decide) 44497 g44497 (by norm_num)
  have g293 : 293 ∈ P := step 293 (by norm_num) (by decide) (by decide) 1171 g1171 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 293 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 293 g293 83 g83
    (by norm_num) (by norm_num))

/-- The factor 53633 of `2^838+1` forces an incompatible chain of divisors. -/
theorem block_838 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^838+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g53633 : 53633 ∈ P := start 53633 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 838 53633 (by decide)).trans hd)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 53633 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 53633 g53633 83 g83
    (by norm_num) (by norm_num))

/-- The factor 1489441 of `2^856+1` forces an incompatible chain of divisors. -/
theorem block_856 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^856+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g1489441 : 1489441 ∈ P := start 1489441 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 856 1489441 (by decide)).trans hd)
  have g744721 : 744721 ∈ P := step 744721 (by norm_num) (by decide) (by decide) 1489441 g1489441 (by norm_num)
  have g33851 : 33851 ∈ P := step 33851 (by norm_num) (by decide) (by decide) 744721 g744721 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 33851 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 33851 g33851 83 g83
    (by norm_num) (by norm_num))

/-- The factor 91373 of `2^862+1` forces an incompatible chain of divisors. -/
theorem block_862 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^862+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g91373 : 91373 ∈ P := start 91373 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 862 91373 (by decide)).trans hd)
  have g97 : 97 ∈ P := step 97 (by norm_num) (by decide) (by decide) 91373 g91373 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 97 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 97 g97 83 g83
    (by norm_num) (by norm_num))

/-- The factor 1733 of `2^866+1` forces an incompatible chain of divisors. -/
theorem block_866 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^866+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g1733 : 1733 ∈ P := start 1733 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 866 1733 (by decide)).trans hd)
  have g67 : 67 ∈ P := fixed 67 (by norm_num) (by decide) (by decide) (by norm_num)
  exact (by decide : 1733 ≠ 67) (duplicate 17 (by norm_num) (by decide) (by decide) 1733 g1733 67 g67
    (by norm_num) (by norm_num))

/-- The factor 29819 of `2^877+1` forces an incompatible chain of divisors. -/
theorem block_877 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^877+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g29819 : 29819 ∈ P := start 29819 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 877 29819 (by decide)).trans hd)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 29819 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 29819 g29819 83 g83
    (by norm_num) (by norm_num))

/-- The factor 695377 of `2^878+1` forces an incompatible chain of divisors. -/
theorem block_878 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^878+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g695377 : 695377 ∈ P := start 695377 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 878 695377 (by decide)).trans hd)
  have g9397 : 9397 ∈ P := step 9397 (by norm_num) (by decide) (by decide) 695377 g695377 (by norm_num)
  exact (by decide : 9397 ≠ 695377) (duplicate 37 (by norm_num) (by decide) (by decide) 9397 g9397 695377 g695377
    (by norm_num) (by norm_num))

/-- The factor 22907 of `2^881+1` forces an incompatible chain of divisors. -/
theorem block_881 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^881+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g22907 : 22907 ∈ P := start 22907 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 881 22907 (by decide)).trans hd)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  exact (by decide : 22907 ≠ 331) (duplicate 83 (by norm_num) (by decide) (by decide) 22907 g22907 331 g331
    (by norm_num) (by norm_num))

/-- The factor 21193 of `2^883+1` forces an incompatible chain of divisors. -/
theorem block_883 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^883+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g21193 : 21193 ∈ P := start 21193 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 883 21193 (by decide)).trans hd)
  have g10597 : 10597 ∈ P := step 10597 (by norm_num) (by decide) (by decide) 21193 g21193 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 10597 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 10597 g10597 83 g83
    (by norm_num) (by norm_num))

/-- The factor 5323 of `2^887+1` forces an incompatible chain of divisors. -/
theorem block_887 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^887+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g5323 : 5323 ∈ P := start 5323 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 887 5323 (by decide)).trans hd)
  exact square 11 (by norm_num) (by decide) (by decide) 5323 g5323 (by norm_num)

/-- The factor 3593 of `2^898+1` forces an incompatible chain of divisors. -/
theorem block_898 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^898+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g3593 : 3593 ∈ P := start 3593 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 898 3593 (by decide)).trans hd)
  have g599 : 599 ∈ P := step 599 (by norm_num) (by decide) (by decide) 3593 g3593 (by norm_num)
  exact square 5 (by norm_num) (by decide) (by decide) 599 g599 (by norm_num)

/-- The factor 3617 of `2^904+1` forces an incompatible chain of divisors. -/
theorem block_904 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^904+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g3617 : 3617 ∈ P := start 3617 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 904 3617 (by decide)).trans hd)
  exact conflict 67 (by norm_num) (by decide) (by decide) (by norm_num) 3617 g3617 (by norm_num)

/-- The factor 830833 of `2^911+1` forces an incompatible chain of divisors. -/
theorem block_911 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^911+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g830833 : 830833 ∈ P := start 830833 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 911 830833 (by decide)).trans hd)
  have g3271 : 3271 ∈ P := step 3271 (by norm_num) (by decide) (by decide) 830833 g830833 (by norm_num)
  have g409 : 409 ∈ P := step 409 (by norm_num) (by decide) (by decide) 3271 g3271 (by norm_num)
  have g41 : 41 ∈ P := step 41 (by norm_num) (by decide) (by decide) 409 g409 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 41 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 41 g41 83 g83
    (by norm_num) (by norm_num))

/-- The factor 71293 of `2^914+1` forces an incompatible chain of divisors. -/
theorem block_914 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^914+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g71293 : 71293 ∈ P := start 71293 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 914 71293 (by decide)).trans hd)
  have g829 : 829 ∈ P := step 829 (by norm_num) (by decide) (by decide) 71293 g71293 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  exact (by decide : 829 ≠ 331) (duplicate 83 (by norm_num) (by decide) (by decide) 829 g829 331 g331
    (by norm_num) (by norm_num))

/-- The factor 14753 of `2^922+1` forces an incompatible chain of divisors. -/
theorem block_922 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^922+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g14753 : 14753 ∈ P := start 14753 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 922 14753 (by decide)).trans hd)
  have g2459 : 2459 ∈ P := step 2459 (by norm_num) (by decide) (by decide) 14753 g14753 (by norm_num)
  have g41 : 41 ∈ P := step 41 (by norm_num) (by decide) (by decide) 2459 g2459 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 41 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 41 g41 83 g83
    (by norm_num) (by norm_num))

/-- The factor 1867 of `2^933+1` forces an incompatible chain of divisors. -/
theorem block_933 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^933+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g1867 : 1867 ∈ P := start 1867 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 933 1867 (by decide)).trans hd)
  have g467 : 467 ∈ P := step 467 (by norm_num) (by decide) (by decide) 1867 g1867 (by norm_num)
  have g13 : 13 ∈ P := step 13 (by norm_num) (by decide) (by decide) 467 g467 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 13 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 13 g13 83 g83
    (by norm_num) (by norm_num))

/-- The factor 252181 of `2^934+1` forces an incompatible chain of divisors. -/
theorem block_934 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^934+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g252181 : 252181 ∈ P := start 252181 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 934 252181 (by decide)).trans hd)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 252181 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 252181 g252181 83 g83
    (by norm_num) (by norm_num))

/-- The factor 1431737 of `2^937+1` forces an incompatible chain of divisors. -/
theorem block_937 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^937+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g1431737 : 1431737 ∈ P := start 1431737 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 937 1431737 (by decide)).trans hd)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 1431737 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 1431737 g1431737 83 g83
    (by norm_num) (by norm_num))

/-- The factor 1738969 of `2^941+1` forces an incompatible chain of divisors. -/
theorem block_941 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^941+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g1738969 : 1738969 ∈ P := start 1738969 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 941 1738969 (by decide)).trans hd)
  have g173897 : 173897 ∈ P := step 173897 (by norm_num) (by decide) (by decide) 1738969 g1738969 (by norm_num)
  have g9661 : 9661 ∈ P := step 9661 (by norm_num) (by decide) (by decide) 173897 g173897 (by norm_num)
  have g4831 : 4831 ∈ P := step 4831 (by norm_num) (by decide) (by decide) 9661 g9661 (by norm_num)
  have g151 : 151 ∈ P := step 151 (by norm_num) (by decide) (by decide) 4831 g4831 (by norm_num)
  have g19 : 19 ∈ P := step 19 (by norm_num) (by decide) (by decide) 151 g151 (by norm_num)
  exact (by decide : 19 ≠ 1738969) (duplicate 5 (by norm_num) (by decide) (by decide) 19 g19 1738969 g1738969
    (by norm_num) (by norm_num))

/-- The factor 13259 of `2^947+1` forces an incompatible chain of divisors. -/
theorem block_947 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^947+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g13259 : 13259 ∈ P := start 13259 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 947 13259 (by decide)).trans hd)
  have g67 : 67 ∈ P := fixed 67 (by norm_num) (by decide) (by decide) (by norm_num)
  exact (by decide : 13259 ≠ 67) (duplicate 17 (by norm_num) (by decide) (by decide) 13259 g13259 67 g67
    (by norm_num) (by norm_num))

/-- The factor 440953 of `2^967+1` forces an incompatible chain of divisors. -/
theorem block_967 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^967+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g440953 : 440953 ∈ P := start 440953 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 967 440953 (by decide)).trans hd)
  have g4691 : 4691 ∈ P := step 4691 (by norm_num) (by decide) (by decide) 440953 g440953 (by norm_num)
  have g67 : 67 ∈ P := fixed 67 (by norm_num) (by decide) (by decide) (by norm_num)
  exact (by decide : 4691 ≠ 67) (duplicate 17 (by norm_num) (by decide) (by decide) 4691 g4691 67 g67
    (by norm_num) (by norm_num))

/-- The factor 495211 of `2^971+1` forces an incompatible chain of divisors. -/
theorem block_971 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^971+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g495211 : 495211 ∈ P := start 495211 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 971 495211 (by decide)).trans hd)
  have g123803 : 123803 ∈ P := step 123803 (by norm_num) (by decide) (by decide) 495211 g495211 (by norm_num)
  have g181 : 181 ∈ P := step 181 (by norm_num) (by decide) (by decide) 123803 g123803 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 181 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 181 g181 83 g83
    (by norm_num) (by norm_num))

/-- The factor 1949 of `2^974+1` forces an incompatible chain of divisors. -/
theorem block_974 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^974+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g1949 : 1949 ∈ P := start 1949 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 974 1949 (by decide)).trans hd)
  exact square 5 (by norm_num) (by decide) (by decide) 1949 g1949 (by norm_num)

/-- The factor 7817 of `2^977+1` forces an incompatible chain of divisors. -/
theorem block_977 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^977+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g7817 : 7817 ∈ P := start 7817 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 977 7817 (by decide)).trans hd)
  have g1303 : 1303 ∈ P := step 1303 (by norm_num) (by decide) (by decide) 7817 g7817 (by norm_num)
  have g163 : 163 ∈ P := step 163 (by norm_num) (by decide) (by decide) 1303 g1303 (by norm_num)
  have g41 : 41 ∈ P := step 41 (by norm_num) (by decide) (by decide) 163 g163 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 41 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 41 g41 83 g83
    (by norm_num) (by norm_num))

/-- The factor 614153 of `2^997+1` forces an incompatible chain of divisors. -/
theorem block_997 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^997+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g614153 : 614153 ∈ P := start 614153 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 997 614153 (by decide)).trans hd)
  have g102359 : 102359 ∈ P := step 102359 (by norm_num) (by decide) (by decide) 614153 g614153 (by norm_num)
  have g853 : 853 ∈ P := step 853 (by norm_num) (by decide) (by decide) 102359 g102359 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 853 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 853 g853 83 g83
    (by norm_num) (by norm_num))

/-- The factor 43913 of `2^998+1` forces an incompatible chain of divisors. -/
theorem block_998 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (hd : 2^998+1 ∣ 2^m+1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨step, start, duplicate, both, _, square, fixed, conflict⟩ := facts hP hK E
  have g43913 : 43913 ∈ P := start 43913 (by norm_num) (by decide) (by decide)
      ((power_plus_one_dvd 998 43913 (by decide)).trans hd)
  have g13 : 13 ∈ P := step 13 (by norm_num) (by decide) (by decide) 43913 g43913 (by norm_num)
  have g661 : 661 ∈ P := fixed 661 (by norm_num) (by decide) (by decide) (by norm_num)
  have g331 : 331 ∈ P := step 331 (by norm_num) (by decide) (by decide) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := step 83 (by norm_num) (by decide) (by decide) 331 g331 (by norm_num)
  exact (by decide : 13 ≠ 83) (duplicate 7 (by norm_num) (by decide) (by decide) 13 g13 83 g83
    (by norm_num) (by norm_num))


open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1 (two_pow_add_one_dvd_of_odd_mul)

/-- Certify the new levels by reducing each modular exponentiation before
following the forced prime factors. -/
theorem all_certified {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2^m+1)*(1+3^11)*∏ p ∈ P,(p+1) = 2^(m+1)*3^11*∏ p ∈ P,p)
    (d : ℕ) (hd : d ∈ ({419, 421, 446, 454, 458, 461, 466, 499, 502, 509, 526, 536, 538, 541, 542, 554, 557, 562, 569, 577, 586, 607, 614, 617, 622, 626, 641, 659, 661, 662, 674, 683, 698, 712, 718, 727, 746, 751, 758, 766, 769, 773, 776, 778, 787, 794, 797, 807, 808, 809, 813, 818, 821, 823, 824, 838, 856, 862, 866, 877, 878, 881, 883, 887, 898, 904, 911, 914, 922, 933, 934, 937, 941, 947, 967, 971, 974, 977, 997, 998} : Finset ℕ)) : m % (2*d) ≠ d := by
  intro h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact block_419 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_421 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_446 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_454 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_458 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_461 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_466 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_499 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_502 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_509 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_526 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_536 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_538 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_541 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_542 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_554 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_557 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_562 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_569 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_577 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_586 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_607 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_614 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_617 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_622 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_626 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_641 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_659 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_661 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_662 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_674 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_683 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_698 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_712 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_718 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_727 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_746 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_751 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_758 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_766 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_769 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_773 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_776 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_778 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_787 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_794 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_797 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_807 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_808 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_809 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_813 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_818 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_821 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_823 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_824 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_838 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_856 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_862 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_866 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_877 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_878 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_881 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_883 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_887 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_898 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_904 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_911 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_914 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_922 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_933 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_934 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_937 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_941 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_947 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_967 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_971 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_974 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_977 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_997 hP E (two_pow_add_one_dvd_of_odd_mul h)
  · exact block_998 hP E (two_pow_add_one_dvd_of_odd_mul h)

end E1052NewSieve

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R2

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (kernel_balance_one)

/-- The remaining odd exponents have a prime outside the bounded smooth class. -/
def H1 : Prop := 
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 11 →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({4, 16} : Finset ℕ), padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({6, 15, 17, 19, 21, 41, 107, 113, 159, 166, 173, 178, 194, 200, 202, 206, 213, 214,
        218, 226, 227, 232, 233, 237, 239, 241, 248, 253, 254, 263, 267, 274, 278, 279, 283, 293,
        296, 298, 299, 301, 305, 309, 326, 327, 329, 331, 337, 341, 344, 365, 367, 373, 381, 382,
        386, 394, 395, 397, 398} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    5 ∣ n → 1000^6 < padicValNat 2 n →
    (∀ d ∈ ({419, 421, 446, 454, 458, 461, 466, 499, 502, 509, 526, 536, 538, 541, 542, 554, 557, 562, 569, 577, 586, 607, 614, 617, 622, 626, 641, 659, 661, 662, 674, 683, 698, 712, 718, 727, 746, 751, 758, 766, 769, 773, 776, 778, 787, 794, 797, 807, 808, 809, 813, 818, 821, 823, 824, 838, 856, 862, 866, 877, 878, 881, 883, 887, 898, 904, 911, 914, 922, 933, 934, 937, 941, 947, 967, 971, 974, 977, 997, 998} : Finset ℕ), padicValNat 2 n % (2*d) ≠ d) →

    padicValNat 2 n % 2 = 1 →
    ((padicValNat 2 n).primeFactorsList.filter (fun p => p%3=0)).length +
      ((padicValNat 2 n).primeFactorsList.filter (fun p => p%3=2)).length ≤ 6 →
    (¬ ∀ p ∈ (padicValNat 2 n).primeFactors, p ≤ 1000 ∧ p%3 ≠ 1) →
    padicValNat 2 n ≤ A

/-- The even exponent after the forced-prime and modular exclusions. -/
def H2 : Prop := 
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 11 →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({4, 16} : Finset ℕ), padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({6, 15, 17, 19, 21, 41, 107, 113, 159, 166, 173, 178, 194, 200, 202, 206, 213, 214,
        218, 226, 227, 232, 233, 237, 239, 241, 248, 253, 254, 263, 267, 274, 278, 279, 283, 293,
        296, 298, 299, 301, 305, 309, 326, 327, 329, 331, 337, 341, 344, 365, 367, 373, 381, 382,
        386, 394, 395, 397, 398} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    5 ∣ n → 1000^6 < padicValNat 2 n →
    (∀ d ∈ ({419, 421, 446, 454, 458, 461, 466, 499, 502, 509, 526, 536, 538, 541, 542, 554, 557, 562, 569, 577, 586, 607, 614, 617, 622, 626, 641, 659, 661, 662, 674, 683, 698, 712, 718, 727, 746, 751, 758, 766, 769, 773, 776, 778, 787, 794, 797, 807, 808, 809, 813, 818, 821, 823, 824, 838, 856, 862, 866, 877, 878, 881, 883, 887, 898, 904, 911, 914, 922, 933, 934, 937, 941, 947, 967, 971, 974, 977, 997, 998} : Finset ℕ), padicValNat 2 n % (2*d) ≠ d) →

    padicValNat 2 n % 2 = 0 → padicValNat 2 n ≤ A

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1.H1 := by
  rintro ⟨Aodd, odd_case⟩ ⟨Aeven, even_case⟩
  refine ⟨max (1000^6) (max Aodd Aeven), ?_⟩
  intro n hperfect hexc he old₁ old₂ old₃
  by_cases small : padicValNat 2 n ≤ 1000^6
  · exact small.trans (le_max_left _ _)
  have hfive := ElevenLeaves.five_dvd_unitary n hperfect hexc he
  have hn0 : n ≠ 0 := hperfect.2.ne'
  have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
    intro r hr hr2 hr3
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hpos := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have : ¬ 2 ≤ n.factorization r := fun hi =>
      hr3 ((hexc r).mp ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr hi⟩)
    omega
  have h3n : 3 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  have h3pf : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3n, hn0⟩
  have ha : n.factorization 2 = padicValNat 2 n := Nat.factorization_def n Nat.prime_two
  obtain ⟨hP, E⟩ := kernel_balance_one hperfect h3pf (by norm_num) hs
  rw [he,ha] at E
  have modular := E1052NewSieve.all_certified hP E
  have h3P : 3 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({3} : Finset ℕ)) := by simp
  by_cases odd : padicValNat 2 n % 2 = 1
  · have budget := E1052Multiplicity.sharpened_exponent_budget hP h3P E odd
    have not_smooth : ¬ ∀ p ∈ (padicValNat 2 n).primeFactors, p ≤ 1000 ∧ p%3 ≠ 1 := by
      intro smooth
      exact small (E1052Multiplicity.smooth_bound (padicValNat 2 n) 1000 (by omega)
        (by decide) budget smooth)
    exact (odd_case n hperfect hexc he old₁ old₂ old₃ hfive (by omega) modular odd budget not_smooth).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · have even : padicValNat 2 n % 2 = 0 := by omega
    exact (even_case n hperfect hexc he old₁ old₂ old₃ hfive (by omega) modular even).trans
      ((le_max_right _ _).trans (le_max_right _ _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R2
