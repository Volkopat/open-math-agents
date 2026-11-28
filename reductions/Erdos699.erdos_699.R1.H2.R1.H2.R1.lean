import OMAReductions.R_Erdos699_erdos_699_R1_H2_R1

/-!
# A midpoint inequality and an elementary prime sieve for Erdős 699

Credit: @witeg4. The parent counting and carry lemmas are due to @rickmanelius.
Pairing opposite terms of the binomial ratio improves the unpaired estimate.
The smooth part of the gcd is bounded using the largest prime powers at most n.
The finite index restriction uses only the six residue classes modulo six.

The finite_bound_of_smooth_estimate lemma is the arithmetic implication used
with Theorem 2.1(i) of Bugeaud, Evertse and Győry, https://arxiv.org/abs/1708.08290.
Their analytic estimate is external to this formalization.
-/

namespace OMA.R_Erdos699_erdos_699_R1_H2_R1_H2_R1
private lemma six_step (m : ℕ) : Nat.primeCounting' (6*(m+1)+5) ≤ Nat.primeCounting' (6*m+5)+2 := by
  let a := 6*m+5
  have no (v p : ℕ) (hp : 1 < p) (hlt : p < v) (hd : p ∣ v) : ¬v.Prime := by
    intro hv
    rcases (Nat.dvd_prime hv).mp hd with h|h <;> omega
  have h1 : ¬Nat.Prime (a+1) := no _ 2 (by omega) (by dsimp [a]; omega) (by dsimp [a]; omega)
  have h3 : ¬Nat.Prime (a+3) := no _ 2 (by omega) (by dsimp [a]; omega) (by dsimp [a]; omega)
  have h4 : ¬Nat.Prime (a+4) := no _ 3 (by omega) (by dsimp [a]; omega) (by dsimp [a]; omega)
  have h5 : ¬Nat.Prime (a+5) := no _ 2 (by omega) (by dsimp [a]; omega) (by dsimp [a]; omega)
  change Nat.count Nat.Prime (6*(m+1)+5) ≤ Nat.count Nat.Prime a + 2
  rw [show 6*(m+1)+5=a+6 by dsimp [a]; omega]
  iterate 6 rw [Nat.count_succ]
  split_ifs <;> omega

theorem prime_bound {i : ℕ} (hi : 33 ≤ i) : 3*Nat.primeCounting' i ≤ i := by
  have base (m : ℕ) : Nat.primeCounting' (6*(m+6)+5) ≤ 2*(m+6) := by
    induction m with
    | zero => decide
    | succ m ih =>
      have h := six_step (m+6)
      rw [show m+6+1=m+1+6 by omega] at h
      omega
  by_cases hm : 36 ≤ i
  · have h := base (i/6-6)
    rw [Nat.sub_add_cancel (by omega : 6 ≤ i/6)] at h
    have h' := Nat.monotone_primeCounting' (show i ≤ 6*(i/6)+5 by omega)
    omega
  · interval_cases i <;> decide

private lemma paired (J N h : ℕ) (hc : J ≤ N) :
    J*(J+h)*(2*N+h)^2 ≤ N*(N+h)*(2*J+h)^2 := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hc
  nlinarith only [Nat.zero_le (h^2*d*(2*J+d+h))]

private lemma endpoints (N k : ℕ) : N.ascFactorial (k+2) =
    N*(N+k+1)*(N+1).ascFactorial k := by
  calc N.ascFactorial (k+2) = (N+(k+1))*((N+k)*N.ascFactorial k) := by
         rw [Nat.ascFactorial_succ,Nat.ascFactorial_succ]
       _ = _ := by rw [← Nat.succ_ascFactorial N k]; ring

theorem midpoint (h : ℕ) (J N : ℕ) (hc : J ≤ N) :
    J.ascFactorial (h+1)*(2*N+h)^(h+1) ≤ N.ascFactorial (h+1)*(2*J+h)^(h+1) := by
  induction h using Nat.strong_induction_on generalizing J N with
  | h h ih =>
    rcases h with _|h
    · simp [Nat.ascFactorial_succ, mul_comm, mul_left_comm]
    rcases h with _|h
    · simpa [Nat.ascFactorial_succ, mul_assoc, mul_comm, mul_left_comm] using paired J N 1 hc
    · have inner := ih h (by omega) (J+1) (N+1) (by omega)
      rw [show 2*(N+1)+h=2*N+(h+2) by omega,show 2*(J+1)+h=2*J+(h+2) by omega] at inner
      have hp := Nat.mul_le_mul inner (paired J N (h+2) hc)
      rw [show h+1+1+1 = (h+1)+2 by omega,endpoints J (h+1),endpoints N (h+1),pow_add,pow_add]
      convert hp using 1 <;> ring

theorem midpoint_choose {n i j : ℕ} (hi : 0 < i) (hij : i ≤ j) (hjn : j ≤ n) :
    j.choose i * (2*n+1-i)^i ≤ n.choose i * (2*j+1-i)^i := by
  have hz := midpoint (i-1) (j+1-i) (n+1-i) (by omega)
  rw [show i-1+1=i by omega, show 2*(n+1-i)+(i-1)=2*n+1-i by omega,
      show 2*(j+1-i)+(i-1)=2*j+1-i by omega,
      ← Nat.add_descFactorial_eq_ascFactorial', ← Nat.add_descFactorial_eq_ascFactorial',
      show j+1-i+i-1=j by omega,show n+1-i+i-1=n by omega,
      Nat.descFactorial_eq_factorial_mul_choose,Nat.descFactorial_eq_factorial_mul_choose,
      mul_assoc,mul_assoc] at hz
  exact Nat.le_of_mul_le_mul_left hz (Nat.factorial_pos _)

theorem index_restriction {n i j : ℕ} (hmin : 3 ≤ i) (hj : 0 < j)
    (hfar : j^3 < n^2) (hcount : n^(i-Nat.primeCounting' i) ≤ j^i) :
    (4 ≤ i ∧ i ≤ 26) ∨ i=32 := by
  have hq : i < 3*Nat.primeCounting' i := by
    by_contra! h
    have hn : 0 < n := by by_contra! hn; interval_cases n <;> simp at hfar
    have h1 := Nat.pow_le_pow_right hn (show 2*i ≤ (i-Nat.primeCounting' i)*3 by omega)
    have h2 := Nat.pow_le_pow_left hcount 3
    have h3 := Nat.pow_lt_pow_left hfar (by omega : i ≠ 0)
    rw [← pow_mul,← pow_mul] at h2 h3
    rw [Nat.mul_comm i 3] at h2
    omega
  have h32 : i < 33 := by
    by_contra! he
    exact (not_lt_of_ge (prime_bound he)) hq
  have tab : ∀ z : Fin 33, 3 ≤ z.val → z.val < 3*Nat.primeCounting' z.val →
      (4 ≤ z.val ∧ z.val ≤ 26) ∨ z.val=32 := by decide
  exact tab ⟨i,h32⟩ hmin hq


open OMA.R_Erdos699_erdos_699_R1_H2_R1

/-- Prime-power bound discounting up to five low positions forced by i. -/
private def primePowerCap (n i : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range i).filter Nat.Prime, p ^ (Nat.log p n - (if p^5 ∣ i then 5 else if p^4 ∣ i then 4 else if p^3 ∣ i then 3 else if p^2 ∣ i then 2 else if p ∣ i then 1 else 0))

/-- A common prime in the form required by the parent reduction. -/
private def carries (n i j : ℕ) : Prop :=
  ∃ p a b : ℕ, p.Prime ∧ i ≤ p ∧ 0 < a ∧ 0 < b ∧
    n % p ^ a < i % p ^ a ∧ n % p ^ b < j % p ^ b

/-- The low base-p places of i which are zero cannot generate a carry in C(n,i). -/
private lemma valuation_bound {p n i : ℕ} (hp : p.Prime) (hi : 0 < i) (hin : i ≤ n) :
    (n.choose i).factorization p ≤ Nat.log p n - i.factorization p := by
  rw [Nat.factorization_choose hp hin (Nat.lt_succ_self _)]
  let hi' := i.factorization p
  have hsub : ((Finset.Ico 1 (Nat.log p n + 1)).filter
        (fun a => p^a ≤ i % p^a + (n-i) % p^a)) ⊆ Finset.Ico (hi'+1) (Nat.log p n+1) := by
    intro a ha
    obtain ⟨ha,hcarry⟩ := Finset.mem_filter.mp ha
    apply Finset.mem_Ico.mpr
    refine ⟨?_,(Finset.mem_Ico.mp ha).2⟩
    by_contra! h
    have hd := (hp.pow_dvd_iff_le_factorization hi.ne').mpr (show a ≤ i.factorization p by omega)
    rw [Nat.mod_eq_zero_of_dvd hd,zero_add] at hcarry
    exact (Nat.not_le_of_lt (Nat.mod_lt _ (pow_pos hp.pos _))) hcarry
  simpa [Nat.card_Ico,hi'] using Finset.card_le_card hsub

private lemma bound_gcd {n i j : ℕ} (hi : 0 < i) (hij : i ≤ j) (hjn : j ≤ n)
    (hnone : ¬ carries n i j) : n.choose i ≤ primePowerCap n i * j.choose i := by
  let g := Nat.gcd (n.choose i) (n.choose j)
  have hA := Nat.choose_pos (le_trans hij hjn)
  have hB := Nat.choose_pos hij
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hA
  have sub : g.primeFactors ⊆ (Finset.range i).filter Nat.Prime := by
    intro p hp
    have hP := Nat.prime_of_mem_primeFactors hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,hP⟩
    by_contra! hip
    have hd := Nat.dvd_of_mem_primeFactors hp
    obtain ⟨a,ha,ha'⟩ := carry_of_dvd hP (le_trans hij hjn) (dvd_trans hd (Nat.gcd_dvd_left _ _))
    obtain ⟨b,hb,hb'⟩ := carry_of_dvd hP hjn (dvd_trans hd (Nat.gcd_dvd_right _ _))
    exact hnone ⟨p,a,b,hP,hip,ha,hb,ha',hb'⟩
  have hcap : g ≤ primePowerCap n i := by
    calc g = g.factorization.prod (fun p k => p^k) := (Nat.prod_factorization_pow_eq_self hg.ne').symm
         _ = ∏ p ∈ g.primeFactors, p^g.factorization p := by rw [Finsupp.prod,Nat.support_factorization]
         _ ≤ ∏ p ∈ g.primeFactors, p^(Nat.log p n - (if p^5 ∣ i then 5 else if p^4 ∣ i then 4 else if p^3 ∣ i then 3 else if p^2 ∣ i then 2 else if p ∣ i then 1 else 0)) := by
           apply Finset.prod_le_prod (by intros; exact Nat.zero_le _)
           intro p hp
           apply Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors hp).pos
           have hv : (if p^5 ∣ i then 5 else if p^4 ∣ i then 4 else if p^3 ∣ i then 3 else if p^2 ∣ i then 2 else if p ∣ i then 1 else 0) ≤ i.factorization p := by
             have hp := Nat.prime_of_mem_primeFactors hp
             split_ifs with h5 h4 h3 h2 h1
             all_goals first | exact (hp.pow_dvd_iff_le_factorization hi.ne').mp (by first | assumption | simpa only [pow_one] using h1) | exact Nat.zero_le _
           apply le_trans _ (Nat.sub_le_sub_left hv _)
           exact le_trans ((Nat.factorization_le_iff_dvd hg.ne' hA.ne').2 (Nat.gcd_dvd_left _ _) p)
             (valuation_bound (Nat.prime_of_mem_primeFactors hp) hi (le_trans hij hjn))
         _ ≤ primePowerCap n i := Finset.prod_le_prod_of_subset_of_one_le' sub (by
           intro p hp _; exact Nat.one_le_pow _ _ (Finset.mem_filter.mp hp).2.pos)
  exact le_trans (Nat.le_of_dvd (Nat.mul_pos hg hB) (choose_dvd_gcd hij))
    (Nat.mul_le_mul_right (j.choose i) hcap)

/-- An unconditional sufficient condition for a common prime, without factoring either binomial. -/
theorem common_of_midpoint {n i j : ℕ} (hi : 0 < i) (hij : i ≤ j) (hjn : j ≤ n)
    (h : primePowerCap n i * (2*j+1-i)^i < (2*n+1-i)^i) : carries n i j := by
  by_contra hnone
  have hratio := midpoint_choose hi hij hjn
  have hbound := bound_gcd hi hij hjn hnone
  have hu : j.choose i*(2*n+1-i)^i ≤ j.choose i*(primePowerCap n i*(2*j+1-i)^i) := by
    calc _ ≤ n.choose i*(2*j+1-i)^i := hratio
         _ ≤ (primePowerCap n i*j.choose i)*(2*j+1-i)^i := Nat.mul_le_mul_right _ hbound
         _ = _ := by ring
  exact (not_lt_of_ge (Nat.le_of_mul_le_mul_left hu (Nat.choose_pos hij))) h

/-- The arithmetic step for the finite-exceptions argument. A squarefree
polynomial S-part estimate with exponent 7/24 supplies the hypothesis on g. -/
theorem finite_bound_of_smooth_estimate {n i j g C : ℕ} (hn : 0 < n) (hi : 0 < i)
    (hg : 0 < g) (hratio : n^i ≤ g*j^i) (hfar : j^3 < n^2)
    (hS : g^24 ≤ C*n^(7*i)) : n^i < C := by
  have h3 := Nat.pow_le_pow_left hratio 3
  have hj := Nat.pow_lt_pow_left hfar hi.ne'
  have he : (n^i)*n^(2*i) < g^3*n^(2*i) := by
    calc n^i*n^(2*i) = (n^i)^3 := by rw [← pow_add,← pow_mul]; congr 1; omega
         _ ≤ (g*j^i)^3 := h3
         _ = g^3*(j^3)^i := by rw [mul_pow,← pow_mul,← pow_mul,Nat.mul_comm i 3]
         _ < _ := by simpa only [pow_mul] using Nat.mul_lt_mul_of_pos_left hj (pow_pos hg 3)
  have h8 := Nat.pow_lt_pow_left (Nat.lt_of_mul_lt_mul_right he) (by decide : 8 ≠ 0)
  have he' : n^i*n^(7*i) < C*n^(7*i) := by
    calc n^i*n^(7*i) = (n^i)^8 := by rw [← pow_add,← pow_mul]; congr 1; omega
         _ < (g^3)^8 := h8
         _ ≤ _ := by simpa only [← pow_mul] using hS
  exact Nat.lt_of_mul_lt_mul_right he'

private lemma cap_mono (i : ℕ) {l u : ℕ} (h : l ≤ u) : primePowerCap l i ≤ primePowerCap u i := by
  apply Finset.prod_le_prod (by intros; exact Nat.zero_le _)
  intro p hp
  exact Nat.pow_le_pow_right (Finset.mem_filter.mp hp).2.pos (Nat.sub_le_sub_right (Nat.log_mono_right h) _)

/-- Certificate for a cover by intervals. Monotonicity bounds the left side at
the right endpoint and the right side at the left endpoint. -/
private def cert (i limit lo : ℕ) : List ℕ → Bool
  | [] => decide (limit < lo)
  | hi::tail => decide (primePowerCap hi i ^ 3 ≤ lo ^ i) && cert i limit (hi+1) tail

private lemma cert_valid (i limit : ℕ) (ends : List ℕ) (lo n : ℕ)
    (hc : cert i limit lo ends = true) (hl : lo ≤ n) (hu : n ≤ limit) :
    primePowerCap n i ^ 3 ≤ n^i := by
  induction ends generalizing lo with
  | nil =>
    have := of_decide_eq_true hc
    omega
  | cons stop tail ih =>
    obtain ⟨here,later⟩ := Bool.and_eq_true_iff.mp hc
    by_cases h : n ≤ stop
    · exact le_trans (Nat.pow_le_pow_left (cap_mono i h) 3)
        (le_trans (of_decide_eq_true here) (Nat.pow_le_pow_left hl i))
    · exact ih (stop+1) later (by omega)

/-- Above the parent's three-halves threshold, a hypothetical counterexample
forces the cube of the prime-power cap to exceed n^i. -/
private theorem cap_necessary {n i j : ℕ} (hi : 0 < i) (hij : i ≤ j)
    (hjn : j ≤ n) (hf : j^3 < n^2) (hnone : ¬ carries n i j) :
    n^i < primePowerCap n i ^ 3 := by
  have h0 := bound_gcd hi hij hjn hnone
  have hB := Nat.choose_pos hij
  have hratio := choose_ratio hjn i
  have hh : j.choose i*n^i ≤ j.choose i*(primePowerCap n i*j^i) := by
    calc j.choose i*n^i ≤ n.choose i*j^i := hratio
         _ ≤ (primePowerCap n i*j.choose i)*j^i := Nat.mul_le_mul_right _ h0
         _ = j.choose i*(primePowerCap n i*j^i) := by ring
  have h := Nat.le_of_mul_le_mul_left hh hB
  have hg : 0 < primePowerCap n i := by
    by_contra! he
    rw [Nat.eq_zero_of_le_zero he,zero_mul] at h0
    exact (not_lt_of_ge h0) (Nat.choose_pos (le_trans hij hjn))
  have HH : n^i*n^(2*i) < primePowerCap n i^3*n^(2*i) := by
    calc n^i*n^(2*i) = (n^i)^3 := by rw [← pow_add,← pow_mul]; congr 1; omega
         _ ≤ (primePowerCap n i*j^i)^3 := Nat.pow_le_pow_left h 3
         _ = primePowerCap n i^3*(j^3)^i := by rw [mul_pow,← pow_mul,← pow_mul,Nat.mul_comm i 3]
         _ < primePowerCap n i^3*n^(2*i) := by
           rw [pow_mul]; exact Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left hf hi.ne') (pow_pos hg 3)
  exact Nat.lt_of_mul_lt_mul_right HH

private theorem cap23 {n : ℕ} (lo : 70 ≤ n) (hi : n ≤ 2476098) :
    primePowerCap n 23 ^ 3 ≤ n^23 := by
  apply cert_valid 23 2476098 [168, 342, 624, 1330, 2400, 4912, 8191, 15624, 28560, 78124, 130320, 161050, 177146, 262143, 390624, 531440, 1048575, 1771560, 2476098] 70 n _ lo hi
  decide

private theorem cap26 {n : ℕ} (lo : 79 ≤ n) (hi : n ≤ 6131066257800) :
    primePowerCap n 26 ^ 3 ≤ n^26 := by
  apply cert_valid 26 6131066257800 [288, 728, 2400, 6858, 16383, 59048, 161050, 371292, 1419856, 4194303, 8388607, 19487170, 47045880, 129140162, 268435455, 536870911, 893871738, 1977326742, 3404825446, 6975757440, 10604499372, 16983563040, 25937424600, 34359738367, 78310985280, 118587876496, 152587890624, 282429536480, 322687697778, 549755813887, 847288609442, 1792160394036, 2199023255551, 3138428376720, 3814697265624, 4747561509942, 6131066257800] 79 n _ lo hi
  decide

private theorem cap32 {n : ℕ} (lo : 97 ≤ n) (hi : n ≤ 41426511213648) :
    primePowerCap n 32 ^ 3 ≤ n^32 := by
  apply cert_valid 32 41426511213648 [360, 960, 3124, 14640, 29790, 117648, 371292, 923520, 2476098, 6436342, 20511148, 47045880, 148035888, 410338672, 887503680, 1977326742, 6103515624, 16983563040, 27512614110, 78310985280, 137858491848, 285311670610, 678223072848, 1792160394036, 3138428376720, 6131066257800, 14507145975868, 26439622160670, 34522712143930, 41426511213648] 97 n _ lo hi
  decide

/-- Residual hypotheses after the midpoint and prime-power tests. -/
private def remaining (n i j : ℕ) : Prop :=
  i < j ∧ j ≤ n/2 ∧ n ≤ j^2 ∧ j^3 < n^2 ∧ n^(i-Nat.primeCounting' i) ≤ j^i ∧
  3*i < 2*j ∧ (2*n+1-i)^i ≤ primePowerCap n i * (2*j+1-i)^i ∧
  (i=23 → 2476099 ≤ n) ∧ (i=26 → 6131066257801 ≤ n) ∧ (i=32 → 41426511213649 ≤ n)

def H1 : Prop := ∀ n i j : ℕ, 4 ≤ i → i ≤ 26 →
    (i < j ∧ j ≤ n/2 ∧ n ≤ j^2 ∧ j^3 < n^2 ∧ n^(i-Nat.primeCounting' i) ≤ j^i ∧
    3*i < 2*j ∧ (2*n+1-i)^i ≤ (∏ p ∈ (Finset.range i).filter Nat.Prime, p ^ (Nat.log p n - (if p^5 ∣ i then 5 else if p^4 ∣ i then 4 else if p^3 ∣ i then 3 else if p^2 ∣ i then 2 else if p ∣ i then 1 else 0))) * (2*j+1-i)^i ∧
    (i=23 → 2476099 ≤ n) ∧ (i=26 → 6131066257801 ≤ n)) →
    ∃ p a b : ℕ, p.Prime ∧ i ≤ p ∧ 0 < a ∧ 0 < b ∧
      n % p^a < i % p^a ∧ n % p^b < j % p^b

def H2 : Prop := ∀ n j : ℕ, 41426511213649 ≤ n →
    (32 < j ∧ j ≤ n/2 ∧ n ≤ j^2 ∧ j^3 < n^2 ∧ n^(32-Nat.primeCounting' 32) ≤ j^32 ∧
    3*32 < 2*j ∧ (2*n+1-32)^32 ≤ (∏ p ∈ (Finset.range 32).filter Nat.Prime, p ^ (Nat.log p n - (if p^5 ∣ (32 : ℕ) then 5 else if p^4 ∣ (32 : ℕ) then 4 else if p^3 ∣ (32 : ℕ) then 3 else if p^2 ∣ (32 : ℕ) then 2 else if p ∣ (32 : ℕ) then 1 else 0))) * (2*j+1-32)^32) →
    ∃ p a b : ℕ, p.Prime ∧ 32 ≤ p ∧ 0 < a ∧ 0 < b ∧
      n % p^a < 32 % p^a ∧ n % p^b < j % p^b

theorem main : H1 → H2 → OMA.R_Erdos699_erdos_699_R1_H2_R1.H2 := by
  intro h1 h2 n i j hi hij hjn hsq hcub hreg hfar
  change carries n i j
  by_cases h : primePowerCap n i*(2*j+1-i)^i < (2*n+1-i)^i
  · exact common_of_midpoint (by omega) hij.le (by omega) h
  by_contra hnone
  have hc := cap_necessary (by omega) hij.le (by omega) hcub hnone
  have hr : remaining n i j := by
    refine ⟨hij,hjn,hsq,hcub,hreg,hfar,not_lt.mp h,?_,?_,?_⟩
    · rintro rfl; by_contra! hl; exact (not_lt_of_ge (cap23 (by omega) (by omega))) hc
    · rintro rfl; by_contra! hl; exact (not_lt_of_ge (cap26 (by omega) (by omega))) hc
    · rintro rfl; by_contra! hl; exact (not_lt_of_ge (cap32 (by omega) (by omega))) hc
  rcases index_restriction hi (by omega) hcub hreg with ⟨h4,h26⟩|rfl
  · obtain ⟨hij',hd,hs,hc',hp,hf,hm,h23,h26',_⟩ := hr
    exact hnone (h1 n i j h4 h26 ⟨hij',hd,hs,hc',hp,hf,hm,h23,h26'⟩)
  · obtain ⟨hij',hd,hs,hc',hp,hf,hm,_,_,h32⟩ := hr
    exact hnone (h2 n j (h32 rfl) ⟨hij',hd,hs,hc',hp,hf,hm⟩)

/-- A prime power divisor of a binomial coefficient restricts its row to
one of the first k residue classes modulo that same prime power. -/
theorem residue_of_pow_dvd {p n k e : ℕ} (hp : p.Prime) (hkn : k ≤ n)
    (he : 0 < e) (hd : p^e ∣ n.choose k) : n % p^e < k := by
  have hcard := (hp.pow_dvd_iff_le_factorization (Nat.choose_pos hkn).ne').mp hd
  rw [Nat.factorization_choose hp hkn (Nat.lt_succ_self _)] at hcard
  change e ≤ ((Finset.Ico 1 (Nat.log p n+1)).filter
    (fun a => p^a ≤ k % p^a + (n-k) % p^a)).card at hcard
  obtain ⟨a, ha, hae⟩ : ∃ a ∈ (Finset.Ico 1 (Nat.log p n+1)).filter
      (fun a => p^a ≤ k % p^a + (n-k) % p^a), e ≤ a := by
    by_contra! h
    have hs : ((Finset.Ico 1 (Nat.log p n+1)).filter
        (fun a => p^a ≤ k % p^a + (n-k) % p^a)) ⊆ Finset.Ico 1 e := by
      intro a ha
      exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1).1,h a ha⟩
    have bound := Finset.card_le_card hs
    rw [Nat.card_Ico] at bound
    omega
  have hcarry := (Finset.mem_filter.mp ha).2
  have hq : 0 < p^a := pow_pos hp.pos a
  have h1 := Nat.mod_lt k hq
  have h2 := Nat.mod_lt (n-k) hq
  have hsum : n % p^a = (k % p^a + (n-k) % p^a) % p^a := by
    rw [← Nat.add_mod, Nat.add_sub_of_le hkn]
  have hsub : (k % p^a + (n-k) % p^a) % p^a = k % p^a + (n-k) % p^a - p^a := by
    rw [Nat.mod_eq_sub_mod hcarry, Nat.mod_eq_of_lt (by omega)]
  calc n % p^e = (n % p^a) % p^e := (Nat.mod_mod_of_dvd n (pow_dvd_pow p hae)).symm
       _ ≤ n % p^a := Nat.mod_le _ _
       _ < k % p^a := by omega
       _ ≤ k := Nat.mod_le _ _

end OMA.R_Erdos699_erdos_699_R1_H2_R1_H2_R1
