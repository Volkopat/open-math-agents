import OMAStatements.S_oeis_a387724

open Finset OMA.S_oeis_a387724

private def g (x : ℝ) (a : ℕ) : ℝ := ∑ i ∈ range (a+1), x^i

private theorem g_zero (x : ℝ) : g x 0 = 1 := by simp [g]

private theorem g_succ (x : ℝ) (a : ℕ) : g x (a+1) = x*g x a + 1 := by
  unfold g
  rw [sum_range_succ', mul_sum]
  simp_rw [pow_succ', pow_zero]

private theorem g_pos {x : ℝ} (hx : 0 ≤ x) (a : ℕ) : 0 < g x a := by
  induction a with
  | zero => simp [g_zero]
  | succ a ih => rw [g_succ]; positivity

private theorem g_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (a : ℕ) :
    g x a ≤ g y a := by
  exact sum_le_sum fun i _ => pow_le_pow_left₀ hx hxy i

private theorem geom_identity (x : ℝ) (a : ℕ) : (x-1)*g x a = x^(a+1)-1 := by
  induction a with
  | zero => simp [g_zero]
  | succ a ih =>
    rw [g_succ, pow_succ]
    linear_combination x*ih

private noncomputable def ratio (p q : ℝ) (a : ℕ) : ℝ := p^a * g q a / (g p a)^2

private noncomputable def abund (p : ℝ) (a : ℕ) : ℝ := g p a / p^a

private theorem ratio_step {p q : ℝ} (hp : 2 ≤ p) (hq : p+1 ≤ q)
    {a : ℕ} (ha : 1 ≤ a) : ratio p q a < ratio p q (a+1) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hs := g_pos hp0.le a
  have ht := g_pos hq0.le a
  have hsa : 3 ≤ g p a := by
    cases a with
    | zero => omega
    | succ a =>
      rw [g_succ]
      have hh : g 0 a = 1 := by cases a <;> simp [g_zero, g_succ]
      have h1 : 1 ≤ g p a := hh ▸ g_mono le_rfl hp0.le a
      nlinarith [mul_nonneg hp0.le (sub_nonneg.mpr h1)]
  have hi : 1 / g p a ≤ (1/3 : ℝ) := by
    apply (div_le_div_iff₀ hs (by norm_num)).2
    simpa using hsa
  have hsq : (p + 1 / g p a)^2 < p*q := by
    have h₁ := pow_le_pow_left₀ (by positivity : 0 ≤ p + 1 / g p a)
      (add_le_add_right hi p) 2
    nlinarith [mul_nonneg hp0.le (sub_nonneg.mpr hq)]
  have hmul := mul_lt_mul_of_pos_right hsq (show 0 < (g p a)^2 by positivity)
  have heq : (p + 1 / g p a)^2 * (g p a)^2 = (p*g p a+1)^2 := by
    field_simp
  rw [heq] at hmul
  unfold ratio
  rw [g_succ p, g_succ q, pow_succ p a]
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
  have hm := mul_lt_mul_of_pos_left hmul (show 0 < p^a*g q a by positivity)
  have hpw : 0 < p^a := pow_pos hp0 a
  have hpos : 0 < p^a * p * (g p a)^2 := by positivity
  nlinarith [hm, hpos]

private theorem ratio_mono {p q : ℝ} (hp : 2 ≤ p) (hq : p+1 ≤ q)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) : ratio p q a ≤ ratio p q b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih => exact ih.trans (ratio_step hp hq (ha.trans hab)).le

private theorem ratio_ge_two {p q : ℝ} (hp : 2 ≤ p) (hq : p+1 ≤ q)
    {a : ℕ} (ha : 2 ≤ a) : ratio p q 2 ≤ ratio p q a :=
  ratio_mono hp hq (by omega) ha

private theorem odd_ratio {p q : ℝ} (hp : 3 ≤ p) (hq : p+2 ≤ q)
    {a : ℕ} (ha : 1 ≤ a) : 1 < ratio p q a := by
  have h₁ : 1 < ratio p q 1 := by
    unfold ratio
    rw [g_succ, g_succ, g_zero, g_zero]
    simp only [pow_one, mul_one]
    apply (lt_div_iff₀ (by positivity)).2
    nlinarith [mul_nonneg (show 0 ≤ p by linarith) (sub_nonneg.mpr hq)]
  exact h₁.trans_le (ratio_mono (by linarith) (by linarith) le_rfl ha)

private theorem next_spec (p : ℕ) : p < nextP p ∧ (nextP p).Prime := by
  simpa [nextP, Nat.succ_le_iff] using Nat.find_spec (Nat.exists_infinite_primes (p+1))

private theorem next_two : nextP 2 = 3 := by
  apply le_antisymm
  · exact Nat.find_min' _ (by decide)
  · exact (next_spec 2).1

private theorem next_three : nextP 3 = 5 := by
  apply le_antisymm
  · exact Nat.find_min' _ (by decide)
  · have ⟨h, hp⟩ := next_spec 3
    by_contra! hh
    have he : nextP 3 = 4 := by omega
    rw [he] at hp
    exact (by decide : ¬ Nat.Prime 4) hp

private theorem next_gap {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : p+2 ≤ nextP p := by
  obtain ⟨hlt,hq⟩ := next_spec p
  have hq2 : nextP p ≠ 2 := by have := hp.two_le; omega
  obtain ⟨u,hu⟩ := hp.odd_of_ne_two h2
  obtain ⟨v,hv⟩ := hq.odd_of_ne_two hq2
  omega

private theorem abund_le_ratio_sq {p q : ℝ} (hp : 5 ≤ p) (hq : p+2 ≤ q)
    {a : ℕ} (ha : 1 ≤ a) : abund p a ≤ (ratio p q a)^2 := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  by_cases h : a = 1
  · subst a
    have hbound : 1 + 1/(2*p) ≤ ratio p q 1 := by
      unfold ratio
      simp only [pow_one, g_succ, g_zero, mul_one]
      apply (le_div_iff₀ (by positivity)).2
      have hh : 0 ≤ p^2-4*p-1 := by nlinarith [sq_nonneg (p-5)]
      have hh' := mul_nonneg (show 0 ≤ p^2 by positivity) (sub_nonneg.mpr hq)
      field_simp
      nlinarith
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 1+1/(2*p)) hbound 2
    have hfin : abund p 1 ≤ (1+1/(2*p))^2 := by
      simp only [abund, pow_one, g_succ, g_zero, mul_one]
      field_simp
      nlinarith
    exact hfin.trans hsq
  · have ha2 : 2 ≤ a := by omega
    have hbound : 1+1/p ≤ ratio p q 2 := by
      have hgp := g_pos hp0.le 2
      have hp1' : 0 < p-1 := by linarith
      have hp5' : 0 ≤ p-5 := by linarith
      unfold ratio
      apply (le_div_iff₀ (by positivity)).2
      have h1 : (p-1)*g p 2 ≤ p^3 := by
        rw [geom_identity]
        norm_num
      have h2 : 0 ≤ (p-1)*g p 2 := by positivity
      have h1sq := pow_le_pow_left₀ h2 h1 2
      have hq2 := pow_le_pow_left₀ (show 0 ≤ p+2 by linarith) hq 2
      have hgg : q^2 ≤ g q 2 := by simp only [g_succ, g_zero]; nlinarith
      have hpoly : (p+1)*p^3 ≤ (p+2)^2*(p-1)^2 := by
        have h₁ : 0 ≤ (p-5)*p^2 := by positivity
        have h₂ : 0 ≤ (p-5)*p := by positivity
        nlinarith [h₁, h₂]
      have hp1 : 0 < (p-1)^2 := by positivity
      have hmul := mul_le_mul_of_nonneg_left h1sq (show 0 ≤ p+1 by positivity)
      have hmul₂ := mul_le_mul_of_nonneg_left (hq2.trans hgg) (show 0 ≤ p^3 by positivity)
      have hmul₃ := mul_le_mul_of_nonneg_right hmul₂ (sq_nonneg (p-1))
      have hmul₄ := mul_le_mul_of_nonneg_left hpoly (show 0 ≤ p^3 by positivity)
      field_simp
      apply (le_of_mul_le_mul_right _ hp1)
      nlinarith [hmul, hmul₃, hmul₄]
    have hr := hbound.trans (ratio_ge_two (by linarith) (by linarith) ha2)
    apply le_trans _ (pow_le_pow_left₀ (by positivity) hr 2)
    unfold abund
    apply (div_le_iff₀ (pow_pos hp0 _)).2
    have hg : (p-1)*g p a ≤ p^(a+1) := by rw [geom_identity]; linarith
    rw [pow_succ] at hg
    have hpow : 0 < p^a := pow_pos hp0 a
    have hnum : p ≤ (p-1)*(1+1/p)^2 := by
      field_simp
      nlinarith [sq_nonneg (p-5)]
    have hnum' := mul_le_mul_of_nonneg_right hnum hpow.le
    have hp1 : 0 < p-1 := by linarith
    apply (le_of_mul_le_mul_left _ hp1)
    nlinarith [hg,hnum']

private theorem normalized {n : ℕ} (hn : n ≠ 0) :
    (∏ p ∈ n.primeFactors, ratio p (nextP p) (n.factorization p)) =
      (n:ℝ) * (shiftedSigma n:ℝ) / (sigma n:ℝ)^2 ∧
    (∏ p ∈ n.primeFactors, abund p (n.factorization p)) = (sigma n:ℝ) / n := by
  have hp : (∏ p ∈ n.primeFactors, (p:ℝ)^(n.factorization p)) = n := by
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  have hs : (∏ p ∈ n.primeFactors, g p (n.factorization p)) = sigma n := by
    simp only [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn,
      mul_one, Nat.cast_prod, Nat.cast_sum, Nat.cast_pow, g]
  have ht : (∏ p ∈ n.primeFactors, g (nextP p) (n.factorization p)) = shiftedSigma n := by
    simp only [shiftedSigma, Nat.cast_prod, Nat.cast_sum, Nat.cast_pow, g]
  constructor
  · simp only [ratio, prod_div_distrib, prod_mul_distrib, hp, ht]
    rw [prod_pow, hs]
  · simp only [abund, prod_div_distrib, hp, hs]

private theorem term_le_product {F : Finset ℕ} {r : ℕ → ℝ}
    (h : ∀ j ∈ F, 1 ≤ r j) {p : ℕ} (hp : p ∈ F) : r p ≤ ∏ j ∈ F, r j := by
  rw [← prod_erase_mul _ _ hp]
  calc
    r p = 1 * r p := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (one_le_prod fun j hj => h j (mem_of_mem_erase hj)) (by linarith [h p hp])

private theorem member_abundancy {n : ℕ} (hn : 0 < n) (hm : member n) (h6 : n ≠ 6) :
    sigma n < 2*n := by
  classical
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hn0 : n ≠ 0 := hn.ne'
  let F := n.primeFactors
  let a (p : ℕ) := n.factorization p
  let r (p : ℕ) := ratio p (nextP p) (a p)
  let b (p : ℕ) := abund p (a p)
  have hprime (p : ℕ) (hp : p ∈ F) : p.Prime := Nat.prime_of_mem_primeFactors hp
  have ha (p : ℕ) (hp : p ∈ F) : 1 ≤ a p :=
    (hprime p hp).factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hp)
  have hr (p : ℕ) (hp : p ∈ F) (h2 : p ≠ 2) : 1 < r p := by
    apply odd_ratio
    · have := (hprime p hp).two_le
      exact_mod_cast (show 3 ≤ p by omega)
    · exact_mod_cast next_gap (hprime p hp) h2
    · exact ha p hp
  obtain ⟨hprod, hab⟩ := normalized hn0
  have hs : 0 < (sigma n:ℝ) := by
    have hp : 0 < sigma n := ArithmeticFunction.sigma_pos 1 n hn.ne'
    exact_mod_cast hp
  have hmR : (∏ p ∈ F, r p) ≤ 1 := by
    change (∏ p ∈ n.primeFactors, ratio p (nextP p) (n.factorization p)) ≤ 1
    rw [hprod]
    apply (div_le_iff₀ (by positivity)).2
    simp only [one_mul]
    exact_mod_cast hm
  obtain hF | hF := F.eq_empty_or_nonempty
  · have he := (Nat.prod_primeFactors_pow_factorization hn0).symm
    change (∏ p ∈ F, p^a p) = n at he
    rw [hF, prod_empty] at he
    subst n
    decide
  have h2 : 2 ∈ F := by
    by_contra hnot
    obtain ⟨p,hp⟩ := hF
    have hb : r p ≤ ∏ j ∈ F, r j :=
      term_le_product (fun j hj => (hr j hj (fun he => hnot (he ▸ hj))).le) hp
    exact (not_lt_of_ge (hb.trans hmR)) (hr p hp (fun he => hnot (he ▸ hp)))
  let G := F.erase 2
  have hrG (p : ℕ) (hp : p ∈ G) : 1 < r p := by
    obtain ⟨hne,hm⟩ := mem_erase.mp hp
    exact hr p hm hne
  have hG1 : 1 ≤ ∏ p ∈ G, r p := one_le_prod fun p hp => (hrG p hp).le
  have hr_split : r 2 * (∏ p ∈ G, r p) ≤ 1 := by
    rwa [mul_comm, prod_erase_mul _ _ h2]
  have ha2 : a 2 = 1 := by
    by_contra hne
    have hge : 2 ≤ a 2 := by have := ha 2 h2; omega
    have hh : (1:ℝ) < r 2 := by
      change 1 < ratio 2 (nextP 2) (a 2)
      rw [next_two]
      refine lt_of_lt_of_le ?_ (ratio_ge_two (by norm_num) (by norm_num) hge)
      norm_num [ratio, g_succ, g_zero]
    have := mul_le_mul_of_nonneg_left hG1 (show 0 ≤ r 2 by linarith)
    linarith
  have hr2 : r 2 = 8/9 := by norm_num [r, ha2, next_two, ratio, g_succ, g_zero]
  have hb2 : b 2 = 3/2 := by norm_num [b, ha2, abund, g_succ, g_zero]
  have hG : (∏ p ∈ G, r p) ≤ 9/8 := by rw [hr2] at hr_split; linarith
  have h3 : 3 ∉ G := by
    intro h3
    let H := G.erase 3
    have h3F : 3 ∈ F := mem_of_mem_erase h3
    have hH1 : 1 ≤ ∏ p ∈ H, r p :=
      one_le_prod fun p hp => (hrG p (mem_of_mem_erase hp)).le
    have hsplit : r 3 * (∏ p ∈ H, r p) ≤ 9/8 := by
      rwa [mul_comm, prod_erase_mul _ _ h3]
    have ha3 : a 3 = 1 := by
      by_contra hne
      have hge : 2 ≤ a 3 := by have := ha 3 h3F; omega
      have hh : (9/8:ℝ) < r 3 := by
        change 9/8 < ratio 3 (nextP 3) (a 3)
        rw [next_three]
        refine lt_of_lt_of_le ?_ (ratio_ge_two (by norm_num) (by norm_num) hge)
        norm_num [ratio, g_succ, g_zero]
      have := mul_le_mul_of_nonneg_left hH1 (show 0 ≤ r 3 by linarith)
      linarith
    have hr3 : r 3 = 9/8 := by norm_num [r, ha3, next_three, ratio, g_succ, g_zero]
    have hH : H = ∅ := by
      by_contra hne
      obtain ⟨p,hp⟩ := nonempty_iff_ne_empty.mpr hne
      have hh := term_le_product (fun j hj => (hrG j (mem_of_mem_erase hj)).le) hp
      have hp' := hrG p (mem_of_mem_erase hp)
      rw [hr3] at hsplit
      linarith
    have hfactor := (Nat.prod_primeFactors_pow_factorization hn0).symm
    change (∏ p ∈ F, p^a p) = n at hfactor
    rw [← prod_erase_mul _ _ h2, ← prod_erase_mul _ _ h3] at hfactor
    change (∏ p ∈ H, p^a p) * 3^a 3 * 2^a 2 = n at hfactor
    simp [hH, ha2, ha3] at hfactor
    exact h6 hfactor.symm
  have hcomp : (∏ p ∈ G, b p) ≤ (∏ p ∈ G, r p)^2 := by
    rw [(prod_pow _ _ _).symm]
    apply prod_le_prod
    · intro p _
      unfold b abund
      exact div_nonneg (sum_nonneg fun i _ => by positivity) (by positivity)
    · intro p hp
      obtain ⟨hp2,hpF⟩ := mem_erase.mp hp
      have hp3 : p ≠ 3 := fun he => h3 (he ▸ hp)
      have hp4 : p ≠ 4 := by
        intro he
        exact (by decide : ¬ Nat.Prime 4) (he ▸ hprime p hpF)
      have hp5 : 5 ≤ p := by have := (hprime p hpF).two_le; omega
      exact abund_le_ratio_sq (by exact_mod_cast hp5)
        (by exact_mod_cast next_gap (hprime p hpF) hp2) (ha p hpF)
  have hcomp' := hcomp.trans (pow_le_pow_left₀ (show 0 ≤ ∏ p ∈ G, r p by linarith) hG 2)
  have hsplit : b 2 * (∏ p ∈ G, b p) = (sigma n:ℝ)/n := by
    rw [mul_comm, prod_erase_mul _ _ h2]
    exact hab
  have hfinal : (sigma n:ℝ)/n < 2 := by rw [← hsplit, hb2]; linarith
  have hfinal' := (div_lt_iff₀ hnR).1 hfinal
  exact_mod_cast hfinal'

private theorem sigma_six : sigma 6 = 12 := by decide +kernel

private theorem member_six : member 6 := by
  have hpf : Nat.primeFactors 6 = {2,3} := by decide +kernel
  have h2 : (6:ℕ).factorization 2 = 1 := by decide +kernel
  have h3 : (6:ℕ).factorization 3 = 1 := by decide +kernel
  norm_num [member, sigma_six, shiftedSigma, hpf, h2, h3, next_two, next_three, sum_range_succ]

theorem OMA.solution : type_of% @OMA.S_oeis_a387724.main := by
  refine ⟨member_six, ?_, ?_⟩
  · intro n hn hm
    constructor
    · intro h
      by_contra hne
      exact (not_lt_of_ge h) (member_abundancy hn hm hne)
    · rintro rfl
      norm_num [sigma_six]
  · intro n hn hm hne
    have h := member_abundancy hn hm hne
    have hs : 0 < sigma n := ArithmeticFunction.sigma_pos 1 n hn.ne'
    apply Nat.lt_of_mul_lt_mul_left (a := n)
    exact lt_of_le_of_lt hm (by
      rw [pow_two, ← mul_assoc, mul_comm n 2]
      exact Nat.mul_lt_mul_of_pos_right h hs)