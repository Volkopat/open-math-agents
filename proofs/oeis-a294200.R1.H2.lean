import OMAReductions.R_oeis_a294200_R1

/-!
Divisor chains for x^m-1 transfer the factor-list condition of B₀ to the
practicality of 2(2^m-1). The Stewart–Sierpiński practical-number component
lemmas follow our earlier proof for the Coleman and practical-complements
problems. The divisor chains and the transfer are specific to this result.
Credit: @krgrocon
-/

namespace PracticalComplements

/-- The subset-sum definition of Nat.IsPractical, written with Mathlib Finsets. -/
def practical (n : ℕ) : Prop :=
  ∀ m, m ≤ n → ∃ s : Finset ℕ, s ⊆ n.divisors ∧ m = ∑ i ∈ s, i


open ArithmeticFunction
open scoped ArithmeticFunction.sigma

def subsetSums (A : Set ℕ) : Set ℕ :=
  {m | ∃ s : Finset ℕ, (s : Set ℕ) ⊆ A ∧ m = ∑ i ∈ s, i}

def positivePractical (n : ℕ) : Prop := 0 < n ∧ practical n

theorem practical_one : practical 1 := by
  intro m hm
  interval_cases m
  · exact ⟨∅, by simp, by simp⟩
  · exact ⟨{1}, by simp, by simp⟩


lemma covered_digit_split {m a b p : ℕ} (hp : 0 < p) (hg : p ≤ a + 1)
    (hm : m ≤ a + p * b) : ∃ x ≤ a, ∃ y ≤ b, m = x + p * y := by
  by_cases h : m / p ≤ b
  · have hr := Nat.mod_lt m hp
    have he := Nat.div_add_mod m p
    exact ⟨m % p, by omega, m / p, h, by omega⟩
  · have hle := Nat.mul_le_mul_left p (show b ≤ m / p by omega)
    have he := Nat.mul_div_le m p
    exact ⟨m - p * b, by omega, b, le_rfl, by omega⟩

lemma covered_union_image (A B : Finset ℕ) {p : ℕ} (hp : 0 < p)
    (hd : Disjoint A (B.image (p * ·))) (hg : p ≤ (∑ a ∈ A, a) + 1)
    (hA : ∀ x, x ≤ ∑ a ∈ A, a → x ∈ subsetSums (A : Set ℕ))
    (hB : ∀ x, x ≤ ∑ b ∈ B, b → x ∈ subsetSums (B : Set ℕ)) :
    ∀ m, m ≤ ∑ d ∈ A ∪ (B.image (p * ·)), d →
      m ∈ subsetSums ((A ∪ (B.image (p * ·)) : Finset ℕ) : Set ℕ) := by
  have hsum (s : Finset ℕ) : (∑ d ∈ s.image (p * ·), d) = p * ∑ i ∈ s, i := by
    rw [Finset.sum_image, Finset.mul_sum]
    intro u hu v hv he
    exact Nat.mul_left_cancel hp he
  intro m hm
  rw [Finset.sum_union hd, hsum] at hm
  obtain ⟨x, hx, y, hy, he⟩ := covered_digit_split hp hg hm
  obtain ⟨s, hs, es⟩ := hA x hx
  obtain ⟨t, ht, et⟩ := hB y hy
  have hs' : s ⊆ A := hs
  have ht' : t.image (p * ·) ⊆ B.image (p * ·) := Finset.image_subset_image ht
  refine ⟨s ∪ t.image (p * ·), ?_, ?_⟩
  · exact Finset.union_subset_union hs' ht'
  · rw [Finset.sum_union (hd.mono hs' ht'), hsum, ← es, ← et]
    exact he

lemma practical_prime_layer {c p : ℕ} (hc : 0 < c) (hp : p.Prime) (e : ℕ) :
    (c * p ^ (e + 1)).divisors =
      c.divisors ∪ ((c * p ^ e).divisors.image (p * ·)) := by
  have hn : c * p ^ (e + 1) ≠ 0 := Nat.mul_ne_zero hc.ne' (pow_ne_zero _ hp.ne_zero)
  have hn' : c * p ^ e ≠ 0 := Nat.mul_ne_zero hc.ne' (pow_ne_zero _ hp.ne_zero)
  have he : c * p ^ (e + 1) = p * (c * p ^ e) := by rw [pow_succ]; ac_rfl
  ext d
  simp only [Finset.mem_union, Nat.mem_divisors, hn, hn', hc.ne', ne_eq,
    not_false_eq_true, and_true, Finset.mem_image]
  constructor
  · intro h
    by_cases hpd : p ∣ d
    · obtain ⟨u, rfl⟩ := hpd
      rw [he] at h
      exact Or.inr ⟨u, Nat.dvd_of_mul_dvd_mul_left hp.pos h, rfl⟩
    · exact Or.inl (((hp.coprime_iff_not_dvd.mpr hpd).symm.pow_right _).dvd_of_dvd_mul_right h)
  · rintro (h | ⟨u, hu, rfl⟩)
    · exact dvd_mul_of_dvd_left h _
    · rw [he]
      exact Nat.mul_dvd_mul_left p hu

lemma cover_mul_prime_pow {c p : ℕ} (hc : 0 < c) (hp : p.Prime) (hcp : c.Coprime p)
    (hgap : p ≤ (∑ d ∈ c.divisors, d) + 1)
    (hcover : ∀ m, m ≤ ∑ d ∈ c.divisors, d → m ∈ subsetSums (c.divisors : Set ℕ))
    (e : ℕ) : ∀ m, m ≤ ∑ d ∈ (c * p ^ e).divisors, d →
      m ∈ subsetSums ((c * p ^ e).divisors : Set ℕ) := by
  induction e with
  | zero => simpa using hcover
  | succ e ih =>
    rw [practical_prime_layer hc hp e]
    apply covered_union_image _ _ hp.pos _ hgap hcover ih
    apply Finset.disjoint_left.mpr
    intro d hd hdp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hdp
    exact (hp.coprime_iff_not_dvd.mp hcp.symm)
      ((dvd_mul_right p t).trans (Nat.mem_divisors.mp hd).1)

theorem whole_le_sigma {c : ℕ} (hc : 0 < c) : c ≤ σ 1 c := by
  rw [ArithmeticFunction.sigma_one_apply]
  exact Finset.single_le_sum (f := fun i : ℕ => i) (fun _ _ => Nat.zero_le _) (Nat.mem_divisors.mpr ⟨dvd_rfl, hc.ne'⟩)

theorem coprime_to_tail {c b t : ℕ} (ht : 0 < t) (hbound : t ≤ σ 1 c + 1)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ b → σ 1 c + 1 < p) : t.Coprime b := by
  by_contra h
  obtain ⟨p, hp, hpt, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact (not_lt_of_ge ((Nat.le_of_dvd ht hpt).trans hbound)) (hrough p hp hpb)

theorem practical_divisor_dvd_prefix {c b d : ℕ} (hc : 0 < c)
    (hd : positivePractical d) (hdiv : d ∣ c * b)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ b → σ 1 c + 1 < p) : d ∣ c := by
  have small (t : ℕ) (ht : 0 < t) (hsize : t ≤ σ 1 c + 1) (htd : t ∣ d) : t ∣ c :=
    (coprime_to_tail ht hsize hrough).dvd_of_dvd_mul_right (htd.trans hdiv)
  by_contra h
  have hsize : σ 1 c + 1 ≤ d := by
    by_contra! hdsmall
    exact h (small d hd.1 (by omega) dvd_rfl)
  obtain ⟨S, hS, hsum⟩ := hd.2 _ hsize
  have hsub : S ⊆ c.divisors := by
    intro x hx
    have hxdiv := Nat.mem_divisors.mp (hS hx)
    have hxle : x ≤ ∑ i ∈ S, i := Finset.single_le_sum (f := fun i : ℕ => i) (fun _ _ => Nat.zero_le _) hx
    exact Nat.mem_divisors.mpr ⟨small x (Nat.pos_of_dvd_of_pos hxdiv.1 hd.1) (hsum ▸ hxle) hxdiv.1, hc.ne'⟩
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun i : ℕ => i) (by intros; omega)
  rw [← ArithmeticFunction.sigma_one_apply] at hle
  omega

theorem component_from_cover
    {n : ℕ} (hn : 0 < n) (hnot : ¬ positivePractical n)
    (b c : ℕ) (hcb : n = c * b) (hcop : c.Coprime b)
    (hcover : ∀ m, m ≤ ∑ d ∈ c.divisors, d → m ∈ subsetSums (c.divisors : Set ℕ)) :
    ∃ u v : ℕ, n = u * v ∧ 1 < v ∧ u.Coprime v ∧
      ∀ p : ℕ, p.Prime → p ∣ v → σ 1 u + 1 < p := by
  induction b using Nat.strong_induction_on generalizing c with
  | h b ih =>
    have hc : 0 < c := by by_contra! hz; simp_all
    have hb : 0 < b := by by_contra! hz; simp_all
    have hb1 : b ≠ 1 := by
      rintro rfl
      simp only [mul_one] at hcb
      subst n
      apply hnot
      refine ⟨hc, fun m hm => hcover m (hm.trans ?_)⟩
      simpa only [ArithmeticFunction.sigma_one_apply] using whole_le_sigma hc
    by_cases hr : ∀ p : ℕ, p.Prime → p ∣ b → σ 1 c + 1 < p
    · exact ⟨c, b, hcb, by omega, hcop, hr⟩
    push Not at hr
    obtain ⟨p, hp, hpb, hl⟩ := hr
    obtain ⟨e, t, hpt, hbt⟩ := Nat.exists_eq_pow_mul_and_not_dvd hb.ne' p hp.ne_one
    have he : e ≠ 0 := by rintro rfl; simp_all
    have ht : 0 < t := by by_contra! hz; simp_all
    have hpow : 1 < p ^ e := one_lt_pow₀ hp.one_lt he
    have htb : t < b := by rw [hbt]; simpa using Nat.mul_lt_mul_of_pos_right hpow ht
    have htt : t ∣ b := by rw [hbt]; exact dvd_mul_left _ _
    have hcp := Nat.Coprime.coprime_dvd_right hpb hcop
    have hct := Nat.Coprime.coprime_dvd_right htt hcop
    have hptcop := hp.coprime_iff_not_dvd.mpr hpt
    apply ih t htb (c * p ^ e)
    · rw [hcb, hbt, Nat.mul_assoc]
    · exact hct.mul_left (hptcop.pow_left e)
    · exact cover_mul_prime_pow hc hp hcp (by simpa only [ArithmeticFunction.sigma_one_apply] using hl) hcover e

theorem has_practical_component {n : ℕ} (hn : 0 < n) (hnot : ¬ positivePractical n) :
    ∃ u v : ℕ, n = u * v ∧ 1 < v ∧ u.Coprime v ∧
      ∀ p : ℕ, p.Prime → p ∣ v → σ 1 u + 1 < p := by
  apply component_from_cover hn hnot n 1 (by simp) (by simp)
  intro m hm
  apply practical_one m
  simpa using hm

end PracticalComplements

namespace ShiftedMersenne

/-- The class denoted B₀ by Guo and Weingartner. Its generators are obtained
from their ordered-prime-factor characterization and their Lemma 3. -/
inductive Built : ℕ → Prop
  | one : Built 1
  | two : Built 2
  | mul {m q : ℕ} : Built m → 0 < q → q ≤ m → Built (m*q)

/-- Successive divisors can be enlarged by a multiplier at most twice the
current divisor plus one. The factor of two is the practical-number starter. -/
inductive Chain (a : ℕ) : ℕ → Prop
  | refl : Chain a a
  | step {d q : ℕ} : Chain a d → 0 < q → q ≤ 2*d+1 → Chain a (d*q)

theorem Chain.trans {a b c : ℕ} (hab : Chain a b) (hbc : Chain b c) : Chain a c := by
  induction hbc with
  | refl => exact hab
  | step h hq hle ih => exact ih.step hq hle

theorem Chain.pos {a b : ℕ} (h : Chain a b) (ha : 0 < a) : 0 < b := by
  induction h with
  | refl => exact ha
  | step _ hq _ ih => exact Nat.mul_pos ih hq

private theorem step_between {d w q : ℕ} (hd : 0 < d) (hw : 0 < w)
    (hdw : d ∣ w) (hwq : w ∣ d*q) (hq : 0 < q) (hle : q ≤ 2*d+1) : Chain d w := by
  obtain ⟨c,rfl⟩ := hdw
  have hc : 0<c := Nat.pos_of_mul_pos_left hw
  have hbound := Nat.le_of_dvd (Nat.mul_pos hd hq) hwq
  exact Chain.refl.step hc ((Nat.le_of_mul_le_mul_left hbound hd).trans hle)

/-- Taking least common multiples with a fixed positive number preserves a chain. -/
theorem Chain.lift {a b : ℕ} (h : Chain a b) (ha : 0 < a) (u : ℕ) (hu : 0 < u) :
    Chain (Nat.lcm u a) (Nat.lcm u b) := by
  induction h with
  | refl => exact .refl
  | @step d q hist hq hle ih =>
    have hd : 0 < d := hist.pos ha
    have hL := Nat.lcm_pos hu hd
    have hdL : d ∣ Nat.lcm u d := Nat.dvd_lcm_right _ _
    have hforward : Nat.lcm u d ∣ Nat.lcm u (d*q) :=
      Nat.lcm_dvd (Nat.dvd_lcm_left _ _) ((dvd_mul_right d q).trans (Nat.dvd_lcm_right _ _))
    have hback : Nat.lcm u (d*q) ∣ (Nat.lcm u d)*q :=
      Nat.lcm_dvd ((Nat.dvd_lcm_left u d).trans (dvd_mul_right _ q))
        (Nat.mul_dvd_mul_right hdL q)
    exact ih.trans (step_between hL (Nat.lcm_pos hu (Nat.mul_pos hd hq)) hforward hback hq
      (by have := Nat.le_of_dvd hL hdL; omega))

private theorem power_sub_pos {x m : ℕ} (hx : 2 ≤ x) (hm : 0 < m) : 0 < x^m-1 := by
  have h := Nat.one_lt_pow (by omega : m ≠ 0) (by omega : x > 1)
  omega

theorem Built.pos {m : ℕ} (hm : Built m) : 0 < m := by
  induction hm with
  | one => decide
  | two => decide
  | mul _ hq _ ih => exact Nat.mul_pos ih hq

/-- Reading the increasing prime factorization, including repeated primes,
implements the arithmetic definition used in the shifted-prime theorem.
The construction in fact works for any ordering satisfying this bound. -/
theorem built_of_factors (l : List ℕ) (h : ∀ i : Fin l.length,
    l[i].Prime ∧ l[i] ≤ max 2 (l.take i.val).prod) : Built l.prod := by
  have go (j : ℕ) (hj : j ≤ l.length) : Built (l.take j).prod := by
    induction j with
    | zero => simpa using Built.one
    | succ j ih =>
      have hj' : j < l.length := by omega
      have hprior := ih (Nat.le_of_lt hj')
      obtain ⟨hq, hle⟩ := h ⟨j,hj'⟩
      rw [List.take_succ_eq_append_getElem hj', List.prod_append]
      simp only [List.prod_cons, List.prod_nil, mul_one]
      change (l[j]).Prime at hq
      change l[j] ≤ max 2 (l.take j).prod at hle
      by_cases hsmall : (l.take j).prod < 2
      · have hp := hprior.pos
        have ho : (l.take j).prod=1 := by omega
        have ht : l[j]=2 := by have := hq.two_le; omega
        simpa only [ho,ht,one_mul] using Built.two
      · exact hprior.mul hq.pos (by omega)
  simpa using go l.length le_rfl

/-- Uniformity in x allows the second copy of a chain to run at x^q. -/
theorem Built.power_chain {m : ℕ} (hm : Built m) (x : ℕ) (hx : 2 ≤ x) :
    Chain (x-1) (x^m-1) := by
  induction hm generalizing x with
  | one => simpa using (Chain.refl (a:=x-1))
  | two =>
    have hprod : (x-1)*(x+1)=x^2-1 := by
      have hsub := Nat.sub_add_cancel (show 1 ≤ x by omega)
      have he : (x-1)*(x+1)+1=x^2 := by nlinarith [hsub]
      omega
    rw [← hprod]
    exact Chain.refl.step (by omega) (by omega)
  | @mul m q hm hq hqm ih =>
    let u := x^m-1
    let v := x^q-1
    have hu : 0 < u := power_sub_pos hx hm.pos
    have hv : 0 < v := power_sub_pos hx hq
    have hvu : v ≤ u := Nat.sub_le_sub_right (Nat.pow_le_pow_right (by omega) hqm) _
    have hab : Chain (x-1) u := ih x hx
    have hbc : Chain u (Nat.lcm u v) := step_between hu (Nat.lcm_pos hu hv)
      (Nat.dvd_lcm_left _ _) (Nat.lcm_dvd_mul _ _) hv (by omega)
    have hcd := (ih (x^q) (by dsimp [v] at hv; omega)).lift hv u hu
    have hend : u ∣ (x^q)^m-1 := by
      rw [← pow_mul]
      exact Nat.pow_sub_one_dvd_pow_sub_one x (dvd_mul_left m q)
    rw [Nat.lcm_eq_right_iff_dvd.mpr hend, ← pow_mul, Nat.mul_comm q m] at hcd
    exact (hab.trans hbc).trans hcd

open PracticalComplements ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- The endpoint +1 is attained at the first step from 2 to 6. This extends
the small-multiplier lemma used in our proof concerning practical complements. -/
theorem practical_mul_next {m j : ℕ} (hm : practical m) (hm0 : 0 < m)
    (hj : 0 < j) (hjbound : j ≤ m+1) : practical (m*j) := by
  by_contra h
  obtain ⟨c,b,hcb,hbig,hcop,hrough⟩ := has_practical_component (Nat.mul_pos hm0 hj) (fun hh => h hh.2)
  have hc : 0 < c := by by_contra! hz; simp_all
  have hmc : m ∣ c := practical_divisor_dvd_prefix hc ⟨hm0,hm⟩
    (hcb ▸ dvd_mul_right m j) hrough
  have hjs : j ≤ σ 1 c+1 := by
    have := Nat.le_of_dvd hc hmc
    have := whole_le_sigma hc
    omega
  have hcop' : (m*j).Coprime b :=
    (Nat.Coprime.coprime_dvd_left hmc hcop).mul_left (coprime_to_tail hj hjs hrough)
  have hd : b ∣ m*j := hcb.symm ▸ dvd_mul_left b c
  have e := hcop'.gcd_eq_one
  rw [Nat.gcd_eq_right hd] at e
  omega

theorem Chain.practical {a b : ℕ} (h : Chain a b) (ha : 0 < a) (hp : practical (2*a)) :
    0 < b ∧ practical (2*b) := by
  induction h with
  | refl => exact ⟨ha,hp⟩
  | step _ hq hbound ih =>
    exact ⟨Nat.mul_pos ih.1 hq, by
      rw [← Nat.mul_assoc]
      exact practical_mul_next ih.2 (by have := ih.1; omega) hq hbound⟩

theorem practical_double_mersenne {m : ℕ} (hm : Built m) :
    practical (2*(2^m-1)) := by
  have h2 : practical 2 := by simpa using
    (practical_mul_next (m:=1) (j:=2) practical_one (by decide) (by decide) (by decide))
  exact ((hm.power_chain 2 (by decide)).practical (by decide) (by simpa using h2)).2


end ShiftedMersenne

theorem OMA.solution : OMA.R_oeis_a294200_R1.H2 := by
  intro l hl
  have hb := ShiftedMersenne.built_of_factors l hl
  have he := ShiftedMersenne.practical_double_mersenne hb
  refine ⟨?_, ?_⟩
  · have h := Nat.one_lt_pow (Nat.ne_of_gt hb.pos) (by decide : 1<2)
    omega
  · intro k hk
    obtain ⟨s,hs,heq⟩ := he k (by omega)
    exact ⟨s,hs,heq.symm⟩
