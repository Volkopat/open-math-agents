import OMAStatements.S_oeis_a294307

/-! A constructive proof of Zhi-Wei Sun's OEIS A294307. -/

namespace PracticalComplements

/-- The subset-sum definition of Nat.IsPractical, written with Mathlib Finsets. -/
def practical (n : ℕ) : Prop :=
  ∀ m, m ≤ n → ∃ s : Finset ℕ, s ⊆ n.divisors ∧ m = ∑ i ∈ s, i

end PracticalComplements

/-! Subset sums and the practical component, adapted from the proof in
the contributor's reduction of Coleman's A017666 (open-math-agents PR 5541).
The prime-power argument is the Stewart–Sierpiński characterization. -/

namespace PracticalComplements
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

namespace PracticalTriples

open PracticalComplements ArithmeticFunction
open scoped ArithmeticFunction.sigma

theorem twice_le_sigma_succ {m : ℕ} (hm : practical m) (hm0 : 0 < m) :
    2*m ≤ σ 1 m+1 := by
  obtain ⟨s, hs, he⟩ := hm (m-1) (by omega)
  have hi : m ∉ s := by
    intro h
    have := Finset.single_le_sum (f := fun i : ℕ => i) (fun i _ => Nat.zero_le i) h
    omega
  have hsub : insert m s ⊆ m.divisors :=
    Finset.insert_subset (Nat.mem_divisors.mpr ⟨dvd_rfl,hm0.ne'⟩) hs
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun i : ℕ => i) (by intros; omega)
  rw [Finset.sum_insert hi, ← ArithmeticFunction.sigma_one_apply] at hle
  omega

theorem mul_double {m j : ℕ} (hm : practical m) (hm0 : 0 < m) (hj : 0 < j)
    (h : j ≤ 2*m) : practical (m*j) := by
  by_contra hnot
  obtain ⟨c,b,hcb,hbig,hcop,hrough⟩ :=
    has_practical_component (Nat.mul_pos hm0 hj) (fun hh => hnot hh.2)
  have hc : 0 < c := by by_contra! hz; simp_all
  have hmc : m ∣ c := practical_divisor_dvd_prefix hc ⟨hm0,hm⟩
    (hcb ▸ dvd_mul_right m j) hrough
  have hjs : j ≤ σ 1 c+1 := by
    obtain ⟨k,hk⟩ := hmc
    by_cases he : k=1
    · have e : c=m := by simpa [he] using hk
      exact e ▸ h.trans (twice_le_sigma_succ hm hm0)
    · have hge : 2≤k := by
        by_cases hz : k=0
        · simp_all
        · omega
      have hmul := Nat.mul_le_mul_left m hge
      have := whole_le_sigma hc
      omega
  have hcop' : (m*j).Coprime b :=
    (Nat.Coprime.coprime_dvd_left hmc hcop).mul_left (coprime_to_tail hj hjs hrough)
  have hd : b ∣ m*j := hcb.symm ▸ dvd_mul_left b c
  have e := hcop'.gcd_eq_one
  rw [Nat.gcd_eq_right hd] at e
  omega

end PracticalTriples

namespace PracticalPowerTowers

open PracticalComplements PracticalTriples

def T (a : ℕ) : ℕ := 3^(2^a)

private theorem grow (a : ℕ) : T (a+1) = (T a)^2 := by
  simp only [T, pow_succ 2 a, pow_mul]

private theorem tall (a : ℕ) : 3 ≤ T a := by
  unfold T
  have h : 0 < 2^a := by positivity
  simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 3) h

private theorem diff_square {x : ℕ} (hx : 0 < x) : x^2-1 = (x-1)*(x+1) := by
  obtain ⟨y,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hx.ne'
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  apply Nat.sub_eq_of_eq_add
  ring

private theorem square_step {x : ℕ} (hx : 3 ≤ x) (h : practical (x-1)) : practical (x^2-1) := by
  rw [diff_square (by omega)]
  exact mul_double h (by omega) (by omega) (by omega)

private theorem base_practical (a : ℕ) : practical (T a-1) := by
  induction a with
  | zero => exact mul_double (m:=1) (j:=2) practical_one (by decide) (by decide) (by decide)
  | succ a ih => rw [grow]; exact square_step (tall a) ih

private def S (x : ℕ) : ℕ → ℕ
  | 0 => 0
  | h+1 => x*S x h + 1

private theorem positive_sum {x h : ℕ} (hh : 0 < h) : 0 < S x h := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hh.ne'
  simp [S]

private theorem sum_equation {x : ℕ} (hx : 0 < x) (h : ℕ) : (x-1)*S x h = x^h-1 := by
  have aux : (x-1)*S x h + 1 = x^h := by
    induction h with
    | zero => simp [S]
    | succ h ih =>
      simp only [S,pow_succ,←ih]
      have hx' : x-1+1=x := by omega
      calc
        (x-1)*(x*S x h+1)+1 = ((x-1)*S x h)*x + (x-1+1) := by ring
        _ = ((x-1)*S x h+1)*x := by rw [hx']; ring
  omega

private theorem odd_factors {h x : ℕ} (ho : Odd h) (hx : 3 ≤ x) :
    ∃ q : ℕ, 0 < q ∧ q ≤ S x h ∧ S (x^2) h = S x h * q := by
  have hh : 0 < h := by obtain ⟨t,ht⟩ := ho; omega
  have hd : x+1 ∣ x^h+1 := by simpa only [one_pow] using ho.nat_add_dvd_pow_add_pow x 1
  obtain ⟨q,hq⟩ := hd
  have hpos : 0 < x^h := by positivity
  have hz : 0 < q := by by_contra! h; simp_all
  have hs := sum_equation (x:=x) (by omega) h
  have hS := positive_sum (x:=x) hh
  have hdiff : x-1+1=x := by omega
  have hbound : q ≤ S x h := by
    apply Nat.le_of_mul_le_mul_left (c:=x+1) _ (by omega)
    calc
      (x+1)*q = (x-1)*S x h+2 := by omega
      _ ≤ (x-1)*S x h + 2*S x h := by omega
      _ = (x+1)*S x h := by rw [←Nat.add_mul]; congr 1; omega
  refine ⟨q,hz,hbound,?_⟩
  have hx2 : 1 < x^2 := by nlinarith
  apply Nat.mul_left_cancel (n:=x^2-1) (by omega)
  calc
    (x^2-1)*S (x^2) h = (x^2)^h-1 := sum_equation (by omega) h
    _ = (x^h)^2-1 := by rw [←pow_mul,←pow_mul,Nat.mul_comm 2 h]
    _ = (x^h-1)*(x^h+1) := diff_square hpos
    _ = (x^2-1)*(S x h*q) := by rw [←hs,hq,diff_square (by omega : 0<x)]; ring

private theorem append_sums {B h : ℕ} (hB : practical B) (hB0 : 0 < B)
    (ho : Odd h) (hsmall : S 3 h ≤ 2*B) (i : ℕ) : practical (B*S (T i) h) := by
  have hh : 0 < h := by obtain ⟨t,ht⟩ := ho; omega
  induction i with
  | zero => exact mul_double hB hB0 (positive_sum hh) hsmall
  | succ i ih =>
    obtain ⟨q,hq0,hq,hfactor⟩ := odd_factors ho (tall i)
    rw [grow,hfactor,←Nat.mul_assoc]
    have hs := positive_sum (x:=T i) hh
    have hle : S (T i) h ≤ B*S (T i) h := Nat.le_mul_of_pos_left _ hB0
    exact mul_double ih (Nat.mul_pos hB0 hs) hq0 (by omega)

/-- For a single a, every exponent from 1 through 2^a works simultaneously. -/
theorem family (a k : ℕ) (hk : 0 < k) (hka : k ≤ 2^a) : practical ((T a)^k-1) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases Nat.even_or_odd k with he|ho
    · obtain ⟨t,ht⟩ := he
      have ht0 : 0<t := by omega
      have heq : k=t*2 := by omega
      rw [heq,pow_mul]
      have hbase : 3≤(T a)^t := (tall a).trans (by
        simpa only [pow_one] using Nat.pow_le_pow_right (by have := tall a; omega : 0<T a) ht0)
      exact square_step hbase (ih t (by omega) ht0 (by omega))
    · have hs := sum_equation (x:=3) (by decide) k
      have hv : 3^k ≤ T a := Nat.pow_le_pow_right (by decide) hka
      have hB := tall a
      have hsmall : S 3 k ≤ 2*(T a-1) := by omega
      rw [←sum_equation (x:=T a) (by omega) k]
      exact append_sums (base_practical a) (by omega) ho hsmall a

theorem infinitely_many (n : ℕ) :
    {m : ℕ | 0 < m ∧ ∀ k : ℕ, 1≤k → k≤n → 0 < m^k-1 ∧ practical (m^k-1)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro cutoff
  let a := n+cutoff+1
  have ha : n ≤ a ∧ cutoff ≤ a := by dsimp [a]; omega
  have h2 : a < 2^a := Nat.lt_pow_self (by decide)
  have h3 : 2^a < T a := Nat.lt_pow_self (by decide : 1<3)
  refine ⟨T a,⟨by have := tall a; omega,?_⟩,by omega⟩
  intro k hk hkn
  have hl := Nat.pow_le_pow_right (n:=T a) (by have := tall a; omega) hk
  simp only [pow_one] at hl
  exact ⟨by have := tall a; omega, family a k hk (by omega)⟩

end PracticalPowerTowers

theorem OMA.solution : type_of% @OMA.S_oeis_a294307.main := by
  intro n _
  apply (PracticalPowerTowers.infinitely_many n).mono
  intro m hm
  refine ⟨hm.1,?_⟩
  intro k hk hn
  obtain ⟨hpos,hpr⟩ := hm.2 k hk hn
  refine ⟨hpos,?_⟩
  intro j hj
  obtain ⟨s,hs,he⟩ := hpr j hj.le
  exact ⟨s,hs,he.symm⟩
