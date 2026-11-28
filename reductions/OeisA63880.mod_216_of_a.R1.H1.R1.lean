import OMAReductions.R_OeisA63880_mod_216_of_a_R1

-- Reduction OeisA63880.mod_216_of_a.R1.H1.R1 of step OeisA63880.mod_216_of_a.R1.H1
-- Credit: @PanPapag

namespace OMA.R_OeisA63880_mod_216_of_a_R1_H1_R1

open OeisA63880
open scoped ArithmeticFunction.sigma

-- Unitary divisor decomposition adapted from desenyon, reduction 1353.
private theorem splitUnitary {m q : ℕ} (hm : 0 < m) (hq : IsPrimePow q)
    (hc : q.Coprime m) :
    unitaryDivisors (m*q) = unitaryDivisors m ∪ (unitaryDivisors m).image (· * q) := by
  have hq0 := hq.pos
  ext d
  simp only [unitaryDivisors, Finset.mem_filter, Nat.mem_divisors, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro ⟨⟨hd, -⟩, hcd⟩
    obtain ⟨t, ht⟩ := hd
    have hd0 : 0 < d := Nat.pos_of_mul_pos_right (ht ▸ Nat.mul_pos hm hq0)
    rw [ht, Nat.mul_div_cancel_left _ hd0] at hcd
    have hqt : q ∣ d*t := ht ▸ dvd_mul_left q m
    rcases (hcd.isPrimePow_dvd_mul hq).1 hqt with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · have he : m = b*t := Nat.eq_of_mul_eq_mul_right hq0 (by linear_combination ht)
      subst m
      have hb : 0 < b := Nat.pos_of_mul_pos_left hd0
      exact Or.inr ⟨b, ⟨⟨dvd_mul_right _ _, hm.ne'⟩, by
        simpa [Nat.mul_div_cancel_left _ hb] using (Nat.coprime_mul_iff_left.1 hcd).2⟩, mul_comm ..⟩
    · have he : m = d*b := Nat.eq_of_mul_eq_mul_right hq0 (by linear_combination ht)
      subst m
      exact Or.inl ⟨⟨dvd_mul_right _ _, hm.ne'⟩, by
        simpa [Nat.mul_div_cancel_left _ hd0] using (Nat.coprime_mul_iff_right.1 hcd).2⟩
  · rintro (⟨⟨⟨t, rfl⟩, -⟩, hcd⟩ | ⟨b, ⟨⟨⟨t, rfl⟩, -⟩, hcd⟩, rfl⟩)
    · have hd := Nat.pos_of_mul_pos_right hm
      rw [Nat.mul_div_cancel_left _ hd] at hcd
      refine ⟨⟨dvd_mul_of_dvd_left (dvd_mul_right d t) q, (Nat.mul_pos hm hq0).ne'⟩, ?_⟩
      rw [mul_assoc, Nat.mul_div_cancel_left _ hd]
      exact hcd.mul_right (Nat.coprime_mul_iff_right.1 hc).1.symm
    · have hb := Nat.pos_of_mul_pos_right hm
      rw [Nat.mul_div_cancel_left _ hb] at hcd
      refine ⟨⟨mul_dvd_mul (dvd_mul_right b t) dvd_rfl, (Nat.mul_pos hm hq0).ne'⟩, ?_⟩
      rw [mul_right_comm b t q, Nat.mul_div_cancel_left _ (Nat.mul_pos hb hq0)]
      exact hcd.mul_left (Nat.coprime_mul_iff_right.1 hc).2

private theorem unitarySum {m q : ℕ} (hm : 0 < m) (hq : IsPrimePow q)
    (hc : q.Coprime m) : usigma (m*q) = usigma m * (q+1) := by
  have dis : Disjoint (unitaryDivisors m) ((unitaryDivisors m).image (· * q)) := by
    rw [Finset.disjoint_left]
    intro d hd hd'
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hd'
    have dvd : b*q ∣ m := (Nat.mem_divisors.1 (Finset.mem_filter.1 hd).1).1
    exact hq.ne_one (hc.eq_one_of_dvd ((dvd_mul_left q b).trans dvd))
  unfold usigma
  rw [splitUnitary hm hq hc, Finset.sum_union dis,
    Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_right hq.pos h),
    ← Finset.sum_mul, mul_add, mul_one, add_comm]

private theorem even_sum {p : ℕ} (hp : Odd p) (k : ℕ) :
    Odd (∑ j ∈ Finset.range (2*k+1), p^j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2*(k+1)+1 = (2*k+1)+1+1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ]
    exact (ih.add_odd hp.pow).add_odd hp.pow

private theorem paired_sum {p : ℕ} (hp : Odd p) (k : ℕ) :
    ∃ t : ℕ, Odd t ∧ (∑ j ∈ Finset.range (4*k+2), p^j) = (p+1)*t := by
  induction k with
  | zero => exact ⟨1, by decide, by simp [Finset.sum_range_succ, Nat.add_comm]⟩
  | succ k ih =>
    obtain ⟨t, ht, eqn⟩ := ih
    let n := 4*k+2
    refine ⟨t + p^n + p^(n+2), (ht.add_odd hp.pow).add_odd hp.pow, ?_⟩
    rw [show 4*(k+1)+2 = n+1+1+1+1 by dsimp [n]; omega]
    iterate 4 rw [Finset.sum_range_succ]
    change (∑ j ∈ Finset.range (4*k+2), p^j) + _ + _ + _ + _ = _
    rw [eqn]
    simp only [pow_succ]
    ring

theorem prime_power {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : e % 4 ≠ 3) :
    ∃ t : ℕ, Odd t ∧ σ 1 (p^e) ∣ t*(p^e+1) := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  by_cases h : e % 2 = 0
  · obtain ⟨k, rfl⟩ : ∃ k, e = 2*k := ⟨e/2, by omega⟩
    exact ⟨_, even_sum ho k, dvd_mul_right ..⟩
  · obtain ⟨k, rfl⟩ : ∃ k, e = 4*k+1 := ⟨e/4, by omega⟩
    obtain ⟨t, ht, eqn⟩ := paired_sum ho k
    have heo : Odd (4*k+1) := ⟨2*k, by omega⟩
    have hd : p+1 ∣ p^(4*k+1)+1 := by simpa using heo.nat_add_dvd_pow_add_pow p 1
    exact ⟨t, ht, by rw [eqn, mul_comm (p+1)]; exact Nat.mul_dvd_mul_left _ hd⟩

private theorem product_bound (m : ℕ) (ho : Odd m)
    (h : ∀ q : ℕ, m.factorization q % 4 ≠ 3) :
    ∃ t : ℕ, Odd t ∧ σ 1 m ∣ t*usigma m := by
  induction m using Nat.recOnPrimePow with
  | zero => simp at ho
  | one => exact ⟨1, by decide, by simp⟩
  | prime_pow_mul a p n hp hpa hn ih =>
    have ha : a ≠ 0 := by rintro rfl; simp at ho
    have hd := Nat.factorization_eq_zero_of_not_dvd hpa
    have ep := h p
    rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) ha, Finsupp.add_apply,
      Nat.factorization_pow_self hp, hd, add_zero] at ep
    have hodd := Nat.odd_mul.mp ho
    have op : Odd p := by
      by_contra hnodd
      have := (Nat.not_odd_iff_even.mp hnodd).pow_of_ne_zero hn.ne'
      exact (Nat.not_even_iff_odd.mpr hodd.1) this
    obtain ⟨u,hu,du⟩ := prime_power hp op ep
    obtain ⟨v,hv,dv⟩ := ih hodd.2 (by
      intro q
      by_cases eq : p = q
      · subst q; simp [hd]
      · have eqn := h q
        simpa [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) ha,
          hp.factorization_pow, Finsupp.single_eq_of_ne (Ne.symm eq)] using eqn)
    have co := (hp.coprime_iff_not_dvd.2 hpa).pow_left n
    refine ⟨u*v, hu.mul hv, ?_⟩
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime co, mul_comm (p^n) a,
      unitarySum (Nat.pos_of_ne_zero ha) ((isPrimePow_nat_iff _).2 ⟨p,n,hp,hn,rfl⟩) co]
    convert Nat.mul_dvd_mul du dv using 1 <;> ring

theorem exceptional_exponent {m : ℕ} (ho : Odd m) (hm : A m) :
    ∃ q : ℕ, m.factorization q % 4 = 3 := by
  by_contra! h
  obtain ⟨t,ht,dt⟩ := product_bound m ho h
  rw [hm.2] at dt
  have pos : 0 < usigma m := by
    have hs := ArithmeticFunction.sigma_pos 1 m hm.1.ne'
    rw [hm.2] at hs
    omega
  have hd : 2 ∣ t := (Nat.dvd_of_mul_dvd_mul_right pos dt)
  exact (Nat.not_even_iff_odd.mpr ht) (even_iff_two_dvd.mpr hd)

def H1 : Prop := ∀ m q : ℕ, Odd m → m.factorization q = 3 → ¬ A m

def H2 : Prop := ∀ m q k : ℕ, Odd m → m.factorization q = 4*k+7 → ¬ A m

theorem main : H1 → H2 → OMA.R_OeisA63880_mod_216_of_a_R1.H1 := by
  intro small large m ho hm
  obtain ⟨q, hq⟩ := exceptional_exponent ho hm
  by_cases h : m.factorization q = 3
  · exact small m q ho h hm
  · exact large m q (m.factorization q / 4 - 1) ho (by omega) hm

end OMA.R_OeisA63880_mod_216_of_a_R1_H1_R1
