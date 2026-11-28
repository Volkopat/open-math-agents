import OMAReductions.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_solvable_R1
import Mathlib.GroupTheory.ClassEquation
import Mathlib.GroupTheory.Rank
import Mathlib.GroupTheory.Sylow
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Finite groups with distinct conjugacy class sizes and prime divisors among two, three and five

The class equation and the structure of two-groups with a small centralizer settle all cases
with at most two prime divisors. For the remaining orders the proof isolates four structural
hypotheses corresponding to the small-centralizer cases in Zhou and Gorshkov, arXiv 2606.22244.

The denominator estimates use integer arithmetic. Scaling all class sizes by 360 allows the
same estimate even when some of the candidate denominators do not divide the group order.
-/

namespace OMA.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_solvable_R1_H2_R1
open Subgroup ConjClasses ConjugacyClassSizes Finset
open scoped Classical
variable {G : Type} [Group G] [Fintype G]

private theorem class_mul_cent (x : G) :
    conjClassCard (ConjClasses.mk x) * Nat.card (centralizer {x}) = Nat.card G := by
  classical
  rw [conjClassCard, Subgroup.nat_card_centralizer_nat_card_stabilizer]
  simp only [Nat.card_eq_fintype_card, ConjClasses.card_carrier]
  apply Nat.div_mul_cancel
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  exact (MulAction.stabilizer (ConjAct G) x).card_subgroup_dvd_card

omit [Fintype G] in
private theorem cent_one : centralizer {(1 : G)} = ⊤ := by
  ext
  simp [mem_centralizer_singleton_iff]

omit [Fintype G] in
private theorem self_le_cent (x : G) : zpowers x ≤ centralizer {x} := by
  simp [zpowers_le, mem_centralizer_singleton_iff]

private theorem cent_ne_one [Nontrivial G] (x : G) : Nat.card (centralizer {x}) ≠ 1 := by
  intro he
  have hx := card_le_of_le (self_le_cent x)
  rw [Nat.card_zpowers, he] at hx
  have hx1 := orderOf_pos x
  obtain rfl := orderOf_eq_one_iff.mp (by omega : orderOf x = 1)
  rw [cent_one, card_top] at he
  exact (ne_of_gt Finite.one_lt_card) he

omit [Fintype G] in
private theorem order_prime_of_cent {p : ℕ} (hp : p.Prime) {x : G}
    (hx : x ≠ 1) (hc : Nat.card (centralizer {x}) = p) : orderOf x = p := by
  have hd := card_dvd_of_le (self_le_cent x)
  rw [Nat.card_zpowers, hc] at hd
  exact ((Nat.dvd_prime hp).mp hd).resolve_left (mt orderOf_eq_one_iff.mp hx)

private theorem cent_ne_prime {p : ℕ} (hp : p.Prime) (hd : p ^ 2 ∣ Nat.card G)
    (x : G) : Nat.card (centralizer {x}) ≠ p := by
  let : Fact p.Prime := ⟨hp⟩
  intro hc
  have hbig := Nat.le_of_dvd (Nat.card_pos (α := G)) hd
  have hlt : p < p ^ 2 := by nlinarith [hp.two_le]
  by_cases hx : x = 1
  · subst x
    rw [cent_one, card_top] at hc
    omega
  have ho := order_prime_of_cent hp hx hc
  obtain ⟨K, hK, hle⟩ := Sylow.exists_subgroup_card_pow_succ (n := 1) hd
    (H := zpowers x) (by rw [Nat.card_zpowers, pow_one, ho])
  let : IsMulCommutative K := IsPGroup.isMulCommutative_of_card_eq_prime_sq hK
  have hKle : K ≤ centralizer {x} := by
    intro y hy
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      (mul_comm' (⟨y, hy⟩ : K) ⟨x, hle (mem_zpowers x)⟩))
  have hle' := card_le_of_le hKle
  rw [hc, hK] at hle'
  exact hlt.not_ge hle'

private theorem sizes_mem {s : ℕ} : s ∈ (univ.image (conjClassCard (G := G))) ↔ ∃ x : G, conjClassCard (ConjClasses.mk x) = s := by
  classical
  simp only [mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c.out, (congrArg conjClassCard (Quotient.out_eq c)).trans hc⟩
  · rintro ⟨x, hx⟩
    exact ⟨ConjClasses.mk x, hx⟩

private theorem size_sum (h : HasDistinctConjClassSizes G) :
    ∑ d ∈ (univ.image (conjClassCard (G := G))), d = Nat.card G := by
  classical
  rw [sum_image (fun _ _ _ _ he => h he)]
  simpa [conjClassCard, Nat.card_eq_fintype_card, Set.toFinset_card] using
    (sum_conjClasses_card_eq_card G)

private theorem sizes_sub : (univ.image (conjClassCard (G := G))) ⊆ (Nat.card G).divisors := by
  intro s hs
  obtain ⟨x, rfl⟩ := sizes_mem.mp hs
  exact Nat.mem_divisors.mpr ⟨⟨_, (class_mul_cent x).symm⟩, Nat.card_pos.ne'⟩

private theorem missing {k : ℕ} (hd : k ∣ Nat.card G)
    (hc : ∀ x : G, Nat.card (centralizer {x}) ≠ k) : Nat.card G / k ∉ (univ.image (conjClassCard (G := G))) := by
  intro hs
  obtain ⟨x, hx⟩ := sizes_mem.mp hs
  have he := class_mul_cent x
  rw [hx] at he
  have he' := he.trans (Nat.div_mul_cancel hd).symm
  apply hc x
  exact Nat.eq_of_mul_eq_mul_left (Nat.div_pos (Nat.le_of_dvd Nat.card_pos hd)
    (Nat.pos_of_dvd_of_pos hd Nat.card_pos)) he'

private theorem budget (h : HasDistinctConjClassSizes G) (F : Finset ℕ)
    (hd : F ⊆ (Nat.card G).divisors) (hm : ∀ d ∈ F, d ∉ (univ.image (conjClassCard (G := G)))) :
    Nat.card G + ∑ d ∈ F, d ≤ (∑ d ∈ (Nat.card G).divisors, d) := by
  classical
  nth_rw 1 [← size_sum h]
  rw [← sum_union (Finset.disjoint_right.mpr hm)]
  exact sum_le_sum_of_subset_of_nonneg (union_subset sizes_sub hd) (by intros; positivity)

private theorem sigma_pow {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (p-1) * (∑ d ∈ (p^a).divisors, d) + 1 = p * p^a := by
  rw [Nat.sum_divisors_prime_pow hp]
  induction a with
  | zero => simp; have := hp.two_le; omega
  | succ a ih =>
    rw [Finset.sum_range_succ, pow_succ, Nat.mul_add]
    have he : p-1+1 = p := by have := hp.two_le; omega
    nlinarith [congrArg (fun t => t * p^a * p) he]

private theorem order_factor (n : ℕ) (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → p = 2 ∨ p = 3 ∨ p = 5) :
    ∃ a b c : ℕ, n = 2^a * 3^b * 5^c := by
  classical
  refine ⟨n.factorization 2, n.factorization 3, n.factorization 5, ?_⟩
  have hs : n.primeFactors ⊆ ({2,3,5} : Finset ℕ) := by
    intro p hp
    simpa using h p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  have he := Finset.prod_subset hs (f := fun p => p ^ n.factorization p)
    (fun p _ hp => by rw [(Finsupp.notMem_support_iff.mp hp : n.factorization p = 0), pow_zero])
  rw [Nat.prod_primeFactors_pow_factorization hn, he]
  norm_num [mul_assoc]


private theorem denominator_budget (h : HasDistinctConjClassSizes G) (D : Finset ℕ)
    (hd : ∀ k ∈ D, k ∣ Nat.card G) (hm : ∀ k ∈ D, ∀ x : G, Nat.card (centralizer {x}) ≠ k) :
    Nat.card G + ∑ k ∈ D, Nat.card G / k ≤ (∑ d ∈ (Nat.card G).divisors, d) := by
  classical
  let n := Nat.card G
  have hinj : Set.InjOn (fun k => n/k) (↑D : Set ℕ) := by
    intro k hk l hl he
    have he' := congrArg (fun t => n/t) he
    change Nat.card G / (Nat.card G / k) = Nat.card G / (Nat.card G / l) at he'
    rwa [Nat.div_div_self (hd k hk) Nat.card_pos.ne',
      Nat.div_div_self (hd l hl) Nat.card_pos.ne'] at he'
  have hb := budget h (D.image (fun k => n/k))
    (by intro d hh; obtain ⟨k, hk, rfl⟩ := mem_image.mp hh
        exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (hd k hk), Nat.card_pos.ne'⟩)
    (by intro d hh; obtain ⟨k, hk, rfl⟩ := mem_image.mp hh
        exact missing (hd k hk) (hm k hk))
  simpa only [sum_image hinj] using hb

private theorem sigma_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hcop : p.Coprime q) (a b : ℕ) :
    (p-1)*(q-1)*(∑ d ∈ (p^a*q^b).divisors, d) < p*q*(p^a*q^b) := by
  have e := sigma_pow hp a
  have f := sigma_pow hq b
  have l : (p-1)*(∑ d ∈ (p^a).divisors, d) < p*p^a := by omega
  have r : (q-1)*(∑ d ∈ (q^b).divisors, d) < q*q^b := by omega
  rw [(hcop.pow_left a |>.pow_right b).sum_divisors_mul]
  change (p-1)*(q-1)*((∑ d ∈ (p^a).divisors, d)*(∑ d ∈ (q^b).divisors, d)) < _
  calc
    _ = ((p-1)*(∑ d ∈ (p^a).divisors, d))*((q-1)*(∑ d ∈ (q^b).divisors, d)) := by ring
    _ < (p*p^a)*(q*q^b) := Nat.mul_lt_mul_of_lt_of_le l r.le (Nat.mul_pos hq.pos (pow_pos hq.pos b))
    _ = _ := by ring

private theorem pow_two_dvd {p a : ℕ} (ha : 2 ≤ a) : p^2 ∣ p^a :=
  pow_dvd_pow p ha

private theorem no_two_five [Nontrivial G] (h : HasDistinctConjClassSizes G)
    {a c : ℕ} (hn : Nat.card G = 2^a * 5^c) : False := by
  have hb := denominator_budget h {1} (by simp) (by simpa using cent_ne_one (G := G))
  simp only [sum_singleton, Nat.div_one] at hb
  have hc := sigma_pow (by decide : Nat.Prime 5) c
  have he := (show Nat.Coprime 2 5 by decide).pow_left a |>.pow_right c
  by_cases ha : 2 ≤ a
  · have h4 : 2^2 ∣ Nat.card G := hn ▸ dvd_mul_of_dvd_left (pow_two_dvd ha) _
    have h2 : 2 ∣ Nat.card G := dvd_trans (by decide : 2 ∣ 2^2) h4
    have hl := denominator_budget h {1,2} (by simpa using h2)
      (by simp only [mem_insert, mem_singleton]; rintro k (rfl | rfl);
          exacts [cent_ne_one, cent_ne_prime (by decide) h4])
    rw [sum_insert (by decide), sum_singleton, Nat.div_one] at hl
    have hu := sigma_two_primes (by decide : Nat.Prime 2) (by decide : Nat.Prime 5)
      (by decide) a c
    rw [← hn] at hu
    norm_num only [Nat.reduceSub, Nat.reduceMul, one_mul] at hu
    omega
  · rw [hn, he.sum_divisors_mul] at hb
    change 2^a * 5^c + 2^a * 5^c ≤ (∑ d ∈ (2^a).divisors, d) * (∑ d ∈ (5^c).divisors, d) at hb
    have s1 : (∑ d ∈ (1 : ℕ).divisors, d) = 1 := by decide
    have s2 : (∑ d ∈ (2 : ℕ).divisors, d) = 3 := by decide
    interval_cases a <;> simp only [pow_zero, pow_one, s1, s2, one_mul] at hb <;> omega


private theorem order_multiple_four_of_five (h : HasDistinctConjClassSizes G)
    (h7 : (Nat.card G).Coprime 7) (h5 : 5 ∣ Nat.card G) : ∃ g : G, 4 ∣ orderOf g := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) 5 h5
  have hr := R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_solvable_R1.rational_of_distinct h x 7 h7
  obtain ⟨g, hg⟩ := isConj_iff.mp hr
  have hiter (m : ℕ) : (MulAut.conj (g^m)) x = x ^ (7^m) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', map_mul, MulAut.mul_apply, ih, map_pow, pow_succ', pow_mul]
      change (g*x*g⁻¹)^(7^m) = _
      rw [hg]
  have he : x ^ (7 ^ orderOf g) = x^1 := by
    simpa only [pow_orderOf_eq_one, map_one, MulAut.one_apply, pow_one] using
      (hiter (orderOf g)).symm
  have hm := pow_eq_pow_iff_modEq.mp he
  rw [hx] at hm
  have hz := (ZMod.natCast_eq_natCast_iff _ _ 5).mpr hm
  have hpow : (7 : ZMod 5) ^ orderOf g = 1 := by simpa using hz
  have hord : orderOf (7 : ZMod 5) = 4 := by
    apply orderOf_eq_of_pow_and_pow_div_prime (by decide) (by decide)
    intro p hp hd
    have he : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow (n := 2) hd)
    subst p
    decide
  exact ⟨g, hord ▸ orderOf_dvd_of_pow_eq_one hpow⟩

omit [Fintype G] in
private theorem same_cent {x y : G} (he : zpowers x = zpowers y) : centralizer {x} = centralizer {y} := by
  rw [← centralizer_closure, ← centralizer_closure ({y} : Set G),
    ← zpowers_eq_closure, ← zpowers_eq_closure, he]

private theorem prime_cent_disjoint {p : ℕ} (hp : p.Prime)
    (hm : (Nat.card G).factorization p = 1) {x z : G}
    (hx : x ≠ 1) (hc : Nat.card (centralizer {x}) = p) (hz : z ≠ 1)
    (hd : p ∣ Nat.card (centralizer {z})) : Nat.card (centralizer {z}) = p := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have ox := order_prime_of_cent hp hx hc
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := centralizer {z}) p hd
  let y : G := v
  have oy : orderOf y = p := (Subgroup.orderOf_coe v).trans hv
  let P := Sylow.ofCard (p := p) (zpowers x) (by rw [Nat.card_zpowers, ox, hm, pow_one])
  let Q := Sylow.ofCard (p := p) (zpowers y) (by rw [Nat.card_zpowers, oy, hm, pow_one])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  let w := (MulAut.conj g) x
  have he : zpowers w = zpowers y := by
    change (zpowers ((MulAut.conj g) x)) = _
    change zpowers ((MulAut.conj g).toMonoidHom x) = _
    rw [← MonoidHom.map_zpowers]
    exact congrArg Sylow.toSubgroup hg
  have hw : IsConj x w := isConj_iff.mpr ⟨g, rfl⟩
  have hec := mk_eq_mk_iff_isConj.mpr hw
  have hcard := class_mul_cent w
  rw [← hec, same_cent he] at hcard
  have hpos : 0 < conjClassCard (ConjClasses.mk x) := by
    have := class_mul_cent x
    by_contra! hh
    have hz' : conjClassCard (ConjClasses.mk x) = 0 := by omega
    rw [hz', zero_mul] at this
    exact Nat.card_pos.ne' this.symm
  have cy : Nat.card (centralizer {y}) = p :=
    (Nat.eq_of_mul_eq_mul_left hpos (hcard.trans (class_mul_cent x).symm)).trans hc
  have hyz : z ∈ centralizer {y} := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp v.property).symm
  have hdiv := card_dvd_of_le (zpowers_le.mpr hyz)
  rw [Nat.card_zpowers, cy] at hdiv
  have oz := ((Nat.dvd_prime hp).mp hdiv).resolve_left (mt orderOf_eq_one_iff.mp hz)
  have he1 := eq_of_le_of_card_ge (zpowers_le.mpr hyz) (by rw [Nat.card_zpowers, oz, cy])
  have he2 := eq_of_le_of_card_ge (self_le_cent y) (by rw [Nat.card_zpowers, oy, cy])
  rwa [same_cent (he1.trans he2.symm)]


private theorem sigma23_fixed (a b : ℕ) :
    2*(∑ d ∈ (2^a*3^b).divisors, d) < (∑ d ∈ (2^a).divisors, d)*3*3^b := by
  have hc := sigma_pow (by decide : Nat.Prime 3) b
  have h2 : 2*(∑ d ∈ (3^b).divisors, d) < 3*3^b := by omega
  have hs := sigma_pow (by decide : Nat.Prime 2) a
  have hpos : 0 < (∑ d ∈ (2^a).divisors, d) := by
    have : 0 < 2^a := by positivity
    omega
  have he := (show Nat.Coprime 2 3 by decide).pow_left a |>.pow_right b
  rw [he.sum_divisors_mul]
  change 2*((∑ d ∈ (2^a).divisors, d)*(∑ d ∈ (3^b).divisors, d)) < _
  nlinarith [Nat.mul_lt_mul_of_pos_left h2 hpos]

private theorem two_three [Nontrivial G] (h : HasDistinctConjClassSizes G)
    {a b : ℕ} (hn : Nat.card G = 2^a*3^b) :
    Nat.card G = 6 ∨ (4 ≤ a ∧ 2 ≤ b ∧
      (∃ x : G, Nat.card (centralizer {x}) = 4) ∧ ∃ x : G, Nat.card (centralizer {x}) = 6) := by
  have hbase := denominator_budget h {1} (by simp) (by simpa using cent_ne_one (G := G))
  rw [sum_singleton, Nat.div_one] at hbase
  have Apos : 0 < 2^a := by positivity
  have Bpos : 0 < 3^b := by positivity
  have hs2 := sigma_pow (by decide : Nat.Prime 2) a
  have hs3 := sigma_pow (by decide : Nat.Prime 3) b
  by_cases ha0 : a = 0
  · subst a
    simp only [pow_zero, one_mul] at hn
    rw [hn] at hbase
    omega
  by_cases hb0 : b = 0
  · subst b
    simp only [pow_zero, mul_one] at hn
    rw [hn] at hbase
    omega
  have d2 : 2 ∣ Nat.card G := hn ▸ dvd_mul_of_dvd_left (dvd_pow_self 2 ha0) _
  have d3 : 3 ∣ Nat.card G := hn ▸ dvd_mul_of_dvd_right (dvd_pow_self 3 hb0) _
  have d6 : 6 ∣ Nat.card G := (show Nat.Coprime 2 3 by decide).mul_dvd_of_dvd_of_dvd d2 d3
  have hfixed := sigma23_fixed a b
  rw [← hn] at hfixed
  by_cases ha1 : a = 1
  · subst a
    by_cases hb1 : b = 1
    · subst b; left; exact hn
    have d9 : 3^2 ∣ Nat.card G := hn ▸ dvd_mul_of_dvd_right (pow_two_dvd (by omega)) _
    have m3 := cent_ne_prime (by decide : Nat.Prime 3) d9
    have hl := denominator_budget h ({1,3} : Finset ℕ)
      (by simp only [mem_insert, mem_singleton]; rintro k (rfl | rfl);
          exacts [one_dvd _, d3])
      (by simp only [mem_insert, mem_singleton]; rintro k (rfl | rfl);
          exacts [cent_ne_one, m3])
    rw [sum_insert (by decide), sum_singleton, Nat.div_one] at hl
    simp only [pow_one] at hn
    have hs : (∑ d ∈ (2 : ℕ).divisors, d) = 3 := by decide
    simp only [pow_one, hs] at hfixed
    omega
  have d4 : 2^2 ∣ Nat.card G := hn ▸ dvd_mul_of_dvd_left (pow_two_dvd (by omega)) _
  have m2 := cent_ne_prime (by decide : Nat.Prime 2) d4
  by_cases hb1 : b = 1
  · subst b
    simp only [pow_one] at hn
    have hupper : (∑ d ∈ (Nat.card G).divisors, d) < 8 * 2^a := by
      have hc := (show Nat.Coprime 2 3 by decide).pow_left a
      rw [hn, hc.sum_divisors_mul]
      change (∑ d ∈ (2^a).divisors, d)*(∑ d ∈ (3 : ℕ).divisors, d) < _
      have hf : (∑ d ∈ (3 : ℕ).divisors, d) = 4 := by decide
      rw [hf]
      omega
    have hforce : ∃ x : G, Nat.card (centralizer {x}) = 3 := by
      by_contra! m3
      have hl := denominator_budget h ({1,2,3} : Finset ℕ)
        (by simp only [mem_insert, mem_singleton]; rintro k (rfl | rfl | rfl);
            exacts [one_dvd _, d2, d3])
        (by simp only [mem_insert, mem_singleton]; rintro k (rfl | rfl | rfl);
            exacts [cent_ne_one, m2, m3])
      rw [sum_insert (by decide), sum_insert (by decide), sum_singleton, Nat.div_one] at hl
      omega
    obtain ⟨x, hx⟩ := hforce
    have hm : (Nat.card G).factorization 3 = 1 := by
      rw [hn, Nat.factorization_mul (by positivity) (by decide), Finsupp.add_apply,
        Nat.prime_two.factorization_pow, Nat.prime_three.factorization]
      simp
    have m6 : ∀ z : G, Nat.card (centralizer {z}) ≠ 6 := by
      intro z hz
      by_cases he : Nat.card G = 6
      · have he4 : 4 ∣ 6 := he ▸ d4
        omega
      have hxn : x ≠ 1 := by
        rintro rfl; rw [cent_one, card_top] at hx; omega
      have hzn : z ≠ 1 := by
        rintro rfl; rw [cent_one, card_top] at hz; exact he hz
      have := prime_cent_disjoint Nat.prime_three hm hxn hx hzn (by rw [hz]; decide)
      omega
    have hl := denominator_budget h ({1,2,6} : Finset ℕ)
      (by simp only [mem_insert, mem_singleton]; rintro k (rfl | rfl | rfl);
          exacts [one_dvd _, d2, d6])
      (by simp only [mem_insert, mem_singleton]; rintro k (rfl | rfl | rfl);
          exacts [cent_ne_one, m2, m6])
    rw [sum_insert (by decide), sum_insert (by decide), sum_singleton, Nat.div_one] at hl
    omega
  have d9 : 3^2 ∣ Nat.card G := hn ▸ dvd_mul_of_dvd_right (pow_two_dvd (by omega)) _
  have m3 := cent_ne_prime (by decide : Nat.Prime 3) d9
  have hl := denominator_budget h ({1,2,3} : Finset ℕ)
    (by simp only [mem_insert, mem_singleton]; rintro k (rfl | rfl | rfl);
        exacts [one_dvd _, d2, d3])
    (by simp only [mem_insert, mem_singleton]; rintro k (rfl | rfl | rfl);
        exacts [cent_ne_one, m2, m3])
  rw [sum_insert (by decide), sum_insert (by decide), sum_singleton, Nat.div_one] at hl
  have ha : 4 ≤ a := by
    by_contra! ht
    interval_cases a <;> first | contradiction | (
      norm_num only [Nat.reducePow] at hn hfixed
      have s4 : (∑ d ∈ (4 : ℕ).divisors, d) = 7 := by decide
      have s8 : (∑ d ∈ (8 : ℕ).divisors, d) = 15 := by decide
      simp only [s4, s8] at hfixed
      omega)
  have hu := sigma_two_primes Nat.prime_two Nat.prime_three (by decide) a b
  rw [← hn] at hu
  norm_num only [Nat.reduceSub, Nat.reduceMul, one_mul] at hu
  refine Or.inr ⟨ha, by omega, ?_, ?_⟩
  · by_contra! m4
    have hl := denominator_budget h ({1,2,3,4} : Finset ℕ)
      (by simp only [mem_insert, mem_singleton]; rintro k (rfl | rfl | rfl | rfl);
          exacts [one_dvd _, d2, d3, d4])
      (by simp only [mem_insert, mem_singleton]; rintro k (rfl | rfl | rfl | rfl);
          exacts [cent_ne_one, m2, m3, m4])
    rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton, Nat.div_one] at hl
    omega
  · by_contra! m6
    have hl := denominator_budget h ({1,2,3,6} : Finset ℕ)
      (by simp only [mem_insert, mem_singleton]; rintro k (rfl | rfl | rfl | rfl);
          exacts [one_dvd _, d2, d3, d6])
      (by simp only [mem_insert, mem_singleton]; rintro k (rfl | rfl | rfl | rfl);
          exacts [cent_ne_one, m2, m3, m6])
    rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton, Nat.div_one] at hl
    omega


private theorem sigma235 (a b c : ℕ) : 4*(∑ d ∈ (2^a*3^b*5^c).divisors, d) < 15*(2^a*3^b*5^c) := by
  have h23 := sigma_two_primes Nat.prime_two Nat.prime_three (by decide) a b
  norm_num only [Nat.reduceSub, Nat.reduceMul, one_mul] at h23
  have h5 := sigma_pow (by decide : Nat.Prime 5) c
  have h5' : 4*(∑ d ∈ (5^c).divisors, d) < 5*5^c := by omega
  have cop := ((show Nat.Coprime 2 5 by decide).pow_left a |>.mul_left
    ((show Nat.Coprime 3 5 by decide).pow_left b)).pow_right c
  rw [cop.sum_divisors_mul]
  change 4*((∑ d ∈ (2^a*3^b).divisors, d)*(∑ d ∈ (5^c).divisors, d)) < _
  have v := Nat.mul_lt_mul_of_lt_of_le h23 h5'.le (by positivity : 0 < 5*5^c)
  nlinarith

private theorem weight_budget (h : HasDistinctConjClassSizes G)
    {a b c : ℕ} (hn : Nat.card G = 2^a*3^b*5^c) (W : Finset ℕ)
    (ht : ∀ w ∈ W, w ∣ 360) (hw : 990 ≤ ∑ w ∈ W, w) :
    ∃ x : G, ∃ w ∈ W, w * Nat.card (centralizer {x}) = 360 := by
  classical
  by_contra! hlarge
  let n := Nat.card G
  let S := ((univ.image (conjClassCard (G := G)))).image (fun d => 360*d)
  let T := W.image (fun w => w*n)
  have hnpos : 0 < n := Nat.card_pos
  have hdis : Disjoint S T := by
    apply disjoint_right.mpr
    intro d hd hs
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hd
    obtain ⟨s, hs, he⟩ := mem_image.mp hs
    obtain ⟨x, rfl⟩ := sizes_mem.mp hs
    have hh := class_mul_cent x
    change conjClassCard (ConjClasses.mk x) * Nat.card (centralizer {x}) = n at hh
    have hpos : 0 < conjClassCard (ConjClasses.mk x) :=
      (Nat.mul_pos_iff_of_pos_right (Nat.card_pos (α := centralizer {x}))).mp (hh.symm ▸ hnpos)
    rw [← hh] at he
    have he' : 360*conjClassCard (ConjClasses.mk x) = (w*Nat.card (centralizer {x}))*conjClassCard (ConjClasses.mk x) := he.trans (by ring)
    have hf := Nat.eq_of_mul_eq_mul_right hpos he'
    exact hlarge x w hw hf.symm
  have hsub : S ∪ T ⊆ (360*n).divisors := by
    intro d hd
    apply Nat.mem_divisors.mpr
    refine ⟨?_, by positivity⟩
    rcases mem_union.mp hd with hs | ht'
    · change d ∈ ((univ.image (conjClassCard (G := G)))).image (fun s => 360*s) at hs
      obtain ⟨s, hsize, rfl⟩ := mem_image.mp hs
      exact Nat.mul_dvd_mul_left 360 (Nat.mem_divisors.mp (sizes_sub hsize)).1
    · change d ∈ W.image (fun w => w*n) at ht'
      obtain ⟨w, hw, rfl⟩ := mem_image.mp ht'
      exact Nat.mul_dvd_mul_right (ht w hw) n
  have hb : ∑ d ∈ S ∪ T, d ≤ (∑ d ∈ (360*n).divisors, d) :=
    sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
  rw [sum_union hdis] at hb
  simp only [S, T, sum_image (fun _ _ _ _ he => Nat.eq_of_mul_eq_mul_left (by decide : 0 < 360) he),
    sum_image (fun _ _ _ _ he => Nat.eq_of_mul_eq_mul_right hnpos he), ← sum_mul] at hb
  rw [← Finset.mul_sum, size_sum h] at hb
  have he : 360*n = 2^(a+3)*3^(b+2)*5^(c+1) := by
    dsimp [n]; rw [hn]; simp only [pow_add]; ring
  have hu := sigma235 (a+3) (b+2) (c+1)
  rw [← he] at hu
  change 360*n + (∑ w ∈ W, w)*n ≤ _ at hb
  have := Nat.mul_le_mul_right n hw
  omega

private theorem small_centers [Nontrivial G] (h : HasDistinctConjClassSizes G)
    {a b c : ℕ} (hn : Nat.card G = 2^a*3^b*5^c) (d4 : 4 ∣ Nat.card G) :
    ((∃ x : G, Nat.card (centralizer {x}) ∈ ({3,4,5,6,8,9} : Finset ℕ)) ∨
      ((∃ x : G, Nat.card (centralizer {x}) = 10) ∧ ∃ x : G, Nat.card (centralizer {x}) = 15)) := by
  classical
  by_cases hs : ∃ x : G, Nat.card (centralizer {x}) ∈ ({3,4,5,6,8,9} : Finset ℕ)
  · exact Or.inl hs
  right
  push Not at hs
  simp only [mem_insert, mem_singleton] at hs
  constructor
  · obtain ⟨x,w,hw,he⟩ := weight_budget h hn ({360,180,120,90,72,60,45,40,36} : Finset ℕ)
      (by decide) (by decide)
    refine ⟨x, ?_⟩
    have h1 := cent_ne_one x
    have h2 := cent_ne_prime Nat.prime_two d4 x
    have hno := hs x
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · obtain ⟨x,w,hw,he⟩ := weight_budget h hn ({360,180,120,90,72,60,45,40,24} : Finset ℕ)
      (by decide) (by decide)
    refine ⟨x, ?_⟩
    have h1 := cent_ne_one x
    have h2 := cent_ne_prime Nat.prime_two d4 x
    have hno := hs x
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private theorem order_totient_dvd (h : HasDistinctConjClassSizes G) (x : G) :
    orderOf x * (orderOf x).totient ∣ Nat.card G := by
  classical
  let H := zpowers x
  let u : H := ⟨x, mem_zpowers x⟩
  have hgen (t : H) : t ∈ zpowers u := by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp t.property
    exact mem_zpowers_iff.mpr ⟨k, Subtype.ext hk⟩
  have sur : Function.Surjective H.normalizerMonoidHom := by
    intro f
    let y : G := f u
    have oy : orderOf y = orderOf x := by
      change orderOf (↑(f u) : G) = _
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe u]
    have hy : zpowers y = H := eq_of_le_of_card_ge (zpowers_le.mpr (f u).property)
      (by change Nat.card (zpowers x) ≤ _; rw [Nat.card_zpowers, Nat.card_zpowers, oy])
    have ce := same_cent hy
    have hc : conjClassCard (ConjClasses.mk x) = conjClassCard (ConjClasses.mk y) := by
      apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := centralizer {x}))
      rw [class_mul_cent, ← ce, class_mul_cent]
    obtain ⟨g,hg⟩ := isConj_iff.mp (mk_eq_mk_iff_isConj.mp (h hc))
    have hnorm : g ∈ normalizer (H : Set G) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      change (zpowers x).map (MulAut.conj g).toMonoidHom = _
      rw [MonoidHom.map_zpowers]
      exact (congrArg zpowers hg).trans hy
    refine ⟨⟨g,hnorm⟩, (MulEquiv.eq_iff_eq_on_generator hgen _ _).mpr ?_⟩
    exact Subtype.ext hg
  let K := H.normalizerMonoidHom.ker
  have hker : Nat.card H ∣ Nat.card K := by
    have e := Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (H : Set G))).toEquiv
    change Nat.card H ∣ Nat.card H.normalizerMonoidHom.ker
    rw [normalizerMonoidHom_ker, e]
    change Nat.card (zpowers x) ∣ Nat.card (centralizer (zpowers x : Set G))
    rw [zpowers_eq_closure, centralizer_closure, ← zpowers_eq_closure]
    exact card_dvd_of_le (self_le_cent x)
  have eqn := H.normalizerMonoidHom.ker.card_mul_index
  rw [index_ker, MonoidHom.range_eq_top.mpr sur, card_top, IsCyclic.card_mulAut] at eqn
  have hd : Nat.card H * (Nat.card H).totient ∣ Nat.card (normalizer (H : Set G)) := by
    rw [← eqn]
    exact Nat.mul_dvd_mul_right hker _
  simpa only [H, Nat.card_zpowers] using hd.trans (normalizer (H : Set G)).card_subgroup_dvd_card

/-- Passing to a quotient cannot increase the order of an element centralizer. -/
private theorem quotient_cent_le (K : Subgroup G) [K.Normal] (x : G) :
    Nat.card (centralizer {(QuotientGroup.mk' K x)}) ≤ Nat.card (centralizer {x}) := by
  classical
  let f := QuotientGroup.mk' K
  let e : G ≃ (G ⧸ K) × K := groupEquivQuotientProdSubgroup
  let j (t : (ConjClasses.mk x).carrier) : (ConjClasses.mk (f x)).carrier × K :=
    (⟨f t.val, f.map_isConj t.property⟩, (e t.val).2)
  have hj : Function.Injective j := by
    intro t u hu
    apply Subtype.ext
    apply e.injective
    exact Prod.ext (congrArg (fun v => v.1.val) hu) (congrArg (fun v : (ConjClasses.mk (f x)).carrier × K => v.2) hu)
  have hd := Nat.card_le_card_of_injective j hj
  rw [Nat.card_prod] at hd
  change conjClassCard (ConjClasses.mk x) ≤ conjClassCard (ConjClasses.mk (f x)) * Nat.card K at hd
  have e1 := class_mul_cent x
  have e2 := class_mul_cent (f x)
  have e3 := K.card_eq_card_quotient_mul_card_subgroup
  let : Nonempty (ConjClasses.mk (f x)).carrier := ⟨⟨_, mem_carrier_mk⟩⟩
  have hpos : 0 < conjClassCard (ConjClasses.mk (f x)) := Nat.card_pos
  change Nat.card (centralizer {(f x)}) ≤ _
  apply Nat.le_of_mul_le_mul_left (c := conjClassCard (ConjClasses.mk (f x))*Nat.card K)
  · calc
      _ = Nat.card G := by rw [mul_right_comm, e2, ← e3]
      _ = _ := e1.symm
      _ ≤ _ := Nat.mul_le_mul_right _ hd
  · exact Nat.mul_pos hpos Nat.card_pos

private theorem involution_of_center {a : ℕ} (ha : 0 < a) (hc : Nat.card G = 2^a) :
    ∃ K : Subgroup G, Nat.card K = 2 ∧ K ≤ center G := by
  classical
  obtain ⟨k,hk,hcenter⟩ := IsPGroup.card_center_eq_prime_pow hc ha
  have hd : 2 ∣ Nat.card (center G) := hcenter ▸ dvd_pow_self 2 hk.ne'
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center G) 2 hd
  exact ⟨zpowers (z : G), (Nat.card_zpowers _).trans ((Subgroup.orderOf_coe z).trans hz),
    zpowers_le.mpr z.property⟩

private theorem order_four_of_eight (hc : Nat.card G = 8) (x : G)
    (hx : Nat.card (centralizer {x}) ≤ 4) : ∃ y : G, orderOf y = 4 := by
  by_contra! hn
  have sqone (y : G) : y^2 = 1 := by
    have hd := orderOf_dvd_natCard y
    rw [hc] at hd
    obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 3)).mp hd
    interval_cases k
    · apply orderOf_dvd_iff_pow_eq_one.mp; rw [he]; decide
    · apply orderOf_dvd_iff_pow_eq_one.mp; rw [he]; decide
    · exact (hn y he).elim
    · have hv := orderOf_pow_of_dvd (x := y) (by decide : 2 ≠ 0) (show 2 ∣ orderOf y by rw [he]; decide)
      exact (hn (y^2) (by rw [hv,he]; decide)).elim
  have hi (y : G) : y⁻¹ = y := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [sq] using sqone y
  have htop : centralizer {x} = ⊤ := top_unique fun y _ => mem_centralizer_singleton_iff.mpr (by
    calc
      y*x = (y*x)⁻¹ := (hi _).symm
      _ = x*y := by rw [mul_inv_rev, hi x, hi y])
  rw [htop,card_top,hc] at hx
  omega


/-- Lift a generator of a cyclic index-two subgroup across a central quotient of order two. -/
private theorem lift_large_order {q : ℕ} (hq : 0 < q) (hG : Nat.card G = 16*q)
    (K : Subgroup G) [K.Normal] (hK : Nat.card K = 2) (zK : K ≤ center G)
    (x : G) (hx : Nat.card (centralizer {x}) ≤ 4) (r : G)
    (hr : orderOf (QuotientGroup.mk' K r) = 4*q) : orderOf r = 8*q := by
  classical
  let f := QuotientGroup.mk' K
  let B := zpowers (f r)
  let A := B.comap f
  have qb := K.card_eq_card_quotient_mul_card_subgroup
  have bc : Nat.card B = 4*q := (Nat.card_zpowers _).trans hr
  have bi := B.index_mul_card
  rw [bc] at bi
  have ai : A.index = 2 := by
    rw [show A.index = B.index from B.index_comap_of_surjective (QuotientGroup.mk'_surjective K)]
    rw [hK,hG] at qb
    nlinarith
  have ac : Nat.card A = 8*q := by
    have hh := A.index_mul_card
    rw [ai,hG] at hh
    omega
  let : A.Normal := A.normal_of_index_eq_two ai
  let af : A →* B := (f.comp A.subtype).codRestrict B fun t => t.property
  have hker : af.ker ≤ center A := by
    intro u hu
    have hz := zK ((QuotientGroup.eq_one_iff u.val).mp (congrArg Subtype.val (af.mem_ker.mp hu)))
    exact mem_center_iff.mpr fun t => Subtype.ext (mem_center_iff.mp hz t.val)
  let : IsMulCommutative A := af.isMulCommutative_of_isCyclic_of_ker_le_center hker
  have comm {u v : G} (hu : u ∈ A) (hv : v ∈ A) : Commute u v :=
    congrArg Subtype.val (mul_comm' (⟨u,hu⟩ : A) ⟨v,hv⟩)
  have rA : r ∈ A := mem_zpowers (f r)
  have xout : x ∉ A := by
    intro h
    have hd : A ≤ centralizer {x} := fun t ht => mem_centralizer_singleton_iff.mpr (comm ht h)
    have := card_le_of_le hd
    omega
  have hKC : K ≤ A ⊓ centralizer {x} := by
    intro t ht
    refine ⟨?_, mem_centralizer_singleton_iff.mpr (mem_center_iff.mp (zK ht) x).symm⟩
    change f t ∈ B
    rw [show f t = 1 from (QuotientGroup.eq_one_iff t).mpr ht]
    exact B.one_mem
  have fixed : K = A ⊓ centralizer {x} := by
    apply eq_of_le_of_card_ge hKC
    have hd := card_dvd_of_le hKC
    rw [hK] at hd ⊢
    have hle := card_le_of_le (inf_le_right : A ⊓ centralizer {x} ≤ centralizer {x})
    by_contra! hn
    have eq := eq_of_le_of_card_ge (inf_le_right : A ⊓ centralizer {x} ≤ centralizer {x}) (by omega)
    have hm : x ∈ A ⊓ centralizer {x} := by rw [eq]; exact mem_centralizer_singleton_iff.mpr rfl
    exact xout hm.1
  let α := MulAut.conj x
  have normA {t : G} (ht : t ∈ A) : α t ∈ A := (inferInstance : A.Normal).conj_mem _ ht x
  have fix_iff {t : G} : α t = t ↔ t ∈ centralizer {x} := by
    change x*t*x⁻¹ = t ↔ _
    rw [mul_inv_eq_iff_eq_mul, mem_centralizer_singleton_iff, eq_comm]
  have sqx : x^2 ∈ A := ai ▸ A.pow_index_mem x
  have harr : α (α r) = r := by
    change x*(x*r*x⁻¹)*x⁻¹ = r
    calc
      _ = (x^2)*r*(x^2)⁻¹ := by simp only [sq,mul_inv_rev,mul_assoc]
      _ = r := by rw [(comm sqx rA).eq]; group
  let z := r * α r
  have zK' : z ∈ K := by
    rw [fixed]
    exact ⟨A.mul_mem rA (normA rA), fix_iff.mp (by
      change α (r*α r) = r*α r
      rw [map_mul,harr,(comm (normA rA) rA).eq])⟩
  have zs : z^2 = 1 := by
    have hd := orderOf_dvd_natCard (⟨z,zK'⟩ : K)
    rw [hK] at hd
    exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp hd)
  have rdiv : orderOf r ∣ 8*q := by
    have h := orderOf_dvd_natCard (⟨r,rA⟩ : A)
    rwa [← Subgroup.orderOf_coe,ac] at h
  have low : 4*q ∣ orderOf r := hr ▸ orderOf_map_dvd f r
  by_contra hn
  obtain ⟨d, hd⟩ := low
  have hle := Nat.le_of_dvd (by positivity : 0 < 8*q) rdiv
  have hd1 : d = 1 := by
    have hp := orderOf_pos r
    by_cases h : d = 0
    · rw [h,mul_zero] at hd; omega
    by_cases h2 : 2 ≤ d
    · have hmul := Nat.mul_le_mul_left (4*q) h2
      exfalso; apply hn; omega
    omega
  have rs : r^(4*q) = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hd,hd1,mul_one])
  let t := r^(2*q)
  have ts : t*t = 1 := by
    change r^(2*q)*r^(2*q) = 1
    rw [← pow_add, show 2*q+2*q=4*q by omega, rs]
  have tz : t*α t = 1 := by
    change r^(2*q)*α (r^(2*q)) = 1
    rw [map_pow, ← (comm rA (normA rA)).mul_pow]
    change z^(2*q) = 1
    rw [pow_mul,zs,one_pow]
  have tK : t ∈ K := by
    rw [fixed]
    exact ⟨A.pow_mem rA _, fix_iff.mp (mul_left_cancel (tz.trans ts.symm))⟩
  have tq := (QuotientGroup.eq_one_iff t).mpr tK
  change f (r^(2*q)) = 1 at tq
  rw [map_pow, ← orderOf_dvd_iff_pow_eq_one, hr] at tq
  have := Nat.le_of_dvd (by positivity : 0 < 2*q) tq
  omega

private theorem large_order_two_group (n : ℕ) (P : Type) [Group P] [Fintype P]
    (hc : Nat.card P = 2^(n+3)) (x : P) (hx : Nat.card (centralizer {x}) ≤ 4) :
    ∃ y : P, orderOf y = 2^(n+2) := by
  classical
  induction n generalizing P with
  | zero => exact order_four_of_eight hc x hx
  | succ n ih =>
    obtain ⟨K,hK,zK⟩ := involution_of_center (by omega : 0 < n+1+3) hc
    let : K.Normal := ⟨fun u hu g => by
      rw [(mem_center_iff.mp (zK hu) g), mul_inv_cancel_right]; exact hu⟩
    have qcard := K.card_eq_card_quotient_mul_card_subgroup
    rw [hc,hK, show n+1+3 = (n+3)+1 by omega, pow_succ] at qcard
    have qq : Nat.card (P ⧸ K) = 2^(n+3) := by omega
    obtain ⟨y,hy⟩ := ih (P ⧸ K) qq (QuotientGroup.mk' K x) ((quotient_cent_le K x).trans hx)
    obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective K y
    refine ⟨r, ?_⟩
    have hh := lift_large_order (q := 2^n) (by positivity)
      (by rw [hc, show n+1+3=n+4 by omega,pow_add]; ring) K hK zK x hx r
      (by rw [hy,pow_add]; ring)
    rw [hh, show n+1+2=n+3 by omega,pow_add]
    ring


private theorem no_cent_four (h : HasDistinctConjClassSizes G)
    {a m : ℕ} (ha : 4 ≤ a) (hmpos : 0 < m) (hcop : Nat.Coprime 2 m)
    (hn : Nat.card G = 2^a*m) (x : G) (hx : Nat.card (centralizer {x}) = 4) : False := by
  classical
  have hc := card_dvd_of_le (self_le_cent x)
  rw [hx] at hc
  have hp : IsPGroup 2 (zpowers x) := isPGroup_iff_card_dvd_pow.mpr ⟨2,hc⟩
  obtain ⟨P,hle⟩ := hp.exists_le_sylow
  have pc := P.card_eq_multiplicity
  have hm : (Nat.card G).factorization 2 = a := by
    rw [hn, Nat.factorization_mul (by positivity) hmpos.ne', Finsupp.add_apply,
      Nat.prime_two.factorization_pow, Nat.factorization_eq_zero_of_not_dvd
        (Nat.prime_two.coprime_iff_not_dvd.mp hcop)]
    simp
  rw [hm] at pc
  let u : P := ⟨x,hle (mem_zpowers x)⟩
  have hu : Nat.card (centralizer ({u} : Set P)) ≤ 4 := by
    rw [← hx]
    apply Nat.card_le_card_of_injective (fun v => (⟨(v.val : G),
      mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
        (mem_centralizer_singleton_iff.mp v.property))⟩ : centralizer {x}))
    intro v w hvw
    exact Subtype.ext (Subtype.ext (congrArg (fun z : centralizer {x} => (z : G)) hvw))
  obtain ⟨v,hv⟩ := large_order_two_group (a-3) P (by rwa [show a-3+3=a by omega]) u hu
  rw [show a-3+2=a-1 by omega] at hv
  have hd := order_totient_dvd h (v : G)
  rw [Subgroup.orderOf_coe, hv, Nat.totient_prime_pow Nat.prime_two (by omega)] at hd
  simp only [Nat.reduceSub, mul_one, ← pow_add] at hd
  rw [hn] at hd
  have cp : Nat.Coprime (2^(a-1+(a-1-1))) m := hcop.pow_left _
  have le := Nat.le_of_dvd (by positivity : 0 < 2^a) (cp.dvd_of_dvd_mul_right hd)
  exact (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : a < a-1+(a-1-1))).not_ge le

/-- Every nontrivial group of order a product of powers of two and three with distinct class sizes has order six. -/
theorem two_three_order [Nontrivial G] (h : HasDistinctConjClassSizes G) {a b : ℕ}
    (hn : Nat.card G = 2^a*3^b) : Nat.card G = 6 := by
  obtain h6 | ⟨ha, _, ⟨x,hx⟩, _⟩ := two_three h hn
  · exact h6
  · exact (no_cent_four h ha (by positivity) ((show Nat.Coprime 2 3 by decide).pow_right b) hn x hx).elim


private theorem prime_budget [Nontrivial G] (h : HasDistinctConjClassSizes G)
    {p m : ℕ} (hp : p.Prime) (hgt : 1 < m) (cop : p.Coprime m)
    (hn : Nat.card G = p*m) (hm : (Nat.card G).factorization p = 1)
    {x : G} (hx : x ≠ 1) (hc : Nat.card (centralizer {x}) = p)
    (D : Finset ℕ) (hd : ∀ k ∈ D, k ∣ m) (hf : ∀ k ∈ D, ∀ y : G, Nat.card (centralizer {y}) ≠ k) :
    Nat.card G + p * ∑ k ∈ D, m/k ≤ 1+m+p*(∑ d ∈ m.divisors, d) := by
  classical
  let V := m.divisors.image (fun d => p*d)
  let T := D.image (fun k => p*(m/k))
  have hTinj : Set.InjOn (fun k => p*(m/k)) (↑D : Set ℕ) := by
    intro k hk l hl he
    have ht := congrArg (fun t => m/t) (Nat.eq_of_mul_eq_mul_left hp.pos he)
    change m/(m/k) = m/(m/l) at ht
    rwa [Nat.div_div_self (hd k hk) (by omega), Nat.div_div_self (hd l hl) (by omega)] at ht
  have dis : Disjoint ((univ.image (conjClassCard (G := G)))) T := by
    apply disjoint_right.mpr
    intro s hs
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hs
    have hd' : k ∣ Nat.card G := hn ▸ dvd_mul_of_dvd_right (hd k hk) _
    simpa only [hn, Nat.mul_div_assoc p (hd k hk)] using missing hd' (hf k hk)
  have hsub : (univ.image (conjClassCard (G := G))) ∪ T ⊆ insert 1 (insert m V) := by
    intro s hs
    rcases mem_union.mp hs with hh | hh
    · obtain ⟨y,rfl⟩ := sizes_mem.mp hh
      have he := class_mul_cent y
      by_cases hy : y = 1
      · subst y
        rw [cent_one,card_top] at he
        have e := Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := G)) (he.trans (one_mul _).symm)
        rw [e]; exact mem_insert_self ..
      apply mem_insert_of_mem
      by_cases dd : p ∣ Nat.card (centralizer {y})
      · rw [prime_cent_disjoint hp hm hx hc hy dd,hn,mul_comm p m] at he
        rw [Nat.eq_of_mul_eq_mul_right hp.pos he]
        exact mem_insert_self ..
      apply mem_insert_of_mem
      have dmul := (centralizer {y}).card_subgroup_dvd_card
      rw [hn] at dmul
      have d := (hp.coprime_iff_not_dvd.mpr dd).symm.dvd_of_dvd_mul_left dmul
      refine mem_image.mpr ⟨m/Nat.card (centralizer {y}),
        Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd d, by omega⟩, ?_⟩
      apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := centralizer {y}))
      rw [mul_assoc, Nat.div_mul_cancel d, he,hn]
    · obtain ⟨k,hk,rfl⟩ := mem_image.mp hh
      exact mem_insert_of_mem (mem_insert_of_mem (mem_image.mpr
        ⟨_, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (hd k hk), by omega⟩, rfl⟩))
  have hex : m ∉ V := by
    intro he
    obtain ⟨s,_,hs⟩ := mem_image.mp he
    exact hp.coprime_iff_not_dvd.mp cop ⟨s,hs.symm⟩
  have hone : 1 ∉ insert m V := by
    simp only [mem_insert, not_or]
    refine ⟨by omega, ?_⟩
    intro hh
    obtain ⟨s,_,hs⟩ := mem_image.mp hh
    exact hp.not_dvd_one ⟨s,hs.symm⟩
  have hb : ∑ s ∈ (univ.image (conjClassCard (G := G))) ∪ T, s ≤ ∑ s ∈ insert 1 (insert m V), s :=
    sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
  rw [sum_union dis,size_sum h,sum_insert hone,sum_insert hex] at hb
  simp only [T,V,sum_image hTinj,
    sum_image (fun _ _ _ _ he => Nat.eq_of_mul_eq_mul_left hp.pos he)] at hb
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hb
  simpa only [add_assoc] using hb


private theorem no_cent_three [Nontrivial G] (h : HasDistinctConjClassSizes G)
    {a b c : ℕ} (ha : 3 ≤ a) (hb : 0 < b) (hc : 0 < c)
    (hn : Nat.card G = 2^a*3^b*5^c) (x : G) (hx : Nat.card (centralizer {x}) = 3) : False := by
  classical
  have b1 : b = 1 := by
    by_contra hne
    have d9 : 3^2 ∣ Nat.card G := hn ▸ dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right (pow_two_dvd (by omega : 2 ≤ b)) _) _
    exact cent_ne_prime Nat.prime_three d9 x hx
  subst b
  let m := 2^a * 5^c
  have n : Nat.card G = 3*m := by rw [hn]; dsimp [m]; ring
  have d4 : 4 ∣ m := dvd_mul_of_dvd_left (pow_two_dvd (by omega : 2 ≤ a)) _
  have d2 : 2 ∣ m := (by decide : 2 ∣ 4).trans d4
  have d5 : 5 ∣ m := dvd_mul_of_dvd_right (dvd_pow_self 5 hc.ne') _
  have d10 : 10 ∣ m := (show Nat.Coprime 2 5 by decide).mul_dvd_of_dvd_of_dvd d2 d5
  have mpos : 0 < m := by dsimp [m]; positivity
  have m40 : 40 ≤ m := by
    have d8 : 8 ∣ m := dvd_mul_of_dvd_left (pow_dvd_pow 2 ha) _
    exact Nat.le_of_dvd mpos ((show Nat.Coprime 8 5 by decide).mul_dvd_of_dvd_of_dvd d8 d5)
  have cop : Nat.Coprime 3 m := ((show Nat.Coprime 3 2 by decide).pow_right a).mul_right
    ((show Nat.Coprime 3 5 by decide).pow_right c)
  have hm : (Nat.card G).factorization 3 = 1 := by
    rw [n,Nat.factorization_mul (by decide) mpos.ne',Finsupp.add_apply,
      Nat.prime_three.factorization, Nat.factorization_eq_zero_of_not_dvd
        (Nat.prime_three.coprime_iff_not_dvd.mp cop)]
    simp
  have xn : x ≠ 1 := by rintro rfl; rw [cent_one,card_top] at hx; omega
  have PB := prime_budget h Nat.prime_three (by omega : 1 < m) cop n hm xn hx
  have m2 := cent_ne_prime Nat.prime_two (n ▸ dvd_mul_of_dvd_right d4 3 : 4 ∣ Nat.card G)
  have choice : ∃ k : ℕ, (k = 5 ∨ (k = 10 ∧ c = 1)) ∧ ∀ z : G, Nat.card (centralizer {z}) ≠ k := by
    by_cases he : ∃ y : G, Nat.card (centralizer {y}) = 5
    · obtain ⟨y,hy⟩ := he
      have c1 : c = 1 := by
        by_contra hne
        have d25 : 5^2 ∣ Nat.card G := hn ▸ dvd_mul_of_dvd_right (pow_two_dvd (by omega : 2 ≤ c)) _
        exact cent_ne_prime (by decide) d25 y hy
      have yn : y ≠ 1 := by rintro rfl; rw [cent_one,card_top] at hy; omega
      have f5 : (Nat.card G).factorization 5 = 1 := by
        rw [hn,c1,pow_one,pow_one,Nat.factorization_mul (by positivity) (by decide),Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd (show ¬ 5 ∣ 2^a*3 from
            (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 5)).mp
            (((show Nat.Coprime 5 2 by decide).pow_right a).mul_right (by decide))),
          (show Nat.Prime 5 by decide).factorization]
        simp
      exact ⟨10, Or.inr ⟨rfl,c1⟩, fun z hz => by
        have zn : z ≠ 1 := by rintro rfl; rw [cent_one,card_top] at hz; omega
        have := prime_cent_disjoint (by decide : Nat.Prime 5) f5 yn hy zn (by rw [hz]; decide)
        omega⟩
    · exact ⟨5, Or.inl rfl, not_exists.mp he⟩
  obtain ⟨k,hk,mk⟩ := choice
  have dk : k ∣ m := by rcases hk with rfl | ⟨rfl,_⟩ <;> assumption
  have hkmin : 4 < k := by rcases hk with rfl | ⟨rfl,_⟩ <;> decide
  have acc := PB ({1,2,k} : Finset ℕ)
    (by simp only [mem_insert,mem_singleton]; rintro i (rfl|rfl|rfl); exacts [one_dvd _,d2,dk])
    (by simp only [mem_insert,mem_singleton]; rintro i (rfl|rfl|rfl); exacts [cent_ne_one,m2,mk])
  rw [sum_insert (by simp; omega),sum_insert (by simp; omega),sum_singleton,Nat.div_one,n] at acc
  by_cases a3 : a = 3
  · subst a
    rcases hk with rfl | ⟨rfl,rfl⟩
    · have hs : (∑ d ∈ m.divisors, d) = 15*(∑ d ∈ (5^c).divisors, d) := by
        change (∑ d ∈ (8*5^c).divisors, d) = _
        rw [((show Nat.Coprime 8 5 by decide).pow_right c).sum_divisors_mul]
        change (∑ d ∈ (8 : ℕ).divisors, d) * (∑ d ∈ (5^c).divisors, d) = _
        rw [show (∑ d ∈ (8 : ℕ).divisors, d) = 15 by decide]
      have he := sigma_pow (by decide : Nat.Prime 5) c
      have mm : m = 8*5^c := rfl
      omega
    · have mm : m = 40 := by decide
      rw [mm, show (∑ d ∈ (40 : ℕ).divisors, d) = 90 by decide] at acc
      omega
  · have m4 : ∀ y : G, Nat.card (centralizer {y}) ≠ 4 := fun y hy =>
      no_cent_four h (by omega : 4 ≤ a) (by positivity : 0 < 3*5^c)
        ((show Nat.Coprime 2 3 by decide).mul_right ((show Nat.Coprime 2 5 by decide).pow_right c))
        (by rw [hn,pow_one,mul_assoc]) y hy
    have acc4 := PB ({1,2,4,k} : Finset ℕ)
      (by simp only [mem_insert,mem_singleton]; rintro i (rfl|rfl|rfl|rfl); exacts [one_dvd _,d2,d4,dk])
      (by simp only [mem_insert,mem_singleton]; rintro i (rfl|rfl|rfl|rfl); exacts [cent_ne_one,m2,m4,mk])
    rw [sum_insert (by simp; omega),sum_insert (by simp; omega),sum_insert (by simp; omega),
      sum_singleton,Nat.div_one,n] at acc4
    have hu := sigma_two_primes Nat.prime_two (by decide : Nat.Prime 5) (by decide) a c
    change 4*(∑ d ∈ m.divisors, d) < 10*m at hu
    rcases hk with rfl | ⟨rfl,_⟩ <;> omega

private theorem four_or_six_of_cent_five [Nontrivial G] (h : HasDistinctConjClassSizes G)
    {a b c : ℕ} (ha : 3 ≤ a) (hb : 0 < b) (hc : 0 < c)
    (hn : Nat.card G = 2^a*3^b*5^c) (x : G) (hx : Nat.card (centralizer {x}) = 5) :
    (∃ y : G, Nat.card (centralizer {y}) = 4) ∨ ∃ y : G, Nat.card (centralizer {y}) = 6 := by
  classical
  by_contra! hno
  obtain ⟨m4,m6⟩ := hno
  have c1 : c = 1 := by
    by_contra hn'
    have d := pow_two_dvd (p := 5) (by omega : 2 ≤ c)
    exact cent_ne_prime (by decide) (hn ▸ dvd_mul_of_dvd_right d _) x hx
  subst c
  let m := 2^a*3^b
  have n : Nat.card G = 5*m := by rw [hn]; dsimp [m]; ring
  have d4 : 4 ∣ m := dvd_mul_of_dvd_left (pow_two_dvd (by omega : 2 ≤ a)) _
  have d2 : 2 ∣ m := (by decide : 2 ∣ 4).trans d4
  have d3 : 3 ∣ m := dvd_mul_of_dvd_right (dvd_pow_self 3 hb.ne') _
  have d6 : 6 ∣ m := (show Nat.Coprime 2 3 by decide).mul_dvd_of_dvd_of_dvd d2 d3
  have mpos : 0 < m := by dsimp [m]; positivity
  have mgt := Nat.le_of_dvd mpos d6
  have cop : Nat.Coprime 5 m := ((show Nat.Coprime 5 2 by decide).pow_right a).mul_right
    ((show Nat.Coprime 5 3 by decide).pow_right b)
  have hm : (Nat.card G).factorization 5 = 1 := by
    rw [n,Nat.factorization_mul (by decide) mpos.ne',Finsupp.add_apply,
      (show Nat.Prime 5 by decide).factorization, Nat.factorization_eq_zero_of_not_dvd
        ((show Nat.Prime 5 by decide).coprime_iff_not_dvd.mp cop)]
    simp
  have xn : x ≠ 1 := by rintro rfl; rw [cent_one,card_top] at hx; omega
  have m2 := cent_ne_prime Nat.prime_two (n ▸ dvd_mul_of_dvd_right d4 5 : 4 ∣ Nat.card G)
  have m3 := no_cent_three h ha hb (by decide : 0 < 1) hn
  have acc := prime_budget h (by decide : Nat.Prime 5) (by omega : 1 < m) cop n hm xn hx
    ({1,2,3,4,6} : Finset ℕ)
    (by simp only [mem_insert,mem_singleton]; rintro k (rfl|rfl|rfl|rfl|rfl);
        exacts [one_dvd _,d2,d3,d4,d6])
    (by simp only [mem_insert,mem_singleton]; rintro k (rfl|rfl|rfl|rfl|rfl);
        exacts [cent_ne_one,m2,m3,m4,m6])
  rw [sum_insert (by decide),sum_insert (by decide),sum_insert (by decide),
    sum_insert (by decide),sum_singleton,Nat.div_one,n] at acc
  have hu := sigma_two_primes Nat.prime_two Nat.prime_three (by decide) a b
  change 2*(∑ d ∈ m.divisors, d) < 6*m at hu
  omega

private theorem generator_of_small_squarefree_center (h : HasDistinctConjClassSizes G)
    {k : ℕ} (hk : k ∈ ({6,10,15} : Finset ℕ)) (x : G) (hn : k < Nat.card G)
    (hc : Nat.card (centralizer {x}) = k) : orderOf x = k := by
  classical
  by_contra hne
  have hn1 : orderOf x ≠ 1 := by
    intro he
    obtain rfl := orderOf_eq_one_iff.mp he
    rw [cent_one,card_top] at hc
    omega
  have od := card_dvd_of_le (self_le_cent x)
  rw [Nat.card_zpowers,hc] at od
  have table : ∀ j ∈ ({6,10,15} : Finset ℕ), ∀ d ∈ j.divisors, d ≠ 1 → d ≠ j →
      (j/d).Prime ∧ d.Coprime (j/d) := by decide
  have kpos : 0 < k := hc ▸ Nat.card_pos (α := centralizer ({x} : Set G))
  obtain ⟨hp,cp⟩ := table k hk (orderOf x) (Nat.mem_divisors.mpr ⟨od,kpos.ne'⟩) hn1 hne
  let : Fact (k / orderOf x).Prime := ⟨hp⟩
  obtain ⟨v,hv⟩ := exists_prime_orderOf_dvd_card' (G := centralizer ({x} : Set G))
    (k/orderOf x) (by rw [hc]; exact Nat.div_dvd_of_dvd od)
  have ho := (Subgroup.orderOf_coe v).trans hv
  have comm : Commute x (v : G) := (mem_centralizer_singleton_iff.mp v.property).symm
  let z := x*(v : G)
  have oz : orderOf z = k := by
    rw [show z=x*(v : G) from rfl, comm.orderOf_mul_eq_mul_orderOf_of_coprime (by rwa [ho]),
      ho,mul_comm,Nat.div_mul_cancel od]
  have hz : zpowers z = centralizer {x} := eq_of_le_of_card_ge
    (zpowers_le.mpr ((centralizer {x}).mul_mem (mem_centralizer_singleton_iff.mpr rfl) v.property))
    (by rw [Nat.card_zpowers,oz,hc])
  have hec : centralizer {z} = centralizer {x} := by
    refine le_antisymm ?_ (by rw [← hz]; exact self_le_cent z)
    rw [← centralizer_closure ({z} : Set G), ← zpowers_eq_closure, hz]
    exact centralizer_le (Set.singleton_subset_iff.mpr (mem_centralizer_singleton_iff.mpr rfl))
  have he : conjClassCard (ConjClasses.mk x) = conjClassCard (ConjClasses.mk z) := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := centralizer ({x} : Set G)))
    rw [class_mul_cent,← hec,class_mul_cent]
  obtain ⟨g,hg⟩ := isConj_iff.mp (mk_eq_mk_iff_isConj.mp (h he))
  have hzorder := (MulAut.conj g).orderOf_eq x
  change orderOf (g*x*g⁻¹) = orderOf x at hzorder
  rw [hg,oz] at hzorder
  exact hne hzorder.symm

/-- Centralizer of order four with Sylow two-subgroups of order eight. -/
def H1 : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [Nontrivial G] (a b c : ℕ),
    3 ≤ a → 0 < b → 0 < c → Nat.card G = 2^a*3^b*5^c → HasDistinctConjClassSizes G →
    a = 3 → (∃ x : G, Nat.card (centralizer ({x} : Set G)) = 4) → False

/-- Self-centralizing element of order six. -/
def H2 : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [Nontrivial G] (a b c : ℕ),
    3 ≤ a → 0 < b → 0 < c → Nat.card G = 2^a*3^b*5^c → HasDistinctConjClassSizes G →
    (∃ x : G, orderOf x = 6 ∧ Nat.card (centralizer ({x} : Set G)) = 6) → False

/-- Centralizer of order eight or nine. -/
def H3 : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [Nontrivial G] (a b c : ℕ),
    3 ≤ a → 0 < b → 0 < c → Nat.card G = 2^a*3^b*5^c → HasDistinctConjClassSizes G →
    (∃ x : G, Nat.card (centralizer ({x} : Set G)) ∈ ({8,9} : Finset ℕ)) → False

/-- Self-centralizing elements of orders ten and fifteen in the same group. -/
def H4 : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [Nontrivial G] (a b c : ℕ),
    3 ≤ a → 0 < b → 0 < c → Nat.card G = 2^a*3^b*5^c → HasDistinctConjClassSizes G →
    (∃ x : G, orderOf x = 10 ∧ Nat.card (centralizer ({x} : Set G)) = 10) →
    (∃ y : G, orderOf y = 15 ∧ Nat.card (centralizer ({y} : Set G)) = 15) → False

theorem main : H1 → H2 → H3 → H4 →
    OMA.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_solvable_R1.H2 := by
  intro core4 core6 core89 core1015 G _ _ _ hpr h
  obtain ⟨a,b,c,hn⟩ := order_factor (Nat.card G) Nat.card_pos.ne' hpr
  by_cases hc : c = 0
  · subst c
    simp only [pow_zero, mul_one] at hn
    exact two_three_order h hn
  have hb : b ≠ 0 := by
    rintro rfl
    simp only [pow_zero, mul_one] at hn
    exact no_two_five h hn
  have h7 : (Nat.card G).Coprime 7 := by
    apply Nat.Coprime.symm
    apply (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 7)).mpr
    intro hd
    have := hpr 7 (by decide) hd
    omega
  have d5 : 5 ∣ Nat.card G := hn ▸ dvd_mul_of_dvd_right (dvd_pow_self 5 hc) _
  obtain ⟨g,hg⟩ := order_multiple_four_of_five h h7 d5
  have og : orderOf (g^(orderOf g / 4)) = 4 := by
    rw [orderOf_pow_of_dvd (Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd hg) (orderOf_pos g)).ne'
      (Nat.div_dvd_of_dvd hg), Nat.div_div_self hg (orderOf_pos g).ne']
  have d8 := order_totient_dvd h (g^(orderOf g / 4))
  rw [og, show Nat.totient 4 = 2 by decide] at d8
  change 8 ∣ Nat.card G at d8
  have d4 := (show 4 ∣ 8 by decide).trans d8
  have ha : 3 ≤ a := by
    have co : Nat.Coprime 8 (3^b*5^c) :=
      ((show Nat.Coprime 8 3 by decide).pow_right b).mul_right
        ((show Nat.Coprime 8 5 by decide).pow_right c)
    rw [hn, mul_assoc] at d8
    have := co.dvd_of_dvd_mul_right d8
    by_contra! ht
    interval_cases a <;> norm_num at *
  apply False.elim
  have nlarge : 15 < Nat.card G := by
    have da : 8 ≤ 2^a := Nat.pow_le_pow_right (by decide : 0 < 2) ha
    have db : 3 ≤ 3^b := Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 1 ≤ b)
    have dc : 5 ≤ 5^c := Nat.pow_le_pow_right (by decide : 0 < 5) (by omega : 1 ≤ c)
    have := Nat.mul_le_mul (Nat.mul_le_mul da db) dc
    omega
  have gen {k : ℕ} (hk : k ∈ ({6,10,15} : Finset ℕ)) {x : G}
      (he : Nat.card (centralizer {x}) = k) : orderOf x = k := by
    refine generator_of_small_squarefree_center h hk x ?_ he
    simp only [mem_insert,mem_singleton] at hk
    omega
  have restrict4 (x : G) (hx : Nat.card (centralizer {x}) = 4) : a = 3 := by
    by_contra he
    exact no_cent_four h (by omega : 4 ≤ a) (by positivity : 0 < 3^b*5^c)
      (((show Nat.Coprime 2 3 by decide).pow_right b).mul_right
        ((show Nat.Coprime 2 5 by decide).pow_right c))
      (by rwa [← mul_assoc]) x hx
  obtain ⟨x,hx⟩ | hp := small_centers h hn d4
  · simp only [mem_insert,mem_singleton] at hx
    rcases hx with h3 | h4 | h5 | hsmall
    · exact (no_cent_three h ha (by omega) (by omega) hn x h3).elim
    · exact core4 G a b c ha (by omega) (by omega) hn h (restrict4 x h4) ⟨x,h4⟩
    · obtain ⟨y,hy⟩ | ⟨y,hy⟩ := four_or_six_of_cent_five h ha (by omega) (by omega) hn x h5
      · exact core4 G a b c ha (by omega) (by omega) hn h (restrict4 y hy) ⟨y,hy⟩
      · exact core6 G a b c ha (by omega) (by omega) hn h ⟨y,gen (by decide) hy,hy⟩
    · rcases hsmall with h6 | h89
      · exact core6 G a b c ha (by omega) (by omega) hn h ⟨x,gen (by decide) h6,h6⟩
      · exact core89 G a b c ha (by omega) (by omega) hn h ⟨x,by simpa only [mem_insert,mem_singleton] using h89⟩
  · obtain ⟨⟨x,hx⟩,⟨y,hy⟩⟩ := hp
    exact core1015 G a b c ha (by omega) (by omega) hn h
      ⟨x,gen (by decide) hx,hx⟩ ⟨y,gen (by decide) hy,hy⟩

end OMA.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_solvable_R1_H2_R1
