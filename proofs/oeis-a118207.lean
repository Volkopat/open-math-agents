import OMAStatements.S_oeis_a118207
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The Möbius sum over square divisors, in a form suited to regrouping finite products. -/
namespace CyclotomicLiouville

open Finset ArithmeticFunction
open scoped ArithmeticFunction

def sign (n : ℕ) : ℤ := (-1) ^ n.primeFactorsList.length

theorem sign_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    sign (m * n) = sign m * sign n := by
  unfold sign
  rw [(Nat.perm_primeFactorsList_mul hm hn).length_eq, List.length_append, pow_add]

theorem sign_sq {n : ℕ} (hn : n ≠ 0) : sign (n ^ 2) = 1 := by
  rw [pow_two, sign_mul hn hn, ← pow_two]
  unfold sign
  rw [← pow_mul, mul_comm _ 2, pow_mul]
  norm_num

theorem sign_two_mul {n : ℕ} (hn : n ≠ 0) : sign (2 * n) = -sign n := by
  rw [sign_mul (by decide : (2 : ℕ) ≠ 0) hn]
  have h : sign 2 = -1 := by
    simp [sign, Nat.primeFactorsList_prime Nat.prime_two]
  simp [h]

private theorem factorization_injective {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a.factorization = b.factorization) : a = b := by
  rw [← Nat.factorization_prod_pow_eq_self ha, h, Nat.factorization_prod_pow_eq_self hb]

theorem squarefree_square_unique {a b c d : ℕ}
    (ha : Squarefree a) (hc : Squarefree c) (hb : b ≠ 0) (hd : d ≠ 0)
    (eq : b ^ 2 * a = d ^ 2 * c) : a = c ∧ b = d := by
  have hf (p : ℕ) :
      2 * b.factorization p + a.factorization p =
        2 * d.factorization p + c.factorization p := by
    have e := congrArg (fun z : ℕ => z.factorization p) eq
    simpa only [Nat.factorization_mul (pow_ne_zero _ hb) ha.ne_zero,
      Nat.factorization_mul (pow_ne_zero _ hd) hc.ne_zero,
      Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul, Nat.cast_id] using e
  constructor
  · apply factorization_injective ha.ne_zero hc.ne_zero
    ext p
    have := hf p
    have := ha.natFactorization_le_one p
    have := hc.natFactorization_le_one p
    omega
  · apply factorization_injective hb hd
    ext p
    have := hf p
    have := ha.natFactorization_le_one p
    have := hc.natFactorization_le_one p
    omega

def squarePairs (N m : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 N) ×ˢ (Icc 1 N)).filter fun p => p.2 ^ 2 * p.1 = m

theorem sum_moebius_squarePairs {N m : ℕ} (hm : 0 < m) (hle : m ≤ N) :
    ∑ p ∈ squarePairs N m, ArithmeticFunction.moebius p.1 = sign m := by
  obtain ⟨a, b, ha, hb, eq, sf⟩ := Nat.sq_mul_squarefree_of_pos hm
  have am : a ≤ m := Nat.le_of_dvd hm ⟨b ^ 2, by rw [← eq, mul_comm]⟩
  have bm : b ≤ m := Nat.le_of_dvd hm ⟨b * a, by rw [← eq, pow_two, mul_assoc]⟩
  have inPairs : (a,b) ∈ squarePairs N m := by
    exact mem_filter.2 ⟨mem_product.2
      ⟨mem_Icc.2 ⟨ha,am.trans hle⟩,mem_Icc.2 ⟨hb,bm.trans hle⟩⟩,eq⟩
  rw [sum_eq_single_of_mem (a,b) inPairs]
  · rw [moebius_apply_of_squarefree sf, cardFactors_apply, ← eq,
      sign_mul (pow_ne_zero _ hb.ne') ha.ne', sign_sq hb.ne', one_mul]
    rfl
  · rintro ⟨c,d⟩ hin hneq
    rcases mem_filter.mp hin with ⟨hpair,hdc⟩
    have hd0 : 0 < d := (mem_Icc.1 (mem_product.1 hpair).2).1
    have hd : d ≠ 0 := hd0.ne'
    apply moebius_eq_zero_of_not_squarefree
    intro hsf
    obtain ⟨rfl,rfl⟩ := squarefree_square_unique hsf sf hd hb.ne' (hdc.trans eq.symm)
    exact hneq rfl

end CyclotomicLiouville

/-! Cyclotomic factorization evaluated at a nilpotent element. -/
namespace CyclotomicLiouville

open Finset Polynomial ArithmeticFunction
open scoped ArithmeticFunction

noncomputable def normalized (n : ℕ) : ℚ[X] :=
  if n = 1 then -cyclotomic n ℚ else cyclotomic n ℚ

theorem prod_normalized {n : ℕ} (hn : n ≠ 0) :
    ∏ d ∈ n.divisors, normalized d = 1 - (X : ℚ[X]) ^ n := by
  classical
  have hit := Nat.one_mem_divisors.2 hn
  have rest :
      ∏ d ∈ n.divisors.erase 1, normalized d = ∏ d ∈ n.divisors.erase 1, cyclotomic d ℚ := by
    apply prod_congr rfl
    intro d hd
    simp [normalized, (mem_erase.1 hd).1]
  rw [← prod_erase_mul _ _ hit, rest, normalized, if_pos rfl, mul_neg,
    prod_erase_mul _ _ hit, prod_cyclotomic_eq_X_pow_sub_one (Nat.pos_of_ne_zero hn), neg_sub]

section Units

variable {R : Type*} [CommRing R] [Algebra ℚ R]

omit [Algebra ℚ R] in
private theorem nilpotent_pow (z : R) (hz : IsNilpotent z) {n : ℕ} (hn : n ≠ 0) :
    IsNilpotent (z ^ n) := by
  obtain ⟨k, hk⟩ := hz
  exact ⟨k, by rw [pow_right_comm, hk, zero_pow hn]⟩

omit [Algebra ℚ R] in
private theorem minus_isUnit (z : R) (hz : IsNilpotent z) {n : ℕ} (hn : n ≠ 0) :
    IsUnit (1 - z ^ n) :=
  (nilpotent_pow z hz hn).isUnit_one_sub

private theorem normalized_isUnit (z : R) (hz : IsNilpotent z) {n : ℕ} (hn : n ≠ 0) :
    IsUnit (aeval z (normalized n)) := by
  have h := Finset.dvd_prod_of_mem (fun d => aeval z (normalized d)) (Nat.mem_divisors_self n hn)
  rw [← map_prod, prod_normalized hn, map_sub, map_one, aeval_X_pow] at h
  obtain ⟨t,ht⟩ := h
  have unit := minus_isUnit z hz hn
  rw [ht] at unit
  exact isUnit_of_mul_isUnit_left unit

noncomputable def minusUnit (z : R) (hz : IsNilpotent z) (n : ℕ) : Rˣ :=
  if hn : n ≠ 0 then (minus_isUnit z hz hn).unit else 1

noncomputable def cycloUnit (z : R) (hz : IsNilpotent z) (n : ℕ) : Rˣ :=
  if hn : n ≠ 0 then (normalized_isUnit z hz hn).unit else 1

omit [Algebra ℚ R] in
theorem minusUnit_val (z : R) (hz : IsNilpotent z) {n : ℕ} (hn : n ≠ 0) :
    ((minusUnit z hz n : Rˣ) : R) = 1 - z ^ n := by
  rw [minusUnit, dif_pos hn, IsUnit.unit_spec]

theorem cycloUnit_val (z : R) (hz : IsNilpotent z) {n : ℕ} (hn : n ≠ 0) :
    ((cycloUnit z hz n : Rˣ) : R) = aeval z (normalized n) := by
  rw [cycloUnit, dif_pos hn, IsUnit.unit_spec]

private theorem cyclo_divisor_product (z : R) (hz : IsNilpotent z) {n : ℕ} (hn : n ≠ 0) :
    ∏ d ∈ n.divisors, cycloUnit z hz d = minusUnit z hz n := by
  apply Units.ext
  rw [minusUnit_val z hz hn]
  change Units.coeHom R (∏ d ∈ n.divisors, cycloUnit z hz d) = _
  rw [map_prod]
  simp only [Units.coeHom_apply]
  calc
    _ = ∏ d ∈ n.divisors, aeval z (normalized d) := by
      exact prod_congr rfl fun d hd => cycloUnit_val z hz (Nat.pos_of_mem_divisors hd).ne'
    _ = 1 - z ^ n := by rw [← map_prod, prod_normalized hn, map_sub, map_one, aeval_X_pow]

theorem cyclo_moebius (z : R) (hz : IsNilpotent z) {n : ℕ} (hn : 0 < n) :
    cycloUnit z hz n =
      ∏ p ∈ n.divisorsAntidiagonal, minusUnit z hz p.2 ^ ArithmeticFunction.moebius p.1 := by
  exact ((prod_eq_iff_prod_pow_moebius_eq).1
    (fun m hm => cyclo_divisor_product z hz hm.ne') n hn).symm

omit [Algebra ℚ R] in
theorem minusUnit_pow (z : R) (hz : IsNilpotent z) {n d : ℕ} (hn : n ≠ 0) (hd : d ≠ 0) :
    minusUnit (z ^ n) (nilpotent_pow z hz hn) d = minusUnit z hz (n * d) := by
  apply Units.ext
  rw [minusUnit_val _ _ hd, minusUnit_val _ _ (mul_ne_zero hn hd), pow_mul]

omit [Algebra ℚ R] in
theorem minusUnit_one_of_zero (z : R) (hz : IsNilpotent z) {m : ℕ} (hm : m ≠ 0)
    (zero : z ^ m = 0) : minusUnit z hz m = 1 := by
  apply Units.ext
  simp only [minusUnit_val z hz hm, zero, sub_zero, Units.val_one]

omit [Algebra ℚ R] in
private theorem pow_eq_zero_above (z : R) {N m : ℕ} (h : z ^ (N + 1) = 0)
    (hm : N < m) : z ^ m = 0 := by
  obtain ⟨k,hk⟩ : ∃ k, m = (N + 1) + k := ⟨m - (N + 1),by omega⟩
  rw [hk, pow_add,h,zero_mul]

private theorem combine_powers {G I : Type*} [CommGroup G] (s : Finset I) (g : G) (e : I → ℤ) :
    ∏ i ∈ s, g ^ e i = g ^ (∑ i ∈ s, e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [prod_insert hi,sum_insert hi,ih,zpow_add]

private def indexBox (N : ℕ) : Finset (ℕ × ℕ) := Icc 1 N ×ˢ Icc 1 N

private def multiplyCut (N : ℕ) : Finset (ℕ × ℕ) :=
  (indexBox N).filter fun p => p.1 * p.2 ≤ N

private def squareCut (N : ℕ) : Finset (ℕ × ℕ) :=
  (indexBox N).filter fun p => p.2 ^ 2 * p.1 ≤ N

private theorem antidiagonal_pack {G : Type*} [CommMonoid G] (N : ℕ) (f : ℕ × ℕ → G) :
    ∏ n ∈ Icc 1 N, ∏ p ∈ n.divisorsAntidiagonal, f p =
      ∏ p ∈ multiplyCut N, f p := by
  classical
  rw [prod_sigma']
  refine prod_bij (fun p _ => p.2) ?_ ?_ ?_ ?_
  · rintro ⟨n,a,b⟩ h
    obtain ⟨hin, hab⟩ := mem_sigma.1 h
    obtain ⟨eq,hn⟩ := Nat.mem_divisorsAntidiagonal.1 hab
    change a * b = n at eq
    change n ≠ 0 at hn
    have hN := (mem_Icc.1 hin).2
    change n ≤ N at hN
    have ap : 0 < a := Nat.pos_of_ne_zero (fun ha => hn (by rw [← eq, ha, zero_mul]))
    have bp : 0 < b := Nat.pos_of_ne_zero (fun hb => hn (by rw [← eq, hb, mul_zero]))
    have ha : a ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) ⟨b,eq.symm⟩
    have hb : b ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) ⟨a,by rw [← eq,mul_comm]⟩
    exact mem_filter.2 ⟨mem_product.2 ⟨mem_Icc.2 ⟨ap,ha.trans hN⟩,
      mem_Icc.2 ⟨bp,hb.trans hN⟩⟩,eq ▸ hN⟩
  · rintro ⟨n,p⟩ h ⟨m,q⟩ h' eq
    change p = q at eq
    subst q
    have en := (Nat.mem_divisorsAntidiagonal.1 (mem_sigma.1 h).2).1
    have em := (Nat.mem_divisorsAntidiagonal.1 (mem_sigma.1 h').2).1
    have same : n = m := en.symm.trans em
    subst m
    rfl
  · rintro ⟨a,b⟩ h
    obtain ⟨hbox,hN⟩ := mem_filter.1 h
    obtain ⟨ha,hb⟩ := mem_product.1 hbox
    have hp : 0 < a * b := Nat.mul_pos (mem_Icc.1 ha).1 (mem_Icc.1 hb).1
    exact ⟨⟨a*b,(a,b)⟩,mem_sigma.2
      ⟨mem_Icc.2 ⟨hp,hN⟩,Nat.mem_divisorsAntidiagonal.2 ⟨rfl,hp.ne'⟩⟩,rfl⟩
  · intro p hp
    rfl

private theorem squareCut_subset (N : ℕ) : squareCut N ⊆ multiplyCut N := by
  intro p h
  obtain ⟨hbox,hN⟩ := mem_filter.1 h
  have hp : 0 < p.2 := (mem_Icc.1 (mem_product.1 hbox).2).1
  exact mem_filter.2 ⟨hbox,by nlinarith⟩

noncomputable def diagonalUnit (z : R) (hz : IsNilpotent z) (n : ℕ) : Rˣ :=
  if hn : n ≠ 0 then cycloUnit (z ^ n) (nilpotent_pow z hz hn) n else 1

theorem diagonalUnit_val (z : R) (hz : IsNilpotent z) {n : ℕ} (hn : n ≠ 0) :
    ((diagonalUnit z hz n : Rˣ) : R) = aeval (z ^ n) (normalized n) := by
  rw [diagonalUnit,dif_pos hn,cycloUnit_val _ _ hn]

theorem cyclos_as_sign (z : R) (hz : IsNilpotent z) {N : ℕ} (h : z ^ (N + 1) = 0) :
    ∏ n ∈ Icc 1 N, diagonalUnit z hz n = ∏ m ∈ Icc 1 N, minusUnit z hz m ^ sign m := by
  classical
  let index (p : ℕ × ℕ) := p.2 ^ 2 * p.1
  let f (p : ℕ × ℕ) := minusUnit z hz (index p) ^ ArithmeticFunction.moebius p.1
  have one (n : ℕ) (hn : n ∈ Icc 1 N) :
      diagonalUnit z hz n = ∏ p ∈ n.divisorsAntidiagonal, f p := by
    have hp : 0 < n := (mem_Icc.1 hn).1
    rw [diagonalUnit,dif_pos hp.ne',cyclo_moebius _ _ hp]
    apply prod_congr rfl
    intro p hpa
    have pd : 0 < p.2 := Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hpa)
    rw [minusUnit_pow z hz hp.ne' pd.ne']
    unfold f index
    have eq := (Nat.mem_divisorsAntidiagonal.1 hpa).1
    rw [show n * p.2 = p.2 ^ 2 * p.1 by rw [← eq]; ring]
  have fibre (m : ℕ) (hm : m ≤ N) : (squareCut N).filter (fun p => index p = m) = squarePairs N m := by
    ext p
    simp only [squareCut, squarePairs,indexBox,index,mem_filter]
    constructor
    · rintro ⟨⟨hbox,_⟩,eq⟩
      exact ⟨hbox,eq⟩
    · rintro ⟨hbox,eq⟩
      exact ⟨⟨hbox,eq ▸ hm⟩,eq⟩
  have target (p : ℕ × ℕ) (hp : p ∈ squareCut N) : index p ∈ Icc 1 N := by
    obtain ⟨hbox,hN⟩ := mem_filter.1 hp
    obtain ⟨ha,hb⟩ := mem_product.1 hbox
    have ap : 0 < p.1 := (mem_Icc.1 ha).1
    have bp : 0 < p.2 := (mem_Icc.1 hb).1
    exact mem_Icc.2 ⟨Nat.mul_pos (pow_pos bp _) ap,hN⟩
  calc
    _ = ∏ n ∈ Icc 1 N, ∏ p ∈ n.divisorsAntidiagonal, f p := prod_congr rfl one
    _ = ∏ p ∈ multiplyCut N, f p := antidiagonal_pack _ _
    _ = ∏ p ∈ squareCut N, f p := by
      symm
      apply prod_subset (squareCut_subset N)
      intro p hin hmiss
      have large : N < index p := by
        by_contra! hsmall
        exact hmiss (mem_filter.2 ⟨(mem_filter.1 hin).1,hsmall⟩)
      simp [f,minusUnit_one_of_zero z hz (by omega : index p ≠ 0) (pow_eq_zero_above z h large)]
    _ = ∏ m ∈ Icc 1 N, ∏ p ∈ (squareCut N).filter (fun p => index p = m), f p :=
      (prod_fiberwise_of_maps_to target f).symm
    _ = _ := by
      apply prod_congr rfl
      intro m hm
      have ⟨mp,mb⟩ := mem_Icc.1 hm
      rw [fibre m mb]
      calc
        _ = ∏ p ∈ squarePairs N m, minusUnit z hz m ^ ArithmeticFunction.moebius p.1 := by
          apply prod_congr rfl
          intro p hp
          have eq : index p = m := (mem_filter.1 hp).2
          simp only [f,eq]
        _ = _ := by rw [combine_powers,sum_moebius_squarePairs mp mb]

private theorem prod_even_reindex {G : Type*} [CommMonoid G] (N : ℕ) (f : ℕ → G)
    (zero : ∀ n, N < n → f n = 1) :
    ∏ n ∈ Icc 1 N, (if Even n then f n else 1) = ∏ n ∈ Icc 1 N, f (2 * n) := by
  classical
  let base := Icc 1 N
  let s := base.filter (fun j => 2*j ≤ N)
  rw [← prod_filter]
  calc
    _ = ∏ n ∈ s, f (2 * n) := by
      symm
      refine prod_bij (fun j _ => 2*j) ?_ ?_ ?_ ?_
      · intro j hj
        obtain ⟨hit,le⟩ := mem_filter.1 hj
        have pos := (mem_Icc.1 hit).1
        change 2*j ∈ (Icc 1 N).filter Even
        exact mem_filter.2 ⟨mem_Icc.2 ⟨by omega, le⟩,⟨j,by omega⟩⟩
      · intro a ha b hb eq
        change 2*a = 2*b at eq
        omega
      · intro n hn
        obtain ⟨hmem,⟨j,eq⟩⟩ := mem_filter.1 hn
        have ⟨hp, hl⟩ := mem_Icc.1 hmem
        have hit : j ∈ s := mem_filter.2 ⟨mem_Icc.2 ⟨by omega,by omega⟩,by omega⟩
        refine ⟨j,hit,?_⟩
        change 2*j = n
        omega
      · intros
        rfl
    _ = _ := by
      apply prod_subset (filter_subset _ _)
      intro j hj hs
      have notBound : ¬ 2*j ≤ N := fun le => hs (mem_filter.2 ⟨hj,le⟩)
      exact zero (2*j) (Nat.lt_of_not_ge notBound)

omit [Algebra ℚ R] in
private theorem plus_isUnit (z : R) (hz : IsNilpotent z) {n : ℕ} (hn : n ≠ 0) :
    IsUnit (1 + z ^ n) := by
  simpa only [sub_neg_eq_add] using (nilpotent_pow z hz hn).neg.isUnit_one_sub

noncomputable def plusUnit (z : R) (hz : IsNilpotent z) (n : ℕ) : Rˣ :=
  if hn : n ≠ 0 then (plus_isUnit z hz hn).unit else 1

omit [Algebra ℚ R] in
theorem plusUnit_val (z : R) (hz : IsNilpotent z) {n : ℕ} (hn : n ≠ 0) :
    ((plusUnit z hz n : Rˣ) : R) = 1 + z ^ n := by
  rw [plusUnit, dif_pos hn, IsUnit.unit_spec]

private theorem plusUnit_mul_minus (z : R) (hz : IsNilpotent z) {n : ℕ} (hn : n ≠ 0) :
    plusUnit z hz n * minusUnit z hz n = minusUnit z hz (2*n) := by
  apply Units.ext
  rw [Units.val_mul,plusUnit_val z hz hn,minusUnit_val z hz hn,minusUnit_val _ _ (by omega),
    mul_comm 2 n,pow_mul]
  ring

omit [Algebra ℚ R] in
private theorem minusUnit_neg_even (z : R) (hz : IsNilpotent z) {n : ℕ} (hn : n ≠ 0) (he : Even n) :
    minusUnit (-z) hz.neg n = minusUnit z hz n := by
  apply Units.ext
  rw [minusUnit_val _ _ hn,minusUnit_val _ _ hn,he.neg_pow]

private theorem minusUnit_neg_odd (z : R) (hz : IsNilpotent z) {n : ℕ} (hn : n ≠ 0) (ho : Odd n) :
    minusUnit (-z) hz.neg n = plusUnit z hz n := by
  apply Units.ext
  rw [minusUnit_val _ _ hn,plusUnit_val _ _ hn,ho.neg_pow,sub_neg_eq_add]

/-- The product at opposite arguments becomes the plus-sign product at squared arguments. -/
theorem sign_products_pair (z : R) (hz : IsNilpotent z) {N : ℕ} (h : z ^ (N + 1) = 0) :
    (∏ n ∈ Icc 1 N, minusUnit z hz n ^ sign n) *
      (∏ n ∈ Icc 1 N, minusUnit (-z) hz.neg n ^ sign n) =
      ∏ n ∈ Icc 1 N, plusUnit z hz (2*n) ^ sign n := by
  classical
  let s := Icc 1 N
  let b (n : ℕ) := minusUnit z hz (2*n)
  have vanish (n : ℕ) (hn : N < n) : minusUnit z hz n = 1 :=
    minusUnit_one_of_zero z hz (by omega) (pow_eq_zero_above z h hn)
  have paired :
      (∏ n ∈ s, minusUnit z hz n ^ sign n) * (∏ n ∈ s, minusUnit (-z) hz.neg n ^ sign n) =
        (∏ n ∈ s, (if Even n then minusUnit z hz n ^ (sign n + sign n) else 1)) *
          ∏ n ∈ s, (if Even n then 1 else b n ^ sign n) := by
    rw [← prod_mul_distrib,← prod_mul_distrib]
    apply prod_congr rfl
    intro n hn
    have nz : n ≠ 0 := Nat.ne_of_gt (mem_Icc.1 hn).1
    by_cases e : Even n
    · rw [minusUnit_neg_even z hz nz e,zpow_add]
      simp [e]
    · have o : Odd n := Nat.not_even_iff_odd.1 e
      rw [minusUnit_neg_odd z hz nz o,← mul_zpow,mul_comm,plusUnit_mul_minus z hz nz]
      simp [e,b]
  have evenFactors :
      (∏ n ∈ s, (if Even n then minusUnit z hz n ^ (sign n + sign n) else 1)) =
        ∏ n ∈ s, b n ^ (-sign n + -sign n) := by
    change (∏ n ∈ Icc 1 N, (if Even n then minusUnit z hz n ^ (sign n + sign n) else 1)) = _
    rw [prod_even_reindex N (fun n => minusUnit z hz n ^ (sign n + sign n))
      (fun n hn => by
        change minusUnit z hz n ^ (sign n + sign n) = 1
        rw [vanish n hn,one_zpow])]
    exact prod_congr rfl fun n hn => by rw [sign_two_mul (Nat.ne_of_gt (mem_Icc.1 hn).1)]
  have plus_split :
      (∏ n ∈ s, plusUnit z hz (2*n) ^ sign n) =
        (∏ n ∈ s, b (2*n) ^ sign n) * ∏ n ∈ s, b n ^ (-sign n) := by
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro n hn
    have nz := Nat.ne_of_gt (mem_Icc.1 hn).1
    have eq : plusUnit z hz (2*n) = b (2*n) * (b n)⁻¹ :=
      eq_mul_inv_iff_mul_eq.2 (plusUnit_mul_minus z hz (mul_ne_zero (by decide) nz))
    rw [eq,mul_zpow,inv_zpow,zpow_neg]
  have plusEven :
      (∏ n ∈ s, b (2*n) ^ sign n) =
        ∏ n ∈ s, (if Even n then b n ^ (-sign n) else 1) := by
    symm
    change (∏ n ∈ Icc 1 N, (if Even n then b n ^ (-sign n) else 1)) = _
    rw [prod_even_reindex N (fun n => b n ^ (-sign n))
      (fun n hn => by simp [b,vanish (2*n) (by omega : N < 2*n)])]
    exact prod_congr rfl fun n hn => by rw [sign_two_mul (Nat.ne_of_gt (mem_Icc.1 hn).1),neg_neg]
  change (∏ n ∈ s, minusUnit z hz n ^ sign n) * (∏ n ∈ s, minusUnit (-z) hz.neg n ^ sign n) =
    ∏ n ∈ s, plusUnit z hz (2*n) ^ sign n
  rw [paired,evenFactors,plus_split,plusEven,← prod_mul_distrib,← prod_mul_distrib]
  apply prod_congr rfl
  intro n hn
  by_cases e : Even n
  · simp [e,zpow_add]
  · simp only [e,if_false,one_mul,← zpow_add]
    rw [show -sign n + -sign n + sign n = -sign n by omega]

end Units

end CyclotomicLiouville

/-! Bala's conjecture on OEIS A118207, as a polynomial divisibility at every truncation. -/
namespace CyclotomicLiouville

open Finset Polynomial

noncomputable def positiveFactors (N : ℕ) : ℚ[X] :=
  ∏ j ∈ range N, if Even (j+1).primeFactorsList.length then 1 + X^(2*(j+1)) else 1

noncomputable def negativeFactors (N : ℕ) : ℚ[X] :=
  ∏ j ∈ range N, if Odd (j+1).primeFactorsList.length then 1 + X^(2*(j+1)) else 1

noncomputable def pairedFactors (N : ℕ) : ℚ[X] :=
  ∏ j ∈ range N, (cyclotomic (j+1) ℚ).comp (X^(j+1)) *
    (cyclotomic (j+1) ℚ).comp ((-X)^(j+1))

private noncomputable def cut (N : ℕ) : Ideal ℚ[X] := Ideal.span {(X : ℚ[X]) ^ (N + 1)}

private noncomputable def project (N : ℕ) : ℚ[X] →+* ℚ[X] ⧸ cut N :=
  Ideal.Quotient.mk (cut N)

private theorem project_comp (N : ℕ) (p q : ℚ[X]) :
    project N (p.comp q) = aeval (project N q) p := by
  unfold Polynomial.comp
  rw [Polynomial.hom_eval₂]
  rfl

private theorem prod_range_as_Icc {G : Type*} [CommMonoid G] (N : ℕ) (f : ℕ → G) :
    ∏ j ∈ range N, f (j+1) = ∏ n ∈ Icc 1 N, f n := by
  refine prod_bij (fun j _ => j+1) ?_ ?_ ?_ ?_
  · intro j h
    have hj := mem_range.1 h
    change j + 1 ∈ Icc 1 N
    exact mem_Icc.2 ⟨by omega,by omega⟩
  · intro j _ k _ eq
    change j + 1 = k + 1 at eq
    omega
  · intro n h
    have ⟨lo,hi⟩ := mem_Icc.1 h
    refine ⟨n-1,mem_range.2 (by omega),?_⟩
    change n - 1 + 1 = n
    omega
  · intros
    rfl

private theorem pair_normalized (n : ℕ) :
    (normalized n).comp (X^n) * (normalized n).comp ((-X)^n) =
      (cyclotomic n ℚ).comp (X^n) * (cyclotomic n ℚ).comp ((-X)^n) := by
  by_cases h : n = 1
  · simp [normalized,h,neg_comp]
    ring
  · simp [normalized,h]

private theorem clear_signs {G : Type*} [CommGroup G] (s : Finset ℕ) (f : ℕ → G) :
    (∏ n ∈ s, if Odd n.primeFactorsList.length then f n else 1) *
      (∏ n ∈ s, f n ^ sign n) =
      ∏ n ∈ s, if Even n.primeFactorsList.length then f n else 1 := by
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro n _
  by_cases h : Even n.primeFactorsList.length
  · have hn := Nat.not_odd_iff_even.2 h
    simp [hn,h,sign,h.neg_one_pow]
  · have odd := Nat.not_even_iff_odd.1 h
    simp [h,odd,sign,odd.neg_one_pow]

theorem main (N : ℕ) : (X : ℚ[X]) ^ (N + 1) ∣
    positiveFactors N - negativeFactors N * pairedFactors N := by
  classical
  let R := ℚ[X] ⧸ cut N
  let ρ : ℚ[X] →+* R := project N
  let z := ρ X
  have zero : z ^ (N+1) = 0 := by
    change ρ X ^ (N+1) = 0
    rw [← map_pow]
    exact (Ideal.Quotient.eq_zero_iff_mem).2
      (Ideal.subset_span (Set.mem_singleton _))
  let hz : IsNilpotent z := ⟨N+1,zero⟩
  have negZero : (-z) ^ (N+1) = 0 := by
    calc
      _ = ((-1 : R) * z) ^ (N+1) := congrArg (fun t : R => t ^ (N+1)) (neg_one_mul z).symm
      _ = _ := by rw [mul_pow,zero,mul_zero]
  let s := Icc 1 N
  let f (n : ℕ) := plusUnit z hz (2*n)
  have flip :
      ((∏ n ∈ s, diagonalUnit z hz n) * ∏ n ∈ s, diagonalUnit (-z) hz.neg n) =
        ∏ n ∈ s, f n ^ sign n := by
    change ((∏ n ∈ Icc 1 N, diagonalUnit z hz n) *
      ∏ n ∈ Icc 1 N, diagonalUnit (-z) hz.neg n) = _
    rw [cyclos_as_sign z hz zero,cyclos_as_sign (-z) hz.neg negZero]
    exact sign_products_pair z hz zero
  have pairVal :
      Units.coeHom R ((∏ n ∈ s, diagonalUnit z hz n) * ∏ n ∈ s, diagonalUnit (-z) hz.neg n) =
        ρ (pairedFactors N) := by
    rw [← prod_mul_distrib, map_prod]
    unfold pairedFactors
    rw [prod_range_as_Icc N (fun n => (cyclotomic n ℚ).comp (X^n) *
      (cyclotomic n ℚ).comp ((-X)^n)),map_prod]
    apply prod_congr rfl
    intro n hn
    have nz : n ≠ 0 := Nat.ne_of_gt (mem_Icc.1 hn).1
    simp only [Units.coeHom_apply, Units.val_mul, diagonalUnit_val _ _ nz]
    have zp : z ^ n = ρ (X ^ n) := (map_pow ρ X n).symm
    have zq : (-z) ^ n = ρ ((-X) ^ n) := by rw [map_pow,map_neg]
    rw [zp,zq,← project_comp,← project_comp,← map_mul,pair_normalized]
  have plusVal (n : ℕ) (hn : n ∈ s) :
      Units.coeHom R (f n) = ρ (1 + X ^ (2*n)) := by
    have nz : n ≠ 0 := Nat.ne_of_gt (mem_Icc.1 hn).1
    simp only [f, Units.coeHom_apply, plusUnit_val _ _ (by omega : 2*n ≠ 0),
      map_add,map_one,map_pow,z]
  have negVal :
      Units.coeHom R (∏ n ∈ s, if Odd n.primeFactorsList.length then f n else 1) =
        ρ (negativeFactors N) := by
    unfold negativeFactors
    rw [prod_range_as_Icc N (fun n => if Odd n.primeFactorsList.length
      then 1 + (X : ℚ[X])^(2*n) else 1),map_prod,map_prod]
    apply prod_congr rfl
    intro n hn
    by_cases e : Odd n.primeFactorsList.length <;> simp [e,plusVal n hn]
  have posVal :
      Units.coeHom R (∏ n ∈ s, if Even n.primeFactorsList.length then f n else 1) =
        ρ (positiveFactors N) := by
    unfold positiveFactors
    rw [prod_range_as_Icc N (fun n => if Even n.primeFactorsList.length
      then 1 + (X : ℚ[X])^(2*n) else 1),map_prod,map_prod]
    apply prod_congr rfl
    intro n hn
    by_cases e : Even n.primeFactorsList.length <;> simp [e,plusVal n hn]
  have eq := congrArg (Units.coeHom R) (clear_signs s f)
  rw [← flip,map_mul,negVal,pairVal,posVal] at eq
  apply Ideal.mem_span_singleton.1
  apply (Ideal.Quotient.eq_zero_iff_mem).1
  change ρ _ = 0
  rw [map_sub,map_mul,eq,sub_self]

end CyclotomicLiouville

theorem OMA.solution : type_of% @OMA.S_oeis_a118207.main :=
  CyclotomicLiouville.main
