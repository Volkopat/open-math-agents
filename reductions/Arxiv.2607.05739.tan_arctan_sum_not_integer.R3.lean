import FormalConjectures.Arxiv.«2607.05739».TanArctanSum

/-! A shrinking interval for integral values of the arctangent sum.

For the complementary angle sum Phi(n), the normalized constant c is the
limit of Phi(n) minus log n. Ono's Proposition 3.2 locates exceptional
indices up to a bounded additive error near exp(j*pi/2-c). At an actual
integer value the signed reciprocal quotient gives a much smaller angular
displacement. An explicit summable correction to log(n+1/2) then puts the
exponential scale within 2/n² of n+1/2+5/(24n), on a specified side of the
half integer. Its floor recovers the unique candidate directly.

Signed residues and Cilleruelo's norm argument supply the quartic lower
bound for any integer quotient. Inert primes sieve the floor by its
residue modulo each prime. What remains are the arithmetic tests on the
two sequences of floors corresponding to even and odd half-periods.

Amdeberhan, Medina and Moll posed the conjecture in J. Number Theory 128
(2008), 1807–1846. The norm estimate follows Cilleruelo's method in Squares
in (1²+1)⋯(n²+1). The normalization and the geometric scale are from Ono,
Integer values of an arctangent sum are rare, https://arxiv.org/abs/2607.05739. -/

namespace ArctanCert.Valuations

open Finset

/-- For an odd prime power, any two square roots of minus one agree up to sign. -/
theorem root_eq_or_neg {p j : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hj : 0<j)
    {x y : ZMod (p^j)} (hx : x^2 = -1) (hy : y^2 = -1) : x=y ∨ x= -y := by
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  let _ : NeZero (p^j) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let red := ZMod.castHom (show p ∣ p^j by exact dvd_pow_self _ hj.ne') (ZMod p)
  have liftUnit (z : ZMod (p^j)) (hz : red z ≠ 0) : IsUnit z := by
    rw [← ZMod.natCast_zmod_val z]
    apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp hj).mpr
    intro he
    apply hz
    rw [← ZMod.natCast_zmod_val z, map_natCast]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr he
  have hx₀ : red x ≠ 0 := by
    intro he
    have h := congrArg red hx
    simp [map_pow, he] at h
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro he
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).mp (by simpa using he)
    have := Nat.le_of_dvd (by decide) hd
    have := hp.two_le
    omega
  have hprod : (x-y)*(x+y)=0 := by linear_combination hx-hy
  by_cases hm : red x = red y
  · have hu : IsUnit (x+y) := by
      apply liftUnit
      rw [map_add, ← hm, ← two_mul]
      exact mul_ne_zero htwo hx₀
    exact Or.inl (sub_eq_zero.mp (hu.mul_left_inj.mp (by simpa using hprod)))
  · have hu : IsUnit (x-y) := liftUnit _ (by simpa using sub_ne_zero.mpr hm)
    exact Or.inr (eq_neg_of_add_eq_zero_left (hu.mul_right_inj.mp (by simpa using hprod)))

private lemma class_count (n q : ℕ) (v : ZMod q) :
    ((Icc 1 n).filter fun k : ℕ => (k : ZMod q)=v).card ≤ n/q+1 := by
  let S := (Icc 1 n).filter fun k : ℕ => (k : ZMod q)=v
  have in_range : Set.MapsTo (fun k : ℕ => k/q) (S : Set ℕ) (range (n/q+1)) := by
    intro k hk
    have hkn := (mem_Icc.mp (mem_filter.mp hk).1).2
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hkn))
  have inj : (S : Set ℕ).InjOn (fun k : ℕ => k/q) := by
    intro k hk l hl he
    have hke : (k : ZMod q)=v := (mem_filter.mp hk).2
    have hle : (l : ZMod q)=v := (mem_filter.mp hl).2
    have hr := (ZMod.natCast_eq_natCast_iff' k l q).mp (hke.trans hle.symm)
    exact (Nat.div_add_mod k q).symm.trans ((congrArg₂ (fun d r : ℕ => q*d+r) he hr).trans
      (Nat.div_add_mod l q))
  exact (card_le_card_of_injOn _ in_range inj).trans_eq (card_range _)

/-- Each positive prime power dividing k²+1 accounts for at most two
residue classes among k from 1 through n. -/
theorem power_count {p j : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hj : 0<j) (n : ℕ) :
    ((Icc 1 n).filter fun k => p^j ∣ k^2+1).card ≤ 2*(n/p^j+1) := by
  let q := p^j
  let S := (Icc 1 n).filter fun k => q ∣ k^2+1
  change S.card ≤ 2*(n/q+1)
  rcases S.eq_empty_or_nonempty with he | ⟨v,hv⟩
  · simp [he]
  have root {k : ℕ} (hk : k∈S) : (k:ZMod q)^2 = -1 := by
    have hd : q ∣ k^2+1 := (mem_filter.mp hk).2
    have hs := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    push_cast at hs
    exact eq_neg_of_add_eq_zero_left hs
  let C (z : ZMod q) := (Icc 1 n).filter fun k : ℕ => (k:ZMod q)=z
  have hc : S ⊆ C (v:ZMod q) ∪ C (-(v:ZMod q)) := by
    intro k hk
    have hk' := (mem_filter.mp hk).1
    rcases root_eq_or_neg hp hodd hj (root hk) (root hv) with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨hk',h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hk',h⟩)
  calc
    S.card ≤ _ := card_le_card hc
    _ ≤ (C (v:ZMod q)).card + (C (-(v:ZMod q))).card := card_union_le _ _
    _ ≤ (n/q+1)+(n/q+1) := Nat.add_le_add (class_count n q _) (class_count n q _)
    _ = _ := by omega

/-- The local valuation is at most twice the factorial valuation plus
one endpoint contribution for each of two residue classes per power. -/
theorem product_bound (n : ℕ) {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    (∏ k ∈ Icc 1 n, (k^2+1)).factorization p ≤
      2*n.factorial.factorization p + 2*Nat.log p (n^2+1) := by
  let L := Nat.log p (n^2+1)
  let J := Ico 1 (L+1)
  have hn : n ≤ n^2+1 := by nlinarith [Nat.le_mul_self n]
  have hlog : Nat.log p n < L+1 := Nat.lt_succ_of_le (Nat.log_mono_right hn)
  have hk (k : ℕ) (h : k∈Icc 1 n) :
      (k^2+1).factorization p = ∑ j ∈ J, (if p^j ∣ k^2+1 then 1 else 0) := by
    have hle : k^2+1 ≤ n^2+1 := Nat.add_le_add_right (Nat.pow_le_pow_left (mem_Icc.mp h).2 _) _
    have hlt : k^2+1 < p^(L+1) := hle.trans_lt (Nat.lt_pow_of_log_lt hp.one_lt (by dsimp [L]; omega))
    rw [Nat.factorization_eq_card_pow_dvd_of_lt hp (by omega) hlt]
    simp [J, sum_boole]
  calc
    _ = ∑ k ∈ Icc 1 n, (k^2+1).factorization p := Nat.factorization_prod_apply (fun k _ => Nat.succ_ne_zero (k^2))
    _ = ∑ k ∈ Icc 1 n, ∑ j ∈ J, if p^j ∣ k^2+1 then 1 else 0 := sum_congr rfl hk
    _ = ∑ j ∈ J, ((Icc 1 n).filter fun k => p^j ∣ k^2+1).card := by rw [sum_comm]; simp [sum_boole]
    _ ≤ ∑ j ∈ J, 2*(n/p^j+1) := sum_le_sum fun j hj => power_count hp hodd (mem_Ico.mp hj).1 n
    _ = _ := by
      rw [Nat.factorization_factorial hp hlog]
      simp [J, L, Nat.mul_add, sum_add_distrib, mul_sum]
      exact Nat.mul_comm _ _

end ArctanCert.Valuations

namespace ArctanCert.Valuations

open Finset

private lemma valuation_at_two (k : ℕ) : (k^2+1).factorization 2 = k%2 := by
  by_cases he : k%2=0
  · rw [he]
    apply Nat.factorization_eq_zero_of_not_dvd
    obtain ⟨m,rfl⟩ : ∃ m, k=2*m := ⟨k/2,by omega⟩
    rw [show (2*m)^2+1 = 2*(2*m*m)+1 by ring]
    omega
  · have ho : k%2=1 := by omega
    rw [ho]
    obtain ⟨m,rfl⟩ : ∃ m, k=2*m+1 := ⟨k/2,by omega⟩
    let u := 2*(m*m+m)+1
    have hprod : (2*m+1)^2+1 = 2*u := by dsimp [u]; ring
    have hodd : ¬2∣u := by dsimp [u]; omega
    have hu : u≠0 := by dsimp [u]; omega
    rw [hprod, Nat.factorization_mul (by decide : 2≠0) hu, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hodd, Nat.add_zero]
    exact Nat.prime_two.factorization_self

/-- Exactly the odd indices contribute to the valuation at two, once each. -/
theorem product_two (n : ℕ) :
    (∏ k ∈ Icc 1 n, (k^2+1)).factorization 2 = (n+1)/2 := by
  rw [Nat.factorization_prod_apply (fun k _ => Nat.succ_ne_zero (k^2))]
  simp_rw [valuation_at_two]
  induction n with
  | zero => decide
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega : 1≤n+1), ih]
    omega

/-- Beyond the first index the dyadic valuation already lies below twice
the factorial valuation, without a logarithmic allowance. -/
theorem product_two_le {n : ℕ} (hn : 2≤n) :
    (∏ k ∈ Icc 1 n, (k^2+1)).factorization 2 ≤ 2*n.factorial.factorization 2 := by
  rw [product_two]
  let L := Nat.log 2 n+2
  have hb : Nat.log 2 n<L := by dsimp [L]; omega
  have hm : 1∈Ico 1 L := mem_Ico.mpr ⟨le_rfl, by dsimp [L]; omega⟩
  have h₁ := single_le_sum (f:=fun j : ℕ => n/2^j) (fun _ _ => Nat.zero_le _) hm
  rw [pow_one, ← Nat.factorization_factorial Nat.prime_two hb] at h₁
  omega

/-- The same local upper bound holds throughout the prime support. -/
theorem product_bound_all (n : ℕ) {p : ℕ} (hp : p.Prime) :
    (∏ k ∈ Icc 1 n, (k^2+1)).factorization p ≤
      2*n.factorial.factorization p + 2*Nat.log p (n^2+1) := by
  by_cases h : p=2
  · subst p
    by_cases hn : 2≤n
    · exact (product_two_le hn).trans (Nat.le_add_right _ _)
    · rw [product_two]
      interval_cases n <;> norm_num [Nat.log]
  · exact product_bound n hp h

end ArctanCert.Valuations

namespace ArctanGlobal

open Arxiv.«2607.05739»

/-- The natural product is the squared norm of the original Gaussian integer. -/
lemma product_norm (n : ℕ) : (∏ k ∈ Finset.Icc 1 n, (k^2+1)) = (A n).natAbs^2+(B n).natAbs^2 := by
  have eqn : ((∏ k ∈ Finset.Icc 1 n, (k^2+1) : ℕ):ℤ) = (gaussProd n).norm := by
    let φ : GaussianInt →* ℤ := Zsqrtd.normMonoidHom
    change _ = φ (gaussProd n)
    rw [gaussProd,map_prod,Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro k _
    change ((k^2+1:ℕ):ℤ) = 1*1-(-1)*(k:ℤ)*k
    push_cast
    ring
  calc
    _ = (gaussProd n).norm.natAbs := congrArg Int.natAbs eqn
    _ = _ := by simpa only [A,B,pow_two] using GaussianInt.natAbs_norm_eq (gaussProd n)

lemma product_norm_int (n : ℕ) : ((∏ k ∈ Finset.Icc 1 n, (k^2+1) : ℕ):ℤ) = A n^2+B n^2 := by
  simp only [product_norm,Nat.cast_add,Nat.cast_pow,Int.natCast_natAbs,sq_abs]

lemma factorial_sq_le_product (n : ℕ) : n.factorial^2 ≤ ∏ k ∈ Finset.Icc 1 n, (k^2+1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.factorial_succ,mul_pow,mul_comm ((n+1)^2),Finset.prod_Icc_succ_top (by omega : 1 ≤ n+1)]
    exact Nat.mul_le_mul ih (Nat.le_succ _)

private lemma root_of_divisor {p j : ℕ} (h : p ∣ j^2+1) : (j:ZMod p)^2 = -1 := by
  have hz : (j:ZMod p)^2+1=0 := by
    simpa only [Nat.cast_add,Nat.cast_pow,Nat.cast_one] using (ZMod.natCast_eq_zero_iff (j^2+1) p).mpr h
  exact eq_neg_of_add_eq_zero_left hz

/-- Inert primes divide none of the norm factors. -/
lemma inert_order_zero (n : ℕ) {p : ℕ} (hp : p.Prime) (hmod : p%4=3) :
    (∏ k ∈ Finset.Icc 1 n, (k^2+1)).factorization p=0 := by
  let _ : Fact p.Prime := ⟨hp⟩
  apply Nat.factorization_eq_zero_of_not_dvd
  apply hp.prime.not_dvd_finsetProd
  intro k _ hk
  exact ZMod.mod_four_ne_three_of_sq_eq_neg_one (root_of_divisor hk) hmod

/-- For `p>2n` at most one entry is a square root of minus one modulo `p`.
That entry has positive norm smaller than `p²`. -/
lemma large_order_le_one (n : ℕ) {p : ℕ} (hp : p.Prime) (hbig : 2*n<p) :
    (∏ k ∈ Finset.Icc 1 n, (k^2+1)).factorization p ≤ 1 := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_prod_apply (fun k _ => by positivity)]
  by_cases hit : ∃ k ∈ Finset.Icc 1 n, p ∣ k^2+1
  · obtain ⟨k,hk,hpk⟩ := hit
    obtain ⟨hk₁,hkn⟩ := Finset.mem_Icc.mp hk
    have unique (j : ℕ) (hj : j ∈ Finset.Icc 1 n) (hpj : p ∣ j^2+1) : j=k := by
      obtain ⟨hj₁,hjn⟩ := Finset.mem_Icc.mp hj
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp ((root_of_divisor hpj).trans (root_of_divisor hpk).symm) with eq|neg
      · simpa only [ZMod.val_natCast_of_lt (by omega : j<p),ZMod.val_natCast_of_lt (by omega : k<p)]
          using congrArg ZMod.val eq
      · have hz : ((j+k:ℕ):ZMod p)=0 := by rw [Nat.cast_add,neg,neg_add_cancel]
        exact False.elim ((Nat.not_dvd_of_pos_of_lt (by omega : 0<j+k) (by omega : j+k<p))
          ((ZMod.natCast_eq_zero_iff (j+k) p).mp hz))
    rw [Finset.sum_eq_single k]
    · have hlt : k^2+1 < p^2 := by
        have h := Nat.pow_le_pow_left (by omega : k+1 ≤ p) 2
        nlinarith only [h,hk₁]
      by_contra! hv
      exact Nat.not_dvd_of_pos_of_lt (by positivity) hlt
        ((hp.pow_dvd_iff_le_factorization (by positivity : k^2+1 ≠ 0)).mpr (by omega : 2≤(k^2+1).factorization p))
    · intro j hj hne
      exact Nat.factorization_eq_zero_of_not_dvd fun hpj => hne (unique j hj hpj)
    · exact fun h => (h hk).elim
  · have h : (∑ k ∈ Finset.Icc 1 n, (k^2+1).factorization p)=0 := by
      apply Finset.sum_eq_zero
      intro k hk
      exact Nat.factorization_eq_zero_of_not_dvd fun h => hit ⟨k,hk,h⟩
    rw [h]
    decide

lemma large_square_not_dvd (n : ℕ) {p : ℕ} (hp : p.Prime) (hbig : 2*n<p) :
    ¬p^2 ∣ (∏ k ∈ Finset.Icc 1 n, (k^2+1)) := by
  intro h
  have hpos : 0 < ∏ k ∈ Finset.Icc 1 n, (k^2+1) := Finset.prod_pos fun _ _ => by positivity
  have htwo := (hp.pow_dvd_iff_le_factorization hpos.ne').mp h
  have hone := large_order_le_one n hp hbig
  omega

/-- A large prime occurring in the product must divide the remaining factor after any square is removed. -/
lemma large_prime_square_factor {n p b W : ℕ} (hp : p.Prime) (hbig : 2*n<p)
    (hdiv : p ∣ (∏ k ∈ Finset.Icc 1 n, (k^2+1))) (hPW : (∏ k ∈ Finset.Icc 1 n, (k^2+1))=b^2*W) :
    (∏ k ∈ Finset.Icc 1 n, (k^2+1)).factorization p=1 ∧ p ∣ W := by
  let P := ∏ k ∈ Finset.Icc 1 n, (k^2+1)
  have hpos : 0<P := Finset.prod_pos fun _ _ => by positivity
  refine ⟨le_antisymm (large_order_le_one n hp hbig) ((hp.dvd_iff_one_le_factorization hpos.ne').mp hdiv),?_⟩
  have hn : ¬ p ∣ b^2 := by
    intro hh
    apply large_square_not_dvd n hp hbig
    rw [hPW]
    exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hh) 2) _
  exact (hp.dvd_mul.mp (hPW ▸ hdiv)).resolve_left hn

/-- For an integer quotient, the large prime divides its norm `1+|m|²`. -/
lemma large_prime_quotient {n p : ℕ} {m : ℤ} (hp : p.Prime) (hbig : 2*n<p)
    (hdiv : p ∣ (∏ k ∈ Finset.Icc 1 n, (k^2+1))) (hm : B n=A n*m) :
    (∏ k ∈ Finset.Icc 1 n, (k^2+1)).factorization p=1 ∧ p ∣ 1+m.natAbs^2 := by
  apply large_prime_square_factor (b:=(A n).natAbs) hp hbig hdiv
  rw [product_norm,hm,Int.natAbs_mul]
  ring

/-- A square factorization of the product and the small-prime estimates give both divisibility
and a lower bound on the remaining factor, using any inert divisor of the factorial. -/
lemma aggregate_square_bound {n I E b W : ℕ} (hn : 1≤n) (hI : 0<I) (hE : 0<E)
    (hIfact : I ∣ n.factorial) (hIsupp : ∀ p : ℕ, p.Prime → p ∣ I → p%4=3)
    (hsmall : ∀ p : ℕ, p.Prime → p≤2*n → (∏ k ∈ Finset.Icc 1 n, (k^2+1)).factorization p ≤
      2*n.factorial.factorization p + 2*E.factorization p)
    (hW : 0<W) (hPW : (∏ k ∈ Finset.Icc 1 n, (k^2+1))=b^2*W) :
    ((∏ k ∈ Finset.Icc 1 n, (k^2+1))*I^2 ∣ n.factorial^2*E^2*W) ∧ I^2 ≤ E^2*W := by
  let P := ∏ k ∈ Finset.Icc 1 n, (k^2+1)
  have hF : 0<n.factorial := lt_of_lt_of_le (by omega : 0<n) (Nat.self_le_factorial n)
  have hP : 0<P := Finset.prod_pos fun _ _ => by positivity
  have mul_val (x y : ℕ) (hx : 0<x) (hy : 0<y) (p : ℕ) :
      (x*y).factorization p = x.factorization p+y.factorization p := by rw [Nat.factorization_mul hx.ne' hy.ne']; rfl
  have sq_val (x p : ℕ) : (x^2).factorization p = 2*x.factorization p := by
    simp [Nat.factorization_pow,Finsupp.smul_apply]
  have divides : P*I^2 ∣ n.factorial^2*E^2*W := by
    apply (Nat.factorization_prime_le_iff_dvd (by positivity) (by positivity)).mp
    intro p hp
    rw [mul_val _ _ hP (by positivity),mul_val _ _ (by positivity) hW,
      mul_val _ _ (by positivity : 0<n.factorial^2) (by positivity : 0<E^2)]
    simp only [sq_val]
    by_cases pi : p ∣ I
    · have hz : P.factorization p=0 := inert_order_zero n hp (hIsupp p hp pi)
      have hle := (Nat.factorization_prime_le_iff_dvd hI.ne' hF.ne').mpr hIfact p hp
      omega
    · have hiz := Nat.factorization_eq_zero_of_not_dvd pi
      by_cases small : p≤2*n
      · have h := hsmall p hp small
        change P.factorization p ≤ _ at h
        omega
      · by_cases hit : p ∣ P
        · obtain ⟨hv,hq⟩ := large_prime_square_factor hp (by omega : 2*n<p) hit hPW
          change P.factorization p=1 at hv
          have hqv := (hp.dvd_iff_one_le_factorization hW.ne').mp hq
          omega
        · have hz := Nat.factorization_eq_zero_of_not_dvd hit
          omega
  refine ⟨divides,?_⟩
  apply Nat.le_of_mul_le_mul_left (c:=n.factorial^2) _ (by positivity)
  have hl := (Nat.mul_le_mul_right (I^2) (factorial_sq_le_product n)).trans (Nat.le_of_dvd (by positivity) divides)
  simpa only [Nat.mul_assoc] using hl

/-- An integral tangent quotient gives the square factor `|A n|²`. -/
lemma aggregate_bound {n I E : ℕ} {m : ℤ} (hn : 1≤n) (hI : 0<I) (hE : 0<E)
    (hIfact : I ∣ n.factorial) (hIsupp : ∀ p : ℕ, p.Prime → p ∣ I → p%4=3)
    (hsmall : ∀ p : ℕ, p.Prime → p≤2*n → (∏ k ∈ Finset.Icc 1 n, (k^2+1)).factorization p ≤
      2*n.factorial.factorization p + 2*E.factorization p)
    (hm : B n=A n*m) :
    ((∏ k ∈ Finset.Icc 1 n, (k^2+1))*I^2 ∣ n.factorial^2*E^2*(1+m.natAbs^2)) ∧
      I^2 ≤ E^2*(1+m.natAbs^2) := by
  apply aggregate_square_bound (b:=(A n).natAbs) hn hI hE hIfact hIsupp hsmall (by positivity)
  rw [product_norm,hm,Int.natAbs_mul]
  ring

/-- The reciprocal integral quotient gives the square factor `|B n|²`. -/
lemma aggregate_reciprocal_bound {n I E : ℕ} {m : ℤ} (hn : 1≤n) (hI : 0<I) (hE : 0<E)
    (hIfact : I ∣ n.factorial) (hIsupp : ∀ p : ℕ, p.Prime → p ∣ I → p%4=3)
    (hsmall : ∀ p : ℕ, p.Prime → p≤2*n → (∏ k ∈ Finset.Icc 1 n, (k^2+1)).factorization p ≤
      2*n.factorial.factorization p + 2*E.factorization p)
    (hm : A n=B n*m) :
    ((∏ k ∈ Finset.Icc 1 n, (k^2+1))*I^2 ∣ n.factorial^2*E^2*(1+m.natAbs^2)) ∧
      I^2 ≤ E^2*(1+m.natAbs^2) := by
  apply aggregate_square_bound (b:=(B n).natAbs) hn hI hE hIfact hIsupp hsmall (by positivity)
  rw [product_norm,hm,Int.natAbs_mul]
  ring

/-- If the product is a square, the inert divisor cannot exceed the small-prime allowance. -/
lemma square_forces_le {n I E b : ℕ} (hn : 1≤n) (hI : 0<I) (hE : 0<E)
    (hIfact : I ∣ n.factorial) (hIsupp : ∀ p : ℕ, p.Prime → p ∣ I → p%4=3)
    (hsmall : ∀ p : ℕ, p.Prime → p≤2*n → (∏ k ∈ Finset.Icc 1 n, (k^2+1)).factorization p ≤
      2*n.factorial.factorization p + 2*E.factorization p)
    (hP : (∏ k ∈ Finset.Icc 1 n, (k^2+1))=b^2) : I ≤ E := by
  have h := (aggregate_square_bound (b:=b) (W:=1) hn hI hE hIfact hIsupp hsmall (by decide)
    (by simpa only [mul_one] using hP)).2
  exact (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp (by simpa only [mul_one] using h)

end ArctanGlobal

namespace ArctanInertLemmas

/-- A kernel-computed prime weight for the explicit finite set. -/
lemma weight_exact :
    (∑ p ∈ (Finset.range 50001).filter (fun q : ℕ => q.Prime ∧ q%4=3),p.log2*(1048576/p))=6591956 := by
  let wheel : ℕ := 249873185435436430377698987059663362395086628984728391823112288166942630559511819124255704981537449930570629002821280463185334406128048989132838398791636205678208673855202473444935869602342296488442348182529563060454306401874514103425982529680729837954985416328663177512069858595443931833472658803081894351725778122546461871134622081830651613340173985723024483556319497604300800000000000000000000000000000000000000000000000000000
  have wheel_factorial : wheel=Nat.factorial 223 := by decide +kernel

  let primeCheck (p : ℕ) : Bool :=
    if p≤223 then decide p.Prime else p.gcd wheel == 1

  have primeCheck_iff {p : ℕ} (hp : p≤50000) : primeCheck p=true ↔ p.Prime := by
    unfold primeCheck
    split
    · simp
    · rename_i hbig
      rw [beq_iff_eq,wheel_factorial,← Nat.coprime_iff_gcd_eq_one]
      constructor
      · intro hc
        apply Nat.prime_def_le_sqrt.mpr
        refine ⟨by omega,?_⟩
        intro d h₂ hs hd
        have hs' := Nat.sqrt_le_sqrt hp
        have h224 : Nat.sqrt 50000 < 224 := Nat.sqrt_lt.mpr (by decide)
        have h223 : d≤223 := by omega
        have hdiv := Nat.dvd_gcd hd (Nat.dvd_factorial (by omega : 0<d) h223)
        rw [hc.gcd_eq_one] at hdiv
        have := Nat.le_of_dvd (by decide : 0<1) hdiv
        omega
      · intro pp
        exact pp.coprime_factorial_of_lt (by omega)

  let weight (p : ℕ) := p.log2*(1048576/p)
  let score (p : ℕ) := if p%4=3 then
    (if primeCheck p then weight p else 0) else 0

  have score_eq {p : ℕ} (hp : p≤50000) :
      score p = if p.Prime ∧ p%4=3 then weight p else 0 := by
    by_cases hm : p%4=3 <;> simp [score,hm,primeCheck_iff hp]
  let subtotal (lo count : ℕ) := Nat.rec (motive:=fun _ => ℕ) 0 (fun k t => t+score (lo+k)) count
  have subtotal_add (start len : ℕ) :
      (∑ p ∈ Finset.range (start+len),score p) =
        (∑ p ∈ Finset.range start,score p) + subtotal start len := by
    induction len with
    | zero => simp [subtotal]
    | succ k ih =>
      rw [Nat.add_succ,Finset.sum_range_succ,ih]
      exact Nat.add_assoc _ _ _
  have next {n old new : ℕ} (prev : (∑ p ∈ Finset.range n,score p)=old) (len : ℕ)
      (h : old+subtotal n len=new) : (∑ p ∈ Finset.range (n+len),score p)=new := by
    rw [subtotal_add,prev,h]
  have zero : (∑ p ∈ Finset.range 0,score p)=0 := by simp
  have c1000 : (∑ p ∈ Finset.range 1000,score p)=3773075 := next zero 1000 (by decide +kernel)
  have c2000 : (∑ p ∈ Finset.range 2000,score p)=4265756 := next c1000 1000 (by decide +kernel)
  have c3000 : (∑ p ∈ Finset.range 3000,score p)=4558723 := next c2000 1000 (by decide +kernel)
  have c4000 : (∑ p ∈ Finset.range 4000,score p)=4763521 := next c3000 1000 (by decide +kernel)
  have c5000 : (∑ p ∈ Finset.range 5000,score p)=4927188 := next c4000 1000 (by decide +kernel)
  have c6000 : (∑ p ∈ Finset.range 6000,score p)=5064756 := next c5000 1000 (by decide +kernel)
  have c7000 : (∑ p ∈ Finset.range 7000,score p)=5176692 := next c6000 1000 (by decide +kernel)
  have c8000 : (∑ p ∈ Finset.range 8000,score p)=5260512 := next c7000 1000 (by decide +kernel)
  have c9000 : (∑ p ∈ Finset.range 9000,score p)=5346871 := next c8000 1000 (by decide +kernel)
  have c10000 : (∑ p ∈ Finset.range 10000,score p)=5428303 := next c9000 1000 (by decide +kernel)
  have c11000 : (∑ p ∈ Finset.range 11000,score p)=5500791 := next c10000 1000 (by decide +kernel)
  have c12000 : (∑ p ∈ Finset.range 12000,score p)=5565596 := next c11000 1000 (by decide +kernel)
  have c13000 : (∑ p ∈ Finset.range 13000,score p)=5619702 := next c12000 1000 (by decide +kernel)
  have c14000 : (∑ p ∈ Finset.range 14000,score p)=5672911 := next c13000 1000 (by decide +kernel)
  have c15000 : (∑ p ∈ Finset.range 15000,score p)=5723195 := next c14000 1000 (by decide +kernel)
  have c16000 : (∑ p ∈ Finset.range 16000,score p)=5770242 := next c15000 1000 (by decide +kernel)
  have c17000 : (∑ p ∈ Finset.range 17000,score p)=5814086 := next c16000 1000 (by decide +kernel)
  have c18000 : (∑ p ∈ Finset.range 18000,score p)=5858970 := next c17000 1000 (by decide +kernel)
  have c19000 : (∑ p ∈ Finset.range 19000,score p)=5892808 := next c18000 1000 (by decide +kernel)
  have c20000 : (∑ p ∈ Finset.range 20000,score p)=5927836 := next c19000 1000 (by decide +kernel)
  have c21000 : (∑ p ∈ Finset.range 21000,score p)=5964054 := next c20000 1000 (by decide +kernel)
  have c22000 : (∑ p ∈ Finset.range 22000,score p)=5999894 := next c21000 1000 (by decide +kernel)
  have c23000 : (∑ p ∈ Finset.range 23000,score p)=6032948 := next c22000 1000 (by decide +kernel)
  have c24000 : (∑ p ∈ Finset.range 24000,score p)=6063314 := next c23000 1000 (by decide +kernel)
  have c25000 : (∑ p ∈ Finset.range 25000,score p)=6092350 := next c24000 1000 (by decide +kernel)
  have c26000 : (∑ p ∈ Finset.range 26000,score p)=6119006 := next c25000 1000 (by decide +kernel)
  have c27000 : (∑ p ∈ Finset.range 27000,score p)=6143604 := next c26000 1000 (by decide +kernel)
  have c28000 : (∑ p ∈ Finset.range 28000,score p)=6170414 := next c27000 1000 (by decide +kernel)
  have c29000 : (∑ p ∈ Finset.range 29000,score p)=6196860 := next c28000 1000 (by decide +kernel)
  have c30000 : (∑ p ∈ Finset.range 30000,score p)=6220926 := next c29000 1000 (by decide +kernel)
  have c31000 : (∑ p ∈ Finset.range 31000,score p)=6241296 := next c30000 1000 (by decide +kernel)
  have c32000 : (∑ p ∈ Finset.range 32000,score p)=6264284 := next c31000 1000 (by decide +kernel)
  have c33000 : (∑ p ∈ Finset.range 33000,score p)=6288266 := next c32000 1000 (by decide +kernel)
  have c34000 : (∑ p ∈ Finset.range 34000,score p)=6310466 := next c33000 1000 (by decide +kernel)
  have c35000 : (∑ p ∈ Finset.range 35000,score p)=6333401 := next c34000 1000 (by decide +kernel)
  have c36000 : (∑ p ∈ Finset.range 36000,score p)=6354716 := next c35000 1000 (by decide +kernel)
  have c37000 : (∑ p ∈ Finset.range 37000,score p)=6374981 := next c36000 1000 (by decide +kernel)
  have c38000 : (∑ p ∈ Finset.range 38000,score p)=6393866 := next c37000 1000 (by decide +kernel)
  have c39000 : (∑ p ∈ Finset.range 39000,score p)=6411161 := next c38000 1000 (by decide +kernel)
  have c40000 : (∑ p ∈ Finset.range 40000,score p)=6431831 := next c39000 1000 (by decide +kernel)
  have c41000 : (∑ p ∈ Finset.range 41000,score p)=6449636 := next c40000 1000 (by decide +kernel)
  have c42000 : (∑ p ∈ Finset.range 42000,score p)=6468326 := next c41000 1000 (by decide +kernel)
  have c43000 : (∑ p ∈ Finset.range 43000,score p)=6485966 := next c42000 1000 (by decide +kernel)
  have c44000 : (∑ p ∈ Finset.range 44000,score p)=6500546 := next c43000 1000 (by decide +kernel)
  have c45000 : (∑ p ∈ Finset.range 45000,score p)=6517796 := next c44000 1000 (by decide +kernel)
  have c46000 : (∑ p ∈ Finset.range 46000,score p)=6530981 := next c45000 1000 (by decide +kernel)
  have c47000 : (∑ p ∈ Finset.range 47000,score p)=6546821 := next c46000 1000 (by decide +kernel)
  have c48000 : (∑ p ∈ Finset.range 48000,score p)=6561461 := next c47000 1000 (by decide +kernel)
  have c49000 : (∑ p ∈ Finset.range 49000,score p)=6575636 := next c48000 1000 (by decide +kernel)
  have c50000 : (∑ p ∈ Finset.range 50000,score p)=6591956 := next c49000 1000 (by decide +kernel)
  have c50001 : (∑ p ∈ Finset.range 50001,score p)=6591956 := next c50000 1 (by decide +kernel)
  rw [Finset.sum_filter]
  apply Eq.trans _ c50001
  apply Finset.sum_congr rfl
  intro p hp
  exact (score_eq (by have := Finset.mem_range.mp hp; omega)).symm

/-- The explicit inert part of n! has only prime divisors congruent to three modulo
four and is large on the entire indicated tail. -/
lemma inert_factorial (n : ℕ) (hn : 2^64≤n) :
    let J := (Finset.range 50001).filter (fun p : ℕ => p.Prime ∧ p%4=3)
    let I := ∏ p ∈ J, p^((n/1048576)*(1048576/p))
    0<I ∧ I∣n.factorial ∧
      (∀ p : ℕ, p.Prime → p∣I → p≤50000 ∧ p%4=3) ∧
      2^((n/1048576)*6590000)≤I ∧ 25*n≤4*((n/1048576)*6590000) ∧ 2^(25*n/4)≤I := by
  let J : Finset ℕ := (Finset.range 50001).filter (fun p : ℕ => p.Prime ∧ p%4=3)

  have mem_J {p : ℕ} : p∈J ↔ p≤50000 ∧ p.Prime ∧ p%4=3 := by
    change p ∈ (Finset.range (50000+1)).filter (fun q : ℕ => q.Prime ∧ q%4=3) ↔ _
    rw [Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff]

  let exponent (n p : ℕ) := (n/1048576)*(1048576/p)
  let I (n : ℕ) := ∏ p ∈ J,p^(exponent n p)

  have I_pos (n : ℕ) : 0<I n :=
    Finset.prod_pos fun _ hp => pow_pos (mem_J.mp hp).2.1.pos _

  have factorization_I (n p : ℕ) :
      (I n).factorization p = if p∈J then exponent n p else 0 := by
    dsimp only [I]
    rw [Nat.factorization_prod_apply (fun q hq => pow_ne_zero _ (mem_J.mp hq).2.1.ne_zero)]
    calc
      _ = ∑ q ∈ J, if p=q then exponent n q else 0 := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [(mem_J.mp hq).2.1.factorization_pow]
        simp [Finsupp.single_apply,eq_comm]
      _ = _ := Finset.sum_ite_eq _ _ _

  have I_dvd_factorial (n : ℕ) : I n ∣ n.factorial := by
    apply (Nat.factorization_le_iff_dvd (I_pos n).ne' n.factorial_ne_zero).mp
    intro p
    rw [factorization_I]
    split
    · rename_i hp
      have prime := (mem_J.mp hp).2.1
      have div : exponent n p ≤ n/p := by
        apply (Nat.le_div_iff_mul_le prime.pos).mpr
        calc
          exponent n p*p = (n/1048576)*((1048576/p)*p) := by unfold exponent; ring
          _ ≤ (n/1048576)*1048576 := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
          _ ≤ n := Nat.div_mul_le_self _ _
      apply div.trans
      rw [Nat.factorization_factorial prime (show Nat.log p n<Nat.log p n+2 by omega)]
      have h₁ : 1 ∈ Finset.Ico 1 (Nat.log p n+2) := Finset.mem_Ico.mpr ⟨le_rfl,by omega⟩
      simpa only [pow_one] using
        (Finset.single_le_sum (f:=fun i => n/p^i) (fun _ _ => Nat.zero_le _) h₁)
    · exact Nat.zero_le _

  have prime_dvd_I {n p : ℕ} (hp : p.Prime) (hd : p ∣ I n) : p∈J := by
    by_contra hn
    have h := hp.factorization_pos_of_dvd (I_pos n).ne' hd
    rw [factorization_I,if_neg hn] at h
    exact (Nat.lt_irrefl 0) h
  have finite_weight : (∑ p ∈ J,p.log2*(1048576/p))=6591956 := weight_exact
  have block_lower (n : ℕ) : 2^((n/1048576)*6590000) ≤ I n := by
    calc
      _ ≤ 2^((n/1048576)*6591956) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (by decide))
      _ = ∏ p ∈ J,(2^p.log2)^(exponent n p) := by
        rw [← finite_weight,Finset.mul_sum,← Finset.prod_pow_eq_pow_sum]
        apply Finset.prod_congr rfl
        intro p _
        rw [← pow_mul]
        apply congrArg (fun e : ℕ => 2^e)
        dsimp only [exponent]
        ring
      _ ≤ I n := by
        apply Finset.prod_le_prod'
        intro p hp
        apply Nat.pow_le_pow_left
        exact (Nat.le_log2 (mem_J.mp hp).2.1.ne_zero).mp le_rfl

  have exponent_bound {n : ℕ} (hn : 2^64≤n) : 25*n ≤ 4*((n/1048576)*6590000) := by
    norm_num at hn
    omega

  have dyadic_lower {n : ℕ} (hn : 2^64≤n) : 2^(25*n/4) ≤ I n := by
    apply le_trans _ (block_lower n)
    apply Nat.pow_le_pow_right (by decide)
    have h := exponent_bound hn
    omega
  refine ⟨I_pos n,I_dvd_factorial n,?_,block_lower n,exponent_bound hn,dyadic_lower hn⟩
  intro p hp hd
  obtain ⟨hlo,_,hmod⟩ := mem_J.mp (prime_dvd_I hp hd)
  exact ⟨hlo,hmod⟩

end ArctanInertLemmas

namespace ArctanGlobal

/-- Beyond the 64-bit boundary, the logarithmic contribution from primes up to the
square root fits into a small fraction of the linear exponent. -/
lemma sqrt_log_budget {n : ℕ} (hn : 2^64 ≤ n) : 256*n.sqrt*(2*n.log2+3) ≤ n := by
  have hn0 : n ≠ 0 := by omega
  have hlog : 64 ≤ n.log2 := (Nat.le_log2 hn0).mpr hn
  have dyadic (k : ℕ) (hk : 64 ≤ k) : (256*(2*k+3))^2 ≤ 2^k := by
    induction k, hk using Nat.le_induction with
    | base => decide
    | succ k hk ih =>
      rw [pow_succ]
      calc
        (256*(2*(k+1)+3))^2 ≤ (256*(2*k+3))^2*2 := by
          nlinarith only [hk,Nat.zero_le (k*k)]
        _ ≤ 2^k*2 := Nat.mul_le_mul_right _ ih
  have pow_le : 2^n.log2 ≤ n := (Nat.le_log2 hn0).mp le_rfl
  have square := (dyadic n.log2 hlog).trans pow_le
  have root : 256*(2*n.log2+3) ≤ n.sqrt :=
    Nat.le_sqrt.mpr (by simpa only [pow_two] using square)
  calc
    256*n.sqrt*(2*n.log2+3) = (256*(2*n.log2+3))*n.sqrt := by ring
    _ ≤ n.sqrt*n.sqrt := Nat.mul_le_mul_right _ root
    _ ≤ n := Nat.sqrt_le _

lemma quadratic_dyadic {n : ℕ} (hn : 2^64 ≤ n) : n^2+1 ≤ 2^(2*n.log2+3) := by
  have h : n < 2^(n.log2+1) := (Nat.log2_lt (by omega : n≠0)).mp (by omega)
  have hh := Nat.mul_lt_mul_of_pos_left h (by omega : 0<n)
  have hsq : n*n < 2^(n.log2+1)*2^(n.log2+1) :=
    hh.trans_le (Nat.mul_le_mul_right _ h.le)
  have expand : 2^(2*n.log2+3) = 2^(n.log2+1)*2^(n.log2+1)*2 := by
    rw [← pow_add]
    rw [← pow_succ]
    congr 1
    omega
  rw [expand,pow_two]
  omega

end ArctanGlobal

namespace ArctanPrimeErrorLemmas

/-- The maximal power is controlled using the three prime cutoffs and one small-prime factor. -/
private lemma prime_weight {n p : ℕ} (hn : 2^64 ≤ n) (hp : p.Prime) :
    p^(Nat.log p (n^2+1)) ≤ p*(if p≤n then p else 1)*(if p≤n/256 then p else 1)*
      (if p≤n.sqrt then n^2+1 else 1) := by
  have hn0 : 0<n := by omega
  have hbase : n^2+1 < (n+1)^2 := by nlinarith
  have pow_le (j : ℕ) (hh : n^2+1 < p^(j+1)) : p^(Nat.log p (n^2+1)) ≤ p^j :=
    Nat.pow_le_pow_right hp.pos (Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by positivity) hh))
  by_cases hs : p≤n.sqrt
  · rw [if_pos hs]
    apply (Nat.pow_log_le_self p (by positivity : n^2+1≠0)).trans
    have ht : 1≤p*(if p≤n then p else 1)*(if p≤n/256 then p else 1) := by
      have hpos := hp.pos
      change 0 < p*(if p≤n then p else 1)*(if p≤n/256 then p else 1)
      split <;> split <;> positivity
    simpa only [one_mul] using Nat.mul_le_mul_right (n^2+1) ht
  rw [if_neg hs,mul_one]
  have hs' : n < p^2 := Nat.sqrt_lt'.mp (Nat.lt_of_not_ge hs)
  by_cases hm : p≤n/256
  · have hl : p≤n := hm.trans (Nat.div_le_self _ _)
    rw [if_pos hl,if_pos hm]
    have h4 : n^2+1 < p^4 := by
      calc
        _ < (n+1)^2 := hbase
        _ ≤ (p^2)^2 := Nat.pow_le_pow_left (by omega) _
        _ = _ := by ring
    simpa only [pow_succ,pow_zero,one_mul] using pow_le 3 h4
  rw [if_neg hm,mul_one]
  by_cases hl : p≤n
  · rw [if_pos hl]
    have hpn : n < 256*p := by omega
    have hsize : 65536 ≤ p := by omega
    have h3 : n^2+1 < p^3 := by
      calc
        _ < (n+1)^2 := hbase
        _ ≤ (256*p)^2 := Nat.pow_le_pow_left (by omega) _
        _ ≤ p^3 := by nlinarith only [Nat.mul_le_mul_right (p*p) hsize]
    simpa only [pow_two] using pow_le 2 h3
  · rw [if_neg hl,mul_one]
    have hh : n^2+1 < p^2 := hbase.trans_le (Nat.pow_le_pow_left (by omega) _)
    simpa only [pow_one] using pow_le 1 hh

private lemma product_le_primorial (n : ℕ) (hn : 2^64≤n) :
    (∏ p ∈ (Finset.Icc 1 (2*n)).filter Nat.Prime,p^(Nat.log p (n^2+1))) ≤ primorial (2*n)*primorial n*primorial (n/256)*(n^2+1)^n.sqrt := by
  classical
  let P (k : ℕ) := (Finset.Icc 1 k).filter Nat.Prime
  have same (k : ℕ) : P k = (Finset.range (k+1)).filter Nat.Prime := by
    ext p
    simp only [P,Finset.mem_filter,Finset.mem_Icc,Finset.mem_range,Nat.lt_succ_iff]
    exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨h.2.one_le,h.1⟩,h.2⟩⟩
  have base (k : ℕ) : (∏ p ∈ P k,p) = primorial k := by rw [same]; rfl
  have cut (k : ℕ) (h : k≤2*n) : (P (2*n)).filter (fun p => p≤k)=P k := by
    ext p
    simp only [P,Finset.mem_filter,Finset.mem_Icc]
    exact ⟨fun f => ⟨⟨f.1.1.1,f.2⟩,f.1.2⟩,fun f => ⟨⟨⟨f.1.1,f.1.2.trans h⟩,f.2⟩,f.1.2⟩⟩
  have piece (k : ℕ) (h : k≤2*n) : (∏ p ∈ P (2*n),if p≤k then p else 1)=primorial k := by
    rw [← Finset.prod_filter,cut k h,base]
  have small : (∏ p ∈ P (2*n), if p≤n.sqrt then n^2+1 else 1) ≤ (n^2+1)^n.sqrt := by
    have hcard : (P n.sqrt).card ≤ n.sqrt := by
      have h := Finset.card_le_card (Finset.filter_subset Nat.Prime (Finset.Icc 1 n.sqrt))
      simpa only [P,Nat.card_Icc,Nat.add_sub_cancel] using h
    rw [← Finset.prod_filter,cut n.sqrt (by have := Nat.sqrt_le_self n; omega),Finset.prod_const]
    exact Nat.pow_le_pow_right (by positivity) hcard
  change (∏ p ∈ P (2*n),p^(Nat.log p (n^2+1))) ≤ _
  calc
    _ ≤ ∏ p ∈ P (2*n), p*(if p≤n then p else 1)*(if p≤n/256 then p else 1)*
        (if p≤n.sqrt then n^2+1 else 1) := Finset.prod_le_prod' fun p hp => prime_weight hn (Finset.mem_filter.mp hp).2
    _ ≤ _ := by
      simp only [Finset.prod_mul_distrib,base,piece n (by omega),piece (n/256) (by omega)]
      exact Nat.mul_le_mul_left _ small

/-- Every relevant prime-power cost divides the same positive integer, whose size is
bounded uniformly beyond the unsigned 64-bit range. -/
lemma error_product (n : ℕ) (hn : 2^64 ≤ n) :
    let E := ∏ p ∈ (Finset.Icc 1 (2*n)).filter Nat.Prime,p^(Nat.log p (n^2+1))
    0 < E ∧ (∀ p : ℕ, p.Prime → p≤2*n → p^(Nat.log p (n^2+1)) ∣ E) ∧ E ≤ 2^(49*n/8) := by
  let E := ∏ p ∈ (Finset.Icc 1 (2*n)).filter Nat.Prime,p^(Nat.log p (n^2+1))
  change 0<E ∧ (∀ p : ℕ, p.Prime → p≤2*n → p^(Nat.log p (n^2+1)) ∣ E) ∧ E≤2^(49*n/8)
  refine ⟨?_,?_,?_⟩
  · exact Finset.prod_pos (fun _ hp => pow_pos (Finset.mem_filter.mp hp).2.pos _)
  · intro p hp hle
    exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.one_le,hle⟩,hp⟩)
  · have hsmall := ArctanGlobal.sqrt_log_budget hn
    have hpow := ArctanGlobal.quadratic_dyadic hn
    let L := 2*n.log2+3
    have he : 256*(L*n.sqrt) ≤ n := by simpa only [L,mul_assoc,mul_comm,mul_left_comm] using hsmall
    calc
      _ ≤ primorial (2*n)*primorial n*primorial (n/256)*(n^2+1)^n.sqrt := product_le_primorial n hn
      _ ≤ 4^(2*n)*4^n*4^(n/256)*(2^L)^n.sqrt := by
        gcongr <;> apply primorial_le_four_pow
      _ = 2^(4*n+2*n+2*(n/256)+L*n.sqrt) := by
        rw [show (4:ℕ)=2^2 by decide]
        simp only [← pow_mul,← pow_add]
        congr 1
        ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

end ArctanPrimeErrorLemmas

namespace ArctanGlobal

open Arxiv.«2607.05739»

/-- Removing any square from the Gaussian norm leaves an exponentially large positive factor. -/
theorem square_factor_large {n b W : ℕ} (hn : 2^64 ≤ n) (hW : 0<W)
    (hP : (∏ k ∈ Finset.Icc 1 n, (k^2+1))=b^2*W) : (2^(n/8))^2 ≤ W := by
  classical
  let J := (Finset.range 50001).filter (fun p : ℕ => p.Prime ∧ p%4=3)
  let I := ∏ p ∈ J, p^((n/1048576)*(1048576/p))
  let E := ∏ p ∈ (Finset.Icc 1 (2*n)).filter Nat.Prime, p^(Nat.log p (n^2+1))
  obtain ⟨hI, hIfact, hIsupp, _, _, lower⟩ := ArctanInertLemmas.inert_factorial n hn
  obtain ⟨hE, powers, upper⟩ := ArctanPrimeErrorLemmas.error_product n hn
  change 0<I at hI
  change 0<E at hE
  change 2^(25*n/4) ≤ I at lower
  change E ≤ 2^(49*n/8) at upper
  have ord (p : ℕ) (hp : p.Prime) (hle : p≤2*n) :
      (∏ k ∈ Finset.Icc 1 n, (k^2+1)).factorization p ≤
        2*n.factorial.factorization p + 2*E.factorization p := by
    have he := (hp.pow_dvd_iff_le_factorization hE.ne').mp (powers p hp hle)
    exact (ArctanCert.Valuations.product_bound_all n hp).trans (by omega)
  have aggregate := (aggregate_square_bound (n:=n) (I:=I) (E:=E) (by omega) hI hE hIfact
    (fun p hp hd => (hIsupp p hp hd).2) ord hW hP).2
  let L : ℕ := 2^(n/8)
  have gain : E*L ≤ I := calc
    E*L ≤ 2^(49*n/8)*L := Nat.mul_le_mul_right _ upper
    _ = 2^(49*n/8+n/8) := (pow_add _ _ _).symm
    _ ≤ 2^(25*n/4) := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ I := lower
  have scaled : E^2*L^2 ≤ E^2*W := calc
    _ = (E*L)^2 := (mul_pow E L 2).symm
    _ ≤ I^2 := Nat.pow_le_pow_left gain _
    _ ≤ _ := aggregate
  exact Nat.le_of_mul_le_mul_left scaled (pow_pos hE 2)

private lemma exponential_of_square {n u : ℕ} (hn : 2^64 ≤ n)
    (small : (2^(n/8))^2 ≤ 1+u^2) : 2^(n/8) ≤ u := by
  let L : ℕ := 2^(n/8)
  change L^2 ≤ 1+u^2 at small
  have two : 2 ≤ L := by
    change 2^1 ≤ 2^(n/8)
    exact Nat.pow_le_pow_right (by decide) (by omega)
  change L ≤ u
  by_contra! bad
  have sq := Nat.pow_le_pow_left (show u+1≤L by omega) 2
  by_cases zero : u=0
  · rw [zero] at small
    have hh := Nat.pow_le_pow_left two 2
    omega
  · have pos : 0 < u := Nat.pos_of_ne_zero zero
    nlinarith only [small,sq,pos]

/-- A hypothetical integer value past the word-size boundary has exponential magnitude. -/
theorem quotient_exponential {n : ℕ} {m : ℤ} (hn : 2^64 ≤ n) (hm : B n=A n*m) :
    2^(n/8) ≤ m.natAbs := by
  apply exponential_of_square hn
  apply square_factor_large (b:=(A n).natAbs) hn (by positivity)
  rw [product_norm,hm,Int.natAbs_mul]
  ring

theorem reciprocal_exponential {n : ℕ} {m : ℤ} (hn : 2^64 ≤ n) (hm : A n=B n*m) :
    2^(n/8) ≤ m.natAbs := by
  apply exponential_of_square hn
  apply square_factor_large (b:=(B n).natAbs) hn (by positivity)
  rw [product_norm,hm,Int.natAbs_mul]
  ring

theorem norm_not_square_large {n b : ℕ} (hn : 2^64 ≤ n) :
    (∏ k ∈ Finset.Icc 1 n, (k^2+1)) ≠ b^2 := by
  intro hs
  have large := square_factor_large (b:=b) (W:=1) hn (by decide) (by simpa only [mul_one] using hs)
  have two : 2^1 ≤ 2^(n/8) := Nat.pow_le_pow_right (by decide) (by omega)
  have sq := Nat.pow_le_pow_left two 2
  omega

/-- A prescribed integer value permits only finitely many indices; this gives
the explicit search limit above the certified finite range. -/
theorem index_lt_bit_bound {n : ℕ} {m : ℤ} (hn : 2^64 ≤ n) (hm : B n=A n*m) :
    n < 8*(m.natAbs.log2+1) := by
  have big := quotient_exponential hn hm
  have positive : 0 < m.natAbs := (by positivity : 0 < 2^(n/8)).trans_le big
  have bits := (Nat.le_log2 positive.ne').mpr big
  omega

private lemma eight_mul_le_exp {n : ℕ} (hn : 2^64 ≤ n) : 8*n ≤ 2^(n/8) := by
  have enough (k : ℕ) (hk : 64≤k) : 64*(k+1) ≤ 2^k := by
    induction k,hk using Nat.le_induction with
    | base => decide
    | succ k hk ih => rw [pow_succ]; omega
  exact (show 8*n ≤ 64*(n/8+1) by omega).trans (enough _ (by omega))

theorem quotient_large_linear {n : ℕ} {m : ℤ} (hn : 2^64 ≤ n) (hm : B n=A n*m) :
    8*(n:ℤ) ≤ |m| := by
  have h := (eight_mul_le_exp hn).trans (quotient_exponential hn hm)
  rw [← Int.natCast_natAbs]
  exact_mod_cast h

end ArctanGlobal

namespace ArctanPhase

/-- From the word-size boundary the exponential obstruction dominates a
quartic with enough slack to recover the second term in the pole scale. -/
lemma quartic_le_exp {n : ℕ} (hn : 2^64 ≤ n) : 1000*n^4 ≤ 2^(n/8) := by
  have doubled {k : ℕ} (h : 256≤k) : (k+2)^4 ≤ 2*(k+1)^4 := by
    obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le h
    have hpos : (0:ℤ) ≤ t := by positivity
    zify
    apply sub_nonneg.mp
    ring_nf
    positivity
  have power (k : ℕ) (hk : 256≤k) : 4096000*(k+1)^4 ≤ 2^k := by
    induction k,hk using Nat.le_induction with
    | base => decide
    | succ k hk ih =>
      calc
        4096000*(k+1+1)^4 ≤ 4096000*(2*(k+1)^4) :=
          Nat.mul_le_mul_left _ (doubled hk)
        _ = 4096000*(k+1)^4*2 := by ring
        _ ≤ 2^k*2 := Nat.mul_le_mul_right _ ih
        _ = 2^(k+1) := (pow_succ _ _).symm
  have cap : n ≤ 8*(n/8+1) := by omega
  calc
    1000*n^4 ≤ 1000*(8*(n/8+1))^4 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left cap 4)
    _ = 4096000*(n/8+1)^4 := by ring
    _ ≤ _ := power _ (by omega)

end ArctanPhase

namespace ArctanCert

open Arxiv.«2607.05739»

private lemma eval_gauss_product {p : ℕ} (n : ℕ) (r : ZMod p) (hr : r*r = -1) :
    (A n : ZMod p)+(B n : ZMod p)*r = ∏ j ∈ Finset.Icc 1 n, (1+(j : ZMod p)*r) := by
  let φ : GaussianInt →+* ZMod p := Zsqrtd.lift ⟨r,by simpa only [Int.cast_neg,Int.cast_one] using hr⟩
  change φ (gaussProd n) = _
  rw [gaussProd,map_prod]
  apply Finset.prod_congr rfl
  intro j _
  change ((1:ℤ):ZMod p) + ((j:ℤ):ZMod p)*r = _
  simp

/-- A prime divisor of `1+k²` larger than `n+k` determines the signed residue
of every integer quotient: the two evaluations of the Gaussian product at `k`
and `-k` have opposite vanishing behavior. -/
lemma signed_residue {n p k : ℕ} (hp : p.Prime) (hk : 1≤k) (hkn : k≤n)
    (hsize : n+k<p) (hdiv : p ∣ 1+k^2) {m : ℤ} (hm : B n = A n*m) :
    (m : ZMod p) = (k : ZMod p) := by
  let _ : Fact p.Prime := ⟨hp⟩
  let K : ZMod p := k
  have hsq : K*K = -1 := by
    have h : (1 + K^2 : ZMod p)=0 := by
      simpa only [K,Nat.cast_add,Nat.cast_one,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff (1+k^2) p).mpr hdiv
    linear_combination h
  have plus : (A n : ZMod p)+(B n : ZMod p)*K=0 := by
    rw [eval_gauss_product n K hsq]
    apply Finset.prod_eq_zero (Finset.mem_Icc.mpr ⟨hk,hkn⟩)
    change 1+K*K=0
    rw [hsq,add_neg_cancel]
  have minus : (A n : ZMod p)+(B n : ZMod p)*(-K) ≠ 0 := by
    rw [eval_gauss_product n (-K) (by simpa only [neg_mul_neg] using hsq)]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj hz
    obtain ⟨hj₁,hjn⟩ := Finset.mem_Icc.mp hj
    have hzero : ((j+k : ℕ) : ZMod p)=0 := by
      rw [Nat.cast_add]
      change (j:ZMod p)+K=0
      calc
        _ = K*(1+(j:ZMod p)*(-K)) := by linear_combination (j:ZMod p)*hsq
        _ = 0 := by rw [hz,mul_zero]
    exact (Nat.not_dvd_of_pos_of_lt (by omega : 0<j+k) (by omega : j+k<p))
      ((ZMod.natCast_eq_zero_iff (j+k) p).mp hzero)
  have hquot : (B n : ZMod p)=(A n : ZMod p)*(m : ZMod p) := by
    simpa only [Int.cast_mul] using congrArg (fun z : ℤ => (z : ZMod p)) hm
  have hA : (A n : ZMod p)≠0 := by
    intro ha
    exact minus (by simp [hquot,ha])
  have hfactor : (A n : ZMod p)*(1+(m : ZMod p)*K)=0 := by
    calc
      _ = (A n : ZMod p)+(B n : ZMod p)*K := by rw [hquot]; ring
      _ = 0 := plus
  have hz := (mul_eq_zero.mp hfactor).resolve_left hA
  change (m : ZMod p)=K
  linear_combination (m : ZMod p)*hsq - K*hz

end ArctanCert

namespace ArctanCRT

/-- Binary modular powering, reducing after each square and multiply. -/
private lemma pow_bits (p a n : ℕ) :
    ((n.bits.foldr (fun b v => (if b then v*v*a else v*v)%p) 1 : ℕ) : ZMod p) = (a : ZMod p)^n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n hb ih =>
    rw [Nat.bits_append_bit n b hb,List.foldr_cons,ZMod.natCast_mod]
    cases b <;> simp [Nat.bit_val,Nat.cast_mul,ih,two_mul,pow_add]

/-- Lucas's criterion with the factors of the square root of `p-1` supplied explicitly. -/
private lemma from_witness (p k a : ℕ) (factors : List ℕ) (hs : p-1=k^2) (hf : factors.prod=k)
    (hp : ∀ q ∈ factors, q.Prime)
    (hc : let v (n : ℕ) := n.bits.foldr (fun b t => (if b then t*t*a else t*t)%p) 1
      v (p-1)=1 ∧ factors.all (fun q => decide ((v ((p-1)/q) : ZMod p) ≠ 1))=true) : p.Prime := by
  let v (n : ℕ) := n.bits.foldr (fun b t => (if b then t*t*a else t*t)%p) 1
  change v (p-1)=1 ∧ factors.all (fun q => decide ((v ((p-1)/q) : ZMod p) ≠ 1))=true at hc
  have hpow (n : ℕ) : (v n : ZMod p)=(a : ZMod p)^n := pow_bits p a n
  apply lucas_primality p (a : ZMod p)
  · rw [← hpow,hc.1,Nat.cast_one]
  · intro q hq hd
    have hmem : q ∈ factors := mem_list_primes_of_dvd_prod (Nat.prime_iff.mp hq)
      (fun b hb => Nat.prime_iff.mp (hp b hb)) (hf ▸ hq.dvd_of_dvd_pow (hs ▸ hd))
    have hv := of_decide_eq_true (List.all_eq_true.mp hc.2 q hmem)
    rwa [hpow] at hv

end ArctanCRT

namespace ArctanCRT


lemma prime_0 : Nat.Prime 999920001601 := by
  apply from_witness 999920001601 999960 17 [2, 2, 2, 3, 5, 13, 641]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_1 : Nat.Prime 999900002501 := by
  apply from_witness 999900002501 999950 3 [2, 5, 5, 7, 2857]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_2 : Nat.Prime 999892002917 := by
  apply from_witness 999892002917 999946 2 [2, 499973]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_3 : Nat.Prime 999868004357 := by
  apply from_witness 999868004357 999934 2 [2, 13, 38459]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_4 : Nat.Prime 999848005777 := by
  apply from_witness 999848005777 999924 5 [2, 2, 3, 103, 809]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_5 : Nat.Prime 999732017957 := by
  apply from_witness 999732017957 999866 2 [2, 7, 71419]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_6 : Nat.Prime 999672026897 := by
  apply from_witness 999672026897 999836 3 [2, 2, 43, 5813]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_7 : Nat.Prime 999628034597 := by
  apply from_witness 999628034597 999814 2 [2, 37, 59, 229]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_8 : Nat.Prime 999620036101 := by
  apply from_witness 999620036101 999810 13 [2, 3, 3, 3, 5, 7, 23, 23]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_9 : Nat.Prime 999568046657 := by
  apply from_witness 999568046657 999784 3 [2, 2, 2, 47, 2659]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

end ArctanCRT

namespace ArctanCRT

open Arxiv.«2607.05739»

private lemma difference_factor {p k : ℕ} {m R : ℤ}
    (hr : (R : ZMod p) = (k : ZMod p)) (hm : (m : ZMod p) = (k : ZMod p)) :
    (p : ℤ) ∣ m-R :=
  (ZMod.intCast_eq_intCast_iff_dvd_sub R m p).mp (hr.trans hm.symm)

private lemma fixed_factor {n p k : ℕ} {m R : ℤ} (hp : p.Prime)
    (lo : 1000000 ≤ n) (hi : n ≤ 900000000000) (hk : 1 ≤ k) (hkmax : k ≤ 1000000)
    (hpmin : 900001000000 < p) (hd : p ∣ 1+k^2) (hm : B n=A n*m)
    (hr : (R : ZMod p)=(k : ZMod p)) : (p : ℤ) ∣ m-R := by
  exact difference_factor hr (ArctanCert.signed_residue hp hk (hkmax.trans lo) (by omega) hd hm)

/-- Ten signed residue classes force any integer quotient in this range to have at least 120 digits. -/
lemma quotient_large {n : ℕ} {m : ℤ} (lo : 1000000 ≤ n) (hi : n ≤ 900000000000)
    (hm : B n = A n*m) : (10 : ℤ)^119 ≤ |m| := by
  let R : ℤ := 314538918741328110436849001151332386002465540153175519696217958824997488014743286934041729987811928674511392258630103331
  have d0 : (999920001601 : ℤ) ∣ m-R := fixed_factor (k:=999960) prime_0 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have d1 : (999900002501 : ℤ) ∣ m-R := fixed_factor (k:=999950) prime_1 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h1 : (999820012101639824004101 : ℤ) ∣ m-R :=
    (show IsCoprime (999920001601 : ℤ) (999900002501 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd d0 d1
  have d2 : (999892002917 : ℤ) ∣ m-R := fixed_factor (k:=999946) prime_2 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h2 : (999712034456807822203591923711962617 : ℤ) ∣ m-R :=
    (show IsCoprime (999820012101639824004101 : ℤ) (999892002917 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd h1 d2
  have d3 : (999868004357 : ℤ) ∣ m-R := fixed_factor (k:=999934) prime_3 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h3 : (999580076824004857699372730919082649547577122269 : ℤ) ∣ m-R :=
    (show IsCoprime (999712034456807822203591923711962617 : ℤ) (999868004357 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd h2 d3
  have d4 : (999848005777 : ℤ) ∣ m-R := fixed_factor (k:=999924) prime_4 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h4 : (999428146426901712773278489193259215504386356982768147348013 : ℤ) ∣ m-R :=
    (show IsCoprime (999580076824004857699372730919082649547577122269 : ℤ) (999848005777 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd h3 d4
  have d5 : (999732017957 : ℤ) ∣ m-R := fixed_factor (k:=999866) prime_5 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h5 : (999160317630390528502129306827917252477986914251362577824091354444269441 : ℤ) ∣ m-R :=
    (show IsCoprime (999428146426901712773278489193259215504386356982768147348013 : ℤ) (999732017957 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd h4 d5
  have d6 : (999672026897 : ℤ) ∣ m-R := fixed_factor (k:=999836) prime_6 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h6 : (998832619920622823713394653537049661369664474443902163517464308214596881110867154577 : ℤ) ∣ m-R :=
    (show IsCoprime (999160317630390528502129306827917252477986914251362577824091354444269441 : ℤ) (999672026897 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd h5 d6
  have d7 : (999628034597 : ℤ) ∣ m-R := fixed_factor (k:=999814) prime_7 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h7 : (998461088742624503416761102738248707316942093665690854248318962705653722371502207788168302900469 : ℤ) ∣ m-R :=
    (show IsCoprime (998832619920622823713394653537049661369664474443902163517464308214596881110867154577 : ℤ) (999628034597 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd h6 d7
  have d8 : (999620036101 : ℤ) ∣ m-R := fixed_factor (k:=999810) prime_8 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h8 : (998081709574346070802949931367700742761678238519024415148810130718388446593806068282810002306030724789831369 : ℤ) ∣ m-R :=
    (show IsCoprime (998461088742624503416761102738248707316942093665690854248318962705653722371502207788168302900469 : ℤ) (999620036101 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd h7 d8
  have d9 : (999568046657 : ℤ) ∣ m-R := fixed_factor (k:=999784) prime_9 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h9 : (997650584843308276910627682450584843863618748551605771183587982339952371712727296788521556256100797109197688367754183433 : ℤ) ∣ m-R :=
    (show IsCoprime (998081709574346070802949931367700742761678238519024415148810130718388446593806068282810002306030724789831369 : ℤ) (999568046657 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd h8 d9
  clear d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 h1 h2 h3 h4 h5 h6 h7 h8 lo hi hm
  obtain ⟨z,hz⟩ := h9
  dsimp [R] at hz
  by_contra! h
  obtain ⟨hl,hu⟩ := abs_lt.mp h
  norm_num at hl hu
  omega

end ArctanCRT

namespace ArctanWordCRT

open Arxiv.«2607.05739»

lemma prime_0 : Nat.Prime 63999977760001932101 := by
  apply ArctanCRT.from_witness 63999977760001932101 7999998610 2 [2, 5, 53, 193, 197, 397]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_1 : Nat.Prime 63999945216011723777 := by
  apply ArctanCRT.from_witness 63999945216011723777 7999996576 3 [2, 2, 2, 2, 2, 11, 13, 43, 109, 373]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_2 : Nat.Prime 63999942880012744901 := by
  apply ArctanCRT.from_witness 63999942880012744901 7999996430 2 [2, 5, 47, 97, 379, 463]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_3 : Nat.Prime 63999940544013808657 := by
  apply ArctanCRT.from_witness 63999940544013808657 7999996284 5 [2, 2, 3, 3, 7, 19, 71, 101, 233]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_4 : Nat.Prime 63999934464016777217 := by
  apply ArctanCRT.from_witness 63999934464016777217 7999995904 3 [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 19, 31, 829]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_5 : Nat.Prime 63999932384017859077 := by
  apply ArctanCRT.from_witness 63999932384017859077 7999995774 2 [2, 3, 37, 67, 593, 907]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_6 : Nat.Prime 63999923840022657601 := by
  apply ArctanCRT.from_witness 63999923840022657601 7999995240 31 [2, 2, 2, 3, 3, 3, 5, 23, 443, 727]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

private lemma signed_factor {n p k : ℕ} {m R : ℤ} (hp : p.Prime)
    (lo : 900000000000 ≤ n) (hi : n ≤ 18446744073709551615)
    (hk : 1≤k) (hkl : k≤900000000000) (hpmin : 18446744073709551615+k<p)
    (hd : p ∣ 1+k^2) (hm : B n=A n*m) (hR : (R : ZMod p)=(k : ZMod p)) : (p : ℤ) ∣ m-R :=
  (ZMod.intCast_eq_intCast_iff_dvd_sub R m p).mp
    (hR.trans (ArctanCert.signed_residue hp hk (hkl.trans lo) (by omega) hd hm).symm)

/-- All seven signs are fixed by the corresponding split-prime evaluations. -/
lemma joint_residue {n : ℕ} {m : ℤ} (lo : 900000000000≤n) (hi : n≤18446744073709551615)
    (hm : B n=A n*m) : (4398018823282643417813692926475385294712984070195663799519080465748185703914887245168684886935938141866859953671632117304449089521051196301:ℤ) ∣ m-(-578133431320477099269313245928101671987616903527324804914741378589609916690901804829913293726783226269011797614644529496127600122667986488) := by
  let R : ℤ := -578133431320477099269313245928101671987616903527324804914741378589609916690901804829913293726783226269011797614644529496127600122667986488
  have d0 : (63999977760001932101 : ℤ) ∣ m-R := signed_factor (k:=7999998610) prime_0 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have d1 : (63999945216011723777 : ℤ) ∣ m-R := signed_factor (k:=7999996576) prime_1 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h1 : (4095995070466092371985415000987521265477 : ℤ) ∣ m-R :=
    (show IsCoprime (63999977760001932101 : ℤ) (63999945216011723777 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd d0 d1
  have d2 : (63999942880012744901 : ℤ) ∣ m-R := signed_factor (k:=7999996430) prime_2 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h2 : (262143450546643689835539850627434313870944816814523899082777 : ℤ) ∣ m-R :=
    (show IsCoprime (4095995070466092371985415000987521265477 : ℤ) (63999942880012744901 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd h1 d2
  have d3 : (63999940544013808657 : ℤ) ∣ m-R := signed_factor (k:=7999996284) prime_3 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h3 : (16777165248987820297220722643512590539213048240464775236206103727551424682200489 : ℤ) ∣ m-R :=
    (show IsCoprime (262143450546643689835539850627434313870944816814523899082777 : ℤ) (63999940544013808657 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd h2 d3
  have d4 : (63999934464016777217 : ℤ) ∣ m-R := signed_factor (k:=7999995904) prime_4 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h4 : (1073737476427200215498362378219010105829188533897124652337242504275071346909624962439305329641459113 : ℤ) ∣ m-R :=
    (show IsCoprime (16777165248987820297220722643512590539213048240464775236206103727551424682200489 : ℤ) (63999934464016777217 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd h3 d4
  have d5 : (63999932384017859077 : ℤ) ∣ m-R := signed_factor (k:=7999995774) prime_5 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h5 : (68719125889526783650594720122289082963567266847347851388477413697860086182843326283279033505229539856809192592691418701 : ℤ) ∣ m-R :=
    (show IsCoprime (1073737476427200215498362378219010105829188533897124652337242504275071346909624962439305329641459113 : ℤ) (63999932384017859077 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd h4 d5
  have d6 : (63999923840022657601 : ℤ) ∣ m-R := signed_factor (k:=7999995240) prime_6 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h6 : (4398018823282643417813692926475385294712984070195663799519080465748185703914887245168684886935938141866859953671632117304449089521051196301 : ℤ) ∣ m-R :=
    (show IsCoprime (68719125889526783650594720122289082963567266847347851388477413697860086182843326283279033505229539856809192592691418701 : ℤ) (63999923840022657601 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd h5 d6
  exact h6

/-- The centered CRT representative minimizes the absolute value in its integer coset. -/
lemma least_absolute (z : ℤ) : |(-578133431320477099269313245928101671987616903527324804914741378589609916690901804829913293726783226269011797614644529496127600122667986488 : ℤ)| ≤ |(-578133431320477099269313245928101671987616903527324804914741378589609916690901804829913293726783226269011797614644529496127600122667986488)+4398018823282643417813692926475385294712984070195663799519080465748185703914887245168684886935938141866859953671632117304449089521051196301*z| := by
  by_contra! he
  obtain ⟨hl,hu⟩ := abs_lt.mp he
  norm_num at hl hu
  omega

lemma quotient_large {n : ℕ} {m : ℤ} (lo : 900000000000≤n) (hi : n≤18446744073709551615)
    (hm : B n=A n*m) : (10 : ℤ)^119 ≤ |m| := by
  obtain ⟨z,hz⟩ := joint_residue lo hi hm
  have he : m=(-578133431320477099269313245928101671987616903527324804914741378589609916690901804829913293726783226269011797614644529496127600122667986488)+4398018823282643417813692926475385294712984070195663799519080465748185703914887245168684886935938141866859953671632117304449089521051196301*z := by omega
  rw [he]
  exact (show (10:ℤ)^119 ≤ |(-578133431320477099269313245928101671987616903527324804914741378589609916690901804829913293726783226269011797614644529496127600122667986488 : ℤ)| by decide +kernel).trans (least_absolute z)

end ArctanWordCRT

namespace ArctanQuartic

open Arxiv.«2607.05739»

/-- A centered representative of a congruence class has the least absolute value. -/
private lemma centered {m R : ℤ} {P : ℕ} (hd : (P:ℤ) ∣ m-R) (hc : 2*R.natAbs ≤ P) :
    R.natAbs ≤ m.natAbs := by
  obtain ⟨z,hz⟩ := hd
  by_cases hzero : z=0
  · subst z
    have he : m=R := sub_eq_zero.mp (by simpa using hz)
    rw [he]
  · have hP : P ≤ (m-R).natAbs := by
      rw [hz, Int.natAbs_mul, Int.natAbs_natCast]
      exact Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr hzero)
    have hu : (m-R).natAbs ≤ m.natAbs + R.natAbs := by
      simpa only [sub_eq_add_neg, Int.natAbs_neg] using Int.natAbs_add_le m (-R)
    omega

/-- Simultaneously check the Lucas witnesses, the signed residues, and the
size of their centered Chinese remainder representative over one interval. -/
private lemma certified_interval {n : ℕ} {m : ℤ} (L U : ℕ) (R : ℤ)
    (seeds : List (ℕ × ℕ × List ℕ)) (lo : L≤n) (hi : n≤U) (hm : B n = A n*m)
    (numbers : seeds.all (fun z =>
      let k := z.1
      let p := k^2+1
      let f := z.2.2
      let v (e : ℕ) : ℕ := e.bits.foldr (fun b t => (if b then t*t*z.2.1 else t*t)%p) 1
      decide (1≤k ∧ k≤L ∧ U+k<p ∧ (R : ZMod p)=(k : ZMod p) ∧ f.prod=k ∧
        (f.all fun q => decide q.Prime) = true ∧ v (p-1)=1 ∧
        (f.all fun q => decide ((v ((p-1)/q) : ZMod p) ≠ 1))=true)) = true)
    (center : 2*R.natAbs ≤ ∏ k ∈ (seeds.map Prod.fst).toFinset, (k^2+1))
    (size : 1000*U^4 ≤ R.natAbs) : 1000*n^4 ≤ m.natAbs := by
  let S := (seeds.map Prod.fst).toFinset
  have valid (k : ℕ) (hk : k ∈ S) : (k^2+1).Prime ∧ ((k^2+1 : ℕ) : ℤ) ∣ m-R := by
    obtain ⟨⟨k',a,f⟩,hz,rfl⟩ := List.mem_map.mp ((List.mem_toFinset).mp hk)
    obtain ⟨h₁,hl,hu,hR,hprod,hpr,hpow,hall⟩ := of_decide_eq_true (List.all_eq_true.mp numbers _ hz)
    have hp : (k'^2+1).Prime := ArctanCRT.from_witness _ k' a f (by omega) hprod
      (fun q hq => of_decide_eq_true (List.all_eq_true.mp hpr _ hq)) ⟨hpow,hall⟩
    refine ⟨hp,?_⟩
    have hr := ArctanCert.signed_residue hp h₁ (hl.trans lo) ((Nat.add_le_add_right hi k').trans_lt hu)
      (by rw [Nat.add_comm]) hm
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub R m _).mp (hR.trans hr.symm)
  have hdiv : ((∏ k ∈ S, (k^2+1) : ℕ) : ℤ) ∣ m-R := by
    rw [Nat.cast_prod]
    apply Finset.prod_dvd_of_coprime
    · intro k hk l hl hne
      apply Int.isCoprime_iff_gcd_eq_one.mpr
      change (k^2+1).Coprime (l^2+1)
      apply (Nat.coprime_primes (valid k hk).1 (valid l hl).1).mpr
      intro he
      exact hne ((Nat.pow_left_inj (by decide : 2≠0)).mp (Nat.add_right_cancel he))
    · intro k hk
      exact (valid k hk).2
  exact (Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left hi 4)).trans
    (size.trans (centered hdiv center))

/-- The four interval certificates use eighteen prime occurrences in total. -/
theorem quotient_large_from_twenty {n : ℕ} {m : ℤ} (lo : 20≤n) (hi : n≤1000000)
    (hm : B n=A n*m) : 1000*n^4 ≤ m.natAbs := by
  by_cases h0 : n≤30
  · apply certified_interval 20 30 (5896798453 : ℤ)
      [(6,2,[2,3]), (10,2,[2,5]), (14,2,[2,7]), (16,3,[2,2,2,2]), (20,3,[2,2,5])] (by omega) (by omega) hm
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h1 : n≤182
  · apply certified_interval 26 182 (-1698150490433 : ℤ)
      [(14,2,[2,7]), (16,3,[2,2,2,2]), (20,3,[2,2,5]), (24,5,[2,2,2,3]), (26,2,[2,13])] (by omega) (by omega) hm
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h2 : n≤3989
  · apply certified_interval 180 3989 (-253427541365267386 : ℤ)
      [(150,2,[2,3,5,5]), (160,3,[2,2,2,2,2,5]), (170,3,[2,5,17]), (180,7,[2,2,3,3,5])] (by omega) (by omega) hm
    · decide +kernel
    · decide +kernel
    · decide +kernel
  apply certified_interval 3794 1000000 (4601120673004199893601159536 : ℤ)
    [(3776,3,[2,2,2,2,2,2,59]), (3784,3,[2,2,2,11,43]), (3790,2,[2,5,379]), (3794,2,[2,7,271])] (by omega) (by omega) hm
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- Every integral quotient between 64 and one million has quartic size. -/
theorem quotient_large {n : ℕ} {m : ℤ} (lo : 64≤n) (hi : n≤1000000)
    (hm : B n=A n*m) : 1000*n^4 ≤ m.natAbs :=
  quotient_large_from_twenty (by omega) hi hm

end ArctanQuartic

namespace ArctanPhase

open Arxiv.«2607.05739»

/-- Every integer quotient from index one million onward has absolute value
at least one thousand times the fourth power of the index. -/
theorem quartic_above_million {n : ℕ} {m : ℤ} (hn : 1000000 ≤ n)
    (hm : B n = A n*m) : 1000*n^4 ≤ m.natAbs := by
  by_cases high : 2^64 ≤ n
  · exact (quartic_le_exp high).trans (ArctanGlobal.quotient_exponential high hm)
  have cap : n ≤ 18446744073709551615 := by omega
  have magnitude : (10 : ℤ)^119 ≤ |m| := by
    by_cases first : n ≤ 900000000000
    · exact ArctanCRT.quotient_large hn first hm
    · exact ArctanWordCRT.quotient_large (by omega) cap hm
  have natural : (10 : ℕ)^119 ≤ m.natAbs := by
    exact_mod_cast magnitude.trans_eq (Int.natCast_natAbs m).symm
  calc
    1000*n^4 ≤ 1000*(18446744073709551615:ℕ)^4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left cap 4)
    _ ≤ 10^119 := by decide
    _ ≤ m.natAbs := natural

end ArctanPhase

/- The scaled-coordinate proof was contributed by HudZah in Left to Solve PR #327.
   https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/327 -/
namespace ArctanTrigBridge
open Arxiv.«2607.05739» Finset

-- The cosine and sine are the two integer coordinates times the same positive factor.
lemma scaled_coordinates (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧
      Real.cos (∑ k ∈ Icc 1 n, Real.arctan k) = c * (A n : ℝ) ∧
      Real.sin (∑ k ∈ Icc 1 n, Real.arctan k) = c * (B n : ℝ) := by
  induction n with
  | zero =>
    exact ⟨1, zero_lt_one, by norm_num [A, gaussProd], by norm_num [B, gaussProd]⟩
  | succ n ih =>
    obtain ⟨c, hc, hcos, hsin⟩ := ih
    let t : ℝ := (n + 1 : ℕ)
    have ht := Real.cos_arctan_pos t
    have hs : Real.sin (Real.arctan t) = t * Real.cos (Real.arctan t) := by
      apply (div_eq_iff ht.ne').mp
      rw [← Real.tan_eq_sin_div_cos, Real.tan_arctan]
    have hp : gaussProd (n + 1) = gaussProd n * (⟨1, (n + 1 : ℕ)⟩ : GaussianInt) := by
      unfold gaussProd
      rw [prod_Icc_succ_top (by omega)]
    have ha : (A (n + 1) : ℝ) = A n - t * B n := by
      simp [A, B, hp, t, sub_eq_add_neg]
      ring
    have hb : (B (n + 1) : ℝ) = t * A n + B n := by
      simp [A, B, hp, t]
      ring
    refine ⟨c * Real.cos (Real.arctan t), mul_pos hc ht, ?_, ?_⟩
    · rw [sum_Icc_succ_top (by omega), Real.cos_add, hcos, hsin, ha]
      change _ - _ * Real.sin (Real.arctan t) = _
      rw [hs]
      ring
    · rw [sum_Icc_succ_top (by omega), Real.sin_add, hcos, hsin, hb]
      change _ + _ * Real.sin (Real.arctan t) = _
      rw [hs]
      ring

end ArctanTrigBridge


namespace ArctanGlobalSpacing

open Arxiv.«2607.05739» Finset

private lemma arctan_upper {t : ℝ} (ht : 0 ≤ t) : Real.arctan t ≤ t := by
  simpa only [Real.tan_arctan] using
    Real.le_tan (Real.arctan_nonneg.mpr ht) (Real.arctan_lt_pi_div_two t)

private lemma arctan_abs (t : ℝ) : |Real.arctan t| ≤ |t| := by
  rcases le_or_gt 0 t with h | h
  · simpa [abs_of_nonneg h, abs_of_nonneg (Real.arctan_nonneg.mpr h)] using arctan_upper h
  · simpa [abs_of_nonpos h.le, abs_of_nonpos (Real.arctan_le_zero.mpr h.le)] using
      arctan_upper (neg_nonneg.mpr h.le)

private lemma complementary_angles (n : ℕ) :
    (∑ j ∈ Icc 1 n, Real.arctan j) + angleSum n = (n:ℝ)*(Real.pi/2) := by
  unfold angleSum
  rw [← sum_add_distrib]
  calc
    _ = ∑ _j ∈ Icc 1 n, Real.pi/2 := by
      apply sum_congr rfl
      intro j hj
      have hp : 0 < (j:ℝ) := by exact_mod_cast (mem_Icc.mp hj).1
      rw [one_div,Real.arctan_inv_of_pos hp]
      ring
    _ = _ := by simp [Nat.card_Icc,nsmul_eq_mul]

end ArctanGlobalSpacing

namespace ArctanPhase

open Arxiv.«2607.05739» Finset

/-- The sign of the reciprocal slope and the parity of the relevant
half-period are both determined by the Gaussian coordinates. -/
theorem signed_grid {n : ℕ} {m : ℤ} (hm : B n = A n*m) (hm₀ : m ≠ 0) :
    ∃ j : ℤ, Odd ((n:ℤ)-j) ∧
      angleSum n - (j:ℝ)*(Real.pi/2) = Real.arctan (1/(m:ℝ)) ∧
      |angleSum n - (j:ℝ)*(Real.pi/2)| ≤ 1/|(m:ℝ)| := by
  let θ := ∑ k ∈ Icc 1 n, Real.arctan k
  let ε := Real.arctan (1/(m:ℝ))
  obtain ⟨c,_hc,hcos,hsin⟩ := ArctanTrigBridge.scaled_coordinates n
  have hε : Real.sin ε = (1/(m:ℝ)) * Real.cos ε := by
    apply (div_eq_iff (Real.cos_arctan_pos _).ne').mp
    exact (Real.tan_eq_sin_div_cos _).symm.trans (Real.tan_arctan _)
  have zm : (m:ℝ) ≠ 0 := by exact_mod_cast hm₀
  have hzero : Real.cos (θ+ε) = 0 := by
    rw [Real.cos_add,hε]
    dsimp only [θ]
    rw [hcos,hsin,hm,Int.cast_mul]
    field_simp
    ring
  obtain ⟨r,hr⟩ := Real.cos_eq_zero_iff.mp hzero
  let j : ℤ := n-(2*r+1)
  have odd : Odd ((n:ℤ)-j) := ⟨r,by dsimp [j]; ring⟩
  have hs := ArctanGlobalSpacing.complementary_angles n
  change θ+angleSum n = _ at hs
  have he : angleSum n - (j:ℝ)*(Real.pi/2) = ε := by
    dsimp only [j]
    push_cast
    linarith only [hs,hr]
  refine ⟨j,odd,he,?_⟩
  rw [he]
  simpa only [ε,abs_div,abs_one] using ArctanGlobalSpacing.arctan_abs (1/(m:ℝ))

end ArctanPhase

namespace ArctanGlobal.WordPrimes

/-- Binary modular powering, reducing after each square and multiply. -/
private lemma pow_bits (p a n : ℕ) :
    ((n.bits.foldr (fun b v => (if b then v*v*a else v*v)%p) 1 : ℕ) : ZMod p) = (a : ZMod p)^n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n hb ih =>
    rw [Nat.bits_append_bit n b hb,List.foldr_cons,ZMod.natCast_mod]
    cases b <;> simp [Nat.bit_val,Nat.cast_mul,ih,two_mul,pow_add]

/-- Lucas's criterion with the factors of the square root of `p-1` supplied explicitly. -/
private lemma from_witness (p k a : ℕ) (factors : List ℕ) (hs : p-1=k^2) (hf : factors.prod=k)
    (hp : ∀ q ∈ factors, q.Prime)
    (hc : let v (n : ℕ) := n.bits.foldr (fun b t => (if b then t*t*a else t*t)%p) 1
      v (p-1)=1 ∧ factors.all (fun q => decide ((v ((p-1)/q) : ZMod p) ≠ 1))=true) : p.Prime := by
  let v (n : ℕ) := n.bits.foldr (fun b t => (if b then t*t*a else t*t)%p) 1
  change v (p-1)=1 ∧ factors.all (fun q => decide ((v ((p-1)/q) : ZMod p) ≠ 1))=true at hc
  have hpow (n : ℕ) : (v n : ZMod p)=(a : ZMod p)^n := pow_bits p a n
  apply lucas_primality p (a : ZMod p)
  · rw [← hpow,hc.1,Nat.cast_one]
  · intro q hq hd
    have hmem : q ∈ factors := mem_list_primes_of_dvd_prod (Nat.prime_iff.mp hq)
      (fun b hb => Nat.prime_iff.mp (hp b hb)) (hf ▸ hq.dvd_of_dvd_pow (hs ▸ hd))
    have hv := of_decide_eq_true (List.all_eq_true.mp hc.2 q hmem)
    rwa [hpow] at hv

lemma bridge : Nat.Prime 2005057 := by
  apply from_witness 2005057 1416 5 [2, 2, 2, 3, 59]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma million : Nat.Prime 999920001601 := by
  apply from_witness 999920001601 999960 17 [2, 2, 2, 3, 5, 13, 641]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma word : Nat.Prime 63999977760001932101 := by
  apply from_witness 63999977760001932101 7999998610 2 [2, 5, 53, 193, 197, 397]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

end ArctanGlobal.WordPrimes

namespace ArctanGlobal

/-- A factor k²+1 divisible by a prime exceeding twice the upper endpoint
gives that prime valuation exactly one throughout the product. -/
theorem norm_simple_prime {n k p : ℕ} (hk : k ∈ Finset.Icc 1 n) (hp : p.Prime)
    (hbig : 2*n<p) (hkdiv : p ∣ k^2+1) :
    (∏ i ∈ Finset.Icc 1 n, (i^2+1)).factorization p = 1 ∧
      ¬IsSquare (∏ i ∈ Finset.Icc 1 n, (i^2+1)) := by
  let P := ∏ i ∈ Finset.Icc 1 n, (i^2+1)
  have hpos : 0<P := Finset.prod_pos fun i _ => Nat.succ_pos (i^2)
  have hd : p∣P := hkdiv.trans (Finset.dvd_prod_of_mem (fun i => i^2+1) hk)
  have h₁ : P.factorization p=1 :=
    le_antisymm (large_order_le_one n hp hbig) ((hp.dvd_iff_one_le_factorization hpos.ne').mp hd)
  refine ⟨h₁,?_⟩
  rintro ⟨b,hb⟩
  change P=b*b at hb
  have hbn : b≠0 := by rintro rfl; simp [hb] at hpos
  rw [hb, Nat.factorization_mul hbn hbn, Finsupp.add_apply] at h₁
  omega

/-- A short chain of overlapping ranges supplies a prime factor k²+1
larger than 2n for every index below 2⁶⁴ starting at four. -/
theorem word_large_prime {n : ℕ} (lo : 4≤n) (hi : n<2^64) :
    ∃ k ∈ Finset.Icc 1 n, (k^2+1).Prime ∧ 2*n<k^2+1 := by
  by_cases h₆ : n<6
  · exact ⟨4, Finset.mem_Icc.mpr ⟨by decide,lo⟩, by decide, by omega⟩
  by_cases h₁₀ : n<10
  · exact ⟨6, Finset.mem_Icc.mpr ⟨by decide,by omega⟩, by decide, by omega⟩
  by_cases h₃₆ : n<36
  · exact ⟨10, Finset.mem_Icc.mpr ⟨by decide,by omega⟩, by decide, by omega⟩
  by_cases h₂₅₆ : n<256
  · exact ⟨36, Finset.mem_Icc.mpr ⟨by decide,by omega⟩, by norm_num, by omega⟩
  by_cases hbridge : n<1416
  · exact ⟨256, Finset.mem_Icc.mpr ⟨by decide,by omega⟩, by norm_num, by omega⟩
  by_cases hmillion : n<999960
  · exact ⟨1416, Finset.mem_Icc.mpr ⟨by decide,by omega⟩, WordPrimes.bridge, by omega⟩
  by_cases hword : n<7999998610
  · exact ⟨999960, Finset.mem_Icc.mpr ⟨by decide,by omega⟩, WordPrimes.million, by omega⟩
  exact ⟨7999998610, Finset.mem_Icc.mpr ⟨by decide,by omega⟩, WordPrimes.word, by omega⟩

theorem norm_not_square_word {n : ℕ} (lo : 4≤n) (hi : n<2^64) :
    ¬IsSquare (∏ k ∈ Finset.Icc 1 n, (k^2+1)) := by
  obtain ⟨k,hk,hp,hbig⟩ := word_large_prime lo hi
  exact (norm_simple_prime hk hp hbig dvd_rfl).2

end ArctanGlobal

namespace ArctanGlobal

open Arxiv.«2607.05739»

/-- Cilleruelo's non-square theorem, with an explicit large-index estimate and
a short finite chain of odd primes covering the remaining indices. -/
theorem norm_ne_square {n : ℕ} (hn : 4≤n) :
    ¬ IsSquare (∏ k ∈ Finset.Icc 1 n, (k^2+1)) := by
  by_cases small : n<2^64
  · exact norm_not_square_word hn small
  rintro ⟨b,hb⟩
  exact norm_not_square_large (n:=n) (b:=b) (by omega) (by simpa only [pow_two] using hb)

/-- The factorial Gaussian product has nonzero real part at every natural index. -/
theorem real_ne_zero (n : ℕ) : A n≠0 := by
  by_cases early : n≤3
  · interval_cases n <;> decide
  intro h
  apply norm_ne_square (n:=n) (by omega)
  refine ⟨(B n).natAbs,?_⟩
  rw [product_norm,h]
  simp [pow_two]

/-- The ordinary real tangent has no poles at any of these arctangent sums. -/
theorem cosine_ne_zero (n : ℕ) : Real.cos (∑ j ∈ Finset.Icc 1 n, Real.arctan j) ≠ 0 := by
  obtain ⟨c,hc,cosine,_⟩ := ArctanTrigBridge.scaled_coordinates n
  rw [cosine]
  exact mul_ne_zero hc.ne' (by exact_mod_cast real_ne_zero n)

end ArctanGlobal

namespace ArctanEffective

open Arxiv.«2607.05739» Finset

/-- No pole exception is needed at any index. -/
lemma tangent_eq_iff (n : ℕ) (m : ℤ) :
    Real.tan (∑ j ∈ Icc 1 n,Real.arctan j)=(m:ℝ) ↔ B n=A n*m := by
  obtain ⟨c,hc,cosine,sine⟩ := ArctanTrigBridge.scaled_coordinates n
  have ha : (A n:ℝ) ≠ 0 := by exact_mod_cast ArctanGlobal.real_ne_zero n
  rw [Real.tan_eq_sin_div_cos,sine,cosine,mul_div_mul_left _ _ hc.ne',div_eq_iff ha]
  constructor
  · intro h
    rw [mul_comm] at h
    exact_mod_cast h
  · intro h
    rw [h,Int.cast_mul,mul_comm]

end ArctanEffective

namespace ArctanCert.Periodic

open Arxiv.«2607.05739»

private lemma coordinate_succ (n : ℕ) :
    A (n+1) = A n - B n * ((n:ℤ)+1) ∧
      B (n+1) = A n * ((n:ℤ)+1) + B n := by
  have h : gaussProd (n+1) = gaussProd n * (⟨1, ((n+1:ℕ):ℤ)⟩ : GaussianInt) := by
    exact Finset.prod_Icc_succ_top (by omega : 1≤n+1) _
  constructor <;> simp [A, B, h, Zsqrtd.re_mul, Zsqrtd.im_mul]
  ring

private lemma coordinate_mod_succ (p n : ℕ) :
    (A (n+1) : ZMod p) = (A n : ZMod p) - (B n : ZMod p)*((n:ZMod p)+1) ∧
      (B (n+1) : ZMod p) = (A n : ZMod p)*((n:ZMod p)+1) + (B n : ZMod p) := by
  obtain ⟨ha,hb⟩ := coordinate_succ n
  simp [ha,hb]

/-- A purely real block multiplier propagates over any following prefix. -/
theorem shift {p : ℕ} (hb : (B p : ZMod p) = 0) (n : ℕ) :
    (A (p+n) : ZMod p) = (A p : ZMod p) * (A n : ZMod p) ∧
      (B (p+n) : ZMod p) = (A p : ZMod p) * (B n : ZMod p) := by
  induction n with
  | zero =>
    have hA : A 0 = 1 := by decide
    have hB : B 0 = 0 := by decide
    simp [hb,hA,hB]
  | succ n ih =>
    obtain ⟨aa,bb⟩ := coordinate_mod_succ p (p+n)
    obtain ⟨a,b⟩ := coordinate_mod_succ p n
    rw [Nat.add_succ, aa, bb, a, b, ih.1, ih.2]
    simp only [Nat.cast_add, ZMod.natCast_self, zero_add]
    constructor <;> ring

/-- Complete p-blocks scale both original coordinates by the same residue. -/
theorem coordinates_mod {p : ℕ} (hb : (B p : ZMod p) = 0) (n : ℕ) :
    (A n : ZMod p) = (A p : ZMod p)^(n/p) * (A (n%p) : ZMod p) ∧
      (B n : ZMod p) = (A p : ZMod p)^(n/p) * (B (n%p) : ZMod p) := by
  have blocks (r k : ℕ) :
      (A (p*k+r) : ZMod p) = (A p : ZMod p)^k * (A r : ZMod p) ∧
        (B (p*k+r) : ZMod p) = (A p : ZMod p)^k * (B r : ZMod p) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have h := shift hb (p*k+r)
      rw [show p*(k+1)+r = p+(p*k+r) by ring, h.1, h.2, ih.1, ih.2, pow_succ]
      constructor <;> ring
  simpa only [Nat.div_add_mod] using blocks (n%p) (n/p)

/-- A good prime excludes every index in a residue class where it divides
the real coordinate and does not divide the imaginary coordinate. -/
theorem not_integer_of_residue {p n : ℕ} (hp : Nat.Prime p)
    (hpb : (p:ℤ) ∣ B p) (hpa : ¬(p:ℤ) ∣ A p)
    (hra : (p:ℤ) ∣ A (n%p)) (hrb : ¬(p:ℤ) ∣ B (n%p)) : ¬ IsIntegerValue n := by
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  have hα : (A p : ZMod p) ≠ 0 := fun h => hpa ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  have hβ : (B (n%p) : ZMod p) ≠ 0 := fun h => hrb ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  obtain ⟨ha,hb⟩ := coordinates_mod ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpb) n
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hra, mul_zero] at ha
  have hB : (B n : ZMod p) ≠ 0 := hb ▸ mul_ne_zero (pow_ne_zero _ hα) hβ
  intro hab
  exact hB ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    (((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ha).trans hab))

theorem not_integer_mod_nineteen {n : ℕ} (h : n%19=5 ∨ n%19=13) : ¬ IsIntegerValue n := by
  apply not_integer_of_residue (p:=19) (by decide) (by decide) (by decide)
  · rcases h with h | h <;> rw [h] <;> decide
  · rcases h with h | h <;> rw [h] <;> decide

end ArctanCert.Periodic

namespace ArctanCert.Periodic

open Arxiv.«2607.05739»
open Polynomial
open scoped QuadraticAlgebra

/-- Evaluate the splitting of X^q-X at an arbitrary point of a commutative algebra. -/
private lemma finite_product {K S : Type*} [Field K] [Fintype K] [CommRing S] [Algebra K S] (z : S) :
    (∏ k : K, (z - algebraMap K S k)) = z^(Fintype.card K) - z := by
  classical
  let f : K[X] := X ^ (Fintype.card K) - X
  have hr : f.roots = Finset.univ.val := FiniteField.roots_X_pow_card_sub_X K
  have hm : f.Monic := Polynomial.monic_X_pow_sub (by simpa using (Fintype.one_lt_card (α:=K)))
  have hd : f.natDegree = Fintype.card K :=
    FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card
  have hp := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm (by rw [hr,hd]; rfl)
  rw [hr] at hp
  change (∏ k : K, (X-C k)) = f at hp
  simpa [f] using congrArg (Polynomial.aeval z) hp

/-- The integers from 1 through p represent all residues, including zero exactly once. -/
private lemma full_residues {p : ℕ} [NeZero p] {S : Type*} [CommMonoid S] (f : ZMod p → S) :
    (∏ k ∈ Finset.Icc 1 p, f (k : ZMod p)) = ∏ k : ZMod p, f k := by
  let e : ZMod p ≃ Fin p := {
    toFun := fun k => ⟨k.val,k.val_lt⟩
    invFun := fun i => (i.val : ZMod p)
    left_inv := fun k => ZMod.natCast_zmod_val k
    right_inv := fun i => Fin.ext (by simp [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt]) }
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_cancel_right, Nat.cast_add, Nat.cast_one]
  rw [← Fin.prod_univ_eq_prod_range (fun k : ℕ => f (1+(k:ZMod p)))]
  exact (e.symm.trans (Equiv.addLeft 1)).prod_comp f

private lemma fourth_root_power {R : Type*} [CommRing R] (z : R) (hz : z^2 = -1)
    {p : ℕ} (h : p%4=3) : z^p = -z := by
  have h₄ : z^4 = 1 := by rw [show 4 = 2*2 by decide, pow_mul, hz]; ring
  have h₃ : z^3 = -z := by rw [pow_succ, hz, neg_one_mul]
  calc
    z^p = z^(4*(p/4)+3) := congrArg (z^·) (by omega)
    _ = -z := by rw [pow_add,pow_mul,h₄,one_pow,one_mul,h₃]

/-- For primes congruent to three modulo four, one complete Gaussian
block has real coordinate two and imaginary coordinate zero modulo p. -/
theorem inert_block {p : ℕ} (hp : Nat.Prime p) (h : p%4=3) :
    (A p : ZMod p) = 2 ∧ (B p : ZMod p) = 0 := by
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  let j : QuadraticAlgebra (ZMod p) (-1) 0 := QuadraticAlgebra.omega
  let ι := algebraMap (ZMod p) (QuadraticAlgebra (ZMod p) (-1) 0)
  let φ : GaussianInt →+* QuadraticAlgebra (ZMod p) (-1) 0 := {
    toFun := fun z => ⟨(z.re : ZMod p), (z.im : ZMod p)⟩
    map_zero' := by ext <;> simp
    map_one' := by ext <;> simp
    map_add' := by intro z w; ext <;> simp
    map_mul' := by intro z w; ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul] }
  have hj : j^2 = -1 := by ext <;> simp [j, pow_two]
  have hφ (k : ℕ) : φ (⟨1,(k:ℤ)⟩ : GaussianInt) = 1+j*ι (k : ZMod p) := by
    ext <;> simp [φ,j,ι]
  have hf (k : ZMod p) : 1+j*ι k = (-j)*(j-ι k) := by
    linear_combination hj
  have hblock : φ (gaussProd p) = 2 := calc
    _ = ∏ k ∈ Finset.Icc 1 p, (1+j*ι (k:ZMod p)) := by
      rw [gaussProd, map_prod]; exact Finset.prod_congr rfl fun k _ => hφ k
    _ = ∏ k : ZMod p, (1+j*ι k) := full_residues (fun k => 1+j*ι k)
    _ = (-j)^p * (j^p-j) := by
      simp only [hf, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ZMod.card]
      rw [finite_product j, ZMod.card]
    _ = 2 := by
      rw [fourth_root_power j hj h, fourth_root_power (-j) (by simpa using hj) h]
      linear_combination -2*hj
  exact ⟨congrArg QuadraticAlgebra.re hblock, congrArg QuadraticAlgebra.im hblock⟩

theorem inert_good {p : ℕ} (hp : Nat.Prime p) (h : p%4=3) :
    (p:ℤ) ∣ B p ∧ ¬ (p:ℤ) ∣ A p := by
  obtain ⟨ha,hb⟩ := inert_block hp h
  refine ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb, ?_⟩
  intro hz
  have h₂ : (2 : ZMod p) = 0 := ha.symm.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hz)
  have hn : (p:ℤ) ∣ (2:ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by simpa using h₂)
  have hd : p ∣ 2 := by exact_mod_cast hn
  have := Nat.le_of_dvd (by decide) hd
  omega

end ArctanCert.Periodic

namespace ArctanPhase

open Arxiv.«2607.05739»

/-- The two Gaussian coordinates cannot both vanish modulo a prime congruent
to three modulo four, since that prime has order zero in their squared norm. -/
theorem inert_not_common (n : ℕ) {p : ℕ} (hp : p.Prime) (hmod : p%4=3) :
    ¬ ((p:ℤ) ∣ A n ∧ (p:ℤ) ∣ B n) := by
  rintro ⟨ha,hb⟩
  let P := ∏ k ∈ Finset.Icc 1 n, (k^2+1)
  have hpos : 0 < P := Finset.prod_pos fun k _ => by positivity
  have hi : (p:ℤ) ∣ (P:ℤ) := by
    dsimp only [P]
    rw [ArctanGlobal.product_norm_int,pow_two,pow_two]
    exact dvd_add (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_left hb _)
  have hn : p ∣ P := by exact_mod_cast hi
  have hv := hp.factorization_pos_of_dvd hpos.ne' hn
  have hz : P.factorization p = 0 := ArctanGlobal.inert_order_zero n hp hmod
  omega

/-- At an integral quotient an inert prime cannot divide the real coordinate. -/
theorem inert_not_dvd_A {n p : ℕ} {m : ℤ} (hp : p.Prime) (hmod : p%4=3)
    (hm : B n = A n*m) : ¬(p:ℤ) ∣ A n := by
  intro ha
  exact inert_not_common n hp hmod ⟨ha,hm ▸ dvd_mul_of_dvd_left ha m⟩

/-- The denominator can be cancelled modulo the inert prime. -/
theorem inert_A_ne_zero_mod {n p : ℕ} {m : ℤ} (hp : p.Prime) (hmod : p%4=3)
    (hm : B n = A n*m) : (A n : ZMod p) ≠ 0 := fun hz =>
  inert_not_dvd_A hp hmod hm ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)

end ArctanPhase

namespace ArctanPhase

open Arxiv.«2607.05739»

/-- All complete periods contribute the same real scalar modulo the period. -/
theorem coordinates_modEq {p : ℕ} {s : ℤ}
    (ha : A p ≡ s [ZMOD (p : ℤ)]) (hb : B p ≡ 0 [ZMOD (p : ℤ)]) (n : ℕ) :
    A n ≡ s^(n/p)*A (n%p) [ZMOD (p : ℤ)] ∧
    B n ≡ s^(n/p)*B (n%p) [ZMOD (p : ℤ)] := by
  have hs := (ZMod.intCast_eq_intCast_iff _ _ p).mpr ha
  have hz : (B p : ZMod p)=0 := by
    simpa only [Int.cast_zero] using (ZMod.intCast_eq_intCast_iff _ _ p).mpr hb
  obtain ⟨hA,hB⟩ := ArctanCert.Periodic.coordinates_mod hz n
  constructor
  · apply (ZMod.intCast_eq_intCast_iff _ _ p).mp
    simpa only [hs,Int.cast_mul,Int.cast_pow] using hA
  · apply (ZMod.intCast_eq_intCast_iff _ _ p).mp
    simpa only [hs,Int.cast_mul,Int.cast_pow] using hB

/-- The complete-period scalar is two for every prime congruent to three modulo four. -/
theorem inert_coordinates_modEq {p : ℕ} (hp : p.Prime) (hm : p%4=3) (n : ℕ) :
    A n ≡ 2^(n/p)*A (n%p) [ZMOD (p : ℤ)] ∧
    B n ≡ 2^(n/p)*B (n%p) [ZMOD (p : ℤ)] := by
  obtain ⟨ha,hb⟩ := ArctanCert.Periodic.inert_block hp hm
  apply coordinates_modEq
  · exact (ZMod.intCast_eq_intCast_iff _ _ p).mp (by simpa using ha)
  · exact (ZMod.intCast_eq_intCast_iff _ _ p).mp (by simpa using hb)

/-- At these primes, divisibility of either coordinate is determined by the residue of the index. -/
theorem inert_dvd_iff {p : ℕ} (hp : p.Prime) (hm : p%4=3) (n : ℕ) :
    ((p:ℤ) ∣ A n ↔ (p:ℤ) ∣ A (n%p)) ∧ ((p:ℤ) ∣ B n ↔ (p:ℤ) ∣ B (n%p)) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨divB,nondivA⟩ := ArctanCert.Periodic.inert_good hp hm
  have hne : (A p : ZMod p)≠0 := fun h => nondivA ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  have block := ArctanCert.Periodic.coordinates_mod ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr divB) n
  simp only [← ZMod.intCast_zmod_eq_zero_iff_dvd,block.1,block.2,mul_eq_zero,pow_ne_zero _ hne,false_or]
  exact ⟨trivial,trivial⟩

end ArctanPhase

namespace ArctanPhase.ExplicitPoles

open Arxiv.«2607.05739»

private lemma next_pair (p k : ℕ) :
    (A (k+1) : ZMod p) = (A k : ZMod p)-(k+1 : ℕ)*(B k : ZMod p) ∧
    (B (k+1) : ZMod p) = (k+1 : ℕ)*(A k : ZMod p)+(B k : ZMod p) := by
  have h : gaussProd (k+1) = gaussProd k * (⟨1, ((k+1:ℕ):ℤ)⟩ : GaussianInt) :=
    Finset.prod_Icc_succ_top (by omega : 1≤k+1) _
  constructor <;> simp [A,B,h,Zsqrtd.re_mul,Zsqrtd.im_mul] <;> ring

private lemma scan_rule (p : ℕ) (rs : List ℕ) :
    let step (state : (ZMod p × ZMod p) × Bool) (k : ℕ) :=
      let a := state.1.1
      let b := state.1.2
      ((a-(k+1 : ℕ)*b,(k+1 : ℕ)*a+b),state.2 && decide ((a=0) ↔ k∈rs))
    ((List.range p).foldl step ((1,0),true)).2=true → ∀ k<p, ((A k : ZMod p)=0 ↔ k∈rs) := by
  let step (state : (ZMod p × ZMod p) × Bool) (k : ℕ) :=
      let a := state.1.1
      let b := state.1.2
      ((a-(k+1 : ℕ)*b,(k+1 : ℕ)*a+b),state.2 && decide ((a=0) ↔ k∈rs))
  let run (n : ℕ) := (List.range n).foldl step ((1,0),true)
  change (run p).2=true → _
  have spec (n : ℕ) : (run n).1.1=(A n : ZMod p) ∧ (run n).1.2=(B n : ZMod p) ∧
      ((run n).2=true → ∀ k<n, ((A k : ZMod p)=0 ↔ k∈rs)) := by
    induction n with
    | zero => simp [run,A,B,gaussProd]
    | succ n ih =>
      have he : run (n+1)=step (run n) n := by simp [run,List.range_succ]
      rw [he]
      obtain ⟨h₁,h₂,hgot⟩ := ih
      obtain ⟨ha,hb⟩ := next_pair p n
      refine ⟨?_,?_,?_⟩
      · simp only [step,h₁,h₂,ha]
      · simp only [step,h₁,h₂,hb]
      · intro h k hk
        have hh := Bool.and_eq_true_iff.mp h
        by_cases hn : k<n
        · exact hgot hh.1 k hn
        · obtain rfl : k=n := by omega
          simpa only [decide_eq_true_eq,h₁] using hh.2
  exact (spec p).2.2

private lemma table_rule (T : List (ℕ × List ℕ))
    (hc : T.all (fun v =>
      let p := v.1
      let rs := v.2
      let step (state : (ZMod p × ZMod p) × Bool) (k : ℕ) :=
        let a := state.1.1
        let b := state.1.2
        ((a-(k+1 : ℕ)*b,(k+1 : ℕ)*a+b),state.2 && decide ((a=0) ↔ k∈rs))
      decide p.Prime && decide (p%4=3) && ((List.range p).foldl step ((1,0),true)).2)=true) :
    ∀ (p : ℕ) (rs : List ℕ), (p,rs)∈T → p.Prime ∧ p%4=3 ∧
      (∀ k<p, ((p : ℤ) ∣ A k ↔ k∈rs)) ∧ (∀ n : ℕ,n%p∈rs → ¬IsIntegerValue n) := by
  intro p rs hh
  have h := List.all_eq_true.mp hc (p,rs) hh
  obtain ⟨⟨hp,hi⟩,hz⟩ := (Bool.and_eq_true_iff.mp h).imp_left Bool.and_eq_true_iff.mp
  have prime : p.Prime := of_decide_eq_true hp
  have inert : p%4=3 := of_decide_eq_true hi
  have he (k : ℕ) (hk : k<p) : (p : ℤ) ∣ A k ↔ k∈rs :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).symm.trans (scan_rule p rs hz k hk)
  refine ⟨prime,inert,he,?_⟩
  rintro n hn ⟨m,hm⟩
  exact ArctanPhase.inert_not_dvd_A prime inert hm ((ArctanPhase.inert_dvd_iff prime inert n).1.mpr
    ((he _ (Nat.mod_lt _ prime.pos)).mpr hn))

/-- Complete zero-residue sets for these 22 inert primes; each listed residue excludes all indices in its class. -/
lemma explicit_inert_residues :
    ∀ (p : ℕ) (rs : List ℕ), (p,rs) ∈ ([(19,[5,13]), (43,[8,34]), (71,[23,47]), (79,[38,40]), (83,[11,71]), (131,[11,119]), (163,[27,135]), (191,[81,109]), (199,[19,30,59,139,168,179]), (211,[76,134]), (223,[49,173]), (227,[65,161]), (263,[70,192]), (311,[83,227]), (331,[7,77,253,323]), (347,[10,110,236,336]), (379,[151,227]), (431,[193,237]), (463,[179,283]), (467,[104,362]), (491,[123,367]), (499,[176,322])] : List (ℕ × List ℕ)) →
      p.Prime ∧ p%4=3 ∧ (∀ k<p, ((p : ℤ) ∣ A k ↔ k∈rs)) ∧ (∀ n : ℕ,n%p∈rs → ¬IsIntegerValue n) := by
  apply table_rule
  decide +kernel

end ArctanPhase.ExplicitPoles

namespace ArctanPhase

private lemma summable_shifted_powers (n p : ℕ) (hp : 1<p) :
    Summable (fun j : ℕ => (1 / ((n+j : ℕ) : ℝ))^p) := by
  have h := (summable_nat_add_iff (f:=fun j : ℕ => 1 / (j : ℝ)^p) n).mpr
    (Real.summable_one_div_nat_pow.mpr hp)
  simpa only [one_div_pow,Nat.add_comm] using h

private lemma summable_shifted_succ (n p : ℕ) (hp : 1<p) :
    Summable (fun j : ℕ => (1 / (((n+j : ℕ) : ℝ)+1))^p) := by
  simpa only [Nat.cast_add,Nat.cast_one,add_right_comm] using summable_shifted_powers (n+1) p hp

lemma summable_tail3 (n : ℕ) : Summable (fun j : ℕ => (1 / (((n+j : ℕ) : ℝ)+1))^3) :=
  summable_shifted_succ n 3 (by decide)

lemma summable_tail5 (n : ℕ) : Summable (fun j : ℕ => (1 / (((n+j : ℕ) : ℝ)+1))^5) :=
  summable_shifted_succ n 5 (by decide)

private lemma summable_potential (c : ℝ) (n p : ℕ) (hp : 1<p) :
    Summable (fun j : ℕ => 1/(c*((n+j : ℕ) : ℝ)^p)) := by
  simpa only [one_div,inv_pow,mul_inv_rev,mul_comm] using (summable_shifted_powers n p hp).mul_left (1/c)

private lemma telescope (f : ℕ → ℝ) (hf : Summable f) :
    Summable (fun j => f j-f (j+1)) ∧ (∑' j, (f j-f (j+1)))=f 0 := by
  have hs := (summable_nat_add_iff (f:=f) 1).mpr hf
  refine ⟨hf.sub hs,?_⟩
  rw [hf.tsum_sub hs]
  linarith [hf.tsum_eq_zero_add]

private lemma reciprocal3_upper_step {x : ℝ} (hx : 0<x) :
    (1/(x+1))^3 ≤ 1/(2*x^2) - 1/(2*(x+1)^2) := by
  apply sub_nonneg.mp
  field_simp
  ring_nf
  positivity

private lemma reciprocal3_lower_step {x : ℝ} (hx : 0<x) :
    1/(2*x^2) - 1/(2*(x+1)^2) ≤ (1/x)^3 := by
  apply sub_nonneg.mp
  field_simp
  ring_nf
  positivity

private lemma reciprocal5_upper_step {x : ℝ} (hx : 0<x) :
    (1/(x+1))^5 ≤ 1/(4*x^4) - 1/(4*(x+1)^4) := by
  apply sub_nonneg.mp
  field_simp
  ring_nf
  positivity

lemma tail3_lower (n : ℕ) (hn : 1≤n) :
    1/(2*((n : ℝ)+1)^2) ≤ ∑' j : ℕ, (1/(((n+j : ℕ):ℝ)+1))^3 := by
  let f (j : ℕ) : ℝ := 1/(2*((n+1+j : ℕ):ℝ)^2)
  obtain ⟨hs,he⟩ := telescope f (summable_potential 2 (n+1) 2 (by decide))
  have h := hs.tsum_le_tsum (g:=fun j : ℕ => (1/(((n+j : ℕ):ℝ)+1))^3) (fun j => by
    have hpos : 0<((n+j : ℕ):ℝ)+1 := by positivity
    simpa only [f,Nat.cast_add,Nat.cast_one,add_assoc,add_left_comm,add_comm] using
      reciprocal3_lower_step hpos) (summable_tail3 n)
  rw [he] at h
  simpa [f] using h

lemma tail3_upper (n : ℕ) (hn : 1≤n) :
    (∑' j : ℕ, (1/(((n+j : ℕ):ℝ)+1))^3) ≤ 1/(2*(n:ℝ)^2) := by
  let f (j : ℕ) : ℝ := 1/(2*((n+j : ℕ):ℝ)^2)
  obtain ⟨hs,he⟩ := telescope f (summable_potential 2 n 2 (by decide))
  have h := (summable_tail3 n).tsum_le_tsum (g:=fun j => f j-f (j+1)) (fun j => by
    have hpos : 0<((n+j : ℕ):ℝ) := by exact_mod_cast (by omega : 0<n+j)
    simpa only [f,Nat.cast_add,Nat.cast_one,add_assoc] using reciprocal3_upper_step hpos) hs
  rw [he] at h
  simpa [f] using h

lemma tail5_upper (n : ℕ) (hn : 1≤n) :
    (∑' j : ℕ, (1/(((n+j : ℕ):ℝ)+1))^5) ≤ 1/(4*(n:ℝ)^4) := by
  let f (j : ℕ) : ℝ := 1/(4*((n+j : ℕ):ℝ)^4)
  obtain ⟨hs,he⟩ := telescope f (summable_potential 4 n 4 (by decide))
  have h := (summable_tail5 n).tsum_le_tsum (g:=fun j => f j-f (j+1)) (fun j => by
    have hpos : 0<((n+j : ℕ):ℝ) := by exact_mod_cast (by omega : 0<n+j)
    simpa only [f,Nat.cast_add,Nat.cast_one,add_assoc] using reciprocal5_upper_step hpos) hs
  rw [he] at h
  simpa [f] using h

end ArctanPhase

namespace ArctanPhase.Remainder

open Arxiv.«2607.05739»

/-- The derivative at both endpoints is computed in the surrounding real line. -/
private lemma centered_derivative {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    HasDerivAt (fun x : ℝ => Real.log (1+x/2) - Real.log (1-x/2) - Real.arctan x) (5*x^2/((4-x^2)*(1+x^2))) x := by
  have hsq : x^2 ≤ 1 := by nlinarith [mul_nonneg hx (sub_nonneg.mpr hx1)]
  have hp : 1+x/2 ≠ 0 := by linarith
  have hm : 1-x/2 ≠ 0 := by linarith
  have hd : 4-x^2 ≠ 0 := by linarith
  have hn : 1+x^2 ≠ 0 := by positivity
  have h₁ : HasDerivAt (fun y : ℝ => 1+y/2) (1/2) x := ((hasDerivAt_id x).div_const 2).const_add 1
  have h₂ : HasDerivAt (fun y : ℝ => 1-y/2) (-(1/2)) x := ((hasDerivAt_id x).div_const 2).const_sub 1
  have hh := ((h₁.log hp).sub (h₂.log hm)).sub (Real.hasDerivAt_arctan x)
  have he : 5*x^2/((4-x^2)*(1+x^2)) =
      1/2/(1+x/2) - (-(1/2))/(1-x/2) - 1/(1+x^2) := by
    have h₂x : 2-x ≠ 0 := by linarith
    field_simp [h₂x]
    ring
  rw [he]
  exact hh

private lemma derivative_bounds {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    5/4*x^2-15/16*x^4 ≤ 5*x^2/((4-x^2)*(1+x^2)) ∧
    5*x^2/((4-x^2)*(1+x^2)) ≤ 5/4*x^2 := by
  have hsq : x^2 ≤ 1 := by nlinarith [mul_nonneg hx (sub_nonneg.mpr hx1)]
  have den : 0 < (4-x^2)*(1+x^2) := mul_pos (by linarith) (by positivity)
  constructor
  · apply (le_div_iff₀ den).mpr
    nlinarith only [mul_nonneg (pow_nonneg hx 6) (show 0 ≤ 65-15*x^2 by linarith)]
  · apply (div_le_iff₀ den).mpr
    nlinarith only [mul_nonneg (pow_nonneg hx 4) (show 0 ≤ 3-x^2 by linarith)]

private lemma nonneg_from_derivative {f g : ℝ → ℝ} (hz : f 0=0)
    (hd : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ g x) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ f x := by
  have h := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) 1)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt) (fun t ht => hg t (interior_subset ht))
  simpa only [hz] using h (show (0:ℝ) ∈ Set.Icc 0 1 from ⟨le_rfl,zero_le_one⟩) ⟨hx,hx1⟩ hx

/-- Cubic and quintic bounds for the difference of the centered logarithm and the arctangent. -/
private lemma centered_bounds (D : ℝ → ℝ) (D0 : D 0=0)
    (derivative : ∀ {x : ℝ}, 0≤x → x≤1 → HasDerivAt D (5*x^2/((4-x^2)*(1+x^2))) x)
    {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    5/12*x^3 - 3/16*x^5 ≤ D x ∧ D x ≤ 5/12*x^3 := by
  let d (t : ℝ) := 5*t^2/((4-t^2)*(1+t^2))
  have h₃ (t : ℝ) : HasDerivAt (fun y : ℝ => 5/12*y^3) (5/4*t^2) t := by
    convert (hasDerivAt_pow 3 t).const_mul (5/12 : ℝ) using 1 <;> first | rfl | ring
  have h₅ (t : ℝ) : HasDerivAt (fun y : ℝ => 3/16*y^5) (15/16*t^4) t := by
    convert (hasDerivAt_pow 5 t).const_mul (3/16 : ℝ) using 1 <;> first | rfl | ring
  constructor
  · apply sub_nonneg.mp
    apply nonneg_from_derivative (f:=fun y => D y-(5/12*y^3-3/16*y^5))
      (g:=fun y => d y-(5/4*y^2-15/16*y^4)) (by norm_num [D0]) _ _ hx hx1
    · exact fun y hy => (derivative hy.1 hy.2).sub ((h₃ y).sub (h₅ y))
    · exact fun _ hy => sub_nonneg.mpr (derivative_bounds hy.1 hy.2).1
  · apply sub_nonneg.mp
    apply nonneg_from_derivative (f:=fun y => 5/12*y^3-D y) (g:=fun y => 5/4*y^2-d y)
      (by norm_num [D0]) _ _ hx hx1
    · exact fun y hy => (h₃ y).sub (derivative hy.1 hy.2)
    · exact fun _ hy => sub_nonneg.mpr (derivative_bounds hy.1 hy.2).2

private lemma log_step {D : ℝ → ℝ} (hd : ∀ x, D x = Real.log (1+x/2) - Real.log (1-x/2) - Real.arctan x) (k : ℕ) :
    Real.arctan (1/((k:ℝ)+1)) + D (1/((k:ℝ)+1)) =
      Real.log ((k:ℝ)+1+1/2) - Real.log ((k:ℝ)+1/2) := by
  have h₁ : 1+(1/((k:ℝ)+1))/2 = ((k:ℝ)+1+1/2)/((k:ℝ)+1) := by
    field_simp
  have h₂ : 1-(1/((k:ℝ)+1))/2 = ((k:ℝ)+1/2)/((k:ℝ)+1) := by
    field_simp
    ring
  rw [hd, h₁, h₂, Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity)]
  ring

private lemma finite_telescope {D : ℝ → ℝ} (hd : ∀ x, D x = Real.log (1+x/2) - Real.log (1-x/2) - Real.arctan x) (n : ℕ) :
    angleSum n + ∑ k ∈ Finset.range n, D (1/((k:ℝ)+1)) =
      Real.log ((n:ℝ)+1/2) - Real.log (1/2) := by
  induction n with
  | zero => simp [angleSum]
  | succ n ih =>
    have h : angleSum (n+1) = angleSum n + Real.arctan (1/((n:ℝ)+1)) := by
      unfold angleSum
      rw [Finset.sum_Icc_succ_top (by omega : 1≤n+1)]
      simp
    rw [h, Finset.sum_range_succ, Nat.cast_succ]
    linarith only [ih, log_step hd n]

private lemma unit_interval (k : ℕ) :
    0 ≤ 1/((k:ℝ)+1) ∧ 1/((k:ℝ)+1) ≤ 1 := by
  constructor
  · positivity
  · rw [div_le_iff₀ (by positivity : 0<(k:ℝ)+1)]
    linarith only [Nat.cast_nonneg (α:=ℝ) k]

private lemma defect_series {D : ℝ → ℝ}
    (bounds : ∀ {x : ℝ}, 0≤x → x≤1 →
      5/12*x^3 - 3/16*x^5 ≤ D x ∧ D x ≤ 5/12*x^3)
    (n : ℕ) (hc : Summable fun j : ℕ => (1/(((n+j:ℕ):ℝ)+1))^3) :
    Summable fun j : ℕ => D (1/(((n+j:ℕ):ℝ)+1)) := by
  let u (j : ℕ) : ℝ := 1/(((n+j:ℕ):ℝ)+1)
  change Summable (fun j => D (u j))
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => (bounds (unit_interval (n+j)).1
    (unit_interval (n+j)).2).2) (hc.mul_left (5/12 : ℝ))
  obtain ⟨h₀,h₁⟩ : 0≤u j ∧ u j≤1 := unit_interval (n+j)
  have hh : u j^5 ≤ u j^3 := pow_le_pow_of_le_one h₀ h₁ (by decide)
  linarith only [(bounds h₀ h₁).1, hh, pow_nonneg h₀ 3]

private lemma exact_remainder {D : ℝ → ℝ} (hd : ∀ x, D x = Real.log (1+x/2) - Real.log (1-x/2) - Real.arctan x)
    (hs : Summable (fun j : ℕ => D (1/((j:ℝ)+1)))) (n : ℕ) :
    angleSum n - Real.log ((n:ℝ)+1/2) - (-Real.log (1/2) - ∑' k : ℕ, D (1/((k:ℝ)+1))) =
      ∑' j : ℕ, D (1/(((n+j:ℕ):ℝ)+1)) := by
  have hpart := hs.sum_add_tsum_nat_add n
  simp only [Nat.add_comm _ n] at hpart
  linarith only [finite_telescope hd n, hpart]

end ArctanPhase.Remainder

namespace ArctanPhase

open Arxiv.«2607.05739»

/-- The reciprocal arctangent sum has an explicit additive constant and a two-sided
estimate for its remainder after subtracting the centered logarithm. -/
lemma explicit_remainder {n : ℕ} (hn : 1≤n) :
    let d := fun x : ℝ => Real.log (1+x/2) - Real.log (1-x/2) - Real.arctan x
    let c : ℝ := -Real.log (1/2) - ∑' k : ℕ, d (1/((k:ℝ)+1))
    5/(24*((n:ℝ)+1)^2)-3/(64*(n:ℝ)^4) ≤ angleSum n - Real.log ((n:ℝ)+1/2)-c ∧
      angleSum n - Real.log ((n:ℝ)+1/2)-c ≤ 5/(24*(n:ℝ)^2) := by
  intro d c
  have hd (x : ℝ) : d x = Real.log (1+x/2) - Real.log (1-x/2) - Real.arctan x := rfl
  have bounds {x : ℝ} (h₀ : 0≤x) (h₁ : x≤1) : 5/12*x^3-3/16*x^5 ≤ d x ∧ d x ≤ 5/12*x^3 :=
    Remainder.centered_bounds d (by norm_num [d]) (fun hx hx₁ => Remainder.centered_derivative hx hx₁) h₀ h₁
  have hs : Summable (fun j : ℕ => d (1/((j:ℝ)+1))) := by
    simpa only [Nat.zero_add] using Remainder.defect_series (D:=d) (fun hx hx₁ => bounds hx hx₁) 0 (summable_tail3 0)
  have htail : angleSum n - Real.log ((n:ℝ)+1/2)-c = ∑' j : ℕ, d (1/(((n+j:ℕ):ℝ)+1)) :=
    Remainder.exact_remainder hd hs n
  rw [htail]
  let u (j : ℕ) : ℝ := 1/(((n+j:ℕ):ℝ)+1)
  let C := ∑' j : ℕ, u j ^ 3
  let Q := ∑' j : ℕ, u j ^ 5
  have h₃ : Summable fun j => u j ^ 3 := summable_tail3 n
  have h₅ : Summable fun j => u j ^ 5 := summable_tail5 n
  have hD : Summable fun j => d (u j) := Remainder.defect_series (D:=d) (fun hx hx₁ => bounds hx hx₁) n h₃
  have hlo : 5/12*C-3/16*Q ≤ ∑' j, d (u j) := by
    have h := Summable.tsum_le_tsum (fun j : ℕ =>
        (bounds (Remainder.unit_interval (n+j)).1 (Remainder.unit_interval (n+j)).2).1)
      ((h₃.mul_left (5/12:ℝ)).sub (h₅.mul_left (3/16:ℝ))) hD
    rwa [(h₃.mul_left (5/12:ℝ)).tsum_sub (h₅.mul_left (3/16:ℝ)), tsum_mul_left, tsum_mul_left] at h
  have hhi : (∑' j, d (u j)) ≤ 5/12*C := by
    have h := Summable.tsum_le_tsum (fun j : ℕ =>
      (bounds (Remainder.unit_interval (n+j)).1 (Remainder.unit_interval (n+j)).2).2) hD (h₃.mul_left (5/12:ℝ))
    rwa [tsum_mul_left] at h
  have sc (x : ℝ) (hx : 0<x) : 5/(24*x^2) = (5/12)*(1/(2*x^2)) := by field_simp; norm_num
  have sq (x : ℝ) (hx : 0<x) : 3/(64*x^4) = (3/16)*(1/(4*x^4)) := by field_simp; norm_num
  have hn' : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  rw [sc _ (by positivity), sq _ hn', sc _ hn']
  have hl : 1/(2*((n:ℝ)+1)^2) ≤ C := tail3_lower n hn
  have hu : C ≤ 1/(2*(n:ℝ)^2) := tail3_upper n hn
  have hv : Q ≤ 1/(4*(n:ℝ)^4) := tail5_upper n hn
  change _ ≤ (∑' j, d (u j)) ∧ (∑' j, d (u j)) ≤ _
  constructor <;> linarith only [hlo,hhi,hl,hu,hv]

end ArctanPhase

namespace ArctanPhase

private lemma rational_budgets (N : ℝ) (hN : 64 ≤ N) :
    0 ≤ 5/(24*(N+1)^2)-3/(64*N^4)-1/(1000*N^4) ∧
    5/(24*N^2)+1/(1000*N^4) ≤ 1/N^2 ∧ 1/N^2 ≤ 1 ∧
    5/(24*N)-2/N^2 ≤ (N+1/2)*(5/(24*(N+1)^2)-3/(64*N^4)-1/(1000*N^4)) ∧
    (N+1/2)*(5/(24*N^2)+1/(1000*N^4)+(1/N^2)^2) ≤ 5/(24*N)+2/N^2 := by
  obtain ⟨s,hs,rfl⟩ : ∃ s : ℝ, 0 ≤ s ∧ N=64+s := ⟨N-64,by linarith,by ring⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals apply sub_nonneg.mp
  all_goals field_simp
  all_goals ring_nf
  all_goals positivity

/-- Exponentiating the phase remainder recovers the first correction with an error at most `2/N²`. -/
lemma inversion_error {N R η : ℝ} (hN : 64 ≤ N)
    (hlo : 5/(24*(N+1)^2)-3/(64*N^4) ≤ R) (hhi : R ≤ 5/(24*N^2))
    (hη : |η| ≤ 1/(1000*N^4)) :
    |(N+1/2)*Real.exp (R+η) - (N+1/2 + 5/(24*N))| ≤ 2/N^2 := by
  obtain ⟨hl₀,hu₁,h₁,hlb,hub⟩ := rational_budgets N hN
  let t := R+η
  have hl : 5/(24*(N+1)^2)-3/(64*N^4)-1/(1000*N^4) ≤ t := by
    dsimp [t]; linarith only [hlo,(abs_le.mp hη).1]
  have hu : t ≤ 5/(24*N^2)+1/(1000*N^4) := by
    dsimp [t]; linarith only [hhi,(abs_le.mp hη).2]
  have ht := hl₀.trans hl
  have hn : |t| ≤ 1 := by rw [abs_of_nonneg ht]; exact (hu.trans hu₁).trans h₁
  have hs : t^2 ≤ (1/N^2)^2 := (sq_le_sq₀ ht (by positivity)).mpr (hu.trans hu₁)
  have el : 5/(24*(N+1)^2)-3/(64*N^4)-1/(1000*N^4) ≤ Real.exp t-1 := by
    linarith only [hl,Real.add_one_le_exp t]
  have eu : Real.exp t-1 ≤ 5/(24*N^2)+1/(1000*N^4)+(1/N^2)^2 := by
    linarith only [(abs_le.mp (Real.abs_exp_sub_one_sub_id_le hn)).2,hu,hs]
  have hp : 0 ≤ N+1/2 := by linarith only [hN]
  have left := hlb.trans (mul_le_mul_of_nonneg_left el hp)
  have right := (mul_le_mul_of_nonneg_left eu hp).trans hub
  change |(N+1/2)*Real.exp t-(N+1/2+5/(24*N))| ≤ 2/N^2
  exact abs_le.mpr ⟨by linarith only [left],by linarith only [right]⟩

/-- The recovered value lies in a strict window of width `5/(24*N)` above `N+1/2`. -/
lemma inversion_window {N R η : ℝ} (hN : 64 ≤ N)
    (hlo : 5/(24*(N+1)^2)-3/(64*N^4) ≤ R) (hhi : R ≤ 5/(24*N^2))
    (hη : |η| ≤ 1/(1000*N^4)) :
    N+1/2+1/(8*N) < (N+1/2)*Real.exp (R+η) ∧ (N+1/2)*Real.exp (R+η) < N+1/2+1/(3*N) := by
  obtain ⟨hl,hu⟩ := abs_le.mp (inversion_error hN hlo hhi hη)
  have hp : 0 < N := by linarith only [hN]
  have low : 1/(8*N) < 5/(24*N)-2/N^2 := by
    field_simp
    linarith only [hN]
  have high : 5/(24*N)+2/N^2 < 1/(3*N) := by
    field_simp
    linarith only [hN]
  exact ⟨by linarith only [hl,low],by linarith only [hu,high]⟩

lemma inversion_unit_interval {N R η : ℝ} (hN : 64 ≤ N)
    (hlo : 5/(24*(N+1)^2)-3/(64*N^4) ≤ R) (hhi : R ≤ 5/(24*N^2))
    (hη : |η| ≤ 1/(1000*N^4)) :
    N+1/2 < (N+1/2)*Real.exp (R+η) ∧ (N+1/2)*Real.exp (R+η) < N+1 := by
  obtain ⟨hl,hu⟩ := inversion_window hN hlo hhi hη
  have hp : 0 < N := by linarith only [hN]
  have small : 1/(3*N) < 1/2 := (div_lt_iff₀ (by positivity)).mpr (by linarith only [hN])
  exact ⟨(lt_add_of_pos_right _ (by positivity)).trans hl,by linarith only [hu,small]⟩

end ArctanPhase

namespace ArctanPhase

open Arxiv.«2607.05739»

/-- The real phase scale pins down the entire integer index and its
first correction as soon as the quotient dominates a quartic. -/
lemma locate_with_remainder {c : ℝ} {n : ℕ} {m : ℤ} (hn : 64≤n) (hm : B n=A n*m)
    (big : 1000*n^4 ≤ m.natAbs)
    (bounds : 5/(24*((n:ℝ)+1)^2)-3/(64*(n:ℝ)^4) ≤ angleSum n-Real.log ((n:ℝ)+1/2)-c ∧
      angleSum n-Real.log ((n:ℝ)+1/2)-c ≤ 5/(24*(n:ℝ)^2)) :
    ∃ j : ℤ, let t := Real.exp ((j:ℝ)*(Real.pi/2)-c)
      Odd ((n:ℤ)-j) ∧ ⌊t⌋₊=n ∧
      |t - ((n:ℝ)+1/2+5/(24*(n:ℝ)))| ≤ 2/(n:ℝ)^2 ∧
      (n:ℝ)+1/2+1/(8*(n:ℝ)) < t ∧
      t < (n:ℝ)+1/2+1/(3*(n:ℝ)) ∧
      angleSum n-(j:ℝ)*(Real.pi/2) = Real.arctan (1/(m:ℝ)) := by
  let scale (j : ℤ) := Real.exp ((j:ℝ)*(Real.pi/2)-c)
  have npos : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have h64 : (64:ℝ)≤n := by exact_mod_cast hn
  have mag : 1000*(n:ℝ)^4 ≤ |(m:ℝ)| := by
    rw [← Int.cast_abs,← Int.natCast_natAbs]
    exact_mod_cast big
  have qpos : (0:ℝ)<1000*(n:ℝ)^4 := by positivity
  have hm₀ : m≠0 := by
    rintro rfl
    simp at mag
    linarith only [mag,qpos]
  obtain ⟨j,odd,signed,small⟩ := signed_grid hm hm₀
  let R := angleSum n-Real.log ((n:ℝ)+1/2)-c
  let η := (j:ℝ)*(Real.pi/2)-angleSum n
  obtain ⟨lo,hi⟩ := bounds
  have eta : |η| ≤ 1/(1000*(n:ℝ)^4) := by
    dsimp only [η]
    rw [abs_sub_comm]
    exact small.trans (one_div_le_one_div_of_le qpos mag)
  have eq : scale j = ((n:ℝ)+1/2)*Real.exp (R+η) := by
    dsimp only [scale,R,η]
    rw [show (j:ℝ)*(Real.pi/2)-c =
      Real.log ((n:ℝ)+1/2) + (angleSum n-Real.log ((n:ℝ)+1/2)-c+
         ((j:ℝ)*(Real.pi/2)-angleSum n)) by ring]
    rw [Real.exp_add,Real.exp_log (by positivity)]
  have err := inversion_error (R:=R) h64 lo hi eta
  have win := inversion_window (R:=R) h64 lo hi eta
  have unit := inversion_unit_interval (R:=R) h64 lo hi eta
  rw [← eq] at err win unit
  have fl : ⌊scale j⌋₊ = n :=
    (Nat.floor_eq_iff (a:=scale j) (Real.exp_pos _).le).mpr
      ⟨(le_add_of_nonneg_right (by norm_num : (0:ℝ)≤1/2)).trans unit.1.le,unit.2⟩
  exact ⟨j,odd,fl,err,win.1,win.2,signed⟩

end ArctanPhase

namespace ArctanPhase

open Arxiv.«2607.05739»

private lemma below_sixty_four {n : ℕ} (lo : 5≤n) (hi : n<64) : ¬IsIntegerValue n := by
  have check : ∀ k : Fin 64, 5≤k.val → ¬IsIntegerValue k.val := by decide +kernel
  exact check ⟨n,hi⟩ lo

/-- The polynomial barrier holds at every nonexceptional index, including
the interval prior to the exponential estimate. -/
theorem quartic_all {n : ℕ} {m : ℤ} (hn : 5≤n) (hm : B n=A n*m) :
    1000*n^4 ≤ m.natAbs := by
  by_cases small : n<64
  · exact (below_sixty_four hn small ⟨m,hm⟩).elim
  by_cases medium : n≤1000000
  · exact ArctanQuartic.quotient_large (by omega) medium hm
  · exact quartic_above_million (by omega) hm

/-- Every prospective integer index is the floor of a single exponential
scale. The signed displacement is determined by the reciprocal quotient. -/
theorem explicit_location {n : ℕ} {m : ℤ} (hn : 5≤n) (hm : B n=A n*m) :
    let d := fun x : ℝ => Real.log (1+x/2)-Real.log (1-x/2)-Real.arctan x
    let c := -Real.log (1/2) - ∑' k : ℕ, d (1/((k:ℝ)+1))
    ∃ j : ℤ, let t := Real.exp ((j:ℝ)*(Real.pi/2)-c)
      Odd ((n:ℤ)-j) ∧ ⌊t⌋₊=n ∧
      |t-((n:ℝ)+1/2+5/(24*(n:ℝ)))| ≤ 2/(n:ℝ)^2 ∧
      (n:ℝ)+1/2+1/(8*(n:ℝ)) < t ∧ t < (n:ℝ)+1/2+1/(3*(n:ℝ)) ∧
      angleSum n-(j:ℝ)*(Real.pi/2) = Real.arctan (1/(m:ℝ)) := by
  have start : 64≤n := by
    by_contra! small
    exact below_sixty_four hn small ⟨m,hm⟩
  exact locate_with_remainder start hm (quartic_all hn hm) (explicit_remainder (by omega))

/-- The same floor formula and quantitative error apply to the ordinary real tangent. -/
theorem real_tangent_location {n : ℕ} {m : ℤ} (hn : 5≤n)
    (hm : Real.tan (∑ k ∈ Finset.Icc 1 n, Real.arctan k)=(m:ℝ)) :
    let d := fun x : ℝ => Real.log (1+x/2)-Real.log (1-x/2)-Real.arctan x
    let c := -Real.log (1/2) - ∑' k : ℕ, d (1/((k:ℝ)+1))
    ∃ j : ℤ, let t := Real.exp ((j:ℝ)*(Real.pi/2)-c)
      Odd ((n:ℤ)-j) ∧ ⌊t⌋₊=n ∧
      |t-((n:ℝ)+1/2+5/(24*(n:ℝ)))| ≤ 2/(n:ℝ)^2 ∧
      (n:ℝ)+1/2+1/(8*(n:ℝ)) < t ∧ t < (n:ℝ)+1/2+1/(3*(n:ℝ)) ∧
      angleSum n-(j:ℝ)*(Real.pi/2) = Real.arctan (1/(m:ℝ)) :=
  explicit_location hn ((ArctanEffective.tangent_eq_iff n m).mp hm)

end ArctanPhase

namespace ArctanPhase

open Arxiv.«2607.05739» Filter
open scoped Topology

/-- The explicit defect series gives the constant in the logarithmic asymptotic of the arctangent sum. -/
lemma explicit_limit :
    let d := fun x : ℝ => Real.log (1+x/2) - Real.log (1-x/2) - Real.arctan x
    let c : ℝ := -Real.log (1/2) - ∑' k : ℕ, d (1/((k:ℝ)+1))
    Tendsto (fun n : ℕ => angleSum n - Real.log (n:ℝ)) atTop (𝓝 c) := by
  intro d c
  let r (n : ℕ) := angleSum n - Real.log ((n:ℝ)+1/2)-c
  have vanish (a b : ℝ) (hb : 0<b) (k : ℕ) (hk : k≠0) :
      Tendsto (fun n : ℕ => a/(b*(n:ℝ)^k)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (((tendsto_pow_atTop (α:=ℝ) hk).comp tendsto_natCast_atTop_atTop).const_mul_atTop hb)
  have bounds (n : ℕ) (hn : 1≤n) : -3/(64*(n:ℝ)^4) ≤ r n ∧ r n ≤ 5/(24*(n:ℝ)^2) := by
    obtain ⟨hl,hu⟩ := explicit_remainder hn
    change 5/(24*((n:ℝ)+1)^2)-3/(64*(n:ℝ)^4) ≤ r n at hl
    refine ⟨?_,hu⟩
    calc
      -3/(64*(n:ℝ)^4) = 0-3/(64*(n:ℝ)^4) := by rw [zero_sub,neg_div]
      _ ≤ _ := (sub_le_sub_right (by positivity : 0 ≤ 5/(24*((n:ℝ)+1)^2)) _).trans hl
  have hr : Tendsto r atTop (𝓝 0) := tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (vanish (-3) 64 (by norm_num) 4 (by decide)) (vanish 5 24 (by norm_num) 2 (by decide))
    ((eventually_ge_atTop (1 : ℕ)).mono fun n hn => (bounds n hn).1)
    ((eventually_ge_atTop (1 : ℕ)).mono fun n hn => (bounds n hn).2)
  have shift : Tendsto (fun n : ℕ => Real.log ((n:ℝ)+1/2)-Real.log (n:ℝ)) atTop (𝓝 0) :=
    (Real.tendsto_log_comp_add_sub_log (1/2)).comp tendsto_natCast_atTop_atTop
  have total : Tendsto (fun n : ℕ => r n+(Real.log ((n:ℝ)+1/2)-Real.log (n:ℝ))+c) atTop (𝓝 c) := by
    simpa only [zero_add] using (hr.add shift).add_const c
  exact total.congr' (Eventually.of_forall fun n => by dsimp [r]; ring)

end ArctanPhase

namespace ArctanPhase

open Arxiv.«2607.05739» Filter
open scoped Topology

/-- The same phase constant equals Euler's constant minus the absolutely convergent
corrections from replacing each reciprocal by its arctangent. -/
lemma explicit_euler_correction :
    let d := fun x : ℝ => Real.log (1+x/2) - Real.log (1-x/2) - Real.arctan x
    let c : ℝ := -Real.log (1/2) - ∑' k : ℕ, d (1/((k:ℝ)+1))
    let term := fun k : ℕ => 1/((k:ℝ)+1) - Real.arctan (1/((k:ℝ)+1))
    Summable (fun k => |term k|) ∧ c = Real.eulerMascheroniConstant - ∑' k, term k := by
  intro d c term
  have nonneg (k : ℕ) : 0 ≤ term k := by
    let x : ℝ := 1/((k:ℝ)+1)
    change 0 ≤ x - Real.arctan x
    apply sub_nonneg.mpr
    simpa only [Real.tan_arctan] using Real.le_tan (Real.arctan_nonneg.mpr (by positivity : 0≤x))
      (Real.arctan_lt_pi_div_two x)
  have partial_sum (n : ℕ) : ∑ k ∈ Finset.range n, term k = (harmonic n : ℝ) - angleSum n := by
    induction n with
    | zero => simp [angleSum]
    | succ n ih =>
      have ha : angleSum (n+1) = angleSum n + Real.arctan (1/((n:ℝ)+1)) := by
        unfold angleSum
        rw [Finset.sum_Icc_succ_top (by omega : 1≤n+1)]
        simp
      rw [Finset.sum_range_succ,ih,harmonic_succ,ha]
      simp only [term,Rat.cast_add,Rat.cast_inv,Rat.cast_natCast,Nat.cast_succ,one_div]
      ring
  have hc : Tendsto (fun n : ℕ => angleSum n - Real.log (n:ℝ)) atTop (𝓝 c) := explicit_limit
  have correction : HasSum term (Real.eulerMascheroniConstant-c) := by
    apply (hasSum_iff_tendsto_nat_of_nonneg nonneg _).mpr
    apply (Real.tendsto_harmonic_sub_log.sub hc).congr'
    apply Eventually.of_forall
    intro n
    dsimp only
    rw [partial_sum]
    ring
  exact ⟨by simpa only [fun k => abs_of_nonneg (nonneg k)] using correction.summable,
    by linarith only [correction.tsum_eq]⟩

end ArctanPhase

namespace OMA.R_Arxiv_2607_05739_tan_arctan_sum_not_integer_R3

open Arxiv.«2607.05739»

/-- The even half-period tests only odd indices. -/
def H1 : Prop :=
  let d := fun x : ℝ => Real.log (1+x/2)-Real.log (1-x/2)-Real.arctan x
  let c := -Real.log (1/2) - ∑' r : ℕ, d (1/((r:ℝ)+1))
  ∀ k : ℤ, let j := 2*k
    let t := Real.exp ((j:ℝ)*(Real.pi/2)-c)
    let n := ⌊t⌋₊
    64≤n → Odd ((n:ℤ)-j) →
      |t-((n:ℝ)+1/2+5/(24*(n:ℝ)))| ≤ 2/(n:ℝ)^2 →
      (n:ℝ)+1/2+1/(8*(n:ℝ)) < t → t < (n:ℝ)+1/2+1/(3*(n:ℝ)) →
      (∀ p : ℕ, p.Prime → p%4=3 → ¬(p:ℤ) ∣ A (n%p)) → ¬A n ∣ B n

/-- The odd half-period tests only even indices. -/
def H2 : Prop :=
  let d := fun x : ℝ => Real.log (1+x/2)-Real.log (1-x/2)-Real.arctan x
  let c := -Real.log (1/2) - ∑' r : ℕ, d (1/((r:ℝ)+1))
  ∀ k : ℤ, let j := 2*k+1
    let t := Real.exp ((j:ℝ)*(Real.pi/2)-c)
    let n := ⌊t⌋₊
    64≤n → Odd ((n:ℤ)-j) →
      |t-((n:ℝ)+1/2+5/(24*(n:ℝ)))| ≤ 2/(n:ℝ)^2 →
      (n:ℝ)+1/2+1/(8*(n:ℝ)) < t → t < (n:ℝ)+1/2+1/(3*(n:ℝ)) →
      (∀ p : ℕ, p.Prime → p%4=3 → ¬(p:ℤ) ∣ A (n%p)) → ¬A n ∣ B n

theorem main : H1 → H2 → type_of% @Arxiv.«2607.05739».tan_arctan_sum_not_integer := by
  intro evenCheck oddCheck n hn integral
  obtain ⟨m,hm⟩ := integral
  let d := fun x : ℝ => Real.log (1+x/2)-Real.log (1-x/2)-Real.arctan x
  let c := -Real.log (1/2) - ∑' k : ℕ, d (1/((k:ℝ)+1))
  let S (j : ℤ) := Real.exp ((j:ℝ)*(Real.pi/2)-c)
  let test (j : ℤ) : Prop :=
    let t := S j
    let k := ⌊t⌋₊
    64≤k → Odd ((k:ℤ)-j) →
      |t-((k:ℝ)+1/2+5/(24*(k:ℝ)))| ≤ 2/(k:ℝ)^2 →
      (k:ℝ)+1/2+1/(8*(k:ℝ)) < t → t < (k:ℝ)+1/2+1/(3*(k:ℝ)) →
      (∀ p : ℕ, p.Prime → p%4=3 → ¬(p:ℤ) ∣ A (k%p)) → ¬A k ∣ B k
  have even (k : ℤ) : test (2*k) := evenCheck k
  have odd (k : ℤ) : test (2*k+1) := oddCheck k
  have all (j : ℤ) : test j := by
    rcases (show j=2*(j/2) ∨ j=2*(j/2)+1 by omega) with h | h
    · exact (congrArg test h).mpr (even (j/2))
    · exact (congrArg test h).mpr (odd (j/2))
  obtain ⟨j,parity,floor_eq,error,lower,upper,_⟩ := ArctanPhase.explicit_location hn hm
  change ⌊S j⌋₊ = n at floor_eq
  have survivor (p : ℕ) (hp : p.Prime) (inert : p%4=3) : ¬(p:ℤ) ∣ A (n%p) := by
    intro h
    exact ArctanPhase.inert_not_dvd_A hp inert hm ((ArctanPhase.inert_dvd_iff hp inert n).1.mpr h)
  have start : 64≤n := by
    by_contra! small
    exact ArctanPhase.below_sixty_four hn small ⟨m,hm⟩
  have obstruct := all j
  change 64≤⌊S j⌋₊ → _ at obstruct
  rw [floor_eq] at obstruct
  exact obstruct start parity error lower upper survivor ⟨m,hm⟩

/-- Both residual tests are necessary. Together they are equivalent to
the original conjecture, with the same Gaussian coordinates. -/
theorem iff_parity_tests :
    (type_of% @Arxiv.«2607.05739».tan_arctan_sum_not_integer) ↔ H1 ∧ H2 := by
  refine ⟨fun full => ⟨?_,?_⟩,fun h => main h.1 h.2⟩
  all_goals
    dsimp only [H1,H2]
    intro k start _ _ _ _ _ integral
    exact full _ ((by decide : 5≤64).trans start) integral

end OMA.R_Arxiv_2607_05739_tan_arctan_sum_not_integer_R3
