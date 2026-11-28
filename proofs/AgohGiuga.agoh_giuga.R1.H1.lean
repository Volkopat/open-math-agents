import OMAReductions.R_AgohGiuga_agoh_giuga_R1
import Mathlib.FieldTheory.Finite.Basic

/-!
# Pointwise equivalence of Agoh's and Giuga's congruences

Lean formalization by @Deldor14. We compare the two congruences at each
prime divisor of the modulus. Giuga's power sums break into complete blocks
of residues. For even Bernoulli index, von Staudt–Clausen expresses the
Bernoulli number as an integer minus reciprocals of distinct primes. The
product of those primes is its reduced denominator, and its numerator modulo
each such prime is the negative product of the other primes.

Mathematical reference: B. C. Kellner, The Equivalence of Giuga's and Agoh's
Conjectures (2004), https://arxiv.org/abs/math/0409259.
-/

namespace OMA.Kellner
open AgohGiuga Finset

private theorem omitZero (p n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    ∑ a ∈ Ioo 0 n, (a : ZMod p)^k = ∑ a ∈ range n, (a : ZMod p)^k := by
  have hs : (range n).erase 0 = Ioo 0 n := by
    ext a
    simp
  rw [← hs, ← Finset.add_sum_erase (range n) (fun a => (a : ZMod p)^k) (by simpa using hn : 0 ∈ range n)]
  simp [zero_pow hk.ne']

private theorem blocks (p t k : ℕ) :
    ∑ a ∈ range (p*t), (a : ZMod p)^k = (t : ZMod p) * ∑ a ∈ range p, (a : ZMod p)^k := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Nat.cast_succ, add_mul, one_mul]
    simp

private theorem residueSum (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    ∑ a ∈ range p, (a : ZMod p)^k = if p-1 ∣ k then -1 else 0 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hsum : (∑ u : (ZMod p)ˣ, (u : ZMod p)^k) =
      ∑ a ∈ Ioo 0 p, (a : ZMod p)^k := by
    refine Finset.sum_bij (fun (u : (ZMod p)ˣ) _ => (u : ZMod p).val) ?_ ?_ ?_ ?_
    · intro u _
      exact Finset.mem_Ioo.mpr ⟨(ZMod.val_pos.mpr u.ne_zero), ZMod.val_lt _⟩
    · intro a _ b _ he
      exact Units.ext (ZMod.val_injective _ he)
    · intro j hj
      obtain ⟨hj0,hjp⟩ := Finset.mem_Ioo.mp hj
      have hj' : (j : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact Nat.not_dvd_of_pos_of_lt hj0 hjp
      exact ⟨Units.mk0 _ hj', Finset.mem_univ _, ZMod.val_cast_of_lt hjp⟩
    · intro u _
      simp
  rw [← omitZero p p k hp.pos hk, ← hsum, FiniteField.sum_pow_units, ZMod.card]

def giugaSum (n : ℕ) := 1 + ∑ a ∈ Ioo 0 n, a^(n-1)
def LocalCondition (n : ℕ) := ∀ p t : ℕ, p.Prime → n=p*t → p-1 ∣ n-1 ∧ (t : ZMod p)=1

theorem localTest {n p t : ℕ} (hn2 : 2 ≤ n) (hp : p.Prime) (ht : n=p*t) :
    p ∣ giugaSum n ↔ p-1 ∣ n-1 ∧ (t : ZMod p)=1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hk : 0 < n-1 := by omega
  rw [← ZMod.natCast_eq_zero_iff, giugaSum]
  push_cast
  rw [omitZero p n (n-1) (by omega) hk]
  conv_lhs => enter [1,2,1,1]; rw [ht]
  rw [blocks,residueSum p (n-1) hp hk]
  by_cases h : p-1 ∣ n-1
  · simp only [h, if_true, true_and, mul_neg, mul_one]
    constructor <;> intro hh <;> linear_combination -hh
  · simp [h]

theorem squarefree_of_local {n : ℕ} (h : LocalCondition n) : Squarefree n := by
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro p hp hpp
  obtain ⟨t,ht⟩ := hpp
  let _ : Fact p.Prime := ⟨hp⟩
  have he := (h p (p*t) hp (by simpa [mul_assoc] using ht)).2
  simp at he

theorem factorsDvd {n m : ℕ} (hs : Squarefree n)
    (h : ∀ p, p.Prime → p ∣ n → p ∣ m) : n ∣ m := by
  rcases eq_or_ne m 0 with rfl | hm
  · exact dvd_zero n
  rw [← Nat.prod_primeFactors_of_squarefree hs, Nat.prod_primeFactors_dvd_iff hm]
  intro p hp
  obtain ⟨hp',hpn,_⟩ := Nat.mem_primeFactors.mp hp
  exact Nat.mem_primeFactors.mpr ⟨hp',h p hp' hpn,hm⟩

theorem factorsIntDvd {n : ℕ} {a : ℤ} (hs : Squarefree n)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → (p : ℤ) ∣ a) : (n : ℤ) ∣ a := by
  rw [Int.natCast_dvd]
  exact factorsDvd hs fun p hp hd => Int.natCast_dvd.mp (h p hp hd)

theorem giugaIff {n : ℕ} (hn : 2 ≤ n) : n ∣ giugaSum n ↔ LocalCondition n := by
  constructor
  · intro hd p t hp ht
    exact (localTest hn hp ht).mp ((show p ∣ n from ⟨t,ht⟩).trans hd)
  · intro hl
    apply factorsDvd (squarefree_of_local hl)
    rintro p hp ⟨t,ht⟩
    exact (localTest hn hp ht).mpr (hl p t hp ht)

def primeProduct (s : Finset ℕ) : ℕ := ∏ p ∈ s, p
def omitProduct (s : Finset ℕ) (p : ℕ) : ℕ := primeProduct (s.erase p)
def corrNum (s : Finset ℕ) (z : ℤ) : ℤ :=
  z * (primeProduct s : ℤ) - ∑ p ∈ s, (omitProduct s p : ℤ)

theorem splitProd {s : Finset ℕ} {p : ℕ} (h : p ∈ s) :
    p * omitProduct s p = primeProduct s := Finset.mul_prod_erase s id h

theorem product_ne_zero {s : Finset ℕ} (hs : ∀ p∈s, p.Prime) : primeProduct s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun p hp => (hs p hp).ne_zero

theorem mem_of_prime_dvd {s : Finset ℕ} (hs : ∀ p∈s, p.Prime)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ primeProduct s) : p ∈ s := by
  obtain ⟨q,hq,hdq⟩ := (hp.prime.dvd_finsetProd_iff id).mp hd
  rwa [(hs q hq).eq_one_or_self_of_dvd p hdq |>.resolve_left hp.ne_one]

theorem omit_nonzero {s : Finset ℕ} (hs : ∀ p∈s, p.Prime)
    {p : ℕ} (hp : p∈s) : (omitProduct s p : ZMod p) ≠ 0 := by
  rw [Ne,ZMod.natCast_eq_zero_iff]
  intro hd
  have h := mem_of_prime_dvd (s:=s.erase p) (fun _ h => hs _ (Finset.mem_erase.mp h).2)
      (hs _ hp) hd
  exact (Finset.notMem_erase _ _) h

theorem numerator_residue {s : Finset ℕ} (z : ℤ) {p : ℕ} (hp : p∈s) :
    (corrNum s z : ZMod p) = -(omitProduct s p : ZMod p) := by
  have hz : (primeProduct s : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr
    ⟨_,(splitProd hp).symm⟩
  have he : (∑ q∈s, (omitProduct s q : ZMod p)) = (omitProduct s p : ZMod p) := by
    apply Finset.sum_eq_single p
    · intro q _ hq
      apply (ZMod.natCast_eq_zero_iff _ _).mpr
      exact Finset.dvd_prod_of_mem id (Finset.mem_erase.mpr ⟨hq.symm,hp⟩)
    · simp [hp]
  simp [corrNum,hz,he]

theorem numerator_coprime {s : Finset ℕ} (hs : ∀ p∈s, p.Prime) (z : ℤ) :
    (corrNum s z).natAbs.Coprime (primeProduct s) := by
  apply Nat.coprime_of_dvd
  intro p hprime hnum hd
  have hps := mem_of_prime_dvd hs hprime hd
  have hn := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Int.natCast_dvd.mpr hnum)
  rw [numerator_residue z hps, neg_eq_zero] at hn
  exact omit_nonzero hs hps hn

theorem numerator_identity {s : Finset ℕ} (hs : ∀ p∈s, p.Prime) (z : ℤ) :
    (corrNum s z : ℚ) =
      (z : ℚ) * primeProduct s - (∑ p∈s, (1:ℚ)/p) * primeProduct s := by
  unfold corrNum
  push_cast
  rw [Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have h0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hs p hp).ne_zero
  field_simp
  exact_mod_cast (mul_comm p (omitProduct s p) ▸ splitProd hp)

theorem fraction_parts {s : Finset ℕ} (hs : ∀ p∈s, p.Prime) {z : ℤ} {B : ℚ}
    (hb : (z : ℚ) = B + ∑ p∈s, (1:ℚ)/p) :
    B.den = primeProduct s ∧ B.num = corrNum s z := by
  let r : ℚ := ⟨corrNum s z, primeProduct s, product_ne_zero hs, numerator_coprime hs z⟩
  have hr : (corrNum s z : ℚ) / primeProduct s = r := Rat.num_div_den r
  have hBr : B = r := by
    rw [← hr, eq_div_iff (Nat.cast_ne_zero.mpr (product_ne_zero hs)), numerator_identity hs z, hb]
    ring
  rw [hBr]
  exact ⟨rfl,rfl⟩

private theorem cancelOrder {n d : ℕ} {a : ℤ} (hn : 0 < n) :
    (∃ k : ℤ, (n : ℤ)*a + d = k*n^2) ↔
      ∃ c : ℕ, d=n*c ∧ (n : ℤ) ∣ a+c := by
  have hnz : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hn.ne'
  constructor
  · rintro ⟨k,h⟩
    have hd : (n : ℤ) ∣ (d : ℤ) := ⟨k*n-a, by linear_combination h⟩
    obtain ⟨c,hc⟩ := Int.natCast_dvd_natCast.mp hd
    refine ⟨c,hc,k,?_⟩
    apply mul_left_cancel₀ hnz
    rw [hc,Nat.cast_mul] at h
    linear_combination h
  · rintro ⟨c,rfl,k,hk⟩
    refine ⟨k,?_⟩
    push_cast
    linear_combination (n : ℤ)*hk

private theorem cancelResidue {s : Finset ℕ} (hs : ∀ p∈s, p.Prime) {p t c : ℕ}
    (hm : p∈s) (hP : primeProduct s = (p*t)*c) (z : ℤ) :
    (p : ℤ) ∣ corrNum s z+c ↔ (t : ZMod p)=1 := by
  let _ : Fact p.Prime := ⟨hs p hm⟩
  have he : omitProduct s p = t*c := Nat.eq_of_mul_eq_mul_left (hs p hm).pos
    (by rw [splitProd hm,hP,Nat.mul_assoc])
  have hc : (c : ZMod p) ≠ 0 := by
    intro h
    apply omit_nonzero hs hm
    rw [he,Nat.cast_mul,h,mul_zero]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_add, Int.cast_natCast, numerator_residue z hm, he, Nat.cast_mul]
  constructor
  · intro h
    apply mul_right_cancel₀ hc
    linear_combination -h
  · intro h
    simp [h]

theorem pointwiseParts {n : ℕ} (hn : 2 ≤ n) {s : Finset ℕ} (hs : ∀ p∈s, p.Prime)
    (hmem : ∀ p, p.Prime → p ∣ n → (p ∈ s ↔ p-1 ∣ n-1))
    (z : ℤ) : (∃ k : ℤ, (n:ℤ)*corrNum s z + primeProduct s = k*n^2) ↔ LocalCondition n := by
  rw [cancelOrder (by omega : 0<n)]
  constructor
  · rintro ⟨c,hc,hd⟩ p t hp ht
    have hpn : p ∣ n := ⟨t,ht⟩
    have hm := mem_of_prime_dvd hs hp (hpn.trans ⟨c,hc⟩)
    have hpnz : (p : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr hpn
    exact ⟨(hmem p hp hpn).mp hm, (cancelResidue hs hm (by simpa [← ht] using hc) z).mp (hpnz.trans hd)⟩
  · intro hl
    have sq := squarefree_of_local hl
    have hdiv : n ∣ primeProduct s := by
      apply factorsDvd sq
      rintro p hp ⟨t,ht⟩
      have hm := (hmem p hp ⟨t,ht⟩).mpr (hl p t hp ht).1
      exact ⟨_,(splitProd hm).symm⟩
    obtain ⟨c,hc⟩ := hdiv
    refine ⟨c,hc,factorsIntDvd sq ?_⟩
    rintro p hp ⟨t,ht⟩
    obtain ⟨ha,hb⟩ := hl p t hp ht
    have hm := (hmem p hp ⟨t,ht⟩).mpr ha
    exact (cancelResidue hs hm (by simpa [← ht] using hc) z).mpr hb

theorem excludeEven {n : ℕ} (hn : 2<n) (he : Even n) : ¬ LocalCondition n := by
  rintro h
  obtain ⟨k,hk⟩ := he
  have hn2 : n=2*k := by omega
  obtain ⟨p,hp,hpdiv⟩ := Nat.exists_prime_and_dvd (by omega : k ≠ 1)
  obtain ⟨t,ht⟩ := hpdiv
  have hnot : p ≠ 2 := by
    rintro rfl
    have hc := (h 2 k Nat.prime_two hn2).2
    have hz : (k : ZMod 2)=0 := (ZMod.natCast_eq_zero_iff _ _).mpr ⟨t,ht⟩
    simp [hz] at hc
  have hodd := hp.eq_two_or_odd.resolve_left hnot
  have hfactor : n=p*(2*t) := by rw [hn2,ht]; ring
  obtain ⟨u,hu⟩ := (h p (2*t) hp hfactor).1
  have hh : Even (p-1) := ⟨(p-1)/2,by omega⟩
  have hv : Even (n-1) := hu ▸ hh.mul_right u
  obtain ⟨v,hv⟩ := hv
  omega

theorem agohBridge (n : ℕ) (hn : 2 ≤ n) :
    (∃ k : ℤ, (n:ℤ)*(bernoulli' (n-1)).num + (bernoulli' (n-1)).den = k*n^2) ↔
       n ∣ giugaSum n := by
  rcases eq_or_lt_of_le hn with h2 | h2
  · subst n
    constructor
    · intro _
      norm_num [giugaSum, show Ioo 0 2 = ({1} : Finset ℕ) by decide]
    · intro _
      exact ⟨1, by norm_num [bernoulli'_one]⟩
  rw [giugaIff hn]
  rcases Nat.even_or_odd (n-1) with he | ho
  · obtain ⟨m,hm⟩ := he
    have hkm : n-1=2*m := by omega
    let s := (range (2*m+2)).filter fun p => p.Prime ∧ p-1 ∣ 2*m
    have hs : ∀ p∈s, p.Prime := fun _ hp => (mem_filter.mp hp).2.1
    have hmem (p : ℕ) (hp : p.Prime) (hd : p∣n) : p∈s ↔ p-1∣n-1 := by
      have hb := Nat.le_of_dvd (by omega : 0<n) hd
      simp [s,hp,hkm,show p < 2*m+2 by omega]
    obtain ⟨z,hz⟩ := Bernoulli.vonStaudt_clausen m
    have hB : bernoulli' (n-1) = bernoulli (2*m) := by
      rw [← bernoulli_eq_bernoulli'_of_ne_one (by omega : n-1 ≠ 1),hkm]
    have hparts := fraction_parts hs (show (z:ℚ)=bernoulli' (n-1) + ∑ p∈s, (1:ℚ)/p from hB ▸ hz)
    rw [hparts.1,hparts.2]
    exact pointwiseParts hn hs hmem z
  · have hB := bernoulli'_eq_zero_of_odd ho (by omega : 1<n-1)
    have he : Even n := by obtain ⟨a,ha⟩ := ho; exact ⟨a+1, by omega⟩
    constructor
    · rintro ⟨k,hk⟩
      simp [hB] at hk
      have hd : (n:ℤ) ∣ (1:ℤ) := ⟨k*n, by linear_combination hk⟩
      have hn1 : n∣1 := Int.natCast_dvd_natCast.mp hd
      have := Nat.le_of_dvd (by decide : 0<1) hn1
      omega
    · intro hl
      exact (excludeEven h2 he hl).elim

end OMA.Kellner

theorem OMA.solution : OMA.R_AgohGiuga_agoh_giuga_R1.H1 := OMA.Kellner.agohBridge
