import OMAStatements.S_mo_348186
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# A sum of at least two consecutive positive like powers has an odd factor
Credit: @witeg4. Problem posed by Pruthviraj, https://mathoverflow.net/q/348186.
Related modular restrictions, even-block sums and the reflection argument were
discussed by Andrea Marino, Luca Vantaggio, and Gerhard Paseman in the linked
threads. See https://math.stackexchange.com/questions/3369713 .
The last step adjoins or removes one even endpoint after bounding the odd
length by a Mersenne number via Fermat's little theorem. The argument covers
every odd common difference in the companion question; set d=1 for the target.
-/
open scoped BigOperators
open Finset
namespace ConsecutivePowers

private lemma obstruct {d s t : ℕ} (hd : 1 < d) (ho : Odd d)
    (hs : ((2 * s : ℕ) : ZMod d) = 0) : s ≠ 2 ^ t := by
  intro h
  have hdiv := (ZMod.natCast_eq_zero_iff (2 * s) d).mp hs
  rw [h, ← pow_succ'] at hdiv
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  cases k with
  | zero => simp_all
  | succ k =>
    obtain ⟨j, hj⟩ := ho
    rw [pow_succ] at hk
    omega

private lemma shift_square (x d : ℕ) (hd : Even d) :
    (x+d)^2 ≡ x^2 [MOD 2*d] := by
  obtain ⟨a,ha⟩ := hd
  rw [show (x+d)^2 = x^2 + (x+a)*(2*d) by rw [ha]; ring]
  exact Nat.add_mul_modulus_modEq_iff.mpr (Nat.ModEq.refl _)

private lemma pair_parity (x m : ℕ) (hm : 0 < m) :
    x^m + (x+1)^m ≡ 1 [MOD 2] := by
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx
  · have h0 : x ≡ 0 [MOD 2] := hx
    have h1 : x+1 ≡ 1 [MOD 2] := by simpa using h0.add_right 1
    simpa [zero_pow hm.ne'] using (h0.pow m).add (h1.pow m)
  · have h1 : x ≡ 1 [MOD 2] := hx
    have h0 : x+1 ≡ 0 [MOD 2] := (h1.add_right 1).trans (by decide)
    simpa [zero_pow hm.ne'] using (h1.pow m).add (h0.pow m)

/-- A complete block of length 2^(k+1) has residue 2^k for any positive even exponent. -/
theorem even_block (k a m : ℕ) (hm : 0 < m) (he : Even m) :
    (∑ i ∈ Finset.range (2^(k+1)), (a+i)^m) ≡ 2^k [MOD 2^(k+1)] := by
  induction k with
  | zero => simpa [Finset.sum_range_succ] using pair_parity a m hm
  | succ k ih =>
    let d := 2^(k+1)
    have hd : Even d := ⟨2^k, by dsimp [d]; rw [pow_succ]; omega⟩
    have hs (i : ℕ) : (a+(d+i))^m ≡ (a+i)^m [MOD 2*d] := by
      obtain ⟨j,hj⟩ := he
      rw [show m=2*j by omega, pow_mul, pow_mul, show a+(d+i) = (a+i)+d by omega]
      exact (shift_square _ _ hd).pow j
    have hsum := Nat.ModEq.sum (s := Finset.range d) (fun i _ => hs i)
    have hh : (∑ i ∈ Finset.range d, (a+i)^m) ≡ 2^k [MOD d] := ih
    change (∑ i ∈ Finset.range (2^(k+1+1)), (a+i)^m) ≡ d [MOD 2^(k+1+1)]
    rw [show 2^(k+1+1)=d+d by dsimp [d]; rw [pow_succ _ (k+1)]; omega,
      Finset.sum_range_add]
    have h2 := hh.mul_left' 2
    change 2 * (∑ i ∈ Finset.range d, (a+i)^m) ≡ 2*2^k [MOD 2*d] at h2
    rw [show d+d = 2*d by omega]
    apply ((Nat.ModEq.refl _).add hsum).trans
    simpa only [two_mul, show 2^k+2^k=d by dsimp [d]; rw [pow_succ]; omega] using h2

theorem even_blocks (k b a m : ℕ) (hm : 0 < m) (he : Even m) :
    (∑ i ∈ Finset.range (2^(k+1)*b), (a+i)^m) ≡ 2^k*b [MOD 2^(k+1)] := by
  induction b with
  | zero => simp [Nat.ModEq]
  | succ b ih =>
    rw [Nat.mul_succ, Nat.mul_succ, Finset.sum_range_add]
    have h := even_block k (a+2^(k+1)*b) m hm he
    simpa only [Nat.add_assoc] using ih.add h

private lemma complete_residues (p : ℕ) [NeZero p] (f : ZMod p → ZMod p) :
    ∑ i ∈ range p, f i = ∑ x : ZMod p, f x := by
  obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne p)
  rw [← Fin.sum_univ_eq_sum_range]
  conv_rhs => rw [← (ZMod.finEquiv (q+1)).toEquiv.sum_comp]
  apply sum_congr rfl
  intro i _
  congr 1
  exact ZMod.natCast_zmod_val (n := q+1) i

private lemma positive_power_sum (p m : ℕ) [Fact p.Prime] (hm : m ≠ 0) :
    (∑ x : ZMod p, x^m) = if p-1 ∣ m then -1 else 0 := by
  classical
  let K := ZMod p
  let emb : Kˣ ↪ K := ⟨fun x => x, Units.val_injective⟩
  have hmap : univ.map emb = univ \ {(0 : K)} := by
    ext x
    simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff,
      mem_singleton, emb] using! isUnit_iff_ne_zero
  calc
    ∑ x : K, x^m = ∑ x ∈ univ \ {(0 : K)}, x^m := by
      rw [← sum_sdiff ({0} : Finset K).subset_univ, sum_singleton, zero_pow hm, add_zero]
    _ = ∑ x : Kˣ, (x:K)^m := by simp [emb, ← hmap, univ.sum_map emb]
    _ = _ := by simpa [K, ZMod.card] using FiniteField.sum_pow_units K m

/-- The exact residue modulo p of a sum taken over b complete blocks. -/
theorem prime_blocks (p m b a : ℕ) (hp : p.Prime) (hm : 0 < m) :
    ((∑ i ∈ range (p*b), (a+i)^m : ℕ) : ZMod p) =
      (b : ZMod p) * (if p-1 ∣ m then -1 else 0) := by
  let : Fact p.Prime := ⟨hp⟩
  have one (s : ℕ) : (∑ i ∈ range p, ((s : ZMod p)+i)^m) =
      if p-1 ∣ m then -1 else 0 := calc
    _ = ∑ x : ZMod p, ((s : ZMod p)+x)^m :=
      complete_residues p (fun x => ((s : ZMod p)+x)^m)
    _ = ∑ x : ZMod p, x^m := Equiv.sum_comp (Equiv.addLeft (s : ZMod p)) (fun x => x^m)
    _ = _ := positive_power_sum p m hm.ne'
  push_cast
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ, sum_range_add, ih]
    push_cast
    simp only [ZMod.natCast_self, zero_mul, zero_add, one, add_mul, one_mul]

/-- For even positive length at most 2^m, the sum cannot vanish modulo 2^m. -/
theorem short_even_block {L m : ℕ} (a : ℕ) (hL : 0 < L) (heL : Even L)
    (hm : 0 < m) (he : Even m) (hle : L ≤ 2^m) :
    ¬ 2^m ∣ (∑ i ∈ range L, (a+i)^m) := by
  obtain ⟨s,b,hb,hs⟩ := Nat.exists_eq_two_pow_mul_odd hL.ne'
  cases s with
  | zero =>
    simp at hs
    obtain ⟨i,hi⟩ := heL
    obtain ⟨j,hj⟩ := hb
    omega
  | succ k =>
    subst L
    have hb1 : 1 ≤ b := by obtain ⟨j,hj⟩ := hb; omega
    have hp : 2^(k+1) ≤ 2^m := (Nat.le_mul_of_pos_right _ hb1).trans hle
    have hkm : k+1 ≤ m := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hp
    intro hdiv
    have hz := Nat.modEq_zero_iff_dvd.mpr (dvd_trans (pow_dvd_pow 2 hkm) hdiv)
    have hv := (even_blocks k b a m hm he).symm.trans hz
    have dd := Nat.modEq_zero_iff_dvd.mp hv
    rw [pow_succ, Nat.mul_dvd_mul_iff_left (Nat.two_pow_pos k)] at dd
    obtain ⟨j,hj⟩ := hb
    omega

end ConsecutivePowers

namespace OddStride
open Finset ConsecutivePowers

def ap (a d L m : ℕ) := ∑ i ∈ range L, (a+i*d)^m

/-- Scaling by the invertible step turns a modular progression into
a consecutive interval at every length. -/
theorem scale (a d q : ℕ) (hc : d.Coprime q) :
    ∃ b : ℕ, ∀ L m, ap a d L m ≡ d^m * ∑ i ∈ range L, (b+i)^m [MOD q] := by
  obtain ⟨u,hu⟩ := (ZMod.isUnit_iff_coprime d q).mpr hc
  let z := (↑u⁻¹ : ZMod q) * a
  by_cases hq : q=0
  · subst q
    simp at hc
    subst d
    exact ⟨a,fun L m => by simp [ap]⟩
  have : NeZero q := ⟨hq⟩
  refine ⟨z.val,fun L m => ?_⟩
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  simp only [ap,Nat.cast_sum,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,ZMod.natCast_zmod_val,Finset.mul_sum]
  apply sum_congr rfl
  intro i _
  rw [← mul_pow, ← hu]
  congr 1
  dsimp [z]
  rw [mul_add,← mul_assoc,Units.mul_inv,one_mul,mul_comm (u : ZMod q)]

private theorem no_two_block (a d k b m : ℕ) (hd : Odd d) (hb : Odd b)
    (hm : 0 < m) (he : Even m) :
    ¬ 2^(k+1) ∣ ap a d (2^(k+1)*b) m := by
  obtain ⟨x,hx⟩ := scale a d (2^(k+1)) (hd.coprime_two_right.pow_right _)
  intro hh
  have hv := ((hx _ _).dvd_iff (dvd_refl _)).mp hh
  have hcop : (2^(k+1)).Coprime (d^m) := (hd.coprime_two_left.pow_left _).pow_right _
  have hdiv := hcop.dvd_of_dvd_mul_left hv
  have hbad := ((even_blocks k b x m hm he).dvd_iff (dvd_refl _)).mp hdiv
  rw [pow_succ,Nat.mul_dvd_mul_iff_left (Nat.two_pow_pos k)] at hbad
  obtain ⟨j,hj⟩ := hb
  omega

theorem even_length_ap (a d L m t : ℕ) (ha : 0 < a) (hd : Odd d) (hl : 0 < L) (hel : Even L)
    (hm : 0 < m) (he : Even m) : ap a d L m ≠ 2^t := by
  obtain ⟨s,b,hb,hs⟩ := Nat.exists_eq_two_pow_mul_odd hl.ne'
  cases s with
  | zero =>
    simp at hs; obtain ⟨j,hj⟩ := hb; obtain ⟨i,hi⟩ := hel; omega
  | succ k =>
    subst L
    intro eq
    have hsize : 2^(k+1)*b ≤ ap a d (2^(k+1)*b) m := by
      simpa [ap] using (sum_le_sum (s:=range (2^(k+1)*b)) (f:=fun _=>1)
        (g:=fun i=>(a+i*d)^m) fun i _=>Nat.one_le_pow _ _ (by omega))
    have h1 : 1≤b := by obtain ⟨z,hz⟩ := hb; omega
    have ht : k+1 ≤ t := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      ((Nat.le_mul_of_pos_right _ h1).trans (hsize.trans_eq eq))
    exact no_two_block a d k b m hd hb hm he (eq ▸ pow_dvd_pow 2 ht)

theorem short_even_ap (a d L m : ℕ) (hd : Odd d) (hl : 0 < L) (hel : Even L)
    (hm : 0 < m) (he : Even m) (hle : L ≤ 2^m) : ¬ 2^m ∣ ap a d L m := by
  obtain ⟨x,hx⟩ := scale a d (2^m) (hd.coprime_two_right.pow_right _)
  intro hh
  have h := ((hx _ _).dvd_iff (dvd_refl _)).mp hh
  have hcop : (2^m).Coprime (d^m) := (hd.coprime_two_left.pow_left _).pow_right _
  exact short_even_block x hl hel hm he hle (hcop.dvd_of_dvd_mul_left h)


/-- For an odd prime divisor p of the length, a sum equal to a power of two
requires p-1 to divide the exponent, and p² cannot divide the length. -/
theorem prime_test {p a d L m t : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 0 < m)
    (hpL : p ∣ L) (h : ap a d L m = 2^t) : p-1 ∣ m ∧ ¬ p^2 ∣ L := by
  obtain ⟨v,rfl⟩ := hpL
  let : Fact p.Prime := ⟨hp⟩
  have nz : (2 : ZMod p)^t ≠ 0 := pow_ne_zero _ (by
    intro z
    have h2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using z)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2))
  have he : ((ap a d (p*v) m : ℕ) : ZMod p) = (2:ZMod p)^t := by rw [h]; push_cast; rfl
  have hn : ¬ p ∣ d := by
    intro hpD
    have h0 := (ZMod.natCast_eq_zero_iff d p).mpr hpD
    have hz : ((ap a d (p*v) m : ℕ) : ZMod p) = 0 := by
      simp [ap,Nat.cast_sum,h0,nsmul_eq_mul]
    exact nz (he.symm.trans hz)
  obtain ⟨x,hx⟩ := scale a d p (hp.coprime_iff_not_dvd.mpr hn).symm
  have hres := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hx (p*v) m)
  rw [he,Nat.cast_mul,Nat.cast_pow,prime_blocks p m v x hp hm] at hres
  constructor
  · by_contra hbad
    exact nz (by simpa [hbad] using hres)
  · rintro ⟨z,hz⟩
    rw [pow_two,Nat.mul_assoc] at hz
    have hv := Nat.eq_of_mul_eq_mul_left hp.pos hz
    exact nz (by simpa [hv,ZMod.natCast_self] using hres)

theorem odd_length_ap {a d L m t : ℕ} (hl : Odd L) (hm : 0 < m) (h : ap a d L m = 2^t) :
    L ∣ 2^m-1 := by
  have hp : 2 ≤ 2^m := calc
    2 = 2^1 := by decide
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hm
  have ntwo : ¬2 ∣ L := by obtain ⟨j,hj⟩ := hl; omega
  have ptest (p : ℕ) (hpr : p.Prime) (hdv : p ∣ L) := prime_test hpr (by
    rintro rfl; exact ntwo hdv) hm hdv h
  have sq : Squarefree L := Nat.squarefree_iff_prime_squarefree.mpr fun p hpr hsq =>
    (ptest p hpr (dvd_trans (dvd_mul_right p p) hsq)).2 (by simpa only [pow_two] using hsq)
  rw [← Nat.prod_primeFactors_of_squarefree sq,Nat.prod_primeFactors_dvd_iff (by omega : 2^m-1 ≠ 0)]
  intro p hpL
  obtain ⟨hpr,hdv,_⟩ := Nat.mem_primeFactors.mp hpL
  have h2 : p ≠ 2 := by rintro rfl; exact ntwo hdv
  obtain ⟨j,hj⟩ := (ptest p hpr hdv).1
  have hf := Nat.ModEq.pow_card_sub_one_eq_one hpr ((Nat.coprime_primes Nat.prime_two hpr).mpr h2.symm)
  have hh : 2^m ≡ 1 [MOD p] := by rw [hj,pow_mul]; simpa using hf.pow j
  exact Nat.mem_primeFactors.mpr ⟨hpr,hh.symm.dvd',by omega⟩

theorem odd_exponent_ap (a d u m t : ℕ) (ha : 0 < a) (hd : Odd d) (hu : 0 < u)
    (hm : Odd m) : ap a d (u+1) m ≠ 2^t := by
  intro eq
  rcases Nat.even_or_odd u with heu | hou
  · let p := (u+1).minFac
    have hpr : p.Prime := Nat.minFac_prime (by omega)
    have hdv : p ∣ u+1 := Nat.minFac_dvd _
    have h2 : p ≠ 2 := by obtain ⟨j,hj⟩ := heu; intro he; rw [he] at hdv; omega
    have hdiv := (prime_test hpr h2 (Odd.pos hm) hdv eq).1
    exact (Nat.not_even_iff_odd.mpr hm) ((Nat.Odd.sub_odd (hpr.odd_of_ne_two h2) (by decide : Odd 1)).trans_dvd hdiv)
  · let q := 2*a+u*d
    have hq : Odd q := by dsimp [q]; exact (even_two_mul a).add_odd (hou.mul hd)
    have hdp : 0 < d := hd.pos
    have hq1 : 1 < q := by dsimp [q]; omega
    apply (ConsecutivePowers.obstruct (d:=q) hq1 hq _ eq)
    unfold ap
    push_cast
    let f := fun i : ℕ => ((a : ZMod q)+i*d)^m
    have hh := Finset.sum_range_reflect f (u+1)
    have hf : (∑ i ∈ range (u+1), f (u+1-1-i)) = -(∑ i ∈ range (u+1), f i) := by
      rw [← Finset.sum_neg_distrib]; apply sum_congr rfl; intro i hi
      have hil : i ≤ u := by simpa using mem_range.mp hi
      have hz : (2 : ZMod q)*a+u*d = 0 := by
        calc
          _ = ((2*a+u*d : ℕ) : ZMod q) := by push_cast; ring
          _ = 0 := ZMod.natCast_self q
      have hr : (a : ZMod q)+((u+1-1-i:ℕ):ZMod q)*d = -(a+i*d : ZMod q) := by
        simp only [Nat.add_sub_cancel,Nat.cast_sub hil]
        linear_combination hz
      simp only [f,hr,hm.neg_pow]
    change 2 * (∑ i ∈ range (u+1), f i) = 0
    linear_combination hf - hh


theorem even_exponent_ap (a d u m t : ℕ) (ha : 0 < a) (hd : Odd d) (hu : 0 < u)
    (hm : 0 < m) (he : Even m) : ap a d (u+1) m ≠ 2^t := by
  intro eq
  rcases Nat.even_or_odd (u+1) with hel | hol
  · exact even_length_ap a d (u+1) m t ha hd (by omega) hel hm he eq
  have hp : 2 ≤ 2^m := calc
    2 = 2^1 := by decide
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hm
  have hlen := Nat.le_of_dvd (show 0 < 2^m-1 by omega) (odd_length_ap hol hm eq)
  have hdp := hd.pos
  have hg : 2^m ≤ ap a d (u+1) m := calc
    _ ≤ (a+1*d)^m := Nat.pow_le_pow_left (by omega) _
    _ ≤ _ := single_le_sum (fun i _ => Nat.zero_le ((a+i*d)^m)) (mem_range.mpr (by omega : 1 < u+1))
  rw [eq] at hg
  have ht := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hg
  have hdv : 2^m ∣ ap a d (u+1) m := eq ▸ pow_dvd_pow 2 ht
  obtain ⟨j,hj⟩ := hol
  rcases Nat.even_or_odd a with hea | hoa
  · have hfirst := pow_dvd_pow_of_dvd (even_iff_two_dvd.mp hea) m
    have hsplit : ap a d (u+1) m = ap (a+d) d u m + a^m := by
      rw [ap,ap,sum_range_succ']; simp only [Nat.zero_mul,Nat.add_zero]
      congr 1; apply sum_congr rfl; intro i _
      rw [show a+(i+1)*d=(a+d)+i*d by ring]
    rw [hsplit] at hdv
    exact short_even_ap (a+d) d u m hd hu ⟨j,by omega⟩ hm he (by omega)
      ((Nat.dvd_add_iff_left hfirst).mpr hdv)
  · have hlast : Even (a+(u+1)*d) := hoa.add_odd ((show Odd (u+1) from ⟨j,hj⟩).mul hd)
    have haug : 2^m ∣ ap a d (u+1+1) m := by
      rw [ap,sum_range_succ]; exact dvd_add hdv (pow_dvd_pow_of_dvd (even_iff_two_dvd.mp hlast) m)
    exact short_even_ap a d (u+1+1) m hd (by omega) ⟨j+1,by omega⟩ hm he (by omega) haug

/-- Any arithmetic progression with positive initial term, odd positive step,
and at least two terms has an odd factor in the sum of its positive like powers. -/
theorem no_power_of_two (a d u m t : ℕ) (ha : 0 < a) (hd : Odd d)
    (hu : 0 < u) (hm : 0 < m) : (∑ i ∈ range (u+1), (a+i*d)^m) ≠ 2^t := by
  rcases Nat.even_or_odd m with he | ho
  · exact even_exponent_ap a d u m t ha hd hu hm he
  · exact odd_exponent_ap a d u m t ha hd hu ho

end OddStride

theorem OMA.solution : type_of% @OMA.S_mo_348186.main := by
  intro a u m t ha hu hm _
  simpa only [Nat.mul_one] using OddStride.no_power_of_two a 1 u m t ha (by decide) hu hm
