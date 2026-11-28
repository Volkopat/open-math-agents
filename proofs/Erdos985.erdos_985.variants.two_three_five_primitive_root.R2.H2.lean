import OMAReductions.R_Erdos985_erdos_985_variants_two_three_five_primitive_root_R2
import Mathlib

/-!
Heath-Brown, Artin's conjecture for primitive roots, Q. J. Math. 37 (1986),
27–38. A pigeonhole collision among the residues of products of powers of
2, 3 and 5 assigns each prime to a bounded difference of products. The number
of products is cubic in the side length, and each difference has only linearly
many prime divisors in that length.
-/

namespace OMA.HeathBrownThreeGenerators

open Finset
open scoped Classical
open OMA.R_Erdos985_erdos_985_variants_two_three_five_primitive_root_R2

private def smooth (v : ℕ × ℕ × ℕ) : ℕ := 2 ^ v.1 * 3 ^ v.2.1 * 5 ^ v.2.2

private theorem smooth_injective : Function.Injective smooth := by
  rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h
  have fac {q : ℕ} (hq : q.Prime) (i : ℕ) : (q ^ i).factorization = Finsupp.single q i := by
    rw [Nat.factorization_pow, hq.factorization, Finsupp.smul_single, smul_eq_mul, mul_one]
  have hfac := congrArg Nat.factorization h
  simp only [smooth, Nat.factorization_mul (by positivity : 2 ^ a * 3 ^ b ≠ 0)
    (by positivity : 5 ^ c ≠ 0), Nat.factorization_mul (by positivity : 2 ^ d * 3 ^ e ≠ 0)
    (by positivity : 5 ^ f ≠ 0), Nat.factorization_mul (by positivity : 2 ^ a ≠ 0)
    (by positivity : 3 ^ b ≠ 0), Nat.factorization_mul (by positivity : 2 ^ d ≠ 0)
    (by positivity : 3 ^ e ≠ 0), fac (q := 2) Nat.prime_two, fac (q := 3) Nat.prime_three,
    fac (q := 5) (by decide)] at hfac
  have ha : a = d := by simpa using DFunLike.congr_fun hfac 2
  have hb : b = e := by simpa using DFunLike.congr_fun hfac 3
  have hc : c = f := by simpa using DFunLike.congr_fun hfac 5
  simp [ha, hb, hc]

private def positive (z : ℤ × ℤ × ℤ) : ℕ × ℕ × ℕ := (z.1.toNat, z.2.1.toNat, z.2.2.toNat)
private def negative (z : ℤ × ℤ × ℤ) : ℕ × ℕ × ℕ := ((-z.1).toNat, (-z.2.1).toNat, (-z.2.2).toNat)
private def discrepancy (z : ℤ × ℤ × ℤ) : ℕ :=
  max 1 (((smooth (positive z) : ℤ) - (smooth (negative z) : ℤ)).natAbs)

private def box (m : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  let I := Icc (-(m : ℤ)) (m : ℤ)
  I ×ˢ (I ×ˢ I)

private theorem smooth_split (u v : ℕ × ℕ × ℕ) :
    smooth u = smooth (min u.1 v.1, min u.2.1 v.2.1, min u.2.2 v.2.2) *
      smooth (u.1 - v.1, u.2.1 - v.2.1, u.2.2 - v.2.2) := by
  have hm (i j : ℕ) : min i j + (i - j) = i := by omega
  simp only [smooth]
  calc
    _ = 2 ^ (min u.1 v.1 + (u.1 - v.1)) *
        3 ^ (min u.2.1 v.2.1 + (u.2.1 - v.2.1)) *
        5 ^ (min u.2.2 v.2.2 + (u.2.2 - v.2.2)) := by simp only [hm]
    _ = _ := by simp only [pow_add]; ring

private theorem nonzero_base {K : Type*} [Field K] {a n : ℕ} (hn : 0 < n)
    (h : (a : K)^n = 1) : (a : K) ≠ 0 := by
  intro hz
  rw [hz, zero_pow hn.ne'] at h
  exact zero_ne_one h

private theorem hits_box {m p N : ℕ} (hp : p.Prime) (hN : 0 < N) (hm : N < m^3)
    (h2 : (2 : ZMod p)^N = 1) (h3 : (3 : ZMod p)^N = 1) (h5 : (5 : ZMod p)^N = 1) :
    p ∈ (box m).biUnion (fun z => (discrepancy z).primeFactors) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let roots := Polynomial.nthRootsFinset N (1 : ZMod p)
  let exponents := Fin m × Fin m × Fin m
  let lift : exponents → ℕ × ℕ × ℕ := fun u => (u.1.val, u.2.1.val, u.2.2.val)
  have swap_pow (a : ZMod p) (b : ℕ) : (a ^ b)^N = (a ^ N)^b := by
    rw [← pow_mul, Nat.mul_comm b N, pow_mul]
  let f : exponents → roots := fun u => ⟨smooth (lift u), by
    rw [Polynomial.mem_nthRootsFinset hN, smooth]
    push_cast
    simp only [mul_pow, swap_pow, h2, h3, h5, one_pow, mul_one]⟩
  have hcard : roots.card ≤ N := by
    change (Polynomial.nthRootsFinset N (1 : ZMod p)).card ≤ N
    rw [Polynomial.nthRootsFinset_def]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
  have hnot : ¬ Function.Injective f := by
    intro hf
    have hh := Fintype.card_le_of_injective f hf
    simp only [exponents, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] at hh
    nlinarith
  simp only [Function.Injective, not_forall] at hnot
  obtain ⟨i, j, heq, hne⟩ := hnot
  have hu : lift i ≠ lift j := by
    intro hh
    apply hne
    exact Prod.ext (Fin.ext (congrArg Prod.fst hh))
      (Prod.ext (Fin.ext (congrArg (fun t => t.2.1) hh))
        (Fin.ext (congrArg (fun t => t.2.2) hh)))
  let u := lift i
  let v := lift j
  let z : ℤ × ℤ × ℤ := ((u.1 : ℤ) - v.1, (u.2.1 : ℤ) - v.2.1, (u.2.2 : ℤ) - v.2.2)
  have hi := i.1.isLt
  have hj := j.1.isLt
  have hi' := i.2.1.isLt
  have hj' := j.2.1.isLt
  have hi'' := i.2.2.isLt
  have hj'' := j.2.2.isLt
  have hz : z ∈ box m := by
    simp only [box, mem_product, mem_Icc, z, u, v, lift]
    omega
  have ht (a b : ℕ) : ((a : ℤ) - (b : ℤ)).toNat = a - b := by omega
  have hpz : positive z = (u.1 - v.1, u.2.1 - v.2.1, u.2.2 - v.2.2) := by
    simp [positive, z, ht]
  have hnz : negative z = (v.1 - u.1, v.2.1 - u.2.1, v.2.2 - u.2.2) := by
    simp [negative, z]
  have hdiff : smooth (positive z) ≠ smooth (negative z) := by
    intro he
    have hc := smooth_injective he
    rw [hpz, hnz] at hc
    apply hu
    change u = v
    have coord (a b : ℕ) (h : a - b = b - a) : a = b := by omega
    exact Prod.ext (coord _ _ (congrArg Prod.fst hc))
      (Prod.ext (coord _ _ (congrArg (fun t => t.2.1) hc))
        (coord _ _ (congrArg (fun t => t.2.2) hc)))
  let B := smooth (min u.1 v.1, min u.2.1 v.2.1, min u.2.2 v.2.2)
  have hB : (B : ZMod p) ≠ 0 := by
    unfold B smooth
    push_cast
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (nonzero_base (a := 2) hN h2))
      (pow_ne_zero _ (nonzero_base (a := 3) hN h3))) (pow_ne_zero _ (nonzero_base (a := 5) hN h5))
  have hcast : (smooth u : ZMod p) = smooth v := congrArg Subtype.val heq
  have hcast' : (smooth (positive z) : ZMod p) = smooth (negative z) := by
    apply mul_left_cancel₀ hB
    rw [← Nat.cast_mul, ← Nat.cast_mul]
    rw [hpz, hnz]
    exact (congrArg (Nat.cast : ℕ → ZMod p) (smooth_split u v)).symm.trans
      (hcast.trans (by simpa only [B, min_comm] using congrArg (Nat.cast : ℕ → ZMod p) (smooth_split v u)))
  have hd : (p : ℤ) ∣ (smooth (positive z) : ℤ) - (smooth (negative z) : ℤ) := by
    rw [← CharP.intCast_eq_zero_iff (ZMod p) p]
    push_cast
    rw [hcast', sub_self]
  have hd' := Int.natAbs_dvd_natAbs.mpr hd
  have hpos : 0 < ((smooth (positive z) : ℤ) - (smooth (negative z) : ℤ)).natAbs := by
    rw [Int.natAbs_pos, sub_ne_zero]
    exact_mod_cast hdiff
  refine mem_biUnion.mpr ⟨z, hz, Nat.mem_primeFactors.mpr ⟨hp, ?_, by unfold discrepancy; omega⟩⟩
  rw [discrepancy, max_eq_right hpos]
  simpa only [Int.natAbs_natCast] using hd'

private theorem discrepancy_bound {m : ℕ} (hm : 0 < m) {z : ℤ × ℤ × ℤ} (hz : z ∈ box m) :
    (discrepancy z).primeFactors.card ≤ 5 * m := by
  simp only [box, mem_product, mem_Icc] at hz
  have ht (v : ℤ) (hv : -(m : ℤ) ≤ v ∧ v ≤ m) : v.toNat ≤ m ∧ (-v).toNat ≤ m := by omega
  have ha := ht z.1 hz.1
  have hb := ht z.2.1 hz.2.1
  have hc := ht z.2.2 hz.2.2
  have hbnd (v : ℕ × ℕ × ℕ) (h1 : v.1 ≤ m) (h2 : v.2.1 ≤ m) (h3 : v.2.2 ≤ m) :
      smooth v ≤ 30 ^ m := by
    rw [smooth, show 30 = 2 * 3 * 5 from rfl, mul_pow, mul_pow]
    gcongr <;> norm_num
  have hl := hbnd (positive z) ha.1 hb.1 hc.1
  have hr := hbnd (negative z) ha.2 hb.2 hc.2
  have hs : discrepancy z ≤ 30 ^ m := by
    unfold discrepancy
    have hh : 0 < 30 ^ m := by positivity
    omega
  have hstrict : 30 ^ m < 2 ^ (5 * m) := by
    rw [pow_mul]
    exact Nat.pow_lt_pow_left (by decide) hm.ne'
  exact (card_pf_lt (by unfold discrepancy; omega) (hs.trans_lt hstrict)).le

private theorem card_box (m : ℕ) (hm : 0 < m) : (box m).card ≤ (3 * m)^3 := by
  have hc : (Icc (-(m : ℤ)) (m : ℤ)).card ≤ 3 * m := by
    rw [Int.card_Icc]
    omega
  simp only [box, card_product]
  rw [pow_succ, pow_succ, pow_one, mul_assoc]
  gcongr

private theorem count {x y m : ℕ} (hm : 0 < m) (hy : y < m^3) :
    ((range (x + 1)).filter (fun p => p.Prime ∧ ∃ N ∈ Icc 1 y,
      (2 : ZMod p)^N = 1 ∧ (3 : ZMod p)^N = 1 ∧ (5 : ZMod p)^N = 1)).card ≤ 135 * m^4 := by
  classical
  have hsub : ((range (x + 1)).filter (fun p => p.Prime ∧ ∃ N ∈ Icc 1 y,
      (2 : ZMod p)^N = 1 ∧ (3 : ZMod p)^N = 1 ∧ (5 : ZMod p)^N = 1)) ⊆
      (box m).biUnion (fun z => (discrepancy z).primeFactors) := by
    intro p hp
    obtain ⟨-, hpr, N, hN, h2, h3, h5⟩ := mem_filter.mp hp
    have hN := mem_Icc.mp hN
    exact hits_box hpr hN.1 (hN.2.trans_lt hy) h2 h3 h5
  calc
    _ ≤ _ := card_le_card hsub
    _ ≤ ∑ z ∈ box m, (discrepancy z).primeFactors.card := card_biUnion_le
    _ ≤ (box m).card • (5 * m) := sum_le_card_nsmul _ _ _ (fun _ hz => discrepancy_bound hm hz)
    _ ≤ (3 * m)^3 * (5 * m) := by rw [nsmul_eq_mul]; gcongr; exact card_box m hm
    _ = 135 * m^4 := by ring

private theorem solution : H2 := by
  refine ⟨2160, fun x y => ?_⟩
  by_cases hy : y = 0
  · subst y
    simp
  let w := (y : ℝ) ^ (1 / 3 : ℝ)
  let m := ⌊w⌋₊ + 1
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hy)
  have hw1 : 1 ≤ w := Real.one_le_rpow hy1 (by norm_num)
  have hwm : w < (m : ℝ) := by
    simpa [m] using Nat.lt_floor_add_one w
  have hml : (m : ℝ) ≤ 2 * w := by
    have hfloor := Nat.floor_le (show 0 ≤ w by linarith)
    simp only [m, Nat.cast_add, Nat.cast_one]
    linarith
  have hw3 : w ^ (3 : ℕ) = y := by
    rw [show w = (y : ℝ) ^ (1 / 3 : ℝ) from rfl,
      ← Real.rpow_mul_natCast (Nat.cast_nonneg y)]
    norm_num
  have hw4 : w ^ (4 : ℕ) = (y : ℝ) ^ (4 / 3 : ℝ) := by
    rw [show w = (y : ℝ) ^ (1 / 3 : ℝ) from rfl,
      ← Real.rpow_mul_natCast (Nat.cast_nonneg y)]
    congr 1
    norm_num
  have hcube : y < m^3 := by
    exact_mod_cast (hw3.symm.trans_lt (pow_lt_pow_left₀ hwm (by linarith) (by decide : (3 : ℕ) ≠ 0)))
  have hc := count (x := x) (y := y) (m := m) (by simp [m]) hcube
  calc
    _ ≤ 135 * (m : ℝ)^4 := by exact_mod_cast hc
    _ ≤ 135 * (2 * w)^4 := by gcongr
    _ = 2160 * (y : ℝ) ^ (4 / 3 : ℝ) := by rw [mul_pow, hw4]; ring

end OMA.HeathBrownThreeGenerators

theorem OMA.solution : OMA.R_Erdos985_erdos_985_variants_two_three_five_primitive_root_R2.H2 :=
  OMA.HeathBrownThreeGenerators.solution
