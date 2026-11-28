import OMAStatements.S_mo_487715

/-!
This proves the negacyclic Parseval identity in the first line of the proof of
Lemma 6 in the May 2023 HAETAE specification. For a primitive 2n-th root ζ,
the Fourier frequencies have the form ζ(ζ²)^j. Twisting a coefficient of
index k by ζ^k reduces the transform to the ordinary length-n Fourier matrix
with primitive root ζ². Orthogonality gives the norm formula. The odd
frequencies are precisely the roots of Xⁿ+1, so evaluation respects reduction
in the polynomial quotient.

Source: https://mathoverflow.net/questions/487715
Specification: https://csrc.nist.gov/csrc/media/Projects/pqc-dig-sig/documents/round-1/spec-files/haetae-spec-web.pdf
-/

namespace OMA.S_mo_487715
open Polynomial Finset
open scoped ComplexConjugate

private lemma half_power {n : ℕ} (hn : 0<n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2*n)) :
    ζ^n = -1 :=
  (IsPrimitiveRoot.pow (by omega : 0<2*n) hζ (mul_comm 2 n)).eq_neg_one_of_two_right

private lemma frequencies {n : ℕ} (hn : 0<n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2*n)) (z : ℂ) :
    z^n = -1 ↔ ∃ i < n, frequency ζ i = z := by
  have hw : IsPrimitiveRoot (ζ^2) n := IsPrimitiveRoot.pow (by omega) hζ rfl
  have hfac := X_pow_sub_C_eq_prod hw hn (half_power hn hζ)
  have e := congrArg (Polynomial.eval z) hfac
  simp only [eval_sub, eval_pow, eval_X, eval_C, eval_prod] at e
  rw [← sub_eq_zero, e, Finset.prod_eq_zero_iff]
  simp only [sub_eq_zero, Finset.mem_range]
  change (∃ i<n, z=(ζ^2)^i*ζ) ↔ _
  simp only [frequency, pow_succ, pow_mul, eq_comm (a:=z)]

private lemma twist (ζ : ℂ) (k a : ℕ) :
    (frequency ζ k)^a = ζ^a * ((ζ^2)^a)^k := by
  rw [frequency, pow_add, pow_one, mul_pow, mul_comm]
  congr 1
  simp only [← pow_mul]
  congr 1
  ring

private lemma orthogonal {n : ℕ} (hn : 0<n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2*n))
    (a b : ℕ) (ha : a<n) (hb : b<n) :
    ∑ k ∈ range n, frequency ζ k ^ a * conj (frequency ζ k ^ b) =
      if a=b then (n:ℂ) else 0 := by
  let w := ζ^2
  have hw : IsPrimitiveRoot w n := IsPrimitiveRoot.pow (by omega) hζ rfl
  have normζ := hζ.norm'_eq_one (by omega)
  have normw := hw.norm'_eq_one hn.ne'
  let u := w^a * conj (w^b)
  have factor : ∑ k ∈ range n, frequency ζ k ^ a * conj (frequency ζ k ^ b) =
      (ζ^a*conj (ζ^b)) * ∑ k ∈ range n, u^k := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro k _
    simp only [twist, map_mul, map_pow, u, w, mul_pow]
    ring
  rw [factor]
  split_ifs with hab
  · subst b
    have hu : u = 1 := by simp [u, Complex.mul_conj', norm_pow, normw]
    rw [Complex.mul_conj']; simp [hu, norm_pow, normζ]
  · have hu : u ≠ 1 := by
      intro hh
      have hg : w^b * conj (w^b) = 1 := by rw [Complex.mul_conj']; simp [norm_pow, normw]
      have hne : conj (w^b) ≠ 0 := by simpa using pow_ne_zero b (hw.ne_zero hn.ne')
      exact hab (hw.pow_inj ha hb (mul_right_cancel₀ hne (hh.trans hg.symm)))
    have hperiod (i : ℕ) : (w^i)^n = 1 := by rw [←pow_mul, mul_comm, pow_mul, hw.pow_eq_one, one_pow]
    have huN : u^n=1 := by simp only [u, mul_pow, ← map_pow, hperiod, map_one, one_mul]
    have hz := geom_sum_mul u n
    rw [huN, sub_self, mul_eq_zero, or_iff_left (sub_ne_zero.mpr hu)] at hz
    rw [hz, mul_zero]

end OMA.S_mo_487715
namespace OMA.S_mo_487715
open Polynomial Finset
open scoped ComplexConjugate

private lemma parseval {n : ℕ} (hn : 0<n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2*n)) (f : ℕ→ℂ) :
    ∑ k ∈ range n, ‖∑ a ∈ range n, f a*(frequency ζ k)^a‖^2 =
      (n:ℝ)*∑ a ∈ range n, ‖f a‖^2 := by
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.mul_conj']
  calc
    _ = ∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n,
        (f a * conj (f b)) * (frequency ζ k ^ a * conj (frequency ζ k ^ b)) := by
      simp only [map_sum, map_mul, sum_mul, mul_sum]
      apply sum_congr rfl; intro k _
      rw [sum_comm]
      apply sum_congr rfl; intro a _
      apply sum_congr rfl; intro b _
      ring
    _ = ∑ a ∈ range n, ∑ b ∈ range n, (f a * conj (f b)) *
        ∑ k ∈ range n, frequency ζ k ^ a * conj (frequency ζ k ^ b) := by
      rw [sum_comm]
      apply sum_congr rfl; intro a _
      rw [sum_comm]
      simp only [mul_sum]
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl; intro a ha
      rw [Finset.sum_eq_single_of_mem a ha, orthogonal hn hζ a a (mem_range.mp ha) (mem_range.mp ha),
        if_pos rfl, mul_comm]
      intro b hb hba
      rw [orthogonal hn hζ a b (mem_range.mp ha) (mem_range.mp hb), if_neg hba.symm, mul_zero]

private lemma term_identity {n : ℕ} (hn : 0<n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2*n))
    (c s : ℤ[X]) : (n:ℝ)*coefficientNormSq n (representative n (c*s)) =
      ∑ j ∈ range n, ‖aeval (frequency ζ j) c‖^2 * ‖aeval (frequency ζ j) s‖^2 := by
  let f := representative n (c*s)
  have hdeg : f.natDegree<n := by
    have H := natDegree_modByMonic_lt (c*s) (monic_X_pow_add_C (1:ℤ) hn.ne')
      (X_pow_add_C_ne_one hn 1)
    rw [natDegree_X_pow_add_C] at H
    simpa only [f, representative, C_1] using H
  refine (parseval hn hζ (fun k => (f.coeff k:ℂ))).symm.trans ?_
  apply sum_congr rfl
  intro j hj
  have ht : (frequency ζ j)^n = -1 := (frequencies hn hζ _).mpr ⟨j,mem_range.mp hj,rfl⟩
  have hroot : aeval (frequency ζ j) ((X:ℤ[X])^n+1) = 0 := by simp [ht]
  have hev : aeval (frequency ζ j) f = aeval (frequency ζ j) (c*s) :=
    aeval_modByMonic_eq_self_of_root hroot
  rw [aeval_eq_sum_range' hdeg, map_mul] at hev
  simp only [zsmul_eq_mul] at hev
  rw [hev, norm_mul, mul_pow]

end OMA.S_mo_487715

open OMA.S_mo_487715 Finset Polynomial in
theorem OMA.solution : type_of% @OMA.S_mo_487715.main := by
  intro d n ζ hζ
  have hn : 0<n := by change 0<2^d; positivity
  refine ⟨?_,frequencies hn hζ,?_⟩
  · intro i _
    apply hζ.pow_of_coprime
    have ho : Odd (2*i+1) := ⟨i,rfl⟩
    exact Nat.coprime_mul_iff_right.mpr ⟨ho.coprime_two_right, ho.coprime_two_right.pow_right d⟩
  · intro m s c
    rw [mul_sum]
    simp_rw [term_identity hn hζ]
    rw [sum_comm]
    simp only [mul_sum]
