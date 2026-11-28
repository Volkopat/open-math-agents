import FormalConjectures.OEIS.«179524»
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.LinearCombination

/-!
# Proof of OeisA179524.conjecture2

For a prime $p \equiv 3, 7 \pmod{20}$ with $2p = x^2 + 5y^2$, we prove
$$\sum_{n=0}^{p-1} a(n) \equiv 2x^2 - 2p \pmod{p^2}, \qquad
  a(n) = \sum_{k=0}^n (-4)^k \binom{n}{k}^2 \binom{n-k}{k}^2.$$

## Proof outline
1. Binomial reflection collapses $\sum_{n=0}^{p-1} a(n) \pmod{p^2}$ to $(-4)^h \widetilde{A}_p(-1/4)$,
   where $h = (p-1)/2$ and $\widetilde{A}_p(z) = \sum_{j=0}^h \binom{2(h-j)}{h-j}^2
   \binom{p+2(h-j)}{2j} z^j$ satisfies a third-order hypergeometric recurrence modulo $p^2$
   with initial value $\binom{2h}{h}^2 \equiv 16^{p-1} \pmod{p^2}$.
2. On $\Gamma_0(2)$ with Fricke involution $W_2$, the weight-2 form $E_2^*(\tau) = 2E_2(2\tau) - E_2(\tau)$
   and weight-8 cusp form $\Delta_8(\tau) = \eta(\tau)^8\eta(2\tau)^8 = \eta_4(\tau)^2$ generate every
   form in $M_{2N}(\Gamma_0(2))$ of $W_2$-eigenvalue $(-1)^N$ as $\sum_{j=0}^{\lfloor N/4 \rfloor}
   c_j \Delta_8^j E_2^{*N-4j}$.
3. From Ramanujan's differential equation $D E_2 = (E_2^2 - E_4)/12$, the $q$-series of $E_2^*$,
   $H_4 = (4E_4(2\tau) - E_4(\tau))/3$, and $P = (E_2(\tau) + 2E_2(2\tau))/3$ satisfy a closed
   differential system showing $H_4 \cdot L_0(E_2^* g) = D^3(g)$ for the ${}_3F_2(\frac14,\frac34,\frac12;1,1;z)$
   Picard-Fuchs operator $L_0$ in $z = 256 \Delta_8 / E_2^{*4} = 256 q U(q)^2$.
   Reducing modulo $(p^2, q^p)$ gives $16^{p-1} U(q)^p E_2^*(q) \equiv \widetilde{A}_p(z(q)) \pmod{p^2, q^p}$.
4. The elementary symmetric functions $S_k(\tau)$ of the $p+1$ Hecke-twisted modular branches
   $\nu_m(\tau)$ lie in $M_{2k(2p-1)}(\Gamma_0(2))$ with $W_2$-sign $(-1)^k$, giving integer polynomials
   $Q_k(u_0)$ in $u_0 = \Delta_8 / E_2^{*4}$ with $\deg Q_1 \le h$, $Q_1(u_0) \equiv \widetilde{A}_p(256 u_0)
   \pmod{p^2}$, and $Q_k \in p^2 \mathbb{Z}[X]$ for $k \ge 2$.
5. At $\tau_0 = \frac{1 + i\sqrt{5}}{2}$, the $p=3$ Hecke polynomial proves $E_2^*(\tau_0) \neq 0$ and
   $z(\tau_0) = -1/4$. The two Fricke-twisted CM endomorphisms $\gamma_\pm = \begin{pmatrix} \pm y & (x \mp y)/2 \\ -(x \pm y) & \pm 3y \end{pmatrix}$
   map $\tau_0$ to $W_2(\tau_0)$ with $\chi(\gamma_\pm) = -1$ and produce the conjugate roots $(-4)^{-h}(x \pm y\sqrt{-5})^2 / 2$,
   whose symmetric sum modulo $p^2$ yields $(-4)^h \widetilde{A}_p(-1/4) \equiv 2x^2 - 2p \pmod{p^2}$.
-/

namespace OMA

/- ### Section 1: Combinatorial collapse, recurrence, and Morley's square congruence -/

section Combinatorics
open Finset Nat

private abbrev R2 (p : ℕ) := ZMod (p ^ 2)

private def red (p : ℕ) : R2 p →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by decide)) _

private lemma p_sq_zero (p : ℕ) : (p : R2 p) ^ 2 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

private lemma unit_red {p : ℕ} (hp : p.Prime) {x : R2 p} (hx : red p x ≠ 0) : IsUnit x := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide)]
  intro hd
  apply hx
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [map_natCast, ZMod.natCast_eq_zero_iff]
  exact hd

private lemma unit_small {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 0 < n) (hnp : n < p) :
    IsUnit (n : R2 p) := by
  apply unit_red hp
  rw [map_natCast]
  intro hz
  exact Nat.not_dvd_of_pos_of_lt hn hnp ((ZMod.natCast_eq_zero_iff n p).mp hz)

private lemma convolution (m k N : ℕ) :
    ∑ i ∈ range (N + 1), (i + m).choose m * (N - i + k).choose k =
      (N + m + k + 1).choose (m + k + 1) := by
  induction k generalizing N with
  | zero => simpa using Nat.sum_range_add_choose N m
  | succ k ih =>
    induction N with
    | zero => simp [Nat.add_assoc]
    | succ N jh =>
      rw [sum_range_succ]
      have eq (i : ℕ) (hi : i ∈ range (N + 1)) :
          (N + 1 - i + (k + 1)).choose (k + 1) =
            (N - i + (k + 1)).choose (k + 1) + (N + 1 - i + k).choose k := by
        rw [show N + 1 - i + (k + 1) = (N + 1 - i + k) + 1 by omega,
          Nat.choose_succ_succ', add_comm]
        congr 2
        simp only [mem_range] at hi
        omega
      rw [sum_congr rfl (show ∀ i ∈ range (N + 1),
          (i + m).choose m * (N + 1 - i + (k + 1)).choose (k + 1) =
            (i + m).choose m * (N - i + (k + 1)).choose (k + 1) +
            (i + m).choose m * (N + 1 - i + k).choose k from fun i hi => by rw [eq i hi, mul_add])]
      simp only [Nat.sub_self, Nat.zero_add, Nat.choose_self, mul_one]
      rw [sum_add_distrib, jh, add_assoc]
      have hh := ih (N + 1)
      rw [sum_range_succ] at hh
      simp only [Nat.sub_self, Nat.zero_add, Nat.choose_self, mul_one] at hh
      rw [hh]
      rw [show N + 1 + m + (k + 1) + 1 = (N + m + (k + 1) + 1) + 1 by omega,
        show m + (k + 1) + 1 = (m + k + 1) + 1 by omega, Nat.choose_succ_succ', add_comm]
      congr 1
      · congr 1; omega

private lemma choose_mul_factorial_prod {R : Type*} [CommRing R] {n m : ℕ} (hm : m ≤ n) :
    (m.factorial : R) * (n.choose m : R) = ∏ i ∈ range m, ((n : R) - (i : R)) := by
  rw [← Nat.cast_mul, ← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range,
    Nat.cast_prod]
  exact prod_congr rfl fun i hi => Nat.cast_sub (by have := mem_range.mp hi; omega)

private lemma choose_reflect (p m n : ℕ) (hp : p.Prime) (hm : m < p)
    (hn : n ∈ Ico m p) (he : Even m) :
    (n.choose m : ZMod p) = ((p + m - 1 - n).choose m : ZMod p) := by
  have hn' := mem_Ico.mp hn
  have hunit : IsUnit (m.factorial : ZMod p) := by
    have h := ZMod.coe_mul_inv_eq_one m.factorial (hp.coprime_factorial_of_lt hm).symm
    exact ⟨⟨_, _, h, by rw [mul_comm]; exact h⟩, rfl⟩
  apply hunit.mul_left_cancel
  rw [choose_mul_factorial_prod hn'.1, choose_mul_factorial_prod (by omega)]
  rw [← prod_range_reflect (fun i => ((n : ZMod p) - (i : ZMod p))) m]
  have hsign : (∏ i ∈ range m, -((n : ZMod p) - (↑(m - 1 - i) : ZMod p))) =
      ∏ i ∈ range m, ((n : ZMod p) - (↑(m - 1 - i) : ZMod p)) := by
    rw [prod_neg, card_range, he.neg_one_pow, one_mul]
  rw [← hsign]
  apply prod_congr rfl
  intro i hi
  have hi' := mem_range.mp hi
  push_cast [show i ≤ m - 1 by omega, show 1 ≤ m by omega,
    show n ≤ p + m - 1 by omega, show 1 ≤ p + m by omega]
  rw [ZMod.natCast_self]
  ring

private lemma choose_square_sum (p m : ℕ) (hp : p.Prime) (hp2 : 2 < p) (hm : m < p)
    (he : Even m) :
    (∑ n ∈ range p, (n.choose m : R2 p) ^ 2) = ((p + m).choose (2 * m + 1) : ℕ) := by
  let b (n : ℕ) : R2 p := n.choose m
  let r (n : ℕ) := p + m - 1 - n
  have hr : ∀ n ∈ Ico m p, r n ∈ Ico m p := by
    intro n hn; simp only [mem_Ico, r] at *; omega
  have hr2 : ∀ n ∈ Ico m p, r (r n) = n := by
    intro n hn; simp only [mem_Ico, r] at *; omega
  have hsq (n : ℕ) (hn : n ∈ Ico m p) : (b n - b (r n)) ^ 2 = 0 := by
    have h := choose_reflect p m n hp hm hn he
    have hdvd : (p : ℤ) ∣ (n.choose m : ℤ) - ((r n).choose m : ℤ) := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      exact sub_eq_zero.mpr h
    obtain ⟨d, hd⟩ := hdvd
    have hx : b n - b (r n) = (p : R2 p) * (d : R2 p) := by
      dsimp [b]
      simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] using
        congrArg (fun x : ℤ => (x : R2 p)) hd
    rw [hx, mul_pow, p_sq_zero, zero_mul]
  have hsum : (∑ n ∈ Ico m p, b (r n) ^ 2) = ∑ n ∈ Ico m p, b n ^ 2 :=
    sum_nbij' r r hr hr hr2 hr2 (fun _ _ => rfl)
  have hb : (∑ n ∈ range p, b n ^ 2) = ∑ n ∈ Ico m p, b n ^ 2 := by
    symm
    apply sum_subset
    · intro n hn; exact mem_range.mpr (mem_Ico.mp hn).2
    · intro n hn hnm
      have h : n < m := by simpa [mem_Ico, mem_range.mp hn] using hnm
      simp [b, Nat.choose_eq_zero_of_lt h]
  have hc : (∑ n ∈ Ico m p, b n * b (r n)) = ((p + m).choose (2 * m + 1) : R2 p) := by
    rw [sum_Ico_eq_sum_range]
    have hlen : p - m = (p - m - 1) + 1 := by omega
    rw [hlen]
    have eq (i : ℕ) (hi : i ∈ range (p - m - 1 + 1)) : r (m + i) = (p - m - 1) - i + m := by
      simp only [r, mem_range] at *; omega
    rw [sum_congr rfl (fun i hi => show b (m + i) * b (r (m + i)) =
      ((m + i).choose m * (p - m - 1 - i + m).choose m : ℕ) by simp [b, eq i hi]), ← Nat.cast_sum]
    rw [show (∑ x ∈ range (p - m - 1 + 1), (m + x).choose m *
          (p - m - 1 - x + m).choose m) =
          ((p - m - 1) + m + m + 1).choose (m + m + 1) from by
      simpa only [add_comm m] using convolution m m (p - m - 1)]
    congr 2 <;> omega
  change (∑ n ∈ range p, b n ^ 2) = _
  rw [hb, ← hc]
  have ht := sum_congr rfl hsq
  simp only [sum_const_zero] at ht
  have exp (n : ℕ) : (b n - b (r n)) ^ 2 = b n ^ 2 + b (r n) ^ 2 - 2 * (b n * b (r n)) := by ring
  simp_rw [exp, sum_sub_distrib, sum_add_distrib, ← mul_sum, hsum, ← two_mul] at ht
  apply (unit_small hp (by decide : 0 < 2) hp2).mul_left_cancel
  exact sub_eq_zero.mp ht

private lemma collapse (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    (∑ n ∈ range p, (OeisA179524.a n : R2 p)) =
      ∑ k ∈ range ((p - 1) / 2 + 1), (-4 : R2 p) ^ k *
        ((2 * k).choose k : R2 p) ^ 2 * ((p + 2 * k).choose (4 * k + 1) : ℕ) := by
  let h := (p - 1) / 2 + 1
  have ha (n : ℕ) (hn : n < p) :
      (OeisA179524.a n : R2 p) =
        ∑ k ∈ range h, (-4 : R2 p) ^ k * ((2 * k).choose k : R2 p) ^ 2 *
          (n.choose (2 * k) : R2 p) ^ 2 := by
    simp only [OeisA179524.a, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_ofNat, Int.cast_natCast]
    have he (k : ℕ) :
        (-4 : R2 p) ^ k * (n.choose k : R2 p) ^ 2 * ((n - k).choose k : R2 p) ^ 2 =
          (-4 : R2 p) ^ k * ((2 * k).choose k : R2 p) ^ 2 * (n.choose (2 * k) : R2 p) ^ 2 := by
      have hx := Nat.choose_mul (n := n) (k := 2 * k) (s := k) (by omega)
      rw [show 2 * k - k = k by omega] at hx
      have hx' := congrArg (fun x : ℕ => (x : R2 p)) hx
      simp only [Nat.cast_mul] at hx'
      linear_combination ((-4 : R2 p) ^ k * ((n.choose (2 * k) : R2 p) * ((2 * k).choose k : R2 p) +
        (n.choose k : R2 p) * ((n - k).choose k : R2 p))) * (-hx')
    simp_rw [he]
    rcases le_total (n + 1) h with hh | hh
    · apply sum_subset (range_mono hh)
      intro k hk hk'
      have hnk : n < 2 * k := by simp only [mem_range, not_lt] at hk'; omega
      simp [Nat.choose_eq_zero_of_lt hnk]
    · symm
      apply sum_subset (range_mono hh)
      intro k hk hk'
      have hnk : n < 2 * k := by dsimp [h] at hk'; simp only [mem_range, not_lt] at hk'; omega
      simp [Nat.choose_eq_zero_of_lt hnk]
  rw [sum_congr rfl (fun n hn => ha n (mem_range.mp hn)), sum_comm]
  apply sum_congr rfl
  intro k hk
  change k ∈ range h at hk
  rw [← mul_sum, choose_square_sum p (2 * k) hp hp2 (by
    dsimp [h] at hk; simp only [mem_range] at hk; omega) ⟨k, by omega⟩]
  congr 3
  omega

/-- The coefficient $c_j = \binom{2(h-j)}{h-j}^2 \binom{p+2(h-j)}{2j}$ of $\widetilde{A}_p(z)$
(defined to be $0$ for $j > h$). -/
private def atCoeff (p h j : ℕ) : R2 p :=
  if j ≤ h then ((2 * (h - j)).choose (h - j) : R2 p) ^ 2 * ((p + 2 * (h - j)).choose (2 * j) : ℕ)
  else 0

private lemma collapse_eq_atCoeff_sum {p h : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hh : p = 2 * h + 1) :
    (∑ n ∈ range p, (OeisA179524.a n : R2 p)) =
      (-4 : R2 p) ^ h * ∑ j ∈ range (h + 1), atCoeff p h j * ((-4 : R2 p)⁻¹) ^ j := by
  rw [collapse p hp hp2, show (p - 1) / 2 = h by omega]
  rw [← sum_range_reflect (fun k => (-4 : R2 p) ^ k * ((2 * k).choose k : R2 p) ^ 2 *
    ((p + 2 * k).choose (4 * k + 1) : ℕ)) (h + 1), mul_sum]
  have hu4 : IsUnit (-4 : R2 p) := by
    have h2 : IsUnit (2 : R2 p) := unit_small hp (by decide : 0 < 2) hp2
    have h4 : IsUnit (4 : R2 p) := by simpa [show (4 : R2 p) = 2 * 2 by ring] using h2.mul h2
    exact h4.neg
  have h4inv : (-4 : R2 p) * (-4 : R2 p)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu4
  apply sum_congr rfl
  intro j hj
  have hjh : j ≤ h := by simp only [mem_range] at hj; omega
  have hsub : h + 1 - 1 - j = h - j := by omega
  rw [hsub, atCoeff, if_pos hjh]
  have hch : (p + 2 * (h - j)).choose (4 * (h - j) + 1) = (p + 2 * (h - j)).choose (2 * j) := by
    rw [← Nat.choose_symm (by omega : 4 * (h - j) + 1 ≤ p + 2 * (h - j))]
    congr 1
    omega
  rw [hch]
  have hpow : (-4 : R2 p) ^ h * ((-4 : R2 p)⁻¹) ^ j = (-4 : R2 p) ^ (h - j) := by
    calc
      (-4 : R2 p) ^ h * ((-4 : R2 p)⁻¹) ^ j
          = (-4 : R2 p) ^ ((h - j) + j) * ((-4 : R2 p)⁻¹) ^ j := by rw [Nat.sub_add_cancel hjh]
      _ = (-4 : R2 p) ^ (h - j) * ((-4 : R2 p) * (-4 : R2 p)⁻¹) ^ j := by
          rw [pow_add, mul_assoc, ← mul_pow]
      _ = (-4 : R2 p) ^ (h - j) := by rw [h4inv, one_pow, mul_one]
  linear_combination ((2 * (h - j)).choose (h - j) : R2 p) ^ 2 *
    ((p + 2 * (h - j)).choose (2 * j) : R2 p) * (-hpow)

private lemma choose_move (u w : ℕ) :
    (u + w + 2).choose (u + 2) * ((u + 1) * (u + 2) * (u + w + 4) * (u + w + 3)) =
      (u + w + 4).choose u * ((w + 4) * (w + 3) * (w + 2) * (w + 1)) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show u + 2 ≤ u + w + 2 by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (show u ≤ u + w + 4 by omega)
  rw [show u + w + 2 - (u + 2) = w by omega, Nat.factorial_succ, Nat.factorial_succ u] at h1
  rw [show u + w + 4 - u = w + 4 by omega, Nat.factorial_succ (w + 3), Nat.factorial_succ (w + 2),
    Nat.factorial_succ (w + 1), Nat.factorial_succ w,
    Nat.factorial_succ (u + w + 3), Nat.factorial_succ (u + w + 2), ← h1] at h2
  have he : (u + w + 2).choose (u + 2) * ((u + 1) * (u + 2) * (u + w + 4) * (u + w + 3)) *
      (u.factorial * w.factorial) =
      (u + w + 4).choose u * ((w + 4) * (w + 3) * (w + 2) * (w + 1)) * (u.factorial * w.factorial) := by
    convert h2.symm using 1 <;> ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)) he

private def halfR (p : ℕ) : R2 p := (2 : R2 p)⁻¹

private lemma two_halfR {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) : 2 * halfR p = 1 :=
  ZMod.mul_inv_of_unit _ (unit_small hp (by decide : 0 < 2) hp2)

/-- Third-order recurrence for `atCoeff p h j` modulo `p ^ 2`, valid for all `j + 1 < p`. -/
private lemma atCoeff_recurrence {p h : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hh : p = 2 * h + 1)
    (j : ℕ) (_hj : j + 1 < p) :
    ((j : R2 p) + 1) * ((j : R2 p) + 1 - (p : R2 p) * halfR p) * ((j : R2 p) + 1 - (p : R2 p)) *
        atCoeff p h (j + 1) =
      ((j : R2 p) + (1 - 2 * (p : R2 p)) * halfR p ^ 2) *
        ((j : R2 p) + (3 - 2 * (p : R2 p)) * halfR p ^ 2) *
        ((j : R2 p) - (h : R2 p)) * atCoeff p h j := by
  have hi := two_halfR hp hp2
  have hP : (p : R2 p) = 2 * (h : R2 p) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      congrArg (fun n : ℕ => (n : R2 p)) hh
  rcases lt_trichotomy j h with hjh | rfl | hjh
  · rw [atCoeff, if_pos (by omega : j + 1 ≤ h), atCoeff, if_pos (by omega : j ≤ h)]
    let J : R2 p := j
    let P : R2 p := p
    let v : R2 p := 2 * J + 1
    let w : R2 p := v + 1
    let A : R2 p := (2 * (h - j - 1)).choose (h - j - 1)
    let B : R2 p := (2 * (h - j)).choose (h - j)
    let D : R2 p := (p + 2 * (h - j - 1)).choose (2 * (j + 1))
    let E : R2 p := (p + 2 * (h - j)).choose (2 * j)
    have hC : 4 * (P - w) * A = (P - v) * B := by
      have he := Nat.succ_mul_centralBinom_succ (h - j - 1)
      rw [show h - j - 1 + 1 = h - j by omega] at he
      have he' := congrArg (fun n : ℕ => (n : R2 p)) he
      simp only [Nat.centralBinom, Nat.cast_mul, Nat.cast_add, Nat.cast_sub (by omega : j ≤ h),
        Nat.cast_sub (by omega : 1 ≤ h - j), Nat.cast_one, Nat.cast_ofNat] at he'
      change ((h : R2 p) - J) * B = 2 * (2 * ((h : R2 p) - J - 1) + 1) * A at he'
      dsimp [w, v]
      linear_combination -2 * he' + ((4 * A) - B) * hP
    let z := p + 2 * (h - j) - 2 * j - 4
    have hD : D * (v * w * (2 * P - v) * (2 * P - w)) =
        E * ((2 * P - 4 * J - 1) * (2 * P - 4 * J - 3) * 4 * (P - v) * (P - w)) := by
      have he := choose_move (2 * j) z
      have hz : 2 * j + z + 2 = p + 2 * (h - j - 1) := by dsimp [z]; omega
      have hz' : 2 * j + z + 4 = p + 2 * (h - j) := by dsimp [z]; omega
      have hz'' : 2 * j + z + 3 = p + 2 * (h - j) - 1 := by dsimp [z]; omega
      rw [hz, hz', hz''] at he
      have he' := congrArg (fun n : ℕ => (n : R2 p)) he
      have hzcast : (z : R2 p) = P + 2 * ((h : R2 p) - J) - 2 * J - 4 := by
        dsimp [z, P, J]
        push_cast [show 2 * j ≤ p + 2 * (h - j) by omega, show 4 ≤ p + 2 * (h - j) - 2 * j by omega,
          show j ≤ h by omega]
        ring
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
        show 2 * j + 2 = 2 * (j + 1) by omega, Nat.cast_sub (by omega : 1 ≤ p + 2 * (h - j)),
        Nat.cast_sub (by omega : j ≤ h), hzcast] at he'
      change D * ((2 * J + 1) * (2 * (J + 1)) * (P + 2 * ((h : R2 p) - J)) *
          (P + 2 * ((h : R2 p) - J) - 1)) =
        E * ((P + 2 * ((h : R2 p) - J) - 2 * J - 4 + 4) *
          (P + 2 * ((h : R2 p) - J) - 2 * J - 4 + 3) *
          (P + 2 * ((h : R2 p) - J) - 2 * J - 4 + 2) *
          (P + 2 * ((h : R2 p) - J) - 2 * J - 4 + 1)) at he'
      dsimp [w, v]
      have hr (X : R2 p) : 2 * ((h : R2 p) - X) = P - 1 - 2 * X := by linear_combination -hP
      rw [hr J] at he'
      linear_combination he'
    have : Fact p.Prime := ⟨hp⟩
    have hv : IsUnit v := by
      dsimp [v, J]
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
        unit_small hp (by omega : 0 < 2 * j + 1) (by omega : 2 * j + 1 < p)
    have hredP : red p P = 0 := (map_natCast (red p) p).trans (ZMod.natCast_self p)
    have hu : IsUnit (2 * P - v) := by
      apply unit_red hp
      rw [map_sub, map_mul, hredP, mul_zero, zero_sub, neg_ne_zero]
      exact (hv.map (red p)).ne_zero
    have hw : IsUnit (P - w) := by
      apply unit_red hp
      have hww : IsUnit w := by
        dsimp [w, v, J]
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
          unit_small hp (by omega : 0 < 2 * j + 1 + 1) (by omega : 2 * j + 1 + 1 < p)
      rw [map_sub, hredP, zero_sub, neg_ne_zero]
      exact (hww.map (red p)).ne_zero
    have hpv : (P - v) ^ 2 = -(v * (2 * P - v)) := by
      have hz : P ^ 2 = 0 := p_sq_zero p
      linear_combination hz
    have hrec : 4 * (P - w) * w * (2 * P - w) * (A ^ 2 * D) =
        (v - P) * (2 * P - 4 * J - 1) * (2 * P - 4 * J - 3) * (B ^ 2 * E) := by
      apply (hv.mul hu).mul_left_cancel
      apply hw.mul_left_cancel
      have hC2 : (4 * (P - w) * A) ^ 2 = ((P - v) * B) ^ 2 := congrArg (fun x : R2 p => x ^ 2) hC
      linear_combination (4 * A ^ 2 * (P - w) ^ 2) * hD +
        (E * (2 * P - 4 * J - 1) * (2 * P - 4 * J - 3) * (P - v) * (P - w)) * (hC2 + B ^ 2 * hpv)
    have k1 : 2 * (J + 1) = w := by dsimp [w, v]; ring
    have k2 : 2 * (J + 1 - P * halfR p) = w - P := by linear_combination k1 - P * hi
    have k3 : 2 * (J + 1 - P) = w - 2 * P := by linear_combination k1
    have k4 : 4 * (J + (1 - 2 * P) * halfR p ^ 2) = 4 * J + 1 - 2 * P := by
      linear_combination (1 - 2 * P) * (2 * halfR p + 1) * hi
    have k5 : 4 * (J + (3 - 2 * P) * halfR p ^ 2) = 4 * J + 3 - 2 * P := by
      linear_combination (3 - 2 * P) * (2 * halfR p + 1) * hi
    have k6 : 2 * (J - (h : R2 p)) = v - P := by dsimp [v]; linear_combination hP
    have hsub1 : h - (j + 1) = h - j - 1 := by omega
    rw [hsub1]
    change (J + 1) * (J + 1 - P * halfR p) * (J + 1 - P) * (A ^ 2 * D) =
      (J + (1 - 2 * P) * halfR p ^ 2) * (J + (3 - 2 * P) * halfR p ^ 2) *
        (J - (h : R2 p)) * (B ^ 2 * E)
    apply ((unit_small hp (by decide : 0 < 2) hp2).pow 5).mul_left_cancel
    calc
      _ = 4 * (2 * (J + 1)) * (2 * (J + 1 - P * halfR p)) * (2 * (J + 1 - P)) * (A ^ 2 * D) := by ring
      _ = (4 * (J + (1 - 2 * P) * halfR p ^ 2)) * (4 * (J + (3 - 2 * P) * halfR p ^ 2)) *
          (2 * (J - (h : R2 p))) * (B ^ 2 * E) := by
        rw [k1, k2, k3, k4, k5, k6]
        linear_combination hrec
      _ = _ := by ring
  · rw [atCoeff, if_neg (by omega : ¬ j + 1 ≤ j)]
    ring
  · rw [atCoeff, if_neg (by omega : ¬ j + 1 ≤ h), atCoeff, if_neg (by omega : ¬ j ≤ h)]
    ring

/-- Morley's congruence squared: $\binom{p-1}{(p-1)/2}^2 \equiv 16^{p-1} \pmod{p^2}$ for any odd
prime $p$. Proved elementarily from $2^p - 2 = \sum_{k=1}^{p-1} \binom{p}{k}$. -/
private lemma morley_sq {p h : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hh : p = 2 * h + 1) :
    ((2 * h).choose h : R2 p) ^ 2 = (16 : R2 p) ^ (p - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : ∀ k ∈ Ico 1 p,
      ((p.choose k : R2 p)) = (p : R2 p) * (-1 : R2 p) ^ (k - 1) * (k : R2 p)⁻¹ := by
    intro k hk
    have hk' := mem_Ico.mp hk
    have huk : IsUnit (k : R2 p) := unit_small hp hk'.1 hk'.2
    have hmul : k * p.choose k = p * (p - 1).choose (k - 1) := by
      have := Nat.add_one_mul_choose_eq (p - 1) (k - 1)
      rw [show p - 1 + 1 = p by omega, show k - 1 + 1 = k by omega] at this
      linarith
    have hch : ((p - 1).choose (k - 1) : ZMod p) = (-1 : ZMod p) ^ (k - 1) := by
      have hfac : IsUnit ((k - 1).factorial : ZMod p) := by
        have h := ZMod.coe_mul_inv_eq_one (k - 1).factorial
          (hp.coprime_factorial_of_lt (by omega)).symm
        exact ⟨⟨_, _, h, by rw [mul_comm]; exact h⟩, rfl⟩
      apply hfac.mul_left_cancel
      rw [choose_mul_factorial_prod (by omega : k - 1 ≤ p - 1)]
      rw [Nat.factorial_eq_prod_range_add_one (k - 1), Nat.cast_prod]
      have hneg : (∏ x ∈ range (k - 1), ((x + 1 : ℕ) : ZMod p)) * (-1 : ZMod p) ^ (k - 1) =
          ∏ x ∈ range (k - 1), -((x : ZMod p) + 1) := by
        rw [prod_neg, card_range, mul_comm]
        congr 1
        exact prod_congr rfl fun i _ => by push_cast; ring
      rw [hneg]
      apply prod_congr rfl
      intro i hi
      push_cast [show 1 ≤ p by omega]
      rw [ZMod.natCast_self]
      ring
    have hdvd : (p : ℤ) ∣ ((p - 1).choose (k - 1) : ℤ) - (-1 : ℤ) ^ (k - 1) := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      exact sub_eq_zero.mpr hch
    obtain ⟨d, hd⟩ := hdvd
    have hch2 : (p : R2 p) * ((p - 1).choose (k - 1) : R2 p) =
        (p : R2 p) * (-1 : R2 p) ^ (k - 1) := by
      have hcast := congrArg (fun x : ℤ => (x : R2 p)) hd
      push_cast at hcast
      linear_combination (p : R2 p) * hcast + (d : R2 p) * p_sq_zero p
    apply huk.mul_left_cancel
    rw [← mul_assoc, mul_comm (k : R2 p) ((p : R2 p) * (-1 : R2 p) ^ (k - 1)), mul_assoc,
      ZMod.mul_inv_of_unit _ huk, mul_one, ← hch2]
    have hmul' := congrArg (fun n : ℕ => (n : R2 p)) hmul
    simpa only [Nat.cast_mul] using hmul'
  have h2p : (2 : R2 p) ^ p - 2 =
      (p : R2 p) * ∑ k ∈ Ico 1 p, (-1 : R2 p) ^ (k - 1) * (k : R2 p)⁻¹ := by
    have hbin : (2 : ℕ) ^ p = ∑ k ∈ range (p + 1), p.choose k := by
      simpa using (Nat.sum_range_choose p).symm
    have hsplit : ∑ k ∈ range (p + 1), p.choose k = 2 + ∑ k ∈ Ico 1 p, p.choose k := by
      rw [sum_range_succ, Nat.choose_self, sum_range_eq_add_Ico _ (by omega : 0 < p),
        Nat.choose_zero_right]
      ring
    have hcast : (2 : R2 p) ^ p - 2 = ∑ k ∈ Ico 1 p, (p.choose k : R2 p) := by
      have := congrArg (fun n : ℕ => (n : R2 p)) (hbin.trans hsplit)
      push_cast at this
      linear_combination this
    rw [hcast, sum_congr rfl h1, mul_sum]
    exact sum_congr rfl fun k _ => by ring
  -- Harmonic sum identity in ZMod p: ∑_{k=1}^{p-1} (-1)^{k-1}/k = - ∑_{m=1}^h 1/m
  have hharm_zero : (∑ k ∈ Ico 1 p, (k : ZMod p)⁻¹) = 0 := by
    have hpair : (∑ k ∈ Ico 1 p, (k : ZMod p)⁻¹) = ∑ k ∈ Ico 1 p, ((p - k : ℕ) : ZMod p)⁻¹ := by
      refine sum_nbij' (fun k => p - k) (fun k => p - k) ?_ ?_ ?_ ?_ ?_
      · intro k hk; simp only [mem_Ico] at *; omega
      · intro k hk; simp only [mem_Ico] at *; omega
      · intro k hk; simp only [mem_Ico] at *; omega
      · intro k hk; simp only [mem_Ico] at *; omega
      · intro k hk; simp only [mem_Ico] at hk; congr 2; omega
    have hneg : ∀ k ∈ Ico 1 p, ((p - k : ℕ) : ZMod p)⁻¹ = -(k : ZMod p)⁻¹ := by
      intro k hk
      have hk' := mem_Ico.mp hk
      rw [Nat.cast_sub (by omega : k ≤ p), ZMod.natCast_self, zero_sub, inv_neg]
    rw [sum_congr rfl hneg, sum_neg_distrib] at hpair
    have h2u : (2 : ZMod p) ≠ 0 := by
      intro h0
      exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hp2 ((ZMod.natCast_eq_zero_iff 2 p).mp h0)
    have h2s : (2 : ZMod p) * ∑ k ∈ Ico 1 p, (k : ZMod p)⁻¹ = 0 := by linear_combination hpair
    exact (mul_eq_zero.mp h2s).resolve_left h2u
  have hharm_alt : (∑ k ∈ Ico 1 p, (-1 : ZMod p) ^ (k - 1) * (k : ZMod p)⁻¹) =
      -∑ m ∈ Ico 1 (h + 1), (m : ZMod p)⁻¹ := by
    have hsplit : ∑ k ∈ Ico 1 p, (-1 : ZMod p) ^ (k - 1) * (k : ZMod p)⁻¹ =
        (∑ k ∈ Ico 1 p, (k : ZMod p)⁻¹) -
          2 * ∑ m ∈ Ico 1 (h + 1), ((2 * m : ℕ) : ZMod p)⁻¹ := by
      have hbi : ∑ k ∈ Ico 1 p, ((-1 : ZMod p) ^ (k - 1) - 1) * (k : ZMod p)⁻¹ =
          -2 * ∑ m ∈ Ico 1 (h + 1), ((2 * m : ℕ) : ZMod p)⁻¹ := by
        rw [mul_sum]
        have hsub : (Ico 1 (h + 1)).image (2 * ·) ⊆ Ico 1 p := by
          intro x hx
          rcases mem_image.mp hx with ⟨m, hm, rfl⟩
          simp only [mem_Ico] at hm ⊢; omega
        rw [← sum_subset hsub]
        · rw [sum_image (fun a _ b _ hab => by omega)]
          apply sum_congr rfl
          intro m hm
          have hm' := mem_Ico.mp hm
          have hpow : (-1 : ZMod p) ^ (2 * m - 1) = -1 := by
            have hodd : Odd (2 * m - 1) := ⟨m - 1, by omega⟩
            exact hodd.neg_one_pow
          rw [hpow]; ring
        · intro k hk hnot
          simp only [mem_Ico] at hk
          rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
          · exfalso; apply hnot
            exact mem_image.mpr ⟨m, mem_Ico.mpr (by omega), by omega⟩
          · have hpow : (-1 : ZMod p) ^ (2 * m + 1 - 1) = 1 := by
              rw [show 2 * m + 1 - 1 = 2 * m by omega, pow_mul]; norm_num
            rw [hpow]; ring
      have hlin : ∑ k ∈ Ico 1 p, ((-1 : ZMod p) ^ (k - 1) - 1) * (k : ZMod p)⁻¹ =
          (∑ k ∈ Ico 1 p, (-1 : ZMod p) ^ (k - 1) * (k : ZMod p)⁻¹) -
            ∑ k ∈ Ico 1 p, (k : ZMod p)⁻¹ := by
        rw [← sum_sub_distrib]
        exact sum_congr rfl fun k _ => by ring
      linear_combination hbi - hlin
    rw [hsplit, hharm_zero, zero_sub]
    rw [mul_sum]
    have h2u : (2 : ZMod p) ≠ 0 := by
      intro h0
      exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hp2 ((ZMod.natCast_eq_zero_iff 2 p).mp h0)
    congr 1
    apply sum_congr rfl
    intro m _
    push_cast
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ h2u, one_mul]
  -- Lift harmonic congruence to `p * (...)` in `R2 p`
  have hlift : (p : R2 p) * ∑ k ∈ Ico 1 p, (-1 : R2 p) ^ (k - 1) * (k : R2 p)⁻¹ =
      -(p : R2 p) * ∑ m ∈ Ico 1 (h + 1), (m : R2 p)⁻¹ := by
    have hred_eq : red p ((∑ k ∈ Ico 1 p, (-1 : R2 p) ^ (k - 1) * (k : R2 p)⁻¹) +
        ∑ m ∈ Ico 1 (h + 1), (m : R2 p)⁻¹) = 0 := by
      rw [map_add, map_sum, map_sum]
      have hinv : ∀ n : ℕ, 0 < n → n < p → red p ((n : R2 p)⁻¹) = (n : ZMod p)⁻¹ := by
        intro n hn hnp
        have hun : IsUnit (n : R2 p) := unit_small hp hn hnp
        have hnz : (n : ZMod p) ≠ 0 := by
          intro h0; exact Nat.not_dvd_of_pos_of_lt hn hnp ((ZMod.natCast_eq_zero_iff n p).mp h0)
        apply mul_left_cancel₀ hnz
        rw [mul_inv_cancel₀ hnz, ← map_natCast (red p), ← map_mul,
          ZMod.mul_inv_of_unit _ hun, map_one]
      have s1 : ∑ k ∈ Ico 1 p, red p ((-1 : R2 p) ^ (k - 1) * (k : R2 p)⁻¹) =
          ∑ k ∈ Ico 1 p, (-1 : ZMod p) ^ (k - 1) * (k : ZMod p)⁻¹ := by
        apply sum_congr rfl
        intro k hk
        have hk' := mem_Ico.mp hk
        rw [map_mul, map_pow, map_neg, map_one, hinv k hk'.1 hk'.2]
      have s2 : ∑ m ∈ Ico 1 (h + 1), red p ((m : R2 p)⁻¹) =
          ∑ m ∈ Ico 1 (h + 1), (m : ZMod p)⁻¹ := by
        apply sum_congr rfl
        intro m hm
        have hm' := mem_Ico.mp hm
        exact hinv m hm'.1 (by omega)
      rw [s1, s2, hharm_alt, neg_add_cancel]
    have : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
    set S := (∑ k ∈ Ico 1 p, (-1 : R2 p) ^ (k - 1) * (k : R2 p)⁻¹) +
        ∑ m ∈ Ico 1 (h + 1), (m : R2 p)⁻¹
    have hdvd : p ∣ S.val := by
      rw [← ZMod.natCast_eq_zero_iff]
      conv_lhs => rw [← map_natCast (red p), ZMod.natCast_zmod_val]
      exact hred_eq
    obtain ⟨d, hd⟩ := hdvd
    have hS : S = (p : R2 p) * (d : R2 p) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val S, hd, Nat.cast_mul]
    have hpS : (p : R2 p) * S = 0 := by rw [hS, ← mul_assoc, ← sq, p_sq_zero, zero_mul]
    linear_combination hpS
  -- Compute `((2 * h).choose h : R2 p)` mod `p^2`
  have hcb : ((2 * h).choose h : R2 p) =
      (-1 : R2 p) ^ h * (1 - (p : R2 p) * ∑ m ∈ Ico 1 (h + 1), (m : R2 p)⁻¹) := by
    have hfac : IsUnit (h.factorial : R2 p) := by
      have hcop : Nat.Coprime h.factorial (p ^ 2) :=
        (hp.coprime_factorial_of_lt (by omega : h < p)).symm.pow_right 2
      have h := ZMod.coe_mul_inv_eq_one h.factorial hcop
      exact ⟨⟨_, _, h, by rw [mul_comm]; exact h⟩, rfl⟩
    apply hfac.mul_left_cancel
    rw [choose_mul_factorial_prod (by omega : h ≤ 2 * h)]
    have hprod_id : ∏ i ∈ range h, ((2 * h : R2 p) - (i : R2 p)) =
        ∏ m ∈ Ico 1 (h + 1), ((p : R2 p) - (m : R2 p)) := by
      refine prod_nbij' (fun i => i + 1) (fun m => m - 1) ?_ ?_ ?_ ?_ ?_
      · intro i hi; simp only [mem_range, mem_Ico] at *; omega
      · intro m hm; simp only [mem_range, mem_Ico] at *; omega
      · intro i _; omega
      · intro m hm; simp only [mem_Ico] at hm; omega
      · intro i _
        have hP : (p : R2 p) = (2 * h : R2 p) + 1 := by
          simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
            congrArg (fun n : ℕ => (n : R2 p)) hh
        push_cast
        linear_combination -hP
    rw [show ((2 * h : ℕ) : R2 p) = (2 * h : R2 p) by push_cast; rfl, hprod_id]
    have hfac_prod : (h.factorial : R2 p) = ∏ m ∈ Ico 1 (h + 1), (m : R2 p) := by
      rw [Nat.factorial_eq_prod_range_add_one, Nat.cast_prod]
      refine prod_nbij' (fun i => i + 1) (fun m => m - 1) ?_ ?_ ?_ ?_ ?_
      · intro i hi; simp only [mem_range, mem_Ico] at *; omega
      · intro m hm; simp only [mem_range, mem_Ico] at *; omega
      · intro i _; omega
      · intro m hm; simp only [mem_Ico] at hm; omega
      · intro i _; push_cast; rfl
    have hlin_prod : ∀ s : Finset ℕ, (∀ m ∈ s, 0 < m ∧ m < p) →
        ∏ m ∈ s, ((p : R2 p) - (m : R2 p)) =
          (-1 : R2 p) ^ s.card * (∏ m ∈ s, (m : R2 p)) *
            (1 - (p : R2 p) * ∑ m ∈ s, (m : R2 p)⁻¹) := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro _; simp
      | insert a s ha ih =>
        intro hs
        have ha' := hs a (mem_insert_self a s)
        have hua : IsUnit (a : R2 p) := unit_small hp ha'.1 ha'.2
        have hainv : (a : R2 p) * (a : R2 p)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hua
        rw [prod_insert ha, prod_insert ha, sum_insert ha, card_insert_of_notMem ha,
          ih (fun m hm => hs m (mem_insert_of_mem hm))]
        have hstep : ((p : R2 p) - (a : R2 p)) * (1 - (p : R2 p) * ∑ m ∈ s, (m : R2 p)⁻¹) =
            -(a : R2 p) * (1 - (p : R2 p) * ((a : R2 p)⁻¹ + ∑ m ∈ s, (m : R2 p)⁻¹)) := by
          linear_combination -(p : R2 p) * hainv -
            (∑ m ∈ s, (m : R2 p)⁻¹) * p_sq_zero p
        calc
          ((p : R2 p) - (a : R2 p)) *
              ((-1 : R2 p) ^ s.card * (∏ m ∈ s, (m : R2 p)) *
                (1 - (p : R2 p) * ∑ m ∈ s, (m : R2 p)⁻¹))
            = (-1 : R2 p) ^ s.card * (∏ m ∈ s, (m : R2 p)) *
                (((p : R2 p) - (a : R2 p)) * (1 - (p : R2 p) * ∑ m ∈ s, (m : R2 p)⁻¹)) := by ring
          _ = (-1 : R2 p) ^ s.card * (∏ m ∈ s, (m : R2 p)) *
                (-(a : R2 p) * (1 - (p : R2 p) * ((a : R2 p)⁻¹ + ∑ m ∈ s, (m : R2 p)⁻¹))) := by
              rw [hstep]
          _ = (-1 : R2 p) ^ (s.card + 1) * ((a : R2 p) * ∏ m ∈ s, (m : R2 p)) *
                (1 - (p : R2 p) * ((a : R2 p)⁻¹ + ∑ m ∈ s, (m : R2 p)⁻¹)) := by
              rw [pow_succ (-1 : R2 p) s.card]; ring
    rw [hlin_prod (Ico 1 (h + 1)) (fun m hm => by simp only [mem_Ico] at hm; omega),
      Nat.card_Ico, show h + 1 - 1 = h by omega, ← hfac_prod]
    ring
  -- Finish: combine `hcb^2` with `h2p`, `hlift`, and Fermat's Little Theorem `(2^(p-1) - 1)^2 = 0`
  have hflt : ((2 : R2 p) ^ (p - 1) - 1) ^ 2 = 0 := by
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h0
      exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hp2 ((ZMod.natCast_eq_zero_iff 2 p).mp h0)
    have hf : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
    have hdvd : (p : ℤ) ∣ (2 : ℤ) ^ (p - 1) - 1 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      exact sub_eq_zero.mpr hf
    obtain ⟨d, hd⟩ := hdvd
    have hcast := congrArg (fun x : ℤ => (x : R2 p)) hd
    push_cast at hcast
    linear_combination ((2 : R2 p) ^ (p - 1) - 1 + (p : R2 p) * (d : R2 p)) * hcast +
      (d : R2 p) ^ 2 * p_sq_zero p
  have h16 : (16 : R2 p) ^ (p - 1) = 1 + 4 * ((2 : R2 p) ^ (p - 1) - 1) := by
    have h16eq : (16 : R2 p) ^ (p - 1) = ((2 : R2 p) ^ (p - 1)) ^ 4 := by
      rw [show (16 : R2 p) = 2 ^ 4 by norm_num, ← pow_mul, mul_comm, pow_mul]
    rw [h16eq]
    set t := (2 : R2 p) ^ (p - 1) - 1
    have ht : (2 : R2 p) ^ (p - 1) = 1 + t := by simp [t]
    rw [ht]
    linear_combination (6 + 4 * t + t ^ 2) * hflt
  have h2p_eq : (2 : R2 p) ^ p - 2 = 2 * ((2 : R2 p) ^ (p - 1) - 1) := by
    have hp1 : (2 : R2 p) ^ p = (2 : R2 p) ^ (p - 1) * 2 := by
      rw [← pow_succ (2 : R2 p) (p - 1), Nat.sub_add_cancel (by omega)]
    linear_combination hp1
  rw [hcb, mul_pow, ← pow_mul, mul_comm h 2, pow_mul, show (-1 : R2 p) ^ 2 = 1 by norm_num,
    one_pow, one_mul, h16]
  have hsq_exp : (1 - (p : R2 p) * ∑ m ∈ Ico 1 (h + 1), (m : R2 p)⁻¹) ^ 2 =
      1 - 2 * ((p : R2 p) * ∑ m ∈ Ico 1 (h + 1), (m : R2 p)⁻¹) := by
    linear_combination (∑ m ∈ Ico 1 (h + 1), (m : R2 p)⁻¹) ^ 2 * p_sq_zero p
  rw [hsq_exp]
  linear_combination -2 * h2p - 2 * hlift + 2 * h2p_eq

end Combinatorics

/- ### Section 2: Modular forms on Gamma0(2)+ and the structure theorem -/

section ModularGamma02
open UpperHalfPlane hiding I
open Complex Filter Function ModularForm ModularGroup CongruenceSubgroup EisensteinSeries
open Matrix.SpecialLinearGroup
open scoped Real Topology Manifold MatrixGroups ModularForm ArithmeticFunction.sigma

private abbrev Γ02 : Subgroup (GL (Fin 2) ℝ) :=
  (CongruenceSubgroup.Gamma0 2 : Subgroup (GL (Fin 2) ℝ))

private lemma neg_one_mem_Gamma02 : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 2 := by
  rw [CongruenceSubgroup.Gamma0_mem]
  decide

private lemma T_mem_Gamma02 : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 2 := by
  rw [CongruenceSubgroup.Gamma0_mem]
  decide

private lemma mapGL_apply (A : SL(2, ℤ)) (i j : Fin 2) :
    ((mapGL ℝ A : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = (A i j : ℝ) := rfl

private lemma one_mem_strictPeriods_Γ02 : (1 : ℝ) ∈ Γ02.strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T, T_mem_Gamma02, ?_⟩
  ext i j
  rw [mapGL_apply]
  fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom]

private def mul2 (τ : ℍ) : ℍ :=
  ⟨2 * (τ : ℂ), by simpa using mul_pos two_pos τ.im_pos⟩

@[simp]
private lemma coe_mul2 (τ : ℍ) : (mul2 τ : ℂ) = 2 * (τ : ℂ) := rfl

private lemma mdiff_comp_mul2 {f : ℍ → ℂ} (hf : MDiff f) : MDiff (fun τ : ℍ ↦ f (mul2 τ)) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf ⊢
  have h2 : DifferentiableOn ℂ (fun z : ℂ ↦ 2 * z) upperHalfPlaneSet := by fun_prop
  have hmaps : Set.MapsTo (fun z : ℂ ↦ 2 * z) upperHalfPlaneSet upperHalfPlaneSet := fun z hz => by
    change 0 < (2 * z).im
    have : 0 < z.im := hz
    simpa using mul_pos two_pos this
  refine (hf.comp h2 hmaps).congr fun z hz => ?_
  have hz2 : 0 < (2 * z).im := hmaps hz
  simp [Function.comp_apply, mul2, ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos hz2]

/-- Determinant-1 Fricke involution $W_2 = \begin{pmatrix} 0 & -1/\sqrt{2} \\ \sqrt{2} & 0 \end{pmatrix}$. -/
private noncomputable def W2 : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(0 : ℝ), -(Real.sqrt 2)⁻¹; Real.sqrt 2, 0]
    (by
      rw [Matrix.det_fin_two_of]
      have hsq : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr two_pos
      field_simp [hsq]
      norm_num)

private lemma W2_val : (W2 : Matrix (Fin 2) (Fin 2) ℝ) =
    !![(0 : ℝ), -(Real.sqrt 2)⁻¹; Real.sqrt 2, 0] := rfl

private lemma W2_det_val : W2.det.val = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, W2_val, Matrix.det_fin_two_of]
  have hsq : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr two_pos
  field_simp [hsq]
  ring

private lemma W2_val_det : (W2 : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply, W2_det_val]

private lemma W2_sq : W2 * W2 = -1 := by
  ext i j
  have hsq : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr two_pos
  fin_cases i <;> fin_cases j <;>
    simp [W2_val, Matrix.mul_apply, Fin.sum_univ_two, hsq]

private lemma W2_inv : W2⁻¹ = -W2 := by
  apply inv_eq_of_mul_eq_one_right
  rw [mul_neg, W2_sq, neg_neg]

private lemma denom_W2 (τ : ℍ) : denom W2 τ = (Real.sqrt 2 : ℂ) * (τ : ℂ) := by
  simp [denom, W2_val]

private lemma coe_W2_smul (τ : ℍ) : ((W2 • τ : ℍ) : ℂ) = -(2 * (τ : ℂ))⁻¹ := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (by rw [W2_det_val]; norm_num)]
  simp only [num, denom, W2_val, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.ofReal_zero, zero_mul, zero_add,
    Complex.ofReal_neg, Complex.ofReal_inv, add_zero]
  have hsq : (Real.sqrt 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr two_pos)
  have hsq2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  field_simp [hsq, hτ]
  linear_combination hsq2

private lemma mul2_W2_smul (τ : ℍ) : mul2 (W2 • τ) = ModularGroup.S • τ := by
  ext
  rw [coe_mul2, coe_W2_smul, UpperHalfPlane.modular_S_smul]
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  field_simp [hτ]

private lemma W2_smul_eq_S_mul2 (τ : ℍ) : W2 • τ = ModularGroup.S • mul2 τ := by
  ext
  rw [coe_W2_smul, UpperHalfPlane.modular_S_smul]
  simp [coe_mul2]

private lemma σ_W2 (z : ℂ) : UpperHalfPlane.σ W2 z = z := by
  simp [UpperHalfPlane.σ, W2_val_det]

private lemma slash_W2_even (N : ℤ) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[2 * N] W2) τ = f (W2 • τ) * (2 * (τ : ℂ) ^ 2) ^ (-N) := by
  rw [ModularForm.slash_apply, σ_W2, W2_det_val, abs_one, Complex.ofReal_one, one_zpow,
    mul_one, denom_W2]
  congr 1
  have hsq2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  rw [show (-(2 * N) : ℤ) = 2 * (-N) by ring, zpow_mul, zpow_two]
  congr 1
  linear_combination (τ : ℂ) ^ 2 * hsq2

private noncomputable def D2inv : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(Real.sqrt 2)⁻¹, (0 : ℝ); 0, Real.sqrt 2]
    (by
      rw [Matrix.det_fin_two_of]
      have hsq : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr two_pos
      field_simp [hsq]
      norm_num)

private lemma W2_mul_D2inv : W2 * D2inv = mapGL ℝ ModularGroup.S := by
  ext i j
  have hsq : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr two_pos
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [mapGL_apply]
  fin_cases i <;> fin_cases j <;>
    simp [W2, D2inv, ModularGroup.S, Matrix.mul_apply, Fin.sum_univ_two, hsq]

private lemma D2inv_10 : D2inv 1 0 = 0 := rfl

private lemma D2inv_mul_T_10 : (D2inv * mapGL ℝ ModularGroup.T) 1 0 = 0 := by
  change (D2inv.1 * (mapGL ℝ ModularGroup.T).1) 1 0 = 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, mapGL_apply]
  simp [D2inv, ModularGroup.T]

private lemma S_mul_S_eq : ModularGroup.S * ModularGroup.S = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

private lemma T_inv_coe : (ModularGroup.T⁻¹ : SL(2, ℤ)).1 = !![1, -1; 0, 1] := by
  let M : SL(2, ℤ) := ⟨!![1, -1; 0, 1], by decide⟩
  have hmul : ModularGroup.T * M = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> decide
  have hinv : ModularGroup.T⁻¹ = M := inv_eq_of_mul_eq_one_right hmul
  rw [hinv]

private lemma Gamma02_coset_decomp (γ : SL(2, ℤ)) :
    γ ∈ CongruenceSubgroup.Gamma0 2 ∨
      (∃ g ∈ CongruenceSubgroup.Gamma0 2, γ = g * (-ModularGroup.S)) ∨
      (∃ g ∈ CongruenceSubgroup.Gamma0 2, γ = g * (-ModularGroup.S) * ModularGroup.T) := by
  have hmem : ∀ A : SL(2, ℤ), A ∈ CongruenceSubgroup.Gamma0 2 ↔ (2 : ℤ) ∣ A 1 0 := fun A => by
    rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    rfl
  by_cases hc : (2 : ℤ) ∣ γ 1 0
  · exact Or.inl ((hmem γ).mpr hc)
  · by_cases hd : (2 : ℤ) ∣ γ 1 1
    · right; left
      refine ⟨γ * ModularGroup.S, ?_, ?_⟩
      · rw [hmem]
        have h10 : (γ * ModularGroup.S) 1 0 = γ 1 1 := by
          change (γ.1 * ModularGroup.S.1) 1 0 = γ 1 1
          simp [ModularGroup.S, Matrix.mul_apply, Fin.sum_univ_two]
        rw [h10]; exact hd
      · rw [mul_neg, mul_assoc, S_mul_S_eq, mul_neg, mul_one, neg_neg]
    · right; right
      refine ⟨γ * ModularGroup.T⁻¹ * ModularGroup.S, ?_, ?_⟩
      · rw [hmem]
        have h10 : (γ * ModularGroup.T⁻¹ * ModularGroup.S) 1 0 = γ 1 1 - γ 1 0 := by
          change ((γ.1 * (ModularGroup.T⁻¹ : SL(2, ℤ)).1) * ModularGroup.S.1) 1 0 = _
          rw [T_inv_coe]
          simp [ModularGroup.S, Matrix.mul_apply, Fin.sum_univ_two]
          ring
        rw [h10]
        omega
      · rw [mul_neg, mul_assoc (γ * ModularGroup.T⁻¹), S_mul_S_eq,
          mul_neg, mul_one, neg_neg, mul_assoc, inv_mul_cancel, mul_one]

private lemma mapGL_neg_one : mapGL ℝ (-1 : SL(2, ℤ)) = (-1 : GL (Fin 2) ℝ) := by
  ext i j
  rw [mapGL_apply]
  fin_cases i <;> fin_cases j <;> simp

private lemma mapGL_neg (A : SL(2, ℤ)) : mapGL ℝ (-A) = -(mapGL ℝ A) := by
  ext i j
  rw [mapGL_apply]
  change ((-A).1 i j : ℝ) = -((mapGL ℝ A : Matrix (Fin 2) (Fin 2) ℝ) i j)
  rw [mapGL_apply]
  simp

/-- Any function invariant under `Γ0(2)` that is a `W2`-eigenform and bounded at `i∞`
is bounded at all cusps of `Γ0(2)`. -/
private lemma isBoundedAt_Γ02_of_W2 {k : ℤ} {f : ℍ → ℂ} {ε : ℂ}
    (hΓ : ∀ γ ∈ CongruenceSubgroup.Gamma0 2, f ∣[k] γ = f)
    (hW : f ∣[k] W2 = ε • f)
    (hbdd : IsBoundedAtImInfty f) :
    ∀ {c : OnePoint ℝ}, IsCusp c Γ02 → c.IsBoundedAt f k := by
  intro c hc
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
  intro γ _
  have hnegGL : f ∣[k] (-1 : GL (Fin 2) ℝ) = f := by
    have h2 : f ∣[k] (mapGL ℝ (-1 : SL(2, ℤ))) = f := hΓ (-1) neg_one_mem_Gamma02
    rwa [mapGL_neg_one] at h2
  rcases Gamma02_coset_decomp γ with hγ | ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
  · rw [hΓ γ hγ]; exact hbdd
  · have hstep : f ∣[k] (g * -ModularGroup.S) = (f ∣[k] W2) ∣[k] D2inv := by
      change f ∣[k] mapGL ℝ (g * -ModularGroup.S) = _
      rw [map_mul, mapGL_neg, SlashAction.slash_mul]
      have hg' : f ∣[k] mapGL ℝ g = f := hΓ g hg
      rw [hg', show -(mapGL ℝ ModularGroup.S) = (-1 : GL (Fin 2) ℝ) * mapGL ℝ ModularGroup.S by simp,
        SlashAction.slash_mul, hnegGL, ← W2_mul_D2inv, SlashAction.slash_mul]
    rw [hstep, hW, ModularForm.smul_slash]
    exact (hbdd.slash k D2inv_10).const_smul_left _
  · have hstep : f ∣[k] (g * -ModularGroup.S * ModularGroup.T) =
        (f ∣[k] W2) ∣[k] (D2inv * mapGL ℝ ModularGroup.T) := by
      change f ∣[k] mapGL ℝ (g * -ModularGroup.S * ModularGroup.T) = _
      rw [map_mul, map_mul, mapGL_neg, SlashAction.slash_mul, SlashAction.slash_mul]
      have hg' : f ∣[k] mapGL ℝ g = f := hΓ g hg
      rw [hg', show -(mapGL ℝ ModularGroup.S) = (-1 : GL (Fin 2) ℝ) * mapGL ℝ ModularGroup.S by simp,
        SlashAction.slash_mul, hnegGL, ← W2_mul_D2inv, SlashAction.slash_mul,
        ← SlashAction.slash_mul]
    rw [hstep, hW, ModularForm.smul_slash]
    exact (hbdd.slash k D2inv_mul_T_10).const_smul_left _

private lemma isZeroAt_Γ02_of_W2 {k : ℤ} {f : ℍ → ℂ} {ε : ℂ}
    (hΓ : ∀ γ ∈ CongruenceSubgroup.Gamma0 2, f ∣[k] γ = f)
    (hW : f ∣[k] W2 = ε • f)
    (hzero : IsZeroAtImInfty f) :
    ∀ {c : OnePoint ℝ}, IsCusp c Γ02 → c.IsZeroAt f k := by
  intro c hc
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
  intro γ _
  have hnegGL : f ∣[k] (-1 : GL (Fin 2) ℝ) = f := by
    have h2 : f ∣[k] (mapGL ℝ (-1 : SL(2, ℤ))) = f := hΓ (-1) neg_one_mem_Gamma02
    rwa [mapGL_neg_one] at h2
  rcases Gamma02_coset_decomp γ with hγ | ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
  · rw [hΓ γ hγ]; exact hzero
  · have hstep : f ∣[k] (g * -ModularGroup.S) = (f ∣[k] W2) ∣[k] D2inv := by
      change f ∣[k] mapGL ℝ (g * -ModularGroup.S) = _
      rw [map_mul, mapGL_neg, SlashAction.slash_mul]
      have hg' : f ∣[k] mapGL ℝ g = f := hΓ g hg
      rw [hg', show -(mapGL ℝ ModularGroup.S) = (-1 : GL (Fin 2) ℝ) * mapGL ℝ ModularGroup.S by simp,
        SlashAction.slash_mul, hnegGL, ← W2_mul_D2inv, SlashAction.slash_mul]
    rw [hstep, hW, ModularForm.smul_slash]
    change Tendsto (fun x => (UpperHalfPlane.σ D2inv ε) • (f ∣[k] D2inv) x) atImInfty (𝓝 0)
    simpa only [smul_zero] using (hzero.slash k D2inv_10).const_smul (UpperHalfPlane.σ D2inv ε)
  · have hstep : f ∣[k] (g * -ModularGroup.S * ModularGroup.T) =
        (f ∣[k] W2) ∣[k] (D2inv * mapGL ℝ ModularGroup.T) := by
      change f ∣[k] mapGL ℝ (g * -ModularGroup.S * ModularGroup.T) = _
      rw [map_mul, map_mul, mapGL_neg, SlashAction.slash_mul, SlashAction.slash_mul]
      have hg' : f ∣[k] mapGL ℝ g = f := hΓ g hg
      rw [hg', show -(mapGL ℝ ModularGroup.S) = (-1 : GL (Fin 2) ℝ) * mapGL ℝ ModularGroup.S by simp,
        SlashAction.slash_mul, hnegGL, ← W2_mul_D2inv, SlashAction.slash_mul,
        ← SlashAction.slash_mul]
    rw [hstep, hW, ModularForm.smul_slash]
    change Tendsto (fun x => (UpperHalfPlane.σ (D2inv * mapGL ℝ ModularGroup.T) ε) •
      (f ∣[k] (D2inv * mapGL ℝ ModularGroup.T)) x) atImInfty (𝓝 0)
    simpa only [smul_zero] using
      (hzero.slash k D2inv_mul_T_10).const_smul (UpperHalfPlane.σ (D2inv * mapGL ℝ ModularGroup.T) ε)

/- #### The weight-2 Eisenstein series $E_2^*(\tau) = 2 E_2(2\tau) - E_2(\tau)$ on $\Gamma_0(2)$ -/

private noncomputable def E2star (τ : ℍ) : ℂ := 2 * E2 (mul2 τ) - E2 τ

private lemma E2star_mdiff : MDiff E2star :=
  (mdifferentiable_const.mul (mdiff_comp_mul2 E2_mdifferentiable)).sub E2_mdifferentiable

private lemma E2star_slash_Gamma02 (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 2) :
    E2star ∣[(2 : ℤ)] γ = E2star := by
  have hc : (2 : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) 2).mp hγ
  obtain ⟨c', hc'⟩ := hc
  let γ' : SL(2, ℤ) := ⟨!![γ 0 0, 2 * γ 0 1; c', γ 1 1], by
    have hdet := γ.2
    rw [Matrix.det_fin_two] at hdet ⊢
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    linear_combination hdet + γ 0 1 * hc'⟩
  have hdenom : ∀ τ : ℍ, denom (mapGL ℝ γ') (mul2 τ) = denom (mapGL ℝ γ) τ := fun τ => by
    simp only [denom, mapGL_apply, coe_mul2]
    change (c' : ℂ) * (2 * (τ : ℂ)) + (γ 1 1 : ℂ) = (γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ)
    rw [hc']; push_cast; ring
  have hsmul : ∀ τ : ℍ, mul2 (γ • τ) = γ' • mul2 τ := fun τ => by
    ext
    have h1 : ((γ • τ : ℍ) : ℂ) = num (mapGL ℝ γ) τ / denom (mapGL ℝ γ) τ :=
      UpperHalfPlane.coe_smul_of_det_pos (by simp) τ
    have h2 : ((γ' • mul2 τ : ℍ) : ℂ) = num (mapGL ℝ γ') (mul2 τ) / denom (mapGL ℝ γ') (mul2 τ) :=
      UpperHalfPlane.coe_smul_of_det_pos (by simp) (mul2 τ)
    rw [coe_mul2, h1, h2, hdenom τ]
    have hnum : 2 * num (mapGL ℝ γ) τ = num (mapGL ℝ γ') (mul2 τ) := by
      simp only [num, mapGL_apply, coe_mul2]
      change 2 * ((γ 0 0 : ℂ) * (τ : ℂ) + (γ 0 1 : ℂ)) =
        (γ 0 0 : ℂ) * (2 * (τ : ℂ)) + ((2 * γ 0 1 : ℤ) : ℂ)
      push_cast; ring
    rw [← mul_div_assoc, hnum]
  ext τ
  rw [ModularForm.SL_slash_def]
  simp only [E2star, hsmul τ]
  have h1 := congrFun (E2_slash_action γ) τ
  have h2 := congrFun (E2_slash_action γ') (mul2 τ)
  simp only [ModularForm.SL_slash_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, D2] at h1 h2
  have hden' : denom γ' (mul2 τ) = denom γ τ := hdenom τ
  rw [hden'] at h2
  have hc'_cast : (γ 1 0 : ℂ) = 2 * (γ' 1 0 : ℂ) := by
    change (γ 1 0 : ℂ) = 2 * (c' : ℂ)
    rw [hc']; push_cast; ring
  rw [hc'_cast] at h1
  linear_combination 2 * h2 - h1

private lemma E2star_slash_W2 : E2star ∣[(2 : ℤ)] W2 = -E2star := by
  ext τ
  have h1 := congrFun (E2_slash_action ModularGroup.S) τ
  have h2 := congrFun (E2_slash_action ModularGroup.S) (mul2 τ)
  simp only [ModularForm.SL_slash_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, D2_S,
    ModularGroup.denom_S, zpow_neg, zpow_two] at h1 h2
  rw [coe_mul2] at h2
  have hW : (E2star ∣[(2 : ℤ)] W2) τ = E2star (W2 • τ) * (2 * (τ : ℂ) ^ 2)⁻¹ := by
    simpa using slash_W2_even 1 E2star τ
  rw [hW, E2star, mul2_W2_smul, W2_smul_eq_S_mul2]
  simp only [Pi.neg_apply, E2star]
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have h2τ : (2 * (τ : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hτ
  have h1' : E2 (ModularGroup.S • τ) =
      (τ : ℂ) ^ 2 * (E2 τ - (1 / (2 * riemannZeta 2)) * (2 * π * I / τ)) := by
    have hmul := congrArg (· * (τ : ℂ) ^ 2) h1
    have hcancel : E2 (ModularGroup.S • τ) * ((τ : ℂ) * (τ : ℂ))⁻¹ * (τ : ℂ) ^ 2 =
        E2 (ModularGroup.S • τ) := by field_simp [hτ]
    linear_combination hmul - hcancel
  have h2' : E2 (ModularGroup.S • mul2 τ) =
      (2 * (τ : ℂ)) ^ 2 * (E2 (mul2 τ) - (1 / (2 * riemannZeta 2)) * (2 * π * I / (2 * τ))) := by
    have hmul := congrArg (· * (2 * (τ : ℂ)) ^ 2) h2
    have hcancel : E2 (ModularGroup.S • mul2 τ) * (2 * (τ : ℂ) * (2 * (τ : ℂ)))⁻¹ * (2 * (τ : ℂ)) ^ 2 =
        E2 (ModularGroup.S • mul2 τ) := by field_simp [h2τ]
    linear_combination hmul - hcancel
  rw [h1', h2']
  field_simp [hτ]
  ring

private def e2starCoeff (m : ℕ) : ℤ :=
  if m = 0 then 1
  else 24 * (σ 1 m : ℤ) - (if 2 ∣ m then 48 * (σ 1 (m / 2) : ℤ) else 0)

private lemma E2star_hasSum_qExpansion (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (e2starCoeff m : ℂ) • Periodic.qParam 1 τ ^ m) (E2star τ) := by
  have h1 := hasSum_qExpansion_E2 (z := τ)
  have h2 := hasSum_qExpansion_E2 (z := mul2 τ)
  have hq2 : ∀ k : ℕ, cexp (2 * π * I * (mul2 τ : ℂ)) ^ k = Periodic.qParam 1 τ ^ (2 * k) := fun k => by
    simp only [coe_mul2, Periodic.qParam, ofReal_one, div_one, ← exp_nat_mul]
    congr 1; push_cast; ring
  have h1' : HasSum (fun m : ℕ ↦ (if m = 0 then 1 else -24 * (σ 1 m : ℂ)) • Periodic.qParam 1 τ ^ m)
      (E2 τ) := by
    simpa only [Periodic.qParam, ofReal_one, div_one] using h1
  have h2_ev : HasSum (fun m : ℕ ↦
      (if 2 ∣ m then (if m / 2 = 0 then 1 else -24 * (σ 1 (m / 2) : ℂ)) else 0) •
        Periodic.qParam 1 τ ^ m) (E2 (mul2 τ)) := by
    have hinj : Function.Injective (fun k : ℕ ↦ 2 * k) := fun a b hab => by dsimp at hab; omega
    rw [← hinj.hasSum_iff (f := fun m : ℕ ↦
      (if 2 ∣ m then (if m / 2 = 0 then 1 else -24 * (σ 1 (m / 2) : ℂ)) else 0) •
        Periodic.qParam 1 τ ^ m)]
    · convert h2 using 1
      ext k
      have hk2 : 2 ∣ 2 * k := ⟨k, rfl⟩
      have hdiv : (2 * k) / 2 = k := Nat.mul_div_right k two_pos
      dsimp only [Function.comp_apply]
      rw [if_pos hk2, hdiv, hq2 k]
    · intro m hm
      have hnd : ¬ 2 ∣ m := by
        intro ⟨k, hk⟩; exact hm ⟨k, hk.symm⟩
      simp [hnd]
  have hcomb := (h2_ev.mul_left 2).sub h1'
  have hfn : (fun m : ℕ ↦ (e2starCoeff m : ℂ) • Periodic.qParam 1 τ ^ m) =
      (fun m : ℕ ↦ 2 * ((if 2 ∣ m then (if m / 2 = 0 then 1 else -24 * (σ 1 (m / 2) : ℂ)) else 0) •
        Periodic.qParam 1 τ ^ m) -
        (if m = 0 then 1 else -24 * (σ 1 m : ℂ)) • Periodic.qParam 1 τ ^ m) := by
    ext m
    simp only [e2starCoeff, smul_eq_mul]
    by_cases hm : m = 0
    · subst hm; simp; ring
    · by_cases hd : 2 ∣ m
      · have hne : m / 2 ≠ 0 := by obtain ⟨k, hk⟩ := hd; omega
        simp [hm, hd, hne]; ring
      · simp [hm, hd]
  rw [hfn]
  exact hcomb

private lemma isBoundedAtImInfty_E2star : IsBoundedAtImInfty E2star :=
  isBoundedAtImInfty_of_hasSum_qExpansion one_pos E2star_hasSum_qExpansion

private noncomputable def E2starMF : ModularForm Γ02 2 where
  toFun := E2star
  slash_action_eq' := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact E2star_slash_Gamma02 γ hγ
  holo' := E2star_mdiff
  bdd_at_cusps' hc := isBoundedAt_Γ02_of_W2 (ε := -1) E2star_slash_Gamma02
    (by simpa using E2star_slash_W2) isBoundedAtImInfty_E2star hc

private lemma E2star_qExpansion_coeff (m : ℕ) :
    (qExpansion 1 (E2starMF : ℍ → ℂ)).coeff m = (e2starCoeff m : ℂ) :=
  (ModularFormClass.qExpansion_coeff_unique (f := E2starMF) one_pos one_mem_strictPeriods_Γ02
    E2star_hasSum_qExpansion m).symm

/- #### Generation of $\Gamma_0(2)$ and the character of $\eta_4(\tau) = \eta(\tau)^4 \eta(2\tau)^4$ -/

private def Umat : SL(2, ℤ) := ⟨!![1, 0; 2, 1], by decide⟩

private lemma Umat_mem_Gamma02 : Umat ∈ CongruenceSubgroup.Gamma0 2 := by
  rw [CongruenceSubgroup.Gamma0_mem]
  decide

private lemma Umat_inv_coe : (Umat⁻¹ : SL(2, ℤ)).1 = !![1, 0; -2, 1] := by
  let M : SL(2, ℤ) := ⟨!![1, 0; -2, 1], by decide⟩
  have hmul : Umat * M = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> decide
  have hinv : Umat⁻¹ = M := inv_eq_of_mul_eq_one_right hmul
  rw [hinv]

private lemma W2_conj_T_inv :
    W2 * (mapGL ℝ (ModularGroup.T⁻¹ : SL(2, ℤ))) * W2⁻¹ = mapGL ℝ Umat := by
  rw [W2_inv]
  ext i j
  have hsq : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr two_pos
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  change ((W2.1 * (mapGL ℝ (ModularGroup.T⁻¹ : SL(2, ℤ))).1) * (-W2.1)) i j =
    (mapGL ℝ Umat : Matrix (Fin 2) (Fin 2) ℝ) i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply, mapGL_apply,
    show ∀ r c, (ModularGroup.T⁻¹ : SL(2, ℤ)) r c = (!![1, -1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) r c from
      fun r c => congrFun (congrFun T_inv_coe r) c]
  fin_cases i <;> fin_cases j <;>
    simp [W2_val, Umat, hsq, hsq2]

/-- $\Gamma_0(2)$ is generated by $-I$, $T = \begin{pmatrix}1 & 1 \\ 0 & 1\end{pmatrix}$, and
$U = \begin{pmatrix}1 & 0 \\ 2 & 1\end{pmatrix}$. -/
private lemma Gamma02_eq_closure :
    CongruenceSubgroup.Gamma0 2 =
      Subgroup.closure ({(-1 : SL(2, ℤ)), ModularGroup.T, Umat} : Set SL(2, ℤ)) := by
  let H := Subgroup.closure ({(-1 : SL(2, ℤ)), ModularGroup.T, Umat} : Set SL(2, ℤ))
  have hHle : H ≤ CongruenceSubgroup.Gamma0 2 := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl | rfl
    · exact neg_one_mem_Gamma02
    · exact T_mem_Gamma02
    · exact Umat_mem_Gamma02
  apply le_antisymm _ hHle
  have hTmem : ModularGroup.T ∈ H := Subgroup.subset_closure (by simp)
  have hUmem : Umat ∈ H := Subgroup.subset_closure (by simp)
  have hNegmem : (-1 : SL(2, ℤ)) ∈ H := Subgroup.subset_closure (by simp)
  have key : ∀ n : ℕ, ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 2 →
      (γ 0 0).natAbs + (γ 1 0).natAbs = n → γ ∈ H := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro γ hγ hn
      have hc2 : (2 : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) 2).mp hγ
      have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
        have hd := γ.2
        rwa [Matrix.det_fin_two] at hd
      by_cases hc0 : γ 1 0 = 0
      · have hmul1 : γ 0 0 * γ 1 1 = 1 := by linear_combination hdet + γ 0 1 * hc0
        have ha : γ 0 0 = 1 ∨ γ 0 0 = -1 := by
          rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hmul1 with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact Or.inl h1
          · exact Or.inr h1
        rcases ha with ha1 | ha1
        · have hd1 : γ 1 1 = 1 := by rw [ha1, one_mul] at hmul1; exact hmul1
          have heq : γ = ModularGroup.T ^ (γ 0 1) := by
            ext i j
            fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow, ha1, hd1, hc0]
          rw [heq]; exact Subgroup.zpow_mem _ hTmem _
        · have hd1 : γ 1 1 = -1 := by rw [ha1, neg_one_mul] at hmul1; linarith
          have heq : γ = (-1) * ModularGroup.T ^ (-(γ 0 1)) := by
            ext i j
            fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow, ha1, hd1, hc0]
          rw [heq]; exact Subgroup.mul_mem _ hNegmem (Subgroup.zpow_mem _ hTmem _)
      · have ha_odd : ¬ (2 : ℤ) ∣ γ 0 0 := by
          intro ⟨k, hk⟩
          obtain ⟨m, hm⟩ := hc2
          have : 2 * (k * γ 1 1 - γ 0 1 * m) = 1 := by
            linear_combination hdet - γ 1 1 * hk + γ 0 1 * hm
          omega
        have hne_abs : (γ 0 0).natAbs ≠ (γ 1 0).natAbs := by
          intro heq
          obtain ⟨m, hm⟩ := hc2
          have : (2 : ℤ) ∣ γ 0 0 := by
            rcases Int.natAbs_eq_natAbs_iff.mp heq with h1 | h1
            · exact ⟨m, by omega⟩
            · exact ⟨-m, by omega⟩
          exact ha_odd this
        rcases lt_or_gt_of_ne hne_abs with hlt | hgt
        · let s : ℤ := if (0 < γ 0 0 ↔ 0 < γ 1 0) then -1 else 1
          let γ' : SL(2, ℤ) := Umat ^ s * γ
          have hγ' : γ' ∈ CongruenceSubgroup.Gamma0 2 :=
            Subgroup.mul_mem _ (Subgroup.zpow_mem _ Umat_mem_Gamma02 s) hγ
          have hUs : (Umat ^ s : SL(2, ℤ)).1 = !![1, 0; 2 * s, 1] := by
            dsimp [s]
            split_ifs
            · rw [zpow_neg_one, Umat_inv_coe]; norm_num
            · rw [zpow_one]; rfl
          have ha' : γ' 0 0 = γ 0 0 := by
            change (Umat ^ s * γ).1 0 0 = γ 0 0
            rw [Matrix.SpecialLinearGroup.coe_mul, hUs]
            simp [Matrix.mul_apply, Fin.sum_univ_two]
          have hc' : γ' 1 0 = γ 1 0 + 2 * s * γ 0 0 := by
            change (Umat ^ s * γ).1 1 0 = _
            rw [Matrix.SpecialLinearGroup.coe_mul, hUs]
            simp [Matrix.mul_apply, Fin.sum_univ_two]
            ring
          have hdec : (γ' 1 0).natAbs < (γ 1 0).natAbs := by
            rw [hc']; dsimp [s]
            split_ifs with hs <;> omega
          have hmem' : γ' ∈ H := ih _ (by omega) γ' hγ' rfl
          have heq : γ = Umat ^ (-s) * γ' := by
            simp [γ', ← mul_assoc]
          rw [heq]
          exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hUmem _) hmem'
        · let s : ℤ := if (0 < γ 0 0 ↔ 0 < γ 1 0) then -1 else 1
          let γ' : SL(2, ℤ) := ModularGroup.T ^ s * γ
          have hγ' : γ' ∈ CongruenceSubgroup.Gamma0 2 :=
            Subgroup.mul_mem _ (Subgroup.zpow_mem _ T_mem_Gamma02 s) hγ
          have ha' : γ' 0 0 = γ 0 0 + s * γ 1 0 := by
            change (ModularGroup.T ^ s * γ).1 0 0 = _
            rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
            simp [Matrix.mul_apply, Fin.sum_univ_two]
          have hc' : γ' 1 0 = γ 1 0 := by
            change (ModularGroup.T ^ s * γ).1 1 0 = _
            rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
            simp [Matrix.mul_apply, Fin.sum_univ_two]
          have hdec : (γ' 0 0).natAbs < (γ 0 0).natAbs := by
            rw [ha']; dsimp [s]
            split_ifs with hs <;> omega
          have hmem' : γ' ∈ H := ih _ (by omega) γ' hγ' rfl
          have heq : γ = ModularGroup.T ^ (-s) * γ' := by
            simp [γ', ← mul_assoc]
          rw [heq]
          exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hTmem _) hmem'
  intro γ hγ
  exact key _ γ hγ rfl

/-- The multiplicative sign character $\tilde\chi\begin{pmatrix}a & b \\ 2c & d\end{pmatrix} = (-1)^{b+c}$
on integer matrices with even bottom-left entry and odd determinant. -/
private def chiInt (M : Matrix (Fin 2) (Fin 2) ℤ) : ℂ :=
  if Even (M 0 1 + M 1 0 / 2) then 1 else -1

private lemma chiInt_sq (M : Matrix (Fin 2) (Fin 2) ℤ) : chiInt M ^ 2 = 1 := by
  unfold chiInt; split_ifs <;> norm_num

private lemma chiInt_mul {M₁ M₂ : Matrix (Fin 2) (Fin 2) ℤ}
    (hc1 : (2 : ℤ) ∣ M₁ 1 0) (hc2 : (2 : ℤ) ∣ M₂ 1 0)
    (hd1 : Odd M₁.det) (hd2 : Odd M₂.det) :
    chiInt (M₁ * M₂) = chiInt M₁ * chiInt M₂ := by
  obtain ⟨c1, hc1'⟩ := hc1
  obtain ⟨c2, hc2'⟩ := hc2
  have hdet1 : M₁ 0 0 * M₁ 1 1 - M₁ 0 1 * (2 * c1) = M₁.det := by
    rw [Matrix.det_fin_two, hc1']
  have hdet2 : M₂ 0 0 * M₂ 1 1 - M₂ 0 1 * (2 * c2) = M₂.det := by
    rw [Matrix.det_fin_two, hc2']
  have h10 : (M₁ * M₂) 1 0 = 2 * (c1 * M₂ 0 0 + M₁ 1 1 * c2) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hc1', hc2']; ring
  have h01 : (M₁ * M₂) 0 1 = M₁ 0 0 * M₂ 0 1 + M₁ 0 1 * M₂ 1 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
  have hdiv1 : M₁ 1 0 / 2 = c1 := by omega
  have hdiv2 : M₂ 1 0 / 2 = c2 := by omega
  have hdiv12 : (M₁ * M₂) 1 0 / 2 = c1 * M₂ 0 0 + M₁ 1 1 * c2 := by omega
  have odd_factors : ∀ a b : ℤ, Odd (a * b) → a % 2 = 1 ∧ b % 2 = 1 := by
    intro a b ⟨k, hk⟩
    have hm : (a * b) % 2 = 1 := by omega
    rw [Int.mul_emod] at hm
    have ha0 : a % 2 = 0 ∨ a % 2 = 1 := by omega
    have hb0 : b % 2 = 0 ∨ b % 2 = 1 := by omega
    rcases ha0 with ha0 | ha0 <;> rcases hb0 with hb0 | hb0 <;> simp [ha0, hb0] at hm ⊢
  have ho1 : M₁ 0 0 % 2 = 1 ∧ M₁ 1 1 % 2 = 1 := by
    rcases hd1 with ⟨k, hk⟩
    exact odd_factors (M₁ 0 0) (M₁ 1 1) ⟨k + M₁ 0 1 * c1, by linear_combination hdet1 + hk⟩
  have ho2 : M₂ 0 0 % 2 = 1 ∧ M₂ 1 1 % 2 = 1 := by
    rcases hd2 with ⟨k, hk⟩
    exact odd_factors (M₂ 0 0) (M₂ 1 1) ⟨k + M₂ 0 1 * c2, by linear_combination hdet2 + hk⟩
  have hpar : ((M₁ * M₂) 0 1 + (M₁ * M₂) 1 0 / 2) % 2 =
      ((M₁ 0 1 + M₁ 1 0 / 2) + (M₂ 0 1 + M₂ 1 0 / 2)) % 2 := by
    rw [h01, hdiv12, hdiv1, hdiv2]
    obtain ⟨k1, hk1⟩ : (2 : ℤ) ∣ (M₁ 0 0 - 1) := ⟨(M₁ 0 0 - 1) / 2, by omega⟩
    obtain ⟨k2, hk2⟩ : (2 : ℤ) ∣ (M₂ 1 1 - 1) := ⟨(M₂ 1 1 - 1) / 2, by omega⟩
    obtain ⟨k3, hk3⟩ : (2 : ℤ) ∣ (M₂ 0 0 - 1) := ⟨(M₂ 0 0 - 1) / 2, by omega⟩
    obtain ⟨k4, hk4⟩ : (2 : ℤ) ∣ (M₁ 1 1 - 1) := ⟨(M₁ 1 1 - 1) / 2, by omega⟩
    have hdiff : (M₁ 0 0 * M₂ 0 1 + M₁ 0 1 * M₂ 1 1 + (c1 * M₂ 0 0 + M₁ 1 1 * c2)) -
        ((M₁ 0 1 + c1) + (M₂ 0 1 + c2)) =
        2 * (k1 * M₂ 0 1 + M₁ 0 1 * k2 + c1 * k3 + k4 * c2) := by
      linear_combination M₂ 0 1 * hk1 + M₁ 0 1 * hk2 + c1 * hk3 + c2 * hk4
    omega
  unfold chiInt
  have hev : ∀ n : ℤ, Even n ↔ n % 2 = 0 := fun n => by
    constructor
    · rintro ⟨k, rfl⟩; omega
    · intro h; exact ⟨n / 2, by omega⟩
  simp only [hev]
  split_ifs with h12 h1 h2 h2 <;> norm_num <;> omega

private lemma chiInt_one : chiInt (1 : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
  simp [chiInt]

private lemma chiInt_neg_one : chiInt (-1 : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
  simp [chiInt]

private lemma chiInt_T : chiInt ModularGroup.T.1 = -1 := by
  simp [chiInt, ModularGroup.T]

private lemma chiInt_U : chiInt Umat.1 = -1 := by
  simp [chiInt, Umat]

/-- $\eta_4(\tau) = \eta(\tau)^4 \eta(2\tau)^4$, weight 4 on $\Gamma_0(2)$ with character `chiInt`. -/
private noncomputable def eta4 (τ : ℍ) : ℂ :=
  ModularForm.eta τ ^ 4 * ModularForm.eta (mul2 τ) ^ 4

private lemma eta4_ne_zero (τ : ℍ) : eta4 τ ≠ 0 :=
  mul_ne_zero (pow_ne_zero 4 (ModularForm.eta_ne_zero τ.2))
    (pow_ne_zero 4 (ModularForm.eta_ne_zero (mul2 τ).2))

private lemma eta4_mdiff : MDiff eta4 := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have h1 : DifferentiableOn ℂ (fun z : ℂ ↦ ModularForm.eta z ^ 4) upperHalfPlaneSet :=
    fun z hz => ((ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hz).pow 4).differentiableWithinAt
  have h2 : DifferentiableOn ℂ (fun z : ℂ ↦ ModularForm.eta (2 * z) ^ 4) upperHalfPlaneSet := by
    intro z hz
    have hz2 : 2 * z ∈ upperHalfPlaneSet := by
      change 0 < (2 * z).im
      have : 0 < z.im := hz
      simpa using mul_pos two_pos this
    exact (((ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hz2).comp z
      (differentiableAt_id.const_mul 2)).pow 4).differentiableWithinAt
  exact (h1.mul h2).congr fun z hz => by simp [eta4, mul2, ofComplex_apply_of_im_pos hz]

private lemma csqrt_sq {z : ℂ} (hz : z ≠ 0) : Complex.sqrt z ^ 2 = z := by
  change (z ^ (2⁻¹ : ℂ)) ^ 2 = z
  rw [Complex.cpow_def_of_ne_zero hz, ← Complex.exp_nat_mul]
  have : (2 : ℕ) * (Complex.log z * (2⁻¹ : ℂ)) = Complex.log z := by push_cast; ring
  rw [this, Complex.exp_log hz]

private lemma eta4_slash_W2 : eta4 ∣[(4 : ℤ)] W2 = eta4 := by
  ext τ
  have hW : (eta4 ∣[(4 : ℤ)] W2) τ = eta4 (W2 • τ) * (2 * (τ : ℂ) ^ 2) ^ (-2 : ℤ) := by
    simpa using slash_W2_even 2 eta4 τ
  rw [hW, eta4, mul2_W2_smul, W2_smul_eq_S_mul2]
  have hS1 : ModularForm.eta ((ModularGroup.S • τ : ℍ) : ℂ) =
      (Complex.sqrt Complex.I)⁻¹ * (Complex.sqrt τ * ModularForm.eta τ) := by
    have h := ModularForm.eta_comp_eq_csqrt_I_inv τ.2
    have harg : ((ModularGroup.S • τ : ℍ) : ℂ) = -1 / (τ : ℂ) := by
      rw [UpperHalfPlane.modular_S_smul]; ring
    rw [harg]
    simpa [Function.comp_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] using h
  have hS2 : ModularForm.eta ((ModularGroup.S • mul2 τ : ℍ) : ℂ) =
      (Complex.sqrt Complex.I)⁻¹ * (Complex.sqrt (mul2 τ) * ModularForm.eta (mul2 τ)) := by
    have h := ModularForm.eta_comp_eq_csqrt_I_inv (mul2 τ).2
    have harg : ((ModularGroup.S • mul2 τ : ℍ) : ℂ) = -1 / (mul2 τ : ℂ) := by
      rw [UpperHalfPlane.modular_S_smul]; ring
    rw [harg]
    simpa [Function.comp_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] using h
  rw [hS1, hS2]
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have h2τ : (mul2 τ : ℂ) ≠ 0 := (mul2 τ).ne_zero
  have hsqI : Complex.sqrt Complex.I ^ 8 = 1 := by
    calc Complex.sqrt Complex.I ^ 8 = (Complex.sqrt Complex.I ^ 2) ^ 4 := by ring
      _ = Complex.I ^ 4 := by rw [csqrt_sq Complex.I_ne_zero]
      _ = 1 := Complex.I_pow_four
  have hsq1 : Complex.sqrt (τ : ℂ) ^ 4 = (τ : ℂ) ^ 2 := by
    calc Complex.sqrt (τ : ℂ) ^ 4 = (Complex.sqrt (τ : ℂ) ^ 2) ^ 2 := by ring
      _ = (τ : ℂ) ^ 2 := by rw [csqrt_sq hτ]
  have hsq2 : Complex.sqrt (mul2 τ : ℂ) ^ 4 = (2 * (τ : ℂ)) ^ 2 := by
    calc Complex.sqrt (mul2 τ : ℂ) ^ 4 = (Complex.sqrt (mul2 τ : ℂ) ^ 2) ^ 2 := by ring
      _ = (2 * (τ : ℂ)) ^ 2 := by rw [csqrt_sq h2τ, coe_mul2]
  have hsqI_ne : Complex.sqrt Complex.I ≠ 0 := by
    intro h0; rw [h0] at hsqI; norm_num at hsqI
  simp only [mul_pow, inv_pow, hsq1, hsq2, zpow_neg, zpow_two, eta4]
  field_simp [hτ, hsqI_ne]
  linear_combination -(ModularForm.eta τ ^ 4 * ModularForm.eta (mul2 τ) ^ 4) * hsqI

private lemma eta_add_one (z : ℂ) :
    ModularForm.eta (z + 1) = cexp (π * Complex.I / 12) * ModularForm.eta z := by
  unfold ModularForm.eta
  have hq : Periodic.qParam 24 (z + 1) = cexp (π * Complex.I / 12) * Periodic.qParam 24 z := by
    simp only [Periodic.qParam, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hprod : ∀ n : ℕ, ModularForm.eta_q n (z + 1) = ModularForm.eta_q n z := fun n => by
    simp only [ModularForm.eta_q_eq_cexp]
    rw [mul_add, mul_one, Complex.exp_add]
    have hper : cexp (2 * π * Complex.I * ((n : ℂ) + 1)) = 1 := by
      have := Complex.exp_nat_mul_two_pi_mul_I (n + 1)
      push_cast at this
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    rw [hper, mul_one]
  simp_rw [hprod, hq, mul_assoc]

private lemma eta4_slash_T : eta4 ∣[(4 : ℤ)] ModularGroup.T = -eta4 := by
  ext τ
  rw [ModularForm.SL_slash_def]
  have hT : (ModularGroup.T • τ : ℍ) = (1 : ℝ) +ᵥ τ := UpperHalfPlane.modular_T_smul τ
  have hden : denom (mapGL ℝ ModularGroup.T) τ = 1 := by
    simp only [denom, mapGL_apply]
    simp [ModularGroup.T]
  change eta4 (ModularGroup.T • τ) * denom (mapGL ℝ ModularGroup.T) τ ^ (-4 : ℤ) = -eta4 τ
  rw [hT, hden, one_zpow, mul_one]
  simp only [eta4, coe_vadd, coe_mul2]
  have h1 : ((1 : ℝ) : ℂ) + (τ : ℂ) = (τ : ℂ) + 1 := by push_cast; ring
  have h2 : (2 : ℂ) * ((τ : ℂ) + 1) = (2 * (τ : ℂ) + 1) + 1 := by ring
  rw [h1, h2, eta_add_one, eta_add_one, eta_add_one]
  have hexp : cexp (π * Complex.I / 12) ^ 4 *
      (cexp (π * Complex.I / 12) * cexp (π * Complex.I / 12)) ^ 4 = -1 := by
    rw [← Complex.exp_add, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    have : (4 : ℕ) * (π * Complex.I / 12) + (4 : ℕ) * (π * Complex.I / 12 + π * Complex.I / 12) =
        π * Complex.I := by push_cast; ring
    rw [this, Complex.exp_pi_mul_I]
  linear_combination (ModularForm.eta τ ^ 4 * ModularForm.eta (2 * (τ : ℂ)) ^ 4) * hexp

private lemma eta4_slash_neg_one : eta4 ∣[(4 : ℤ)] (-1 : SL(2, ℤ)) = eta4 := by
  ext τ
  rw [ModularForm.SL_slash_def]
  have hact : (-1 : SL(2, ℤ)) • τ = τ := by
    ext
    change ((mapGL ℝ (-1 : SL(2, ℤ)) • τ : ℍ) : ℂ) = (τ : ℂ)
    have hdet1 : 0 < ((-1 : GL (Fin 2) ℝ).det : ℝ) := by
      rw [Matrix.GeneralLinearGroup.val_det_apply]
      change 0 < (-(1 : Matrix (Fin 2) (Fin 2) ℝ)).det
      rw [Matrix.det_fin_two]; norm_num
    rw [mapGL_neg_one, UpperHalfPlane.coe_smul_of_det_pos hdet1]
    simp [num, denom]
  change eta4 ((-1 : SL(2, ℤ)) • τ) * denom (mapGL ℝ (-1 : SL(2, ℤ))) τ ^ (-4 : ℤ) = eta4 τ
  rw [hact, mapGL_neg_one, denom_neg, denom_one]
  norm_num

private lemma eta4_slash_U : eta4 ∣[(4 : ℤ)] Umat = -eta4 := by
  have hTinv : eta4 ∣[(4 : ℤ)] (ModularGroup.T⁻¹ : SL(2, ℤ)) = -eta4 := by
    have h := congrArg (fun f => f ∣[(4 : ℤ)] (ModularGroup.T⁻¹ : SL(2, ℤ))) eta4_slash_T
    rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one, SlashAction.neg_slash] at h
    exact neg_eq_iff_eq_neg.mp h.symm
  have hnegGL : eta4 ∣[(4 : ℤ)] (-1 : GL (Fin 2) ℝ) = eta4 := by
    have h2 : eta4 ∣[(4 : ℤ)] mapGL ℝ (-1 : SL(2, ℤ)) = eta4 := eta4_slash_neg_one
    rwa [mapGL_neg_one] at h2
  change eta4 ∣[(4 : ℤ)] mapGL ℝ Umat = -eta4
  rw [← W2_conj_T_inv, SlashAction.slash_mul, SlashAction.slash_mul,
    eta4_slash_W2]
  have hTinv' : eta4 ∣[(4 : ℤ)] mapGL ℝ (ModularGroup.T⁻¹ : SL(2, ℤ)) = -eta4 := hTinv
  rw [hTinv', SlashAction.neg_slash, W2_inv,
    show (-W2 : GL (Fin 2) ℝ) = W2 * (-1 : GL (Fin 2) ℝ) by simp,
    SlashAction.slash_mul, eta4_slash_W2, hnegGL]

private lemma eta4_slash_Gamma02 (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 2) :
    eta4 ∣[(4 : ℤ)] γ = chiInt γ.1 • eta4 := by
  rw [Gamma02_eq_closure] at hγ
  induction hγ using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl
    · rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, chiInt_neg_one, one_smul]
      exact eta4_slash_neg_one
    · rw [chiInt_T, neg_one_smul]; exact eta4_slash_T
    · rw [chiInt_U, neg_one_smul]; exact eta4_slash_U
  | one =>
    rw [Matrix.SpecialLinearGroup.coe_one, chiInt_one, one_smul, SlashAction.slash_one]
  | mul x y hx hy ihx ihy =>
    have hx' : x ∈ CongruenceSubgroup.Gamma0 2 := by rw [Gamma02_eq_closure]; exact hx
    have hy' : y ∈ CongruenceSubgroup.Gamma0 2 := by rw [Gamma02_eq_closure]; exact hy
    have hcx : (2 : ℤ) ∣ x.1 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hx'
    have hcy : (2 : ℤ) ∣ y.1 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hy'
    rw [SlashAction.slash_mul, ihx, ModularForm.SL_smul_slash, ihy, smul_smul,
      Matrix.SpecialLinearGroup.coe_mul,
      chiInt_mul hcx hcy (by simp [x.2]) (by simp [y.2]), mul_comm]
  | inv x hx ihx =>
    have hx' : x ∈ CongruenceSubgroup.Gamma0 2 := by rw [Gamma02_eq_closure]; exact hx
    have hxi : x⁻¹ ∈ CongruenceSubgroup.Gamma0 2 := Subgroup.inv_mem _ hx'
    have hcx : (2 : ℤ) ∣ x.1 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hx'
    have hcxi : (2 : ℤ) ∣ (x⁻¹).1 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hxi
    have hdet_inv : Odd (x⁻¹).1.det := by
      have : (x⁻¹).1.det = 1 := (x⁻¹).2
      rw [this]; exact odd_one
    have hchi_inv : chiInt (x⁻¹).1 = chiInt x.1 := by
      have hm := chiInt_mul hcx hcxi (by simp [x.2]) hdet_inv
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, chiInt_one] at hm
      have hsq := chiInt_sq x.1
      linear_combination -chiInt (x⁻¹).1 * hsq + chiInt x.1 * hm.symm
    have h := congrArg (fun f => f ∣[(4 : ℤ)] x⁻¹) ihx
    rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one,
      ModularForm.SL_smul_slash] at h
    rw [hchi_inv]
    have hsq := chiInt_sq x.1
    have h2 := congrArg (fun f => chiInt x.1 • f) h.symm
    rw [smul_smul, ← sq, hsq, one_smul] at h2
    exact h2

/- #### The weight-8 cusp form $\Delta_8(\tau) = \eta_4(\tau)^2$ and the Structure Theorem -/

private noncomputable def Delta8 (τ : ℍ) : ℂ := eta4 τ ^ 2

private lemma Delta8_eq_mul : Delta8 = eta4 * eta4 := by
  ext τ; simp [Delta8, sq]

private lemma Delta8_ne_zero (τ : ℍ) : Delta8 τ ≠ 0 := pow_ne_zero 2 (eta4_ne_zero τ)

private lemma Delta8_mdiff : MDiff Delta8 := eta4_mdiff.pow 2

private lemma Delta8_slash_Gamma02 (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 2) :
    Delta8 ∣[(8 : ℤ)] γ = Delta8 := by
  rw [Delta8_eq_mul, show (8 : ℤ) = 4 + 4 by norm_num, ModularForm.mul_slash_SL2,
    eta4_slash_Gamma02 γ hγ]
  ext τ
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  have hsq := chiInt_sq γ.1
  linear_combination (eta4 τ * eta4 τ) * hsq

private lemma Delta8_slash_W2 : Delta8 ∣[(8 : ℤ)] W2 = Delta8 := by
  ext τ
  have hW : (Delta8 ∣[(8 : ℤ)] W2) τ = Delta8 (W2 • τ) * (2 * (τ : ℂ) ^ 2) ^ (-4 : ℤ) := by
    simpa using slash_W2_even 4 Delta8 τ
  rw [hW]
  have h := congrFun eta4_slash_W2 τ
  have hW4 : (eta4 ∣[(4 : ℤ)] W2) τ = eta4 (W2 • τ) * (2 * (τ : ℂ) ^ 2) ^ (-2 : ℤ) := by
    simpa using slash_W2_even 2 eta4 τ
  rw [hW4] at h
  have hsq := congrArg (fun x : ℂ => x ^ 2) h
  have hpow : ((2 * (τ : ℂ) ^ 2) ^ (-2 : ℤ)) ^ 2 = (2 * (τ : ℂ) ^ 2) ^ (-4 : ℤ) := by
    rw [← zpow_natCast, ← zpow_mul]; norm_num
  rw [mul_pow, hpow] at hsq
  exact hsq

private lemma Delta8_eq_q_prod (τ : ℍ) :
    Delta8 τ = Periodic.qParam 1 τ *
      (∏' n : ℕ, (1 - ModularForm.eta_q n τ) ^ 8) *
      (∏' n : ℕ, (1 - ModularForm.eta_q n (mul2 τ)) ^ 8) := by
  simp only [Delta8, eta4, ModularForm.eta, mul_pow, ← pow_mul]
  have hq : Periodic.qParam 24 (τ : ℂ) ^ 8 * Periodic.qParam 24 (mul2 τ : ℂ) ^ 8 =
      Periodic.qParam 1 τ := by
    simp only [Periodic.qParam, coe_mul2, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hp1 : (∏' n : ℕ, (1 - ModularForm.eta_q n τ)) ^ 8 =
      ∏' n : ℕ, (1 - ModularForm.eta_q n τ) ^ 8 :=
    ((ModularForm.multipliableLocallyUniformlyOn_eta.multipliable τ.2).tprod_pow 8).symm
  have hp2 : (∏' n : ℕ, (1 - ModularForm.eta_q n (mul2 τ))) ^ 8 =
      ∏' n : ℕ, (1 - ModularForm.eta_q n (mul2 τ)) ^ 8 :=
    ((ModularForm.multipliableLocallyUniformlyOn_eta.multipliable (mul2 τ).2).tprod_pow 8).symm
  rw [hp1, hp2]
  linear_combination (∏' n, (1 - ModularForm.eta_q n τ) ^ 8) *
    (∏' n, (1 - ModularForm.eta_q n (mul2 τ)) ^ 8) * hq

private lemma tendsto_tprod_one_sub_pow_zero (k : ℕ) :
    Tendsto (fun q : ℂ ↦ ∏' n : ℕ, (1 - q ^ (n + 1)) ^ k) (𝓝 0) (𝓝 1) := by
  have htprod : Tendsto (fun q : ℂ ↦ ∏' n : ℕ, (1 - q ^ (n + 1))) (𝓝 0) (𝓝 1) := by
    have := tendsto_tprod_one_add_of_dominated_convergence (𝓕 := 𝓝 (0 : ℂ)) (g := 0)
      (f := fun (q : ℂ) (n : ℕ) ↦ -q ^ (n + 1)) (bound := fun n ↦ (1 / 2 : ℝ) ^ (n + 1))
    simp only [Pi.zero_apply, norm_neg, norm_pow, add_zero, tprod_one] at this
    simp_rw [sub_eq_add_neg]
    refine this
      (by simpa only [pow_succ'] using (summable_geometric_of_abs_lt_one (by norm_num)).mul_left _)
      (fun m ↦ by simpa using ((continuous_pow (M := ℂ) (m + 1)).tendsto 0).neg) ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with q hq m
    exact pow_le_pow_left₀ (norm_nonneg _) (mem_ball_zero_iff.mp hq).le _
  have hpow := htprod.pow k
  rw [one_pow] at hpow
  refine hpow.congr' ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with q hq
  exact ((ModularForm.multipliable_one_sub_pow (mem_ball_zero_iff.mp hq)).tprod_pow k).symm

private lemma Delta8_tendsto_prod :
    Tendsto (fun τ : ℍ ↦ (∏' n : ℕ, (1 - ModularForm.eta_q n τ) ^ 8) *
      (∏' n : ℕ, (1 - ModularForm.eta_q n (mul2 τ)) ^ 8)) atImInfty (𝓝 1) := by
  have h1 := (tendsto_tprod_one_sub_pow_zero 8).comp (UpperHalfPlane.qParam_tendsto_atImInfty one_pos)
  have hq2_t : Tendsto (fun τ : ℍ ↦ Periodic.qParam 1 τ ^ 2) atImInfty (𝓝 0) := by
    have ht := ((continuous_pow (M := ℂ) 2).tendsto 0).comp (UpperHalfPlane.qParam_tendsto_atImInfty one_pos)
    rw [zero_pow two_ne_zero] at ht
    exact ht
  have h2 := (tendsto_tprod_one_sub_pow_zero 8).comp hq2_t
  have hmul := h1.mul h2
  rw [mul_one] at hmul
  refine hmul.congr fun τ => ?_
  simp only [Function.comp_apply, ModularForm.eta_q]
  congr 2
  ext n
  have hq2 : Periodic.qParam 1 (mul2 τ : ℂ) = Periodic.qParam 1 τ ^ 2 := by
    simp only [Periodic.qParam, coe_mul2, ofReal_one, div_one, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  rw [hq2]

private lemma Delta8_isZeroAtImInfty : IsZeroAtImInfty Delta8 := by
  apply Tendsto.congr (fun τ => (Delta8_eq_q_prod τ).symm)
  rw [show (0 : ℂ) = 0 * 1 by ring]
  have h := (UpperHalfPlane.qParam_tendsto_atImInfty one_pos).mul Delta8_tendsto_prod
  simpa only [mul_assoc] using h

private lemma exp_isBigO_Delta8 : (fun τ : ℍ ↦ Real.exp (-2 * π * τ.im)) =O[atImInfty] Delta8 := by
  refine .of_bound 2 ?_
  have hprod := Delta8_tendsto_prod.eventually
    (Metric.ball_mem_nhds 1 (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hprod] with τ hτ
  rw [Delta8_eq_q_prod, mul_assoc (Periodic.qParam 1 τ), norm_mul,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  have hq_norm : ‖Periodic.qParam 1 τ‖ = Real.exp (-2 * π * τ.im) := by
    rw [Periodic.norm_qParam]
    change Real.exp (-2 * π * τ.im / 1) = Real.exp (-2 * π * τ.im)
    ring_nf
  rw [← hq_norm]
  have hsub : ‖(∏' n, (1 - ModularForm.eta_q n τ) ^ 8) *
      (∏' n, (1 - ModularForm.eta_q n (mul2 τ)) ^ 8) - 1‖ < 1 / 2 := by
    rwa [Complex.dist_eq] at hτ
  have h1 := norm_sub_norm_le 1 ((∏' n, (1 - ModularForm.eta_q n τ) ^ 8) *
      (∏' n, (1 - ModularForm.eta_q n (mul2 τ)) ^ 8))
  have hprod_bound : 1 / 2 ≤ ‖(∏' n, (1 - ModularForm.eta_q n τ) ^ 8) *
      (∏' n, (1 - ModularForm.eta_q n (mul2 τ)) ^ 8)‖ := by
    rw [norm_one, norm_sub_rev] at h1; linarith
  linarith [norm_nonneg (Periodic.qParam 1 τ),
    mul_le_mul_of_nonneg_left hprod_bound (norm_nonneg (Periodic.qParam 1 τ))]

private noncomputable def Delta8CF : CuspForm Γ02 8 where
  toFun := Delta8
  slash_action_eq' := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact Delta8_slash_Gamma02 γ hγ
  holo' := Delta8_mdiff
  zero_at_cusps' hc := isZeroAt_Γ02_of_W2 (ε := 1) Delta8_slash_Gamma02
    (by simpa using Delta8_slash_W2) Delta8_isZeroAtImInfty hc

private noncomputable def Delta8MF : ModularForm Γ02 8 := Delta8CF

private lemma Delta8_cuspFunction_eqOn :
    Set.EqOn (cuspFunction 1 Delta8)
      (fun q ↦ q * (∏' n : ℕ, (1 - q ^ (n + 1)) ^ 8) * (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) ^ 8))
      (Metric.ball 0 1) := by
  intro q hq
  by_cases hq0 : q = 0
  · subst hq0
    simp only [zero_mul]
    exact Periodic.cuspFunction_zero_of_zero_at_inf one_pos
      Delta8_isZeroAtImInfty.zero_at_infty_comp_ofComplex
  · have him := Periodic.im_invQParam_pos_of_norm_lt_one one_pos
      (by simpa [dist_zero_right] using hq) hq0
    let τ : ℍ := ⟨Periodic.invQParam 1 q, him⟩
    have hqτ : Periodic.qParam 1 τ = q := Periodic.qParam_right_inv one_ne_zero hq0
    have hq2τ : Periodic.qParam 1 (mul2 τ : ℂ) = q ^ 2 := by
      rw [← hqτ]
      simp only [Periodic.qParam, coe_mul2, ofReal_one, div_one, ← Complex.exp_nat_mul]
      congr 1; push_cast; ring
    simp only [cuspFunction, Periodic.cuspFunction_eq_of_nonzero 1 _ hq0, Function.comp_apply,
      ofComplex_apply_of_im_pos him]
    rw [Delta8_eq_q_prod τ]
    simp only [ModularForm.eta_q, hqτ, hq2τ]

/-- Elementary product bound: $\left|\prod_{i \in s} (1 + a_i) - 1\right| \le \exp(\sum_{i \in s} |a_i|) - 1$. -/
private lemma norm_finset_prod_one_add_sub_one_le {ι : Type*} (s : Finset ι) (a : ι → ℂ) :
    ‖(∏ i ∈ s, (1 + a i)) - 1‖ ≤ Real.exp (∑ i ∈ s, ‖a i‖) - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx, Real.exp_add]
    set P := ∏ i ∈ s, (1 + a i)
    set S := ∑ i ∈ s, ‖a i‖
    have hsplit : (1 + a x) * P - 1 = (P - 1) + a x * (P - 1) + a x := by ring
    have h1 : ‖(1 + a x) * P - 1‖ ≤ ‖P - 1‖ + ‖a x‖ * ‖P - 1‖ + ‖a x‖ := by
      rw [hsplit]
      calc ‖(P - 1) + a x * (P - 1) + a x‖
          ≤ ‖(P - 1) + a x * (P - 1)‖ + ‖a x‖ := norm_add_le _ _
        _ ≤ ‖P - 1‖ + ‖a x * (P - 1)‖ + ‖a x‖ := by gcongr; exact norm_add_le _ _
        _ = ‖P - 1‖ + ‖a x‖ * ‖P - 1‖ + ‖a x‖ := by rw [norm_mul]
    have h2 : ‖P - 1‖ + ‖a x‖ * ‖P - 1‖ + ‖a x‖ = (1 + ‖a x‖) * (‖P - 1‖ + 1) - 1 := by ring
    have hexp : 1 + ‖a x‖ ≤ Real.exp ‖a x‖ := by linarith [Real.add_one_le_exp ‖a x‖]
    have hP : ‖P - 1‖ + 1 ≤ Real.exp S := by linarith
    have hmul : (1 + ‖a x‖) * (‖P - 1‖ + 1) ≤ Real.exp ‖a x‖ * Real.exp S :=
      mul_le_mul hexp hP (by positivity) (Real.exp_pos _).le
    linarith

/-- If $f$ is analytic at $0$ and $f(q) = O(\|q\|^{m+1})$ as $q \to 0$, then `iteratedDeriv j f 0 = 0`
for all $j \le m$. -/
private lemma iteratedDeriv_eq_zero_of_isBigO_pow {f : ℂ → ℂ} {m : ℕ}
    (hf : AnalyticAt ℂ f 0)
    (hO : ∃ C > 0, ∀ᶠ q in 𝓝 (0 : ℂ), ‖f q‖ ≤ C * ‖q‖ ^ (m + 1)) :
    ∀ j ≤ m, iteratedDeriv j f 0 = 0 := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun n ↦ iteratedDeriv n f 0 / n.factorial)
  obtain ⟨r, hball⟩ := hf.hasFPowerSeriesAt
  have hr0 : 0 < r := hball.r_pos
  have hcoeff : ∀ j, (j.factorial : ℂ)⁻¹ * iteratedDeriv j f 0 = p.coeff j := fun j => by
    simp [p, FormalMultilinearSeries.coeff_ofScalars, div_eq_inv_mul]
  obtain ⟨r0, hr0pos, hr0lt⟩ : ∃ r0 : ℝ, 0 < r0 ∧ ENNReal.ofReal r0 < r := by
    rcases eq_or_ne r ⊤ with rfl | hrtop
    · exact ⟨1, one_pos, ENNReal.ofReal_lt_top⟩
    · refine ⟨r.toReal / 2, half_pos (ENNReal.toReal_pos hr0.ne' hrtop), ?_⟩
      rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_toReal hrtop, ENNReal.ofReal_ofNat]
      exact ENNReal.half_lt_self hr0.ne' hrtop
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hjm
    have hzero_lt : ∀ i < j, p.coeff i = 0 := fun i hi => by
      rw [← hcoeff i, ih i hi (by omega), mul_zero]
    suffices hpj : p.coeff j = 0 by
      have hc := hcoeff j
      rw [hpj] at hc
      exact (mul_eq_zero.mp hc).resolve_left
        (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)))
    obtain ⟨C, hCpos, hOev⟩ := hO
    rw [Metric.eventually_nhds_iff] at hOev
    obtain ⟨δ, hδ0, hOδ⟩ := hOev
    have hsum_eq : ∀ᶠ q : ℂ in 𝓝 (0 : ℂ),
        f q = q ^ j * (p.coeff j + q * ∑' k : ℕ, p.coeff (k + j + 1) * q ^ k) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr0pos] with q hq
      have hqball : q ∈ Metric.eball (0 : ℂ) r := by
        rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
        exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (mem_ball_zero_iff.mp hq).le) hr0lt
      have hhas := hball.hasSum (by simpa using hqball)
      rw [zero_add] at hhas
      have hhas' : HasSum (fun n : ℕ ↦ p.coeff n * q ^ n) (f q) := by
        refine hhas.congr_fun fun n => ?_
        rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]
      rw [← hasSum_nat_add_iff' (j + 1)] at hhas'
      have hfin : ∑ i ∈ Finset.range (j + 1), p.coeff i * q ^ i = p.coeff j * q ^ j := by
        rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun i hi => by
          rw [hzero_lt i (Finset.mem_range.mp hi), zero_mul]), zero_add]
      rw [hfin] at hhas'
      have hts := hhas'.tsum_eq
      have hts2 : ∑' k : ℕ, p.coeff (k + (j + 1)) * q ^ (k + (j + 1)) =
          q ^ (j + 1) * ∑' k : ℕ, p.coeff (k + j + 1) * q ^ k := by
        rw [← tsum_mul_left]
        refine tsum_congr fun k => ?_
        rw [show k + (j + 1) = k + j + 1 by omega, pow_add]; ring
      rw [hts2] at hts
      linear_combination -hts
    have htend0 : Tendsto (fun q : ℂ ↦ f q / q ^ j) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
      refine ⟨min δ (min 1 (ε / (2 * C))), lt_min hδ0 (lt_min one_pos (by positivity)), fun q hq hq0 => ?_⟩
      have hqδ : dist q 0 < δ := lt_of_lt_of_le hq (min_le_left _ _)
      have hq1 : ‖q‖ < 1 := by
        rw [← dist_zero_right]; exact lt_of_lt_of_le hq ((min_le_right _ _).trans (min_le_left _ _))
      have hqε : ‖q‖ < ε / (2 * C) := by
        rw [← dist_zero_right]; exact lt_of_lt_of_le hq ((min_le_right _ _).trans (min_le_right _ _))
      have hbound := hOδ hqδ
      rw [dist_zero_right, norm_div, norm_pow]
      have hqn : 0 < ‖q‖ := norm_pos_iff.mpr hq0
      have hpow_le : ‖q‖ ^ (m + 1) / ‖q‖ ^ j ≤ ‖q‖ := by
        have h1 : ‖q‖ ^ (m + 1) = ‖q‖ ^ j * ‖q‖ ^ (m + 1 - j) := by
          rw [← pow_add, Nat.add_sub_cancel' (by omega)]
        rw [h1, mul_div_cancel_left₀ _ (pow_ne_zero j hqn.ne')]
        exact pow_le_of_le_one (norm_nonneg _) hq1.le (by omega)
      calc ‖f q‖ / ‖q‖ ^ j
          ≤ C * ‖q‖ ^ (m + 1) / ‖q‖ ^ j := div_le_div_of_nonneg_right hbound (by positivity)
        _ = C * (‖q‖ ^ (m + 1) / ‖q‖ ^ j) := by ring
        _ ≤ C * ‖q‖ := mul_le_mul_of_nonneg_left hpow_le hCpos.le
        _ < C * (ε / (2 * C)) := mul_lt_mul_of_pos_left hqε hCpos
        _ = ε / 2 := by field_simp [hCpos.ne']
        _ < ε := half_lt_self hε
    have htendp : Tendsto (fun q : ℂ ↦ f q / q ^ j) (𝓝[≠] (0 : ℂ)) (𝓝 (p.coeff j)) := by
      have hr2pos : (0 : ℝ) < r0 / 2 := half_pos hr0pos
      have hsumm_all : Summable (fun n : ℕ ↦ ‖p.coeff n‖ * (r0 / 2) ^ n) := by
        let r3 : ℝ := 3 * r0 / 4
        have hr3pos : 0 < r3 := by dsimp [r3]; linarith
        have hr3lt : ENNReal.ofReal r3 < r :=
          lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by dsimp [r3]; linarith)) hr0lt
        have hyball : ((r3 : ℝ) : ℂ) ∈ Metric.eball (0 : ℂ) r := by
          rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, Complex.norm_real,
            Real.norm_of_nonneg hr3pos.le]
          exact hr3lt
        have hs3 : Summable (fun n : ℕ ↦ p n (fun _ => ((r3 : ℝ) : ℂ))) :=
          (hball.hasSum (by simpa using hyball)).summable
        have ht0 := Metric.tendsto_atTop.mp hs3.tendsto_atTop_zero 1 one_pos
        obtain ⟨N, hN⟩ := ht0
        have hgeom : Summable (fun k : ℕ ↦ (2 / 3 : ℝ) ^ (k + N)) :=
          (summable_nat_add_iff N).mpr (summable_geometric_of_lt_one (by norm_num) (by norm_num))
        have htail_s : Summable (fun k : ℕ ↦ ‖p.coeff (k + N)‖ * (r0 / 2) ^ (k + N)) :=
          hgeom.of_nonneg_of_le (fun _ => by positivity) (fun k => by
            have hk := hN (k + N) (Nat.le_add_left N k)
            rw [dist_zero_right, FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul,
              norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr3pos.le] at hk
            have hr_eq : r0 / 2 = r3 * (2 / 3) := by dsimp [r3]; ring
            rw [hr_eq, mul_pow]
            calc ‖p.coeff (k + N)‖ * (r3 ^ (k + N) * (2 / 3) ^ (k + N))
                = (r3 ^ (k + N) * ‖p.coeff (k + N)‖) * (2 / 3) ^ (k + N) := by ring
              _ ≤ 1 * (2 / 3) ^ (k + N) := mul_le_mul_of_nonneg_right hk.le (by positivity)
              _ = (2 / 3) ^ (k + N) := one_mul _)
        exact (summable_nat_add_iff N).mp htail_s
      have hsumm : Summable (fun k : ℕ ↦ ‖p.coeff (k + j + 1)‖ * (r0 / 2) ^ k) := by
        have hsh := (summable_nat_add_iff (j + 1)).mpr hsumm_all
        have hmul := hsh.mul_right ((r0 / 2) ^ (j + 1))⁻¹
        refine hmul.congr fun k => ?_
        rw [pow_add (r0 / 2) k (j + 1), mul_assoc, mul_assoc,
          mul_inv_cancel₀ (pow_ne_zero _ hr2pos.ne'), mul_one,
          show k + (j + 1) = k + j + 1 by omega]
      let M := ∑' k : ℕ, ‖p.coeff (k + j + 1)‖ * (r0 / 2) ^ k
      have hM0 : 0 ≤ M := tsum_nonneg fun k => by positivity
      have htail : Tendsto (fun q : ℂ ↦ p.coeff j + q * ∑' k : ℕ, p.coeff (k + j + 1) * q ^ k)
          (𝓝[≠] (0 : ℂ)) (𝓝 (p.coeff j)) := by
        rw [Metric.tendsto_nhds]
        intro ε hε
        rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
        refine ⟨min (r0 / 2) (ε / (M + 1)), lt_min hr2pos (by positivity), fun q hq _ => ?_⟩
        rw [dist_eq_norm, add_sub_cancel_left, norm_mul]
        have hqr : ‖q‖ ≤ r0 / 2 := by
          rw [← dist_zero_right]; exact (lt_of_lt_of_le hq (min_le_left _ _)).le
        have hqε : ‖q‖ < ε / (M + 1) := by
          rw [← dist_zero_right]; exact lt_of_lt_of_le hq (min_le_right _ _)
        have hdom : Summable (fun k : ℕ ↦ ‖p.coeff (k + j + 1) * q ^ k‖) :=
          hsumm.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => by
            rw [norm_mul, norm_pow]
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hqr k) (norm_nonneg _))
        have hle : ‖∑' k : ℕ, p.coeff (k + j + 1) * q ^ k‖ ≤ M :=
          (norm_tsum_le_tsum_norm hdom).trans <| Summable.tsum_le_tsum (fun k => by
            rw [norm_mul, norm_pow]
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hqr k) (norm_nonneg _))
            hdom hsumm
        calc ‖q‖ * ‖∑' k : ℕ, p.coeff (k + j + 1) * q ^ k‖
            ≤ ‖q‖ * M := mul_le_mul_of_nonneg_left hle (norm_nonneg _)
          _ ≤ ‖q‖ * (M + 1) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
          _ < (ε / (M + 1)) * (M + 1) := mul_lt_mul_of_pos_right hqε (by linarith)
          _ = ε := by field_simp [(by linarith : M + 1 ≠ 0)]
      refine htail.congr' ?_
      filter_upwards [nhdsWithin_le_nhds hsum_eq, self_mem_nhdsWithin] with q hq hq0
      rw [hq, mul_div_cancel_left₀ _ (pow_ne_zero j hq0)]
    exact tendsto_nhds_unique htendp htend0

/-- Helper: `‖u ^ k - 1‖ ≤ (1 + ‖u - 1‖) ^ k - 1`. -/
private lemma norm_pow_sub_one_le (u : ℂ) (k : ℕ) :
    ‖u ^ k - 1‖ ≤ (1 + ‖u - 1‖) ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    have hsp : u ^ k * u - 1 = (u ^ k - 1) + (u ^ k - 1) * (u - 1) + (u - 1) := by ring
    rw [hsp]
    have htri : ‖(u ^ k - 1) + (u ^ k - 1) * (u - 1) + (u - 1)‖ ≤
        ‖u ^ k - 1‖ + ‖u ^ k - 1‖ * ‖u - 1‖ + ‖u - 1‖ := by
      calc ‖(u ^ k - 1) + (u ^ k - 1) * (u - 1) + (u - 1)‖
          ≤ ‖(u ^ k - 1) + (u ^ k - 1) * (u - 1)‖ + ‖u - 1‖ := norm_add_le _ _
        _ ≤ ‖u ^ k - 1‖ + ‖(u ^ k - 1) * (u - 1)‖ + ‖u - 1‖ := by gcongr; exact norm_add_le _ _
        _ = ‖u ^ k - 1‖ + ‖u ^ k - 1‖ * ‖u - 1‖ + ‖u - 1‖ := by rw [norm_mul]
    have hn := norm_nonneg (u - 1)
    nlinarith

/-- Infinite products $\prod_{n \ge 1} (1 - q^{dn})^k$ have integer Taylor coefficients at $0$. -/
private lemma tprod_one_sub_pow_taylor_int (d k : ℕ) (hd : 0 < d) (m : ℕ) :
    ∃ a : ℤ, ((m.factorial : ℂ)⁻¹ *
      iteratedDeriv m (fun q : ℂ ↦ ∏' n : ℕ, (1 - (q ^ d) ^ (n + 1)) ^ k) 0) = a := by
  let g : ℂ → ℂ := fun q => ∏' n : ℕ, (1 - (q ^ d) ^ (n + 1)) ^ k
  let P : Polynomial ℤ := ∏ n ∈ Finset.range (m + 1), (1 - Polynomial.X ^ (d * (n + 1))) ^ k
  let R : ℂ → ℂ := fun q => ∏' n : ℕ, (1 - (q ^ d) ^ (n + m + 2)) ^ k
  have hmul_split : ∀ q ∈ Metric.ball (0 : ℂ) 1,
      g q = (Polynomial.aeval q P) * R q := by
    intro q hq
    have hqn : ‖q ^ d‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp hq) (by omega)
    have htail_mp1 : Multipliable fun n : ℕ ↦ 1 - (q ^ d) ^ ((n + (m + 1)) + 1) := by
      simp_rw [sub_eq_add_neg]
      apply multipliable_one_add_of_summable
      have hgeom := (summable_nat_add_iff (m + 2)).mpr
        (summable_geometric_of_lt_one (norm_nonneg (q ^ d)) hqn)
      exact hgeom.congr fun n => by
        rw [norm_neg, norm_pow (q ^ d), show n + (m + 2) = n + (m + 1) + 1 by omega]
    have htail_mp : Multipliable fun n : ℕ ↦ (1 - (q ^ d) ^ ((n + (m + 1)) + 1)) ^ k :=
      htail_mp1.pow k
    have hsplit : HasProd (fun n : ℕ ↦ (1 - (q ^ d) ^ (n + 1)) ^ k)
        ((∏ n ∈ Finset.range (m + 1), (1 - (q ^ d) ^ (n + 1)) ^ k) *
          ∏' n : ℕ, (1 - (q ^ d) ^ ((n + (m + 1)) + 1)) ^ k) :=
      HasProd.prod_range_mul (f := fun n : ℕ ↦ (1 - (q ^ d) ^ (n + 1)) ^ k) (k := m + 1)
        htail_mp.hasProd
    have ht := hsplit.tprod_eq
    dsimp [g, R]
    rw [ht]
    congr 1
    simp only [P, map_prod, map_pow, map_sub, map_one, Polynomial.aeval_X]
    apply Finset.prod_congr rfl
    intro n _
    rw [pow_mul]
  have hP_ne : ∀ q ∈ Metric.ball (0 : ℂ) (1 / 2), (Polynomial.aeval q P : ℂ) ≠ 0 := by
    intro q hq
    simp only [P, map_prod, map_pow, map_sub, map_one, Polynomial.aeval_X]
    rw [Finset.prod_ne_zero_iff]
    intro n _
    apply pow_ne_zero
    rw [sub_ne_zero]
    intro heq
    have h1 : ‖q ^ (d * (n + 1))‖ = 1 := by rw [← heq, norm_one]
    have h2 : ‖q ^ (d * (n + 1))‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) (lt_trans (mem_ball_zero_iff.mp hq) (by norm_num))
        (Nat.mul_pos hd (Nat.succ_pos n)).ne'
    linarith
  have hg_diff : DifferentiableOn ℂ g (Metric.ball 0 1) := by
    refine (ModularForm.differentiableOn_tprod_one_sub_pow_pow k).comp
      (differentiable_pow d).differentiableOn ?_
    intro q hq
    rw [mem_ball_zero_iff, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp hq) (by omega)
  have hP_diff : DifferentiableOn ℂ (fun q : ℂ ↦ (Polynomial.aeval q P : ℂ)) (Metric.ball 0 1) := by
    have : (fun q : ℂ ↦ (Polynomial.aeval q P : ℂ)) = fun q => (P.map (Int.castRingHom ℂ)).eval q := by
      ext q; simp [Polynomial.aeval_def, Polynomial.eval_map]
    rw [this]
    exact (P.map (Int.castRingHom ℂ)).differentiable.differentiableOn
  have hR_diff : DifferentiableOn ℂ R (Metric.ball 0 (1 / 2)) := by
    have hdiv : DifferentiableOn ℂ (fun q => g q / (Polynomial.aeval q P : ℂ)) (Metric.ball 0 (1 / 2)) :=
      (hg_diff.mono (Metric.ball_subset_ball (by norm_num))).div
        (hP_diff.mono (Metric.ball_subset_ball (by norm_num))) hP_ne
    refine hdiv.congr fun q hq => ?_
    have hq1 : q ∈ Metric.ball (0 : ℂ) 1 := Metric.ball_subset_ball (by norm_num) hq
    rw [hmul_split q hq1, mul_div_cancel_left₀ _ (hP_ne q hq)]
  have hR_ana : AnalyticAt ℂ R 0 :=
    hR_diff.analyticAt (Metric.ball_mem_nhds (0 : ℂ) (by norm_num))
  have hR_O : ∃ C > 0, ∀ᶠ q in 𝓝 (0 : ℂ), ‖R q - 1‖ ≤ C * ‖q‖ ^ (m + 1) := by
    let C : ℝ := (2 * (k : ℝ) + 1) * Real.exp (2 * (k : ℝ) + 1)
    refine ⟨C, by positivity, ?_⟩
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with q hq
    have hq12 : ‖q‖ < 1 / 2 := mem_ball_zero_iff.mp hq
    have hwn : ‖q ^ d‖ ≤ ‖q‖ := by
      rw [norm_pow]; exact pow_le_of_le_one (norm_nonneg _) (by linarith) (by omega)
    have hwl1 : ‖q ^ d‖ < 1 / 2 := lt_of_le_of_lt hwn hq12
    have hmp1 : Multipliable fun n : ℕ ↦ 1 - (q ^ d) ^ (n + m + 2) := by
      simp_rw [sub_eq_add_neg]
      apply multipliable_one_add_of_summable
      have hgeom := (summable_nat_add_iff (m + 2)).mpr
        (summable_geometric_of_lt_one (norm_nonneg (q ^ d)) (lt_trans hwl1 (by norm_num)))
      exact hgeom.congr fun n => by
        rw [norm_neg, norm_pow (q ^ d), show n + (m + 2) = n + m + 2 by omega]
    have hR_pow : R q = (∏' n : ℕ, (1 - (q ^ d) ^ (n + m + 2))) ^ k :=
      hmp1.tprod_pow k
    let S0 : ℝ := ‖q ^ d‖ ^ (m + 2) / (1 - ‖q ^ d‖)
    have hS0_le : S0 ≤ 2 * ‖q‖ ^ (m + 1) := by
      have h1m : 1 / 2 ≤ 1 - ‖q ^ d‖ := by linarith
      have hpow : ‖q ^ d‖ ^ (m + 2) ≤ ‖q‖ ^ (m + 1) := calc
        ‖q ^ d‖ ^ (m + 2) ≤ ‖q‖ ^ (m + 2) := pow_le_pow_left₀ (norm_nonneg _) hwn _
        _ = ‖q‖ ^ (m + 1) * ‖q‖ := pow_succ _ _
        _ ≤ ‖q‖ ^ (m + 1) * 1 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = ‖q‖ ^ (m + 1) := mul_one _
      calc S0 = ‖q ^ d‖ ^ (m + 2) / (1 - ‖q ^ d‖) := rfl
        _ ≤ ‖q ^ d‖ ^ (m + 2) / (1 / 2) := div_le_div_of_nonneg_left (by positivity) (by norm_num) h1m
        _ = 2 * ‖q ^ d‖ ^ (m + 2) := by ring
        _ ≤ 2 * ‖q‖ ^ (m + 1) := by linarith
    have hS0_nonneg : 0 ≤ S0 := div_nonneg (by positivity) (by linarith)
    have hprod_le : ‖(∏' n : ℕ, (1 - (q ^ d) ^ (n + m + 2))) - 1‖ ≤ Real.exp S0 - 1 := by
      have htend : Tendsto (fun N : ℕ ↦ ‖(∏ n ∈ Finset.range N, (1 - (q ^ d) ^ (n + m + 2))) - 1‖)
          atTop (𝓝 ‖(∏' n : ℕ, (1 - (q ^ d) ^ (n + m + 2))) - 1‖) :=
        ((hmp1.hasProd.tendsto_prod_nat).sub tendsto_const_nhds).norm
      refine le_of_tendsto htend (Eventually.of_forall fun N => ?_)
      have hb := norm_finset_prod_one_add_sub_one_le (Finset.range N) (fun n => -(q ^ d) ^ (n + m + 2))
      have heq : (∏ n ∈ Finset.range N, (1 + -(q ^ d) ^ (n + m + 2))) =
          ∏ n ∈ Finset.range N, (1 - (q ^ d) ^ (n + m + 2)) :=
        Finset.prod_congr rfl fun _ _ => by ring
      rw [heq] at hb
      refine hb.trans ?_
      have hsum_le : (∑ n ∈ Finset.range N, ‖-(q ^ d) ^ (n + m + 2)‖) ≤ S0 := by
        have hgs : Summable (fun n : ℕ ↦ ‖q ^ d‖ ^ (m + 2) * ‖q ^ d‖ ^ n) :=
          (summable_geometric_of_lt_one (norm_nonneg _) (lt_trans hwl1 (by norm_num))).mul_left _
        have hts : ∑' n : ℕ, ‖q ^ d‖ ^ (m + 2) * ‖q ^ d‖ ^ n = S0 := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (norm_nonneg _) (lt_trans hwl1 (by norm_num))]
          ring
        rw [← hts]
        calc ∑ n ∈ Finset.range N, ‖-(q ^ d) ^ (n + m + 2)‖
            = ∑ n ∈ Finset.range N, ‖q ^ d‖ ^ (m + 2) * ‖q ^ d‖ ^ n :=
              Finset.sum_congr rfl fun n _ => by
                rw [norm_neg, norm_pow, show n + m + 2 = (m + 2) + n by omega, pow_add]
          _ ≤ ∑' n : ℕ, ‖q ^ d‖ ^ (m + 2) * ‖q ^ d‖ ^ n :=
              hgs.sum_le_tsum (Finset.range N) (fun _ _ => by positivity)
      exact sub_le_sub_right (Real.exp_le_exp.mpr hsum_le) 1
    have hpow_bound : ‖R q - 1‖ ≤ Real.exp ((k : ℝ) * S0) - 1 := by
      rw [hR_pow]
      have h1 := norm_pow_sub_one_le (∏' n : ℕ, (1 - (q ^ d) ^ (n + m + 2))) k
      have h2 : (1 + ‖(∏' n : ℕ, (1 - (q ^ d) ^ (n + m + 2))) - 1‖) ^ k ≤ Real.exp ((k : ℝ) * S0) := by
        calc (1 + ‖(∏' n : ℕ, (1 - (q ^ d) ^ (n + m + 2))) - 1‖) ^ k
            ≤ (Real.exp S0) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
          _ = Real.exp ((k : ℝ) * S0) := by rw [← Real.exp_nat_mul]
      linarith
    have hexp_le : ∀ x : ℝ, Real.exp x - 1 ≤ x * Real.exp x := fun x => by
      have h := Real.add_one_le_exp (-x)
      have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos x).le
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hmul
      linarith
    have hkS0_le : (k : ℝ) * S0 ≤ 2 * (k : ℝ) + 1 := by
      have hqpow1 : ‖q‖ ^ (m + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) (by linarith)
      nlinarith
    calc ‖R q - 1‖
        ≤ Real.exp ((k : ℝ) * S0) - 1 := hpow_bound
      _ ≤ ((k : ℝ) * S0) * Real.exp ((k : ℝ) * S0) := hexp_le _
      _ ≤ ((k : ℝ) * (2 * ‖q‖ ^ (m + 1))) * Real.exp (2 * (k : ℝ) + 1) := by gcongr
      _ ≤ C * ‖q‖ ^ (m + 1) := by
          dsimp [C]
          have : 0 ≤ ‖q‖ ^ (m + 1) * Real.exp (2 * (k : ℝ) + 1) := by positivity
          nlinarith
  have hR_deriv_zero : ∀ j ≤ m, iteratedDeriv j (fun q => R q - 1) 0 = 0 :=
    iteratedDeriv_eq_zero_of_isBigO_pow (hR_ana.sub analyticAt_const) hR_O
  have hR0 : R 0 = 1 := by
    have h0 := hR_deriv_zero 0 (Nat.zero_le m)
    rw [iteratedDeriv_zero] at h0
    exact sub_eq_zero.mp h0
  have hRj : ∀ j, 1 ≤ j → j ≤ m → iteratedDeriv j R 0 = 0 := by
    intro j hj1 hjm
    have h0 := hR_deriv_zero j hjm
    have hsub : iteratedDeriv j (fun q => R q - 1) 0 =
        iteratedDeriv j R 0 - iteratedDeriv j (fun _ : ℂ => (1 : ℂ)) 0 :=
      iteratedDeriv_sub (hR_ana.contDiffAt.of_le le_top) contDiffAt_const
    rw [hsub, iteratedDeriv_const, if_neg (by omega), sub_zero] at h0
    exact h0
  have hEq : g =ᶠ[𝓝 (0 : ℂ)] ((fun q => (Polynomial.aeval q P : ℂ)) * R) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with q hq
    exact hmul_split q hq
  have hP_cd : ContDiffAt ℂ m (fun q : ℂ ↦ (Polynomial.aeval q P : ℂ)) 0 :=
    (hP_diff.analyticAt (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)).contDiffAt.of_le le_top
  have hR_cd : ContDiffAt ℂ m R 0 := hR_ana.contDiffAt.of_le le_top
  have hleib : iteratedDeriv m g 0 = iteratedDeriv m (fun q : ℂ ↦ (Polynomial.aeval q P : ℂ)) 0 := by
    rw [hEq.iteratedDeriv_eq, iteratedDeriv_mul hP_cd hR_cd]
    rw [Finset.sum_eq_single m]
    · simp [hR0]
    · intro i hi hne
      have him : i < m := by have := Finset.mem_range.mp hi; omega
      rw [hRj (m - i) (by omega) (by omega), mul_zero]
    · intro hnot; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self m)) hnot
  refine ⟨P.coeff m, ?_⟩
  change (m.factorial : ℂ)⁻¹ * iteratedDeriv m g 0 = (P.coeff m : ℂ)
  rw [hleib]
  have hpoly : ∀ Q : Polynomial ℤ, ∀ n : ℕ,
      (n.factorial : ℂ)⁻¹ * iteratedDeriv n (fun q : ℂ ↦ (Polynomial.aeval q Q : ℂ)) 0 = (Q.coeff n : ℂ) := by
    intro Q n
    have hmap : (fun q : ℂ ↦ (Polynomial.aeval q Q : ℂ)) = fun q => (Q.map (Int.castRingHom ℂ)).eval q := by
      ext q; simp [Polynomial.aeval_def, Polynomial.eval_map]
    rw [hmap]
    have hiter : ∀ k : ℕ, ∀ R0 : Polynomial ℂ,
        iteratedDeriv k (fun q : ℂ ↦ R0.eval q) 0 = (Polynomial.derivative^[k] R0).eval 0 := by
      intro k
      induction k with
      | zero => intro R0; simp
      | succ k ih =>
        intro R0
        rw [iteratedDeriv_succ', Function.iterate_succ_apply]
        have hd : deriv (fun q : ℂ ↦ R0.eval q) = fun q => (Polynomial.derivative R0).eval q := by
          ext q; exact Polynomial.deriv R0
        rw [hd, ih]
    rw [hiter n (Q.map (Int.castRingHom ℂ)), ← Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.coeff_iterate_derivative, zero_add, Nat.descFactorial_self,
      Polynomial.coeff_map, Int.coe_castRingHom, nsmul_eq_mul]
    field_simp [Nat.factorial_ne_zero]
  exact hpoly P m

private lemma Delta8_qExpansion_coeff_zero :
    (qExpansion 1 (Delta8MF : ℍ → ℂ)).coeff 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero Delta8CF one_pos one_mem_strictPeriods_Γ02

private lemma Delta8_qExpansion_coeff_one :
    (qExpansion 1 (Delta8MF : ℍ → ℂ)).coeff 1 = 1 := by
  have hmem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := Metric.mem_ball_self one_pos
  have h1 : DifferentiableOn ℂ (fun q : ℂ ↦ ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 8) (Metric.ball 0 1) :=
    ModularForm.differentiableOn_tprod_one_sub_pow_pow 8
  have h2 : DifferentiableOn ℂ (fun q : ℂ ↦ ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) ^ 8) (Metric.ball 0 1) := by
    refine h1.comp (differentiable_pow 2).differentiableOn fun q hq => ?_
    rw [mem_ball_zero_iff, norm_pow]; exact pow_lt_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp hq) two_ne_zero
  calc (qExpansion 1 (Delta8MF : ℍ → ℂ)).coeff 1
      = derivWithin (cuspFunction 1 Delta8) (Metric.ball 0 1) 0 := by
        rw [show (Delta8MF : ℍ → ℂ) = Delta8 from rfl]
        simp [qExpansion_coeff, ← derivWithin_of_isOpen Metric.isOpen_ball hmem]
    _ = derivWithin (fun q : ℂ ↦ q * (∏' n : ℕ, (1 - q ^ (n + 1)) ^ 8) *
          (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) ^ 8)) (Metric.ball 0 1) 0 :=
        derivWithin_congr Delta8_cuspFunction_eqOn (Delta8_cuspFunction_eqOn hmem)
    _ = 1 := by
        let G : ℂ → ℂ := fun q => (∏' n : ℕ, (1 - q ^ (n + 1)) ^ 8) *
            (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) ^ 8)
        have hGdiff : DifferentiableWithinAt ℂ G (Metric.ball 0 1) 0 := (h1.mul h2) 0 hmem
        have hprod_eq : (fun q : ℂ ↦ q * (∏' n : ℕ, (1 - q ^ (n + 1)) ^ 8) *
            (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) ^ 8)) = fun q : ℂ ↦ q * G q := by
          ext q; dsimp [G]; ring
        rw [hprod_eq, derivWithin_fun_mul differentiableWithinAt_fun_id hGdiff,
          derivWithin_id' _ _ (Metric.isOpen_ball.uniqueDiffWithinAt hmem)]
        simp [G]

private lemma Delta8_qExpansion_int (m : ℕ) :
    ∃ a : ℤ, (qExpansion 1 (Delta8MF : ℍ → ℂ)).coeff m = a := by
  let f1 : ℂ → ℂ := fun q => ∏' n : ℕ, (1 - (q ^ 1) ^ (n + 1)) ^ 8
  let f2 : ℂ → ℂ := fun q => ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) ^ 8
  have hf1_ana : AnalyticAt ℂ f1 0 :=
    ((ModularForm.differentiableOn_tprod_one_sub_pow_pow 8).congr fun q _ => by simp [f1]).analyticAt
      (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
  have hf2_ana : AnalyticAt ℂ f2 0 := by
    have hd : DifferentiableOn ℂ f2 (Metric.ball 0 1) :=
      (ModularForm.differentiableOn_tprod_one_sub_pow_pow 8).comp
        (differentiable_pow 2).differentiableOn fun q hq => by
          rw [mem_ball_zero_iff, norm_pow]
          exact pow_lt_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp hq) two_ne_zero
    exact hd.analyticAt (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
  have hEq : cuspFunction 1 Delta8 =ᶠ[𝓝 (0 : ℂ)] ((id : ℂ → ℂ) * (f1 * f2)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with q hq
    simpa [f1, f2, mul_assoc] using Delta8_cuspFunction_eqOn hq
  cases m with
  | zero => exact ⟨0, by simp [Delta8_qExpansion_coeff_zero]⟩
  | succ m =>
    have hcoeff : (qExpansion 1 (Delta8MF : ℍ → ℂ)).coeff (m + 1) =
        ((m.factorial : ℂ)⁻¹ * iteratedDeriv m (f1 * f2) 0) := by
      rw [qExpansion_coeff]
      change (((m + 1).factorial : ℂ)⁻¹ * iteratedDeriv (m + 1) (cuspFunction 1 Delta8) 0) = _
      rw [hEq.iteratedDeriv_eq]
      have hprod_cd : ContDiffAt ℂ (m + 1) (f1 * f2) 0 :=
        (hf1_ana.mul hf2_ana).contDiffAt.of_le le_top
      rw [iteratedDeriv_mul contDiffAt_id hprod_cd]
      rw [Finset.sum_eq_single 1]
      · simp only [Nat.choose_one_right, iteratedDeriv_one, deriv_id, Nat.add_sub_cancel,
          Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        field_simp [Nat.factorial_ne_zero]
      · intro i hi hne
        rcases i with _ | _ | i
        · simp
        · exact absurd rfl hne
        · have : iteratedDeriv (i + 2) (id : ℂ → ℂ) 0 = 0 := by
            rw [iteratedDeriv_succ', deriv_id', iteratedDeriv_const, if_neg (by omega)]
          simp [this]
      · intro hnot; exact absurd (Finset.mem_range.mpr (Nat.succ_lt_succ (Nat.succ_pos m))) hnot
    rw [hcoeff, iteratedDeriv_mul (hf1_ana.contDiffAt.of_le le_top) (hf2_ana.contDiffAt.of_le le_top)]
    have hsum : ((m.factorial : ℂ)⁻¹ * ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℂ) * iteratedDeriv i f1 0 * iteratedDeriv (m - i) f2 0) =
        ∑ i ∈ Finset.range (m + 1),
          ((i.factorial : ℂ)⁻¹ * iteratedDeriv i f1 0) *
          (((m - i).factorial : ℂ)⁻¹ * iteratedDeriv (m - i) f2 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [Nat.cast_choose (K := ℂ) him]
      field_simp [Nat.factorial_ne_zero]
    rw [hsum]
    have hterm : ∀ i ∈ Finset.range (m + 1), ∃ a : ℤ,
        ((i.factorial : ℂ)⁻¹ * iteratedDeriv i f1 0) *
          (((m - i).factorial : ℂ)⁻¹ * iteratedDeriv (m - i) f2 0) = a := by
      intro i _
      obtain ⟨a1, ha1⟩ := tprod_one_sub_pow_taylor_int 1 8 one_pos i
      obtain ⟨a2, ha2⟩ := tprod_one_sub_pow_taylor_int 2 8 two_pos (m - i)
      exact ⟨a1 * a2, by rw [ha1, ha2, Int.cast_mul]⟩
    choose a ha using hterm
    refine ⟨∑ i ∈ (Finset.range (m + 1)).attach, a i.1 i.2, ?_⟩
    rw [Int.cast_sum, ← Finset.sum_attach (Finset.range (m + 1))]
    exact Finset.sum_congr rfl fun i _ => ha i.1 i.2

/-- Divide a `W2`-eigenform on `Γ0(2)` that vanishes at `i∞` by `Δ8`. -/
private noncomputable def divDelta8 {k : ℤ} (f : ModularForm Γ02 k) (ε : ℂ)
    (hW : (f : ℍ → ℂ) ∣[k] W2 = ε • (f : ℍ → ℂ))
    (h0 : (qExpansion 1 (f : ℍ → ℂ)).coeff 0 = 0) : ModularForm Γ02 (k - 8) := by
  have hf_per : Periodic ((f : ℍ → ℂ) ∘ ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_Γ02
  have hf_ana : AnalyticAt ℂ (cuspFunction 1 (f : ℍ → ℂ)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_Γ02
  have hval0 : valueAtInfty (f : ℍ → ℂ) = 0 := by
    rw [← UpperHalfPlane.qExpansion_coeff_zero one_pos hf_ana hf_per]
    exact h0
  have hf_zero : IsZeroAtImInfty (f : ℍ → ℂ) := by
    have hdec := UpperHalfPlane.exp_decay_sub_atImInfty one_pos hf_per f.holo' (ModularFormClass.bdd_at_infty f)
    rw [hval0] at hdec
    simp only [sub_zero, div_one] at hdec
    have ht0 : Tendsto (fun τ : ℍ ↦ Real.exp (-2 * π * τ.im)) atImInfty (𝓝 0) := by
      have : Tendsto (fun τ : ℍ ↦ -2 * π * τ.im) atImInfty atBot := by
        have h1 : Tendsto (fun τ : ℍ ↦ τ.im) atImInfty atTop := tendsto_comap
        have h2 : (-2 * π : ℝ) < 0 := by linarith [Real.pi_pos]
        exact Tendsto.const_mul_atTop_of_neg h2 h1
      exact Real.tendsto_exp_atBot.comp this
    exact hdec.trans_tendsto ht0
  have hf_decay : (f : ℍ → ℂ) =O[atImInfty] Delta8 :=
    (hf_zero.exp_decay_atImInfty one_pos hf_per f.holo' (ModularFormClass.bdd_at_infty f)).trans
      (by simpa [div_one] using exp_isBigO_Delta8)
  have hdiv_slash_Γ : ∀ γ ∈ CongruenceSubgroup.Gamma0 2,
      (fun τ : ℍ ↦ f τ / Delta8 τ) ∣[k - 8] γ = fun τ ↦ f τ / Delta8 τ := by
    intro γ hγ
    change ((f : ℍ → ℂ) / Delta8) ∣[k - 8] γ = (f : ℍ → ℂ) / Delta8
    have hmem : mapGL ℝ γ ∈ Γ02 := ⟨γ, hγ, rfl⟩
    have hfγ : (f : ℍ → ℂ) ∣[k] γ = (f : ℍ → ℂ) :=
      SlashInvariantFormClass.slash_action_eq f (mapGL ℝ γ) hmem
    rw [ModularForm.div_slash_SL2, hfγ, Delta8_slash_Gamma02 γ hγ]
  have hdiv_slash_W2 : (fun τ : ℍ ↦ f τ / Delta8 τ) ∣[k - 8] W2 =
      ε • (fun τ : ℍ ↦ f τ / Delta8 τ) := by
    ext τ
    have hfW := congrFun hW τ
    have hdW := congrFun Delta8_slash_W2 τ
    simp only [ModularForm.slash_apply, σ_W2, W2_det_val, abs_one, Complex.ofReal_one, one_zpow,
      mul_one, Pi.smul_apply, smul_eq_mul] at hfW hdW ⊢
    have hdz : denom W2 τ ≠ 0 := UpperHalfPlane.denom_ne_zero W2 τ
    have hpow : denom W2 τ ^ (-(k - 8)) = denom W2 τ ^ (-k) / denom W2 τ ^ (-8 : ℤ) := by
      rw [← zpow_sub₀ hdz]; congr 1; ring
    rw [hpow]
    calc f (W2 • τ) / Delta8 (W2 • τ) * (denom W2 τ ^ (-k) / denom W2 τ ^ (-8 : ℤ))
        = (f (W2 • τ) * denom W2 τ ^ (-k)) / (Delta8 (W2 • τ) * denom W2 τ ^ (-8 : ℤ)) := by ring
      _ = (ε * f τ) / Delta8 τ := by rw [hfW, hdW]
      _ = ε * (f τ / Delta8 τ) := by ring
  have hdiv_bdd : IsBoundedAtImInfty (fun τ : ℍ ↦ f τ / Delta8 τ) := by
    rw [Asymptotics.isBigO_iff] at hf_decay
    obtain ⟨C, hC⟩ := hf_decay
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [hC] with τ hτ
    rw [norm_div, Pi.one_apply, norm_one, mul_one]
    exact (div_le_iff₀ (norm_pos_iff.mpr (Delta8_ne_zero τ))).mpr hτ
  exact {
    toFun := fun τ => f τ / Delta8 τ
    slash_action_eq' := by rintro _ ⟨γ, hγ, rfl⟩; exact hdiv_slash_Γ γ hγ
    holo' := f.holo'.div Delta8_mdiff Delta8_ne_zero
    bdd_at_cusps' := isBoundedAt_Γ02_of_W2 hdiv_slash_Γ hdiv_slash_W2 hdiv_bdd }

private lemma divDelta8_slash_W2 {k : ℤ} (f : ModularForm Γ02 k) (ε : ℂ)
    (hW : (f : ℍ → ℂ) ∣[k] W2 = ε • (f : ℍ → ℂ))
    (h0 : (qExpansion 1 (f : ℍ → ℂ)).coeff 0 = 0) :
    ((divDelta8 f ε hW h0 : ModularForm Γ02 (k - 8)) : ℍ → ℂ) ∣[k - 8] W2 =
      ε • ((divDelta8 f ε hW h0 : ModularForm Γ02 (k - 8)) : ℍ → ℂ) := by
  ext τ
  have hfW := congrFun hW τ
  have hdW := congrFun Delta8_slash_W2 τ
  change ((fun τ => f τ / Delta8 τ) ∣[k - 8] W2) τ = ε * (f τ / Delta8 τ)
  simp only [ModularForm.slash_apply, σ_W2, W2_det_val, abs_one, Complex.ofReal_one, one_zpow,
    mul_one, Pi.smul_apply, smul_eq_mul] at hfW hdW ⊢
  have hdz : denom W2 τ ≠ 0 := UpperHalfPlane.denom_ne_zero W2 τ
  have hpow : denom W2 τ ^ (-(k - 8)) = denom W2 τ ^ (-k) / denom W2 τ ^ (-8 : ℤ) := by
    rw [← zpow_sub₀ hdz]; congr 1; ring
  rw [hpow]
  calc f (W2 • τ) / Delta8 (W2 • τ) * (denom W2 τ ^ (-k) / denom W2 τ ^ (-8 : ℤ))
      = (f (W2 • τ) * denom W2 τ ^ (-k)) / (Delta8 (W2 • τ) * denom W2 τ ^ (-8 : ℤ)) := by ring
    _ = (ε * f τ) / Delta8 τ := by rw [hfW, hdW]
    _ = ε * (f τ / Delta8 τ) := by ring

private lemma Delta8_mul_divDelta8 {k : ℤ} (f : ModularForm Γ02 k) (ε : ℂ)
    (hW : (f : ℍ → ℂ) ∣[k] W2 = ε • (f : ℍ → ℂ))
    (h0 : (qExpansion 1 (f : ℍ → ℂ)).coeff 0 = 0) (τ : ℍ) :
    Delta8 τ * (divDelta8 f ε hW h0) τ = f τ :=
  mul_div_cancel₀ (f τ) (Delta8_ne_zero τ)

/-- Power series integrality helper: if `f` and `g` have coefficients in `d * ℤ` and `ℤ` respectively
with `g.coeff 0 = 0` and `g.coeff 1 = 1`, and `f = g * h`, then `h` has coefficients in `d * ℤ`. -/
private lemma powerSeries_div_dvd_int {d : ℤ} {f g h : PowerSeries ℂ}
    (hf : ∀ m, ∃ a : ℤ, f.coeff m = (d : ℂ) * a)
    (hg : ∀ m, ∃ b : ℤ, g.coeff m = b)
    (hg0 : g.coeff 0 = 0) (hg1 : g.coeff 1 = 1)
    (hfg : f = g * h) :
    ∀ m, ∃ a : ℤ, h.coeff m = (d : ℂ) * a := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    have hcm := congrArg (PowerSeries.coeff (m + 1)) hfg
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hcm
    have hsplit : ∑ i ∈ Finset.range (m + 2), g.coeff i * h.coeff (m + 1 - i) =
        h.coeff m + ∑ i ∈ Finset.Ico 2 (m + 2), g.coeff i * h.coeff (m + 1 - i) := by
      rw [Finset.sum_range_eq_add_Ico _ (by omega : 0 < m + 2), hg0, zero_mul, zero_add]
      have h1 : Finset.Ico 1 (m + 2) = insert 1 (Finset.Ico 2 (m + 2)) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [h1, Finset.sum_insert (by simp), hg1, one_mul, Nat.add_sub_cancel]
    rw [hsplit] at hcm
    obtain ⟨af, haf⟩ := hf (m + 1)
    have htail : ∀ i ∈ Finset.Ico 2 (m + 2), ∃ a : ℤ, g.coeff i * h.coeff (m + 1 - i) = (d : ℂ) * a := by
      intro i hi
      have hi' := Finset.mem_Ico.mp hi
      obtain ⟨bi, hbi⟩ := hg i
      obtain ⟨ai, hai⟩ := ih (m + 1 - i) (by omega)
      exact ⟨bi * ai, by rw [hbi, hai, Int.cast_mul]; ring⟩
    choose at_ hat using htail
    refine ⟨af - ∑ i ∈ (Finset.Ico 2 (m + 2)).attach, at_ i.1 i.2, ?_⟩
    have hsum_eq : ∑ i ∈ Finset.Ico 2 (m + 2), g.coeff i * h.coeff (m + 1 - i) =
        (d : ℂ) * ((∑ i ∈ (Finset.Ico 2 (m + 2)).attach, at_ i.1 i.2 : ℤ) : ℂ) := by
      rw [Int.cast_sum, Finset.mul_sum, ← Finset.sum_attach (Finset.Ico 2 (m + 2))]
      exact Finset.sum_congr rfl fun i _ => hat i.1 i.2
    rw [Int.cast_sub]
    linear_combination haf - hcm - hsum_eq

/-- Power series product preserves `d * ℤ` coefficients. -/
private lemma powerSeries_mul_dvd_int {d : ℤ} {f g : PowerSeries ℂ}
    (hf : ∀ m, ∃ a : ℤ, f.coeff m = (d : ℂ) * a)
    (hg : ∀ m, ∃ b : ℤ, g.coeff m = b) :
    ∀ m, ∃ a : ℤ, (f * g).coeff m = (d : ℂ) * a := by
  intro m
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hterm : ∀ i ∈ Finset.range (m + 1), ∃ a : ℤ, f.coeff i * g.coeff (m - i) = (d : ℂ) * a := by
    intro i _
    obtain ⟨a1, ha1⟩ := hf i
    obtain ⟨b2, hb2⟩ := hg (m - i)
    exact ⟨a1 * b2, by rw [ha1, hb2, Int.cast_mul]; ring⟩
  choose at_ hat using hterm
  refine ⟨∑ i ∈ (Finset.range (m + 1)).attach, at_ i.1 i.2, ?_⟩
  rw [Int.cast_sum, Finset.mul_sum, ← Finset.sum_attach (Finset.range (m + 1))]
  exact Finset.sum_congr rfl fun i _ => hat i.1 i.2

private lemma E2starMF_pow_qExpansion_int (N : ℕ) (m : ℕ) :
    ∃ a : ℤ, (qExpansion 1 ((E2starMF.pow N : ModularForm Γ02 (N * 2)) : ℍ → ℂ)).coeff m = a := by
  rw [ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_Γ02]
  induction N generalizing m with
  | zero =>
    rw [pow_zero]
    by_cases hm : m = 0
    · subst hm; exact ⟨1, by simp⟩
    · exact ⟨0, by simp [PowerSeries.coeff_one, hm]⟩
  | succ N ih =>
    rw [pow_succ]
    have h1 := powerSeries_mul_dvd_int (d := 1) (f := (qExpansion 1 (E2starMF : ℍ → ℂ)) ^ N)
      (g := qExpansion 1 (E2starMF : ℍ → ℂ))
      (fun k => by obtain ⟨a, ha⟩ := ih k; exact ⟨a, by simpa using ha⟩)
      (fun k => ⟨e2starCoeff k, E2star_qExpansion_coeff k⟩) m
    obtain ⟨a, ha⟩ := h1
    exact ⟨a, by simpa using ha⟩

private lemma E2star_pow_slash_W2 (N : ℕ) :
    (fun τ : ℍ ↦ E2star τ ^ N) ∣[(2 * (N : ℤ))] W2 =
      ((-1 : ℂ) ^ N) • (fun τ : ℍ ↦ E2star τ ^ N) := by
  ext τ
  have h1 := congrFun E2star_slash_W2 τ
  have hW1 : (E2star ∣[(2 : ℤ)] W2) τ = E2star (W2 • τ) * (2 * (τ : ℂ) ^ 2)⁻¹ := by
    simpa using slash_W2_even 1 E2star τ
  rw [hW1, Pi.neg_apply] at h1
  rw [slash_W2_even (N : ℤ) (fun z => E2star z ^ N) τ]
  simp only [Pi.smul_apply, smul_eq_mul, zpow_neg, zpow_natCast]
  rw [← inv_pow, ← mul_pow, h1, neg_eq_neg_one_mul, mul_pow]

/-- **Structure theorem for $M_{2N}(\Gamma_0(2))$ with $W_2$-eigenvalue $(-1)^N$:**
Every such form equals $\sum_{j=0}^{\lfloor N/4 \rfloor} c_j \Delta_8^j E_2^{*N-4j}$, and if all
$q$-expansion coefficients are integer multiples of $d \in \mathbb{Z}$, then so are all $c_j$. -/
private theorem structure_Gamma02_dvd (N : ℕ) (d : ℤ) (f : ModularForm Γ02 (2 * (N : ℤ)))
    (hW : (f : ℍ → ℂ) ∣[2 * (N : ℤ)] W2 = ((-1 : ℂ) ^ N) • (f : ℍ → ℂ))
    (hd : ∀ m, ∃ a : ℤ, (qExpansion 1 (f : ℍ → ℂ)).coeff m = (d : ℂ) * a) :
    ∃ c : ℕ → ℤ,
      ∀ τ : ℍ, f τ = ∑ j ∈ Finset.range (N / 4 + 1),
        ((d : ℂ) * (c j : ℂ)) * Delta8 τ ^ j * E2star τ ^ (N - 4 * j) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    obtain ⟨c0, hc0⟩ := hd 0
    let eN : ModularForm Γ02 (2 * (N : ℤ)) :=
      ModularForm.mcast (by ring) (E2starMF.pow N)
    let g : ModularForm Γ02 (2 * (N : ℤ)) := f - ((d : ℂ) * (c0 : ℂ)) • eN
    have heN_coe : (eN : ℍ → ℂ) = fun τ => E2star τ ^ N := by
      ext τ; simp [eN, ModularForm.coe_pow]; rfl
    have heN_W : (eN : ℍ → ℂ) ∣[2 * (N : ℤ)] W2 = ((-1 : ℂ) ^ N) • (eN : ℍ → ℂ) := by
      rw [heN_coe]; exact E2star_pow_slash_W2 N
    have hg_W : (g : ℍ → ℂ) ∣[2 * (N : ℤ)] W2 = ((-1 : ℂ) ^ N) • (g : ℍ → ℂ) := by
      change ((f : ℍ → ℂ) - ((d : ℂ) * (c0 : ℂ)) • (eN : ℍ → ℂ)) ∣[2 * (N : ℤ)] W2 = _
      rw [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ModularForm.smul_slash,
        hW, heN_W, σ_W2, smul_comm]
      ext τ
      simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
      change (-1 : ℂ) ^ N * f τ + -((-1 : ℂ) ^ N * (((d : ℂ) * (c0 : ℂ)) * eN τ)) =
        (-1 : ℂ) ^ N * (f τ - ((d : ℂ) * (c0 : ℂ)) * eN τ)
      ring
    have hg_qExp : qExpansion 1 (g : ℍ → ℂ) =
        qExpansion 1 (f : ℍ → ℂ) - ((d : ℂ) * (c0 : ℂ)) • qExpansion 1 (eN : ℍ → ℂ) := by
      have h1 : (g : ℍ → ℂ) = (f : ℍ → ℂ) - (((d : ℂ) * (c0 : ℂ)) • eN : ModularForm Γ02 _) := rfl
      have h2 : ((((d : ℂ) * (c0 : ℂ)) • eN : ModularForm Γ02 _) : ℍ → ℂ) =
          ((d : ℂ) * (c0 : ℂ)) • (eN : ℍ → ℂ) := rfl
      rw [h1, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_Γ02, h2,
        ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_Γ02]
    have heN_q0 : (qExpansion 1 (eN : ℍ → ℂ)).coeff 0 = 1 := by
      have hq : qExpansion 1 (eN : ℍ → ℂ) = (qExpansion 1 (E2starMF : ℍ → ℂ)) ^ N := by
        simpa [eN] using ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_Γ02 E2starMF N
      rw [hq, PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
        ← PowerSeries.coeff_zero_eq_constantCoeff, E2star_qExpansion_coeff 0]
      simp [e2starCoeff]
    have hg_q0 : (qExpansion 1 (g : ℍ → ℂ)).coeff 0 = 0 := by
      rw [hg_qExp, map_sub, PowerSeries.coeff_smul, hc0, heN_q0, smul_eq_mul, mul_one, sub_self]
    have hg_dvd : ∀ m, ∃ a : ℤ, (qExpansion 1 (g : ℍ → ℂ)).coeff m = (d : ℂ) * a := by
      intro m
      rw [hg_qExp, map_sub, PowerSeries.coeff_smul, smul_eq_mul]
      obtain ⟨af, haf⟩ := hd m
      obtain ⟨ae, hae⟩ := E2starMF_pow_qExpansion_int N m
      have hae' : (qExpansion 1 (eN : ℍ → ℂ)).coeff m = ae := by simpa [eN] using hae
      exact ⟨af - c0 * ae, by rw [haf, hae', Int.cast_sub, Int.cast_mul]; ring⟩
    let qg : ModularForm Γ02 (2 * (N : ℤ) - 8) := divDelta8 g ((-1 : ℂ) ^ N) hg_W hg_q0
    by_cases hN4 : N < 4
    · have hqg0 : qg = 0 := ModularForm.isZero_of_neg_weight (by omega) qg
      refine ⟨fun j => if j = 0 then c0 else 0, fun τ => ?_⟩
      have hdiv0 : N / 4 = 0 := Nat.div_eq_of_lt hN4
      rw [hdiv0, Finset.range_one, Finset.sum_singleton]
      simp only [↓reduceIte, pow_zero, mul_one, Nat.mul_zero, Nat.sub_zero]
      have hg0 : g τ = 0 := by
        have := Delta8_mul_divDelta8 g ((-1 : ℂ) ^ N) hg_W hg_q0 τ
        rw [show divDelta8 g ((-1 : ℂ) ^ N) hg_W hg_q0 = qg from rfl, hqg0] at this
        simpa using this.symm
      change f τ - (d : ℂ) * (c0 : ℂ) * eN τ = 0 at hg0
      rw [heN_coe] at hg0
      exact sub_eq_zero.mp hg0
    · have hNge : 4 ≤ N := Nat.le_of_not_lt hN4
      have hwt : 2 * (N : ℤ) - 8 = 2 * ((N - 4 : ℕ) : ℤ) := by omega
      let qg' : ModularForm Γ02 (2 * ((N - 4 : ℕ) : ℤ)) := ModularForm.mcast hwt qg
      have hqg'_W : (qg' : ℍ → ℂ) ∣[2 * ((N - 4 : ℕ) : ℤ)] W2 =
          ((-1 : ℂ) ^ (N - 4)) • (qg' : ℍ → ℂ) := by
        have h : (qg : ℍ → ℂ) ∣[2 * (N : ℤ) - 8] W2 = ((-1 : ℂ) ^ N) • (qg : ℍ → ℂ) :=
          divDelta8_slash_W2 g ((-1 : ℂ) ^ N) hg_W hg_q0
        have hsign : (-1 : ℂ) ^ N = (-1 : ℂ) ^ (N - 4) := by
          rw [show N = (N - 4) + 4 by omega, pow_add]; norm_num
        have hcoe : (qg' : ℍ → ℂ) = (qg : ℍ → ℂ) := rfl
        rw [hcoe, ← hwt, h, hsign]
      have hqg'_dvd : ∀ m, ∃ a : ℤ, (qExpansion 1 (qg' : ℍ → ℂ)).coeff m = (d : ℂ) * a := by
        have hmul : qExpansion 1 (g : ℍ → ℂ) =
            qExpansion 1 (Delta8MF : ℍ → ℂ) * qExpansion 1 (qg' : ℍ → ℂ) := by
          have hfn : (g : ℍ → ℂ) = (Delta8MF : ℍ → ℂ) * (qg' : ℍ → ℂ) := by
            ext τ
            exact (Delta8_mul_divDelta8 g ((-1 : ℂ) ^ N) hg_W hg_q0 τ).symm
          rw [hfn]
          exact ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_Γ02 Delta8MF qg'
        exact powerSeries_div_dvd_int hg_dvd Delta8_qExpansion_int
          Delta8_qExpansion_coeff_zero Delta8_qExpansion_coeff_one hmul
      obtain ⟨c', hc'⟩ := ih (N - 4) (by omega) qg' hqg'_W hqg'_dvd
      refine ⟨fun j => if j = 0 then c0 else c' (j - 1), fun τ => ?_⟩
      have hdiv : N / 4 + 1 = ((N - 4) / 4 + 1) + 1 := by omega
      rw [hdiv, Finset.sum_range_succ']
      simp only [↓reduceIte, pow_zero, mul_one, Nat.mul_zero, Nat.sub_zero, Nat.add_eq_zero_iff,
        one_ne_zero, and_false, Nat.add_sub_cancel]
      have htail : ∑ k ∈ Finset.range ((N - 4) / 4 + 1),
          ((d : ℂ) * (c' k : ℂ)) * Delta8 τ ^ (k + 1) * E2star τ ^ (N - 4 * (k + 1)) =
          Delta8 τ * qg' τ := by
        rw [hc' τ, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [pow_succ, show N - 4 * (k + 1) = (N - 4) - 4 * k by omega]
        ring
      rw [htail]
      have hmulτ : Delta8 τ * qg' τ = g τ := Delta8_mul_divDelta8 g ((-1 : ℂ) ^ N) hg_W hg_q0 τ
      rw [hmulτ]
      have hgval : g τ = f τ - (d : ℂ) * (c0 : ℂ) * E2star τ ^ N := by
        change f τ - (d : ℂ) * (c0 : ℂ) * eN τ = _
        rw [heN_coe]
      rw [hgval]; ring

end ModularGamma02

/- ### Section 3: Ramanujan ODEs and the Picard-Fuchs congruence modulo `(p^2, q^p)` -/

section RamanujanODEs
open UpperHalfPlane hiding I
open Complex Filter Function ModularForm ModularGroup CongruenceSubgroup EisensteinSeries
open Matrix.SpecialLinearGroup
open scoped Real Topology Manifold MatrixGroups ModularForm ArithmeticFunction.sigma

private noncomputable abbrev nD : (ℍ → ℂ) → (ℍ → ℂ) := Derivative.normalizedDerivOfComplex

private lemma qParam_one_eq_cexp (z : ℂ) : Periodic.qParam 1 z = cexp (2 * π * I * z) := by
  simp [Periodic.qParam]

private lemma nD_eq_q_deriv_cuspFunction {f : ℍ → ℂ}
    (hf_per : Periodic (f ∘ ofComplex) 1) (hf_hol : MDiff f) (hf_bdd : IsBoundedAtImInfty f)
    (τ : ℍ) :
    nD f τ = Periodic.qParam 1 τ * deriv (cuspFunction 1 f) (Periodic.qParam 1 τ) := by
  let g : ℂ → ℂ := cuspFunction 1 f
  have hg_diff : DifferentiableOn ℂ g (Metric.ball 0 1) :=
    UpperHalfPlane.differentiableOn_cuspFunction_ball one_pos hf_per hf_hol hf_bdd
  have hq_mem : Periodic.qParam 1 τ ∈ Metric.ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    exact Periodic.norm_qParam_lt_one one_pos τ.im_pos
  have hg_at : HasDerivAt g (deriv g (Periodic.qParam 1 τ)) (Periodic.qParam 1 τ) :=
    (hg_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hq_mem)).hasDerivAt
  have hq_at : HasDerivAt (Periodic.qParam 1) (2 * π * I * Periodic.qParam 1 τ) (τ : ℂ) := by
    have hfun : Periodic.qParam 1 = fun z : ℂ ↦ cexp ((2 * π * I) * z) := by
      ext z; exact qParam_one_eq_cexp z
    rw [hfun]
    have h1 : HasDerivAt (fun z : ℂ ↦ (2 * π * I) * z) (2 * π * I) (τ : ℂ) := by
      simpa using (hasDerivAt_id (τ : ℂ)).const_mul (2 * π * I)
    simpa [mul_comm, qParam_one_eq_cexp] using h1.cexp
  have hcomp : (f ∘ ofComplex) =ᶠ[𝓝 (τ : ℂ)] (g ∘ Periodic.qParam 1) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
    have hEq := UpperHalfPlane.eq_cuspFunction (⟨z, hz⟩ : ℍ) one_ne_zero hf_per
    simpa [g, Function.comp_apply, ofComplex_apply_of_im_pos hz] using hEq.symm
  have hd : deriv (f ∘ ofComplex) (τ : ℂ) =
      deriv g (Periodic.qParam 1 τ) * (2 * π * I * Periodic.qParam 1 τ) :=
    ((hg_at.comp (τ : ℂ) hq_at).congr_of_eventuallyEq hcomp).deriv
  simp only [nD, Derivative.normalizedDerivOfComplex, hd]
  have hne : (2 * π * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  dsimp [g]
  field_simp [hne]

private lemma nD_isZeroAtImInfty {f : ℍ → ℂ}
    (hf_per : Periodic (f ∘ ofComplex) 1) (hf_hol : MDiff f) (hf_bdd : IsBoundedAtImInfty f) :
    IsZeroAtImInfty (nD f) := by
  let g : ℂ → ℂ := cuspFunction 1 f
  have hg_diff : DifferentiableOn ℂ g (Metric.ball 0 1) :=
    UpperHalfPlane.differentiableOn_cuspFunction_ball one_pos hf_per hf_hol hf_bdd
  have hdg_cont : ContinuousAt (deriv g) 0 :=
    ((hg_diff.deriv Metric.isOpen_ball).differentiableAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))).continuousAt
  have h1 : Tendsto (Periodic.qParam 1 ∘ ((↑) : ℍ → ℂ)) atImInfty (𝓝 0) :=
    UpperHalfPlane.qParam_tendsto_atImInfty one_pos
  have h2 : Tendsto (fun τ : ℍ ↦ deriv g (Periodic.qParam 1 τ)) atImInfty (𝓝 (deriv g 0)) :=
    hdg_cont.tendsto.comp h1
  have hmul : Tendsto (fun τ : ℍ ↦ Periodic.qParam 1 τ * deriv g (Periodic.qParam 1 τ))
      atImInfty (𝓝 (0 * deriv g 0)) := h1.mul h2
  rw [zero_mul] at hmul
  exact hmul.congr fun τ => (nD_eq_q_deriv_cuspFunction hf_per hf_hol hf_bdd τ).symm

private lemma nD_isBoundedAtImInfty {f : ℍ → ℂ}
    (hf_per : Periodic (f ∘ ofComplex) 1) (hf_hol : MDiff f) (hf_bdd : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (nD f) :=
  (nD_isZeroAtImInfty hf_per hf_hol hf_bdd).isBigO_one ℝ

private lemma nD_periodic {f : ℍ → ℂ}
    (hf_per : Periodic (f ∘ ofComplex) 1) (hf_hol : MDiff f) (hf_bdd : IsBoundedAtImInfty f) :
    Periodic ((nD f) ∘ ofComplex) 1 := by
  intro z
  by_cases hz : 0 < z.im
  · have hz1 : 0 < (z + 1).im := by simpa using hz
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos hz1]
    rw [nD_eq_q_deriv_cuspFunction hf_per hf_hol hf_bdd ⟨z + 1, hz1⟩,
      nD_eq_q_deriv_cuspFunction hf_per hf_hol hf_bdd ⟨z, hz⟩]
    have hqp : Periodic.qParam 1 (z + 1) = Periodic.qParam 1 z := by
      simp only [qParam_one_eq_cexp, mul_add, mul_one, Complex.exp_add]
      have h1 : cexp (2 * π * I) = 1 := Complex.exp_two_pi_mul_I
      rw [h1, mul_one]
    change Periodic.qParam 1 (z + 1) * deriv (cuspFunction 1 f) (Periodic.qParam 1 (z + 1)) =
      Periodic.qParam 1 z * deriv (cuspFunction 1 f) (Periodic.qParam 1 z)
    rw [hqp]
  · have hz1 : ¬ 0 < (z + 1).im := by simpa using hz
    simp only [Function.comp_apply, ofComplex_apply_of_im_nonpos (not_lt.mp hz),
      ofComplex_apply_of_im_nonpos (not_lt.mp hz1)]

private lemma qExpansion_nD {f : ℍ → ℂ}
    (hf_per : Periodic (f ∘ ofComplex) 1) (hf_hol : MDiff f) (hf_bdd : IsBoundedAtImInfty f) :
    qExpansion 1 (nD f) = PowerSeries.X * PowerSeries.derivative ℂ (qExpansion 1 f) := by
  let g : ℂ → ℂ := cuspFunction 1 f
  have hg_diff : DifferentiableOn ℂ g (Metric.ball 0 1) :=
    UpperHalfPlane.differentiableOn_cuspFunction_ball one_pos hf_per hf_hol hf_bdd
  have hg_ana : AnalyticAt ℂ g 0 :=
    hg_diff.analyticAt (Metric.ball_mem_nhds (0 : ℂ) one_pos)
  have hdg_ana : AnalyticAt ℂ (deriv g) 0 :=
    (hg_diff.deriv Metric.isOpen_ball).analyticAt (Metric.ball_mem_nhds (0 : ℂ) one_pos)
  have hcusp : cuspFunction 1 (nD f) =ᶠ[𝓝 (0 : ℂ)] ((id : ℂ → ℂ) * deriv g) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with q hq
    by_cases hq0 : q = 0
    · subst hq0
      simp only [Pi.mul_apply, id_eq, zero_mul]
      exact (nD_isZeroAtImInfty hf_per hf_hol hf_bdd).cuspFunction_apply_zero one_pos
    · have him := Periodic.im_invQParam_pos_of_norm_lt_one one_pos (mem_ball_zero_iff.mp hq) hq0
      let τ : ℍ := ⟨Periodic.invQParam 1 q, him⟩
      have hqτ : Periodic.qParam 1 τ = q := Periodic.qParam_right_inv one_ne_zero hq0
      simp only [cuspFunction, Periodic.cuspFunction_eq_of_nonzero 1 _ hq0, Function.comp_apply,
        ofComplex_apply_of_im_pos him, Pi.mul_apply, id_eq]
      rw [nD_eq_q_deriv_cuspFunction hf_per hf_hol hf_bdd τ, hqτ]
  ext m
  cases m with
  | zero =>
    rw [PowerSeries.coeff_zero_X_mul, qExpansion_coeff]
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero, one_mul]
    exact (nD_isZeroAtImInfty hf_per hf_hol hf_bdd).cuspFunction_apply_zero one_pos
  | succ m =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, qExpansion_coeff, qExpansion_coeff]
    rw [hcusp.iteratedDeriv_eq, iteratedDeriv_mul contDiffAt_id (hdg_ana.contDiffAt.of_le le_top)]
    rw [Finset.sum_eq_single 1]
    · simp only [Nat.choose_one_right, iteratedDeriv_one, deriv_id, Nat.add_sub_cancel,
        ← iteratedDeriv_succ', Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      dsimp [g]
      field_simp [Nat.factorial_ne_zero]
    · intro i _ hne
      rcases i with _ | _ | i
      · simp
      · exact absurd rfl hne
      · have : iteratedDeriv (i + 2) (id : ℂ → ℂ) 0 = 0 := by
          rw [iteratedDeriv_succ', deriv_id', iteratedDeriv_const, if_neg (by omega)]
        simp [this]
    · intro hnot
      exact absurd (Finset.mem_range.mpr (Nat.succ_lt_succ (Nat.succ_pos m))) hnot

/- #### Ramanujan's differential equation $D E_2 = (E_2^2 - E_4) / 12$ -/

private lemma E2_periodic : Periodic (E2 ∘ ofComplex) 1 := by
  intro z
  by_cases hz : 0 < z.im
  · have hz1 : 0 < (z + 1).im := by simpa using hz
    let τ : ℍ := ⟨z, hz⟩
    let τ1 : ℍ := ⟨z + 1, hz1⟩
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos hz1]
    have hT := congrFun (E2_slash_action ModularGroup.T) τ
    rw [D2_T, smul_zero, sub_zero, ModularForm.SL_slash_def] at hT
    have hden : denom (mapGL ℝ ModularGroup.T) τ = 1 := by
      rw [denom, mapGL_apply, mapGL_apply]
      simp [ModularGroup.T]
    have hsm : ModularGroup.T • τ = τ1 := by
      ext
      rw [UpperHalfPlane.modular_T_smul]
      simp [τ, τ1, add_comm]
    change E2 (ModularGroup.T • τ) * denom (mapGL ℝ ModularGroup.T) τ ^ (-2 : ℤ) = E2 τ at hT
    rw [hsm, hden, one_zpow, mul_one] at hT
    exact hT
  · have hz1 : ¬ 0 < (z + 1).im := by simpa using hz
    simp only [Function.comp_apply, ofComplex_apply_of_im_nonpos (not_lt.mp hz),
      ofComplex_apply_of_im_nonpos (not_lt.mp hz1)]

private lemma qExpansion_coeff_unique_fun {f : ℍ → ℂ} {c : ℕ → ℂ}
    (hfanalytic : AnalyticAt ℂ (cuspFunction 1 f) 0)
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • Periodic.qParam 1 τ ^ m) (f τ)) (m : ℕ) :
    c m = (qExpansion 1 f).coeff m := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction one_pos hfanalytic hf).hasFPowerSeriesAt
  have h2 := hfanalytic.hasFPowerSeriesAt
  have := congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)
  simp only [FormalMultilinearSeries.coeff_ofScalars] at this
  rw [this, qExpansion_coeff, div_eq_inv_mul]

private lemma E2_qExpansion_coeff (m : ℕ) :
    (qExpansion 1 E2).coeff m = if m = 0 then 1 else -24 * (σ 1 m : ℂ) := by
  have hana : AnalyticAt ℂ (cuspFunction 1 E2) 0 :=
    (UpperHalfPlane.differentiableOn_cuspFunction_ball one_pos E2_periodic
      E2_mdifferentiable isBoundedAtImInfty_E2).analyticAt (Metric.ball_mem_nhds (0 : ℂ) one_pos)
  exact (qExpansion_coeff_unique_fun (c := fun n => if n = 0 then 1 else -24 * (σ 1 n : ℂ)) hana
    (fun τ => by simpa only [Function.Periodic.qParam, ofReal_one, div_one] using
      hasSum_qExpansion_E2 (z := τ)) m).symm

private lemma nD_D2_eq (γ : SL(2, ℤ)) (τ : ℍ) :
    nD (D2 γ) τ = -(γ 1 0 : ℂ) ^ 2 / denom (mapGL ℝ γ) τ ^ 2 := by
  have hden_ne : (γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (mapGL ℝ γ) τ
    simpa [denom, mapGL_apply] using this
  have hlin : HasDerivAt (fun z : ℂ ↦ (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) (γ 1 0 : ℂ) (τ : ℂ) := by
    simpa using ((hasDerivAt_id (τ : ℂ)).const_mul (γ 1 0 : ℂ)).add_const (γ 1 1 : ℂ)
  have hmul : HasDerivAt (fun z : ℂ ↦ (2 * π * I * (γ 1 0 : ℂ)) * ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ))⁻¹)
      ((2 * π * I * (γ 1 0 : ℂ)) * (-(γ 1 0 : ℂ) / ((γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ)) ^ 2)) (τ : ℂ) :=
    (hlin.inv hden_ne).const_mul (2 * π * I * (γ 1 0 : ℂ))
  have hcomp : (D2 γ ∘ ofComplex) =ᶠ[𝓝 (τ : ℂ)]
      fun z : ℂ ↦ (2 * π * I * (γ 1 0 : ℂ)) * ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ))⁻¹ := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz, D2, denom, div_eq_mul_inv]
    rfl
  have hderiv : deriv (D2 γ ∘ ofComplex) (τ : ℂ) =
      (2 * π * I * (γ 1 0 : ℂ)) * (-(γ 1 0 : ℂ) / ((γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ)) ^ 2) :=
    (hmul.congr_of_eventuallyEq hcomp).deriv
  simp only [nD, Derivative.normalizedDerivOfComplex, hderiv]
  have hden_eq : denom (mapGL ℝ γ) τ = (γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ) := by
    simp [denom, mapGL_apply]
  rw [hden_eq]
  have hne : (2 * π * I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  field_simp [hne, hden_ne]

private lemma D2_mdiff (γ : SL(2, ℤ)) : MDiff (D2 γ) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hd : DifferentiableOn ℂ
      (fun z : ℂ ↦ (2 * π * I * (γ 1 0 : ℂ)) / ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)))
      upperHalfPlaneSet := by
    refine (differentiableOn_const _).div
      ((differentiableOn_const _).mul differentiableOn_id |>.add (differentiableOn_const _)) ?_
    intro z hz
    have := UpperHalfPlane.denom_ne_zero (mapGL ℝ γ) ⟨z, hz⟩
    simpa [denom, mapGL_apply] using this
  refine hd.congr fun z hz => ?_
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz, D2, denom]
  rfl

private lemma nD_E2_sub_sq_slash (γ : SL(2, ℤ)) :
    (fun τ : ℍ ↦ nD E2 τ - E2 τ ^ 2 / 12) ∣[(4 : ℤ)] γ =
      fun τ : ℍ ↦ nD E2 τ - E2 τ ^ 2 / 12 := by
  have h1 := Derivative.normalizedDerivOfComplex_SL_slash (k := 2) E2_mdifferentiable (γ := γ)
  have h2 := E2_slash_action γ
  have hD_rhs : nD (E2 ∣[(2 : ℤ)] γ) = nD E2 - (1 / (2 * riemannZeta 2)) • nD (D2 γ) := by
    dsimp [nD]
    rw [h2, Derivative.normalizedDerivOfComplex_sub _ _ E2_mdifferentiable
      ((D2_mdiff γ).const_smul _), Derivative.normalizedDerivOfComplex_smul _ _ (D2_mdiff γ)]
  ext τ
  have h1τ := congrFun h1 τ
  have hDτ := congrFun hD_rhs τ
  have h2τ := congrFun h2 τ
  have hD2τ := nD_D2_eq γ τ
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1τ hDτ h2τ
  have hslash_sub : ((fun z : ℍ ↦ nD E2 z - E2 z ^ 2 / 12) ∣[(4 : ℤ)] γ) τ =
      (nD E2 ∣[(4 : ℤ)] γ) τ - ((E2 ∣[(2 : ℤ)] γ) τ) ^ 2 / 12 := by
    simp only [ModularForm.SL_slash_def]
    have hpow : ∀ w : ℂ, w ^ (-4 : ℤ) = (w ^ (-2 : ℤ)) ^ 2 := fun w => by
      rw [← zpow_natCast, ← zpow_mul]; norm_num
    rw [hpow]; ring
  rw [hslash_sub]
  have hz2 : (riemannZeta 2 : ℂ) = π ^ 2 / 6 := riemannZeta_two
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hden_eq : denom γ τ = denom (mapGL ℝ γ) τ := rfl
  have hden_ne : denom (mapGL ℝ γ) τ ≠ 0 := UpperHalfPlane.denom_ne_zero (mapGL ℝ γ) τ
  have h1τ' : nD (E2 ∣[(2 : ℤ)] γ) τ = (nD E2 ∣[(4 : ℤ)] γ) τ -
      (2 : ℂ) * (2 * π * I)⁻¹ * ((γ 1 0 : ℂ) / denom γ τ) * (E2 ∣[(2 : ℤ)] γ) τ := by
    simpa [nD] using h1τ
  have hstep : (nD E2 ∣[(4 : ℤ)] γ) τ =
      nD E2 τ - 1 / (2 * riemannZeta 2) * nD (D2 γ) τ +
      (2 : ℂ) * (2 * π * I)⁻¹ * ((γ 1 0 : ℂ) / denom γ τ) * (E2 ∣[(2 : ℤ)] γ) τ := by
    linear_combination hDτ - h1τ'
  rw [hstep, h2τ, hD2τ, hz2, hden_eq]
  simp only [D2, hden_eq]
  field_simp [hpi, Complex.I_ne_zero, hden_ne]
  have hI3 : (I : ℂ) ^ 3 = -I := by rw [pow_succ, Complex.I_sq]; ring
  ring_nf
  rw [hI3, Complex.I_sq]
  ring

private lemma nD_E2_eq (τ : ℍ) : nD E2 τ = (E2 τ ^ 2 - E₄ τ) / 12 := by
  let Ffun : ℍ → ℂ := fun z => nD E2 z - E2 z ^ 2 / 12 + E₄ z / 12
  have hF_slash : ∀ γ : SL(2, ℤ), Ffun ∣[(4 : ℤ)] γ = Ffun := by
    intro γ
    have hE4 : (E₄ : ℍ → ℂ) ∣[(4 : ℤ)] γ = (E₄ : ℍ → ℂ) :=
      SlashInvariantFormClass.slash_action_eq E₄ (mapGL ℝ γ) ⟨γ, rfl⟩
    have h1 := nD_E2_sub_sq_slash γ
    have hadd : Ffun = (fun z => nD E2 z - E2 z ^ 2 / 12) + ((1 / 12 : ℂ) • (E₄ : ℍ → ℂ)) := by
      ext z; simp [Ffun, div_eq_inv_mul]
    rw [hadd, SlashAction.add_slash, h1, ModularForm.SL_smul_slash, hE4]
  have hF_holo : MDiff Ffun := by
    have hEq : Ffun = fun z => nD E2 z - E2 z ^ 2 * (12 : ℂ)⁻¹ + E₄ z * (12 : ℂ)⁻¹ := by
      ext z; simp [Ffun, div_eq_mul_inv]
    rw [hEq]
    exact ((Derivative.normalizedDerivOfComplex_mdifferentiable E2_mdifferentiable).sub
      ((E2_mdifferentiable.pow 2).mul mdifferentiable_const)).add (E₄.holo'.mul mdifferentiable_const)
  have hF_bdd : IsBoundedAtImInfty Ffun := by
    have h1 : IsBoundedAtImInfty (nD E2) :=
      nD_isBoundedAtImInfty E2_periodic E2_mdifferentiable isBoundedAtImInfty_E2
    have h2 : IsBoundedAtImInfty (fun z : ℍ ↦ -(1 / 12 : ℂ) * (E2 z * E2 z)) :=
      (isBoundedAtImInfty_E2.mul isBoundedAtImInfty_E2).const_mul_left _
    have h3 : IsBoundedAtImInfty (fun z : ℍ ↦ (1 / 12 : ℂ) * E₄ z) :=
      (ModularFormClass.bdd_at_infty E₄).const_mul_left _
    have heq : Ffun = fun z => nD E2 z + (-(1 / 12 : ℂ) * (E2 z * E2 z)) + (1 / 12 : ℂ) * E₄ z := by
      ext z; simp [Ffun]; ring
    rw [heq]
    exact (h1.add h2).add h3
  let FMF : ModularForm 𝒮ℒ 4 := {
    toFun := Ffun
    slash_action_eq' := by rintro _ ⟨γ, rfl⟩; exact hF_slash γ
    holo' := hF_holo
    bdd_at_cusps' := fun {c} hc => by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
      rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
      intro γ _
      rw [hF_slash γ]
      exact hF_bdd }
  have hF0 : (qExpansion 1 (FMF : ℍ → ℂ)).coeff 0 = 0 := by
    have hE2_ana : AnalyticAt ℂ (cuspFunction 1 E2) 0 :=
      (UpperHalfPlane.differentiableOn_cuspFunction_ball one_pos E2_periodic
        E2_mdifferentiable isBoundedAtImInfty_E2).analyticAt (Metric.ball_mem_nhds (0 : ℂ) one_pos)
    have hDE2_ana : AnalyticAt ℂ (cuspFunction 1 (nD E2)) 0 :=
      (UpperHalfPlane.differentiableOn_cuspFunction_ball one_pos
        (nD_periodic E2_periodic E2_mdifferentiable isBoundedAtImInfty_E2)
        (Derivative.normalizedDerivOfComplex_mdifferentiable E2_mdifferentiable)
        (nD_isBoundedAtImInfty E2_periodic E2_mdifferentiable isBoundedAtImInfty_E2)).analyticAt
          (Metric.ball_mem_nhds (0 : ℂ) one_pos)
    have hE4_ana : AnalyticAt ℂ (cuspFunction 1 (E₄ : ℍ → ℂ)) 0 :=
      ModularFormClass.analyticAt_cuspFunction_zero E₄ one_pos one_mem_strictPeriods_SL
    have hE2sq_ana : AnalyticAt ℂ (cuspFunction 1 (E2 * E2)) 0 := by
      rw [UpperHalfPlane.cuspFunction_mul hE2_ana.continuousAt hE2_ana.continuousAt]
      exact hE2_ana.mul hE2_ana
    have hsm1_ana : AnalyticAt ℂ (cuspFunction 1 ((1 / 12 : ℂ) • (E2 * E2))) 0 := by
      rw [UpperHalfPlane.cuspFunction_smul hE2sq_ana.continuousAt]
      exact analyticAt_const.smul hE2sq_ana
    have hsub_ana : AnalyticAt ℂ (cuspFunction 1 (nD E2 - (1 / 12 : ℂ) • (E2 * E2))) 0 := by
      rw [UpperHalfPlane.cuspFunction_sub hDE2_ana.continuousAt hsm1_ana.continuousAt]
      exact hDE2_ana.sub hsm1_ana
    have hsm2_ana : AnalyticAt ℂ (cuspFunction 1 ((1 / 12 : ℂ) • (E₄ : ℍ → ℂ))) 0 := by
      rw [UpperHalfPlane.cuspFunction_smul hE4_ana.continuousAt]
      exact analyticAt_const.smul hE4_ana
    have hF_eq : (FMF : ℍ → ℂ) = (nD E2 - (1 / 12 : ℂ) • (E2 * E2)) + (1 / 12 : ℂ) • (E₄ : ℍ → ℂ) := by
      ext z; change nD E2 z - E2 z ^ 2 / 12 + E₄ z / 12 = _; simp [sq, div_eq_inv_mul]
    rw [hF_eq, UpperHalfPlane.qExpansion_add hsub_ana hsm2_ana,
      UpperHalfPlane.qExpansion_sub hDE2_ana hsm1_ana,
      UpperHalfPlane.qExpansion_smul hE2sq_ana, UpperHalfPlane.qExpansion_mul hE2_ana hE2_ana,
      UpperHalfPlane.qExpansion_smul hE4_ana, map_add, map_sub, PowerSeries.coeff_smul,
      PowerSeries.coeff_smul, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff, E2_qExpansion_coeff 0,
      EisensteinSeries.E_qExpansion_coeff_zero (k := 4) (by norm_num) ⟨2, rfl⟩,
      qExpansion_nD E2_periodic E2_mdifferentiable isBoundedAtImInfty_E2,
      PowerSeries.coeff_zero_X_mul]
    norm_num
  have hCF0 : ModularForm.toCuspForm FMF hF0 = 0 :=
    rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num)) _
  have hτ : Ffun τ = 0 := congrFun (congrArg DFunLike.coe hCF0) τ
  dsimp [Ffun] at hτ
  linear_combination hτ

end RamanujanODEs

section RamanujanODEs
open UpperHalfPlane hiding I
open Complex Filter Function ModularForm ModularGroup CongruenceSubgroup EisensteinSeries
open Matrix.SpecialLinearGroup
open scoped Real Topology Manifold MatrixGroups ModularForm ArithmeticFunction.sigma

/- #### Modular identities on $\Gamma_0(2)$: $E_4 + 4 E_4(2\tau) = 5 E_2^{*2}$ and $H_4^2 = E_2^{*4} - 256 \Delta_8$ -/

private lemma SL_inv_apply {f : ℍ → ℂ} {k : ℤ} {γ : SL(2, ℤ)} (h : f ∣[k] mapGL ℝ γ = f) (τ : ℍ) :
    f (γ • τ) * denom (mapGL ℝ γ) τ ^ (-k) = f τ :=
  (ModularForm.SL_slash_apply (f := f) (k := k) γ τ).symm.trans (congrFun h τ)

private lemma SL_inv_apply' {f : ℍ → ℂ} {k : ℤ} {γ : SL(2, ℤ)} (h : f ∣[k] mapGL ℝ γ = f) (τ : ℍ) :
    f (γ • τ) * denom (γ : GL (Fin 2) ℝ) τ ^ (-k) = f τ :=
  (ModularForm.SL_slash_apply (f := f) (k := k) γ τ).symm.trans (congrFun h τ)

private noncomputable def E4_2 (τ : ℍ) : ℂ := E₄ (mul2 τ)

private lemma E4_slash_Gamma02 (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma0 2) :
    (E₄ : ℍ → ℂ) ∣[(4 : ℤ)] γ = (E₄ : ℍ → ℂ) :=
  SlashInvariantFormClass.slash_action_eq E₄ (mapGL ℝ γ) ⟨γ, rfl⟩

private lemma E4_2_slash_Gamma02 (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 2) :
    E4_2 ∣[(4 : ℤ)] γ = E4_2 := by
  have hc : (2 : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) 2).mp hγ
  obtain ⟨c', hc'⟩ := hc
  let γ' : SL(2, ℤ) := ⟨!![γ 0 0, 2 * γ 0 1; c', γ 1 1], by
    have hdet := γ.2
    rw [Matrix.det_fin_two] at hdet ⊢
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    linear_combination hdet + γ 0 1 * hc'⟩
  have hdenom : ∀ τ : ℍ, denom (mapGL ℝ γ') (mul2 τ) = denom (mapGL ℝ γ) τ := fun τ => by
    simp only [denom, mapGL_apply, coe_mul2]
    change (c' : ℂ) * (2 * (τ : ℂ)) + (γ 1 1 : ℂ) = (γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ)
    rw [hc']; push_cast; ring
  have hsmul : ∀ τ : ℍ, mul2 (γ • τ) = γ' • mul2 τ := fun τ => by
    ext
    have h1 : ((γ • τ : ℍ) : ℂ) = num (mapGL ℝ γ) τ / denom (mapGL ℝ γ) τ :=
      UpperHalfPlane.coe_smul_of_det_pos (by simp) τ
    have h2 : ((γ' • mul2 τ : ℍ) : ℂ) = num (mapGL ℝ γ') (mul2 τ) / denom (mapGL ℝ γ') (mul2 τ) :=
      UpperHalfPlane.coe_smul_of_det_pos (by simp) (mul2 τ)
    rw [coe_mul2, h1, h2, hdenom τ]
    have hnum : 2 * num (mapGL ℝ γ) τ = num (mapGL ℝ γ') (mul2 τ) := by
      simp only [num, mapGL_apply, coe_mul2]
      change 2 * ((γ 0 0 : ℂ) * (τ : ℂ) + (γ 0 1 : ℂ)) =
        (γ 0 0 : ℂ) * (2 * (τ : ℂ)) + ((2 * γ 0 1 : ℤ) : ℂ)
      push_cast; ring
    rw [← mul_div_assoc, hnum]
  ext τ
  rw [ModularForm.SL_slash_def]
  simp only [E4_2, hsmul τ]
  have h : E₄ (γ' • mul2 τ) * denom (mapGL ℝ γ') (mul2 τ) ^ (-4 : ℤ) = E₄ (mul2 τ) := by
    exact SL_inv_apply (SlashInvariantFormClass.slash_action_eq E₄ (mapGL ℝ γ') ⟨γ', rfl⟩) (mul2 τ)
  rw [hdenom τ] at h
  exact h

private lemma E4_slash_W2 : (E₄ : ℍ → ℂ) ∣[(4 : ℤ)] W2 = (4 : ℂ) • E4_2 := by
  ext τ
  have hW : ((E₄ : ℍ → ℂ) ∣[(4 : ℤ)] W2) τ = E₄ (W2 • τ) * (2 * (τ : ℂ) ^ 2) ^ (-2 : ℤ) := by
    simpa using slash_W2_even 2 (E₄ : ℍ → ℂ) τ
  rw [hW, W2_smul_eq_S_mul2]
  have hS : E₄ (ModularGroup.S • mul2 τ) * denom (ModularGroup.S : GL (Fin 2) ℝ) (mul2 τ) ^ (-4 : ℤ) =
      E₄ (mul2 τ) :=
    SL_inv_apply' (SlashInvariantFormClass.slash_action_eq E₄ (mapGL ℝ ModularGroup.S) ⟨ModularGroup.S, rfl⟩) (mul2 τ)
  rw [ModularGroup.denom_S, coe_mul2] at hS
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hpow1 : (2 * (τ : ℂ)) ^ (-4 : ℤ) = ((2 * (τ : ℂ)) ^ 4)⁻¹ := by rw [zpow_neg]; norm_cast
  have hpow2 : (2 * (τ : ℂ) ^ 2) ^ (-2 : ℤ) = ((2 * (τ : ℂ) ^ 2) ^ 2)⁻¹ := by rw [zpow_neg]; norm_cast
  rw [hpow1] at hS
  rw [hpow2]
  simp only [Pi.smul_apply, smul_eq_mul, E4_2]
  have hS' : E₄ (ModularGroup.S • mul2 τ) = E₄ (mul2 τ) * (2 * (τ : ℂ)) ^ 4 := by
    have hm := congrArg (· * (2 * (τ : ℂ)) ^ 4) hS
    have hc : E₄ (ModularGroup.S • mul2 τ) * ((2 * (τ : ℂ)) ^ 4)⁻¹ * (2 * (τ : ℂ)) ^ 4 =
        E₄ (ModularGroup.S • mul2 τ) := by field_simp [hτ]
    linear_combination hm - hc
  rw [hS']
  field_simp [hτ]
  ring

private lemma E4_2_slash_W2 : E4_2 ∣[(4 : ℤ)] W2 = (1 / 4 : ℂ) • (E₄ : ℍ → ℂ) := by
  ext τ
  have hW : (E4_2 ∣[(4 : ℤ)] W2) τ = E4_2 (W2 • τ) * (2 * (τ : ℂ) ^ 2) ^ (-2 : ℤ) := by
    simpa using slash_W2_even 2 E4_2 τ
  rw [hW, E4_2, mul2_W2_smul]
  have hS : E₄ (ModularGroup.S • τ) * denom (ModularGroup.S : GL (Fin 2) ℝ) τ ^ (-4 : ℤ) = E₄ τ :=
    SL_inv_apply' (SlashInvariantFormClass.slash_action_eq E₄ (mapGL ℝ ModularGroup.S) ⟨ModularGroup.S, rfl⟩) τ
  rw [ModularGroup.denom_S] at hS
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hpow1 : (τ : ℂ) ^ (-4 : ℤ) = ((τ : ℂ) ^ 4)⁻¹ := by rw [zpow_neg]; norm_cast
  have hpow2 : (2 * (τ : ℂ) ^ 2) ^ (-2 : ℤ) = ((2 * (τ : ℂ) ^ 2) ^ 2)⁻¹ := by rw [zpow_neg]; norm_cast
  rw [hpow1] at hS
  rw [hpow2]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hS' : E₄ (ModularGroup.S • τ) = E₄ τ * (τ : ℂ) ^ 4 := by
    have hm := congrArg (· * (τ : ℂ) ^ 4) hS
    have hc : E₄ (ModularGroup.S • τ) * ((τ : ℂ) ^ 4)⁻¹ * (τ : ℂ) ^ 4 =
        E₄ (ModularGroup.S • τ) := by field_simp [hτ]
    linear_combination hm - hc
  rw [hS']
  field_simp [hτ]
  ring

private def e4Coeff (m : ℕ) : ℤ :=
  if m = 0 then 1 else 240 * (σ 3 m : ℤ)

private lemma E4_qExpansion_coeff (m : ℕ) :
    (qExpansion 1 (E₄ : ℍ → ℂ)).coeff m = (e4Coeff m : ℂ) := by
  have h := EisensteinSeries.E_qExpansion_coeff (k := 4) (by norm_num) ⟨2, rfl⟩ m
  rw [show bernoulli 4 = -1 / 30 by decide +kernel] at h
  change (qExpansion 1 (E₄ : ℍ → ℂ)).coeff m = _
  rw [h]
  unfold e4Coeff
  split_ifs <;> push_cast <;> ring

private lemma E4_hasSum_qExpansion (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (e4Coeff m : ℂ) • Periodic.qParam 1 τ ^ m) (E₄ τ) := by
  have h := ModularForm.hasSum_qExpansion (f := E₄) one_pos one_mem_strictPeriods_SL τ
  refine h.congr_fun fun m => ?_
  rw [E4_qExpansion_coeff m, smul_eq_mul]

private lemma E4_2_hasSum_qExpansion (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (if 2 ∣ m then (e4Coeff (m / 2) : ℂ) else 0) • Periodic.qParam 1 τ ^ m)
      (E4_2 τ) := by
  have h2 := E4_hasSum_qExpansion (mul2 τ)
  have hq2 : ∀ k : ℕ, Periodic.qParam 1 (mul2 τ) ^ k = Periodic.qParam 1 τ ^ (2 * k) := fun k => by
    simp only [qParam_one_eq_cexp, coe_mul2, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have hinj : Function.Injective (fun k : ℕ ↦ 2 * k) := fun a b hab => by dsimp at hab; omega
  rw [← hinj.hasSum_iff (f := fun m : ℕ ↦
    (if 2 ∣ m then (e4Coeff (m / 2) : ℂ) else 0) • Periodic.qParam 1 τ ^ m)]
  · dsimp [E4_2]
    convert h2 using 1
    ext k
    have hk2 : 2 ∣ 2 * k := ⟨k, rfl⟩
    have hdiv : (2 * k) / 2 = k := Nat.mul_div_right k two_pos
    dsimp only [Function.comp_apply]
    rw [if_pos hk2, hdiv, hq2 k]
    simp only [smul_eq_mul]
  · intro m hm
    have hnd : ¬ 2 ∣ m := fun ⟨k, hk⟩ => hm ⟨k, hk.symm⟩
    simp [hnd]

private noncomputable def H4 (τ : ℍ) : ℂ := (4 * E4_2 τ - E₄ τ) / 3

private def h4Coeff (m : ℕ) : ℤ :=
  if m = 0 then 1
  else (if 2 ∣ m then 320 * (σ 3 (m / 2) : ℤ) else 0) - 80 * (σ 3 m : ℤ)

private lemma H4_hasSum_qExpansion (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (h4Coeff m : ℂ) • Periodic.qParam 1 τ ^ m) (H4 τ) := by
  have hcomb := (((E4_2_hasSum_qExpansion τ).mul_left 4).sub (E4_hasSum_qExpansion τ)).mul_left (3 : ℂ)⁻¹
  have hval : (3 : ℂ)⁻¹ * (4 * E4_2 τ - E₄ τ) = H4 τ := by simp [H4, div_eq_inv_mul]
  rw [hval] at hcomb
  refine hcomb.congr_fun fun m => ?_
  simp only [h4Coeff, e4Coeff, smul_eq_mul]
  by_cases hm : m = 0
  · subst hm; simp; ring
  · by_cases hd : 2 ∣ m
    · have hne : m / 2 ≠ 0 := by obtain ⟨k, hk⟩ := hd; omega
      simp [hm, hd, hne]; ring
    · simp [hm, hd]; ring

private lemma H4_slash_Gamma02 (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 2) :
    H4 ∣[(4 : ℤ)] γ = H4 := by
  have hdef : H4 = (4 / 3 : ℂ) • E4_2 + (-(1 / 3 : ℂ)) • (E₄ : ℍ → ℂ) := by
    ext τ; simp [H4]; ring
  rw [hdef, SlashAction.add_slash, ModularForm.SL_smul_slash, ModularForm.SL_smul_slash,
    E4_2_slash_Gamma02 γ hγ, E4_slash_Gamma02 γ hγ]

private lemma H4_slash_W2 : H4 ∣[(4 : ℤ)] W2 = -H4 := by
  have hdef : H4 = (4 / 3 : ℂ) • E4_2 + (-(1 / 3 : ℂ)) • (E₄ : ℍ → ℂ) := by
    ext τ; simp [H4]; ring
  rw [hdef, SlashAction.add_slash, ModularForm.smul_slash, ModularForm.smul_slash,
    σ_W2, σ_W2, E4_2_slash_W2, E4_slash_W2]
  ext τ; simp; ring

private lemma H4_mdiff : MDiff H4 := by
  have hEq : H4 = fun z => ((4 : ℂ) * E₄ (mul2 z) - E₄ z) * (3 : ℂ)⁻¹ := by
    ext z; simp [H4, E4_2, div_eq_mul_inv]
  rw [hEq]
  exact ((mdifferentiable_const.mul (mdiff_comp_mul2 E₄.holo')).sub E₄.holo').mul
    mdifferentiable_const

private noncomputable def H4MF : ModularForm Γ02 4 where
  toFun := H4
  slash_action_eq' := by rintro _ ⟨γ, hγ, rfl⟩; exact H4_slash_Gamma02 γ hγ
  holo' := H4_mdiff
  bdd_at_cusps' hc := isBoundedAt_Γ02_of_W2 (ε := -1) H4_slash_Gamma02
    (by simpa using H4_slash_W2)
    (isBoundedAtImInfty_of_hasSum_qExpansion one_pos H4_hasSum_qExpansion) hc

private lemma H4_qExpansion_coeff (m : ℕ) :
    (qExpansion 1 (H4MF : ℍ → ℂ)).coeff m = (h4Coeff m : ℂ) :=
  (ModularFormClass.qExpansion_coeff_unique (f := H4MF) one_pos one_mem_strictPeriods_Γ02
    H4_hasSum_qExpansion m).symm

private lemma E4_add_four_E4_2 (τ : ℍ) : E₄ τ + 4 * E₄ (mul2 τ) = 5 * E2star τ ^ 2 := by
  let f : ℍ → ℂ := fun z => E₄ z + 4 * E4_2 z
  have hf_Γ : ∀ γ ∈ CongruenceSubgroup.Gamma0 2, f ∣[(4 : ℤ)] γ = f := by
    intro γ hγ
    have hdef : f = (E₄ : ℍ → ℂ) + (4 : ℂ) • E4_2 := by ext z; simp [f]
    rw [hdef, SlashAction.add_slash, E4_slash_Gamma02 γ hγ, ModularForm.SL_smul_slash,
      E4_2_slash_Gamma02 γ hγ]
  have hf_W : f ∣[(4 : ℤ)] W2 = ((-1 : ℂ) ^ 2) • f := by
    have hdef : f = (E₄ : ℍ → ℂ) + (4 : ℂ) • E4_2 := by ext z; simp [f]
    rw [hdef, SlashAction.add_slash, E4_slash_W2, ModularForm.smul_slash, σ_W2, E4_2_slash_W2]
    ext z; simp; ring
  have hf_hasSum : ∀ z : ℍ, HasSum (fun m : ℕ ↦
      ((e4Coeff m + if 2 ∣ m then 4 * e4Coeff (m / 2) else 0 : ℤ) : ℂ) • Periodic.qParam 1 z ^ m)
      (f z) := fun z => by
    have h := (E4_hasSum_qExpansion z).add ((E4_2_hasSum_qExpansion z).mul_left 4)
    refine h.congr_fun fun m => ?_
    simp only [smul_eq_mul]; split_ifs <;> push_cast <;> ring
  let fMF : ModularForm Γ02 (2 * ((2 : ℕ) : ℤ)) := {
    toFun := f
    slash_action_eq' := by rintro _ ⟨γ, hγ, rfl⟩; exact hf_Γ γ hγ
    holo' := E₄.holo'.add (mdifferentiable_const.mul (mdiff_comp_mul2 E₄.holo'))
    bdd_at_cusps' := isBoundedAt_Γ02_of_W2 hf_Γ hf_W
      (isBoundedAtImInfty_of_hasSum_qExpansion one_pos hf_hasSum) }
  have hf_q : ∀ m, (qExpansion 1 (fMF : ℍ → ℂ)).coeff m =
      ((e4Coeff m + if 2 ∣ m then 4 * e4Coeff (m / 2) else 0 : ℤ) : ℂ) := fun m =>
    (ModularFormClass.qExpansion_coeff_unique (f := fMF) one_pos one_mem_strictPeriods_Γ02
      hf_hasSum m).symm
  obtain ⟨c, hc⟩ := structure_Gamma02_dvd 2 1 fMF hf_W
    (fun m => ⟨e4Coeff m + if 2 ∣ m then 4 * e4Coeff (m / 2) else 0, by rw [hf_q m]; simp⟩)
  have hform : ∀ z : ℍ, f z = (c 0 : ℂ) * E2star z ^ 2 := fun z => by
    have hz : f z = ∑ j ∈ Finset.range (2 / 4 + 1),
        (((1 : ℤ) : ℂ) * (c j : ℂ)) * Delta8 z ^ j * E2star z ^ (2 - 4 * j) := hc z
    rw [show (2 : ℕ) / 4 + 1 = 1 by decide, Finset.range_one, Finset.sum_singleton] at hz
    simpa [fMF] using hz
  have hc0 : (c 0 : ℂ) = 5 := by
    have hqeq : qExpansion 1 (fMF : ℍ → ℂ) = (c 0 : ℂ) • (qExpansion 1 (E2starMF : ℍ → ℂ) ^ 2) := by
      have hfn : (fMF : ℍ → ℂ) = (c 0 : ℂ) • ((E2starMF.pow 2 : ModularForm Γ02 _) : ℍ → ℂ) := by
        ext z; simp only [Pi.smul_apply, smul_eq_mul, ModularForm.coe_pow]; exact hform z
      rw [hfn, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_Γ02,
        ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_Γ02]
    have h0 := congrArg (PowerSeries.coeff 0) hqeq
    rw [hf_q 0, PowerSeries.coeff_smul, PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
      ← PowerSeries.coeff_zero_eq_constantCoeff, E2star_qExpansion_coeff 0] at h0
    simp [e4Coeff, e2starCoeff] at h0
    linear_combination -h0
  have hres := hform τ
  rw [hc0] at hres
  exact hres

private lemma H4_sq_eq (τ : ℍ) : H4 τ ^ 2 = E2star τ ^ 4 - 256 * Delta8 τ := by
  let H4sq : ModularForm Γ02 (2 * ((4 : ℕ) : ℤ)) := ModularForm.mcast (by norm_num) (H4MF.mul H4MF)
  have hH4sq_coe : (H4sq : ℍ → ℂ) = fun z => H4 z ^ 2 := by
    ext z; change H4 z * H4 z = H4 z ^ 2; ring
  have hH4sq_W : (H4sq : ℍ → ℂ) ∣[2 * ((4 : ℕ) : ℤ)] W2 = ((-1 : ℂ) ^ 4) • (H4sq : ℍ → ℂ) := by
    ext z
    rw [hH4sq_coe, slash_W2_even ((4 : ℕ) : ℤ)]
    have h1 := congrFun H4_slash_W2 z
    have hW4 : (H4 ∣[(4 : ℤ)] W2) z = H4 (W2 • z) * (2 * (z : ℂ) ^ 2) ^ (-2 : ℤ) := by
      simpa using slash_W2_even 2 H4 z
    rw [hW4] at h1
    have hsq := congrArg (fun x : ℂ => x ^ 2) h1
    simp only [Pi.neg_apply, neg_sq, mul_pow] at hsq
    have hpow : ((2 * (z : ℂ) ^ 2) ^ (-2 : ℤ)) ^ 2 = (2 * (z : ℂ) ^ 2) ^ (-4 : ℤ) := by
      rw [← zpow_natCast, ← zpow_mul]; norm_num
    rw [hpow] at hsq
    simp only [Pi.smul_apply, smul_eq_mul, show ((-1 : ℂ) ^ 4) = 1 by norm_num, one_mul]
    simpa using hsq
  have hH4sq_q : qExpansion 1 (H4sq : ℍ → ℂ) = qExpansion 1 (H4MF : ℍ → ℂ) ^ 2 := by
    rw [sq]
    simpa [H4sq] using ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_Γ02 H4MF H4MF
  have hH4sq_int : ∀ m, ∃ a : ℤ, (qExpansion 1 (H4sq : ℍ → ℂ)).coeff m = (1 : ℤ) * a := by
    intro m
    rw [hH4sq_q, sq]
    exact powerSeries_mul_dvd_int (d := 1)
      (fun k => ⟨h4Coeff k, by rw [H4_qExpansion_coeff k]; simp⟩)
      (fun k => ⟨h4Coeff k, H4_qExpansion_coeff k⟩) m
  obtain ⟨c, hc⟩ := structure_Gamma02_dvd 4 1 H4sq hH4sq_W hH4sq_int
  have hform : ∀ z : ℍ, H4 z ^ 2 = (c 0 : ℂ) * E2star z ^ 4 + (c 1 : ℂ) * Delta8 z := fun z => by
    have hz := hc z
    rw [show (4 : ℕ) / 4 + 1 = 2 by decide, Finset.sum_range_succ, Finset.range_one,
      Finset.sum_singleton] at hz
    change H4 z * H4 z = _ at hz
    rw [← sq] at hz
    simpa [add_comm] using hz
  have hqeq : qExpansion 1 (H4sq : ℍ → ℂ) =
      (c 0 : ℂ) • (qExpansion 1 (E2starMF : ℍ → ℂ) ^ 4) +
      (c 1 : ℂ) • qExpansion 1 (Delta8MF : ℍ → ℂ) := by
    let e4 : ModularForm Γ02 8 := ModularForm.mcast (by norm_num) (E2starMF.pow 4)
    have hfn : (H4sq : ℍ → ℂ) = ((c 0 : ℂ) • e4 : ModularForm Γ02 8) +
        ((c 1 : ℂ) • Delta8MF : ModularForm Γ02 8) := by
      ext z
      change H4 z * H4 z = (c 0 : ℂ) * E2star z ^ 4 + (c 1 : ℂ) * Delta8 z
      rw [← sq]; exact hform z
    rw [hfn, ModularForm.qExpansion_add one_pos one_mem_strictPeriods_Γ02]
    have hs1 : (((c 0 : ℂ) • e4 : ModularForm Γ02 8) : ℍ → ℂ) = (c 0 : ℂ) • (e4 : ℍ → ℂ) := rfl
    have hs2 : (((c 1 : ℂ) • Delta8MF : ModularForm Γ02 8) : ℍ → ℂ) = (c 1 : ℂ) • (Delta8MF : ℍ → ℂ) := rfl
    rw [hs1, hs2, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_Γ02,
      ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_Γ02]
    congr 2
    simpa [e4] using ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_Γ02 E2starMF 4
  have hH0 : (qExpansion 1 (H4MF : ℍ → ℂ)).coeff 0 = 1 := by
    rw [H4_qExpansion_coeff 0]; simp [h4Coeff]
  have hH1 : (qExpansion 1 (H4MF : ℍ → ℂ)).coeff 1 = -80 := by
    rw [H4_qExpansion_coeff 1]
    simp [h4Coeff, show σ 3 1 = 1 by decide]
  have hE0 : (qExpansion 1 (E2starMF : ℍ → ℂ)).coeff 0 = 1 := by
    rw [E2star_qExpansion_coeff 0]; simp [e2starCoeff]
  have hE1 : (qExpansion 1 (E2starMF : ℍ → ℂ)).coeff 1 = 24 := by
    rw [E2star_qExpansion_coeff 1]
    simp [e2starCoeff, show σ 1 1 = 1 by decide]
  have coeff_pow_zero : ∀ (F : PowerSeries ℂ) (n : ℕ), (F ^ n).coeff 0 = F.coeff 0 ^ n := fun F n => by
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff]
  have coeff_pow_one : ∀ (F : PowerSeries ℂ) (n : ℕ),
      (F ^ n).coeff 1 = (n : ℂ) * F.coeff 0 ^ (n - 1) * F.coeff 1 := fun F n => by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton]
      simp only [Nat.sub_zero, Nat.sub_self, coeff_pow_zero, ih]
      cases n with
      | zero => simp
      | succ n =>
        rw [show n + 1 - 1 = n by omega, show n + 1 + 1 - 1 = n + 1 by omega, pow_succ]
        push_cast; ring
  have hc0 : (c 0 : ℂ) = 1 := by
    have h0 := congrArg (PowerSeries.coeff 0) hqeq
    rw [hH4sq_q, map_add, PowerSeries.coeff_smul, PowerSeries.coeff_smul, smul_eq_mul, smul_eq_mul,
      coeff_pow_zero, coeff_pow_zero, hH0, hE0, Delta8_qExpansion_coeff_zero] at h0
    linear_combination -h0
  have hc1 : (c 1 : ℂ) = -256 := by
    have h1 := congrArg (PowerSeries.coeff 1) hqeq
    rw [hH4sq_q, map_add, PowerSeries.coeff_smul, PowerSeries.coeff_smul, smul_eq_mul, smul_eq_mul,
      coeff_pow_one, coeff_pow_one, hH0, hH1, hE0, hE1, Delta8_qExpansion_coeff_one, hc0] at h1
    norm_num at h1
    linear_combination -h1
  have hres := hform τ
  rw [hc0, hc1] at hres
  linear_combination hres

/- #### Closed Ramanujan ODE system on $\Gamma_0(2)$ -/

private noncomputable def P_ser (τ : ℍ) : ℂ := (E2 τ + 2 * E2 (mul2 τ)) / 3

private def pSerCoeff (m : ℕ) : ℤ :=
  if m = 0 then 1
  else -8 * (σ 1 m : ℤ) - (if 2 ∣ m then 16 * (σ 1 (m / 2) : ℤ) else 0)

private lemma P_ser_hasSum_qExpansion (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (pSerCoeff m : ℂ) • Periodic.qParam 1 τ ^ m) (P_ser τ) := by
  have h1 := hasSum_qExpansion_E2 (z := τ)
  have h2 := hasSum_qExpansion_E2 (z := mul2 τ)
  have hq2 : ∀ k : ℕ, cexp (2 * π * I * (mul2 τ : ℂ)) ^ k = Periodic.qParam 1 τ ^ (2 * k) := fun k => by
    simp only [coe_mul2, qParam_one_eq_cexp, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have h1' : HasSum (fun m : ℕ ↦ (if m = 0 then 1 else -24 * (σ 1 m : ℂ)) • Periodic.qParam 1 τ ^ m)
      (E2 τ) := by simpa only [qParam_one_eq_cexp] using h1
  have h2_ev : HasSum (fun m : ℕ ↦
      (if 2 ∣ m then (if m / 2 = 0 then 1 else -24 * (σ 1 (m / 2) : ℂ)) else 0) •
        Periodic.qParam 1 τ ^ m) (E2 (mul2 τ)) := by
    have hinj : Function.Injective (fun k : ℕ ↦ 2 * k) := fun a b hab => by dsimp at hab; omega
    rw [← hinj.hasSum_iff (f := fun m : ℕ ↦
      (if 2 ∣ m then (if m / 2 = 0 then 1 else -24 * (σ 1 (m / 2) : ℂ)) else 0) •
        Periodic.qParam 1 τ ^ m)]
    · convert h2 using 1
      ext k
      have hk2 : 2 ∣ 2 * k := ⟨k, rfl⟩
      have hdiv : (2 * k) / 2 = k := Nat.mul_div_right k two_pos
      dsimp only [Function.comp_apply]
      rw [if_pos hk2, hdiv, hq2 k]
    · intro m hm
      have hnd : ¬ 2 ∣ m := fun ⟨k, hk⟩ => hm ⟨k, hk.symm⟩
      simp [hnd]
  have hcomb := (h1'.add (h2_ev.mul_left 2)).mul_left (3 : ℂ)⁻¹
  have hval : (3 : ℂ)⁻¹ * (E2 τ + 2 * E2 (mul2 τ)) = P_ser τ := by simp [P_ser, div_eq_inv_mul]
  rw [hval] at hcomb
  refine hcomb.congr_fun fun m => ?_
  simp only [pSerCoeff, smul_eq_mul]
  by_cases hm : m = 0
  · subst hm; simp; ring
  · by_cases hd : 2 ∣ m
    · have hne : m / 2 ≠ 0 := by obtain ⟨k, hk⟩ := hd; omega
      simp [hm, hd, hne]; ring
    · simp [hm, hd]; ring

private lemma P_ser_periodic : Periodic (P_ser ∘ ofComplex) 1 := by
  intro z
  by_cases hz : 0 < z.im
  · have hz1 : 0 < (z + 1).im := by simpa using hz
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos hz1]
    have h1 := E2_periodic z
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos hz1] at h1
    have h2a := E2_periodic (2 * z)
    have h2b := E2_periodic (2 * z + 1)
    have h2z : 0 < (2 * z).im := by simpa using mul_pos two_pos hz
    have h2z1 : 0 < (2 * z + 1).im := by simpa using h2z
    have h2z2 : 0 < (2 * z + 1 + 1).im := by simpa using h2z
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos h2z, ofComplex_apply_of_im_pos h2z1,
      ofComplex_apply_of_im_pos h2z2] at h2a h2b
    have hm2 : mul2 ⟨z + 1, hz1⟩ = ⟨2 * z + 1 + 1, h2z2⟩ := by ext; simp [coe_mul2]; ring
    have hm1 : mul2 ⟨z, hz⟩ = ⟨2 * z, h2z⟩ := by ext; simp [coe_mul2]
    simp only [P_ser, h1, hm2, hm1, h2b, h2a]
  · have hz1 : ¬ 0 < (z + 1).im := by simpa using hz
    simp only [Function.comp_apply, ofComplex_apply_of_im_nonpos (not_lt.mp hz),
      ofComplex_apply_of_im_nonpos (not_lt.mp hz1)]

private lemma P_ser_mdiff : MDiff P_ser := by
  have hEq : P_ser = fun z => (E2 z + (2 : ℂ) * E2 (mul2 z)) * (3 : ℂ)⁻¹ := by
    ext z; simp [P_ser, div_eq_mul_inv]
  rw [hEq]
  exact (E2_mdifferentiable.add (mdifferentiable_const.mul (mdiff_comp_mul2 E2_mdifferentiable))).mul
    mdifferentiable_const

private lemma P_ser_bdd : IsBoundedAtImInfty P_ser :=
  isBoundedAtImInfty_of_hasSum_qExpansion one_pos P_ser_hasSum_qExpansion

private lemma P_ser_qExpansion_coeff (m : ℕ) :
    (qExpansion 1 P_ser).coeff m = (pSerCoeff m : ℂ) := by
  have hana : AnalyticAt ℂ (cuspFunction 1 P_ser) 0 :=
    (UpperHalfPlane.differentiableOn_cuspFunction_ball one_pos P_ser_periodic
      P_ser_mdiff P_ser_bdd).analyticAt (Metric.ball_mem_nhds (0 : ℂ) one_pos)
  exact (qExpansion_coeff_unique_fun (c := fun n => (pSerCoeff n : ℂ))
    hana P_ser_hasSum_qExpansion m).symm

private lemma nD_comp_mul2 {f : ℍ → ℂ} (hf : MDiff f) (τ : ℍ) :
    nD (fun z : ℍ ↦ f (mul2 z)) τ = 2 * nD f (mul2 τ) := by
  have hft : HasDerivAt (f ∘ ofComplex) (deriv (f ∘ ofComplex) (mul2 τ : ℂ)) (mul2 τ : ℂ) :=
    (UpperHalfPlane.mdifferentiableAt_iff.mp (hf (mul2 τ))).hasDerivAt
  have h2 : HasDerivAt (fun z : ℂ ↦ 2 * z) 2 (τ : ℂ) := by
    simpa using (hasDerivAt_id (τ : ℂ)).const_mul (2 : ℂ)
  have hcomp : ((fun z : ℍ ↦ f (mul2 z)) ∘ ofComplex) =ᶠ[𝓝 (τ : ℂ)]
      ((f ∘ ofComplex) ∘ fun z : ℂ ↦ 2 * z) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
    have hz2 : 0 < (2 * z).im := by simpa using mul_pos two_pos hz
    simp [Function.comp_apply, mul2, ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos hz2]
  have hd := ((hft.comp (τ : ℂ) h2).congr_of_eventuallyEq hcomp).deriv
  simp only [nD, Derivative.normalizedDerivOfComplex, hd]
  ring

private lemma nD_Delta8_eq (τ : ℍ) : nD Delta8 τ = P_ser τ * Delta8 τ := by
  have h1 : HasDerivAt ModularForm.eta ((π * I / 12) * E2 τ * ModularForm.eta τ) (τ : ℂ) := by
    have hlog := ModularForm.logDeriv_eta_eq_E2 τ
    have hd := (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet τ.im_pos).hasDerivAt
    have hne : ModularForm.eta τ ≠ 0 := ModularForm.eta_ne_zero τ.im_pos
    simp only [logDeriv_apply] at hlog
    have hval : deriv ModularForm.eta τ = (π * I / 12) * E2 τ * ModularForm.eta τ := by
      have hm := congrArg (· * ModularForm.eta τ) hlog
      rwa [div_mul_cancel₀ _ hne] at hm
    rwa [← hval]
  have h2 : HasDerivAt (fun z : ℂ ↦ ModularForm.eta (2 * z))
      (2 * ((π * I / 12) * E2 (mul2 τ) * ModularForm.eta (mul2 τ))) (τ : ℂ) := by
    have hlog := ModularForm.logDeriv_eta_eq_E2 (mul2 τ)
    have hd := (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet (mul2 τ).im_pos).hasDerivAt
    have hne : ModularForm.eta (mul2 τ) ≠ 0 := ModularForm.eta_ne_zero (mul2 τ).im_pos
    simp only [logDeriv_apply] at hlog
    have hval : deriv ModularForm.eta (mul2 τ) = (π * I / 12) * E2 (mul2 τ) * ModularForm.eta (mul2 τ) := by
      have hm := congrArg (· * ModularForm.eta (mul2 τ)) hlog
      rwa [div_mul_cancel₀ _ hne] at hm
    have hlin : HasDerivAt (fun z : ℂ ↦ 2 * z) 2 (τ : ℂ) := by
      simpa using (hasDerivAt_id (τ : ℂ)).const_mul (2 : ℂ)
    have hc := hd.comp (τ : ℂ) hlin
    rw [hval] at hc
    have hfun : (fun z : ℂ ↦ ModularForm.eta (2 * z)) = ModularForm.eta ∘ (fun z : ℂ ↦ 2 * z) := rfl
    rw [hfun]
    exact hc.congr_deriv (by ring)
  have hprod := (h1.pow 8).mul (h2.pow 8)
  have hcomp : (Delta8 ∘ ofComplex) =ᶠ[𝓝 (τ : ℂ)]
      fun z : ℂ ↦ ModularForm.eta z ^ 8 * ModularForm.eta (2 * z) ^ 8 := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz, Delta8, eta4, coe_mul2]
    ring
  have hd := (hprod.congr_of_eventuallyEq hcomp).deriv
  simp only [nD, Derivative.normalizedDerivOfComplex, hd, Delta8, eta4, P_ser, coe_mul2, Pi.pow_apply]
  have hne : (2 * π * I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  field_simp [hne]
  ring

private lemma nD_E2star_eq (τ : ℍ) : nD E2star τ = (P_ser τ * E2star τ - H4 τ) / 4 := by
  have hdef : E2star = (2 : ℂ) • (fun z => E2 (mul2 z)) - E2 := by ext z; simp [E2star]
  have h1 := congrFun (Derivative.normalizedDerivOfComplex_sub _ _
    ((mdiff_comp_mul2 E2_mdifferentiable).const_smul (2 : ℂ)) E2_mdifferentiable) τ
  have h2 := congrFun (Derivative.normalizedDerivOfComplex_smul (2 : ℂ) _
    (mdiff_comp_mul2 E2_mdifferentiable)) τ
  change nD ((2 : ℂ) • (fun z => E2 (mul2 z)) - E2) τ = _ at h1
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  rw [← hdef, h2] at h1
  have h3 : Derivative.normalizedDerivOfComplex (fun z => E2 (mul2 z)) τ = 2 * nD E2 (mul2 τ) :=
    nD_comp_mul2 E2_mdifferentiable τ
  have h4 : Derivative.normalizedDerivOfComplex E2 τ = (E2 τ ^ 2 - E₄ τ) / 12 := nD_E2_eq τ
  rw [h1, h3, nD_E2_eq (mul2 τ), h4]
  simp only [P_ser, E2star, H4, E4_2]
  ring

private lemma nD_P_ser_eq (τ : ℍ) : nD P_ser τ = (P_ser τ ^ 2 - E2star τ ^ 2) / 8 := by
  have hdef : P_ser = (1 / 3 : ℂ) • (E2 + (2 : ℂ) • (fun z => E2 (mul2 z))) := by
    ext z; simp [P_ser]; ring
  have h1 := congrFun (Derivative.normalizedDerivOfComplex_smul (1 / 3 : ℂ) _
    (E2_mdifferentiable.add ((mdiff_comp_mul2 E2_mdifferentiable).const_smul (2 : ℂ)))) τ
  have h2 := congrFun (Derivative.normalizedDerivOfComplex_add E2 _
    E2_mdifferentiable ((mdiff_comp_mul2 E2_mdifferentiable).const_smul (2 : ℂ))) τ
  have h3 := congrFun (Derivative.normalizedDerivOfComplex_smul (2 : ℂ) _
    (mdiff_comp_mul2 E2_mdifferentiable)) τ
  change nD ((1 / 3 : ℂ) • (E2 + (2 : ℂ) • (fun z => E2 (mul2 z)))) τ = _ at h1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3
  rw [← hdef, h2, h3] at h1
  have h4 : Derivative.normalizedDerivOfComplex (fun z => E2 (mul2 z)) τ = 2 * nD E2 (mul2 τ) :=
    nD_comp_mul2 E2_mdifferentiable τ
  have h5 : Derivative.normalizedDerivOfComplex E2 τ = (E2 τ ^ 2 - E₄ τ) / 12 := nD_E2_eq τ
  rw [h1, h4, nD_E2_eq (mul2 τ), h5]
  have hE4 := E4_add_four_E4_2 τ
  simp only [P_ser, E2star] at hE4 ⊢
  linear_combination -(1 / 36 : ℂ) * hE4

/- #### Integer power series lifts and formal Picard-Fuchs ODE modulo `(p^2, q^p)` -/

private noncomputable def thetaQ {R : Type*} [CommRing R] (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.X * PowerSeries.derivative R f

private lemma coeff_thetaQ {R : Type*} [CommRing R] (f : PowerSeries R) (n : ℕ) :
    (thetaQ f).coeff n = (n : R) * f.coeff n := by
  cases n with
  | zero => simp [thetaQ]
  | succ n =>
    simp [thetaQ, PowerSeries.coeff_derivative, mul_comm]

private lemma thetaQ_zero {R : Type*} [CommRing R] : thetaQ (0 : PowerSeries R) = 0 := by
  ext n; simp [coeff_thetaQ]

private lemma thetaQ_C {R : Type*} [CommRing R] (r : R) :
    thetaQ (PowerSeries.C r) = 0 := by
  simp [thetaQ]

private lemma thetaQ_one {R : Type*} [CommRing R] : thetaQ (1 : PowerSeries R) = 0 := by
  rw [← map_one (PowerSeries.C (R := R))]; exact thetaQ_C _

private lemma thetaQ_nat {R : Type*} [CommRing R] (k : ℕ) :
    thetaQ (k : PowerSeries R) = 0 := by
  rw [← map_natCast (PowerSeries.C (R := R)) k]; exact thetaQ_C _

private lemma thetaQ_ofNat {R : Type*} [CommRing R] (k : ℕ) [k.AtLeastTwo] :
    thetaQ (ofNat(k) : PowerSeries R) = 0 := by
  rw [← map_ofNat (PowerSeries.C (R := R)) k]; exact thetaQ_C _

private lemma thetaQ_ofNat_mul {R : Type*} [CommRing R] (k : ℕ) [k.AtLeastTwo] (f : PowerSeries R) :
    thetaQ (ofNat(k) * f) = ofNat(k) * thetaQ f := by
  rw [← map_ofNat (PowerSeries.C (R := R)) k]
  ext n; simp only [coeff_thetaQ, PowerSeries.coeff_C_mul]; ring

private lemma thetaQ_add {R : Type*} [CommRing R] (f g : PowerSeries R) :
    thetaQ (f + g) = thetaQ f + thetaQ g := by
  ext n; simp [coeff_thetaQ, mul_add]

private lemma thetaQ_sub {R : Type*} [CommRing R] (f g : PowerSeries R) :
    thetaQ (f - g) = thetaQ f - thetaQ g := by
  ext n; simp [coeff_thetaQ, mul_sub]


private lemma thetaQ_C_mul {R : Type*} [CommRing R] (r : R) (f : PowerSeries R) :
    thetaQ (PowerSeries.C r * f) = PowerSeries.C r * thetaQ f := by
  ext n; simp [coeff_thetaQ]; ring

private lemma thetaQ_mul {R : Type*} [CommRing R] (f g : PowerSeries R) :
    thetaQ (f * g) = thetaQ f * g + f * thetaQ g := by
  simp only [thetaQ, Derivation.leibniz, smul_eq_mul]; ring

private lemma thetaQ_pow {R : Type*} [CommRing R] (f : PowerSeries R) (n : ℕ) :
    thetaQ (f ^ n) = (n : PowerSeries R) * f ^ (n - 1) * thetaQ f := by
  simp only [thetaQ, PowerSeries.derivative_pow]; ring

private lemma thetaQ_X {R : Type*} [CommRing R] :
    thetaQ (PowerSeries.X : PowerSeries R) = PowerSeries.X := by
  simp [thetaQ]

private lemma thetaQ_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f : PowerSeries R) :
    thetaQ (f.map φ) = (thetaQ f).map φ := by
  ext n; simp [coeff_thetaQ]

private def E2star_ps_int : PowerSeries ℤ := PowerSeries.mk e2starCoeff
private def H4_ps_int : PowerSeries ℤ := PowerSeries.mk h4Coeff
private def P_ps_int : PowerSeries ℤ := PowerSeries.mk pSerCoeff

private lemma E2star_ps_int_map_C :
    E2star_ps_int.map (Int.castRingHom ℂ) = qExpansion 1 (E2starMF : ℍ → ℂ) := by
  ext m; simp [E2star_ps_int, E2star_qExpansion_coeff]

private lemma H4_ps_int_map_C :
    H4_ps_int.map (Int.castRingHom ℂ) = qExpansion 1 (H4MF : ℍ → ℂ) := by
  ext m; simp [H4_ps_int, H4_qExpansion_coeff]

private lemma P_ps_int_map_C :
    P_ps_int.map (Int.castRingHom ℂ) = qExpansion 1 P_ser := by
  ext m; simp [P_ps_int, P_ser_qExpansion_coeff]

private noncomputable def eta4_prod_fn (q : ℂ) : ℂ :=
  (∏' n : ℕ, (1 - (q ^ 1) ^ (n + 1)) ^ 4) * (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) ^ 4)

private lemma eta4_prod_taylor_int (m : ℕ) :
    ∃ a : ℤ, ((m.factorial : ℂ)⁻¹ * iteratedDeriv m eta4_prod_fn 0) = a := by
  let f1 : ℂ → ℂ := fun q => ∏' n : ℕ, (1 - (q ^ 1) ^ (n + 1)) ^ 4
  let f2 : ℂ → ℂ := fun q => ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) ^ 4
  have hf1_ana : AnalyticAt ℂ f1 0 :=
    ((ModularForm.differentiableOn_tprod_one_sub_pow_pow 4).congr fun q _ => by simp [f1]).analyticAt
      (Metric.ball_mem_nhds (0 : ℂ) one_pos)
  have hf2_ana : AnalyticAt ℂ f2 0 :=
    ((ModularForm.differentiableOn_tprod_one_sub_pow_pow 4).comp
      (differentiable_pow 2).differentiableOn fun q hq => by
        rw [mem_ball_zero_iff, norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp hq) two_ne_zero).analyticAt
      (Metric.ball_mem_nhds (0 : ℂ) one_pos)
  have hfn : eta4_prod_fn = f1 * f2 := rfl
  rw [hfn, iteratedDeriv_mul (hf1_ana.contDiffAt.of_le le_top) (hf2_ana.contDiffAt.of_le le_top)]
  have hsum : ((m.factorial : ℂ)⁻¹ * ∑ i ∈ Finset.range (m + 1),
      (m.choose i : ℂ) * iteratedDeriv i f1 0 * iteratedDeriv (m - i) f2 0) =
      ∑ i ∈ Finset.range (m + 1),
        ((i.factorial : ℂ)⁻¹ * iteratedDeriv i f1 0) *
        (((m - i).factorial : ℂ)⁻¹ * iteratedDeriv (m - i) f2 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [Nat.cast_choose (K := ℂ) him]
    field_simp [Nat.factorial_ne_zero]
  rw [hsum]
  have hterm : ∀ i ∈ Finset.range (m + 1), ∃ a : ℤ,
      ((i.factorial : ℂ)⁻¹ * iteratedDeriv i f1 0) *
        (((m - i).factorial : ℂ)⁻¹ * iteratedDeriv (m - i) f2 0) = a := by
    intro i _
    obtain ⟨a1, ha1⟩ := tprod_one_sub_pow_taylor_int 1 4 one_pos i
    obtain ⟨a2, ha2⟩ := tprod_one_sub_pow_taylor_int 2 4 two_pos (m - i)
    exact ⟨a1 * a2, by rw [ha1, ha2, Int.cast_mul]⟩
  choose a ha using hterm
  refine ⟨∑ i ∈ (Finset.range (m + 1)).attach, a i.1 i.2, ?_⟩
  rw [Int.cast_sum, ← Finset.sum_attach (Finset.range (m + 1))]
  exact Finset.sum_congr rfl fun i _ => ha i.1 i.2

private noncomputable def eta4_prod_ps_int : PowerSeries ℤ :=
  PowerSeries.mk fun m => Classical.choose (eta4_prod_taylor_int m)

private lemma eta4_prod_ps_int_coeff_C (m : ℕ) :
    (eta4_prod_ps_int.coeff m : ℂ) = (m.factorial : ℂ)⁻¹ * iteratedDeriv m eta4_prod_fn 0 := by
  simp only [eta4_prod_ps_int, PowerSeries.coeff_mk]
  exact (Classical.choose_spec (eta4_prod_taylor_int m)).symm

private lemma eta4_prod_ps_int_coeff_zero : eta4_prod_ps_int.coeff 0 = 1 := by
  apply Int.cast_injective (α := ℂ)
  rw [eta4_prod_ps_int_coeff_C 0]
  simp [eta4_prod_fn]

private noncomputable def Delta8_ps_int : PowerSeries ℤ := PowerSeries.X * eta4_prod_ps_int ^ 2

private lemma Delta8_ps_int_map_C :
    Delta8_ps_int.map (Int.castRingHom ℂ) = qExpansion 1 (Delta8MF : ℍ → ℂ) := by
  have heta_ana : AnalyticAt ℂ eta4_prod_fn 0 := by
    have hf1 : DifferentiableOn ℂ (fun q : ℂ ↦ ∏' n : ℕ, (1 - (q ^ 1) ^ (n + 1)) ^ 4) (Metric.ball 0 1) :=
      (ModularForm.differentiableOn_tprod_one_sub_pow_pow 4).congr fun q _ => by simp
    have hf2 : DifferentiableOn ℂ (fun q : ℂ ↦ ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) ^ 4) (Metric.ball 0 1) :=
      (ModularForm.differentiableOn_tprod_one_sub_pow_pow 4).comp
        (differentiable_pow 2).differentiableOn fun q hq => by
          rw [mem_ball_zero_iff, norm_pow]
          exact pow_lt_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp hq) two_ne_zero
    exact (hf1.mul hf2).analyticAt (Metric.ball_mem_nhds (0 : ℂ) one_pos)
  have hcusp : cuspFunction 1 Delta8 =ᶠ[𝓝 (0 : ℂ)] ((id : ℂ → ℂ) * (eta4_prod_fn * eta4_prod_fn)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with q hq
    rw [Delta8_cuspFunction_eqOn hq]
    simp only [Pi.mul_apply, id_eq, eta4_prod_fn]
    have hq1 : ‖q‖ < 1 := mem_ball_zero_iff.mp hq
    have hq2 : ‖q ^ 2‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq1 two_ne_zero
    have mp1 := ModularForm.multipliable_one_sub_pow hq1
    have mp2 := ModularForm.multipliable_one_sub_pow hq2
    have h1 : (∏' n : ℕ, (1 - q ^ (n + 1)) ^ 8) = (∏' n : ℕ, (1 - (q ^ 1) ^ (n + 1)) ^ 4) ^ 2 := by
      simp_rw [pow_one]
      rw [mp1.tprod_pow 8, mp1.tprod_pow 4, ← pow_mul]
    have h2 : (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) ^ 8) = (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) ^ 4) ^ 2 := by
      rw [mp2.tprod_pow 8, mp2.tprod_pow 4, ← pow_mul]
    rw [h1, h2]; ring
  ext m
  cases m with
  | zero =>
    simp [Delta8_ps_int, Delta8_qExpansion_coeff_zero]
  | succ m =>
    rw [Delta8_ps_int, map_mul, PowerSeries.map_X, map_pow,
      PowerSeries.coeff_succ_X_mul, sq, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [qExpansion_coeff]
    change _ = ((m + 1).factorial : ℂ)⁻¹ * iteratedDeriv (m + 1) (cuspFunction 1 Delta8) 0
    rw [hcusp.iteratedDeriv_eq, iteratedDeriv_mul contDiffAt_id
      ((heta_ana.mul heta_ana).contDiffAt.of_le le_top)]
    rw [Finset.sum_eq_single (s := Finset.range (m + 1 + 1)) 1]
    · have hid1 : iteratedDeriv 1 (id : ℂ → ℂ) 0 = 1 := by simp
      rw [hid1, Nat.choose_one_right, Nat.add_sub_cancel, mul_one]
      rw [iteratedDeriv_mul (heta_ana.contDiffAt.of_le le_top) (heta_ana.contDiffAt.of_le le_top)]
      have hfac : (((m + 1).factorial : ℂ)⁻¹ * ((m + 1 : ℕ) : ℂ)) = (m.factorial : ℂ)⁻¹ := by
        rw [Nat.factorial_succ, Nat.cast_mul]; field_simp [Nat.factorial_ne_zero]
      rw [← mul_assoc, hfac, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [PowerSeries.coeff_map, PowerSeries.coeff_map, Int.coe_castRingHom]
      dsimp only
      rw [eta4_prod_ps_int_coeff_C i, eta4_prod_ps_int_coeff_C (m - i),
        Nat.cast_choose (K := ℂ) him]
      field_simp [Nat.factorial_ne_zero]
    · intro i _ hne
      rcases i with _ | _ | i
      · simp
      · exact absurd rfl hne
      · have : iteratedDeriv (i + 2) (id : ℂ → ℂ) 0 = 0 := by
          rw [iteratedDeriv_succ', deriv_id', iteratedDeriv_const, if_neg (by omega)]
        simp [this]
    · intro hnot
      exact absurd (Finset.mem_range.mpr (Nat.succ_lt_succ (Nat.succ_pos m))) hnot

private lemma isUnit_of_coeff_zero_one {R : Type*} [CommRing R] {f : PowerSeries R}
    (hf : f.coeff 0 = 1) : IsUnit f := by
  rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff, hf]
  exact isUnit_one

private lemma E2star_ps_int_coeff_zero : E2star_ps_int.coeff 0 = 1 := by
  simp [E2star_ps_int, e2starCoeff]

private lemma H4_ps_int_coeff_zero : H4_ps_int.coeff 0 = 1 := by
  simp [H4_ps_int, h4Coeff]

private noncomputable def E2star_ps_int_inv : PowerSeries ℤ :=
  ((isUnit_of_coeff_zero_one E2star_ps_int_coeff_zero).unit⁻¹ : (PowerSeries ℤ)ˣ)

private lemma E2star_ps_int_mul_inv : E2star_ps_int * E2star_ps_int_inv = 1 :=
  (isUnit_of_coeff_zero_one E2star_ps_int_coeff_zero).unit.mul_inv

private noncomputable def U_ps_int : PowerSeries ℤ := eta4_prod_ps_int * E2star_ps_int_inv ^ 2

private noncomputable def u0_ps_int : PowerSeries ℤ := PowerSeries.X * U_ps_int ^ 2

private lemma U_ps_int_coeff_zero : U_ps_int.coeff 0 = 1 := by
  have hinv0 : E2star_ps_int_inv.coeff 0 = 1 := by
    have h := congrArg PowerSeries.constantCoeff E2star_ps_int_mul_inv
    rw [map_mul, map_one, ← PowerSeries.coeff_zero_eq_constantCoeff, E2star_ps_int_coeff_zero,
      one_mul] at h
    exact h
  rw [U_ps_int, PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_pow,
    ← PowerSeries.coeff_zero_eq_constantCoeff, eta4_prod_ps_int_coeff_zero, hinv0]
  norm_num

private lemma u0_ps_int_coeff_zero : u0_ps_int.coeff 0 = 0 := by
  simp [u0_ps_int]

private lemma u0_ps_int_coeff_one : u0_ps_int.coeff 1 = 1 := by
  rw [u0_ps_int, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
    ← PowerSeries.coeff_zero_eq_constantCoeff, U_ps_int_coeff_zero, one_pow]

private lemma u0_mul_E2star_pow_four : u0_ps_int * E2star_ps_int ^ 4 = Delta8_ps_int := by
  calc u0_ps_int * E2star_ps_int ^ 4
      = PowerSeries.X * eta4_prod_ps_int ^ 2 * (E2star_ps_int * E2star_ps_int_inv) ^ 4 := by
        simp only [u0_ps_int, U_ps_int]; ring
    _ = PowerSeries.X * eta4_prod_ps_int ^ 2 := by rw [E2star_ps_int_mul_inv, one_pow, mul_one]
    _ = Delta8_ps_int := rfl

private lemma int_map_inj {f g : PowerSeries ℤ}
    (h : f.map (Int.castRingHom ℂ) = g.map (Int.castRingHom ℂ)) : f = g := by
  ext m
  apply Int.cast_injective (α := ℂ)
  have := congrArg (PowerSeries.coeff m) h
  simpa using this

private lemma H4_sq_ps_int :
    H4_ps_int ^ 2 = E2star_ps_int ^ 4 - 256 * Delta8_ps_int := by
  apply int_map_inj
  simp only [map_sub, map_pow, map_mul, map_ofNat, H4_ps_int_map_C, E2star_ps_int_map_C,
    Delta8_ps_int_map_C]
  have hH4 : AnalyticAt ℂ (cuspFunction 1 (H4MF : ℍ → ℂ)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero H4MF one_pos one_mem_strictPeriods_Γ02
  have hE : AnalyticAt ℂ (cuspFunction 1 (E2starMF : ℍ → ℂ)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero E2starMF one_pos one_mem_strictPeriods_Γ02
  have hD : AnalyticAt ℂ (cuspFunction 1 (Delta8MF : ℍ → ℂ)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero Delta8MF one_pos one_mem_strictPeriods_Γ02
  have hfn : ((H4MF.mul H4MF : ModularForm Γ02 _) : ℍ → ℂ) =
      ((E2starMF.pow 4 : ModularForm Γ02 _) : ℍ → ℂ) -
        ((256 : ℂ) • Delta8MF : ModularForm Γ02 _) := by
    ext τ
    change H4 τ * H4 τ = E2star τ ^ 4 - 256 * Delta8 τ
    rw [← sq]; exact H4_sq_eq τ
  have hq := congrArg (qExpansion 1) hfn
  have hsm : (((256 : ℂ) • Delta8MF : ModularForm Γ02 _) : ℍ → ℂ) = (256 : ℂ) • (Delta8MF : ℍ → ℂ) := rfl
  rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_Γ02, ← sq,
    ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_Γ02,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_Γ02, hsm,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_Γ02] at hq
  rw [show (256 : PowerSeries ℂ) = PowerSeries.C 256 from (map_ofNat _ 256).symm]
  simpa [PowerSeries.smul_eq_C_mul] using hq

private lemma ode_Delta8_ps_int : thetaQ Delta8_ps_int = P_ps_int * Delta8_ps_int := by
  apply int_map_inj
  rw [← thetaQ_map, map_mul, Delta8_ps_int_map_C, P_ps_int_map_C]
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex Delta8MF one_mem_strictPeriods_Γ02
  have hhol := Delta8MF.holo'
  have hbdd := ModularFormClass.bdd_at_infty Delta8MF
  dsimp [thetaQ]
  rw [← qExpansion_nD hper hhol hbdd]
  have hfn : nD (Delta8MF : ℍ → ℂ) = P_ser * (Delta8MF : ℍ → ℂ) := by
    ext τ; exact nD_Delta8_eq τ
  rw [hfn]
  have hP_ana : AnalyticAt ℂ (cuspFunction 1 P_ser) 0 :=
    (UpperHalfPlane.differentiableOn_cuspFunction_ball one_pos P_ser_periodic
      P_ser_mdiff P_ser_bdd).analyticAt (Metric.ball_mem_nhds (0 : ℂ) one_pos)
  have hD_ana : AnalyticAt ℂ (cuspFunction 1 (Delta8MF : ℍ → ℂ)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero Delta8MF one_pos one_mem_strictPeriods_Γ02
  exact UpperHalfPlane.qExpansion_mul hP_ana hD_ana

private lemma ode_E2star_ps_int :
    4 * thetaQ E2star_ps_int = P_ps_int * E2star_ps_int - H4_ps_int := by
  apply int_map_inj
  rw [map_mul, map_ofNat, ← thetaQ_map, map_sub, map_mul, E2star_ps_int_map_C, P_ps_int_map_C,
    H4_ps_int_map_C]
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex E2starMF one_mem_strictPeriods_Γ02
  have hhol := E2starMF.holo'
  have hbdd := ModularFormClass.bdd_at_infty E2starMF
  dsimp [thetaQ]
  rw [← qExpansion_nD hper hhol hbdd]
  have hP_ana : AnalyticAt ℂ (cuspFunction 1 P_ser) 0 :=
    (UpperHalfPlane.differentiableOn_cuspFunction_ball one_pos P_ser_periodic
      P_ser_mdiff P_ser_bdd).analyticAt (Metric.ball_mem_nhds (0 : ℂ) one_pos)
  have hE_ana : AnalyticAt ℂ (cuspFunction 1 (E2starMF : ℍ → ℂ)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero E2starMF one_pos one_mem_strictPeriods_Γ02
  have hH_ana : AnalyticAt ℂ (cuspFunction 1 (H4MF : ℍ → ℂ)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero H4MF one_pos one_mem_strictPeriods_Γ02
  have hDE_ana : AnalyticAt ℂ (cuspFunction 1 (nD (E2starMF : ℍ → ℂ))) 0 :=
    (UpperHalfPlane.differentiableOn_cuspFunction_ball one_pos (nD_periodic hper hhol hbdd)
      (Derivative.normalizedDerivOfComplex_mdifferentiable hhol)
      (nD_isBoundedAtImInfty hper hhol hbdd)).analyticAt (Metric.ball_mem_nhds (0 : ℂ) one_pos)
  have hPE_ana : AnalyticAt ℂ (cuspFunction 1 (P_ser * (E2starMF : ℍ → ℂ))) 0 := by
    rw [UpperHalfPlane.cuspFunction_mul hP_ana.continuousAt hE_ana.continuousAt]
    exact hP_ana.mul hE_ana
  have hfn : (4 : ℂ) • nD (E2starMF : ℍ → ℂ) = P_ser * (E2starMF : ℍ → ℂ) - (H4MF : ℍ → ℂ) := by
    ext τ
    change 4 * nD E2star τ = P_ser τ * E2star τ - H4 τ
    rw [nD_E2star_eq τ]; ring
  have hq := congrArg (qExpansion 1) hfn
  rw [UpperHalfPlane.qExpansion_smul hDE_ana, UpperHalfPlane.qExpansion_sub hPE_ana hH_ana,
    UpperHalfPlane.qExpansion_mul hP_ana hE_ana] at hq
  rw [show (4 : PowerSeries ℂ) = PowerSeries.C 4 from (map_ofNat _ 4).symm]
  simpa [PowerSeries.smul_eq_C_mul] using hq

private lemma ode_P_ps_int :
    8 * thetaQ P_ps_int = P_ps_int ^ 2 - E2star_ps_int ^ 2 := by
  apply int_map_inj
  rw [map_mul, map_ofNat, ← thetaQ_map, map_sub, map_pow, map_pow, P_ps_int_map_C,
    E2star_ps_int_map_C]
  dsimp [thetaQ]
  rw [← qExpansion_nD P_ser_periodic P_ser_mdiff P_ser_bdd]
  have hP_ana : AnalyticAt ℂ (cuspFunction 1 P_ser) 0 :=
    (UpperHalfPlane.differentiableOn_cuspFunction_ball one_pos P_ser_periodic
      P_ser_mdiff P_ser_bdd).analyticAt (Metric.ball_mem_nhds (0 : ℂ) one_pos)
  have hE_ana : AnalyticAt ℂ (cuspFunction 1 (E2starMF : ℍ → ℂ)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero E2starMF one_pos one_mem_strictPeriods_Γ02
  have hDP_ana : AnalyticAt ℂ (cuspFunction 1 (nD P_ser)) 0 :=
    (UpperHalfPlane.differentiableOn_cuspFunction_ball one_pos
      (nD_periodic P_ser_periodic P_ser_mdiff P_ser_bdd)
      (Derivative.normalizedDerivOfComplex_mdifferentiable P_ser_mdiff)
      (nD_isBoundedAtImInfty P_ser_periodic P_ser_mdiff P_ser_bdd)).analyticAt
        (Metric.ball_mem_nhds (0 : ℂ) one_pos)
  have hP2_ana : AnalyticAt ℂ (cuspFunction 1 (P_ser * P_ser)) 0 := by
    rw [UpperHalfPlane.cuspFunction_mul hP_ana.continuousAt hP_ana.continuousAt]
    exact hP_ana.mul hP_ana
  have hE2_ana : AnalyticAt ℂ (cuspFunction 1 ((E2starMF : ℍ → ℂ) * (E2starMF : ℍ → ℂ))) 0 := by
    rw [UpperHalfPlane.cuspFunction_mul hE_ana.continuousAt hE_ana.continuousAt]
    exact hE_ana.mul hE_ana
  have hfn : (8 : ℂ) • nD P_ser = P_ser * P_ser - (E2starMF : ℍ → ℂ) * (E2starMF : ℍ → ℂ) := by
    ext τ
    change 8 * nD P_ser τ = P_ser τ * P_ser τ - E2star τ * E2star τ
    rw [nD_P_ser_eq τ]; ring
  have hq := congrArg (qExpansion 1) hfn
  rw [UpperHalfPlane.qExpansion_smul hDP_ana, UpperHalfPlane.qExpansion_sub hP2_ana hE2_ana,
    UpperHalfPlane.qExpansion_mul hP_ana hP_ana, UpperHalfPlane.qExpansion_mul hE_ana hE_ana] at hq
  rw [show (8 : PowerSeries ℂ) = PowerSeries.C 8 from (map_ofNat _ 8).symm]
  simpa [PowerSeries.smul_eq_C_mul, sq] using hq

private lemma ode_H4_ps_int :
    2 * thetaQ H4_ps_int = P_ps_int * H4_ps_int - E2star_ps_int ^ 3 := by
  have hdiff := congrArg thetaQ H4_sq_ps_int
  rw [thetaQ_pow, thetaQ_sub, thetaQ_pow, thetaQ_ofNat_mul, ode_Delta8_ps_int] at hdiff
  have hmul : H4_ps_int * (2 * thetaQ H4_ps_int) =
      H4_ps_int * (P_ps_int * H4_ps_int - E2star_ps_int ^ 3) := by
    have hE := ode_E2star_ps_int
    have hsq := H4_sq_ps_int
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one] at hdiff
    linear_combination hdiff + E2star_ps_int ^ 3 * hE - P_ps_int * hsq
  have hHne : H4_ps_int ≠ 0 := by
    intro h0
    have := congrArg (PowerSeries.coeff 0) h0
    simp [H4_ps_int_coeff_zero] at this
  exact mul_left_cancel₀ hHne hmul

private lemma ode_U_ps_int :
    2 * E2star_ps_int * thetaQ U_ps_int = (H4_ps_int - E2star_ps_int) * U_ps_int := by
  have hdiff := congrArg thetaQ u0_mul_E2star_pow_four
  rw [thetaQ_mul, thetaQ_pow, ode_Delta8_ps_int, ← u0_mul_E2star_pow_four] at hdiff
  have hu0 : thetaQ u0_ps_int = u0_ps_int + 2 * PowerSeries.X * U_ps_int * thetaQ U_ps_int := by
    rw [u0_ps_int, thetaQ_mul, thetaQ_X, thetaQ_pow]
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring
  rw [hu0] at hdiff
  have hu0_def : u0_ps_int = PowerSeries.X * U_ps_int ^ 2 := rfl
  rw [hu0_def] at hdiff
  have hmul : (PowerSeries.X * U_ps_int * E2star_ps_int ^ 3) * (2 * E2star_ps_int * thetaQ U_ps_int) =
      (PowerSeries.X * U_ps_int * E2star_ps_int ^ 3) * ((H4_ps_int - E2star_ps_int) * U_ps_int) := by
    have hE := ode_E2star_ps_int
    simp only [Nat.cast_ofNat, Nat.reduceSub] at hdiff
    linear_combination hdiff - (PowerSeries.X * U_ps_int ^ 2 * E2star_ps_int ^ 3) * hE
  have hne : PowerSeries.X * U_ps_int * E2star_ps_int ^ 3 ≠ 0 := by
    have hX : (PowerSeries.X : PowerSeries ℤ) ≠ 0 := PowerSeries.X_ne_zero
    have hU : U_ps_int ≠ 0 := fun h0 => by
      have := congrArg (PowerSeries.coeff 0) h0; simp [U_ps_int_coeff_zero] at this
    have hE : E2star_ps_int ≠ 0 := fun h0 => by
      have := congrArg (PowerSeries.coeff 0) h0; simp [E2star_ps_int_coeff_zero] at this
    exact mul_ne_zero (mul_ne_zero hX hU) (pow_ne_zero 3 hE)
  exact mul_left_cancel₀ hne hmul

set_option maxHeartbeats 1000000 in
/-- Exact Picard-Fuchs operator annihilation modulo $p^2$ on `PowerSeries (R2 p)`:
for every odd prime $p = 2h + 1$, the coefficients of $16^{p-1} U(q)^p E_2^*(q)$ and
$\sum_{j=0}^h \mathrm{atCoeff}(p,h,j)\,(256\,u_0(q))^j$ agree modulo $p^2$ for all $m < p$. -/
private theorem picard_fuchs_congruence_mod_p_sq {p h : ℕ}
    (hp : p.Prime) (hp2 : 2 < p) (hh : p = 2 * h + 1) :
    let φ : ℤ →+* R2 p := Int.castRingHom (R2 p)
    let E_mod : PowerSeries (R2 p) := E2star_ps_int.map φ
    let U_mod : PowerSeries (R2 p) := U_ps_int.map φ
    let u0_mod : PowerSeries (R2 p) := u0_ps_int.map φ
    ∀ m < p,
      (PowerSeries.C ((16 : R2 p) ^ (p - 1)) * U_mod ^ p * E_mod).coeff m =
      (∑ j ∈ Finset.range (h + 1),
        PowerSeries.C (atCoeff p h j) * (PowerSeries.C (256 : R2 p) * u0_mod) ^ j).coeff m := by
  intro φ E_mod U_mod u0_mod
  let P_mod : PowerSeries (R2 p) := P_ps_int.map φ
  let H_mod : PowerSeries (R2 p) := H4_ps_int.map φ
  let h2 : R2 p := halfR p
  have hh2 : (2 : R2 p) * h2 = 1 := two_halfR hp hp2
  let h2s : PowerSeries (R2 p) := PowerSeries.C h2
  have hh2s : (2 : PowerSeries (R2 p)) * h2s = 1 := by
    rw [show (2 : PowerSeries (R2 p)) = PowerSeries.C 2 from (map_ofNat PowerSeries.C 2).symm,
      ← map_mul, hh2, map_one]
  let ps : PowerSeries (R2 p) := PowerSeries.C (p : R2 p)
  have hps2 : ps ^ 2 = 0 := by rw [← map_pow, p_sq_zero p, map_zero]
  have hE0 : E_mod.coeff 0 = 1 := by simp [E_mod, E2star_ps_int_coeff_zero]
  have hH0 : H_mod.coeff 0 = 1 := by simp [H_mod, H4_ps_int_coeff_zero]
  have hU0 : U_mod.coeff 0 = 1 := by simp [U_mod, U_ps_int_coeff_zero]
  have hu0_0 : u0_mod.coeff 0 = 0 := by simp [u0_mod, u0_ps_int_coeff_zero]
  let E_inv : PowerSeries (R2 p) := ((isUnit_of_coeff_zero_one hE0).unit⁻¹ : (PowerSeries (R2 p))ˣ)
  let H_inv : PowerSeries (R2 p) := ((isUnit_of_coeff_zero_one hH0).unit⁻¹ : (PowerSeries (R2 p))ˣ)
  have hE_inv : E_mod * E_inv = 1 := (isUnit_of_coeff_zero_one hE0).unit.mul_inv
  have hH_inv : H_mod * H_inv = 1 := (isUnit_of_coeff_zero_one hH0).unit.mul_inv
  have hE_inv0 : E_inv.coeff 0 = 1 := by
    have h0 := congrArg PowerSeries.constantCoeff hE_inv
    rw [map_mul, map_one, ← PowerSeries.coeff_zero_eq_constantCoeff, hE0, one_mul] at h0
    exact h0
  have hH_inv0 : H_inv.coeff 0 = 1 := by
    have h0 := congrArg PowerSeries.constantCoeff hH_inv
    rw [map_mul, map_one, ← PowerSeries.coeff_zero_eq_constantCoeff, hH0, one_mul] at h0
    exact h0
  -- Mapped ODEs in `PowerSeries (R2 p)`
  have hdE4 : 4 * thetaQ E_mod = P_mod * E_mod - H_mod := by
    have h := congrArg (PowerSeries.map φ) ode_E2star_ps_int
    simpa [E_mod, P_mod, H_mod, thetaQ_map, map_ofNat] using h
  have hdP8 : 8 * thetaQ P_mod = P_mod ^ 2 - E_mod ^ 2 := by
    have h := congrArg (PowerSeries.map φ) ode_P_ps_int
    simpa [E_mod, P_mod, thetaQ_map, map_ofNat] using h
  have hdH2 : 2 * thetaQ H_mod = P_mod * H_mod - E_mod ^ 3 := by
    have h := congrArg (PowerSeries.map φ) ode_H4_ps_int
    simpa [E_mod, P_mod, H_mod, thetaQ_map, map_ofNat] using h
  have hdU2 : 2 * E_mod * thetaQ U_mod = (H_mod - E_mod) * U_mod := by
    have h := congrArg (PowerSeries.map φ) ode_U_ps_int
    simpa [E_mod, H_mod, U_mod, thetaQ_map, map_ofNat] using h
  have hHsq : H_mod ^ 2 = E_mod ^ 4 - 256 * u0_mod * E_mod ^ 4 := by
    have h1 := congrArg (PowerSeries.map φ) H4_sq_ps_int
    have h2 := congrArg (PowerSeries.map φ) u0_mul_E2star_pow_four
    simp only [map_sub, map_pow, map_mul, map_ofNat] at h1 h2
    rw [← h2] at h1
    change H_mod ^ 2 = E_mod ^ 4 - 256 * (u0_mod * E_mod ^ 4) at h1
    linear_combination h1
  have hdE : thetaQ E_mod = h2s ^ 2 * (P_mod * E_mod - H_mod) := by
    linear_combination h2s ^ 2 * hdE4 + thetaQ E_mod * (2 * h2s + 1) * (-hh2s)
  have hdP : thetaQ P_mod = h2s ^ 3 * (P_mod ^ 2 - E_mod ^ 2) := by
    linear_combination h2s ^ 3 * hdP8 +
      thetaQ P_mod * (4 * h2s ^ 2 + 2 * h2s + 1) * (-hh2s)
  have hdH : thetaQ H_mod = h2s * (P_mod * H_mod - E_mod ^ 3) := by
    linear_combination h2s * hdH2 + thetaQ H_mod * (-hh2s)
  have hdU : thetaQ U_mod = h2s * (H_mod * E_inv - 1) * U_mod := by
    linear_combination h2s * E_inv * hdU2 + thetaQ U_mod * (-hh2s) +
      2 * h2s * thetaQ U_mod * (-hE_inv) + h2s * U_mod * (-hE_inv)
  have hdH_inv : thetaQ H_inv = -H_inv ^ 2 * thetaQ H_mod := by
    have h0 := congrArg thetaQ hH_inv
    rw [thetaQ_mul, thetaQ_one] at h0
    linear_combination H_inv * h0 - thetaQ H_inv * hH_inv
  -- Define `z_mod = 256 * u0_mod`, `tz = (E_mod * H_inv) * thetaQ`, `Dp = tz - (p/2)`, and `Lp`
  let z_mod : PowerSeries (R2 p) := PowerSeries.C (256 : R2 p) * u0_mod
  have hz_eq : z_mod = 1 - H_mod ^ 2 * E_inv ^ 4 := by
    change PowerSeries.C (256 : R2 p) * u0_mod = 1 - H_mod ^ 2 * E_inv ^ 4
    rw [show PowerSeries.C (256 : R2 p) = (256 : PowerSeries (R2 p)) from map_ofNat PowerSeries.C 256]
    have hE4 : E_mod ^ 4 * E_inv ^ 4 = 1 := by rw [← mul_pow, hE_inv, one_pow]
    linear_combination E_inv ^ 4 * hHsq + (1 - 256 * u0_mod) * hE4
  have hz0 : z_mod.coeff 0 = 0 := by simp [z_mod, hu0_0]
  let tz (f : PowerSeries (R2 p)) : PowerSeries (R2 p) := (E_mod * H_inv) * thetaQ f
  have htz_add : ∀ f g, tz (f + g) = tz f + tz g := fun f g => by simp [tz, thetaQ_add, mul_add]
  have htz_sub : ∀ f g, tz (f - g) = tz f - tz g := fun f g => by simp [tz, thetaQ_sub, mul_sub]
  have htz_C_mul : ∀ r f, tz (PowerSeries.C r * f) = PowerSeries.C r * tz f := fun r f => by
    simp [tz, thetaQ_C_mul]; ring
  have htz_mul : ∀ f g, tz (f * g) = tz f * g + f * tz g := fun f g => by
    simp [tz, thetaQ_mul]; ring
  have htz_z : tz z_mod = z_mod := by
    have hu0_diff : thetaQ u0_mod = (H_mod * E_inv) * u0_mod := by
      have h1 : thetaQ u0_mod = u0_mod + 2 * PowerSeries.X * U_mod * thetaQ U_mod := by
        have hdef : u0_mod = PowerSeries.X * U_mod ^ 2 := by
          simp [u0_mod, U_mod, u0_ps_int]
        rw [hdef, thetaQ_mul, thetaQ_X, thetaQ_pow]
        simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring
      rw [h1, hdU]
      have hdef : u0_mod = PowerSeries.X * U_mod ^ 2 := by simp [u0_mod, U_mod, u0_ps_int]
      rw [hdef]
      linear_combination PowerSeries.X * U_mod ^ 2 * (H_mod * E_inv - 1) * hh2s
    dsimp [tz, z_mod]
    rw [thetaQ_C_mul, hu0_diff]
    linear_combination PowerSeries.C (256 : R2 p) * u0_mod * (E_mod * E_inv * hH_inv + hE_inv)
  have htz_z_pow : ∀ j : ℕ, tz (z_mod ^ j) = PowerSeries.C (j : R2 p) * z_mod ^ j := by
    intro j
    induction j with
    | zero => simp [tz, thetaQ_one]
    | succ j ih =>
      rw [pow_succ, htz_mul, ih, htz_z, Nat.cast_succ, map_add, map_one]
      ring
  let Dp (f : PowerSeries (R2 p)) : PowerSeries (R2 p) := tz f - (ps * h2s) * f
  have hDp_add : ∀ f g, Dp (f + g) = Dp f + Dp g := fun f g => by
    dsimp [Dp]; rw [htz_add]; ring
  have hDp_sub : ∀ f g, Dp (f - g) = Dp f - Dp g := fun f g => by
    dsimp [Dp]; rw [htz_sub]; ring
  have hDp_C_mul : ∀ r f, Dp (PowerSeries.C r * f) = PowerSeries.C r * Dp f := fun r f => by
    dsimp [Dp]; rw [htz_C_mul]; ring
  have hDp_z_pow : ∀ j : ℕ, Dp (z_mod ^ j) = PowerSeries.C ((j : R2 p) - (p : R2 p) * h2) * z_mod ^ j := by
    intro j
    dsimp [Dp]
    rw [htz_z_pow j]
    simp only [ps, h2s, map_sub, map_mul]
    ring
  let Lp (f : PowerSeries (R2 p)) : PowerSeries (R2 p) :=
    Dp (Dp (Dp f)) - z_mod * (Dp (Dp (Dp f)) +
      (3 * h2s) * Dp (Dp f) + (11 * h2s ^ 4) * Dp f + (3 * h2s ^ 5) * f)
  have hLp_add : ∀ f g, Lp (f + g) = Lp f + Lp g := fun f g => by
    dsimp [Lp]; simp only [hDp_add]; ring
  have hLp_sub : ∀ f g, Lp (f - g) = Lp f - Lp g := fun f g => by
    dsimp [Lp]; simp only [hDp_sub]; ring
  have hLp_C_mul : ∀ r f, Lp (PowerSeries.C r * f) = PowerSeries.C r * Lp f := fun r f => by
    dsimp [Lp]; simp only [hDp_C_mul]; ring
  have hLp_sum : ∀ (s : Finset ℕ) (F : ℕ → PowerSeries (R2 p)),
      Lp (∑ j ∈ s, F j) = ∑ j ∈ s, Lp (F j) := by
    intro s F
    classical
    induction s using Finset.induction_on with
    | empty => simp [Lp, Dp, tz, thetaQ_zero]
    | insert a s ha ih => rw [Finset.sum_insert ha, hLp_add, ih, Finset.sum_insert ha]
  -- Step 1: `Lp (U_mod ^ p * E_mod) = 0` via factoring out `U_mod ^ p`!
  let Tp (f : PowerSeries (R2 p)) : PowerSeries (R2 p) := thetaQ f - (ps * h2s) * f
  let J (f : PowerSeries (R2 p)) : PowerSeries (R2 p) := (E_mod * H_inv) * Tp f
  have hDp_Up_mul : ∀ f : PowerSeries (R2 p), Dp (U_mod ^ p * f) = U_mod ^ p * J f := by
    intro f
    have hUp : thetaQ (U_mod ^ p) = (ps * h2s) * (H_mod * E_inv - 1) * U_mod ^ p := by
      rw [thetaQ_pow, hdU]
      have hp1 : U_mod ^ (p - 1) * U_mod = U_mod ^ p := by
        rw [← pow_succ, Nat.sub_add_cancel hp.pos]
      have hps : (p : PowerSeries (R2 p)) = ps := by simp [ps]
      rw [hps]
      linear_combination (ps * h2s * (H_mod * E_inv - 1)) * hp1
    dsimp [Dp, tz, J, Tp]
    rw [thetaQ_mul, hUp]
    have hcancel : (E_mod * H_inv) * (H_mod * E_inv) = 1 := by
      linear_combination E_mod * E_inv * hH_inv + hE_inv
    linear_combination (ps * h2s * U_mod ^ p * f) * hcancel
  have hLp_UpE : Lp (U_mod ^ p * E_mod) = 0 := by
    have hD1 : Dp (U_mod ^ p * E_mod) = U_mod ^ p * J E_mod := hDp_Up_mul E_mod
    have hD2 : Dp (Dp (U_mod ^ p * E_mod)) = U_mod ^ p * J (J E_mod) := by
      rw [hD1, hDp_Up_mul]
    have hD3 : Dp (Dp (Dp (U_mod ^ p * E_mod))) = U_mod ^ p * J (J (J E_mod)) := by
      rw [hD2, hDp_Up_mul]
    -- Express `J^k E_mod` explicitly in `(E_mod, P_mod, H_mod, H_inv)`
    let q1 : PowerSeries (R2 p) := E_mod * Tp E_mod
    let q2 : PowerSeries (R2 p) := E_mod * (H_mod * Tp q1 - q1 * thetaQ H_mod)
    let q3 : PowerSeries (R2 p) := E_mod * (H_mod * Tp q2 - 3 * q2 * thetaQ H_mod)
    have hJ1 : J E_mod = q1 * H_inv := by dsimp [J, q1]; ring
    have hJ2 : J (J E_mod) = q2 * H_inv ^ 3 := by
      rw [hJ1]
      dsimp [J, Tp, q2]
      rw [thetaQ_mul, hdH_inv]
      linear_combination -E_mod * H_inv ^ 2 * (thetaQ q1 - ps * h2s * q1) * hH_inv
    have hJ3 : J (J (J E_mod)) = q3 * H_inv ^ 5 := by
      rw [hJ2]
      dsimp [J, Tp, q3]
      rw [thetaQ_mul, thetaQ_pow, hdH_inv]
      simp only [Nat.cast_ofNat, Nat.reduceSub]
      linear_combination -E_mod * H_inv ^ 4 * (thetaQ q2 - ps * h2s * q2) * hH_inv
    have hq1_val : 4 * q1 = E_mod * (P_mod * E_mod - H_mod - 2 * ps * E_mod) := by
      dsimp [q1, Tp]
      linear_combination E_mod * hdE4 - 2 * ps * E_mod ^ 2 * hh2s
    have hps0 : thetaQ ps = 0 := thetaQ_C (p : R2 p)
    have hq1_deriv : 8 * thetaQ (4 * q1) =
        2 * (P_mod * E_mod - H_mod) * (P_mod * E_mod - H_mod - 2 * ps * E_mod) +
        E_mod * ((P_mod ^ 2 - E_mod ^ 2) * E_mod + 2 * P_mod * (P_mod * E_mod - H_mod) -
          4 * (P_mod * H_mod - E_mod ^ 3) - 4 * ps * (P_mod * E_mod - H_mod)) := by
      rw [hq1_val, thetaQ_mul, thetaQ_sub, thetaQ_sub, thetaQ_mul, thetaQ_mul,
        thetaQ_ofNat_mul, hps0, mul_zero, zero_mul, zero_add]
      linear_combination 2 * (P_mod * E_mod - H_mod - 2 * ps * E_mod) * hdE4 +
        E_mod ^ 2 * hdP8 + 2 * E_mod * P_mod * hdE4 - 4 * E_mod * hdH2 - 4 * E_mod * ps * hdE4
    have hq2_val : 32 * q2 =
        E_mod * (H_mod * (8 * thetaQ (4 * q1) - 4 * ps * (4 * q1)) - 4 * (4 * q1) * (P_mod * H_mod - E_mod ^ 3)) := by
      have htq : thetaQ (4 * q1) = 4 * thetaQ q1 := thetaQ_ofNat_mul 4 q1
      dsimp [q2, Tp]
      rw [htq]
      linear_combination -16 * E_mod * H_mod * ps * q1 * hh2s - 16 * E_mod * q1 * hdH2
    -- Simplify `32 * q2` explicitly as a 9-term polynomial in `E, P, H, ps`
    have hq2_poly : 32 * q2 =
        2 * E_mod * H_mod ^ 3 + 12 * E_mod ^ 2 * H_mod ^ 2 * ps - 6 * E_mod ^ 2 * P_mod * H_mod ^ 2 +
        8 * E_mod ^ 3 * H_mod * ps ^ 2 - 4 * E_mod ^ 3 * P_mod * H_mod * ps +
        E_mod ^ 3 * P_mod ^ 2 * H_mod - E_mod ^ 5 * H_mod - 8 * E_mod ^ 6 * ps +
        4 * E_mod ^ 6 * P_mod := by
      rw [hq2_val, hq1_deriv, hq1_val]
      ring
    -- Compute `8 * thetaQ (32 * q2)` directly from `hq2_poly`!
    have hq2_deriv : 8 * thetaQ (32 * q2) =
        (2 * (P_mod * E_mod - H_mod)) *
          (2 * H_mod ^ 3 + 24 * E_mod * H_mod ^ 2 * ps - 12 * E_mod * P_mod * H_mod ^ 2 +
           24 * E_mod ^ 2 * H_mod * ps ^ 2 - 12 * E_mod ^ 2 * P_mod * H_mod * ps +
           3 * E_mod ^ 2 * P_mod ^ 2 * H_mod - 5 * E_mod ^ 4 * H_mod - 48 * E_mod ^ 5 * ps +
           24 * E_mod ^ 5 * P_mod) +
        (P_mod ^ 2 - E_mod ^ 2) *
          (-6 * E_mod ^ 2 * H_mod ^ 2 - 4 * E_mod ^ 3 * H_mod * ps +
           2 * E_mod ^ 3 * P_mod * H_mod + 4 * E_mod ^ 6) +
        (4 * (P_mod * H_mod - E_mod ^ 3)) *
          (6 * E_mod * H_mod ^ 2 + 24 * E_mod ^ 2 * H_mod * ps - 12 * E_mod ^ 2 * P_mod * H_mod +
           8 * E_mod ^ 3 * ps ^ 2 - 4 * E_mod ^ 3 * P_mod * ps +
           E_mod ^ 3 * P_mod ^ 2 - E_mod ^ 5) := by
      rw [hq2_poly]
      simp only [thetaQ_add, thetaQ_sub, thetaQ_mul, thetaQ_pow, thetaQ_ofNat, hps0,
        Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_mul, mul_zero, add_zero, zero_add]
      linear_combination
        2 * (2 * H_mod ^ 3 + 24 * E_mod * H_mod ^ 2 * ps - 12 * E_mod * P_mod * H_mod ^ 2 +
          24 * E_mod ^ 2 * H_mod * ps ^ 2 - 12 * E_mod ^ 2 * P_mod * H_mod * ps +
          3 * E_mod ^ 2 * P_mod ^ 2 * H_mod - 5 * E_mod ^ 4 * H_mod - 48 * E_mod ^ 5 * ps +
          24 * E_mod ^ 5 * P_mod) * hdE4 +
        (-6 * E_mod ^ 2 * H_mod ^ 2 - 4 * E_mod ^ 3 * H_mod * ps +
          2 * E_mod ^ 3 * P_mod * H_mod + 4 * E_mod ^ 6) * hdP8 +
        4 * (6 * E_mod * H_mod ^ 2 + 24 * E_mod ^ 2 * H_mod * ps - 12 * E_mod ^ 2 * P_mod * H_mod +
          8 * E_mod ^ 3 * ps ^ 2 - 4 * E_mod ^ 3 * P_mod * ps +
          E_mod ^ 3 * P_mod ^ 2 - E_mod ^ 5) * hdH2
    have hq3_val : 256 * q3 =
        E_mod * (H_mod * (8 * thetaQ (32 * q2) - 4 * ps * (32 * q2)) -
          12 * (32 * q2) * (P_mod * H_mod - E_mod ^ 3)) := by
      have htq : thetaQ (32 * q2) = 32 * thetaQ q2 := thetaQ_ofNat_mul 32 q2
      dsimp [q3, Tp]
      rw [htq]
      linear_combination -128 * E_mod * H_mod * ps * q2 * hh2s - 384 * E_mod * q2 * hdH2
    have hmain_int :
        H_mod ^ 2 * (256 * q3) - (E_mod ^ 4 - H_mod ^ 2) *
          (12 * H_mod ^ 2 * (32 * q2) + 44 * H_mod ^ 4 * (4 * q1) + 24 * H_mod ^ 5 * E_mod) =
        -32 * ps ^ 3 * E_mod ^ 4 * H_mod ^ 4 := by
      rw [hq3_val, hq2_deriv, hq2_poly, hq1_val]
      ring
    have hps3 : ps ^ 3 = 0 := by rw [show (3 : ℕ) = 2 + 1 by decide, pow_add, hps2, zero_mul]
    rw [hps3, mul_zero, zero_mul, zero_mul] at hmain_int
    -- Divide out the units `256`, `E_mod^4`, `H_mod^5` to get `Lp (U_mod ^ p * E_mod) = 0`!
    dsimp [Lp]
    rw [hD3, hD2, hD1, hJ3, hJ2, hJ1, hz_eq]
    have hE4 : E_mod ^ 4 * E_inv ^ 4 = 1 := by rw [← mul_pow, hE_inv, one_pow]
    have hH5 : H_mod ^ 5 * H_inv ^ 5 = 1 := by rw [← mul_pow, hH_inv, one_pow]
    have h256 : (256 : PowerSeries (R2 p)) * h2s ^ 8 = 1 := by
      rw [show (256 : PowerSeries (R2 p)) = 2 ^ 8 by norm_num, ← mul_pow, hh2s, one_pow]
    -- Show `256 * E_mod ^ 4 * H_mod ^ 5 * (...) = 0`
    have hscaled : (256 : PowerSeries (R2 p)) * E_mod ^ 4 * H_mod ^ 5 *
        (q3 * H_inv ^ 5 - (1 - H_mod ^ 2 * E_inv ^ 4) *
          (q3 * H_inv ^ 5 + (3 * h2s) * (q2 * H_inv ^ 3) +
            (11 * h2s ^ 4) * (q1 * H_inv) + (3 * h2s ^ 5) * E_mod)) = 0 := by
      have hH1 : H_mod ^ 5 * H_inv = H_mod ^ 4 := by
        linear_combination H_mod ^ 4 * hH_inv
      have hH3 : H_mod ^ 5 * H_inv ^ 3 = H_mod ^ 2 := by
        have h3 : H_mod ^ 3 * H_inv ^ 3 = 1 := by rw [← mul_pow, hH_inv, one_pow]
        linear_combination H_mod ^ 2 * h3
      have h1_2 : (256 : PowerSeries (R2 p)) * (3 * h2s) = 384 := by
        linear_combination 384 * hh2s
      have h1_4 : (256 : PowerSeries (R2 p)) * (11 * h2s ^ 4) = 176 := by
        have h4 : (16 : PowerSeries (R2 p)) * h2s ^ 4 = 1 := by
          rw [show (16 : PowerSeries (R2 p)) = 2 ^ 4 by norm_num, ← mul_pow, hh2s, one_pow]
        linear_combination 176 * h4
      have h1_5 : (256 : PowerSeries (R2 p)) * (3 * h2s ^ 5) = 24 := by
        have h5 : (32 : PowerSeries (R2 p)) * h2s ^ 5 = 1 := by
          rw [show (32 : PowerSeries (R2 p)) = 2 ^ 5 by norm_num, ← mul_pow, hh2s, one_pow]
        linear_combination 24 * h5
      calc (256 : PowerSeries (R2 p)) * E_mod ^ 4 * H_mod ^ 5 *
            (q3 * H_inv ^ 5 - (1 - H_mod ^ 2 * E_inv ^ 4) *
              (q3 * H_inv ^ 5 + (3 * h2s) * (q2 * H_inv ^ 3) +
                (11 * h2s ^ 4) * (q1 * H_inv) + (3 * h2s ^ 5) * E_mod))
          = (256 * q3) * H_mod ^ 2 * (H_mod ^ 5 * H_inv ^ 5) * (E_mod ^ 4 * E_inv ^ 4) -
            (E_mod ^ 4 - H_mod ^ 2 * (E_mod ^ 4 * E_inv ^ 4)) *
              ((256 * (3 * h2s)) * (H_mod ^ 5 * H_inv ^ 3) * q2 +
               (256 * (11 * h2s ^ 4)) * (H_mod ^ 5 * H_inv) * q1 +
               (256 * (3 * h2s ^ 5)) * H_mod ^ 5 * E_mod) := by ring
        _ = H_mod ^ 2 * (256 * q3) - (E_mod ^ 4 - H_mod ^ 2) *
              (12 * H_mod ^ 2 * (32 * q2) + 44 * H_mod ^ 4 * (4 * q1) + 24 * H_mod ^ 5 * E_mod) := by
            rw [hH5, hE4, hH3, hH1, h1_2, h1_4, h1_5]; ring
        _ = 0 := hmain_int
    have hinner : q3 * H_inv ^ 5 - (1 - H_mod ^ 2 * E_inv ^ 4) *
        (q3 * H_inv ^ 5 + (3 * h2s) * (q2 * H_inv ^ 3) +
          (11 * h2s ^ 4) * (q1 * H_inv) + (3 * h2s ^ 5) * E_mod) = 0 := by
      set X := q3 * H_inv ^ 5 - (1 - H_mod ^ 2 * E_inv ^ 4) *
        (q3 * H_inv ^ 5 + (3 * h2s) * (q2 * H_inv ^ 3) +
          (11 * h2s ^ 4) * (q1 * H_inv) + (3 * h2s ^ 5) * E_mod) with hXdef
      have hmul := congrArg (fun x => (h2s ^ 8 * E_inv ^ 4 * H_inv ^ 5) * x) hscaled
      simp only [mul_zero] at hmul
      linear_combination hmul - X * h256 - X * (256 * h2s ^ 8) * hE4 -
        X * (256 * h2s ^ 8) * (E_mod ^ 4 * E_inv ^ 4) * hH5
    have hfactor : U_mod ^ p * (q3 * H_inv ^ 5) - (1 - H_mod ^ 2 * E_inv ^ 4) *
        (U_mod ^ p * (q3 * H_inv ^ 5) + 3 * h2s * (U_mod ^ p * (q2 * H_inv ^ 3)) +
          11 * h2s ^ 4 * (U_mod ^ p * (q1 * H_inv)) + 3 * h2s ^ 5 * (U_mod ^ p * E_mod)) =
        U_mod ^ p * (q3 * H_inv ^ 5 - (1 - H_mod ^ 2 * E_inv ^ 4) *
          (q3 * H_inv ^ 5 + (3 * h2s) * (q2 * H_inv ^ 3) +
            (11 * h2s ^ 4) * (q1 * H_inv) + (3 * h2s ^ 5) * E_mod)) := by ring
    rw [hfactor, hinner, mul_zero]
  -- Step 2: `Lp (∑_{j=0}^h atCoeff(j) * z_mod^j) = 0` via `atCoeff_recurrence`!
  let Ap_z : PowerSeries (R2 p) :=
    ∑ j ∈ Finset.range (h + 1), PowerSeries.C (atCoeff p h j) * z_mod ^ j
  have hLp_Ap : Lp Ap_z = 0 := by
    dsimp [Ap_z]
    rw [hLp_sum]
    have hterm : ∀ j : ℕ, Lp (PowerSeries.C (atCoeff p h j) * z_mod ^ j) =
        PowerSeries.C (atCoeff p h j * ((j : R2 p) - (p : R2 p) * h2) ^ 3) * z_mod ^ j -
        PowerSeries.C (atCoeff p h j *
          ((j : R2 p) + (1 - 2 * (p : R2 p)) * h2 ^ 2) *
          ((j : R2 p) + (3 - 2 * (p : R2 p)) * h2 ^ 2) *
          ((j : R2 p) - (h : R2 p))) * z_mod ^ (j + 1) := by
      intro j
      rw [hLp_C_mul]
      dsimp [Lp]
      simp only [hDp_z_pow, hDp_C_mul]
      have hP : (p : R2 p) = 2 * (h : R2 p) + 1 := by
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
          congrArg (fun n : ℕ => (n : R2 p)) hh
      have hpoly : ∀ a : R2 p,
          a ^ 3 + (3 * h2) * a ^ 2 + (11 * h2 ^ 4) * a + (3 * h2 ^ 5) =
          (a + h2 ^ 2) * (a + 3 * h2 ^ 2) * (a + h2) := by
        intro a
        linear_combination (4 * h2 ^ 3 * a - 2 * h2 * a ^ 2) * hh2
      have hfac1 : ((j : R2 p) - (p : R2 p) * h2) + h2 ^ 2 =
          (j : R2 p) + (1 - 2 * (p : R2 p)) * h2 ^ 2 := by
        linear_combination (p : R2 p) * h2 * hh2
      have hfac2 : ((j : R2 p) - (p : R2 p) * h2) + 3 * h2 ^ 2 =
          (j : R2 p) + (3 - 2 * (p : R2 p)) * h2 ^ 2 := by
        linear_combination (p : R2 p) * h2 * hh2
      have hfac3 : ((j : R2 p) - (p : R2 p) * h2) + h2 = (j : R2 p) - (h : R2 p) := by
        linear_combination -(h2 * hP) - (h : R2 p) * hh2
      have hcomb : ((j : R2 p) - (p : R2 p) * h2) ^ 3 +
          (3 * h2) * ((j : R2 p) - (p : R2 p) * h2) ^ 2 +
          (11 * h2 ^ 4) * ((j : R2 p) - (p : R2 p) * h2) + (3 * h2 ^ 5) =
          ((j : R2 p) + (1 - 2 * (p : R2 p)) * h2 ^ 2) *
          ((j : R2 p) + (3 - 2 * (p : R2 p)) * h2 ^ 2) *
          ((j : R2 p) - (h : R2 p)) := by
        rw [hpoly, hfac1, hfac2, hfac3]
      have hCcomb : PowerSeries.C (((j : R2 p) - (p : R2 p) * h2) ^ 3) +
          (3 * h2s) * PowerSeries.C (((j : R2 p) - (p : R2 p) * h2) ^ 2) +
          (11 * h2s ^ 4) * PowerSeries.C ((j : R2 p) - (p : R2 p) * h2) +
          (3 * h2s ^ 5) =
          PowerSeries.C (((j : R2 p) + (1 - 2 * (p : R2 p)) * h2 ^ 2) *
            ((j : R2 p) + (3 - 2 * (p : R2 p)) * h2 ^ 2) * ((j : R2 p) - (h : R2 p))) := by
        rw [← hcomb]; simp only [h2s, map_add, map_mul, map_pow, map_ofNat]
      rw [pow_succ z_mod j]
      simp only [map_mul, map_pow] at hCcomb ⊢
      linear_combination -(PowerSeries.C (atCoeff p h j) * z_mod * z_mod ^ j) * hCcomb
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_sub_distrib]
    rw [Finset.sum_range_succ' _ h, Finset.sum_range_succ _ h]
    have hzero0 : ((0 : ℕ) : R2 p) - (p : R2 p) * h2 = -(p : R2 p) * h2 := by simp
    have hzero0_cube : (((0 : ℕ) : R2 p) - (p : R2 p) * h2) ^ 3 = 0 := by
      rw [hzero0]; linear_combination -(p : R2 p) * h2 ^ 3 * p_sq_zero p
    rw [hzero0_cube, mul_zero, map_zero, zero_mul, add_zero]
    have hzeroh : ((h : R2 p) - (h : R2 p)) = 0 := sub_self _
    rw [hzeroh, mul_zero, map_zero, zero_mul, add_zero, sub_eq_zero]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjh : j < h := Finset.mem_range.mp hj
    have hrec := atCoeff_recurrence hp hp2 hh j (by omega)
    have hcube'' : ((j : R2 p) + 1) * ((j : R2 p) + 1 - (p : R2 p) * h2) *
        ((j : R2 p) + 1 - (p : R2 p)) = ((j : R2 p) + 1 - (p : R2 p) * h2) ^ 3 := by
      have hpa : (p : R2 p) = 2 * ((p : R2 p) * h2) := by linear_combination -(p : R2 p) * hh2
      have hpsq : ((p : R2 p) * h2) ^ 2 = 0 := by linear_combination h2 ^ 2 * p_sq_zero p
      linear_combination -((j : R2 p) + 1 - (p : R2 p) * h2) * hpsq +
        ((j : R2 p) + 1) * ((j : R2 p) + 1 - (p : R2 p) * h2) * (-hpa)
    rw [show ((j + 1 : ℕ) : R2 p) = (j : R2 p) + 1 by push_cast; ring]
    congr 2
    rw [mul_comm (atCoeff p h (j + 1)), ← hcube'']
    linear_combination hrec
  -- Step 3: Strong induction on `m < p` for `Δ := 16^(p-1) * U_mod^p * E_mod - Ap_z`!
  let Δ : PowerSeries (R2 p) :=
    PowerSeries.C ((16 : R2 p) ^ (p - 1)) * (U_mod ^ p * E_mod) - Ap_z
  have hLp_Δ : Lp Δ = 0 := by
    dsimp [Δ]
    rw [hLp_sub, hLp_C_mul, hLp_UpE, hLp_Ap, mul_zero, sub_zero]
  have hΔ0 : Δ.coeff 0 = 0 := by
    dsimp [Δ, Ap_z]
    have hleft : (PowerSeries.C ((16 : R2 p) ^ (p - 1)) * (U_mod ^ p * E_mod)).coeff 0 =
        (16 : R2 p) ^ (p - 1) := by
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_pow,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply U_mod,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply E_mod, hU0, hE0, one_pow, mul_one, mul_one]
    rw [map_sub, hleft]
    rw [map_sum, Finset.sum_range_succ' _ h]
    have htail0 : ∑ k ∈ Finset.range h,
        (PowerSeries.C (atCoeff p h (k + 1)) * z_mod ^ (k + 1)).coeff 0 = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_pow,
        ← PowerSeries.coeff_zero_eq_constantCoeff, hz0, zero_pow (Nat.succ_ne_zero k), mul_zero]
    rw [htail0, zero_add, pow_zero, mul_one, PowerSeries.coeff_zero_C]
    rw [atCoeff, if_pos (Nat.zero_le h), Nat.sub_zero, Nat.mul_zero, Nat.choose_zero_right,
      Nat.cast_one, mul_one, morley_sq hp hp2 hh, sub_self]
  have hEH0 : (E_mod * H_inv).coeff 0 = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff,
      hE0, hH_inv0, mul_one]
  -- Helper: if `f.coeff k = 0` for all `k < m`, then `(Dp f).coeff k = 0` for all `k < m`
  -- and `(Dp f).coeff m = (m - p * h2) * f.coeff m`.
  have hDp_lead : ∀ (f : PowerSeries (R2 p)) (m : ℕ),
      (∀ k < m, f.coeff k = 0) →
      (∀ k < m, (Dp f).coeff k = 0) ∧
        (Dp f).coeff m = ((m : R2 p) - (p : R2 p) * h2) * f.coeff m := by
    intro f m hfm
    have htz_coeff : ∀ n ≤ m, (tz f).coeff n = (n : R2 p) * f.coeff n := by
      intro n hnm
      dsimp [tz]
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      rw [Finset.sum_eq_single 0]
      · simp [hEH0, coeff_thetaQ]
      · intro i hi hne
        have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [coeff_thetaQ, hfm (n - i) (by omega), mul_zero, mul_zero]
      · intro hnot; exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) hnot
    constructor
    · intro k hk
      dsimp [Dp]
      rw [map_sub, htz_coeff k hk.le, hfm k hk, mul_zero, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      have h0 : ∑ i ∈ Finset.range (k + 1), (ps * h2s).coeff i * f.coeff (k - i) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hfm (k - i) (by omega), mul_zero]
      rw [h0, sub_zero]
    · dsimp [Dp]
      rw [map_sub, htz_coeff m le_rfl, show ps * h2s = PowerSeries.C ((p : R2 p) * h2) by simp [ps, h2s],
        PowerSeries.coeff_C_mul]
      ring
  have hzero_m : ∀ m < p, Δ.coeff m = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hmp
      cases m with
      | zero => exact hΔ0
      | succ m =>
        have hlt : ∀ k < m + 1, Δ.coeff k = 0 := fun k hk => ih k hk (by omega)
        have hd1 := hDp_lead Δ (m + 1) hlt
        have hd2 := hDp_lead (Dp Δ) (m + 1) hd1.1
        have hd3 := hDp_lead (Dp (Dp Δ)) (m + 1) hd2.1
        have htail_coeff : ∀ (G : PowerSeries (R2 p)), (∀ k < m + 1, G.coeff k = 0) →
            (z_mod * G).coeff (m + 1) = 0 := by
          intro G hG
          rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
          refine Finset.sum_eq_zero fun i hi => ?_
          cases i with
          | zero => rw [hz0, zero_mul]
          | succ i =>
            have him : i + 1 ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            rw [hG (m + 1 - (i + 1)) (by omega), mul_zero]
        have hG_lt : ∀ k < m + 1,
            (Dp (Dp (Dp Δ)) + (3 * h2s) * Dp (Dp Δ) + (11 * h2s ^ 4) * Dp Δ + (3 * h2s ^ 5) * Δ).coeff k = 0 := by
          intro k hk
          have hc1 : (3 * h2s : PowerSeries (R2 p)) = PowerSeries.C (3 * h2) := by
            simp [h2s, map_ofNat]
          have hc2 : (11 * h2s ^ 4 : PowerSeries (R2 p)) = PowerSeries.C (11 * h2 ^ 4) := by
            simp [h2s, map_ofNat]
          have hc3 : (3 * h2s ^ 5 : PowerSeries (R2 p)) = PowerSeries.C (3 * h2 ^ 5) := by
            simp [h2s, map_ofNat]
          rw [hc1, hc2, hc3]
          simp only [map_add, PowerSeries.coeff_C_mul, hd3.1 k hk, hd2.1 k hk, hd1.1 k hk, hlt k hk,
            mul_zero, add_zero]
        have hLp_m := congrArg (PowerSeries.coeff (m + 1)) hLp_Δ
        dsimp [Lp] at hLp_m
        rw [map_sub, htail_coeff _ hG_lt, sub_zero, hd3.2, hd2.2, hd1.2, map_zero] at hLp_m
        have hu : IsUnit (((m + 1 : ℕ) : R2 p) - (p : R2 p) * h2) := by
          apply unit_red hp
          rw [map_sub, map_mul, map_natCast (red p) p, ZMod.natCast_self, zero_mul, sub_zero]
          have h1u : IsUnit ((m + 1 : ℕ) : R2 p) := unit_small hp (Nat.succ_pos m) hmp
          have : Fact p.Prime := ⟨hp⟩
          exact (h1u.map (red p)).ne_zero
        have hmul0 : (((m + 1 : ℕ) : R2 p) - (p : R2 p) * h2) ^ 3 * Δ.coeff (m + 1) = 0 := by
          linear_combination hLp_m
        exact (hu.pow 3).mul_right_eq_zero.mp hmul0
  intro m hmp
  have h0 := hzero_m m hmp
  dsimp [Δ, Ap_z] at h0
  rw [map_sub, sub_eq_zero] at h0
  simpa [mul_assoc, z_mod] using h0

end RamanujanODEs

/- ### Section 4: Hecke branches on $\Gamma_0(2)$ and their symmetric functions -/

section HeckeCosets
open UpperHalfPlane hiding I
open Complex Filter Function ModularForm ModularGroup CongruenceSubgroup
open Matrix.SpecialLinearGroup
open scoped Real Topology Manifold MatrixGroups ModularForm

/-- Coset representatives of `Γ₀(2) \ {M : det M = p, 2 ∣ M₁₀}`. -/
private def gmat (p : ℕ) : Option (ZMod p) → Matrix (Fin 2) (Fin 2) ℤ
  | none => !![(p : ℤ), 0; 0, 1]
  | some j => !![1, (j.val : ℤ); 0, (p : ℤ)]

private lemma gmat_det (p : ℕ) (m : Option (ZMod p)) : (gmat p m).det = p := by
  cases m <;> simp [gmat, Matrix.det_fin_two]

private lemma gmat_10 (p : ℕ) (m : Option (ZMod p)) : gmat p m 1 0 = 0 := by
  cases m <;> simp [gmat]

private lemma det_one_of_mul_gmat {p : ℕ} (hp : p.Prime) {m : Option (ZMod p)}
    {σ M : Matrix (Fin 2) (Fin 2) ℤ} (h : σ * gmat p m = M) (hM : M.det = p) : σ.det = 1 := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, gmat_det, hM] at h1
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  exact mul_right_cancel₀ hp0 (by rw [h1, one_mul])

private lemma two_dvd_of_p_mul {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) {c : ℤ} (h : (2 : ℤ) ∣ p * c) :
    (2 : ℤ) ∣ c := by
  have hodd : ¬ (2 : ℤ) ∣ p := by
    intro h2
    have h2' : (2 : ℕ) ∣ p := by exact_mod_cast h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2'
    omega
  exact (Int.prime_two.dvd_or_dvd h).resolve_left hodd

private lemma coset_exists {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : M.det = p) (hc : (2 : ℤ) ∣ M 1 0) :
    ∃ m : Option (ZMod p), ∃ σ : SL(2, ℤ), σ ∈ Gamma0 2 ∧
      (σ : Matrix (Fin 2) (Fin 2) ℤ) * gmat p m = M := by
  have : Fact p.Prime := ⟨hp⟩
  suffices H : ∃ m : Option (ZMod p), ∃ σ : Matrix (Fin 2) (Fin 2) ℤ, (2 : ℤ) ∣ σ 1 0 ∧
      σ * gmat p m = M by
    obtain ⟨m, σ, hσc, hσ⟩ := H
    refine ⟨m, (⟨σ, det_one_of_mul_gmat hp hσ hdet⟩ : SL(2, ℤ)), ?_, hσ⟩
    refine CongruenceSubgroup.Gamma0_mem.mpr ?_
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr hσc
  have hdetM : M 0 0 * M 1 1 - M 0 1 * M 1 0 = p := by rw [← hdet, Matrix.det_fin_two]
  by_cases h0 : (p : ℤ) ∣ M 0 0 ∧ (p : ℤ) ∣ M 1 0
  · obtain ⟨⟨a, ha⟩, ⟨c, hc'⟩⟩ := h0
    refine ⟨none, !![a, M 0 1; c, M 1 1], ?_, ?_⟩
    · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      exact two_dvd_of_p_mul hp hp2 (hc' ▸ hc)
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [gmat, Matrix.mul_apply, Fin.sum_univ_two, ha, hc'] <;> ring
  · -- find `j` with `M 0 1 ≡ j M 0 0` and `M 1 1 ≡ j M 1 0` modulo `p`
    have hZ : ((M 0 0 : ℤ) : ZMod p) * (M 1 1 : ZMod p) - (M 0 1 : ZMod p) * (M 1 0 : ZMod p) = 0 := by
      have := congrArg (fun z : ℤ => (z : ZMod p)) hdetM
      simpa using this
    have hex : ∃ j : ZMod p, (M 0 1 : ZMod p) = j * (M 0 0 : ZMod p) ∧
        (M 1 1 : ZMod p) = j * (M 1 0 : ZMod p) := by
      by_cases hA : ((M 0 0 : ℤ) : ZMod p) = 0
      · have hC : ((M 1 0 : ℤ) : ZMod p) ≠ 0 := by
          intro hC
          exact h0 ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hA,
            (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hC⟩
        refine ⟨(M 1 1 : ZMod p) / (M 1 0 : ZMod p), ?_, by field_simp⟩
        rw [hA, mul_zero]
        rw [hA, zero_mul, zero_sub, neg_eq_zero] at hZ
        exact (mul_eq_zero.mp hZ).resolve_right hC
      · refine ⟨(M 0 1 : ZMod p) / (M 0 0 : ZMod p), by field_simp, ?_⟩
        field_simp
        linear_combination hZ
    obtain ⟨j, hj1, hj2⟩ := hex
    have hd1 : (p : ℤ) ∣ M 0 1 - (j.val : ℤ) * M 0 0 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val, hj1, sub_self]
    have hd2 : (p : ℤ) ∣ M 1 1 - (j.val : ℤ) * M 1 0 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val, hj2, sub_self]
    obtain ⟨b, hb⟩ := hd1
    obtain ⟨d, hd⟩ := hd2
    refine ⟨some j, !![M 0 0, b; M 1 0, d], ?_, ?_⟩
    · simpa using hc
    · ext i k
      fin_cases i <;> fin_cases k <;>
        simp [gmat, Matrix.mul_apply, Fin.sum_univ_two, -ZMod.natCast_val] <;>
        first | linear_combination -(hb) | linear_combination -(hd)

private lemma coset_unique {p : ℕ} (hp : p.Prime) {σ σ' : SL(2, ℤ)} {m m' : Option (ZMod p)}
    (h : (σ : Matrix (Fin 2) (Fin 2) ℤ) * gmat p m = (σ' : Matrix (Fin 2) (Fin 2) ℤ) * gmat p m') :
    m = m' := by
  have : Fact p.Prime := ⟨hp⟩
  have hdet (τ : SL(2, ℤ)) : ((τ 0 0 : ℤ) : ZMod p) * (τ 1 1 : ZMod p) -
      (τ 0 1 : ZMod p) * (τ 1 0 : ZMod p) = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod p)) (Matrix.det_fin_two (τ : Matrix (Fin 2) (Fin 2) ℤ))
    simp only [Matrix.SpecialLinearGroup.det_coe, Int.cast_one, Int.cast_sub, Int.cast_mul] at this
    exact this.symm
  have hcol (τ : SL(2, ℤ)) : ((τ 0 0 : ℤ) : ZMod p) ≠ 0 ∨ ((τ 1 0 : ℤ) : ZMod p) ≠ 0 := by
    by_contra hc
    simp only [not_or, not_not] at hc
    have := hdet τ
    rw [hc.1, hc.2, zero_mul, mul_zero, sub_zero] at this
    exact zero_ne_one this
  have hE : ∀ i k, (((σ : Matrix (Fin 2) (Fin 2) ℤ) * gmat p m) i k : ZMod p) =
      (((σ' : Matrix (Fin 2) (Fin 2) ℤ) * gmat p m') i k : ZMod p) := fun i k => by rw [h]
  have hp0 : ((p : ℤ) : ZMod p) = 0 := by simp
  cases m with
  | none =>
    cases m' with
    | none => rfl
    | some j' =>
      exfalso
      have e00 := hE 0 0
      have e10 := hE 1 0
      simp [gmat, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
      rcases hcol σ' with h1 | h1
      · exact h1 e00.symm
      · exact h1 e10.symm
  | some j =>
    cases m' with
    | none =>
      exfalso
      have e00 := hE 0 0
      have e10 := hE 1 0
      simp [gmat, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
      rcases hcol σ with h1 | h1
      · exact h1 e00
      · exact h1 e10
    | some j' =>
      have e00 := hE 0 0
      have e10 := hE 1 0
      have e01 := hE 0 1
      have e11 := hE 1 1
      simp [gmat, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10 e01 e11
      rw [e00] at e01
      rw [e10] at e11
      congr 1
      rcases hcol σ' with h1 | h1
      · exact mul_right_cancel₀ h1 (by linear_combination e01)
      · exact mul_right_cancel₀ h1 (by linear_combination e11)

open Classical in
/-- The coset index of an integer matrix (the `m` with `M ∈ Γ₀(2) · gmat p m`). -/
private noncomputable def cosetIdx (p : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) : Option (ZMod p) :=
  if h : ∃ m : Option (ZMod p), ∃ σ : SL(2, ℤ), σ ∈ Gamma0 2 ∧
      (σ : Matrix (Fin 2) (Fin 2) ℤ) * gmat p m = M then Classical.choose h else none

private lemma cosetIdx_spec {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : M.det = p) (hc : (2 : ℤ) ∣ M 1 0) :
    ∃ σ : SL(2, ℤ), σ ∈ Gamma0 2 ∧ (σ : Matrix (Fin 2) (Fin 2) ℤ) * gmat p (cosetIdx p M) = M := by
  have h := coset_exists hp hp2 M hdet hc
  rw [cosetIdx, dif_pos h]
  exact Classical.choose_spec h

private lemma two_dvd_of_Gamma0 {σ : SL(2, ℤ)} (hσ : σ ∈ Gamma0 2) : (2 : ℤ) ∣ σ 1 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp (Gamma0_mem.mp hσ)

private lemma two_dvd_mul_10 {A B : Matrix (Fin 2) (Fin 2) ℤ} (hA : (2 : ℤ) ∣ A 1 0) (hB : (2 : ℤ) ∣ B 1 0) :
    (2 : ℤ) ∣ (A * B) 1 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact dvd_add (hA.mul_right _) (hB.mul_left _)

private lemma gmat_10_dvd (p : ℕ) (m : Option (ZMod p)) : (2 : ℤ) ∣ gmat p m 1 0 := by
  rw [gmat_10]; exact dvd_zero _

private lemma cosetIdx_eq {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) {M : Matrix (Fin 2) (Fin 2) ℤ}
    {σ : SL(2, ℤ)} (hσ : σ ∈ Gamma0 2) {m : Option (ZMod p)}
    (h : (σ : Matrix (Fin 2) (Fin 2) ℤ) * gmat p m = M) :
    cosetIdx p M = m := by
  have hdet : M.det = p := by rw [← h, Matrix.det_mul, gmat_det, σ.2, one_mul]
  have hc : (2 : ℤ) ∣ M 1 0 := h ▸ two_dvd_mul_10 (two_dvd_of_Gamma0 hσ) (gmat_10_dvd p m)
  obtain ⟨σ', _, hσ'⟩ := cosetIdx_spec hp hp2 hdet hc
  exact coset_unique hp (hσ'.trans h.symm)

private lemma mat_eq_inv_mul {S Si X Y : Matrix (Fin 2) (Fin 2) ℤ} (hS : Si * S = 1) (h : S * X = Y) :
    X = Si * Y := by
  rw [← h, ← Matrix.mul_assoc, hS, Matrix.one_mul]

private lemma mat_swap {S Si G Gi X Y : Matrix (Fin 2) (Fin 2) ℤ} (hS : Si * S = 1) (hG : Gi * G = 1)
    (h : S * X = Y * Gi) : Si * Y = X * G := by
  rw [mat_eq_inv_mul hS h, Matrix.mul_assoc, Matrix.mul_assoc, hG, Matrix.mul_one]

private lemma SL_inv_mul_coe (σ : SL(2, ℤ)) :
    ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (σ : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

/-- Right multiplication by `g ∈ Γ₀(2)` permutes the cosets. -/
private noncomputable def permG (p : ℕ) (g : SL(2, ℤ)) (m : Option (ZMod p)) : Option (ZMod p) :=
  cosetIdx p (gmat p m * (g : Matrix (Fin 2) (Fin 2) ℤ))

private lemma permG_spec {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) {g : SL(2, ℤ)} (hg : g ∈ Gamma0 2)
    (m : Option (ZMod p)) :
    ∃ σ : SL(2, ℤ), σ ∈ Gamma0 2 ∧ (σ : Matrix (Fin 2) (Fin 2) ℤ) * gmat p (permG p g m) =
      gmat p m * (g : Matrix (Fin 2) (Fin 2) ℤ) :=
  cosetIdx_spec hp hp2 (by rw [Matrix.det_mul, gmat_det, g.2, mul_one])
    (two_dvd_mul_10 (gmat_10_dvd p m) (two_dvd_of_Gamma0 hg))

private lemma permG_surj {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) {g : SL(2, ℤ)} (hg : g ∈ Gamma0 2) :
    Function.Surjective (permG p g) := by
  intro n
  have hg' : g⁻¹ ∈ Gamma0 2 := Subgroup.inv_mem _ hg
  obtain ⟨σ, hσ, hσeq⟩ := cosetIdx_spec hp hp2 (M := gmat p n * ((g⁻¹ : SL(2, ℤ)) : Matrix _ _ ℤ))
    (by rw [Matrix.det_mul, gmat_det, (g⁻¹).2, mul_one])
    (two_dvd_mul_10 (gmat_10_dvd p n) (two_dvd_of_Gamma0 hg'))
  refine ⟨cosetIdx p (gmat p n * ((g⁻¹ : SL(2, ℤ)) : Matrix _ _ ℤ)), ?_⟩
  generalize cosetIdx p (gmat p n * ((g⁻¹ : SL(2, ℤ)) : Matrix _ _ ℤ)) = m at hσeq
  show cosetIdx p _ = n
  exact cosetIdx_eq hp hp2 (Subgroup.inv_mem _ hσ)
    (mat_swap (SL_inv_mul_coe σ) (SL_inv_mul_coe g) hσeq)

/-- Conjugation by the Fricke involution on integer matrices with even lower-left entry. -/
private def conjW (M : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![M 1 1, -(M 1 0 / 2); -(2 * M 0 1), M 0 0]

private lemma conjW_eq {M : Matrix (Fin 2) (Fin 2) ℤ} {c : ℤ} (hc : M 1 0 = 2 * c) :
    conjW M = !![M 1 1, -c; -(2 * M 0 1), M 0 0] := by
  simp [conjW, hc]

private lemma conjW_det {M : Matrix (Fin 2) (Fin 2) ℤ} (hc : (2 : ℤ) ∣ M 1 0) : (conjW M).det = M.det := by
  obtain ⟨c, hc⟩ := hc
  rw [conjW_eq hc, Matrix.det_fin_two_of, Matrix.det_fin_two, hc]
  ring

private lemma conjW_10 (M : Matrix (Fin 2) (Fin 2) ℤ) : (2 : ℤ) ∣ conjW M 1 0 := by
  simp [conjW]

private lemma conjW_mul {A B : Matrix (Fin 2) (Fin 2) ℤ} (hA : (2 : ℤ) ∣ A 1 0) (hB : (2 : ℤ) ∣ B 1 0) :
    conjW (A * B) = conjW A * conjW B := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hab : (A * B) 1 0 = 2 * (a * B 0 0 + A 1 1 * b) := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, ha, hb]; ring
  rw [conjW_eq hab, conjW_eq ha, conjW_eq hb]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb] <;> ring

private lemma conjW_conjW {M : Matrix (Fin 2) (Fin 2) ℤ} (hc : (2 : ℤ) ∣ M 1 0) : conjW (conjW M) = M := by
  obtain ⟨c, hc⟩ := hc
  have h1 : conjW M 1 0 = 2 * (-M 0 1) := by rw [conjW_eq hc]; simp
  rw [conjW_eq h1, conjW_eq hc]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hc]

/-- `conjW` of an element of `Γ₀(2)`, as an element of `SL(2, ℤ)`. -/
private def conjWSL (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 2) : SL(2, ℤ) :=
  ⟨conjW σ, by rw [conjW_det (two_dvd_of_Gamma0 hσ)]; exact σ.2⟩

private lemma conjWSL_mem (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 2) : conjWSL σ hσ ∈ Gamma0 2 :=
  Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr (conjW_10 _))

/-- Conjugation by `W₂` permutes the cosets. -/
private noncomputable def permW (p : ℕ) (m : Option (ZMod p)) : Option (ZMod p) :=
  cosetIdx p (conjW (gmat p m))

private lemma permW_spec {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (m : Option (ZMod p)) :
    ∃ σ : SL(2, ℤ), σ ∈ Gamma0 2 ∧ (σ : Matrix (Fin 2) (Fin 2) ℤ) * gmat p (permW p m) =
      conjW (gmat p m) :=
  cosetIdx_spec hp hp2 (by rw [conjW_det (gmat_10_dvd p m), gmat_det]) (conjW_10 _)

private lemma permW_surj {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) : Function.Surjective (permW p) := by
  intro n
  obtain ⟨τ, hτ, hτeq⟩ := cosetIdx_spec hp hp2 (M := conjW (gmat p n))
    (by rw [conjW_det (gmat_10_dvd p n), gmat_det]) (conjW_10 _)
  refine ⟨cosetIdx p (conjW (gmat p n)), ?_⟩
  generalize cosetIdx p (conjW (gmat p n)) = m at hτeq
  have hg : gmat p m = ((τ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * conjW (gmat p n) :=
    mat_eq_inv_mul (SL_inv_mul_coe τ) hτeq
  have hτ' : τ⁻¹ ∈ Gamma0 2 := Subgroup.inv_mem _ hτ
  show cosetIdx p _ = n
  apply cosetIdx_eq hp hp2 (conjWSL_mem _ hτ')
  rw [hg, conjW_mul (two_dvd_of_Gamma0 hτ') (conjW_10 _), conjW_conjW (gmat_10_dvd p n)]
  rfl

/- #### Integer matrices in `GL(2, ℝ)` and pointwise slash identities -/

/-- An integer matrix as an element of `GL(2, ℝ)` (junk value `1` if singular). -/
private noncomputable def glZ (M : Matrix (Fin 2) (Fin 2) ℤ) : GL (Fin 2) ℝ :=
  if h : ((Int.castRingHom ℝ).mapMatrix M).det ≠ 0 then
    Matrix.GeneralLinearGroup.mkOfDetNeZero _ h else 1

private lemma glZ_val {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M.det ≠ 0) :
    (glZ M : Matrix (Fin 2) (Fin 2) ℝ) = (Int.castRingHom ℝ).mapMatrix M := by
  have h : ((Int.castRingHom ℝ).mapMatrix M).det ≠ 0 := by
    rw [← RingHom.map_det]
    show ((M.det : ℤ) : ℝ) ≠ 0
    exact_mod_cast hM
  rw [glZ, dif_pos h]
  rfl

private lemma glZ_apply {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M.det ≠ 0) (i j : Fin 2) :
    (glZ M : Matrix (Fin 2) (Fin 2) ℝ) i j = (M i j : ℝ) := by
  rw [glZ_val hM]; rfl

private lemma glZ_det {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M.det ≠ 0) : (glZ M).det.val = (M.det : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, glZ_val hM, ← RingHom.map_det]
  rfl

private lemma glZ_mul {M N : Matrix (Fin 2) (Fin 2) ℤ} (hM : M.det ≠ 0) (hN : N.det ≠ 0) :
    glZ (M * N) = glZ M * glZ N := by
  have hMN : (M * N).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero hM hN
  apply Units.ext
  rw [Units.val_mul, glZ_val hM, glZ_val hN, glZ_val hMN, map_mul]

private lemma mapGL_eq_glZ (σ : SL(2, ℤ)) : mapGL ℝ σ = glZ (σ : Matrix (Fin 2) (Fin 2) ℤ) := by
  have h1 : (σ : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by rw [σ.2]; exact one_ne_zero
  apply Units.ext
  ext i j
  rw [mapGL_apply, glZ_apply h1]

private lemma glZ_mul_W2 {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M.det ≠ 0) (hc : (2 : ℤ) ∣ M 1 0) :
    glZ M * W2 = W2 * glZ (conjW M) := by
  have hM' : (conjW M).det ≠ 0 := by rw [conjW_det hc]; exact hM
  obtain ⟨c, hc⟩ := hc
  have hsq : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr two_pos
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  apply Units.ext
  ext i j
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply,
    Fin.sum_univ_two, glZ_apply hM, glZ_apply hM, glZ_apply hM', glZ_apply hM', W2_val, conjW_eq hc]
  fin_cases i <;> fin_cases j <;> simp [hc] <;> (try field_simp) <;>
    simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma denom_glZ {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M.det ≠ 0) (τ : ℍ) :
    denom (glZ M) τ = (M 1 0 : ℂ) * τ + M 1 1 := by
  simp [denom, glZ_apply hM]

private lemma coe_glZ_smul {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : 0 < M.det) (τ : ℍ) :
    ((glZ M • τ : ℍ) : ℂ) = ((M 0 0 : ℂ) * τ + M 0 1) / ((M 1 0 : ℂ) * τ + M 1 1) := by
  have hM' : M.det ≠ 0 := hM.ne'
  rw [UpperHalfPlane.coe_smul_of_det_pos (by rw [glZ_det hM']; exact_mod_cast hM)]
  simp [num, denom, glZ_apply hM']

private lemma slash_apply_of_det_pos {k : ℤ} {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] g) τ = f (g • τ) * ((g.det.val : ℂ)) ^ (k - 1) * denom g τ ^ (-k) := by
  have hg' : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at hg
  rw [ModularForm.slash_apply, abs_of_pos hg]
  simp [UpperHalfPlane.σ, hg']

private lemma slash_comp_apply {k : ℤ} (A B : GL (Fin 2) ℝ) (hB : B.det.val = 1) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] A) (B • τ) = denom B τ ^ k * (f ∣[k] (A * B)) τ := by
  rw [SlashAction.slash_mul, slash_apply_of_det_pos (g := B) (by rw [hB]; exact one_pos) (f ∣[k] A), hB]
  have hd : denom B τ ≠ 0 := denom_ne_zero B τ
  rw [Complex.ofReal_one, one_zpow, mul_one, zpow_neg, mul_comm,
    inv_mul_cancel_right₀ (zpow_ne_zero _ hd)]

private lemma mapGL_det (σ : SL(2, ℤ)) : (mapGL ℝ σ).det.val = 1 := by
  have h1 : (σ : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by rw [σ.2]; exact one_ne_zero
  rw [mapGL_eq_glZ, glZ_det h1, σ.2, Int.cast_one]

end HeckeCosets

section BranchFamilies
open UpperHalfPlane hiding I
open Complex Filter Function ModularForm ModularGroup CongruenceSubgroup
open Matrix.SpecialLinearGroup
open scoped Real Topology Manifold MatrixGroups ModularForm

/-- A family of branches of weight `2 n`, indexed by integer matrices of determinant `p` with even
lower-left entry: left `Γ₀(2)`-invariant, right `Γ₀(2)`-equivariant and `W₂`-equivariant. -/
structure IsBranchFamily (p n : ℕ) (Φ : Matrix (Fin 2) (Fin 2) ℤ → ℍ → ℂ) : Prop where
  left : ∀ σ : SL(2, ℤ), σ ∈ Gamma0 2 → ∀ M : Matrix (Fin 2) (Fin 2) ℤ, M.det = p →
    (2 : ℤ) ∣ M 1 0 → Φ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * M) = Φ M
  right : ∀ σ : SL(2, ℤ), σ ∈ Gamma0 2 → ∀ M : Matrix (Fin 2) (Fin 2) ℤ, M.det = p →
    (2 : ℤ) ∣ M 1 0 → ∀ τ : ℍ, Φ M (mapGL ℝ σ • τ) =
      denom (mapGL ℝ σ) τ ^ (2 * (n : ℤ)) * Φ (M * (σ : Matrix (Fin 2) (Fin 2) ℤ)) τ
  fricke : ∀ M : Matrix (Fin 2) (Fin 2) ℤ, M.det = p → (2 : ℤ) ∣ M 1 0 → ∀ τ : ℍ,
    Φ M (W2 • τ) = (-1) ^ n * denom W2 τ ^ (2 * (n : ℤ)) * Φ (conjW M) τ

/-- The `k`-th elementary symmetric function of the `p + 1` branches `Φ (gmat p m)`. -/
private noncomputable def Ssym (p : ℕ) [NeZero p] (Φ : Matrix (Fin 2) (Fin 2) ℤ → ℍ → ℂ) (k : ℕ)
    (τ : ℍ) : ℂ :=
  ∑ t ∈ Finset.powersetCard k (Finset.univ : Finset (Option (ZMod p))), ∏ m ∈ t, Φ (gmat p m) τ

private lemma sum_powersetCard_comp_equiv {α : Type*} [Fintype α] [DecidableEq α] (e : α ≃ α) (k : ℕ)
    (f : α → ℂ) :
    ∑ t ∈ Finset.powersetCard k (Finset.univ : Finset α), ∏ m ∈ t, f (e m) =
      ∑ t ∈ Finset.powersetCard k (Finset.univ : Finset α), ∏ m ∈ t, f m := by
  refine Finset.sum_nbij' (fun t => t.map e.toEmbedding) (fun t => t.map e.symm.toEmbedding)
    ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at ht ⊢
    rwa [Finset.card_map]
  · intro t ht
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at ht ⊢
    rwa [Finset.card_map]
  · intro t _
    ext x; simp
  · intro t _
    ext x; simp
  · intro t _
    rw [Finset.prod_map]
    rfl

private lemma prod_powersetCard_mul_const {α : Type*} [Fintype α] [DecidableEq α] (k : ℕ) (c : ℂ)
    (f : α → ℂ) :
    ∑ t ∈ Finset.powersetCard k (Finset.univ : Finset α), ∏ m ∈ t, (c * f m) =
      c ^ k * ∑ t ∈ Finset.powersetCard k (Finset.univ : Finset α), ∏ m ∈ t, f m := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp ht).2]

variable {p n : ℕ} {Φ : Matrix (Fin 2) (Fin 2) ℤ → ℍ → ℂ}

private lemma IsBranchFamily.apply_gmat_smul (hF : IsBranchFamily p n Φ) (hp : p.Prime) (hp2 : 2 < p)
    {σ : SL(2, ℤ)} (hσ : σ ∈ Gamma0 2) (m : Option (ZMod p)) (τ : ℍ) :
    Φ (gmat p m) (mapGL ℝ σ • τ) =
      denom (mapGL ℝ σ) τ ^ (2 * (n : ℤ)) * Φ (gmat p (permG p σ m)) τ := by
  rw [hF.right σ hσ (gmat p m) (gmat_det p m) (gmat_10_dvd p m) τ]
  obtain ⟨σ', hσ', hσ'eq⟩ := permG_spec hp hp2 hσ m
  rw [← hσ'eq, hF.left σ' hσ' _ (gmat_det p _) (gmat_10_dvd p _)]

private lemma IsBranchFamily.apply_gmat_W2 (hF : IsBranchFamily p n Φ) (hp : p.Prime) (hp2 : 2 < p)
    (m : Option (ZMod p)) (τ : ℍ) :
    Φ (gmat p m) (W2 • τ) =
      ((-1) ^ n * denom W2 τ ^ (2 * (n : ℤ))) * Φ (gmat p (permW p m)) τ := by
  rw [hF.fricke (gmat p m) (gmat_det p m) (gmat_10_dvd p m) τ]
  obtain ⟨σ', hσ', hσ'eq⟩ := permW_spec hp hp2 m
  rw [← hσ'eq, hF.left σ' hσ' _ (gmat_det p _) (gmat_10_dvd p _)]

private lemma IsBranchFamily.Ssym_smul (hF : IsBranchFamily p n Φ) (hp : p.Prime) (hp2 : 2 < p)
    [NeZero p] {σ : SL(2, ℤ)} (hσ : σ ∈ Gamma0 2) (k : ℕ) (τ : ℍ) :
    Ssym p Φ k (mapGL ℝ σ • τ) = (denom (mapGL ℝ σ) τ ^ (2 * (n : ℤ))) ^ k * Ssym p Φ k τ := by
  have hsurj := permG_surj (p := p) hp hp2 hσ
  let e : Option (ZMod p) ≃ Option (ZMod p) :=
    Equiv.ofBijective _ ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  simp only [Ssym, hF.apply_gmat_smul hp hp2 hσ]
  rw [prod_powersetCard_mul_const]
  congr 1
  exact sum_powersetCard_comp_equiv e k (fun m => Φ (gmat p m) τ)

private lemma IsBranchFamily.Ssym_W2 (hF : IsBranchFamily p n Φ) (hp : p.Prime) (hp2 : 2 < p)
    [NeZero p] (k : ℕ) (τ : ℍ) :
    Ssym p Φ k (W2 • τ) = ((-1) ^ n * denom W2 τ ^ (2 * (n : ℤ))) ^ k * Ssym p Φ k τ := by
  have hsurj := permW_surj (p := p) hp hp2
  let e : Option (ZMod p) ≃ Option (ZMod p) :=
    Equiv.ofBijective _ ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  simp only [Ssym, hF.apply_gmat_W2 hp hp2]
  rw [prod_powersetCard_mul_const]
  congr 1
  exact sum_powersetCard_comp_equiv e k (fun m => Φ (gmat p m) τ)

private lemma IsBranchFamily.Ssym_slash (hF : IsBranchFamily p n Φ) (hp : p.Prime) (hp2 : 2 < p)
    [NeZero p] (k : ℕ) (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 2) :
    Ssym p Φ k ∣[2 * ((k * n : ℕ) : ℤ)] σ = Ssym p Φ k := by
  ext τ
  change (Ssym p Φ k ∣[2 * ((k * n : ℕ) : ℤ)] mapGL ℝ σ) τ = _
  rw [slash_apply_of_det_pos (by rw [mapGL_det]; exact one_pos), mapGL_det, hF.Ssym_smul hp hp2 hσ,
    Complex.ofReal_one, one_zpow, mul_one]
  have hd : denom (mapGL ℝ σ) τ ≠ 0 := denom_ne_zero _ τ
  rw [← zpow_natCast, ← zpow_mul, mul_comm, ← mul_assoc, ← zpow_add₀ hd]
  push_cast
  rw [show -(2 * ((k : ℤ) * n)) + 2 * n * k = 0 by ring, zpow_zero, one_mul]

private lemma IsBranchFamily.Ssym_slash_W2 (hF : IsBranchFamily p n Φ) (hp : p.Prime) (hp2 : 2 < p)
    [NeZero p] (k : ℕ) :
    Ssym p Φ k ∣[2 * ((k * n : ℕ) : ℤ)] W2 = ((-1 : ℂ) ^ (k * n)) • Ssym p Φ k := by
  ext τ
  rw [slash_apply_of_det_pos (by rw [W2_det_val]; exact one_pos), W2_det_val, hF.Ssym_W2 hp hp2,
    Complex.ofReal_one, one_zpow, mul_one, Pi.smul_apply, smul_eq_mul]
  have hd : denom W2 τ ≠ 0 := denom_ne_zero _ τ
  rw [mul_pow, ← pow_mul, ← zpow_natCast (denom W2 τ ^ (2 * (n : ℤ))), ← zpow_mul]
  have : denom W2 τ ^ (2 * (n : ℤ) * (k : ℤ)) * denom W2 τ ^ (-(2 * ((k * n : ℕ) : ℤ))) = 1 := by
    rw [← zpow_add₀ hd]; push_cast; rw [show 2 * (n : ℤ) * k + -(2 * (k * n)) = 0 by ring, zpow_zero]
  rw [mul_comm n k]
  linear_combination ((-1 : ℂ) ^ (k * n) * Ssym p Φ k τ) * this

private lemma Ssym_eq_sum_prod (p : ℕ) [NeZero p] (Φ : Matrix (Fin 2) (Fin 2) ℤ → ℍ → ℂ) (k : ℕ) :
    Ssym p Φ k = ∑ t ∈ Finset.powersetCard k (Finset.univ : Finset (Option (ZMod p))),
      ∏ m ∈ t, Φ (gmat p m) := by
  ext τ
  simp [Ssym, Finset.sum_apply, Finset.prod_apply]

private lemma Ssym_mdiff [NeZero p] (hΦ : ∀ m : Option (ZMod p), MDiff (Φ (gmat p m))) (k : ℕ) :
    MDiff (Ssym p Φ k) := by
  rw [Ssym_eq_sum_prod]
  refine Finset.sum_induction _ (fun f : ℍ → ℂ => MDiff f) (fun f g hf hg => hf.add hg)
    mdifferentiable_const ?_
  intro t _
  exact Finset.prod_induction _ (fun f : ℍ → ℂ => MDiff f) (fun f g hf hg => hf.mul hg)
    mdifferentiable_const (fun m _ => hΦ m)

private lemma Ssym_bdd [NeZero p] (hΦ : ∀ m : Option (ZMod p), IsBoundedAtImInfty (Φ (gmat p m)))
    (k : ℕ) : IsBoundedAtImInfty (Ssym p Φ k) := by
  rw [Ssym_eq_sum_prod]
  refine Finset.sum_induction _ (fun f : ℍ → ℂ => IsBoundedAtImInfty f) (fun f g hf hg => hf.add hg)
    (zero_form_isBoundedAtImInfty) ?_
  intro t _
  exact Finset.prod_induction _ (fun f : ℍ → ℂ => IsBoundedAtImInfty f) (fun f g hf hg => hf.mul hg)
    (Filter.const_boundedAtFilter _ (1 : ℂ)) (fun m _ => hΦ m)

/-- The symmetric function `S_k` of a branch family, as a modular form on `Γ₀(2)`. -/
private noncomputable def SsymMF (hF : IsBranchFamily p n Φ) (hp : p.Prime) (hp2 : 2 < p) [NeZero p]
    (hΦ : ∀ m : Option (ZMod p), MDiff (Φ (gmat p m)))
    (hΦb : ∀ m : Option (ZMod p), IsBoundedAtImInfty (Φ (gmat p m))) (k : ℕ) :
    ModularForm Γ02 (2 * ((k * n : ℕ) : ℤ)) where
  toFun := Ssym p Φ k
  slash_action_eq' := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact hF.Ssym_slash hp hp2 k γ hγ
  holo' := Ssym_mdiff hΦ k
  bdd_at_cusps' hc := isBoundedAt_Γ02_of_W2 (ε := (-1 : ℂ) ^ (k * n))
    (fun γ hγ => hF.Ssym_slash hp hp2 k γ hγ) (hF.Ssym_slash_W2 hp hp2 k) (Ssym_bdd hΦb k) hc

private lemma SsymMF_coe (hF : IsBranchFamily p n Φ) (hp : p.Prime) (hp2 : 2 < p) [NeZero p]
    (hΦ : ∀ m : Option (ZMod p), MDiff (Φ (gmat p m)))
    (hΦb : ∀ m : Option (ZMod p), IsBoundedAtImInfty (Φ (gmat p m))) (k : ℕ) :
    (SsymMF hF hp hp2 hΦ hΦb k : ℍ → ℂ) = Ssym p Φ k := rfl

/-- **Vieta**: the polynomial with roots the branches. -/
private lemma prod_sub_eq_sum_Ssym (p : ℕ) [NeZero p] (Φ : Matrix (Fin 2) (Fin 2) ℤ → ℍ → ℂ) (τ : ℍ)
    (Y : ℂ) :
    ∏ m : Option (ZMod p), (Y - Φ (gmat p m) τ) =
      ∑ k ∈ Finset.range (p + 1 + 1), (-1) ^ k * Ssym p Φ k τ * Y ^ (p + 1 - k) := by
  have hv := Multiset.prod_X_add_C_eq_sum_esymm
    ((Finset.univ : Finset (Option (ZMod p))).val.map fun m => -Φ (gmat p m) τ)
  have hv' := congrArg (Polynomial.eval Y) hv
  rw [Polynomial.eval_multiset_prod, Multiset.map_map, Polynomial.eval_finsetSum] at hv'
  simp only [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_option,
    ZMod.card, Function.comp_apply, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_pow, Finset.esymm_map_val] at hv'
  have hL : (∏ m : Option (ZMod p), (Y - Φ (gmat p m) τ)) =
      (Multiset.map (fun x => Y + x)
        (Multiset.map (fun m => -Φ (gmat p m) τ) Finset.univ.val)).prod := by
    rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
    congr 1
  rw [hL, hv']
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Ssym, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.prod_neg, (Finset.mem_powersetCard.mp ht).2]

end BranchFamilies

section QCalculus
open UpperHalfPlane hiding I
open Complex Filter Function ModularForm ModularGroup CongruenceSubgroup
open Matrix.SpecialLinearGroup
open scoped Real Topology Manifold MatrixGroups ModularForm

/-- Functions on `ℍ` with a holomorphic `q`-expansion at `i∞` (period `1`). -/
structure NiceQ (f : ℍ → ℂ) : Prop where
  per : Periodic (f ∘ ofComplex) 1
  mdiff : MDiff f
  bdd : IsBoundedAtImInfty f

private lemma qParam_add_one (z : ℂ) : Periodic.qParam 1 (z + 1) = Periodic.qParam 1 z := by
  rw [qParam_one_eq_cexp, qParam_one_eq_cexp, mul_add, mul_one, Complex.exp_add,
    Complex.exp_two_pi_mul_I, mul_one]

namespace NiceQ

variable {f g : ℍ → ℂ}

private lemma analytic (hf : NiceQ f) : AnalyticAt ℂ (cuspFunction 1 f) 0 :=
  analyticAt_cuspFunction_zero one_pos hf.per hf.mdiff hf.bdd

private lemma mul (hf : NiceQ f) (hg : NiceQ g) : NiceQ (f * g) :=
  ⟨fun z => by
    show (f ∘ ofComplex) (z + 1) * (g ∘ ofComplex) (z + 1) = (f ∘ ofComplex) z * (g ∘ ofComplex) z
    rw [hf.per z, hg.per z], hf.mdiff.mul hg.mdiff, hf.bdd.mul hg.bdd⟩

private lemma add (hf : NiceQ f) (hg : NiceQ g) : NiceQ (f + g) :=
  ⟨fun z => by
    show (f ∘ ofComplex) (z + 1) + (g ∘ ofComplex) (z + 1) = (f ∘ ofComplex) z + (g ∘ ofComplex) z
    rw [hf.per z, hg.per z], hf.mdiff.add hg.mdiff, hf.bdd.add hg.bdd⟩

private lemma const (c : ℂ) : NiceQ (fun _ => c) :=
  ⟨fun _ => rfl, mdifferentiable_const, Filter.const_boundedAtFilter _ c⟩

private lemma one : NiceQ (1 : ℍ → ℂ) := const 1

private lemma zero : NiceQ (0 : ℍ → ℂ) := const 0

private lemma smul (c : ℂ) (hf : NiceQ f) : NiceQ (c • f) := by
  have h : c • f = (fun _ => c) * f := by ext τ; simp
  rw [h]; exact (const c).mul hf

private lemma neg (hf : NiceQ f) : NiceQ (-f) := by
  have h : -f = (-1 : ℂ) • f := by ext τ; simp
  rw [h]; exact hf.smul _

private lemma sub (hf : NiceQ f) (hg : NiceQ g) : NiceQ (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

private lemma pow (hf : NiceQ f) (n : ℕ) : NiceQ (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact one
  | succ n ih => rw [pow_succ]; exact ih.mul hf

private lemma sum {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ} (hF : ∀ i ∈ s, NiceQ (F i)) :
    NiceQ (∑ i ∈ s, F i) :=
  Finset.sum_induction _ NiceQ (fun _ _ h1 h2 => h1.add h2) zero hF

private lemma prod {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ} (hF : ∀ i ∈ s, NiceQ (F i)) :
    NiceQ (∏ i ∈ s, F i) :=
  Finset.prod_induction _ NiceQ (fun _ _ h1 h2 => h1.mul h2) one hF

private lemma qExp_mul (hf : NiceQ f) (hg : NiceQ g) :
    qExpansion 1 (f * g) = qExpansion 1 f * qExpansion 1 g :=
  qExpansion_mul hf.analytic hg.analytic

private lemma qExp_add (hf : NiceQ f) (hg : NiceQ g) :
    qExpansion 1 (f + g) = qExpansion 1 f + qExpansion 1 g :=
  qExpansion_add hf.analytic hg.analytic

private lemma qExp_sub (hf : NiceQ f) (hg : NiceQ g) :
    qExpansion 1 (f - g) = qExpansion 1 f - qExpansion 1 g :=
  qExpansion_sub hf.analytic hg.analytic

private lemma qExp_smul (c : ℂ) (hf : NiceQ f) :
    qExpansion 1 (c • f) = PowerSeries.C c * qExpansion 1 f := by
  rw [qExpansion_smul hf.analytic, PowerSeries.smul_eq_C_mul]

private lemma qExp_const (c : ℂ) : qExpansion 1 (fun _ : ℍ => c) = PowerSeries.C c := by
  have h : (fun _ : ℍ => c) = c • (1 : ℍ → ℂ) := by ext τ; simp
  rw [h, qExp_smul c one, qExpansion_one, mul_one]

private lemma qExp_pow (hf : NiceQ f) (n : ℕ) : qExpansion 1 (f ^ n) = qExpansion 1 f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, qExpansion_one]
  | succ n ih => rw [pow_succ, pow_succ, qExp_mul (hf.pow n) hf, ih]

private lemma qExp_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) {F : ι → ℍ → ℂ}
    (hF : ∀ i ∈ s, NiceQ (F i)) :
    qExpansion 1 (∑ i ∈ s, F i) = ∑ i ∈ s, qExpansion 1 (F i) := by
  induction s using Finset.induction_on with
  | empty => simpa using qExpansion_zero 1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      qExp_add (hF a (Finset.mem_insert_self a s))
        (sum s fun i hi => hF i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]

private lemma qExp_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) {F : ι → ℍ → ℂ}
    (hF : ∀ i ∈ s, NiceQ (F i)) :
    qExpansion 1 (∏ i ∈ s, F i) = ∏ i ∈ s, qExpansion 1 (F i) := by
  induction s using Finset.induction_on with
  | empty => simpa using qExpansion_one 1
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      qExp_mul (hF a (Finset.mem_insert_self a s))
        (prod s fun i hi => hF i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]

end NiceQ

/-- A holomorphic function with an everywhere-convergent `q`-expansion is `NiceQ`, and its
`q`-expansion is the given one. -/
private lemma niceQ_of_hasSum {f : ℍ → ℂ} {c : ℕ → ℂ} (hf : MDiff f)
    (hs : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam 1 τ ^ m) (f τ)) :
    NiceQ f ∧ qExpansion 1 f = PowerSeries.mk c := by
  have hper : Periodic (f ∘ ofComplex) 1 := by
    intro z
    by_cases hz : 0 < z.im
    · have hz1 : 0 < (z + 1).im := by simpa using hz
      simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos hz1]
      have e : Periodic.qParam 1 ((⟨z + 1, hz1⟩ : ℍ) : ℂ) =
          Periodic.qParam 1 ((⟨z, hz⟩ : ℍ) : ℂ) := by
        exact qParam_add_one z
      have h1 := hs ⟨z + 1, hz1⟩
      rw [e] at h1
      exact h1.unique (hs ⟨z, hz⟩)
    · have hz1 : ¬ 0 < (z + 1).im := by simpa using hz
      simp only [Function.comp_apply, ofComplex_apply_of_im_nonpos (not_lt.mp hz),
        ofComplex_apply_of_im_nonpos (not_lt.mp hz1)]
  have hN : NiceQ f := ⟨hper, hf, isBoundedAtImInfty_of_hasSum_qExpansion one_pos hs⟩
  refine ⟨hN, ?_⟩
  ext m
  rw [PowerSeries.coeff_mk]
  exact (qExpansion_coeff_unique_fun hN.analytic hs m).symm

/-- Composition of a function holomorphic on the unit disc with `q = e^{2πiτ}`. -/
private lemma niceQ_comp_qParam {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (Metric.ball 0 1)) :
    NiceQ (fun τ : ℍ => F (Periodic.qParam 1 τ)) ∧
      ∀ m, (qExpansion 1 (fun τ : ℍ => F (Periodic.qParam 1 τ))).coeff m =
        (m.factorial : ℂ)⁻¹ * iteratedDeriv m F 0 := by
  set f : ℍ → ℂ := fun τ => F (Periodic.qParam 1 τ) with hfdef
  have hper : Periodic (f ∘ ofComplex) 1 := by
    intro z
    by_cases hz : 0 < z.im
    · have hz1 : 0 < (z + 1).im := by simpa using hz
      simp only [hfdef, Function.comp_apply, ofComplex_apply_of_im_pos hz,
        ofComplex_apply_of_im_pos hz1, UpperHalfPlane.coe_mk, qParam_add_one]
    · have hz1 : ¬ 0 < (z + 1).im := by simpa using hz
      simp only [Function.comp_apply, ofComplex_apply_of_im_nonpos (not_lt.mp hz),
        ofComplex_apply_of_im_nonpos (not_lt.mp hz1)]
  have hmaps : Set.MapsTo (Periodic.qParam 1) upperHalfPlaneSet (Metric.ball 0 1) :=
    fun z hz => mem_ball_zero_iff.mpr (Periodic.norm_qParam_lt_one one_pos hz)
  have hmd : MDiff f := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine (hF.comp (Periodic.differentiable_qParam.differentiableOn) hmaps).congr fun z hz => ?_
    simp [hfdef, Function.comp_apply, ofComplex_apply_of_im_pos hz]
  have hcont : ContinuousAt F 0 :=
    hF.continuousOn.continuousAt (Metric.ball_mem_nhds (0 : ℂ) one_pos)
  have hbdd : IsBoundedAtImInfty f :=
    (hcont.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty one_pos)).isBigO_one ℝ
  have hN : NiceQ f := ⟨hper, hmd, hbdd⟩
  refine ⟨hN, fun m => ?_⟩
  have hev : cuspFunction 1 f =ᶠ[𝓝 (0 : ℂ)] F := by
    refine (hN.analytic.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hcont).mp ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) one_pos)] with q hq0 hq
    have him := Periodic.im_invQParam_pos_of_norm_lt_one one_pos
      (by simpa [dist_zero_right] using hq) hq0
    simp only [cuspFunction, Periodic.cuspFunction_eq_of_nonzero 1 _ hq0, Function.comp_apply,
      ofComplex_apply_of_im_pos him, hfdef, UpperHalfPlane.coe_mk,
      Periodic.qParam_right_inv one_ne_zero hq0]
  rw [qExpansion_coeff, hev.iteratedDeriv_eq]

/-- Affine maps `τ ↦ a τ + b` of the upper half-plane (`a > 0`, `b` real). -/
private def affH (a : ℝ) (ha : 0 < a) (b : ℝ) (τ : ℍ) : ℍ :=
  ⟨(a : ℂ) * τ + b, by simpa using mul_pos ha τ.im_pos⟩

@[simp]
private lemma coe_affH (a : ℝ) (ha : 0 < a) (b : ℝ) (τ : ℍ) :
    (affH a ha b τ : ℂ) = (a : ℂ) * τ + b := rfl

private lemma mdiff_comp_affH {f : ℍ → ℂ} (hf : MDiff f) (a : ℝ) (ha : 0 < a) (b : ℝ) :
    MDiff (fun τ : ℍ => f (affH a ha b τ)) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf ⊢
  have h2 : DifferentiableOn ℂ (fun z : ℂ => (a : ℂ) * z + b) upperHalfPlaneSet := by fun_prop
  have hmaps : Set.MapsTo (fun z : ℂ => (a : ℂ) * z + b) upperHalfPlaneSet upperHalfPlaneSet :=
    fun z hz => by
      change 0 < ((a : ℂ) * z + b).im
      have : 0 < z.im := hz
      simpa using mul_pos ha this
  refine (hf.comp h2 hmaps).congr fun z hz => ?_
  have hz2 : 0 < ((a : ℂ) * z + b).im := hmaps hz
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos hz2]
  rfl

/-- Scaling `τ ↦ n τ`. -/
private noncomputable def smulN (n : ℕ) [NeZero n] (τ : ℍ) : ℍ :=
  affH n (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)) 0 τ

@[simp]
private lemma coe_smulN (n : ℕ) [NeZero n] (τ : ℍ) : (smulN n τ : ℂ) = (n : ℂ) * τ := by
  simp [smulN]

private lemma qParam_smulN (n : ℕ) [NeZero n] (τ : ℍ) :
    Periodic.qParam 1 (smulN n τ : ℂ) = Periodic.qParam 1 τ ^ n := by
  rw [coe_smulN, qParam_one_eq_cexp, qParam_one_eq_cexp, ← Complex.exp_nat_mul]
  congr 1; ring

private lemma NiceQ.comp_smulN {f : ℍ → ℂ} (hf : NiceQ f) (n : ℕ) [NeZero n] :
    NiceQ (fun τ => f (smulN n τ)) ∧
      qExpansion 1 (fun τ => f (smulN n τ)) =
        PowerSeries.expand n (NeZero.ne n) (qExpansion 1 f) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hmd : MDiff (fun τ => f (smulN n τ)) := mdiff_comp_affH hf.mdiff _ _ 0
  have hs : ∀ τ : ℍ, HasSum (fun m => ((PowerSeries.expand n (NeZero.ne n) (qExpansion 1 f)).coeff m) •
      Periodic.qParam 1 τ ^ m) (f (smulN n τ)) := by
    intro τ
    have h0 := hasSum_qExpansion one_pos hf.per hf.mdiff hf.bdd (smulN n τ)
    rw [qParam_smulN] at h0
    have hinj : Function.Injective (fun k : ℕ => n * k) := fun a b h => by
      simpa [hn.ne'] using h
    rw [← hasSum_extend_zero hinj] at h0
    convert h0 using 1
    ext m
    rw [PowerSeries.coeff_expand]
    split_ifs with hdvd
    · obtain ⟨k, rfl⟩ := hdvd
      rw [hinj.extend_apply, Nat.mul_div_cancel_left _ hn, ← pow_mul]
    · rw [Function.extend_apply' _ _ _ (by rintro ⟨k, rfl⟩; exact hdvd ⟨k, rfl⟩)]
      simp
  obtain ⟨hN, hq⟩ := niceQ_of_hasSum hmd hs
  refine ⟨hN, ?_⟩
  rw [hq]
  ext m; simp

/-- The shifts `τ ↦ (τ + j)/p`. -/
private noncomputable def shiftH (p : ℕ) [NeZero p] (j : ℕ) (τ : ℍ) : ℍ :=
  affH (1 / p) (by
    have : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
    positivity) (j / p) τ

@[simp]
private lemma coe_shiftH (p : ℕ) [NeZero p] (j : ℕ) (τ : ℍ) :
    (shiftH p j τ : ℂ) = ((τ : ℂ) + j) / p := by
  simp [shiftH]
  ring

private lemma smulN_shiftH (p : ℕ) [NeZero p] (j : ℕ) (τ : ℍ) :
    (smulN p (shiftH p j τ) : ℂ) = (τ : ℂ) + j := by
  have : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  rw [coe_smulN, coe_shiftH]; field_simp

/-- `∑_{j < p} F((τ + j)/p)`. -/
private noncomputable def shiftSum (p : ℕ) [NeZero p] (F : ℍ → ℂ) (τ : ℍ) : ℂ :=
  ∑ j ∈ Finset.range p, F (shiftH p j τ)

private lemma sum_qParam_shift_pow (p : ℕ) [NeZero p] (hp : p.Prime) (τ : ℍ) (n : ℕ) :
    ∑ j ∈ Finset.range p, Periodic.qParam 1 (shiftH p j τ : ℂ) ^ n =
      if p ∣ n then (p : ℂ) * Periodic.qParam 1 τ ^ (n / p) else 0 := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set ζ : ℂ := Complex.exp (2 * π * I / p) with hζ
  have hterm (j : ℕ) : Periodic.qParam 1 (shiftH p j τ : ℂ) ^ n =
      Complex.exp (2 * π * I * τ * n / p) * (ζ ^ n) ^ j := by
    rw [coe_shiftH, qParam_one_eq_cexp, ← Complex.exp_nat_mul, hζ, ← Complex.exp_nat_mul,
      ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1; field_simp
  simp only [hterm, ← Finset.mul_sum]
  have hprim : IsPrimitiveRoot ζ p := Complex.isPrimitiveRoot_exp p hp.ne_zero
  split_ifs with hdvd
  · obtain ⟨k, rfl⟩ := hdvd
    have h1 : ζ ^ (p * k) = 1 := by rw [pow_mul, hprim.pow_eq_one, one_pow]
    rw [h1]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [Nat.mul_div_cancel_left _ hp.pos, qParam_one_eq_cexp, ← Complex.exp_nat_mul, mul_comm]
    congr 2; push_cast; field_simp
  · have hcop : Nat.Coprime n p := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hdvd))
    have hprim' : IsPrimitiveRoot (ζ ^ n) p := hprim.pow_of_coprime n hcop
    rw [hprim'.geom_sum_eq_zero hp.one_lt, mul_zero]

private lemma NiceQ.shift_sum {F : ℍ → ℂ} (hF : NiceQ F) (p : ℕ) [NeZero p] (hp : p.Prime) :
    NiceQ (OMA.shiftSum p F) ∧
      qExpansion 1 (OMA.shiftSum p F) =
        PowerSeries.mk fun m => (p : ℂ) * (qExpansion 1 F).coeff (p * m) := by
  have hmd : MDiff (OMA.shiftSum p F) := by
    have : OMA.shiftSum p F = ∑ j ∈ Finset.range p, fun τ => F (shiftH p j τ) := by
      ext τ; simp [shiftSum, Finset.sum_apply]
    rw [this]
    exact Finset.sum_induction _ (fun f : ℍ → ℂ => MDiff f) (fun f g hf hg => hf.add hg)
      mdifferentiable_const (fun j _ => mdiff_comp_affH hF.mdiff _ _ _)
  have hs : ∀ τ : ℍ, HasSum (fun m => ((p : ℂ) * (qExpansion 1 F).coeff (p * m)) •
      Periodic.qParam 1 τ ^ m) (OMA.shiftSum p F τ) := by
    intro τ
    have h0 : HasSum (fun n => ∑ j ∈ Finset.range p,
        (qExpansion 1 F).coeff n • Periodic.qParam 1 (shiftH p j τ : ℂ) ^ n) (OMA.shiftSum p F τ) :=
      hasSum_sum fun j _ => hasSum_qExpansion one_pos hF.per hF.mdiff hF.bdd (shiftH p j τ)
    simp only [smul_eq_mul, ← Finset.mul_sum, sum_qParam_shift_pow p hp τ] at h0
    have hinj : Function.Injective (fun k : ℕ => p * k) := fun a b h => by
      simpa [hp.ne_zero] using h
    rw [← hasSum_extend_zero hinj]
    convert h0 using 1
    ext n
    split_ifs with hdvd
    · obtain ⟨k, rfl⟩ := hdvd
      rw [hinj.extend_apply, Nat.mul_div_cancel_left _ hp.pos, smul_eq_mul]
      ring
    · rw [Function.extend_apply' _ _ _ (by rintro ⟨k, rfl⟩; exact hdvd ⟨k, rfl⟩)]
      simp
  exact niceQ_of_hasSum hmd hs

/-- The power `q^k` of the uniformizer. -/
private lemma niceQ_qParam_pow (k : ℕ) :
    NiceQ (fun τ : ℍ => Periodic.qParam 1 τ ^ k) ∧
      qExpansion 1 (fun τ : ℍ => Periodic.qParam 1 τ ^ k) = PowerSeries.X ^ k := by
  have hmd : MDiff (fun τ : ℍ => Periodic.qParam 1 τ ^ k) := by
    have h := (niceQ_comp_qParam (F := fun q : ℂ => q ^ k) (by fun_prop)).1.mdiff
    exact h
  have hs : ∀ τ : ℍ, HasSum (fun m => (if m = k then (1 : ℂ) else 0) • Periodic.qParam 1 τ ^ m)
      (Periodic.qParam 1 τ ^ k) := by
    intro τ
    convert hasSum_ite_eq k (Periodic.qParam 1 (τ : ℂ) ^ k) using 1
    ext m
    split_ifs with h <;> simp [h]
  obtain ⟨hN, hq⟩ := niceQ_of_hasSum hmd hs
  refine ⟨hN, ?_⟩
  rw [hq]
  ext m
  simp [PowerSeries.coeff_X_pow]

/-- Integral `q`-expansions. -/
private def HasIntQ (f : ℍ → ℂ) (F : PowerSeries ℤ) : Prop :=
  NiceQ f ∧ qExpansion 1 f = F.map (Int.castRingHom ℂ)

namespace HasIntQ

variable {f g : ℍ → ℂ} {F G : PowerSeries ℤ}

private lemma mul (hf : HasIntQ f F) (hg : HasIntQ g G) : HasIntQ (f * g) (F * G) :=
  ⟨hf.1.mul hg.1, by rw [hf.1.qExp_mul hg.1, hf.2, hg.2, map_mul]⟩

private lemma add (hf : HasIntQ f F) (hg : HasIntQ g G) : HasIntQ (f + g) (F + G) :=
  ⟨hf.1.add hg.1, by rw [hf.1.qExp_add hg.1, hf.2, hg.2, map_add]⟩

private lemma sub (hf : HasIntQ f F) (hg : HasIntQ g G) : HasIntQ (f - g) (F - G) :=
  ⟨hf.1.sub hg.1, by rw [hf.1.qExp_sub hg.1, hf.2, hg.2, map_sub]⟩

private lemma const (c : ℤ) : HasIntQ (fun _ => (c : ℂ)) (PowerSeries.C c) :=
  ⟨NiceQ.const _, by rw [NiceQ.qExp_const, PowerSeries.map_C]; rfl⟩

private lemma one : HasIntQ 1 1 := ⟨NiceQ.one, by rw [qExpansion_one, map_one]⟩

private lemma zsmul (c : ℤ) (hf : HasIntQ f F) : HasIntQ ((c : ℂ) • f) (PowerSeries.C c * F) :=
  ⟨hf.1.smul _, by rw [NiceQ.qExp_smul _ hf.1, hf.2, map_mul, PowerSeries.map_C]; rfl⟩

private lemma pow (hf : HasIntQ f F) (n : ℕ) : HasIntQ (f ^ n) (F ^ n) :=
  ⟨hf.1.pow n, by rw [hf.1.qExp_pow n, hf.2, map_pow]⟩

private lemma sum {ι : Type*} [DecidableEq ι] (s : Finset ι) {f : ι → ℍ → ℂ} {F : ι → PowerSeries ℤ}
    (hf : ∀ i ∈ s, HasIntQ (f i) (F i)) : HasIntQ (∑ i ∈ s, f i) (∑ i ∈ s, F i) :=
  ⟨NiceQ.sum s fun i hi => (hf i hi).1, by
    rw [NiceQ.qExp_sum s fun i hi => (hf i hi).1, map_sum]
    exact Finset.sum_congr rfl fun i hi => (hf i hi).2⟩

private lemma prod {ι : Type*} [DecidableEq ι] (s : Finset ι) {f : ι → ℍ → ℂ} {F : ι → PowerSeries ℤ}
    (hf : ∀ i ∈ s, HasIntQ (f i) (F i)) : HasIntQ (∏ i ∈ s, f i) (∏ i ∈ s, F i) :=
  ⟨NiceQ.prod s fun i hi => (hf i hi).1, by
    rw [NiceQ.qExp_prod s fun i hi => (hf i hi).1, map_prod]
    exact Finset.prod_congr rfl fun i hi => (hf i hi).2⟩

private lemma congr_fun (hf : HasIntQ f F) (h : f = g) : HasIntQ g F := h ▸ hf

private lemma comp_smulN (hf : HasIntQ f F) (n : ℕ) [NeZero n] :
    HasIntQ (fun τ => f (smulN n τ)) (PowerSeries.expand n (NeZero.ne n) F) := by
  obtain ⟨hN, hq⟩ := hf.1.comp_smulN n
  exact ⟨hN, by rw [hq, hf.2, PowerSeries.map_expand]⟩

private lemma shift_sum (hf : HasIntQ f F) (p : ℕ) [NeZero p] (hp : p.Prime) :
    HasIntQ (OMA.shiftSum p f) (PowerSeries.mk fun m => (p : ℤ) * F.coeff (p * m)) := by
  obtain ⟨hN, hq⟩ := hf.1.shift_sum p hp
  refine ⟨hN, ?_⟩
  rw [hq, hf.2]
  ext m
  simp

private lemma qParam_pow (k : ℕ) :
    HasIntQ (fun τ : ℍ => Periodic.qParam 1 τ ^ k) (PowerSeries.X ^ k) :=
  ⟨(niceQ_qParam_pow k).1, by rw [(niceQ_qParam_pow k).2, map_pow, PowerSeries.map_X]⟩

private lemma unique (hf : HasIntQ f F) (hg : HasIntQ f G) : F = G := by
  apply int_map_inj
  rw [← hf.2, ← hg.2]

end HasIntQ

end QCalculus

section EtaQSeries
open UpperHalfPlane hiding I
open Complex Filter Function ModularForm ModularGroup CongruenceSubgroup
open Matrix.SpecialLinearGroup
open scoped Real Topology Manifold MatrixGroups ModularForm

private lemma eta4_prod_fn_differentiableOn : DifferentiableOn ℂ eta4_prod_fn (Metric.ball 0 1) := by
  have hf1 : DifferentiableOn ℂ (fun q : ℂ ↦ ∏' n : ℕ, (1 - (q ^ 1) ^ (n + 1)) ^ 4)
      (Metric.ball 0 1) :=
    (ModularForm.differentiableOn_tprod_one_sub_pow_pow 4).congr fun q _ => by simp
  have hf2 : DifferentiableOn ℂ (fun q : ℂ ↦ ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) ^ 4)
      (Metric.ball 0 1) :=
    (ModularForm.differentiableOn_tprod_one_sub_pow_pow 4).comp
      (differentiable_pow 2).differentiableOn fun q hq => by
        rw [mem_ball_zero_iff, norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp hq) two_ne_zero
  exact hf1.mul hf2

/-- $\eta_4(\tau) = e^{\pi i \tau} V(q)$ with $V(q) = \prod (1-q^n)^4 (1-q^{2n})^4$. -/
private lemma eta4_eq_exp_mul (τ : ℍ) :
    eta4 τ = cexp (π * I * τ) * eta4_prod_fn (Periodic.qParam 1 τ) := by
  have hq1 : ‖Periodic.qParam 1 (τ : ℂ)‖ < 1 := Periodic.norm_qParam_lt_one one_pos τ.im_pos
  have hq2 : ‖Periodic.qParam 1 (τ : ℂ) ^ 2‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq1 two_ne_zero
  have mp1 := ModularForm.multipliable_one_sub_pow hq1
  have mp2 := ModularForm.multipliable_one_sub_pow hq2
  have e1 : ∀ n, ModularForm.eta_q n (τ : ℂ) = Periodic.qParam 1 (τ : ℂ) ^ (n + 1) := by
    intro n; rw [ModularForm.eta_q_eq_pow, qParam_one_eq_cexp]
  have e2 : ∀ n, ModularForm.eta_q n (mul2 τ : ℂ) = (Periodic.qParam 1 (τ : ℂ) ^ 2) ^ (n + 1) := by
    intro n
    have h2 : cexp (2 * π * I * (2 * (τ : ℂ))) = cexp (2 * π * I * τ) ^ 2 := by
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    rw [ModularForm.eta_q_eq_pow, qParam_one_eq_cexp, coe_mul2, h2]
  have hq : Periodic.qParam 24 (τ : ℂ) ^ 4 * Periodic.qParam 24 (mul2 τ : ℂ) ^ 4 =
      cexp (π * I * τ) := by
    simp only [Periodic.qParam, coe_mul2, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hV : eta4_prod_fn (Periodic.qParam 1 τ) =
      (∏' n : ℕ, (1 - Periodic.qParam 1 (τ : ℂ) ^ (n + 1))) ^ 4 *
        (∏' n : ℕ, (1 - (Periodic.qParam 1 (τ : ℂ) ^ 2) ^ (n + 1))) ^ 4 := by
    rw [eta4_prod_fn]
    simp only [pow_one]
    rw [mp1.tprod_pow 4, mp2.tprod_pow 4]
  simp only [eta4, ModularForm.eta, mul_pow, e1, e2]
  rw [hV]
  linear_combination (∏' n : ℕ, (1 - Periodic.qParam 1 (τ : ℂ) ^ (n + 1))) ^ 4 *
    (∏' n : ℕ, (1 - (Periodic.qParam 1 (τ : ℂ) ^ 2) ^ (n + 1))) ^ 4 * hq

private lemma eta4_prod_fn_ne_zero {q : ℂ} (hq : q ∈ Metric.ball (0 : ℂ) 1) : eta4_prod_fn q ≠ 0 := by
  by_cases hq0 : q = 0
  · subst hq0; simp [eta4_prod_fn]
  · have him := Periodic.im_invQParam_pos_of_norm_lt_one one_pos
      (by simpa [dist_zero_right] using hq) hq0
    let τ : ℍ := ⟨Periodic.invQParam 1 q, him⟩
    have hqτ : Periodic.qParam 1 (τ : ℂ) = q := Periodic.qParam_right_inv one_ne_zero hq0
    have h := eta4_ne_zero τ
    rw [eta4_eq_exp_mul, hqτ] at h
    exact right_ne_zero_of_mul h

/-- $V(\tau) = \eta_4(\tau) e^{-\pi i \tau}$, a holomorphic function of `q`. -/
private noncomputable def Vfn (τ : ℍ) : ℂ := eta4_prod_fn (Periodic.qParam 1 τ)

/-- $1/V$. -/
private noncomputable def Vinv (τ : ℍ) : ℂ := (eta4_prod_fn (Periodic.qParam 1 τ))⁻¹

private lemma Vfn_ne_zero (τ : ℍ) : Vfn τ ≠ 0 :=
  eta4_prod_fn_ne_zero (mem_ball_zero_iff.mpr (Periodic.norm_qParam_lt_one one_pos τ.im_pos))

private lemma Vinv_mul_Vfn : Vinv * Vfn = 1 := by
  ext τ
  simp only [Pi.mul_apply, Pi.one_apply, Vinv]
  exact inv_mul_cancel₀ (Vfn_ne_zero τ)

private noncomputable def V_ps_inv : PowerSeries ℤ :=
  ((isUnit_of_coeff_zero_one eta4_prod_ps_int_coeff_zero).unit⁻¹ : (PowerSeries ℤ)ˣ)

private lemma V_ps_mul_inv : eta4_prod_ps_int * V_ps_inv = 1 :=
  (isUnit_of_coeff_zero_one eta4_prod_ps_int_coeff_zero).unit.mul_inv

private lemma V_ps_inv_coeff_zero : V_ps_inv.coeff 0 = 1 := by
  have h := congrArg (PowerSeries.coeff 0) V_ps_mul_inv
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, eta4_prod_ps_int_coeff_zero, one_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_one] at h
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact h

private lemma hasIntQ_Vfn : HasIntQ Vfn eta4_prod_ps_int := by
  obtain ⟨hN, hc⟩ := niceQ_comp_qParam eta4_prod_fn_differentiableOn
  refine ⟨hN, ?_⟩
  ext m
  rw [PowerSeries.coeff_map, Int.coe_castRingHom]
  exact (hc m).trans (eta4_prod_ps_int_coeff_C m).symm

private lemma hasIntQ_Vinv : HasIntQ Vinv V_ps_inv := by
  have hd : DifferentiableOn ℂ (fun q => (eta4_prod_fn q)⁻¹) (Metric.ball 0 1) :=
    eta4_prod_fn_differentiableOn.inv fun q hq => eta4_prod_fn_ne_zero hq
  have hN : NiceQ Vinv := (niceQ_comp_qParam hd).1
  refine ⟨hN, ?_⟩
  have h1 : qExpansion 1 Vinv * qExpansion 1 Vfn = 1 := by
    rw [← hN.qExp_mul hasIntQ_Vfn.1, Vinv_mul_Vfn, qExpansion_one]
  calc qExpansion 1 Vinv
      = qExpansion 1 Vinv * (eta4_prod_ps_int.map (Int.castRingHom ℂ) *
          V_ps_inv.map (Int.castRingHom ℂ)) := by
        rw [← map_mul, V_ps_mul_inv, map_one, mul_one]
    _ = V_ps_inv.map (Int.castRingHom ℂ) := by
        rw [← mul_assoc, ← hasIntQ_Vfn.2, h1, one_mul]

private lemma niceQ_E2star : NiceQ E2star :=
  ⟨SlashInvariantFormClass.periodic_comp_ofComplex (f := E2starMF) one_mem_strictPeriods_Γ02,
    E2star_mdiff, isBoundedAtImInfty_E2star⟩

private lemma hasIntQ_E2star : HasIntQ E2star E2star_ps_int :=
  ⟨niceQ_E2star, E2star_ps_int_map_C.symm⟩

private lemma niceQ_Delta8 : NiceQ Delta8 :=
  ⟨SlashInvariantFormClass.periodic_comp_ofComplex (f := Delta8MF) one_mem_strictPeriods_Γ02,
    Delta8_mdiff, Delta8_isZeroAtImInfty.isBoundedAtImInfty⟩

private lemma hasIntQ_Delta8 : HasIntQ Delta8 Delta8_ps_int :=
  ⟨niceQ_Delta8, Delta8_ps_int_map_C.symm⟩

/-- $W = E_2^* / V$. -/
private noncomputable def Wfn : ℍ → ℂ := E2star * Vinv

private lemma hasIntQ_Wfn : HasIntQ Wfn (E2star_ps_int * V_ps_inv) :=
  hasIntQ_E2star.mul hasIntQ_Vinv

private lemma Vfn_add_int (τ : ℍ) (j : ℕ) (z : ℍ) (hz : (z : ℂ) = τ + j) : Vfn z = Vfn τ := by
  have hq : Periodic.qParam 1 (z : ℂ) = Periodic.qParam 1 (τ : ℂ) := by
    rw [hz, qParam_one_eq_cexp, qParam_one_eq_cexp, mul_add, Complex.exp_add,
      show 2 * π * I * (j : ℂ) = (j : ℂ) * (2 * π * I) by ring, Complex.exp_nat_mul_two_pi_mul_I,
      mul_one]
  simp only [Vfn, hq]

end EtaQSeries

section NuFamily
open UpperHalfPlane hiding I
open Complex Filter Function ModularForm ModularGroup CongruenceSubgroup
open Matrix.SpecialLinearGroup
open scoped Real Topology Manifold MatrixGroups ModularForm

private lemma apply_of_slash_eq {k : ℤ} {g : GL (Fin 2) ℝ} (hg : g.det.val = 1) {f : ℍ → ℂ} {c : ℂ}
    (h : f ∣[k] g = c • f) (τ : ℍ) : f (g • τ) = c * denom g τ ^ k * f τ := by
  have h1 := congrFun h τ
  rw [slash_apply_of_det_pos (by rw [hg]; exact one_pos), hg, Complex.ofReal_one, one_zpow,
    mul_one, Pi.smul_apply, smul_eq_mul] at h1
  have hd : denom g τ ^ k ≠ 0 := zpow_ne_zero _ (denom_ne_zero g τ)
  rw [zpow_neg] at h1
  field_simp at h1
  linear_combination h1

private lemma smul_slash_of_det_pos {k : ℤ} {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (f : ℍ → ℂ) (c : ℂ) :
    (c • f) ∣[k] g = c • (f ∣[k] g) := by
  ext τ
  simp only [slash_apply_of_det_pos hg, Pi.smul_apply, smul_eq_mul]
  ring

private lemma chiInt_conjW {M : Matrix (Fin 2) (Fin 2) ℤ} (hc : (2 : ℤ) ∣ M 1 0) :
    chiInt (conjW M) = chiInt M := by
  obtain ⟨c, hc⟩ := hc
  have h1 : conjW M 1 0 / 2 = -M 0 1 := by rw [conjW_eq hc]; simp; omega
  have h2 : conjW M 0 1 = -c := by rw [conjW_eq hc]; simp
  have h3 : M 1 0 / 2 = c := by rw [hc]; omega
  unfold chiInt
  rw [h1, h2, h3]
  simp only [show -c + -M 0 1 = -(M 0 1 + c) by ring, even_neg]

private lemma chiInt_pow_odd (M : Matrix (Fin 2) (Fin 2) ℤ) (h : ℕ) : chiInt M ^ (2 * h + 1) = chiInt M := by
  rw [pow_succ, pow_mul, chiInt_sq, one_pow, one_mul]

/-- $16^{p-1}$. -/
private def Cn (p : ℕ) : ℤ := 16 ^ (p - 1)

/-- The twisted Hecke branch $\nu_M = 16^{p-1} p^2 \chi(M)\,\eta_4^p\,(E_2^*|M)/(\eta_4|M)$. -/
private noncomputable def nuFam (p : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) (τ : ℍ) : ℂ :=
  ((Cn p : ℂ) * (p : ℂ) ^ 2 * chiInt M) * eta4 τ ^ p *
    (E2star ∣[(2 : ℤ)] glZ M) τ / (eta4 ∣[(4 : ℤ)] glZ M) τ

private lemma glZ_det_pos {p : ℕ} (hp : p.Prime) {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M.det = p) :
    0 < (glZ M).det.val := by
  rw [glZ_det (by rw [hM]; exact_mod_cast hp.ne_zero), hM]
  exact_mod_cast hp.pos

private lemma eta4_slash_glZ_ne_zero {p : ℕ} (hp : p.Prime) {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hM : M.det = p) (τ : ℍ) : (eta4 ∣[(4 : ℤ)] glZ M) τ ≠ 0 := by
  have hpos := glZ_det_pos hp hM
  rw [slash_apply_of_det_pos hpos]
  refine mul_ne_zero (mul_ne_zero (eta4_ne_zero _) (zpow_ne_zero _ ?_)) (zpow_ne_zero _
    (denom_ne_zero _ _))
  exact_mod_cast hpos.ne'

private lemma E2star_slash_glZ_left {σ : SL(2, ℤ)} (hσ : σ ∈ Gamma0 2) {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hM : M.det ≠ 0) :
    E2star ∣[(2 : ℤ)] glZ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * M) = E2star ∣[(2 : ℤ)] glZ M := by
  have h1 : (σ : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by rw [σ.2]; exact one_ne_zero
  rw [glZ_mul h1 hM, ← mapGL_eq_glZ, SlashAction.slash_mul]
  have h2 : E2star ∣[(2 : ℤ)] mapGL ℝ σ = E2star := E2star_slash_Gamma02 σ hσ
  rw [h2]

private lemma eta4_slash_glZ_left {σ : SL(2, ℤ)} (hσ : σ ∈ Gamma0 2) {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hMp : 0 < (glZ M).det.val) (hM : M.det ≠ 0) :
    eta4 ∣[(4 : ℤ)] glZ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * M) =
      chiInt σ.1 • (eta4 ∣[(4 : ℤ)] glZ M) := by
  have h1 : (σ : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by rw [σ.2]; exact one_ne_zero
  rw [glZ_mul h1 hM, ← mapGL_eq_glZ, SlashAction.slash_mul]
  have h2 : eta4 ∣[(4 : ℤ)] mapGL ℝ σ = chiInt σ.1 • eta4 := eta4_slash_Gamma02 σ hσ
  rw [h2, smul_slash_of_det_pos hMp]

private lemma odd_det_SL (σ : SL(2, ℤ)) : Odd (σ : Matrix (Fin 2) (Fin 2) ℤ).det := by
  rw [σ.2]; exact odd_one

private lemma odd_p {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) : Odd (p : ℤ) := by
  have := hp.odd_of_ne_two (by omega)
  exact_mod_cast this

/-- The branches $\nu_M$ form a branch family of weight $2(2p-1)$. -/
private lemma nuFam_isBranchFamily {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    IsBranchFamily p (2 * p - 1) (nuFam p) := by
  obtain ⟨h, hh⟩ := hp.odd_of_ne_two (by omega)
  have hn : ((2 * p - 1 : ℕ) : ℤ) = 4 * h + 1 := by rw [hh]; omega
  have hn' : (2 * p - 1 : ℕ) = 4 * h + 1 := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro σ hσ M hM hc
    have hM0 : M.det ≠ 0 := by rw [hM]; exact_mod_cast hp.ne_zero
    have hMp := glZ_det_pos hp hM
    ext τ
    simp only [nuFam]
    rw [E2star_slash_glZ_left hσ hM0, eta4_slash_glZ_left hσ hMp hM0,
      chiInt_mul (two_dvd_of_Gamma0 hσ) hc (odd_det_SL σ) (by rw [hM]; exact odd_p hp hp2)]
    have hne := eta4_slash_glZ_ne_zero hp hM τ
    have hχ : chiInt σ.1 ^ 2 = 1 := chiInt_sq _
    have hχ0 : chiInt σ.1 ≠ 0 := by intro h0; rw [h0] at hχ; norm_num at hχ
    rw [Pi.smul_apply, smul_eq_mul]
    field_simp
  · intro σ hσ M hM hc τ
    have hM0 : M.det ≠ 0 := by rw [hM]; exact_mod_cast hp.ne_zero
    have hσ0 : (σ : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by rw [σ.2]; exact one_ne_zero
    have hMσ : (M * (σ : Matrix (Fin 2) (Fin 2) ℤ)).det = p := by
      rw [Matrix.det_mul, hM, σ.2, mul_one]
    have hglZ : glZ (M * (σ : Matrix (Fin 2) (Fin 2) ℤ)) = glZ M * mapGL ℝ σ := by
      rw [glZ_mul hM0 hσ0, ← mapGL_eq_glZ]
    have hE := slash_comp_apply (k := 2) (glZ M) (mapGL ℝ σ) (mapGL_det σ) E2star τ
    have hη := slash_comp_apply (k := 4) (glZ M) (mapGL ℝ σ) (mapGL_det σ) eta4 τ
    have hη0 : eta4 (mapGL ℝ σ • τ) = chiInt σ.1 * denom (mapGL ℝ σ) τ ^ (4 : ℤ) * eta4 τ :=
      apply_of_slash_eq (mapGL_det σ) (eta4_slash_Gamma02 σ hσ) τ
    rw [← hglZ] at hE hη
    simp only [nuFam]
    rw [hE, hη, hη0, chiInt_mul hc (two_dvd_of_Gamma0 hσ) (by rw [hM]; exact odd_p hp hp2)
      (odd_det_SL σ)]
    have hne := eta4_slash_glZ_ne_zero hp hMσ τ
    have hd : denom (mapGL ℝ σ) τ ≠ 0 := denom_ne_zero _ τ
    rw [hn]
    have hz4 : denom (mapGL ℝ σ) τ ^ (4 : ℤ) = denom (mapGL ℝ σ) τ ^ (4 : ℕ) := by
      norm_cast
    have hz2 : denom (mapGL ℝ σ) τ ^ (2 : ℤ) = denom (mapGL ℝ σ) τ ^ (2 : ℕ) := by
      norm_cast
    have hz : denom (mapGL ℝ σ) τ ^ (2 * (4 * (h : ℤ) + 1)) =
        denom (mapGL ℝ σ) τ ^ (8 * h + 2 : ℕ) := by
      rw [← zpow_natCast]; congr 1; push_cast; ring
    rw [hz4, hz2, hz]
    have hχ := chiInt_pow_odd σ.1 h
    subst hh
    rw [mul_pow, mul_pow, hχ]
    field_simp
    ring
  · intro M hM hc τ
    have hM0 : M.det ≠ 0 := by rw [hM]; exact_mod_cast hp.ne_zero
    have hcM : (conjW M).det = p := by rw [conjW_det hc, hM]
    have hglZ : glZ M * W2 = W2 * glZ (conjW M) := glZ_mul_W2 hM0 hc
    have hE := slash_comp_apply (k := 2) (glZ M) W2 W2_det_val E2star τ
    have hη := slash_comp_apply (k := 4) (glZ M) W2 W2_det_val eta4 τ
    rw [hglZ, SlashAction.slash_mul, E2star_slash_W2, SlashAction.neg_slash] at hE
    rw [hglZ, SlashAction.slash_mul, eta4_slash_W2] at hη
    have hη0 : eta4 (W2 • τ) = 1 * denom W2 τ ^ (4 : ℤ) * eta4 τ :=
      apply_of_slash_eq W2_det_val (by rw [one_smul]; exact eta4_slash_W2) τ
    simp only [nuFam]
    rw [hE, hη, hη0, chiInt_conjW hc, Pi.neg_apply]
    have hne := eta4_slash_glZ_ne_zero hp hcM τ
    have hd : denom W2 τ ≠ 0 := denom_ne_zero _ τ
    rw [hn, hn']
    have hz4 : denom W2 τ ^ (4 : ℤ) = denom W2 τ ^ (4 : ℕ) := by
      norm_cast
    have hz2 : denom W2 τ ^ (2 : ℤ) = denom W2 τ ^ (2 : ℕ) := by
      norm_cast
    have hz : denom W2 τ ^ (2 * (4 * (h : ℤ) + 1)) = denom W2 τ ^ (8 * h + 2 : ℕ) := by
      rw [← zpow_natCast]; congr 1; push_cast; ring
    rw [hz4, hz2, hz]
    subst hh
    rw [show (-1 : ℂ) ^ (4 * h + 1) = -1 by rw [pow_succ, pow_mul]; norm_num]
    field_simp
    ring

private lemma nuFam_mdiff {p : ℕ} (hp : p.Prime) {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M.det = p) :
    MDiff (nuFam p M) := by
  have h1 : MDiff (fun τ => ((Cn p : ℂ) * (p : ℂ) ^ 2 * chiInt M) * eta4 τ ^ p *
      (E2star ∣[(2 : ℤ)] glZ M) τ) :=
    (mdifferentiable_const.mul (eta4_mdiff.pow p)).mul (E2star_mdiff.slash 2 (glZ M))
  exact h1.div (eta4_mdiff.slash 4 (glZ M)) (eta4_slash_glZ_ne_zero hp hM)

/- #### Explicit formulas for the branches -/

private lemma chiInt_gmat_none (p : ℕ) : chiInt (gmat p none) = 1 := by
  simp [chiInt, gmat]

private lemma chiInt_gmat_some (p : ℕ) (j : ZMod p) : chiInt (gmat p (some j)) = (-1) ^ j.val := by
  rcases Nat.even_or_odd j.val with he | ho
  · simp [chiInt, gmat, he, he.neg_one_pow, Int.even_coe_nat]
  · have : ¬ Even (j.val : ℤ) := by
      rw [Int.even_coe_nat]; exact Nat.not_even_iff_odd.mpr ho
    simp [chiInt, gmat, this, ho.neg_one_pow]

private lemma glZ_gmat_none_smul {p : ℕ} [NeZero p] (hp : p.Prime) (τ : ℍ) :
    glZ (gmat p none) • τ = smulN p τ := by
  ext
  rw [coe_glZ_smul (by rw [gmat_det]; exact_mod_cast hp.pos), coe_smulN]
  simp [gmat]

private lemma glZ_gmat_some_smul {p : ℕ} [NeZero p] (hp : p.Prime) (j : ZMod p) (τ : ℍ) :
    glZ (gmat p (some j)) • τ = shiftH p j.val τ := by
  ext
  rw [coe_glZ_smul (by rw [gmat_det]; exact_mod_cast hp.pos), coe_shiftH]
  simp [gmat]

private lemma exp_pi_pow (z : ℂ) (n : ℕ) : cexp (π * I * z) ^ n = cexp (π * I * ((n : ℂ) * z)) := by
  rw [← Complex.exp_nat_mul]; congr 1; ring

private lemma nuFam_none {p : ℕ} [NeZero p] (hp : p.Prime) :
    nuFam p (gmat p none) = (Cn p : ℂ) • (Vfn ^ p * fun τ => Wfn (smulN p τ)) := by
  have hdet : (gmat p none).det ≠ 0 := by rw [gmat_det]; exact_mod_cast hp.ne_zero
  have hpos : 0 < (glZ (gmat p none)).det.val := glZ_det_pos hp (gmat_det p none)
  have hden (τ : ℍ) : denom (glZ (gmat p none)) τ = 1 := by
    rw [denom_glZ hdet]; simp [gmat]
  have hdetv : ((glZ (gmat p none)).det.val : ℂ) = p := by
    rw [glZ_det hdet, gmat_det]; push_cast; rfl
  ext τ
  simp only [nuFam, slash_apply_of_det_pos hpos, glZ_gmat_none_smul hp, hden, hdetv,
    chiInt_gmat_none, one_zpow, mul_one, Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul,
    Wfn, Vinv]
  rw [eta4_eq_exp_mul, eta4_eq_exp_mul, mul_pow, exp_pi_pow, coe_smulN]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hV0 := Vfn_ne_zero (smulN p τ)
  have he0 : cexp (π * I * ((p : ℂ) * τ)) ≠ 0 := Complex.exp_ne_zero _
  simp only [Vfn] at hV0 ⊢
  rw [coe_smulN] at hV0
  have h21 : ((2 : ℤ) - 1) = 1 := by norm_num
  have h41 : ((4 : ℤ) - 1) = 3 := by norm_num
  rw [h21, h41, zpow_one, show ((p : ℂ) ^ (3 : ℤ)) = (p : ℂ) ^ (3 : ℕ) by norm_cast]
  field_simp

/-- The function $G(w) = q^{(p^2-1)/2} V(pw)^p W(w)$ with $\nu_j(\tau) = 16^{p-1} p^2 G((\tau+j)/p)$. -/
private noncomputable def Gfn (p : ℕ) [NeZero p] : ℍ → ℂ :=
  (fun w : ℍ => Periodic.qParam 1 (w : ℂ) ^ (2 * (p / 2) * (p / 2 + 1))) *
    (fun w : ℍ => Vfn (smulN p w) ^ p) * Wfn

private lemma nuFam_some {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : 2 < p) (j : ZMod p) (τ : ℍ) :
    nuFam p (gmat p (some j)) τ = ((Cn p : ℂ) * (p : ℂ) ^ 2) * Gfn p (shiftH p j.val τ) := by
  obtain ⟨h, hh⟩ := hp.odd_of_ne_two (by omega)
  have hp2h : p / 2 = h := by omega
  have hdet : (gmat p (some j)).det ≠ 0 := by rw [gmat_det]; exact_mod_cast hp.ne_zero
  have hpos : 0 < (glZ (gmat p (some j))).det.val := glZ_det_pos hp (gmat_det p (some j))
  have hden : denom (glZ (gmat p (some j))) τ = p := by
    rw [denom_glZ hdet]; simp [gmat]
  have hdetv : ((glZ (gmat p (some j))).det.val : ℂ) = p := by
    rw [glZ_det hdet, gmat_det]; push_cast; rfl
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set w := shiftH p j.val τ with hw
  have hEw : (E2star ∣[(2 : ℤ)] glZ (gmat p (some j))) τ = E2star w / p := by
    rw [slash_apply_of_det_pos hpos, glZ_gmat_some_smul hp, hden, hdetv, ← hw]
    rw [show ((2 : ℤ) - 1) = 1 by norm_num, zpow_one,
      show ((p : ℂ) ^ (-(2 : ℤ))) = ((p : ℂ) ^ (2 : ℕ))⁻¹ by rw [zpow_neg]; norm_cast]
    field_simp
  have hηw : (eta4 ∣[(4 : ℤ)] glZ (gmat p (some j))) τ = eta4 w / p := by
    rw [slash_apply_of_det_pos hpos, glZ_gmat_some_smul hp, hden, hdetv, ← hw]
    rw [show ((4 : ℤ) - 1) = 3 by norm_num, show ((p : ℂ) ^ (3 : ℤ)) = (p : ℂ) ^ (3 : ℕ) by norm_cast,
      show ((p : ℂ) ^ (-(4 : ℤ))) = ((p : ℂ) ^ (4 : ℕ))⁻¹ by rw [zpow_neg]; norm_cast]
    field_simp
  have hτ : (τ : ℂ) = (p : ℂ) * w - j.val := by
    have := smulN_shiftH p j.val τ
    rw [coe_smulN, ← hw] at this
    linear_combination -this
  have hV1 : eta4_prod_fn (Periodic.qParam 1 (τ : ℂ)) = Vfn (smulN p w) :=
    (Vfn_add_int τ j.val (smulN p w) (by rw [hw, smulN_shiftH])).symm
  set a := cexp (π * I * w) with ha
  set sg : ℂ := (-1) ^ j.val with hsg
  have hsg2 : sg * sg = 1 := by
    rw [hsg, ← mul_pow, show (-1 : ℂ) * -1 = 1 by norm_num, one_pow]
  have hexpτ : cexp (π * I * τ) = a ^ p * sg := by
    rw [hτ, ha, hsg]
    have e : π * I * ((p : ℂ) * w - j.val) = (p : ℂ) * (π * I * w) + (j.val : ℂ) * (-(π * I)) := by
      ring
    rw [e, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_nat_mul, Complex.exp_neg,
      Complex.exp_pi_mul_I]
    norm_num
  have hsgp : sg ^ p = sg := by
    rw [hh, pow_succ, pow_mul, sq, hsg2, one_pow, one_mul]
  have hη : sg * eta4 τ ^ p = a ^ (p * p) * Vfn (smulN p w) ^ p := by
    rw [eta4_eq_exp_mul τ, hexpτ, hV1, mul_pow, mul_pow, hsgp, ← pow_mul]
    linear_combination (a ^ (p * p) * Vfn (smulN p w) ^ p) * hsg2
  have hq : Periodic.qParam 1 (w : ℂ) = a ^ 2 := by
    rw [qParam_one_eq_cexp, ha, exp_pi_pow]; congr 1; push_cast; ring
  have ha2 : a ^ (p * p) = (a ^ 2) ^ (2 * h * (h + 1)) * a := by
    rw [← pow_mul, ← pow_succ]; congr 1; rw [hh]; ring
  have hηw' : eta4 w = a * eta4_prod_fn (Periodic.qParam 1 (w : ℂ)) := eta4_eq_exp_mul w
  have hV0 : eta4_prod_fn (Periodic.qParam 1 (w : ℂ)) ≠ 0 := Vfn_ne_zero w
  have ha0 : a ≠ 0 := Complex.exp_ne_zero _
  simp only [nuFam, hEw, hηw, chiInt_gmat_some, Gfn, Pi.mul_apply, Wfn, Vinv, ← hsg]
  rw [show (Cn p : ℂ) * (p : ℂ) ^ 2 * sg * eta4 τ ^ p * (E2star w / p) / (eta4 w / p) =
    (Cn p : ℂ) * (p : ℂ) ^ 2 * (sg * eta4 τ ^ p) * (E2star w / p) / (eta4 w / p) by ring,
    hη, ha2, hηw', hq, hp2h]
  field_simp

end NuFamily

section NuIntegrality
open UpperHalfPlane hiding I
open Complex Filter Function ModularForm ModularGroup CongruenceSubgroup
open Matrix.SpecialLinearGroup
open scoped Real Topology Manifold MatrixGroups ModularForm

private lemma IsBoundedAtImInfty.comp_affH {f : ℍ → ℂ} (hf : IsBoundedAtImInfty f) (a : ℝ) (ha : 0 < a)
    (b : ℝ) : IsBoundedAtImInfty (fun τ => f (affH a ha b τ)) := by
  have ht : Tendsto (affH a ha b) atImInfty atImInfty := by
    refine tendsto_comap_iff.mpr ?_
    have h1 : Tendsto (fun τ : ℍ => a * τ.im) atImInfty atTop :=
      Tendsto.const_mul_atTop ha tendsto_comap
    refine h1.congr fun τ => ?_
    change a * τ.im = ((a : ℂ) * τ + b).im
    simp
  exact hf.comp_tendsto ht

/-- Coefficientwise divisibility of an integral `q`-expansion. -/
private def DivQ (d : ℤ) (f : ℍ → ℂ) : Prop :=
  ∃ F : PowerSeries ℤ, HasIntQ f F ∧ ∀ m, d ∣ F.coeff m

namespace DivQ

variable {d e : ℤ} {f g : ℍ → ℂ}

private lemma of_hasIntQ {F : PowerSeries ℤ} (hf : HasIntQ f F) : DivQ 1 f :=
  ⟨F, hf, fun _ => one_dvd _⟩

private lemma mul (hf : DivQ d f) (hg : DivQ e g) : DivQ (d * e) (f * g) := by
  obtain ⟨F, hF, hFd⟩ := hf
  obtain ⟨G, hG, hGd⟩ := hg
  refine ⟨F * G, hF.mul hG, fun m => ?_⟩
  rw [PowerSeries.coeff_mul]
  exact Finset.dvd_sum fun x _ => mul_dvd_mul (hFd _) (hGd _)

private lemma add (hf : DivQ d f) (hg : DivQ d g) : DivQ d (f + g) := by
  obtain ⟨F, hF, hFd⟩ := hf
  obtain ⟨G, hG, hGd⟩ := hg
  exact ⟨F + G, hF.add hG, fun m => by rw [map_add]; exact dvd_add (hFd m) (hGd m)⟩

private lemma zsmul (c : ℤ) (hf : DivQ d f) : DivQ (d * c) ((c : ℂ) • f) := by
  obtain ⟨F, hF, hFd⟩ := hf
  refine ⟨PowerSeries.C c * F, hF.zsmul c, fun m => ?_⟩
  rw [PowerSeries.coeff_C_mul, mul_comm d c]
  exact mul_dvd_mul_left c (hFd m)

private lemma zsmul' (c : ℤ) (hf : DivQ d f) : DivQ d ((c : ℂ) • f) := by
  obtain ⟨F, hF, hFd⟩ := hf
  exact ⟨PowerSeries.C c * F, hF.zsmul c, fun m => by
    rw [PowerSeries.coeff_C_mul]; exact (hFd m).mul_left c⟩

private lemma of_dvd (hde : d ∣ e) (hf : DivQ e f) : DivQ d f := by
  obtain ⟨F, hF, hFd⟩ := hf
  exact ⟨F, hF, fun m => hde.trans (hFd m)⟩

private lemma zero : DivQ d (0 : ℍ → ℂ) :=
  ⟨0, ⟨NiceQ.zero, by rw [qExpansion_zero, map_zero]⟩, fun m => by simp⟩

private lemma sum {ι : Type*} [DecidableEq ι] (s : Finset ι) {f : ι → ℍ → ℂ}
    (hf : ∀ i ∈ s, DivQ d (f i)) : DivQ d (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using (zero : DivQ d (0 : ℍ → ℂ))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma congr (hf : DivQ d f) (h : f = g) : DivQ d g := h ▸ hf

private lemma hasIntQ (hf : DivQ d f) : ∃ F, HasIntQ f F := ⟨hf.choose, hf.choose_spec.1⟩

end DivQ

variable {p : ℕ}

private noncomputable def Gps (p : ℕ) [NeZero p] : PowerSeries ℤ :=
  PowerSeries.X ^ (2 * (p / 2) * (p / 2 + 1)) *
    PowerSeries.expand p (NeZero.ne p) (eta4_prod_ps_int ^ p) * (E2star_ps_int * V_ps_inv)

private lemma hasIntQ_Gfn [NeZero p] : HasIntQ (Gfn p) (Gps p) := by
  have h1 := (hasIntQ_Vfn.pow p).comp_smulN p
  have h2 : (fun τ => (Vfn ^ p) (smulN p τ)) = fun τ => Vfn (smulN p τ) ^ p := rfl
  rw [h2] at h1
  exact ((HasIntQ.qParam_pow _).mul h1).mul hasIntQ_Wfn

private noncomputable def nuInfPs (p : ℕ) [NeZero p] : PowerSeries ℤ :=
  PowerSeries.C (Cn p) *
    (eta4_prod_ps_int ^ p * PowerSeries.expand p (NeZero.ne p) (E2star_ps_int * V_ps_inv))

private lemma hasIntQ_nuInf [NeZero p] (hp : p.Prime) : HasIntQ (nuFam p (gmat p none)) (nuInfPs p) := by
  rw [nuFam_none hp]
  exact ((hasIntQ_Vfn.pow p).mul (hasIntQ_Wfn.comp_smulN p)).zsmul (Cn p)

private lemma nuFam_some_fun [NeZero p] (hp : p.Prime) (hp2 : 2 < p) (j : ZMod p) :
    nuFam p (gmat p (some j)) =
      fun τ => ((Cn p : ℂ) * (p : ℂ) ^ 2) * Gfn p (shiftH p j.val τ) := by
  ext τ; exact nuFam_some hp hp2 j τ

private lemma nuFam_bdd [NeZero p] (hp : p.Prime) (hp2 : 2 < p) (m : Option (ZMod p)) :
    IsBoundedAtImInfty (nuFam p (gmat p m)) := by
  cases m with
  | none => exact (hasIntQ_nuInf hp).1.bdd
  | some j =>
    rw [nuFam_some_fun hp hp2]
    exact (Filter.const_boundedAtFilter _ _).mul
      (IsBoundedAtImInfty.comp_affH hasIntQ_Gfn.1.bdd _ _ _)

private lemma nuFam_mdiff' (hp : p.Prime) (m : Option (ZMod p)) : MDiff (nuFam p (gmat p m)) :=
  nuFam_mdiff hp (gmat_det p m)

/- #### Power sums and elementary symmetric functions of the finite branches -/

/-- The finite branches `ν_j`, `j ∈ ZMod p`. -/
private noncomputable def nuj (p : ℕ) (j : ZMod p) : ℍ → ℂ := nuFam p (gmat p (some j))

private noncomputable def esym (p : ℕ) [NeZero p] (r : ℕ) (τ : ℍ) : ℂ :=
  ∑ t ∈ Finset.powersetCard r (Finset.univ : Finset (ZMod p)), ∏ j ∈ t, nuj p j τ

private noncomputable def psm (p : ℕ) [NeZero p] (b : ℕ) (τ : ℍ) : ℂ :=
  ∑ j : ZMod p, nuj p j τ ^ b

private lemma sum_zmod_eq_sum_range (p : ℕ) [NeZero p] (F : ℕ → ℂ) :
    ∑ j : ZMod p, F j.val = ∑ j ∈ Finset.range p, F j := by
  refine Finset.sum_nbij (fun j => j.val) (fun j _ => Finset.mem_range.mpr (ZMod.val_lt j))
    (fun a _ b _ h => ZMod.val_injective p h) ?_ (fun _ _ => rfl)
  intro k hk
  refine ⟨(k : ZMod p), Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
  exact ZMod.val_cast_of_lt (Finset.mem_range.mp hk)

private lemma psm_eq [NeZero p] (hp : p.Prime) (hp2 : 2 < p) (b : ℕ) :
    psm p b = (((Cn p * (p : ℤ) ^ 2) ^ b : ℤ) : ℂ) • shiftSum p (Gfn p ^ b) := by
  ext τ
  simp only [psm, nuj, nuFam_some hp hp2, Pi.smul_apply, smul_eq_mul, shiftSum, Pi.pow_apply]
  rw [Finset.mul_sum, ← sum_zmod_eq_sum_range p (fun j => (((Cn p * (p : ℤ) ^ 2) ^ b : ℤ) : ℂ) *
    Gfn p (shiftH p j τ) ^ b)]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

private lemma psm_divQ [NeZero p] (hp : p.Prime) (hp2 : 2 < p) (b : ℕ) :
    DivQ ((p : ℤ) ^ (2 * b + 1)) (psm p b) := by
  rw [psm_eq hp hp2]
  have h := (hasIntQ_Gfn (p := p)).pow b
  have h2 := h.shift_sum p hp
  refine ⟨_, h2.zsmul _, fun m => ?_⟩
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, mul_pow, ← pow_mul, pow_succ]
  exact mul_dvd_mul (dvd_mul_left _ _) (dvd_mul_right _ _)

private lemma esym_zero [NeZero p] : esym p 0 = 1 := by
  ext τ; simp [esym]

private lemma esym_eq_zero [NeZero p] {r : ℕ} (hr : p < r) : esym p r = 0 := by
  ext τ
  simp only [esym, Pi.zero_apply]
  rw [Finset.powersetCard_eq_empty.mpr (by rw [Finset.card_univ, ZMod.card]; exact hr),
    Finset.sum_empty]

/-- Newton's identity for the finite branches. -/
private lemma esym_newton [NeZero p] (r : ℕ) (τ : ℍ) :
    (r : ℂ) * esym p r τ = (-1) ^ (r + 1) * ∑ a ∈ Finset.HasAntidiagonal.antidiagonal r with a.1 < r,
      (-1) ^ a.1 * esym p a.1 τ * psm p a.2 τ := by
  have h := congrArg (MvPolynomial.aeval (R := ℂ) (fun j : ZMod p => nuj p j τ))
    (MvPolynomial.mul_esymm_eq_sum (ZMod p) ℂ r)
  simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, Finset.esymm_map_val, MvPolynomial.psum,
    MvPolynomial.aeval_X] at h
  exact h

private lemma esym_divQ [NeZero p] (hp : p.Prime) (hp2 : 2 < p) (r : ℕ) (hr : 1 ≤ r) :
    DivQ ((p : ℤ) ^ (2 * r + 1)) (((r.factorial : ℤ) : ℂ) • esym p r) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have hfun : ((((r' + 1).factorial : ℤ) : ℂ) • esym p (r' + 1)) =
        ∑ a ∈ Finset.HasAntidiagonal.antidiagonal (r' + 1) with a.1 < r' + 1,
          ((((-1) ^ (r' + 1 + 1) * (-1) ^ a.1 * (r'.descFactorial (r' - a.1) : ℤ)) : ℤ) : ℂ) •
            ((((a.1.factorial : ℤ) : ℂ) • esym p a.1) * psm p a.2) := by
      ext τ
      simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.mul_apply]
      rw [Nat.factorial_succ, Nat.cast_mul, Int.cast_mul, mul_assoc]
      have hN := esym_newton (p := p) (r' + 1) τ
      push_cast at hN ⊢
      rw [mul_left_comm, hN, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      have ha1 : a.1 < r' + 1 := (Finset.mem_filter.mp ha).2
      have hfac : (r'.factorial : ℂ) = (a.1.factorial : ℂ) * (r'.descFactorial (r' - a.1) : ℂ) := by
        have := Nat.factorial_mul_descFactorial (n := r') (k := r' - a.1) (by omega)
        rw [show r' - (r' - a.1) = a.1 by omega] at this
        exact_mod_cast this.symm
      rw [hfac]
      ring
    rw [hfun]
    refine DivQ.sum _ fun a ha => ?_
    have ha1 : a.1 < r' + 1 := (Finset.mem_filter.mp ha).2
    have hsum : a.1 + a.2 = r' + 1 := Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_filter.mp ha).1
    refine DivQ.zsmul' _ ?_
    rcases Nat.eq_zero_or_pos a.1 with h0 | hpos
    · have hP := psm_divQ hp hp2 a.2
      have hb : a.2 = r' + 1 := by omega
      rw [hb] at hP
      have h1 : DivQ 1 (((a.1.factorial : ℤ) : ℂ) • esym p a.1) := by
        rw [h0, esym_zero]
        exact DivQ.of_hasIntQ (HasIntQ.one.zsmul _)
      have := h1.mul hP
      rw [hb]; rwa [one_mul] at this
    · have hE := ih a.1 ha1 hpos
      have hP := psm_divQ hp hp2 a.2
      refine (hE.mul hP).of_dvd ?_
      rw [← pow_add]
      exact pow_dvd_pow _ (by omega)

/-- `(p-1)! e_r` has all coefficients divisible by `p²` for `1 ≤ r`. -/
private lemma esym_divQ_sq [NeZero p] (hp : p.Prime) (hp2 : 2 < p) (r : ℕ) (hr : 1 ≤ r) :
    DivQ ((p : ℤ) ^ 2) ((((p - 1).factorial : ℤ) : ℂ) • esym p r) := by
  rcases lt_trichotomy r p with hrp | hrp | hrp
  · have hE := esym_divQ hp hp2 r hr
    have hfac : ((p - 1).factorial : ℤ) = (r.factorial : ℤ) * ((p - 1).descFactorial (p - 1 - r) : ℤ) := by
      have := Nat.factorial_mul_descFactorial (n := p - 1) (k := p - 1 - r) (by omega)
      rw [show p - 1 - (p - 1 - r) = r by omega] at this
      exact_mod_cast this.symm
    have h2 : (((p - 1).factorial : ℤ) : ℂ) • esym p r =
        ((((p - 1).descFactorial (p - 1 - r) : ℤ)) : ℂ) • ((((r.factorial : ℤ)) : ℂ) • esym p r) := by
      rw [hfac, smul_smul]; push_cast; ring_nf
    rw [h2]
    exact (hE.zsmul' _).of_dvd (pow_dvd_pow _ (by omega))
  · obtain ⟨F, hF, hFd⟩ := esym_divQ hp hp2 r hr
    have hpF (m : ℕ) : (p : ℤ) ∣ F.coeff m := (dvd_pow_self _ (by omega)).trans (hFd m)
    let G : PowerSeries ℤ := PowerSeries.mk fun m => F.coeff m / p
    have hFG : F = PowerSeries.C (p : ℤ) * G := by
      ext m
      simp only [G, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
      exact (Int.mul_ediv_cancel' (hpF m)).symm
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hfr : ((r.factorial : ℤ) : ℂ) = (p : ℂ) * (((p - 1).factorial : ℤ) : ℂ) := by
      rw [hrp, ← Nat.mul_factorial_pred hp.ne_zero]; push_cast; ring
    have h2 : (((p - 1).factorial : ℤ) : ℂ) • esym p r =
        (p : ℂ)⁻¹ • ((((r.factorial : ℤ)) : ℂ) • esym p r) := by
      rw [hfr, smul_smul, ← mul_assoc, inv_mul_cancel₀ hp0, one_mul]
    have hN : NiceQ ((((p - 1).factorial : ℤ) : ℂ) • esym p r) := by
      rw [h2]; exact hF.1.smul _
    refine ⟨G, ⟨hN, ?_⟩, fun m => ?_⟩
    · rw [h2, NiceQ.qExp_smul _ hF.1, hF.2, hFG, map_mul, PowerSeries.map_C, ← mul_assoc,
        ← map_mul]
      simp [hp0]
    · simp only [G, PowerSeries.coeff_mk]
      have h3 : (p : ℤ) ^ (2 * r + 1) = (p : ℤ) * (p : ℤ) ^ (2 * r) := by ring
      obtain ⟨y, hy⟩ := hFd m
      rw [hy, h3, mul_assoc, Int.mul_ediv_cancel_left _ (by exact_mod_cast hp.ne_zero)]
      exact (pow_dvd_pow _ (by omega)).mul_right _
  · rw [esym_eq_zero hrp, smul_zero]; exact DivQ.zero

private lemma multiset_esymm_cons {R : Type*} [CommRing R] (a : R) (s : Multiset R) (k : ℕ) :
    (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_def, Multiset.prod_cons, Multiset.sum_map_mul_left]

private lemma Ssym_nu_succ [NeZero p] (k : ℕ) (τ : ℍ) :
    Ssym p (nuFam p) (k + 1) τ = esym p (k + 1) τ + nuFam p (gmat p none) τ * esym p k τ := by
  have hu : (Finset.univ : Finset (Option (ZMod p))).val =
      none ::ₘ (Finset.univ : Finset (ZMod p)).val.map some := by
    rw [univ_option]; rfl
  simp only [Ssym, esym, nuj, ← Finset.esymm_map_val, hu, Multiset.map_cons, Multiset.map_map,
    Function.comp_def]
  exact multiset_esymm_cons _ _ k

end NuIntegrality

section NuStructure
open UpperHalfPlane hiding I
open Complex Filter Function ModularForm ModularGroup CongruenceSubgroup
open Matrix.SpecialLinearGroup
open scoped Real Topology Manifold MatrixGroups ModularForm

variable {p : ℕ}

private lemma coeff_mul_expand_lt {R : Type*} [CommRing R] (p : ℕ) (hp : p ≠ 0) (A G : PowerSeries R)
    {m : ℕ} (hm : m < p) :
    (A * PowerSeries.expand p hp G).coeff m = (A * PowerSeries.C (G.coeff 0)).coeff m := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  congr 1
  rcases Nat.eq_zero_or_pos x.2 with h0 | hpos
  · rw [h0, PowerSeries.coeff_C, if_pos rfl, PowerSeries.coeff_expand, if_pos (dvd_zero p),
      Nat.zero_div]
  · rw [PowerSeries.coeff_C, if_neg hpos.ne', PowerSeries.coeff_expand_of_not_dvd p hp G]
    intro hd
    have := Nat.le_of_dvd hpos hd
    omega

private lemma triangular_zero {R : Type*} [CommRing R] (W : PowerSeries R) (hW : W.coeff 0 = 1)
    (n : ℕ) (a : ℕ → R)
    (h : ∀ m < n,
      (∑ j ∈ Finset.range n, PowerSeries.C (a j) * (PowerSeries.X * W) ^ j).coeff m = 0) :
    ∀ m < n, a m = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    have h1 := h m hm
    rw [map_sum, Finset.sum_eq_single m] at h1
    · rw [PowerSeries.coeff_C_mul, mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl,
        Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hW, one_pow, mul_one] at h1
      exact h1
    · intro j _ hjm
      rcases lt_or_gt_of_ne hjm with hlt | hgt
      · rw [ih j hlt (by omega), map_zero, zero_mul, map_zero]
      · rw [PowerSeries.coeff_C_mul, mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega),
          mul_zero]
    · intro hm'
      exact absurd (Finset.mem_range.mpr hm) hm'

private lemma Ssym_nu_one_hasIntQ [NeZero p] (hp : p.Prime) (hp2 : 2 < p) :
    ∃ F : PowerSeries ℤ, HasIntQ (Ssym p (nuFam p) 1) (nuInfPs p + F) ∧
      ∀ m, (p : ℤ) ^ 3 ∣ F.coeff m := by
  obtain ⟨F, hF, hFd⟩ := esym_divQ hp hp2 1 le_rfl
  have hfun : Ssym p (nuFam p) 1 = nuFam p (gmat p none) +
      (((Nat.factorial 1 : ℤ)) : ℂ) • esym p 1 := by
    ext τ
    rw [Ssym_nu_succ 0 τ, esym_zero]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, Nat.factorial_one,
      Nat.cast_one, Int.cast_one, one_mul, mul_one]
    ring
  exact ⟨F, ((hasIntQ_nuInf hp).add hF).congr_fun hfun.symm, hFd⟩

private lemma divQ_Ssym_nu [NeZero p] (hp : p.Prime) (hp2 : 2 < p) (k : ℕ) (hk : 2 ≤ k) :
    DivQ ((p : ℤ) ^ 2) ((((p - 1).factorial : ℤ) : ℂ) • Ssym p (nuFam p) k) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hfun : (((p - 1).factorial : ℤ) : ℂ) • Ssym p (nuFam p) (k' + 1) =
      (((p - 1).factorial : ℤ) : ℂ) • esym p (k' + 1) +
        nuFam p (gmat p none) * ((((p - 1).factorial : ℤ) : ℂ) • esym p k') := by
    ext τ
    simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Ssym_nu_succ]
    ring
  rw [hfun]
  refine (esym_divQ_sq hp hp2 _ (by omega)).add ?_
  have := (DivQ.of_hasIntQ (hasIntQ_nuInf hp)).mul (esym_divQ_sq hp hp2 k' (by omega))
  rwa [one_mul] at this

/-- Structure of $(p-1)!\,S_k$ for $k \ge 2$: all coefficients divisible by $p^2$. -/
private lemma nu_Sk_structure [NeZero p] (hp : p.Prime) (hp2 : 2 < p) (k : ℕ) (hk : 2 ≤ k) :
    ∃ c : ℕ → ℤ, ∀ τ : ℍ, (((p - 1).factorial : ℤ) : ℂ) * Ssym p (nuFam p) k τ =
      ∑ j ∈ Finset.range (k * (2 * p - 1) / 4 + 1),
        ((((p : ℤ) ^ 2 : ℤ) : ℂ) * (c j : ℂ)) * Delta8 τ ^ j *
          E2star τ ^ (k * (2 * p - 1) - 4 * j) := by
  let f : ModularForm Γ02 (2 * ((k * (2 * p - 1) : ℕ) : ℤ)) :=
    (((p - 1).factorial : ℤ) : ℂ) • SsymMF (nuFam_isBranchFamily hp hp2) hp hp2
      (nuFam_mdiff' hp) (nuFam_bdd hp hp2) k
  have hf : (f : ℍ → ℂ) = (((p - 1).factorial : ℤ) : ℂ) • Ssym p (nuFam p) k := rfl
  obtain ⟨F, hF, hFd⟩ := divQ_Ssym_nu hp hp2 k hk
  have hW : (f : ℍ → ℂ) ∣[2 * ((k * (2 * p - 1) : ℕ) : ℤ)] W2 =
      ((-1 : ℂ) ^ (k * (2 * p - 1))) • (f : ℍ → ℂ) := by
    rw [hf, smul_slash_of_det_pos (by rw [W2_det_val]; exact one_pos),
      (nuFam_isBranchFamily hp hp2).Ssym_slash_W2 hp hp2, smul_comm]
  obtain ⟨c, hc⟩ := structure_Gamma02_dvd (k * (2 * p - 1)) ((p : ℤ) ^ 2) f hW (fun m => by
    obtain ⟨a, ha⟩ := hFd m
    refine ⟨a, ?_⟩
    rw [hf, hF.2, PowerSeries.coeff_map, ha]
    simp)
  refine ⟨c, fun τ => ?_⟩
  rw [← hc τ]
  rfl

private lemma Ssym_nu_one_structure [NeZero p] (hp : p.Prime) (hp2 : 2 < p) {h : ℕ}
    (hh : p = 2 * h + 1) :
    ∃ c : ℕ → ℤ, ∀ τ : ℍ, Ssym p (nuFam p) 1 τ =
      ∑ j ∈ Finset.range (h + 1), (c j : ℂ) * Delta8 τ ^ j * E2star τ ^ (2 * p - 1 - 4 * j) := by
  obtain ⟨F, hF, -⟩ := Ssym_nu_one_hasIntQ hp hp2
  let f : ModularForm Γ02 (2 * ((1 * (2 * p - 1) : ℕ) : ℤ)) :=
    SsymMF (nuFam_isBranchFamily hp hp2) hp hp2 (nuFam_mdiff' hp) (nuFam_bdd hp hp2) 1
  have hf : (f : ℍ → ℂ) = Ssym p (nuFam p) 1 := rfl
  have hW : (f : ℍ → ℂ) ∣[2 * ((1 * (2 * p - 1) : ℕ) : ℤ)] W2 =
      ((-1 : ℂ) ^ (1 * (2 * p - 1))) • (f : ℍ → ℂ) :=
    (nuFam_isBranchFamily hp hp2).Ssym_slash_W2 hp hp2 1
  obtain ⟨c, hc⟩ := structure_Gamma02_dvd (1 * (2 * p - 1)) 1 f hW (fun m => by
    refine ⟨(nuInfPs p + F).coeff m, ?_⟩
    rw [hf, hF.2, PowerSeries.coeff_map]
    simp)
  refine ⟨c, fun τ => ?_⟩
  have h4 : 1 * (2 * p - 1) / 4 = h := by omega
  rw [← hf, hc τ, h4]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Int.cast_one, one_mul]

/-- The first symmetric function: its structure coefficients are $c_j \cdot 256^j$ mod $p^2$. -/
private theorem Ssym_nu_one_coeffs [NeZero p] (hp : p.Prime) (hp2 : 2 < p) {h : ℕ}
    (hh : p = 2 * h + 1) :
    ∃ c : ℕ → ℤ, (∀ τ : ℍ, Ssym p (nuFam p) 1 τ =
      ∑ j ∈ Finset.range (h + 1), (c j : ℂ) * Delta8 τ ^ j * E2star τ ^ (2 * p - 1 - 4 * j)) ∧
      ∀ j ≤ h, (c j : R2 p) = atCoeff p h j * 256 ^ j := by
  obtain ⟨F, hF, hFd⟩ := Ssym_nu_one_hasIntQ hp hp2
  obtain ⟨c, hc⟩ := Ssym_nu_one_structure hp hp2 hh
  refine ⟨c, hc, ?_⟩
  set N := 2 * p - 1 with hN
  -- the integer power series identity
  let G : PowerSeries ℤ := ∑ j ∈ Finset.range (h + 1),
    PowerSeries.C (c j) * (Delta8_ps_int ^ j * E2star_ps_int ^ (N - 4 * j))
  have hG : HasIntQ (Ssym p (nuFam p) 1) G := by
    have h1 : HasIntQ (∑ j ∈ Finset.range (h + 1),
        ((c j : ℂ) • (Delta8 ^ j * E2star ^ (N - 4 * j)))) G :=
      HasIntQ.sum _ fun j _ => ((hasIntQ_Delta8.pow j).mul (hasIntQ_E2star.pow _)).zsmul (c j)
    refine h1.congr_fun ?_
    ext τ
    rw [hc τ, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul]
    ring
  have hFG : nuInfPs p + F = G := hF.unique hG
  let Q : PowerSeries ℤ := ∑ j ∈ Finset.range (h + 1), PowerSeries.C (c j) * u0_ps_int ^ j
  have hGQ : G = E2star_ps_int ^ N * Q := by
    simp only [G, Q, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : 4 * j ≤ N := by simp only [Finset.mem_range] at hj; omega
    rw [← u0_mul_E2star_pow_four, mul_pow, ← pow_mul]
    have hsplit : E2star_ps_int ^ N = E2star_ps_int ^ (4 * j) * E2star_ps_int ^ (N - 4 * j) := by
      rw [← pow_add, Nat.add_sub_cancel' hj']
    rw [hsplit]
    ring
  have hEinv : E2star_ps_int ^ N * E2star_ps_int_inv ^ N = 1 := by
    rw [← mul_pow, E2star_ps_int_mul_inv, one_pow]
  have hQ : Q = (nuInfPs p + F) * E2star_ps_int_inv ^ N := by
    rw [hFG, hGQ]
    linear_combination Q * hEinv.symm
  -- the main term
  have hmain : ∀ m < p, (nuInfPs p * E2star_ps_int_inv ^ N).coeff m =
      (PowerSeries.C (Cn p) * U_ps_int ^ p * E2star_ps_int).coeff m := by
    intro m hm
    have h1 : nuInfPs p * E2star_ps_int_inv ^ N =
        (PowerSeries.C (Cn p) * eta4_prod_ps_int ^ p * E2star_ps_int_inv ^ N) *
          PowerSeries.expand p (NeZero.ne p) (E2star_ps_int * V_ps_inv) := by
      simp only [nuInfPs]; ring
    have h0 : (E2star_ps_int * V_ps_inv).coeff 0 = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, E2star_ps_int_coeff_zero,
        V_ps_inv_coeff_zero, one_mul]
    rw [h1, coeff_mul_expand_lt p (NeZero.ne p) _ _ hm, h0, map_one, mul_one]
    congr 1
    have hNp : 2 * p = N + 1 := by omega
    have hEE : E2star_ps_int * E2star_ps_int_inv = 1 := E2star_ps_int_mul_inv
    simp only [U_ps_int]
    rw [mul_pow, ← pow_mul, hNp, pow_succ]
    linear_combination (PowerSeries.C (Cn p) * eta4_prod_ps_int ^ p * E2star_ps_int_inv ^ N) *
      hEE.symm
  -- reduce modulo p^2
  let φ : ℤ →+* R2 p := Int.castRingHom (R2 p)
  have hp2dvd : ∀ m, (p : ℤ) ^ 2 ∣ (F * E2star_ps_int_inv ^ N).coeff m := by
    intro m
    rw [PowerSeries.coeff_mul]
    exact Finset.dvd_sum fun x _ =>
      ((pow_dvd_pow (p : ℤ) (by norm_num : 2 ≤ 3)).trans (hFd x.1)).mul_right _
  have hcong : ∀ m < p, φ (Q.coeff m) = φ ((PowerSeries.C (Cn p) * U_ps_int ^ p *
      E2star_ps_int).coeff m) := by
    intro m hm
    rw [hQ, add_mul, map_add, hmain m hm, map_add]
    have hz : φ ((F * E2star_ps_int_inv ^ N).coeff m) = 0 := by
      have := hp2dvd m
      simp only [φ, eq_intCast]
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast this
    rw [hz, add_zero]
  have hPF := picard_fuchs_congruence_mod_p_sq hp hp2 hh
  simp only at hPF
  -- the difference series
  let W : PowerSeries (R2 p) := (U_ps_int.map φ) ^ 2
  have hW0 : W.coeff 0 = 1 := by
    simp only [W, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      U_ps_int_coeff_zero, map_one, one_pow]
  have hu0 : u0_ps_int.map φ = PowerSeries.X * W := by
    simp only [u0_ps_int, W, map_mul, map_pow, PowerSeries.map_X]
  let a : ℕ → R2 p := fun j => φ (c j) - atCoeff p h j * 256 ^ j
  have hdiff : ∀ m < h + 1,
      (∑ j ∈ Finset.range (h + 1), PowerSeries.C (a j) * (PowerSeries.X * W) ^ j).coeff m = 0 := by
    intro m hm
    have hmp : m < p := by omega
    have e1 : (Q.map φ).coeff m = (PowerSeries.C ((16 : R2 p) ^ (p - 1)) *
        (U_ps_int.map φ) ^ p * E2star_ps_int.map φ).coeff m := by
      rw [PowerSeries.coeff_map, hcong m hmp, ← PowerSeries.coeff_map]
      congr 1
      simp only [map_mul, map_pow, Cn, φ, map_ofNat]
    rw [hPF m hmp] at e1
    have e2 : Q.map φ = ∑ j ∈ Finset.range (h + 1),
        PowerSeries.C (φ (c j)) * (PowerSeries.X * W) ^ j := by
      simp only [Q, map_sum, map_mul, map_pow, PowerSeries.map_C, hu0]
    rw [e2] at e1
    have e3 : (∑ j ∈ Finset.range (h + 1), PowerSeries.C (a j) * (PowerSeries.X * W) ^ j) =
        (∑ j ∈ Finset.range (h + 1), PowerSeries.C (φ (c j)) * (PowerSeries.X * W) ^ j) -
        ∑ j ∈ Finset.range (h + 1), PowerSeries.C (atCoeff p h j) *
          (PowerSeries.C (256 : R2 p) * u0_ps_int.map φ) ^ j := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [a, hu0, map_sub, map_mul, map_pow, mul_pow]
      ring
    rw [e3, map_sub, e1, sub_self]
  intro j hj
  have := triangular_zero W hW0 (h + 1) a hdiff j (by omega)
  simp only [a, φ, eq_intCast] at this
  exact sub_eq_zero.mp this

end NuStructure

section HeckeE2
open UpperHalfPlane hiding I
open Complex Filter Function ModularForm ModularGroup CongruenceSubgroup
open Matrix.SpecialLinearGroup
open scoped Real Topology Manifold MatrixGroups ModularForm

variable {p : ℕ}

/-- Power sums of all `p + 1` branches. -/
private noncomputable def Psum (p : ℕ) [NeZero p] (Φ : Matrix (Fin 2) (Fin 2) ℤ → ℍ → ℂ) (b : ℕ)
    (τ : ℍ) : ℂ :=
  ∑ m : Option (ZMod p), Φ (gmat p m) τ ^ b

private lemma Ssym_zero [NeZero p] (Φ : Matrix (Fin 2) (Fin 2) ℤ → ℍ → ℂ) : Ssym p Φ 0 = 1 := by
  ext τ; simp [Ssym]

private lemma Ssym_newton [NeZero p] (Φ : Matrix (Fin 2) (Fin 2) ℤ → ℍ → ℂ) (r : ℕ) (τ : ℍ) :
    (r : ℂ) * Ssym p Φ r τ = (-1) ^ (r + 1) *
      ∑ a ∈ Finset.HasAntidiagonal.antidiagonal r with a.1 < r,
        (-1) ^ a.1 * Ssym p Φ a.1 τ * Psum p Φ a.2 τ := by
  have h := congrArg (MvPolynomial.aeval (R := ℂ) (fun m : Option (ZMod p) => Φ (gmat p m) τ))
    (MvPolynomial.mul_esymm_eq_sum (Option (ZMod p)) ℂ r)
  simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, Finset.esymm_map_val, MvPolynomial.psum,
    MvPolynomial.aeval_X] at h
  exact h

private lemma Ssym_divQ_one [NeZero p] (Φ : Matrix (Fin 2) (Fin 2) ℤ → ℍ → ℂ)
    (hP : ∀ b, 1 ≤ b → DivQ 1 (Psum p Φ b)) (r : ℕ) :
    DivQ 1 (((r.factorial : ℤ) : ℂ) • Ssym p Φ r) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    rcases Nat.eq_zero_or_pos r with h0 | hr
    · subst h0
      rw [Ssym_zero]
      exact DivQ.of_hasIntQ (HasIntQ.one.zsmul _)
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have hfun : ((((r' + 1).factorial : ℤ) : ℂ) • Ssym p Φ (r' + 1)) =
        ∑ a ∈ Finset.HasAntidiagonal.antidiagonal (r' + 1) with a.1 < r' + 1,
          ((((-1) ^ (r' + 1 + 1) * (-1) ^ a.1 * (r'.descFactorial (r' - a.1) : ℤ)) : ℤ) : ℂ) •
            ((((a.1.factorial : ℤ) : ℂ) • Ssym p Φ a.1) * Psum p Φ a.2) := by
      ext τ
      simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.mul_apply]
      rw [Nat.factorial_succ, Nat.cast_mul, Int.cast_mul, mul_assoc]
      have hN := Ssym_newton (p := p) Φ (r' + 1) τ
      push_cast at hN ⊢
      rw [mul_left_comm, hN, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      have ha1 : a.1 < r' + 1 := (Finset.mem_filter.mp ha).2
      have hfac : (r'.factorial : ℂ) =
          (a.1.factorial : ℂ) * (r'.descFactorial (r' - a.1) : ℂ) := by
        have := Nat.factorial_mul_descFactorial (n := r') (k := r' - a.1) (by omega)
        rw [show r' - (r' - a.1) = a.1 by omega] at this
        exact_mod_cast this.symm
      rw [hfac]
      ring
    rw [hfun]
    refine DivQ.sum _ fun a ha => ?_
    have ha1 : a.1 < r' + 1 := (Finset.mem_filter.mp ha).2
    have hsum : a.1 + a.2 = r' + 1 :=
      Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_filter.mp ha).1
    refine DivQ.zsmul' _ ?_
    have := (ih a.1 ha1).mul (hP a.2 (by omega))
    rwa [one_mul] at this

/-- The branches $b_M = p\,(E_2^*|_2 M)$. -/
private noncomputable def bFam (p : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) (τ : ℍ) : ℂ :=
  (p : ℂ) * (E2star ∣[(2 : ℤ)] glZ M) τ

private lemma bFam_isBranchFamily (hp : p.Prime) : IsBranchFamily p 1 (bFam p) := by
  have h21 : (2 : ℤ) * ((1 : ℕ) : ℤ) = 2 := by norm_num
  refine ⟨?_, ?_, ?_⟩
  · intro σ hσ M hM _
    have hM0 : M.det ≠ 0 := by rw [hM]; exact_mod_cast hp.ne_zero
    ext τ
    simp only [bFam]
    rw [E2star_slash_glZ_left hσ hM0]
  · intro σ _ M hM _ τ
    have hM0 : M.det ≠ 0 := by rw [hM]; exact_mod_cast hp.ne_zero
    have hσ0 : (σ : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by rw [σ.2]; exact one_ne_zero
    have hglZ : glZ (M * (σ : Matrix (Fin 2) (Fin 2) ℤ)) = glZ M * mapGL ℝ σ := by
      rw [glZ_mul hM0 hσ0, ← mapGL_eq_glZ]
    have hE := slash_comp_apply (k := 2) (glZ M) (mapGL ℝ σ) (mapGL_det σ) E2star τ
    rw [← hglZ] at hE
    simp only [bFam]
    rw [hE, h21]
    ring
  · intro M hM hc τ
    have hM0 : M.det ≠ 0 := by rw [hM]; exact_mod_cast hp.ne_zero
    have hglZ : glZ M * W2 = W2 * glZ (conjW M) := glZ_mul_W2 hM0 hc
    have hE := slash_comp_apply (k := 2) (glZ M) W2 W2_det_val E2star τ
    rw [hglZ, SlashAction.slash_mul, E2star_slash_W2, SlashAction.neg_slash] at hE
    simp only [bFam]
    rw [hE, Pi.neg_apply, h21]
    ring

private lemma bFam_mdiff (m : Option (ZMod p)) : MDiff (bFam p (gmat p m)) :=
  mdifferentiable_const.mul (E2star_mdiff.slash 2 (glZ (gmat p m)))

private lemma bFam_none [NeZero p] (hp : p.Prime) (τ : ℍ) :
    bFam p (gmat p none) τ = (p : ℂ) ^ 2 * E2star (smulN p τ) := by
  have hdet : (gmat p none).det ≠ 0 := by rw [gmat_det]; exact_mod_cast hp.ne_zero
  have hpos : 0 < (glZ (gmat p none)).det.val := glZ_det_pos hp (gmat_det p none)
  have hden : denom (glZ (gmat p none)) τ = 1 := by
    rw [denom_glZ hdet]; simp [gmat]
  have hdetv : ((glZ (gmat p none)).det.val : ℂ) = p := by
    rw [glZ_det hdet, gmat_det]; push_cast; rfl
  simp only [bFam]
  rw [slash_apply_of_det_pos hpos, glZ_gmat_none_smul hp, hden, hdetv,
    show ((2 : ℤ) - 1) = 1 by norm_num, zpow_one, one_zpow]
  ring

private lemma bFam_some [NeZero p] (hp : p.Prime) (j : ZMod p) (τ : ℍ) :
    bFam p (gmat p (some j)) τ = E2star (shiftH p j.val τ) := by
  have hdet : (gmat p (some j)).det ≠ 0 := by rw [gmat_det]; exact_mod_cast hp.ne_zero
  have hpos : 0 < (glZ (gmat p (some j))).det.val := glZ_det_pos hp (gmat_det p (some j))
  have hden : denom (glZ (gmat p (some j))) τ = p := by
    rw [denom_glZ hdet]; simp [gmat]
  have hdetv : ((glZ (gmat p (some j))).det.val : ℂ) = p := by
    rw [glZ_det hdet, gmat_det]; push_cast; rfl
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  simp only [bFam]
  rw [slash_apply_of_det_pos hpos, glZ_gmat_some_smul hp, hden, hdetv,
    show ((2 : ℤ) - 1) = 1 by norm_num, zpow_one,
    show ((p : ℂ) ^ (-(2 : ℤ))) = ((p : ℂ) ^ (2 : ℕ))⁻¹ by rw [zpow_neg]; norm_cast]
  field_simp

private lemma bFam_bdd [NeZero p] (hp : p.Prime) (m : Option (ZMod p)) :
    IsBoundedAtImInfty (bFam p (gmat p m)) := by
  cases m with
  | none =>
    have h := ((hasIntQ_E2star.comp_smulN p).zsmul ((p : ℤ) ^ 2)).1.bdd
    convert h using 1
    ext τ
    simp only [Pi.smul_apply, smul_eq_mul, bFam_none hp]
    push_cast; ring
  | some j =>
    have h := IsBoundedAtImInfty.comp_affH isBoundedAtImInfty_E2star (1 / p) (by
      have : (0 : ℝ) < p := by exact_mod_cast hp.pos
      positivity) (j.val / p)
    convert h using 1
    ext τ
    rw [bFam_some hp]
    rfl

/-- The integer `q`-series of the power sums of the `b`-branches. -/
private noncomputable def PPs (p : ℕ) [NeZero p] (b : ℕ) : PowerSeries ℤ :=
  PowerSeries.C (((p : ℤ) ^ 2) ^ b) * PowerSeries.expand p (NeZero.ne p) (E2star_ps_int ^ b) +
    PowerSeries.mk fun m => (p : ℤ) * (E2star_ps_int ^ b).coeff (p * m)

private lemma hasIntQ_Psum_bFam [NeZero p] (hp : p.Prime) (b : ℕ) :
    HasIntQ (Psum p (bFam p) b) (PPs p b) := by
  have h1 := (((hasIntQ_E2star.pow b).comp_smulN p).zsmul (((p : ℤ) ^ 2) ^ b))
  have h2 := (hasIntQ_E2star.pow b).shift_sum p hp
  refine (h1.add h2).congr_fun ?_
  ext τ
  simp only [Psum, Fintype.sum_option, bFam_none hp, bFam_some hp, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Pi.pow_apply, shiftSum]
  rw [sum_zmod_eq_sum_range p (fun j => E2star (shiftH p j τ) ^ b)]
  push_cast
  ring

private lemma E2star_pow_coeff_zero (b : ℕ) : (E2star_ps_int ^ b).coeff 0 = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, E2star_ps_int_coeff_zero, one_pow]

private lemma PPs_coeff_zero [NeZero p] (b : ℕ) : (PPs p b).coeff 0 = ((p : ℤ) ^ 2) ^ b + p := by
  simp only [PPs, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, mul_zero]
  rw [PowerSeries.coeff_expand, if_pos (dvd_zero p), Nat.zero_div, E2star_pow_coeff_zero]
  ring

private lemma PPs_coeff_one [NeZero p] (hp1 : 1 < p) (b : ℕ) :
    (PPs p b).coeff 1 = p * (E2star_ps_int ^ b).coeff p := by
  simp only [PPs, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, mul_one]
  rw [PowerSeries.coeff_expand_of_not_dvd p _ _ (by
    intro h; have := Nat.le_of_dvd one_pos h; omega)]
  ring

private lemma coeff_mul_E2star (A : PowerSeries ℤ) :
    (A * E2star_ps_int).coeff 1 = A.coeff 0 * 24 + A.coeff 1 ∧
    (A * E2star_ps_int).coeff 2 = A.coeff 0 * 24 + A.coeff 1 * 24 + A.coeff 2 ∧
    (A * E2star_ps_int).coeff 3 =
      A.coeff 0 * 96 + A.coeff 1 * 24 + A.coeff 2 * 24 + A.coeff 3 := by
  have h0 : E2star_ps_int.coeff 0 = 1 := E2star_ps_int_coeff_zero
  have h1 : E2star_ps_int.coeff 1 = 24 := by
    simp only [E2star_ps_int, PowerSeries.coeff_mk]; decide
  have h2 : E2star_ps_int.coeff 2 = 24 := by
    simp only [E2star_ps_int, PowerSeries.coeff_mk]; decide
  have h3 : E2star_ps_int.coeff 3 = 96 := by
    simp only [E2star_ps_int, PowerSeries.coeff_mk]; decide
  refine ⟨?_, ?_, ?_⟩ <;>
  simp [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ, h0, h1, h2, h3] <;> ring

private lemma E2star_pow_succ_coeff (b : ℕ) :
    (E2star_ps_int ^ (b + 1)).coeff 1 =
      (E2star_ps_int ^ b).coeff 0 * 24 + (E2star_ps_int ^ b).coeff 1 ∧
    (E2star_ps_int ^ (b + 1)).coeff 2 = (E2star_ps_int ^ b).coeff 0 * 24 +
      (E2star_ps_int ^ b).coeff 1 * 24 + (E2star_ps_int ^ b).coeff 2 ∧
    (E2star_ps_int ^ (b + 1)).coeff 3 = (E2star_ps_int ^ b).coeff 0 * 96 +
      (E2star_ps_int ^ b).coeff 1 * 24 + (E2star_ps_int ^ b).coeff 2 * 24 +
        (E2star_ps_int ^ b).coeff 3 := by
  rw [pow_succ]; exact coeff_mul_E2star _

private lemma E2star_pow_coeffs :
    (E2star_ps_int ^ 1).coeff 3 = 96 ∧ (E2star_ps_int ^ 2).coeff 3 = 1344 ∧
    (E2star_ps_int ^ 3).coeff 3 = 17568 ∧ (E2star_ps_int ^ 4).coeff 3 = 62592 ∧
    (E2star_ps_int ^ 4).coeff 1 = 96 := by
  have c0 := E2star_pow_coeff_zero
  have z1 : (E2star_ps_int ^ 0).coeff 1 = 0 := by simp [PowerSeries.coeff_one]
  have z2 : (E2star_ps_int ^ 0).coeff 2 = 0 := by simp [PowerSeries.coeff_one]
  have z3 : (E2star_ps_int ^ 0).coeff 3 = 0 := by simp [PowerSeries.coeff_one]
  obtain ⟨a1, a2, a3⟩ := E2star_pow_succ_coeff 0
  obtain ⟨b1, b2, b3⟩ := E2star_pow_succ_coeff 1
  obtain ⟨d1, d2, d3⟩ := E2star_pow_succ_coeff 2
  obtain ⟨f1, -, f3⟩ := E2star_pow_succ_coeff 3
  simp only [c0, z1, z2, z3, Nat.reduceAdd] at a1 a2 a3 b1 b2 b3 d1 d2 d3 f1 f3
  simp only [a1, a2, a3] at b1 b2 b3
  simp only [b1, b2, b3] at d1 d2 d3
  simp only [d1, d2, d3] at f1 f3
  norm_num at a3 b3 d3 f1 f3
  exact ⟨by rw [pow_one]; exact a3, b3, d3, f3, f1⟩

end HeckeE2

section TauZero
open UpperHalfPlane hiding I
open Complex Filter Function ModularForm ModularGroup CongruenceSubgroup
open Matrix.SpecialLinearGroup
open scoped Real Topology Manifold MatrixGroups ModularForm

private lemma structure_small (N : ℕ) (hN : N < 4) (f : ModularForm Γ02 (2 * (N : ℤ)))
    (hW : (f : ℍ → ℂ) ∣[2 * (N : ℤ)] W2 = ((-1 : ℂ) ^ N) • (f : ℍ → ℂ))
    {G : PowerSeries ℤ} (hG : HasIntQ f G) (τ : ℍ) :
    f τ = (qExpansion 1 (f : ℍ → ℂ)).coeff 0 * E2star τ ^ N := by
  obtain ⟨c, hc⟩ := structure_Gamma02_dvd N 1 f hW (fun m => ⟨G.coeff m, by
    rw [hG.2, PowerSeries.coeff_map]; simp⟩)
  have h0 : N / 4 = 0 := by omega
  have hf : ∀ τ, f τ = (c 0 : ℂ) * E2star τ ^ N := by
    intro τ; rw [hc τ, h0]; simp
  have hq : HasIntQ f (PowerSeries.C (c 0) * E2star_ps_int ^ N) :=
    ((hasIntQ_E2star.pow N).zsmul (c 0)).congr_fun (by ext τ; rw [hf τ]; simp)
  rw [hq.2, PowerSeries.coeff_map, PowerSeries.coeff_C_mul, E2star_pow_coeff_zero, hf τ]
  simp

private lemma Delta8_ps_coeffs : Delta8_ps_int.coeff 0 = 0 ∧ Delta8_ps_int.coeff 1 = 1 := by
  refine ⟨by simp [Delta8_ps_int], ?_⟩
  rw [Delta8_ps_int, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, eta4_prod_ps_int_coeff_zero,
    one_pow]

private lemma structure_four (N : ℕ) (hN : N = 4) (f : ModularForm Γ02 (2 * (N : ℤ)))
    (hW : (f : ℍ → ℂ) ∣[2 * (N : ℤ)] W2 = ((-1 : ℂ) ^ N) • (f : ℍ → ℂ))
    {G : PowerSeries ℤ} (hG : HasIntQ f G) (τ : ℍ) :
    f τ = (qExpansion 1 (f : ℍ → ℂ)).coeff 0 * E2star τ ^ 4 +
      ((qExpansion 1 (f : ℍ → ℂ)).coeff 1 - 96 * (qExpansion 1 (f : ℍ → ℂ)).coeff 0) *
        Delta8 τ := by
  obtain ⟨c, hc⟩ := structure_Gamma02_dvd N 1 f hW (fun m => ⟨G.coeff m, by
    rw [hG.2, PowerSeries.coeff_map]; simp⟩)
  subst hN
  have hf : ∀ τ, f τ = (c 0 : ℂ) * E2star τ ^ 4 + (c 1 : ℂ) * Delta8 τ := by
    intro τ; rw [hc τ]; simp [Finset.sum_range_succ]
  have hq : HasIntQ f (PowerSeries.C (c 0) * E2star_ps_int ^ 4 +
      PowerSeries.C (c 1) * Delta8_ps_int) :=
    (((hasIntQ_E2star.pow 4).zsmul (c 0)).add (hasIntQ_Delta8.zsmul (c 1))).congr_fun
      (by ext τ; rw [hf τ]; simp)
  obtain ⟨hD0, hD1⟩ := Delta8_ps_coeffs
  have hE1 := E2star_pow_coeffs.2.2.2.2
  rw [hq.2, PowerSeries.coeff_map, PowerSeries.coeff_map, hf τ]
  simp only [map_add, PowerSeries.coeff_C_mul, E2star_pow_coeff_zero, hD0, hD1, hE1]
  simp only [eq_intCast]
  push_cast
  ring

/- #### The `p = 3` family -/

private lemma newton_small (p : ℕ) [NeZero p] (Φ : Matrix (Fin 2) (Fin 2) ℤ → ℍ → ℂ) :
    Ssym p Φ 1 = Psum p Φ 1 ∧
    (2 : ℂ) • Ssym p Φ 2 = Ssym p Φ 1 * Psum p Φ 1 - Psum p Φ 2 ∧
    (3 : ℂ) • Ssym p Φ 3 =
      Ssym p Φ 2 * Psum p Φ 1 - Ssym p Φ 1 * Psum p Φ 2 + Psum p Φ 3 ∧
    (4 : ℂ) • Ssym p Φ 4 = Ssym p Φ 3 * Psum p Φ 1 - Ssym p Φ 2 * Psum p Φ 2 +
      Ssym p Φ 1 * Psum p Φ 3 - Psum p Φ 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext τ
  · have h := Ssym_newton (p := p) Φ 1 τ
    simp [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Ssym_zero] at h
    linear_combination h
  · have h := Ssym_newton (p := p) Φ 2 τ
    simp [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, Ssym_zero] at h
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, smul_eq_mul]
    linear_combination h
  · have h := Ssym_newton (p := p) Φ 3 τ
    simp [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, Ssym_zero] at h
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, smul_eq_mul]
    linear_combination h
  · have h := Ssym_newton (p := p) Φ 4 τ
    simp [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, Ssym_zero] at h
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, smul_eq_mul]
    linear_combination h

private lemma coeff0_mul' (f g : PowerSeries ℂ) : (f * g).coeff 0 = f.coeff 0 * g.coeff 0 := by
  simp [PowerSeries.coeff_mul]

private lemma coeff1_mul' (f g : PowerSeries ℂ) :
    (f * g).coeff 1 = f.coeff 0 * g.coeff 1 + f.coeff 1 * g.coeff 0 := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

private lemma b3_niceQ_Psum (b : ℕ) : NiceQ (Psum 3 (bFam 3) b) :=
  (hasIntQ_Psum_bFam Nat.prime_three b).1

private lemma b3_divQ (r : ℕ) : DivQ 1 (((r.factorial : ℤ) : ℂ) • Ssym 3 (bFam 3) r) :=
  Ssym_divQ_one (bFam 3) (fun b _ => DivQ.of_hasIntQ (hasIntQ_Psum_bFam Nat.prime_three b)) r

private lemma b3_niceQ_Ssym (r : ℕ) : NiceQ (Ssym 3 (bFam 3) r) := by
  obtain ⟨G, hG, -⟩ := b3_divQ r
  have h := hG.1.smul (((r.factorial : ℤ) : ℂ))⁻¹
  have hne : (((r.factorial : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
  rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h

private lemma b3_Psum_coeffs (b : ℕ) :
    (qExpansion 1 (Psum 3 (bFam 3) b)).coeff 0 = 9 ^ b + 3 ∧
    (qExpansion 1 (Psum 3 (bFam 3) b)).coeff 1 = 3 * ((E2star_ps_int ^ b).coeff 3 : ℂ) := by
  rw [(hasIntQ_Psum_bFam Nat.prime_three b).2, PowerSeries.coeff_map, PowerSeries.coeff_map,
    PPs_coeff_zero, PPs_coeff_one (by norm_num)]
  constructor <;> simp only [eq_intCast] <;> push_cast <;> ring

private lemma b3_coeffs :
    (qExpansion 1 (Ssym 3 (bFam 3) 1)).coeff 0 = 12 ∧
    (qExpansion 1 (Ssym 3 (bFam 3) 2)).coeff 0 = 30 ∧
    (qExpansion 1 (Ssym 3 (bFam 3) 3)).coeff 0 = 28 ∧
    (qExpansion 1 (Ssym 3 (bFam 3) 4)).coeff 0 = 9 ∧
    (qExpansion 1 (Ssym 3 (bFam 3) 4)).coeff 1 = 111456 := by
  obtain ⟨N1, N2, N3, N4⟩ := newton_small 3 (bFam 3)
  have hS := b3_niceQ_Ssym
  have hP := b3_niceQ_Psum
  obtain ⟨P10, P11⟩ := b3_Psum_coeffs 1
  obtain ⟨P20, P21⟩ := b3_Psum_coeffs 2
  obtain ⟨P30, P31⟩ := b3_Psum_coeffs 3
  obtain ⟨P40, P41⟩ := b3_Psum_coeffs 4
  obtain ⟨e1, e2, e3, e4, -⟩ := E2star_pow_coeffs
  rw [e1] at P11; rw [e2] at P21; rw [e3] at P31; rw [e4] at P41
  push_cast at P11 P21 P31 P41
  -- q-expansions of the Newton identities
  have q1 := congrArg (qExpansion 1) N1
  have q2 := congrArg (qExpansion 1) N2
  have q3 := congrArg (qExpansion 1) N3
  have q4 := congrArg (qExpansion 1) N4
  rw [NiceQ.qExp_smul _ (hS 2), NiceQ.qExp_sub ((hS 1).mul (hP 1)) (hP 2),
    NiceQ.qExp_mul (hS 1) (hP 1)] at q2
  rw [NiceQ.qExp_smul _ (hS 3), NiceQ.qExp_add (((hS 2).mul (hP 1)).sub ((hS 1).mul (hP 2)))
    (hP 3), NiceQ.qExp_sub ((hS 2).mul (hP 1)) ((hS 1).mul (hP 2)),
    NiceQ.qExp_mul (hS 2) (hP 1), NiceQ.qExp_mul (hS 1) (hP 2)] at q3
  rw [NiceQ.qExp_smul _ (hS 4),
    NiceQ.qExp_sub ((((hS 3).mul (hP 1)).sub ((hS 2).mul (hP 2))).add ((hS 1).mul (hP 3)))
      (hP 4),
    NiceQ.qExp_add (((hS 3).mul (hP 1)).sub ((hS 2).mul (hP 2))) ((hS 1).mul (hP 3)),
    NiceQ.qExp_sub ((hS 3).mul (hP 1)) ((hS 2).mul (hP 2)),
    NiceQ.qExp_mul (hS 3) (hP 1), NiceQ.qExp_mul (hS 2) (hP 2),
    NiceQ.qExp_mul (hS 1) (hP 3)] at q4
  set s1 := qExpansion 1 (Ssym 3 (bFam 3) 1)
  set s2 := qExpansion 1 (Ssym 3 (bFam 3) 2)
  set s3 := qExpansion 1 (Ssym 3 (bFam 3) 3)
  set s4 := qExpansion 1 (Ssym 3 (bFam 3) 4)
  set π1 := qExpansion 1 (Psum 3 (bFam 3) 1)
  set π2 := qExpansion 1 (Psum 3 (bFam 3) 2)
  set π3 := qExpansion 1 (Psum 3 (bFam 3) 3)
  set π4 := qExpansion 1 (Psum 3 (bFam 3) 4)
  have c10 : s1.coeff 0 = 12 := by rw [q1, P10]; norm_num
  have c11 : s1.coeff 1 = 288 := by rw [q1, P11]; norm_num
  have r20 := congrArg (PowerSeries.coeff 0) q2
  have r21 := congrArg (PowerSeries.coeff 1) q2
  simp only [PowerSeries.coeff_C_mul, map_sub, coeff0_mul', coeff1_mul',
    c10, c11, P10, P11, P20, P21] at r20 r21
  have c20 : s2.coeff 0 = 30 := by linear_combination r20 / 2
  have c21 : s2.coeff 1 = 1440 := by linear_combination r21 / 2
  have r30 := congrArg (PowerSeries.coeff 0) q3
  have r31 := congrArg (PowerSeries.coeff 1) q3
  simp only [PowerSeries.coeff_C_mul, map_sub, map_add, coeff0_mul',
    coeff1_mul', c10, c11, c20, c21, P10, P11, P20, P21, P30, P31] at r30 r31
  have c30 : s3.coeff 0 = 28 := by linear_combination r30 / 3
  have c31 : s3.coeff 1 = 2016 := by linear_combination r31 / 3
  have r40 := congrArg (PowerSeries.coeff 0) q4
  have r41 := congrArg (PowerSeries.coeff 1) q4
  simp only [PowerSeries.coeff_C_mul, map_sub, map_add, coeff0_mul',
    coeff1_mul', c10, c11, c20, c21, c30, c31, P10, P11, P20, P21, P30, P31, P40,
    P41] at r40 r41
  have c40 : s4.coeff 0 = 9 := by linear_combination r40 / 4
  have c41 : s4.coeff 1 = 111456 := by linear_combination r41 / 4
  exact ⟨c10, c20, c30, c40, c41⟩

private lemma b3_hW (r : ℕ) :
    ((((r.factorial : ℤ) : ℂ) • Ssym 3 (bFam 3) r) ∣[2 * ((r * 1 : ℕ) : ℤ)] W2) =
      ((-1 : ℂ) ^ (r * 1)) • (((r.factorial : ℤ) : ℂ) • Ssym 3 (bFam 3) r) := by
  rw [smul_slash_of_det_pos (by rw [W2_det_val]; exact one_pos),
    (bFam_isBranchFamily Nat.prime_three).Ssym_slash_W2 Nat.prime_three (by norm_num), smul_comm]

/-- The modular form `r! S_r` for the `p = 3` family. -/
private noncomputable def b3MF (r : ℕ) : ModularForm Γ02 (2 * ((r * 1 : ℕ) : ℤ)) :=
  (((r.factorial : ℤ) : ℂ)) • SsymMF (bFam_isBranchFamily Nat.prime_three) Nat.prime_three
    (by norm_num) bFam_mdiff (bFam_bdd Nat.prime_three) r

private lemma b3MF_coe (r : ℕ) :
    (b3MF r : ℍ → ℂ) = (((r.factorial : ℤ) : ℂ)) • Ssym 3 (bFam 3) r := rfl

private lemma b3MF_coeff (r i : ℕ) : (qExpansion 1 (b3MF r : ℍ → ℂ)).coeff i =
    ((r.factorial : ℤ) : ℂ) * (qExpansion 1 (Ssym 3 (bFam 3) r)).coeff i := by
  rw [b3MF_coe, NiceQ.qExp_smul _ (b3_niceQ_Ssym r), PowerSeries.coeff_C_mul]

private lemma b3_small (r : ℕ) (hr : r < 4) (τ : ℍ) :
    Ssym 3 (bFam 3) r τ = (qExpansion 1 (Ssym 3 (bFam 3) r)).coeff 0 * E2star τ ^ r := by
  obtain ⟨G, hG, -⟩ := b3_divQ r
  have h := structure_small (r * 1) (by omega) (b3MF r) (by rw [b3MF_coe]; exact b3_hW r)
    (G := G) (by rw [b3MF_coe]; exact hG) τ
  rw [b3MF_coeff] at h
  simp only [Nat.mul_one] at h
  have hne : (((r.factorial : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
  change ((r.factorial : ℤ) : ℂ) * Ssym 3 (bFam 3) r τ = _ at h
  apply mul_left_cancel₀ hne
  rw [h]; ring

private lemma b3_four (τ : ℍ) : Ssym 3 (bFam 3) 4 τ = 9 * E2star τ ^ 4 + 110592 * Delta8 τ := by
  obtain ⟨G, hG, -⟩ := b3_divQ 4
  have h := structure_four (4 * 1) (by norm_num) (b3MF 4) (by rw [b3MF_coe]; exact b3_hW 4)
    (G := G) (by rw [b3MF_coe]; exact hG) τ
  rw [b3MF_coeff, b3MF_coeff, b3_coeffs.2.2.2.1, b3_coeffs.2.2.2.2] at h
  change ((Nat.factorial 4 : ℤ) : ℂ) * Ssym 3 (bFam 3) 4 τ = _ at h
  have h24 : ((Nat.factorial 4 : ℤ) : ℂ) = 24 := by norm_num [Nat.factorial]
  rw [h24] at h
  linear_combination h / 24

/-- The CM point $\tau_0 = (1 + i\sqrt5)/2$. -/
private noncomputable def tau0 : ℍ := ⟨(1 + I * (Real.sqrt 5 : ℂ)) / 2, by
  have h : ((1 + I * (Real.sqrt 5 : ℂ)) / 2).im = Real.sqrt 5 / 2 := by simp
  rw [h]
  positivity⟩

private lemma coe_tau0 : (tau0 : ℂ) = (1 + I * (Real.sqrt 5 : ℂ)) / 2 := rfl

private lemma sqrt5_sq : ((Real.sqrt 5 : ℝ) : ℂ) ^ 2 = 5 := by
  rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

private lemma I_sqrt5_sq : (I * (Real.sqrt 5 : ℂ)) ^ 2 = -5 := by
  rw [mul_pow, I_sq, sqrt5_sq]; ring

private lemma E2star_add_one (z w : ℍ) (h : (z : ℂ) = (w : ℂ) + 1) : E2star z = E2star w := by
  have := niceQ_E2star.per (w : ℂ)
  rw [← h] at this
  simpa [ofComplex_apply] using this

private lemma one_add_I_sqrt5_ne_zero : (1 + I * (Real.sqrt 5 : ℂ)) ≠ 0 := by
  intro h0
  have hu := I_sqrt5_sq
  have h' : I * (Real.sqrt 5 : ℂ) = -1 := by linear_combination h0
  rw [h'] at hu; norm_num at hu

private lemma b3_root : bFam 3 (gmat 3 (some 2)) tau0 = (2 - I * (Real.sqrt 5 : ℂ)) * E2star tau0 := by
  rw [bFam_some Nat.prime_three]
  have hv : (2 : ZMod 3).val = 2 := rfl
  rw [hv]
  have hu := I_sqrt5_sq
  have hne := one_add_I_sqrt5_ne_zero
  have h1 : E2star (shiftH 3 2 tau0) = E2star (W2 • tau0) := by
    apply E2star_add_one
    rw [coe_shiftH, coe_W2_smul, coe_tau0]
    push_cast
    field_simp
    linear_combination hu
  have h2 := apply_of_slash_eq (k := 2) W2_det_val
    (show E2star ∣[(2 : ℤ)] W2 = (-1 : ℂ) • E2star by rw [E2star_slash_W2, neg_one_smul]) tau0
  rw [h1, h2, denom_W2, coe_tau0]
  have h22 : ((Real.sqrt 2 : ℂ) * ((1 + I * (Real.sqrt 5 : ℂ)) / 2)) ^ (2 : ℤ) =
      2 * ((1 + I * (Real.sqrt 5 : ℂ)) / 2) ^ 2 := by
    rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, mul_pow, ← ofReal_pow,
      Real.sq_sqrt (by norm_num)]
    push_cast; ring
  rw [h22]
  linear_combination (-(1 : ℂ) / 2) * E2star tau0 * hu

/-- $E_2^*(\tau_0)^4 + 1024\,\Delta_8(\tau_0) = 0$. -/
private theorem E2star_Delta8_tau0 : E2star tau0 ^ 4 + 1024 * Delta8 tau0 = 0 := by
  have hprod := prod_sub_eq_sum_Ssym 3 (bFam 3) tau0 (bFam 3 (gmat 3 (some 2)) tau0)
  rw [Finset.prod_eq_zero (Finset.mem_univ (some 2)) (sub_self _)] at hprod
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Ssym_zero] at hprod
  rw [b3_small 1 (by norm_num), b3_small 2 (by norm_num), b3_small 3 (by norm_num), b3_four,
    b3_coeffs.1, b3_coeffs.2.1, b3_coeffs.2.2.1, b3_root] at hprod
  have hu := I_sqrt5_sq
  norm_num at hprod
  linear_combination (-1 / 108 : ℂ) * hprod -
    (1 / 108 : ℂ) * E2star tau0 ^ 4 *
      ((I * (Real.sqrt 5 : ℂ)) ^ 2 + 4 * (I * (Real.sqrt 5 : ℂ)) - 23) * hu

end TauZero

section CMRoots
open UpperHalfPlane hiding I
open Complex Filter Function ModularForm ModularGroup CongruenceSubgroup
open Matrix.SpecialLinearGroup
open scoped Real Topology Manifold MatrixGroups ModularForm

private lemma tau0_quad : 2 * (tau0 : ℂ) ^ 2 - 2 * tau0 + 3 = 0 := by
  rw [coe_tau0]; linear_combination (1 / 2 : ℂ) * I_sqrt5_sq

private lemma tau0_ne_zero : (tau0 : ℂ) ≠ 0 := by
  rw [coe_tau0]
  exact div_ne_zero one_add_I_sqrt5_ne_zero (by norm_num)

private lemma odd_xy_of_two_mul_prime {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) {x y : ℤ}
    (hxy : 2 * (p : ℤ) = x ^ 2 + 5 * y ^ 2) : Odd x ∧ Odd y := by
  have hp_odd : Odd (p : ℤ) := odd_p hp hp2
  obtain ⟨k, hk⟩ := hp_odd
  have hx : Odd x := by
    rw [Int.odd_iff]
    have h4 : (x ^ 2 + 5 * y ^ 2) % 4 = 2 := by omega
    rcases Int.emod_two_eq_zero_or_one x with hx0 | hx1
    · exfalso
      obtain ⟨a, ha⟩ : ∃ a, x = 2 * a := ⟨x / 2, by omega⟩
      rcases Int.emod_two_eq_zero_or_one y with hy0 | hy1
      · obtain ⟨b, hb⟩ : ∃ b, y = 2 * b := ⟨y / 2, by omega⟩
        have : (x ^ 2 + 5 * y ^ 2) % 4 = 0 := by
          rw [ha, hb]
          have : (2 * a) ^ 2 + 5 * (2 * b) ^ 2 = 4 * (a ^ 2 + 5 * b ^ 2) := by ring
          omega
        omega
      · obtain ⟨b, hb⟩ : ∃ b, y = 2 * b + 1 := ⟨y / 2, by omega⟩
        have : (x ^ 2 + 5 * y ^ 2) % 4 = 1 := by
          rw [ha, hb]
          have : (2 * a) ^ 2 + 5 * (2 * b + 1) ^ 2 = 4 * (a ^ 2 + 5 * b ^ 2 + 5 * b + 1) + 1 := by
            ring
          omega
        omega
    · exact hx1
  have hy : Odd y := by
    rw [Int.odd_iff]
    have h4 : (x ^ 2 + 5 * y ^ 2) % 4 = 2 := by omega
    obtain ⟨a, ha⟩ := hx
    rcases Int.emod_two_eq_zero_or_one y with hy0 | hy1
    · exfalso
      obtain ⟨b, hb⟩ : ∃ b, y = 2 * b := ⟨y / 2, by omega⟩
      have : (x ^ 2 + 5 * y ^ 2) % 4 = 1 := by
        rw [ha, hb]
        have : (2 * a + 1) ^ 2 + 5 * (2 * b) ^ 2 = 4 * (a ^ 2 + a + 5 * b ^ 2) + 1 := by ring
        omega
      omega
    · exact hy1
  exact ⟨hx, hy⟩

/-- The Fricke-twisted CM matrix $\gamma_2 = \begin{pmatrix} y & (x-y)/2 \\ -(x+y) & 3y\end{pmatrix}$
mapping $\tau_0$ to $W_2 \cdot \tau_0$. -/
private def gam2 (x y : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![y, (x - y) / 2; -(x + y), 3 * y]

private lemma gam2_det {x y : ℤ} (hx : Odd x) (hy : Odd y) :
    2 * (gam2 x y).det = x ^ 2 + 5 * y ^ 2 := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hdiv : (2 * a + 1 - (2 * b + 1)) / 2 = a - b := by omega
  simp only [gam2, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, hdiv]
  ring

private lemma gam2_10 {x y : ℤ} (hx : Odd x) (hy : Odd y) :
    (2 : ℤ) ∣ gam2 x y 1 0 := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  refine ⟨-(a + b + 1), ?_⟩
  simp only [gam2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

private lemma chiInt_gam2 {x y : ℤ} (hx : Odd x) (hy : Odd y) :
    chiInt (gam2 x y) = -1 := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have h : gam2 (2 * a + 1) (2 * b + 1) 0 1 + gam2 (2 * a + 1) (2 * b + 1) 1 0 / 2 =
      -(2 * b + 1) := by
    simp only [gam2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    omega
  unfold chiInt
  rw [h, if_neg]
  intro hev
  obtain ⟨c, hc⟩ := hev
  omega

private lemma gam2_denom (x y : ℤ) :
    (gam2 x y 1 0 : ℂ) * tau0 + gam2 x y 1 1 =
      -(tau0 : ℂ) * ((x : ℂ) + y * (I * (Real.sqrt 5 : ℂ))) := by
  have hu := I_sqrt5_sq
  simp only [gam2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [coe_tau0]
  push_cast
  linear_combination ((y : ℂ) / 2) * hu

private lemma gam2_map {x y : ℤ} (hx : Odd x) (hy : Odd y) (hpos : 0 < (gam2 x y).det) :
    glZ (gam2 x y) • tau0 = W2 • tau0 := by
  have hM0 : (gam2 x y).det ≠ 0 := hpos.ne'
  have hd : (gam2 x y 1 0 : ℂ) * tau0 + gam2 x y 1 1 ≠ 0 := by
    rw [← denom_glZ hM0]; exact denom_ne_zero _ _
  have h2t : (2 : ℂ) * tau0 ≠ 0 := mul_ne_zero (by norm_num) tau0_ne_zero
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hdiv : (2 * a + 1 - (2 * b + 1)) / 2 = a - b := by omega
  ext
  rw [coe_glZ_smul hpos, coe_W2_smul, div_eq_iff hd]
  have hq := tau0_quad
  simp only [gam2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, hdiv]
  push_cast
  apply mul_left_cancel₀ h2t
  rw [show (2 : ℂ) * tau0 *
        (-(2 * (tau0 : ℂ))⁻¹ * (-(2 * a + 1 + (2 * b + 1)) * tau0 + 3 * (2 * b + 1))) =
      -(((2 : ℂ) * (tau0 : ℂ) * (2 * (tau0 : ℂ))⁻¹) *
        (-(2 * a + 1 + (2 * b + 1)) * tau0 + 3 * (2 * b + 1))) by ring,
    mul_inv_cancel₀ h2t, one_mul]
  linear_combination (2 * (b : ℂ) + 1) * hq

/-- CM value of a branch mapping `tau0` to `W2 • tau0`. -/
private lemma nuFam_CM_W2 {p : ℕ} (hp : p.Prime) {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M.det = p)
    (hmap : glZ M • tau0 = W2 • tau0) (hχ : chiInt M = -1) :
    nuFam p M tau0 = (Cn p : ℂ) * eta4 tau0 ^ (p - 1) * E2star tau0 *
      (((M 1 0 : ℂ) * tau0 + M 1 1) ^ 2 / (2 * (tau0 : ℂ) ^ 2)) := by
  have hpos := glZ_det_pos hp hM
  have hM0 : M.det ≠ 0 := by rw [hM]; exact_mod_cast hp.ne_zero
  have hdetv : ((glZ M).det.val : ℂ) = p := by rw [glZ_det hM0, hM]; push_cast; rfl
  have hd0 : denom (glZ M) tau0 ≠ 0 := denom_ne_zero _ _
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have he0 := eta4_ne_zero tau0
  have ht0 := tau0_ne_zero
  have hE2W := apply_of_slash_eq (k := 2) W2_det_val
    (show E2star ∣[(2 : ℤ)] W2 = (-1 : ℂ) • E2star by rw [E2star_slash_W2, neg_one_smul]) tau0
  have hηW := apply_of_slash_eq (k := 4) W2_det_val
    (show eta4 ∣[(4 : ℤ)] W2 = (1 : ℂ) • eta4 by rw [one_smul]; exact eta4_slash_W2) tau0
  have hsq2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hE2W' : E2star (W2 • tau0) = -2 * (tau0 : ℂ) ^ 2 * E2star tau0 := by
    rw [hE2W, denom_W2, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, mul_pow, hsq2]
    ring
  have hηW' : eta4 (W2 • tau0) = 4 * (tau0 : ℂ) ^ 4 * eta4 tau0 := by
    rw [hηW, denom_W2, show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast, mul_pow,
      show (Real.sqrt 2 : ℂ) ^ 4 = ((Real.sqrt 2 : ℂ) ^ 2) ^ 2 by ring, hsq2]
    ring
  simp only [nuFam]
  rw [slash_apply_of_det_pos hpos, slash_apply_of_det_pos hpos, hmap, hE2W', hηW', hdetv, hχ,
    ← denom_glZ hM0]
  have hpow : eta4 tau0 ^ p = eta4 tau0 ^ (p - 1) * eta4 tau0 := by
    rw [← pow_succ, Nat.sub_add_cancel hp.pos]
  rw [show ((2 : ℤ) - 1) = 1 by norm_num, show ((4 : ℤ) - 1) = 3 by norm_num, zpow_one,
    show ((p : ℂ) ^ (3 : ℤ)) = (p : ℂ) ^ (3 : ℕ) by norm_cast,
    show denom (glZ M) tau0 ^ (-(2 : ℤ)) = (denom (glZ M) tau0 ^ (2 : ℕ))⁻¹ by
      rw [zpow_neg]; norm_cast,
    show denom (glZ M) tau0 ^ (-(4 : ℤ)) = (denom (glZ M) tau0 ^ (4 : ℕ))⁻¹ by
      rw [zpow_neg]; norm_cast]
  rw [hpow]
  field_simp
  ring

/-- Each `γ_2 = gam2 x y` (and its conjugate `gam2 x (-y)`) gives a root of the `ν`-polynomial. -/
private lemma nu_root_c2 {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : 2 < p) {x y : ℤ}
    (hxy : 2 * (p : ℤ) = x ^ 2 + 5 * y ^ 2) :
    ∃ m : Option (ZMod p), nuFam p (gmat p m) tau0 = (Cn p : ℂ) * eta4 tau0 ^ (p - 1) *
      E2star tau0 * (((x : ℂ) + y * (I * (Real.sqrt 5 : ℂ))) ^ 2 / 2) := by
  obtain ⟨hx, hy⟩ := odd_xy_of_two_mul_prime hp hp2 hxy
  have hdet : (gam2 x y).det = p := by
    have h2 := gam2_det hx hy
    omega
  have hpos : 0 < (gam2 x y).det := by rw [hdet]; exact_mod_cast hp.pos
  obtain ⟨σ, hσ, hσM⟩ := cosetIdx_spec hp hp2 hdet (gam2_10 hx hy)
  refine ⟨cosetIdx p (gam2 x y), ?_⟩
  have hl := (nuFam_isBranchFamily hp hp2).left σ hσ (gmat p (cosetIdx p (gam2 x y)))
    (gmat_det p _) (gmat_10_dvd p _)
  rw [hσM] at hl
  rw [← hl, nuFam_CM_W2 hp hdet (gam2_map hx hy hpos) (chiInt_gam2 hx hy), gam2_denom]
  have ht0 := tau0_ne_zero
  field_simp

end CMRoots

section Final
open UpperHalfPlane hiding I
open Complex Filter Function ModularForm ModularGroup CongruenceSubgroup
open Matrix.SpecialLinearGroup
open scoped Real Topology Manifold MatrixGroups ModularForm

/-- The integer sequence $t_n$ with $t_0 = 2$, $t_1 = \sigma$, $t_{n+2} = \sigma t_{n+1} - q t_n$. -/
private def tseq (σ q : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => σ
  | (n + 2) => σ * tseq σ q (n + 1) - q * tseq σ q n

private lemma tseq_cast (σ q : ℤ) (b1 b2 : ℂ) (hs : b1 + b2 = σ) (hq : b1 * b2 = q) (n : ℕ) :
    (tseq σ q n : ℂ) = b1 ^ n + b2 ^ n := by
  have key : ∀ n, (tseq σ q n : ℂ) = b1 ^ n + b2 ^ n ∧
      (tseq σ q (n + 1) : ℂ) = b1 ^ (n + 1) + b2 ^ (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨by norm_num [tseq], by simp [tseq, hs]⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [tseq]
      push_cast
      rw [ih.2, ih.1, ← hs, ← hq]
      ring
  exact (key n).1

private lemma tseq_mod (p : ℕ) (σ : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    ((tseq σ ((p : ℤ) ^ 2) n : ℤ) : R2 p) = (σ : R2 p) ^ n := by
  have hp0 : (((p : ℤ) ^ 2 : ℤ) : R2 p) = 0 := by push_cast; exact p_sq_zero p
  have key : ∀ n, ((tseq σ ((p : ℤ) ^ 2) (n + 1) : ℤ) : R2 p) = (σ : R2 p) ^ (n + 1) ∧
      ((tseq σ ((p : ℤ) ^ 2) (n + 2) : ℤ) : R2 p) = (σ : R2 p) ^ (n + 2) := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simp [tseq], ?_⟩
      rw [tseq]
      push_cast
      rw [show ((p : R2 p)) ^ 2 = 0 from p_sq_zero p]
      simp [tseq]
      ring
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [show n + 1 + 2 = (n + 1) + 2 from rfl, tseq, Int.cast_sub, Int.cast_mul, Int.cast_mul,
        hp0, zero_mul, sub_zero, ih.2]
      ring
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (key m).1

private lemma key_term (E D : ℂ) (h : E ^ 4 + 1024 * D = 0) {L j M : ℕ} (hjL : j ≤ L) (hjM : 4 * j ≤ M) :
    (1024 : ℂ) ^ L * (D ^ j * E ^ (M - 4 * j)) =
      (((-1) ^ j * 1024 ^ (L - j) : ℤ) : ℂ) * E ^ M := by
  obtain ⟨a, rfl⟩ : ∃ a, L = j + a := ⟨L - j, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, M = 4 * j + b := ⟨M - 4 * j, by omega⟩
  rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
  have h1 : (1024 : ℂ) ^ j * D ^ j = (-1) ^ j * E ^ (4 * j) := by
    rw [← mul_pow, show (1024 : ℂ) * D = (-1) * E ^ 4 by linear_combination h, mul_pow, pow_mul]
  push_cast
  rw [pow_add, pow_add]
  linear_combination (1024 ^ a * E ^ b) * h1

private lemma x_not_dvd_c2 {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hp5 : p ≠ 5) {x y : ℤ}
    (hxy : 2 * (p : ℤ) = x ^ 2 + 5 * y ^ 2) : (x : ZMod p) ≠ 0 := by
  intro hx
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hx
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨a, rfl⟩ := hx
  have h5 : (p : ℤ) ∣ 5 * y ^ 2 := ⟨2 - p * a ^ 2, by linear_combination -hxy⟩
  rcases hpz.dvd_or_dvd h5 with h | h
  · have h' : p ∣ 5 := by exact_mod_cast h
    rcases (Nat.prime_five.eq_one_or_self_of_dvd p h') with h1 | h1
    · exact hp.one_lt.ne' h1
    · exact hp5 h1
  · obtain ⟨b, rfl⟩ := hpz.dvd_of_dvd_pow h
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have h1 : (p : ℤ) * (a ^ 2 + 5 * b ^ 2) = 2 := by
      apply mul_left_cancel₀ hp0
      linear_combination -hxy
    have hdvd : (p : ℤ) ∣ 2 := ⟨a ^ 2 + 5 * b ^ 2, h1.symm⟩
    have hdvdN : p ∣ 2 := by exact_mod_cast hdvd
    have := Nat.le_of_dvd (by decide) hdvdN
    omega

/-- The polynomial identity at a Fricke-twisted CM root, with denominators cleared. -/
private lemma root_identity_c2 {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : 2 < p) {h : ℕ}
    (hh : p = 2 * h + 1)
    (A : ℕ → ℤ) (F : ℤ) (L : ℕ) (hE4 : E2star tau0 ^ 4 + 1024 * Delta8 tau0 = 0)
    (hE0 : E2star tau0 ≠ 0)
    (hK : ∀ k ≤ p + 1, (F : ℂ) * 1024 ^ L * Ssym p (nuFam p) k tau0 =
      (A k : ℂ) * E2star tau0 ^ (k * (2 * p - 1)))
    (x yy : ℤ) (hyy : 2 * (p : ℤ) = x ^ 2 + 5 * yy ^ 2) :
    ∑ k ∈ Finset.range (p + 1 + 1), (-1 : ℂ) ^ k * (A k : ℂ) * 4 ^ (h * k) *
      ((-1) ^ h * (((x : ℂ) + yy * (I * (Real.sqrt 5 : ℂ))) ^ 2 / 2)) ^ (p + 1 - k) = 0 := by
  obtain ⟨m, hm⟩ := nu_root_c2 hp hp2 hyy
  have hpoly := prod_sub_eq_sum_Ssym p (nuFam p) tau0 (nuFam p (gmat p m) tau0)
  rw [Finset.prod_eq_zero (Finset.mem_univ m) (sub_self _)] at hpoly
  set N := 2 * p - 1 with hN
  have hN4 : N = 4 * h + 1 := by omega
  set Y := nuFam p (gmat p m) tau0 with hYdef
  set β := (-1 : ℂ) ^ h * (((x : ℂ) + yy * (I * (Real.sqrt 5 : ℂ))) ^ 2 / 2) with hβ
  have hY : (4 : ℂ) ^ h * Y = E2star tau0 ^ N * β := by
    rw [hm]
    have hη : eta4 tau0 ^ (p - 1) = Delta8 tau0 ^ h := by
      rw [show p - 1 = 2 * h by omega, pow_mul]; rfl
    have hCn : (Cn p : ℂ) = 256 ^ h := by
      simp only [Cn]; push_cast; rw [show p - 1 = 2 * h by omega, pow_mul]; norm_num
    have h4 : (4 : ℂ) ^ h * (256 ^ h * Delta8 tau0 ^ h) = (-1) ^ h * (E2star tau0 ^ 4) ^ h := by
      rw [← mul_pow, ← mul_pow, show (4 : ℂ) * (256 * Delta8 tau0) = -(E2star tau0 ^ 4) by
        linear_combination hE4, neg_pow]
    rw [hη, hCn, hN4, hβ]
    linear_combination (E2star tau0 * (((x : ℂ) + yy * (I * (Real.sqrt 5 : ℂ))) ^ 2 / 2)) * h4
  clear_value β Y
  have hmain : E2star tau0 ^ (N * (p + 1)) * ∑ k ∈ Finset.range (p + 1 + 1),
      (-1 : ℂ) ^ k * (A k : ℂ) * 4 ^ (h * k) * β ^ (p + 1 - k) =
      ((F : ℂ) * 1024 ^ L) * 4 ^ (h * (p + 1)) * ∑ k ∈ Finset.range (p + 1 + 1),
        (-1) ^ k * Ssym p (nuFam p) k tau0 * Y ^ (p + 1 - k) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ p + 1 := by simp only [Finset.mem_range] at hk; omega
    obtain ⟨n, hn⟩ : ∃ n, p + 1 = k + n := ⟨p + 1 - k, by omega⟩
    have hsub : p + 1 - k = n := by omega
    rw [hsub]
    have e1 : E2star tau0 ^ (N * (p + 1)) = E2star tau0 ^ (k * N) * (E2star tau0 ^ N) ^ n := by
      rw [← pow_mul, ← pow_add, hn]; congr 1; ring1
    have e2 : (4 : ℂ) ^ (h * (p + 1)) = 4 ^ (h * k) * ((4 : ℂ) ^ h) ^ n := by
      rw [← pow_mul, ← pow_add, hn]; congr 1; ring1
    rw [e1, e2]
    have hKk := hK k hk'
    calc _ = (-1) ^ k * ((A k : ℂ) * E2star tau0 ^ (k * N)) * 4 ^ (h * k) *
          (E2star tau0 ^ N * β) ^ n := by ring1
      _ = (-1) ^ k * ((F : ℂ) * 1024 ^ L * Ssym p (nuFam p) k tau0) * 4 ^ (h * k) *
          ((4 : ℂ) ^ h * Y) ^ n := by rw [hKk, hY]
      _ = _ := by ring1
  rw [← hpoly, mul_zero] at hmain
  exact (mul_eq_zero.mp hmain).resolve_left (pow_ne_zero _ hE0)

/-- **Main congruence** for `conjecture2` in `ZMod (p^2)`. -/
private theorem main_congr_c2 {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hp5 : p ≠ 5) (x y : ℤ)
    (hxy : 2 * (p : ℤ) = x ^ 2 + 5 * y ^ 2) :
    ((∑ k ∈ Finset.range p, OeisA179524.a k : ℤ) : R2 p) =
      ((2 * x ^ 2 - 2 * (p : ℤ) : ℤ) : R2 p) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨h, hh⟩ : ∃ h, p = 2 * h + 1 := by
    obtain ⟨h, hh⟩ := hp.odd_of_ne_two (by omega); exact ⟨h, hh⟩
  have hE4 : E2star tau0 ^ 4 + 1024 * Delta8 tau0 = 0 := E2star_Delta8_tau0
  have hE0 : E2star tau0 ≠ 0 := by
    intro h0
    apply Delta8_ne_zero tau0
    rw [h0] at hE4
    linear_combination hE4 / 1024
  obtain ⟨c, hc1, hcmod⟩ := Ssym_nu_one_coeffs hp hp2 hh
  choose! C hC using fun k (hk : 2 ≤ k) => nu_Sk_structure hp hp2 k hk
  set N := 2 * p - 1 with hN
  set L := (p + 1) * N with hL
  set F : ℤ := ((p - 1).factorial : ℤ) with hF
  have hNL : N ≤ L := Nat.le_mul_of_pos_left N (by omega)
  let A : ℕ → ℤ := fun k => if k = 0 then F * 1024 ^ L else if k = 1 then
      F * ∑ j ∈ Finset.range (h + 1), c j * ((-1) ^ j * 1024 ^ (L - j))
    else (p : ℤ) ^ 2 * ∑ j ∈ Finset.range (k * N / 4 + 1), C k j * ((-1) ^ j * 1024 ^ (L - j))
  have hK : ∀ k ≤ p + 1, (F : ℂ) * 1024 ^ L * Ssym p (nuFam p) k tau0 =
      (A k : ℂ) * E2star tau0 ^ (k * N) := by
    intro k hk
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · simp [A, Ssym_zero]
      · simp only [A, one_ne_zero, if_false, if_true, one_mul]
        rw [hc1 tau0]
        push_cast
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjh : j ≤ h := by simp only [Finset.mem_range] at hj; omega
        rw [show (F : ℂ) * 1024 ^ L * ((c j : ℂ) * Delta8 tau0 ^ j * E2star tau0 ^ (N - 4 * j)) =
          (F : ℂ) * c j * ((1024 : ℂ) ^ L * (Delta8 tau0 ^ j * E2star tau0 ^ (N - 4 * j))) by ring,
          key_term _ _ hE4 (by omega) (by omega)]
        push_cast
        ring
    · have hC' := hC k hk2 tau0
      simp only [A, if_neg (show k ≠ 0 by omega), if_neg (show k ≠ 1 by omega)]
      rw [show (F : ℂ) * 1024 ^ L * Ssym p (nuFam p) k tau0 = (1024 : ℂ) ^ L *
        ((((p - 1).factorial : ℤ) : ℂ) * Ssym p (nuFam p) k tau0) by rw [hF]; ring, hC']
      push_cast
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j ≤ k * N / 4 := by simp only [Finset.mem_range] at hj; omega
      have h4j : 4 * j ≤ k * N := by omega
      have hkN : k * N ≤ (p + 1) * N := Nat.mul_le_mul_right _ hk
      have hjL : j ≤ L := by omega
      rw [show (1024 : ℂ) ^ L * ((p : ℂ) ^ 2 * (C k j : ℂ) * Delta8 tau0 ^ j *
          E2star tau0 ^ (k * N - 4 * j)) = (p : ℂ) ^ 2 * C k j *
          ((1024 : ℂ) ^ L * (Delta8 tau0 ^ j * E2star tau0 ^ (k * N - 4 * j))) by ring,
        key_term _ _ hE4 hjL h4j]
      push_cast
      ring
  -- the two conjugate Fricke-twisted CM roots
  have hr1 := root_identity_c2 hp hp2 hh A F L hE4 hE0 hK x y hxy
  have hr2 := root_identity_c2 hp hp2 hh A F L hE4 hE0 hK x (-y) (by rw [hxy]; ring)
  set b1 := (-1 : ℂ) ^ h * (((x : ℂ) + (y : ℂ) * (I * (Real.sqrt 5 : ℂ))) ^ 2 / 2) with hb1
  set b2 := (-1 : ℂ) ^ h * (((x : ℂ) + ((-y : ℤ) : ℂ) * (I * (Real.sqrt 5 : ℂ))) ^ 2 / 2) with hb2
  set σ : ℤ := (-1) ^ h * (2 * x ^ 2 - 2 * p) with hσ
  have hu := I_sqrt5_sq
  have hxyC : 2 * (p : ℂ) = (x : ℂ) ^ 2 + 5 * (y : ℂ) ^ 2 := by exact_mod_cast hxy
  have hε2 : ((-1 : ℂ) ^ h) * (-1) ^ h = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have hs : b1 + b2 = (σ : ℂ) := by
    rw [hb1, hb2, hσ]
    push_cast
    linear_combination (-1 : ℂ) ^ h * (y : ℂ) ^ 2 * hu + (-1 : ℂ) ^ h * hxyC
  have hq : b1 * b2 = (((p : ℤ) ^ 2 : ℤ) : ℂ) := by
    rw [hb1, hb2]
    push_cast
    linear_combination (((x : ℂ) ^ 2 - (y : ℂ) ^ 2 * (I * (Real.sqrt 5 : ℂ)) ^ 2) ^ 2 / 4) * hε2 +
      (-(y : ℂ) ^ 2 * (2 * (x : ℂ) ^ 2 - (y : ℂ) ^ 2 * (I * (Real.sqrt 5 : ℂ)) ^ 2 +
        5 * (y : ℂ) ^ 2) / 4) * hu - (((x : ℂ) ^ 2 + 5 * (y : ℂ) ^ 2 + 2 * p) / 4) * hxyC
  have hT := tseq_cast σ ((p : ℤ) ^ 2) b1 b2 hs hq
  have hZ : ∑ k ∈ Finset.range (p + 1 + 1), (-1 : ℤ) ^ k * A k * 4 ^ (h * k) *
      tseq σ ((p : ℤ) ^ 2) (p + 1 - k) = 0 := by
    have h1 : ((∑ k ∈ Finset.range (p + 1 + 1), (-1 : ℤ) ^ k * A k * 4 ^ (h * k) *
        tseq σ ((p : ℤ) ^ 2) (p + 1 - k) : ℤ) : ℂ) = 0 := by
      push_cast
      simp only [hT]
      rw [← add_zero (0 : ℂ)]
      nth_rewrite 1 [← hr1]
      rw [← hr2, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    exact_mod_cast h1
  -- reduce modulo p^2
  let g : ℕ → R2 p := fun k => (((-1 : ℤ) ^ k * A k * 4 ^ (h * k) *
    tseq σ ((p : ℤ) ^ 2) (p + 1 - k) : ℤ) : R2 p)
  have hR : ∑ k ∈ Finset.range (p + 1 + 1), g k = 0 := by
    have := congrArg (Int.cast : ℤ → R2 p) hZ
    rw [Int.cast_sum, Int.cast_zero] at this
    exact this
  rw [Finset.sum_range_succ', Finset.sum_range_succ'] at hR
  have hrest : ∑ k ∈ Finset.range p, g (k + 1 + 1) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [g, A, if_neg (show k + 1 + 1 ≠ 0 by omega), if_neg (show k + 1 + 1 ≠ 1 by omega)]
    push_cast
    rw [p_sq_zero]
    ring
  rw [hrest, zero_add] at hR
  have ht0 := tseq_mod p σ (p + 1) (by omega)
  have ht1 := tseq_mod p σ p (by omega)
  set S1 : R2 p := ∑ j ∈ Finset.range (h + 1), (c j : R2 p) * ((-1) ^ j * 1024 ^ (L - j))
    with hS1
  have hg0 : g 0 = (F : R2 p) * 1024 ^ L * (σ : R2 p) ^ (p + 1) := by
    simp only [g, A, Nat.sub_zero]
    push_cast
    rw [ht0]
    ring
  have hg1 : g (0 + 1) = -((F : R2 p) * S1 * 4 ^ h * (σ : R2 p) ^ p) := by
    simp only [g, A, zero_add, one_ne_zero, if_false, if_true, Nat.add_sub_cancel]
    push_cast
    rw [ht1, hS1]
    ring
  rw [hg0, hg1] at hR
  -- units
  have hu2 : IsUnit (2 : R2 p) := by
    have := unit_small hp (by norm_num : 0 < 2) hp2
    simpa using this
  have hu4 : IsUnit (-4 : R2 p) := by
    rw [show (-4 : R2 p) = -(2 * 2) by ring]; exact (hu2.mul hu2).neg
  have h4inv : (-4 : R2 p) * (-4 : R2 p)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu4
  have hu1024 : IsUnit (1024 : R2 p) := by
    rw [show (1024 : R2 p) = 2 ^ 10 by norm_num]; exact hu2.pow 10
  have huF : IsUnit (F : R2 p) := by
    apply unit_red hp
    rw [map_intCast, hF, Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff,
      Nat.Prime.dvd_factorial hp]
    omega
  have hx0 := x_not_dvd_c2 hp hp2 hp5 hxy
  have h2p : (2 : ZMod p) ≠ 0 := by
    have := (hu2.map (red p)).ne_zero
    rwa [map_ofNat] at this
  have huσ : IsUnit (σ : R2 p) := by
    apply unit_red hp
    rw [map_intCast, hσ]
    push_cast
    rw [ZMod.natCast_self, mul_zero, sub_zero]
    refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) ?_
    exact mul_ne_zero h2p (pow_ne_zero 2 hx0)
  -- solve
  have hcomb : ((F : R2 p) * (σ : R2 p) ^ p) * ((1024 : R2 p) ^ L * σ - 4 ^ h * S1) = 0 := by
    linear_combination hR
  have hlin := (huF.mul (huσ.pow p)).mul_right_eq_zero.mp hcomb
  have hS2 : S1 = (1024 : R2 p) ^ L *
      ∑ j ∈ Finset.range (h + 1), atCoeff p h j * ((-4 : R2 p)⁻¹) ^ j := by
    rw [hS1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjh : j ≤ h := by simp only [Finset.mem_range] at hj; omega
    have hjL : j ≤ L := by omega
    rw [hcmod j hjh]
    have e1 : (1024 : R2 p) ^ L = 1024 ^ (L - j) * 1024 ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hjL]
    have h256 : (1024 : R2 p) * (-4)⁻¹ = -256 := by linear_combination (-256 : R2 p) * h4inv
    have e2 : (1024 : R2 p) ^ j * ((-4)⁻¹) ^ j = (-1) ^ j * 256 ^ j := by
      rw [← mul_pow, h256, neg_pow]
    rw [e1]
    linear_combination (-(atCoeff p h j) * 1024 ^ (L - j)) * e2
  have hσeq : (σ : R2 p) = 4 ^ h * ∑ j ∈ Finset.range (h + 1), atCoeff p h j *
      ((-4 : R2 p)⁻¹) ^ j := by
    apply (hu1024.pow L).mul_left_cancel
    rw [hS2] at hlin
    linear_combination hlin
  have hσcast : (σ : R2 p) = (-1) ^ h * (2 * (x : R2 p) ^ 2 - 2 * p) := by
    rw [hσ]; push_cast; ring
  have hε2' : ((-1 : R2 p) ^ h) * (-1) ^ h = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have hneg4 : (-4 : R2 p) ^ h = (-1) ^ h * 4 ^ h := by
    rw [show (-4 : R2 p) = (-1) * 4 by ring, mul_pow]
  push_cast
  rw [collapse_eq_atCoeff_sum hp hp2 hh]
  set S3 := ∑ j ∈ Finset.range (h + 1), atCoeff p h j * ((-4 : R2 p)⁻¹) ^ j
  linear_combination S3 * hneg4 - (-1 : R2 p) ^ h * hσeq + (-1 : R2 p) ^ h * hσcast +
    (2 * (x : R2 p) ^ 2 - 2 * p) * hε2'

end Final

end OMA

theorem OMA.solution : type_of% @OeisA179524.conjecture2 := by
  intro p hp h_mod x y h_sq
  have hp2 : 2 < p := by
    by_contra hc
    have h2 : p = 2 := by have := hp.two_le; omega
    subst h2
    rcases h_mod with h | h <;> norm_num [Int.ModEq] at h
  have hp5 : p ≠ 5 := by
    rintro rfl
    rcases h_mod with h | h <;> norm_num [Int.ModEq] at h
  have hmain := OMA.main_congr_c2 hp hp2 hp5 x y h_sq
  have hcast : (p : ℤ) ^ 2 = ((p ^ 2 : ℕ) : ℤ) := by push_cast; rfl
  rw [hcast]
  exact (ZMod.intCast_eq_intCast_iff _ _ _).mp hmain
