import OMAStatements.S_oeis_a363990
import Mathlib

/-!
# Peter Bala's A363990 supercongruence

The proof formalizes the four-binomial convolution approach from Blake Stone's
Supercongruences for Peter Bala's companion binomial sums. It uses exact formal
power series and coefficient extraction for the sequence identity, then proves
the prime-power congruence by splitting the integral convolution into index
classes. The arithmetic implementation adapts the checked Kazandzidis argument
from the related A363986 development in #34346.
-/

section

/-!
Arithmetic excerpt of Public34346.lean, OMA PR34346, DiscoCharlie/open-math-agents,
head 22dd6669aa8ac9cccf968efd096d475f9500cbfa, agent antigravity/Gemini4Neon.
Only general positive-top Kazandzidis arithmetic is retained; no m=2 sequence identity.
Original source and attribution remain in the adjacent Public34346.lean.
-/

namespace OeisA363986Part23
open Finset Polynomial

/-- `p^M` divides `q : ℚ` in `ℤ_{(p)}`, i.e., `q = p^M * a / b` with `0 < b` and `p ⊥ b`. -/
def pDvdRat (p M : ℕ) (q : ℚ) : Prop :=
  ∃ a : ℤ, ∃ b : ℕ, 0 < b ∧ Nat.Coprime p b ∧ q = (p : ℚ) ^ M * (a : ℚ) / (b : ℚ)

lemma pDvdRat_zero (p M : ℕ) : pDvdRat p M 0 :=
  ⟨0, 1, Nat.one_pos, Nat.coprime_one_right p, by simp⟩

lemma pDvdRat_mono {p M1 M2 : ℕ} {q : ℚ} (h : M1 ≤ M2) (hq : pDvdRat p M2 q) :
    pDvdRat p M1 q := by
  rcases hq with ⟨a, b, hb, hcop, rfl⟩
  refine ⟨(p : ℤ) ^ (M2 - M1) * a, b, hb, hcop, ?_⟩
  push_cast
  rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]

lemma pDvdRat_neg {p M : ℕ} {q : ℚ} (hq : pDvdRat p M q) : pDvdRat p M (-q) := by
  rcases hq with ⟨a, b, hb, hcop, rfl⟩
  exact ⟨-a, b, hb, hcop, by push_cast; ring⟩

lemma pDvdRat_add {p M : ℕ} {q1 q2 : ℚ} (h1 : pDvdRat p M q1) (h2 : pDvdRat p M q2) :
    pDvdRat p M (q1 + q2) := by
  rcases h1 with ⟨a1, b1, hb1, hc1, rfl⟩
  rcases h2 with ⟨a2, b2, hb2, hc2, rfl⟩
  refine ⟨a1 * b2 + a2 * b1, b1 * b2, Nat.mul_pos hb1 hb2, hc1.mul_right hc2, ?_⟩
  have hb1q : (b1 : ℚ) ≠ 0 := by positivity
  have hb2q : (b2 : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

lemma pDvdRat_sub {p M : ℕ} {q1 q2 : ℚ} (h1 : pDvdRat p M q1) (h2 : pDvdRat p M q2) :
    pDvdRat p M (q1 - q2) := by
  rw [sub_eq_add_neg]; exact pDvdRat_add h1 (pDvdRat_neg h2)

lemma pDvdRat_mul {p M1 M2 : ℕ} {q1 q2 : ℚ} (h1 : pDvdRat p M1 q1) (h2 : pDvdRat p M2 q2) :
    pDvdRat p (M1 + M2) (q1 * q2) := by
  rcases h1 with ⟨a1, b1, hb1, hc1, rfl⟩
  rcases h2 with ⟨a2, b2, hb2, hc2, rfl⟩
  refine ⟨a1 * a2, b1 * b2, Nat.mul_pos hb1 hb2, hc1.mul_right hc2, ?_⟩
  push_cast
  rw [pow_add]
  ring

lemma pDvdRat_pow {p M : ℕ} {q : ℚ} (hq : pDvdRat p M q) (k : ℕ) :
    pDvdRat p (k * M) (q ^ k) := by
  induction k with
  | zero => exact ⟨1, 1, Nat.one_pos, Nat.coprime_one_right p, by simp⟩
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact pDvdRat_mul ih hq

lemma pDvdRat_sum {ι : Type*} {s : Finset ι} {p M : ℕ} {f : ι → ℚ}
    (hf : ∀ i ∈ s, pDvdRat p M (f i)) : pDvdRat p M (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pDvdRat_zero p M
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact pDvdRat_add (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma pDvdRat_of_int {p M : ℕ} (z : ℤ) (hz : (p : ℤ) ^ M ∣ z) : pDvdRat p M (z : ℚ) := by
  rcases hz with ⟨a, rfl⟩
  exact ⟨a, 1, Nat.one_pos, Nat.coprime_one_right p, by push_cast; ring⟩

lemma pDvdRat_of_int_zero (p : ℕ) (z : ℤ) : pDvdRat p 0 (z : ℚ) :=
  pDvdRat_of_int z (by simp)

lemma pDvdRat_inv_nat {p d : ℕ} (hd : 0 < d) (hcop : Nat.Coprime p d) :
    pDvdRat p 0 ((d : ℚ)⁻¹) :=
  ⟨1, d, hd, hcop, by push_cast; rw [pow_zero, one_mul, one_div]⟩

lemma int_dvd_of_pDvdRat {p M : ℕ} {z : ℤ} (hz : pDvdRat p M (z : ℚ)) : (p : ℤ) ^ M ∣ z := by
  rcases hz with ⟨a, b, hb, hcop, heq⟩
  have hbq : (b : ℚ) ≠ 0 := by positivity
  have hmulq : (z : ℚ) * (b : ℚ) = (p : ℚ) ^ M * (a : ℚ) := by
    rw [heq, div_mul_cancel₀ _ hbq]
  have hmul : z * (b : ℤ) = (p : ℤ) ^ M * a := by exact_mod_cast hmulq
  have hdvd : (p : ℤ) ^ M ∣ (b : ℤ) * z := ⟨a, by linarith⟩
  have hcopZ : IsCoprime ((p : ℤ) ^ M) (b : ℤ) :=
    (Nat.isCoprime_iff_coprime.mpr hcop).pow_left
  exact hcopZ.dvd_of_dvd_mul_left hdvd

lemma pDvdRat_div_nat {p M d E : ℕ} (hp : p.Prime) (hd : 0 < d)
    (hvp : padicValNat p d ≤ E) (hEM : E ≤ M) {q : ℚ} (hq : pDvdRat p M q) :
    pDvdRat p (M - E) (q / (d : ℚ)) := by
  have : Fact p.Prime := ⟨hp⟩
  rcases hq with ⟨a, b, hb, hcop, rfl⟩
  set v := padicValNat p d
  obtain ⟨d', hd'⟩ := pow_padicValNat_dvd (p := p) (n := d)
  have hd'_pos : 0 < d' := by
    rcases Nat.eq_zero_or_pos d' with rfl | hpos
    · simp at hd'; omega
    · exact hpos
  have hcop_d' : Nat.Coprime p d' := by
    rw [hp.coprime_iff_not_dvd]
    intro hpd'
    rcases hpd' with ⟨t, rfl⟩
    have h1 : p ^ (v + 1) ∣ d := ⟨t, by rw [hd', pow_succ]; ring⟩
    have h2 : v + 1 ≤ padicValNat p d := (padicValNat_dvd_iff_le (by omega)).mp h1
    omega
  refine ⟨(p : ℤ) ^ (E - v) * a, b * d', Nat.mul_pos hb hd'_pos, hcop.mul_right hcop_d', ?_⟩
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hd_cast : (d : ℚ) = (p : ℚ) ^ v * (d' : ℚ) := by exact_mod_cast hd'
  rw [hd_cast]
  have hexp : M = (M - E) + (E - v) + v := by omega
  push_cast
  calc (p : ℚ) ^ M * (a : ℚ) / (b : ℚ) / ((p : ℚ) ^ v * (d' : ℚ))
      = (p : ℚ) ^ ((M - E) + (E - v) + v) * (a : ℚ) / ((b : ℚ) * (d' : ℚ) * (p : ℚ) ^ v) := by
          rw [← hexp]; ring
    _ = ((p : ℚ) ^ (M - E) * ((p : ℚ) ^ (E - v) * (a : ℚ)) / ((b : ℚ) * (d' : ℚ))) *
        ((p : ℚ) ^ v / (p : ℚ) ^ v) := by rw [pow_add, pow_add]; ring
    _ = (p : ℚ) ^ (M - E) * ((p : ℚ) ^ (E - v) * (a : ℚ)) / ((b : ℚ) * (d' : ℚ)) := by
        rw [div_self (pow_ne_zero v hpq), mul_one]

/-- For `p ≥ 5` prime and `k ≥ 1`, `4 * padicValNat p k ≤ k - 1`. -/
lemma four_mul_padicValNat_le {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 1 ≤ k) :
    4 * padicValNat p k ≤ k - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  set v := padicValNat p k
  have hle : p ^ v ≤ k := Nat.le_of_dvd hk pow_padicValNat_dvd
  have h5v : 5 ^ v ≤ p ^ v := Nat.pow_le_pow_left hp5 v
  have hlin : 4 * v + 1 ≤ 5 ^ v := by
    induction v with
    | zero => norm_num
    | succ v ih =>
      rw [pow_succ]
      omega
  omega

/-- For `p ≥ 5` prime and `m : ℕ`, `4 * padicValNat p m.factorial ≤ m`. -/
lemma four_mul_padicValNat_factorial_le {p m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    4 * padicValNat p m.factorial ≤ m := by
  have : Fact p.Prime := ⟨hp⟩
  have h := sub_one_mul_padicValNat_factorial (p := p) m
  have h4 : 4 ≤ p - 1 := by omega
  calc 4 * padicValNat p m.factorial
      ≤ (p - 1) * padicValNat p m.factorial := Nat.mul_le_mul_right _ h4
    _ = m - (p.digits m).sum := h
    _ ≤ m := Nat.sub_le _ _

/-- Truncated logarithm `∑_{k=1}^M (-1)^{k-1} u^k / k`. -/
def truncLog (M : ℕ) (u : ℚ) : ℚ :=
  ∑ k ∈ Icc 1 M, (-1 : ℚ) ^ (k - 1) * u ^ k / (k : ℚ)

lemma poly_coeff_pDvdRat_mul {p : ℕ} {P Q : ℚ[X]}
    (hP : ∀ i, pDvdRat p (2 * i) (P.coeff i))
    (hQ : ∀ i, pDvdRat p (2 * i) (Q.coeff i)) :
    ∀ j, pDvdRat p (2 * j) ((P * Q).coeff j) := by
  intro j
  rw [Polynomial.coeff_mul]
  refine pDvdRat_sum (fun x hx => ?_)
  have hsum : x.1 + x.2 = j := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have hm := pDvdRat_mul (hP x.1) (hQ x.2)
  rwa [show 2 * x.1 + 2 * x.2 = 2 * j by omega] at hm

lemma poly_coeff_pDvdRat_pow {p : ℕ} {P : ℚ[X]}
    (hP : ∀ i, pDvdRat p (2 * i) (P.coeff i)) (k : ℕ) :
    ∀ j, pDvdRat p (2 * j) ((P ^ k).coeff j) := by
  induction k with
  | zero =>
    intro j
    rcases j with _ | j
    · simp; exact pDvdRat_of_int_zero p 1
    · rw [pow_zero, Polynomial.coeff_one]; simp [pDvdRat_zero]
  | succ k ih =>
    rw [pow_succ]
    exact poly_coeff_pDvdRat_mul ih hP

lemma coeff_zero_of_mul_unit_const {H P : ℚ[X]} (hH0 : H.coeff 0 = 1) (M : ℕ)
    (hHP : ∀ j < M, (H * P).coeff j = 0) : ∀ j < M, P.coeff j = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    have h0 := hHP j hj
    rw [Polynomial.coeff_mul] at h0
    have hsplit : ∑ x ∈ Finset.HasAntidiagonal.antidiagonal j, H.coeff x.1 * P.coeff x.2 =
        H.coeff 0 * P.coeff j := by
      rw [Finset.sum_eq_single (0, j)]
      · intro x hx hne
        have hsum : x.1 + x.2 = j := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
        have hlt : x.2 < j := by
          by_contra hge
          have h2 : x.2 = j := by omega
          have h1 : x.1 = 0 := by omega
          exact hne (Prod.ext h1 h2)
        rw [ih x.2 hlt (lt_trans hlt hj), mul_zero]
      · intro hnot
        exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega)) hnot
    rw [hsplit, hH0, one_mul] at h0
    exact h0

lemma natDegree_finset_sum_le {ι R : Type*} [Semiring R] (s : Finset ι) (f : ι → R[X]) (d : ℕ)
    (hf : ∀ i ∈ s, (f i).natDegree ≤ d) : (∑ i ∈ s, f i).natDegree ≤ d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (natDegree_add_le _ _).trans
      (max_le (hf a (Finset.mem_insert_self a s)) (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))))

lemma nat_coprime_prod_right {ι : Type*} {s : Finset ι} {p : ℕ} {f : ι → ℕ}
    (hf : ∀ i ∈ s, Nat.Coprime p (f i)) : Nat.Coprime p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul_right
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma truncLog_mul {p M : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {u v : ℚ}
    (hu : pDvdRat p 2 u) (hv : pDvdRat p 2 v) :
    pDvdRat p M (truncLog M (u + v + u * v) - truncLog M u - truncLog M v) := by
  let A : ℚ[X] := C (u + v) * X + C (u * v) * X ^ 2
  let Bu : ℚ[X] := C u * X
  let Bv : ℚ[X] := C v * X
  let G : ℚ[X] := ∑ k ∈ Icc 1 M,
    C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * (A ^ k - Bu ^ k - Bv ^ k)
  have hGeval1 : G.eval 1 = truncLog M (u + v + u * v) - truncLog M u - truncLog M v := by
    simp only [G, truncLog, eval_finsetSum, eval_mul, eval_C, eval_sub, eval_pow, A, Bu, Bv,
      eval_add, eval_X, one_pow, mul_one]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have hG0 : G.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    dsimp only [G]
    rw [Polynomial.eval_finsetSum]
    refine Finset.sum_eq_zero (fun k hk => ?_)
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hne : k ≠ 0 := by omega
    simp [A, Bu, Bv, zero_pow hne]
  -- Derivative identity: (1 + Bu) * (1 + Bv) * G.derivative is divisible by X^M!
  have hderiv_pow : ∀ (P : ℚ[X]),
      (1 + P) * (∑ k ∈ Icc 1 M, C ((-1 : ℚ) ^ (k - 1)) * P ^ (k - 1) * P.derivative) =
        P.derivative * (1 - (-P) ^ M) := by
    intro P
    have hsum : (1 + P) * (∑ k ∈ Icc 1 M, (-P) ^ (k - 1)) = 1 - (-P) ^ M := by
      have hgeom := geom_sum_mul (-P) M
      have hre : ∑ k ∈ Icc 1 M, (-P) ^ (k - 1) = ∑ i ∈ range M, (-P) ^ i := by
        refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
        · intro k hk; simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢; omega
        · intro k1 hk1 k2 hk2 h; simp only [Finset.mem_Icc] at hk1 hk2; omega
        · intro i hi; exact ⟨i + 1, Finset.mem_Icc.mpr ⟨by omega, by rw [Finset.mem_range] at hi; omega⟩, by omega⟩
        · intro k _; rfl
      rw [hre]
      linear_combination -hgeom
    have hrew : ∑ k ∈ Icc 1 M, C ((-1 : ℚ) ^ (k - 1)) * P ^ (k - 1) * P.derivative =
        (∑ k ∈ Icc 1 M, (-P) ^ (k - 1)) * P.derivative := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have hc : C ((-1 : ℚ) ^ (k - 1)) * P ^ (k - 1) = (-P) ^ (k - 1) := by
        rw [map_pow, map_neg, map_one, ← mul_pow]; simp
      rw [hc]
    rw [hrew, ← mul_assoc, hsum]
    ring
  have hGderiv : G.derivative =
      (∑ k ∈ Icc 1 M, C ((-1 : ℚ) ^ (k - 1)) * A ^ (k - 1) * A.derivative) -
      (∑ k ∈ Icc 1 M, C ((-1 : ℚ) ^ (k - 1)) * Bu ^ (k - 1) * Bu.derivative) -
      (∑ k ∈ Icc 1 M, C ((-1 : ℚ) ^ (k - 1)) * Bv ^ (k - 1) * Bv.derivative) := by
    simp only [G, derivative_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkq : (k : ℚ) ≠ 0 := by positivity
    rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_sub, derivative_sub,
      derivative_pow, derivative_pow, derivative_pow]
    have hcancel : C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * (k : ℚ[X]) = C ((-1 : ℚ) ^ (k - 1)) := by
      rw [← map_natCast C, ← map_mul, div_mul_cancel₀ _ hkq]
    calc C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) *
          ((k : ℚ[X]) * A ^ (k - 1) * A.derivative -
           (k : ℚ[X]) * Bu ^ (k - 1) * Bu.derivative -
           (k : ℚ[X]) * Bv ^ (k - 1) * Bv.derivative)
        = (C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * (k : ℚ[X])) * A ^ (k - 1) * A.derivative -
          (C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * (k : ℚ[X])) * Bu ^ (k - 1) * Bu.derivative -
          (C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * (k : ℚ[X])) * Bv ^ (k - 1) * Bv.derivative := by ring
      _ = C ((-1 : ℚ) ^ (k - 1)) * A ^ (k - 1) * A.derivative -
          C ((-1 : ℚ) ^ (k - 1)) * Bu ^ (k - 1) * Bu.derivative -
          C ((-1 : ℚ) ^ (k - 1)) * Bv ^ (k - 1) * Bv.derivative := by rw [hcancel]
  have h1A : 1 + A = (1 + Bu) * (1 + Bv) := by
    simp only [A, Bu, Bv, map_add, map_mul]; ring
  have hAderiv : A.derivative = Bu.derivative * (1 + Bv) + Bv.derivative * (1 + Bu) := by
    simp only [A, Bu, Bv, derivative_mul, derivative_C, derivative_X,
      derivative_pow, map_add, map_mul, map_natCast]
    ring
  have hH_mul : ((1 + Bu) * (1 + Bv)) * G.derivative =
      -(A.derivative * (-A) ^ M) + (1 + Bv) * (Bu.derivative * (-Bu) ^ M) +
      (1 + Bu) * (Bv.derivative * (-Bv) ^ M) := by
    rw [hGderiv, mul_sub, mul_sub]
    have t1 : (1 + Bu) * (1 + Bv) *
        (∑ k ∈ Icc 1 M, C ((-1 : ℚ) ^ (k - 1)) * A ^ (k - 1) * A.derivative) =
        A.derivative * (1 - (-A) ^ M) := by rw [← h1A, hderiv_pow A]
    have t2 : (1 + Bu) * (1 + Bv) *
        (∑ k ∈ Icc 1 M, C ((-1 : ℚ) ^ (k - 1)) * Bu ^ (k - 1) * Bu.derivative) =
        (1 + Bv) * (Bu.derivative * (1 - (-Bu) ^ M)) := by
      rw [mul_comm (1 + Bu) (1 + Bv), mul_assoc, hderiv_pow Bu]
    have t3 : (1 + Bu) * (1 + Bv) *
        (∑ k ∈ Icc 1 M, C ((-1 : ℚ) ^ (k - 1)) * Bv ^ (k - 1) * Bv.derivative) =
        (1 + Bu) * (Bv.derivative * (1 - (-Bv) ^ M)) := by
      rw [mul_assoc, hderiv_pow Bv]
    rw [t1, t2, t3, hAderiv]
    ring
  have hXdvd_A : X ∣ A := ⟨C (u + v) + C (u * v) * X, by simp only [A]; ring⟩
  have hXdvd_Bu : X ∣ Bu := ⟨C u, by simp only [Bu]; ring⟩
  have hXdvd_Bv : X ∣ Bv := ⟨C v, by simp only [Bv]; ring⟩
  have hXM_dvd : X ^ M ∣ ((1 + Bu) * (1 + Bv)) * G.derivative := by
    rw [hH_mul]
    have d1 : X ^ M ∣ (-A) ^ M := pow_dvd_pow_of_dvd (dvd_neg.mpr hXdvd_A) M
    have d2 : X ^ M ∣ (-Bu) ^ M := pow_dvd_pow_of_dvd (dvd_neg.mpr hXdvd_Bu) M
    have d3 : X ^ M ∣ (-Bv) ^ M := pow_dvd_pow_of_dvd (dvd_neg.mpr hXdvd_Bv) M
    exact dvd_add (dvd_add (dvd_neg.mpr (dvd_mul_of_dvd_right d1 _))
      (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right d2 _) _))
      (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right d3 _) _)
  have hH0 : ((1 + Bu) * (1 + Bv)).coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]; simp [Bu, Bv]
  have hGd_zero : ∀ j < M, G.derivative.coeff j = 0 := by
    refine coeff_zero_of_mul_unit_const hH0 M (fun j hj => ?_)
    rcases hXM_dvd with ⟨Q, hQ⟩
    rw [hQ, coeff_X_pow_mul']
    simp [Nat.not_le.mpr hj]
  have hG_coeff_zero : ∀ j ≤ M, G.coeff j = 0 := by
    intro j hj
    rcases j with _ | j
    · exact hG0
    · have h1 := hGd_zero j (by omega)
      rw [coeff_derivative] at h1
      have hne : ((j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      exact (mul_eq_zero.mp h1).resolve_right (by push_cast at hne ⊢; exact hne)
  have hGdeg : G.natDegree ≤ 2 * M := by
    have hdegA : A.natDegree ≤ 2 := by
      calc A.natDegree ≤ max (C (u + v) * X).natDegree (C (u * v) * X ^ 2).natDegree := natDegree_add_le _ _
        _ ≤ max (0 + 1) (0 + 2) := by
          gcongr
          · exact natDegree_C_mul_le _ _ |>.trans (by simp)
          · exact natDegree_C_mul_le _ _ |>.trans (by simp)
        _ = 2 := by norm_num
    have hdegBu : Bu.natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans (by simp)
    have hdegBv : Bv.natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans (by simp)
    refine natDegree_finset_sum_le (Icc 1 M) _ (2 * M) (fun k hk => ?_)
    have hkM : k ≤ M := (Finset.mem_Icc.mp hk).2
    refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le ?_ ?_)) ?_)
    · exact (natDegree_pow_le).trans (by nlinarith)
    · exact (natDegree_pow_le).trans (by nlinarith)
    · exact (natDegree_pow_le).trans (by nlinarith)
  rw [← hGeval1, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hGdeg)]
  simp only [one_pow, mul_one]
  refine pDvdRat_sum (fun j hj => ?_)
  by_cases hjM : j ≤ M
  · rw [hG_coeff_zero j hjM]; exact pDvdRat_zero p M
  · have hjgt : M < j := Nat.lt_of_not_ge hjM
    simp only [G, finsetSum_coeff, coeff_C_mul, coeff_sub]
    refine pDvdRat_sum (fun k hk => ?_)
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkM : k ≤ M := (Finset.mem_Icc.mp hk).2
    have hBu0 : (Bu ^ k).coeff j = 0 := by
      have hdeg : (Bu ^ k).natDegree ≤ k :=
        (natDegree_pow_le).trans (by have : Bu.natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans (by simp); nlinarith)
      exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (lt_of_le_of_lt hkM hjgt))
    have hBv0 : (Bv ^ k).coeff j = 0 := by
      have hdeg : (Bv ^ k).natDegree ≤ k :=
        (natDegree_pow_le).trans (by have : Bv.natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans (by simp); nlinarith)
      exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (lt_of_le_of_lt hkM hjgt))
    rw [hBu0, hBv0, sub_zero, sub_zero]
    have hAcoeff : ∀ i, pDvdRat p (2 * i) (A.coeff i) := by
      intro i
      rcases i with _ | _ | _ | i
      · have : A.coeff 0 = 0 := by simp [A]
        rw [this]; exact pDvdRat_zero p 0
      · have : A.coeff 1 = u + v := by
          simp only [A, coeff_add, coeff_C_mul, coeff_X_one, coeff_X_pow]
          norm_num
        rw [this]; exact pDvdRat_add hu hv
      · have : A.coeff 2 = u * v := by
          simp only [A, coeff_add, coeff_C_mul, coeff_X, coeff_X_pow]
          norm_num
        rw [this]; exact pDvdRat_mul hu hv
      · have hdeg : A.natDegree ≤ 2 := by
          calc A.natDegree ≤ max (C (u + v) * X).natDegree (C (u * v) * X ^ 2).natDegree := natDegree_add_le _ _
            _ ≤ max 1 2 := max_le_max ((natDegree_C_mul_le _ _).trans (by simp)) ((natDegree_C_mul_le _ _).trans (by simp))
            _ = 2 := by norm_num
        rw [coeff_eq_zero_of_natDegree_lt (by omega)]; exact pDvdRat_zero p _
    have hAkj : pDvdRat p (2 * j) ((A ^ k).coeff j) := poly_coeff_pDvdRat_pow hAcoeff k j
    have hvp : padicValNat p k ≤ j := by
      have h4 := four_mul_padicValNat_le hp hp5 hk1
      omega
    have hdiv := pDvdRat_div_nat hp (by omega : 0 < k) hvp (by omega : j ≤ 0 + 2 * j)
      (pDvdRat_mul (pDvdRat_of_int_zero p ((-1 : ℤ) ^ (k - 1))) hAkj)
    have hrew : ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * (A ^ k).coeff j =
        ((((-1 : ℤ) ^ (k - 1) : ℤ) : ℚ) * (A ^ k).coeff j) / (k : ℚ) := by push_cast; ring
    rw [hrew]
    exact pDvdRat_mono (by omega : M ≤ 0 + 2 * j - j) hdiv

lemma truncLog_prod {ι : Type*} (s : Finset ι) {p M : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (u : ι → ℚ) (hu : ∀ i ∈ s, pDvdRat p 2 (u i)) :
    pDvdRat p 2 ((∏ i ∈ s, (1 + u i)) - 1) ∧
    pDvdRat p M (truncLog M ((∏ i ∈ s, (1 + u i)) - 1) - ∑ i ∈ s, truncLog M (u i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using pDvdRat_zero p 2, ?_⟩
    simp only [Finset.prod_empty, sub_self, Finset.sum_empty, sub_zero]
    have h0 : truncLog M 0 = 0 := by
      refine Finset.sum_eq_zero (fun k hk => ?_)
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      rw [zero_pow (by omega : k ≠ 0), mul_zero, zero_div]
    rw [h0]; exact pDvdRat_zero p M
  | insert a s ha ih =>
    have hua : pDvdRat p 2 (u a) := hu a (Finset.mem_insert_self a s)
    obtain ⟨hP2, hPlog⟩ := ih (fun i hi => hu i (Finset.mem_insert_of_mem hi))
    set v := (∏ i ∈ s, (1 + u i)) - 1
    have hprod : (∏ i ∈ insert a s, (1 + u i)) - 1 = u a + v + u a * v := by
      rw [Finset.prod_insert ha]
      have : ∏ i ∈ s, (1 + u i) = 1 + v := by simp [v]
      rw [this]; ring
    rw [hprod, Finset.sum_insert ha]
    refine ⟨pDvdRat_add (pDvdRat_add hua hP2) (pDvdRat_mono (by omega : 2 ≤ 2 + 2) (pDvdRat_mul hua hP2)), ?_⟩
    have hstep := truncLog_mul (M := M) hp hp5 hua hP2
    have hcomb := pDvdRat_add hstep hPlog
    convert hcomb using 1
    ring

lemma truncLog_inj {p M : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {w : ℚ}
    (hw2 : pDvdRat p 2 w) (hlog : pDvdRat p M (truncLog M w)) : pDvdRat p M w := by
  by_cases hM2 : M ≤ 2
  · exact pDvdRat_mono hM2 hw2
  · have hstep : ∀ t : ℕ, 2 ≤ t → t ≤ M → pDvdRat p t w := by
      intro t ht2 htM
      induction t with
      | zero => omega
      | succ t ih =>
        by_cases h2 : t + 1 ≤ 2
        · exact pDvdRat_mono h2 hw2
        · have ht : pDvdRat p t w := ih (by omega) (by omega)
          have hlog' : pDvdRat p (t + 1) (truncLog M w) := pDvdRat_mono htM hlog
          have htail : pDvdRat p (t + 1) (∑ k ∈ Icc 2 M, (-1 : ℚ) ^ (k - 1) * w ^ k / (k : ℚ)) := by
            refine pDvdRat_sum (fun k hk => ?_)
            have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
            have hwk : pDvdRat p (k * t) (w ^ k) := pDvdRat_pow ht k
            have hvp : padicValNat p k ≤ k - 1 := by
              have h4 := four_mul_padicValNat_le hp hp5 (by omega : 1 ≤ k)
              omega
            have ht_ge2 : 2 ≤ t := by omega
            have hkt : k + t ≤ k * t := by nlinarith
            have hdiv := pDvdRat_div_nat hp (by omega : 0 < k) hvp (by omega : k - 1 ≤ 0 + k * t)
              (pDvdRat_mul (pDvdRat_of_int_zero p ((-1 : ℤ) ^ (k - 1))) hwk)
            have hrew : (-1 : ℚ) ^ (k - 1) * w ^ k / (k : ℚ) =
                ((((-1 : ℤ) ^ (k - 1) : ℤ) : ℚ) * w ^ k) / (k : ℚ) := by push_cast; ring
            rw [hrew]
            exact pDvdRat_mono (by omega : t + 1 ≤ 0 + k * t - (k - 1)) hdiv
          have hsplit : truncLog M w = w + ∑ k ∈ Icc 2 M, (-1 : ℚ) ^ (k - 1) * w ^ k / (k : ℚ) := by
            unfold truncLog
            have hIcc : Icc 1 M = insert 1 (Icc 2 M) := by
              ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            rw [hIcc, Finset.sum_insert (by simp)]
            simp
          have hw_eq : w = truncLog M w - ∑ k ∈ Icc 2 M, (-1 : ℚ) ^ (k - 1) * w ^ k / (k : ℚ) := by
            linarith
          rw [hw_eq]
          exact pDvdRat_sub hlog' htail
    exact hstep M (by omega) le_rfl

/-- Integer-scaled Faulhaber polynomial: `(faulhaberInt d).eval (B : ℤ) = (d+1)! * ∑_{j<B} j^d`. -/
noncomputable def faulhaberInt : ℕ → ℤ[X]
  | 0 => X
  | d + 1 =>
    C ((d + 1).factorial : ℤ) * X ^ (d + 2) -
    ∑ m ∈ (range (d + 1)).attach,
      C (((d + 2).choose m.1 * ((d + 1).factorial / (m.1 + 1).factorial) : ℕ) : ℤ) *
        faulhaberInt m.1
termination_by d => d
decreasing_by
  exact Finset.mem_range.mp m.2

lemma faulhaberInt_eval (d B : ℕ) :
    (faulhaberInt d).eval (B : ℤ) = ((d + 1).factorial : ℤ) * ∑ j ∈ range B, (j : ℤ) ^ d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    rcases d with _ | d
    · simp [faulhaberInt]
    · rw [faulhaberInt]
      simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_finsetSum]
      have htel : (B : ℤ) ^ (d + 2) = ∑ j ∈ range B, ((j + 1 : ℤ) ^ (d + 2) - (j : ℤ) ^ (d + 2)) := by
        have hgen : ∀ B' : ℕ, (B' : ℤ) ^ (d + 2) =
            ∑ j ∈ range B', ((j + 1 : ℤ) ^ (d + 2) - (j : ℤ) ^ (d + 2)) := by
          intro B'
          induction B' with
          | zero => simp
          | succ B' ihB =>
            rw [Finset.sum_range_succ, ← ihB]
            push_cast; ring
        exact hgen B
      have hexp : ∀ j : ℕ, (j + 1 : ℤ) ^ (d + 2) - (j : ℤ) ^ (d + 2) =
          ((d + 2 : ℕ) : ℤ) * (j : ℤ) ^ (d + 1) +
          ∑ m ∈ range (d + 1), ((d + 2).choose m : ℤ) * (j : ℤ) ^ m := by
        intro j
        rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ]
        simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one]
        have hch : (d + 2).choose (d + 1) = d + 2 := by
          rw [← Nat.choose_symm (by omega : d + 1 ≤ d + 2)]
          simp
        rw [hch]; ring
      have hsum_tel : (B : ℤ) ^ (d + 2) =
          ((d + 2 : ℕ) : ℤ) * (∑ j ∈ range B, (j : ℤ) ^ (d + 1)) +
          ∑ m ∈ range (d + 1), ((d + 2).choose m : ℤ) * (∑ j ∈ range B, (j : ℤ) ^ m) := by
        rw [htel, Finset.sum_congr rfl (fun j _ => hexp j), Finset.sum_add_distrib,
          ← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [← Finset.mul_sum]
      have hmul_tel := congrArg (fun z : ℤ => ((d + 1).factorial : ℤ) * z) hsum_tel
      have hfac : ((d + 1).factorial : ℤ) * ((d + 2 : ℕ) : ℤ) = ((d + 2).factorial : ℤ) := by
        have hnat : (d + 2).factorial = (d + 2) * (d + 1).factorial := Nat.factorial_succ (d + 1)
        rw [hnat]
        push_cast; ring
      rw [mul_add, ← mul_assoc, hfac] at hmul_tel
      have hmul_rhs : ((d + 1).factorial : ℤ) *
          ∑ m ∈ range (d + 1), ((d + 2).choose m : ℤ) * ∑ j ∈ range B, (j : ℤ) ^ m =
          ∑ m ∈ range (d + 1), ((d + 1).factorial : ℤ) *
            (((d + 2).choose m : ℤ) * ∑ j ∈ range B, (j : ℤ) ^ m) :=
        Finset.mul_sum _ _ _
      rw [hmul_rhs] at hmul_tel
      have hih_sum : ∑ m ∈ (range (d + 1)).attach,
          (((d + 2).choose m.1 * ((d + 1).factorial / (m.1 + 1).factorial) : ℕ) : ℤ) *
            (faulhaberInt m.1).eval (B : ℤ) =
          ∑ m ∈ range (d + 1), ((d + 1).factorial : ℤ) *
            (((d + 2).choose m : ℤ) * ∑ j ∈ range B, (j : ℤ) ^ m) := by
        have hstep : ∑ m ∈ (range (d + 1)).attach,
            (((d + 2).choose m.1 * ((d + 1).factorial / (m.1 + 1).factorial) : ℕ) : ℤ) *
              (faulhaberInt m.1).eval (B : ℤ) =
            ∑ m ∈ (range (d + 1)).attach, ((d + 1).factorial : ℤ) *
              (((d + 2).choose m.1 : ℤ) * ∑ j ∈ range B, (j : ℤ) ^ m.1) := by
          refine Finset.sum_congr rfl (fun m _ => ?_)
          have hmd : m.1 < d + 1 := Finset.mem_range.mp m.2
          rw [ih m.1 hmd]
          have hdvd : (m.1 + 1).factorial ∣ (d + 1).factorial := Nat.factorial_dvd_factorial (by omega)
          have hdiv : ((d + 1).factorial / (m.1 + 1).factorial : ℕ) * (m.1 + 1).factorial = (d + 1).factorial :=
            Nat.div_mul_cancel hdvd
          have hdivZ : (((d + 1).factorial / (m.1 + 1).factorial : ℕ) : ℤ) * ((m.1 + 1).factorial : ℤ) =
              ((d + 1).factorial : ℤ) := by exact_mod_cast hdiv
          rw [Nat.cast_mul]
          linear_combination ((d + 2).choose m.1 : ℤ) * (∑ j ∈ range B, (j : ℤ) ^ m.1) * hdivZ
        rw [hstep, Finset.sum_attach (range (d + 1)) (fun m =>
          ((d + 1).factorial : ℤ) * (((d + 2).choose m : ℤ) * ∑ j ∈ range B, (j : ℤ) ^ m))]
      rw [hih_sum]
      linarith

lemma faulhaberInt_eval_zero (d : ℕ) : (faulhaberInt d).eval 0 = 0 := by
  have := faulhaberInt_eval d 0
  simpa using this

/-- Power-sum divisibility: `B * D * (B + D)` divides `(2k+1)! * S_k(B, D)` in `ℤ`. -/
lemma power_sum_dvd (k B D : ℕ) :
    ((B * D * (B + D) : ℕ) : ℤ) ∣
      ((2 * k + 1).factorial : ℤ) *
        ∑ j ∈ range B, ((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ k -
                        ((j : ℤ) * ((j : ℤ) + 1)) ^ k) := by
  -- Inner polynomial ring `ℤ[X]` represents variable `B`; outer `Polynomial (ℤ[X])` represents `D`.
  -- Auxiliary `Q : Polynomial (ℤ[X])` where inner `ℤ[X]` is `D` and outer `X` is `j`:
  let Q : Polynomial (ℤ[X]) :=
    ((C (X : ℤ[X]) + X) * (C (X : ℤ[X]) + X + 1)) ^ k - (X * (X + 1)) ^ k
  have hQdeg : Q.natDegree ≤ 2 * k := by
    have hd1 : ((C (X : ℤ[X]) + X) * (C (X : ℤ[X]) + X + 1)).natDegree ≤ 2 := by
      have h1 : (C (X : ℤ[X]) + X).natDegree ≤ 1 :=
        (natDegree_add_le _ _).trans (max_le (by simp) (by simp))
      have h2 : (C (X : ℤ[X]) + X + 1).natDegree ≤ 1 :=
        (natDegree_add_le _ _).trans (max_le h1 (by simp))
      exact natDegree_mul_le.trans (by omega)
    have hd2 : ((X : Polynomial (ℤ[X])) * (X + 1)).natDegree ≤ 2 := by
      have hX : (X : Polynomial (ℤ[X])).natDegree ≤ 1 := natDegree_X_le
      have h1 : ((X : Polynomial (ℤ[X])) + 1).natDegree ≤ 1 :=
        (natDegree_add_le _ _).trans (max_le hX (by simp))
      exact natDegree_mul_le.trans (by omega)
    exact (natDegree_sub_le _ _).trans (max_le (natDegree_pow_le.trans (by nlinarith))
      (natDegree_pow_le.trans (by nlinarith)))
  let Fsc : ℕ → ℤ[X] := fun m =>
    C (((2 * k + 1).factorial / (m + 1).factorial : ℕ) : ℤ) * faulhaberInt m
  let P_BD : Polynomial (ℤ[X]) :=
    ∑ m ∈ range (2 * k + 1), (Q.coeff m).map C * C (Fsc m)
  have hFsc_eval : ∀ m ∈ range (2 * k + 1), ∀ b : ℕ,
      (Fsc m).eval (b : ℤ) = ((2 * k + 1).factorial : ℤ) * ∑ j ∈ range b, (j : ℤ) ^ m := by
    intro m hm b
    have hmk : m ≤ 2 * k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    simp only [Fsc, eval_mul, eval_C, faulhaberInt_eval]
    have hdvd : (m + 1).factorial ∣ (2 * k + 1).factorial := Nat.factorial_dvd_factorial (by omega)
    have hdiv : ((2 * k + 1).factorial / (m + 1).factorial : ℕ) * (m + 1).factorial =
        (2 * k + 1).factorial := Nat.div_mul_cancel hdvd
    have hdivZ : (((2 * k + 1).factorial / (m + 1).factorial : ℕ) : ℤ) * ((m + 1).factorial : ℤ) =
        ((2 * k + 1).factorial : ℤ) := by exact_mod_cast hdiv
    rw [← mul_assoc, hdivZ]
  have hP_eval : ∀ (b : ℕ) (d : ℤ),
      (P_BD.eval (C d)).eval (b : ℤ) =
        ((2 * k + 1).factorial : ℤ) *
          ∑ j ∈ range b, (((d + (j : ℤ)) * (d + (j : ℤ) + 1)) ^ k - ((j : ℤ) * ((j : ℤ) + 1)) ^ k) := by
    intro b d
    have hmap_eval : ∀ (f : ℤ[X]), (f.map (C : ℤ →+* ℤ[X])).eval (C d) = C (f.eval d) := by
      intro f
      induction f using Polynomial.induction_on' with
      | add p q ihp ihq => rw [Polynomial.map_add, eval_add, ihp, ihq, eval_add, map_add]
      | monomial m c => simp
    have hlhs : (P_BD.eval (C d)).eval (b : ℤ) =
        ∑ m ∈ range (2 * k + 1), (Q.coeff m).eval d * (Fsc m).eval (b : ℤ) := by
      simp only [P_BD, eval_finsetSum, eval_mul, eval_C, hmap_eval]
    rw [hlhs]
    have h2 : ∑ m ∈ range (2 * k + 1), (Q.coeff m).eval d * (Fsc m).eval (b : ℤ) =
        ((2 * k + 1).factorial : ℤ) *
          ∑ j ∈ range b, ∑ m ∈ range (2 * k + 1), (Q.coeff m).eval d * (j : ℤ) ^ m := by
      rw [Finset.mul_sum]
      have hinner : ∑ j ∈ range b, ((2 * k + 1).factorial : ℤ) *
          ∑ m ∈ range (2 * k + 1), (Q.coeff m).eval d * (j : ℤ) ^ m =
          ∑ j ∈ range b, ∑ m ∈ range (2 * k + 1),
            ((2 * k + 1).factorial : ℤ) * ((Q.coeff m).eval d * (j : ℤ) ^ m) :=
        Finset.sum_congr rfl (fun j _ => Finset.mul_sum _ _ _)
      rw [hinner, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [hFsc_eval m hm b, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => by ring)
    rw [h2]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hdeg_map : (Q.map (evalRingHom d)).natDegree ≤ 2 * k :=
      natDegree_map_le.trans hQdeg
    have hq_sum : ∑ m ∈ range (2 * k + 1), (Q.coeff m).eval d * (j : ℤ) ^ m =
        (Q.map (evalRingHom d)).eval (j : ℤ) := by
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg_map)]
      refine Finset.sum_congr rfl (fun m _ => by
        rw [coeff_map]; rfl)
    rw [hq_sum]
    simp only [Q, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_add,
      Polynomial.map_C, Polynomial.map_X, Polynomial.map_one, eval_sub, eval_pow, eval_mul,
      eval_add, eval_C, eval_X, eval_one]
    change (((X : ℤ[X]).eval d + (j : ℤ)) * ((X : ℤ[X]).eval d + (j : ℤ) + 1)) ^ k -
        ((j : ℤ) * ((j : ℤ) + 1)) ^ k = _
    simp
  -- Factor 1: X ∣ P_BD (since P_BD.eval 0 = 0)
  have hzero_of_nat : ∀ f : ℤ[X], (∀ b : ℕ, 1 ≤ b → f.eval (b : ℤ) = 0) → f = 0 := by
    intro f hf
    by_contra hne
    have hsub : (range (f.natDegree + 1)).image (fun b : ℕ => ((b + 1 : ℕ) : ℤ)) ⊆ f.roots.toFinset := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨b, _, rfl⟩
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
      exact hf (b + 1) (by omega)
    have hinj : Function.Injective (fun b : ℕ => ((b + 1 : ℕ) : ℤ)) := fun a b h => by
      have := Int.ofNat.inj h; omega
    have hcard1 : ((range (f.natDegree + 1)).image (fun b : ℕ => ((b + 1 : ℕ) : ℤ))).card = f.natDegree + 1 := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
    have hcard2 : f.roots.toFinset.card ≤ f.natDegree :=
      (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' f)
    have := Finset.card_le_card hsub
    omega
  have hP_eval0 : P_BD.eval 0 = 0 := by
    apply hzero_of_nat
    intro b _
    simpa using hP_eval b 0
  obtain ⟨P1, hP1⟩ : X ∣ P_BD := by
    rw [show (X : Polynomial (ℤ[X])) = X - C 0 by simp, Polynomial.dvd_iff_isRoot]
    exact hP_eval0
  -- Factor 2: (X + C X) ∣ P1 (since P1.eval (-X) = 0; note `-X : ℤ[X]` is the element of the base ring!)
  have hP1_root : P1.eval (-X : ℤ[X]) = 0 := by
    apply hzero_of_nat
    intro b hb
    have h1 := hP_eval b (-(b : ℤ))
    have hsym : ∑ j ∈ range b, (((-(b : ℤ) + (j : ℤ)) * (-(b : ℤ) + (j : ℤ) + 1)) ^ k -
        ((j : ℤ) * ((j : ℤ) + 1)) ^ k) = 0 := by
      rw [Finset.sum_sub_distrib]
      have href := Finset.sum_range_reflect (fun j => ((j : ℤ) * ((j : ℤ) + 1)) ^ k) b
      have heq : ∑ j ∈ range b, ((-(b : ℤ) + (j : ℤ)) * (-(b : ℤ) + (j : ℤ) + 1)) ^ k =
          ∑ j ∈ range b, (((b - 1 - j : ℕ) : ℤ) * (((b - 1 - j : ℕ) : ℤ) + 1)) ^ k := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        have hjb : j ≤ b - 1 := by rw [Finset.mem_range] at hj; omega
        have hsub : ((b - 1 - j : ℕ) : ℤ) = (b : ℤ) - 1 - (j : ℤ) := by omega
        rw [hsub]; congr 1; ring
      rw [heq, href, sub_self]
    rw [hsym, mul_zero] at h1
    have hev_neg : ∀ R : Polynomial (ℤ[X]), (R.eval (-X : ℤ[X])).eval (b : ℤ) =
        (R.eval (C (-(b : ℤ)))).eval (b : ℤ) := by
      intro R
      induction R using Polynomial.induction_on' with
      | add p q ihp ihq => simp [ihp, ihq]
      | monomial m c =>
        simp only [eval_monomial, eval_mul, eval_pow, eval_neg, eval_C, eval_X]
    have h2 : (P_BD.eval (-X : ℤ[X])).eval (b : ℤ) = 0 := by rw [hev_neg, h1]
    rw [hP1, eval_mul, eval_X, eval_mul, eval_neg, eval_X] at h2
    have hbne : -(b : ℤ) ≠ 0 := by omega
    exact (mul_eq_zero.mp h2).resolve_left hbne
  obtain ⟨P2, hP2⟩ : (X - C (-X : ℤ[X]) : Polynomial (ℤ[X])) ∣ P1 := by
    rw [Polynomial.dvd_iff_isRoot]
    exact hP1_root
  -- Factor 3: C X ∣ P2 (since evaluating inner B = 0 gives P_BD.map (evalRingHom 0) = 0!)
  have hP_map0 : P_BD.map (evalRingHom (0 : ℤ)) = 0 := by
    simp only [P_BD, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]
    refine Finset.sum_eq_zero (fun m _ => ?_)
    have hF0 : (evalRingHom (0 : ℤ)) (Fsc m) = 0 := by
      change (Fsc m).eval 0 = 0
      simp [Fsc, faulhaberInt_eval_zero]
    rw [hF0, map_zero, mul_zero]
  have hP2_map0 : P2.map (evalRingHom (0 : ℤ)) = 0 := by
    have h1 := hP_map0
    rw [hP1, hP2, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C] at h1
    have h0neg : (evalRingHom (0 : ℤ)) (-X : ℤ[X]) = 0 := by
      change (-X : ℤ[X]).eval 0 = 0; simp
    rw [h0neg, map_zero, sub_zero] at h1
    have hX2 : (X : ℤ[X]) * (X : ℤ[X]) ≠ 0 := mul_ne_zero X_ne_zero X_ne_zero
    rw [← mul_assoc] at h1
    exact (mul_eq_zero.mp h1).resolve_left hX2
  have hP2_coeff0 : ∀ m, (X : ℤ[X]) ∣ P2.coeff m := by
    intro m
    rw [show (X : ℤ[X]) = X - C 0 by simp, Polynomial.dvd_iff_isRoot]
    have h := congrArg (fun f : ℤ[X] => f.coeff m) hP2_map0
    rw [coeff_map, coeff_zero] at h
    exact h
  -- Write P2 = C X * P3 by dividing each coefficient by X (via P2 = ∑ m, C (P2.coeff m) * X^m)
  have hCX_dvd_P2 : C (X : ℤ[X]) ∣ P2 := by
    rw [Polynomial.as_sum_range_C_mul_X_pow P2]
    refine Finset.dvd_sum (fun m _ => ?_)
    obtain ⟨q, hq⟩ := hP2_coeff0 m
    refine ⟨C q * X ^ m, ?_⟩
    rw [hq, map_mul, mul_assoc]
  obtain ⟨P3, hP3⟩ := hCX_dvd_P2
  -- Now evaluate P_BD = X * ((X - C (-X)) * (C X * P3)) at outer D and inner B!
  have hfinal := hP_eval B (D : ℤ)
  rw [hP1, hP2, hP3] at hfinal
  simp only [eval_mul, eval_sub, eval_X, eval_C, sub_neg_eq_add, eval_add] at hfinal
  refine ⟨(P3.eval (C (D : ℤ))).eval (B : ℤ), ?_⟩
  push_cast
  linarith

/-- For prime `p ≥ 5`, `p` divides the numerator of `∑_{i=1}^{(p-1)/2} (i*(p-i))⁻¹` in `ℤ_{(p)}`. -/
lemma half_sum_inv_p_dvd {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    pDvdRat p 1 (∑ i ∈ Icc 1 ((p - 1) / 2), (((i * (p - i) : ℕ) : ℚ)⁻¹)) := by
  have : Fact p.Prime := ⟨hp⟩
  set h := (p - 1) / 2
  have h2h : 2 * h + 1 = p := by
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
    omega
  -- Common denominator P = ∏ i ∈ Icc 1 h, (i * (p - i))
  set P : ℕ := ∏ i ∈ Icc 1 h, (i * (p - i))
  have hP_pos : 0 < P := Finset.prod_pos (fun i hi => by
    have := Finset.mem_Icc.mp hi; exact Nat.mul_pos (by omega) (by omega))
  have hP_cop : Nat.Coprime p P := by
    refine nat_coprime_prod_right (fun i hi => ?_)
    have hi' := Finset.mem_Icc.mp hi
    have hc1 : Nat.Coprime p i := (hp.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
    have hc2 : Nat.Coprime p (p - i) := (hp.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
    exact hc1.mul_right hc2
  -- Numerator N = ∑ i ∈ Icc 1 h, P / (i * (p - i))
  set N : ℕ := ∑ i ∈ Icc 1 h, P / (i * (p - i))
  have hsum_eq : ∑ i ∈ Icc 1 h, (((i * (p - i) : ℕ) : ℚ)⁻¹) = (N : ℚ) / (P : ℚ) := by
    have hPq : (P : ℚ) ≠ 0 := by positivity
    rw [eq_div_iff hPq, Finset.sum_mul]
    simp only [N, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hdvd : i * (p - i) ∣ P := Finset.dvd_prod_of_mem _ hi
    have hpos : 0 < i * (p - i) := by have := Finset.mem_Icc.mp hi; exact Nat.mul_pos (by omega) (by omega)
    have hmul : (P / (i * (p - i)) : ℕ) * (i * (p - i)) = P := Nat.div_mul_cancel hdvd
    have hmulq : ((P / (i * (p - i)) : ℕ) : ℚ) * ((i * (p - i) : ℕ) : ℚ) = (P : ℚ) := by exact_mod_cast hmul
    rw [← hmulq]
    have hne : ((i * (p - i) : ℕ) : ℚ) ≠ 0 := by positivity
    field_simp
  -- Show p ∣ N by working in ZMod p (which is a Field)!
  have hp_dvd_N : p ∣ N := by
    rw [← ZMod.natCast_eq_zero_iff]
    have hPz : (P : ZMod p) ≠ 0 := by
      intro h0
      have hd : p ∣ P := (ZMod.natCast_eq_zero_iff P p).mp h0
      have h1 : p ∣ Nat.gcd p P := Nat.dvd_gcd dvd_rfl hd
      rw [hP_cop.gcd_eq_one] at h1
      exact hp.not_dvd_one h1
    have hNz : (N : ZMod p) = (P : ZMod p) * ∑ i ∈ Icc 1 h, -((i : ZMod p) ^ 2)⁻¹ := by
      simp only [N, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi' := Finset.mem_Icc.mp hi
      have hiz : (i : ZMod p) ≠ 0 := by
        intro h0
        have := (ZMod.natCast_eq_zero_iff i p).mp h0
        exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) this
      have hpiz : ((i * (p - i) : ℕ) : ZMod p) = -((i : ZMod p) ^ 2) := by
        have hsub : ((p - i : ℕ) : ZMod p) = -(i : ZMod p) := by
          have h1 : ((p - i : ℕ) : ZMod p) + (i : ZMod p) = (p : ZMod p) := by
            rw [← Nat.cast_add, Nat.sub_add_cancel (by omega)]
          rw [ZMod.natCast_self] at h1
          exact eq_neg_of_add_eq_zero_left h1
        rw [Nat.cast_mul, hsub]; ring
      have hdvd : i * (p - i) ∣ P := Finset.dvd_prod_of_mem _ hi
      have hmul : ((P / (i * (p - i)) : ℕ) : ZMod p) * ((i * (p - i) : ℕ) : ZMod p) = (P : ZMod p) := by
        rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
      rw [hpiz] at hmul
      have hsqne : -((i : ZMod p) ^ 2) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 2 hiz)
      calc ((P / (i * (p - i)) : ℕ) : ZMod p)
          = ((P / (i * (p - i)) : ℕ) : ZMod p) * (-((i : ZMod p) ^ 2) * (-((i : ZMod p) ^ 2))⁻¹) := by
              rw [mul_inv_cancel₀ hsqne, mul_one]
        _ = (((P / (i * (p - i)) : ℕ) : ZMod p) * -((i : ZMod p) ^ 2)) * (-((i : ZMod p) ^ 2))⁻¹ := by ring
        _ = (P : ZMod p) * -((i : ZMod p) ^ 2)⁻¹ := by rw [hmul, inv_neg]
    -- Show ∑ i ∈ Icc 1 h, ((i : ZMod p) ^ 2)⁻¹ = 0
    have hsum_zero : ∑ i ∈ Icc 1 h, ((i : ZMod p) ^ 2)⁻¹ = 0 := by
      have hpair : ∑ i ∈ Icc 1 h, ((i : ZMod p) ^ 2)⁻¹ =
          ∑ i ∈ Icc (h + 1) (p - 1), ((i : ZMod p) ^ 2)⁻¹ := by
        refine Finset.sum_bij (fun i _ => p - i) ?_ ?_ ?_ ?_
        · intro i hi; simp only [Finset.mem_Icc] at hi ⊢; omega
        · intro i1 hi1 i2 hi2 heq; simp only [Finset.mem_Icc] at hi1 hi2; omega
        · intro j hj; simp only [Finset.mem_Icc] at hj
          exact ⟨p - j, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro i hi
          have hi' := Finset.mem_Icc.mp hi
          have hsub : ((p - i : ℕ) : ZMod p) = -(i : ZMod p) := by
            have h1 : ((p - i : ℕ) : ZMod p) + (i : ZMod p) = (p : ZMod p) := by
              rw [← Nat.cast_add, Nat.sub_add_cancel (by omega)]
            rw [ZMod.natCast_self] at h1
            exact eq_neg_of_add_eq_zero_left h1
          rw [hsub, neg_sq]
      have hfull : (∑ i ∈ Icc 1 h, ((i : ZMod p) ^ 2)⁻¹) +
          (∑ i ∈ Icc (h + 1) (p - 1), ((i : ZMod p) ^ 2)⁻¹) =
          ∑ x : ZMod p, (x ^ 2)⁻¹ := by
        rw [← Finset.sum_union (by
          rw [Finset.disjoint_left]; intro x hx1 hx2; simp only [Finset.mem_Icc] at hx1 hx2; omega)]
        have hun : Icc 1 h ∪ Icc (h + 1) (p - 1) = Ico 1 p := by
          ext x; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ico]; omega
        rw [hun]
        have h0 : ∑ x : ZMod p, (x ^ 2)⁻¹ = ∑ x ∈ Finset.univ.erase (0 : ZMod p), (x ^ 2)⁻¹ := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))]
          rw [zero_pow (by decide : 2 ≠ 0), inv_zero, zero_add]
        rw [h0]
        refine Finset.sum_bij (fun i _ => (i : ZMod p)) ?_ ?_ ?_ ?_
        · intro i hi
          have hi' := Finset.mem_Ico.mp hi
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
          intro hzero
          exact Nat.not_dvd_of_pos_of_lt hi'.1 hi'.2 ((ZMod.natCast_eq_zero_iff i p).mp hzero)
        · intro i1 hi1 i2 hi2 heq
          have h1 := Finset.mem_Ico.mp hi1
          have h2 := Finset.mem_Ico.mp hi2
          have hv := congrArg ZMod.val heq
          rwa [ZMod.val_natCast_of_lt h1.2, ZMod.val_natCast_of_lt h2.2] at hv
        · intro x hx
          have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
          have hlt : x.val < p := ZMod.val_lt x
          have hpos : 1 ≤ x.val := by
            rcases Nat.eq_zero_or_pos x.val with h0' | hp'
            · exact absurd ((ZMod.val_eq_zero x).mp h0') hx0
            · exact hp'
          exact ⟨x.val, Finset.mem_Ico.mpr ⟨hpos, hlt⟩, ZMod.natCast_zmod_val x⟩
        · intro _ _; rfl
      have hall0 : ∑ x : ZMod p, (x ^ 2)⁻¹ = 0 := by
        have h2ne : (2 : ZMod p) ≠ 0 := by
          intro h0; have := (ZMod.natCast_eq_zero_iff 2 p).mp h0
          have := Nat.le_of_dvd (by decide) this; omega
        have h3ne : (3 : ZMod p) ≠ 0 := by
          intro h0; have := (ZMod.natCast_eq_zero_iff 3 p).mp h0
          have := Nat.le_of_dvd (by decide) this; omega
        set T : ZMod p := ∑ x : ZMod p, (x ^ 2)⁻¹
        have hmul : (2 : ZMod p) ^ 2 * T = T := by
          rw [Finset.mul_sum]
          have h1 : ∀ x : ZMod p, (2 : ZMod p) ^ 2 * (x ^ 2)⁻¹ = (((2 : ZMod p)⁻¹ * x) ^ 2)⁻¹ := by
            intro x; rw [mul_pow, mul_inv, inv_pow, inv_inv]
          rw [Finset.sum_congr rfl (fun x _ => h1 x)]
          exact Fintype.sum_equiv (Equiv.mulLeft₀ (2 : ZMod p)⁻¹ (inv_ne_zero h2ne)) _ _ (fun _ => rfl)
        have h3T : (3 : ZMod p) * T = 0 := by
          have : (3 : ZMod p) = (2 : ZMod p) ^ 2 - 1 := by norm_num
          rw [this, sub_mul, one_mul, hmul, sub_self]
        exact (mul_eq_zero.mp h3T).resolve_left h3ne
      rw [hall0, ← hpair, ← two_mul] at hfull
      have h2ne : (2 : ZMod p) ≠ 0 := by
        intro h0; have := (ZMod.natCast_eq_zero_iff 2 p).mp h0
        have := Nat.le_of_dvd (by decide) this; omega
      exact (mul_eq_zero.mp hfull).resolve_left h2ne
    rw [hNz, Finset.sum_neg_distrib, hsum_zero, neg_zero, mul_zero]
  obtain ⟨q, hq⟩ := hp_dvd_N
  refine ⟨q, P, hP_pos, hP_cop, ?_⟩
  rw [hsum_eq, hq]; push_cast; ring

/-- Block product `F p m = ∏_{i=1}^{p-1} (m * p + i)`. -/
def Fblock (p m : ℕ) : ℕ := ∏ i ∈ Ico 1 p, (m * p + i)

lemma Fblock_coprime {p : ℕ} (hp : p.Prime) (m : ℕ) : Nat.Coprime p (Fblock p m) := by
  refine nat_coprime_prod_right (fun i hi => ?_)
  have hi' := Finset.mem_Ico.mp hi
  rw [hp.coprime_iff_not_dvd]
  intro hd
  have hd_i : p ∣ i := (Nat.dvd_add_right (dvd_mul_left p m)).mp hd
  exact Nat.not_dvd_of_pos_of_lt hi'.1 hi'.2 hd_i

lemma Fblock_pair {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (m : ℕ) :
    (Fblock p m : ℚ) = ∏ i ∈ Icc 1 ((p - 1) / 2),
      (((i * (p - i) : ℕ) : ℚ) + ((m * (m + 1) : ℕ) : ℚ) * (p : ℚ) ^ 2) := by
  set h := (p - 1) / 2
  have h2h : 2 * h + 1 = p := by
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
    omega
  unfold Fblock
  have hsplit : Ico 1 p = Icc 1 h ∪ Icc (h + 1) (p - 1) := by
    ext x; simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Icc 1 h) (Icc (h + 1) (p - 1)) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2; simp only [Finset.mem_Icc] at hx1 hx2; omega
  rw [hsplit, Finset.prod_union hdisj, Nat.cast_mul, Nat.cast_prod, Nat.cast_prod]
  have hbij : ∏ i ∈ Icc (h + 1) (p - 1), ((m * p + i : ℕ) : ℚ) =
      ∏ i ∈ Icc 1 h, ((m * p + (p - i) : ℕ) : ℚ) := by
    refine Finset.prod_bij (fun j _ => p - j) ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
    · intro j1 hj1 j2 hj2 heq; simp only [Finset.mem_Icc] at hj1 hj2; omega
    · intro i hi; simp only [Finset.mem_Icc] at hi
      exact ⟨p - i, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro j hj; simp only [Finset.mem_Icc] at hj; congr 1; omega
  rw [hbij, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  have hi' := Finset.mem_Icc.mp hi
  have hsub : ((p - i : ℕ) : ℚ) = (p : ℚ) - (i : ℚ) := Nat.cast_sub (by omega)
  push_cast
  rw [hsub]
  ring

lemma factorial_mul_eq {p : ℕ} (hp : 0 < p) (m : ℕ) :
    (m * p).factorial = p ^ m * m.factorial * ∏ j ∈ range m, Fblock p j := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : ((m + 1) * p).factorial = (m * p).factorial * ∏ i ∈ Icc 1 p, (m * p + i) := by
      have hgen : ∀ a k : ℕ, (a + k).factorial = a.factorial * ∏ i ∈ Icc 1 k, (a + i) := by
        intro a k
        induction k with
        | zero => simp
        | succ k ihk =>
          rw [show a + (k + 1) = (a + k) + 1 by omega, Nat.factorial_succ, ihk]
          have hIcc : Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hIcc, Finset.prod_insert (by simp)]
          ring
      simpa [Nat.add_mul] using hgen (m * p) p
    have hIcc : ∏ i ∈ Icc 1 p, (m * p + i) = ((m + 1) * p) * Fblock p m := by
      have hs : Icc 1 p = insert p (Ico 1 p) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
      rw [hs, Finset.prod_insert (by simp), Fblock]
      have : m * p + p = (m + 1) * p := by ring
      rw [this]
    rw [hsplit, hIcc, ih, Finset.prod_range_succ, pow_succ, Nat.factorial_succ]
    ring

lemma choose_mul_Fblock {p : ℕ} (hp : 0 < p) (B D : ℕ) :
    ((B + D) * p).choose (B * p) * (∏ j ∈ range B, Fblock p j) =
      (B + D).choose B * (∏ j ∈ range B, Fblock p (D + j)) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show B * p ≤ (B + D) * p by nlinarith)
  have h2 := Nat.choose_mul_factorial_mul_factorial (show B ≤ B + D by omega)
  have hs1 : (B + D) * p - B * p = D * p := by
    rw [Nat.add_mul, Nat.add_sub_cancel_left]
  have hs2 : B + D - B = D := Nat.add_sub_cancel_left B D
  rw [hs1] at h1; rw [hs2] at h2
  have hprod_split : ∏ j ∈ range (B + D), Fblock p j =
      (∏ j ∈ range D, Fblock p j) * (∏ j ∈ range B, Fblock p (D + j)) := by
    have hs : range (B + D) = range D ∪ Ico D (B + D) := by
      ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hd : Disjoint (range D) (Ico D (B + D)) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2; simp only [Finset.mem_range, Finset.mem_Ico] at hx1 hx2; omega
    rw [hs, Finset.prod_union hd]
    congr 1
    refine Finset.prod_bij (fun j _ => j - D) ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢; omega
    · intro j1 hj1 j2 hj2 heq; simp only [Finset.mem_Ico] at hj1 hj2; omega
    · intro j hj; simp only [Finset.mem_range] at hj
      exact ⟨D + j, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro j hj; simp only [Finset.mem_Ico] at hj; congr 1; omega
  have hpos : 0 < p ^ (B + D) * B.factorial * D.factorial * (∏ j ∈ range D, Fblock p j) := by
    have hFp : 0 < ∏ j ∈ range D, Fblock p j :=
      Finset.prod_pos (fun j _ => Finset.prod_pos (fun i hi => by
        have := (Finset.mem_Ico.mp hi).1; omega))
    positivity
  apply Nat.eq_of_mul_eq_mul_left hpos
  have hlhs : p ^ (B + D) * B.factorial * D.factorial * (∏ j ∈ range D, Fblock p j) *
      (((B + D) * p).choose (B * p) * ∏ j ∈ range B, Fblock p j) =
      ((B + D) * p).choose (B * p) * (B * p).factorial * (D * p).factorial := by
    rw [factorial_mul_eq hp B, factorial_mul_eq hp D, pow_add]; ring
  have hrhs : p ^ (B + D) * B.factorial * D.factorial * (∏ j ∈ range D, Fblock p j) *
      ((B + D).choose B * ∏ j ∈ range B, Fblock p (D + j)) =
      ((B + D) * p).factorial := by
    rw [factorial_mul_eq hp (B + D), hprod_split, ← h2]; ring
  rw [hlhs, hrhs, h1]

/-- Main Kazandzidis F-product congruence:
`p^(3 + v_p(B) + v_p(D) + v_p(B+D)) ∣ ∏_{j<B} F(D+j) - ∏_{j<B} F(j)`. -/
lemma Fblock_prod_congr {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (B D : ℕ) (hB : 0 < B) (hD : 0 < D) :
    ((p : ℤ) ^ (3 + padicValNat p B + padicValNat p D + padicValNat p (B + D))) ∣
      ((∏ j ∈ range B, Fblock p (D + j) : ℕ) : ℤ) - ((∏ j ∈ range B, Fblock p j : ℕ) : ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  set M := 3 + padicValNat p B + padicValNat p D + padicValNat p (B + D)
  set h := (p - 1) / 2
  have h2h : 2 * h + 1 = p := by
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
    omega
  set P0 : ℕ := ∏ j ∈ range B, Fblock p j
  set P1 : ℕ := ∏ j ∈ range B, Fblock p (D + j)
  set F0 : ℕ := Fblock p 0
  have hF0_pos : 0 < F0 := Finset.prod_pos (fun i hi => by have := (Finset.mem_Ico.mp hi).1; omega)
  have hF0_cop : Nat.Coprime p F0 := Fblock_coprime hp 0
  have hP0_pos : 0 < P0 := Finset.prod_pos (fun j _ =>
    Finset.prod_pos (fun i hi => by have := (Finset.mem_Ico.mp hi).1; omega))
  have hP0_cop : Nat.Coprime p P0 := nat_coprime_prod_right (fun j _ => Fblock_coprime hp j)
  -- Express P1 / F0^B and P0 / F0^B as products of (1 + u_{j,i}) where p^2 ∣ u_{j,i}!
  have hF0_pair : (F0 : ℚ) = ∏ i ∈ Icc 1 h, ((i * (p - i) : ℕ) : ℚ) := by
    simpa [F0, h] using Fblock_pair hp hp5 0
  have hratio : ∀ m : ℕ, (Fblock p m : ℚ) / (F0 : ℚ) =
      ∏ i ∈ Icc 1 h, (1 + ((m * (m + 1) : ℕ) : ℚ) * (p : ℚ) ^ 2 / ((i * (p - i) : ℕ) : ℚ)) := by
    intro m
    rw [Fblock_pair hp hp5 m, hF0_pair, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have hi' := Finset.mem_Icc.mp hi
    have hne : ((i * (p - i) : ℕ) : ℚ) ≠ 0 := by
      have : 0 < i * (p - i) := Nat.mul_pos (by omega) (by omega)
      positivity
    field_simp
  let u : ℕ → ℕ × ℕ → ℚ := fun shift ji =>
    (((shift + ji.1) * (shift + ji.1 + 1) : ℕ) : ℚ) * (p : ℚ) ^ 2 / ((ji.2 * (p - ji.2) : ℕ) : ℚ)
  let S_idx : Finset (ℕ × ℕ) := range B ×ˢ Icc 1 h
  have hu_p2 : ∀ shift, ∀ ji ∈ S_idx, pDvdRat p 2 (u shift ji) := by
    intro shift ji hji
    have hi' := Finset.mem_Icc.mp (Finset.mem_product.mp hji).2
    have hpos : 0 < ji.2 * (p - ji.2) := Nat.mul_pos (by omega) (by omega)
    have hcop : Nat.Coprime p (ji.2 * (p - ji.2)) :=
      ((hp.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).mul_right
        ((hp.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)))
    exact ⟨((shift + ji.1) * (shift + ji.1 + 1) : ℕ), ji.2 * (p - ji.2), hpos, hcop, by
      simp only [u]; push_cast; ring⟩
  have hP1_eq : (P1 : ℚ) / ((F0 : ℚ) ^ B) = ∏ ji ∈ S_idx, (1 + u D ji) := by
    simp only [P1, S_idx, Finset.prod_product, Nat.cast_prod]
    rw [show (F0 : ℚ) ^ B = ∏ _j ∈ range B, (F0 : ℚ) by simp, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl (fun j _ => hratio (D + j))
  have hP0_eq : (P0 : ℚ) / ((F0 : ℚ) ^ B) = ∏ ji ∈ S_idx, (1 + u 0 ji) := by
    simp only [P0, S_idx, Finset.prod_product, Nat.cast_prod]
    rw [show (F0 : ℚ) ^ B = ∏ _j ∈ range B, (F0 : ℚ) by simp, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl (fun j _ => by simpa [u] using hratio j)
  -- Apply truncLog_prod to both products!
  obtain ⟨hQ1_2, hQ1_log⟩ := truncLog_prod S_idx (M := M) hp hp5 (u D) (hu_p2 D)
  obtain ⟨hQ0_2, hQ0_log⟩ := truncLog_prod S_idx (M := M) hp hp5 (u 0) (hu_p2 0)
  -- Show ∑ truncLog M (u D ji) - ∑ truncLog M (u 0 ji) has pDvdRat p M!
  have hlog_diff : pDvdRat p M (∑ ji ∈ S_idx, truncLog M (u D ji) - ∑ ji ∈ S_idx, truncLog M (u 0 ji)) := by
    have hrew : (∑ ji ∈ S_idx, truncLog M (u D ji)) - (∑ ji ∈ S_idx, truncLog M (u 0 ji)) =
        ∑ k ∈ Icc 1 M, ((-1 : ℚ) ^ (k - 1) * (p : ℚ) ^ (2 * k) / (k : ℚ)) *
          (∑ i ∈ Icc 1 h, (((i * (p - i) : ℕ) : ℚ)⁻¹) ^ k) *
          (∑ j ∈ range B, (((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ k -
                            ((j : ℤ) * ((j : ℤ) + 1)) ^ k : ℤ) : ℚ)) := by
      simp only [truncLog, ← Finset.sum_sub_distrib]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      conv_lhs => simp only [S_idx, Finset.sum_product, u, mul_pow, div_pow, ← pow_mul]
      have hcomm : ∑ j ∈ range B, ∑ i ∈ Icc 1 h,
          ((-1 : ℚ) ^ (k - 1) * ((((D + j) * (D + j + 1) : ℕ) : ℚ) ^ k * (p : ℚ) ^ (2 * k) /
            ((i * (p - i) : ℕ) : ℚ) ^ k) / (k : ℚ) -
           (-1 : ℚ) ^ (k - 1) * ((((0 + j) * (0 + j + 1) : ℕ) : ℚ) ^ k * (p : ℚ) ^ (2 * k) /
            ((i * (p - i) : ℕ) : ℚ) ^ k) / (k : ℚ)) =
          ∑ j ∈ range B, ((-1 : ℚ) ^ (k - 1) * (p : ℚ) ^ (2 * k) / (k : ℚ)) *
            (∑ i ∈ Icc 1 h, (((i * (p - i) : ℕ) : ℚ)⁻¹) ^ k) *
            (((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ k -
              ((j : ℤ) * ((j : ℤ) + 1)) ^ k : ℤ) : ℚ) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        push_cast
        rw [inv_pow]
        ring
      rw [hcomm, ← Finset.mul_sum]
    rw [hrew]
    refine pDvdRat_sum (fun k hk => ?_)
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hV : (p : ℤ) ^ (padicValNat p B + padicValNat p D + padicValNat p (B + D)) ∣
        ((B * D * (B + D) : ℕ) : ℤ) := by
      have h1 : p ^ padicValNat p B ∣ B := pow_padicValNat_dvd
      have h2 : p ^ padicValNat p D ∣ D := pow_padicValNat_dvd
      have h3 : p ^ padicValNat p (B + D) ∣ B + D := pow_padicValNat_dvd
      have hmul : p ^ (padicValNat p B + padicValNat p D + padicValNat p (B + D)) ∣ B * D * (B + D) := by
        rw [pow_add, pow_add]; exact mul_dvd_mul (mul_dvd_mul h1 h2) h3
      exact_mod_cast hmul
    have hSk_dvd : (p : ℤ) ^ (padicValNat p B + padicValNat p D + padicValNat p (B + D)) ∣
        ((2 * k + 1).factorial : ℤ) *
          ∑ j ∈ range B, ((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ k -
                          ((j : ℤ) * ((j : ℤ) + 1)) ^ k) :=
      hV.trans (power_sum_dvd k B D)
    set V := padicValNat p B + padicValNat p D + padicValNat p (B + D)
    have hinv_sum_0 : pDvdRat p 0 (∑ i ∈ Icc 1 h, (((i * (p - i) : ℕ) : ℚ)⁻¹) ^ k) := by
      refine pDvdRat_sum (fun i hi => ?_)
      have hi' := Finset.mem_Icc.mp hi
      have hpos : 0 < i * (p - i) := Nat.mul_pos (by omega) (by omega)
      have hcop : Nat.Coprime p (i * (p - i)) :=
        ((hp.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).mul_right
          ((hp.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)))
      simpa using pDvdRat_pow (pDvdRat_inv_nat hpos hcop) k
    by_cases hk_eq1 : k = 1
    · subst hk_eq1
      have hinv1 := half_sum_inv_p_dvd hp hp5
      have hS1_eq : ∑ j ∈ range B, ((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ 1 -
          ((j : ℤ) * ((j : ℤ) + 1)) ^ 1) = ((B * D * (B + D) : ℕ) : ℤ) := by
        have h1 : ∀ B' : ℕ, ∑ j ∈ range B', ((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ 1 -
            ((j : ℤ) * ((j : ℤ) + 1)) ^ 1) = ((B' * D * (B' + D) : ℕ) : ℤ) := by
          intro B'
          induction B' with
          | zero => simp
          | succ B' ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
        exact h1 B
      have hS1_p : pDvdRat p V (∑ j ∈ range B, (((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ 1 -
          ((j : ℤ) * ((j : ℤ) + 1)) ^ 1 : ℤ) : ℚ)) := by
        rw [← Int.cast_sum, hS1_eq]
        exact pDvdRat_of_int _ hV
      have hp2 : pDvdRat p 2 ((-1 : ℚ) ^ (1 - 1) * (p : ℚ) ^ (2 * 1) / ((1 : ℕ) : ℚ)) := by
        refine ⟨1, 1, Nat.one_pos, Nat.coprime_one_right p, ?_⟩; norm_num
      have hinv1' : pDvdRat p 1 (∑ i ∈ Icc 1 h, (((i * (p - i) : ℕ) : ℚ)⁻¹) ^ 1) := by
        simpa only [pow_one] using hinv1
      have hprod := pDvdRat_mul (pDvdRat_mul hp2 hinv1') hS1_p
      exact pDvdRat_mono (by omega : M ≤ 2 + 1 + V) hprod
    · have hk2 : 2 ≤ k := by omega
      have hSk_q : pDvdRat p V ((((2 * k + 1).factorial : ℤ) *
          ∑ j ∈ range B, ((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ k -
                          ((j : ℤ) * ((j : ℤ) + 1)) ^ k) : ℤ) : ℚ) :=
        pDvdRat_of_int _ hSk_dvd
      have hp2k : pDvdRat p (2 * k) ((-1 : ℚ) ^ (k - 1) * (p : ℚ) ^ (2 * k)) := by
        refine ⟨(-1 : ℤ) ^ (k - 1), 1, Nat.one_pos, Nat.coprime_one_right p, ?_⟩
        push_cast; ring
      have hnum := pDvdRat_mul (pDvdRat_mul hp2k hinv_sum_0) hSk_q
      have hvp_k : 4 * padicValNat p k ≤ k - 1 := four_mul_padicValNat_le hp hp5 hk1
      have hvp_fac : 4 * padicValNat p (2 * k + 1).factorial ≤ 2 * k + 1 :=
        four_mul_padicValNat_factorial_le hp hp5
      have hvp_prod : padicValNat p (k * (2 * k + 1).factorial) =
          padicValNat p k + padicValNat p (2 * k + 1).factorial :=
        padicValNat.mul (by omega) (Nat.factorial_ne_zero _)
      have hbound : 3 + padicValNat p (k * (2 * k + 1).factorial) ≤ 2 * k := by omega
      have hdiv := pDvdRat_div_nat hp (Nat.mul_pos (by omega) (Nat.factorial_pos _))
        le_rfl (by omega : padicValNat p (k * (2 * k + 1).factorial) ≤ 2 * k + 0 + V) hnum
      have hrew_k : ((-1 : ℚ) ^ (k - 1) * (p : ℚ) ^ (2 * k) / (k : ℚ)) *
          (∑ i ∈ Icc 1 h, (((i * (p - i) : ℕ) : ℚ)⁻¹) ^ k) *
          (∑ j ∈ range B, (((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ k -
                            ((j : ℤ) * ((j : ℤ) + 1)) ^ k : ℤ) : ℚ)) =
          ((-1 : ℚ) ^ (k - 1) * (p : ℚ) ^ (2 * k) *
            (∑ i ∈ Icc 1 h, (((i * (p - i) : ℕ) : ℚ)⁻¹) ^ k) *
            ((((2 * k + 1).factorial : ℤ) *
              ∑ j ∈ range B, ((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ k -
                              ((j : ℤ) * ((j : ℤ) + 1)) ^ k) : ℤ) : ℚ)) /
            ((k * (2 * k + 1).factorial : ℕ) : ℚ) := by
        rw [← Int.cast_sum]
        have hfacne : ((2 * k + 1).factorial : ℚ) ≠ 0 := by positivity
        have hkne : (k : ℚ) ≠ 0 := by positivity
        push_cast
        field_simp
      rw [hrew_k]
      exact pDvdRat_mono (by omega : M ≤ 2 * k + 0 + V - padicValNat p (k * (2 * k + 1).factorial)) hdiv
  -- Combine: truncLog M (P1/F0^B - 1) - truncLog M (P0/F0^B - 1) has pDvdRat p M!
  set q1 : ℚ := (P1 : ℚ) / ((F0 : ℚ) ^ B) - 1
  set q0 : ℚ := (P0 : ℚ) / ((F0 : ℚ) ^ B) - 1
  rw [← hP1_eq] at hQ1_2 hQ1_log
  rw [← hP0_eq] at hQ0_2 hQ0_log
  have hlog_q : pDvdRat p M (truncLog M q1 - truncLog M q0) := by
    have h1 := pDvdRat_add (pDvdRat_sub hQ1_log hQ0_log) hlog_diff
    convert h1 using 1
    ring
  -- Define w = (P1 - P0) / P0 so 1 + q1 = (1 + q0) * (1 + w)
  set w : ℚ := ((P1 : ℚ) - (P0 : ℚ)) / (P0 : ℚ)
  have h1q1 : 1 + q1 = (1 + q0) * (1 + w) := by
    have hP0ne : (P0 : ℚ) ≠ 0 := by positivity
    have hF0ne : (F0 : ℚ) ^ B ≠ 0 := pow_ne_zero B (by positivity)
    simp only [q1, q0, w]; field_simp; ring
  have hq1_eq : q1 = q0 + w + q0 * w := by linarith
  have hw2 : pDvdRat p 2 w := by
    have hq10 : pDvdRat p 2 (q1 - q0) := pDvdRat_sub hQ1_2 hQ0_2
    have hF0B : pDvdRat p 0 (((F0 : ℚ) ^ B) / (P0 : ℚ)) := by
      refine ⟨(F0 : ℤ) ^ B, P0, hP0_pos, hP0_cop, ?_⟩; push_cast; ring
    have hw_eq : w = (q1 - q0) * (((F0 : ℚ) ^ B) / (P0 : ℚ)) := by
      have hP0ne : (P0 : ℚ) ≠ 0 := by positivity
      have hF0ne : (F0 : ℚ) ^ B ≠ 0 := pow_ne_zero B (by positivity)
      simp only [q1, q0, w]; field_simp; ring
    rw [hw_eq]
    simpa using pDvdRat_mul hq10 hF0B
  have hmul_log := truncLog_mul (M := M) hp hp5 hQ0_2 hw2
  rw [← hq1_eq] at hmul_log
  have hlog_w : pDvdRat p M (truncLog M w) := by
    have h := pDvdRat_sub hlog_q hmul_log
    convert h using 1
    ring
  have hwM : pDvdRat p M w := truncLog_inj hp hp5 hw2 hlog_w
  -- Multiply by P0 to get pDvdRat p M ((P1 - P0 : ℤ) : ℚ)!
  have hdiff_q : pDvdRat p M ((((P1 : ℤ) - (P0 : ℤ) : ℤ) : ℚ)) := by
    have hP0_0 : pDvdRat p 0 (P0 : ℚ) := pDvdRat_of_int_zero p (P0 : ℤ)
    have hmul := pDvdRat_mul hwM hP0_0
    have hP0ne : (P0 : ℚ) ≠ 0 := by positivity
    have heq : w * (P0 : ℚ) = (((P1 : ℤ) - (P0 : ℤ) : ℤ) : ℚ) := by
      simp only [w]; push_cast; field_simp
    rw [heq] at hmul
    simpa using hmul
  exact int_dvd_of_pDvdRat hdiff_q

/-- Kazandzidis congruence with extra `p`-adic factor from `C(B+D, B)`:
`p^(3 + v_p(B) + v_p(D) + v_p(B+D) + v_p(C(B+D, B))) ∣ C((B+D)p, Bp) - C(B+D, B)` (in `ℤ`). -/
lemma kazandzidis_pow {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (B D : ℕ) (hB : 0 < B) (hD : 0 < D) :
    ((p : ℤ) ^ (3 + padicValNat p B + padicValNat p D + padicValNat p (B + D) +
        padicValNat p ((B + D).choose B))) ∣
      (((B + D) * p).choose (B * p) : ℤ) - ((B + D).choose B : ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  set E := 3 + padicValNat p B + padicValNat p D + padicValNat p (B + D)
  set V := padicValNat p ((B + D).choose B)
  set P0 : ℕ := ∏ j ∈ range B, Fblock p j
  set P1 : ℕ := ∏ j ∈ range B, Fblock p (D + j)
  have hrel : (((B + D) * p).choose (B * p) : ℤ) * (P0 : ℤ) = ((B + D).choose B : ℤ) * (P1 : ℤ) := by
    exact_mod_cast choose_mul_Fblock hp.pos B D
  have hsub : ((((B + D) * p).choose (B * p) : ℤ) - ((B + D).choose B : ℤ)) * (P0 : ℤ) =
      ((B + D).choose B : ℤ) * ((P1 : ℤ) - (P0 : ℤ)) := by linarith
  have hP0_cop : Nat.Coprime p P0 := nat_coprime_prod_right (fun j _ => Fblock_coprime hp j)
  have hd1 : (p : ℤ) ^ E ∣ (P1 : ℤ) - (P0 : ℤ) := Fblock_prod_congr hp hp5 B D hB hD
  have hd2 : (p : ℤ) ^ V ∣ ((B + D).choose B : ℤ) := by
    exact_mod_cast pow_padicValNat_dvd (p := p) (n := (B + D).choose B)
  have hmul : (p : ℤ) ^ (E + V) ∣ (P0 : ℤ) * ((((B + D) * p).choose (B * p) : ℤ) - ((B + D).choose B : ℤ)) := by
    rw [mul_comm, hsub, pow_add, mul_comm ((p : ℤ) ^ E)]
    exact mul_dvd_mul hd2 hd1
  have hcopZ : IsCoprime ((p : ℤ) ^ (E + V)) (P0 : ℤ) :=
    (Nat.isCoprime_iff_coprime.mpr hP0_cop).pow_left
  exact hcopZ.dvd_of_dvd_mul_left hmul

/-- Part 3 helper: `p^(v_p(A) - v_p(B)) ∣ C(A, B)` whenever `0 < B ≤ A` and `v_p(B) ≤ v_p(A)`. -/
lemma padicValNat_choose_ge {p A B : ℕ} (hp : p.Prime) (hB : 0 < B) (hBA : B ≤ A) :
    padicValNat p A - padicValNat p B ≤ padicValNat p (A.choose B) := by
  have : Fact p.Prime := ⟨hp⟩
  have hA : 0 < A := lt_of_lt_of_le hB hBA
  have hch_pos : 0 < A.choose B := Nat.choose_pos hBA
  have hmul : B * A.choose B = A * (A - 1).choose (B - 1) := by
    have := Nat.add_one_mul_choose_eq (A - 1) (B - 1)
    rw [Nat.sub_add_cancel hA, Nat.sub_add_cancel hB] at this
    linarith
  have hv := congrArg (padicValNat p) hmul
  have hprev_pos : 0 < (A - 1).choose (B - 1) := Nat.choose_pos (by omega)
  rw [padicValNat.mul (by omega) (by omega), padicValNat.mul (by omega) (by omega)] at hv
  omega


end OeisA363986Part23

end

section

open Finset OeisA363986Part23
noncomputable section
namespace A363990Valuation

/-- Positive representation of the negative-top coefficient (-1)^k binom(-A,k). -/
def negChoose (A k : ℕ) : ℕ := (A + k - 1).choose k

theorem negChoose_pos {A : ℕ} (hA : 0 < A) (k : ℕ) : 0 < negChoose A k :=
  Nat.choose_pos (by omega)

/-- The cleared ratio that converts negative-top scaling to ordinary Kazandzidis. -/
theorem mul_negChoose {A : ℕ} (hA : 0 < A) (k : ℕ) :
    (A + k) * negChoose A k = A * (A + k).choose k := by
  have h := Nat.choose_mul_succ_eq (A + k - 1) k
  rw [Nat.sub_add_cancel (by omega : 1 ≤ A + k), show A + k - k = A by omega] at h
  simpa only [negChoose, mul_comm] using h

/-- The corresponding identity for the difference of two scaled coefficients. -/
theorem negChoose_scale_identity {p A : ℕ} (hp : 0 < p) (hA : 0 < A) (k : ℕ) :
    ((A + k : ℕ) : ℤ) * ((negChoose (A * p) (k * p) : ℤ) - negChoose A k) =
      (A : ℤ) * ((((A + k) * p).choose (k * p) : ℤ) - (A + k).choose k) := by
  have hu := mul_negChoose (Nat.mul_pos hA hp) (k * p)
  have hs : ((A + k) * negChoose (A * p) (k * p)) * p =
      (A * ((A + k) * p).choose (k * p)) * p := by
    convert hu using 1 <;> ring
  have hsc := mul_right_cancel₀ hp.ne' hs
  have hl := mul_negChoose hA k
  have hz1 : ((A + k : ℕ) : ℤ) * (negChoose (A * p) (k * p) : ℤ) =
      (A : ℤ) * (((A + k) * p).choose (k * p) : ℤ) := by exact_mod_cast hsc
  have hz0 : ((A + k : ℕ) : ℤ) * (negChoose A k : ℤ) =
      (A : ℤ) * ((A + k).choose k : ℤ) := by exact_mod_cast hl
  linear_combination hz1 - hz0

/-- Certified negative-top Kazandzidis, including the full lower coefficient valuation. -/
theorem negChoose_kazandzidis {p A k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hA : 0 < A) (hk : 0 < k) :
    (p : ℤ) ^ (3 + padicValNat p A + padicValNat p k + padicValNat p (A + k) +
      padicValNat p (negChoose A k)) ∣
      (negChoose (A * p) (k * p) : ℤ) - negChoose A k := by
  letI : Fact p.Prime := ⟨hp⟩
  let Δ : ℤ := (negChoose (A * p) (k * p) : ℤ) - negChoose A k
  let C : ℤ := (((A + k) * p).choose (k * p) : ℤ) - (A + k).choose k
  by_cases hz : Δ = 0
  · change _ ∣ Δ
    rw [hz]
    exact dvd_zero _
  have hid : ((A + k : ℕ) : ℤ) * Δ = (A : ℤ) * C := negChoose_scale_identity hp.pos hA k
  have hC : C ≠ 0 := by
    intro he
    rw [he, mul_zero] at hid
    exact hz ((mul_eq_zero.mp hid).resolve_left (by positivity))
  have hd := kazandzidis_pow hp hp5 k A hk hA
  rw [Nat.add_comm k A] at hd
  change (p : ℤ) ^ (3 + padicValNat p k + padicValNat p A + padicValNat p (A + k) +
    padicValNat p ((A + k).choose k)) ∣ C at hd
  have hdv := ((padicValInt_dvd_iff _ C).mp hd).resolve_left hC
  have hv := congrArg (padicValInt p) hid
  rw [padicValInt.mul (by positivity) hz, padicValInt.mul (by positivity) hC,
    padicValInt.of_nat, padicValInt.of_nat] at hv
  have hlow := congrArg (padicValNat p) (mul_negChoose hA k)
  rw [padicValNat.mul (by omega) (negChoose_pos hA k).ne',
    padicValNat.mul hA.ne' (Nat.choose_pos (by omega)).ne'] at hlow
  apply (padicValInt_dvd_iff _ _).mpr
  right
  change _ ≤ padicValInt p Δ
  omega

/-- A unit lower index exposes every prime power in an ordinary binomial top. -/
theorem choose_unit_dvd {p e A k : ℕ} (hp : p.Prime) (hA : p ^ e ∣ A)
    (hk : ¬p ∣ k) : (p : ℤ) ^ e ∣ (A.choose k : ℤ) := by
  by_cases hka : k ≤ A
  · have hk0 : 0 < k := Nat.pos_of_ne_zero (fun h => hk (h ▸ dvd_zero p))
    have hA0 : 0 < A := lt_of_lt_of_le hk0 hka
    have hh := Nat.add_one_mul_choose_eq (A - 1) (k - 1)
    rw [Nat.sub_add_cancel hA0, Nat.sub_add_cancel hk0] at hh
    have hid : (k : ℤ) * (A.choose k : ℤ) =
        (A : ℤ) * ((A - 1).choose (k - 1) : ℤ) := by
      have hn : k * A.choose k = A * (A - 1).choose (k - 1) := by simpa only [mul_comm] using hh.symm
      exact_mod_cast hn
    have hd : (p : ℤ) ^ e ∣ (A : ℤ) := by exact_mod_cast hA
    have hm : (p : ℤ) ^ e ∣ (k : ℤ) * (A.choose k : ℤ) := by
      rw [hid]
      exact dvd_mul_of_dvd_left hd _
    have hc : IsCoprime ((p : ℤ) ^ e) (k : ℤ) :=
      (Nat.isCoprime_iff_coprime.mpr (hp.coprime_iff_not_dvd.mpr hk)).pow_left
    exact hc.dvd_of_dvd_mul_left hm
  · rw [Nat.choose_eq_zero_of_lt (by omega : A < k), Nat.cast_zero]
    exact dvd_zero _

/-- The same unit-index divisibility for the negative-top positive representation. -/
theorem negChoose_unit_dvd {p e A k : ℕ} (hp : p.Prime) (hA : p ^ e ∣ A)
    (hk : ¬p ∣ k) : (p : ℤ) ^ e ∣ (negChoose A k : ℤ) := by
  have hk0 : 0 < k := Nat.pos_of_ne_zero (fun h => hk (h ▸ dvd_zero p))
  have hh := Nat.choose_succ_right_eq (A + k - 1) (k - 1)
  rw [Nat.sub_add_cancel hk0, show A + k - 1 - (k - 1) = A by omega] at hh
  have hid : (k : ℤ) * (negChoose A k : ℤ) =
      (A : ℤ) * ((A + k - 1).choose (k - 1) : ℤ) := by
    exact_mod_cast (show k * negChoose A k = A * (A + k - 1).choose (k - 1) by
      simpa only [negChoose, mul_comm] using hh)
  have hd : (p : ℤ) ^ e ∣ (A : ℤ) := by exact_mod_cast hA
  have hm : (p : ℤ) ^ e ∣ (k : ℤ) * (negChoose A k : ℤ) := by
    rw [hid]
    exact dvd_mul_of_dvd_left hd _
  have hc : IsCoprime ((p : ℤ) ^ e) (k : ℤ) :=
    (Nat.isCoprime_iff_coprime.mpr (hp.coprime_iff_not_dvd.mpr hk)).pow_left
  exact hc.dvd_of_dvd_mul_left hm

/-- The m=4 signed convolution, after cancellation of its negative-top sign. -/
def term (N i j k : ℕ) : ℤ :=
  (4 * N).choose i * ((4 * N).choose j : ℤ) ^ 2 * negChoose (6 * N) k

/-- The complete j-unit part is pointwise divisible by p^(3r). -/
theorem unit_j_term {p r N i j k : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hN : p ^ r ∣ N) (hsum : i + j + k = N) (hj : ¬p ∣ j) :
    (p : ℤ) ^ (3 * r) ∣ term N i j k := by
  have h4 : p ^ r ∣ 4 * N := dvd_mul_of_dvd_right hN _
  have h6 : p ^ r ∣ 6 * N := dvd_mul_of_dvd_right hN _
  have hdj := choose_unit_dvd hp h4 hj
  have hN1 : p ∣ N := by simpa only [pow_one] using (pow_dvd_pow p hr).trans hN
  have hu : ¬p ∣ i ∨ ¬p ∣ k := by
    by_contra h
    push Not at h
    obtain ⟨hi, hk⟩ := h
    have hNi : (p : ℤ) ∣ (N : ℤ) := by exact_mod_cast hN1
    have hii : (p : ℤ) ∣ (i : ℤ) := by exact_mod_cast hi
    have hki : (p : ℤ) ∣ (k : ℤ) := by exact_mod_cast hk
    have hji : (p : ℤ) ∣ (j : ℤ) := by
      have hh : (p : ℤ) ∣ (N : ℤ) - i - k := dvd_sub (dvd_sub hNi hii) hki
      have he : (N : ℤ) - i - k = j := by
        have he : (i : ℤ) + j + k = N := by exact_mod_cast hsum
        linear_combination -he
      rw [he] at hh
      exact hh
    exact hj (by exact_mod_cast hji)
  have hjsq : (p : ℤ) ^ (2 * r) ∣ ((4 * N).choose j : ℤ) ^ 2 := by
    have hh : ((p : ℤ) ^ r) ^ 2 ∣ ((4 * N).choose j : ℤ) ^ 2 := pow_dvd_pow_of_dvd hdj 2
    rw [← pow_mul] at hh
    simpa only [Nat.mul_comm r 2] using hh
  rcases hu with hi | hk
  · have hdi := choose_unit_dvd hp h4 hi
    have hd := dvd_mul_of_dvd_left (mul_dvd_mul hdi hjsq) (negChoose (6 * N) k : ℤ)
    simpa only [term, ← pow_add, show r + 2 * r = 3 * r by omega] using hd
  · have hdk := negChoose_unit_dvd hp h6 hk
    have hd := dvd_mul_of_dvd_left (mul_dvd_mul hjsq hdk) ((4 * N).choose i : ℤ)
    rw [← pow_add, show 2 * r + r = 3 * r by omega] at hd
    have he : ((4 * N).choose j : ℤ) ^ 2 * (negChoose (6 * N) k : ℤ) *
        ((4 * N).choose i : ℤ) = term N i j k := by unfold term; ring
    rw [he] at hd
    exact hd

/-- Uniform ordinary-binomial scaling when the top and index carry prescribed powers. -/
theorem choose_scale_bound {p A k R t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hA : p ^ R ∣ A) (hk : p ^ t ∣ k) (ht : t ≤ R) :
    (p : ℤ) ^ (3 + R + 2 * t + padicValNat p (A.choose k)) ∣
      ((A * p).choose (k * p) : ℤ) - A.choose k := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hk0 : k = 0
  · subst k
    simp only [Nat.zero_mul, Nat.choose_zero_right, Nat.cast_one, sub_self, dvd_zero]
  by_cases hka : k < A
  · have hD : 0 < A - k := Nat.sub_pos_of_lt hka
    have hA0 : 0 < A := lt_of_le_of_lt (Nat.zero_le k) hka
    have hAt : p ^ t ∣ A := (pow_dvd_pow p ht).trans hA
    have hDt : p ^ t ∣ A - k := Nat.dvd_sub hAt hk
    have hvA := (padicValNat_dvd_iff_le hA0.ne').mp hA
    have hvk := (padicValNat_dvd_iff_le hk0).mp hk
    have hvD := (padicValNat_dvd_iff_le hD.ne').mp hDt
    have hd := kazandzidis_pow hp hp5 k (A - k) (Nat.pos_of_ne_zero hk0) hD
    rw [show k + (A - k) = A by omega] at hd
    exact (pow_dvd_pow (p : ℤ) (by omega :
      3 + R + 2 * t + padicValNat p (A.choose k) ≤
      3 + padicValNat p k + padicValNat p (A - k) + padicValNat p A +
        padicValNat p (A.choose k))).trans hd
  · by_cases hEq : k = A
    · subst k
      simp only [Nat.choose_self, Nat.cast_one, sub_self, dvd_zero]
    · have hlt : A < k := by omega
      rw [Nat.choose_eq_zero_of_lt hlt,
        Nat.choose_eq_zero_of_lt (Nat.mul_lt_mul_of_pos_right hlt hp.pos)]
      simp

/-- Uniform negative-top scaling, with exactly the same gain as an ordinary factor. -/
theorem negChoose_scale_bound {p A k R t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hA0 : 0 < A) (hA : p ^ R ∣ A) (hk : p ^ t ∣ k) (ht : t ≤ R) :
    (p : ℤ) ^ (3 + R + 2 * t + padicValNat p (negChoose A k)) ∣
      (negChoose (A * p) (k * p) : ℤ) - negChoose A k := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hk0 : k = 0
  · subst k
    simp only [Nat.zero_mul, negChoose, Nat.add_zero, Nat.choose_zero_right, Nat.cast_one,
      sub_self, dvd_zero]
  have hAt : p ^ t ∣ A := (pow_dvd_pow p ht).trans hA
  have hsum : p ^ t ∣ A + k := dvd_add hAt hk
  have hvA := (padicValNat_dvd_iff_le hA0.ne').mp hA
  have hvk := (padicValNat_dvd_iff_le hk0).mp hk
  have hvsum := (padicValNat_dvd_iff_le (by omega : A + k ≠ 0)).mp hsum
  have hd := negChoose_kazandzidis hp hp5 hA0 (Nat.pos_of_ne_zero hk0)
  exact (pow_dvd_pow (p : ℤ) (by omega :
    3 + R + 2 * t + padicValNat p (negChoose A k) ≤
    3 + padicValNat p A + padicValNat p k + padicValNat p (A + k) +
      padicValNat p (negChoose A k))).trans hd

/-- Four relative p-adic errors preserve the sum of all lower-factor valuations. -/
theorem four_factor_congr (q : ℤ) (E va vb vc vd : ℕ) (a b c d A B C D : ℤ)
    (ha : q ^ va ∣ a) (hb : q ^ vb ∣ b) (hc : q ^ vc ∣ c) (hd : q ^ vd ∣ d)
    (hA : q ^ (E + va) ∣ A - a) (hB : q ^ (E + vb) ∣ B - b)
    (hC : q ^ (E + vc) ∣ C - c) (hD : q ^ (E + vd) ∣ D - d) :
    q ^ (E + va + vb + vc + vd) ∣ A * B * C * D - a * b * c * d := by
  have baseline (v : ℕ) (x X : ℤ) (hx : q ^ v ∣ x) (hX : q ^ (E + v) ∣ X - x) :
      q ^ v ∣ X := by
    have hh : q ^ v ∣ X - x := (pow_dvd_pow q (by omega : v ≤ E + v)).trans hX
    simpa only [sub_add_cancel] using dvd_add hh hx
  have hBh := baseline vb b B hb hB
  have hCh := baseline vc c C hc hC
  have hDh := baseline vd d D hd hD
  have h1 := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul hA hBh) hCh) hDh
  have h2 := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul ha hB) hCh) hDh
  have h3 := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul ha hb) hC) hDh
  have h4 := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul ha hb) hc) hD
  simp only [← pow_add] at h1 h2 h3 h4
  rw [show va + (E + vb) + vc + vd = E + va + vb + vc + vd by omega] at h2
  rw [show va + vb + (E + vc) + vd = E + va + vb + vc + vd by omega] at h3
  rw [show va + vb + vc + (E + vd) = E + va + vb + vc + vd by omega] at h4
  have ht : A * B * C * D - a * b * c * d =
      (A - a) * B * C * D + a * (B - b) * C * D +
      a * b * (C - c) * D + a * b * c * (D - d) := by ring
  rw [ht]
  exact dvd_add (dvd_add (dvd_add h1 h2) h3) h4

/-- Strong common-scale congruence for the complete m=4 convolution summand. -/
theorem term_scale_strong {p M R t i j k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hM0 : 0 < M) (hM : p ^ R ∣ M) (ht : t ≤ R)
    (hi : p ^ t ∣ i) (hj : p ^ t ∣ j) (hk : p ^ t ∣ k) :
    (p : ℤ) ^ (3 + R + 2 * t + padicValNat p ((4 * M).choose i) +
      padicValNat p ((4 * M).choose j) + padicValNat p ((4 * M).choose j) +
      padicValNat p (negChoose (6 * M) k)) ∣
      term (M * p) (i * p) (j * p) (k * p) - term M i j k := by
  have h4 : p ^ R ∣ 4 * M := dvd_mul_of_dvd_right hM _
  have h6 : p ^ R ∣ 6 * M := dvd_mul_of_dvd_right hM _
  have hiS := choose_scale_bound hp hp5 h4 hi ht
  have hjS := choose_scale_bound hp hp5 h4 hj ht
  have hkS := negChoose_scale_bound hp hp5 (by omega : 0 < 6 * M) h6 hk ht
  have divNat (n : ℕ) : (p : ℤ) ^ padicValNat p n ∣ (n : ℤ) := by
    exact_mod_cast pow_padicValNat_dvd (p := p) (n := n)
  have hh := four_factor_congr (p : ℤ) (3 + R + 2 * t)
    (padicValNat p ((4 * M).choose i)) (padicValNat p ((4 * M).choose j))
    (padicValNat p ((4 * M).choose j)) (padicValNat p (negChoose (6 * M) k))
    ((4 * M).choose i) ((4 * M).choose j) ((4 * M).choose j) (negChoose (6 * M) k)
    (((4 * M) * p).choose (i * p)) (((4 * M) * p).choose (j * p))
    (((4 * M) * p).choose (j * p)) (negChoose ((6 * M) * p) (k * p))
    (divNat _) (divNat _) (divNat _) (divNat _) hiS hjS hjS hkS
  simpa only [term, pow_two, Nat.mul_assoc, mul_assoc] using hh

/-- A known exact common exponent is recovered without a convention for v_p(0). -/
theorem valuation_eq_of_dvd_not_dvd {p k t : ℕ} (hp : p.Prime)
    (hk : p ^ t ∣ k) (hn : ¬p ^ (t + 1) ∣ k) : padicValNat p k = t := by
  letI : Fact p.Prime := ⟨hp⟩
  have hk0 : k ≠ 0 := fun h => hn (h ▸ dvd_zero _)
  have hlo := (padicValNat_dvd_iff_le hk0).mp hk
  have hhi : padicValNat p k < t + 1 := by
    by_contra h
    exact hn ((padicValNat_dvd_iff_le hk0).mpr (by omega))
  omega

/-- Index-clearing identity for the positive representation of a negative binomial. -/
theorem index_mul_negChoose {A k : ℕ} (hk : 0 < k) :
    k * negChoose A k = A * (A + k - 1).choose (k - 1) := by
  have hh := Nat.choose_succ_right_eq (A + k - 1) (k - 1)
  rw [Nat.sub_add_cancel hk, show A + k - 1 - (k - 1) = A by omega] at hh
  simpa only [negChoose, mul_comm] using hh

/-- A negative binomial carries at least the top valuation minus the index valuation. -/
theorem negChoose_valuation_ge {p A k R : ℕ} (hp : p.Prime) (hA : 0 < A)
    (hk : 0 < k) (hR : p ^ R ∣ A) :
    R - padicValNat p k ≤ padicValNat p (negChoose A k) := by
  letI : Fact p.Prime := ⟨hp⟩
  have h := congrArg (padicValNat p) (index_mul_negChoose (A := A) hk)
  rw [padicValNat.mul hk.ne' (negChoose_pos hA k).ne',
    padicValNat.mul hA.ne' (Nat.choose_pos (by omega)).ne'] at h
  have hvA := (padicValNat_dvd_iff_le hA.ne').mp hR
  omega

/-- The ordinary counterpart in a form convenient for the convolution. -/
theorem choose_valuation_ge {p A k R : ℕ} (hp : p.Prime)
    (hk : 0 < k) (hka : k ≤ A) (hR : p ^ R ∣ A) :
    R - padicValNat p k ≤ padicValNat p (A.choose k) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hvA := (padicValNat_dvd_iff_le (by omega : A ≠ 0)).mp hR
  have hh := padicValNat_choose_ge hp hk hka
  omega

/-- The minimum common index scale forces two lower-factor valuation contributions. -/
theorem term_valuation_mass {p M R t i j k : ℕ} (hp : p.Prime) (hM0 : 0 < M)
    (hM : p ^ R ∣ M) (ht : t < R) (hsum : i + j + k = M)
    (hi : p ^ t ∣ i) (hj : p ^ t ∣ j) (hk : p ^ t ∣ k)
    (hn : ¬(p ^ (t + 1) ∣ i ∧ p ^ (t + 1) ∣ j ∧ p ^ (t + 1) ∣ k)) :
    2 * (R - t) ≤ padicValNat p ((4 * M).choose i) +
      padicValNat p ((4 * M).choose j) + padicValNat p ((4 * M).choose j) +
      padicValNat p (negChoose (6 * M) k) := by
  have h4 : p ^ R ∣ 4 * M := dvd_mul_of_dvd_right hM _
  have h6 : p ^ R ∣ 6 * M := dvd_mul_of_dvd_right hM _
  by_cases hjn : p ^ (t + 1) ∣ j
  · have hMn : p ^ (t + 1) ∣ M := (pow_dvd_pow p (by omega : t + 1 ≤ R)).trans hM
    have hin : ¬p ^ (t + 1) ∣ i := by
      intro hin
      have hkn : p ^ (t + 1) ∣ k := by
        have hd := Nat.dvd_sub (Nat.dvd_sub hMn hin) hjn
        simpa only [show M - i - j = k by omega] using hd
      exact hn ⟨hin, hjn, hkn⟩
    have hkn : ¬p ^ (t + 1) ∣ k := by
      intro hkn
      have hin : p ^ (t + 1) ∣ i := by
        have hd := Nat.dvd_sub (Nat.dvd_sub hMn hjn) hkn
        simpa only [show M - j - k = i by omega] using hd
      exact hn ⟨hin, hjn, hkn⟩
    have hiv := valuation_eq_of_dvd_not_dvd hp hi hin
    have hkv := valuation_eq_of_dvd_not_dvd hp hk hkn
    have hip : 0 < i := Nat.pos_of_ne_zero (fun h => hin (h ▸ dvd_zero _))
    have hkp : 0 < k := Nat.pos_of_ne_zero (fun h => hkn (h ▸ dvd_zero _))
    have hci := choose_valuation_ge hp hip (by omega : i ≤ 4 * M) h4
    have hck := negChoose_valuation_ge hp (by omega : 0 < 6 * M) hkp h6
    rw [hiv] at hci
    rw [hkv] at hck
    omega
  · have hjv := valuation_eq_of_dvd_not_dvd hp hj hjn
    have hjp : 0 < j := Nat.pos_of_ne_zero (fun h => hjn (h ▸ dvd_zero _))
    have hcj := choose_valuation_ge hp hjp (by omega : j ≤ 4 * M) h4
    rw [hjv] at hcj
    omega

/-- Every all-p-divisible convolution index scales with the full cubic modulus. -/
theorem term_scale {p M R i j k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hM0 : 0 < M) (hM : p ^ R ∣ M) (hsum : i + j + k = M) :
    (p : ℤ) ^ (3 * (R + 1)) ∣
      term (M * p) (i * p) (j * p) (k * p) - term M i j k := by
  classical
  let P : ℕ → Prop := fun t => p ^ t ∣ i ∧ p ^ t ∣ j ∧ p ^ t ∣ k
  let t := Nat.findGreatest P R
  have ht : t ≤ R := Nat.findGreatest_le R
  have hP : P t := Nat.findGreatest_spec (P := P) (m := 0) (Nat.zero_le R) (by simp [P])
  have hstrong := term_scale_strong hp hp5 hM0 hM ht hP.1 hP.2.1 hP.2.2
  have he : 3 * (R + 1) ≤ 3 + R + 2 * t + padicValNat p ((4 * M).choose i) +
      padicValNat p ((4 * M).choose j) + padicValNat p ((4 * M).choose j) +
      padicValNat p (negChoose (6 * M) k) := by
    by_cases htR : t = R
    · omega
    · have hlt : t < R := by omega
      have hn : ¬P (t + 1) := Nat.findGreatest_is_greatest (by omega) (by omega : t + 1 ≤ R)
      have hm := term_valuation_mass hp hM0 hM hlt hsum hP.1 hP.2.1 hP.2.2 hn
      omega
  exact (pow_dvd_pow (p : ℤ) he).trans hstrong

/-- The exact n,p,r form needed to pair all-divisible summation blocks. -/
theorem divisible_term_dvd {p n r i j k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hsum : i + j + k = n * p ^ (r - 1)) :
    (p : ℤ) ^ (3 * r) ∣ term (n * p ^ r) (p * i) (p * j) (p * k) -
      term (n * p ^ (r - 1)) i j k := by
  have hM : p ^ (r - 1) ∣ n * p ^ (r - 1) := dvd_mul_left _ _
  have hM0 : 0 < n * p ^ (r - 1) := Nat.mul_pos hn (pow_pos hp.pos _)
  have h := term_scale hp hp5 hM0 hM hsum
  rw [Nat.sub_add_cancel hr] at h
  have hNM : n * p ^ (r - 1) * p = n * p ^ r := by
    rw [Nat.mul_assoc, ← pow_succ, Nat.sub_add_cancel hr]
  simpa only [hNM, Nat.mul_comm i p, Nat.mul_comm j p, Nat.mul_comm k p] using h

end A363990Valuation
end

end

section

open Finset A363990Valuation
noncomputable section
namespace A363990Convolution

/-- The transformed m=4 convolution, including all three zero-index faces. -/
def convolution (N : ℕ) : ℤ :=
  ∑ j ∈ range (N + 1), ∑ i ∈ range (N - j + 1), term N i j (N - j - i)

/-- The all-divisible part; the third index is automatically divisible too. -/
def allDivisible (p N : ℕ) : ℤ :=
  ∑ j ∈ (range (N + 1)).filter (fun j => p ∣ j),
    ∑ i ∈ (range (N - j + 1)).filter (fun i => p ∣ i), term N i j (N - j - i)

/-- Exact multiples reindexing, proved by a finite-set bijection. -/
theorem sum_multiples (p M : ℕ) (hp : 0 < p) (f : ℕ → ℤ) :
    (∑ j ∈ (range (p * M + 1)).filter (fun j => p ∣ j), f j) =
      ∑ j ∈ range (M + 1), f (p * j) := by
  classical
  symm
  apply sum_bij (fun j _ => p * j)
  · intro j hj
    apply mem_filter.mpr
    constructor
    · apply mem_range.mpr
      have hj' : j ≤ M := by have := mem_range.mp hj; omega
      have hm := Nat.mul_le_mul_left p hj'
      omega
    · exact dvd_mul_right p j
  · intro a _ b _ hab
    exact mul_left_cancel₀ hp.ne' hab
  · intro j hj
    obtain ⟨hjr, hjd⟩ := mem_filter.mp hj
    obtain ⟨a, rfl⟩ := hjd
    refine ⟨a, ?_, rfl⟩
    apply mem_range.mpr
    have hm : p * a ≤ p * M := by have := mem_range.mp hjr; omega
    have ha : a ≤ M := le_of_mul_le_mul_left hm hp
    omega
  · intro j _
    rfl

/-- The two nested multiples filters reindex to the lower-scale triangle exactly. -/
theorem allDivisible_reindex (p M : ℕ) (hp : 0 < p) :
    allDivisible p (p * M) =
      ∑ j ∈ range (M + 1), ∑ i ∈ range (M - j + 1),
        term (p * M) (p * i) (p * j) (p * (M - j - i)) := by
  unfold allDivisible
  rw [sum_multiples p M hp]
  apply sum_congr rfl
  intro j _
  rw [show p * M - p * j = p * (M - j) by rw [Nat.mul_sub_left_distrib]]
  rw [sum_multiples p (M - j) hp]
  apply sum_congr rfl
  intro i _
  rw [← Nat.mul_sub_left_distrib]

/-- Every paired all-divisible block has the full cubic modulus. -/
theorem allDivisible_scale {p M R : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hM : 0 < M) (hd : p ^ R ∣ M) :
    (p : ℤ) ^ (3 * (R + 1)) ∣ allDivisible p (p * M) - convolution M := by
  rw [allDivisible_reindex p M hp.pos]
  unfold convolution
  rw [← sum_sub_distrib]
  apply dvd_sum
  intro j hj
  rw [← sum_sub_distrib]
  apply dvd_sum
  intro i hi
  have hj' : j ≤ M := by have := mem_range.mp hj; omega
  have hi' : i ≤ M - j := by have := mem_range.mp hi; omega
  have hs : i + j + (M - j - i) = M := by omega
  have hh := term_scale hp hp5 hM hd hs
  simpa only [Nat.mul_comm M p, Nat.mul_comm i p, Nat.mul_comm j p,
    Nat.mul_comm (M - j - i) p] using hh

/-- Finite-sum assembly needs only the remaining two-unit block estimate. -/
theorem convolution_sub_allDivisible {p N r : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hN : p ^ r ∣ N)
    (hblock : ∀ j, j ≤ N → p ∣ j →
      (p : ℤ) ^ (3 * r) ∣
        ∑ i ∈ (range (N - j + 1)).filter (fun i => ¬p ∣ i), term N i j (N - j - i)) :
    (p : ℤ) ^ (3 * r) ∣ convolution N - allDivisible p N := by
  classical
  unfold convolution allDivisible
  rw [sum_filter, ← sum_sub_distrib]
  apply dvd_sum
  intro j hj
  have hj' : j ≤ N := by have := mem_range.mp hj; omega
  by_cases hjp : p ∣ j
  · rw [if_pos hjp]
    have hpart := sum_filter_add_sum_filter_not (range (N - j + 1)) (fun i => p ∣ i)
      (fun i => term N i j (N - j - i))
    have he : (∑ i ∈ range (N - j + 1), term N i j (N - j - i)) -
        (∑ i ∈ (range (N - j + 1)).filter (fun i => p ∣ i), term N i j (N - j - i)) =
        ∑ i ∈ (range (N - j + 1)).filter (fun i => ¬p ∣ i), term N i j (N - j - i) := by
      linear_combination -hpart
    rw [he]
    exact hblock j hj' hjp
  · rw [if_neg hjp, sub_zero]
    apply dvd_sum
    intro i hi
    have hi' : i ≤ N - j := by have := mem_range.mp hi; omega
    exact unit_j_term hp hr hN (by omega) hjp

/-- Exact convolution tower, parameterized only by the two-unit block estimate. -/
theorem convolution_tower {p n r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hn : 1 ≤ n) (hr : 1 ≤ r)
    (hblock : ∀ j, j ≤ n * p ^ r → p ∣ j →
      (p : ℤ) ^ (3 * r) ∣
        ∑ i ∈ (range (n * p ^ r - j + 1)).filter (fun i => ¬p ∣ i),
          term (n * p ^ r) i j (n * p ^ r - j - i)) :
    convolution (n * p ^ r) ≡ convolution (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ (3 * r)] := by
  have hN : p ^ r ∣ n * p ^ r := dvd_mul_left _ _
  have h1 := convolution_sub_allDivisible hp hr hN hblock
  have hM : 0 < n * p ^ (r - 1) := Nat.mul_pos hn (pow_pos hp.pos _)
  have hd : p ^ (r - 1) ∣ n * p ^ (r - 1) := dvd_mul_left _ _
  have h2 := allDivisible_scale hp hp5 hM hd
  rw [Nat.sub_add_cancel hr] at h2
  have hNM : p * (n * p ^ (r - 1)) = n * p ^ r := by
    rw [mul_comm p, Nat.mul_assoc, ← pow_succ, Nat.sub_add_cancel hr]
  rw [hNM] at h2
  have h := dvd_add h1 h2
  rw [sub_add_sub_cancel] at h
  rw [Int.modEq_iff_dvd]
  simpa only [neg_sub] using dvd_neg.mpr h

end A363990Convolution
end

end

section

namespace A363990LocalVariation

def posUnit (A i : ℕ) : ℤ := (-1 : ℤ)^(i-1) * ((A-1).choose (i-1) : ℤ)

def negUnit (D i : ℕ) : ℤ := ((D+i-1).choose (i-1) : ℤ)

def weight (A D h i : ℕ) : ℤ := posUnit A i * negUnit D (h-i)

theorem posUnit_step (A i : ℕ) (ha : 0 < A) (hi : 0 < i) :
    (i : ℤ) * (posUnit A (i+1) - posUnit A i) = -(A : ℤ) * posUnit A i := by
  have hindex : i - 1 + 1 = i := by omega
  by_cases hle : i ≤ A
  · have h := Nat.choose_succ_right_eq (A-1) (i-1)
    rw [hindex, show A-1-(i-1) = A-i by omega] at h
    have hc := congrArg (fun n : ℕ => (n : ℤ)) h
    push_cast [Nat.cast_sub hle] at hc
    have he : (-1 : ℤ)^i = (-1 : ℤ)^(i-1) * (-1) := by
      rw [← pow_succ, hindex]
    simp only [posUnit, Nat.add_sub_cancel, he]
    linear_combination -(-1 : ℤ)^(i-1) * hc
  · have h0 : (A-1).choose (i-1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h1 : (A-1).choose i = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [posUnit, h0, h1]

theorem negUnit_step (D i : ℕ) (hd : 0 < D) (hi : 0 < i) :
    (i : ℤ) * (negUnit D (i+1) - negUnit D i) = (D : ℤ) * negUnit D i := by
  have hk : i - 1 + 1 = i := by omega
  have hn : D + i - 1 + 1 = D + i := by omega
  have h := Nat.add_one_mul_choose_eq (D+i-1) (i-1)
  rw [hk, hn] at h
  have hc := congrArg (fun n : ℕ => (n : ℤ)) h
  push_cast at hc
  simp only [negUnit, Nat.add_sub_cancel,
    show D + (i+1) - 1 = D+i by omega]
  linear_combination -hc

/-- An index interior to a p^t-block can absorb at most t-1 powers of p. -/
theorem cancel_from_interior {p r t i : ℕ} {z : ℤ} (hp : p.Prime) (hi : i ≠ 0)
    (htr : t ≤ r) (hnot : ¬ p^t ∣ i) (h : (p : ℤ)^r ∣ (i : ℤ)*z) :
    (p : ℤ)^(r-t+1) ∣ z := by
  by_cases hz : z = 0
  · simp [hz]
  have hz' : z.natAbs ≠ 0 := by simpa using hz
  have hnat : p^r ∣ i * z.natAbs := by
    rw [← Int.natAbs_natCast i, ← Int.natAbs_mul, ← Int.natCast_dvd, Nat.cast_pow]
    exact h
  have hs := (hp.pow_dvd_iff_le_factorization (mul_ne_zero hi hz')).mp hnat
  rw [Nat.factorization_mul hi hz', Finsupp.add_apply] at hs
  have hit : i.factorization p < t :=
    lt_of_not_ge (fun he => hnot ((hp.pow_dvd_iff_le_factorization hi).mpr he))
  rw [← Nat.cast_pow, Int.natCast_dvd]
  exact (hp.pow_dvd_iff_le_factorization hz').mpr (by omega)

theorem interior_not_dvd {m L i : ℕ} (_hm : 0 < m)
    (hl : L*m < i) (hu : i < (L+1)*m) : ¬m ∣ i := by
  rintro ⟨k, rfl⟩
  rw [Nat.mul_comm m k] at hl hu
  have hkl := Nat.lt_of_mul_lt_mul_right hl
  have hku := Nat.lt_of_mul_lt_mul_right hu
  omega

theorem block_constant {m modulus L i j : ℕ} (f : ℕ → ℤ)
    (hi0 : L*m < i) (hi1 : i < (L+1)*m) (hj0 : L*m < j) (hj1 : j < (L+1)*m)
    (hstep : ∀ x, L*m < x → x < (L+1)*m → f x ≡ f (x+1) [ZMOD (modulus : ℤ)]) :
    f i ≡ f j [ZMOD (modulus : ℤ)] := by
  have forward (u v : ℕ) (hu : L*m < u) (hv : v < (L+1)*m) (huv : u ≤ v) :
      f u ≡ f v [ZMOD (modulus : ℤ)] := by
    induction v, huv using Nat.le_induction with
    | base => exact Int.ModEq.refl _
    | succ n hn ih =>
      exact (ih (by omega)).trans (hstep n (by omega) (by omega))
  by_cases h : i ≤ j
  · exact forward i j hi0 hj1 h
  · exact (forward j i hj0 hi1 (by omega)).symm

theorem block_constant_of_scaled_step {p r t L i j : ℕ} (hp : p.Prime) (htr : t ≤ r)
    (f : ℕ → ℤ) {a : ℤ} (ha : (p : ℤ)^r ∣ a)
    (hstep : ∀ x : ℕ, 0 < x → (x : ℤ)*(f (x+1)-f x) = a*f x)
    (hi0 : L*p^t < i) (hi1 : i < (L+1)*p^t)
    (hj0 : L*p^t < j) (hj1 : j < (L+1)*p^t) :
    f i ≡ f j [ZMOD (p : ℤ)^(r-t+1)] := by
  rw [← Nat.cast_pow]
  apply block_constant f hi0 hi1 hj0 hj1
  intro x hx0 hx1
  have hx : 0 < x := (Nat.zero_le _).trans_lt hx0
  have hnot := interior_not_dvd (pow_pos hp.pos t) hx0 hx1
  have h : (p : ℤ)^r ∣ (x : ℤ)*(f (x+1)-f x) := by
    rw [hstep x hx]
    exact dvd_mul_of_dvd_left ha (f x)
  rw [Int.modEq_iff_dvd, Nat.cast_pow]
  exact cancel_from_interior hp hx.ne' htr hnot h

/-- Reflection of an open interval whose endpoints are consecutive multiples of m. -/
theorem reflect_block {m L h i j : ℕ}
    (hdvd : m ∣ h) (hi : i < h) (hj : j < h)
    (hi0 : L*m < i) (hi1 : i < (L+1)*m)
    (hj0 : L*m < j) (hj1 : j < (L+1)*m) :
    ∃ L', L'*m < h-i ∧ h-i < (L'+1)*m ∧
      L'*m < h-j ∧ h-j < (L'+1)*m := by
  obtain ⟨Q, hQ⟩ := hdvd
  have hL : L < Q := Nat.lt_of_mul_lt_mul_right
    (by rw [← Nat.mul_comm m Q, ← hQ]; exact hi0.trans hi)
  let L' := Q-(L+1)
  have h1 : L'+(L+1)=Q := Nat.sub_add_cancel hL
  have h2 : (L'+1)+L=Q := by omega
  have he1 : L'*m+(L+1)*m=h := by
    rw [← Nat.add_mul,h1,Nat.mul_comm,← hQ]
  have he2 : (L'+1)*m+L*m=h := by
    rw [← Nat.add_mul,h2,Nat.mul_comm,← hQ]
  exact ⟨L', by omega, by omega, by omega, by omega⟩

/-- The product of shifted binomial factors is locally constant on every full block. -/
theorem weight_variation {p A D h r t L i j : ℕ}
    (hp : p.Prime) (hA : 0 < A) (hD : 0 < D)
    (ha : (p : ℤ)^r ∣ (A : ℤ)) (hd : (p : ℤ)^r ∣ (D : ℤ))
    (htr : t ≤ r) (hh : p^t ∣ h) (hi : i < h) (hj : j < h)
    (hi0 : L*p^t < i) (hi1 : i < (L+1)*p^t)
    (hj0 : L*p^t < j) (hj1 : j < (L+1)*p^t) :
    (p : ℤ)^(r-t+1) ∣ weight A D h i - weight A D h j := by
  have hpos := block_constant_of_scaled_step hp htr (posUnit A)
    (Int.dvd_neg.mpr ha) (fun x hx => posUnit_step A x hA hx) hi0 hi1 hj0 hj1
  obtain ⟨L',hi0',hi1',hj0',hj1'⟩ := reflect_block hh hi hj hi0 hi1 hj0 hj1
  have hneg := block_constant_of_scaled_step hp htr (negUnit D) hd
    (fun x hx => negUnit_step D x hD hx) hi0' hi1' hj0' hj1'
  exact Int.modEq_iff_dvd.mp (hpos.mul hneg).symm

theorem posChoose_scaled {A i : ℕ} (hA : 0 < A) (hi : 0 < i) :
    (i : ℤ) * (A.choose i : ℤ) = (A : ℤ) * ((A-1).choose (i-1) : ℤ) := by
  have h := Nat.add_one_mul_choose_eq (A-1) (i-1)
  rw [show A-1+1=A by omega, show i-1+1=i by omega] at h
  exact_mod_cast (Nat.mul_comm i _).trans h.symm

theorem negChoose_scaled {D i : ℕ} (hi : 0 < i) :
    (i : ℤ) * ((D+i-1).choose i : ℤ) = (D : ℤ) * negUnit D i := by
  have h := Nat.choose_succ_right_eq (D+i-1) (i-1)
  rw [show i-1+1=i by omega, show D+i-1-(i-1)=D by omega] at h
  unfold negUnit
  exact_mod_cast (Nat.mul_comm i _).trans (h.trans (Nat.mul_comm _ D))

/-- Clear the unit denominator in the factorization used by cancellation. -/
theorem weighted_pair_identity {A D h i : ℕ} (hA : 0 < A) (hi : 0 < i) (hh : i < h) :
    (i : ℤ) * ((h-i : ℕ) : ℤ) *
      ((A.choose i : ℤ)*((D+(h-i)-1).choose (h-i) : ℤ)) =
    (A : ℤ)*(D : ℤ)*(-1 : ℤ)^(i-1)*weight A D h i := by
  have hpos := posChoose_scaled hA hi
  have hneg := negChoose_scaled (D := D) (by omega : 0 < h-i)
  unfold weight posUnit
  have hsign : (-1 : ℤ)^(i-1) * (-1)^(i-1) = 1 := by
    rw [← mul_pow, show (-1 : ℤ) * (-1) = 1 by decide, one_pow]
  calc
    _ = ((i : ℤ)*(A.choose i : ℤ)) *
        (((h-i : ℕ) : ℤ)*((D+(h-i)-1).choose (h-i) : ℤ)) := by ring
    _ = (A : ℤ)*(D : ℤ)*((A-1).choose (i-1) : ℤ)*negUnit D (h-i) := by rw [hpos,hneg]; ring
    _ = _ := by
      symm
      calc
        _ = ((-1 : ℤ)^(i-1) * (-1)^(i-1)) *
            ((A : ℤ)*(D : ℤ)*((A-1).choose (i-1) : ℤ)*negUnit D (h-i)) := by ring
        _ = _ := by rw [hsign, one_mul]

end A363990LocalVariation

end

section

namespace A363990Cancellation
open Finset

/-- Decompose an arbitrary complete interval into adjacent equal blocks. -/
theorem sum_range_blocks {R : Type*} [AddCommMonoid R] (M q : ℕ) (f : ℕ → R) :
    ∑ i ∈ range (M*q), f i = ∑ L ∈ range M, ∑ i ∈ Ico (L*q) ((L+1)*q), f i := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ← ih, show (M+1)*q=M*q+q by ring]
    have hd : Disjoint (range (M*q)) (Ico (M*q) (M*q+q)) := by
      rw [Finset.disjoint_left]
      intro x hx hy
      simp only [Finset.mem_range, Finset.mem_Ico] at hx hy
      omega
    have hu : range (M*q+q) = range (M*q) ∪ Ico (M*q) (M*q+q) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
      omega
    rw [hu,Finset.sum_union hd]

/-- A blockwise constant weight of valuation s-t kills a kernel whose
complete p^t-block sums have valuation t. The multiplicity M is arbitrary. -/
theorem weighted_layer_zero {p s t M : ℕ} (hp : p.Prime) (ht : t ≤ s)
    (g b : ℕ → ZMod (p^s))
    (hkernel : ∀ L < M*p^(s-t), (p : ZMod (p^s))^t ∣
      ∑ i ∈ Ico (L*p^t) ((L+1)*p^t), b i)
    (hweight : ∀ L < M*p^(s-t), ∃ c : ZMod (p^s),
      (p : ZMod (p^s))^(s-t) ∣ c ∧
      ∀ i ∈ Ico (L*p^t) ((L+1)*p^t), g i*b i=c*b i) :
    ∑ i ∈ range (M*p^s), g i*b i=0 := by
  have hlen : M*p^s=(M*p^(s-t))*p^t := by
    rw [mul_assoc,← pow_add,Nat.sub_add_cancel ht]
  rw [hlen,sum_range_blocks]
  apply Finset.sum_eq_zero
  intro L hL
  have hL' := Finset.mem_range.mp hL
  obtain ⟨c,hc,hconst⟩ := hweight L hL'
  rw [Finset.sum_congr rfl (fun i hi => hconst i hi),← Finset.mul_sum]
  obtain ⟨a,ha⟩ := hc
  obtain ⟨d,hd⟩ := hkernel L hL'
  rw [ha,hd]
  calc
    _ = (p : ZMod (p^s))^((s-t)+t)*(a*d) := by rw [pow_add]; ring
    _ = 0 := by rw [Nat.sub_add_cancel ht,← Nat.cast_pow,ZMod.natCast_self,zero_mul]

/-- Multiscale cancellation in ZMod(p^s). W_t is any hierarchy of coarse
weights. It is sufficient that each layer difference is blockwise constant
(after multiplying by the kernel), and divisible by p^(s-t). -/
theorem multiscale_zero {p s M : ℕ} (hp : p.Prime)
    (W : ℕ → ℕ → ZMod (p^s)) (b : ℕ → ZMod (p^s))
    (hkernel : ∀ t ≤ s, ∀ L < M*p^(s-t), (p : ZMod (p^s))^t ∣
      ∑ i ∈ Ico (L*p^t) ((L+1)*p^t), b i)
    (hdiff : ∀ t < s, ∀ L < M*p^(s-t), ∃ c : ZMod (p^s),
      (p : ZMod (p^s))^(s-t) ∣ c ∧
      ∀ i ∈ Ico (L*p^t) ((L+1)*p^t),
        (W t i-W (t+1) i)*b i=c*b i)
    (htop : ∀ L < M, ∃ c : ZMod (p^s),
      ∀ i ∈ Ico (L*p^s) ((L+1)*p^s), W s i*b i=c*b i) :
    ∑ i ∈ range (M*p^s), W 0 i*b i=0 := by
  have htel (m i : ℕ) :
      (∑ t ∈ range m, (W t i-W (t+1) i))=W 0 i-W m i := by
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ,ih]; ring
  have hpoint (i : ℕ) : W 0 i*b i=W s i*b i+
      ∑ t ∈ range s, (W t i-W (t+1) i)*b i := by
    rw [← Finset.sum_mul,htel]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hpoint i),Finset.sum_add_distrib,Finset.sum_comm]
  have htop0 : ∑ i ∈ range (M*p^s), W s i*b i=0 := by
    apply weighted_layer_zero hp (le_refl s) (W s) b (hkernel s le_rfl)
    intro L hL
    simp only [Nat.sub_self,pow_zero,mul_one] at hL ⊢
    obtain ⟨c,hc⟩ := htop L hL
    exact ⟨c,one_dvd _,hc⟩
  have hmid : ∑ t ∈ range s, ∑ i ∈ range (M*p^s), (W t i-W (t+1) i)*b i=0 := by
    apply Finset.sum_eq_zero
    intro t ht
    exact weighted_layer_zero hp (Finset.mem_range.mp ht).le
      (fun i => W t i-W (t+1) i) b (hkernel t (Finset.mem_range.mp ht).le)
      (hdiff t (Finset.mem_range.mp ht))
  rw [htop0,hmid,add_zero]

end A363990Cancellation

end

section

namespace A363990Cancellation
open Finset

/-- Reflection reverses the sign of an alternating summand across an odd
integer, without any characteristic assumption on the coefficient ring. -/
theorem neg_one_reflect {R : Type*} [Ring R] {C i : ℕ} (hC : Odd C) (hi : i ≤ C) :
    (-1 : R)^(C-i) = -(-1 : R)^i := by
  have hc : C%2=1 := Nat.odd_iff.mp hC
  have hsum : C-i+i=C := Nat.sub_add_cancel hi
  rw [neg_one_pow_eq_pow_mod_two (C-i),neg_one_pow_eq_pow_mod_two i]
  by_cases he : i%2=0
  · have hj : (C-i)%2=1 := by omega
    rw [he,hj]
    simp
  · have he' : i%2=1 := by omega
    have hj : (C-i)%2=0 := by omega
    rw [he',hj]
    simp

/-- Alternating reciprocal squares cancel on every complete open unit block.
The unit filter is preserved by reflection, and the block width is odd. -/
theorem signed_inverse_square_block {p t L : ℕ}
    (hp : p.Prime) (hp3 : 3 ≤ p) (ht : 1 ≤ t) :
    ∑ i ∈ (Ioo (L*p^t) ((L+1)*p^t)).filter (fun i => ¬p∣i),
      (-1 : ZMod (p^t))^i * ((i : ZMod (p^t))^2)⁻¹ = 0 := by
  classical
  let q := p^t
  let C := (2*L+1)*q
  let S := (Ioo (L*q) ((L+1)*q)).filter (fun i => ¬p∣i)
  have hqpos : 0 < q := pow_pos hp.pos t
  have hpq : p ∣ q := dvd_pow_self p (by omega)
  have hC : C=L*q+(L+1)*q := by dsimp [C]; ring
  have hCodd : Odd C := by
    dsimp [C,q]
    exact (show Odd (2*L+1) from ⟨L,rfl⟩).mul (hp.odd_of_ne_two (by omega)).pow
  have hpc : p ∣ C := hpq.trans (dvd_mul_left q (2*L+1))
  have hmem (i : ℕ) (hi : i ∈ S) : C-i ∈ S := by
    simp only [S,mem_filter,mem_Ioo] at hi ⊢
    refine ⟨⟨by omega,by omega⟩,?_⟩
    intro hd
    have hsum : C-i+i=C := Nat.sub_add_cancel (by omega)
    exact hi.2 ((Nat.dvd_add_right hd).mp (hsum.symm ▸ hpc))
  apply Finset.sum_involution (fun i _ => C-i)
  · intro i hi
    have hb : L*q < i ∧ i < (L+1)*q := (Finset.mem_Ioo.mp (Finset.mem_filter.mp hi).1)
    have hiC : i ≤ C := by omega
    have hc0 : (C : ZMod q)=0 := by dsimp [C]; simp
    have href : ((C-i : ℕ) : ZMod q)=-(i : ZMod q) := by
      rw [Nat.cast_sub hiC,hc0,zero_sub]
    have hsign := neg_one_reflect (R := ZMod q) hCodd hiC
    change (-1 : ZMod q)^i * ((i : ZMod q)^2)⁻¹ +
      (-1 : ZMod q)^(C-i) * (((C-i : ℕ) : ZMod q)^2)⁻¹=0
    rw [href,neg_sq,hsign]
    ring
  · intro i hi _ heq
    have hb : L*q < i ∧ i < (L+1)*q := (Finset.mem_Ioo.mp (Finset.mem_filter.mp hi).1)
    have hodd := Nat.odd_iff.mp hCodd
    omega
  · exact hmem
  · intro i hi
    have hb : L*q < i ∧ i < (L+1)*q := (Finset.mem_Ioo.mp (Finset.mem_filter.mp hi).1)
    omega

/-- Reflection cancellation for an arbitrary even function of the unit residue. -/
theorem alternating_even_block {R : Type*} [Ring R] {p t L : ℕ}
    (hp : p.Prime) (hp3 : 3 ≤ p) (ht : 1 ≤ t)
    (F : ZMod (p^t) → R) (hF : ∀ x, F (-x)=F x) :
    ∑ i ∈ (Ioo (L*p^t) ((L+1)*p^t)).filter (fun i => ¬p∣i),
      (-1 : R)^i * F (i : ZMod (p^t)) = 0 := by
  classical
  let q := p^t
  let C := (2*L+1)*q
  let S := (Ioo (L*q) ((L+1)*q)).filter (fun i => ¬p∣i)
  have hqpos : 0 < q := pow_pos hp.pos t
  have hpq : p ∣ q := dvd_pow_self p (by omega)
  have hC : C=L*q+(L+1)*q := by dsimp [C]; ring
  have hCodd : Odd C := by
    dsimp [C,q]
    exact (show Odd (2*L+1) from ⟨L,rfl⟩).mul (hp.odd_of_ne_two (by omega)).pow
  have hpc : p ∣ C := hpq.trans (dvd_mul_left q (2*L+1))
  have hmem (i : ℕ) (hi : i ∈ S) : C-i ∈ S := by
    simp only [S,mem_filter,mem_Ioo] at hi ⊢
    refine ⟨⟨by omega,by omega⟩,?_⟩
    intro hd
    have hsum : C-i+i=C := Nat.sub_add_cancel (by omega)
    exact hi.2 ((Nat.dvd_add_right hd).mp (hsum.symm ▸ hpc))
  apply Finset.sum_involution (fun i _ => C-i)
  · intro i hi
    have hb : L*q < i ∧ i < (L+1)*q := (Finset.mem_Ioo.mp (Finset.mem_filter.mp hi).1)
    have hiC : i ≤ C := by omega
    have hc0 : (C : ZMod q)=0 := by dsimp [C]; simp
    have href : ((C-i : ℕ) : ZMod q)=-(i : ZMod q) := by
      rw [Nat.cast_sub hiC,hc0,zero_sub]
    have hsign := neg_one_reflect (R := R) hCodd hiC
    change (-1 : R)^i * F (i : ZMod q) +
      (-1 : R)^(C-i) * F ((C-i : ℕ) : ZMod q)=0
    rw [href,hF,hsign,neg_mul,add_neg_cancel]
  · intro i hi _ heq
    have hb : L*q < i ∧ i < (L+1)*q := (Finset.mem_Ioo.mp (Finset.mem_filter.mp hi).1)
    have hodd := Nat.odd_iff.mp hCodd
    omega
  · exact hmem
  · intro i hi
    have hb : L*q < i ∧ i < (L+1)*q := (Finset.mem_Ioo.mp (Finset.mem_filter.mp hi).1)
    omega

/-- The actual signed two-unit-index denominator on a complete block.
The fixed h is divisible by the block modulus. -/
theorem signed_kernel_block {p t L h : ℕ}
    (hp : p.Prime) (hp3 : 3 ≤ p) (ht : 1 ≤ t) (hh : p^t ∣ h)
    (hblock : (L+1)*p^t ≤ h) :
    ∑ i ∈ (Ioo (L*p^t) ((L+1)*p^t)).filter (fun i => ¬p∣i),
      (-1 : ZMod (p^t))^i * ((i : ZMod (p^t))*((h-i : ℕ) : ZMod (p^t)))⁻¹=0 := by
  let F : ZMod (p^t) → ZMod (p^t) := fun x => (x*(-x))⁻¹
  have hF : ∀ x, F (-x)=F x := by
    intro x
    dsimp [F]
    congr 1
    ring
  have hc := alternating_even_block hp hp3 ht F hF (L := L)
  have hz : (h : ZMod (p^t))=0 := (ZMod.natCast_eq_zero_iff h _).mpr hh
  convert hc using 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := (Finset.mem_Ioo.mp (Finset.mem_filter.mp hi).1).2
  have hih : i ≤ h := by omega
  dsimp [F]
  rw [Nat.cast_sub hih,hz,zero_sub]


end A363990Cancellation

end

section

namespace A363990Cancellation
open Finset

noncomputable def unitKernel (p s h i : ℕ) : ZMod (p^s) :=
  if p ∣ i then 0 else (-1)^i * ((i : ZMod (p^s))*((h-i : ℕ) : ZMod (p^s)))⁻¹

theorem map_inverse_unit {m n : ℕ} (f : ZMod m →+* ZMod n) (x : ZMod m)
    (hx : IsUnit x) : f x⁻¹=(f x)⁻¹ := by
  have hunit : IsUnit (f x) := hx.map f
  calc
    f x⁻¹ = 1*f x⁻¹ := (one_mul _).symm
    _ = ((f x)⁻¹*f x)*f x⁻¹ := by rw [ZMod.inv_mul_of_unit _ hunit]
    _ = (f x)⁻¹*(f x*f x⁻¹) := by rw [mul_assoc]
    _ = (f x)⁻¹ := by rw [← map_mul,ZMod.mul_inv_of_unit _ hx,map_one,mul_one]

theorem pow_dvd_of_projection_zero {p s t : ℕ} (hp : p.Prime) (ht : t ≤ s)
    (x : ZMod (p^s))
    (hx : ZMod.castHom (pow_dvd_pow p ht) (ZMod (p^t)) x=0) :
    (p : ZMod (p^s))^t ∣ x := by
  let : NeZero (p^s) := ⟨pow_ne_zero s hp.ne_zero⟩
  have hv : ((x.val : ℕ) : ZMod (p^t))=0 := by
    rw [← ZMod.natCast_zmod_val x] at hx
    simpa only [map_natCast] using hx
  obtain ⟨a,ha⟩ := (ZMod.natCast_eq_zero_iff x.val (p^t)).mp hv
  refine ⟨(a : ZMod (p^s)),?_⟩
  calc
    x = (x.val : ZMod (p^s)) := (ZMod.natCast_zmod_val x).symm
    _ = (p : ZMod (p^s))^t*(a : ZMod (p^s)) := by rw [ha,Nat.cast_mul,Nat.cast_pow]

theorem unitKernel_map {p s t h i : ℕ} (hp : p.Prime) (ht : t ≤ s)
    (hh : p ∣ h) (hi : i ≤ h) :
    ZMod.castHom (pow_dvd_pow p ht) (ZMod (p^t)) (unitKernel p s h i)=unitKernel p t h i := by
  classical
  unfold unitKernel
  by_cases hip : p ∣ i
  · simp only [if_pos hip,map_zero]
  · simp only [if_neg hip]
    have hhi : ¬p ∣ h-i := by
      intro hd
      have he : h-i+i=h := Nat.sub_add_cancel hi
      exact hip ((Nat.dvd_add_right hd).mp (he.symm ▸ hh))
    have hunit (j : ℕ) (hj : ¬p∣j) : IsUnit (j : ZMod (p^s)) :=
      (ZMod.isUnit_iff_coprime _ _).mpr (((hp.coprime_iff_not_dvd.mpr hj).symm).pow_right s)
    rw [map_mul,map_pow,map_neg,map_one,
      map_inverse_unit _ _ ((hunit i hip).mul (hunit (h-i) hhi)),map_mul,map_natCast,map_natCast]

theorem unitKernel_block_zero {p t L h : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (ht : 1 ≤ t) (hh : p^t ∣ h) (hblock : (L+1)*p^t ≤ h) :
    ∑ i ∈ Ico (L*p^t) ((L+1)*p^t), unitKernel p t h i=0 := by
  classical
  have hpq : p ∣ p^t := dvd_pow_self p (by omega)
  have hlow : p ∣ L*p^t := dvd_mul_of_dvd_right hpq L
  have hf : (Ico (L*p^t) ((L+1)*p^t)).filter (fun i => ¬p∣i) =
      (Ioo (L*p^t) ((L+1)*p^t)).filter (fun i => ¬p∣i) := by
    ext i
    simp only [mem_filter,mem_Ico,mem_Ioo]
    constructor
    · rintro ⟨⟨hlo,hhi⟩,hn⟩
      refine ⟨⟨?_,hhi⟩,hn⟩
      by_contra h
      have he : i=L*p^t := by omega
      exact hn (he ▸ hlow)
    · rintro ⟨⟨hlo,hhi⟩,hn⟩
      exact ⟨⟨hlo.le,hhi⟩,hn⟩
  calc
    _ = ∑ i ∈ (Ico (L*p^t) ((L+1)*p^t)).filter (fun i => ¬p∣i),
        (-1 : ZMod (p^t))^i*((i : ZMod (p^t))*((h-i : ℕ) : ZMod (p^t)))⁻¹ := by
      rw [sum_filter]
      apply sum_congr rfl
      intro i hi
      by_cases hip : p∣i <;> simp [unitKernel,hip]
    _ = 0 := by rw [hf]; exact signed_kernel_block hp hp3 ht hh hblock

/-- Complete block kernel sums gain their full block power in every ambient
prime-power quotient, including at t=0. -/
theorem unitKernel_block_dvd {p s t M L : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (ht : t ≤ s) (hL : L < M*p^(s-t)) :
    (p : ZMod (p^s))^t ∣
      ∑ i ∈ Ico (L*p^t) ((L+1)*p^t), unitKernel p s (M*p^s) i := by
  by_cases ht0 : t=0
  · subst t
    simp
  · apply pow_dvd_of_projection_zero hp ht
    rw [map_sum]
    have hbound : (L+1)*p^t ≤ M*p^s := by
      calc
        _ ≤ (M*p^(s-t))*p^t := Nat.mul_le_mul_right _ (by omega)
        _ = _ := by rw [mul_assoc,← pow_add,Nat.sub_add_cancel ht]
    have hpH : p ∣ M*p^s := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) M
    rw [sum_congr rfl (fun i hi => unitKernel_map hp ht hpH
      (by have hh := (mem_Ico.mp hi).2; omega))]
    exact unitKernel_block_zero hp hp3 (by omega)
      (dvd_mul_of_dvd_right (pow_dvd_pow p ht) M) hbound

end A363990Cancellation

end

section

namespace A363990Cancellation
open Finset

noncomputable def coarseWeight (p : ℕ) (W : ℕ → ℤ) (t i : ℕ) : ℤ :=
  if t=0 then W i else W ((i/p^t)*p^t+1)

theorem block_quotient {q L i : ℕ} (hq : 0 < q) (hi : L*q ≤ i ∧ i < (L+1)*q) : i/q=L := by
  apply Nat.le_antisymm
  · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hq).mpr hi.2)
  · exact (Nat.le_div_iff_mul_le hq).mpr hi.1

theorem coarse_on_block {p t L i : ℕ} (hp : 0 < p) (ht : 1 ≤ t)
    (W : ℕ → ℤ) (hi : L*p^t ≤ i ∧ i < (L+1)*p^t) :
    coarseWeight p W t i=coarseWeight p W t (L*p^t) := by
  have hq := pow_pos hp t
  have hdiv := block_quotient hq hi
  simp only [coarseWeight,show ¬t=0 by omega,if_false,hdiv,Nat.mul_div_cancel _ hq]

theorem parent_quotient {p t L i : ℕ} (hp : 0 < p)
    (hi : L*p^t ≤ i ∧ i < (L+1)*p^t) : i/p^(t+1)=L/p := by
  rw [pow_succ,← Nat.div_div_eq_div_mul,block_quotient (pow_pos hp t) hi]

theorem coarse_parent_on_block {p t L i : ℕ} (hp : 0 < p)
    (W : ℕ → ℤ) (hi : L*p^t ≤ i ∧ i < (L+1)*p^t) :
    coarseWeight p W (t+1) i=coarseWeight p W (t+1) (L*p^t) := by
  have hstart : L*p^t/p^(t+1)=L/p := by
    rw [pow_succ,← Nat.div_div_eq_div_mul,Nat.mul_div_cancel _ (pow_pos hp t)]
  simp only [coarseWeight,Nat.succ_ne_zero,if_false,parent_quotient hp hi,hstart]

theorem cast_int_pow_dvd {p s e d : ℕ} {a : ℤ}
    (h : (p : ℤ)^e ∣ a) (hd : d ≤ e) :
    (p : ZMod (p^s))^d ∣ (a : ZMod (p^s)) := by
  have hcast : (p : ZMod (p^s))^e ∣ (a : ZMod (p^s)) := by
    obtain ⟨c,hc⟩ := h
    refine ⟨(c : ZMod (p^s)),?_⟩
    rw [hc,Int.cast_mul,Int.cast_pow,Int.cast_natCast]
  exact (pow_dvd_pow (p : ZMod (p^s)) hd).trans hcast

/-- Local integer variation on all complete open blocks supplies precisely
the coarse layer divisibility needed by multiscale cancellation. -/
theorem weighted_zero_of_variation {p r s M : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hs : 1 ≤ s) (hsr : s ≤ r) (W : ℕ → ℤ)
    (hvar : ∀ t, 1 ≤ t → t ≤ s → ∀ L i j,
      i < M*p^s → j < M*p^s →
      L*p^t < i → i < (L+1)*p^t → L*p^t < j → j < (L+1)*p^t →
      (p : ℤ)^(r-t+1) ∣ W i-W j) :
    ∑ i ∈ range (M*p^s), (W i : ZMod (p^s))*unitKernel p s (M*p^s) i=0 := by
  let C : ℕ → ℕ → ZMod (p^s) := fun t i => (coarseWeight p W t i : ZMod (p^s))
  have hkernel : ∀ t ≤ s, ∀ L < M*p^(s-t), (p : ZMod (p^s))^t ∣
      ∑ i ∈ Ico (L*p^t) ((L+1)*p^t), unitKernel p s (M*p^s) i := by
    intro t ht L hL
    exact unitKernel_block_dvd hp hp3 ht hL
  have hdiff : ∀ t < s, ∀ L < M*p^(s-t), ∃ c : ZMod (p^s),
      (p : ZMod (p^s))^(s-t) ∣ c ∧
      ∀ i ∈ Ico (L*p^t) ((L+1)*p^t),
        (C t i-C (t+1) i)*unitKernel p s (M*p^s) i=c*unitKernel p s (M*p^s) i := by
    intro t ht L hL
    have hlen : (M*p^(s-t))*p^t=M*p^s := by
      rw [mul_assoc,← pow_add,Nat.sub_add_cancel ht.le]
    have hupper : (L+1)*p^t ≤ M*p^s := by
      calc _ ≤ (M*p^(s-t))*p^t := Nat.mul_le_mul_right _ (by omega)
           _ = _ := hlen
    by_cases ht0 : t=0
    · subst t
      simp only [pow_zero,mul_one,Nat.sub_zero] at hL hupper ⊢
      by_cases hLp : p ∣ L
      · refine ⟨0,dvd_zero _,?_⟩
        intro i hi
        have he : i=L := by have := mem_Ico.mp hi; omega
        subst i
        simp [unitKernel,hLp]
      · let j := L/p*p+1
        have hlo : L/p*p < L := by
          have hd := Nat.mod_add_div L p
          rw [Nat.mul_comm p (L/p)] at hd
          have hm : L%p ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hLp
          omega
        have hhi : L < (L/p+1)*p :=
          (Nat.div_lt_iff_lt_mul hp.pos).mp (Nat.lt_succ_self _)
        have hj0 : L/p*p < j := by dsimp [j]; omega
        have hj1 : j < (L/p+1)*p := by dsimp [j]; nlinarith
        have hjL : j ≤ L := by dsimp [j]; omega
        have hv := hvar 1 (by omega) hs (L/p) L j hL (lt_of_le_of_lt hjL hL)
          (by simpa only [pow_one] using hlo) (by simpa only [pow_one] using hhi)
          (by simpa only [pow_one] using hj0) (by simpa only [pow_one] using hj1)
        have hv' : (p : ℤ)^r ∣ W L-W j := by
          simpa only [show r-1+1=r by omega] using hv
        refine ⟨((W L-W j : ℤ) : ZMod (p^s)),cast_int_pow_dvd hv' hsr,?_⟩
        intro i hi
        have he : i=L := by have := mem_Ico.mp hi; omega
        subst i
        dsimp [C,coarseWeight,j]
        simp only [pow_one,Int.cast_sub]
    · let a := L*p^t+1
      let b := (L/p)*p^(t+1)+1
      have ht1 : 1 ≤ t := by omega
      have hq : 1 < p^t := one_lt_pow₀ (by omega : 1 < p) (by omega)
      have hLlo : L/p*p ≤ L := Nat.div_mul_le_self L p
      have hLhi : L < (L/p+1)*p :=
        (Nat.div_lt_iff_lt_mul hp.pos).mp (Nat.lt_succ_self _)
      have hparent0 : (L/p)*p^(t+1) ≤ L*p^t := by
        calc _ = (L/p*p)*p^t := by rw [pow_succ]; ring
             _ ≤ _ := Nat.mul_le_mul_right _ hLlo
      have hparent1 : (L+1)*p^t ≤ (L/p+1)*p^(t+1) := by
        calc _ ≤ ((L/p+1)*p)*p^t := Nat.mul_le_mul_right _ (by omega)
             _ = _ := by rw [pow_succ]; ring
      have ha0 : (L/p)*p^(t+1) < a := by dsimp [a]; omega
      have ha1 : a < (L/p+1)*p^(t+1) := by dsimp [a]; nlinarith
      have hb0 : (L/p)*p^(t+1) < b := by dsimp [b]; omega
      have hb1 : b < (L/p+1)*p^(t+1) := by
        have hq1 : 1 < p^(t+1) := one_lt_pow₀ (by omega : 1 < p) (by omega)
        dsimp [b]
        nlinarith
      have haH : a < M*p^s := by dsimp [a]; nlinarith
      have hbH : b < M*p^s := by dsimp [b,a] at *; omega
      have hv := hvar (t+1) (by omega) (by omega) (L/p) a b haH hbH ha0 ha1 hb0 hb1
      have hv' : (p : ℤ)^(r-t) ∣ W a-W b := by
        simpa only [show r-(t+1)+1=r-t by omega] using hv
      have hcs : coarseWeight p W t (L*p^t)=W a := by
        simp only [coarseWeight,ht0,if_false,Nat.mul_div_cancel _ (pow_pos hp.pos t)]
        rfl
      have hcp : coarseWeight p W (t+1) (L*p^t)=W b := by
        have hdiv : L*p^t/p^(t+1)=L/p := by
          rw [pow_succ,← Nat.div_div_eq_div_mul,Nat.mul_div_cancel _ (pow_pos hp.pos t)]
        simp only [coarseWeight,Nat.succ_ne_zero,if_false,hdiv]
        rfl
      refine ⟨((W a-W b : ℤ) : ZMod (p^s)),
        cast_int_pow_dvd hv' (Nat.sub_le_sub_right hsr t),?_⟩
      intro i hi
      have hi' := mem_Ico.mp hi
      dsimp [C]
      rw [coarse_on_block hp.pos ht1 W hi',coarse_parent_on_block hp.pos W hi',hcs,hcp,Int.cast_sub]
  have htop : ∀ L < M, ∃ c : ZMod (p^s),
      ∀ i ∈ Ico (L*p^s) ((L+1)*p^s), C s i*unitKernel p s (M*p^s) i=
        c*unitKernel p s (M*p^s) i := by
    intro L hL
    refine ⟨C s (L*p^s),?_⟩
    intro i hi
    dsimp [C]
    rw [coarse_on_block hp.pos hs W (mem_Ico.mp hi)]
  have hc := multiscale_zero hp C (unitKernel p s (M*p^s)) hkernel hdiff htop
  simpa [C,coarseWeight] using hc

/-- The full signed two-unit-index weighted cancellation needed by the m=4
convolution, using the actual positive-top binomial weights. -/
theorem weighted_unit_sum_zero {p r s A D h : ℕ}
    (hp : p.Prime) (hp3 : 3 ≤ p) (hs : 1 ≤ s) (hsr : s ≤ r)
    (hdivh : p^s ∣ h) (hA : 0 < A) (hD : 0 < D)
    (ha : (p : ℤ)^r ∣ (A : ℤ)) (hd : (p : ℤ)^r ∣ (D : ℤ)) :
    ∑ i ∈ range h, (A363990LocalVariation.weight A D h i : ZMod (p^s))*
      unitKernel p s h i=0 := by
  obtain ⟨M,hM⟩ := hdivh
  have he : h=M*p^s := by rw [hM,Nat.mul_comm]
  subst h
  rw [he]
  apply weighted_zero_of_variation hp hp3 hs hsr (A363990LocalVariation.weight A D (M*p^s))
  intro t ht hts L i j hi hj hi0 hi1 hj0 hj1
  exact A363990LocalVariation.weight_variation hp hA hD ha hd (hts.trans hsr)
    (dvd_mul_of_dvd_right (pow_dvd_pow p hts) M) hi hj hi0 hi1 hj0 hj1

/-- Filtered-index form, including the original convolution endpoint h.
That endpoint is excluded automatically since p divides h. -/
theorem weighted_unit_sum_zero_filter {p r s A D h : ℕ}
    (hp : p.Prime) (hp3 : 3 ≤ p) (hs : 1 ≤ s) (hsr : s ≤ r)
    (hdivh : p^s ∣ h) (hA : 0 < A) (hD : 0 < D)
    (ha : (p : ℤ)^r ∣ (A : ℤ)) (hd : (p : ℤ)^r ∣ (D : ℤ)) :
    ∑ i ∈ (range (h+1)).filter (fun i => ¬p∣i),
      (A363990LocalVariation.weight A D h i : ZMod (p^s)) *
      (-1)^i*((i : ZMod (p^s))*((h-i : ℕ) : ZMod (p^s)))⁻¹=0 := by
  classical
  have hc := weighted_unit_sum_zero hp hp3 hs hsr hdivh hA hD ha hd
  have hph : p ∣ h := (dvd_pow_self p (by omega)).trans hdivh
  have he : ∑ i ∈ range (h+1), (A363990LocalVariation.weight A D h i : ZMod (p^s))*
      unitKernel p s h i=0 := by
    rw [Finset.sum_range_succ,hc]
    simp [unitKernel,hph]
  rw [sum_filter]
  convert he using 1
  apply sum_congr rfl
  intro i hi
  by_cases hip : p∣i <;> simp [unitKernel,hip,mul_assoc]

end A363990Cancellation

end

section

open Finset

namespace A363990LocalVariation

/-- The integer summand, with the nonunit indices omitted by a zero value. -/
def unitTerm (p A D h i : ℕ) : ℤ :=
  if p ∣ i then 0 else (A.choose i : ℤ) * ((D+(h-i)-1).choose (h-i) : ℤ)

/-- The signed inverse denominator in the quotient calculation. -/
def signedKernel (p s h i : ℕ) : ZMod (p^s) :=
  if p ∣ i then 0 else
    (-1 : ZMod (p^s))^i * ((i : ZMod (p^s)) * ((h-i : ℕ) : ZMod (p^s)))⁻¹

theorem not_dvd_complement {p h i : ℕ} (hi : i ≤ h) (hh : p ∣ h)
    (hpi : ¬ p ∣ i) : ¬ p ∣ h-i := by
  intro hrem
  exact hpi (by simpa only [Nat.sub_sub_self hi] using Nat.dvd_sub hh hrem)

/-- Convert a kernel cancellation modulo p^s into the integer congruence
    modulo p^(2r+s), by dividing both factors by p^r before reducing. -/
theorem unit_sum_dvd_of_kernel_zero {p A D h r s : ℕ} (hp : p.Prime)
    (hA : 0 < A) (hs : 1 ≤ s) (hr : 1 ≤ r) (hh : p^s ∣ h)
    (hAdvd : (p : ℤ)^r ∣ (A : ℤ)) (hDdvd : (p : ℤ)^r ∣ (D : ℤ))
    (hker : ∑ i ∈ range h, (weight A D h i : ZMod (p^s)) * signedKernel p s h i = 0) :
    (p : ℤ)^(2*r+s) ∣ ∑ i ∈ range h, unitTerm p A D h i := by
  let R := ZMod (p^s)
  let P : ℤ := (p : ℤ)^(2*r)
  have hP : P ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  obtain ⟨a,ha⟩ := hAdvd
  obtain ⟨d,hd⟩ := hDdvd
  have had : (A : ℤ)*(D : ℤ) = P*(a*d) := by
    rw [ha,hd,show P = (p : ℤ)^r*(p : ℤ)^r by rw [← pow_add, ← two_mul]]
    ring
  have hph : p ∣ h := (dvd_pow_self p (by omega : s ≠ 0)).trans hh
  let q (i : ℕ) : ℤ := unitTerm p A D h i / P
  have hfac (i : ℕ) (hi : i < h) : unitTerm p A D h i = P*q i := by
    have hdiv : P ∣ unitTerm p A D h i := by
      by_cases hpi : p ∣ i
      · simp [unitTerm, hpi]
      have hi0 : 0 < i := by
        apply Nat.pos_of_ne_zero
        intro hz
        subst i
        exact hpi (dvd_zero p)
      have hrem := not_dvd_complement hi.le hph hpi
      have hden : ¬ p ∣ i*(h-i) := fun h => (hp.dvd_mul.mp h).elim hpi hrem
      have H := weighted_pair_identity (D := D) hA hi0 hi
      rw [had] at H
      have hmul : (p : ℤ)^(2*r) ∣ ((i*(h-i) : ℕ) : ℤ)*unitTerm p A D h i := by
        rw [Nat.cast_mul, unitTerm, if_neg hpi,H]
        change P ∣ P*(a*d)*(-1 : ℤ)^(i-1)*weight A D h i
        exact ⟨(a*d)*(-1 : ℤ)^(i-1)*weight A D h i, by ring⟩
      have hcancel := cancel_from_interior hp (Nat.mul_ne_zero hi0.ne' (by omega))
        (t := 1) (by omega : 1 ≤ 2*r) (by simpa using hden) hmul
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ 2*r)] using hcancel
    change unitTerm p A D h i = P * (unitTerm p A D h i / P)
    rw [mul_comm, Int.ediv_mul_cancel hdiv]
  have hcast (i : ℕ) (hi : i < h) :
      (q i : R) = -((a*d : ℤ) : R) * ((weight A D h i : ℤ) : R) * signedKernel p s h i := by
    by_cases hpi : p ∣ i
    · simp [q, unitTerm, signedKernel, hpi]
    have hi0 : 0 < i := by
        apply Nat.pos_of_ne_zero
        intro hz
        subst i
        exact hpi (dvd_zero p)
    have hrem := not_dvd_complement hi.le hph hpi
    have hden : ¬ p ∣ i*(h-i) := fun h => (hp.dvd_mul.mp h).elim hpi hrem
    have hcop : (i*(h-i)).Coprime (p^s) :=
      ((hp.coprime_iff_not_dvd.mpr hden).symm).pow_right s
    have H := weighted_pair_identity (D := D) hA hi0 hi
    rw [had] at H
    have H' : ((i*(h-i) : ℕ) : ℤ)*q i =
        (a*d)*(-1 : ℤ)^(i-1)*weight A D h i := by
      have hf := hfac i hi
      rw [unitTerm, if_neg hpi] at hf
      rw [hf] at H
      apply mul_left_cancel₀ hP
      push_cast
      linear_combination H
    have hsign : (-1 : ℤ)^(i-1) = -(-1)^i := by
      have he : (-1 : ℤ)^i = (-1 : ℤ)^(i-1)*(-1) := by
        rw [← pow_succ, Nat.sub_add_cancel hi0]
      rw [he]
      ring
    rw [hsign] at H'
    have HC := congrArg (Int.castRingHom R) H'
    simp only [map_mul, map_natCast, map_neg, map_pow, map_one] at HC
    rw [signedKernel, if_neg hpi]
    rw [Nat.cast_mul] at HC
    change (i : R) * ((h-i : ℕ) : R) * (q i : R) =
      (a : R) * (d : R) * -(-1 : R)^i * (weight A D h i : R) at HC
    have hI := ZMod.coe_mul_inv_eq_one (i*(h-i)) hcop
    rw [Nat.cast_mul] at hI
    calc
      _ = (((i : R)*((h-i : ℕ) : R))*(q i : R)) *
          ((i : R)*((h-i : ℕ) : R))⁻¹ := by
        rw [mul_comm ((i : R)*((h-i : ℕ) : R)) (q i : R), mul_assoc, hI, mul_one]
      _ = _ := by rw [HC, Int.cast_mul]; ring
  have hzero : ((∑ i ∈ range h, q i : ℤ) : R) = 0 := by
    rw [Int.cast_sum]
    calc
      _ = -((a*d : ℤ) : R) * ∑ i ∈ range h,
          (weight A D h i : R)*signedKernel p s h i := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i hi
        rw [hcast i (mem_range.mp hi), mul_assoc]
      _ = 0 := by rw [hker,mul_zero]
  have hq : (p : ℤ)^s ∣ ∑ i ∈ range h, q i := by
    rw [← Nat.cast_pow]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  have hsum : ∑ i ∈ range h, unitTerm p A D h i = P * ∑ i ∈ range h, q i := by
    rw [mul_sum]
    exact sum_congr rfl fun i hi => hfac i (mem_range.mp hi)
  rw [hsum,pow_add]
  exact mul_dvd_mul_left P hq

end A363990LocalVariation

end

section

open Finset A363990Valuation

namespace A363990LocalVariation

/-- The squared middle factor supplies the powers left after cancellation of the unit block. -/
theorem middle_square_dvd {p r N j s : ℕ} (hp : p.Prime) (hN : p^r ∣ N)
    (hj : j ≤ N) (hh : N-j ≠ 0) (hs : s = min r (padicValNat p (N-j)))
    (hspan : p^s ∣ N-j) :
    (p : ℤ)^(2*(r-s)) ∣ ((4*N).choose j : ℤ)^2 := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hsr : s = r
  · simp [hsr]
  have hlt : s < r := by
    have hle : s ≤ r := hs.trans_le (min_le_left _ _)
    omega
  have hnot : ¬ p^(s+1) ∣ N-j := by
    intro h
    have hv := (padicValNat_dvd_iff_le hh).mp h
    have hmin : s+1 ≤ min r (padicValNat p (N-j)) := le_min (by omega) hv
    omega
  have hjdvd : p^s ∣ j := by
    simpa only [Nat.sub_sub_self hj] using
      Nat.dvd_sub ((pow_dvd_pow p hlt.le).trans hN) hspan
  have hjnot : ¬ p^(s+1) ∣ j := fun h =>
    hnot (Nat.dvd_sub ((pow_dvd_pow p (by omega : s+1 ≤ r)).trans hN) h)
  have hj0 : 0 < j := Nat.pos_of_ne_zero (fun h => hjnot (h ▸ dvd_zero _))
  have hjv := valuation_eq_of_dvd_not_dvd hp hjdvd hjnot
  have htop : p^r ∣ 4*N := dvd_mul_of_dvd_right hN 4
  have hj4 : j ≤ 4*N := by omega
  have hv := choose_valuation_ge hp hj0 hj4 htop
  rw [hjv] at hv
  have hd : p^(r-s) ∣ (4*N).choose j :=
    (padicValNat_dvd_iff_le (Nat.choose_pos hj4).ne').mpr hv
  have hc : (p : ℤ)^(r-s) ∣ ((4*N).choose j : ℤ) := by exact_mod_cast hd
  have hc2 := pow_dvd_pow_of_dvd hc 2
  rwa [← pow_mul, Nat.mul_comm (r-s) 2] at hc2

/-- Turn a weighted-kernel cancellation into the exact unit-index block of the m=4 convolution. -/
theorem unit_convolution_block {p r N j : ℕ}
    (hp : p.Prime) (hr : 1 ≤ r) (hN : p^r ∣ N) (hle : j ≤ N) (hj : p ∣ j)
    (hzero : ∀ s : ℕ, 1 ≤ s → s ≤ r → 0 < N-j → p^s ∣ N-j →
      ∑ i ∈ range (N-j), (weight (4*N) (6*N) (N-j) i : ZMod (p^s)) *
        signedKernel p s (N-j) i = 0) :
    (p : ℤ)^(3*r) ∣ ∑ i ∈ range (N-j+1),
      if p ∣ i then 0 else term N i j (N-j-i) := by
  let h := N-j
  have hph : p ∣ h := Nat.dvd_sub ((dvd_pow_self p (by omega)).trans hN) hj
  by_cases h0 : h = 0
  · change _ ∣ ∑ i ∈ range (h+1), if p ∣ i then 0 else term N i j (h-i)
    rw [h0]
    simp
  let : Fact p.Prime := ⟨hp⟩
  let s := min r (padicValNat p h)
  have hv : 1 ≤ padicValNat p h :=
    (padicValNat_dvd_iff_le h0).mp (by simpa using hph)
  have hs : 1 ≤ s := le_min hr hv
  have hsr : s ≤ r := min_le_left _ _
  have hspan : p^s ∣ h := (padicValNat_dvd_iff_le h0).mpr (min_le_right _ _)
  have hac : (p : ℤ)^r ∣ ((4*N : ℕ) : ℤ) := by
    exact_mod_cast (dvd_mul_of_dvd_right hN 4)
  have hdc : (p : ℤ)^r ∣ ((6*N : ℕ) : ℤ) := by
    exact_mod_cast (dvd_mul_of_dvd_right hN 6)
  have hpos : 0 < 4*N := by dsimp [h] at h0; omega
  have hU := unit_sum_dvd_of_kernel_zero hp hpos hs hr hspan hac hdc
    (hzero s hs hsr (Nat.pos_of_ne_zero h0) hspan)
  have hB := middle_square_dvd hp hN hle h0 (s := s) rfl hspan
  change _ ∣ ∑ i ∈ range (h+1), if p ∣ i then 0 else term N i j (h-i)
  rw [sum_range_succ, if_pos hph, add_zero]
  have he : ∑ i ∈ range h, (if p ∣ i then 0 else term N i j (h-i)) =
      ((4*N).choose j : ℤ)^2 * ∑ i ∈ range h, unitTerm p (4*N) (6*N) h i := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    by_cases hpi : p ∣ i
    · simp [hpi, unitTerm]
    · simp only [hpi, if_false, unitTerm, term, negChoose]
      ring
  rw [he]
  have hProd : (p : ℤ)^(2*(r-s)+(2*r+s)) ∣
      ((4*N).choose j : ℤ)^2 * ∑ i ∈ range h, unitTerm p (4*N) (6*N) h i := by
    rw [pow_add]
    exact mul_dvd_mul hB hU
  exact (pow_dvd_pow _ (by omega : 3*r ≤ 2*(r-s)+(2*r+s))).trans hProd

end A363990LocalVariation

end

section

open Finset A363990Valuation A363990LocalVariation

namespace A363990Convolution

theorem transformed_congruence {p n r : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    convolution (n*p^r) ≡ convolution (n*p^(r-1)) [ZMOD (p : ℤ)^(3*r)] := by
  apply convolution_tower hp hp5 hn hr
  intro j hle hj
  let N := n*p^r
  change (p : ℤ)^(3*r) ∣ ∑ i ∈ (range (N-j+1)).filter (fun i => ¬p ∣ i),
    term N i j (N-j-i)
  have hN : p^r ∣ N := dvd_mul_left _ _
  have h : 0 < N := Nat.mul_pos hn (pow_pos hp.pos _)
  rw [sum_filter]
  simp_rw [ite_not]
  apply unit_convolution_block hp hr hN hle hj
  intro s hs hsr hh hdivh
  have hac : (p : ℤ)^r ∣ ((4*N : ℕ) : ℤ) := by
    exact_mod_cast (dvd_mul_of_dvd_right hN 4)
  have hdc : (p : ℤ)^r ∣ ((6*N : ℕ) : ℤ) := by
    exact_mod_cast (dvd_mul_of_dvd_right hN 6)
  exact A363990Cancellation.weighted_unit_sum_zero hp (by omega) hs hsr hdivh
    (by omega) (by omega) hac hdc

end A363990Convolution

end

section

noncomputable section
namespace A363990Transform
open PowerSeries

/-- Inverse of1-y and the quadratic t-substitution. -/
def geometricSeries : ℚ⟦X⟧ := (invOneSubPow ℚ 1).val

def quadraticSeries : ℚ⟦X⟧ := X * geometricSeries^2

lemma geometricSeries_inverse : geometricSeries*(1-X) = 1 := by
  have h := (invOneSubPow ℚ 1).val_inv
  rw [invOneSubPow_inv_eq_one_sub_pow, pow_one] at h
  exact h

lemma geometricSeries_constant : constantCoeff geometricSeries = 1 := by
  simp [geometricSeries, invOneSubPow]

lemma quadraticSeries_constant : constantCoeff quadraticSeries = 0 := by
  simp [quadraticSeries]

lemma quadraticSeries_hasSubst : HasSubst quadraticSeries :=
  HasSubst.of_constantCoeff_zero' quadraticSeries_constant

end A363990Transform
end

end

section

noncomputable section
namespace A363990Transform
open PowerSeries

/-- Pure ring identity relating the original central-binomial denominator to
the rescaled square-binomial denominator under t=y/(1+y)^2. -/
theorem rationalize_denominator {R : Type*} [CommRing R]
    (y ep em : R) (hp : ep*(1+y)=1) (hm : em*(1-y)=1) :
    let z := y*ep^2
    let f := (1-y)*ep
    let a := (1+y)*em^2
    (C (f^2) : R⟦X⟧) *
      ((1-C ((1+y)*a)*X)^2-C (4*y*a^2)*X^2) =
      (1-X)^2-C (4*z) := by
  dsimp only
  have hF : ((1-y)*ep)^2=1-4*(y*ep^2) := by
    have hh : (ep*(1+y))^2=1 := by rw [hp, one_pow]
    linear_combination hh
  have hFA : ((1-y)*ep)^2*(1+y)*((1+y)*em^2)=1 := by
    calc _ = (ep*(1+y))^2*(em*(1-y))^2 := by ring
         _ = 1 := by rw [hp, hm]; ring
  have hFA2 : ((1-y)*ep)^2*((1+y)*em^2)^2*(1-y)^2=1 := by
    calc _ = (ep*(1+y))^2*(em*(1-y))^4 := by ring
         _ = 1 := by rw [hp, hm]; ring
  calc
    _ = C (((1-y)*ep)^2) -
        C (2*(((1-y)*ep)^2*(1+y)*((1+y)*em^2)))*X +
        C (((1-y)*ep)^2*((1+y)*em^2)^2*(1-y)^2)*X^2 := by
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one]
      ring
    _ = _ := by
      rw [hFA, hFA2, hF]
      simp only [map_sub, map_mul, map_ofNat, map_one, mul_one]
      ring

/-- Multiplying the original square-root generating function by the rational
prefactor produces the square-binomial generating function's denominator. -/
theorem rationalize_original_square {R : Type*} [CommRing R]
    (y ep em : R) (hp : ep*(1+y)=1) (hm : em*(1-y)=1)
    (B : R⟦X⟧) (hB : B^2*((1-X)^2-C (4*(y*ep^2)))=1) :
    let a := (1+y)*em^2
    (C ((1-y)*ep)*B)^2 *
      ((1-C ((1+y)*a)*X)^2-C (4*y*a^2)*X^2)=1 := by
  dsimp only
  have hd := rationalize_denominator y ep em hp hm
  dsimp only at hd
  calc
    _ = B^2*(C (((1-y)*ep)^2)*
      ((1-C ((1+y)*((1+y)*em^2))*X)^2-C (4*y*((1+y)*em^2)^2)*X^2)) := by
        rw [map_pow]
        ring
    _ = 1 := by rw [hd]; exact hB

end A363990Transform
end

end

section

open Finset PowerSeries

namespace A363990Series

variable {R : Type*} [Semiring R]

/-- Swap the two coefficient indices of an iterated formal power series. -/
noncomputable def flipCoeffs (F : PowerSeries (PowerSeries R)) : PowerSeries (PowerSeries R) :=
  PowerSeries.mk (fun i => PowerSeries.mk (fun j => coeff i (coeff j F)))

theorem coeff_coeff_flip (F : PowerSeries (PowerSeries R)) (i j : ℕ) :
    coeff j (coeff i (flipCoeffs F)) = coeff i (coeff j F) := by
  simp [flipCoeffs]

/-- Transposition preserves Cauchy multiplication, by interchanging the finite coefficient sums. -/
noncomputable def transpose : PowerSeries (PowerSeries R) →+* PowerSeries (PowerSeries R) where
  toFun := flipCoeffs
  map_one' := by
    ext i j
    rw [coeff_coeff_flip]
    simp only [coeff_one]
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi,hj]
  map_mul' := by
    intro F G
    ext i j
    rw [coeff_coeff_flip, coeff_mul, coeff_mul]
    simp only [map_sum, coeff_mul, coeff_coeff_flip]
    rw [Finset.sum_comm]
  map_zero' := by
    ext i j
    simp [coeff_coeff_flip]
  map_add' := by
    intro F G
    ext i j
    simp [coeff_coeff_flip]

@[simp] theorem coeff_coeff_transpose (F : PowerSeries (PowerSeries R)) (i j : ℕ) :
    coeff j (coeff i (transpose F)) = coeff i (coeff j F) :=
  coeff_coeff_flip F i j

@[simp] theorem transpose_twice (F : PowerSeries (PowerSeries R)) :
    transpose (transpose F) = F := by
  ext i j
  simp

@[simp] theorem transpose_X : transpose (X : PowerSeries (PowerSeries R)) =
    C (X : PowerSeries R) := by
  ext i j
  rw [coeff_coeff_transpose, coeff_X, coeff_C]
  by_cases hj : j = 1 <;> by_cases hi : i = 0 <;> simp [hj,hi,coeff_one,coeff_X]

@[simp] theorem transpose_C_X : transpose (C (X : PowerSeries R)) = X := by
  rw [← transpose_X, transpose_twice]

@[simp] theorem transpose_C_C (a : R) : transpose (C (C a)) = C (C a) := by
  ext i j
  rw [coeff_coeff_transpose, coeff_C, coeff_C]
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi,hj,coeff_C]

end A363990Series

end

section

open Finset PowerSeries

namespace A363990Series

variable {R : Type*} [CommRing R]

/-- Only the first n+1 coefficients contribute to the substitution X ↦ X*u. -/
theorem coeff_subst_X_mul (f u : PowerSeries R) (n : ℕ) :
    coeff n (f.subst (X*u)) =
      ∑ k ∈ range (n+1), coeff k f * coeff (n-k) (u^k) := by
  have hsubst : HasSubst (X*u) := HasSubst.of_constantCoeff_zero' (by simp)
  rw [coeff_subst' hsubst]
  classical
  rw [finsum_eq_sum_of_support_subset (s := range (n+1))]
  · apply sum_congr rfl
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (mem_range.mp hk)
    rw [mul_pow, coeff_X_pow_mul', if_pos hkn, smul_eq_mul]
  · intro k hk
    by_contra hm
    have hkn : ¬ k ≤ n := by simpa [mem_range, Nat.lt_succ_iff] using hm
    apply hk
    change coeff k f • coeff n ((X*u)^k) = 0
    rw [mul_pow, coeff_X_pow_mul', if_neg hkn, smul_zero]

/-- A prefactor can be included before extracting a substituted coefficient. -/
theorem coeff_mul_subst_X_mul (P f u : PowerSeries R) (n : ℕ) :
    coeff n (P * f.subst (X*u)) =
      ∑ k ∈ range (n+1), coeff k f * coeff (n-k) (P*u^k) := by
  let G : PowerSeries R := ∑ k ∈ range (n+1), C (coeff k f) * (X*u)^k
  have hG (m : ℕ) (hm : m ≤ n) : coeff m (f.subst (X*u)) = coeff m G := by
    rw [coeff_subst_X_mul, show G = _ from rfl, map_sum]
    rw [← sum_subset (range_mono (Nat.succ_le_succ hm))]
    · apply sum_congr rfl
      intro k hk
      have hkm : k ≤ m := Nat.le_of_lt_succ (mem_range.mp hk)
      rw [coeff_C_mul, mul_pow, coeff_X_pow_mul', if_pos hkm]
    · intro k hk hkm
      have hkn : ¬ k ≤ m := by simpa [mem_range, Nat.lt_succ_iff] using hkm
      rw [coeff_C_mul, mul_pow, coeff_X_pow_mul', if_neg hkn, mul_zero]
  have he : coeff n (P * f.subst (X*u)) = coeff n (P*G) := by
    rw [coeff_mul, coeff_mul]
    apply sum_congr rfl
    intro ij hij
    rw [hG ij.2 ((Nat.le_add_left _ _).trans_eq (Finset.HasAntidiagonal.mem_antidiagonal.mp hij))]
  rw [he, show G = _ from rfl, mul_sum, map_sum]
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (mem_range.mp hk)
  have hterm : P * (C (coeff k f) * (X*u)^k) =
      C (coeff k f) * (X^k * (P*u^k)) := by rw [mul_pow]; ring
  rw [hterm, coeff_C_mul, coeff_X_pow_mul', if_pos hkn]

end A363990Series

end

section

open Finset PowerSeries A363990Valuation

namespace A363990Series

/-- The coefficient of a power of the inverse geometric factor. -/
theorem inverse_geometric_coeff (E : PowerSeries ℚ) (hE : E*(1-X)=1) (a k : ℕ)
    (ha : 0 < a) : coeff k (E^a) = ((a+k-1).choose k : ℚ) := by
  have h : E = (PowerSeries.mk 1 : PowerSeries ℚ) := by
    calc
      E = E*((1-X)*PowerSeries.mk 1) := by
        rw [mul_comm (1-X), mk_one_mul_one_sub_eq_one, mul_one]
      _ = (E*(1-X))*PowerSeries.mk 1 := (mul_assoc _ _ _).symm
      _ = _ := by rw [hE,one_mul]
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  rw [h, mk_one_pow_eq_mk_choose_add, coeff_mk]
  congr 1
  rw [show d+1+k-1 = d+k by omega, Nat.choose_symm_add]

theorem positive_binomial_coeff (a k : ℕ) : coeff k ((1+X : PowerSeries ℚ)^a) =
    (a.choose k : ℚ) := by
  have h : (1+X : PowerSeries ℚ)^a =
      (((1 : Polynomial ℚ) + Polynomial.X)^a).toPowerSeries := by simp
  rw [h, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

/-- Removing the coefficient-change factor recovers the integral m=4
convolution from the rescaled square-binomial row. -/
theorem scaled_row_coeff (N : ℕ) (E row : PowerSeries ℚ)
    (hE : E*(1-X)=1) (hrow : ∀ j : ℕ, coeff j row = ((4*N).choose j : ℚ)^2) :
    coeff N ((1-X)^(2*N) * ((((1+X)*E^2)^(4*N))*row)) =
      (A363990Convolution.convolution N : ℚ) := by
  cases N with
  | zero =>
    simp only [Nat.mul_zero, pow_zero, one_mul, hrow, Nat.choose_self, Nat.cast_one]
    norm_num [A363990Convolution.convolution, term, negChoose]
  | succ N =>
    let M := N+1
    change coeff M ((1-X)^(2*M) * ((((1+X)*E^2)^(4*M))*row)) =
      (A363990Convolution.convolution M : ℚ)
    have hcancel : (1-X : PowerSeries ℚ)^(2*M) * E^(2*(4*M)) = E^(6*M) := by
      rw [show 2*(4*M) = 2*M + 6*M by omega, pow_add, ← mul_assoc, ← mul_pow, mul_comm (1-X), hE,
        one_pow, one_mul]
    have hprod : (1-X : PowerSeries ℚ)^(2*M) * ((((1+X)*E^2)^(4*M))*row) =
        row * ((1+X)^(4*M)*E^(6*M)) := by
      rw [mul_pow, ← pow_mul, ← hcancel]
      ring
    rw [hprod, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    unfold A363990Convolution.convolution
    push_cast
    apply sum_congr rfl
    intro j hj
    rw [hrow, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [positive_binomial_coeff, inverse_geometric_coeff E hE (6*M) _ (by omega)]
    simp only [term, negChoose, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    ring

end A363990Series

end

section

namespace A363990Central
open PowerSeries

noncomputable def centralSeries (R : Type*) [CommSemiring R] : PowerSeries R :=
  PowerSeries.mk fun n => (Nat.centralBinom n : R)

@[simp] theorem coeff_centralSeries (R : Type*) [CommSemiring R] (n : ℕ) :
    PowerSeries.coeff n (centralSeries R)=(Nat.centralBinom n : R) := by
  simp [centralSeries]

@[simp] theorem constant_centralSeries (R : Type*) [CommSemiring R] :
    PowerSeries.constantCoeff (centralSeries R)=1 := by
  simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- The elementary central-binomial recurrence is the differential equation
(1-4X)C'=2C in every commutative coefficient ring. -/
theorem central_ode (R : Type*) [CommRing R] :
    (1-PowerSeries.C (4 : R)*PowerSeries.X)*
      PowerSeries.derivative R (centralSeries R)=PowerSeries.C (2 : R)*centralSeries R := by
  rw [sub_mul,one_mul,mul_assoc]
  ext n
  cases n with
  | zero =>
    simp only [map_sub,PowerSeries.coeff_derivative,coeff_centralSeries,
      PowerSeries.coeff_C_mul,PowerSeries.coeff_zero_X_mul]
    norm_num [Nat.centralBinom]
  | succ n =>
    simp only [map_sub,PowerSeries.coeff_derivative,coeff_centralSeries,
      PowerSeries.coeff_C_mul,PowerSeries.coeff_succ_X_mul]
    have hrec := congrArg (fun z : ℕ => (z : R)) (Nat.succ_mul_centralBinom_succ (n+1))
    push_cast at hrec
    push_cast
    linear_combination hrec

/-- Integer central-binomial square equation. Its derivative vanishes by
central_ode, and the constant coefficient is 1. -/
theorem central_square_int :
    centralSeries ℤ ^ 2 * (1-PowerSeries.C (4 : ℤ)*PowerSeries.X)=1 := by
  apply PowerSeries.derivative.ext
  · have hode := central_ode ℤ
    have hd : PowerSeries.derivative ℤ
        (centralSeries ℤ ^ 2 * (1-PowerSeries.C (4 : ℤ)*PowerSeries.X))=0 := by
      calc
        _ = 2*centralSeries ℤ*((1-PowerSeries.C (4 : ℤ)*PowerSeries.X)*
            PowerSeries.derivative ℤ (centralSeries ℤ)-2*centralSeries ℤ) := by
          simp only [Derivation.leibniz,map_sub,PowerSeries.derivative_one,
            PowerSeries.derivative_X,PowerSeries.derivative_pow,
            smul_eq_mul,pow_one,Nat.reduceSub,mul_one,map_ofNat]
          rw [show PowerSeries.derivative ℤ (4 : PowerSeries ℤ)=0 from
            (PowerSeries.derivative ℤ).map_natCast 4]
          ring
        _ = 0 := by rw [hode]; simp
    rw [hd,PowerSeries.derivative_one]
  · simp

/-- Universal central-binomial generating-series identity, valid even in
positive characteristic because it is transported from integer coefficients. -/
theorem central_square (R : Type*) [CommRing R] :
    centralSeries R ^ 2 * (1-PowerSeries.C (4 : R)*PowerSeries.X)=1 := by
  have hmap : PowerSeries.map (Int.castRingHom R) (centralSeries ℤ)=centralSeries R := by
    ext n
    simp [PowerSeries.coeff_map]
  have h := congrArg (PowerSeries.map (Int.castRingHom R)) central_square_int
  simpa only [map_mul,map_pow,map_sub,map_one,PowerSeries.map_C,PowerSeries.map_X,
    map_ofNat,hmap] using h

end A363990Central

end

section

namespace A363990OriginalGF
open PowerSeries A363990Central A363990Series

noncomputable def geometric (R : Type*) [CommRing R] : PowerSeries R := PowerSeries.mk 1

noncomputable def transposedB (R : Type*) [CommRing R] : PowerSeries (PowerSeries R) :=
  PowerSeries.C (geometric R) *
    PowerSeries.rescale ((geometric R)^2) (centralSeries (PowerSeries R))

/-- The outer variable marks ℓ and the inner variable marks k. -/
noncomputable def originalB (R : Type*) [CommRing R] : PowerSeries (PowerSeries R) :=
  A363990Series.transpose (transposedB R)

/-- Exact original binomial coefficients, before the alternating change of variable. -/
theorem coeff_coeff_originalB (R : Type*) [CommRing R] (l k : ℕ) :
    PowerSeries.coeff k (PowerSeries.coeff l (originalB R)) =
      ((l+2*k).choose (2*k) : R) * (Nat.centralBinom k : R) := by
  rw [originalB,coeff_coeff_transpose]
  simp only [transposedB,PowerSeries.coeff_C_mul,PowerSeries.coeff_rescale,coeff_centralSeries]
  have hnat : (Nat.centralBinom k : PowerSeries R)=PowerSeries.C (Nat.centralBinom k : R) :=
    (map_natCast PowerSeries.C _).symm
  rw [← mul_assoc,hnat,PowerSeries.coeff_mul_C]
  have hpow : geometric R*((geometric R)^2)^k=(geometric R)^(2*k+1) := by
    rw [pow_add,pow_mul,pow_one]
    ring
  rw [hpow,geometric,PowerSeries.mk_one_pow_eq_mk_choose_add,PowerSeries.coeff_mk]
  rw [Nat.add_comm (2*k) l]

@[simp] theorem constant_originalB (R : Type*) [CommRing R] :
    PowerSeries.constantCoeff (originalB R)=centralSeries R := by
  ext k
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,coeff_coeff_originalB]
  simp only [Nat.zero_add,Nat.choose_self,Nat.cast_one,one_mul,coeff_centralSeries]

@[simp] theorem corner_originalB (R : Type*) [CommRing R] :
    PowerSeries.constantCoeff (PowerSeries.constantCoeff (originalB R))=1 := by simp

theorem transposedB_square (R : Type*) [CommRing R] :
    transposedB R^2 * ((1-PowerSeries.C (PowerSeries.X : PowerSeries R))^2-
      4*(PowerSeries.X : PowerSeries (PowerSeries R)))=1 := by
  let G := geometric R
  let T := PowerSeries.rescale (G^2) (centralSeries (PowerSeries R))
  have hG : G*(1-PowerSeries.X)=1 := PowerSeries.mk_one_mul_one_sub_eq_one R
  have hGG : G^2*(1-PowerSeries.X)^2=1 := by rw [← mul_pow,hG,one_pow]
  have hCGG : (PowerSeries.C G)^2*PowerSeries.C ((1-PowerSeries.X)^2)=
      (1 : PowerSeries (PowerSeries R)) := by
    rw [← map_pow,← map_mul,hGG,map_one]
  have hT := congrArg (PowerSeries.rescale (G^2)) (central_square (PowerSeries R))
  simp only [map_pow,map_mul,map_sub,map_one,map_ofNat,PowerSeries.rescale_X] at hT
  have hcalc : (PowerSeries.C G*T)^2 *
      (PowerSeries.C ((1-PowerSeries.X)^2)-4*PowerSeries.X)=1 := by
    calc
      _ = T^2*((PowerSeries.C G)^2*PowerSeries.C ((1-PowerSeries.X)^2)-
          4*(PowerSeries.C G)^2*PowerSeries.X) := by ring
      _ = T^2*(1-4*((PowerSeries.C G)^2*PowerSeries.X)) := by rw [hCGG]; ring
      _ = 1 := hT
  simpa only [map_pow,map_sub,map_one,transposedB,G,T] using hcalc

/-- The original bivariate GF has the exact algebraic square required by
formal rationalization and coefficient extraction. -/
theorem originalB_square (R : Type*) [CommRing R] :
    originalB R^2 * ((1-PowerSeries.X)^2-
      4*PowerSeries.C (PowerSeries.X : PowerSeries R))=1 := by
  have h := congrArg A363990Series.transpose (transposedB_square R)
  simpa only [map_pow,map_mul,map_sub,map_one,map_ofNat,transpose_C_X,transpose_X,
    originalB] using h

end A363990OriginalGF

end

section

open Finset PowerSeries
noncomputable section
namespace A363990Square

/-- Squared-binomial row in the inner variable y. -/
def squareRow (l : ℕ) : ℚ⟦X⟧ :=
  ∑ j ∈ range (l + 1), C ((l.choose j : ℚ) ^ 2) * X ^ j

/-- The two-variable generating function, outer variable u and inner variable y. -/
def squareGF : PowerSeries (PowerSeries ℚ) := PowerSeries.mk squareRow

@[simp] theorem coeff_squareRow (l k : ℕ) : coeff k (squareRow l) = (l.choose k : ℚ) ^ 2 := by
  classical
  simp only [squareRow, map_sum, coeff_C_mul_X_pow]
  by_cases hk : k < l + 1
  · simp [hk]
  · have hlk : l < k := by omega
    simp [hk, Nat.choose_eq_zero_of_lt hlk]

@[simp] theorem coeff_squareGF (l : ℕ) : coeff l squareGF = squareRow l := coeff_mk _ _

/-- Adjacent binomials, with signed subtraction so the identity holds outside the row. -/
theorem choose_step (n k : ℕ) :
    ((n : ℚ) - k) * (n.choose k : ℚ) = ((k : ℚ) + 1) * (n.choose (k + 1) : ℚ) := by
  by_cases hk : k ≤ n
  · have h := Nat.choose_succ_right_eq n k
    have hcast : (n.choose (k + 1) : ℚ) * ((k : ℚ) + 1) =
        (n.choose k : ℚ) * ((n : ℚ) - k) := by
      exact_mod_cast h
    linear_combination -hcast
  · have hkn : n < k := by omega
    rw [Nat.choose_eq_zero_of_lt hkn, Nat.choose_eq_zero_of_lt (by omega : n < k + 1)]
    simp

/-- The division-free coefficient certificate behind the Legendre recurrence. -/
theorem row_coefficient_recurrence (n k : ℕ) :
    ((n : ℚ) + 2) * (Nat.choose (n + 2) (k + 2) : ℚ) ^ 2 =
      (2 * (n : ℚ) + 3) *
        ((Nat.choose (n + 1) (k + 2) : ℚ) ^ 2 + (Nat.choose (n + 1) (k + 1) : ℚ) ^ 2) -
      ((n : ℚ) + 1) * ((n.choose (k + 2) : ℚ) ^ 2 -
        2 * (n.choose (k + 1) : ℚ) ^ 2 + (n.choose k : ℚ) ^ 2) := by
  have h1 := choose_step n (k + 1)
  have h2 := choose_step n k
  simp only [Nat.cast_add, Nat.cast_one] at h1
  simp only [Nat.choose_succ_succ, Nat.cast_add]
  linear_combination
    -2 * ((n.choose (k + 1) : ℚ) + (n.choose k : ℚ)) * h1 +
    2 * ((n.choose (k + 2) : ℚ) + (n.choose (k + 1) : ℚ)) * h2

/-- The squared-binomial rows satisfy the Legendre three-term recurrence. -/
theorem squareRow_recurrence (n : ℕ) :
    C ((n : ℚ) + 2) * squareRow (n + 2) =
      C (2 * (n : ℚ) + 3) * squareRow (n + 1) +
      (C (2 * (n : ℚ) + 3) * squareRow (n + 1)) * X ^ 1 -
      C ((n : ℚ) + 1) * squareRow n +
      (C (2 * ((n : ℚ) + 1)) * squareRow n) * X ^ 1 -
      (C ((n : ℚ) + 1) * squareRow n) * X ^ 2 := by
  ext k
  simp only [map_sub (coeff k), map_add (coeff k), coeff_mul_X_pow', coeff_C_mul, coeff_squareRow]
  cases k with
  | zero => simp; ring
  | succ k =>
    cases k with
    | zero => simp; push_cast; ring
    | succ k =>
      simp only [show 1 ≤ k + 1 + 1 by omega, show 2 ≤ k + 1 + 1 by omega,
        if_true, show k + 1 + 1 - 1 = k + 1 by omega,
        show k + 1 + 1 - 2 = k by omega]
      convert row_coefficient_recurrence n k using 1 <;> ring

/-- The same row recurrence in its compact quadratic-coefficient form. -/
theorem squareRow_recurrence_compact (n : ℕ) :
    C ((n : ℚ) + 2) * squareRow (n + 2) =
      C (2 * (n : ℚ) + 3) * (1 + X) * squareRow (n + 1) -
      C ((n : ℚ) + 1) * (1 - X) ^ 2 * squareRow n := by
  rw [squareRow_recurrence]
  simp only [pow_one]
  have hc : C (2 * ((n : ℚ) + 1)) = 2 * C ((n : ℚ) + 1) := by
    rw [map_mul, map_ofNat]
  rw [hc]
  ring

@[simp] theorem squareRow_zero : squareRow 0 = 1 := by simp [squareRow]

@[simp] theorem squareRow_one : squareRow 1 = 1 + X := by
  norm_num [squareRow, sum_range_succ]

/-- General Legendre-recurrence generating-function differential equation. -/
theorem recurrence_ode {R : Type*} [CommRing R]
    (H : ℕ → R) (a b : R) (h0 : H 0 = 1) (h1 : H 1 = a)
    (hr : ∀ n : ℕ, ((n : R) + 2) * H (n + 2) =
      (2 * (n : R) + 3) * a * H (n + 1) - ((n : R) + 1) * b * H n) :
    let G : PowerSeries R := PowerSeries.mk H
    derivative R G - (C (2 * a) * derivative R G) * X ^ 1 +
        (C b * derivative R G) * X ^ 2 =
      C a * G - (C b * G) * X ^ 1 := by
  intro G
  ext n
  simp only [map_add (coeff n), map_sub (coeff n), coeff_mul_X_pow', coeff_C_mul,
    coeff_derivative, G, coeff_mk]
  cases n with
  | zero => simp [h0, h1]
  | succ n =>
    cases n with
    | zero =>
      have hh := hr 0
      norm_num at hh ⊢
      linear_combination hh
    | succ n =>
      simp only [show 1 ≤ n + 1 + 1 by omega, show 2 ≤ n + 1 + 1 by omega,
        if_true, show n + 1 + 1 - 1 = n + 1 by omega,
        show n + 1 + 1 - 2 = n by omega, Nat.cast_add, Nat.cast_one]
      have hh := hr (n + 1)
      simp only [Nat.cast_add, Nat.cast_one] at hh
      linear_combination hh

/-- The ODE integrates to the formal square equation with constant coefficient one. -/
theorem recurrence_square {R : Type*} [CommRing R] [IsAddTorsionFree R]
    (H : ℕ → R) (a b : R) (h0 : H 0 = 1) (h1 : H 1 = a)
    (hr : ∀ n : ℕ, ((n : R) + 2) * H (n + 2) =
      (2 * (n : R) + 3) * a * H (n + 1) - ((n : R) + 1) * b * H n) :
    (PowerSeries.mk H) ^ 2 *
      (1 - C (2 * a) * X + C b * X ^ 2 : PowerSeries R) = 1 := by
  let G : PowerSeries R := PowerSeries.mk H
  let D : PowerSeries R := 1 - C (2 * a) * X + C b * X ^ 2
  have he := recurrence_ode H a b h0 h1 hr
  have hode : D * derivative R G = (C a - C b * X) * G := by
    dsimp only [D, G]
    simp only [pow_one] at he
    linear_combination he
  change G ^ 2 * D = 1
  apply derivative.ext
  · rw [derivative_one]
    calc
      derivative R (G ^ 2 * D) =
          2 * G * (D * derivative R G - (C a - C b * X) * G) := by
        dsimp only [D]
        simp only [Derivation.leibniz, map_add, map_sub, derivative_one, derivative_C,
          derivative_X, derivative_pow, smul_eq_mul, pow_one, Nat.reduceSub, mul_one,
          zero_mul, mul_zero, zero_add, add_zero, sub_zero]
        simp only [map_mul, map_ofNat]
        ring
      _ = 0 := by rw [hode]; ring
  · simp [G, D, h0]

/-- Exact two-variable square identity for the square-binomial generating function. -/
theorem squareGF_quadratic :
    squareGF ^ 2 *
      (1 - C (2 * (1 + (X : ℚ⟦X⟧))) * X +
        C ((1 - (X : ℚ⟦X⟧)) ^ 2) * X ^ 2) = 1 := by
  letI : IsAddTorsionFree ℚ⟦X⟧ := by
    constructor
    intro n hn f g h
    ext k
    have hk := congrArg (coeff k) h
    simp only [map_nsmul] at hk
    exact (IsAddTorsionFree.nsmul_right_injective (M := ℚ) hn) hk
  apply recurrence_square squareRow (1 + (X : ℚ⟦X⟧)) ((1 - (X : ℚ⟦X⟧)) ^ 2)
    squareRow_zero squareRow_one
  intro n
  have h := squareRow_recurrence_compact n
  simpa only [map_add, map_mul, map_natCast, map_ofNat, map_one] using h

/-- Requested form: denominator (1-(1+y)u)^2-4yu^2. -/
theorem squareGF_square :
    squareGF ^ 2 * ((1 - C (1 + (X : ℚ⟦X⟧)) * X) ^ 2 -
      C (4 * (X : ℚ⟦X⟧)) * X ^ 2) = 1 := by
  have hinner : (1 - (X : ℚ⟦X⟧)) ^ 2 = (1 + (X : ℚ⟦X⟧)) ^ 2 - 4 * X := by ring
  have hd : ((1 - C (1 + (X : ℚ⟦X⟧)) * X) ^ 2 -
      C (4 * (X : ℚ⟦X⟧)) * X ^ 2 : PowerSeries (PowerSeries ℚ)) =
      1 - C (2 * (1 + (X : ℚ⟦X⟧))) * X + C ((1 - (X : ℚ⟦X⟧)) ^ 2) * X ^ 2 := by
    rw [hinner]
    simp only [map_sub, map_pow, map_mul, map_ofNat]
    ring
  rw [hd]
  exact squareGF_quadratic

end A363990Square
end

end

section

noncomputable section
namespace A363990Transform
open PowerSeries

lemma geometricSeries_pow (d : ℕ) :
    geometricSeries^d=(invOneSubPow ℚ d).val := by
  induction d with
  | zero => simp [invOneSubPow_zero]
  | succ d ih =>
    rw [pow_succ, ih]
    exact (congrArg Units.val (invOneSubPow_add ℚ (d := d) 1)).symm

lemma geometric_cancel (m k : ℕ) (hk : k ≤ m) :
    (1-X : ℚ⟦X⟧)^(2*m)*geometricSeries^(2*k+1) =
      if k=m then geometricSeries else (1-X)^(2*(m-k)-1) := by
  rw [geometricSeries_pow]
  by_cases he : k=m
  · subst k
    rw [if_pos rfl, show 2*m+1=1+2*m by omega]
    exact one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val ℚ (d := 1) (2*m)
  · rw [if_neg he, show 2*m=(2*(m-k)-1)+(2*k+1) by omega]
    exact one_sub_pow_add_mul_invOneSubPow_val_eq_one_sub_pow ℚ (d := 2*(m-k)-1) (2*k+1)

lemma one_add_X_ps_coeff (n k : ℕ) :
    coeff k ((1+X : ℚ⟦X⟧)^n) = (n.choose k : ℚ) := by
  have he : (1+X : ℚ⟦X⟧)^n = ((1+Polynomial.X : Polynomial ℚ)^n).toPowerSeries := by simp
  rw [he, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

lemma one_sub_X_ps_coeff (n k : ℕ) :
    coeff k ((1-X : ℚ⟦X⟧)^n) = (-1 : ℚ)^k*(n.choose k : ℚ) := by
  have he : (1-X : ℚ⟦X⟧)^n = rescale (-1) ((1+X)^n) := by simp [sub_eq_add_neg]
  rw [he, coeff_rescale, one_add_X_ps_coeff]

lemma jacobian_ps_coeff (m : ℕ) :
    coeff m ((1+X : ℚ⟦X⟧)*(1-X)^(2*m-1)) = if m=0 then 1 else 0 := by
  cases m with
  | zero => simp
  | succ m =>
    rw [show 2*(m+1)-1=2*m+1 by omega, add_mul, one_mul, map_add]
    have hX : coeff (m+1) (X*(1-X : ℚ⟦X⟧)^(2*m+1)) =
        coeff m ((1-X : ℚ⟦X⟧)^(2*m+1)) := by
      simpa only [pow_one] using coeff_X_pow_mul ((1-X : ℚ⟦X⟧)^(2*m+1)) 1 m
    rw [hX]
    rw [one_sub_X_ps_coeff, one_sub_X_ps_coeff, Nat.choose_symm_half]
    simp only [pow_succ, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte]
    ring

/-- The finite coefficient kernel used when applying the quadratic change to
an arbitrary formal power series. -/
theorem jacobian_geometric_kernel (m k : ℕ) (hk : k ≤ m) :
    coeff (m-k) (((1+X : ℚ⟦X⟧)*(1-X)^(2*m)*geometricSeries)*
      (geometricSeries^2)^k) = if k=m then 1 else 0 := by
  rw [show ((1+X : ℚ⟦X⟧)*(1-X)^(2*m)*geometricSeries)*(geometricSeries^2)^k =
      (1+X)*((1-X)^(2*m)*geometricSeries^(2*k+1)) by ring]
  rw [geometric_cancel m k hk]
  by_cases he : k=m
  · subst k
    simp only [Nat.sub_self]
    rw [coeff_zero_eq_constantCoeff_apply]
    simp [geometricSeries_constant]
  · rw [if_neg he, jacobian_ps_coeff, if_neg (by omega : m-k ≠ 0), if_neg he]

/-- The quadratic change with its Jacobian preserves the selected coefficient. -/
theorem quadratic_ps_coefficient (f : ℚ⟦X⟧) (m : ℕ) :
    coeff m (((1+X : ℚ⟦X⟧)*(1-X)^(2*m)*geometricSeries)*
      f.subst quadraticSeries) = coeff m f := by
  unfold quadraticSeries
  rw [A363990Series.coeff_mul_subst_X_mul]
  have he (k : ℕ) (hk : k ∈ Finset.range (m+1)) :
      coeff k f * coeff (m-k)
        (((1+X : ℚ⟦X⟧)*(1-X)^(2*m)*geometricSeries)*(geometricSeries^2)^k) =
      if k=m then coeff m f else 0 := by
    rw [jacobian_geometric_kernel m k (by have := Finset.mem_range.mp hk; omega)]
    by_cases h : k=m <;> simp [h]
  rw [Finset.sum_congr rfl he]
  simp

lemma quadraticSeries_relation :
    1+C (4 : ℚ)*quadraticSeries = ((1+X)*geometricSeries)^2 := by
  have he : geometricSeries^2*(1-X)^2=1 := by
    rw [← mul_pow, geometricSeries_inverse, one_pow]
  unfold quadraticSeries
  simp only [map_ofNat]
  linear_combination -he

/-- Odd quadratic coefficient identity, derived from the checked Jacobian
rather than importing a hypergeometric summation formula. -/
theorem odd_quadratic_kernel (N m : ℕ) (hm : m ≤ N) :
    coeff m ((1+X : ℚ⟦X⟧)^(2*N+1)*geometricSeries^(2*(N-m)+1)) =
      (4 : ℚ)^m*(N.choose m : ℚ) := by
  let f : ℚ⟦X⟧ := (1+C 4*X)^N
  let φ := substAlgHom (R := ℚ) quadraticSeries_hasSubst
  have hφeval (p : ℚ⟦X⟧) : φ p=p.subst quadraticSeries := by
    simp only [φ, coe_substAlgHom]
  have hφX : φ X=quadraticSeries := by rw [hφeval]; exact subst_X quadraticSeries_hasSubst
  have hφC (q : ℚ) : φ (C q)=C q := φ.commutes q
  have hsubst : f.subst quadraticSeries = ((1+X)*geometricSeries)^(2*N) := by
    rw [← hφeval]
    change φ ((1+C 4*X)^N) = _
    rw [map_pow, map_add, map_one, map_mul, hφC, hφX, quadraticSeries_relation, ← pow_mul]
  have hc : (1-X : ℚ⟦X⟧)^(2*m)*geometricSeries^(2*N+1) =
      geometricSeries^(2*(N-m)+1) := by
    simp only [geometricSeries_pow]
    rw [show 2*N+1=(2*(N-m)+1)+2*m by omega]
    exact one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val ℚ (d := 2*(N-m)+1) (2*m)
  have hchange := quadratic_ps_coefficient f m
  rw [hsubst] at hchange
  have hp : ((1+X : ℚ⟦X⟧)*(1-X)^(2*m)*geometricSeries)*
      ((1+X)*geometricSeries)^(2*N) =
      (1+X)^(2*N+1)*((1-X)^(2*m)*geometricSeries^(2*N+1)) := by
    simp only [mul_pow, pow_succ]
    ring
  rw [hp, hc] at hchange
  have hf : f=rescale 4 ((1+X)^N) := by simp [f]
  rw [hf, coeff_rescale, one_add_X_ps_coeff] at hchange
  exact hchange

end A363990Transform
end

end

section

noncomputable section
namespace A363990Transform
open PowerSeries

/-- The inverse of1+y. -/
def positiveGeometricSeries : ℚ⟦X⟧ := rescale (-1) geometricSeries

def mobiusArgument : ℚ⟦X⟧ := X*positiveGeometricSeries^2

def mobiusFactor : ℚ⟦X⟧ := (1-X)*positiveGeometricSeries

def rowScale : ℚ⟦X⟧ := (1+X)*geometricSeries^2

lemma positiveGeometric_inverse : positiveGeometricSeries*(1+X)=1 := by
  have h := congrArg (rescale (-1 : ℚ)) geometricSeries_inverse
  simpa only [map_mul, map_sub, map_one, rescale_neg_one_X, sub_neg_eq_add,
    positiveGeometricSeries] using h

lemma positiveGeometric_constant : constantCoeff positiveGeometricSeries=1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [positiveGeometricSeries, geometricSeries_constant]

lemma mobius_hasSubst : HasSubst mobiusArgument :=
  HasSubst.of_constantCoeff_zero' (by simp [mobiusArgument])

/-- Substitute y/(1+y)^2 into the coefficient variable. -/
def mobiusSubst : ℚ⟦X⟧ →+* ℚ⟦X⟧ :=
  (substAlgHom (R := ℚ) mobius_hasSubst).toRingHom

lemma mobiusSubst_apply (f : ℚ⟦X⟧) : mobiusSubst f=f.subst mobiusArgument := by
  simp only [mobiusSubst, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, coe_substAlgHom]

lemma mobiusSubst_X : mobiusSubst X=mobiusArgument := by
  rw [mobiusSubst_apply]
  exact subst_X mobius_hasSubst

lemma mobiusSubst_constant (f : ℚ⟦X⟧) : constantCoeff (mobiusSubst f)=constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, mobiusSubst_apply, mobiusArgument,
    A363990Series.coeff_subst_X_mul]
  simp

lemma rescale_C_series {R : Type*} [CommSemiring R] (a r : R) :
    rescale a (C r)=C r := by
  ext n
  by_cases h : n=0 <;> simp [coeff_rescale, coeff_C, h]

lemma constantCoeff_map_series {R S : Type*} [CommSemiring R] [CommSemiring S]
    (ψ : R →+* S) (f : R⟦X⟧) : constantCoeff (map ψ f)=ψ (constantCoeff f) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply]

/-- The normalized transform of the original nonalternating double series. -/
def transformedB (B : ℚ⟦X⟧⟦X⟧) : ℚ⟦X⟧⟦X⟧ :=
  C mobiusFactor * map mobiusSubst B

/-- Equality of normalized square roots only requires the double constant. -/
theorem nested_same_square_denominator {S T D : ℚ⟦X⟧⟦X⟧}
    (hS : S^2*D=1) (hT : T^2*D=1)
    (hcS : constantCoeff (constantCoeff S)=1)
    (hcT : constantCoeff (constantCoeff T)=1) : S=T := by
  have hD : D ≠ 0 := by intro hz; rw [hz, mul_zero] at hS; exact zero_ne_one hS
  have he : S^2=T^2 := mul_right_cancel₀ hD (hS.trans hT.symm)
  have hz : (S-T)*(S+T)=0 := by linear_combination he
  rcases mul_eq_zero.mp hz with hh | hh
  · exact sub_eq_zero.mp hh
  · have hc := congrArg (fun f : ℚ⟦X⟧⟦X⟧ => constantCoeff (constantCoeff f)) hh
    simp only [map_add, hcS, hcT, map_zero] at hc
    norm_num at hc

/-- The quadratic substitution identifies the original and square-binomial
bivariate generating functions from their algebraic equations. -/
theorem bivariate_equality (B Q : ℚ⟦X⟧⟦X⟧)
    (hB : B^2*((1-X)^2-4*C (X : ℚ⟦X⟧))=1)
    (hQ : Q^2*((1-C (1+(X : ℚ⟦X⟧))*X)^2-C (4*(X : ℚ⟦X⟧))*X^2)=1)
    (hB0 : constantCoeff (constantCoeff B)=1)
    (hQ0 : constantCoeff (constantCoeff Q)=1) :
    transformedB B=rescale rowScale Q := by
  have hb : (map mobiusSubst B)^2*((1-X)^2-C (4*mobiusArgument))=1 := by
    have h := congrArg (map mobiusSubst) hB
    simpa only [map_mul, map_pow, map_sub, map_one, map_ofNat,
      PowerSeries.map_X, PowerSeries.map_C, mobiusSubst_X] using h
  have hs := rationalize_original_square (X : ℚ⟦X⟧) positiveGeometricSeries geometricSeries
    positiveGeometric_inverse geometricSeries_inverse (map mobiusSubst B) hb
  dsimp only at hs
  change (transformedB B)^2*
    ((1-C ((1+(X : ℚ⟦X⟧))*rowScale)*X)^2-C (4*(X : ℚ⟦X⟧)*rowScale^2)*X^2)=1 at hs
  have hq : (rescale rowScale Q)^2*
    ((1-C ((1+(X : ℚ⟦X⟧))*rowScale)*X)^2-C (4*(X : ℚ⟦X⟧)*rowScale^2)*X^2)=1 := by
    have h := congrArg (rescale rowScale) hQ
    simp only [map_mul, map_pow, map_sub, map_one, rescale_C_series, rescale_X] at h
    convert h using 1 <;> simp only [map_mul, map_pow] <;> ring
  apply nested_same_square_denominator hs hq
  · simp only [transformedB, map_mul, constantCoeff_C, constantCoeff_map_series]
    rw [mobiusSubst_constant]
    simp [mobiusFactor, positiveGeometric_constant, hB0]
  · rw [← coeff_zero_eq_constantCoeff_apply (rescale rowScale Q), coeff_rescale]
    simpa only [pow_zero, one_mul, coeff_zero_eq_constantCoeff_apply] using hQ0

end A363990Transform
end

end

section

noncomputable section
namespace A363990Transform
open PowerSeries Finset

/-- Coefficient kernel for the original alternating binomial transform. -/
theorem alternating_quadratic_kernel (N k : ℕ) (hk : k ≤ N) :
    coeff (N-k) ((1-X : ℚ⟦X⟧)^(2*N+1)*positiveGeometricSeries^(2*k+1)) =
      (-4 : ℚ)^(N-k)*(N.choose k : ℚ) := by
  have hh := odd_quadratic_kernel N (N-k) (Nat.sub_le _ _)
  rw [show N-(N-k)=k by omega] at hh
  calc
    _ = (-1 : ℚ)^(N-k) * coeff (N-k)
        ((1+X : ℚ⟦X⟧)^(2*N+1)*geometricSeries^(2*k+1)) := by
      rw [← coeff_rescale]
      congr 1
      simp [positiveGeometricSeries, sub_eq_add_neg]
    _ = _ := by
      rw [hh, Nat.choose_symm hk, ← mul_assoc, ← mul_pow]
      norm_num

/-- The rationalized nonalternating series gives the exact original
alternating sum after the finite coefficient extraction. -/
theorem left_coefficient_generic (f : ℚ⟦X⟧) (N : ℕ) :
    coeff N ((1-X : ℚ⟦X⟧)^(2*N) *
      (mobiusFactor * f.subst mobiusArgument)) =
      ∑ k ∈ range (N+1), (-4 : ℚ)^(N-k)*(N.choose k : ℚ)*coeff k f := by
  have he : (1-X : ℚ⟦X⟧)^(2*N)*(mobiusFactor*f.subst mobiusArgument) =
      ((1-X)^(2*N+1)*positiveGeometricSeries)*f.subst mobiusArgument := by
    unfold mobiusFactor
    rw [pow_succ]
    ring
  rw [he, mobiusArgument, A363990Series.coeff_mul_subst_X_mul]
  apply sum_congr rfl
  intro k hk
  have hkN : k ≤ N := by have := mem_range.mp hk; omega
  have hp : ((1-X : ℚ⟦X⟧)^(2*N+1)*positiveGeometricSeries)*
      (positiveGeometricSeries^2)^k =
      (1-X)^(2*N+1)*positiveGeometricSeries^(2*k+1) := by
    simp only [pow_mul, pow_succ]
    ring
  rw [hp, alternating_quadratic_kernel N k hkN]
  ring

/-- Nested-series interface: only the known nonalternating coefficient row
is required from the original generating function. -/
theorem left_coefficient (B : ℚ⟦X⟧⟦X⟧) (N l : ℕ)
    (hB : ∀ k : ℕ, coeff k (coeff l B) =
      ((l+2*k).choose (2*k) : ℚ)*((2*k).choose k : ℚ)) :
    coeff N ((1-X : ℚ⟦X⟧)^(2*N)*coeff l (transformedB B)) =
      ∑ k ∈ range (N+1), (-4 : ℚ)^(N-k)*(N.choose k : ℚ)*
        ((l+2*k).choose (2*k) : ℚ)*((2*k).choose k : ℚ) := by
  rw [transformedB, coeff_C_mul, coeff_map, mobiusSubst_apply, left_coefficient_generic]
  apply sum_congr rfl
  intro k _
  rw [hB]
  ring

/-- Exact pinned A363990 left endpoint. -/
theorem a_left_coefficient (B : ℚ⟦X⟧⟦X⟧) (N : ℕ)
    (hB : ∀ k : ℕ, coeff k (coeff (4*N) B) =
      ((4*N+2*k).choose (2*k) : ℚ)*((2*k).choose k : ℚ)) :
    coeff N ((1-X : ℚ⟦X⟧)^(2*N)*coeff (4*N) (transformedB B)) =
      (OMA.S_oeis_a363990.a N : ℚ) := by
  rw [left_coefficient B N (4*N) hB]
  unfold OMA.S_oeis_a363990.a
  push_cast
  rfl

end A363990Transform
end

end

section

noncomputable section
namespace A363990Transform
open PowerSeries A363990OriginalGF A363990Square

/-- Exact formal-series change of variables, with both double generating
functions identified from their normalized algebraic equations. -/
theorem exact_generating_function :
    transformedB (originalB ℚ)=rescale rowScale squareGF := by
  apply bivariate_equality (originalB ℚ) squareGF
  · exact originalB_square ℚ
  · exact squareGF_square
  · exact corner_originalB ℚ
  · rw [← coeff_zero_eq_constantCoeff_apply squareGF,
      ← coeff_zero_eq_constantCoeff_apply (coeff 0 squareGF)]
    simp

/-- The original v₄ sequence is exactly the integral convolution used by
the valuation and cancellation proofs. -/
theorem exact_identity (N : ℕ) :
    OMA.S_oeis_a363990.a N=A363990Convolution.convolution N := by
  apply Int.cast_injective (α := ℚ)
  have hleft := a_left_coefficient (originalB ℚ) N (fun k => by
    simpa only [Nat.centralBinom_eq_two_mul_choose] using coeff_coeff_originalB ℚ (4*N) k)
  have he := congrArg (fun F : ℚ⟦X⟧⟦X⟧ =>
    coeff N ((1-X : ℚ⟦X⟧)^(2*N)*coeff (4*N) F)) exact_generating_function
  rw [hleft, coeff_rescale, coeff_squareGF] at he
  exact he.trans (A363990Series.scaled_row_coeff N geometricSeries (squareRow (4*N))
    geometricSeries_inverse (fun j => coeff_squareRow (4*N) j))

end A363990Transform
end

end

section

/-- Peter Bala's supercongruence for the exact A363990 sequence. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a363990.main := by
  intro p n r hp hp5 hn hr
  rw [A363990Transform.exact_identity, A363990Transform.exact_identity]
  exact A363990Convolution.transformed_congruence hp hp5 hn hr

end
