import FormalConjectures.ErdosProblems.«510»
import Mathlib

-- Problem: Erdős Problem 510 — bedert
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/510.lean:65 (declaration Erdos510.erdos_510.variants.bedert)
-- Credit: @yhay81 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
# Proof of `Erdos510.erdos_510.variants.bedert`

We prove the stronger uniform log-free polynomial bound: for every nonempty finite set
`S ⊂ ℕ \ {0}` of size `N`, there exists `θ : ℝ` such that
`∑ n ∈ S, Real.cos (n * θ) < - (1 / 100) * N ^ (1 / 7 : ℝ)` (in fact, `≪ N ^ (1 / 5)`).

The proof works completely discretely on `ZMod Q` for a large prime `Q > 10 * max(S) + 1`,
combining:
1. Roth's Cauchy–Schwarz lower bound on additive triples (Bedert, arXiv:2509.05260v3, Lemma 4.1);
2. Shankar's exact total-boundary counting identity (arXiv:2609.05338, Lemma 3.1) to find a
   nonzero shift `t` with `|B_t| ≥ |A| / (6 K)`;
3. Bedert's improved `L²` decomposition of `1̂_{B_t}` (Lemma 7.1), 32-case Fourier coefficient
   separation (Lemma 7.2), and asymmetric-boundary upper bound `|B_t| ≪ K⁴` (Proposition 7.3).
-/

namespace OMA.Bedert

open Finset

section DiscreteFourier

variable {Q : ℕ} [Fact Q.Prime]

/-- Standard additive character `e(x) = exp(2πi x / Q)` on `ZMod Q`. -/
noncomputable def e (x : ZMod Q) : ℂ := ZMod.stdAddChar x

/-- Exponential sum with frequency set `E`. -/
noncomputable def gB (E : Finset (ZMod Q)) (x : ZMod Q) : ℂ := ∑ a ∈ E, e (a * x)

/-- Real part of the exponential sum `gB E`. -/
noncomputable def fR (E : Finset (ZMod Q)) (x : ZMod Q) : ℝ := (gB E x).re

/-- Normalized Fourier coefficient on `ZMod Q`. -/
noncomputable def fhat (u : ZMod Q → ℂ) (m : ZMod Q) : ℂ :=
  (∑ x, u x * e (-(m * x))) / (Q : ℂ)

/-- Normalized convolution on `ZMod Q`. -/
noncomputable def conv (u v : ZMod Q → ℂ) (x : ZMod Q) : ℂ :=
  (∑ y, u y * v (x - y)) / (Q : ℂ)

/-- Normalized `L¹` norm. -/
noncomputable def N1 (u : ZMod Q → ℂ) : ℝ := (∑ x, ‖u x‖) / (Q : ℝ)

/-- Normalized squared `L²` norm. -/
noncomputable def N2sq (u : ZMod Q → ℂ) : ℝ := (∑ x, ‖u x‖ ^ 2) / (Q : ℝ)

/-- Normalized `L²` norm. -/
noncomputable def N2 (u : ZMod Q → ℂ) : ℝ := Real.sqrt (N2sq u)

/-- Symmetry of a subset of `ZMod Q`. -/
def Sym (A : Finset (ZMod Q)) : Prop := ∀ a ∈ A, -a ∈ A

/-- Incoming intersection `A_t = {a ∈ A : a - t ∈ A}`. -/
def At (A : Finset (ZMod Q)) (t : ZMod Q) : Finset (ZMod Q) :=
  A.filter (fun a => a - t ∈ A)

/-- Asymmetric boundary `B_t = {a ∈ A : a - t ∈ A ∧ a + t ∉ A}`. -/
def Bt (A : Finset (ZMod Q)) (t : ZMod Q) : Finset (ZMod Q) :=
  A.filter (fun a => a - t ∈ A ∧ a + t ∉ A)

private lemma Q_pos : (0 : ℝ) < (Q : ℝ) := by
  exact_mod_cast (Fact.out : Q.Prime).pos

private lemma Q_ne_zero_C : (Q : ℂ) ≠ 0 := by
  exact_mod_cast (Fact.out : Q.Prime).ne_zero

private lemma e_add (x y : ZMod Q) : e (x + y) = e x * e y :=
  AddChar.map_add_eq_mul _ _ _

private lemma e_zero : e (0 : ZMod Q) = 1 :=
  AddChar.map_zero_eq_one _

private lemma norm_e (x : ZMod Q) : ‖e x‖ = 1 := by
  unfold e
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

private lemma e_neg (x : ZMod Q) : e (-x) = (starRingEnd ℂ) (e x) := by
  unfold e
  rw [AddChar.map_neg_eq_inv]
  exact Complex.inv_eq_conj (norm_e x)

private lemma e_orth (r : ZMod Q) : ∑ x : ZMod Q, e (r * x) = if r = 0 then (Q : ℂ) else 0 := by
  unfold e
  simp_rw [mul_comm r]
  rw [AddChar.sum_mulShift r (ZMod.isPrimitive_stdAddChar Q)]
  simp [ZMod.card]

private lemma e_natCast (n : ℕ) (x : ZMod Q) :
    (e ((n : ZMod Q) * x)).re = Real.cos ((n : ℝ) * (2 * Real.pi * (x.val : ℝ) / (Q : ℝ))) := by
  have h : (n : ZMod Q) * x = (((n * x.val : ℕ) : ℤ) : ZMod Q) := by
    rw [Int.cast_natCast, Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [h]
  unfold e
  rw [ZMod.stdAddChar_coe]
  have h2 : (2 * (Real.pi : ℂ) * Complex.I * (((n * x.val : ℕ) : ℤ) : ℂ) / ((Q : ℕ) : ℂ)) =
      (((2 * Real.pi * ((n : ℝ) * (x.val : ℝ)) / (Q : ℝ)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h2, Complex.exp_ofReal_mul_I_re]
  congr 1
  ring

private lemma fourier_inv (u : ZMod Q → ℂ) (x : ZMod Q) :
    ∑ m, fhat u m * e (m * x) = u x := by
  unfold fhat
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner : ∀ y : ZMod Q,
      ∑ m : ZMod Q, u y * e (-(m * y)) * e (m * x) = if y = x then u y * (Q : ℂ) else 0 := by
    intro y
    have hterm : ∀ m : ZMod Q, u y * e (-(m * y)) * e (m * x) = u y * e ((x - y) * m) := by
      intro m
      rw [mul_assoc, ← e_add]
      congr 2
      ring
    simp_rw [hterm, ← Finset.mul_sum, e_orth]
    by_cases hyx : y = x
    · subst hyx
      simp
    · have hne : x - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hyx)
      simp [hyx, hne]
  simp_rw [hinner, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact mul_div_cancel_right₀ _ Q_ne_zero_C

private lemma fhat_add (u v : ZMod Q → ℂ) (m : ZMod Q) :
    fhat (fun x => u x + v x) m = fhat u m + fhat v m := by
  simp only [fhat, add_mul, Finset.sum_add_distrib, add_div]

private lemma fhat_sub (u v : ZMod Q → ℂ) (m : ZMod Q) :
    fhat (fun x => u x - v x) m = fhat u m - fhat v m := by
  simp only [fhat, sub_mul, Finset.sum_sub_distrib, sub_div]

private lemma fhat_const_mul (c : ℂ) (u : ZMod Q → ℂ) (m : ZMod Q) :
    fhat (fun x => c * u x) m = c * fhat u m := by
  simp only [fhat, mul_assoc, ← Finset.mul_sum, mul_div_assoc]

private lemma fhat_mul_e (t : ZMod Q) (u : ZMod Q → ℂ) (m : ZMod Q) :
    fhat (fun x => e (t * x) * u x) m = fhat u (m - t) := by
  unfold fhat
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  dsimp only
  rw [mul_comm (e (t * x)) (u x), mul_assoc, ← e_add]
  congr 2
  ring

private lemma fhat_gB (E : Finset (ZMod Q)) (m : ZMod Q) :
    fhat (gB E) m = if m ∈ E then (1 : ℂ) else 0 := by
  unfold fhat gB
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner : ∀ a : ZMod Q,
      ∑ x : ZMod Q, e (a * x) * e (-(m * x)) = if a = m then (Q : ℂ) else 0 := by
    intro a
    have hterm : ∀ x : ZMod Q, e (a * x) * e (-(m * x)) = e ((a - m) * x) := by
      intro x
      rw [← e_add]
      congr 1
      ring
    simp_rw [hterm, e_orth, sub_eq_zero]
  simp_rw [hinner, Finset.sum_ite_eq']
  split_ifs with hm
  · exact div_self Q_ne_zero_C
  · exact zero_div _

private lemma fhat_neg_arg (u : ZMod Q → ℂ) (m : ZMod Q) :
    fhat (fun x => u (-x)) m = fhat u (-m) := by
  unfold fhat
  congr 1
  have h := Equiv.sum_comp (Equiv.neg (ZMod Q)) (fun x => u x * e (-((-m) * x)))
  rw [← h]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Equiv.neg_apply]
  congr 2
  ring

private lemma fhat_conj (u : ZMod Q → ℂ) (m : ZMod Q) :
    fhat (fun x => (starRingEnd ℂ) (u x)) m = (starRingEnd ℂ) (fhat u (-m)) := by
  unfold fhat
  rw [map_div₀, map_sum, Complex.conj_natCast]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, ← e_neg]
  congr 2
  ring

private lemma fhat_real_neg_arg (r : ZMod Q → ℝ) (m : ZMod Q) :
    fhat (fun x => (r (-x) : ℂ)) m = (starRingEnd ℂ) (fhat (fun x => (r x : ℂ)) m) := by
  have h1 : fhat (fun x => (r (-x) : ℂ)) m = fhat (fun y => (r y : ℂ)) (-m) :=
    fhat_neg_arg (fun y => (r y : ℂ)) m
  have h2 := fhat_conj (fun x => (r x : ℂ)) (-m)
  simp only [Complex.conj_ofReal, neg_neg] at h2
  exact h1.trans h2

private lemma fhat_conv (u v : ZMod Q → ℂ) (m : ZMod Q) :
    fhat (conv u v) m = fhat u m * fhat v m := by
  unfold fhat conv
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner : ∀ y : ZMod Q,
      ∑ x : ZMod Q, u y * v (x - y) * e (-(m * x)) =
        (u y * e (-(m * y))) * ∑ z : ZMod Q, v z * e (-(m * z)) := by
    intro y
    rw [Finset.mul_sum]
    have hre := Equiv.sum_comp (Equiv.subRight y) (fun z => u y * e (-(m * y)) * (v z * e (-(m * z))))
    rw [← hre]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Equiv.subRight_apply]
    have he : e (-(m * x)) = e (-(m * y)) * e (-(m * (x - y))) := by
      rw [← e_add]
      congr 1
      ring
    rw [he]
    ring
  simp_rw [hinner, ← Finset.sum_mul]
  ring

private lemma conv_comm (u v : ZMod Q → ℂ) (x : ZMod Q) : conv u v x = conv v u x := by
  unfold conv
  congr 1
  have h := Equiv.sum_comp (Equiv.subLeft x) (fun y => u y * v (x - y))
  rw [← h]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Equiv.subLeft_apply, sub_sub_cancel]
  ring

private lemma conv_add_left (u1 u2 v : ZMod Q → ℂ) (x : ZMod Q) :
    conv (fun y => u1 y + u2 y) v x = conv u1 v x + conv u2 v x := by
  simp only [conv, add_mul, Finset.sum_add_distrib, add_div]

private lemma conv_add_right (u v1 v2 : ZMod Q → ℂ) (x : ZMod Q) :
    conv u (fun y => v1 y + v2 y) x = conv u v1 x + conv u v2 x := by
  simp only [conv, mul_add, Finset.sum_add_distrib, add_div]

private lemma conv_sub_left (u1 u2 v : ZMod Q → ℂ) (x : ZMod Q) :
    conv (fun y => u1 y - u2 y) v x = conv u1 v x - conv u2 v x := by
  simp only [conv, sub_mul, Finset.sum_sub_distrib, sub_div]

private lemma conv_sub_right (u v1 v2 : ZMod Q → ℂ) (x : ZMod Q) :
    conv u (fun y => v1 y - v2 y) x = conv u v1 x - conv u v2 x := by
  simp only [conv, mul_sub, Finset.sum_sub_distrib, sub_div]

private lemma conv_gB (E F : Finset (ZMod Q)) (x : ZMod Q) :
    conv (gB E) (gB F) x = gB (E ∩ F) x := by
  rw [← fourier_inv (conv (gB E) (gB F)) x, ← fourier_inv (gB (E ∩ F)) x]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [fhat_conv, fhat_gB, fhat_gB, fhat_gB]
  by_cases hmE : m ∈ E <;> by_cases hmF : m ∈ F <;> simp [hmE, hmF]

private lemma parseval_inner (u v : ZMod Q → ℂ) :
    (∑ x, u x * v x) / (Q : ℂ) = ∑ m, fhat u (-m) * fhat v m := by
  have h1 : ∑ x, u x * v x = ∑ m, fhat u m * ∑ x, v x * e (m * x) := by
    calc ∑ x, u x * v x
        = ∑ x, (∑ m, fhat u m * e (m * x)) * v x :=
          Finset.sum_congr rfl fun x _ => by rw [fourier_inv]
      _ = ∑ x, ∑ m, fhat u m * (v x * e (m * x)) :=
          Finset.sum_congr rfl fun x _ => by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun m _ => by ring
      _ = ∑ m, ∑ x, fhat u m * (v x * e (m * x)) := Finset.sum_comm
      _ = ∑ m, fhat u m * ∑ x, v x * e (m * x) :=
          Finset.sum_congr rfl fun m _ => (Finset.mul_sum _ _ _).symm
  have h2 : ∀ m : ZMod Q, ∑ x, v x * e (m * x) = (Q : ℂ) * fhat v (-m) := by
    intro m
    unfold fhat
    rw [mul_div_cancel₀ _ Q_ne_zero_C]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 2
    ring
  rw [h1]
  simp_rw [h2]
  have h3 : (∑ m, fhat u m * ((Q : ℂ) * fhat v (-m))) / (Q : ℂ) = ∑ m, fhat u m * fhat v (-m) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show fhat u m * ((Q : ℂ) * fhat v (-m)) = (Q : ℂ) * (fhat u m * fhat v (-m)) by ring]
    exact mul_div_cancel_left₀ _ Q_ne_zero_C
  rw [h3]
  have hre := Equiv.sum_comp (Equiv.neg (ZMod Q)) (fun m => fhat u (-m) * fhat v m)
  rw [← hre]
  refine Finset.sum_congr rfl fun m _ => by simp

private lemma parseval_sq (u : ZMod Q → ℂ) :
    N2sq u = ∑ m, ‖fhat u m‖ ^ 2 := by
  have hC : ((N2sq u : ℝ) : ℂ) = ((∑ m, ‖fhat u m‖ ^ 2 : ℝ) : ℂ) := by
    unfold N2sq
    rw [Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast, Complex.ofReal_sum]
    have hL : ∑ x, ((‖u x‖ ^ 2 : ℝ) : ℂ) = ∑ x, u x * (starRingEnd ℂ) (u x) :=
      Finset.sum_congr rfl fun x _ => by rw [Complex.ofReal_pow, ← Complex.mul_conj']
    rw [hL, parseval_inner]
    have hR : ∑ m, fhat u (-m) * fhat (fun x => (starRingEnd ℂ) (u x)) m =
        ∑ m, ((‖fhat u (-m)‖ ^ 2 : ℝ) : ℂ) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [fhat_conj, Complex.ofReal_pow, ← Complex.mul_conj']
    rw [hR]
    have hre := Equiv.sum_comp (Equiv.neg (ZMod Q)) (fun m => ((‖fhat u m‖ ^ 2 : ℝ) : ℂ))
    exact hre
  exact Complex.ofReal_injective hC

private lemma N2sq_nonneg (u : ZMod Q → ℂ) : 0 ≤ N2sq u := by
  unfold N2sq
  exact div_nonneg (Finset.sum_nonneg fun x _ => sq_nonneg _) Q_pos.le

private lemma N2_nonneg (u : ZMod Q → ℂ) : 0 ≤ N2 u := Real.sqrt_nonneg _

private lemma N2_sq (u : ZMod Q → ℂ) : N2 u ^ 2 = N2sq u :=
  Real.sq_sqrt (N2sq_nonneg u)

private lemma N2sq_gB (E : Finset (ZMod Q)) : N2sq (gB E) = (E.card : ℝ) := by
  rw [parseval_sq]
  have h1 : ∀ m : ZMod Q, ‖fhat (gB E) m‖ ^ 2 = if m ∈ E then (1 : ℝ) else 0 := by
    intro m
    rw [fhat_gB]
    split_ifs <;> simp
  simp_rw [h1, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]

private lemma N2_le_of_bdd (u : ZMod Q → ℂ) (B : ℝ) (hB : 0 ≤ B) (h : ∀ x, ‖u x‖ ≤ B) :
    N2 u ≤ B := by
  unfold N2
  rw [Real.sqrt_le_iff]
  refine ⟨hB, ?_⟩
  unfold N2sq
  rw [div_le_iff₀ Q_pos]
  calc ∑ x, ‖u x‖ ^ 2 ≤ ∑ _x : ZMod Q, B ^ 2 :=
        Finset.sum_le_sum fun x _ => pow_le_pow_left₀ (norm_nonneg _) (h x) 2
    _ = B ^ 2 * (Q : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; ring

private lemma N2_add_le (u v : ZMod Q → ℂ) :
    N2 (fun x => u x + v x) ≤ N2 u + N2 v := by
  have hcs : (∑ x, ‖u x‖ * ‖v x‖) ^ 2 ≤ (∑ x, ‖u x‖ ^ 2) * (∑ x, ‖v x‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq univ (fun x => ‖u x‖) (fun x => ‖v x‖)
  have hprod : (∑ x, ‖u x‖ * ‖v x‖) / (Q : ℝ) ≤ N2 u * N2 v := by
    have hnn : 0 ≤ N2 u * N2 v := mul_nonneg (N2_nonneg u) (N2_nonneg v)
    have hsq : ((∑ x, ‖u x‖ * ‖v x‖) / (Q : ℝ)) ^ 2 ≤ (N2 u * N2 v) ^ 2 := by
      rw [mul_pow, N2_sq, N2_sq]
      unfold N2sq
      rw [div_pow, div_mul_div_comm, ← sq]
      exact div_le_div_of_nonneg_right hcs (sq_nonneg _)
    have hlhs : 0 ≤ (∑ x : ZMod Q, ‖u x‖ * ‖v x‖) / (Q : ℝ) :=
      div_nonneg (Finset.sum_nonneg fun x _ => mul_nonneg (norm_nonneg (u x)) (norm_nonneg (v x))) Q_pos.le
    nlinarith
  have hsq_le : N2sq (fun x => u x + v x) ≤ (N2 u + N2 v) ^ 2 := by
    have hpt : ∀ x, ‖u x + v x‖ ^ 2 ≤ ‖u x‖ ^ 2 + 2 * (‖u x‖ * ‖v x‖) + ‖v x‖ ^ 2 := by
      intro x
      have htri := norm_add_le (u x) (v x)
      nlinarith [norm_nonneg (u x + v x), norm_nonneg (u x), norm_nonneg (v x)]
    calc N2sq (fun x => u x + v x)
        ≤ (∑ x, (‖u x‖ ^ 2 + 2 * (‖u x‖ * ‖v x‖) + ‖v x‖ ^ 2)) / (Q : ℝ) :=
          div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => hpt x) Q_pos.le
      _ = N2sq u + 2 * ((∑ x, ‖u x‖ * ‖v x‖) / (Q : ℝ)) + N2sq v := by
          unfold N2sq
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
          ring
      _ ≤ N2 u ^ 2 + 2 * (N2 u * N2 v) + N2 v ^ 2 := by
          rw [N2_sq, N2_sq]; linarith
      _ = (N2 u + N2 v) ^ 2 := by ring
  unfold N2
  exact Real.sqrt_le_iff.mpr ⟨add_nonneg (N2_nonneg u) (N2_nonneg v), hsq_le⟩

private lemma N2_sub_le (u v : ZMod Q → ℂ) :
    N2 (fun x => u x - v x) ≤ N2 u + N2 v := by
  have h : (fun x => u x - v x) = (fun x => u x + (-v x)) := by ext x; ring
  have hneg : N2 (fun x => -v x) = N2 v := by unfold N2 N2sq; simp
  rw [h, ← hneg]
  exact N2_add_le u (fun x => -v x)

private lemma N2_const_mul (c : ℂ) (u : ZMod Q → ℂ) :
    N2 (fun x => c * u x) = ‖c‖ * N2 u := by
  unfold N2 N2sq
  have h : (∑ x, ‖c * u x‖ ^ 2) / (Q : ℝ) = ‖c‖ ^ 2 * ((∑ x, ‖u x‖ ^ 2) / (Q : ℝ)) := by
    simp_rw [norm_mul, mul_pow, ← Finset.mul_sum]
    ring
  rw [h, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg c)]

private lemma N2_conj_neg (u : ZMod Q → ℂ) :
    N2 (fun x => (starRingEnd ℂ) (u (-x))) = N2 u := by
  unfold N2 N2sq
  congr 2
  have h := Equiv.sum_comp (Equiv.neg (ZMod Q)) (fun x => ‖u x‖ ^ 2)
  rw [← h]
  refine Finset.sum_congr rfl fun x _ => by simp

private lemma N2_conv_gB_le (u : ZMod Q → ℂ) (E : Finset (ZMod Q)) :
    N2 (conv u (gB E)) ≤ N2 u := by
  unfold N2
  apply Real.sqrt_le_sqrt
  rw [parseval_sq, parseval_sq]
  refine Finset.sum_le_sum fun m _ => ?_
  rw [fhat_conv, fhat_gB, norm_mul]
  split_ifs <;> simp

private lemma young_inf_left (u v : ZMod Q → ℂ) (L : ℝ) (hv : ∀ x, ‖v x‖ ≤ L) (x : ZMod Q) :
    ‖conv u v x‖ ≤ N1 u * L := by
  have hs : ‖∑ y, u y * v (x - y)‖ ≤ (∑ y, ‖u y‖) * L := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hv _) (norm_nonneg _)
  unfold conv N1
  rw [norm_div, Complex.norm_natCast, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hs Q_pos.le

private lemma young_inf_right (u v : ZMod Q → ℂ) (L : ℝ) (hu : ∀ x, ‖u x‖ ≤ L) (x : ZMod Q) :
    ‖conv u v x‖ ≤ L * N1 v := by
  rw [conv_comm, mul_comm]
  exact young_inf_left v u L hu x

private lemma conv_dom (u v : ZMod Q → ℂ) (w1 w2 : ZMod Q → ℝ)
    (hu : ∀ x, ‖u x‖ ≤ w1 x) (hv : ∀ x, ‖v x‖ ≤ w2 x) (x : ZMod Q) :
    ‖conv u v x‖ ≤ (∑ y, w1 y * w2 (x - y)) / (Q : ℝ) := by
  have hs : ‖∑ y, u y * v (x - y)‖ ≤ ∑ y, w1 y * w2 (x - y) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    rw [norm_mul]
    exact mul_le_mul (hu y) (hv (x - y)) (norm_nonneg _) ((norm_nonneg _).trans (hu y))
  unfold conv
  rw [norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right hs Q_pos.le

private lemma split_norm (z : ℂ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hz : ‖z‖ ≤ a + b) :
    ∃ z1 z2 : ℂ, z = z1 + z2 ∧ ‖z1‖ ≤ a ∧ ‖z2‖ ≤ b := by
  by_cases hab : a + b = 0
  · have hz0 : z = 0 := norm_eq_zero.mp (le_antisymm (by linarith) (norm_nonneg z))
    exact ⟨0, 0, by simp [hz0], by simpa using ha, by simpa using hb⟩
  · have hpos : 0 < a + b := lt_of_le_of_ne (by linarith) (Ne.symm hab)
    have h1 : a / (a + b) + b / (a + b) = 1 := by rw [← add_div, div_self hab]
    refine ⟨(a / (a + b) : ℝ) • z, (b / (a + b) : ℝ) • z, ?_, ?_, ?_⟩
    · rw [← add_smul, h1, one_smul]
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg ha hpos.le)]
      calc a / (a + b) * ‖z‖ ≤ a / (a + b) * (a + b) :=
            mul_le_mul_of_nonneg_left hz (div_nonneg ha hpos.le)
        _ = a := by field_simp
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hb hpos.le)]
      calc b / (a + b) * ‖z‖ ≤ b / (a + b) * (a + b) :=
            mul_le_mul_of_nonneg_left hz (div_nonneg hb hpos.le)
        _ = b := by field_simp

/- ## Section 2: Symmetric sets, `1 ≤ K`, and Roth's triple lower bound -/

private lemma gB_eq_fR (A : Finset (ZMod Q)) (hA : Sym A) (x : ZMod Q) :
    gB A x = ((fR A x : ℝ) : ℂ) := by
  have hconj : (starRingEnd ℂ) (gB A x) = gB A x := by
    unfold gB
    rw [map_sum]
    refine Finset.sum_nbij' (fun a => -a) (fun a => -a) (fun a ha => hA a ha)
      (fun a ha => hA a ha) (fun a _ => neg_neg a) (fun a _ => neg_neg a) (fun a _ => ?_)
    show (starRingEnd ℂ) (e (a * x)) = e (-a * x)
    rw [← e_neg, neg_mul]
  rw [Complex.conj_eq_iff_re] at hconj
  exact hconj.symm

private lemma fR_neg (A : Finset (ZMod Q)) (hA : Sym A) (x : ZMod Q) :
    fR A (-x) = fR A x := by
  apply Complex.ofReal_injective
  rw [← gB_eq_fR A hA, ← gB_eq_fR A hA]
  unfold gB
  refine Finset.sum_nbij' (fun a => -a) (fun a => -a) (fun a ha => hA a ha)
    (fun a ha => hA a ha) (fun a _ => neg_neg a) (fun a _ => neg_neg a) (fun a _ => ?_)
  congr 1
  ring

private lemma sum_fR (A : Finset (ZMod Q)) (h0 : (0 : ZMod Q) ∉ A) :
    ∑ x : ZMod Q, fR A x = 0 := by
  have hC : ∑ x : ZMod Q, gB A x = 0 := by
    unfold gB
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun a ha => ?_
    have ha0 : a ≠ 0 := fun h => h0 (h ▸ ha)
    rw [e_orth, if_neg ha0]
  have := congrArg Complex.re hC
  simpa [fR, Complex.re_sum] using this

private lemma one_le_K (A : Finset (ZMod Q)) (hA : Sym A) (h0 : (0 : ZMod Q) ∉ A)
    (hne : A.Nonempty) (K : ℝ) (hK : ∀ x, 0 ≤ fR A x + K) : 1 ≤ K := by
  obtain ⟨a0, ha0⟩ := hne
  have ha0_ne : a0 ≠ 0 := fun h => h0 (h ▸ ha0)
  have h1 : fhat (fun x => ((fR A x + K : ℝ) : ℂ)) a0 = 1 := by
    have hsplit : (fun x => ((fR A x + K : ℝ) : ℂ)) = (fun x => gB A x + (K : ℂ)) := by
      ext x; rw [Complex.ofReal_add, gB_eq_fR A hA]
    rw [hsplit, fhat_add, fhat_gB, if_pos ha0]
    have hconst : fhat (fun _ => (K : ℂ)) a0 = 0 := by
      unfold fhat
      rw [← Finset.mul_sum]
      have horth : ∑ x : ZMod Q, e (-(a0 * x)) = 0 := by
        have ht : ∀ x : ZMod Q, e (-(a0 * x)) = e ((-a0) * x) := fun x => by congr 1; ring
        simp_rw [ht, e_orth, if_neg (neg_ne_zero.mpr ha0_ne)]
      rw [horth, mul_zero, zero_div]
    rw [hconst, add_zero]
  have hnorm : (1 : ℝ) ≤ (∑ x : ZMod Q, (fR A x + K)) / (Q : ℝ) := by
    calc (1 : ℝ) = ‖fhat (fun x => ((fR A x + K : ℝ) : ℂ)) a0‖ := by rw [h1, norm_one]
      _ = ‖∑ x, ((fR A x + K : ℝ) : ℂ) * e (-(a0 * x))‖ / (Q : ℝ) := by
          unfold fhat; rw [norm_div, Complex.norm_natCast]
      _ ≤ (∑ x, ‖((fR A x + K : ℝ) : ℂ) * e (-(a0 * x))‖) / (Q : ℝ) :=
          div_le_div_of_nonneg_right (norm_sum_le _ _) Q_pos.le
      _ = (∑ x, (fR A x + K)) / (Q : ℝ) := by
          congr 1
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK x)]
  have hsum : (∑ x : ZMod Q, (fR A x + K)) / (Q : ℝ) = K := by
    rw [Finset.sum_add_distrib, sum_fR A h0, zero_add, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul, mul_div_cancel_left₀ _ Q_pos.ne']
  linarith

private lemma ww (A : Finset (ZMod Q)) (hA : Sym A) (h0 : (0 : ZMod Q) ∉ A) (K : ℝ) (x : ZMod Q) :
    (∑ y, (fR A y + K) * (fR A (x - y) + K)) / (Q : ℝ) = fR A x + K ^ 2 := by
  have hrefl : ∑ y : ZMod Q, fR A (x - y) = 0 :=
    (Equiv.sum_comp (Equiv.subLeft x) (fun y => fR A y)).trans (sum_fR A h0)
  have hconv : (∑ y, fR A y * fR A (x - y)) / (Q : ℝ) = fR A x := by
    have hc : conv (gB A) (gB A) x = gB A x := by rw [conv_gB, Finset.inter_self]
    unfold conv at hc
    simp only [gB_eq_fR A hA] at hc
    apply Complex.ofReal_injective
    push_cast
    exact_mod_cast hc
  have hexp : ∑ y, (fR A y + K) * (fR A (x - y) + K) =
      ∑ y, fR A y * fR A (x - y) + (Q : ℝ) * K ^ 2 := by
    have hpt : ∀ y, (fR A y + K) * (fR A (x - y) + K) =
        fR A y * fR A (x - y) + K * fR A y + K * fR A (x - y) + K ^ 2 := fun y => by ring
    simp only [hpt, Finset.sum_add_distrib, ← Finset.mul_sum, hrefl, sum_fR A h0]
    simp [Finset.sum_const, Finset.card_univ, ZMod.card]
  rw [hexp, add_div, hconv, mul_div_cancel_left₀ _ Q_pos.ne']

private lemma sum_fR_sq (A : Finset (ZMod Q)) (hA : Sym A) :
    (∑ x : ZMod Q, fR A x ^ 2) / (Q : ℝ) = (A.card : ℝ) := by
  have h1 : ∀ x : ZMod Q, fR A x ^ 2 = ‖gB A x‖ ^ 2 := fun x => by
    rw [gB_eq_fR A hA, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [h1]
  exact N2sq_gB A

private lemma sum_fR_cube (A : Finset (ZMod Q)) (hA : Sym A) :
    (∑ x : ZMod Q, fR A x ^ 3) / (Q : ℝ) =
      (((A ×ˢ A).filter (fun p => p.1 - p.2 ∈ A)).card : ℝ) := by
  have hC : (∑ x : ZMod Q, gB A x ^ 3) / (Q : ℂ) =
      ((((A ×ˢ A).filter (fun p => p.1 - p.2 ∈ A)).card : ℕ) : ℂ) := by
    have hcube : ∀ x : ZMod Q, gB A x ^ 3 = ∑ a ∈ A, ∑ b ∈ A, ∑ c ∈ A, e ((a + b + c) * x) := by
      intro x
      unfold gB
      rw [pow_succ, pow_two, Finset.sum_mul_sum]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun c _ => ?_
      rw [← e_add, ← e_add]
      congr 1
      ring
    simp_rw [hcube]
    rw [Finset.sum_comm]
    have hswap1 : ∀ a ∈ A, ∑ x : ZMod Q, ∑ b ∈ A, ∑ c ∈ A, e ((a + b + c) * x) =
        ∑ b ∈ A, ∑ c ∈ A, if a + b + c = 0 then (Q : ℂ) else 0 := by
      intro a _
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => e_orth (a + b + c)
    rw [Finset.sum_congr rfl hswap1]
    have hinner : ∀ a ∈ A, ∀ b ∈ A,
        (∑ c ∈ A, if a + b + c = 0 then (Q : ℂ) else 0) =
          if a + b ∈ A then (Q : ℂ) else 0 := by
      intro a _ b _
      have heq : ∀ c : ZMod Q, (a + b + c = 0) ↔ c = -(a + b) := fun c => by
        constructor <;> intro h <;> [exact eq_neg_of_add_eq_zero_right h; rw [h, add_neg_cancel]]
      simp_rw [heq, Finset.sum_ite_eq']
      by_cases hab : a + b ∈ A
      · rw [if_pos (hA _ hab), if_pos hab]
      · have hnab : -(a + b) ∉ A := fun hm => hab (by simpa using hA _ hm)
        rw [if_neg hnab, if_neg hab]
    have hsum2 : ∑ a ∈ A, ∑ b ∈ A, (∑ c ∈ A, if a + b + c = 0 then (Q : ℂ) else 0) =
        ∑ a ∈ A, ∑ b ∈ A, if a - b ∈ A then (Q : ℂ) else 0 := by
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.sum_congr rfl (fun b hb => hinner a ha b hb)]
      refine Finset.sum_nbij' (fun b => -b) (fun b => -b) (fun b hb => hA b hb)
        (fun b hb => hA b hb) (fun b _ => neg_neg b) (fun b _ => neg_neg b) (fun b _ => ?_)
      simp [sub_eq_add_neg]
    rw [hsum2, ← Finset.sum_product']
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      mul_div_cancel_right₀ _ Q_ne_zero_C]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast, Complex.ofReal_natCast]
  simpa [gB_eq_fR A hA] using hC

/-- Roth's additive-triple lower bound on `ZMod Q` (Bedert Lemma 4.1). -/
private lemma roth_triples (A : Finset (ZMod Q)) (hA : Sym A) (h0 : (0 : ZMod Q) ∉ A)
    (K : ℝ) (hKpos : 0 < K) (hK : ∀ x, 0 ≤ fR A x + K) (hbig : 2 * K ^ 2 ≤ (A.card : ℝ)) :
    (A.card : ℝ) ^ 2 / (2 * K) ≤ (((A ×ˢ A).filter (fun p => p.1 - p.2 ∈ A)).card : ℝ) := by
  set T : ℝ := (((A ×ˢ A).filter (fun p => p.1 - p.2 ∈ A)).card : ℝ)
  have h1 : (∑ x : ZMod Q, fR A x * (fR A x + K)) / (Q : ℝ) = (A.card : ℝ) := by
    have he : ∑ x : ZMod Q, fR A x * (fR A x + K) =
        ∑ x : ZMod Q, fR A x ^ 2 + K * ∑ x : ZMod Q, fR A x := by
      simp_rw [mul_add, ← sq, Finset.sum_add_distrib, mul_comm _ K, ← Finset.mul_sum]
    rw [he, sum_fR A h0, mul_zero, add_zero, sum_fR_sq A hA]
  have h2 : (∑ x : ZMod Q, (fR A x + K)) / (Q : ℝ) = K := by
    rw [Finset.sum_add_distrib, sum_fR A h0, zero_add, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul, mul_div_cancel_left₀ _ Q_pos.ne']
  have h3 : (∑ x : ZMod Q, fR A x ^ 2 * (fR A x + K)) / (Q : ℝ) = T + K * (A.card : ℝ) := by
    have he : ∑ x : ZMod Q, fR A x ^ 2 * (fR A x + K) =
        ∑ x : ZMod Q, fR A x ^ 3 + K * ∑ x : ZMod Q, fR A x ^ 2 := by
      have hpt : ∀ x : ZMod Q, fR A x ^ 2 * (fR A x + K) = fR A x ^ 3 + K * fR A x ^ 2 :=
        fun x => by ring
      simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [he, add_div, sum_fR_cube A hA, mul_div_assoc, sum_fR_sq A hA]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (ZMod Q))
    (fun x => Real.sqrt (fR A x + K)) (fun x => fR A x * Real.sqrt (fR A x + K))
  have eL : ∑ x : ZMod Q, Real.sqrt (fR A x + K) * (fR A x * Real.sqrt (fR A x + K)) =
      ∑ x : ZMod Q, fR A x * (fR A x + K) :=
    Finset.sum_congr rfl fun x _ => by
      linear_combination fR A x * Real.mul_self_sqrt (hK x)
  have eR1 : ∑ x : ZMod Q, Real.sqrt (fR A x + K) ^ 2 = ∑ x : ZMod Q, (fR A x + K) :=
    Finset.sum_congr rfl fun x _ => Real.sq_sqrt (hK x)
  have eR2 : ∑ x : ZMod Q, (fR A x * Real.sqrt (fR A x + K)) ^ 2 =
      ∑ x : ZMod Q, fR A x ^ 2 * (fR A x + K) :=
    Finset.sum_congr rfl fun x _ => by rw [mul_pow, Real.sq_sqrt (hK x)]
  rw [eL, eR1, eR2] at hcs
  have hdiv : ((∑ x : ZMod Q, fR A x * (fR A x + K)) / (Q : ℝ)) ^ 2 ≤
      ((∑ x : ZMod Q, (fR A x + K)) / (Q : ℝ)) *
      ((∑ x : ZMod Q, fR A x ^ 2 * (fR A x + K)) / (Q : ℝ)) := by
    rw [div_pow, div_mul_div_comm, ← sq]
    exact div_le_div_of_nonneg_right hcs (sq_nonneg _)
  rw [h1, h2, h3] at hdiv
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/- ## Section 3: Bedert Lemma 7.1 (`L²` decomposition of `gB (Bt A t)`) -/

private lemma gB_At_decomp (A : Finset (ZMod Q)) (hA : Sym A) (h0 : (0 : ZMod Q) ∉ A)
    (K : ℝ) (hK1 : 1 ≤ K) (hK : ∀ x, 0 ≤ fR A x + K) (t : ZMod Q) :
    ∃ R1 R2 : ZMod Q → ℂ,
      (∀ x, gB (At A t) x = R1 x + R2 x) ∧
      (∀ x, ‖R1 x‖ ≤ fR A x + K) ∧
      (∀ x, ‖R2 x‖ ≤ 4 * K ^ 2) := by
  let T1 : ZMod Q → ℂ := fun x => (max (fR A x) 0 : ℝ)
  let T2 : ZMod Q → ℂ := fun x => (min (fR A x) 0 : ℝ)
  have hT_add : ∀ x, gB A x = T1 x + T2 x := fun x => by
    rw [gB_eq_fR A hA]
    dsimp [T1, T2]
    rw [← Complex.ofReal_add, max_add_min, add_zero]
  have hT1_le : ∀ x, ‖T1 x‖ ≤ fR A x + K := fun x => by
    dsimp [T1]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith) (hK x)
  have hT1_N1 : N1 T1 ≤ K := by
    unfold N1
    rw [div_le_iff₀ Q_pos]
    calc ∑ x, ‖T1 x‖ ≤ ∑ x, (fR A x + K) := Finset.sum_le_sum fun x _ => hT1_le x
      _ = K * (Q : ℝ) := by
          rw [Finset.sum_add_distrib, sum_fR A h0, zero_add, Finset.sum_const, Finset.card_univ,
            ZMod.card, nsmul_eq_mul]; ring
  have hT2_le : ∀ x, ‖T2 x‖ ≤ K := fun x => by
    dsimp [T2]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    have h1 := hK x
    exact ⟨by linarith [min_le_left (fR A x) 0, le_min (by linarith : -K ≤ fR A x) (by linarith : -K ≤ (0 : ℝ))],
           (min_le_right _ _).trans (by linarith)⟩
  have hT2_N1 : N1 T2 ≤ K := by
    unfold N1
    rw [div_le_iff₀ Q_pos]
    calc ∑ x, ‖T2 x‖ ≤ ∑ _x : ZMod Q, K := Finset.sum_le_sum fun x _ => hT2_le x
      _ = K * (Q : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; ring
  have hAt_conv : ∀ x, gB (At A t) x = conv (gB A) (fun y => e (t * y) * gB A y) x := by
    intro x
    rw [← fourier_inv (gB (At A t)) x, ← fourier_inv (conv (gB A) (fun y => e (t * y) * gB A y)) x]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [fhat_conv, fhat_mul_e, fhat_gB, fhat_gB, fhat_gB]
    unfold At
    by_cases h1 : m ∈ A <;> by_cases h2 : m - t ∈ A <;> simp [h1, h2]
  let et1 : ZMod Q → ℂ := fun y => e (t * y) * T1 y
  let et2 : ZMod Q → ℂ := fun y => e (t * y) * T2 y
  have het1_le : ∀ y, ‖et1 y‖ ≤ fR A y + K := fun y => by
    dsimp [et1]; rw [norm_mul, norm_e, one_mul]; exact hT1_le y
  have het1_N1 : N1 et1 ≤ K := by
    have : N1 et1 = N1 T1 := by
      unfold N1; congr 1; refine Finset.sum_congr rfl fun y _ => by
        dsimp [et1]; rw [norm_mul, norm_e, one_mul]
    rw [this]; exact hT1_N1
  have het2_le : ∀ y, ‖et2 y‖ ≤ K := fun y => by
    dsimp [et2]; rw [norm_mul, norm_e, one_mul]; exact hT2_le y
  have h11 : ∀ x, ‖conv T1 et1 x‖ ≤ (fR A x + K) + (K ^ 2 - K) := fun x => by
    have hdom := conv_dom T1 et1 (fun y => fR A y + K) (fun y => fR A y + K) hT1_le het1_le x
    rw [ww A hA h0 K x] at hdom
    linarith
  have hK2 : 0 ≤ K ^ 2 - K := by nlinarith
  have hsplit : ∀ x, ∃ u v : ℂ, conv T1 et1 x = u + v ∧ ‖u‖ ≤ fR A x + K ∧ ‖v‖ ≤ K ^ 2 - K :=
    fun x => split_norm (conv T1 et1 x) (fR A x + K) (K ^ 2 - K) (hK x) hK2 (h11 x)
  choose U V hUV hU hV using hsplit
  refine ⟨U, fun x => V x + conv T1 et2 x + conv T2 et1 x + conv T2 et2 x, ?_, hU, ?_⟩
  · intro x
    rw [hAt_conv x]
    have hleft : gB A = fun y => T1 y + T2 y := funext hT_add
    have hright : (fun y => e (t * y) * gB A y) = fun y => et1 y + et2 y := by
      ext y; dsimp [et1, et2]; rw [hT_add y, mul_add]
    rw [hright, hleft, conv_add_left, conv_add_right, conv_add_right, hUV x]
    ring
  · intro x
    have hb1 : ‖V x‖ ≤ K ^ 2 := by linarith [hV x]
    have hb2 : ‖conv T1 et2 x‖ ≤ K ^ 2 :=
      (young_inf_left T1 et2 K het2_le x).trans (by nlinarith)
    have hb3 : ‖conv T2 et1 x‖ ≤ K ^ 2 :=
      (young_inf_right T2 et1 K hT2_le x).trans (by nlinarith)
    have hb4 : ‖conv T2 et2 x‖ ≤ K ^ 2 :=
      (young_inf_left T2 et2 K het2_le x).trans (by nlinarith)
    calc ‖V x + conv T1 et2 x + conv T2 et1 x + conv T2 et2 x‖
        ≤ ‖V x + conv T1 et2 x + conv T2 et1 x‖ + ‖conv T2 et2 x‖ := norm_add_le _ _
      _ ≤ ‖V x + conv T1 et2 x‖ + ‖conv T2 et1 x‖ + ‖conv T2 et2 x‖ := by
          linarith [norm_add_le (V x + conv T1 et2 x) (conv T2 et1 x)]
      _ ≤ ‖V x‖ + ‖conv T1 et2 x‖ + ‖conv T2 et1 x‖ + ‖conv T2 et2 x‖ := by
          linarith [norm_add_le (V x) (conv T1 et2 x)]
      _ ≤ 4 * K ^ 2 := by linarith

/-- Bedert Lemma 7.1 on `ZMod Q`: conjugate-symmetric decomposition of `gB (Bt A t)`. -/
private lemma bedert_lemma_7_1 (A : Finset (ZMod Q)) (hA : Sym A) (h0 : (0 : ZMod Q) ∉ A)
    (K : ℝ) (hK1 : 1 ≤ K) (hK : ∀ x, 0 ≤ fR A x + K) (t : ZMod Q) :
    ∃ Q1 Q2 : ZMod Q → ℂ,
      (∀ x, gB (Bt A t) x = Q1 x + Q2 x) ∧
      (∀ x, Q1 (-x) = (starRingEnd ℂ) (Q1 x)) ∧
      (∀ x, ‖Q1 x‖ ≤ 4 * (fR A x + K)) ∧
      N2 Q2 ≤ 14 * K ^ 2 := by
  let T1 : ZMod Q → ℂ := fun x => (max (fR A x) 0 : ℝ)
  let T2 : ZMod Q → ℂ := fun x => (min (fR A x) 0 : ℝ)
  have hT_add : ∀ x, gB A x = T1 x + T2 x := fun x => by
    rw [gB_eq_fR A hA]; dsimp [T1, T2]; rw [← Complex.ofReal_add, max_add_min, add_zero]
  have hT1_le : ∀ x, ‖T1 x‖ ≤ fR A x + K := fun x => by
    dsimp [T1]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith) (hK x)
  have hT1_N1 : N1 T1 ≤ K := by
    unfold N1; rw [div_le_iff₀ Q_pos]
    calc ∑ x, ‖T1 x‖ ≤ ∑ x, (fR A x + K) := Finset.sum_le_sum fun x _ => hT1_le x
      _ = K * (Q : ℝ) := by
          rw [Finset.sum_add_distrib, sum_fR A h0, zero_add, Finset.sum_const, Finset.card_univ,
            ZMod.card, nsmul_eq_mul]; ring
  have hT2_le : ∀ x, ‖T2 x‖ ≤ K := fun x => by
    dsimp [T2]; rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    have h1 := hK x
    exact ⟨by linarith [le_min (by linarith : -K ≤ fR A x) (by linarith : -K ≤ (0 : ℝ))],
           (min_le_right _ _).trans (by linarith)⟩
  have hK2 : 0 ≤ K ^ 2 - K := by nlinarith
  -- Step 1: decompositions of `At A t` and `At A (-t)`
  obtain ⟨R1', R2', hR'_eq, hR1'_le, hR2'_le⟩ := gB_At_decomp A hA h0 K hK1 hK t
  obtain ⟨R1'', R2'', hR''_eq, hR1''_le, hR2''_le⟩ := gB_At_decomp A hA h0 K hK1 hK (-t)
  -- Step 2: decomposition of triple intersection `At A t ∩ At A (-t)`
  let A3 : Finset (ZMod Q) := At A t ∩ At A (-t)
  let emt1 : ZMod Q → ℂ := fun y => e ((-t) * y) * T1 y
  let emt2 : ZMod Q → ℂ := fun y => e ((-t) * y) * T2 y
  have hemt1_le : ∀ y, ‖emt1 y‖ ≤ fR A y + K := fun y => by
    dsimp [emt1]; rw [norm_mul, norm_e, one_mul]; exact hT1_le y
  have hemt2_le : ∀ y, ‖emt2 y‖ ≤ K := fun y => by
    dsimp [emt2]; rw [norm_mul, norm_e, one_mul]; exact hT2_le y
  have hR1'_N1 : N1 R1' ≤ K := by
    unfold N1; rw [div_le_iff₀ Q_pos]
    calc ∑ x, ‖R1' x‖ ≤ ∑ x, (fR A x + K) := Finset.sum_le_sum fun x _ => hR1'_le x
      _ = K * (Q : ℝ) := by
          rw [Finset.sum_add_distrib, sum_fR A h0, zero_add, Finset.sum_const, Finset.card_univ,
            ZMod.card, nsmul_eq_mul]; ring
  have hA3_conv : ∀ x, gB A3 x = conv (gB (At A t)) (gB (A.image (fun a => a - t))) x := by
    intro x
    rw [conv_gB]
    congr 1
    ext m
    simp only [A3, At, Finset.mem_inter, Finset.mem_filter, Finset.mem_image, sub_neg_eq_add]
    constructor
    · rintro ⟨⟨hm, hmt⟩, ⟨_, hmpt⟩⟩
      exact ⟨⟨hm, hmt⟩, m + t, hmpt, by ring⟩
    · rintro ⟨⟨hm, hmt⟩, a, ha, rfl⟩
      exact ⟨⟨hm, hmt⟩, hm, by simpa using ha⟩
  have hgB_shift : ∀ y, gB (A.image (fun a => a - t)) y = e ((-t) * y) * gB A y := by
    intro y
    unfold gB
    rw [Finset.sum_image (fun a _ b _ h => sub_left_injective h), Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← e_add]
    congr 1
    ring
  have hR1'emt1 : ∀ x, ‖conv R1' emt1 x‖ ≤ (fR A x + K) + (K ^ 2 - K) := fun x => by
    have hdom := conv_dom R1' emt1 (fun y => fR A y + K) (fun y => fR A y + K) hR1'_le hemt1_le x
    rw [ww A hA h0 K x] at hdom
    linarith
  have hsplit3 : ∀ x, ∃ u v : ℂ, conv R1' emt1 x = u + v ∧ ‖u‖ ≤ fR A x + K ∧ ‖v‖ ≤ K ^ 2 - K :=
    fun x => split_norm (conv R1' emt1 x) (fR A x + K) (K ^ 2 - K) (hK x) hK2 (hR1'emt1 x)
  choose R1''' V3 hV3_eq hR1'''_le hV3_le using hsplit3
  let R2''' : ZMod Q → ℂ := fun x =>
    V3 x + conv R1' emt2 x + conv R2' (gB (A.image (fun a => a - t))) x
  have hA3_eq : ∀ x, gB A3 x = R1''' x + R2''' x := by
    intro x
    rw [hA3_conv x]
    have hL : gB (At A t) = fun y => R1' y + R2' y := funext hR'_eq
    have hR : gB (A.image (fun a => a - t)) = fun y => emt1 y + emt2 y := by
      ext y; rw [hgB_shift y, hT_add y, mul_add]
    rw [hL, conv_add_left, hR, conv_add_right, ← hR, hV3_eq x]
    dsimp [R2''']
    ring
  have hN2_V3 : N2 V3 ≤ K ^ 2 :=
    N2_le_of_bdd V3 (K ^ 2) (by positivity) fun x => by linarith [hV3_le x]
  have hN2_R1'emt2 : N2 (conv R1' emt2) ≤ K ^ 2 :=
    N2_le_of_bdd _ (K ^ 2) (by positivity) fun x =>
      (young_inf_left R1' emt2 K hemt2_le x).trans (by nlinarith)
  have hN2_R2' : N2 (conv R2' (gB (A.image (fun a => a - t)))) ≤ 4 * K ^ 2 :=
    (N2_conv_gB_le R2' _).trans (N2_le_of_bdd R2' (4 * K ^ 2) (by positivity) hR2'_le)
  have hN2_R2''' : N2 R2''' ≤ 6 * K ^ 2 := by
    have h1 := N2_add_le (fun x => V3 x + conv R1' emt2 x) (conv R2' (gB (A.image (fun a => a - t))))
    have h2 := N2_add_le V3 (conv R1' emt2)
    change N2 (fun x => V3 x + conv R1' emt2 x + conv R2' (gB (A.image (fun a => a - t))) x) ≤ 6 * K ^ 2
    linarith
  -- Combine for `gB (Bt A t) + gB (Bt A (-t))`
  let R1 : ZMod Q → ℂ := fun x => R1' x + R1'' x - 2 * R1''' x
  let R2 : ZMod Q → ℂ := fun x => R2' x + R2'' x - 2 * R2''' x
  have hsym_plus : ∀ x, gB (Bt A t) x + gB (Bt A (-t)) x = R1 x + R2 x := by
    intro x
    have hid : gB (Bt A t) x + gB (Bt A (-t)) x =
        gB (At A t) x + gB (At A (-t)) x - 2 * gB A3 x := by
      rw [← fourier_inv (fun y => gB (Bt A t) y + gB (Bt A (-t)) y) x,
          ← fourier_inv (fun y => gB (At A t) y + gB (At A (-t)) y - 2 * gB A3 y) x]
      refine Finset.sum_congr rfl fun m _ => ?_
      congr 1
      rw [fhat_add, fhat_sub, fhat_add, fhat_const_mul, fhat_gB, fhat_gB, fhat_gB, fhat_gB, fhat_gB]
      unfold A3 At Bt
      by_cases hm : m ∈ A <;> by_cases hm1 : m - t ∈ A <;> by_cases hm2 : m + t ∈ A <;>
        simp [hm, hm1, hm2, sub_neg_eq_add, ← sub_eq_add_neg] <;> try ring
    rw [hid, hR'_eq x, hR''_eq x, hA3_eq x]
    dsimp [R1, R2]
    ring
  have hR1_le : ∀ x, ‖R1 x‖ ≤ 4 * (fR A x + K) := fun x => by
    dsimp [R1]
    calc ‖R1' x + R1'' x - 2 * R1''' x‖
        ≤ ‖R1' x + R1'' x‖ + ‖2 * R1''' x‖ := norm_sub_le _ _
      _ ≤ ‖R1' x‖ + ‖R1'' x‖ + ‖(2 : ℂ)‖ * ‖R1''' x‖ := by
          rw [norm_mul]; linarith [norm_add_le (R1' x) (R1'' x)]
      _ ≤ 4 * (fR A x + K) := by
          have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
          rw [h2n]; linarith [hR1'_le x, hR1''_le x, hR1'''_le x]
  have hN2_R2 : N2 R2 ≤ 20 * K ^ 2 := by
    have h1 := N2_sub_le (fun x => R2' x + R2'' x) (fun x => 2 * R2''' x)
    have h2 := N2_add_le R2' R2''
    have h3 : N2 (fun x => 2 * R2''' x) = 2 * N2 R2''' := by
      rw [N2_const_mul]; norm_num
    have hb1 : N2 R2' ≤ 4 * K ^ 2 := N2_le_of_bdd R2' (4 * K ^ 2) (by positivity) hR2'_le
    have hb2 : N2 R2'' ≤ 4 * K ^ 2 := N2_le_of_bdd R2'' (4 * K ^ 2) (by positivity) hR2''_le
    change N2 (fun x => R2' x + R2'' x - 2 * R2''' x) ≤ 20 * K ^ 2
    linarith
  -- Step 3: decomposition of `gB (Bt A t) - gB (Bt A (-t))`
  let S1' : ZMod Q → ℂ := fun y => (e (t * y) - e (-(t * y))) * T1 y
  let S2' : ZMod Q → ℂ := fun y => (e (t * y) - e (-(t * y))) * T2 y
  have hed_le : ∀ y, ‖e (t * y) - e (-(t * y))‖ ≤ 2 := fun y =>
    (norm_sub_le _ _).trans (by rw [norm_e, norm_e]; norm_num)
  have hS1'_le : ∀ y, ‖S1' y‖ ≤ 2 * (fR A y + K) := fun y => by
    dsimp [S1']; rw [norm_mul]
    exact mul_le_mul (hed_le y) (hT1_le y) (norm_nonneg _) (by norm_num)
  have hS1'_N1 : N1 S1' ≤ 2 * K := by
    unfold N1; rw [div_le_iff₀ Q_pos]
    calc ∑ y, ‖S1' y‖ ≤ ∑ y, 2 * (fR A y + K) := Finset.sum_le_sum fun y _ => hS1'_le y
      _ = 2 * K * (Q : ℝ) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, sum_fR A h0, zero_add,
            Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; ring
  have hS2'_le : ∀ y, ‖S2' y‖ ≤ 2 * K := fun y => by
    dsimp [S2']; rw [norm_mul]
    exact mul_le_mul (hed_le y) (hT2_le y) (norm_nonneg _) (by norm_num)
  have hdiff_conv : ∀ x, gB (Bt A t) x - gB (Bt A (-t)) x =
      conv (gB A) (fun y => (e (t * y) - e (-(t * y))) * gB A y) x := by
    intro x
    rw [← fourier_inv (fun y => gB (Bt A t) y - gB (Bt A (-t)) y) x,
        ← fourier_inv (conv (gB A) (fun y => (e (t * y) - e (-(t * y))) * gB A y)) x]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hsub_e : (fun y => (e (t * y) - e (-(t * y))) * gB A y) =
        (fun y => e (t * y) * gB A y - e ((-t) * y) * gB A y) := by
      ext y; rw [sub_mul, neg_mul]
    rw [fhat_sub, fhat_conv, hsub_e, fhat_sub, fhat_mul_e, fhat_mul_e, fhat_gB, fhat_gB, fhat_gB, fhat_gB, fhat_gB]
    unfold Bt
    by_cases hm : m ∈ A <;> by_cases hm1 : m - t ∈ A <;> by_cases hm2 : m + t ∈ A <;>
      simp [hm, hm1, hm2, sub_neg_eq_add, ← sub_eq_add_neg]
  have hT1S1' : ∀ x, ‖conv T1 S1' x‖ ≤ 2 * (fR A x + K) + 2 * (K ^ 2 - K) := fun x => by
    have hdom := conv_dom T1 S1' (fun y => fR A y + K) (fun y => 2 * (fR A y + K)) hT1_le hS1'_le x
    have hsum : (∑ y, (fR A y + K) * (2 * (fR A (x - y) + K))) / (Q : ℝ) =
        2 * ((∑ y, (fR A y + K) * (fR A (x - y) + K)) / (Q : ℝ)) := by
      have hpt : ∀ y, (fR A y + K) * (2 * (fR A (x - y) + K)) =
          2 * ((fR A y + K) * (fR A (x - y) + K)) := fun y => by ring
      simp_rw [hpt, ← Finset.mul_sum, mul_div_assoc]
    rw [hsum, ww A hA h0 K x] at hdom
    linarith
  have hsplitS : ∀ x, ∃ u v : ℂ, conv T1 S1' x = u + v ∧
      ‖u‖ ≤ 2 * (fR A x + K) ∧ ‖v‖ ≤ 2 * (K ^ 2 - K) :=
    fun x => split_norm (conv T1 S1' x) (2 * (fR A x + K)) (2 * (K ^ 2 - K))
      (by linarith [hK x]) (by linarith) (hT1S1' x)
  choose S1 VS hVS_eq hS1_le hVS_le using hsplitS
  let S2 : ZMod Q → ℂ := fun x => VS x + conv T1 S2' x + conv T2 S1' x + conv T2 S2' x
  have hsym_minus : ∀ x, gB (Bt A t) x - gB (Bt A (-t)) x = S1 x + S2 x := by
    intro x
    rw [hdiff_conv x]
    have hL : gB A = fun y => T1 y + T2 y := funext hT_add
    have hR : (fun y => (e (t * y) - e (-(t * y))) * gB A y) = fun y => S1' y + S2' y := by
      ext y; dsimp [S1', S2']; rw [hT_add y, mul_add]
    rw [hR, hL, conv_add_left, conv_add_right, conv_add_right, hVS_eq x]
    dsimp [S2]
    ring
  have hS2_le : ∀ x, ‖S2 x‖ ≤ 8 * K ^ 2 := fun x => by
    have hb1 : ‖VS x‖ ≤ 2 * K ^ 2 := by linarith [hVS_le x]
    have hb2 : ‖conv T1 S2' x‖ ≤ 2 * K ^ 2 :=
      (young_inf_left T1 S2' (2 * K) hS2'_le x).trans (by nlinarith)
    have hb3 : ‖conv T2 S1' x‖ ≤ 2 * K ^ 2 :=
      (young_inf_right T2 S1' K hT2_le x).trans (by nlinarith)
    have hb4 : ‖conv T2 S2' x‖ ≤ 2 * K ^ 2 :=
      (young_inf_left T2 S2' (2 * K) hS2'_le x).trans (by
        have hT2_N1 : N1 T2 ≤ K := by
          unfold N1; rw [div_le_iff₀ Q_pos]
          calc ∑ y, ‖T2 y‖ ≤ ∑ _y : ZMod Q, K := Finset.sum_le_sum fun y _ => hT2_le y
            _ = K * (Q : ℝ) := by
                rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; ring
        nlinarith)
    dsimp [S2]
    calc ‖VS x + conv T1 S2' x + conv T2 S1' x + conv T2 S2' x‖
        ≤ ‖VS x + conv T1 S2' x + conv T2 S1' x‖ + ‖conv T2 S2' x‖ := norm_add_le _ _
      _ ≤ ‖VS x + conv T1 S2' x‖ + ‖conv T2 S1' x‖ + ‖conv T2 S2' x‖ := by
          linarith [norm_add_le (VS x + conv T1 S2' x) (conv T2 S1' x)]
      _ ≤ ‖VS x‖ + ‖conv T1 S2' x‖ + ‖conv T2 S1' x‖ + ‖conv T2 S2' x‖ := by
          linarith [norm_add_le (VS x) (conv T1 S2' x)]
      _ ≤ 8 * K ^ 2 := by linarith
  have hN2_S2 : N2 S2 ≤ 8 * K ^ 2 := N2_le_of_bdd S2 (8 * K ^ 2) (by positivity) hS2_le
  -- Step 4: average and conjugate-symmetrize
  let P1 : ZMod Q → ℂ := fun x => ((1 / 2 : ℝ) : ℂ) * (R1 x + S1 x)
  let P2 : ZMod Q → ℂ := fun x => ((1 / 2 : ℝ) : ℂ) * (R2 x + S2 x)
  have hP_eq : ∀ x, gB (Bt A t) x = P1 x + P2 x := fun x => by
    have hp := hsym_plus x
    have hm := hsym_minus x
    dsimp [P1, P2]
    push_cast
    linear_combination (hp + hm) / 2
  have hP1_le : ∀ x, ‖P1 x‖ ≤ 4 * (fR A x + K) := fun x => by
    dsimp [P1]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have htri := norm_add_le (R1 x) (S1 x)
    linarith [hR1_le x, hS1_le x, hK x]
  have hN2_P2 : N2 P2 ≤ 14 * K ^ 2 := by
    have hc := N2_const_mul ((1 / 2 : ℝ) : ℂ) (fun x => R2 x + S2 x)
    have hhalf : ‖((1 / 2 : ℝ) : ℂ)‖ = 1 / 2 := by norm_num
    have hadd := N2_add_le R2 S2
    change N2 (fun x => ((1 / 2 : ℝ) : ℂ) * (R2 x + S2 x)) ≤ 14 * K ^ 2
    rw [hc, hhalf]
    linarith
  let Q1 : ZMod Q → ℂ := fun x => ((1 / 2 : ℝ) : ℂ) * (P1 x + (starRingEnd ℂ) (P1 (-x)))
  let Q2 : ZMod Q → ℂ := fun x => ((1 / 2 : ℝ) : ℂ) * (P2 x + (starRingEnd ℂ) (P2 (-x)))
  have hgB_conj_neg : ∀ x, (starRingEnd ℂ) (gB (Bt A t) (-x)) = gB (Bt A t) x := fun x => by
    unfold gB
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← e_neg]
    congr 1
    ring
  refine ⟨Q1, Q2, ?_, ?_, ?_, ?_⟩
  · intro x
    have h1 := hP_eq x
    have h2 : gB (Bt A t) x = (starRingEnd ℂ) (P1 (-x)) + (starRingEnd ℂ) (P2 (-x)) := by
      rw [← hgB_conj_neg x, hP_eq (-x), map_add]
    dsimp [Q1, Q2]
    push_cast
    linear_combination (h1 + h2) / 2
  · intro x
    have haux : ∀ z w : ℂ, ((1 / 2 : ℝ) : ℂ) * (w + (starRingEnd ℂ) z) =
        (starRingEnd ℂ) (((1 / 2 : ℝ) : ℂ) * (z + (starRingEnd ℂ) w)) := fun z w => by
      rw [map_mul, Complex.conj_ofReal, map_add, starRingEnd_self_apply, add_comm]
    simpa [Q1, neg_neg] using haux (P1 x) (P1 (-x))
  · intro x
    dsimp [Q1]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have htri := norm_add_le (P1 x) ((starRingEnd ℂ) (P1 (-x)))
    rw [Complex.norm_conj] at htri
    have h2 := hP1_le (-x)
    rw [fR_neg A hA x] at h2
    linarith [hP1_le x]
  · have hc := N2_const_mul ((1 / 2 : ℝ) : ℂ) (fun x => P2 x + (starRingEnd ℂ) (P2 (-x)))
    have hhalf : ‖((1 / 2 : ℝ) : ℂ)‖ = 1 / 2 := by norm_num
    have hadd := N2_add_le P2 (fun x => (starRingEnd ℂ) (P2 (-x)))
    rw [N2_conj_neg] at hadd
    change N2 (fun x => ((1 / 2 : ℝ) : ℂ) * (P2 x + (starRingEnd ℂ) (P2 (-x)))) ≤ 14 * K ^ 2
    rw [hc, hhalf]
    linarith

/- ## Section 4: Bedert Lemma 7.2 (32-case Fourier coefficient bounds) -/

/-- Complex weight `w = (1 + i) / (2√2) = (√2 / 4) (1 + i)`. -/
private noncomputable def wConst : ℂ :=
  ((Real.sqrt 2 / 4 : ℝ) : ℂ) * (1 + Complex.I)

private lemma norm_wConst : ‖wConst‖ = 1 / 2 := by
  have hsq : ‖wConst‖ ^ 2 = (1 / 2 : ℝ) ^ 2 := by
    unfold wConst
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have h1I : ‖(1 : ℂ) + Complex.I‖ ^ 2 = 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      norm_num
    rw [h1I]
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith
  nlinarith [norm_nonneg wConst]

/-- Boolean formula for `ρ_m = f̂_t(m)² - w f̂_t(m - t)² - w̄ f̂_t(m + t)²`. -/
private noncomputable def rhoBit (b0 b1 b2 b3 b4 : Bool) : ℂ :=
  let f (x y z : Bool) : ℂ :=
    2 * (if y then (1 : ℂ) else 0) - Complex.I * (if x then 1 else 0) +
      Complex.I * (if z then 1 else 0)
  f b1 b2 b3 ^ 2 - wConst * f b0 b1 b2 ^ 2 - (starRingEnd ℂ) wConst * f b2 b3 b4 ^ 2

private lemma rhoBit_bounds (b0 b1 b2 b3 b4 : Bool) :
    (rhoBit b0 b1 b2 b3 b4).re ≤ 4 + Real.sqrt 2 / 2 ∧
    |(rhoBit b0 b1 b2 b3 b4).im| ≤ 4 + 2 * Real.sqrt 2 ∧
    (b1 = true → b2 = true → b3 = false → 4 + Real.sqrt 2 ≤ -(rhoBit b0 b1 b2 b3 b4).im) := by
  have hs : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
  · simp only [rhoBit, wConst, Bool.false_eq_true, ↓reduceIte, map_mul, map_add, map_one,
      Complex.conj_I, Complex.conj_ofReal, Complex.sub_re, Complex.add_re, Complex.mul_re,
      Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im,
      sq, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul,
      neg_neg, neg_mul, mul_neg, Complex.neg_re, Complex.neg_im, Complex.re_ofNat, Complex.im_ofNat]
    refine ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩, fun h1 h2 h3 => by
      try cases h1
      try cases h2
      try cases h3
      try linarith⟩

/- ## Section 5: Bedert Proposition 7.3 (`|Bt A t| ≤ 500000 K⁴`) -/

private lemma prop_7_3 (A : Finset (ZMod Q)) (hA : Sym A) (h0 : (0 : ZMod Q) ∉ A)
    (K : ℝ) (hK1 : 1 ≤ K) (hK : ∀ x, 0 ≤ fR A x + K) (t : ZMod Q) :
    ((Bt A t).card : ℝ) ≤ 500000 * K ^ 4 := by
  set B := Bt A t
  -- Auxiliary functions `f_t`, `M_t`, `r_t`, `ψ_t`, `φ_t`
  let ft : ZMod Q → ℝ := fun x => 2 * (1 + (e (t * x)).im) * fR A x
  let ftC : ZMod Q → ℂ := fun x => (ft x : ℂ)
  have hft_eq : ∀ x, ftC x = (2 - Complex.I * e (t * x) + Complex.I * e (-(t * x))) * gB A x := by
    intro x
    have htr : ((2 * (1 + (e (t * x)).im) : ℝ) : ℂ) =
        2 - Complex.I * e (t * x) + Complex.I * e (-(t * x)) := by
      rw [e_neg]
      apply Complex.ext <;> (simp; try ring)
    change ((2 * (1 + (e (t * x)).im) * fR A x : ℝ) : ℂ) = _
    rw [Complex.ofReal_mul, htr, gB_eq_fR A hA]
  have hft_ge : ∀ x, 0 ≤ ft x + 4 * K := fun x => by
    have him : |(e (t * x)).im| ≤ 1 := by
      calc |(e (t * x)).im| ≤ ‖e (t * x)‖ := Complex.abs_im_le_norm _
        _ = 1 := norm_e _
    have h1 : 0 ≤ 1 + (e (t * x)).im := by linarith [(abs_le.mp him).1]
    have h2 : 1 + (e (t * x)).im ≤ 2 := by linarith [(abs_le.mp him).2]
    have h3 : -K ≤ fR A x := by linarith [hK x]
    dsimp [ft]
    nlinarith
  have hfhat_ft : ∀ m : ZMod Q, fhat ftC m =
      2 * (if m ∈ A then (1 : ℂ) else 0) -
      Complex.I * (if m - t ∈ A then 1 else 0) +
      Complex.I * (if m + t ∈ A then 1 else 0) := by
    intro m
    have hfun : ftC = fun x =>
        2 * gB A x - Complex.I * (e (t * x) * gB A x) + Complex.I * (e ((-t) * x) * gB A x) := by
      ext x; rw [hft_eq x, neg_mul]; ring
    rw [hfun, fhat_add, fhat_sub, fhat_const_mul, fhat_const_mul, fhat_const_mul,
      fhat_mul_e, fhat_mul_e, fhat_gB, fhat_gB, fhat_gB, sub_neg_eq_add]
  have hsum_ft : ∑ x : ZMod Q, ft x = 0 := by
    have h0' : fhat ftC 0 = 0 := by
      rw [hfhat_ft 0, if_neg h0]
      simp only [zero_sub, zero_add]
      by_cases ht : t ∈ A
      · rw [if_pos (hA t ht), if_pos ht]; ring
      · have hnt : -t ∉ A := fun hm => ht (by simpa using hA (-t) hm)
        rw [if_neg hnt, if_neg ht]; ring
    unfold fhat at h0'
    simp only [zero_mul, neg_zero, e_zero, mul_one] at h0'
    have hsumC : ∑ x : ZMod Q, ftC x = 0 :=
      (div_eq_iff Q_ne_zero_C).mp h0' |>.trans (zero_mul _)
    have := congrArg Complex.re hsumC
    simpa [ftC, Complex.re_sum] using this
  have hconv_ft_real : ∀ x, conv ftC ftC x = (((∑ y, ft y * ft (x - y)) / (Q : ℝ) : ℝ) : ℂ) := by
    intro x
    unfold conv
    rw [Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast]
    congr 1
    refine Finset.sum_congr rfl fun y _ => by simp [ftC]
  have hconv_ft_ge : ∀ x, -16 * K ^ 2 ≤ (conv ftC ftC x).re := fun x => by
    rw [hconv_ft_real x, Complex.ofReal_re]
    have hnn : 0 ≤ (∑ y : ZMod Q, (ft y + 4 * K) * (ft (x - y) + 4 * K)) / (Q : ℝ) :=
      div_nonneg (Finset.sum_nonneg fun y _ => mul_nonneg (hft_ge y) (hft_ge (x - y))) Q_pos.le
    have hrefl : ∑ y : ZMod Q, ft (x - y) = 0 :=
      (Equiv.sum_comp (Equiv.subLeft x) ft).trans hsum_ft
    have hexp : (∑ y : ZMod Q, (ft y + 4 * K) * (ft (x - y) + 4 * K)) / (Q : ℝ) =
        (∑ y : ZMod Q, ft y * ft (x - y)) / (Q : ℝ) + 16 * K ^ 2 := by
      have hpt : ∀ y, (ft y + 4 * K) * (ft (x - y) + 4 * K) =
          ft y * ft (x - y) + 4 * K * ft y + 4 * K * ft (x - y) + 16 * K ^ 2 := fun y => by ring
      simp only [hpt, Finset.sum_add_distrib, ← Finset.mul_sum, hsum_ft, hrefl, mul_zero, add_zero,
        Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      rw [add_div]
      congr 1
      field_simp [Q_pos.ne']
    linarith
  -- Weight `Mt x = 1 - 2 * Re(wConst * e(t * x))`
  let Mt : ZMod Q → ℝ := fun x => 1 - 2 * (wConst * e (t * x)).re
  have hMt_bounds : ∀ x, 0 ≤ Mt x ∧ Mt x ≤ 2 := fun x => by
    have hab : |(wConst * e (t * x)).re| ≤ 1 / 2 := by
      calc |(wConst * e (t * x)).re| ≤ ‖wConst * e (t * x)‖ := Complex.abs_re_le_norm _
        _ = 1 / 2 := by rw [norm_mul, norm_wConst, norm_e, mul_one]
    dsimp [Mt]
    constructor <;> linarith [(abs_le.mp hab).1, (abs_le.mp hab).2]
  have hMt_eq : ∀ x, (Mt x : ℂ) = 1 - wConst * e (t * x) - (starRingEnd ℂ) wConst * e (-(t * x)) := by
    intro x
    have hconj : (starRingEnd ℂ) (wConst * e (t * x)) = (starRingEnd ℂ) wConst * e (-(t * x)) := by
      rw [map_mul, e_neg]
    have hre : wConst * e (t * x) + (starRingEnd ℂ) (wConst * e (t * x)) =
        ((2 * (wConst * e (t * x)).re : ℝ) : ℂ) := by
      simpa [Complex.ofReal_mul] using Complex.add_conj (wConst * e (t * x))
    dsimp [Mt]
    rw [Complex.ofReal_sub, Complex.ofReal_one, ← hre, hconj]
    ring
  let rt : ZMod Q → ℝ := fun x => Mt x * (conv ftC ftC x).re
  let rtC : ZMod Q → ℂ := fun x => (rt x : ℂ)
  have hrt_ge : ∀ x, -32 * K ^ 2 ≤ rt x := fun x => by
    dsimp [rt]
    have ⟨hm0, hm2⟩ := hMt_bounds x
    have hc := hconv_ft_ge x
    nlinarith
  have hrtC_eq : ∀ x, rtC x =
      (1 - wConst * e (t * x) - (starRingEnd ℂ) wConst * e (-(t * x))) * conv ftC ftC x := by
    intro x
    change ((Mt x * (conv ftC ftC x).re : ℝ) : ℂ) = _
    rw [Complex.ofReal_mul, hMt_eq x]
    congr 1
    rw [hconv_ft_real x, Complex.ofReal_re]
  have hfhat_rt : ∀ m : ZMod Q, fhat rtC m =
      rhoBit (decide (m - t - t ∈ A)) (decide (m - t ∈ A)) (decide (m ∈ A))
             (decide (m + t ∈ A)) (decide (m + t + t ∈ A)) := by
    intro m
    have hfun : rtC = fun x =>
        conv ftC ftC x - wConst * (e (t * x) * conv ftC ftC x) -
          (starRingEnd ℂ) wConst * (e ((-t) * x) * conv ftC ftC x) := by
      ext x; rw [hrtC_eq x, neg_mul]; ring
    rw [hfun, fhat_sub, fhat_sub, fhat_const_mul, fhat_const_mul,
      fhat_mul_e, fhat_mul_e, fhat_conv, fhat_conv, fhat_conv, sub_neg_eq_add,
      ← sq, ← sq, ← sq, hfhat_ft, hfhat_ft, hfhat_ft]
    have h1 : m - t + t = m := by ring
    have h2 : m + t - t = m := by ring
    rw [h1, h2]
    dsimp [rhoBit]
    simp only [decide_eq_true_eq]
  -- Even and odd parts `ψt` and `φt`
  let ψt : ZMod Q → ℝ := fun x => (rt x + rt (-x)) / 2
  let φt : ZMod Q → ℝ := fun x => (rt x - rt (-x)) / 2
  let ψtC : ZMod Q → ℂ := fun x => (ψt x : ℂ)
  let φtC : ZMod Q → ℂ := fun x => (φt x : ℂ)
  have hφ_le_ψ : ∀ x, |φt x| ≤ ψt x + 32 * K ^ 2 := fun x => by
    dsimp [ψt, φt]
    rw [abs_le]
    constructor <;> linarith [hrt_ge x, hrt_ge (-x)]
  have hfhat_ψ : ∀ m : ZMod Q, fhat ψtC m = ((fhat rtC m).re : ℂ) := fun m => by
    have hfun : ψtC = fun x => ((1 / 2 : ℝ) : ℂ) * (rtC x + rtC (-x)) := by
      ext x; dsimp [ψtC, ψt, rtC]; push_cast; ring
    rw [hfun, fhat_const_mul, fhat_add, fhat_real_neg_arg rt m, Complex.add_conj]
    push_cast; ring
  have hfhat_φ : ∀ m : ZMod Q, fhat φtC m = ((fhat rtC m).im : ℂ) * Complex.I := fun m => by
    have hfun : φtC = fun x => ((1 / 2 : ℝ) : ℂ) * (rtC x - rtC (-x)) := by
      ext x; dsimp [φtC, φt, rtC]; push_cast; ring
    rw [hfun, fhat_const_mul, fhat_sub, fhat_real_neg_arg rt m, Complex.sub_conj]
    push_cast; ring
  have hfhat_φ_neg : ∀ m : ZMod Q, fhat φtC (-m) = -fhat φtC m := fun m => by
    rw [← fhat_neg_arg]
    have hfun : (fun x => φtC (-x)) = (fun x => (-1 : ℂ) * φtC x) := by
      ext x; dsimp [φtC, φt]; push_cast; ring
    rw [hfun, fhat_const_mul]; ring
  have hψ_even_fhat : ∀ m : ZMod Q, fhat ψtC (-m) = fhat ψtC m := fun m => by
    rw [← fhat_neg_arg]
    have hfun : (fun x => ψtC (-x)) = ψtC := by
      ext x; dsimp [ψtC, ψt]; rw [neg_neg, add_comm]
    rw [hfun]
  -- Apply Lemma 7.1
  obtain ⟨Q1, Q2, hQ_eq, hQ1_sym, hQ1_le, hN2_Q2⟩ := bedert_lemma_7_1 A hA h0 K hK1 hK t
  let H : ZMod Q → ℝ := fun x => ‖Q1 x‖
  let HC : ZMod Q → ℂ := fun x => (H x : ℂ)
  have hH_even : ∀ x, H (-x) = H x := fun x => by
    dsimp [H]; rw [hQ1_sym x, Complex.norm_conj]
  have hH_fhat_real : ∀ m : ZMod Q, fhat HC m = ((fhat HC m).re : ℂ) := fun m => by
    have h := fhat_real_neg_arg H m
    have hev : (fun x => (H (-x) : ℂ)) = HC := by ext x; dsimp [HC]; rw [hH_even x]
    rw [hev] at h
    exact (Complex.conj_eq_iff_re.mp h.symm).symm
  have hH_fhat_sq : ∀ m : ZMod Q, fhat HC m ^ 2 = ((‖fhat HC m‖ ^ 2 : ℝ) : ℂ) := fun m => by
    rw [hH_fhat_real m, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hHH_real : ∀ x, conv HC HC x = (((∑ y, H y * H (x - y)) / (Q : ℝ) : ℝ) : ℂ) := fun x => by
    unfold conv
    rw [Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast]
    congr 1
    refine Finset.sum_congr rfl fun y _ => by simp [HC]
  have hHH_nonneg : ∀ x, 0 ≤ (conv HC HC x).re := fun x => by
    rw [hHH_real x, Complex.ofReal_re]
    exact div_nonneg (Finset.sum_nonneg fun y _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) Q_pos.le
  -- Define test quantity `X`
  set X : ℝ := (∑ x : ZMod Q, (ψt x + 32 * K ^ 2) * (conv HC HC x).re) / (Q : ℝ)
  -- Upper bound on `X`
  have hN1_Q1 : N1 Q1 ≤ 4 * K := by
    unfold N1; rw [div_le_iff₀ Q_pos]
    calc ∑ x, ‖Q1 x‖ ≤ ∑ x, 4 * (fR A x + K) := Finset.sum_le_sum fun x _ => hQ1_le x
      _ = 4 * K * (Q : ℝ) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, sum_fR A h0, zero_add,
            Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; ring
  have hN2_Q1 : N2 Q1 ≤ Real.sqrt (B.card : ℝ) + 14 * K ^ 2 := by
    have hfun : Q1 = fun x => gB B x - Q2 x := by ext x; exact eq_sub_of_add_eq (hQ_eq x).symm
    rw [hfun]
    have htri := N2_sub_le (gB B) Q2
    have hgb : N2 (gB B) = Real.sqrt (B.card : ℝ) := by unfold N2; rw [N2sq_gB]
    linarith
  have hX_upper : X ≤ (4 + Real.sqrt 2 / 2) * (Real.sqrt (B.card : ℝ) + 14 * K ^ 2) ^ 2 +
      512 * K ^ 4 := by
    have hsplitX : X = (∑ x, ψt x * (conv HC HC x).re) / (Q : ℝ) +
        32 * K ^ 2 * ((∑ x, (conv HC HC x).re) / (Q : ℝ)) := by
      dsimp [X]
      have hpt : ∀ x, (ψt x + 32 * K ^ 2) * (conv HC HC x).re =
          ψt x * (conv HC HC x).re + 32 * K ^ 2 * (conv HC HC x).re := fun x => by ring
      simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum, add_div, mul_div_assoc]
    have hterm1 : (∑ x, ψt x * (conv HC HC x).re) / (Q : ℝ) ≤
        (4 + Real.sqrt 2 / 2) * N2sq Q1 := by
      have hparseval : ((∑ x, ψt x * (conv HC HC x).re) / (Q : ℝ) : ℝ) =
          ∑ m : ZMod Q, (fhat rtC m).re * ‖fhat HC m‖ ^ 2 := by
        apply Complex.ofReal_injective
        have hL : (((∑ x, ψt x * (conv HC HC x).re) / (Q : ℝ) : ℝ) : ℂ) =
            (∑ x, ψtC x * conv HC HC x) / (Q : ℂ) := by
          rw [Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast]
          congr 1
          refine Finset.sum_congr rfl fun x _ => by
            rw [Complex.ofReal_mul, hHH_real x, Complex.ofReal_re]
        rw [hL, parseval_inner]
        rw [Complex.ofReal_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hψ_even_fhat m, hfhat_ψ m, fhat_conv, ← sq, hH_fhat_sq m, Complex.ofReal_mul]
      rw [hparseval]
      have hbound : ∑ m : ZMod Q, (fhat rtC m).re * ‖fhat HC m‖ ^ 2 ≤
          (4 + Real.sqrt 2 / 2) * ∑ m : ZMod Q, ‖fhat HC m‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun m _ => ?_
        have hre := (rhoBit_bounds (decide (m - t - t ∈ A)) (decide (m - t ∈ A)) (decide (m ∈ A))
          (decide (m + t ∈ A)) (decide (m + t + t ∈ A))).1
        rw [← hfhat_rt m] at hre
        exact mul_le_mul_of_nonneg_right hre (sq_nonneg _)
      have hN2H : ∑ m : ZMod Q, ‖fhat HC m‖ ^ 2 = N2sq Q1 := by
        rw [← parseval_sq HC]
        unfold N2sq
        congr 1
        refine Finset.sum_congr rfl fun x _ => by
          dsimp [HC, H]
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      rw [hN2H] at hbound
      exact hbound
    have hterm2 : (∑ x, (conv HC HC x).re) / (Q : ℝ) = (N1 Q1) ^ 2 := by
      have h1 : ∀ x, (conv HC HC x).re = (∑ y, H y * H (x - y)) / (Q : ℝ) := fun x => by
        rw [hHH_real x, Complex.ofReal_re]
      simp_rw [h1, ← Finset.sum_div, div_div, ← sq]
      rw [Finset.sum_comm]
      have h2 : ∑ y : ZMod Q, ∑ x : ZMod Q, H y * H (x - y) = (∑ y : ZMod Q, H y) ^ 2 := by
        have hinner : ∀ y : ZMod Q, ∑ x : ZMod Q, H y * H (x - y) = H y * ∑ z : ZMod Q, H z := by
          intro y
          rw [← Finset.mul_sum]
          congr 1
          exact Equiv.sum_comp (Equiv.subRight y) H
        simp_rw [hinner, ← Finset.sum_mul, sq]
      rw [h2, ← div_pow]
      rfl
    have hQ1sq : N2sq Q1 ≤ (Real.sqrt (B.card : ℝ) + 14 * K ^ 2) ^ 2 := by
      rw [← N2_sq Q1]
      exact pow_le_pow_left₀ (N2_nonneg Q1) hN2_Q1 2
    have hN1sq : N1 Q1 ^ 2 ≤ 16 * K ^ 2 := by
      have hnn : 0 ≤ N1 Q1 := div_nonneg (Finset.sum_nonneg fun x _ => norm_nonneg _) Q_pos.le
      nlinarith
    have hcoeff_nn : 0 ≤ 4 + Real.sqrt 2 / 2 := by positivity
    rw [hsplitX, hterm2]
    nlinarith [mul_le_mul_of_nonneg_left hQ1sq hcoeff_nn,
      mul_le_mul_of_nonneg_left hN1sq (show (0 : ℝ) ≤ 32 * K ^ 2 by positivity)]
  -- Lower bound on `X`
  let I0 : ℂ := (∑ x, φtC x * gB B x) / (Q : ℂ)
  let I1 : ℂ := (∑ x, φtC x * conv (gB B) Q2 x) / (Q : ℂ)
  let I2 : ℂ := (∑ x, φtC x * conv Q2 Q2 x) / (Q : ℂ)
  have hconv_Q1_expand : ∀ x, conv Q1 Q1 x = gB B x - 2 * conv (gB B) Q2 x + conv Q2 Q2 x := by
    intro x
    have hfun : Q1 = fun y => gB B y - Q2 y := by ext y; exact eq_sub_of_add_eq (hQ_eq y).symm
    rw [hfun, conv_sub_left, conv_sub_right, conv_sub_right, conv_gB, Finset.inter_self,
      conv_comm Q2 (gB B)]
    ring
  have hX_ge_norm : ‖I0 - 2 * I1 + I2‖ ≤ X := by
    have hcomb : I0 - 2 * I1 + I2 = (∑ x, φtC x * conv Q1 Q1 x) / (Q : ℂ) := by
      dsimp [I0, I1, I2]
      simp_rw [hconv_Q1_expand]
      have hpt : ∀ x, φtC x * (gB B x - 2 * conv (gB B) Q2 x + conv Q2 Q2 x) =
          φtC x * gB B x - 2 * (φtC x * conv (gB B) Q2 x) + φtC x * conv Q2 Q2 x :=
        fun x => by ring
      simp_rw [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    rw [hcomb, norm_div, Complex.norm_natCast]
    dsimp [X]
    refine div_le_div_of_nonneg_right ?_ Q_pos.le
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [norm_mul]
    have hφn : ‖φtC x‖ = |φt x| := by dsimp [φtC]; rw [Complex.norm_real, Real.norm_eq_abs]
    have hdom : ‖conv Q1 Q1 x‖ ≤ (conv HC HC x).re := by
      rw [hHH_real x, Complex.ofReal_re]
      exact conv_dom Q1 Q1 H H (fun _ => le_rfl) (fun _ => le_rfl) x
    rw [hφn]
    exact mul_le_mul (hφ_le_ψ x) hdom (norm_nonneg _) (by linarith [hφ_le_ψ x, abs_nonneg (φt x)])
  have hI0_lb : (4 + Real.sqrt 2) * (B.card : ℝ) ≤ ‖I0‖ := by
    have hI0_eq : I0 = ((∑ m ∈ B, -(fhat rtC m).im : ℝ) : ℂ) * Complex.I := by
      dsimp [I0]
      rw [parseval_inner]
      have hterm : ∀ m : ZMod Q, fhat φtC (-m) * fhat (gB B) m =
          if m ∈ B then ((-(fhat rtC m).im : ℝ) : ℂ) * Complex.I else 0 := by
        intro m
        rw [hfhat_φ_neg m, hfhat_φ m, fhat_gB]
        split_ifs <;> simp
      simp_rw [hterm, Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_mul, Complex.ofReal_sum]
    have hterm_lb : ∀ m ∈ B, 4 + Real.sqrt 2 ≤ -(fhat rtC m).im := by
      intro m hm
      have hmem : m ∈ A ∧ m - t ∈ A ∧ m + t ∉ A := by
        simpa [B, Bt] using hm
      have hb := (rhoBit_bounds (decide (m - t - t ∈ A)) (decide (m - t ∈ A)) (decide (m ∈ A))
        (decide (m + t ∈ A)) (decide (m + t + t ∈ A))).2.2
      rw [← hfhat_rt m] at hb
      exact hb (decide_eq_true hmem.2.1) (decide_eq_true hmem.1) (decide_eq_false hmem.2.2)
    have hsum_lb : (4 + Real.sqrt 2) * (B.card : ℝ) ≤ ∑ m ∈ B, -(fhat rtC m).im := by
      calc (4 + Real.sqrt 2) * (B.card : ℝ)
          = ∑ _m ∈ B, (4 + Real.sqrt 2) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ ∑ m ∈ B, -(fhat rtC m).im := Finset.sum_le_sum hterm_lb
    have hsum_nn : 0 ≤ ∑ m ∈ B, -(fhat rtC m).im :=
      le_trans (mul_nonneg (by positivity) (Nat.cast_nonneg _)) hsum_lb
    rw [hI0_eq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hsum_nn]
    exact hsum_lb
  have hfhat_φ_ub : ∀ m : ZMod Q, ‖fhat φtC (-m)‖ ≤ 4 + 2 * Real.sqrt 2 := fun m => by
    rw [hfhat_φ_neg m, norm_neg, hfhat_φ m, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
    have h := (rhoBit_bounds (decide (m - t - t ∈ A)) (decide (m - t ∈ A)) (decide (m ∈ A))
      (decide (m + t ∈ A)) (decide (m + t + t ∈ A))).2.1
    rw [← hfhat_rt m] at h
    exact h
  have hI1_ub : ‖I1‖ ≤ (4 + 2 * Real.sqrt 2) * (14 * K ^ 2) * Real.sqrt (B.card : ℝ) := by
    dsimp [I1]
    rw [parseval_inner]
    have h1 : ‖∑ m, fhat φtC (-m) * fhat (conv (gB B) Q2) m‖ ≤
        (4 + 2 * Real.sqrt 2) * ∑ m ∈ B, ‖fhat Q2 m‖ := by
      have hrew : ∑ m, fhat φtC (-m) * fhat (conv (gB B) Q2) m =
          ∑ m ∈ B, fhat φtC (-m) * fhat Q2 m := by
        have hterm : ∀ m : ZMod Q, fhat φtC (-m) * fhat (conv (gB B) Q2) m =
            if m ∈ B then fhat φtC (-m) * fhat Q2 m else 0 := by
          intro m; rw [fhat_conv, fhat_gB]; split_ifs <;> simp
        simp_rw [hterm, Finset.sum_ite_mem, Finset.univ_inter]
      rw [hrew, Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hfhat_φ_ub m) (norm_nonneg _)
    have hcs : ∑ m ∈ B, ‖fhat Q2 m‖ ≤ Real.sqrt (B.card : ℝ) * N2 Q2 := by
      have hsq : (∑ m ∈ B, ‖fhat Q2 m‖) ^ 2 ≤ (B.card : ℝ) * N2sq Q2 := by
        calc (∑ m ∈ B, ‖fhat Q2 m‖) ^ 2
            = (∑ m ∈ B, (1 : ℝ) * ‖fhat Q2 m‖) ^ 2 := by simp
          _ ≤ (∑ _m ∈ B, (1 : ℝ) ^ 2) * ∑ m ∈ B, ‖fhat Q2 m‖ ^ 2 :=
              Finset.sum_mul_sq_le_sq_mul_sq B _ _
          _ = (B.card : ℝ) * ∑ m ∈ B, ‖fhat Q2 m‖ ^ 2 := by simp
          _ ≤ (B.card : ℝ) * ∑ m : ZMod Q, ‖fhat Q2 m‖ ^ 2 :=
              mul_le_mul_of_nonneg_left
                (Finset.sum_le_univ_sum_of_nonneg fun m => sq_nonneg _) (Nat.cast_nonneg _)
          _ = (B.card : ℝ) * N2sq Q2 := by rw [parseval_sq]
      have hrr : (Real.sqrt (B.card : ℝ) * N2 Q2) ^ 2 = (B.card : ℝ) * N2sq Q2 := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), N2_sq]
      nlinarith [Finset.sum_nonneg (s := B) fun m _ => norm_nonneg (fhat Q2 m),
        mul_nonneg (Real.sqrt_nonneg (B.card : ℝ)) (N2_nonneg Q2)]
    have h2 : ∑ m ∈ B, ‖fhat Q2 m‖ ≤ 14 * K ^ 2 * Real.sqrt (B.card : ℝ) := by
      have := mul_le_mul_of_nonneg_left hN2_Q2 (Real.sqrt_nonneg (B.card : ℝ))
      linarith
    have hpos : (0 : ℝ) ≤ 4 + 2 * Real.sqrt 2 := by positivity
    calc ‖∑ m, fhat φtC (-m) * fhat (conv (gB B) Q2) m‖
        ≤ (4 + 2 * Real.sqrt 2) * ∑ m ∈ B, ‖fhat Q2 m‖ := h1
      _ ≤ (4 + 2 * Real.sqrt 2) * (14 * K ^ 2 * Real.sqrt (B.card : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 hpos
      _ = (4 + 2 * Real.sqrt 2) * (14 * K ^ 2) * Real.sqrt (B.card : ℝ) := by ring
  have hI2_ub : ‖I2‖ ≤ (4 + 2 * Real.sqrt 2) * (14 * K ^ 2) ^ 2 := by
    dsimp [I2]
    rw [parseval_inner]
    have h1 : ‖∑ m, fhat φtC (-m) * fhat (conv Q2 Q2) m‖ ≤
        (4 + 2 * Real.sqrt 2) * N2sq Q2 := by
      rw [parseval_sq, Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
      rw [fhat_conv, norm_mul, norm_mul, ← sq]
      exact mul_le_mul_of_nonneg_right (hfhat_φ_ub m) (sq_nonneg _)
    have h2 : N2sq Q2 ≤ (14 * K ^ 2) ^ 2 := by
      rw [← N2_sq Q2]
      exact pow_le_pow_left₀ (N2_nonneg Q2) hN2_Q2 2
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  -- Combine lower and upper bounds on `X`
  have hX_lower : (4 + Real.sqrt 2) * (B.card : ℝ) -
      2 * ((4 + 2 * Real.sqrt 2) * (14 * K ^ 2) * Real.sqrt (B.card : ℝ)) -
      (4 + 2 * Real.sqrt 2) * (14 * K ^ 2) ^ 2 ≤ X := by
    have htri1 : ‖I0‖ - ‖2 * I1 - I2‖ ≤ ‖I0 - 2 * I1 + I2‖ := by
      have h := norm_sub_norm_le I0 (2 * I1 - I2)
      have heq : I0 - (2 * I1 - I2) = I0 - 2 * I1 + I2 := by ring
      rw [heq] at h
      exact h
    have htri2 : ‖2 * I1 - I2‖ ≤ 2 * ‖I1‖ + ‖I2‖ := by
      have h := norm_sub_le (2 * I1) I2
      rw [norm_mul] at h
      have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h2n] at h
      exact h
    linarith [hX_ge_norm, hI0_lb, hI1_ub, hI2_ub]
  -- Algebraic cleanup using `1.4 ≤ √2 ≤ 1.5`
  have hs_lo : (1.4 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hs_hi : Real.sqrt 2 ≤ 1.5 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  set sB : ℝ := Real.sqrt (B.card : ℝ)
  have hsB_sq : sB ^ 2 = (B.card : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hsB_nn : 0 ≤ sB := Real.sqrt_nonneg _
  have hK4_nn : 0 ≤ K ^ 4 := by positivity
  have hgap : (0.7 : ℝ) * sB ^ 2 ≤ 336 * K ^ 2 * sB + 2864 * K ^ 4 := by
    have hcomb := hX_lower.trans hX_upper
    rw [← hsB_sq] at hcomb
    nlinarith [sq_nonneg sB, mul_nonneg (sq_nonneg K) hsB_nn, hK4_nn]
  have hamgm : 336 * K ^ 2 * sB ≤ 0.2 * sB ^ 2 + 141120 * K ^ 4 := by
    nlinarith [sq_nonneg (sB - 840 * K ^ 2)]
  rw [← hsB_sq]
  nlinarith

end DiscreteFourier

/- ## Section 6: Shankar's exact total-boundary counting identity (arXiv:2609.05338, Lemma 3.1) -/

/-- Symmetrized integer set `A_Z = S ∪ (-S)`. -/
private def symInt (S : Finset ℕ) : Finset ℤ :=
  S.image (fun n : ℕ => (n : ℤ)) ∪ S.image (fun n : ℕ => -(n : ℤ))

private lemma mem_symInt_iff {S : Finset ℕ} (_h0 : 0 ∉ S) (x : ℤ) :
    x ∈ symInt S ↔ (∃ n ∈ S, x = (n : ℤ)) ∨ (∃ n ∈ S, x = -(n : ℤ)) := by
  simp only [symInt, Finset.mem_union, Finset.mem_image, eq_comm]

private lemma neg_mem_symInt {S : Finset ℕ} {x : ℤ} (hx : x ∈ symInt S) : -x ∈ symInt S := by
  simp only [symInt, Finset.mem_union, Finset.mem_image] at hx ⊢
  rcases hx with ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
  · exact Or.inr ⟨n, hn, rfl⟩
  · exact Or.inl ⟨n, hn, (neg_neg _).symm⟩

private lemma zero_notMem_symInt {S : Finset ℕ} (h0 : 0 ∉ S) : (0 : ℤ) ∉ symInt S := by
  simp only [symInt, Finset.mem_union, Finset.mem_image, not_or]
  refine ⟨?_, ?_⟩
  · rintro ⟨n, hn, h⟩; exact h0 ((Int.natCast_eq_zero.mp h) ▸ hn)
  · rintro ⟨n, hn, h⟩
    have : (n : ℤ) = 0 := by omega
    exact h0 ((Int.natCast_eq_zero.mp this) ▸ hn)

private lemma natCast_mem_symInt_iff {S : Finset ℕ} (h0 : 0 ∉ S) (n : ℕ) :
    (n : ℤ) ∈ symInt S ↔ n ∈ S := by
  constructor
  · intro h
    rcases (mem_symInt_iff h0 _).mp h with ⟨m, hm, heq⟩ | ⟨m, hm, heq⟩
    · exact (Int.ofNat.inj heq) ▸ hm
    · have : m = 0 := by omega
      exact absurd (this ▸ hm) h0
  · intro hn
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hn)

private lemma neg_natCast_mem_symInt_iff {S : Finset ℕ} (h0 : 0 ∉ S) (n : ℕ) :
    -(n : ℤ) ∈ symInt S ↔ n ∈ S := by
  constructor
  · intro h
    have := neg_mem_symInt h
    rw [neg_neg] at this
    exact (natCast_mem_symInt_iff h0 n).mp this
  · intro hn
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hn)

private lemma card_symInt {S : Finset ℕ} (h0 : 0 ∉ S) : (symInt S).card = 2 * S.card := by
  unfold symInt
  have hdisj : Disjoint (S.image (fun n : ℕ => (n : ℤ))) (S.image (fun n : ℕ => -(n : ℤ))) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hy
    have : a = 0 := by omega
    exact h0 (this ▸ ha)
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective S (fun (a b : ℕ) (h : (a : ℤ) = (b : ℤ)) => Int.ofNat.inj h),
    Finset.card_image_of_injective S (fun (a b : ℕ) (h : -(a : ℤ) = -(b : ℤ)) => Int.ofNat.inj (neg_inj.mp h)),
    two_mul]

/-- Shankar's Lemma 3.1: `T(A) ≤ 3 * ∑_{t ∈ A} |B_t|` for `A = S ∪ (-S)`. -/
private lemma shankar_boundary_identity (S : Finset ℕ) (h0 : 0 ∉ S) :
    ((symInt S ×ˢ symInt S).filter (fun p => p.1 - p.2 ∈ symInt S)).card ≤
      3 * ∑ t ∈ symInt S, ((symInt S).filter (fun a => a - t ∈ symInt S ∧ a + t ∉ symInt S)).card := by
  set A := symInt S
  let Qset := (S ×ˢ S).filter (fun p => p.1 + p.2 ∈ S)
  let Dset := (S ×ˢ S).filter (fun p => (p.1 : ℤ) - (p.2 : ℤ) ∈ A)
  let Iset := (S ×ˢ S).filter (fun p => (p.1 : ℤ) - (p.2 : ℤ) ∈ A ∧ p.1 + p.2 ∈ S)
  let Tset := (A ×ˢ A).filter (fun p => p.1 - p.2 ∈ A)
  -- Helper: sum over `A` splits into positive and negative parts
  have hsum_A : ∀ f : ℤ → ℕ, ∑ x ∈ A, f x = ∑ u ∈ S, (f (u : ℤ) + f (-(u : ℤ))) := by
    intro f
    have hdisj : Disjoint (S.image (fun n : ℕ => (n : ℤ))) (S.image (fun n : ℕ => -(n : ℤ))) := by
      rw [Finset.disjoint_left]
      intro x hx hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, _, hab⟩ := Finset.mem_image.mp hy
      have : a = 0 := by omega
      exact h0 (this ▸ ha)
    change ∑ x ∈ S.image (fun n : ℕ => (n : ℤ)) ∪ S.image (fun n : ℕ => -(n : ℤ)), f x = _
    rw [Finset.sum_union hdisj,
      Finset.sum_image (fun (a : ℕ) _ (b : ℕ) _ (h : (a : ℤ) = (b : ℤ)) => Int.ofNat.inj h),
      Finset.sum_image (fun (a : ℕ) _ (b : ℕ) _ (h : -(a : ℤ) = -(b : ℤ)) => Int.ofNat.inj (neg_inj.mp h)),
      Finset.sum_add_distrib]
  -- Step 1: `Dset.card = 2 * Qset.card`
  have hD_eq : Dset.card = 2 * Qset.card := by
    let Dgt := Dset.filter (fun p => p.2 < p.1)
    let Dlt := Dset.filter (fun p => p.1 < p.2)
    have hD_union : Dset = Dgt ∪ Dlt := by
      ext p
      simp only [Dgt, Dlt, Dset, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨⟨h1, h2⟩, hsub⟩
        by_cases heq : p.1 = p.2
        · exfalso; rw [heq, sub_self] at hsub; exact zero_notMem_symInt h0 hsub
        · rcases lt_or_gt_of_ne heq with h | h
          · exact Or.inr ⟨⟨⟨h1, h2⟩, hsub⟩, h⟩
          · exact Or.inl ⟨⟨⟨h1, h2⟩, hsub⟩, h⟩
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    have hD_disj : Disjoint Dgt Dlt := by
      rw [Finset.disjoint_left]
      intro p h1 h2
      have := (Finset.mem_filter.mp h1).2
      have := (Finset.mem_filter.mp h2).2
      omega
    have hDgt_eq : Dgt.card = Qset.card := by
      refine Finset.card_bij (fun p _ => (p.2, p.1 - p.2)) ?_ ?_ ?_
      · intro p hp
        simp only [Dgt, Dset, Qset, Finset.mem_filter, Finset.mem_product] at hp ⊢
        obtain ⟨⟨⟨hp1, hp2⟩, hsub⟩, hlt⟩ := hp
        have hcast : ((p.1 - p.2 : ℕ) : ℤ) = (p.1 : ℤ) - (p.2 : ℤ) := Int.ofNat_sub hlt.le
        have hdiff : p.1 - p.2 ∈ S := (natCast_mem_symInt_iff h0 _).mp (hcast ▸ hsub)
        refine ⟨⟨hp2, hdiff⟩, ?_⟩
        rwa [Nat.add_sub_of_le hlt.le]
      · intro p1 hp1 p2 hp2 heq
        have hlt1 := (Finset.mem_filter.mp hp1).2
        have hlt2 := (Finset.mem_filter.mp hp2).2
        have h2 : p1.2 = p2.2 := congrArg Prod.fst heq
        have hd : p1.1 - p1.2 = p2.1 - p2.2 := congrArg Prod.snd heq
        exact Prod.ext (by omega) h2
      · intro q hq
        simp only [Qset, Finset.mem_filter, Finset.mem_product] at hq
        obtain ⟨⟨hq1, hq2⟩, hadd⟩ := hq
        have hq2_pos : 0 < q.2 := Nat.pos_of_ne_zero (fun h => h0 (h ▸ hq2))
        refine ⟨(q.1 + q.2, q.1), ?_, Prod.ext rfl (by omega)⟩
        simp only [Dgt, Dset, Finset.mem_filter, Finset.mem_product]
        refine ⟨⟨⟨hadd, hq1⟩, ?_⟩, by omega⟩
        have : ((q.1 + q.2 : ℕ) : ℤ) - (q.1 : ℤ) = (q.2 : ℤ) := by push_cast; ring
        rw [this]
        exact (natCast_mem_symInt_iff h0 _).mpr hq2
    have hDlt_eq : Dlt.card = Dgt.card := by
      refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
      · intro p hp
        simp only [Dlt, Dgt, Dset, Finset.mem_filter, Finset.mem_product] at hp ⊢
        obtain ⟨⟨⟨hp1, hp2⟩, hsub⟩, hlt⟩ := hp
        have hneg := neg_mem_symInt hsub
        rw [neg_sub] at hneg
        exact ⟨⟨⟨hp2, hp1⟩, hneg⟩, hlt⟩
      · intro p1 _ p2 _ heq
        exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
      · intro q hq
        simp only [Dlt, Dgt, Dset, Finset.mem_filter, Finset.mem_product] at hq ⊢
        obtain ⟨⟨⟨hq1, hq2⟩, hsub⟩, hlt⟩ := hq
        refine ⟨(q.2, q.1), ?_, rfl⟩
        have hneg := neg_mem_symInt hsub
        rw [neg_sub] at hneg
        exact ⟨⟨⟨hq2, hq1⟩, hneg⟩, hlt⟩
    rw [hD_union, Finset.card_union_of_disjoint hD_disj, hDlt_eq, hDgt_eq, two_mul]
  -- Step 2: `Iset.card ≤ Qset.card`
  have hI_le : Iset.card ≤ Qset.card :=
    Finset.card_le_card fun p hp => by
      simp only [Iset, Qset, Finset.mem_filter] at hp ⊢
      exact ⟨hp.1, hp.2.2⟩
  -- Step 3: `Tset.card = 6 * Qset.card`
  have hT_eq : Tset.card = 6 * Qset.card := by
    have hsumT : Tset.card = ∑ a ∈ A, ∑ t ∈ A, if a - t ∈ A then 1 else 0 := by
      rw [Finset.card_filter, Finset.sum_product]
    rw [hsumT, hsum_A]
    have hinner : ∀ u ∈ S,
        (∑ t ∈ A, if (u : ℤ) - t ∈ A then 1 else 0) +
        (∑ t ∈ A, if -(u : ℤ) - t ∈ A then 1 else 0) =
        2 * ∑ v ∈ S, ((if (u : ℤ) - (v : ℤ) ∈ A then 1 else 0) +
                      (if u + v ∈ S then 1 else 0)) := by
      intro u _
      rw [hsum_A, hsum_A, ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      have h1 : (-(u : ℤ) - -(v : ℤ) ∈ A) ↔ ((u : ℤ) - (v : ℤ) ∈ A) := by
        constructor <;> intro h
        · have := neg_mem_symInt h; convert this using 1; ring
        · have := neg_mem_symInt h; convert this using 1; ring
      have h2 : ((u : ℤ) - -(v : ℤ) ∈ A) ↔ u + v ∈ S := by
        rw [sub_neg_eq_add, ← Nat.cast_add]
        exact natCast_mem_symInt_iff h0 (u + v)
      have h3 : (-(u : ℤ) - (v : ℤ) ∈ A) ↔ u + v ∈ S := by
        have heq : -(u : ℤ) - (v : ℤ) = -((u + v : ℕ) : ℤ) := by push_cast; ring
        rw [heq]
        exact neg_natCast_mem_symInt_iff h0 (u + v)
      simp only [h1, h2, h3]
      omega
    rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
    have hD_sum : ∑ u ∈ S, ∑ v ∈ S, (if (u : ℤ) - (v : ℤ) ∈ A then 1 else 0) = Dset.card := by
      rw [Finset.card_filter, Finset.sum_product]
    have hQ_sum : ∑ u ∈ S, ∑ v ∈ S, (if u + v ∈ S then 1 else 0) = Qset.card := by
      rw [Finset.card_filter, Finset.sum_product]
    simp_rw [Finset.sum_add_distrib]
    rw [hD_sum, hQ_sum, hD_eq]
    omega
  -- Step 4: `∑ t ∈ A, |B_t| + 4 * Iset.card = 6 * Qset.card`
  have hB_eq : (∑ t ∈ A, (A.filter (fun a => a - t ∈ A ∧ a + t ∉ A)).card) + 4 * Iset.card =
      6 * Qset.card := by
    have hrew : ∑ t ∈ A, (A.filter (fun a => a - t ∈ A ∧ a + t ∉ A)).card =
        ∑ a ∈ A, ∑ t ∈ A, if a - t ∈ A ∧ a + t ∉ A then 1 else 0 := by
      simp_rw [Finset.card_filter]
      rw [Finset.sum_comm]
    rw [hrew, hsum_A]
    have hinner : ∀ u ∈ S,
        (∑ t ∈ A, if (u : ℤ) - t ∈ A ∧ (u : ℤ) + t ∉ A then 1 else 0) +
        (∑ t ∈ A, if -(u : ℤ) - t ∈ A ∧ -(u : ℤ) + t ∉ A then 1 else 0) =
        ∑ v ∈ S, (2 * (if (u : ℤ) - (v : ℤ) ∈ A ∧ u + v ∉ S then 1 else 0) +
                  2 * (if u + v ∈ S ∧ (u : ℤ) - (v : ℤ) ∉ A then 1 else 0)) := by
      intro u _
      rw [hsum_A, hsum_A, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      have h1 : (-(u : ℤ) - -(v : ℤ) ∈ A) ↔ ((u : ℤ) - (v : ℤ) ∈ A) := by
        constructor <;> intro h
        · have := neg_mem_symInt h; convert this using 1; ring
        · have := neg_mem_symInt h; convert this using 1; ring
      have h2 : (-(u : ℤ) + (v : ℤ) ∈ A) ↔ ((u : ℤ) - (v : ℤ) ∈ A) := by
        constructor <;> intro h
        · have := neg_mem_symInt h; convert this using 1; ring
        · have := neg_mem_symInt h; convert this using 1; ring
      have h3 : ((u : ℤ) + (v : ℤ) ∈ A) ↔ u + v ∈ S := by
        rw [← Nat.cast_add]; exact natCast_mem_symInt_iff h0 (u + v)
      have h4 : ((u : ℤ) - -(v : ℤ) ∈ A) ↔ u + v ∈ S := by
        rw [sub_neg_eq_add, ← Nat.cast_add]; exact natCast_mem_symInt_iff h0 (u + v)
      have h5 : (-(u : ℤ) - (v : ℤ) ∈ A) ↔ u + v ∈ S := by
        have heq : -(u : ℤ) - (v : ℤ) = -((u + v : ℕ) : ℤ) := by push_cast; ring
        rw [heq]; exact neg_natCast_mem_symInt_iff h0 (u + v)
      have h6 : (-(u : ℤ) + -(v : ℤ) ∈ A) ↔ u + v ∈ S := by
        have heq : -(u : ℤ) + -(v : ℤ) = -((u + v : ℕ) : ℤ) := by push_cast; ring
        rw [heq]; exact neg_natCast_mem_symInt_iff h0 (u + v)
      have h7 : ((u : ℤ) + -(v : ℤ) ∈ A) ↔ ((u : ℤ) - (v : ℤ) ∈ A) := by
        rw [← sub_eq_add_neg]
      simp only [h1, h2, h3, h4, h5, h6, h7]
      by_cases hd : (u : ℤ) - (v : ℤ) ∈ A <;> by_cases hp : u + v ∈ S <;> simp [hd, hp]
    rw [Finset.sum_congr rfl hinner]
    have hpt : ∀ u ∈ S, ∀ v ∈ S,
        (2 * (if (u : ℤ) - (v : ℤ) ∈ A ∧ u + v ∉ S then 1 else 0) +
         2 * (if u + v ∈ S ∧ (u : ℤ) - (v : ℤ) ∉ A then 1 else 0)) +
        4 * (if (u : ℤ) - (v : ℤ) ∈ A ∧ u + v ∈ S then 1 else 0) =
        2 * (if (u : ℤ) - (v : ℤ) ∈ A then 1 else 0) + 2 * (if u + v ∈ S then 1 else 0) := by
      intro u _ v _
      by_cases hd : (u : ℤ) - (v : ℤ) ∈ A <;> by_cases hp : u + v ∈ S <;> simp [hd, hp]
    have hI_sum : Iset.card = ∑ u ∈ S, ∑ v ∈ S, if (u : ℤ) - (v : ℤ) ∈ A ∧ u + v ∈ S then 1 else 0 := by
      rw [Finset.card_filter, Finset.sum_product]
    have hD_sum : Dset.card = ∑ u ∈ S, ∑ v ∈ S, if (u : ℤ) - (v : ℤ) ∈ A then 1 else 0 := by
      rw [Finset.card_filter, Finset.sum_product]
    have hQ_sum : Qset.card = ∑ u ∈ S, ∑ v ∈ S, if u + v ∈ S then 1 else 0 := by
      rw [Finset.card_filter, Finset.sum_product]
    rw [hI_sum, Finset.mul_sum]
    simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    have hcomb : ∑ u ∈ S, ∑ v ∈ S,
        ((2 * (if (u : ℤ) - (v : ℤ) ∈ A ∧ u + v ∉ S then 1 else 0) +
          2 * (if u + v ∈ S ∧ (u : ℤ) - (v : ℤ) ∉ A then 1 else 0)) +
         4 * (if (u : ℤ) - (v : ℤ) ∈ A ∧ u + v ∈ S then 1 else 0)) =
        ∑ u ∈ S, ∑ v ∈ S,
          (2 * (if (u : ℤ) - (v : ℤ) ∈ A then 1 else 0) + 2 * (if u + v ∈ S then 1 else 0)) :=
      Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => hpt u hu v hv
    rw [hcomb]
    simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [← hD_sum, ← hQ_sum, hD_eq]
    omega
  change Tset.card ≤ 3 * ∑ t ∈ A, (A.filter (fun a => a - t ∈ A ∧ a + t ∉ A)).card
  omega

/- ## Section 7: Transporting `symInt S` to `ZMod Q` and closing `erdos_510.variants.bedert` -/

private lemma int_cast_zmod_eq_iff {Q : ℕ} {a b : ℤ} (hQ : 0 < Q)
    (ha : |a| < (Q : ℤ) / 2) (hb : |b| < (Q : ℤ) / 2) :
    (a : ZMod Q) = (b : ZMod Q) ↔ a = b := by
  constructor
  · intro h
    have hdvd : (Q : ℤ) ∣ a - b := (ZMod.intCast_eq_intCast_iff_dvd_sub b a Q).mp h.symm
    obtain ⟨k, hk⟩ := hdvd
    have hlt : |a - b| < (Q : ℤ) := by
      calc |a - b| ≤ |a| + |b| := abs_sub a b
        _ < (Q : ℤ) / 2 + (Q : ℤ) / 2 := add_lt_add ha hb
        _ ≤ (Q : ℤ) := by omega
    have hk0 : k = 0 := by
      by_contra hne
      have h1 : 1 ≤ |k| := Int.one_le_abs hne
      have h2 : (Q : ℤ) ≤ |a - b| := by
        rw [hk, abs_mul, abs_of_pos (Int.natCast_pos.mpr hQ)]
        nlinarith
      omega
    subst hk0
    simp only [mul_zero] at hk
    omega
  · intro h; rw [h]

private lemma main_bound (S : Finset ℕ) (h0 : 0 ∉ S) (hne : S.Nonempty)
    (K : ℝ) (hK : ∀ θ : ℝ, -K / 2 ≤ ∑ n ∈ S, Real.cos ((n : ℝ) * θ)) :
    (S.card : ℝ) ≤ 1500000 * K ^ 5 := by
  let M : ℕ := S.sup id
  obtain ⟨Q, hQge, hQprime⟩ := Nat.exists_infinite_primes (10 * M + 10)
  have : Fact Q.Prime := ⟨hQprime⟩
  have hQpos : 0 < Q := hQprime.pos
  have hmem_le : ∀ z ∈ symInt S, |z| ≤ (M : ℤ) := by
    intro z hz
    rcases (mem_symInt_iff h0 z).mp hz with ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
    · rw [abs_of_nonneg (Int.natCast_nonneg n)]
      exact Int.ofNat_le.mpr (Finset.le_sup (f := id) hn)
    · rw [abs_neg, abs_of_nonneg (Int.natCast_nonneg n)]
      exact Int.ofNat_le.mpr (Finset.le_sup (f := id) hn)
  have hbound : ∀ z : ℤ, |z| ≤ 2 * (M : ℤ) → |z| < (Q : ℤ) / 2 := by
    intro z hz; omega
  let AQ : Finset (ZMod Q) := (symInt S).image (Int.cast : ℤ → ZMod Q)
  have hinj : Set.InjOn (Int.cast : ℤ → ZMod Q) (symInt S : Set ℤ) := by
    intro a ha b hb h
    exact (int_cast_zmod_eq_iff hQpos (hbound a (by linarith [hmem_le a ha]))
      (hbound b (by linarith [hmem_le b hb]))).mp h
  have hmem_AQ_iff : ∀ z : ℤ, |z| ≤ 2 * (M : ℤ) → ((z : ZMod Q) ∈ AQ ↔ z ∈ symInt S) := by
    intro z hz
    constructor
    · intro h
      obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp h
      have heq := (int_cast_zmod_eq_iff hQpos (hbound w (by linarith [hmem_le w hw]))
        (hbound z hz)).mp hwz
      exact heq ▸ hw
    · intro h; exact Finset.mem_image_of_mem _ h
  have hAQ_card : AQ.card = 2 * S.card := by
    rw [Finset.card_image_of_injOn hinj, card_symInt h0]
  have hAQ_sym : Sym AQ := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨-z, neg_mem_symInt hz, Int.cast_neg z⟩
  have hAQ_zero : (0 : ZMod Q) ∉ AQ := by
    intro h
    have h0' : (0 : ℤ) ∈ symInt S := (hmem_AQ_iff 0 (by simp)).mp (by simpa using h)
    exact zero_notMem_symInt h0 h0'
  have hAQ_ne : AQ.Nonempty := by
    obtain ⟨n, hn⟩ := hne
    exact ⟨((n : ℤ) : ZMod Q), Finset.mem_image_of_mem _ ((natCast_mem_symInt_iff h0 n).mpr hn)⟩
  -- `fR AQ x = 2 * ∑ n ∈ S, cos(n * θ_x) ≥ -K`
  have hAQ_pos : ∀ x : ZMod Q, 0 ≤ fR AQ x + K := by
    intro x
    let θ : ℝ := 2 * Real.pi * (x.val : ℝ) / (Q : ℝ)
    have hfR_eq : fR AQ x = 2 * ∑ n ∈ S, Real.cos ((n : ℝ) * θ) := by
      have hdisj : Disjoint (S.image (fun n : ℕ => (n : ZMod Q)))
          (S.image (fun n : ℕ => -(n : ZMod Q))) := by
        rw [Finset.disjoint_left]
        intro y hy1 hy2
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy1
        obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hy2
        have heq : (((-(b : ℤ) : ℤ) : ZMod Q)) = ((a : ℤ) : ZMod Q) := by
          rw [Int.cast_neg, Int.cast_natCast, Int.cast_natCast]
          exact hab
        have hba := (int_cast_zmod_eq_iff hQpos
          (hbound (-(b : ℤ)) (by linarith [hmem_le (-(b : ℤ)) ((neg_natCast_mem_symInt_iff h0 b).mpr hb)]))
          (hbound (a : ℤ) (by linarith [hmem_le (a : ℤ) ((natCast_mem_symInt_iff h0 a).mpr ha)]))).mp heq
        have : a = 0 := by omega
        exact h0 (this ▸ ha)
      have hAQ_union : AQ = S.image (fun n : ℕ => (n : ZMod Q)) ∪ S.image (fun n : ℕ => -(n : ZMod Q)) := by
        ext y
        simp only [AQ, symInt, Finset.image_union, Finset.mem_union, Finset.mem_image]
        constructor
        · rintro (⟨z, ⟨n, hn, rfl⟩, rfl⟩ | ⟨z, ⟨n, hn, rfl⟩, rfl⟩)
          · exact Or.inl ⟨n, hn, by simp⟩
          · exact Or.inr ⟨n, hn, by simp⟩
        · rintro (⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩)
          · exact Or.inl ⟨(n : ℤ), ⟨n, hn, rfl⟩, by simp⟩
          · exact Or.inr ⟨-(n : ℤ), ⟨n, hn, rfl⟩, by simp⟩
      have hinj1 : Set.InjOn (fun n : ℕ => (n : ZMod Q)) (S : Set ℕ) := by
        intro a ha b hb h
        have heq : ((a : ℤ) : ZMod Q) = ((b : ℤ) : ZMod Q) := by simpa using h
        have := (int_cast_zmod_eq_iff hQpos
          (hbound (a : ℤ) (by linarith [hmem_le (a : ℤ) ((natCast_mem_symInt_iff h0 a).mpr ha)]))
          (hbound (b : ℤ) (by linarith [hmem_le (b : ℤ) ((natCast_mem_symInt_iff h0 b).mpr hb)]))).mp heq
        omega
      have hinj2 : Set.InjOn (fun n : ℕ => -(n : ZMod Q)) (S : Set ℕ) := by
        intro a ha b hb h
        exact hinj1 ha hb (neg_inj.mp h)
      unfold fR gB
      rw [hAQ_union, Finset.sum_union hdisj, Finset.sum_image hinj1, Finset.sum_image hinj2,
        Complex.add_re, Complex.re_sum, Complex.re_sum]
      have hs1 : ∑ n ∈ S, (e ((n : ZMod Q) * x)).re = ∑ n ∈ S, Real.cos ((n : ℝ) * θ) :=
        Finset.sum_congr rfl fun n _ => e_natCast n x
      have hs2 : ∑ n ∈ S, (e (-(n : ZMod Q) * x)).re = ∑ n ∈ S, Real.cos ((n : ℝ) * θ) :=
        Finset.sum_congr rfl fun n _ => by
          rw [neg_mul, e_neg, Complex.conj_re, e_natCast n x]
      rw [hs1, hs2, two_mul]
    rw [hfR_eq]
    linarith [hK θ]
  have hK1 : 1 ≤ K := one_le_K AQ hAQ_sym hAQ_zero hAQ_ne K hAQ_pos
  by_cases hsmall : (AQ.card : ℝ) < 2 * K ^ 2
  · rw [hAQ_card] at hsmall
    push_cast at hsmall
    have hK25 : K ^ 2 ≤ K ^ 5 := pow_le_pow_right₀ hK1 (by norm_num)
    nlinarith
  · push Not at hsmall
    have hT_lb := roth_triples AQ hAQ_sym hAQ_zero K (by linarith) hAQ_pos hsmall
    -- Transport Shankar's identity to `AQ`
    have hT_eq : ((AQ ×ˢ AQ).filter (fun p => p.1 - p.2 ∈ AQ)).card =
        ((symInt S ×ˢ symInt S).filter (fun p => p.1 - p.2 ∈ symInt S)).card := by
      refine (Finset.card_bij (fun (p : ℤ × ℤ) _ => ((p.1 : ZMod Q), (p.2 : ZMod Q))) ?_ ?_ ?_).symm
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
        obtain ⟨⟨h1, h2⟩, hsub⟩ := hp
        refine ⟨⟨Finset.mem_image_of_mem _ h1, Finset.mem_image_of_mem _ h2⟩, ?_⟩
        rw [← Int.cast_sub]
        exact Finset.mem_image_of_mem _ hsub
      · intro p1 hp1 p2 hp2 heq
        simp only [Finset.mem_filter, Finset.mem_product] at hp1 hp2
        exact Prod.ext (hinj hp1.1.1 hp2.1.1 (congrArg Prod.fst heq))
          (hinj hp1.1.2 hp2.1.2 (congrArg Prod.snd heq))
      · rintro ⟨q1, q2⟩ hq
        simp only [Finset.mem_filter, Finset.mem_product] at hq
        obtain ⟨⟨hq1, hq2⟩, hsub⟩ := hq
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq1
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq2
        refine ⟨(a, b), ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_product]
        refine ⟨⟨ha, hb⟩, ?_⟩
        rw [← Int.cast_sub] at hsub
        have hab : |a - b| ≤ 2 * (M : ℤ) := by
          calc |a - b| ≤ |a| + |b| := abs_sub a b
            _ ≤ (M : ℤ) + (M : ℤ) := add_le_add (hmem_le a ha) (hmem_le b hb)
            _ = 2 * (M : ℤ) := by ring
        exact (hmem_AQ_iff (a - b) hab).mp hsub
    have hB_eq : ∀ t ∈ symInt S,
        (Bt AQ (t : ZMod Q)).card =
          ((symInt S).filter (fun a => a - t ∈ symInt S ∧ a + t ∉ symInt S)).card := by
      intro t ht
      refine (Finset.card_bij (fun (a : ℤ) _ => (a : ZMod Q)) ?_ ?_ ?_).symm
      · intro a ha
        simp only [Bt, Finset.mem_filter] at ha ⊢
        obtain ⟨haA, hsub, hadd⟩ := ha
        refine ⟨Finset.mem_image_of_mem _ haA, ?_, ?_⟩
        · rw [← Int.cast_sub]; exact Finset.mem_image_of_mem _ hsub
        · rw [← Int.cast_add]
          intro hmem
          have hbd : |a + t| ≤ 2 * (M : ℤ) := by
            calc |a + t| ≤ |a| + |t| := abs_add_le a t
              _ ≤ (M : ℤ) + (M : ℤ) := add_le_add (hmem_le a haA) (hmem_le t ht)
              _ = 2 * (M : ℤ) := by ring
          exact hadd ((hmem_AQ_iff (a + t) hbd).mp hmem)
      · intro a1 ha1 a2 ha2 heq
        exact hinj (Finset.mem_filter.mp ha1).1 (Finset.mem_filter.mp ha2).1 heq
      · intro x hx
        simp only [Bt, Finset.mem_filter] at hx
        obtain ⟨hxA, hsub, hadd⟩ := hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hxA
        refine ⟨a, ?_, rfl⟩
        simp only [Finset.mem_filter]
        refine ⟨ha, ?_, ?_⟩
        · rw [← Int.cast_sub] at hsub
          have hbd : |a - t| ≤ 2 * (M : ℤ) := by
            calc |a - t| ≤ |a| + |t| := abs_sub a t
              _ ≤ (M : ℤ) + (M : ℤ) := add_le_add (hmem_le a ha) (hmem_le t ht)
              _ = 2 * (M : ℤ) := by ring
          exact (hmem_AQ_iff (a - t) hbd).mp hsub
        · intro hm
          rw [← Int.cast_add] at hadd
          exact hadd (Finset.mem_image_of_mem _ hm)
    have hsumB_eq : ∑ t ∈ AQ, (Bt AQ t).card =
        ∑ t ∈ symInt S, ((symInt S).filter (fun a => a - t ∈ symInt S ∧ a + t ∉ symInt S)).card := by
      rw [Finset.sum_image hinj]
      exact Finset.sum_congr rfl fun t ht => hB_eq t ht
    have hshankar : ((AQ ×ˢ AQ).filter (fun p => p.1 - p.2 ∈ AQ)).card ≤
        3 * ∑ t ∈ AQ, (Bt AQ t).card := by
      rw [hT_eq, hsumB_eq]
      exact shankar_boundary_identity S h0
    have hsumB_ub : ∑ t ∈ AQ, ((Bt AQ t).card : ℝ) ≤ (AQ.card : ℝ) * (500000 * K ^ 4) := by
      calc ∑ t ∈ AQ, ((Bt AQ t).card : ℝ)
          ≤ ∑ _t ∈ AQ, (500000 * K ^ 4) :=
            Finset.sum_le_sum fun t _ => prop_7_3 AQ hAQ_sym hAQ_zero K hK1 hAQ_pos t
        _ = (AQ.card : ℝ) * (500000 * K ^ 4) := by rw [Finset.sum_const, nsmul_eq_mul]
    have hshankarR : (((AQ ×ˢ AQ).filter (fun p => p.1 - p.2 ∈ AQ)).card : ℝ) ≤
        3 * ∑ t ∈ AQ, ((Bt AQ t).card : ℝ) := by exact_mod_cast hshankar
    have hAQ_pos_card : (0 : ℝ) < (AQ.card : ℝ) := by
      have : 0 < AQ.card := Finset.card_pos.mpr hAQ_ne
      exact_mod_cast this
    have hkey : (AQ.card : ℝ) ^ 2 / (2 * K) ≤ 3 * ((AQ.card : ℝ) * (500000 * K ^ 4)) := by
      linarith
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * K)] at hkey
    have hAQ_le : (AQ.card : ℝ) ≤ 3000000 * K ^ 5 := by
      have hmul : (AQ.card : ℝ) * (AQ.card : ℝ) ≤ (AQ.card : ℝ) * (3000000 * K ^ 5) := by
        nlinarith
      exact le_of_mul_le_mul_left hmul hAQ_pos_card
    rw [hAQ_card] at hAQ_le
    push_cast at hAQ_le
    linarith

end OMA.Bedert

theorem OMA.solution : type_of% @Erdos510.erdos_510.variants.bedert := by
  refine ⟨(1 : ℝ) / 100, by norm_num, Filter.eventually_atTop.mpr ⟨1, fun N hN A h0 hcard => ?_⟩⟩
  by_contra h
  push Not at h
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  let K : ℝ := 2 * ((1 : ℝ) / 100) * (N : ℝ) ^ ((1 : ℝ) / 7)
  have hK : ∀ θ : ℝ, -K / 2 ≤ ∑ n ∈ A, Real.cos ((n : ℝ) * θ) := fun θ => by
    have hθ := h θ
    dsimp [K]
    linarith
  have hbound := OMA.Bedert.main_bound A h0 hne K hK
  rw [hcard] at hbound
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpow5 : ((N : ℝ) ^ ((1 : ℝ) / 7)) ^ 5 ≤ (N : ℝ) := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ ((1 : ℝ) / 7)) 5,
      ← Real.rpow_mul (by linarith)]
    calc (N : ℝ) ^ (((1 : ℝ) / 7) * (5 : ℕ)) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = (N : ℝ) := Real.rpow_one _
  have hK5 : K ^ 5 = ((2 : ℝ) / 100) ^ 5 * ((N : ℝ) ^ ((1 : ℝ) / 7)) ^ 5 := by
    dsimp [K]; ring
  rw [hK5] at hbound
  have hsmall : 1500000 * (((2 : ℝ) / 100) ^ 5 * ((N : ℝ) ^ ((1 : ℝ) / 7)) ^ 5) ≤
      1500000 * (((2 : ℝ) / 100) ^ 5 * (N : ℝ)) := by
    nlinarith [show (0 : ℝ) ≤ 1500000 * ((2 : ℝ) / 100) ^ 5 by positivity]
  have hlt : 1500000 * (((2 : ℝ) / 100) ^ 5 * (N : ℝ)) < (N : ℝ) := by
    have : 1500000 * ((2 : ℝ) / 100) ^ 5 < 1 := by norm_num
    nlinarith
  linarith
