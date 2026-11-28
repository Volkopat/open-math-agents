import OMAStatements.S_oeis_a255242
import Mathlib

namespace OMA.S_oeis_a255242

open ArithmeticFunction
open scoped ArithmeticFunction.zeta

def lift (f : ℕ → ℤ) : ArithmeticFunction ℤ := ⟨fun n => if n = 0 then 0 else f n, by simp⟩

lemma lift_apply (f : ℕ → ℤ) {n : ℕ} (hn : n ≠ 0) : lift f n = f n := by simp [lift, hn]

lemma sub_app (f g : ArithmeticFunction ℤ) (n : ℕ) : (f - g) n = f n - g n := by
  rw [sub_eq_add_neg]; simp [ArithmeticFunction.neg_apply, ArithmeticFunction.add_apply, sub_eq_add_neg]

lemma divsum (f : ℕ → ℤ) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, f d = f n + ∑ d ∈ n.properDivisors, f d := by
  rw [← Nat.cons_self_properDivisors hn, Finset.sum_cons]

lemma mulzeta (f : ArithmeticFunction ℤ) (x : ℕ) :
    (f * ζ) x = ∑ d ∈ x.divisors, f d := by
  have := ArithmeticFunction.coe_mul_zeta_apply (f := f) (x := x)
  simpa using this

lemma uniq (r : ℕ → ℤ) (x y : ℕ → ℤ)
    (hx : ∀ n, 1 ≤ n → x n = r n + ∑ d ∈ n.properDivisors, x d)
    (hy : ∀ n, 1 ≤ n → y n = r n + ∑ d ∈ n.properDivisors, y d) :
    ∀ n, 1 ≤ n → x n = y n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rw [hx n hn, hy n hn]
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    exact ih d (Nat.mem_properDivisors.1 hd).2 (Nat.pos_of_mem_properDivisors hd)

lemma alg (X : ArithmeticFunction ℤ) (r : ℕ → ℤ)
    (h : ∀ n, 1 ≤ n → 2 * X n = r n + (X * ζ) n) :
    ∀ n, 1 ≤ n → X n = r n + ∑ d ∈ n.properDivisors, X d := by
  intro n hn
  have := h n hn
  rw [mulzeta, divsum _ (by omega)] at this
  linarith

lemma sum_proper_id (n : ℕ) : ∑ d ∈ n.properDivisors, (d : ℤ) = (sigma 1 n : ℤ) - n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h := divsum (fun d : ℕ => (d : ℤ)) hn.ne'
  rw [ArithmeticFunction.sigma_one_apply]
  push_cast
  linarith

def S : ArithmeticFunction ℤ := lift (fun n => (sigma 1 n : ℤ))
def I : ArithmeticFunction ℤ := lift (fun n => (n : ℤ))
def Φ : ArithmeticFunction ℤ := lift (fun n => (Nat.totient n : ℤ))

lemma I_zeta : I * ζ = S := by
  ext n
  rw [mulzeta]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [S, lift]
  · rw [S, lift_apply _ hn.ne', ArithmeticFunction.sigma_one_apply]
    push_cast
    refine Finset.sum_congr rfl (fun d hd => ?_)
    rw [I, lift_apply _ (Nat.pos_of_mem_divisors hd).ne']

lemma Phi_zeta : Φ * ζ = I := by
  ext n
  rw [mulzeta]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [I, lift]
  · rw [I, lift_apply _ hn.ne']
    calc ∑ d ∈ n.divisors, Φ d = ∑ d ∈ n.divisors, ((Nat.totient d : ℕ) : ℤ) :=
          Finset.sum_congr rfl (fun d hd => by rw [Φ, lift_apply _ (Nat.pos_of_mem_divisors hd).ne'])
      _ = ((∑ d ∈ n.divisors, Nat.totient d : ℕ) : ℤ) := by push_cast; rfl
      _ = n := by rw [Nat.sum_totient]

lemma lift_sum_proper (f : ℕ → ℤ) (n : ℕ) :
    ∑ d ∈ n.properDivisors, lift f d = ∑ d ∈ n.properDivisors, f d :=
  Finset.sum_congr rfl (fun d hd => lift_apply _ (Nat.pos_of_mem_properDivisors hd).ne')

lemma H_zeta (H : ℕ → ℤ) (h1 : H 1 = 1)
    (h : ∀ n : ℕ, 2 ≤ n → H n = ∑ d ∈ n.properDivisors, H d) :
    lift H * ζ = lift H + lift H - 1 := by
  ext n
  rw [mulzeta]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [lift]
  · rw [divsum _ hn.ne', lift_sum_proper, lift_apply _ hn.ne']
    simp only [sub_app, ArithmeticFunction.add_apply, ArithmeticFunction.one_apply]
    rw [lift_apply _ hn.ne']
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have : n = 1 := by omega
      subst this
      simp [h1]
    · rw [if_neg (by omega), ← h n h2]; ring

lemma B_zeta (B : ℕ → ℤ) (h1 : B 1 = 1)
    (h : ∀ n : ℕ, 2 ≤ n → B n = 1 + ∑ d ∈ n.properDivisors, B d) :
    lift B * ζ = lift B + lift B - (ζ : ArithmeticFunction ℤ) := by
  ext n
  rw [mulzeta]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [lift]
  · rw [divsum _ hn.ne', lift_sum_proper, lift_apply _ hn.ne']
    simp only [sub_app, ArithmeticFunction.add_apply]
    rw [lift_apply _ hn.ne']
    rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg hn.ne']
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have : n = 1 := by omega
      subst this
      simp [h1]
    · have := h n h2
      push_cast
      linarith

lemma conv_apply (P : ArithmeticFunction ℤ) (Hf : ℕ → ℤ) {n : ℕ} (hn : n ≠ 0) :
    (P * lift Hf) n = ∑ d ∈ n.divisors, P d * Hf (n / d) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun i j => P i * lift Hf j)]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have : n / d ≠ 0 := (Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)).ne'
  rw [lift_apply _ this]

lemma rec_a (a : ℕ → ℤ) (ha : ∀ n : ℕ, 1 ≤ n → a n = ∑ d ∈ n.properDivisors, (a d + d)) :
    ∀ n, 1 ≤ n → a n = ((sigma 1 n : ℤ) - n) + ∑ d ∈ n.properDivisors, a d := by
  intro n hn
  rw [ha n hn, Finset.sum_add_distrib, sum_proper_id]; ring

lemma lemC (a : ℕ → ℤ) (ha : ∀ n : ℕ, 1 ≤ n → a n = ∑ d ∈ n.properDivisors, (a d + d))
    (c : ArithmeticFunction ℤ) (hc : c * ζ = c + c - (S - I)) :
    ∀ n, 1 ≤ n → a n = c n := by
  apply uniq (fun n => (sigma 1 n : ℤ) - n) a c (rec_a a ha)
  apply alg c
  intro n hn
  have := congrArg (fun f : ArithmeticFunction ℤ => f n) hc
  simp only [sub_app, ArithmeticFunction.add_apply] at this
  have hS : S n = (sigma 1 n : ℤ) := lift_apply _ (by omega)
  have hI : I n = (n : ℤ) := lift_apply _ (by omega)
  rw [hS, hI] at this
  linarith

theorem sol_aux : type_of% @OMA.S_oeis_a255242.main := by
  intro a g H B ha hg hH hB n hn
  refine ⟨?_, ?_, ?_⟩
  · have key : ∀ m, 1 ≤ m → (fun m => 2 * a m + (m : ℤ)) m =
        (sigma 1 m : ℤ) + ∑ d ∈ m.properDivisors, (fun m => 2 * a m + (m : ℤ)) d := by
      intro m hm
      have h1 := ha m hm
      have h2 := sum_proper_id m
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [Finset.sum_add_distrib] at h1
      linarith
    have := uniq (fun m => (sigma 1 m : ℤ)) _ g key hg n hn
    have this' : 2 * a n + (n : ℤ) = g n := this
    linarith
  · have hc : (S - I) * lift H * ζ = (S - I) * lift H + (S - I) * lift H - (S - I) := by
      rw [mul_assoc, H_zeta H hH.1 hH.2]
      ring
    have := lemC a ha _ hc n hn
    rw [this, conv_apply _ _ (by omega)]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    rw [sub_app, S, I, lift_apply _ hd0, lift_apply _ hd0]
  · have e1 : (I - Φ) * ζ = S - I := by rw [sub_mul, I_zeta, Phi_zeta]
    have hc : (I - Φ) * lift B * ζ = (I - Φ) * lift B + (I - Φ) * lift B - (S - I) := by
      rw [mul_assoc, B_zeta B hB.1 hB.2]
      linear_combination (-1 : ArithmeticFunction ℤ) * e1
    have := lemC a ha _ hc n hn
    rw [this, conv_apply _ _ (by omega)]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    rw [sub_app, Φ, I, lift_apply _ hd0, lift_apply _ hd0]

end OMA.S_oeis_a255242

theorem OMA.solution : type_of% @OMA.S_oeis_a255242.main := OMA.S_oeis_a255242.sol_aux
