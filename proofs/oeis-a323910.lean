import OMAStatements.S_oeis_a323910
import Mathlib

namespace OMA.S_oeis_a323910

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

lemma rec_one (x kf : ℕ → ℤ) (hk1 : kf 1 = 1) (hx1 : x 1 = 1)
    (hx : ∀ n : ℕ, 2 ≤ n → x n = -∑ d ∈ n.properDivisors, kf (n / d) * x d) :
    lift x * lift kf = 1 := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [lift]
  · rw [conv_apply _ _ hn.ne']
    rw [divsum (fun d => lift x d * kf (n / d)) hn.ne']
    rw [Nat.div_self hn, hk1, lift_apply _ hn.ne']
    have hp : ∑ d ∈ n.properDivisors, lift x d * kf (n / d) = ∑ d ∈ n.properDivisors, kf (n / d) * x d :=
      Finset.sum_congr rfl (fun d hd => by
        rw [lift_apply _ (Nat.pos_of_mem_properDivisors hd).ne', mul_comm])
    rw [hp]
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have : n = 1 := by omega
      subst this
      simp [hx1]
    · rw [ArithmeticFunction.one_apply, if_neg (by omega)]
      have := hx n h2
      linarith

lemma uniq1 (X A K : ArithmeticFunction ℤ) (hA : A * K = 1) (hX : X * K = 1) : X = A := by
  calc X = X * (A * K) := by rw [hA, mul_one]
    _ = A * (X * K) := by ring
    _ = A := by rw [hX, mul_one]

lemma mu_sum (n : ℕ) : ∑ d ∈ n.divisors, ArithmeticFunction.moebius d = if n = 1 then 1 else 0 := by
  have := congrArg (fun f : ArithmeticFunction ℤ => f n) ArithmeticFunction.moebius_mul_coe_zeta
  rw [mulzeta] at this
  rw [this, ArithmeticFunction.one_apply]

lemma Mob_I : lift (fun n => (n : ℤ) * ArithmeticFunction.moebius n) * I = 1 := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [lift, I]
  · have h1 : I = lift (fun n : ℕ => (n : ℤ)) := rfl
    rw [mul_comm, h1, conv_apply _ _ hn.ne']
    have h2 : ∀ d ∈ n.divisors, lift (fun n : ℕ => (n : ℤ)) d * (((n / d : ℕ) : ℤ) * ArithmeticFunction.moebius (n / d))
        = (n : ℤ) * ArithmeticFunction.moebius (n / d) := by
      intro d hd
      have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
      have hnd : n / d ≠ 0 := (Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)).ne'
      rw [lift_apply _ hd0]
      have : (d : ℤ) * ((n / d : ℕ) : ℤ) = n := by exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
      linear_combination (ArithmeticFunction.moebius (n / d)) * this
    rw [Finset.sum_congr rfl h2, ← Finset.mul_sum,
      Nat.sum_div_divisors n (fun d => ArithmeticFunction.moebius d), mu_sum,
      ArithmeticFunction.one_apply]
    split_ifs with h
    · subst h; simp
    · simp

lemma lift_zero' (f : ℕ → ℤ) : lift f 0 = 0 := by simp [lift]

lemma Kf_eq : lift (fun m : ℕ => 2 * (m : ℤ) - (sigma 1 m : ℤ)) = I + I - S := by
  ext m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [lift_zero', sub_app, ArithmeticFunction.add_apply, I, S, lift_zero']; simp
  · simp only [sub_app, ArithmeticFunction.add_apply, I, S, lift_apply _ hm.ne']
    ring

lemma Mf_eq : lift (fun m : ℕ => 2 * (Nat.totient m : ℤ) - (m : ℤ)) = Φ + Φ - I := by
  ext m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [lift_zero', sub_app, ArithmeticFunction.add_apply, Φ, I, lift_zero']; simp
  · simp only [sub_app, ArithmeticFunction.add_apply, I, Φ, lift_apply _ hm.ne']
    ring

theorem sol_aux : type_of% @OMA.S_oeis_a323910.main := by
  intro a s B H e ha hs hB hH he n hn
  have E3 : S = I * ζ := I_zeta.symm
  have hA : lift a * lift (fun m : ℕ => 2 * (m : ℤ) - (sigma 1 m : ℤ)) = 1 :=
    rec_one a _ (by simp) ha.1 ha.2
  rw [Kf_eq] at hA
  have hE : lift e * lift (fun m : ℕ => 2 * (Nat.totient m : ℤ) - (m : ℤ)) = 1 :=
    rec_one e _ (by simp) he.1 he.2
  rw [Mf_eq] at hE
  have hAn : a n = lift a n := (lift_apply _ (by omega)).symm
  refine ⟨?_, ?_, ?_⟩
  · have E4 : lift s * S = 1 := by
      ext m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [lift]
      · have h1 : S = lift (fun n => (sigma 1 n : ℤ)) := rfl
        rw [h1, conv_apply _ _ hm.ne', ArithmeticFunction.one_apply]
        rw [← hs m hm]
        refine Finset.sum_congr rfl (fun d hd => ?_)
        rw [lift_apply _ (Nat.pos_of_mem_divisors hd).ne']
    have E2 := B_zeta B hB.1 hB.2
    have hX : (lift s * lift B) * (I + I - S) = 1 := by
      linear_combination (-(lift s * lift B) - lift s) * E3 + (-(lift s * I)) * E2 + E4
    have := congrArg (fun f : ArithmeticFunction ℤ => f n) (uniq1 _ _ _ hA hX)
    rw [hAn, ← this, conv_apply _ _ (by omega)]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    rw [lift_apply _ (Nat.pos_of_mem_divisors hd).ne']
  · have E2 := H_zeta H hH.1 hH.2
    have hX : (lift (fun n => (n : ℤ) * ArithmeticFunction.moebius n) * lift H) * (I + I - S) = 1 := by
      linear_combination (-(lift (fun n => (n : ℤ) * ArithmeticFunction.moebius n) * lift H)) * E3
        + (-(lift (fun n => (n : ℤ) * ArithmeticFunction.moebius n) * I)) * E2 + Mob_I
    have := congrArg (fun f : ArithmeticFunction ℤ => f n) (uniq1 _ _ _ hA hX)
    rw [hAn, ← this, conv_apply _ _ (by omega)]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    rw [lift_apply _ (Nat.pos_of_mem_divisors hd).ne']
  · have hk : I + I - S = ζ * (Φ + Φ - I) := by
      linear_combination (-2 : ArithmeticFunction ℤ) * Phi_zeta + (-1 : ArithmeticFunction ℤ) * E3
    have E5 : (ArithmeticFunction.moebius : ArithmeticFunction ℤ) * ζ = 1 :=
      ArithmeticFunction.moebius_mul_coe_zeta
    have hX : (ArithmeticFunction.moebius * lift e) * (I + I - S) = 1 := by
      rw [hk]
      linear_combination (lift e * (Φ + Φ - I)) * E5 + hE
    have := congrArg (fun f : ArithmeticFunction ℤ => f n) (uniq1 _ _ _ hA hX)
    rw [hAn, ← this]
    have hmul : ∀ (P : ArithmeticFunction ℤ), (P * lift e) n = ∑ d ∈ n.divisors, P d * e (n / d) :=
      fun P => conv_apply P e (by omega)
    rw [hmul]

end OMA.S_oeis_a323910

theorem OMA.solution : type_of% @OMA.S_oeis_a323910.main := OMA.S_oeis_a323910.sol_aux
