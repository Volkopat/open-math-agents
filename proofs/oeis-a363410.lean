import OMAStatements.S_oeis_a363410
import Mathlib

/-!
# OEIS A363410: every prime divides a(n) for some n >= 1

Credit: @Squee451. The proof was found with Claude (claude-fable-5-2) and Codex; the Lean text was
written by Codex.

Outline. Write t = sqrt(-2), so t^2 = -2, and P(n) = Product_{k=1..n} (1 + k*t) = R(n) + B(n)*t with integers
R, B (R(n+1) = R(n) - 2(n+1)B(n), B(n+1) = B(n) + (n+1)R(n)); then a(n) = B(n). For an odd prime p
take n = p-1. Reindexing k -> p-k gives P(p-1) = Product (1 + (p-k)*t), and 1 + (p-k)*t = (1 - k*t)
+ p*t, so P(p-1) = conj(P(p-1)) + p*z for some z in Z[t]. Comparing t-coefficients, 2*B(p-1) =
p*(coefficient of z), so p divides 2*B(p-1) and hence B(p-1). (Equivalently: pair the factors k and
p-k, whose product is 1 - 2k(p-k) + p*t.) For p = 2: (1+t)(1+2t)(1+3t) = -21 - 6t, so a(3) = -6.
-/

open OMA.S_oeis_a363410

namespace OMA.A363410Proof

def P (n : ℕ) : Zsqrtd (-2) :=
  ∏ k ∈ Finset.Icc 1 n, (⟨1, k⟩ : Zsqrtd (-2))

lemma complex_root :
    ((Real.sqrt 2 : ℂ) * Complex.I) * ((Real.sqrt 2 : ℂ) * Complex.I) =
      ((-2 : ℤ) : ℂ) := by
  have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  calc
    _ = ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) *
        (Complex.I * Complex.I) := by ring
    _ = _ := by rw [hs, Complex.I_mul_I]; norm_num

lemma a_eq_im (n : ℕ) : a n = ((P n).im : ℝ) := by
  let φ : Zsqrtd (-2) →+* ℂ :=
    Zsqrtd.lift ⟨(Real.sqrt 2 : ℂ) * Complex.I, complex_root⟩
  have hprod : φ (P n) =
      ∏ k ∈ Finset.Icc 1 n, (1 + (k : ℂ) * (Real.sqrt 2 : ℂ) * Complex.I) := by
    simp only [P, map_prod]
    apply Finset.prod_congr rfl
    intro k hk
    simp [φ, Zsqrtd.lift, mul_assoc]
  have him : (φ (P n)).im = ((P n).im : ℝ) * Real.sqrt 2 := by
    simp [φ, Zsqrtd.lift]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  unfold a
  rw [← hprod, him, mul_div_cancel_right₀ _ hs]

lemma prod_add_multiple {α A : Type*} [CommRing A]
    (s : Finset α) (x y : α → A) (c : A) :
    ∃ z : A, (∏ k ∈ s, (x k + c * y k)) = (∏ k ∈ s, x k) + c * z := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert k s hk ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨x k * z + y k * (∏ j ∈ s, x j) + c * y k * z, ?_⟩
    simp only [Finset.prod_insert hk, hz]
    ring

lemma reflected (p : ℕ) :
    P (p - 1) = ∏ k ∈ Finset.Icc 1 (p - 1), (⟨1, (p - k : ℕ)⟩ : Zsqrtd (-2)) := by
  unfold P
  refine Finset.prod_bij (fun k _ => p - k) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · intro k hk l hl h
    simp only [Finset.mem_Icc] at hk hl
    omega
  · intro k hk
    refine ⟨p - k, ?_, ?_⟩
    · simp only [Finset.mem_Icc] at hk ⊢
      omega
    · simp only [Finset.mem_Icc] at hk
      omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    have h : p - (p - k) = k := by omega
    rw [h]

lemma conjugate_multiple (p : ℕ) :
    ∃ z : Zsqrtd (-2), P (p - 1) = star (P (p - 1)) + (p : Zsqrtd (-2)) * z := by
  obtain ⟨z, hz⟩ := prod_add_multiple (Finset.Icc 1 (p - 1))
    (fun k => (⟨1, -(k : ℤ)⟩ : Zsqrtd (-2)))
    (fun _ => (⟨0, 1⟩ : Zsqrtd (-2))) (p : Zsqrtd (-2))
  refine ⟨z, ?_⟩
  conv_lhs => rw [reflected]
  have heq : (∏ k ∈ Finset.Icc 1 (p - 1), (⟨1, (p - k : ℕ)⟩ : Zsqrtd (-2))) =
      ∏ k ∈ Finset.Icc 1 (p - 1),
        ((⟨1, -(k : ℤ)⟩ : Zsqrtd (-2)) + (p : Zsqrtd (-2)) * ⟨0, 1⟩) := by
    apply Finset.prod_congr rfl
    intro k hk
    have hk' : k ≤ p := by simp only [Finset.mem_Icc] at hk; omega
    ext <;> simp [Nat.cast_sub hk', sub_eq_add_neg, add_comm]
  rw [heq, hz]
  congr 1
  simp [P, star_prod]

lemma prime_dvd_im (p : ℕ) (hp : p.Prime) (hne : p ≠ 2) :
    (p : ℤ) ∣ (P (p - 1)).im := by
  obtain ⟨z, hz⟩ := conjugate_multiple p
  have hi := congrArg Zsqrtd.im hz
  simp only [Zsqrtd.im_add, Zsqrtd.im_star, Zsqrtd.im_mul,
    Zsqrtd.re_natCast, Zsqrtd.im_natCast, zero_mul, add_zero] at hi
  have hd : (p : ℤ) ∣ 2 * (P (p - 1)).im := ⟨z.im, by linarith⟩
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hprime.dvd_mul.mp hd with htwo | hB
  · have htwo' : p ∣ 2 := by exact_mod_cast htwo
    have : p = 2 := (Nat.dvd_prime Nat.prime_two).mp htwo' |>.resolve_left hp.ne_one
    exact (hne this).elim
  · exact hB

lemma im_three : (P 3).im = -6 := by
  decide +kernel

end OMA.A363410Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a363410.main := by
  intro p hp
  by_cases htwo : p = 2
  · subst p
    refine ⟨3, by omega, -3, ?_⟩
    rw [OMA.A363410Proof.a_eq_im, OMA.A363410Proof.im_three]
    norm_num
  · obtain ⟨q, hq⟩ := OMA.A363410Proof.prime_dvd_im p hp htwo
    refine ⟨p - 1, by have := hp.two_le; omega, q, ?_⟩
    rw [OMA.A363410Proof.a_eq_im, hq]
    push_cast
    rfl
