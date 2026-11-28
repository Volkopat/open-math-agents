import OMAStatements.S_oeis_a301311
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a301311

open OMA.S_oeis_a301311

/-- Forward difference operator on `ℤ → ℤ`. -/
private def Δ (f : ℤ → ℤ) : ℤ → ℤ := fun n => f (n + 1) - f n

/-- Iterated forward difference `Δ^k f`. -/
private def fwdDiff : ℕ → (ℤ → ℤ) → (ℤ → ℤ)
  | 0, f => f
  | k + 1, f => fwdDiff k (Δ f)

/-- Shift operator `(shift f)(n) = f(n + 1)`. -/
private def shift (f : ℤ → ℤ) : ℤ → ℤ := fun n => f (n + 1)

/-- Reflection operator `(ref f)(n) = f(-n)`. -/
private def ref (f : ℤ → ℤ) : ℤ → ℤ := fun n => f (-n)

private lemma fwdDiff_succ_right (k : ℕ) (f : ℤ → ℤ) :
    fwdDiff (k + 1) f = Δ (fwdDiff k f) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih => exact ih (Δ f)

private lemma fwdDiff_zero_fun (k : ℕ) : fwdDiff k (fun _ => (0 : ℤ)) = fun _ => 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : Δ (fun _ => (0 : ℤ)) = fun _ => 0 := by ext n; simp [Δ]
    rw [fwdDiff, h, ih]

private lemma fwdDiff_eq_zero_of_le {k m : ℕ} (hkm : k ≤ m) {f : ℤ → ℤ}
    (hf : fwdDiff k f = fun _ => 0) : fwdDiff m f = fun _ => 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hkm
  clear hkm
  induction r with
  | zero => simpa using hf
  | succ r ih =>
    rw [← Nat.add_assoc, fwdDiff_succ_right, ih]
    ext n; simp [Δ]

private lemma fwdDiff_add (k : ℕ) (f g : ℤ → ℤ) :
    fwdDiff k (fun n => f n + g n) = fun n => fwdDiff k f n + fwdDiff k g n := by
  induction k generalizing f g with
  | zero => rfl
  | succ k ih =>
    have h : Δ (fun n => f n + g n) = fun n => Δ f n + Δ g n := by ext n; dsimp [Δ]; ring
    rw [fwdDiff, h, ih]
    rfl

private lemma fwdDiff_sub (k : ℕ) (f g : ℤ → ℤ) :
    fwdDiff k (fun n => f n - g n) = fun n => fwdDiff k f n - fwdDiff k g n := by
  induction k generalizing f g with
  | zero => rfl
  | succ k ih =>
    have h : Δ (fun n => f n - g n) = fun n => Δ f n - Δ g n := by ext n; dsimp [Δ]; ring
    rw [fwdDiff, h, ih]
    rfl

private lemma fwdDiff_const_mul (k : ℕ) (c : ℤ) (f : ℤ → ℤ) :
    fwdDiff k (fun n => c * f n) = fun n => c * fwdDiff k f n := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    have h : Δ (fun n => c * f n) = fun n => c * Δ f n := by ext n; dsimp [Δ]; ring
    rw [fwdDiff, h, ih]
    rfl

private lemma fwdDiff_shift (k : ℕ) (f : ℤ → ℤ) :
    fwdDiff k (shift f) = shift (fwdDiff k f) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    have h : Δ (shift f) = shift (Δ f) := by ext n; rfl
    rw [fwdDiff, h, ih]
    rfl

private lemma fwdDiff_ref (k : ℕ) (f : ℤ → ℤ) :
    ∀ n : ℤ, fwdDiff k (ref f) n = (-1 : ℤ) ^ k * fwdDiff k f (-n - k) := by
  induction k generalizing f with
  | zero => intro n; simp [fwdDiff, ref]
  | succ k ih =>
    intro n
    have hstep' : Δ (ref f) = fun x => (-1 : ℤ) * ref (fun t => Δ f (t - 1)) x := by
      ext x; dsimp [Δ, ref]; ring
    rw [fwdDiff, hstep', fwdDiff_const_mul]
    dsimp only
    rw [ih]
    have hshift : ∀ m : ℕ, ∀ g : ℤ → ℤ, ∀ x : ℤ,
        fwdDiff m (fun t => g (t - 1)) x = fwdDiff m g (x - 1) := by
      intro m
      induction m with
      | zero => intro g x; rfl
      | succ m ihm =>
        intro g x
        have hd : Δ (fun t => g (t - 1)) = fun t => Δ g (t - 1) := by
          ext t; dsimp [Δ]; ring_nf
        rw [fwdDiff, hd, ihm]
        rfl
    rw [hshift k (Δ f) (-n - k)]
    have harg : -n - (k : ℤ) - 1 = -n - ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [harg, pow_succ', mul_assoc]
    rfl

private lemma fwdDiff_pow_le_eq_zero :
    ∀ d : ℕ, ∀ j : ℕ, j ≤ d → fwdDiff (d + 1) (fun n : ℤ => n ^ j) = fun _ => 0 := by
  intro d
  induction d with
  | zero =>
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    ext n; simp [fwdDiff, Δ]
  | succ d ih =>
    intro j hj
    rcases eq_or_lt_of_le hj with rfl | hlt
    · have hΔ : Δ (fun n : ℤ => n ^ (d + 1)) =
          fun n => ∑ i ∈ Finset.range (d + 1), ((d + 1).choose i : ℤ) * n ^ i := by
        ext n
        dsimp [Δ]
        rw [add_pow, Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, one_pow, mul_one,
          mul_one, add_sub_cancel_right]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [one_pow, mul_one, mul_comm]
      rw [fwdDiff, hΔ]
      have hlin : ∀ (s : Finset ℕ) (c : ℕ → ℤ),
          (∀ i ∈ s, fwdDiff (d + 1) (fun n : ℤ => n ^ i) = fun _ => 0) →
          fwdDiff (d + 1) (fun n : ℤ => ∑ i ∈ s, c i * n ^ i) = fun _ => 0 := by
        intro s c hs
        induction s using Finset.induction with
        | empty => simp [fwdDiff_zero_fun]
        | insert a s ha ihs =>
          have hsum : (fun n : ℤ => ∑ i ∈ insert a s, c i * n ^ i) =
              fun n => c a * n ^ a + ∑ i ∈ s, c i * n ^ i := by
            ext n; rw [Finset.sum_insert ha]
          rw [hsum, fwdDiff_add, fwdDiff_const_mul, hs a (Finset.mem_insert_self a s),
            ihs (fun i hi => hs i (Finset.mem_insert_of_mem hi))]
          ext n; simp
      exact hlin _ _ (fun i hi => ih i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
    · exact fwdDiff_eq_zero_of_le (Nat.le_succ _) (ih j (Nat.lt_succ_iff.mp hlt))

private lemma fwdDiff_poly_eq_zero (P : Polynomial ℤ) (d : ℕ) (hd : P.natDegree ≤ d) :
    fwdDiff (d + 1) (fun n : ℤ => P.eval n) = fun _ => 0 := by
  have heval : (fun n : ℤ => P.eval n) =
      fun n => ∑ i ∈ Finset.range (d + 1), P.coeff i * n ^ i := by
    ext n
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hd)]
  rw [heval]
  have hlin : ∀ (s : Finset ℕ) (c : ℕ → ℤ),
      (∀ i ∈ s, fwdDiff (d + 1) (fun n : ℤ => n ^ i) = fun _ => 0) →
      fwdDiff (d + 1) (fun n : ℤ => ∑ i ∈ s, c i * n ^ i) = fun _ => 0 := by
    intro s c hs
    induction s using Finset.induction with
    | empty => simp [fwdDiff_zero_fun]
    | insert a s ha ihs =>
      have hsum : (fun n : ℤ => ∑ i ∈ insert a s, c i * n ^ i) =
          fun n => c a * n ^ a + ∑ i ∈ s, c i * n ^ i := by
        ext n; rw [Finset.sum_insert ha]
      rw [hsum, fwdDiff_add, fwdDiff_const_mul, hs a (Finset.mem_insert_self a s),
        ihs (fun i hi => hs i (Finset.mem_insert_of_mem hi))]
      ext n; simp
  exact hlin _ _ (fun i hi => fwdDiff_pow_le_eq_zero d i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))

/-- Euler transform value `∑_{k=0}^d p^k (Δ^k f)(0)`. -/
private def eulerVal (p d : ℕ) (f : ℤ → ℤ) : ℤ :=
  ∑ k ∈ Finset.range (d + 1), (p : ℤ) ^ k * fwdDiff k f 0

private lemma eulerVal_sub (p d : ℕ) (f g : ℤ → ℤ) :
    eulerVal p d (fun n => f n - g n) = eulerVal p d f - eulerVal p d g := by
  simp only [eulerVal, fwdDiff_sub, mul_sub, Finset.sum_sub_distrib]

private lemma eulerVal_succ_of_zero {p d : ℕ} {f : ℤ → ℤ}
    (hf : fwdDiff (d + 1) f = fun _ => 0) :
    eulerVal p (d + 1) f = eulerVal p d f := by
  simp only [eulerVal, Finset.sum_range_succ, hf, mul_zero, add_zero]

private lemma eulerVal_rec {p d : ℕ} {f : ℤ → ℤ}
    (hf : fwdDiff (d + 1) f = fun _ => 0) :
    eulerVal p d f = f 0 + (p : ℤ) * eulerVal p d (Δ f) := by
  rw [← eulerVal_succ_of_zero hf]
  unfold eulerVal
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul, fwdDiff, Finset.mul_sum]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [pow_succ', mul_assoc]

private lemma eulerVal_shift_rec {p d : ℕ} {f : ℤ → ℤ}
    (hf : fwdDiff (d + 1) f = fun _ => 0) :
    ((p : ℤ) + 1) * eulerVal p d f - (p : ℤ) * eulerVal p d (shift f) = f 0 := by
  have hrec := eulerVal_rec (p := p) hf
  have hΔ : Δ f = fun n => shift f n - f n := rfl
  rw [hΔ, eulerVal_sub] at hrec
  linarith

private lemma dvd_eulerVal_add_shift {p d : ℕ} {f : ℤ → ℤ}
    (hf : fwdDiff (d + 1) f = fun _ => 0) :
    (2 * (p : ℤ) + 1) ∣ (eulerVal p d f + eulerVal p d (shift f) - 2 * f 0) := by
  have h := eulerVal_shift_rec (p := p) hf
  refine ⟨eulerVal p d (shift f) - eulerVal p d f, ?_⟩
  linarith

private lemma dvd_eulerVal_sub_shift_ref (p : ℕ) :
    ∀ d : ℕ, ∀ f : ℤ → ℤ, fwdDiff (d + 1) f = (fun _ => 0) →
      (2 * (p : ℤ) + 1) ∣ (eulerVal p d f - eulerVal p d (shift (ref f))) := by
  intro d
  induction d with
  | zero =>
    intro f hf
    have hconst : ∀ n : ℤ, f (n + 1) = f n := by
      intro n
      have h0 := congr_fun hf n
      dsimp [fwdDiff, Δ] at h0
      linarith
    have hf1 : f (-1) = f 0 := by
      have := hconst (-1)
      simpa using this.symm
    have hval : eulerVal p 0 f - eulerVal p 0 (shift (ref f)) = 0 := by
      simp [eulerVal, fwdDiff, shift, ref, hf1]
    rw [hval]
    exact dvd_zero _
  | succ d ih =>
    intro f hf
    have hΔf : fwdDiff (d + 1) (Δ f) = fun _ => 0 := hf
    have hSf : fwdDiff (d + 2) (shift f) = fun _ => 0 := by
      rw [fwdDiff_shift, hf]; rfl
    have hrf : fwdDiff (d + 2) (ref f) = fun _ => 0 := by
      ext n; rw [fwdDiff_ref, hf]; simp
    have hSrf : fwdDiff (d + 2) (shift (ref f)) = fun _ => 0 := by
      rw [fwdDiff_shift, hrf]; rfl
    have hih : (2 * (p : ℤ) + 1) ∣ (eulerVal p d (Δ f) - eulerVal p d (shift (ref (Δ f)))) :=
      ih (Δ f) hΔf
    have hΔ_sref : fwdDiff (d + 1) (shift (ref (Δ f))) = fun _ => 0 := by
      rw [fwdDiff_shift]
      ext n; dsimp [shift]; rw [fwdDiff_ref, hΔf]; simp
    have hih' : (2 * (p : ℤ) + 1) ∣
        (eulerVal p (d + 1) (Δ f) - eulerVal p (d + 1) (shift (ref (Δ f)))) := by
      rw [eulerVal_succ_of_zero hΔf, eulerVal_succ_of_zero hΔ_sref]
      exact hih
    -- Note `shift (ref (Δ f)) = fun n => ref f n - shift (ref f) n`!
    have hsrΔ : shift (ref (Δ f)) = fun n => ref f n - shift (ref f) n := by
      ext n
      dsimp [shift, ref, Δ]
      have h1 : -(n + 1) + 1 = -n := by ring
      rw [h1]
    have hΔ_eq : eulerVal p (d + 1) (Δ f) =
        eulerVal p (d + 1) (shift f) - eulerVal p (d + 1) f :=
      eulerVal_sub p (d + 1) (shift f) f
    have hsrΔ_eq : eulerVal p (d + 1) (shift (ref (Δ f))) =
        eulerVal p (d + 1) (ref f) - eulerVal p (d + 1) (shift (ref f)) := by
      rw [hsrΔ]; exact eulerVal_sub p (d + 1) (ref f) (shift (ref f))
    rw [hΔ_eq, hsrΔ_eq] at hih'
    have h1 := dvd_eulerVal_add_shift (p := p) hf
    have h2 := dvd_eulerVal_add_shift (p := p) hrf
    have href0 : ref f 0 = f 0 := by simp [ref]
    rw [href0] at h2
    have h2K : (2 * (p : ℤ) + 1) ∣ (2 * (eulerVal p (d + 1) f - eulerVal p (d + 1) (shift (ref f)))) := by
      have hcomb := dvd_sub (dvd_sub h1 h2) hih'
      have heq : 2 * (eulerVal p (d + 1) f - eulerVal p (d + 1) (shift (ref f))) =
          ((eulerVal p (d + 1) f + eulerVal p (d + 1) (shift f) - 2 * f 0) -
            (eulerVal p (d + 1) (ref f) + eulerVal p (d + 1) (shift (ref f)) - 2 * f 0)) -
          ((eulerVal p (d + 1) (shift f) - eulerVal p (d + 1) f) -
            (eulerVal p (d + 1) (ref f) - eulerVal p (d + 1) (shift (ref f)))) := by ring
      rw [heq]
      exact hcomb
    have hcop : IsCoprime (2 * (p : ℤ) + 1) 2 := ⟨-1, (p : ℤ) + 1, by ring⟩
    exact hcop.dvd_of_dvd_mul_left h2K

private lemma dvd_eulerVal_even {p d : ℕ} {f : ℤ → ℤ}
    (hf : fwdDiff (d + 1) f = fun _ => 0)
    (heven : ref f = f) (h0 : f 0 = 0) :
    ((p : ℤ) * (2 * (p : ℤ) + 1)) ∣ eulerVal p d f := by
  have hdvd_p : (p : ℤ) ∣ eulerVal p d f := by
    unfold eulerVal
    rw [Finset.sum_range_succ']
    simp only [pow_zero, one_mul, fwdDiff, h0, add_zero]
    refine Finset.dvd_sum (fun k _ => ?_)
    rw [pow_succ', mul_assoc]
    exact dvd_mul_right _ _
  have hdvd_M : (2 * (p : ℤ) + 1) ∣ eulerVal p d f := by
    have h1 := dvd_eulerVal_add_shift (p := p) hf
    rw [h0, mul_zero, sub_zero] at h1
    have h2 := dvd_eulerVal_sub_shift_ref p d f hf
    rw [heven] at h2
    have h2A : (2 * (p : ℤ) + 1) ∣ (2 * eulerVal p d f) := by
      have hcomb := dvd_add h1 h2
      have heq : 2 * eulerVal p d f =
          (eulerVal p d f + eulerVal p d (shift f)) +
          (eulerVal p d f - eulerVal p d (shift f)) := by ring
      rw [heq]
      exact hcomb
    have hcop : IsCoprime (2 * (p : ℤ) + 1) 2 := ⟨-1, (p : ℤ) + 1, by ring⟩
    exact hcop.dvd_of_dvd_mul_left h2A
  have hcop : IsCoprime (p : ℤ) (2 * (p : ℤ) + 1) := ⟨-2, 1, by ring⟩
  exact hcop.mul_dvd hdvd_p hdvd_M

/-- Every `f : ℤ → ℤ` with `Δ^(d+1) f = 0` is polynomially bounded on `ℕ`, hence
`n ↦ f(n) * (p / (p + 1))^n` is summable. -/
private lemma summable_of_fwdDiff_zero (p : ℕ) :
    ∀ d : ℕ, ∀ f : ℤ → ℤ, fwdDiff (d + 1) f = (fun _ => 0) →
      Summable (fun n : ℕ => (f n : ℝ) * ((p : ℝ) / ((p : ℝ) + 1)) ^ n) := by
  have hr0 : (0 : ℝ) ≤ (p : ℝ) / ((p : ℝ) + 1) := by positivity
  have hr1 : (p : ℝ) / ((p : ℝ) + 1) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  have hnorm : ‖(p : ℝ) / ((p : ℝ) + 1)‖ < 1 := by
    rw [Real.norm_of_nonneg hr0]; exact hr1
  have hpoly_bound : ∀ d : ℕ, ∀ f : ℤ → ℤ, fwdDiff (d + 1) f = (fun _ => 0) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ‖(f n : ℝ)‖ ≤ C * ((n : ℝ) + 1) ^ d := by
    intro d
    induction d with
    | zero =>
      intro f hf
      have hconst : ∀ n : ℕ, f n = f 0 := by
        intro n
        induction n with
        | zero => rfl
        | succ n ihn =>
          have h0 := congr_fun hf n
          dsimp [fwdDiff, Δ] at h0
          push_cast; linarith
      refine ⟨‖(f 0 : ℝ)‖, norm_nonneg _, fun n => ?_⟩
      rw [hconst n, pow_zero, mul_one]
    | succ d ih =>
      intro f hf
      obtain ⟨C, hC0, hC⟩ := ih (Δ f) hf
      refine ⟨‖(f 0 : ℝ)‖ + C, add_nonneg (norm_nonneg _) hC0, fun n => ?_⟩
      have htele : (f n : ℝ) = (f 0 : ℝ) + ∑ k ∈ Finset.range n, (Δ f k : ℝ) := by
        induction n with
        | zero => simp
        | succ n ihn =>
          rw [Finset.sum_range_succ, ← add_assoc, ← ihn]
          dsimp [Δ]; push_cast; ring
      rw [htele]
      have hsum_le : ‖∑ k ∈ Finset.range n, (Δ f k : ℝ)‖ ≤ C * (n : ℝ) * ((n : ℝ) + 1) ^ d := by
        calc ‖∑ k ∈ Finset.range n, (Δ f k : ℝ)‖
            ≤ ∑ k ∈ Finset.range n, ‖(Δ f k : ℝ)‖ := norm_sum_le _ _
          _ ≤ ∑ k ∈ Finset.range n, C * ((k : ℝ) + 1) ^ d :=
              Finset.sum_le_sum (fun k _ => hC k)
          _ ≤ ∑ _k ∈ Finset.range n, C * ((n : ℝ) + 1) ^ d := by
              refine Finset.sum_le_sum (fun k hk => ?_)
              have hkn : (k : ℝ) ≤ n := Nat.cast_le.mpr (le_of_lt (Finset.mem_range.mp hk))
              exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) d) hC0
          _ = C * (n : ℝ) * ((n : ℝ) + 1) ^ d := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ (d + 1) := one_le_pow₀ (by linarith)
      calc ‖(f 0 : ℝ) + ∑ k ∈ Finset.range n, (Δ f k : ℝ)‖
          ≤ ‖(f 0 : ℝ)‖ + ‖∑ k ∈ Finset.range n, (Δ f k : ℝ)‖ := norm_add_le _ _
        _ ≤ ‖(f 0 : ℝ)‖ * ((n : ℝ) + 1) ^ (d + 1) + C * (n : ℝ) * ((n : ℝ) + 1) ^ d := by
            have := mul_le_mul_of_nonneg_left h1 (norm_nonneg (f 0 : ℝ))
            linarith
        _ ≤ ‖(f 0 : ℝ)‖ * ((n : ℝ) + 1) ^ (d + 1) + C * ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ d := by
            have : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
            have hpow : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ d := by positivity
            nlinarith
        _ = (‖(f 0 : ℝ)‖ + C) * ((n : ℝ) + 1) ^ (d + 1) := by rw [pow_succ']; ring
  intro d f hf
  obtain ⟨C, hC0, hC⟩ := hpoly_bound d f hf
  have hsum_maj : Summable (fun n : ℕ =>
      C * (((n : ℝ) + 1) ^ d * ((p : ℝ) / ((p : ℝ) + 1)) ^ n)) := by
    have hpow : Summable (fun n : ℕ =>
        ∑ j ∈ Finset.range (d + 1), (d.choose j : ℝ) * ((n : ℝ) ^ j * ((p : ℝ) / ((p : ℝ) + 1)) ^ n)) := by
      refine summable_sum (fun j _ => ?_)
      exact (summable_pow_mul_geometric_of_norm_lt_one j hnorm).mul_left _
    have heq : (fun n : ℕ => C * (((n : ℝ) + 1) ^ d * ((p : ℝ) / ((p : ℝ) + 1)) ^ n)) =
        fun n : ℕ => C * ∑ j ∈ Finset.range (d + 1),
          (d.choose j : ℝ) * ((n : ℝ) ^ j * ((p : ℝ) / ((p : ℝ) + 1)) ^ n) := by
      ext n
      congr 1
      rw [add_pow, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [one_pow, mul_one]; ring
    rw [heq]
    exact hpow.mul_left C
  refine Summable.of_norm_bounded hsum_maj (fun n => ?_)
  rw [norm_mul, norm_pow, Real.norm_of_nonneg hr0, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hC n) (pow_nonneg hr0 n)

private lemma hasSum_eulerVal (p : ℕ) :
    ∀ d : ℕ, ∀ f : ℤ → ℤ, fwdDiff (d + 1) f = (fun _ => 0) →
      HasSum (fun n : ℕ => (p : ℝ) ^ n * (f n : ℝ) / ((p : ℝ) + 1) ^ (n + 1))
        (eulerVal p d f : ℝ) := by
  have hq : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  have hr0 : (0 : ℝ) ≤ (p : ℝ) / ((p : ℝ) + 1) := by positivity
  have hr1 : (p : ℝ) / ((p : ℝ) + 1) < 1 := by rw [div_lt_one hq]; linarith
  intro d
  induction d with
  | zero =>
    intro f hf
    have hconst : ∀ n : ℕ, f n = f 0 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ihn =>
        have h0 := congr_fun hf n
        dsimp [fwdDiff, Δ] at h0
        push_cast; linarith
    have hgeom := hasSum_geometric_of_lt_one hr0 hr1
    have hmul := hgeom.mul_left ((f 0 : ℝ) / ((p : ℝ) + 1))
    have hval : (f 0 : ℝ) / ((p : ℝ) + 1) * (1 - (p : ℝ) / ((p : ℝ) + 1))⁻¹ =
        (eulerVal p 0 f : ℝ) := by
      have he0 : eulerVal p 0 f = f 0 := by simp [eulerVal, fwdDiff]
      rw [he0]
      have h1 : 1 - (p : ℝ) / ((p : ℝ) + 1) = 1 / ((p : ℝ) + 1) := by field_simp; ring
      rw [h1, one_div, inv_inv, div_mul_cancel₀ _ (ne_of_gt hq)]
    rw [hval] at hmul
    refine hmul.congr_fun (fun n => ?_)
    rw [hconst n, div_pow, pow_succ]
    field_simp
  | succ d ih =>
    intro f hf
    have hΔ := ih (Δ f) hf
    let a : ℕ → ℝ := fun n => (f n : ℝ) * ((p : ℝ) / ((p : ℝ) + 1)) ^ n
    have hsum_a : Summable a := summable_of_fwdDiff_zero p (d + 1) f hf
    have ha0 : HasSum a (∑' n, a n) := hsum_a.hasSum
    have ha1 : HasSum (fun n => a (n + 1)) ((∑' n, a n) - a 0) := by
      have h := (hasSum_nat_add_iff' (f := a) 1).mpr ha0
      simpa using h
    have htele : HasSum (fun n => a n - a (n + 1)) (a 0) := by
      have h := ha0.sub ha1
      simpa using h
    have hcomb := htele.add (hΔ.mul_left (p : ℝ))
    have hsum_eq : a 0 + (p : ℝ) * (eulerVal p d (Δ f) : ℝ) = (eulerVal p (d + 1) f : ℝ) := by
      have hrec := eulerVal_rec (p := p) hf
      have hrec' : eulerVal p (d + 1) f = f 0 + (p : ℝ) * eulerVal p d (Δ f) := by
        have := eulerVal_succ_of_zero (p := p) (d := d) (f := Δ f) hf
        -- Directly from `eulerVal_rec` at `d + 1`:
        have hstep := congr_arg (Int.cast (R := ℝ)) hrec
        push_cast at hstep
        rw [this] at hstep
        exact hstep
      dsimp [a]
      simp only [pow_zero, mul_one]
      exact hrec'.symm
    rw [hsum_eq] at hcomb
    refine hcomb.congr_fun (fun n => ?_)
    dsimp [a, Δ]
    push_cast
    rw [div_pow, div_pow, pow_succ, pow_succ]
    field_simp
    ring

private lemma choose_sq_add_fwdDiff_zero (m : ℕ) :
    fwdDiff (2 * m + 1) (fun z : ℤ => (Nat.choose (z.natAbs ^ 2 + m - 1) m : ℤ)) = fun _ => 0 := by
  let P : Polynomial ℤ := ∏ j ∈ Finset.range m, (Polynomial.X ^ 2 + Polynomial.C (j : ℤ))
  have hdeg : P.natDegree ≤ 2 * m := by
    calc P.natDegree
        ≤ ∑ j ∈ Finset.range m, (Polynomial.X ^ 2 + Polynomial.C (j : ℤ)).natDegree :=
          Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _j ∈ Finset.range m, 2 := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          exact le_trans (Polynomial.natDegree_add_le _ _) (by simp)
      _ = 2 * m := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring
  have hmul : (fun z : ℤ => (m.factorial : ℤ) * (Nat.choose (z.natAbs ^ 2 + m - 1) m : ℤ)) =
      fun z : ℤ => P.eval z := by
    ext z
    dsimp [P]
    rw [Polynomial.eval_prod]
    have hnat : (m.factorial : ℤ) * (Nat.choose (z.natAbs ^ 2 + m - 1) m : ℤ) =
        ((z.natAbs ^ 2 + m - 1).descFactorial m : ℤ) := by
      exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose (z.natAbs ^ 2 + m - 1) m).symm
    rw [hnat]
    have hdesc : ∀ k : ℕ, k ≤ m → ((z.natAbs ^ 2 + k - 1).descFactorial k : ℤ) =
        ∏ j ∈ Finset.range k, ((z ^ 2 : ℤ) + (j : ℤ)) := by
      intro k hk
      induction k with
      | zero => simp
      | succ k ih =>
        by_cases hk0 : k = 0
        · subst hk0
          simp
        · have heq1 : z.natAbs ^ 2 + (k + 1) - 1 = z.natAbs ^ 2 + k := by omega
          have heq2 : z.natAbs ^ 2 + k - 1 = z.natAbs ^ 2 + k - 1 := rfl
          rw [heq1, Finset.prod_range_succ, ← ih (by omega)]
          have hstep : (z.natAbs ^ 2 + k).descFactorial (k + 1) =
              (z.natAbs ^ 2 + k) * (z.natAbs ^ 2 + k - 1).descFactorial k := by
            have hsucc : z.natAbs ^ 2 + k = (z.natAbs ^ 2 + k - 1) + 1 := by omega
            conv_lhs => rw [hsucc]
            rw [Nat.succ_descFactorial_succ, ← hsucc]
          rw [hstep, Nat.cast_mul, mul_comm]
          congr 1
          push_cast
          simp
    simpa [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] using hdesc m le_rfl
  have h0 : fwdDiff (2 * m + 1)
      (fun z : ℤ => (m.factorial : ℤ) * (Nat.choose (z.natAbs ^ 2 + m - 1) m : ℤ)) =
      fun _ => 0 := by
    rw [hmul]; exact fwdDiff_poly_eq_zero P (2 * m) hdeg
  rw [fwdDiff_const_mul] at h0
  ext z
  have hz := congr_fun h0 z
  have hfac : (m.factorial : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  exact (mul_eq_zero.mp hz).resolve_left hfac

private lemma prove_a301311 (m : ℕ) (hm : 1 ≤ m) :
    ∃ k : ℕ, HasSum (fun n : ℕ => (2 : ℝ) ^ n * (Nat.choose (n ^ 2 + m - 1) m : ℝ) / (3 : ℝ) ^ (n + 1))
      ((10 * k : ℕ) : ℝ) := by
  let f : ℤ → ℤ := fun z => (Nat.choose (z.natAbs ^ 2 + m - 1) m : ℤ)
  have hf : fwdDiff (2 * m + 1) f = fun _ => 0 := choose_sq_add_fwdDiff_zero m
  have heven : ref f = f := by
    ext z; simp [ref, f]
  have hf0 : f 0 = 0 := by
    dsimp [f]; rw [Nat.choose_eq_zero_of_lt (by omega)]; rfl
  have hdvd : (10 : ℤ) ∣ eulerVal 2 (2 * m) f := by
    simpa using dvd_eulerVal_even (p := 2) hf heven hf0
  have hsum := hasSum_eulerVal 2 (2 * m) f hf
  have hsum' : HasSum (fun n : ℕ => (2 : ℝ) ^ n * (Nat.choose (n ^ 2 + m - 1) m : ℝ) / (3 : ℝ) ^ (n + 1))
      (eulerVal 2 (2 * m) f : ℝ) := by
    refine hsum.congr_fun (fun n => ?_)
    norm_num [f]
  have hnonneg : (0 : ℝ) ≤ (eulerVal 2 (2 * m) f : ℝ) :=
    hsum'.nonneg (fun n => by positivity)
  have heul_nn : 0 ≤ eulerVal 2 (2 * m) f := by exact_mod_cast hnonneg
  obtain ⟨q, hq⟩ := hdvd
  have hq_nn : 0 ≤ q := by omega
  refine ⟨q.toNat, ?_⟩
  have hcast : ((10 * q.toNat : ℕ) : ℝ) = (eulerVal 2 (2 * m) f : ℝ) := by
    rw [hq]
    have : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq_nn
    exact_mod_cast congr_arg (10 * ·) this
  rwa [hcast]

end OMA.P_oeis_a301311

theorem OMA.solution : type_of% @OMA.S_oeis_a301311.main :=
  OMA.P_oeis_a301311.prove_a301311
