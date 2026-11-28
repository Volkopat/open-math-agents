import FormalConjectures.OEIS.«115257»
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.IntervalCases

open Polynomial OeisA115257
namespace OMA.R_OeisA115257_conjecture_R1

lemma even_pos (q : Bool) (x : ℚ) (m : ℕ) :
    0 < (if q then polyQ (2*m) else polyP (2*m)).eval x := by
  let b (k : ℕ) : ℚ := Nat.centralBinom k

  have b_nonneg (k : ℕ) : 0 ≤ b k := by
    simp only [b]
    positivity

  have b_succ (k : ℕ) :
      b (k+1) = (2*(2*(k:ℚ)+1)/((k:ℚ)+1))*b k := by
    have h : ((k:ℚ)+1)*b (k+1) = 2*(2*(k:ℚ)+1)*b k := by
      simp only [b]
      exact_mod_cast Nat.succ_mul_centralBinom_succ k
    field_simp
    nlinarith [h]

  let terms (q : Bool) (t : ℚ) (k : ℕ) : ℚ :=
    b k ^ 2 * t^k / (if q then (k:ℚ)+1 else 1)

  have terms_nonneg (q : Bool) (t : ℚ) (ht : 0 ≤ t) (k : ℕ) :
      0 ≤ terms q t k := by
    cases q <;> simp [terms] <;> positivity

  let ratio (q : Bool) (t : ℚ) (k : ℕ) : ℚ :=
    4*(2*(k:ℚ)+1)^2*t/((k:ℚ)+1) / (if q then (k:ℚ)+2 else (k:ℚ)+1)

  have ratio_nonneg (q : Bool) (t : ℚ) (ht : 0 ≤ t) (k : ℕ) :
      0 ≤ ratio q t k := by
    cases q <;> simp [ratio] <;> positivity

  have terms_succ (q : Bool) (t : ℚ) (k : ℕ) :
      terms q t (k+1) = ratio q t k * terms q t k := by
    cases q <;> simp [terms, ratio, b_succ, pow_succ, Nat.cast_add, Nat.cast_one]
    all_goals
      field_simp
      <;> ring

  have ratio_mono (q : Bool) (t : ℚ) (ht : 0 ≤ t) (k : ℕ) :
      ratio q t k ≤ ratio q t (k+1) := by
    cases q
    · simp only [ratio, Bool.false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_one]
      rw [div_div, div_div]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hk : 0 ≤ (k:ℚ) := by positivity
      have h : 0 ≤ (4*(k:ℚ)^2 + 10*(k:ℚ) +5)*t := by positivity
      nlinarith
    · simp only [ratio, ↓reduceIte, Nat.cast_add, Nat.cast_one]
      rw [div_div, div_div]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have h : 0 ≤ (8*(k:ℚ)+6)*((k:ℚ)+2)*t := by positivity
      nlinarith

  have terms_convex (q : Bool) (t : ℚ) (ht : 0 ≤ t) (k : ℕ) :
      2*terms q t (k+1) ≤ terms q t k + terms q t (k+2) := by
    have h1 := terms_succ q t k
    have h2 := terms_succ q t (k+1)
    have h3 := ratio_mono q t ht k
    have h4 := terms_nonneg q t ht k
    have h5 := terms_nonneg q t ht (k+1)
    have h6 := mul_le_mul_of_nonneg_right h3 h5
    rw [← h2] at h6
    have h7 : 0 ≤ (ratio q t k - 1)^2 * terms q t k :=
      mul_nonneg (sq_nonneg _) h4
    rw [h1] at h6
    rw [h1]
    nlinarith

  have even_alt_sum_aux (u : ℕ → ℚ) (hc : ∀ k, 2*u (k+1) ≤ u k+u (k+2)) (m : ℕ) :
      u 0 + u (2*m) ≤ 2 * ∑ k ∈ Finset.range (2*m+1), (-1:ℚ)^k*u k := by
    induction m with
    | zero => simp
              linarith
    | succ m ih =>
      have hr : 2*(m+1)+1 = (2*m+1)+1+1 := by omega
      rw [hr, Finset.sum_range_succ, Finset.sum_range_succ]
      rw [show 2*m+1+1 = 2*m+2 by omega,
          pow_add, pow_add, pow_mul]
      norm_num
      rw [show 2*(m+1) = 2*m+2 by omega]
      have h := hc (2*m)
      linarith

  have terms_zero (q : Bool) (t : ℚ) : terms q t 0 = 1 := by
    cases q <;> simp [terms, b, Nat.centralBinom]

  have even_alt_sum_pos (q : Bool) (t : ℚ) (ht : 0 ≤ t) (m : ℕ) :
      0 < ∑ k ∈ Finset.range (2*m+1), (-1:ℚ)^k * terms q t k := by
    have h := even_alt_sum_aux (terms q t) (terms_convex q t ht) m
    rw [terms_zero] at h
    have hn := terms_nonneg q t ht (2*m)
    linarith

  have eval_terms (q : Bool) (t : ℚ) (n : ℕ) :
      (if q then polyQ n else polyP n).eval t =
        ∑ k ∈ Finset.range (n+1), terms q t k := by
    cases q <;> simp [polyQ, polyP, terms, b, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_pow]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [div_mul_eq_mul_div]

  have eval_neg_terms (q : Bool) (t : ℚ) (n : ℕ) :
      (if q then polyQ n else polyP n).eval (-t) =
        ∑ k ∈ Finset.range (n+1), (-1:ℚ)^k * terms q t k := by
    rw [eval_terms]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [terms]
    rw [show -t = (-1:ℚ)*t by ring, mul_pow]
    ring

  have polyPQ_even_pos (q : Bool) (x : ℚ) (m : ℕ) :
      0 < (if q then polyQ (2*m) else polyP (2*m)).eval x := by
    by_cases hx : 0 ≤ x
    · rw [eval_terms]
      have h0 : (0:ℕ) ∈ Finset.range (2*m+1) := by simp
      calc
        0 < 1 := by norm_num
        _ = terms q x 0 := (terms_zero q x).symm
        _ ≤ _ := Finset.single_le_sum (fun k hk => terms_nonneg q x hx k) h0
    · rw [show x = -(-x) by ring, eval_neg_terms]
      exact even_alt_sum_pos q (-x) (by linarith) m

  exact polyPQ_even_pos q x m

lemma coeff_family (q : Bool) (n i : ℕ) :
    (if q then polyQ n else polyP n).coeff i =
      if i ≤ n then (Nat.centralBinom i : ℚ)^2 / (if q then (i:ℚ)+1 else 1) else 0 := by
  cases q
  · change (polyP n).coeff i = _
    rw [polyP, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff,
      Bool.false_eq_true, if_false, div_one]
  · change (polyQ n).coeff i = _
    rw [polyQ, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff, if_true]

lemma coeff_top (q : Bool) (n : ℕ) :
    (if q then polyQ n else polyP n).coeff n ≠ 0 := by
  rw [coeff_family, if_pos (le_refl n)]
  have hb : (Nat.centralBinom n : ℚ) ≠ 0 := by exact_mod_cast Nat.centralBinom_ne_zero n
  apply div_ne_zero (pow_ne_zero 2 hb)
  cases q <;> simp <;> positivity

lemma even_no_linear_factor (q : Bool) (m : ℕ) (g : Polynomial ℚ)
    (hd : g.natDegree = 1) : ¬ g ∣ (if q then polyQ (2*m) else polyP (2*m)) := by
  intro h
  have hn : g ≠ 0 := by intro hg; simp [hg] at hd
  have hdegree : g.degree = 1 := by rw [degree_eq_natDegree hn, hd]; rfl
  obtain ⟨x, hx⟩ := exists_root_of_degree_eq_one hdegree
  obtain ⟨f, hf⟩ := h
  have hzero : (if q then polyQ (2*m) else polyP (2*m)).eval x = 0 := by
    rw [hf, eval_mul, hx.eq_zero, zero_mul]
  have hpos := even_pos q (x : ℚ) m
  rw [hzero] at hpos
  exact (lt_irrefl 0) hpos

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
lemma odd_no_root (q : Bool) (n : ℕ) (hn : 3 ≤ n) (ho : Odd n) (x : ℚ) :
    (if q then polyQ n else polyP n).eval x ≠ 0 := by
  let F (a : ℕ → ℚ) (x : ℚ) (n : ℕ) : ℚ :=
    Nat.rec (a 0) (fun k z => x*z + (-1)^(k+1)*a (k+1)) n
  have F_zero (a : ℕ → ℚ) (x : ℚ) : F a x 0 = a 0 := rfl
  have F_succ (a : ℕ → ℚ) (x : ℚ) (n : ℕ) : F a x (n+1) = x * F a x n + (-1)^(n+1)*a (n+1) := rfl

  have F_two (a : ℕ → ℚ) (x : ℚ) (m : ℕ) :
      F a x (2*m+2) = x^2 * F a x (2*m) - x * a (2*m+1) + a (2*m+2) := by
    rw [show 2*m+2 = (2*m+1)+1 by omega, F_succ a x (2*m+1), F_succ a x (2*m)]
    rw [show 2*m+2 = 2*(m+1) by omega,pow_mul]
    norm_num
    rw [pow_add, pow_mul]
    norm_num
    ring

  have odd_two (a : ℕ → ℚ) (x : ℚ) (m : ℕ) :
      F a x (2*m+3) = x^2 * F a x (2*m+1) + x * a (2*m+2) - a (2*m+3) := by
    rw [show 2*m+3 = (2*m+2)+1 by omega, F_succ a x (2*m+2), show 2*m+2=(2*m+1)+1 by omega, F_succ a x (2*m+1)]
    rw [show 2*m+3=2*(m+1)+1 by omega, show 2*m+2=2*(m+1) by omega]
    rw [pow_add]
    rw [pow_mul]
    norm_num
    ring

  have even_lower (a : ℕ → ℚ) (x : ℚ) (ha : ∀ k, 0 < a k)
      (h0 : a 0 = 1)
      (hc : ∀ k, (a (k+1))^2 ≤ a k * a (k+2)) (hx : 0 ≤ x) :
      ∀ m, x^(2*m) + a (2*m) ≤ 2 * F a x (2*m) := by
    intro m
    induction m with
    | zero => norm_num [F_zero,h0]
    | succ m ih =>
      rw [show 2*(m+1)=2*m+2 by omega, F_two]
      have hcx := hc (2*m)
      have hd : 0 ≤ x^2 * a (2*m) - 2*x*a (2*m+1) + a (2*m+2) := by
        have he : 0 ≤ (x * a (2*m) - a (2*m+1))^2 := sq_nonneg _
        have hf : 0 ≤ a (2*m) * a (2*m+2) - a (2*m+1)^2 := sub_nonneg.mpr hcx
        have hg : 0 ≤ a (2*m) * (x^2 * a (2*m) - 2*x*a (2*m+1) + a (2*m+2)) := by
          linarith only [he,hf]
        exact nonneg_of_mul_nonneg_right hg (ha _)
      have hh := mul_le_mul_of_nonneg_left ih (sq_nonneg x)
      rw [pow_add]
      nlinarith only [hd,hh]

  have even_pos (a : ℕ → ℚ) (x : ℚ) (ha : ∀ k, 0 < a k)
      (h0 : a 0 = 1)
      (hc : ∀ k, (a (k+1))^2 ≤ a k * a (k+2)) (hx : 0 ≤ x) (m : ℕ) :
      0 < F a x (2*m) := by
    have hl := even_lower a x ha h0 hc hx m
    have hp := pow_nonneg hx (2*m)
    have hk := ha (2*m)
    linarith

  have odd_large (a : ℕ → ℚ) (x : ℚ) (ha1 : a 0 = 1)
      (h : ∀ k, a (k+1) < x * a k) (hx : 0 ≤ x) (m : ℕ) :
      0 < F a x (2*m+1) := by
    induction m with
    | zero =>
      have hh := h 0
      simp [ha1] at hh
      simpa [F_zero,F_succ,ha1] using sub_pos.mpr hh
    | succ m ih =>
      rw [show 2*(m+1)+1=2*m+3 by omega, odd_two]
      have hp := mul_nonneg (sq_nonneg x) (le_of_lt ih)
      have hh := h (2*m+2)
      linarith

  have odd_after (a : ℕ → ℚ) (x : ℚ) (k m : ℕ) (hkm : k ≤ m)
      (h : ∀ j, k ≤ j → x * a (2*j+2) < a (2*j+3))
      (hbase : F a x (2*k+1) < 0) :
      F a x (2*m+1) < 0 := by
    induction m, hkm using Nat.le_induction with
    | base => exact hbase
    | succ j hj ih =>
      rw [show 2*(j+1)+1=2*j+3 by omega, odd_two]
      have hp := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) (le_of_lt ih)
      have hh := h j hj
      linarith


  let A (q : Bool) (n : ℕ) : ℚ :=
    (Nat.centralBinom n : ℚ)^2 / (if q then (n+1:ℚ) else 1)

  let R (q : Bool) (n : ℕ) : ℚ :=
    (2*(2*(n:ℚ)+1))^2 / ((n+1) * (if q then n+2 else n+1))

  have A_pos (q : Bool) (n : ℕ) : 0 < A q n := by
    have h : 0 < (Nat.centralBinom n : ℚ) := by exact_mod_cast Nat.centralBinom_pos n
    cases q <;> simp [A] <;> positivity

  have A_zero (q : Bool) : A q 0 = 1 := by cases q <;> norm_num [A]

  have A_R (q : Bool) (n : ℕ) : A q (n+1) = R q n * A q n := by
    have h : ((n:ℚ)+1) * (Nat.centralBinom (n+1) : ℚ) =
        2*(2*(n:ℚ)+1)*(Nat.centralBinom n : ℚ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    have hn : (0:ℚ) ≤ n := by positivity
    have h1 : (n:ℚ)+1 ≠ 0 := by positivity
    have h2 : (n:ℚ)+2 ≠ 0 := by positivity
    have hx : (Nat.centralBinom (n+1) : ℚ) =
        2*(2*(n:ℚ)+1)*(Nat.centralBinom n : ℚ)/(n+1) := by
      rw [eq_div_iff h1, mul_comm]; exact h
    cases q <;> simp [A,R,hx] <;> field_simp <;> ring

  have R_pos (q : Bool) (n : ℕ) : 0 < R q n := by
    cases q <;> simp [R] <;> positivity

  have R_lt16 (q : Bool) (n : ℕ) : R q n < 16 := by
    have hn : (0:ℚ) ≤ n := by positivity
    cases q <;> simp [R] <;> rw [div_lt_iff₀ (by positivity)] <;> nlinarith

  have R_gt15 (q : Bool) (n : ℕ) (hn : 40 ≤ n) : 15 < R q n := by
    have hn' : (40:ℚ) ≤ n := by exact_mod_cast hn
    have hsq := sq_nonneg ((n:ℚ)-40)
    cases q <;> simp [R] <;> rw [lt_div_iff₀ (by positivity)] <;> nlinarith

  have R_mono (q : Bool) (n : ℕ) : R q n ≤ R q (n+1) := by
    have hn : (0:ℚ) ≤ n := by positivity
    have h1 : (0:ℚ)<(n:ℚ)+1 := by positivity
    have h2 : (0:ℚ)<(n:ℚ)+2 := by positivity
    have h3 : (0:ℚ)<(n:ℚ)+3 := by positivity
    cases q <;> simp [R] <;> apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr <;> ring_nf <;> nlinarith [pow_nonneg hn 2, pow_nonneg hn 3]

  have A_logconv (q : Bool) (n : ℕ) : A q (n+1)^2 ≤ A q n * A q (n+2) := by
    have ha := A_pos q n
    have hb := A_pos q (n+1)
    have h := mul_le_mul_of_nonneg_right (R_mono q n)
      (mul_nonneg (le_of_lt ha) (le_of_lt hb))
    calc
      A q (n+1)^2 = R q n * (A q n * A q (n+1)) := by
        nth_rw 1 [pow_two, A_R q n]; ring
      _ ≤ R q (n+1) * (A q n * A q (n+1)) := h
      _ = A q n * A q (n+2) := by rw [A_R q (n+1)]; ring

  have A_even_pos (q : Bool) (m : ℕ) (x : ℚ) (hx : 0 ≤ x) :
      0 < F (A q) x (2*m) :=
    even_pos _ _ (A_pos q) (A_zero q) (A_logconv q) hx m

  have A_odd_large (q : Bool) (m : ℕ) (x : ℚ) (hx : 16 ≤ x) :
      0 < F (A q) x (2*m+1) := by
    apply odd_large _ _ (A_zero q) _ (by linarith)
    intro k
    rw [A_R]
    apply mul_lt_mul_of_pos_right _ (A_pos q k)
    exact lt_of_lt_of_le (R_lt16 q k) hx

  have A_odd_after (q : Bool) (m : ℕ) (x : ℚ) (hx : x ≤ 15) (k : ℕ)
      (hk : 20 ≤ k) (hkm : k ≤ m) (hbase : F (A q) x (2*k+1) < 0) :
      F (A q) x (2*m+1) < 0 := by
    apply odd_after _ _ k m hkm _ hbase
    intro j hj
    rw [A_R q (2*j+2)]
    apply mul_lt_mul_of_pos_right _ (A_pos q _)
    exact lt_of_le_of_lt hx (R_gt15 q _ (by omega))



  have R_monotone (q : Bool) : Monotone (R q) := monotone_nat_of_le_succ (R_mono q)

  have odd_pos_between (q : Bool) (x : ℚ) (hx : 0 < x) (m k : ℕ)
      (hm : 1 ≤ m) (hmk : m ≤ k) (h1 : 0 < F (A q) x 3)
      (hk : 0 < F (A q) x (2*k+1)) : 0 < F (A q) x (2*m+1) := by
    by_cases h : x ≤ R q (2*m+2)
    · by_contra! hn
      have haux : ∀ j, m ≤ j → F (A q) x (2*j+1) ≤ 0 := by
        intro j hj
        induction j,hj using Nat.le_induction with
        | base => exact hn
        | succ j hj ih =>
          rw [show 2*(j+1)+1=2*j+3 by omega, odd_two, show 2*j+3=(2*j+2)+1 by omega, A_R q (2*j+2)]
          have hR : x ≤ R q (2*j+2) := h.trans (R_monotone q (by omega))
          have hA := mul_le_mul_of_nonneg_right hR (A_pos q (2*j+2)).le
          have hp := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) ih
          linarith
      exact (not_lt_of_ge (haux k hmk)) hk
    · push_neg at h
      have haux : ∀ j, 1 ≤ j → j ≤ m → 0 < F (A q) x (2*j+1) := by
        intro j hj
        induction j,hj using Nat.le_induction with
        | base => intro _; simpa using h1
        | succ j hj ih =>
          intro hjm
          rw [show 2*(j+1)+1=2*j+3 by omega, odd_two, show 2*j+3=(2*j+2)+1 by omega, A_R q (2*j+2)]
          have hR : R q (2*j+2) < x := lt_of_le_of_lt (R_monotone q (by omega)) h
          have hA := mul_lt_mul_of_pos_right hR (A_pos q (2*j+2))
          have hp := mul_pos (pow_pos hx 2) (ih (by omega))
          linarith
      exact haux m hm le_rfl

  have odd_neg_after_ratio (q : Bool) (x : ℚ) (k m : ℕ) (hkm : k ≤ m)
      (hR : x < R q (2*k+2)) (hF : F (A q) x (2*k+1) < 0) :
      F (A q) x (2*m+1) < 0 := by
    apply odd_after _ _ k m hkm _ hF
    intro j hj
    rw [show 2*j+3=(2*j+2)+1 by omega, A_R q (2*j+2)]
    apply mul_lt_mul_of_pos_right _ (A_pos q (2*j+2))
    exact lt_of_lt_of_le hR (R_monotone q (by omega))

  let aZ (q : Bool) (n : ℕ) : ℤ :=
    (Nat.fast_choose (2*n) n)^2 / (if q then (n+1 : ℕ) else 1)

  have aZ_cast (q : Bool) (n : ℕ) : (aZ q n : ℚ) = A q n := by
    have hchoose : Nat.fast_choose (2*n) n = Nat.centralBinom n := by
      rw [Nat.fast_choose, ← Nat.choose_eq_descFactorial_div_factorial, Nat.centralBinom]
    -- Both quotients use natural division; the displayed denominator divides the numerator.
    cases q
    · simp [aZ, A, hchoose]
    · have hd : n+1 ∣ (Nat.centralBinom n)^2 := by
        simpa [pow_two] using dvd_mul_of_dvd_left (Nat.succ_dvd_centralBinom n) (Nat.centralBinom n)
      have he := Nat.div_mul_cancel hd
      have hc : (((Nat.centralBinom n)^2 / (n+1) : ℕ) : ℚ)*((n:ℚ)+1) = (Nat.centralBinom n : ℚ)^2 := by
        exact_mod_cast he
      simp only [aZ, hchoose, ↓reduceIte, Int.cast_natCast, A]
      exact (eq_div_iff (by positivity)).mpr hc

  let FZ (q : Bool) (x : ℤ) (n : ℕ) : ℤ :=
    Nat.rec (aZ q 0) (fun k z => x*z + (-1)^(k+1)*aZ q (k+1)) n
  have FZ_zero (q : Bool) (x : ℤ) : FZ q x 0 = aZ q 0 := rfl
  have FZ_succ (q : Bool) (x : ℤ) (n : ℕ) : FZ q x (n+1) = x*FZ q x n + (-1)^(n+1)*aZ q (n+1) := rfl

  have FZ_cast (q : Bool) (r : ℤ) (n : ℕ) : (Int.cast (R := ℚ) (FZ q r n)) = F (A q) (r:ℚ) n := by
    induction n with
    | zero => simp [FZ_zero,F_zero,aZ_cast]
    | succ n ih => simp [FZ_succ,F_succ,ih,aZ_cast]

  have FZ_nat_cast (q : Bool) (r n : ℕ) : (Int.cast (R := ℚ) (FZ q (r:ℤ) n)) = F (A q) (r:ℚ) n := by
    simpa only [Int.cast_natCast] using FZ_cast q (r:ℤ) n

  let threshold (q : Bool) (r : ℕ) : ℕ :=
    (if q then [1,1,1,1,2,2,3,4,6,7,10,15,22,39,95]
     else [1,1,1,1,1,1,1,2,3,4,5,7,11,20,48]).getD (r-1) 1

  have finite_cert (q : Bool) (r : ℕ) (hr1 : 1 ≤ r) (hr2 : r ≤ 15) :
      let k := threshold q r
      1 ≤ k ∧ FZ q r (2*k+1) < 0 ∧ (r:ℚ) < R q (2*k+2) ∧
        (k=1 ∨ (0 < FZ q r 3 ∧ 0 < FZ q r (2*(k-1)+1))) := by
    cases q <;> interval_cases r
    all_goals
      constructor
      · decide
      · constructor
        · decide
        · constructor
          · norm_num [R,threshold]
          · decide

  have odd_int_nonzero (q : Bool) (r m : ℕ) (hr : 0 < r) (hm : 1 ≤ m) :
      F (A q) (r:ℚ) (2*m+1) ≠ 0 := by
    by_cases hlarge : 16 ≤ r
    · exact ne_of_gt (A_odd_large q m r (by exact_mod_cast hlarge))
    · let k := threshold q r
      have hcert := finite_cert q r (by omega) (by omega)
      change 1 ≤ k ∧ FZ q r (2*k+1) < 0 ∧ (r:ℚ) < R q (2*k+2) ∧
        (k=1 ∨ (0 < FZ q r 3 ∧ 0 < FZ q r (2*(k-1)+1))) at hcert
      obtain ⟨hk, hneg, hR, hpos⟩ := hcert
      have hneg' : F (A q) (r:ℚ) (2*k+1) < 0 := by
        exact lt_of_eq_of_lt (FZ_nat_cast q r (2*k+1)).symm (Int.cast_lt_zero.mpr hneg)
      by_cases hm' : k ≤ m
      · exact ne_of_lt (odd_neg_after_ratio q r k m hm' hR hneg')
      · rcases hpos with h1 | ⟨hstart, hend⟩
        · omega
        · apply ne_of_gt (odd_pos_between q r (by exact_mod_cast hr) m (k-1) hm (by omega) _ _)
          · exact lt_of_lt_of_eq (Int.cast_pos.mpr hstart) (FZ_nat_cast q r 3)
          · exact lt_of_lt_of_eq (Int.cast_pos.mpr hend) (FZ_nat_cast q r (2*(k-1)+1))

  let S (q : Bool) (n : ℕ) : Polynomial ℤ :=
    Nat.rec 1 (fun k z => X*z+C ((-1)^(k+1)*aZ q (k+1))) n
  have S_zero (q : Bool) : S q 0 = 1 := rfl
  have S_succ (q : Bool) (n : ℕ) : S q (n+1) = X*S q n + C ((-1)^(n+1)*aZ q (n+1)) := rfl

  have S_monic (q : Bool) (n : ℕ) : (S q n).Monic := by
    induction n with
    | zero => simp [S_zero]
    | succ n ih =>
      rw [S_succ]
      have hM : ((X : Polynomial ℤ)*S q n).Monic := monic_X.mul ih
      apply hM.add_of_left
      apply lt_of_le_of_lt degree_C_le
      rw [degree_eq_natDegree hM.ne_zero, monic_X.natDegree_mul ih, natDegree_X]
      exact_mod_cast (by omega : 0 < 1 + (S q n).natDegree)

  have S_eval (q : Bool) (x : ℚ) (n : ℕ) : aeval x (S q n) = F (A q) x n := by
    induction n with
    | zero => simp [S_zero,F_zero,A_zero]
    | succ n ih => simp [S_succ,F_succ,ih,aZ_cast]


  have poly_eval_zero (q : Bool) (x : ℚ) : (if q then polyQ 0 else polyP 0).eval x = 1 := by
    cases q <;> norm_num [polyP,polyQ]

  have poly_eval_succ (q : Bool) (n : ℕ) (x : ℚ) :
    (if q then polyQ (n+1) else polyP (n+1)).eval x =
      (if q then polyQ n else polyP n).eval x + A q (n+1)*x^(n+1) := by
    cases q
    · change (polyP (n+1)).eval x = (polyP n).eval x + A false (n+1)*x^(n+1)
      rw [polyP, Finset.sum_range_succ, eval_add]
      simp [polyP,A,eval_mul,eval_X_pow]
    · change (polyQ (n+1)).eval x = (polyQ n).eval x + A true (n+1)*x^(n+1)
      rw [polyQ, Finset.sum_range_succ, eval_add]
      simp [polyQ,A,eval_mul,eval_X_pow]

  have poly_eval_nonneg_pos (q : Bool) (x : ℚ) (hx : 0 ≤ x) (n : ℕ) :
    0 < (if q then polyQ n else polyP n).eval x := by
    induction n with
    | zero => rw [poly_eval_zero]; norm_num
    | succ n ih =>
      rw [poly_eval_succ]
      exact add_pos_of_pos_of_nonneg ih (mul_nonneg (A_pos q _).le (pow_nonneg hx _))

  have F_eval (q : Bool) (x : ℚ) (hx : x ≠ 0) (n : ℕ) :
      F (A q) (-x⁻¹) n = (-x⁻¹)^n * (if q then polyQ n else polyP n).eval x := by
    induction n with
    | zero => simp [F_zero,A_zero,poly_eval_zero]
    | succ n ih =>
      rw [F_succ,ih,poly_eval_succ]
      have hpow : (-x⁻¹)^(n+1) * x^(n+1) = (-1:ℚ)^(n+1) := by
        rw [← mul_pow, neg_mul, inv_mul_cancel₀ hx]
      rw [mul_add, pow_succ' (-x⁻¹) n, mul_assoc] 
      -- Expand the terminal monomial and simplify by the inverse relation.
      rw [← mul_assoc (-x⁻¹) ((-x⁻¹)^n), ← pow_succ', mul_left_comm ((-x⁻¹)^(n+1)), hpow]
      ring

  have odd_rational_nonzero (q : Bool) (n : ℕ) (hn : 3 ≤ n) (ho : Odd n) (x : ℚ) :
    (if q then polyQ n else polyP n).eval x ≠ 0 := by
    intro hz
    have hxneg : x < 0 := by
      by_contra! hnonneg
      exact (ne_of_gt (poly_eval_nonneg_pos q x hnonneg n)) hz
    have hxn : x ≠ 0 := ne_of_lt hxneg
    let y : ℚ := -x⁻¹
    have hy : 0 < y := by dsimp [y]; exact neg_pos.mpr (inv_lt_zero.mpr hxneg)
    have hF : F (A q) y n = 0 := by
      rw [show y = -x⁻¹ by rfl, F_eval q x hxn, hz, mul_zero]
    obtain ⟨z, hzcast, _⟩ := exists_integer_of_is_root_of_monic (S_monic q n) (by rwa [S_eval])
    have hcast : y = (z:ℚ) := hzcast
    have hzp : 0 < z := by exact_mod_cast (hcast ▸ hy)
    let r := z.toNat
    have hrz : (r:ℤ) = z := Int.toNat_of_nonneg hzp.le
    have hr : 0 < r := by omega
    have hry : y = (r:ℚ) := by rw [hcast, ← hrz]; norm_num
    obtain ⟨m, hm⟩ := ho
    have hm1 : 1 ≤ m := by omega
    rw [hm,hry] at hF
    exact (odd_int_nonzero q r m hr hm1) hF

  exact odd_rational_nonzero q n hn ho x


namespace A115257Valuation

lemma central_val (n : ℕ) : (Nat.centralBinom n).factorization 2 = (Nat.digits 2 n).sum := by
  have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2*n by omega)
  rw [show 2*n-n=n by omega, ← Nat.centralBinom_eq_two_mul_choose] at h
  have h' := congrArg (fun x : ℕ => x.factorization 2) h
  simp only [Nat.factorization_mul (Nat.centralBinom_ne_zero n) (Nat.factorial_ne_zero n), Nat.factorization_mul (mul_ne_zero (Nat.centralBinom_ne_zero n) (Nat.factorial_ne_zero n)) (Nat.factorial_ne_zero n), Finsupp.coe_add, Pi.add_apply, Nat.factorization_factorial_mul Nat.prime_two] at h'
  have h'' := Nat.sub_one_mul_factorization_factorial (n := n) Nat.prime_two
  norm_num at h''
  have hd := Nat.digit_sum_le 2 n
  omega

lemma digit_sum_pos {n : ℕ} (hn : 0 < n) : 0 < (Nat.digits 2 n).sum := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [Nat.digits_def' (by decide) hn, List.sum_cons]
    by_cases h : n / 2 = 0
    · omega
    · have hlt : n / 2 < n := Nat.div_lt_self hn (by decide)
      have hp := ih (n/2) hlt (by omega)
      omega

lemma digit_sum_eq_one_iff (n : ℕ) : (Nat.digits 2 n).sum = 1 ↔ ∃ r : ℕ, n = 2^r := by
  constructor
  · induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hs
      have hn : 0 < n := by
        by_contra! h
        have : n = 0 := by omega
        simp [this] at hs
      rw [Nat.digits_def' (by decide) hn, List.sum_cons] at hs
      by_cases hq : n / 2 = 0
      · have : n = 1 := by omega
        exact ⟨0, by simpa using this⟩
      · have hqpos : 0 < n / 2 := by omega
        have hh := digit_sum_pos hqpos
        have h1 : (Nat.digits 2 (n / 2)).sum = 1 := by omega
        obtain ⟨r, hr⟩ := ih (n/2) (Nat.div_lt_self hn (by decide)) h1
        refine ⟨r+1, ?_⟩
        rw [pow_succ]
        omega
  · rintro ⟨r, rfl⟩
    have h := @Nat.digits_base_pow_mul 2 r 1 (by decide) (by decide)
    simpa using congrArg List.sum h

lemma central_val_pow (r : ℕ) : (Nat.centralBinom (2^r)).factorization 2 = 1 := by
  rw [central_val, digit_sum_eq_one_iff]
  exact ⟨r, rfl⟩

lemma central_val_between (r k : ℕ) (h1 : 2^r < k) (h2 : k < 2^(r+1)) :
    2 ≤ (Nat.centralBinom k).factorization 2 := by
  rw [central_val]
  have hp := digit_sum_pos (show 0 < k by omega)
  by_contra! h
  have hh : (Nat.digits 2 k).sum = 1 := by omega
  obtain ⟨s, hs⟩ := (digit_sum_eq_one_iff k).mp hh
  rw [hs] at h1 h2
  have hr : r < s := by
    by_contra! hh
    exact (not_lt_of_ge (Nat.pow_le_pow_right (by decide : 0 < 2) hh)) h1
  exact (not_lt_of_ge (Nat.pow_le_pow_right (by decide : 0 < 2) (show r+1 ≤ s by omega))) h2

end A115257Valuation


open Polynomial
namespace A115257Lift

lemma irreducible_of_reverse {p : Polynomial ℚ} (h0 : p.coeff 0 ≠ 0)
    (hirr : Irreducible p.reverse) : Irreducible p := by
  rw [irreducible_iff] at hirr ⊢
  constructor
  · intro hu
    have hd := natDegree_eq_zero_of_isUnit hu
    have he := eq_C_of_natDegree_eq_zero hd
    rw [he, reverse_C] at hirr
    exact hirr.1 (isUnit_C.mpr (IsUnit.mk0 _ h0))
  · intro a b hab
    have h0' : a.coeff 0 * b.coeff 0 ≠ 0 := by rwa [hab, mul_coeff_zero] at h0
    have ha : a.coeff 0 ≠ 0 := left_ne_zero_of_mul h0'
    have hb : b.coeff 0 ≠ 0 := right_ne_zero_of_mul h0'
    have hh : p.reverse = a.reverse * b.reverse := by rw [hab, reverse_mul_of_domain]
    rcases hirr.2 hh with h | h
    · left
      have hdeg := natDegree_eq_zero_of_isUnit h
      have htd : a.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (Or.inr ha)
      rw [reverse_natDegree, htd, Nat.sub_zero] at hdeg
      rw [eq_C_of_natDegree_eq_zero hdeg, isUnit_C]
      exact IsUnit.mk0 _ ha
    · right
      have hdeg := natDegree_eq_zero_of_isUnit h
      have htd : b.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (Or.inr hb)
      rw [reverse_natDegree, htd, Nat.sub_zero] at hdeg
      rw [eq_C_of_natDegree_eq_zero hdeg, isUnit_C]
      exact IsUnit.mk0 _ hb


lemma coeff_truncRat (a : ℕ → ℚ) (n i : ℕ) : (((fun (a : ℕ → ℚ) (n : ℕ) => ∑ k ∈ Finset.range (n+1), C (a k) * X ^ k) : (ℕ → ℚ) → ℕ → Polynomial ℚ) a n).coeff i = if i ≤ n then a i else 0 := by
  classical
  rw [finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Nat.lt_succ_iff]

lemma natDegree_truncRat (a : ℕ → ℚ) (n : ℕ) (ha : a n ≠ 0) : (((fun (a : ℕ → ℚ) (n : ℕ) => ∑ k ∈ Finset.range (n+1), C (a k) * X ^ k) : (ℕ → ℚ) → ℕ → Polynomial ℚ) a n).natDegree = n := by
  apply le_antisymm
  · rw [natDegree_le_iff_degree_le, degree_le_iff_coeff_zero]
    intro i hi
    rw [coeff_truncRat, if_neg (by exact_mod_cast not_le_of_gt hi)]
  · apply le_natDegree_of_ne_zero
    simp [coeff_truncRat, ha]


lemma coeff_revInt (a : ℕ → ℤ) (n i : ℕ) : (((fun (a : ℕ → ℤ) (n : ℕ) => ∑ i ∈ Finset.range (n+1), C (a (n-i)) * X ^ i) : (ℕ → ℤ) → ℕ → Polynomial ℤ) a n).coeff i = if i ≤ n then a (n-i) else 0 := by
  classical
  rw [finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Nat.lt_succ_iff]

lemma natDegree_revInt (a : ℕ → ℤ) (n : ℕ) (ha : a 0 = 1) : (((fun (a : ℕ → ℤ) (n : ℕ) => ∑ i ∈ Finset.range (n+1), C (a (n-i)) * X ^ i) : (ℕ → ℤ) → ℕ → Polynomial ℤ) a n).natDegree = n := by
  apply le_antisymm
  · rw [natDegree_le_iff_degree_le, degree_le_iff_coeff_zero]
    intro i hi
    rw [coeff_revInt, if_neg (by exact_mod_cast not_le_of_gt hi)]
  · apply le_natDegree_of_ne_zero
    simp [coeff_revInt, ha]

lemma monic_revInt (a : ℕ → ℤ) (n : ℕ) (ha : a 0 = 1) : (((fun (a : ℕ → ℤ) (n : ℕ) => ∑ i ∈ Finset.range (n+1), C (a (n-i)) * X ^ i) : (ℕ → ℤ) → ℕ → Polynomial ℤ) a n).Monic := by
  unfold Monic
  rw [leadingCoeff, natDegree_revInt _ _ ha, coeff_revInt]
  simp [ha]

lemma reverse_trunc_eq (a : ℕ → ℤ) (n : ℕ) (ha : a n ≠ 0) :
    (((fun (a : ℕ → ℚ) (n : ℕ) => ∑ k ∈ Finset.range (n+1), C (a k) * X ^ k) : (ℕ → ℚ) → ℕ → Polynomial ℚ) (fun k => (a k : ℚ)) n).reverse = (((fun (a : ℕ → ℤ) (n : ℕ) => ∑ i ∈ Finset.range (n+1), C (a (n-i)) * X ^ i) : (ℕ → ℤ) → ℕ → Polynomial ℤ) a n).map (Int.castRingHom ℚ) := by
  ext i
  have hdeg : (((fun (a : ℕ → ℚ) (n : ℕ) => ∑ k ∈ Finset.range (n+1), C (a k) * X ^ k) : (ℕ → ℚ) → ℕ → Polynomial ℚ) (fun k => (a k : ℚ)) n).natDegree = n := natDegree_truncRat _ _ (by exact_mod_cast ha)
  rw [coeff_reverse, hdeg, coeff_map, coeff_revInt]
  by_cases hi : i ≤ n
  · rw [revAt_le hi, coeff_truncRat, if_pos (by omega), if_pos hi]
    rfl
  · rw [if_neg hi, map_zero, revAt_eq_self_of_lt (Nat.lt_of_not_ge hi), coeff_truncRat, if_neg hi]

lemma trunc_irr_of_reverse_int (a : ℕ → ℤ) (n : ℕ) (ha : a 0 = 1) (han : a n ≠ 0)
    (hirr : Irreducible (((fun (a : ℕ → ℤ) (n : ℕ) => ∑ i ∈ Finset.range (n+1), C (a (n-i)) * X ^ i) : (ℕ → ℤ) → ℕ → Polynomial ℤ) a n)) : Irreducible (((fun (a : ℕ → ℚ) (n : ℕ) => ∑ k ∈ Finset.range (n+1), C (a k) * X ^ k) : (ℕ → ℚ) → ℕ → Polynomial ℚ) (fun k => (a k : ℚ)) n) := by
  apply irreducible_of_reverse (by simp [coeff_truncRat, ha])
  rw [reverse_trunc_eq a n han]
  exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast (monic_revInt a n ha).isPrimitive).mp hirr

end A115257Lift


open Polynomial

namespace BinomialIrredQ


private lemma eq_pow_add_two {f : ℤ[X]} (h : ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) f = X ^ f.natDegree) :
    ∃ U : ℤ[X], f = X ^ f.natDegree + C 2 * U := by
  have hd : C (2 : ℤ) ∣ f - X ^ f.natDegree := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    have h' := congrArg (fun p : (ZMod 2)[X] => p.coeff i) h
    rw [coeff_map, coeff_X_pow] at h'
    rw [coeff_sub, coeff_X_pow]
    change ((2 : ℕ) : ℤ) ∣ _
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero]
    simpa using sub_eq_zero.mpr h'
  obtain ⟨U, hU⟩ := hd
  exact ⟨U, sub_eq_iff_eq_add.mp hU |>.trans (add_comm _ _)⟩

private lemma red_eq_X_pow_of_mul {f g : ℤ[X]} {n : ℕ}
    (hf : f.Monic) (hg : g.Monic) (hfg : ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) (f*g) = X^n) :
    ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) f = X ^ f.natDegree ∧ ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) g = X ^ g.natDegree := by
  have hf' : (((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) f).Monic := hf.map _
  have hg' : (((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) g).Monic := hg.map _
  have hprod : ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) f * ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) g = X^n := by simpa [] using hfg
  have hd : (((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) f).natDegree + (((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) g).natDegree = n := by
    rw [← hf'.natDegree_mul hg', hprod, natDegree_X_pow]
  have ht : (((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) f).natTrailingDegree + (((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) g).natTrailingDegree = n := by
    rw [← natTrailingDegree_mul hf'.ne_zero hg'.ne_zero, hprod, natTrailingDegree_X_pow]
  have h1 := natTrailingDegree_le_natDegree (((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) f)
  have h2 := natTrailingDegree_le_natDegree (((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) g)
  have hf'' := hf'.eq_X_pow_iff_natTrailingDegree_eq_natDegree.mpr (by omega)
  have hg'' := hg'.eq_X_pow_iff_natTrailingDegree_eq_natDegree.mpr (by omega)
  simpa [hf.natDegree_map, hg.natDegree_map] using And.intro hf'' hg''

theorem criterion (m : ℕ) (hm : 2 ≤ m) (he : Even m) (H f : ℤ[X])
    (hf : f.Monic)
    (hdeg : f.natDegree = 2*m)
    (hform : f = X^(2*m) + C 2 * X^(2*m-1) + C 4 * H)
    (hc : ¬ (2 : ℤ) ∣ H.coeff 0)
    (hH : (2 : ℤ) ∣ H.coeff (m-1)) :
    Irreducible f := by
  rw [hf.irreducible_iff_natDegree]
  constructor
  · intro hh; simp [hh] at hdeg; omega
  · intro A B hA hB hAB
    by_contra! h
    obtain ⟨ha, hb⟩ := h
    have hsum : A.natDegree + B.natDegree = 2*m := by
      rw [← hA.natDegree_mul hB, hAB, hdeg]
    have htzero : (2 : (ZMod 2)[X]) = 0 := by
      exact CharP.cast_eq_zero _ 2
    have hfzero : (4 : (ZMod 2)[X]) = 0 := by
      calc
        (4 : (ZMod 2)[X]) = 2 * 2 := by norm_num
        _ = 0 := by rw [htzero, zero_mul]
    have hred : ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) (A*B) = X^(2*m) := by
      rw [hAB, hform]
      simp [htzero, hfzero]
    obtain ⟨hredA, hredB⟩ := red_eq_X_pow_of_mul hA hB hred
    obtain ⟨U, hU⟩ := eq_pow_add_two hredA
    obtain ⟨V, hV⟩ := eq_pow_add_two hredB
    have hconst : U.coeff 0 * V.coeff 0 = H.coeff 0 := by
      have hh := congrArg (fun P : ℤ[X] => P.coeff 0) hAB
      rw [hU, hV, hform] at hh
      simp [coeff_add, coeff_X_pow, coeff_C_mul, if_neg (by omega : 0 ≠ A.natDegree),
        if_neg (by omega : 0 ≠ B.natDegree), if_neg (by omega : 0 ≠ 2*m),
        if_neg (by omega : 0 ≠ 2*m-1), Nat.ne_of_gt (by omega : 0 < m)] at hh
      nlinarith
    have hU0 : (((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) U).coeff 0 ≠ 0 := by
      rw [coeff_map]
      intro hz
      have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (U.coeff 0) 2).mp hz
      exact hc (hconst ▸ dvd_mul_of_dvd_left hd _)
    have hV0 : (((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) V).coeff 0 ≠ 0 := by
      rw [coeff_map]
      intro hz
      have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (V.coeff 0) 2).mp hz
      exact hc (hconst ▸ dvd_mul_of_dvd_right hd _)
    have hident : X^A.natDegree * V + X^B.natDegree * U + C 2 * U * V =
        X^(2*m-1) + C 2 * H := by
      have hh := hAB
      rw [hU, hV, hform] at hh
      replace hh : C (2 : ℤ) * (X^A.natDegree * V + X^B.natDegree * U + C 2 * U * V) =
          C 2 * (X^(2*m-1) + C 2 * H) := by
        have hx : X^A.natDegree * X^B.natDegree = (X : ℤ[X])^(2*m) := by rw [← pow_add, hsum]
        have hC4 : C (4 : ℤ) = C 2 * C 2 := by rw [← C_mul]; norm_num
        rw [hC4] at hh
        linear_combination hh - hx
      exact mul_left_cancel₀ (by norm_num) hh
    have hredident : (X : (ZMod 2)[X])^A.natDegree * ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) V +
        X^B.natDegree * ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) U = X^(2*m-1) := by
      have hh := congrArg ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) hident
      simpa [htzero] using hh
    have heq : A.natDegree = B.natDegree := by
      rcases lt_trichotomy A.natDegree B.natDegree with hh | hh | hh
      · exfalso
        have hcoeff := congrArg (fun p : (ZMod 2)[X] => p.coeff A.natDegree) hredident
        simp [coeff_X_pow_mul', coeff_X_pow, hh.not_ge, if_neg (by omega : A.natDegree ≠ 2*m-1)] at hcoeff
        exact hV0 (by simpa using hcoeff)
      · exact hh
      · exfalso
        have hcoeff := congrArg (fun p : (ZMod 2)[X] => p.coeff B.natDegree) hredident
        simp [coeff_X_pow_mul', coeff_X_pow, hh.not_ge, if_neg (by omega : B.natDegree ≠ 2*m-1)] at hcoeff
        exact hU0 (by simpa using hcoeff)
    have hAm : A.natDegree = m := by omega
    have hBm : B.natDegree = m := by omega
    have hredsum : ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) U + ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) V = X^(m-1) := by
      rw [hAm, hBm, ← mul_add] at hredident
      have hx : (X : (ZMod 2)[X])^(2*m-1) = X^m * X^(m-1) := by rw [← pow_add]; congr 1; omega
      rw [hx] at hredident
      exact (add_comm _ _).trans (mul_left_cancel₀ (pow_ne_zero _ X_ne_zero) hredident)
    have hprod : (((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) U * ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) V).coeff (m-1) = 0 := by
      have hh := congrArg (fun p : ℤ[X] => p.coeff (m-1)) hident
      rw [hAm, hBm] at hh
      simp [coeff_add, coeff_X_pow_mul', coeff_X_pow, coeff_C_mul,
        if_neg (by omega : ¬ m ≤ m-1), if_neg (by omega : m-1 ≠ 2*m-1)] at hh
      rw [mul_assoc] at hh
      change (C (2 : ℤ) * (U*V)).coeff (m-1) = _ at hh
      rw [coeff_C_mul] at hh
      have hZ : (U*V).coeff (m-1) = H.coeff (m-1) := by nlinarith
      rw [← Polynomial.map_mul, coeff_map, hZ]
      change ((H.coeff (m-1) : ℤ) : ZMod 2) = 0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hH
    have hUsq : (((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) U * ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) U).coeff (m-1) = 0 := by
      rw [← pow_two, ← Polynomial.map_frobenius_expand (p := 2), coeff_map, coeff_expand (by norm_num : 0 < (2:ℕ))]
      have hodd : ¬ 2 ∣ m-1 := by
        obtain ⟨k, hk⟩ := he
        omega
      simp [hodd]
    have hlast : ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) U * ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) U + ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) U * ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) V = ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) U * X^(m-1) := by rw [← mul_add, hredsum]
    have hh := congrArg (fun p : (ZMod 2)[X] => p.coeff (m-1)) hlast
    simp [coeff_add, hUsq, hprod, coeff_mul_X_pow'] at hh
    exact hU0 (by simpa using hh.symm)

end BinomialIrredQ


open Polynomial

namespace BinomialPowerTwo

lemma eq_pow_of_monic_product_pow {K : Type*} [CommRing K] [IsDomain K]
    {A B : Polynomial K} (hA : A.Monic) (hB : B.Monic)
    {n : ℕ} (h : A * B = X ^ n) : A = X ^ A.natDegree ∧ B = X ^ B.natDegree := by
  have h₁ := natTrailingDegree_mul hA.ne_zero hB.ne_zero
  have h₂ := natDegree_mul hA.ne_zero hB.ne_zero
  rw [h, natTrailingDegree_X_pow] at h₁
  rw [h, natDegree_X_pow] at h₂
  have h₃ := natTrailingDegree_le_natDegree A
  have h₄ := natTrailingDegree_le_natDegree B
  exact ⟨(hA.eq_X_pow_iff_natTrailingDegree_eq_natDegree).2 (by omega),
         (hB.eq_X_pow_iff_natTrailingDegree_eq_natDegree).2 (by omega)⟩

lemma mod2_zero_iff (p : Polynomial ℤ) :
    p.map (Int.castRingHom (ZMod 2)) = 0 ↔ C 2 ∣ p := by
  rw [C_dvd_iff_dvd_coeff]
  constructor
  · intro h i
    have hh := congrArg (fun p : Polynomial (ZMod 2) => p.coeff i) h
    simp only [coeff_map, coeff_zero] at hh
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hh
  · intro h
    ext i
    simp only [coeff_map, coeff_zero]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (h i)

lemma low_square_mod4 {r : ℕ} (hr : 0 < r) (g : Polynomial ℤ)
    (hg : ∀ j, 0 < j → j < r → (2 : ℤ) ∣ g.coeff j) :
    ∀ i, 0 < i → i < 2*r →
    (4 : ℤ) ∣ (g*g).coeff i - 2*g.coeff 0*g.coeff i := by
  let s := g - C (g.coeff 0)
  let t := s %ₘ (X ^ r)
  let v := s /ₘ (X ^ r)
  have hst : t + X ^ r * v = s := modByMonic_add_div _ _
  have ht : C (2 : ℤ) ∣ t := by
    rw [C_dvd_iff_dvd_coeff]
    intro j
    by_cases hj : j < r
    · have hc := congrArg (fun p : Polynomial ℤ => p.coeff j) hst
      simp only [coeff_add, coeff_X_pow_mul', if_neg (show ¬ r ≤ j from by omega),
        add_zero, s, coeff_sub, coeff_C] at hc
      rw [hc]
      by_cases jz : j = 0
      · simp [jz]
      · simp [jz, hg j (by omega) hj]
    · have hlt : t.natDegree < r := by
        have hh := natDegree_modByMonic_lt s (monic_X_pow r) (by
          intro he; have := congrArg natDegree he; simp at this; omega)
        simpa [t] using hh
      rw [coeff_eq_zero_of_natDegree_lt (show t.natDegree < j by omega)]
      exact dvd_zero _
  obtain ⟨u,hu⟩ := ht
  have hs : g = C (g.coeff 0) + C 2 * u + X^r*v := by
    rw [← hu]
    calc
      g = C (g.coeff 0) + (g-C (g.coeff 0)) := by ring
      _ = _ := by
        dsimp [s] at hst
        rw [← hst]
        ring
  let z := g.coeff 0
  change g = C z + C 2 * u + X^r*v at hs
  have hid : g*g - C (2*g.coeff 0)*g + C (g.coeff 0)^2 =
      C 4*(u*u + u*(X^r*v)) + X^(2*r)*v^2 := by
    change g*g - C (2*z)*g + C z^2 = _
    rw [hs, show (X : ℤ[X])^(2*r) = (X^r)^2 by rw [mul_comm 2 r, pow_mul]]
    simp only [map_mul, map_ofNat]
    ring
  intro i hi him
  have hh := congrArg (fun p : Polynomial ℤ => p.coeff i) hid
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow_mul',
    if_neg (show ¬ 2*r ≤ i by omega), add_zero, ← map_pow, coeff_C,
    if_neg (show i ≠ 0 by omega)] at hh
  exact ⟨(u*u+u*(X^r*v)).coeff i, by rw [coeff_add]; exact hh⟩


private lemma red_coeff (f : ℤ[X]) (i : ℕ) : (((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) f).coeff i = f.coeff i := by
  simp [coeff_map]

private lemma red_add (f g : ℤ[X]) : ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) (f+g) = ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) f + ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) g := by simp []
private lemma red_mul (f g : ℤ[X]) : ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) (f*g) = ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) f * ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) g := by simp []

lemma eq_pow_add_two {f : ℤ[X]} (h : ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) f = X ^ f.natDegree) :
    ∃ U : ℤ[X], f = X ^ f.natDegree + C 2 * U := by
  have hd : C (2 : ℤ) ∣ f - X ^ f.natDegree := by
    rw [← mod2_zero_iff]
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X]
    change ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) f - X^f.natDegree = 0
    rw [h, sub_self]
  obtain ⟨U,hU⟩ := hd
  exact ⟨U,sub_eq_iff_eq_add.mp hU |>.trans (add_comm _ _)⟩

lemma red_eq_X_pow_of_mul {f g : ℤ[X]} {n : ℕ}
    (hf : f.Monic) (hg : g.Monic) (hfg : ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) (f*g) = X^n) :
    ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) f = X ^ f.natDegree ∧ ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) g = X ^ g.natDegree := by
  have hf' : (((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) f).Monic := hf.map _
  have hg' : (((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) g).Monic := hg.map _
  have hprod : ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) f * ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) g = X^n := by simpa [] using hfg
  have h := eq_pow_of_monic_product_pow hf' hg' hprod
  simpa [hf.natDegree_map, hg.natDegree_map] using h

lemma square_coeff_even (f : (ZMod 2)[X]) (j : ℕ) : (f^2).coeff (2*j) = f.coeff j := by
  have hchar : (2 : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero _ 2
  have hscalar : ∀ a : ZMod 2, a*a=a := by decide
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    simp [add_sq,hchar,coeff_add,hf,hg]
  | monomial i a =>
    rw [pow_two,monomial_mul_monomial,coeff_monomial,coeff_monomial]
    by_cases h:i=j
    · subst i
      simp [show j+j=2*j by omega,hscalar]
    · simp [h, show i+i ≠ 2*j by omega]

lemma square_coeff_odd (f : (ZMod 2)[X]) (j : ℕ) (hodd : ¬ 2 ∣ j) : (f^2).coeff j = 0 := by
  have hchar : (2 : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero _ 2
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    simp [add_sq,hchar,coeff_add,hf,hg]
  | monomial i a =>
    rw [pow_two,monomial_mul_monomial,coeff_monomial]
    exact if_neg (show i+i ≠ j by omega)

lemma coeff_mul_mod2_edges (f g : ℤ[X]) (i : ℕ) (hi : 0 < i)
    (hg : ∀ j, 0 < j → j < i → (2:ℤ) ∣ g.coeff j) :
    ((f*g).coeff i : ZMod 2) = (f.coeff i : ZMod 2)*(g.coeff 0 : ZMod 2) +
      (f.coeff 0 : ZMod 2)*(g.coeff i : ZMod 2) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Int.cast_sum]
  simp only [Int.cast_mul]
  have hs : ({0,i} : Finset ℕ) ⊆ Finset.range (i+1) := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl|rfl <;> simp
  rw [← Finset.sum_subset hs (by
    intro j hj hnot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    simp only [Finset.mem_range] at hj
    have hdiv := hg (i-j) (by omega) (by omega)
    have hz : (g.coeff (i-j) : ZMod 2)=0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdiv
    simp [hz])]
  rw [Finset.sum_pair (by omega : (0:ℕ) ≠ i)]
  simp [add_comm]

theorem criterion (m : ℕ) (hm : 2 ≤ m) (he : Even m) (f W : ℤ[X]) (hf : f.Monic)
    (hdeg : f.natDegree = 2*m) (hfW : f = X^(2*m) + C 4 * W)
    (hc : ∃ c : ℤ, ¬ (2:ℤ) ∣ c ∧ W.coeff 0 = c^2)
    (hlow : ∀ i, 0 < i → i < m → (4:ℤ) ∣ W.coeff i)
    (htop : ¬ (2:ℤ) ∣ W.coeff (2*m-1)) :
    Irreducible f := by
  rw [hf.irreducible_iff_natDegree]
  constructor
  · intro h; simp [h] at hdeg; omega
  · intro A B hA hB hAB
    by_contra! hab
    obtain ⟨ha,hb⟩ := hab
    have hsum : A.natDegree + B.natDegree = 2*m := by rw [←hA.natDegree_mul hB,hAB,hdeg]
    have htzero : (2 : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero _ 2
    have hfzero : (4 : (ZMod 2)[X]) = 0 := by
      rw [show (4 : (ZMod 2)[X]) = 2*2 by norm_num,htzero,zero_mul]
    have hred : ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) (A*B) = X^(2*m) := by
      rw [hAB,hfW]
      simp [htzero,hfzero]
    obtain ⟨hredA,hredB⟩ := red_eq_X_pow_of_mul hA hB hred
    obtain ⟨U,hU⟩ := eq_pow_add_two hredA
    obtain ⟨V,hV⟩ := eq_pow_add_two hredB
    have hconst : U.coeff 0 * V.coeff 0 = W.coeff 0 := by
      have hh := congrArg (fun p : ℤ[X] => p.coeff 0) hAB
      rw [hU,hV,hfW] at hh
      simp only [coeff_zero_eq_eval_zero,eval_mul,eval_add,eval_pow,eval_X,eval_C] at hh ⊢
      simp [zero_pow (show A.natDegree ≠ 0 by omega),zero_pow (show B.natDegree ≠ 0 by omega),
        zero_pow (show 2*m ≠ 0 by omega)] at hh
      nlinarith
    obtain ⟨c,hcodd,hcW⟩ := hc
    have hcodd' : ¬ (2:ℤ) ∣ W.coeff 0 := by
      intro hd; rw [hcW,pow_two] at hd
      have hcmod : c % 2 = 1 := by omega
      have hdd : (c*c) % 2 = 0 := by omega
      rw [Int.mul_emod c c 2, hcmod] at hdd
      norm_num at hdd
    have hU0 : ¬ (2:ℤ) ∣ U.coeff 0 := fun hd => hcodd' (hconst ▸ dvd_mul_of_dvd_left hd _)
    have hV0 : ¬ (2:ℤ) ∣ V.coeff 0 := fun hd => hcodd' (hconst ▸ dvd_mul_of_dvd_right hd _)
    have hU0r : (((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) U).coeff 0 ≠ 0 := by
      rw [red_coeff]
      exact fun hz => hU0 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hz)
    have hV0r : (((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) V).coeff 0 ≠ 0 := by
      rw [red_coeff]
      exact fun hz => hV0 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hz)
    have hident : X^A.natDegree * V + X^B.natDegree * U + C 2 * (U*V) = C 2 * W := by
      have hh := hAB
      rw [hU,hV,hfW] at hh
      have hh' : C (2:ℤ) * (X^A.natDegree * V + X^B.natDegree * U + C 2 * (U*V)) =
          C 2 * (C 2 * W) := by
        have hx : X^A.natDegree * X^B.natDegree = (X : ℤ[X])^(2*m) := by rw [←pow_add,hsum]
        have hC4 : C (4 : ℤ) = C 2 * C 2 := by rw [←C_mul]; norm_num
        rw [hC4] at hh
        linear_combination hh-hx
      exact mul_left_cancel₀ (by norm_num) hh'
    have hredident : (X : (ZMod 2)[X]) ^ A.natDegree * ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) V + X ^ B.natDegree * ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) U = 0 := by
      have hh := congrArg ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) hident
      simpa [htzero] using hh
    have heq : A.natDegree=B.natDegree := by
      rcases lt_trichotomy A.natDegree B.natDegree with hlt|heq|hgt
      · exfalso
        have hh := congrArg (fun p : (ZMod 2)[X] => p.coeff A.natDegree) hredident
        simp [coeff_X_pow_mul',hlt.not_ge] at hh
        exact hV0r (by simpa using hh)
      · exact heq
      · exfalso
        have hh := congrArg (fun p : (ZMod 2)[X] => p.coeff B.natDegree) hredident
        simp [coeff_X_pow_mul',hgt.not_ge] at hh
        exact hU0r (by simpa using hh)
    have hAm : A.natDegree=m := by omega
    have hBm : B.natDegree=m := by omega
    have hredsum : ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) (U+V) = 0 := by
      rw [red_add]
      rw [hAm,hBm,←mul_add] at hredident
      exact (add_comm _ _).trans ((mul_eq_zero.mp hredident).resolve_left (pow_ne_zero _ X_ne_zero))
    obtain ⟨Q,hQ⟩ := (mod2_zero_iff _).1 hredsum
    have hW : W = X^m*Q + U*V := by
      rw [hAm,hBm,←mul_add,add_comm V U,hQ] at hident
      have h' : C (2:ℤ) * (X^m*Q + U*V) = C 2 * W := by linear_combination hident
      exact (mul_left_cancel₀ (by norm_num) h').symm
    have hUeqV : ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) U = ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) V := by
      have hh := congrArg ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) hQ
      have hab : ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) U + ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) V=0 := by simpa [htzero] using hh
      linear_combination hab - (((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) V)*htzero
    have hredW : ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) W = X^m * ((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) Q + (((fun (f : ℤ[X]) => f.map (Int.castRingHom (ZMod 2))) : ℤ[X] → (ZMod 2)[X]) U)^2 := by
      simp only [hW,red_add,red_mul]
      change U.map (Int.castRingHom (ZMod 2)) = V.map (Int.castRingHom (ZMod 2)) at hUeqV
      rw [show map (Int.castRingHom (ZMod 2)) ((X : ℤ[X])^m) = (X : (ZMod 2)[X])^m by simp [], ← hUeqV,pow_two]
    have h_evenU : ∀ j, 0 < j → 2*j < m → (2:ℤ) ∣ U.coeff j := by
      intro j hj hjm
      have hh := congrArg (fun p : (ZMod 2)[X] => p.coeff (2*j)) hredW
      rw [coeff_add,coeff_X_pow_mul',if_neg (by omega : ¬ m≤2*j),zero_add,
        square_coeff_even] at hh
      rw [red_coeff,red_coeff] at hh
      have hdiv := dvd_trans (show (2:ℤ) ∣ 4 by decide) (hlow (2*j) (by omega) hjm)
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (hh.symm.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdiv))
    have hQ0 : ¬ (2:ℤ) ∣ Q.coeff 0 := by
      have hh := congrArg (fun p : ℤ[X] => p.coeff 0) hQ
      simp [coeff_add,coeff_C_mul] at hh
      have hcst : U.coeff 0 * V.coeff 0 = c^2 := hconst.trans hcW
      have hu : U.coeff 0 % 2=1 := by omega
      have hv : V.coeff 0 % 2=1 := by omega
      have hcc : c%2=1 := by omega
      have huu : U.coeff 0 % 4 = 1 ∨ U.coeff 0 % 4 = 3 := by omega
      have hvv : V.coeff 0 % 4 = 1 ∨ V.coeff 0 % 4 = 3 := by omega
      have hc' : c % 4 = 1 ∨ c % 4 = 3 := by omega
      have hmod := congrArg (fun z : ℤ => z % 4) hcst
      rw [Int.mul_emod (U.coeff 0) (V.coeff 0) 4, pow_two, Int.mul_emod c c 4] at hmod
      rcases huu with hu'|hu' <;> rcases hvv with hv'|hv' <;>
        rcases hc' with hc'|hc' <;> rw [hu',hv',hc'] at hmod <;> norm_num at hmod <;> omega
    have hUeq : V = C 2*Q-U := by linear_combination hQ
    have hprod : U*V = C 2*(U*Q)-U*U := by rw [hUeq]; ring
    obtain ⟨r,hrm⟩ := he
    have hr : 0<r := by omega
    have hsq := low_square_mod4 hr U (fun j hj hjr => h_evenU j hj (by omega))
    have hQeven : ∀ i, 0 < i → i < m → (2:ℤ) ∣ Q.coeff i := by
      intro i
      induction i using Nat.strong_induction_on with
      | h i IH =>
        intro hi him
        have hUV := congrArg (fun p : ℤ[X] => p.coeff i) hW
        simp [coeff_X_pow_mul',if_neg (show ¬ m ≤ i from by omega)] at hUV
        have hmul := congrArg (fun p : ℤ[X] => p.coeff i) hprod
        simp [coeff_C_mul,coeff_sub] at hmul
        obtain ⟨z,hz⟩ := hsq i hi (by omega)
        obtain ⟨w,hw⟩ := hlow i hi him
        have hdvd : (2:ℤ) ∣ (U*Q).coeff i-U.coeff 0*U.coeff i := by
          exact ⟨z+w, by nlinarith only [hUV,hmul,hz,hw]⟩
        have hcast := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdvd
        simp only [Int.cast_sub, Int.cast_mul] at hcast
        have hQ0r : (Q.coeff 0 : ZMod 2) = 1 := by
          have hmod : Q.coeff 0 ≡ (1:ℤ) [ZMOD 2] := by
            unfold Int.ModEq
            omega
          have heq := (ZMod.intCast_eq_intCast_iff (Q.coeff 0) 1 2).2 hmod
          simpa using heq
        rw [coeff_mul_mod2_edges U Q i hi (fun j hj hji => IH j hji hj (by omega)), hQ0r, mul_one] at hcast
        have hU0r1 : (U.coeff 0 : ZMod 2) = 1 := by
          have hmod : U.coeff 0 ≡ (1:ℤ) [ZMOD 2] := by
            unfold Int.ModEq
            omega
          have heq := (ZMod.intCast_eq_intCast_iff (U.coeff 0) 1 2).2 hmod
          simpa using heq
        have hh : (U.coeff 0 : ZMod 2)*(Q.coeff i : ZMod 2)=0 := by
          rw [hU0r1,one_mul] at hcast ⊢
          linear_combination hcast
        have hu : (U.coeff 0 : ZMod 2)≠0 := by
          exact fun hz => hU0 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hz)
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 ((mul_eq_zero.mp hh).resolve_left hu)
    have hlast := congrArg (fun p : (ZMod 2)[X] => p.coeff (2*m-1)) hredW
    rw [coeff_add,coeff_X_pow_mul',if_pos (show m ≤ 2*m-1 from by omega),
      show 2*m-1-m=m-1 by omega, square_coeff_odd _ _ (by omega), add_zero] at hlast
    have hq := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (hQeven (m-1) (by omega) (by omega))
    rw [red_coeff,red_coeff,hq] at hlast
    exact htop ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hlast)

end BinomialPowerTwo

open Polynomial
namespace A115257Power
open A115257Valuation A115257Lift



lemma div_dvd_sq (k : ℕ) : k+1 ∣ (Nat.centralBinom k)^2 := by
  simpa [pow_two] using dvd_mul_of_dvd_left (Nat.succ_dvd_centralBinom k) (Nat.centralBinom k)

lemma aN_cast (q : Bool) (k : ℕ) : (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q k : ℚ) = ((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k : ℚ)^2 / (if q then (k:ℚ)+1 else 1)) : Bool → ℕ → ℚ) q k := by
  cases q
  · simp []
  · have h := Nat.div_mul_cancel (div_dvd_sq k)
    have hc : (((Nat.centralBinom k)^2 / (k+1) : ℕ):ℚ)*((k:ℚ)+1) = (Nat.centralBinom k:ℚ)^2 := by exact_mod_cast h
    simpa [] using (eq_div_iff (by positivity : (k:ℚ)+1 ≠ 0)).mpr hc

lemma aN_pos (q : Bool) (k : ℕ) : 0 < ((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q k := by
  have hc : 0 < (Nat.centralBinom k:ℚ) := by exact_mod_cast Nat.centralBinom_pos k
  have h : 0 < ((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k : ℚ)^2 / (if q then (k:ℚ)+1 else 1)) : Bool → ℕ → ℚ) q k := by cases q <;> simp [] <;> positivity
  rw [← aN_cast] at h
  exact_mod_cast h

lemma aN_zero (q : Bool) : ((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q 0 = 1 := by cases q <;> decide

lemma aN_val (q : Bool) (k : ℕ) : (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q k).factorization 2 =
    2 * (Nat.centralBinom k).factorization 2 - (if q then (k+1).factorization 2 else 0) := by
  cases q
  · simp [Nat.factorization_pow, Finsupp.smul_apply]
  · simp only [↓reduceIte, Nat.factorization_div (div_dvd_sq k), Nat.factorization_pow, Finsupp.tsub_apply, Finsupp.smul_apply, nsmul_eq_mul]
    rfl

lemma cval_pos {k : ℕ} (hk : 0 < k) : 1 ≤ (Nat.centralBinom k).factorization 2 := by
  rw [central_val]
  exact digit_sum_pos hk

lemma even_pow2 (r : ℕ) (hr : 1 ≤ r) : 2 ∣ (2:ℕ)^r := by
  obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  rw [hs,pow_succ]
  exact dvd_mul_left _ _

lemma cval_ge_two_of_odd (k : ℕ) (hk : 2 ≤ k) (ho : ¬2 ∣ k) : 2 ≤ (Nat.centralBinom k).factorization 2 := by
  by_contra! h
  have hval : (Nat.centralBinom k).factorization 2 = 1 := by have hp := cval_pos (show 0 < k by omega); omega
  rw [central_val,digit_sum_eq_one_iff] at hval
  obtain ⟨r,hr⟩ := hval
  have hr1 : 1 ≤ r := by
    by_contra! h
    have hz : r = 0 := by omega
    simp [hz] at hr
    omega
  exact ho (hr ▸ even_pow2 r hr1)

lemma aN_four_dvd_P (k : ℕ) (hk : 0 < k) : 4 ∣ ((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) false k := by
  apply (Nat.prime_two.pow_dvd_iff_le_factorization (aN_pos false k).ne' (k:=2)).2
  rw [aN_val]
  simp
  have h := cval_pos hk
  omega

lemma aN_four_dvd_Q (k : ℕ) (hk : 2 ≤ k) : 4 ∣ ((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) true k := by
  apply (Nat.prime_two.pow_dvd_iff_le_factorization (aN_pos true k).ne' (k:=2)).2
  rw [aN_val]
  simp only [↓reduceIte]
  by_cases he : 2 ∣ k
  · have hh : ¬2 ∣ k+1 := by omega
    rw [Nat.factorization_eq_zero_of_not_dvd hh]
    have h := cval_pos (show 0 < k by omega)
    omega
  · have hc := cval_ge_two_of_odd k hk he
    have hle := (Nat.factorization_le_iff_dvd (by omega : k+1 ≠ 0) (Nat.centralBinom_ne_zero k)).2 (Nat.succ_dvd_centralBinom k) 2
    omega

lemma pow2_aN_val (q : Bool) (r : ℕ) (hr : 1 ≤ r) : (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q (2^r)).factorization 2 = 2 := by
  have he := even_pow2 r hr
  have hd : ¬2 ∣ 2^r+1 := by omega
  rw [aN_val,central_val_pow, Nat.factorization_eq_zero_of_not_dvd hd]
  cases q <;> rfl

lemma aN_P_sixteen (r k : ℕ) (h1 : 2^r < k) (h2 : k < 2^(r+1)) : 16 ∣ ((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) false k := by
  apply (Nat.prime_two.pow_dvd_iff_le_factorization (aN_pos false k).ne' (k:=4)).2
  rw [aN_val]
  simp
  have h := central_val_between r k h1 h2
  omega

lemma aN_Q_eight (r : ℕ) (hr : 2 ≤ r) : 8 ∣ ((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) true (2^r+1) := by
  have h4 : 4 ∣ (2:ℕ)^r := by
    change (2:ℕ)^2 ∣ 2^r
    exact pow_dvd_pow _ hr
  have hpos : 4 ≤ (2:ℕ)^r := by exact Nat.pow_le_pow_right (by decide : (0:ℕ) < 2) hr
  have h1 : 2^r < 2^r+1 := by omega
  have h2 : 2^r+1 < 2^(r+1) := by rw [pow_succ]; omega
  have hc := central_val_between r (2^r+1) h1 h2
  have hd1 : 2 ∣ (2:ℕ)^r+1+1 := by omega
  have hd2 : ¬4 ∣ (2:ℕ)^r+1+1 := by omega
  have hv1 := (Nat.prime_two.pow_dvd_iff_le_factorization (by omega : (2:ℕ)^r+1+1 ≠ 0) (k := 1)).1 (by simpa using hd1)
  have hv2 : ¬ 2 ≤ ((2:ℕ)^r+1+1).factorization 2 := by
    intro h
    exact hd2 ((Nat.prime_two.pow_dvd_iff_le_factorization (by omega : (2:ℕ)^r+1+1 ≠ 0) (k := 2)).2 h)
  have hv : ((2:ℕ)^r+1+1).factorization 2 = 1 := by omega
  apply (Nat.prime_two.pow_dvd_iff_le_factorization (aN_pos true (2^r+1)).ne' (k:=3)).2
  rw [aN_val]
  simp only [↓reduceIte,hv]
  omega


lemma f_coeff (q : Bool) (n i : ℕ) : (((fun (q : Bool) (n : ℕ) => ((fun (a : ℕ → ℤ) (n : ℕ) => ∑ i ∈ Finset.range (n+1), C (a (n-i)) * X ^ i) : (ℕ → ℤ) → ℕ → Polynomial ℤ) (fun i => (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q i:ℤ)) n) : Bool → ℕ → Polynomial ℤ) q n).coeff i = if i ≤ n then (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q (n-i):ℤ) else 0 := by
  classical
  rw [finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Nat.lt_succ_iff]

lemma f_deg (q : Bool) (n : ℕ) : (((fun (q : Bool) (n : ℕ) => ((fun (a : ℕ → ℤ) (n : ℕ) => ∑ i ∈ Finset.range (n+1), C (a (n-i)) * X ^ i) : (ℕ → ℤ) → ℕ → Polynomial ℤ) (fun i => (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q i:ℤ)) n) : Bool → ℕ → Polynomial ℤ) q n).natDegree = n := by
  apply le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [f_coeff, if_neg (by omega)]
  · apply le_natDegree_of_ne_zero
    rw [f_coeff, if_pos le_rfl, Nat.sub_self]
    exact_mod_cast (show ((Nat.centralBinom 0)^2 / (if q then 0+1 else 1) : ℕ) ≠ 0 from by cases q <;> decide)

lemma f_monic (q : Bool) (n : ℕ) : (((fun (q : Bool) (n : ℕ) => ((fun (a : ℕ → ℤ) (n : ℕ) => ∑ i ∈ Finset.range (n+1), C (a (n-i)) * X ^ i) : (ℕ → ℤ) → ℕ → Polynomial ℤ) (fun i => (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q i:ℤ)) n) : Bool → ℕ → Polynomial ℤ) q n).Monic := by
  unfold Monic
  rw [leadingCoeff, f_deg, f_coeff, if_pos le_rfl, Nat.sub_self]
  cases q <;> decide

lemma fP_form (n : ℕ) : ∃ W : Polynomial ℤ, ((fun (q : Bool) (n : ℕ) => ((fun (a : ℕ → ℤ) (n : ℕ) => ∑ i ∈ Finset.range (n+1), C (a (n-i)) * X ^ i) : (ℕ → ℤ) → ℕ → Polynomial ℤ) (fun i => (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q i:ℤ)) n) : Bool → ℕ → Polynomial ℤ) false n = X^n + C 4 * W := by
  have hd : C (4:ℤ) ∣ ((fun (q : Bool) (n : ℕ) => ((fun (a : ℕ → ℤ) (n : ℕ) => ∑ i ∈ Finset.range (n+1), C (a (n-i)) * X ^ i) : (ℕ → ℤ) → ℕ → Polynomial ℤ) (fun i => (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q i:ℤ)) n) : Bool → ℕ → Polynomial ℤ) false n - X^n := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    rw [coeff_sub, f_coeff, coeff_X_pow]
    rcases lt_trichotomy i n with h|rfl|h
    · rw [if_pos h.le, if_neg h.ne, sub_zero]
      exact_mod_cast aN_four_dvd_P (n-i) (by omega)
    · simp [aN_zero]
    · simp [if_neg (by omega : ¬i ≤ n), if_neg h.ne']
  obtain ⟨W,hW⟩ := hd
  exact ⟨W, (sub_eq_iff_eq_add.mp hW).trans (add_comm _ _)⟩

lemma fQ_form (n : ℕ) (hn : 2 ≤ n) : ∃ H : Polynomial ℤ, ((fun (q : Bool) (n : ℕ) => ((fun (a : ℕ → ℤ) (n : ℕ) => ∑ i ∈ Finset.range (n+1), C (a (n-i)) * X ^ i) : (ℕ → ℤ) → ℕ → Polynomial ℤ) (fun i => (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q i:ℤ)) n) : Bool → ℕ → Polynomial ℤ) true n = X^n + C 2 * X^(n-1) + C 4 * H := by
  have hd : C (4:ℤ) ∣ ((fun (q : Bool) (n : ℕ) => ((fun (a : ℕ → ℤ) (n : ℕ) => ∑ i ∈ Finset.range (n+1), C (a (n-i)) * X ^ i) : (ℕ → ℤ) → ℕ → Polynomial ℤ) (fun i => (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q i:ℤ)) n) : Bool → ℕ → Polynomial ℤ) true n - (X^n + C 2 * X^(n-1)) := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    rw [coeff_sub, coeff_add, f_coeff, coeff_X_pow, coeff_C_mul_X_pow]
    by_cases hi : i = n
    · subst i; simp [aN_zero, if_neg (by omega : n ≠ n-1)]
    by_cases hi' : i = n-1
    · subst i
      have h : n-(n-1)=1 := by omega
      simp [h, if_pos (show n-1 ≤ n by omega),if_neg (by omega : n-1 ≠ n)]
      decide
    by_cases hil : i < n-1
    · rw [if_pos (by omega),if_neg hi,if_neg hi', zero_add, sub_zero]
      exact_mod_cast aN_four_dvd_Q (n-i) (by omega)
    · rw [if_neg (by omega),if_neg hi,if_neg hi',zero_add, sub_zero]; exact dvd_zero _
  obtain ⟨H,hH⟩ := hd
  exact ⟨H,(sub_eq_iff_eq_add.mp hH).trans (add_comm _ _)⟩

lemma fP_Wcoeff {n i : ℕ} (h : i < n) (W : Polynomial ℤ)
    (hW : ((fun (q : Bool) (n : ℕ) => ((fun (a : ℕ → ℤ) (n : ℕ) => ∑ i ∈ Finset.range (n+1), C (a (n-i)) * X ^ i) : (ℕ → ℤ) → ℕ → Polynomial ℤ) (fun i => (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q i:ℤ)) n) : Bool → ℕ → Polynomial ℤ) false n = X^n + C 4*W) : (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) false (n-i):ℤ) = 4*W.coeff i := by
  have hh := congrArg (fun p : ℤ[X] => p.coeff i) hW
  rw [f_coeff false n i, if_pos h.le, coeff_add, coeff_X_pow, if_neg h.ne, coeff_C_mul, zero_add] at hh
  exact hh

lemma fQ_Hcoeff {n i : ℕ} (h : i < n-1) (H : Polynomial ℤ)
    (hH : ((fun (q : Bool) (n : ℕ) => ((fun (a : ℕ → ℤ) (n : ℕ) => ∑ i ∈ Finset.range (n+1), C (a (n-i)) * X ^ i) : (ℕ → ℤ) → ℕ → Polynomial ℤ) (fun i => (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q i:ℤ)) n) : Bool → ℕ → Polynomial ℤ) true n = X^n + C 2*X^(n-1) + C 4*H) : (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) true (n-i):ℤ) = 4*H.coeff i := by
  have hh := congrArg (fun p : ℤ[X] => p.coeff i) hH
  simpa [f_coeff,show i ≤ n by omega,show i ≠ n by omega,h.ne,coeff_add,coeff_X_pow,coeff_C_mul,coeff_C_mul_X_pow] using hh

lemma fP_power (r : ℕ) (hr : 1 ≤ r) : Irreducible (((fun (q : Bool) (n : ℕ) => ((fun (a : ℕ → ℤ) (n : ℕ) => ∑ i ∈ Finset.range (n+1), C (a (n-i)) * X ^ i) : (ℕ → ℤ) → ℕ → Polynomial ℤ) (fun i => (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q i:ℤ)) n) : Bool → ℕ → Polynomial ℤ) false (2^(r+1))) := by
  let m : ℕ := 2^r
  have hn : 2^(r+1)=2*m := by rw [pow_succ]; simp [m,mul_comm]
  rw [hn]
  have hm : 2 ≤ m := by exact Nat.pow_le_pow_right (by decide : (0:ℕ) < 2) hr
  have he : Even m := even_iff_two_dvd.mpr (even_pow2 r hr)
  obtain ⟨W,hW⟩ := fP_form (2*m)
  apply BinomialPowerTwo.criterion m hm he _ W (f_monic false (2*m)) (f_deg false (2*m)) hW
  · have hconst := fP_Wcoeff (n:=2*m) (i:=0) (by omega) W hW
    rw [Nat.sub_zero] at hconst
    have hval : (Nat.centralBinom (2*m)).factorization 2 = 1 := by rw [← hn,central_val_pow]
    have hd : 2 ∣ Nat.centralBinom (2*m) := (Nat.prime_two.dvd_iff_one_le_factorization (Nat.centralBinom_ne_zero _)).2 (by omega)
    have hnd : ¬4 ∣ Nat.centralBinom (2*m) := by
      intro h
      have hh := (Nat.prime_two.pow_dvd_iff_le_factorization (Nat.centralBinom_ne_zero _) (k:=2)).1 h
      omega
    obtain ⟨c,hc⟩ := hd
    have hco : ¬2 ∣ c := by omega
    refine ⟨(c:ℤ), by exact_mod_cast hco, ?_⟩
    simp [hc, Nat.cast_mul,Nat.cast_pow] at hconst
    nlinarith
  · intro i hi him
    have hcoef := fP_Wcoeff (by omega : i < 2*m) W hW
    have hd := aN_P_sixteen r (2*m-i) (by dsimp [m] at *; omega) (by rw [hn]; omega)
    have hdz : (16:ℤ) ∣ (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) false (2*m-i):ℤ) := by exact_mod_cast hd
    omega
  · have ht := fP_Wcoeff (n:=2*m) (i:=2*m-1) (by omega) W hW
    rw [show 2*m-(2*m-1)=1 by omega,show ((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) false 1=4 by decide] at ht
    omega

lemma fQ_power (r : ℕ) (hr : 2 ≤ r) : Irreducible (((fun (q : Bool) (n : ℕ) => ((fun (a : ℕ → ℤ) (n : ℕ) => ∑ i ∈ Finset.range (n+1), C (a (n-i)) * X ^ i) : (ℕ → ℤ) → ℕ → Polynomial ℤ) (fun i => (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q i:ℤ)) n) : Bool → ℕ → Polynomial ℤ) true (2^(r+1))) := by
  let m : ℕ := 2^r
  have hn : 2^(r+1)=2*m := by rw [pow_succ]; simp [m,mul_comm]
  rw [hn]
  have hm : 4 ≤ m := by exact Nat.pow_le_pow_right (by decide : (0:ℕ) < 2) hr
  have he : Even m := even_iff_two_dvd.mpr (even_pow2 r (by omega))
  obtain ⟨H,hH⟩ := fQ_form (2*m) (by omega)
  apply BinomialIrredQ.criterion m (by omega) he H _ (f_monic true (2*m)) (f_deg true (2*m)) hH
  · have hconst := fQ_Hcoeff (n:=2*m) (i:=0) (by omega) H hH
    rw [Nat.sub_zero] at hconst
    have hval : (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) true (2*m)).factorization 2 = 2 := by rw [← hn]; exact pow2_aN_val true (r+1) (by omega)
    have hnd : ¬8 ∣ ((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) true (2*m) := by
      intro h
      have hh := (Nat.prime_two.pow_dvd_iff_le_factorization (aN_pos true (2*m)).ne' (k:=3)).1 h
      omega
    have hndz : ¬ (8:ℤ) ∣ (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) true (2*m):ℤ) := by exact_mod_cast hnd
    intro hH0
    apply hndz
    obtain ⟨z, hz⟩ := hH0
    refine ⟨z, ?_⟩
    rw [hconst, hz]
    ring
  · have hcoef := fQ_Hcoeff (n:=2*m) (i:=m-1) (by omega) H hH
    rw [show 2*m-(m-1)=m+1 by omega] at hcoef
    have hd := aN_Q_eight r hr
    have hdz : (8:ℤ) ∣ (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) true (m+1):ℤ) := by exact_mod_cast hd
    omega


lemma trunc_eq_family (q : Bool) (n : ℕ) :
    ((fun (a : ℕ → ℚ) (n : ℕ) => ∑ k ∈ Finset.range (n+1), C (a k) * X ^ k) : (ℕ → ℚ) → ℕ → Polynomial ℚ) (fun k => ((((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q k:ℤ):ℚ)) n = if q then polyQ n else polyP n := by
  cases q
  · simp only [Bool.false_eq_true, ↓reduceIte, polyP]
    apply Finset.sum_congr rfl
    intro k hk
    apply congrArg (fun a : ℚ => C a * X^k)
    simpa only [Int.cast_natCast, Bool.false_eq_true, ↓reduceIte, div_one] using (aN_cast false k)
  · simp only [↓reduceIte, polyQ]
    apply Finset.sum_congr rfl
    intro k hk
    apply congrArg (fun a : ℚ => C a * X^k)
    simpa only [Int.cast_natCast, ↓reduceIte] using (aN_cast true k)

lemma family_irr_of_f (q : Bool) (n : ℕ) (h : Irreducible (((fun (q : Bool) (n : ℕ) => ((fun (a : ℕ → ℤ) (n : ℕ) => ∑ i ∈ Finset.range (n+1), C (a (n-i)) * X ^ i) : (ℕ → ℤ) → ℕ → Polynomial ℤ) (fun i => (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q i:ℤ)) n) : Bool → ℕ → Polynomial ℤ) q n)) :
    Irreducible (if q then polyQ n else polyP n) := by
  rw [← trunc_eq_family]
  apply trunc_irr_of_reverse_int
  · simp [aN_zero]
  · exact_mod_cast (aN_pos q n).ne'
  · exact h

theorem polyP_pow2_ge4 (r : ℕ) (hr : 1 ≤ r) : Irreducible (polyP (2^(r+1))) :=
  family_irr_of_f false _ (fP_power r hr)

theorem polyQ_pow2_ge8 (r : ℕ) (hr : 2 ≤ r) : Irreducible (polyQ (2^(r+1))) :=
  family_irr_of_f true _ (fQ_power r hr)

end A115257Power
open Polynomial
namespace A115257Power

lemma monic_int_irr_of_map {p : ℕ} [Fact p.Prime] {g : ℤ[X]} (hm : g.Monic)
    (hi : Irreducible (g.map (Int.castRingHom (ZMod p)))) : Irreducible g := by
  rw [hm.irreducible_iff_natDegree]
  have hi' := ((hm.map (Int.castRingHom (ZMod p))).irreducible_iff_natDegree).mp hi
  refine ⟨?_, ?_⟩
  · rintro rfl; exact hi'.1 (by simp)
  · intro a b ha hb hab
    have hab' : a.map (Int.castRingHom (ZMod p)) * b.map (Int.castRingHom (ZMod p)) =
        g.map (Int.castRingHom (ZMod p)) := by rw [← Polynomial.map_mul,hab]
    simpa [ha.natDegree_map,hb.natDegree_map] using hi'.2 _ _ (ha.map _) (hb.map _) hab'

lemma monic_irr_deg_le_three {K : Type*} [CommRing K] [IsDomain K] {g : K[X]}
    (hm : g.Monic) (hn : 0 < g.natDegree) (h3 : g.natDegree ≤ 3)
    (hroot : ∀ x : K, g.eval x ≠ 0) : Irreducible g := by
  rw [hm.irreducible_iff_natDegree]
  constructor
  · intro h; simp [h] at hn
  · intro a b ha hb hab
    by_contra! h
    obtain ⟨h1,h2⟩ := h
    have hsum : a.natDegree + b.natDegree = g.natDegree := by rw [←ha.natDegree_mul hb,hab]
    have hor : a.natDegree=1 ∨ b.natDegree=1 := by omega
    rcases hor with hA | hB
    · have hx := hroot (-a.coeff 0)
      rw [←hab,eval_mul,ha.eq_X_add_C hA] at hx
      simp at hx
    · have hx := hroot (-b.coeff 0)
      rw [←hab,eval_mul,hb.eq_X_add_C hB] at hx
      simp at hx

lemma irreducible_quartic_scalar {K : Type*} [Field K] {g : K[X]} (hm : g.Monic)
    (hd : g.natDegree = 4) (h1 : ∀ a : K, g.eval a ≠ 0)
    (h2 : ∀ a b : K, let c := g.coeff 3 - a; let d := g.coeff 2 - b - a*c;
      ¬ (b*d = g.coeff 0 ∧ a*d+b*c = g.coeff 1)) : Irreducible g := by
  rw [hm.irreducible_iff_natDegree]
  constructor
  · intro h; simp [h] at hd
  · intro u v hu hv huv
    by_contra! h
    obtain ⟨hU,hV⟩ := h
    have hsum : u.natDegree + v.natDegree = 4 := by rw [←hu.natDegree_mul hv,huv,hd]
    have hor : u.natDegree=1 ∨ v.natDegree=1 ∨ (u.natDegree=2 ∧ v.natDegree=2) := by omega
    rcases hor with hu1 | hv1 | ⟨hu2,hv2⟩
    · have h := h1 (-u.coeff 0)
      rw [← huv, eval_mul, hu.eq_X_add_C hu1] at h
      simp at h
    · have h := h1 (-v.coeff 0)
      rw [← huv, eval_mul, hv.eq_X_add_C hv1] at h
      simp at h
    · have huc : u.coeff 2 = 1 := by simpa [hu2] using hu.coeff_natDegree
      have hvc : v.coeff 2 = 1 := by simpa [hv2] using hv.coeff_natDegree
      have hu3 : u.coeff 3 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      have hv3 : v.coeff 3 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      have h0 : u.coeff 0 * v.coeff 0 = g.coeff 0 := by rw [← huv, mul_coeff_zero]
      have h1' : u.coeff 0 * v.coeff 1 + u.coeff 1 * v.coeff 0 = g.coeff 1 := by
        rw [← huv, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        simp [Finset.sum_range_succ]
      have h2' : v.coeff 0 + u.coeff 0 + u.coeff 1 * v.coeff 1 = g.coeff 2 := by
        rw [← huv, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        simp [Finset.sum_range_succ, huc, hvc]; ring
      have h3 : u.coeff 1 + v.coeff 1 = g.coeff 3 := by
        rw [← huv, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        simp [Finset.sum_range_succ, huc, hvc, hu3, hv3]
      have hc : g.coeff 3 - u.coeff 1 = v.coeff 1 := by rw [← h3]; ring
      have he : g.coeff 2 - u.coeff 0 - u.coeff 1 * v.coeff 1 = v.coeff 0 := by rw [← h2']; ring
      apply h2 (u.coeff 1) (u.coeff 0)
      rw [hc,he]
      exact ⟨h0, by rw [add_comm]; exact h1'⟩

lemma f_one (q : Bool) : Irreducible (((fun (q : Bool) (n : ℕ) => ((fun (a : ℕ → ℤ) (n : ℕ) => ∑ i ∈ Finset.range (n+1), C (a (n-i)) * X ^ i) : (ℕ → ℤ) → ℕ → Polynomial ℤ) (fun i => (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q i:ℤ)) n) : Bool → ℕ → Polynomial ℤ) q 1) := by
  rw [(f_monic q 1).irreducible_iff_natDegree]
  constructor
  · intro hh
    have h := f_deg q 1
    rw [hh, natDegree_one] at h
    omega
  · intro A B hA hB hAB
    have hsum : A.natDegree+B.natDegree=1 := by rw [←hA.natDegree_mul hB,hAB,f_deg]
    omega

lemma mapped_coeff (p : ℕ) (q : Bool) (n i : ℕ) :
    ((((fun (q : Bool) (n : ℕ) => ((fun (a : ℕ → ℤ) (n : ℕ) => ∑ i ∈ Finset.range (n+1), C (a (n-i)) * X ^ i) : (ℕ → ℤ) → ℕ → Polynomial ℤ) (fun i => (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q i:ℤ)) n) : Bool → ℕ → Polynomial ℤ) q n).map (Int.castRingHom (ZMod p))).coeff i = if i ≤ n then (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q (n-i):ZMod p) else 0 := by
  rw [coeff_map,f_coeff]
  split_ifs
  · exact Int.cast_natCast _
  · exact map_zero _

lemma mapped_eval (p : ℕ) [Fact p.Prime] (q : Bool) (n : ℕ) (x : ZMod p) :
    ((((fun (q : Bool) (n : ℕ) => ((fun (a : ℕ → ℤ) (n : ℕ) => ∑ i ∈ Finset.range (n+1), C (a (n-i)) * X ^ i) : (ℕ → ℤ) → ℕ → Polynomial ℤ) (fun i => (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q i:ℤ)) n) : Bool → ℕ → Polynomial ℤ) q n).map (Int.castRingHom (ZMod p))).eval x =
       ∑ i ∈ Finset.range (n+1), (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q (n-i):ZMod p)*x^i := by
  have hm := f_monic q n
  have hdeg : ((((fun (q : Bool) (n : ℕ) => ((fun (a : ℕ → ℤ) (n : ℕ) => ∑ i ∈ Finset.range (n+1), C (a (n-i)) * X ^ i) : (ℕ → ℤ) → ℕ → Polynomial ℤ) (fun i => (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q i:ℤ)) n) : Bool → ℕ → Polynomial ℤ) q n).map (Int.castRingHom (ZMod p))).natDegree = n := (hm.natDegree_map (Int.castRingHom (ZMod p))).trans (f_deg q n)
  rw [eval_eq_sum_range,hdeg]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mapped_coeff,if_pos (by simpa [Nat.lt_succ_iff] using hi)]

lemma f_P2 : Irreducible (((fun (q : Bool) (n : ℕ) => ((fun (a : ℕ → ℤ) (n : ℕ) => ∑ i ∈ Finset.range (n+1), C (a (n-i)) * X ^ i) : (ℕ → ℤ) → ℕ → Polynomial ℤ) (fun i => (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q i:ℤ)) n) : Bool → ℕ → Polynomial ℤ) false 2) := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply monic_int_irr_of_map (p:=5) (f_monic false 2)
  have hd : ((((fun (q : Bool) (n : ℕ) => ((fun (a : ℕ → ℤ) (n : ℕ) => ∑ i ∈ Finset.range (n+1), C (a (n-i)) * X ^ i) : (ℕ → ℤ) → ℕ → Polynomial ℤ) (fun i => (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q i:ℤ)) n) : Bool → ℕ → Polynomial ℤ) false 2).map (Int.castRingHom (ZMod 5))).natDegree = 2 := ((f_monic false 2).natDegree_map (Int.castRingHom (ZMod 5))).trans (f_deg false 2)
  apply monic_irr_deg_le_three ((f_monic false 2).map _) (by rw [hd]; decide) (by rw [hd]; decide)
  intro x
  rw [mapped_eval]
  have h : ∀ x : ZMod 5, (∑ i ∈ Finset.range (2+1), (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) false (2-i):ZMod 5)*x^i) ≠ 0 := by decide
  exact h x

lemma f_Q2 : Irreducible (((fun (q : Bool) (n : ℕ) => ((fun (a : ℕ → ℤ) (n : ℕ) => ∑ i ∈ Finset.range (n+1), C (a (n-i)) * X ^ i) : (ℕ → ℤ) → ℕ → Polynomial ℤ) (fun i => (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q i:ℤ)) n) : Bool → ℕ → Polynomial ℤ) true 2) := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply monic_int_irr_of_map (p:=7) (f_monic true 2)
  have hd : ((((fun (q : Bool) (n : ℕ) => ((fun (a : ℕ → ℤ) (n : ℕ) => ∑ i ∈ Finset.range (n+1), C (a (n-i)) * X ^ i) : (ℕ → ℤ) → ℕ → Polynomial ℤ) (fun i => (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q i:ℤ)) n) : Bool → ℕ → Polynomial ℤ) true 2).map (Int.castRingHom (ZMod 7))).natDegree = 2 := ((f_monic true 2).natDegree_map (Int.castRingHom (ZMod 7))).trans (f_deg true 2)
  apply monic_irr_deg_le_three ((f_monic true 2).map _) (by rw [hd]; decide) (by rw [hd]; decide)
  intro x
  rw [mapped_eval]
  have h : ∀ x : ZMod 7, (∑ i ∈ Finset.range (2+1), (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) true (2-i):ZMod 7)*x^i) ≠ 0 := by decide
  exact h x

lemma f_Q4 : Irreducible (((fun (q : Bool) (n : ℕ) => ((fun (a : ℕ → ℤ) (n : ℕ) => ∑ i ∈ Finset.range (n+1), C (a (n-i)) * X ^ i) : (ℕ → ℤ) → ℕ → Polynomial ℤ) (fun i => (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q i:ℤ)) n) : Bool → ℕ → Polynomial ℤ) true 4) := by
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  apply monic_int_irr_of_map (p:=13) (f_monic true 4)
  have hd : ((((fun (q : Bool) (n : ℕ) => ((fun (a : ℕ → ℤ) (n : ℕ) => ∑ i ∈ Finset.range (n+1), C (a (n-i)) * X ^ i) : (ℕ → ℤ) → ℕ → Polynomial ℤ) (fun i => (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) q i:ℤ)) n) : Bool → ℕ → Polynomial ℤ) true 4).map (Int.castRingHom (ZMod 13))).natDegree = 4 := ((f_monic true 4).natDegree_map (Int.castRingHom (ZMod 13))).trans (f_deg true 4)
  apply irreducible_quartic_scalar ((f_monic true 4).map _) hd
  · intro x
    rw [mapped_eval]
    have h : ∀ x : ZMod 13, (∑ i ∈ Finset.range (4+1), (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) true (4-i):ZMod 13)*x^i) ≠ 0 := by decide
    exact h x
  · intro a b
    rw [mapped_coeff 13 true 4 3, mapped_coeff 13 true 4 2, mapped_coeff 13 true 4 0, mapped_coeff 13 true 4 1]
    simp only [if_pos (by decide : 3 ≤ 4), if_pos (by decide : 2 ≤ 4), if_pos (by decide : 1 ≤ 4), if_pos (by decide : 0 ≤ 4)]
    have h : ∀ a b : ZMod 13, let c := (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) true (4-3):ZMod 13)-a; let d := (((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) true (4-2):ZMod 13)-b-a*c;
      ¬(b*d=(((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) true (4-0):ZMod 13) ∧ a*d+b*c=(((fun (q : Bool) (k : ℕ) => (Nat.centralBinom k)^2 / (if q then k+1 else 1)) : Bool → ℕ → ℕ) true (4-1):ZMod 13)) := by decide
    exact h a b

theorem all_power_two (r : ℕ) : Irreducible (polyP (2^r)) ∧ Irreducible (polyQ (2^r)) := by
  rcases r with _|r
  · exact ⟨family_irr_of_f false 1 (f_one false),family_irr_of_f true 1 (f_one true)⟩
  rcases r with _|r
  · exact ⟨family_irr_of_f false 2 f_P2,family_irr_of_f true 2 f_Q2⟩
  rcases r with _|r
  · exact ⟨polyP_pow2_ge4 1 (by decide),family_irr_of_f true 4 f_Q4⟩
  exact ⟨polyP_pow2_ge4 (r+2) (by omega),polyQ_pow2_ge8 (r+2) (by omega)⟩

end A115257Power


-- H1 asks only for exclusion of higher-degree possible proper factors.
def H1 : Prop := ∀ (n : ℕ), 1 ≤ n → (¬ ∃ r : ℕ, n = 2^r) →
  ∀ (g : Polynomial ℚ), g.Monic → 2 ≤ g.natDegree →
    g.natDegree ≤ (polyP n).natDegree / 2 → ¬ g ∣ polyP n

def H2 : Prop := ∀ (n : ℕ), 1 ≤ n → (¬ ∃ r : ℕ, n = 2^r) →
  ∀ (g : Polynomial ℚ), g.Monic → 2 ≤ g.natDegree →
    g.natDegree ≤ (polyQ n).natDegree / 2 → ¬ g ∣ polyQ n

lemma irreducible_aux (h1 : H1) (h2 : H2) (q : Bool) (n : ℕ) (hn : 1 ≤ n) :
    Irreducible (if q then polyQ n else polyP n) := by
  by_cases hp : ∃ r : ℕ, n = 2^r
  · obtain ⟨r, rfl⟩ := hp
    cases q
    · exact (A115257Power.all_power_two r).1
    · exact (A115257Power.all_power_two r).2
  let p : Polynomial ℚ := if q then polyQ n else polyP n
  change Irreducible p
  have htop : p.coeff n ≠ 0 := coeff_top q n
  have hp0 : p ≠ 0 := by intro h; simp [h] at htop
  have hpn : n ≤ p.natDegree := le_natDegree_of_ne_zero htop
  have hpu : ¬ IsUnit p := by
    intro h; have hh := natDegree_eq_zero_of_isUnit h; omega
  by_cases hsmall : n = 1
  · subst n
    apply irreducible_of_degree_eq_one
    rw [degree_eq_natDegree hp0]
    have hh : p.natDegree ≤ 1 := by
      apply natDegree_le_iff_coeff_eq_zero.mpr
      intro i hi
      change (if q then polyQ 1 else polyP 1).coeff i = 0
      rw [coeff_family, if_neg (by omega)]
    have he : p.natDegree = 1 := by omega
    rw [he]
    rfl
  · rw [irreducible_iff_lt_natDegree_lt hp0 hpu]
    intro g hg hd hdiv
    have hdpos : 0 < g.natDegree := (Finset.mem_Ioc.mp hd).1
    have hdle : g.natDegree ≤ p.natDegree / 2 := (Finset.mem_Ioc.mp hd).2
    by_cases hlin : g.natDegree = 1
    · rcases Nat.even_or_odd n with he | ho
      · obtain ⟨m, hm⟩ := he
        have hnn : n = 2*m := by omega
        change g ∣ (if q then polyQ n else polyP n) at hdiv
        rw [hnn] at hdiv
        exact even_no_linear_factor q m g hlin hdiv
      · have hg0 : g ≠ 0 := hg.ne_zero
        have hd1 : g.degree = 1 := by rw [degree_eq_natDegree hg0, hlin]; rfl
        obtain ⟨x, hx⟩ := exists_root_of_degree_eq_one hd1
        obtain ⟨f, hf⟩ := hdiv
        have hz : p.eval x = 0 := by rw [hf, eval_mul, hx.eq_zero, zero_mul]
        have ho' := ho
        obtain ⟨k, hk⟩ := ho'
        exact odd_no_root q n (by omega) ho x hz
    · have hd2 : 2 ≤ g.natDegree := by omega
      cases q
      · exact h1 n hn hp g hg hd2 hdle hdiv
      · exact h2 n hn hp g hg hd2 hdle hdiv

theorem main : H1 → H2 → type_of% @OeisA115257.conjecture := by
  intro h1 h2 n hn
  exact ⟨irreducible_aux h1 h2 false n hn, irreducible_aux h1 h2 true n hn⟩

end OMA.R_OeisA115257_conjecture_R1

