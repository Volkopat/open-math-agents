import FormalConjectures.ErdosProblems.«372»
import Mathlib

-- Problem: Erdős Problem 372
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/372.lean:38 (declaration Erdos372.erdos_372)
-- Credit: @Mapika (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
# Erdős Problem 372: infinitely many `n` with `P(n) > P(n+1) > P(n+2)`

The result is due to Balog (2001). The argument formalised here is elementary and uses the
family `n = y² - 2`, `n + 1 = (y - 1)(y + 1)`, `n + 2 = y²`.

* Call `y` a peak if `P(y) > P(y-1)` and `P(y) > P(y+1)`. Two consecutive integers are never
  both peaks, so at least about half of the `y` in `(X, 2X]` are not peaks, and for those
  `P(n+1) > P(n+2)`.
* It is enough to find a non-peak `y` in `(X, 2X]` such that `y² - 2` has a prime factor above
  `2X + 1`. Suppose there is none. The von Mangoldt mass of `y² - 2` on primes at most
  `N = 2X + 1` (and on proper prime powers), summed over `y` in `(X, 2X]`, is at most
  `X log N + O(X)`: a prime power `d` divides `y² - 2` on at most `1 + χ₈(d) + [d = 2]`
  classes, and `∑_{d ≤ N} Λ(d)(1 + χ₈(d))/d ≤ log N + O(1)`.
* The non-peaks use up `(X - 1) log X` of that mass, so the peaks carry `O(X)`.
* The same count inside a class `y ≡ a (mod q)` with `q ≡ 1 (mod 8)` prime and `a² ≡ 2`
  shows about half of the class consists of peaks, each carrying mass at least `log q`.
  Summing over `q` in a finite set `Q` bounds `∑_{q ∈ Q} log q / q`, contradicting the
  divergence of that sum over primes `q ≡ 1 (mod 8)`.
-/

open Finset Real

namespace E372

/-- The real quadratic character modulo 8 attached to `ℚ(√2)`. -/
noncomputable def chi8 (n : ℕ) : ℝ :=
  if n % 8 = 1 ∨ n % 8 = 7 then 1 else if n % 8 = 3 ∨ n % 8 = 5 then -1 else 0

lemma chi8_mul (m n : ℕ) : chi8 (m * n) = chi8 m * chi8 n := by
  have h : (m * n) % 8 = ((m % 8) * (n % 8)) % 8 := Nat.mul_mod m n 8
  have hm : m % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hn : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
  unfold chi8
  rw [h]
  generalize m % 8 = a at hm
  generalize n % 8 = b at hn
  interval_cases a <;> interval_cases b <;> norm_num

lemma chi8_abs_le (n : ℕ) : |chi8 n| ≤ 1 := by
  unfold chi8
  split_ifs <;> norm_num

lemma chi8_ge (n : ℕ) : -1 ≤ chi8 n := (abs_le.mp (chi8_abs_le n)).1

lemma chi8_le (n : ℕ) : chi8 n ≤ 1 := (abs_le.mp (chi8_abs_le n)).2

/-- Partial sums of `chi8` only depend on the residue modulo 8. -/
lemma chi8_sum (n : ℕ) : ∑ m ∈ Ioc 0 n, chi8 m =
    if n % 8 = 1 ∨ n % 8 = 2 then 1 else if n % 8 = 5 ∨ n % 8 = 6 then -1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le n), ih]
    have hn : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have h : (n + 1) % 8 = (n % 8 + 1) % 8 := by omega
    unfold chi8
    rw [h]
    generalize n % 8 = a at hn
    interval_cases a <;> norm_num

lemma chi8_sum_abs (n : ℕ) : |∑ m ∈ Ioc 0 n, chi8 m| ≤ 1 := by
  rw [chi8_sum]
  split_ifs <;> norm_num

lemma chi8_sum_Ioc_abs (M N : ℕ) (h : M ≤ N) : |∑ m ∈ Ioc M N, chi8 m| ≤ 2 := by
  have h1 : ∑ m ∈ Ioc 0 N, chi8 m = ∑ m ∈ Ioc 0 M, chi8 m + ∑ m ∈ Ioc M N, chi8 m :=
    (Finset.sum_Ioc_consecutive _ (Nat.zero_le M) h).symm
  have h2 := chi8_sum_abs N
  have h3 := chi8_sum_abs M
  rw [abs_le] at *
  constructor <;> linarith [h2.1, h2.2, h3.1, h3.2]

/-- Abel's inequality for `chi8` against a nonincreasing nonnegative weight. -/
lemma abel_chi8 (g : ℕ → ℝ) (M : ℕ) (k : ℕ)
    (hmono : ∀ n, M < n → g (n + 1) ≤ g n) (hpos : ∀ n, M < n → 0 ≤ g n) :
    |∑ n ∈ Ioc M (M + 1 + k), chi8 n * g n| ≤ 2 * g (M + 1) := by
  have key : ∀ k : ℕ, |∑ n ∈ Ioc M (M + 1 + k), chi8 n * g n
      - (∑ n ∈ Ioc M (M + 1 + k), chi8 n) * g (M + 1 + k)| ≤ 2 * (g (M + 1) - g (M + 1 + k)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : M + 1 + (k + 1) = (M + 1 + k) + 1 := by ring
      rw [e, Finset.sum_Ioc_succ_top (by omega), Finset.sum_Ioc_succ_top (by omega)]
      have hd := chi8_sum_Ioc_abs M (M + 1 + k) (by omega)
      have hg := hmono (M + 1 + k) (by omega)
      set S := ∑ n ∈ Ioc M (M + 1 + k), chi8 n * g n
      set D := ∑ n ∈ Ioc M (M + 1 + k), chi8 n
      have e2 : S + chi8 (M + 1 + k + 1) * g (M + 1 + k + 1)
          - (D + chi8 (M + 1 + k + 1)) * g (M + 1 + k + 1)
          = (S - D * g (M + 1 + k)) + D * (g (M + 1 + k) - g (M + 1 + k + 1)) := by ring
      rw [e2]
      have h3 : |D * (g (M + 1 + k) - g (M + 1 + k + 1))| ≤ 2 * (g (M + 1 + k) - g (M + 1 + k + 1)) := by
        rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hg)]
        exact mul_le_mul_of_nonneg_right hd (sub_nonneg.mpr hg)
      calc _ ≤ |S - D * g (M + 1 + k)| + |D * (g (M + 1 + k) - g (M + 1 + k + 1))| := abs_add_le _ _
        _ ≤ 2 * (g (M + 1) - g (M + 1 + k)) + 2 * (g (M + 1 + k) - g (M + 1 + k + 1)) := add_le_add ih h3
        _ = _ := by ring
  have h1 := key k
  have hd := chi8_sum_Ioc_abs M (M + 1 + k) (by omega)
  have hg := hpos (M + 1 + k) (by omega)
  have h2 : |(∑ n ∈ Ioc M (M + 1 + k), chi8 n) * g (M + 1 + k)| ≤ 2 * g (M + 1 + k) := by
    rw [abs_mul, abs_of_nonneg hg]
    exact mul_le_mul_of_nonneg_right hd hg
  calc |∑ n ∈ Ioc M (M + 1 + k), chi8 n * g n|
      = |(∑ n ∈ Ioc M (M + 1 + k), chi8 n * g n
          - (∑ n ∈ Ioc M (M + 1 + k), chi8 n) * g (M + 1 + k))
          + (∑ n ∈ Ioc M (M + 1 + k), chi8 n) * g (M + 1 + k)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ 2 * (g (M + 1) - g (M + 1 + k)) + 2 * g (M + 1 + k) := add_le_add h1 h2
    _ = _ := by ring

open ArithmeticFunction in
/-- `A M = ∑_{m ≤ M} χ(m)/m`. -/
noncomputable def A (M : ℕ) : ℝ := ∑ m ∈ Ioc 0 M, chi8 m * (1 / (m : ℝ))

lemma A_diff (M N : ℕ) (h : M ≤ N) : |A N - A M| ≤ 2 / ((M : ℝ) + 1) := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · simp only [sub_self, abs_zero]; positivity
  obtain ⟨k, rfl⟩ : ∃ k, N = M + 1 + k := ⟨N - M - 1, by omega⟩
  have h1 : A (M + 1 + k) - A M = ∑ m ∈ Ioc M (M + 1 + k), chi8 m * (1 / (m : ℝ)) := by
    unfold A
    rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le M) h]
    ring
  rw [h1]
  have h2 := abel_chi8 (fun n => 1 / (n : ℝ)) M k
    (by
      intro n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      apply one_div_le_one_div_of_le hn'
      push_cast; linarith)
    (by intro n _; positivity)
  have e : (2 : ℝ) * (1 / ((M + 1 : ℕ) : ℝ)) = 2 / ((M : ℝ) + 1) := by push_cast; ring
  rw [← e]
  exact h2

lemma A_one : A 1 = 1 := by
  unfold A
  rw [show Ioc 0 1 = {1} from by decide]
  simp [chi8]

lemma A_two : A 2 = 1 := by
  unfold A
  rw [show Ioc 0 2 = {1, 2} from by decide]
  simp [chi8]

lemma A_three : A 3 = 2 / 3 := by
  unfold A
  rw [show Ioc 0 3 = {1, 2, 3} from by decide]
  simp [chi8]
  norm_num

lemma A_ge (M : ℕ) (hM : 1 ≤ M) : 1 / 6 ≤ A M := by
  rcases Nat.lt_or_ge M 3 with h | h
  · interval_cases M
    · rw [A_one]; norm_num
    · rw [A_two]; norm_num
  · have h1 := A_diff 3 M h
    rw [A_three, abs_le] at h1
    norm_num at h1
    linarith [h1.1]

/-- `B N = ∑_{n ≤ N} χ(n) log n / n`. -/
noncomputable def B (N : ℕ) : ℝ := ∑ n ∈ Ioc 0 N, chi8 n * (Real.log n / n)

lemma B_abs (N : ℕ) : |B N| ≤ 2 := by
  have hB2 : B 2 = 0 := by
    unfold B
    rw [show Ioc 0 2 = {1, 2} from by decide]
    simp [chi8]
  rcases Nat.lt_or_ge N 3 with h | h
  · interval_cases N
    · simp [B]
    · simp [B]
    · rw [hB2]; norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, N = 2 + 1 + k := ⟨N - 3, by omega⟩
    have h1 : B (2 + 1 + k) = ∑ n ∈ Ioc 2 (2 + 1 + k), chi8 n * (Real.log n / n) := by
      have := Finset.sum_Ioc_consecutive (fun n => chi8 n * (Real.log n / n)) (Nat.zero_le 2)
        (by omega : 2 ≤ 2 + 1 + k)
      unfold B at hB2 ⊢
      rw [← this, hB2, zero_add]
    rw [h1]
    have he : Real.exp 1 ≤ 3 := by
      have := Real.exp_one_lt_d9
      linarith
    have h2 := abel_chi8 (fun n => Real.log n / n) 2 k
      (by
        intro n hn
        have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (by omega : 3 ≤ n)
        have := Real.log_div_self_antitoneOn (a := (n : ℝ)) (b := ((n + 1 : ℕ) : ℝ))
          (by change Real.exp 1 ≤ (n : ℝ); linarith)
          (by change Real.exp 1 ≤ ((n + 1 : ℕ) : ℝ); push_cast; linarith)
          (by push_cast; linarith)
        exact this)
      (by
        intro n hn
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
        exact div_nonneg (Real.log_nonneg hn1) (by linarith))
    have h3 : Real.log ((2 + 1 : ℕ) : ℝ) / ((2 + 1 : ℕ) : ℝ) ≤ 1 := by
      have : Real.log ((2 + 1 : ℕ) : ℝ) ≤ ((2 + 1 : ℕ) : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [div_le_one (by positivity)]
      push_cast at this ⊢
      linarith
    calc _ ≤ 2 * (Real.log ((2 + 1 : ℕ) : ℝ) / ((2 + 1 : ℕ) : ℝ)) := h2
      _ ≤ 2 * 1 := by gcongr
      _ = 2 := by ring

open ArithmeticFunction in
lemma psi_bound (N : ℕ) : ∑ d ∈ Ioc 0 N, vonMangoldt d ≤ (Real.log 4 + 4) * N := by
  have := Chebyshev.psi_le_const_mul_self (x := (N : ℝ)) (by positivity)
  unfold Chebyshev.psi at this
  simpa using this

lemma nat_div_bounds (N d : ℕ) (hd : 0 < d) :
    (N : ℝ) / d - 1 ≤ ((N / d : ℕ) : ℝ) ∧ ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · have h1 : (N : ℝ) < d * (((N / d : ℕ) : ℝ) + 1) := by
      exact_mod_cast Nat.lt_mul_div_succ N hd
    rw [sub_le_iff_le_add, div_le_iff₀ hd']
    linarith
  · exact Nat.cast_div_le

open ArithmeticFunction in
/-- Mertens' first theorem, upper bound. -/
lemma mertens_upper (N : ℕ) (hN : 1 ≤ N) :
    ∑ d ∈ Ioc 0 N, vonMangoldt d / d ≤ Real.log N + (Real.log 4 + 4) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ∑ n ∈ Ioc 0 N, Real.log n = ∑ d ∈ Ioc 0 N, vonMangoldt d * ((N / d : ℕ) : ℝ) := by
    rw [← sum_Ioc_mul_zeta_eq_sum, vonMangoldt_mul_zeta]
    simp [ArithmeticFunction.log_apply]
  have h2 : ∑ n ∈ Ioc 0 N, Real.log n ≤ N * Real.log N := by
    calc ∑ n ∈ Ioc 0 N, Real.log n ≤ ∑ _n ∈ Ioc 0 N, Real.log N := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_Ioc] at hn
          exact Real.log_le_log (by exact_mod_cast hn.1) (by exact_mod_cast hn.2)
      _ = N * Real.log N := by simp
  have h3 : ∑ d ∈ Ioc 0 N, vonMangoldt d * ((N : ℝ) / d - 1)
      ≤ ∑ d ∈ Ioc 0 N, vonMangoldt d * ((N / d : ℕ) : ℝ) := by
    apply Finset.sum_le_sum
    intro d hd
    rw [Finset.mem_Ioc] at hd
    exact mul_le_mul_of_nonneg_left (nat_div_bounds N d hd.1).1 vonMangoldt_nonneg
  have h4 : ∑ d ∈ Ioc 0 N, vonMangoldt d * ((N : ℝ) / d - 1)
      = N * ∑ d ∈ Ioc 0 N, vonMangoldt d / d - ∑ d ∈ Ioc 0 N, vonMangoldt d := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  have h5 := psi_bound N
  have h6 : N * ∑ d ∈ Ioc 0 N, vonMangoldt d / d ≤ N * (Real.log N + (Real.log 4 + 4)) := by
    nlinarith
  exact le_of_mul_le_mul_left h6 hN'

open ArithmeticFunction in
/-- `d ↦ χ(d) Λ(d) / d` as an arithmetic function. -/
noncomputable def F : ArithmeticFunction ℝ := ⟨fun n => chi8 n * vonMangoldt n / n, by simp⟩

/-- `m ↦ χ(m) / m` as an arithmetic function. -/
noncomputable def G : ArithmeticFunction ℝ := ⟨fun n => chi8 n * (1 / (n : ℝ)), by simp⟩

open ArithmeticFunction in
lemma FG_apply (n : ℕ) : (F * G) n = chi8 n * (Real.log n / n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [ArithmeticFunction.mul_apply]
  have h : ∀ x ∈ n.divisorsAntidiagonal, F x.1 * G x.2 = chi8 n / n * vonMangoldt x.1 := by
    intro x hx
    obtain ⟨hxn, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have h1 : x.1 ≠ 0 := by rintro h; rw [h, zero_mul] at hxn; exact hn0 hxn.symm
    have h2 : x.2 ≠ 0 := by rintro h; rw [h, mul_zero] at hxn; exact hn0 hxn.symm
    have h1' : (x.1 : ℝ) ≠ 0 := by exact_mod_cast h1
    have h2' : (x.2 : ℝ) ≠ 0 := by exact_mod_cast h2
    simp only [F, G, ArithmeticFunction.coe_mk]
    rw [← hxn, chi8_mul]
    push_cast
    field_simp
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum,
    Nat.sum_divisorsAntidiagonal (f := fun a _ => vonMangoldt a), vonMangoldt_sum]
  ring

open ArithmeticFunction in
lemma F_abs (d : ℕ) : |F d| ≤ vonMangoldt d / d := by
  simp only [F, ArithmeticFunction.coe_mk]
  rw [abs_div, abs_mul, abs_of_nonneg (vonMangoldt_nonneg (n := d)), Nat.abs_cast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg d)
  calc |chi8 d| * vonMangoldt d ≤ 1 * vonMangoldt d :=
        mul_le_mul_of_nonneg_right (chi8_abs_le d) vonMangoldt_nonneg
    _ = vonMangoldt d := one_mul _

open ArithmeticFunction in
/-- The sum of `χ(d) Λ(d) / d` is bounded. -/
lemma chi_vm_bound (N : ℕ) :
    |∑ d ∈ Ioc 0 N, chi8 d * vonMangoldt d / d| ≤ 6 * (2 + 2 * (Real.log 4 + 4)) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp; positivity
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hS : ∑ d ∈ Ioc 0 N, chi8 d * vonMangoldt d / d = ∑ d ∈ Ioc 0 N, F d := by
    simp [F]
  rw [hS]
  have hB : B N = ∑ d ∈ Ioc 0 N, F d * A (N / d) := by
    have h1 := sum_Ioc_mul_eq_sum_sum F G N
    have h2 : ∑ n ∈ Ioc 0 N, (F * G) n = B N := by
      unfold B
      exact Finset.sum_congr rfl (fun n _ => FG_apply n)
    rw [← h2, h1]
    apply Finset.sum_congr rfl
    intro d _
    simp [A, G]
  have hdiff : A N * ∑ d ∈ Ioc 0 N, F d - B N = ∑ d ∈ Ioc 0 N, F d * (A N - A (N / d)) := by
    rw [hB, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hterm : ∀ d ∈ Ioc 0 N, |F d * (A N - A (N / d))| ≤ 2 * vonMangoldt d / N := by
    intro d hd
    rw [Finset.mem_Ioc] at hd
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd.1
    have h1 := F_abs d
    have h2 := A_diff (N / d) N (Nat.div_le_self N d)
    have h3 : 2 / (((N / d : ℕ) : ℝ) + 1) ≤ 2 * d / N := by
      have h4 : (N : ℝ) < d * (((N / d : ℕ) : ℝ) + 1) := by
        exact_mod_cast Nat.lt_mul_div_succ N hd.1
      rw [div_le_div_iff₀ (by positivity) hN']
      nlinarith
    rw [abs_mul]
    calc |F d| * |A N - A (N / d)| ≤ (vonMangoldt d / d) * (2 * d / N) :=
          mul_le_mul h1 (h2.trans h3) (abs_nonneg _) (div_nonneg vonMangoldt_nonneg hd'.le)
      _ = 2 * vonMangoldt d / N := by field_simp
  have hsum : |A N * ∑ d ∈ Ioc 0 N, F d - B N| ≤ 2 * (Real.log 4 + 4) := by
    rw [hdiff]
    calc |∑ d ∈ Ioc 0 N, F d * (A N - A (N / d))|
        ≤ ∑ d ∈ Ioc 0 N, |F d * (A N - A (N / d))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Ioc 0 N, 2 * vonMangoldt d / N := Finset.sum_le_sum hterm
      _ = 2 * (∑ d ∈ Ioc 0 N, vonMangoldt d) / N := by
          rw [Finset.mul_sum, Finset.sum_div]
      _ ≤ 2 * ((Real.log 4 + 4) * N) / N := by
          apply div_le_div_of_nonneg_right _ hN'.le
          linarith [psi_bound N]
      _ = 2 * (Real.log 4 + 4) := by field_simp
  have hAS : |A N * ∑ d ∈ Ioc 0 N, F d| ≤ 2 + 2 * (Real.log 4 + 4) := by
    have h1 := B_abs N
    have h2 : A N * ∑ d ∈ Ioc 0 N, F d = (A N * ∑ d ∈ Ioc 0 N, F d - B N) + B N := by ring
    rw [h2]
    calc _ ≤ |A N * ∑ d ∈ Ioc 0 N, F d - B N| + |B N| := abs_add_le _ _
      _ ≤ 2 * (Real.log 4 + 4) + 2 := add_le_add hsum h1
      _ = _ := by ring
  have hA := A_ge N hN
  rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ A N)] at hAS
  have h5 : (1 / 6 : ℝ) * |∑ d ∈ Ioc 0 N, F d| ≤ 2 + 2 * (Real.log 4 + 4) :=
    (mul_le_mul_of_nonneg_right hA (abs_nonneg _)).trans hAS
  linarith

open ArithmeticFunction in
/-- Mertens-type bound for the primes that split in `ℚ(√2)`. -/
lemma main_sum (N : ℕ) (hN : 1 ≤ N) :
    ∑ d ∈ Ioc 0 N, (1 + chi8 d) * vonMangoldt d / d
      ≤ Real.log N + ((Real.log 4 + 4) + 6 * (2 + 2 * (Real.log 4 + 4))) := by
  have h1 := mertens_upper N hN
  have h2 := (abs_le.mp (chi_vm_bound N)).2
  have h3 : ∑ d ∈ Ioc 0 N, (1 + chi8 d) * vonMangoldt d / d
      = ∑ d ∈ Ioc 0 N, vonMangoldt d / d + ∑ d ∈ Ioc 0 N, chi8 d * vonMangoldt d / d := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [h3]
  linarith

lemma chi8_pow (p k : ℕ) (hp : chi8 p = 1) : chi8 (p ^ k) = 1 := by
  induction k with
  | zero => simp [chi8]
  | succ k ih => rw [pow_succ, chi8_mul, ih, hp, one_mul]

lemma four_not_dvd (y : ℕ) (hy : 2 ≤ y) : ¬ 4 ∣ y ^ 2 - 2 := by
  rintro ⟨k, hk⟩
  have h2 : 4 ≤ y ^ 2 := by nlinarith
  have h3 : y ^ 2 % 4 = 2 := by omega
  have h4 : y ^ 2 % 4 = (y % 4) ^ 2 % 4 := Nat.pow_mod y 2 4
  have h5 : y % 4 < 4 := Nat.mod_lt _ (by norm_num)
  rw [h4] at h3
  generalize y % 4 = a at h3 h5
  interval_cases a <;> omega

/-- Two solutions of `y² ≡ 2` modulo a prime power differ by a sign. -/
lemma sol_pm (p k : ℕ) (hp : p.Prime) (hk : 0 < k) (y1 y2 : ℕ) (h1 : 2 ≤ y1) (h2 : 2 ≤ y2)
    (d1 : p ^ k ∣ y1 ^ 2 - 2) (d2 : p ^ k ∣ y2 ^ 2 - 2) :
    ((p ^ k : ℕ) : ℤ) ∣ (y1 : ℤ) - y2 ∨ ((p ^ k : ℕ) : ℤ) ∣ (y1 : ℤ) + y2 := by
  have s1 : 2 ≤ y1 ^ 2 := by nlinarith
  have s2 : 2 ≤ y2 ^ 2 := by nlinarith
  have e1 : ((p ^ k : ℕ) : ℤ) ∣ (y1 : ℤ) ^ 2 - 2 := by
    have := Int.natCast_dvd_natCast.mpr d1
    rwa [Nat.cast_sub s1, Nat.cast_pow, Nat.cast_ofNat] at this
  have e2 : ((p ^ k : ℕ) : ℤ) ∣ (y2 : ℤ) ^ 2 - 2 := by
    have := Int.natCast_dvd_natCast.mpr d2
    rwa [Nat.cast_sub s2, Nat.cast_pow, Nat.cast_ofNat] at this
  have e3 : ((p ^ k : ℕ) : ℤ) ∣ ((y1 : ℤ) - y2) * ((y1 : ℤ) + y2) := by
    have := dvd_sub e1 e2
    have e : ((y1 : ℤ) - y2) * ((y1 : ℤ) + y2) = ((y1 : ℤ) ^ 2 - 2) - ((y2 : ℤ) ^ 2 - 2) := by ring
    rw [e]; exact this
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rw [Nat.cast_pow] at e3 ⊢
  by_cases hd : (p : ℤ) ∣ (y1 : ℤ) - y2
  · by_cases hs : (p : ℤ) ∣ (y1 : ℤ) + y2
    · -- then p ∣ 2 * y1, so p = 2
      have h2y : (p : ℤ) ∣ 2 * (y1 : ℤ) := by
        have := dvd_add hd hs
        have e : (y1 : ℤ) - y2 + ((y1 : ℤ) + y2) = 2 * y1 := by ring
        rwa [e] at this
      have hp2 : p = 2 := by
        rcases hpZ.dvd_or_dvd h2y with h | h
        · have : p ∣ 2 := by exact_mod_cast h
          exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
        · -- p ∣ y1, so p ∣ y1^2, so p ∣ 2
          have hpy : p ∣ y1 := by exact_mod_cast h
          have hpd : p ∣ y1 ^ 2 - 2 := dvd_trans (dvd_pow_self p hk.ne') d1
          have hpy2 : p ∣ y1 ^ 2 := dvd_pow hpy two_ne_zero
          have : p ∣ 2 := by
            have := (Nat.dvd_sub_iff_right s1 hpy2).mp hpd
            exact this
          exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
      subst hp2
      have hk1 : k = 1 := by
        by_contra hne
        have hk2 : 2 ≤ k := by omega
        have : 4 ∣ y1 ^ 2 - 2 := dvd_trans (by
          have : (2 : ℕ) ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hk2
          simpa using this) d1
        exact four_not_dvd y1 h1 this
      subst hk1
      left
      simpa using hd
    · left
      exact hpZ.pow_dvd_of_dvd_mul_right k hs e3
  · right
    exact hpZ.pow_dvd_of_dvd_mul_left k hd e3

/-- A residue class has at most `X / n + 1` elements in `(X, 2X]`. -/
lemma class_card (X n c : ℕ) (_hn : 0 < n) :
    (((Ioc X (2 * X)).filter (fun y => y ≡ c [MOD n])).card : ℝ) ≤ (X : ℝ) / n + 1 := by
  have h : ((Ioc X (2 * X)).filter (fun y => y ≡ c [MOD n])).card ≤ X / n + 1 := by
    calc _ ≤ (Finset.range (X / n + 1)).card := by
          apply Finset.card_le_card_of_injOn (fun y => (y - X - 1) / n)
          · intro y hy
            rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hy
            rw [Finset.mem_coe, Finset.mem_range]
            apply Nat.lt_succ_of_le
            apply Nat.div_le_div_right
            omega
          · intro y hy y' hy' heq
            rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hy hy'
            simp only at heq
            have hyy : y ≡ y' [MOD n] := hy.2.trans hy'.2.symm
            have e1 : y = (y - X - 1) + (X + 1) := by omega
            have e2 : y' = (y' - X - 1) + (X + 1) := by omega
            rw [e1, e2] at hyy
            have hmod : (y - X - 1) % n = (y' - X - 1) % n := Nat.ModEq.add_right_cancel' _ hyy
            have h3 := Nat.div_add_mod (y - X - 1) n
            have h4 := Nat.div_add_mod (y' - X - 1) n
            rw [heq, hmod] at h3
            omega
      _ = X / n + 1 := Finset.card_range _
  calc (((Ioc X (2 * X)).filter (fun y => y ≡ c [MOD n])).card : ℝ)
      ≤ ((X / n + 1 : ℕ) : ℝ) := by exact_mod_cast h
    _ = ((X / n : ℕ) : ℝ) + 1 := by push_cast; ring
    _ ≤ (X : ℝ) / n + 1 := by gcongr; exact Nat.cast_div_le

/-- The basic count: solutions of `d ∣ y² - 2` in a class modulo `m` coprime to the prime
power `d` lie in at most two classes modulo `m * d`. -/
lemma count_le (X m a p k : ℕ) (hX : 2 ≤ X) (hm : 0 < m) (hp : p.Prime) (hk : 0 < k)
    (hcop : Nat.Coprime m (p ^ k)) :
    (((Ioc X (2 * X)).filter (fun y => y ≡ a [MOD m] ∧ p ^ k ∣ y ^ 2 - 2)).card : ℝ)
      ≤ 2 * ((X : ℝ) / ((m * p ^ k : ℕ) : ℝ) + 1) := by
  set d := p ^ k with hd
  have hdpos : 0 < d := pos_of_ne_zero (pow_ne_zero k hp.ne_zero)
  set S := (Ioc X (2 * X)).filter (fun y => y ≡ a [MOD m] ∧ d ∣ y ^ 2 - 2) with hS
  have hmd : 0 < m * d := Nat.mul_pos hm hdpos
  rcases S.eq_empty_or_nonempty with hempty | ⟨y0, hy0⟩
  · rw [hempty]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
  have hy0' := hy0
  rw [hS, Finset.mem_filter, Finset.mem_Ioc] at hy0'
  set S2 := S.filter (fun y => ¬ y ≡ y0 [MOD m * d]) with hS2
  have hsub : S ⊆ (Ioc X (2 * X)).filter (fun y => y ≡ y0 [MOD m * d]) ∪ S2 := by
    intro y hy
    by_cases h : y ≡ y0 [MOD m * d]
    · apply Finset.mem_union_left
      rw [Finset.mem_filter]
      exact ⟨(Finset.mem_filter.mp hy).1, h⟩
    · apply Finset.mem_union_right
      rw [hS2, Finset.mem_filter]
      exact ⟨hy, h⟩
  have hS2card : (S2.card : ℝ) ≤ (X : ℝ) / ((m * d : ℕ) : ℝ) + 1 := by
    rcases S2.eq_empty_or_nonempty with hempty | ⟨y1, hy1⟩
    · rw [hempty]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
    have key : ∀ y ∈ S2, ((d : ℕ) : ℤ) ∣ (y : ℤ) + y0 ∧ y ≡ a [MOD m] := by
      intro y hy
      rw [hS2, Finset.mem_filter] at hy
      obtain ⟨hyS, hne⟩ := hy
      rw [hS, Finset.mem_filter, Finset.mem_Ioc] at hyS
      have hym : y ≡ y0 [MOD m] := hyS.2.1.trans hy0'.2.1.symm
      have hnd : ¬ y ≡ y0 [MOD d] := by
        intro h
        exact hne ((Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hym, h⟩)
      rcases sol_pm p k hp hk y y0 (by omega) (by omega) hyS.2.2 hy0'.2.2 with h | h
      · exfalso
        apply hnd
        rw [Nat.modEq_iff_dvd]
        have : ((d : ℕ) : ℤ) ∣ -((y : ℤ) - y0) := (dvd_neg).mpr h
        rwa [neg_sub] at this
      · exact ⟨h, hyS.2.1⟩
    have hsub2 : S2 ⊆ (Ioc X (2 * X)).filter (fun y => y ≡ y1 [MOD m * d]) := by
      intro y hy
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).1
      · obtain ⟨h1, h2⟩ := key y hy
        obtain ⟨h3, h4⟩ := key y1 hy1
        apply (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
        refine ⟨h2.trans h4.symm, ?_⟩
        rw [Nat.modEq_iff_dvd]
        have := dvd_sub h3 h1
        have e : (y1 : ℤ) + y0 - ((y : ℤ) + y0) = (y1 : ℤ) - y := by ring
        rwa [e] at this
    calc (S2.card : ℝ) ≤ (((Ioc X (2 * X)).filter (fun y => y ≡ y1 [MOD m * d])).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub2
      _ ≤ _ := class_card X (m * d) y1 hmd
  calc (S.card : ℝ)
      ≤ ((((Ioc X (2 * X)).filter (fun y => y ≡ y0 [MOD m * d])) ∪ S2).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (((Ioc X (2 * X)).filter (fun y => y ≡ y0 [MOD m * d])).card : ℝ) + (S2.card : ℝ) := by
        exact_mod_cast Finset.card_union_le _ _
    _ ≤ ((X : ℝ) / ((m * d : ℕ) : ℝ) + 1) + ((X : ℝ) / ((m * d : ℕ) : ℝ) + 1) :=
        add_le_add (class_card X (m * d) y0 hmd) hS2card
    _ = _ := by ring

/-- The weight: an upper bound for the number of classes of solutions of `d ∣ y² - 2`. -/
noncomputable def u (d : ℕ) : ℝ := 1 + chi8 d + (if d = 2 then 1 else 0)

lemma u_nonneg (d : ℕ) : 0 ≤ u d := by
  unfold u
  have := chi8_ge d
  split_ifs <;> linarith

lemma u_le_two (d : ℕ) : u d ≤ 2 := by
  unfold u
  split_ifs with h
  · subst h
    have : chi8 2 = 0 := by simp [chi8]
    rw [this]; norm_num
  · have := chi8_le d
    linarith

lemma count_u (X m a d : ℕ) (hX : 2 ≤ X) (hm : 0 < m) (hd : IsPrimePow d)
    (hcop : Nat.Coprime m d) :
    (((Ioc X (2 * X)).filter (fun y => y ≡ a [MOD m] ∧ d ∣ y ^ 2 - 2)).card : ℝ)
      ≤ u d * ((X : ℝ) / ((m * d : ℕ) : ℝ) + 1) := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff d).mp hd
  rcases ((Ioc X (2 * X)).filter
      (fun y => y ≡ a [MOD m] ∧ p ^ k ∣ y ^ 2 - 2)).eq_empty_or_nonempty with hempty | ⟨y0, hy0⟩
  · rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (u_nonneg _) (by positivity)
  rw [Finset.mem_filter, Finset.mem_Ioc] at hy0
  have hy2 : 2 ≤ y0 := by omega
  have hu : u (p ^ k) = 2 := by
    by_cases hp2 : p = 2
    · subst hp2
      have hk1 : k = 1 := by
        by_contra hne
        have hk2 : 2 ≤ k := by omega
        have : 4 ∣ y0 ^ 2 - 2 := dvd_trans (by
          have : (2 : ℕ) ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hk2
          simpa using this) hy0.2.2
        exact four_not_dvd y0 hy2 this
      subst hk1
      simp [u, chi8]
      norm_num
    · have : Fact p.Prime := ⟨hp⟩
      have hpd : p ∣ y0 ^ 2 - 2 := dvd_trans (dvd_pow_self p hk.ne') hy0.2.2
      have hs : 2 ≤ y0 ^ 2 := by nlinarith
      have hz : ((y0 ^ 2 - 2 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpd
      rw [Nat.cast_sub hs, Nat.cast_pow, Nat.cast_ofNat, sub_eq_zero] at hz
      have hsq : IsSquare (2 : ZMod p) := ⟨(y0 : ZMod p), by rw [← hz]; ring⟩
      have h8 := (ZMod.exists_sq_eq_two_iff hp2).mp hsq
      have hchi : chi8 p = 1 := by
        unfold chi8
        rw [if_pos h8]
      have hne2 : p ^ k ≠ 2 := by
        intro h
        have : p ∣ 2 := by rw [← h]; exact dvd_pow_self p hk.ne'
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
      unfold u
      rw [chi8_pow p k hchi, if_neg hne2]
      norm_num
  rw [hu]
  exact count_le X m a p k hX hm hp hk hcop

lemma count_all (X d : ℕ) (hX : 2 ≤ X) (hd : IsPrimePow d) :
    (((Ioc X (2 * X)).filter (fun y => d ∣ y ^ 2 - 2)).card : ℝ)
      ≤ u d * ((X : ℝ) / (d : ℝ) + 1) := by
  have h := count_u X 1 0 d hX one_pos hd (Nat.coprime_one_left d)
  have e : (Ioc X (2 * X)).filter (fun y => y ≡ 0 [MOD 1] ∧ d ∣ y ^ 2 - 2)
      = (Ioc X (2 * X)).filter (fun y => d ∣ y ^ 2 - 2) := by
    apply Finset.filter_congr
    intro y _
    simp [Nat.modEq_one]
  rw [e] at h
  simpa using h

open ArithmeticFunction in
/-- The von Mangoldt weight restricted to primes at most `N` and proper prime powers. -/
noncomputable def g (N d : ℕ) : ℝ := if d ≤ N ∨ ¬ d.Prime then vonMangoldt d else 0

open ArithmeticFunction in
lemma g_nonneg (N d : ℕ) : 0 ≤ g N d := by
  unfold g
  split_ifs
  · exact vonMangoldt_nonneg
  · exact le_refl _

open ArithmeticFunction in
lemma g_le (N d : ℕ) : g N d ≤ vonMangoldt d := by
  unfold g
  split_ifs
  · exact le_refl _
  · exact vonMangoldt_nonneg

open ArithmeticFunction in
lemma g_eq_zero (N d : ℕ) (h : ¬ IsPrimePow d) : g N d = 0 := by
  have h1 := g_le N d
  have h2 := g_nonneg N d
  rw [vonMangoldt_eq_zero_iff.mpr h] at h1
  linarith

/-- The mass of `y² - 2` on primes at most `N`. -/
noncomputable def s (N y : ℕ) : ℝ := ∑ d ∈ (y ^ 2 - 2).divisors, g N d

open ArithmeticFunction in
lemma s_eq_log (N y : ℕ) (h : ∀ p : ℕ, p.Prime → p ∣ y ^ 2 - 2 → p ≤ N) :
    s N y = Real.log ((y ^ 2 - 2 : ℕ) : ℝ) := by
  unfold s
  rw [← vonMangoldt_sum]
  apply Finset.sum_congr rfl
  intro d hd
  unfold g
  rw [if_pos]
  by_cases hdp : d.Prime
  · left; exact h d hdp (Nat.dvd_of_mem_divisors hd)
  · right; exact hdp

open ArithmeticFunction in
lemma s_ge (N y : ℕ) (hy : 2 ≤ y) (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime ∧ q ≤ N) :
    ∑ q ∈ Q.filter (fun q => q ∣ y ^ 2 - 2), Real.log q ≤ s N y := by
  have hne : y ^ 2 - 2 ≠ 0 := by
    have : 4 ≤ y ^ 2 := by nlinarith
    omega
  have hsub : Q.filter (fun q => q ∣ y ^ 2 - 2) ⊆ (y ^ 2 - 2).divisors := by
    intro q hq
    rw [Finset.mem_filter] at hq
    exact Nat.mem_divisors.mpr ⟨hq.2, hne⟩
  have heq : ∑ q ∈ Q.filter (fun q => q ∣ y ^ 2 - 2), Real.log q
      = ∑ q ∈ Q.filter (fun q => q ∣ y ^ 2 - 2), g N q := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨hqp, hqN⟩ := hQ q hq.1
    unfold g
    rw [if_pos (Or.inl hqN), vonMangoldt_apply_prime hqp]
  rw [heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => g_nonneg N d)

lemma sum_s (N M : ℕ) (C : Finset ℕ) (hC : ∀ y ∈ C, y ^ 2 - 2 ≠ 0 ∧ y ^ 2 - 2 ≤ M) :
    ∑ y ∈ C, s N y
      = ∑ d ∈ Ioc 0 M, g N d * ((C.filter (fun y => d ∣ y ^ 2 - 2)).card : ℝ) := by
  have h1 : ∀ y ∈ C, s N y = ∑ d ∈ Ioc 0 M, if d ∣ y ^ 2 - 2 then g N d else 0 := by
    intro y hy
    obtain ⟨hne, hle⟩ := hC y hy
    unfold s
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext d
    rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hne),
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hd).trans hle⟩, hd⟩
    · rintro ⟨_, hd⟩
      exact ⟨hd, hne⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  ring

open ArithmeticFunction in
lemma np_nonneg (d : ℕ) : (0 : ℝ) ≤ (if ¬ d.Prime then vonMangoldt d else 0) := by
  by_cases h : d.Prime
  · rw [if_neg (not_not.mpr h)]
  · rw [if_pos h]; exact vonMangoldt_nonneg

open ArithmeticFunction in
/-- Proper prime powers up to `N²` carry mass `O(N)`. -/
lemma nonprime_sum : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ N : ℕ,
    ∑ d ∈ Ioc 0 (N ^ 2), (if ¬ d.Prime then vonMangoldt d else 0) ≤ Cs * N := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have key : ∀ N : ℕ,
      ∑ d ∈ Ioc 0 (N ^ 2), (if ¬ d.Prime then vonMangoldt d else 0) ≤ C * N := by
    intro N
    have h := hC (((N ^ 2 : ℕ) : ℝ))
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast] at h
    rw [Finset.sum_filter] at h
    have e : Real.sqrt (((N ^ 2 : ℕ) : ℝ)) = N := by
      push_cast
      exact Real.sqrt_sq (Nat.cast_nonneg N)
    rw [e] at h
    exact h
  refine ⟨C, ?_, key⟩
  have h1 := key 1
  have h0 : (0 : ℝ) ≤ ∑ d ∈ Ioc 0 (1 ^ 2), (if ¬ d.Prime then vonMangoldt d else 0) := by
    apply Finset.sum_nonneg
    intro d _
    exact np_nonneg d
  simp only [Nat.cast_one, mul_one] at h1
  linarith

open ArithmeticFunction in
/-- First moment: the weights `g u / d` sum to at most `log N + O(1)`. -/
lemma gu_div_bound : ∃ K5 : ℝ, 0 ≤ K5 ∧ ∀ N : ℕ, 2 ≤ N →
    ∑ d ∈ Ioc 0 (N ^ 2), g N d * u d / d ≤ Real.log N + K5 := by
  obtain ⟨Cs, hCs0, hCs⟩ := nonprime_sum
  refine ⟨((Real.log 4 + 4) + 6 * (2 + 2 * (Real.log 4 + 4))) + Real.log 2 / 2 + 2 * Cs, ?_, ?_⟩
  · have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  intro N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNsq : N ≤ N ^ 2 := by nlinarith
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le N) hNsq]
  have hfirst : ∑ d ∈ Ioc 0 N, g N d * u d / d
      ≤ Real.log N + ((Real.log 4 + 4) + 6 * (2 + 2 * (Real.log 4 + 4))) + Real.log 2 / 2 := by
    have h1 := main_sum N (by omega)
    have h2 : ∑ d ∈ Ioc 0 N, g N d * u d / d
        = ∑ d ∈ Ioc 0 N, (1 + chi8 d) * vonMangoldt d / d
          + ∑ d ∈ Ioc 0 N, (if d = 2 then vonMangoldt d / d else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mem_Ioc] at hd
      unfold g u
      rw [if_pos (Or.inl hd.2)]
      split_ifs <;> ring
    have h3 : ∑ d ∈ Ioc 0 N, (if d = 2 then vonMangoldt d / d else 0) = Real.log 2 / 2 := by
      rw [Finset.sum_ite_eq' (Ioc 0 N) 2 (fun d => vonMangoldt d / d)]
      rw [if_pos (by rw [Finset.mem_Ioc]; omega), vonMangoldt_apply_prime Nat.prime_two]
      norm_num
    rw [h2, h3]
    linarith
  have hsecond : ∑ d ∈ Ioc N (N ^ 2), g N d * u d / d ≤ 2 * Cs := by
    have hterm : ∀ d ∈ Ioc N (N ^ 2), g N d * u d / d
        ≤ (2 / N) * (if ¬ d.Prime then vonMangoldt d else 0) := by
      intro d hd
      rw [Finset.mem_Ioc] at hd
      have hd' : (N : ℝ) < d := by exact_mod_cast hd.1
      have hgd : g N d = (if ¬ d.Prime then vonMangoldt d else 0) := by
        unfold g
        by_cases hp : d.Prime
        · rw [if_neg (not_or.mpr ⟨not_le.mpr hd.1, not_not.mpr hp⟩), if_neg (not_not.mpr hp)]
        · rw [if_pos (Or.inr hp), if_pos hp]
      have hg0 := g_nonneg N d
      rw [← hgd]
      rw [div_le_iff₀ (by linarith)]
      have h4 : g N d * u d ≤ g N d * 2 := mul_le_mul_of_nonneg_left (u_le_two d) hg0
      have h5 : g N d * 2 ≤ 2 / N * g N d * d := by
        have : (1 : ℝ) ≤ d / N := by rw [le_div_iff₀ hN']; linarith
        calc g N d * 2 = 2 * g N d * 1 := by ring
          _ ≤ 2 * g N d * (d / N) := by
              apply mul_le_mul_of_nonneg_left this
              positivity
          _ = 2 / N * g N d * d := by field_simp
      linarith
    calc ∑ d ∈ Ioc N (N ^ 2), g N d * u d / d
        ≤ ∑ d ∈ Ioc N (N ^ 2), (2 / N) * (if ¬ d.Prime then vonMangoldt d else 0) :=
          Finset.sum_le_sum hterm
      _ = (2 / N) * ∑ d ∈ Ioc N (N ^ 2), (if ¬ d.Prime then vonMangoldt d else 0) := by
          rw [Finset.mul_sum]
      _ ≤ (2 / N) * ∑ d ∈ Ioc 0 (N ^ 2), (if ¬ d.Prime then vonMangoldt d else 0) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro d hd
            rw [Finset.mem_Ioc] at hd ⊢
            omega
          · intro d _ _
            exact np_nonneg d
      _ ≤ (2 / N) * (Cs * N) := mul_le_mul_of_nonneg_left (hCs N) (by positivity)
      _ = 2 * Cs := by field_simp
  linarith

open ArithmeticFunction in
/-- The weights `g u` sum to `O(N)`. -/
lemma gu_bound : ∃ K6 : ℝ, 0 ≤ K6 ∧ ∀ N : ℕ, 1 ≤ N →
    ∑ d ∈ Ioc 0 (N ^ 2), g N d * u d ≤ K6 * N := by
  obtain ⟨Cs, hCs0, hCs⟩ := nonprime_sum
  refine ⟨2 * ((Real.log 4 + 4) + Cs), ?_, ?_⟩
  · have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  intro N hN
  have hNsq : N ≤ N ^ 2 := by nlinarith
  have hterm : ∀ d ∈ Ioc 0 (N ^ 2), g N d * u d
      ≤ 2 * ((if d ≤ N then vonMangoldt d else 0) + (if ¬ d.Prime then vonMangoldt d else 0)) := by
    intro d _
    have hg0 := g_nonneg N d
    have h1 : g N d ≤ (if d ≤ N then vonMangoldt d else 0)
        + (if ¬ d.Prime then vonMangoldt d else 0) := by
      unfold g
      have hv : (0 : ℝ) ≤ vonMangoldt d := vonMangoldt_nonneg
      by_cases h1 : d ≤ N <;> by_cases h2 : d.Prime <;> simp [h1, h2, hv]
    calc g N d * u d ≤ g N d * 2 := mul_le_mul_of_nonneg_left (u_le_two d) hg0
      _ ≤ _ := by linarith
  have hA : ∑ d ∈ Ioc 0 (N ^ 2), (if d ≤ N then vonMangoldt d else 0)
      = ∑ d ∈ Ioc 0 N, vonMangoldt d := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext d
    rw [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ioc]
    omega
  calc ∑ d ∈ Ioc 0 (N ^ 2), g N d * u d
      ≤ ∑ d ∈ Ioc 0 (N ^ 2), 2 * ((if d ≤ N then vonMangoldt d else 0)
          + (if ¬ d.Prime then vonMangoldt d else 0)) := Finset.sum_le_sum hterm
    _ = 2 * (∑ d ∈ Ioc 0 N, vonMangoldt d
          + ∑ d ∈ Ioc 0 (N ^ 2), (if ¬ d.Prime then vonMangoldt d else 0)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, hA]
    _ ≤ 2 * ((Real.log 4 + 4) * N + Cs * N) := by
        have := psi_bound N
        have := hCs N
        linarith
    _ = _ := by ring


/-- Mass of a residue class, split into moduli coprime to `m` and the rest. -/
lemma mass_class (X m a : ℕ) (hX : 2 ≤ X) (hm : 0 < m) :
    ∑ y ∈ (Ioc X (2 * X)).filter (fun y => y ≡ a [MOD m]), s (2 * X + 1) y
      ≤ ∑ d ∈ Ioc 0 ((2 * X + 1) ^ 2),
          (if Nat.Coprime m d then
            g (2 * X + 1) d * u d * ((X : ℝ) / ((m * d : ℕ) : ℝ) + 1)
          else g (2 * X + 1) d
            * (((Ioc X (2 * X)).filter (fun y => d ∣ y ^ 2 - 2)).card : ℝ)) := by
  have hC : ∀ y ∈ (Ioc X (2 * X)).filter (fun y => y ≡ a [MOD m]),
      y ^ 2 - 2 ≠ 0 ∧ y ^ 2 - 2 ≤ (2 * X + 1) ^ 2 := by
    intro y hy
    rw [Finset.mem_filter, Finset.mem_Ioc] at hy
    have h1 : 3 ≤ y := by omega
    have h2 : 9 ≤ y ^ 2 := by nlinarith
    have h3 : y ^ 2 ≤ (2 * X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  rw [sum_s (2 * X + 1) ((2 * X + 1) ^ 2) _ hC]
  apply Finset.sum_le_sum
  intro d _
  by_cases hpp : IsPrimePow d
  · by_cases hcop : Nat.Coprime m d
    · rw [if_pos hcop, Finset.filter_filter, mul_assoc]
      exact mul_le_mul_of_nonneg_left (count_u X m a d hX hm hpp hcop) (g_nonneg _ _)
    · rw [if_neg hcop]
      apply mul_le_mul_of_nonneg_left _ (g_nonneg _ _)
      exact_mod_cast Finset.card_le_card
        (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
  · rw [g_eq_zero _ _ hpp]
    split_ifs <;> simp

lemma mass_class_bound (K5 K6 : ℝ)
    (h5 : ∀ N : ℕ, 2 ≤ N → ∑ d ∈ Ioc 0 (N ^ 2), g N d * u d / d ≤ Real.log N + K5)
    (h6 : ∀ N : ℕ, 1 ≤ N → ∑ d ∈ Ioc 0 (N ^ 2), g N d * u d ≤ K6 * N)
    (X m a : ℕ) (hX : 2 ≤ X) (hm : 0 < m) :
    ∑ y ∈ (Ioc X (2 * X)).filter (fun y => y ≡ a [MOD m]), s (2 * X + 1) y
      ≤ (X : ℝ) / m * (Real.log ((2 * X + 1 : ℕ) : ℝ) + K5) + K6 * ((2 * X + 1 : ℕ) : ℝ)
        + ∑ d ∈ Ioc 0 ((2 * X + 1) ^ 2),
            (if Nat.Coprime m d then (0 : ℝ)
             else g (2 * X + 1) d
              * (((Ioc X (2 * X)).filter (fun y => d ∣ y ^ 2 - 2)).card : ℝ)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  refine (mass_class X m a hX hm).trans ?_
  have hterm : ∀ d ∈ Ioc 0 ((2 * X + 1) ^ 2),
      (if Nat.Coprime m d then
            g (2 * X + 1) d * u d * ((X : ℝ) / ((m * d : ℕ) : ℝ) + 1)
          else g (2 * X + 1) d
            * (((Ioc X (2 * X)).filter (fun y => d ∣ y ^ 2 - 2)).card : ℝ))
      ≤ ((X : ℝ) / m * (g (2 * X + 1) d * u d / d) + g (2 * X + 1) d * u d)
        + (if Nat.Coprime m d then (0 : ℝ)
             else g (2 * X + 1) d
              * (((Ioc X (2 * X)).filter (fun y => d ∣ y ^ 2 - 2)).card : ℝ)) := by
    intro d hd
    rw [Finset.mem_Ioc] at hd
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd.1
    have hgu : 0 ≤ g (2 * X + 1) d * u d := mul_nonneg (g_nonneg _ _) (u_nonneg _)
    by_cases hcop : Nat.Coprime m d
    · rw [if_pos hcop, if_pos hcop]
      have e : g (2 * X + 1) d * u d * ((X : ℝ) / ((m * d : ℕ) : ℝ) + 1)
          = (X : ℝ) / m * (g (2 * X + 1) d * u d / d) + g (2 * X + 1) d * u d := by
        push_cast
        field_simp
      linarith
    · rw [if_neg hcop, if_neg hcop]
      have : 0 ≤ (X : ℝ) / m * (g (2 * X + 1) d * u d / d) :=
        mul_nonneg (by positivity) (div_nonneg hgu hd'.le)
      linarith
  have h5' := h5 (2 * X + 1) (by omega)
  have h6' := h6 (2 * X + 1) (by omega)
  have hxm : (0 : ℝ) ≤ (X : ℝ) / m := by positivity
  calc _ ≤ ∑ d ∈ Ioc 0 ((2 * X + 1) ^ 2),
          (((X : ℝ) / m * (g (2 * X + 1) d * u d / d) + g (2 * X + 1) d * u d)
          + (if Nat.Coprime m d then (0 : ℝ)
             else g (2 * X + 1) d
              * (((Ioc X (2 * X)).filter (fun y => d ∣ y ^ 2 - 2)).card : ℝ))) :=
        Finset.sum_le_sum hterm
    _ = (X : ℝ) / m * ∑ d ∈ Ioc 0 ((2 * X + 1) ^ 2), g (2 * X + 1) d * u d / d
          + ∑ d ∈ Ioc 0 ((2 * X + 1) ^ 2), g (2 * X + 1) d * u d
          + ∑ d ∈ Ioc 0 ((2 * X + 1) ^ 2),
            (if Nat.Coprime m d then (0 : ℝ)
             else g (2 * X + 1) d
              * (((Ioc X (2 * X)).filter (fun y => d ∣ y ^ 2 - 2)).card : ℝ)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left h5' hxm
        linarith

lemma geom_bound (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (L : ℕ) :
    ∑ k ∈ Icc 1 L, r ^ k ≤ 2 * r := by
  have key : ∀ L : ℕ, ∑ k ∈ Icc 1 L, r ^ k + 2 * r ^ (L + 1) ≤ 2 * r := by
    intro L
    induction L with
    | zero => simp
    | succ L ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have h1 : 0 ≤ r ^ (L + 1) := pow_nonneg hr0 _
      have h2 : r ^ (L + 1 + 1) = r ^ (L + 1) * r := pow_succ _ _
      nlinarith [mul_nonneg h1 (by linarith : (0 : ℝ) ≤ 1 - 2 * r)]
  have h1 := key L
  have h2 : 0 ≤ r ^ (L + 1) := pow_nonneg hr0 _
  linarith

open ArithmeticFunction in
/-- The part of the mass of a class modulo `q` carried by powers of `q` itself. -/
lemma NC_bound (X q : ℕ) (hX : 2 ≤ X) (hq : q.Prime) :
    ∑ d ∈ Ioc 0 ((2 * X + 1) ^ 2),
        (if Nat.Coprime q d then (0 : ℝ)
         else g (2 * X + 1) d
          * (((Ioc X (2 * X)).filter (fun y => d ∣ y ^ 2 - 2)).card : ℝ))
      ≤ 4 * X * Real.log q / q + 4 * Real.log ((2 * X + 1 : ℕ) : ℝ) := by
  set N := 2 * X + 1 with hN
  set L := Nat.log q (N ^ 2) with hL
  have hq1 : 1 < q := hq.one_lt
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
  have hk0 : ∀ k : ℕ, 0 ≤ 2 * Real.log q * ((X : ℝ) / (q : ℝ) ^ k + 1) := by
    intro k
    exact mul_nonneg (mul_nonneg (by norm_num) hlogq) (by positivity)
  have hterm : ∀ d ∈ Ioc 0 (N ^ 2),
      (if Nat.Coprime q d then (0 : ℝ)
         else g N d * (((Ioc X (2 * X)).filter (fun y => d ∣ y ^ 2 - 2)).card : ℝ))
      ≤ ∑ k ∈ Icc 1 L,
          (if d = q ^ k then 2 * Real.log q * ((X : ℝ) / (q : ℝ) ^ k + 1) else 0) := by
    intro d hd
    have hnn : (0 : ℝ) ≤ ∑ k ∈ Icc 1 L,
          (if d = q ^ k then 2 * Real.log q * ((X : ℝ) / (q : ℝ) ^ k + 1) else 0) := by
      apply Finset.sum_nonneg
      intro k _
      split_ifs
      · exact hk0 k
      · exact le_refl _
    by_cases hcop : Nat.Coprime q d
    · rw [if_pos hcop]; exact hnn
    rw [if_neg hcop]
    by_cases hpp : IsPrimePow d
    · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff d).mp hpp
      have hpq : p = q := by
        by_contra hne
        exact hcop (((Nat.coprime_primes hq hp).mpr (Ne.symm hne)).pow_right k)
      subst hpq
      have hkL : k ≤ L := Nat.le_log_of_pow_le hq1 (Finset.mem_Ioc.mp hd).2
      have hcount := count_all X (p ^ k) hX hpp
      have hgl : g N (p ^ k) ≤ Real.log p := by
        refine (g_le _ _).trans ?_
        rw [vonMangoldt_apply_pow hk.ne', vonMangoldt_apply_prime hp]
      have hc2 : (((Ioc X (2 * X)).filter (fun y => p ^ k ∣ y ^ 2 - 2)).card : ℝ)
          ≤ 2 * ((X : ℝ) / (p : ℝ) ^ k + 1) := by
        refine hcount.trans ?_
        push_cast
        exact mul_le_mul_of_nonneg_right (u_le_two _) (by positivity)
      calc g N (p ^ k) * (((Ioc X (2 * X)).filter (fun y => p ^ k ∣ y ^ 2 - 2)).card : ℝ)
          ≤ Real.log p * (2 * ((X : ℝ) / (p : ℝ) ^ k + 1)) :=
            mul_le_mul hgl hc2 (Nat.cast_nonneg _) hlogq
        _ = (if p ^ k = p ^ k then 2 * Real.log p * ((X : ℝ) / (p : ℝ) ^ k + 1) else 0) := by
            rw [if_pos rfl]; ring
        _ ≤ _ := Finset.single_le_sum
            (f := fun k' => if p ^ k = p ^ k'
              then 2 * Real.log p * ((X : ℝ) / (p : ℝ) ^ k' + 1) else 0)
            (fun k' _ => by
              split_ifs
              · exact hk0 k'
              · exact le_refl _)
            (Finset.mem_Icc.mpr ⟨hk, hkL⟩)
    · rw [g_eq_zero _ _ hpp, zero_mul]; exact hnn
  have hswap : ∀ k ∈ Icc 1 L, ∑ d ∈ Ioc 0 (N ^ 2),
      (if d = q ^ k then 2 * Real.log q * ((X : ℝ) / (q : ℝ) ^ k + 1) else 0)
      ≤ 2 * Real.log q * X * (1 / (q : ℝ)) ^ k + 2 * Real.log q := by
    intro k _
    rw [Finset.sum_ite_eq' (Ioc 0 (N ^ 2)) (q ^ k)
      (fun _ => 2 * Real.log q * ((X : ℝ) / (q : ℝ) ^ k + 1))]
    have e : 2 * Real.log q * ((X : ℝ) / (q : ℝ) ^ k + 1)
        = 2 * Real.log q * X * (1 / (q : ℝ)) ^ k + 2 * Real.log q := by
      rw [one_div, inv_pow]; ring
    split_ifs
    · rw [e]
    · rw [← e]; exact hk0 k
  have hgeo := geom_bound (1 / (q : ℝ)) (by positivity)
    (by rw [div_le_div_iff₀ hq' (by norm_num)]; linarith) L
  have hLlog : (L : ℝ) * Real.log q ≤ 2 * Real.log ((N : ℕ) : ℝ) := by
    have h1 : q ^ L ≤ N ^ 2 := Nat.pow_log_le_self q (by positivity)
    have h2 : ((q : ℝ)) ^ L ≤ ((N : ℕ) : ℝ) ^ 2 := by exact_mod_cast h1
    have h3 := Real.log_le_log (by positivity) h2
    rw [Real.log_pow, Real.log_pow] at h3
    exact_mod_cast h3
  calc _ ≤ ∑ d ∈ Ioc 0 (N ^ 2), ∑ k ∈ Icc 1 L,
          (if d = q ^ k then 2 * Real.log q * ((X : ℝ) / (q : ℝ) ^ k + 1) else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑ k ∈ Icc 1 L, ∑ d ∈ Ioc 0 (N ^ 2),
          (if d = q ^ k then 2 * Real.log q * ((X : ℝ) / (q : ℝ) ^ k + 1) else 0) :=
        Finset.sum_comm
    _ ≤ ∑ k ∈ Icc 1 L, (2 * Real.log q * X * (1 / (q : ℝ)) ^ k + 2 * Real.log q) :=
        Finset.sum_le_sum hswap
    _ = 2 * Real.log q * X * ∑ k ∈ Icc 1 L, (1 / (q : ℝ)) ^ k + L * (2 * Real.log q) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc,
          nsmul_eq_mul]
        simp
    _ ≤ 2 * Real.log q * X * (2 * (1 / (q : ℝ))) + 2 * (2 * Real.log ((N : ℕ) : ℝ)) := by
        have h1 : 0 ≤ 2 * Real.log q * X := by positivity
        have := mul_le_mul_of_nonneg_left hgeo h1
        linarith
    _ = _ := by ring

/-- A residue class has at least `X / n - 1` elements in `(X, 2X]`. -/
lemma class_card_lower (X n c : ℕ) (hn : 0 < n) :
    (X : ℝ) / n - 1 ≤ (((Ioc X (2 * X)).filter (fun y => y ≡ c [MOD n])).card : ℝ) := by
  have h := Nat.Ioc_filter_modEq_card X (2 * X) hn c
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have h1 : (((2 * X : ℕ) : ℚ) - c) / n - 1 < ⌊(((2 * X : ℕ) : ℚ) - c) / n⌋ :=
    Int.sub_one_lt_floor _
  have h2 : ((⌊((X : ℚ) - c) / n⌋ : ℤ) : ℚ) ≤ ((X : ℚ) - c) / n := Int.floor_le _
  have h3 : (⌊(((2 * X : ℕ) : ℚ) - c) / n⌋ - ⌊((X : ℚ) - c) / n⌋ : ℤ)
      ≤ (((Ioc X (2 * X)).filter (fun y => y ≡ c [MOD n])).card : ℤ) := by
    rw [h]; exact le_max_left _ _
  have h4 : ((⌊(((2 * X : ℕ) : ℚ) - c) / n⌋ - ⌊((X : ℚ) - c) / n⌋ : ℤ) : ℚ)
      ≤ (((Ioc X (2 * X)).filter (fun y => y ≡ c [MOD n])).card : ℚ) := by exact_mod_cast h3
  have h5 : (X : ℚ) / n - 1
      ≤ (((Ioc X (2 * X)).filter (fun y => y ≡ c [MOD n])).card : ℚ) := by
    have e : (((2 * X : ℕ) : ℚ) - c) / n - ((X : ℚ) - c) / n = (X : ℚ) / n := by
      push_cast; field_simp; ring
    push_cast at h4 h1 e ⊢
    linarith
  have h6 : (((X : ℚ) / n - 1 : ℚ) : ℝ)
      ≤ ((((Ioc X (2 * X)).filter (fun y => y ≡ c [MOD n])).card : ℚ) : ℝ) := by
    exact_mod_cast h5
  push_cast at h6
  exact h6

/-- A peak of the largest prime factor function. -/
def peak (y : ℕ) : Prop :=
  Nat.maxPrimeFac (y - 1) < Nat.maxPrimeFac y ∧ Nat.maxPrimeFac (y + 1) < Nat.maxPrimeFac y

instance : DecidablePred peak := fun y => by unfold peak; infer_instance

lemma peak_succ (y : ℕ) (h : peak y) : ¬ peak (y + 1) := by
  intro h'
  have h1 := h.2
  have h2 := h'.1
  rw [Nat.add_sub_cancel] at h2
  omega

/-- At least half of the integers of `(X, 2X]` are not peaks. -/
lemma NP_card (X : ℕ) : X / 2 ≤ ((Ioc X (2 * X)).filter (fun y => ¬ peak y)).card := by
  have h : (Finset.range (X / 2)).card
      ≤ ((Ioc X (2 * X)).filter (fun y => ¬ peak y)).card := by
    apply Finset.card_le_card_of_injOn
      (fun j => if peak (X + 1 + 2 * j) then X + 1 + 2 * j + 1 else X + 1 + 2 * j)
    · intro j hj
      rw [Finset.mem_coe, Finset.mem_range] at hj
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc]
      dsimp only
      by_cases h : peak (X + 1 + 2 * j)
      · rw [if_pos h]
        exact ⟨by omega, peak_succ _ h⟩
      · rw [if_neg h]
        exact ⟨by omega, h⟩
    · intro j _ j' _ heq
      dsimp only at heq
      split_ifs at heq <;> omega
  simpa using h

/-- A non-peak `y` for which `y² - 2` has a prime factor above `y + 1` gives a descending
triple at `n = y² - 2`. -/
lemma triple (y p : ℕ) (hy : 3 ≤ y) (hnp : ¬ peak y) (hp : p.Prime) (hpd : p ∣ y ^ 2 - 2)
    (hbig : y + 1 < p) :
    Nat.maxPrimeFac (y ^ 2 - 2) > Nat.maxPrimeFac (y ^ 2 - 2 + 1) ∧
      Nat.maxPrimeFac (y ^ 2 - 2 + 1) > Nat.maxPrimeFac (y ^ 2 - 2 + 2) := by
  have h9 : 9 ≤ y ^ 2 := by nlinarith
  have hn2 : y ^ 2 - 2 + 2 = y ^ 2 := by omega
  have hn1 : y ^ 2 - 2 + 1 = (y - 1) * (y + 1) := by
    obtain ⟨z, rfl⟩ : ∃ z, y = z + 1 := ⟨y - 1, by omega⟩
    have e : (z + 1) ^ 2 = z * (z + 1 + 1) + 1 := by ring
    have h1 : 1 ≤ z * (z + 1 + 1) := by nlinarith
    rw [Nat.add_sub_cancel, e]
    omega
  have hne : y ^ 2 - 2 ≠ 0 := by omega
  have hP2 : Nat.maxPrimeFac (y ^ 2 - 2 + 2) = Nat.maxPrimeFac y := by
    rw [hn2, Nat.maxPrimeFac_pow two_ne_zero]
  have hP1 : Nat.maxPrimeFac (y ^ 2 - 2 + 1)
      = max (Nat.maxPrimeFac (y - 1)) (Nat.maxPrimeFac (y + 1)) := by
    rw [hn1, Nat.maxPrimeFac_mul (by omega) (by omega)]
  have hPy : (Nat.maxPrimeFac y).Prime := Nat.prime_maxPrimeFac_of_one_lt y (by omega)
  have hdy : Nat.maxPrimeFac y ∣ y := Nat.maxPrimeFac_dvd
  have hne1 : Nat.maxPrimeFac y ≠ Nat.maxPrimeFac (y - 1) := by
    intro h
    have h1 : Nat.maxPrimeFac y ∣ y - 1 := by rw [h]; exact Nat.maxPrimeFac_dvd
    have h2 : Nat.maxPrimeFac y ∣ y - (y - 1) := Nat.dvd_sub hdy h1
    have h3 : y - (y - 1) = 1 := by omega
    rw [h3] at h2
    exact hPy.one_lt.ne' (Nat.dvd_one.mp h2)
  have hne2 : Nat.maxPrimeFac y ≠ Nat.maxPrimeFac (y + 1) := by
    intro h
    have h1 : Nat.maxPrimeFac y ∣ y + 1 := by rw [h]; exact Nat.maxPrimeFac_dvd
    have h2 : Nat.maxPrimeFac y ∣ (y + 1) - y := Nat.dvd_sub h1 hdy
    have h3 : (y + 1) - y = 1 := by omega
    rw [h3] at h2
    exact hPy.one_lt.ne' (Nat.dvd_one.mp h2)
  have hlt : Nat.maxPrimeFac y < max (Nat.maxPrimeFac (y - 1)) (Nat.maxPrimeFac (y + 1)) := by
    unfold peak at hnp
    rw [not_and_or, not_lt, not_lt] at hnp
    rcases hnp with h | h
    · exact lt_of_lt_of_le (lt_of_le_of_ne h hne1) (le_max_left _ _)
    · exact lt_of_lt_of_le (lt_of_le_of_ne h hne2) (le_max_right _ _)
  have hle : max (Nat.maxPrimeFac (y - 1)) (Nat.maxPrimeFac (y + 1)) ≤ y + 1 := by
    apply max_le
    · exact (Nat.maxPrimeFac_le).trans (by omega)
    · exact Nat.maxPrimeFac_le
  have hbigP : p ≤ Nat.maxPrimeFac (y ^ 2 - 2) := Nat.le_maxPrimeFac hne hp hpd
  rw [hP1, hP2]
  constructor
  · show max (Nat.maxPrimeFac (y - 1)) (Nat.maxPrimeFac (y + 1)) < Nat.maxPrimeFac (y ^ 2 - 2)
    omega
  · exact hlt

/-- For a prime `q ≡ 1 (mod 8)` there is a class modulo `q` on which `q ∣ y² - 2`. -/
lemma root_exists (q : ℕ) (hq : q.Prime) (h8 : q % 8 = 1) :
    ∃ a : ℕ, ∀ y : ℕ, y ≡ a [MOD q] → 2 ≤ y → q ∣ y ^ 2 - 2 := by
  have : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := by rintro rfl; norm_num at h8
  obtain ⟨r, hr⟩ := (ZMod.exists_sq_eq_two_iff hq2).mpr (Or.inl h8)
  refine ⟨r.val, fun y hy h2 => ?_⟩
  have hs : 2 ≤ y ^ 2 := by nlinarith
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hs, Nat.cast_pow, Nat.cast_ofNat]
  have hyr : (y : ZMod q) = r := by
    have := (ZMod.natCast_eq_natCast_iff y r.val q).mpr hy
    rwa [ZMod.natCast_zmod_val] at this
  rw [hyr, hr]; ring

lemma zmod8 (i : ℕ) : ((i : ZMod 8) = 1) ↔ i % 8 = 1 := by
  have h := ZMod.natCast_eq_natCast_iff' i 1 8
  rw [Nat.cast_one] at h
  rw [h]

open ArithmeticFunction in
/-- The sum of `log q / q` over primes `q ≡ 1 (mod 8)` is unbounded
(from Mathlib's proof of Dirichlet's theorem). -/
lemma W_unbounded (B : ℝ) : ∃ Q : Finset ℕ, (∀ q ∈ Q, q.Prime ∧ q % 8 = 1) ∧
    B < ∑ q ∈ Q, Real.log q / q := by
  have hns := vonMangoldt.not_summable_residueClass_prime_div (q := 8) (a := 1) isUnit_one
  by_contra hcon
  rw [not_exists] at hcon
  apply hns
  apply summable_of_sum_range_le (c := B)
  · intro n
    apply div_nonneg _ (Nat.cast_nonneg n)
    split_ifs
    · exact vonMangoldt.residueClass_nonneg _ _
    · exact le_refl _
  · intro n
    have h1 := hcon ((Finset.range n).filter (fun q => q.Prime ∧ q % 8 = 1))
    rw [not_and, not_lt] at h1
    have h2 := h1 (by intro q hq; exact (Finset.mem_filter.mp hq).2)
    refine le_trans (le_of_eq ?_) h2
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hp : i.Prime
    · by_cases h8 : i % 8 = 1
      · rw [if_pos hp, if_pos ⟨hp, h8⟩]
        unfold vonMangoldt.residueClass
        rw [Set.indicator_of_mem (by exact (zmod8 i).mpr h8), vonMangoldt_apply_prime hp]
      · rw [if_pos hp, if_neg (fun h => h8 h.2)]
        unfold vonMangoldt.residueClass
        rw [Set.indicator_of_notMem (by exact fun h => h8 ((zmod8 i).mp h)), zero_div]
    · rw [if_neg hp, if_neg (fun h => hp h.1), zero_div]

lemma s_nonneg (N y : ℕ) : 0 ≤ s N y := Finset.sum_nonneg (fun d _ => g_nonneg N d)

/-- A non-peak of `(X, 2X]` whose `y² - 2` has only prime factors at most `2X + 1`
carries mass at least `2 log X`. -/
lemma s_lower (X y : ℕ) (hX : 1 ≤ X) (hy : y ∈ Ioc X (2 * X))
    (h : ∀ p : ℕ, p.Prime → p ∣ y ^ 2 - 2 → p ≤ 2 * X + 1) :
    2 * Real.log X ≤ s (2 * X + 1) y := by
  rw [s_eq_log _ _ h]
  rw [Finset.mem_Ioc] at hy
  have h1 : (X + 1) ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : (X + 1) ^ 2 = X ^ 2 + 2 * X + 1 := by ring
  have h3 : X ^ 2 ≤ y ^ 2 - 2 := by omega
  have h4 : ((X : ℝ)) ^ 2 ≤ ((y ^ 2 - 2 : ℕ) : ℝ) := by exact_mod_cast h3
  have hX' : (0 : ℝ) < X := by exact_mod_cast hX
  have h5 := Real.log_le_log (by positivity) h4
  rw [Real.log_pow] at h5
  exact_mod_cast h5

/-- The main inequality: if every non-peak of `(X, 2X]` has `y² - 2` free of prime factors
above `2X + 1`, then the sum of `log q / q` over `Q` is bounded. -/
lemma core (K5 K6 : ℝ) (hK5 : 0 ≤ K5) (hK6 : 0 ≤ K6)
    (h5 : ∀ N : ℕ, 2 ≤ N → ∑ d ∈ Ioc 0 (N ^ 2), g N d * u d / d ≤ Real.log N + K5)
    (h6 : ∀ N : ℕ, 1 ≤ N → ∑ d ∈ Ioc 0 (N ^ 2), g N d * u d ≤ K6 * N)
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime ∧ q % 8 = 1)
    (X : ℕ) (hX : 3 ≤ X) (hQX : ∀ q ∈ Q, q ≤ 2 * X + 1)
    (hbad : ∀ y ∈ Ioc X (2 * X), ¬ peak y →
      ∀ p : ℕ, p.Prime → p ∣ y ^ 2 - 2 → p ≤ 2 * X + 1) :
    (X : ℝ) / 2 * ∑ q ∈ Q, Real.log q / q
      ≤ (2 + K5 + 3 * K6) * X + Real.log X
        + (X : ℝ) / (2 * Real.log X)
            * ∑ q ∈ Q, Real.log q * ((2 + K5 + 3 * K6) + 4 * Real.log q)
        + 7 * ∑ q ∈ Q, Real.log q := by
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (X : ℝ) := ⟨_, rfl⟩
  obtain ⟨K8, hK8⟩ : ∃ K8 : ℝ, K8 = 2 + K5 + 3 * K6 := ⟨_, rfl⟩
  obtain ⟨lN, hlNdef⟩ : ∃ lN : ℝ, lN = Real.log ((2 * X + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hL, ← hK8]
  have hX' : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hX3 : (3 : ℝ) ≤ X := by exact_mod_cast hX
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hX']
    have := Real.exp_one_lt_d9
    linarith
  have hL0 : L ≠ 0 := by linarith
  have hNX : ((2 * X + 1 : ℕ) : ℝ) ≤ 3 * X := by push_cast; linarith
  have hlN : lN ≤ L + 2 := by
    have h1 : Real.log ((2 * X + 1 : ℕ) : ℝ) ≤ Real.log (3 * X) :=
      Real.log_le_log (by positivity) hNX
    rw [Real.log_mul (by norm_num) hX'.ne'] at h1
    have h2 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    rw [hlNdef, hL]
    linarith
  -- total mass
  have hS : ∑ y ∈ Ioc X (2 * X), s (2 * X + 1) y
      ≤ X * (lN + K5) + K6 * ((2 * X + 1 : ℕ) : ℝ) := by
    have h := mass_class_bound K5 K6 h5 h6 X 1 0 (by omega) one_pos
    have e1 : (Ioc X (2 * X)).filter (fun y => y ≡ 0 [MOD 1]) = Ioc X (2 * X) := by
      apply Finset.filter_true_of_mem
      intro y _
      exact Nat.modEq_one
    have e2 : ∑ d ∈ Ioc 0 ((2 * X + 1) ^ 2),
        (if Nat.Coprime 1 d then (0 : ℝ)
         else g (2 * X + 1) d
          * (((Ioc X (2 * X)).filter (fun y => d ∣ y ^ 2 - 2)).card : ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro d _
      rw [if_pos (Nat.coprime_one_left d)]
    rw [e1, e2, ← hlNdef] at h
    simpa using h
  -- the non-peaks carry mass `2 L` each
  have hNPmass : ((X : ℝ) - 1) * L
      ≤ ∑ y ∈ (Ioc X (2 * X)).filter (fun y => ¬ peak y), s (2 * X + 1) y := by
    have h1 : ∀ y ∈ (Ioc X (2 * X)).filter (fun y => ¬ peak y), 2 * L ≤ s (2 * X + 1) y := by
      intro y hy
      rw [Finset.mem_filter] at hy
      rw [hL]
      exact s_lower X y (by omega) hy.1 (hbad y hy.1 hy.2)
    have h2 := Finset.card_nsmul_le_sum _ _ _ h1
    rw [nsmul_eq_mul] at h2
    have h3 : ((X : ℝ) - 1) / 2
        ≤ (((Ioc X (2 * X)).filter (fun y => ¬ peak y)).card : ℝ) := by
      have h4 := NP_card X
      have h5 : X - 1 ≤ 2 * (X / 2) := by omega
      have h6 : ((X : ℝ) - 1) ≤ 2 * ((X / 2 : ℕ) : ℝ) := by
        have h7 : ((X - 1 : ℕ) : ℝ) ≤ ((2 * (X / 2) : ℕ) : ℝ) := by exact_mod_cast h5
        rw [Nat.cast_sub (by omega)] at h7
        push_cast at h7
        linarith
      have h8 : ((X / 2 : ℕ) : ℝ)
          ≤ (((Ioc X (2 * X)).filter (fun y => ¬ peak y)).card : ℝ) := by exact_mod_cast h4
      linarith
    calc ((X : ℝ) - 1) * L = ((X : ℝ) - 1) / 2 * (2 * L) := by ring
      _ ≤ (((Ioc X (2 * X)).filter (fun y => ¬ peak y)).card : ℝ) * (2 * L) :=
          mul_le_mul_of_nonneg_right h3 (by linarith)
      _ ≤ _ := h2
  -- so the peaks carry `O(X)`
  have hsplit := Finset.sum_filter_add_sum_filter_not (Ioc X (2 * X)) (fun y => peak y)
    (fun y => s (2 * X + 1) y)
  have hU : ∑ y ∈ (Ioc X (2 * X)).filter (fun y => peak y), s (2 * X + 1) y
      ≤ K8 * X + L := by
    have h1 : (X : ℝ) * (lN + K5) ≤ X * (L + 2 + K5) :=
      mul_le_mul_of_nonneg_left (by linarith) hX'.le
    have h2 : K6 * ((2 * X + 1 : ℕ) : ℝ) ≤ K6 * (3 * X) := mul_le_mul_of_nonneg_left hNX hK6
    rw [hK8]
    linarith
  -- a class modulo `q` on which `q ∣ y² - 2`
  have hroot : ∀ q : ℕ, ∃ a : ℕ, ∀ y : ℕ, (q.Prime ∧ q % 8 = 1) →
      y ≡ a [MOD q] → 2 ≤ y → q ∣ y ^ 2 - 2 := by
    intro q
    by_cases h : q.Prime ∧ q % 8 = 1
    · obtain ⟨a, ha⟩ := root_exists q h.1 h.2
      exact ⟨a, fun y _ => ha y⟩
    · exact ⟨0, fun _ h' => absurd h' h⟩
  choose a ha using hroot
  -- at least about half of each class consists of peaks
  have hq_bound : ∀ q ∈ Q,
      (X : ℝ) / q / 2 - (X : ℝ) / (2 * L) * (K8 + 4 * Real.log q) - 7
      ≤ ((((Ioc X (2 * X)).filter (fun y => y ≡ a q [MOD q])).filter
          (fun y => peak y)).card : ℝ) := by
    intro q hq
    obtain ⟨hqp, hq8⟩ := hQ q hq
    have hqpos : 0 < q := hqp.pos
    have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hqp.one_le
    have hq0 : (q : ℝ) ≠ 0 := by linarith
    have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq'
    have hc := class_card_lower X q (a q) hqpos
    have hcard := Finset.card_filter_add_card_filter_not
      (s := (Ioc X (2 * X)).filter (fun y => y ≡ a q [MOD q])) (fun y => peak y)
    have hcard' : ((((Ioc X (2 * X)).filter (fun y => y ≡ a q [MOD q])).filter
          (fun y => peak y)).card : ℝ)
        + ((((Ioc X (2 * X)).filter (fun y => y ≡ a q [MOD q])).filter
          (fun y => ¬ peak y)).card : ℝ)
        = (((Ioc X (2 * X)).filter (fun y => y ≡ a q [MOD q])).card : ℝ) := by
      exact_mod_cast hcard
    have hn : ((((Ioc X (2 * X)).filter (fun y => y ≡ a q [MOD q])).filter
          (fun y => ¬ peak y)).card : ℝ) * (2 * L)
        ≤ (X : ℝ) / q * (lN + K5) + K6 * ((2 * X + 1 : ℕ) : ℝ)
          + (4 * X * Real.log q / q + 4 * lN) := by
      have h1 : ∀ y ∈ ((Ioc X (2 * X)).filter (fun y => y ≡ a q [MOD q])).filter
          (fun y => ¬ peak y), 2 * L ≤ s (2 * X + 1) y := by
        intro y hy
        rw [Finset.mem_filter, Finset.mem_filter] at hy
        rw [hL]
        exact s_lower X y (by omega) hy.1.1 (hbad y hy.1.1 hy.2)
      have h2 := Finset.card_nsmul_le_sum _ _ _ h1
      rw [nsmul_eq_mul] at h2
      have h3 : ∑ y ∈ ((Ioc X (2 * X)).filter (fun y => y ≡ a q [MOD q])).filter
          (fun y => ¬ peak y), s (2 * X + 1) y
          ≤ ∑ y ∈ (Ioc X (2 * X)).filter (fun y => y ≡ a q [MOD q]), s (2 * X + 1) y :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun y _ _ => s_nonneg _ _)
      have h4 := mass_class_bound K5 K6 h5 h6 X q (a q) (by omega) hqpos
      have h5' := NC_bound X q (by omega) hqp
      rw [← hlNdef] at h4 h5'
      linarith
    have hxq0 : 0 ≤ (X : ℝ) / q := by positivity
    have hxq1 : (X : ℝ) / q ≤ X := div_le_self hX'.le hq'
    have hkey : ((((Ioc X (2 * X)).filter (fun y => y ≡ a q [MOD q])).filter
          (fun y => ¬ peak y)).card : ℝ) * (2 * L)
        ≤ ((X : ℝ) / q / 2 + (X : ℝ) / (2 * L) * (K8 + 4 * Real.log q) + 6) * (2 * L) := by
      have e : ((X : ℝ) / q / 2 + (X : ℝ) / (2 * L) * (K8 + 4 * Real.log q) + 6) * (2 * L)
          = (X : ℝ) / q * L + X * (K8 + 4 * Real.log q) + 12 * L := by
        field_simp
        ring
      rw [e]
      have t1 : (X : ℝ) / q * (lN + K5) ≤ (X : ℝ) / q * L + X * (2 + K5) := by
        have s1 : (X : ℝ) / q * (lN + K5) ≤ (X : ℝ) / q * (L + 2 + K5) :=
          mul_le_mul_of_nonneg_left (by linarith) hxq0
        have s2 : (X : ℝ) / q * (2 + K5) ≤ X * (2 + K5) :=
          mul_le_mul_of_nonneg_right hxq1 (by linarith)
        linarith
      have t2 : K6 * ((2 * X + 1 : ℕ) : ℝ) ≤ X * (3 * K6) := by
        have := mul_le_mul_of_nonneg_left hNX hK6
        linarith
      have t3 : 4 * X * Real.log q / q ≤ X * (4 * Real.log q) := by
        have s1 : (X : ℝ) / q * (4 * Real.log q) ≤ X * (4 * Real.log q) :=
          mul_le_mul_of_nonneg_right hxq1 (by linarith)
        have e3 : 4 * X * Real.log q / q = (X : ℝ) / q * (4 * Real.log q) := by ring
        linarith
      have t4 : 4 * lN ≤ 12 * L := by linarith
      rw [hK8]
      linarith
    have hnle : ((((Ioc X (2 * X)).filter (fun y => y ≡ a q [MOD q])).filter
          (fun y => ¬ peak y)).card : ℝ)
        ≤ (X : ℝ) / q / 2 + (X : ℝ) / (2 * L) * (K8 + 4 * Real.log q) + 6 :=
      le_of_mul_le_mul_right hkey (by linarith)
    linarith
  -- each peak of the class carries mass at least `log q`
  have hLow : ∑ q ∈ Q, Real.log q
      * ((((Ioc X (2 * X)).filter (fun y => y ≡ a q [MOD q])).filter
          (fun y => peak y)).card : ℝ)
      ≤ ∑ y ∈ (Ioc X (2 * X)).filter (fun y => peak y), s (2 * X + 1) y := by
    have h1 : ∀ y ∈ (Ioc X (2 * X)).filter (fun y => peak y),
        ∑ q ∈ Q, (if q ∣ y ^ 2 - 2 then Real.log q else 0) ≤ s (2 * X + 1) y := by
      intro y hy
      rw [Finset.mem_filter, Finset.mem_Ioc] at hy
      rw [← Finset.sum_filter]
      exact s_ge (2 * X + 1) y (by omega) Q (fun q hq => ⟨(hQ q hq).1, hQX q hq⟩)
    have h2 : ∀ q ∈ Q, Real.log q
        * ((((Ioc X (2 * X)).filter (fun y => y ≡ a q [MOD q])).filter
          (fun y => peak y)).card : ℝ)
        ≤ ∑ y ∈ (Ioc X (2 * X)).filter (fun y => peak y),
            (if q ∣ y ^ 2 - 2 then Real.log q else 0) := by
      intro q hq
      obtain ⟨hqp, hq8⟩ := hQ q hq
      have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hqp.one_le)
      have e : ∑ y ∈ (Ioc X (2 * X)).filter (fun y => peak y),
            (if q ∣ y ^ 2 - 2 then Real.log q else 0)
          = Real.log q * ((((Ioc X (2 * X)).filter (fun y => peak y)).filter
              (fun y => q ∣ y ^ 2 - 2)).card : ℝ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      rw [e]
      apply mul_le_mul_of_nonneg_left _ hlogq
      have hsub : ((Ioc X (2 * X)).filter (fun y => y ≡ a q [MOD q])).filter (fun y => peak y)
          ⊆ ((Ioc X (2 * X)).filter (fun y => peak y)).filter (fun y => q ∣ y ^ 2 - 2) := by
        intro y hy
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc] at hy
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨hy.1.1, hy.2⟩, ha q y ⟨hqp, hq8⟩ hy.1.2 (by omega)⟩
      exact_mod_cast Finset.card_le_card hsub
    calc _ ≤ ∑ q ∈ Q, ∑ y ∈ (Ioc X (2 * X)).filter (fun y => peak y),
            (if q ∣ y ^ 2 - 2 then Real.log q else 0) := Finset.sum_le_sum h2
      _ = ∑ y ∈ (Ioc X (2 * X)).filter (fun y => peak y), ∑ q ∈ Q,
            (if q ∣ y ^ 2 - 2 then Real.log q else 0) := Finset.sum_comm
      _ ≤ _ := Finset.sum_le_sum h1
  have hsum : ∑ q ∈ Q, Real.log q
        * ((X : ℝ) / q / 2 - (X : ℝ) / (2 * L) * (K8 + 4 * Real.log q) - 7)
      ≤ ∑ q ∈ Q, Real.log q
        * ((((Ioc X (2 * X)).filter (fun y => y ≡ a q [MOD q])).filter
          (fun y => peak y)).card : ℝ) := by
    apply Finset.sum_le_sum
    intro q hq
    have hlogq : 0 ≤ Real.log q :=
      Real.log_nonneg (by exact_mod_cast (hQ q hq).1.one_le)
    exact mul_le_mul_of_nonneg_left (hq_bound q hq) hlogq
  have e : ∑ q ∈ Q, Real.log q
        * ((X : ℝ) / q / 2 - (X : ℝ) / (2 * L) * (K8 + 4 * Real.log q) - 7)
      = (X : ℝ) / 2 * ∑ q ∈ Q, Real.log q / q
        - (X : ℝ) / (2 * L) * ∑ q ∈ Q, Real.log q * (K8 + 4 * Real.log q)
        - 7 * ∑ q ∈ Q, Real.log q := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q _
    ring
  linarith

end E372

theorem OMA.solution : type_of% @Erdos372.erdos_372 := by
  obtain ⟨K5, hK5, h5⟩ := E372.gu_div_bound
  obtain ⟨K6, hK6, h6⟩ := E372.gu_bound
  obtain ⟨Q, hQ, hW⟩ := E372.W_unbounded (2 * (2 + K5 + 3 * K6) + 4)
  apply Set.infinite_of_forall_exists_gt
  intro a0
  by_contra hcon
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = ∑ q ∈ Q, Real.log q := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : ℝ,
      H = ∑ q ∈ Q, Real.log q * ((2 + K5 + 3 * K6) + 4 * Real.log q) := ⟨_, rfl⟩
  obtain ⟨X, hXdef⟩ : ∃ X : ℕ,
      X = 3 + ⌈Real.exp H⌉₊ + ⌈14 * G⌉₊ + Q.sup id + a0 := ⟨_, rfl⟩
  have hX3 : 3 ≤ X := by omega
  have hX' : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hXH : Real.exp H ≤ X := by
    have h1 : Real.exp H ≤ ⌈Real.exp H⌉₊ := Nat.le_ceil _
    have h2 : ((⌈Real.exp H⌉₊ : ℕ) : ℝ) ≤ X := by
      exact_mod_cast (by omega : ⌈Real.exp H⌉₊ ≤ X)
    linarith
  have hXG : 14 * G ≤ X := by
    have h1 : 14 * G ≤ ⌈14 * G⌉₊ := Nat.le_ceil _
    have h2 : ((⌈14 * G⌉₊ : ℕ) : ℝ) ≤ X := by
      exact_mod_cast (by omega : ⌈14 * G⌉₊ ≤ X)
    linarith
  have hQX : ∀ q ∈ Q, q ≤ 2 * X + 1 := by
    intro q hq
    have h1 : q ≤ Q.sup id := Finset.le_sup (f := id) hq
    omega
  have hbad : ∀ y ∈ Finset.Ioc X (2 * X), ¬ E372.peak y →
      ∀ p : ℕ, p.Prime → p ∣ y ^ 2 - 2 → p ≤ 2 * X + 1 := by
    intro y hy hnp p hp hpd
    by_contra hlt
    rw [Finset.mem_Ioc] at hy
    apply hcon
    refine ⟨y ^ 2 - 2, E372.triple y p (by omega) hnp hp hpd (by omega), ?_⟩
    have h1 : 4 * y ≤ y ^ 2 := by nlinarith
    omega
  have hcore := E372.core K5 K6 hK5 hK6 h5 h6 Q hQ X hX3 hQX hbad
  rw [← hG, ← hH] at hcore
  have hLH : H ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX']
    exact hXH
  have hL1 : 1 ≤ Real.log (X : ℝ) := by
    rw [Real.le_log_iff_exp_le hX']
    have h1 := Real.exp_one_lt_d9
    have h2 : (3 : ℝ) ≤ X := by exact_mod_cast hX3
    linarith
  have hLX : Real.log (X : ℝ) ≤ X / 2 := by
    have h1 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (X : ℝ) / 2)
    rw [Real.log_div hX'.ne' (by norm_num)] at h1
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith
  have hterm : (X : ℝ) / (2 * Real.log X) * H ≤ X / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hWX : (X : ℝ) / 2 * (2 * (2 + K5 + 3 * K6) + 4)
      < (X : ℝ) / 2 * ∑ q ∈ Q, Real.log q / q :=
    mul_lt_mul_of_pos_left hW (by positivity)
  linarith
