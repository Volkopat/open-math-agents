import OMAStatements.S_oeis_a397048

-- Problem: A397048: Triangle T(n, k) read by rows: T(n, k) = (Sum_{i=0..k} (-1)^i * binomial(k, i) * (n+i)^n) * (-1)^k / k! for 0 <= k <= n.
-- Upstream: formal-conjectures statements/oeis-a397048.lean:0 (declaration OMA.S_oeis_a397048.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: write D_r g for the r-th forward difference of g at 0. Then T(n, k) k! = D_k f
-- with f x = (n + x)^n, and r! S(m, r) = D_r (x^m) (from the recurrence, using
-- D_{r+1}(x g) = (r+1) D_r g(. + 1)). Conjecture 1: with sum_j s(n, j) x^j = x(x-1)...(x-n+1),
-- (n+k)! times the sum is D_{n+k} (x^n x(x-1)...(x-n+1)) = (n+k)!/k! D_k f.
-- Conjecture 2: T(n, k) = sum_m C(n, m) n^(n-m) S(m, k), and sum_k S(m, k) = Bell(m)
-- (S(m+1, r+1) = sum_j C(m, j) S(j, r)). Conjecture 3: Gregory-Newton (shift_eq_sum_fwdDiff_iter).

namespace A397048Aux

open OMA.S_oeis_a397048

theorem D_succ (g : ℕ → ℚ) (r y : ℕ) :
    (fwdDiff (1 : ℕ))^[r + 1] g y = (fwdDiff (1 : ℕ))^[r] g (y + 1) - (fwdDiff (1 : ℕ))^[r] g y := by
  rw [Function.iterate_succ_apply']
  rfl

theorem D0 (g : ℕ → ℚ) (r : ℕ) :
    (fwdDiff (1 : ℕ))^[r + 1] g 0 = (fwdDiff (1 : ℕ))^[r] g 1 - (fwdDiff (1 : ℕ))^[r] g 0 :=
  D_succ g r 0

theorem DX (g : ℕ → ℚ) (r : ℕ) : (fwdDiff (1 : ℕ))^[r] g 0 =
    ∑ i ∈ Finset.range (r + 1), (-1 : ℚ) ^ (r - i) * (((r.choose i : ℕ) : ℚ) * g i) := by
  rw [fwdDiff_iter_eq_sum_shift]
  apply Finset.sum_congr rfl
  intro i _
  have e : g (0 + i • 1) = g i := by simp
  rw [e, zsmul_eq_mul]
  push_cast
  ring

theorem L1 (g : ℕ → ℚ) (r : ℕ) : ∀ y : ℕ,
    (fwdDiff (1 : ℕ))^[r + 1] (fun x : ℕ => (x : ℚ) * g x) y =
      (y : ℚ) * (fwdDiff (1 : ℕ))^[r + 1] g y + ((r : ℚ) + 1) * (fwdDiff (1 : ℕ))^[r] g (y + 1) := by
  induction r with
  | zero =>
    intro y
    rw [D_succ (fun x : ℕ => (x : ℚ) * g x) 0 y, D_succ g 0 y]
    simp only [Function.iterate_zero, id_eq]
    push_cast
    ring
  | succ r ih =>
    intro y
    rw [D_succ (fun x : ℕ => (x : ℚ) * g x) (r + 1) y, ih (y + 1), ih y]
    have h1 := D_succ g r (y + 1)
    have h2 := D_succ g (r + 1) y
    push_cast at h1 h2 ⊢
    linear_combination (-(y : ℚ)) * h2 - ((r : ℚ) + 1) * h1

theorem L1z (g φ : ℕ → ℚ) (hφ : ∀ x, φ x = (x : ℚ) * g x) (r : ℕ) :
    (fwdDiff (1 : ℕ))^[r + 1] φ 0 = ((r : ℚ) + 1) * (fwdDiff (1 : ℕ))^[r] g 1 := by
  have e : φ = fun x : ℕ => (x : ℚ) * g x := funext hφ
  subst e
  have h0 := L1 g r 0
  simp only [Nat.cast_zero, zero_mul, zero_add] at h0
  exact h0

theorem SH (g g' : ℕ → ℚ) (hg : ∀ x, g' x = g (x + 1)) (r : ℕ) :
    (fwdDiff (1 : ℕ))^[r] g' 0 = (fwdDiff (1 : ℕ))^[r] g 1 := by
  have e : g' = fun x => g (x + 1) := funext hg
  subst e
  have h := fwdDiff_iter_comp_add (1 : ℕ) g 1 r 0
  rw [zero_add] at h
  exact h

theorem stir2_explicit (m : ℕ) : ∀ r : ℕ,
    ((r.factorial : ℕ) : ℚ) * ((Nat.stirlingSecond m r : ℕ) : ℚ) =
      (fwdDiff (1 : ℕ))^[r] (fun x : ℕ => (x : ℚ) ^ m) 0 := by
  induction m with
  | zero =>
    intro r
    cases r with
    | zero => simp
    | succ r =>
      have hc : fwdDiff (1 : ℕ) (fun x : ℕ => (x : ℚ) ^ 0) = fun _ => (0 : ℚ) := by
        funext x
        simp [fwdDiff]
      rw [show Nat.stirlingSecond 0 (r + 1) = 0 from rfl, Function.iterate_succ_apply, hc,
        Function.iterate_fixed (fwdDiff_const (1 : ℕ) (0 : ℚ)) r]
      simp
  | succ m ih =>
    intro r
    cases r with
    | zero =>
      rw [show Nat.stirlingSecond (m + 1) 0 = 0 from rfl]
      simp [pow_succ]
    | succ r =>
      rw [L1z (fun x : ℕ => (x : ℚ) ^ m) (fun x : ℕ => (x : ℚ) ^ (m + 1))
        (fun x => show (x : ℚ) ^ (m + 1) = (x : ℚ) * (x : ℚ) ^ m by ring) r]
      have hs := D0 (fun x : ℕ => (x : ℚ) ^ m) r
      have i1 := ih (r + 1)
      have i0 := ih r
      rw [Nat.factorial_succ] at i1
      rw [Nat.stirlingSecond_succ_succ, Nat.factorial_succ]
      push_cast at hs i1 i0 ⊢
      linear_combination ((r : ℚ) + 1) * i1 + ((r : ℚ) + 1) * i0 + ((r : ℚ) + 1) * hs

theorem s_succ_succ (n k : ℕ) : s (n + 1) (k + 1) = s n k - (n : ℤ) * s n (k + 1) := rfl

theorem s_succ_zero (n : ℕ) : s (n + 1) 0 = 0 := rfl

theorem s_zero_of_lt : ∀ n k : ℕ, n < k → s n k = 0
  | _, 0, hk => absurd hk (Nat.not_lt_zero _)
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, hk => by
    rw [s_succ_succ, s_zero_of_lt n k (by omega), s_zero_of_lt n (k + 1) (by omega)]
    simp

theorem DFsucc (x n : ℕ) :
    ((x.descFactorial (n + 1) : ℕ) : ℚ) = ((x : ℚ) - n) * ((x.descFactorial n : ℕ) : ℚ) := by
  rcases Nat.lt_or_ge x n with hx | hx
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hx,
      Nat.descFactorial_eq_zero_iff_lt.mpr (show x < n + 1 by omega)]
    simp
  · rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hx]

theorem stir1_poly (x : ℕ) : ∀ n : ℕ,
    ∑ j ∈ Finset.range (n + 1), (s n j : ℚ) * (x : ℚ) ^ j = ((x.descFactorial n : ℕ) : ℚ) := by
  intro n
  induction n with
  | zero => simp [s]
  | succ n ih =>
    rw [Finset.sum_range_succ' (fun j => (s (n + 1) j : ℚ) * (x : ℚ) ^ j) (n + 1)]
    have h1 : ∑ j ∈ Finset.range (n + 1), (s (n + 1) (j + 1) : ℚ) * (x : ℚ) ^ (j + 1) =
        (x : ℚ) * ∑ j ∈ Finset.range (n + 1), (s n j : ℚ) * (x : ℚ) ^ j -
        (n : ℚ) * ∑ j ∈ Finset.range (n + 1), (s n (j + 1) : ℚ) * (x : ℚ) ^ (j + 1) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [s_succ_succ]
      push_cast
      ring
    have hB := Finset.sum_range_succ' (fun j => (s n j : ℚ) * (x : ℚ) ^ j) (n + 1)
    have hC := Finset.sum_range_succ (fun j => (s n j : ℚ) * (x : ℚ) ^ j) (n + 1)
    have hz : s n (n + 1) = 0 := s_zero_of_lt n (n + 1) (by omega)
    have hn0 : (n : ℚ) * (s n 0 : ℚ) = 0 := by
      cases n with
      | zero => simp
      | succ n => simp [s_succ_zero]
    have hD := DFsucc x n
    rw [h1, s_succ_zero]
    rw [hz] at hC
    push_cast at ih hB hC hD hn0 ⊢
    linear_combination ((x : ℚ) - n) * ih + hn0 + (n : ℚ) * hB - (n : ℚ) * hC - hD

theorem desc_mul_shift (n : ℕ) : ∀ (h φ hn : ℕ → ℚ),
    (∀ x, φ x = ((x.descFactorial n : ℕ) : ℚ) * h x) → (∀ x, hn x = h (x + n)) → ∀ k : ℕ,
    (fwdDiff (1 : ℕ))^[n + k] φ 0 * ((k.factorial : ℕ) : ℚ) =
      (((n + k).factorial : ℕ) : ℚ) * (fwdDiff (1 : ℕ))^[k] hn 0 := by
  induction n with
  | zero =>
    intro h φ hn hφ hhn k
    have e1 : φ = h := funext fun x => by
      rw [hφ x, Nat.descFactorial_zero, Nat.cast_one, one_mul]
    have e2 : hn = h := funext fun x => by rw [hhn x, Nat.add_zero]
    rw [e1, e2, Nat.zero_add]
    ring
  | succ n ih =>
    intro h φ hn hφ hhn k
    have hφ2 : ∀ x : ℕ, φ x = (x : ℚ) * ((((x - 1).descFactorial n : ℕ) : ℚ) * h x) := by
      intro x
      rw [hφ x]
      cases x with
      | zero => simp
      | succ y =>
        rw [Nat.succ_descFactorial_succ, Nat.add_sub_cancel]
        push_cast
        ring
    have hg : ∀ x : ℕ, ((x.descFactorial n : ℕ) : ℚ) * h (x + 1) =
        (((x + 1 - 1).descFactorial n : ℕ) : ℚ) * h (x + 1) := by
      intro x
      rw [Nat.add_sub_cancel]
    have hi := ih (fun x => h (x + 1)) (fun x : ℕ => ((x.descFactorial n : ℕ) : ℚ) * h (x + 1)) hn
      (fun x => rfl) (fun x => (hhn x).trans (congrArg h (Nat.add_assoc x n 1).symm)) k
    rw [show n + 1 + k = n + k + 1 by omega,
      L1z (fun x : ℕ => (((x - 1).descFactorial n : ℕ) : ℚ) * h x) φ hφ2 (n + k),
      ← SH (fun x : ℕ => (((x - 1).descFactorial n : ℕ) : ℚ) * h x)
        (fun x : ℕ => ((x.descFactorial n : ℕ) : ℚ) * h (x + 1)) hg (n + k),
      Nat.factorial_succ]
    push_cast at hi ⊢
    linear_combination ((n : ℚ) + k + 1) * hi

theorem T_mul_fact (n k : ℕ) : T n k * ((k.factorial : ℕ) : ℚ) =
    ∑ i ∈ Finset.range (k + 1), (-1 : ℚ) ^ (k - i) * (((k.choose i : ℕ) : ℚ) * ((n : ℚ) + i) ^ n) := by
  have hk : ((k.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  unfold T
  rw [div_mul_cancel₀ _ hk, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  obtain ⟨d, rfl⟩ : ∃ d, k = i + d := ⟨k - i, by omega⟩
  rw [show i + d - i = d by omega, pow_add]
  have hsq : ((-1 : ℚ) ^ i) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  linear_combination ((((i + d).choose i : ℕ) : ℚ) * ((n : ℚ) + i) ^ n * (-1 : ℚ) ^ d) * hsq

theorem conj1 (n k : ℕ) (hk : k ≤ n) : T n k = ∑ i ∈ Finset.range (n - k + 1),
    (s n (k + i) : ℚ) * (Nat.stirlingSecond (n + k + i) (n + k) : ℚ) := by
  have hext : ∑ i ∈ Finset.range (n - k + 1),
      (s n (k + i) : ℚ) * (Nat.stirlingSecond (n + k + i) (n + k) : ℚ) =
      ∑ j ∈ Finset.range (n + 1), (s n j : ℚ) * (Nat.stirlingSecond (n + j) (n + k) : ℚ) := by
    rw [show n + 1 = k + (n - k + 1) by omega,
      Finset.sum_range_add (fun j => (s n j : ℚ) * (Nat.stirlingSecond (n + j) (n + k) : ℚ))
        k (n - k + 1)]
    have hz : ∑ j ∈ Finset.range k, (s n j : ℚ) * (Nat.stirlingSecond (n + j) (n + k) : ℚ) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      simp [Nat.stirlingSecond_eq_zero_of_lt (show n + j < n + k by omega)]
    rw [hz, zero_add]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.add_assoc]
  rw [hext]
  have hR : (((n + k).factorial : ℕ) : ℚ) *
      ∑ j ∈ Finset.range (n + 1), (s n j : ℚ) * (Nat.stirlingSecond (n + j) (n + k) : ℚ) =
      (fwdDiff (1 : ℕ))^[n + k] (fun x : ℕ => ((x.descFactorial n : ℕ) : ℚ) * (x : ℚ) ^ n) 0 := by
    have lhs : (((n + k).factorial : ℕ) : ℚ) *
        ∑ j ∈ Finset.range (n + 1), (s n j : ℚ) * (Nat.stirlingSecond (n + j) (n + k) : ℚ) =
        ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + k + 1),
          (s n j : ℚ) * ((-1 : ℚ) ^ (n + k - i) * ((((n + k).choose i : ℕ) : ℚ) * (i : ℚ) ^ (n + j))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have h := stir2_explicit (n + j) (n + k)
      rw [DX] at h
      rw [← Finset.mul_sum, ← h]
      ring
    have rhs : (fwdDiff (1 : ℕ))^[n + k]
        (fun x : ℕ => ((x.descFactorial n : ℕ) : ℚ) * (x : ℚ) ^ n) 0 =
        ∑ i ∈ Finset.range (n + k + 1), ∑ j ∈ Finset.range (n + 1),
          (s n j : ℚ) * ((-1 : ℚ) ^ (n + k - i) * ((((n + k).choose i : ℕ) : ℚ) * (i : ℚ) ^ (n + j))) := by
      rw [DX]
      apply Finset.sum_congr rfl
      intro i _
      rw [← stir1_poly i n, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [lhs, rhs, Finset.sum_comm]
  have hG := desc_mul_shift n (fun x : ℕ => (x : ℚ) ^ n)
    (fun x : ℕ => ((x.descFactorial n : ℕ) : ℚ) * (x : ℚ) ^ n)
    (fun x : ℕ => ((n : ℚ) + x) ^ n) (fun x => rfl) (fun x => by push_cast; ring) k
  have hT : T n k * ((k.factorial : ℕ) : ℚ) =
      (fwdDiff (1 : ℕ))^[k] (fun x : ℕ => ((n : ℚ) + x) ^ n) 0 := by
    rw [T_mul_fact, DX]
  have hne : (((n + k).factorial : ℕ) : ℚ) * ((k.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hne
  linear_combination (((n + k).factorial : ℕ) : ℚ) * hT - hG - ((k.factorial : ℕ) : ℚ) * hR

theorem T_stir (n k : ℕ) : T n k = ∑ m ∈ Finset.range (n + 1),
    ((n.choose m : ℕ) : ℚ) * (n : ℚ) ^ (n - m) * (Nat.stirlingSecond m k : ℚ) := by
  have hk : ((k.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  apply mul_right_cancel₀ hk
  rw [T_mul_fact, Finset.sum_mul]
  have e : ∀ m ∈ Finset.range (n + 1),
      ((n.choose m : ℕ) : ℚ) * (n : ℚ) ^ (n - m) * (Nat.stirlingSecond m k : ℚ) *
        ((k.factorial : ℕ) : ℚ) =
      ∑ i ∈ Finset.range (k + 1), ((n.choose m : ℕ) : ℚ) * (n : ℚ) ^ (n - m) *
        ((-1 : ℚ) ^ (k - i) * (((k.choose i : ℕ) : ℚ) * (i : ℚ) ^ m)) := by
    intro m _
    have h := stir2_explicit m k
    rw [DX] at h
    rw [← Finset.mul_sum, ← h]
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [add_comm (n : ℚ) (i : ℚ), add_pow, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem SE (j m : ℕ) (h : j ≤ m) : ∑ r ∈ Finset.range (m + 1), (Nat.stirlingSecond j r : ℚ) =
    ∑ r ∈ Finset.range (j + 1), (Nat.stirlingSecond j r : ℚ) := by
  rw [show m + 1 = j + 1 + (m - j) by omega,
    Finset.sum_range_add (fun r => (Nat.stirlingSecond j r : ℚ)) (j + 1) (m - j)]
  have hz : ∑ x ∈ Finset.range (m - j), (Nat.stirlingSecond j (j + 1 + x) : ℚ) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    simp [Nat.stirlingSecond_eq_zero_of_lt (show j < j + 1 + x by omega)]
  rw [hz, add_zero]

theorem SRq (m r : ℕ) : (Nat.stirlingSecond (m + 1) (r + 1) : ℚ) =
    ∑ j ∈ Finset.range (m + 1), ((m.choose j : ℕ) : ℚ) * (Nat.stirlingSecond j r : ℚ) := by
  have h1 := stir2_explicit (m + 1) (r + 1)
  rw [L1z (fun x : ℕ => (x : ℚ) ^ m) (fun x : ℕ => (x : ℚ) ^ (m + 1))
      (fun x => show (x : ℚ) ^ (m + 1) = (x : ℚ) * (x : ℚ) ^ m by ring) r,
    ← SH (fun x : ℕ => (x : ℚ) ^ m) (fun x : ℕ => ((x : ℚ) + 1) ^ m)
      (fun x => show ((x : ℚ) + 1) ^ m = (((x + 1 : ℕ) : ℚ)) ^ m by simp) r, DX] at h1
  have h2 : ∑ i ∈ Finset.range (r + 1), (-1 : ℚ) ^ (r - i) * (((r.choose i : ℕ) : ℚ) * ((i : ℚ) + 1) ^ m) =
      ((r.factorial : ℕ) : ℚ) *
        ∑ j ∈ Finset.range (m + 1), ((m.choose j : ℕ) : ℚ) * (Nat.stirlingSecond j r : ℚ) := by
    rw [Finset.mul_sum]
    have e : ∀ j ∈ Finset.range (m + 1),
        ((r.factorial : ℕ) : ℚ) * (((m.choose j : ℕ) : ℚ) * (Nat.stirlingSecond j r : ℚ)) =
        ∑ i ∈ Finset.range (r + 1), ((m.choose j : ℕ) : ℚ) *
          ((-1 : ℚ) ^ (r - i) * (((r.choose i : ℕ) : ℚ) * (i : ℚ) ^ j)) := by
      intro j _
      have h := stir2_explicit j r
      rw [DX] at h
      rw [← Finset.mul_sum, ← h]
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [add_pow, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h2, Nat.factorial_succ] at h1
  have hr : ((r.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have hr1 : ((r : ℚ) + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ (mul_ne_zero hr1 hr)
  push_cast at h1
  linear_combination h1

theorem bellS (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), (Nat.stirlingSecond m k : ℚ) = (Nat.bell m : ℚ) := by
  refine Nat.strong_induction_on m ?_
  rintro (_ | m) ih
  · simp
  · have hL : ∑ k ∈ Finset.range (m + 1 + 1), (Nat.stirlingSecond (m + 1) k : ℚ) =
        ∑ j ∈ Finset.range (m + 1), ((m.choose j : ℕ) : ℚ) * (Nat.bell j : ℚ) := by
      rw [Finset.sum_range_succ' (fun k => (Nat.stirlingSecond (m + 1) k : ℚ)) (m + 1),
        show Nat.stirlingSecond (m + 1) 0 = 0 from rfl, Nat.cast_zero, add_zero,
        Finset.sum_congr rfl (fun r _ => SRq m r), Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [← Finset.mul_sum, SE j m hjm, ih j (by omega)]
    have hrefl : ∑ i ∈ Finset.range (m + 1), ((m.choose i : ℕ) : ℚ) * (Nat.bell (m - i) : ℚ) =
        ∑ j ∈ Finset.range (m + 1), ((m.choose j : ℕ) : ℚ) * (Nat.bell j : ℚ) := by
      rw [← Finset.sum_range_reflect (fun j => ((m.choose j : ℕ) : ℚ) * (Nat.bell j : ℚ)) (m + 1)]
      apply Finset.sum_congr rfl
      intro i hi
      have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [show m + 1 - 1 - i = m - i by omega, Nat.choose_symm him]
    rw [hL, Nat.bell_succ, ← Nat.range_succ_eq_Iic]
    push_cast
    exact hrefl.symm

theorem bell_ext (m n : ℕ) (h : m ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (Nat.stirlingSecond m k : ℚ) = (Nat.bell m : ℚ) := by
  rw [SE m n h, bellS m]

theorem conj2 (n : ℕ) : ∑ k ∈ Finset.range (n + 1), T n k = ((a134980 n : ℕ) : ℚ) := by
  rw [Finset.sum_congr rfl (fun k _ => T_stir n k), Finset.sum_comm]
  unfold a134980
  push_cast
  apply Finset.sum_congr rfl
  intro m hm
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [← Finset.mul_sum, bell_ext m n hmn]

theorem conj3 (n k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), T n i * (k.factorial : ℚ) / ((k - i).factorial : ℚ) =
      ((n : ℚ) + k) ^ n := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℚ, ∀ j, f j = ((n : ℚ) + j) ^ n := ⟨_, fun _ => rfl⟩
  have hD : ∀ i : ℕ, T n i = (fwdDiff (1 : ℕ))^[i] f 0 / (i.factorial : ℚ) := by
    intro i
    rw [fwdDiff_iter_eq_sum_shift (1 : ℕ) f i 0]
    unfold T
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    obtain ⟨d, rfl⟩ : ∃ d, i = j + d := ⟨i - j, by omega⟩
    have hsq : ((-1 : ℚ) ^ j) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    have hfj : f (0 + j • 1) = ((n : ℚ) + j) ^ n := by
      rw [hf]
      simp
    rw [zsmul_eq_mul, hfj, show j + d - j = d by omega, pow_add]
    push_cast
    linear_combination ((((j + d).choose j : ℕ) : ℚ) * ((n : ℚ) + j) ^ n * (-1 : ℚ) ^ d) * hsq
  have hshift := shift_eq_sum_fwdDiff_iter (1 : ℕ) f k 0
  have hfk : f (0 + k • 1) = ((n : ℚ) + k) ^ n := by
    rw [hf]
    simp
  rw [← hfk, hshift]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [hD i, nsmul_eq_mul]
  have hfac : ((k.choose i : ℕ) : ℚ) * (i.factorial : ℚ) * ((k - i).factorial : ℚ) =
      (k.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hik
  rw [← hfac]
  have h1 : (i.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((k - i).factorial : ℚ) ≠ 0 := by positivity
  field

end A397048Aux

open OMA.S_oeis_a397048 in
theorem OMA.solution : type_of% @OMA.S_oeis_a397048.main := by
  exact ⟨fun n k hk => A397048Aux.conj1 n k hk, fun n => A397048Aux.conj2 n,
    fun n k _ => A397048Aux.conj3 n k⟩
