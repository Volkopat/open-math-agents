import OMAStatements.S_oeis_a013936
import Mathlib

/-!
The sharpness claim for the asymmetric divisor count of pairs with j k² ≤ n.
We prove an error of order n^(249/1000) by splitting the count at its cube root.
Finite differencing and Fourier smoothing control the fractional parts.
The two leading coefficients are uniquely determined by any error of order o(√n).
A stronger error bound for this counting function is reported by A. V. Lelechenko,
Average number of squares dividing mn, arXiv:1407.1222.
-/
namespace A013936
open Finset Asymptotics Filter

private theorem row (n b : ℕ) (hb : b ≤ n) :
    (∑ j ∈ Icc 1 n, if j ≤ b then 1 else 0) = b := by
  classical
  rw [← sum_filter]
  have h : (Icc 1 n).filter (· ≤ b) = Icc 1 b := by ext; simp; omega
  simp [h]

private theorem rowDiv (n k : ℕ) (hk : 0 < k) :
    (∑ j ∈ Icc 1 n, if j * k^2 ≤ n then 1 else 0) = n / k^2 := by
  have eqv (j : ℕ) : j ≤ n / k^2 ↔ j*k^2 ≤ n := Nat.le_div_iff_mul_le (pow_pos hk 2)
  rw [← row n (n / k^2) (Nat.div_le_self ..)]
  apply sum_congr rfl
  intro j _
  by_cases hj : j ≤ n / k^2
  · simp [hj, (eqv j).mp hj]
  · simp [hj, (eqv j).not.mp hj]

private theorem rowSqrt (n j : ℕ) (hj : 0 < j) :
    (∑ k ∈ Icc 1 n, if j * k^2 ≤ n then 1 else 0) = Nat.sqrt (n / j) := by
  simpa only [Nat.le_sqrt', Nat.le_div_iff_mul_le hj, mul_comm j] using
    row n (Nat.sqrt (n/j)) ((Nat.sqrt_le_self _).trans (Nat.div_le_self ..))

/-- Count the two strips of the hyperbola and subtract their square of overlap. -/
theorem hyperbola (n L : ℕ) (hL : L ≤ n) (hlo : L^3 ≤ n) (hhi : n < (L+1)^3) :
    (∑ k ∈ Icc 1 n, n / k^2) + L^2 =
      (∑ k ∈ Icc 1 L, n / k^2) + ∑ j ∈ Icc 1 L, Nat.sqrt (n/j) := by
  classical
  let S := Icc 1 n
  let T := Icc 1 L
  let w := fun j k : ℕ => if j * k^2 ≤ n then 1 else 0
  have sub : T ⊆ S := Icc_subset_Icc_right hL
  have restrict_sum (f : ℕ → ℕ) : (∑ k ∈ S, if k ≤ L then f k else 0) = ∑ k ∈ T, f k := by
    rw [← sum_filter]
    congr 1
    ext; simp [S,T]; omega
  have atom (j k : ℕ) :
      w j k + (if k ≤ L ∧ j ≤ L then 1 else 0) =
      (if k ≤ L then w j k else 0) + (if j ≤ L then w j k else 0) := by
    by_cases a : k ≤ L <;> by_cases b : j ≤ L
    · have hh : j*k^2 ≤ n := calc
        _ ≤ L*L^2 := Nat.mul_le_mul b (Nat.pow_le_pow_left a 2)
        _ ≤ n := by simpa [pow_succ, Nat.mul_comm] using hlo
      simp [a,b,w,hh]
    · simp [a,b]
    · simp [a,b]
    · have hh : n < j*k^2 := calc
        _ < (L+1)^3 := hhi
        _ = (L+1)*(L+1)^2 := by ring
        _ ≤ _ := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) 2)
      simp [a,b,w,hh.not_ge]
  have h := sum_congr (s₁ := S) rfl (fun k _ => sum_congr (s₁ := S) rfl (fun j _ => atom j k))
  simp only [sum_add_distrib] at h
  have one (k : ℕ) : (∑ j ∈ S, if k ≤ L ∧ j ≤ L then 1 else 0) =
      if k ≤ L then L else 0 := by
    split_ifs with hk <;> simp [hk, S, row n L hL]
  have left (k) : (∑ j ∈ S, if k ≤ L then w j k else 0) =
      if k ≤ L then ∑ j ∈ S, w j k else 0 := by split_ifs <;> simp_all
  simp_rw [one, left] at h
  rw [restrict_sum, restrict_sum, sum_comm (f := fun k j => if j ≤ L then w j k else 0)] at h
  have right (j) : (∑ k ∈ S, if j ≤ L then w j k else 0) =
      if j ≤ L then ∑ k ∈ S, w j k else 0 := by split_ifs <;> simp_all
  simp_rw [right] at h
  rw [restrict_sum] at h
  have rows (U : Finset ℕ) (hU : U ⊆ S) : (∑ k ∈ U, ∑ j ∈ S, w j k) =
      ∑ k ∈ U, n / k^2 := sum_congr rfl (fun k hk => rowDiv n k (mem_Icc.mp (hU hk)).1)
  rw [rows S (fun _ h => h), rows T sub] at h
  have cols : (∑ j ∈ T, ∑ k ∈ S, w j k) = ∑ j ∈ T, Nat.sqrt (n/j) :=
    sum_congr rfl (fun j hj => rowSqrt n j (mem_Icc.mp hj).1)
  simpa [cols, T, S, pow_two] using h

noncomputable def wave (x : ℝ) : ℂ := Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ))

theorem wave_add (x y : ℝ) : wave (x+y) = wave x * wave y := by
  unfold wave
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem norm_wave (x : ℝ) : ‖wave x‖ = 1 := Complex.norm_exp_I_mul_ofReal _

theorem chord_lower {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1/2) :
    4*t ≤ ‖wave t - 1‖ := by
  rw [wave, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
  have h := Real.le_sin_mul (x := 2*t) (by linarith) (by linarith)
  rw [show 2*Real.pi*t/2 = Real.pi/2*(2*t) by ring]
  exact le_trans (by linarith) (le_abs_self _)

theorem chord_upper (s t : ℝ) : ‖wave s - wave t‖ ≤ 2*Real.pi*|s-t| := by
  have he : wave s - wave t = wave t * (wave (s-t) - 1) := by
    rw [mul_sub, ← wave_add, mul_one, add_sub_cancel]
  rw [he, norm_mul, norm_wave, one_mul]
  simpa [wave, Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*(s-t)))

private theorem reciprocal_variation {q s t : ℝ} (hq : 0 < q)
    (hs : q ≤ s) (ht : q ≤ t) (hs' : s ≤ 1/2) (ht' : t ≤ 1/2) :
    ‖(wave s - 1)⁻¹ - (wave t - 1)⁻¹‖ ≤ 2*Real.pi*|s-t| / (4*q)^2 := by
  have hS := chord_lower (hq.le.trans hs) hs'
  have hT := chord_lower (hq.le.trans ht) ht'
  have S : wave s - 1 ≠ 0 := norm_pos_iff.mp (by linarith)
  have T : wave t - 1 ≠ 0 := norm_pos_iff.mp (by linarith)
  rw [show (wave s - 1)⁻¹ - (wave t - 1)⁻¹ = (wave t - wave s)/((wave s-1)*(wave t-1)) by field_simp; ring,
      norm_div, norm_mul, norm_sub_rev]
  apply div_le_div₀ (by positivity) (chord_upper s t) (by positivity)
  rw [sq]
  exact mul_le_mul (by linarith) (by linarith) (by linarith) (norm_nonneg _)

/-- Summing adjacent differences while keeping the two boundary terms explicit. -/
private theorem weighted_telescope (z c : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ range (N+1), (z (n+1)-z n)*c n) =
      z (N+1)*c N - z 0*c 0 + ∑ n ∈ range N, z (n+1)*(c n-c (n+1)) := by
  induction N with
  | zero => simp [sub_mul]
  | succ N ih =>
    rw [sum_range_succ _ (N+1), ih, sum_range_succ _ N]
    ring

/-- A monotone phase increment confined to a fixed-ratio band away from zero
gives cancellation with an explicit bound independent of the number of terms. -/
theorem small_increment_test (x : ℕ → ℝ) (N : ℕ) (q Q : ℝ)
    (hq : 0 < q) (hQ : Q ≤ 1/2)
    (band : ∀ n ≤ N, q ≤ x (n+1)-x n ∧ x (n+1)-x n ≤ Q)
    (mon : MonotoneOn (fun n => x (n+1)-x n) (Set.Icc 0 N) ∨
      AntitoneOn (fun n => x (n+1)-x n) (Set.Icc 0 N)) :
    ‖∑ n ∈ range (N+1), wave (x n)‖ ≤ 2/(4*q) + 2*Real.pi*(Q-q)/(4*q)^2 := by
  let v (n : ℕ) := x (n+1)-x n
  let z (n : ℕ) := wave (x n)
  let c (n : ℕ) := (wave (v n)-1)⁻¹
  have lower (n) (hn : n ≤ N) : 4*q ≤ ‖wave (v n)-1‖ :=
    (mul_le_mul_of_nonneg_left (band n hn).1 (by norm_num : (0:ℝ) ≤ 4)).trans
      (chord_lower (hq.le.trans (band n hn).1) ((band n hn).2.trans hQ))
  have cb (n) (hn : n ≤ N) : ‖c n‖ ≤ 1/(4*q) := by
    simpa [c, one_div] using inv_anti₀ (by positivity : 0 < 4*q) (lower n hn)
  have step (n) (hn : n ≤ N) : z n = (z (n+1)-z n)*c n := by
    have hnz : wave (v n)-1 ≠ 0 := norm_pos_iff.mp (by linarith [lower n hn])
    have hnext : z (n+1) = z n * wave (v n) := by
      rw [← wave_add]; simp [v,z]
    dsimp only [c]
    rw [hnext, ← mul_sub_one, mul_assoc, mul_inv_cancel₀ hnz, mul_one]
  have variation : (∑ n ∈ range N, |v n-v (n+1)|) ≤ Q-q := by
    have inc (n : ℕ) (hn : n < N) : n ∈ Set.Icc 0 N ∧ n+1 ∈ Set.Icc 0 N := by simp; omega
    rcases mon with h | h
    · calc
        _ = ∑ n ∈ range N, (v (n+1)-v n) := sum_congr rfl fun n hn =>
          abs_sub_comm .. |>.trans (abs_of_nonneg (sub_nonneg.mpr
            (h (inc n (mem_range.mp hn)).1 (inc n (mem_range.mp hn)).2 (Nat.le_succ n))))
        _ = v N - v 0 := sum_range_sub v N
        _ ≤ _ := sub_le_sub (band N le_rfl).2 (band 0 (Nat.zero_le _)).1
    · calc
        _ = ∑ n ∈ range N, (v n-v (n+1)) := sum_congr rfl fun n hn =>
          abs_of_nonneg (sub_nonneg.mpr
            (h (inc n (mem_range.mp hn)).1 (inc n (mem_range.mp hn)).2 (Nat.le_succ n)))
        _ = v 0 - v N := sum_range_sub' v N
        _ ≤ _ := sub_le_sub (band 0 (Nat.zero_le _)).2 (band N le_rfl).1
  change ‖∑ n ∈ range (N+1), z n‖ ≤ _
  rw [sum_congr rfl (fun n hn => step n (Nat.lt_succ_iff.mp (mem_range.mp hn))),
      weighted_telescope]
  have rem : ‖∑ n ∈ range N, z (n+1)*(c n-c (n+1))‖ ≤ 2*Real.pi*(Q-q)/(4*q)^2 := by
    calc
      _ ≤ ∑ n ∈ range N, ‖z (n+1)*(c n-c (n+1))‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ range N, 2*Real.pi*|v n-v (n+1)|/(4*q)^2 := by
        apply sum_le_sum
        intro n hn
        have hn' := mem_range.mp hn
        rw [norm_mul, norm_wave, one_mul]
        exact reciprocal_variation hq (band n (by omega)).1 (band (n+1) (by omega)).1
          ((band n (by omega)).2.trans hQ) ((band (n+1) (by omega)).2.trans hQ)
      _ = 2*Real.pi*(∑ n ∈ range N, |v n-v (n+1)|)/(4*q)^2 := by
        rw [mul_sum, sum_div]
      _ ≤ _ := by gcongr
  apply (norm_add_le ..).trans
  apply add_le_add _ rem
  apply (norm_sub_le ..).trans
  simp only [norm_mul, z, norm_wave, one_mul]
  calc
    _ ≤ 1/(4*q) + 1/(4*q) := add_le_add (cb N le_rfl) (cb 0 (Nat.zero_le N))
    _ = _ := by ring

open scoped ComplexConjugate

private theorem shift_window {B K d : ℕ} (hd : K+d ≤ B) (f : ℕ → ℂ)
    (hf : ∀ i < B, i < d ∨ K+d ≤ i → f i = 0) :
    (∑ i ∈ range B, f i) = ∑ j ∈ range K, f (j+d) := by
  rw [← Nat.Ico_zero_eq_range K, sum_Ico_add', zero_add]
  symm
  apply sum_subset
  · intro i hi
    exact mem_range.mpr ((mem_Ico.mp hi).2.trans_le hd)
  · intro i hi h
    apply hf i (mem_range.mp hi)
    simp_all only [mem_Ico, not_and_or, not_le, not_lt]

/-- The energy of the row sums of a finite complex matrix expressed via its columns. -/
private theorem column_energy (B R : ℕ) (u : ℕ → ℕ → ℂ) :
    (∑ i ∈ range B, ‖∑ r ∈ range R, u i r‖^2) ≤
      ∑ r ∈ range R, ∑ s ∈ range R, ‖∑ i ∈ range B, conj (u i r) * u i s‖ := by
  let v i := ∑ r ∈ range R, u i r
  have he : ((∑ i ∈ range B, ‖v i‖^2 : ℝ) : ℂ) =
      ∑ r ∈ range R, ∑ s ∈ range R, ∑ i ∈ range B, conj (u i r) * u i s := by
    simp only [Complex.ofReal_sum, Complex.sq_norm, Complex.normSq_eq_conj_mul_self,
      v, map_sum, sum_mul, mul_sum]
    conv_rhs => rw [sum_comm]
    rw [sum_comm]
    exact sum_congr rfl (fun _ _ => sum_comm)
  calc
    _ = ‖((∑ i ∈ range B, ‖v i‖^2 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    _ ≤ _ := by rw [he]; exact (norm_sum_le ..).trans (sum_le_sum (fun _ _ => norm_sum_le ..))

private theorem ordered_pairs (A : ℕ → ℕ → ℝ) (D : ℝ) (V : ℕ → ℝ) (R : ℕ)
    (symm : ∀ r s, A r s = A s r)
    (diag : ∀ r < R, A r r ≤ D)
    (off : ∀ r s, r < s → s < R → A r s ≤ V (s-r))
    (nn : ∀ r, 0 ≤ V r) :
    (∑ r ∈ range R, ∑ s ∈ range R, A r s) ≤
      R * (D + 2 * ∑ k ∈ range R, V (k+1)) := by
  have row (s : ℕ) (hs : s < R) : (∑ r ∈ range s, A r s) ≤ ∑ k ∈ range R, V (k+1) := by
    calc
      _ ≤ ∑ r ∈ range s, V (s-r) := sum_le_sum fun r hr => off r s (mem_range.mp hr) hs
      _ = ∑ k ∈ range s, V (k+1) := by
        rw [← sum_range_reflect (fun k => V (k+1)) s]
        apply sum_congr rfl
        intro r hr
        congr 1
        have := mem_range.mp hr
        omega
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (range_mono hs.le) (fun k _ _ => nn _)
  have prefixBound (K : ℕ) (hK : K ≤ R) : (∑ r ∈ range K, ∑ s ∈ range K, A r s) ≤
      K * (D + 2 * ∑ k ∈ range R, V (k+1)) := by
    induction K with
    | zero => simp
    | succ K ih =>
      rw [sum_range_succ, sum_range_succ (A K)]
      simp_rw [sum_range_succ (A _)]
      rw [sum_add_distrib]
      have hs : (∑ s ∈ range K, A K s) = ∑ s ∈ range K, A s K := sum_congr rfl fun s _ => symm K s
      rw [hs, Nat.cast_succ]
      linarith [row K (by omega), diag K (by omega), ih (by omega)]
  exact prefixBound R le_rfl

/-- Finite van der Corput inequality. The overlap for a shift of r has N-r terms.
The support window has N+R terms even if the block is truncated. -/
theorem shift_bound (z : ℕ → ℂ) (N R : ℕ) (V : ℕ → ℝ)
    (hz : ∀ n < N, ‖z n‖ ≤ 1) (nn : ∀ r, 0 ≤ V r)
    (hv : ∀ r, 0 < r → r < R →
      ‖∑ k ∈ range (N-r), conj (z (k+r)) * z k‖ ≤ V r) :
    (R:ℝ)^2 * ‖∑ n ∈ range N, z n‖^2 ≤
      (N+R : ℝ) * R * (N + 2 * ∑ r ∈ range R, V (r+1)) := by
  let u (i r : ℕ) : ℂ := if r ≤ i ∧ i < N+r then z (i-r) else 0
  let A (r s : ℕ) := ‖∑ i ∈ range (N+R), conj (u i r) * u i s‖
  have trn (r : ℕ) (hr : r < R) : (∑ i ∈ range (N+R), u i r) = ∑ k ∈ range N, z k := by
    rw [shift_window (K := N) (d := r) (by omega)]
    · apply sum_congr rfl
      intro k hk
      simp [u, mem_range.mp hk]
    · intro i hi h
      rcases h with h | h <;> simp [u, show ¬(r ≤ i ∧ i < N+r) by omega]
  have sum_u : (∑ i ∈ range (N+R), ∑ r ∈ range R, u i r) = (R:ℂ) * ∑ k ∈ range N, z k := by
    rw [sum_comm, sum_congr rfl (fun r hr => trn r (mem_range.mp hr))]
    simp
  have asymm (r s) : A r s = A s r := by
    unfold A
    rw [← Complex.norm_conj (∑ i ∈ range (N+R), conj (u i r) * u i s)]
    simp [mul_comm]
  have overlap (r s : ℕ) (hrs : r ≤ s) (hs : s < R) :
      A r s = ‖∑ k ∈ range (N-(s-r)), conj (z (k+(s-r))) * z k‖ := by
    unfold A
    rw [shift_window (K := N-(s-r)) (d := s) (by omega)]
    · congr 1
      apply sum_congr rfl
      intro k hk
      have := mem_range.mp hk
      simp [u, show r ≤ k+s by omega, show k+s < N+r by omega, show k<N by omega,
        show k+s-r = k+(s-r) by omega]
    · intro i hi h
      by_cases hr : r ≤ i ∧ i < N+r
      · have hs' : ¬ (s ≤ i ∧ i < N+s) := by omega
        simp [u, hs']
      · simp [u, hr]
  have diag (r : ℕ) (hr : r < R) : A r r ≤ N := by
    rw [overlap r r le_rfl hr]
    simp only [Nat.sub_self, Nat.sub_zero, add_zero]
    apply (norm_sum_le ..).trans
    calc
      _ ≤ ∑ k ∈ range N, (1 : ℝ)*1 := sum_le_sum fun k hk => by
        rw [norm_mul, Complex.norm_conj]
        gcongr <;> apply hz k (mem_range.mp hk)
      _ = _ := by simp
  have bound := ordered_pairs A N V R asymm diag (fun r s hrs hs => by
    rw [overlap r s hrs.le hs]
    exact hv (s-r) (by omega) (by omega)) nn
  have cs : ‖∑ i ∈ range (N+R), ∑ r ∈ range R, u i r‖^2 ≤
      (N+R:ℝ) * ∑ i ∈ range (N+R), ‖∑ r ∈ range R, u i r‖^2 := by
    calc
      _ ≤ (∑ i ∈ range (N+R), ‖∑ r ∈ range R, u i r‖)^2 := by gcongr; apply norm_sum_le
      _ ≤ _ := by simpa using (sq_sum_le_card_mul_sum_sq
        (s := range (N+R)) (f := fun i => ‖∑ r ∈ range R, u i r‖))
  rw [sum_u, norm_mul, Complex.norm_natCast, mul_pow] at cs
  rw [mul_assoc]
  exact cs.trans (mul_le_mul_of_nonneg_left ((column_energy (N+R) R u).trans bound) (by positivity))

def delta (x : ℕ → ℝ) (n : ℕ) := x (n+1)-x n

private theorem sum_delta_from (x : ℕ → ℝ) (n r : ℕ) :
    (∑ j ∈ range r, delta x (n+j)) = x (n+r)-x n := by
  simpa [delta, Nat.add_assoc] using sum_range_sub (fun j => x (n+j)) r

private theorem shifted_delta (x : ℕ → ℝ) (n r : ℕ) :
    delta (fun k => x (k+r)-x k) n = ∑ j ∈ range r, delta (delta x) (n+j) := by
  rw [sum_delta_from]
  simp [delta, Nat.add_right_comm]
  ring

theorem wave_conj (x : ℝ) : conj (wave x) = wave (-x) := by
  unfold wave
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, mul_neg, neg_mul]
  push_cast
  ring

theorem wave_correlation (x : ℕ → ℝ) (N r : ℕ) :
    ‖∑ k ∈ range (N-r), conj (wave (x (k+r))) * wave (x k)‖ =
      ‖∑ k ∈ range (N-r), wave (x (k+r)-x k)‖ := by
  rw [← Complex.norm_conj (∑ k ∈ range (N-r), wave (x (k+r)-x k))]
  simp only [map_sum, wave_conj, ← wave_add]
  simp [sub_eq_add_neg, add_comm]

private theorem shifted_band (x : ℕ → ℝ) (N : ℕ) (q Q : ℝ) (r : ℕ)
    (bnd : ∀ k < N, q ≤ delta (delta x) k ∧ delta (delta x) k ≤ Q)
    (mon : AntitoneOn (delta (delta x)) (Set.Icc 0 N)) :
    (∀ n < N-r, (r:ℝ)*q ≤ delta (fun k => x (k+r)-x k) n ∧
      delta (fun k => x (k+r)-x k) n ≤ (r:ℝ)*Q) ∧
    AntitoneOn (delta (fun k => x (k+r)-x k)) (Set.Icc 0 (N-r)) := by
  constructor
  · intro n hn
    rw [shifted_delta]
    constructor
    · calc
        _ = ∑ _j ∈ range r, q := by simp
        _ ≤ _ := sum_le_sum fun j hj => (bnd (n+j) (by have := mem_range.mp hj; omega)).1
    · calc
        _ ≤ ∑ _j ∈ range r, Q := sum_le_sum fun j hj => (bnd (n+j) (by have := mem_range.mp hj; omega)).2
        _ = _ := by simp
  · intro a ha b hb hab
    simp only [shifted_delta]
    by_cases hr : r ≤ N
    · apply sum_le_sum
      intro j hj
      have := mem_range.mp hj
      apply mon <;> simp_all [Set.mem_Icc] <;> omega
    · have he : a = b := by simp_all [Nat.sub_eq_zero_of_le (by omega : N ≤ r)]
      rw [he]

/-- Cancellation for one correlation, provided the shift stays below the first
integer crossing of the differenced phase increment. -/
theorem correlation_bound (x : ℕ → ℝ) (N r : ℕ) (q C : ℝ)
    (hq : 0 < q) (hC : 1 ≤ C) (hr : 0 < r) (hcut : (r:ℝ)*(C*q) ≤ 1/2)
    (bnd : ∀ k < N, q ≤ delta (delta x) k ∧ delta (delta x) k ≤ C*q)
    (mon : AntitoneOn (delta (delta x)) (Set.Icc 0 N)) :
    ‖∑ k ∈ range (N-r), conj (wave (x (k+r))) * wave (x k)‖ ≤
      (1 + Real.pi*C)/((r:ℝ)*q) := by
  rw [wave_correlation]
  obtain ⟨hb,hm⟩ := shifted_band x N q (C*q) r bnd mon
  let y (k : ℕ) := x (k+r)-x k
  cases e : N-r with
  | zero => simp; positivity
  | succ m =>
    have estimate := small_increment_test y m (r*q) (r*(C*q)) (by positivity) hcut
      (fun n hn => hb n (by omega))
      (Or.inr (hm.mono (show Set.Icc 0 m ⊆ Set.Icc 0 (N-r) by intro k hk; simp_all [Set.mem_Icc]; omega)))
    apply estimate.trans
    have hr' : 0 < (r:ℝ) := by exact_mod_cast hr
    field_simp
    nlinarith [mul_pos Real.pi_pos (show 0 < C by linarith), Real.pi_pos]

/-- One differencing step for a phase with positive decreasing second differences. -/
theorem second_difference (x : ℕ → ℝ) (N R : ℕ) (q C : ℝ)
    (hq : 0 < q) (hC : 1 ≤ C) (hcut : (R:ℝ)*(C*q) ≤ 1/2)
    (bnd : ∀ k < N, q ≤ delta (delta x) k ∧ delta (delta x) k ≤ C*q)
    (mon : AntitoneOn (delta (delta x)) (Set.Icc 0 N)) :
    (R:ℝ)^2 * ‖∑ n ∈ range N, wave (x n)‖^2 ≤
      (N+R:ℝ) * R * (N + 2 * ((1+Real.pi*C)/q) * ∑ r ∈ range R, (1/(r+1:ℝ))) := by
  have h := shift_bound (fun n => wave (x n)) N R (fun r => (1+Real.pi*C)/((r:ℝ)*q))
    (fun n _ => (norm_wave (x n)).le) (fun r => by positivity)
    (fun r hr hrR => correlation_bound x N r q C hq hC hr
      ((mul_le_mul_of_nonneg_right (by exact_mod_cast hrR.le) (by positivity)).trans hcut) bnd mon)
  have eqsum : (∑ r ∈ range R, (1+Real.pi*C)/((↑(r+1):ℝ)*q)) =
      ((1+Real.pi*C)/q) * ∑ r ∈ range R, (1/(r+1:ℝ)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro r _
    push_cast
    rw [div_eq_mul_inv, mul_inv_rev]
    ring
  rwa [eqsum, ← mul_assoc] at h

private theorem trivial_sum (x : ℕ → ℝ) (N : ℕ) :
    ‖∑ n ∈ range N, wave (x n)‖ ≤ N := by
  simpa only [norm_wave, sum_const, card_range, nsmul_eq_mul, mul_one] using
    (norm_sum_le (range N) (fun n => wave (x n)))

/-- Choose the shift from the size of the second difference and sum the reciprocal shifts. -/
theorem sqrt_curvature_bound (x : ℕ → ℝ) (N : ℕ) (q C : ℝ)
    (hN : 1 ≤ N) (hq : 0 < q) (hC : 1 ≤ C)
    (bnd : ∀ k < N, q ≤ delta (delta x) k ∧ delta (delta x) k ≤ C*q)
    (mon : AntitoneOn (delta (delta x)) (Set.Icc 0 N)) :
    ‖∑ n ∈ range N, wave (x n)‖^2 ≤
      32*(1+Real.pi*C)*(1+C)*(1+Real.log N)*((N:ℝ)^2*q + N + 1/q) := by
  let D := 1+Real.pi*C
  let H := 1+Real.log N
  have cpos : 0 < C := by linarith
  have n1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have d1 : 1 ≤ D := by dsimp [D]; linarith [mul_nonneg Real.pi_pos.le cpos.le]
  have h1 : 1 ≤ H := by dsimp [H]; linarith [Real.log_nonneg n1]
  change _ ≤ 32*D*(1+C)*H*_
  by_cases small : C*q ≤ 1/2
  · let R := min N ⌊1/(2*C*q)⌋₊
    have inv1 : 1 ≤ 1/(2*C*q) := by rw [le_div_iff₀ (by positivity)]; linarith
    have r1 : 1 ≤ R := le_min hN (Nat.le_floor (by simpa using inv1))
    have rn : R ≤ N := min_le_left ..
    have rp : (0:ℝ) < R := by exact_mod_cast r1
    have cut : (R:ℝ)*(C*q) ≤ 1/2 := by
      have rb : (R:ℝ) ≤ 1/(2*C*q) :=
        (Nat.cast_le.mpr (min_le_right ..)).trans (Nat.floor_le (by positivity))
      rw [le_div_iff₀ (by positivity)] at rb
      linarith
    have ratio : (N:ℝ) / R ≤ 1 + 4*C*N*q := by
      by_cases h : N ≤ ⌊1/(2*C*q)⌋₊
      · simp [R, min_eq_left h, div_self (by positivity : (N:ℝ) ≠ 0)]
        positivity
      · have lt := Nat.div_two_lt_floor inv1
        have rinv : (1 / (2*C*q)) / 2 < (R:ℝ) := by simpa [R, min_eq_right (le_of_not_ge h)] using lt
        have rr : 1 ≤ 4*C*q*R := by
          field_simp at rinv
          linarith
        rw [div_le_iff₀ rp]
        nlinarith [mul_le_mul_of_nonneg_left rr (by positivity : (0:ℝ) ≤ N)]
    have har : (∑ r ∈ range R, 1/(r+1:ℝ)) ≤ H := by
      have hr := harmonic_le_one_add_log R
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Nat.cast_add,
        Nat.cast_one, one_div] at hr ⊢
      calc
        _ ≤ 1+Real.log R := by simpa using hr
        _ ≤ _ := by dsimp [H]; linarith [Real.log_le_log rp (Nat.cast_le.mpr rn)]
    have sq := second_difference x N R q C hq hC cut bnd mon
    have raw : ‖∑ n ∈ range N, wave (x n)‖^2 ≤
        2*((N:ℝ)/R)*(N+2*(D/q)*H) := by
      apply (le_of_mul_le_mul_left ?_ (sq_pos_of_pos rp))
      calc
        _ ≤ _ := sq
        _ ≤ ((N:ℝ)+N)*R*(N+2*(D/q)*H) := by
          dsimp [D]; gcongr
        _ = _ := by field_simp; ring
    apply raw.trans
    calc
      _ ≤ 2*(1+4*C*N*q)*(N+2*(D/q)*H) := by gcongr
      _ = 2*N + 4*(D*H)*(1/q) + 8*C*((N:ℝ)^2*q) + 16*C*(D*H)*N := by field_simp; ring
      _ ≤ _ := by
        let K := 32*D*(1+C)*H
        have dh : 1 ≤ D*H := one_le_mul_of_one_le_of_one_le d1 h1
        have c1 : 1 ≤ 1+C := by linarith
        have coeff : 32*(D*H) ≤ K := by
          dsimp [K]; nlinarith [mul_nonneg (show 0 ≤ D*H by positivity) cpos.le]
        have coeff' : 32*C*(D*H) ≤ K := by dsimp [K]; nlinarith [dh]
        have coeff'' : 32*C ≤ 32*C*(D*H) := le_mul_of_one_le_right (by positivity) dh
        calc
          _ ≤ K*N + K*(1/q) + K*((N:ℝ)^2*q) := by
            have hn : 2 + 16*C*(D*H) ≤ K := by dsimp [K]; nlinarith [dh, mul_nonneg cpos.le (show 0 ≤ D*H by positivity)]
            have ha := mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg N)
            have hb := mul_le_mul_of_nonneg_right (show 4*(D*H) ≤ K by linarith) (by positivity : 0 ≤ 1/q)
            have hc := mul_le_mul_of_nonneg_right (show 8*C ≤ K by linarith) (by positivity : 0 ≤ (N:ℝ)^2*q)
            linarith
          _ = _ := by dsimp [K]; ring
  · have ht := trivial_sum x N
    have hn : ‖∑ n ∈ range N, wave (x n)‖^2 ≤ (N:ℝ)^2 := by gcongr
    apply hn.trans
    have one : 1 ≤ 2*C*q := by linarith
    calc
      _ ≤ 2*C*((N:ℝ)^2*q) := by nlinarith [mul_le_mul_of_nonneg_left one (sq_nonneg (N:ℝ))]
      _ ≤ _ := by
        have hc : 2*C ≤ 32*D*(1+C)*H := calc
          _ ≤ 32*1*(1+C)*1 := by linarith
          _ ≤ _ := by gcongr
        apply mul_le_mul hc _ (by positivity) (by positivity)
        linarith [show (0:ℝ) ≤ 1/q by positivity, Nat.cast_nonneg (α := ℝ) N]

private theorem shifted_second (x : ℕ → ℝ) (r n : ℕ) :
    delta (delta (fun k => x k - x (k+r))) n =
      ∑ j ∈ range r, -delta (delta (delta x)) (n+j) := by
  rw [sum_neg_distrib, sum_delta_from]
  simp only [delta, Nat.add_right_comm n 1 r, Nat.add_right_comm (n+1) 1 r]
  ring

/-- A second differencing step in a region of decreasing positive -Δ³. -/
theorem third_difference (x : ℕ → ℝ) (N R : ℕ) (μ C : ℝ)
    (hN : 1 ≤ N) (hR : 1 ≤ R) (hrN : R ≤ N) (hμ : 0 < μ) (hC : 1 ≤ C)
    (bnd : ∀ k < N, μ ≤ -delta (delta (delta x)) k ∧ -delta (delta (delta x)) k ≤ C*μ)
    (mon : AntitoneOn (fun k => -delta (delta (delta x)) k) (Set.Icc 0 N)) :
    ‖∑ n ∈ range N, wave (x n)‖^2 ≤ 2*(N:ℝ)^2/R +
      4*N*Real.sqrt (32*(1+Real.pi*C)*(1+C)*(1+Real.log N)*
        ((N:ℝ)^2*R*μ + N + 1/μ)) := by
  let D := Real.sqrt (32*(1+Real.pi*C)*(1+C)*(1+Real.log N)*((N:ℝ)^2*R*μ+N+1/μ))
  have corr (r : ℕ) (hr : 0 < r) (hrR : r < R) :
      ‖∑ k ∈ range (N-r), conj (wave (x (k+r))) * wave (x k)‖ ≤ D := by
    let y (k : ℕ) := x k-x (k+r)
    have he : ∀ k, conj (wave (x (k+r))) * wave (x k) = wave (y k) := by
      intro k
      rw [wave_conj, ← wave_add]
      simp [y, sub_eq_add_neg, add_comm]
    simp_rw [he]
    have hb (k : ℕ) (hk : k < N-r) :
        r*μ ≤ delta (delta y) k ∧ delta (delta y) k ≤ C*(r*μ) := by
      rw [show delta (delta y) k = _ from shifted_second x r k]
      constructor
      · calc
          _ = ∑ _j ∈ range r, μ := by simp
          _ ≤ _ := sum_le_sum fun j hj => (bnd (k+j) (by have := mem_range.mp hj; omega)).1
      · calc
          _ ≤ ∑ _j ∈ range r, C*μ := sum_le_sum fun j hj => (bnd (k+j) (by have := mem_range.mp hj; omega)).2
          _ = _ := by simp; ring
    have hm : AntitoneOn (delta (delta y)) (Set.Icc 0 (N-r)) := by
      intro a ha b hb hab
      change delta (delta (fun k => x k-x (k+r))) b ≤ delta (delta (fun k => x k-x (k+r))) a
      rw [shifted_second, shifted_second]
      apply sum_le_sum
      intro k hk
      have := mem_range.mp hk
      apply mon <;> simp_all [Set.mem_Icc] <;> omega
    have hnr : 1 ≤ N-r := by omega
    have hn' : 0 < (↑(N-r):ℝ) := by exact_mod_cast hnr
    have hnr' : (↑(N-r):ℝ) ≤ N := by exact_mod_cast Nat.sub_le N r
    have hrr : (1:ℝ) ≤ r := by exact_mod_cast hr
    have hg := sqrt_curvature_bound y (N-r) (r*μ) C hnr (by positivity) hC hb hm
    apply Real.le_sqrt_of_sq_le
    apply hg.trans
    have lg : 1 ≤ (1+Real.log (↑(N-r):ℝ)) := by
      linarith [Real.log_nonneg (by exact_mod_cast hnr : (1:ℝ) ≤ ↑(N-r))]
    have hinv : 1/((r:ℝ)*μ) ≤ 1/μ := by gcongr; exact le_mul_of_one_le_left hμ.le hrr
    rw [mul_assoc ((N:ℝ)^2)]
    gcongr
  have b := shift_bound (fun n => wave (x n)) N R (fun _ => D)
    (fun n _ => (norm_wave _).le) (fun _ => Real.sqrt_nonneg _) corr
  simp only [sum_const, card_range, nsmul_eq_mul] at b
  have rp : 0 < (R:ℝ) := by exact_mod_cast hR
  change _ ≤ 2*(N:ℝ)^2/R + 4*N*D
  apply le_of_mul_le_mul_left (a := (R:ℝ)^2) _ (by positivity)
  calc
    _ ≤ _ := b
    _ ≤ ((N:ℝ)+N)*R*(N+2*(R*D)) := by gcongr
    _ = _ := by field_simp; ring

noncomputable def diff : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f, x => f x
  | n+1, f, x => diff n f (x+1)-diff n f x

private theorem deriv_diff (f g : ℝ → ℝ) (h : ∀ x > 0, HasDerivAt f (g x) x)
    (n : ℕ) (x : ℝ) (hx : 0 < x) : HasDerivAt (diff n f) (diff n g x) x := by
  induction n generalizing x with
  | zero => exact h _ hx
  | succ n ih =>
    exact ((ih (x+1) (by linarith)).comp_add_const x 1).sub (ih x hx)

private theorem next_diff (f g : ℝ → ℝ) (h : ∀ x > 0, HasDerivAt f (g x) x)
    (n : ℕ) (x : ℝ) (hx : 0 < x) :
    ∃ t ∈ Set.Icc x (x+1), diff (n+1) f x = diff n g t := by
  obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope (diff n f) (diff n g) (a := x) (b := x+1)
    (by linarith) (fun y hy => (deriv_diff _ _ h n y (hx.trans_le hy.1)).continuousAt.continuousWithinAt)
    (fun y hy => deriv_diff _ _ h n y (hx.trans hy.1))
  exact ⟨t, ⟨ht.1.le, ht.2.le⟩, by simpa [diff] using he.symm⟩

noncomputable def powerCoeff : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n+1, p => p * powerCoeff n (p-1)

theorem power_mean (n : ℕ) (A p x : ℝ) (hx : 0 < x) :
    ∃ t ∈ Set.Icc x (x+n), diff n (fun y => A*y^p) x = A * powerCoeff n p * t^(p-n) := by
  induction n generalizing A p x with
  | zero => exact ⟨x, by simp, by simp [diff, powerCoeff]⟩
  | succ n ih =>
    have der (u : ℝ) (hu : 0 < u) :
        HasDerivAt (fun y : ℝ => A*y^p) (A*p*u^(p-1)) u := by
      simpa [mul_assoc] using (Real.hasDerivAt_rpow_const (p := p) (Or.inl hu.ne')).const_mul A
    obtain ⟨v,hv,he⟩ := next_diff _ _ der n x hx
    obtain ⟨t,ht,he'⟩ := ih (A*p) (p-1) v (hx.trans_le hv.1)
    refine ⟨t, ⟨hv.1.trans ht.1, ?_⟩, ?_⟩
    · push_cast; linarith [ht.2, hv.2]
    · rw [he, he', powerCoeff]
      push_cast
      ring_nf

noncomputable def powerPhase (A p M : ℝ) (k : ℕ) : ℝ := A*(M+k)^p

private theorem sample_eq (n : ℕ) (A p M : ℝ) (k : ℕ) :
    (delta^[n]) (powerPhase A p M) k = diff n (fun y => A*y^p) (M+k) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply', delta, ih, Nat.cast_succ, ← add_assoc, diff]

private theorem moment (n : ℕ) (A p M : ℝ) (k : ℕ) (hM : 0 < M) :
    ∃ t ∈ Set.Icc (M+k) (M+k+n),
      (delta^[n]) (powerPhase A p M) k = A * powerCoeff n p * t^(p-n) := by
  rw [sample_eq]
  exact power_mean n A p _ (by positivity)

theorem second_power_phase (A p M : ℝ) (N : ℕ) (ha : 0 < A) (hp : p < 0) (hm : 1 ≤ M) (hn : N ≤ M) :
    let q := A*(p*(p-1))*(4*M)^(p-2)
    let C := (4:ℝ)^(2-p)
    (0 < q ∧ 1 ≤ C) ∧ (∀ k < N, q ≤ delta (delta (powerPhase A p M)) k ∧
      delta (delta (powerPhase A p M)) k ≤ C*q) ∧
      Antitone (delta (delta (powerPhase A p M))) := by
  dsimp only
  have hm' : 0 < M := by linarith
  have hcoef : 0 < A*(p*(p-1)) := mul_pos ha (mul_pos_of_neg_of_neg hp (by linarith))
  have mul4 : 4^(2-p) * (4*M)^(p-2) = M^(p-2) := by
    rw [Real.mul_rpow (by norm_num) hm'.le, ← mul_assoc, ← Real.rpow_add (by norm_num)]
    norm_num
  refine ⟨⟨by positivity, Real.one_le_rpow (by norm_num) (by linarith)⟩, ?_, ?_⟩
  · intro k hk
    obtain ⟨t,ht,he⟩ := moment 2 A p M k hm'
    change delta (delta (powerPhase A p M)) k = _ at he
    norm_num [powerCoeff] at he
    rw [he]
    have hl : M ≤ t := by linarith [ht.1, (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    norm_num at ht
    have hu : t ≤ 4*M := by linarith [ht.2, (by exact_mod_cast hk : (k:ℝ) < N)]
    constructor
    · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (hm'.trans_le hl) hu (by linarith)) hcoef.le
    · calc
        _ ≤ A*(p*(p-1))*M^(p-2) := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hm' hl (by linarith)) hcoef.le
        _ = _ := by rw [← mul4]; ring
  · apply antitone_nat_of_succ_le
    intro k
    obtain ⟨t,ht,he⟩ := moment 3 A p M k hm'
    change delta (delta (delta (powerPhase A p M))) k = _ at he
    norm_num [powerCoeff] at he
    have ht' : 0 < t := lt_of_lt_of_le (by positivity) ht.1
    have hneg : A*(p*((p-1)*(p-1-1))) < 0 := by
      exact mul_neg_of_pos_of_neg ha (mul_neg_of_neg_of_pos hp (mul_pos_of_neg_of_neg (by linarith) (by linarith)))
    exact sub_nonpos.mp (show delta (delta (delta (powerPhase A p M))) k ≤ 0 by
      rw [he]; exact (mul_neg_of_neg_of_pos hneg (Real.rpow_pos_of_pos ht' _)).le)

theorem third_reciprocal_square (A M : ℝ) (N : ℕ) (ha : 0 < A) (hm : 1 ≤ M) (hn : N ≤ M) :
    let q := 24*A/(5*M)^5
    (∀ k < N, q ≤ -delta (delta (delta (powerPhase A (-2) M))) k ∧
      -delta (delta (delta (powerPhase A (-2) M))) k ≤ 3125*q) ∧
      Antitone (fun k => -delta (delta (delta (powerPhase A (-2) M))) k) := by
  dsimp only
  have hm' : 0 < M := by linarith
  constructor
  · intro k hk
    obtain ⟨t,ht,he⟩ := moment 3 A (-2) M k hm'
    change delta (delta (delta (powerPhase A (-2) M))) k = _ at he
    norm_num [powerCoeff] at ht he
    have hl : M ≤ t := by linarith [ht.1, (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    have hu : t ≤ 5*M := by linarith [ht.2, (by exact_mod_cast hk : (k:ℝ) < N)]
    rw [he]
    have form : - -(A*24*(t^5)⁻¹) = 24*A/t^5 := by ring
    rw [form]
    constructor
    · have ht' : 0 < t := hm'.trans_le hl
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ ht'.le hu 5)
    · calc
        _ ≤ 24*A/M^5 := div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hm'.le hl 5)
        _ = _ := by ring
  · apply antitone_nat_of_succ_le
    intro k
    obtain ⟨t,ht,he⟩ := moment 4 A (-2) M k hm'
    change delta (delta (delta (delta (powerPhase A (-2) M)))) k = _ at he
    norm_num [powerCoeff] at he
    have ht' : 0 < t := lt_of_lt_of_le (by positivity) ht.1
    apply neg_le_neg
    apply sub_nonneg.mp
    change 0 ≤ delta (delta (delta (delta (powerPhase A (-2) M)))) k
    rw [he]; positivity



open scoped Real

noncomputable def bern (x : ℝ) := bernoulliFun 2 (Int.fract x)
noncomputable def saw (x : ℝ) := Int.fract x - 1/2

theorem one_sided_smoothing (t d : ℝ) (hd : 0 < d) (h1 : d ≤ 1) :
    2*d*saw (t+d)-d^2 ≤ bern (t+d)-bern t ∧ bern (t+d)-bern t ≤ 2*d*saw t+d^2 := by
  let u := Int.fract t
  have u0 : 0 ≤ u := Int.fract_nonneg _
  have u1 : u < 1 := Int.fract_lt_one _
  have shift : Int.fract (t+d) = Int.fract (u+d) := by
    conv_lhs => rw [← Int.fract_add_floor t]
    rw [add_right_comm, Int.fract_add_intCast]
  simp only [saw, bern, bernoulliFun_two, shift]
  change 2*d*(Int.fract (u+d)-1/2)-d^2 ≤ _ - (u^2-u+6⁻¹) ∧
    _ - (u^2-u+6⁻¹) ≤ 2*d*(u-1/2)+d^2
  by_cases h : u+d < 1
  · rw [Int.fract_eq_self.mpr ⟨by linarith,h⟩]
    constructor <;> linarith only
  · have floor_one : ⌊u+d⌋ = 1 := Int.floor_eq_iff.mpr (by push_cast; constructor <;> linarith)
    rw [show Int.fract (u+d) = u+d-1 by simp [Int.fract, floor_one]]
    constructor <;> linarith

private noncomputable def gain : ℂ := -(2*(Real.pi:ℂ)*Complex.I)^2 / (2:ℕ).factorial

private theorem bern_series (x : ℝ) :
    HasSum (fun j : ℤ => (1/(j:ℂ)^2)*wave (j*x)) (gain*(bern x:ℂ)) := by
  have hh := hasSum_one_div_pow_mul_fourier_mul_bernoulliFun (k := 2) (by norm_num)
    (x := Int.fract x) ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  simp only [AddCircle.coe_fract] at hh
  apply hh.congr_fun
  intro j
  congr 1
  rw [fourier_coe_apply]
  unfold wave
  push_cast
  congr 1
  ring

private theorem translated_difference (x c d : ℝ) :
    HasSum (fun j : ℤ => (1/(j:ℂ)^2)*wave (j*c)*(wave (j*d)-1)*wave (j*x))
      (gain*((bern (x+c+d):ℂ)-(bern (x+c):ℂ))) := by
  rw [mul_sub]
  apply ((bern_series (x+c+d)).sub (bern_series (x+c))).congr_fun
  intro j
  simp only [mul_add, wave_add]
  ring

private theorem holder_chord (x : ℝ) (hx : x ≠ 0) :
    ‖wave x-1‖ ≤ (2+2*Real.pi)*|x|^(49/100:ℝ) := by
  have hxp := abs_pos.mpr hx
  by_cases h : |x| ≤ 1
  · have b : |x| ≤ |x|^(49/100:ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hxp h (by norm_num : (49:ℝ)/100 ≤ 1)
    have step : ‖wave x-1‖ ≤ 2*Real.pi*|x| := by simpa [wave] using chord_upper x 0
    exact step.trans (mul_le_mul (by linarith) b hxp.le (by positivity))
  · have b := Real.one_le_rpow (le_of_not_ge h) (by norm_num : 0 ≤ (49:ℝ)/100)
    calc
      _ ≤ ‖wave x‖+‖(1:ℂ)‖ := norm_sub_le ..
      _ ≤ _ := by rw [norm_wave, norm_one]; nlinarith [Real.pi_pos,
        mul_nonneg Real.pi_pos.le (Real.rpow_nonneg (abs_nonneg x) (49/100))]

private noncomputable def fourierCost : ℝ :=
    (2+2*Real.pi)*(∑' j : ℤ, |(j:ℝ)|^(-(101/100):ℝ))/‖gain‖

private theorem gain_pos : 0 < ‖gain‖ := by
  apply norm_pos_iff.mpr
  dsimp [gain]; norm_num [Real.pi_ne_zero, Complex.I_ne_zero]

private theorem translated_sum_bound (x : ℕ → ℝ) (N : ℕ) (d c A : ℝ) (hd : 0 < d) (_hA : 0 ≤ A)
    (freq : ∀ j : ℤ, j ≠ 0 → ‖∑ n ∈ range N, wave (j*x n)‖ ≤ A*|(j:ℝ)|^(1/2:ℝ)) :
    |∑ n ∈ range N, (bern (x n+c+d)-bern (x n+c))| ≤ fourierCost*A*d^(49/100:ℝ) := by
  let W : ℤ → ℝ := fun j => |(j:ℝ)|^(-(101/100):ℝ)
  let T := (2+2*Real.pi)*A*d^(49/100:ℝ)
  have ser := hasSum_sum (s := range N) (fun n _ => translated_difference (x n) c d)
  have bound := ser.norm_le_of_bounded
    (((Real.summable_abs_int_rpow (b := 101/100) (by norm_num)).hasSum).mul_left T)
  have maj (j : ℤ) : ‖∑ n ∈ range N,
      1/(j:ℂ)^2*wave (j*c)*(wave (j*d)-1)*wave (j*x n)‖ ≤ T*W j := by
    rw [← mul_sum]
    by_cases hj : j = 0
    · simp [hj,W]
    have aj : 0 < |(j:ℝ)| := abs_pos.mpr (by exact_mod_cast hj)
    have v := holder_chord ((j:ℝ)*d) (mul_ne_zero (by exact_mod_cast hj) hd.ne')
    rw [abs_mul, abs_of_pos hd, Real.mul_rpow aj.le hd.le] at v
    simp only [norm_mul, norm_div, norm_one, norm_pow, Complex.norm_intCast, norm_wave, mul_one]
    calc
      _ ≤ 1/|(j:ℝ)|^2*((2+2*Real.pi)*(|(j:ℝ)|^(49/100:ℝ)*d^(49/100:ℝ)))*(A*|(j:ℝ)|^(1/2:ℝ)) := by gcongr; apply freq j hj
      _ = _ := by
        have id : |(j:ℝ)|^(49/100:ℝ)*|(j:ℝ)|^(1/2:ℝ)/|(j:ℝ)|^2 = W j := by
          rw [← Real.rpow_add aj, ← Real.rpow_natCast, ← Real.rpow_sub aj]
          norm_num [W]
        dsimp [T]
        rw [← id]; ring
  specialize bound maj
  simp only [← mul_sum, ← Complex.ofReal_sub, ← Complex.ofReal_sum, norm_mul, Complex.norm_real,
    Real.norm_eq_abs] at bound
  apply (le_of_mul_le_mul_left (a := ‖gain‖) _ gain_pos)
  apply bound.trans_eq
  dsimp [T, fourierCost]
  field_simp [gain_pos.ne']

/-- Fractional parts from a square-root frequency bound, including integer arguments. -/
theorem smooth_bound (x : ℕ → ℝ) (N : ℕ) (d A : ℝ) (hd : 0 < d) (h1 : d ≤ 1) (hA : 0 ≤ A)
    (freq : ∀ j : ℤ, j ≠ 0 → ‖∑ n ∈ range N, wave (j*x n)‖ ≤ A*|(j:ℝ)|^(1/2:ℝ)) :
    |∑ n ∈ range N, saw (x n)| ≤ N*d/2 + fourierCost*A*d^(-(51/100):ℝ)/2 := by
  have est (c : ℝ) := abs_le.mp (translated_sum_bound x N d c A hd hA freq)
  have left := sum_le_sum (s := range N) (fun n _ => (one_sided_smoothing (x n) d hd h1).2)
  have right := sum_le_sum (s := range N) (fun n _ => (one_sided_smoothing (x n-d) d hd h1).1)
  simp only [sub_add_cancel, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const,
    card_range, nsmul_eq_mul] at left right
  have hlow := (est 0).1
  have hhigh := (est (-d)).2
  simp only [add_zero] at hlow
  simp only [← sub_eq_add_neg, sub_add_cancel] at hhigh
  have hpow : d^(49/100:ℝ) = d^(-(51/100):ℝ)*d := by
    rw [← Real.rpow_add_one hd.ne']; norm_num
  simp only [hpow, sum_sub_distrib] at hlow hhigh
  rw [abs_le]
  constructor
  · apply le_of_mul_le_mul_left (a := 2*d) _ (by positivity)
    linarith
  · apply le_of_mul_le_mul_left (a := 2*d) _ (by positivity)
    linarith


private theorem log_factor {N : ℕ} {X C : ℝ} (hn : 0 < N) (hNX : N ≤ X)
    (hx : 1 ≤ X) (hc : 1 ≤ C) (hc' : C ≤ 4000) :
    32*(1+Real.pi*C)*(1+C)*(1+Real.log N) ≤ 10^14 * X^(1/10000:ℝ) := by
  have Xp := Real.one_le_rpow hx (by norm_num : 0 ≤ (1:ℝ)/10000)
  have lb := Real.log_le_rpow_div (by linarith : 0 ≤ X) (by norm_num : 0 < (1:ℝ)/10000)
  have lN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hn)
  have l : Real.log N ≤ Real.log X := Real.log_le_log (by positivity) hNX
  calc
    _ ≤ 32*(1+4*4000)*(1+4000)*(10001*X^(1/10000:ℝ)) := by
      gcongr <;> first | exact Real.pi_lt_four.le | linarith
    _ ≤ _ := by linarith

private theorem scale_energy {N : ℕ} {X m u v b h C z : ℝ}
    (hN : 0 < N) (hM : N ≤ X^m) (hm : m ≤ 1) (hx : 1 ≤ X)
    (h₁ : 1 ≤ h) (hb : 1/10000 ≤ b) (hb' : b ≤ 100)
    (hc : 1 ≤ C) (hc' : C ≤ 4000)
    (e₁ : 2*m+u ≤ z) (e₂ : m ≤ z) (e₃ : -v ≤ z) :
    32*(1+Real.pi*C)*(1+C)*(1+Real.log N)*((N:ℝ)^2*(b*h*X^u)+N+1/(b*h*X^v)) ≤
      10^19*h*X^(1/10000+z) := by
  have xp : 0 < X := by linarith
  have hp : 0 < h := by linarith
  have bp : 0 < b := by linarith
  have NX : (N:ℝ) ≤ X := hM.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hx hm)
  have front := log_factor hN NX hx hc hc'
  have bound1 : (N:ℝ)^2*(b*h*X^u) ≤ 100*h*X^z := calc
    _ ≤ (X^m)^2*(100*h*X^u) := by gcongr
    _ = 100*h*X^(2*m+u) := by
      rw [Real.rpow_add xp, mul_comm 2 m, Real.rpow_mul xp.le]; norm_num; ring
    _ ≤ _ := by gcongr
  have bound2 : (N:ℝ) ≤ h*X^z := calc
    _ ≤ X^m := hM
    _ ≤ X^z := Real.rpow_le_rpow_of_exponent_le hx e₂
    _ ≤ _ := le_mul_of_one_le_left (by positivity) h₁
  have bh : 1/(b*h) ≤ 10000 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [le_mul_of_one_le_right bp.le h₁]
  have bound3 : 1/(b*h*X^v) ≤ 10000*h*X^z := calc
    _ = 1/(b*h)*X^(-v) := by rw [Real.rpow_neg xp.le]; ring
    _ ≤ (10000*h)*X^z := by
      apply mul_le_mul (by linarith) (Real.rpow_le_rpow_of_exponent_le hx e₃) <;> positivity
  calc
    _ ≤ (10^14 * X^(1/10000:ℝ))*(10101*h*X^z) := by
      apply mul_le_mul front (by linarith) <;> positivity
    _ ≤ _ := by rw [Real.rpow_add xp]; nlinarith [mul_nonneg (show 0 ≤ X^(1/10000:ℝ)*X^z by positivity) hp.le]

private theorem second_budget {S X m u b h C a : ℝ} {N : ℕ}
    (hN : 0 < N) (hM : N ≤ X^m) (hm : m ≤ 1) (hx : 1 ≤ X)
    (h₁ : 1 ≤ h) (hb : 1/10000 ≤ b) (hb' : b ≤ 100)
    (hc : 1 ≤ C) (hc' : C ≤ 4000)
    (e₁ : 2*m+u ≤ 2*a-1/10000) (e₂ : m ≤ 2*a-1/10000) (e₃ : -u ≤ 2*a-1/10000)
    (est : S^2 ≤ 32*(1+Real.pi*C)*(1+C)*(1+Real.log N)*((N:ℝ)^2*(b*h*X^u)+N+1/(b*h*X^u))) :
    S ≤ 10^10 * X^a * h^(1/2:ℝ) := by
  have t := est.trans (scale_energy hN hM hm hx h₁ hb hb' hc hc' e₁ e₂ e₃)
  have xp : 0 < X := by linarith
  apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (by positivity)
  apply t.trans
  rw [mul_pow, mul_pow, ← Real.rpow_natCast (h^(1/2:ℝ)), ← Real.rpow_mul (by linarith : 0 ≤ h),
    ← Real.rpow_natCast (X^a), ← Real.rpow_mul xp.le]
  norm_num
  rw [mul_comm 2 a]
  nlinarith [show 0 ≤ h*X^(a*2) by positivity]

private theorem third_budget {S X m u h b : ℝ} {N R : ℕ}
    (hN : 0 < N) (hM : N ≤ X^m) (hm : m ≤ 26/100) (hx : 1 ≤ X)
    (h₁ : 1 ≤ h) (hb : 1/10000 ≤ b) (hb' : b ≤ 100)
    (hR : R ≤ X^(6/100:ℝ)) (hR' : X^(6/100:ℝ)/2 ≤ R)
    (e₁ : 2*m+6/100+u ≤ 34/100) (e₂ : -u ≤ 34/100)
    (est : S^2 ≤ 2*(N:ℝ)^2/R + 4*N*Real.sqrt
      (32*(1+Real.pi*3125)*(1+3125)*(1+Real.log N)*((N:ℝ)^2*R*(b*h*X^u)+N+1/(b*h*X^u)))) :
    S ≤ 10^10*X^(23/100:ℝ)*h^(1/2:ℝ) := by
  have xp : 0 < X := by linarith
  have hp : 0 < h := by linarith
  have bp : 0 < b := by linarith
  have kpow := Real.rpow_pos_of_pos xp (6/100)
  have rp : 0 < (R:ℝ) := by linarith
  have en := scale_energy (u := 6/100+u) (v := u) (z := 34/100) hN hM (by linarith) hx
    h₁ hb hb' (C := 3125) (by norm_num) (by norm_num) (by linarith) (by linarith) e₂
  have d : Real.sqrt (32*(1+Real.pi*3125)*(1+3125)*(1+Real.log N)*
      ((N:ℝ)^2*R*(b*h*X^u)+N+1/(b*h*X^u))) ≤ 10^10*h*X^(18/100:ℝ) := by
    apply Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    calc
      _ ≤ 32*(1+Real.pi*3125)*(1+3125)*(1+Real.log N)*
          ((N:ℝ)^2*(b*h*X^(6/100+u))+N+1/(b*h*X^u)) := by
        have ln := Real.log_nonneg (by exact_mod_cast hN : 1 ≤ (N:ℝ))
        rw [Real.rpow_add xp]
        gcongr 3
        nlinarith [mul_le_mul_of_nonneg_right hR (show 0 ≤ (N:ℝ)^2*(b*h*X^u) by positivity)]
      _ ≤ _ := en
      _ ≤ _ := by
        rw [mul_pow, mul_pow, ← Real.rpow_natCast (X^(18/100:ℝ)), ← Real.rpow_mul xp.le]
        norm_num
        apply mul_le_mul _ (Real.rpow_le_rpow_of_exponent_le hx (by norm_num)) <;> try positivity
        nlinarith [mul_nonneg hp.le (sub_nonneg.mpr h₁)]
  have first : 2*(N:ℝ)^2/R ≤ 4*X^(46/100:ℝ) := by
    rw [div_le_iff₀ rp]
    calc
      _ ≤ 2*(X^m)^2 := by gcongr
      _ ≤ 2*X^(52/100:ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul xp.le]
        gcongr; norm_num; linarith
      _ = 4*X^(46/100:ℝ)*(X^(6/100:ℝ)/2) := by
        rw [show (52/100:ℝ) = 46/100+6/100 by norm_num, Real.rpow_add xp]; ring
      _ ≤ _ := by gcongr
  have other : 4*(N:ℝ)*(10^10*h*X^(18/100:ℝ)) ≤ 4*10^10*h*X^(46/100:ℝ) := calc
    _ ≤ 4*(X^m)*(10^10*h*X^(18/100:ℝ)) := by gcongr
    _ = 4*10^10*h*X^(m+18/100) := by rw [Real.rpow_add xp]; ring
    _ ≤ _ := by gcongr; linarith
  apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (by positivity)
  apply est.trans
  calc
    _ ≤ 4*X^(46/100:ℝ) + 4*(N:ℝ)*(10^10*h*X^(18/100:ℝ)) := by gcongr
    _ ≤ (4+4*10^10)*h*X^(46/100:ℝ) := by
      nlinarith [le_mul_of_one_le_left (by positivity : 0 ≤ X^(46/100:ℝ)) h₁]
    _ ≤ _ := by
      rw [mul_pow,mul_pow, ← Real.rpow_natCast (h^(1/2:ℝ)), ← Real.rpow_mul hp.le,
        ← Real.rpow_natCast (X^(23/100:ℝ)), ← Real.rpow_mul xp.le]
      norm_num
      nlinarith [show 0 ≤ h*X^(23/50:ℝ) by positivity]


private theorem abs_frequency (j : ℤ) (x : ℕ → ℝ) (N : ℕ) :
    ‖∑ n ∈ range N, wave (j*x n)‖ = ‖∑ n ∈ range N, wave (|(j:ℝ)| *x n)‖ := by
  rcases le_total 0 (j:ℝ) with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, ← Complex.norm_conj (∑ n ∈ range N, wave ((j:ℝ)*x n))]
    simp only [map_sum, wave_conj, neg_mul]

private theorem power_freq (X m p t : ℝ) (N : ℕ) (hx : 1 ≤ X) (hm : 0 ≤ m) (hm' : m ≤ 1)
    (hn : 0 < N) (hN : N ≤ X^m) (hp : p < 0)
    (hb : 1/10000 ≤ p*(p-1)*(4:ℝ)^(p-2)) (hb' : p*(p-1)*(4:ℝ)^(p-2) ≤ 100) (hc : (4:ℝ)^(2-p) ≤ 4000) (a : ℝ)
    (e₁ : 2*m+(t+m*(p-2)) ≤ 2*a-1/10000) (e₂ : m ≤ 2*a-1/10000)
    (e₃ : -(t+m*(p-2)) ≤ 2*a-1/10000)
    (j : ℤ) (hj : j ≠ 0) :
    ‖∑ n ∈ range N, wave (j*powerPhase (X^t) p (X^m) n)‖ ≤
      10^10*X^a*|(j:ℝ)|^(1/2:ℝ) := by
  rw [abs_frequency]
  let h : ℝ := |(j:ℝ)|
  have h₁ : 1 ≤ h := by dsimp [h]; exact_mod_cast Int.one_le_abs hj
  have xp : 0 < X := by linarith
  let y := powerPhase (h*X^t) p (X^m)
  have hid (n : ℕ) : |(j:ℝ)| *powerPhase (X^t) p (X^m) n = y n := by dsimp [powerPhase,y,h]; ring
  simp_rw [hid]
  have props := second_power_phase (h*X^t) p (X^m) N (by positivity) hp (Real.one_le_rpow hx hm) hN
  obtain ⟨⟨hq,hC⟩,hbnd,hmono⟩ := props
  have est := sqrt_curvature_bound y N _ _ hn hq hC hbnd (hmono.antitoneOn _)
  have eq : h*X^t*(p*(p-1))*(4*X^m)^(p-2) = (p*(p-1)*(4:ℝ)^(p-2))*h*X^(t+m*(p-2)) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), Real.rpow_add xp, Real.rpow_mul xp.le]
    ring
  rw [eq] at est
  exact second_budget hn hN hm' hx h₁ hb hb' hC hc e₁ e₂ e₃ est

private theorem middle_freq (X m : ℝ) (N : ℕ) (hx : 1 ≤ X) (hm : 24/100 ≤ m) (hm' : m ≤ 26/100)
    (hn : 0 < N) (hN : N ≤ X^m) (j : ℤ) (hj : j ≠ 0) :
    ‖∑ n ∈ range N, wave (j*powerPhase X (-2) (X^m) n)‖ ≤ 10^10*X^(23/100:ℝ)*|(j:ℝ)|^(1/2:ℝ) := by
  rw [abs_frequency]
  let h : ℝ := |(j:ℝ)|
  have h₁ : 1 ≤ h := by dsimp [h]; exact_mod_cast Int.one_le_abs hj
  have xp : 0 < X := by linarith
  let y := powerPhase (h*X) (-2) (X^m)
  have hid (n : ℕ) : |(j:ℝ)| *powerPhase X (-2) (X^m) n = y n := by dsimp [powerPhase,y,h]; ring
  simp_rw [hid]
  let R := ⌊X^(6/100:ℝ)⌋₊
  have x1 := Real.one_le_rpow hx (by norm_num : 0 ≤ (6:ℝ)/100)
  have r1 : 1 ≤ R := Nat.le_floor (by simpa using x1)
  have rX : (R:ℝ) ≤ X^(6/100:ℝ) := Nat.floor_le (by positivity)
  by_cases hrN : R ≤ N
  · obtain ⟨hbnd,hmon⟩ := third_reciprocal_square (h*X) (X^m) N (by positivity)
      (Real.one_le_rpow hx (by linarith)) hN
    have hmup : 0 < 24*(h*X)/(5*X^m)^5 := by positivity
    have est := third_difference y N R _ 3125 hn r1 hrN hmup (by norm_num) hbnd (hmon.antitoneOn _)
    have eq : 24*(h*X)/(5*X^m)^5 = (24/3125)*h*X^(1-5*m) := by
      rw [Real.rpow_sub xp, Real.rpow_one, mul_comm (5:ℝ) m, Real.rpow_mul xp.le]
      norm_num
      ring
    rw [eq] at est
    exact third_budget hn hN hm' hx h₁ (by norm_num) (by norm_num) rX (Nat.div_two_lt_floor x1).le
      (by linarith) (by linarith) est
  · calc
      _ ≤ (N:ℝ) := trivial_sum y N
      _ ≤ X^(6/100:ℝ) := (Nat.cast_le.mpr (by omega : N ≤ R)).trans rX
      _ ≤ 10^10*X^(23/100:ℝ)*h^(1/2:ℝ) := by
        have b := Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (6:ℝ)/100 ≤ 23/100)
        have c := Real.one_le_rpow h₁ (by norm_num : 0 ≤ (1:ℝ)/2)
        nlinarith [le_mul_of_one_le_right (by positivity : 0 ≤ X^(23/100:ℝ)) c,
          show 0 ≤ X^(23/100:ℝ) by positivity]

private theorem saw_trivial (x : ℕ → ℝ) (N : ℕ) : |∑ n ∈ range N, saw (x n)| ≤ N := by
  calc
    _ ≤ ∑ n ∈ range N, |saw (x n)| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ _n ∈ range N, (1:ℝ) := sum_le_sum fun n _ => by
      rw [abs_le]; dsimp [saw]; constructor <;> linarith [Int.fract_lt_one (x n), Int.fract_nonneg (x n)]
    _ = _ := by simp

private noncomputable def blockK : ℝ := 1 + |fourierCost| *10^10

private theorem from_frequency {X m v a : ℝ} {x : ℕ → ℝ} {N : ℕ}
    (hx : 1 ≤ X) (hN : N ≤ X^m) (hv : v ≤ 0)
    (em : m+v ≤ 248/1000) (ea : a+v*(-(51/100)) ≤ 248/1000)
    (h : ∀ j : ℤ, j ≠ 0 → ‖∑ n ∈ range N, wave (j*x n)‖ ≤ 10^10*X^a*|(j:ℝ)|^(1/2:ℝ)) :
    |∑ n ∈ range N, saw (x n)| ≤ blockK*X^(248/1000:ℝ) := by
  have xp : 0 < X := by linarith
  have est := smooth_bound x N (X^v) (10^10*X^a) (by positivity)
    (Real.rpow_le_one_of_one_le_of_nonpos hx hv) (by positivity) h
  apply est.trans
  have h₁ : (N:ℝ)*X^v ≤ X^(248/1000:ℝ) := calc
    _ ≤ X^m*X^v := by gcongr
    _ = _ := (Real.rpow_add xp ..).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx em
  have h₂ : X^a*(X^v)^(-(51/100):ℝ) ≤ X^(248/1000:ℝ) := by
    rw [← Real.rpow_mul xp.le, ← Real.rpow_add xp]
    exact Real.rpow_le_rpow_of_exponent_le hx ea
  have c := le_abs_self fourierCost
  dsimp [blockK]
  have prod := mul_le_mul c h₂ (by positivity) (abs_nonneg _)
  nlinarith [show 0 ≤ X^(248/1000:ℝ) by positivity,
    show 0 ≤ |fourierCost| * X^(248/1000:ℝ) by positivity]

theorem phase_block (X m : ℝ) (N : ℕ) (hx : 1 ≤ X) (hm : 0 ≤ m) (hm' : m ≤ 1/3)
    (hN : N ≤ X^m) (t p : ℝ) (phase : (t = 1 ∧ p = -2) ∨ (t = 1/2 ∧ p = -(1/2))) :
    |∑ n ∈ range N, saw (powerPhase (X^t) p (X^m) n)| ≤ blockK*X^(248/1000:ℝ) := by
  have pos : 0 ≤ blockK := by dsimp [blockK]; positivity
  rcases Nat.eq_zero_or_pos N with rfl | hn
  · simp; positivity
  by_cases small : m ≤ 248/1000
  · exact (saw_trivial _ _).trans (hN.trans ((Real.rpow_le_rpow_of_exponent_le hx small).trans
      (le_mul_of_one_le_left (by positivity) (by dsimp [blockK]; linarith [abs_nonneg fourierCost]))))
  let a := 248/1000 + (248/1000-m)*(51/100)
  have applySecond : (∀ j : ℤ, j ≠ 0 → ‖∑ n ∈ range N, wave (j*powerPhase (X^t) p (X^m) n)‖ ≤
      10^10*X^a*|(j:ℝ)|^(1/2:ℝ)) → _ := from_frequency hx hN (v := 248/1000-m)
        (by linarith) (by linarith) (by dsimp [a]; linarith)
  rcases phase with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · by_cases big : 26/100 ≤ m
    · apply applySecond
      intro j hj
      apply power_freq X m (-2) 1 N hx hm (by linarith) hn hN (by norm_num)
      all_goals first | exact hj | (norm_num [a] <;> linarith)
    · simp only [Real.rpow_one]
      apply from_frequency hx hN (v := -(3/100)) (a := 23/100) (by norm_num) (by linarith) (by norm_num)
      exact middle_freq X m N hx (by linarith) (by linarith) hn hN
  · apply applySecond
    intro j hj
    apply power_freq X m (-(1/2)) (1/2) N hx hm (by linarith) hn hN (by norm_num)
    all_goals first | exact hj | (norm_num [a] <;> linarith)

theorem phase_sum (X : ℝ) (L : ℕ) (hx : 1 < X) (hl : 1 ≤ L) (hL : L ≤ X^(1/3:ℝ))
    (t p : ℝ) (phase : (t = 1 ∧ p = -2) ∨ (t = 1/2 ∧ p = -(1/2))) :
    |∑ n ∈ Icc 1 L, saw (X^t*(n:ℝ)^p)| ≤ 2001*blockK*X^(249/1000:ℝ) := by
  let K := Nat.log 2 L
  let cut (k : ℕ) := min (2^k) (L+1)
  let f (n : ℕ) := saw (X^t*(n:ℝ)^p)
  have xp : 0 < X := by linarith
  have bk : 0 ≤ blockK := by dsimp [blockK]; positivity
  have cut1 (i : ℕ) : 1 ≤ cut i := le_min (Nat.one_le_pow _ _ (by decide)) (by omega)
  have pp : 2^K ≤ L := Nat.pow_log_le_self _ (by omega)
  have block (k : ℕ) (hk : k ≤ K) :
      |∑ n ∈ Ico (cut k) (cut (k+1)), f n| ≤ blockK*X^(248/1000:ℝ) := by
    let M : ℕ := 2^k
    let B := cut (k+1)
    have mm : 1 ≤ M := Nat.one_le_pow _ _ (by decide)
    have ml : M ≤ L := (Nat.pow_le_pow_right (by decide) hk).trans pp
    have cm : cut k = M := min_eq_left (by dsimp [M] at ml; omega)
    have bc : M ≤ B := le_min (by dsimp [M]; rw [pow_succ]; omega) (by omega)
    have bm : B ≤ M+M := by dsimp [B,cut,M]; rw [pow_succ, ← Nat.mul_two]; exact min_le_left ..
    let m := Real.logb X M
    have xM : X^m = M := Real.rpow_logb xp hx.ne' (by positivity)
    have hm := Real.logb_nonneg hx (show 1 ≤ (M:ℝ) by exact_mod_cast mm)
    have hm' : m ≤ 1/3 := (Real.logb_le_iff_le_rpow hx (by positivity)).mpr ((Nat.cast_le.mpr ml).trans hL)
    have hN : ((B-M:ℕ):ℝ) ≤ X^m := by rw [xM]; exact_mod_cast (by omega : B-M ≤ M)
    have res := phase_block X m (B-M) hx.le hm hm' hN t p phase
    rw [xM] at res
    rw [cm]
    change |∑ n ∈ Ico M B, f n| ≤ _
    rw [show Ico M B = Ico (0+M) (B-M+M) by rw [zero_add,Nat.sub_add_cancel bc],
      ← sum_Ico_add', Nat.Ico_zero_eq_range]
    simpa only [f, powerPhase,Nat.cast_add,add_comm (M:ℝ)] using res
  have parts (i : ℕ) (hi : i ≤ K+1) : |∑ n ∈ Ico 1 (cut i), f n| ≤
      i*(blockK*X^(248/1000:ℝ)) := by
    induction i with
    | zero => simp [cut]
    | succ i ih =>
      have mono : cut i ≤ cut (i+1) := min_le_min_right _ (Nat.pow_le_pow_right (by decide) (by omega))
      rw [← sum_Ico_consecutive f (cut1 _) mono]
      exact (abs_add_le ..).trans ((add_le_add (ih (by omega)) (block i (by omega))).trans_eq (by push_cast; ring))
  have final_cut : cut (K+1) = L+1 := min_eq_right (Nat.lt_pow_succ_log_self (by decide : 1 < 2) L)
  have h := parts (K+1) le_rfl
  rw [final_cut, Ico_add_one_right_eq_Icc] at h
  apply h.trans
  have lp : (2:ℝ)^K ≤ X := (show (2:ℝ)^K ≤ L by exact_mod_cast pp).trans
    (hL.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hx.le (by norm_num : (1:ℝ)/3 ≤ 1)))
  have kk := Real.log_le_log (by positivity) lp
  rw [Real.log_pow] at kk
  have lk := Real.log_le_rpow_div xp.le (by norm_num : 0 < (1:ℝ)/1000)
  have kg : (↑(K+1):ℝ) ≤ 2001*X^(1/1000:ℝ) := by
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) K) (show 0 ≤ Real.log 2 - 1/2 by linarith [Real.log_two_gt_d9]),
      Real.one_le_rpow hx.le (by norm_num : 0 ≤ (1:ℝ)/1000)]
  calc
    _ ≤ (2001*X^(1/1000:ℝ))*(blockK*X^(248/1000:ℝ)) := by gcongr
    _ = _ := by rw [show (249/1000:ℝ) = 1/1000+248/1000 by norm_num, Real.rpow_add xp]; ring


private theorem nested_error (F V : ℕ → ℝ) (hV : ∀ n, 0 ≤ V n)
    (step : ∀ n, |F (n+1)-F n| ≤ V n-V (n+1)) :
    ∃ C : ℝ, ∀ n, |F n-C| ≤ V n := by
  let lower n := F n-V n
  let upper n := F n+V n
  have lo : Monotone lower := monotone_nat_of_le_succ fun n => by
    dsimp [lower]; linarith [(abs_le.mp (step n)).1]
  have hi : Antitone upper := antitone_nat_of_succ_le fun n => by
    dsimp [upper]; linarith [(abs_le.mp (step n)).2]
  have sep (m n : ℕ) : lower m ≤ upper n := by
    calc
      _ ≤ lower (max m n) := lo (le_max_left ..)
      _ ≤ upper (max m n) := by dsimp [lower,upper]; linarith [hV (max m n)]
      _ ≤ _ := hi (le_max_right ..)
  have bd : BddAbove (Set.range lower) := ⟨upper 0, by rintro y ⟨m,rfl⟩; exact sep m 0⟩
  refine ⟨sSup (Set.range lower), fun n => abs_le.mpr ⟨?_,?_⟩⟩
  · have h : sSup (Set.range lower) ≤ upper n := csSup_le (Set.range_nonempty _) (by
      rintro y ⟨m,rfl⟩; exact sep m n)
    dsimp [upper] at h; linarith
  · have h := le_csSup bd (Set.mem_range_self n)
    dsimp [lower] at h; linarith

private theorem midpoint_square (a : ℝ) (ha : 0 < a) :
    |1/(a+1/2)^2 + 1/(a+1) - 1/a| ≤ 1/a^3 - 1/(a+1)^3 := by
  have eq : 1/(a+1/2)^2 + 1/(a+1) - 1/a = - (1/(4*a*(a+1)*(a+1/2)^2)) := by
    field_simp; ring
  rw [eq, abs_neg, abs_of_pos (by positivity)]
  field_simp
  ring_nf
  nlinarith [pow_nonneg ha.le 2, pow_nonneg ha.le 3, pow_nonneg ha.le 4]

private theorem midpoint_root (a : ℝ) (ha : 1/2 ≤ a) :
    |1/Real.sqrt (a+1/2) - 2*(Real.sqrt (a+1)-Real.sqrt a)| ≤
      8/(Real.sqrt a)^3 - 8/(Real.sqrt (a+1))^3 := by
  let u := Real.sqrt a
  let v := Real.sqrt (a+1)
  let w := Real.sqrt (a+1/2)
  have up : 0 < u := Real.sqrt_pos.mpr (by linarith)
  have vp : 0 < v := Real.sqrt_pos.mpr (by linarith)
  have wp : 0 < w := Real.sqrt_pos.mpr (by linarith)
  have u2 : u^2 = a := Real.sq_sqrt (by linarith)
  have v2 : v^2 = a+1 := Real.sq_sqrt (by linarith)
  have w2 : w^2 = a+1/2 := Real.sq_sqrt (by linarith)
  have uv : u ≤ v := Real.sqrt_le_sqrt (by linarith)
  have uw : u ≤ w := Real.sqrt_le_sqrt (by linarith)
  have vu : v ≤ 2*u := by nlinarith [sq_nonneg (v-2*u)]
  have rel : (v-u)*(v+u) = 1 := by nlinarith
  have gap : v-u = 1/(v+u) := (eq_div_iff (by positivity)).mpr rel
  have dbl : (2*w-v-u)*(2*w+v+u) = (v-u)^2 := by nlinarith
  have form : 2*(v-u)-1/w = (v-u)^2/(w*(v+u)*(2*w+v+u)) := by
    rw [← dbl]
    conv_lhs => rw [gap]
    field_simp
    ring
  change |1/w-2*(v-u)| ≤ 8/u^3 - 8/v^3
  rw [abs_sub_comm,form,abs_of_nonneg (by positivity)]
  have gi : v-u ≤ 1/u := by rw [gap]; gcongr; linarith
  calc
    _ ≤ (v-u)^2/(u*u*u) := by
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      apply mul_le_mul (mul_le_mul uw (by linarith) up.le wp.le) (by linarith) (by positivity) (by positivity)
    _ ≤ (v-u)/u^4 := by
      rw [sq, div_eq_mul_inv]
      calc
        _ ≤ ((v-u)*(1/u))*(u*u*u)⁻¹ := by gcongr
        _ = _ := by ring
    _ ≤ 8/u^3-8/v^3 := by
      have nv : v^3 ≤ 8*u^3 := calc
        _ ≤ (2*u)^3 := pow_le_pow_left₀ vp.le vu 3
        _ = _ := by ring
      have rhs : 8/u^3-8/v^3 = (v-u)*(8*(v^2+v*u+u^2))/(u^3*v^3) := by field_simp; ring
      rw [rhs]
      have vnn : 0 ≤ u*v := by positivity
      have num : v^3 ≤ 8*u*(v^2+v*u+u^2) := by
        nlinarith [mul_nonneg up.le (sq_nonneg v), mul_nonneg (sq_nonneg u) vp.le]
      have inv : 1/u^4 ≤ 8*(v^2+v*u+u^2)/(u^3*v^3) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left num (pow_nonneg up.le 3)]
      calc
        _ = (v-u)*(1/u^4) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left inv (sub_nonneg.mpr uv)
        _ = _ := by ring

noncomputable def U (L : ℕ) : ℝ := L+1/2

private theorem sum_next (f : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Icc 1 (n+1), f k) = (∑ k ∈ Icc 1 n, f k)+f (n+1) := by
  rw [← Ico_add_one_right_eq_Icc, ← Ico_add_one_right_eq_Icc, Finset.sum_Ico_succ_top (by omega)]

/-- Centering the integration cells at integers leaves summable errors in both power sums. -/
theorem main_expansions :
    (∃ A : ℝ, ∀ L : ℕ, |(∑ k ∈ Icc 1 L, (1:ℝ)/(k:ℝ)^2) + 1/U L - A| ≤ 1/(U L)^3) ∧
    (∃ B : ℝ, ∀ L : ℕ, |(∑ k ∈ Icc 1 L, 1/Real.sqrt k) - 2*Real.sqrt (U L) - B| ≤
      8/(Real.sqrt (U L))^3) := by
  have up (n : ℕ) : 0 < U n := by dsimp [U]; positivity
  have un (n : ℕ) : U (n+1) = U n+1 := by simp [U]; ring
  have mid (n : ℕ) : (↑(n+1):ℝ) = U n+1/2 := by simp [U]; ring
  constructor
  · apply nested_error (fun n => (∑ k ∈ Icc 1 n, (1:ℝ)/(k:ℝ)^2)+1/U n) (fun n => 1/(U n)^3) (fun n => by dsimp [U]; positivity)
    intro n
    simp only [sum_next _ n, un, mid]
    convert midpoint_square (U n) (up n) using 2; ring
  · apply nested_error (fun n => (∑ k ∈ Icc 1 n, 1/Real.sqrt k)-2*Real.sqrt (U n)) (fun n => 8/(Real.sqrt (U n))^3) (fun n => by positivity)
    intro n
    simp only [sum_next _ n, un, mid]
    convert midpoint_root (U n) (by dsimp [U]; linarith [Nat.cast_nonneg (α := ℝ) n]) using 2; ring

private theorem boundary (X : ℝ) (L : ℕ) (hL : 1 ≤ L) (hlo : (L:ℝ)^3 ≤ X)
    (hhi : X ≤ ((L:ℝ)+1)^3) :
    X/(U L)^3 ≤ 8 ∧ Real.sqrt X * (8/(Real.sqrt (U L))^3) ≤ 24 ∧
      |-(X/U L) + 2*Real.sqrt X*Real.sqrt (U L) - L - (L:ℝ)^2| ≤ 10 := by
  let u := U L
  let s := Real.sqrt u
  let t := Real.sqrt X
  have l1 : 1 ≤ (L:ℝ) := by exact_mod_cast hL
  have u1 : 1 ≤ u := by dsimp [u,U]; linarith
  have up : 0 < u := by linarith
  have sp : 0 < s := Real.sqrt_pos.mpr up
  have xp : 0 ≤ X := (pow_nonneg (by positivity) 3).trans hlo
  have tp : 0 ≤ t := Real.sqrt_nonneg _
  have ss : s^2 = u := Real.sq_sqrt up.le
  have tt : t^2 = X := Real.sq_sqrt xp
  have xm : X ≤ 8*u^3 := calc
    _ ≤ ((L:ℝ)+1)^3 := hhi
    _ ≤ (2*u)^3 := by gcongr; dsimp [u,U]; linarith
    _ = _ := by ring
  have tsmall : t ≤ 3*s^3 := by
    apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (by positivity)
    rw [tt, mul_pow, show (s^3)^2 = (s^2)^3 by ring, ss]
    linarith [pow_nonneg up.le 3]
  refine ⟨(div_le_iff₀ (by positivity : 0 < u^3)).mpr xm, ?_, ?_⟩
  · change t*(8/s^3) ≤ 24
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]; linarith
  let z := t/s
  have zp : 0 ≤ z := div_nonneg tp sp.le
  have zz : z^2*u = X := by dsimp [z]; rw [div_pow, ss, div_mul_cancel₀ _ up.ne', tt]
  have ud : u = L+1/2 := rfl
  have diff : |X-u^3| ≤ 3*u^2 := by
    rw [ud,abs_le]
    constructor <;> nlinarith [sq_nonneg (L:ℝ), l1]
  have w : |z-u| ≤ 3 := by
    have id : |X-u^3| = |z-u| *((z+u)*u) := by
      rw [← zz, show z^2*u-u^3 = (z-u)*((z+u)*u) by ring, abs_mul, abs_of_pos (mul_pos (add_pos_of_nonneg_of_pos zp up) up)]
    rw [id] at diff
    apply le_of_mul_le_mul_right (a := u^2) _ (sq_pos_of_pos up)
    calc
      _ ≤ |z-u| *((z+u)*u) := by gcongr; nlinarith [mul_nonneg zp up.le]
      _ ≤ _ := diff
  have id : -(X/u) + 2*t*s - L - (L:ℝ)^2 = 1/4 - (z-u)^2 := by
    rw [← zz, mul_div_cancel_right₀ _ up.ne']
    have prod : z*u = t*s := by dsimp [z]; rw [← ss]; field_simp
    nlinarith [prod, show u^2 = (L:ℝ)^2+L+1/4 by rw [ud]; ring]
  change |-(X/u) + 2*t*s - L - (L:ℝ)^2| ≤ 10
  rw [id,abs_le]
  have wb : (z-u)^2 ≤ 9 := by have hh := pow_le_pow_left₀ (abs_nonneg _) w 2; simpa only [sq_abs, show (3:ℝ)^2=9 by norm_num] using hh
  constructor <;> nlinarith [sq_nonneg (z-u)]


noncomputable def count (n : ℕ) : ℝ := ((∑ k ∈ Icc 1 n, n/k^2 : ℕ):ℝ)

private theorem floor_decomp {x : ℝ} (hx : 0 ≤ x) :
    (⌊x⌋₊:ℝ) = x-1/2-saw x := by
  have he : ((⌊x⌋₊:ℕ):ℝ) = (⌊x⌋:ℤ) := by exact_mod_cast Int.natCast_floor_eq_floor hx
  rw [he]; unfold saw Int.fract; ring

private theorem row_real (n k : ℕ) : (↑(n/k^2):ℝ) =
    n*(1/(k:ℝ)^2)-1/2-saw ((n:ℝ)^((1:ℝ))*(k:ℝ)^(-2:ℝ)) := by
  have h := floor_decomp (x := (n:ℝ)/((k^2:ℕ):ℝ)) (by positivity)
  rw [Nat.floor_div_eq_div] at h
  simpa [div_eq_mul_inv] using h

private theorem col_real (n k : ℕ) (hk : 0 < k) : (↑(n/k).sqrt:ℝ) =
    Real.sqrt n*(1/Real.sqrt k)-1/2-saw ((n:ℝ)^(1/2:ℝ)*(k:ℝ)^(-(1/2):ℝ)) := by
  have kp : 0 < (k:ℝ) := by exact_mod_cast hk
  have he : ⌊Real.sqrt ((n:ℝ)/k)⌋₊ = (n/k).sqrt := by
    have eq (j : ℕ) : j ≤ ⌊Real.sqrt ((n:ℝ)/k)⌋₊ ↔ j ≤ (n/k).sqrt := by
      rw [Nat.le_floor_iff (Real.sqrt_nonneg _), Real.le_sqrt (by positivity) (by positivity),
        le_div_iff₀ kp, Nat.le_sqrt', Nat.le_div_iff_mul_le hk]
      norm_cast
    exact le_antisymm ((eq _).mp le_rfl) ((eq _).mpr le_rfl)
  have h := floor_decomp (x := Real.sqrt ((n:ℝ)/k)) (Real.sqrt_nonneg _)
  rw [he,Real.sqrt_div (by positivity)] at h
  rw [Real.rpow_neg kp.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  simpa [div_eq_mul_inv] using h

private theorem expanded_count (n L : ℕ) (hl : L ≤ n) (hlo : L^3 ≤ n) (hhi : n < (L+1)^3) :
    count n = n*(∑ k ∈ Icc 1 L, 1/(k:ℝ)^2) + Real.sqrt n*(∑ k ∈ Icc 1 L, 1/Real.sqrt k)
      - L - (L:ℝ)^2 - (∑ k ∈ Icc 1 L, saw ((n:ℝ)^(1:ℝ)*(k:ℝ)^(-2:ℝ)))
      - (∑ k ∈ Icc 1 L, saw ((n:ℝ)^(1/2:ℝ)*(k:ℝ)^(-(1/2):ℝ))) := by
  have hh := congrArg (Nat.cast : ℕ → ℝ) (hyperbola n L hl hlo hhi)
  unfold count
  push_cast at hh ⊢
  have hs := sum_congr (s₁ := Icc 1 L) rfl (fun k _ => row_real n k)
  have ht := sum_congr (s₁ := Icc 1 L) rfl (fun k hk => col_real n k (mem_Icc.mp hk).1)
  rw [hs,ht] at hh
  simp only [sum_sub_distrib, ← mul_sum, sum_const, Nat.card_Icc, Nat.add_sub_cancel,
    nsmul_eq_mul] at hh
  linarith

noncomputable def err (A B : ℝ) (n : ℕ) := count n - A*n - B*Real.sqrt n

theorem better_expansion : ∃ A B : ℝ, err A B =O[atTop] fun n : ℕ => (n:ℝ)^(249/1000:ℝ) := by
  obtain ⟨⟨A,hA⟩,⟨B,hB⟩⟩ := main_expansions
  refine ⟨A,B, isBigO_iff.mpr ⟨42+4002*blockK, ?_⟩⟩
  filter_upwards [eventually_ge_atTop 2] with n hn
  let X : ℝ := n
  have xp : 1 < X := by dsimp [X]; exact_mod_cast (by omega : 1 < n)
  let L := ⌊X^(1/3:ℝ)⌋₊
  have l1 : 1 ≤ L := Nat.le_floor (by simpa using Real.one_le_rpow xp.le (by norm_num : 0 ≤ (1:ℝ)/3))
  have lc : (L:ℝ) ≤ X^(1/3:ℝ) := Nat.floor_le (by positivity)
  have powid : (X^(1/3:ℝ))^3 = X := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ X)]; norm_num
  have lo : (L:ℝ)^3 ≤ X := powid ▸ pow_le_pow_left₀ (by positivity) lc 3
  have hi : X < ((L:ℝ)+1)^3 := by rw [← powid]; exact pow_lt_pow_left₀ (Nat.lt_floor_add_one _) (by positivity) (by decide)
  have ln' : (L:ℝ) ≤ X := lc.trans (by simpa using Real.rpow_le_rpow_of_exponent_le xp.le (by norm_num : (1:ℝ)/3 ≤ 1))
  have ln : L ≤ n := (Nat.cast_le (α := ℝ)).mp ln'
  have eq := expanded_count n L ln (by dsimp [X] at lo; exact_mod_cast lo)
    (by dsimp [X] at hi; exact_mod_cast hi)
  obtain ⟨b1,b2,b3⟩ := boundary X L l1 lo hi.le
  let V := X^(249/1000:ℝ)
  have v1 : 1 ≤ V := Real.one_le_rpow xp.le (by norm_num)
  have f := phase_sum X L xp l1 lc 1 (-2) (Or.inl ⟨rfl,rfl⟩)
  have g := phase_sum X L xp l1 lc (1/2) (-(1/2)) (Or.inr ⟨rfl,rfl⟩)
  let S := ∑ k ∈ Icc 1 L, (1:ℝ)/(k:ℝ)^2
  let T := ∑ k ∈ Icc 1 L, 1/Real.sqrt k
  let F := ∑ k ∈ Icc 1 L, saw (X^(1:ℝ)*(k:ℝ)^(-2:ℝ))
  let G := ∑ k ∈ Icc 1 L, saw (X^(1/2:ℝ)*(k:ℝ)^(-(1/2):ℝ))
  have e1 : |X*(S+1/U L-A)| ≤ 8 := by
    rw [abs_mul,abs_of_pos (by linarith : 0 < X)]
    exact (mul_le_mul_of_nonneg_left (hA L) (by positivity)).trans (by simpa [div_eq_mul_inv] using b1)
  have e2 : |Real.sqrt X*(T-2*Real.sqrt (U L)-B)| ≤ 24 := by
    rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (hB L) (Real.sqrt_nonneg _)).trans b2
  change count n = X*S+Real.sqrt X*T-L-(L:ℝ)^2-F-G at eq
  change |F| ≤ 2001*blockK*V at f
  change |G| ≤ 2001*blockK*V at g
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  change |count n-A*X-B*Real.sqrt X| ≤ (42+4002*blockK)*V
  rw [abs_le]
  obtain ⟨f₁,f₂⟩ := abs_le.mp f
  obtain ⟨g₁,g₂⟩ := abs_le.mp g
  obtain ⟨a₁,a₂⟩ := abs_le.mp e1
  obtain ⟨b₁,b₂⟩ := abs_le.mp e2
  obtain ⟨c₁,c₂⟩ := abs_le.mp b3
  simp only [div_eq_mul_inv, one_mul] at a₁ a₂ c₁ c₂
  constructor <;> linarith only [eq,v1,f₁,f₂,g₁,g₂,a₁,a₂,b₁,b₂,c₁,c₂]

private noncomputable def scale (u : ℝ) (n : ℕ) := (n:ℝ)^u

private theorem power_little {u v : ℝ} (hu : u < v) : scale u =o[atTop] scale v := by
  apply isLittleO_of_tendsto'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hp : 0 < (n:ℝ) := by exact_mod_cast hn
    exact fun he => False.elim ((Real.rpow_pos_of_pos hp v).ne' he)
  · have t := (tendsto_rpow_neg_atTop (sub_pos.mpr hu)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
    apply t.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hp : 0 < (n:ℝ) := by exact_mod_cast hn
    simp [scale, neg_sub, Real.rpow_sub hp]

private theorem coeff_zero {u c : ℝ} (h : (fun n => c*scale u n) =o[atTop] scale u) : c = 0 := by
  by_contra hn
  apply isLittleO_irrefl _ ((isLittleO_const_mul_left_iff hn).mp h)
  apply Filter.Eventually.frequently
  filter_upwards [eventually_ge_atTop 1] with n hn'
  exact (Real.rpow_pos_of_pos (by exact_mod_cast hn' : 0 < (n:ℝ)) u).ne'

theorem not_sharp (C D : ℝ) :
    ¬ ((∀ ε : ℝ, 0 < ε → err C D =O[atTop] scale (1/4 + ε)) ∧
        (∀ ε : ℝ, 0 < ε → ¬ err C D =O[atTop] scale (1/4 - ε))) := by
  intro ⟨upper,sharp⟩
  obtain ⟨A,B,h⟩ := better_expansion
  change err A B =O[atTop] scale (249/1000) at h
  have hj := upper (1/8) (by norm_num)
  have diff : (fun n => (A-C)*scale 1 n + (B-D)*scale (1/2) n) =o[atTop] scale (1/2) := by
    apply ((hj.trans_isLittleO (power_little (v := 1/2) (by norm_num))).sub
      (h.trans_isLittleO (power_little (v := 1/2) (by norm_num)))).congr_left
    intro n
    simp only [err, scale, Real.rpow_one, Real.sqrt_eq_rpow]; ring
  have lo := power_little (u := 1/2) (v := 1) (by norm_num)
  have ac : A-C = 0 := by
    apply coeff_zero (u := 1)
    apply ((diff.trans lo).sub (lo.const_mul_left (B-D))).congr_left
    intro n; ring
  have bd : B-D = 0 := by
    apply coeff_zero (u := 1/2)
    simpa [ac] using diff
  rw [sub_eq_zero.mp ac, sub_eq_zero.mp bd] at h
  apply sharp (1/1000) (by norm_num)
  convert h using 1; norm_num

end A013936

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a013936.main) := by
  exact A013936.not_sharp _ _
