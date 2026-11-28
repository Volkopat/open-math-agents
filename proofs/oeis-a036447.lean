import OMAStatements.S_oeis_a036447
import Mathlib.Tactic

open Filter OMA.S_oeis_a036447

namespace DoubleReverseGrowth

def flip (x : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 x).reverse

/-- Reverse the last k decimal places, preserving their width. -/
def rev : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k+1, x => x % 10 * 10^k + rev k (x/10)

lemma rev_lt (k x : ℕ) : rev k x < 10^k := by
  induction k generalizing x with
  | zero => simp [rev]
  | succ k ih =>
    have hh := ih (x/10)
    have h := Nat.mod_lt x (by decide : 0 < 10)
    have hm := Nat.mul_le_mul_right (10^k) (show x%10 ≤ 9 by omega)
    simp only [rev, pow_succ]
    omega

lemma rev_list (l : List ℕ) (h : ∀ d ∈ l, d < 10) :
    rev l.length (Nat.ofDigits 10 l) = Nat.ofDigits 10 l.reverse := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    have hd := h d (List.mem_cons_self ..)
    have ht := ih (fun t hm => h t (List.mem_cons_of_mem _ hm))
    simp only [List.length_cons, Nat.ofDigits_cons, rev, Nat.ofDigits_reverse_cons]
    rw [show (d + 10 * Nat.ofDigits 10 l) % 10 = d by omega,
      show (d + 10 * Nat.ofDigits 10 l) / 10 = Nat.ofDigits 10 l by omega, ht]
    ring

lemma flip_eq (x : ℕ) : flip x = rev (Nat.digits 10 x).length x := by
  have h := rev_list (Nat.digits 10 x) (fun _ hd => Nat.digits_lt_base (by decide) hd)
  simpa only [Nat.ofDigits_digits, flip] using h.symm

lemma rev_split (k m x : ℕ) :
    rev (k+m) x = rev k (x/10^m) + 10^k * rev m x := by
  induction m generalizing x with
  | zero => simp [rev]
  | succ m ih =>
    change x%10 * 10^(k+m) + rev (k+m) (x/10) =
      rev k (x/10^(m+1)) + 10^k * (x%10 * 10^m + rev m (x/10))
    rw [ih (x/10), Nat.div_div_eq_div_mul, pow_succ' 10 m, pow_add]
    ring

lemma edges (x k : ℕ) (hlo : 10 ≤ x / 10^k) (hhi : x / 10^k < 100) :
    flip x / 10^k = rev 2 x ∧ flip x % 100 = rev 2 (x / 10^k) := by
  have hs : 0 < 10^k := by positivity
  have ha := (Nat.le_div_iff_mul_le hs).mp hlo
  have hb := (Nat.div_lt_iff_lt_mul hs).mp hhi
  have hl : (Nat.digits 10 x).length = k+2 := by
    have low := (Nat.lt_digits_length_iff (b := 10) (k := k+1) (by decide) x).2
      (by rw [pow_succ]; omega)
    have high := (Nat.digits_length_le_iff (b := 10) (k := k+2) (by decide) x).2
      (by rw [pow_add]; norm_num; omega)
    omega
  rw [flip_eq, hl]
  constructor
  · rw [rev_split k 2, Nat.add_mul_div_left _ _ hs, Nat.div_eq_of_lt (rev_lt _ _), zero_add]
  · rw [Nat.add_comm k 2, rev_split 2 k]
    have h := rev_lt 2 (x / 10^k)
    norm_num at h ⊢
    omega

lemma rev_two (x : ℕ) : rev 2 x = x%10*10 + (x/10)%10 := by simp [rev]

lemma twice_prefix (x s : ℕ) (hs : 0 < s) :
    2*(x/s) ≤ 2*x/s ∧ 2*x/s < 2*(x/s)+2 := by
  have h := Nat.mod_add_div x s
  have hm := Nat.mod_lt x hs
  constructor
  · apply (Nat.le_div_iff_mul_le hs).2
    nlinarith only [Nat.div_mul_le_self x s]
  · apply (Nat.div_lt_iff_lt_mul hs).2
    nlinarith

/-- k is the number of places after the first two digits. The high
flag selects a leading 8; the low flag selects a trailing 4. -/
def shape (x k : ℕ) (high low : Bool) : Prop :=
  (if high then 80 ≤ x/10^k ∧ x/10^k < 90 else 20 ≤ x/10^k ∧ x/10^k < 25) ∧
  (if low then x%10 = 4 else x%100 = 61 ∨ x%100 = 71)

lemma advance (x k : ℕ) (high low : Bool) (h : shape x k high low) :
    shape (flip (2*x)) (k+if high then 1 else 0) low (!high) := by
  let j := k+if high then 1 else 0
  let q := 2*x / 10^j
  have twice := twice_prefix x (10^k) (by positivity)
  have hlead : if high then (q=16 ∨ q=17) else (40 ≤ q ∧ q<50) := by
    have hr := h.1
    cases high
    · simp [q, j] at hr ⊢
      omega
    · simp [q, j, pow_succ, ← Nat.div_div_eq_div_mul] at hr ⊢
      omega
  have hlo : 10 ≤ q := by cases high <;> simp_all <;> omega
  have hhi : q < 100 := by cases high <;> simp_all <;> omega
  have ⟨top, bottom⟩ := edges (2*x) j hlo hhi
  rw [rev_two] at top bottom
  change shape (flip (2*x)) j low (!high)
  constructor
  · have hr := h.2
    cases low <;> simp_all [shape] <;> omega
  · change flip (2*x) % 100 = q%10*10 + (q/10)%10 at bottom
    cases high with
    | false =>
      change 40 ≤ q ∧ q < 50 at hlead
      change flip (2*x) % 10 = 4
      have hd : q/10 = 4 := by omega
      rw [← Nat.mod_mod_of_dvd (flip (2*x)) (by decide : 10 ∣ 100), bottom, hd]
      omega
    | true =>
      change q=16 ∨ q=17 at hlead
      change flip (2*x) % 100 = 61 ∨ flip (2*x) % 100 = 71
      rcases hlead with he | he <;> rw [he] at bottom <;> norm_num at bottom <;> omega

lemma next_shape (n k : ℕ) (h l : Bool) (hs : shape (a n) k h l) :
    shape (a (n+1)) (k+if h then 1 else 0) l (!h) := advance _ _ _ _ hs

lemma cycles (j : ℕ) : shape (a (4*j+6)) (2*j+1) false true := by
  induction j with
  | zero => unfold shape; decide
  | succ j ih =>
    have s1 := next_shape _ _ _ _ ih
    have s2 := next_shape _ _ _ _ s1
    have s3 := next_shape _ _ _ _ s2
    have s4 := next_shape _ _ _ _ s3
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false,
      if_true, Nat.add_zero] at s4
    rw [show 4*j.succ+6 = 4*j+6+1+1+1+1 by omega,
      show 2*j.succ+1 = 2*j+3 by omega]
    exact s4

lemma length_bounds {x k : ℕ} {h l : Bool} (hs : shape x k h l) :
    10^(k+1) ≤ x ∧ x < 10^(k+2) := by
  have ht := hs.1
  have low : 10 ≤ x/10^k := by cases h <;> simp_all <;> omega
  have high : x/10^k < 100 := by cases h <;> simp_all <;> omega
  have s : 0 < 10^k := by positivity
  have h1 := (Nat.le_div_iff_mul_le s).mp low
  have h2 := (Nat.div_lt_iff_lt_mul s).mp high
  rw [pow_succ, pow_add]
  norm_num
  omega

lemma square_bounds (n : ℕ) (hn : 6 ≤ n) :
    10^n ≤ 10^6 * (a n)^2 ∧ (a n)^2 ≤ 10^6 * 10^n := by
  obtain ⟨j, hj⟩ : ∃ j, n = 4*j+6 ∨ n = 4*j+7 ∨ n = 4*j+8 ∨ n = 4*j+9 :=
    ⟨(n-6)/4, by omega⟩
  have s0 := cycles j
  have s1 := next_shape _ _ _ _ s0
  have s2 := next_shape _ _ _ _ s1
  have s3 := next_shape _ _ _ _ s2
  have helper : ∀ m k h l, shape (a m) k h l →
      m ≤ (k+1)*2+6 → (k+2)*2 ≤ m+6 →
      10^m ≤ 10^6*(a m)^2 ∧ (a m)^2 ≤ 10^6*10^m := by
    intro m k h l hs hl hu
    have ⟨sl, su⟩ := length_bounds hs
    have h1 := Nat.pow_le_pow_left sl 2
    have h2 := Nat.pow_le_pow_left su.le 2
    have p1 := Nat.pow_le_pow_right (n := 10) (by decide) hl
    have p2 := Nat.pow_le_pow_right (n := 10) (by decide) hu
    rw [← pow_mul] at h1 h2
    rw [pow_add] at p1 p2
    exact ⟨p1.trans (by nlinarith only [h1]), h2.trans (by nlinarith only [p2])⟩
  rcases hj with rfl | rfl | rfl | rfl
  · exact helper _ _ _ _ s0 (by omega) (by omega)
  · exact helper _ _ _ _ s1 (by simp; omega) (by simp; omega)
  · exact helper _ _ _ _ s2 (by simp; omega) (by simp; omega)
  · exact helper _ _ _ _ s3 (by simp; omega) (by simp; omega)

lemma root_limit : Tendsto (fun n : ℕ => (a n : ℝ) ^ (1 / (n : ℝ)))
    atTop (nhds (Real.sqrt 10)) := by
  let c : ℝ := Real.log 10 / 2
  let err (n : ℕ) : ℝ := 3 * Real.log 10 / n
  have bounds : ∀ᶠ n : ℕ in atTop, 0 < (a n : ℝ) ∧
      c - err n ≤ Real.log (a n) / n ∧ Real.log (a n) / n ≤ c + err n := by
    filter_upwards [eventually_ge_atTop 6] with n hn
    have ⟨h₁, h₂⟩ := square_bounds n hn
    have ha : 0 < a n := by
      by_contra! hz
      have hnz : a n = 0 := by omega
      simp [hnz] at h₁
    have harp : 0 < (a n : ℝ) := by exact_mod_cast ha
    have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have w₁ : (10:ℝ)^n ≤ 10^6*(a n:ℝ)^2 := by exact_mod_cast h₁
    have w₂ : (a n:ℝ)^2 ≤ 10^6*(10:ℝ)^n := by exact_mod_cast h₂
    have t₁ := Real.log_le_log (by positivity) w₁
    have t₂ := Real.log_le_log (by positivity) w₂
    rw [Real.log_mul (by positivity) (by positivity)] at t₁ t₂
    simp only [Real.log_pow, Nat.cast_ofNat] at t₁ t₂
    refine ⟨harp, ?_, ?_⟩
    · dsimp [c, err]
      field_simp [hnr.ne']
      nlinarith only [t₁]
    · dsimp [c, err]
      field_simp [hnr.ne']
      nlinarith only [t₂]
  have e : Tendsto err atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat _
  have lower : Tendsto (fun n => c - err n) atTop (nhds c) := by
    simpa using (tendsto_const_nhds (x := c)).sub e
  have upper : Tendsto (fun n => c + err n) atTop (nhds c) := by
    simpa using (tendsto_const_nhds (x := c)).add e
  have logs := tendsto_of_tendsto_of_tendsto_of_le_of_le' lower upper
    (bounds.mono fun _ h => h.2.1) (bounds.mono fun _ h => h.2.2)
  have he : Real.exp c = Real.sqrt 10 := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0:ℝ)<10)]
    congr 1
    dsimp [c]
    ring
  rw [← he]
  apply ((Real.continuous_exp.tendsto c).comp logs).congr'
  filter_upwards [bounds] with n h
  simp only [Function.comp_apply, Real.rpow_def_of_pos h.1, div_eq_mul_inv, one_mul]

end DoubleReverseGrowth

theorem OMA.solution : type_of% @OMA.S_oeis_a036447.main := by
  apply DoubleReverseGrowth.root_limit
