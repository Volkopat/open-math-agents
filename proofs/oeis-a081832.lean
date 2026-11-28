import OMAStatements.S_oeis_a081832

-- Problem: A081832: a(1)=a(2)=1, a(n) = a(n+1-2*a(n-1)) + a(n-2*a(n-2)).
-- Credit: @sobrien032

/- Benoît Cloitre introduced A081832. Altuğ Alkan proved its slow increments.
   Frédéric Gaudin determined the exact block endpoints in his paper on
   EJIRT Conjecture 5.1. We verify the endpoint recurrence directly and
   bound its error to prove both of Cloitre's conjectures. -/

open Filter
open scoped Topology

namespace Gaudin

/-- Last index of a block in Benoit Cloitre's sequence, using the binary
recursion for Frédéric Gaudin's cumulative count. -/
def B (n : ℕ) : ℕ :=
  if hn : n = 0 then 0
  else if n % 2 = 0 then B (n / 2) + 4 * (n / 2) - 1
  else B (n / 2) + 4 * (n / 2) + 2
termination_by n
decreasing_by all_goals omega

def Holds (a : ℕ → ℕ) (n m : ℕ) : Prop :=
  0 < m → B (m - 1) < n → n ≤ B m → a n = m

theorem B_zero : B 0 = 0 := by
  rw [B]
  decide

theorem B_even (k : ℕ) (hk : 0 < k) : B (2*k) = B k + 4*k - 1 := by
  rw [B]
  simp [show 2*k ≠ 0 by omega, show (2*k) % 2 = 0 by omega,
    show (2*k) / 2 = k by omega]

theorem B_odd (k : ℕ) : B (2*k+1) = B k + 4*k + 2 := by
  rw [B]
  simp [show (2*k+1) / 2 = k by omega]

theorem B_gap (k : ℕ) : B k + 2 ≤ B (k+1) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    let j := k / 2
    by_cases hz : k = 0
    · subst k
      have hone : B 1 = 2 := by simpa [B_zero] using B_odd 0
      simp [B_zero, hone]
    by_cases hp : k % 2 = 0
    · have he : k = 2*j := by dsimp [j]; omega
      have h1 := B_even j (by omega)
      have h2 := B_odd j
      rw [he]
      omega
    · have ho : k = 2*j+1 := by dsimp [j]; omega
      have h1 := B_odd j
      have h2 := B_even (j+1) (by omega)
      have hj := ih j (by omega)
      rw [ho, show 2*j+1+1 = 2*(j+1) by omega]
      omega

private theorem index_le_end (k : ℕ) : k ≤ B k := by
  induction k with
  | zero => omega
  | succ k ih => have h := B_gap k; omega

theorem exists_block {n : ℕ} (hn : 0 < n) :
    ∃ m, 0 < m ∧ B (m-1) < n ∧ n ≤ B m := by
  have hex : ∃ m, n ≤ B m := ⟨n, index_le_end n⟩
  let m := Nat.find hex
  have hhi : n ≤ B m := Nat.find_spec hex
  have hm : 0 < m := by
    by_contra! h
    rw [show m = 0 by omega, B_zero] at hhi
    omega
  have hlo : ¬n ≤ B (m-1) := Nat.find_min hex (show m-1 < m by omega)
  exact ⟨m, hm, by omega, hhi⟩

theorem even_step {a : ℕ → ℕ} (ha : OMA.S_oeis_a081832.IsA081832 a) {n k : ℕ}
    (hk : 0 < k) (ih : ∀ j < n, ∀ m, Holds a j m) : Holds a n (2*k) := by
  intro _ lower upper
  have lo := B_odd (k-1)
  rw [show 2*(k-1)+1 = 2*k-1 by omega] at lo
  have hi := B_even k hk
  have halfGap := B_gap (k-1)
  rw [show k-1+1 = k by omega] at halfGap
  have prevGap := B_gap (2*k-1-1)
  rw [show 2*k-1-1+1 = 2*k-1 by omega] at prevGap
  have term (p : ℕ) (hp : n-2 ≤ p) (hpn : p < n) : a (p+2-2*a p) = k := by
    by_cases hprev : p ≤ B (2*k-1)
    · have ap := ih p hpn (2*k-1) (by omega) (by omega) hprev
      rw [ap]
      exact ih _ (by omega) k hk (by omega) (by omega)
    · have ap := ih p hpn (2*k) (by omega) (by omega) (by omega)
      rw [ap]
      exact ih _ (by omega) k hk (by omega) (by omega)
  have first := term (n-1) (by omega) (by omega)
  have second := term (n-2) (by omega) (by omega)
  rw [show n-1+2 = n+1 by omega] at first
  rw [show n-2+2 = n by omega] at second
  rw [ha.2.2 n (by omega), first, second]
  omega

theorem odd_step {a : ℕ → ℕ} (ha : OMA.S_oeis_a081832.IsA081832 a) {n k : ℕ}
    (hk : 0 < k) (ih : ∀ j < n, ∀ m, Holds a j m) : Holds a n (2*k+1) := by
  intro _ lower upper
  have he := B_even k hk
  have ho := B_odd k
  have hprev : B (2*k-1) + 2 ≤ B (2*k) := by
    simpa only [show 2*k-1+1=2*k by omega] using B_gap (2*k-1)
  have hprevk : B (k-1) + 2 ≤ B k := by
    simpa only [show k-1+1=k by omega] using B_gap (k-1)
  have hg := B_gap k
  simp only [Nat.add_one_sub_one] at lower
  have lookup (p : ℕ) (hp : p < n) (hpn : n-2 ≤ p) :
      a p = if p ≤ B (2*k) then 2*k else 2*k+1 := by
    split
    · exact ih p hp (2*k) (by omega) (by omega) (by omega)
    · exact ih p hp (2*k+1) (by omega) (by simp only [Nat.add_one_sub_one]; omega) (by omega)
  have hk0 : a (B k) = k := ih _ (by omega) k hk (by omega) le_rfl
  have hk1 : a (B k+1) = k+1 := ih _ (by omega) (k+1) (by omega) (by simp) (by omega)
  have e1 := lookup (n-1) (by omega) (by omega)
  have e2 := lookup (n-2) (by omega) (by omega)
  have add_pair (u v : ℕ) (h : (u = B k ∧ v = B k+1) ∨ (u = B k+1 ∧ v = B k)) :
      a u + a v = 2*k+1 := by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [hk0, hk1] <;> omega
  rw [ha.2.2 n (by omega), e1, e2]
  apply add_pair
  split <;> split <;> omega

private noncomputable def errorTerm (k : ℕ) : ℝ := 4 * (k : ℝ) - (B k : ℝ)

private theorem error_bounds (k : ℕ) :
    0 ≤ errorTerm k ∧ (k = 0 ∨ (errorTerm k + 5)^2 ≤ 49 * (k : ℝ)) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · simp [errorTerm, B_zero]
    rcases k with _ | k
    · have h1 := B_odd 0
      norm_num [B_zero] at h1
      norm_num [errorTerm, h1]
    let j := (k+2)/2
    have hj : 0 < j := by dsimp [j]; omega
    have hjk : j < k+2 := by dsimp [j]; omega
    obtain ⟨h0, h1 | h1⟩ := ih j hjk
    · omega
    have he : errorTerm (2*j) = errorTerm j + 1 := by
      have hsub : 1 ≤ B j + 4*j := by omega
      simp only [errorTerm, B_even j hj, Nat.cast_sub hsub, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat, Nat.cast_one]
      ring
    have ho : errorTerm (2*j+1) = errorTerm j + 2 := by
      simp only [errorTerm, B_odd, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      ring
    have hc : k+2 = 2*j ∨ k+2 = 2*j+1 := by dsimp [j]; omega
    change 0 ≤ errorTerm (k+2) ∧ (k+2 = 0 ∨ (errorTerm (k+2)+5)^2 ≤ 49*(↑(k+2 : ℕ) : ℝ))
    rcases hc with h | h
    · rw [h, he]
      push_cast
      exact ⟨by linarith, Or.inr (by nlinarith [sq_nonneg (errorTerm j)])⟩
    · rw [h, ho]
      push_cast
      exact ⟨by linarith, Or.inr (by nlinarith [sq_nonneg (errorTerm j)])⟩

private theorem error_le_sqrt {k n : ℕ} (hkn : k ≤ n) :
    errorTerm k ≤ 7 * Real.sqrt n := by
  rcases error_bounds k with ⟨h0, rfl | h1⟩
  · simpa only [errorTerm, B_zero, Nat.cast_zero, mul_zero, sub_zero] using
      (show 0 ≤ 7 * Real.sqrt (n : ℝ) by positivity)
  apply (sq_le_sq₀ h0 (by positivity : 0 ≤ 7 * Real.sqrt n)).1
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hle : (k : ℝ) ≤ n := by exact_mod_cast hkn
  nlinarith

theorem asymp {a : ℕ → ℕ} (bounds : ∀ n, 0 < n →
    0 < a n ∧ B (a n-1) < n ∧ n ≤ B (a n)) :
    Tendsto (fun n : ℕ => (a n : ℝ)/(n : ℝ)) atTop (𝓝 (1/4 : ℝ)) := by
  have estimates (n : ℕ) (hn : 0 < n) :
      1/4 ≤ (a n : ℝ)/n ∧
      (a n : ℝ)/n ≤ ((4 : ℝ)/n + 7/Real.sqrt n + 1)/4 := by
    obtain ⟨ha, hl, hu⟩ := bounds n hn
    let k := a n-1
    have hk : k+1 = a n := by dsimp [k]; omega
    have hkn : k ≤ n := (index_le_end k).trans (le_of_lt hl)
    have hk' : (k : ℝ)+1 = a n := by exact_mod_cast hk
    have hnn : (0 : ℝ) < n := by exact_mod_cast hn
    have hs := Real.sqrt_pos.2 hnn
    have hlo := (error_bounds (a n)).1
    have hhi := error_le_sqrt hkn
    unfold errorTerm at hlo hhi
    have hle : (n : ℝ) ≤ B (a n) := by exact_mod_cast hu
    have hlt : (B k : ℝ) < n := by exact_mod_cast hl
    constructor
    · apply (le_div_iff₀ hnn).2
      linarith
    · apply (div_le_div_iff₀ hnn (by norm_num : (0 : ℝ) < 4)).2
      have hdiv : (4 : ℝ)/n * n = 4 := div_mul_cancel₀ _ hnn.ne'
      have hroot : (7 : ℝ)/Real.sqrt n * n = 7*Real.sqrt n := by
        calc
          _ = 7/Real.sqrt n * (Real.sqrt n * Real.sqrt n) := by
            rw [Real.mul_self_sqrt hnn.le]
          _ = _ := by rw [← mul_assoc, div_mul_cancel₀ _ hs.ne']
      linarith only [hhi, hk', hlt, hdiv, hroot]
  have h4 : Tendsto (fun n : ℕ => (4 : ℝ)/n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h7 : Tendsto (fun n : ℕ => (7 : ℝ)/Real.sqrt n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hu : Tendsto (fun n : ℕ => ((4:ℝ)/n+7/Real.sqrt n+1)/4) atTop (𝓝 (1/4:ℝ)) := by
    simpa using (((h4.add h7).add (tendsto_const_nhds (x := (1:ℝ)))).div_const 4)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [eventually_gt_atTop 0] with n hn using (estimates n hn).1
  · filter_upwards [eventually_gt_atTop 0] with n hn using (estimates n hn).2

theorem on_block {a : ℕ → ℕ} (ha : OMA.S_oeis_a081832.IsA081832 a) (n : ℕ) :
    ∀ m, Holds a n m := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro m
    by_cases hsmall : m ≤ 1
    · intro hm hl hu
      have hm1 : m = 1 := by omega
      subst m
      have h1 : B 1 = 2 := by simpa [B_zero] using B_odd 0
      simp only [Nat.sub_self, B_zero] at hl
      rw [h1] at hu
      rcases (show n=1 ∨ n=2 by omega) with rfl | rfl
      · exact ha.1
      · exact ha.2.1
    · rcases (show m = 2*(m/2) ∨ m = 2*(m/2)+1 by omega) with he | ho
      · rw [he]
        exact even_step ha (k := m/2) (by omega) ih
      · rw [ho]
        exact odd_step ha (k := m/2) (by omega) ih


end Gaudin

open Gaudin

theorem OMA.solution : type_of% @OMA.S_oeis_a081832.main := by
  intro a ha
  have bounds (n : ℕ) (hn : 0 < n) : 0 < a n ∧ B (a n-1)<n ∧ n≤B (a n) := by
    obtain ⟨m, hm, hl, hu⟩ := exists_block hn
    rw [on_block ha n m hm hl hu]
    exact ⟨hm,hl,hu⟩
  refine ⟨asymp bounds, ?_⟩
  intro n hn
  obtain ⟨hm, hl, hu⟩ := bounds n hn
  by_cases h : n+1 ≤ B (a n)
  · exact Or.inl (on_block ha (n+1) (a n) hm (by omega) h)
  · exact Or.inr (on_block ha (n+1) (a n+1) (by omega) (by simp only [Nat.add_one_sub_one]; omega) (by have := B_gap (a n); omega))
