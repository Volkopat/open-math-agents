import OMAStatements.S_oeis_a001652

-- Problem: A001652: a(n) = 6*a(n-1) - a(n-2) + 2 with a(0) = 0, a(1) = 3.
-- Upstream: formal-conjectures statements/oeis-a001652.lean:0 (declaration OMA.S_oeis_a001652.main)
-- Credit: @GiridhariPradeep (agent: Claude Code, model claude-opus-5-5)
-- Lease: a860de86-1271-41a4-8203-3a1eccc5a743
--
-- Proof idea. Write `H, P` for the companion Pell and Pell numbers (`H j + P j √2 = (1+√2)^j`).
-- Because `H j √2 - 2 P j = 2 (-1)^j / (H j √2 + 2 P j)` is tiny, `⌊(H j + r) √2⌋ = ⌊r √2⌋ + 2 P j`
-- for `1 ≤ r < 2 P j`, `r ≠ P j` (the near misses are classified by the Pell equation).
-- Hence the partial sums satisfy `b (H j + r) = b (H j) + b r ∓ 2 (-1)^j [P j ≤ r]`, with
-- `b (H j) = (-1)^j`. This gives sharp bounds for `b` on each block `[0, H j)`, and
-- `a (n+1) = H (2n+2) + a n` is then exactly the first time `b` reaches `n + 1`.

namespace OMA.A1652

/-- Companion Pell numbers `H` (1,1,3,7,17,…) and Pell numbers `P` (0,1,2,5,12,…). -/
def HP : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | j + 1 => ((HP j).1 + 2 * (HP j).2, (HP j).1 + (HP j).2)

def H (j : ℕ) : ℕ := (HP j).1
def P (j : ℕ) : ℕ := (HP j).2

@[simp] lemma H_zero : H 0 = 1 := rfl
@[simp] lemma P_zero : P 0 = 0 := rfl
lemma H_succ (j : ℕ) : H (j + 1) = H j + 2 * P j := rfl
lemma P_succ (j : ℕ) : P (j + 1) = H j + P j := rfl

/-- sign `(-1)^j` -/
def e (j : ℕ) : ℤ := if j % 2 = 0 then 1 else -1

lemma e_succ (j : ℕ) : e (j + 1) = - e j := by
  unfold e; split_ifs <;> omega

lemma H_pos (j : ℕ) : 1 ≤ H j := by
  induction j with
  | zero => simp
  | succ j ih => rw [H_succ]; omega

lemma P_le_H (j : ℕ) : P j ≤ H j := by
  induction j with
  | zero => simp
  | succ j ih => rw [H_succ, P_succ]; omega

lemma H_odd (j : ℕ) : H j % 2 = 1 := by
  induction j with
  | zero => simp
  | succ j ih => rw [H_succ]; omega

lemma P_pos {j : ℕ} (hj : 1 ≤ j) : 1 ≤ P j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [P_succ]; have := H_pos k; omega

lemma P_mono {i j : ℕ} (h : i ≤ j) : P i ≤ P j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [P_succ]; omega

lemma H_mono {i j : ℕ} (h : i ≤ j) : H i ≤ H j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [H_succ]; omega

/-- Pell identity `H^2 - 2 P^2 = (-1)^j`. -/
lemma pell (j : ℕ) : (H j : ℤ) ^ 2 - 2 * (P j : ℤ) ^ 2 = e j := by
  induction j with
  | zero => simp [e]
  | succ j ih => rw [H_succ, P_succ, e_succ, ← ih]; push_cast; ring

lemma pell_even {j : ℕ} (h : j % 2 = 0) : H j ^ 2 = 2 * P j ^ 2 + 1 := by
  have := pell j; simp [e, h] at this; zify; linarith

lemma pell_odd {j : ℕ} (h : j % 2 = 1) : H j ^ 2 + 1 = 2 * P j ^ 2 := by
  have := pell j; simp [e, h] at this; zify; linarith

/-- All nonnegative solutions of `x^2 - 2 y^2 = ±1` are `(H i, P i)`. -/
lemma pell_class : ∀ y x : ℕ, (x ^ 2 = 2 * y ^ 2 + 1 ∨ x ^ 2 + 1 = 2 * y ^ 2) →
    ∃ i, x = H i ∧ y = P i := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro x hx
    rcases Nat.eq_zero_or_pos y with rfl | hy
    · refine ⟨0, ?_, rfl⟩
      rcases hx with hx | hx
      · simp at hx; simpa using hx
      · simp at hx
    · have hxy : y ≤ x := by
        by_contra hc; push Not at hc
        have : x ^ 2 < y ^ 2 := Nat.pow_lt_pow_left hc (by norm_num)
        rcases hx with hx | hx <;> nlinarith
      have hx2 : x < 2 * y := by
        by_contra hc; push Not at hc
        have : (2 * y) ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hc 2
        rcases hx with hx | hx <;> nlinarith
      obtain ⟨i, hi1, hi2⟩ := ih (x - y) (by omega) (2 * y - x) (by
        obtain ⟨a, rfl⟩ : ∃ a, x = y + a := ⟨x - y, by omega⟩
        have e1 : y + a - y = a := by omega
        have e2 : 2 * y - (y + a) = y - a := by omega
        rw [e1, e2]
        obtain ⟨c, hc⟩ : ∃ c, y = a + c := ⟨y - a, by omega⟩
        have e3 : y - a = c := by omega
        rw [e3]; subst hc
        rcases hx with hx | hx
        · right; nlinarith
        · left; nlinarith)
      refine ⟨i + 1, ?_, ?_⟩
      · rw [H_succ]; omega
      · rw [P_succ]; omega

/-! ## `√2` and floors -/

noncomputable abbrev s : ℝ := Real.sqrt 2

lemma s_sq : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)
lemma s_pos : 0 < s := Real.sqrt_pos.2 (by norm_num)
lemma s_lo : (1.414 : ℝ) < s := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num
lemma s_hi : s < (1.415 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma even_of_sq {u w : ℕ} (h : u ^ 2 = 2 * w) : ∃ v, u = 2 * v := by
  rcases Nat.even_or_odd u with ⟨v, hv⟩ | ⟨v, hv⟩
  · exact ⟨v, by omega⟩
  · subst hv
    have : (2 * v + 1) ^ 2 = 2 * (2 * v ^ 2 + 2 * v) + 1 := by ring
    omega

/-- `⌊k √2⌋` as a natural number. -/
noncomputable def fl (k : ℕ) : ℕ := ⌊(k : ℝ) * s⌋.toNat

lemma fl_spec (k : ℕ) : (fl k : ℝ) ≤ k * s ∧ (k : ℝ) * s < fl k + 1 := by
  have h0 : 0 ≤ (k : ℝ) * s := by positivity
  have hf : (0 : ℤ) ≤ ⌊(k : ℝ) * s⌋ := Int.floor_nonneg.2 h0
  have hc : ((fl k : ℕ) : ℝ) = ((⌊(k : ℝ) * s⌋ : ℤ) : ℝ) := by
    have h1 : ((fl k : ℕ) : ℤ) = ⌊(k : ℝ) * s⌋ := Int.toNat_of_nonneg hf
    rw [← h1, Int.cast_natCast]
  rw [hc]
  exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩

lemma fl_eq {k t : ℕ} (h1 : (t : ℝ) ≤ k * s) (h2 : (k : ℝ) * s < t + 1) : fl k = t := by
  have : ⌊(k : ℝ) * s⌋ = t := Int.floor_eq_iff.2 ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  simp [fl, this]

lemma le_of_sq {t k : ℕ} (h : t ^ 2 ≤ 2 * k ^ 2) : (t : ℝ) ≤ k * s := by
  have h' : (t : ℝ) ^ 2 ≤ 2 * (k : ℝ) ^ 2 := by exact_mod_cast h
  have h0 : 0 ≤ (k : ℝ) * s := by positivity
  by_contra hc; push Not at hc
  nlinarith [s_sq]

lemma lt_of_sq {t k : ℕ} (h : 2 * k ^ 2 < t ^ 2) : (k : ℝ) * s < t := by
  have h' : 2 * (k : ℝ) ^ 2 < (t : ℝ) ^ 2 := by exact_mod_cast h
  have h0 : 0 ≤ (t : ℝ) := by positivity
  by_contra hc; push Not at hc
  nlinarith [s_sq]

lemma sq_le_of {t k : ℕ} (h : (t : ℝ) ≤ k * s) : t ^ 2 ≤ 2 * k ^ 2 := by
  have h0 : 0 ≤ (t : ℝ) := by positivity
  have : (t : ℝ) ^ 2 ≤ 2 * (k : ℝ) ^ 2 := by nlinarith [s_sq]
  exact_mod_cast this

lemma sq_lt_of {t k : ℕ} (h : (k : ℝ) * s < t) : 2 * k ^ 2 < t ^ 2 := by
  have h0 : 0 ≤ (k : ℝ) * s := by positivity
  have : 2 * (k : ℝ) ^ 2 < (t : ℝ) ^ 2 := by nlinarith [s_sq]
  exact_mod_cast this

/-! ## the sign sequence -/

noncomputable def σ (k : ℕ) : ℤ := (-1 : ℤ) ^ (fl k)

lemma neg_one_pow_eq (n : ℕ) : (-1 : ℤ) ^ n = if n % 2 = 0 then 1 else -1 := by
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow]; simp [Nat.even_iff.1 h]
  · rw [h.neg_one_pow]; simp [Nat.odd_iff.1 h]

lemma σ_eq_e {k j : ℕ} (h : fl k % 2 = j % 2) : σ k = e j := by
  unfold σ e; rw [neg_one_pow_eq]; split_ifs <;> omega

lemma fl_P {j : ℕ} (_hj : 1 ≤ j) : fl (P j) % 2 = j % 2 := by
  have hH := H_pos j
  have hodd := H_odd j
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · have hp := pell_even h
    obtain ⟨c, hc⟩ : ∃ c, H j = c + 1 := ⟨H j - 1, by omega⟩
    have : fl (P j) = c := by
      apply fl_eq
      · apply le_of_sq; rw [hc] at hp; nlinarith
      · have := lt_of_sq (t := c + 1) (k := P j) (by rw [← hc]; omega)
        push_cast at this; linarith
    omega
  · have hp := pell_odd h
    have : fl (P j) = H j := by
      apply fl_eq
      · apply le_of_sq; omega
      · have := lt_of_sq (t := H j + 1) (k := P j) (by nlinarith)
        push_cast at this; linarith
    omega

lemma fl_H {j : ℕ} (hj : 1 ≤ j) : fl (H j) % 2 = j % 2 := by
  have hP := P_pos hj
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · have hp := pell_even h
    have : fl (H j) = 2 * P j := by
      apply fl_eq
      · have := le_of_sq (t := 2 * P j) (k := H j) (by nlinarith)
        push_cast at this ⊢; linarith
      · have := lt_of_sq (t := 2 * P j + 1) (k := H j) (by nlinarith)
        push_cast at this ⊢; linarith
    omega
  · have hp := pell_odd h
    obtain ⟨c, hc⟩ : ∃ c, P j = c + 1 := ⟨P j - 1, by omega⟩
    have : fl (H j) = 2 * c + 1 := by
      apply fl_eq
      · apply le_of_sq; rw [hc] at hp; nlinarith
      · have := lt_of_sq (t := 2 * c + 2) (k := H j) (by rw [hc] at hp; nlinarith)
        push_cast at this ⊢; linarith
    omega

lemma σ_P {j : ℕ} (hj : 1 ≤ j) : σ (P j) = e j := σ_eq_e (fl_P hj)
lemma σ_H {j : ℕ} (hj : 1 ≤ j) : σ (H j) = e j := σ_eq_e (fl_H hj)

/-! ## `L i = H i + P i √2 = (1 + √2)^i` -/

noncomputable def L (i : ℕ) : ℝ := H i + P i * s

lemma L_succ (i : ℕ) : L (i + 1) = L i * (1 + s) := by
  unfold L; rw [H_succ, P_succ]; push_cast
  linear_combination (-(P i : ℝ)) * s_sq

lemma L_pos (i : ℕ) : 0 < L i := by
  unfold L; have := H_pos i
  have : (1 : ℝ) ≤ H i := by exact_mod_cast this
  positivity

lemma L_lt_succ (i : ℕ) : L i < L (i + 1) := by
  rw [L_succ]; nlinarith [L_pos i, s_pos]

lemma L_mono {i j : ℕ} (h : i ≤ j) : L i ≤ L j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (L_lt_succ _).le

lemma L_lt {i j : ℕ} (h : i < j) : L i < L j :=
  (L_lt_succ i).trans_le (L_mono h)

lemma L_two (i : ℕ) : L (i + 2) = L i * (3 + 2 * s) := by
  rw [L_succ, L_succ]; linear_combination (L i) * s_sq

lemma key_lt {A B C D N : ℝ} (hB : 0 < B) (hD : 0 < D) (hAB : A * B = 2) (hCD : C * D = N)
    (h : 2 * D < N * B) : A < C := by
  have hA : A = 2 / B := by field_simp; linarith
  have hC : C = N / D := by field_simp; linarith
  rw [hA, hC, div_lt_div_iff₀ hB hD]; linarith

lemma key_le {A B C D N : ℝ} (hB : 0 < B) (hD : 0 < D) (hAB : A * B = 2) (hCD : C * D = N)
    (h : 2 * D ≤ N * B) : A ≤ C := by
  have hA : A = 2 / B := by field_simp; linarith
  have hC : C = N / D := by field_simp; linarith
  rw [hA, hC, div_le_div_iff₀ hB hD]; linarith

lemma sL (j : ℕ) : s * L j = H j * s + 2 * P j := by
  unfold L; linear_combination (P j : ℝ) * s_sq

lemma Hs_gt {j : ℕ} (hj : 1 ≤ j) : (2 * P j : ℝ) - 1 < H j * s := by
  have hP : (1 : ℝ) ≤ P j := by exact_mod_cast P_pos hj
  have hpe := pell j
  have he : e j = 1 ∨ e j = -1 := by unfold e; split_ifs <;> simp
  have hpR : (H j : ℝ) ^ 2 - 2 * (P j : ℝ) ^ 2 = e j := by exact_mod_cast hpe
  have h0 : 0 ≤ (H j : ℝ) * s := by positivity
  have h2 : (2 * (P j : ℝ) ^ 2 - 1) ≤ (H j : ℝ) ^ 2 := by
    rcases he with h | h <;> rw [h] at hpR <;> push_cast at hpR <;> linarith
  by_contra hc; push Not at hc
  nlinarith [s_sq]

/-- index bound from `P i < 2 P j` -/
lemma idx_P {i j : ℕ} (h : P i < 2 * P j) : i ≤ j := by
  by_contra hc; push Not at hc
  have := P_mono (show j + 1 ≤ i by omega)
  rw [P_succ] at this; have := P_le_H j; omega

lemma idx_H {i j : ℕ} (h : H i < 2 * P j) : i ≤ j := by
  by_contra hc; push Not at hc
  have := H_mono (show j + 1 ≤ i by omega)
  rw [H_succ] at this; have := H_pos j; omega

lemma parity_of_pell_even {i : ℕ} (h : H i ^ 2 = 2 * P i ^ 2 + 1) : i % 2 = 0 := by
  by_contra hc
  have := pell_odd (j := i) (by omega); omega

lemma parity_of_pell_odd {i : ℕ} (h : H i ^ 2 + 1 = 2 * P i ^ 2) : i % 2 = 1 := by
  by_contra hc
  have := pell_even (j := i) (by omega); omega

lemma aux1 {Li Lj : ℝ} (hLi : 0 < Li) (h : Li * (3 + 2 * s) ≤ Lj) : 2 * Li < s * Lj := by
  have := s_lo; have := s_pos
  have h1 := mul_le_mul_of_nonneg_left h s_pos.le
  have h2 : s * (Li * (3 + 2 * s)) = Li * (3 * s + 4) := by linear_combination (2 * Li) * s_sq
  nlinarith

lemma aux3 {P X B rs : ℝ} (hP : 1 ≤ P) (hX : X ≤ 2 * rs + 1) (hrs : rs ≤ (2 * P - 1) * s)
    (hB : 4 * P - 1 < B) : 2 * X < 3 * B := by
  have := s_hi
  have h1 : 0 ≤ (12 - 8 * s) * (P - 1) := mul_nonneg (by linarith) (by linarith)
  nlinarith

lemma eq_of_sq_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) : a = b :=
  (pow_left_inj₀ ha hb two_ne_zero).1 h

lemma core_even {j r : ℕ} (hj : 1 ≤ j) (hr1 : 1 ≤ r) (hr2 : r < 2 * P j) (hne : r ≠ P j)
    (hpar : j % 2 = 0) :
    (H j : ℝ) * s - 2 * P j < ((fl r + 1 : ℕ) : ℝ) - r * s := by
  have ht2 := (fl_spec r).2
  have hu : 2 * r ^ 2 < (fl r + 1) ^ 2 := sq_lt_of (by push_cast; linarith)
  generalize hU : fl r + 1 = u at hu ht2 ⊢
  have hP1 : (1 : ℝ) ≤ P j := by exact_mod_cast P_pos hj
  have hHs := Hs_gt hj
  have hsL := sL j
  have hB : (0 : ℝ) < H j * s + 2 * P j := by linarith
  have hp := pell_even hpar
  have hpR : (H j : ℝ) ^ 2 = 2 * (P j : ℝ) ^ 2 + 1 := by exact_mod_cast hp
  have hAB : (H j * s - 2 * P j) * (H j * s + 2 * P j) = 2 := by
    linear_combination ((H j : ℝ) ^ 2) * s_sq + 2 * hpR
  have hCD : ((u : ℝ) - r * s) * ((u : ℝ) + r * s) = ((u ^ 2 - 2 * r ^ 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hu.le]; push_cast
    linear_combination (-(r : ℝ) ^ 2) * s_sq
  have hD : (0 : ℝ) < u + r * s := by have := s_pos; positivity
  apply key_lt hB hD hAB hCD
  rcases (show u ^ 2 = 2 * r ^ 2 + 1 ∨ u ^ 2 = 2 * r ^ 2 + 2 ∨ 2 * r ^ 2 + 3 ≤ u ^ 2 by omega)
    with h | h | h
  · obtain ⟨i, hui, hri⟩ := pell_class r u (Or.inl h)
    have hi0 : i % 2 = 0 := parity_of_pell_even (by rw [← hui, ← hri]; exact h)
    have hij : i ≤ j := idx_P (by rw [← hri]; exact hr2)
    have hij' : i ≠ j := by rintro rfl; exact hne hri
    have hL := L_mono (show i + 2 ≤ j by omega)
    rw [L_two] at hL
    have hDL : (u : ℝ) + r * s = L i := by unfold L; rw [hui, hri]
    rw [hDL, show u ^ 2 - 2 * r ^ 2 = 1 by omega]
    have := aux1 (L_pos i) hL
    push_cast; linarith
  · obtain ⟨v, hv⟩ := even_of_sq (w := r ^ 2 + 1) (by omega)
    have h4 : (2 * v) ^ 2 = 4 * v ^ 2 := by ring
    rw [hv] at h
    obtain ⟨i, hri, hvi⟩ := pell_class v r (Or.inr (by omega))
    have hi1 : i % 2 = 1 := parity_of_pell_odd (by rw [← hri, ← hvi]; omega)
    have hij : i ≤ j := idx_H (by rw [← hri]; exact hr2)
    have hLt := mul_lt_mul_of_pos_left (L_lt (show i < j by omega)) s_pos
    have hDL : ((2 * v : ℕ) : ℝ) + r * s = s * L i := by
      rw [sL, hri, hvi]; push_cast; ring
    rw [hv, hDL, show (2 * v) ^ 2 - 2 * r ^ 2 = 2 by omega]
    push_cast; linarith
  · have hN : (3 : ℝ) ≤ ((u ^ 2 - 2 * r ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast (show 3 ≤ u ^ 2 - 2 * r ^ 2 by omega)
    have h3 := mul_le_mul_of_nonneg_right hN hB.le
    have hrsP : (r : ℝ) * s ≤ (2 * P j - 1) * s := by
      have : (r : ℝ) + 1 ≤ 2 * P j := by exact_mod_cast (show r + 1 ≤ 2 * P j by omega)
      have := s_pos; nlinarith
    have hX : (u : ℝ) + r * s ≤ 2 * (r * s) + 1 := by
      have := (fl_spec r).1
      have hu' : (u : ℝ) = fl r + 1 := by rw [← hU]; push_cast; ring
      linarith
    have := aux3 (B := H j * s + 2 * P j) hP1 hX hrsP (by linarith)
    linarith

lemma core_odd {j r : ℕ} (hj : 1 ≤ j) (hr1 : 1 ≤ r) (hr2 : r < 2 * P j) (hne : r ≠ P j)
    (hpar : j % 2 = 1) :
    2 * P j - (H j : ℝ) * s ≤ (r : ℝ) * s - fl r := by
  have ht1 := (fl_spec r).1
  have ht0 : fl r ^ 2 ≤ 2 * r ^ 2 := sq_le_of ht1
  generalize fl r = t at ht0 ht1 ⊢
  have hP1 : (1 : ℝ) ≤ P j := by exact_mod_cast P_pos hj
  have hHs := Hs_gt hj
  have hsL := sL j
  have hB : (0 : ℝ) < H j * s + 2 * P j := by linarith
  have hp := pell_odd hpar
  have hpR : (H j : ℝ) ^ 2 + 1 = 2 * (P j : ℝ) ^ 2 := by exact_mod_cast hp
  have hAB : (2 * P j - H j * s) * (H j * s + 2 * P j) = 2 := by
    linear_combination (-(H j : ℝ) ^ 2) * s_sq - 2 * hpR
  have hCD : ((r : ℝ) * s - t) * ((r : ℝ) * s + t) = ((2 * r ^ 2 - t ^ 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub ht0]; push_cast
    linear_combination ((r : ℝ) ^ 2) * s_sq
  have hrs : (0 : ℝ) < r * s := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    have := s_pos; positivity
  have hD : (0 : ℝ) < r * s + t := by positivity
  apply key_le hB hD hAB hCD
  rcases (show 2 * r ^ 2 = t ^ 2 ∨ 2 * r ^ 2 = t ^ 2 + 1 ∨ 2 * r ^ 2 = t ^ 2 + 2 ∨
      t ^ 2 + 3 ≤ 2 * r ^ 2 by omega) with h | h | h | h
  · exfalso
    have hR : ((r : ℝ) * s) ^ 2 = (t : ℝ) ^ 2 := by
      have : (t : ℝ) ^ 2 = 2 * (r : ℝ) ^ 2 := by exact_mod_cast h.symm
      rw [mul_pow, s_sq]; linarith
    have heq := eq_of_sq_eq hrs.le (by positivity) hR
    exact (irrational_sqrt_two.mul_natCast (m := r) (by omega)).ne_nat t
      (by rw [mul_comm]; exact heq)
  · obtain ⟨i, hti, hri⟩ := pell_class r t (Or.inr (by omega))
    have hi1 : i % 2 = 1 := parity_of_pell_odd (by rw [← hti, ← hri]; omega)
    have hij : i ≤ j := idx_P (by rw [← hri]; exact hr2)
    have hij' : i ≠ j := by rintro rfl; exact hne hri
    have hL := L_mono (show i + 2 ≤ j by omega)
    rw [L_two] at hL
    have hDL : (r : ℝ) * s + t = L i := by unfold L; rw [hti, hri]; ring
    rw [hDL, show 2 * r ^ 2 - t ^ 2 = 1 by omega]
    have := aux1 (L_pos i) hL
    push_cast; linarith
  · obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le (Nat.one_le_pow 2 r hr1)
    obtain ⟨v, hv⟩ := even_of_sq (u := t) (w := c) (by omega)
    have h4 : (2 * v) ^ 2 = 4 * v ^ 2 := by ring
    rw [hv] at h
    obtain ⟨i, hri, hvi⟩ := pell_class v r (Or.inl (by omega))
    have hi0 : i % 2 = 0 := parity_of_pell_even (by rw [← hri, ← hvi]; omega)
    have hij : i ≤ j := idx_H (by rw [← hri]; exact hr2)
    have hLt := mul_le_mul_of_nonneg_left (L_mono hij) s_pos.le
    have hDL : (r : ℝ) * s + ((2 * v : ℕ) : ℝ) = s * L i := by
      rw [sL, hri, hvi]; push_cast; ring
    rw [hv, hDL, show 2 * r ^ 2 - (2 * v) ^ 2 = 2 by omega]
    push_cast; linarith
  · have hN : (3 : ℝ) ≤ ((2 * r ^ 2 - t ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast (show 3 ≤ 2 * r ^ 2 - t ^ 2 by omega)
    have h3 := mul_le_mul_of_nonneg_right hN hB.le
    have hrsP : (r : ℝ) * s ≤ (2 * P j - 1) * s := by
      have : (r : ℝ) + 1 ≤ 2 * P j := by exact_mod_cast (show r + 1 ≤ 2 * P j by omega)
      have := s_pos; nlinarith
    have hX : (r : ℝ) * s + t ≤ 2 * (r * s) + 1 := by linarith
    have := aux3 (B := H j * s + 2 * P j) hP1 hX hrsP (by linarith)
    linarith

/-- The core self-similarity: shifting by `H j` adds exactly `2 P j` to `⌊k √2⌋`
for `1 ≤ r < 2 P j`, `r ≠ P j`. -/
lemma core {j r : ℕ} (hj : 1 ≤ j) (hr1 : 1 ≤ r) (hr2 : r < 2 * P j) (hne : r ≠ P j) :
    fl (H j + r) = fl r + 2 * P j := by
  obtain ⟨ht1, ht2⟩ := fl_spec r
  rcases Nat.mod_two_eq_zero_or_one j with hpar | hpar
  · have hm := core_even hj hr1 hr2 hne hpar
    have h2P : (2 * P j : ℝ) ≤ H j * s := by
      have := le_of_sq (t := 2 * P j) (k := H j) (by have := pell_even hpar; nlinarith)
      push_cast at this; linarith
    push_cast at hm
    exact fl_eq (by push_cast; linarith) (by push_cast; linarith)
  · have hm := core_odd hj hr1 hr2 hne hpar
    have h2P : (H j : ℝ) * s < 2 * P j := by
      have := lt_of_sq (t := 2 * P j) (k := H j) (by have := pell_odd hpar; nlinarith)
      push_cast at this; linarith
    exact fl_eq (by push_cast; linarith) (by push_cast; linarith)

/-! ## partial sums -/

noncomputable def B (m : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 m, σ k

@[simp] lemma B_zero : B 0 = 0 := by simp [B]

lemma B_succ (m : ℕ) : B (m + 1) = B m + σ (m + 1) := by
  unfold B; rw [Finset.sum_Icc_succ_top (by omega)]

lemma σ_shift {j r : ℕ} (hj : 1 ≤ j) (hr1 : 1 ≤ r) (hr2 : r < 2 * P j) (hne : r ≠ P j) :
    σ (H j + r) = σ r := by
  unfold σ; rw [core hj hr1 hr2 hne, pow_add, pow_mul]; simp

lemma e_sq (j : ℕ) : e j * e j = 1 := by unfold e; split_ifs <;> simp

/-- Block recursion. -/
lemma shift {j : ℕ} (hj : 1 ≤ j) : ∀ r, r < 2 * P j →
    B (H j + r) = B (H j) + B r - (if P j ≤ r then 2 * e j else 0) := by
  have hP := P_pos hj
  intro r
  induction r with
  | zero => intro _; simp; omega
  | succ r ih =>
    intro hr
    have ih' := ih (by omega)
    rw [← add_assoc, B_succ, B_succ, ih']
    by_cases hrp : r + 1 = P j
    · have h1 : H j + r + 1 = P (j + 1) := by rw [P_succ]; omega
      rw [h1, σ_P (by omega), e_succ, hrp, σ_P hj]
      have : ¬ P j ≤ r := by omega
      rw [if_neg this, if_pos (by omega)]; ring
    · rw [show H j + r + 1 = H j + (r + 1) by ring, σ_shift hj (by omega) hr hrp]
      by_cases h : P j ≤ r
      · rw [if_pos h, if_pos (by omega)]; ring
      · rw [if_neg h, if_neg (by omega)]; ring

lemma shift_lo {j r : ℕ} (hj : 1 ≤ j) (hr : r < P j) : B (H j + r) = B (H j) + B r := by
  rw [shift hj r (by omega), if_neg (by omega)]; ring

lemma shift_hi {j r : ℕ} (hj : 1 ≤ j) (hr1 : P j ≤ r) (hr : r < 2 * P j) :
    B (H j + r) = B (H j) + B r - 2 * e j := by
  rw [shift hj r hr, if_pos hr1]

lemma H_one : H 1 = 1 := rfl
lemma P_one : P 1 = 1 := rfl
lemma H_two : H 2 = 3 := rfl
lemma P_two : P 2 = 2 := rfl

lemma BH_step (k : ℕ) (h1 : B (H (k + 1)) = e (k + 1)) (h0 : B (H k - 1) = 0) :
    B (H (k + 2)) = e (k + 2) := by
  have hPk := P_pos (j := k + 1) (by omega)
  have hHk := H_pos k
  have hP1 : P (k + 1) = H k + P k := P_succ k
  have hH1 : H (k + 1) = H k + 2 * P k := H_succ k
  have hH2 : H (k + 2) = H (k + 1) + 2 * P (k + 1) := H_succ (k + 1)
  have eq1 : H (k + 2) = (H (k + 1) + (2 * P (k + 1) - 1)) + 1 := by omega
  rw [eq1, B_succ, ← eq1, σ_H (by omega), shift_hi (by omega) (by omega) (by omega), h1]
  have eq2 : 2 * P (k + 1) - 1 = H (k + 1) + (H k - 1) := by omega
  rw [eq2, shift_lo (by omega) (by omega), h1, h0]
  have := e_succ (k + 1)
  rw [show k + 1 + 1 = k + 2 by ring] at this
  linarith

lemma BH_pair (k : ℕ) : B (H k - 1) = 0 ∧ B (H (k + 1)) = e (k + 1) := by
  induction k with
  | zero =>
    refine ⟨by simp, ?_⟩
    have h := σ_H (j := 1) le_rfl
    rw [H_one] at h
    have h2 := B_succ 0
    simp only [B_zero, zero_add] at h2
    show B (H 1) = e 1
    rw [H_one, h2, h]
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨?_, BH_step k h1 h0⟩
    have hH := H_pos (k + 1)
    have := B_succ (H (k + 1) - 1)
    rw [Nat.sub_add_cancel hH, h1, σ_H (by omega)] at this
    linarith

lemma BH {j : ℕ} (hj : 1 ≤ j) : B (H j) = e j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact (BH_pair k).2

/-! ## range bounds on the blocks `[0, H j)` -/

def Inv1 (j : ℕ) : Prop := ∀ m < H j, -((j : ℤ) / 2) ≤ B m ∧ B m ≤ ((j : ℤ) - 1) / 2
def Inv2 (j : ℕ) : Prop :=
  ∀ m, P j ≤ m → m < H j → -(((j : ℤ) - 1) / 2) ≤ B m ∧ B m ≤ ((j : ℤ) - 2) / 2

lemma e_cases (j : ℕ) : (e j = 1 ∧ j % 2 = 0) ∨ (e j = -1 ∧ j % 2 = 1) := by
  unfold e; split_ifs with h
  · left; exact ⟨rfl, h⟩
  · right; exact ⟨rfl, by omega⟩

lemma inv_step (k : ℕ) (hA : Inv1 (k + 1)) (hB1 : Inv1 (k + 2)) (hB2 : Inv2 (k + 2)) :
    Inv1 (k + 3) ∧ Inv2 (k + 3) := by
  have hH3 : H (k + 3) = H (k + 2) + 2 * P (k + 2) := H_succ (k + 2)
  have hP3 : P (k + 3) = H (k + 2) + P (k + 2) := P_succ (k + 2)
  have hH2 : H (k + 2) = H (k + 1) + 2 * P (k + 1) := H_succ (k + 1)
  have hP2 : P (k + 2) = H (k + 1) + P (k + 1) := P_succ (k + 1)
  have hPH := P_le_H (k + 1)
  have hBJ := BH (j := k + 2) (by omega)
  have he := e_cases (k + 2)
  -- the upper half `[H J + P J, H J + 2 P J)`
  have claim : ∀ r, P (k + 2) ≤ r → r < 2 * P (k + 2) →
      -((((k + 3 : ℕ) : ℤ) - 1) / 2) ≤ B (H (k + 2) + r) ∧
        B (H (k + 2) + r) ≤ (((k + 3 : ℕ) : ℤ) - 2) / 2 := by
    intro r hr1 hr2
    rw [shift_hi (by omega) hr1 hr2, hBJ]
    by_cases hrH : r < H (k + 2)
    · have := hB2 r hr1 hrH
      push_cast at this ⊢
      omega
    · obtain ⟨r', rfl⟩ : ∃ r', r = H (k + 2) + r' := ⟨r - H (k + 2), by omega⟩
      rw [shift_lo (by omega) (by omega), hBJ]
      have := hA r' (by omega)
      push_cast at this ⊢
      omega
  refine ⟨?_, ?_⟩
  · intro m hm
    by_cases h1 : m < H (k + 2)
    · have := hB1 m h1
      push_cast at this ⊢
      omega
    · obtain ⟨r, rfl⟩ : ∃ r, m = H (k + 2) + r := ⟨m - H (k + 2), by omega⟩
      by_cases h2 : r < P (k + 2)
      · rw [shift_lo (by omega) h2, hBJ]
        have := hB1 r (by have := P_le_H (k + 2); omega)
        push_cast at this ⊢
        omega
      · have := claim r (by omega) (by omega)
        push_cast at this ⊢
        omega
  · intro m hm1 hm2
    obtain ⟨r, rfl⟩ : ∃ r, m = H (k + 2) + r := ⟨m - H (k + 2), by omega⟩
    exact claim r (by omega) (by omega)

lemma B_one : B 1 = -1 := by
  have h := BH (j := 1) le_rfl
  rw [H_one] at h; rw [h]; rfl

lemma B_two : B 2 = 0 := by
  have h := shift_hi (j := 1) (r := 1) le_rfl (by rw [P_one]) (by rw [P_one]; norm_num)
  rw [H_one, B_one] at h
  rw [show (2 : ℕ) = 1 + 1 by rfl, h]; simp [e]

lemma inv_all (k : ℕ) : Inv1 (k + 1) ∧ Inv1 (k + 2) ∧ Inv2 (k + 2) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro m hm; rw [H_one] at hm
      obtain rfl : m = 0 := by omega
      simp
    · intro m hm; rw [H_two] at hm
      rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with rfl | rfl | rfl
      · simp
      · rw [B_one]; norm_num
      · rw [B_two]; norm_num
    · intro m hm1 hm2; rw [H_two] at hm2; rw [P_two] at hm1
      obtain rfl : m = 2 := by omega
      rw [B_two]; norm_num
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    obtain ⟨h4, h5⟩ := inv_step k h1 h2 h3
    exact ⟨h2, h4, h5⟩

lemma inv1 {j : ℕ} (hj : 1 ≤ j) : Inv1 j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact (inv_all k).1

/-! ## first hitting times -/

def A : ℕ → ℕ
  | 0 => 0
  | n + 1 => H (2 * n + 2) + A n

lemma A_succ (n : ℕ) : A (n + 1) = H (2 * n + 2) + A n := rfl

lemma H2' (k : ℕ) : H (k + 2) = 2 * H (k + 1) + H k := by
  have h1 : H (k + 1) = H k + 2 * P k := H_succ k
  have h2 : H (k + 2) = H (k + 1) + 2 * P (k + 1) := H_succ (k + 1)
  have p1 : P (k + 1) = H k + P k := P_succ k
  omega

lemma A_H (n : ℕ) : 2 * A n + 1 = H (2 * n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [A_succ, show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring, H2' (2 * n + 1),
      show 2 * n + 1 + 1 = 2 * n + 2 by ring]
    omega

lemma A_lt_P (n : ℕ) : A n < P (2 * n + 2) := by
  have h := A_H n
  have : P (2 * n + 2) = H (2 * n + 1) + P (2 * n + 1) := P_succ (2 * n + 1)
  omega

lemma e_even (n : ℕ) : e (2 * n + 2) = 1 := by
  unfold e; rw [if_pos (by omega)]

lemma A_hit (n : ℕ) : B (A n) = n ∧ ∀ m < A n, B m < n := by
  induction n with
  | zero => exact ⟨by simp [A], fun m hm => by simp [A] at hm⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have hj : 1 ≤ 2 * n + 2 := by omega
    refine ⟨?_, ?_⟩
    · rw [A_succ, shift_lo hj (A_lt_P n), BH hj, e_even, h1]; push_cast; ring
    · intro m hm
      rw [A_succ] at hm
      by_cases hmH : m < H (2 * n + 2)
      · have := (inv1 hj m hmH).2
        push_cast at this ⊢
        omega
      · obtain ⟨r, rfl⟩ : ∃ r, m = H (2 * n + 2) + r := ⟨m - H (2 * n + 2), by omega⟩
        have hr : r < A n := by omega
        rw [shift_lo hj (by have := A_lt_P n; omega), BH hj, e_even]
        have := h2 r hr
        push_cast; omega

lemma A_rec (n : ℕ) : (A (n + 2) : ℤ) = 6 * A (n + 1) - A n + 2 := by
  rw [A_succ (n + 1), A_succ n]
  have h1 := H2' (2 * n + 2)
  have h2 := H2' (2 * n + 1)
  have h3 := A_H n
  rw [show 2 * (n + 1) + 2 = 2 * n + 2 + 2 by ring, show 2 * n + 2 + 1 = 2 * n + 1 + 2 by ring]
    at *
  rw [show 2 * n + 1 + 1 = 2 * n + 2 by ring] at *
  push_cast
  omega

lemma a_eq (n : ℕ) : S_oeis_a001652.a n = A n ∧ S_oeis_a001652.a (n + 1) = A (n + 1) := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    show 6 * S_oeis_a001652.a (n + 1) - S_oeis_a001652.a n + 2 = _
    rw [ih.1, ih.2, A_rec]

end OMA.A1652

theorem OMA.solution : type_of% @OMA.S_oeis_a001652.main := by
  intro n hn
  rw [(OMA.A1652.a_eq n).1, Int.toNat_natCast]
  have hb : ∀ m, OMA.S_oeis_a001652.b m = OMA.A1652.B m := fun m => rfl
  obtain ⟨h1, h2⟩ := OMA.A1652.A_hit n
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [OMA.A1652.A_succ]; have := OMA.A1652.H_pos (2 * k + 2); push_cast; omega
  · rw [hb, h1]
  · intro m _ hm
    rw [hb]; have := h2 m hm; omega
