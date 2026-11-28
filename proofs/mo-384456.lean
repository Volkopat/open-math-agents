import OMAStatements.S_mo_384456

/-!
# A refinement of Simmons' inequality (MathOverflow 384456)

For `X ∼ Bin(n, m / n)` with `n > 2 m` put `α i = P(X ≤ m - i) - P(X ≥ m + i)`. Then
`∑_{i=1}^{k} α i ≥ 0` for every `k ≤ m` (Conjecture 4.2 of Fokkink, Papavassiliou and Pelekis,
arXiv 2011.11795).

Proof. Let `d j = P(X = m - j) - P(X = m + j)` for `j ≥ 1`, with `P(X = l) = 0` for `l < 0`.

* `α i = ∑_{j ≥ i} d j`, hence `∑_{i=1}^{k} α i = ∑_j min(j, k) d j` (`tail_eq`, `dsum`).
* The mean of `X` is `m`, hence `∑_j j d j = 0` (`dd_mean`).
* `d` changes sign once: `d j ≥ 0` for `j < J` and `d j ≤ 0` for `j ≥ J` (`single_crossing`). Indeed, the
  ratio of `P(X = m + i) / P(X = m - i)` at `i + 1` and at `i` equals `Uc i / Vc i`; it increases with `i`
  and is below one at `i = 0`, so `P(X = m + i) / P(X = m - i)` first decreases from the value one and then
  increases.
* Therefore `J ∑_j min(j, k) d j = ∑_j (J min(j, k) - min(J, k) j) d j`, and every term is nonnegative,
  because `min(j, k) / j` does not increase with `j` (`sc_lemma`).
-/

open Finset

namespace OMA

/-- A sequence that is nonnegative before `J` and nonpositive from `J` on, with vanishing first moment,
has nonnegative sums against `min j k`. -/
lemma sc_lemma (N J : ℕ) (hJ : 1 ≤ J) (d : ℕ → ℝ)
    (h1 : ∀ j, 1 ≤ j → j < J → 0 ≤ d j) (h2 : ∀ j, J ≤ j → d j ≤ 0)
    (h0 : ∑ j ∈ Icc 1 N, (j : ℝ) * d j = 0) (k : ℕ) :
    0 ≤ ∑ j ∈ Icc 1 N, ((min j k : ℕ) : ℝ) * d j := by
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  have key : (J : ℝ) * ∑ j ∈ Icc 1 N, ((min j k : ℕ) : ℝ) * d j =
      ∑ j ∈ Icc 1 N, ((J : ℝ) * (min j k : ℕ) - (min J k : ℕ) * j) * d j := by
    have : ∑ j ∈ Icc 1 N, ((J : ℝ) * (min j k : ℕ) - (min J k : ℕ) * j) * d j =
        (J : ℝ) * ∑ j ∈ Icc 1 N, ((min j k : ℕ) : ℝ) * d j -
          (min J k : ℕ) * ∑ j ∈ Icc 1 N, (j : ℝ) * d j := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, h0, mul_zero, sub_zero]
  have nn : 0 ≤ ∑ j ∈ Icc 1 N, ((J : ℝ) * (min j k : ℕ) - (min J k : ℕ) * j) * d j := by
    refine Finset.sum_nonneg fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    rcases lt_or_ge j J with hjJ | hjJ
    · refine mul_nonneg ?_ (h1 j hj.1 hjJ)
      have hnat : min J k * j ≤ J * min j k := by
        rcases le_total j k with h | h
        · rw [min_eq_left h]; exact Nat.mul_le_mul_right j (min_le_left J k)
        · rw [min_eq_right h, min_eq_right (le_trans h hjJ.le), mul_comm]
          exact Nat.mul_le_mul_right k hjJ.le
      have : ((min J k : ℕ) : ℝ) * j ≤ (J : ℝ) * (min j k : ℕ) := by exact_mod_cast hnat
      linarith
    · refine mul_nonneg_of_nonpos_of_nonpos ?_ (h2 j hjJ)
      have hnat : J * min j k ≤ min J k * j := by
        rcases le_total J k with h | h
        · rw [min_eq_left h]; exact Nat.mul_le_mul_left J (min_le_left j k)
        · rw [min_eq_right h, min_eq_right (le_trans h hjJ), mul_comm]
          exact Nat.mul_le_mul_left k hjJ
      have : (J : ℝ) * (min j k : ℕ) ≤ ((min J k : ℕ) : ℝ) * j := by exact_mod_cast hnat
      linarith
  rw [← key] at nn
  exact (mul_nonneg_iff_of_pos_left hJ').1 nn

/-- exchanging the order of summation in the sum of the tails -/
lemma dsum (N : ℕ) (d : ℕ → ℝ) (k : ℕ) :
    ∑ i ∈ Icc 1 k, ∑ j ∈ Icc i N, d j = ∑ j ∈ Icc 1 N, ((min j k : ℕ) : ℝ) * d j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have e : ∑ j ∈ Icc (k + 1) N, d j = ∑ j ∈ Icc 1 N, (if k + 1 ≤ j then d j else 0) := by
      rw [← Finset.sum_filter]
      congr 1
      ext j
      simp only [Finset.mem_Icc, Finset.mem_filter]
      omega
    rw [e, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · have : min j (k + 1) = min j k + 1 := by omega
      rw [this]; push_cast; ring
    · have : min j (k + 1) = min j k := by omega
      rw [this]; ring


section binom

/-- the binomial probabilities with `n` trials and mean `m` -/
noncomputable def bp (n m l : ℕ) : ℝ :=
  (n.choose l : ℝ) * ((m : ℝ) / n) ^ l * (1 - (m : ℝ) / n) ^ (n - l)

variable {n m : ℕ}

lemma p_pos (hm : 0 < m) (hn : 2 * m < n) : 0 < (m : ℝ) / n := by
  have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have : (0 : ℝ) < m := by exact_mod_cast hm
  positivity

lemma q_pos (hn : 2 * m < n) : 0 < 1 - (m : ℝ) / n := by
  have h1 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h2 : (m : ℝ) < n := by exact_mod_cast (by omega : m < n)
  rw [sub_pos, div_lt_one h1]
  exact h2

lemma bp_pos (hm : 0 < m) (hn : 2 * m < n) {l : ℕ} (hl : l ≤ n) : 0 < bp n m l := by
  have hc : (0 : ℝ) < (n.choose l : ℝ) := by exact_mod_cast Nat.choose_pos hl
  have := p_pos hm hn
  have := q_pos hn
  unfold bp
  positivity

lemma bp_zero {l : ℕ} (hl : n < l) : bp n m l = 0 := by
  simp [bp, Nat.choose_eq_zero_of_lt hl]

lemma bp_nonneg (hm : 0 < m) (hn : 2 * m < n) (l : ℕ) : 0 ≤ bp n m l := by
  rcases le_or_gt l n with h | h
  · exact (bp_pos hm hn h).le
  · rw [bp_zero h]

/-- the step relation between consecutive binomial probabilities -/
lemma bp_step {l : ℕ} (hl : l < n) :
    bp n m (l + 1) * (l + 1) * (1 - (m : ℝ) / n) = bp n m l * (n - l) * ((m : ℝ) / n) := by
  have hc : (n.choose (l + 1) : ℝ) * (l + 1) = (n.choose l : ℝ) * (n - l) := by
    have := Nat.choose_succ_right_eq n l
    have h2 : ((n - l : ℕ) : ℝ) = (n : ℝ) - l := Nat.cast_sub hl.le
    rw [← h2]
    exact_mod_cast this
  rw [bp, bp, pow_succ, show n - l = (n - (l + 1)) + 1 by omega, pow_succ]
  linear_combination ((m : ℝ) / n) ^ l * ((m : ℝ) / n) * (1 - (m : ℝ) / n) ^ (n - (l + 1)) *
    (1 - (m : ℝ) / n) * hc

lemma bp_sum : ∑ l ∈ range (n + 1), bp n m l = 1 := by
  have h := add_pow ((m : ℝ) / n) (1 - (m : ℝ) / n) n
  rw [show (m : ℝ) / n + (1 - (m : ℝ) / n) = 1 by ring, one_pow] at h
  rw [h]
  exact Finset.sum_congr rfl fun l _ => by rw [bp]; ring

lemma bp_mean (hn : 2 * m < n) : ∑ l ∈ range (n + 1), (l : ℝ) * bp n m l = m := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set E := ∑ l ∈ range (n + 1), (l : ℝ) * bp n m l with hE
  have e1 : E = ∑ l ∈ range n, ((l : ℝ) + 1) * bp n m (l + 1) := by
    rw [hE, Finset.sum_range_succ']
    simp
  have e2 : (1 - (m : ℝ) / n) * E = ((m : ℝ) / n) * ∑ l ∈ range n, bp n m l * ((n : ℝ) - l) := by
    rw [e1, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.mem_range] at hl
    have := bp_step (m := m) hl
    linarith
  have e3 : ∑ l ∈ range n, bp n m l = 1 - bp n m n := by
    have := bp_sum (n := n) (m := m)
    rw [Finset.sum_range_succ] at this
    linarith
  have e4 : ∑ l ∈ range n, (l : ℝ) * bp n m l = E - n * bp n m n := by
    rw [hE, Finset.sum_range_succ]
    ring
  have e5 : ∑ l ∈ range n, bp n m l * ((n : ℝ) - l) = n - E := by
    have : ∑ l ∈ range n, bp n m l * ((n : ℝ) - l) =
        n * ∑ l ∈ range n, bp n m l - ∑ l ∈ range n, (l : ℝ) * bp n m l := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [this, e3, e4]
    ring
  rw [e5] at e2
  have : E = (m : ℝ) / n * n := by linarith
  rw [this]
  field_simp

end binom

section crossing

variable {n m : ℕ}

/-- numerator and denominator of the ratio of consecutive ratios `P(X = m + i) / P(X = m - i)` -/
noncomputable def Uc (n m i : ℕ) : ℝ :=
  ((n : ℝ) - m - i) * ((n : ℝ) - m + i + 1) * ((m : ℝ) / n) ^ 2

noncomputable def Vc (n m i : ℕ) : ℝ :=
  ((m : ℝ) + i + 1) * ((m : ℝ) - i) * (1 - (m : ℝ) / n) ^ 2

lemma Vc_pos (hn : 2 * m < n) {i : ℕ} (hi : i < m) : 0 < Vc n m i := by
  have h1 : (0 : ℝ) < (m : ℝ) - i := by
    have : (i : ℝ) < m := by exact_mod_cast hi
    linarith
  have h2 : (0 : ℝ) < (m : ℝ) + i + 1 := by positivity
  have := q_pos hn
  unfold Vc
  positivity

lemma Uc_nonneg (hn : 2 * m < n) {i : ℕ} (hi : i < m) : 0 ≤ Uc n m i := by
  have h1 : (0 : ℝ) ≤ (n : ℝ) - m - i := by
    have : ((m + i : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : m + i ≤ n)
    push_cast at this
    linarith
  have h2 : (0 : ℝ) ≤ (n : ℝ) - m + i + 1 := by
    have : (m : ℝ) ≤ n := by exact_mod_cast (by omega : m ≤ n)
    have : (0 : ℝ) ≤ i := by positivity
    linarith
  unfold Uc
  positivity

/-- the ratios `Uc / Vc` increase -/
lemma UV_mono (hn : 2 * m < n) {i j : ℕ} (hij : i ≤ j) :
    Uc n m i * Vc n m j ≤ Uc n m j * Vc n m i := by
  have hi : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hnm : (2 : ℝ) * m ≤ n := by exact_mod_cast hn.le
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hi0 : (0 : ℝ) ≤ i := by positivity
  have key : Uc n m j * Vc n m i - Uc n m i * Vc n m j =
      ((m : ℝ) / n) ^ 2 * (1 - (m : ℝ) / n) ^ 2 *
        ((((n : ℝ) - 2 * m) * ((n : ℝ) + 1)) * (((j : ℝ) - i) * ((j : ℝ) + i + 1))) := by
    simp only [Uc, Vc]
    ring
  have h1 : (0 : ℝ) ≤ ((n : ℝ) - 2 * m) * ((n : ℝ) + 1) := mul_nonneg (by linarith) (by linarith)
  have h2 : (0 : ℝ) ≤ ((j : ℝ) - i) * ((j : ℝ) + i + 1) := mul_nonneg (by linarith) (by linarith)
  have : 0 ≤ Uc n m j * Vc n m i - Uc n m i * Vc n m j := by
    rw [key]
    positivity
  linarith

/-- the first ratio is below one -/
lemma UV_init (hm : 0 < m) (hn : 2 * m < n) : Uc n m 0 < Vc n m 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hnm : (2 : ℝ) * m < n := by exact_mod_cast hn
  have key : Vc n m 0 - Uc n m 0 = (m : ℝ) * ((n : ℝ) - m) * ((n : ℝ) - 2 * m) / (n : ℝ) ^ 2 := by
    simp only [Uc, Vc]
    field_simp
    ring
  have : 0 < Vc n m 0 - Uc n m 0 := by
    rw [key]
    have : (0 : ℝ) < (n : ℝ) - m := by linarith
    have : (0 : ℝ) < (n : ℝ) - 2 * m := by linarith
    positivity
  linarith

/-- the cross relation between the two sides of the mean -/
lemma cross_step (hn : 2 * m < n) {i : ℕ} (hi : i < m) :
    bp n m (m + (i + 1)) * bp n m (m - i) * Vc n m i =
      bp n m (m + i) * bp n m (m - (i + 1)) * Uc n m i := by
  have E1 := bp_step (n := n) (m := m) (l := m + i) (by omega)
  have E2 := bp_step (n := n) (m := m) (l := m - (i + 1)) (by omega)
  rw [show m - (i + 1) + 1 = m - i by omega] at E2
  have c1 : ((m + i : ℕ) : ℝ) = (m : ℝ) + i := by push_cast; ring
  have c2 : ((m - (i + 1) : ℕ) : ℝ) = (m : ℝ) - i - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [c1] at E1
  rw [c2] at E2
  rw [show m + (i + 1) = m + i + 1 by omega]
  simp only [Uc, Vc]
  linear_combination (bp n m (m - i) * ((m : ℝ) - i) * (1 - (m : ℝ) / n)) * E1 +
    (bp n m (m + i) * ((n : ℝ) - m - i) * ((m : ℝ) / n)) * E2

/-- while the ratio is below one, the left side dominates strictly -/
lemma left_wins (hm : 0 < m) (hn : 2 * m < n) : ∀ t, t < m → Uc n m t < Vc n m t →
    bp n m (m + (t + 1)) < bp n m (m - (t + 1)) := by
  intro t
  induction t with
  | zero =>
    intro ht hUV
    have hc := cross_step hn ht
    simp only [Nat.sub_zero, Nat.add_zero] at hc
    have hb := bp_pos hm hn (l := m) (by omega)
    have hL := bp_pos hm hn (l := m - (0 + 1)) (by omega)
    have hV := Vc_pos hn ht
    have h1 : bp n m (m + (0 + 1)) * Vc n m 0 = bp n m (m - (0 + 1)) * Uc n m 0 := by
      have : bp n m m * (bp n m (m + (0 + 1)) * Vc n m 0) =
          bp n m m * (bp n m (m - (0 + 1)) * Uc n m 0) := by linarith
      exact mul_left_cancel₀ hb.ne' this
    have h2 : bp n m (m - (0 + 1)) * Uc n m 0 < bp n m (m - (0 + 1)) * Vc n m 0 :=
      mul_lt_mul_of_pos_left hUV hL
    have h3 : bp n m (m + (0 + 1)) * Vc n m 0 < bp n m (m - (0 + 1)) * Vc n m 0 := by linarith
    exact lt_of_mul_lt_mul_right h3 hV.le
  | succ t ih =>
    intro ht hUV
    have ht' : t < m := by omega
    have hVt := Vc_pos hn ht'
    have hVt1 := Vc_pos hn ht
    have hmono := UV_mono hn (Nat.le_succ t)
    have hUVt : Uc n m t < Vc n m t := by
      have : Uc n m t * Vc n m (t + 1) < Vc n m t * Vc n m (t + 1) := by
        calc Uc n m t * Vc n m (t + 1) ≤ Uc n m (t + 1) * Vc n m t := hmono
          _ < Vc n m (t + 1) * Vc n m t := mul_lt_mul_of_pos_right hUV hVt
          _ = Vc n m t * Vc n m (t + 1) := mul_comm _ _
      exact lt_of_mul_lt_mul_right this hVt1.le
    have hIH := ih ht' hUVt
    have hc := cross_step hn ht
    have hL1 := bp_pos hm hn (l := m - (t + 1)) (by omega)
    have hL2 := bp_pos hm hn (l := m - (t + 1 + 1)) (by omega)
    have hU := Uc_nonneg hn ht
    have h1 : bp n m (m + (t + 1)) * bp n m (m - (t + 1 + 1)) * Uc n m (t + 1) ≤
        bp n m (m - (t + 1)) * bp n m (m - (t + 1 + 1)) * Uc n m (t + 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hIH.le hL2.le) hU
    have h2 : bp n m (m - (t + 1)) * bp n m (m - (t + 1 + 1)) * Uc n m (t + 1) <
        bp n m (m - (t + 1)) * bp n m (m - (t + 1 + 1)) * Vc n m (t + 1) :=
      mul_lt_mul_of_pos_left hUV (mul_pos hL1 hL2)
    have h3 : bp n m (m - (t + 1)) * (bp n m (m + (t + 1 + 1)) * Vc n m (t + 1)) <
        bp n m (m - (t + 1)) * (bp n m (m - (t + 1 + 1)) * Vc n m (t + 1)) := by linarith
    have h4 := lt_of_mul_lt_mul_left h3 hL1.le
    exact lt_of_mul_lt_mul_right h4 hVt1.le

/-- once the right side is at least the left side, it stays so -/
lemma right_persists (hm : 0 < m) (hn : 2 * m < n) {t : ℕ} (ht : t + 1 < m)
    (h : bp n m (m - (t + 1)) ≤ bp n m (m + (t + 1))) :
    bp n m (m - (t + 1 + 1)) ≤ bp n m (m + (t + 1 + 1)) := by
  have ht' : t < m := by omega
  have hVt := Vc_pos hn ht'
  have hVt1 := Vc_pos hn ht
  have hUV : Vc n m t ≤ Uc n m t := by
    by_contra hcon
    exact absurd (left_wins hm hn t ht' (not_le.1 hcon)) (not_lt.2 h)
  have hmono := UV_mono hn (Nat.le_succ t)
  have hUV1 : Vc n m (t + 1) ≤ Uc n m (t + 1) := by
    have : Vc n m (t + 1) * Vc n m t ≤ Uc n m (t + 1) * Vc n m t := by
      calc Vc n m (t + 1) * Vc n m t = Vc n m t * Vc n m (t + 1) := mul_comm _ _
        _ ≤ Uc n m t * Vc n m (t + 1) := mul_le_mul_of_nonneg_right hUV hVt1.le
        _ ≤ Uc n m (t + 1) * Vc n m t := hmono
    exact le_of_mul_le_mul_right this hVt
  have hc := cross_step hn ht
  have hL1 := bp_pos hm hn (l := m - (t + 1)) (by omega)
  have hL2 := bp_pos hm hn (l := m - (t + 1 + 1)) (by omega)
  have h1 : bp n m (m - (t + 1)) * bp n m (m - (t + 1 + 1)) * Vc n m (t + 1) ≤
      bp n m (m + (t + 1)) * bp n m (m - (t + 1 + 1)) * Uc n m (t + 1) :=
    mul_le_mul (mul_le_mul_of_nonneg_right h hL2.le) hUV1 hVt1.le
      (mul_nonneg (le_trans hL1.le h) hL2.le)
  have h3 : bp n m (m - (t + 1)) * (bp n m (m - (t + 1 + 1)) * Vc n m (t + 1)) ≤
      bp n m (m - (t + 1)) * (bp n m (m + (t + 1 + 1)) * Vc n m (t + 1)) := by linarith
  have h4 := le_of_mul_le_mul_left h3 hL1
  exact le_of_mul_le_mul_right h4 hVt1

lemma right_persists_all (hm : 0 < m) (hn : 2 * m < n) {i : ℕ} (hi : 1 ≤ i)
    (h : bp n m (m - i) ≤ bp n m (m + i)) : ∀ j, i ≤ j → j ≤ m →
    bp n m (m - j) ≤ bp n m (m + j) := by
  intro j hij
  induction j, hij using Nat.le_induction with
  | base => intro _; exact h
  | succ j hij ih =>
    intro hj
    obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
    exact right_persists hm hn (by omega) (ih (by omega))

/-- the differences `P(X = m - j) - P(X = m + j)` -/
noncomputable def dd (n m j : ℕ) : ℝ := (if j ≤ m then bp n m (m - j) else 0) - bp n m (m + j)

/-- the differences change sign once -/
lemma single_crossing (hm : 0 < m) (hn : 2 * m < n) :
    ∃ J, 1 ≤ J ∧ (∀ j, 1 ≤ j → j < J → 0 ≤ dd n m j) ∧ ∀ j, J ≤ j → dd n m j ≤ 0 := by
  classical
  have hex : ∃ j, 1 ≤ j ∧ dd n m j ≤ 0 := by
    refine ⟨m + 1, by omega, ?_⟩
    have := bp_nonneg hm hn (m + (m + 1))
    simp only [dd, show ¬ (m + 1 ≤ m) by omega, if_false]
    linarith
  have hJ := Nat.find_spec hex
  have hmin : ∀ j, j < Nat.find hex → ¬ (1 ≤ j ∧ dd n m j ≤ 0) := fun j h => Nat.find_min hex h
  generalize Nat.find hex = J at hJ hmin
  refine ⟨J, hJ.1, ?_, ?_⟩
  · intro j hj hjJ
    by_contra hcon
    exact hmin j hjJ ⟨hj, (not_le.1 hcon).le⟩
  · intro j hjJ
    rcases Nat.lt_or_ge m j with hjm | hjm
    · have := bp_nonneg hm hn (m + j)
      simp only [dd, show ¬ (j ≤ m) by omega, if_false]
      linarith
    · have hJm : J ≤ m := le_trans hjJ hjm
      have h1 : bp n m (m - J) ≤ bp n m (m + J) := by
        have := hJ.2
        rw [dd, if_pos hJm] at this
        linarith
      have := right_persists_all hm hn hJ.1 h1 j hjJ hjm
      rw [dd, if_pos hjm]
      linarith

end crossing

section core

variable {n m : ℕ}

/-- partial sums of the binomial probabilities: `P(X < j)` -/
noncomputable def Fb (n m j : ℕ) : ℝ := ∑ l ∈ range j, bp n m l

lemma Fb_big {N : ℕ} (hN : n + 1 ≤ N) : Fb n m N = 1 := by
  rw [Fb, ← bp_sum (n := n) (m := m)]
  symm
  refine Finset.sum_subset (Finset.range_mono hN) fun l hl hl' => ?_
  rw [Finset.mem_range] at hl hl'
  exact bp_zero (by omega)

/-- the tails of the differences are the quantities `α i` of the source -/
lemma tail_eq {i : ℕ} (him : i ≤ m) (hn : 2 * m < n) :
    ∑ j ∈ Icc i n, dd n m j = Fb n m (m - i + 1) - (1 - Fb n m (m + i)) := by
  have hl : ∑ j ∈ Icc i n, (if j ≤ m then bp n m (m - j) else 0) = Fb n m (m - i + 1) := by
    have e1 : ∑ j ∈ Icc i n, (if j ≤ m then bp n m (m - j) else 0) =
        ∑ j ∈ Ico i (m + 1), bp n m (m - j) := by
      rw [← Finset.sum_filter]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [e1, Finset.sum_Ico_reflect (fun l => bp n m l) i (le_refl (m + 1)), Fb,
      show m + 1 - (m + 1) = 0 by omega, show m + 1 - i = m - i + 1 by omega, Finset.range_eq_Ico]
  have hr : ∑ j ∈ Icc i n, bp n m (m + j) = 1 - Fb n m (m + i) := by
    have e1 : ∑ j ∈ Icc i n, bp n m (m + j) = ∑ l ∈ Ico (i + m) (n + 1 + m), bp n m l := by
      rw [← Finset.sum_Ico_add' (fun l => bp n m l) i (n + 1) m]
      refine Finset.sum_congr ?_ fun j _ => by rw [add_comm]
      ext j
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    have hbig := Fb_big (n := n) (m := m) (N := n + 1 + m) (by omega)
    rw [Fb] at hbig
    rw [e1, Finset.sum_Ico_eq_sub _ (by omega : i + m ≤ n + 1 + m), hbig, Fb, add_comm i m]
  simp only [dd]
  rw [Finset.sum_sub_distrib, hl, hr]

/-- the first moment of the differences vanishes: the mean of the law is `m` -/
lemma dd_mean (hn : 2 * m < n) : ∑ j ∈ Icc 1 n, (j : ℝ) * dd n m j = 0 := by
  have hl : ∑ j ∈ Icc 1 n, (j : ℝ) * (if j ≤ m then bp n m (m - j) else 0) =
      ∑ l ∈ range m, ((m : ℝ) - l) * bp n m l := by
    have e1 : ∑ j ∈ Icc 1 n, (j : ℝ) * (if j ≤ m then bp n m (m - j) else 0) =
        ∑ j ∈ Ico 1 (m + 1), ((m : ℝ) - ((m - j : ℕ) : ℝ)) * bp n m (m - j) := by
      have : ∀ j ∈ Icc 1 n, (j : ℝ) * (if j ≤ m then bp n m (m - j) else 0) =
          if j ≤ m then ((m : ℝ) - ((m - j : ℕ) : ℝ)) * bp n m (m - j) else 0 := by
        intro j _
        split_ifs with h
        · rw [Nat.cast_sub h]; ring
        · ring
      rw [Finset.sum_congr rfl this, ← Finset.sum_filter]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [e1, Finset.sum_Ico_reflect (fun l : ℕ => ((m : ℝ) - (l : ℝ)) * bp n m l) 1 (le_refl (m + 1)),
      show m + 1 - (m + 1) = 0 by omega, show m + 1 - 1 = m by omega, Finset.range_eq_Ico]
  have hr : ∑ j ∈ Icc 1 n, (j : ℝ) * bp n m (m + j) =
      ∑ l ∈ Ico (m + 1) (n + 1 + m), ((l : ℝ) - m) * bp n m l := by
    rw [show m + 1 = 1 + m by omega,
      ← Finset.sum_Ico_add' (fun l : ℕ => ((l : ℝ) - m) * bp n m l) 1 (n + 1) m]
    refine Finset.sum_congr ?_ fun j _ => ?_
    · ext j
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    · rw [add_comm m j]; push_cast; ring
  have hsplit : ∑ l ∈ range (n + 1 + m), ((m : ℝ) - l) * bp n m l =
      ∑ l ∈ range m, ((m : ℝ) - l) * bp n m l -
        ∑ l ∈ Ico (m + 1) (n + 1 + m), ((l : ℝ) - m) * bp n m l := by
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : m ≤ n + 1 + m),
      Finset.sum_eq_sum_Ico_succ_bot (by omega : m < n + 1 + m)]
    have : ∑ l ∈ Ico (m + 1) (n + 1 + m), ((m : ℝ) - l) * bp n m l =
        -∑ l ∈ Ico (m + 1) (n + 1 + m), ((l : ℝ) - m) * bp n m l := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [this]
    ring
  have htot : ∑ l ∈ range (n + 1 + m), ((m : ℝ) - l) * bp n m l = 0 := by
    have h1 : ∑ l ∈ range (n + 1 + m), bp n m l = 1 := by
      have := Fb_big (n := n) (m := m) (N := n + 1 + m) (by omega)
      rwa [Fb] at this
    have h2 : ∑ l ∈ range (n + 1 + m), (l : ℝ) * bp n m l = m := by
      rw [← bp_mean (n := n) (m := m) hn]
      symm
      refine Finset.sum_subset (Finset.range_mono (by omega)) fun l hl hl' => ?_
      rw [Finset.mem_range] at hl hl'
      rw [bp_zero (by omega), mul_zero]
    have : ∑ l ∈ range (n + 1 + m), ((m : ℝ) - l) * bp n m l =
        m * ∑ l ∈ range (n + 1 + m), bp n m l - ∑ l ∈ range (n + 1 + m), (l : ℝ) * bp n m l := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [this, h1, h2]
    ring
  have : ∑ j ∈ Icc 1 n, (j : ℝ) * dd n m j =
      ∑ j ∈ Icc 1 n, (j : ℝ) * (if j ≤ m then bp n m (m - j) else 0) -
        ∑ j ∈ Icc 1 n, (j : ℝ) * bp n m (m + j) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [dd]; ring
  rw [this, hl, hr, ← hsplit, htot]

/-- **The partial sums of the `α i` are nonnegative.** -/
theorem core (hm : 0 < m) (hn : 2 * m < n) {k : ℕ} (hk : k ≤ m) :
    0 ≤ ∑ i ∈ Icc 1 k, (Fb n m (m - i + 1) - (1 - Fb n m (m + i))) := by
  obtain ⟨J, hJ, h1, h2⟩ := single_crossing hm hn
  have e : ∑ i ∈ Icc 1 k, (Fb n m (m - i + 1) - (1 - Fb n m (m + i))) =
      ∑ i ∈ Icc 1 k, ∑ j ∈ Icc i n, dd n m j := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_Icc] at hi
    exact (tail_eq (by omega) hn).symm
  rw [e, dsum]
  exact sc_lemma n J hJ (dd n m) h1 h2 (dd_mean hn) k

end core

section wrapper

open MeasureTheory

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℕ} {n m : ℕ}

/-- the distribution function of a variable with the binomial law -/
lemma cdf_eq (hX : Measurable X) (hlaw : ∀ j : ℕ, P.real {ω | X ω = j} = bp n m j) (t : ℕ) :
    P.real {ω | X ω < t} = Fb n m t := by
  have h := sum_measureReal_preimage_singleton (μ := P) (range t) (f := X)
    (fun y _ => hX (measurableSet_singleton y))
  have e : X ⁻¹' ↑(range t) = {ω | X ω < t} := by
    ext ω
    simp
  rw [← e, ← h, Fb]
  exact Finset.sum_congr rfl fun l _ => hlaw l

lemma le_eq (hX : Measurable X) (hlaw : ∀ j : ℕ, P.real {ω | X ω = j} = bp n m j) (t : ℕ) :
    P.real {ω | X ω ≤ t} = Fb n m (t + 1) := by
  rw [← cdf_eq hX hlaw (t + 1)]
  congr 1
  ext ω
  exact Nat.lt_succ_iff.symm

lemma ge_eq (hX : Measurable X) (hlaw : ∀ j : ℕ, P.real {ω | X ω = j} = bp n m j) (t : ℕ) :
    P.real {ω | t ≤ X ω} = 1 - Fb n m t := by
  have hmeas : MeasurableSet {ω | X ω < t} := hX measurableSet_Iio
  rw [← cdf_eq hX hlaw t, ← probReal_compl_eq_one_sub hmeas]
  congr 1
  ext ω
  simp

end wrapper

end OMA

/-- **The refinement of Simmons' inequality.** For `X ∼ Bin(n, m / n)` with `n > 2 m`, the partial sums of
`α i = P(X ≤ m - i) - P(X ≥ m + i)` are nonnegative. -/
theorem OMA.solution : type_of% @OMA.S_mo_384456.main := by
  intro n m hm hn _ Ω _ P _ X hX hlaw k hk
  rw [Finset.mem_Icc] at hk
  have hlaw' : ∀ j : ℕ, P.real {ω | X ω = j} = OMA.bp n m j := fun j => hlaw j
  have e : ∑ i ∈ Finset.Icc 1 k, (P.real {ω | X ω ≤ m - i} - P.real {ω | m + i ≤ X ω}) =
      ∑ i ∈ Finset.Icc 1 k, (OMA.Fb n m (m - i + 1) - (1 - OMA.Fb n m (m + i))) :=
    Finset.sum_congr rfl fun i _ => by rw [OMA.le_eq hX hlaw', OMA.ge_eq hX hlaw']
  rw [e]
  exact OMA.core hm hn hk.2
