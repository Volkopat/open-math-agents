import OMAStatements.S_mo_434958

namespace OMA.S_mo_434958

private lemma avg_eq_sum_div {d : ℕ} (f : Cube d → ℝ) :
    avg f = (∑ x : Cube d, f x) / (Fintype.card (Cube d) : ℝ) := by
  simp [avg, Finset.expect_eq_sum_div_card]

private lemma card_cube_pos (d : ℕ) : (0 : ℝ) < (Fintype.card (Cube d) : ℝ) := by
  exact_mod_cast Fintype.card_pos (α := Cube d)

private lemma avg_const {d : ℕ} (c : ℝ) : avg (fun _ : Cube d => c) = c := by
  have hpos : (Fintype.card (Cube d) : ℝ) ≠ 0 := ne_of_gt (card_cube_pos d)
  rw [avg_eq_sum_div, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hpos]

private lemma avg_add {d : ℕ} (f g : Cube d → ℝ) :
    avg (fun x => f x + g x) = avg f + avg g := by
  simp [avg_eq_sum_div, Finset.sum_add_distrib, add_div]

private lemma avg_sub {d : ℕ} (f g : Cube d → ℝ) :
    avg (fun x => f x - g x) = avg f - avg g := by
  simp [avg_eq_sum_div, Finset.sum_sub_distrib, sub_div]

private lemma avg_const_mul {d : ℕ} (c : ℝ) (f : Cube d → ℝ) :
    avg (fun x => c * f x) = c * avg f := by
  simp [avg_eq_sum_div, ← Finset.mul_sum, mul_div_assoc]

private lemma avg_mono {d : ℕ} {f g : Cube d → ℝ} (h : ∀ x, f x ≤ g x) :
    avg f ≤ avg g := by
  rw [avg_eq_sum_div, avg_eq_sum_div]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x) (le_of_lt (card_cube_pos d))

private lemma avg_nonneg {d : ℕ} {f : Cube d → ℝ} (h : ∀ x, 0 ≤ f x) :
    0 ≤ avg f := by
  simpa [avg_const] using avg_mono h

private lemma avg_sq_eq_zero_iff {d : ℕ} (f : Cube d → ℝ) :
    avg (fun x => f x ^ 2) = 0 ↔ ∀ x, f x = 0 := by
  constructor
  · intro h x
    have hpos : (0 : ℝ) < (Fintype.card (Cube d) : ℝ) := card_cube_pos d
    rw [avg_eq_sum_div, div_eq_zero_iff] at h
    have hsum : ∑ y : Cube d, f y ^ 2 = 0 := h.resolve_right (ne_of_gt hpos)
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => sq_nonneg (f y))).mp hsum
    exact sq_eq_zero_iff.mp (hzero x (Finset.mem_univ x))
  · intro h
    simp [avg_eq_sum_div, h]

private lemma avg_mul_sq_le {d : ℕ} (f g : Cube d → ℝ) :
    (avg (fun x => f x * g x)) ^ 2 ≤ avg (fun x => f x ^ 2) * avg (fun x => g x ^ 2) := by
  set A := avg (fun x => f x ^ 2)
  set B := avg (fun x => f x * g x)
  set C := avg (fun x => g x ^ 2)
  have hA : 0 ≤ A := avg_nonneg (fun x => sq_nonneg (f x))
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · have hf : ∀ x, f x = 0 := (avg_sq_eq_zero_iff f).mp hA0.symm
    have hB : B = 0 := by simp [B, avg_eq_sum_div, hf]
    rw [hB, ← hA0]
    simp
  · set t := -B / A
    have hquad : 0 ≤ avg (fun x => (t * f x + g x) ^ 2) :=
      avg_nonneg (fun x => sq_nonneg _)
    have hexpand : avg (fun x => (t * f x + g x) ^ 2) = t ^ 2 * A + 2 * t * B + C := by
      have h1 : (fun x => (t * f x + g x) ^ 2) =
          fun x => (t ^ 2 * f x ^ 2 + (2 * t) * (f x * g x)) + g x ^ 2 := by
        ext x; ring
      rw [h1, avg_add, avg_add, avg_const_mul, avg_const_mul]
    rw [hexpand] at hquad
    have hmul : 0 ≤ A * (t ^ 2 * A + 2 * t * B + C) := mul_nonneg (le_of_lt hApos) hquad
    have hsimp : A * (t ^ 2 * A + 2 * t * B + C) = A * C - B ^ 2 := by
      dsimp [t]
      field_simp [ne_of_gt hApos]
      ring
    linarith

private lemma avg_zero (f : Cube 0 → ℝ) : avg f = f Fin.elim0 := by
  rw [avg_eq_sum_div]
  have hcard : Fintype.card (Cube 0) = 1 := by simp [Cube]
  have huniv : (Finset.univ : Finset (Cube 0)) = {Fin.elim0} := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    ext i
    exact Fin.elim0 i
  rw [huniv, Finset.sum_singleton, hcard]
  simp

private lemma avg_succ {d : ℕ} (f : Cube (d + 1) → ℝ) :
    avg f =
      (avg (fun x : Cube d => f (Fin.cons true x)) +
        avg (fun x : Cube d => f (Fin.cons false x))) / 2 := by
  rw [avg_eq_sum_div, avg_eq_sum_div, avg_eq_sum_div]
  have hsum :
      ∑ x : Cube (d + 1), f x =
        (∑ x : Cube d, f (Fin.cons true x)) + ∑ x : Cube d, f (Fin.cons false x) := by
    let e : Bool × Cube d ≃ Cube (d + 1) := Fin.consEquiv (fun _ : Fin (d + 1) => Bool)
    rw [← Fintype.sum_equiv e (fun p => f (Fin.cons p.1 p.2)) f (fun p => rfl)]
    rw [Fintype.sum_prod_type]
    simp
  have hcard : (Fintype.card (Cube (d + 1)) : ℝ) = 2 * (Fintype.card (Cube d) : ℝ) := by
    have hc : Fintype.card (Cube (d + 1)) = 2 * Fintype.card (Cube d) := by
      simp [Cube, pow_succ']
    exact_mod_cast hc
  have hpos : (Fintype.card (Cube d) : ℝ) ≠ 0 := ne_of_gt (card_cube_pos d)
  rw [hsum, hcard]
  field_simp [hpos]

private lemma sign_not (b : Bool) : sign (!b) = -sign b := by
  cases b <;> simp [sign]

private lemma sign_sq (b : Bool) : sign b ^ 2 = 1 := by
  cases b <;> simp [sign]

private lemma S_not {d : ℕ} (u : Fin d → ℝ) (x : Cube d) :
    S u (fun i => !x i) = -S u x := by
  simp [S, sign_not, Finset.sum_neg_distrib]

private lemma S_succ {d : ℕ} (u : Fin (d + 1) → ℝ) (b : Bool) (x : Cube d) :
    S u (Fin.cons b x) = u 0 * sign b + S (u ∘ Fin.succ) x := by
  simp [S, Fin.sum_univ_succ]

private lemma avg_not {d : ℕ} (f : Cube d → ℝ) :
    avg (fun x => f (fun i => !x i)) = avg f := by
  rw [avg_eq_sum_div, avg_eq_sum_div]
  congr 1
  let e : Cube d ≃ Cube d :=
    { toFun := fun x i => !x i
      invFun := fun x i => !x i
      left_inv := fun x => by ext i; simp
      right_inv := fun x => by ext i; simp }
  exact Fintype.sum_equiv e (fun x => f (fun i => !x i)) f (fun _ => rfl)

private lemma avg_S_mul_S {d : ℕ} (u v : Fin d → ℝ) :
    avg (fun x => S u x * S v x) = dot u v := by
  induction d with
  | zero =>
    simp [avg_zero, S, dot]
  | succ d ih =>
    rw [avg_succ]
    have hsimp :
        avg (fun x : Cube d => S u (Fin.cons true x) * S v (Fin.cons true x)) +
          avg (fun x : Cube d => S u (Fin.cons false x) * S v (Fin.cons false x)) =
        avg (fun x : Cube d =>
          2 * (u 0 * v 0) + 2 * (S (u ∘ Fin.succ) x * S (v ∘ Fin.succ) x)) := by
      rw [← avg_add]
      congr 1
      ext x
      rw [S_succ, S_succ, S_succ, S_succ]
      simp [sign]
      ring
    rw [hsimp, avg_add, avg_const, avg_const_mul, ih (u ∘ Fin.succ) (v ∘ Fin.succ)]
    simp [dot, Fin.sum_univ_succ]
    ring

private lemma avg_S_sq {d : ℕ} (u : Fin d → ℝ) :
    avg (fun x => S u x ^ 2) = dot u u := by
  simpa [sq] using avg_S_mul_S u u

private lemma avg_affine_pow_four (d : ℕ) (a : ℝ) (u : Fin d → ℝ) :
    avg (fun x => (a + S u x) ^ 4) ≤ 3 * (avg (fun x => (a + S u x) ^ 2)) ^ 2 := by
  induction d generalizing a with
  | zero =>
    have h0 : avg (fun x : Cube 0 => (a + S u x) ^ 4) = a ^ 4 := by
      simp [avg_zero, S]
    have h2 : avg (fun x : Cube 0 => (a + S u x) ^ 2) = a ^ 2 := by
      simp [avg_zero, S]
    rw [h0, h2]
    nlinarith [sq_nonneg (a ^ 2)]
  | succ d ih =>
    set u' : Fin d → ℝ := u ∘ Fin.succ
    set h : ℝ := u 0
    have h2 :
        avg (fun x : Cube (d + 1) => (a + S u x) ^ 2) =
          avg (fun x : Cube d => (a + S u' x) ^ 2) + h ^ 2 := by
      rw [avg_succ]
      have hs :
          avg (fun x : Cube d => (a + S u (Fin.cons true x)) ^ 2) +
            avg (fun x : Cube d => (a + S u (Fin.cons false x)) ^ 2) =
          avg (fun x : Cube d => 2 * (a + S u' x) ^ 2 + 2 * h ^ 2) := by
        rw [← avg_add]
        congr 1
        ext x
        rw [S_succ, S_succ]
        simp [sign, u', h]
        ring
      rw [hs, avg_add, avg_const_mul, avg_const]
      ring
    have h4 :
        avg (fun x : Cube (d + 1) => (a + S u x) ^ 4) =
          avg (fun x : Cube d => (a + S u' x) ^ 4) +
            6 * h ^ 2 * avg (fun x : Cube d => (a + S u' x) ^ 2) + h ^ 4 := by
      rw [avg_succ]
      have hs :
          avg (fun x : Cube d => (a + S u (Fin.cons true x)) ^ 4) +
            avg (fun x : Cube d => (a + S u (Fin.cons false x)) ^ 4) =
          avg (fun x : Cube d =>
            (2 * (a + S u' x) ^ 4 + (12 * h ^ 2) * (a + S u' x) ^ 2) + 2 * h ^ 4) := by
        rw [← avg_add]
        congr 1
        ext x
        rw [S_succ, S_succ]
        simp [sign, u', h]
        ring
      rw [hs, avg_add, avg_add, avg_const_mul, avg_const_mul, avg_const]
      ring
    rw [h2, h4]
    have hih := ih a u'
    nlinarith [sq_nonneg (h ^ 2)]

private lemma avg_quad_pow_four (d : ℕ) (a : ℝ) (v u : Fin d → ℝ) :
    avg (fun x => (a + S v x + S u x ^ 2) ^ 4) ≤
      27 * (avg (fun x => (a + S v x + S u x ^ 2) ^ 2)) ^ 2 := by
  induction d generalizing a with
  | zero =>
    have h0 : avg (fun x : Cube 0 => (a + S v x + S u x ^ 2) ^ 4) = a ^ 4 := by
      simp [avg_zero, S]
    have h2 : avg (fun x : Cube 0 => (a + S v x + S u x ^ 2) ^ 2) = a ^ 2 := by
      simp [avg_zero, S]
    rw [h0, h2]
    nlinarith [sq_nonneg (a ^ 2)]
  | succ d ih =>
    set u' : Fin d → ℝ := u ∘ Fin.succ
    set v' : Fin d → ℝ := v ∘ Fin.succ
    set w : Fin d → ℝ := fun i => 2 * u 0 * u' i
    set g : Cube d → ℝ := fun x => (a + u 0 ^ 2) + S v' x + S u' x ^ 2
    set h : Cube d → ℝ := fun x => v 0 + S w x
    have hsplit : ∀ (b : Bool) (x : Cube d),
        a + S v (Fin.cons b x) + S u (Fin.cons b x) ^ 2 = g x + sign b * h x := by
      intro b x
      have hSw : S w x = 2 * u 0 * S u' x := by
        simp [S, w, Finset.mul_sum, mul_assoc]
      rw [S_succ, S_succ]
      have hsq : sign b ^ 2 = 1 := sign_sq b
      dsimp [g, h, u', v']
      rw [hSw]
      nlinarith [hsq]
    have h2 :
        avg (fun x : Cube (d + 1) => (a + S v x + S u x ^ 2) ^ 2) =
          avg (fun x => g x ^ 2) + avg (fun x => h x ^ 2) := by
      rw [avg_succ]
      have hs :
          avg (fun x : Cube d => (a + S v (Fin.cons true x) + S u (Fin.cons true x) ^ 2) ^ 2) +
            avg (fun x : Cube d =>
              (a + S v (Fin.cons false x) + S u (Fin.cons false x) ^ 2) ^ 2) =
          avg (fun x : Cube d => 2 * g x ^ 2 + 2 * h x ^ 2) := by
        rw [← avg_add]
        congr 1
        ext x
        rw [hsplit true x, hsplit false x]
        simp [sign]
        ring
      rw [hs, avg_add, avg_const_mul, avg_const_mul]
      ring
    have h4 :
        avg (fun x : Cube (d + 1) => (a + S v x + S u x ^ 2) ^ 4) =
          avg (fun x => g x ^ 4) + 6 * avg (fun x => g x ^ 2 * h x ^ 2) +
            avg (fun x => h x ^ 4) := by
      rw [avg_succ]
      have hs :
          avg (fun x : Cube d => (a + S v (Fin.cons true x) + S u (Fin.cons true x) ^ 2) ^ 4) +
            avg (fun x : Cube d =>
              (a + S v (Fin.cons false x) + S u (Fin.cons false x) ^ 2) ^ 4) =
          avg (fun x : Cube d =>
            (2 * g x ^ 4 + 12 * (g x ^ 2 * h x ^ 2)) + 2 * h x ^ 4) := by
        rw [← avg_add]
        congr 1
        ext x
        rw [hsplit true x, hsplit false x]
        simp [sign]
        ring
      rw [hs, avg_add, avg_add, avg_const_mul, avg_const_mul, avg_const_mul]
      ring
    have hg4 : avg (fun x => g x ^ 4) ≤ 27 * (avg (fun x => g x ^ 2)) ^ 2 :=
      ih (a + u 0 ^ 2) v' u'
    have hh4 : avg (fun x => h x ^ 4) ≤ 3 * (avg (fun x => h x ^ 2)) ^ 2 :=
      avg_affine_pow_four d (v 0) w
    have hcs :
        (avg (fun x => g x ^ 2 * h x ^ 2)) ^ 2 ≤
          avg (fun x => g x ^ 4) * avg (fun x => h x ^ 4) := by
      have h0 := avg_mul_sq_le (fun x => g x ^ 2) (fun x => h x ^ 2)
      have h1 : (fun x => (g x ^ 2) ^ 2) = fun x => g x ^ 4 := by ext x; ring
      have h2 : (fun x => (h x ^ 2) ^ 2) = fun x => h x ^ 4 := by ext x; ring
      rwa [h1, h2] at h0
    have hg2_nn : 0 ≤ avg (fun x => g x ^ 2) := avg_nonneg (fun x => sq_nonneg _)
    have hh2_nn : 0 ≤ avg (fun x => h x ^ 2) := avg_nonneg (fun x => sq_nonneg _)
    have hg4_nn : 0 ≤ avg (fun x => g x ^ 4) := avg_nonneg (fun x => by positivity)
    have hh4_nn : 0 ≤ avg (fun x => h x ^ 4) := avg_nonneg (fun x => by positivity)
    have hgh_sq :
        (avg (fun x => g x ^ 2 * h x ^ 2)) ^ 2 ≤
          (9 * avg (fun x => g x ^ 2) * avg (fun x => h x ^ 2)) ^ 2 := by
      calc (avg (fun x => g x ^ 2 * h x ^ 2)) ^ 2
          ≤ avg (fun x => g x ^ 4) * avg (fun x => h x ^ 4) := hcs
        _ ≤ (27 * (avg (fun x => g x ^ 2)) ^ 2) * (3 * (avg (fun x => h x ^ 2)) ^ 2) :=
            mul_le_mul hg4 hh4 hh4_nn (by positivity)
        _ = (9 * avg (fun x => g x ^ 2) * avg (fun x => h x ^ 2)) ^ 2 := by ring
    have hgh : avg (fun x => g x ^ 2 * h x ^ 2) ≤
        9 * avg (fun x => g x ^ 2) * avg (fun x => h x ^ 2) := by
      nlinarith [hgh_sq, mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9) hg2_nn) hh2_nn]
    rw [h2, h4]
    nlinarith [sq_nonneg (avg (fun x => h x ^ 2))]

private noncomputable def sqEvent {d : ℕ} (u : Fin d → ℝ) (t : ℝ) (x : Cube d) : ℝ :=
  if t ^ 2 ≤ S u x ^ 2 then 1 else 0

private lemma sqEvent_sq {d : ℕ} (u : Fin d → ℝ) (t : ℝ) (x : Cube d) :
    sqEvent u t x ^ 2 = sqEvent u t x := by
  unfold sqEvent
  split_ifs <;> norm_num

private lemma event_sq {d : ℕ} (u : Fin d → ℝ) (t : ℝ) (x : Cube d) :
    event u t x ^ 2 = event u t x := by
  unfold event
  split_ifs <;> norm_num

private lemma event_nonneg {d : ℕ} (u : Fin d → ℝ) (t : ℝ) (x : Cube d) :
    0 ≤ event u t x := by
  unfold event
  split_ifs <;> norm_num

private lemma avg_sqEvent_le_two_prob {d : ℕ} (u : Fin d → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    avg (sqEvent u t) ≤ 2 * probability u t := by
  have hpt : ∀ x : Cube d, sqEvent u t x ≤ event u t x + event u t (fun i => !x i) := by
    intro x
    unfold sqEvent event
    rw [S_not]
    by_cases h1 : t ^ 2 ≤ S u x ^ 2
    · rw [if_pos h1]
      by_cases h2 : t ≤ S u x
      · rw [if_pos h2]
        have : 0 ≤ if t ≤ -S u x then (1 : ℝ) else 0 := by split_ifs <;> norm_num
        linarith
      · rw [if_neg h2]
        have h3 : t ≤ -S u x := by
          by_contra hlt
          have ha : S u x < t := lt_of_not_ge h2
          have hb : -S u x < t := lt_of_not_ge hlt
          nlinarith
        rw [if_pos h3]
        norm_num
    · rw [if_neg h1]
      have ha : 0 ≤ if t ≤ S u x then (1 : ℝ) else 0 := by split_ifs <;> norm_num
      have hb : 0 ≤ if t ≤ -S u x then (1 : ℝ) else 0 := by split_ifs <;> norm_num
      linarith
  have havg := avg_mono hpt
  rw [avg_add, avg_not (event u t)] at havg
  simpa [probability, two_mul] using havg

private lemma part1 :
    ∃ u v : Fin 2 → ℝ, dot u u = 1 ∧ dot v v = 1 ∧ dot u v = 16 / 65 ∧
      ∀ t : ℝ, 0 < t → t ≤ 1 / 5 → probability u t = 1 / 2 ∧ conditional u v t = -5 / 13 := by
  let u : Fin 2 → ℝ := ![3 / 5, 4 / 5]
  let v : Fin 2 → ℝ := ![12 / 13, -5 / 13]
  refine ⟨u, v, ?_, ?_, ?_, ?_⟩
  · simp [dot, Fin.sum_univ_two, u]; norm_num
  · simp [dot, Fin.sum_univ_two, v]; norm_num
  · simp [dot, Fin.sum_univ_two, u, v]; norm_num
  · intro t ht0 ht1
    have hS : ∀ (b0 b1 : Bool),
        S u (Fin.cons b0 (Fin.cons b1 Fin.elim0)) = (3 / 5 : ℝ) * sign b0 + (4 / 5 : ℝ) * sign b1 := by
      intro b0 b1
      simp [S, Fin.sum_univ_two, u]
    have hSv : ∀ (b0 b1 : Bool),
        S v (Fin.cons b0 (Fin.cons b1 Fin.elim0)) = (12 / 13 : ℝ) * sign b0 + (-5 / 13 : ℝ) * sign b1 := by
      intro b0 b1
      simp [S, Fin.sum_univ_two, v]
    have hprob : probability u t = 1 / 2 := by
      unfold probability
      rw [avg_succ, avg_succ, avg_succ, avg_zero, avg_zero, avg_zero, avg_zero]
      unfold event
      rw [hS true true, hS true false, hS false true, hS false false]
      simp only [sign, ↓reduceIte, Bool.false_eq_true]
      have h1 : t ≤ (3 / 5 : ℝ) * 1 + 4 / 5 * 1 := by linarith
      have h2 : ¬(t ≤ (3 / 5 : ℝ) * 1 + 4 / 5 * -1) := by linarith
      have h3 : t ≤ (3 / 5 : ℝ) * -1 + 4 / 5 * 1 := by linarith
      have h4 : ¬(t ≤ (3 / 5 : ℝ) * -1 + 4 / 5 * -1) := by linarith
      rw [if_pos h1, if_neg h2, if_pos h3, if_neg h4]
      norm_num
    refine ⟨hprob, ?_⟩
    unfold conditional
    rw [hprob, avg_succ, avg_succ, avg_succ, avg_zero, avg_zero, avg_zero, avg_zero]
    unfold event
    rw [hS true true, hS true false, hS false true, hS false false]
    rw [hSv true true, hSv true false, hSv false true, hSv false false]
    simp only [sign, ↓reduceIte, Bool.false_eq_true]
    have h1 : t ≤ (3 / 5 : ℝ) * 1 + 4 / 5 * 1 := by linarith
    have h2 : ¬(t ≤ (3 / 5 : ℝ) * 1 + 4 / 5 * -1) := by linarith
    have h3 : t ≤ (3 / 5 : ℝ) * -1 + 4 / 5 * 1 := by linarith
    have h4 : ¬(t ≤ (3 / 5 : ℝ) * -1 + 4 / 5 * -1) := by linarith
    rw [if_pos h1, if_neg h2, if_pos h3, if_neg h4]
    norm_num

private lemma part2 :
    ∀ (d : ℕ) (u v : Fin d → ℝ) (c t : ℝ), dot u u = 1 → dot v v = 1 →
      0 ≤ c → c ≤ dot u v → 0 ≤ t → t < 1 →
      (1 - t ^ 2) ^ 2 / 6 ≤ probability u t ∧
      c * t - Real.sqrt (6 * (1 - c ^ 2)) / (1 - t ^ 2) ≤ conditional u v t := by
  intro d u v c t huu hvv hc0 hcr ht0 ht1
  have h1mt2_pos : 0 < 1 - t ^ 2 := by nlinarith
  have hprob : (1 - t ^ 2) ^ 2 / 6 ≤ probability u t := by
    have hpt : ∀ x : Cube d, S u x ^ 2 - t ^ 2 ≤ S u x ^ 2 * sqEvent u t x := by
      intro x
      unfold sqEvent
      split_ifs with h
      · nlinarith
      · linarith
    have havg : 1 - t ^ 2 ≤ avg (fun x => S u x ^ 2 * sqEvent u t x) := by
      have h := avg_mono hpt
      rw [avg_sub, avg_S_sq, avg_const, huu] at h
      exact h
    have hcs :
        (avg (fun x => S u x ^ 2 * sqEvent u t x)) ^ 2 ≤
          avg (fun x => S u x ^ 4) * avg (sqEvent u t) := by
      have h := avg_mul_sq_le (fun x => S u x ^ 2) (sqEvent u t)
      have hsq : (fun x => (S u x ^ 2) ^ 2) = fun x => S u x ^ 4 := by ext x; ring
      have heq : (fun x => sqEvent u t x ^ 2) = sqEvent u t := by ext x; exact sqEvent_sq u t x
      rw [hsq, heq] at h
      exact h
    have h4 : avg (fun x => S u x ^ 4) ≤ 3 := by
      have h := avg_affine_pow_four d 0 u
      simp only [zero_add, avg_S_sq, huu] at h
      linarith
    have hsqE_nn : 0 ≤ avg (sqEvent u t) := avg_nonneg (fun x => by unfold sqEvent; split_ifs <;> norm_num)
    have h2p : avg (sqEvent u t) ≤ 2 * probability u t := avg_sqEvent_le_two_prob u ht0
    have hsq : (1 - t ^ 2) ^ 2 ≤ (avg (fun x => S u x ^ 2 * sqEvent u t x)) ^ 2 := by
      nlinarith
    have hmul : avg (fun x => S u x ^ 4) * avg (sqEvent u t) ≤ 6 * probability u t := by
      nlinarith
    linarith
  refine ⟨hprob, ?_⟩
  set P := probability u t
  have hP_pos : 0 < P := by
    have : 0 < (1 - t ^ 2) ^ 2 / 6 := by positivity
    linarith
  set r := dot u v
  set w : Fin d → ℝ := fun i => v i - r * u i
  have hww : dot w w = 1 - r ^ 2 := by
    have : dot w w = dot v v - 2 * r * dot u v + r ^ 2 * dot u u := by
      simp only [dot, w]
      have h1 : ∀ i, (v i - r * u i) * (v i - r * u i) =
          v i * v i - 2 * r * (u i * v i) + r ^ 2 * (u i * u i) := fun i => by ring
      simp_rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [this, huu, hvv]
    dsimp [r]
    ring
  have hww_nn : 0 ≤ 1 - r ^ 2 := by
    rw [← hww, ← avg_S_sq]
    exact avg_nonneg (fun x => sq_nonneg _)
  have h1mc2_nn : 0 ≤ 1 - c ^ 2 := by nlinarith
  have hSv : ∀ x : Cube d, S v x = r * S u x + S w x := by
    intro x
    simp only [S, w]
    have h1 : ∀ i, (v i - r * u i) * sign (x i) =
        v i * sign (x i) - r * (u i * sign (x i)) := fun i => by ring
    simp_rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hdecomp :
      avg (fun x => S v x * event u t x) =
        r * avg (fun x => S u x * event u t x) + avg (fun x => S w x * event u t x) := by
    have h1 : (fun x => S v x * event u t x) =
        fun x => r * (S u x * event u t x) + S w x * event u t x := by
      ext x
      rw [hSv x]
      ring
    rw [h1, avg_add, avg_const_mul]
  have hterm1 : c * t * P ≤ r * avg (fun x => S u x * event u t x) := by
    have hpt : ∀ x : Cube d, t * event u t x ≤ S u x * event u t x := by
      intro x
      unfold event
      split_ifs with h
      · linarith
      · norm_num
    have havg := avg_mono hpt
    rw [avg_const_mul] at havg
    have hP_nn : 0 ≤ P := le_of_lt hP_pos
    have h1 : c * (t * P) ≤ r * (t * P) :=
      mul_le_mul_of_nonneg_right hcr (mul_nonneg ht0 hP_nn)
    have h2 : r * (t * P) ≤ r * avg (fun x => S u x * event u t x) :=
      mul_le_mul_of_nonneg_left havg (le_trans hc0 hcr)
    linarith
  have hterm2_sq :
      (avg (fun x => S w x * event u t x)) ^ 2 ≤ (1 - c ^ 2) * P := by
    have hcs := avg_mul_sq_le (S w) (event u t)
    have heq : (fun x => event u t x ^ 2) = event u t := by ext x; exact event_sq u t x
    rw [avg_S_sq, hww, heq] at hcs
    have hcr_sq : c ^ 2 ≤ r ^ 2 := by nlinarith
    have hle : (1 - r ^ 2) * P ≤ (1 - c ^ 2) * P :=
      mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hP_pos)
    exact le_trans hcs hle
  have hterm2 : -Real.sqrt ((1 - c ^ 2) * P) ≤ avg (fun x => S w x * event u t x) := by
    have hsq : (avg (fun x => S w x * event u t x)) ^ 2 ≤ (Real.sqrt ((1 - c ^ 2) * P)) ^ 2 := by
      rwa [Real.sq_sqrt (mul_nonneg h1mc2_nn (le_of_lt hP_pos))]
    nlinarith [Real.sqrt_nonneg ((1 - c ^ 2) * P)]
  have hbound_div :
      Real.sqrt ((1 - c ^ 2) * P) / P ≤ Real.sqrt (6 * (1 - c ^ 2)) / (1 - t ^ 2) := by
    have hL_nn : 0 ≤ Real.sqrt ((1 - c ^ 2) * P) / P := by positivity
    have hR_nn : 0 ≤ Real.sqrt (6 * (1 - c ^ 2)) / (1 - t ^ 2) := by positivity
    have hsq :
        (Real.sqrt ((1 - c ^ 2) * P) / P) ^ 2 ≤
          (Real.sqrt (6 * (1 - c ^ 2)) / (1 - t ^ 2)) ^ 2 := by
      rw [div_pow, div_pow, Real.sq_sqrt (mul_nonneg h1mc2_nn (le_of_lt hP_pos)),
        Real.sq_sqrt (by linarith)]
      have hPne : P ≠ 0 := ne_of_gt hP_pos
      have h1ne : (1 - t ^ 2) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos h1mt2_pos)
      rw [div_le_div_iff₀ (sq_pos_of_pos hP_pos) (sq_pos_of_pos h1mt2_pos)]
      nlinarith [hprob, h1mc2_nn, hP_pos]
    nlinarith
  unfold conditional
  change c * t - Real.sqrt (6 * (1 - c ^ 2)) / (1 - t ^ 2) ≤
    avg (fun x => S v x * event u t x) / P
  rw [hdecomp]
  have hstep : c * t - Real.sqrt ((1 - c ^ 2) * P) / P ≤
      (r * avg (fun x => S u x * event u t x) + avg (fun x => S w x * event u t x)) / P := by
    have hnum : c * t * P - Real.sqrt ((1 - c ^ 2) * P) ≤
        r * avg (fun x => S u x * event u t x) + avg (fun x => S w x * event u t x) := by
      linarith
    have hdiv := div_le_div_of_nonneg_right hnum (le_of_lt hP_pos)
    have hPne : P ≠ 0 := ne_of_gt hP_pos
    have hrew : (c * t * P - Real.sqrt ((1 - c ^ 2) * P)) / P =
        c * t - Real.sqrt ((1 - c ^ 2) * P) / P := by
      field_simp [hPne]
    rwa [hrew] at hdiv
  linarith

private lemma part3 :
    ∀ (d : ℕ) (u v : Fin d → ℝ), dot u u = 1 → dot v v = 1 →
      1 / 864 ≤ probability u 1 ∧ -Real.sqrt 864 ≤ conditional u v 1 := by
  intro d u v huu hvv
  have hprob : 1 / 864 ≤ probability u 1 := by
    set Z : Cube d → ℝ := fun x => S u x ^ 2 - 1
    have hZ_avg : avg Z = 0 := by
      change avg (fun x => S u x ^ 2 - 1) = 0
      rw [avg_sub, avg_S_sq, avg_const, huu]
      ring
    have hZ2_nn : 0 ≤ avg (fun x => Z x ^ 2) := avg_nonneg (fun x => sq_nonneg _)
    rcases eq_or_lt_of_le hZ2_nn with hZ2_zero | hZ2_pos
    · have hZ0 : ∀ x, Z x = 0 := (avg_sq_eq_zero_iff Z).mp hZ2_zero.symm
      have hsq1 : ∀ x, sqEvent u 1 x = 1 := by
        intro x
        unfold sqEvent
        have hx : S u x ^ 2 = 1 := by linarith [hZ0 x]
        rw [hx]
        norm_num
      have havg1 : avg (sqEvent u 1) = 1 := by
        have h1 : sqEvent u 1 = fun _ => 1 := funext hsq1
        rw [h1]
        exact avg_const 1
      have h2p := avg_sqEvent_le_two_prob u (by norm_num : (0 : ℝ) ≤ 1)
      linarith
    · set Zpos : Cube d → ℝ := fun x => max (Z x) 0
      set Zabs : Cube d → ℝ := fun x => |Z x|
      have hZabs_eq : ∀ x, Zabs x = 2 * Zpos x - Z x := by
        intro x
        dsimp [Zabs, Zpos]
        rcases le_total 0 (Z x) with h | h
        · rw [abs_of_nonneg h, max_eq_left h]; ring
        · rw [abs_of_nonpos h, max_eq_right h]; ring
      have havg_abs : avg Zabs = 2 * avg Zpos := by
        have h1 : Zabs = fun x => 2 * Zpos x - Z x := funext hZabs_eq
        rw [h1, avg_sub, avg_const_mul, hZ_avg]
        ring
      have hcs1 :
          (avg (fun x => Z x ^ 2)) ^ 2 ≤ avg Zabs * avg (fun x => Zabs x ^ 3) := by
        have h := avg_mul_sq_le (fun x => Real.sqrt (Zabs x))
          (fun x => Zabs x * Real.sqrt (Zabs x))
        have hL : (fun x => Real.sqrt (Zabs x) * (Zabs x * Real.sqrt (Zabs x))) =
            fun x => Z x ^ 2 := by
          ext x
          have hnn : 0 ≤ Zabs x := abs_nonneg (Z x)
          calc Real.sqrt (Zabs x) * (Zabs x * Real.sqrt (Zabs x))
              = Zabs x * (Real.sqrt (Zabs x) * Real.sqrt (Zabs x)) := by ring
            _ = Zabs x * Zabs x := by rw [Real.mul_self_sqrt hnn]
            _ = Z x ^ 2 := by simp [Zabs, sq]
        have hR1 : (fun x => Real.sqrt (Zabs x) ^ 2) = Zabs := by
          ext x
          exact Real.sq_sqrt (abs_nonneg (Z x))
        have hR2 : (fun x => (Zabs x * Real.sqrt (Zabs x)) ^ 2) = fun x => Zabs x ^ 3 := by
          ext x
          rw [mul_pow, Real.sq_sqrt (abs_nonneg (Z x))]
          ring
        rw [hL, hR1, hR2] at h
        exact h
      have hcs2 :
          (avg (fun x => Zabs x ^ 3)) ^ 2 ≤
            avg (fun x => Z x ^ 2) * avg (fun x => Z x ^ 4) := by
        have h := avg_mul_sq_le Zabs (fun x => Z x ^ 2)
        have hL : (fun x => Zabs x * Z x ^ 2) = fun x => Zabs x ^ 3 := by
          ext x
          simp [Zabs, pow_succ]
          ring
        have hR1 : (fun x => Zabs x ^ 2) = fun x => Z x ^ 2 := by
          ext x
          simp [Zabs]
        have hR2 : (fun x => (Z x ^ 2) ^ 2) = fun x => Z x ^ 4 := by
          ext x; ring
        rw [hL, hR1, hR2] at h
        exact h
      have hcs3 :
          (avg Zpos) ^ 2 ≤ avg (fun x => Z x ^ 2) * avg (sqEvent u 1) := by
        have h := avg_mul_sq_le Zpos (sqEvent u 1)
        have hL : (fun x => Zpos x * sqEvent u 1 x) = Zpos := by
          ext x
          dsimp [Zpos, Z, sqEvent]
          split_ifs with h1
          · ring
          · have hlt : S u x ^ 2 - 1 < 0 := by linarith
            rw [max_eq_right (le_of_lt hlt)]
            ring
        have hR2 : (fun x => sqEvent u 1 x ^ 2) = sqEvent u 1 := by
          ext x; exact sqEvent_sq u 1 x
        have hR1 : avg (fun x => Zpos x ^ 2) ≤ avg (fun x => Z x ^ 2) := by
          apply avg_mono
          intro x
          dsimp [Zpos]
          rcases le_total 0 (Z x) with h | h
          · rw [max_eq_left h]
          · rw [max_eq_right h]
            nlinarith
        have hsqE_nn : 0 ≤ avg (sqEvent u 1) :=
          avg_nonneg (fun x => by unfold sqEvent; split_ifs <;> norm_num)
        rw [hL, hR2] at h
        exact le_trans h (mul_le_mul_of_nonneg_right hR1 hsqE_nn)
      have hZ4 : avg (fun x => Z x ^ 4) ≤ 27 * (avg (fun x => Z x ^ 2)) ^ 2 := by
        have h := avg_quad_pow_four d (-1) (fun _ => 0) u
        have heq : ∀ x : Cube d, (-1 : ℝ) + S (fun _ => 0) x + S u x ^ 2 = Z x := by
          intro x
          simp [Z, S]
          ring
        simp_rw [heq] at h
        exact h
      have hZabs_nn : 0 ≤ avg Zabs := avg_nonneg (fun x => abs_nonneg _)
      have hZabs3_nn : 0 ≤ avg (fun x => Zabs x ^ 3) :=
        avg_nonneg (fun x => pow_nonneg (abs_nonneg _) 3)
      have hZ4_nn : 0 ≤ avg (fun x => Z x ^ 4) := avg_nonneg (fun x => by positivity)
      have hstep1 :
          (avg (fun x => Z x ^ 2)) ^ 4 ≤
            (avg Zabs) ^ 2 * (avg (fun x => Zabs x ^ 3)) ^ 2 := by
        have hsq := pow_le_pow_left₀ (sq_nonneg _) hcs1 2
        calc (avg (fun x => Z x ^ 2)) ^ 4
            = ((avg (fun x => Z x ^ 2)) ^ 2) ^ 2 := by ring
          _ ≤ (avg Zabs * avg (fun x => Zabs x ^ 3)) ^ 2 := hsq
          _ = (avg Zabs) ^ 2 * (avg (fun x => Zabs x ^ 3)) ^ 2 := by ring
      have hstep2 :
          (avg (fun x => Z x ^ 2)) ^ 4 ≤
            (avg Zabs) ^ 2 * (avg (fun x => Z x ^ 2) * avg (fun x => Z x ^ 4)) :=
        le_trans hstep1 (mul_le_mul_of_nonneg_left hcs2 (sq_nonneg _))
      have hstep3 :
          (avg (fun x => Z x ^ 2)) ^ 4 ≤
            4 * (avg (fun x => Z x ^ 2) * avg (sqEvent u 1)) *
              (avg (fun x => Z x ^ 2) * avg (fun x => Z x ^ 4)) := by
        rw [havg_abs] at hstep2
        have h4pos : (2 * avg Zpos) ^ 2 ≤ 4 * (avg (fun x => Z x ^ 2) * avg (sqEvent u 1)) := by
          linarith
        exact le_trans hstep2
          (mul_le_mul_of_nonneg_right h4pos (mul_nonneg (le_of_lt hZ2_pos) hZ4_nn))
      have hsqE_nn : 0 ≤ avg (sqEvent u 1) :=
        avg_nonneg (fun x => by unfold sqEvent; split_ifs <;> norm_num)
      have hstep4 :
          (avg (fun x => Z x ^ 2)) ^ 4 ≤
            108 * avg (sqEvent u 1) * (avg (fun x => Z x ^ 2)) ^ 4 := by
        have hmul :
            4 * (avg (fun x => Z x ^ 2) * avg (sqEvent u 1)) *
              (avg (fun x => Z x ^ 2) * avg (fun x => Z x ^ 4)) ≤
            4 * (avg (fun x => Z x ^ 2) * avg (sqEvent u 1)) *
              (avg (fun x => Z x ^ 2) * (27 * (avg (fun x => Z x ^ 2)) ^ 2)) := by
          have hc1 : 0 ≤ 4 * (avg (fun x => Z x ^ 2) * avg (sqEvent u 1)) := by positivity
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hZ4 (le_of_lt hZ2_pos)) hc1
        calc (avg (fun x => Z x ^ 2)) ^ 4
            ≤ 4 * (avg (fun x => Z x ^ 2) * avg (sqEvent u 1)) *
                (avg (fun x => Z x ^ 2) * (27 * (avg (fun x => Z x ^ 2)) ^ 2)) :=
              le_trans hstep3 hmul
          _ = 108 * avg (sqEvent u 1) * (avg (fun x => Z x ^ 2)) ^ 4 := by ring
      have hZ2_4_pos : 0 < (avg (fun x => Z x ^ 2)) ^ 4 := pow_pos hZ2_pos 4
      have h108 : 1 ≤ 108 * avg (sqEvent u 1) := by nlinarith
      have h2p := avg_sqEvent_le_two_prob u (by norm_num : (0 : ℝ) ≤ 1)
      linarith
  refine ⟨hprob, ?_⟩
  set P := probability u 1
  have hP_pos : 0 < P := by linarith
  have hcs : (avg (fun x => S v x * event u 1 x)) ^ 2 ≤ P := by
    have h := avg_mul_sq_le (S v) (event u 1)
    have heq : (fun x => event u 1 x ^ 2) = event u 1 := by ext x; exact event_sq u 1 x
    rw [avg_S_sq, hvv, heq] at h
    simpa [P, probability] using h
  have hcond_sq : (conditional u v 1) ^ 2 ≤ 864 := by
    unfold conditional
    rw [div_pow]
    have h1 : (avg (fun x => S v x * event u 1 x)) ^ 2 / P ^ 2 ≤ P / P ^ 2 :=
      div_le_div_of_nonneg_right hcs (sq_nonneg P)
    have h2 : P / P ^ 2 = 1 / P := by
      field_simp [ne_of_gt hP_pos]
    have h3 : 1 / P ≤ 864 := by
      rw [div_le_iff₀ hP_pos]
      linarith
    linarith
  have hsqrt_sq : (Real.sqrt 864) ^ 2 = 864 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 864]

private lemma part4 :
    ∀ c t L : ℝ, 0 ≤ c → c < 1 → 1 < t → ∃ d : ℕ, ∃ u v : Fin d → ℝ,
      dot u u = 1 ∧ dot v v = 1 ∧ dot u v = c ∧ 0 < probability u t ∧ conditional u v t < L := by
  intro c t L hc0 hc1 ht1
  have h1mc2_pos : 0 < 1 - c ^ 2 := by nlinarith
  have hsc_pos : 0 < Real.sqrt (1 - c ^ 2) := Real.sqrt_pos.mpr h1mc2_pos
  obtain ⟨m, hm⟩ := exists_nat_gt (max 1 (((c * t - L) / Real.sqrt (1 - c ^ 2)) ^ 2 + t ^ 2))
  have hm1 : (1 : ℝ) < (m : ℝ) := lt_of_le_of_lt (le_max_left _ _) hm
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hm_big : ((c * t - L) / Real.sqrt (1 - c ^ 2)) ^ 2 + t ^ 2 < (m : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hm
  have hD_pos : 0 < (m : ℝ) + 1 - t ^ 2 := by
    have : 0 ≤ ((c * t - L) / Real.sqrt (1 - c ^ 2)) ^ 2 := sq_nonneg _
    linarith
  set r : ℝ := Real.sqrt ((m : ℝ) * ((m : ℝ) + 1 - t ^ 2))
  have hr_nn : 0 ≤ r := Real.sqrt_nonneg _
  have hr_sq : r ^ 2 = (m : ℝ) * ((m : ℝ) + 1 - t ^ 2) :=
    Real.sq_sqrt (mul_nonneg (le_of_lt hm_pos) (le_of_lt hD_pos))
  set a : ℝ := (t + r) / ((m : ℝ) + 1)
  set b : ℝ := ((m : ℝ) * t - r) / ((m : ℝ) * ((m : ℝ) + 1))
  have ha_pos : 0 < a := by
    dsimp [a]
    apply div_pos <;> linarith
  have hmt_gt_r : r < (m : ℝ) * t := by
    have ht2 : 1 < t ^ 2 := by nlinarith
    have hdiff : 0 < (m : ℝ) * ((m : ℝ) + 1) * (t ^ 2 - 1) := by positivity
    have hsq : r ^ 2 < ((m : ℝ) * t) ^ 2 := by
      rw [hr_sq]
      linarith
    have hmt_nn : 0 ≤ (m : ℝ) * t := by positivity
    nlinarith [hsq, hr_nn, hmt_nn]
  have hb_pos : 0 < b := by
    dsimp [b]
    apply div_pos
    · linarith
    · positivity
  let u : Fin (m + 1) → ℝ := Fin.cons a (fun _ => b)
  have hu_pos : ∀ i : Fin (m + 1), 0 < u i := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa [u] using ha_pos
    · intro j; simpa [u] using hb_pos
  have hsum_u : ∑ i : Fin (m + 1), u i = t := by
    rw [Fin.sum_univ_succ]
    simp only [u, Fin.cons_zero, Fin.cons_succ, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    dsimp [a, b]
    field_simp [ne_of_gt hm_pos, ne_of_gt hm1_pos]
    ring
  have huu : dot u u = 1 := by
    unfold dot
    rw [Fin.sum_univ_succ]
    simp only [u, Fin.cons_zero, Fin.cons_succ, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    dsimp [a, b]
    have hne1 : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
    have hne2 : (m : ℝ) + 1 ≠ 0 := ne_of_gt hm1_pos
    field_simp [hne1, hne2]
    nlinarith [hr_sq]
  set s : ℝ := Real.sqrt ((m : ℝ) + 1 - t ^ 2)
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hD_pos
  have hs_sq : s ^ 2 = (m : ℝ) + 1 - t ^ 2 := Real.sq_sqrt (le_of_lt hD_pos)
  let w : Fin (m + 1) → ℝ := fun i => -(1 - t * u i) / s
  have huw : dot u w = 0 := by
    unfold dot
    have h1 : ∀ i, u i * w i = (-1 / s) * (u i - t * (u i * u i)) := by
      intro i; dsimp [w]; ring
    simp_rw [h1, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
    change (-1 / s) * ((∑ i, u i) - t * dot u u) = 0
    rw [hsum_u, huu]
    ring
  have hww : dot w w = 1 := by
    unfold dot
    have h1 : ∀ i, w i * w i = (1 / s ^ 2) * (1 - 2 * t * u i + t ^ 2 * (u i * u i)) := by
      intro i; dsimp [w]; ring
    simp_rw [h1, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hcard : (((m + 1 : ℕ) : ℝ)) * 1 = (m : ℝ) + 1 := by push_cast; ring
    change (1 / s ^ 2) * ((((m + 1 : ℕ) : ℝ)) * 1 - 2 * t * (∑ i, u i) + t ^ 2 * dot u u) = 1
    rw [hcard, hsum_u, huu]
    have hs2ne : s ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hs_pos)
    field_simp [hs2ne]
    linarith [hs_sq]
  have hsum_w : ∑ i : Fin (m + 1), w i = -s := by
    have h1 : ∀ i, w i = (-1 / s) * (1 - t * u i) := by
      intro i; dsimp [w]; ring
    simp_rw [h1, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hcard : (((m + 1 : ℕ) : ℝ)) * 1 = (m : ℝ) + 1 := by push_cast; ring
    rw [hcard, hsum_u]
    have hsne : s ≠ 0 := ne_of_gt hs_pos
    field_simp [hsne]
    nlinarith [hs_sq]
  let v : Fin (m + 1) → ℝ := fun i => c * u i + Real.sqrt (1 - c ^ 2) * w i
  have huv : dot u v = c := by
    unfold dot
    have h1 : ∀ i, u i * v i = c * (u i * u i) + Real.sqrt (1 - c ^ 2) * (u i * w i) := by
      intro i; dsimp [v]; ring
    simp_rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum]
    change c * dot u u + Real.sqrt (1 - c ^ 2) * dot u w = c
    rw [huu, huw]
    ring
  have hvv : dot v v = 1 := by
    unfold dot
    have h1 : ∀ i, v i * v i =
        c ^ 2 * (u i * u i) + (2 * c * Real.sqrt (1 - c ^ 2)) * (u i * w i) +
          (Real.sqrt (1 - c ^ 2) ^ 2) * (w i * w i) := by
      intro i; dsimp [v]; ring
    simp_rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum]
    change c ^ 2 * dot u u + (2 * c * Real.sqrt (1 - c ^ 2)) * dot u w +
      (Real.sqrt (1 - c ^ 2) ^ 2) * dot w w = 1
    rw [huu, huw, hww, Real.sq_sqrt (le_of_lt h1mc2_pos)]
    ring
  let allTrue : Cube (m + 1) := fun _ => true
  have hSu_true : S u allTrue = t := by
    simpa [S, allTrue, sign] using hsum_u
  have hevent_eq : ∀ x : Cube (m + 1), event u t x = if x = allTrue then 1 else 0 := by
    intro x
    unfold event
    by_cases hx : x = allTrue
    · rw [hx, hSu_true, if_pos le_rfl, if_pos rfl]
    · rw [if_neg hx]
      have hex : ∃ j : Fin (m + 1), x j = false := by
        by_contra hall
        push Not at hall
        apply hx
        ext j
        cases hxj : x j
        · exact absurd hxj (hall j)
        · rfl
      obtain ⟨j, hj⟩ := hex
      have hlt : S u x < t := by
        rw [← hsum_u]
        unfold S
        apply Finset.sum_lt_sum
        · intro i _
          have hui := hu_pos i
          cases x i <;> simp [sign] <;> linarith
        · refine ⟨j, Finset.mem_univ j, ?_⟩
          have huj := hu_pos j
          rw [hj]
          simp [sign]
          linarith
      rw [if_neg (not_le_of_gt hlt)]
  have hprob_val : probability u t = 1 / (Fintype.card (Cube (m + 1)) : ℝ) := by
    unfold probability
    rw [avg_eq_sum_div]
    simp_rw [hevent_eq]
    simp
  have hprob_pos : 0 < probability u t := by
    rw [hprob_val]
    exact div_pos one_pos (card_cube_pos (m + 1))
  have hcond_val : conditional u v t = S v allTrue := by
    unfold conditional
    rw [avg_eq_sum_div, hprob_val]
    have hnum : ∑ x : Cube (m + 1), S v x * event u t x = S v allTrue := by
      simp_rw [hevent_eq]
      simp
    rw [hnum]
    have hne : (Fintype.card (Cube (m + 1)) : ℝ) ≠ 0 := ne_of_gt (card_cube_pos (m + 1))
    field_simp [hne]
  have hSv_val : S v allTrue = c * t - Real.sqrt (1 - c ^ 2) * s := by
    have h1 : S v allTrue = ∑ i : Fin (m + 1), v i := by
      simp [S, allTrue, sign]
    rw [h1]
    simp only [v, Finset.sum_add_distrib, ← Finset.mul_sum, hsum_u, hsum_w]
    ring
  have hcond_lt : conditional u v t < L := by
    rw [hcond_val, hSv_val]
    have hs_gt : (c * t - L) / Real.sqrt (1 - c ^ 2) < s := by
      by_cases hctL : 0 ≤ (c * t - L) / Real.sqrt (1 - c ^ 2)
      · have hsq : ((c * t - L) / Real.sqrt (1 - c ^ 2)) ^ 2 < s ^ 2 := by
          rw [hs_sq]
          linarith
        nlinarith
      · linarith
    have hmul : c * t - L < Real.sqrt (1 - c ^ 2) * s := by
      have := (div_lt_iff₀ hsc_pos).mp hs_gt
      linarith
    linarith
  exact ⟨m + 1, u, v, huu, hvv, huv, hprob_pos, hcond_lt⟩

end OMA.S_mo_434958

theorem OMA.solution : type_of% @OMA.S_mo_434958.main :=
  ⟨OMA.S_mo_434958.part1, OMA.S_mo_434958.part2, OMA.S_mo_434958.part3, OMA.S_mo_434958.part4⟩
