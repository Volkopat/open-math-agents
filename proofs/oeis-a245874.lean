import OMAStatements.S_oeis_a245874

/-!
# OEIS A245874

Source: https://oeis.org/A245874
The parity polynomials and generating function were conjectured by Colin Barker.
Formal statement credit: @clementtrecourt. Proof credit: @grp06.
-/

namespace OMA.S_oeis_a245874

open scoped BigOperators

private abbrev Letter (n : ℕ) := Fin (n + 1)

private def mirror {n : ℕ} (x : Letter n) : Letter n :=
  ⟨n - x.val, by omega⟩

private theorem mirror_eq_iff {n : ℕ} (x y : Letter n) :
    mirror x = y ↔ x.val + y.val = n := by
  have hx := x.isLt
  have hy := y.isLt
  rw [← Fin.val_inj]
  change n - x.val = y.val ↔ _
  omega

private theorem mirror_mirror {n : ℕ} (x : Letter n) :
    mirror (mirror x) = x := by
  have hx := x.isLt
  apply Fin.ext
  change n - (n - x.val) = x.val
  omega

private theorem mirror_injective {n : ℕ} : Function.Injective (@mirror n) := by
  intro x y h
  simpa only [mirror_mirror] using congrArg mirror h

private theorem mirror_swap {n : ℕ} {x y : Letter n} (h : mirror x = y) :
    mirror y = x := by rw [← h, mirror_mirror]

private abbrev Fixed {n : ℕ} (x : Letter n) : Prop := mirror x = x

private theorem fixed_unique {n : ℕ} {x y : Letter n}
    (hx : Fixed x) (hy : Fixed y) : x = y := by
  have hx' := (mirror_eq_iff x x).mp hx
  have hy' := (mirror_eq_iff y y).mp hy
  apply Fin.ext
  omega

private theorem nonfixed_mirror {n : ℕ} {x : Letter n} (hx : ¬Fixed x) :
    ¬Fixed (mirror x) := by
  intro h
  exact hx (h.symm.trans (mirror_mirror x))

private def fixedCount (n : ℕ) : ℚ := if Even n then 1 else 0

private theorem sum_fixed {n : ℕ} (r : ℚ) :
    (∑ x : Letter n, if Fixed x then r else 0) = fixedCount n * r := by
  by_cases h : Even n
  · let z : Letter n := ⟨n / 2, by omega⟩
    have hz : Fixed z := by
      apply (mirror_eq_iff z z).mpr
      have hn := Nat.even_iff.mp h
      change n / 2 + n / 2 = n
      omega
    have heq (x : Letter n) : Fixed x ↔ x = z :=
      ⟨fun hx => fixed_unique hx hz, fun hx => hx.symm ▸ hz⟩
    simp only [heq, Fintype.sum_ite_eq', fixedCount, if_pos h, one_mul]
  · have hn (x : Letter n) : ¬Fixed x := by
      intro hx
      exact h ⟨x.val, ((mirror_eq_iff x x).mp hx).symm⟩
    simp [hn, fixedCount, h]

private theorem sum_choose_fixed {n : ℕ} (u v : ℚ) :
    (∑ x : Letter n, if Fixed x then u else v) =
      fixedCount n * u + ((n : ℚ) + 1 - fixedCount n) * v := by
  calc
    _ = ∑ x : Letter n, (v + if Fixed x then u - v else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : Fixed x
      · simp only [if_pos hx]
        ring
      · simp only [if_neg hx, add_zero]
    _ = _ := by
      rw [Finset.sum_add_distrib, sum_fixed]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one]
      ring

private inductive Suffix
  | ff | fn | nf | eq | cp | other

private def state {n : ℕ} (b c : Letter n) : Suffix :=
  if Fixed b then (if Fixed c then .ff else .fn)
  else if Fixed c then .nf
  else if c = b then .eq
  else if mirror b = c then .cp
  else .other

private def valid {n : ℕ} (b c y : Letter n) : Prop :=
  mirror b = c ∨ y = mirror b ∨ y = mirror c

private instance {n : ℕ} (b c y : Letter n) : Decidable (valid b c y) :=
  inferInstanceAs (Decidable (mirror b = c ∨ y = mirror b ∨ y = mirror c))

private theorem sum_all_next_fixed {n : ℕ} (v : Suffix → ℚ)
    (c : Letter n) (hc : Fixed c) :
    (∑ y : Letter n, v (state c y)) =
      fixedCount n * v .ff + ((n : ℚ) + 1 - fixedCount n) * v .fn := by
  calc
    _ = ∑ y : Letter n, (if Fixed y then v .ff else v .fn) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [state, if_pos hc]
      by_cases hy : Fixed y
      · simp only [if_pos hy]
      · simp only [if_neg hy]
    _ = _ := sum_choose_fixed _ _

private theorem sum_all_next_nonfixed {n : ℕ} (v : Suffix → ℚ)
    (c : Letter n) (hc : ¬Fixed c) :
    (∑ y : Letter n, v (state c y)) =
      fixedCount n * v .nf + v .eq + v .cp +
        ((n : ℚ) + 1 - 2 - fixedCount n) * v .other := by
  have hm := nonfixed_mirror hc
  calc
    _ = ∑ y : Letter n,
        ((if Fixed y then v .nf else v .other) +
          (if y = c then v .eq - v .other else 0) +
          (if y = mirror c then v .cp - v .other else 0)) := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y = c
      · subst y
        simp [state, hc, Ne.symm hc] <;> ring
      · by_cases hy' : y = mirror c
        · subst y
          simp [state, hc, hm] <;> ring
        · by_cases hf : Fixed y
          · simp [state, hc, if_pos hf, hy, hy', Ne.symm hy']
          · simp [state, hc, if_neg hf, hy, hy', Ne.symm hy']
    _ = _ := by
      simp only [Finset.sum_add_distrib, sum_choose_fixed, Fintype.sum_ite_eq']
      ring

private theorem sum_one_letter {n : ℕ} (f : Letter n → ℚ) (u : Letter n) :
    (∑ y : Letter n, if y = u then f y else 0) = f u := by
  simp only [Fintype.sum_ite_eq']

private theorem sum_two_letters {n : ℕ} (f : Letter n → ℚ)
    {u w : Letter n} (h : u ≠ w) :
    (∑ y : Letter n, if y = u ∨ y = w then f y else 0) = f u + f w := by
  calc
    _ = ∑ y : Letter n, ((if y = u then f y else 0) + (if y = w then f y else 0)) := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y = u
      · subst y
        simp [h]
      · simp [hy]
    _ = _ := by rw [Finset.sum_add_distrib, sum_one_letter, sum_one_letter]

private def step (q e : ℚ) (v : Suffix → ℚ) : Suffix → ℚ
  | .ff => v .ff + (q - 1) * v .fn
  | .fn => v .nf + v .cp
  | .nf => v .ff + v .fn
  | .eq => v .cp
  | .cp => e * v .nf + v .eq + v .cp + (q - 2 - e) * v .other
  | .other => v .cp + v .other

/-- The weighted transition formula gives each row by choosing a state indicator as weight. -/
private theorem transition {n : ℕ} (v : Suffix → ℚ) (b c : Letter n) :
    (∑ y : Letter n, if valid b c y then v (state c y) else 0) =
      step ((n : ℚ) + 1) (fixedCount n) v (state b c) := by
  by_cases hbc : mirror b = c
  · subst c
    simp only [valid, true_or, if_true]
    by_cases hb : Fixed b
    · have he : Even n := ⟨b.val, ((mirror_eq_iff b b).mp hb).symm⟩
      rw [show mirror b = b from hb, sum_all_next_fixed v b hb]
      simp [state, if_pos hb, step, fixedCount, he]
    · have hm := nonfixed_mirror hb
      rw [sum_all_next_nonfixed v (mirror b) hm]
      simp [state, hb, hm, step]
  · simp only [valid, hbc, false_or]
    by_cases heq : b = c
    · subst c
      have hb : ¬Fixed b := hbc
      calc
        _ = ∑ y : Letter n, (if y = mirror b then v (state b y) else 0) := by
          apply Finset.sum_congr rfl
          intro y _
          by_cases hy : y = mirror b
          · have hor : y = mirror b ∨ y = mirror b := Or.inl hy
            rw [if_pos hor, if_pos hy]
          · have hor : ¬(y = mirror b ∨ y = mirror b) := fun h => h.elim hy hy
            rw [if_neg hor, if_neg hy]
        _ = _ := by
          rw [sum_one_letter]
          simp [state, hb, nonfixed_mirror hb, step]
    · have hmir : mirror b ≠ mirror c := fun h => heq (mirror_injective h)
      rw [sum_two_letters _ hmir]
      by_cases hb : Fixed b
      · have hc : ¬Fixed c := fun h => heq (fixed_unique hb h)
        rw [show mirror b = b from hb]
        simp [state, hc, if_pos hb, nonfixed_mirror hc, step]
      · by_cases hc : Fixed c
        · rw [show mirror c = c from hc]
          simp [state, if_pos hc, hb, nonfixed_mirror hb, step, add_comm]
        · have hy : mirror b ≠ c := hbc
          have hy' : mirror c ≠ mirror b := Ne.symm hmir
          simp [state, hb, hc, nonfixed_mirror hb, nonfixed_mirror hc,
            Ne.symm heq, hy, hy', step, add_comm]

private def weight (q e : ℚ) : ℕ → Suffix → ℚ
  | 0 => fun _ => 1
  | k + 1 => step q e (weight q e k)

private def extension {n : ℕ} : ℕ → Letter n → Letter n → ℚ
  | 0, _, _ => 1
  | k + 1, b, c => ∑ y : Letter n, if valid b c y then extension k c y else 0

private theorem extension_eq {n : ℕ} (k : ℕ) (b c : Letter n) :
    extension k b c = weight ((n : ℚ) + 1) (fixedCount n) k (state b c) := by
  induction k generalizing b c with
  | zero => rfl
  | succ k ih =>
    simp only [extension, weight, ih]
    exact transition _ _ _

private def initial (q e : ℚ) (v : Suffix → ℚ) : ℚ :=
  e * v .ff + e * (q - e) * v .fn + e * (q - e) * v .nf +
    (q - e) * v .eq + (q - e) * v .cp + (q - e) * (q - e - 2) * v .other

private theorem sum_initial {n : ℕ} (v : Suffix → ℚ) :
    (∑ b : Letter n, ∑ c : Letter n, v (state b c)) =
      initial ((n : ℚ) + 1) (fixedCount n) v := by
  let q : ℚ := (n : ℚ) + 1
  let e := fixedCount n
  calc
    _ = ∑ b : Letter n,
        (if Fixed b then e * v .ff + (q - e) * v .fn
         else e * v .nf + v .eq + v .cp + (q - 2 - e) * v .other) := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : Fixed b
      · rw [if_pos hb]
        exact sum_all_next_fixed v b hb
      · rw [if_neg hb]
        exact sum_all_next_nonfixed v b hb
    _ = _ := by
      rw [sum_choose_fixed]
      by_cases h : Even n <;>
        simp only [q, e, initial, fixedCount, h, if_true, if_false] <;> ring

/-- Prepending a letter turns a sum over tuples into two nested sums. -/
private theorem sum_cons {n k : ℕ} (f : (Fin (k + 1) → Letter n) → ℚ) :
    (∑ x, f x) = ∑ y : Letter n, ∑ ys : Fin k → Letter n, f (Fin.cons y ys) := by
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Letter n)).sum_comp f,
    Fintype.sum_prod_type] <;> rfl

private def admissible {n : ℕ} :
    (k : ℕ) → Letter n → Letter n → (Fin k → Letter n) → Prop
  | 0, _, _, _ => True
  | k + 1, b, c, xs => valid b c (xs 0) ∧ admissible k c (xs 0) (Fin.tail xs)

private instance admissibleDecidable {n : ℕ} :
    (k : ℕ) → (b c : Letter n) → (xs : Fin k → Letter n) →
      Decidable (admissible k b c xs)
  | 0, _, _, _ => isTrue trivial
  | k + 1, b, c, xs =>
    letI : Decidable (admissible k c (xs 0) (Fin.tail xs)) :=
      admissibleDecidable k c (xs 0) (Fin.tail xs)
    (inferInstance : Decidable (valid b c (xs 0) ∧ admissible k c (xs 0) (Fin.tail xs)))

private theorem sum_admissible {n : ℕ} (k : ℕ) (b c : Letter n) :
    (∑ xs : Fin k → Letter n, if admissible k b c xs then (1 : ℚ) else 0) =
      extension k b c := by
  induction k generalizing b c with
  | zero =>
    calc
      _ = ∑ _xs : Fin 0 → Letter n, (1 : ℚ) := by
        apply Finset.sum_congr rfl
        intro xs _
        exact if_pos (show admissible 0 b c xs from trivial)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Fintype.card_pi_const, pow_zero, Nat.cast_one, one_mul, extension]
  | succ k ih =>
    rw [sum_cons, extension]
    apply Finset.sum_congr rfl
    intro y _
    simp only [admissible, Fin.cons_zero, Fin.tail_cons]
    by_cases h : valid b c y
    · simpa only [h, true_and, if_true] using ih c y
    · simp [h]

private theorem valid_sums {n : ℕ} (b c y : Letter n) :
    valid b c y ↔ b.val + c.val = n ∨ b.val + y.val = n ∨ c.val + y.val = n := by
  rw [valid, eq_comm (a := y) (b := mirror b), eq_comm (a := y) (b := mirror c),
    mirror_eq_iff, mirror_eq_iff, mirror_eq_iff]

private theorem window_iff {n : ℕ} (x : Fin 7 → Letter n) (i : ℕ) (hi : i < 5) :
    (∃ s < (3 : ℕ), ∃ t < (3 : ℕ),
      s < t ∧ get x (i + s) + get x (i + t) = n) ↔
      valid (x ⟨i, by omega⟩) (x ⟨i + 1, by omega⟩) (x ⟨i + 2, by omega⟩) := by
  rw [valid_sums]
  have h0 : i < 7 := by omega
  have h1 : i + 1 < 7 := by omega
  have h2 : i + 2 < 7 := by omega
  constructor
  · rintro ⟨s, hs, t, ht, hst, h⟩
    interval_cases s <;> interval_cases t
    all_goals first
      | omega
      | exact Or.inl (by simpa only [get, Nat.add_zero, dif_pos h0, dif_pos h1] using h)
      | exact Or.inr (Or.inl (by simpa only [get, Nat.add_zero, dif_pos h0, dif_pos h2] using h))
      | exact Or.inr (Or.inr (by simpa only [get, dif_pos h1, dif_pos h2] using h))
  · rintro (h | h | h)
    · exact ⟨0, by decide, 1, by decide, by decide,
        by simpa only [get, Nat.add_zero, dif_pos h0, dif_pos h1] using h⟩
    · exact ⟨0, by decide, 2, by decide, by decide,
        by simpa only [get, Nat.add_zero, dif_pos h0, dif_pos h2] using h⟩
    · exact ⟨1, by decide, 2, by decide, by decide,
        by simpa only [get, dif_pos h1, dif_pos h2] using h⟩

private theorem good_iff {n : ℕ} (x : Fin 7 → Letter n) :
    good x = true ↔ admissible 5 (x 0) (x 1) (Fin.tail (Fin.tail x)) := by
  unfold good
  rw [decide_eq_true_eq]
  change _ ↔ valid (x 0) (x 1) (x 2) ∧ valid (x 1) (x 2) (x 3) ∧
    valid (x 2) (x 3) (x 4) ∧ valid (x 3) (x 4) (x 5) ∧
    valid (x 4) (x 5) (x 6) ∧ True
  constructor
  · intro h
    exact ⟨(window_iff x 0 (by decide)).mp (h 0 (by decide)),
      (window_iff x 1 (by decide)).mp (h 1 (by decide)),
      (window_iff x 2 (by decide)).mp (h 2 (by decide)),
      (window_iff x 3 (by decide)).mp (h 3 (by decide)),
      (window_iff x 4 (by decide)).mp (h 4 (by decide)), trivial⟩
  · rintro ⟨h0, h1, h2, h3, h4, _⟩ i hi
    apply (window_iff x i hi).mpr
    interval_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4

private theorem count_initial (n : ℕ) :
    (a n : ℚ) =
      initial ((n : ℚ) + 1) (fixedCount n) (weight ((n : ℚ) + 1) (fixedCount n) 5) := by
  unfold a
  rw [Int.cast_natCast, Finset.natCast_card_filter]
  calc
    _ = ∑ x : Fin 7 → Letter n,
        (if admissible 5 (x 0) (x 1) (Fin.tail (Fin.tail x)) then (1 : ℚ) else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : good x = true
      · rw [if_pos h, if_pos ((good_iff x).mp h)]
      · rw [if_neg h, if_neg (fun hh => h ((good_iff x).mpr hh))]
    _ = ∑ b : Letter n, ∑ c : Letter n, extension 5 b c := by
      rw [sum_cons]
      apply Finset.sum_congr rfl
      intro b _
      rw [sum_cons]
      apply Finset.sum_congr rfl
      intro c _
      simpa only [Fin.cons_zero, Fin.cons_one, Fin.tail_cons] using sum_admissible 5 b c
    _ = _ := by simp only [extension_eq, sum_initial]

private def evenPoly (x : ℚ) : ℚ := 1 + 12 * x + 26 * x ^ 2 + 39 * x ^ 3 + 7 * x ^ 4

private def oddPoly (x : ℚ) : ℚ := -9 - 18 * x + 23 * x ^ 2 + 39 * x ^ 3 + 7 * x ^ 4

set_option maxHeartbeats 1600000 in
private theorem count_even (n : ℕ) (h : Even n) : (a n : ℚ) = evenPoly n := by
  rw [count_initial]
  simp only [fixedCount, if_pos h, initial, weight, step, evenPoly]
  ring

set_option maxHeartbeats 1600000 in
private theorem count_odd (n : ℕ) (h : Odd n) : (a n : ℚ) = oddPoly n := by
  have he : ¬Even n := Nat.not_even_iff_odd.mpr h
  rw [count_initial]
  simp only [fixedCount, if_neg he, initial, weight, step, oddPoly]
  ring

open PowerSeries

private def sequenceValue (n : ℕ) : ℚ :=
  if n < 1 then 0 else if Even n then evenPoly n else oddPoly n

private theorem sequenceValue_eq (n : ℕ) :
    (if n < 1 then 0 else (a n : ℚ)) = sequenceValue n := by
  unfold sequenceValue
  by_cases h : Even n
  · simp only [if_pos h, count_even n h]
  · simp only [if_neg h, count_odd n (Nat.not_even_iff_odd.mp h)]

private theorem coeff_weighted_shift (f : PowerSeries ℚ) (r : ℚ) (k n : ℕ) :
    coeff n (f * (C r * X ^ k)) = if k ≤ n then coeff (n - k) f * r else 0 := by
  rw [← mul_assoc, coeff_mul_X_pow']
  by_cases h : k ≤ n <;> simp only [h, if_true, if_false, coeff_mul_C]

private theorem denominator_expansion :
    ((1 - X) ^ 5 * (1 + X) ^ 3 : PowerSeries ℚ) =
      C 1 * X ^ 0 + C (-2) * X ^ 1 + C (-2) * X ^ 2 + C 6 * X ^ 3 +
      C (-6) * X ^ 5 + C 2 * X ^ 6 + C 2 * X ^ 7 + C (-1) * X ^ 8 := by
  simp only [map_neg, map_ofNat, map_one, pow_zero, pow_one]
  ring

private theorem numerator_expansion :
    (X * (42 + 469 * X + 574 * X ^ 2 + 371 * X ^ 3 + 10 * X ^ 4 -
      121 * X ^ 5 - 2 * X ^ 6 + X ^ 7) : PowerSeries ℚ) =
      C 42 * X ^ 1 + C 469 * X ^ 2 + C 574 * X ^ 3 + C 371 * X ^ 4 +
      C 10 * X ^ 5 + C (-121) * X ^ 6 + C (-2) * X ^ 7 + C 1 * X ^ 8 := by
  simp only [map_neg, map_ofNat, map_one, pow_one]
  ring

set_option maxHeartbeats 1600000 in
private theorem generating :
    PowerSeries.mk sequenceValue * ((1 - X) ^ 5 * (1 + X) ^ 3 : PowerSeries ℚ) =
      X * (42 + 469 * X + 574 * X ^ 2 + 371 * X ^ 3 + 10 * X ^ 4 -
        121 * X ^ 5 - 2 * X ^ 6 + X ^ 7) := by
  apply PowerSeries.ext
  intro n
  rw [denominator_expansion, numerator_expansion]
  simp only [mul_add, map_add, coeff_weighted_shift, coeff_C_mul_X_pow, coeff_mk]
  by_cases hn : n < 9
  · interval_cases n <;> norm_num [sequenceValue, Nat.even_iff, evenPoly, oddPoly]
  · have present (k : ℕ) (hk : k ≤ 8) : k ≤ n := by omega
    have positive (k : ℕ) (hk : k ≤ 8) : ¬n - k < 1 := by omega
    have absent (k : ℕ) (hk : k ≤ 8) : n ≠ k := by omega
    have cast_sub (k : ℕ) (hk : k ≤ 8) : ((n - k : ℕ) : ℚ) = n - (k : ℚ) :=
      Nat.cast_sub (present k hk)
    simp only [if_pos (present 0 (by decide)), if_pos (present 1 (by decide)), if_pos (present 2 (by decide)), if_pos (present 3 (by decide)),
      if_pos (present 5 (by decide)), if_pos (present 6 (by decide)), if_pos (present 7 (by decide)), if_pos (present 8 (by decide)),
      if_neg (absent 1 (by decide)), if_neg (absent 2 (by decide)), if_neg (absent 3 (by decide)), if_neg (absent 4 (by decide)),
      if_neg (absent 5 (by decide)), if_neg (absent 6 (by decide)), if_neg (absent 7 (by decide)), if_neg (absent 8 (by decide)),
      sequenceValue, if_neg (positive 0 (by decide)), if_neg (positive 1 (by decide)), if_neg (positive 2 (by decide)), if_neg (positive 3 (by decide)),
      if_neg (positive 5 (by decide)), if_neg (positive 6 (by decide)), if_neg (positive 7 (by decide)), if_neg (positive 8 (by decide)),
      Nat.even_iff]
    by_cases hp : n % 2 = 0
    · have h0 : (n - 0) % 2 = 0 := by omega
      have h1 : ¬(n - 1) % 2 = 0 := by omega
      have h2 : (n - 2) % 2 = 0 := by omega
      have h3 : ¬(n - 3) % 2 = 0 := by omega
      have h5 : ¬(n - 5) % 2 = 0 := by omega
      have h6 : (n - 6) % 2 = 0 := by omega
      have h7 : ¬(n - 7) % 2 = 0 := by omega
      have h8 : (n - 8) % 2 = 0 := by omega
      simp only [if_pos h0, if_neg h1, if_pos h2, if_neg h3, if_neg h5, if_pos h6, if_neg h7, if_pos h8,
        cast_sub 0 (by decide), cast_sub 1 (by decide), cast_sub 2 (by decide), cast_sub 3 (by decide),
        cast_sub 5 (by decide), cast_sub 6 (by decide), cast_sub 7 (by decide), cast_sub 8 (by decide), evenPoly, oddPoly]
      ring
    · have h0 : ¬(n - 0) % 2 = 0 := by omega
      have h1 : (n - 1) % 2 = 0 := by omega
      have h2 : ¬(n - 2) % 2 = 0 := by omega
      have h3 : (n - 3) % 2 = 0 := by omega
      have h5 : (n - 5) % 2 = 0 := by omega
      have h6 : ¬(n - 6) % 2 = 0 := by omega
      have h7 : (n - 7) % 2 = 0 := by omega
      have h8 : ¬(n - 8) % 2 = 0 := by omega
      simp only [if_neg h0, if_pos h1, if_neg h2, if_pos h3, if_pos h5, if_neg h6, if_pos h7, if_neg h8,
        cast_sub 0 (by decide), cast_sub 1 (by decide), cast_sub 2 (by decide), cast_sub 3 (by decide),
        cast_sub 5 (by decide), cast_sub 6 (by decide), cast_sub 7 (by decide), cast_sub 8 (by decide), evenPoly, oddPoly]
      ring

end OMA.S_oeis_a245874

open OMA.S_oeis_a245874 in
theorem OMA.solution : type_of% @OMA.S_oeis_a245874.main := by
  refine ⟨?_, ?_, ?_⟩
  · have h : (fun n : ℕ => if n < 1 then 0 else (a n : ℚ)) = sequenceValue :=
      funext sequenceValue_eq
    rw [h]
    exact generating
  · intro n _ h
    exact count_even n h
  · intro n _ h
    exact count_odd n h

