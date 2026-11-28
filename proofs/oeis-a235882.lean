import OMAStatements.S_oeis_a235882

/-! The row-transfer counting framework is from @jleguina, PR #29537. -/

namespace OMA.S_oeis_a235882

open PowerSeries Finset



/-! ## The window condition, rows and the transfer -/

/-- A row. -/
abbrev Row := Fin 7 → Fin 3

/-- The window condition on the 2 X 2 block with top row (p, q) and bottom row (r, s). -/
def P (p q r s : Fin 3) : Prop :=
  medEq (p).val (q).val (r).val (s).val = true

instance (p q r s : Fin 3) : Decidable (P p q r s) := by unfold P; infer_instance

/-- Row s may follow row r: every block between them satisfies P. -/
def rowOK (r s : Fin 7 → Fin 3) : Prop :=
  ∀ j j' : Fin 7, j'.val = j.val + 1 → P (r j) (r j') (s j) (s j')

instance : DecidableRel rowOK := fun r s => by unfold rowOK; infer_instance

/-- Consecutive rows allowed. -/
def Valid {m : ℕ} (x : Fin m → Fin 7 → Fin 3) : Prop :=
  ∀ i i' : Fin m, i'.val = i.val + 1 → rowOK (x i) (x i')

instance {m : ℕ} : DecidablePred (@Valid m) := fun x => by unfold Valid; infer_instance

/-- The number of valid arrays with n + 1 rows. -/
def cnt (n : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 7 → Fin 3)).filter Valid).card

lemma a_eq (n : ℕ) : a n = cnt n := by
  unfold a cnt
  exact congrArg Finset.card (Finset.filter_congr (fun x _ => Iff.rfl))

/-- W(n, r): valid arrays with n + 1 rows whose first row is r. -/
def W (n : ℕ) (r : Fin 7 → Fin 3) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 7 → Fin 3)).filter (fun x => Valid x ∧ x 0 = r)).card

lemma valid_cons {n : ℕ} (r : Row) (g : Fin (n + 1) → Row) :
    Valid (Fin.cons r g : Fin (n + 2) → Row) ↔ rowOK r (g 0) ∧ Valid g := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h 0 1 (by simp)
      simpa using this
    · intro i j hij
      have := h i.succ j.succ (by simp [hij])
      simpa using this
  · rintro ⟨h0, hg⟩ i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        have hj : j = 0 := by ext; simp at hij; omega
        subst hj
        simpa using h0
    | succ i =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        simp only [Fin.cons_succ]
        exact hg i j (by simp at hij; omega)

lemma cnt_sum (n : ℕ) : cnt n = ∑ r : Row, W n r := by
  unfold cnt W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f => f 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  congr 1
  ext f
  simp

lemma W_zero (r : Row) : W 0 r = 1 := by
  unfold W
  rw [Finset.card_eq_one]
  refine ⟨fun _ => r, ?_⟩
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨_, hf⟩
    funext i
    rw [Fin.fin_one_eq_zero i, hf]
  · rintro rfl
    refine ⟨?_, rfl⟩
    intro i j hij
    have := j.isLt
    omega

/-- Prepending the row r. -/
def consEmb (n : ℕ) (r : Row) : (Fin (n + 1) → Row) ↪ (Fin (n + 2) → Row) where
  toFun g := Fin.cons r g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (r : Row) (g : Fin (n + 1) → Row) :
    consEmb n r g = Fin.cons r g := rfl

lemma W_succ (n : ℕ) (r : Row) :
    W (n + 1) r = ∑ s : Row, if rowOK r s then W n s else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → Row)).filter (fun f => Valid f ∧ f 0 = r)) =
      (((univ : Finset (Fin (n + 1) → Row)).filter (fun g => rowOK r (g 0) ∧ Valid g)).map
        (consEmb n r)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, consEmb_apply]
    constructor
    · rintro ⟨hv, h0⟩
      refine ⟨Fin.tail f, ?_, ?_⟩
      · have hf : f = Fin.cons r (Fin.tail f) := by
          rw [← h0]; exact (Fin.cons_self_tail f).symm
        rw [hf, valid_cons] at hv
        exact hv
      · rw [← h0]; exact Fin.cons_self_tail f
    · rintro ⟨g, hg, rfl⟩
      exact ⟨(valid_cons r g).2 hg, by simp⟩
  unfold W
  rw [e, Finset.card_map]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  split_ifs with hrs
  · congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, hg⟩, h0⟩
      exact ⟨hg, h0⟩
    · rintro ⟨hg, h0⟩
      exact ⟨⟨h0 ▸ hrs, hg⟩, h0⟩
  · rw [Finset.card_eq_zero]
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨hok, _⟩, h0⟩
    exact hrs (h0 ▸ hok)

/-! The median condition says each color occurs an even number of times.
The three colors embed in the two-bit group, so successor rows differ by
one fixed XOR translation. A row can use any translation that avoids the
fourth vector, and translations preserve the number of colors in a row. -/

private abbrev Bits := Bool × Bool

private def xor2 (u v : Bits) : Bits := (u.1 != v.1, u.2 != v.2)

private def pack (c : Fin 3) : Bits := (c == 1, c == 2)

private def missing : Bits := (true, true)

private def unpack (v : Bits) : Fin 3 := if v.1 then 1 else if v.2 then 2 else 0

private theorem xor_right (u v : Bits) : xor2 (xor2 u v) v = u :=
  (by decide : ∀ u v, xor2 (xor2 u v) v = u) u v

private theorem xor_left (u v : Bits) : xor2 u (xor2 u v) = v :=
  (by decide : ∀ u v, xor2 u (xor2 u v) = v) u v

private theorem pack_inj : Function.Injective pack := by decide

private theorem pack_ne_missing (c : Fin 3) : pack c ≠ missing :=
  (by decide : ∀ c, pack c ≠ missing) c

private theorem pack_unpack (v : Bits) (h : v ≠ missing) : pack (unpack v) = v :=
  (by decide : ∀ v, v ≠ missing → pack (unpack v) = v) v h

private theorem block_iff (p q r s : Fin 3) :
    P p q r s ↔ xor2 (pack r) (pack p) = xor2 (pack s) (pack q) :=
  (by decide : ∀ p q r s,
    P p q r s ↔ xor2 (pack r) (pack p) = xor2 (pack s) (pack q)) p q r s

private theorem row_constant (r s : Row) : rowOK r s ↔
    ∀ j, xor2 (pack (s j)) (pack (r j)) = xor2 (pack (s 0)) (pack (r 0)) := by
  constructor
  · intro h j
    induction j using Fin.induction with
    | zero => rfl
    | succ i ih =>
      exact ((block_iff _ _ _ _).1 (h i.castSucc i.succ rfl)).symm.trans ih
  · intro h j j' _
    exact (block_iff _ _ _ _).2 ((h j).trans (h j').symm)

private def used (r : Row) : Finset Bits := univ.image fun j : Fin 7 => pack (r j)

private def offsets (r : Row) : Finset Bits :=
  univ \ (univ.image fun j : Fin 7 => xor2 missing (pack (r j)))

private theorem mem_offsets {r : Row} {v : Bits} :
    v ∈ offsets r ↔ ∀ j, xor2 v (pack (r j)) ≠ missing := by
  simp only [offsets, mem_sdiff, mem_univ, true_and, mem_image, not_exists]
  apply forall_congr'
  intro j
  constructor <;> intro h he <;> apply h <;>
    simpa only [xor_right] using (congrArg (fun u => xor2 u (pack (r j))) he).symm

private def shift (r : Row) (v : Bits) : Row := fun j => unpack (xor2 v (pack (r j)))

private theorem pack_shift {r : Row} {v : Bits} (hv : v ∈ offsets r) (j : Fin 7) :
    pack (shift r v j) = xor2 v (pack (r j)) := pack_unpack _ (mem_offsets.1 hv j)

private def successors (r : Row) : Finset Row := univ.filter (rowOK r)

private theorem successors_image (r : Row) : successors r = (offsets r).image (shift r) := by
  ext s
  simp only [successors, mem_filter, mem_univ, true_and, mem_image, row_constant]
  constructor
  · intro h
    let v := xor2 (pack (s 0)) (pack (r 0))
    have he (j : Fin 7) : xor2 v (pack (r j)) = pack (s j) := by
      change xor2 (xor2 (pack (s 0)) (pack (r 0))) (pack (r j)) = _
      rw [← h j, xor_right]
    have hv : v ∈ offsets r := mem_offsets.2 fun j => by rw [he j]; exact pack_ne_missing _
    exact ⟨v, hv, funext fun j => pack_inj ((pack_shift hv j).trans (he j))⟩
  · rintro ⟨v, hv, rfl⟩ j
    rw [pack_shift hv j, pack_shift hv 0, xor_right, xor_right]

private def weight (r : Row) : ℕ := 4 - (used r).card

private theorem xor_inj (v : Bits) : Function.Injective (xor2 v) := by
  intro u w h
  simpa only [xor_left] using congrArg (xor2 v) h

private theorem successors_card (r : Row) : (successors r).card = weight r := by
  rw [successors_image, card_image_of_injOn]
  · have h : (univ.image fun j : Fin 7 => xor2 missing (pack (r j))).card = (used r).card := by
      change (univ.image (xor2 missing ∘ fun j : Fin 7 => pack (r j))).card = (used r).card
      rw [← image_image, card_image_of_injective _ (xor_inj missing)]
      rfl
    rw [offsets, card_sdiff_of_subset (subset_univ _), h, weight]
    simp [Fintype.card_prod]
  · intro v hv w hw he
    have h := congrArg (fun s : Row => pack (s 0)) he
    change pack (shift r v 0) = pack (shift r w 0) at h
    rw [pack_shift hv, pack_shift hw] at h
    simpa only [xor_right] using congrArg (fun u => xor2 u (pack (r 0))) h

private theorem used_card_eq {r s : Row} (h : rowOK r s) : (used s).card = (used r).card := by
  have hs : s ∈ successors r := mem_filter.2 ⟨mem_univ _, h⟩
  rw [successors_image] at hs
  obtain ⟨v, hv, rfl⟩ := mem_image.1 hs
  have he : used (shift r v) = (used r).image (xor2 v) := by
    unfold used
    rw [image_image]
    congr 1
    funext j
    exact pack_shift hv j
  rw [he, card_image_of_injective _ (xor_inj v)]

private theorem W_pow (n : ℕ) (r : Row) : W n r = weight r ^ n := by
  induction n generalizing r with
  | zero => simp [W_zero]
  | succ n ih =>
    rw [W_succ, ← sum_filter]
    calc
      _ = ∑ s ∈ successors r, weight r ^ n := by
        apply sum_congr rfl
        intro s hs
        have h := used_card_eq (mem_filter.1 hs).2
        simpa only [weight, h] using ih s
      _ = _ := by rw [sum_const, smul_eq_mul, successors_card, pow_succ, Nat.mul_comm]

private def colors (r : Row) : Finset (Fin 3) := univ.image r

private theorem used_card_colors (r : Row) : (used r).card = (colors r).card := by
  change (univ.image (pack ∘ r)).card = (colors r).card
  rw [← image_image, card_image_of_injective _ pack_inj]
  rfl

private def paletteCount (s : Finset (Fin 3)) : ℕ :=
  ((univ : Finset Row).filter (fun r => colors r = s)).card

private theorem palette_sum (s : Finset (Fin 3)) :
    ∑ t ∈ s.powerset, paletteCount t = s.card ^ 7 := by
  let R : Finset Row := univ.filter (fun r => ∀ j, r j ∈ s)
  have hCard : R.card = s.card ^ 7 := by
    let e : {r : Row // ∀ j, r j ∈ s} ≃ (Fin 7 → ↥s) :=
      { toFun := fun r j => ⟨r.1 j, r.2 j⟩
        invFun := fun f => ⟨fun j => (f j).1, fun j => (f j).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [show R.card = Fintype.card {r : Row // ∀ j, r j ∈ s} from
      (Fintype.card_subtype _).symm, Fintype.card_congr e]
    simp
  have hMaps : (R : Set Row).MapsTo colors s.powerset := by
    intro r hr
    have hr' := (mem_filter.1 (show r ∈ R from hr)).2
    apply mem_powerset.2
    intro c hc
    obtain ⟨j, _, rfl⟩ := mem_image.1 hc
    exact hr' j
  rw [← hCard, card_eq_sum_card_fiberwise hMaps]
  apply sum_congr rfl
  intro t ht
  unfold paletteCount
  congr 1
  ext r
  simp only [R, mem_filter, mem_univ, true_and]
  refine ⟨fun he => ⟨?_, he⟩, And.right⟩
  intro j
  apply mem_powerset.1 ht
  rw [← he]
  exact mem_image_of_mem r (mem_univ j)

/-- Counts for an exact palette of zero, one, two, or three colors. -/
private def expected : ℕ → ℕ
  | 1 => 1
  | 2 => 126
  | 3 => 1806
  | _ => 0

private theorem expected_sum : ∀ s : Finset (Fin 3),
    ∑ t ∈ s.powerset, expected t.card = s.card ^ 7 := by decide

private theorem palette_formula (s : Finset (Fin 3)) : paletteCount s = expected s.card := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    have h : ∑ t ∈ s.powerset.erase s, paletteCount t =
        ∑ t ∈ s.powerset.erase s, expected t.card := by
      apply sum_congr rfl
      intro t ht
      exact ih t (ssubset_of_subset_of_ne (mem_powerset.1 (mem_erase.1 ht).2) (mem_erase.1 ht).1)
    have hs := mem_powerset_self s
    have h₁ := (sum_erase_add _ paletteCount hs).trans (palette_sum s)
    have h₂ := (sum_erase_add _ (fun t => expected t.card) hs).trans (expected_sum s)
    omega

private theorem palette_total (n : ℕ) :
    ∑ s : Finset (Fin 3), expected s.card * (4 - s.card) ^ n = 1806 + 378 * 2 ^ n + 3 * 3 ^ n := by
  have h₁ : ∑ s : Finset (Fin 3), (if s.card = 3 then expected s.card else 0) = 1806 := by decide
  have h₂ : ∑ s : Finset (Fin 3), (if s.card = 2 then expected s.card else 0) = 378 := by decide
  have h₃ : ∑ s : Finset (Fin 3), (if s.card = 1 then expected s.card else 0) = 3 := by decide
  calc
    _ = ∑ s : Finset (Fin 3), ((if s.card = 3 then expected s.card else 0) * 1 ^ n +
        (if s.card = 2 then expected s.card else 0) * 2 ^ n +
        (if s.card = 1 then expected s.card else 0) * 3 ^ n) := by
      apply sum_congr rfl
      intro s _
      have h : s.card ≤ 3 := by simpa using card_le_univ s
      interval_cases he : s.card <;> simp [expected]
    _ = _ := by rw [sum_add_distrib, sum_add_distrib, ← sum_mul, ← sum_mul, ← sum_mul,
      h₁, h₂, h₃, one_pow, mul_one]

private theorem a_formula (n : ℕ) : a n = 1806 + 378 * 2 ^ n + 3 * 3 ^ n := by
  rw [a_eq, cnt_sum]
  simp only [W_pow, weight, used_card_colors]
  rw [← sum_fiberwise_of_maps_to' (g := colors) (t := univ) (fun _ _ => mem_univ _)
    (fun s => (4 - s.card) ^ n)]
  simp only [sum_const, smul_eq_mul]
  change (∑ s : Finset (Fin 3), paletteCount s * (4 - s.card) ^ n) = _
  simp only [palette_formula]
  exact palette_total n

private theorem a_rec (k : ℕ) : (a (k + 3) : ℚ) + 11 * (a (k + 1) : ℚ) =
    6 * (a (k + 2) : ℚ) + 6 * (a (k + 0) : ℚ) := by
  simp only [a_formula, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
  ring

private theorem a1 : (a 1 : ℚ) = 2571 := by norm_num [a_formula]
private theorem a2 : (a 2 : ℚ) = 3345 := by norm_num [a_formula]
private theorem a3 : (a 3 : ℚ) = 4911 := by norm_num [a_formula]

private theorem closed : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 3 * (602 + 63 * 2 ^ (1 + n) + 3 ^ n) := by
  intro n _
  simp only [a_formula, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
  ring

/-- The g.f. as stated. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) * (1 - 2 * X) * (1 - 3 * X)) =
      3 * X * (857 - 4027 * X + 4374 * X ^ 2) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) * (1 - 2 * X) * (1 - 3 * X)) = A - C (6 : ℚ) * (A * X ^ 1) + C (11 : ℚ) * (A * X ^ 2) - C (6 : ℚ) * (A * X ^ 3) := by
    rw [show (C (6 : ℚ) : ℚ⟦X⟧) = 6 from map_ofNat C 6, show (C (11 : ℚ) : ℚ⟦X⟧) = 11 from map_ofNat C 11]
    ring
  have e2 : (3 * X * (857 - 4027 * X + 4374 * X ^ 2) : ℚ⟦X⟧) = C (2571 : ℚ) * X ^ 1 - C (12081 : ℚ) * X ^ 2 + C (13122 : ℚ) * X ^ 3 := by
    rw [show (C (2571 : ℚ) : ℚ⟦X⟧) = 2571 from map_ofNat C 2571, show (C (12081 : ℚ) : ℚ⟦X⟧) = 12081 from map_ofNat C 12081, show (C (13122 : ℚ) : ℚ⟦X⟧) = 13122 from map_ofNat C 13122]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_C, hA,
    coeff_mk]
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> norm_num only [a1, a2, a3, if_true, if_false]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    have h' := (show (a (k + 4) : ℚ) + 11 * (a (k + 2) : ℚ) = 6 * (a (k + 3) : ℚ) + 6 * (a (k + 1) : ℚ) by simpa only [Nat.add_assoc, Nat.reduceAdd] using a_rec (k + 1))
    simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega, show k + 4 - 3 = k + 1 by omega, show ¬ (k + 4 = 0) by omega, show ¬ (k + 3 = 0) by omega, show ¬ (k + 2 = 0) by omega, show ¬ (k + 1 = 0) by omega, show 1 ≤ k + 4 by omega, show 2 ≤ k + 4 by omega, show 3 ≤ k + 4 by omega, show ¬ (k + 4 = 0) by omega, show ¬ (k + 4 = 1) by omega, show ¬ (k + 4 = 2) by omega, show ¬ (k + 4 = 3) by omega, if_true, if_false]
    linear_combination h'

/-- Controls: the entry's data. -/
theorem controls : a 1 = 2571 ∧ a 2 = 3345 ∧ a 3 = 4911 ∧ a 4 = 8097 ∧ a 5 = 14631 ∧ a 6 = 28185 ∧ a 7 = 56751 ∧ a 8 = 118257 ∧ a 9 = 254391 ∧ a 10 = 566025 ∧ a 11 = 1307391 ∧ a 12 = 3144417 ∧ a 13 = 7881351 ∧ a 14 = 20543865 ∧ a 15 = 55434831 ∧ a 16 = 153914577 ∧ a 17 = 436967511 ∧ a 18 = 1261353705 ∧ a 19 = 3684967071 ∧ a 20 = 10856716737 ∧ a 21 = 32173784871 ∧ a 22 = 95728627545 ∧ a 23 = 285600432111 := by
  norm_num [a_formula]

/-- The conjunction stated as `main`. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 2 * X) * (1 - 3 * X)) =
        3 * X * (857 - 4027 * X + 4374 * X ^ 2) ∧
      ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 3 * (602 + 63 * 2 ^ (1 + n) + 3 ^ n) :=
  ⟨gf, closed⟩

end OMA.S_oeis_a235882

theorem OMA.solution : type_of% @OMA.S_oeis_a235882.main :=
  OMA.S_oeis_a235882.conjecture
