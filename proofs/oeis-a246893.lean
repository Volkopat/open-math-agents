import OMAStatements.S_oeis_a246893
import Mathlib
-- Credit: @ptc-prover-bot

/-!
Proof idea. Two entries sum to `n` exactly when one is the reversal `Fin.rev` of the other.
Count the complement: tuples with no two positions holding complementary values. Build such a
tuple one letter at a time (first-letter recursion). For a valid prefix with value set `S`
(`d = #S`, `mu` = number of fixed points of `rev` in `S`, at most one), a new letter `a` is
allowed iff `rev a` is not in `S`, and the new state depends only on whether `a` is in `S` and
whether `a` is the fixed point. This gives a linear operator `Tφ` on functions of `(d, mu)`
with `#complement = Tφ^5 1 (0, 0)`, an explicit polynomial in `n` and `eps` (the number of
fixed points of `rev`, `1` for even `n`, `0` for odd `n`). The generating function then
follows coefficientwise from the closed form
`a n = -7 + 15n/2 + 25n^2 - 5n^3 + 10n^4 + (-1)^n (8 - 25n/2 + 5n^2)`.
Same method as our proof of A245951 (window of length 4), here with one window of length 5.
-/

namespace A246893Proof

open OMA.S_oeis_a246893 PowerSeries Finset

variable {n : ℕ}

/-- No two different positions hold complementary values. -/
def Valid {k : ℕ} (x : Fin k → Fin (n + 1)) : Prop :=
  ∀ s t : Fin k, s ≠ t → x t ≠ Fin.rev (x s)

instance {k : ℕ} (x : Fin k → Fin (n + 1)) : Decidable (Valid x) := by
  unfold Valid; infer_instance

/-- A value set without a complementary pair of distinct values. -/
def SValid (S : Finset (Fin (n + 1))) : Prop := ∀ v ∈ S, Fin.rev v ∈ S → Fin.rev v = v

/-- Number of fixed points of `rev` in `S`. -/
def mu (S : Finset (Fin (n + 1))) : ℕ := #(S.filter (fun v => Fin.rev v = v))

/-- Number of fixed points of `rev` on `Fin (n + 1)`. -/
def eps (n : ℕ) : ℕ := #((univ : Finset (Fin (n + 1))).filter (fun v => Fin.rev v = v))

/-- The transfer operator on functions of the state `(d, mu)`. -/
def Tφ (n : ℕ) (φ : ℕ → ℕ → ℤ) (d m : ℕ) : ℤ :=
  ((d : ℤ) - m) * φ d m + ((n : ℤ) + 1 - 2 * d + 2 * m - eps n) * φ (d + 1) m +
    ((eps n : ℤ) - m) * φ (d + 1) (m + 1)

/-- Weighted count of valid tuples of length `k`. -/
def W (n k : ℕ) (φ : ℕ → ℕ → ℤ) : ℤ :=
  ∑ x : Fin k → Fin (n + 1),
    if Valid x then φ (#(univ.image x)) (mu (univ.image x)) else 0

lemma K (S : Finset (Fin (n + 1))) (hS : SValid S) (φ : ℕ → ℕ → ℤ) :
    ∑ a : Fin (n + 1), (if Fin.rev a ∈ S then 0 else φ (#(insert a S)) (mu (insert a S))) =
      Tφ n φ (#S) (mu S) := by
  have hpt : ∀ a : Fin (n + 1),
      (if Fin.rev a ∈ S then 0 else φ (#(insert a S)) (mu (insert a S))) =
        ((if a ∈ S then (1 : ℤ) else 0) - (if a ∈ S ∧ Fin.rev a = a then 1 else 0)) *
            φ (#S) (mu S) +
          (1 - (if a ∈ S then (1 : ℤ) else 0) - (if Fin.rev a ∈ S then 1 else 0) +
              2 * (if a ∈ S ∧ Fin.rev a = a then 1 else 0) - (if Fin.rev a = a then 1 else 0)) *
            φ (#S + 1) (mu S) +
          ((if Fin.rev a = a then (1 : ℤ) else 0) - (if a ∈ S ∧ Fin.rev a = a then 1 else 0)) *
            φ (#S + 1) (mu S + 1) := by
    intro a
    by_cases h1 : a ∈ S <;> by_cases h2 : Fin.rev a ∈ S <;> by_cases h3 : Fin.rev a = a
    · simp [h1, h2, h3]
    · exact absurd (hS a h1 h2) h3
    · exact absurd (by rw [h3]; exact h1) h2
    · simp [h1, h2, h3, insert_eq_of_mem h1]
    · exact absurd (h3 ▸ h2) h1
    · simp [h1, h2, h3]
    · have hm : a ∉ S.filter (fun v => Fin.rev v = v) := by simp [h1]
      simp [h1, h2, h3, card_insert_of_notMem h1, mu, filter_insert, card_insert_of_notMem hm]
    · simp [h1, h2, h3, card_insert_of_notMem h1, mu, filter_insert]
  rw [sum_congr rfl (fun a _ => hpt a)]
  simp only [sum_add_distrib, ← sum_mul]
  have c1 : #((univ : Finset (Fin (n + 1))).filter (fun a => a ∈ S)) = #S := by
    congr 1; ext a; simp
  have c2 : #((univ : Finset (Fin (n + 1))).filter (fun a => Fin.rev a ∈ S)) = #S := by
    rw [show (univ : Finset (Fin (n + 1))).filter (fun a => Fin.rev a ∈ S) = S.image Fin.rev by
      ext a
      simp only [mem_filter, mem_univ, true_and, mem_image]
      constructor
      · intro h; exact ⟨Fin.rev a, h, Fin.rev_rev a⟩
      · rintro ⟨b, hb, rfl⟩; rwa [Fin.rev_rev]]
    exact card_image_of_injective _ Fin.rev_injective
  have c3 : #((univ : Finset (Fin (n + 1))).filter (fun a => a ∈ S ∧ Fin.rev a = a)) = mu S := by
    unfold mu; congr 1; ext a; simp
  have hA : ∑ a : Fin (n + 1), ((if a ∈ S then (1 : ℤ) else 0) -
      (if a ∈ S ∧ Fin.rev a = a then 1 else 0)) = (#S : ℤ) - mu S := by
    rw [sum_sub_distrib, sum_boole, sum_boole, c1, c3]
  have hC : ∑ a : Fin (n + 1), ((if Fin.rev a = a then (1 : ℤ) else 0) -
      (if a ∈ S ∧ Fin.rev a = a then 1 else 0)) = (eps n : ℤ) - mu S := by
    rw [sum_sub_distrib, sum_boole, sum_boole, c3]; rfl
  have hB : ∑ a : Fin (n + 1), (1 - (if a ∈ S then (1 : ℤ) else 0) -
      (if Fin.rev a ∈ S then 1 else 0) + 2 * (if a ∈ S ∧ Fin.rev a = a then 1 else 0) -
      (if Fin.rev a = a then 1 else 0)) = (n : ℤ) + 1 - 2 * #S + 2 * mu S - eps n := by
    rw [sum_sub_distrib, sum_add_distrib, sum_sub_distrib, sum_sub_distrib, ← mul_sum,
      sum_boole, sum_boole, sum_boole, sum_boole, c1, c2, c3]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    unfold eps
    push_cast
    ring
  rw [hA, hB, hC]
  unfold Tφ
  push_cast
  ring

lemma valid_cons {k : ℕ} (a : Fin (n + 1)) (x : Fin k → Fin (n + 1)) :
    Valid (Fin.cons a x : Fin (k + 1) → Fin (n + 1)) ↔ Valid x ∧ ∀ t, x t ≠ Fin.rev a := by
  constructor
  · intro h
    refine ⟨fun s t hst => ?_, fun t => ?_⟩
    · have := h s.succ t.succ (fun e => hst (Fin.succ_injective _ e))
      simpa using this
    · have := h 0 t.succ (Fin.succ_ne_zero t).symm
      simpa using this
  · rintro ⟨h1, h2⟩ s t hst
    induction s using Fin.cases with
    | zero =>
      induction t using Fin.cases with
      | zero => exact absurd rfl hst
      | succ t => simpa using h2 t
    | succ s =>
      induction t using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        intro e
        apply h2 s
        rw [e, Fin.rev_rev]
      | succ t =>
        simp only [Fin.cons_succ]
        exact h1 s t (fun e => hst (by rw [e]))

lemma image_cons {k : ℕ} (a : Fin (n + 1)) (x : Fin k → Fin (n + 1)) :
    univ.image (Fin.cons a x : Fin (k + 1) → Fin (n + 1)) = insert a (univ.image x) := by
  ext v
  simp only [mem_image, mem_univ, true_and, mem_insert, Fin.exists_fin_succ, Fin.cons_zero,
    Fin.cons_succ]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h

lemma valid_svalid {k : ℕ} {x : Fin k → Fin (n + 1)} (hx : Valid x) : SValid (univ.image x) := by
  intro v hv hr
  simp only [mem_image, mem_univ, true_and] at hv hr
  obtain ⟨s, rfl⟩ := hv
  obtain ⟨t, ht⟩ := hr
  by_cases hst : s = t
  · subst hst
    exact ht.symm
  · exact absurd ht (hx s t hst)

lemma sum_cons {α : Type*} [Fintype α] [DecidableEq α] (k : ℕ) (f : (Fin (k + 1) → α) → ℤ) :
    ∑ w, f w = ∑ a, ∑ v : Fin k → α, f (Fin.cons a v) := by
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => α) (fun p => f (Fin.cons p.1 p.2)) f
    (fun p => rfl), Fintype.sum_prod_type]

lemma step (k : ℕ) (φ : ℕ → ℕ → ℤ) : W n (k + 1) φ = W n k (Tφ n φ) := by
  unfold W
  rw [sum_cons, Finset.sum_comm]
  refine sum_congr rfl (fun x _ => ?_)
  by_cases hx : Valid x
  · rw [if_pos hx, ← K _ (valid_svalid hx)]
    refine sum_congr rfl (fun a _ => ?_)
    rw [image_cons]
    by_cases h : Fin.rev a ∈ univ.image x
    · have : ¬ Valid (Fin.cons a x : Fin (k + 1) → Fin (n + 1)) := by
        rw [valid_cons]
        simp only [mem_image, mem_univ, true_and] at h
        obtain ⟨t, ht⟩ := h
        exact fun hh => hh.2 t ht
      rw [if_neg this, if_pos h]
    · have : Valid (Fin.cons a x : Fin (k + 1) → Fin (n + 1)) := by
        rw [valid_cons]
        exact ⟨hx, fun t ht => h (mem_image.2 ⟨t, mem_univ _, ht⟩)⟩
      rw [if_pos this, if_neg h]
  · rw [if_neg hx]
    refine sum_eq_zero (fun a _ => ?_)
    have : ¬ Valid (Fin.cons a x : Fin (k + 1) → Fin (n + 1)) := by
      rw [valid_cons]
      exact fun hh => hx hh.1
    rw [if_neg this]

lemma base (φ : ℕ → ℕ → ℤ) : W n 0 φ = φ 0 0 := by
  unfold W
  rw [Fintype.sum_unique]
  split_ifs with h
  · simp [mu]
  · exact absurd (fun s => s.elim0) h

lemma good_iff (x : Fin 5 → Fin (n + 1)) : good x = true ↔ ¬ Valid x := by
  unfold good Valid
  rw [decide_eq_true_iff]
  push_neg
  constructor
  · intro h
    obtain ⟨s, hs, t, ht, hst, he⟩ := h 0 (by norm_num)
    simp only [zero_add] at he
    unfold OMA.S_oeis_a246893.get at he
    rw [dif_pos hs, dif_pos ht] at he
    refine ⟨⟨s, hs⟩, ⟨t, ht⟩, ?_, ?_⟩
    · intro e
      have := congrArg Fin.val e
      simp at this
      omega
    · ext
      simp only [Fin.val_rev]
      omega
  · rintro ⟨s, t, hst, he⟩ i hi
    have hi0 : i = 0 := by omega
    subst hi0
    have hv : (x s : ℕ) + x t = n := by
      rw [he, Fin.val_rev]
      have := (x s).isLt
      omega
    have hs := s.isLt
    have ht := t.isLt
    rcases lt_or_gt_of_ne hst with h | h
    · refine ⟨s, hs, t, ht, Fin.lt_def.mp h, ?_⟩
      simp only [zero_add, OMA.S_oeis_a246893.get, dif_pos hs, dif_pos ht]
      exact hv
    · refine ⟨t, ht, s, hs, Fin.lt_def.mp h, ?_⟩
      simp only [zero_add, OMA.S_oeis_a246893.get, dif_pos hs, dif_pos ht, Fin.eta]
      omega

lemma a_eq (n : ℕ) : a n = ((n : ℤ) + 1) ^ 5 - W n 5 (fun _ _ => 1) := by
  unfold a W
  rw [card_filter]
  push_cast
  have : ∀ x : Fin 5 → Fin (n + 1),
      (if good x = true then (1 : ℤ) else 0) = 1 - if Valid x then 1 else 0 := by
    intro x
    by_cases h : Valid x
    · have : ¬ good x = true := fun hg => (good_iff x).1 hg h
      simp [h, this]
    · have : good x = true := (good_iff x).2 h
      simp [h, this]
  rw [sum_congr rfl (fun x _ => this x), sum_sub_distrib]
  simp

lemma eps_even (m : ℕ) : eps (2 * m) = 1 := by
  unfold eps
  rw [card_eq_one]
  refine ⟨⟨m, by omega⟩, ?_⟩
  ext v
  simp only [mem_filter, mem_univ, true_and, mem_singleton, Fin.ext_iff, Fin.val_rev]
  omega

lemma eps_odd (m : ℕ) : eps (2 * m + 1) = 0 := by
  unfold eps
  rw [card_eq_zero, filter_eq_empty_iff]
  intro v _ h
  have := congrArg Fin.val h
  simp only [Fin.val_rev] at this
  omega

lemma B5 (n : ℕ) :
    W n 5 (fun _ _ => 1) = Tφ n (Tφ n (Tφ n (Tφ n (Tφ n (fun _ _ => 1))))) 0 0 := by
  rw [step, step, step, step, step, base]

lemma a_even (m : ℕ) :
    a (2 * m) = 1 - 5 * (2 * m : ℤ) + 30 * (2 * m : ℤ) ^ 2 - 5 * (2 * m : ℤ) ^ 3 +
      10 * (2 * m : ℤ) ^ 4 := by
  rw [a_eq, B5]
  simp only [Tφ, eps_even]
  push_cast
  ring

lemma a_odd (m : ℕ) :
    a (2 * m + 1) = -15 + 20 * (2 * m + 1 : ℤ) + 20 * (2 * m + 1 : ℤ) ^ 2 -
      5 * (2 * m + 1 : ℤ) ^ 3 + 10 * (2 * m + 1 : ℤ) ^ 4 := by
  rw [a_eq, B5]
  simp only [Tφ, eps_odd]
  push_cast
  ring

lemma a_closed (n : ℕ) : (a n : ℚ) =
    -7 + 15 / 2 * n + 25 * n ^ 2 - 5 * n ^ 3 + 10 * n ^ 4 +
      (-1) ^ n * (8 - 25 / 2 * n + 5 * n ^ 2) := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [a_even m]
    have : ((-1 : ℚ)) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
    rw [this]
    push_cast
    ring
  · rw [a_odd m]
    have : ((-1 : ℚ)) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [this]
    push_cast
    ring

lemma gf : PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) *
    ((1 - X) ^ 5 * (1 + X) ^ 3 : PowerSeries ℚ) =
      X * (30 + 171 * X + 378 * X ^ 2 + 619 * X ^ 3 + 394 * X ^ 4 + 329 * X ^ 5 - 2 * X ^ 6 +
        X ^ 7) := by
  set F := PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) with hF
  have e2 : (C (2 : ℚ) : PowerSeries ℚ) = 2 := map_ofNat C 2
  have e6 : (C (6 : ℚ) : PowerSeries ℚ) = 6 := map_ofNat C 6
  have e30 : (C (30 : ℚ) : PowerSeries ℚ) = 30 := map_ofNat C 30
  have e171 : (C (171 : ℚ) : PowerSeries ℚ) = 171 := map_ofNat C 171
  have e378 : (C (378 : ℚ) : PowerSeries ℚ) = 378 := map_ofNat C 378
  have e619 : (C (619 : ℚ) : PowerSeries ℚ) = 619 := map_ofNat C 619
  have e394 : (C (394 : ℚ) : PowerSeries ℚ) = 394 := map_ofNat C 394
  have e329 : (C (329 : ℚ) : PowerSeries ℚ) = 329 := map_ofNat C 329
  have hL : F * ((1 - X) ^ 5 * (1 + X) ^ 3 : PowerSeries ℚ) = F - C 2 * (F * X ^ 1) -
      C 2 * (F * X ^ 2) + C 6 * (F * X ^ 3) - C 6 * (F * X ^ 5) + C 2 * (F * X ^ 6) +
      C 2 * (F * X ^ 7) - F * X ^ 8 := by
    rw [e2, e6]; ring
  have hR : (X * (30 + 171 * X + 378 * X ^ 2 + 619 * X ^ 3 + 394 * X ^ 4 + 329 * X ^ 5 -
      2 * X ^ 6 + X ^ 7) : PowerSeries ℚ) =
      C 30 * X ^ 1 + C 171 * X ^ 2 + C 378 * X ^ 3 + C 619 * X ^ 4 + C 394 * X ^ 5 +
        C 329 * X ^ 6 - C 2 * X ^ 7 + X ^ 8 := by
    rw [e2, e30, e171, e378, e619, e394, e329]; ring
  rw [hL, hR]
  ext k
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', hF, coeff_mk, coeff_C_mul_X_pow,
    coeff_X_pow, coeff_C]
  rcases (by omega : k < 9 ∨ 9 ≤ k) with hk | hk
  · interval_cases k <;> norm_num [a_closed]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 9 := ⟨k - 9, by omega⟩
    simp only [show (1 : ℕ) ≤ j + 9 by omega, show (2 : ℕ) ≤ j + 9 by omega,
      show (3 : ℕ) ≤ j + 9 by omega, show (5 : ℕ) ≤ j + 9 by omega,
      show (6 : ℕ) ≤ j + 9 by omega, show (7 : ℕ) ≤ j + 9 by omega,
      show (8 : ℕ) ≤ j + 9 by omega,
      show j + 9 - 1 = j + 8 by omega, show j + 9 - 2 = j + 7 by omega,
      show j + 9 - 3 = j + 6 by omega, show j + 9 - 5 = j + 4 by omega,
      show j + 9 - 6 = j + 3 by omega, show j + 9 - 7 = j + 2 by omega,
      show j + 9 - 8 = j + 1 by omega,
      show ¬ (j + 9 < 1) by omega, show ¬ (j + 8 < 1) by omega, show ¬ (j + 7 < 1) by omega,
      show ¬ (j + 6 < 1) by omega, show ¬ (j + 4 < 1) by omega, show ¬ (j + 3 < 1) by omega,
      show ¬ (j + 2 < 1) by omega, show ¬ (j + 1 < 1) by omega,
      show ¬ (j + 9 = 1) by omega, show ¬ (j + 9 = 2) by omega, show ¬ (j + 9 = 3) by omega,
      show ¬ (j + 9 = 4) by omega, show ¬ (j + 9 = 5) by omega, show ¬ (j + 9 = 6) by omega,
      show ¬ (j + 9 = 7) by omega, show ¬ (j + 9 = 8) by omega,
      if_true, if_false, a_closed]
    push_cast
    ring

theorem main' :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) *
      ((1 - X) ^ 5 * (1 + X) ^ 3 : PowerSeries ℚ) =
        X * (30 + 171 * X + 378 * X ^ 2 + 619 * X ^ 3 + 394 * X ^ 4 + 329 * X ^ 5 -
          2 * X ^ 6 + X ^ 7)) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = 1 - 5 * (n : ℚ) + 30 * (n : ℚ) ^ 2 -
      5 * (n : ℚ) ^ 3 + 10 * (n : ℚ) ^ 4) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = -15 + 20 * (n : ℚ) + 20 * (n : ℚ) ^ 2 -
      5 * (n : ℚ) ^ 3 + 10 * (n : ℚ) ^ 4) := by
  refine ⟨gf, fun n _ he => ?_, fun n _ ho => ?_⟩
  · rw [a_closed, he.neg_one_pow]
    ring
  · rw [a_closed, ho.neg_one_pow]
    ring

end A246893Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a246893.main := A246893Proof.main'

