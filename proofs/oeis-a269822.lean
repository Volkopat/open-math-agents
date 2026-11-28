import OMAStatements.S_oeis_a269822

-- Problem: OEIS A269822, the number of words of length n over 0..4 with exactly one adjacent pair
-- of sum 4. Conjectures: a(n) = 8 a(n-1) - 16 a(n-2), the generating function
-- 5 x^2 / (1 - 4 x)^2, and a(n) = 5 * 4^(n-2) * (n-1).
-- Proof, for q letters and target sum q - 1. Every letter has exactly one partner making the
-- sum q - 1. Prepending a letter to a word either creates one more such pair (1 choice) or not
-- (q - 1 choices), so the numbers W(m,k) of words of length m+1 with k pairs satisfy
-- W(m+1,0) = (q-1) W(m,0) and W(m+1,1) = W(m,0) + (q-1) W(m,1). Hence W(m,0) = q (q-1)^m and
-- W(m+1,1) = q (m+1) (q-1)^m, which gives the closed form; the recurrence and the generating
-- function follow from it.

open Finset

/-- Number of adjacent pairs of the word `x` (length `m + 1`, letters in `Fin q`) with sum `T`. -/
def OMA.pairs (q T m : ℕ) (x : Fin (m + 1) → Fin q) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => (x i.castSucc : ℕ) + (x i.succ : ℕ) = T)).card

/-- Number of words of length `m + 1` with exactly `k` adjacent pairs of sum `T`. -/
def OMA.W (q T m k : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin (m + 1) → Fin q => OMA.pairs q T m x = k)).card

lemma OMA.pairs_cons (q T m : ℕ) (y : Fin q) (x : Fin (m + 1) → Fin q) :
    OMA.pairs q T (m + 1) (Fin.cons y x : Fin (m + 1 + 1) → Fin q)
      = (if (y : ℕ) + (x 0 : ℕ) = T then 1 else 0) + OMA.pairs q T m x := by
  unfold OMA.pairs
  rw [Fin.card_filter_univ_succ']
  have h0 : ((Fin.cons y x : Fin (m + 1 + 1) → Fin q) (Fin.castSucc (0 : Fin (m + 1))) : ℕ) = (y : ℕ) := by
    rw [Fin.castSucc_zero, Fin.cons_zero]
  have h1 : ((Fin.cons y x : Fin (m + 1 + 1) → Fin q) (Fin.succ (0 : Fin (m + 1))) : ℕ) = (x 0 : ℕ) := by
    rw [Fin.cons_succ]
  have h2 : ∀ j : Fin m, ((Fin.cons y x : Fin (m + 1 + 1) → Fin q) (Fin.castSucc (Fin.succ j)) : ℕ)
      = (x (Fin.castSucc j) : ℕ) := by
    intro j
    rw [← Fin.succ_castSucc, Fin.cons_succ]
  have h3 : ∀ j : Fin m, ((Fin.cons y x : Fin (m + 1 + 1) → Fin q) (Fin.succ (Fin.succ j)) : ℕ)
      = (x (Fin.succ j) : ℕ) := by
    intro j
    rw [Fin.cons_succ]
  simp only [h0, h1, h2, h3]

lemma OMA.W_step (q T m k : ℕ)
    (hT : ∀ v : Fin q, (univ.filter (fun y : Fin q => (y : ℕ) + (v : ℕ) = T)).card = 1) :
    OMA.W q T (m + 1) k
      = (univ.filter (fun x : Fin (m + 1) → Fin q => 1 + OMA.pairs q T m x = k)).card
        + (q - 1) * OMA.W q T m k := by
  unfold OMA.W
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter,
    ← (Fin.consEquiv (fun _ : Fin (m + 1 + 1) => Fin q)).sum_comp, Fintype.sum_prod_type_right,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hx : ∀ y : Fin q,
      (if OMA.pairs q T (m + 1) ((Fin.consEquiv (fun _ : Fin (m + 1 + 1) => Fin q)) (y, x)) = k
        then 1 else 0)
      = if (y : ℕ) + (x 0 : ℕ) = T then (if 1 + OMA.pairs q T m x = k then 1 else 0)
        else (if OMA.pairs q T m x = k then 1 else 0) := by
    intro y
    have h := OMA.pairs_cons q T m y x
    have he : (Fin.consEquiv (fun _ : Fin (m + 1 + 1) => Fin q)) (y, x)
        = (Fin.cons y x : Fin (m + 1 + 1) → Fin q) := rfl
    rw [he, h]
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl (fun y _ => hx y), Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    hT (x 0)]
  have hc : (univ.filter (fun y : Fin q => ¬ ((y : ℕ) + (x 0 : ℕ) = T))).card = q - 1 := by
    have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin q)))
      (fun y : Fin q => (y : ℕ) + (x 0 : ℕ) = T)
    rw [hT (x 0), Finset.card_univ, Fintype.card_fin] at h
    omega
  rw [hc]
  simp

lemma OMA.W00 (q T : ℕ) : OMA.W q T 0 0 = q := by
  unfold OMA.W OMA.pairs
  simp

lemma OMA.W01 (q T : ℕ) : OMA.W q T 0 1 = 0 := by
  unfold OMA.W OMA.pairs
  simp

lemma OMA.W0 (q T : ℕ)
    (hT : ∀ v : Fin q, (univ.filter (fun y : Fin q => (y : ℕ) + (v : ℕ) = T)).card = 1) (m : ℕ) :
    OMA.W q T m 0 = q * (q - 1) ^ m := by
  induction m with
  | zero => rw [OMA.W00]; simp
  | succ m ih =>
    rw [OMA.W_step q T m 0 hT, ih]
    have h : (univ.filter (fun x : Fin (m + 1) → Fin q => 1 + OMA.pairs q T m x = 0)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _
      omega
    rw [h, pow_succ]
    ring

lemma OMA.W1 (q T : ℕ)
    (hT : ∀ v : Fin q, (univ.filter (fun y : Fin q => (y : ℕ) + (v : ℕ) = T)).card = 1) (m : ℕ) :
    OMA.W q T (m + 1) 1 = q * (m + 1) * (q - 1) ^ m := by
  have hstep : ∀ m, OMA.W q T (m + 1) 1 = OMA.W q T m 0 + (q - 1) * OMA.W q T m 1 := by
    intro m
    rw [OMA.W_step q T m 1 hT]
    congr 1
    unfold OMA.W
    congr 1
    refine Finset.filter_congr (fun x _ => ?_)
    omega
  induction m with
  | zero => rw [hstep, OMA.W00, OMA.W01]; simp
  | succ m ih =>
    rw [hstep, ih, OMA.W0 q T hT, pow_succ]
    ring

open OMA.S_oeis_a269822 PowerSeries

lemma OMA.hT : ∀ v : Fin 5, (univ.filter (fun y : Fin 5 => (y : ℕ) + (v : ℕ) = 4)).card = 1 := by
  decide

lemma OMA.a_zero : a 0 = 0 := rfl

lemma OMA.a_one : a 1 = 0 := by
  have h := OMA.W01 5 4
  exact h

lemma OMA.a_two (m : ℕ) : a (m + 2) = 5 * (m + 1) * 4 ^ m := by
  have h := OMA.W1 5 4 OMA.hT m
  have h2 : (5 - 1 : ℕ) = 4 := rfl
  rw [h2] at h
  exact h

lemma OMA.a_rec (n : ℕ) : (a (n + 3) : ℤ) = 8 * a (n + 2) - 16 * a (n + 1) := by
  rcases n with _ | k
  · rw [OMA.a_two 1, OMA.a_two 0, OMA.a_one]
    norm_num
  · have e3 : k + 1 + 3 = (k + 2) + 2 := rfl
    have e2 : k + 1 + 2 = (k + 1) + 2 := rfl
    have e1 : k + 1 + 1 = k + 2 := rfl
    rw [e3, e2, e1, OMA.a_two, OMA.a_two, OMA.a_two]
    push_cast
    ring

lemma OMA.coeff_rat_mul (z : ℚ) (g : ℚ⟦X⟧) (n : ℕ) :
    coeff n ((C z : ℚ⟦X⟧) * g) = z * coeff n g := by
  rw [coeff_C_mul]

lemma OMA.gf : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 4 * X) ^ 2 = 5 * X ^ 2 := by
  have hL : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 4 * X) ^ 2
      = PowerSeries.mk (fun n => (a n : ℚ)) + C (-8 : ℚ) * (X * PowerSeries.mk (fun n => (a n : ℚ)))
        + C (16 : ℚ) * (X * (X * PowerSeries.mk (fun n => (a n : ℚ)))) := by
    simp only [map_neg, map_ofNat]
    ring
  have hR : (5 * X ^ 2 : ℚ⟦X⟧) = C (5 : ℚ) * X ^ 2 := by
    simp only [map_ofNat]
  rw [hL, hR]
  ext n
  rcases n with _ | _ | _ | n
  · simp [OMA.a_zero]
  · have e1 : coeff (0 + 1) (X * PowerSeries.mk (fun n => (a n : ℚ)) : ℚ⟦X⟧)
        = coeff 0 (PowerSeries.mk (fun n => (a n : ℚ)) : ℚ⟦X⟧) := coeff_succ_X_mul 0 _
    have e2 : coeff (0 + 1) (X * (X * PowerSeries.mk (fun n => (a n : ℚ))) : ℚ⟦X⟧) = 0 := by
      rw [coeff_succ_X_mul, coeff_zero_X_mul]
    rw [map_add, map_add, OMA.coeff_rat_mul, OMA.coeff_rat_mul, OMA.coeff_rat_mul, e1, e2,
      coeff_mk, coeff_mk, coeff_X_pow, OMA.a_zero, OMA.a_one]
    norm_num
  · have e1 : coeff (0 + 1 + 1) (X * PowerSeries.mk (fun n => (a n : ℚ)) : ℚ⟦X⟧)
        = coeff (0 + 1) (PowerSeries.mk (fun n => (a n : ℚ)) : ℚ⟦X⟧) := coeff_succ_X_mul (0 + 1) _
    have e2 : coeff (0 + 1 + 1) (X * (X * PowerSeries.mk (fun n => (a n : ℚ))) : ℚ⟦X⟧)
        = coeff 0 (PowerSeries.mk (fun n => (a n : ℚ)) : ℚ⟦X⟧) := by
      rw [coeff_succ_X_mul, coeff_succ_X_mul]
    have h2 : a (0 + 1 + 1) = 5 := by
      have h := OMA.a_two 0
      simpa using h
    rw [map_add, map_add, OMA.coeff_rat_mul, OMA.coeff_rat_mul, OMA.coeff_rat_mul, e1, e2,
      coeff_mk, coeff_mk, coeff_mk, coeff_X_pow, OMA.a_zero, h2]
    have h1 : a (0 + 1) = 0 := OMA.a_one
    rw [h1]
    norm_num
  · have e1 : coeff (n + 1 + 1 + 1) (X * PowerSeries.mk (fun n => (a n : ℚ)) : ℚ⟦X⟧)
        = coeff (n + 1 + 1) (PowerSeries.mk (fun n => (a n : ℚ)) : ℚ⟦X⟧) := coeff_succ_X_mul (n + 1 + 1) _
    have e2 : coeff (n + 1 + 1 + 1) (X * (X * PowerSeries.mk (fun n => (a n : ℚ))) : ℚ⟦X⟧)
        = coeff (n + 1) (PowerSeries.mk (fun n => (a n : ℚ)) : ℚ⟦X⟧) := by
      rw [coeff_succ_X_mul, coeff_succ_X_mul]
    have hr : (a (n + 1 + 1 + 1) : ℚ) = 8 * a (n + 1 + 1) - 16 * a (n + 1) := by
      exact_mod_cast OMA.a_rec n
    have hne : ¬ (n + 1 + 1 + 1 = 2) := by omega
    rw [map_add, map_add, OMA.coeff_rat_mul, OMA.coeff_rat_mul, OMA.coeff_rat_mul, e1, e2,
      coeff_mk, coeff_mk, coeff_mk, coeff_X_pow, if_neg hne, hr]
    ring

theorem OMA.solution : type_of% @OMA.S_oeis_a269822.main := by
  refine ⟨?_, OMA.gf, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    exact OMA.a_rec k
  · intro n hn
    rcases n with _ | _ | k
    · omega
    · simp [OMA.a_one]
    · have h0 := OMA.a_two k
      have h1 : k + 1 + 1 - 2 = k := rfl
      have h2 : k + 1 + 1 - 1 = k + 1 := rfl
      rw [h0, h1, h2]
      ring
