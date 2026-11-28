import OMAStatements.S_oeis_a238923
import Mathlib

namespace OMA.S_oeis_a238923

open Finset PowerSeries

private def wordAt {n : ℕ} (w : Fin n → Fin 4) (i : ℕ) : Fin 4 :=
  if h : i < n then w ⟨i, h⟩ else 0

private theorem wordAt_get {n : ℕ} (w : Fin n → Fin 4) (i : Fin n) :
    wordAt w i.val = w i := by simp [wordAt, i.isLt]

private theorem wordAt_tail {n : ℕ} (w : Fin (n + 1) → Fin 4) (i : ℕ) :
    wordAt (Fin.tail w) i = wordAt w (i + 1) := by
  unfold wordAt
  split_ifs <;> first | rfl | omega

private def Valid {n : ℕ} (w : Fin (n + 1) → Fin 4) (forced : Bool) : Prop :=
  (n = 0 → forced = false) ∧
  (0 < n → forced = true → wordAt w 0 ≠ wordAt w 1) ∧
  (∀ i, i + 2 ≤ n → wordAt w i ≠ wordAt w (i + 1) ∨
    wordAt w (i + 1) ≠ wordAt w (i + 2)) ∧
  (0 < n → wordAt w (n - 1) ≠ wordAt w n)

private theorem valid_tail {n : ℕ} (w : Fin (n + 2) → Fin 4) (b : Bool) :
    Valid w b ↔ (b = false ∨ wordAt w 0 ≠ wordAt w 1) ∧
      Valid (Fin.tail w) (decide (wordAt w 0 = wordAt w 1)) := by
  unfold Valid
  simp only [wordAt_tail]
  constructor
  · rintro ⟨_, hfirst, htriple, hlast⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · cases b <;> simp [hfirst]
    · intro hn
      subst n
      simpa using hlast (by omega)
    · intro hn hsame
      have heq : wordAt w 0 = wordAt w 1 := of_decide_eq_true hsame
      exact (htriple 0 (by omega)).resolve_left (not_not_intro heq)
    · intro i hi
      exact htriple (i + 1) (by omega)
    · intro hn
      rw [show n - 1 + 1 = n by omega]
      exact hlast (by omega)
  · rintro ⟨hfirst, hzero, hnext, htriple, hlast⟩
    refine ⟨by omega, ?_, ?_, ?_⟩
    · intro _ hb
      exact hfirst.resolve_left (by simp [hb])
    · intro i hi
      cases i with
      | zero =>
        by_cases h : wordAt w 0 = wordAt w 1
        · exact Or.inr (hnext (by omega) (decide_eq_true h))
        · exact Or.inl h
      | succ j => exact htriple j (by omega)
    · intro _
      by_cases h : n = 0
      · subst n
        simpa using hzero rfl
      · have hv := hlast (by omega)
        rw [show n - 1 + 1 = n by omega] at hv
        exact hv

private def Vertical {n : ℕ} (w : Fin (n + 1) → Fin 4) : Prop :=
  ∀ i, ∃ j, vnb i j ∧ w j ≠ w i

private theorem vertical_iff_valid {n : ℕ} (w : Fin (n + 1) → Fin 4) :
    Vertical w ↔ Valid w true := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hn
      subst n
      obtain ⟨j, hj, _⟩ := h 0
      fin_cases j
      simp [vnb] at hj
    · intro hn _
      let i : Fin (n + 1) := ⟨0, by omega⟩
      obtain ⟨j, hj, hjne⟩ := h i
      have hjv : j.val = 1 := by
        change i.val + 1 = j.val ∨ j.val + 1 = i.val at hj
        dsimp [i] at hj
        omega
      have he := wordAt_get w j
      rw [hjv] at he
      rw [he, show wordAt w 0 = w i from wordAt_get w i]
      exact Ne.symm hjne
    · intro k hk
      let i : Fin (n + 1) := ⟨k + 1, by omega⟩
      obtain ⟨j, hj, hjne⟩ := h i
      change k + 1 + 1 = j.val ∨ j.val + 1 = k + 1 at hj
      have hiw : wordAt w (k + 1) = w i := wordAt_get w i
      have hjw := wordAt_get w j
      rcases hj with hright | hleft
      · rw [← hright] at hjw
        exact Or.inr (by rw [hiw, hjw]; exact Ne.symm hjne)
      · have hjv : j.val = k := by omega
        rw [hjv] at hjw
        exact Or.inl (by rw [hiw, hjw]; exact hjne)
    · intro hn
      let i : Fin (n + 1) := ⟨n, by omega⟩
      obtain ⟨j, hj, hjne⟩ := h i
      change n + 1 = j.val ∨ j.val + 1 = n at hj
      have hjv : j.val = n - 1 := by have := j.isLt; omega
      have hw := wordAt_get w j
      rw [hjv] at hw
      rw [hw, show wordAt w n = w i from wordAt_get w i]
      exact hjne
  · rintro ⟨hzero, hfirst, htriple, hlast⟩ i
    have hn : 0 < n := by
      by_contra! h
      have := hzero (by omega)
      contradiction
    have hiw := wordAt_get w i
    by_cases hi0 : i.val = 0
    · let j : Fin (n + 1) := ⟨1, by omega⟩
      refine ⟨j, Or.inl (by simp [j, hi0]), ?_⟩
      rw [hi0] at hiw
      exact (by
        rw [← hiw, ← wordAt_get w j]
        exact Ne.symm (hfirst hn rfl))
    by_cases hin : i.val = n
    · let j : Fin (n + 1) := ⟨n - 1, by omega⟩
      refine ⟨j, Or.inr (by dsimp [j]; omega), ?_⟩
      rw [hin] at hiw
      rw [← hiw, ← wordAt_get w j]
      exact hlast hn
    have hib := i.isLt
    let j : Fin (n + 1) := ⟨i.val - 1, by omega⟩
    let k : Fin (n + 1) := ⟨i.val + 1, by omega⟩
    have hp := htriple (i.val - 1) (by omega)
    rw [show i.val - 1 + 1 = i.val by omega, show i.val - 1 + 2 = i.val + 1 by omega,
      hiw, show wordAt w (i.val - 1) = w j from wordAt_get w j,
      show wordAt w (i.val + 1) = w k from wordAt_get w k] at hp
    rcases hp with hj | hk
    · exact ⟨j, Or.inr (by dsimp [j]; omega), hj⟩
    · exact ⟨k, Or.inl rfl, Ne.symm hk⟩

private theorem row_constant {n : ℕ} {w : Fin (n + 1) → Fin 2 → Fin 4}
    (h : good w) (i : Fin (n + 1)) (j : Fin 2) : w i j = w i 0 := by
  fin_cases j
  · rfl
  · apply le_antisymm
    · by_contra! hlt
      apply (h i 1).1
      intro j hj
      fin_cases j <;> first | exact hlt | simp [hnb] at hj
    · by_contra! hlt
      apply (h i 0).1
      intro j hj
      fin_cases j <;> first | exact hlt | simp [hnb] at hj

private theorem grid_word {n : ℕ} (w : Fin (n + 1) → Fin 4) :
    good (fun i _ => w i) ↔ Valid w true := by
  rw [← vertical_iff_valid]
  constructor
  · intro h i
    have hv := (h i 0).2
    push Not at hv
    exact hv
  · intro h i j
    refine ⟨?_, ?_⟩
    · intro hlt
      have hv : hnb j (1 - j) := by fin_cases j <;> decide
      exact (lt_irrefl _) (hlt _ hv)
    · intro he
      obtain ⟨k, hk, hne⟩ := h i
      exact hne (he k hk)

private theorem split_words {n : ℕ} {R : Type*} [AddCommMonoid R]
    (f : (Fin (n + 1) → Fin 4) → R) :
    (∑ w, f w) = ∑ c : Fin 4, ∑ tail : Fin n → Fin 4, f (Fin.cons c tail) := by
  calc
    _ = ∑ p : Fin 4 × (Fin n → Fin 4), f (Fin.cons p.1 p.2) :=
      (Fintype.sum_equiv (Fin.consEquiv (fun _ => Fin 4))
        (fun p => f (Fin.cons p.1 p.2)) f (fun _ => rfl)).symm
    _ = _ := Fintype.sum_prod_type
      (fun p : Fin 4 × (Fin n → Fin 4) => f (Fin.cons p.1 p.2))

private noncomputable def stateCount (n : ℕ) (c : Fin 4) (b : Bool) : ℕ := by
  classical
  exact ∑ w : Fin n → Fin 4, if Valid (Fin.cons c w) b then 1 else 0

private theorem state_step (n : ℕ) (c : Fin 4) (b : Bool) :
    stateCount (n + 1) c b =
      ∑ d : Fin 4, if d = c then (if b then 0 else stateCount n c true)
        else stateCount n d false := by
  classical
  unfold stateCount at *
  rw [split_words]
  apply Finset.sum_congr rfl
  intro d _
  have h0 (w : Fin n → Fin 4) : wordAt (Fin.cons c (Fin.cons d w)) 0 = c := by
    exact wordAt_get _ (0 : Fin (n + 2))
  have h1 (w : Fin n → Fin 4) : wordAt (Fin.cons c (Fin.cons d w)) 1 = d := by
    exact wordAt_get _ (1 : Fin (n + 2))
  by_cases hd : d = c
  · subst d
    cases b <;> simp [valid_tail, h0, h1, Fin.tail_cons]
  · simp [valid_tail, h0, h1, Fin.tail_cons, hd, Ne.symm hd]

private theorem sum_color (c : Fin 4) (x y : ℕ) :
    (∑ d : Fin 4, if d = c then x else y) = x + 3 * y := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ c)]
  have he : (∑ d ∈ (Finset.univ : Finset (Fin 4)).erase c, if d = c then x else y) =
      ∑ _d ∈ (Finset.univ : Finset (Fin 4)).erase c, y := by
    apply Finset.sum_congr rfl
    intro d hd
    exact if_neg (Finset.ne_of_mem_erase hd)
  rw [he]
  simp [Finset.card_erase_of_mem (Finset.mem_univ c), add_comm]

private def totals : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | n + 1 => (3 * (totals n).2, 3 * (totals n).2 + (totals n).1)

private theorem state_totals (n : ℕ) (c : Fin 4) (b : Bool) :
    stateCount n c b = if b then (totals n).1 else (totals n).2 := by
  classical
  induction n generalizing c b with
  | zero =>
    cases b <;> simp [stateCount, Valid, totals]
  | succ n ih =>
    rw [state_step]
    simp only [ih]
    cases b <;> simp [sum_color, totals, add_comm]

private theorem count_words (n : ℕ) : a n = 4 * (totals n).1 := by
  classical
  have he : a n =
      ((univ : Finset (Fin (n + 1) → Fin 4)).filter (fun w => Valid w true)).card := by
    unfold a
    apply Finset.card_bij' (fun w _ i => w i 0) (fun w _ i _ => w i)
    · intro w hw
      funext i j
      exact (row_constant (Finset.mem_filter.mp hw).2 i j).symm
    · intro w _
      rfl
    · intro g hg
      have hh := (Finset.mem_filter.mp hg).2
      have eqg : (fun i (_ : Fin 2) => g i 0) = g := by
        funext i j
        exact (row_constant hh i j).symm
      have hh' : good (fun i _ => g i 0) := by rwa [eqg]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (grid_word _).mp hh'⟩
    · intro w hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (grid_word _).mpr (Finset.mem_filter.mp hw).2⟩
  rw [he]
  calc
    _ = ∑ w : Fin (n + 1) → Fin 4, if Valid w true then (1 : ℕ) else 0 :=
      (Finset.sum_boole (fun w => Valid w true) Finset.univ).symm
    _ = _ := by
      rw [split_words]
      change (∑ c : Fin 4, stateCount n c true) = _
      simp [state_totals]

private theorem a_zero : a 0 = 0 := by simp [count_words, totals]

private theorem a_one : a 1 = 12 := by simp [count_words, totals]

private theorem a_step (n : ℕ) : a (n + 2) = 3 * a (n + 1) + 3 * a n := by
  simp only [count_words, totals]
  omega

private theorem series_identity :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - 3 * X - 3 * X ^ 2) =
      12 * X := by
  have hoff (n : ℕ) : (if n = 0 then (0 : ℚ) else (a n : ℚ)) = (a n : ℚ) := by
    by_cases h : n = 0 <;> simp [h, a_zero]
  simp only [hoff]
  have hd : (1 - 3 * X - 3 * X ^ 2 : ℚ⟦X⟧) = 1 - X ^ 1 * C 3 - X ^ 2 * C 3 := by
    simp only [pow_one, map_ofNat]
    ring
  have hn : (12 * X : ℚ⟦X⟧) = X ^ 1 * C 12 := by
    simp only [pow_one, map_ofNat]
    ring
  rw [hd, hn]
  ext n
  simp only [mul_sub, mul_one, ← mul_assoc, map_sub, coeff_mul_C, coeff_mul_X_pow',
    coeff_mk, coeff_X_pow]
  obtain (_ | _ | k) := n
  · norm_num [a_zero]
  · norm_num [a_zero, a_one]
  · simp only [if_pos (show 1 ≤ k + 2 by omega), if_pos (show 2 ≤ k + 2 by omega),
      show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega,
      if_neg (show k + 2 ≠ 1 by omega), zero_mul]
    have hr : (a (k + 2) : ℚ) = 3 * (a (k + 1) : ℚ) + 3 * (a k : ℚ) := by
      exact_mod_cast a_step k
    linarith

private theorem root_step (r : ℝ) (h : r ^ 2 = 3 * r + 3) (n : ℕ) :
    r ^ (n + 2) = 3 * r ^ (n + 1) + 3 * r ^ n := by
  rw [pow_add r n 2, h, pow_succ r n]
  ring

private theorem explicit_formula (n : ℕ) :
    (a n : ℝ) = (-4) * (Real.sqrt (3 / 7) *
      (((3 - Real.sqrt 21) / 2) ^ n - ((3 + Real.sqrt 21) / 2) ^ n)) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)
  have hp : Real.sqrt (3 / 7) * Real.sqrt 21 = 3 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3 / 7),
      show (3 : ℝ) / 7 * 21 = (3 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain (_ | _ | k) := n
    · simp [a_zero]
    · have he : (3 - Real.sqrt 21) / 2 - (3 + Real.sqrt 21) / 2 = -Real.sqrt 21 := by ring
      rw [a_one, pow_one, pow_one, he, mul_neg, hp]
      norm_num
    · have hr : (a (k + 2) : ℝ) = 3 * (a (k + 1) : ℝ) + 3 * (a k : ℝ) := by
        exact_mod_cast a_step k
      rw [hr, ih (k + 1) (by omega), ih k (by omega),
        root_step ((3 - Real.sqrt 21) / 2) (by nlinarith),
        root_step ((3 + Real.sqrt 21) / 2) (by nlinarith)]
      ring

end OMA.S_oeis_a238923

open OMA.S_oeis_a238923 in
theorem OMA.solution : type_of% @OMA.S_oeis_a238923.main := by
  exact ⟨series_identity, fun n _ => explicit_formula n⟩