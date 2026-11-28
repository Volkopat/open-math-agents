import OMAStatements.S_oeis_a297835

-- Problem: A297835: Solution of the complementary equation a(n) = a(1)*b(n-1) - a(0)*b(n-2) + 2*n + 1, where a(0) = 1, a(1) = 2, b(0) = 3, b(1) = 4, and (b(n)) is the increasing sequence of positive integers not in (a(n)).  See Comments.
-- Upstream: formal-conjectures statements/oeis-a297835.lean:0 (declaration OMA.S_oeis_a297835.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: Prove the counting identity b(m) = m + J + 2 with a(J) < b(m) < a(J + 1), deduce
-- b(m + 1) <= b(m) + 2 by strong induction, derive a(n) = 3*n + 4 for 2 <= n <= 7, and close
-- 0 <= a(n) - (2 + sqrt 2)*n <= 4 for all n >= 2 by strong induction using
-- 141/100 < sqrt 2 < 142/100.

namespace P1A297835

open OMA.S_oeis_a297835

theorem a_ge {a b : ℕ → ℕ} (h : IsSolution a b) (n : ℕ) : n + 1 ≤ a n := by
  obtain ⟨ha0, _, _, _, _, hma, _, _⟩ := id h
  induction n with
  | zero => rw [ha0]
  | succ k ih =>
    have hlt : a k < a (k + 1) := hma (show k < k + 1 by omega)
    omega

theorem b_ge {a b : ℕ → ℕ} (h : IsSolution a b) (n : ℕ) : n + 3 ≤ b n := by
  obtain ⟨_, _, hb0, _, _, _, hmb, _⟩ := id h
  induction n with
  | zero => rw [hb0]
  | succ k ih =>
    have hlt : b k < b (k + 1) := hmb (show k < k + 1 by omega)
    omega

theorem a_rec_int {a b : ℕ → ℕ} (h : IsSolution a b) {n : ℕ} (hn : 2 ≤ n) :
    (a n : ℤ) = 2 * (b (n - 1) : ℤ) - (b (n - 2) : ℤ) + 2 * (n : ℤ) + 1 := by
  obtain ⟨ha0, ha1, _, _, hrec, _, _, _⟩ := id h
  have hr := hrec n hn
  rw [ha0, ha1] at hr
  push_cast at hr
  linarith

theorem a_lower {a b : ℕ → ℕ} (h : IsSolution a b) {j : ℕ} (hj : 2 ≤ j) :
    3 * j + 4 ≤ a j := by
  obtain ⟨_, _, _, _, _, _, hmb, _⟩ := id h
  have hr := a_rec_int h hj
  have hb1 : j + 2 ≤ b (j - 1) := by
    have := b_ge h (j - 1)
    omega
  have hblt : b (j - 2) < b (j - 1) := hmb (by omega)
  omega

theorem counting {a b : ℕ → ℕ} (h : IsSolution a b) (n : ℕ) :
    ∃ J : ℕ, a J < b n ∧ b n < a (J + 1) ∧ b n = n + J + 2 := by
  obtain ⟨ha0, _, _, _, _, hma, hmb, hcomp⟩ := id h
  have hex : ∃ j : ℕ, b n < a j := ⟨b n, by have := a_ge h (b n); omega⟩
  classical
  let j0 := Nat.find hex
  have hj0_gt : b n < a j0 := Nat.find_spec hex
  have hbn_ge : 3 ≤ b n := by have := b_ge h n; omega
  have hj0_pos : 0 < j0 := by
    by_contra h0
    have hj0_eq : j0 = 0 := by omega
    rw [hj0_eq, ha0] at hj0_gt
    omega
  let J := j0 - 1
  have hJ1 : J + 1 = j0 := by omega
  have hbn_lt : b n < a (J + 1) := by rwa [hJ1]
  have haJ_le : a J ≤ b n := by
    have hmin := Nat.find_min hex (show J < j0 by omega)
    omega
  have haJ_ne : a J ≠ b n := by
    intro heq
    have h1 : 1 ≤ b n := by omega
    have hnot : b n ∉ Set.range a := (hcomp (b n) h1).mp ⟨n, rfl⟩
    exact hnot ⟨J, heq⟩
  have haJ_lt : a J < b n := by omega
  refine ⟨J, haJ_lt, hbn_lt, ?_⟩
  let A := (Finset.range (J + 1)).image a
  let B := (Finset.range (n + 1)).image b
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    rcases Finset.mem_image.mp hxA with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp hxB with ⟨k, _, hbk⟩
    have h1 : 1 ≤ a i := by have := a_ge h i; omega
    have hnot : a i ∉ Set.range a := (hcomp (a i) h1).mp ⟨k, hbk⟩
    exact hnot ⟨i, rfl⟩
  have hunion : A ∪ B = Finset.Icc 1 (b n) := by
    ext x
    dsimp only [A, B]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro (⟨i, hi, rfl⟩ | ⟨k, hk, rfl⟩)
      · refine ⟨by have := a_ge h i; omega, ?_⟩
        have : a i ≤ a J := hma.monotone (by omega)
        omega
      · refine ⟨by have := b_ge h k; omega, ?_⟩
        exact hmb.monotone (by omega)
    · rintro ⟨hx1, hxle⟩
      by_cases hxb : x ∈ Set.range b
      · rcases hxb with ⟨k, rfl⟩
        right
        refine ⟨k, ?_, rfl⟩
        have hkn : k ≤ n := hmb.le_iff_le.mp hxle
        omega
      · left
        have hxa : x ∈ Set.range a := by
          by_contra hna
          exact hxb ((hcomp x hx1).mpr hna)
        rcases hxa with ⟨i, rfl⟩
        refine ⟨i, ?_, rfl⟩
        exact hma.lt_iff_lt.mp (by omega)
  have hcardA : A.card = J + 1 := by
    rw [Finset.card_image_of_injective _ hma.injective, Finset.card_range]
  have hcardB : B.card = n + 1 := by
    rw [Finset.card_image_of_injective _ hmb.injective, Finset.card_range]
  have hcardU : (A ∪ B).card = b n := by
    rw [hunion, Nat.card_Icc]
    omega
  rw [Finset.card_union_of_disjoint hdisj, hcardA, hcardB] at hcardU
  omega

theorem b_gap {a b : ℕ → ℕ} (h : IsSolution a b) : ∀ n : ℕ, b (n + 1) ≤ b n + 2 := by
  obtain ⟨_, ha1, hb0, hb1, _, hma, hmb, hcomp⟩ := id h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · rw [hb0, hb1]
      omega
    · rw [show n + 1 + 1 = n + 2 by omega]
      by_contra hbig
      have hge3 : b (n + 1) + 3 ≤ b (n + 2) := by omega
      have hnotb1 : b (n + 1) + 1 ∉ Set.range b := by
        rintro ⟨k, hk⟩
        rcases le_or_gt k (n + 1) with hle | hgt
        · have : b k ≤ b (n + 1) := hmb.monotone hle
          omega
        · have : b (n + 2) ≤ b k := hmb.monotone hgt
          omega
      have hnotb2 : b (n + 1) + 2 ∉ Set.range b := by
        rintro ⟨k, hk⟩
        rcases le_or_gt k (n + 1) with hle | hgt
        · have : b k ≤ b (n + 1) := hmb.monotone hle
          omega
        · have : b (n + 2) ≤ b k := hmb.monotone hgt
          omega
      have ha1m : b (n + 1) + 1 ∈ Set.range a := by
        by_contra hna
        exact hnotb1 ((hcomp (b (n + 1) + 1) (by omega)).mpr hna)
      have ha2m : b (n + 1) + 2 ∈ Set.range a := by
        by_contra hna
        exact hnotb2 ((hcomp (b (n + 1) + 2) (by omega)).mpr hna)
      rcases ha1m with ⟨j, hj⟩
      rcases ha2m with ⟨j', hj'⟩
      have hjj' : j < j' := hma.lt_iff_lt.mp (by omega)
      have hj1_eq : j' = j + 1 := by
        by_contra hne
        have hlt : j + 1 < j' := by omega
        have h1 : a j < a (j + 1) := hma (show j < j + 1 by omega)
        have h2 : a (j + 1) < a j' := hma hlt
        omega
      rw [hj1_eq] at hj'
      have hbn1_ge : 4 ≤ b (n + 1) := by have := b_ge h (n + 1); omega
      have hj_ge2 : 2 ≤ j := by
        by_contra hlt2
        have hle1 : j ≤ 1 := by omega
        have : a j ≤ a 1 := hma.monotone hle1
        rw [ha1] at this
        omega
      obtain ⟨J, hJlt, hJgt, hJeq⟩ := counting h (n + 1)
      have hJ_eq : J + 1 = j := by
        have h1 : J < j := hma.lt_iff_lt.mp (by omega)
        have h2 : j ≤ J + 1 := hma.le_iff_le.mp (by omega)
        omega
      have haj_low : 3 * j + 4 ≤ a j := a_lower h hj_ge2
      have hj_lt : j - 2 < n + 1 := by omega
      have hgap_prev : b (j - 2 + 1) ≤ b (j - 2) + 2 := ih (j - 2) hj_lt
      rw [show j - 2 + 1 = j - 1 by omega] at hgap_prev
      have hr1 := a_rec_int h hj_ge2
      have hr2 := a_rec_int h (show 2 ≤ j + 1 by omega)
      rw [show j + 1 - 1 = j by omega, show j + 1 - 2 = j - 1 by omega] at hr2
      have hblt : b (j - 1) < b j := hmb (by omega)
      omega

theorem a_two {a b : ℕ → ℕ} (h : IsSolution a b) : a 2 = 10 := by
  obtain ⟨_, _, hb0, hb1, _, _, _, _⟩ := id h
  have hr := a_rec_int h (le_refl 2)
  rw [show (2 : ℕ) - 1 = 1 by rfl, show (2 : ℕ) - 2 = 0 by rfl, hb0, hb1] at hr
  omega

theorem b_small {a b : ℕ → ℕ} (h : IsSolution a b) : ∀ m : ℕ, m ≤ 6 → b m = m + 3 := by
  obtain ⟨ha0, ha1, hb0, _, _, hma, hmb, hcomp⟩ := id h
  have ha2 := a_two h
  intro m
  induction m with
  | zero => intro _; exact hb0
  | succ k ih =>
    intro hk
    have hbk : b k = k + 3 := ih (by omega)
    have hnotA : k + 4 ∉ Set.range a := by
      rintro ⟨j, hj⟩
      rcases Nat.lt_or_ge j 2 with hlt | hge
      · rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
        · omega
        · omega
      · have : a 2 ≤ a j := hma.monotone hge
        omega
    have hinB : k + 4 ∈ Set.range b := (hcomp (k + 4) (by omega)).mpr hnotA
    rcases hinB with ⟨i, hi⟩
    have hki : k < i := hmb.lt_iff_lt.mp (by omega)
    have hle : b (k + 1) ≤ b i := hmb.monotone hki
    have hlt : b k < b (k + 1) := hmb (show k < k + 1 by omega)
    omega

theorem a_small {a b : ℕ → ℕ} (h : IsSolution a b) {n : ℕ} (hn2 : 2 ≤ n) (hn7 : n ≤ 7) :
    a n = 3 * n + 4 := by
  have hr := a_rec_int h hn2
  have hb1 := b_small h (n - 1) (by omega)
  have hb2 := b_small h (n - 2) (by omega)
  omega

theorem sqrt2_bounds : (141 : ℝ) / 100 < Real.sqrt 2 ∧ Real.sqrt 2 < 142 / 100 := by
  have hnn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  constructor
  · nlinarith
  · nlinarith

theorem g_bounds {a b : ℕ → ℕ} (h : IsSolution a b) :
    ∀ n : ℕ, 2 ≤ n →
      (0 : ℝ) ≤ (a n : ℝ) - (2 + Real.sqrt 2) * n ∧
      (a n : ℝ) - (2 + Real.sqrt 2) * n ≤ 4 := by
  obtain ⟨_, _, _, _, _, hma, hmb, _⟩ := id h
  have ⟨hsqL, hsqU⟩ := sqrt2_bounds
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn2
    by_cases hn7 : n ≤ 7
    · have han : (a n : ℝ) = 3 * (n : ℝ) + 4 := by
        exact_mod_cast a_small h hn2 hn7
      have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      have hn7R : (n : ℝ) ≤ 7 := by exact_mod_cast hn7
      rw [han]
      constructor
      · nlinarith [mul_nonneg (sub_nonneg.mpr hn2R) (sub_nonneg.mpr hsqU.le)]
      · nlinarith [mul_nonneg (sub_nonneg.mpr hn2R) (sub_nonneg.mpr hsqL.le)]
    · have hn8 : 8 ≤ n := by omega
      obtain ⟨J, hJlt, hJgt, hJeq⟩ := counting h (n - 1)
      have ha2 := a_two h
      have hbn_ge : a 2 ≤ b (n - 1) := by
        have := b_ge h (n - 1)
        omega
      have hJ_ge2 : 2 ≤ J := by
        have : 2 < J + 1 := hma.lt_iff_lt.mp (by omega)
        omega
      have haJ_low : 3 * J + 4 ≤ a J := a_lower h hJ_ge2
      have hJ1_lt : J + 1 < n := by omega
      have hJ_lt : J < n := by omega
      have ⟨hgJL, _⟩ := ih J hJ_lt hJ_ge2
      have ⟨_, hgJ1U⟩ := ih (J + 1) hJ1_lt (by omega)
      have hgap : b (n - 1) ≤ b (n - 2) + 2 := by
        have := b_gap h (n - 2)
        rwa [show n - 2 + 1 = n - 1 by omega] at this
      have hblt : b (n - 2) + 1 ≤ b (n - 1) := by
        have := hmb (show n - 2 < n - 1 by omega)
        omega
      have hr : (a n : ℝ) = 2 * (b (n - 1) : ℝ) - (b (n - 2) : ℝ) + 2 * (n : ℝ) + 1 := by
        have hz := congrArg (fun z : ℤ => (z : ℝ)) (a_rec_int h hn2)
        push_cast at hz
        linarith
      have hJeqR : (b (n - 1) : ℝ) = (n : ℝ) + (J : ℝ) + 1 := by
        have : b (n - 1) = n + J + 1 := by omega
        exact_mod_cast this
      have haJ_leR : (a J : ℝ) + 1 ≤ (b (n - 1) : ℝ) := by
        exact_mod_cast (show a J + 1 ≤ b (n - 1) by omega)
      have haJ1_geR : (b (n - 1) : ℝ) + 1 ≤ (a (J + 1) : ℝ) := by
        exact_mod_cast (show b (n - 1) + 1 ≤ a (J + 1) by omega)
      have hgapR : (b (n - 1) : ℝ) ≤ (b (n - 2) : ℝ) + 2 := by exact_mod_cast hgap
      have hbltR : (b (n - 2) : ℝ) + 1 ≤ (b (n - 1) : ℝ) := by exact_mod_cast hblt
      push_cast at hgJ1U
      set β : ℝ := Real.sqrt 2
      set s : ℝ := β - 1 with hs
      have hs_pos : 0 < s := by linarith
      have hdiffU : (2 - ((a J : ℝ) - (2 + β) * (J : ℝ) - 1) * s) -
          ((b (n - 1) : ℝ) - ((n : ℝ) - 1) * β) = s * ((b (n - 1) : ℝ) - 1 - (a J : ℝ)) := by
        rw [hs]
        linear_combination (J : ℝ) * hsq - β * hJeqR
      have heU : (b (n - 1) : ℝ) - ((n : ℝ) - 1) * β ≤
          2 - ((a J : ℝ) - (2 + β) * (J : ℝ) - 1) * s := by
        have hp : 0 ≤ s * ((b (n - 1) : ℝ) - 1 - (a J : ℝ)) :=
          mul_nonneg hs_pos.le (by linarith)
        linarith
      have hdiffL : ((b (n - 1) : ℝ) - ((n : ℝ) - 1) * β) -
          (1 - ((a (J + 1) : ℝ) - (2 + β) * ((J : ℝ) + 1) - 2) * s) =
          s * ((a (J + 1) : ℝ) - 1 - (b (n - 1) : ℝ)) := by
        rw [hs]
        linear_combination -((J : ℝ) + 1) * hsq + β * hJeqR
      have heL : 1 - ((a (J + 1) : ℝ) - (2 + β) * ((J : ℝ) + 1) - 2) * s ≤
          (b (n - 1) : ℝ) - ((n : ℝ) - 1) * β := by
        have hp : 0 ≤ s * ((a (J + 1) : ℝ) - 1 - (b (n - 1) : ℝ)) :=
          mul_nonneg hs_pos.le (by linarith)
        linarith
      have hpU : 0 ≤ ((a J : ℝ) - (2 + β) * (J : ℝ)) * s :=
        mul_nonneg (by linarith) hs_pos.le
      have hpL : 0 ≤ (4 - ((a (J + 1) : ℝ) - (2 + β) * ((J : ℝ) + 1))) * s :=
        mul_nonneg (by linarith) hs_pos.le
      constructor
      · linarith
      · linarith

end P1A297835

open OMA.S_oeis_a297835 in
theorem OMA.solution : type_of% @OMA.S_oeis_a297835.main := by
  intro a b h n hn
  rcases eq_or_lt_of_le hn with rfl | hgt
  · have ⟨_, ha1, _, _, _, _, _, _⟩ := h
    have ⟨hsqL, _⟩ := P1A297835.sqrt2_bounds
    rw [ha1]
    push_cast
    linarith
  · have ⟨_, hgU⟩ := P1A297835.g_bounds h n (by omega)
    linarith
