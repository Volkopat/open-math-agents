import OMAStatements.S_oeis_a154142

namespace OMA.P_oeis_a154142

open OMA.S_oeis_a154142 PowerSeries

private def P (k : ℕ) : Prop := IsSquare (9 + k * (k + 1) / 2)

private def xy : ℕ → ℕ × ℕ
  | 0 => (1, 3)
  | 1 => (21, 8)
  | n + 2 =>
    let p := xy n
    (3 * p.1 + 8 * p.2, p.1 + 3 * p.2)

private lemma xy_odd : ∀ n : ℕ, (xy n).1 % 2 = 1
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
    have ih := xy_odd n
    simp only [xy]
    omega

private lemma xy_pell : ∀ n : ℕ, ((xy n).1 : ℤ) ^ 2 - 8 * ((xy n).2 : ℤ) ^ 2 = -71
  | 0 => by norm_num [xy]
  | 1 => by norm_num [xy]
  | n + 2 => by
    have ih := xy_pell n
    simp only [xy]
    calc
      ((3 * (xy n).1 + 8 * (xy n).2 : ℕ) : ℤ) ^ 2 -
          8 * (((xy n).1 + 3 * (xy n).2 : ℕ) : ℤ) ^ 2
        = ((xy n).1 : ℤ) ^ 2 - 8 * ((xy n).2 : ℤ) ^ 2 := by push_cast; ring
      _ = -71 := ih

private lemma xy_strict : ∀ n : ℕ, (xy n).1 < (xy (n + 1)).1 ∧ (xy n).2 < (xy (n + 1)).2
  | 0 => by norm_num [xy]
  | 1 => by norm_num [xy]
  | n + 2 => by
    have ih := xy_strict n
    simp only [xy]
    omega

private def enum (n : ℕ) : ℕ := ((xy n).1 - 1) / 2

private lemma enum_two_mul_add_one (n : ℕ) : 2 * enum n + 1 = (xy n).1 := by
  have hodd := xy_odd n
  simp only [enum]
  omega

private lemma enum_strictMono : StrictMono enum := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h1 := enum_two_mul_add_one n
  have h2 := enum_two_mul_add_one (n + 1)
  have hlt := (xy_strict n).1
  omega

private lemma two_mul_tri (k : ℕ) : 2 * (k * (k + 1) / 2) = k * (k + 1) := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · have hk : k = 2 * (k / 2) := by omega
    conv_lhs => rw [hk]
    conv_rhs => rw [hk]
    rw [mul_assoc, Nat.mul_div_cancel_left _ (by omega)]
  · have hk : k + 1 = 2 * ((k + 1) / 2) := by omega
    conv_lhs => rw [hk]
    conv_rhs => rw [hk]
    rw [mul_left_comm, Nat.mul_div_cancel_left _ (by omega)]

private lemma eight_mul_tri_eq (k : ℕ) :
    8 * ((9 + k * (k + 1) / 2 : ℕ) : ℤ) = (2 * (k : ℤ) + 1) ^ 2 + 71 := by
  have htri : 2 * ((k * (k + 1) / 2 : ℕ) : ℤ) = (k : ℤ) * ((k : ℤ) + 1) := by
    exact_mod_cast two_mul_tri k
  calc
    8 * ((9 + k * (k + 1) / 2 : ℕ) : ℤ)
      = 72 + 4 * (2 * ((k * (k + 1) / 2 : ℕ) : ℤ)) := by
          simp only [Nat.cast_add, Nat.cast_ofNat]
          ring
    _ = 72 + 4 * ((k : ℤ) * ((k : ℤ) + 1)) := by rw [htri]
    _ = (2 * (k : ℤ) + 1) ^ 2 + 71 := by ring

private lemma sq_ne_of_between {x k m : ℤ} (hx0 : 0 ≤ x) (hk0 : 0 ≤ k)
    (h1 : k ^ 2 < m) (h2 : m < (k + 1) ^ 2) : x ^ 2 ≠ m := by
  intro hsq
  rcases le_or_gt x k with hle | hgt
  · nlinarith
  · have hge : k + 1 ≤ x := by omega
    nlinarith

private lemma pell_classify :
    ∀ y x : ℕ, (x : ℤ) ^ 2 - 8 * (y : ℤ) ^ 2 = -71 → ∃ n : ℕ, xy n = (x, y) := by
  intro y
  induction y using Nat.strong_induction_on with
  | h y ih =>
    intro x hxy
    have hx0 : (0 : ℤ) ≤ x := Int.natCast_nonneg x
    rcases lt_or_ge y 9 with hsmall | hbig
    · interval_cases y
      · norm_num at hxy; nlinarith
      · norm_num at hxy; nlinarith
      · norm_num at hxy; nlinarith
      · norm_num at hxy
        have hxZ : (x : ℤ) = 1 := by
          have hmul : ((x : ℤ) - 1) * ((x : ℤ) + 1) = 0 := by linarith
          rcases mul_eq_zero.mp hmul with h1 | h2 <;> linarith
        have hx : x = 1 := by omega
        subst hx
        exact ⟨0, rfl⟩
      · norm_num at hxy
        exact absurd (show (x : ℤ) ^ 2 = 57 by linarith)
          (sq_ne_of_between hx0 (by norm_num : (0 : ℤ) ≤ 7) (by norm_num) (by norm_num))
      · norm_num at hxy
        exact absurd (show (x : ℤ) ^ 2 = 129 by linarith)
          (sq_ne_of_between hx0 (by norm_num : (0 : ℤ) ≤ 11) (by norm_num) (by norm_num))
      · norm_num at hxy
        exact absurd (show (x : ℤ) ^ 2 = 217 by linarith)
          (sq_ne_of_between hx0 (by norm_num : (0 : ℤ) ≤ 14) (by norm_num) (by norm_num))
      · norm_num at hxy
        exact absurd (show (x : ℤ) ^ 2 = 321 by linarith)
          (sq_ne_of_between hx0 (by norm_num : (0 : ℤ) ≤ 17) (by norm_num) (by norm_num))
      · norm_num at hxy
        have hxZ : (x : ℤ) = 21 := by
          have hmul : ((x : ℤ) - 21) * ((x : ℤ) + 21) = 0 := by linarith
          rcases mul_eq_zero.mp hmul with h1 | h2 <;> linarith
        have hx : x = 21 := by omega
        subst hx
        exact ⟨1, rfl⟩
    · have h2y_lt_x : 2 * (y : ℤ) < (x : ℤ) := by nlinarith
      have hx_lt_3y : (x : ℤ) < 3 * (y : ℤ) := by nlinarith
      have h8y_lt_3x : 8 * (y : ℤ) < 3 * (x : ℤ) := by nlinarith
      let x' : ℕ := 3 * x - 8 * y
      let y' : ℕ := 3 * y - x
      have hx' : (x' : ℤ) = 3 * (x : ℤ) - 8 * (y : ℤ) := by
        dsimp only [x']; omega
      have hy' : (y' : ℤ) = 3 * (y : ℤ) - (x : ℤ) := by
        dsimp only [y']; omega
      have hy'_lt : y' < y := by dsimp only [y']; omega
      have hpell' : (x' : ℤ) ^ 2 - 8 * (y' : ℤ) ^ 2 = -71 := by
        rw [hx', hy']
        calc
          (3 * (x : ℤ) - 8 * (y : ℤ)) ^ 2 - 8 * (3 * (y : ℤ) - (x : ℤ)) ^ 2
            = (x : ℤ) ^ 2 - 8 * (y : ℤ) ^ 2 := by ring
          _ = -71 := hxy
      obtain ⟨m, hm⟩ := ih y' hy'_lt x' hpell'
      refine ⟨m + 2, ?_⟩
      simp only [xy, hm]
      exact Prod.ext (by dsimp only [x', y']; omega) (by dsimp only [x', y']; omega)

private lemma enum_iff (k : ℕ) : P k ↔ ∃ n : ℕ, enum n = k := by
  constructor
  · rintro ⟨y, hy⟩
    have h8 := eight_mul_tri_eq k
    have hyZ : ((9 + k * (k + 1) / 2 : ℕ) : ℤ) = (y : ℤ) * (y : ℤ) := by
      exact_mod_cast hy
    have hpell : ((2 * k + 1 : ℕ) : ℤ) ^ 2 - 8 * (y : ℤ) ^ 2 = -71 := by
      push_cast
      nlinarith
    obtain ⟨n, hn⟩ := pell_classify y (2 * k + 1) hpell
    refine ⟨n, ?_⟩
    have h1 := enum_two_mul_add_one n
    have hx : (xy n).1 = 2 * k + 1 := congrArg Prod.fst hn
    omega
  · rintro ⟨n, rfl⟩
    refine ⟨(xy n).2, ?_⟩
    have h8 := eight_mul_tri_eq (enum n)
    have h1 : 2 * (enum n : ℤ) + 1 = ((xy n).1 : ℤ) := by
      exact_mod_cast enum_two_mul_add_one n
    have hpell := xy_pell n
    have hZ : ((9 + enum n * (enum n + 1) / 2 : ℕ) : ℤ) =
        (((xy n).2 * (xy n).2 : ℕ) : ℤ) := by
      have h8' : 8 * ((9 + enum n * (enum n + 1) / 2 : ℕ) : ℤ) =
          8 * (((xy n).2 * (xy n).2 : ℕ) : ℤ) := by
        rw [h8, h1, Nat.cast_mul]
        linarith [hpell, sq ((xy n).2 : ℤ)]
      omega
    exact_mod_cast hZ

private lemma nth_P_eq (k : ℕ) : Nat.nth P k = enum k := by
  classical
  have hinf : {n | P n}.Infinite := by
    have hrange : Set.range enum = {n | P n} := by
      ext n
      exact (enum_iff n).symm
    rw [← hrange]
    exact Set.infinite_range_of_injective enum_strictMono.injective
  induction k using Nat.strong_induction_on with
  | h m ih =>
    have hmem : P (Nat.nth P m) := Nat.nth_mem_of_infinite hinf m
    obtain ⟨j, hj⟩ := (enum_iff _).mp hmem
    have hj_le : m ≤ j := by
      rcases le_or_gt m j with hle | hlt
      · exact hle
      · exfalso
        have heq := ih j hlt
        have hstrict : Nat.nth P j < Nat.nth P m := Nat.nth_strictMono hinf hlt
        omega
    have hm_le : j ≤ m := by
      rcases le_or_gt j m with hle | hlt
      · exact hle
      · exfalso
        have hf_lt : enum m < enum j := enum_strictMono hlt
        rw [hj] at hf_lt
        have hfm : P (enum m) := (enum_iff _).mpr ⟨m, rfl⟩
        have hcount : Nat.count P (Nat.nth P m) = m :=
          Nat.count_nth_of_infinite hinf m
        have hsub : Finset.image enum (Finset.range m) ⊆
            (Finset.range (Nat.nth P m)).filter P := by
          intro x hx
          rw [Finset.mem_image] at hx
          obtain ⟨i, hi, rfl⟩ := hx
          rw [Finset.mem_range] at hi
          rw [Finset.mem_filter, Finset.mem_range]
          refine ⟨?_, (enum_iff _).mpr ⟨i, rfl⟩⟩
          rw [← ih i hi]
          exact Nat.nth_strictMono hinf hi
        have hcard1 : (Finset.image enum (Finset.range m)).card = m := by
          rw [Finset.card_image_of_injective _ enum_strictMono.injective, Finset.card_range]
        have hcard2 : ((Finset.range (Nat.nth P m)).filter P).card = m := by
          rw [← Nat.count_eq_card_filter_range]
          exact hcount
        have heq_set : Finset.image enum (Finset.range m) =
            (Finset.range (Nat.nth P m)).filter P :=
          Finset.eq_of_subset_of_card_le hsub (by omega)
        have hmem_filt : enum m ∈ (Finset.range (Nat.nth P m)).filter P := by
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨hf_lt, hfm⟩
        rw [← heq_set, Finset.mem_image] at hmem_filt
        obtain ⟨i, hi, hfi⟩ := hmem_filt
        rw [Finset.mem_range] at hi
        have := enum_strictMono.injective hfi
        omega
    have : j = m := by omega
    rw [← hj, this]

private lemma a_eq_enum {n : ℕ} (hn : 1 ≤ n) : a n = enum (n - 1) := by
  unfold a
  rw [if_neg (by omega)]
  exact nth_P_eq (n - 1)

private lemma xy_rec (n : ℕ) :
    ((xy (n + 4)).1 : ℤ) = 6 * ((xy (n + 2)).1 : ℤ) - ((xy n).1 : ℤ) := by
  simp only [xy]
  push_cast
  ring

private lemma enum_rec4 (n : ℕ) :
    (enum (n + 4) : ℤ) = 6 * (enum (n + 2) : ℤ) - (enum n : ℤ) + 2 := by
  have h0 : 2 * (enum n : ℤ) + 1 = ((xy n).1 : ℤ) := by
    exact_mod_cast enum_two_mul_add_one n
  have h2 : 2 * (enum (n + 2) : ℤ) + 1 = ((xy (n + 2)).1 : ℤ) := by
    exact_mod_cast enum_two_mul_add_one (n + 2)
  have h4 : 2 * (enum (n + 4) : ℤ) + 1 = ((xy (n + 4)).1 : ℤ) := by
    exact_mod_cast enum_two_mul_add_one (n + 4)
  have hr := xy_rec n
  omega

private lemma part1 : ∀ n : ℕ, 5 < n →
    (a n : ℤ) = a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) - a (n - 4) + a (n - 5) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have h0 : a (m + 6) = enum (m + 5) := by rw [a_eq_enum (by omega)]; congr 1
  have h1 : a (m + 6 - 1) = enum (m + 4) := by rw [a_eq_enum (by omega)]; congr 1
  have h2 : a (m + 6 - 2) = enum (m + 3) := by rw [a_eq_enum (by omega)]; congr 1
  have h3 : a (m + 6 - 3) = enum (m + 2) := by rw [a_eq_enum (by omega)]; congr 1
  have h4 : a (m + 6 - 4) = enum (m + 1) := by rw [a_eq_enum (by omega)]; congr 1
  have h5 : a (m + 6 - 5) = enum m := by rw [a_eq_enum (by omega)]; congr 1
  rw [h0, h1, h2, h3, h4, h5]
  have hr1 := enum_rec4 (m + 1)
  rw [show m + 1 + 4 = m + 5 by omega, show m + 1 + 2 = m + 3 by omega] at hr1
  have hr0 := enum_rec4 m
  omega

private lemma a_vals :
    a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 10 ∧ a 3 = 13 ∧ a 4 = 63 ∧ a 5 = 80 := by
  refine ⟨by simp [a], ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [a_eq_enum (by omega)] <;> decide

private lemma part2 :
    (1 - X) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1) *
      PowerSeries.mk (fun n => (a n : ℤ)) =
      (X ^ 2 * (10 + 3 * X - 10 * X ^ 2 - X ^ 3) : PowerSeries ℤ) := by
  set S : PowerSeries ℤ := PowerSeries.mk (fun n => (a n : ℤ))
  have hlhs : ((1 - X) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1) * S : PowerSeries ℤ) =
      S - X * S - C (6 : ℤ) * (X ^ 2 * S) + C (6 : ℤ) * (X ^ 3 * S) + X ^ 4 * S - X ^ 5 * S := by
    simp only [map_ofNat]
    ring
  have hrhs : (X ^ 2 * (10 + 3 * X - 10 * X ^ 2 - X ^ 3) : PowerSeries ℤ) =
      C (10 : ℤ) * X ^ 2 + C (3 : ℤ) * X ^ 3 - C (10 : ℤ) * X ^ 4 - X ^ 5 := by
    simp only [map_ofNat]
    ring
  rw [hlhs, hrhs]
  ext n
  have hc0 : ∀ m, coeff m S = (a m : ℤ) := fun m => by simp [S]
  have hck : ∀ (k m : ℕ), coeff m (X ^ k * S) = if m < k then 0 else (a (m - k) : ℤ) := by
    intro k m
    rw [coeff_X_pow_mul']
    by_cases h : k ≤ m
    · have hlt : ¬ m < k := by omega
      simp [h, hlt, S]
    · have hlt : m < k := by omega
      simp [h, hlt]
  have hc1 : ∀ m, coeff m (X * S) = if m < 1 then 0 else (a (m - 1) : ℤ) := by
    intro m
    have hX : (X : PowerSeries ℤ) * S = X ^ 1 * S := by rw [pow_one]
    rw [hX, hck 1 m]
  simp only [map_add, map_sub, coeff_C_mul]
  rw [hc0 n, hc1 n, hck 2 n, hck 3 n, hck 4 n, hck 5 n]
  rcases lt_or_ge n 6 with hlt | hge
  · have hvals := a_vals
    interval_cases n <;>
      simp [hvals, coeff_X_pow]
  · have hrec := part1 n (by omega)
    have h1 : ¬ n < 1 := by omega
    have h2 : ¬ n < 2 := by omega
    have h3 : ¬ n < 3 := by omega
    have h4 : ¬ n < 4 := by omega
    have h5 : ¬ n < 5 := by omega
    have hne2 : n ≠ 2 := by omega
    have hne3 : n ≠ 3 := by omega
    have hne4 : n ≠ 4 := by omega
    have hne5 : n ≠ 5 := by omega
    simp only [h1, h2, h3, h4, h5, ↓reduceIte, coeff_X_pow, hne2, hne3, hne4, hne5]
    linarith

theorem main_proof : type_of% @OMA.S_oeis_a154142.main :=
  ⟨part1, part2⟩

end OMA.P_oeis_a154142

theorem OMA.solution : type_of% @OMA.S_oeis_a154142.main :=
  OMA.P_oeis_a154142.main_proof
