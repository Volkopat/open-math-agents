import OMAStatements.S_oeis_a179100
import Mathlib

/-! A179100: closed form 2 S(n+1) = (n+1)((n+1)T(n+1)^2 - 6n T(n+1)T(n) + 9(n+1)T(n)^2) from the central trinomial
recurrence; then T odd gives integrality, and T(p) = 1, T(p-1) = (p/3) mod p give the congruence. -/

namespace A179100
open Finset Polynomial OMA.S_oeis_a179100

private def t (k j : ℕ) : ℤ := ((Nat.choose k (2 * j) * Nat.choose (2 * j) j : ℕ) : ℤ)

private lemma t_zero (k j : ℕ) (h : k < 2 * j) : t k j = 0 := by
  simp [t, Nat.choose_eq_zero_of_lt h]

private lemma t_fact (k j : ℕ) (h : 2 * j ≤ k) :
    (t k j : ℚ) = k.factorial / (j.factorial * j.factorial * (k - 2 * j).factorial) := by
  unfold t
  push_cast
  rw [Nat.cast_choose ℚ h, Nat.cast_choose ℚ (by omega : j ≤ 2 * j), show 2 * j - j = j by omega]
  have := (2 * j).factorial_pos
  have := j.factorial_pos
  have := (k - 2 * j).factorial_pos
  field_simp

private lemma T_eq (k K : ℕ) (hK : k + 2 ≤ K) : T k = ∑ j ∈ range K, t k j := by
  unfold T
  rw [← Finset.sum_range_add_sum_Ico _ (show k / 2 + 1 ≤ K by omega)]
  rw [Finset.sum_eq_zero (s := Ico _ _) (fun j hj => by
    simp only [mem_Ico] at hj; exact t_zero k j (by omega)), add_zero]
  rfl

private lemma key (k i : ℕ) :
    ((k + 2 : ℕ) : ℤ) * t (k + 2) (i + 1) - (2 * ((k + 1 : ℕ) : ℤ) + 1) * t (k + 1) (i + 1)
      - 3 * ((k + 1 : ℕ) : ℤ) * t k (i + 1)
      = -4 * (((k + 1 : ℕ) : ℤ) - 2 * i - 2) * t (k + 1) (i + 1)
        + 4 * (((k + 1 : ℕ) : ℤ) - 2 * i) * t (k + 1) i := by
  apply Int.cast_injective (α := ℚ)
  push_cast
  rcases lt_trichotomy k (2 * i) with hlt | heq | hgt
  · rw [t_zero (k + 2) (i + 1) (by omega), t_zero (k + 1) (i + 1) (by omega),
      t_zero k (i + 1) (by omega)]
    rcases Nat.lt_or_ge (k + 1) (2 * i) with h1 | h1
    · rw [t_zero (k + 1) i h1]; ring
    · have : (k : ℚ) + 1 - 2 * i = 0 := by
        have : k + 1 = 2 * i := by omega
        exact_mod_cast (by omega : (k : ℤ) + 1 - 2 * i = 0)
      rw [this]; ring
  · subst heq
    rw [t_zero (2 * i + 1) (i + 1) (by omega), t_zero (2 * i) (i + 1) (by omega),
      t_fact (2 * i + 2) (i + 1) (by omega), t_fact (2 * i + 1) i (by omega),
      show 2 * i + 2 - 2 * (i + 1) = 0 by omega, show 2 * i + 1 - 2 * i = 1 by omega]
    simp only [Nat.factorial_succ, Nat.factorial_zero]
    push_cast
    have := (2 * i).factorial_pos
    have := i.factorial_pos
    field_simp
    ring
  · rcases Nat.lt_or_ge k (2 * i + 2) with h2 | h2
    · have hk : k = 2 * i + 1 := by omega
      subst hk
      rw [t_zero (2 * i + 1) (i + 1) (by omega),
        t_fact (2 * i + 1 + 2) (i + 1) (by omega), t_fact (2 * i + 1 + 1) (i + 1) (by omega),
        t_fact (2 * i + 1 + 1) i (by omega),
        show 2 * i + 1 + 2 - 2 * (i + 1) = 1 by omega, show 2 * i + 1 + 1 - 2 * (i + 1) = 0 by omega,
        show 2 * i + 1 + 1 - 2 * i = 2 by omega]
      simp only [Nat.factorial_succ, Nat.factorial_zero]
      push_cast
      have := (2 * i).factorial_pos
      have := i.factorial_pos
      field_simp
      ring
    · obtain ⟨r, hr⟩ : ∃ r, k = 2 * i + 2 + r := ⟨k - (2 * i + 2), by omega⟩
      rw [t_fact (k + 2) (i + 1) (by omega), t_fact (k + 1) (i + 1) (by omega),
        t_fact k (i + 1) (by omega), t_fact (k + 1) i (by omega),
        show k + 2 - 2 * (i + 1) = r + 1 + 1 by omega, show k + 1 - 2 * (i + 1) = r + 1 by omega,
        show k - 2 * (i + 1) = r by omega, show k + 1 - 2 * i = r + 1 + 1 + 1 by omega]
      simp only [Nat.factorial_succ]
      push_cast
      have := k.factorial_pos
      have := i.factorial_pos
      have := r.factorial_pos
      have hq : (k : ℚ) = 2 * i + 2 + r := by exact_mod_cast hr
      field_simp
      rw [hq]
      ring

private lemma recur (k : ℕ) :
    ((k + 2 : ℕ) : ℤ) * T (k + 2) = (2 * ((k + 1 : ℕ) : ℤ) + 1) * T (k + 1)
      + 3 * ((k + 1 : ℕ) : ℤ) * T k := by
  rw [T_eq (k + 2) (k + 4) le_rfl, T_eq (k + 1) (k + 4) (by omega), T_eq k (k + 4) (by omega),
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_range_succ']
  have h := Finset.sum_range_sub (fun i => -4 * (((k + 1 : ℕ) : ℤ) - 2 * i) * t (k + 1) i) (k + 3)
  rw [t_zero (k + 1) (k + 3) (by omega)] at h
  have e : ∀ i ∈ range (k + 3),
      ((k + 2 : ℕ) : ℤ) * t (k + 2) (i + 1) - ((2 * ((k + 1 : ℕ) : ℤ) + 1) * t (k + 1) (i + 1)
        + 3 * ((k + 1 : ℕ) : ℤ) * t k (i + 1))
      = -4 * (((k + 1 : ℕ) : ℤ) - 2 * ((i + 1 : ℕ) : ℤ)) * t (k + 1) (i + 1)
        - -4 * (((k + 1 : ℕ) : ℤ) - 2 * (i : ℤ)) * t (k + 1) i := by
    intro i _
    have := key k i
    push_cast at this ⊢
    linear_combination this
  rw [Finset.sum_congr rfl e, h]
  simp [t]
  ring

private lemma T0 : T 0 = 1 := by simp [T]
private lemma T1 : T 1 = 1 := by simp [T]
private lemma T2 : T 2 = 3 := by decide
private lemma T_odd (k : ℕ) : (2 : ℤ) ∣ T k - 1 := by
  unfold T
  rw [Finset.sum_range_succ', add_sub_assoc]
  simp only [mul_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, sub_self, add_zero]
  apply Finset.dvd_sum
  intro j _
  push_cast
  apply Dvd.dvd.mul_left
  have := Nat.two_dvd_centralBinom_of_one_le (n := j + 1) (by omega)
  rw [Nat.centralBinom_eq_two_mul_choose] at this
  exact_mod_cast this


private noncomputable abbrev F : ℤ[X] := 1 + X + X ^ 2

private lemma central (n : ℕ) : (F ^ n).coeff n = T n := by
  have expandTwo (j : ℕ) : (1 + X ^ 2 : ℤ[X]) ^ j = expand ℤ 2 ((1 + X) ^ j) := by simp
  rw [show F = (1 + X ^ 2) + X by ring, add_pow, finsetSum_coeff]
  simp only [coeff_mul_natCast, coeff_mul_X_pow', Nat.sub_le, if_true]
  calc
    _ = ∑ j ∈ (range (n + 1)).filter (fun j => 2 ∣ j),
          (j.choose (j / 2) : ℤ) * n.choose j := by
      rw [sum_filter]
      apply sum_congr rfl
      intro j hj
      have hjn := Nat.le_of_lt_succ (mem_range.mp hj)
      rw [Nat.sub_sub_self hjn, expandTwo, coeff_expand (by decide), coeff_one_add_X_pow]
      split_ifs <;> simp
    _ = _ := by
      unfold T
      refine sum_bij' (fun j _ => j / 2) (fun k _ => 2 * k) ?_ ?_ ?_ ?_ ?_
      · intro j hj
        obtain ⟨h, _⟩ := mem_filter.mp hj
        simp only [mem_range] at *
        omega
      · intro k hk
        apply mem_filter.mpr
        refine ⟨mem_range.mpr ?_, dvd_mul_right _ _⟩
        simp only [mem_range] at hk
        omega
      · intro j hj
        exact Nat.mul_div_cancel' (mem_filter.mp hj).2
      · intro k _
        omega
      · intro j hj
        rw [Nat.mul_div_cancel' (mem_filter.mp hj).2]; push_cast; ring

private lemma Tp {p : ℕ} (hp : p.Prime) : ((T p : ℤ) : ZMod p) = 1 := by
  have := Fact.mk hp
  rw [← central]
  change (Int.castRingHom (ZMod p)) _ = _
  rw [← coeff_map, Polynomial.map_pow, ← ZMod.expand_card, coeff_expand hp.pos,
    if_pos dvd_rfl, Nat.div_self hp.pos]
  simp [F, coeff_one]

private lemma Tq {p : ℕ} (hp : p.Prime) : ((T (p - 1) : ℤ) : ZMod p) =
    if (p - 1) % 3 = 0 then 1 else if (p - 1) % 3 = 1 then -1 else 0 := by
  have := Fact.mk hp
  rw [← central]
  change (Int.castRingHom (ZMod p)) _ = _
  rw [← coeff_map, Polynomial.map_pow]
  have hF : F.map (Int.castRingHom (ZMod p)) = 1 + X + X ^ 2 := by simp [F]
  rw [hF]
  set G : (ZMod p)[X] := (1 + X + X ^ 2) ^ (p - 1) with hGdef
  have h1 : (1 + X + X ^ 2 : (ZMod p)[X]) ^ p = 1 + X ^ p + (X ^ p) ^ 2 := by
    rw [← ZMod.expand_card]; simp
  have h2 : G * (1 + X + X ^ 2) = 1 + X ^ p + (X ^ p) ^ 2 := by
    rw [hGdef, ← pow_succ, Nat.sub_add_cancel hp.one_lt.le, h1]
  have hG : G - X ^ 3 * G = 1 - X + X ^ p - X ^ p * X + X ^ (2 * p) - X ^ (2 * p) * X := by
    rw [pow_mul']
    linear_combination (1 - X) * h2
  have hc : ∀ m, m < p → G.coeff m = if m % 3 = 0 then 1 else if m % 3 = 1 then -1 else 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      have e := congrArg (fun q => Polynomial.coeff q m) hG
      simp only [coeff_sub, coeff_add, coeff_X_pow_mul', coeff_one, coeff_X,
        coeff_X_pow] at e
      have a1 : m ≠ p := by omega
      have a2 : m ≠ 2 * p := by omega
      have a3 : ¬ p ≤ m := by omega
      have a4 : ¬ 2 * p ≤ m := by omega
      simp only [a1, a2, a3, a4, if_false] at e
      rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ 3 ≤ m) with h | h | h | h
      · subst h; simp at e; simp [e]
      · subst h; simp at e; simp [e]
      · subst h; simp at e; simp [e]
      · have b1 : m ≠ 0 := by omega
        have b2 : ¬ (1 = m) := by omega
        simp only [b1, b2, h, if_false, if_true] at e
        have e2 : G.coeff m = G.coeff (m - 3) := by linear_combination e
        rw [e2, ih (m - 3) (by omega) (by omega), show (m - 3) % 3 = m % 3 by omega]
  exact hc (p - 1) (by have := hp.pos; omega)

private lemma chi_val (p : ℕ) : jacobiSym (p : ℤ) 3 =
    if p % 3 = 0 then 0 else if p % 3 = 1 then 1 else -1 := by
  rw [jacobiSym.mod_left, ← Int.natCast_mod]
  rcases (by omega : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2) with h | h | h <;> rw [h] <;> simp
  all_goals norm_num


private lemma S_succ (n : ℕ) : S (n + 1) = S n + (8 * (n : ℤ) + 5) * T n ^ 2 := by
  unfold S
  rw [Finset.sum_range_succ]

private lemma closed (m : ℕ) : 2 * S (m + 1) = ((m : ℤ) + 1) * (((m : ℤ) + 1) * T (m + 1) ^ 2
    - 6 * (m : ℤ) * T (m + 1) * T m + 9 * ((m : ℤ) + 1) * T m ^ 2) := by
  induction m with
  | zero => simp [S, T0, T1]
  | succ m ih =>
    rw [S_succ]
    have hr := recur m
    push_cast at hr ih ⊢
    linear_combination ih + (-3 * T m * (m : ℤ) - 3 * T m + 4 * T (m + 1) * (m : ℤ)
      + 3 * T (m + 1) - T (m + 2) * (m : ℤ) - 2 * T (m + 2)) * hr

private def K (m : ℕ) : ℤ :=
  ((m : ℤ) + 1) * ((T (m + 1) ^ 2 + 9 * T m ^ 2) / 2) - 3 * (m : ℤ) * T (m + 1) * T m

private lemma S_eq (m : ℕ) : S (m + 1) = ((m : ℤ) + 1) * K m := by
  obtain ⟨u, hu⟩ := T_odd (m + 1)
  obtain ⟨v, hv⟩ := T_odd m
  have hc := closed m
  have e : (T (m + 1) ^ 2 + 9 * T m ^ 2) / 2 = 2 * u ^ 2 + 2 * u + 18 * v ^ 2 + 18 * v + 5 := by
    rw [show T (m + 1) = 2 * u + 1 by linarith, show T m = 2 * v + 1 by linarith]
    rw [show (2 * u + 1) ^ 2 + 9 * (2 * v + 1) ^ 2
      = 2 * (2 * u ^ 2 + 2 * u + 18 * v ^ 2 + 18 * v + 5) by ring]
    simp
  unfold K
  rw [e]
  have hT1 : T (m + 1) = 2 * u + 1 := by linarith
  have hT0 : T m = 2 * v + 1 := by linarith
  rw [hT1, hT0] at hc ⊢
  linarith

private theorem main' :
    (∀ n : ℕ, 1 ≤ n → (n : ℤ) ∣ S n) ∧
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ a p - 3 * jacobiSym (p : ℤ) 3) := by
  refine ⟨fun n hn => ?_, fun p hp => ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact ⟨K m, by rw [S_eq]; push_cast; ring⟩
  · have hTp := Tp hp
    have hTq := Tq hp
    have hchi := chi_val p
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.pos; omega⟩
    have := Fact.mk hp
    simp only [Nat.add_sub_cancel] at hTq
    have ha : a (m + 1) = K m := by
      unfold a
      rw [S_eq]
      push_cast
      exact Int.mul_ediv_cancel_left _ (by positivity)
    rw [ha, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hm : ((m : ℤ) : ZMod (m + 1)) = -1 := by
      have : ((m + 1 : ℕ) : ZMod (m + 1)) = 0 := ZMod.natCast_self _
      push_cast at this ⊢
      linear_combination this
    unfold K
    push_cast
    have hm1 : ((m : ℤ) : ZMod (m + 1)) + 1 = 0 := by rw [hm]; ring
    push_cast at hm hm1
    push_cast at hchi
    rw [hm1, hm, hTp, hchi, hTq]
    rcases (by omega : (m + 1) % 3 = 0 ∨ (m + 1) % 3 = 1 ∨ (m + 1) % 3 = 2) with h | h | h
    · simp only [h, show m % 3 = 2 by omega]; norm_num
    · simp only [h, show m % 3 = 0 by omega]; norm_num
    · simp only [h, show m % 3 = 1 by omega]; norm_num

end A179100

theorem OMA.solution : type_of% @OMA.S_oeis_a179100.main := A179100.main'
