import OMAStatements.S_oeis_a184878

namespace OMA.P_oeis_a184878

open Polynomial OMA.S_oeis_a184878

/-- The multiset of roots of `Q(n)`. -/
def S (n : ℕ) : Multiset ℤ :=
  (Multiset.range ((n + 1) / 2)).map (fun i => (((n - 2 * i : ℕ) : ℤ) ^ 2))

lemma Q_eq (n : ℕ) : Q n = ((S n).map (fun t => X - C t)).prod := by
  unfold Q S
  rw [Finset.prod_eq_multiset_prod, Finset.range_val, Multiset.map_map]
  rfl

lemma card_S (n : ℕ) : Multiset.card (S n) = (n + 1) / 2 := by
  simp [S]

lemma a_eq (n : ℕ) : a n = (S n).esymm 3 := by
  unfold a T
  split_ifs with h
  · rw [Q_eq, Multiset.prod_X_sub_C_coeff _ (by rw [card_S]; omega), card_S,
      show (n + 1) / 2 - ((n + 1) / 2 - 3) = 3 by omega]
    ring
  · have hc : Multiset.card (S n) < 3 := by rw [card_S]; omega
    simp [Multiset.esymm, Multiset.powersetCard_eq_empty _ hc]

lemma esymm_cons (x : ℤ) (s : Multiset ℤ) (k : ℕ) :
    (x ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + x * s.esymm k := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_def, Multiset.prod_cons, Multiset.sum_map_mul_left]

lemma range_succ' (d : ℕ) : Multiset.range (d + 1) = 0 ::ₘ (Multiset.range d).map Nat.succ := by
  simp only [Multiset.range, List.range_succ_eq_map, Multiset.map_coe, Multiset.cons_coe]

lemma S_succ (n : ℕ) : S (n + 2) = ((n + 2 : ℕ) : ℤ) ^ 2 ::ₘ S n := by
  unfold S
  rw [show (n + 2 + 1) / 2 = (n + 1) / 2 + 1 by omega, range_succ', Multiset.map_cons,
    Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro i _
  simp only [Function.comp_apply, Nat.succ_eq_add_one]
  rw [show n + 2 - 2 * (i + 1) = n - 2 * i by omega]

lemma S_zero : S 0 = 0 := by simp [S]

lemma S_one : S 1 = (1 : ℤ) ::ₘ 0 := by simp [S]

lemma esymm_zero_ms (k : ℕ) : (0 : Multiset ℤ).esymm (k + 1) = 0 := by
  rw [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by simp)]
  simp

lemma esymm0 (s : Multiset ℤ) : s.esymm 0 = 1 := by
  simp [Multiset.esymm]

def P (n : ℕ) : Prop :=
    ((S n).esymm 1 : ℚ) = (n : ℚ) * (n + 1) * (n + 2) / 6 ∧
    ((S n).esymm 2 : ℚ) = (n : ℚ) * (n - 2) * (n - 1) * (n + 1) * (n + 2) * (5 * n + 12) / 360 ∧
    ((S n).esymm 3 : ℚ) = (n : ℚ) * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n + 2) * (n + 1) *
      (35 * n ^ 2 + 182 * n + 240) / 45360

lemma P_all : ∀ n, P n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ =>
      simp only [P, S_zero, esymm_zero_ms]; norm_num
    | 1, _ =>
      simp only [P, S_one, esymm_cons, esymm_zero_ms, esymm0]; norm_num
    | m + 2, ih =>
      obtain ⟨h1, h2, h3⟩ := ih m (by omega)
      simp only [P, S_succ, esymm_cons, esymm0]
      push_cast
      rw [h1, h2, h3]
      refine ⟨by ring, by ring, by ring⟩

end OMA.P_oeis_a184878

theorem OMA.solution : type_of% @OMA.S_oeis_a184878.main := by
  intro n _
  rw [OMA.P_oeis_a184878.a_eq]
  exact (OMA.P_oeis_a184878.P_all n).2.2
