import OMAReductions.R_AlspachConjecture_alspach_conjecture_variants_oberwolfach_R1

namespace OMA.Proof_AlspachConjecture_oberwolfach_R1_H1

open SimpleGraph

private def waleckiBase (m : ℕ) (t : Fin (2 * m + 1)) : Fin (2 * m + 1) :=
  if h0 : t.val = 0 then ⟨2 * m, by omega⟩
  else if hodd : t.val % 2 = 1 then ⟨(t.val - 1) / 2, by omega⟩
  else ⟨2 * m - t.val / 2, by omega⟩

private def waleckiBaseInv (m : ℕ) (x : Fin (2 * m + 1)) : Fin (2 * m + 1) :=
  if hx : x.val = 2 * m then ⟨0, by omega⟩
  else if hlo : x.val < m then ⟨2 * x.val + 1, by omega⟩
  else ⟨2 * (2 * m - x.val), by omega⟩

private def waleckiBaseEquiv (m : ℕ) : Fin (2 * m + 1) ≃ Fin (2 * m + 1) where
  toFun := waleckiBase m
  invFun := waleckiBaseInv m
  left_inv t := by
    ext
    unfold waleckiBase waleckiBaseInv
    by_cases h0 : t.val = 0
    · simp [h0]
    · by_cases hodd : t.val % 2 = 1
      · simp only [h0, ↓reduceDIte, hodd]
        have hlt : (t.val - 1) / 2 < m := by omega
        have hne : (t.val - 1) / 2 ≠ 2 * m := by omega
        simp only [hne, ↓reduceDIte, hlt]
        omega
      · simp only [h0, ↓reduceDIte, hodd]
        have hge : ¬ 2 * m - t.val / 2 < m := by omega
        have hne : 2 * m - t.val / 2 ≠ 2 * m := by omega
        simp only [hne, ↓reduceDIte, hge]
        omega
  right_inv x := by
    ext
    unfold waleckiBase waleckiBaseInv
    by_cases hx : x.val = 2 * m
    · simp [hx]
    · by_cases hlo : x.val < m
      · simp only [hx, ↓reduceDIte, hlo]
        have hne : 2 * x.val + 1 ≠ 0 := by omega
        have hodd : (2 * x.val + 1) % 2 = 1 := by omega
        simp only [hne, ↓reduceDIte, hodd]
        omega
      · simp only [hx, ↓reduceDIte, hlo]
        have hne : 2 * (2 * m - x.val) ≠ 0 := by omega
        have hev : ¬ (2 * (2 * m - x.val)) % 2 = 1 := by omega
        simp only [hne, ↓reduceDIte, hev]
        omega

private def rotEquiv (m : ℕ) (i : Fin m) : Fin (2 * m + 1) ≃ Fin (2 * m + 1) where
  toFun x :=
    if hx : x.val < 2 * m then ⟨(x.val + i.val) % (2 * m), by
      have hm : 0 < 2 * m := by omega
      have := Nat.mod_lt (x.val + i.val) hm; omega⟩
    else ⟨2 * m, by omega⟩
  invFun y :=
    if hy : y.val < 2 * m then ⟨(y.val + 2 * m - i.val) % (2 * m), by
      have hm : 0 < 2 * m := by omega
      have := Nat.mod_lt (y.val + 2 * m - i.val) hm; omega⟩
    else ⟨2 * m, by omega⟩
  left_inv x := by
    ext
    by_cases hx : x.val < 2 * m
    · have hm : 0 < 2 * m := by omega
      have hlt : (x.val + i.val) % (2 * m) < 2 * m := Nat.mod_lt _ hm
      simp only [hx, ↓reduceDIte, hlt]
      have hi : i.val < m := i.isLt
      have h1 : (x.val + i.val) % (2 * m) + 2 * m - i.val =
          ((x.val + i.val) % (2 * m) + (2 * m - i.val)) := by omega
      rw [h1, Nat.mod_add_mod, show x.val + i.val + (2 * m - i.val) = x.val + 2 * m by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hx]
    · simp [hx]; omega
  right_inv y := by
    ext
    by_cases hy : y.val < 2 * m
    · have hm : 0 < 2 * m := by omega
      have hlt : (y.val + 2 * m - i.val) % (2 * m) < 2 * m := Nat.mod_lt _ hm
      simp only [hy, ↓reduceDIte, hlt]
      have hi : i.val < m := i.isLt
      rw [Nat.mod_add_mod, show y.val + 2 * m - i.val + i.val = y.val + 2 * m by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hy]
    · simp [hy]; omega

private def waleckiPerm (m : ℕ) (i : Fin m) : Fin (2 * m + 1) ≃ Fin (2 * m + 1) :=
  (waleckiBaseEquiv m).trans (rotEquiv m i)

private def waleckiCycle (m : ℕ) (i : Fin m) : SimpleGraph (Fin (2 * m + 1)) :=
  (cycleGraph (2 * m + 1)).comap (waleckiPerm m i).symm

private lemma waleckiCycle_iso (m : ℕ) (i : Fin m) :
    Nonempty (waleckiCycle m i ≃g cycleGraph (2 * m + 1)) :=
  ⟨{ toEquiv := (waleckiPerm m i).symm, map_rel_iff' := Iff.rfl }⟩

private lemma cycleGraph_adj_iff_nat {N : ℕ} (hN : 3 ≤ N) (a b : Fin N) :
    (cycleGraph N).Adj a b ↔
      (a.val = (b.val + 1) % N ∨ b.val = (a.val + 1) % N) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 2 := ⟨N - 2, by omega⟩
  rw [SimpleGraph.cycleGraph_adj]
  have hsub : ∀ x y : Fin (k + 2), x - y = 1 ↔ x.val = (y.val + 1) % (k + 2) := by
    intro x y
    rw [sub_eq_iff_eq_add, Fin.ext_iff, Fin.val_add]
    have h1 : (1 : Fin (k + 2)).val = 1 := by
      simp [Nat.mod_eq_of_lt (show 1 < k + 2 by omega)]
    rw [h1, Nat.add_comm 1 y.val]
  rw [hsub a b, hsub b a]

private lemma mod_two_mul_le_one_iff {m s : ℕ} (hm : 1 ≤ m) (hlo : 2 ≤ s) (hhi : s < 4 * m) :
    s % (2 * m) ≤ 1 ↔ s = 2 * m ∨ s = 2 * m + 1 := by
  by_cases hlt : s < 2 * m
  · rw [Nat.mod_eq_of_lt hlt]; omega
  · have hsub : s = (s - 2 * m) + 2 * m := by omega
    conv_lhs => rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt (show s - 2 * m < 2 * m by omega)]
    omega

private lemma waleckiBase_adj_iff {m : ℕ} (hm : 1 ≤ m) (x y : Fin (2 * m + 1)) :
    (cycleGraph (2 * m + 1)).Adj ((waleckiBaseEquiv m).symm x) ((waleckiBaseEquiv m).symm y) ↔
      (x.val = 2 * m ∧ (y.val = 0 ∨ y.val = m)) ∨
      (y.val = 2 * m ∧ (x.val = 0 ∨ x.val = m)) ∨
      (x.val < 2 * m ∧ y.val < 2 * m ∧ x ≠ y ∧ (x.val + y.val + 1) % (2 * m) ≤ 1) := by
  rw [cycleGraph_adj_iff_nat (by omega)]
  change (((waleckiBaseInv m x).val = ((waleckiBaseInv m y).val + 1) % (2 * m + 1)) ∨
    ((waleckiBaseInv m y).val = ((waleckiBaseInv m x).val + 1) % (2 * m + 1))) ↔ _
  unfold waleckiBaseInv
  by_cases hx : x.val = 2 * m
  · by_cases hy : y.val = 2 * m
    · simp only [hx, hy, ↓reduceDIte, zero_add, lt_self_iff_false, true_and, false_and, false_or, or_false]
      have h1 : 1 % (2 * m + 1) = 1 := Nat.mod_eq_of_lt (by omega)
      rw [h1]; constructor <;> intro h <;> omega
    · by_cases hylo : y.val < m
      · simp only [hx, hy, hylo, ↓reduceDIte, zero_add, lt_self_iff_false, true_and, false_and, false_or, or_false]
        have h1 : 1 % (2 * m + 1) = 1 := Nat.mod_eq_of_lt (by omega)
        have h2 : (2 * y.val + 1 + 1) % (2 * m + 1) = 2 * y.val + 2 := Nat.mod_eq_of_lt (by omega)
        rw [h1, h2]
        constructor
        · intro h; left; omega
        · intro h; right; omega
      · simp only [hx, hy, hylo, ↓reduceDIte, zero_add, lt_self_iff_false, true_and, false_and, false_or, or_false]
        have h1 : 1 % (2 * m + 1) = 1 := Nat.mod_eq_of_lt (by omega)
        by_cases hym : y.val = m
        · have h2 : (2 * (2 * m - y.val) + 1) % (2 * m + 1) = 0 := by
            rw [show 2 * (2 * m - y.val) + 1 = 2 * m + 1 by omega, Nat.mod_self]
          rw [h1, h2]
          constructor
          · intro _; right; exact hym
          · intro _; left; rfl
        · have h2 : (2 * (2 * m - y.val) + 1) % (2 * m + 1) = 2 * (2 * m - y.val) + 1 :=
            Nat.mod_eq_of_lt (by omega)
          rw [h1, h2]; constructor <;> intro h <;> omega
  · by_cases hy : y.val = 2 * m
    · by_cases hxlo : x.val < m
      · simp only [hx, hy, hxlo, ↓reduceDIte, zero_add, lt_self_iff_false, true_and, false_and, and_false, false_or, or_false]
        have h1 : 1 % (2 * m + 1) = 1 := Nat.mod_eq_of_lt (by omega)
        have h2 : (2 * x.val + 1 + 1) % (2 * m + 1) = 2 * x.val + 2 := Nat.mod_eq_of_lt (by omega)
        rw [h1, h2]
        constructor
        · intro h; left; omega
        · intro h; left; omega
      · simp only [hx, hy, hxlo, ↓reduceDIte, zero_add, lt_self_iff_false, true_and, false_and, and_false, false_or, or_false]
        have h1 : 1 % (2 * m + 1) = 1 := Nat.mod_eq_of_lt (by omega)
        by_cases hxm : x.val = m
        · have h2 : (2 * (2 * m - x.val) + 1) % (2 * m + 1) = 0 := by
            rw [show 2 * (2 * m - x.val) + 1 = 2 * m + 1 by omega, Nat.mod_self]
          rw [h1, h2]
          constructor
          · intro _; right; exact hxm
          · intro _; right; rfl
        · have h2 : (2 * (2 * m - x.val) + 1) % (2 * m + 1) = 2 * (2 * m - x.val) + 1 :=
            Nat.mod_eq_of_lt (by omega)
          rw [h1, h2]; constructor <;> intro h <;> omega
    · have hxlt : x.val < 2 * m := by omega
      have hylt : y.val < 2 * m := by omega
      by_cases hxlo : x.val < m
      · by_cases hylo : y.val < m
        · simp only [hx, hy, hxlo, hylo, ↓reduceDIte, hxlt, hylt, false_and, false_or, true_and]
          have h1 : (2 * y.val + 1 + 1) % (2 * m + 1) = 2 * y.val + 2 :=
            Nat.mod_eq_of_lt (by omega)
          have h2 : (2 * x.val + 1 + 1) % (2 * m + 1) = 2 * x.val + 2 :=
            Nat.mod_eq_of_lt (by omega)
          rw [h1, h2]
          constructor
          · intro h; omega
          · rintro ⟨hne, hmod⟩
            have hne' : x.val ≠ y.val := fun h => hne (Fin.ext h)
            rw [Nat.mod_eq_of_lt (by omega)] at hmod
            omega
        · simp only [hx, hy, hxlo, hylo, ↓reduceDIte, hxlt, hylt, false_and, false_or, true_and]
          have hne : x ≠ y := fun h => by have := congrArg Fin.val h; omega
          have h2 : (2 * x.val + 1 + 1) % (2 * m + 1) = 2 * x.val + 2 :=
            Nat.mod_eq_of_lt (by omega)
          rw [h2, mod_two_mul_le_one_iff hm (by omega) (by omega)]
          by_cases hym : y.val = m
          · have h1 : (2 * (2 * m - y.val) + 1) % (2 * m + 1) = 0 := by
              rw [show 2 * (2 * m - y.val) + 1 = 2 * m + 1 by omega, Nat.mod_self]
            rw [h1]
            constructor <;> intro h <;> first | exact ⟨hne, by omega⟩ | omega
          · have h1 : (2 * (2 * m - y.val) + 1) % (2 * m + 1) = 2 * (2 * m - y.val) + 1 :=
              Nat.mod_eq_of_lt (by omega)
            rw [h1]
            constructor <;> intro h <;> first | exact ⟨hne, by omega⟩ | omega
      · by_cases hylo : y.val < m
        · simp only [hx, hy, hxlo, hylo, ↓reduceDIte, hxlt, hylt, false_and, false_or, true_and]
          have hne : x ≠ y := fun h => by have := congrArg Fin.val h; omega
          have h1 : (2 * y.val + 1 + 1) % (2 * m + 1) = 2 * y.val + 2 :=
            Nat.mod_eq_of_lt (by omega)
          rw [h1, mod_two_mul_le_one_iff hm (by omega) (by omega)]
          by_cases hxm : x.val = m
          · have h2 : (2 * (2 * m - x.val) + 1) % (2 * m + 1) = 0 := by
              rw [show 2 * (2 * m - x.val) + 1 = 2 * m + 1 by omega, Nat.mod_self]
            rw [h2]
            constructor <;> intro h <;> first | exact ⟨hne, by omega⟩ | omega
          · have h2 : (2 * (2 * m - x.val) + 1) % (2 * m + 1) = 2 * (2 * m - x.val) + 1 :=
              Nat.mod_eq_of_lt (by omega)
            rw [h2]
            constructor <;> intro h <;> first | exact ⟨hne, by omega⟩ | omega
        · simp only [hx, hy, hxlo, hylo, ↓reduceDIte, hxlt, hylt, false_and, false_or, true_and]
          have hne_rhs : ¬ (x ≠ y ∧ (x.val + y.val + 1) % (2 * m) ≤ 1) := by
            rintro ⟨hne, hmod⟩
            have hne' : x.val ≠ y.val := fun h => hne (Fin.ext h)
            have hmod' : (x.val + y.val + 1) % (2 * m) = x.val + y.val + 1 - 2 * m := by
              have hsub : x.val + y.val + 1 = (x.val + y.val + 1 - 2 * m) + 2 * m := by omega
              conv_lhs => rw [hsub, Nat.add_mod_right]
              exact Nat.mod_eq_of_lt (by omega)
            omega
          have hlhs : ¬ (2 * (2 * m - x.val) = (2 * (2 * m - y.val) + 1) % (2 * m + 1) ∨
              2 * (2 * m - y.val) = (2 * (2 * m - x.val) + 1) % (2 * m + 1)) := by
            have hval : ∀ z : ℕ, m ≤ z → z < 2 * m →
                (2 * (2 * m - z) + 1) % (2 * m + 1) = 0 ∨
                (2 * (2 * m - z) + 1) % (2 * m + 1) = 2 * (2 * m - z) + 1 := by
              intro z hzm hzlt
              by_cases hzm' : z = m
              · left; rw [show 2 * (2 * m - z) + 1 = 2 * m + 1 by omega, Nat.mod_self]
              · right; exact Nat.mod_eq_of_lt (by omega)
            rcases hval x.val (by omega) hxlt with h1 | h1 <;>
              rcases hval y.val (by omega) hylt with h2 | h2 <;> omega
          exact iff_of_false hlhs hne_rhs

private lemma shift_mod_zero_or_m {m u i : ℕ} (hu : u < 2 * m) (hi : i < m) :
    ((u + 2 * m - i) % (2 * m) = 0 ∨ (u + 2 * m - i) % (2 * m) = m) ↔
      (u = i ∨ u = i + m) := by
  by_cases hiu : i ≤ u
  · have heq : u + 2 * m - i = (u - i) + 2 * m := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

private lemma shift_sum_mod_iff {m u v i : ℕ} (hm : 1 ≤ m) (hu : u < 2 * m) (hv : v < 2 * m)
    (hi : i < m) :
    ((u + 2 * m - i) % (2 * m) + (v + 2 * m - i) % (2 * m) + 1) % (2 * m) ≤ 1 ↔
      ((u + v + 1) % (2 * m)) / 2 = i := by
  have hstep1 :
      ((u + 2 * m - i) % (2 * m) + (v + 2 * m - i) % (2 * m) + 1) % (2 * m) =
      (((u + v + 1) % (2 * m)) + (2 * m - 2 * i)) % (2 * m) := by
    calc ((u + 2 * m - i) % (2 * m) + (v + 2 * m - i) % (2 * m) + 1) % (2 * m)
        = ((u + 2 * m - i) % (2 * m) + ((v + 2 * m - i) % (2 * m) + 1)) % (2 * m) := by
          rw [add_assoc]
      _ = ((u + 2 * m - i) + ((v + 2 * m - i) % (2 * m) + 1)) % (2 * m) := Nat.mod_add_mod _ _ _
      _ = (((u + 2 * m - i) + 1) + (v + 2 * m - i) % (2 * m)) % (2 * m) := by congr 1; omega
      _ = (((u + 2 * m - i) + 1) + (v + 2 * m - i)) % (2 * m) := Nat.add_mod_mod _ _ _
      _ = ((u + v + 1 + (2 * m - 2 * i)) + 2 * m) % (2 * m) := by congr 1; omega
      _ = (u + v + 1 + (2 * m - 2 * i)) % (2 * m) := Nat.add_mod_right _ _
      _ = ((u + v + 1) % (2 * m) + (2 * m - 2 * i)) % (2 * m) := (Nat.mod_add_mod _ _ _).symm
  rw [hstep1]
  set r := (u + v + 1) % (2 * m)
  have hr : r < 2 * m := Nat.mod_lt _ (by omega)
  by_cases hri : r < 2 * i
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · have hsub : r + (2 * m - 2 * i) = (r - 2 * i) + 2 * m := by omega
    rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

private lemma waleckiCycle_adj_iff {m : ℕ} (hm : 1 ≤ m) (i : Fin m) (u v : Fin (2 * m + 1)) :
    (waleckiCycle m i).Adj u v ↔
      (u.val = 2 * m ∧ (v.val = i.val ∨ v.val = i.val + m)) ∨
      (v.val = 2 * m ∧ (u.val = i.val ∨ u.val = i.val + m)) ∨
      (u.val < 2 * m ∧ v.val < 2 * m ∧ u ≠ v ∧ ((u.val + v.val + 1) % (2 * m)) / 2 = i.val) := by
  change (cycleGraph (2 * m + 1)).Adj
    ((waleckiBaseEquiv m).symm ((rotEquiv m i).symm u))
    ((waleckiBaseEquiv m).symm ((rotEquiv m i).symm v)) ↔ _
  rw [waleckiBase_adj_iff hm]
  have hrot : ∀ w : Fin (2 * m + 1),
      ((rotEquiv m i).symm w).val =
        if w.val < 2 * m then (w.val + 2 * m - i.val) % (2 * m) else 2 * m := by
    intro w
    change (if hy : w.val < 2 * m then _ else _ : Fin (2 * m + 1)).val = _
    split_ifs <;> rfl
  have hinj : ((rotEquiv m i).symm u ≠ (rotEquiv m i).symm v) ↔ u ≠ v :=
    not_iff_not.mpr (rotEquiv m i).symm.injective.eq_iff
  rw [hinj, hrot u, hrot v]
  by_cases hu : u.val < 2 * m <;> by_cases hv : v.val < 2 * m
  · have hmu : (u.val + 2 * m - i.val) % (2 * m) < 2 * m := Nat.mod_lt _ (by omega)
    have hmv : (v.val + 2 * m - i.val) % (2 * m) < 2 * m := Nat.mod_lt _ (by omega)
    simp only [hu, hv, ↓reduceIte, hmu, hmv, true_and,
      show ¬ (u.val + 2 * m - i.val) % (2 * m) = 2 * m by omega,
      show ¬ (v.val + 2 * m - i.val) % (2 * m) = 2 * m by omega,
      show ¬ u.val = 2 * m by omega, show ¬ v.val = 2 * m by omega, false_and, false_or]
    rw [shift_sum_mod_iff hm hu hv i.isLt]
  · have hmu : (u.val + 2 * m - i.val) % (2 * m) < 2 * m := Nat.mod_lt _ (by omega)
    have hv_eq : v.val = 2 * m := by omega
    simp only [hu, hv, hv_eq, ↓reduceIte, hmu, true_and, false_and, false_or, or_false,
      show ¬ (u.val + 2 * m - i.val) % (2 * m) = 2 * m by omega,
      show ¬ u.val = 2 * m by omega, show ¬ 2 * m < 2 * m by omega]
    exact shift_mod_zero_or_m hu i.isLt
  · have hmv : (v.val + 2 * m - i.val) % (2 * m) < 2 * m := Nat.mod_lt _ (by omega)
    have hu_eq : u.val = 2 * m := by omega
    simp only [hu, hv, hu_eq, ↓reduceIte, hmv, true_and, false_and, false_or, or_false,
      show ¬ (v.val + 2 * m - i.val) % (2 * m) = 2 * m by omega,
      show ¬ v.val = 2 * m by omega, show ¬ 2 * m < 2 * m by omega]
    exact shift_mod_zero_or_m hv i.isLt
  · have hu_eq : u.val = 2 * m := by omega
    have hv_eq : v.val = 2 * m := by omega
    have hi : i.val < m := i.isLt
    simp only [hu, hv, hu_eq, hv_eq, ↓reduceIte, true_and, false_and, or_false,
      show ¬ 2 * m < 2 * m by omega]
    omega

private lemma walecki_decomp {m : ℕ} (hm : 1 ≤ m) (u v : Fin (2 * m + 1)) :
    (completeGraph (Fin (2 * m + 1))).Adj u v ↔ ∃! i : Fin m, (waleckiCycle m i).Adj u v := by
  simp only [completeGraph_eq_top, top_adj]
  constructor
  · intro huv
    by_cases hu : u.val = 2 * m
    · have hv : v.val < 2 * m := by
        have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
        omega
      refine ⟨⟨v.val % m, Nat.mod_lt _ (by omega)⟩, ?_, ?_⟩
      · dsimp only
        rw [waleckiCycle_adj_iff hm]
        left
        refine ⟨hu, ?_⟩
        by_cases hvm : v.val < m
        · left; exact (Nat.mod_eq_of_lt hvm).symm
        · right
          dsimp only
          have hsub : v.val = (v.val - m) + m := by omega
          conv_rhs => rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          omega
      · intro i hi
        rw [waleckiCycle_adj_iff hm] at hi
        ext
        dsimp only
        have h1 : v.val = i.val ∨ v.val = i.val + m := by
          rcases hi with ⟨-, h⟩ | ⟨hv', -⟩ | ⟨hu', -⟩
          · exact h
          · omega
          · omega
        rcases h1 with h1 | h1
        · rw [h1, Nat.mod_eq_of_lt i.isLt]
        · rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
    · by_cases hv : v.val = 2 * m
      · have hu' : u.val < 2 * m := by omega
        refine ⟨⟨u.val % m, Nat.mod_lt _ (by omega)⟩, ?_, ?_⟩
        · dsimp only
          rw [waleckiCycle_adj_iff hm]
          right; left
          refine ⟨hv, ?_⟩
          by_cases hum : u.val < m
          · left; exact (Nat.mod_eq_of_lt hum).symm
          · right
            dsimp only
            have hsub : u.val = (u.val - m) + m := by omega
            conv_rhs => rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            omega
        · intro i hi
          rw [waleckiCycle_adj_iff hm] at hi
          ext
          dsimp only
          have h1 : u.val = i.val ∨ u.val = i.val + m := by
            rcases hi with ⟨hu2, -⟩ | ⟨-, h⟩ | ⟨-, hv2, -⟩
            · omega
            · exact h
            · omega
          rcases h1 with h1 | h1
          · rw [h1, Nat.mod_eq_of_lt i.isLt]
          · rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
      · have hu' : u.val < 2 * m := by omega
        have hv' : v.val < 2 * m := by omega
        have hdiv : ((u.val + v.val + 1) % (2 * m)) / 2 < m := by
          have := Nat.mod_lt (u.val + v.val + 1) (show 0 < 2 * m by omega)
          omega
        refine ⟨⟨((u.val + v.val + 1) % (2 * m)) / 2, hdiv⟩, ?_, ?_⟩
        · dsimp only
          rw [waleckiCycle_adj_iff hm]
          right; right
          exact ⟨hu', hv', huv, rfl⟩
        · intro i hi
          rw [waleckiCycle_adj_iff hm] at hi
          ext
          dsimp only
          rcases hi with ⟨hu2, -⟩ | ⟨hv2, -⟩ | ⟨-, -, -, heq⟩
          · omega
          · omega
          · exact heq.symm
  · rintro ⟨i, hi, -⟩
    exact (waleckiCycle m i).ne_of_adj hi

end OMA.Proof_AlspachConjecture_oberwolfach_R1_H1

theorem OMA.solution : OMA.R_AlspachConjecture_alspach_conjecture_variants_oberwolfach_R1.H1 := by
  intro n hn h3
  obtain ⟨m, rfl⟩ := hn
  have hm : 1 ≤ m := by omega
  have hdiv : (2 * m + 1 - 1) / 2 = m := by omega
  rw [hdiv]
  exact ⟨OMA.Proof_AlspachConjecture_oberwolfach_R1_H1.waleckiCycle m,
    OMA.Proof_AlspachConjecture_oberwolfach_R1_H1.waleckiCycle_iso m,
    OMA.Proof_AlspachConjecture_oberwolfach_R1_H1.walecki_decomp hm⟩
