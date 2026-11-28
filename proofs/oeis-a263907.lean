import OMAStatements.S_oeis_a263907

open OMA.S_oeis_a263907 PowerSeries

namespace A263907Proof

abbrev Row := Fin 4 → Fin 2
abbrev St := Fin 4 → Fin 3

def good (r : Row) : Prop := (8 * (r 0).val + 4 * (r 1).val + 2 * (r 2).val + (r 3).val) % 3 = 1

instance (r : Row) : Decidable (good r) := by unfold good; infer_instance

def dl (u v : Row) : St := fun j => ⟨(2 * (u j).val + (v j).val) % 3, Nat.mod_lt _ (by norm_num)⟩

def stp (f : St → ℕ) (s : St) : ℕ :=
  ∑ u : Row, ∑ v : Row, if good u ∧ good v then f (s - dl u v) else 0

def cnt : ℕ → St → ℕ
  | 0, s => if s = 0 then 1 else 0
  | k + 1, s => stp (cnt k) s

theorem rowVal_mod (r : Row) : rowVal r % 3 = 1 ↔ good r := by
  simp only [rowVal, good, Fin.sum_univ_four]
  simp
  constructor <;> intro h <;> omega

theorem colVal_cons {m : ℕ} (r : Row) (B : Fin m → Row) (j : Fin 4) :
    colVal (Fin.cons r B : Fin (m + 1) → Row) j = (r j).val * 2 ^ m + colVal B j := by
  unfold colVal
  rw [Fin.sum_univ_succ]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  simp only [Fin.val_succ]
  omega

def G (m : ℕ) (s : St) : ℕ :=
  (Finset.univ.filter fun B : Fin m → Row =>
    (∀ i, rowVal (B i) % 3 = 1) ∧ ∀ j, colVal B j % 3 = (s j).val).card

theorem col_step (m : ℕ) (hm : 2 ^ m % 3 = 1) (u v : Row) (c : ℕ) (s : St) (j : Fin 4) :
    ((u j).val * 2 ^ (m + 1) + ((v j).val * 2 ^ m + c)) % 3 = (s j).val ↔
      c % 3 = ((s - dl u v) j).val := by
  rw [pow_succ]
  generalize 2 ^ m = P at hm ⊢
  have hs := (s j).isLt
  simp only [Pi.sub_apply, Fin.sub_def, dl]
  have hu := (u j).isLt
  have hv := (v j).isLt
  generalize (u j).val = x at hu ⊢
  generalize (v j).val = y at hv ⊢
  generalize (s j).val = z at hs ⊢
  interval_cases x <;> interval_cases y <;> simp <;> omega

theorem G_succ (m : ℕ) (hm : 2 ^ m % 3 = 1) (s : St) : G (m + 2) s = stp (G m) s := by
  rw [G, Finset.card_filter, ← (Fin.consEquiv fun _ => Row).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← (Fin.consEquiv fun _ => Row).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.forall_fin_succ (n := m + 1),
    Fin.forall_fin_succ (n := m), Fin.cons_zero, Fin.cons_succ,
    colVal_cons, rowVal_mod, col_step m hm]
  by_cases h : good u ∧ good v
  · rw [if_pos h, G, Finset.card_filter]
    exact Finset.sum_congr rfl fun B _ => by simp [h, rowVal_mod]
  · rw [if_neg h, Finset.sum_eq_zero]
    intro B _
    rw [if_neg]
    tauto

theorem G_zero (s : St) : G 0 s = cnt 0 s := by
  rw [G, cnt]
  by_cases hs : s = 0
  · rw [if_pos hs, Finset.card_eq_one]
    refine ⟨fun i => i.elim0, ?_⟩
    ext B
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun _ => funext fun i => i.elim0, fun _ => ⟨fun i => i.elim0, fun j => ?_⟩⟩
    simp [colVal, hs]
  · rw [if_neg hs, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro B - ⟨-, h⟩
    apply hs
    funext j
    have := h j
    simp [colVal] at this
    exact Fin.ext this.symm

theorem G_eq (k : ℕ) : ∀ s, G (2 * k) s = cnt k s := by
  induction k with
  | zero => exact G_zero
  | succ k ih =>
    intro s
    have hm : 2 ^ (2 * k) % 3 = 1 := by
      rw [pow_mul, Nat.pow_mod]; norm_num
    show G (2 * k + 2) s = stp (cnt k) s
    rw [G_succ _ hm]
    congr 1
    funext t
    exact ih t

theorem a_eq (n : ℕ) : a n = cnt (n + 1) 1 := by
  rw [← G_eq]
  show _ = G (2 * n + 2) 1
  rw [a, G]
  congr 1

-- Tables of cnt k on all 81 states, indexed by 27 s0 + 9 s1 + 3 s2 + s3.
def idx (s : St) : ℕ := 27 * (s 0).val + 9 * (s 1).val + 3 * (s 2).val + (s 3).val

def L1 : List ℕ := [5, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0,
  0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1,
  0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]

def L2 : List ℕ := [45, 0, 0, 0, 25, 0, 0, 0, 25, 0, 0, 25, 25, 0, 0, 0, 23, 0, 0, 25, 0, 0, 0,
  23, 25, 0, 0, 0, 25, 0, 0, 0, 23, 25, 0, 0, 25, 0, 0, 0, 16, 0, 0, 0, 16, 0, 0, 23, 23, 0, 0, 0,
  16, 0, 0, 0, 25, 25, 0, 0, 0, 23, 0, 0, 23, 0, 0, 0, 16, 23, 0, 0, 25, 0, 0, 0, 16, 0, 0, 0, 16]

def L3 : List ℕ := [709, 0, 0, 0, 597, 0, 0, 0, 597, 0, 0, 597, 597, 0, 0, 0, 573, 0, 0, 597, 0,
  0, 0, 573, 597, 0, 0, 0, 597, 0, 0, 0, 573, 597, 0, 0, 597, 0, 0, 0, 528, 0, 0, 0, 528, 0, 0,
  573, 573, 0, 0, 0, 528, 0, 0, 0, 597, 597, 0, 0, 0, 573, 0, 0, 573, 0, 0, 0, 528, 573, 0, 0,
  597, 0, 0, 0, 528, 0, 0, 0, 528]

def L4 : List ℕ := [15293, 0, 0, 0, 14617, 0, 0, 0, 14617, 0, 0, 14617, 14617, 0, 0, 0, 14407, 0,
  0, 14617, 0, 0, 0, 14407, 14617, 0, 0, 0, 14617, 0, 0, 0, 14407, 14617, 0, 0, 14617, 0, 0, 0,
  14112, 0, 0, 0, 14112, 0, 0, 14407, 14407, 0, 0, 0, 14112, 0, 0, 0, 14617, 14617, 0, 0, 0,
  14407, 0, 0, 14407, 0, 0, 0, 14112, 14407, 0, 0, 14617, 0, 0, 0, 14112, 0, 0, 0, 14112]

def tb (L : List ℕ) (s : St) : ℕ := L.getD (idx s) 0

theorem chk1 : ∀ s, stp (cnt 0) s = tb L1 s := by decide +kernel
theorem chk2 : ∀ s, stp (tb L1) s = tb L2 s := by decide +kernel
theorem chk3 : ∀ s, stp (tb L2) s = tb L3 s := by decide +kernel
theorem chk4 : ∀ s, stp (tb L3) s = tb L4 s := by decide +kernel

theorem cnt1 : cnt 1 = tb L1 := funext chk1
theorem cnt2 : cnt 2 = tb L2 := by
  funext s; show stp (cnt 1) s = _; rw [cnt1]; exact chk2 s
theorem cnt3 : cnt 3 = tb L3 := by
  funext s; show stp (cnt 2) s = _; rw [cnt2]; exact chk3 s
theorem cnt4 : cnt 4 = tb L4 := by
  funext s; show stp (cnt 3) s = _; rw [cnt3]; exact chk4 s

def W (k : ℕ) (s : St) : ℤ :=
  (cnt (k + 4) s : ℤ) - 37 * cnt (k + 3) s + 339 * cnt (k + 2) s - 1003 * cnt (k + 1) s +
    700 * cnt k s

theorem W_succ (k : ℕ) (s : St) :
    W (k + 1) s = ∑ u : Row, ∑ v : Row, if good u ∧ good v then W k (s - dl u v) else 0 := by
  have e : ∀ j, (cnt (j + 1) s : ℤ) = ∑ u : Row, ∑ v : Row,
      if good u ∧ good v then (cnt j (s - dl u v) : ℤ) else 0 := by
    intro j
    show ((stp (cnt j) s : ℕ) : ℤ) = _
    unfold stp
    push_cast [Nat.cast_sum, Nat.cast_ite]
    rfl
  have hr : ∀ u v : Row, (if good u ∧ good v then W k (s - dl u v) else 0) =
      (if good u ∧ good v then (cnt (k + 4) (s - dl u v) : ℤ) else 0) -
      37 * (if good u ∧ good v then (cnt (k + 3) (s - dl u v) : ℤ) else 0) +
      339 * (if good u ∧ good v then (cnt (k + 2) (s - dl u v) : ℤ) else 0) -
      1003 * (if good u ∧ good v then (cnt (k + 1) (s - dl u v) : ℤ) else 0) +
      700 * (if good u ∧ good v then (cnt k (s - dl u v) : ℤ) else 0) := by
    intro u v
    unfold W
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => hr u v]
  show (cnt (k + 4 + 1) s : ℤ) - 37 * cnt (k + 3 + 1) s + 339 * cnt (k + 2 + 1) s -
    1003 * cnt (k + 1 + 1) s + 700 * cnt (k + 1) s = _
  rw [e (k + 4), e (k + 3), e (k + 2), e (k + 1), e k]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

theorem W0_chk : ∀ s : St, (tb L4 s : ℤ) - 37 * tb L3 s + 339 * tb L2 s - 1003 * tb L1 s +
    700 * cnt 0 s = 0 := by decide +kernel

theorem W_zero (k : ℕ) : ∀ s, W k s = 0 := by
  induction k with
  | zero =>
    intro s
    unfold W
    rw [Nat.zero_add, Nat.zero_add, Nat.zero_add, Nat.zero_add, cnt1, cnt2, cnt3, cnt4]
    exact W0_chk s
  | succ k ih =>
    intro s
    rw [W_succ]
    refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => ?_
    split_ifs
    · exact ih _
    · rfl

theorem a0 : a 0 = 0 := by rw [a_eq, cnt1]; decide +kernel
theorem a1 : a 1 = 16 := by rw [a_eq, cnt2]; decide +kernel
theorem a2 : a 2 = 528 := by rw [a_eq, cnt3]; decide +kernel
theorem a3 : a 3 = 14112 := by rw [a_eq, cnt4]; decide +kernel

theorem a_rec (n : ℕ) : (a (n + 4) : ℤ) =
    37 * a (n + 3) - 339 * a (n + 2) + 1003 * a (n + 1) - 700 * a n := by
  have h := W_zero (n + 1) 1
  simp only [W] at h
  rw [a_eq, a_eq, a_eq, a_eq, a_eq]
  rw [show n + 4 + 1 = n + 1 + 4 by ring, show n + 3 + 1 = n + 1 + 3 by ring,
    show n + 2 + 1 = n + 1 + 2 by ring]
  linarith

theorem closed (n : ℕ) : 27 * (a n : ℤ) = 3 - 4 * 7 ^ (1 + n) + 25 ^ (1 + n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n) with h | h | h | h | h
    · subst h; rw [a0]; norm_num
    · subst h; rw [a1]; norm_num
    · subst h; rw [a2]; norm_num
    · subst h; rw [a3]; norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have h0 := ih m (by omega)
      have h1 := ih (m + 1) (by omega)
      have h2 := ih (m + 2) (by omega)
      have h3 := ih (m + 3) (by omega)
      rw [a_rec]
      have e7 : (7 : ℤ) ^ (1 + (m + 4)) = 7 ^ 4 * 7 ^ (1 + m) := by ring
      have e25 : (25 : ℤ) ^ (1 + (m + 4)) = 25 ^ 4 * 25 ^ (1 + m) := by ring
      have f7 : ∀ i : ℕ, (7 : ℤ) ^ (1 + (m + i)) = 7 ^ i * 7 ^ (1 + m) := fun i => by ring
      have f25 : ∀ i : ℕ, (25 : ℤ) ^ (1 + (m + i)) = 25 ^ i * 25 ^ (1 + m) := fun i => by ring
      rw [f7, f25] at h1 h2 h3
      rw [e7, e25]
      linear_combination 37 * h3 - 339 * h2 + 1003 * h1 - 700 * h0

theorem gf :
    (1 - X) * (1 - 7 * X) * (1 - 25 * X) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (16 * X : PowerSeries ℤ) := by
  set s : PowerSeries ℤ := mk (fun n => if n = 0 then 0 else (a n : ℤ)) with hs
  have hd : (1 - X) * (1 - 7 * X) * (1 - 25 * X) * s =
      s - (s * C (33 : ℤ)) * X ^ 1 + (s * C (207 : ℤ)) * X ^ 2 - (s * C (175 : ℤ)) * X ^ 3 := by
    simp only [pow_one, map_ofNat]
    ring
  have hn : (16 * X : PowerSeries ℤ) = C (16 : ℤ) * X ^ 1 := by
    simp only [pow_one, map_ofNat]
  rw [hd, hn]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_mul_C, coeff_C, hs, coeff_mk]
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n) with h | h | h | h
  · subst h; simp
  · subst h; simp [a1]
  · subst h; simp [a1, a2]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have h0 := closed m
    have h1 := closed (m + 1)
    have h2 := closed (m + 2)
    have h3 := closed (m + 3)
    have f7 : ∀ i : ℕ, (7 : ℤ) ^ (1 + (m + i)) = 7 ^ i * 7 ^ (1 + m) := fun i => by ring
    have f25 : ∀ i : ℕ, (25 : ℤ) ^ (1 + (m + i)) = 25 ^ i * 25 ^ (1 + m) := fun i => by ring
    rw [f7, f25] at h1 h2 h3
    have key27 : 27 * ((a (m + 3) : ℤ) - 33 * a (m + 2) + 207 * a (m + 1) - 175 * a m) = 0 := by
      linear_combination h3 - 33 * h2 + 207 * h1 - 175 * h0
    have key : (a (m + 3) : ℤ) - 33 * a (m + 2) + 207 * a (m + 1) - 175 * a m = 0 := by
      omega
    simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
      show m + 3 - 3 = m by omega]
    have hm0 : (if m = 0 then (0 : ℤ) else (a m : ℤ)) = a m := by
      split_ifs with hm
      · subst hm; rw [a0]; simp
      · rfl
    simp [hm0]
    linarith

end A263907Proof

open A263907Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a263907.main :=
  ⟨gf, fun n _ => closed n⟩

