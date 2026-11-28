import OMAStatements.S_oeis_a263908

open OMA.S_oeis_a263908 PowerSeries

namespace A263908Proof

abbrev Row := Fin 5 → Fin 2
abbrev St := Fin 5 → Fin 3

def good (r : Row) : Prop :=
  (16 * (r 0).val + 8 * (r 1).val + 4 * (r 2).val + 2 * (r 3).val + (r 4).val) % 3 = 1

instance (r : Row) : Decidable (good r) := by unfold good; infer_instance

def dl (u v : Row) : St := fun j => ⟨(2 * (u j).val + (v j).val) % 3, Nat.mod_lt _ (by norm_num)⟩

def e1 (u : Row) : St := fun j => ⟨(u j).val, by have := (u j).isLt; omega⟩

def stp (f : St → ℕ) (s : St) : ℕ :=
  ∑ u : Row, ∑ v : Row, if good u ∧ good v then f (s - dl u v) else 0

def cnt : ℕ → St → ℕ
  | 0, s => if s = 0 then 1 else 0
  | k + 1, s => stp (cnt k) s

theorem rowVal_mod (r : Row) : rowVal r % 3 = 1 ↔ good r := by
  simp only [rowVal, good, Fin.sum_univ_five]
  simp
  constructor <;> intro h <;> omega

theorem colVal_cons {m : ℕ} (r : Row) (B : Fin m → Row) (j : Fin 5) :
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

theorem col_step (m : ℕ) (hm : 2 ^ m % 3 = 1) (u v : Row) (c : ℕ) (s : St) (j : Fin 5) :
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

theorem col_step1 (m : ℕ) (hm : 2 ^ m % 3 = 1) (u : Row) (c : ℕ) (s : St) (j : Fin 5) :
    ((u j).val * 2 ^ m + c) % 3 = (s j).val ↔ c % 3 = ((s - e1 u) j).val := by
  generalize 2 ^ m = P at hm ⊢
  have hs := (s j).isLt
  simp only [Pi.sub_apply, Fin.sub_def, e1]
  have hu := (u j).isLt
  generalize (u j).val = x at hu ⊢
  generalize (s j).val = z at hs ⊢
  interval_cases x <;> simp <;> omega

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

theorem G_succ1 (m : ℕ) (hm : 2 ^ m % 3 = 1) (s : St) :
    G (m + 1) s = ∑ u : Row, if good u then G m (s - e1 u) else 0 := by
  rw [G, Finset.card_filter, ← (Fin.consEquiv fun _ => Row).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.forall_fin_succ (n := m), Fin.cons_zero,
    Fin.cons_succ, colVal_cons, rowVal_mod, col_step1 m hm]
  by_cases h : good u
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

theorem pow_mod3 (k : ℕ) : 2 ^ (2 * k) % 3 = 1 := by
  rw [pow_mul, Nat.pow_mod]; norm_num

theorem G_eq (k : ℕ) : ∀ s, G (2 * k) s = cnt k s := by
  induction k with
  | zero => exact G_zero
  | succ k ih =>
    intro s
    show G (2 * k + 2) s = stp (cnt k) s
    rw [G_succ _ (pow_mod3 k)]
    congr 1
    funext t
    exact ih t

theorem a_eq (n : ℕ) : a n = ∑ u : Row, if good u then cnt n (1 - e1 u) else 0 := by
  have h : a n = G (2 * n + 1) 1 := by
    rw [a, G]
    congr 1
  rw [h, G_succ1 _ (pow_mod3 n)]
  simp only [G_eq]

-- Tables of cnt k on all 243 states, indexed by 81 s0 + 27 s1 + 9 s2 + 3 s3 + s4.
def idx (s : St) : ℕ := 81 * (s 0).val + 27 * (s 1).val + 9 * (s 2).val + 3 * (s 3).val + (s 4).val

def L1 : List ℕ := [
  11, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 3, 3, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 1, 3, 0, 0, 0, 3, 0, 0,
  0, 1, 3, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 3, 3, 0, 0, 0, 1,
  0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 3, 3, 0, 0, 0, 1, 0, 0, 1, 0,
  0, 0, 1, 1, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 1, 3, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0,
  0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  1, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 3, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0,
  0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3,
  0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]

def L2 : List ℕ := [
  351, 0, 0, 0, 231, 0, 0, 0, 231, 0, 0, 231, 231, 0, 0, 0, 179, 0, 0, 231, 0, 0, 0, 179, 231,
  0, 0, 0, 231, 0, 0, 0, 179, 231, 0, 0, 231, 0, 0, 0, 161, 0, 0, 0, 161, 0, 0, 179, 179, 0, 0,
  0, 161, 0, 0, 0, 231, 231, 0, 0, 0, 179, 0, 0, 179, 0, 0, 0, 161, 179, 0, 0, 231, 0, 0, 0,
  161, 0, 0, 0, 161, 0, 0, 231, 231, 0, 0, 0, 179, 0, 0, 179, 0, 0, 0, 161, 179, 0, 0, 231, 0,
  0, 0, 161, 0, 0, 0, 161, 231, 0, 0, 0, 161, 0, 0, 0, 161, 0, 0, 161, 161, 0, 0, 0, 126, 0, 0,
  161, 0, 0, 0, 126, 161, 0, 0, 0, 179, 0, 0, 0, 161, 179, 0, 0, 179, 0, 0, 0, 126, 0, 0, 0,
  126, 0, 0, 161, 161, 0, 0, 0, 126, 0, 0, 231, 0, 0, 0, 179, 231, 0, 0, 231, 0, 0, 0, 161, 0,
  0, 0, 161, 0, 0, 179, 179, 0, 0, 0, 161, 0, 0, 0, 179, 179, 0, 0, 0, 161, 0, 0, 161, 0, 0, 0,
  126, 161, 0, 0, 179, 0, 0, 0, 126, 0, 0, 0, 126, 231, 0, 0, 0, 161, 0, 0, 0, 161, 0, 0, 161,
  161, 0, 0, 0, 126, 0, 0, 161, 0, 0, 0, 126, 161, 0, 0]

def L3 : List ℕ := [
  26131, 0, 0, 0, 23391, 0, 0, 0, 23391, 0, 0, 23391, 23391, 0, 0, 0, 22053, 0, 0, 23391, 0, 0,
  0, 22053, 23391, 0, 0, 0, 23391, 0, 0, 0, 22053, 23391, 0, 0, 23391, 0, 0, 0, 21189, 0, 0, 0,
  21189, 0, 0, 22053, 22053, 0, 0, 0, 21189, 0, 0, 0, 23391, 23391, 0, 0, 0, 22053, 0, 0, 22053,
  0, 0, 0, 21189, 22053, 0, 0, 23391, 0, 0, 0, 21189, 0, 0, 0, 21189, 0, 0, 23391, 23391, 0, 0,
  0, 22053, 0, 0, 22053, 0, 0, 0, 21189, 22053, 0, 0, 23391, 0, 0, 0, 21189, 0, 0, 0, 21189,
  23391, 0, 0, 0, 21189, 0, 0, 0, 21189, 0, 0, 21189, 21189, 0, 0, 0, 20088, 0, 0, 21189, 0, 0,
  0, 20088, 21189, 0, 0, 0, 22053, 0, 0, 0, 21189, 22053, 0, 0, 22053, 0, 0, 0, 20088, 0, 0, 0,
  20088, 0, 0, 21189, 21189, 0, 0, 0, 20088, 0, 0, 23391, 0, 0, 0, 22053, 23391, 0, 0, 23391, 0,
  0, 0, 21189, 0, 0, 0, 21189, 0, 0, 22053, 22053, 0, 0, 0, 21189, 0, 0, 0, 22053, 22053, 0, 0,
  0, 21189, 0, 0, 21189, 0, 0, 0, 20088, 21189, 0, 0, 22053, 0, 0, 0, 20088, 0, 0, 0, 20088,
  23391, 0, 0, 0, 21189, 0, 0, 0, 21189, 0, 0, 21189, 21189, 0, 0, 0, 20088, 0, 0, 21189, 0, 0,
  0, 20088, 21189, 0, 0]

def L4 : List ℕ := [
  2767631, 0, 0, 0, 2692695, 0, 0, 0, 2692695, 0, 0, 2692695, 2692695, 0, 0, 0, 2655355, 0, 0,
  2692695, 0, 0, 0, 2655355, 2692695, 0, 0, 0, 2692695, 0, 0, 0, 2655355, 2692695, 0, 0,
  2692695, 0, 0, 0, 2624305, 0, 0, 0, 2624305, 0, 0, 2655355, 2655355, 0, 0, 0, 2624305, 0, 0,
  0, 2692695, 2692695, 0, 0, 0, 2655355, 0, 0, 2655355, 0, 0, 0, 2624305, 2655355, 0, 0,
  2692695, 0, 0, 0, 2624305, 0, 0, 0, 2624305, 0, 0, 2692695, 2692695, 0, 0, 0, 2655355, 0, 0,
  2655355, 0, 0, 0, 2624305, 2655355, 0, 0, 2692695, 0, 0, 0, 2624305, 0, 0, 0, 2624305,
  2692695, 0, 0, 0, 2624305, 0, 0, 0, 2624305, 0, 0, 2624305, 2624305, 0, 0, 0, 2590110, 0, 0,
  2624305, 0, 0, 0, 2590110, 2624305, 0, 0, 0, 2655355, 0, 0, 0, 2624305, 2655355, 0, 0,
  2655355, 0, 0, 0, 2590110, 0, 0, 0, 2590110, 0, 0, 2624305, 2624305, 0, 0, 0, 2590110, 0, 0,
  2692695, 0, 0, 0, 2655355, 2692695, 0, 0, 2692695, 0, 0, 0, 2624305, 0, 0, 0, 2624305, 0, 0,
  2655355, 2655355, 0, 0, 0, 2624305, 0, 0, 0, 2655355, 2655355, 0, 0, 0, 2624305, 0, 0,
  2624305, 0, 0, 0, 2590110, 2624305, 0, 0, 2655355, 0, 0, 0, 2590110, 0, 0, 0, 2590110,
  2692695, 0, 0, 0, 2624305, 0, 0, 0, 2624305, 0, 0, 2624305, 2624305, 0, 0, 0, 2590110, 0, 0,
  2624305, 0, 0, 0, 2590110, 2624305, 0, 0]

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
  (cnt (k + 4) s : ℤ) - 169 * cnt (k + 3) s + 6387 * cnt (k + 2) s - 71671 * cnt (k + 1) s +
    195052 * cnt k s

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
      169 * (if good u ∧ good v then (cnt (k + 3) (s - dl u v) : ℤ) else 0) +
      6387 * (if good u ∧ good v then (cnt (k + 2) (s - dl u v) : ℤ) else 0) -
      71671 * (if good u ∧ good v then (cnt (k + 1) (s - dl u v) : ℤ) else 0) +
      195052 * (if good u ∧ good v then (cnt k (s - dl u v) : ℤ) else 0) := by
    intro u v
    unfold W
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => hr u v]
  show (cnt (k + 4 + 1) s : ℤ) - 169 * cnt (k + 3 + 1) s + 6387 * cnt (k + 2 + 1) s -
    71671 * cnt (k + 1 + 1) s + 195052 * cnt (k + 1) s = _
  rw [e (k + 4), e (k + 3), e (k + 2), e (k + 1), e k]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

theorem W0_chk : ∀ s : St, (tb L4 s : ℤ) - 169 * tb L3 s + 6387 * tb L2 s - 71671 * tb L1 s +
    195052 * cnt 0 s = 0 := by decide +kernel

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

theorem a0 : a 0 = 1 := by
  rw [a_eq]; simp only [cnt]; decide +kernel
theorem a1 : a 1 = 33 := by rw [a_eq, cnt1]; decide +kernel
theorem a2 : a 2 = 2399 := by rw [a_eq, cnt2]; decide +kernel
theorem a3 : a 3 = 252097 := by rw [a_eq, cnt3]; decide +kernel

theorem a_rec (n : ℕ) : (a (n + 4) : ℤ) =
    169 * a (n + 3) - 6387 * a (n + 2) + 71671 * a (n + 1) - 195052 * a n := by
  have h : (∑ u : Row, if good u then W n (1 - e1 u) else 0) = 0 :=
    Finset.sum_eq_zero fun u _ => by split_ifs <;> simp [W_zero]
  have hr : ∀ u : Row, (if good u then W n (1 - e1 u) else 0) =
      (if good u then (cnt (n + 4) (1 - e1 u) : ℤ) else 0) -
      169 * (if good u then (cnt (n + 3) (1 - e1 u) : ℤ) else 0) +
      6387 * (if good u then (cnt (n + 2) (1 - e1 u) : ℤ) else 0) -
      71671 * (if good u then (cnt (n + 1) (1 - e1 u) : ℤ) else 0) +
      195052 * (if good u then (cnt n (1 - e1 u) : ℤ) else 0) := by
    intro u
    unfold W
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun u _ => hr u] at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  rw [a_eq, a_eq, a_eq, a_eq, a_eq]
  push_cast [Nat.cast_sum, Nat.cast_ite]
  linarith

theorem closed (n : ℕ) :
    81 * (a n : ℤ) = 5 * 2 ^ (1 + 2 * n) + 11 ^ (1 + 2 * n) + 31 * 13 ^ n + 29 * 31 ^ n := by
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
      have f2 : ∀ i : ℕ, (2 : ℤ) ^ (1 + 2 * (m + i)) = 4 ^ i * 2 ^ (1 + 2 * m) := fun i => by
        rw [show 1 + 2 * (m + i) = 2 * i + (1 + 2 * m) by ring, pow_add, pow_mul]; norm_num
      have f11 : ∀ i : ℕ, (11 : ℤ) ^ (1 + 2 * (m + i)) = 121 ^ i * 11 ^ (1 + 2 * m) := fun i => by
        rw [show 1 + 2 * (m + i) = 2 * i + (1 + 2 * m) by ring, pow_add, pow_mul]; norm_num
      have f13 : ∀ i : ℕ, (13 : ℤ) ^ (m + i) = 13 ^ i * 13 ^ m := fun i => by ring
      have f31 : ∀ i : ℕ, (31 : ℤ) ^ (m + i) = 31 ^ i * 31 ^ m := fun i => by ring
      rw [f2, f11, f13, f31] at h1 h2 h3
      rw [f2, f11, f13, f31]
      linear_combination 169 * h3 - 6387 * h2 + 71671 * h1 - 195052 * h0

theorem gf :
    (1 - 4 * X) * (1 - 13 * X) * (1 - 31 * X) * (1 - 121 * X) *
        mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (X * (33 - 3178 * X + 57437 * X ^ 2 - 195052 * X ^ 3) : PowerSeries ℤ) := by
  set s : PowerSeries ℤ := mk (fun n => if n = 0 then 0 else (a n : ℤ)) with hs
  have hd : (1 - 4 * X) * (1 - 13 * X) * (1 - 31 * X) * (1 - 121 * X) * s =
      s - (s * C (169 : ℤ)) * X ^ 1 + (s * C (6387 : ℤ)) * X ^ 2 - (s * C (71671 : ℤ)) * X ^ 3 +
        (s * C (195052 : ℤ)) * X ^ 4 := by
    simp only [pow_one, map_ofNat]
    ring
  have hn : (X * (33 - 3178 * X + 57437 * X ^ 2 - 195052 * X ^ 3) : PowerSeries ℤ) =
      C (33 : ℤ) * X ^ 1 - C (3178 : ℤ) * X ^ 2 + C (57437 : ℤ) * X ^ 3 -
        C (195052 : ℤ) * X ^ 4 := by
    simp only [pow_one, map_ofNat]
    ring
  have a4 : a 4 = 29452071 := by
    have h := closed 4
    have e : (5 : ℤ) * 2 ^ (1 + 2 * 4) + 11 ^ (1 + 2 * 4) + 31 * 13 ^ 4 + 29 * 31 ^ 4 =
        81 * 29452071 := by norm_num
    rw [e] at h
    omega
  rw [hd, hn]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_mul_C, coeff_C, hs, coeff_mk]
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n) with h | h | h | h | h | h
  · subst h; simp
  · subst h; simp [a1]
  · subst h; simp [a1, a2]
  · subst h; simp [a1, a2, a3]
  · subst h; simp [a1, a2, a3, a4]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have key := a_rec (m + 1)
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
    simp
    rw [show m + 1 + 4 = m + 5 by ring, show m + 1 + 3 = m + 4 by ring,
      show m + 1 + 2 = m + 3 by ring] at key
    linarith

end A263908Proof

open A263908Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a263908.main :=
  ⟨gf, fun n _ => closed n⟩
