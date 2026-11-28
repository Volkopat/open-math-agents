import OMAStatements.S_oeis_a091915
import Mathlib

/-- Maximal product of a multiset of naturals with sum `n`. -/
def a091915_U : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | (n + 5) => 3 * a091915_U (n + 2)

theorem a091915_U0 : a091915_U 0 = 1 := by
  first
    | rfl
    | simp [a091915_U]

theorem a091915_U_step (n : ℕ) : a091915_U (n + 5) = 3 * a091915_U (n + 2) := by
  first
    | rfl
    | rw [a091915_U]
    | simp [a091915_U]

theorem a091915_U_step' (n k : ℕ) (hn : 2 ≤ n) (hk : k = n + 3) :
    a091915_U k = 3 * a091915_U n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  subst hk
  exact (congrArg a091915_U (by omega : j + 2 + 3 = j + 5)).trans (a091915_U_step j)

theorem a091915_scale (c k : ℕ)
    (h : ∀ m, m < 5 → c * a091915_U m ≤ a091915_U (m + k)) (m : ℕ) :
    c * a091915_U m ≤ a091915_U (m + k) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m < 5
    · exact h m hm
    · have e1 : a091915_U m = 3 * a091915_U (m - 3) :=
        a091915_U_step' (m - 3) m (by omega) (by omega)
      have e2 : a091915_U (m + k) = 3 * a091915_U (m - 3 + k) :=
        a091915_U_step' (m - 3 + k) (m + k) (by omega) (by omega)
      have h3 : c * a091915_U (m - 3) ≤ a091915_U (m - 3 + k) := ih (m - 3) (by omega)
      rw [e1, e2]
      calc c * (3 * a091915_U (m - 3)) = 3 * (c * a091915_U (m - 3)) := by ring
        _ ≤ 3 * a091915_U (m - 3 + k) := Nat.mul_le_mul_left 3 h3

theorem a091915_U1 (m : ℕ) : 1 * a091915_U m ≤ a091915_U (m + 1) :=
  a091915_scale 1 1 (by intro m hm; interval_cases m <;> (first | decide | simp [a091915_U])) m

theorem a091915_U2 (m : ℕ) : 2 * a091915_U m ≤ a091915_U (m + 2) :=
  a091915_scale 2 2 (by intro m hm; interval_cases m <;> (first | decide | simp [a091915_U])) m

theorem a091915_U3 (m : ℕ) : 3 * a091915_U m ≤ a091915_U (m + 3) :=
  a091915_scale 3 3 (by intro m hm; interval_cases m <;> (first | decide | simp [a091915_U])) m

theorem a091915_Umul (x : ℕ) : ∀ m : ℕ, x * a091915_U m ≤ a091915_U (m + x) := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro m
    by_cases hx : x < 4
    · rcases (show x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 by omega) with rfl | rfl | rfl | rfl
      · simp
      · exact a091915_U1 m
      · exact a091915_U2 m
      · exact a091915_U3 m
    · have h1 : (x - 2) * a091915_U m ≤ a091915_U (m + (x - 2)) := ih (x - 2) (by omega) m
      have h2 : 2 * a091915_U (m + (x - 2)) ≤ a091915_U (m + (x - 2) + 2) :=
        a091915_U2 (m + (x - 2))
      have e : m + (x - 2) + 2 = m + x := by omega
      rw [e] at h2
      have h3 : x * a091915_U m ≤ 2 * ((x - 2) * a091915_U m) := by
        calc x * a091915_U m ≤ (2 * (x - 2)) * a091915_U m :=
              Nat.mul_le_mul_right _ (by omega)
          _ = 2 * ((x - 2) * a091915_U m) := Nat.mul_assoc _ _ _
      exact h3.trans ((Nat.mul_le_mul_left 2 h1).trans h2)

theorem a091915_Uhalf (j m : ℕ) : (j + 1) * a091915_U m ≤ a091915_U (m + 2 * j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h2 : 2 * a091915_U (m + 2 * j) ≤ a091915_U (m + 2 * j + 2) :=
      a091915_U2 (m + 2 * j)
    have e : m + 2 * j + 2 = m + 2 * (j + 1) := by omega
    rw [e] at h2
    have h3 : (j + 1 + 1) * a091915_U m ≤ 2 * ((j + 1) * a091915_U m) := by
      calc (j + 1 + 1) * a091915_U m ≤ (2 * (j + 1)) * a091915_U m :=
            Nat.mul_le_mul_right _ (by omega)
        _ = 2 * ((j + 1) * a091915_U m) := Nat.mul_assoc _ _ _
    exact h3.trans ((Nat.mul_le_mul_left 2 ih).trans h2)

theorem a091915_Ubound (s : Multiset ℕ) : s.prod ≤ a091915_U s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp [a091915_U0]
  | cons x t ih =>
    rw [Multiset.prod_cons, Multiset.sum_cons]
    calc x * t.prod ≤ x * a091915_U t.sum := Nat.mul_le_mul_left x ih
      _ ≤ a091915_U (t.sum + x) := a091915_Umul x t.sum
      _ = a091915_U (x + t.sum) := congrArg a091915_U (Nat.add_comm t.sum x)

theorem a091915_Ebound (s : Multiset ℕ) : (∀ i ∈ s, 0 < i) → Even s.prod →
    ∃ k, s.sum = k + 2 ∧ s.prod ≤ 2 * a091915_U k := by
  induction s using Multiset.induction_on with
  | empty =>
    intro _ hev
    simp at hev
  | cons x t ih =>
    intro hpos hev
    rw [Multiset.prod_cons] at hev
    rw [Multiset.sum_cons, Multiset.prod_cons]
    have hx : 0 < x := hpos x (Multiset.mem_cons.mpr (Or.inl rfl))
    have ht : ∀ i ∈ t, 0 < i := fun i hi => hpos i (Multiset.mem_cons.mpr (Or.inr hi))
    rcases Nat.even_mul.mp hev with hxe | hte
    · obtain ⟨j, hj⟩ := hxe
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      subst hj
      refine ⟨t.sum + 2 * i, by omega, ?_⟩
      calc (i + 1 + (i + 1)) * t.prod = 2 * ((i + 1) * t.prod) := by ring
        _ ≤ 2 * ((i + 1) * a091915_U t.sum) :=
            Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left (i + 1) (a091915_Ubound t))
        _ ≤ 2 * a091915_U (t.sum + 2 * i) := Nat.mul_le_mul_left 2 (a091915_Uhalf i t.sum)
    · obtain ⟨k, hk, hle⟩ := ih ht hte
      refine ⟨k + x, by omega, ?_⟩
      calc x * t.prod ≤ x * (2 * a091915_U k) := Nat.mul_le_mul_left x hle
        _ = 2 * (x * a091915_U k) := by ring
        _ ≤ 2 * a091915_U (k + x) := Nat.mul_le_mul_left 2 (a091915_Umul x k)

theorem a091915_mem_le (n : ℕ) (q : Nat.Partition n) (h : Even q.parts.prod) :
    q.parts.prod ≤ OMA.S_oeis_a091915.a n := by
  unfold OMA.S_oeis_a091915.a
  exact Finset.le_sup (f := fun p : Nat.Partition n => p.parts.prod)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ q, h⟩)

theorem a091915_le_of_forall (n B : ℕ)
    (h : ∀ p : Nat.Partition n, Even p.parts.prod → p.parts.prod ≤ B) :
    OMA.S_oeis_a091915.a n ≤ B := by
  unfold OMA.S_oeis_a091915.a
  exact Finset.sup_le (fun p hp => h p (Finset.mem_filter.mp hp).2)

theorem a091915_le_of_multiset (n : ℕ) (s : Multiset ℕ) (hpos : ∀ i ∈ s, 0 < i)
    (hsum : s.sum = n) (hev : Even s.prod) : s.prod ≤ OMA.S_oeis_a091915.a n :=
  a091915_mem_le n ⟨s, fun {i} hi => hpos i hi, hsum⟩ hev

theorem a091915_upper (n k : ℕ) (h : n = k + 2) :
    OMA.S_oeis_a091915.a n ≤ 2 * a091915_U k := by
  apply a091915_le_of_forall
  intro p hp
  obtain ⟨k', hk', hle⟩ := a091915_Ebound p.parts (fun i hi => p.parts_pos hi) hp
  rw [p.parts_sum] at hk'
  have e : k' = k := by omega
  rw [e] at hle
  exact hle

theorem a091915_cons (n x N : ℕ) (hx : 0 < x) (hN : N = n + x) :
    x * OMA.S_oeis_a091915.a n ≤ OMA.S_oeis_a091915.a N := by
  subst hN
  have h : OMA.S_oeis_a091915.a n ≤ OMA.S_oeis_a091915.a (n + x) / x := by
    apply a091915_le_of_forall
    intro p hp
    have h1 := a091915_le_of_multiset (n + x) (x ::ₘ p.parts)
      (fun i hi => by
        rcases Multiset.mem_cons.mp hi with h | h
        · omega
        · exact p.parts_pos h)
      (by rw [Multiset.sum_cons, p.parts_sum]; omega)
      (by rw [Multiset.prod_cons]; exact Nat.even_mul.mpr (Or.inr hp))
    rw [Multiset.prod_cons] at h1
    exact (Nat.le_div_iff_mul_le hx).mpr ((Nat.mul_comm p.parts.prod x).le.trans h1)
  calc x * OMA.S_oeis_a091915.a n
      ≤ x * (OMA.S_oeis_a091915.a (n + x) / x) := Nat.mul_le_mul_left x h
    _ ≤ OMA.S_oeis_a091915.a (n + x) := Nat.mul_div_le _ _

theorem a091915_base : 2 ≤ OMA.S_oeis_a091915.a 2 := by
  have h := a091915_le_of_multiset 2 {2} (by simp) (by simp) (by simp)
  simpa using h

theorem a091915_lower (k : ℕ) : ∀ N, 2 ≤ k → N = k + 2 →
    2 * a091915_U k ≤ OMA.S_oeis_a091915.a N := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro N hk hN
    subst hN
    by_cases h5 : k < 5
    · have hU : a091915_U k = k := by
        rcases (show k = 2 ∨ k = 3 ∨ k = 4 by omega) with rfl | rfl | rfl <;>
          (first | rfl | decide | simp [a091915_U])
      rw [hU]
      calc 2 * k = k * 2 := Nat.mul_comm 2 k
        _ ≤ k * OMA.S_oeis_a091915.a 2 := Nat.mul_le_mul_left k a091915_base
        _ ≤ OMA.S_oeis_a091915.a (k + 2) := a091915_cons 2 k (k + 2) (by omega) (by omega)
    · have h1 : 2 * a091915_U (k - 3) ≤ OMA.S_oeis_a091915.a (k - 3 + 2) :=
        ih (k - 3) (by omega) (k - 3 + 2) (by omega) rfl
      have e : a091915_U k = 3 * a091915_U (k - 3) :=
        a091915_U_step' (k - 3) k (by omega) (by omega)
      rw [e]
      calc 2 * (3 * a091915_U (k - 3)) = 3 * (2 * a091915_U (k - 3)) := by ring
        _ ≤ 3 * OMA.S_oeis_a091915.a (k - 3 + 2) := Nat.mul_le_mul_left 3 h1
        _ ≤ OMA.S_oeis_a091915.a (k + 2) :=
            a091915_cons (k - 3 + 2) 3 (k + 2) (by omega) (by omega)

theorem OMA.solution : type_of% @OMA.S_oeis_a091915.main := by
  intro n hn
  have hu : OMA.S_oeis_a091915.a (n + 3) ≤ 2 * a091915_U (n + 1) :=
    a091915_upper (n + 3) (n + 1) (by omega)
  have hl : 2 * a091915_U (n - 2) ≤ OMA.S_oeis_a091915.a n :=
    a091915_lower (n - 2) n (by omega) (by omega)
  have e : a091915_U (n + 1) = 3 * a091915_U (n - 2) :=
    a091915_U_step' (n - 2) (n + 1) (by omega) (by omega)
  have hc : 3 * OMA.S_oeis_a091915.a n ≤ OMA.S_oeis_a091915.a (n + 3) :=
    a091915_cons n 3 (n + 3) (by omega) rfl
  omega
