import OMAStatements.S_oeis_a000907

namespace OMA.S_oeis_a000907

open Finset Multiset
open scoped Nat

private def oneFour (n : ℕ) : Multiset ℕ := 4 ::ₘ Multiset.replicate n 2

private def twoThrees (n : ℕ) : Multiset ℕ := 3 ::ₘ 3 ::ₘ Multiset.replicate (n - 1) 2

private noncomputable def cycleCount (n : ℕ) (s : Multiset ℕ) : ℕ := by
  classical
  exact ((univ : Finset (Equiv.Perm (Fin (2 * n + 4)))).filter (fun g => g.cycleType = s)).card

private theorem sum_bound (s : Multiset ℕ) (h : ∀ x ∈ s, 2 ≤ x) :
    2 * s.card ≤ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    have hx := h x (by simp)
    have hs := ih (fun y hy => h y (by simp [hy]))
    simp only [Multiset.card_cons, Multiset.sum_cons]
    omega

private theorem sum_minimal (s : Multiset ℕ) (h : ∀ x ∈ s, 2 ≤ x)
    (hs : s.sum = 2 * s.card) : s = Multiset.replicate s.card 2 := by
  apply Multiset.eq_replicate_card.mpr
  intro x hx
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hx
  have ht := sum_bound t (fun y hy => h y (by simp [hy]))
  have hx2 := h x (by simp)
  simp only [Multiset.sum_cons, Multiset.card_cons] at hs
  omega

private theorem exists_large (s : Multiset ℕ) (h : ∀ x ∈ s, 2 ≤ x)
    (hs : 2 * s.card < s.sum) : ∃ x ∈ s, 2 < x := by
  by_contra! hb
  have he : s = Multiset.replicate s.card 2 :=
    Multiset.eq_replicate_card.mpr (fun x hx => le_antisymm (hb x hx) (h x hx))
  have hsum := congrArg Multiset.sum he
  simp at hsum
  omega

private theorem cycle_shapes (n : ℕ) (s : Multiset ℕ) (h : ∀ x ∈ s, 2 ≤ x)
    (hc : s.card = n + 1) (hs : s.sum = 2 * n + 4) :
    s = oneFour n ∨ s = twoThrees n := by
  obtain ⟨x, hx, hx2⟩ := exists_large s h (by omega)
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hx
  have ht (y : ℕ) (hy : y ∈ t) : 2 ≤ y := h y (by simp [hy])
  have hb := sum_bound t ht
  simp only [Multiset.card_cons, Multiset.sum_cons] at hc hs
  have hx34 : x = 3 ∨ x = 4 := by omega
  rcases hx34 with rfl | rfl
  · obtain ⟨y, hy, hy2⟩ := exists_large t ht (by omega)
    obtain ⟨u, rfl⟩ := Multiset.exists_cons_of_mem hy
    have hu (z : ℕ) (hz : z ∈ u) : 2 ≤ z := ht z (by simp [hz])
    have hub := sum_bound u hu
    simp only [Multiset.card_cons, Multiset.sum_cons] at hc hs
    have hy3 : y = 3 := by omega
    subst y
    have he := sum_minimal u hu (by omega)
    right
    unfold twoThrees
    rw [he, show u.card = n - 1 by omega]
  · have he := sum_minimal t ht (by omega)
    left
    unfold oneFour
    rw [he, show t.card = n by omega]

private theorem fixed_iff {n : ℕ} (g : Equiv.Perm (Fin n)) :
    (∀ x : Fin n, g x ≠ x) ↔ g.cycleType.sum = n := by
  rw [Equiv.Perm.sum_cycleType]
  constructor
  · intro h
    have hs : g.support = univ := by
      ext x
      exact iff_of_true (Equiv.Perm.mem_support.mpr (h x)) (mem_univ x)
    simp [hs]
  · intro h x
    have hs : g.support = univ := eq_univ_of_card g.support (by simpa using h)
    apply Equiv.Perm.mem_support.mp
    simp [hs]

private theorem split_count (n : ℕ) :
    a n = (cycleCount n (oneFour n) : ℤ) + cycleCount n (twoThrees n) := by
  classical
  let s : Finset (Equiv.Perm (Fin (2 * n + 4))) :=
    univ.filter (fun g => (∀ x, g x ≠ x) ∧ g.cycleType.card = n + 1)
  let s₄ : Finset (Equiv.Perm (Fin (2 * n + 4))) :=
    univ.filter (fun g => g.cycleType = oneFour n)
  let s₃ : Finset (Equiv.Perm (Fin (2 * n + 4))) :=
    univ.filter (fun g => g.cycleType = twoThrees n)
  have hcard : (assocStirling (2 * n + 4) (n + 1)) = s.card := by
    unfold assocStirling
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_of_subtype s (by intro g; simp [s])
  have hs : s = s₄ ∪ s₃ := by
    ext g
    simp only [s, s₄, s₃, Finset.mem_filter, mem_univ, true_and, Finset.mem_union, fixed_iff]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact cycle_shapes n _ (fun _ hx => Equiv.Perm.two_le_of_mem_cycleType hx) h₂ h₁
    · rintro (h₄ | h₃)
      · rw [h₄]
        simp [oneFour, Nat.mul_comm, Nat.add_comm]
      · rw [h₃]
        cases n with
        | zero =>
          have hbad := g.sum_cycleType_le
          norm_num [h₃, twoThrees] at hbad
        | succ k =>
          simp [twoThrees, Nat.mul_comm]
          omega
  have hdisj : Disjoint s₄ s₃ := by
    apply Finset.disjoint_left.mpr
    intro g hg₄ hg₃
    have h₄ := (Finset.mem_filter.mp hg₄).2
    have h₃ := (Finset.mem_filter.mp hg₃).2
    have he := congrArg (Multiset.count 4) (h₄.symm.trans h₃)
    norm_num [oneFour, twoThrees, Multiset.count_replicate] at he
  unfold a
  rw [hcard, hs, card_union_of_disjoint hdisj, Nat.cast_add]
  rfl

private theorem weight_four (n : ℕ) :
    (∏ j ∈ (oneFour n).toFinset, ((oneFour n).count j)!) = n.factorial := by
  cases n with
  | zero => simp [oneFour]
  | succ n =>
    have hf : (oneFour (n + 1)).toFinset = ({4, 2} : Finset ℕ) := by
      ext j
      simp only [oneFour, Multiset.mem_toFinset, Multiset.mem_cons, Multiset.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [hf]
    norm_num [oneFour, Multiset.count_replicate]

private theorem weight_threes (n : ℕ) :
    (∏ j ∈ (twoThrees (n + 1)).toFinset, ((twoThrees (n + 1)).count j)!) = 2 * n.factorial := by
  cases n with
  | zero => norm_num [twoThrees]
  | succ n =>
    have hf : (twoThrees (n + 1 + 1)).toFinset = ({3, 2} : Finset ℕ) := by
      ext j
      simp only [twoThrees, Multiset.mem_toFinset, Multiset.mem_cons, Multiset.mem_replicate, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [hf]
    norm_num [twoThrees, Multiset.count_replicate]

private theorem count_four (n : ℕ) :
    cycleCount n (oneFour n) * (4 * 2 ^ n * n.factorial) = (2 * n + 4)! := by
  have h := Equiv.Perm.card_of_cycleType_mul_eq (Fin (2 * n + 4)) (oneFour n)
  have hsum : (oneFour n).sum = 2 * n + 4 := by
    simp [oneFour, Nat.mul_comm, Nat.add_comm]
  have hmem : ∀ j ∈ oneFour n, 2 ≤ j := by
    intro j hj
    simp [oneFour, Multiset.mem_replicate] at hj
    omega
  rw [Fintype.card_fin, hsum, Nat.sub_self, Nat.factorial_zero, one_mul, weight_four,
    if_pos ⟨le_rfl, hmem⟩] at h
  have hm : (oneFour n).prod = 4 * 2 ^ n := by simp [oneFour]
  rwa [hm] at h

private theorem count_threes (n : ℕ) :
    cycleCount (n + 1) (twoThrees (n + 1)) * (18 * 2 ^ n * n.factorial) = (2 * (n + 1) + 4)! := by
  have h := Equiv.Perm.card_of_cycleType_mul_eq (Fin (2 * (n + 1) + 4)) (twoThrees (n + 1))
  have hsum : (twoThrees (n + 1)).sum = 2 * (n + 1) + 4 := by
    simp [twoThrees, Nat.mul_comm]
    omega
  have hmem : ∀ j ∈ twoThrees (n + 1), 2 ≤ j := by
    intro j hj
    simp [twoThrees, Multiset.mem_replicate] at hj
    omega
  rw [Fintype.card_fin, hsum, Nat.sub_self, Nat.factorial_zero, one_mul, weight_threes,
    if_pos ⟨le_rfl, hmem⟩] at h
  have hm : (twoThrees (n + 1)).prod * (2 * n.factorial) = 18 * 2 ^ n * n.factorial := by
    simp [twoThrees]
    ring
  rwa [hm] at h

private theorem count_threes_zero : cycleCount 0 (twoThrees 0) = 0 := by
  apply (Equiv.Perm.card_of_cycleType_eq_zero_iff (Fin (2 * 0 + 4))).mpr
  norm_num [twoThrees]

private theorem cross_formula (n : ℕ) :
    a n * (36 * 2 ^ n * (n.factorial : ℤ)) = (4 * (n : ℤ) + 9) * ((2 * n + 4)! : ℤ) := by
  rw [split_count]
  have h4 : (cycleCount n (oneFour n) : ℤ) * (4 * 2 ^ n * (n.factorial : ℤ)) =
      ((2 * n + 4)! : ℤ) := by exact_mod_cast count_four n
  cases n with
  | zero =>
    rw [count_threes_zero]
    norm_num at h4 ⊢
    omega
  | succ n =>
    have h3 : (cycleCount (n + 1) (twoThrees (n + 1)) : ℤ) * (18 * 2 ^ n * (n.factorial : ℤ)) =
        ((2 * (n + 1) + 4)! : ℤ) := by exact_mod_cast count_threes n
    rw [Nat.factorial_succ n, pow_succ (2 : ℤ) n] at h4 ⊢
    push_cast at h4 ⊢
    linear_combination 9 * h4 + (4 * ((n : ℤ) + 1)) * h3

end OMA.S_oeis_a000907

open scoped Nat in
open OMA.S_oeis_a000907 in
theorem OMA.solution : type_of% @OMA.S_oeis_a000907.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
  have h0 := cross_formula (k + 1)
  have h1 := cross_formula k
  have hf : (2 * (k + 1) + 4)! = (2 * k + 6) * (2 * k + 5) * (2 * k + 4)! := by
    rw [show 2 * (k + 1) + 4 = (2 * k + 4) + 1 + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ, mul_assoc]
  rw [hf, Nat.factorial_succ k, pow_succ (2 : ℤ) k] at h0
  push_cast at h0 ⊢
  have h : (72 * (2 : ℤ) ^ k * (k.factorial : ℤ)) *
      (((k : ℤ) + 1) * (4 * ((k : ℤ) + 1) + 5) * a (k + 1) -
        (2 * ((k : ℤ) + 1) + 3) * ((k : ℤ) + 1 + 2) *
          (4 * ((k : ℤ) + 1) + 9) * a k) = 0 := by
    linear_combination (4 * (k : ℤ) + 9) * h0 -
       2 * (2 * (k : ℤ) + 5) * ((k : ℤ) + 3) * (4 * (k : ℤ) + 13) * h1
  exact (mul_eq_zero.mp h).resolve_left (by positivity)
