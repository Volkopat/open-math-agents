import OMAStatements.S_oeis_a249265
import Mathlib

namespace OMA.A249265Proof

open OMA.S_oeis_a249265

/-! ## Unfolding the greedy definition -/

theorem a_succ (n : ℕ) : a (n + 1) = nextTerm (firstTerms n) := rfl

theorem ft_succ (n : ℕ) : firstTerms (n + 1) = firstTerms n ++ [a (n + 1)] := rfl

theorem ft_length (n : ℕ) : (firstTerms n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ft_succ, List.length_append, ih, List.length_singleton]

/-- `nextTerm l` is pinned by a witness `x0` and minimality below it. -/
theorem nextTerm_eq (l : List ℕ) (x0 : ℕ) (hmem : x0 ∉ l)
    (hsum : ∃ k : ℕ, l.sum + x0 = (l.length + 1) * Nat.fib k)
    (hmin : ∀ x < x0, x ∉ l → ∀ k : ℕ, l.sum + x ≠ (l.length + 1) * Nat.fib k) :
    nextTerm l = x0 := by
  have hne : ({x : ℕ | x ∉ l ∧ ∃ k : ℕ, l.sum + x = (l.length + 1) * Nat.fib k}).Nonempty :=
    ⟨x0, hmem, hsum⟩
  show sInf {x : ℕ | x ∉ l ∧ ∃ k : ℕ, l.sum + x = (l.length + 1) * Nat.fib k} = x0
  apply le_antisymm
  · exact Nat.sInf_le ⟨hmem, hsum⟩
  · by_contra h
    obtain ⟨h1, k, hk⟩ := Nat.sInf_mem hne
    exact hmin _ (Nat.gt_of_not_le h) h1 k hk

/-- Minimality only needs the `k` with `F(k) < F(k0)`, hence `k < k0`. -/
theorem nextTerm_eq_dec (l : List ℕ) (x0 k0 : ℕ) (hmem : x0 ∉ l)
    (hsum : l.sum + x0 = (l.length + 1) * Nat.fib k0)
    (hmin : ∀ x < x0, ∀ k < k0, x ∉ l → l.sum + x ≠ (l.length + 1) * Nat.fib k) :
    nextTerm l = x0 := by
  refine nextTerm_eq l x0 hmem ⟨k0, hsum⟩ ?_
  intro x hx hxl k hk
  have hkk : k < k0 := by
    by_contra hc
    have h1 := Nat.mul_le_mul_left (l.length + 1) (Nat.fib_mono (Nat.le_of_not_lt hc))
    omega
  exact hmin x hx k hkk hxl hk

theorem a_eq_of (n : ℕ) (l : List ℕ) (x0 k0 : ℕ) (h : firstTerms n = l) (hmem : x0 ∉ l)
    (hsum : l.sum + x0 = (l.length + 1) * Nat.fib k0)
    (hmin : ∀ x < x0, ∀ k < k0, x ∉ l → l.sum + x ≠ (l.length + 1) * Nat.fib k) :
    a (n + 1) = x0 := by
  rw [a_succ, h]
  exact nextTerm_eq_dec l x0 k0 hmem hsum hmin

theorem ft_step (n : ℕ) (l : List ℕ) (x0 : ℕ) (h : firstTerms n = l) (hx : a (n + 1) = x0) :
    firstTerms (n + 1) = l ++ [x0] := by
  rw [ft_succ, h, hx]

/-! ## The first nine terms -/

theorem base_chain : firstTerms 9 = [0, 2, 1, 5, 7, 3, 17, 29, 8] ∧ a 4 = 5 ∧ a 5 = 7 ∧
    a 8 = 29 ∧ a 9 = 8 := by
  have h0 : firstTerms 0 = [] := rfl
  have a1 : a 1 = 0 := a_eq_of 0 [] 0 0 h0 (by decide) (by decide) (by decide)
  have h1 : firstTerms 1 = [0] := ft_step 0 [] 0 h0 a1
  have a2 : a 2 = 2 := a_eq_of 1 [0] 2 1 h1 (by decide) (by decide) (by decide)
  have h2 : firstTerms 2 = [0, 2] := ft_step 1 [0] 2 h1 a2
  have a3 : a 3 = 1 := a_eq_of 2 [0, 2] 1 1 h2 (by decide) (by decide) (by decide)
  have h3 : firstTerms 3 = [0, 2, 1] := ft_step 2 [0, 2] 1 h2 a3
  have a4 : a 4 = 5 := a_eq_of 3 [0, 2, 1] 5 3 h3 (by decide) (by decide) (by decide)
  have h4 : firstTerms 4 = [0, 2, 1, 5] := ft_step 3 [0, 2, 1] 5 h3 a4
  have a5 : a 5 = 7 := a_eq_of 4 [0, 2, 1, 5] 7 4 h4 (by decide) (by decide) (by decide)
  have h5 : firstTerms 5 = [0, 2, 1, 5, 7] := ft_step 4 [0, 2, 1, 5] 7 h4 a5
  have a6 : a 6 = 3 := a_eq_of 5 [0, 2, 1, 5, 7] 3 4 h5 (by decide) (by decide) (by decide)
  have h6 : firstTerms 6 = [0, 2, 1, 5, 7, 3] := ft_step 5 [0, 2, 1, 5, 7] 3 h5 a6
  have a7 : a 7 = 17 := a_eq_of 6 [0, 2, 1, 5, 7, 3] 17 5 h6 (by decide) (by decide) (by decide)
  have h7 : firstTerms 7 = [0, 2, 1, 5, 7, 3, 17] := ft_step 6 [0, 2, 1, 5, 7, 3] 17 h6 a7
  have a8 : a 8 = 29 :=
    a_eq_of 7 [0, 2, 1, 5, 7, 3, 17] 29 6 h7 (by decide) (by decide) (by decide)
  have h8 : firstTerms 8 = [0, 2, 1, 5, 7, 3, 17, 29] :=
    ft_step 7 [0, 2, 1, 5, 7, 3, 17] 29 h7 a8
  have a9 : a 9 = 8 :=
    a_eq_of 8 [0, 2, 1, 5, 7, 3, 17, 29] 8 6 h8 (by decide) (by decide) (by decide)
  have h9 : firstTerms 9 = [0, 2, 1, 5, 7, 3, 17, 29, 8] :=
    ft_step 8 [0, 2, 1, 5, 7, 3, 17, 29] 8 h8 a9
  exact ⟨h9, a4, a5, a8, a9⟩

/-! ## Fibonacci facts -/

theorem fib_succ_le_two_mul (m : ℕ) (hm : 1 ≤ m) : Nat.fib (m + 1) ≤ 2 * Nat.fib m := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have h1 : Nat.fib (j + 2) = Nat.fib j + Nat.fib (j + 1) := Nat.fib_add_two
  have h2 : Nat.fib j ≤ Nat.fib (j + 1) := Nat.fib_le_fib_succ
  show Nat.fib (j + 2) ≤ 2 * Nat.fib (j + 1)
  omega

theorem two_mul_lt_fib (j : ℕ) (hj : 6 ≤ j) : 2 * j < Nat.fib (j + 1) := by
  induction j, hj using Nat.le_induction with
  | base => decide
  | succ j hj ih =>
    have h1 : Nat.fib (j + 1 + 1) = Nat.fib j + Nat.fib (j + 1) := Nat.fib_add_two
    have h2 : Nat.fib 3 ≤ Nat.fib j := Nat.fib_mono (by omega)
    have h3 : Nat.fib 3 = 2 := by decide
    omega

theorem not_fib_of (v N : ℕ) (hN : v < Nat.fib N) (h : ∀ s < N, Nat.fib s ≠ v) :
    ∀ s, Nat.fib s ≠ v := by
  intro s
  rcases Nat.lt_or_ge s N with hs | hs
  · exact h s hs
  · have := Nat.fib_mono hs
    omega

/-- `E(j) = F(j+1) + 2 j F(j)` is never a Fibonacci number for `j ≥ 5`. -/
theorem not_fib_E (j : ℕ) (hj : 5 ≤ j) :
    ∀ s, Nat.fib s ≠ Nat.fib (j + 1) + 2 * j * Nat.fib j := by
  rcases (show j = 5 ∨ 6 ≤ j by omega) with rfl | hj6
  · have h58 : Nat.fib (5 + 1) + 2 * 5 * Nat.fib 5 = 58 := by decide
    rw [h58]
    exact not_fib_of 58 11 (by decide) (by decide)
  · intro s hs
    have hD := two_mul_lt_fib j hj6
    have hFj : 0 < Nat.fib j := Nat.fib_pos.mpr (by omega)
    rcases (show s ≤ j + 2 ∨ j + 3 ≤ s by omega) with hs1 | hs1
    · have h1 : Nat.fib s ≤ Nat.fib (j + 2) := Nat.fib_mono hs1
      have h2 : Nat.fib (j + 2) = Nat.fib j + Nat.fib (j + 1) := Nat.fib_add_two
      have h3 : 6 * Nat.fib j ≤ j * Nat.fib j := Nat.mul_le_mul_right _ hj6
      linarith
    · obtain ⟨t, rfl⟩ : ∃ t, s = j + t + 1 := ⟨s - j - 1, by omega⟩
      rw [Nat.fib_add j t] at hs
      have h3 : Nat.fib 3 ≤ Nat.fib (t + 1) := Nat.fib_mono (by omega)
      have h3' : Nat.fib 3 = 2 := by decide
      obtain ⟨u, hu⟩ : ∃ u, Nat.fib (t + 1) = u + 1 := ⟨Nat.fib (t + 1) - 1, by omega⟩
      rw [hu, mul_add, mul_one] at hs
      have hs' : Nat.fib j * Nat.fib t + Nat.fib (j + 1) * u = 2 * j * Nat.fib j := by omega
      have hdvd : Nat.fib j ∣ Nat.fib (j + 1) * u := by
        have h4 : Nat.fib j ∣ Nat.fib j * Nat.fib t + Nat.fib (j + 1) * u := by
          rw [hs']
          exact dvd_mul_left _ _
        exact (Nat.dvd_add_right (dvd_mul_right _ _)).mp h4
      have hdvd2 : Nat.fib j ∣ u := (Nat.fib_coprime_fib_succ j).dvd_of_dvd_mul_left hdvd
      have hle : Nat.fib j ≤ u := Nat.le_of_dvd (by omega) hdvd2
      have h5 : Nat.fib (j + 1) * Nat.fib j ≤ Nat.fib (j + 1) * u := Nat.mul_le_mul_left _ hle
      have h6 : (2 * j + 1) * Nat.fib j ≤ Nat.fib (j + 1) * Nat.fib j :=
        Nat.mul_le_mul_right _ (by omega)
      have h7 := Nat.zero_le (Nat.fib j * Nat.fib t)
      linarith

/-! ## The invariant after `2m + 1` terms, for `m ≥ 4` -/

/-- After `2m + 1` terms: the sum is `(2m+1) F(m+2)`, `F(m+2)` is used, every term is below
`E(m+1) = F(m+2) + 2(m+1) F(m+1)`, every Fibonacci term is at most `F(m+2)`, and
`a(2m) = E(m)`, `a(2m+1) = F(m+2)`. -/
def InvA (m : ℕ) : Prop :=
  (firstTerms (2 * m + 1)).sum = (2 * m + 1) * Nat.fib (m + 2) ∧
  Nat.fib (m + 2) ∈ firstTerms (2 * m + 1) ∧
  (∀ x ∈ firstTerms (2 * m + 1), x < Nat.fib (m + 2) + 2 * (m + 1) * Nat.fib (m + 1)) ∧
  (∀ x ∈ firstTerms (2 * m + 1), x ≤ Nat.fib (m + 2) ∨ ∀ s, Nat.fib s ≠ x) ∧
  a (2 * m) = Nat.fib (m + 1) + 2 * m * Nat.fib m ∧
  a (2 * m + 1) = Nat.fib (m + 2)

theorem inv_base : InvA 4 := by
  obtain ⟨h9, -, -, a8, a9⟩ := base_chain
  have e1 : (firstTerms 9).sum = 9 * Nat.fib 6 := by rw [h9]; decide
  have e2 : Nat.fib 6 ∈ firstTerms 9 := by rw [h9]; decide
  have e3 : ∀ x ∈ firstTerms 9, x < Nat.fib 6 + 2 * 5 * Nat.fib 5 := by rw [h9]; decide
  have e4 : ∀ x ∈ firstTerms 9, x ≤ Nat.fib 6 ∨ ∀ s, Nat.fib s ≠ x := by
    rw [h9]
    have key : ∀ y ∈ ([0, 2, 1, 5, 7, 3, 17, 29, 8] : List ℕ),
        y ≤ Nat.fib 6 ∨ y = 7 ∨ y = 17 ∨ y = 29 := by decide
    intro x hx
    rcases key x hx with h | rfl | rfl | rfl
    · exact Or.inl h
    · exact Or.inr (not_fib_of 7 6 (by decide) (by decide))
    · exact Or.inr (not_fib_of 17 8 (by decide) (by decide))
    · exact Or.inr (not_fib_of 29 9 (by decide) (by decide))
  have e5 : a 8 = Nat.fib 5 + 2 * 4 * Nat.fib 4 := by rw [a8]; decide
  have e6 : a 9 = Nat.fib 6 := by rw [a9]; decide
  exact ⟨e1, e2, e3, e4, e5, e6⟩

theorem inv_step (m : ℕ) (hm : 4 ≤ m) (h : InvA m) : InvA (m + 1) := by
  obtain ⟨hsum, hmemF, hlt, hfib, -, -⟩ := h
  have hlen : (firstTerms (2 * m + 1)).length = 2 * m + 1 := ft_length _
  have hF0 : 0 < Nat.fib m := Nat.fib_pos.mpr (by omega)
  have hF1 : 0 < Nat.fib (m + 1) := Nat.fib_pos.mpr (by omega)
  have hF2pos : 0 < Nat.fib (m + 2) := Nat.fib_pos.mpr (by omega)
  have hF2 : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
  have hF3 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
  have hle1 : Nat.fib (m + 1) ≤ 2 * Nat.fib m := fib_succ_le_two_mul m (by omega)
  have hle2 : Nat.fib (m + 2) ≤ 2 * Nat.fib (m + 1) := fib_succ_le_two_mul (m + 1) (by omega)
  have hm0 : 4 * Nat.fib m ≤ m * Nat.fib m := Nat.mul_le_mul_right _ hm
  have hm1 : 4 * Nat.fib (m + 1) ≤ m * Nat.fib (m + 1) := Nat.mul_le_mul_right _ hm
  -- step 2m+2: the term is E(m+1)
  have hE : a (2 * m + 2) = Nat.fib (m + 2) + 2 * (m + 1) * Nat.fib (m + 1) := by
    rw [show 2 * m + 2 = 2 * m + 1 + 1 from rfl, a_succ]
    refine nextTerm_eq _ _ (fun hx => lt_irrefl _ (hlt _ hx)) ⟨m + 3, ?_⟩ ?_
    · rw [hsum, hlen, hF3]
      ring
    · intro x hx hxl k hk
      rw [hsum, hlen] at hk
      rcases (show k ≤ m + 1 ∨ k = m + 2 ∨ m + 3 ≤ k by omega) with hk1 | rfl | hk3
      · have h2 := Nat.mul_le_mul_left (2 * m + 1 + 1) (Nat.fib_mono hk1)
        rw [hF2] at hk
        linarith
      · apply hxl
        have hx2 : x = Nat.fib (m + 2) := by linarith
        rw [hx2]
        exact hmemF
      · have h2 := Nat.mul_le_mul_left (2 * m + 1 + 1) (Nat.fib_mono hk3)
        rw [hF3] at h2
        linarith
  have hpre2 : firstTerms (2 * m + 2) =
      firstTerms (2 * m + 1) ++ [Nat.fib (m + 2) + 2 * (m + 1) * Nat.fib (m + 1)] := by
    rw [← hE]
    exact ft_succ (2 * m + 1)
  have hsum2 : (firstTerms (2 * m + 2)).sum = (2 * m + 2) * Nat.fib (m + 3) := by
    rw [hpre2, List.sum_append, hsum, List.sum_singleton, hF3]
    ring
  have hlen2 : (firstTerms (2 * m + 2)).length = 2 * m + 2 := ft_length _
  have hnot : Nat.fib (m + 3) ∉ firstTerms (2 * m + 2) := by
    rw [hpre2, List.mem_append, List.mem_singleton]
    rintro (hx | hx)
    · rcases hfib _ hx with h1 | h1
      · have h2 : Nat.fib (m + 2) < Nat.fib (m + 3) := Nat.fib_lt_fib_succ (by omega)
        omega
      · exact h1 (m + 3) rfl
    · exact not_fib_E (m + 1) (by omega) (m + 3) hx
  -- step 2m+3: the term is F(m+3)
  have hO : a (2 * m + 3) = Nat.fib (m + 3) := by
    rw [show 2 * m + 3 = 2 * m + 2 + 1 from rfl, a_succ]
    refine nextTerm_eq _ _ hnot ⟨m + 3, ?_⟩ ?_
    · rw [hsum2, hlen2]
      ring
    · intro x hx hxl k hk
      rw [hsum2, hlen2] at hk
      rcases (show k ≤ m + 2 ∨ m + 3 ≤ k by omega) with hk1 | hk3
      · have h2 := Nat.mul_le_mul_left (2 * m + 2 + 1) (Nat.fib_mono hk1)
        rw [hF3] at hk
        linarith
      · have h2 := Nat.mul_le_mul_left (2 * m + 2 + 1) (Nat.fib_mono hk3)
        linarith
  have hpre3 : firstTerms (2 * m + 3) = firstTerms (2 * m + 2) ++ [Nat.fib (m + 3)] := by
    rw [← hO]
    exact ft_succ (2 * m + 2)
  have hsum3 : (firstTerms (2 * m + 3)).sum = (2 * m + 3) * Nat.fib (m + 3) := by
    rw [hpre3, List.sum_append, hsum2, List.sum_singleton]
    ring
  have hmem3 : Nat.fib (m + 3) ∈ firstTerms (2 * m + 3) := by
    rw [hpre3, List.mem_append, List.mem_singleton]
    exact Or.inr rfl
  have hmono : (m + 1) * Nat.fib (m + 1) ≤ (m + 2) * Nat.fib (m + 2) :=
    Nat.mul_le_mul (by omega) Nat.fib_le_fib_succ
  have hlt3 : ∀ x ∈ firstTerms (2 * m + 3),
      x < Nat.fib (m + 3) + 2 * (m + 2) * Nat.fib (m + 2) := by
    intro x hx
    simp only [hpre3, hpre2, List.mem_append, List.mem_singleton] at hx
    rcases hx with (hx | rfl) | rfl
    · have := hlt x hx
      linarith
    · linarith
    · have h4 : 4 * Nat.fib (m + 2) ≤ 2 * (m + 2) * Nat.fib (m + 2) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
  have hfib3 : ∀ x ∈ firstTerms (2 * m + 3), x ≤ Nat.fib (m + 3) ∨ ∀ s, Nat.fib s ≠ x := by
    intro x hx
    simp only [hpre3, hpre2, List.mem_append, List.mem_singleton] at hx
    rcases hx with (hx | rfl) | rfl
    · rcases hfib x hx with h1 | h1
      · exact Or.inl (le_trans h1 Nat.fib_le_fib_succ)
      · exact Or.inr h1
    · exact Or.inr (not_fib_E (m + 1) (by omega))
    · exact Or.inl le_rfl
  exact ⟨hsum3, hmem3, hlt3, hfib3, hE, hO⟩

theorem inv_all (m : ℕ) (hm : 4 ≤ m) : InvA m := by
  induction m, hm using Nat.le_induction with
  | base => exact inv_base
  | succ m hm ih => exact inv_step m hm ih

/-- Closed form at even indices: `a(2m) = F(m+1) + 2m F(m)` for `m ≥ 4`. -/
theorem aE (m m1 n : ℕ) (hm : 4 ≤ m) (h1 : m1 = m + 1) (hn : n = 2 * m) :
    a n = Nat.fib m1 + 2 * m * Nat.fib m := by
  subst h1 hn
  exact (inv_all m hm).2.2.2.2.1

/-- Closed form at odd indices: `a(2m+1) = F(m+2)` for `m ≥ 4`. -/
theorem aO (m m2 n : ℕ) (hm : 4 ≤ m) (h2 : m2 = m + 2) (hn : n = 2 * m + 1) :
    a n = Nat.fib m2 := by
  subst h2 hn
  exact (inv_all m hm).2.2.2.2.2

end OMA.A249265Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a249265.main := by
  intro n hn
  obtain ⟨p, rfl | rfl⟩ : ∃ p, n = 2 * p + 16 ∨ n = 2 * p + 17 := ⟨(n - 16) / 2, by omega⟩
  · rw [OMA.A249265Proof.aE (p + 8) (p + 9) (2 * p + 16) (by omega) (by omega) (by omega),
      OMA.A249265Proof.aE (p + 7) (p + 8) (2 * p + 16 - 2) (by omega) (by omega) (by omega),
      OMA.A249265Proof.aE (p + 6) (p + 7) (2 * p + 16 - 4) (by omega) (by omega) (by omega),
      OMA.A249265Proof.aE (p + 5) (p + 6) (2 * p + 16 - 6) (by omega) (by omega) (by omega),
      OMA.A249265Proof.aE (p + 4) (p + 5) (2 * p + 16 - 8) (by omega) (by omega) (by omega)]
    have h6 : Nat.fib (p + 6) = Nat.fib (p + 4) + Nat.fib (p + 5) := Nat.fib_add_two
    have h7 : Nat.fib (p + 7) = Nat.fib (p + 5) + Nat.fib (p + 6) := Nat.fib_add_two
    have h8 : Nat.fib (p + 8) = Nat.fib (p + 6) + Nat.fib (p + 7) := Nat.fib_add_two
    have h9 : Nat.fib (p + 9) = Nat.fib (p + 7) + Nat.fib (p + 8) := Nat.fib_add_two
    rw [h9, h8, h7, h6]
    push_cast
    ring
  · rw [OMA.A249265Proof.aO (p + 8) (p + 10) (2 * p + 17) (by omega) (by omega) (by omega),
      OMA.A249265Proof.aO (p + 7) (p + 9) (2 * p + 17 - 2) (by omega) (by omega) (by omega),
      OMA.A249265Proof.aO (p + 6) (p + 8) (2 * p + 17 - 4) (by omega) (by omega) (by omega),
      OMA.A249265Proof.aO (p + 5) (p + 7) (2 * p + 17 - 6) (by omega) (by omega) (by omega),
      OMA.A249265Proof.aO (p + 4) (p + 6) (2 * p + 17 - 8) (by omega) (by omega) (by omega)]
    have h8 : Nat.fib (p + 8) = Nat.fib (p + 6) + Nat.fib (p + 7) := Nat.fib_add_two
    have h9 : Nat.fib (p + 9) = Nat.fib (p + 7) + Nat.fib (p + 8) := Nat.fib_add_two
    have h10 : Nat.fib (p + 10) = Nat.fib (p + 8) + Nat.fib (p + 9) := Nat.fib_add_two
    rw [h10, h9, h8]
    push_cast
    ring
