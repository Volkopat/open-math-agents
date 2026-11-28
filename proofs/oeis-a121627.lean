import OMAStatements.S_oeis_a121627

-- Problem: A121627: Real part of a complex operation analogous to the factorials.
-- Upstream: formal-conjectures statements/oeis-a121627.lean:0 (declaration OMA.S_oeis_a121627.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: with x = re k(n) and y = im k(n) we have x' = (n+1)(x - y), y' = (n+1)(x + y).
-- By induction, according to n mod 4: y = 0, y = x, x = 0 or y = -x, and the other part is
-- nonzero. Hence a(n) = 0 iff n = 2 mod 4. If n = 0 mod 4 then a(n+1) = (n+1) a(n); if n = 3
-- mod 4 then a(n+1) = 2 (n+1) a(n); if n = 1 mod 4 then a(n+1) = 0 and
-- a(n+2) = -2 (n+1) (n+2) a(n). In each case the quotient is an integer divisible by the index.

open OMA.S_oeis_a121627 in
theorem OMA.solution : type_of% @OMA.S_oeis_a121627.main := by
  have ha : ∀ j : ℕ, a j = (k j).re := fun j => rfl
  have hre : ∀ j : ℕ, (k (j + 1)).re = ((j : ℤ) + 1) * ((k j).re - (k j).im) := by
    intro j
    have h : (k (j + 1)).re =
        ((j : ℤ) + 1) * (k j).re + -1 * ((j : ℤ) + 1) * (k j).im := rfl
    rw [h]
    ring
  have him : ∀ j : ℕ, (k (j + 1)).im = ((j : ℤ) + 1) * ((k j).re + (k j).im) := by
    intro j
    have h : (k (j + 1)).im = ((j : ℤ) + 1) * (k j).im + ((j : ℤ) + 1) * (k j).re := rfl
    rw [h]
    ring
  have inv : ∀ j : ℕ,
      (j % 4 = 0 → (k j).im = 0 ∧ (k j).re ≠ 0) ∧
      (j % 4 = 1 → (k j).im = (k j).re ∧ (k j).re ≠ 0) ∧
      (j % 4 = 2 → (k j).re = 0 ∧ (k j).im ≠ 0) ∧
      (j % 4 = 3 → (k j).im = -(k j).re ∧ (k j).re ≠ 0) := by
    intro j
    induction j with
    | zero =>
      have e1 : (k 0).re = 1 := rfl
      have e2 : (k 0).im = 0 := rfl
      rw [e1, e2]
      exact ⟨fun _ => ⟨rfl, one_ne_zero⟩, fun h => absurd h (by norm_num),
        fun h => absurd h (by norm_num), fun h => absurd h (by norm_num)⟩
    | succ j ih =>
      obtain ⟨h0, h1, h2, h3⟩ := ih
      have hc : ((j : ℤ) + 1) ≠ 0 := by omega
      rw [hre j, him j]
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
      · obtain ⟨e, hx⟩ := h3 (by omega)
        rw [e]
        refine ⟨by ring, ?_⟩
        rw [show (k j).re - -(k j).re = 2 * (k j).re by ring]
        exact mul_ne_zero hc (mul_ne_zero two_ne_zero hx)
      · obtain ⟨e, hx⟩ := h0 (by omega)
        rw [e]
        refine ⟨by ring, ?_⟩
        rw [sub_zero]
        exact mul_ne_zero hc hx
      · obtain ⟨e, hx⟩ := h1 (by omega)
        rw [e]
        refine ⟨by ring, ?_⟩
        rw [show (k j).re + (k j).re = 2 * (k j).re by ring]
        exact mul_ne_zero hc (mul_ne_zero two_ne_zero hx)
      · obtain ⟨e, hy⟩ := h2 (by omega)
        rw [e]
        refine ⟨by ring, ?_⟩
        rw [zero_sub]
        exact mul_ne_zero hc (neg_ne_zero.mpr hy)
  intro n m _ hnm han ham hz
  simp only [ha] at han ham hz ⊢
  obtain ⟨h0, h1, h2, h3⟩ := inv n
  have hn2 : n % 4 ≠ 2 := fun h => han (h2 h).1
  have hc1 : ((n : ℤ) + 1) ≠ 0 := by omega
  have hc2 : ((n : ℤ) + 1 + 1) ≠ 0 := by omega
  have hcast1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by omega
  have hcast2 : ((n + 1 + 1 : ℕ) : ℤ) = (n : ℤ) + 1 + 1 := by omega
  rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 3) with hr | hr | hr
  · obtain ⟨e, hx⟩ := h0 hr
    have hnext : (k (n + 1)).re = (k n).re * ((n : ℤ) + 1) := by
      rw [hre n, e]
      ring
    have hm : m = n + 1 := by
      by_contra hne
      have h := hz (n + 1) (by omega) (by omega)
      rw [hnext] at h
      exact mul_ne_zero hx hc1 h
    subst hm
    rw [hnext, hcast1, Int.mul_ediv_cancel_left _ hx]
    exact ⟨dvd_mul_right _ _, dvd_refl _⟩
  · obtain ⟨e, hx⟩ := h1 hr
    have hz1 : (k (n + 1)).re = 0 := by
      rw [hre n, e]
      ring
    have hi1 : (k (n + 1)).im = (k n).re * (2 * ((n : ℤ) + 1)) := by
      rw [him n, e]
      ring
    have hnext : (k (n + 1 + 1)).re =
        (k n).re * (-(2 * ((n : ℤ) + 1) * ((n : ℤ) + 1 + 1))) := by
      rw [hre (n + 1), hz1, hi1, hcast1]
      ring
    have hne0 : (k n).re * (-(2 * ((n : ℤ) + 1) * ((n : ℤ) + 1 + 1))) ≠ 0 :=
      mul_ne_zero hx (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero two_ne_zero hc1) hc2))
    have hm : m = n + 1 + 1 := by
      rcases (by omega : m = n + 1 ∨ m = n + 1 + 1 ∨ n + 1 + 1 < m) with h | h | h
      · subst h
        exact absurd hz1 ham
      · exact h
      · have h' := hz (n + 1 + 1) (by omega) h
        rw [hnext] at h'
        exact absurd h' hne0
    subst hm
    rw [hnext, hcast2, Int.mul_ediv_cancel_left _ hx]
    exact ⟨dvd_mul_right _ _, dvd_neg.mpr (dvd_mul_left _ _)⟩
  · obtain ⟨e, hx⟩ := h3 hr
    have hnext : (k (n + 1)).re = (k n).re * (2 * ((n : ℤ) + 1)) := by
      rw [hre n, e]
      ring
    have hne0 : (k n).re * (2 * ((n : ℤ) + 1)) ≠ 0 :=
      mul_ne_zero hx (mul_ne_zero two_ne_zero hc1)
    have hm : m = n + 1 := by
      by_contra hne
      have h := hz (n + 1) (by omega) (by omega)
      rw [hnext] at h
      exact hne0 h
    subst hm
    rw [hnext, hcast1, Int.mul_ediv_cancel_left _ hx]
    exact ⟨dvd_mul_right _ _, dvd_mul_left _ _⟩
