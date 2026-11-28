import FormalConjectures.ErdosProblems.«384»

/-!
Short elementary proof of Ecklund's theorem (Erdős problem 384).
For `n = m + j + 2`, `k = j + 2 ≤ m`, if every prime divisor `p` of `C(n, k)` satisfies
`n < 2 * p`, then every non-prime `a` with `0 < a ≤ n` is coprime to `C(n, k)`. Applying
this single cancellation rule to the standard binomial identities gives `n` and `m + 1` prime
(so `j` is odd and `m` is even), `j + 3 ∣ m`, `m + 2 ∣ (j + 2) * (j + 1)`, and
`m + j + 1 ∣ (j + 2) * (j + 1)`. Writing `m = (j + 3) * s` leaves only `(m, j) = (4, 1)`.
-/

theorem OMA.core (m j : ℕ) (hkm : j + 2 ≤ m)
    (hA : ∀ p : ℕ, p.Prime → p ∣ (m + j + 2).choose (j + 2) → m + j + 2 < 2 * p) :
    m = 4 ∧ j = 1 := by
  set n := m + j + 2
  set N := n.choose (j + 2)
  have cancel {a b : ℕ} (ha0 : 0 < a) (han : a ≤ n) (hnp : ¬ a.Prime) (hd : a ∣ N * b) : a ∣ b := by
    refine Nat.Coprime.dvd_of_dvd_mul_left ?_ hd
    by_contra h
    obtain ⟨p, hp, ⟨c, rfl⟩, hpN⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    have h2 := hA p hp hpN
    have hc : c = 1 := by
      by_cases hc : 2 ≤ c
      · have := Nat.mul_le_mul_left p hc
        omega
      · rcases c with _ | c
        · simp at ha0
        · omega
    exact hnp (by simpa [hc] using hp)
  have ev {a b : ℕ} (h4 : 4 ≤ a) (han : a ≤ n) (h2 : a % 2 = 0) (hd : a ∣ N * b) : a ∣ b :=
    cancel (by omega) han (fun hp => by rcases hp.eq_two_or_odd with h | h <;> omega) hd
  have I1 : n * (m + j + 1).choose (j + 1) = N * (j + 2) :=
    Nat.add_one_mul_choose_eq (m + j + 1) (j + 1)
  have I2 : N * (j + 2) = n.choose (j + 1) * (m + 1) := by
    have h := Nat.choose_succ_right_eq n (j + 1)
    rwa [show n - (j + 1) = m + 1 by omega] at h
  have hnP : n.Prime := by
    by_contra hnp
    have hd : n ∣ j + 2 := cancel (by omega) le_rfl hnp (Dvd.intro _ I1)
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hmP : (m + 1).Prime := by
    by_contra hnp
    have hd : m + 1 ∣ j + 2 := cancel (by omega) (by omega) hnp (Dvd.intro_left _ I2.symm)
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hn_odd : n % 2 = 1 := hnP.eq_two_or_odd.resolve_left (by omega)
  have hm_odd : (m + 1) % 2 = 1 := hmP.eq_two_or_odd.resolve_left (by omega)
  have F2 : (j + 3) ∣ m := by
    have h := Nat.choose_succ_right_eq n (j + 2)
    rw [show n - (j + 2) = m by omega] at h
    exact ev (by omega) (by omega) (by omega) (Dvd.intro_left _ h)
  have F3 : (m + 2) ∣ (j + 2) * (j + 1) := by
    have h := Nat.choose_succ_right_eq n j
    rw [show n - j = m + 2 by omega] at h
    refine ev (by omega) (by omega) (by omega) ⟨n.choose j * (m + 1), ?_⟩
    calc N * ((j + 2) * (j + 1)) = (N * (j + 2)) * (j + 1) := by ring
      _ = (n.choose (j + 1) * (j + 1)) * (m + 1) := by rw [I2]; ring
      _ = (m + 2) * (n.choose j * (m + 1)) := by rw [h]; ring
  have F4 : (m + j + 1) ∣ (j + 2) * (j + 1) := by
    have h := Nat.add_one_mul_choose_eq (m + j) j
    refine ev (by omega) (by omega) (by omega) ⟨n * (m + j).choose j, ?_⟩
    calc N * ((j + 2) * (j + 1)) = (N * (j + 2)) * (j + 1) := by ring
      _ = n * ((m + j + 1).choose (j + 1) * (j + 1)) := by rw [← I1]; ring
      _ = (m + j + 1) * (n * (m + j).choose j) := by rw [← h]; ring
  obtain ⟨s, hs⟩ := F2
  rcases s with _ | _ | t
  · simp at hs; omega
  · have hm' : m = j + 3 := by simpa using hs
    have h12 : (j + 5) ∣ 12 := by
      have h : (j + 5) ∣ (j + 5) * j + 12 := by
        rw [show (j + 5) * j + 12 = (j + 2) * (j + 1) + (j + 5) * 2 by ring]
        exact Dvd.dvd.add (by rwa [hm'] at F3) (dvd_mul_right _ _)
      exact (Nat.dvd_add_right (dvd_mul_right _ _)).mp h
    obtain ⟨q, hq⟩ := h12
    have hq2 : q ≤ 2 := by nlinarith
    interval_cases q
    · omega
    · exfalso
      have h2 : 2 ∣ N := by
        change 2 ∣ (m + j + 2).choose (j + 2)
        rw [hm', show j = 7 by omega]
        decide
      have := hA 2 Nat.prime_two h2; omega
    · exact ⟨by omega, by omega⟩
  · exfalso
    subst hs
    have hle : (j + 3) * (t + 2) + j + 1 ≤ (j + 2) * (j + 1) := Nat.le_of_dvd (by positivity) F4
    have hjt : t + 1 ≤ j := by
      by_contra h
      have h1 : (j + 3) * (j + 2) ≤ (j + 3) * (t + 2) := Nat.mul_le_mul_left _ (by omega)
      nlinarith
    let D := (j + 3) * (t + 2) + j + 1
    have hd : D ∣ 2 * (t + 2) * (t + 1) := by
      apply (Nat.dvd_add_right (dvd_mul_right D ((t + 3) * j + 2))).mp
      rw [show D * ((t + 3) * j + 2) + 2 * (t + 2) * (t + 1) =
        (t + 3) ^ 2 * ((j + 2) * (j + 1)) by dsimp [D]; ring]
      exact Dvd.dvd.mul_left F4 _
    obtain ⟨c, hc⟩ := hd
    dsimp [D] at hc
    have hc1 : c = 1 := by
      rcases c with _ | _ | c
      · simp at hc
      · rfl
      · have hmul := Nat.mul_le_mul_left ((j + 3) * (t + 2) + j + 1) (show 2 ≤ c+2 by omega)
        have hle' := Nat.mul_le_mul_right (t + 2) (show t + 4 ≤ j + 3 by omega)
        nlinarith
    rw [hc1, mul_one] at hc
    have h6 : (t + 3) ∣ 6 := by
      have h1 : (t + 3) ∣ (t + 3) * (2 * t) + 6 := ⟨j + 3, by nlinarith⟩
      exact (Nat.dvd_add_right (dvd_mul_right _ _)).mp h1
    have ht : t ≤ 3 := by have := Nat.le_of_dvd (by decide) h6; omega
    have h4 : (t + 3) * (t + 1) ≤ (t + 3) * 4 := Nat.mul_le_mul_left _ (by omega)
    nlinarith

theorem OMA.solution : type_of% @Erdos384.erdos_384 := by
  intro n k hk hkn h₃ h₄
  by_contra hex
  have hcon : ∀ p : ℕ, p.Prime → p ∣ n.choose k → n < 2 * p := fun p hp hd => by
    by_contra h; exact hex ⟨p, hp, hd, by omega⟩
  rcases Nat.le_total k (n - k) with h | h
  · obtain ⟨h1, h2⟩ := OMA.core (n - k) (k - 2) (by omega) (by
      rwa [show n - k + (k - 2) + 2 = n by omega, show k - 2 + 2 = k by omega])
    exact h₃ (Prod.ext (by omega) (by omega))
  · obtain ⟨h1, h2⟩ := OMA.core k (n - k - 2) (by omega) (by
      have e : (k + (n - k - 2) + 2).choose (n - k - 2 + 2) = n.choose k := by
        rw [show k + (n - k - 2) + 2 = n by omega, show n - k - 2 + 2 = n - k by omega,
          Nat.choose_symm (by omega)]
      rw [e, show k + (n - k - 2) + 2 = n by omega]
      exact hcon)
    exact h₄ (Prod.ext (by omega) (by omega))
