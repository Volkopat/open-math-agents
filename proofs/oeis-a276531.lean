import OMAStatements.S_oeis_a276531

-- Problem: A276531: a(n) = (a(n-1) * a(n-5) + a(n-2) * a(n-3) * a(n-4)) / a(n-6), with a(0) = a(1) = a(2) = a(3) = a(4) = a(5) = 1.
-- Upstream: formal-conjectures statements/oeis-a276531.lean:0 (declaration OMA.S_oeis_a276531.main)
-- Credit: @oceancheol (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Proof (elementary, in the style of the classical integrality proofs for Somos sequences).
-- Let b be the sequence of natural numbers defined by the same recurrence with floor division.
-- By induction on n we prove together:
--   (pos) b k > 0 for k < n + 6,
--   (rel) b (k+6) * b k = b (k+5) * b (k+1) + b (k+4) * b (k+3) * b (k+2) for k < n,
--   (cop) b i and b j are coprime for i < j <= i + 5, j < n + 6.
-- Exactness of the next division: with x0 = b (k+6), y_j = b (k+6-j), x_i = b (k+6+i) and
-- T = x5 * x1 + x4 * x3 * x2, the six previous relations give an explicit Q with
-- T * (y1 * y2 * y3 * y4 * y5) = x0 * Q; as x0 is coprime to y1, ..., y5, x0 divides T.
-- Coprimality of the new term z with the five terms before it follows from
-- z * b n = w1 * w5 + w2 * w3 * w4 and the coprimality of w1, ..., w5.
-- Remark: a 2016 comment in the OEIS entry (M. Somos) states that the recursion has the
-- Laurent property, which would also imply integrality; no proof is given there.

namespace OMA.A276531

/-- The recurrence of A276531 over the natural numbers, with floor division. -/
def b : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | (n + 6) => (b (n + 5) * b (n + 1) + b (n + 4) * b (n + 3) * b (n + 2)) / b n

lemma b_add_six (n : ℕ) :
    b (n + 6) = (b (n + 5) * b (n + 1) + b (n + 4) * b (n + 3) * b (n + 2)) / b n := by
  rw [b]

lemma a_add_six (n : ℕ) :
    OMA.S_oeis_a276531.a (n + 6) =
      (OMA.S_oeis_a276531.a (n + 5) * OMA.S_oeis_a276531.a (n + 1) +
        OMA.S_oeis_a276531.a (n + 4) * OMA.S_oeis_a276531.a (n + 3) *
          OMA.S_oeis_a276531.a (n + 2)) / OMA.S_oeis_a276531.a n := by
  rw [OMA.S_oeis_a276531.a]

lemma cop_step (z c w u v : ℕ) (h : z * c = w * u + v) (hwv : Nat.Coprime w v) :
    Nat.Coprime z w := by
  have hd1 : Nat.gcd z w ∣ w * u + v := by
    rw [← h]
    exact Dvd.dvd.mul_right (Nat.gcd_dvd_left z w) c
  have hd2 : Nat.gcd z w ∣ w * u := Dvd.dvd.mul_right (Nat.gcd_dvd_right z w) u
  have hd3 : Nat.gcd z w ∣ v := (Nat.dvd_add_right hd2).mp hd1
  have hd4 : Nat.gcd z w ∣ Nat.gcd w v := Nat.dvd_gcd (Nat.gcd_dvd_right z w) hd3
  have h1 : Nat.gcd w v = 1 := hwv
  rw [h1] at hd4
  exact Nat.dvd_one.mp hd4

lemma dvd_step (x0 x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 y6 : ℕ)
    (r1 : x5 * y1 = x4 * x0 + x3 * x2 * x1)
    (r2 : x4 * y2 = x3 * y1 + x2 * x1 * x0)
    (r3 : x3 * y3 = x2 * y2 + x1 * x0 * y1)
    (r4 : x2 * y4 = x1 * y3 + x0 * y1 * y2)
    (r5 : x1 * y5 = x0 * y4 + y1 * y2 * y3)
    (r6 : x0 * y6 = y1 * y5 + y2 * y3 * y4) :
    x0 ∣ (x5 * x1 + x4 * x3 * x2) * (y1 * y2 * y3 * y4 * y5) := by
  have h1 : (x5 : ℤ) * y1 = x4 * x0 + x3 * x2 * x1 := by exact_mod_cast r1
  have h2 : (x4 : ℤ) * y2 = x3 * y1 + x2 * x1 * x0 := by exact_mod_cast r2
  have h3 : (x3 : ℤ) * y3 = x2 * y2 + x1 * x0 * y1 := by exact_mod_cast r3
  have h4 : (x2 : ℤ) * y4 = x1 * y3 + x0 * y1 * y2 := by exact_mod_cast r4
  have h5 : (x1 : ℤ) * y5 = x0 * y4 + y1 * y2 * y3 := by exact_mod_cast r5
  have h6 : (x0 : ℤ) * y6 = y1 * y5 + y2 * y3 * y4 := by exact_mod_cast r6
  have key : (x0 : ℤ) ∣ ((x5 : ℤ) * x1 + x4 * x3 * x2) * (y1 * y2 * y3 * y4 * y5) := by
    refine ⟨(x3 : ℤ) * x2 * y2 * x1 * y3 * y1 * y6 + x3 * x2 * y2 * x1 * y3 * (y4 * y4)
        + x3 * x2 * y2 * (y1 ^ 3 * y2) * y5 + x3 * x2 * (x1 * y1 ^ 3) * y4 * y5
        + (x1 * y2 * x4 + x3 * x2 * x2 * x1 * y1) * y3 * y4 * y5, ?_⟩
    linear_combination (x1 * y2 * y3 * y4 * y5 : ℤ) * h1 + (x3 * x2 * y1 * y3 * y4 * y5 : ℤ) * h2
      + (x3 * x2 * y1 ^ 2 * y4 * y5 : ℤ) * h3 + (x3 * x2 * y2 * y1 ^ 2 * y5 : ℤ) * h4
      + (x3 * x2 * y2 * x1 * y3 * y4 : ℤ) * h5 - (x3 * x2 * y2 * x1 * y3 * y1 : ℤ) * h6
  exact_mod_cast key

lemma inv (n : ℕ) :
    (∀ k, k < n + 6 → 0 < b k) ∧
    (∀ k, k < n →
      b (k + 6) * b k = b (k + 5) * b (k + 1) + b (k + 4) * b (k + 3) * b (k + 2)) ∧
    (∀ i j, i < j → j < n + 6 → j ≤ i + 5 → Nat.Coprime (b i) (b j)) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      interval_cases k <;> simp [b]
    · intro k hk
      omega
    · intro i j hij hj _
      have hi : i < 6 := by omega
      interval_cases j <;> interval_cases i <;> simp [b]
  | succ n ih =>
    obtain ⟨hpos, hrel, hcop⟩ := ih
    have hT : b n ∣ b (n + 5) * b (n + 1) + b (n + 4) * b (n + 3) * b (n + 2) := by
      rcases Nat.lt_or_ge n 6 with h6 | h6
      · have h1 : b n = 1 := by interval_cases n <;> simp [b]
        rw [h1]
        exact one_dvd _
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
        have r6 := hrel k (by omega)
        have r5 := hrel (k + 1) (by omega)
        have r4 := hrel (k + 2) (by omega)
        have r3 := hrel (k + 3) (by omega)
        have r2 := hrel (k + 4) (by omega)
        have r1 := hrel (k + 5) (by omega)
        have c1 : Nat.Coprime (b (k + 6)) (b (k + 5)) :=
          (hcop (k + 5) (k + 6) (by omega) (by omega) (by omega)).symm
        have c2 : Nat.Coprime (b (k + 6)) (b (k + 4)) :=
          (hcop (k + 4) (k + 6) (by omega) (by omega) (by omega)).symm
        have c3 : Nat.Coprime (b (k + 6)) (b (k + 3)) :=
          (hcop (k + 3) (k + 6) (by omega) (by omega) (by omega)).symm
        have c4 : Nat.Coprime (b (k + 6)) (b (k + 2)) :=
          (hcop (k + 2) (k + 6) (by omega) (by omega) (by omega)).symm
        have c5 : Nat.Coprime (b (k + 6)) (b (k + 1)) :=
          (hcop (k + 1) (k + 6) (by omega) (by omega) (by omega)).symm
        simp only [Nat.add_assoc, Nat.reduceAdd] at r1 r2 r3 r4 r5 r6 ⊢
        have hd := dvd_step (b (k + 6)) (b (k + 7)) (b (k + 8)) (b (k + 9)) (b (k + 10))
          (b (k + 11)) (b (k + 5)) (b (k + 4)) (b (k + 3)) (b (k + 2)) (b (k + 1)) (b k)
          r1 r2 r3 r4 r5 r6
        exact ((((c1.mul_right c2).mul_right c3).mul_right c4).mul_right c5).dvd_of_dvd_mul_right hd
    have hrel_n : b (n + 6) * b n
        = b (n + 5) * b (n + 1) + b (n + 4) * b (n + 3) * b (n + 2) := by
      rw [b_add_six]
      exact Nat.div_mul_cancel hT
    have hTpos : 0 < b (n + 5) * b (n + 1) + b (n + 4) * b (n + 3) * b (n + 2) :=
      Nat.add_pos_left (Nat.mul_pos (hpos _ (by omega)) (hpos _ (by omega))) _
    have hnew : 0 < b (n + 6) := by
      apply Nat.pos_of_ne_zero
      intro h0
      rw [h0, zero_mul] at hrel_n
      exact (Nat.ne_of_gt hTpos) hrel_n.symm
    have c12 : Nat.Coprime (b (n + 1)) (b (n + 2)) := hcop _ _ (by omega) (by omega) (by omega)
    have c13 : Nat.Coprime (b (n + 1)) (b (n + 3)) := hcop _ _ (by omega) (by omega) (by omega)
    have c14 : Nat.Coprime (b (n + 1)) (b (n + 4)) := hcop _ _ (by omega) (by omega) (by omega)
    have c25 : Nat.Coprime (b (n + 2)) (b (n + 5)) := hcop _ _ (by omega) (by omega) (by omega)
    have c35 : Nat.Coprime (b (n + 3)) (b (n + 5)) := hcop _ _ (by omega) (by omega) (by omega)
    have c45 : Nat.Coprime (b (n + 4)) (b (n + 5)) := hcop _ _ (by omega) (by omega) (by omega)
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      rcases Nat.lt_or_ge k (n + 6) with h | h
      · exact hpos k h
      · obtain rfl : k = n + 6 := by omega
        exact hnew
    · intro k hk
      rcases Nat.lt_or_ge k n with h | h
      · exact hrel k h
      · obtain rfl : k = n := by omega
        exact hrel_n
    · intro i j hij hj hji
      rcases Nat.lt_or_ge j (n + 6) with h | h
      · exact hcop i j hij h hji
      · obtain rfl : j = n + 6 := by omega
        have hi : i = n + 1 ∨ i = n + 2 ∨ i = n + 3 ∨ i = n + 4 ∨ i = n + 5 := by omega
        rcases hi with rfl | rfl | rfl | rfl | rfl
        · refine (cop_step (b (n + 6)) (b n) (b (n + 1)) (b (n + 5))
            (b (n + 4) * b (n + 3) * b (n + 2)) ?_ ((c14.mul_right c13).mul_right c12)).symm
          rw [hrel_n]
          ring
        · refine (cop_step (b (n + 6)) (b n) (b (n + 2)) (b (n + 4) * b (n + 3))
            (b (n + 5) * b (n + 1)) ?_ (c25.mul_right c12.symm)).symm
          rw [hrel_n]
          ring
        · refine (cop_step (b (n + 6)) (b n) (b (n + 3)) (b (n + 4) * b (n + 2))
            (b (n + 5) * b (n + 1)) ?_ (c35.mul_right c13.symm)).symm
          rw [hrel_n]
          ring
        · refine (cop_step (b (n + 6)) (b n) (b (n + 4)) (b (n + 3) * b (n + 2))
            (b (n + 5) * b (n + 1)) ?_ (c45.mul_right c14.symm)).symm
          rw [hrel_n]
          ring
        · refine (cop_step (b (n + 6)) (b n) (b (n + 5)) (b (n + 1))
            (b (n + 4) * b (n + 3) * b (n + 2)) ?_
            ((c45.symm.mul_right c35.symm).mul_right c25.symm)).symm
          exact hrel_n

lemma a_eq (n : ℕ) : OMA.S_oeis_a276531.a n = (b n : ℚ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 6 with h | h
    · interval_cases n <;> simp [OMA.S_oeis_a276531.a, b]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
      have hrel := (inv (k + 1)).2.1 k (by omega)
      have hpos := (inv (k + 1)).1 k (by omega)
      rw [a_add_six, ih (k + 5) (by omega), ih (k + 1) (by omega), ih (k + 4) (by omega),
        ih (k + 3) (by omega), ih (k + 2) (by omega), ih k (by omega)]
      have hq : (b (k + 6) : ℚ) * (b k : ℚ)
          = (b (k + 5) : ℚ) * b (k + 1) + b (k + 4) * b (k + 3) * b (k + 2) := by
        exact_mod_cast hrel
      have hne : (b k : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
      rw [div_eq_iff hne]
      exact hq.symm

end OMA.A276531

theorem OMA.solution : type_of% @OMA.S_oeis_a276531.main := by
  intro n
  exact ⟨(OMA.A276531.b n : ℤ), by rw [OMA.A276531.a_eq, Int.cast_natCast]⟩
