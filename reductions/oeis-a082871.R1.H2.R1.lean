import OMAReductions.R_oeis_a082871_R1

-- Reduction oeis-a082871.R1.H2.R1 of step oeis-a082871.R1.H2
-- Credit: @ehsanmok

/-! H2 of oeis-a082871.R1 from two explicit prime-distribution statements.

Write A = (x+1)(x+2)...(y). If a prime q with q ≤ x < 2q has 2q ≤ y then q divides A, so q does not
divide 1+A. Otherwise every prime of (x/2, x] would have to divide 1+A, hence so would their product,
which forces (product of the primes in (x/2, x]) ≤ 1+A ≤ 1 + (x+1)...(2q-1). H1 (a Chebyshev-type lower
bound for that product) and H2 (a short prime gap above x/2) contradict this for x ≥ 400.
The range 11 ≤ x < 400 is checked by kernel evaluation with a table of primes. -/

namespace OMA.R_oeis_a082871_R1_H2_R1

private def PL : List ℕ := [7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397]
private def cands (x : ℕ) : List ℕ := PL.filter fun p => Nat.ble p x && Nat.blt x (2*p)

private def tst (c : List ℕ) (A : ℕ) : Bool := c.any fun p => !Nat.beq ((1+A) % p) 0

private def loop (c : List ℕ) (x : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | f+1, k, A => tst c A && loop c x f (k+1) ((x+1+k)*A)

lemma loop_spec (c : List ℕ) (x : ℕ) : ∀ f k, loop c x f k ((x+1).ascFactorial k) = true →
    ∀ j, j < f → tst c ((x+1).ascFactorial (k+j)) = true := by
  intro f
  induction f with
  | zero => intro k _ j hj; omega
  | succ f ih =>
    intro k h j hj
    simp only [loop, Bool.and_eq_true] at h
    rcases j with _ | j
    · simpa using h.1
    · have h2 := h.2
      rw [← Nat.ascFactorial_succ] at h2
      have h3 := ih (k+1) h2 j (by omega)
      rwa [show k + (j+1) = k+1+j by omega]

lemma PL_prime : ∀ p ∈ PL, p.Prime := by decide +kernel

lemma fin_all : ∀ x < 400, 11 ≤ x → loop (cands x) x x 0 1 = true := by decide +kernel

/-- The primes of (x/2, x] multiply to at least 2^(x/2). -/
def H1 : Prop := ∀ x : ℕ, 400 ≤ x →
    2 ^ (x/2) ≤ ∏ p ∈ (Finset.Ioc (x/2) x).filter Nat.Prime, p

/-- Some prime q of (x/2, x] is so close to x/2 that 1 + (x+1)(x+2)...(2q-1) < 2^(x/2). -/
def H2 : Prop := ∀ x : ℕ, 400 ≤ x →
    ∃ p : ℕ, p.Prime ∧ p ≤ x ∧ x < 2*p ∧ 1 + (x+1).ascFactorial (2*p-1-x) < 2 ^ (x/2)

lemma finite_part {x y : ℕ} (lo : 11 ≤ x) (hi : x < 400) (le : x ≤ y) (lt : y < 2*x) :
    ∃ p : ℕ, p.Prime ∧ p ≤ x ∧ x < 2*p ∧ ¬ p ∣ 1+(x+1).ascFactorial (y-x) := by
  have h0 := fin_all x hi lo
  have h := loop_spec (cands x) x x 0 (by simpa using h0) (y-x) (by omega)
  rw [Nat.zero_add] at h
  unfold tst at h
  rw [List.any_eq_true] at h
  obtain ⟨p, hp, hc⟩ := h
  unfold cands at hp
  rw [List.mem_filter] at hp
  obtain ⟨hpl, hr⟩ := hp
  rw [Bool.and_eq_true] at hr
  have r1 : p ≤ x := Nat.le_of_ble_eq_true hr.1
  have r2 : x < 2*p := Nat.le_of_ble_eq_true hr.2
  refine ⟨p, PL_prime p hpl, r1, r2, fun hd => ?_⟩
  rw [Nat.mod_eq_zero_of_dvd hd] at hc
  simp at hc

lemma dvd_asc {x y n : ℕ} (h1 : x < n) (h2 : n ≤ y) : n ∣ (x+1).ascFactorial (y-x) := by
  rw [Nat.ascFactorial_eq_prod_range]
  have : n = x + 1 + (n - x - 1) := by omega
  rw [this]
  exact Finset.dvd_prod_of_mem (fun i => x + 1 + i) (Finset.mem_range.mpr (by omega))

lemma asc_mono (n : ℕ) {k l : ℕ} (h : k ≤ l) : (n+1).ascFactorial k ≤ (n+1).ascFactorial l := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← Nat.ascFactorial_mul_ascFactorial]
  have hpos : 0 < (n+1+k).ascFactorial j := by
    rw [show n+1+k = (n+k)+1 by omega]
    exact Nat.ascFactorial_pos _ _
  exact Nat.le_mul_of_pos_right _ hpos

theorem main : H1 → H2 → OMA.R_oeis_a082871_R1.H2 := by
  intro hprod hgap x y lo le lt
  by_cases hx : x < 400
  · exact finite_part lo hx le lt
  have hx' : 400 ≤ x := by omega
  obtain ⟨q, hq, qle, qhi, qsz⟩ := hgap x hx'
  by_cases hy : 2*q ≤ y
  · refine ⟨q, hq, qle, qhi, fun hd => ?_⟩
    have d1 : q ∣ (x+1).ascFactorial (y-x) :=
      (Dvd.intro_left 2 rfl).trans (dvd_asc (n := 2*q) qhi hy)
    have d2 : q ∣ 1 := (Nat.dvd_add_left d1).mp hd
    exact hq.one_lt.ne' (Nat.dvd_one.mp d2)
  by_contra hcon
  have hne : ∀ p : ℕ, p.Prime → p ≤ x → x < 2*p → p ∣ 1+(x+1).ascFactorial (y-x) := by
    intro p hp h1 h2
    by_contra hd
    exact hcon ⟨p, hp, h1, h2, hd⟩
  have hdvd : ∏ p ∈ (Finset.Ioc (x/2) x).filter Nat.Prime, p ∣ 1+(x+1).ascFactorial (y-x) := by
    apply Finset.prod_primes_dvd
    · intro a ha
      exact (Finset.mem_filter.mp ha).2.prime
    · intro a ha
      obtain ⟨hm, hpa⟩ := Finset.mem_filter.mp ha
      have hm' := Finset.mem_Ioc.mp hm
      exact hne a hpa hm'.2 (by omega)
  have h1 := Nat.le_of_dvd (by omega) hdvd
  have h2 := asc_mono x (show y - x ≤ 2*q-1-x by omega)
  have h3 := hprod x hx'
  omega

end OMA.R_oeis_a082871_R1_H2_R1
