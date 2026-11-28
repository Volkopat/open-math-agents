import OMAStatements.S_oeis_a120860
import Mathlib

namespace OMA.A120860Proof

open OMA.S_oeis_a120860

/-! ## Floors of multiples of `√2` as `Nat.sqrt` -/

theorem sqrt_cast_eq (k : ℕ) : Real.sqrt ((2 * k * k : ℕ) : ℝ) = (k : ℝ) * Real.sqrt 2 := by
  rw [show ((2 * k * k : ℕ) : ℝ) = (k : ℝ) ^ 2 * 2 by push_cast; ring,
    Real.sqrt_mul (sq_nonneg (k : ℝ)) 2, Real.sqrt_sq (Nat.cast_nonneg k)]

theorem nfloor (k : ℕ) : ⌊(k : ℝ) * Real.sqrt 2⌋₊ = Nat.sqrt (2 * k * k) := by
  rw [← sqrt_cast_eq, Real.nat_floor_real_sqrt_eq_nat_sqrt]

theorem ifloor (k : ℕ) : ⌊Real.sqrt 2 * (k : ℝ)⌋ = ((Nat.sqrt (2 * k * k) : ℕ) : ℤ) := by
  rw [mul_comm (Real.sqrt 2) (k : ℝ), ← sqrt_cast_eq, Real.floor_real_sqrt_eq_nat_sqrt]

theorem f_eq (n : ℕ) : f n = 3 * n + 2 * Nat.sqrt (2 * n * n) := by
  unfold f
  rw [nfloor]

theorem a_eq (m : ℕ) : A187967 m =
    ((Nat.sqrt (2 * (m + 2) * (m + 2)) : ℕ) : ℤ) - ((Nat.sqrt (2 * m * m) : ℕ) : ℤ) - 2 := by
  have e1 : Real.sqrt 2 * (m : ℝ) + 2 * Real.sqrt 2 = Real.sqrt 2 * ((m + 2 : ℕ) : ℝ) := by
    push_cast; ring
  have e3 : 2 * Real.sqrt 2 = Real.sqrt 2 * ((2 : ℕ) : ℝ) := by
    push_cast; ring
  have h8 : Nat.sqrt (2 * 2 * 2) = 2 := (Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm
  have h1 : ⌊Real.sqrt 2 * (m : ℝ) + 2 * Real.sqrt 2⌋ =
      ((Nat.sqrt (2 * (m + 2) * (m + 2)) : ℕ) : ℤ) := by
    rw [e1, ifloor]
  have h2 : ⌊Real.sqrt 2 * (m : ℝ)⌋ = ((Nat.sqrt (2 * m * m) : ℕ) : ℤ) := ifloor m
  have h3 : ⌊2 * Real.sqrt 2⌋ = ((Nat.sqrt (2 * 2 * 2) : ℕ) : ℤ) := by
    rw [e3, ifloor]
  unfold A187967
  rw [h1, h2, h3]
  omega

/-! ## Integer facts about `s = floor(n √2) = Nat.sqrt (2 n n)` -/

theorem sq_spec (x : ℕ) : Nat.sqrt x * Nat.sqrt x ≤ x ∧ x < (Nat.sqrt x + 1) * (Nat.sqrt x + 1) :=
  Nat.eq_sqrt.1 rfl

theorem sqrt_eq_of (a x : ℕ) (h1 : a * a ≤ x) (h2 : x < (a + 1) * (a + 1)) : Nat.sqrt x = a :=
  (Nat.eq_sqrt.2 ⟨h1, h2⟩).symm

/-- Lemma A: `floor(f(n) √2) = 4 n + 3 floor(n √2)`. -/
theorem lemA (n : ℕ) :
    Nat.sqrt (2 * (3 * n + 2 * Nat.sqrt (2 * n * n)) * (3 * n + 2 * Nat.sqrt (2 * n * n))) =
      4 * n + 3 * Nat.sqrt (2 * n * n) := by
  obtain ⟨h1, h2⟩ := sq_spec (2 * n * n)
  apply sqrt_eq_of
  · nlinarith
  · nlinarith

/-- Lemma B: `f (f n) = 6 f n - n`. -/
theorem lemB (n : ℕ) : f (f n) + n = 6 * f n := by
  rw [f_eq (f n), f_eq n, lemA]
  ring

theorem f_zero : f 0 = 0 := by
  have h0 : Nat.sqrt (2 * 0 * 0) = 0 := sqrt_eq_of 0 _ (by norm_num) (by norm_num)
  rw [f_eq]
  omega

theorem f_ge (n : ℕ) : 3 * n ≤ f n := by
  rw [f_eq]; omega

theorem f_lt (n : ℕ) (h : 1 ≤ n) : n < f n := by
  have := f_ge n; omega

/-- `f n + 1` is never a value of `f` (consecutive values differ by at least `3`). -/
theorem f_gap (n k : ℕ) : f k ≠ f n + 1 := by
  rw [f_eq, f_eq]
  rcases le_total k n with hkn | hkn
  · have hkk : 2 * k * k ≤ 2 * n * n := by nlinarith [Nat.mul_self_le_mul_self hkn]
    have := Nat.sqrt_le_sqrt hkk
    omega
  · have hkk : 2 * n * n ≤ 2 * k * k := by nlinarith [Nat.mul_self_le_mul_self hkn]
    have := Nat.sqrt_le_sqrt hkk
    omega

/-! ## Lemma C: the range of `f` and the values of A187967 -/

theorem hc_of_range (n : ℕ) :
    2 * (f n + 2) * (f n + 2) < (Nat.sqrt (2 * f n * f n) + 3) * (Nat.sqrt (2 * f n * f n) + 3) := by
  rw [f_eq, lemA]
  obtain ⟨h1, h2⟩ := sq_spec (2 * n * n)
  nlinarith

/-- The inverse of the unimodular matrix `[[3,2],[4,3]]`: `n = 3m - 2M`, `s = 3M - 4m`. -/
theorem back_core (m M : ℕ) (h1 : M * M ≤ 2 * m * m)
    (hc : 2 * (m + 2) * (m + 2) < (M + 3) * (M + 3)) :
    ∃ n s : ℕ, m = 3 * n + 2 * s ∧ s * s ≤ 2 * n * n ∧ 2 * n * n < (s + 1) * (s + 1) := by
  have hc' : 2 * (m + 2) * (m + 2) + 1 ≤ (M + 3) * (M + 3) := hc
  have hA : 2 * M ≤ 3 * m := by
    by_contra hcon
    push_neg at hcon
    have := Nat.mul_self_le_mul_self (show 3 * m + 1 ≤ 2 * M by omega)
    nlinarith [Nat.zero_le (m * m)]
  have h8 : 8 * m ≤ 6 * M := by nlinarith
  have hB : 4 * m ≤ 3 * M := by omega
  obtain ⟨n, hn⟩ : ∃ n, 3 * m = 2 * M + n := ⟨3 * m - 2 * M, by omega⟩
  obtain ⟨s, hs⟩ : ∃ s, 3 * M = 4 * m + s := ⟨3 * M - 4 * m, by omega⟩
  have hm : m = 3 * n + 2 * s := by omega
  have hMv : M = 4 * n + 3 * s := by omega
  rw [hm, hMv] at h1 hc
  exact ⟨n, s, hm, by nlinarith, by nlinarith⟩

/-- Lemma C: `m` is a value of `f` iff `(m + 2) √2 < floor(m √2) + 3`, i.e. `{m √2} < 3 - 2 √2`. -/
theorem range_iff (m : ℕ) : (∃ n, f n = m) ↔
    2 * (m + 2) * (m + 2) < (Nat.sqrt (2 * m * m) + 3) * (Nat.sqrt (2 * m * m) + 3) := by
  constructor
  · rintro ⟨n, rfl⟩
    exact hc_of_range n
  · intro hc
    obtain ⟨n, s, hm, hs1, hs2⟩ := back_core m (Nat.sqrt (2 * m * m)) (sq_spec (2 * m * m)).1 hc
    refine ⟨n, ?_⟩
    have hsq : Nat.sqrt (2 * n * n) = s := sqrt_eq_of s _ hs1 hs2
    rw [f_eq, hsq]
    omega

theorem T_core (m M : ℕ) (h1 : M * M ≤ 2 * m * m) (h2 : 2 * m * m < (M + 1) * (M + 1)) :
    (M + 2) * (M + 2) ≤ 2 * (m + 2) * (m + 2) ∧ 2 * (m + 2) * (m + 2) < (M + 4) * (M + 4) := by
  have h2' : 2 * m * m + 1 ≤ (M + 1) * (M + 1) := h2
  have hM2 : M ≤ 2 * m := by
    by_contra hcon
    push_neg at hcon
    have := Nat.mul_self_le_mul_self (show 2 * m + 1 ≤ M by omega)
    nlinarith [Nat.zero_le (m * m)]
  have h4 : 4 * m < 3 * M + 4 := by
    by_contra hcon
    push_neg at hcon
    have := Nat.mul_self_le_mul_self hcon
    nlinarith [Nat.zero_le (M * M)]
  have h4' : 4 * m + 1 ≤ 3 * M + 4 := h4
  constructor
  · nlinarith
  · nlinarith

theorem T_bounds (m : ℕ) :
    Nat.sqrt (2 * m * m) + 2 ≤ Nat.sqrt (2 * (m + 2) * (m + 2)) ∧
      Nat.sqrt (2 * (m + 2) * (m + 2)) ≤ Nat.sqrt (2 * m * m) + 3 := by
  obtain ⟨h1, h2⟩ := sq_spec (2 * m * m)
  obtain ⟨hlo, hhi⟩ := T_core m (Nat.sqrt (2 * m * m)) h1 h2
  constructor
  · exact Nat.le_sqrt.2 hlo
  · have := Nat.sqrt_lt.2 hhi
    omega

theorem T_low_iff (m : ℕ) :
    Nat.sqrt (2 * (m + 2) * (m + 2)) = Nat.sqrt (2 * m * m) + 2 ↔
      2 * (m + 2) * (m + 2) < (Nat.sqrt (2 * m * m) + 3) * (Nat.sqrt (2 * m * m) + 3) := by
  obtain ⟨hlo, hhi⟩ := T_bounds m
  constructor
  · intro h
    exact Nat.sqrt_lt.1 (by omega)
  · intro h
    have := Nat.sqrt_lt.2 h
    omega

theorem A_cases (m : ℕ) :
    (A187967 m = 0 ∧
      2 * (m + 2) * (m + 2) < (Nat.sqrt (2 * m * m) + 3) * (Nat.sqrt (2 * m * m) + 3)) ∨
    (A187967 m = 1 ∧
      ¬ 2 * (m + 2) * (m + 2) < (Nat.sqrt (2 * m * m) + 3) * (Nat.sqrt (2 * m * m) + 3)) := by
  rw [a_eq]
  obtain ⟨hlo, hhi⟩ := T_bounds m
  have hiff := T_low_iff m
  by_cases hc : 2 * (m + 2) * (m + 2) < (Nat.sqrt (2 * m * m) + 3) * (Nat.sqrt (2 * m * m) + 3)
  · left
    refine ⟨?_, hc⟩
    have hT := hiff.2 hc
    omega
  · right
    refine ⟨?_, hc⟩
    have hT : ¬ Nat.sqrt (2 * (m + 2) * (m + 2)) = Nat.sqrt (2 * m * m) + 2 :=
      fun h => hc (hiff.1 h)
    omega

theorem A_zero_iff (m : ℕ) : A187967 m = 0 ↔ ∃ n, f n = m := by
  rw [range_iff]
  rcases A_cases m with ⟨h0, hc⟩ | ⟨h1, hc⟩
  · exact ⟨fun _ => hc, fun _ => h0⟩
  · exact ⟨fun h => absurd (h1.symm.trans h) one_ne_zero, fun h => absurd h hc⟩

theorem A_one_iff (m : ℕ) : A187967 m = 1 ↔ ¬ ∃ n, f n = m := by
  rw [range_iff]
  rcases A_cases m with ⟨h0, hc⟩ | ⟨h1, hc⟩
  · exact ⟨fun h => absurd (h0.symm.trans h) zero_ne_one, fun h => absurd hc h⟩
  · exact ⟨fun _ => hc, fun _ => h1⟩

/-! ## Rows are `f`-orbits (Lemma B) -/

theorem row_one (x : ℕ) : row x 1 = x := by
  first
  | rfl
  | simp [row]

theorem row_two (x : ℕ) : row x 2 = f x := by
  first
  | rfl
  | simp [row]

theorem row_rec (x k : ℕ) : row x (k + 3) = 6 * row x (k + 2) - row x (k + 1) := by
  first
  | rfl
  | simp [row]

theorem row_succ (x k : ℕ) :
    row x (k + 2) = f (row x (k + 1)) ∧ row x (k + 3) = f (row x (k + 2)) := by
  induction k with
  | zero =>
    have e3 : row x 3 = 6 * row x 2 - row x 1 := row_rec x 0
    refine ⟨?_, ?_⟩
    · show row x 2 = f (row x 1)
      rw [row_two, row_one]
    · show row x 3 = f (row x 2)
      rw [e3, row_two, row_one]
      have := lemB x
      omega
  | succ k ih =>
    have e : row x (k + 4) = 6 * row x (k + 3) - row x (k + 2) := row_rec x (k + 1)
    refine ⟨?_, ?_⟩
    · show row x (k + 3) = f (row x (k + 2))
      exact ih.2
    · show row x (k + 4) = f (row x (k + 3))
      rw [e, ih.2]
      have := lemB (row x (k + 2))
      omega

theorem row_step (x h : ℕ) (hh : 1 ≤ h) : row x (h + 1) = f (row x h) := by
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  exact (row_succ x k).1

theorem row_range (x h : ℕ) (hh : 2 ≤ h) : ∃ k, f k = row x h := by
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 2 := ⟨h - 2, by omega⟩
  exact ⟨row x (k + 1), (row_succ x k).1.symm⟩

/-! ## Lemma D: the dispersion -/

/-- The set whose least element is `rowStart g`. -/
def missSet (g : ℕ) : Set ℕ :=
  {m : ℕ | 0 < m ∧ ∀ r : ℕ, 1 ≤ r → r < g → ∀ h : ℕ, 1 ≤ h → row (rowStart r) h ≠ m}

theorem mem_missSet (g m : ℕ) :
    m ∈ missSet g ↔ 0 < m ∧ ∀ r : ℕ, 1 ≤ r → r < g → ∀ h : ℕ, 1 ≤ h → row (rowStart r) h ≠ m :=
  Iff.rfl

theorem rs_eq (g : ℕ) : rowStart g = sInf (missSet g) := by
  rw [rowStart, missSet]

theorem missSet_nonempty (g : ℕ) : (missSet g).Nonempty := by
  refine ⟨f ((Finset.range g).sup rowStart) + 1, ?_⟩
  rw [mem_missSet]
  refine ⟨by omega, ?_⟩
  intro r _ hrg h hh heq
  have hrN : rowStart r ≤ (Finset.range g).sup rowStart := Finset.le_sup (Finset.mem_range.2 hrg)
  rcases Nat.lt_or_ge h 2 with h2 | h2
  · have h1 : h = 1 := by omega
    subst h1
    rw [row_one] at heq
    have := f_ge ((Finset.range g).sup rowStart)
    omega
  · obtain ⟨k, hk⟩ := row_range (rowStart r) h h2
    exact f_gap _ k (hk.trans heq)

theorem rs_mem (g : ℕ) : rowStart g ∈ missSet g := by
  rw [rs_eq]
  exact Nat.sInf_mem (missSet_nonempty g)

theorem rs_le (g m : ℕ) (hm : m ∈ missSet g) : rowStart g ≤ m := by
  rw [rs_eq]
  exact Nat.sInf_le hm

theorem rs_pos (g : ℕ) : 0 < rowStart g := ((mem_missSet _ _).1 (rs_mem g)).1

/-- (D i) No `D(g,1)` is a value of `f`. -/
theorem rs_not_range (g k : ℕ) : f k ≠ rowStart g := by
  intro hk
  have hmem := (mem_missSet _ _).1 (rs_mem g)
  have hpos := rs_pos g
  have k_pos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, f_zero] at hk
      omega
    · omega
  have hlt : k < rowStart g := by
    have := f_lt k k_pos
    omega
  have hnot : k ∉ missSet g := fun hkS => by
    have := rs_le g k hkS
    omega
  rw [mem_missSet] at hnot
  push_neg at hnot
  obtain ⟨r, hr1, hrg, h, hh, hrow⟩ := hnot (by omega)
  have hstep := row_step (rowStart r) h hh
  rw [hrow, hk] at hstep
  exact hmem.2 r hr1 hrg (h + 1) (by omega) hstep

theorem rs_strict (g g' : ℕ) (hg : 1 ≤ g) (hgg : g < g') : rowStart g < rowStart g' := by
  have hmem' := (mem_missSet _ _).1 (rs_mem g')
  have hle : rowStart g ≤ rowStart g' := by
    apply rs_le
    rw [mem_missSet]
    exact ⟨hmem'.1, fun r hr1 hrg h hh => hmem'.2 r hr1 (by omega) h hh⟩
  have hne : rowStart g ≠ rowStart g' := by
    have := hmem'.2 g hg hgg 1 le_rfl
    rw [row_one] at this
    exact this
  omega

theorem rs_ge (n : ℕ) : n + 1 ≤ rowStart (n + 1) := by
  induction n with
  | zero =>
    show 1 ≤ rowStart 1
    have := rs_pos 1
    omega
  | succ n ih =>
    have := rs_strict (n + 1) (n + 1 + 1) (by omega) (by omega)
    omega

/-- (D ii) Every positive non-value of `f` is some `D(g,1)`. -/
theorem rs_surj (m : ℕ) (hm : 1 ≤ m) (hnr : ∀ k, f k ≠ m) : ∃ g, 1 ≤ g ∧ rowStart g = m := by
  have hT : ({g : ℕ | 1 ≤ g ∧ m ≤ rowStart g} : Set ℕ).Nonempty := by
    refine ⟨m, ?_⟩
    show 1 ≤ m ∧ m ≤ rowStart m
    refine ⟨hm, ?_⟩
    have := rs_ge (m - 1)
    rwa [Nat.sub_add_cancel hm] at this
  obtain ⟨g0, hg0, hmin0⟩ : ∃ g0 : ℕ, (1 ≤ g0 ∧ m ≤ rowStart g0) ∧
      ∀ r, r < g0 → ¬ (1 ≤ r ∧ m ≤ rowStart r) :=
    ⟨sInf {g : ℕ | 1 ≤ g ∧ m ≤ rowStart g}, Nat.sInf_mem hT, fun r hr => Nat.notMem_of_lt_sInf hr⟩
  have hmin : ∀ r, 1 ≤ r → r < g0 → rowStart r < m := by
    intro r hr1 hr
    have := hmin0 r hr
    omega
  have hmS : m ∈ missSet g0 := by
    rw [mem_missSet]
    refine ⟨by omega, ?_⟩
    intro r hr1 hrg h hh heq
    rcases Nat.lt_or_ge h 2 with h2 | h2
    · have h1 : h = 1 := by omega
      subst h1
      rw [row_one] at heq
      have := hmin r hr1 hrg
      omega
    · obtain ⟨k, hk⟩ := row_range (rowStart r) h h2
      exact hnr k (hk.trans heq)
  exact ⟨g0, hg0.1, le_antisymm (rs_le g0 m hmS) hg0.2⟩

theorem col_iff (m : ℕ) (hm : 1 ≤ m) : (∃ g, 1 ≤ g ∧ D g 1 = m) ↔ ¬ ∃ n, f n = m := by
  constructor
  · rintro ⟨g, _, hD⟩ ⟨n, hn⟩
    have hD1 : D g 1 = rowStart g := row_one (rowStart g)
    exact rs_not_range g n (hn.trans (hD.symm.trans hD1))
  · intro hnr
    push_neg at hnr
    obtain ⟨g, hg, hrs⟩ := rs_surj m hm hnr
    exact ⟨g, hg, (row_one (rowStart g)).trans hrs⟩

end OMA.A120860Proof

open OMA.S_oeis_a120860 OMA.A120860Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a120860.main := by
  refine ⟨fun m hm => ?_, fun m _ => ?_, fun m hm => ?_⟩
  · rw [col_iff m hm, A_one_iff]
  · rw [A_one_iff, A_zero_iff]
  · rw [A_zero_iff, col_iff m hm, not_not]
