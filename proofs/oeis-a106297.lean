import OMAStatements.S_oeis_a106297

/-!
# Proof of the three conjectures of A106297 (period of the Lucas 5-step numbers mod n)

Outline. Every integer sequence with the pentanacci recurrence is an integer combination of
shifts of the pentanacci numbers (Hankel determinant 1), and 9584 times the pentanacci numbers
is an integer combination of shifts of the Lucas sequence (Hankel determinant 9584 = 2^4 * 599).
Hence a period of the Lucas sequence modulo p^k is a period modulo p^k of 9584 g for every
recurrence sequence g. Lifting: if Q is a period modulo p^k but not modulo p^(k+1), then pQ is
a period modulo p^(k+1) but not modulo p^(k+2); this holds for odd p not 599 and k >= 1, for
p = 599 and k >= 2, and for p = 2 and k >= 6. The minimal period divides every period.
Base cases are computed with a fast windowed evaluation: a(4), a(8), a(16), a(32), a(64) =
6, 12, 24, 48, 96 and 96 is not a period mod 128; a(5) = 781 and 781 is not a period mod 25;
a(599) = 598, a(599^2) = 358202 and 358202 is not a period mod 599^3 (chunked computation).
-/

namespace OMA.P_oeis_a106297
open OMA.S_oeis_a106297

/-! ## The Lucas 5-step numbers modulo N -/

theorem s_succ5 (n : ℕ) : s (n + 5) = s n + s (n + 1) + s (n + 2) + s (n + 3) + s (n + 4) := rfl

/-- `P` is a period of `s` modulo `N` (`P = 0` allowed). -/
def Per (N P : ℕ) : Prop := ∀ m : ℕ, s (m + P) ≡ s m [MOD N]

theorem rec_modEq {N : ℕ} (u v : ℕ → ℕ)
    (hu : ∀ n, u (n + 5) = u n + u (n + 1) + u (n + 2) + u (n + 3) + u (n + 4))
    (hv : ∀ n, v (n + 5) = v n + v (n + 1) + v (n + 2) + v (n + 3) + v (n + 4))
    (h : ∀ i < 5, u i ≡ v i [MOD N]) : ∀ n, u n ≡ v n [MOD N] := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 5 with hn | hn
    · exact h n hn
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
      rw [hu, hv]
      exact ((((ih k (by omega)).add (ih (k + 1) (by omega))).add
        (ih (k + 2) (by omega))).add (ih (k + 3) (by omega))).add (ih (k + 4) (by omega))

theorem s_shift_rec (P : ℕ) (n : ℕ) :
    s (n + 5 + P) = s (n + P) + s (n + 1 + P) + s (n + 2 + P) + s (n + 3 + P) + s (n + 4 + P) := by
  rw [show n + 5 + P = n + P + 5 by ring, s_succ5, Nat.add_right_comm n P 1,
    Nat.add_right_comm n P 2, Nat.add_right_comm n P 3, Nat.add_right_comm n P 4]

theorem per_of_init {N P : ℕ} (h : ∀ i < 5, s (i + P) ≡ s i [MOD N]) : Per N P :=
  rec_modEq (fun m => s (m + P)) s (s_shift_rec P) s_succ5 h

/-- Fast computation of five consecutive values modulo `N`. -/
def step (N : ℕ) (t : ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  (t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2, (t.1 + t.2.1 + t.2.2.1 + t.2.2.2.1 + t.2.2.2.2) % N)

def win (N : ℕ) : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ
  | 0 => (5 % N, 1 % N, 3 % N, 7 % N, 15 % N)
  | (n + 1) => step N (win N n)

def iter (N : ℕ) : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ → ℕ × ℕ × ℕ × ℕ × ℕ
  | 0, t => t
  | (k + 1), t => iter N k (step N t)

theorem win_add (N a k : ℕ) : win N (a + k) = iter N k (win N a) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    rw [show a + (k + 1) = (a + 1) + k by ring, ih (a + 1)]
    rfl

theorem win_spec (N n : ℕ) :
    win N n = (s n % N, s (n + 1) % N, s (n + 2) % N, s (n + 3) % N, s (n + 4) % N) := by
  induction n with
  | zero => simp [win, s]
  | succ n ih =>
    rw [win, ih, step]
    simp only [Prod.mk.injEq, true_and]
    rw [show n + 1 + 4 = n + 5 by ring, s_succ5]
    exact ((((Nat.mod_modEq _ N).add (Nat.mod_modEq _ N)).add (Nat.mod_modEq _ N)).add
      (Nat.mod_modEq _ N)).add (Nat.mod_modEq _ N)

theorem per_iff_win (N P : ℕ) : Per N P ↔ win N P = win N 0 := by
  rw [win_spec, win_spec]
  simp only [Prod.mk.injEq, zero_add]
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    simp only [Nat.ModEq, zero_add] at h0 h1 h2 h3 h4
    rw [add_comm 1 P] at h1
    rw [add_comm 2 P] at h2
    rw [add_comm 3 P] at h3
    rw [add_comm 4 P] at h4
    exact ⟨h0, h1, h2, h3, h4⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩
    apply per_of_init
    intro i hi
    interval_cases i
    · simpa [Nat.ModEq] using h0
    · simpa [Nat.ModEq, add_comm] using h1
    · simpa [Nat.ModEq, add_comm] using h2
    · simpa [Nat.ModEq, add_comm] using h3
    · simpa [Nat.ModEq, add_comm] using h4

/-! ## Existence of a period (pigeonhole) -/

theorem back {N m m' : ℕ} (h : ∀ t < 5, s (m + 1 + t) ≡ s (m' + 1 + t) [MOD N]) :
    ∀ t < 5, s (m + t) ≡ s (m' + t) [MOD N] := by
  intro t ht
  rcases Nat.eq_zero_or_pos t with rfl | htp
  · have e : ∀ x, s (x + 1 + 4) = s (x + 0) +
        (s (x + 1 + 0) + s (x + 1 + 1) + s (x + 1 + 2) + s (x + 1 + 3)) := by
      intro x
      rw [show x + 1 + 4 = x + 5 by ring, s_succ5]
      simp only [add_zero, add_assoc]
    have h4 := h 4 (by omega)
    rw [e m, e m'] at h4
    exact Nat.ModEq.add_right_cancel
      ((((h 0 (by omega)).add (h 1 (by omega))).add (h 2 (by omega))).add (h 3 (by omega))) h4
  · have := h (t - 1) (by omega)
    rwa [show m + 1 + (t - 1) = m + t by omega, show m' + 1 + (t - 1) = m' + t by omega] at this

theorem per_of_eq_window {N i j : ℕ} (hij : i < j)
    (hw : ∀ t < 5, s (i + t) ≡ s (j + t) [MOD N]) : Per N (j - i) := by
  have key : ∀ k ≤ i, ∀ t < 5, s (i - k + t) ≡ s (j - k + t) [MOD N] := by
    intro k
    induction k with
    | zero => simpa using hw
    | succ k ih =>
      intro hk
      apply back
      intro t ht
      have := ih (by omega) t ht
      rwa [show i - (k + 1) + 1 = i - k by omega, show j - (k + 1) + 1 = j - k by omega]
  have h0 := key i le_rfl
  apply per_of_init
  intro t ht
  have := (h0 t ht).symm
  rwa [Nat.sub_self, zero_add, add_comm] at this

theorem exists_per {N : ℕ} (hN : 0 < N) : ∃ P, 0 < P ∧ Per N P := by
  let w : ℕ → Fin 5 → Fin N := fun m t => ⟨s (m + t) % N, Nat.mod_lt _ hN⟩
  obtain ⟨i, j, hij, hw⟩ := Finite.exists_ne_map_eq_of_infinite w
  have hw' : ∀ t < 5, s (i + t) ≡ s (j + t) [MOD N] := by
    intro t ht
    have := congrArg (fun g => (g ⟨t, ht⟩ : ℕ)) hw
    simpa [w, Nat.ModEq] using this
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact ⟨j - i, by omega, per_of_eq_window h hw'⟩
  · exact ⟨i - j, by omega, per_of_eq_window h (fun t ht => (hw' t ht).symm)⟩

/-! ## Period algebra -/

theorem per_zero (N : ℕ) : Per N 0 := fun m => by simp [Nat.ModEq.refl]

theorem per_add {N P Q : ℕ} (hP : Per N P) (hQ : Per N Q) : Per N (P + Q) := by
  intro m
  rw [← add_assoc]
  exact (hQ (m + P)).trans (hP m)

theorem per_mul {N P : ℕ} (hP : Per N P) (j : ℕ) : Per N (j * P) := by
  induction j with
  | zero => simpa using per_zero N
  | succ j ih => rw [Nat.succ_mul]; exact per_add ih hP

theorem per_sub {N P Q : ℕ} (hP : Per N P) (hQ : Per N Q) (hle : P ≤ Q) : Per N (Q - P) := by
  intro m
  have h1 := hP (m + (Q - P))
  rw [add_assoc, Nat.sub_add_cancel hle] at h1
  exact h1.symm.trans (hQ m)

theorem per_mod {N P Q : ℕ} (hP : Per N P) (hQ : Per N Q) : Per N (Q % P) := by
  have h := per_sub (per_mul hP (Q / P)) hQ (Nat.div_mul_le_self Q P)
  rwa [show Q - Q / P * P = Q % P by rw [Nat.mod_eq_sub_div_mul]] at h

theorem per_of_dvd {N M P : ℕ} (hNM : N ∣ M) (h : Per M P) : Per N P :=
  fun m => (h m).of_dvd hNM

theorem a_spec {N : ℕ} (hN : 0 < N) : 0 < a N ∧ Per N (a N) :=
  Nat.sInf_mem (exists_per hN)

theorem a_dvd {N P : ℕ} (hN : 0 < N) (hP : Per N P) : a N ∣ P := by
  obtain ⟨hpos, hper⟩ := a_spec hN
  have hm := per_mod hper hP
  by_contra hnd
  have hne : P % a N ≠ 0 := fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0)
  have hle : a N ≤ P % a N := Nat.sInf_le ⟨Nat.pos_of_ne_zero hne, hm⟩
  exact absurd (Nat.mod_lt P hpos) (not_lt.2 hle)

/-! ## Integer recurrence sequences; the pentanacci numbers as a basis -/

/-- The pentanacci numbers A001591 (an auxiliary sequence for the proof). -/
def fib5 : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 1
  | (n + 5) => fib5 n + fib5 (n + 1) + fib5 (n + 2) + fib5 (n + 3) + fib5 (n + 4)

def F (n : ℕ) : ℤ := fib5 n

def LZ (n : ℕ) : ℤ := s n

def RecZ (g : ℕ → ℤ) : Prop :=
  ∀ n, g (n + 5) = g n + g (n + 1) + g (n + 2) + g (n + 3) + g (n + 4)

theorem F_rec : RecZ F := fun n => by
  simp only [F, show fib5 (n + 5) = fib5 n + fib5 (n + 1) + fib5 (n + 2) + fib5 (n + 3)
    + fib5 (n + 4) from rfl]
  push_cast
  ring

theorem LZ_rec : RecZ LZ := fun n => by simp [LZ, s_succ5]

theorem recZ_eq {u v : ℕ → ℤ} (hu : RecZ u) (hv : RecZ v) (h : ∀ i < 5, u i = v i) :
    ∀ n, u n = v n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 5 with hn | hn
    · exact h n hn
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
      rw [hu, hv, ih k (by omega), ih (k + 1) (by omega), ih (k + 2) (by omega),
        ih (k + 3) (by omega), ih (k + 4) (by omega)]

theorem recZ_shiftdiff {g : ℕ → ℤ} (hg : RecZ g) (Q : ℕ) : RecZ (fun n => g (n + Q) - g n) := by
  intro n
  simp only
  rw [show n + 5 + Q = n + Q + 5 by ring, hg (n + Q), hg n, Nat.add_right_comm n Q 1,
    Nat.add_right_comm n Q 2, Nat.add_right_comm n Q 3, Nat.add_right_comm n Q 4]
  ring

theorem recZ_quot {g : ℕ → ℤ} {M : ℤ} (hg : RecZ g) (hM : M ≠ 0) (hd : ∀ n, M ∣ g n) :
    RecZ (fun n => g n / M) := by
  intro n
  apply mul_left_cancel₀ hM
  simp only [mul_add]
  rw [Int.mul_ediv_cancel' (hd _), Int.mul_ediv_cancel' (hd _), Int.mul_ediv_cancel' (hd _),
    Int.mul_ediv_cancel' (hd _), Int.mul_ediv_cancel' (hd _), Int.mul_ediv_cancel' (hd _)]
  exact hg n

def c4 (g : ℕ → ℤ) : ℤ := g 0
def c3 (g : ℕ → ℤ) : ℤ := g 1 - c4 g
def c2 (g : ℕ → ℤ) : ℤ := g 2 - c3 g - 2 * c4 g
def c1 (g : ℕ → ℤ) : ℤ := g 3 - c2 g - 2 * c3 g - 4 * c4 g
def c0 (g : ℕ → ℤ) : ℤ := g 4 - c1 g - 2 * c2 g - 4 * c3 g - 8 * c4 g

theorem F_vals : F 0 = 0 ∧ F 1 = 0 ∧ F 2 = 0 ∧ F 3 = 0 ∧ F 4 = 1 ∧ F 5 = 1 ∧ F 6 = 2 ∧
    F 7 = 4 ∧ F 8 = 8 := by
  simp only [F]
  norm_num [fib5]

/-- Every integer recurrence sequence is an integer combination of shifts of `F`. -/
theorem rep {g : ℕ → ℤ} (hg : RecZ g) (n : ℕ) :
    g n = c0 g * F n + c1 g * F (n + 1) + c2 g * F (n + 2) + c3 g * F (n + 3)
      + c4 g * F (n + 4) := by
  have hF : ∀ m, F (m + 5) = F m + F (m + 1) + F (m + 2) + F (m + 3) + F (m + 4) := F_rec
  refine recZ_eq (v := fun m => c0 g * F m + c1 g * F (m + 1) + c2 g * F (m + 2)
      + c3 g * F (m + 3) + c4 g * F (m + 4)) hg ?_ ?_ n
  · intro m
    beta_reduce
    have e1 := hF (m + 1)
    have e2 := hF (m + 2)
    have e3 := hF (m + 3)
    have e4 := hF (m + 4)
    have e0 := hF m
    ring_nf at e0 e1 e2 e3 e4 ⊢
    linear_combination c0 g * e0 + c1 g * e1 + c2 g * e2 + c3 g * e3 + c4 g * e4
  · intro i hi
    obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8⟩ := F_vals
    interval_cases i <;> simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, c0, c1, c2, c3, c4] <;> ring

/-- `9584 * F` is an integer combination of shifts of the Lucas sequence. -/
theorem F_of_L (n : ℕ) : 9584 * F n = 72 * LZ n + 2032 * LZ (n + 1) - 1584 * LZ (n + 2)
    + 80 * LZ (n + 3) + 120 * LZ (n + 4) := by
  have hL : ∀ m, LZ (m + 5) = LZ m + LZ (m + 1) + LZ (m + 2) + LZ (m + 3) + LZ (m + 4) := LZ_rec
  refine recZ_eq (u := fun m => 9584 * F m) (v := fun m => 72 * LZ m + 2032 * LZ (m + 1)
      - 1584 * LZ (m + 2) + 80 * LZ (m + 3) + 120 * LZ (m + 4)) ?_ ?_ ?_ n
  · intro m
    beta_reduce
    rw [F_rec m]
    ring
  · intro m
    beta_reduce
    have e1 := hL (m + 1)
    have e2 := hL (m + 2)
    have e3 := hL (m + 3)
    have e4 := hL (m + 4)
    have e0 := hL m
    ring_nf at e0 e1 e2 e3 e4 ⊢
    linear_combination 72 * e0 + 2032 * e1 - 1584 * e2 + 80 * e3 + 120 * e4
  · intro i hi
    obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8⟩ := F_vals
    interval_cases i <;> simp [v0, v1, v2, v3, v4, LZ, s]

def PerZ (M : ℤ) (Q : ℕ) : Prop := ∀ n, M ∣ LZ (n + Q) - LZ n

theorem per_iff_perZ (N Q : ℕ) : Per N Q ↔ PerZ (N : ℤ) Q := by
  unfold Per PerZ
  refine forall_congr' fun n => ?_
  rw [Nat.ModEq.comm, Nat.modEq_iff_dvd]
  rfl

theorem spanF {M : ℤ} {Q : ℕ} (hQ : PerZ M Q) (m : ℕ) : M ∣ 9584 * (F (m + Q) - F m) := by
  rw [mul_sub, F_of_L, F_of_L]
  have d0 := hQ m
  have d1 := hQ (m + 1)
  have d2 := hQ (m + 2)
  have d3 := hQ (m + 3)
  have d4 := hQ (m + 4)
  rw [Nat.add_right_comm m 1 Q] at d1
  rw [Nat.add_right_comm m 2 Q] at d2
  rw [Nat.add_right_comm m 3 Q] at d3
  rw [Nat.add_right_comm m 4 Q] at d4
  have : 72 * LZ (m + Q) + 2032 * LZ (m + Q + 1) - 1584 * LZ (m + Q + 2) + 80 * LZ (m + Q + 3)
      + 120 * LZ (m + Q + 4) - (72 * LZ m + 2032 * LZ (m + 1) - 1584 * LZ (m + 2)
      + 80 * LZ (m + 3) + 120 * LZ (m + 4))
      = 72 * (LZ (m + Q) - LZ m) + 2032 * (LZ (m + Q + 1) - LZ (m + 1))
        - 1584 * (LZ (m + Q + 2) - LZ (m + 2)) + 80 * (LZ (m + Q + 3) - LZ (m + 3))
        + 120 * (LZ (m + Q + 4) - LZ (m + 4)) := by ring
  rw [this]
  exact (((((d0.mul_left _).add (d1.mul_left _)).sub (d2.mul_left _)).add
    (d3.mul_left _)).add (d4.mul_left _))

/-- A period of the Lucas sequence modulo `M` is a period modulo `M` of `9584 * g` for every
integer recurrence sequence `g`. -/
theorem spanL {g : ℕ → ℤ} (hg : RecZ g) {M : ℤ} {Q : ℕ} (hQ : PerZ M Q) (n : ℕ) :
    M ∣ 9584 * (g (n + Q) - g n) := by
  rw [rep hg (n + Q), rep hg n]
  have d0 := spanF hQ n
  have d1 := spanF hQ (n + 1)
  have d2 := spanF hQ (n + 2)
  have d3 := spanF hQ (n + 3)
  have d4 := spanF hQ (n + 4)
  rw [Nat.add_right_comm n 1 Q] at d1
  rw [Nat.add_right_comm n 2 Q] at d2
  rw [Nat.add_right_comm n 3 Q] at d3
  rw [Nat.add_right_comm n 4 Q] at d4
  have : 9584 * (c0 g * F (n + Q) + c1 g * F (n + Q + 1) + c2 g * F (n + Q + 2)
      + c3 g * F (n + Q + 3) + c4 g * F (n + Q + 4) - (c0 g * F n + c1 g * F (n + 1)
      + c2 g * F (n + 2) + c3 g * F (n + 3) + c4 g * F (n + 4)))
      = c0 g * (9584 * (F (n + Q) - F n)) + c1 g * (9584 * (F (n + Q + 1) - F (n + 1)))
        + c2 g * (9584 * (F (n + Q + 2) - F (n + 2))) + c3 g * (9584 * (F (n + Q + 3) - F (n + 3)))
        + c4 g * (9584 * (F (n + Q + 4) - F (n + 4))) := by ring
  rw [this]
  exact ((((d0.mul_left _).add (d1.mul_left _)).add (d2.mul_left _)).add
    (d3.mul_left _)).add (d4.mul_left _)

theorem perZ_mul {M : ℤ} {Q : ℕ} (hQ : PerZ M Q) (j : ℕ) : PerZ M (j * Q) := by
  induction j with
  | zero => intro n; simp
  | succ j ih =>
    intro n
    have h1 := hQ (n + j * Q)
    have h2 := ih n
    rw [Nat.succ_mul, ← add_assoc]
    have : LZ (n + j * Q + Q) - LZ n
        = (LZ (n + j * Q + Q) - LZ (n + j * Q)) + (LZ (n + j * Q) - LZ n) := by ring
    rw [this]
    exact h1.add h2

/-! ## The lifting lemma, with a loss of `k - r` powers of `p` coming from `9584` -/

theorem liftL {p k r Q : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hloss : ∀ x : ℤ, (p : ℤ) ^ k ∣ 9584 * x → (p : ℤ) ^ r ∣ x)
    (hcond : (p : ℤ) ^ (k + 2) ∣ (p : ℤ) ^ (k + r) * ∑ i ∈ Finset.range p, (i : ℤ))
    (hQ : PerZ ((p : ℤ) ^ k) Q) (hnot : ¬ PerZ ((p : ℤ) ^ (k + 1)) Q) :
    PerZ ((p : ℤ) ^ (k + 1)) (p * Q) ∧ ¬ PerZ ((p : ℤ) ^ (k + 2)) (p * Q) := by
  set q : ℤ := (p : ℤ) with hqdef
  have hq0 : q ≠ 0 := by simp [q, hp.ne_zero]
  have hqk : q ^ k ≠ 0 := pow_ne_zero k hq0
  have hqr : q ^ r ≠ 0 := pow_ne_zero r hq0
  have hGrec : RecZ (fun n => LZ (n + Q) - LZ n) := recZ_shiftdiff LZ_rec Q
  set h : ℕ → ℤ := fun n => (LZ (n + Q) - LZ n) / q ^ k with hhdef
  have hG : ∀ n, LZ (n + Q) - LZ n = q ^ k * h n := fun n => (Int.mul_ediv_cancel' (hQ n)).symm
  have hh : RecZ h := recZ_quot hGrec hqk hQ
  have hDrec : RecZ (fun n => h (n + Q) - h n) := recZ_shiftdiff hh Q
  have hDd : ∀ n, q ^ r ∣ h (n + Q) - h n := fun n => hloss _ (spanL hh hQ n)
  set h' : ℕ → ℤ := fun n => (h (n + Q) - h n) / q ^ r with hh'def
  have hD : ∀ n, h (n + Q) - h n = q ^ r * h' n := fun n => (Int.mul_ediv_cancel' (hDd n)).symm
  have hh' : RecZ h' := recZ_quot hDrec hqr hDd
  have hh'per : ∀ i n, q ^ r ∣ h' (n + i * Q) - h' n :=
    fun i n => hloss _ (spanL hh' (perZ_mul hQ i) n)
  have claimA : ∀ j n, q ^ (2 * r) ∣ h (n + j * Q) - h n - j * q ^ r * h' n := by
    intro j
    induction j with
    | zero => intro n; simp
    | succ j ih =>
      intro n
      have e : h (n + (j + 1) * Q) = h (n + j * Q) + q ^ r * h' (n + j * Q) := by
        rw [← hD, Nat.succ_mul, ← add_assoc]
        ring
      rw [e]
      have : h (n + j * Q) + q ^ r * h' (n + j * Q) - h n - ((j + 1 : ℕ) : ℤ) * q ^ r * h' n
          = (h (n + j * Q) - h n - j * q ^ r * h' n) + q ^ r * (h' (n + j * Q) - h' n) := by
        push_cast
        ring
      rw [this]
      refine (ih n).add ?_
      rw [two_mul, pow_add]
      exact mul_dvd_mul_left _ (hh'per j n)
  have claimB : ∀ j n, LZ (n + j * Q) - LZ n = q ^ k * ∑ i ∈ Finset.range j, h (n + i * Q) := by
    intro j
    induction j with
    | zero => intro n; simp
    | succ j ih =>
      intro n
      rw [Finset.sum_range_succ, mul_add, ← ih n, ← hG (n + j * Q), Nat.succ_mul, ← add_assoc]
      ring
  have key : ∀ n, q ^ (k + 2) ∣ LZ (n + p * Q) - LZ n - q ^ (k + 1) * h n := by
    intro n
    have hsum : ∑ i ∈ Finset.range p, (h (n + i * Q) - h n - i * q ^ r * h' n)
        = ∑ i ∈ Finset.range p, h (n + i * Q) - p * h n
          - q ^ r * (∑ i ∈ Finset.range p, (i : ℤ)) * h' n := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        Finset.mul_sum, Finset.sum_mul]
      simp only [nsmul_eq_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => by ring
    have hE : q ^ (2 * r) ∣ ∑ i ∈ Finset.range p, (h (n + i * Q) - h n - i * q ^ r * h' n) :=
      Finset.dvd_sum fun i _ => claimA i n
    obtain ⟨E, hEq⟩ := hE
    have hF := claimB p n
    have hexp : LZ (n + p * Q) - LZ n - q ^ (k + 1) * h n
        = q ^ (k + r) * (∑ i ∈ Finset.range p, (i : ℤ)) * h' n + q ^ (k + 2 * r) * E := by
      rw [hF]
      have : ∑ i ∈ Finset.range p, h (n + i * Q)
          = q ^ (2 * r) * E + p * h n + q ^ r * (∑ i ∈ Finset.range p, (i : ℤ)) * h' n := by
        rw [← hEq, hsum]
        ring
      rw [this, hqdef]
      ring
    rw [hexp]
    refine dvd_add (Dvd.dvd.mul_right hcond _) (Dvd.dvd.mul_right ?_ _)
    exact pow_dvd_pow q (by omega)
  refine ⟨?_, ?_⟩
  · intro n
    have h1 := key n
    have h2 : q ^ (k + 1) ∣ q ^ (k + 2) := pow_dvd_pow q (by omega)
    have := (h2.trans h1).add (dvd_mul_right (q ^ (k + 1)) (h n))
    simpa using this
  · intro hall
    apply hnot
    intro n
    by_contra hn
    have hnq : ¬ q ∣ h n := by
      rintro ⟨c, hc⟩
      apply hn
      rw [hG n, hc, pow_succ]
      exact ⟨c, by ring⟩
    have h1 := key n
    have h2 := hall n
    have h3 : q ^ (k + 2) ∣ q ^ (k + 1) * h n := by
      have := dvd_sub h2 h1
      simpa using this
    rw [pow_succ q (k + 1)] at h3
    exact hnq ((mul_dvd_mul_iff_left (pow_ne_zero _ hq0)).1 h3)

theorem liftPer {p k r : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hloss : ∀ x : ℤ, (p : ℤ) ^ k ∣ 9584 * x → (p : ℤ) ^ r ∣ x)
    (hcond : (p : ℤ) ^ (k + 2) ∣ (p : ℤ) ^ (k + r) * ∑ i ∈ Finset.range p, (i : ℤ))
    (Q : ℕ) (hQ : Per (p ^ k) Q) (hnot : ¬ Per (p ^ (k + 1)) Q) :
    Per (p ^ (k + 1)) (p * Q) ∧ ¬ Per (p ^ (k + 2)) (p * Q) := by
  rw [per_iff_perZ] at hQ hnot ⊢
  rw [per_iff_perZ]
  push_cast at hQ hnot ⊢
  exact liftL hp hr hloss hcond hQ hnot

/-! ## The tower -/

theorem tower {p : ℕ} (hp : p.Prime) (k0 : ℕ)
    (hlift : ∀ k, k0 ≤ k → ∀ Q, Per (p ^ k) Q → ¬ Per (p ^ (k + 1)) Q →
      Per (p ^ (k + 1)) (p * Q) ∧ ¬ Per (p ^ (k + 2)) (p * Q))
    (Q : ℕ) (hQa : a (p ^ k0) = Q) (hnot : ¬ Per (p ^ (k0 + 1)) Q) :
    ∀ j, a (p ^ (k0 + j)) = p ^ j * Q ∧ ¬ Per (p ^ (k0 + j + 1)) (p ^ j * Q) := by
  have hp0 : 0 < p := hp.pos
  intro j
  induction j with
  | zero => simpa using ⟨hQa, hnot⟩
  | succ j ih =>
    obtain ⟨ha, hn⟩ := ih
    set k := k0 + j with hkdef
    have hpk : 0 < p ^ k := pow_pos hp0 k
    have hper : Per (p ^ k) (p ^ j * Q) := by rw [← ha]; exact (a_spec hpk).2
    obtain ⟨hl1', hl2'⟩ := hlift k (by omega) _ hper hn
    have hpk1 : 0 < p ^ (k + 1) := pow_pos hp0 _
    have hd1 : a (p ^ (k + 1)) ∣ p * (p ^ j * Q) := a_dvd hpk1 hl1'
    have hd2 : p ^ j * Q ∣ a (p ^ (k + 1)) := by
      rw [← ha]
      exact a_dvd hpk (per_of_dvd (pow_dvd_pow p (by omega)) (a_spec hpk1).2)
    obtain ⟨d, hd⟩ := hd2
    have hQpos : 0 < p ^ j * Q := by rw [← ha]; exact (a_spec hpk).1
    have hdp : d ∣ p := by
      rw [hd, mul_comm p] at hd1
      exact (Nat.mul_dvd_mul_iff_left hQpos).1 hd1
    rcases (Nat.dvd_prime hp).1 hdp with hd1' | hdp'
    · exfalso
      apply hn
      have := (a_spec hpk1).2
      rwa [hd, hd1', mul_one] at this
    · rw [hdp'] at hd
      refine ⟨?_, ?_⟩
      · rw [show k0 + (j + 1) = k + 1 by omega, hd, pow_succ]; ring
      · rw [show k0 + (j + 1) + 1 = k + 1 + 1 by omega,
          show p ^ (j + 1) * Q = p * (p ^ j * Q) by ring]
        exact hl2'

/-! ## The loss of powers of `p` in `9584 = 2^4 * 599` -/

theorem loss_coprime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h599 : p ≠ 599) (k : ℕ) :
    ∀ x : ℤ, (p : ℤ) ^ k ∣ 9584 * x → (p : ℤ) ^ k ∣ x := by
  have hnd : ¬ p ∣ 9584 := by
    intro h
    rw [show (9584 : ℕ) = 2 ^ 4 * 599 by norm_num] at h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
    · exact h599 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)
  have hcop : Nat.Coprime (p ^ k) 9584 :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
  have hc : IsCoprime ((p : ℤ) ^ k) 9584 := by
    have := Nat.isCoprime_iff_coprime.2 hcop
    push_cast at this
    exact this
  intro x hx
  exact hc.dvd_of_dvd_mul_left hx

theorem loss_two {k : ℕ} (hk : 4 ≤ k) :
    ∀ x : ℤ, ((2 : ℕ) : ℤ) ^ k ∣ 9584 * x → ((2 : ℕ) : ℤ) ^ (k - 4) ∣ x := by
  intro x hx
  push_cast at hx ⊢
  have e1 : (2 : ℤ) ^ k = 2 ^ 4 * 2 ^ (k - 4) := by rw [← pow_add]; congr 1; omega
  rw [e1, show (9584 : ℤ) * x = 2 ^ 4 * (599 * x) by ring] at hx
  have h2 := (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ^ 4 ≠ 0)).1 hx
  have hc : IsCoprime ((2 : ℤ) ^ (k - 4)) 599 := by
    apply IsCoprime.pow_left
    rw [Int.isCoprime_iff_gcd_eq_one]
    rfl
  exact hc.dvd_of_dvd_mul_left h2

theorem loss_599 {k : ℕ} (hk : 1 ≤ k) :
    ∀ x : ℤ, ((599 : ℕ) : ℤ) ^ k ∣ 9584 * x → ((599 : ℕ) : ℤ) ^ (k - 1) ∣ x := by
  intro x hx
  push_cast at hx ⊢
  have e1 : (599 : ℤ) ^ k = 599 * 599 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  rw [e1, show (9584 : ℤ) * x = 599 * (16 * x) by ring] at hx
  have h2 := (mul_dvd_mul_iff_left (by norm_num : (599 : ℤ) ≠ 0)).1 hx
  have hc : IsCoprime ((599 : ℤ) ^ (k - 1)) 16 := by
    apply IsCoprime.pow_left
    rw [Int.isCoprime_iff_gcd_eq_one]
    rfl
  exact hc.dvd_of_dvd_mul_left h2

/-! ## Sums of `i` over `i < p` -/

theorem sum_range_two : ∑ i ∈ Finset.range 2, (i : ℤ) = 1 := by decide

theorem dvd_sum_range_odd {p : ℕ} (hodd : Odd p) : (p : ℤ) ∣ ∑ i ∈ Finset.range p, (i : ℤ) := by
  have h2 := Finset.sum_range_id_mul_two p
  obtain ⟨t, ht⟩ := hodd
  have hS : ∑ i ∈ Finset.range p, i = p * t := by
    have : (∑ i ∈ Finset.range p, i) * 2 = (p * t) * 2 := by
      rw [h2, ht]; simp; ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) this
  refine ⟨t, ?_⟩
  have := congrArg (fun x : ℕ => (x : ℤ)) hS
  push_cast at this
  exact this

/-! ## Concrete computations -/

theorem a4 : a 4 = 6 := by
  have hP : Per 4 6 := (per_iff_win _ _).2 (by decide)
  have hd : a 4 ∣ 6 := a_dvd (by norm_num) hP
  obtain ⟨_, hper⟩ := a_spec (N := 4) (by norm_num)
  have hm : a 4 ∈ Nat.divisors 6 := Nat.mem_divisors.2 ⟨hd, by norm_num⟩
  rw [show Nat.divisors 6 = {1, 2, 3, 6} by decide] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h | h <;> rw [h] at hper ⊢
  all_goals first | rfl | exact absurd ((per_iff_win _ _).1 hper) (by decide)

theorem a8 : a 8 = 12 := by
  have hP : Per 8 12 := (per_iff_win _ _).2 (by decide)
  have hd : a 8 ∣ 12 := a_dvd (by norm_num) hP
  obtain ⟨_, hper⟩ := a_spec (N := 8) (by norm_num)
  have hm : a 8 ∈ Nat.divisors 12 := Nat.mem_divisors.2 ⟨hd, by norm_num⟩
  rw [show Nat.divisors 12 = {1, 2, 3, 4, 6, 12} by decide] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h | h | h | h <;> rw [h] at hper ⊢
  all_goals first | rfl | exact absurd ((per_iff_win _ _).1 hper) (by decide)

theorem a16 : a 16 = 24 := by
  have hP : Per 16 24 := (per_iff_win _ _).2 (by decide)
  have hd : a 16 ∣ 24 := a_dvd (by norm_num) hP
  obtain ⟨_, hper⟩ := a_spec (N := 16) (by norm_num)
  have hm : a 16 ∈ Nat.divisors 24 := Nat.mem_divisors.2 ⟨hd, by norm_num⟩
  rw [show Nat.divisors 24 = {1, 2, 3, 4, 6, 8, 12, 24} by decide] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h | h | h | h | h | h <;> rw [h] at hper ⊢
  all_goals first | rfl | exact absurd ((per_iff_win _ _).1 hper) (by decide)

theorem a32 : a 32 = 48 := by
  have hP : Per 32 48 := (per_iff_win _ _).2 (by decide)
  have hd : a 32 ∣ 48 := a_dvd (by norm_num) hP
  obtain ⟨_, hper⟩ := a_spec (N := 32) (by norm_num)
  have hm : a 32 ∈ Nat.divisors 48 := Nat.mem_divisors.2 ⟨hd, by norm_num⟩
  rw [show Nat.divisors 48 = {1, 2, 3, 4, 6, 8, 12, 16, 24, 48} by decide] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h <;> rw [h] at hper ⊢
  all_goals first | rfl | exact absurd ((per_iff_win _ _).1 hper) (by decide)

theorem a64 : a 64 = 96 := by
  have hP : Per 64 96 := (per_iff_win _ _).2 (by decide)
  have hd : a 64 ∣ 96 := a_dvd (by norm_num) hP
  obtain ⟨_, hper⟩ := a_spec (N := 64) (by norm_num)
  have hm : a 64 ∈ Nat.divisors 96 := Nat.mem_divisors.2 ⟨hd, by norm_num⟩
  rw [show Nat.divisors 96 = {1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 96} by decide] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] at hper ⊢
  all_goals first | rfl | exact absurd ((per_iff_win _ _).1 hper) (by decide)

theorem not_per_128_96 : ¬ Per 128 96 := fun h => absurd ((per_iff_win _ _).1 h) (by decide)

set_option maxRecDepth 100000 in
theorem a5 : a 5 = 781 := by
  have hP : Per 5 781 := (per_iff_win _ _).2 (by decide)
  have hd : a 5 ∣ 781 := a_dvd (by norm_num) hP
  obtain ⟨_, hper⟩ := a_spec (N := 5) (by norm_num)
  have hm : a 5 ∈ Nat.divisors 781 := Nat.mem_divisors.2 ⟨hd, by norm_num⟩
  rw [show Nat.divisors 781 = {1, 11, 71, 781} by decide] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h | h <;> rw [h] at hper ⊢
  all_goals first | rfl | exact absurd ((per_iff_win _ _).1 hper) (by decide)

set_option maxRecDepth 100000 in
theorem not_per_25_781 : ¬ Per 25 781 := fun h => absurd ((per_iff_win _ _).1 h) (by decide)

set_option maxRecDepth 100000 in
theorem a599 : a 599 = 598 := by
  have hP : Per 599 598 := (per_iff_win _ _).2 (by decide)
  have hd : a 599 ∣ 598 := a_dvd (by norm_num) hP
  obtain ⟨_, hper⟩ := a_spec (N := 599) (by norm_num)
  have hm : a 599 ∈ Nat.divisors 598 := Nat.mem_divisors.2 ⟨hd, by norm_num⟩
  rw [show Nat.divisors 598 = {1, 2, 13, 23, 26, 46, 299, 598} by decide] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h | h | h | h | h | h <;> rw [h] at hper ⊢
  all_goals first | rfl | exact absurd ((per_iff_win _ _).1 hper) (by decide)

set_option maxRecDepth 100000 in
theorem not_per_599sq_598 : ¬ Per 358801 598 :=
  fun h => absurd ((per_iff_win _ _).1 h) (by decide)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch2_0 : win 358801 20000 = (323024, 264261, 358323, 324165, 335461) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch2_1 : iter 358801 20000 (323024, 264261, 358323, 324165, 335461) = (171111, 95162, 72564, 344050, 88808) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch2_2 : iter 358801 20000 (171111, 95162, 72564, 344050, 88808) = (121295, 207688, 87972, 40864, 227042) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch2_3 : iter 358801 20000 (121295, 207688, 87972, 40864, 227042) = (306446, 85380, 103927, 37076, 58594) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch2_4 : iter 358801 20000 (306446, 85380, 103927, 37076, 58594) = (19728, 217590, 283294, 33142, 53571) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch2_5 : iter 358801 20000 (19728, 217590, 283294, 33142, 53571) = (5623, 337395, 195614, 41569, 337354) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch2_6 : iter 358801 20000 (5623, 337395, 195614, 41569, 337354) = (135642, 340263, 346731, 225143, 348156) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch2_7 : iter 358801 20000 (135642, 340263, 346731, 225143, 348156) = (238343, 239396, 60382, 233065, 142315) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch2_8 : iter 358801 20000 (238343, 239396, 60382, 233065, 142315) = (253979, 175514, 336054, 61129, 37794) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch2_9 : iter 358801 20000 (253979, 175514, 336054, 61129, 37794) = (121, 30056, 230037, 49032, 351877) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch2_10 : iter 358801 20000 (121, 30056, 230037, 49032, 351877) = (139053, 155365, 55863, 84043, 2965) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch2_11 : iter 358801 20000 (139053, 155365, 55863, 84043, 2965) = (24478, 98368, 346842, 229022, 178613) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch2_12 : iter 358801 20000 (24478, 98368, 346842, 229022, 178613) = (188985, 279671, 32238, 302106, 304355) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch2_13 : iter 358801 20000 (188985, 279671, 32238, 302106, 304355) = (298269, 13974, 163188, 246128, 171830) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch2_14 : iter 358801 20000 (298269, 13974, 163188, 246128, 171830) = (2736, 154780, 167837, 2882, 208593) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch2_15 : iter 358801 20000 (2736, 154780, 167837, 2882, 208593) = (346132, 98754, 64230, 197935, 43390) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch2_16 : iter 358801 20000 (346132, 98754, 64230, 197935, 43390) = (186172, 170170, 238155, 268378, 272656) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch2_17 : iter 358801 18202 (186172, 170170, 238155, 268378, 272656) = (5, 1, 3, 7, 15) := by decide

theorem per_599sq : Per 358801 358202 := by
  rw [per_iff_win]
  have c0 : win 358801 20000 = (323024, 264261, 358323, 324165, 335461) := ch2_0
  have c1 : win 358801 40000 = (171111, 95162, 72564, 344050, 88808) := by
    rw [show (40000 : ℕ) = 20000 + 20000 from rfl, win_add, c0]
    exact ch2_1
  have c2 : win 358801 60000 = (121295, 207688, 87972, 40864, 227042) := by
    rw [show (60000 : ℕ) = 40000 + 20000 from rfl, win_add, c1]
    exact ch2_2
  have c3 : win 358801 80000 = (306446, 85380, 103927, 37076, 58594) := by
    rw [show (80000 : ℕ) = 60000 + 20000 from rfl, win_add, c2]
    exact ch2_3
  have c4 : win 358801 100000 = (19728, 217590, 283294, 33142, 53571) := by
    rw [show (100000 : ℕ) = 80000 + 20000 from rfl, win_add, c3]
    exact ch2_4
  have c5 : win 358801 120000 = (5623, 337395, 195614, 41569, 337354) := by
    rw [show (120000 : ℕ) = 100000 + 20000 from rfl, win_add, c4]
    exact ch2_5
  have c6 : win 358801 140000 = (135642, 340263, 346731, 225143, 348156) := by
    rw [show (140000 : ℕ) = 120000 + 20000 from rfl, win_add, c5]
    exact ch2_6
  have c7 : win 358801 160000 = (238343, 239396, 60382, 233065, 142315) := by
    rw [show (160000 : ℕ) = 140000 + 20000 from rfl, win_add, c6]
    exact ch2_7
  have c8 : win 358801 180000 = (253979, 175514, 336054, 61129, 37794) := by
    rw [show (180000 : ℕ) = 160000 + 20000 from rfl, win_add, c7]
    exact ch2_8
  have c9 : win 358801 200000 = (121, 30056, 230037, 49032, 351877) := by
    rw [show (200000 : ℕ) = 180000 + 20000 from rfl, win_add, c8]
    exact ch2_9
  have c10 : win 358801 220000 = (139053, 155365, 55863, 84043, 2965) := by
    rw [show (220000 : ℕ) = 200000 + 20000 from rfl, win_add, c9]
    exact ch2_10
  have c11 : win 358801 240000 = (24478, 98368, 346842, 229022, 178613) := by
    rw [show (240000 : ℕ) = 220000 + 20000 from rfl, win_add, c10]
    exact ch2_11
  have c12 : win 358801 260000 = (188985, 279671, 32238, 302106, 304355) := by
    rw [show (260000 : ℕ) = 240000 + 20000 from rfl, win_add, c11]
    exact ch2_12
  have c13 : win 358801 280000 = (298269, 13974, 163188, 246128, 171830) := by
    rw [show (280000 : ℕ) = 260000 + 20000 from rfl, win_add, c12]
    exact ch2_13
  have c14 : win 358801 300000 = (2736, 154780, 167837, 2882, 208593) := by
    rw [show (300000 : ℕ) = 280000 + 20000 from rfl, win_add, c13]
    exact ch2_14
  have c15 : win 358801 320000 = (346132, 98754, 64230, 197935, 43390) := by
    rw [show (320000 : ℕ) = 300000 + 20000 from rfl, win_add, c14]
    exact ch2_15
  have c16 : win 358801 340000 = (186172, 170170, 238155, 268378, 272656) := by
    rw [show (340000 : ℕ) = 320000 + 20000 from rfl, win_add, c15]
    exact ch2_16
  have c17 : win 358801 358202 = (5, 1, 3, 7, 15) := by
    rw [show (358202 : ℕ) = 340000 + 18202 from rfl, win_add, c16]
    exact ch2_17
  rw [c17]
  decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch3_0 : win 214921799 20000 = (21133482, 122615402, 153566350, 182236272, 185835578) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch3_1 : iter 214921799 20000 (21133482, 122615402, 153566350, 182236272, 185835578) = (166654775, 164426020, 88696411, 128436007, 137509591) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch3_2 : iter 214921799 20000 (166654775, 164426020, 88696411, 128436007, 137509591) = (24878564, 189295815, 171236049, 204198633, 95668108) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch3_3 : iter 214921799 20000 (24878564, 189295815, 171236049, 204198633, 95668108) = (122657587, 211419169, 178428024, 31970365, 137838178) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch3_4 : iter 214921799 20000 (122657587, 211419169, 178428024, 31970365, 137838178) = (50610669, 32868481, 4230105, 137095124, 139985961) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch3_5 : iter 214921799 20000 (50610669, 32868481, 4230105, 137095124, 139985961) = (136350003, 111206904, 179954915, 137821153, 337354) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch3_6 : iter 214921799 20000 (136350003, 111206904, 179954915, 137821153, 337354) = (143297241, 192657599, 1781935, 181778449, 121264093) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch3_7 : iter 214921799 20000 (143297241, 192657599, 1781935, 181778449, 121264093) = (93885404, 87428039, 147886394, 112178977, 56832873) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch3_8 : iter 214921799 20000 (93885404, 87428039, 147886394, 112178977, 56832873) = (206205753, 12015947, 59538219, 61129, 125259343) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch3_9 : iter 214921799 20000 (206205753, 12015947, 59538219, 61129, 125259343) = (8252544, 43803778, 52973784, 212100423, 137772660) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch3_10 : iter 214921799 20000 (8252544, 43803778, 52973784, 212100423, 137772660) = (77640069, 55410719, 184120776, 155444876, 151058186) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch3_11 : iter 214921799 20000 (77640069, 55410719, 184120776, 155444876, 151058186) = (28010956, 213226162, 148172854, 121503760, 204336382) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch3_12 : iter 214921799 20000 (28010956, 213226162, 148172854, 121503760, 204336382) = (148732599, 124424817, 49905577, 127676461, 212714547) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch3_13 : iter 214921799 20000 (148732599, 124424817, 49905577, 127676461, 212714547) = (95021733, 65315756, 134713563, 214809126, 45739557) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch3_14 : iter 214921799 20000 (95021733, 65315756, 134713563, 214809126, 45739557) = (6102353, 89855030, 162704690, 139217670, 85244430) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch3_15 : iter 214921799 20000 (6102353, 89855030, 162704690, 139217670, 85244430) = (44837456, 95181019, 190946362, 29978418, 192001925) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch3_16 : iter 214921799 20000 (44837456, 95181019, 190946362, 29978418, 192001925) = (88092417, 154095799, 38629862, 92839036, 90331707) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem ch3_17 : iter 214921799 18202 (88092417, 154095799, 38629862, 92839036, 90331707) = (5, 130244764, 198775757, 208463388, 30498100) := by decide

theorem not_per_599cube : ¬ Per 214921799 358202 := by
  rw [per_iff_win]
  intro hw
  have c0 : win 214921799 20000 = (21133482, 122615402, 153566350, 182236272, 185835578) := ch3_0
  have c1 : win 214921799 40000 = (166654775, 164426020, 88696411, 128436007, 137509591) := by
    rw [show (40000 : ℕ) = 20000 + 20000 from rfl, win_add, c0]
    exact ch3_1
  have c2 : win 214921799 60000 = (24878564, 189295815, 171236049, 204198633, 95668108) := by
    rw [show (60000 : ℕ) = 40000 + 20000 from rfl, win_add, c1]
    exact ch3_2
  have c3 : win 214921799 80000 = (122657587, 211419169, 178428024, 31970365, 137838178) := by
    rw [show (80000 : ℕ) = 60000 + 20000 from rfl, win_add, c2]
    exact ch3_3
  have c4 : win 214921799 100000 = (50610669, 32868481, 4230105, 137095124, 139985961) := by
    rw [show (100000 : ℕ) = 80000 + 20000 from rfl, win_add, c3]
    exact ch3_4
  have c5 : win 214921799 120000 = (136350003, 111206904, 179954915, 137821153, 337354) := by
    rw [show (120000 : ℕ) = 100000 + 20000 from rfl, win_add, c4]
    exact ch3_5
  have c6 : win 214921799 140000 = (143297241, 192657599, 1781935, 181778449, 121264093) := by
    rw [show (140000 : ℕ) = 120000 + 20000 from rfl, win_add, c5]
    exact ch3_6
  have c7 : win 214921799 160000 = (93885404, 87428039, 147886394, 112178977, 56832873) := by
    rw [show (160000 : ℕ) = 140000 + 20000 from rfl, win_add, c6]
    exact ch3_7
  have c8 : win 214921799 180000 = (206205753, 12015947, 59538219, 61129, 125259343) := by
    rw [show (180000 : ℕ) = 160000 + 20000 from rfl, win_add, c7]
    exact ch3_8
  have c9 : win 214921799 200000 = (8252544, 43803778, 52973784, 212100423, 137772660) := by
    rw [show (200000 : ℕ) = 180000 + 20000 from rfl, win_add, c8]
    exact ch3_9
  have c10 : win 214921799 220000 = (77640069, 55410719, 184120776, 155444876, 151058186) := by
    rw [show (220000 : ℕ) = 200000 + 20000 from rfl, win_add, c9]
    exact ch3_10
  have c11 : win 214921799 240000 = (28010956, 213226162, 148172854, 121503760, 204336382) := by
    rw [show (240000 : ℕ) = 220000 + 20000 from rfl, win_add, c10]
    exact ch3_11
  have c12 : win 214921799 260000 = (148732599, 124424817, 49905577, 127676461, 212714547) := by
    rw [show (260000 : ℕ) = 240000 + 20000 from rfl, win_add, c11]
    exact ch3_12
  have c13 : win 214921799 280000 = (95021733, 65315756, 134713563, 214809126, 45739557) := by
    rw [show (280000 : ℕ) = 260000 + 20000 from rfl, win_add, c12]
    exact ch3_13
  have c14 : win 214921799 300000 = (6102353, 89855030, 162704690, 139217670, 85244430) := by
    rw [show (300000 : ℕ) = 280000 + 20000 from rfl, win_add, c13]
    exact ch3_14
  have c15 : win 214921799 320000 = (44837456, 95181019, 190946362, 29978418, 192001925) := by
    rw [show (320000 : ℕ) = 300000 + 20000 from rfl, win_add, c14]
    exact ch3_15
  have c16 : win 214921799 340000 = (88092417, 154095799, 38629862, 92839036, 90331707) := by
    rw [show (340000 : ℕ) = 320000 + 20000 from rfl, win_add, c15]
    exact ch3_16
  have c17 : win 214921799 358202 = (5, 130244764, 198775757, 208463388, 30498100) := by
    rw [show (358202 : ℕ) = 340000 + 18202 from rfl, win_add, c16]
    exact ch3_17
  rw [c17] at hw
  exact absurd hw (by decide)

theorem a599sq : a (599 ^ 2) = 358202 := by
  have hP : Per (599 ^ 2) 358202 := by norm_num; exact per_599sq
  have hd : a (599 ^ 2) ∣ 358202 := a_dvd (by norm_num) hP
  have hd2 : 598 ∣ a (599 ^ 2) := by
    rw [← a599]
    exact a_dvd (by norm_num) (per_of_dvd (dvd_pow_self 599 two_ne_zero) (a_spec (by norm_num)).2)
  obtain ⟨d, hd'⟩ := hd2
  have hdp : d ∣ 599 := by
    rw [hd', show (358202 : ℕ) = 598 * 599 by norm_num] at hd
    exact (Nat.mul_dvd_mul_iff_left (by norm_num)).1 hd
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 599)).1 hdp with h1 | h1
  · exfalso
    have := (a_spec (N := 599 ^ 2) (by norm_num)).2
    rw [hd', h1, mul_one] at this
    exact not_per_599sq_598 (by norm_num at this; exact this)
  · rw [hd', h1]

/-! ## Main theorem -/

theorem part3 : ∀ p : ℕ, p.Prime → 2 < p → a p ≠ a (p ^ 2) →
    ∀ k : ℕ, 0 < k → a (p ^ k) = p ^ (k - 1) * a p := by
  intro p hp hp2 hne k hk
  have hp0 : 0 < p := hp.pos
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  by_cases h599 : p = 599
  · subst h599
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · obtain rfl : k = 1 := by omega
      simp
    · have hlift : ∀ k, 2 ≤ k → ∀ Q, Per (599 ^ k) Q → ¬ Per (599 ^ (k + 1)) Q →
          Per (599 ^ (k + 1)) (599 * Q) ∧ ¬ Per (599 ^ (k + 2)) (599 * Q) := by
        intro k hk Q hQ hn
        refine liftPer (r := k - 1) (by norm_num) (by omega) (loss_599 (by omega)) ?_ Q hQ hn
        obtain ⟨t, ht⟩ := dvd_sum_range_odd hodd
        rw [ht, ← mul_assoc, ← pow_succ]
        exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _
      have hnot : ¬ Per (599 ^ (2 + 1)) 358202 := by norm_num; exact not_per_599cube
      have ht := (tower (by norm_num) 2 hlift 358202 a599sq hnot (k - 2)).1
      rw [show 2 + (k - 2) = k by omega] at ht
      rw [ht, a599]
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      simp only [Nat.add_sub_cancel, show j + 2 - 1 = j + 1 by omega, pow_succ]
      ring
  · have h2 : p ≠ 2 := by omega
    have hlift : ∀ k, 1 ≤ k → ∀ Q, Per (p ^ k) Q → ¬ Per (p ^ (k + 1)) Q →
        Per (p ^ (k + 1)) (p * Q) ∧ ¬ Per (p ^ (k + 2)) (p * Q) := by
      intro k hk Q hQ hn
      refine liftPer (r := k) hp hk (loss_coprime hp h2 h599 k) ?_ Q hQ hn
      obtain ⟨t, ht⟩ := dvd_sum_range_odd hodd
      rw [ht, ← mul_assoc, ← pow_succ]
      exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _
    have hnot : ¬ Per (p ^ (1 + 1)) (a p) := by
      intro h
      apply hne
      have hpp : 0 < p ^ 2 := pow_pos hp0 2
      have d1 : a (p ^ 2) ∣ a p := a_dvd hpp (by simpa using h)
      have d2 : a p ∣ a (p ^ 2) :=
        a_dvd hp0 (per_of_dvd (dvd_pow_self p (by norm_num)) (a_spec hpp).2)
      exact Nat.dvd_antisymm d2 d1
    have ht := (tower hp 1 hlift (a p) (by simp) hnot (k - 1)).1
    rwa [show 1 + (k - 1) = k by omega] at ht

theorem part2 : ∀ k : ℕ, 1 < k → a (2 ^ k) = 3 * 2 ^ (k - 1) := by
  intro k hk
  rcases (show k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ 6 ≤ k by omega) with h | h | h | h | hk6
  · subst h; simpa using a4
  · subst h; simpa using a8
  · subst h; simpa using a16
  · subst h; simpa using a32
  · have hlift : ∀ k, 6 ≤ k → ∀ Q, Per (2 ^ k) Q → ¬ Per (2 ^ (k + 1)) Q →
        Per (2 ^ (k + 1)) (2 * Q) ∧ ¬ Per (2 ^ (k + 2)) (2 * Q) := by
      intro k hk Q hQ hn
      refine liftPer (r := k - 4) Nat.prime_two (by omega) (loss_two (by omega)) ?_ Q hQ hn
      rw [sum_range_two, mul_one]
      exact pow_dvd_pow _ (by omega)
    have ht := (tower Nat.prime_two 6 hlift 96 (by simpa using a64)
      (by simpa using not_per_128_96) (k - 6)).1
    rw [show 6 + (k - 6) = k by omega] at ht
    rw [ht]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
    simp only [Nat.add_sub_cancel, show j + 6 - 1 = j + 5 by omega, pow_add]
    ring

theorem solution :
    (∀ k : ℕ, 0 < k → a (5 ^ k) = 781 * 5 ^ (k - 1)) ∧
    (∀ k : ℕ, 1 < k → a (2 ^ k) = 3 * 2 ^ (k - 1)) ∧
    (∀ p : ℕ, p.Prime → 2 < p → a p ≠ a (p ^ 2) →
      ∀ k : ℕ, 0 < k → a (p ^ k) = p ^ (k - 1) * a p) := by
  refine ⟨?_, part2, part3⟩
  intro k hk
  have hne : a 5 ≠ a (5 ^ 2) := by
    intro h
    have := (a_spec (N := 5 ^ 2) (by norm_num)).2
    rw [← h, a5] at this
    exact not_per_25_781 (by simpa using this)
  rw [part3 5 (by norm_num) (by norm_num) hne k hk, a5, mul_comm]

end OMA.P_oeis_a106297

theorem OMA.solution : type_of% @OMA.S_oeis_a106297.main := OMA.P_oeis_a106297.solution
