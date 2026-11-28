import OMAStatements.S_oeis_a106303

/-!
# Proof of the two conjectures of A106303 (period of the pentanacci numbers mod n)

Outline. The shifts of f span all integer sequences with the pentanacci recurrence (the
Hankel determinant of f is 1), so a period of f modulo M is a period modulo M of every such
sequence. Lifting: if Q is a period modulo p^k but not modulo p^(k+1), then pQ is a period
modulo p^(k+1) but not modulo p^(k+2), provided p is odd and k >= 1, or k >= 2. The minimal
period divides every period, which gives a(p^(k+1)) = p * a(p^k). For p = 2 the tower starts at
a(4) = 12 (with 12 not a period mod 8); for p = 5, a(5) = 781 and 781 is not a period mod 25.
The small values are computed with a fast windowed evaluation of f modulo N.
-/

namespace OMA.P_oeis_a106303
open OMA.S_oeis_a106303

/-! ## Basic facts about the pentanacci numbers -/

theorem f_succ5 (n : ℕ) : f (n + 5) = f n + f (n + 1) + f (n + 2) + f (n + 3) + f (n + 4) := rfl

/-- `P` is a period of `f` modulo `N` (`P = 0` allowed). -/
def Per (N P : ℕ) : Prop := ∀ m : ℕ, f (m + P) ≡ f m [MOD N]

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

theorem f_shift_rec (P : ℕ) (n : ℕ) :
    f (n + 5 + P) = f (n + P) + f (n + 1 + P) + f (n + 2 + P) + f (n + 3 + P) + f (n + 4 + P) := by
  rw [show n + 5 + P = n + P + 5 by ring, f_succ5, Nat.add_right_comm n P 1,
    Nat.add_right_comm n P 2, Nat.add_right_comm n P 3, Nat.add_right_comm n P 4]

theorem per_of_init {N P : ℕ} (h : ∀ i < 5, f (i + P) ≡ f i [MOD N]) : Per N P :=
  rec_modEq (fun m => f (m + P)) f (f_shift_rec P) f_succ5 h

/-- Fast computation of five consecutive values modulo `N`. -/
def step (N : ℕ) (t : ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  (t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2, (t.1 + t.2.1 + t.2.2.1 + t.2.2.2.1 + t.2.2.2.2) % N)

def win (N : ℕ) : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ
  | 0 => (0, 0, 0, 0, 1 % N)
  | (n + 1) => step N (win N n)

theorem win_spec (N n : ℕ) :
    win N n = (f n % N, f (n + 1) % N, f (n + 2) % N, f (n + 3) % N, f (n + 4) % N) := by
  induction n with
  | zero => simp [win, f]
  | succ n ih =>
    rw [win, ih, step]
    simp only [Prod.mk.injEq, true_and]
    rw [show n + 1 + 4 = n + 5 by ring, f_succ5]
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

theorem back {N m m' : ℕ} (h : ∀ t < 5, f (m + 1 + t) ≡ f (m' + 1 + t) [MOD N]) :
    ∀ t < 5, f (m + t) ≡ f (m' + t) [MOD N] := by
  intro t ht
  rcases Nat.eq_zero_or_pos t with rfl | htp
  · have e : ∀ x, f (x + 1 + 4) = f (x + 0) +
        (f (x + 1 + 0) + f (x + 1 + 1) + f (x + 1 + 2) + f (x + 1 + 3)) := by
      intro x
      rw [show x + 1 + 4 = x + 5 by ring, f_succ5]
      simp only [add_zero, add_assoc]
    have h4 := h 4 (by omega)
    rw [e m, e m'] at h4
    exact Nat.ModEq.add_right_cancel
      ((((h 0 (by omega)).add (h 1 (by omega))).add (h 2 (by omega))).add (h 3 (by omega))) h4
  · have := h (t - 1) (by omega)
    rwa [show m + 1 + (t - 1) = m + t by omega, show m' + 1 + (t - 1) = m' + t by omega] at this

theorem per_of_eq_window {N i j : ℕ} (hij : i < j)
    (hw : ∀ t < 5, f (i + t) ≡ f (j + t) [MOD N]) : Per N (j - i) := by
  have key : ∀ s ≤ i, ∀ t < 5, f (i - s + t) ≡ f (j - s + t) [MOD N] := by
    intro s
    induction s with
    | zero => simpa using hw
    | succ s ih =>
      intro hs
      apply back
      intro t ht
      have := ih (by omega) t ht
      rwa [show i - (s + 1) + 1 = i - s by omega, show j - (s + 1) + 1 = j - s by omega]
  have h0 := key i le_rfl
  apply per_of_init
  intro t ht
  have := (h0 t ht).symm
  rwa [Nat.sub_self, zero_add, add_comm] at this

theorem exists_per {N : ℕ} (hN : 0 < N) : ∃ P, 0 < P ∧ Per N P := by
  let w : ℕ → Fin 5 → Fin N := fun m t => ⟨f (m + t) % N, Nat.mod_lt _ hN⟩
  obtain ⟨i, j, hij, hw⟩ := Finite.exists_ne_map_eq_of_infinite w
  have hw' : ∀ t < 5, f (i + t) ≡ f (j + t) [MOD N] := by
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

/-! ## Integer sequences satisfying the recurrence -/

def F (n : ℕ) : ℤ := f n

def RecZ (g : ℕ → ℤ) : Prop :=
  ∀ n, g (n + 5) = g n + g (n + 1) + g (n + 2) + g (n + 3) + g (n + 4)

theorem F_rec : RecZ F := fun n => by simp [F, f_succ5]

def PerZ (M : ℤ) (Q : ℕ) : Prop := ∀ n, M ∣ F (n + Q) - F n

theorem per_iff_perZ (N Q : ℕ) : Per N Q ↔ PerZ (N : ℤ) Q := by
  unfold Per PerZ
  refine forall_congr' fun n => ?_
  rw [Nat.ModEq.comm, Nat.modEq_iff_dvd]
  rfl

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

/-- Coefficients expressing a recurrence sequence through the shifts of `F`. -/
def c4 (g : ℕ → ℤ) : ℤ := g 0
def c3 (g : ℕ → ℤ) : ℤ := g 1 - c4 g
def c2 (g : ℕ → ℤ) : ℤ := g 2 - c3 g - 2 * c4 g
def c1 (g : ℕ → ℤ) : ℤ := g 3 - c2 g - 2 * c3 g - 4 * c4 g
def c0 (g : ℕ → ℤ) : ℤ := g 4 - c1 g - 2 * c2 g - 4 * c3 g - 8 * c4 g

/-- Every integer sequence with the pentanacci recurrence is an integer combination of
shifts of `F` (the Hankel determinant of `F` is 1). -/
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
    have v : F 0 = 0 ∧ F 1 = 0 ∧ F 2 = 0 ∧ F 3 = 0 ∧ F 4 = 1 ∧ F 5 = 1 ∧ F 6 = 2 ∧ F 7 = 4 ∧
        F 8 = 8 := by
      simp only [F]
      norm_num [f]
    obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8⟩ := v
    interval_cases i <;> simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, c0, c1, c2, c3, c4] <;> ring

/-- A period of `F` modulo `M` is a period modulo `M` of every recurrence sequence. -/
theorem span {g : ℕ → ℤ} (hg : RecZ g) {M : ℤ} {Q : ℕ} (hQ : PerZ M Q) (n : ℕ) :
    M ∣ g (n + Q) - g n := by
  rw [rep hg (n + Q), rep hg n]
  have d0 := hQ n
  have d1 := hQ (n + 1)
  have d2 := hQ (n + 2)
  have d3 := hQ (n + 3)
  have d4 := hQ (n + 4)
  rw [Nat.add_right_comm n 1 Q] at d1
  rw [Nat.add_right_comm n 2 Q] at d2
  rw [Nat.add_right_comm n 3 Q] at d3
  rw [Nat.add_right_comm n 4 Q] at d4
  have : c0 g * F (n + Q) + c1 g * F (n + Q + 1) + c2 g * F (n + Q + 2) + c3 g * F (n + Q + 3)
      + c4 g * F (n + Q + 4) - (c0 g * F n + c1 g * F (n + 1) + c2 g * F (n + 2)
      + c3 g * F (n + 3) + c4 g * F (n + 4))
      = c0 g * (F (n + Q) - F n) + c1 g * (F (n + Q + 1) - F (n + 1))
        + c2 g * (F (n + Q + 2) - F (n + 2)) + c3 g * (F (n + Q + 3) - F (n + 3))
        + c4 g * (F (n + Q + 4) - F (n + 4)) := by ring
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
    have : F (n + j * Q + Q) - F n
        = (F (n + j * Q + Q) - F (n + j * Q)) + (F (n + j * Q) - F n) := by ring
    rw [this]
    exact h1.add h2

/-! ## The lifting lemma -/

theorem lift {p k Q : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    (hcond : (p : ℤ) ^ (k + 2) ∣ (p : ℤ) ^ (2 * k) * ∑ i ∈ Finset.range p, (i : ℤ))
    (hQ : PerZ ((p : ℤ) ^ k) Q) (hnot : ¬ PerZ ((p : ℤ) ^ (k + 1)) Q) :
    PerZ ((p : ℤ) ^ (k + 1)) (p * Q) ∧ ¬ PerZ ((p : ℤ) ^ (k + 2)) (p * Q) := by
  set q : ℤ := (p : ℤ) with hqdef
  have hq0 : q ≠ 0 := by simp [q, hp.ne_zero]
  have hqk : q ^ k ≠ 0 := pow_ne_zero k hq0
  have hGrec : RecZ (fun n => F (n + Q) - F n) := recZ_shiftdiff F_rec Q
  set h : ℕ → ℤ := fun n => (F (n + Q) - F n) / q ^ k with hhdef
  have hG : ∀ n, F (n + Q) - F n = q ^ k * h n := fun n => (Int.mul_ediv_cancel' (hQ n)).symm
  have hh : RecZ h := recZ_quot hGrec hqk hQ
  have hDrec : RecZ (fun n => h (n + Q) - h n) := recZ_shiftdiff hh Q
  have hDd : ∀ n, q ^ k ∣ h (n + Q) - h n := span hh hQ
  set h' : ℕ → ℤ := fun n => (h (n + Q) - h n) / q ^ k with hh'def
  have hD : ∀ n, h (n + Q) - h n = q ^ k * h' n := fun n => (Int.mul_ediv_cancel' (hDd n)).symm
  have hh' : RecZ h' := recZ_quot hDrec hqk hDd
  have hh'per : ∀ i n, q ^ k ∣ h' (n + i * Q) - h' n := fun i n => span hh' (perZ_mul hQ i) n
  have claimA : ∀ j n, q ^ (2 * k) ∣ h (n + j * Q) - h n - j * q ^ k * h' n := by
    intro j
    induction j with
    | zero => intro n; simp
    | succ j ih =>
      intro n
      have e : h (n + (j + 1) * Q) = h (n + j * Q) + q ^ k * h' (n + j * Q) := by
        rw [← hD, Nat.succ_mul, ← add_assoc]
        ring
      rw [e]
      have : h (n + j * Q) + q ^ k * h' (n + j * Q) - h n - ((j + 1 : ℕ) : ℤ) * q ^ k * h' n
          = (h (n + j * Q) - h n - j * q ^ k * h' n) + q ^ k * (h' (n + j * Q) - h' n) := by
        push_cast
        ring
      rw [this]
      refine (ih n).add ?_
      rw [two_mul, pow_add]
      exact mul_dvd_mul_left _ (hh'per j n)
  have claimB : ∀ j n, F (n + j * Q) - F n = q ^ k * ∑ i ∈ Finset.range j, h (n + i * Q) := by
    intro j
    induction j with
    | zero => intro n; simp
    | succ j ih =>
      intro n
      rw [Finset.sum_range_succ, mul_add, ← ih n, ← hG (n + j * Q), Nat.succ_mul, ← add_assoc]
      ring
  have key : ∀ n, q ^ (k + 2) ∣ F (n + p * Q) - F n - q ^ (k + 1) * h n := by
    intro n
    have hsum : ∑ i ∈ Finset.range p, (h (n + i * Q) - h n - i * q ^ k * h' n)
        = ∑ i ∈ Finset.range p, h (n + i * Q) - p * h n
          - q ^ k * (∑ i ∈ Finset.range p, (i : ℤ)) * h' n := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        Finset.mul_sum, Finset.sum_mul]
      simp only [nsmul_eq_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => by ring
    have hE : q ^ (2 * k) ∣ ∑ i ∈ Finset.range p, (h (n + i * Q) - h n - i * q ^ k * h' n) :=
      Finset.dvd_sum fun i _ => claimA i n
    obtain ⟨E, hEq⟩ := hE
    have hF := claimB p n
    have hexp : F (n + p * Q) - F n - q ^ (k + 1) * h n
        = q ^ (2 * k) * (∑ i ∈ Finset.range p, (i : ℤ)) * h' n + q ^ (3 * k) * E := by
      rw [hF]
      have : ∑ i ∈ Finset.range p, h (n + i * Q)
          = q ^ (2 * k) * E + p * h n + q ^ k * (∑ i ∈ Finset.range p, (i : ℤ)) * h' n := by
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

/-! ## The tower -/

theorem tower {p : ℕ} (hp : p.Prime) (k0 : ℕ) (hk0 : 1 ≤ k0)
    (hcond : ∀ k, k0 ≤ k → (p : ℤ) ^ (k + 2) ∣ (p : ℤ) ^ (2 * k) * ∑ i ∈ Finset.range p, (i : ℤ))
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
    have hlift := lift hp (by omega) (hcond k (by omega))
      (by have := (per_iff_perZ _ _).1 hper; push_cast at this; exact this)
      (by intro h; apply hn; rw [per_iff_perZ]; push_cast; exact h)
    obtain ⟨hl1, hl2⟩ := hlift
    have hl1' : Per (p ^ (k + 1)) (p * (p ^ j * Q)) := by
      rw [per_iff_perZ]; push_cast; exact hl1
    have hl2' : ¬ Per (p ^ (k + 1 + 1)) (p * (p ^ j * Q)) := by
      rw [per_iff_perZ]; push_cast; exact hl2
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

/-! ## Concrete computations -/

theorem a2 : a 2 = 6 := by
  have h6 : Per 2 6 := (per_iff_win _ _).2 (by decide)
  have hd : a 2 ∣ 6 := a_dvd (by norm_num) h6
  obtain ⟨_, hper⟩ := a_spec (N := 2) (by norm_num)
  have hm : a 2 ∈ Nat.divisors 6 := Nat.mem_divisors.2 ⟨hd, by norm_num⟩
  rw [show Nat.divisors 6 = {1, 2, 3, 6} by decide] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h | h <;> rw [h] at hper ⊢
  all_goals first | rfl | exact absurd ((per_iff_win _ _).1 hper) (by decide)

theorem a4 : a 4 = 12 := by
  have h12 : Per 4 12 := (per_iff_win _ _).2 (by decide)
  have hd : a 4 ∣ 12 := a_dvd (by norm_num) h12
  obtain ⟨_, hper⟩ := a_spec (N := 4) (by norm_num)
  have hm : a 4 ∈ Nat.divisors 12 := Nat.mem_divisors.2 ⟨hd, by norm_num⟩
  rw [show Nat.divisors 12 = {1, 2, 3, 4, 6, 12} by decide] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h | h | h | h <;> rw [h] at hper ⊢
  all_goals first | rfl | exact absurd ((per_iff_win _ _).1 hper) (by decide)

theorem not_per_8_12 : ¬ Per 8 12 := fun h => absurd ((per_iff_win _ _).1 h) (by decide)

set_option maxRecDepth 100000 in
theorem a5 : a 5 = 781 := by
  have h781 : Per 5 781 := (per_iff_win _ _).2 (by decide)
  have hd : a 5 ∣ 781 := a_dvd (by norm_num) h781
  obtain ⟨_, hper⟩ := a_spec (N := 5) (by norm_num)
  have hm : a 5 ∈ Nat.divisors 781 := Nat.mem_divisors.2 ⟨hd, by norm_num⟩
  rw [show Nat.divisors 781 = {1, 11, 71, 781} by decide] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h | h <;> rw [h] at hper ⊢
  all_goals first | rfl | exact absurd ((per_iff_win _ _).1 hper) (by decide)

set_option maxRecDepth 100000 in
theorem not_per_25_781 : ¬ Per 25 781 := fun h => absurd ((per_iff_win _ _).1 h) (by decide)

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

/-! ## Main theorem -/

theorem part2 : ∀ p : ℕ, p.Prime → a p ≠ a (p ^ 2) →
    ∀ k : ℕ, 0 < k → a (p ^ k) = p ^ (k - 1) * a p := by
  intro p hp hne k hk
  rcases hp.eq_two_or_odd' with rfl | hodd
  · rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · obtain rfl : k = 1 := by omega
      simp
    · have hcond : ∀ k, 2 ≤ k → ((2 : ℕ) : ℤ) ^ (k + 2) ∣
          ((2 : ℕ) : ℤ) ^ (2 * k) * ∑ i ∈ Finset.range 2, (i : ℤ) := by
        intro k hk
        rw [sum_range_two, mul_one]
        exact pow_dvd_pow _ (by omega)
      have ht := (tower Nat.prime_two 2 (by norm_num) hcond 12 (by simpa using a4)
        (by simpa using not_per_8_12) (k - 2)).1
      rw [show 2 + (k - 2) = k by omega] at ht
      rw [ht, a2]
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      simp only [Nat.add_sub_cancel, show j + 2 - 1 = j + 1 by omega, pow_succ]
      ring
  · have hp0 : 0 < p := hp.pos
    have hcond : ∀ k, 1 ≤ k →
        (p : ℤ) ^ (k + 2) ∣ (p : ℤ) ^ (2 * k) * ∑ i ∈ Finset.range p, (i : ℤ) := by
      intro k hk
      obtain ⟨t, ht⟩ := dvd_sum_range_odd hodd
      rw [ht, ← mul_assoc, ← pow_succ]
      exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _
    have hnot : ¬ Per (p ^ (1 + 1)) (a p) := by
      intro h
      apply hne
      have hp2 : 0 < p ^ 2 := pow_pos hp0 2
      have d1 : a (p ^ 2) ∣ a p := a_dvd hp2 (by simpa using h)
      have d2 : a p ∣ a (p ^ 2) :=
        a_dvd hp0 (per_of_dvd (dvd_pow_self p (by norm_num)) (a_spec hp2).2)
      exact Nat.dvd_antisymm d2 d1
    have ht := (tower hp 1 le_rfl hcond (a p) (by simp) hnot (k - 1)).1
    rwa [show 1 + (k - 1) = k by omega] at ht

theorem solution :
    (∀ k : ℕ, 0 < k → a (5 ^ k) = 781 * 5 ^ (k - 1)) ∧
    (∀ p : ℕ, p.Prime → a p ≠ a (p ^ 2) → ∀ k : ℕ, 0 < k → a (p ^ k) = p ^ (k - 1) * a p) := by
  refine ⟨?_, part2⟩
  intro k hk
  have hne : a 5 ≠ a (5 ^ 2) := by
    intro h
    have := (a_spec (N := 5 ^ 2) (by norm_num)).2
    rw [← h, a5] at this
    exact not_per_25_781 (by simpa using this)
  rw [part2 5 (by norm_num) hne k hk, a5, mul_comm]

end OMA.P_oeis_a106303

theorem OMA.solution : type_of% @OMA.S_oeis_a106303.main := OMA.P_oeis_a106303.solution
