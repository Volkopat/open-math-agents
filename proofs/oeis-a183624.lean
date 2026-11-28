import OMAStatements.S_oeis_a183624

-- Credit: @Dariusthedoggie
-- Proof: 9-state transfer matrix over rows; the transition operator annihilates the order-3 recurrence polynomial, giving recurrence, closed form and g.f., bridged to the IsValid/integer encoding.

namespace OMA.P183624

open PowerSeries

def okBlock (a b c d : Fin 3) : Prop :=
  a.val + b.val + c.val + d.val = 4

instance (a b c d : Fin 3) : Decidable (okBlock a b c d) := by
  unfold okBlock; infer_instance

def isValid (m : ℕ) (x : Fin (m + 1) → Fin 2 → Fin 3) : Prop :=
  ∀ i : Fin m, ∀ j : Fin 1,
    okBlock (x i.castSucc j.castSucc) (x i.castSucc j.succ)
      (x i.succ j.castSucc) (x i.succ j.succ)

instance (m : ℕ) (x : Fin (m + 1) → Fin 2 → Fin 3) : Decidable (isValid m x) := by
  unfold isValid; infer_instance

def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (Finset.univ.filter (isValid (n + 1))).card

abbrev Row := Fin 2 → Fin 3

def okRow (r₁ r₂ : Row) : Prop :=
  ∀ j : Fin 1, okBlock (r₁ j.castSucc) (r₁ j.succ) (r₂ j.castSucc) (r₂ j.succ)

instance (r₁ r₂ : Row) : Decidable (okRow r₁ r₂) := by
  unfold okRow; infer_instance

def enc (r : Row) : Fin 9 :=
  ⟨3 * (r 0).val + (r 1).val, by
    have h0 := (r 0).isLt; have h1 := (r 1).isLt; omega⟩

def dec (k : Fin 9) : Row := fun c =>
  have hk := k.isLt
  if c.val = 0 then ⟨k.val / 3, by omega⟩ else ⟨k.val % 3, by omega⟩

lemma enc_dec : ∀ k : Fin 9, enc (dec k) = k := by
  intro k; have hk := k.isLt; ext; simp [enc, dec]; try omega

lemma dec_enc : ∀ r : Row, dec (enc r) = r := by
  intro r; ext c
  have h0 := (r 0).isLt; have h1 := (r 1).isLt
  fin_cases c
  · change (dec (enc r) 0).val = (r 0).val; simp [dec, enc]; try omega
  · change (dec (enc r) 1).val = (r 1).val; simp [dec, enc]; try omega

def ok2 (i j : Fin 9) : Prop := okRow (dec i) (dec j)

instance (i j : Fin 9) : Decidable (ok2 i j) := by
  unfold ok2; infer_instance

def adjMask : Fin 9 → ℕ
  | ⟨0, _⟩ => 256
  | ⟨1, _⟩ => 160
  | ⟨2, _⟩ => 84
  | ⟨3, _⟩ => 160
  | ⟨4, _⟩ => 84
  | ⟨5, _⟩ => 10
  | ⟨6, _⟩ => 84
  | ⟨7, _⟩ => 10
  | ⟨8, _⟩ => 1

lemma ok2_iff : ∀ i j : Fin 9, ok2 i j ↔ (adjMask i / 2 ^ j.val) % 2 = 1 := by decide +kernel

def step (f : Fin 9 → ℕ) (i : Fin 9) : ℕ :=
  ∑ j : Fin 9, if ok2 i j then f j else 0

def v : ℕ → Fin 9 → ℕ
  | 0, _ => 1
  | m + 1, i => step (v m) i

lemma sum_cons {m : ℕ} (f : (Fin (m + 2) → Row) → ℕ) :
    ∑ x, f x = ∑ r : Row, ∑ y : Fin (m + 1) → Row, f (Fin.cons r y) := by
  rw [← (Fin.consEquiv (fun _ => Row)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma fiber (m : ℕ) (g : (Fin (m + 1) → Row) → ℕ) :
    ∑ y, g y = ∑ i : Fin 9, ∑ y : Fin (m + 1) → Row, if enc (y 0) = i then g y else 0 := by
  trans ∑ y : Fin (m + 1) → Row, ∑ i : Fin 9, if enc (y 0) = i then g y else 0
  · apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_eq_single (enc (y 0))]
    · simp
    · intro i _ hi; simp [Ne.symm hi]
    · simp
  · exact Finset.sum_comm

lemma isValid_zero (y : Fin 1 → Row) : isValid 0 y := by
  intro i; exact Fin.elim0 i

lemma isValid_cons (m : ℕ) (r : Row) (y : Fin (m + 1) → Row) :
    isValid (m + 1) (Fin.cons r y) ↔ okRow r (y 0) ∧ isValid m y := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro j
      simpa [Fin.castSucc_zero, Fin.succ_zero_eq_one] using h 0 j
    · intro i j
      simpa using h i.succ j
  · rintro ⟨h0, hy⟩ i j
    refine Fin.cases ?_ (fun i' => ?_) i
    · simpa [Fin.castSucc_zero, Fin.succ_zero_eq_one] using h0 j
    · simpa using hy i' j

lemma v_eq (m : ℕ) (i : Fin 9) :
    v m i = ∑ y : Fin (m + 1) → Row, if enc (y 0) = i ∧ isValid m y then 1 else 0 := by
  induction m generalizing i with
  | zero =>
    rw [v, ← (Equiv.funUnique (Fin 1) Row).symm.sum_comp]
    rw [Finset.sum_eq_single (dec i)]
    · have hu : (Equiv.funUnique (Fin 1) Row).symm (dec i) = fun _ : Fin 1 => dec i := funext fun _ => rfl
      rw [hu]
      simp [enc_dec, isValid_zero]
    · intro r _ hr
      have hne : enc r ≠ i := fun h => hr (by rw [← dec_enc r, h])
      have hu : (Equiv.funUnique (Fin 1) Row).symm r = fun _ : Fin 1 => r := funext fun _ => rfl
      rw [hu]
      simp [hne]
    · simp
  | succ m ih =>
    rw [v, step, sum_cons]
    rw [Finset.sum_eq_single (dec i)]
    · simp only [Fin.cons_zero, enc_dec, true_and, isValid_cons]
      rw [fiber]
      apply Finset.sum_congr rfl
      intro j _
      rw [ih j]
      by_cases h : ok2 i j
      · simp only [h, ↓reduceIte]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : enc (y 0) = j
        · have hok : okRow (dec i) (y 0) := by
            rw [← dec_enc (y 0), hy]; exact h
          simp [hy, hok]
        · simp [hy]
      · simp only [h, ↓reduceIte]
        symm
        apply Finset.sum_eq_zero
        intro y _
        by_cases hy : enc (y 0) = j
        · have hnok : ¬ okRow (dec i) (y 0) := by
            rw [← dec_enc (y 0), hy]; exact h
          simp [hy, hnok]
        · simp [hy]
    · intro r _ hr
      have hne : enc r ≠ i := fun h => hr (by rw [← dec_enc r, h])
      apply Finset.sum_eq_zero
      intro y _
      simp [hne]
    · simp

lemma a_succ (n : ℕ) : a (n + 1) = ∑ i : Fin 9, v (n + 1) i := by
  simp only [a, Finset.card_filter]
  rw [fiber]
  apply Finset.sum_congr rfl
  intro i _
  rw [v_eq]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> tauto

def vtab0 : Fin 9 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => 1
  | ⟨6, _⟩ => 1
  | ⟨7, _⟩ => 1
  | ⟨8, _⟩ => 1

def vtab1 : Fin 9 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 2
  | ⟨4, _⟩ => 3
  | ⟨5, _⟩ => 2
  | ⟨6, _⟩ => 3
  | ⟨7, _⟩ => 2
  | ⟨8, _⟩ => 1

def vtab2 : Fin 9 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 4
  | ⟨2, _⟩ => 9
  | ⟨3, _⟩ => 4
  | ⟨4, _⟩ => 9
  | ⟨5, _⟩ => 4
  | ⟨6, _⟩ => 9
  | ⟨7, _⟩ => 4
  | ⟨8, _⟩ => 1

def vtab3 : Fin 9 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 8
  | ⟨2, _⟩ => 27
  | ⟨3, _⟩ => 8
  | ⟨4, _⟩ => 27
  | ⟨5, _⟩ => 8
  | ⟨6, _⟩ => 27
  | ⟨7, _⟩ => 8
  | ⟨8, _⟩ => 1

lemma v_0 : ∀ i : Fin 9, v 0 i = vtab0 i := by decide +kernel
lemma v_1 : ∀ i : Fin 9, v 1 i = vtab1 i := by
  intro i; rw [show (1 : ℕ) = 0 + 1 from rfl, v, step]; simp only [v_0, ok2_iff]; revert i; decide +kernel
lemma v_2 : ∀ i : Fin 9, v 2 i = vtab2 i := by
  intro i; rw [show (2 : ℕ) = 1 + 1 from rfl, v, step]; simp only [v_1, ok2_iff]; revert i; decide +kernel
lemma v_3 : ∀ i : Fin 9, v 3 i = vtab3 i := by
  intro i; rw [show (3 : ℕ) = 2 + 1 from rfl, v, step]; simp only [v_2, ok2_iff]; revert i; decide +kernel

def err (m : ℕ) (i : Fin 9) : ℤ :=
  (v (m + 3) i : ℤ) - 6 * (v (m + 2) i : ℤ) + 11 * (v (m + 1) i : ℤ) - 6 * (v m i : ℤ)

lemma err_base : ∀ i : Fin 9, err 0 i = 0 := by
  intro i
  change (v 3 i : ℤ) - 6 * (v 2 i : ℤ) + 11 * (v 1 i : ℤ) - 6 * (v 0 i : ℤ) = 0
  simp only [v_3, v_2, v_1, v_0]
  revert i; decide +kernel

lemma err_succ (m : ℕ) (i : Fin 9) :
    err (m + 1) i = ∑ j : Fin 9, if ok2 i j then err m j else 0 := by
  have hV : ∀ r, (v (r + 1) i : ℤ) = ∑ j : Fin 9, if ok2 i j then (v r j : ℤ) else 0 := by
    intro r; rw [v, step]; simp
  unfold err
  simp only [hV]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

lemma err_all (m : ℕ) (i : Fin 9) : err m i = 0 := by
  induction m generalizing i with
  | zero => exact err_base i
  | succ m ih =>
    rw [err_succ]
    exact Finset.sum_eq_zero (fun j _ => by simp [ih j])

lemma err_ge (m : ℕ) (i : Fin 9) : err (m + 1) i = 0 := err_all (m + 1) i

lemma a_rec_ge (m : ℕ) :
    (a (m + 4) : ℤ) = 6 * a (m + 3) - 11 * a (m + 2) + 6 * a (m + 1) := by
  have h : ∑ i : Fin 9, err (m + 1) i = 0 :=
    Finset.sum_eq_zero (fun i _ => err_ge m i)
  unfold err at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  have hsum : ∀ r : ℕ, (∑ i : Fin 9, (v (m + 1 + r) i : ℤ)) = (a (m + 1 + r) : ℤ) := by
    intro r
    have h1 : m + 1 + r = (m + 0 + r) + 1 := by omega
    rw [h1, a_succ, Nat.cast_sum]
  have hsum0 : (∑ i : Fin 9, (v (m + 1) i : ℤ)) = (a (m + 1) : ℤ) := by
    simpa using hsum 0
  simp only [hsum, hsum0] at h
  have h2_1 : m + 1 + 1 = m + 2 := by omega
  have h2_2 : m + 1 + 2 = m + 3 := by omega
  have h2_3 : m + 1 + 3 = m + 4 := by omega
  simp only [h2_1, h2_2, h2_3] at h
  linarith

lemma a_0 : a 0 = 0 := rfl
lemma a_1 : a 1 = 19 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ]
  change ∑ i : Fin 9, v 1 i = 19
  simp only [v_1]; decide +kernel
lemma a_2 : a 2 = 45 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ]
  change ∑ i : Fin 9, v 2 i = 45
  simp only [v_2]; decide +kernel
lemma a_3 : a 3 = 115 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_succ]
  change ∑ i : Fin 9, v 3 i = 115
  simp only [v_3]; decide +kernel

def cf (n : ℕ) : ℤ :=
  (2 : ℤ) + (2 : ℤ) ^ (2 + n) + (3 : ℤ) ^ (1 + n)

theorem main_proof_ours :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 6 * a (n - 1) - 11 * a (n - 2) + 6 * a (n - 3)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X) * (1 - 3 * X)) =
      X * (19 - 69 * X + 54 * X ^ 2)) ∧
    (∀ n : ℕ, 1 ≤ n → a n = 2 + 2 ^ (2 + n) + 3 ^ (1 + n)) := by
  have hrec : ∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 6 * a (n - 1) - 11 * a (n - 2) + 6 * a (n - 3) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    simpa using a_rec_ge m
  have hgf : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X) * (1 - 3 * X)) =
      X * (19 - 69 * X + 54 * X ^ 2) := by
    have hl : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X) * (1 - 3 * X)) =
        PowerSeries.mk (fun n => (a n : ℚ))
        - C (6 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        + C (11 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
        - C (6 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3) := by
      simp only [map_ofNat, map_one]; ring
    have hr : (X * (19 - 69 * X + 54 * X ^ 2) : PowerSeries ℚ) =
        C (19 : ℚ) * X ^ 1 - C (69 : ℚ) * X ^ 2 + C (54 : ℚ) * X ^ 3 := by
      simp only [map_ofNat, map_one]; ring
    rw [hl, hr]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases Nat.lt_or_ge n 4 with hn | hn
    · interval_cases n <;> simp [a_0, a_1, a_2, a_3] <;> try norm_num
    · have hq : (a n : ℚ) = 6 * a (n - 1) - 11 * a (n - 2) + 6 * a (n - 3) := by
        exact_mod_cast hrec n (by omega)
      have c1 : 1 ≤ n := by omega
      have c2 : 2 ≤ n := by omega
      have c3 : 3 ≤ n := by omega
      have e1 : n - 1 ≠ 0 := by omega
      have e2 : n - 2 ≠ 0 := by omega
      have e3 : n - 3 ≠ 0 := by omega
      simp only [c1, c2, c3, e1, e2, e3, coeff_C, if_true, if_false, ite_self]
      rw [hq]; ring
  have hcf : ∀ n : ℕ, 1 ≤ n → a n = 2 + 2 ^ (2 + n) + 3 ^ (1 + n) := by
    have hZ : ∀ m : ℕ,
                (a (m + 1) : ℤ) = cf (m + 1) ∧
        (a (m + 2) : ℤ) = cf (m + 2) ∧
        (a (m + 3) : ℤ) = cf (m + 3) := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.zero_add, cf, a_1, a_2, a_3]
        norm_num
      | succ m ih =>
        obtain ⟨h0, h1, h2⟩ := ih
        refine ⟨(by simpa only [show m + 1 + 1 = m + 2 by omega] using h1), (by simpa only [show m + 1 + 2 = m + 3 by omega] using h2), ?_⟩
        rw [show m + 1 + 3 = m + 4 by omega]
        have hr := hrec (m + 4) (by omega)
        simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega] at hr
        rw [hr, h0, h1, h2]
        unfold cf
        have hp0_1 : (2 : ℤ) ^ (2 + (m + 2)) = (2 : ℤ) ^ (2 + (m + 1)) * (2 : ℤ) ^ 1 := by rw [show 2 + (m + 2) = (2 + (m + 1)) + 1 by omega, pow_add]
        have hp0_2 : (2 : ℤ) ^ (2 + (m + 3)) = (2 : ℤ) ^ (2 + (m + 1)) * (2 : ℤ) ^ 2 := by rw [show 2 + (m + 3) = (2 + (m + 1)) + 2 by omega, pow_add]
        have hp0_3 : (2 : ℤ) ^ (2 + (m + 4)) = (2 : ℤ) ^ (2 + (m + 1)) * (2 : ℤ) ^ 3 := by rw [show 2 + (m + 4) = (2 + (m + 1)) + 3 by omega, pow_add]
        have hp1_1 : (3 : ℤ) ^ (1 + (m + 2)) = (3 : ℤ) ^ (1 + (m + 1)) * (3 : ℤ) ^ 1 := by rw [show 1 + (m + 2) = (1 + (m + 1)) + 1 by omega, pow_add]
        have hp1_2 : (3 : ℤ) ^ (1 + (m + 3)) = (3 : ℤ) ^ (1 + (m + 1)) * (3 : ℤ) ^ 2 := by rw [show 1 + (m + 3) = (1 + (m + 1)) + 2 by omega, pow_add]
        have hp1_3 : (3 : ℤ) ^ (1 + (m + 4)) = (3 : ℤ) ^ (1 + (m + 1)) * (3 : ℤ) ^ 3 := by rw [show 1 + (m + 4) = (1 + (m + 1)) + 3 by omega, pow_add]
        simp only [hp0_1, hp0_2, hp0_3, hp1_1, hp1_2, hp1_3]
        ring
    intro n hn
    have h := (hZ (n - 1)).1
    rw [show n - 1 + 1 = n by omega] at h
    unfold cf at h
    have hcast : ((a n : ℕ) : ℤ) = ((2 + 2 ^ (2 + n) + 3 ^ (1 + n) : ℕ) : ℤ) := by
      push_cast; exact h
    exact Nat.cast_injective hcast
  exact ⟨hrec, hgf, hcf⟩


lemma valid_iff (n : ℕ) (g : Fin (n + 1) → Fin 2 → Fin 3) :
    OMA.S_oeis_a183624.IsValid g ↔ isValid n g := by
  simp [OMA.S_oeis_a183624.IsValid, isValid, okBlock, Fin.forall_fin_one]

lemma a_eq (n : ℕ) : OMA.S_oeis_a183624.a n = (a n : ℤ) := by
  cases n with
  | zero => rfl
  | succ n =>
    show ((Finset.univ.filter fun g => OMA.S_oeis_a183624.IsValid g).card : ℤ) =
      ((Finset.univ.filter (isValid (n + 1))).card : ℤ)
    congr 2
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact valid_iff (n + 1) g

theorem main_proof : type_of% @OMA.S_oeis_a183624.main := by
  obtain ⟨hrec, _, hcf⟩ := main_proof_ours
  have hfun : OMA.S_oeis_a183624.a = fun n => (a n : ℤ) := funext a_eq
  rw [hfun]
  refine ⟨?_, hrec, ?_⟩
  · intro n hn
    show ((a n : ℕ) : ℤ) = _
    rw [hcf n hn]
    push_cast
    ring
  · have hl : PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 2 * X) * (1 - 3 * X)) =
        PowerSeries.mk (fun n => (a n : ℤ))
        - C (6 : ℤ) * (PowerSeries.mk (fun n => (a n : ℤ)) * X ^ 1)
        + C (11 : ℤ) * (PowerSeries.mk (fun n => (a n : ℤ)) * X ^ 2)
        - C (6 : ℤ) * (PowerSeries.mk (fun n => (a n : ℤ)) * X ^ 3) := by
      simp only [map_ofNat, map_one]; ring
    have hr : (X * (19 - 69 * X + 54 * X ^ 2) : PowerSeries ℤ) =
        C (19 : ℤ) * X ^ 1 - C (69 : ℤ) * X ^ 2 + C (54 : ℤ) * X ^ 3 := by
      simp only [map_ofNat, map_one]; ring
    rw [hl, hr]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases Nat.lt_or_ge n 4 with hn | hn
    · interval_cases n <;> simp only [coeff_C, a_0, a_1, a_2, a_3] <;> norm_num [a_0, a_1, a_2, a_3]
    · have hq := hrec n (by omega)
      have c1 : 1 ≤ n := by omega
      have c2 : 2 ≤ n := by omega
      have c3 : 3 ≤ n := by omega
      have e1 : n - 1 ≠ 0 := by omega
      have e2 : n - 2 ≠ 0 := by omega
      have e3 : n - 3 ≠ 0 := by omega
      simp only [c1, c2, c3, e1, e2, e3, coeff_C, if_true, if_false, ite_self]
      rw [hq]; ring

end OMA.P183624

theorem OMA.solution : type_of% @OMA.S_oeis_a183624.main := OMA.P183624.main_proof
