import OMAStatements.S_oeis_a101424

-- Problem: A101424: cuboids with volume p^4 q^n.
-- Upstream: formal-conjectures statements/oeis-a101424.lean:0 (declaration OMA.S_oeis_a101424.main)
-- Credit: @biondadave (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.A101424Proof

open Finset OMA.S_oeis_a101424

/-! ## The sorting identity `6 * cuboids V = |T| + 3 |Sq|` for `V` not a cube -/

/-- Ordered triples of divisors with product `V`. -/
def T (V : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (V.divisors ×ˢ V.divisors ×ˢ V.divisors).filter (fun t => t.1 * t.2.1 * t.2.2 = V)

/-- Pairs `(x, z)` of divisors with `x * x * z = V`. -/
def Sq (V : ℕ) : Finset (ℕ × ℕ) :=
  (V.divisors ×ˢ V.divisors).filter (fun s => s.1 * s.1 * s.2 = V)

lemma mem_T {V : ℕ} (hV : V ≠ 0) (t : ℕ × ℕ × ℕ) : t ∈ T V ↔ t.1 * t.2.1 * t.2.2 = V := by
  simp only [T, mem_filter, mem_product, Nat.mem_divisors]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨⟨?_, hV⟩, ⟨?_, hV⟩, ⟨?_, hV⟩⟩, h⟩
    · exact ⟨t.2.1 * t.2.2, by rw [← h]; ring⟩
    · exact ⟨t.1 * t.2.2, by rw [← h]; ring⟩
    · exact ⟨t.1 * t.2.1, by rw [← h]; ring⟩

lemma mem_Sq {V : ℕ} (hV : V ≠ 0) (s : ℕ × ℕ) : s ∈ Sq V ↔ s.1 * s.1 * s.2 = V := by
  simp only [Sq, mem_filter, mem_product, Nat.mem_divisors]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨⟨?_, hV⟩, ⟨?_, hV⟩⟩, h⟩
    · exact ⟨s.1 * s.2, by rw [← h]; ring⟩
    · exact ⟨s.1 * s.1, by rw [← h]; ring⟩

lemma cuboids_eq (V : ℕ) :
    cuboids V = ((T V).filter (fun t => t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2)).card := by
  unfold cuboids T
  rw [filter_filter]
  congr 1
  apply filter_congr
  intro t _
  tauto

/-- Permuting coordinates by a product-preserving bijection preserves filtered counts of `T`. -/
lemma card_T_perm {V : ℕ} (hV : V ≠ 0) (σ τ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ)
    (hστ : ∀ t, σ (τ t) = t) (hτσ : ∀ t, τ (σ t) = t)
    (hprod : ∀ t, (σ t).1 * (σ t).2.1 * (σ t).2.2 = t.1 * t.2.1 * t.2.2)
    (P : ℕ × ℕ × ℕ → Prop) [DecidablePred P] :
    ((T V).filter (fun t => P (σ t))).card = ((T V).filter P).card := by
  have hprod' : ∀ t, (τ t).1 * (τ t).2.1 * (τ t).2.2 = t.1 * t.2.1 * t.2.2 := by
    intro t; rw [← hprod (τ t), hστ]
  apply card_nbij' σ τ
  · intro t ht
    simp only [coe_filter, Set.mem_ofPred_eq, mem_T hV] at ht ⊢
    exact ⟨by rw [hprod]; exact ht.1, ht.2⟩
  · intro t ht
    simp only [coe_filter, Set.mem_ofPred_eq, mem_T hV] at ht ⊢
    exact ⟨by rw [hprod']; exact ht.1, by rw [hστ]; exact ht.2⟩
  · intro t _; exact hτσ t
  · intro t _; exact hστ t

/-- The `x = y` part of `T` is in bijection with `Sq`. -/
lemma card_T_eq12 {V : ℕ} (hV : V ≠ 0) :
    ((T V).filter (fun t => t.1 = t.2.1)).card = (Sq V).card := by
  apply card_nbij' (fun t => (t.1, t.2.2)) (fun s => (s.1, s.1, s.2))
  · rintro ⟨x, y, z⟩ ht
    rw [mem_coe, mem_filter, mem_T hV] at ht
    rw [mem_coe, mem_Sq hV]
    dsimp only at ht ⊢
    obtain ⟨h, rfl⟩ := ht
    exact h
  · rintro ⟨x, z⟩ hs
    rw [mem_coe, mem_Sq hV] at hs
    rw [mem_coe, mem_filter, mem_T hV]
    exact ⟨hs, rfl⟩
  · rintro ⟨x, y, z⟩ ht
    rw [mem_coe, mem_filter] at ht
    dsimp only at ht
    obtain ⟨_, rfl⟩ := ht
    rfl
  · intro s _; rfl

/-- The `x = z` part of `T` is in bijection with `Sq`. -/
lemma card_T_eq13 {V : ℕ} (hV : V ≠ 0) :
    ((T V).filter (fun t => t.1 = t.2.2)).card = (Sq V).card := by
  apply card_nbij' (fun t => (t.1, t.2.1)) (fun s => (s.1, s.2, s.1))
  · rintro ⟨x, y, z⟩ ht
    rw [mem_coe, mem_filter, mem_T hV] at ht
    rw [mem_coe, mem_Sq hV]
    dsimp only at ht ⊢
    obtain ⟨h, rfl⟩ := ht
    rw [← h]; ring
  · rintro ⟨x, y⟩ hs
    rw [mem_coe, mem_Sq hV] at hs
    rw [mem_coe, mem_filter, mem_T hV]
    dsimp only at hs ⊢
    exact ⟨by rw [← hs]; ring, rfl⟩
  · rintro ⟨x, y, z⟩ ht
    rw [mem_coe, mem_filter] at ht
    dsimp only at ht
    obtain ⟨_, rfl⟩ := ht
    rfl
  · intro s _; rfl

/-- The `y = z` part of `T` is in bijection with `Sq`. -/
lemma card_T_eq23 {V : ℕ} (hV : V ≠ 0) :
    ((T V).filter (fun t => t.2.1 = t.2.2)).card = (Sq V).card := by
  apply card_nbij' (fun t => (t.2.1, t.1)) (fun s => (s.2, s.1, s.1))
  · rintro ⟨x, y, z⟩ ht
    rw [mem_coe, mem_filter, mem_T hV] at ht
    rw [mem_coe, mem_Sq hV]
    dsimp only at ht ⊢
    obtain ⟨h, rfl⟩ := ht
    rw [← h]; ring
  · rintro ⟨x, y⟩ hs
    rw [mem_coe, mem_Sq hV] at hs
    rw [mem_coe, mem_filter, mem_T hV]
    dsimp only at hs ⊢
    exact ⟨by rw [← hs]; ring, rfl⟩
  · rintro ⟨x, y, z⟩ ht
    rw [mem_coe, mem_filter] at ht
    dsimp only at ht
    obtain ⟨_, rfl⟩ := ht
    rfl
  · intro s _; rfl

lemma card_T_lt_eq {V : ℕ} (hV : V ≠ 0) :
    ((T V).filter (fun t => t.1 = t.2.1 ∧ t.2.1 < t.2.2)).card =
      ((Sq V).filter (fun s => s.1 < s.2)).card := by
  apply card_nbij' (fun t => (t.1, t.2.2)) (fun s => (s.1, s.1, s.2))
  · rintro ⟨x, y, z⟩ ht
    rw [mem_coe, mem_filter, mem_T hV] at ht
    rw [mem_coe, mem_filter, mem_Sq hV]
    dsimp only at ht ⊢
    obtain ⟨h, rfl, h2⟩ := ht
    exact ⟨h, h2⟩
  · rintro ⟨x, z⟩ hs
    rw [mem_coe, mem_filter, mem_Sq hV] at hs
    rw [mem_coe, mem_filter, mem_T hV]
    exact ⟨hs.1, rfl, hs.2⟩
  · rintro ⟨x, y, z⟩ ht
    rw [mem_coe, mem_filter] at ht
    dsimp only at ht
    obtain ⟨_, rfl, _⟩ := ht
    rfl
  · intro s _; rfl

lemma card_T_eq_lt {V : ℕ} (hV : V ≠ 0) :
    ((T V).filter (fun t => t.1 < t.2.1 ∧ t.2.1 = t.2.2)).card =
      ((Sq V).filter (fun s => s.2 < s.1)).card := by
  apply card_nbij' (fun t => (t.2.1, t.1)) (fun s => (s.2, s.1, s.1))
  · rintro ⟨x, y, z⟩ ht
    rw [mem_coe, mem_filter, mem_T hV] at ht
    rw [mem_coe, mem_filter, mem_Sq hV]
    dsimp only at ht ⊢
    obtain ⟨h, h1, rfl⟩ := ht
    exact ⟨by rw [← h]; ring, h1⟩
  · rintro ⟨x, y⟩ hs
    rw [mem_coe, mem_filter, mem_Sq hV] at hs
    rw [mem_coe, mem_filter, mem_T hV]
    dsimp only at hs ⊢
    exact ⟨by rw [← hs.1]; ring, hs.2, rfl⟩
  · rintro ⟨x, y, z⟩ ht
    rw [mem_coe, mem_filter] at ht
    dsimp only at ht
    obtain ⟨_, _, rfl⟩ := ht
    rfl
  · intro s _; rfl

theorem sorting_identity {V : ℕ} (hV : V ≠ 0) (hcube : ∀ x, x * x * x ≠ V) :
    6 * cuboids V = (T V).card + 3 * (Sq V).card := by
  have hnc : ∀ t ∈ T V, ¬ (t.1 = t.2.1 ∧ t.2.1 = t.2.2) := by
    intro t ht h
    rw [mem_T hV] at ht
    apply hcube t.1
    rw [← ht, ← h.1, ← h.2, ← h.1]
  -- the six strict order types all have the size of `x < y < z`
  set A := ((T V).filter (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2)).card with hA
  have c2 : ((T V).filter (fun t => t.1 < t.2.2 ∧ t.2.2 < t.2.1)).card = A :=
    card_T_perm hV (fun t => (t.1, t.2.2, t.2.1)) (fun t => (t.1, t.2.2, t.2.1))
      (fun _ => rfl) (fun _ => rfl) (fun t => by simp only; ring)
      (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2)
  have c3 : ((T V).filter (fun t => t.2.1 < t.1 ∧ t.1 < t.2.2)).card = A :=
    card_T_perm hV (fun t => (t.2.1, t.1, t.2.2)) (fun t => (t.2.1, t.1, t.2.2))
      (fun _ => rfl) (fun _ => rfl) (fun t => by simp only; ring)
      (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2)
  have c4 : ((T V).filter (fun t => t.2.1 < t.2.2 ∧ t.2.2 < t.1)).card = A :=
    card_T_perm hV (fun t => (t.2.1, t.2.2, t.1)) (fun t => (t.2.2, t.1, t.2.1))
      (fun _ => rfl) (fun _ => rfl) (fun t => by simp only; ring)
      (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2)
  have c5 : ((T V).filter (fun t => t.2.2 < t.1 ∧ t.1 < t.2.1)).card = A :=
    card_T_perm hV (fun t => (t.2.2, t.1, t.2.1)) (fun t => (t.2.1, t.2.2, t.1))
      (fun _ => rfl) (fun _ => rfl) (fun t => by simp only; ring)
      (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2)
  have c6 : ((T V).filter (fun t => t.2.2 < t.2.1 ∧ t.2.1 < t.1)).card = A :=
    card_T_perm hV (fun t => (t.2.2, t.2.1, t.1)) (fun t => (t.2.2, t.2.1, t.1))
      (fun _ => rfl) (fun _ => rfl) (fun t => by simp only; ring)
      (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2)
  -- |T| splits into the nine classes
  have hT : (T V).card = A + ((T V).filter (fun t => t.1 < t.2.2 ∧ t.2.2 < t.2.1)).card +
      ((T V).filter (fun t => t.2.1 < t.1 ∧ t.1 < t.2.2)).card +
      ((T V).filter (fun t => t.2.1 < t.2.2 ∧ t.2.2 < t.1)).card +
      ((T V).filter (fun t => t.2.2 < t.1 ∧ t.1 < t.2.1)).card +
      ((T V).filter (fun t => t.2.2 < t.2.1 ∧ t.2.1 < t.1)).card +
      ((T V).filter (fun t => t.1 = t.2.1)).card + ((T V).filter (fun t => t.1 = t.2.2)).card +
      ((T V).filter (fun t => t.2.1 = t.2.2)).card := by
    simp only [hA, card_filter, ← sum_add_distrib]
    rw [card_eq_sum_ones]
    apply sum_congr rfl
    intro t ht
    have := hnc t ht
    split_ifs <;> omega
  -- the sorted triples split into three classes
  have hS : ((T V).filter (fun t => t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2)).card = A +
      ((T V).filter (fun t => t.1 = t.2.1 ∧ t.2.1 < t.2.2)).card +
      ((T V).filter (fun t => t.1 < t.2.1 ∧ t.2.1 = t.2.2)).card := by
    simp only [hA, card_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro t ht
    have := hnc t ht
    split_ifs <;> omega
  have hSq : (Sq V).card = ((Sq V).filter (fun s => s.1 < s.2)).card +
      ((Sq V).filter (fun s => s.2 < s.1)).card := by
    simp only [card_filter, ← sum_add_distrib]
    rw [card_eq_sum_ones]
    apply sum_congr rfl
    intro s hs
    have hne : s.1 ≠ s.2 := by
      intro h
      rw [mem_Sq hV] at hs
      apply hcube s.1
      rw [← hs, ← h]
    split_ifs <;> omega
  rw [cuboids_eq, hS, card_T_lt_eq hV, card_T_eq_lt hV, hT, c2, c3, c4, c5, c6, card_T_eq12 hV,
    card_T_eq13 hV, card_T_eq23 hV, hSq]
  ring

/-! ## The counts for `V = p^4 q^n` -/

section Specific

variable {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
include hp hq hpq

lemma fac_p (a u : ℕ) : (p ^ a * q ^ u).factorization p = a := by
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero),
    Finsupp.add_apply, hp.factorization_pow, hq.factorization_pow]
  simp [Ne.symm hpq]

lemma fac_q (a u : ℕ) : (p ^ a * q ^ u).factorization q = u := by
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero),
    Finsupp.add_apply, hp.factorization_pow, hq.factorization_pow]
  simp [hpq]

omit hpq in
lemma dvd_form {n x : ℕ} (hx : x ∣ p ^ 4 * q ^ n) :
    ∃ a u, a ≤ 4 ∧ u ≤ n ∧ x = p ^ a * q ^ u := by
  obtain ⟨y, z, hy, hz, rfl⟩ := Nat.dvd_mul.mp hx
  obtain ⟨a, ha, rfl⟩ := (Nat.dvd_prime_pow hp).mp hy
  obtain ⟨u, hu, rfl⟩ := (Nat.dvd_prime_pow hq).mp hz
  exact ⟨a, u, ha, hu, rfl⟩

omit hpq in
lemma ne_zero_V (n : ℕ) : p ^ 4 * q ^ n ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero)

/-- A divisor of `V` is determined by its two exponents. -/
lemma eq_of_dvd {n x : ℕ} (hx : x ∣ p ^ 4 * q ^ n) :
    x = p ^ x.factorization p * q ^ x.factorization q := by
  obtain ⟨a, u, -, -, rfl⟩ := dvd_form hp hq hx
  rw [fac_p hp hq hpq, fac_q hp hq hpq]

end Specific

/-- Exponent triples summing to `k`. -/
def Tri (k : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (range (k + 1) ×ˢ range (k + 1) ×ˢ range (k + 1)).filter (fun e => e.1 + e.2.1 + e.2.2 = k)

lemma mem_Tri (k : ℕ) (e : ℕ × ℕ × ℕ) : e ∈ Tri k ↔ e.1 + e.2.1 + e.2.2 = k := by
  simp only [Tri, mem_filter, mem_product, mem_range]
  omega

lemma two_mul_card_Tri (k : ℕ) : 2 * (Tri k).card = (k + 1) * (k + 2) := by
  have h1 : (Tri k).card = ((range (k + 1) ×ˢ range (k + 1)).filter
      (fun e : ℕ × ℕ => e.1 + e.2 ≤ k)).card := by
    apply card_nbij' (fun e => (e.1, e.2.1)) (fun e => (e.1, e.2, k - e.1 - e.2))
    · rintro ⟨a, b, c⟩ h
      rw [mem_coe, mem_Tri] at h
      simp only [mem_coe, mem_filter, mem_product, mem_range]
      dsimp only at h ⊢
      omega
    · rintro ⟨a, b⟩ h
      simp only [mem_coe, mem_filter, mem_product, mem_range] at h
      rw [mem_coe, mem_Tri]
      dsimp only
      omega
    · rintro ⟨a, b, c⟩ h
      rw [mem_coe, mem_Tri] at h
      dsimp only at h ⊢
      ext <;> simp; omega
    · intro e _; rfl
  have h2 : ((range (k + 1) ×ˢ range (k + 1)).filter (fun e : ℕ × ℕ => e.1 + e.2 ≤ k)).card =
      ∑ a ∈ range (k + 1), (k + 1 - a) := by
    rw [card_filter, sum_product]
    apply sum_congr rfl
    intro a ha
    rw [mem_range] at ha
    rw [← card_filter]
    have : (range (k + 1)).filter (fun b => a + b ≤ k) = range (k + 1 - a) := by
      ext b; simp only [mem_filter, mem_range]; omega
    rw [this, card_range]
  have h3 : ∀ m, 2 * ∑ a ∈ range (m + 1), (m + 1 - a) = (m + 1) * (m + 2) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ', show m + 1 + 1 - 0 = m + 2 by omega]
      have : ∑ a ∈ range (m + 1), (m + 1 + 1 - (a + 1)) = ∑ a ∈ range (m + 1), (m + 1 - a) := by
        apply sum_congr rfl; intro a _; omega
      rw [this, mul_add, ih]
      ring
  rw [h1, h2, h3]

lemma card_Tri_four : (Tri 4).card = 15 := by decide

section Specific2

variable {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
include hp hq hpq

lemma card_T_V (n : ℕ) : (T (p ^ 4 * q ^ n)).card = (Tri 4).card * (Tri n).card := by
  have hV := ne_zero_V hp hq n
  rw [← card_product]
  symm
  apply card_nbij'
    (fun e : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) =>
      (p ^ e.1.1 * q ^ e.2.1, p ^ e.1.2.1 * q ^ e.2.2.1, p ^ e.1.2.2 * q ^ e.2.2.2))
    (fun t => ((t.1.factorization p, t.2.1.factorization p, t.2.2.factorization p),
      (t.1.factorization q, t.2.1.factorization q, t.2.2.factorization q)))
  · rintro ⟨⟨a, b, c⟩, ⟨u, v, w⟩⟩ h
    rw [mem_coe, mem_product, mem_Tri, mem_Tri] at h
    rw [mem_coe, mem_T hV]
    dsimp only at h ⊢
    rw [← h.1, ← h.2, pow_add, pow_add, pow_add, pow_add]
    ring
  · rintro ⟨x, y, z⟩ h
    rw [mem_coe, mem_T hV] at h
    rw [mem_coe, mem_product, mem_Tri, mem_Tri]
    dsimp only at h ⊢
    have hx : x ≠ 0 := by rintro rfl; apply hV; rw [← h]; try simp
    have hy : y ≠ 0 := by rintro rfl; apply hV; rw [← h]; try simp
    have hz : z ≠ 0 := by rintro rfl; apply hV; rw [← h]; try simp
    have hf := congrArg Nat.factorization h
    rw [Nat.factorization_mul (mul_ne_zero hx hy) hz, Nat.factorization_mul hx hy] at hf
    constructor
    · have := congrArg (· p) hf
      simp only [Finsupp.add_apply] at this
      rw [this, fac_p hp hq hpq]
    · have := congrArg (· q) hf
      simp only [Finsupp.add_apply] at this
      rw [this, fac_q hp hq hpq]
  · rintro ⟨⟨a, b, c⟩, ⟨u, v, w⟩⟩ _
    simp only [fac_p hp hq hpq, fac_q hp hq hpq]
  · rintro ⟨x, y, z⟩ h
    rw [mem_coe, mem_T hV] at h
    dsimp only at h ⊢
    have hxd : x ∣ p ^ 4 * q ^ n := ⟨y * z, by rw [← h]; ring⟩
    have hyd : y ∣ p ^ 4 * q ^ n := ⟨x * z, by rw [← h]; ring⟩
    have hzd : z ∣ p ^ 4 * q ^ n := ⟨x * y, by rw [← h]; ring⟩
    rw [← eq_of_dvd hp hq hpq hxd, ← eq_of_dvd hp hq hpq hyd, ← eq_of_dvd hp hq hpq hzd]

lemma card_Sq_V (n : ℕ) : (Sq (p ^ 4 * q ^ n)).card = 3 * (n / 2 + 1) := by
  have hV := ne_zero_V hp hq n
  have hc : (range 3 ×ˢ range (n / 2 + 1)).card = 3 * (n / 2 + 1) := by
    rw [card_product, card_range, card_range]
  rw [← hc]
  symm
  apply card_nbij' (fun e : ℕ × ℕ => (p ^ e.1 * q ^ e.2, p ^ (4 - 2 * e.1) * q ^ (n - 2 * e.2)))
    (fun s => (s.1.factorization p, s.1.factorization q))
  · rintro ⟨a, u⟩ h
    rw [mem_coe, mem_product, mem_range, mem_range] at h
    rw [mem_coe, mem_Sq hV]
    dsimp only
    have e1 : 4 = a + a + (4 - 2 * a) := by omega
    have e2 : n = u + u + (n - 2 * u) := by omega
    calc p ^ a * q ^ u * (p ^ a * q ^ u) * (p ^ (4 - 2 * a) * q ^ (n - 2 * u))
        = p ^ (a + a + (4 - 2 * a)) * q ^ (u + u + (n - 2 * u)) := by
          rw [pow_add, pow_add, pow_add, pow_add]; ring
      _ = p ^ 4 * q ^ n := by rw [← e1, ← e2]
  · rintro ⟨x, z⟩ h
    rw [mem_coe, mem_Sq hV] at h
    rw [mem_coe, mem_product, mem_range, mem_range]
    dsimp only at h ⊢
    have hx : x ≠ 0 := by rintro rfl; apply hV; rw [← h]; try simp
    have hz : z ≠ 0 := by rintro rfl; apply hV; rw [← h]; try simp
    have hf := congrArg Nat.factorization h
    rw [Nat.factorization_mul (mul_ne_zero hx hx) hz, Nat.factorization_mul hx hx] at hf
    have h1 := congrArg (· p) hf
    have h2 := congrArg (· q) hf
    simp only [Finsupp.add_apply, fac_p hp hq hpq, fac_q hp hq hpq] at h1 h2
    constructor <;> omega
  · rintro ⟨a, u⟩ _
    simp only [fac_p hp hq hpq, fac_q hp hq hpq]
  · rintro ⟨x, z⟩ h
    rw [mem_coe, mem_Sq hV] at h
    dsimp only at h ⊢
    have hx : x ≠ 0 := by rintro rfl; apply hV; rw [← h]; try simp
    have hz : z ≠ 0 := by rintro rfl; apply hV; rw [← h]; try simp
    have hxd : x ∣ p ^ 4 * q ^ n := ⟨x * z, by rw [← h]; ring⟩
    have hzd : z ∣ p ^ 4 * q ^ n := ⟨x * x, by rw [← h]; ring⟩
    have hf := congrArg Nat.factorization h
    rw [Nat.factorization_mul (mul_ne_zero hx hx) hz, Nat.factorization_mul hx hx] at hf
    have h1 := congrArg (· p) hf
    have h2 := congrArg (· q) hf
    simp only [Finsupp.add_apply, fac_p hp hq hpq, fac_q hp hq hpq] at h1 h2
    have e1 : 4 - 2 * x.factorization p = z.factorization p := by omega
    have e2 : n - 2 * x.factorization q = z.factorization q := by omega
    refine Prod.ext (eq_of_dvd hp hq hpq hxd).symm ?_
    dsimp only
    rw [e1, e2]
    exact (eq_of_dvd hp hq hpq hzd).symm

lemma not_cube (n x : ℕ) : x * x * x ≠ p ^ 4 * q ^ n := by
  intro h
  have hV := ne_zero_V hp hq n
  have hx : x ≠ 0 := by rintro rfl; apply hV; rw [← h]; try simp
  have hf := congrArg (fun m => m.factorization p) h
  simp only [Nat.factorization_mul (mul_ne_zero hx hx) hx, Nat.factorization_mul hx hx,
    Finsupp.add_apply, fac_p hp hq hpq] at hf
  omega

end Specific2

end OMA.A101424Proof

open OMA.A101424Proof OMA.S_oeis_a101424 in
theorem OMA.solution : type_of% @OMA.S_oeis_a101424.main := by
  intro p q hp hq hpq n
  have h6 := sorting_identity (ne_zero_V hp hq n) (fun x => not_cube hp hq hpq n x)
  rw [card_T_V hp hq hpq, card_Sq_V hp hq hpq, card_Tri_four] at h6
  have h2 := two_mul_card_Tri n
  set C := cuboids (p ^ 4 * q ^ n)
  set t := (Tri n).card
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have hd : 2 * m / 2 = m := by omega
    rw [hd] at h6
    have hneg : ((-1 : ℤ)) ^ (2 * m) = 1 := by rw [pow_mul]; simp
    rw [hneg]
    have h6' : (6 * C : ℤ) = 15 * t + 3 * (3 * (m + 1)) := by exact_mod_cast h6
    have h2' : (2 * t : ℤ) = (2 * m + 1) * (2 * m + 2) := by exact_mod_cast h2
    push_cast
    nlinarith
  · have hd : (2 * m + 1) / 2 = m := by omega
    rw [hd] at h6
    have hneg : ((-1 : ℤ)) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; simp
    rw [hneg]
    have h6' : (6 * C : ℤ) = 15 * t + 3 * (3 * (m + 1)) := by exact_mod_cast h6
    have h2' : (2 * t : ℤ) = (2 * m + 1 + 1) * (2 * m + 1 + 2) := by exact_mod_cast h2
    push_cast
    nlinarith
