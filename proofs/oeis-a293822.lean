import OMAStatements.S_oeis_a293822
import Mathlib

/-! Proof for OEIS A293822: Burnside's lemma for the rotation group `ℤ/5`: the identity fixes
`C(n-1, 4) - 5 C(⌊n/2⌋, 4)` pentagons (compositions of `n` into 5 parts, minus those with a side
`≥ n/2`; at most one side can be that long) and each non-trivial rotation fixes only the regular
pentagon when `5 ∣ n`. So `120 a(n) = (n-1)(n-2)(n-3)(n-4) - 5 m(m-1)(m-2)(m-3) + 96 [5 ∣ n]`,
`m = ⌊n/2⌋`. The denominator is `(1 - x^2)^4 (1 - x^5)`; coefficients are compared directly for
`n < 23` and by cases on `n mod 10` beyond.
Credit: Sudharsan Rajendiran -/

namespace OMA.P293822
open OMA.S_oeis_a293822 Finset

lemma mem_Q {n : ℕ} {v : Fin 5 → ℕ} :
    v ∈ Q n ↔ (∀ i, 0 < v i ∧ 2 * v i < n) ∧ v 0 + v 1 + v 2 + v 3 + v 4 = n := by
  simp only [Q, mem_filter, Fintype.mem_piFinset, mem_range, Fin.sum_univ_five]
  constructor
  · exact fun h => h.2
  · intro h; refine ⟨fun i => ?_, h⟩
    have := h.1 i; omega

abbrev G := Multiplicative (Fin 5)
abbrev X (n : ℕ) := {v : Fin 5 → ℕ // v ∈ Q n}

lemma rot_mem {n : ℕ} (k : Fin 5) {v : Fin 5 → ℕ} (hv : v ∈ Q n) : (fun i => v (i + k)) ∈ Q n := by
  simp only [Q, Finset.mem_filter, Fintype.mem_piFinset] at hv ⊢
  refine ⟨fun i => hv.1 _, fun i => hv.2.1 _, ?_⟩
  rw [← hv.2.2]; exact Equiv.sum_comp (Equiv.addRight k) v

instance act (n : ℕ) : MulAction G (X n) where
  smul g x := ⟨fun i => x.1 (i + Multiplicative.toAdd g), rot_mem _ x.2⟩
  one_smul x := by
    apply Subtype.ext; funext i
    show x.1 (i + Multiplicative.toAdd 1) = _
    simp
  mul_smul g h x := by
    apply Subtype.ext; funext i
    show x.1 (i + Multiplicative.toAdd (g * h)) = x.1 (i + Multiplicative.toAdd g + Multiplicative.toAdd h)
    rw [toAdd_mul, add_assoc]

open Classical in
noncomputable def cls (n : ℕ) (v : Fin 5 → ℕ) : Finset (Fin 5 → ℕ) :=
  (Q n).filter (fun w => ∃ k : Fin 5, w = fun i => v (i + k))

lemma cls_rot (n : ℕ) (v : Fin 5 → ℕ) (g : Fin 5) : cls n (fun i => v (i + g)) = cls n v := by
  ext w
  simp only [cls, Finset.mem_filter]
  constructor
  · rintro ⟨hw, k, rfl⟩
    exact ⟨hw, k + g, by funext i; simp [add_assoc]⟩
  · rintro ⟨hw, k, rfl⟩
    exact ⟨hw, k - g, by funext i; simp [add_assoc]⟩

open Classical in
lemma a_eq (n : ℕ) : a n = Fintype.card (MulAction.orbitRel.Quotient G (X n)) := by
  let F : MulAction.orbitRel.Quotient G (X n) → Finset (Fin 5 → ℕ) :=
    Quotient.lift (fun x : X n => cls n x.1) (fun x y hxy => by
      obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 hxy
      exact cls_rot n y.1 (Multiplicative.toAdd g))
  have hF : Function.Injective F := by
    intro x y hxy
    induction x using Quotient.inductionOn with | h x => ?_
    induction y using Quotient.inductionOn with | h y => ?_
    have hx : x.1 ∈ cls n x.1 := by
      simp only [cls, Finset.mem_filter]; exact ⟨x.2, 0, by funext i; simp⟩
    have hxy' : cls n x.1 = cls n y.1 := hxy
    rw [hxy'] at hx
    simp only [cls, Finset.mem_filter] at hx
    obtain ⟨-, k, hk⟩ := hx
    apply Quotient.sound
    show x ∈ MulAction.orbit G y
    exact ⟨Multiplicative.ofAdd k, Subtype.ext (by rw [hk]; rfl)⟩
  have : (Q n).image (fun v => (Q n).filter (fun w => ∃ k : Fin 5, w = fun i => v (i + k))) =
      Finset.univ.image F := by
    ext s
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨Quotient.mk _ ⟨v, hv⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      induction x using Quotient.inductionOn with
      | h x => exact ⟨x.1, x.2, rfl⟩
  unfold a
  rw [this, Finset.card_image_of_injective _ hF, Finset.card_univ]

open Classical in
noncomputable def fixCount (n : ℕ) (g : G) : ℕ :=
  (Finset.univ.filter (fun x : X n => g • x = x)).card

lemma fix_iff {n : ℕ} (k : Fin 5) (x : X n) :
    (Multiplicative.ofAdd k : G) • x = x ↔ ∀ i, x.1 (i + k) = x.1 i := by
  constructor
  · intro h i; exact congrArg (fun y : X n => y.1 i) h
  · intro h; exact Subtype.ext (funext h)

lemma const_of_fix (v : Fin 5 → ℕ) (k : Fin 5) (hk : k ≠ 0) (h : ∀ i, v (i + k) = v i) :
    ∀ i, v i = v 0 := by
  have hk' : ∀ k : Fin 5, k ≠ 0 → k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by decide
  rcases hk' k hk with rfl | rfl | rfl | rfl
  · have h0 := h 0; rw [show (0 : Fin 5) + 1 = 1 from rfl] at h0
    have h1 := h 1; rw [show (1 : Fin 5) + 1 = 2 from rfl] at h1
    have h2 := h 2; rw [show (2 : Fin 5) + 1 = 3 from rfl] at h2
    have h3 := h 3; rw [show (3 : Fin 5) + 1 = 4 from rfl] at h3
    have h4 := h 4; rw [show (4 : Fin 5) + 1 = 0 from rfl] at h4
    intro i; fin_cases i <;> simp <;> omega
  · have h0 := h 0; rw [show (0 : Fin 5) + 2 = 2 from rfl] at h0
    have h1 := h 1; rw [show (1 : Fin 5) + 2 = 3 from rfl] at h1
    have h2 := h 2; rw [show (2 : Fin 5) + 2 = 4 from rfl] at h2
    have h3 := h 3; rw [show (3 : Fin 5) + 2 = 0 from rfl] at h3
    have h4 := h 4; rw [show (4 : Fin 5) + 2 = 1 from rfl] at h4
    intro i; fin_cases i <;> simp <;> omega
  · have h0 := h 0; rw [show (0 : Fin 5) + 3 = 3 from rfl] at h0
    have h1 := h 1; rw [show (1 : Fin 5) + 3 = 4 from rfl] at h1
    have h2 := h 2; rw [show (2 : Fin 5) + 3 = 0 from rfl] at h2
    have h3 := h 3; rw [show (3 : Fin 5) + 3 = 1 from rfl] at h3
    have h4 := h 4; rw [show (4 : Fin 5) + 3 = 2 from rfl] at h4
    intro i; fin_cases i <;> simp <;> omega
  · have h0 := h 0; rw [show (0 : Fin 5) + 4 = 4 from rfl] at h0
    have h1 := h 1; rw [show (1 : Fin 5) + 4 = 0 from rfl] at h1
    have h2 := h 2; rw [show (2 : Fin 5) + 4 = 1 from rfl] at h2
    have h3 := h 3; rw [show (3 : Fin 5) + 4 = 2 from rfl] at h3
    have h4 := h 4; rw [show (4 : Fin 5) + 4 = 3 from rfl] at h4
    intro i; fin_cases i <;> simp <;> omega

open Classical in
lemma fix_k (n : ℕ) (hn : 1 ≤ n) (k : Fin 5) (hk : k ≠ 0) :
    fixCount n (Multiplicative.ofAdd k) = if 5 ∣ n then 1 else 0 := by
  unfold fixCount
  have key : ∀ x : X n, (Multiplicative.ofAdd k : G) • x = x → ∀ i, 5 * x.1 i = n := by
    intro x h i
    rw [fix_iff] at h
    have hc := const_of_fix x.1 k hk h
    have hs := (mem_Q.1 x.2).2
    rw [hc 1, hc 2, hc 3, hc 4] at hs
    rw [hc i]; omega
  split_ifs with h5
  · obtain ⟨q, rfl⟩ := h5
    have hq : 0 < q := by omega
    rw [card_eq_one]
    have hm : (fun _ : Fin 5 => q) ∈ Q (5 * q) := by
      rw [mem_Q]; exact ⟨fun i => ⟨hq, by omega⟩, by ring⟩
    refine ⟨⟨_, hm⟩, ?_⟩
    ext x; simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro hx; apply Subtype.ext; funext i; have := key x hx i; simp only; omega
    · rintro rfl; rw [fix_iff]; intro i; rfl
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro x _ hx
    exact h5 ⟨x.1 0, (key x hx 0).symm⟩

open Classical in
lemma fix_zero_eq (n : ℕ) : fixCount n (Multiplicative.ofAdd 0) = (Q n).card := by
  unfold fixCount
  rw [Finset.filter_true_of_mem (fun x _ => (fix_iff 0 x).2 (fun i => by simp)),
    Finset.card_univ, Fintype.card_coe]

/-! ## Counting pentagons -/

def comp (n : ℕ) : Finset (Fin 5 → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (n + 1)).filter (fun v => (∀ i, 0 < v i) ∧ ∑ i, v i = n)

lemma mem_comp {n : ℕ} {v : Fin 5 → ℕ} :
    v ∈ comp n ↔ (∀ i, 0 < v i) ∧ v 0 + v 1 + v 2 + v 3 + v 4 = n := by
  simp only [comp, mem_filter, Fintype.mem_piFinset, mem_range, Fin.sum_univ_five]
  constructor
  · exact fun h => h.2
  · intro h; refine ⟨fun i => ?_, h⟩
    have := h.1 0; have := h.1 1; have := h.1 2; have := h.1 3; have := h.1 4
    fin_cases i <;> simp <;> omega

lemma card_filter_prod {α β : Type*} (A : Finset α) (B : Finset β) (P : α × β → Prop)
    [DecidablePred P] : ((A ×ˢ B).filter P).card = ∑ a ∈ A, (B.filter (fun b => P (a, b))).card := by
  rw [card_filter, sum_product]
  simp only [card_filter]

def D3N (s : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (range (s + 1) ×ˢ range (s + 1) ×ˢ range (s + 1)).filter (fun t => t.1 + t.2.1 + t.2.2 ≤ s)

def D4N (s : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (range (s + 1) ×ˢ range (s + 1) ×ˢ range (s + 1) ×ˢ range (s + 1)).filter
    (fun t => t.1 + t.2.1 + t.2.2.1 + t.2.2.2 ≤ s)

lemma SC (t : ℕ) : 2 * ∑ j ∈ range (t + 1), (j + 1) = (t + 1) * (t + 2) := by
  induction t with
  | zero => simp
  | succ t ih => rw [sum_range_succ, mul_add, ih]; ring

lemma SD (s : ℕ) : 3 * ∑ j ∈ range (s + 1), ((j + 1) * (j + 2)) = (s + 1) * (s + 2) * (s + 3) := by
  induction s with
  | zero => simp
  | succ s ih => rw [sum_range_succ, mul_add, ih]; ring

lemma SE (s : ℕ) : 4 * ∑ j ∈ range (s + 1), ((j + 1) * (j + 2) * (j + 3)) =
    (s + 1) * (s + 2) * (s + 3) * (s + 4) := by
  induction s with
  | zero => simp
  | succ s ih => rw [sum_range_succ, mul_add, ih]; ring

lemma D2N (s t : ℕ) (ht : t ≤ s) :
    2 * ((range (s + 1) ×ˢ range (s + 1)).filter (fun p : ℕ × ℕ => p.1 + p.2 ≤ t)).card =
      (t + 1) * (t + 2) := by
  rw [card_filter_prod]
  have hc : ∀ b ∈ range (s + 1), ((range (s + 1)).filter (fun c => (b, c).1 + (b, c).2 ≤ t)).card =
      if b ≤ t then t - b + 1 else 0 := by
    intro b _
    split_ifs with hb
    · rw [show (range (s + 1)).filter (fun c => (b, c).1 + (b, c).2 ≤ t) = range (t - b + 1) by
        ext c; simp only [mem_filter, mem_range]; omega, card_range]
    · rw [card_eq_zero, filter_eq_empty_iff]; intro c _; simp only; omega
  rw [sum_congr rfl hc, ← sum_subset (s₁ := range (t + 1)) (fun b hb => by
      simp only [mem_range] at hb ⊢; omega) (fun b _ hb => by
      simp only [mem_range] at hb; rw [if_neg (by omega)])]
  rw [sum_congr rfl (fun b hb => by simp only [mem_range] at hb; rw [if_pos (by omega)])]
  have := sum_range_reflect (fun j => j + 1) (t + 1)
  simp only [show t + 1 - 1 = t by omega] at this
  rw [this]; exact SC t

lemma D3B (s t : ℕ) (ht : t ≤ s) :
    6 * ((range (s + 1) ×ˢ range (s + 1) ×ˢ range (s + 1)).filter
      (fun q : ℕ × ℕ × ℕ => q.1 + q.2.1 + q.2.2 ≤ t)).card = (t + 1) * (t + 2) * (t + 3) := by
  rw [card_filter_prod]
  have hc : ∀ a ∈ range (s + 1), 2 * ((range (s + 1) ×ˢ range (s + 1)).filter
      (fun q : ℕ × ℕ => (a, q).1 + (a, q).2.1 + (a, q).2.2 ≤ t)).card =
      if a ≤ t then (t - a + 1) * (t - a + 2) else 0 := by
    intro a ha
    split_ifs with h
    · rw [← D2N s (t - a) (by omega)]
      congr 2; apply filter_congr; intro q _; simp only; omega
    · rw [show ((range (s + 1) ×ˢ range (s + 1)).filter
          (fun q : ℕ × ℕ => (a, q).1 + (a, q).2.1 + (a, q).2.2 ≤ t)) = ∅ by
        rw [filter_eq_empty_iff]; intro q _; simp only; omega]; rfl
  rw [show 6 = 3 * 2 by rfl, mul_assoc, mul_sum, sum_congr rfl hc,
    ← sum_subset (s₁ := range (t + 1)) (fun b hb => by simp only [mem_range] at hb ⊢; omega)
      (fun b _ hb => by simp only [mem_range] at hb; rw [if_neg (by omega)])]
  rw [sum_congr rfl (fun b hb => by simp only [mem_range] at hb; rw [if_pos (by omega)])]
  have := sum_range_reflect (fun j => (j + 1) * (j + 2)) (t + 1)
  simp only [show t + 1 - 1 = t by omega] at this
  rw [this]; exact SD t

lemma card_D4N (s : ℕ) : 24 * (D4N s).card = (s + 1) * (s + 2) * (s + 3) * (s + 4) := by
  unfold D4N
  rw [card_filter_prod]
  have hc : ∀ a ∈ range (s + 1), 6 * ((range (s + 1) ×ˢ range (s + 1) ×ˢ range (s + 1)).filter
      (fun q : ℕ × ℕ × ℕ => (a, q).1 + (a, q).2.1 + (a, q).2.2.1 + (a, q).2.2.2 ≤ s)).card =
      (s - a + 1) * (s - a + 2) * (s - a + 3) := by
    intro a ha
    simp only [mem_range] at ha
    rw [← D3B s (s - a) (by omega)]
    congr 2; apply filter_congr; intro q _; simp only; omega
  rw [show 24 = 4 * 6 by rfl, mul_assoc, mul_sum, sum_congr rfl hc]
  have := sum_range_reflect (fun j => (j + 1) * (j + 2) * (j + 3)) (s + 1)
  simp only [show s + 1 - 1 = s by omega] at this
  rw [this]; exact SE s

lemma card_comp (n : ℕ) (hn : 5 ≤ n) : (comp n).card = (D4N (n - 5)).card := by
  apply card_nbij' (fun v => (v 0 - 1, v 1 - 1, v 2 - 1, v 3 - 1))
    (fun t => ![t.1 + 1, t.2.1 + 1, t.2.2.1 + 1, t.2.2.2 + 1, n - 4 - t.1 - t.2.1 - t.2.2.1 - t.2.2.2])
  · intro v hv
    rw [mem_coe, mem_comp] at hv
    have := hv.1 0; have := hv.1 1; have := hv.1 2; have := hv.1 3; have := hv.1 4
    simp only [mem_coe, D4N, mem_filter, mem_product, mem_range]; omega
  · intro t ht
    simp only [mem_coe, D4N, mem_filter, mem_product, mem_range] at ht
    rw [mem_coe, mem_comp]
    refine ⟨fun i => ?_, by simp; omega⟩
    fin_cases i <;> simp <;> omega
  · intro v hv
    rw [mem_coe, mem_comp] at hv
    have := hv.1 0; have := hv.1 1; have := hv.1 2; have := hv.1 3; have := hv.1 4
    funext i; fin_cases i <;> simp <;> omega
  · intro t _; simp

def E (n : ℕ) (k : Fin 5) : Finset (Fin 5 → ℕ) := (comp n).filter (fun v => n ≤ 2 * v k)

lemma card_E0 (n : ℕ) : 24 * (E n 0).card = (n / 2) * (n / 2 - 1) * (n / 2 - 2) * (n / 2 - 3) := by
  rcases Nat.lt_or_ge (n / 2) 4 with h | h
  · rw [show (E n 0).card = 0 by
      rw [card_eq_zero, E, filter_eq_empty_iff]
      intro v hv h'
      rw [mem_comp] at hv
      have := hv.1 1; have := hv.1 2; have := hv.1 3; have := hv.1 4; omega]
    interval_cases (n / 2) <;> rfl
  · rw [show (E n 0).card = (D4N (n / 2 - 4)).card by
      apply card_nbij' (fun v => (v 1 - 1, v 2 - 1, v 3 - 1, v 4 - 1))
        (fun t => ![n - 4 - t.1 - t.2.1 - t.2.2.1 - t.2.2.2, t.1 + 1, t.2.1 + 1, t.2.2.1 + 1, t.2.2.2 + 1])
      · intro v hv
        simp only [mem_coe, E, mem_filter, mem_comp] at hv
        have := hv.1.1 0; have := hv.1.1 1; have := hv.1.1 2; have := hv.1.1 3; have := hv.1.1 4
        simp only [mem_coe, D4N, mem_filter, mem_product, mem_range]; omega
      · intro t ht
        simp only [mem_coe, D4N, mem_filter, mem_product, mem_range] at ht
        simp only [mem_coe, E, mem_filter, mem_comp]
        refine ⟨⟨fun i => ?_, by simp; omega⟩, by simp; omega⟩
        fin_cases i <;> simp <;> omega
      · intro v hv
        simp only [mem_coe, E, mem_filter, mem_comp] at hv
        have := hv.1.1 0; have := hv.1.1 1; have := hv.1.1 2; have := hv.1.1 3; have := hv.1.1 4
        funext i; fin_cases i <;> simp <;> omega
      · intro t _; simp]
    rw [card_D4N]
    obtain ⟨m, hm⟩ : ∃ m, n / 2 = m + 4 := ⟨n / 2 - 4, by omega⟩
    rw [hm, show m + 4 - 4 = m by omega, show m + 4 - 1 = m + 3 by omega,
      show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega]
    ring

lemma rot_comp {n : ℕ} (k : Fin 5) {v : Fin 5 → ℕ} (hv : v ∈ comp n) : (fun i => v (i + k)) ∈ comp n := by
  simp only [comp, Finset.mem_filter, Fintype.mem_piFinset] at hv ⊢
  refine ⟨fun i => hv.1 _, fun i => hv.2.1 _, ?_⟩
  rw [← hv.2.2]; exact Equiv.sum_comp (Equiv.addRight k) v

lemma card_Ek (n : ℕ) (k : Fin 5) : (E n k).card = (E n 0).card := by
  apply card_nbij' (fun v => fun i => v (i + k)) (fun v => fun i => v (i - k))
  · intro v hv
    simp only [mem_coe, E, mem_filter] at hv ⊢
    exact ⟨rot_comp k hv.1, by simpa using hv.2⟩
  · intro v hv
    simp only [mem_coe, E, mem_filter] at hv ⊢
    exact ⟨by simpa [sub_eq_add_neg] using rot_comp (-k) hv.1, by simpa using hv.2⟩
  · intro v _; funext i; simp
  · intro v _; funext i; simp

/-- at most one side can be `≥ n / 2`. -/
lemma two_big {n : ℕ} {v : Fin 5 → ℕ} (hv : v ∈ comp n) {i j : Fin 5} (hij : i ≠ j)
    (hi : n ≤ 2 * v i) (hj : n ≤ 2 * v j) : False := by
  rw [mem_comp] at hv
  have := hv.1 0; have := hv.1 1; have := hv.1 2; have := hv.1 3; have := hv.1 4
  fin_cases i <;> fin_cases j <;> simp at hij hi hj <;> omega

lemma split (n : ℕ) : (comp n).card = (Q n).card + 5 * (E n 0).card := by
  have hQ : (comp n).filter (fun v => ∀ i, ¬ n ≤ 2 * v i) = Q n := by
    ext v; simp only [mem_filter, mem_comp, mem_Q, not_le]
    constructor
    · rintro ⟨⟨h, hs⟩, h'⟩; exact ⟨fun i => ⟨h i, h' i⟩, hs⟩
    · rintro ⟨h, hs⟩; exact ⟨⟨fun i => (h i).1, hs⟩, fun i => (h i).2⟩
  have hU : (comp n).filter (fun v => ¬ ∀ i, ¬ n ≤ 2 * v i) =
      (univ : Finset (Fin 5)).biUnion (fun k => E n k) := by
    ext v; simp only [mem_filter, mem_biUnion, mem_univ, true_and, E, not_forall, not_not]
    constructor
    · rintro ⟨hv, k, hk⟩; exact ⟨k, hv, hk⟩
    · rintro ⟨k, hv, hk⟩; exact ⟨hv, k, hk⟩
  have hd : ((univ : Finset (Fin 5)) : Set (Fin 5)).PairwiseDisjoint (fun k => E n k) := by
    intro i _ j _ hij
    rw [Function.onFun, disjoint_left]
    intro v hvi hvj
    simp only [E, mem_filter] at hvi hvj
    exact two_big hvi.1 hij hvi.2 hvj.2
  have s0 := card_filter_add_card_filter_not (s := comp n) (fun v => ∀ i, ¬ n ≤ 2 * v i)
  rw [hQ, hU, card_biUnion hd] at s0
  simp only [card_Ek n] at s0
  rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at s0
  omega

open Classical in
lemma burnside (n : ℕ) (hn : 1 ≤ n) : Fintype.card (MulAction.orbitRel.Quotient G (X n)) * 5 =
    (Q n).card + 4 * (if 5 ∣ n then 1 else 0) := by
  have hb := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (X n)
  have hG : Fintype.card G = 5 := by simp
  have hfix : ∀ g : G, Fintype.card (MulAction.fixedBy (X n) g) = fixCount n g := by
    intro g
    unfold fixCount
    rw [← Fintype.card_subtype]; rfl
  have hsum : (∑ g : G, fixCount n g) = ∑ k : Fin 5, fixCount n (Multiplicative.ofAdd k) :=
    (Fintype.sum_equiv Multiplicative.ofAdd _ _ (fun _ => rfl)).symm
  rw [hG] at hb
  simp only [hfix] at hb
  rw [hsum, Fin.sum_univ_five, fix_zero_eq, fix_k n hn 1 (by decide), fix_k n hn 2 (by decide),
    fix_k n hn 3 (by decide), fix_k n hn 4 (by decide)] at hb
  change _ = Fintype.card (MulAction.orbitRel.Quotient G (X n)) * 5 at hb
  omega

lemma closed (N : ℕ) (hN : 5 ≤ N) : 120 * a N + 5 * ((N / 2) * (N / 2 - 1) * (N / 2 - 2) * (N / 2 - 3)) =
    (N - 1) * (N - 2) * (N - 3) * (N - 4) + 96 * (if 5 ∣ N then 1 else 0) := by
  have hb := burnside N (by omega)
  rw [← a_eq] at hb
  have hs := split N
  rw [card_comp N hN] at hs
  have h4 := card_D4N (N - 5)
  have hE := card_E0 N
  rw [show N - 5 + 1 = N - 4 by omega, show N - 5 + 2 = N - 3 by omega,
    show N - 5 + 3 = N - 2 by omega, show N - 5 + 4 = N - 1 by omega] at h4
  have : 24 * (Q N).card + 5 * (24 * (E N 0).card) = (N - 4) * (N - 3) * (N - 2) * (N - 1) := by
    rw [← h4, hs]; ring
  rw [hE] at this
  nlinarith

lemma a_small (N : ℕ) (hN : N < 5) : a N = 0 := by
  have : Q N = ∅ := by
    rw [Q, filter_eq_empty_iff]
    intro v _ hv
    rw [Fin.sum_univ_five] at hv
    have := (hv.1 0).1; have := (hv.1 1).1; have := (hv.1 2).1; have := (hv.1 3).1; have := (hv.1 4).1
    omega
  unfold a; rw [this]; simp

/-- the closed form, over `ℚ`. -/
noncomputable def F (N : ℕ) : ℚ :=
  if N < 5 then 0 else
    (((N : ℚ) - 1) * (N - 2) * (N - 3) * (N - 4)
      - 5 * (((N / 2 : ℕ) : ℚ) * ((N / 2 : ℕ) - 1) * ((N / 2 : ℕ) - 2) * ((N / 2 : ℕ) - 3))
      + 96 * (if 5 ∣ N then 1 else 0)) / 120

lemma a_eq_F (N : ℕ) : (a N : ℚ) = F N := by
  unfold F
  by_cases h : N < 5
  · rw [if_pos h, a_small N h]; simp
  · rw [if_neg h]
    have hc := closed N (by omega)
    have e1 : ((N - 1 : ℕ) : ℚ) = N - 1 := by rw [Nat.cast_sub (by omega)]; simp
    have e2 : ((N - 2 : ℕ) : ℚ) = N - 2 := by rw [Nat.cast_sub (by omega)]; simp
    have e3 : ((N - 3 : ℕ) : ℚ) = N - 3 := by rw [Nat.cast_sub (by omega)]; simp
    have e4 : ((N - 4 : ℕ) : ℚ) = N - 4 := by rw [Nat.cast_sub (by omega)]; simp
    have hM : (((N / 2) * (N / 2 - 1) * (N / 2 - 2) * (N / 2 - 3) : ℕ) : ℚ) =
        ((N / 2 : ℕ) : ℚ) * ((N / 2 : ℕ) - 1) * ((N / 2 : ℕ) - 2) * ((N / 2 : ℕ) - 3) := by
      rcases Nat.lt_or_ge (N / 2) 4 with hm | hm
      · interval_cases (N / 2) <;> norm_num
      · rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_sub (by omega),
          Nat.cast_sub (by omega)]
        simp
    by_cases h5 : 5 ∣ N
    · rw [if_pos h5] at hc ⊢
      simp only [mul_one] at hc
      have hq : (120 * (a N : ℚ) + 5 * (((N / 2) * (N / 2 - 1) * (N / 2 - 2) * (N / 2 - 3) : ℕ) : ℚ)) =
          ((N - 1 : ℕ) : ℚ) * ((N - 2 : ℕ) : ℚ) * ((N - 3 : ℕ) : ℚ) * ((N - 4 : ℕ) : ℚ) + 96 := by
        exact_mod_cast hc
      rw [hM, e1, e2, e3, e4] at hq
      linear_combination hq / 120
    · rw [if_neg h5] at hc ⊢
      simp only [mul_zero, add_zero] at hc
      have hq : (120 * (a N : ℚ) + 5 * (((N / 2) * (N / 2 - 1) * (N / 2 - 2) * (N / 2 - 3) : ℕ) : ℚ)) =
          ((N - 1 : ℕ) : ℚ) * ((N - 2 : ℕ) : ℚ) * ((N - 3 : ℕ) : ℚ) * ((N - 4 : ℕ) : ℚ) := by
        exact_mod_cast hc
      rw [hM, e1, e2, e3, e4] at hq
      linear_combination hq / 120

lemma F_val (p c : ℕ) (hc : 5 ≤ c) : F (10 * p + c) =
    ((((10 * p + c : ℕ) : ℚ) - 1) * ((10 * p + c : ℕ) - 2) * ((10 * p + c : ℕ) - 3) * ((10 * p + c : ℕ) - 4)
      - 5 * (((5 * p + c / 2 : ℕ) : ℚ) * ((5 * p + c / 2 : ℕ) - 1) * ((5 * p + c / 2 : ℕ) - 2) *
        ((5 * p + c / 2 : ℕ) - 3)) + 96 * (if 5 ∣ 10 * p + c then 1 else 0)) / 120 := by
  unfold F
  rw [if_neg (by omega), show (10 * p + c) / 2 = 5 * p + c / 2 by omega]

end OMA.P293822

namespace OMA.P293822

lemma F0 : OMA.P293822.F 0 = 0 := by norm_num [OMA.P293822.F]
lemma F1 : OMA.P293822.F 1 = 0 := by norm_num [OMA.P293822.F]
lemma F2 : OMA.P293822.F 2 = 0 := by norm_num [OMA.P293822.F]
lemma F3 : OMA.P293822.F 3 = 0 := by norm_num [OMA.P293822.F]
lemma F4 : OMA.P293822.F 4 = 0 := by norm_num [OMA.P293822.F]
lemma F5 : OMA.P293822.F 5 = 1 := by norm_num [OMA.P293822.F]
lemma F6 : OMA.P293822.F 6 = 1 := by norm_num [OMA.P293822.F]
lemma F7 : OMA.P293822.F 7 = 3 := by norm_num [OMA.P293822.F]
lemma F8 : OMA.P293822.F 8 = 6 := by norm_num [OMA.P293822.F]
lemma F9 : OMA.P293822.F 9 = 13 := by norm_num [OMA.P293822.F]
lemma F10 : OMA.P293822.F 10 = 21 := by norm_num [OMA.P293822.F]
lemma F11 : OMA.P293822.F 11 = 37 := by norm_num [OMA.P293822.F]
lemma F12 : OMA.P293822.F 12 = 51 := by norm_num [OMA.P293822.F]
lemma F13 : OMA.P293822.F 13 = 84 := by norm_num [OMA.P293822.F]
lemma F14 : OMA.P293822.F 14 = 108 := by norm_num [OMA.P293822.F]
lemma F15 : OMA.P293822.F 15 = 166 := by norm_num [OMA.P293822.F]
lemma F16 : OMA.P293822.F 16 = 203 := by norm_num [OMA.P293822.F]
lemma F17 : OMA.P293822.F 17 = 294 := by norm_num [OMA.P293822.F]
lemma F18 : OMA.P293822.F 18 = 350 := by norm_num [OMA.P293822.F]
lemma F19 : OMA.P293822.F 19 = 486 := by norm_num [OMA.P293822.F]
lemma F20 : OMA.P293822.F 20 = 566 := by norm_num [OMA.P293822.F]
lemma F21 : OMA.P293822.F 21 = 759 := by norm_num [OMA.P293822.F]
lemma F22 : OMA.P293822.F 22 = 867 := by norm_num [OMA.P293822.F]

lemma rec0 (p : ℕ) : OMA.P293822.F (10 * p + 23) - 4 * OMA.P293822.F (10 * p + 21) + 6 * OMA.P293822.F (10 * p + 19) - OMA.P293822.F (10 * p + 18) - 4 * OMA.P293822.F (10 * p + 17) + 4 * OMA.P293822.F (10 * p + 16) + OMA.P293822.F (10 * p + 15) - 6 * OMA.P293822.F (10 * p + 14) + 4 * OMA.P293822.F (10 * p + 12) - OMA.P293822.F (10 * p + 10) = 0 := by
  rw [OMA.P293822.F_val p 23 (by norm_num), OMA.P293822.F_val p 21 (by norm_num), OMA.P293822.F_val p 19 (by norm_num), OMA.P293822.F_val p 18 (by norm_num), OMA.P293822.F_val p 17 (by norm_num), OMA.P293822.F_val p 16 (by norm_num), OMA.P293822.F_val p 15 (by norm_num), OMA.P293822.F_val p 14 (by norm_num), OMA.P293822.F_val p 12 (by norm_num), OMA.P293822.F_val p 10 (by norm_num)]
  rw [if_neg (show ¬ 5 ∣ 10 * p + 23 by omega), if_neg (show ¬ 5 ∣ 10 * p + 21 by omega), if_neg (show ¬ 5 ∣ 10 * p + 19 by omega), if_neg (show ¬ 5 ∣ 10 * p + 18 by omega), if_neg (show ¬ 5 ∣ 10 * p + 17 by omega), if_neg (show ¬ 5 ∣ 10 * p + 16 by omega), if_pos (show 5 ∣ 10 * p + 15 by omega), if_neg (show ¬ 5 ∣ 10 * p + 14 by omega), if_neg (show ¬ 5 ∣ 10 * p + 12 by omega), if_pos (show 5 ∣ 10 * p + 10 by omega)]
  simp only [Nat.reduceDiv]
  push_cast
  ring

lemma rec1 (p : ℕ) : OMA.P293822.F (10 * p + 24) - 4 * OMA.P293822.F (10 * p + 22) + 6 * OMA.P293822.F (10 * p + 20) - OMA.P293822.F (10 * p + 19) - 4 * OMA.P293822.F (10 * p + 18) + 4 * OMA.P293822.F (10 * p + 17) + OMA.P293822.F (10 * p + 16) - 6 * OMA.P293822.F (10 * p + 15) + 4 * OMA.P293822.F (10 * p + 13) - OMA.P293822.F (10 * p + 11) = 0 := by
  rw [OMA.P293822.F_val p 24 (by norm_num), OMA.P293822.F_val p 22 (by norm_num), OMA.P293822.F_val p 20 (by norm_num), OMA.P293822.F_val p 19 (by norm_num), OMA.P293822.F_val p 18 (by norm_num), OMA.P293822.F_val p 17 (by norm_num), OMA.P293822.F_val p 16 (by norm_num), OMA.P293822.F_val p 15 (by norm_num), OMA.P293822.F_val p 13 (by norm_num), OMA.P293822.F_val p 11 (by norm_num)]
  rw [if_neg (show ¬ 5 ∣ 10 * p + 24 by omega), if_neg (show ¬ 5 ∣ 10 * p + 22 by omega), if_pos (show 5 ∣ 10 * p + 20 by omega), if_neg (show ¬ 5 ∣ 10 * p + 19 by omega), if_neg (show ¬ 5 ∣ 10 * p + 18 by omega), if_neg (show ¬ 5 ∣ 10 * p + 17 by omega), if_neg (show ¬ 5 ∣ 10 * p + 16 by omega), if_pos (show 5 ∣ 10 * p + 15 by omega), if_neg (show ¬ 5 ∣ 10 * p + 13 by omega), if_neg (show ¬ 5 ∣ 10 * p + 11 by omega)]
  simp only [Nat.reduceDiv]
  push_cast
  ring

lemma rec2 (p : ℕ) : OMA.P293822.F (10 * p + 25) - 4 * OMA.P293822.F (10 * p + 23) + 6 * OMA.P293822.F (10 * p + 21) - OMA.P293822.F (10 * p + 20) - 4 * OMA.P293822.F (10 * p + 19) + 4 * OMA.P293822.F (10 * p + 18) + OMA.P293822.F (10 * p + 17) - 6 * OMA.P293822.F (10 * p + 16) + 4 * OMA.P293822.F (10 * p + 14) - OMA.P293822.F (10 * p + 12) = 0 := by
  rw [OMA.P293822.F_val p 25 (by norm_num), OMA.P293822.F_val p 23 (by norm_num), OMA.P293822.F_val p 21 (by norm_num), OMA.P293822.F_val p 20 (by norm_num), OMA.P293822.F_val p 19 (by norm_num), OMA.P293822.F_val p 18 (by norm_num), OMA.P293822.F_val p 17 (by norm_num), OMA.P293822.F_val p 16 (by norm_num), OMA.P293822.F_val p 14 (by norm_num), OMA.P293822.F_val p 12 (by norm_num)]
  rw [if_pos (show 5 ∣ 10 * p + 25 by omega), if_neg (show ¬ 5 ∣ 10 * p + 23 by omega), if_neg (show ¬ 5 ∣ 10 * p + 21 by omega), if_pos (show 5 ∣ 10 * p + 20 by omega), if_neg (show ¬ 5 ∣ 10 * p + 19 by omega), if_neg (show ¬ 5 ∣ 10 * p + 18 by omega), if_neg (show ¬ 5 ∣ 10 * p + 17 by omega), if_neg (show ¬ 5 ∣ 10 * p + 16 by omega), if_neg (show ¬ 5 ∣ 10 * p + 14 by omega), if_neg (show ¬ 5 ∣ 10 * p + 12 by omega)]
  simp only [Nat.reduceDiv]
  push_cast
  ring

lemma rec3 (p : ℕ) : OMA.P293822.F (10 * p + 26) - 4 * OMA.P293822.F (10 * p + 24) + 6 * OMA.P293822.F (10 * p + 22) - OMA.P293822.F (10 * p + 21) - 4 * OMA.P293822.F (10 * p + 20) + 4 * OMA.P293822.F (10 * p + 19) + OMA.P293822.F (10 * p + 18) - 6 * OMA.P293822.F (10 * p + 17) + 4 * OMA.P293822.F (10 * p + 15) - OMA.P293822.F (10 * p + 13) = 0 := by
  rw [OMA.P293822.F_val p 26 (by norm_num), OMA.P293822.F_val p 24 (by norm_num), OMA.P293822.F_val p 22 (by norm_num), OMA.P293822.F_val p 21 (by norm_num), OMA.P293822.F_val p 20 (by norm_num), OMA.P293822.F_val p 19 (by norm_num), OMA.P293822.F_val p 18 (by norm_num), OMA.P293822.F_val p 17 (by norm_num), OMA.P293822.F_val p 15 (by norm_num), OMA.P293822.F_val p 13 (by norm_num)]
  rw [if_neg (show ¬ 5 ∣ 10 * p + 26 by omega), if_neg (show ¬ 5 ∣ 10 * p + 24 by omega), if_neg (show ¬ 5 ∣ 10 * p + 22 by omega), if_neg (show ¬ 5 ∣ 10 * p + 21 by omega), if_pos (show 5 ∣ 10 * p + 20 by omega), if_neg (show ¬ 5 ∣ 10 * p + 19 by omega), if_neg (show ¬ 5 ∣ 10 * p + 18 by omega), if_neg (show ¬ 5 ∣ 10 * p + 17 by omega), if_pos (show 5 ∣ 10 * p + 15 by omega), if_neg (show ¬ 5 ∣ 10 * p + 13 by omega)]
  simp only [Nat.reduceDiv]
  push_cast
  ring

lemma rec4 (p : ℕ) : OMA.P293822.F (10 * p + 27) - 4 * OMA.P293822.F (10 * p + 25) + 6 * OMA.P293822.F (10 * p + 23) - OMA.P293822.F (10 * p + 22) - 4 * OMA.P293822.F (10 * p + 21) + 4 * OMA.P293822.F (10 * p + 20) + OMA.P293822.F (10 * p + 19) - 6 * OMA.P293822.F (10 * p + 18) + 4 * OMA.P293822.F (10 * p + 16) - OMA.P293822.F (10 * p + 14) = 0 := by
  rw [OMA.P293822.F_val p 27 (by norm_num), OMA.P293822.F_val p 25 (by norm_num), OMA.P293822.F_val p 23 (by norm_num), OMA.P293822.F_val p 22 (by norm_num), OMA.P293822.F_val p 21 (by norm_num), OMA.P293822.F_val p 20 (by norm_num), OMA.P293822.F_val p 19 (by norm_num), OMA.P293822.F_val p 18 (by norm_num), OMA.P293822.F_val p 16 (by norm_num), OMA.P293822.F_val p 14 (by norm_num)]
  rw [if_neg (show ¬ 5 ∣ 10 * p + 27 by omega), if_pos (show 5 ∣ 10 * p + 25 by omega), if_neg (show ¬ 5 ∣ 10 * p + 23 by omega), if_neg (show ¬ 5 ∣ 10 * p + 22 by omega), if_neg (show ¬ 5 ∣ 10 * p + 21 by omega), if_pos (show 5 ∣ 10 * p + 20 by omega), if_neg (show ¬ 5 ∣ 10 * p + 19 by omega), if_neg (show ¬ 5 ∣ 10 * p + 18 by omega), if_neg (show ¬ 5 ∣ 10 * p + 16 by omega), if_neg (show ¬ 5 ∣ 10 * p + 14 by omega)]
  simp only [Nat.reduceDiv]
  push_cast
  ring

lemma rec5 (p : ℕ) : OMA.P293822.F (10 * p + 28) - 4 * OMA.P293822.F (10 * p + 26) + 6 * OMA.P293822.F (10 * p + 24) - OMA.P293822.F (10 * p + 23) - 4 * OMA.P293822.F (10 * p + 22) + 4 * OMA.P293822.F (10 * p + 21) + OMA.P293822.F (10 * p + 20) - 6 * OMA.P293822.F (10 * p + 19) + 4 * OMA.P293822.F (10 * p + 17) - OMA.P293822.F (10 * p + 15) = 0 := by
  rw [OMA.P293822.F_val p 28 (by norm_num), OMA.P293822.F_val p 26 (by norm_num), OMA.P293822.F_val p 24 (by norm_num), OMA.P293822.F_val p 23 (by norm_num), OMA.P293822.F_val p 22 (by norm_num), OMA.P293822.F_val p 21 (by norm_num), OMA.P293822.F_val p 20 (by norm_num), OMA.P293822.F_val p 19 (by norm_num), OMA.P293822.F_val p 17 (by norm_num), OMA.P293822.F_val p 15 (by norm_num)]
  rw [if_neg (show ¬ 5 ∣ 10 * p + 28 by omega), if_neg (show ¬ 5 ∣ 10 * p + 26 by omega), if_neg (show ¬ 5 ∣ 10 * p + 24 by omega), if_neg (show ¬ 5 ∣ 10 * p + 23 by omega), if_neg (show ¬ 5 ∣ 10 * p + 22 by omega), if_neg (show ¬ 5 ∣ 10 * p + 21 by omega), if_pos (show 5 ∣ 10 * p + 20 by omega), if_neg (show ¬ 5 ∣ 10 * p + 19 by omega), if_neg (show ¬ 5 ∣ 10 * p + 17 by omega), if_pos (show 5 ∣ 10 * p + 15 by omega)]
  simp only [Nat.reduceDiv]
  push_cast
  ring

lemma rec6 (p : ℕ) : OMA.P293822.F (10 * p + 29) - 4 * OMA.P293822.F (10 * p + 27) + 6 * OMA.P293822.F (10 * p + 25) - OMA.P293822.F (10 * p + 24) - 4 * OMA.P293822.F (10 * p + 23) + 4 * OMA.P293822.F (10 * p + 22) + OMA.P293822.F (10 * p + 21) - 6 * OMA.P293822.F (10 * p + 20) + 4 * OMA.P293822.F (10 * p + 18) - OMA.P293822.F (10 * p + 16) = 0 := by
  rw [OMA.P293822.F_val p 29 (by norm_num), OMA.P293822.F_val p 27 (by norm_num), OMA.P293822.F_val p 25 (by norm_num), OMA.P293822.F_val p 24 (by norm_num), OMA.P293822.F_val p 23 (by norm_num), OMA.P293822.F_val p 22 (by norm_num), OMA.P293822.F_val p 21 (by norm_num), OMA.P293822.F_val p 20 (by norm_num), OMA.P293822.F_val p 18 (by norm_num), OMA.P293822.F_val p 16 (by norm_num)]
  rw [if_neg (show ¬ 5 ∣ 10 * p + 29 by omega), if_neg (show ¬ 5 ∣ 10 * p + 27 by omega), if_pos (show 5 ∣ 10 * p + 25 by omega), if_neg (show ¬ 5 ∣ 10 * p + 24 by omega), if_neg (show ¬ 5 ∣ 10 * p + 23 by omega), if_neg (show ¬ 5 ∣ 10 * p + 22 by omega), if_neg (show ¬ 5 ∣ 10 * p + 21 by omega), if_pos (show 5 ∣ 10 * p + 20 by omega), if_neg (show ¬ 5 ∣ 10 * p + 18 by omega), if_neg (show ¬ 5 ∣ 10 * p + 16 by omega)]
  simp only [Nat.reduceDiv]
  push_cast
  ring

lemma rec7 (p : ℕ) : OMA.P293822.F (10 * p + 30) - 4 * OMA.P293822.F (10 * p + 28) + 6 * OMA.P293822.F (10 * p + 26) - OMA.P293822.F (10 * p + 25) - 4 * OMA.P293822.F (10 * p + 24) + 4 * OMA.P293822.F (10 * p + 23) + OMA.P293822.F (10 * p + 22) - 6 * OMA.P293822.F (10 * p + 21) + 4 * OMA.P293822.F (10 * p + 19) - OMA.P293822.F (10 * p + 17) = 0 := by
  rw [OMA.P293822.F_val p 30 (by norm_num), OMA.P293822.F_val p 28 (by norm_num), OMA.P293822.F_val p 26 (by norm_num), OMA.P293822.F_val p 25 (by norm_num), OMA.P293822.F_val p 24 (by norm_num), OMA.P293822.F_val p 23 (by norm_num), OMA.P293822.F_val p 22 (by norm_num), OMA.P293822.F_val p 21 (by norm_num), OMA.P293822.F_val p 19 (by norm_num), OMA.P293822.F_val p 17 (by norm_num)]
  rw [if_pos (show 5 ∣ 10 * p + 30 by omega), if_neg (show ¬ 5 ∣ 10 * p + 28 by omega), if_neg (show ¬ 5 ∣ 10 * p + 26 by omega), if_pos (show 5 ∣ 10 * p + 25 by omega), if_neg (show ¬ 5 ∣ 10 * p + 24 by omega), if_neg (show ¬ 5 ∣ 10 * p + 23 by omega), if_neg (show ¬ 5 ∣ 10 * p + 22 by omega), if_neg (show ¬ 5 ∣ 10 * p + 21 by omega), if_neg (show ¬ 5 ∣ 10 * p + 19 by omega), if_neg (show ¬ 5 ∣ 10 * p + 17 by omega)]
  simp only [Nat.reduceDiv]
  push_cast
  ring

lemma rec8 (p : ℕ) : OMA.P293822.F (10 * p + 31) - 4 * OMA.P293822.F (10 * p + 29) + 6 * OMA.P293822.F (10 * p + 27) - OMA.P293822.F (10 * p + 26) - 4 * OMA.P293822.F (10 * p + 25) + 4 * OMA.P293822.F (10 * p + 24) + OMA.P293822.F (10 * p + 23) - 6 * OMA.P293822.F (10 * p + 22) + 4 * OMA.P293822.F (10 * p + 20) - OMA.P293822.F (10 * p + 18) = 0 := by
  rw [OMA.P293822.F_val p 31 (by norm_num), OMA.P293822.F_val p 29 (by norm_num), OMA.P293822.F_val p 27 (by norm_num), OMA.P293822.F_val p 26 (by norm_num), OMA.P293822.F_val p 25 (by norm_num), OMA.P293822.F_val p 24 (by norm_num), OMA.P293822.F_val p 23 (by norm_num), OMA.P293822.F_val p 22 (by norm_num), OMA.P293822.F_val p 20 (by norm_num), OMA.P293822.F_val p 18 (by norm_num)]
  rw [if_neg (show ¬ 5 ∣ 10 * p + 31 by omega), if_neg (show ¬ 5 ∣ 10 * p + 29 by omega), if_neg (show ¬ 5 ∣ 10 * p + 27 by omega), if_neg (show ¬ 5 ∣ 10 * p + 26 by omega), if_pos (show 5 ∣ 10 * p + 25 by omega), if_neg (show ¬ 5 ∣ 10 * p + 24 by omega), if_neg (show ¬ 5 ∣ 10 * p + 23 by omega), if_neg (show ¬ 5 ∣ 10 * p + 22 by omega), if_pos (show 5 ∣ 10 * p + 20 by omega), if_neg (show ¬ 5 ∣ 10 * p + 18 by omega)]
  simp only [Nat.reduceDiv]
  push_cast
  ring

lemma rec9 (p : ℕ) : OMA.P293822.F (10 * p + 32) - 4 * OMA.P293822.F (10 * p + 30) + 6 * OMA.P293822.F (10 * p + 28) - OMA.P293822.F (10 * p + 27) - 4 * OMA.P293822.F (10 * p + 26) + 4 * OMA.P293822.F (10 * p + 25) + OMA.P293822.F (10 * p + 24) - 6 * OMA.P293822.F (10 * p + 23) + 4 * OMA.P293822.F (10 * p + 21) - OMA.P293822.F (10 * p + 19) = 0 := by
  rw [OMA.P293822.F_val p 32 (by norm_num), OMA.P293822.F_val p 30 (by norm_num), OMA.P293822.F_val p 28 (by norm_num), OMA.P293822.F_val p 27 (by norm_num), OMA.P293822.F_val p 26 (by norm_num), OMA.P293822.F_val p 25 (by norm_num), OMA.P293822.F_val p 24 (by norm_num), OMA.P293822.F_val p 23 (by norm_num), OMA.P293822.F_val p 21 (by norm_num), OMA.P293822.F_val p 19 (by norm_num)]
  rw [if_neg (show ¬ 5 ∣ 10 * p + 32 by omega), if_pos (show 5 ∣ 10 * p + 30 by omega), if_neg (show ¬ 5 ∣ 10 * p + 28 by omega), if_neg (show ¬ 5 ∣ 10 * p + 27 by omega), if_neg (show ¬ 5 ∣ 10 * p + 26 by omega), if_pos (show 5 ∣ 10 * p + 25 by omega), if_neg (show ¬ 5 ∣ 10 * p + 24 by omega), if_neg (show ¬ 5 ∣ 10 * p + 23 by omega), if_neg (show ¬ 5 ∣ 10 * p + 21 by omega), if_neg (show ¬ 5 ∣ 10 * p + 19 by omega)]
  simp only [Nat.reduceDiv]
  push_cast
  ring

end OMA.P293822

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a293822.main := by
  have hA : (PowerSeries.mk fun n => (OMA.S_oeis_a293822.a n : ℚ)) = PowerSeries.mk OMA.P293822.F := by
    ext n; simp [OMA.P293822.a_eq_F]
  rw [hA]
  have hD : ((1 - X) ^ 5 * (1 + X) ^ 4 * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) : PowerSeries ℚ) =
      1 - C (4 : ℚ) * X ^ 2 + C (6 : ℚ) * X ^ 4 - X ^ 5 - C (4 : ℚ) * X ^ 6 + C (4 : ℚ) * X ^ 7 + X ^ 8
        - C (6 : ℚ) * X ^ 9 + C (4 : ℚ) * X ^ 11 - X ^ 13 := by
    simp only [map_ofNat]; ring
  have hN : (X ^ 5 * (1 + X - X ^ 2 + 2 * X ^ 3 + 7 * X ^ 4 + 2 * X ^ 5 - 2 * X ^ 6 + X ^ 8) : PowerSeries ℚ) =
      X ^ 5 + X ^ 6 - X ^ 7 + C (2 : ℚ) * X ^ 8 + C (7 : ℚ) * X ^ 9 + C (2 : ℚ) * X ^ 10
        - C (2 : ℚ) * X ^ 11 + X ^ 13 := by
    simp only [map_ofNat]; ring
  rw [hD, hN]
  ext m
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, coeff_mk, mul_left_comm _ (C _),
    coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_C]
  rcases Nat.lt_or_ge m 23 with hm | hm
  · interval_cases m <;> norm_num [OMA.P293822.F0, OMA.P293822.F1, OMA.P293822.F2, OMA.P293822.F3, OMA.P293822.F4, OMA.P293822.F5, OMA.P293822.F6, OMA.P293822.F7, OMA.P293822.F8, OMA.P293822.F9, OMA.P293822.F10, OMA.P293822.F11, OMA.P293822.F12, OMA.P293822.F13, OMA.P293822.F14, OMA.P293822.F15, OMA.P293822.F16, OMA.P293822.F17, OMA.P293822.F18, OMA.P293822.F19, OMA.P293822.F20, OMA.P293822.F21, OMA.P293822.F22]
  · obtain ⟨p, r, hr, rfl⟩ : ∃ p r, r < 10 ∧ m = 10 * p + r + 23 :=
      ⟨(m - 23) / 10, (m - 23) % 10, Nat.mod_lt _ (by norm_num), by omega⟩
    simp only [if_pos (show 2 ≤ 10 * p + r + 23 by omega), if_pos (show 4 ≤ 10 * p + r + 23 by omega), if_pos (show 5 ≤ 10 * p + r + 23 by omega), if_pos (show 6 ≤ 10 * p + r + 23 by omega), if_pos (show 7 ≤ 10 * p + r + 23 by omega), if_pos (show 8 ≤ 10 * p + r + 23 by omega), if_pos (show 9 ≤ 10 * p + r + 23 by omega), if_pos (show 10 ≤ 10 * p + r + 23 by omega), if_pos (show 11 ≤ 10 * p + r + 23 by omega), if_pos (show 13 ≤ 10 * p + r + 23 by omega)]
    simp only [if_neg (show ¬ (10 * p + r + 23 = 5) by omega), if_neg (show ¬ (10 * p + r + 23 = 6) by omega), if_neg (show ¬ (10 * p + r + 23 = 7) by omega), if_neg (show ¬ (10 * p + r + 23 = 13) by omega), if_neg (show ¬ (10 * p + r + 23 - 8 = 0) by omega), if_neg (show ¬ (10 * p + r + 23 - 9 = 0) by omega), if_neg (show ¬ (10 * p + r + 23 - 10 = 0) by omega), if_neg (show ¬ (10 * p + r + 23 - 11 = 0) by omega)]
    simp only [add_zero, sub_zero]
    try simp only [zero_add, add_zero, sub_zero]
    interval_cases r
    · rw [show 10 * p + 0 + 23 = 10 * p + 23 by ring, show 10 * p + 0 + 23 - 2 = 10 * p + 21 by omega, show 10 * p + 0 + 23 - 4 = 10 * p + 19 by omega, show 10 * p + 0 + 23 - 5 = 10 * p + 18 by omega, show 10 * p + 0 + 23 - 6 = 10 * p + 17 by omega, show 10 * p + 0 + 23 - 7 = 10 * p + 16 by omega, show 10 * p + 0 + 23 - 8 = 10 * p + 15 by omega, show 10 * p + 0 + 23 - 9 = 10 * p + 14 by omega, show 10 * p + 0 + 23 - 11 = 10 * p + 12 by omega, show 10 * p + 0 + 23 - 13 = 10 * p + 10 by omega]
      linear_combination OMA.P293822.rec0 p
    · rw [show 10 * p + 1 + 23 = 10 * p + 24 by ring, show 10 * p + 1 + 23 - 2 = 10 * p + 22 by omega, show 10 * p + 1 + 23 - 4 = 10 * p + 20 by omega, show 10 * p + 1 + 23 - 5 = 10 * p + 19 by omega, show 10 * p + 1 + 23 - 6 = 10 * p + 18 by omega, show 10 * p + 1 + 23 - 7 = 10 * p + 17 by omega, show 10 * p + 1 + 23 - 8 = 10 * p + 16 by omega, show 10 * p + 1 + 23 - 9 = 10 * p + 15 by omega, show 10 * p + 1 + 23 - 11 = 10 * p + 13 by omega, show 10 * p + 1 + 23 - 13 = 10 * p + 11 by omega]
      linear_combination OMA.P293822.rec1 p
    · rw [show 10 * p + 2 + 23 = 10 * p + 25 by ring, show 10 * p + 2 + 23 - 2 = 10 * p + 23 by omega, show 10 * p + 2 + 23 - 4 = 10 * p + 21 by omega, show 10 * p + 2 + 23 - 5 = 10 * p + 20 by omega, show 10 * p + 2 + 23 - 6 = 10 * p + 19 by omega, show 10 * p + 2 + 23 - 7 = 10 * p + 18 by omega, show 10 * p + 2 + 23 - 8 = 10 * p + 17 by omega, show 10 * p + 2 + 23 - 9 = 10 * p + 16 by omega, show 10 * p + 2 + 23 - 11 = 10 * p + 14 by omega, show 10 * p + 2 + 23 - 13 = 10 * p + 12 by omega]
      linear_combination OMA.P293822.rec2 p
    · rw [show 10 * p + 3 + 23 = 10 * p + 26 by ring, show 10 * p + 3 + 23 - 2 = 10 * p + 24 by omega, show 10 * p + 3 + 23 - 4 = 10 * p + 22 by omega, show 10 * p + 3 + 23 - 5 = 10 * p + 21 by omega, show 10 * p + 3 + 23 - 6 = 10 * p + 20 by omega, show 10 * p + 3 + 23 - 7 = 10 * p + 19 by omega, show 10 * p + 3 + 23 - 8 = 10 * p + 18 by omega, show 10 * p + 3 + 23 - 9 = 10 * p + 17 by omega, show 10 * p + 3 + 23 - 11 = 10 * p + 15 by omega, show 10 * p + 3 + 23 - 13 = 10 * p + 13 by omega]
      linear_combination OMA.P293822.rec3 p
    · rw [show 10 * p + 4 + 23 = 10 * p + 27 by ring, show 10 * p + 4 + 23 - 2 = 10 * p + 25 by omega, show 10 * p + 4 + 23 - 4 = 10 * p + 23 by omega, show 10 * p + 4 + 23 - 5 = 10 * p + 22 by omega, show 10 * p + 4 + 23 - 6 = 10 * p + 21 by omega, show 10 * p + 4 + 23 - 7 = 10 * p + 20 by omega, show 10 * p + 4 + 23 - 8 = 10 * p + 19 by omega, show 10 * p + 4 + 23 - 9 = 10 * p + 18 by omega, show 10 * p + 4 + 23 - 11 = 10 * p + 16 by omega, show 10 * p + 4 + 23 - 13 = 10 * p + 14 by omega]
      linear_combination OMA.P293822.rec4 p
    · rw [show 10 * p + 5 + 23 = 10 * p + 28 by ring, show 10 * p + 5 + 23 - 2 = 10 * p + 26 by omega, show 10 * p + 5 + 23 - 4 = 10 * p + 24 by omega, show 10 * p + 5 + 23 - 5 = 10 * p + 23 by omega, show 10 * p + 5 + 23 - 6 = 10 * p + 22 by omega, show 10 * p + 5 + 23 - 7 = 10 * p + 21 by omega, show 10 * p + 5 + 23 - 8 = 10 * p + 20 by omega, show 10 * p + 5 + 23 - 9 = 10 * p + 19 by omega, show 10 * p + 5 + 23 - 11 = 10 * p + 17 by omega, show 10 * p + 5 + 23 - 13 = 10 * p + 15 by omega]
      linear_combination OMA.P293822.rec5 p
    · rw [show 10 * p + 6 + 23 = 10 * p + 29 by ring, show 10 * p + 6 + 23 - 2 = 10 * p + 27 by omega, show 10 * p + 6 + 23 - 4 = 10 * p + 25 by omega, show 10 * p + 6 + 23 - 5 = 10 * p + 24 by omega, show 10 * p + 6 + 23 - 6 = 10 * p + 23 by omega, show 10 * p + 6 + 23 - 7 = 10 * p + 22 by omega, show 10 * p + 6 + 23 - 8 = 10 * p + 21 by omega, show 10 * p + 6 + 23 - 9 = 10 * p + 20 by omega, show 10 * p + 6 + 23 - 11 = 10 * p + 18 by omega, show 10 * p + 6 + 23 - 13 = 10 * p + 16 by omega]
      linear_combination OMA.P293822.rec6 p
    · rw [show 10 * p + 7 + 23 = 10 * p + 30 by ring, show 10 * p + 7 + 23 - 2 = 10 * p + 28 by omega, show 10 * p + 7 + 23 - 4 = 10 * p + 26 by omega, show 10 * p + 7 + 23 - 5 = 10 * p + 25 by omega, show 10 * p + 7 + 23 - 6 = 10 * p + 24 by omega, show 10 * p + 7 + 23 - 7 = 10 * p + 23 by omega, show 10 * p + 7 + 23 - 8 = 10 * p + 22 by omega, show 10 * p + 7 + 23 - 9 = 10 * p + 21 by omega, show 10 * p + 7 + 23 - 11 = 10 * p + 19 by omega, show 10 * p + 7 + 23 - 13 = 10 * p + 17 by omega]
      linear_combination OMA.P293822.rec7 p
    · rw [show 10 * p + 8 + 23 = 10 * p + 31 by ring, show 10 * p + 8 + 23 - 2 = 10 * p + 29 by omega, show 10 * p + 8 + 23 - 4 = 10 * p + 27 by omega, show 10 * p + 8 + 23 - 5 = 10 * p + 26 by omega, show 10 * p + 8 + 23 - 6 = 10 * p + 25 by omega, show 10 * p + 8 + 23 - 7 = 10 * p + 24 by omega, show 10 * p + 8 + 23 - 8 = 10 * p + 23 by omega, show 10 * p + 8 + 23 - 9 = 10 * p + 22 by omega, show 10 * p + 8 + 23 - 11 = 10 * p + 20 by omega, show 10 * p + 8 + 23 - 13 = 10 * p + 18 by omega]
      linear_combination OMA.P293822.rec8 p
    · rw [show 10 * p + 9 + 23 = 10 * p + 32 by ring, show 10 * p + 9 + 23 - 2 = 10 * p + 30 by omega, show 10 * p + 9 + 23 - 4 = 10 * p + 28 by omega, show 10 * p + 9 + 23 - 5 = 10 * p + 27 by omega, show 10 * p + 9 + 23 - 6 = 10 * p + 26 by omega, show 10 * p + 9 + 23 - 7 = 10 * p + 25 by omega, show 10 * p + 9 + 23 - 8 = 10 * p + 24 by omega, show 10 * p + 9 + 23 - 9 = 10 * p + 23 by omega, show 10 * p + 9 + 23 - 11 = 10 * p + 21 by omega, show 10 * p + 9 + 23 - 13 = 10 * p + 19 by omega]
      linear_combination OMA.P293822.rec9 p
