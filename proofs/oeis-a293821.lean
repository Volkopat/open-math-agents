import OMAStatements.S_oeis_a293821
import Mathlib

/-! Proof for OEIS A293821: Burnside's lemma for the rotation group `ℤ/4`. The identity fixes all
`C(N-1, 3) - 4 C(⌊N/2⌋, 3)` quadrilaterals of perimeter `N` (compositions of `N` into 4 parts, minus
those with a side `≥ N/2`; at most one side can be that long), the half-turn fixes the `N/2 - 1`
side sequences `(c, N/2 - c, c, N/2 - c)` when `N` is even, and the quarter-turns fix the square when
`4 ∣ N`. The closed form then follows by cases on `n mod 4`.
Credit: Sudharsan Rajendiran -/

namespace OMA.P293821
open OMA.S_oeis_a293821 Finset

lemma mem_Q {n : ℕ} {v : Fin 4 → ℕ} :
    v ∈ Q n ↔ (∀ i, 0 < v i ∧ 2 * v i < n) ∧ v 0 + v 1 + v 2 + v 3 = n := by
  simp only [Q, mem_filter, Fintype.mem_piFinset, mem_range, Fin.sum_univ_four]
  constructor
  · exact fun h => h.2
  · intro h; refine ⟨fun i => ?_, h⟩
    have := h.1 i; omega

abbrev G := Multiplicative (Fin 4)
abbrev X (n : ℕ) := {v : Fin 4 → ℕ // v ∈ Q n}

lemma rot_mem {n : ℕ} (k : Fin 4) {v : Fin 4 → ℕ} (hv : v ∈ Q n) : (fun i => v (i + k)) ∈ Q n := by
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
noncomputable def cls (n : ℕ) (v : Fin 4 → ℕ) : Finset (Fin 4 → ℕ) :=
  (Q n).filter (fun w => ∃ k : Fin 4, w = fun i => v (i + k))

lemma cls_rot (n : ℕ) (v : Fin 4 → ℕ) (g : Fin 4) : cls n (fun i => v (i + g)) = cls n v := by
  ext w
  simp only [cls, Finset.mem_filter]
  constructor
  · rintro ⟨hw, k, rfl⟩
    exact ⟨hw, k + g, by funext i; simp [add_assoc]⟩
  · rintro ⟨hw, k, rfl⟩
    exact ⟨hw, k - g, by funext i; simp [add_assoc]⟩

open Classical in
lemma a_eq (n : ℕ) : a n = Fintype.card (MulAction.orbitRel.Quotient G (X n)) := by
  let F : MulAction.orbitRel.Quotient G (X n) → Finset (Fin 4 → ℕ) :=
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
  have : (Q n).image (fun v => (Q n).filter (fun w => ∃ k : Fin 4, w = fun i => v (i + k))) =
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

/-! ## Fixed points -/

open Classical in
noncomputable def fixCount (n : ℕ) (g : G) : ℕ :=
  (Finset.univ.filter (fun x : X n => g • x = x)).card

lemma fix_iff {n : ℕ} (k : Fin 4) (x : X n) :
    (Multiplicative.ofAdd k : G) • x = x ↔ ∀ i, x.1 (i + k) = x.1 i := by
  constructor
  · intro h i; exact congrArg (fun y : X n => y.1 i) h
  · intro h; exact Subtype.ext (funext h)

open Classical in
lemma fix_one_eq (n : ℕ) (hn : 1 ≤ n) (k : Fin 4) (hk : k = 1 ∨ k = 3) :
    fixCount n (Multiplicative.ofAdd k) = if 4 ∣ n then 1 else 0 := by
  unfold fixCount
  have key : ∀ x : X n, (Multiplicative.ofAdd k : G) • x = x → ∀ i, 4 * x.1 i = n := by
    intro x h
    rw [fix_iff] at h
    have hs := (mem_Q.1 x.2).2
    rcases hk with rfl | rfl
    · have h0 := h 0; have h1 := h 1; have h2 := h 2
      simp only [show (0 : Fin 4) + 1 = 1 from rfl, show (1 : Fin 4) + 1 = 2 from rfl,
        show (2 : Fin 4) + 1 = 3 from rfl] at h0 h1 h2
      intro i; fin_cases i <;> simp <;> omega
    · have h0 := h 0; have h1 := h 1; have h2 := h 2
      simp only [show (0 : Fin 4) + 3 = 3 from rfl, show (1 : Fin 4) + 3 = 0 from rfl,
        show (2 : Fin 4) + 3 = 1 from rfl] at h0 h1 h2
      intro i; fin_cases i <;> simp <;> omega
  split_ifs with h4
  · obtain ⟨q, rfl⟩ := h4
    have hq : 0 < q := by omega
    rw [card_eq_one]
    have hm : (fun _ : Fin 4 => q) ∈ Q (4 * q) := by
      rw [mem_Q]; exact ⟨fun i => ⟨hq, by omega⟩, by ring⟩
    refine ⟨⟨_, hm⟩, ?_⟩
    ext x; simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro hx; apply Subtype.ext; funext i; have := key x hx i; simp only; omega
    · rintro rfl; rw [fix_iff]; intro i; rfl
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro x _ hx
    exact h4 ⟨x.1 0, (key x hx 0).symm⟩

open Classical in
lemma fix_zero_eq (n : ℕ) : fixCount n (Multiplicative.ofAdd 0) = (Q n).card := by
  unfold fixCount
  rw [Finset.filter_true_of_mem (fun x _ => (fix_iff 0 x).2 (fun i => by simp)),
    Finset.card_univ, Fintype.card_coe]

open Classical in
lemma fix_two_eq (n : ℕ) : fixCount n (Multiplicative.ofAdd 2) = if 2 ∣ n then n / 2 - 1 else 0 := by
  unfold fixCount
  have key : ∀ x : X n, (Multiplicative.ofAdd (2 : Fin 4) : G) • x = x →
      x.1 2 = x.1 0 ∧ x.1 3 = x.1 1 := by
    intro x h
    rw [fix_iff] at h
    have h0 := h 0; have h1 := h 1
    simp only [show (0 : Fin 4) + 2 = 2 from rfl, show (1 : Fin 4) + 2 = 3 from rfl] at h0 h1
    exact ⟨h0, h1⟩
  split_ifs with h2
  · obtain ⟨q, rfl⟩ := h2
    rw [show 2 * q / 2 - 1 = (Icc 1 (q - 1)).card by simp]
    have hm : ∀ c ∈ Icc 1 (q - 1), ![c, q - c, c, q - c] ∈ Q (2 * q) := by
      intro c hc; simp only [mem_Icc] at hc
      rw [mem_Q]; refine ⟨fun i => ?_, by simp; omega⟩
      fin_cases i <;> simp <;> omega
    symm
    apply card_bij (fun c hc => (⟨![c, q - c, c, q - c], hm c hc⟩ : X (2 * q)))
    · intro c hc
      simp only [mem_filter, mem_univ, true_and, fix_iff]
      intro i; fin_cases i <;> rfl
    · intro c hc d hd h
      have := congrArg (fun x : X (2 * q) => x.1 0) h
      simpa using this
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      have k := key x hx
      have hx2 := mem_Q.1 x.2
      have h0 := hx2.1 0; have h1 := hx2.1 1
      refine ⟨x.1 0, by simp only [mem_Icc]; omega, ?_⟩
      apply Subtype.ext; funext i
      fin_cases i <;> simp <;> omega
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro x _ hx
    have := key x hx
    have hs := (mem_Q.1 x.2).2
    exact h2 ⟨x.1 0 + x.1 1, by omega⟩

/-! ## Counting quadrilaterals -/

def comp (n : ℕ) : Finset (Fin 4 → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (n + 1)).filter (fun v => (∀ i, 0 < v i) ∧ ∑ i, v i = n)

lemma mem_comp {n : ℕ} {v : Fin 4 → ℕ} :
    v ∈ comp n ↔ (∀ i, 0 < v i) ∧ v 0 + v 1 + v 2 + v 3 = n := by
  simp only [comp, mem_filter, Fintype.mem_piFinset, mem_range, Fin.sum_univ_four]
  constructor
  · exact fun h => h.2
  · intro h; refine ⟨fun i => ?_, h⟩
    have := h.1 0; have := h.1 1; have := h.1 2; have := h.1 3
    fin_cases i <;> simp <;> omega

lemma card_filter_prod {α β : Type*} (A : Finset α) (B : Finset β) (P : α × β → Prop)
    [DecidablePred P] : ((A ×ˢ B).filter P).card = ∑ a ∈ A, (B.filter (fun b => P (a, b))).card := by
  rw [card_filter, sum_product]
  simp only [card_filter]

def D3N (s : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (range (s + 1) ×ˢ range (s + 1) ×ˢ range (s + 1)).filter (fun t => t.1 + t.2.1 + t.2.2 ≤ s)

lemma SC (t : ℕ) : 2 * ∑ j ∈ range (t + 1), (j + 1) = (t + 1) * (t + 2) := by
  induction t with
  | zero => simp
  | succ t ih => rw [sum_range_succ, mul_add, ih]; ring

lemma SD (s : ℕ) : 3 * ∑ j ∈ range (s + 1), ((j + 1) * (j + 2)) = (s + 1) * (s + 2) * (s + 3) := by
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

lemma card_D3N (s : ℕ) : 6 * (D3N s).card = (s + 1) * (s + 2) * (s + 3) := by
  unfold D3N
  rw [card_filter_prod]
  have hc : ∀ a ∈ range (s + 1), 2 * ((range (s + 1) ×ˢ range (s + 1)).filter
      (fun q : ℕ × ℕ => (a, q).1 + (a, q).2.1 + (a, q).2.2 ≤ s)).card = (s - a + 1) * (s - a + 2) := by
    intro a ha
    simp only [mem_range] at ha
    rw [← D2N s (s - a) (by omega)]
    congr 2; apply filter_congr; intro q _; simp only; omega
  rw [show 6 = 3 * 2 by rfl, mul_assoc, mul_sum, sum_congr rfl hc]
  have := sum_range_reflect (fun j => (j + 1) * (j + 2)) (s + 1)
  simp only [show s + 1 - 1 = s by omega] at this
  rw [this]; exact SD s

lemma card_comp (n : ℕ) (hn : 4 ≤ n) : (comp n).card = (D3N (n - 4)).card := by
  apply card_nbij' (fun v => (v 0 - 1, v 1 - 1, v 2 - 1))
    (fun t => ![t.1 + 1, t.2.1 + 1, t.2.2 + 1, n - 3 - t.1 - t.2.1 - t.2.2])
  · intro v hv
    rw [mem_coe, mem_comp] at hv
    have := hv.1 0; have := hv.1 1; have := hv.1 2; have := hv.1 3
    simp only [mem_coe, D3N, mem_filter, mem_product, mem_range]; omega
  · intro t ht
    simp only [mem_coe, D3N, mem_filter, mem_product, mem_range] at ht
    rw [mem_coe, mem_comp]
    refine ⟨fun i => ?_, by simp; omega⟩
    fin_cases i <;> simp <;> omega
  · intro v hv
    rw [mem_coe, mem_comp] at hv
    have := hv.1 0; have := hv.1 1; have := hv.1 2; have := hv.1 3
    funext i; fin_cases i <;> simp <;> omega
  · intro t _; simp

/-- tuples whose side `k` is at least `n / 2`. -/
def E (n : ℕ) (k : Fin 4) : Finset (Fin 4 → ℕ) := (comp n).filter (fun v => n ≤ 2 * v k)

lemma card_E0 (n : ℕ) : 6 * (E n 0).card = (n / 2) * (n / 2 - 1) * (n / 2 - 2) := by
  rcases Nat.lt_or_ge (n / 2) 3 with h | h
  · rw [show (E n 0).card = 0 by
      rw [card_eq_zero, E, filter_eq_empty_iff]
      intro v hv h'
      rw [mem_comp] at hv
      have := hv.1 1; have := hv.1 2; have := hv.1 3; omega]
    interval_cases (n / 2) <;> rfl
  · rw [show (E n 0).card = (D3N (n / 2 - 3)).card by
      apply card_nbij' (fun v => (v 1 - 1, v 2 - 1, v 3 - 1))
        (fun t => ![n - 3 - t.1 - t.2.1 - t.2.2, t.1 + 1, t.2.1 + 1, t.2.2 + 1])
      · intro v hv
        simp only [mem_coe, E, mem_filter, mem_comp] at hv
        have := hv.1.1 0; have := hv.1.1 1; have := hv.1.1 2; have := hv.1.1 3
        simp only [mem_coe, D3N, mem_filter, mem_product, mem_range]; omega
      · intro t ht
        simp only [mem_coe, D3N, mem_filter, mem_product, mem_range] at ht
        simp only [mem_coe, E, mem_filter, mem_comp]
        refine ⟨⟨fun i => ?_, by simp; omega⟩, by simp; omega⟩
        fin_cases i <;> simp <;> omega
      · intro v hv
        simp only [mem_coe, E, mem_filter, mem_comp] at hv
        have := hv.1.1 0; have := hv.1.1 1; have := hv.1.1 2; have := hv.1.1 3
        funext i; fin_cases i <;> simp <;> omega
      · intro t _; simp]
    rw [card_D3N]
    obtain ⟨m, hm⟩ : ∃ m, n / 2 = m + 3 := ⟨n / 2 - 3, by omega⟩
    rw [hm, show m + 3 - 3 = m by omega, show m + 3 - 1 = m + 2 by omega,
      show m + 3 - 2 = m + 1 by omega]
    ring

lemma rot_comp {n : ℕ} (k : Fin 4) {v : Fin 4 → ℕ} (hv : v ∈ comp n) : (fun i => v (i + k)) ∈ comp n := by
  simp only [comp, Finset.mem_filter, Fintype.mem_piFinset] at hv ⊢
  refine ⟨fun i => hv.1 _, fun i => hv.2.1 _, ?_⟩
  rw [← hv.2.2]; exact Equiv.sum_comp (Equiv.addRight k) v

lemma card_Ek (n : ℕ) (k : Fin 4) : (E n k).card = (E n 0).card := by
  apply card_nbij' (fun v => fun i => v (i + k)) (fun v => fun i => v (i - k))
  · intro v hv
    simp only [mem_coe, E, mem_filter] at hv ⊢
    exact ⟨rot_comp k hv.1, by simpa using hv.2⟩
  · intro v hv
    simp only [mem_coe, E, mem_filter] at hv ⊢
    exact ⟨by simpa [sub_eq_add_neg] using rot_comp (-k) hv.1, by simpa using hv.2⟩
  · intro v _; funext i; simp
  · intro v _; funext i; simp

lemma split (n : ℕ) : (comp n).card = (Q n).card + 4 * (E n 0).card := by
  have s0 := card_filter_add_card_filter_not (s := comp n) (fun v => n ≤ 2 * v 0)
  set C1 := (comp n).filter (fun v => ¬ n ≤ 2 * v 0)
  have s1 := card_filter_add_card_filter_not (s := C1) (fun v => n ≤ 2 * v 1)
  set C2 := C1.filter (fun v => ¬ n ≤ 2 * v 1)
  have s2 := card_filter_add_card_filter_not (s := C2) (fun v => n ≤ 2 * v 2)
  set C3 := C2.filter (fun v => ¬ n ≤ 2 * v 2)
  have s3 := card_filter_add_card_filter_not (s := C3) (fun v => n ≤ 2 * v 3)
  have e1 : C1.filter (fun v => n ≤ 2 * v 1) = E n 1 := by
    ext v; simp only [C1, E, mem_filter, mem_comp]
    constructor
    · rintro ⟨⟨h, -⟩, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩; have := h.1 2; have := h.1 3; exact ⟨⟨h, by omega⟩, h'⟩
  have e2 : C2.filter (fun v => n ≤ 2 * v 2) = E n 2 := by
    ext v; simp only [C2, C1, E, mem_filter, mem_comp]
    constructor
    · rintro ⟨⟨⟨h, -⟩, -⟩, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩; have := h.1 1; have := h.1 3; have := h.1 0
      exact ⟨⟨⟨h, by omega⟩, by omega⟩, h'⟩
  have e3 : C3.filter (fun v => n ≤ 2 * v 3) = E n 3 := by
    ext v; simp only [C3, C2, C1, E, mem_filter, mem_comp]
    constructor
    · rintro ⟨⟨⟨⟨h, -⟩, -⟩, -⟩, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩; have := h.1 1; have := h.1 2; have := h.1 0
      exact ⟨⟨⟨⟨h, by omega⟩, by omega⟩, by omega⟩, h'⟩
  have e4 : C3.filter (fun v => ¬ n ≤ 2 * v 3) = Q n := by
    ext v; simp only [C3, C2, C1, mem_filter, mem_comp, mem_Q, not_le]
    constructor
    · rintro ⟨⟨⟨⟨h, h0⟩, h1⟩, h2⟩, h3⟩
      refine ⟨fun i => ?_, h.2⟩
      fin_cases i
      · exact ⟨h.1 0, h0⟩
      · exact ⟨h.1 1, h1⟩
      · exact ⟨h.1 2, h2⟩
      · exact ⟨h.1 3, h3⟩
    · rintro ⟨h, hs⟩
      exact ⟨⟨⟨⟨⟨fun i => (h i).1, hs⟩, (h 0).2⟩, (h 1).2⟩, (h 2).2⟩, (h 3).2⟩
  rw [e3, e4] at s3; rw [e2] at s2; rw [e1] at s1
  change (E n 0).card + C1.card = (comp n).card at s0
  rw [card_Ek n 1] at s1; rw [card_Ek n 2] at s2; rw [card_Ek n 3] at s3
  omega

/-! ## Burnside -/

open Classical in
lemma burnside (n : ℕ) (hn : 1 ≤ n) : Fintype.card (MulAction.orbitRel.Quotient G (X n)) * 4 =
    (Q n).card + (if 2 ∣ n then n / 2 - 1 else 0) + 2 * (if 4 ∣ n then 1 else 0) := by
  have hb := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (X n)
  have hG : Fintype.card G = 4 := by simp
  have hfix : ∀ g : G, Fintype.card (MulAction.fixedBy (X n) g) = fixCount n g := by
    intro g
    unfold fixCount
    rw [← Fintype.card_subtype]; rfl
  have hsum : (∑ g : G, fixCount n g) = ∑ k : Fin 4, fixCount n (Multiplicative.ofAdd k) :=
    (Fintype.sum_equiv Multiplicative.ofAdd _ _ (fun _ => rfl)).symm
  rw [hG] at hb
  simp only [hfix] at hb
  rw [hsum, Fin.sum_univ_four, fix_zero_eq, fix_two_eq, fix_one_eq n hn 1 (Or.inl rfl),
    fix_one_eq n hn 3 (Or.inr rfl)] at hb
  change _ = Fintype.card (MulAction.orbitRel.Quotient G (X n)) * 4 at hb
  omega

lemma closed (N : ℕ) (hN : 4 ≤ N) : 24 * a N + 4 * (N / 2) * (N / 2 - 1) * (N / 2 - 2) =
    (N - 1) * (N - 2) * (N - 3) + 6 * (if 2 ∣ N then N / 2 - 1 else 0) +
      12 * (if 4 ∣ N then 1 else 0) := by
  have hb := burnside N (by omega)
  rw [← a_eq] at hb
  have hs := split N
  rw [card_comp N hN] at hs
  have h3 := card_D3N (N - 4)
  have hE := card_E0 N
  rw [show N - 4 + 1 = N - 3 by omega, show N - 4 + 2 = N - 2 by omega,
    show N - 4 + 3 = N - 1 by omega] at h3
  have : 6 * (Q N).card + 4 * (6 * (E N 0).card) = (N - 3) * (N - 2) * (N - 1) := by
    rw [← h3, hs]; ring
  rw [hE] at this
  nlinarith

end OMA.P293821

lemma pow4 {z : ℂ} (h : z ^ 4 = 1) (p r : ℕ) : z ^ (4 * p + r) = z ^ r := by
  rw [pow_add, pow_mul, h, one_pow, one_mul]

open Complex in
theorem OMA.solution : type_of% @OMA.S_oeis_a293821.main := by
  intro n hn
  have hI4 : I ^ 4 = 1 := Complex.I_pow_four
  have hJ4 : (-I) ^ 4 = 1 := by rw [neg_pow, hI4]; norm_num
  have hM4 : ((-1 : ℂ)) ^ 4 = 1 := by norm_num
  have hr : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hr with h | h | h | h
  · obtain ⟨p, rfl⟩ : ∃ p, n = 4 * p + 4 := ⟨n / 4 - 1, by omega⟩
    have hc := OMA.P293821.closed (4 * p + 4 + 1) (by omega)
    rw [show (4 * p + 4 + 1) / 2 = 2 * p + 2 by omega, if_neg (by omega), if_neg (by omega),
      show 2 * p + 2 - 1 = 2 * p + 1 by omega, show 2 * p + 2 - 2 = 2 * p by omega,
      show 4 * p + 4 + 1 - 1 = 4 * p + 4 by omega, show 4 * p + 4 + 1 - 2 = 4 * p + 3 by omega,
      show 4 * p + 4 + 1 - 3 = 4 * p + 2 by omega] at hc
    have hC : (24 * (OMA.S_oeis_a293821.a (4 * p + 4 + 1) : ℂ) + 4 * (2 * p + 2) * (2 * p + 1) * (2 * p)) =
        (4 * p + 4) * (4 * p + 3) * (4 * p + 2) := by exact_mod_cast hc
    rw [show 4 * p + 4 = 4 * (p + 1) + 0 by ring, pow4 hM4, pow4 hJ4, pow4 hI4]
    push_cast
    linear_combination hC / 24
  · obtain ⟨p, rfl⟩ : ∃ p, n = 4 * p + 5 := ⟨n / 4 - 1, by omega⟩
    have hc := OMA.P293821.closed (4 * p + 5 + 1) (by omega)
    rw [show (4 * p + 5 + 1) / 2 = 2 * p + 3 by omega, if_pos (by omega), if_neg (by omega),
      show 2 * p + 3 - 1 = 2 * p + 2 by omega, show 2 * p + 3 - 2 = 2 * p + 1 by omega,
      show 4 * p + 5 + 1 - 1 = 4 * p + 5 by omega, show 4 * p + 5 + 1 - 2 = 4 * p + 4 by omega,
      show 4 * p + 5 + 1 - 3 = 4 * p + 3 by omega] at hc
    have hC : (24 * (OMA.S_oeis_a293821.a (4 * p + 5 + 1) : ℂ) + 4 * (2 * p + 3) * (2 * p + 2) * (2 * p + 1)) =
        (4 * p + 5) * (4 * p + 4) * (4 * p + 3) + 6 * (2 * p + 2) := by exact_mod_cast hc
    rw [show 4 * p + 5 = 4 * (p + 1) + 1 by ring, pow4 hM4, pow4 hJ4, pow4 hI4]
    have e : (-1 + (-1) ^ 1 + 4 * I * (-I) ^ 1 - 4 * I * I ^ 1 : ℂ) = 6 := by
      ring_nf; rw [I_sq]; ring
    rw [e]
    push_cast
    linear_combination hC / 24
  · obtain ⟨p, rfl⟩ : ∃ p, n = 4 * p + 6 := ⟨n / 4 - 1, by omega⟩
    have hc := OMA.P293821.closed (4 * p + 6 + 1) (by omega)
    rw [show (4 * p + 6 + 1) / 2 = 2 * p + 3 by omega, if_neg (by omega), if_neg (by omega),
      show 2 * p + 3 - 1 = 2 * p + 2 by omega, show 2 * p + 3 - 2 = 2 * p + 1 by omega,
      show 4 * p + 6 + 1 - 1 = 4 * p + 6 by omega, show 4 * p + 6 + 1 - 2 = 4 * p + 5 by omega,
      show 4 * p + 6 + 1 - 3 = 4 * p + 4 by omega] at hc
    have hC : (24 * (OMA.S_oeis_a293821.a (4 * p + 6 + 1) : ℂ) + 4 * (2 * p + 3) * (2 * p + 2) * (2 * p + 1)) =
        (4 * p + 6) * (4 * p + 5) * (4 * p + 4) := by exact_mod_cast hc
    rw [show 4 * p + 6 = 4 * (p + 1) + 2 by ring, pow4 hM4, pow4 hJ4, pow4 hI4]
    have e : (-1 + (-1) ^ 2 + 4 * I * (-I) ^ 2 - 4 * I * I ^ 2 : ℂ) = 0 := by ring
    rw [e]
    push_cast
    linear_combination hC / 24
  · obtain ⟨p, rfl⟩ : ∃ p, n = 4 * p + 3 := ⟨n / 4, by omega⟩
    have hc := OMA.P293821.closed (4 * p + 3 + 1) (by omega)
    rw [show (4 * p + 3 + 1) / 2 = 2 * p + 2 by omega, if_pos (by omega), if_pos (by omega),
      show 2 * p + 2 - 1 = 2 * p + 1 by omega, show 2 * p + 2 - 2 = 2 * p by omega,
      show 4 * p + 3 + 1 - 1 = 4 * p + 3 by omega, show 4 * p + 3 + 1 - 2 = 4 * p + 2 by omega,
      show 4 * p + 3 + 1 - 3 = 4 * p + 1 by omega] at hc
    have hC : (24 * (OMA.S_oeis_a293821.a (4 * p + 3 + 1) : ℂ) + 4 * (2 * p + 2) * (2 * p + 1) * (2 * p)) =
        (4 * p + 3) * (4 * p + 2) * (4 * p + 1) + 6 * (2 * p + 1) + 12 := by exact_mod_cast hc
    rw [pow4 hM4, pow4 hJ4, pow4 hI4]
    have e : (-1 + (-1) ^ 3 + 4 * I * (-I) ^ 3 - 4 * I * I ^ 3 : ℂ) = -10 := by
      ring_nf; rw [I_pow_four]; ring
    rw [e]
    push_cast
    linear_combination hC / 24
