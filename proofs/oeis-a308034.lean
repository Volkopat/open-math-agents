import OMAStatements.S_oeis_a308034

namespace OMA.S_oeis_a308034

open Finset PowerSeries




lemma mem_parts {n : ℕ} {t : ℕ × ℕ × ℕ} :
    t ∈ parts n ↔ 1 ≤ t.1 ∧ t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 + t.2.1 + t.2.2 = n := by
  simp only [parts, mem_filter, mem_product, mem_Icc]
  constructor
  · intro h; omega
  · intro h; omega

/-- The number of partitions into 3 parts. -/
def p (n : ℕ) : ℕ := (parts n).card

lemma p_succ3 (n : ℕ) : p (n + 3) = p n + (n + 2) / 2 := by
  have h1 : ((parts (n + 3)).filter fun t => ¬ t.1 = 1).card = (parts n).card := by
    apply card_nbij' (fun t => (t.1 - 1, t.2.1 - 1, t.2.2 - 1))
      (fun t => (t.1 + 1, t.2.1 + 1, t.2.2 + 1))
    · rintro ⟨x, y, z⟩ h
      simp only [mem_coe, mem_filter, mem_parts] at h
      simp only [mem_coe, mem_parts]
      omega
    · rintro ⟨x, y, z⟩ h
      simp only [mem_coe, mem_parts] at h
      simp only [mem_coe, mem_filter, mem_parts]
      omega
    · rintro ⟨x, y, z⟩ h
      simp only [mem_coe, mem_filter, mem_parts] at h
      simp only [Prod.mk.injEq]
      omega
    · rintro ⟨x, y, z⟩ h
      simp only [Prod.mk.injEq]
      omega
  have h2 : ((parts (n + 3)).filter fun t => t.1 = 1).card = (n + 2) / 2 := by
    rw [← Nat.add_sub_cancel ((n + 2) / 2) 1, ← Nat.card_Icc 1 ((n + 2) / 2)]
    apply card_nbij' (fun t => t.2.1) (fun b => (1, b, n + 2 - b))
    · rintro ⟨x, y, z⟩ h
      simp only [mem_coe, mem_filter, mem_parts] at h
      simp only [mem_coe, mem_Icc]
      omega
    · intro b hb
      simp only [mem_coe, mem_Icc] at hb
      simp only [mem_coe, mem_filter, mem_parts, and_true]
      omega
    · rintro ⟨x, y, z⟩ h
      simp only [mem_coe, mem_filter, mem_parts] at h
      simp only [Prod.mk.injEq, true_and]
      omega
    · intro b _
      rfl
  unfold p
  rw [← card_filter_add_card_filter_not (s := parts (n + 3)) (fun t => t.1 = 1), h1, h2]
  ring

lemma p_shift12 (n : ℕ) : p (n + 12) = p n + 2 * n + 12 := by
  rw [show n + 12 = (n + 9) + 3 by ring, p_succ3, show n + 9 = (n + 6) + 3 by ring, p_succ3,
    show n + 6 = (n + 3) + 3 by ring, p_succ3, p_succ3]
  omega

/-- The partitions of n into 3 parts that all divide n. -/
def dparts (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (parts n).filter fun t => t.1 ∣ n ∧ t.2.1 ∣ n ∧ t.2.2 ∣ n

lemma classify {n x y z : ℕ} (h1 : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hs : x + y + z = n)
    (dy : y ∣ n) (dz : z ∣ n) :
    (3 ∣ n ∧ (x, y, z) = (n / 3, n / 3, n / 3)) ∨ (4 ∣ n ∧ (x, y, z) = (n / 4, n / 4, n / 2)) ∨
      (6 ∣ n ∧ (x, y, z) = (n / 6, n / 3, n / 2)) := by
  obtain ⟨k, hk⟩ := dz
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k <;> omega
    · exact h
  have hk3 : k ≤ 3 := by
    by_contra hc
    have : z * 4 ≤ z * k := Nat.mul_le_mul_left z (by omega)
    omega
  interval_cases k
  · obtain ⟨j, hj⟩ := dy
    have hj3 : 3 ≤ j := by
      by_contra hc
      have : y * j ≤ y * 2 := Nat.mul_le_mul_left y (by omega)
      omega
    have hj4 : j ≤ 4 := by
      by_contra hc
      have : y * 5 ≤ y * j := Nat.mul_le_mul_left y (by omega)
      omega
    interval_cases j
    · right; right
      refine ⟨⟨x, by omega⟩, ?_⟩
      simp only [Prod.mk.injEq]
      omega
    · right; left
      refine ⟨⟨y, by omega⟩, ?_⟩
      simp only [Prod.mk.injEq]
      omega
  · left
    refine ⟨⟨z, by omega⟩, ?_⟩
    simp only [Prod.mk.injEq]
    omega

/-- The three shapes, indexed by 3, 4 and 6. -/
def shape (n k : ℕ) : ℕ × ℕ × ℕ :=
  if k = 3 then (n / 3, n / 3, n / 3) else if k = 4 then (n / 4, n / 4, n / 2)
  else (n / 6, n / 3, n / 2)

lemma dparts_eq (n : ℕ) (hn : 1 ≤ n) :
    dparts n = (({3, 4, 6} : Finset ℕ).filter (· ∣ n)).image (shape n) := by
  ext ⟨x, y, z⟩
  simp only [dparts, mem_filter, mem_parts, mem_image, mem_insert, mem_singleton]
  constructor
  · rintro ⟨⟨h1, hxy, hyz, hs⟩, dx, dy, dz⟩
    rcases classify h1 hxy hyz hs dy dz with ⟨h3, he⟩ | ⟨h4, he⟩ | ⟨h6, he⟩
    · exact ⟨3, ⟨by simp, h3⟩, by simp [shape, he]⟩
    · exact ⟨4, ⟨by simp, h4⟩, by simp [shape, he]⟩
    · exact ⟨6, ⟨by simp, h6⟩, by simp [shape, he]⟩
  · rintro ⟨k, ⟨hk, hkn⟩, he⟩
    rcases hk with rfl | rfl | rfl
    · simp only [shape, if_true, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      obtain ⟨m, rfl⟩ := hkn
      refine ⟨by omega, ?_, ?_, ?_⟩ <;>
        exact ⟨3, by omega⟩
    · simp only [shape, show (4 : ℕ) ≠ 3 by norm_num, if_false, if_true, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      obtain ⟨m, rfl⟩ := hkn
      refine ⟨by omega, ⟨4, by omega⟩, ⟨4, by omega⟩, ⟨2, by omega⟩⟩
    · simp only [shape, show (6 : ℕ) ≠ 3 by norm_num, show (6 : ℕ) ≠ 4 by norm_num, if_false,
        Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      obtain ⟨m, rfl⟩ := hkn
      refine ⟨by omega, ⟨6, by omega⟩, ⟨3, by omega⟩, ⟨2, by omega⟩⟩

lemma dparts_card (n : ℕ) (hn : 1 ≤ n) :
    (dparts n).card = (({3, 4, 6} : Finset ℕ).filter (· ∣ n)).card := by
  rw [dparts_eq n hn]
  apply card_image_of_injOn
  intro k hk l hl hkl
  simp only [coe_filter, Set.mem_ofPred_eq, mem_insert, mem_singleton] at hk hl
  obtain ⟨hk, hkn⟩ := hk
  obtain ⟨hl, hln⟩ := hl
  rcases hk with rfl | rfl | rfl <;> rcases hl with rfl | rfl | rfl <;>
    simp only [shape, Prod.mk.injEq] at hkl <;> norm_num at hkl <;> omega

lemma a_add_d (n : ℕ) : a n + (dparts n).card = p n := by
  unfold a dparts p
  rw [add_comm, ← card_filter_add_card_filter_not (s := parts n)
    (fun t => t.1 ∣ n ∧ t.2.1 ∣ n ∧ t.2.2 ∣ n)]
  congr 2
  ext t
  simp only [mem_filter]
  tauto

lemma a_shift12 (n : ℕ) (hn : 1 ≤ n) : a (n + 12) = a n + 2 * n + 12 := by
  have h1 := a_add_d n
  have h2 := a_add_d (n + 12)
  have h3 : (dparts (n + 12)).card = (dparts n).card := by
    rw [dparts_card n hn, dparts_card (n + 12) (by omega)]
    congr 1
    apply filter_congr
    intro k hk
    simp only [mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl | rfl <;> omega
  have h4 := p_shift12 n
  omega

/-- The values from the closed forms, for the finite checks. -/
def pf : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | n + 3 => pf n + (n + 2) / 2

lemma p_eq_pf (n : ℕ) : p n = pf n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | n + 3 => rw [p_succ3, pf, ih n (by omega)]

def af (n : ℕ) : ℕ :=
  pf n - ((if 3 ∣ n then 1 else 0) + (if 4 ∣ n then 1 else 0) + (if 6 ∣ n then 1 else 0))

lemma a_eq_af (n : ℕ) (hn : 1 ≤ n) : a n = af n := by
  have h := a_add_d n
  rw [dparts_card n hn, p_eq_pf] at h
  unfold af
  have : (({3, 4, 6} : Finset ℕ).filter (· ∣ n)).card =
      (if 3 ∣ n then 1 else 0) + (if 4 ∣ n then 1 else 0) + (if 6 ∣ n then 1 else 0) := by
    rw [show ({3, 4, 6} : Finset ℕ) = insert 3 (insert 4 {6}) from rfl, filter_insert,
      filter_insert, filter_singleton]
    by_cases h3 : 3 ∣ n <;> by_cases h4 : 4 ∣ n <;> by_cases h6 : 6 ∣ n <;> simp [h3, h4, h6]
  omega

/-- The residual of Barker's recurrence at n. -/
def res (n : ℕ) : ℤ :=
  a n - (2 * a (n - 1) - 2 * a (n - 2) + 2 * a (n - 3) - a (n - 4) + a (n - 6) - 2 * a (n - 7) +
    2 * a (n - 8) - 2 * a (n - 9) + a (n - 10))

lemma res_shift (n : ℕ) (hn : 11 ≤ n) : res (n + 12) = res n := by
  unfold res
  have e : ∀ i, i ≤ 10 → (a (n + 12 - i) : ℤ) = a (n - i) + 2 * ((n : ℤ) - i) + 12 := by
    intro i hi
    rw [show n + 12 - i = (n - i) + 12 by omega, a_shift12 (n - i) (by omega)]
    push_cast [Nat.cast_sub (by omega : i ≤ n)]
    ring
  have e0 := e 0 (by norm_num)
  have e1 := e 1 (by norm_num)
  have e2 := e 2 (by norm_num)
  have e3 := e 3 (by norm_num)
  have e4 := e 4 (by norm_num)
  have e6 := e 6 (by norm_num)
  have e7 := e 7 (by norm_num)
  have e8 := e 8 (by norm_num)
  have e9 := e 9 (by norm_num)
  have e10 := e 10 (by norm_num)
  simp only [Nat.sub_zero, Nat.cast_zero, sub_zero] at e0
  push_cast at e1 e2 e3 e4 e6 e7 e8 e9 e10 ⊢
  linarith

lemma res_base : ∀ n, 11 ≤ n → n ≤ 22 → res n = 0 := by
  intro n h1 h2
  unfold res
  have e : ∀ i, i ≤ 10 → (a (n - i) : ℤ) = af (n - i) := fun i hi => by
    rw [a_eq_af (n - i) (by omega)]
  rw [e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num), e 4 (by norm_num), e 6 (by norm_num),
    e 7 (by norm_num), e 8 (by norm_num), e 9 (by norm_num), e 10 (by norm_num),
    a_eq_af n (by omega)]
  interval_cases n <;> decide

/-- Barker's recurrence for n > 10. -/
theorem recurrence : ∀ n : ℕ, 10 < n → (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 2) + 2 * a (n - 3) -
    a (n - 4) + a (n - 6) - 2 * a (n - 7) + 2 * a (n - 8) - 2 * a (n - 9) + a (n - 10) := by
  intro n hn
  have : res n = 0 := by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases Nat.lt_or_ge n 23 with h | h
      · exact res_base n (by omega) (by omega)
      · rw [show n = (n - 12) + 12 by omega, res_shift (n - 12) (by omega)]
        exact ih (n - 12) (by omega) (by omega)
  unfold res at this
  linarith

lemma coeff_gf (n : ℕ) : coeff n gf = (a n : ℚ) := by simp [gf]

lemma a_small : a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 0 ∧ a 4 = 0 ∧ a 5 = 2 ∧ a 6 = 1 ∧ a 7 = 4 ∧
    a 8 = 4 ∧ a 9 = 6 ∧ a 10 = 8 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [a_eq_af _ (by norm_num)] <;> decide

/-- Barker's g.f. as an identity in Q[[x]]. -/
theorem gf_eq : gf = X ^ 5 * (2 - 3 * X + 6 * X ^ 2 - 6 * X ^ 3 + 6 * X ^ 4 - 3 * X ^ 5) *
    ((1 - X) ^ 3 * (1 + X) * (1 - X + X ^ 2) * (1 + X ^ 2) * (1 + X + X ^ 2))⁻¹ := by
  set D : ℚ⟦X⟧ := (1 - X) ^ 3 * (1 + X) * (1 - X + X ^ 2) * (1 + X ^ 2) * (1 + X + X ^ 2) with hD
  have hden : constantCoeff D ≠ 0 := by rw [hD]; simp
  have key : gf * D = X ^ 5 * (2 - 3 * X + 6 * X ^ 2 - 6 * X ^ 3 + 6 * X ^ 4 - 3 * X ^ 5) := by
    have e : gf * D = gf - C 2 * (gf * X ^ 1) + C 2 * (gf * X ^ 2) - C 2 * (gf * X ^ 3) +
        gf * X ^ 4 - gf * X ^ 6 + C 2 * (gf * X ^ 7) - C 2 * (gf * X ^ 8) + C 2 * (gf * X ^ 9) -
        gf * X ^ 10 := by
      rw [hD]; simp only [map_ofNat]; ring
    have en : (X : ℚ⟦X⟧) ^ 5 * (2 - 3 * X + 6 * X ^ 2 - 6 * X ^ 3 + 6 * X ^ 4 - 3 * X ^ 5) =
        C 2 * X ^ 5 - C 3 * X ^ 6 + C 6 * X ^ 7 - C 6 * X ^ 8 + C 6 * X ^ 9 - C 3 * X ^ 10 := by
      simp only [map_ofNat]; ring
    rw [e, en]
    ext n
    simp only [map_sub, map_add, coeff_mul_X_pow', coeff_gf, coeff_C_mul, coeff_C]
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := a_small
    rcases Nat.lt_or_ge n 11 with hn | hn
    · interval_cases n <;> simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10] <;> norm_num
    · have hr := recurrence n (by omega)
      have hq : (a n : ℚ) = 2 * a (n - 1) - 2 * a (n - 2) + 2 * a (n - 3) - a (n - 4) +
          a (n - 6) - 2 * a (n - 7) + 2 * a (n - 8) - 2 * a (n - 9) + a (n - 10) := by
        exact_mod_cast hr
      simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
        show 4 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega, show 8 ≤ n by omega,
        show 9 ≤ n by omega, show 10 ≤ n by omega, show 5 ≤ n by omega, if_true,
        show n - 5 ≠ 0 by omega, show n - 6 ≠ 0 by omega, show n - 7 ≠ 0 by omega,
        show n - 8 ≠ 0 by omega, show n - 9 ≠ 0 by omega, show n - 10 ≠ 0 by omega, if_false]
      linarith
  calc gf = gf * (D * D⁻¹) := by rw [PowerSeries.mul_inv_cancel _ hden, mul_one]
    _ = (gf * D) * D⁻¹ := (mul_assoc gf _ _).symm
    _ = _ := by rw [key]

/-- Both of Barker's conjectures. -/
theorem conjecture :
    gf = X ^ 5 * (2 - 3 * X + 6 * X ^ 2 - 6 * X ^ 3 + 6 * X ^ 4 - 3 * X ^ 5) *
      ((1 - X) ^ 3 * (1 + X) * (1 - X + X ^ 2) * (1 + X ^ 2) * (1 + X + X ^ 2))⁻¹ ∧
    (∀ n : ℕ, 10 < n → (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 2) + 2 * a (n - 3) -
      a (n - 4) + a (n - 6) - 2 * a (n - 7) + 2 * a (n - 8) - 2 * a (n - 9) + a (n - 10)) :=
  ⟨gf_eq, recurrence⟩

/-- Controls from the entry, a(1..12) = 0, 0, 0, 0, 2, 1, 4, 4, 6, 8, 10, 9, by kernel computation
from the definition. -/
example : a 1 = 0 ∧ a 5 = 2 ∧ a 6 = 1 ∧ a 7 = 4 ∧ a 10 = 8 ∧ a 11 = 10 ∧ a 12 = 9 := by
  unfold a parts
  decide +kernel

end OMA.S_oeis_a308034

theorem OMA.solution : type_of% @OMA.S_oeis_a308034.main :=
  OMA.S_oeis_a308034.conjecture
