import OMAStatements.S_oeis_a211480

-- Problem: A211480 (George Beck's conjecture): triples count = partitions of 4n+2 into 3 parts.
-- Both reduce to S(N) = #{(q,p) : 2q + 3p <= N}; S(N+6) = S(N) + N + 6 gives S(6n+1) = S(4n) + S(4n-1) + S(2n-1).
-- Credit: @bnb9001

namespace OMA_A211480_Proof

open Finset OMA.S_oeis_a211480

/-- the lattice-point set `{(q,p) : 2q + 3p ≤ N}` -/
def Sset (N : ℕ) : Finset (ℕ × ℕ) :=
  (range (N + 1) ×ˢ range (N + 1)).filter (fun qp => 2 * qp.1 + 3 * qp.2 ≤ N)

def S (N : ℕ) : ℕ := (Sset N).card

theorem mem_Sset {N : ℕ} {qp : ℕ × ℕ} : qp ∈ Sset N ↔ 2 * qp.1 + 3 * qp.2 ≤ N := by
  simp only [Sset, mem_filter, mem_product, mem_range]
  omega

theorem card_line (M c : ℕ) :
    ((range (M + 1)).filter (fun q => 2 * q ≤ c)).card = min M (c / 2) + 1 := by
  have : (range (M + 1)).filter (fun q => 2 * q ≤ c) = range (min M (c / 2) + 1) := by
    ext q; simp only [mem_filter, mem_range]; omega
  rw [this, card_range]

theorem S_step (N : ℕ) : S (N + 6) = S N + N + 6 := by
  unfold S
  set X := Sset (N + 6)
  have h1 := card_filter_add_card_filter_not (s := X) (p := fun qp => 2 ≤ qp.2)
  have h2 := card_filter_add_card_filter_not (s := X.filter (fun qp => ¬ 2 ≤ qp.2))
    (p := fun qp => qp.2 = 0)
  have hA : (X.filter (fun qp => 2 ≤ qp.2)) = (Sset N).image (fun qp => (qp.1, qp.2 + 2)) := by
    ext ⟨q, p⟩
    simp only [X, mem_filter, mem_image, mem_Sset, Prod.mk.injEq]
    constructor
    · rintro ⟨h, hp⟩; exact ⟨(q, p - 2), by simp only; omega, rfl, by omega⟩
    · rintro ⟨⟨q', p'⟩, h, rfl, rfl⟩; simp only at h; omega
  have hAc : ((Sset N).image (fun qp => (qp.1, qp.2 + 2))).card = (Sset N).card :=
    card_image_of_injective _ (fun x y h => by
      simp only [Prod.mk.injEq] at h; exact Prod.ext h.1 (by omega))
  have hB : ((X.filter (fun qp => ¬ 2 ≤ qp.2)).filter (fun qp => qp.2 = 0)) =
      ((range (N + 7)).filter (fun q => 2 * q ≤ N + 6)).image (fun q => (q, 0)) := by
    ext ⟨q, p⟩
    simp only [X, Sset, mem_filter, mem_image, mem_product, mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨⟨hq, hp⟩, h⟩, h2⟩, h0⟩; exact ⟨q, ⟨by omega, by omega⟩, rfl, h0.symm⟩
    · rintro ⟨q', ⟨hq, h⟩, rfl, rfl⟩; omega
  have hC : ((X.filter (fun qp => ¬ 2 ≤ qp.2)).filter (fun qp => ¬ qp.2 = 0)) =
      ((range (N + 7)).filter (fun q => 2 * q ≤ N + 3)).image (fun q => (q, 1)) := by
    ext ⟨q, p⟩
    simp only [X, Sset, mem_filter, mem_image, mem_product, mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨⟨hq, hp⟩, h⟩, h2⟩, h0⟩; exact ⟨q, ⟨by omega, by omega⟩, rfl, by omega⟩
    · rintro ⟨q', ⟨hq, h⟩, rfl, rfl⟩; omega
  have hBc := card_image_of_injective ((range (N + 7)).filter (fun q => 2 * q ≤ N + 6))
    (f := fun q => (q, 0)) (fun x y h => by simp only [Prod.mk.injEq] at h; exact h.1)
  have hCc := card_image_of_injective ((range (N + 7)).filter (fun q => 2 * q ≤ N + 3))
    (f := fun q => (q, 1)) (fun x y h => by simp only [Prod.mk.injEq] at h; exact h.1)
  rw [card_line] at hBc hCc
  rw [← h1, ← h2, hA, hAc, hB, hC, hBc, hCc]
  omega

theorem S_small : S 0 = 1 ∧ S 1 = 1 ∧ S 2 = 2 ∧ S 3 = 3 ∧ S 4 = 4 ∧ S 5 = 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem identity : ∀ n : ℕ, 1 ≤ n → S (6 * n + 1) = S (4 * n) + S (4 * n - 1) + S (2 * n - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    obtain ⟨s0, s1, s2, s3, s4, s5⟩ := S_small
    have st := S_step
    rcases Nat.lt_or_ge n 4 with hlt | hge
    · interval_cases n
      · -- n = 1: S 7 = S 4 + S 3 + S 1
        have := st 1; norm_num at this ⊢; omega
      · -- n = 2: S 13 = S 8 + S 7 + S 3
        have a7 := st 1; have a13 := st 7; have a8 := st 2
        norm_num at a7 a13 a8 ⊢; omega
      · -- n = 3: S 19 = S 12 + S 11 + S 5
        have a7 := st 1; have a13 := st 7; have a19 := st 13
        have a6 := st 0; have a12 := st 6; have a11 := st 5
        norm_num at a7 a13 a19 a6 a12 a11 ⊢; omega
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      have IH := ih k (by omega) (by omega)
      have e1 := st (6 * k + 1); have e2 := st (6 * k + 7); have e3 := st (6 * k + 13)
      have f1 := st (4 * k); have f2 := st (4 * k + 6)
      have g1 := st (4 * k - 1); have g2 := st (4 * k + 5)
      have h1 := st (2 * k - 1)
      have hk1 : 1 ≤ k := by omega
      rw [show 4 * (k + 3) - 1 = 4 * k + 5 + 6 by omega, show 4 * (k + 3) = 4 * k + 6 + 6 by ring,
        show 6 * (k + 3) + 1 = 6 * k + 13 + 6 by ring, show 2 * (k + 3) - 1 = 2 * k - 1 + 6 by omega]
      rw [show 6 * k + 7 + 6 = 6 * k + 13 by ring] at e2
      rw [show 6 * k + 1 + 6 = 6 * k + 7 by ring] at e1
      rw [show 4 * k - 1 + 6 = 4 * k + 5 by omega] at g1
      omega

theorem a_zero : a 0 = 0 := by
  unfold a
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨w, x, y⟩ ht
  simp only [mem_product, mem_Icc, Nat.cast_zero, neg_zero] at ht
  show ¬ (w + 2 * x + 3 * y = 1)
  omega

theorem p3_zero : p3 2 = 0 := by decide

theorem p3_eq (n : ℕ) (hn : 1 ≤ n) : p3 (4 * n + 2) = S (4 * n - 1) := by
  unfold p3 S
  apply Finset.card_nbij' (fun t : ℕ × ℕ × ℕ => (t.2.1 - t.1, t.1 - 1))
    (fun qp : ℕ × ℕ => (qp.2 + 1, qp.2 + 1 + qp.1, 4 * n + 2 - (qp.2 + 1) - (qp.2 + 1 + qp.1)))
  · rintro ⟨x, y, z⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Icc] at h
    simp only [mem_coe, mem_Sset]
    omega
  · rintro ⟨q, p⟩ h
    simp only [mem_coe, mem_Sset] at h
    simp only [mem_coe, mem_filter, mem_product, mem_Icc]
    omega
  · rintro ⟨x, y, z⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Icc] at h
    simp only [Prod.mk.injEq]
    omega
  · rintro ⟨q, p⟩ h
    simp only [mem_coe, mem_Sset] at h
    simp only [Prod.mk.injEq]
    omega

theorem a_eq (n : ℕ) (hn : 1 ≤ n) : a n + S (2 * n - 1) + S (4 * n) = S (6 * n + 1) := by
  set A := Sset (6 * n + 1)
  have h1 := card_filter_add_card_filter_not (s := A) (p := fun qp => 2 * n + 1 ≤ qp.1)
  have h2 := card_filter_add_card_filter_not (s := A.filter (fun qp => ¬ 2 * n + 1 ≤ qp.1))
    (p := fun qp => 4 * n + 1 ≤ 2 * qp.1 + 3 * qp.2)
  -- the part with large q
  have hA2 : A.filter (fun qp => 2 * n + 1 ≤ qp.1) =
      (Sset (2 * n - 1)).image (fun qp => (qp.1 + (2 * n + 1), qp.2)) := by
    ext ⟨q, p⟩
    simp only [A, mem_filter, mem_image, mem_Sset, Prod.mk.injEq]
    constructor
    · rintro ⟨h, hq⟩; exact ⟨(q - (2 * n + 1), p), by simp only; omega, by omega, rfl⟩
    · rintro ⟨⟨q', p'⟩, h, rfl, rfl⟩; simp only at h; omega
  have hA2c : ((Sset (2 * n - 1)).image (fun qp => (qp.1 + (2 * n + 1), qp.2))).card =
      S (2 * n - 1) :=
    card_image_of_injective _ (fun x y h => by
      simp only [Prod.mk.injEq] at h; exact Prod.ext (by omega) h.2)
  -- the part below the strip
  have hA3 : (A.filter (fun qp => ¬ 2 * n + 1 ≤ qp.1)).filter
      (fun qp => ¬ 4 * n + 1 ≤ 2 * qp.1 + 3 * qp.2) = Sset (4 * n) := by
    ext ⟨q, p⟩
    simp only [A, mem_filter, mem_Sset]
    omega
  -- the strip is in bijection with the triples
  have hA1 : ((A.filter (fun qp => ¬ 2 * n + 1 ≤ qp.1)).filter
      (fun qp => 4 * n + 1 ≤ 2 * qp.1 + 3 * qp.2)).card = a n := by
    unfold a
    symm
    apply Finset.card_nbij' (fun t : ℤ × ℤ × ℤ => ((t.2.1 + n).toNat, (t.2.2 + n).toNat))
      (fun qp : ℕ × ℕ =>
        (1 - 2 * ((qp.1 : ℤ) - n) - 3 * ((qp.2 : ℤ) - n), (qp.1 : ℤ) - n, (qp.2 : ℤ) - n))
    · rintro ⟨w, x, y⟩ h
      simp only [mem_coe, mem_filter, mem_product, mem_Icc] at h
      simp only [mem_coe, A, mem_filter, mem_Sset]
      have hx : (((x + n).toNat : ℕ) : ℤ) = x + n := Int.toNat_of_nonneg (by omega)
      have hy : (((y + n).toNat : ℕ) : ℤ) = y + n := Int.toNat_of_nonneg (by omega)
      omega
    · rintro ⟨q, p⟩ h
      simp only [mem_coe, A, mem_filter, mem_Sset] at h
      simp only [mem_coe, mem_filter, mem_product, mem_Icc]
      omega
    · rintro ⟨w, x, y⟩ h
      simp only [mem_coe, mem_filter, mem_product, mem_Icc] at h
      have hx : (((x + n).toNat : ℕ) : ℤ) = x + n := Int.toNat_of_nonneg (by omega)
      have hy : (((y + n).toNat : ℕ) : ℤ) = y + n := Int.toNat_of_nonneg (by omega)
      simp only [Prod.mk.injEq]
      omega
    · rintro ⟨q, p⟩ h
      simp only [Prod.mk.injEq]
      constructor <;> omega
  have hS : S (6 * n + 1) = A.card := rfl
  rw [hS, ← h1, ← h2, hA2, hA2c, hA3, hA1]
  unfold S
  omega

end OMA_A211480_Proof

open Finset OMA.S_oeis_a211480 OMA_A211480_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a211480.main := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [a_zero, show 4 * 0 + 2 = 2 by rfl, p3_zero]
  · have h1 := a_eq n hn
    have h2 := identity n hn
    rw [p3_eq n hn]
    omega
