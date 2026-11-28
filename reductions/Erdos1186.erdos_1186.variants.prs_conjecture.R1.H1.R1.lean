import OMAReductions.R_Erdos1186_erdos_1186_variants_prs_conjecture_R1

/-!
Carlos Toledo's report gives three separate certificates for the near-cut side
of the two-fifths threshold. The regions below are the discrete versions of
the inner region and the first two slabs, with the parent's linear error.
See §§2–3 of https://carlostoledo.co/reports/delta3.html.
-/

open Finset
open scoped BigOperators Classical

namespace OMA.R_Erdos1186_erdos_1186_variants_prs_conjecture_R1_H1_R1

private theorem complement_card (n : ℕ) (d : ℕ → Bool) :
    ((Icc 1 n).filter (fun x => (!d x) = true)).card =
      n - ((Icc 1 n).filter (fun x => d x = true)).card := by
  have hfilters : (Icc 1 n).filter (fun x => (!d x) = true) =
      (Icc 1 n).filter (fun x => ¬ d x = true) := by
    ext x
    cases hx : d x <;> simp [hx]
  have hcard := card_filter_add_card_filter_not (s := Icc 1 n) (fun x => d x = true)
  rw [hfilters]
  have htotal : (Icc 1 n).card = n := by simp
  omega

private theorem complement_weight (R : Finset (ℕ × ℕ)) (ref d : ℕ → Bool) :
    (∑ p ∈ R, (if (!d p.1) = (!d p.2) then 0 else
      if ref p.1 = ref p.2 then 1 else -1 : ℤ)) =
    ∑ p ∈ R, (if d p.1 = d p.2 then 0 else
      if ref p.1 = ref p.2 then 1 else -1 : ℤ) := by
  simp only [Bool.not_inj_iff]

/-- The inner certificate region, ending at one fifth of the interval. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℕ, 1 ≤ w → ∀ d : ℕ → Bool,
    let n := 1096*w
    let ref := fun x : ℕ =>
      let b := (x - 1) / (2*w)
      b < 28 || (34 ≤ b && b < 62) || (99 ≤ b && b < 158) ||
      (274 ≤ b && b < 390) || (449 ≤ b && b < 486) || (514 ≤ b && b < 520)
    let R := ((Icc 1 n ×ˢ Icc 1 n).filter fun p : ℕ × ℕ =>
      p.1 + 1 ≤ 2*p.2 ∧ 2*p.2 ≤ p.1 + n)
    let t := ((Icc 1 n).filter (fun x => d x = true)).card
    5 * t ≤ n →
      ((∑ p ∈ R, (if d p.1 = d p.2 then 0 else
        if ref p.1 = ref p.2 then 1 else -1 : ℤ) : ℤ) : ℝ) ≤ C * n

/-- The first slab, from one fifth to three tenths of the interval. -/
def H2 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℕ, 1 ≤ w → ∀ d : ℕ → Bool,
    let n := 1096*w
    let ref := fun x : ℕ =>
      let b := (x - 1) / (2*w)
      b < 28 || (34 ≤ b && b < 62) || (99 ≤ b && b < 158) ||
      (274 ≤ b && b < 390) || (449 ≤ b && b < 486) || (514 ≤ b && b < 520)
    let R := ((Icc 1 n ×ˢ Icc 1 n).filter fun p : ℕ × ℕ =>
      p.1 + 1 ≤ 2*p.2 ∧ 2*p.2 ≤ p.1 + n)
    let t := ((Icc 1 n).filter (fun x => d x = true)).card
    n ≤ 5 * t → 10 * t ≤ 3 * n →
      ((∑ p ∈ R, (if d p.1 = d p.2 then 0 else
        if ref p.1 = ref p.2 then 1 else -1 : ℤ) : ℤ) : ℝ) ≤ C * n

/-- The second slab, from three tenths to two fifths of the interval. -/
def H3 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℕ, 1 ≤ w → ∀ d : ℕ → Bool,
    let n := 1096*w
    let ref := fun x : ℕ =>
      let b := (x - 1) / (2*w)
      b < 28 || (34 ≤ b && b < 62) || (99 ≤ b && b < 158) ||
      (274 ≤ b && b < 390) || (449 ≤ b && b < 486) || (514 ≤ b && b < 520)
    let R := ((Icc 1 n ×ˢ Icc 1 n).filter fun p : ℕ × ℕ =>
      p.1 + 1 ≤ 2*p.2 ∧ 2*p.2 ≤ p.1 + n)
    let t := ((Icc 1 n).filter (fun x => d x = true)).card
    3 * n ≤ 10 * t → 5 * t ≤ 2 * n →
      ((∑ p ∈ R, (if d p.1 = d p.2 then 0 else
        if ref p.1 = ref p.2 then 1 else -1 : ℤ) : ℤ) : ℝ) ≤ C * n

theorem main : H1 → H2 → H3 → OMA.R_Erdos1186_erdos_1186_variants_prs_conjecture_R1.H1 := by
  rintro ⟨C₁, hC₁, h₁⟩ ⟨C₂, _, h₂⟩ ⟨C₃, _, h₃⟩
  let C := max C₁ (max C₂ C₃)
  have hle₁ : C₁ ≤ C := le_max_left _ _
  have hle₂ : C₂ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hle₃ : C₃ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, hC₁.trans hle₁, ?_⟩
  intro w hw d
  let n := 1096*w
  let ref := fun x : ℕ =>
    let b := (x - 1) / (2*w)
    b < 28 || (34 ≤ b && b < 62) || (99 ≤ b && b < 158) ||
    (274 ≤ b && b < 390) || (449 ≤ b && b < 486) || (514 ≤ b && b < 520)
  let R := ((Icc 1 n ×ˢ Icc 1 n).filter fun p : ℕ × ℕ =>
    p.1 + 1 ≤ 2*p.2 ∧ 2*p.2 ≤ p.1 + n)
  let size := fun e : ℕ → Bool => ((Icc 1 n).filter (fun x => e x = true)).card
  let gain := fun e : ℕ → Bool => ∑ p ∈ R, (if e p.1 = e p.2 then 0 else
    if ref p.1 = ref p.2 then 1 else -1 : ℤ)
  change 5 * min (size d) (n - size d) ≤ 2*n → (gain d : ℝ) ≤ C * n
  intro hnear
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have apply_region (e : ℕ → Bool) (he : 5 * size e ≤ 2*n) :
      (gain e : ℝ) ≤ C * n := by
    by_cases hsmall : 5 * size e ≤ n
    · exact (h₁ w hw e hsmall).trans (mul_le_mul_of_nonneg_right hle₁ hn)
    by_cases hmiddle : 10 * size e ≤ 3 * n
    · have hlo : n ≤ 5 * size e := by omega
      exact (h₂ w hw e hlo hmiddle).trans (mul_le_mul_of_nonneg_right hle₂ hn)
    · have hlo : 3 * n ≤ 10 * size e := by omega
      exact (h₃ w hw e hlo he).trans (mul_le_mul_of_nonneg_right hle₃ hn)
  by_cases horient : size d ≤ n - size d
  · rw [min_eq_left horient] at hnear
    exact apply_region d hnear
  · rw [min_eq_right (le_of_lt (lt_of_not_ge horient))] at hnear
    have hs : size (fun x => !d x) = n - size d := complement_card n d
    have hg : gain (fun x => !d x) = gain d := complement_weight R ref d
    rw [← hg]
    exact apply_region (fun x => !d x) (hs.symm ▸ hnear)

end OMA.R_Erdos1186_erdos_1186_variants_prs_conjecture_R1_H1_R1
