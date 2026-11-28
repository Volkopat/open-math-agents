import OMAStatements.S_oeis_a007953
import Mathlib

/-!
# Rank of ten times n among the single digit insertions (OEIS A007953)

Write the digits of `n`, most significant first, as `d :: ds`. Among the values
obtained by inserting one digit (leading zero allowed), those at most
`10 * decimalValue (d :: ds)` are the `d` insertions of a digit `x < d` in front,
together with the values `d * 10 ^ (ds.length + 1) + y` for the insertions `y`
into `ds` with `y ≤ 10 * decimalValue ds`. Inserting `d` itself in front gives the
same value as inserting `d` in front of `ds`, and a larger front digit gives a
value that is too large. By induction the count is the digit sum plus one. For the
digit list of `n` the only value below `10 ^ (ds.length + 1)` is `n` itself (front
digit zero), so the filter in `insertions` removes exactly one value.
-/

namespace R007953

open OMA.S_oeis_a007953

theorem decimalValue_cons (d : ℕ) (ds : List ℕ) :
    decimalValue (d :: ds) = decimalValue ds + 10 ^ ds.length * d := by
  simp only [decimalValue, List.reverse_cons, Nat.ofDigits_append, List.length_reverse,
    Nat.ofDigits_singleton]

theorem decimalValue_lt (ds : List ℕ) (h : ∀ x ∈ ds, x < 10) :
    decimalValue ds < 10 ^ ds.length := by
  have := Nat.ofDigits_lt_base_pow_length (b := 10) (l := ds.reverse) (by norm_num)
    (fun x hx => h x (List.mem_reverse.mp hx))
  simpa [decimalValue] using this

theorem mem_front (d : ℕ) (hd : d < 10) (ds : List ℕ) :
    d * 10 ^ ds.length + decimalValue ds ∈ insertedValues ds := by
  cases ds with
  | nil => simp [insertedValues, decimalValue, hd]
  | cons e es =>
    simp only [insertedValues]
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨d, Finset.mem_range.mpr hd, by simp⟩

theorem step_aux (S : Finset ℕ) (d k P w M v : ℕ) (hk : k ≤ d) (hd : d < 10) (hwP : w < P)
    (hM : M = P * 10) (hv : v = w + P * d) (hmem : ∀ x, x < 10 → x * P + w ∈ S) :
    (((Finset.range 10).image (fun x => x * M + v) ∪ S.image (fun x => d * M + x)).filter
        (fun y => k * M ≤ y ∧ y ≤ 10 * v)).card =
      (d - k) + (S.filter (fun y => y ≤ 10 * w)).card := by
  subst hM hv
  have hP : 0 < P := by omega
  have h4 : P * d ≤ P * 9 := Nat.mul_le_mul le_rfl (by omega)
  have hset : (((Finset.range 10).image (fun x => x * (P * 10) + (w + P * d)) ∪
        S.image (fun x => d * (P * 10) + x)).filter
        (fun y => k * (P * 10) ≤ y ∧ y ≤ 10 * (w + P * d))) =
      (Finset.Ico k d).image (fun x => x * (P * 10) + (w + P * d)) ∪
        (S.filter (fun y => y ≤ 10 * w)).image (fun y => d * (P * 10) + y) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_range,
      Finset.mem_Ico]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩ | ⟨z, hz, rfl⟩, h1, h2⟩
      · rcases lt_trichotomy x d with hlt | heq | hgt
        · left
          refine ⟨x, ⟨?_, hlt⟩, rfl⟩
          by_contra hcon
          have h3 : (x + 1) * (P * 10) ≤ k * (P * 10) := Nat.mul_le_mul (by omega) le_rfl
          nlinarith
        · right
          rw [heq] at h2
          refine ⟨d * P + w, ⟨hmem d hd, by nlinarith⟩, ?_⟩
          rw [heq]
          ring
        · exfalso
          have h3 : (d + 1) * (P * 10) ≤ x * (P * 10) := Nat.mul_le_mul (by omega) le_rfl
          nlinarith
      · right
        exact ⟨z, ⟨hz, by nlinarith⟩, rfl⟩
    · rintro (⟨x, ⟨hkx, hxd⟩, rfl⟩ | ⟨z, ⟨hz, hzw⟩, rfl⟩)
      · refine ⟨Or.inl ⟨x, by omega, rfl⟩, ?_, ?_⟩
        · have h3 : k * (P * 10) ≤ x * (P * 10) := Nat.mul_le_mul hkx le_rfl
          exact le_trans h3 (Nat.le_add_right _ _)
        · have h3 : (x + 1) * (P * 10) ≤ d * (P * 10) := Nat.mul_le_mul (by omega) le_rfl
          nlinarith
      · refine ⟨Or.inr ⟨z, hz, rfl⟩, ?_, ?_⟩
        · have h3 : k * (P * 10) ≤ d * (P * 10) := Nat.mul_le_mul hk le_rfl
          exact le_trans h3 (Nat.le_add_right _ _)
        · nlinarith
  have hinj1 : Function.Injective (fun x : ℕ => x * (P * 10) + (w + P * d)) := by
    intro a b hab
    have hab' : a * (P * 10) + (w + P * d) = b * (P * 10) + (w + P * d) := hab
    exact Nat.eq_of_mul_eq_mul_right (by omega) (Nat.add_right_cancel hab')
  have hinj2 : Function.Injective (fun y : ℕ => d * (P * 10) + y) := by
    intro a b hab
    have hab' : d * (P * 10) + a = d * (P * 10) + b := hab
    exact Nat.add_left_cancel hab'
  have hdisj : Disjoint ((Finset.Ico k d).image (fun x => x * (P * 10) + (w + P * d)))
      ((S.filter (fun y => y ≤ 10 * w)).image (fun y => d * (P * 10) + y)) := by
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    simp only [Finset.mem_image, Finset.mem_Ico, Finset.mem_filter] at hy1 hy2
    obtain ⟨x, ⟨_, hxd⟩, rfl⟩ := hy1
    obtain ⟨z, _, hz⟩ := hy2
    have h3 : (x + 1) * (P * 10) ≤ d * (P * 10) := Nat.mul_le_mul (by omega) le_rfl
    nlinarith
  rw [hset, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj1,
    Finset.card_image_of_injective _ hinj2, Nat.card_Ico]

theorem step (d : ℕ) (ds : List ℕ) (k : ℕ) (hk : k ≤ d) (hd : d < 10)
    (hds : ∀ x ∈ ds, x < 10) :
    ((insertedValues (d :: ds)).filter
        (fun y => k * 10 ^ (ds.length + 1) ≤ y ∧ y ≤ 10 * decimalValue (d :: ds))).card =
      (d - k) + ((insertedValues ds).filter (fun y => y ≤ 10 * decimalValue ds)).card := by
  simp only [insertedValues]
  exact step_aux (insertedValues ds) d k (10 ^ ds.length) (decimalValue ds) _ _ hk hd
    (decimalValue_lt ds hds) (pow_succ 10 ds.length) (decimalValue_cons d ds)
    (fun x hx => mem_front x hx ds)

theorem count_le (L : List ℕ) (hL : ∀ x ∈ L, x < 10) :
    ((insertedValues L).filter (fun y => y ≤ 10 * decimalValue L)).card = L.sum + 1 := by
  induction L with
  | nil => first | decide | rfl | simp [insertedValues, decimalValue]
  | cons d ds ih =>
    have hd : d < 10 := hL d (by simp)
    have hds : ∀ x ∈ ds, x < 10 := fun x hx => hL x (by simp [hx])
    have hcongr : (insertedValues (d :: ds)).filter (fun y => y ≤ 10 * decimalValue (d :: ds)) =
        (insertedValues (d :: ds)).filter
          (fun y => 0 * 10 ^ (ds.length + 1) ≤ y ∧ y ≤ 10 * decimalValue (d :: ds)) :=
      Finset.filter_congr (fun y _ => by simp)
    rw [hcongr, step d ds 0 (Nat.zero_le d) hd hds, ih hds, List.sum_cons]
    omega

theorem pos_count (d : ℕ) (ds : List ℕ) (hd0 : 1 ≤ d) (hL : ∀ x ∈ d :: ds, x < 10) :
    ((insertedValues (d :: ds)).filter
        (fun y => 10 ^ (ds.length + 1) ≤ y ∧ y ≤ 10 * decimalValue (d :: ds))).card =
      (d :: ds).sum := by
  have hd : d < 10 := hL d (by simp)
  have hds : ∀ x ∈ ds, x < 10 := fun x hx => hL x (by simp [hx])
  have h := step d ds 1 hd0 hd hds
  rw [one_mul] at h
  rw [h, count_le ds hds, List.sum_cons]
  omega

theorem final_aux (L : List ℕ) (n : ℕ) (hn : 0 < n) (hlt : ∀ x ∈ L, x < 10)
    (hval : decimalValue L = n) (hpow : 10 ^ L.length ≤ 10 * n) :
    L.sum = ((insertedValues L).filter (fun y => 10 ^ L.length ≤ y ∧ y ≤ 10 * n)).card := by
  subst hval
  cases L with
  | nil => simp [decimalValue] at hn
  | cons d ds =>
    have hw := decimalValue_lt ds (fun x hx => hlt x (by simp [hx]))
    have hd0 : 1 ≤ d := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · subst h0
        rw [decimalValue_cons, List.length_cons, pow_succ] at hpow
        nlinarith
      · exact h0
    rw [List.length_cons]
    exact (pos_count d ds hd0 hlt).symm

theorem final (n : ℕ) (hn : 0 < n) : (Nat.digits 10 n).sum = position n := by
  have h := final_aux (Nat.digits 10 n).reverse n hn
    (fun x hx => Nat.digits_lt_base (by norm_num) (List.mem_reverse.mp hx))
    (by simp only [decimalValue, List.reverse_reverse, Nat.ofDigits_digits])
    (by rw [List.length_reverse]; exact Nat.base_pow_length_digits_le 10 n (by norm_num) hn.ne')
  rw [List.sum_reverse, List.length_reverse] at h
  unfold position insertions
  rw [Finset.filter_filter]
  exact h

end R007953

theorem OMA.solution : type_of% @OMA.S_oeis_a007953.main := by
  intro n hn
  exact R007953.final n hn
