import OMAStatements.S_oeis_a146557
import Mathlib

namespace OMA.A146557

open OMA.S_oeis_a146557

theorem valid_image {n : ℕ} (t : Point n) {s : Finset (Point n)} (h : valid s) :
    valid (s.image (fun x => t + x)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (add_right_injective t)]; exact h.1
  · simp only [Finset.mem_image]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
    have := h.2.1 x hx y hy (by rintro rfl; exact hne rfl)
    simpa using this
  · simp only [Finset.mem_image]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    have := h.2.2 x hx y hy z hz
    simp only [Prod.fst_add, Prod.snd_add, add_sub_add_left_eq_sub]
    exact this

noncomputable instance act (n : ℕ) : AddAction (Point n) {s : Finset (Point n) // valid s} where
  vadd t s := ⟨s.1.image (fun x => t + x), valid_image t s.2⟩
  zero_vadd s := Subtype.ext (by
    show s.1.image (fun x => 0 + x) = s.1
    simp)
  add_vadd t u s := Subtype.ext (by
    show s.1.image (fun x => t + u + x) = (s.1.image (fun x => u + x)).image (fun x => t + x)
    rw [Finset.image_image]
    refine Finset.image_congr (fun x _ => ?_)
    simp [add_assoc])

theorem free {n : ℕ} (h3 : ¬ 3 ∣ n) (t : Point n) (s : {s : Finset (Point n) // valid s})
    (h : t +ᵥ s = s) : t = 0 := by
  have h1 : s.1.image (fun x => t + x) = s.1 := congrArg Subtype.val h
  have h2 : ∑ x ∈ s.1.image (fun x => t + x), x = ∑ x ∈ s.1, x := by rw [h1]
  rw [Finset.sum_image (fun x _ y _ hxy => add_right_injective t hxy), Finset.sum_add_distrib,
    Finset.sum_const, s.2.1] at h2
  have h4 : (3 : ℕ) • t = 0 := by simpa using h2
  have hu : IsUnit ((3 : ℕ) : ZMod n) :=
    (ZMod.isUnit_iff_coprime 3 n).2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)
  have h5 := congrArg Prod.fst h4
  have h6 := congrArg Prod.snd h4
  simp only [Prod.fst_zero, Prod.snd_zero, nsmul_eq_mul] at h5 h6
  exact Prod.ext (hu.mul_right_eq_zero.1 h5) (hu.mul_right_eq_zero.1 h6)

end OMA.A146557

open OMA.S_oeis_a146557 OMA.A146557 in
theorem OMA.solution : type_of% @OMA.S_oeis_a146557.main := by
  intro n hn h3
  have : NeZero n := ⟨hn.ne'⟩
  have e : {s : Finset (Point n) // valid s} ≃
      Σ g : Point n, AddAction.fixedBy {s : Finset (Point n) // valid s} g :=
    Equiv.ofBijective (fun x => ⟨0, x, zero_vadd _ x⟩)
      ⟨fun x y hxy => congrArg (fun p => (p.2 : {s : Finset (Point n) // valid s})) hxy, by
        rintro ⟨g, x, hx⟩
        obtain rfl := free h3 g x hx
        exact ⟨x, rfl⟩⟩
  unfold a
  rw [Nat.card_congr (e.trans (AddAction.sigmaFixedByEquivOrbitsProdAddGroup (Point n) _)),
    Nat.card_prod, Nat.card_prod, Nat.card_zmod, ← sq]
  exact dvd_mul_left _ _
