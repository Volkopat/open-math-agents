import OMAStatements.S_mo_44817

namespace OMA.S_mo_44817

/-- An infinite strictly increasing sequence of natural roots forces a
    polynomial over a characteristic-zero integral domain to vanish. -/
theorem polynomial_eq_zero_of_nat_roots {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (P : Polynomial R) (v : ℕ → ℕ) (hv : StrictMono v)
    (h : ∀ t : ℕ, P.eval (v t : R) = 0) : P = 0 := by
  apply P.eq_zero_of_infinite_isRoot
  have hinj : Function.Injective (fun t : ℕ ↦ (v t : R)) :=
    Nat.cast_injective.comp hv.injective
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨t, rfl⟩
  exact h t

/-- A bivariate rational polynomial vanishes identically when it vanishes on
    the product of two infinite, strictly increasing sequences of natural numbers. -/
theorem polynomial_eq_zero_of_grid (P : Polynomial (Polynomial ℚ))
    (v w : ℕ → ℕ) (hv : StrictMono v) (hw : StrictMono w)
    (h : ∀ t u : ℕ, (P.eval (Polynomial.C (v t : ℚ))).eval (w u : ℚ) = 0) :
    P = 0 := by
  have hv' : Function.Injective (fun t : ℕ ↦ Polynomial.C (v t : ℚ)) :=
    Polynomial.C_injective.comp (Nat.cast_injective.comp hv.injective)
  have hw' : Function.Injective (fun u : ℕ ↦ (w u : ℚ)) :=
    Nat.cast_injective.comp hw.injective
  apply P.eq_zero_of_infinite_isRoot
  apply (Set.infinite_range_of_injective hv').mono
  rintro _ ⟨t, rfl⟩
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply (Set.infinite_range_of_injective hw').mono
  rintro _ ⟨u, rfl⟩
  exact h t u

end OMA.S_mo_44817

namespace OMA.S_mo_44817

/-- Indicator of the perfect squares. -/
noncomputable def mark (n : ℕ) : ℕ := if IsSquare n then 1 else 0

/-- A block in which the only square occurs at the prescribed offset. -/
def start (d a t : ℕ) : ℕ := (d+t+2)^2-a

theorem start_add (d a t : ℕ) (ha : a≤d) : start d a t + a = (d+t+2)^2 := by
  apply Nat.sub_add_cancel
  exact (show a≤d+t+2 by omega).trans (Nat.le_self_pow (by decide) _)

theorem start_mono (d a : ℕ) (ha : a≤d) : StrictMono (start d a) := by
  apply strictMono_nat_of_lt_succ
  intro t
  have h0 := start_add d a t ha
  have h1 := start_add d a (t+1) ha
  nlinarith only [h0,h1,Nat.zero_le d,Nat.zero_le t]

theorem mark_start (d a t b : ℕ) (ha : a≤d) (hb : b≤d) :
    mark (start d a t+b) = if b=a then 1 else 0 := by
  have hs := start_add d a t ha
  have test : IsSquare (start d a t+b) ↔ b=a := by
    rw [isSquare_iff_exists_sq]
    constructor
    · rintro ⟨z,hz⟩
      have heq : z=d+t+2 := by
        rcases lt_trichotomy z (d+t+2) with h|h|h
        · have hle := Nat.pow_le_pow_left (show z≤d+t+1 by omega) 2
          nlinarith only [hs,hz,hle,ha,hb,Nat.zero_le b,Nat.zero_le t]
        · exact h
        · have hle := Nat.pow_le_pow_left (show d+t+3 ≤ z by omega) 2
          nlinarith only [hs,hz,hle,ha,hb,Nat.zero_le a,Nat.zero_le t]
      rw [heq] at hz
      omega
    · rintro rfl
      exact ⟨d+t+2,hs⟩
  simp only [mark,test]

end OMA.S_mo_44817

namespace OMA.S_mo_44817

/-- One summand depends on the first coordinate, and one depends on the two other coordinates. -/
noncomputable def exampleArray (i j k : ℕ) : ℕ := mark i + mark j * mark k

private theorem recurrence_from_mixed_difference (A : ℕ → ℕ → ℕ → ℕ)
    (h : ∀ t x y : ℕ, (A t x y : ℚ) - A t x (y+1) - A t (x+1) y + A t (x+1) (y+1) = 0) :
    HasPlanarRecurrence A := by
  refine ⟨2,fun a b => if a=b then 1 else -1,⟨0,0,by simp⟩,?_⟩
  intro t x y
  simp [Fin.sum_univ_two,value]
  linear_combination h t x y

private theorem marker {d : ℕ} (a b : Fin d) (x : ℕ) :
    mark (start d a.val x + b.val) = if b=a then 1 else 0 := by
  simpa only [Fin.val_inj] using mark_start d a.val x b.val a.isLt.le b.isLt.le

/-- The square indicator cannot itself satisfy a nonzero one-variable polynomial recurrence. -/
theorem square_indicator_nonrecursive (d : ℕ) (p : Fin d → Polynomial ℚ)
    (h : ∀ x : ℕ, (∑ a : Fin d, (p a).eval (x : ℚ) * (mark (x+a.val) : ℚ))=0)
    (a : Fin d) : p a=0 := by
  apply polynomial_eq_zero_of_nat_roots (p a) (start d a.val) (start_mono d a.val a.isLt.le)
  intro t
  simpa [marker,mul_ite] using h (start d a.val t)

private noncomputable def val₂ (P : Polynomial (Polynomial ℚ)) (x y : ℕ) : ℚ :=
  (P.eval (x : Polynomial ℚ)).eval (y : ℚ)

/-- Even after fixing the first coordinate, every linear relation in the other two
coordinates has identically zero polynomial coefficients. -/
theorem slice_nonrecursive (i d : ℕ) (c : Fin d → Fin d → Polynomial (Polynomial ℚ))
    (hrec : ∀ x y : ℕ, (∑ a : Fin d, ∑ b : Fin d,
      val₂ (c a b) x y * (exampleArray i (x+a.val) (y+b.val) : ℚ))=0)
    (a b : Fin d) : c a b=0 := by
  let gap := fun t => start (d+1) 0 t + 1
  have hgap (t : ℕ) (r : Fin d) : mark (gap t + r.val)=0 := by
    have hr : 1+r.val ≤ d+1 := by omega
    simpa [gap,Nat.add_assoc] using mark_start (d+1) 0 t (1+r.val) (by omega) hr
  let B := ∑ r : Fin d, ∑ s : Fin d, c r s * (mark i : Polynomial (Polynomial ℚ))
  have hB (x y : ℕ) : val₂ B x y =
      ∑ r : Fin d, ∑ s : Fin d, val₂ (c r s) x y * (mark i : ℚ) := by
    simp [B,val₂,Polynomial.eval_finsetSum]
  have hbzero : B=0 := by
    apply polynomial_eq_zero_of_grid B gap id
      (fun x y h => Nat.add_lt_add_right ((start_mono (d+1) 0 (by omega)) h) 1) strictMono_id
    intro x y
    have h := hrec (gap x) y
    simp only [exampleArray,hgap,zero_mul,add_zero] at h
    simpa [val₂] using (hB (gap x) y).trans h
  have hbase (x y : ℕ) :
      (∑ r : Fin d, ∑ s : Fin d, val₂ (c r s) x y * (mark i : ℚ))=0 := by
    rw [← hB,hbzero]
    simp [val₂]
  apply polynomial_eq_zero_of_grid _ (start d a.val) (start d b.val)
    (start_mono d a.val a.isLt.le) (start_mono d b.val b.isLt.le)
  intro x y
  have h := hrec (start d a.val x) (start d b.val y)
  simp only [exampleArray,marker,Nat.cast_add,Nat.cast_mul,mul_add,Finset.sum_add_distrib,
    hbase,zero_add] at h
  simpa [val₂,mul_ite,ite_mul] using h

private theorem no_third_plane : ¬ HasPlanarRecurrence exampleArray := by
  rintro ⟨d,c,⟨a,b,hn⟩,hrec⟩
  apply hn
  apply polynomial_eq_zero_of_nat_roots (c a b) id strictMono_id
  intro i
  exact slice_nonrecursive i d (fun r s => (c r s).eval (i : Polynomial (Polynomial ℚ))) (hrec i) a b

end OMA.S_mo_44817

open OMA.S_mo_44817 in
theorem OMA.solution : type_of% @OMA.S_mo_44817.main := by
  refine ⟨exampleArray,recurrence_from_mixed_difference _ ?_,
    recurrence_from_mixed_difference _ ?_,no_third_plane⟩ <;>
    intro t x y <;> simp [exampleArray] <;> ring
