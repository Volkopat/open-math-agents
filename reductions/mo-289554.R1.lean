import OMAStatements.S_mo_289554

/-!
The two residue ranges in the four-cubes theorem. The first is the
Sierpiński–Schinzel range and the second is Dem'yanenko's Theorem 1.
-/

namespace OMA.R_mo_289554_R1

private theorem three_cubes_residue (a b c : ℤ) :
    (a ^ 3 + b ^ 3 + c ^ 3) % 9 ≠ 4 ∧ (a ^ 3 + b ^ 3 + c ^ 3) % 9 ≠ 5 := by
  have h : ∀ x y z : ZMod 9, x ^ 3 + y ^ 3 + z ^ 3 ≠ 4 ∧
      x ^ 3 + y ^ 3 + z ^ 3 ≠ 5 := by decide +kernel
  obtain ⟨h4, h5⟩ := h (a : ZMod 9) (b : ZMod 9) (c : ZMod 9)
  constructor
  · intro he
    apply h4
    have he' := (ZMod.intCast_eq_intCast_iff' (a ^ 3 + b ^ 3 + c ^ 3) 4 9).2 (by
      simpa using he)
    simpa only [Int.cast_add, Int.cast_pow, Int.cast_ofNat] using he'
  · intro he
    apply h5
    have he' := (ZMod.intCast_eq_intCast_iff' (a ^ 3 + b ^ 3 + c ^ 3) 5 9).2 (by
      simpa using he)
    simpa only [Int.cast_add, Int.cast_pow, Int.cast_ofNat] using he'

private theorem infinite_neg {N : ℤ}
    (h : {v : ℤ × ℤ × ℤ × ℤ | v.1 ^ 3 + v.2.1 ^ 3 + v.2.2.1 ^ 3 + v.2.2.2 ^ 3 = -N}.Infinite) :
    {v : ℤ × ℤ × ℤ × ℤ | v.1 ^ 3 + v.2.1 ^ 3 + v.2.2.1 ^ 3 + v.2.2.2 ^ 3 = N}.Infinite := by
  let f (v : ℤ × ℤ × ℤ × ℤ) := (-v.1, -v.2.1, -v.2.2.1, -v.2.2.2)
  have inv (v : ℤ × ℤ × ℤ × ℤ) : f (f v) = v := by
    rcases v with ⟨a, b, c, d⟩
    simp [f]
  have hinj : Function.Injective f := fun x y he =>
    (inv x).symm.trans ((congrArg f he).trans (inv y))
  refine ((Set.infinite_image_iff hinj.injOn).mpr h).mono ?_
  rintro _ ⟨v, hv, rfl⟩
  simp only [f, Set.mem_ofPred_eq] at hv ⊢
  linear_combination -hv

def H1 : Prop := ∀ N : ℤ, N % 3 = 0 ∨ N % 18 = 1 ∨ N % 18 = 7 ∨ N % 18 = 8 →
  {v : ℤ × ℤ × ℤ × ℤ | v.1 ^ 3 + v.2.1 ^ 3 + v.2.2.1 ^ 3 + v.2.2.2 ^ 3 = N}.Infinite

def H2 : Prop := ∀ N : ℤ, N % 18 = 2 →
  {v : ℤ × ℤ × ℤ × ℤ | v.1 ^ 3 + v.2.1 ^ 3 + v.2.2.1 ^ 3 + v.2.2.2 ^ 3 = N}.Infinite

theorem main : H1 → H2 → type_of% @OMA.S_mo_289554.main := by
  intro h1 h2 N hN
  obtain ⟨a, b, c, rfl⟩ := hN
  let n := a ^ 3 + b ^ 3 + c ^ 3
  change {v : ℤ × ℤ × ℤ × ℤ | v.1 ^ 3 + v.2.1 ^ 3 + v.2.2.1 ^ 3 + v.2.2.2 ^ 3 = n}.Infinite
  have ⟨h4, h5⟩ : n % 9 ≠ 4 ∧ n % 9 ≠ 5 := three_cubes_residue a b c
  by_cases hPos : n % 3 = 0 ∨ n % 18 = 1 ∨ n % 18 = 7 ∨ n % 18 = 8
  · exact h1 n hPos
  by_cases hNeg : (-n) % 3 = 0 ∨ (-n) % 18 = 1 ∨ (-n) % 18 = 7 ∨ (-n) % 18 = 8
  · exact infinite_neg (h1 (-n) hNeg)
  by_cases hTwo : n % 18 = 2
  · exact h2 n hTwo
  exact infinite_neg (h2 (-n) (by omega))

end OMA.R_mo_289554_R1
