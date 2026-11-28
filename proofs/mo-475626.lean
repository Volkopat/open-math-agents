import OMAStatements.S_mo_475626

/-!
Complete proof by @connoranderson, linked by statement PR #21601 and desk DONE #97048.
Pinned source: https://github.com/connoranderson/open-math-agents/blob/9a83654ab475d2d93bb03d999792ff823ce3ebde/proofs/mo-475626.lean
The mathematical source is unchanged; this port adds provenance and current-checker validation.
Port and validation: @rodolfoquint.

# Signed enumeration of monomial symmetric polynomials on roots of unity

Source: wkmath, https://mathoverflow.net/questions/475626 (CC BY-SA 4.0).
The discussion gives elementary-symmetric and plethystic approaches, and
Miek Messerschmidt observes the weight divisibility condition.
Credit: @connoranderson.

Sum the determinants of a Fourier matrix with row j replaced by row
j+b_j modulo n over all distinct rearrangements b of the parts.
Row collisions give zero and row permutations give their signs.
Expansion by permutations instead gives the monomial symmetric value
times the Fourier determinant. This Vandermonde determinant is nonzero.
-/

namespace OMA.S_mo_475626
open Matrix
open scoped BigOperators
noncomputable section

private lemma rearrange_mem {n : ℕ} {a b : Fin n → ℕ} (hb : b ∈ arrangements a)
    (σ : Equiv.Perm (Fin n)) : b ∘ σ ∈ arrangements a := by
  obtain ⟨τ,_,rfl⟩ := Finset.mem_image.mp hb
  exact Finset.mem_image.mpr ⟨σ.trans τ,Finset.mem_univ _,rfl⟩

private lemma rearranged_sum {n : ℕ} (a : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
    (x : Fin n → ℂ) :
    (∑ b ∈ arrangements a, ∏ i, x i ^ b (σ i)) = monomialSymmetric a x := by
  unfold monomialSymmetric
  apply Finset.sum_bij' (fun b _ => b ∘ σ) (fun b _ => b ∘ σ.symm)
  · exact fun _ hb => rearrange_mem hb _
  · exact fun _ hb => rearrange_mem hb _
  · intro b _
    funext i
    simp
  · intro b _
    funext i
    simp
  · intro b _
    rfl

private lemma det_shift {n : ℕ} (b : Fin (n+1) → ℕ)
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    (M.submatrix (shift b) id).det = (contribution b : ℂ)*M.det := by
  classical
  by_cases hb : Function.Bijective (shift b)
  · let e := Equiv.ofBijective (shift b) hb
    change (M.submatrix e id).det = _
    rw [Matrix.det_permute]
    simp only [contribution,dif_pos hb,e]
  · have hni : ¬ Function.Injective (shift b) := fun h => hb
      ⟨h,Finite.surjective_of_injective h⟩
    obtain ⟨i,j,he,hij⟩ := Function.not_injective_iff.mp hni
    have zero : (M.submatrix (shift b) id).det=0 :=
      Matrix.det_zero_of_row_eq hij (by funext k; simp [Matrix.submatrix_apply,he])
    simp only [zero,contribution,dif_neg hb,Int.cast_zero,zero_mul]

theorem symmetric_root_formula {n : ℕ} (a : Fin (n+1) → ℕ) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (n+1)) :
    monomialSymmetric a (fun i => ζ^i.val) = ((∑ b ∈ arrangements a, contribution b : ℤ) : ℂ) := by
  classical
  let x : Fin (n+1) → ℂ := fun j => ζ^j.val
  let M := Matrix.vandermonde x
  have hM : M.det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr
    (fun i j hij => Fin.ext (hζ.pow_inj i.isLt j.isLt hij))
  have entry (b : Fin (n+1) → ℕ) (i j : Fin (n+1)) :
      M (shift b i) j = M i j * x j ^ b i := by
    change (ζ^((i.val+b i)%(n+1)))^j.val = (ζ^i.val)^j.val * (ζ^j.val)^b i
    have hp : ζ^((i.val+b i)%(n+1))=ζ^(i.val+b i) :=
      pow_eq_pow_of_modEq (Nat.mod_modEq _ _) hζ.pow_eq_one
    rw [hp,pow_add,mul_pow]
    congr 1
    rw [← pow_mul,← pow_mul,Nat.mul_comm]
  have hh : (∑ b ∈ arrangements a, (M.submatrix (shift b) id).det) =
      M.det * monomialSymmetric a x := by
    simp only [Matrix.det_apply',Matrix.submatrix_apply,id_eq,entry,Finset.prod_mul_distrib,
      ← mul_assoc]
    rw [Finset.sum_comm,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro σ _
    rw [← Finset.mul_sum,rearranged_sum]
  apply mul_left_cancel₀ hM
  rw [← hh]
  simp only [det_shift,Int.cast_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  exact mul_comm _ _

end
end OMA.S_mo_475626

namespace OMA.S_mo_475626

lemma shift_bijective_dvd_sum {n : ℕ} {b : Fin (n+1) → ℕ} (h : Function.Bijective (shift b)) :
    n+1 ∣ ∑ i, b i := by
  let f (j : Fin (n+1)) : ZMod (n+1) := j.val
  have hh := (Equiv.ofBijective (shift b) h).sum_comp f
  change ∑ j, f (shift b j) = ∑ j, f j at hh
  have hf (j : Fin (n+1)) : f (shift b j)=f j+(b j : ZMod (n+1)) := by
    simp [f,shift,ZMod.natCast_mod]
  simp only [hf,Finset.sum_add_distrib,add_eq_left] at hh
  exact (ZMod.natCast_eq_zero_iff _ _).mp (by simpa using hh)

lemma sum_contribution_eq_zero_of_not_dvd (n : ℕ) (a : Fin (n+1) → ℕ)
    (h : ¬n+1 ∣ ∑ i, a i) : (∑ b ∈ arrangements a, contribution b) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro b hb
  obtain ⟨σ,_,rfl⟩ := Finset.mem_image.mp hb
  have hs : ∑ i, (a ∘ σ) i = ∑ i, a i := Equiv.sum_comp σ a
  have hn : ¬Function.Bijective (shift (a ∘ σ)) := fun hh => h (hs ▸ shift_bijective_dvd_sum hh)
  unfold contribution
  rw [dif_neg hn]

end OMA.S_mo_475626

theorem OMA.solution : type_of% @OMA.S_mo_475626.main := by
  intro n a ζ _ _ hζ
  exact OMA.S_mo_475626.symmetric_root_formula a hζ
