import OMAStatements.S_mo_504001

/-!
Ilya Bogdanov's construction (https://mathoverflow.net/a/504113) puts a
progression with a different step in every residue class. At the cutoff 2,
steps 2 and 2d suffice: all d² cross-differences in one direction are
distinct, whereas the even differences lie in two progressions.
-/

namespace OMA.S_mo_504001
open Finset
open scoped Pointwise

private noncomputable def indices (d : ℕ) : Finset ℤ := Ico 0 d
private def oddTerm (d : ℕ) (j : ℤ) : ℤ := 2*((d:ℤ)*j)+1
private noncomputable def exampleSet (d : ℕ) : Finset ℤ :=
  (indices d).image (fun i => 2*i) ∪ (indices d).image (oddTerm d)

private lemma size_indices (d : ℕ) : (indices d).card = d := by
  simp [indices, Int.card_Ico]

private lemma size_example (d : ℕ) : d ≤ (exampleSet d).card := by
  calc
    d = (indices d).card := (size_indices d).symm
    _ ≤ _ := ?_
  apply card_le_card_of_injOn (fun i : ℤ => 2*i)
  · intro i hi
    exact mem_union_left _ (mem_image_of_mem _ hi)
  · intro i hi j hj hij
    dsimp at hij
    omega

private lemma many_differences (d : ℕ) :
    d*d ≤ (exampleSet d - exampleSet d).card := by
  let T := indices d ×ˢ indices d
  have hcard : T.card = d*d := by simp [T,size_indices]
  rw [← hcard]
  apply card_le_card_of_injOn (fun z : ℤ × ℤ => 2*z.1 - oddTerm d z.2)
  · rintro ⟨i,j⟩ hij
    have hp := mem_product.mp hij
    exact sub_mem_sub (mem_union_left _ (mem_image_of_mem _ hp.1))
      (mem_union_right _ (mem_image_of_mem _ hp.2))
  · rintro ⟨i,j⟩ hij ⟨k,m⟩ hkm heq
    change 2*i - (2*((d:ℤ)*j)+1) = 2*k - (2*((d:ℤ)*m)+1) at heq
    have hr₁ := mem_product.mp hij
    have hr₂ := mem_product.mp hkm
    have hi := mem_Ico.mp hr₁.1
    have hk := mem_Ico.mp hr₂.1
    have hd : (0:ℤ) ≤ d := Int.natCast_nonneg _
    have hjm : j = m := by
      rcases lt_trichotomy j m with h | h | h
      · have ht : 0 ≤ m-j-1 := by omega
        nlinarith [mul_nonneg hd ht, hi.1, hi.2, hk.1, hk.2]
      · exact h
      · have ht : 0 ≤ j-m-1 := by omega
        nlinarith [mul_nonneg hd ht, hi.1, hi.2, hk.1, hk.2]
    subst m
    exact Prod.ext (by omega) rfl

private noncomputable def span (d : ℕ) : Finset ℤ := Icc (-(d:ℤ)) d
private noncomputable def evenCover (d : ℕ) : Finset ℤ :=
  (span d).image (fun i => 2*i) ∪ (span d).image (fun j => 2*((d:ℤ)*j))

private lemma size_cover (d : ℕ) : (evenCover d).card ≤ 4*d+2 := by
  have hs : (span d).card = 2*d+1 := by
    rw [span, Int.card_Icc]
    omega
  have H := card_union_le ((span d).image (fun i => 2*i)) ((span d).image (fun j => 2*((d:ℤ)*j)))
  exact H.trans ((Nat.add_le_add card_image_le card_image_le).trans (by omega))

private lemma even_mem_cover (d : ℕ) {z : ℤ}
    (hz : z ∈ exampleSet d - exampleSet d) (he : (2:ℤ) ∣ z) : z ∈ evenCover d := by
  obtain ⟨x,hx,y,hy,rfl⟩ := mem_sub.mp hz
  obtain ⟨q,hq⟩ := he
  rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
  all_goals
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hy
    have hi' := mem_Ico.mp hi
    have hj' := mem_Ico.mp hj
  · exact mem_union_left _ (mem_image.mpr ⟨i-j, mem_Icc.mpr (by constructor <;> omega), by ring⟩)
  · unfold oddTerm at hq
    omega
  · unfold oddTerm at hq
    omega
  · exact mem_union_right _ (mem_image.mpr ⟨i-j, mem_Icc.mpr (by constructor <;> omega),
      by unfold oddTerm; ring⟩)

end OMA.S_mo_504001
open OMA.S_mo_504001
open scoped Pointwise

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_504001.main) := by
  intro h
  obtain ⟨c,hc,N,hN⟩ := h 2
  obtain ⟨k,hk⟩ := exists_nat_gt (6/c)
  let d := N+k+1
  have hd : 0 < (d:ℝ) := by dsimp [d]; positivity
  have hNk : N ≤ d := by dsimp [d]; omega
  have hkd : (k:ℝ) ≤ d := by exact_mod_cast (show k ≤ d by dsimp [d]; omega)
  obtain ⟨A,hA,hdiv,hdens⟩ := hN (exampleSet d) (hNk.trans (size_example d))
  have hsub : A ⊆ evenCover d := by
    intro z hz
    exact even_mem_cover d (hA hz) (hdiv z hz 2 Nat.prime_two (by decide))
  have hcount := (Finset.card_le_card hsub).trans (size_cover d)
  have hupper : (A.card:ℝ) ≤ 4*d+2 := by exact_mod_cast hcount
  have hlower : (d:ℝ)*d ≤ (exampleSet d - exampleSet d).card := by exact_mod_cast many_differences d
  have hsmall := (mul_le_mul_of_nonneg_left hlower hc.le).trans (hdens.trans hupper)
  have hsix : 6 < c * d := by
    have h' := (div_lt_iff₀ hc).mp hk
    nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hkd)]
  have hone : (1:ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by dsimp [d]; omega)
  nlinarith [mul_pos (sub_pos.mpr hsix) hd]
