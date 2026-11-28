import OMAStatements.S_mo_162723

/-!
Faithful credited port of @connoranderson's complete proof linked from statement PR #25843
and desk DONE #118262. Pinned companion:
https://github.com/connoranderson/open-math-agents/blob/58289dd2db046a65e89cf02ebe7353f78d76c938/proofs/mo-162723.lean
All mathematical source is unchanged. This registers existing proof work.
Source: mohi, https://mathoverflow.net/questions/162723 (CC BY-SA 4.0).
Answer: Suvrit, https://mathoverflow.net/a/163566 (CC BY-SA 3.0).
The binary objective and clique reduction are due to Suvrit, who credits S. Jegelka.
The registered theorem certifies the exact clique equivalence, including PSD inputs;
it does not formalize a computational complexity class or an efficient algorithm.
-/

namespace OMA.S_mo_162723
open Finset Matrix
open scoped Matrix.Norms.Frobenius Classical ComplexOrder
private noncomputable def score {n : ℕ} (A : Mat n) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S, ‖A i j‖^2
private lemma norm_sq {n : ℕ} (A : Mat n) (S : Finset (Fin n)) :
    principalNorm A S ^ 2 = score A S := by
  rw [principalNorm,Matrix.frobenius_norm_def]
  simp only [Real.rpow_two,←Real.sqrt_eq_rpow,Matrix.submatrix_apply]
  rw [Real.sq_sqrt (by positivity)]
  simp only [score]
  calc
    _ = ∑ i ∈ S.attach, ∑ j ∈ S, ‖A i j‖^2 :=
      sum_congr rfl (fun i _ => Finset.sum_attach S (fun j => ‖A i j‖^2))
    _ = _ := Finset.sum_attach S (fun i => ∑ j ∈ S, ‖A i j‖^2)
private lemma mono_score {n : ℕ} (A : Mat n) {S T : Finset (Fin n)} (h : S⊆T) :
    score A S ≤ score A T := by
  unfold score
  apply le_trans (sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => sum_nonneg fun _ _ => sq_nonneg _))
  apply sum_le_sum
  intro i _
  exact sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => sq_nonneg _)

private lemma input_score {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℕ) (S : Finset (Fin n)) :
    score (input G d) S = (S.card:ℝ)*d^2 +
      ((S.offDiag.filter (fun p => G.Adj p.1 p.2)).card:ℝ) := by
  classical
  have hp (p : Fin n × Fin n) : ‖input G d p.1 p.2‖^2 =
      (if p.1=p.2 then (d:ℝ)^2 else 0) + (if G.Adj p.1 p.2 then 1 else 0) := by
    rcases p with ⟨i,j⟩
    by_cases h : i=j
    · subst j;simp [input]
    · by_cases ha : G.Adj i j <;> simp [input,h,ha]
  have hs : (S ×ˢ S).filter (fun p => G.Adj p.1 p.2) =
      S.offDiag.filter (fun p => G.Adj p.1 p.2) := by
    ext p
    simp only [mem_filter,mem_product,mem_offDiag]
    exact ⟨fun h => ⟨⟨h.1.1,h.1.2,h.2.ne⟩,h.2⟩,fun h => ⟨⟨h.1.1,h.1.2.1⟩,h.2⟩⟩
  change (∑ i ∈ S,∑ j ∈ S, ‖input G d i j‖^2)=_
  rw [← Finset.sum_product']
  simp only [hp,sum_add_distrib,sum_boole,hs]
  congr 1
  rw [Finset.sum_product]
  simp

private lemma exact_threshold {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℕ) (S : Finset (Fin n)) :
    threshold S.card d ≤ score (input G d) S ↔ G.IsClique (S : Set (Fin n)) := by
  classical
  have hc : S.offDiag.card = S.card*(S.card-1) := by
    rw [offDiag_card,Nat.mul_sub,Nat.mul_one]
  rw [input_score, threshold, ←hc, add_le_add_iff_left]
  rw [Nat.cast_le,show S.offDiag.card ≤ (S.offDiag.filter (fun p => G.Adj p.1 p.2)).card ↔
      (S.offDiag.filter (fun p => G.Adj p.1 p.2)).card=S.offDiag.card from
      ⟨fun h => h.antisymm' (card_filter_le ..),fun h => h.ge⟩,card_filter_eq_iff]
  constructor
  · intro h i hi j hj hij
    exact h (i,j) (mem_offDiag.mpr ⟨hi,hj,hij⟩)
  · intro h p hp
    exact h (mem_offDiag.mp hp).1 (mem_offDiag.mp hp).2.1 (mem_offDiag.mp hp).2.2

private lemma shifted_psd {n : ℕ} (G : SimpleGraph (Fin n)) : (input G n).PosSemidef := by
  classical
  let B := G.incMatrix ℂ
  let D (i : Fin n) : ℂ := ((n-G.degree i:ℕ):ℂ)
  have hb : B.conjTranspose=B.transpose := by
    ext i j
    simp [B,Matrix.conjTranspose_apply,SimpleGraph.incMatrix_apply']
  have hM : input G n=B*B.conjTranspose+Matrix.diagonal D := by
    rw [hb,G.incMatrix_mul_transpose]
    ext i j
    by_cases h : i=j
    · subst j
      have hd : G.degree i ≤ n := by simpa using (G.degree_lt_card_verts i).le
      simp [input, Matrix.add_apply,D,Nat.cast_sub hd]
    · simp [input,Matrix.add_apply,h]
  rw [hM]
  exact (posSemidef_self_mul_conjTranspose B).add (PosSemidef.diagonal (fun _ => by dsimp [D];positivity))

private lemma input_hermitian {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℕ) : (input G d).IsHermitian := by
  ext i j
  by_cases h : i=j
  · subst j;simp [input]
  · by_cases ha : G.Adj i j
    · simp [input,h,Ne.symm h,ha,ha.symm]
    · simp [input,h,Ne.symm h,ha,show ¬G.Adj j i from fun h => ha h.symm]

private lemma finite_opt {n : ℕ} (A : Mat n) (s : ℕ) (hs : s ≤ n) :
    ∃ S : Finset (Fin n), S.card=s ∧ ∀ J : Finset (Fin n), J.card ≤ s → principalNorm A J ≤ principalNorm A S := by
  have hS : (univ.powersetCard s : Finset (Finset (Fin n))).Nonempty :=
    powersetCard_nonempty.mpr (by simpa using hs)
  obtain ⟨S,hS,hmax⟩ := exists_max_image _ (principalNorm A) hS
  refine ⟨S,(mem_powersetCard.mp hS).2,?_⟩
  intro J hJ
  obtain ⟨W,hJW,hW⟩ := Finset.exists_superset_card_eq hJ (by simpa using hs)
  apply le_trans _ (hmax W (mem_powersetCard.mpr ⟨subset_univ _,hW⟩))
  have hh := mono_score A hJW
  rw [←norm_sq,←norm_sq] at hh
  exact le_of_sq_le_sq hh (norm_nonneg _)

end OMA.S_mo_162723

open OMA.S_mo_162723 Finset in
theorem OMA.solution : type_of% @OMA.S_mo_162723.main := by
  classical
  intro n
  constructor
  · intro A _
    refine ⟨?_,finite_opt A⟩
    intro b
    rw [norm_sq]
    simp only [score,binary,sum_filter]
    apply sum_congr rfl
    intro i _
    cases b i <;> simp [mul_ite]
  · intro G
    refine ⟨shifted_psd G,fun d => ⟨input_hermitian G d,?_⟩⟩
    intro s hs
    constructor
    · rintro ⟨J,hJ,hg⟩
      obtain ⟨S,hJS,hS⟩ := Finset.exists_superset_card_eq hJ (by simpa using hs)
      refine ⟨S,hS,(exact_threshold G d S).mp ?_⟩
      rw [hS]
      exact hg.trans (by rw [norm_sq];exact mono_score _ hJS)
    · rintro ⟨S,hS,hc⟩
      exact ⟨S,hS.le,by rw [norm_sq,← hS];exact (exact_threshold G d S).mpr hc⟩
