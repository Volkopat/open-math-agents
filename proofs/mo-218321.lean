import OMAStatements.S_mo_218321

/-!
The scalar step uses Newton's identities and Vieta's formula. After projected
multiplicities are known, the projections of an unmatched point could agree
with the other configuration only in a union of N proper hyperplanes. Removing
matched points accounts for repetitions. Moment-curve directions satisfy the
hyperplane bound by univariate root counting.

For related results on reconstruction from projections see Tanguy, Flamary
and Delon, "Reconstructing discrete measures from projections" (2023).
-/
namespace OMA.S_mo_218321

open Finset MvPolynomial

private lemma scalar_reconstruct {N : ℕ} (x y : Fin N → ℝ)
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ N → (∑ i, (x i)^k) = ∑ i, (y i)^k) :
    (univ : Finset (Fin N)).val.map x=univ.val.map y := by
  classical
  let E := fun (z : Fin N → ℝ) (k : ℕ) => (univ.val.map z).esymm k
  let P := fun (z : Fin N → ℝ) (k : ℕ) => ∑ i, (z i)^k
  have recurrence (z : Fin N → ℝ) (k : ℕ) :
      k*E z k = (-1:ℝ)^(k+1) * (∑ a ∈ (Finset.HasAntidiagonal.antidiagonal k).filter (fun a => a.1 < k),
        (-1:ℝ)^a.1 * E z a.1 * P z a.2) := by
    have hr := congrArg (MvPolynomial.aeval z : MvPolynomial (Fin N) ℝ →ₐ[ℝ] ℝ)
      (MvPolynomial.mul_esymm_eq_sum (Fin N) ℝ k)
    simpa only [map_mul,map_natCast,map_pow,map_neg,map_one,map_sum,
      aeval_esymm_eq_multiset_esymm,psum,aeval_X,E,P] using hr
  have he (k : ℕ) (hk : k ≤ N) : E x k=E y k := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      by_cases hz : k=0
      · simp [hz,E,Multiset.esymm]
      apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr hz : (k:ℝ) ≠ 0)
      rw [recurrence x,recurrence y]
      apply congrArg (_*·)
      apply sum_congr rfl
      intro a ha
      obtain ⟨hb,hc⟩ := mem_filter.mp ha
      have hadd := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      rw [ih a.1 hc (by omega),show P x a.2 = P y a.2 from h _ (by omega) (by omega)]
  let sx := (univ : Finset (Fin N)).val.map x
  let sy := (univ : Finset (Fin N)).val.map y
  have cx : sx.card=N := by simp [sx]
  have cy : sy.card=N := by simp [sy]
  have hp : (sx.map fun t => Polynomial.X-Polynomial.C t).prod =
      (sy.map fun t => Polynomial.X-Polynomial.C t).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm,Multiset.prod_X_sub_X_eq_sum_esymm,cx,cy]
    apply sum_congr rfl
    intro j hj
    have hej : sx.esymm j = sy.esymm j := he j (by simpa using hj)
    rw [hej]
  simpa only [Polynomial.roots_multiset_prod_X_sub_C] using congrArg Polynomial.roots hp

end OMA.S_mo_218321
namespace OMA.S_mo_218321

open Finset

private lemma recover {n M : ℕ} (v : Fin M → Point n) (hv : generalPosition v)
    (s t : Multiset (Point n)) (hc : s.card=t.card) (hM : t.card*(n-1) < M)
    (he : ∀ j, s.map (project (v j))=t.map (project (v j))) : s=t := by
  classical
  induction s using Multiset.induction generalizing t with
  | empty =>
    apply (Multiset.card_eq_zero.mp ?_).symm
    simpa using hc.symm
  | cons a s ih =>
    have ha : a ∈ t := by
      by_contra H
      let bad := fun b : Point n => univ.filter (fun j => project (v j) (a-b)=0)
      have hbad (b) (hb : b ∈ t.toFinset) : (bad b).card ≤ n-1 :=
        hv _ (sub_ne_zero.mpr (fun h => H (h ▸ Multiset.mem_toFinset.mp hb)))
      have cover : univ ⊆ t.toFinset.biUnion bad := by
        intro j _
        have hmem : project (v j) a ∈ t.map (project (v j)) := by
          rw [← he j]
          simp
        obtain ⟨b,hb,hh⟩ := Multiset.mem_map.mp hmem
        refine mem_biUnion.mpr ⟨b,Multiset.mem_toFinset.mpr hb,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
        simpa [project,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib] using sub_eq_zero.mpr hh.symm
      have hcount : M ≤ t.card*(n-1) := calc
        M = (univ : Finset (Fin M)).card := by simp
        _ ≤ _ := card_le_card cover
        _ ≤ ∑ b ∈ t.toFinset, (bad b).card := card_biUnion_le
        _ ≤ ∑ _ ∈ t.toFinset, (n-1) := sum_le_sum hbad
        _ ≤ t.card*(n-1) := by
          simpa [Nat.mul_comm] using Nat.mul_le_mul_right (n-1) t.toFinset_card_le
      exact hM.not_ge hcount
    obtain ⟨u,rfl⟩ := Multiset.exists_cons_of_mem ha
    congr 1
    apply ih u
    · simpa using hc
    · exact (Nat.mul_le_mul_right _ (by simp : u.card ≤ (a ::ₘ u).card)).trans_lt hM
    · intro j
      simpa using he j

private lemma curve_general {n M : ℕ} (t : Fin M → ℝ) (ht : Function.Injective t) :
    generalPosition (fun j (k : Fin n) => (t j)^k.val) := by
  classical
  intro z hz
  let p := Polynomial.ofFn n z
  have hp : p ≠ 0 := by
    intro h
    apply hz
    exact Polynomial.injective_ofFn n (h.trans (Polynomial.ofFn_zero n).symm)
  have hn := Polynomial.ne_zero_of_ofFn_ne_zero hp
  have hd := Polynomial.ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr hn) z
  let S := univ.filter (fun j => project (fun k : Fin n => (t j)^k.val) z=0)
  have hroots : (S.image t).val ⊆ p.roots := by
    intro a ha
    change a ∈ S.image t at ha
    obtain ⟨j,hj,rfl⟩ := mem_image.mp ha
    apply (Polynomial.mem_roots hp).mpr
    have h := (mem_filter.mp hj).2
    simpa [p,Polynomial.ofFn_eq_sum_monomial,Polynomial.eval_finsetSum,Polynomial.eval_monomial,
      project,mul_comm] using h
  have hcard := Polynomial.card_le_degree_of_subset_roots hroots
  rw [card_image_of_injective _ ht] at hcard
  change p.natDegree < n at hd
  change S.card ≤ n-1
  omega

end OMA.S_mo_218321
open OMA.S_mo_218321 Finset in
theorem OMA.solution : type_of% @OMA.S_mo_218321.main := by
  classical
  constructor
  · intro n N M v hM hv x y h
    let s := (univ : Finset (Fin N)).val.map x
    let t := (univ : Finset (Fin N)).val.map y
    have he (j : Fin M) : s.map (project (v j)) = t.map (project (v j)) := by
      simpa [s,t,Multiset.map_map,Function.comp_def] using
        scalar_reconstruct (fun i => project (v j) (x i)) (fun i => project (v j) (y i)) (h j)
    have eqs := recover v hv s t (by simp [s,t]) (by simpa [t] using hM) he
    refine ⟨eqs,fun α => ?_⟩
    have eq := congrArg (fun U : Multiset (Point n) => (U.map (fun z => ∏ i, (z i)^(α i))).sum) eqs
    simpa only [s,t,Multiset.map_map,Function.comp_apply,Finset.sum] using eq
  · intro n M t ht
    exact curve_general t ht
