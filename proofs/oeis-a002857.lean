import OMAStatements.S_oeis_a002857
import Mathlib

namespace OMA.P_oeis_a002857

open OMA.S_oeis_a002857
open scoped Classical

private def setToVec {n : ℕ} (s : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ s)

private def vecToSet {n : ℕ} (v : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => v i = true)

private lemma setToVec_vecToSet {n : ℕ} (v : Fin n → Bool) :
    setToVec (vecToSet v) = v := by
  ext i
  simp [setToVec, vecToSet]

private lemma vecToSet_setToVec {n : ℕ} (s : Finset (Fin n)) :
    vecToSet (setToVec s) = s := by
  ext i
  simp [setToVec, vecToSet]

private lemma setToVec_empty (n : ℕ) :
    setToVec (∅ : Finset (Fin n)) = fun _ => false := by
  ext i; simp [setToVec]

private lemma setToVec_univ (n : ℕ) :
    setToVec (Finset.univ : Finset (Fin n)) = fun _ => true := by
  ext i; simp [setToVec]

private def fnToHyp {n : ℕ} (f : (Fin n → Bool) → Bool) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun s => f (setToVec s) = true)

private def hypToFn {n : ℕ} (H : Finset (Finset (Fin n))) : (Fin n → Bool) → Bool :=
  fun v => decide (vecToSet v ∈ H)

private lemma hypToFn_fnToHyp {n : ℕ} (f : (Fin n → Bool) → Bool) :
    hypToFn (fnToHyp f) = f := by
  ext v
  simp [hypToFn, fnToHyp, setToVec_vecToSet]

private lemma fnToHyp_hypToFn {n : ℕ} (H : Finset (Finset (Fin n))) :
    fnToHyp (hypToFn H) = H := by
  ext s
  simp [fnToHyp, hypToFn, vecToSet_setToVec]

private lemma map_perm_symm_cancel {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Finset (Fin n)) :
    (s.map σ.symm.toEmbedding).map σ.toEmbedding = s := by
  ext i
  simp only [Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨j, ⟨k, hk, rfl⟩, rfl⟩
    simpa using hk
  · intro hi
    exact ⟨σ.symm i, ⟨i, hi, rfl⟩, σ.apply_symm_apply i⟩

private lemma setToVec_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Finset (Fin n)) :
    setToVec s ∘ σ = setToVec (s.map σ.symm.toEmbedding) := by
  ext i
  simp only [setToVec, Function.comp_apply, Finset.mem_map, Equiv.coe_toEmbedding]
  congr 1
  refine propext ⟨fun h => ⟨σ i, h, σ.symm_apply_apply i⟩, ?_⟩
  rintro ⟨j, hj, hji⟩
  have : j = σ i := by rw [← hji, σ.apply_symm_apply]
  rwa [← this]

private lemma fnToHyp_equivariant {n : ℕ} (σ : Equiv.Perm (Fin n))
    (f : (Fin n → Bool) → Bool) :
    fnToHyp (permActBoolFn σ f) = permActHypergraph σ (fnToHyp f) := by
  ext s
  simp only [fnToHyp, permActHypergraph]
  rw [Finset.mem_filter, Finset.mem_image]
  simp only [Finset.mem_univ, true_and, Finset.mem_filter, permActBoolFn]
  constructor
  · intro hf
    rw [setToVec_comp_perm] at hf
    exact ⟨s.map σ.symm.toEmbedding, hf, map_perm_symm_cancel σ s⟩
  · rintro ⟨t, ht, rfl⟩
    have hinv : (t.map σ.toEmbedding).map σ.symm.toEmbedding = t := by
      simpa using map_perm_symm_cancel σ.symm t
    rw [setToVec_comp_perm, hinv]
    exact ht

private lemma permActHypergraph_univ {n : ℕ} (σ : Equiv.Perm (Fin n))
    (H : Finset (Finset (Fin n))) :
    Finset.univ ∈ permActHypergraph σ H ↔ Finset.univ ∈ H := by
  simp only [permActHypergraph, Finset.mem_image]
  constructor
  · rintro ⟨s, hs, hmap⟩
    have hsu : s = Finset.univ := by
      ext i
      simp only [Finset.mem_univ, iff_true]
      have hmem : σ i ∈ s.map σ.toEmbedding := hmap.symm ▸ Finset.mem_univ (σ i)
      rcases Finset.mem_map.mp hmem with ⟨j, hj, hji⟩
      have : j = i := σ.injective hji
      rwa [← this]
    rwa [← hsu]
  · intro hu
    refine ⟨Finset.univ, hu, ?_⟩
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Equiv.coe_toEmbedding, iff_true]
    exact ⟨σ.symm i, σ.apply_symm_apply i⟩

private lemma hypergraphEquiv_univ_iff {n : ℕ} {H₁ H₂ : Finset (Finset (Fin n))}
    (h : hypergraphEquiv n H₁ H₂) :
    Finset.univ ∈ H₁ ↔ Finset.univ ∈ H₂ := by
  rcases h with ⟨σ, rfl⟩
  exact (permActHypergraph_univ σ H₁).symm

private lemma boolFnEquiv_iff_fnToHyp {n : ℕ} (f g : (Fin n → Bool) → Bool) :
    boolFnEquiv n f g ↔ hypergraphEquiv n (fnToHyp f) (fnToHyp g) := by
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨σ, (fnToHyp_equivariant σ f).symm⟩
  · rintro ⟨σ, h⟩
    refine ⟨σ, ?_⟩
    have h1 := congr_arg hypToFn ((fnToHyp_equivariant σ f).trans h)
    simpa [hypToFn_fnToHyp] using h1

private lemma isPostBoolFn_iff_fnToHyp {n : ℕ} (f : (Fin n → Bool) → Bool) :
    IsPostBoolFn n f ↔ ∅ ∉ fnToHyp f ∧ Finset.univ ∈ fnToHyp f := by
  simp only [IsPostBoolFn, fnToHyp, Finset.mem_filter, Finset.mem_univ, true_and,
    setToVec_empty, setToVec_univ, Bool.not_eq_true]

/-- An improper cover of `Fin n`: a cover containing `Finset.univ`
(equivalently `∅ ∉ H ∧ Finset.univ ∈ H`). -/
private def IsImproperCover (n : ℕ) (H : Finset (Finset (Fin n))) : Prop :=
  IsCover n H ∧ Finset.univ ∈ H

private lemma isImproperCover_iff (n : ℕ) (H : Finset (Finset (Fin n))) :
    IsImproperCover n H ↔ ∅ ∉ H ∧ Finset.univ ∈ H := by
  constructor
  · rintro ⟨⟨hem, _⟩, hu⟩; exact ⟨hem, hu⟩
  · rintro ⟨hem, hu⟩; exact ⟨⟨hem, fun i => ⟨Finset.univ, hu, Finset.mem_univ i⟩⟩, hu⟩

lemma solve_a002857 :
    ∀ n : ℕ, 1 ≤ n → a002857 n = a055621 n - a055152 n := by
  intro n _
  let QPost := Quot (fun x y : { f : (Fin n → Bool) → Bool // IsPostBoolFn n f } =>
    boolFnEquiv n x.val y.val)
  let QCov := Quot (fun x y : { H : Finset (Finset (Fin n)) // IsCover n H } =>
    hypergraphEquiv n x.val y.val)
  let QProp := Quot (fun x y : { H : Finset (Finset (Fin n)) // IsProperCover n H } =>
    hypergraphEquiv n x.val y.val)
  let QImprop := Quot (fun x y : { H : Finset (Finset (Fin n)) // IsImproperCover n H } =>
    hypergraphEquiv n x.val y.val)
  -- Equivalence 1: `QPost ≃ QImprop` via `fnToHyp` / `hypToFn`
  have e1 : QPost ≃ QImprop := by
    refine
      { toFun := Quot.lift
          (fun x => Quot.mk _ ⟨fnToHyp x.val, (isImproperCover_iff n _).mpr
            ((isPostBoolFn_iff_fnToHyp x.val).mp x.property)⟩)
          (fun x y hxy => Quot.sound ((boolFnEquiv_iff_fnToHyp x.val y.val).mp hxy))
        invFun := Quot.lift
          (fun x => Quot.mk _ ⟨hypToFn x.val, (isPostBoolFn_iff_fnToHyp _).mpr
            (by rw [fnToHyp_hypToFn]; exact (isImproperCover_iff n _).mp x.property)⟩)
          (fun x y hxy => Quot.sound ((boolFnEquiv_iff_fnToHyp _ _).mpr
            (by simpa [fnToHyp_hypToFn] using hxy)))
        left_inv := fun q => by
          induction q using Quot.ind with
          | _ x => exact congr_arg (Quot.mk _) (Subtype.ext (hypToFn_fnToHyp x.val))
        right_inv := fun q => by
          induction q using Quot.ind with
          | _ x => exact congr_arg (Quot.mk _) (Subtype.ext (fnToHyp_hypToFn x.val)) }
  -- Equivalence 2: `QCov ≃ QProp ⊕ QImprop`
  have e2 : QCov ≃ QProp ⊕ QImprop := by
    let toSum : { H : Finset (Finset (Fin n)) // IsCover n H } → QProp ⊕ QImprop := fun x =>
      if hu : Finset.univ ∈ x.val then
        Sum.inr (Quot.mk _ ⟨x.val, x.property, hu⟩)
      else
        Sum.inl (Quot.mk _ ⟨x.val, x.property, hu⟩)
    have htoSum : ∀ x y : { H : Finset (Finset (Fin n)) // IsCover n H },
        hypergraphEquiv n x.val y.val → toSum x = toSum y := by
      intro x y hxy
      have hiff := hypergraphEquiv_univ_iff hxy
      dsimp only [toSum]
      by_cases hx : Finset.univ ∈ x.val
      · have hy : Finset.univ ∈ y.val := hiff.mp hx
        rw [dif_pos hx, dif_pos hy]
        exact congr_arg Sum.inr (Quot.sound hxy)
      · have hy : Finset.univ ∉ y.val := fun h => hx (hiff.mpr h)
        rw [dif_neg hx, dif_neg hy]
        exact congr_arg Sum.inl (Quot.sound hxy)
    let fromSum : QProp ⊕ QImprop → QCov := Sum.elim
      (Quot.lift (fun x => Quot.mk _ ⟨x.val, x.property.1⟩) (fun _ _ h => Quot.sound h))
      (Quot.lift (fun x => Quot.mk _ ⟨x.val, x.property.1⟩) (fun _ _ h => Quot.sound h))
    refine
      { toFun := Quot.lift toSum htoSum
        invFun := fromSum
        left_inv := fun q => by
          induction q using Quot.ind with
          | _ x =>
            change fromSum (toSum x) = Quot.mk _ x
            dsimp only [toSum, fromSum]
            split_ifs <;> rfl
        right_inv := fun s => by
          rcases s with qp | qi
          · induction qp using Quot.ind with
            | _ x =>
              change toSum ⟨x.val, x.property.1⟩ = Sum.inl (Quot.mk _ x)
              dsimp only [toSum]
              rw [dif_neg x.property.2]
          · induction qi using Quot.ind with
            | _ x =>
              change toSum ⟨x.val, x.property.1⟩ = Sum.inr (Quot.mk _ x)
              dsimp only [toSum]
              rw [dif_pos x.property.2] }
  -- Both `QProp` and `QImprop` are finite (quotients of finite subtypes).
  have : Finite QProp := Finite.of_surjective _ Quot.mk_surjective
  have : Finite QImprop := Finite.of_surjective _ Quot.mk_surjective
  have hsum : Nat.card QCov = Nat.card QProp + Nat.card QImprop := by
    rw [Nat.card_congr e2, Nat.card_sum]
  have hpost : Nat.card QPost = Nat.card QImprop := Nat.card_congr e1
  change Nat.card QPost = Nat.card QCov - Nat.card QProp
  omega

end OMA.P_oeis_a002857

theorem OMA.solution : type_of% @OMA.S_oeis_a002857.main :=
  OMA.P_oeis_a002857.solve_a002857
