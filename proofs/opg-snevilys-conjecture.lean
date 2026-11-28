import OMAStatements.S_opg_snevilys_conjecture
import Mathlib
open scoped BigOperators

namespace Snevily

private noncomputable def sumProfile {ι G : Type} [Fintype ι] (f : ι → G) : G →₀ ℕ :=
  ∑ i, Finsupp.single (f i) 1

private theorem sumProfile_apply {ι G : Type} [Fintype ι] [DecidableEq G] (f : ι → G) (g : G) :
    (sumProfile f) g = (Finset.univ.filter (fun i => f i = g)).card := by
  rw [sumProfile, Finsupp.finsetSum_apply, Finset.card_filter]
  simp only [Finsupp.single_apply]

private theorem unique_profile {G : Type} [AddCommGroup G]
    {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β)
    (a : α → G) (b : β → G) (ha : Function.Injective a) (hb : Function.Injective b) :
    ∃ π : α ≃ β, ∀ σ : α ≃ β,
      sumProfile (fun i => a i + b (σ i)) = sumProfile (fun i => a i + b (π i)) → σ = π := by
  classical
  suffices h : ∀ n (α β : Type) [Fintype α] [Fintype β], Fintype.card α = n →
      ∀ (e : α ≃ β) (a : α → G) (b : β → G),
        Function.Injective a → Function.Injective b →
        ∃ π : α ≃ β, ∀ σ : α ≃ β,
          sumProfile (fun i => a i + b (σ i)) = sumProfile (fun i => a i + b (π i)) → σ = π by
    exact h _ α β rfl e a b ha hb
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro α β _ _ hn e a b ha hb
    by_cases hα : Nonempty α
    · obtain ⟨i₀⟩ := hα
      let g := a i₀ + b (e i₀)
      let p (i : α) : Prop := ∃ j, a i + b j = g
      let q (j : β) : Prop := ∃ i, a i + b j = g
      let f (i : {i // p i}) : {j // q j} :=
        ⟨i.2.choose, ⟨i, i.2.choose_spec⟩⟩
      have hf (i : {i // p i}) : a i + b (f i) = g := i.2.choose_spec
      let m : {i // p i} ≃ {j // q j} := Equiv.ofBijective f (by
        refine ⟨?_, ?_⟩
        · intro i j hij
          apply Subtype.ext
          apply ha
          have hval : (f i : β) = f j := congrArg Subtype.val hij
          apply add_right_cancel (b := b (f j))
          rw [← hval, hf i, hval, hf j]
        · intro j
          obtain ⟨i, hi⟩ := j.2
          let k : {i // p i} := ⟨i, ⟨j, hi⟩⟩
          refine ⟨k, Subtype.ext (hb (add_left_cancel (a := a i) ?_))⟩
          exact (hf k).trans hi.symm)
      have hm (i : {i // p i}) : a i + b (m i) = g := hf i
      have hp : 0 < Fintype.card {i // p i} :=
        Fintype.card_pos_iff.mpr ⟨⟨i₀, e i₀, rfl⟩⟩
      have hlt : Fintype.card {i // ¬p i} < n := by
        rw [Fintype.card_subtype_compl, hn]
        have hnpos : 0 < n := hn ▸ Fintype.card_pos_iff.mpr ⟨i₀⟩
        omega
      have hcard : Fintype.card {i // ¬p i} = Fintype.card {j // ¬q j} := by
        rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl,
          Fintype.card_congr e, Fintype.card_congr m]
      let ar (i : {i // ¬p i}) := a i
      let br (j : {j // ¬q j}) := b j
      obtain ⟨r, hr⟩ := ih _ hlt _ _ rfl (Fintype.equivOfCardEq hcard) ar br
        (ha.comp Subtype.val_injective) (hb.comp Subtype.val_injective)
      let π := (Equiv.sumCompl p).symm.trans ((m.sumCongr r).trans (Equiv.sumCompl q))
      have hπ₁ (i : {i // p i}) : π i = m i := by
        simp [π, Equiv.sumCompl_symm_apply_pos]
      have hπ₂ (i : {i // ¬p i}) : π i = r i := by
        simp [π, Equiv.sumCompl_symm_apply_neg]
      have hπg (i : α) : a i + b (π i) = g ↔ p i :=
        ⟨fun hi => ⟨π i, hi⟩, fun hi => (congrArg (fun j => a i + b j)
          (hπ₁ ⟨i, hi⟩)).trans (hm ⟨i, hi⟩)⟩
      refine ⟨π, fun σ hσ => ?_⟩
      have hfilters : (Finset.univ.filter fun i => a i + b (σ i) = g) =
          Finset.univ.filter p := by
        apply Finset.eq_of_subset_of_card_le
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          exact ⟨σ i, hi⟩
        · have hh := congrArg (fun d : G →₀ ℕ => d g) hσ
          rw [sumProfile_apply, sumProfile_apply] at hh
          rw [hh]
          simp only [hπg, le_refl]
      have hσ₁ (i : {i // p i}) : σ i = m i := by
        apply hb
        apply add_left_cancel (a := a i)
        refine Eq.trans ?_ (hm i).symm
        have hmem : (i : α) ∈ Finset.univ.filter p := by simp [i.2]
        simpa only [← hfilters, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
      have hσq (i : α) : p i ↔ q (σ i) := by
        refine ⟨fun hi => hσ₁ ⟨i, hi⟩ ▸ (m ⟨i, hi⟩).2, fun hj => ?_⟩
        let j : {j // q j} := ⟨σ i, hj⟩
        let k := m.symm j
        have heq : σ k = σ i :=
          (hσ₁ k).trans (congrArg Subtype.val (m.apply_symm_apply j))
        exact σ.injective heq ▸ k.2
      let s : {i // ¬p i} ≃ {j // ¬q j} := σ.subtypeEquiv (fun i => not_congr (hσq i))
      have hs : s = r := by
        apply hr
        have split := Fintype.sum_subtype_add_sum_subtype p
          (fun i => Finsupp.single (a i + b (σ i)) (1 : ℕ))
        have split' := Fintype.sum_subtype_add_sum_subtype p
          (fun i => Finsupp.single (a i + b (π i)) (1 : ℕ))
        unfold sumProfile
        change (∑ i : {i // ¬p i}, Finsupp.single (a i + b (σ i)) 1) =
          ∑ i : {i // ¬p i}, Finsupp.single (a i + b (r i)) 1
        simp_rw [hπ₁, hπ₂, ← hσ₁] at split'
        exact add_left_cancel (split.trans (hσ.trans split'.symm))
      ext i
      by_cases hi : p i
      · exact (hσ₁ ⟨i, hi⟩).trans (hπ₁ ⟨i, hi⟩).symm
      · exact (congrArg (fun t : {i // ¬p i} ≃ {j // ¬q j} => (t ⟨i, hi⟩ : β)) hs).trans
          (hπ₂ ⟨i, hi⟩).symm
    · exact ⟨e, fun σ _ => Equiv.ext fun i => (hα ⟨i⟩).elim⟩

private theorem character_expansion {G F R : Type*}
    [AddCommGroup G] [Fintype G] [Field F] [CharP F 2] [IsAlgClosed F]
    [CommRing R] [Algebra F R] (hG : Odd (Fintype.card G)) (φ : G → R) :
    ∃ (χ : Fin (Fintype.card G) → AddChar G R) (w : Fin (Fintype.card G) → R),
      ∀ g, φ g = ∑ i, w i * χ i g := by
  classical
  let H := Multiplicative G
  let D := H →* Fˣ
  have he : Monoid.exponent H ∣ Fintype.card G := by
    simpa only [H, Fintype.card_multiplicative] using (Group.exponent_dvd_card (G := H))
  have : NeZero ((Monoid.exponent H : ℕ) : F) :=
    ⟨fun h => hG.not_two_dvd_nat
      ((CharP.cast_eq_zero_iff F 2 _).mp h |>.trans he)⟩
  let e : D ≃ H :=
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity H F).some.toEquiv
  let : Fintype D := Fintype.ofEquiv H e.symm
  have hD : Fintype.card D = Fintype.card G := Fintype.card_congr e
  let c (ξ : D) (g : G) : F := (ξ (Multiplicative.ofAdd g) : Fˣ)
  have hc (ξ : D) (a b : G) : c ξ (a + b) = c ξ a * c ξ b :=
    congrArg (fun v : Fˣ => (v : F)) (map_mul ξ (Multiplicative.ofAdd a) (Multiplicative.ofAdd b))
  have horth (g : G) : ∑ ξ : D, c ξ g = if g = 0 then 1 else 0 := by
    split_ifs with hg
    · subst g
      have hcard : (Fintype.card G : F) = 1 :=
        natCast_eq_one_of_odd_of_two_eq_zero hG CharTwo.two_eq_zero
      simpa [c, hD] using hcard
    · obtain ⟨η, hη⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity H F
        (a := Multiplicative.ofAdd g) hg
      apply eq_zero_of_mul_eq_self_left (mt Units.val_eq_one.mp hη)
      rw [Finset.mul_sum]
      exact Fintype.sum_equiv (Equiv.mulLeft η) _ _ fun ξ => by
        change c η g * c ξ g = c (η * ξ) g
        rfl
  let t : Fin (Fintype.card G) ≃ D :=
    (Fintype.equivFinOfCardEq hD).symm
  let d (ξ : D) (g : G) : R := algebraMap F R (c ξ g)
  let w (ξ : D) : R := ∑ h, φ h * d ξ (-h)
  let χ (ξ : D) : AddChar G R :=
    ⟨d ξ, by simp [d, c], fun a b => by simp only [d, hc, map_mul]⟩
  refine ⟨χ ∘ t, w ∘ t, fun g => ?_⟩
  change φ g = ∑ i, w (t i) * d (t i) g
  rw [Equiv.sum_comp t (fun ξ => w ξ * d ξ g)]
  symm
  calc
    (∑ ξ, w ξ * d ξ g) = ∑ h, φ h * (∑ ξ, d ξ (-h + g)) := by
      simp only [w, Finset.sum_mul, Finset.mul_sum, mul_assoc, d, hc, map_mul]
      exact Finset.sum_comm
    _ = φ g := by
      have hd (h : G) : ∑ ξ, d ξ (-h + g) = if h = g then 1 else 0 := by
        rw [show (∑ ξ, d ξ (-h + g)) = algebraMap F R (∑ ξ, c ξ (-h + g)) by
          simp only [d, map_sum], horth]
        by_cases hh : h = g
        · simp [hh]
        · have hne : -h + g ≠ 0 := fun h₀ => hh (neg_add_eq_zero.mp h₀)
          simp [hh, hne]
      simp [hd]

private theorem det_eq_perm_sum {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] [CharP R 2] (M : Matrix ι ι R) :
    M.det = ∑ σ : Equiv.Perm ι, ∏ i, M (σ i) i := by
  rw [Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
    simp [h, CharTwo.neg_eq]

private theorem sum_image_fiber {ι κ R : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [AddCommMonoid R] (P : (ι → κ) → R) (s : Finset κ)
    (v : ι → κ) (hv : Function.Injective v) (hs : Finset.univ.image v = s) :
    (∑ u ∈ (Finset.univ.filter Function.Injective).filter (fun u => Finset.univ.image u = s),
        P u) = ∑ τ : Equiv.Perm ι, P (v ∘ τ) := by
  classical
  symm
  refine Finset.sum_nbij (fun τ : Equiv.Perm ι => v ∘ τ) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro τ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hv.comp τ.injective, by rw [Finset.image_comp,
      Finset.image_univ_of_surjective τ.surjective, hs]⟩
  · intro τ _ ρ _ he
    exact Equiv.ext fun i => hv (congrFun he i)
  · intro u hu
    change u ∈ (Finset.univ.filter Function.Injective).filter
      (fun u : ι → κ => Finset.univ.image u = s) at hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    have h (i : ι) : ∃ j, v j = u i := by
      have hi : u i ∈ Finset.univ.image v := by
        rw [hs, ← hu.2]
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
      exact ⟨j, hj⟩
    have hi : Function.Injective (fun i => (h i).choose) := by
      intro i j hij
      exact hu.1 ((h i).choose_spec.symm.trans ((congrArg v hij).trans (h j).choose_spec))
    let τ := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hi)
    exact ⟨τ, Finset.mem_univ _, funext fun i => (h i).choose_spec⟩

private theorem det_zero_of_collisions {ι κ G R : Type*} [Fintype ι] [Fintype κ]
    [AddCommGroup G] [CommRing R] [CharP R 2] [DecidableEq ι]
    (a b : ι → G) (φ : G → R) (χ : κ → AddChar G R) (w : κ → R)
    (hφ : ∀ g, φ g = ∑ j, w j * χ j g)
    (h : ∀ σ : Equiv.Perm ι, ¬ Function.Injective (fun i => a i + b (σ i))) :
    (Matrix.of fun i j => φ (a j + b i)).det = 0 := by
  classical
  let P (u : ι → κ) (σ : Equiv.Perm ι) := ∏ i, w (u i) * χ (u i) (a i + b (σ i))
  let S := Finset.univ.filter (Function.Injective : (ι → κ) → Prop)
  have hrepeat (u : ι → κ) (hu : ¬ Function.Injective u) : ∑ σ, P u σ = 0 := by
    obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hu
    let M : Matrix ι ι R := Matrix.of fun k l => χ (u l) (b k)
    have hM : M.det = 0 :=
      Matrix.det_zero_of_column_eq hne (fun k => by simp [M, hij])
    let d (l : ι) := w (u l) * χ (u l) (a l)
    calc
      (∑ σ, P u σ) = (Matrix.of fun k l => d l * M k l).det := by
        simp only [det_eq_perm_sum, Matrix.of_apply, P, d, M,
          AddChar.map_add_eq_mul, mul_assoc]
      _ = 0 := by rw [Matrix.det_mul_row, hM, mul_zero]
  calc
    (Matrix.of fun i j => φ (a j + b i)).det = ∑ u, ∑ σ, P u σ := by
      simp only [det_eq_perm_sum, Matrix.of_apply, hφ, Fintype.prod_sum, P]
      exact Finset.sum_comm
    _ = ∑ u ∈ S, ∑ σ, P u σ := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun u _ hu => ?_
      exact hrepeat u (by simpa [S] using hu)
    _ = ∑ s : Finset κ, ∑ u ∈ S.filter (fun u => Finset.univ.image u = s), ∑ σ, P u σ :=
      (Finset.sum_fiberwise S (fun u => Finset.univ.image u) (fun u => ∑ σ, P u σ)).symm
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro s _
      let T := S.filter (fun u => Finset.univ.image u = s)
      change (∑ u ∈ T, ∑ σ, P u σ) = 0
      rcases T.eq_empty_or_nonempty with ht | ⟨v, hv⟩
      · simp [ht]
      · have hv' : Function.Injective v ∧ Finset.univ.image v = s := by
          simpa [T, S] using hv
        rw [Finset.sum_comm]
        apply Finset.sum_eq_zero
        intro σ _
        obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp (h σ)
        rw [show T = (Finset.univ.filter Function.Injective).filter
          (fun u : ι → κ => Finset.univ.image u = s) by rfl]
        rw [sum_image_fiber (fun u => P u σ) s v hv'.1 hv'.2]
        let N : Matrix ι ι R := Matrix.of fun k l => w (v k) * χ (v k) (a l + b (σ l))
        have hN : N.det = 0 :=
          Matrix.det_zero_of_column_eq hne (fun k => by simp [N, hij])
        simpa only [det_eq_perm_sum, Matrix.of_apply, N, P, Function.comp_apply] using hN

private theorem sum_matrix_det_ne_zero {ι G F : Type}
    [Fintype ι] [DecidableEq ι] [AddCommGroup G] [CommRing F] [CharP F 2] [Nontrivial F]
    (a b : ι → G) (ha : Function.Injective a) (hb : Function.Injective b) :
    (Matrix.of fun i j => (MvPolynomial.X (a j + b i) : MvPolynomial G F)).det ≠ 0 := by
  classical
  obtain ⟨π, hπ⟩ := unique_profile (Equiv.refl ι) a b ha hb
  let p (σ : Equiv.Perm ι) := sumProfile (fun i => a i + b (σ i))
  have hprod (σ : Equiv.Perm ι) :
      (∏ i, MvPolynomial.X (a i + b (σ i)) : MvPolynomial G F) =
        MvPolynomial.monomial (p σ) 1 :=
    (MvPolynomial.monomial_sum_one Finset.univ _).symm
  intro hz
  have hc := congrArg (MvPolynomial.coeff (R := F) (p π)) hz
  simp only [det_eq_perm_sum, Matrix.of_apply, hprod, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial, MvPolynomial.coeff_zero] at hc
  rw [Finset.sum_eq_single π] at hc
  · simp at hc
  · intro σ _ hσ
    exact if_neg (fun hp => hσ (hπ σ hp))
  · simp

end Snevily

open Snevily in
theorem snevily_conjecture :
    ∀ (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G],
      Odd (Fintype.card G) →
      ∀ (A B : Finset G), A.card = B.card →
        ∃ f : A ≃ B, Function.Injective (fun a : A => (a : G) + (f a : G)) := by
  classical
  intro G _ _ _ hG A B hAB
  let e : A ≃ B := Finset.equivOfCardEq hAB
  let a (i : A) : G := i
  let b (i : A) : G := (e i : G)
  let F := AlgebraicClosure (ZMod 2)
  let φ (g : G) : MvPolynomial G F := MvPolynomial.X g
  have hperm : ∃ σ : Equiv.Perm A, Function.Injective (fun i => a i + b (σ i)) := by
    by_contra! h
    obtain ⟨χ, w, hφ⟩ := character_expansion (F := F) hG φ
    exact sum_matrix_det_ne_zero (F := F) a b Subtype.val_injective
      (Subtype.val_injective.comp e.injective) (det_zero_of_collisions a b φ χ w hφ h)
  obtain ⟨σ, hσ⟩ := hperm
  exact ⟨σ.trans e, hσ⟩

theorem OMA.solution : type_of% @OMA.S_opg_snevilys_conjecture.main := by
  classical
  intro G _ _ hOdd A B hCard
  exact snevily_conjecture G hOdd A B hCard
