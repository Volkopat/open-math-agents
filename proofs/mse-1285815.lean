import OMAStatements.S_mse_1285815

namespace OMA.Mse1285815

open Filter Topology MeasureTheory

/-!
## 1. Symmetry of iterated Frechet derivatives and directional derivatives
-/

lemma iteratedFDeriv_apply_eval_clm {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) {f : E → F} {x : E} (k : ℕ) (hf : ContDiffAt ℝ ⊤ f x) :
    ∀ v : Fin k → E,
      iteratedFDeriv ℝ k (fun y => L (f y)) x v = L (iteratedFDeriv ℝ k f x v) := by
  have hcomp : iteratedFDeriv ℝ k (L ∘ f) x = L.compContinuousMultilinearMap (iteratedFDeriv ℝ k f x) :=
    L.iteratedFDeriv_comp_left hf le_top
  intro v
  exact congrFun (congrArg DFunLike.coe hcomp) v

lemma iteratedFDeriv_swap_zero_one {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} (m : ℕ) (hf : ContDiffAt ℝ ⊤ f x) (v : Fin (m + 2) → E) :
    iteratedFDeriv ℝ (m + 2) f x (v ∘ Equiv.swap 0 1) = iteratedFDeriv ℝ (m + 2) f x v := by
  have hsymm : IsSymmSndFDerivAt ℝ (iteratedFDeriv ℝ m f) x := by
    have hcm : ContDiffAt ℝ ⊤ (iteratedFDeriv ℝ m f) x := hf.iteratedFDeriv_right (by simp)
    exact hcm.isSymmSndFDerivAt (by simp)
  have heq : ∀ w : Fin (m + 2) → E,
      iteratedFDeriv ℝ (m + 2) f x w =
        fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ m f)) x (w 0) (w 1) (Fin.tail (Fin.tail w)) := by
    intro w
    rw [iteratedFDeriv_succ_apply_left]
    rw [iteratedFDeriv_succ_eq_comp_left (n := m) (f := f)]
    let e : (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin m => E) F) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => E) F :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) F).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hcm_m : ContDiffAt ℝ ⊤ (iteratedFDeriv ℝ m f) x := hf.iteratedFDeriv_right (by simp)
    have hcm_fd : ContDiffAt ℝ ⊤ (fderiv ℝ (iteratedFDeriv ℝ m f)) x := hcm_m.fderiv_right (by simp)
    have h1 := iteratedFDeriv_apply_eval_clm e 1 hcm_fd (fun _ => w 0)
    simp only [iteratedFDeriv_one_apply] at h1
    change fderiv ℝ (fun y => e (fderiv ℝ (iteratedFDeriv ℝ m f) y)) x (w 0) (Fin.tail w) = _
    rw [h1]
    rfl
  rw [heq (v ∘ Equiv.swap 0 1), heq v]
  have h0 : (v ∘ Equiv.swap (0 : Fin (m + 2)) 1) 0 = v 1 := by simp
  have h1 : (v ∘ Equiv.swap (0 : Fin (m + 2)) 1) 1 = v 0 := by simp
  have htail : Fin.tail (Fin.tail (v ∘ Equiv.swap (0 : Fin (m + 2)) 1)) = Fin.tail (Fin.tail v) := by
    funext i
    simp only [Fin.tail, Function.comp_apply]
    have hne0 : i.succ.succ ≠ (0 : Fin (m + 2)) := Fin.succ_ne_zero _
    have hne1 : i.succ.succ ≠ (1 : Fin (m + 2)) := by
      intro h
      have := congrArg Fin.val h
      simp at this
    rw [Equiv.swap_apply_of_ne_of_ne hne0 hne1]
  rw [h0, h1, htail, hsymm (v 1) (v 0)]

lemma iteratedFDeriv_swap_adj {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ∀ (k : ℕ) {f : E → F} {x : E}, ContDiffAt ℝ ⊤ f x →
      ∀ (i : ℕ) (hi : i + 1 < k) (v : Fin k → E),
        iteratedFDeriv ℝ k f x (v ∘ Equiv.swap ⟨i, by omega⟩ ⟨i + 1, hi⟩) =
          iteratedFDeriv ℝ k f x v := by
  intro k
  induction k with
  | zero => intro _ _ _ i hi; omega
  | succ k ih =>
    intro f x hf i hi v
    cases k with
    | zero => omega
    | succ m =>
      cases i with
      | zero =>
        exact iteratedFDeriv_swap_zero_one m hf v
      | succ j =>
        have hcm : ContDiffAt ℝ ⊤ (fderiv ℝ f) x := hf.fderiv_right (by simp)
        -- Use iteratedFDeriv_succ_apply_left and symmetry of iteratedFDeriv (m+1) on a nhd of x
        have hnhd : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ⊤ f y := hf.eventually (by simp)
        let τ : Equiv.Perm (Fin (m + 1)) := Equiv.swap ⟨j, by omega⟩ ⟨j + 1, by omega⟩
        have hcomp_eq : (fun y => iteratedFDeriv ℝ (m + 1) f y (Fin.tail v ∘ τ)) =ᶠ[𝓝 x]
            (fun y => iteratedFDeriv ℝ (m + 1) f y (Fin.tail v)) := by
          filter_upwards [hnhd] with y hy
          exact ih hy j (by omega) (Fin.tail v)
        have hfd := hcomp_eq.fderiv_eq (𝕜 := ℝ)
        have happly : ∀ (w : Fin (m + 1) → E),
            fderiv ℝ (fun y => iteratedFDeriv ℝ (m + 1) f y w) x (v 0) =
              fderiv ℝ (iteratedFDeriv ℝ (m + 1) f) x (v 0) w := by
          intro w
          let ev : ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => E) F →L[ℝ] F :=
            ContinuousMultilinearMap.apply ℝ (fun _ : Fin (m + 1) => E) F w
          have hcm_m1 : ContDiffAt ℝ ⊤ (iteratedFDeriv ℝ (m + 1) f) x := hf.iteratedFDeriv_right (by simp)
          have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ (m + 1) f) x := hcm_m1.differentiableAt (by simp)
          have := (ev.hasFDerivAt.comp x hdiff.hasFDerivAt).fderiv
          exact congrFun (congrArg DFunLike.coe this) (v 0)
        rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left]
        have h0 : (v ∘ Equiv.swap ⟨j + 1, by omega⟩ ⟨j + 2, hi⟩) 0 = v 0 := by
          simp only [Function.comp_apply]
          rw [Equiv.swap_apply_of_ne_of_ne]
          · intro h; have := congrArg Fin.val h; simp at this
          · intro h; have := congrArg Fin.val h; simp at this
        have htail : Fin.tail (v ∘ Equiv.swap ⟨j + 1, by omega⟩ ⟨j + 2, hi⟩) = Fin.tail v ∘ τ := by
          funext a
          simp only [Fin.tail, Function.comp_apply, τ]
          by_cases ha1 : a = ⟨j, by omega⟩
          · subst ha1
            have h1 : (⟨j, by omega⟩ : Fin (m + 1)).succ = ⟨j + 1, by omega⟩ := Fin.ext rfl
            rw [h1, Equiv.swap_apply_left, Equiv.swap_apply_left]; rfl
          · by_cases ha2 : a = ⟨j + 1, by omega⟩
            · subst ha2
              have h2 : (⟨j + 1, by omega⟩ : Fin (m + 1)).succ = ⟨j + 2, hi⟩ := Fin.ext rfl
              rw [h2, Equiv.swap_apply_right, Equiv.swap_apply_right]; rfl
            · have hne1 : a.succ ≠ ⟨j + 1, by omega⟩ := fun h =>
                ha1 (Fin.ext (by have := congrArg Fin.val h; simp at this; omega))
              have hne2 : a.succ ≠ ⟨j + 2, hi⟩ := fun h =>
                ha2 (Fin.ext (by have := congrArg Fin.val h; simp at this; omega))
              rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2, Equiv.swap_apply_of_ne_of_ne ha1 ha2]
        rw [h0, htail, ← happly (Fin.tail v ∘ τ), ← happly (Fin.tail v), hfd]

lemma iteratedFDeriv_swap {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} {f : E → F} {x : E} (hf : ContDiffAt ℝ ⊤ f x)
    (i j : Fin k) (v : Fin k → E) :
    iteratedFDeriv ℝ k f x (v ∘ Equiv.swap i j) = iteratedFDeriv ℝ k f x v := by
  suffices h : ∀ (d : ℕ) (a b : Fin k), b.val = a.val + d →
      ∀ w : Fin k → E, iteratedFDeriv ℝ k f x (w ∘ Equiv.swap a b) = iteratedFDeriv ℝ k f x w by
    rcases le_total i.val j.val with hij | hji
    · exact h (j.val - i.val) i j (by omega) v
    · rw [Equiv.swap_comm]
      exact h (i.val - j.val) j i (by omega) v
  intro d
  induction d with
  | zero =>
    intro a b hab w
    have : a = b := Fin.ext (by omega)
    subst this; simp
  | succ d ih =>
    intro a b hab w
    cases d with
    | zero =>
      have ha : a = ⟨a.val, a.isLt⟩ := rfl
      have hb : b = ⟨a.val + 1, by omega⟩ := Fin.ext (by omega)
      rw [ha, hb]
      exact iteratedFDeriv_swap_adj k hf a.val (by omega) w
    | succ d' =>
      let c : Fin k := ⟨a.val + d' + 1, by omega⟩
      have hdecomp : Equiv.swap a b = (Equiv.swap c b).trans ((Equiv.swap a c).trans (Equiv.swap c b)) := by
        ext t
        have hac : a ≠ c := fun h => by have := congrArg Fin.val h; dsimp [c] at this; omega
        have hcb : c ≠ b := fun h => by have := congrArg Fin.val h; dsimp [c] at this; omega
        have hab' : a ≠ b := fun h => by have := congrArg Fin.val h; omega
        by_cases hta : t = a
        · subst hta
          simp [Equiv.swap_apply_of_ne_of_ne hac hab']
        · by_cases htb : t = b
          · subst htb
            simp [Equiv.swap_apply_of_ne_of_ne hac hab']
          · by_cases htc : t = c
            · subst htc
              simp [Equiv.swap_apply_of_ne_of_ne hac.symm hcb, Equiv.swap_apply_of_ne_of_ne hab'.symm hcb.symm]
            · simp [Equiv.swap_apply_of_ne_of_ne hta htb, Equiv.swap_apply_of_ne_of_ne htc htb,
                Equiv.swap_apply_of_ne_of_ne hta htc]
      have hfun : w ∘ Equiv.swap a b = ((w ∘ Equiv.swap c b) ∘ Equiv.swap a c) ∘ Equiv.swap c b := by
        funext t; simp [hdecomp]
      rw [hfun]
      have h1 := iteratedFDeriv_swap_adj k hf (a.val + d' + 1) (by omega)
        ((w ∘ Equiv.swap c b) ∘ Equiv.swap a c)
      have hc_eq : (⟨a.val + d' + 1, by omega⟩ : Fin k) = c := rfl
      have hb_eq : (⟨a.val + d' + 1 + 1, by omega⟩ : Fin k) = b := Fin.ext (by dsimp; omega)
      rw [hc_eq, hb_eq] at h1
      rw [h1]
      rw [ih a c (by dsimp [c]; omega) (w ∘ Equiv.swap c b)]
      have h2 := iteratedFDeriv_swap_adj k hf (a.val + d' + 1) (by omega) w
      rw [hc_eq, hb_eq] at h2
      exact h2

lemma iteratedDeriv_line_eq_iteratedFDeriv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ∀ (k : ℕ) {f : E → F} {x : E} (v : E), ContDiffAt ℝ ⊤ f x →
      iteratedDeriv k (fun t : ℝ => f (x + t • v)) 0 = iteratedFDeriv ℝ k f x (fun _ => v) := by
  intro k
  induction k with
  | zero =>
    intro f x v _
    simp
  | succ k ih =>
    intro f x v hf
    rw [iteratedDeriv_succ']
    have hnhd : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ⊤ f y := hf.eventually (by simp)
    have hline : Continuous (fun t : ℝ => x + t • v) := by fun_prop
    have hnhd0 : ∀ᶠ t in 𝓝 (0 : ℝ), ContDiffAt ℝ ⊤ f (x + t • v) := by
      have htend : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 (x + (0 : ℝ) • v)) :=
        (hline.continuousAt (x := (0 : ℝ))).tendsto
      rw [zero_smul, add_zero] at htend
      exact htend hnhd
    have hderiv_eq : deriv (fun t : ℝ => f (x + t • v)) =ᶠ[𝓝 (0 : ℝ)]
        (fun t : ℝ => fderiv ℝ f (x + t • v) v) := by
      filter_upwards [hnhd0] with t ht
      have hd1 : HasDerivAt (fun s : ℝ => x + s • v) v t := by
        simpa using (hasDerivAt_id t).smul_const v |>.const_add x
      have hd2 : HasFDerivAt f (fderiv ℝ f (x + t • v)) (x + t • v) :=
        (ht.differentiableAt (by simp)).hasFDerivAt
      exact (hd2.comp_hasDerivAt t hd1).deriv
    rw [hderiv_eq.iteratedDeriv_eq]
    have hg : ContDiffAt ℝ ⊤ (fun y => fderiv ℝ f y v) x := by
      have h1 : ContDiffAt ℝ ⊤ (fderiv ℝ f) x := hf.fderiv_right (by simp)
      exact (ContinuousLinearMap.apply ℝ F v).contDiff.contDiffAt.comp x h1
    rw [ih v hg]
    have heval := iteratedFDeriv_apply_eval_clm (ContinuousLinearMap.apply ℝ F v) k
      (hf.fderiv_right (by simp)) (fun _ => v)
    change iteratedFDeriv ℝ k (fun y => (ContinuousLinearMap.apply ℝ F v) (fderiv ℝ f y)) x (fun _ => v) = _
    rw [heval]
    rw [iteratedFDeriv_succ_apply_right]
    rfl

/-!
## 2. Banach's theorem on symmetric multilinear forms on real Hilbert space
-/

lemma banach_symmetric_multilinear {n k : ℕ} (hn : 0 < n)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => EuclideanSpace ℝ (Fin n)) ℝ)
    (hsymm : ∀ (i j : Fin k) (v : Fin k → EuclideanSpace ℝ (Fin n)),
      T (v ∘ Equiv.swap i j) = T v)
    {M : ℝ} (_hM : 0 ≤ M)
    (hdiag : ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 → |T (fun _ => v)| ≤ M) :
    ∀ v : Fin k → EuclideanSpace ℝ (Fin n), (∀ i, ‖v i‖ = 1) → |T v| ≤ M := by
  let E := EuclideanSpace ℝ (Fin n)
  let S : Set E := Metric.sphere (0 : E) 1
  have hS_ne : S.Nonempty := by
    refine ⟨EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ), ?_⟩
    dsimp only [S, E]
    simp
  have hS_comp : IsCompact S := isCompact_sphere (0 : E) 1
  let P : Set (Fin k → E) := Set.univ.pi (fun _ => S)
  have hP_ne : P.Nonempty := ⟨fun _ => hS_ne.some, fun _ _ => hS_ne.some_mem⟩
  have hP_comp : IsCompact P := isCompact_univ_pi (fun _ => hS_comp)
  have hTcont : Continuous (fun v : Fin k → E => |T v|) := T.cont.abs
  obtain ⟨v0, hv0_mem, hv0_max⟩ := hP_comp.exists_isMaxOn hP_ne hTcont.continuousOn
  set μ := |T v0|
  have hμ_ge : ∀ w ∈ P, |T w| ≤ μ := fun w hw => hv0_max hw
  have hμ_nonneg : 0 ≤ μ := abs_nonneg _
  let K : Set (Fin k → E) := {w ∈ P | |T w| = μ}
  have hK_ne : K.Nonempty := ⟨v0, hv0_mem, rfl⟩
  have hK_comp : IsCompact K :=
    hP_comp.of_isClosed_subset (hP_comp.isClosed.inter (isClosed_eq hTcont continuous_const))
      (fun _ hw => hw.1)
  have hsum_cont : Continuous (fun w : Fin k → E => ‖∑ r : Fin k, w r‖ ^ 2) := by
    have : Continuous (fun w : Fin k → E => ∑ r : Fin k, w r) :=
      continuous_finsetSum Finset.univ (fun r _ => continuous_apply r)
    exact (this.norm).pow 2
  obtain ⟨v, hvK, hv_max⟩ := hK_comp.exists_isMaxOn hK_ne hsum_cont.continuousOn
  have hvP : v ∈ P := hvK.1
  have hvT : |T v| = μ := hvK.2
  have hv_norm : ∀ i, ‖v i‖ = 1 := fun i => by simpa [P, S, Metric.mem_sphere] using hvP i (Set.mem_univ i)
  have hall_eq : ∀ i j : Fin k, v i = v j := by
    intro i j
    by_contra hne
    have hij : i ≠ j := fun h => hne (h ▸ rfl)
    let replace2 : E → E → (Fin k → E) := fun a b r =>
      if r = i then a else if r = j then b else v r
    have hrep_orig : replace2 (v i) (v j) = v := by
      funext r; simp only [replace2]; split_ifs with h1 h2 <;> simp_all
    have hrep_symm : ∀ a b : E, T (replace2 a b) = T (replace2 b a) := by
      intro a b
      rw [← hsymm i j (replace2 a b)]
      congr 1; funext r
      simp only [Function.comp_apply, replace2]
      by_cases hri : r = i
      · subst hri; simp [hij.symm]
      · by_cases hrj : r = j
        · subst hrj; simp [hij.symm]
        · rw [Equiv.swap_apply_of_ne_of_ne hri hrj]; simp [hri, hrj]
    have hrep_add_left : ∀ a₁ a₂ b : E, T (replace2 (a₁ + a₂) b) = T (replace2 a₁ b) + T (replace2 a₂ b) := by
      intro a₁ a₂ b
      have h1 : replace2 (a₁ + a₂) b = Function.update (replace2 a₁ b) i (a₁ + a₂) := by
        funext r; by_cases hri : r = i <;> simp [replace2, Function.update, hri]
      have h2 : replace2 a₁ b = Function.update (replace2 a₁ b) i a₁ := by
        funext r; by_cases hri : r = i <;> simp [replace2, Function.update, hri]
      have h3 : replace2 a₂ b = Function.update (replace2 a₁ b) i a₂ := by
        funext r; by_cases hri : r = i <;> simp [replace2, Function.update, hri]
      rw [h1, T.map_update_add, ← h2, ← h3]
    have hrep_add_right : ∀ a b₁ b₂ : E, T (replace2 a (b₁ + b₂)) = T (replace2 a b₁) + T (replace2 a b₂) := by
      intro a b₁ b₂
      rw [hrep_symm a (b₁ + b₂), hrep_add_left, hrep_symm b₁ a, hrep_symm b₂ a]
    have hrep_smul_left : ∀ (c : ℝ) (a b : E), T (replace2 (c • a) b) = c * T (replace2 a b) := by
      intro c a b
      have h1 : replace2 (c • a) b = Function.update (replace2 a b) i (c • a) := by
        funext r; by_cases hri : r = i <;> simp [replace2, Function.update, hri]
      have h2 : replace2 a b = Function.update (replace2 a b) i a := by
        funext r; by_cases hri : r = i <;> simp [replace2, Function.update, hri]
      rw [h1, T.map_update_smul, ← h2, smul_eq_mul]
    have hrep_smul_right : ∀ (c : ℝ) (a b : E), T (replace2 a (c • b)) = c * T (replace2 a b) := by
      intro c a b
      rw [hrep_symm, hrep_smul_left, hrep_symm]
    have hrep_P : ∀ a b : E, ‖a‖ = 1 → ‖b‖ = 1 → replace2 a b ∈ P := by
      intro a b ha hb r _
      simp only [replace2, S, Metric.mem_sphere, dist_zero_right]
      split_ifs
      · exact ha
      · exact hb
      · exact hv_norm r
    let Srest : E := ∑ r ∈ (Finset.univ.erase i).erase j, v r
    have hsum_rep : ∀ a b : E, ∑ r : Fin k, replace2 a b r = a + b + Srest := by
      intro a b
      have hi_mem : i ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ i
      have hj_mem : j ∈ (Finset.univ : Finset (Fin k)).erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
      rw [← Finset.add_sum_erase _ _ hi_mem, ← Finset.add_sum_erase _ _ hj_mem]
      have h1 : replace2 a b i = a := by simp [replace2]
      have h2 : replace2 a b j = b := by simp [replace2, hij.symm]
      have h3 : ∑ r ∈ (Finset.univ.erase i).erase j, replace2 a b r = Srest := by
        refine Finset.sum_congr rfl fun r hr => ?_
        have hrj : r ≠ j := (Finset.mem_erase.mp hr).1
        have hri : r ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
        simp [replace2, hri, hrj]
      rw [h1, h2, h3, add_assoc]
    have hsum_v : ∑ r : Fin k, v r = v i + v j + Srest := by
      conv_lhs => rw [← hrep_orig]
      exact hsum_rep (v i) (v j)
    by_cases hsum0 : v i + v j = 0
    · have hvj_neg : v j = -(v i) := eq_neg_of_add_eq_zero_right hsum0
      have hT_ii : |T (replace2 (v i) (v i))| = μ := by
        have h1 : T (replace2 (v i) (v j)) = -T (replace2 (v i) (v i)) := by
          rw [hvj_neg, show -(v i) = (-1 : ℝ) • v i by simp, hrep_smul_right]; ring
        calc |T (replace2 (v i) (v i))| = |-T (replace2 (v i) (v i))| := (abs_neg _).symm
          _ = |T (replace2 (v i) (v j))| := by rw [← h1]
          _ = |T v| := by rw [hrep_orig]
          _ = μ := hvT
      let ε : ℝ := if 0 ≤ inner ℝ (v i) Srest then 1 else -1
      have hε_sq : ε ^ 2 = 1 := by dsimp [ε]; split_ifs <;> norm_num
      have hε_abs : |ε| = 1 := by dsimp [ε]; split_ifs <;> norm_num
      have hε_inner : 0 ≤ inner ℝ (ε • v i) Srest := by
        rw [inner_smul_left]; dsimp [ε]; split_ifs with h <;> simp <;> linarith
      have hu_norm : ‖ε • v i‖ = 1 := by rw [norm_smul, Real.norm_eq_abs, hε_abs, hv_norm i, mul_one]
      have hw_K : replace2 (ε • v i) (ε • v i) ∈ K := by
        refine ⟨hrep_P _ _ hu_norm hu_norm, ?_⟩
        rw [hrep_smul_left, hrep_smul_right, ← mul_assoc, ← sq, hε_sq, one_mul, hT_ii]
      have hle : ‖∑ r : Fin k, replace2 (ε • v i) (ε • v i) r‖ ^ 2 ≤ ‖∑ r : Fin k, v r‖ ^ 2 :=
        hv_max hw_K
      rw [hsum_rep, hsum_v, hsum0, zero_add] at hle
      have hnorm_ge : ‖ε • v i + ε • v i + Srest‖ ^ 2 = 4 + 4 * inner ℝ (ε • v i) Srest + ‖Srest‖ ^ 2 := by
        rw [show ε • v i + ε • v i = (2 : ℝ) • (ε • v i) by module]
        rw [norm_add_sq_real, norm_smul, Real.norm_ofNat, hu_norm, inner_smul_left]
        simp; ring
      linarith
    · set c := ‖v i + v j‖
      have hc_pos : 0 < c := norm_pos_iff.mpr hsum0
      have hpara : ‖v i + v j‖ ^ 2 + ‖v i - v j‖ ^ 2 = 4 := by
        have := parallelogram_law_with_norm ℝ (v i) (v j)
        rw [hv_norm i, hv_norm j] at this
        linarith
      have hdiff_pos : 0 < ‖v i - v j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      have hc_lt2 : c < 2 := by nlinarith [sq_pos_of_pos hdiff_pos]
      set u := c⁻¹ • (v i + v j)
      have hu_norm : ‖u‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc_pos, inv_mul_cancel₀ hc_pos.ne']
      have hT_uu : |T (replace2 u u)| = μ := by
        have hpol : 4 * T (replace2 (v i) (v j)) =
            T (replace2 (v i + v j) (v i + v j)) - T (replace2 (v i - v j) (v i - v j)) := by
          have h1 : T (replace2 (v i + v j) (v i + v j)) =
              T (replace2 (v i) (v i)) + 2 * T (replace2 (v i) (v j)) + T (replace2 (v j) (v j)) := by
            rw [hrep_add_left, hrep_add_right, hrep_add_right, hrep_symm (v j) (v i)]; ring
          have h2 : T (replace2 (v i - v j) (v i - v j)) =
              T (replace2 (v i) (v i)) - 2 * T (replace2 (v i) (v j)) + T (replace2 (v j) (v j)) := by
            rw [sub_eq_add_neg, show -(v j) = (-1 : ℝ) • v j by simp,
              hrep_add_left, hrep_add_right, hrep_add_right,
              hrep_smul_left, hrep_smul_right, hrep_smul_left, hrep_smul_right, hrep_symm (v j) (v i)]
            ring
          linarith
        have h1 : T (replace2 (v i + v j) (v i + v j)) = c ^ 2 * T (replace2 u u) := by
          have : v i + v j = c • u := by rw [smul_smul, mul_inv_cancel₀ hc_pos.ne', one_smul]
          rw [this, hrep_smul_left, hrep_smul_right]; ring
        set d := ‖v i - v j‖
        set w := d⁻¹ • (v i - v j)
        have hw_norm : ‖w‖ = 1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hdiff_pos, inv_mul_cancel₀ hdiff_pos.ne']
        have h2 : T (replace2 (v i - v j) (v i - v j)) = d ^ 2 * T (replace2 w w) := by
          have : v i - v j = d • w := by rw [smul_smul, mul_inv_cancel₀ hdiff_pos.ne', one_smul]
          rw [this, hrep_smul_left, hrep_smul_right]; ring
        have hu_le : |T (replace2 u u)| ≤ μ := hμ_ge _ (hrep_P u u hu_norm hu_norm)
        have hw_le : |T (replace2 w w)| ≤ μ := hμ_ge _ (hrep_P w w hw_norm hw_norm)
        have h4μ : 4 * μ ≤ c ^ 2 * |T (replace2 u u)| + d ^ 2 * |T (replace2 w w)| := by
          calc 4 * μ = |4 * T (replace2 (v i) (v j))| := by
                rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), hrep_orig, hvT]
            _ = |c ^ 2 * T (replace2 u u) - d ^ 2 * T (replace2 w w)| := by rw [hpol, h1, h2]
            _ ≤ |c ^ 2 * T (replace2 u u)| + |d ^ 2 * T (replace2 w w)| := abs_sub _ _
            _ = c ^ 2 * |T (replace2 u u)| + d ^ 2 * |T (replace2 w w)| := by
                rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg c), abs_of_nonneg (sq_nonneg d)]
        have hcd : c ^ 2 + d ^ 2 = 4 := hpara
        nlinarith [sq_pos_of_pos hc_pos, sq_nonneg d]
      let ε : ℝ := if 0 ≤ inner ℝ u Srest then 1 else -1
      have hε_sq : ε ^ 2 = 1 := by dsimp [ε]; split_ifs <;> norm_num
      have hε_abs : |ε| = 1 := by dsimp [ε]; split_ifs <;> norm_num
      have hεu_norm : ‖ε • u‖ = 1 := by rw [norm_smul, Real.norm_eq_abs, hε_abs, hu_norm, mul_one]
      have hw_K : replace2 (ε • u) (ε • u) ∈ K := by
        refine ⟨hrep_P _ _ hεu_norm hεu_norm, ?_⟩
        rw [hrep_smul_left, hrep_smul_right, ← mul_assoc, ← sq, hε_sq, one_mul, hT_uu]
      have hle : ‖∑ r : Fin k, replace2 (ε • u) (ε • u) r‖ ^ 2 ≤ ‖∑ r : Fin k, v r‖ ^ 2 :=
        hv_max hw_K
      rw [hsum_rep, hsum_v] at hle
      have hcu : v i + v j = c • u := by rw [smul_smul, mul_inv_cancel₀ hc_pos.ne', one_smul]
      have hnorm1 : ‖v i + v j + Srest‖ ^ 2 = c ^ 2 + 2 * c * inner ℝ u Srest + ‖Srest‖ ^ 2 := by
        rw [hcu, norm_add_sq_real, norm_smul, Real.norm_eq_abs, abs_of_pos hc_pos, hu_norm,
          inner_smul_left]
        simp; ring
      have hnorm2 : ‖ε • u + ε • u + Srest‖ ^ 2 = 4 + 4 * ε * inner ℝ u Srest + ‖Srest‖ ^ 2 := by
        rw [show ε • u + ε • u = (2 * ε) • u by module, norm_add_sq_real, norm_smul,
          Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), hε_abs, hu_norm,
          inner_smul_left]
        simp; ring
      rw [hnorm1, hnorm2] at hle
      have hterm : 0 ≤ (2 * ε - c) * inner ℝ u Srest := by
        dsimp [ε]
        split_ifs with h
        · nlinarith
        · push Not at h; nlinarith
      nlinarith [sq_pos_of_pos hc_pos]
  intro w hw
  have hwP : w ∈ P := fun i _ => by simpa [S, Metric.mem_sphere] using hw i
  have hle : |T w| ≤ μ := hμ_ge w hwP
  -- Handle k = 0 vs k > 0 cleanly
  cases k with
  | zero =>
    have h0 : w = fun _ => hS_ne.some := funext fun i => Fin.elim0 i
    rw [h0]
    exact hdiag hS_ne.some (by simpa [S, Metric.mem_sphere] using hS_ne.some_mem)
  | succ m =>
    have hv_const : v = fun _ => v 0 := funext fun i => hall_eq i 0
    have hμ_le : μ ≤ M := by
      rw [← hvT, hv_const]
      exact hdiag (v 0) (hv_norm 0)
    exact le_trans hle hμ_le

/-!
## 3. Smoothness/calculus helpers, powers vanishing at a point, and Taylor integral remainder
-/

lemma contDiffAt_deriv_top {g : ℝ → ℝ} {x : ℝ} (hg : ContDiffAt ℝ ⊤ g x) :
    ContDiffAt ℝ ⊤ (deriv g) x := by
  have h1 : deriv g = fun y => (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)) (fderiv ℝ g y) :=
    funext fun _ => rfl
  rw [h1]
  exact (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).contDiff.contDiffAt.comp x (hg.fderiv_right (by simp))

lemma contDiffAt_iteratedDeriv_top {g : ℝ → ℝ} {x : ℝ} (hg : ContDiffAt ℝ ⊤ g x) :
    ∀ k : ℕ, ContDiffAt ℝ ⊤ (iteratedDeriv k g) x := by
  intro k
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact contDiffAt_deriv_top ih

lemma poly_iteratedDeriv_eval :
    ∀ (k : ℕ) (P : Polynomial ℝ) (x : ℝ),
      iteratedDeriv k (fun t => P.eval t) x = (Polynomial.derivative^[k] P).eval x := by
  intro k
  induction k with
  | zero => intro P x; simp
  | succ k ih =>
    intro P x
    rw [iteratedDeriv_succ', Function.iterate_succ_apply]
    have h1 : deriv (fun t => P.eval t) = fun t => (Polynomial.derivative P).eval t :=
      funext fun t => (P.hasDerivAt t).deriv
    rw [h1]
    exact ih (Polynomial.derivative P) x

lemma iteratedDeriv_const_mul_real :
    ∀ (n : ℕ) (c : ℝ) (f : ℝ → ℝ) (x : ℝ),
      iteratedDeriv n (fun t => c * f t) x = c * iteratedDeriv n f x := by
  intro n
  induction n with
  | zero => intro c f x; simp
  | succ n ih =>
    intro c f x
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    have h1 : deriv (fun t => c * f t) = fun t => c * deriv f t :=
      funext fun t => deriv_const_mul_field c
    rw [h1, ih c (deriv f) x]

lemma iteratedDeriv_comp_const_add_top :
    ∀ (k : ℕ) {F : ℝ → ℝ} {a x : ℝ}, ContDiffAt ℝ ⊤ F (a + x) →
      iteratedDeriv k (fun t : ℝ => F (a + t)) x = iteratedDeriv k F (a + x) := by
  intro k
  induction k with
  | zero => intro F a x _; simp
  | succ k ih =>
    intro F a x hF
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    have hnhd : ∀ᶠ y in 𝓝 (a + x), ContDiffAt ℝ ⊤ F y := hF.eventually (by simp)
    have hadd_cont : Continuous (fun t : ℝ => a + t) := continuous_const.add continuous_id
    have hnhd_x : ∀ᶠ t in 𝓝 x, ContDiffAt ℝ ⊤ F (a + t) :=
      (hadd_cont.continuousAt (x := x)).tendsto hnhd
    have hderiv_eq : deriv (fun t : ℝ => F (a + t)) =ᶠ[𝓝 x] fun t => deriv F (a + t) := by
      filter_upwards [hnhd_x] with t ht
      have h1 : HasDerivAt (fun s : ℝ => a + s) 1 t := by
        simpa using (hasDerivAt_id t).const_add a
      have h2 : HasDerivAt F (deriv F (a + t)) (a + t) := (ht.differentiableAt (by simp)).hasDerivAt
      change deriv (F ∘ fun s : ℝ => a + s) t = deriv F (a + t)
      simpa using (h2.comp t h1).deriv
    rw [hderiv_eq.iteratedDeriv_eq]
    exact ih (contDiffAt_deriv_top hF)

lemma iteratedDeriv_pow_vanish {h : ℝ → ℝ} {x : ℝ} (hh : ContDiffAt ℝ ⊤ h x) (hx : h x = 0) :
    ∀ (m : ℕ),
      (∀ j < m, iteratedDeriv j (fun t => (h t) ^ m) x = 0) ∧
      iteratedDeriv m (fun t => (h t) ^ m) x = (m.factorial : ℝ) * (deriv h x) ^ m ∧
      (1 ≤ m → iteratedDeriv (m + 1) (fun t => (h t) ^ m) x =
        (m.factorial : ℝ) * ((m + 1) * m / 2 : ℝ) * (deriv h x) ^ (m - 1) * iteratedDeriv 2 h x) := by
  intro m
  induction m with
  | zero =>
    refine ⟨fun j hj => by omega, by simp, fun h => by omega⟩
  | succ m ih =>
    have hpow_eq : (fun t => (h t) ^ (m + 1)) = (fun t => h t * (h t) ^ m) := by
      funext t; ring
    have hpow_smooth : ContDiffAt ℝ ⊤ (fun t => (h t) ^ m) x := hh.pow m
    have hleib : ∀ n : ℕ,
        iteratedDeriv n (fun t => (h t) ^ (m + 1)) x =
          ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * iteratedDeriv i h x * iteratedDeriv (n - i) (fun t => (h t) ^ m) x := by
      intro n
      rw [hpow_eq, iteratedDeriv_fun_mul (hh.of_le (by simp)) (hpow_smooth.of_le (by simp))]
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      rw [hleib j]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      by_cases hi0 : i = 0
      · subst hi0; simp [hx]
      · have hlt : j - i < m := by omega
        rw [ih.1 (j - i) hlt, mul_zero]
    · rw [hleib (m + 1)]
      have honly : ∀ i ∈ Finset.range (m + 2), i ≠ 1 →
          ((m + 1).choose i : ℝ) * iteratedDeriv i h x *
            iteratedDeriv (m + 1 - i) (fun t => (h t) ^ m) x = 0 := by
        intro i hi hne1
        have hi_le : i ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        by_cases hi0 : i = 0
        · subst hi0; simp [hx]
        · have hlt : m + 1 - i < m := by omega
          rw [ih.1 (m + 1 - i) hlt, mul_zero]
      rw [Finset.sum_eq_single 1 honly (fun h => absurd (Finset.mem_range.mpr (by omega)) h)]
      simp only [Nat.choose_one_right, Nat.add_sub_cancel, iteratedDeriv_one, ih.2.1,
        Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring
    · intro _
      rw [hleib (m + 2)]
      cases m with
      | zero =>
        simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
          Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_self,
          iteratedDeriv_zero, hx, zero_mul, mul_zero, iteratedDeriv_one, pow_zero,
          Nat.factorial_one, Nat.cast_one]
        have h2 : iteratedDeriv 1 (fun _ : ℝ => (1 : ℝ)) x = 0 := by
          rw [iteratedDeriv_const]; simp
        simp [h2]
      | succ m' =>
        have honly : ∀ i ∈ Finset.range (m' + 4), i ≠ 1 ∧ i ≠ 2 →
            ((m' + 3).choose i : ℝ) * iteratedDeriv i h x *
              iteratedDeriv (m' + 3 - i) (fun t => (h t) ^ (m' + 1)) x = 0 := by
          intro i hi ⟨hne1, hne2⟩
          have hi_le : i ≤ m' + 3 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          by_cases hi0 : i = 0
          · subst hi0; simp [hx]
          · have hlt : m' + 3 - i < m' + 1 := by omega
            rw [ih.1 (m' + 3 - i) hlt, mul_zero]
        have hsum_pair :
            ∑ i ∈ Finset.range (m' + 4),
              ((m' + 3).choose i : ℝ) * iteratedDeriv i h x *
                iteratedDeriv (m' + 3 - i) (fun t => (h t) ^ (m' + 1)) x =
            ((m' + 3).choose 1 : ℝ) * iteratedDeriv 1 h x *
                iteratedDeriv (m' + 2) (fun t => (h t) ^ (m' + 1)) x +
            ((m' + 3).choose 2 : ℝ) * iteratedDeriv 2 h x *
                iteratedDeriv (m' + 1) (fun t => (h t) ^ (m' + 1)) x := by
          have hsub : ({1, 2} : Finset ℕ) ⊆ Finset.range (m' + 4) := by
            intro i hi
            simp only [Finset.mem_insert, Finset.mem_singleton] at hi
            rcases hi with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
          rw [← Finset.sum_subset hsub (fun i hi hnot => honly i hi (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot; exact hnot))]
          rw [Finset.sum_pair (by norm_num)]
          simp only [show m' + 3 - 1 = m' + 2 by omega, show m' + 3 - 2 = m' + 1 by omega]
        rw [hsum_pair, iteratedDeriv_one, ih.2.2 (by omega), ih.2.1]
        have hch1 : ((m' + 3).choose 1 : ℝ) = (m' + 3 : ℝ) := by
          rw [Nat.choose_one_right]; push_cast; ring
        have hch2 : ((m' + 3).choose 2 : ℝ) = ((m' + 3) * (m' + 2) / 2 : ℝ) := by
          rw [Nat.choose_two_right, show m' + 3 - 1 = m' + 2 by omega]
          have hdvd : 2 ∣ (m' + 3) * (m' + 2) := by
            have := Nat.even_mul_succ_self (m' + 2)
            rw [even_iff_two_dvd, mul_comm] at this
            simpa [Nat.add_assoc] using this
          rw [Nat.cast_div hdvd (by norm_num)]; push_cast; ring
        rw [hch1, hch2]
        simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        have hpow : deriv h x * (deriv h x) ^ m' = (deriv h x) ^ (m' + 1) := by ring
        have hpow2 : (deriv h x) ^ (m' + 1) = deriv h x * (deriv h x) ^ m' := by ring
        ring

lemma taylor_integral_remainder {g : ℝ → ℝ} {k : ℕ} {R : ℝ} (hR : 0 < R)
    (hg : ContDiffOn ℝ ⊤ g (Set.Ioo (-R) R)) (hk : 1 ≤ k) :
    ∀ u ∈ Set.Ioo (0 : ℝ) R,
      g u = (∑ j ∈ Finset.range k, iteratedDeriv j g 0 / (j.factorial : ℝ) * u ^ j) +
        ∫ s in (0 : ℝ)..u, (u - s) ^ (k - 1) / ((k - 1).factorial : ℝ) * iteratedDeriv k g s := by
  -- Prove by induction on k >= 1
  induction k with
  | zero => omega
  | succ m ih =>
    intro u hu
    cases m with
    | zero =>
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
        iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, mul_one,
        Nat.sub_self, one_mul, iteratedDeriv_one]
      have hdiff : ∀ s ∈ Set.uIcc (0 : ℝ) u, HasDerivAt g (deriv g s) s := by
        intro s hs
        rw [Set.uIcc_of_le hu.1.le] at hs
        have hmem : s ∈ Set.Ioo (-R) R := ⟨by linarith [hs.1], by linarith [hs.2, hu.2]⟩
        exact ((hg s hmem).contDiffAt (isOpen_Ioo.mem_nhds hmem)).differentiableAt (by simp) |>.hasDerivAt
      have hint : IntervalIntegrable (deriv g) volume 0 u := by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le hu.1.le]
        intro s hs
        have hmem : s ∈ Set.Ioo (-R) R := ⟨by linarith [hs.1], by linarith [hs.2, hu.2]⟩
        have hcont : ContinuousAt (deriv g) s :=
          (contDiffAt_deriv_top ((hg s hmem).contDiffAt (isOpen_Ioo.mem_nhds hmem))).continuousAt
        exact hcont.continuousWithinAt
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hdiff hint
      linarith
    | succ m' =>
      have hprev := ih (by omega) u hu
      -- Integration by parts on the remainder
      have hcont_d1 : ContinuousOn (iteratedDeriv (m' + 1) g) (Set.uIcc 0 u) := by
        rw [Set.uIcc_of_le hu.1.le]
        intro s hs
        have hmem : s ∈ Set.Ioo (-R) R := ⟨by linarith [hs.1], by linarith [hs.2, hu.2]⟩
        exact (contDiffAt_iteratedDeriv_top ((hg s hmem).contDiffAt (isOpen_Ioo.mem_nhds hmem)) (m' + 1)).continuousAt.continuousWithinAt
      have hcont_d2 : ContinuousOn (iteratedDeriv (m' + 2) g) (Set.uIcc 0 u) := by
        rw [Set.uIcc_of_le hu.1.le]
        intro s hs
        have hmem : s ∈ Set.Ioo (-R) R := ⟨by linarith [hs.1], by linarith [hs.2, hu.2]⟩
        exact (contDiffAt_iteratedDeriv_top ((hg s hmem).contDiffAt (isOpen_Ioo.mem_nhds hmem)) (m' + 2)).continuousAt.continuousWithinAt
      let U : ℝ → ℝ := fun s => -((u - s) ^ (m' + 1) / ((m' + 1).factorial : ℝ))
      let U' : ℝ → ℝ := fun s => (u - s) ^ m' / (m'.factorial : ℝ)
      have hU : ∀ s ∈ Set.uIcc (0 : ℝ) u, HasDerivAt U (U' s) s := by
        intro s _
        have h1 : HasDerivAt (fun s : ℝ => u - s) (-1) s := by
          simpa using (hasDerivAt_id s).const_sub u
        have h2 := ((h1.pow (m' + 1)).div_const ((m' + 1).factorial : ℝ)).neg
        refine h2.congr_deriv ?_
        dsimp only [U']
        rw [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        have hne : ((m' + 1 : ℝ)) ≠ 0 := by positivity
        have hfne : ((m'.factorial : ℝ)) ≠ 0 := by positivity
        field_simp [hne, hfne]
      have hV : ∀ s ∈ Set.uIcc (0 : ℝ) u,
          HasDerivAt (iteratedDeriv (m' + 1) g) (iteratedDeriv (m' + 2) g s) s := by
        intro s hs
        rw [Set.uIcc_of_le hu.1.le] at hs
        have hmem : s ∈ Set.Ioo (-R) R := ⟨by linarith [hs.1], by linarith [hs.2, hu.2]⟩
        rw [iteratedDeriv_succ (n := m' + 1)]
        exact (contDiffAt_iteratedDeriv_top ((hg s hmem).contDiffAt (isOpen_Ioo.mem_nhds hmem)) (m' + 1)).differentiableAt (by simp) |>.hasDerivAt
      have hprod : ∀ s ∈ Set.uIcc (0 : ℝ) u,
          HasDerivAt (fun s => U s * iteratedDeriv (m' + 1) g s)
            (U' s * iteratedDeriv (m' + 1) g s + U s * iteratedDeriv (m' + 2) g s) s :=
        fun s hs => (hU s hs).fun_mul (hV s hs)
      have hint1 : IntervalIntegrable (fun s => U' s * iteratedDeriv (m' + 1) g s) volume 0 u :=
        ((by fun_prop : Continuous U').continuousOn.mul hcont_d1).intervalIntegrable
      have hint2 : IntervalIntegrable (fun s => U s * iteratedDeriv (m' + 2) g s) volume 0 u :=
        ((by fun_prop : Continuous U).continuousOn.mul hcont_d2).intervalIntegrable
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hprod (hint1.add hint2)
      rw [intervalIntegral.integral_add hint1 hint2] at hftc
      have hU_u : U u = 0 := by simp [U]
      have hU_0 : U 0 = -(u ^ (m' + 1) / ((m' + 1).factorial : ℝ)) := by simp [U]
      rw [hU_u, zero_mul, hU_0] at hftc
      have hneg_int : ∫ s in (0 : ℝ)..u, U s * iteratedDeriv (m' + 2) g s =
          -(∫ s in (0 : ℝ)..u, (u - s) ^ (m' + 1) / ((m' + 1).factorial : ℝ) * iteratedDeriv (m' + 2) g s) := by
        simp only [U, neg_mul, intervalIntegral.integral_neg]
      rw [hneg_int] at hftc
      rw [Finset.sum_range_succ, hprev]
      dsimp only [U'] at hftc
      simp only [Nat.add_sub_cancel] at hprev ⊢
      have hcomm : iteratedDeriv (m' + 1) g 0 / ((m' + 1).factorial : ℝ) * u ^ (m' + 1) =
          u ^ (m' + 1) / ((m' + 1).factorial : ℝ) * iteratedDeriv (m' + 1) g 0 := by ring
      linarith

/-!
## 4. Exact Catalan kernel formula and positivity via the 1-line PDE
-/

noncomputable def rFun (b x : ℝ) : ℝ := Real.sqrt (x ^ 2 + b ^ 2)

lemma rFun_pos {b : ℝ} (hb : 0 < b) (x : ℝ) : 0 < rFun b x :=
  Real.sqrt_pos.mpr (by positivity)

lemma rFun_sq {b : ℝ} (hb : 0 < b) (x : ℝ) : rFun b x ^ 2 = x ^ 2 + b ^ 2 :=
  Real.sq_sqrt (by positivity)

lemma rFun_contDiff {b : ℝ} (hb : 0 < b) : ContDiff ℝ ⊤ (rFun b) := by
  have h1 : ContDiff ℝ ⊤ (fun x : ℝ => x ^ 2 + b ^ 2) := by fun_prop
  exact h1.sqrt (fun x => by positivity)

lemma rFun_hasDerivAt {b : ℝ} (hb : 0 < b) (x : ℝ) :
    HasDerivAt (rFun b) (x / rFun b x) x := by
  have h1 : HasDerivAt (fun t : ℝ => t ^ 2 + b ^ 2) (2 * x) x := by
    simpa using ((hasDerivAt_pow 2 x).add_const (b ^ 2))
  have h2 := h1.sqrt (by positivity : x ^ 2 + b ^ 2 ≠ 0)
  refine h2.congr_deriv ?_
  have hr : rFun b x ≠ 0 := (rFun_pos hb x).ne'
  dsimp only [rFun] at hr ⊢
  field_simp [hr]

lemma rFun_deriv {b : ℝ} (hb : 0 < b) (x : ℝ) : deriv (rFun b) x = x / rFun b x :=
  (rFun_hasDerivAt hb x).deriv

lemma rFun_second_deriv {b : ℝ} (hb : 0 < b) (x : ℝ) :
    iteratedDeriv 2 (rFun b) x = b ^ 2 / rFun b x ^ 3 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv_eq : deriv (rFun b) = fun t => t / rFun b t := funext (rFun_deriv hb)
  rw [hderiv_eq]
  have hr := rFun_pos hb x
  have h := (hasDerivAt_id x).fun_div (rFun_hasDerivAt hb x) hr.ne'
  change deriv (fun y => id y / rFun b y) x = _
  rw [h.deriv]
  have hsq := rFun_sq hb x
  simp only [id_eq]
  field_simp [hr.ne']
  nlinarith

/-- The differential kernel `F_k(b, x, s) = (1/(k-1)!) d^k/dx^k ((r(x) - s)^(k-1))`. -/
noncomputable def kernelF (k : ℕ) (b x s : ℝ) : ℝ :=
  iteratedDeriv k (fun t => (rFun b t - s) ^ (k - 1)) x / ((k - 1).factorial : ℝ)

/-- Catalan-binomial coefficient `C(m, j) = (m+2)! / (2 * 4^j * j! * (j+1)! * (m-2j)!)`. -/
noncomputable def catCoeff (m j : ℕ) : ℝ :=
  if 2 * j ≤ m then
    ((m + 2).factorial : ℝ) /
      (2 * (4 : ℝ) ^ j * (j.factorial : ℝ) * ((j + 1).factorial : ℝ) * ((m - 2 * j).factorial : ℝ))
  else 0

/-- Explicit closed-form nonnegative kernel `G_{m+2}(b, x, s)`. -/
noncomputable def kernelG (m : ℕ) (b x s : ℝ) : ℝ :=
  b ^ 2 / rFun b x ^ (2 * m + 3) *
    ∑ j ∈ Finset.range (m / 2 + 1),
      catCoeff m j * (x * s) ^ (m - 2 * j) * (b ^ 2 * (rFun b x ^ 2 - s ^ 2)) ^ j

lemma catCoeff_nonneg (m j : ℕ) : 0 ≤ catCoeff m j := by
  unfold catCoeff
  split_ifs <;> positivity

lemma kernelG_nonneg {m : ℕ} {b x s : ℝ} (hb : 0 < b) (hx : 0 ≤ x)
    (hs0 : 0 ≤ s) (hsr : s ≤ rFun b x) : 0 ≤ kernelG m b x s := by
  unfold kernelG
  have hr : 0 < rFun b x := rFun_pos hb x
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => ?_)
  have hdiff : 0 ≤ rFun b x ^ 2 - s ^ 2 := by nlinarith
  exact mul_nonneg (mul_nonneg (catCoeff_nonneg m j) (pow_nonneg (mul_nonneg hx hs0) _))
    (pow_nonneg (mul_nonneg (sq_nonneg b) hdiff) j)

lemma kernelG_at_r {m : ℕ} {b x : ℝ} (hb : 0 < b) :
    kernelG m b x (rFun b x) =
      ((m + 2) * (m + 1) / 2 : ℝ) * (x / rFun b x) ^ m * (b ^ 2 / rFun b x ^ 3) := by
  unfold kernelG
  have honly : ∀ j ∈ Finset.range (m / 2 + 1), j ≠ 0 →
      catCoeff m j * (x * rFun b x) ^ (m - 2 * j) *
        (b ^ 2 * (rFun b x ^ 2 - rFun b x ^ 2)) ^ j = 0 := by
    intro j _ hj
    rw [sub_self, mul_zero, zero_pow hj, mul_zero]
  rw [Finset.sum_eq_single 0 honly (fun h => absurd (Finset.mem_range.mpr (by omega)) h)]
  have hcat0 : catCoeff m 0 = ((m + 2) * (m + 1) / 2 : ℝ) := by
    unfold catCoeff
    rw [if_pos (by omega)]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one,
      Nat.mul_zero, Nat.sub_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add]
    have hf : (m.factorial : ℝ) ≠ 0 := by positivity
    field_simp [hf]
    ring
  have hr : rFun b x ≠ 0 := (rFun_pos hb x).ne'
  rw [hcat0]
  simp only [Nat.mul_zero, Nat.sub_zero, pow_zero, mul_one, mul_pow, div_pow]
  have hpow : rFun b x ^ (2 * m + 3) = rFun b x ^ m * rFun b x ^ m * rFun b x ^ 3 := by ring
  rw [hpow]
  field_simp [hr]

lemma kernelF_at_r {m : ℕ} {b x : ℝ} (hb : 0 < b) :
    kernelF (m + 2) b x (rFun b x) =
      ((m + 2) * (m + 1) / 2 : ℝ) * (x / rFun b x) ^ m * (b ^ 2 / rFun b x ^ 3) := by
  unfold kernelF
  rw [show m + 2 - 1 = m + 1 by omega]
  have hh : ContDiffAt ℝ ⊤ (fun t => rFun b t - rFun b x) x :=
    ((rFun_contDiff hb).sub contDiff_const).contDiffAt
  have hx0 : rFun b x - rFun b x = 0 := sub_self _
  have hval := (iteratedDeriv_pow_vanish hh hx0 (m + 1)).2.2 (by omega)
  rw [hval]
  have hd1 : deriv (fun t => rFun b t - rFun b x) x = x / rFun b x := by
    rw [deriv_sub_const, rFun_deriv hb x]
  have hd2 : iteratedDeriv 2 (fun t => rFun b t - rFun b x) x = b ^ 2 / rFun b x ^ 3 := by
    have hsub : deriv (fun t => rFun b t - rFun b x) = deriv (rFun b) :=
      funext fun t => deriv_sub_const _
    calc iteratedDeriv 2 (fun t => rFun b t - rFun b x) x
        = deriv (deriv (fun t => rFun b t - rFun b x)) x := by rw [iteratedDeriv_succ, iteratedDeriv_one]
      _ = deriv (deriv (rFun b)) x := by rw [hsub]
      _ = iteratedDeriv 2 (rFun b) x := by rw [iteratedDeriv_succ, iteratedDeriv_one]
      _ = b ^ 2 / rFun b x ^ 3 := rFun_second_deriv hb x
  rw [hd1, hd2]
  simp only [Nat.add_sub_cancel]
  have hf : ((m + 1).factorial : ℝ) ≠ 0 := by positivity
  field_simp [hf]
  push_cast
  ring

lemma kernelF_base {b x s : ℝ} (hb : 0 < b) : kernelF 2 b x s = kernelG 0 b x s := by
  unfold kernelF kernelG
  rw [show (2 : ℕ) - 1 = 1 from rfl]
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one,
    Nat.zero_div, Finset.range_one, Finset.sum_singleton, pow_zero, mul_one, mul_zero, zero_add,
    Nat.sub_self]
  have hcat : catCoeff 0 0 = 1 := by
    unfold catCoeff
    rw [if_pos (by omega)]
    norm_num
  rw [hcat, mul_one]
  have hsub : deriv (fun t => rFun b t - s) = deriv (rFun b) := funext fun t => deriv_sub_const _
  calc iteratedDeriv 2 (fun t => rFun b t - s) x
      = deriv (deriv (fun t => rFun b t - s)) x := by rw [iteratedDeriv_succ, iteratedDeriv_one]
    _ = deriv (deriv (rFun b)) x := by rw [hsub]
    _ = iteratedDeriv 2 (rFun b) x := by rw [iteratedDeriv_succ, iteratedDeriv_one]
    _ = b ^ 2 / rFun b x ^ 3 := rFun_second_deriv hb x

lemma kernelF_hasDerivAt_s {m : ℕ} {b x : ℝ} (hb : 0 < b) (s : ℝ) :
    HasDerivAt (fun u => kernelF (m + 3) b x u) (-deriv (fun t => kernelF (m + 2) b t s) x) s := by
  -- Expand `(rFun b t - u) ^ (m + 2)` by binomial theorem so `u` is outside `iteratedDeriv`!
  have hexp : ∀ (k : ℕ) (t u : ℝ),
      (rFun b t - u) ^ k = ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * (-u) ^ i * (rFun b t) ^ (k - i) := by
    intro k t u
    rw [sub_eq_add_neg, add_comm, add_pow]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hF_bin : ∀ (k : ℕ) (t u : ℝ),
      kernelF (k + 1) b t u =
        (∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * (-u) ^ i * iteratedDeriv (k + 1) (fun z => (rFun b z) ^ (k - i)) t) /
          (k.factorial : ℝ) := by
    intro k t u
    unfold kernelF
    simp only [Nat.add_sub_cancel]
    congr 1
    have hfun : (fun z => (rFun b z - u) ^ k) =
        fun z => ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (-u) ^ i * (rFun b z) ^ (k - i) :=
      funext fun z => hexp k z u
    rw [hfun, iteratedDeriv_fun_sum (fun i _ => by
      exact (contDiff_const.mul ((rFun_contDiff hb).pow (k - i))).contDiffAt.of_le (by simp))]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact iteratedDeriv_const_mul_real (k + 1) ((k.choose i : ℝ) * (-u) ^ i)
      (fun z => (rFun b z) ^ (k - i)) t
  have hfun_s : (fun u => kernelF (m + 3) b x u) =
      fun u => (∑ i ∈ Finset.range (m + 3),
        ((m + 2).choose i : ℝ) * (-u) ^ i *
          iteratedDeriv (m + 3) (fun z => (rFun b z) ^ (m + 2 - i)) x) / ((m + 2).factorial : ℝ) :=
    funext fun u => hF_bin (m + 2) x u
  rw [hfun_s]
  have hd_term : ∀ i ∈ Finset.range (m + 3),
      HasDerivAt (fun u : ℝ => ((m + 2).choose i : ℝ) * (-u) ^ i *
        iteratedDeriv (m + 3) (fun z => (rFun b z) ^ (m + 2 - i)) x)
        (-(((m + 2).choose i : ℝ) * (i : ℝ) * (-s) ^ (i - 1) *
          iteratedDeriv (m + 3) (fun z => (rFun b z) ^ (m + 2 - i)) x)) s := by
    intro i _
    cases i with
    | zero =>
      simpa using hasDerivAt_const s _
    | succ i' =>
      have h1 : HasDerivAt (fun u : ℝ => -u) (-1) s := (hasDerivAt_id s).neg
      have h2 := ((h1.pow (i' + 1)).const_mul ((m + 2).choose (i' + 1) : ℝ)).mul_const
        (iteratedDeriv (m + 3) (fun z => (rFun b z) ^ (m + 2 - (i' + 1))) x)
      refine h2.congr_deriv ?_
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      ring
  have hd_sum := (HasDerivAt.fun_sum hd_term).div_const ((m + 2).factorial : ℝ)
  refine hd_sum.congr_deriv ?_
  -- Now compute `-deriv (fun t => kernelF (m + 2) b t s) x`
  have hfun_t : (fun t => kernelF (m + 2) b t s) =
      fun t => (∑ i ∈ Finset.range (m + 2),
        ((m + 1).choose i : ℝ) * (-s) ^ i *
          iteratedDeriv (m + 2) (fun z => (rFun b z) ^ (m + 1 - i)) t) / ((m + 1).factorial : ℝ) :=
    funext fun t => hF_bin (m + 1) t s
  rw [hfun_t]
  have hd_t : HasDerivAt (fun t => (∑ i ∈ Finset.range (m + 2),
        ((m + 1).choose i : ℝ) * (-s) ^ i *
          iteratedDeriv (m + 2) (fun z => (rFun b z) ^ (m + 1 - i)) t) / ((m + 1).factorial : ℝ))
      ((∑ i ∈ Finset.range (m + 2),
        ((m + 1).choose i : ℝ) * (-s) ^ i *
          iteratedDeriv (m + 3) (fun z => (rFun b z) ^ (m + 1 - i)) x) / ((m + 1).factorial : ℝ)) x := by
    refine (HasDerivAt.fun_sum fun i _ => ?_).div_const _
    have hdiff : HasDerivAt (iteratedDeriv (m + 2) (fun z => (rFun b z) ^ (m + 1 - i)))
        (iteratedDeriv (m + 3) (fun z => (rFun b z) ^ (m + 1 - i)) x) x := by
      rw [iteratedDeriv_succ (n := m + 2)]
      exact (contDiffAt_iteratedDeriv_top ((rFun_contDiff hb).pow (m + 1 - i)).contDiffAt (m + 2)).differentiableAt (by simp) |>.hasDerivAt
    exact hdiff.const_mul _
  rw [hd_t.deriv]
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, mul_zero, zero_mul, neg_zero, add_zero, Nat.add_sub_cancel,
    Finset.sum_neg_distrib, neg_div]
  congr 1
  rw [Nat.factorial_succ, Nat.cast_mul, ← div_div]
  congr 1
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hch : ((m + 2).choose (i + 1) : ℝ) * ((i + 1 : ℕ) : ℝ) =
      ((m + 2 : ℕ) : ℝ) * ((m + 1).choose i : ℝ) := by
    have := Nat.add_one_mul_choose_eq (m + 1) i
    have h1 : (m + 2).choose (i + 1) * (i + 1) = (m + 2) * (m + 1).choose i := by
      linarith [Nat.choose_succ_right_eq (m + 1) i, this]
    exact_mod_cast h1
  have hm2 : ((m + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hsub : m + 2 - (i + 1) = m + 1 - i := by omega
  rw [hsub, show ((m + 1 + 1 : ℕ) : ℝ) = ((m + 2 : ℕ) : ℝ) by rfl]
  field_simp [hm2]
  calc ((m + 2).choose (i + 1) : ℝ) * ((i + 1 : ℕ) : ℝ) * (-s) ^ i *
        iteratedDeriv (m + 3) (fun z => rFun b z ^ (m + 1 - i)) x
      = (((m + 2 : ℕ) : ℝ) * ((m + 1).choose i : ℝ)) * (-s) ^ i *
        iteratedDeriv (m + 3) (fun z => rFun b z ^ (m + 1 - i)) x := by rw [hch]
    _ = _ := by ring

lemma catCoeff_step_A {m j : ℕ} (h2j : 2 * j ≤ m) :
    catCoeff (m + 1) j * ((m + 1 - 2 * j : ℕ) : ℝ) = catCoeff m j * (m + 3 : ℝ) := by
  have h2j1 : 2 * j ≤ m + 1 := by omega
  unfold catCoeff
  rw [if_pos h2j1, if_pos h2j]
  have hsub : m + 1 - 2 * j = (m - 2 * j) + 1 := by omega
  rw [hsub, Nat.factorial_succ (m + 2), Nat.factorial_succ (m - 2 * j)]
  push_cast
  have h1 : (((m - 2 * j : ℕ) : ℝ) + 1) ≠ 0 := by positivity
  have h2 : (4 : ℝ) ^ j ≠ 0 := by positivity
  have h3 : (j.factorial : ℝ) ≠ 0 := by positivity
  have h4 : ((j + 1).factorial : ℝ) ≠ 0 := by positivity
  have h5 : ((m - 2 * j).factorial : ℝ) ≠ 0 := by positivity
  field_simp [h1, h2, h3, h4, h5]
  ring

lemma catCoeff_step_B_int {m j : ℕ} (h2j2 : 2 * (j + 1) ≤ m) :
    catCoeff (m + 1) (j + 1) * (2 * ((j + 1 : ℕ) : ℝ)) =
      catCoeff m j * ((m - 2 * j : ℕ) : ℝ) +
        catCoeff m (j + 1) * (2 * ((j + 1 : ℕ) : ℝ)) := by
  obtain ⟨r, rfl⟩ : ∃ r : ℕ, m = r + 2 * j + 2 := ⟨m - 2 * (j + 1), by omega⟩
  have h2j1 : 2 * (j + 1) ≤ r + 2 * j + 2 + 1 := by omega
  have h2j : 2 * j ≤ r + 2 * j + 2 := by omega
  unfold catCoeff
  rw [if_pos h2j1, if_pos h2j, if_pos h2j2]
  rw [show r + 2 * j + 2 + 1 - 2 * (j + 1) = r + 1 by omega,
    show r + 2 * j + 2 - 2 * j = r + 2 by omega,
    show r + 2 * j + 2 - 2 * (j + 1) = r by omega]
  rw [Nat.factorial_succ (r + 2 * j + 2 + 2),
    Nat.factorial_succ (r + 1), Nat.factorial_succ r,
    Nat.factorial_succ (j + 1), Nat.factorial_succ j, pow_succ]
  push_cast
  have h1 : (4 : ℝ) ^ j ≠ 0 := by positivity
  have h2 : (j.factorial : ℝ) ≠ 0 := by positivity
  have h3 : (r.factorial : ℝ) ≠ 0 := by positivity
  have h4 : ((j : ℝ) + 1) ≠ 0 := by positivity
  have h5 : ((j : ℝ) + 2) ≠ 0 := by positivity
  have h6 : ((r : ℝ) + 1) ≠ 0 := by positivity
  have h7 : ((r : ℝ) + 2) ≠ 0 := by positivity
  field_simp [h1, h2, h3, h4, h5, h6, h7]
  ring

lemma catCoeff_step_B_bdry {m j : ℕ} (h2j1 : 2 * (j + 1) ≤ m + 1) (h2j2 : ¬ 2 * (j + 1) ≤ m) :
    catCoeff (m + 1) (j + 1) * (2 * ((j + 1 : ℕ) : ℝ)) =
      catCoeff m j * ((m - 2 * j : ℕ) : ℝ) := by
  have h2j : 2 * j ≤ m := by omega
  have hm_eq : m - 2 * j = 1 := by omega
  have h0 : m + 1 - 2 * (j + 1) = 0 := by omega
  unfold catCoeff
  rw [if_pos h2j1, if_pos h2j, h0, hm_eq, Nat.factorial_succ (m + 2),
    Nat.factorial_succ (j + 1), Nat.factorial_succ j, pow_succ]
  simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, mul_one]
  push_cast
  have hm_val : (m : ℝ) = 2 * (j : ℝ) + 1 := by exact_mod_cast (show m = 2 * j + 1 by omega)
  have h1 : (4 : ℝ) ^ j ≠ 0 := by positivity
  have h2 : (j.factorial : ℝ) ≠ 0 := by positivity
  have h4 : ((j : ℝ) + 1) ≠ 0 := by positivity
  have h5 : ((j : ℝ) + 2) ≠ 0 := by positivity
  field_simp [h1, h2, h4, h5]
  rw [hm_val]
  ring

/-- Core algebraic PDE: `∂/∂s G_{m+1}(b, x, s) = -∂/∂x G_m(b, x, s)`. -/
lemma kernelG_pde (m : ℕ) {b : ℝ} (hb : 0 < b) (x s : ℝ) :
    HasDerivAt (fun u => kernelG (m + 1) b x u)
      (-deriv (fun t => kernelG m b t s) x) s := by
  have hr_pos : 0 < rFun b x := rFun_pos hb x
  have hr_ne : rFun b x ≠ 0 := hr_pos.ne'
  have hr_sq : rFun b x ^ 2 = x ^ 2 + b ^ 2 := rFun_sq hb x
  -- First compute HasDerivAt wrt u of kernelG (m + 1) b x u
  let dsTerm : ℕ → ℝ := fun j =>
    catCoeff (m + 1) j *
      (((m + 1 - 2 * j : ℕ) : ℝ) * x * (x * s) ^ (m - 2 * j) * (b ^ 2 * (rFun b x ^ 2 - s ^ 2)) ^ j +
        (x * s) ^ (m + 1 - 2 * j) * ((j : ℝ) * (b ^ 2 * (rFun b x ^ 2 - s ^ 2)) ^ (j - 1) * (-2 * b ^ 2 * s)))
  have hds : HasDerivAt (fun u => kernelG (m + 1) b x u)
      (b ^ 2 / rFun b x ^ (2 * (m + 1) + 3) * ∑ j ∈ Finset.range ((m + 1) / 2 + 1), dsTerm j) s := by
    unfold kernelG
    refine (HasDerivAt.fun_sum fun j hj => ?_).const_mul _
    have h2j : 2 * j ≤ m + 1 := by
      have := Finset.mem_range.mp hj; omega
    have h1 : HasDerivAt (fun u : ℝ => (x * u) ^ (m + 1 - 2 * j))
        (((m + 1 - 2 * j : ℕ) : ℝ) * (x * s) ^ (m + 1 - 2 * j - 1) * x) s := by
      have hx : HasDerivAt (fun u : ℝ => x * u) x s := by simpa using (hasDerivAt_id s).const_mul x
      exact hx.pow (m + 1 - 2 * j)
    have h2 : HasDerivAt (fun u : ℝ => (b ^ 2 * (rFun b x ^ 2 - u ^ 2)) ^ j)
        ((j : ℝ) * (b ^ 2 * (rFun b x ^ 2 - s ^ 2)) ^ (j - 1) * (-2 * b ^ 2 * s)) s := by
      have hu : HasDerivAt (fun u : ℝ => b ^ 2 * (rFun b x ^ 2 - u ^ 2)) (-2 * b ^ 2 * s) s := by
        have := ((hasDerivAt_pow 2 s).const_sub (rFun b x ^ 2)).const_mul (b ^ 2)
        refine this.congr_deriv ?_; ring
      exact hu.pow j
    have hmul : HasDerivAt
        (fun u : ℝ => catCoeff (m + 1) j * (x * u) ^ (m + 1 - 2 * j) * (b ^ 2 * (rFun b x ^ 2 - u ^ 2)) ^ j)
        (dsTerm j) s := by
      have hm := (h1.const_mul (catCoeff (m + 1) j)).fun_mul h2
      refine hm.congr_deriv ?_
      dsimp only [dsTerm]
      by_cases hlast : m + 1 - 2 * j = 0
      · rw [hlast]; simp
      · have hexp : m + 1 - 2 * j - 1 = m - 2 * j := by omega
        rw [hexp]; ring
    exact hmul
  -- Next compute HasDerivAt wrt t of kernelG m b t s at x
  let dxTerm : ℕ → ℝ := fun j =>
    catCoeff m j *
      (((2 * m + 3 : ℝ) * x * (x * s) ^ (m - 2 * j) * (b ^ 2 * (rFun b x ^ 2 - s ^ 2)) ^ j) -
       rFun b x ^ 2 *
        (((m - 2 * j : ℕ) : ℝ) * s * (x * s) ^ (m - 2 * j - 1) * (b ^ 2 * (rFun b x ^ 2 - s ^ 2)) ^ j +
          (x * s) ^ (m - 2 * j) * ((j : ℝ) * (b ^ 2 * (rFun b x ^ 2 - s ^ 2)) ^ (j - 1) * (2 * b ^ 2 * x))))
  have hdx : HasDerivAt (fun t => kernelG m b t s)
      (-(b ^ 2 / rFun b x ^ (2 * m + 5) * ∑ j ∈ Finset.range (m / 2 + 1), dxTerm j)) x := by
    unfold kernelG
    have hfac : HasDerivAt (fun t => b ^ 2 / rFun b t ^ (2 * m + 3))
        (-(2 * m + 3 : ℝ) * b ^ 2 * x / rFun b x ^ (2 * m + 5)) x := by
      have hp := (rFun_hasDerivAt hb x).pow (2 * m + 3)
      have hdiv := (hasDerivAt_const x (b ^ 2)).fun_div hp (pow_ne_zero _ hr_ne)
      refine hdiv.congr_deriv ?_
      simp only [Pi.pow_apply]
      have hpow : rFun b x ^ (2 * m + 5) = rFun b x ^ (2 * m + 3) * rFun b x ^ 2 := by ring
      have hpow2 : rFun b x ^ (2 * m + 3) = rFun b x ^ (2 * m + 2) * rFun b x := by ring
      rw [show 2 * m + 3 - 1 = 2 * m + 2 by omega, hpow, hpow2]
      push_cast
      field_simp [hr_ne]
      ring
    have hsum : HasDerivAt
        (fun t => ∑ j ∈ Finset.range (m / 2 + 1),
          catCoeff m j * (t * s) ^ (m - 2 * j) * (b ^ 2 * (rFun b t ^ 2 - s ^ 2)) ^ j)
        (∑ j ∈ Finset.range (m / 2 + 1),
          catCoeff m j *
            (((m - 2 * j : ℕ) : ℝ) * s * (x * s) ^ (m - 2 * j - 1) * (b ^ 2 * (rFun b x ^ 2 - s ^ 2)) ^ j +
              (x * s) ^ (m - 2 * j) * ((j : ℝ) * (b ^ 2 * (rFun b x ^ 2 - s ^ 2)) ^ (j - 1) * (2 * b ^ 2 * x)))) x := by
      refine HasDerivAt.fun_sum fun j _ => ?_
      have h1 : HasDerivAt (fun t : ℝ => (t * s) ^ (m - 2 * j))
          (((m - 2 * j : ℕ) : ℝ) * (x * s) ^ (m - 2 * j - 1) * s) x := by
        have h0 : HasDerivAt (fun t : ℝ => t * s) s x := by simpa using (hasDerivAt_id x).mul_const s
        exact h0.pow (m - 2 * j)
      have h2 : HasDerivAt (fun t : ℝ => (b ^ 2 * (rFun b t ^ 2 - s ^ 2)) ^ j)
          ((j : ℝ) * (b ^ 2 * (rFun b x ^ 2 - s ^ 2)) ^ (j - 1) * (2 * b ^ 2 * x)) x := by
        have ht : (fun t : ℝ => (b ^ 2 * (rFun b t ^ 2 - s ^ 2)) ^ j) =
            fun t => (b ^ 2 * (t ^ 2 + b ^ 2 - s ^ 2)) ^ j :=
          funext fun t => by rw [rFun_sq hb t]
        rw [ht]
        have hd : HasDerivAt (fun t : ℝ => b ^ 2 * (t ^ 2 + b ^ 2 - s ^ 2)) (2 * b ^ 2 * x) x := by
          have := (((hasDerivAt_pow 2 x).add_const (b ^ 2)).sub_const (s ^ 2)).const_mul (b ^ 2)
          refine this.congr_deriv ?_; ring
        refine (hd.pow j).congr_deriv ?_
        rw [rFun_sq hb x]
      have hmul := (h1.const_mul (catCoeff m j)).fun_mul h2
      refine hmul.congr_deriv ?_; ring
    have hprod := hfac.fun_mul hsum
    refine hprod.congr_deriv ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only [dxTerm]
    have hpow : rFun b x ^ (2 * m + 5) = rFun b x ^ (2 * m + 3) * rFun b x ^ 2 := by ring
    rw [hpow]
    field_simp [hr_ne]
    ring
  -- Now prove the algebraic sum identity: ∑_{j < (m+1)/2+1} dsTerm j = ∑_{j < m/2+1} dxTerm j
  refine hds.congr_deriv ?_
  rw [hdx.deriv, neg_neg]
  have hexp_eq : 2 * (m + 1) + 3 = 2 * m + 5 := by omega
  rw [hexp_eq]
  congr 1
  -- Extend both sums to `N := m + 2` (since `catCoeff` vanishes for `2 * j > m` / `m + 1`)!
  let N := m + 2
  have hsum_ds : ∑ j ∈ Finset.range ((m + 1) / 2 + 1), dsTerm j = ∑ j ∈ Finset.range N, dsTerm j := by
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun j _ hnot => ?_
    have hgt : ¬ (2 * j ≤ m + 1) := by
      have := Finset.mem_range.not.mp hnot; omega
    simp [dsTerm, catCoeff, hgt]
  have hsum_dx : ∑ j ∈ Finset.range (m / 2 + 1), dxTerm j = ∑ j ∈ Finset.range N, dxTerm j := by
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun j _ hnot => ?_
    have hgt : ¬ (2 * j ≤ m) := by
      have := Finset.mem_range.not.mp hnot; omega
    simp [dxTerm, catCoeff, hgt]
  rw [hsum_ds, hsum_dx]
  -- Split `dsTerm j` into `A_j - B_j` and shift `B_{j+1}`!
  set W := b ^ 2 * (rFun b x ^ 2 - s ^ 2)
  let A : ℕ → ℝ := fun j =>
    catCoeff (m + 1) j * ((m + 1 - 2 * j : ℕ) : ℝ) * x * (x * s) ^ (m - 2 * j) * W ^ j
  let B : ℕ → ℝ := fun j =>
    catCoeff (m + 1) j * (2 * (j : ℝ)) * b ^ 2 * s * (x * s) ^ (m + 1 - 2 * j) * W ^ (j - 1)
  have hds_split : ∀ j, dsTerm j = A j - B j := fun j => by
    dsimp only [dsTerm, A, B, W]; ring
  rw [Finset.sum_congr rfl (fun j _ => hds_split j), Finset.sum_sub_distrib]
  have hB0 : B 0 = 0 := by simp [B]
  have hBN : B N = 0 := by
    have : ¬ (2 * N ≤ m + 1) := by dsimp [N]; omega
    simp [B, catCoeff, this]
  have hB_shift : ∑ j ∈ Finset.range N, B j = ∑ j ∈ Finset.range N, B (j + 1) := by
    have h1 := Finset.sum_range_succ B N
    have h2 := Finset.sum_range_succ' B N
    rw [hBN, add_zero] at h1
    rw [hB0, add_zero] at h2
    linarith
  rw [hB_shift, ← Finset.sum_sub_distrib]
  -- Similarly split `dxTerm j` using `rFun b x ^ 2 = x ^ 2 + b ^ 2` and `b ^ 2 * rFun b x ^ 2 = W + b ^ 2 * s ^ 2`!
  let P : ℕ → ℝ := fun j =>
    catCoeff m j * ((m + 3 : ℝ) * x * (x * s) ^ (m - 2 * j) * W ^ j)
  let Q : ℕ → ℝ := fun j =>
    catCoeff m j * ((m - 2 * j : ℕ) : ℝ) * b ^ 2 * s * (x * s) ^ (m - 2 * j - 1) * W ^ j
  let R : ℕ → ℝ := fun j =>
    catCoeff m j * (2 * (j : ℝ)) * b ^ 2 * s ^ 2 * x * (x * s) ^ (m - 2 * j) * W ^ (j - 1)
  have hdx_split : ∀ j ∈ Finset.range N, dxTerm j = P j - Q j - R j := by
    intro j _
    by_cases h2j : 2 * j ≤ m
    · dsimp only [dxTerm, P, Q, R, W]
      have hterm1 :
          rFun b x ^ 2 * (((m - 2 * j : ℕ) : ℝ) * s * (x * s) ^ (m - 2 * j - 1)) =
            ((m - 2 * j : ℕ) : ℝ) * x * (x * s) ^ (m - 2 * j) +
              ((m - 2 * j : ℕ) : ℝ) * b ^ 2 * s * (x * s) ^ (m - 2 * j - 1) := by
        rw [hr_sq]
        by_cases hm0 : m - 2 * j = 0
        · rw [hm0]; simp
        · have hpow : (x * s) ^ (m - 2 * j) = x * s * (x * s) ^ (m - 2 * j - 1) := by
            conv_lhs => rw [show m - 2 * j = (m - 2 * j - 1) + 1 by omega, pow_succ]
            ring
          rw [hpow]; ring
      have hterm2 :
          rFun b x ^ 2 * ((x * s) ^ (m - 2 * j) * ((j : ℝ) * (b ^ 2 * (rFun b x ^ 2 - s ^ 2)) ^ (j - 1) * (2 * b ^ 2 * x))) =
            (2 * (j : ℝ)) * x * (x * s) ^ (m - 2 * j) * (b ^ 2 * (rFun b x ^ 2 - s ^ 2)) ^ j +
              (2 * (j : ℝ)) * b ^ 2 * s ^ 2 * x * (x * s) ^ (m - 2 * j) * (b ^ 2 * (rFun b x ^ 2 - s ^ 2)) ^ (j - 1) := by
        cases j with
        | zero => simp
        | succ j' =>
          simp only [Nat.add_sub_cancel]
          have hpow : (b ^ 2 * (rFun b x ^ 2 - s ^ 2)) ^ (j' + 1) =
              (b ^ 2 * (rFun b x ^ 2 - s ^ 2)) * (b ^ 2 * (rFun b x ^ 2 - s ^ 2)) ^ j' := by
            rw [pow_succ]; ring
          rw [hpow]; ring
      have hcoeff : ((2 * m + 3 : ℝ) - ((m - 2 * j : ℕ) : ℝ) - 2 * (j : ℝ)) = (m + 3 : ℝ) := by
        have hsub : ((m - 2 * j : ℕ) : ℝ) = (m : ℝ) - 2 * (j : ℝ) := by
          rw [Nat.cast_sub h2j]; push_cast; ring
        linarith
      calc catCoeff m j *
            ((2 * m + 3 : ℝ) * x * (x * s) ^ (m - 2 * j) * (b ^ 2 * (rFun b x ^ 2 - s ^ 2)) ^ j -
              rFun b x ^ 2 * (((m - 2 * j : ℕ) : ℝ) * s * (x * s) ^ (m - 2 * j - 1) * (b ^ 2 * (rFun b x ^ 2 - s ^ 2)) ^ j +
                (x * s) ^ (m - 2 * j) * ((j : ℝ) * (b ^ 2 * (rFun b x ^ 2 - s ^ 2)) ^ (j - 1) * (2 * b ^ 2 * x))))
          = catCoeff m j *
            ((2 * m + 3 : ℝ) * x * (x * s) ^ (m - 2 * j) * (b ^ 2 * (rFun b x ^ 2 - s ^ 2)) ^ j -
              (rFun b x ^ 2 * (((m - 2 * j : ℕ) : ℝ) * s * (x * s) ^ (m - 2 * j - 1))) * (b ^ 2 * (rFun b x ^ 2 - s ^ 2)) ^ j -
              rFun b x ^ 2 * ((x * s) ^ (m - 2 * j) * ((j : ℝ) * (b ^ 2 * (rFun b x ^ 2 - s ^ 2)) ^ (j - 1) * (2 * b ^ 2 * x)))) := by ring
        _ = catCoeff m j * (((2 * m + 3 : ℝ) - ((m - 2 * j : ℕ) : ℝ) - 2 * (j : ℝ)) *
              x * (x * s) ^ (m - 2 * j) * (b ^ 2 * (rFun b x ^ 2 - s ^ 2)) ^ j) -
            catCoeff m j * ((m - 2 * j : ℕ) : ℝ) * b ^ 2 * s * (x * s) ^ (m - 2 * j - 1) * (b ^ 2 * (rFun b x ^ 2 - s ^ 2)) ^ j -
            catCoeff m j * (2 * (j : ℝ)) * b ^ 2 * s ^ 2 * x * (x * s) ^ (m - 2 * j) * (b ^ 2 * (rFun b x ^ 2 - s ^ 2)) ^ (j - 1) := by
              rw [hterm1, hterm2]; ring
        _ = _ := by rw [hcoeff]
    · simp [dxTerm, P, Q, R, catCoeff, h2j]
  rw [Finset.sum_congr rfl hdx_split, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hR0 : R 0 = 0 := by simp [R]
  have hRN : R N = 0 := by
    have : ¬ (2 * N ≤ m) := by dsimp [N]; omega
    simp [R, catCoeff, this]
  have hR_shift : ∑ j ∈ Finset.range N, R j = ∑ j ∈ Finset.range N, R (j + 1) := by
    have h1 := Finset.sum_range_succ R N
    have h2 := Finset.sum_range_succ' R N
    rw [hRN, add_zero] at h1
    rw [hR0, add_zero] at h2
    linarith
  rw [hR_shift, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  -- Match term-by-term: `A j = P j` AND `B (j + 1) = Q j + R (j + 1)`!
  refine Finset.sum_congr rfl fun j _ => ?_
  have hAP : A j = P j := by
    dsimp only [A, P]
    by_cases h2j : 2 * j ≤ m
    · have hcat := catCoeff_step_A h2j
      calc catCoeff (m + 1) j * ↑(m + 1 - 2 * j) * x * (x * s) ^ (m - 2 * j) * W ^ j
          = (catCoeff (m + 1) j * ↑(m + 1 - 2 * j)) * (x * (x * s) ^ (m - 2 * j) * W ^ j) := by ring
        _ = (catCoeff m j * (m + 3 : ℝ)) * (x * (x * s) ^ (m - 2 * j) * W ^ j) := by rw [hcat]
        _ = _ := by ring
    · by_cases h2j1 : 2 * j ≤ m + 1
      · have h0 : m + 1 - 2 * j = 0 := by omega
        simp [catCoeff, h2j, h0]
      · simp [catCoeff, h2j, h2j1]
  have hBQR : B (j + 1) = Q j + R (j + 1) := by
    dsimp only [B, Q, R]
    simp only [Nat.add_sub_cancel]
    by_cases h2j1 : 2 * (j + 1) ≤ m + 1
    · have hsub1 : m + 1 - 2 * (j + 1) = m - 2 * j - 1 := by omega
      rw [hsub1]
      by_cases h2j2 : 2 * (j + 1) ≤ m
      · have hpow : s * (x * s) ^ (m - 2 * j - 1) = s ^ 2 * x * (x * s) ^ (m - 2 * (j + 1)) := by
          have hexp : m - 2 * j - 1 = (m - 2 * (j + 1)) + 1 := by omega
          rw [hexp, pow_succ]; ring
        have hcat_id := catCoeff_step_B_int h2j2
        calc catCoeff (m + 1) (j + 1) * (2 * ↑(j + 1)) * b ^ 2 * s * (x * s) ^ (m - 2 * j - 1) * W ^ j
            = (catCoeff (m + 1) (j + 1) * (2 * ↑(j + 1))) * (b ^ 2 * s * (x * s) ^ (m - 2 * j - 1) * W ^ j) := by ring
          _ = (catCoeff m j * ↑(m - 2 * j) + catCoeff m (j + 1) * (2 * ↑(j + 1))) *
                (b ^ 2 * s * (x * s) ^ (m - 2 * j - 1) * W ^ j) := by rw [hcat_id]
          _ = catCoeff m j * ↑(m - 2 * j) * b ^ 2 * s * (x * s) ^ (m - 2 * j - 1) * W ^ j +
              catCoeff m (j + 1) * (2 * ↑(j + 1)) * b ^ 2 * (s * (x * s) ^ (m - 2 * j - 1)) * W ^ j := by ring
          _ = _ := by rw [hpow]; ring
      · have hcat_r : catCoeff m (j + 1) = 0 := by unfold catCoeff; rw [if_neg h2j2]
        rw [hcat_r, zero_mul, zero_mul, zero_mul, zero_mul, zero_mul, zero_mul, add_zero]
        have hcat_id := catCoeff_step_B_bdry h2j1 h2j2
        calc catCoeff (m + 1) (j + 1) * (2 * ↑(j + 1)) * b ^ 2 * s * (x * s) ^ (m - 2 * j - 1) * W ^ j
            = (catCoeff (m + 1) (j + 1) * (2 * ↑(j + 1))) * (b ^ 2 * s * (x * s) ^ (m - 2 * j - 1) * W ^ j) := by ring
          _ = (catCoeff m j * ↑(m - 2 * j)) * (b ^ 2 * s * (x * s) ^ (m - 2 * j - 1) * W ^ j) := by rw [hcat_id]
          _ = _ := by ring
    · have hcat_b : catCoeff (m + 1) (j + 1) = 0 := by unfold catCoeff; rw [if_neg h2j1]
      have hcat_r : catCoeff m (j + 1) = 0 := by unfold catCoeff; rw [if_neg (by omega)]
      rw [hcat_b, hcat_r]
      by_cases h2j : 2 * j ≤ m
      · have h0 : m - 2 * j = 0 := by omega
        rw [h0]; simp
      · have hcat_q : catCoeff m j = 0 := by unfold catCoeff; rw [if_neg h2j]
        rw [hcat_q]; simp
  linarith

lemma kernelF_eq_kernelG : ∀ (m : ℕ) {b : ℝ}, 0 < b → ∀ x s : ℝ,
    kernelF (m + 2) b x s = kernelG m b x s := by
  intro m
  induction m with
  | zero => intro b hb x s; exact kernelF_base hb
  | succ m ih =>
    intro b hb x s
    have hdiff_zero : ∀ u : ℝ, HasDerivAt (fun w => kernelF (m + 3) b x w - kernelG (m + 1) b x w) 0 u := by
      intro u
      have h1 := kernelF_hasDerivAt_s (m := m) (x := x) hb u
      have h2 := kernelG_pde m hb x u
      have heq_t : (fun t => kernelF (m + 2) b t u) = fun t => kernelG m b t u :=
        funext fun t => ih hb t u
      rw [heq_t] at h1
      simpa using h1.fun_sub h2
    have hconst := is_const_of_deriv_eq_zero
      (fun u => (hdiff_zero u).differentiableAt)
      (fun u => (hdiff_zero u).deriv) s (rFun b x)
    have hat_r : kernelF (m + 3) b x (rFun b x) - kernelG (m + 1) b x (rFun b x) = 0 := by
      rw [kernelF_at_r hb, kernelG_at_r hb, sub_self]
    linarith

/-!
## 5. Exact k-th derivative representation for radial slices and integral bound <= 1
-/

lemma iteratedDeriv_integral_radial {b R : ℝ} (hb : 0 < b) (_hR : b < R)
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Set.Icc 0 R)) :
    ∀ (k : ℕ), 1 ≤ k →
      ∀ (j : ℕ), j ≤ k →
        ∀ x : ℝ, rFun b x < R →
          iteratedDeriv j (fun t => ∫ s in (0 : ℝ)..rFun b t,
            (rFun b t - s) ^ (k - 1) / ((k - 1).factorial : ℝ) * φ s) x =
          (if j = k then (x / rFun b x) ^ k * φ (rFun b x) else 0) +
            ∫ s in (0 : ℝ)..rFun b x,
              (iteratedDeriv j (fun t => (rFun b t - s) ^ (k - 1)) x / ((k - 1).factorial : ℝ)) * φ s := by
  intro k hk j
  induction j with
  | zero =>
    intro _ x _
    simp [Nat.ne_of_lt (show 0 < k by omega)]
  | succ j ih =>
    intro hjk x hxr
    have hopen : IsOpen {t : ℝ | rFun b t < R} :=
      isOpen_lt (rFun_contDiff hb).continuous continuous_const
    have hmem_nhd : ∀ᶠ t in 𝓝 x, rFun b t < R := hopen.mem_nhds hxr
    rw [iteratedDeriv_succ]
    have hprev_eq :
        iteratedDeriv j (fun t => ∫ s in (0 : ℝ)..rFun b t,
          (rFun b t - s) ^ (k - 1) / ((k - 1).factorial : ℝ) * φ s) =ᶠ[𝓝 x]
        fun t => ∫ s in (0 : ℝ)..rFun b t,
          (iteratedDeriv j (fun z => (rFun b z - s) ^ (k - 1)) t / ((k - 1).factorial : ℝ)) * φ s := by
      filter_upwards [hmem_nhd] with t ht
      have hne : j ≠ k := by omega
      simpa [hne] using ih (by omega) t ht
    rw [hprev_eq.deriv_eq]
    -- Rewrite integrand via binomial expansion so `t` is completely outside the integral!
    have hexp : ∀ (t : ℝ), rFun b t < R →
        (∫ s in (0 : ℝ)..rFun b t,
          (iteratedDeriv j (fun z => (rFun b z - s) ^ (k - 1)) t / ((k - 1).factorial : ℝ)) * φ s) =
        (∑ i ∈ Finset.range k,
          (((k - 1).choose i : ℝ) * iteratedDeriv j (fun z => (rFun b z) ^ (k - 1 - i)) t) *
            (∫ s in (0 : ℝ)..rFun b t, (-s) ^ i * φ s)) / ((k - 1).factorial : ℝ) := by
      intro t ht
      have hbin : ∀ s : ℝ,
          (iteratedDeriv j (fun z => (rFun b z - s) ^ (k - 1)) t / ((k - 1).factorial : ℝ)) * φ s =
          (∑ i ∈ Finset.range k,
            (((k - 1).choose i : ℝ) * iteratedDeriv j (fun z => (rFun b z) ^ (k - 1 - i)) t) *
              ((-s) ^ i * φ s)) / ((k - 1).factorial : ℝ) := by
        intro s
        have hfun : (fun z => (rFun b z - s) ^ (k - 1)) =
            fun z => ∑ i ∈ Finset.range k,
              ((k - 1).choose i : ℝ) * (-s) ^ i * (rFun b z) ^ (k - 1 - i) := by
          funext z
          rw [sub_eq_add_neg, add_comm, add_pow, show k - 1 + 1 = k by omega]
          refine Finset.sum_congr rfl fun i _ => by ring
        rw [hfun, iteratedDeriv_fun_sum (fun i _ =>
          (contDiff_const.mul ((rFun_contDiff hb).pow (k - 1 - i))).contDiffAt.of_le (by simp))]
        rw [Finset.sum_div, Finset.sum_mul, Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [iteratedDeriv_const_mul_real]
        ring
      simp_rw [hbin]
      rw [intervalIntegral.integral_div, intervalIntegral.integral_finsetSum]
      · congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [intervalIntegral.integral_const_mul]
      · intro i _
        have hsub : Set.uIcc (0 : ℝ) (rFun b t) ⊆ Set.Icc 0 R := by
          rw [Set.uIcc_of_le (rFun_pos hb t).le]
          exact Set.Icc_subset_Icc_right ht.le
        exact (ContinuousOn.mul continuousOn_const
          ((by fun_prop : Continuous fun s : ℝ => (-s) ^ i).continuousOn.mul (hφ.mono hsub))).intervalIntegrable
    have hfun_eq :
        (fun t => ∫ s in (0 : ℝ)..rFun b t,
          (iteratedDeriv j (fun z => (rFun b z - s) ^ (k - 1)) t / ((k - 1).factorial : ℝ)) * φ s) =ᶠ[𝓝 x]
        fun t => (∑ i ∈ Finset.range k,
          (((k - 1).choose i : ℝ) * iteratedDeriv j (fun z => (rFun b z) ^ (k - 1 - i)) t) *
            (∫ s in (0 : ℝ)..rFun b t, (-s) ^ i * φ s)) / ((k - 1).factorial : ℝ) := by
      filter_upwards [hmem_nhd] with t ht using hexp t ht
    rw [hfun_eq.deriv_eq]
    have hderiv_each : ∀ i ∈ Finset.range k,
        HasDerivAt
          (fun t => (((k - 1).choose i : ℝ) * iteratedDeriv j (fun z => (rFun b z) ^ (k - 1 - i)) t) *
            (∫ s in (0 : ℝ)..rFun b t, (-s) ^ i * φ s))
          ((((k - 1).choose i : ℝ) * iteratedDeriv (j + 1) (fun z => (rFun b z) ^ (k - 1 - i)) x) *
            (∫ s in (0 : ℝ)..rFun b x, (-s) ^ i * φ s) +
          (((k - 1).choose i : ℝ) * iteratedDeriv j (fun z => (rFun b z) ^ (k - 1 - i)) x) *
            ((-rFun b x) ^ i * φ (rFun b x) * (x / rFun b x))) x := by
      intro i _
      have hd1 : HasDerivAt
          (fun t => ((k - 1).choose i : ℝ) * iteratedDeriv j (fun z => (rFun b z) ^ (k - 1 - i)) t)
          (((k - 1).choose i : ℝ) * iteratedDeriv (j + 1) (fun z => (rFun b z) ^ (k - 1 - i)) x) x := by
        rw [iteratedDeriv_succ]
        exact ((contDiffAt_iteratedDeriv_top ((rFun_contDiff hb).pow (k - 1 - i)).contDiffAt j).differentiableAt (by simp) |>.hasDerivAt).const_mul _
      have hd2 : HasDerivAt (fun t => ∫ s in (0 : ℝ)..rFun b t, (-s) ^ i * φ s)
          ((-rFun b x) ^ i * φ (rFun b x) * (x / rFun b x)) x := by
        have hr_mem : rFun b x ∈ Set.Ioo (0 : ℝ) R := ⟨rFun_pos hb x, hxr⟩
        have hcont_on : ContinuousOn (fun s : ℝ => (-s) ^ i * φ s) (Set.Ioo 0 R) :=
          (by fun_prop : Continuous fun s : ℝ => (-s) ^ i).continuousOn.mul (hφ.mono Set.Ioo_subset_Icc_self)
        have hcont_at : ContinuousAt (fun s : ℝ => (-s) ^ i * φ s) (rFun b x) :=
          hcont_on.continuousAt (isOpen_Ioo.mem_nhds hr_mem)
        have hint_at : IntervalIntegrable (fun s : ℝ => (-s) ^ i * φ s) volume 0 (rFun b x) := by
          have hsub : Set.uIcc (0 : ℝ) (rFun b x) ⊆ Set.Icc 0 R := by
            rw [Set.uIcc_of_le (rFun_pos hb x).le]; exact Set.Icc_subset_Icc_right hxr.le
          exact ((by fun_prop : Continuous fun s : ℝ => (-s) ^ i).continuousOn.mul (hφ.mono hsub)).intervalIntegrable
        have hftc := intervalIntegral.integral_hasDerivAt_right hint_at
          (hcont_on.stronglyMeasurableAtFilter isOpen_Ioo (rFun b x) hr_mem) hcont_at
        exact hftc.comp x (rFun_hasDerivAt hb x)
      exact hd1.fun_mul hd2
    have hderiv_all := (HasDerivAt.fun_sum hderiv_each).div_const ((k - 1).factorial : ℝ)
    rw [hderiv_all.deriv, Finset.sum_add_distrib, add_div, add_comm]
    congr 1
    · -- Boundary term: re-sums to `iteratedDeriv j (fun z => (rFun b z - rFun b x)^(k-1)) x / (k-1)! * (x / rFun b x) * φ (rFun b x)`
      have hbdry :
          (∑ i ∈ Finset.range k,
            (((k - 1).choose i : ℝ) * iteratedDeriv j (fun z => (rFun b z) ^ (k - 1 - i)) x) *
              ((-rFun b x) ^ i * φ (rFun b x) * (x / rFun b x))) / ((k - 1).factorial : ℝ) =
          (iteratedDeriv j (fun z => (rFun b z - rFun b x) ^ (k - 1)) x / ((k - 1).factorial : ℝ)) *
            (x / rFun b x) * φ (rFun b x) := by
        have hfun : (fun z => (rFun b z - rFun b x) ^ (k - 1)) =
            fun z => ∑ i ∈ Finset.range k,
              ((k - 1).choose i : ℝ) * (-rFun b x) ^ i * (rFun b z) ^ (k - 1 - i) := by
          funext z
          rw [sub_eq_add_neg, add_comm, add_pow, show k - 1 + 1 = k by omega]
          refine Finset.sum_congr rfl fun i _ => by ring
        rw [hfun, iteratedDeriv_fun_sum (fun i _ =>
          (contDiff_const.mul ((rFun_contDiff hb).pow (k - 1 - i))).contDiffAt.of_le (by simp))]
        rw [Finset.sum_div, Finset.sum_div, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [iteratedDeriv_const_mul_real]
        ring
      rw [hbdry]
      have hh : ContDiffAt ℝ ⊤ (fun z => rFun b z - rFun b x) x :=
        ((rFun_contDiff hb).sub contDiff_const).contDiffAt
      have hv := iteratedDeriv_pow_vanish hh (sub_self (rFun b x)) (k - 1)
      by_cases hjk_eq : j + 1 = k
      · rw [if_pos hjk_eq]
        have hj_eq : j = k - 1 := by omega
        rw [hj_eq, hv.2.1]
        have hd : deriv (fun z => rFun b z - rFun b x) x = x / rFun b x := by
          rw [deriv_sub_const, rFun_deriv hb x]
        rw [hd]
        have hf : ((k - 1).factorial : ℝ) ≠ 0 := by positivity
        field_simp [hf]
        have hpow : (x / rFun b x) ^ (k - 1) * (x / rFun b x) = (x / rFun b x) ^ k := by
          rw [← pow_succ, show k - 1 + 1 = k by omega]
        rw [← hpow]
        ring
      · rw [if_neg hjk_eq, hv.1 j (by omega)]
        simp
    · -- Interior term: re-sums to `∫ s in 0..rFun b x, iteratedDeriv (j+1) ... * φ s`
      have hbin : ∀ s : ℝ,
          (iteratedDeriv (j + 1) (fun z => (rFun b z - s) ^ (k - 1)) x / ((k - 1).factorial : ℝ)) * φ s =
          (∑ i ∈ Finset.range k,
            (((k - 1).choose i : ℝ) * iteratedDeriv (j + 1) (fun z => (rFun b z) ^ (k - 1 - i)) x) *
              ((-s) ^ i * φ s)) / ((k - 1).factorial : ℝ) := by
        intro s
        have hfun : (fun z => (rFun b z - s) ^ (k - 1)) =
            fun z => ∑ i ∈ Finset.range k,
              ((k - 1).choose i : ℝ) * (-s) ^ i * (rFun b z) ^ (k - 1 - i) := by
          funext z
          rw [sub_eq_add_neg, add_comm, add_pow, show k - 1 + 1 = k by omega]
          refine Finset.sum_congr rfl fun i _ => by ring
        rw [hfun, iteratedDeriv_fun_sum (fun i _ =>
          (contDiff_const.mul ((rFun_contDiff hb).pow (k - 1 - i))).contDiffAt.of_le (by simp))]
        rw [Finset.sum_div, Finset.sum_mul, Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [iteratedDeriv_const_mul_real]
        ring
      simp_rw [hbin]
      rw [intervalIntegral.integral_div, intervalIntegral.integral_finsetSum]
      · congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [intervalIntegral.integral_const_mul]
      · intro i _
        have hsub : Set.uIcc (0 : ℝ) (rFun b x) ⊆ Set.Icc 0 R := by
          rw [Set.uIcc_of_le (rFun_pos hb x).le]
          exact Set.Icc_subset_Icc_right hxr.le
        exact (ContinuousOn.mul continuousOn_const
          ((by fun_prop : Continuous fun s : ℝ => (-s) ^ i).continuousOn.mul (hφ.mono hsub))).intervalIntegrable

lemma weight_sum_le_one {k : ℕ} (hk : 2 ≤ k) {b : ℝ} (hb : 0 < b) {x : ℝ} (hx : 0 ≤ x) :
    (x / rFun b x) ^ k + ∫ s in (0 : ℝ)..rFun b x, kernelF k b x s ≤ 1 := by
  let H : ℝ → ℝ := fun t => iteratedDeriv k (fun z => rFun b z ^ k) t / (k.factorial : ℝ)
  have hH_eq : ∀ t : ℝ, H t = (t / rFun b t) ^ k + ∫ s in (0 : ℝ)..rFun b t, kernelF k b t s := by
    intro t
    have hR : rFun b t < rFun b t + 1 := by linarith
    have hbR : b < rFun b t + 1 := by
      have : b ≤ rFun b t := calc
        b = Real.sqrt (b ^ 2) := (Real.sqrt_sq hb.le).symm
        _ ≤ Real.sqrt (t ^ 2 + b ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      linarith
    have h1 := iteratedDeriv_integral_radial hb hbR (φ := fun _ => (1 : ℝ)) continuousOn_const
      k (by omega) k le_rfl t hR
    have hint_pow : (fun z => ∫ s in (0 : ℝ)..rFun b z,
        (rFun b z - s) ^ (k - 1) / ((k - 1).factorial : ℝ) * (1 : ℝ)) =
        fun z => rFun b z ^ k / (k.factorial : ℝ) := by
      funext z
      have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) (rFun b z),
          HasDerivAt (fun s => -((rFun b z - s) ^ k / (k.factorial : ℝ)))
            ((rFun b z - s) ^ (k - 1) / ((k - 1).factorial : ℝ) * 1) s := by
        intro s _
        have hs1 : HasDerivAt (fun s : ℝ => rFun b z - s) (-1) s := by
          simpa using (hasDerivAt_id s).const_sub (rFun b z)
        have hs := ((hs1.pow k).div_const (k.factorial : ℝ)).neg
        refine hs.congr_deriv ?_
        have hk1 : k = (k - 1) + 1 := by omega
        have hfac : (k.factorial : ℝ) = ((k - 1 : ℕ) + 1 : ℝ) * ((k - 1).factorial : ℝ) := by
          conv_lhs => rw [hk1, Nat.factorial_succ]
          push_cast; ring
        have hk_cast : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast hk1
        have h1' : (((k - 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
        have h2' : ((k - 1).factorial : ℝ) ≠ 0 := by positivity
        rw [hfac, hk_cast]
        field_simp [h1', h2']
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        ((by fun_prop : Continuous fun s => (rFun b z - s) ^ (k - 1) / ((k - 1).factorial : ℝ) * 1).intervalIntegrable 0 (rFun b z))
      rw [hftc, sub_self, zero_pow (by omega), zero_div, neg_zero, sub_zero, zero_sub, neg_neg]
    rw [hint_pow, if_pos rfl, mul_one] at h1
    simp only [mul_one] at h1
    have hdiv : iteratedDeriv k (fun z => rFun b z ^ k / (k.factorial : ℝ)) t = H t := by
      dsimp only [H]
      rw [show (fun z => rFun b z ^ k / (k.factorial : ℝ)) = fun z => ((k.factorial : ℝ))⁻¹ * rFun b z ^ k by
        funext z; ring]
      rw [iteratedDeriv_const_mul_real]
      ring
    rw [← hdiv, h1]
    rfl
  -- Monotonicity: `deriv H t = kernelF (k + 1) b t 0 = kernelG (k - 1) b t 0 >= 0` for `t >= 0`!
  have hH_deriv : ∀ t : ℝ, HasDerivAt H (kernelF (k + 1) b t 0) t := by
    intro t
    have hd : HasDerivAt (iteratedDeriv k (fun z => rFun b z ^ k))
        (iteratedDeriv (k + 1) (fun z => rFun b z ^ k) t) t := by
      rw [iteratedDeriv_succ]
      exact (contDiffAt_iteratedDeriv_top ((rFun_contDiff hb).pow k).contDiffAt k).differentiableAt (by simp) |>.hasDerivAt
    have h1 := hd.div_const (k.factorial : ℝ)
    refine h1.congr_deriv ?_
    unfold kernelF
    simp only [Nat.add_sub_cancel, sub_zero]
  have hH_mono : MonotoneOn H (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun t _ => (hH_deriv t).continuousAt.continuousWithinAt)
      (fun t _ => (hH_deriv t).differentiableAt.differentiableWithinAt) ?_
    intro t ht
    rw [(hH_deriv t).deriv]
    have ht0 : 0 ≤ t := by
      rw [interior_Ici] at ht; exact le_of_lt ht
    have hk_eq : k + 1 = (k - 1) + 2 := by omega
    rw [hk_eq, kernelF_eq_kernelG (k - 1) hb t 0]
    exact kernelG_nonneg hb ht0 le_rfl (rFun_pos hb t).le
  -- Limit as t -> +infty: `H t -> 1`!
  have hH_tendsto : Tendsto H atTop (𝓝 1) := by
    have hterm1 : Tendsto (fun t => (t / rFun b t) ^ k) atTop (𝓝 1) := by
      have hratio : Tendsto (fun t => t / rFun b t) atTop (𝓝 1) := by
        have hev : (fun t => t / rFun b t) =ᶠ[atTop] fun t => (Real.sqrt (1 + (b / t) ^ 2))⁻¹ := by
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
          dsimp only [rFun]
          have h1 : t ^ 2 + b ^ 2 = t ^ 2 * (1 + (b / t) ^ 2) := by field_simp [ht.ne']
          rw [h1, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]
          field_simp [ht.ne']
        rw [tendsto_congr' hev]
        have hb_div : Tendsto (fun t : ℝ => b / t) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop tendsto_id
        have hsq : Tendsto (fun t : ℝ => 1 + (b / t) ^ 2) atTop (𝓝 (1 + 0 ^ 2)) :=
          tendsto_const_nhds.add (hb_div.pow 2)
        have hsqrt : Tendsto (fun t : ℝ => Real.sqrt (1 + (b / t) ^ 2)) atTop (𝓝 1) := by
          simpa using hsq.sqrt
        simpa using hsqrt.inv₀ (by norm_num)
      simpa using hratio.pow k
    have hterm2 : Tendsto (fun t => ∫ s in (0 : ℝ)..rFun b t, kernelF k b t s) atTop (𝓝 0) := by
      -- Bound `0 <= kernelG (k - 2) b t s <= C * b^2 / rFun b t^3` for all `0 <= s <= rFun b t`!
      set m := k - 2
      have hkm : k = m + 2 := by omega
      let C : ℝ := ∑ j ∈ Finset.range (m / 2 + 1), catCoeff m j
      have hbound : ∀ᶠ t in atTop,
          0 ≤ (∫ s in (0 : ℝ)..rFun b t, kernelF k b t s) ∧
          (∫ s in (0 : ℝ)..rFun b t, kernelF k b t s) ≤ C * b ^ 2 / rFun b t ^ 2 := by
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
        have hr := rFun_pos hb t
        have hpt : ∀ s ∈ Set.Icc (0 : ℝ) (rFun b t),
            0 ≤ kernelF k b t s ∧ kernelF k b t s ≤ C * b ^ 2 / rFun b t ^ 3 := by
          intro s hs
          rw [hkm, kernelF_eq_kernelG m hb t s]
          refine ⟨kernelG_nonneg hb ht hs.1 hs.2, ?_⟩
          unfold kernelG
          have ht_le : t ≤ rFun b t := calc
            t = Real.sqrt (t ^ 2) := (Real.sqrt_sq ht).symm
            _ ≤ Real.sqrt (t ^ 2 + b ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
          have hb_le : b ≤ rFun b t := calc
            b = Real.sqrt (b ^ 2) := (Real.sqrt_sq hb.le).symm
            _ ≤ Real.sqrt (t ^ 2 + b ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
          have hsum_le :
              ∑ j ∈ Finset.range (m / 2 + 1),
                catCoeff m j * (t * s) ^ (m - 2 * j) * (b ^ 2 * (rFun b t ^ 2 - s ^ 2)) ^ j ≤
              C * rFun b t ^ (2 * m) := by
            dsimp only [C]
            rw [Finset.sum_mul]
            refine Finset.sum_le_sum fun j hj => ?_
            have h2j : 2 * j ≤ m := by have := Finset.mem_range.mp hj; omega
            have hts : (t * s) ^ (m - 2 * j) ≤ (rFun b t ^ 2) ^ (m - 2 * j) :=
              pow_le_pow_left₀ (mul_nonneg ht hs.1) (by nlinarith [hs.1, hs.2, ht, ht_le]) _
            have hbs : (b ^ 2 * (rFun b t ^ 2 - s ^ 2)) ^ j ≤ (rFun b t ^ 4) ^ j := by
              refine pow_le_pow_left₀ (mul_nonneg (sq_nonneg b) (by nlinarith [hs.1, hs.2])) ?_ j
              have h1 : b ^ 2 ≤ rFun b t ^ 2 := by nlinarith
              have h2 : rFun b t ^ 2 - s ^ 2 ≤ rFun b t ^ 2 := by nlinarith
              nlinarith
            have hmul_le : (t * s) ^ (m - 2 * j) * (b ^ 2 * (rFun b t ^ 2 - s ^ 2)) ^ j ≤
                rFun b t ^ (2 * m) := by
              calc (t * s) ^ (m - 2 * j) * (b ^ 2 * (rFun b t ^ 2 - s ^ 2)) ^ j
                  ≤ (rFun b t ^ 2) ^ (m - 2 * j) * (rFun b t ^ 4) ^ j :=
                    mul_le_mul hts hbs (pow_nonneg (mul_nonneg (sq_nonneg b) (by nlinarith [hs.1, hs.2])) j) (by positivity)
                _ = rFun b t ^ (2 * (m - 2 * j) + 4 * j) := by rw [← pow_mul, ← pow_mul, ← pow_add]
                _ = rFun b t ^ (2 * m) := by congr 1; omega
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left hmul_le (catCoeff_nonneg m j)
          calc b ^ 2 / rFun b t ^ (2 * m + 3) *
                ∑ j ∈ Finset.range (m / 2 + 1),
                  catCoeff m j * (t * s) ^ (m - 2 * j) * (b ^ 2 * (rFun b t ^ 2 - s ^ 2)) ^ j
              ≤ b ^ 2 / rFun b t ^ (2 * m + 3) * (C * rFun b t ^ (2 * m)) :=
                mul_le_mul_of_nonneg_left hsum_le (by positivity)
            _ = C * b ^ 2 / rFun b t ^ 3 := by
                have hpow : rFun b t ^ (2 * m + 3) = rFun b t ^ (2 * m) * rFun b t ^ 3 := by ring
                rw [hpow]; field_simp [hr.ne']
        have hcont : Continuous (fun s => kernelF k b t s) := by
          have : (fun s => kernelF k b t s) = fun s => kernelG m b t s :=
            funext fun s => by rw [hkm]; exact kernelF_eq_kernelG m hb t s
          rw [this]; unfold kernelG; fun_prop
        constructor
        · exact intervalIntegral.integral_nonneg hr.le (fun s hs => (hpt s hs).1)
        · calc ∫ s in (0 : ℝ)..rFun b t, kernelF k b t s
              ≤ ∫ _s in (0 : ℝ)..rFun b t, (C * b ^ 2 / rFun b t ^ 3) :=
                intervalIntegral.integral_mono_on hr.le (hcont.intervalIntegrable 0 (rFun b t))
                  intervalIntegrable_const (fun s hs => (hpt s hs).2)
            _ = rFun b t * (C * b ^ 2 / rFun b t ^ 3) := by
                simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
            _ = C * b ^ 2 / rFun b t ^ 2 := by field_simp [hr.ne']
      have htop_lim : Tendsto (fun t => C * b ^ 2 / rFun b t ^ 2) atTop (𝓝 0) := by
        have hr_sq_inf : Tendsto (fun t : ℝ => rFun b t ^ 2) atTop atTop := by
          have : (fun t : ℝ => rFun b t ^ 2) = fun t => t ^ 2 + b ^ 2 := funext (rFun_sq hb)
          rw [this]
          exact Filter.Tendsto.atTop_add (tendsto_pow_atTop (by norm_num : 2 ≠ 0)) tendsto_const_nhds
        exact tendsto_const_nhds.div_atTop hr_sq_inf
      exact squeeze_zero' (hbound.mono fun _ h => h.1) (hbound.mono fun _ h => h.2) htop_lim
    have hsum : Tendsto (fun t => (t / rFun b t) ^ k + ∫ s in (0 : ℝ)..rFun b t, kernelF k b t s) atTop (𝓝 (1 + 0)) :=
      hterm1.add hterm2
    have hH_fun : H = fun t => (t / rFun b t) ^ k + ∫ s in (0 : ℝ)..rFun b t, kernelF k b t s :=
      funext hH_eq
    rw [hH_fun]
    simpa using hsum
  rw [← hH_eq x]
  exact ge_of_tendsto hH_tendsto (by
    filter_upwards [eventually_ge_atTop x] with t ht
    exact hH_mono hx (le_trans hx ht) ht)

/-!
## 6. Putting everything together for `mse-1285815`
-/

lemma even_odd_iteratedDeriv_zero {g : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (heven : ∀ t ∈ Set.Ioo (-R) R, g (-t) = g t) :
    ∀ j : ℕ, Odd j → iteratedDeriv j g 0 = 0 := by
  have hneg : ∀ m : ℕ, ∀ t ∈ Set.Ioo (-R) R,
      iteratedDeriv m g (-t) = (-1 : ℝ) ^ m * iteratedDeriv m g t := by
    intro m
    induction m with
    | zero => intro t ht; simpa using heven t ht
    | succ m ih =>
      intro t ht
      have hmem : ∀ᶠ s in 𝓝 t, s ∈ Set.Ioo (-R) R := isOpen_Ioo.mem_nhds ht
      have heq : (fun s => iteratedDeriv m g (-s)) =ᶠ[𝓝 t]
          fun s => (-1 : ℝ) ^ m * iteratedDeriv m g s := by
        filter_upwards [hmem] with s hs using ih s hs
      have hd := Filter.EventuallyEq.deriv_eq heq
      have hcomp : deriv (fun s => iteratedDeriv m g (-s)) t = -deriv (iteratedDeriv m g) (-t) := by
        rw [deriv_comp_neg]
      rw [hcomp, deriv_const_mul_field] at hd
      rw [iteratedDeriv_succ]
      rw [pow_succ]; linarith
  intro j ⟨m, hm⟩
  subst hm
  have h0 := hneg (2 * m + 1) 0 ⟨by linarith, hR⟩
  simp only [neg_zero, pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul, neg_mul] at h0
  linarith

lemma radial_directional_bound {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {g : ℝ → ℝ}
    (hf : ContDiffOn ℝ ⊤ f (Metric.closedBall 0 1))
    (hrad : ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, f x = g ‖x‖)
    {M : ℝ} (hM : ∀ r ∈ Set.Ioo (0 : ℝ) 1, |iteratedDeriv k g r| ≤ M)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
    {v : EuclideanSpace ℝ (Fin n)} (hv : ‖v‖ = 1) :
    |iteratedFDeriv ℝ k f x (fun _ => v)| ≤ M := by
  have hx_lt : ‖x‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hx
  have hf_at : ContDiffAt ℝ ⊤ f x :=
    (hf x (Metric.ball_subset_closedBall hx)).contDiffAt (Metric.closedBall_mem_nhds_of_mem hx)
  rw [← iteratedDeriv_line_eq_iteratedFDeriv k v hf_at]
  -- Define smooth even profile `gtilde t = f (t • e0)`
  let e0 : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ)
  have he0_norm : ‖e0‖ = 1 := by simp [e0]
  let gtilde : ℝ → ℝ := fun t => f (t • e0)
  have hgt_smooth : ContDiffOn ℝ ⊤ gtilde (Set.Ioo (-1) 1) := by
    have hmap : Set.MapsTo (fun t : ℝ => t • e0) (Set.Ioo (-1) 1) (Metric.closedBall 0 1) := by
      intro t ht
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, he0_norm, mul_one]
      exact (abs_lt.mpr ht).le
    exact hf.comp (contDiff_id.smul contDiff_const).contDiffOn hmap
  have hgt_eq_g : ∀ t ∈ Set.Ioo (0 : ℝ) 1, gtilde t = g t := by
    intro t ht
    have hmem : t • e0 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, he0_norm, mul_one,
        abs_of_pos ht.1]
      exact ht.2.le
    rw [show gtilde t = f (t • e0) from rfl, hrad _ hmem, norm_smul, Real.norm_eq_abs,
      he0_norm, mul_one, abs_of_pos ht.1]
  have hgt_even : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, gtilde (-t) = gtilde t := by
    intro t ht
    have hm1 : (-t) • e0 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_neg, he0_norm, mul_one]
      exact (abs_lt.mpr ht).le
    have hm2 : t • e0 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, he0_norm, mul_one]
      exact (abs_lt.mpr ht).le
    dsimp only [gtilde]
    rw [hrad _ hm1, hrad _ hm2, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
  have hgt_deriv_bound : ∀ t ∈ Set.Ioo (0 : ℝ) 1, |iteratedDeriv k gtilde t| ≤ M := by
    intro t ht
    have hev : gtilde =ᶠ[𝓝 t] g := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs using hgt_eq_g s hs
    rw [hev.iteratedDeriv_eq]
    exact hM t ht
  have hgt_deriv_zero : |iteratedDeriv k gtilde 0| ≤ M := by
    have hcont : ContinuousAt (fun t => |iteratedDeriv k gtilde t|) 0 :=
      (contDiffAt_iteratedDeriv_top ((hgt_smooth 0 ⟨by norm_num, by norm_num⟩).contDiffAt
        (isOpen_Ioo.mem_nhds ⟨by norm_num, by norm_num⟩)) k).continuousAt.abs
    have htend : Tendsto (fun t => |iteratedDeriv k gtilde t|) (𝓝[>] 0) (𝓝 |iteratedDeriv k gtilde 0|) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto htend ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
    exact hgt_deriv_bound t ht
  -- Decompose `x` along `v`: `a = inner ℝ x v`, `b = sqrt(‖x‖^2 - a^2)`
  -- WLOG `a >= 0` (flipping `v -> -v` preserves `|iteratedDeriv k ... 0|`)
  suffices hnonneg : ∀ (u : EuclideanSpace ℝ (Fin n)), ‖u‖ = 1 → 0 ≤ inner ℝ x u →
      |iteratedDeriv k (fun t : ℝ => f (x + t • u)) 0| ≤ M by
    by_cases ha : 0 ≤ inner ℝ x v
    · exact hnonneg v hv ha
    · have hneg_v : ‖-v‖ = 1 := by rw [norm_neg, hv]
      have hneg_a : 0 ≤ inner ℝ x (-v) := by rw [inner_neg_right]; linarith
      have hrel : (fun t : ℝ => f (x + t • (-v))) = fun t => f (x + (-t) • v) := by
        funext t; simp [smul_neg, neg_smul]
      have hneg_deriv : ∀ m : ℕ, ∀ (F : ℝ → ℝ),
          iteratedDeriv m (fun t => F (-t)) 0 = (-1 : ℝ) ^ m * iteratedDeriv m F 0 := by
        intro m
        induction m with
        | zero => intro F; simp
        | succ m ihm =>
          intro F
          rw [iteratedDeriv_succ', iteratedDeriv_succ']
          have h1 : deriv (fun t => F (-t)) = fun t => (-1 : ℝ) * (deriv F (-t)) := by
            funext t; rw [deriv_comp_neg]; ring
          rw [h1, iteratedDeriv_const_mul_real, ihm (deriv F), pow_succ]; ring
      have hval := hnonneg (-v) hneg_v hneg_a
      rw [hrel, hneg_deriv k (fun t => f (x + t • v)), abs_mul, abs_pow, abs_neg, abs_one,
        one_pow, one_mul] at hval
      exact hval
  intro u hu ha
  set a := inner ℝ x u
  have ha_sq_le : a ^ 2 ≤ ‖x‖ ^ 2 := by
    have hcs : |a| ≤ ‖x‖ := by simpa [a, hu] using abs_real_inner_le_norm x u
    nlinarith [sq_abs a, abs_nonneg a, norm_nonneg x]
  set b := Real.sqrt (‖x‖ ^ 2 - a ^ 2)
  have hb_nonneg : 0 ≤ b := Real.sqrt_nonneg _
  have hab_sq : a ^ 2 + b ^ 2 = ‖x‖ ^ 2 := by
    dsimp only [b]; rw [Real.sq_sqrt (by linarith)]; ring
  have hnorm_line : ∀ t : ℝ, ‖x + t • u‖ = Real.sqrt ((a + t) ^ 2 + b ^ 2) := by
    intro t
    have h1 : ‖x + t • u‖ ^ 2 = (a + t) ^ 2 + b ^ 2 := by
      rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs,
        inner_smul_right]
      linarith [hab_sq]
    rw [← Real.sqrt_sq (norm_nonneg (x + t • u)), h1]
  -- Case 1: `b = 0`
  by_cases hb0 : b = 0
  · by_cases ha0 : a = 0
    · -- `x = 0`, so `f (t • u) = gtilde t` near `0`!
      have hev : (fun t : ℝ => f (x + t • u)) =ᶠ[𝓝 (0 : ℝ)] gtilde := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) zero_lt_one] with t ht
        have ht1 : |t| < 1 := by simpa [Metric.mem_ball] using ht
        have hmem1 : x + t • u ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
          rw [Metric.mem_closedBall, dist_zero_right, hnorm_line, ha0, hb0]
          simp [Real.sqrt_sq_eq_abs, ht1.le]
        have hmem2 : t • e0 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
          rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, he0_norm, mul_one]
          exact ht1.le
        dsimp only [gtilde]
        rw [hrad _ hmem1, hrad _ hmem2, hnorm_line, ha0, hb0, norm_smul, Real.norm_eq_abs,
          he0_norm, mul_one]
        simp [Real.sqrt_sq_eq_abs]
      rw [hev.iteratedDeriv_eq]
      exact hgt_deriv_zero
    · -- `a > 0` and `b = 0`, so `f (x + t • u) = gtilde (a + t)` near `0`!
      have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have ha_lt1 : a < 1 := by nlinarith [hab_sq, hx_lt, norm_nonneg x, hb0]
      have hδ : 0 < min a (1 - a) := lt_min ha_pos (by linarith)
      have hev : (fun t : ℝ => f (x + t • u)) =ᶠ[𝓝 (0 : ℝ)] fun t => gtilde (a + t) := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
        have htabs : |t| < min a (1 - a) := by simpa [Metric.mem_ball] using ht
        have hta1 : 0 < a + t := by linarith [(abs_lt.mp htabs).1, min_le_left a (1 - a)]
        have hta2 : a + t < 1 := by linarith [(abs_lt.mp htabs).2, min_le_right a (1 - a)]
        have hmem : x + t • u ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
          rw [Metric.mem_closedBall, dist_zero_right, hnorm_line, hb0]
          simp [Real.sqrt_sq hta1.le, hta2.le]
        rw [hrad _ hmem, hnorm_line, hb0, hgt_eq_g (a + t) ⟨hta1, hta2⟩]
        simp [Real.sqrt_sq hta1.le]
      rw [hev.iteratedDeriv_eq]
      have hgt_a : ContDiffAt ℝ ⊤ gtilde (a + 0) := by
        rw [add_zero]
        exact (hgt_smooth a ⟨by linarith, ha_lt1⟩).contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith, ha_lt1⟩)
      rw [iteratedDeriv_comp_const_add_top k hgt_a, add_zero]
      exact hgt_deriv_bound a ⟨ha_pos, ha_lt1⟩
  · -- Case 2: `b > 0`!
    have hb_pos : 0 < b := lt_of_le_of_ne hb_nonneg (Ne.symm hb0)
    have hr_lt1 : rFun b a < 1 := by
      dsimp only [rFun]; rw [hab_sq, Real.sqrt_sq (norm_nonneg x)]; exact hx_lt
    -- `f (x + t • u) = gtilde (rFun b (a + t))` near `0`!
    have hev : (fun t : ℝ => f (x + t • u)) =ᶠ[𝓝 (0 : ℝ)] fun t => gtilde (rFun b (a + t)) := by
      have hopen : IsOpen {t : ℝ | rFun b (a + t) < 1} :=
        isOpen_lt ((rFun_contDiff hb_pos).continuous.comp (continuous_const.add continuous_id)) continuous_const
      filter_upwards [hopen.mem_nhds (by simpa using hr_lt1)] with t ht
      have hmem1 : x + t • u ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
        rw [Metric.mem_closedBall, dist_zero_right, hnorm_line]; exact ht.le
      have hrpos : 0 < rFun b (a + t) := rFun_pos hb_pos (a + t)
      rw [hrad _ hmem1, hnorm_line, hgt_eq_g (rFun b (a + t)) ⟨hrpos, ht⟩]
      rfl
    rw [hev.iteratedDeriv_eq]
    have hgr_a : ContDiffAt ℝ ⊤ (fun t => gtilde (rFun b t)) (a + 0) := by
      rw [add_zero]
      have hr_Ioo : rFun b a ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [rFun_pos hb_pos a], hr_lt1⟩
      exact ((hgt_smooth _ hr_Ioo).contDiffAt (isOpen_Ioo.mem_nhds hr_Ioo)).comp a
        (rFun_contDiff hb_pos).contDiffAt
    have hshift : iteratedDeriv k (fun t => gtilde (rFun b (a + t))) 0 =
        iteratedDeriv k (fun t => gtilde (rFun b t)) a := by
      simpa using iteratedDeriv_comp_const_add_top k hgr_a
    rw [hshift]
    -- Case `k = 1` directly!
    by_cases hk1 : k = 1
    · subst hk1
      rw [iteratedDeriv_one]
      have hr_Ioo : rFun b a ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [rFun_pos hb_pos a], hr_lt1⟩
      have hgd : HasDerivAt gtilde (deriv gtilde (rFun b a)) (rFun b a) :=
        (((hgt_smooth _ hr_Ioo).contDiffAt (isOpen_Ioo.mem_nhds hr_Ioo)).differentiableAt (by simp)).hasDerivAt
      change |deriv (gtilde ∘ rFun b) a| ≤ M
      rw [(hgd.comp a (rFun_hasDerivAt hb_pos a)).deriv, abs_mul]
      have hratio : |a / rFun b a| ≤ 1 := by
        rw [abs_of_nonneg (div_nonneg ha (rFun_pos hb_pos a).le), div_le_one (rFun_pos hb_pos a)]
        calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
          _ ≤ Real.sqrt (a ^ 2 + b ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      have hg_bd : |deriv gtilde (rFun b a)| ≤ M := by
        simpa [iteratedDeriv_one] using hgt_deriv_bound (rFun b a) ⟨rFun_pos hb_pos a, hr_lt1⟩
      have hM0 : 0 ≤ M := le_trans (abs_nonneg _) hg_bd
      calc |deriv gtilde (rFun b a)| * |a / rFun b a|
          ≤ M * 1 := mul_le_mul hg_bd hratio (abs_nonneg _) hM0
        _ = M := mul_one M
    · -- Main case: `k >= 2`! Apply Taylor integral remainder + our exact Catalan kernel!
      have hk2 : 2 ≤ k := by omega
      set R := (rFun b a + 1) / 2
      have hR_gt : rFun b a < R := by dsimp [R]; linarith
      have hR_lt1 : R < 1 := by dsimp [R]; linarith
      have hbR : b < R := by
        have : b ≤ rFun b a := calc
          b = Real.sqrt (b ^ 2) := (Real.sqrt_sq hb_pos.le).symm
          _ ≤ Real.sqrt (a ^ 2 + b ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        linarith
      have hopen : IsOpen {t : ℝ | rFun b t < R} :=
        isOpen_lt (rFun_contDiff hb_pos).continuous continuous_const
      -- On `{t | rFun b t < R}`, `gtilde (rFun b t)` equals even poly of degree `< k` + integral remainder!
      have htaylor_eq : (fun t => gtilde (rFun b t)) =ᶠ[𝓝 a]
          fun t =>
            (∑ j ∈ Finset.range k, iteratedDeriv j gtilde 0 / (j.factorial : ℝ) * rFun b t ^ j) +
            ∫ s in (0 : ℝ)..rFun b t,
              (rFun b t - s) ^ (k - 1) / ((k - 1).factorial : ℝ) * iteratedDeriv k gtilde s := by
        filter_upwards [hopen.mem_nhds hR_gt] with t ht
        exact taylor_integral_remainder zero_lt_one hgt_smooth hk (rFun b t)
          ⟨rFun_pos hb_pos t, lt_trans ht hR_lt1⟩
      rw [htaylor_eq.iteratedDeriv_eq]
      -- Smoothness of polynomial part and integral part at `a`
      have hpoly_smooth : ContDiffAt ℝ ⊤
          (fun t => ∑ j ∈ Finset.range k, iteratedDeriv j gtilde 0 / (j.factorial : ℝ) * rFun b t ^ j) a :=
        ContDiffAt.sum fun j _ => contDiffAt_const.mul ((rFun_contDiff hb_pos).pow j).contDiffAt
      have hint_smooth : ContDiffAt ℝ ⊤
          (fun t => ∫ s in (0 : ℝ)..rFun b t,
            (rFun b t - s) ^ (k - 1) / ((k - 1).factorial : ℝ) * iteratedDeriv k gtilde s) a := by
        have heq_sub :
            (fun t => ∫ s in (0 : ℝ)..rFun b t,
              (rFun b t - s) ^ (k - 1) / ((k - 1).factorial : ℝ) * iteratedDeriv k gtilde s) =ᶠ[𝓝 a]
            fun t => gtilde (rFun b t) -
              ∑ j ∈ Finset.range k, iteratedDeriv j gtilde 0 / (j.factorial : ℝ) * rFun b t ^ j := by
          filter_upwards [htaylor_eq] with t ht; linarith
        refine ContDiffAt.congr_of_eventuallyEq ?_ heq_sub
        have hgr : ContDiffAt ℝ ⊤ (fun t => gtilde (rFun b t)) a := by
          have hr_Ioo : rFun b a ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [rFun_pos hb_pos a], hr_lt1⟩
          exact ((hgt_smooth _ hr_Ioo).contDiffAt (isOpen_Ioo.mem_nhds hr_Ioo)).comp a
            (rFun_contDiff hb_pos).contDiffAt
        exact hgr.sub hpoly_smooth
      rw [iteratedDeriv_fun_add (hpoly_smooth.of_le (by simp)) (hint_smooth.of_le (by simp))]
      -- Every term in the Taylor polynomial has `k`-th derivative `0`:
      -- odd `j` has `iteratedDeriv j gtilde 0 = 0`; even `j = 2m < k` gives `(t^2 + b^2)^m`, degree `2m < k`!
      have hpoly_zero :
          iteratedDeriv k (fun t => ∑ j ∈ Finset.range k,
            iteratedDeriv j gtilde 0 / (j.factorial : ℝ) * rFun b t ^ j) a = 0 := by
        rw [iteratedDeriv_fun_sum (fun j _ =>
          (contDiffAt_const.mul ((rFun_contDiff hb_pos).pow j).contDiffAt).of_le (by simp))]
        refine Finset.sum_eq_zero fun j hj => ?_
        have hjk : j < k := Finset.mem_range.mp hj
        rw [iteratedDeriv_const_mul_real]
        rcases Nat.even_or_odd j with ⟨m, rfl⟩ | hodd
        · have hpow_eq : (fun t => rFun b t ^ (m + m)) =
              fun t => Polynomial.eval t ((Polynomial.X ^ 2 + Polynomial.C (b ^ 2)) ^ m) := by
            funext t
            rw [show m + m = 2 * m by omega, pow_mul, rFun_sq hb_pos t]
            simp
          rw [hpow_eq, poly_iteratedDeriv_eval]
          have hdeg : ((Polynomial.X ^ 2 + Polynomial.C (b ^ 2) : Polynomial ℝ) ^ m).natDegree < k := by
            have h1 : ((Polynomial.X ^ 2 + Polynomial.C (b ^ 2) : Polynomial ℝ) ^ m).natDegree ≤
                m * (Polynomial.X ^ 2 + Polynomial.C (b ^ 2) : Polynomial ℝ).natDegree :=
              Polynomial.natDegree_pow_le
            have h2 : (Polynomial.X ^ 2 + Polynomial.C (b ^ 2) : Polynomial ℝ).natDegree ≤ 2 := by
              refine le_trans (Polynomial.natDegree_add_le _ _) ?_
              simp [Polynomial.natDegree_C]
            have h3 : m * (Polynomial.X ^ 2 + Polynomial.C (b ^ 2) : Polynomial ℝ).natDegree ≤ m * 2 :=
              Nat.mul_le_mul_left m h2
            omega
          rw [Polynomial.iterate_derivative_eq_zero hdeg, Polynomial.eval_zero, mul_zero]
        · rw [even_odd_iteratedDeriv_zero zero_lt_one hgt_even j hodd, zero_div, zero_mul]
      rw [hpoly_zero, zero_add]
      have hφ_cont : ContinuousOn (iteratedDeriv k gtilde) (Set.Icc 0 R) := by
        intro s hs
        have hmem : s ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hs.1], lt_of_le_of_lt hs.2 hR_lt1⟩
        exact (contDiffAt_iteratedDeriv_top ((hgt_smooth s hmem).contDiffAt (isOpen_Ioo.mem_nhds hmem)) k).continuousAt.continuousWithinAt
      rw [iteratedDeriv_integral_radial hb_pos hbR hφ_cont k hk k le_rfl a hR_gt, if_pos rfl]
      -- Now apply triangle inequality + `kernelF >= 0` + `weight_sum_le_one`!
      have hφ_bound : ∀ s ∈ Set.Icc (0 : ℝ) (rFun b a), |iteratedDeriv k gtilde s| ≤ M := by
        intro s hs
        rcases eq_or_lt_of_le hs.1 with rfl | hs_pos
        · exact hgt_deriv_zero
        · exact hgt_deriv_bound s ⟨hs_pos, lt_of_le_of_lt hs.2 hr_lt1⟩
      have hM0 : 0 ≤ M := le_trans (abs_nonneg _) hgt_deriv_zero
      have hker_nonneg : ∀ s ∈ Set.Icc (0 : ℝ) (rFun b a), 0 ≤ kernelF k b a s := by
        intro s hs
        have hkm : k = (k - 2) + 2 := by omega
        rw [hkm, kernelF_eq_kernelG (k - 2) hb_pos a s]
        exact kernelG_nonneg hb_pos ha hs.1 hs.2
      have hker_cont : Continuous (fun s => kernelF k b a s) := by
        have hkm : k = (k - 2) + 2 := by omega
        have : (fun s => kernelF k b a s) = fun s => kernelG (k - 2) b a s :=
          funext fun s => by rw [hkm]; exact kernelF_eq_kernelG (k - 2) hb_pos a s
        rw [this]; unfold kernelG; fun_prop
      have hsub_R : Set.uIcc (0 : ℝ) (rFun b a) ⊆ Set.Icc 0 R := by
        rw [Set.uIcc_of_le (rFun_pos hb_pos a).le]; exact Set.Icc_subset_Icc_right hR_gt.le
      have hint_abs :
          |∫ s in (0 : ℝ)..rFun b a, kernelF k b a s * iteratedDeriv k gtilde s| ≤
            M * ∫ s in (0 : ℝ)..rFun b a, kernelF k b a s := by
        calc |∫ s in (0 : ℝ)..rFun b a, kernelF k b a s * iteratedDeriv k gtilde s|
            ≤ ∫ s in (0 : ℝ)..rFun b a, |kernelF k b a s * iteratedDeriv k gtilde s| :=
              intervalIntegral.abs_integral_le_integral_abs (rFun_pos hb_pos a).le
          _ ≤ ∫ s in (0 : ℝ)..rFun b a, kernelF k b a s * M := by
              refine intervalIntegral.integral_mono_on (rFun_pos hb_pos a).le ?_ ?_ fun s hs => ?_
              · exact (hker_cont.continuousOn.mul (hφ_cont.mono hsub_R)).abs.intervalIntegrable
              · exact (hker_cont.continuousOn.mul continuousOn_const).intervalIntegrable
              · rw [abs_mul, abs_of_nonneg (hker_nonneg s hs)]
                exact mul_le_mul_of_nonneg_left (hφ_bound s hs) (hker_nonneg s hs)
          _ = M * ∫ s in (0 : ℝ)..rFun b a, kernelF k b a s := by
              rw [intervalIntegral.integral_mul_const, mul_comm]
      have hr_nonneg : 0 ≤ (a / rFun b a) ^ k := pow_nonneg (div_nonneg ha (rFun_pos hb_pos a).le) k
      have hbd1 : |(a / rFun b a) ^ k * iteratedDeriv k gtilde (rFun b a)| ≤ M * (a / rFun b a) ^ k := by
        rw [abs_mul, abs_of_nonneg hr_nonneg, mul_comm]
        exact mul_le_mul_of_nonneg_right (hφ_bound (rFun b a) ⟨(rFun_pos hb_pos a).le, le_rfl⟩) hr_nonneg
      have hw := weight_sum_le_one hk2 hb_pos ha
      calc |(a / rFun b a) ^ k * iteratedDeriv k gtilde (rFun b a) +
              ∫ s in (0 : ℝ)..rFun b a, kernelF k b a s * iteratedDeriv k gtilde s|
          ≤ |(a / rFun b a) ^ k * iteratedDeriv k gtilde (rFun b a)| +
              |∫ s in (0 : ℝ)..rFun b a, kernelF k b a s * iteratedDeriv k gtilde s| := abs_add_le _ _
        _ ≤ M * (a / rFun b a) ^ k + M * ∫ s in (0 : ℝ)..rFun b a, kernelF k b a s :=
            add_le_add hbd1 hint_abs
        _ = M * ((a / rFun b a) ^ k + ∫ s in (0 : ℝ)..rFun b a, kernelF k b a s) := by ring
        _ ≤ M * 1 := mul_le_mul_of_nonneg_left hw hM0
        _ = M := mul_one M

end OMA.Mse1285815

theorem OMA.solution : type_of% @OMA.S_mse_1285815.main := by
  intro n k hn hk f g hf hrad M hM x hx idx
  have hf_at : ContDiffAt ℝ ⊤ f x :=
    (hf x (Metric.ball_subset_closedBall hx)).contDiffAt (Metric.closedBall_mem_nhds_of_mem hx)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM (1 / 2) ⟨by norm_num, by norm_num⟩)
  refine OMA.Mse1285815.banach_symmetric_multilinear hn (iteratedFDeriv ℝ k f x)
    (fun i j v => OMA.Mse1285815.iteratedFDeriv_swap hf_at i j v) hM0
    (fun v hv => OMA.Mse1285815.radial_directional_bound hn hk hf hrad hM hx hv)
    (fun i => EuclideanSpace.single (idx i) (1 : ℝ)) ?_
  intro i
  simp
