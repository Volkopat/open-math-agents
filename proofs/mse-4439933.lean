import OMAStatements.S_mse_4439933
import Mathlib

/-!
Retains @Genbox’s merged proof #29696, head 0f08e3de9567f6118affe220fcc0d836cbf959fa.
The direct product derivative and concise integrating-factor derivative conversion
are adapted from @etaubman’s earlier verified proof linked by statement #20446:
https://github.com/etaubman/open-math-agents/blob/b66349f9bd2e565b04a933b85b56a67568dbb6f6/verified/mse-4439933.lean
Original question: Galen, Math StackExchange 4439933 (CC BY-SA 4.0).
-/

open scoped BigOperators
open Set MeasureTheory OMA.S_mse_4439933

private theorem product_hasDerivAt {n : ℕ} {f df : Fin n → ℝ → ℝ} {x : ℝ}
    (hf : ∀ i, HasDerivAt (f i) (df i x) x) :
    HasDerivAt (productValue f) (productDerivative f df x) x := by
  change HasDerivAt (fun t => ∏ i, f i t) (productDerivative f df x) x
  simpa only [productDerivative, smul_eq_mul] using
    (HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ => hf i))

private theorem product_equation {n : ℕ} {f df : Fin n → ℝ → ℝ} {g : ℝ → ℝ}
    {dg x : ℝ} (hf : ∀ i, HasDerivAt (f i) (df i x) x) (hg : HasDerivAt g dg x) :
    (deriv (fun t => productValue f t * g t) x = productValue df x * dg) ↔
      (productValue df x - productValue f x) * dg = productDerivative f df x * g x := by
  rw [((product_hasDerivAt hf).fun_mul hg).deriv]
  constructor <;> intro h <;> linarith

theorem OMA.solution : type_of% @OMA.S_mse_4439933.main := by
  constructor
  · exact fun _ _ _ _ _ _ hf hg => product_equation hf hg
  · intro n f df s hs hconn hf hdf hne x₀ hx₀
    have cf (i : Fin n) : ContinuousOn (f i) s :=
      fun x hx => (hf i x hx).continuousAt.continuousWithinAt
    have cp : ContinuousOn (productValue f) s :=
      continuousOn_finsetProd _ (fun i _ => cf i)
    have cdp : ContinuousOn (productValue df) s :=
      continuousOn_finsetProd _ (fun i _ => hdf i)
    have csum : ContinuousOn (productDerivative f df) s :=
      continuousOn_finsetSum _ (fun i _ =>
        (continuousOn_finsetProd (Finset.univ.erase i) (fun j _ => cf j)).mul (hdf i))
    have cc : ContinuousOn (coefficient f df) s :=
      csum.div (cdp.sub cp) (fun x hx => sub_ne_zero.mpr (hne x hx))
    have hprim (x : ℝ) (hx : x ∈ s) :
        HasDerivAt (primitive f df x₀) (coefficient f df x) x := by
      have hc := cc.continuousAt (hs.mem_nhds hx)
      exact intervalIntegral.integral_hasDerivAt_right
        ((cc.mono (hconn.uIcc_subset hx₀ hx)).intervalIntegrable)
        (ContinuousOn.stronglyMeasurableAtFilter hs cc x hx) hc
    have hinit (C : ℝ) : OMA.S_mse_4439933.solution f df x₀ C x₀ = C := by
      simp [OMA.S_mse_4439933.solution, primitive]
    constructor
    · intro C
      refine ⟨hinit C, ?_⟩
      intro x hx
      have hsol : HasDerivAt (OMA.S_mse_4439933.solution f df x₀ C)
          (OMA.S_mse_4439933.solution f df x₀ C x * coefficient f df x) x := by
        change HasDerivAt (fun t => C * Real.exp (primitive f df x₀ t))
          ((C * Real.exp (primitive f df x₀ x)) * coefficient f df x) x
        simpa only [mul_assoc, mul_comm, mul_left_comm] using ((hprim x hx).exp.const_mul C)
      refine ⟨hsol.differentiableAt, ?_⟩
      rw [hsol.deriv]
      apply (product_equation (fun i => hf i x hx) hsol).2
      unfold coefficient
      field_simp [sub_ne_zero.mpr (hne x hx)]
    · intro g hg heq x hx
      let F : ℝ → ℝ := fun t => g t * Real.exp (-primitive f df x₀ t)
      have hF (t : ℝ) (ht : t ∈ s) : HasDerivAt F 0 t := by
        have hgt := (hg t ht).hasDerivAt
        have he := (product_equation (fun i => hf i t ht) hgt).1 (heq t ht)
        have hr : deriv g t = g t * coefficient f df t := by
          unfold coefficient
          field_simp [sub_ne_zero.mpr (hne t ht)]
          linarith
        apply (hgt.mul (hprim t ht).neg.exp).congr_deriv
        rw [hr]
        ring
      have hconst : F x = F x₀ :=
        hs.is_const_of_deriv_eq_zero hconn.isPreconnected
          (fun t ht => (hF t ht).differentiableAt.differentiableWithinAt)
          (fun t ht => (hF t ht).deriv) hx hx₀
      have hc : g x * Real.exp (-primitive f df x₀ x) = g x₀ := by
        simpa [F, primitive] using hconst
      have hm := congrArg (fun z : ℝ => z * Real.exp (primitive f df x₀ x)) hc
      simpa only [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one,
        OMA.S_mse_4439933.solution] using hm