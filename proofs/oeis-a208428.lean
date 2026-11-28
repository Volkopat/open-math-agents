import OMAStatements.S_oeis_a208428
import Mathlib.Tactic

open OMA.S_oeis_a208428 PowerSeries

namespace KnightColors

private def ready (b : Boundary) : Bool := b.seenOne && b.previous.isSome

-- A knight edge has already forced the introduction of color 1 by row three.
set_option maxRecDepth 8192 in
private lemma first : (boundaries 2).all ready = true := by decide +kernel

private lemma stable (b : Boundary) (h : ready b=true) (s : Boundary) (hs : s ∈ extend b) :
    ready s=true := by
  have seen : b.seenOne=true := (Bool.and_eq_true_iff.mp h).1
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hs
  simp [ready,seen]

private lemma allReady (n : ℕ) : ∀ b ∈ boundaries (n+2), ready b=true := by
  induction n with
  | zero => exact List.all_eq_true.mp first
  | succ n ih =>
    intro b hb
    obtain ⟨old,h₁,h₂⟩ := List.mem_flatMap.mp hb
    exact stable old (ih old h₁) b h₂

-- Each new cell may use either of the two colors which differ from its
-- knight neighbor. The two choices in a row are independent.
private lemma four : ∀ (old cur : Row), (extend ⟨some old,cur,true⟩).length=4 := by decide +kernel

private lemma degree (b : Boundary) (h : ready b=true) : (extend b).length=4 := by
  rcases b with ⟨old,cur,seen⟩
  cases old with
  | none => simp [ready] at h
  | some r =>
    cases seen with
    | false => simp [ready] at h
    | true => exact four r cur

private lemma countNext (bs : List Boundary) (h : ∀ b ∈ bs, ready b=true) :
    (bs.flatMap extend).length=4*bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,
      degree b (h b (by simp)),ih (fun v hv => h v (List.mem_cons_of_mem b hv))]
    omega

private lemma rec (n : ℕ) : a (n+4)=4*a (n+3) := countNext _ (allReady n)

set_option maxRecDepth 8192 in
private lemma initial : a 0=0 ∧ a 1=2 ∧ a 2=14 ∧ a 3=54 := by decide +kernel

private lemma formula (n : ℕ) : a (n+3)=27*2^(2*n+1) := by
  induction n with
  | zero => exact initial.2.2.2
  | succ n ih =>
    rw [rec n,ih,show 2*(n+1)+1=(2*n+1)+2 by omega,pow_add]
    ring

private lemma series : (1-4*X)*(PowerSeries.mk (fun n => (a n : ℚ))) =
    2*X*(1+3*X-X^2) := by
  let F := PowerSeries.mk (fun n => (a n : ℚ))
  have h : F-C (4:ℚ)*(F*X)=C (2:ℚ)*X+C (6:ℚ)*X^2-C (2:ℚ)*X^3 := by
    ext k
    by_cases hk : k ≤ 3
    · obtain ⟨z,o,t,th⟩ := initial
      interval_cases k <;> norm_num [F,coeff_C_mul,coeff_succ_mul_X,coeff_X,coeff_X_pow,
        coeff_zero_eq_constantCoeff,z,o,t,th]
    · obtain ⟨j,rfl⟩ : ∃ j, k=j+4 := ⟨k-4,by omega⟩
      have hr : (a (j+4):ℚ)=4*(a (j+3):ℚ) := by exact_mod_cast rec j
      simp [F,coeff_C_mul,coeff_succ_mul_X,coeff_X_pow,hr]
  change (1-4*X)*F=_
  simp only [map_ofNat] at h
  linear_combination h

end KnightColors

theorem OMA.solution : type_of% @OMA.S_oeis_a208428.main :=
  ⟨KnightColors.rec,KnightColors.series,KnightColors.formula⟩
