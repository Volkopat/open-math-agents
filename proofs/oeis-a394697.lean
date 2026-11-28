import OMAStatements.S_oeis_a394697
import Mathlib.Tactic

open OMA.S_oeis_a394697 Filter Topology Finset

namespace KingBoardEntropy

private lemma onBoard {w : Bool} {n : ℕ} {s : Placement} :
    s ∈ boards w n ↔ s ⊆ cells n ∧ independent w n s := by
  classical
  simp [boards]

private lemma inCells {p : Square} {n : ℕ} :
    p ∈ cells n ↔ p.1<n ∧ p.2<n := by simp [cells]

private lemma emptyBoard (w : Bool) (n : ℕ) : (∅ : Placement) ∈ boards w n := by
  apply onBoard.mpr
  simp [independent]

private lemma positiveOrdinary (n : ℕ) : 0 < ordinary n :=
  card_pos.mpr ⟨_,emptyBoard false n⟩

private lemma positivePeak (n : ℕ) : 0 < peak n := by
  have h : 0 < coefficient n 0 := card_pos.mpr ⟨∅,mem_filter.mpr ⟨emptyBoard true n,by simp⟩⟩
  exact h.trans_le (le_sup (f:=coefficient n) (mem_range.mpr (by omega : 0<n^2+1)))

private lemma periodicOrdinary (n : ℕ) : boards true n ⊆ boards false n := by
  intro s hs
  obtain ⟨sub,ind⟩ := onBoard.mp hs
  apply onBoard.mpr
  refine ⟨sub,?_⟩
  intro x hx y hy h₁ h₂
  apply ind x hx y hy
  · exact Or.inl (by simpa [near] using h₁)
  · exact Or.inl (by simpa [near] using h₂)

private lemma ordinaryPeriodic (n : ℕ) : boards false n ⊆ boards true (n+1) := by
  intro s hs
  obtain ⟨sub,ind⟩ := onBoard.mp hs
  have internal {i j : ℕ} (hi : i<n) (hj : j<n) :
      near true (n+1) i j → near false n i j := by simp [near]; omega
  apply onBoard.mpr
  constructor
  · intro x hx
    obtain ⟨h₁,h₂⟩ := inCells.mp (sub hx)
    exact inCells.mpr ⟨by omega,by omega⟩
  · intro x hx y hy h₁ h₂
    have X := inCells.mp (sub hx)
    have Y := inCells.mp (sub hy)
    exact ind x hx y hy (internal X.1 Y.1 h₁) (internal X.2 Y.2 h₂)

private lemma peakUpper (n : ℕ) : peak n ≤ ordinary n := by
  apply Finset.sup_le
  intro k _
  exact (card_filter_le _ _).trans (card_le_card (periodicOrdinary n))

private lemma peakLower (n : ℕ) : ordinary n ≤ ((n+1)^2+1)*peak (n+1) := by
  classical
  let m := n+1
  have covers (s : Placement) (hs : s ∈ boards true m) : s.card ∈ range (m^2+1) := by
    apply mem_range.mpr
    have h := card_le_card (onBoard.mp hs).1
    simpa [cells,sq] using Nat.lt_succ_of_le h
  have fibers := card_eq_sum_card_fiberwise (s:=boards true m) (t:=range (m^2+1))
    (f:=fun s : Placement => s.card) covers
  calc
    ordinary n ≤ (boards true m).card := card_le_card (ordinaryPeriodic n)
    _ = ∑ k ∈ range (m^2+1), coefficient m k := fibers
    _ ≤ ∑ _k ∈ range (m^2+1), peak m := sum_le_sum (fun k hk => le_sup (f:=coefficient m) hk)
    _ = _ := by simp [m]

private def tile (m i j : ℕ) (s : Placement) : Placement :=
  (cells m).filter (fun z => (z.1+m*i,z.2+m*j) ∈ s)

private lemma validTile {n : ℕ} {s : Placement} (hs : s ∈ boards false n) (m i j : ℕ) :
    tile m i j s ∈ boards false m := by
  apply onBoard.mpr
  refine ⟨filter_subset _ _,?_⟩
  intro x hx y hy h₁ h₂
  have shift {a b c : ℕ} : near false m a b → near false n (a+c) (b+c) := by
    simp [near]; omega
  have e := (onBoard.mp hs).2 _ (mem_filter.mp hx).2 _ (mem_filter.mp hy).2 (shift h₁) (shift h₂)
  exact Prod.ext (by have h := congrArg Prod.fst e; dsimp at h; omega)
    (by have h := congrArg Prod.snd e; dsimp at h; omega)

-- A placement is determined by its restrictions to a square array of tiles.
private lemma tiling (n m : ℕ) (hm : 0 < m) :
    ordinary n ≤ (ordinary m)^((n/m+1)^2) := by
  classical
  let K := n/m+1
  let address (v : ℕ) (hv : v<n) : Fin K :=
    ⟨v/m,Nat.lt_succ_of_le (Nat.div_le_div_right hv.le)⟩
  let split : ↥(boards false n) → (Fin K × Fin K → ↥(boards false m)) :=
    fun b t => ⟨tile m t.1.val t.2.val b.val,validTile b.property m t.1.val t.2.val⟩
  have inj : Function.Injective split := by
    intro b d h
    apply Subtype.ext
    ext p
    by_cases hp : p ∈ cells n
    · have H := inCells.mp hp
      let t : Fin K × Fin K := (address p.1 H.1,address p.2 H.2)
      have recover (v : ↥(boards false n)) :
          (p.1%m,p.2%m) ∈ (split v t).val ↔ p ∈ v.val := by
        simp [split,t,tile,address,cells,Nat.mod_lt _ hm,Nat.mod_add_div]
      rw [←recover b,←recover d]
      exact Iff.of_eq (congrArg (fun B : ↥(boards false m) => (p.1%m,p.2%m) ∈ B.val) (congrFun h t))
    · have hb : p ∉ b.val := fun z => hp ((onBoard.mp b.property).1 z)
      have hd : p ∉ d.val := fun z => hp ((onBoard.mp d.property).1 z)
      simp [hb,hd]
  have bound := Fintype.card_le_of_injective split inj
  simpa [ordinary,K,Fintype.card_fun,sq] using bound

private noncomputable def rate (n : ℕ) : ℝ := Real.log (ordinary n:ℝ)/(n:ℝ)^2

private lemma tileRatio (m : ℕ) (hm : 0 < m) :
    Tendsto (fun n : ℕ => ((n/m+1:ℕ):ℝ)/(n:ℝ)) atTop (𝓝 (1/(m:ℝ))) := by
  have mr : (0:ℝ) < m := by exact_mod_cast hm
  have inv : Tendsto (fun n : ℕ => 1/(n:ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have H : Tendsto (fun n : ℕ => 1/(m:ℝ)+1/(n:ℝ)) atTop (𝓝 (1/(m:ℝ))) := by
    simpa using inv.const_add (1/(m:ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds H
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have nr : (0:ℝ)<n := by exact_mod_cast hn
    rw [div_le_div_iff₀ mr nr,one_mul]
    have h : n ≤ (n/m+1)*m := by
      have z := Nat.mod_lt n hm
      have eqn := Nat.mod_add_div n m
      rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm (n/m) m]
      omega
    exact_mod_cast h
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have nr : (0:ℝ)<n := by exact_mod_cast hn
    have Q : ((n/m:ℕ):ℝ)*(m:ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.div_mul_le_self n m
    push_cast
    field_simp
    nlinarith only [Q]

private lemma tileLog (m : ℕ) (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop, rate n ≤ Real.log (ordinary m:ℝ)*(((n/m+1:ℕ):ℝ)/(n:ℝ))^2 := by
  apply Eventually.of_forall
  intro n
  have B : (ordinary n:ℝ) ≤ (ordinary m:ℝ)^((n/m+1)^2) := by exact_mod_cast tiling n m hm
  have pos : (0:ℝ)<ordinary n := by exact_mod_cast positiveOrdinary n
  have L := Real.log_le_log pos B
  rw [Real.log_pow] at L
  unfold rate
  apply (div_le_div_of_nonneg_right L (by positivity : 0≤(n:ℝ)^2)).trans_eq
  push_cast
  ring

private noncomputable def values : Set ℝ := {r | ∃ m : ℕ, 0 < m ∧ rate m = r}
private noncomputable def entropyLog := sInf values

private lemma ordinaryLimit : Tendsto rate atTop (𝓝 entropyLog) := by
  have bounded : BddBelow values := by
    refine ⟨0,?_⟩
    rintro x ⟨m,_,rfl⟩
    unfold rate
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast positiveOrdinary m)) (by positivity)
  have nonempty : values.Nonempty := ⟨rate 1,1,by decide,rfl⟩
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact ha.trans_le (csInf_le bounded (show rate n ∈ values from ⟨n,hn,rfl⟩))
  · intro b hb
    obtain ⟨r,⟨m,hm,rfl⟩,lt⟩ := exists_lt_of_csInf_lt nonempty hb
    have conv : Tendsto (fun n : ℕ => Real.log (ordinary m:ℝ)*(((n/m+1:ℕ):ℝ)/(n:ℝ))^2)
        atTop (𝓝 (rate m)) := by
      have H := ((tileRatio m hm).pow 2).const_mul (Real.log (ordinary m:ℝ))
      simpa [rate,div_pow,div_eq_mul_inv] using H
    filter_upwards [tileLog m hm,conv.eventually_lt_const lt] with n hl hr
    exact hl.trans_lt hr

-- The ordinary count on boards of side n uses exponent 1/(n+1)^2 in A063443.
private lemma shiftedLog :
    Tendsto (fun n : ℕ => Real.log (ordinary n:ℝ)/((n:ℝ)+1)^2) atTop (𝓝 entropyLog) := by
  have inv : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp (tendsto_add_atTop_nat 1)
  have ratio : Tendsto (fun n : ℕ => (n:ℝ)/((n:ℝ)+1)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x:=(1:ℝ))).sub inv
    convert h using 2 with n
    · field_simp; ring
    · norm_num
  have H := ordinaryLimit.mul (ratio.pow 2)
  apply (show Tendsto (fun n : ℕ => rate n*((n:ℝ)/((n:ℝ)+1))^2) atTop (𝓝 entropyLog) by simpa using H).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have p : (0:ℝ)<n := by exact_mod_cast hn
  unfold rate
  field_simp

private lemma countingLoss :
    Tendsto (fun n : ℕ => Real.log (((n:ℝ)+1)^2+1)/((n:ℝ)+1)^2) atTop (𝓝 0) := by
  have lg : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have linear : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x:=(1:ℝ)))
  have square : Tendsto (fun n : ℕ => ((n:ℝ)+1)^2) atTop atTop :=
    (tendsto_pow_atTop (by decide : (2:ℕ)≠0)).comp linear
  have plus : Tendsto (fun n : ℕ => ((n:ℝ)+1)^2+1) atTop atTop :=
    square.atTop_add (tendsto_const_nhds (x:=(1:ℝ)))
  have H := lg.comp plus
  have I : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)^2) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp square |>.congr (fun n => by simp)
  have J := H.mul (I.const_add 1)
  apply (show Tendsto (fun n : ℕ => (Real.log (((n:ℝ)+1)^2+1)/(((n:ℝ)+1)^2+1))*
      (1+1/((n:ℝ)+1)^2)) atTop (𝓝 0) by simpa [Function.comp_def] using J).congr
  intro n
  field_simp

private lemma peakLog :
    Tendsto (fun n : ℕ => Real.log (peak (n+1):ℝ)/((n:ℝ)+1)^2) atTop (𝓝 entropyLog) := by
  have l := shiftedLog.sub countingLoss
  have l' : Tendsto (fun n : ℕ => Real.log (ordinary n:ℝ)/((n:ℝ)+1)^2 -
      Real.log (((n:ℝ)+1)^2+1)/((n:ℝ)+1)^2) atTop (𝓝 entropyLog) := by simpa using l
  have u : Tendsto (fun n : ℕ => Real.log (ordinary (n+1):ℝ)/((n:ℝ)+1)^2) atTop (𝓝 entropyLog) := by
    simpa [rate,Function.comp_def] using ordinaryLimit.comp (tendsto_add_atTop_nat 1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le l' u
  · intro n
    have B : (ordinary n:ℝ) ≤ (((n:ℝ)+1)^2+1)*(peak (n+1):ℝ) := by exact_mod_cast peakLower n
    have x : (0:ℝ)<ordinary n := by exact_mod_cast positiveOrdinary n
    have y : (0:ℝ)<peak (n+1) := by exact_mod_cast positivePeak (n+1)
    have h := Real.log_le_log x B
    rw [Real.log_mul (by positivity) y.ne'] at h
    dsimp only
    rw [←sub_div]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  · intro n
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Real.log_le_log (by exact_mod_cast positivePeak (n+1))
    exact_mod_cast peakUpper (n+1)

end KingBoardEntropy

open KingBoardEntropy

theorem OMA.solution : type_of% @OMA.S_oeis_a394697.main := by
  refine ⟨Real.exp entropyLog,?_,?_⟩
  · apply (tendsto_add_atTop_iff_nat 1).mp
    have h := (Real.continuous_exp.tendsto entropyLog).comp shiftedLog
    apply h.congr
    intro n
    change Real.exp (Real.log (ordinary n:ℝ)/((n:ℝ)+1)^2) =
      (ordinary (n+1-1):ℝ)^(1/((n+1:ℕ):ℝ)^2)
    rw [Nat.add_sub_cancel,Real.rpow_def_of_pos (by exact_mod_cast positiveOrdinary n)]
    push_cast
    congr 1
    ring
  · apply (tendsto_add_atTop_iff_nat 1).mp
    have h := (Real.continuous_exp.tendsto entropyLog).comp peakLog
    apply h.congr
    intro n
    change Real.exp (Real.log (peak (n+1):ℝ)/((n:ℝ)+1)^2) = (peak (n+1):ℝ)^(1/((n+1:ℕ):ℝ)^2)
    rw [Real.rpow_def_of_pos (by exact_mod_cast positivePeak (n+1))]
    push_cast
    congr 1
    ring
