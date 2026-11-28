import OMAStatements.S_mo_198378

namespace OMA.S_mo_198378
open Finset
private noncomputable def score {m : ℕ} (b : Bits m) (v : Fin m→ℝ) : ℝ :=
  ∑ i, (2*(bit (b i)-1/2)*v i - v i^2)
private lemma mom_one (v : ℝ) : (∑ b : Bool, Real.exp (2*(2*(bit b-1/2)*v-v^2))) ≤ 2 := by
  rw [Fintype.sum_bool]
  have h := Real.cosh_le_exp_half_sq (2*v)
  rw [Real.cosh_eq] at h
  have h1 : 2*(2*(bit true-1/2)*v-v^2)=2*v+(-(2*v)^2/2) := by simp [bit]; ring
  have h0 : 2*(2*(bit false-1/2)*v-v^2)=-(2*v)+(-(2*v)^2/2) := by simp [bit]; ring
  rw [h1,h0,Real.exp_add,Real.exp_add,show -(2*v)^2/2=-((2*v)^2/2) by ring,Real.exp_neg ((2*v)^2/2)]
  have hp : 0<Real.exp ((2*v)^2/2) := Real.exp_pos _
  field_simp
  rw [show (2*v)^2/2=2*v^2 by ring] at h
  linarith
private lemma mom_score {m : ℕ} (v : Fin m→ℝ) :
    (∑ b : Bits m, Real.exp (2*score b v)) ≤ 2^m := by
  calc _ = ∑ b : Bits m, ∏ i, Real.exp (2*(2*(bit (b i)-1/2)*v i-v i^2)) := by
             apply sum_congr rfl; intro b _
             rw [score,Finset.mul_sum,Real.exp_sum]
       _ = ∏ i, ∑ b : Bool, Real.exp (2*(2*(bit b-1/2)*v i-v i^2)) :=
             (Fintype.prod_sum (fun (i : Fin m) (a : Bool) => Real.exp (2*(2*(bit a-1/2)*v i-v i^2)))).symm
       _ ≤ ∏ _i : Fin m, (2:ℝ) := prod_le_prod (fun i _ => by positivity) (fun i _ => mom_one _)
       _ = _ := by simp
private lemma mom_source {m r : ℕ} {p : Bits m→ℝ} (hp : source r p) (v : Fin m→ℝ) :
    (∑ b,p b*Real.exp (2*score b v))≤2^r := by
  calc _ ≤ ∑ b : Bits m,(2^r/2^m : ℝ)*Real.exp (2*score b v) :=
             sum_le_sum (fun b _ => mul_le_mul_of_nonneg_right (hp.2.2 b) (Real.exp_pos _).le)
       _ = _ := (Finset.mul_sum _ _ _).symm
       _ ≤ ((2:ℝ)^r/2^m)*2^m := mul_le_mul_of_nonneg_left (mom_score v) (by positivity)
       _ = _ := by field_simp
private noncomputable def offset {m : ℕ} (v : Fin m→ℝ) (i : Fin m) := 1/2+v i
private noncomputable def center {n m : ℕ} (P : Fin n→Finset (Fin m)) (v : Fin m→ℝ) (j : Fin n) :=
  max 0 (min 1 (avg (P j) (offset v)))
private lemma center_mem {n m} (P : Fin n→Finset (Fin m)) (v : Fin m→ℝ) (j : Fin n) :
    center P v j ∈ Set.Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _,max_le zero_le_one (min_le_left _ _)⟩
private lemma reading_mem {m n} (P : Fin n→Finset (Fin m)) (b : Bits m) (j : Fin n) :
    readings P b j ∈ Set.Icc (0:ℝ) 1 := by
  have h : ∀ i, bit (b i)∈Set.Icc (0:ℝ) 1 := by intro i; cases b i <;> norm_num [bit]
  constructor
  · exact div_nonneg (sum_nonneg fun i _ => (h i).1) (Nat.cast_nonneg _)
  · by_cases h0 : (P j).card=0
    · simp [readings,avg,h0]
    · apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0))).mpr
      simpa using sum_le_sum (s := P j) (g := fun _ => (1:ℝ)) (fun i _ => (h i).2)
private lemma dist_clip {y a : ℝ} (hy : y∈Set.Icc (0:ℝ) 1) : |max 0 (min 1 a)-y|≤|a-y| := by
  rcases le_total a 0 with ha|ha
  · rw [min_eq_right (ha.trans zero_le_one),max_eq_left ha,abs_of_nonpos (by linarith [hy.1]),abs_of_nonpos (by linarith [hy.1])]; linarith
  · rcases le_total a 1 with hb|hb
    · rw [min_eq_right hb,max_eq_right ha]
    · rw [min_eq_left hb,max_eq_right zero_le_one,abs_of_nonneg (by linarith [hy.2]),abs_of_nonneg (by linarith [hy.2])]; linarith
private noncomputable def move {m : ℕ} (v : Fin m→ℝ) (P : Finset (Fin m)) (d : ℝ) (i : Fin m) :=
  if i∈P then v i+d else v i
private lemma score_move {m} (b : Bits m) (v : Fin m→ℝ) (P : Finset (Fin m)) (d : ℝ) :
    score b (move v P d) = score b v +
      (2*d*((∑ i ∈ P,bit (b i)) - ∑ i ∈ P,offset v i)-P.card*d^2) := by
  have h : ∀ i, (2*(bit (b i)-1/2)*move v P d i - (move v P d i)^2) =
      2*(bit (b i)-1/2)*v i -v i^2 + (if i∈P then 2*d*(bit (b i)-offset v i)-d^2 else 0) := by
    intro i; by_cases hp : i∈P <;> simp [move,hp,offset]; ring
  simp only [score,h,sum_add_distrib,Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_sub_distrib,
    ←Finset.mul_sum,sum_const,nsmul_eq_mul]
private lemma step_gain {n m : ℕ} {K ε : ℝ} (hK : 0<K) (hε : 0<ε) (P : Fin n→Finset (Fin m))
    (hP : ∀ j,K≤((P j).card:ℝ)) (b : Bits m) (v : Fin m→ℝ) (hbad : ¬near ε (center P v) (readings P b)) :
    ∃ j : Fin n, ∃ s : Bool, score b v+ε^2*K ≤ score b (move v (P j) (if s then ε else -ε)) := by
  obtain ⟨j,hj⟩ : ∃ j, ε < |center P v j-readings P b j| := by simpa [near] using hbad
  have hd := hj.trans_le (dist_clip (a := avg (P j) (offset v)) (reading_mem P b j))
  have hc : 0<((P j).card:ℝ) := hK.trans_le (hP j)
  have hscale (f : Fin m→ℝ) : avg (P j) f * ((P j).card:ℝ) = ∑ i∈P j,f i :=
    div_mul_cancel₀ _ hc.ne'
  rw [lt_abs] at hd
  rcases hd with h|h
  · refine ⟨j,false,?_⟩
    rw [score_move,←hscale,←hscale]
    have h' := mul_lt_mul_of_pos_right h hc
    have h'' := mul_le_mul_of_nonneg_left (hP j) (sq_nonneg ε)
    change ε < avg (P j) (offset v)-avg (P j) (fun i => bit (b i)) at h
    dsimp only [readings] at h'
    simp only [Bool.false_eq_true, if_false]
    nlinarith [mul_pos hε (sub_pos.mpr h')]
  · refine ⟨j,true,?_⟩
    rw [score_move,←hscale,←hscale]
    have h' := mul_lt_mul_of_pos_right h hc
    have h'' := mul_le_mul_of_nonneg_left (hP j) (sq_nonneg ε)
    dsimp only [readings] at h'
    simp only [if_true]
    nlinarith [mul_pos hε (sub_pos.mpr h')]
end OMA.S_mo_198378

namespace OMA.S_mo_198378
open Finset
private abbrev Action (n : ℕ) := Option (Fin n×Bool)
private noncomputable def applyStep {n m : ℕ} (P : Fin n→Finset (Fin m)) (ε : ℝ)
    (v : Fin m→ℝ) : Action n → (Fin m→ℝ)
  | none => v
  | some (j,s) => move v (P j) (if s then ε else -ε)
private noncomputable def states {n m : ℕ} (P : Fin n→Finset (Fin m)) (ε : ℝ) : ℕ→Finset (Fin m→ℝ)
  | 0 => {0}
  | t+1 => by classical exact ((states P ε t) ×ˢ (univ : Finset (Action n))).image (fun q => applyStep P ε q.1 q.2)
private lemma mem_step {n m t : ℕ} (P : Fin n→Finset (Fin m)) (ε : ℝ) {v : Fin m→ℝ}
    (hv : v∈states P ε t) (a : Action n) : applyStep P ε v a ∈ states P ε (t+1) := by
  classical
  exact mem_image.mpr ⟨(v,a),mem_product.mpr ⟨hv,mem_univ _⟩,rfl⟩
private lemma size_states {n m : ℕ} (P : Fin n→Finset (Fin m)) (ε : ℝ) (t : ℕ) :
    (states P ε t).card ≤ (2*n+1)^t := by
  classical
  induction t with
  | zero => simp [states]
  | succ t ih =>
    calc _ ≤ ((states P ε t) ×ˢ (univ : Finset (Action n))).card := card_image_le
         _ = (states P ε t).card * (2*n+1) := by simp [Action,Nat.mul_comm]
         _ ≤ _ := by rw [pow_succ]; gcongr
private lemma escaped {n m : ℕ} (P : Fin n→Finset (Fin m)) {ε K : ℝ} (hε : 0<ε) (hK : 0<K)
    (hP : ∀ j,K≤((P j).card:ℝ)) (b : Bits m) (t : ℕ)
    (hbad : ∀ v∈states P ε t, ¬near ε (center P v) (readings P b)) :
    ∃ v∈states P ε (t+1), ((t+1:ℕ):ℝ)*ε^2*K ≤ score b v := by
  induction t with
  | zero =>
    have hz : 0∈states P ε 0 := by simp [states]
    obtain ⟨j,s,h⟩ := step_gain hK hε P hP b 0 (hbad 0 hz)
    exact ⟨_,mem_step P ε hz (some (j,s)),by simpa [score,applyStep] using h⟩
  | succ t ih =>
    obtain ⟨v,hv,hscore⟩ := ih (fun w hw => hbad w (mem_step P ε hw none))
    obtain ⟨j,s,h⟩ := step_gain hK hε P hP b v (hbad v hv)
    refine ⟨_,mem_step P ε hv (some (j,s)),?_⟩
    change _ ≤ score b (move v (P j) (if s then ε else -ε))
    push_cast at hscore ⊢
    linarith
private lemma finite_cover (m n t : ℕ) (P : Fin n→Finset (Fin m)) (ε K : ℝ) (hε : 0<ε) (hK : 0<K)
    (hP : ∀ j,K≤((P j).card:ℝ)) :
    ∃ S : Finset (Fin n→ℝ), cube S ∧ S.card ≤ (2*n+1)^t ∧ ∀ r p, source r p →
      missed p P S ε ≤ (2:ℝ)^r*(((2*n+1:ℕ):ℝ)*Real.exp (-2*ε^2*K))^(t+1) := by
  classical
  let Z := (states P ε t).image (center P)
  refine ⟨Z,?_,card_image_le.trans (size_states P ε t),?_⟩
  · intro z hz j
    obtain ⟨v,_,rfl⟩ := mem_image.mp hz
    exact center_mem P v j
  intro r p hp
  let A := ((t+1:ℕ):ℝ)*ε^2*K
  let V := states P ε (t+1)
  have point (b : Bits m) :
      (if ∃ z∈Z,near ε z (readings P b) then 0 else p b)*Real.exp (2*A) ≤
        ∑ v∈V,p b*Real.exp (2*score b v) := by
    split_ifs with hg
    · simp only [zero_mul]; exact sum_nonneg (fun v _ => mul_nonneg (hp.1 b) (Real.exp_pos _).le)
    · have hbad : ∀ v∈states P ε t, ¬near ε (center P v) (readings P b) :=
        fun v hv hn => hg ⟨_,mem_image_of_mem _ hv,hn⟩
      obtain ⟨v,hv,h⟩ := escaped P hε hK hP b t hbad
      calc _ ≤ p b*Real.exp (2*score b v) := by gcongr; exact hp.1 b
           _ ≤ _ := single_le_sum (f := fun w => p b*Real.exp (2*score b w)) (fun w _ => mul_nonneg (hp.1 b) (Real.exp_pos _).le) hv
  have hb : missed p P Z ε * Real.exp (2*A) ≤ (2:ℝ)^r * ((2*n+1:ℕ):ℝ)^(t+1) := by
    calc _ = ∑ b : Bits m,(if ∃ z∈Z,near ε z (readings P b) then 0 else p b)*Real.exp (2*A) := by rw [missed,sum_mul]
         _ ≤ ∑ b : Bits m,∑ v∈V,p b*Real.exp (2*score b v) := sum_le_sum fun b _ => point b
         _ = ∑ v∈V,∑ b : Bits m,p b*Real.exp (2*score b v) := sum_comm
         _ ≤ ∑ _v∈V,(2:ℝ)^r := sum_le_sum fun v _ => mom_source hp v
         _ = (2:ℝ)^r*(V.card:ℝ) := by simp [mul_comm]
         _ ≤ _ := by gcongr; exact_mod_cast size_states P ε (t+1)
  calc missed p P Z ε ≤ (2:ℝ)^r*((2*n+1:ℕ):ℝ)^(t+1)/Real.exp (2*A) := (le_div_iff₀ (Real.exp_pos _)).mpr hb
       _ = _ := by
         rw [mul_pow,←Real.exp_nat_mul,show ((t+1:ℕ):ℝ)*(-2*ε^2*K)=-(2*A) by dsimp [A]; ring,Real.exp_neg]
         ring
end OMA.S_mo_198378

namespace OMA.S_mo_198378
open Finset
private lemma budget_cover (m n s : ℕ) (P : Fin n→Finset (Fin m)) (hspos : 0<s) (hn : 20000≤Real.log n)
    (hP : ∀ j,(Real.log n)^2≤((P j).card:ℝ)) :
    ∃ S : Finset (Fin n→ℝ), cube S ∧ S.card ≤ s ∧
      ∀ r p,source r p → missed p P S (1/100) ≤ (2:ℝ)^r/s := by
  let B := 2*n+1
  have hn' : 3≤n := by
    by_contra h
    have hle : (n:ℝ)≤2 := by exact_mod_cast (show n≤2 by omega)
    rcases Nat.eq_zero_or_pos n with he|hp
    · norm_num [he] at hn
    · linarith [Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr hp)]
  have hb : 1<B := by dsimp [B]; omega
  have hb0 : 0<(B:ℝ) := by exact_mod_cast zero_lt_one.trans hb
  have he : Real.log (B:ℝ) ≤ Real.log n+Real.log n := by
    rw [←Real.log_mul (by positivity : (n:ℝ) ≠ 0) (by positivity : (n:ℝ) ≠ 0)]
    apply Real.log_le_log hb0
    change ((2*n+1:ℕ):ℝ) ≤ _
    push_cast
    have h3 : 3≤(n:ℝ) := by exact_mod_cast hn'
    nlinarith [mul_nonneg (show 0≤(n:ℝ)-3 by linarith) (show 0≤(n:ℝ) by positivity)]
  have hdec : (B:ℝ)*Real.exp (-2*(1/100:ℝ)^2*(Real.log n)^2) ≤ (B:ℝ)⁻¹ := by
    have h' : -2*(1/100:ℝ)^2*(Real.log n)^2 ≤ -(Real.log (B:ℝ)+Real.log (B:ℝ)) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hn) (show 0≤Real.log n by linarith)]
    have hh := Real.exp_le_exp.mpr h'
    rw [Real.exp_neg,Real.exp_add,Real.exp_log hb0] at hh
    calc _ ≤ (B:ℝ)*((B:ℝ)*(B:ℝ))⁻¹ := mul_le_mul_of_nonneg_left hh hb0.le
         _ = _ := by field_simp
  let t := Nat.log B s
  obtain ⟨S,hS,hs,hbnd⟩ := finite_cover m n t P (1/100) ((Real.log n)^2) (by norm_num)
      (sq_pos_of_pos (by linarith)) hP
  refine ⟨S,hS,hs.trans (Nat.pow_log_le_self B hspos.ne'),?_⟩
  intro r p hp
  have hc : (s:ℝ) < (B:ℝ)^(t+1) := by exact_mod_cast Nat.lt_pow_succ_log_self hb s
  calc _ ≤ _ := hbnd r p hp
       _ ≤ (2:ℝ)^r*((B:ℝ)⁻¹)^(t+1) := by
         apply mul_le_mul_of_nonneg_left _ (by positivity)
         exact pow_le_pow_left₀ (mul_nonneg hb0.le (Real.exp_pos _).le) hdec _
       _ ≤ (2:ℝ)^r/s := by
         rw [inv_pow,←div_eq_mul_inv]
         exact div_le_div_of_nonneg_left (by positivity) (Nat.cast_pos.mpr hspos) hc.le
private lemma large_cover (m n r : ℕ) (P : Fin n→Finset (Fin m)) (hn : 20000≤Real.log n)
    (hP : ∀ j,(Real.log n)^2≤((P j).card:ℝ)) :
    ∃ S : Finset (Fin n→ℝ), cube S ∧ S.card≤100*2^r ∧
      ∀ p,source r p → missed p P S (1/100) ≤ 1/100 := by
  obtain ⟨S,hS,hs,h⟩ := budget_cover m n (100*2^r) P (by positivity) hn hP
  refine ⟨S,hS,hs,fun p hp => (h r p hp).trans_eq ?_⟩
  push_cast
  field_simp
private lemma grid_cover (m n : ℕ) (P : Fin n→Finset (Fin m)) :
    ∃ S : Finset (Fin n→ℝ), cube S ∧ S.card≤101^n ∧
      ∀ p,missed p P S (1/100)=0 := by
  classical
  let points := fun (a : Fin n→Fin 101) (i : Fin n) => ((a i).val:ℝ)/100
  let S := (univ : Finset (Fin n→Fin 101)).image points
  refine ⟨S,?_,card_image_le.trans (by simp),?_⟩
  · intro z hz j
    obtain ⟨a,_,rfl⟩ := mem_image.mp hz
    have hu : (a j).val≤100 := by omega
    dsimp [points]
    exact ⟨by positivity,by exact (div_le_one (by norm_num)).mpr (by exact_mod_cast hu)⟩
  intro p
  apply sum_eq_zero
  intro b _
  have approx (i : Fin n) : ∃ a : Fin 101, |((a:ℕ):ℝ)/100-readings P b i| ≤ 1/100 := by
    let y := readings P b i
    have hy := reading_mem P b i
    have hl : 0≤100*y := by dsimp [y]; linarith [hy.1]
    have hu : (⌊100*y⌋₊:ℝ) ≤ 100 := (Nat.floor_le hl).trans (by dsimp [y]; linarith [hy.2])
    refine ⟨⟨⌊100*y⌋₊,Nat.lt_succ_of_le (by exact_mod_cast hu)⟩,?_⟩
    change |(⌊100*y⌋₊:ℝ)/100-y|≤1/100
    rw [abs_le]
    constructor <;> linarith [Nat.floor_le hl,Nat.lt_floor_add_one (100*y)]
  choose a ha using approx
  exact if_pos ⟨points a,mem_image_of_mem _ (mem_univ a),ha⟩
private lemma all_cover : ∃ C : ℕ, ∀ (m n r : ℕ) (P : Fin n→Finset (Fin m)),
      (∀ j,(Real.log n)^2 ≤ ((P j).card:ℝ)) →
      ∃ S : Finset (Fin n→ℝ), cube S ∧ S.card ≤ C*2^r ∧
        ∀ p, source r p → missed p P S (1/100) ≤ 1/100 := by
  let N := ⌈Real.exp 20000⌉₊
  refine ⟨max 100 (101^N),?_⟩
  intro m n r P hP
  rcases le_or_gt 20000 (Real.log n) with h|h
  · obtain ⟨S,hS,hs,h⟩ := large_cover m n r P h hP
    exact ⟨S,hS,hs.trans (Nat.mul_le_mul_right _ (le_max_left _ _)),h⟩
  · have hn : n≤N := by
      rcases Nat.eq_zero_or_pos n with hz|hp
      · simp [hz]
      · have h' := Real.exp_lt_exp.mpr h
        rw [Real.exp_log (Nat.cast_pos.mpr hp)] at h'
        exact_mod_cast h'.le.trans (Nat.le_ceil (Real.exp 20000))
    obtain ⟨S,hS,hs,hm⟩ := grid_cover m n P
    refine ⟨S,hS,?_,fun p _ => by rw [hm]; norm_num⟩
    calc S.card ≤ 101^n := hs
         _ ≤ 101^N := Nat.pow_le_pow_right (by norm_num) hn
         _ ≤ max 100 (101^N) := le_max_right _ _
         _ ≤ _ := Nat.le_mul_of_pos_right _ (by positivity)
end OMA.S_mo_198378
open OMA.S_mo_198378
theorem OMA.solution : type_of% @OMA.S_mo_198378.main := ⟨finite_cover,budget_cover,large_cover,all_cover⟩
