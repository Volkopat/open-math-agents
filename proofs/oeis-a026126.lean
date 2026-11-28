import OMAStatements.S_oeis_a026126

namespace WalkMotzkin
open OMA.S_oeis_a026126 PowerSeries

private def mot : ℕ → ℚ
  | 0 => 1
  | 1 => 1
  | n+2 => mot (n+1) + ∑ x : ↥(Finset.HasAntidiagonal.antidiagonal n), mot x.val.1 * mot x.val.2
termination_by n => n
decreasing_by all_goals first | omega | (have hx := Finset.HasAntidiagonal.mem_antidiagonal.mp x.property; omega)

private theorem shift_one (s : PowerSeries ℚ) (j : ℕ) :
    coeff (j+1) (X*s) = coeff j s := by simp

theorem exists_mot : ∃ M : PowerSeries ℚ, M = 1 + X*M + X^2*M^2 := by
  refine ⟨PowerSeries.mk mot, ?_⟩
  ext n
  rcases n with _|n
  · simp [coeff_zero_eq_constantCoeff_apply,constantCoeff_mk,mot]
  rcases n with _|n
  · simp [coeff_one,coeff_X_pow_mul',coeff_mk,mot]
  · simp only [map_add, coeff_one, if_neg (show n+2 ≠ 0 by omega), zero_add]
    rw [shift_one _ (n+1), coeff_X_pow_mul _ 2 n, pow_two, coeff_mul]
    simp only [coeff_mk]
    rw [mot]
    congr 1
    exact Finset.sum_attach _ (fun x : ℕ × ℕ => mot x.1 * mot x.2)


private def Valid (n : ℕ) (s : Fin (n+1)→ℕ) : Prop :=
  s 0 = 1 ∧ ∀ i : Fin n, if i.val = 0 then |(s i.succ : ℤ) - (s i.castSucc : ℤ)| = 1
    else |(s i.succ : ℤ) - (s i.castSucc : ℤ)| ≤ 1

private def sn {n : ℕ} (v : ℕ) : (Fin n → ℕ) ↪ (Fin (n+1) → ℕ) :=
  ⟨fun x => Fin.snoc x v, Fin.snoc_left_injective (α := fun _ => ℕ) _⟩

private def prev {α : Type} [DecidableEq α] (f : ℕ → Finset α) : ℕ → Finset α
  | 0 => f 0 ∪ f 1
  | h+1 => (f h ∪ f (h+1)) ∪ f (h+2)

private def paths : (n : ℕ) → ℕ → Finset (Fin (n+1) → ℕ)
  | 0,h => if h=1 then {fun _ => 1} else ∅
  | 1,h => if h=0 ∨ h=2 then {fun i => if i.val=0 then 1 else h} else ∅
  | n+2,h => (prev (paths (n+1)) h).map (sn h)

private theorem valid_snoc {n : ℕ} (x : Fin (n+2)→ℕ) (v : ℕ) :
    Valid (n+2) (sn v x) ↔ Valid (n+1) x ∧ |(v:ℤ)-x (Fin.last (n+1))| ≤ 1 := by
  have hzero : (sn v x) 0 = x 0 := by
    exact Fin.snoc_castSucc (α := fun _ => ℕ) v x 0
  refine ⟨fun ⟨h0,h⟩ => ⟨⟨hzero ▸ h0,fun i => ?_⟩,?_⟩,fun ⟨⟨h0,h⟩,hv⟩ => ⟨hzero.trans h0,?_⟩⟩
  · simpa only [sn,Function.Embedding.coeFn_mk,Fin.val_castSucc,Fin.succ_castSucc,Fin.snoc_castSucc] using h i.castSucc
  · simpa [sn,Fin.succ_last] using h (Fin.last (n+1))
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [sn,Fin.succ_last] using hv
    · simpa only [sn,Function.Embedding.coeFn_mk,Fin.val_castSucc,Fin.succ_castSucc,Fin.snoc_castSucc] using h j


private theorem prev_iff {n : ℕ} (f : ℕ → Finset (Fin (n+1)→ℕ))
    (hf : ∀ h x, x ∈ f h ↔ Valid n x ∧ x (Fin.last n) = h) (h : ℕ) (x : Fin (n+1)→ℕ) :
    x ∈ prev f h ↔ Valid n x ∧ |(h:ℤ)-x (Fin.last n)| ≤ 1 := by
  cases h <;> simp only [prev, Finset.mem_union, hf, abs_le] <;> push_cast <;>
    by_cases hv : Valid n x <;> simp [hv] <;> omega

private theorem mem_paths (n h : ℕ) (s : Fin (n+1)→ℕ) :
    s ∈ paths n h ↔ Valid n s ∧ s (Fin.last n)=h := by
  induction n using Nat.twoStepInduction generalizing h with
  | zero =>
    change (s ∈ (if h=1 then {fun _ : Fin 1 => 1} else ∅)) ↔ (s 0 = 1 ∧ _) ∧ s 0 = h
    simp only [Fin.forall_fin_zero, and_true]
    split_ifs with hh
    · subst h; simp only [Finset.mem_singleton,and_self]
      exact ⟨fun e => congrFun e 0, fun h0 => funext fun i => by fin_cases i; exact h0⟩
    · simp; omega
  | one =>
    have v : Valid 1 s ↔ s 0 = 1 ∧ |(s 1 : ℤ) - s 0| = 1 := by simp [Valid, Fin.forall_fin_one]
    rw [v]
    change s ∈ (if h=0 ∨ h=2 then {fun i : Fin 2 => if i.val=0 then 1 else h} else ∅) ↔
      (s 0=1 ∧ |(s 1:ℤ)-s 0|=1) ∧ s 1=h
    split_ifs with hh
    · simp only [Finset.mem_singleton]
      constructor
      · rintro rfl; rcases hh with rfl|rfl <;> decide
      · rintro ⟨⟨h0,_⟩,he⟩; funext i; fin_cases i <;> assumption
    · simp only [Finset.notMem_empty,false_iff,not_and]; intro hv he
      rcases hv with ⟨hv,ha⟩; rw [hv,he] at ha; rw [abs_eq (by norm_num)] at ha; omega
  | more n _ ih =>
    simp only [paths,Finset.mem_map]
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨(valid_snoc x h).mpr ((prev_iff _ ih h x).mp hx), by simp [sn]⟩
    · rintro ⟨vs,hs⟩
      have e : sn h (Fin.init s)=s := by rw [← hs]; exact Fin.snoc_init_self s
      refine ⟨Fin.init s,(prev_iff _ ih h _).mpr ((valid_snoc _ _).mp (by rw [e]; exact vs)),e⟩


private theorem agrees (n : ℕ) (s : Fin (n+1)→ℕ) : s ∈ walks n ↔ s ∈ paths n 5 := by
  rw [mem_paths]
  constructor
  · rintro ⟨h0,he,h1,hd⟩
    refine ⟨⟨h0 0 rfl, fun i => ?_⟩,he _ rfl⟩
    split_ifs with hi
    · exact h1 _ _ rfl (by change i.val+1 ≤ 1; omega)
    · exact hd _ _ rfl (by change 1 < i.val+1; omega)
  · rintro ⟨⟨h0,hs⟩,he⟩
    have hb (i j : Fin (n+1)) (hji : j.val = i.val+1) :
        if i.val=0 then |(s j : ℤ) - s i| = 1 else |(s j : ℤ)-s i| ≤ 1 := by
      let k : Fin n := ⟨i.val,by have := j.isLt;omega⟩
      have ei : i=k.castSucc := Fin.ext rfl
      have ej : j=k.succ := Fin.ext hji
      rw [ei,ej]; exact hs k
    refine ⟨fun i hi => ?_,fun i hi => ?_,fun i j hji hj => ?_,fun i j hji hj => ?_⟩
    · exact (congrArg s (Fin.ext hi)).trans h0
    · exact (congrArg s (Fin.ext hi)).trans he
    · simpa [show i.val=0 by omega] using hb i j hji
    · simpa [show i.val≠0 by omega] using hb i j hji

private theorem acard (n : ℕ) : a n = (paths n 5).card := by
  have e : walks n = (paths n 5 : Set (Fin (n+1)→ℕ)) := Set.ext (agrees n)
  simp [a,e]

private theorem disjoint_paths (n : ℕ) {i j : ℕ} (h : i≠j) : Disjoint (paths n i) (paths n j) := by
  apply Finset.disjoint_left.mpr
  intro s hs ht
  exact h (((mem_paths _ _ _).mp hs).2.symm.trans ((mem_paths _ _ _).mp ht).2)

private theorem count_zero (n : ℕ) : (paths (n+2) 0).card =
    (paths (n+1) 0).card + (paths (n+1) 1).card := by
  simp [paths,prev,Finset.card_union_of_disjoint (disjoint_paths _ (by decide : 0≠1))]

private theorem count_pos (n h : ℕ) : (paths (n+2) (h+1)).card =
    (paths (n+1) h).card + (paths (n+1) (h+1)).card + (paths (n+1) (h+2)).card := by
  have dh : Disjoint (paths (n+1) h) (paths (n+1) (h+1)) := disjoint_paths _ (by omega)
  have dl : Disjoint (paths (n+1) h ∪ paths (n+1) (h+1)) (paths (n+1) (h+2)) :=
    Finset.disjoint_union_left.mpr ⟨disjoint_paths _ (by omega),disjoint_paths _ (by omega)⟩
  simp only [paths, prev, Finset.card_map, Finset.card_union_of_disjoint dl,Finset.card_union_of_disjoint dh]


private noncomputable def row (M : PowerSeries ℚ) : ℕ → PowerSeries ℚ
  | 0 => (1-X)*M*(X*M)
  | h+1 => (1-X)*M*(X*M)^h*(1+(X*M)^2)

private theorem row_zero (M : PowerSeries ℚ) (hm : M=1+X*M+X^2*M^2) :
    row M 0 = X*(row M 0 + row M 1) := by
  simp only [row,pow_zero,mul_one]
  linear_combination (1-X)*X*M*hm

private theorem row_pos (M : PowerSeries ℚ) (hm : M=1+X*M+X^2*M^2) (h : ℕ) :
    row M (h+1) = (if h=0 then 1-X else 0) + X*(row M h + row M (h+1) + row M (h+2)) := by
  cases h with
  | zero =>
    simp only [row,pow_zero,pow_one,mul_one, ↓reduceIte]
    linear_combination (1-X)*(1+(X*M)^2)*hm
  | succ h =>
    simp only [row,pow_succ, if_neg (Nat.succ_ne_zero h), zero_add]
    linear_combination (1-X)*X*M*(X*M)^h*(1+(X*M)^2)*hm

private theorem row_base (M : PowerSeries ℚ) (hm : M=1+X*M+X^2*M^2) (h : ℕ) :
    coeff 0 (row M h) = if h=1 then 1 else 0 := by
  have m0 : constantCoeff M=1 := by simpa using congrArg constantCoeff hm
  rcases h with _|(_|h) <;> simp [row,coeff_zero_eq_constantCoeff_apply,m0]

private theorem row_card (M : PowerSeries ℚ) (hm : M=1+X*M+X^2*M^2) (n h : ℕ) :
    coeff n (row M h) = ((paths n h).card : ℚ) := by
  induction n using Nat.twoStepInduction generalizing h with
  | zero =>
    rw [row_base _ hm]; simp only [paths]; split_ifs <;> simp
  | one =>
    cases h with
    | zero =>
      rw [row_zero M hm, shift_one _ 0, map_add, row_base M hm, row_base M hm]
      norm_num [paths]
    | succ h =>
      rw [row_pos M hm h,map_add,shift_one _ 0]
      simp only [map_add,row_base M hm,paths]
      split_ifs <;> simp_all [coeff_one]
  | more n _ ih =>
    cases h with
    | zero =>
      rw [row_zero M hm,shift_one,map_add,ih,ih,count_zero]
      simp
    | succ h =>
      rw [row_pos M hm h,map_add,shift_one,map_add,map_add,ih,ih,ih,count_pos]
      split_ifs <;> simp [coeff_one,coeff_X]

/-- The Motzkin generating function and the second difference of A005325 are
both recorded in OEIS A026126. We derive the series from the registered walks. -/
noncomputable def G (M : PowerSeries ℚ) := X^4*(1-X)^2*M^6

theorem bridge (M : PowerSeries ℚ) (hm : M = 1+X*M+X^2*M^2) (n : ℕ) :
    (a n : ℚ) = coeff n (G M) := by
  have e : G M = row M 5 := by
    simp only [G,row]
    linear_combination X^4*(1-X)*M^5*hm
  rw [e,acard]
  exact (row_card M hm n 5).symm

end WalkMotzkin
namespace WalkMotzkin
open OMA.S_oeis_a026126 PowerSeries

noncomputable def E (s : PowerSeries ℚ) : PowerSeries ℚ :=
  X * PowerSeries.derivative ℚ s

noncomputable def operator (G : PowerSeries ℚ) : PowerSeries ℚ :=
  -(E (E G)) - 4*E G + 32*G + X*(4*E (E G)+13*E G-64*G) +
  X^2*(-2*E (E G)+5*E G+56*G) + X^3*(-4*E (E G)-17*E G) +
  X^4*(3*E (E G)+3*E G)

private theorem coeff_E (s : PowerSeries ℚ) (n : ℕ) : coeff n (E s) = n * coeff n s := by
  cases n with
  | zero => simp [E]
  | succ n =>
    rw [E,shift_one,coeff_derivative,Nat.cast_succ,mul_comm]

private theorem coeff_num (s : PowerSeries ℚ) (m n : ℕ) [m.AtLeastTwo] :
    coeff n (ofNat(m)*s) = ofNat(m) * coeff n s := by
  change coeff n ((m : PowerSeries ℚ)*s) = (m : ℚ)*coeff n s
  simp only [← nsmul_eq_mul,map_nsmul]

private theorem extract (G : PowerSeries ℚ) (ha : ∀ n, (a n : ℚ) = coeff n G)
    (hd : operator G = 0) : type_of% @OMA.S_oeis_a026126.main := by
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k, n = k+8 := ⟨n-8,by omega⟩
  have hx (s : PowerSeries ℚ) : coeff (k+8) (X*s) = coeff (k+7) s := shift_one _ _
  have h2 (s : PowerSeries ℚ) : coeff (k+8) (X^2*s) = coeff (k+6) s := coeff_X_pow_mul s 2 (k+6)
  have h3 (s : PowerSeries ℚ) : coeff (k+8) (X^3*s) = coeff (k+5) s := coeff_X_pow_mul s 3 (k+5)
  have h4 (s : PowerSeries ℚ) : coeff (k+8) (X^4*s) = coeff (k+4) s := coeff_X_pow_mul s 4 (k+4)
  have hc := congrArg (coeff (k+8)) hd
  simp only [operator, map_add, map_sub, map_neg, map_zero, hx,h2,h3,h4,neg_mul,
    coeff_num,
    coeff_E,← ha,Nat.cast_add,Nat.cast_ofNat] at hc
  have h1n : k+8-1=k+7 := by omega
  have h2n : k+8-2=k+6 := by omega
  have h3n : k+8-3=k+5 := by omega
  have h4n : k+8-4=k+4 := by omega
  rw [h1n,h2n,h3n,h4n]
  apply (Int.cast_inj (α:=ℚ)).mp
  push_cast
  linear_combination hc

theorem from_operator (M : PowerSeries ℚ) (hm : M = 1+X*M+X^2*M^2)
    (hd : operator (G M)=0) : type_of% @OMA.S_oeis_a026126.main :=
  extract _ (bridge M hm) hd

end WalkMotzkin
namespace WalkMotzkin
open PowerSeries
private abbrev PS := PowerSeries ℚ
private theorem e_add (a b : PS) : E (a+b) = E a+E b := by simp [E,mul_add]
private theorem e_sub (a b : PS) : E (a-b) = E a-E b := by simp [E,mul_sub]
private theorem e_mul (a b : PS) : E (a*b) = E a*b+a*E b := by
  simp only [E,Derivation.leibniz,smul_eq_mul]; ring
private theorem e_pow (a : PS) (n : ℕ) : E (a^n) = n*a^(n-1)*E a := by
  simp only [E,PowerSeries.derivative_pow]; ring
private theorem e_X : E (X : PS) = X := by simp [E]
private theorem e_one : E (1 : PS) = 0 := by simp [E]
private theorem e_num (n : ℕ) : E (n : PS)=0 := by simp [E,Derivation.map_natCast]

set_option maxHeartbeats 1200000 in
theorem motzkin_operator (M : PS) (hm : M=1+X*M+X^2*M^2) :
    operator (G M)=0 := by
  let w : PS := X*M
  have hw : w=X*(1+w+w^2) := by dsimp [w]; linear_combination X*hm
  have hg : G M = (w^8 + 2*w^6 + w^4) := by
    dsimp only [G,w]; linear_combination (X*M)^4*((1-X)*M+1+(X*M)^2)*hm
  rw [hg]
  let v := E w
  let b := E v
  let d : PS := 1-X*(1+2*w)
  let L : PS := 8*w^7 + 12*w^5 + 4*w^3
  let J : PS := 56*w^6 + 60*w^4 + 12*w^2
  have hd : d ≠ 0 := by intro h; have hh := congrArg PowerSeries.constantCoeff h; simp [d] at hh
  have h₁ : d*v=w := by
    have h := congrArg E hw
    simp only [e_mul,e_add,e_X,e_pow,e_one,Nat.cast_ofNat] at h
    norm_num at h
    dsimp only [d,v]
    linear_combination h-hw
  have h₂ : d*b=(2-d)*v+2*X*v^2 := by
    have h := congrArg E h₁
    change E ((1-X*(1+2*w))*v) = E w at h
    simp only [e_mul,e_add,e_sub,e_one,e_X,show E (2 : PS)=0 from e_num 2] at h
    dsimp only [d,b]
    change (0-(X*(1+2*w)+X*(0+(0*w+2*v))))*v+(1-X*(1+2*w))*E v=v at h
    linear_combination h
  have h₃ : E (w^8 + 2*w^6 + w^4)=L*v := by
    simp only [e_add,e_mul,e_pow,show E (2 : PS)=0 from e_num 2]
    dsimp only [L,v]; norm_num; ring
  have hL : E L=J*v := by
    dsimp only [L,J,v]
    simp only [e_add,e_mul,e_pow,show E (4 : PS)=0 from e_num 4,
      show E (8 : PS)=0 from e_num 8,
      show E (12 : PS)=0 from e_num 12]
    norm_num; ring
  have h₄ : E (E (w^8 + 2*w^6 + w^4)) = J*v^2+L*b := by
    rw [h₃,e_mul,hL]; dsimp only [b]; ring
  apply (mul_eq_zero.mp (show d^3 * operator (w^8 + 2*w^6 + w^4) = 0 from ?_)).resolve_left (pow_ne_zero _ hd)
  unfold operator; rw [h₄,h₃]
  let A : PS := 3*X^4 - 4*X^3 - 2*X^2 + 4*X - 1
  let B : PS := 3*X^4 - 17*X^3 + 5*X^2 + 13*X - 4
  let Q : PS := 8*w^4*(56*w^5*X^4 - 64*w^5*X^3 + 32*w^5*X^2 + 80*w^4*X^4 - 88*w^4*X^3 + 12*w^4*X^2 - 4*w^4*X + 118*w^3*X^4 - 172*w^3*X^3 + 54*w^3*X^2 + 32*w^3*X - 8*w^3 + 95*w^2*X^4 - 149*w^2*X^3 + 81*w^2*X^2 - 27*w^2*X + 59*w*X^4 - 104*w*X^3 + 24*w*X^2 + 28*w*X - 7*w + 21*X^4 - 63*X^3 + 63*X^2 - 21*X)
  linear_combination (norm := (dsimp only [A,B,Q,d,J,L]; ring))
    A*L*d^2*h₂ +
    (A*(d*J+2*X*L)*(d*v+w)+A*d*L*(2-d)+B*d^2*L)*h₁ + Q*hw
end WalkMotzkin

theorem OMA.solution : type_of% @OMA.S_oeis_a026126.main := by
  obtain ⟨M,hm⟩ := WalkMotzkin.exists_mot
  exact WalkMotzkin.from_operator M hm (WalkMotzkin.motzkin_operator M hm)
