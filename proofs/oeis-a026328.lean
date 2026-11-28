import OMAStatements.S_oeis_a026328

namespace WalkMotzkin
open OMA.S_oeis_a026328 PowerSeries

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
  s 0 = 2 ∧ ∀ i : Fin n, |(s i.succ : ℤ) - (s i.castSucc : ℤ)| ≤ 1

private def sn {n : ℕ} (v : ℕ) : (Fin n → ℕ) ↪ (Fin (n+1) → ℕ) :=
  ⟨fun x => Fin.snoc x v, Fin.snoc_left_injective (α := fun _ => ℕ) _⟩

private def prev {α : Type} [DecidableEq α] (f : ℕ → Finset α) : ℕ → Finset α
  | 0 => f 0 ∪ f 1
  | h+1 => (f h ∪ f (h+1)) ∪ f (h+2)

private def paths : (n : ℕ) → ℕ → Finset (Fin (n+1) → ℕ)
  | 0,h => if h=2 then {fun _ => 2} else ∅
  | n+1,h => (prev (paths n) h).map (sn h)

private theorem valid_snoc {n : ℕ} (x : Fin (n+1)→ℕ) (v : ℕ) :
    Valid (n+1) (sn v x) ↔ Valid n x ∧ |(v:ℤ)-x (Fin.last n)| ≤ 1 := by
  have hzero : (sn v x) 0 = x 0 := Fin.snoc_castSucc (α := fun _ => ℕ) v x 0
  refine ⟨fun ⟨h0,h⟩ => ⟨⟨hzero ▸ h0,fun i => ?_⟩,?_⟩,fun ⟨⟨h0,h⟩,hv⟩ => ⟨hzero.trans h0,?_⟩⟩
  · simpa only [sn,Function.Embedding.coeFn_mk,Fin.succ_castSucc,Fin.snoc_castSucc] using h i.castSucc
  · simpa [sn,Fin.succ_last] using h (Fin.last n)
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [sn,Fin.succ_last] using hv
    · simpa only [sn,Function.Embedding.coeFn_mk,Fin.succ_castSucc,Fin.snoc_castSucc] using h j

private theorem prev_iff {n : ℕ} (f : ℕ → Finset (Fin (n+1)→ℕ))
    (hf : ∀ h x, x ∈ f h ↔ Valid n x ∧ x (Fin.last n) = h) (h : ℕ) (x : Fin (n+1)→ℕ) :
    x ∈ prev f h ↔ Valid n x ∧ |(h:ℤ)-x (Fin.last n)| ≤ 1 := by
  cases h <;> simp only [prev, Finset.mem_union, hf, abs_le] <;> push_cast <;>
    by_cases hv : Valid n x <;> simp [hv] <;> omega

private theorem mem_paths (n h : ℕ) (s : Fin (n+1)→ℕ) :
    s ∈ paths n h ↔ Valid n s ∧ s (Fin.last n)=h := by
  induction n generalizing h with
  | zero =>
    change (s ∈ (if h=2 then {fun _ : Fin 1 => 2} else ∅)) ↔ (s 0 = 2 ∧ _) ∧ s 0 = h
    simp only [Fin.forall_fin_zero, and_true]
    split_ifs with hh
    · subst h; simp only [Finset.mem_singleton,and_self]
      exact ⟨fun e => congrFun e 0, fun h0 => funext fun i => by fin_cases i; exact h0⟩
    · simp; omega
  | succ n ih =>
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
  · rintro ⟨h0,he,hd⟩
    exact ⟨⟨h0 0 rfl, fun i => hd _ _ rfl⟩,he _ rfl⟩
  · rintro ⟨⟨h0,hs⟩,he⟩
    refine ⟨fun i hi => ?_,fun i hi => ?_,fun i j hji => ?_⟩
    · exact (congrArg s (Fin.ext hi)).trans h0
    · exact (congrArg s (Fin.ext hi)).trans he
    · let k : Fin n := ⟨i.val,by have := j.isLt;omega⟩
      have ei : i=k.castSucc := Fin.ext rfl
      have ej : j=k.succ := Fin.ext hji
      rw [ei,ej]; exact hs k

private theorem acard (n : ℕ) : a n = (paths n 5).card := by
  have e : walks n = (paths n 5 : Set (Fin (n+1)→ℕ)) := Set.ext (agrees n)
  simp [a,e]

private theorem disjoint_paths (n : ℕ) {i j : ℕ} (h : i≠j) : Disjoint (paths n i) (paths n j) := by
  apply Finset.disjoint_left.mpr
  intro s hs ht
  exact h (((mem_paths _ _ _).mp hs).2.symm.trans ((mem_paths _ _ _).mp ht).2)

private theorem count_zero (n : ℕ) : (paths (n+1) 0).card =
    (paths n 0).card + (paths n 1).card := by
  simp [paths,prev,Finset.card_union_of_disjoint (disjoint_paths _ (by decide : 0≠1))]

private theorem count_pos (n h : ℕ) : (paths (n+1) (h+1)).card =
    (paths n h).card + (paths n (h+1)).card + (paths n (h+2)).card := by
  have dh : Disjoint (paths n h) (paths n (h+1)) := disjoint_paths _ (by omega)
  have dl : Disjoint (paths n h ∪ paths n (h+1)) (paths n (h+2)) :=
    Finset.disjoint_union_left.mpr ⟨disjoint_paths _ (by omega),disjoint_paths _ (by omega)⟩
  simp only [paths, prev, Finset.card_map, Finset.card_union_of_disjoint dl,Finset.card_union_of_disjoint dh]


private noncomputable def row (M : PowerSeries ℚ) : ℕ → PowerSeries ℚ
  | 0 => M*(X*M)^2
  | 1 => M*(X*M)*(1+(X*M)^2)
  | h+2 => M*(X*M)^h*(1+(X*M)^2+(X*M)^4)

private theorem row_zero (M : PowerSeries ℚ) (hm : M=1+X*M+X^2*M^2) :
    row M 0 = X*(row M 0 + row M 1) := by
  simp only [row]
  linear_combination X^2*M^2*hm

private theorem row_pos (M : PowerSeries ℚ) (hm : M=1+X*M+X^2*M^2) (h : ℕ) :
    row M (h+1) = (if h=1 then 1 else 0) + X*(row M h + row M (h+1) + row M (h+2)) := by
  rcases h with _|(_|h)
  · simp only [row, pow_zero, mul_one, zero_ne_one, ↓reduceIte,zero_add]
    linear_combination X*M*(1+(X*M)^2)*hm
  · simp only [row,pow_zero,pow_one,mul_one, ↓reduceIte]
    linear_combination (1+(X*M)^2+(X*M)^4)*hm
  · simp only [row,pow_succ,if_neg (show h+1+1 ≠ 1 by omega),zero_add]
    linear_combination X*M*(X*M)^h*(1+(X*M)^2+(X*M)^4)*hm

private theorem row_base (M : PowerSeries ℚ) (hm : M=1+X*M+X^2*M^2) (h : ℕ) :
    coeff 0 (row M h) = if h=2 then 1 else 0 := by
  have m0 : constantCoeff M=1 := by simpa using congrArg constantCoeff hm
  rcases h with _|(_|(_|h)) <;> simp [row,coeff_zero_eq_constantCoeff_apply,m0]

private theorem row_card (M : PowerSeries ℚ) (hm : M=1+X*M+X^2*M^2) (n h : ℕ) :
    coeff n (row M h) = ((paths n h).card : ℚ) := by
  induction n generalizing h with
  | zero =>
    rw [row_base _ hm]; simp only [paths]; split_ifs <;> simp
  | succ n ih =>
    cases h with
    | zero =>
      rw [row_zero M hm,shift_one,map_add,ih,ih,count_zero]
      simp
    | succ h =>
      rw [row_pos M hm h,map_add,shift_one,map_add,map_add,ih,ih,ih,count_pos]
      split_ifs <;> simp [coeff_one]

noncomputable def G (M : PowerSeries ℚ) := M*(X*M)^3*(1+(X*M)^2+(X*M)^4)

theorem bridge (M : PowerSeries ℚ) (hm : M = 1+X*M+X^2*M^2) (n : ℕ) :
    (a n : ℚ) = coeff n (G M) := by
  rw [acard]
  exact (row_card M hm n 5).symm

end WalkMotzkin
namespace WalkMotzkin
open OMA.S_oeis_a026328 PowerSeries

noncomputable def E (s : PowerSeries ℚ) : PowerSeries ℚ :=
  X * PowerSeries.derivative ℚ s

noncomputable def operator (G : PowerSeries ℚ) : PowerSeries ℚ :=
  -(E (E G)) - 6*E G + 27*G + X*(6*E (E G)+33*E G-101*G) +
  X^2*(-9*E (E G)-39*E G+110*G) + X^3*(-4*E (E G)-36*E G-56*G) +
  X^4*(12*E (E G)+60*E G+72*G)


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
    (hd : operator G = 0) : type_of% @OMA.S_oeis_a026328.main := by
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k, n = k+7 := ⟨n-7,by omega⟩
  have hx (s : PowerSeries ℚ) : coeff (k+7) (X*s) = coeff (k+6) s := shift_one _ _
  have h2 (s : PowerSeries ℚ) : coeff (k+7) (X^2*s) = coeff (k+5) s := coeff_X_pow_mul s 2 (k+5)
  have h3 (s : PowerSeries ℚ) : coeff (k+7) (X^3*s) = coeff (k+4) s := coeff_X_pow_mul s 3 (k+4)
  have h4 (s : PowerSeries ℚ) : coeff (k+7) (X^4*s) = coeff (k+3) s := coeff_X_pow_mul s 4 (k+3)
  have hc := congrArg (coeff (k+7)) hd
  simp only [operator, map_add, map_sub, map_neg, map_zero, hx,h2,h3,h4,neg_mul,
    coeff_num,
    coeff_E,← ha,Nat.cast_add,Nat.cast_ofNat] at hc
  have h1n : k+7-1=k+6 := by omega
  have h2n : k+7-2=k+5 := by omega
  have h3n : k+7-3=k+4 := by omega
  have h4n : k+7-4=k+3 := by omega
  rw [h1n,h2n,h3n,h4n]
  apply (Int.cast_inj (α:=ℚ)).mp
  push_cast
  linear_combination hc

theorem from_operator (M : PowerSeries ℚ) (hm : M = 1+X*M+X^2*M^2)
    (hd : operator (G M)=0) : type_of% @OMA.S_oeis_a026328.main :=
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

set_option maxHeartbeats 1600000 in
theorem motzkin_operator (M : PS) (hm : M=1+X*M+X^2*M^2) :
    operator (G M)=0 := by
  let w : PS := X*M
  have hw : w=X*(1+w+w^2) := by dsimp [w]; linear_combination X*hm
  have hg : G M = (w^9 + w^8 + 2*w^7 + w^6 + 2*w^5 + w^4 + w^3) := by
    dsimp only [G,w]; linear_combination (X*M)^3*(1+(X*M)^2+(X*M)^4)*hm
  rw [hg]
  let v := E w
  let b := E v
  let d : PS := 1-X*(1+2*w)
  let L : PS := 9*w^8 + 8*w^7 + 14*w^6 + 6*w^5 + 10*w^4 + 4*w^3 + 3*w^2
  let J : PS := 72*w^7 + 56*w^6 + 84*w^5 + 30*w^4 + 40*w^3 + 12*w^2 + 6*w
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
  have h₃ : E (w^9 + w^8 + 2*w^7 + w^6 + 2*w^5 + w^4 + w^3)=L*v := by
    simp only [e_add,e_mul,e_pow,show E (2 : PS)=0 from e_num 2]
    dsimp only [L,v]; norm_num; ring
  have hL : E L=J*v := by
    dsimp only [L,J,v]
    simp only [e_add,e_mul,e_pow,show E (3 : PS)=0 from e_num 3,
      show E (4 : PS)=0 from e_num 4,
      show E (6 : PS)=0 from e_num 6,
      show E (8 : PS)=0 from e_num 8,
      show E (9 : PS)=0 from e_num 9,
      show E (10 : PS)=0 from e_num 10,
      show E (14 : PS)=0 from e_num 14]
    norm_num; ring
  have h₄ : E (E (w^9 + w^8 + 2*w^7 + w^6 + 2*w^5 + w^4 + w^3)) = J*v^2+L*b := by
    rw [h₃,e_mul,hL]; dsimp only [b]; ring
  apply (mul_eq_zero.mp (show d^3 * operator (w^9 + w^8 + 2*w^7 + w^6 + 2*w^5 + w^4 + w^3) = 0 from ?_)).resolve_left (pow_ne_zero _ hd)
  unfold operator; rw [h₄,h₃]
  let A : PS := 12*X^4 - 4*X^3 - 9*X^2 + 6*X - 1
  let B : PS := 60*X^4 - 36*X^3 - 39*X^2 + 33*X - 6
  let Q : PS := w^3*(576*w^7*X^6 - 448*w^7*X^5 + 880*w^7*X^4 - 808*w^7*X^3 + 216*w^7*X^2 + 864*w^6*X^6 - 2688*w^6*X^5 + 2696*w^6*X^4 - 572*w^6*X^3 - 244*w^6*X^2 + 72*w^6*X + 1008*w^5*X^6 - 2896*w^5*X^5 + 5100*w^5*X^4 - 2094*w^5*X^3 - 916*w^5*X^2 + 714*w^5*X - 108*w^5 + 936*w^4*X^6 - 3056*w^4*X^5 + 4550*w^4*X^4 - 2113*w^4*X^3 - 329*w^4*X^2 + 449*w^4*X - 85*w^4 + 1008*w^3*X^6 - 2440*w^3*X^5 + 4556*w^3*X^4 - 2570*w^3*X^3 - 520*w^3*X^2 + 710*w^3*X - 128*w^3 + 936*w^2*X^6 - 2504*w^2*X^5 + 3270*w^2*X^4 - 2313*w^2*X^3 + 607*w^2*X^2 + 81*w^2*X - 45*w^2 + 432*w*X^6 - 1752*w*X^5 + 2748*w*X^4 - 1546*w*X^3 - 16*w*X^2 + 262*w*X - 56*w + 72*X^6 - 416*X^5 + 1022*X^4 - 1109*X^3 + 491*X^2 - 47*X - 13)
  linear_combination (norm := (dsimp only [A,B,Q,d,J,L]; ring))
    A*L*d^2*h₂ +
    (A*(d*J+2*X*L)*(d*v+w)+A*d*L*(2-d)+B*d^2*L)*h₁ + Q*hw
end WalkMotzkin

theorem OMA.solution : type_of% @OMA.S_oeis_a026328.main := by
  obtain ⟨M,hm⟩ := WalkMotzkin.exists_mot
  exact WalkMotzkin.from_operator M hm (WalkMotzkin.motzkin_operator M hm)
