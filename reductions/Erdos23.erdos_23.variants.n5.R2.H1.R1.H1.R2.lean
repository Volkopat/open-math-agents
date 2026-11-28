import OMAReductions.R_Erdos23_erdos_23_variants_n5_R2_H1_R1
import Mathlib

/-! # Removing an adjacent pair from a triangle-free graph on twenty-five vertices

If the remaining graph maps to a pentagon, five cuts with opposite colors on
the selected edge, followed by a neighborhood estimate, give the 25-edge
bipartization bound. All edge sums in this file count both orientations.
-/
namespace OMA.R_Erdos23_erdos_23_variants_n5_R2_H1_R1_H1_R2
open SimpleGraph Finset
open scoped Classical
open OMA.R_Erdos23_erdos_23_variants_n5_R2 (cut_subgraph edge_sum)
open OMA.R_Erdos23_erdos_23_variants_n5_R2_H1_R1 (rootedSums rootedAverage restrictedSum extendHalf)

lemma even_cost (G : SimpleGraph (Fin 25)) (f : Fin 25 → Bool) :
    2 ∣ ∑ i, ∑ j, if G.Adj i j ∧ f i = f j then (1:ℕ) else 0 := by
  classical
  let M : SimpleGraph (Fin 25) := {
    Adj := fun i j => G.Adj i j ∧ f i = f j
    symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
    loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩ }
  exact ⟨M.edgeFinset.card, edge_sum M⟩

lemma root_identity (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3) (v : Fin 25) :
    let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
    let f (i : Fin 25) := decide (G.Adj v i)
    (∑ i,∑ j,if G.Adj i j ∧ f i=f j then (1:ℕ) else 0) +
      2*(∑ i,w v i * ∑ j,w i j) = ∑ i,∑ j,w i j := by
  classical
  intro w f
  have sym (i j : Fin 25) : w i j = w j i := by simp only [w,G.adj_comm i j]
  have eq (i j : Fin 25) :
      (if G.Adj i j ∧ f i=f j then (1:ℕ) else 0) +
        w v i*w i j + w v j*w i j = w i j := by
    by_cases h : G.Adj i j <;> by_cases a : G.Adj v i <;> by_cases b : G.Adj v j <;>
      simp [w,f,h,a,b]
    exact (tri _ (is3Clique_triple_iff.mpr ⟨a,b,h⟩)).elim
  have allEq := sum_congr (s₁:=univ) rfl (fun i _ => sum_congr (s₁:=univ) rfl (fun j _ => eq i j))
  simp only [sum_add_distrib] at allEq
  have both := rootedSums w sym v
  rw [← both]
  simpa only [add_assoc] using allEq

/-- Degree moments in the rooted-neighborhood inequalities. -/
lemma moments (D : Fin 25 → ℤ) (W : Fin 25 → Fin 25 → ℤ) (M : ℤ)
    (sym : ∀ i j, W i j=W j i) (row : ∀ i, ∑ j,W i j=D i)
    (total : (∑ i,D i)=2*M) (bits : ∀ i j, W i j=1 ∨ W i j=0)
    (cap : ∀ v, (∑ i,W v i*D i)+26 ≤ M) :
    M ≤ 121 ∧ (120 ≤ M → ∀ v,D v ≤ 17) := by
  let P (v : Fin 25) := ∑ i,W v i*D i
  change ∀ v,P v+26 ≤ M at cap
  have squares : (∑ i,D i^2) ≤ 25*M-650 := by
    have eq : (∑ v,P v) = ∑ i,D i^2 := by
      dsimp only [P]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      rw [← sum_mul]
      have col : (∑ v,W v i)=D i := (sum_congr rfl (fun v _ => sym v i)).trans (row i)
      rw [col,pow_two]
    have h := sum_le_sum (s := univ) (fun v _ => (show P v ≤ M-26 by linarith [cap v]))
    rw [eq] at h
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at h
    linarith
  let z (i : Fin 25) := 10-D i
  have zsum : (∑ i,z i) = 250-2*M := by simp [z,sum_sub_distrib,total]
  have zsq : (∑ i,z i^2) ≤ 1850-15*M := by
    have eq (i : Fin 25) : z i^2 = 100-20*D i+D i^2 := by dsimp only [z]; ring
    simp only [eq,sum_add_distrib,sum_sub_distrib,← mul_sum,total,sum_const,card_univ,
      Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]
    linarith
  have sum_nonneg : 0 ≤ ∑ i,z i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have one (i : Fin 25) : z i^2 ≤ ∑ j,z j^2 :=
    single_le_sum (fun j _ => sq_nonneg (z j)) (mem_univ i)
  have high (lo : 122 ≤ M) : False := by
    have maxD (v : Fin 25) : D v ≤ 10 := by
      have point (i : Fin 25) : 2*(W v i*z i) ≤ z i^2 + z i := by
        have gap (t : ℤ) : 0 ≤ t*(t-1) := by
          by_cases ht : 1 ≤ t
          · exact mul_nonneg (by omega) (by omega)
          · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
        rcases bits v i with h|h
        · simp only [h,one_mul]
          nlinarith [gap (z i)]
        · simp only [h,zero_mul,mul_zero]
          nlinarith [gap (-(z i))]
      have h := sum_le_sum (s:=univ) (fun i _ => point i)
      simp only [← mul_sum,sum_add_distrib,zsum] at h
      have calcP : (∑ i,W v i*z i) = 10*D v - P v := by
        dsimp only [z,P]
        simp only [mul_sub,sum_sub_distrib,← sum_mul,row]
        ring
      rw [calcP] at h
      have c := cap v
      omega
    have zn (v : Fin 25) : 0 ≤ z v := by dsimp only [z]; linarith [maxD v]
    let L (v : Fin 25) := ∑ i,W v i*z i
    have Ln (v : Fin 25) : 0 ≤ L v :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (by rcases bits v i with h|h <;> omega) (zn i))
    have Ltotal : (∑ v,L v) ≤ 10*(250-2*M) := by
      dsimp only [L]
      rw [sum_comm,← zsum,mul_sum]
      apply sum_le_sum
      intro i _
      rw [← sum_mul]
      have col : (∑ v,W v i)=D i := (sum_congr rfl (fun j _ => sym j i)).trans (row i)
      rw [col]
      exact mul_le_mul_of_nonneg_right (maxD i) (zn i)
    have upper : M ≤ 123 := by omega
    have each (v : Fin 25) : 126-M ≤ L v + (126-M)*z v := by
      by_cases hz : z v=0
      · have dv : D v=10 := by dsimp only [z] at hz; omega
        have eq : L v = 10*D v - P v := by
          dsimp only [L,z,P]
          simp only [mul_sub,sum_sub_distrib,← sum_mul,row]
          ring
        rw [hz,mul_zero,add_zero,eq,dv]
        linarith [cap v]
      · have hz' : 1 ≤ z v := by have := zn v; omega
        nlinarith [mul_nonneg (show 0 ≤ 126-M by omega) (show 0 ≤ z v-1 by omega),Ln v]
    have allV := sum_le_sum (s:=univ) (fun v _ => each v)
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,sum_add_distrib,← mul_sum,zsum] at allV
    have choices : M=122 ∨ M=123 := by omega
    rcases choices with h|h <;> rw [h] at allV Ltotal <;> omega
  refine ⟨by by_contra! lo; exact high (by omega),?_⟩
  intro lo v
  have sq := one v
  by_contra! h
  have hv : 8 ≤ -z v := by dsimp only [z]; omega
  nlinarith [mul_nonneg (show 0 ≤ -z v-8 by omega) (show 0 ≤ -z v+8 by omega)]

set_option maxHeartbeats 1600000 in
/-- If every neighborhood cut loses at least 26 edges, there are at most
121 edges. In the 120- and 121-edge range every degree is at most 17. -/
lemma degree_bounds (G : SimpleGraph (Fin 25)) :
    let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
    let d (i : Fin 25) := ∑ j,w i j
    let m := G.edgeFinset.card
    (∀ v, (∑ i,w v i*d i) + 26 ≤ m) →
    m ≤ 121 ∧ (120 ≤ m → ∀ v, d v ≤ 17) := by
  classical
  intro w d m rooted
  let D (i : Fin 25) : ℤ := d i
  let W (i j : Fin 25) : ℤ := w i j
  let P (v : Fin 25) := ∑ i,W v i*D i
  let M : ℤ := m
  have sym (i j : Fin 25) : W i j = W j i := by simp only [W,w,G.adj_comm i j]
  have row (i : Fin 25) : ∑ j,W i j = D i := (Nat.cast_sum univ (w i)).symm
  have total : (∑ i,D i) = 2*M := by
    have h : (∑ i,d i) = 2*m := edge_sum G
    dsimp only [D,M]
    exact_mod_cast h
  have cap (v : Fin 25) : P v + 26 ≤ M := by
    dsimp only [P,W,D,M]
    exact_mod_cast rooted v
  have bits (i j) : W i j=1 ∨ W i j=0 := by
    by_cases h : G.Adj i j <;> simp [W,w,h]
  obtain ⟨upper,deg⟩ := moments D W M sym row total bits cap
  change (m:ℤ) ≤ 121 at upper
  refine ⟨by exact_mod_cast upper,?_⟩
  intro lo v
  have lm : (120:ℤ) ≤ (m:ℤ) := by exact_mod_cast lo
  have b := deg lm v
  change (d v:ℤ) ≤ 17 at b
  exact_mod_cast b

/-- The two endpoints are constant opposite words. A neighbor of the first
endpoint uses the shadow word of its core color. -/
lemma pair_masks :
    let bit (s : Fin 4) (a k : Fin 5) : Bool :=
      if s=2 then false else if s=3 then true else if s=1 then decide (k≠a+1)
      else decide (k=a ∨ k=a+2)
    ∀ (s t : Fin 4) (a b : Fin 5),
      ((s<2 ∧ t<2 ∧ (s=0 ∨ t=0) ∧ (b=a+1 ∨ a=b+1)) ∨
       (s=2 ∧ t=1) ∨ (s=1 ∧ t=2) ∨ (s=3 ∧ t=0) ∨ (s=0 ∧ t=3) ∨
       (s=2 ∧ t=3) ∨ (s=3 ∧ t=2)) →
      (∑ k, if bit s a k=bit t b k then (1:ℕ) else 0) +
        (if s=2 ∧ t=3 then 2 else 0) + (if s=3 ∧ t=2 then 2 else 0) =
      1+(if s=3 then 1 else 0)+(if t=3 then 1 else 0) := by decide +kernel

set_option maxHeartbeats 800000 in
/-- Five cuts around the oriented edge pq. For unordered edges their total
loss is exactly m + deg(q) - 2. -/
lemma opposed_pair (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3) (p q : Fin 25)
    (pq : G.Adj p q) (g : Fin 25 → Fin 5)
    (maps : ∀ i, i≠p → i≠q → ∀ j, j≠p → j≠q → G.Adj i j →
      g j=g i+1 ∨ g i=g j+1) :
    let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
    ∃ f : Fin 25 → Bool,
      5*(∑ i,∑ j,if G.Adj i j ∧ f i=f j then (1:ℕ) else 0)+4 ≤
      (∑ i,∑ j,w i j)+2*(∑ i,w q i) := by
  classical
  intro w
  let kind (i : Fin 25) : Fin 4 :=
    if i=p then 2 else if i=q then 3 else if G.Adj p i then 1 else 0
  let bit (s : Fin 4) (a k : Fin 5) : Bool :=
    if s=2 then false else if s=3 then true else if s=1 then decide (k≠a+1)
    else decide (k=a ∨ k=a+2)
  let color (k : Fin 5) (i : Fin 25) := bit (kind i) (g i) k
  have ne := pq.ne
  have kp : kind p=2 := by simp [kind]
  have kq : kind q=3 := by simp [kind,ne.symm]
  have two (i) : kind i=2 ↔ i=p := by
    by_cases hp : i=p <;> by_cases hq : i=q <;> by_cases h : G.Adj p i <;> simp [kind,hp,hq,h]
  have three (i) : kind i=3 ↔ i=q := by
    by_cases hp : i=p
    · subst i; simp [kp,ne]
    · by_cases hq : i=q <;> by_cases h : G.Adj p i <;> simp [kind,hp,hq,h,ne.symm]
  have shadow {i} (h : G.Adj p i) (hq : i≠q) : kind i=1 := by simp [kind,h.ne.symm,hq,h]
  have ordinary {i} (h : G.Adj q i) (hp : i≠p) : kind i=0 := by
    have no : ¬G.Adj p i := fun pi => tri _ (is3Clique_triple_iff.mpr ⟨pq,pi,h⟩)
    simp [kind,h.ne.symm,hp,no]
  have core {i} (hp : i≠p) (hq : i≠q) : kind i<2 := by
    by_cases h : G.Adj p i <;> simp [kind,hp,hq,h]
  have edge (i j : Fin 25) :
      (∑ k, if G.Adj i j ∧ color k i=color k j then (1:ℕ) else 0) +
      (if i=p then if j=q then 2 else 0 else 0) +
      (if i=q then if j=p then 2 else 0 else 0) =
      w i j + (if i=q then w i j else 0) + (if j=q then w i j else 0) := by
    by_cases h : G.Adj i j
    · have typed :
          ((kind i<2 ∧ kind j<2 ∧ (kind i=0 ∨ kind j=0) ∧ (g j=g i+1 ∨ g i=g j+1)) ∨
          (kind i=2 ∧ kind j=1) ∨ (kind i=1 ∧ kind j=2) ∨ (kind i=3 ∧ kind j=0) ∨
          (kind i=0 ∧ kind j=3) ∨ (kind i=2 ∧ kind j=3) ∨ (kind i=3 ∧ kind j=2)) := by
        by_cases ip : i=p
        · subst i
          by_cases jq : j=q
          · subst j; simp [kp,kq]
          · simp [kp,shadow h jq]
        by_cases iq : i=q
        · subst i
          by_cases jp : j=p
          · subst j; simp [kp,kq]
          · simp [kq,ordinary h jp]
        by_cases jp : j=p
        · subst j; simp [kp,shadow h.symm iq]
        by_cases jq : j=q
        · subst j; simp [kq,ordinary h.symm ip]
        apply Or.inl
        refine ⟨core ip iq,core jp jq,?_,maps i ip iq j jp jq h⟩
        by_cases pi : G.Adj p i
        · have pj : ¬G.Adj p j := fun z => tri _ (is3Clique_triple_iff.mpr ⟨pi,z,h⟩)
          exact Or.inr (by simp [kind,jp,jq,pj])
        · exact Or.inl (by simp [kind,ip,iq,pi])
      have eq := pair_masks (kind i) (kind j) (g i) (g j) typed
      change (∑ k, if color k i=color k j then (1:ℕ) else 0) +
        (if kind i=2 ∧ kind j=3 then 2 else 0) +
        (if kind i=3 ∧ kind j=2 then 2 else 0) =
        1+(if kind i=3 then 1 else 0)+(if kind j=3 then 1 else 0) at eq
      simpa only [h,true_and,w,if_true,two,three,ite_and] using eq
    · have npq : ¬(i=p ∧ j=q) := fun ⟨a,b⟩ => h (a ▸ b ▸ pq)
      have nqp : ¬(i=q ∧ j=p) := fun ⟨a,b⟩ => h (a ▸ b ▸ pq.symm)
      simp [h,w,← ite_and,npq,nqp]
  let cost (k : Fin 5) := ∑ i,∑ j, if G.Adj i j ∧ color k i=color k j then (1:ℕ) else 0
  have eq := sum_congr (s₁:=univ) rfl (fun i _ => sum_congr (s₁:=univ) rfl (fun j _ => edge i j))
  simp only [sum_add_distrib] at eq
  have point (a b : Fin 25) :
      (∑ i : Fin 25, ∑ j : Fin 25, if i=a then if j=b then (2:ℕ) else 0 else 0) = 2 := by
    simp_rw [← Finset.ite_sum_zero]
    simp
  have row : (∑ i : Fin 25,∑ j : Fin 25, if i=q then w i j else 0)=∑ j,w q j := by
    simp_rw [← Finset.ite_sum_zero]
    simp
  have col : (∑ i : Fin 25,∑ j : Fin 25, if j=q then w i j else 0)=∑ j,w q j := by
    simp only [sum_ite_eq',mem_univ,if_true]
    exact sum_congr rfl (fun i _ => by simp only [w,G.adj_comm i q])
  have swap : (∑ k,cost k) = ∑ i,∑ j,∑ k,if G.Adj i j ∧ color k i=color k j then (1:ℕ) else 0 := by
    dsimp only [cost]
    rw [sum_comm]
    simp_rw [sum_comm (s:= (univ : Finset (Fin 5))) (t:= (univ : Finset (Fin 25)))]
  rw [← swap,point,point,col,row] at eq
  obtain ⟨k,_,hk⟩ := univ.exists_min_image cost univ_nonempty
  have small := sum_le_sum (s:=univ) (f:=fun _ => cost k) hk
  have bound : 5 * cost k ≤ ∑ k,cost k := by simpa using small
  exact ⟨color k,by change 5*cost k+4 ≤ _; omega⟩

/-- Color two independent neighborhoods oppositely. Extending over their
complement spends at most half its degree sum, rounded down. -/
lemma small_exterior (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3) (p q : Fin 25)
    (_pq : G.Adj p q) :
    let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
    let d (i : Fin 25) := ∑ j,w i j
    let R := univ.filter (fun i => ¬G.Adj p i ∧ ¬G.Adj q i)
    (∑ i ∈ R,d i) ≤ 51 →
    ∃ f : Fin 25 → Bool, (∑ i,∑ j,if G.Adj i j ∧ f i=f j then (1:ℕ) else 0) ≤ 50 := by
  classical
  intro w d R bound
  let T := Rᶜ
  let b (i : Fin 25) := decide (G.Adj p i)
  have notR (i) : i ∈ T ↔ i ∉ R := mem_compl
  have inside (i) (hi : i ∈ T) : G.Adj p i ∨ G.Adj q i := by
    by_contra! h
    exact (notR i).mp hi (mem_filter.mpr ⟨mem_univ _,h⟩)
  have mono : (∑ i ∈ T,∑ j ∈ T,if b i=b j then w i j else 0)=0 := by
    apply sum_eq_zero
    intro i hi
    apply sum_eq_zero
    intro j hj
    by_cases ij : G.Adj i j
    · by_cases pi : G.Adj p i <;> by_cases pj : G.Adj p j
      · exact (tri _ (is3Clique_triple_iff.mpr ⟨pi,pj,ij⟩)).elim
      · simp [b,pi,pj]
      · simp [b,pi,pj]
      · exact (tri _ (is3Clique_triple_iff.mpr
          ⟨(inside i hi).resolve_left pi,(inside j hj).resolve_left pj,ij⟩)).elim
    · simp [w,ij]
  have sym (i j) : w i j = w j i := by simp only [w,G.adj_comm i j]
  have diag (i) : w i i=0 := by simp [w]
  obtain ⟨f,hf⟩ := extendHalf w sym diag T b
  rw [mono] at hf
  have localLe (i j : Fin 25) : w i j ≤
      (if i∈T ∧ j∈T then w i j else 0)+(if i∈R then w i j else 0)+
      (if j∈R then w i j else 0) := by
    by_cases hi : i∈R <;> by_cases hj : j∈R <;> simp [notR,hi,hj]
  have sums := sum_le_sum (s:=univ) (fun i _ => sum_le_sum (s:=univ) (fun j _ => localLe i j))
  have rows : (∑ i,∑ j,if i∈R then w i j else 0)=∑ i ∈ R,d i := by
    have e (i : Fin 25) : (∑ j,if i∈R then w i j else 0) = if i∈R then d i else 0 := by
      by_cases hi : i∈R <;> simp [hi,d]
    simp_rw [e,← sum_filter]
    simp
  have cols : (∑ i,∑ j,if j∈R then w i j else 0)=∑ i ∈ R,d i := by
    rw [sum_comm,← rows]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [sym j i]
  simp only [sum_add_distrib,restrictedSum,rows,cols] at sums
  have eq (i j : Fin 25) : (if G.Adj i j ∧ f i=f j then (1:ℕ) else 0) =
      (if f i=f j then w i j else 0) := by
    by_cases h : f i=f j <;> simp [w,h]
  have he := even_cost G f
  refine ⟨f,?_⟩
  simp only [eq] at he ⊢
  omega

lemma exterior_card (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3)
    (p q : Fin 25) (pq : G.Adj p q) :
    let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
    let d (i : Fin 25) := ∑ j,w i j
    let R := univ.filter (fun i => ¬G.Adj p i ∧ ¬G.Adj q i)
    R.card + d p + d q = 25 := by
  classical
  intro w d R
  have localEq (i : Fin 25) : (if i ∈ R then 1 else 0) + w p i + w q i = 1 := by
    by_cases hp : G.Adj p i <;> by_cases hq : G.Adj q i <;> simp [R,w,hp,hq]
    exact (tri _ (is3Clique_triple_iff.mpr ⟨pq,hp,hq⟩)).elim
  have sums := sum_congr (s₁:=univ) rfl (fun i _ => localEq i)
  simpa [sum_add_distrib,d] using sums

lemma obstruction_bounds (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3)
    (bad : ∀ f : Fin 25 → Bool, 50 < ∑ i,∑ j,if G.Adj i j ∧ f i=f j then (1:ℕ) else 0) :
    let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
    let d (i : Fin 25) := ∑ j,w i j
    let m := G.edgeFinset.card
    m ≤ 121 ∧ (120 ≤ m → ∀ v, d v ≤ 17) := by
  classical
  apply degree_bounds
  intro v
  let f (i : Fin 25) := decide (G.Adj v i)
  have id := root_identity G tri v
  have even := even_cost G f
  have fail := bad f
  let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
  change (∑ i,∑ j,if G.Adj i j ∧ f i=f j then (1:ℕ) else 0) +
    2*(∑ i,w v i * ∑ j,w i j) = ∑ i,∑ j,w i j at id
  have count : (∑ i,∑ j,w i j) = 2*G.edgeFinset.card := edge_sum G
  change (∑ i,w v i * ∑ j,w i j) + 26 ≤ G.edgeFinset.card
  omega

/-- Any triangle-free graph on 25 vertices with at least 122 edges admits
a suitable bipartite subgraph. -/
lemma bipartize_dense (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3)
    (dense : 122 ≤ G.edgeFinset.card) :
    ∃ H : SimpleGraph (Fin 25), H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 25 := by
  classical
  suffices h : ∃ f : Fin 25 → Bool, (∑ i,∑ j,if G.Adj i j ∧ f i=f j then (1:ℕ) else 0) ≤ 50 by
    obtain ⟨f,hf⟩ := h
    exact cut_subgraph G f hf
  by_contra! bad
  have h := (obstruction_bounds G tri bad).1
  omega

lemma cut_of_pair_deletion (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3) (p q : Fin 25)
    (pq : G.Adj p q) (g : Fin 25 → Fin 5)
    (maps : ∀ i, i≠p → i≠q → ∀ j, j≠p → j≠q → G.Adj i j → g j=g i+1 ∨ g i=g j+1) :
    ∃ f : Fin 25 → Bool, (∑ i,∑ j,if G.Adj i j ∧ f i=f j then (1:ℕ) else 0) ≤ 50 := by
  classical
  by_contra! bad
  let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
  let d (i : Fin 25) := ∑ j,w i j
  let m := G.edgeFinset.card
  let R := univ.filter (fun i => ¬G.Adj p i ∧ ¬G.Adj q i)
  have size : R.card+d p+d q=25 := exterior_card G tri p q pq
  have count : (∑ i,∑ j,w i j) = 2*m := edge_sum G
  obtain ⟨upper,cap⟩ := obstruction_bounds G tri bad
  change m ≤ 121 at upper
  change 120 ≤ m → ∀ v,d v ≤ 17 at cap
  have lower {p q : Fin 25} (pq : G.Adj p q)
      (hg : ∀ i, i≠p → i≠q → ∀ j, j≠p → j≠q → G.Adj i j → g j=g i+1 ∨ g i=g j+1) :
      132 ≤ m+d q := by
    obtain ⟨f,hf⟩ := opposed_pair G tri p q pq g hg
    change 5*_+4 ≤ (∑ i,∑ j,w i j)+2*d q at hf
    have he := even_cost G f
    have hb := bad f
    omega
  have lq := lower pq maps
  have lp := lower pq.symm (fun i a b j c d => maps i b a j d c)
  have den : 120 ≤ m := by omega
  have few : R.card ≤ 3 := by omega
  have bound : (∑ i ∈ R,d i) ≤ 51 := calc
    _ ≤ R.card * 17 := by simpa using R.sum_le_card_nsmul d 17 (fun i _ => cap den i)
    _ ≤ 3 * 17 := Nat.mul_le_mul_right 17 few
    _ = 51 := rfl
  obtain ⟨f,hf⟩ := small_exterior G tri p q pq bound
  exact (not_lt_of_ge hf) (bad f)

/-- The edge-deletion conclusion in the original graph language, at all
densities and without a domination hypothesis. -/
lemma bipartize_of_pair_deletion (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3)
    (p q : Fin 25) (pq : G.Adj p q) (g : Fin 25 → Fin 5)
    (maps : ∀ i, i≠p → i≠q → ∀ j, j≠p → j≠q → G.Adj i j → g j=g i+1 ∨ g i=g j+1) :
    ∃ H : SimpleGraph (Fin 25), H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 25 := by
  obtain ⟨f,hf⟩ := cut_of_pair_deletion G tri p q pq g maps
  exact cut_subgraph G f hf

/-- The two-neighbor classification on the pentagon, restricted to the
complement of the vertices with a unique cycle neighbor. -/
lemma color_core {V : Type*} (G : SimpleGraph V) (tri : G.CliqueFree 3)
    (v : Fin 5 → V) (cycle : ∀ i, G.Adj (v i) (v (i+1)))
    (dom : ∀ x, ∃ i, G.Adj x (v i)) :
    ∃ g : V → Fin 5, ∀ x, ¬(∃! i, G.Adj x (v i)) →
      ∀ y, ¬(∃! i, G.Adj y (v i)) →
        G.Adj x y → g y=g x+1 ∨ g x=g y+1 := by
  classical
  let S (x : V) := univ.filter (fun i : Fin 5 => G.Adj x (v i))
  have mem (x : V) (i : Fin 5) : i ∈ S x ↔ G.Adj x (v i) := by simp [S]
  have classify : ∀ T : Finset (Fin 5), 2 ≤ T.card → (∀ i ∈ T, i+1 ∉ T) →
      ∃ a : Fin 5, ∀ i, i ∈ T ↔ (i=a+1 ∨ a=i+1) := by decide +kernel
  have common : ∀ a b : Fin 5, ¬(b=a+1 ∨ a=b+1) →
      ∃ i, (i=a+1 ∨ a=i+1) ∧ (i=b+1 ∨ b=i+1) := by decide +kernel
  have label (x : V) : ∃ a : Fin 5, ∀ i, ¬(∃! j, G.Adj x (v j)) →
      (i ∈ S x ↔ (i=a+1 ∨ a=i+1)) := by
    by_cases single : ∃! i, G.Adj x (v i)
    · exact ⟨0, fun _ h => (h single).elim⟩
    · obtain ⟨i,hi⟩ := dom x
      have pos : 0 < (S x).card := Finset.card_pos.mpr ⟨i,(mem x i).mpr hi⟩
      have two : 2 ≤ (S x).card := by
        by_contra! small
        obtain ⟨j,hj⟩ := Finset.card_eq_one.mp (show (S x).card = 1 by omega)
        apply single
        have eq (k : Fin 5) : G.Adj x (v k) ↔ k = j := by rw [← mem,hj,mem_singleton]
        exact ⟨j,(eq j).mpr rfl,fun k hk => (eq k).mp hk⟩
      obtain ⟨a,ha⟩ := classify (S x) two
        (fun j hj hk => tri _ (is3Clique_triple_iff.mpr
          ⟨(mem x j).mp hj,(mem x _).mp hk,cycle j⟩))
      exact ⟨a,fun i _ => ha i⟩
  choose g hg using label
  refine ⟨g,fun x hx y hy xy => ?_⟩
  by_contra hn
  obtain ⟨i,hi,hj⟩ := common _ _ hn
  exact tri _ (is3Clique_triple_iff.mpr
    ⟨xy,(mem x i).mp ((hg x i hx).mpr hi),(mem y i).mp ((hg y i hy).mpr hj)⟩)


/-- A dominating pentagon with two adjacent exceptional vertices has the
25-edge property, even if its full graph does not map to a pentagon. -/
lemma bipartize_adjacent_exceptions (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3)
    (v : Fin 5 → Fin 25) (cycle : ∀ i,G.Adj (v i) (v (i+1)))
    (dom : ∀ x, ∃ i,G.Adj x (v i)) (p q : Fin 25) (pq : G.Adj p q)
    (cover : ∀ x, (∃! i,G.Adj x (v i)) → x=p ∨ x=q) :
    ∃ H : SimpleGraph (Fin 25), H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 25 := by
  obtain ⟨g,hg⟩ := color_core G tri v cycle dom
  have core {x : Fin 25} (hp : x≠p) (hq : x≠q) : ¬∃! i,G.Adj x (v i) :=
    fun h => (cover x h).elim hp hq
  exact bipartize_of_pair_deletion G tri p q pq g (fun i hi hj j hk hl => hg i (core hi hj) j (core hk hl))

/-- At least two independent exceptions, with no edge whose deletion of both endpoints leaves a pentagon-mappable graph. -/
def H1 : Prop := ∀ (G : SimpleGraph (Fin 25)), G.CliqueFree 3 →
    let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
    let d (i : Fin 25) := ∑ j,w i j
    let S := ∑ i,d i
    200 ≤ S → S ≤ 242 →
    (∀ i, 2*(∑ j,w i j*d j)+51 ≤ S) →
    (∀ W : Finset (Fin 25), ∀ b : Fin 25 → Bool,
      (∀ i ∈ W, ∀ j ∈ W, G.Adj i j → b i ≠ b j) →
      (∑ i ∈ W, ∑ j ∈ W, w i j)+102 ≤ S) →
    (∀ p q, G.Adj p q → ¬∃ g : Fin 25 → Fin 5,
      ∀ i, i≠p → i≠q → ∀ j, j≠p → j≠q → G.Adj i j → g j=g i+1 ∨ g i=g j+1) →
    ∀ v : Fin 5 → Fin 25, (∀ i, G.Adj (v i) (v (i+1))) →
    (∀ x, ∃ i, G.Adj x (v i)) →
    let X := univ.filter (fun x => ∃! i, G.Adj x (v i))
    (∀ x ∈ X, ∀ y ∈ X, ¬G.Adj x y) → (∃ x ∈ X, ∃ y ∈ X, x ≠ y) →
    ∃ f : Fin 25 → Bool, (∑ i, ∑ j, if G.Adj i j ∧ f i=f j then 1 else 0) ≤ (50:ℕ)

/-- Two adjacent exceptions and a third distinct exception, with every edge failing the two-vertex deletion criterion. -/
def H2 : Prop := ∀ (G : SimpleGraph (Fin 25)), G.CliqueFree 3 →
    let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
    let d (i : Fin 25) := ∑ j,w i j
    let S := ∑ i,d i
    200 ≤ S → S ≤ 242 →
    (∀ i, 2*(∑ j,w i j*d j)+51 ≤ S) →
    (∀ W : Finset (Fin 25), ∀ b : Fin 25 → Bool,
      (∀ i ∈ W, ∀ j ∈ W, G.Adj i j → b i ≠ b j) →
      (∑ i ∈ W, ∑ j ∈ W, w i j)+102 ≤ S) →
    (∀ p q, G.Adj p q → ¬∃ g : Fin 25 → Fin 5,
      ∀ i, i≠p → i≠q → ∀ j, j≠p → j≠q → G.Adj i j → g j=g i+1 ∨ g i=g j+1) →
    ∀ v : Fin 5 → Fin 25, (∀ i, G.Adj (v i) (v (i+1))) →
    (∀ x, ∃ i, G.Adj x (v i)) →
    let X := univ.filter (fun x => ∃! i, G.Adj x (v i))
    (∃ p ∈ X, ∃ q ∈ X, G.Adj p q ∧ ∃ r ∈ X, r≠p ∧ r≠q) →
    ∃ f : Fin 25 → Bool, (∑ i, ∑ j, if G.Adj i j ∧ f i=f j then 1 else 0) ≤ (50:ℕ)

theorem main : H1 → H2 → OMA.R_Erdos23_erdos_23_variants_n5_R2_H1_R1.H1 := by
  classical
  intro independent adjacent G tri w d S dense _upper _nonmap rooted induced a b c d' e ab bc cd de ea dom
  let v : Fin 5 → Fin 25 := ![a,b,c,d',e]
  have cycle (i : Fin 5) : G.Adj (v i) (v (i+1)) := by
    fin_cases i <;> first | exact ab | exact bc | exact cd | exact de | exact ea
  have hits (x : Fin 25) : ∃ i,G.Adj x (v i) := by
    rcases dom x with h|h|h|h|h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
    · exact ⟨3,h⟩
    · exact ⟨4,h⟩
  let X := univ.filter (fun x => ∃! i,G.Adj x (v i))
  by_contra! bad
  have fail (cut : ∃ f : Fin 25 → Bool,
      (∑ i,∑ j,if G.Adj i j ∧ f i=f j then (1:ℕ) else 0) ≤ 50) : False := by
    obtain ⟨f,hf⟩ := cut
    exact (not_lt_of_ge hf) (bad f)
  have count : S=2*G.edgeFinset.card := edge_sum G
  have cap := (obstruction_bounds G tri bad).1
  have upper : S ≤ 242 := by omega
  have none (p q : Fin 25) (pq : G.Adj p q) : ¬∃ g : Fin 25 → Fin 5,
      ∀ i, i≠p → i≠q → ∀ j, j≠p → j≠q → G.Adj i j → g j=g i+1 ∨ g i=g j+1 := by
    rintro ⟨g,hg⟩
    exact fail (cut_of_pair_deletion G tri p q pq g hg)
  obtain ⟨g,hg⟩ := color_core G tri v cycle hits
  have outside (p q : Fin 25) (pq : G.Adj p q) : ∃ r ∈ X, r≠p ∧ r≠q := by
    by_contra! h
    apply none p q pq
    have reg {i} (ip : i≠p) (iq : i≠q) : ¬∃! k,G.Adj i (v k) := by
      intro ex
      have hx : i ∈ X := mem_filter.mpr ⟨mem_univ _,ex⟩
      exact iq (h i hx ip)
    exact ⟨g,fun i ip iq j jp jq => hg i (reg ip iq) j (reg jp jq)⟩
  by_cases ind : ∀ x ∈ X, ∀ y ∈ X, ¬G.Adj x y
  · obtain ⟨x,hx,_,_⟩ := outside a b ab
    obtain ⟨i,xi⟩ := hits x
    obtain ⟨y,hy,yx,_⟩ := outside x (v i) xi
    exact fail (independent G tri dense upper rooted induced none v cycle hits ind ⟨x,hx,y,hy,yx.symm⟩)
  · push Not at ind
    obtain ⟨x,hx,y,hy,xy⟩ := ind
    exact fail (adjacent G tri dense upper rooted induced none v cycle hits ⟨x,hx,y,hy,xy,outside x y xy⟩)

end OMA.R_Erdos23_erdos_23_variants_n5_R2_H1_R1_H1_R2
