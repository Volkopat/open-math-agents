import OMAReductions.R_Erdos23_erdos_23_variants_n5_R2_H1_R1
import Mathlib

/-! # Three exceptions at a dominating pentagon

Five coordinate cuts bound the cost of reinserting the exceptional vertices.
Edge sums count both orientations unless expressed using the edge finset. -/
namespace OMA.R_Erdos23_erdos_23_variants_n5_R2_H1_R1_H1_R3
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


/- Large-independent-set argument by @synthrosai (n5 desk notes 86740, 86767, 86816). -/
/- Removing a large independent set

Choose thirteen independent vertices and write B for the graph on the other
twelve. If B has at most 25 edges, the partition already suffices. Otherwise
choose a vertex r of B uniformly, cut its neighbourhood from its complement,
and put each of the thirteen vertices opposite most of its neighbours.

For an independent set I of neighbours in B, let K be the sum of their
degrees and t the number of vertices outside I. The edges outside I satisfy
Mantel's bound 4(e − K) ≤ t². Averaging over r bounds the loss on edges
incident to I by min(K, |I|t − K) / 12. Cauchy–Schwarz bounds the sum of
squared degrees on I and on its complement. The finite inequality below
combines these bounds to make the expected total loss strictly below 26. -/

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
private theorem num_twelve : ∀ (e : Fin 67) (h : Fin 13) (K : Fin 67),
    26 ≤ e.val → K.val ≤ e.val → K.val ≤ h.val * (12-h.val) →
    4*(e.val-K.val) ≤ (12-h.val)^2 →
    12*e.val+13*min K.val (h.val*(12-h.val)-K.val) <
      312+K.val^2 / max 1 h.val+(2*e.val-K.val)^2/max 1 (12-h.val) := by
  decide +kernel

private theorem turan_small : ∀ t : Fin 13,
    4 * ((t.val^2-(t.val%2)^2)*(2-1)/(2*2)+(t.val%2).choose 2) ≤ t.val^2 := by
  decide +kernel

open scoped Classical in
private theorem indep_degree_internal {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (tf : B.CliqueFree 3) (I : Finset V)
    (ind : ∀ x ∈ I, ∀ y ∈ I, ¬ B.Adj x y) (small : Iᶜ.card ≤ 12) :
    let K := ∑ i ∈ I, B.degree i
    K ≤ B.edgeFinset.card ∧ 4*(B.edgeFinset.card-K) ≤ Iᶜ.card^2 := by
  classical
  let H := B.between (I : Set V) (Iᶜ : Finset V)
  have disj : Disjoint (I : Set V) (Iᶜ : Finset V) := by
    rw [Finset.coe_compl]; exact disjoint_compl_right
  have hb : H.IsBipartiteWith I (Iᶜ : Finset V) := between_isBipartiteWith disj
  have hs : H ≤ B := between_le
  have same (x : V) (hx : x ∈ I) : H.degree x = B.degree x := by
    rw [← H.card_neighborFinset_eq_degree, ← B.card_neighborFinset_eq_degree]
    congr 1
    ext y
    simp only [mem_neighborFinset]
    exact ⟨fun h => hs h,fun h => ⟨h,Or.inl ⟨hx,mem_compl.mpr (fun hy => ind x hx y hy h)⟩⟩⟩
  have kept : (∑ x ∈ I, B.degree x) = H.edgeFinset.card := by
    rw [← isBipartiteWith_sum_degrees_eq_card_edges hb]
    exact sum_congr rfl (fun x h => (same x h).symm)
  let T := Iᶜ
  let D := B.induce (T : Set V)
  have omitted : B.edgeFinset \ H.edgeFinset ⊆
      D.edgeFinset.map ⟨Sym2.map Subtype.val, Sym2.map.injective Subtype.val_injective⟩ := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      obtain ⟨xy,nh⟩ := mem_sdiff.mp he
      have adj : B.Adj x y := by simpa using xy
      have notBetween : ¬H.Adj x y := by simpa using nh
      have xt : x ∈ T := by
        apply mem_compl.mpr
        intro xi
        exact notBetween ⟨adj,Or.inl ⟨xi, mem_compl.mpr (fun yi => ind x xi y yi adj)⟩⟩
      have yt : y ∈ T := by
        apply mem_compl.mpr
        intro yi
        exact notBetween ⟨adj,Or.inr ⟨mem_compl.mpr (fun xi => ind x xi y yi adj),yi⟩⟩
      refine mem_map.mpr ⟨s(⟨x,xt⟩, ⟨y,yt⟩), ?_, by simp⟩
      exact mem_edgeFinset.mpr (show D.Adj ⟨x,xt⟩ ⟨y,yt⟩ from adj)
  have dc : D.CliqueFree 3 := tf.comap (Embedding.induce _).isContained
  have dt := dc.card_edgeFinset_le (r:=2)
  have cardT : Fintype.card ↑(↑T : Set V) = T.card := by simp
  dsimp only at dt
  rw [cardT] at dt
  have numer : 4*((T.card^2-(T.card%2)^2)*(2-1)/(2*2)+(T.card%2).choose 2) ≤ T.card^2 :=
    turan_small ⟨T.card,by change Iᶜ.card < 13; omega⟩
  have size := card_le_card omitted
  rw [card_map] at size
  have part : (B.edgeFinset \ H.edgeFinset).card + H.edgeFinset.card = B.edgeFinset.card :=
    card_sdiff_add_card_eq_card (edgeFinset_mono hs)
  dsimp only
  rw [kept]
  refine ⟨(edgeFinset_mono hs |> card_le_card), ?_⟩
  have count : B.edgeFinset.card - H.edgeFinset.card ≤ D.edgeFinset.card := by omega
  exact (Nat.mul_le_mul_left 4 count).trans ((Nat.mul_le_mul_left 4 dt).trans numer)

open scoped Classical in
/-- For each independent neighbour set in a twelve-vertex core, sum the losses
from uniformly chosen neighbourhood cuts. The sum of degree squares counts
the retained core edges over all twelve choices. -/
theorem twelve_independent_bound {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (order : Fintype.card V = 12) (tf : B.CliqueFree 3)
    (many : 26 ≤ B.edgeFinset.card) (I : Finset V)
    (ind : ∀ x ∈ I, ∀ y ∈ I, ¬ B.Adj x y) :
    let k (x : V) := (I.filter (B.Adj x)).card
    12*B.edgeFinset.card + 13*(∑ x, min (k x) (I.card-k x)) <
      312+(∑ x, B.degree x ^ 2) := by
  classical
  let I' := Iᶜ
  let k (x : V) := (I.filter (B.Adj x)).card
  let K := ∑ i ∈ I, B.degree i
  let e := B.edgeFinset.card
  let s₁ := ∑ i ∈ I, B.degree i ^ 2
  let s₂ := ∑ i ∈ I', B.degree i ^ 2
  have partI : I.card + I'.card = 12 := by
    have bound := card_le_univ I
    rw [order] at bound
    simp only [I',card_compl,order]
    omega
  have cardI : I.card ≤ 12 := by omega
  have cardT : I'.card ≤ 12 := by omega
  have Tdef : I'.card = 12-I.card := by omega
  obtain ⟨Ke,em⟩ := indep_degree_internal B tf I ind cardT
  change K ≤ e at Ke
  change 4*(e-K) ≤ I'.card^2 at em
  have total : (∑ x, k x) = K := by
    simp only [k,card_filter,K]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    rw [← B.card_neighborFinset_eq_degree, B.neighborFinset_eq_filter, card_filter]
    exact sum_congr rfl (fun x _ => by simp only [adj_comm])
  have zeroI (x : V) (hx : x ∈ I) : k x = 0 := by
    apply Finset.card_eq_zero.mpr
    exact Finset.filter_eq_empty_iff.mpr (ind x hx)
  have kt : (∑ x ∈ I', k x) = K := by
    have q := sum_add_sum_compl I k
    have z : (∑ x ∈ I, k x) = 0 := sum_eq_zero zeroI
    change _ + (∑ x ∈ I', k x) = _ at q
    omega
  have k_le (x : V) : k x ≤ I.card := card_filter_le _ _
  have capacity : K ≤ I.card*I'.card := by
    have q := sum_le_sum (s:=I') (fun x _ => k_le x)
    simpa [kt,Nat.mul_comm] using q
  have total_min : (∑ x, min (k x) (I.card-k x)) ≤ min K (I.card*I'.card-K) := by
    have L := sum_le_sum (s:=univ) (fun x _ => min_le_left (k x) (I.card-k x))
    rw [total] at L
    apply le_min L
    have z : (∑ x ∈ I, min (k x) (I.card-k x)) = 0 :=
      sum_eq_zero (fun x hx => by simp [zeroI x hx])
    have q := sum_add_sum_compl I (fun x => min (k x) (I.card-k x))
    change _ + (∑ x ∈ I', _) = _ at q
    have R := sum_le_sum (s:=I') (fun x _ => min_le_right (k x) (I.card-k x))
    have ksum : (∑ x ∈ I', ((I.card-k x)+k x)) = I'.card*I.card := by
      calc
        _ = ∑ _x ∈ I', I.card := sum_congr rfl (fun x _ => Nat.sub_add_cancel (k_le x))
        _ = _ := by simp
    rw [sum_add_distrib,kt,Nat.mul_comm] at ksum
    omega
  have ds := sum_add_sum_compl I (fun x => B.degree x)
  rw [B.sum_degrees_eq_twice_card_edges] at ds
  change K+(∑ x ∈ I', B.degree x)=2*e at ds
  have dT : (∑ x ∈ I', B.degree x) = 2*e-K := by omega
  have sqs := sum_add_sum_compl I (fun x => B.degree x ^ 2)
  change s₁+s₂ = _ at sqs
  have c₁ := sq_sum_le_card_mul_sum_sq (s:=I) (f:=fun x => B.degree x)
  have c₂ := sq_sum_le_card_mul_sum_sq (s:=I') (f:=fun x => B.degree x)
  rw [dT] at c₂
  change K^2 ≤ I.card*s₁ at c₁
  change _ ≤ I'.card*s₂ at c₂
  have divide (z h s : ℕ) (p : z ≤ h*s) : z / max 1 h ≤ s := by
    calc
      _ ≤ (max 1 h*s)/(max 1 h) := Nat.div_le_div_right (p.trans (Nat.mul_le_mul_right s (le_max_right 1 h)))
      _ = s := Nat.mul_div_cancel_left s (by positivity)
  have b₁ := divide _ _ _ c₁
  have b₂ := divide _ _ _ c₂
  have emax := B.card_edgeFinset_le_card_choose_two
  rw [order,show (12:ℕ).choose 2 = 66 by decide] at emax
  have ee : e < 67 := by change B.edgeFinset.card < 67; omega
  have num := num_twelve ⟨e,ee⟩ ⟨I.card,by omega⟩ ⟨K,by omega⟩ many Ke
    (Tdef ▸ capacity) (Tdef ▸ em)
  dsimp only at num
  rw [← Tdef] at num
  change 12*e+13*(∑ x, min (k x) (I.card-k x)) < _
  omega

open scoped Classical in
private theorem ordered_edges {V : Type*} [Fintype V] (B : SimpleGraph V) [DecidableRel B.Adj] :
    (∑ x, ∑ y, if B.Adj x y then 1 else 0) = 2*B.edgeFinset.card := by
  classical
  rw [← B.sum_degrees_eq_twice_card_edges]
  apply sum_congr rfl
  intro x _
  simp [← B.card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.sum_boole]

open scoped Classical in
private theorem sum_innerLoss {V : Type*} [Fintype V] (B : SimpleGraph V) (tf : B.CliqueFree 3) :
    (∑ r, (∑ x, ∑ y, if B.Adj x y ∧ (B.Adj r x ↔ B.Adj r y) then (1:ℕ) else 0)) + 2*(∑ x, B.degree x^2) = Fintype.card V*(2*B.edgeFinset.card) := by
  classical
  let leg (r x y : V) : ℕ := if B.Adj x y ∧ B.Adj r x then 1 else 0
  have point (r x y : V) :
      (if B.Adj x y ∧ (B.Adj r x ↔ B.Adj r y) then 1 else 0) + leg r x y + leg r y x =
      (if B.Adj x y then 1 else 0) := by
    have no : ¬(B.Adj x y ∧ B.Adj r x ∧ B.Adj r y) := fun ⟨xy,rx,ry⟩ =>
      tf {r,x,y} (is3Clique_triple_iff.mpr ⟨rx,ry,xy⟩)
    by_cases xy : B.Adj x y <;> by_cases rx : B.Adj r x <;> by_cases ry : B.Adj r y <;>
      simp_all [leg, adj_comm]
  have once (r : V) : (∑ x,∑ y, leg r x y) = ∑ x ∈ B.neighborFinset r, B.degree x := by
    rw [neighborFinset_eq_filter,sum_filter]
    apply sum_congr rfl
    intro x _
    by_cases rx : B.Adj r x
    · simp [leg,rx,← B.card_neighborFinset_eq_degree,neighborFinset_eq_filter,Finset.sum_boole]
    · simp [leg,rx]
  have byRoot (r : V) : (∑ x, ∑ y, if B.Adj x y ∧ (B.Adj r x ↔ B.Adj r y) then (1:ℕ) else 0) + 2*(∑ x ∈ B.neighborFinset r, B.degree x) = 2*B.edgeFinset.card := by
    have e := ordered_edges B
    have sums := sum_congr (s₁:=(univ : Finset V)) rfl (fun x _ =>
      sum_congr (s₁:=(univ : Finset V)) rfl (fun y _ => point r x y))
    simp only [sum_add_distrib] at sums
    have swap : (∑ x,∑ y,leg r y x) = ∑ x,∑ y,leg r x y := sum_comm
    rw [swap,once] at sums
    change _ + _ + _ = _ at sums
    omega
  have transposed : (∑ r,∑ x ∈ B.neighborFinset r, B.degree x) = ∑ x, B.degree x^2 := by
    simp_rw [neighborFinset_eq_filter, sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro x _
    rw [← sum_filter,sum_const,smul_eq_mul,sq]
    congr 1
    rw [← B.card_neighborFinset_eq_degree, neighborFinset_eq_filter]
    congr 1
    ext y
    simp [adj_comm]
  have total := sum_congr (s₁:=(univ : Finset V)) rfl (fun r _ => byRoot r)
  simp only [sum_add_distrib,← mul_sum,transposed,sum_const,card_univ,smul_eq_mul] at total
  rw [total]
  ring

open scoped Classical in
/-- A triangle-free graph on 25 vertices with an independent set of at least 13
vertices admits a bipartite spanning subgraph after at most 25 deletions. -/
theorem cut_of_large_independent (G : SimpleGraph (Fin 25)) (tf : G.CliqueFree 3)
    (S : Finset (Fin 25)) (size : 13 ≤ S.card)
    (ind : ∀ a ∈ S, ∀ a' ∈ S, ¬ G.Adj a a') :
    ∃ f : Fin 25 → Bool, (∑ x,∑ y, if G.Adj x y ∧ f x=f y then (1:ℕ) else 0) ≤ 50 := by
  classical
  obtain ⟨A,sub,order⟩ := exists_subset_card_eq size
  let U := Aᶜ
  let B : SimpleGraph U := G.induce (U : Set (Fin 25))
  let I (a : A) : Finset U := univ.filter fun u => G.Adj (a : Fin 25) (u : Fin 25)
  have aorder : Fintype.card A = 13 := by rwa [Fintype.card_coe]
  have uorder : Fintype.card U = 12 := by simp [U,order]
  have tfB : B.CliqueFree 3 := tf.comap (Embedding.induce _).isContained
  have indI (a : A) (x : U) (hx : x ∈ I a) (y : U) (hy : y ∈ I a) : ¬ B.Adj x y :=
    fun xy => tf {(a:Fin 25),(x:Fin 25),(y:Fin 25)}
      (is3Clique_triple_iff.mpr ⟨(mem_filter.mp hx).2,(mem_filter.mp hy).2,xy⟩)
  have splitSum (w : Fin 25 → ℕ) :
      (∑ x, w x) = (∑ a : A,w a)+(∑ u : U,w u) := by
    rw [Finset.sum_coe_sort,Finset.sum_coe_sort]
    exact (sum_add_sum_compl A w).symm
  have extend (b : U → Bool)
      (bound : (∑ u : U,∑ z : U, if B.Adj u z ∧ b u = b z then 1 else 0) +
        2*(∑ a : A, min (((I a).filter (fun u => b u = true)).card)
          ((I a).card-((I a).filter (fun u => b u = true)).card)) < 52) :
      ∃ f : Fin 25 → Bool, (∑ x,∑ y, if G.Adj x y ∧ f x=f y then (1:ℕ) else 0) ≤ 50 := by
    let k (a : A) := ((I a).filter (fun u => b u = true)).card
    let choice (a : A) := decide (k a ≤ (I a).card-k a)
    let col (x : Fin 25) := if ha : x ∈ A then choice ⟨x,ha⟩
      else b ⟨x,mem_compl.mpr ha⟩
    let f (x y : Fin 25) : ℕ := if G.Adj x y ∧ col x = col y then 1 else 0
    have ca (a : A) : col a = choice a := by simp [col,a.property]
    have cu (u : U) : col u = b u := by simp [col,mem_compl.mp u.property]
    have sym (x y : Fin 25) : f x y = f y x := by simp [f,adj_comm,eq_comm]
    have uu (u z : U) : f u z = (if B.Adj u z ∧ b u = b z then 1 else 0) := by
      simp [f,cu,B]
    have aa (a a' : A) : f a a' = 0 := by
      simp [f,ind a (sub a.property) a' (sub a'.property)]
    have red (a : A) : (∑ u : U, if G.Adj (a:Fin 25) (u:Fin 25) ∧ b u = true then 1 else 0) = k a := by
      rw [← card_filter]
      apply congrArg Finset.card
      ext u
      simp [I]
    have blue (a : A) : (∑ u : U, if G.Adj (a:Fin 25) (u:Fin 25) ∧ b u = false then 1 else 0) =
        (I a).card-k a := by
      have q := Finset.card_filter_add_card_filter_not (fun u : U => b u = true) (s:=I a)
      have q' : (∑ u : U, if G.Adj (a:Fin 25) (u:Fin 25) ∧ b u = false then 1 else 0) =
          ((I a).filter (fun u => ¬b u = true)).card := by
        rw [← card_filter]
        apply congrArg Finset.card
        ext u
        simp [I]
      change k a + _ = _ at q
      omega
    have towards (a : A) : (∑ u : U, f a u) = min (k a) ((I a).card-k a) := by
      by_cases pick : k a ≤ (I a).card-k a
      · have colA : choice a = true := by simp [choice,pick]
        simpa [f,ca,cu,colA,eq_comm (a:=true),min_eq_left pick] using red a
      · have colA : choice a = false := by simp [choice,pick]
        simpa [f,ca,cu,colA,eq_comm (a:=false),min_eq_right (by omega : (I a).card-k a ≤ k a)]
          using blue a
    have atA (a : A) : (∑ x, f a x) = ∑ u : U, f a u := by
      rw [splitSum]; simp [aa]
    have atU (u : U) : (∑ x, f u x) = (∑ a : A, f a u) + ∑ z : U, f u z := by
      rw [splitSum]
      exact congrArg (fun t : ℕ => t + ∑ z : U, f u z) (sum_congr rfl (fun a _ => sym u a))
    refine ⟨col,?_⟩
    have ev := even_cost G col
    change 2 ∣ ∑ x,∑ y,f x y at ev
    change (∑ x,∑ y,f x y) ≤ 50
    suffices h : (∑ x,∑ y,f x y) < 52 by omega
    rw [splitSum (fun x => ∑ y, f x y)]
    simp_rw [atA,atU]
    rw [sum_add_distrib,show (∑ u : U,∑ a : A,f a u) = ∑ a : A,∑ u : U,f a u from sum_comm]
    simp_rw [towards,uu]
    change _ + 2*(∑ a : A,min (k a) ((I a).card-k a)) < 52 at bound
    omega
  by_cases many : 26 ≤ B.edgeFinset.card
  · let k (a : A) (r : U) := ((I a).filter (B.Adj r)).card
    let loss (a : A) (r : U) := min (k a r) ((I a).card-k a r)
    have single (a : A) : 12*B.edgeFinset.card+13*(∑ r,loss a r) < 312+(∑ x, B.degree x^2) :=
      twelve_independent_bound (V:=U) B uorder tfB many (I a) (indI a)
    have total := sum_le_sum (s:=(univ : Finset A)) (fun a _ =>
      show (12*B.edgeFinset.card + 13*(∑ r,loss a r))+1 ≤ _ from single a)
    simp only [sum_add_distrib,←mul_sum,sum_const,card_univ,aorder,smul_eq_mul] at total
    have core : (∑ r : U,(∑ x, ∑ y, if B.Adj x y ∧ (B.Adj r x ↔ B.Adj r y) then (1:ℕ) else 0))+2*(∑ x : U,B.degree x^2) =
        12*(2*B.edgeFinset.card) := by
      have q := sum_innerLoss (V:=U) B tfB
      rw [uorder] at q
      convert! q using 1
    have someRoot : ∃ r, (∑ x, ∑ y, if B.Adj x y ∧ (B.Adj r x ↔ B.Adj r y) then (1:ℕ) else 0)+2*(∑ a,loss a r) < 52 := by
      by_contra! bad
      have no := sum_le_sum (s:=(univ : Finset U)) (fun r _ => bad r)
      simp only [sum_add_distrib,←mul_sum,sum_const,card_univ,uorder,smul_eq_mul] at no
      rw [show (∑ r,∑ a, loss a r) = ∑ a,∑ r, loss a r from sum_comm] at no
      omega
    obtain ⟨r,hr⟩ := someRoot
    apply extend (fun u => decide (B.Adj r u))
    convert! hr using 1
    simp only [loss,k,decide_eq_decide,decide_eq_true_eq]
  · apply extend (fun _ => true)
    simp only [and_true,filter_true,Nat.sub_self,Nat.min_zero,sum_const_zero,mul_zero,add_zero]
    calc
      _ = 2*B.edgeFinset.card := ordered_edges (V:=U) B
      _ < 52 := by omega

open scoped Classical in
theorem degree_at_least_thirteen (G : SimpleGraph (Fin 25)) (tf : G.CliqueFree 3)
    (p : Fin 25) (big : 13 ≤ G.degree p) :
    ∃ f : Fin 25 → Bool, (∑ x,∑ y, if G.Adj x y ∧ f x=f y then (1:ℕ) else 0) ≤ 50 := by
  classical
  apply cut_of_large_independent G tf (G.neighborFinset p)
  · simpa only [card_neighborFinset_eq_degree] using big
  · intro a ha a' ha' h
    exact tf {p,a,a'} (is3Clique_triple_iff.mpr ⟨(mem_neighborFinset _ _ _).mp ha,
      (mem_neighborFinset _ _ _).mp ha',h⟩)


/-- The two-neighbor classification on the pentagon, restricted to the
complement of the vertices with a unique cycle neighbor. -/
lemma pentagon_profiles {V : Type*} (G : SimpleGraph V) (tri : G.CliqueFree 3)
    (v : Fin 5 → V) (cycle : ∀ i, G.Adj (v i) (v (i+1)))
    (dom : ∀ x, ∃ i, G.Adj x (v i)) :
    ∃ g : V → Fin 5, (∀ x, ¬(∃! j, G.Adj x (v j)) → ∀ i,
      G.Adj x (v i) ↔ (i=g x+1 ∨ g x=i+1)) ∧ ∀ x, ¬(∃! i, G.Adj x (v i)) →
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
  refine ⟨g,fun x hx i => (mem x i).symm.trans (hg x i hx),fun x hx y hy xy => ?_⟩
  by_contra hn
  obtain ⟨i,hi,hj⟩ := common _ _ hn
  exact tri _ (is3Clique_triple_iff.mpr
    ⟨xy,(mem x i).mp ((hg x i hx).mpr hi),(mem y i).mp ((hg y i hy).mpr hj)⟩)


set_option maxHeartbeats 1600000 in
/-- Three single-neighbor exceptions span one edge or a path. Orient the
edge pq so that the third vertex r misses q. For the five cuts below a path
saves four units of unordered loss compared with the one-edge bound. -/
lemma triple_cuts (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3)
    (v : Fin 5 → Fin 25) (cyc : ∀ i,G.Adj (v i) (v (i+1)))
    (dom : ∀ x,∃ i,G.Adj x (v i)) (p q r : Fin 25) (pq : G.Adj p q)
    (rp : r≠p) (rq : r≠q) (miss : ¬G.Adj r q)
    (ap aq : Fin 5) (hp : G.Adj p (v ap)) (hq : G.Adj q (v aq))
    (cover : ∀ x, (∃! i,G.Adj x (v i)) → x=p ∨ x=q ∨ x=r) :
    let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
    ∃ f : Fin 25 → Bool,
      5*(∑ i,∑ j,if G.Adj i j ∧ f i=f j then (1:ℕ) else 0) +
        (if G.Adj r p then 8 else 0) ≤ (∑ i,∑ j,w i j)+2*((∑ i,w p i)+(∑ i,w q i)) := by
  classical
  intro w
  obtain ⟨g,profile,maps⟩ := pentagon_profiles G tri v cyc dom
  let kind (i : Fin 25) : Fin 5 :=
    if i=p then (if G.Adj r p then 4 else 3) else if i=q then 3 else if i=r then 2
    else if G.Adj r i then 1 else 0
  let label (i : Fin 25) := if i=p then ap else if i=q then aq else g i
  let bit (s a k : Fin 5) : Bool :=
    if s=2 then false else if s=3 then decide (k=a+1) else if s=4 then true
    else if s=1 then decide (k≠a+1) else decide (k=a ∨ k=a+2)
  let valid (s t : Fin 5) (a b : Fin 5) : Prop :=
    (s<2 ∧ t<2 ∧ (s=0 ∨ t=0) ∧ (b=a+1 ∨ a=b+1)) ∨
    (s=2 ∧ t=1) ∨ (t=2 ∧ s=1) ∨
    (s=3 ∧ t<2 ∧ ¬(b=a+1 ∨ a=b+1)) ∨ (t=3 ∧ s<2 ∧ ¬(b=a+1 ∨ a=b+1)) ∨
    (s=4 ∧ t=0) ∨ (t=4 ∧ s=0) ∨ (s=3 ∧ t=3 ∧ a≠b) ∨
    (s=4 ∧ (t=2 ∨ t=3)) ∨ (t=4 ∧ (s=2 ∨ s=3))
  let color (k : Fin 5) (i : Fin 25) := bit (kind i) (label i) k
  have table : ∀ (s t a b : Fin 5), valid s t a b →
      (∑ k,if bit s a k=bit t b k then (1:ℕ) else 0) +
      (if s=4 ∧ 2≤t then 2 else 0)+(if t=4 ∧ 2 ≤ s then 2 else 0) ≤
      1+(if 3 ≤ s then 1 else 0)+(if 3≤t then 1 else 0) := by
    intro s t a b ok
    rcases ok with h|h|h|h|h|h|h|h|h|h <;> revert s t a b <;> dsimp only [bit] <;> decide +kernel
  have flip : ∀ (s t a b : Fin 5), valid s t a b → valid t s b a := by
    intro s t a b ok
    rcases ok with ⟨u,v,w,n⟩|h|h|⟨h,k,n⟩|⟨h,k,n⟩|h|h|⟨h,k,n⟩|h|h
    · exact Or.inl ⟨v,u,w.symm,n.symm⟩
    · iterate 2 right
      exact Or.inl h
    · iterate 1 right
      exact Or.inl h
    · iterate 4 right
      exact Or.inl ⟨h,k,fun e => n e.symm⟩
    · iterate 3 right
      exact Or.inl ⟨h,k,fun e => n e.symm⟩
    · iterate 6 right
      exact Or.inl h
    · iterate 5 right
      exact Or.inl h
    · iterate 7 right
      exact Or.inl ⟨k,h,n.symm⟩
    · iterate 9 right
      exact h
    · iterate 8 right
      exact Or.inl h
  have ne := pq.ne
  have sep : ap≠aq := by
    rintro h
    exact tri _ (is3Clique_triple_iff.mpr ⟨pq,h ▸ hp,hq⟩)
  let pole := ({p,q} : Finset (Fin 25))
  let ends := ({q,r} : Finset (Fin 25))
  let save : ℕ := if G.Adj r p then 2 else 0
  let reserve (i j : Fin 25) : ℕ := if i=p then if j∈ends then save else 0 else 0
  have lp : label p=ap := by simp [label]
  have lq : label q=aq := by simp [label,ne.symm]
  have kp : kind p=(if G.Adj r p then 4 else 3) := by simp [kind]
  have kq : kind q=3 := by simp [kind,ne.symm]
  have kr : kind r=2 := by simp [kind,rp,rq]
  have pole_test (i) : 3≤kind i ↔ i∈pole := by
    by_cases a : i=p <;> by_cases b : i=q <;> by_cases c : i=r <;>
      by_cases h : G.Adj r p <;> by_cases z : G.Adj r i <;> simp [kind,pole,a,b,c,h,z,ne.symm,rp,rq]
  have four (i) : kind i=4 ↔ i=p ∧ G.Adj r p := by
    by_cases a : i=p <;> by_cases b : i=q <;> by_cases c : i=r <;>
      by_cases h : G.Adj r p <;> by_cases z : G.Adj r i <;> simp [kind,a,b,c,h,z,ne.symm,rp,rq]
  have special (i) : 2 ≤ kind i ↔ i=p ∨ i∈ends := by
    by_cases a : i=p <;> by_cases b : i=q <;> by_cases c : i=r <;>
      by_cases h : G.Adj r p <;> by_cases z : G.Adj r i <;> simp [kind,ends,a,b,c,h,z,ne.symm,rp,rq]
  have reserve_test {i j} (ij : G.Adj i j) :
      (if kind i=4 ∧ 2≤kind j then 2 else 0) = reserve i j := by
    simp only [four,special]
    by_cases a : i=p
    · subst i
      by_cases h : G.Adj r p <;> by_cases b : j∈ends <;> simp [reserve,save,h,b,ij.ne.symm]
    · simp [reserve,a]
  have regular {i} (a : i≠p) (b : i≠q) (c : i≠r) : ¬∃! k,G.Adj i (v k) :=
    fun e => (cover i e).elim a (fun t => t.elim b c)
  have excludes {i z k} (hi : ¬∃! n,G.Adj i (v n)) (zi : G.Adj z i) (zk : G.Adj z (v k)) :
      ¬(g i=k+1 ∨ k=g i+1) := fun close =>
    tri _ (is3Clique_triple_iff.mpr ⟨zi,zk,(profile i hi k).mpr close.symm⟩)
  have typed {i j} (ij : G.Adj i j) : valid (kind i) (kind j) (label i) (label j) := by
    have fromP {x} (px : G.Adj p x) : valid (kind p) (kind x) (label p) (label x) := by
      by_cases b : x=q
      · subst x
        by_cases h : G.Adj r p <;> simp [valid,kp,kq,lp,lq,h,sep]
      by_cases c : x=r
      · subst x
        simp [valid,kp,kr,px.symm]
      have a := px.ne.symm
      have ex := excludes (regular a b c) px hp
      by_cases h : G.Adj r p
      · have rx : ¬G.Adj r x := fun t => tri _ (is3Clique_triple_iff.mpr ⟨h,t,px⟩)
        simp [valid,h,kind,a,b,c,rx]
      · by_cases rx : G.Adj r x <;> simp [valid,h,lp,label,kind,a,b,c,rx] <;> exact not_or.mp ex
    have fromQ {x} (qx : G.Adj q x) (a : x≠p) : valid (kind q) (kind x) (label q) (label x) := by
      have b := qx.ne.symm
      have c : x≠r := fun t => miss (t ▸ qx.symm)
      have ex := excludes (regular a b c) qx hq
      by_cases rx : G.Adj r x <;> simp [valid,kq,lq,kind,label,a,b,c,rx] <;> exact not_or.mp ex
    have fromR {x} (rx : G.Adj r x) (a : x≠p) (b : x≠q) :
        valid (kind r) (kind x) (label r) (label x) := by
      simp [valid,kr,kind,a,b,rx.ne.symm,rx]
    by_cases a : i=p
    · subst i; exact fromP ij
    by_cases a' : j=p
    · subst j; exact flip _ _ _ _ (fromP ij.symm)
    by_cases b : i=q
    · subst i; exact fromQ ij a'
    by_cases b' : j=q
    · subst j; exact flip _ _ _ _ (fromQ ij.symm a)
    by_cases c : i=r
    · subst i; exact fromR ij a' b'
    by_cases c' : j=r
    · subst j; exact flip _ _ _ _ (fromR ij.symm a b)
    have near := maps i (regular a b c) j (regular a' b' c') ij
    have no : ¬(G.Adj r i ∧ G.Adj r j) := fun ⟨u,v⟩ => tri _ (is3Clique_triple_iff.mpr ⟨u,v,ij⟩)
    by_cases ri : G.Adj r i
    · have rj : ¬G.Adj r j := fun h => no ⟨ri,h⟩
      simp [valid,kind,label,a,b,c,a',b',c',ri,rj,near]
    · by_cases rj : G.Adj r j <;> simp [valid,kind,label,a,b,c,a',b',c',ri,rj,near]
  have noreserve {i j} (ij : ¬G.Adj i j) : reserve i j=0 := by
    by_cases a : i=p
    · subst i
      have b : j≠q := fun e => ij (e ▸ pq)
      by_cases h : G.Adj r p
      · have c : j≠r := fun e => ij (e ▸ h.symm)
        simp [reserve,ends,b,c]
      · simp [reserve,save,h]
    · simp [reserve,a]
  have edge (i j : Fin 25) :
      (∑ k, if G.Adj i j ∧ color k i=color k j then (1:ℕ) else 0) + reserve i j + reserve j i ≤
        w i j+(if i∈pole then w i j else 0)+(if j∈pole then w i j else 0) := by
    by_cases h : G.Adj i j
    · have z := table _ _ _ _ (typed h)
      simpa only [color,h,true_and,w,if_true,reserve_test h,reserve_test h.symm,pole_test] using z
    · simp [w,h,noreserve h,noreserve (fun a : G.Adj j i => h a.symm)]
  let cost (k : Fin 5) := ∑ i,∑ j, if G.Adj i j ∧ color k i=color k j then (1:ℕ) else 0
  have total := sum_le_sum (s:=univ) (fun i _ => sum_le_sum (s:=univ) (fun j _ => edge i j))
  simp only [sum_add_distrib] at total
  have rs : (∑ i,∑ j,reserve i j)=2*save := by
    simp only [reserve]
    simp_rw [← Finset.ite_sum_zero]
    simp only [sum_ite_eq',mem_univ,if_true,←sum_filter,filter_mem_eq_inter,univ_inter]
    simp [ends,rq.symm,two_mul]
  have rt : (∑ i,∑ j,reserve j i)=2*save := sum_comm.trans rs
  have row : (∑ i,∑ j,if i∈pole then w i j else 0) = (∑ i,w p i)+(∑ i,w q i) := by
    simp_rw [← Finset.ite_sum_zero,← sum_filter]
    simp only [filter_mem_eq_inter,univ_inter]
    simp [pole,ne]
  have col : (∑ i,∑ j,if j∈pole then w i j else 0) = (∑ i,w p i)+(∑ i,w q i) := by
    rw [sum_comm,←row]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro i _
    simp only [w,G.adj_comm i j]
  have swap : (∑ k,cost k) = ∑ i,∑ j,∑ k,if G.Adj i j ∧ color k i=color k j then (1:ℕ) else 0 := by
    dsimp only [cost]
    rw [sum_comm]
    simp_rw [sum_comm (s:=(univ : Finset (Fin 5))) (t:=(univ : Finset (Fin 25)))]
  rw [←swap,rs,rt,col,row] at total
  obtain ⟨k,_,hk⟩ := univ.exists_min_image cost univ_nonempty
  have small := sum_le_sum (s:=univ) (f:=fun _ => cost k) hk
  have bound : 5 * cost k ≤ ∑ k,cost k := by simpa using small
  refine ⟨color k,?_⟩
  change 5*cost k+_ ≤ _
  by_cases h : G.Adj r p <;> simp only [save,h,if_true,if_false] at total ⊢ <;> omega

/-- In a counterexample the ends of every edge have total degree at most
twenty. Otherwise their neighborhoods leave at most four vertices and the
sum of the exterior degrees is at most 48. -/
lemma endpoint_cap (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3)
    (bad : ∀ f : Fin 25 → Bool, 50 < ∑ i,∑ j,if G.Adj i j ∧ f i=f j then (1:ℕ) else 0)
    (p q : Fin 25) (pq : G.Adj p q) :
    let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
    (∑ i,w p i)+(∑ i,w q i) ≤ 20 := by
  classical
  intro w
  let d (i : Fin 25) := ∑ j,w i j
  have degree_eq (i) : d i=G.degree i := by
    simp [d,w,← G.card_neighborFinset_eq_degree,neighborFinset_eq_filter,Finset.sum_boole]
  have cap (i : Fin 25) : d i ≤ 12 := by
    by_contra! high
    obtain ⟨f,hf⟩ := degree_at_least_thirteen G tri i (by rw [←degree_eq]; omega)
    exact (not_lt_of_ge hf) (bad f)
  let R := univ.filter (fun i => ¬G.Adj p i ∧ ¬G.Adj q i)
  have size : R.card+d p+d q=25 := exterior_card G tri p q pq
  change d p+d q ≤ 20
  by_contra! high
  have few : R.card ≤ 4 := by omega
  have small : (∑ i ∈ R,d i) ≤ 51 := calc
    _ ≤ R.card*12 := by simpa using R.sum_le_card_nsmul d 12 (fun i _ => cap i)
    _ ≤ 4*12 := Nat.mul_le_mul_right _ few
    _ ≤ 51 := by decide
  obtain ⟨f,hf⟩ := small_exterior G tri p q pq small
  exact (not_lt_of_ge hf) (bad f)

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

/-- An edge whose two endpoints can be deleted to produce a pentagon
homomorphism is excluded by the edge-degree cap and the five cuts with opposite endpoint colors. -/
lemma no_pair_map (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3)
    (bad : ∀ f : Fin 25 → Bool, 50 < ∑ i,∑ j,if G.Adj i j ∧ f i=f j then (1:ℕ) else 0)
    (p q : Fin 25) (pq : G.Adj p q) : ¬∃ g : Fin 25 → Fin 5,
      ∀ i, i≠p → i≠q → ∀ j, j≠p → j≠q → G.Adj i j → g j=g i+1 ∨ g i=g j+1 := by
  classical
  rintro ⟨g,maps⟩
  let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
  let d (i : Fin 25) := ∑ j,w i j
  let m := G.edgeFinset.card
  have count : (∑ i,∑ j,w i j)=2*m := edge_sum G
  have upper : m ≤ 121 := (obstruction_bounds G tri bad).1
  have cap : d p+d q ≤ 20 := endpoint_cap G tri bad p q pq
  have lower {u v : Fin 25} (uv : G.Adj u v)
      (hom : ∀ i, i≠u → i≠v → ∀ j, j≠u → j≠v → G.Adj i j → g j=g i+1 ∨ g i=g j+1) :
      132 ≤ m+d v := by
    obtain ⟨f,hf⟩ := opposed_pair G tri u v uv g hom
    change 5*_+4 ≤ (∑ i,∑ j,w i j)+2*d v at hf
    have hb := bad f
    have ev := even_cost G f
    omega
  have a := lower pq maps
  have b := lower pq.symm (fun i h k j s t => maps i k h j t s)
  omega

/-- Erasing a single vertex allows its neighborhood to use shadow words.
A properly colored edge outside the apex which misses the pentagon costs
at most two extra monochromatic incidences across the five cuts. -/
lemma lift_with_errors (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3) (r : Fin 25)
    (g : Fin 25 → Fin 5) (proper : ∀ i, i≠r → ∀ j, j≠r → G.Adj i j → g i≠g j) :
    let err (i j : Fin 25) : ℕ := if G.Adj i j ∧ i≠r ∧ j≠r ∧
      ¬(g j=g i+1 ∨ g i=g j+1) then 1 else 0
    ∃ f : Fin 25 → Bool, 5*(∑ i,∑ j,if G.Adj i j ∧ f i=f j then (1:ℕ) else 0) ≤
      2*G.edgeFinset.card+2*(∑ i,∑ j,err i j) := by
  classical
  intro err
  let kind (i : Fin 25) : Fin 3 := if i=r then 2 else if G.Adj r i then 1 else 0
  let bit (s : Fin 3) (a k : Fin 5) : Bool := if s=2 then false else
    if s=1 then decide (k≠a+1) else decide (k=a ∨ k=a+2)
  let color (k : Fin 5) (i : Fin 25) := bit (kind i) (g i) k
  have table : ∀ (s t : Fin 3) (a b : Fin 5),
      ((s<2 ∧ t<2 ∧ (s=0 ∨ t=0) ∧ a≠b) ∨ (s=2 ∧ t=1) ∨ (t=2 ∧ s=1)) →
      (∑ k, if bit s a k=bit t b k then (1:ℕ) else 0) ≤
      1+2*(if s≠2 ∧ t≠2 ∧ ¬(b=a+1 ∨ a=b+1) then 1 else 0) := by decide +kernel
  have apex (i) : kind i≠2 ↔ i≠r := by
    by_cases a : i=r <;> by_cases b : G.Adj r i <;> simp [kind,a,b]
  have edge (i j : Fin 25) :
      (∑ k, if G.Adj i j ∧ color k i=color k j then (1:ℕ) else 0) ≤
        (if G.Adj i j then 1 else 0)+2*err i j := by
    by_cases h : G.Adj i j
    · have typed : ((kind i<2 ∧ kind j<2 ∧ (kind i=0 ∨ kind j=0) ∧ g i≠g j) ∨
          (kind i=2 ∧ kind j=1) ∨ (kind j=2 ∧ kind i=1)) := by
        by_cases a : i=r
        · subst i
          simp [kind,h,h.ne.symm]
        by_cases b : j=r
        · subst j
          simp [kind,h.symm,h.ne]
        have ne := proper i a j b h
        have no : ¬(G.Adj r i ∧ G.Adj r j) := fun ⟨u,v⟩ => tri _ (is3Clique_triple_iff.mpr ⟨u,v,h⟩)
        by_cases u : G.Adj r i <;> by_cases v : G.Adj r j <;> simp_all [kind]
      simpa only [h,color,err,true_and,if_true,apex] using table _ _ _ _ typed
    · simp [h,err]
  let cost (k : Fin 5) := ∑ i,∑ j, if G.Adj i j ∧ color k i=color k j then (1:ℕ) else 0
  have total := sum_le_sum (s:=univ) (fun i _ => sum_le_sum (s:=univ) (fun j _ => edge i j))
  simp only [sum_add_distrib,←mul_sum,edge_sum] at total
  have swap : (∑ k,cost k) = ∑ i,∑ j,∑ k,if G.Adj i j ∧ color k i=color k j then (1:ℕ) else 0 := by
    dsimp only [cost]
    rw [sum_comm]
    simp_rw [sum_comm (s:=(univ : Finset (Fin 5))) (t:=(univ : Finset (Fin 25)))]
  rw [←swap] at total
  obtain ⟨k,_,hk⟩ := univ.exists_min_image cost univ_nonempty
  have small := sum_le_sum (s:=univ) (f:=fun _ => cost k) hk
  exact ⟨color k,(show 5 * cost k ≤ ∑ k,cost k by simpa using small).trans total⟩

/-- Each edge outside the cycle relation is counted in both orientations.
The resulting cut has at most 25 monochromatic unordered edges. -/
lemma cut_of_repair (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3) (r : Fin 25)
    (g : Fin 25 → Fin 5) (proper : ∀ i, i≠r → ∀ j, j≠r → G.Adj i j → g i≠g j)
    (budget : G.edgeFinset.card+(∑ i,∑ j, if G.Adj i j ∧ i≠r ∧ j≠r ∧
      ¬(g j=g i+1 ∨ g i=g j+1) then (1:ℕ) else 0)<130) :
    ∃ f : Fin 25 → Bool, (∑ i,∑ j,if G.Adj i j ∧ f i=f j then (1:ℕ) else 0) ≤ 50 := by
  obtain ⟨f,hf⟩ := lift_with_errors G tri r g proper
  have ev := even_cost G f
  exact ⟨f,by dsimp only at hf; omega⟩

/-- Compute a repair using the two independent exceptions x,y. Choose a
neighboring cycle label at each anchor. Only the incidences with the core
which miss those two chosen labels' neighborhoods consume the error budget. -/
lemma two_anchor_repair (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3)
    (v : Fin 5 → Fin 25) (cyc : ∀ i,G.Adj (v i) (v (i+1)))
    (dom : ∀ i,∃ k,G.Adj i (v k)) (x y r : Fin 25) (xy : x≠y)
    (ind : ¬G.Adj x y) (cover : ∀ i, (∃! k,G.Adj i (v k)) → i=x ∨ i=y ∨ i=r) :
    ∃ g : Fin 25 → Fin 5,
      (∀ i, i≠x → i≠y → i≠r → ∀ k, G.Adj i (v k) ↔ k=g i+1 ∨ g i=k+1) ∧
      ∀ ax ay cx cy : Fin 5, G.Adj x (v ax) → G.Adj y (v ay) →
      (cx=ax+1 ∨ ax=cx+1) → (cy=ay+1 ∨ ay=cy+1) →
      let misses (z : Fin 25) (c : Fin 5) := ∑ i, if i≠r ∧ G.Adj z i ∧
        ¬(g i=c+1 ∨ c=g i+1) then (1:ℕ) else 0
      G.edgeFinset.card+2*(misses x cx+misses y cy)<130 →
      ∃ f : Fin 25 → Bool, (∑ i,∑ j,if G.Adj i j ∧ f i=f j then (1:ℕ) else 0) ≤ 50 := by
  classical
  obtain ⟨g,prof,maps⟩ := pentagon_profiles G tri v cyc dom
  have reg {i} (a : i≠x) (b : i≠y) (c : i≠r) : ¬∃! k,G.Adj i (v k) :=
    fun h => (cover i h).elim a (fun t => t.elim b c)
  refine ⟨g,fun i a b c => prof i (reg a b c),?_⟩
  intro ax ay cx cy hx hy nx ny misses bound
  let col (i : Fin 25) := if i=x then cx else if i=y then cy else g i
  let off (z : Fin 25) (c : Fin 5) (i : Fin 25) : ℕ :=
    if i≠r ∧ G.Adj z i ∧ ¬(g i=c+1 ∨ c=g i+1) then 1 else 0
  let row (i j : Fin 25) := (if i=x then off x cx j else 0)+(if i=y then off y cy j else 0)
  have atX : col x=cx := by simp [col]
  have atY : col y=cy := by simp [col,xy.symm]
  have away {z i a c} (zi : G.Adj z i) (za : G.Adj z (v a)) (nc : c=a+1 ∨ a=c+1)
      (regular : ¬∃! k,G.Adj i (v k)) : c≠g i := by
    intro eq
    have ia := (prof i regular a).mpr (eq ▸ nc.symm)
    exact tri _ (is3Clique_triple_iff.mpr ⟨zi,za,ia⟩)
  have atPole {j} (jr : j≠r) (jx : G.Adj x j) : col x≠col j := by
    have jy : j≠y := fun e => ind (e ▸ jx)
    simpa [col,jx.ne.symm,jy] using away jx hx nx (reg jx.ne.symm jy jr)
  have atOther {j} (jr : j≠r) (jy : G.Adj y j) : col y≠col j := by
    have jx : j≠x := fun e => ind (e ▸ jy.symm)
    simpa [col,xy.symm,jy.ne.symm,jx] using away jy hy ny (reg jx jy.ne.symm jr)
  have proper (i) (ir : i≠r) (j) (jr : j≠r) (ij : G.Adj i j) : col i≠col j := by
    by_cases a : i=x
    · subst i; exact atPole jr ij
    by_cases b : i=y
    · subst i; exact atOther jr ij
    by_cases c : j=x
    · subst j; exact (atPole ir ij.symm).symm
    by_cases d : j=y
    · subst j; exact (atOther ir ij.symm).symm
    have near := maps i (reg a b ir) j (reg c d jr) ij
    have ne : ∀ u t : Fin 5, t=u+1 ∨ u=t+1 → u≠t := by decide +kernel
    simpa [col,a,b,c,d] using ne _ _ near
  apply cut_of_repair G tri r col proper
  have edge (i j : Fin 25) :
      (if G.Adj i j ∧ i≠r ∧ j≠r ∧ ¬(col j=col i+1 ∨ col i=col j+1) then (1:ℕ) else 0)
      ≤ row i j+row j i := by
    split_ifs with bad
    · obtain ⟨ij,ir,jr,fault⟩ := bad
      by_cases a : i=x
      · subst i
        have b := ij.ne.symm
        have c : j≠y := fun h => ind (h ▸ ij)
        simp only [atX,col,if_neg b,if_neg c] at fault
        simp [row,off,ij,jr,(not_or.mp fault).1,(not_or.mp fault).2,b,c,xy]
      by_cases b : i=y
      · subst i
        have a' := ij.ne.symm
        have c : j≠x := fun h => ind (h ▸ ij.symm)
        simp only [atY,col,if_neg a',if_neg c] at fault
        simp [row,off,ij,jr,(not_or.mp fault).1,(not_or.mp fault).2,a',c,xy.symm]
      by_cases c : j=x
      · subst j
        have wrong : ¬(g i=cx+1 ∨ cx=g i+1) := fun h => fault (by simpa [col,a,b] using h.symm)
        simp [row,off,ij.symm,ir,(not_or.mp wrong).1,(not_or.mp wrong).2,a,b,xy]
      by_cases d : j=y
      · subst j
        have wrong : ¬(g i=cy+1 ∨ cy=g i+1) := fun h => fault (by simpa [col,a,b,xy.symm] using h.symm)
        simp [row,off,ij.symm,ir,(not_or.mp wrong).1,(not_or.mp wrong).2,a,b,xy.symm]
      exact (fault (by simpa [col,a,b,c,d] using maps i (reg a b ir) j (reg c d jr) ij)).elim
    · exact Nat.zero_le _
  have rows : (∑ i,∑ j,row i j)=misses x cx+misses y cy := by
    simp only [row,sum_add_distrib]
    simp_rw [← Finset.ite_sum_zero]
    simp [misses,off]
  have cols : (∑ i,∑ j,row j i)=misses x cx+misses y cy := sum_comm.trans rows
  have sumBound := sum_le_sum (s:=univ) (fun i _ => sum_le_sum (s:=univ) (fun j _ => edge i j))
  simp only [sum_add_distrib,rows,cols] at sumBound
  omega

/-- The bounds hold for any choice of an edge pq of the three exceptions
whose endpoint q misses the third exception r. -/
lemma triple_obstruction (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3)
    (bad : ∀ f : Fin 25 → Bool, 50 < ∑ i,∑ j,if G.Adj i j ∧ f i=f j then (1:ℕ) else 0)
    (v : Fin 5 → Fin 25) (cyc : ∀ i,G.Adj (v i) (v (i+1)))
    (dom : ∀ x,∃ i,G.Adj x (v i)) (p q r : Fin 25) (pq : G.Adj p q)
    (rp : r≠p) (rq : r≠q) (miss : ¬G.Adj r q)
    (cover : ∀ x, (∃! i,G.Adj x (v i)) → x=p ∨ x=q ∨ x=r) :
    let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
    let d (i : Fin 25) := ∑ j,w i j
    let m := G.edgeFinset.card
    m ≤ 121 ∧ d p+d q ≤ 20 ∧ 130+(if G.Adj r p then 4 else 0) ≤ m+d p+d q := by
  classical
  intro w d m
  obtain ⟨ap,hp⟩ := dom p
  obtain ⟨aq,hq⟩ := dom q
  obtain ⟨f,hf⟩ := triple_cuts G tri v cyc dom p q r pq rp rq miss ap aq hp hq cover
  change 5*_+_ ≤ (∑ i,∑ j,w i j)+2*(d p+d q) at hf
  have count : (∑ i,∑ j,w i j)=2*m := edge_sum G
  have ev := even_cost G f
  have hb := bad f
  refine ⟨(obstruction_bounds G tri bad).1,endpoint_cap G tri bad p q pq,?_⟩
  by_cases h : G.Adj r p <;> simp only [h,if_true,if_false] at hf ⊢ <;> omega

/-- A spanning bipartite subgraph after at most 25 edge deletions. The
unconditional upper endpoint is 109 edges for an isolated third exception
and 113 for a path. The endpoint-degree test applies above these thresholds. -/
lemma bipartize_three (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3)
    (v : Fin 5 → Fin 25) (cyc : ∀ i,G.Adj (v i) (v (i+1)))
    (dom : ∀ x,∃ i,G.Adj x (v i)) (p q r : Fin 25) (pq : G.Adj p q)
    (rp : r≠p) (rq : r≠q) (miss : ¬G.Adj r q)
    (cover : ∀ x, (∃! i,G.Adj x (v i)) → x=p ∨ x=q ∨ x=r)
    (small : G.edgeFinset.card + min 20 (G.degree p + G.degree q) <
      130+(if G.Adj r p then 4 else 0)) :
    ∃ H : SimpleGraph (Fin 25), H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 25 := by
  classical
  suffices cut : ∃ f : Fin 25 → Bool,
      (∑ i,∑ j,if G.Adj i j ∧ f i=f j then (1:ℕ) else 0) ≤ 50 by
    obtain ⟨f,hf⟩ := cut
    exact cut_subgraph G f hf
  by_contra! bad
  obtain ⟨_,cap,lo⟩ := triple_obstruction G tri bad v cyc dom p q r pq rp rq miss cover
  have deg (i : Fin 25) : (∑ j,if G.Adj i j then (1:ℕ) else 0) = G.degree i := by
    simp [←G.card_neighborFinset_eq_degree,neighborFinset_eq_filter,Finset.sum_boole]
  dsimp only at cap lo
  simp only [deg] at cap lo
  rw [min_eq_right cap] at small
  omega

/-- All remaining configurations outside the three-exception case with an edge. -/
def H1 : Prop := ∀ (G : SimpleGraph (Fin 25)), G.CliqueFree 3 →
    let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
    let d (i : Fin 25) := ∑ j,w i j
    let m := G.edgeFinset.card
    100 ≤ m → m ≤ 121 →
    (¬∃ g : Fin 25 → Fin 5, ∀ i j,G.Adj i j → g j=g i+1 ∨ g i=g j+1) →
    (∀ i,2*(∑ j,w i j*d j)+51 ≤ 2*m) →
    (∀ W : Finset (Fin 25), ∀ b : Fin 25 → Bool,
      (∀ i ∈ W, ∀ j ∈ W,G.Adj i j → b i ≠ b j) →
      (∑ i ∈ W,∑ j ∈ W,w i j)+102 ≤ 2*m) →
    (∀ p q,G.Adj p q → d p+d q ≤ 20) →
    (∀ p q,G.Adj p q → ¬∃ g : Fin 25 → Fin 5,
      ∀ i,i≠p → i≠q → ∀ j,j≠p → j≠q → G.Adj i j → g j=g i+1 ∨ g i=g j+1) →
    ∀ v : Fin 5 → Fin 25, (∀ i,G.Adj (v i) (v (i+1))) →
    (∀ x,∃ i,G.Adj x (v i)) →
    let X := univ.filter (fun x => ∃! i,G.Adj x (v i))
    (∀ r ∈ X, ∀ g : Fin 25 → Fin 5, (∀ i, i≠r → ∀ j, j≠r → G.Adj i j → g i≠g j) →
      130 ≤ m+(∑ i,∑ j,if G.Adj i j ∧ i≠r ∧ j≠r ∧ ¬(g j=g i+1 ∨ g i=g j+1) then 1 else 0)) →
    (X.card≠3 ∨ ∀ p ∈ X,∀ q ∈ X,¬G.Adj p q) →
    ∃ f : Fin 25 → Bool, (∑ i,∑ j,if G.Adj i j ∧ f i=f j then 1 else 0) ≤ (50:ℕ)

/-- One exceptional edge with an isolated third exception, from 110 edges. -/
def H2 : Prop := ∀ (G : SimpleGraph (Fin 25)), G.CliqueFree 3 →
    let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
    let d (i : Fin 25) := ∑ j,w i j
    let m := G.edgeFinset.card
    100 ≤ m → m ≤ 121 →
    (¬∃ g : Fin 25 → Fin 5, ∀ i j,G.Adj i j → g j=g i+1 ∨ g i=g j+1) →
    (∀ i,2*(∑ j,w i j*d j)+51 ≤ 2*m) →
    (∀ W : Finset (Fin 25), ∀ b : Fin 25 → Bool,
      (∀ i ∈ W, ∀ j ∈ W,G.Adj i j → b i ≠ b j) →
      (∑ i ∈ W,∑ j ∈ W,w i j)+102 ≤ 2*m) →
    (∀ p q,G.Adj p q → d p+d q ≤ 20) →
    (∀ p q,G.Adj p q → ¬∃ g : Fin 25 → Fin 5,
      ∀ i,i≠p → i≠q → ∀ j,j≠p → j≠q → G.Adj i j → g j=g i+1 ∨ g i=g j+1) →
    ∀ v : Fin 5 → Fin 25, (∀ i,G.Adj (v i) (v (i+1))) →
    (∀ x,∃ i,G.Adj x (v i)) →
    let X := univ.filter (fun x => ∃! i,G.Adj x (v i))
    (∀ r ∈ X, ∀ g : Fin 25 → Fin 5, (∀ i, i≠r → ∀ j, j≠r → G.Adj i j → g i≠g j) →
      130 ≤ m+(∑ i,∑ j,if G.Adj i j ∧ i≠r ∧ j≠r ∧ ¬(g j=g i+1 ∨ g i=g j+1) then 1 else 0)) →
    ∀ p q r : Fin 25, X={p,q,r} → G.Adj p q → r≠p → r≠q → ¬G.Adj r q →
    ¬G.Adj r p → 110 ≤ m → 130 ≤ m+d p+d q →
    ∃ f : Fin 25 → Bool, (∑ i,∑ j,if G.Adj i j ∧ f i=f j then 1 else 0) ≤ (50:ℕ)

/-- The three exceptional vertices form a path, from 114 edges. -/
def H3 : Prop := ∀ (G : SimpleGraph (Fin 25)), G.CliqueFree 3 →
    let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
    let d (i : Fin 25) := ∑ j,w i j
    let m := G.edgeFinset.card
    100 ≤ m → m ≤ 121 →
    (¬∃ g : Fin 25 → Fin 5, ∀ i j,G.Adj i j → g j=g i+1 ∨ g i=g j+1) →
    (∀ i,2*(∑ j,w i j*d j)+51 ≤ 2*m) →
    (∀ W : Finset (Fin 25), ∀ b : Fin 25 → Bool,
      (∀ i ∈ W, ∀ j ∈ W,G.Adj i j → b i ≠ b j) →
      (∑ i ∈ W,∑ j ∈ W,w i j)+102 ≤ 2*m) →
    (∀ p q,G.Adj p q → d p+d q ≤ 20) →
    (∀ p q,G.Adj p q → ¬∃ g : Fin 25 → Fin 5,
      ∀ i,i≠p → i≠q → ∀ j,j≠p → j≠q → G.Adj i j → g j=g i+1 ∨ g i=g j+1) →
    ∀ v : Fin 5 → Fin 25, (∀ i,G.Adj (v i) (v (i+1))) →
    (∀ x,∃ i,G.Adj x (v i)) →
    let X := univ.filter (fun x => ∃! i,G.Adj x (v i))
    (∀ r ∈ X, ∀ g : Fin 25 → Fin 5, (∀ i, i≠r → ∀ j, j≠r → G.Adj i j → g i≠g j) →
      130 ≤ m+(∑ i,∑ j,if G.Adj i j ∧ i≠r ∧ j≠r ∧ ¬(g j=g i+1 ∨ g i=g j+1) then 1 else 0)) →
    ∀ p q r : Fin 25, X={p,q,r} → G.Adj p q → r≠p → r≠q → ¬G.Adj r q →
    G.Adj r p → 114 ≤ m → 134 ≤ m+d p+d q →
    ∃ f : Fin 25 → Bool, (∑ i,∑ j,if G.Adj i j ∧ f i=f j then 1 else 0) ≤ (50:ℕ)

section
set_option maxHeartbeats 3200000 in
theorem main : H1 → H2 → H3 → OMA.R_Erdos23_erdos_23_variants_n5_R2_H1_R1.H1 := by
  classical
  intro other isolated path G tri w d S dense _upper nonmap rooted induced a b c d' e ab bc cd de ea dom
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
  let m := G.edgeFinset.card
  have count : S=2*m := edge_sum G
  have low : 100 ≤ m := by omega
  rw [count] at rooted induced
  by_contra! bad
  have fail (cut : ∃ f : Fin 25 → Bool,
      (∑ i,∑ j,if G.Adj i j ∧ f i=f j then (1:ℕ) else 0) ≤ 50) : False := by
    obtain ⟨f,hf⟩ := cut
    exact (not_lt_of_ge hf) (bad f)
  have cap : m ≤ 121 := (obstruction_bounds G tri bad).1
  have allCaps := endpoint_cap G tri bad
  have noPair := no_pair_map G tri bad
  have errors (r : Fin 25) (_ : r∈X) (g : Fin 25 → Fin 5)
      (proper : ∀ i, i≠r → ∀ j, j≠r → G.Adj i j → g i≠g j) :
      130 ≤ m+(∑ i,∑ j,if G.Adj i j ∧ i≠r ∧ j≠r ∧ ¬(g j=g i+1 ∨ g i=g j+1) then 1 else 0) := by
    apply Nat.le_of_not_gt
    intro h
    exact fail (cut_of_repair G tri r g proper h)
  by_cases rest : X.card≠3 ∨ ∀ p ∈ X,∀ q ∈ X,¬G.Adj p q
  · exact fail (other G tri low cap nonmap rooted induced allCaps noPair v cycle hits errors rest)
  push Not at rest
  obtain ⟨size,p,hp,q,hq,pq⟩ := rest
  obtain ⟨r,hr,rp,rq⟩ : ∃ r ∈ X, r≠p ∧ r≠q := by
    by_contra! no
    have sub : X ⊆ {p,q} := by
      intro x hx
      by_cases a : x=p
      · simp [a]
      · simp [no x hx a]
    have small := card_le_card sub
    simp [pq.ne,size] at small
  have eq : X={p,q,r} := by
    symm
    apply eq_of_subset_of_card_le
    · simpa [insert_subset_iff] using And.intro hp (And.intro hq hr)
    · simp [size,pq.ne,rp.symm,rq.symm]
  have use_edge (p q r : Fin 25) (eq : X={p,q,r}) (pq : G.Adj p q)
      (rp : r≠p) (rq : r≠q) (miss : ¬G.Adj r q) : False := by
    have cover (x) (hx : ∃! i,G.Adj x (v i)) : x=p ∨ x=q ∨ x=r := by
      have mem : x∈X := mem_filter.mpr ⟨mem_univ _,hx⟩
      simpa [eq] using mem
    obtain ⟨_,ec,lc⟩ := triple_obstruction G tri bad v cycle hits p q r pq rp rq miss cover
    change d p+d q ≤ 20 at ec
    change 130+(if G.Adj r p then 4 else 0) ≤ m+d p+d q at lc
    by_cases h : G.Adj r p
    · simp only [h,if_true] at lc
      exact fail (path G tri low cap nonmap rooted induced allCaps noPair v cycle hits errors
        p q r eq pq rp rq miss h (by omega) lc)
    · simp only [h,if_false,Nat.add_zero] at lc
      exact fail (isolated G tri low cap nonmap rooted induced allCaps noPair v cycle hits errors
        p q r eq pq rp rq miss h (by omega) lc)
  by_cases miss : G.Adj r q
  · have no : ¬G.Adj r p := fun h => tri _ (is3Clique_triple_iff.mpr ⟨h,miss,pq⟩)
    exact use_edge q p r (by rw [eq,insert_comm p q]) pq.symm rq rp no
  · exact use_edge p q r eq pq rp rq miss
end

end OMA.R_Erdos23_erdos_23_variants_n5_R2_H1_R1_H1_R3
