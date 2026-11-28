import OMAReductions.R_Erdos713_erdos_713_parts_i_R1_H1_R1_H2_R1

/-!
Cores with one side of degree two that contain a four-cycle.

For r, t at least two let K(r,t) be the graph with r main vertices in which
every pair of main vertices has t private common neighbours (the witnesses),
and no other vertices or edges. This is the t-fold fattened subdivision of the
complete graph on r vertices, one of the universal graphs of Erdős for bipartite
graphs with one side of degree at most two.

Let J be a connected bipartite graph of minimum degree at least two with a
proper two-colouring in which every vertex of colour one has degree two, and in
which some two vertices of colour zero have two common neighbours. Let t be the
largest number of common neighbours of two distinct vertices of colour zero.
Then the complete bipartite graph with parts of sizes 2 and t is contained in J,
and J is contained in K(r,t) with r the order of J: a vertex of colour zero is
sent to itself as a main vertex, and a vertex of colour one is sent to a witness
of its pair of neighbours, the witnesses of one pair being used injectively
(at most t vertices have the same pair of neighbours). Extremal numbers are
monotone under containment, so

  ex(n, K(2,t)-biclique) ≤ ex(n, J) ≤ ex(n, K(r,t)).

H1 is the upper bound ex(n, K(r,t)) ≤ (1+o(1)) (sqrt(t-1)/2) n^(3/2) and
H2 is the matching lower bound for the complete bipartite graph, due to
Füredi, New asymptotics for bipartite Turán numbers, JCTA 75 (1996); for the
order of magnitude of the universal graphs see Füredi, On a Turán type problem
of Erdős, Combinatorica 11 (1991). Together they give the power law with
exponent 3/2 and constant sqrt(t-1)/2 for every J in this class. H3 is the
power law for the remaining cores.
-/

open SimpleGraph Filter Asymptotics Finset
open scoped Topology Classical

namespace E713Fat

/-- Two sided eventual bounds with every relative error give asymptotic equivalence. -/
theorem squeeze (f : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (up : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, f n ≤ (1+ε)*c*(n:ℝ)^(3/2:ℝ))
    (lo : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (1-ε)*c*(n:ℝ)^(3/2:ℝ) ≤ f n) :
    IsEquivalent atTop f (fun n : ℕ => c*(n:ℝ)^(3/2:ℝ)) := by
  have pos : ∀ᶠ n : ℕ in atTop, 0 < c*(n:ℝ)^(3/2:ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (0:ℝ) < n := by exact_mod_cast hn
    positivity
  rw [isEquivalent_iff_tendsto_one (pos.mono fun _ h => h.ne'),Metric.tendsto_nhds]
  intro ε he
  filter_upwards [up (ε/2) (by positivity),lo (ε/2) (by positivity),pos] with n h1 h2 h3
  have h4 := mul_pos he h3
  rw [Real.dist_eq,abs_lt]
  simp only [Pi.div_apply]
  constructor
  · rw [lt_sub_iff_add_lt,lt_div_iff₀ h3]
    nlinarith
  · rw [sub_lt_iff_lt_add,div_lt_iff₀ h3]
    nlinarith

/-- Two distinct vertices with a set of common neighbours span a complete bipartite graph. -/
theorem biclique {V : Type*} (J : SimpleGraph V) (a b : V) (ne : a ≠ b) (S : Finset V)
    (hS : ∀ u ∈ S, J.Adj a u ∧ J.Adj b u) :
    completeBipartiteGraph (Fin 2) (Fin S.card) ⊑ J := by
  classical
  let e := S.equivFin.symm
  let f : Fin 2 ⊕ Fin S.card → V := Sum.elim ![a,b] (fun k => (e k : V))
  have left (i : Fin 2) (k : Fin S.card) : J.Adj (f (Sum.inl i)) (f (Sum.inr k)) := by
    have h := hS _ (e k).2
    fin_cases i
    · exact h.1
    · exact h.2
  refine ⟨⟨⟨f,?_⟩,?_⟩⟩
  · rintro (i|i) (j|j) h
    · simp [completeBipartiteGraph] at h
    · exact left i j
    · exact (left j i).symm
    · simp [completeBipartiteGraph] at h
  · rintro (i|i) (j|j) h
    · change ![a,b] i = ![a,b] j at h
      fin_cases i <;> fin_cases j <;> first | rfl | exact (ne h).elim | exact (ne h.symm).elim
    · exact ((left i j).ne h).elim
    · exact ((left j i).ne h.symm).elim
    · change (e i : V) = (e j : V) at h
      exact congrArg Sum.inr (e.injective (Subtype.ext h))

/-- Among vertices with the same neighbourhood, the number of smaller ones is strictly monotone. -/
theorem rank_lt {r : ℕ} (J : SimpleGraph (Fin r)) (w w' : Fin r)
    (same : J.neighborFinset w = J.neighborFinset w') (lt : w < w') :
    (univ.filter (fun z => J.neighborFinset z = J.neighborFinset w ∧ z < w)).card <
      (univ.filter (fun z => J.neighborFinset z = J.neighborFinset w' ∧ z < w')).card := by
  apply card_lt_card
  refine ⟨fun z hz => ?_,fun sub => ?_⟩
  · obtain ⟨h1,h2⟩ := (mem_filter.mp hz).2
    exact mem_filter.mpr ⟨mem_univ _,h1.trans same,h2.trans lt⟩
  · have h := sub (mem_filter.mpr ⟨mem_univ _,same,lt⟩)
    exact lt_irrefl _ (mem_filter.mp h).2.2

/-- A bipartite graph with one side of degree two embeds in the fattened subdivision of a complete graph. -/
theorem fat {r t : ℕ} (J : SimpleGraph (Fin r)) (c : Fin r → Bool)
    (proper : ∀ x y, J.Adj x y → c x ≠ c y) (two : ∀ v, c v = true → J.degree v = 2)
    (cap : ∀ a b, a ≠ b → c a = false → c b = false →
      (J.neighborFinset a ∩ J.neighborFinset b).card ≤ t) :
    J ⊑ SimpleGraph.fromRel (fun (u v : Fin r ⊕ ({p : Fin r × Fin r // p.1 < p.2} × Fin t)) =>
      ∃ i p k, u = Sum.inl i ∧ v = Sum.inr (p,k) ∧ (i = p.1.1 ∨ i = p.1.2)) := by
  classical
  have spec (w : Fin r) : ∃ y : Fin r ⊕ ({p : Fin r × Fin r // p.1 < p.2} × Fin t),
      (c w = false → y = Sum.inl w) ∧ (c w = true → ∃ (p : {p : Fin r × Fin r // p.1 < p.2}) (k : Fin t),
        y = Sum.inr (p,k) ∧ J.neighborFinset w = {p.1.1,p.1.2} ∧
        (k:ℕ) = (univ.filter (fun z => J.neighborFinset z = J.neighborFinset w ∧ z < w)).card) := by
    cases hw : c w with
    | false => exact ⟨Sum.inl w,fun _ => rfl,fun h => by simp at h⟩
    | true =>
      have card := two w hw
      rw [← J.card_neighborFinset_eq_degree] at card
      have ordered : ∃ a b, a < b ∧ J.neighborFinset w = {a,b} := by
        obtain ⟨x,y,xy,eq⟩ := card_eq_two.mp card
        rcases lt_or_gt_of_ne xy with h | h
        · exact ⟨x,y,h,eq⟩
        · exact ⟨y,x,h,by rw [eq,pair_comm]⟩
      obtain ⟨a,b,ab,eq⟩ := ordered
      have wa : J.Adj w a := (J.mem_neighborFinset w a).mp (by rw [eq]; simp)
      have wb : J.Adj w b := (J.mem_neighborFinset w b).mp (by rw [eq]; simp)
      have ca : c a = false := by
        have h := proper w a wa
        rw [hw] at h
        simpa using h.symm
      have cb : c b = false := by
        have h := proper w b wb
        rw [hw] at h
        simpa using h.symm
      have bound := cap a b ab.ne ca cb
      have small : (univ.filter (fun z => J.neighborFinset z = J.neighborFinset w ∧ z < w)).card < t := by
        apply lt_of_lt_of_le _ bound
        apply card_lt_card
        refine ⟨fun z hz => ?_,fun sub => ?_⟩
        · obtain ⟨h1,_⟩ := (mem_filter.mp hz).2
          have za : J.Adj z a := (J.mem_neighborFinset z a).mp (by rw [h1,eq]; simp)
          have zb : J.Adj z b := (J.mem_neighborFinset z b).mp (by rw [h1,eq]; simp)
          exact mem_inter.mpr ⟨(J.mem_neighborFinset a z).mpr za.symm,(J.mem_neighborFinset b z).mpr zb.symm⟩
        · have h := sub (mem_inter.mpr ⟨(J.mem_neighborFinset a w).mpr wa.symm,(J.mem_neighborFinset b w).mpr wb.symm⟩)
          exact lt_irrefl _ (mem_filter.mp h).2.2
      exact ⟨Sum.inr (⟨(a,b),ab⟩,⟨_,small⟩),fun h => by simp at h,fun _ => ⟨⟨(a,b),ab⟩,⟨_,small⟩,rfl,eq,rfl⟩⟩
  choose g low high using spec
  have edge (x y : Fin r) (adj : J.Adj x y) (cx : c x = false) (cy : c y = true) :
      (SimpleGraph.fromRel (fun (u v : Fin r ⊕ ({p : Fin r × Fin r // p.1 < p.2} × Fin t)) =>
        ∃ i p k, u = Sum.inl i ∧ v = Sum.inr (p,k) ∧ (i = p.1.1 ∨ i = p.1.2))).Adj (g x) (g y) := by
    obtain ⟨p,k,gy,nb,_⟩ := high y cy
    have mem : x ∈ J.neighborFinset y := (J.mem_neighborFinset y x).mpr adj.symm
    rw [nb,mem_insert,mem_singleton] at mem
    rw [low x cx,gy]
    exact ⟨Sum.inl_ne_inr,Or.inl ⟨x,p,k,rfl,rfl,mem⟩⟩
  refine ⟨⟨⟨g,?_⟩,?_⟩⟩
  · intro x y adj
    have diff := proper x y adj
    cases cx : c x with
    | false =>
      cases cy : c y with
      | false => rw [cx,cy] at diff; exact (diff rfl).elim
      | true => exact edge x y adj cx cy
    | true =>
      cases cy : c y with
      | false => exact (edge y x adj.symm cy cx).symm
      | true => rw [cx,cy] at diff; exact (diff rfl).elim
  · intro x y eq
    change g x = g y at eq
    cases cx : c x with
    | false =>
      cases cy : c y with
      | false =>
        rw [low x cx,low y cy] at eq
        exact Sum.inl.inj eq
      | true =>
        obtain ⟨p,k,gy,_⟩ := high y cy
        rw [low x cx,gy] at eq
        exact (Sum.inl_ne_inr eq).elim
    | true =>
      obtain ⟨p,k,gx,nx,kx⟩ := high x cx
      cases cy : c y with
      | false =>
        rw [low y cy,gx] at eq
        exact (Sum.inr_ne_inl eq).elim
      | true =>
        obtain ⟨p',k',gy,ny,ky⟩ := high y cy
        rw [gx,gy] at eq
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Sum.inr.inj eq)
        have same : J.neighborFinset x = J.neighborFinset y := nx.trans ny.symm
        rcases lt_trichotomy x y with h | h | h
        · have := rank_lt J x y same h
          omega
        · exact h
        · have := rank_lt J y x same.symm h
          omega

end E713Fat

namespace OMA.R_Erdos713_erdos_713_parts_i_R1_H1_R1_H2_R1_H1_R1

/-- Upper bound for the fattened subdivision of a complete graph: r main vertices, and t private
common neighbours for every pair of main vertices. Its extremal number is at most
(1+o(1)) (sqrt(t-1)/2) n^(3/2). -/
def H1 : Prop := ∀ r t : ℕ, 2 ≤ r → 2 ≤ t → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    (extremalNumber n (SimpleGraph.fromRel (fun (u v : Fin r ⊕ ({p : Fin r × Fin r // p.1 < p.2} × Fin t)) =>
      ∃ i p k, u = Sum.inl i ∧ v = Sum.inr (p,k) ∧ (i = p.1.1 ∨ i = p.1.2))) : ℝ) ≤
      (1+ε)*(Real.sqrt ((t:ℝ)-1)/2)*(n:ℝ)^(3/2:ℝ)

/-- Füredi's lower bound for complete bipartite graphs with one side of size two. -/
def H2 : Prop := ∀ t : ℕ, 2 ≤ t → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    (1-ε)*(Real.sqrt ((t:ℝ)-1)/2)*(n:ℝ)^(3/2:ℝ) ≤
      (extremalNumber n (completeBipartiteGraph (Fin 2) (Fin t)) : ℝ)

/-- The superlinear power law for the remaining cores: those without a proper two-colouring in
which one colour class has all degrees at most two and two vertices of the other class have
two common neighbours. -/
def H3 : Prop := ∀ (r : ℕ) (J : SimpleGraph (Fin r)), J.IsBipartite → J.Connected →
    (∀ v, 2 ≤ J.degree v) → 5 ≤ r → 6 ≤ J.edgeFinset.card →
    completeBipartiteGraph (Fin 2) (Fin 2) ⊑ J →
    ¬ Nonempty (J ≃g completeBipartiteGraph (Fin 2) (Fin 2)) →
    (∀ p : ℕ, p.Prime → p ^ 3 ≤ extremalNumber (2 * p ^ 2) J) →
    ¬ (∃ c : Fin r → Bool, (∀ x y, J.Adj x y → c x ≠ c y) ∧ (∀ v, c v = true → J.degree v ≤ 2) ∧
      ∃ a b u v, a ≠ b ∧ u ≠ v ∧ c a = false ∧ c b = false ∧
        J.Adj a u ∧ J.Adj b u ∧ J.Adj a v ∧ J.Adj b v) →
    Tendsto (fun n : ℕ => (extremalNumber n J : ℝ)/n) atTop atTop →
    ∃ α c : ℝ, α ∈ Set.Ioo 1 2 ∧ 0<c ∧ IsEquivalent atTop
      (fun n : ℕ => (extremalNumber n J : ℝ)) (fun n => c*(n:ℝ)^α)

theorem main : H1 → H2 → H3 → OMA.R_Erdos713_erdos_713_parts_i_R1_H1_R1_H2_R1.H1 := by
  intro upper lower rest r J bip conn deg r5 e6 c4 square primes growth
  by_cases cls : ∃ c : Fin r → Bool, (∀ x y, J.Adj x y → c x ≠ c y) ∧ (∀ v, c v = true → J.degree v ≤ 2) ∧
      ∃ a b u v, a ≠ b ∧ u ≠ v ∧ c a = false ∧ c b = false ∧
        J.Adj a u ∧ J.Adj b u ∧ J.Adj a v ∧ J.Adj b v
  swap
  · exact rest r J bip conn deg r5 e6 c4 square primes cls growth
  obtain ⟨c,proper,thin,a,b,u,v,ab,uv,ca,cb,au,bu,av,bv⟩ := cls
  let P : Finset (Fin r × Fin r) := univ.filter (fun p => p.1 ≠ p.2 ∧ c p.1 = false ∧ c p.2 = false)
  have start : (a,b) ∈ P := mem_filter.mpr ⟨mem_univ _,ab,ca,cb⟩
  obtain ⟨m,hm,best⟩ := exists_max_image P
    (fun p => (J.neighborFinset p.1 ∩ J.neighborFinset p.2).card) ⟨_,start⟩
  obtain ⟨_,m12,cm1,cm2⟩ := mem_filter.mp hm
  let S := J.neighborFinset m.1 ∩ J.neighborFinset m.2
  have t2 : 2 ≤ S.card := by
    have pair : ({u,v} : Finset (Fin r)) ⊆ J.neighborFinset a ∩ J.neighborFinset b := by
      intro z hz
      rw [mem_insert,mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact mem_inter.mpr ⟨(J.mem_neighborFinset _ _).mpr au,(J.mem_neighborFinset _ _).mpr bu⟩
      · exact mem_inter.mpr ⟨(J.mem_neighborFinset _ _).mpr av,(J.mem_neighborFinset _ _).mpr bv⟩
    have h := (card_le_card pair).trans (best _ start)
    rwa [card_pair uv] at h
  have r2 : 2 ≤ r := by
    have h := Fintype.one_lt_card_iff.mpr ⟨a,b,ab⟩
    rw [Fintype.card_fin] at h
    exact h
  have inner : completeBipartiteGraph (Fin 2) (Fin S.card) ⊑ J :=
    E713Fat.biclique J m.1 m.2 m12 S (fun z hz =>
      ⟨(J.mem_neighborFinset _ _).mp (mem_inter.mp hz).1,(J.mem_neighborFinset _ _).mp (mem_inter.mp hz).2⟩)
  have outer := E713Fat.fat (t:=S.card) J c proper (fun w hw => le_antisymm (thin w hw) (deg w))
    (fun x y xy cx cy => best (x,y) (mem_filter.mpr ⟨mem_univ _,xy,cx,cy⟩))
  have tpos : 0 < Real.sqrt ((S.card:ℝ)-1)/2 := by
    have : (2:ℝ) ≤ S.card := by exact_mod_cast t2
    have := Real.sqrt_pos.mpr (show 0 < (S.card:ℝ)-1 by linarith)
    positivity
  refine ⟨3/2,Real.sqrt ((S.card:ℝ)-1)/2,by norm_num,tpos,E713Fat.squeeze _ _ tpos ?_ ?_⟩
  · intro ε he
    filter_upwards [upper r S.card r2 t2 ε he] with n hn
    exact le_trans (by exact_mod_cast outer.extremalNumber_le) hn
  · intro ε he
    filter_upwards [lower S.card t2 ε he] with n hn
    exact le_trans hn (by exact_mod_cast inner.extremalNumber_le)

end OMA.R_Erdos713_erdos_713_parts_i_R1_H1_R1_H2_R1_H1_R1
