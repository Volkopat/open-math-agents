import OMAReductions.R_Erdos1182_erdos_1182_variants_small_values_R1_H1_R1_H1_R1


/-! The ten-vertex covering. Classify graphs avoiding the cores of both forbidden masks.
Delete a minimum-degree vertex, classify the induced graph, and certify all relevant extensions.
Only minimum-degree attachments are needed. The final table is empty. -/

/- Finite records for the ten-vertex forbidden-graph classification. -/
namespace Astra1182.Ten
def threshold : Nat → Nat
  | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 7 | 6 => 10 | 7 => 14 | 8 => 18 | 9 => 22 | 10 => 27 | _ => 0

def pair (t i j : Nat) := let a:=min i j; let b:=max i j
  decide (i≠j) && t.testBit (a*(19-a)/2 + b-a-1)
def augment (n t h i j : Nat) := if i=j then false else
  if max i j=n then h.testBit (min i j) else pair t i j

def order (kind : Bool) : Nat := if kind then 8 else 10
def mask (kind : Bool) : Nat := if kind then 72057645653176374 else 618970019714747783169716278
def core (kind : Bool) (i j : Fin (order kind)) :=
  (mask kind).testBit ((min i j).val*10+(max i j).val)
def label (n code i : Nat) : Fin (n+1) := Fin.ofNat (n+1) ((code >>> (4*i)) %16)
def weight (n h : Nat) := (Finset.univ.filter (fun i : Fin n => h.testBit i.val)).card

theorem pair_symm (t i j) : pair t i j = pair t j i := by simp [pair,min_comm i j,max_comm i j,(eq_comm : i=j ↔ j=i)]
theorem aug_symm (n t h i j) : augment n t h i j = augment n t h j i := by
  simp only [augment, min_comm i j, max_comm i j,pair_symm t i j,(eq_comm : i=j ↔ j=i)]

abbrev Shape := Nat × Nat
abbrev CopyRule := Nat × Bool × Nat
abbrev IsoRule := Nat × Nat × Nat

def goodCopy (n t : Nat) (w : CopyRule) : Prop :=
  Function.Injective (fun i : Fin (order w.2.1) => label n w.2.2 i.val) ∧
    ∀ i j : Fin (order w.2.1), core w.2.1 i j=true →
      augment n t w.1 (label n w.2.2 i.val).val (label n w.2.2 j.val).val = true
instance (n t w) : Decidable (goodCopy n t w) := by unfold goodCopy; infer_instance

def goodIso (n : Nat) (s : Shape) (children : List Shape) (w : IsoRule) : Prop :=
  (w.2.1,s.2 + weight n w.1) ∈ children ∧
  Function.Injective (fun i : Fin (n+1) => label n w.2.2 i.val) ∧
    ∀ i j : Fin (n+1), pair w.2.1 i.val j.val =
      augment n s.1 w.1 (label n w.2.2 i.val).val (label n w.2.2 j.val).val
instance (n s c w) : Decidable (goodIso n s c w) := by unfold goodIso; infer_instance

def augmentedDegree (n t h i : Nat) :=
  (Finset.univ.filter (fun j : Fin (n+1) => augment n t h i j.val)).card
def covers (n : Nat) (s : Shape) (ws : List CopyRule) (zs : List IsoRule) : Prop :=
  ∀ h : Fin (2^n), threshold (n+1) ≤ s.2 + weight n h.val → s.2 + weight n h.val ≤ 27 →
    (∀ j : Fin n, weight n h.val ≤ augmentedDegree n s.1 h.val j.val) →
    (∃ w ∈ ws, (w.1 &&& h.val) = w.1) ∨ ∃ z ∈ zs, z.1=h.val
instance (n s ws zs) : Decidable (covers n s ws zs) := by unfold covers; infer_instance

def row (n : Nat) (s : Shape) (next : List Shape) : Prop :=
  ∃ ws : List CopyRule, ∃ zs : List IsoRule, (∀w∈ws, goodCopy n s.1 w) ∧
    (∀z∈zs, goodIso n s next z) ∧ covers n s ws zs

theorem augment_mono {n t r h i j} (inc : r &&& h=r) (hit : augment n t r i j=true) :
    augment n t h i j=true := by
  by_cases hd : i=j
  · simp [augment,hd] at hit
  by_cases hl : max i j=n
  · have old : r.testBit (min i j)=true := by simpa [augment,hd,hl] using hit
    have eq := congrArg (fun x : Nat => x.testBit (min i j)) inc
    simpa [Nat.testBit_and,old,augment,hd,hl] using eq
  · simpa [augment,hd,hl] using hit

theorem dropBound : ∀ n : Fin 10, ∀ m d : Fin 28,
    threshold (n.val+1) ≤ m.val → (n.val+1)*d.val ≤ 2*m.val → threshold n.val ≤ m.val-d.val := by
  decide +kernel

theorem encode (f : Nat → Bool) (n : Nat) :
    ∃ h < 2^n, ∀ i<n, h.testBit i = f i := by
  induction n with
  | zero => exact ⟨0,by decide,by simp⟩
  | succ n ih =>
    obtain ⟨x,hx,bits⟩ := ih
    have hi : x.testBit n=false := Nat.testBit_lt_two_pow hx
    cases hf : f n with
    | false =>
      refine ⟨x,by rw [Nat.pow_succ]; omega,?_⟩
      intro i h
      by_cases he : i=n
      · simpa [he,hf] using hi
      · exact bits _ (by omega)
    | true =>
      refine ⟨2^n+x,by rw [Nat.pow_succ]; omega,?_⟩
      intro i h
      by_cases he : i=n
      · subst i; simp [Nat.testBit_two_pow_add_eq,hi,hf]
      · rw [Nat.testBit_two_pow_add_gt (by omega)]
        exact bits i (by omega)
end Astra1182.Ten

/- Soundness of a one-vertex extension in the forbidden-graph classification. -/
namespace Astra1182.Ten
open SimpleGraph

def HasCore {X : Type} (G : SimpleGraph X) : Prop :=
  ∃ kind : Bool, ∃ e : Fin (order kind) ↪ X, ∀ i j, core kind i j=true → G.Adj (e i) (e j)
def Represents {X : Type} (G : SimpleGraph X) (n mask : Nat) : Prop :=
  ∃ e : Fin n ≃ X, ∀ i j, G.Adj (e i) (e j) ↔ pair mask i.val j.val=true
def Classified {X : Type} [Fintype X] [DecidableEq X] (G : SimpleGraph X) [DecidableRel G.Adj]
    (n : Nat) (shapes : List Shape) :=
  HasCore G ∨ ∃ s ∈ shapes, G.edgeFinset.card=s.2 ∧ Represents G n s.1

theorem aug_old {n t h i j} (hi : i<n) (hj : j<n) : augment n t h i j = pair t i j := by
  by_cases he : i=j
  · simp [augment,pair,he]
  · simp [augment,he,(max_lt hi hj).ne]
theorem aug_last {n t h i} (hi : i<n) : augment n t h n i = h.testBit i := by
  simp [augment,Nat.ne_of_gt hi,max_eq_left hi.le,min_eq_right hi.le]

theorem extendStage {X : Type} [Fintype X] [DecidableEq X] (G : SimpleGraph X) [DecidableRel G.Adj]
    (v : X) (minimal : ∀ x, G.degree v ≤ G.degree x) {n : Nat} (cardX : Fintype.card X=n+1) (s : Shape) (next : List Shape)
    (bound : threshold (n+1) ≤ G.edgeFinset.card) (upper : G.edgeFinset.card ≤ 27)
    (previous : (G.induce {v}ᶜ).edgeFinset.card=s.2) (rep : Represents (G.induce {v}ᶜ) n s.1)
    (records : row n s next) : Classified G (n+1) next := by
  classical
  obtain ⟨e,old⟩ := rep
  let lab : Fin (n+1) → X := Fin.lastCases v (fun i => (e i).val)
  have labLast : lab (Fin.last n)=v := by simp [lab]
  have labCast (i : Fin n) : lab i.castSucc=(e i).val := by simp [lab]
  have inj : Function.Injective lab := by
    intro i j
    refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j
    · simp
    · intro hv; rw [labLast,labCast] at hv; exact ((e b).property (Set.mem_singleton_iff.mpr hv.symm)).elim
    · intro hv; rw [labCast,labLast] at hv; exact ((e a).property (Set.mem_singleton_iff.mpr hv)).elim
    · intro he; rw [labCast,labCast] at he; exact congrArg Fin.castSucc (e.injective (Subtype.ext he))
  let E := Equiv.ofBijective lab
    ((Fintype.bijective_iff_injective_and_card lab).mpr ⟨inj,by simp [cardX]⟩)
  have eLast : E (Fin.last n)=v := labLast
  have eCast (i : Fin n) : E i.castSucc=(e i).val := labCast i
  let f (k : Nat) := if hk : k<n then decide (G.Adj (e ⟨k,hk⟩).val v) else false
  obtain ⟨hood, hlow, masked⟩ := encode f n
  have bits (i : Fin n) : hood.testBit i.val=decide (G.Adj (e i).val v) := by
    simpa [f,i.isLt] using masked i.val i.isLt
  have extAdj (i j : Fin (n+1)) :
      G.Adj (E i) (E j) ↔ augment n s.1 hood i.val j.val=true := by
    refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j
    all_goals simp only [eLast,eCast,Fin.val_last,Fin.val_castSucc]
    · simp [augment]
    · rw [aug_last b.isLt,bits,decide_eq_true_eq,G.adj_comm]
    · rw [aug_symm,aug_last a.isLt,bits,decide_eq_true_eq]
    · rw [aug_old a.isLt b.isLt]
      exact old a b
  let guest : Fin n ↪ X := e.toEmbedding.trans (Function.Embedding.subtype _)
  let set := Finset.univ.filter (fun i : Fin n => hood.testBit i.val)
  have mapped : set.map guest = G.neighborFinset v := by
    ext x
    constructor
    · intro hit
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hit
      apply (G.mem_neighborFinset v _).mpr
      exact (of_decide_eq_true ((bits i).symm.trans (Finset.mem_filter.mp hi).2)).symm
    · intro hit
      have hx := (G.mem_neighborFinset v _).mp hit
      let y : ↥({v}ᶜ : Set X) := ⟨x,hx.ne.symm⟩
      refine Finset.mem_map.mpr ⟨e.symm y,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
      · rw [bits,decide_eq_true_eq,e.apply_symm_apply]; exact hx.symm
      · change (e (e.symm y)).val=x; rw [e.apply_symm_apply]
  have deg : G.degree v = weight n hood := by
    rw [←G.card_neighborFinset_eq_degree, ←mapped, Finset.card_map]
    rfl
  have count : G.edgeFinset.card=s.2+weight n hood := by
    rw [G.card_edgeFinset_induce_compl_singleton,G.card_edgeFinset_deleteIncidenceSet] at previous
    have hd := G.degree_le_card_edgeFinset v
    omega
  have augDegree (i : Fin (n+1)) : augmentedDegree n s.1 hood i.val = G.degree (E i) := by
    rw [← G.card_neighborFinset_eq_degree (E i)]
    unfold augmentedDegree
    rw [← Finset.card_map E.toEmbedding]
    congr 1
    ext x
    constructor
    · intro h
      obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp h
      exact (G.mem_neighborFinset _ _).2 ((extAdj i j).2 (Finset.mem_filter.mp hj).2)
    · intro h
      refine Finset.mem_map.mpr ⟨E.symm x, Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
      · apply (extAdj i _).1
        simpa using (G.mem_neighborFinset _ _).1 h
      · exact E.apply_symm_apply _
  have mind (j : Fin n) : weight n hood ≤ augmentedDegree n s.1 hood j.val := by
    rw [←deg,show augmentedDegree n s.1 hood j.val = G.degree (E j.castSucc) from augDegree j.castSucc]
    exact minimal _
  obtain ⟨ws,zs,hws,hzs,hcover⟩ := records
  rcases hcover ⟨hood,hlow⟩ (count ▸ bound) (count ▸ upper) mind with ⟨w,hw,inc⟩ | ⟨z,hz,he⟩
  · left
    obtain ⟨inject,good⟩ := hws w hw
    refine ⟨w.2.1,(⟨fun i : Fin (order w.2.1) => label n w.2.2 i.val,inject⟩ : Fin (order w.2.1) ↪ Fin (n+1)).trans E.toEmbedding,?_⟩
    intro i j hij
    exact (extAdj _ _).2 (augment_mono inc (good i j hij))
  · right
    obtain ⟨member,inject,good⟩ := hzs z hz
    have eqhood : z.1=hood := he
    rw [eqhood] at member good
    let p := Equiv.ofBijective (fun i : Fin (n+1) => label n z.2.2 i.val) inject.bijective_of_finite
    refine ⟨(z.2.1,s.2+weight n hood),member,count,p.trans E,?_⟩
    intro i j
    change G.Adj (E (p i)) (E (p j)) ↔ pair z.2.1 i.val j.val=true
    rw [extAdj,good i j]
    rfl
end Astra1182.Ten

/- Delete a vertex of minimum degree, classify the induced graph, and reattach the vertex. -/
namespace Astra1182.Ten
open SimpleGraph

theorem classify (stages : Nat → List Shape) (base : (0,0)∈stages 1)
    (rows : ∀ n : Fin 10, 0<n.val → ∀ s∈stages n.val, row n.val s (stages (n.val+1))) :
    ∀ k < 10, ∀ (X : Type) [Fintype X] [DecidableEq X] (G : SimpleGraph X) [DecidableRel G.Adj],
      Fintype.card X=k+1 → threshold (k+1) ≤ G.edgeFinset.card → G.edgeFinset.card≤ 27 →
      Classified G (k+1) (stages (k+1)) := by
  classical
  intro k
  induction k with
  | zero =>
    intro _ X _ _ G _ hc _ _
    let e := (Fintype.equivFinOfCardEq hc).symm
    have size := G.card_edgeFinset_le_card_choose_two
    rw [hc] at size
    refine Or.inr ⟨(0,0),base,by exact Nat.eq_zero_of_le_zero size,e,?_⟩
    intro i j
    have he : i=j := Fin.ext (by omega)
    subst j
    simp [pair]
  | succ k ih =>
    intro hk X _ _ G _ hc lower upper
    have : Nonempty X := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨v,smallest⟩ := G.exists_minimal_degree_vertex
    have degSum : (k+2)*G.degree v ≤ 2*G.edgeFinset.card := calc
      _ = ∑ _ : X, G.degree v := by simp [hc]
      _ ≤ ∑ i, G.degree i := Finset.sum_le_sum fun i _ => by rw [←smallest]; exact G.minDegree_le_degree i
      _ = _ := G.sum_degrees_eq_twice_card_edges
    let n : Fin 10 := ⟨k+1,by omega⟩
    let m : Fin 28 := ⟨G.edgeFinset.card,by omega⟩
    let d : Fin 28 := ⟨G.degree v, lt_of_le_of_lt (G.degree_le_card_edgeFinset v) m.isLt⟩
    have residual := dropBound n m d lower degSum
    have count := (G.card_edgeFinset_induce_compl_singleton v).trans (G.card_edgeFinset_deleteIncidenceSet v)
    have c : Fintype.card ↥({v}ᶜ : Set X) = k+1 := calc
      _ = Fintype.card X - Fintype.card ↥({v} : Set X) := Fintype.card_compl_set _
      _ = k+1 := by simp [hc]
    have ord : threshold (k+1) ≤ (G.induce {v}ᶜ).edgeFinset.card := by rw [count]; exact residual
    have up : (G.induce {v}ᶜ).edgeFinset.card ≤ 27 := by rw [count]; omega
    rcases ih (by omega) _ (G.induce {v}ᶜ) c ord up with ⟨kind,e,he⟩ | ⟨s,hs,sz,rep⟩
    · exact Or.inl ⟨kind,e.trans (Function.Embedding.subtype _),he⟩
    · exact extendStage G v (fun x => smallest ▸ G.minDegree_le_degree x) hc s _ lower upper sz rep (rows n (by dsimp [n]; omega) s hs)
end Astra1182.Ten

/- Certificates for all one-vertex extensions needed by the density induction. -/
namespace Astra1182.Ten
def stages : Nat → List Shape
  | 1 => [(0,0)]
  | 2 => [(1,1)]
  | 3 => [(515,3)]
  | 4 => [(1543,5), (132615,6)]
  | 5 => [(3599,7), (263695,7), (17040903,7), (17040911,8), (132623,7), (134671,8), (396815,9), (17174031,10)]
  | 6 => [(1107824143,10), (1107559967,10), (1107564047,10), (1124861447,10), (17045023,10), (17569295,10), (17569311,11), (51119631,10), (51119647,11), (51123727,11), (1124865551,12), (138783,10), (658975,10), (34213391,10), (1073876511,10), (1073880607,11), (1074400783,10), (1107955215,11), (396831,10), (400927,11), (925215,12), (33951247,10), (33951263,11), (33955359,12), (1107693071,11), (1107693087,12), (1107697183,13), (17174031,10), (17174047,11), (17178143,12), (17702431,13), (51256863,14), (1124998687,15)]
  | 7 => [(37683203599,14), (37682943503,14), (18626111,14), (84686399,14), (85726783,14), (85734943,14), (2232161855,14), (2232170015,14), (34377315903,14), (34378364447,14), (34444416575,14), (34444424735,14), (34445465119,14), (36591900191,14), (36591900223,15), (36591908383,15), (119277119,14), (119285279,14), (2198611519,14), (2199660063,14), (36558349855,14), (36558349887,15), (36559398431,15), (2199664143,14), (2266764815,14), (36558345775,14), (36559394319,14), (36626503183,15), (1124873775,14), (1125922351,15), (1193022991,14), (1193023023,15), (1193031215,16), (3340514831,16), (1074937407,14), (1142038079,14), (3289521695,14), (37649260063,15), (1109012015,14), (3323596303,14), (37615177263,14), (36574731807,14), (933439,14), (1982015,15), (68034111,14), (68042303,15), (2215517727,14), (2215517759,15), (36575256095,15), (36575256127,16), (36541173311,14), (36541181471,14), (36608282143,14), (33963583,14), (35003967,14), (102112799,14), (102112831,15), (2181439039,14), (2181447231,15), (2182487583,14), (2182487615,15), (2248547871,14), (2248547903,15), (2249596447,15), (36541177375,14), (36541177407,15), (36541185599,16), (36542225951,15), (36542225983,16), (36609334815,16), (37682023951,14), (1107701311,14), (1108749855,14), (1174801983,14), (1174810143,14), (3322285599,14), (3322285631,15), (3322293791,15), (35467431487,14), (35467439647,14), (35467439679,15), (35468488223,15), (35534540319,14), (35534540351,15), (35534548511,15), (37682023967,15), (37682023999,16), (1107697215,14), (1107705407,15), (1108745759,14), (1108745791,15), (1108753983,16), (1175854623,15), (1175854655,16), (1175862847,17), (3322289695,15), (3322289727,16), (3322297919,17), (3323338271,16), (3323338303,17), (37683076639,17), (37683076671,18), (17186367,14), (18226751,14), (85335583,14), (34376916543,14), (34376924735,15), (34377965087,14), (34377965119,15), (34445073951,15), (17702463,14), (17710655,15), (18759231,16), (84811295,14), (84811327,15), (84819519,16), (2232294943,15), (2232294975,16), (34377440799,14), (34377440831,15), (34377449023,16), (34378497599,17), (34444549663,15), (34444549695,16), (36592033311,16), (36592033343,17), (51256863,14), (51256895,15), (51265087,16), (52313663,17), (119422527,18), (2198740511,15), (2198740543,16), (2198748735,17), (2199797311,18), (36558478879,16), (36558478911,17), (36558487103,18), (36559535679,19), (1124998687,15), (1124998719,16), (1125006911,17), (1126055487,18), (1193164351,19), (3340647999,20), (37700386367,21)]
  | 8 => [(620707468927,18), (657282840095,18), (657216779807,18), (105313490495,18), (659331749391,18), (659463869967,18), (1128035951,18), (550881752687,18), (550883849839,19), (623912296063,18), (623912312383,18), (587405090399,18), (4095615,18), (136216191,18), (202276479,18), (204357247,18), (238444095,18), (620657778303,18), (109555637823,18), (659311435327,18), (660586499599,18), (7751470719,18), (104388234879,18), (108548984447,18), (37816241791,18), (550863535743,18), (550866656895,18), (551067983391,18), (557507288607,18), (37683076671,18), (34379038335,18), (34513239679,18), (38808206911,18), (103096417919,18), (652852215423,18), (652852231807,19), (103099555391,18), (652853255807,18), (652853272127,18), (18775679,18), (20872831,19), (652852731519,18), (652852747839,18), (34378497663,18), (653054058015,18), (655067323935,18), (51281535,18), (549807079039,18), (549807095423,19), (119422527,18), (6493707903,18), (551954554495,18), (556249521727,18), (556249521791,19), (2199797311,18), (109572922911,18), (590609260063,18), (659328736799,19), (36558487103,18), (36559535679,19), (550880812671,18), (550880828991,18), (1125006975,18), (1125023359,19), (550880820799,18), (550880820863,19), (550880837247,20), (1126055487,18), (1193164351,19), (3340647999,20), (37700386367,21)]
  | 9 => [(6163699349023,22), (6163633288735,22), (4640803182143,22), (5611729999423,22), (6121474629375,22), (6084963262175,22), (660859162255,22), (669444902543,22), (6048421707519,22), (6048428990207,22), (6048898752031,22), (6287849307903,22), (652856459007,22), (653124861695,22), (653124894463,23), (661714796159,22), (661714796287,23), (6287850348287,22), (25100031,22), (1649318756095,22), (6047365234431,22), (1664351084287,22), (6053807660799,22), (6062397595263,22), (1904869252639,22), (6165476810271,22), (6302915763743,23), (5498683162367,22), (6048438959871,22), (6048438992511,22), (550880870143,22), (1650392465151,22), (1650392497919,23), (6048438976127,22), (6048438976255,23), (6048439009023,24), (4435746897471,22)]
  | 10 => []
  | _ => []
def cones0 : List CopyRule := []
def cases0 : List IsoRule := [(1, 1, 16)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert0 : row 1 (0,0) (stages 2) := by
  refine ⟨cones0,cases0,?_,?_,?_⟩ <;> decide +kernel
def cones1 : List CopyRule := []
def cases1 : List IsoRule := [(3, 515, 528)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert1 : row 2 (1,1) (stages 3) := by
  refine ⟨cones1,cases1,?_,?_,?_⟩ <;> decide +kernel
def cones2 : List CopyRule := []
def cases2 : List IsoRule := [(3, 1543, 12816), (5, 1543, 12576), (6, 1543, 12321), (7, 132615, 12816)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert2 : row 3 (515,3) (stages 4) := by
  refine ⟨cones2,cases2,?_,?_,?_⟩ <;> decide +kernel
def cones3 : List CopyRule := []
def cases3 : List IsoRule := [(3, 3599, 274960), (5, 263695, 274960), (6, 263695, 274945), (9, 263695, 271120), (10, 263695, 271105), (12, 17040903, 274960), (13, 17040911, 274960), (14, 17040911, 274945)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert3 : row 4 (1543,5) (stages 5) := by
  refine ⟨cones3,cases3,?_,?_,?_⟩ <;> decide +kernel
def cones4 : List CopyRule := []
def cases4 : List IsoRule := [(1, 132623, 274960), (2, 132623, 274945), (3, 134671, 274960), (4, 132623, 274690), (5, 134671, 274720), (6, 134671, 274465), (7, 396815, 274960), (8, 132623, 270595), (9, 134671, 270640), (10, 134671, 270385), (11, 396815, 271120), (12, 134671, 266290), (13, 396815, 267040), (14, 396815, 262945), (15, 17174031, 274960)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert4 : row 4 (132615,6) (stages 5) := by
  refine ⟨cones4,cases4,?_,?_,?_⟩ <;> decide +kernel
def cones5 : List CopyRule := []
def cases5 : List IsoRule := [(28, 1107824143, 5517840)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert5 : row 5 (3599,7) (stages 6) := by
  refine ⟨cones5,cases5,?_,?_,?_⟩ <;> decide +kernel
def cones6 : List CopyRule := []
def cases6 : List IsoRule := [(25, 1107559967, 5517840), (26, 1107564047, 5517840), (28, 1107564047, 5456160)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert6 : row 5 (263695,7) (stages 6) := by
  refine ⟨cones6,cases6,?_,?_,?_⟩ <;> decide +kernel
def cones7 : List CopyRule := []
def cases7 : List IsoRule := [(19, 1107824143, 4534800), (21, 1107564047, 4411680), (22, 1107564047, 4411425), (25, 1107564047, 4346160), (26, 1107564047, 4345905), (28, 1124861447, 5517840)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert7 : row 5 (17040903,7) (stages 6) := by
  refine ⟨cones7,cases7,?_,?_,?_⟩ <;> decide +kernel
def cones8 : List CopyRule := []
def cases8 : List IsoRule := [(3, 17045023, 5517840), (5, 17045023, 5456160), (6, 17569295, 5517840), (7, 17569311, 5517840), (9, 17045023, 5390640), (10, 17569295, 5514000), (11, 17569311, 5514000), (12, 51119631, 5517840), (13, 51119647, 5517840), (14, 51123727, 5517840), (17, 17045023, 5321280), (18, 51119631, 5456160), (19, 51119647, 5456160), (20, 17569295, 5444640), (21, 17569311, 5444640), (22, 51123727, 5456160), (24, 17569295, 5379120), (25, 17569311, 5379120), (26, 51123727, 5390640), (28, 51123727, 5321280), (30, 1124865551, 5517840)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert8 : row 5 (17040911,8) (stages 6) := by
  refine ⟨cones8,cases8,?_,?_,?_⟩ <;> decide +kernel
def cones9 : List CopyRule := []
def cases9 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert9 : row 5 (132623,7) (stages 6) := by
  refine ⟨cones9,cases9,?_,?_,?_⟩ <;> decide +kernel
def cones10 : List CopyRule := []
def cases10 : List IsoRule := [(3, 138783, 5517840), (5, 658975, 5517840), (6, 658975, 5517825), (9, 658975, 5514000), (10, 658975, 5513985), (12, 34213391, 5517840), (17, 1073876511, 5517840), (18, 1073876511, 5517825), (19, 1073880607, 5517840), (20, 1074400783, 5517840), (21, 17569311, 3490320), (22, 17569311, 3490305), (24, 1074400783, 5514000), (25, 17569311, 2442000), (26, 17569311, 2441985), (28, 1107955215, 5517840)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert10 : row 5 (134671,8) (stages 6) := by
  refine ⟨cones10,cases10,?_,?_,?_⟩ <;> decide +kernel
def cones11 : List CopyRule := []
def cases11 : List IsoRule := [(1, 396831, 5517840), (2, 396831, 5517825), (3, 400927, 5517840), (4, 396831, 5517570), (5, 400927, 5517600), (6, 400927, 5517345), (7, 925215, 5517840), (8, 33951247, 5517840), (9, 33951263, 5517840), (10, 33951263, 5517825), (11, 33955359, 5517840), (12, 33951263, 5517570), (13, 33955359, 5517600), (14, 33955359, 5517345), (16, 33951247, 5456400), (17, 33951263, 5456400), (18, 33951263, 5456385), (19, 33955359, 5456400), (20, 33951263, 5456130), (21, 33955359, 5456160), (22, 33955359, 5455905), (24, 1107693071, 5517840), (25, 1107693087, 5517840), (26, 1107693087, 5517825), (27, 1107697183, 5517840), (28, 1107693087, 5517570), (29, 1107697183, 5517600), (30, 1107697183, 5517345)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert11 : row 5 (396815,9) (stages 6) := by
  refine ⟨cones11,cases11,?_,?_,?_⟩ <;> decide +kernel
def cones12 : List CopyRule := []
def cases12 : List IsoRule := [(0, 17174031, 5517840), (1, 17174047, 5517840), (2, 17174047, 5517825), (3, 17178143, 5517840), (4, 17174047, 5517570), (5, 17178143, 5517600), (6, 17178143, 5517345), (7, 17702431, 5517840), (8, 17174047, 5513475), (9, 17178143, 5513520), (10, 17178143, 5513265), (11, 17702431, 5514000), (12, 17178143, 5509170), (13, 17702431, 5509920), (14, 17702431, 5505825), (15, 51256863, 5517840), (16, 17174047, 5447940), (17, 17178143, 5448000), (18, 17178143, 5447745), (19, 17702431, 5448720), (20, 17178143, 5443650), (21, 17702431, 5444640), (22, 17702431, 5440545), (23, 51256863, 5456400), (24, 17178143, 5378115), (25, 17702431, 5379120), (26, 17702431, 5375025), (27, 51256863, 5391120), (28, 17702431, 5309490), (29, 51256863, 5325600), (30, 51256863, 5260065), (31, 1124998687, 5517840)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert12 : row 5 (17174031,10) (stages 6) := by
  refine ⟨cones12,cases12,?_,?_,?_⟩ <;> decide +kernel
def cones13 : List CopyRule := []
def cases13 : List IsoRule := [(60, 37683203599, 106181136)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert13 : row 6 (1107824143,10) (stages 7) := by
  refine ⟨cones13,cases13,?_,?_,?_⟩ <;> decide +kernel
def cones14 : List CopyRule := []
def cases14 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert14 : row 6 (1107559967,10) (stages 7) := by
  refine ⟨cones14,cases14,?_,?_,?_⟩ <;> decide +kernel
def cones15 : List CopyRule := []
def cases15 : List IsoRule := [(60, 37682943503, 106181136)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert15 : row 6 (1107564047,10) (stages 7) := by
  refine ⟨cones15,cases15,?_,?_,?_⟩ <;> decide +kernel
def cones16 : List CopyRule := []
def cases16 : List IsoRule := [(51, 37683203599, 88486416)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert16 : row 6 (1124861447,10) (stages 7) := by
  refine ⟨cones16,cases16,?_,?_,?_⟩ <;> decide +kernel
def cones17 : List CopyRule := []
def cases17 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert17 : row 6 (17045023,10) (stages 7) := by
  refine ⟨cones17,cases17,?_,?_,?_⟩ <;> decide +kernel
def cones18 : List CopyRule := []
def cases18 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert18 : row 6 (17569295,10) (stages 7) := by
  refine ⟨cones18,cases18,?_,?_,?_⟩ <;> decide +kernel
def cones19 : List CopyRule := []
def cases19 : List IsoRule := [(7, 18626111, 106181136), (11, 84686399, 106181136), (13, 85726783, 106181136), (14, 85734943, 106181136), (19, 85726783, 106119456), (21, 84686399, 106119456), (22, 85734943, 106119456), (25, 2232161855, 106181136), (26, 2232170015, 106181136), (28, 2232170015, 106119456), (35, 34377315903, 106181136), (37, 34377315903, 106119456), (38, 34378364447, 106181136), (41, 34444416575, 106181136), (42, 34444424735, 106181136), (44, 34445465119, 106181136), (49, 34444416575, 106119456), (50, 34445465119, 106119456), (52, 34444424735, 106119456), (56, 36591900191, 106181136), (57, 36591900223, 106181136), (58, 36591908383, 106181136), (60, 36591908383, 106119456)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert19 : row 6 (17569311,11) (stages 7) := by
  refine ⟨cones19,cases19,?_,?_,?_⟩ <;> decide +kernel
def cones20 : List CopyRule := []
def cases20 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert20 : row 6 (51119631,10) (stages 7) := by
  refine ⟨cones20,cases20,?_,?_,?_⟩ <;> decide +kernel
def cones21 : List CopyRule := []
def cases21 : List IsoRule := [(7, 85726783, 90452496), (11, 85726783, 90448656), (13, 119277119, 106181136), (14, 119285279, 106181136), (19, 2198611519, 106181136), (21, 85726783, 90255936), (22, 2199660063, 106181136), (25, 85726783, 90252096), (26, 2199660063, 106177296), (28, 119285279, 105984576), (35, 2198611519, 105198096), (37, 85726783, 73478736), (38, 2199660063, 105198096), (41, 85726783, 73474896), (42, 2199660063, 105194256), (44, 119285279, 104936016), (49, 2198611519, 23286816), (50, 36558349855, 106181136), (51, 36558349887, 106181136), (52, 2199660063, 102052416), (54, 36559398431, 106181136), (56, 2199660063, 102048576), (58, 36559398431, 106177296)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert21 : row 6 (51119647,11) (stages 7) := by
  refine ⟨cones21,cases21,?_,?_,?_⟩ <;> decide +kernel
def cones22 : List CopyRule := []
def cases22 : List IsoRule := [(7, 85734943, 90452496), (11, 85734943, 90448656), (13, 119285279, 90452496), (14, 119285279, 73740801), (19, 2199660063, 90390816), (21, 2232170015, 90379296), (22, 2199664143, 106181136), (25, 2232170015, 90313776), (26, 2199664143, 106177296), (28, 2266764815, 106181136), (35, 2199660063, 73617441), (37, 2199664143, 105198081), (38, 2232170015, 73598241), (41, 2199664143, 105194241), (42, 2232170015, 73532721), (44, 2266764815, 105198081), (49, 36558345775, 106181136), (50, 36558345775, 105198081), (51, 36559398431, 90390816), (52, 36559394319, 106181136), (53, 36591908383, 90379296), (54, 36591908383, 73598241), (56, 36559394319, 106177296), (57, 36591908383, 90313776), (58, 36591908383, 73532721), (60, 36626503183, 106181136)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert22 : row 6 (51123727,11) (stages 7) := by
  refine ⟨cones22,cases22,?_,?_,?_⟩ <;> decide +kernel
def cones23 : List CopyRule := []
def cases23 : List IsoRule := [(3, 1124873775, 106181136), (5, 1124873775, 106119456), (6, 1124873775, 105074721), (7, 1125922351, 106181136), (9, 1124873775, 106053936), (10, 1124873775, 105009201), (11, 1125922351, 106177296), (12, 1193022991, 106181136), (13, 1193023023, 106181136), (14, 1193023023, 105198081), (15, 1193031215, 106181136), (17, 1124873775, 105984576), (18, 1193022991, 106119456), (19, 1193023023, 106119456), (20, 1124873775, 103895106), (21, 1125922351, 106107936), (22, 1193023023, 104153346), (23, 1193031215, 106119456), (24, 1124873775, 102846531), (25, 1125922351, 106042416), (26, 1193023023, 103104771), (27, 1193031215, 106053936), (28, 1193023023, 102052356), (29, 1193031215, 105984576), (30, 3340514831, 106181136), (33, 1193022991, 105074721), (34, 1124873775, 104870481), (35, 1193023023, 105074721), (36, 1124873775, 103825746), (37, 1193023023, 104091666), (38, 1125922351, 105055521), (39, 1193031215, 105074721), (40, 1124873775, 102777171), (41, 1193023023, 103043091), (42, 1125922351, 104990001), (43, 1193031215, 105009201), (44, 1193023023, 100938261), (45, 3340514831, 105198081), (46, 1193031215, 104870481), (48, 1124873775, 101724756), (49, 1193023023, 101928996), (50, 1193023023, 100876581), (51, 3340514831, 104153346), (52, 1125922351, 103875906), (53, 1193031215, 103895106), (54, 1193031215, 103825746), (56, 1125922351, 102827331), (57, 1193031215, 102846531), (58, 1193031215, 102777171), (60, 1193031215, 101724756)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert23 : row 6 (1124865551,12) (stages 7) := by
  refine ⟨cones23,cases23,?_,?_,?_⟩ <;> decide +kernel
def cones24 : List CopyRule := []
def cases24 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert24 : row 6 (138783,10) (stages 7) := by
  refine ⟨cones24,cases24,?_,?_,?_⟩ <;> decide +kernel
def cones25 : List CopyRule := []
def cases25 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert25 : row 6 (658975,10) (stages 7) := by
  refine ⟨cones25,cases25,?_,?_,?_⟩ <;> decide +kernel
def cones26 : List CopyRule := []
def cases26 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert26 : row 6 (34213391,10) (stages 7) := by
  refine ⟨cones26,cases26,?_,?_,?_⟩ <;> decide +kernel
def cones27 : List CopyRule := []
def cases27 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert27 : row 6 (1073876511,10) (stages 7) := by
  refine ⟨cones27,cases27,?_,?_,?_⟩ <;> decide +kernel
def cones28 : List CopyRule := []
def cases28 : List IsoRule := [(7, 1074937407, 106181136), (11, 1074937407, 106177296), (13, 1142038079, 106181136), (14, 1142038079, 106181121), (19, 1074937407, 103961616), (21, 84686399, 87441936), (22, 84686399, 87441921), (25, 84686399, 86393616), (26, 84686399, 86393601), (28, 3289521695, 106181136), (35, 1074937407, 103957776), (37, 84686399, 70668816), (38, 84686399, 70668801), (41, 84686399, 69620496), (42, 84686399, 69620481), (44, 3289521695, 105198096), (49, 1142038079, 103961616), (50, 1142038079, 103961601), (52, 3289521695, 103961616), (56, 3289521695, 102978576), (60, 37649260063, 106181136)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert28 : row 6 (1073880607,11) (stages 7) := by
  refine ⟨cones28,cases28,?_,?_,?_⟩ <;> decide +kernel
def cones29 : List CopyRule := []
def cases29 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert29 : row 6 (1074400783,10) (stages 7) := by
  refine ⟨cones29,cases29,?_,?_,?_⟩ <;> decide +kernel
def cones30 : List CopyRule := []
def cases30 : List IsoRule := [(7, 1109012015, 106181136), (11, 1109012015, 106177296), (13, 1109012015, 105189426), (14, 1109012015, 105185586), (19, 3289521695, 90452496), (21, 34445465119, 87441936), (22, 34445465119, 87441921), (25, 34445465119, 86393616), (26, 34445465119, 86393601), (28, 3323596303, 106181136), (35, 3323596303, 105189426), (37, 34445465119, 68571186), (38, 34445465119, 67522866), (41, 34445465119, 68571171), (42, 34445465119, 67522851), (44, 3289521695, 73732146), (49, 37615177263, 106181136), (50, 37615177263, 106181121), (51, 37649260063, 90452496), (52, 37615177263, 105189426), (53, 36591908383, 87318816), (54, 36591908383, 87318561), (56, 37615177263, 105189411), (57, 36591908383, 86270256), (58, 36591908383, 86270001), (60, 37649260063, 73732146)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert30 : row 6 (1107955215,11) (stages 7) := by
  refine ⟨cones30,cases30,?_,?_,?_⟩ <;> decide +kernel
def cones31 : List CopyRule := []
def cases31 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert31 : row 6 (396831,10) (stages 7) := by
  refine ⟨cones31,cases31,?_,?_,?_⟩ <;> decide +kernel
def cones32 : List CopyRule := []
def cases32 : List IsoRule := [(35, 1074937407, 73740816), (37, 18626111, 70668816), (38, 18626111, 70668801), (41, 34377315903, 69620496), (42, 34377315903, 69620481), (44, 1109012015, 73740816), (49, 34377315903, 52843536), (50, 34377315903, 52843521), (52, 1109012015, 56967696), (56, 36574731807, 106181136)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert32 : row 6 (400927,11) (stages 7) := by
  refine ⟨cones32,cases32,?_,?_,?_⟩ <;> decide +kernel
def cones33 : List CopyRule := []
def cases33 : List IsoRule := [(3, 933439, 106181136), (5, 933439, 106180896), (6, 933439, 106180641), (7, 1982015, 106181136), (9, 68034111, 106181136), (10, 68034111, 106181121), (11, 68042303, 106181136), (12, 68034111, 106180866), (13, 68042303, 106180896), (14, 68042303, 106180641), (17, 68034111, 106119696), (18, 68034111, 106119681), (19, 68042303, 106119696), (20, 68034111, 106119426), (21, 68042303, 106119456), (22, 68042303, 106119201), (24, 2215517727, 106181136), (25, 2215517759, 106181136), (26, 2215517759, 106181121), (28, 2215517759, 106180866), (33, 68034111, 105075216), (34, 68034111, 105075201), (35, 68042303, 105075216), (36, 68034111, 105074946), (37, 68042303, 105074976), (38, 68042303, 105074721), (40, 2215517727, 105198096), (41, 2215517759, 105198096), (42, 2215517759, 105198081), (44, 2215517759, 105197826), (48, 2215517727, 104153616), (49, 2215517759, 104153616), (50, 2215517759, 104153601), (52, 2215517759, 104153346), (56, 36575256095, 106181136), (57, 36575256127, 106181136), (58, 36575256127, 106181121), (60, 36575256127, 106180866)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert33 : row 6 (925215,12) (stages 7) := by
  refine ⟨cones33,cases33,?_,?_,?_⟩ <;> decide +kernel
def cones34 : List CopyRule := []
def cases34 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert34 : row 6 (33951247,10) (stages 7) := by
  refine ⟨cones34,cases34,?_,?_,?_⟩ <;> decide +kernel
def cones35 : List CopyRule := []
def cases35 : List IsoRule := [(35, 34377315903, 69559056), (37, 34377315903, 68510496), (38, 1109012015, 72757281), (41, 1142038079, 73736496), (42, 34378364447, 69619971), (44, 34378364447, 68571651), (49, 36541173311, 106181136), (50, 36541181471, 106181136), (52, 36541181471, 106180896), (56, 36608282143, 106181136)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert35 : row 6 (33951263,11) (stages 7) := by
  refine ⟨cones35,cases35,?_,?_,?_⟩ <;> decide +kernel
def cones36 : List CopyRule := []
def cases36 : List IsoRule := [(3, 33963583, 106181136), (5, 35003967, 106181136), (6, 35003967, 106181121), (7, 68042303, 90452496), (9, 35003967, 105194256), (10, 35003967, 105194241), (11, 68042303, 73736976), (12, 102112799, 106181136), (13, 102112831, 106181136), (14, 102112831, 106181121), (17, 2181439039, 106181136), (18, 2181439039, 106181121), (19, 2181447231, 106181136), (20, 2182487583, 106181136), (21, 2182487615, 106181136), (22, 2182487615, 106181121), (24, 2248547871, 106181136), (25, 2248547903, 106181136), (26, 2248547903, 106181121), (28, 2249596447, 106181136), (33, 2181439039, 105194256), (34, 2181439039, 105194241), (35, 2181447231, 105194256), (36, 2248547871, 105194256), (37, 2248547903, 105194256), (38, 2248547903, 105194241), (40, 2182487583, 105194256), (41, 2182487615, 105194256), (42, 2182487615, 105194241), (44, 2249596447, 105194256), (48, 36541177375, 106181136), (49, 36541177407, 106181136), (50, 36541177407, 106181121), (51, 36541185599, 106181136), (52, 36542225951, 106181136), (53, 36542225983, 106181136), (54, 36542225983, 106181121), (56, 36542225951, 105194256), (57, 36542225983, 105194256), (58, 36542225983, 105194241), (60, 36609334815, 106181136)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert36 : row 6 (33955359,12) (stages 7) := by
  refine ⟨cones36,cases36,?_,?_,?_⟩ <;> decide +kernel
def cones37 : List CopyRule := []
def cases37 : List IsoRule := [(35, 36574731807, 90452496), (37, 36574731807, 90452256), (38, 36574731807, 90452001), (41, 36608282143, 90452496), (42, 36608282143, 90452481), (44, 36608282143, 90452226), (49, 36608282143, 90391056), (50, 36608282143, 90391041), (52, 36608282143, 90390786), (56, 37682023951, 106181136)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert37 : row 6 (1107693071,11) (stages 7) := by
  refine ⟨cones37,cases37,?_,?_,?_⟩ <;> decide +kernel
def cones38 : List CopyRule := []
def cases38 : List IsoRule := [(3, 1107701311, 106181136), (5, 1107701311, 106180896), (6, 1108749855, 106181136), (7, 2215517759, 90452496), (9, 1174801983, 106181136), (10, 1174810143, 106181136), (11, 2248547903, 90452496), (12, 1174810143, 106180896), (13, 2248547903, 90452256), (14, 2249596447, 90452001), (17, 1174801983, 106119696), (18, 1174810143, 106119696), (19, 2248547903, 90391056), (20, 1174810143, 106119456), (21, 2248547903, 90390816), (22, 2249596447, 90390561), (24, 3322285599, 106181136), (25, 3322285631, 106181136), (26, 3322293791, 106181136), (28, 3322293791, 106180896), (33, 35467431487, 106181136), (34, 35467439647, 106181136), (35, 35467439679, 106181136), (36, 35467439647, 106180896), (37, 35467439679, 106180896), (38, 35468488223, 106181136), (39, 36575256127, 90452496), (40, 35534540319, 106181136), (41, 35534540351, 106181136), (42, 35534548511, 106181136), (43, 36542225983, 88482576), (44, 35534548511, 106180896), (45, 36542225983, 88478496), (46, 36609334815, 90452001), (48, 35534540319, 106119696), (49, 35534540351, 106119696), (50, 35534548511, 106119696), (51, 36542225983, 87434256), (52, 35534548511, 106119456), (53, 36542225983, 87430176), (54, 36609334815, 90390561), (56, 37682023967, 106181136), (57, 37682023999, 106181136), (58, 1193031215, 40190736), (60, 1193031215, 23413536)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert38 : row 6 (1107693087,12) (stages 7) := by
  refine ⟨cones38,cases38,?_,?_,?_⟩ <;> decide +kernel
def cones39 : List CopyRule := []
def cases39 : List IsoRule := [(1, 1107697215, 106181136), (2, 1107697215, 106181121), (3, 1107705407, 106181136), (4, 1108745759, 106181136), (5, 1108745791, 106181136), (6, 1108745791, 106181121), (7, 1108753983, 106181136), (8, 1108745759, 105194256), (9, 1108745791, 105194256), (10, 1108745791, 105194241), (11, 1108753983, 105194256), (12, 1175854623, 106181136), (13, 1175854655, 106181136), (14, 1175854655, 106181121), (15, 1175862847, 106181136), (16, 1108745759, 104145936), (17, 1108745791, 104145936), (18, 1108745791, 104145921), (19, 1108753983, 104145936), (20, 1175854623, 106119696), (21, 1175854655, 106119696), (22, 1175854655, 106119681), (23, 1175862847, 106119696), (24, 3322289695, 106181136), (25, 3322289727, 106181136), (26, 3322289727, 106181121), (27, 3322297919, 106181136), (28, 3323338271, 106181136), (29, 3323338303, 106181136), (30, 3323338303, 106181121), (32, 1108745759, 103036176), (33, 1108745791, 103036176), (34, 1108745791, 103036161), (35, 1108753983, 103036176), (36, 3322289695, 105194256), (37, 3322289727, 105194256), (38, 3322289727, 105194241), (39, 3322297919, 105194256), (40, 1175854623, 105009936), (41, 1175854655, 105009936), (42, 1175854655, 105009921), (43, 1175862847, 105009936), (44, 3323338271, 105194256), (45, 3323338303, 105194256), (46, 3323338303, 105194241), (48, 1175854623, 103961616), (49, 1175854655, 103961616), (50, 1175854655, 103961601), (51, 1175862847, 103961616), (52, 3323338271, 104145936), (53, 3323338303, 104145936), (54, 3323338303, 104145921), (56, 3323338271, 103036176), (57, 3323338303, 103036176), (58, 3323338303, 103036161), (60, 37683076639, 106181136), (61, 37683076671, 106181136), (62, 37683076671, 106181121)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert39 : row 6 (1107697183,13) (stages 7) := by
  refine ⟨cones39,cases39,?_,?_,?_⟩ <;> decide +kernel
def cones40 : List CopyRule := []
def cases40 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert40 : row 6 (17174031,10) (stages 7) := by
  refine ⟨cones40,cases40,?_,?_,?_⟩ <;> decide +kernel
def cones41 : List CopyRule := []
def cases41 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert41 : row 6 (17174047,11) (stages 7) := by
  refine ⟨cones41,cases41,?_,?_,?_⟩ <;> decide +kernel
def cones42 : List CopyRule := []
def cases42 : List IsoRule := [(3, 17186367, 106181136), (5, 18226751, 106181136), (6, 18226751, 106181121), (9, 18226751, 106177296), (10, 18226751, 106177281), (12, 85335583, 106181136), (17, 18226751, 106112016), (18, 18226751, 106112001), (20, 85335583, 106119696), (24, 85335583, 106054416), (33, 34376916543, 106181136), (34, 34376916543, 106181121), (35, 34376924735, 106181136), (36, 34377965087, 106181136), (37, 34377965119, 106181136), (38, 34377965119, 106181121), (40, 34377965087, 106177296), (41, 34377965119, 106177296), (42, 34377965119, 106177281), (44, 34445073951, 106181136), (48, 34377965087, 106112016), (49, 34377965119, 106112016), (50, 34377965119, 106112001), (52, 34445073951, 106119696), (56, 34445073951, 106054416)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert42 : row 6 (17178143,12) (stages 7) := by
  refine ⟨cones42,cases42,?_,?_,?_⟩ <;> decide +kernel
def cones43 : List CopyRule := []
def cases43 : List IsoRule := [(1, 17702463, 106181136), (2, 17702463, 106181121), (3, 17710655, 106181136), (4, 17702463, 106180866), (5, 17710655, 106180896), (6, 17710655, 106180641), (7, 18759231, 106181136), (8, 84811295, 106181136), (9, 84811327, 106181136), (10, 84811327, 106181121), (11, 84819519, 106181136), (12, 84811327, 106180866), (13, 84819519, 106180896), (14, 84819519, 106180641), (16, 84811295, 106119696), (17, 84811327, 106119696), (18, 84811327, 106119681), (19, 84819519, 106119696), (20, 84811327, 106119426), (21, 84819519, 106119456), (22, 84819519, 106119201), (24, 2232294943, 106181136), (25, 2232294975, 106181136), (26, 2232294975, 106181121), (28, 2232294975, 106180866), (32, 34377440799, 106181136), (33, 34377440831, 106181136), (34, 34377440831, 106181121), (35, 34377449023, 106181136), (36, 34377440831, 106180866), (37, 34377449023, 106180896), (38, 34377449023, 106180641), (39, 34378497599, 106181136), (40, 34444549663, 106181136), (41, 34444549695, 106181136), (42, 34444549695, 106181121), (43, 1175862847, 73740816), (44, 34444549695, 106180866), (45, 1175862847, 73740576), (46, 1175862847, 73740321), (48, 34444549663, 106119696), (49, 34444549695, 106119696), (50, 34444549695, 106119681), (51, 1175862847, 56967696), (52, 34444549695, 106119426), (53, 1175862847, 56967456), (54, 1175862847, 56967201), (56, 36592033311, 106181136), (57, 36592033343, 106181136), (58, 36592033343, 106181121), (60, 36592033343, 106180866)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert43 : row 6 (17702431,13) (stages 7) := by
  refine ⟨cones43,cases43,?_,?_,?_⟩ <;> decide +kernel
def cones44 : List CopyRule := []
def cases44 : List IsoRule := [(0, 51256863, 106181136), (1, 51256895, 106181136), (2, 51256895, 106181121), (3, 51265087, 106181136), (4, 51256895, 106180866), (5, 51265087, 106180896), (6, 51265087, 106180641), (7, 52313663, 106181136), (8, 51256895, 106176771), (9, 51265087, 106176816), (10, 51265087, 106176561), (11, 52313663, 106177296), (12, 51265087, 106172466), (13, 52313663, 106173216), (14, 52313663, 106169121), (15, 119422527, 106181136), (16, 2198740511, 106181136), (17, 2198740543, 106181136), (18, 2198740543, 106181121), (19, 2198748735, 106181136), (20, 2198740543, 106180866), (21, 2198748735, 106180896), (22, 2198748735, 106180641), (23, 2199797311, 106181136), (24, 2198740543, 106176771), (25, 2198748735, 106176816), (26, 2198748735, 106176561), (27, 2199797311, 106177296), (28, 2198748735, 106172466), (29, 2199797311, 106173216), (30, 2199797311, 106169121), (32, 2198740511, 105198096), (33, 2198740543, 105198096), (34, 2198740543, 105198081), (35, 2198748735, 105198096), (36, 2198740543, 105197826), (37, 2198748735, 105197856), (38, 2198748735, 105197601), (39, 2199797311, 105198096), (40, 2198740543, 105193731), (41, 2198748735, 105193776), (42, 2198748735, 105193521), (43, 2199797311, 105194256), (44, 2198748735, 105189426), (45, 2199797311, 105190176), (46, 2199797311, 105186081), (48, 36558478879, 106181136), (49, 36558478911, 106181136), (50, 36558478911, 106181121), (51, 36558487103, 106181136), (52, 36558478911, 106180866), (53, 36558487103, 106180896), (54, 36558487103, 106180641), (55, 36559535679, 106181136), (56, 36558478911, 106176771), (57, 36558487103, 106176816), (58, 36558487103, 106176561), (59, 36559535679, 106177296), (60, 36558487103, 106172466), (61, 36559535679, 106173216), (62, 36559535679, 106169121)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert44 : row 6 (51256863,14) (stages 7) := by
  refine ⟨cones44,cases44,?_,?_,?_⟩ <;> decide +kernel
def cones45 : List CopyRule := []
def cases45 : List IsoRule := [(0, 1124998687, 106181136), (1, 1124998719, 106181136), (2, 1124998719, 106181121), (3, 1125006911, 106181136), (4, 1124998719, 106180866), (5, 1125006911, 106180896), (6, 1125006911, 106180641), (7, 1126055487, 106181136), (8, 1124998719, 106176771), (9, 1125006911, 106176816), (10, 1125006911, 106176561), (11, 1126055487, 106177296), (12, 1125006911, 106172466), (13, 1126055487, 106173216), (14, 1126055487, 106169121), (15, 1193164351, 106181136), (16, 1124998719, 106111236), (17, 1125006911, 106111296), (18, 1125006911, 106111041), (19, 1126055487, 106112016), (20, 1125006911, 106106946), (21, 1126055487, 106107936), (22, 1126055487, 106103841), (23, 1193164351, 106119696), (24, 1125006911, 106041411), (25, 1126055487, 106042416), (26, 1126055487, 106038321), (27, 1193164351, 106054416), (28, 1126055487, 105972786), (29, 1193164351, 105988896), (30, 1193164351, 105923361), (31, 3340647999, 106181136), (32, 1124998719, 105062661), (33, 1125006911, 105062736), (34, 1125006911, 105062481), (35, 1126055487, 105063696), (36, 1125006911, 105058386), (37, 1126055487, 105059616), (38, 1126055487, 105055521), (39, 1193164351, 105075216), (40, 1125006911, 104992851), (41, 1126055487, 104994096), (42, 1126055487, 104990001), (43, 1193164351, 105009936), (44, 1126055487, 104924466), (45, 1193164351, 104944416), (46, 1193164351, 104878881), (47, 3340647999, 105198096), (48, 1125006911, 103944276), (49, 1126055487, 103945536), (50, 1126055487, 103941441), (51, 1193164351, 103961616), (52, 1126055487, 103875906), (53, 1193164351, 103896096), (54, 1193164351, 103830561), (55, 3340647999, 104153616), (56, 1126055487, 102827331), (57, 1193164351, 102847536), (58, 1193164351, 102782001), (59, 3340647999, 103105296), (60, 1193164351, 101733426), (61, 3340647999, 102056736), (62, 3340647999, 101008161), (63, 37700386367, 106181136)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert45 : row 6 (1124998687,15) (stages 7) := by
  refine ⟨cones45,cases45,?_,?_,?_⟩ <;> decide +kernel
def cones46 : List CopyRule := [(1,true,1951805698), (2,true,1951805458), (32,true,1946236498), (64,true,1946236258)]
def cases46 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert46 : row 7 (37683203599,14) (stages 8) := by
  refine ⟨cones46,cases46,?_,?_,?_⟩ <;> decide +kernel
def cones47 : List CopyRule := [(12,true,1164390658), (18,true,911688193), (33,true,642208528), (65,true,355951648), (66,true,69690673), (36,true,51861058), (24,true,302466643)]
def cases47 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert47 : row 7 (37682943503,14) (stages 8) := by
  refine ⟨cones47,cases47,?_,?_,?_⟩ <;> decide +kernel
def cones48 : List CopyRule := [(48,true,927343888)]
def cases48 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert48 : row 7 (18626111,14) (stages 8) := by
  refine ⟨cones48,cases48,?_,?_,?_⟩ <;> decide +kernel
def cones49 : List CopyRule := [(96,true,1197675808), (40,true,1194726688)]
def cases49 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert49 : row 7 (84686399,14) (stages 8) := by
  refine ⟨cones49,cases49,?_,?_,?_⟩ <;> decide +kernel
def cones50 : List CopyRule := [(48,true,927343888)]
def cases50 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert50 : row 7 (85726783,14) (stages 8) := by
  refine ⟨cones50,cases50,?_,?_,?_⟩ <;> decide +kernel
def cones51 : List CopyRule := [(65,true,1412915728), (18,true,1446461953), (80,true,1465988098)]
def cases51 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert51 : row 7 (85734943,14) (stages 8) := by
  refine ⟨cones51,cases51,?_,?_,?_⟩ <;> decide +kernel
def cones52 : List CopyRule := [(102,true,879063568), (106,true,610628368), (108,true,1094087968), (114,true,843478288), (116,true,325415968), (120,true,307655728)]
def cases52 : List IsoRule := [(99, 620707468927, 1985229328), (101, 620707468927, 1985167648), (105, 620707468927, 1969361968), (113, 620707468927, 1969300288)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert52 : row 7 (2232161855,14) (stages 8) := by
  refine ⟨cones52,cases52,?_,?_,?_⟩ <;> decide +kernel
def cones53 : List CopyRule := [(68,true,1466122753), (72,true,1466057473), (12,true,1463173633), (50,true,896942593), (99,true,1380147568), (113,true,622028608)]
def cases53 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert53 : row 7 (2232170015,14) (stages 8) := by
  refine ⟨cones53,cases53,?_,?_,?_⟩ <;> decide +kernel
def cones54 : List CopyRule := [(40,true,1194726688), (76,true,1450455298), (90,true,1380151648)]
def cases54 : List IsoRule := [(89, 620707468927, 1733571088)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert54 : row 7 (34377315903,14) (stages 8) := by
  refine ⟨cones54,cases54,?_,?_,?_⟩ <;> decide +kernel
def cones55 : List CopyRule := [(81,true,880108048), (82,true,1450394113), (76,true,1450455298)]
def cases55 : List IsoRule := [(120, 657282840095, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert55 : row 7 (34378364447,14) (stages 8) := by
  refine ⟨cones55,cases55,?_,?_,?_⟩ <;> decide +kernel
def cones56 : List CopyRule := [(3,true,1178015008), (69,true,913581328), (82,true,1450328833), (49,true,880169488), (92,true,354711088), (116,true,325415968), (120,true,307655728)]
def cases56 : List IsoRule := [(89, 620707468927, 1701975088)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert56 : row 7 (34444416575,14) (stages 8) := by
  refine ⟨cones56,cases56,?_,?_,?_⟩ <;> decide +kernel
def cones57 : List CopyRule := [(81,true,611672848), (82,true,1450328833), (76,true,1450455298), (50,true,880169473), (56,true,611733523)]
def cases57 : List IsoRule := [(116, 657216779807, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert57 : row 7 (34444424735,14) (stages 8) := by
  refine ⟨cones57,cases57,?_,?_,?_⟩ <;> decide +kernel
def cones58 : List CopyRule := [(3,true,1178015008), (18,true,1446461953), (65,true,1094149408), (12,true,1164390658), (36,true,1130844418), (80,true,1465988098)]
def cases58 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert58 : row 7 (34445465119,14) (stages 8) := by
  refine ⟨cones58,cases58,?_,?_,?_⟩ <;> decide +kernel
def cones59 : List CopyRule := [(5,true,910632208), (3,true,1178015008), (65,true,307717168), (40,true,610750483), (48,true,325537828), (76,true,1450259458), (82,true,1450328833)]
def cases59 : List IsoRule := [(102, 657282840095, 1733571088)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert59 : row 7 (36591900191,14) (stages 8) := by
  refine ⟨cones59,cases59,?_,?_,?_⟩ <;> decide +kernel
def cones60 : List CopyRule := [(5,true,910632208), (3,true,1178015008), (12,true,1447505938), (18,true,1446461473), (17,true,354895408), (33,true,879186448), (40,true,610750483), (48,true,325537828), (65,true,307717168), (66,true,1113022513), (68,true,827809858)]
def cases60 : List IsoRule := [(38, 105313490495, 1985229328), (88, 105313490495, 1969361968)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert60 : row 7 (36591900223,15) (stages 8) := by
  refine ⟨cones60,cases60,?_,?_,?_⟩ <;> decide +kernel
def cones61 : List CopyRule := [(2,true,1917019408), (8,true,1917149488), (32,true,1917018448), (5,true,910632208), (65,true,843539728), (68,true,1466122753)]
def cases61 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert61 : row 7 (36591908383,15) (stages 8) := by
  refine ⟨cones61,cases61,?_,?_,?_⟩ <;> decide +kernel
def cones62 : List CopyRule := [(18,true,1698120193)]
def cases62 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert62 : row 7 (119277119,14) (stages 8) := by
  refine ⟨cones62,cases62,?_,?_,?_⟩ <;> decide +kernel
def cones63 : List CopyRule := [(48,true,391525378), (18,true,1446461953)]
def cases63 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert63 : row 7 (119285279,14) (stages 8) := by
  refine ⟨cones63,cases63,?_,?_,?_⟩ <;> decide +kernel
def cones64 : List CopyRule := [(12,true,1463173633), (18,true,1698120193), (99,true,1159927648), (101,true,907290448), (102,true,879063568), (105,true,638859088), (106,true,610628368), (113,true,354633568), (116,true,324432928), (120,true,307655728)]
def cases64 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert64 : row 7 (2198611519,14) (stages 8) := by
  refine ⟨cones64,cases64,?_,?_,?_⟩ <;> decide +kernel
def cones65 : List CopyRule := [(68,true,1466122753), (12,true,1463173633), (72,true,1466057473), (97,true,896819728), (98,true,1181962753), (50,true,896942593)]
def cases65 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert65 : row 7 (2199660063,14) (stages 8) := by
  refine ⟨cones65,cases65,?_,?_,?_⟩ <;> decide +kernel
def cones66 : List CopyRule := [(1,true,1966490113), (12,true,1463173633), (18,true,895959553), (68,true,1466122753), (34,true,879186433), (72,true,1466057473)]
def cases66 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert66 : row 7 (36558349855,14) (stages 8) := by
  refine ⟨cones66,cases66,?_,?_,?_⟩ <;> decide +kernel
def cones67 : List CopyRule := [(1,true,1966490113), (4,true,1966489633), (8,true,1965441073), (64,true,1965244513), (18,true,895959553), (34,true,1681347073)]
def cases67 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert67 : row 7 (36558349887,15) (stages 8) := by
  refine ⟨cones67,cases67,?_,?_,?_⟩ <;> decide +kernel
def cones68 : List CopyRule := [(4,true,1933926688), (1,true,1966490113), (8,true,1965441073), (64,true,1963147873), (18,true,895959553), (34,true,879186433)]
def cases68 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert68 : row 7 (36559398431,15) (stages 8) := by
  refine ⟨cones68,cases68,?_,?_,?_⟩ <;> decide +kernel
def cones69 : List CopyRule := [(64,true,1966096993), (33,true,1681347088), (50,true,896942593)]
def cases69 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert69 : row 7 (2199664143,14) (stages 8) := by
  refine ⟨cones69,cases69,?_,?_,?_⟩ <;> decide +kernel
def cones70 : List CopyRule := [(34,true,1196830978), (48,true,391525378), (44,true,1165373698), (101,true,1177638688), (105,true,1176590128)]
def cases70 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert70 : row 7 (2266764815,14) (stages 8) := by
  refine ⟨cones70,cases70,?_,?_,?_⟩ <;> decide +kernel
def cones71 : List CopyRule := [(2,true,1949717008), (1,true,1985033218), (12,true,374813698), (48,true,1733374978)]
def cases71 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert71 : row 7 (36558345775,14) (stages 8) := by
  refine ⟨cones71,cases71,?_,?_,?_⟩ <;> decide +kernel
def cones72 : List CopyRule := [(1,true,1985033218), (2,true,1983919378), (12,true,374813698)]
def cases72 : List IsoRule := [(116, 659331749391, 1985229328), (120, 659463869967, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert72 : row 7 (36559394319,14) (stages 8) := by
  refine ⟨cones72,cases72,?_,?_,?_⟩ <;> decide +kernel
def cones73 : List CopyRule := [(1,true,1969500418), (2,true,1952788498), (12,true,1164390658), (48,true,391525378), (80,true,392508418), (96,true,124007698)]
def cases73 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert73 : row 7 (36626503183,15) (stages 8) := by
  refine ⟨cones73,cases73,?_,?_,?_⟩ <;> decide +kernel
def cones74 : List CopyRule := []
def cases74 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert74 : row 7 (1124873775,14) (stages 8) := by
  refine ⟨cones74,cases74,?_,?_,?_⟩ <;> decide +kernel
def cones75 : List CopyRule := [(8,true,1982091568), (16,true,1980977728), (32,true,1979925073)]
def cases75 : List IsoRule := [(7, 1128035951, 1985229328), (67, 550881752687, 1985229328), (69, 550881752687, 1985167648), (70, 550881752687, 1984122913), (71, 550883849839, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert75 : row 7 (1125922351,15) (stages 8) := by
  refine ⟨cones75,cases75,?_,?_,?_⟩ <;> decide +kernel
def cones76 : List CopyRule := []
def cases76 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert76 : row 7 (1193022991,14) (stages 8) := by
  refine ⟨cones76,cases76,?_,?_,?_⟩ <;> decide +kernel
def cones77 : List CopyRule := [(2,true,1983140368), (1,true,1983201793), (16,true,1982943808), (12,true,1731543553), (36,true,1733509633), (40,true,1733444353)]
def cases77 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert77 : row 7 (1193023023,15) (stages 8) := by
  refine ⟨cones77,cases77,?_,?_,?_⟩ <;> decide +kernel
def cones78 : List CopyRule := [(2,true,1983140368), (16,true,1980977728), (4,true,1983140128), (8,true,1982091568), (32,true,1979925073), (65,true,1412915728)]
def cases78 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert78 : row 7 (1193031215,16) (stages 8) := by
  refine ⟨cones78,cases78,?_,?_,?_⟩ <;> decide +kernel
def cones79 : List CopyRule := [(2,true,1983140368), (4,true,1983140128), (8,true,1982091568), (16,true,1980977728), (33,true,1681347088), (65,true,1412915728), (96,true,123946273)]
def cases79 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert79 : row 7 (3340514831,16) (stages 8) := by
  refine ⟨cones79,cases79,?_,?_,?_⟩ <;> decide +kernel
def cones80 : List CopyRule := [(24,true,1732580128)]
def cases80 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert80 : row 7 (1074937407,14) (stages 8) := by
  refine ⟨cones80,cases80,?_,?_,?_⟩ <;> decide +kernel
def cones81 : List CopyRule := [(20,true,1732579888), (24,true,1732580128)]
def cases81 : List IsoRule := [(113, 623912296063, 1985229328), (114, 623912312383, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert81 : row 7 (1142038079,14) (stages 8) := by
  refine ⟨cones81,cases81,?_,?_,?_⟩ <;> decide +kernel
def cones82 : List CopyRule := [(32,true,1982010448), (4,true,1984238368), (24,true,1732580128)]
def cases82 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert82 : row 7 (3289521695,14) (stages 8) := by
  refine ⟨cones82,cases82,?_,?_,?_⟩ <;> decide +kernel
def cones83 : List CopyRule := [(4,true,1984238368), (8,true,1984238128), (16,true,1982010688), (32,true,1982010448)]
def cases83 : List IsoRule := [(67, 587405090399, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert83 : row 7 (37649260063,15) (stages 8) := by
  refine ⟨cones83,cases83,?_,?_,?_⟩ <;> decide +kernel
def cones84 : List CopyRule := [(4,true,1967526688), (33,true,1632064288), (80,true,1464014368), (24,true,1464210208)]
def cases84 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert84 : row 7 (1109012015,14) (stages 8) := by
  refine ⟨cones84,cases84,?_,?_,?_⟩ <;> decide +kernel
def cones85 : List CopyRule := [(3,true,1699156768), (33,true,1632064288), (34,true,1615287073), (108,true,1677800818), (116,true,1661027698), (120,true,1644250483)]
def cases85 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert85 : row 7 (3323596303,14) (stages 8) := by
  refine ⟨cones85,cases85,?_,?_,?_⟩ <;> decide +kernel
def cones86 : List CopyRule := [(4,true,1900434208), (64,true,1898140768), (24,true,390484768)]
def cases86 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert86 : row 7 (37615177263,14) (stages 8) := by
  refine ⟨cones86,cases86,?_,?_,?_⟩ <;> decide +kernel
def cones87 : List CopyRule := [(4,true,1984238368), (1,true,1969373443), (66,true,1466056963), (24,true,627523843)]
def cases87 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert87 : row 7 (36574731807,14) (stages 8) := by
  refine ⟨cones87,cases87,?_,?_,?_⟩ <;> decide +kernel
def cones88 : List CopyRule := []
def cases88 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert88 : row 7 (933439,14) (stages 8) := by
  refine ⟨cones88,cases88,?_,?_,?_⟩ <;> decide +kernel
def cones89 : List CopyRule := [(24,true,1732584208), (40,true,1733567248), (48,true,1733501968), (72,true,1466180368), (80,true,1466115088), (96,true,1197679888)]
def cases89 : List IsoRule := [(7, 4095615, 1985229328), (11, 136216191, 1985229328), (13, 136216191, 1985229088), (14, 136216191, 1985228833), (19, 136216191, 1985167888), (21, 136216191, 1985167648), (22, 136216191, 1985167393), (35, 136216191, 1984123408), (37, 136216191, 1984123168), (38, 136216191, 1984122913), (67, 136216191, 1967350288), (69, 136216191, 1967350048), (70, 136216191, 1967349793)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert89 : row 7 (1982015,15) (stages 8) := by
  refine ⟨cones89,cases89,?_,?_,?_⟩ <;> decide +kernel
def cones90 : List CopyRule := []
def cases90 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert90 : row 7 (68034111,14) (stages 8) := by
  refine ⟨cones90,cases90,?_,?_,?_⟩ <;> decide +kernel
def cones91 : List CopyRule := [(64,true,1917129568), (18,true,1732583728), (24,true,1732584208), (34,true,1733566768), (40,true,1733567248), (48,true,1733501968), (21,true,1685397808), (37,true,1702109488)]
def cases91 : List IsoRule := [(7, 136216191, 1733571088), (11, 202276479, 1985229328), (13, 204357247, 1985229328), (14, 204357247, 1985229313)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert91 : row 7 (68042303,15) (stages 8) := by
  refine ⟨cones91,cases91,?_,?_,?_⟩ <;> decide +kernel
def cones92 : List CopyRule := []
def cases92 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert92 : row 7 (2215517727,14) (stages 8) := by
  refine ⟨cones92,cases92,?_,?_,?_⟩ <;> decide +kernel
def cones93 : List CopyRule := [(2,true,1984242448), (4,true,1984238368), (1,true,1984242433), (24,true,1732584193), (40,true,1733567233), (48,true,1733501953)]
def cases93 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert93 : row 7 (2215517759,15) (stages 8) := by
  refine ⟨cones93,cases93,?_,?_,?_⟩ <;> decide +kernel
def cones94 : List CopyRule := [(2,true,1984242448), (1,true,1984242433), (4,true,1984238368), (24,true,627523843), (40,true,610750723), (48,true,593973508)]
def cases94 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert94 : row 7 (36575256095,15) (stages 8) := by
  refine ⟨cones94,cases94,?_,?_,?_⟩ <;> decide +kernel
def cones95 : List CopyRule := [(2,true,1984242448), (4,true,1984238368), (1,true,1984242433), (8,true,1984241713), (16,true,1983193153), (32,true,1983127633)]
def cases95 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert95 : row 7 (36575256127,16) (stages 8) := by
  refine ⟨cones95,cases95,?_,?_,?_⟩ <;> decide +kernel
def cones96 : List CopyRule := [(102,true,1129738768), (106,true,610627888), (108,true,342192688), (114,true,592867648), (116,true,324432448)]
def cases96 : List IsoRule := [(99, 620707468927, 1176859408), (101, 620707468927, 1175810848), (105, 623912296063, 1685397808), (113, 623912296063, 1400250688), (120, 659331749391, 558067813)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert96 : row 7 (36541173311,14) (stages 8) := by
  refine ⟨cones96,cases96,?_,?_,?_⟩ <;> decide +kernel
def cones97 : List CopyRule := [(65,true,592929088), (9,true,1180119328), (34,true,610750513), (18,true,895959073), (37,true,1702109968), (88,true,1450328323)]
def cases97 : List IsoRule := [(108, 657282840095, 1679249923), (116, 657282840095, 1392992788)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert97 : row 7 (36541181471,14) (stages 8) := by
  refine ⟨cones97,cases97,?_,?_,?_⟩ <;> decide +kernel
def cones98 : List CopyRule := [(66,true,1466056963), (68,true,1465991683), (6,true,1447502593), (24,true,627523603)]
def cases98 : List IsoRule := [(105, 623912312383, 1685397808), (113, 659331749391, 558063733)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert98 : row 7 (36608282143,14) (stages 8) := by
  refine ⟨cones98,cases98,?_,?_,?_⟩ <;> decide +kernel
def cones99 : List CopyRule := []
def cases99 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert99 : row 7 (33963583,14) (stages 8) := by
  refine ⟨cones99,cases99,?_,?_,?_⟩ <;> decide +kernel
def cones100 : List CopyRule := []
def cases100 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert100 : row 7 (35003967,14) (stages 8) := by
  refine ⟨cones100,cases100,?_,?_,?_⟩ <;> decide +kernel
def cones101 : List CopyRule := []
def cases101 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert101 : row 7 (102112799,14) (stages 8) := by
  refine ⟨cones101,cases101,?_,?_,?_⟩ <;> decide +kernel
def cones102 : List CopyRule := [(18,true,1464213808), (24,true,1464214288), (34,true,1196831008), (36,true,1196831248), (48,true,1733497888), (66,true,1197814048), (68,true,1197814288), (72,true,1466180368), (80,true,1466115088), (96,true,1197618448), (21,true,1417027888), (41,true,1165373728)]
def cases102 : List IsoRule := [(7, 204357247, 1702113808), (11, 204357247, 1685398288), (13, 204357247, 1417024288), (14, 238444095, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert102 : row 7 (102112831,15) (stages 8) := by
  refine ⟨cones102,cases102,?_,?_,?_⟩ <;> decide +kernel
def cones103 : List CopyRule := []
def cases103 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert103 : row 7 (2181439039,14) (stages 8) := by
  refine ⟨cones103,cases103,?_,?_,?_⟩ <;> decide +kernel
def cones104 : List CopyRule := [(8,true,1952780848), (5,true,1447502128), (3,true,1416041008), (20,true,1464209968), (36,true,1733497408), (48,true,928388128), (68,true,1466176048), (80,true,929371168), (96,true,660870448)]
def cases104 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert104 : row 7 (2181447231,15) (stages 8) := by
  refine ⟨cones104,cases104,?_,?_,?_⟩ <;> decide +kernel
def cones105 : List CopyRule := []
def cases105 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert105 : row 7 (2182487583,14) (stages 8) := by
  refine ⟨cones105,cases105,?_,?_,?_⟩ <;> decide +kernel
def cones106 : List CopyRule := [(8,true,1984238128), (5,true,1416044848), (18,true,1464213808), (36,true,1733497408), (48,true,1733497888), (66,true,1466179888), (80,true,1466115088), (35,true,1702105888)]
def cases106 : List IsoRule := [(97, 620657778303, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert106 : row 7 (2182487615,15) (stages 8) := by
  refine ⟨cones106,cases106,?_,?_,?_⟩ <;> decide +kernel
def cones107 : List CopyRule := []
def cases107 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert107 : row 7 (2248547871,14) (stages 8) := by
  refine ⟨cones107,cases107,?_,?_,?_⟩ <;> decide +kernel
def cones108 : List CopyRule := [(2,true,1952789008), (4,true,1952788768), (9,true,1416049168), (17,true,1399276048), (48,true,1732384048), (96,true,1197618448), (88,true,1450328083)]
def cases108 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert108 : row 7 (2248547903,15) (stages 8) := by
  refine ⟨cones108,cases108,?_,?_,?_⟩ <;> decide +kernel
def cones109 : List CopyRule := [(8,true,1984238128), (4,true,1984238368), (16,true,1983189568), (32,true,1982075728), (65,true,1363632688)]
def cases109 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert109 : row 7 (2249596447,15) (stages 8) := by
  refine ⟨cones109,cases109,?_,?_,?_⟩ <;> decide +kernel
def cones110 : List CopyRule := []
def cases110 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert110 : row 7 (36541177375,14) (stages 8) := by
  refine ⟨cones110,cases110,?_,?_,?_⟩ <;> decide +kernel
def cones111 : List CopyRule := [(4,true,1985156128), (8,true,1984042288), (3,true,911676448), (17,true,895959328), (33,true,610750768), (66,true,592928833)]
def cases111 : List IsoRule := [(50, 109555637823, 1985229328), (112, 659311435327, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert111 : row 7 (36541177407,15) (stages 8) := by
  refine ⟨cones111,cases111,?_,?_,?_⟩ <;> decide +kernel
def cones112 : List CopyRule := [(4,true,1969492768), (8,true,1952780848), (16,true,1935020608), (32,true,1917195088), (64,true,1916081248), (3,true,1164383008)]
def cases112 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert112 : row 7 (36541185599,16) (stages 8) := by
  refine ⟨cones112,cases112,?_,?_,?_⟩ <;> decide +kernel
def cones113 : List CopyRule := [(4,true,1985156128), (8,true,1984238128), (16,true,1985155648), (3,true,911676448), (65,true,827810848), (66,true,811033633)]
def cases113 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert113 : row 7 (36542225951,15) (stages 8) := by
  refine ⟨cones113,cases113,?_,?_,?_⟩ <;> decide +kernel
def cones114 : List CopyRule := [(2,true,1969496848), (4,true,1985156128), (32,true,1931763793), (9,true,1180119568), (17,true,895959328), (24,true,1464214288), (65,true,827810848), (72,true,1466180368), (80,true,1466115088)]
def cases114 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert114 : row 7 (36542225983,16) (stages 8) := by
  refine ⟨cones114,cases114,?_,?_,?_⟩ <;> decide +kernel
def cones115 : List CopyRule := [(4,true,1984238368), (8,true,1984238128), (16,true,1983189568), (32,true,1982075728), (3,true,1180111648), (65,true,1096246048), (66,true,1079468833)]
def cases115 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert115 : row 7 (36609334815,16) (stages 8) := by
  refine ⟨cones115,cases115,?_,?_,?_⟩ <;> decide +kernel
def cones116 : List CopyRule := [(34,true,659964163), (36,true,391528963), (33,true,659963923)]
def cases116 : List IsoRule := [(120, 660586499599, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert116 : row 7 (37682023951,14) (stages 8) := by
  refine ⟨cones116,cases116,?_,?_,?_⟩ <;> decide +kernel
def cones117 : List CopyRule := []
def cases117 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert117 : row 7 (1107701311,14) (stages 8) := by
  refine ⟨cones117,cases117,?_,?_,?_⟩ <;> decide +kernel
def cones118 : List CopyRule := []
def cases118 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert118 : row 7 (1108749855,14) (stages 8) := by
  refine ⟨cones118,cases118,?_,?_,?_⟩ <;> decide +kernel
def cones119 : List CopyRule := []
def cases119 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert119 : row 7 (1174801983,14) (stages 8) := by
  refine ⟨cones119,cases119,?_,?_,?_⟩ <;> decide +kernel
def cones120 : List CopyRule := []
def cases120 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert120 : row 7 (1174810143,14) (stages 8) := by
  refine ⟨cones120,cases120,?_,?_,?_⟩ <;> decide +kernel
def cones121 : List CopyRule := []
def cases121 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert121 : row 7 (3322285599,14) (stages 8) := by
  refine ⟨cones121,cases121,?_,?_,?_⟩ <;> decide +kernel
def cones122 : List CopyRule := [(2,true,1951805968), (4,true,1951805728), (33,true,659963923), (65,true,660946963), (96,true,660686083), (56,true,628506643), (88,true,645218323)]
def cases122 : List IsoRule := [(25, 7751470719, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert122 : row 7 (3322285631,15) (stages 8) := by
  refine ⟨cones122,cases122,?_,?_,?_⟩ <;> decide +kernel
def cones123 : List CopyRule := [(5,true,1699160848), (9,true,1683436048), (10,true,1416049153), (17,true,1666662928), (18,true,1399276033), (34,true,642208513), (6,true,1447502593), (36,true,373773058), (24,true,1365721603), (65,true,625435408), (68,true,88564498), (96,true,660686083)]
def cases123 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert123 : row 7 (3322293791,15) (stages 8) := by
  refine ⟨cones123,cases123,?_,?_,?_⟩ <;> decide +kernel
def cones124 : List CopyRule := []
def cases124 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert124 : row 7 (35467431487,14) (stages 8) := by
  refine ⟨cones124,cases124,?_,?_,?_⟩ <;> decide +kernel
def cones125 : List CopyRule := []
def cases125 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert125 : row 7 (35467439647,14) (stages 8) := by
  refine ⟨cones125,cases125,?_,?_,?_⟩ <;> decide +kernel
def cones126 : List CopyRule := [(4,true,1967526688), (1,true,1917211393), (24,true,658920193), (34,true,1648841473), (72,true,660886273), (80,true,660820993)]
def cases126 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert126 : row 7 (35467439679,15) (stages 8) := by
  refine ⟨cones126,cases126,?_,?_,?_⟩ <;> decide +kernel
def cones127 : List CopyRule := [(8,true,1967530033), (16,true,1966481473), (5,true,1699160848), (6,true,1164387073), (3,true,1699156768), (34,true,1114067713), (65,true,1129800208), (36,true,1097290498)]
def cases127 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert127 : row 7 (35468488223,15) (stages 8) := by
  refine ⟨cones127,cases127,?_,?_,?_⟩ <;> decide +kernel
def cones128 : List CopyRule := []
def cases128 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert128 : row 7 (35534540319,14) (stages 8) := by
  refine ⟨cones128,cases128,?_,?_,?_⟩ <;> decide +kernel
def cones129 : List CopyRule := [(2,true,1951805968), (4,true,1951805728), (64,true,1947350368), (24,true,643252243)]
def cases129 : List IsoRule := [(41, 104388234879, 1985229328), (49, 108548984447, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert129 : row 7 (35534540351,15) (stages 8) := by
  refine ⟨cones129,cases129,?_,?_,?_⟩ <;> decide +kernel
def cones130 : List CopyRule := [(1,true,1917211393), (8,true,1917210673), (16,true,1916162113), (64,true,1912886113), (6,true,1699160113), (34,true,1648840753)]
def cases130 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert130 : row 7 (35534548511,15) (stages 8) := by
  refine ⟨cones130,cases130,?_,?_,?_⟩ <;> decide +kernel
def cones131 : List CopyRule := [(2,true,1969373203), (4,true,1969307683), (24,true,627523603), (33,true,659963923), (65,true,660946963), (96,true,660686083)]
def cases131 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert131 : row 7 (37682023967,15) (stages 8) := by
  refine ⟨cones131,cases131,?_,?_,?_⟩ <;> decide +kernel
def cones132 : List CopyRule := [(2,true,1951805968), (4,true,1951805728), (32,true,1947350608), (64,true,1947350368), (24,true,643252243)]
def cases132 : List IsoRule := [(9, 37816241791, 1985229328), (17, 37816241791, 1985167888)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert132 : row 7 (37682023999,16) (stages 8) := by
  refine ⟨cones132,cases132,?_,?_,?_⟩ <;> decide +kernel
def cones133 : List CopyRule := []
def cases133 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert133 : row 7 (1107697215,14) (stages 8) := by
  refine ⟨cones133,cases133,?_,?_,?_⟩ <;> decide +kernel
def cones134 : List CopyRule := [(4,true,1967526688), (9,true,1683436048), (72,true,1197806368), (17,true,1666662928), (80,true,929371168), (33,true,1648841488), (96,true,660870448), (40,true,1196823328), (48,true,928388128)]
def cases134 : List IsoRule := [(67, 550863535743, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert134 : row 7 (1107705407,15) (stages 8) := by
  refine ⟨cones134,cases134,?_,?_,?_⟩ <;> decide +kernel
def cones135 : List CopyRule := []
def cases135 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert135 : row 7 (1108745759,14) (stages 8) := by
  refine ⟨cones135,cases135,?_,?_,?_⟩ <;> decide +kernel
def cones136 : List CopyRule := [(2,true,1967530768), (72,true,1466180368), (80,true,1466115088), (24,true,1464214288), (33,true,1733378083), (36,true,1632064258)]
def cases136 : List IsoRule := [(69, 550866656895, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert136 : row 7 (1108745791,15) (stages 8) := by
  refine ⟨cones136,cases136,?_,?_,?_⟩ <;> decide +kernel
def cones137 : List CopyRule := [(2,true,1967530768), (4,true,1967526688), (64,true,1966350688), (9,true,1683436048), (17,true,1666662928), (24,true,1464214288), (33,true,1648841488), (40,true,1733563168), (48,true,1733497888)]
def cases137 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert137 : row 7 (1108753983,16) (stages 8) := by
  refine ⟨cones137,cases137,?_,?_,?_⟩ <;> decide +kernel
def cones138 : List CopyRule := [(16,true,1983189568), (32,true,1982075728), (3,true,1699156768), (69,true,1450451728), (70,true,1450451713), (73,true,1182085648), (74,true,1182085633)]
def cases138 : List IsoRule := [(76, 551067983391, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert138 : row 7 (1175854623,15) (stages 8) := by
  refine ⟨cones138,cases138,?_,?_,?_⟩ <;> decide +kernel
def cones139 : List CopyRule := [(2,true,1951805968), (4,true,1951805728), (64,true,1947546208), (9,true,1683435808), (17,true,1666662688), (24,true,1464214288), (33,true,1648841008), (40,true,1733563168), (48,true,1733497888)]
def cases139 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert139 : row 7 (1175854655,16) (stages 8) := by
  refine ⟨cones139,cases139,?_,?_,?_⟩ <;> decide +kernel
def cones140 : List CopyRule := [(1,true,1951805953), (2,true,1951805968), (4,true,1951805728), (8,true,1967530288), (16,true,1966481728), (32,true,1948660048), (64,true,1966350688)]
def cases140 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert140 : row 7 (1175862847,17) (stages 8) := by
  refine ⟨cones140,cases140,?_,?_,?_⟩ <;> decide +kernel
def cones141 : List CopyRule := [(4,true,1984238368), (1,true,1983992578), (2,true,1983927058), (32,true,1984041808)]
def cases141 : List IsoRule := [(88, 557507288607, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert141 : row 7 (3322289695,15) (stages 8) := by
  refine ⟨cones141,cases141,?_,?_,?_⟩ <;> decide +kernel
def cones142 : List CopyRule := [(2,true,1951805968), (4,true,1951805728), (1,true,1983992578), (8,true,1983991858), (16,true,1982943298), (96,true,1197618448)]
def cases142 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert142 : row 7 (3322289727,16) (stages 8) := by
  refine ⟨cones142,cases142,?_,?_,?_⟩ <;> decide +kernel
def cones143 : List CopyRule := [(1,true,1951805953), (2,true,1951805968), (4,true,1951805728), (8,true,1951797808), (16,true,1935020608), (32,true,1948660048), (64,true,1948594528)]
def cases143 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert143 : row 7 (3322297919,17) (stages 8) := by
  refine ⟨cones143,cases143,?_,?_,?_⟩ <;> decide +kernel
def cones144 : List CopyRule := [(4,true,1984238368), (8,true,1984238128), (16,true,1983189568), (32,true,1982075728), (3,true,1699156768), (65,true,356999968), (66,true,88564513)]
def cases144 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert144 : row 7 (3323338271,16) (stages 8) := by
  refine ⟨cones144,cases144,?_,?_,?_⟩ <;> decide +kernel
def cones145 : List CopyRule := [(1,true,1967284993), (2,true,1951805968), (4,true,1951805728), (8,true,1967530288), (16,true,1966481728), (32,true,1948660048), (64,true,1947546208)]
def cases145 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert145 : row 7 (3323338303,17) (stages 8) := by
  refine ⟨cones145,cases145,?_,?_,?_⟩ <;> decide +kernel
def cones146 : List CopyRule := [(1,true,1935954178), (2,true,1935953938), (4,true,1984238368), (8,true,1984238128), (16,true,1983189568), (32,true,1982075728), (64,true,1880380258)]
def cases146 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert146 : row 7 (37683076639,17) (stages 8) := by
  refine ⟨cones146,cases146,?_,?_,?_⟩ <;> decide +kernel
def cones147 : List CopyRule := [(1,true,1934909953), (2,true,1951805968), (4,true,1951805728), (8,true,1967530288), (16,true,1966481728), (32,true,1948660048), (64,true,1947546208)]
def cases147 : List IsoRule := [(0, 37683076671, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert147 : row 7 (37683076671,18) (stages 8) := by
  refine ⟨cones147,cases147,?_,?_,?_⟩ <;> decide +kernel
def cones148 : List CopyRule := []
def cases148 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert148 : row 7 (17186367,14) (stages 8) := by
  refine ⟨cones148,cases148,?_,?_,?_⟩ <;> decide +kernel
def cones149 : List CopyRule := []
def cases149 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert149 : row 7 (18226751,14) (stages 8) := by
  refine ⟨cones149,cases149,?_,?_,?_⟩ <;> decide +kernel
def cones150 : List CopyRule := []
def cases150 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert150 : row 7 (85335583,14) (stages 8) := by
  refine ⟨cones150,cases150,?_,?_,?_⟩ <;> decide +kernel
def cones151 : List CopyRule := []
def cases151 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert151 : row 7 (34376916543,14) (stages 8) := by
  refine ⟨cones151,cases151,?_,?_,?_⟩ <;> decide +kernel
def cones152 : List CopyRule := [(36,true,1196823088), (40,true,1196823328), (48,true,928388128), (68,true,1197806128), (72,true,1197806368), (80,true,929371168)]
def cases152 : List IsoRule := [(7, 34379038335, 1985229328), (11, 34379038335, 1985225488), (13, 34513239679, 1985229328), (14, 34513239679, 1985229313), (19, 34379038335, 1985160208), (21, 34513239679, 1985167888), (22, 34513239679, 1985167873), (25, 34513239679, 1985102608), (26, 34513239679, 1985102593), (28, 38808206911, 1985229328), (35, 103096417919, 1985229328), (67, 103096417919, 1969500688), (97, 652852215423, 1985229328), (98, 652852215423, 1985229313), (99, 652852231807, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert152 : row 7 (34376924735,15) (stages 8) := by
  refine ⟨cones152,cases152,?_,?_,?_⟩ <;> decide +kernel
def cones153 : List CopyRule := []
def cases153 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert153 : row 7 (34377965087,14) (stages 8) := by
  refine ⟨cones153,cases153,?_,?_,?_⟩ <;> decide +kernel
def cones154 : List CopyRule := [(8,true,1969496368), (16,true,1969430848), (5,true,1164386608), (3,true,1180111408)]
def cases154 : List IsoRule := [(38, 103099555391, 1985229328), (70, 103099555391, 1969500448), (97, 652853255807, 1985229328), (98, 652853272127, 1985229328), (100, 652853272127, 1969500448), (102, 550883849839, 1131827728)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert154 : row 7 (34377965119,15) (stages 8) := by
  refine ⟨cones154,cases154,?_,?_,?_⟩ <;> decide +kernel
def cones155 : List CopyRule := [(4,true,1985221408), (8,true,1985221168), (16,true,1983189568), (3,true,1180111648), (65,true,1096246048), (66,true,1079468833)]
def cases155 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert155 : row 7 (34445073951,15) (stages 8) := by
  refine ⟨cones155,cases155,?_,?_,?_⟩ <;> decide +kernel
def cones156 : List CopyRule := []
def cases156 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert156 : row 7 (17702463,14) (stages 8) := by
  refine ⟨cones156,cases156,?_,?_,?_⟩ <;> decide +kernel
def cones157 : List CopyRule := [(68,true,1197806128), (72,true,1466176288), (80,true,1466111008), (24,true,1732584208), (96,true,1197675808), (40,true,1733567248), (48,true,1733501968)]
def cases157 : List IsoRule := [(67, 34379038335, 1466184208)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert157 : row 7 (17710655,15) (stages 8) := by
  refine ⟨cones157,cases157,?_,?_,?_⟩ <;> decide +kernel
def cones158 : List CopyRule := [(8,true,1918243888), (16,true,1918243648), (32,true,1949704528), (64,true,1949639008)]
def cases158 : List IsoRule := [(3, 18775679, 1985229328), (5, 18775679, 1985229088), (6, 18775679, 1985228833), (7, 20872831, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert158 : row 7 (18759231,16) (stages 8) := by
  refine ⟨cones158,cases158,?_,?_,?_⟩ <;> decide +kernel
def cones159 : List CopyRule := []
def cases159 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert159 : row 7 (84811295,14) (stages 8) := by
  refine ⟨cones159,cases159,?_,?_,?_⟩ <;> decide +kernel
def cones160 : List CopyRule := [(66,true,1466183968), (68,true,1466184208), (80,true,1466053648), (20,true,1464218128), (33,true,1733566513), (40,true,1733567233)]
def cases160 : List IsoRule := [(73, 34513239679, 1466179888)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert160 : row 7 (84811327,15) (stages 8) := by
  refine ⟨cones160,cases160,?_,?_,?_⟩ <;> decide +kernel
def cones161 : List CopyRule := [(4,true,1936004128), (8,true,1918243888), (32,true,1983127888), (64,true,1965306208), (3,true,1399264288), (17,true,1446461728), (18,true,1464217888)]
def cases161 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert161 : row 7 (84819519,16) (stages 8) := by
  refine ⟨cones161,cases161,?_,?_,?_⟩ <;> decide +kernel
def cones162 : List CopyRule := [(2,true,1984242448), (4,true,1984238368), (1,true,1984242433), (40,true,1733432128), (48,true,1733432368)]
def cases162 : List IsoRule := [(88, 38808206911, 1466044483)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert162 : row 7 (2232294943,15) (stages 8) := by
  refine ⟨cones162,cases162,?_,?_,?_⟩ <;> decide +kernel
def cones163 : List CopyRule := [(2,true,1984242448), (8,true,1965441328), (1,true,1984242433), (4,true,1984238368), (32,true,1983127633), (80,true,1466053648)]
def cases163 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert163 : row 7 (2232294975,16) (stages 8) := by
  refine ⟨cones163,cases163,?_,?_,?_⟩ <;> decide +kernel
def cones164 : List CopyRule := []
def cases164 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert164 : row 7 (34377440799,14) (stages 8) := by
  refine ⟨cones164,cases164,?_,?_,?_⟩ <;> decide +kernel
def cones165 : List CopyRule := [(8,true,1985224753), (16,true,1985159233), (67,true,1181947168), (69,true,1181951248), (70,true,1181951233)]
def cases165 : List IsoRule := [(97, 652852731519, 1985229328), (98, 652852747839, 1985229328), (100, 652852747839, 1985229088)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert165 : row 7 (34377440831,15) (stages 8) := by
  refine ⟨cones165,cases165,?_,?_,?_⟩ <;> decide +kernel
def cones166 : List CopyRule := [(8,true,1985225008), (16,true,1985159488), (32,true,1933972048), (64,true,1916015968), (3,true,1164382768), (5,true,1180115248), (6,true,1180114993)]
def cases166 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert166 : row 7 (34377449023,16) (stages 8) := by
  refine ⟨cones166,cases166,?_,?_,?_⟩ <;> decide +kernel
def cones167 : List CopyRule := [(8,true,1985225008), (16,true,1985159488), (32,true,1949704528), (64,true,1949639008), (3,true,1180111408), (5,true,1180115248), (6,true,1180114993)]
def cases167 : List IsoRule := [(1, 34378497663, 1985229328), (2, 34378497663, 1985229313), (4, 34378497663, 1985229058)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert167 : row 7 (34378497599,17) (stages 8) := by
  refine ⟨cones167,cases167,?_,?_,?_⟩ <;> decide +kernel
def cones168 : List CopyRule := [(2,true,1985225488), (1,true,1985225473), (4,true,1985221408), (16,true,1985090368)]
def cases168 : List IsoRule := [(104, 653054058015, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert168 : row 7 (34444549663,15) (stages 8) := by
  refine ⟨cones168,cases168,?_,?_,?_⟩ <;> decide +kernel
def cones169 : List CopyRule := [(2,true,1969500688), (4,true,1969500448), (16,true,1965437248), (1,true,1985225473), (8,true,1985224753), (32,true,1983127633)]
def cases169 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert169 : row 7 (34444549695,16) (stages 8) := by
  refine ⟨cones169,cases169,?_,?_,?_⟩ <;> decide +kernel
def cones170 : List CopyRule := [(2,true,1984242448), (8,true,1985029168), (4,true,1984238368), (1,true,1984242433), (16,true,1985090368)]
def cases170 : List IsoRule := [(96, 655067323935, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert170 : row 7 (36592033311,16) (stages 8) := by
  refine ⟨cones170,cases170,?_,?_,?_⟩ <;> decide +kernel
def cones171 : List CopyRule := [(1,true,1984242433), (2,true,1969500688), (4,true,1969500448), (8,true,1965441328), (16,true,1965437248), (32,true,1983127633), (64,true,1964130403)]
def cases171 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert171 : row 7 (36592033343,17) (stages 8) := by
  refine ⟨cones171,cases171,?_,?_,?_⟩ <;> decide +kernel
def cones172 : List CopyRule := []
def cases172 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert172 : row 7 (51256863,14) (stages 8) := by
  refine ⟨cones172,cases172,?_,?_,?_⟩ <;> decide +kernel
def cones173 : List CopyRule := []
def cases173 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert173 : row 7 (51256895,15) (stages 8) := by
  refine ⟨cones173,cases173,?_,?_,?_⟩ <;> decide +kernel
def cones174 : List CopyRule := [(4,true,1935021088), (8,true,1918243888), (16,true,1966477888), (32,true,1949700688)]
def cases174 : List IsoRule := [(3, 51281535, 1985229328), (65, 549807079039, 1985229328), (66, 549807079039, 1985229313), (67, 549807095423, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert174 : row 7 (51265087,16) (stages 8) := by
  refine ⟨cones174,cases174,?_,?_,?_⟩ <;> decide +kernel
def cones175 : List CopyRule := [(1,true,1935025153), (2,true,1935025168), (4,true,1935021088), (8,true,1918243888), (16,true,1966481728), (32,true,1949704528), (64,true,1966350688)]
def cases175 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert175 : row 7 (52313663,17) (stages 8) := by
  refine ⟨cones175,cases175,?_,?_,?_⟩ <;> decide +kernel
def cones176 : List CopyRule := [(1,true,1935025153), (2,true,1935025168), (4,true,1935021088), (8,true,1918243888), (16,true,1983193408), (32,true,1983127888), (64,true,1966350688)]
def cases176 : List IsoRule := [(0, 119422527, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert176 : row 7 (119422527,18) (stages 8) := by
  refine ⟨cones176,cases176,?_,?_,?_⟩ <;> decide +kernel
def cones177 : List CopyRule := []
def cases177 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert177 : row 7 (2198740511,15) (stages 8) := by
  refine ⟨cones177,cases177,?_,?_,?_⟩ <;> decide +kernel
def cones178 : List CopyRule := [(2,true,1966490128), (4,true,1966489888), (8,true,1965441328), (32,true,1984110673)]
def cases178 : List IsoRule := [(17, 6493707903, 1985229328), (65, 551954554495, 1985229328), (80, 556249521727, 1985229328), (81, 556249521791, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert178 : row 7 (2198740543,16) (stages 8) := by
  refine ⟨cones178,cases178,?_,?_,?_⟩ <;> decide +kernel
def cones179 : List CopyRule := [(1,true,1966490113), (2,true,1966490128), (4,true,1984246048), (8,true,1984241968), (16,true,1935020608), (32,true,1984110928), (64,true,1965244768)]
def cases179 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert179 : row 7 (2198748735,17) (stages 8) := by
  refine ⟨cones179,cases179,?_,?_,?_⟩ <;> decide +kernel
def cones180 : List CopyRule := [(1,true,1984246273), (2,true,1984246288), (4,true,1984246048), (8,true,1984241968), (16,true,1966481728), (32,true,1949704528), (64,true,1966350688)]
def cases180 : List IsoRule := [(0, 2199797311, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert180 : row 7 (2199797311,18) (stages 8) := by
  refine ⟨cones180,cases180,?_,?_,?_⟩ <;> decide +kernel
def cones181 : List CopyRule := [(2,true,1985160208), (4,true,1985156128), (1,true,1985160193), (8,true,1985090608)]
def cases181 : List IsoRule := [(48, 109572922911, 1985229328), (80, 590609260063, 1985229328), (96, 590609260063, 1984246288), (112, 659328736799, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert181 : row 7 (36558478879,16) (stages 8) := by
  refine ⟨cones181,cases181,?_,?_,?_⟩ <;> decide +kernel
def cones182 : List CopyRule := [(1,true,1985160193), (2,true,1966490128), (4,true,1966489888), (8,true,1965441328), (16,true,1985159233), (32,true,1984110673), (64,true,1930580068)]
def cases182 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert182 : row 7 (36558478911,17) (stages 8) := by
  refine ⟨cones182,cases182,?_,?_,?_⟩ <;> decide +kernel
def cones183 : List CopyRule := [(1,true,1966490113), (2,true,1966490128), (4,true,1984246048), (8,true,1984241968), (16,true,1985159488), (32,true,1984110928), (64,true,1965244768)]
def cases183 : List IsoRule := [(0, 36558487103, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert183 : row 7 (36558487103,18) (stages 8) := by
  refine ⟨cones183,cases183,?_,?_,?_⟩ <;> decide +kernel
def cones184 : List CopyRule := [(1,true,1984246273), (2,true,1966490128), (4,true,1984246048), (8,true,1984241968), (16,true,1966481728), (32,true,1949704528), (64,true,1966350688)]
def cases184 : List IsoRule := [(0, 36559535679, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert184 : row 7 (36559535679,19) (stages 8) := by
  refine ⟨cones184,cases184,?_,?_,?_⟩ <;> decide +kernel
def cones185 : List CopyRule := []
def cases185 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert185 : row 7 (1124998687,15) (stages 8) := by
  refine ⟨cones185,cases185,?_,?_,?_⟩ <;> decide +kernel
def cones186 : List CopyRule := []
def cases186 : List IsoRule := [(65, 550880812671, 1985229328), (66, 550880828991, 1985229328), (68, 550880828991, 1985229088), (72, 550880828991, 1985225008), (80, 550880828991, 1985159488), (96, 550880828991, 1984110928)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert186 : row 7 (1124998719,16) (stages 8) := by
  refine ⟨cones186,cases186,?_,?_,?_⟩ <;> decide +kernel
def cones187 : List CopyRule := [(4,true,1951798048), (8,true,1967526448), (16,true,1966477888), (32,true,1949700688)]
def cases187 : List IsoRule := [(1, 1125006975, 1985229328), (2, 1125006975, 1985229313), (3, 1125023359, 1985229328), (64, 550880820799, 1985229328), (65, 550880820863, 1985229328), (66, 550880820863, 1985229313), (67, 550880837247, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert187 : row 7 (1125006911,17) (stages 8) := by
  refine ⟨cones187,cases187,?_,?_,?_⟩ <;> decide +kernel
def cones188 : List CopyRule := [(1,true,1951802113), (2,true,1951802128), (4,true,1951798048), (8,true,1967530288), (16,true,1966481728), (32,true,1949704528), (64,true,1966350688)]
def cases188 : List IsoRule := [(0, 1126055487, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert188 : row 7 (1126055487,18) (stages 8) := by
  refine ⟨cones188,cases188,?_,?_,?_⟩ <;> decide +kernel
def cones189 : List CopyRule := [(1,true,1967534593), (2,true,1967534608), (4,true,1967534368), (8,true,1967530288), (16,true,1983193408), (32,true,1983127888), (64,true,1966350688)]
def cases189 : List IsoRule := [(0, 1193164351, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert189 : row 7 (1193164351,19) (stages 8) := by
  refine ⟨cones189,cases189,?_,?_,?_⟩ <;> decide +kernel
def cones190 : List CopyRule := [(1,true,1984246273), (2,true,1983140368), (4,true,1984246048), (8,true,1984241968), (16,true,1983193408), (32,true,1983127888), (64,true,1966350688)]
def cases190 : List IsoRule := [(0, 3340647999, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert190 : row 7 (3340647999,20) (stages 8) := by
  refine ⟨cones190,cases190,?_,?_,?_⟩ <;> decide +kernel
def cones191 : List CopyRule := [(1,true,1984246273), (2,true,1983140368), (4,true,1984246048), (8,true,1984241968), (16,true,1983193408), (32,true,1983127888), (64,true,1966350688)]
def cases191 : List IsoRule := [(0, 37700386367, 1985229328)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert191 : row 7 (37700386367,21) (stages 8) := by
  refine ⟨cones191,cases191,?_,?_,?_⟩ <;> decide +kernel
def cones192 : List CopyRule := [(9,true,655898176), (65,true,561537856), (40,true,1211569440), (160,true,1215501600), (49,true,881283600), (133,true,931407120), (145,true,394413616), (131,true,1199772960), (23,true,1412896800), (30,true,1447199504), (39,true,1165170720), (54,true,1933738320), (78,true,1412858384), (86,true,1397129504), (90,true,655590976), (92,true,1898218336), (102,true,879067664), (114,true,843482384), (116,true,325420064), (142,true,1412923920), (150,true,896827920), (154,true,642220816), (156,true,372737056), (198,true,879198736), (202,true,610763536), (204,true,338134576), (210,true,588744256), (212,true,325551136), (216,true,561414976)]
def cases192 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert192 : row 8 (620707468927,18) (stages 9) := by
  refine ⟨cones192,cases192,?_,?_,?_⟩ <;> decide +kernel
def cones193 : List CopyRule := [(5,true,927474960), (3,true,1194857760), (40,true,645419267), (6,true,929572097), (129,true,307786800), (130,true,540570977), (132,true,273184098), (48,true,376984068), (73,true,1132814624), (81,true,881156624), (82,true,1451442689), (76,true,1451503874)]
def cases193 : List IsoRule := [(216, 6163699349023, 36344967696)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert193 : row 8 (657282840095,18) (stages 9) := by
  refine ⟨cones193,cases193,?_,?_,?_⟩ <;> decide +kernel
def cones194 : List CopyRule := [(5,true,927474960), (3,true,1178080544), (34,true,929583617), (65,true,1113088304), (36,true,913854722), (129,true,827880000), (130,true,807957857), (56,true,612782099), (76,true,1451503874), (82,true,1451377409), (140,true,1468085250), (84,true,75589458), (168,true,662722067), (112,true,377509668), (30,true,1464042000)]
def cases194 : List IsoRule := [(216, 6163633288735, 36344967696)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert194 : row 8 (657216779807,18) (stages 9) := by
  refine ⟨cones194,cases194,?_,?_,?_⟩ <;> decide +kernel
def cones195 : List CopyRule := [(5,true,910697744), (33,true,879251984), (137,true,1132818720), (14,true,1669800017), (145,true,881160720), (146,true,1468219905), (140,true,1468281090), (42,true,1132941345), (50,true,1703100929), (52,true,881283090), (168,true,663113987), (193,true,914519312), (70,true,914826497), (194,true,662922497), (196,true,394552578), (176,true,394678788)]
def cases195 : List IsoRule := [(166, 4640803182143, 36344967696), (216, 5611729999423, 36344967696)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert195 : row 8 (105313490495,18) (stages 9) := by
  refine ⟨cones195,cases195,?_,?_,?_⟩ <;> decide +kernel
def cones196 : List CopyRule := [(1,true,2253468674), (2,true,2252354834), (12,true,374879234), (72,true,137844260), (192,true,141776420), (112,true,109270820), (176,true,126047780)]
def cases196 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert196 : row 8 (659331749391,18) (stages 9) := by
  refine ⟨cones196,cases196,?_,?_,?_⟩ <;> decide +kernel
def cones197 : List CopyRule := [(1,true,2253468674), (2,true,2252354834), (12,true,374879234), (48,true,121132580), (192,true,141776420), (72,true,137844260)]
def cases197 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert197 : row 8 (659463869967,18) (stages 9) := by
  refine ⟨cones197,cases197,?_,?_,?_⟩ <;> decide +kernel
def cones198 : List CopyRule := [(192,true,947136016), (12,true,1748259344), (80,true,944186896), (20,true,1749242384), (24,true,1749177104), (33,true,1681412624)]
def cases198 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert198 : row 8 (1128035951,18) (stages 9) := by
  refine ⟨cones198,cases198,?_,?_,?_⟩ <;> decide +kernel
def cones199 : List CopyRule := [(10,true,1748259104), (12,true,1748259344), (18,true,1749242144), (20,true,1749242384), (24,true,1749177104), (33,true,1681412624), (36,true,1750286849), (192,true,1215501856), (72,true,1211569696), (133,true,931407376), (131,true,1199773216), (81,true,881287696)]
def cases199 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert199 : row 8 (550881752687,18) (stages 9) := by
  refine ⟨cones199,cases199,?_,?_,?_⟩ <;> decide +kernel
def cones200 : List CopyRule := [(64,true,2202476896), (128,true,2202411376), (5,true,1934106976), (10,true,1748259104), (12,true,1748259344), (18,true,1749242144), (20,true,1749242384), (24,true,1749177104), (33,true,1681412624), (36,true,1750286849)]
def cases200 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert200 : row 8 (550883849839,19) (stages 9) := by
  refine ⟨cones200,cases200,?_,?_,?_⟩ <;> decide +kernel
def cones201 : List CopyRule := [(12,true,1198010386), (24,true,1749357344), (40,true,1750340384), (48,true,645419028), (20,true,1749357104), (36,true,1750340144), (71,true,1197637651), (75,true,1197703186), (83,true,645220368), (99,true,645158928), (135,true,1197680656), (139,true,1197619216), (147,true,645169173), (163,true,645234708), (195,true,558200928), (198,true,1130856976), (202,true,1114080016), (210,true,628524048), (226,true,611747088)]
def cases201 : List IsoRule := [(197, 6121474629375, 36344967696), (201, 6121474629375, 36344963856), (209, 6121474629375, 36091089936), (225, 6121474629375, 36091086096)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert201 : row 8 (623912296063,18) (stages 9) := by
  refine ⟨cones201,cases201,?_,?_,?_⟩ <;> decide +kernel
def cones202 : List CopyRule := [(12,true,1211589121), (24,true,1749357344), (40,true,1750340384), (48,true,676754448), (80,true,677737488), (96,true,677672208), (129,true,1382576448), (20,true,1749357104), (36,true,1750340144), (132,true,1215521281), (70,true,1116168961), (74,true,1132945921)]
def cases202 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert202 : row 8 (623912312383,18) (stages 9) := by
  refine ⟨cones202,cases202,?_,?_,?_⟩ <;> decide +kernel
def cones203 : List CopyRule := [(4,true,2252673824), (16,true,2250446144), (136,true,1752437536), (160,true,1752307008), (40,true,1750340384)]
def cases203 : List IsoRule := [(195, 6084963262175, 36344967696)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert203 : row 8 (587405090399,18) (stages 9) := by
  refine ⟨cones203,cases203,?_,?_,?_⟩ <;> decide +kernel
def cones204 : List CopyRule := []
def cases204 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert204 : row 8 (4095615,18) (stages 9) := by
  refine ⟨cones204,cases204,?_,?_,?_⟩ <;> decide +kernel
def cones205 : List CopyRule := [(48,true,1750279184)]
def cases205 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert205 : row 8 (136216191,18) (stages 9) := by
  refine ⟨cones205,cases205,?_,?_,?_⟩ <;> decide +kernel
def cones206 : List CopyRule := [(48,true,1750279184)]
def cases206 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert206 : row 8 (202276479,18) (stages 9) := by
  refine ⟨cones206,cases206,?_,?_,?_⟩ <;> decide +kernel
def cones207 : List CopyRule := [(48,true,1750279184)]
def cases207 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert207 : row 8 (204357247,18) (stages 9) := by
  refine ⟨cones207,cases207,?_,?_,?_⟩ <;> decide +kernel
def cones208 : List CopyRule := [(80,true,1482892304)]
def cases208 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert208 : row 8 (238444095,18) (stages 9) := by
  refine ⟨cones208,cases208,?_,?_,?_⟩ <;> decide +kernel
def cones209 : List CopyRule := [(24,true,1480991504), (40,true,1750340384), (48,true,1750275104), (72,true,1482957584), (80,true,1482892304), (66,true,1482957104), (36,true,1750274624), (137,true,1199715600), (145,true,931218976), (35,true,1703154464), (69,true,1451435024), (135,true,1197680656), (142,true,1181975056), (150,true,910656016)]
def cases209 : List IsoRule := [(225, 6121474629375, 18832896336)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert209 : row 8 (620657778303,18) (stages 9) := by
  refine ⟨cones209,cases209,?_,?_,?_⟩ <;> decide +kernel
def cones210 : List CopyRule := [(4,true,2253591584), (8,true,2252477744), (129,true,643331088), (66,true,660104193), (176,true,663113988)]
def cases210 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert210 : row 8 (109555637823,18) (stages 9) := by
  refine ⟨cones210,cases210,?_,?_,?_⟩ <;> decide +kernel
def cones211 : List CopyRule := [(4,true,2253591584), (8,true,2252477744), (17,true,896024864), (130,true,678842628), (3,true,911741984), (66,true,660104193), (33,true,610816304), (176,true,662787588)]
def cases211 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert211 : row 8 (659311435327,18) (stages 9) := by
  refine ⟨cones211,cases211,?_,?_,?_⟩ <;> decide +kernel
def cones212 : List CopyRule := [(34,true,676741379), (36,true,408306179), (66,true,677724419), (68,true,409289219), (33,true,676741139), (130,true,678772995), (132,true,410337795), (65,true,677724179), (153,true,391268355)]
def cases212 : List IsoRule := [(15, 660859162255, 36344967696), (23, 660859162255, 36344906256), (27, 669444902543, 36344967696), (29, 669444902543, 36344967456), (30, 669444902543, 36344967201), (120, 669444902543, 34913662821), (184, 669444902543, 34913662581), (216, 669444902543, 34913662326), (232, 660859162255, 34913662821), (240, 660859162255, 34913601381)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert212 : row 8 (660586499599,18) (stages 9) := by
  refine ⟨cones212,cases212,?_,?_,?_⟩ <;> decide +kernel
def cones213 : List CopyRule := [(2,true,2220241424), (96,true,677463299), (36,true,1213608464)]
def cases213 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert213 : row 8 (7751470719,18) (stages 9) := by
  refine ⟨cones213,cases213,?_,?_,?_⟩ <;> decide +kernel
def cones214 : List CopyRule := [(2,true,2220241424), (68,true,1214591504), (192,true,410277424), (80,true,407328304), (36,true,1213608464)]
def cases214 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert214 : row 8 (104388234879,18) (stages 9) := by
  refine ⟨cones214,cases214,?_,?_,?_⟩ <;> decide +kernel
def cones215 : List CopyRule := [(2,true,2220241424), (68,true,1214591504), (192,true,410277424), (80,true,407328304), (36,true,1213608464)]
def cases215 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert215 : row 8 (108548984447,18) (stages 9) := by
  refine ⟨cones215,cases215,?_,?_,?_⟩ <;> decide +kernel
def cones216 : List CopyRule := []
def cases216 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert216 : row 8 (37816241791,18) (stages 9) := by
  refine ⟨cones216,cases216,?_,?_,?_⟩ <;> decide +kernel
def cones217 : List CopyRule := [(4,true,2235962144), (9,true,1683501584), (72,true,1214583584), (17,true,1666728464), (80,true,946148384), (33,true,1648907024), (96,true,677647664), (40,true,1213600544), (48,true,945165344)]
def cases217 : List IsoRule := [(195, 6048421707519, 36344967696)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert217 : row 8 (550863535743,18) (stages 9) := by
  refine ⟨cones217,cases217,?_,?_,?_⟩ <;> decide +kernel
def cones218 : List CopyRule := [(2,true,2235966224), (72,true,1482957584), (80,true,1482892304), (33,true,1750155299), (36,true,1632129794)]
def cases218 : List IsoRule := [(197, 6048428990207, 36344967696)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert218 : row 8 (550866656895,18) (stages 9) := by
  refine ⟨cones218,cases218,?_,?_,?_⟩ <;> decide +kernel
def cones219 : List CopyRule := [(16,true,2251625024), (32,true,2250511184), (3,true,1699222304), (69,true,1451500304), (70,true,1451500289), (73,true,1183134224), (74,true,1183134209)]
def cases219 : List IsoRule := [(204, 6048898752031, 36344967696)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert219 : row 8 (551067983391,18) (stages 9) := by
  refine ⟨cones219,cases219,?_,?_,?_⟩ <;> decide +kernel
def cones220 : List CopyRule := [(4,true,2252673824), (1,true,2252428034), (2,true,2252362514), (32,true,2252477264)]
def cases220 : List IsoRule := [(216, 669444902543, 23746327056)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert220 : row 8 (557507288607,18) (stages 9) := by
  refine ⟨cones220,cases220,?_,?_,?_⟩ <;> decide +kernel
def cones221 : List CopyRule := []
def cases221 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert221 : row 8 (37683076671,18) (stages 9) := by
  refine ⟨cones221,cases221,?_,?_,?_⟩ <;> decide +kernel
def cones222 : List CopyRule := [(160,true,945035040), (136,true,1484006160), (144,true,1483940880)]
def cases222 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert222 : row 8 (34379038335,18) (stages 9) := by
  refine ⟨cones222,cases222,?_,?_,?_⟩ <;> decide +kernel
def cones223 : List CopyRule := [(129,true,1484009490), (130,true,1412985345), (132,true,1484010000), (136,true,1484006160), (144,true,1483940880)]
def cases223 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert223 : row 8 (34513239679,18) (stages 9) := by
  refine ⟨cones223,cases223,?_,?_,?_⟩ <;> decide +kernel
def cones224 : List CopyRule := [(4,true,2269451040), (129,true,1484009490), (130,true,1484009730), (40,true,1213600544), (48,true,945165344)]
def cases224 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert224 : row 8 (38808206911,18) (stages 9) := by
  refine ⟨cones224,cases224,?_,?_,?_⟩ <;> decide +kernel
def cones225 : List CopyRule := [(68,true,1214583344), (72,true,1214583584), (80,true,946148384), (36,true,1213600304), (40,true,1213600544), (48,true,945165344)]
def cases225 : List IsoRule := [(195, 6048421707519, 18027603216), (225, 6048428990207, 18027602256), (226, 6048428990207, 18027602001)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert225 : row 8 (103096417919,18) (stages 9) := by
  refine ⟨cones225,cases225,?_,?_,?_⟩ <;> decide +kernel
def cones226 : List CopyRule := [(36,true,1213600304), (40,true,1213600544), (48,true,945165344), (68,true,1214583344), (72,true,1214583584), (80,true,946148384), (140,true,1468280850), (148,true,1468219410), (152,true,1468153875), (135,true,928258080), (139,true,659822640), (147,true,659757120)]
def cases226 : List IsoRule := [(163, 6048428990207, 18026619216), (195, 6048428990207, 18026615136), (225, 6287849307903, 36344967696), (226, 6048898752031, 18027581541)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert226 : row 8 (652852215423,18) (stages 9) := by
  refine ⟨cones226,cases226,?_,?_,?_⟩ <;> decide +kernel
def cones227 : List CopyRule := [(36,true,1213600304), (40,true,1213600544), (48,true,945165344), (68,true,1214583344), (72,true,1214583584), (80,true,946148384), (132,true,1215631920), (136,true,1215632160), (144,true,947196960)]
def cases227 : List IsoRule := [(7, 652856459007, 36344967696), (11, 652856459007, 36344963856), (13, 653124861695, 36344967696), (14, 653124861695, 36344967681), (15, 653124894463, 36344967696), (19, 652856459007, 36344898576), (21, 653124861695, 36344906256), (22, 653124861695, 36344906241), (23, 653124894463, 36344906256), (25, 653124861695, 36344840976), (26, 653124861695, 36344840961), (27, 653124894463, 36344840976), (28, 661714796159, 36344967696), (29, 661714796287, 36344967696), (30, 661714796287, 36344967681), (35, 652856459007, 35486393616), (67, 652856459007, 35486389776), (97, 653124861695, 35486393616), (98, 653124861695, 35486393601), (99, 653124894463, 35486393616), (131, 652856459007, 35486324496), (161, 653124861695, 35486332176), (162, 653124861695, 35486332161), (163, 653124894463, 35486332176), (193, 653124861695, 35486266896), (194, 653124861695, 35486266881), (195, 653124894463, 35486266896), (224, 661714796159, 35486393616), (225, 661714796287, 35486393616), (226, 661714796287, 35486393601)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert227 : row 8 (652852231807,19) (stages 9) := by
  refine ⟨cones227,cases227,?_,?_,?_⟩ <;> decide +kernel
def cones228 : List CopyRule := [(129,true,911766032), (66,true,928539137), (72,true,1482957584), (80,true,1482892304), (24,true,1480991504), (164,true,931549442)]
def cases228 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert228 : row 8 (103099555391,18) (stages 9) := by
  refine ⟨cones228,cases228,?_,?_,?_⟩ <;> decide +kernel
def cones229 : List CopyRule := [(24,true,1480991504), (3,true,1180176944), (5,true,1164452144), (40,true,1750340384), (48,true,1750275104), (72,true,1482957584), (80,true,1482892304), (194,true,931292417), (164,true,931223042), (142,true,1412923920), (150,true,1397195280)]
def cases229 : List IsoRule := [(225, 6287850348287, 36344967696)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert229 : row 8 (652853255807,18) (stages 9) := by
  refine ⟨cones229,cases229,?_,?_,?_⟩ <;> decide +kernel
def cones230 : List CopyRule := [(8,true,2237931824), (16,true,2237866304), (3,true,1180176944), (5,true,1164452144), (36,true,945250817), (132,true,947216897), (160,true,947021057), (194,true,931292417)]
def cases230 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert230 : row 8 (652853272127,18) (stages 9) := by
  refine ⟨cones230,cases230,?_,?_,?_⟩ <;> decide +kernel
def cones231 : List CopyRule := []
def cases231 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert231 : row 8 (18775679,18) (stages 9) := by
  refine ⟨cones231,cases231,?_,?_,?_⟩ <;> decide +kernel
def cones232 : List CopyRule := [(8,true,2186679344), (16,true,2186679104), (34,true,1213604144), (66,true,1214587184), (96,true,1214457104), (130,true,1215635760), (160,true,1215505680), (192,true,1215505936), (37,true,1166418224), (69,true,1183129904), (133,true,1199907120)]
def cases232 : List IsoRule := [(7, 25100031, 36344967696)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert232 : row 8 (20872831,19) (stages 9) := by
  refine ⟨cones232,cases232,?_,?_,?_⟩ <;> decide +kernel
def cones233 : List CopyRule := [(8,true,2253660209), (16,true,2253594689), (66,true,946295072), (68,true,946295312)]
def cases233 : List IsoRule := [(225, 6287849307903, 18020333136)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert233 : row 8 (652852731519,18) (stages 9) := by
  refine ⟨cones233,cases233,?_,?_,?_⟩ <;> decide +kernel
def cones234 : List CopyRule := [(8,true,2270437680), (16,true,2270372160), (33,true,929583392), (34,true,913854497), (67,true,1182995744), (69,true,1182999824), (70,true,1182999809)]
def cases234 : List IsoRule := [(228, 4640803182143, 18121974021)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert234 : row 8 (652852747839,18) (stages 9) := by
  refine ⟨cones234,cases234,?_,?_,?_⟩ <;> decide +kernel
def cones235 : List CopyRule := []
def cases235 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert235 : row 8 (34378497663,18) (stages 9) := by
  refine ⟨cones235,cases235,?_,?_,?_⟩ <;> decide +kernel
def cones236 : List CopyRule := [(2,true,2253660944), (1,true,2253660929), (4,true,2253656864), (16,true,2253525824)]
def cases236 : List IsoRule := [(232, 660859162255, 19451425296)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert236 : row 8 (653054058015,18) (stages 9) := by
  refine ⟨cones236,cases236,?_,?_,?_⟩ <;> decide +kernel
def cones237 : List CopyRule := []
def cases237 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert237 : row 8 (655067323935,18) (stages 9) := by
  refine ⟨cones237,cases237,?_,?_,?_⟩ <;> decide +kernel
def cones238 : List CopyRule := []
def cases238 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert238 : row 8 (51281535,18) (stages 9) := by
  refine ⟨cones238,cases238,?_,?_,?_⟩ <;> decide +kernel
def cones239 : List CopyRule := []
def cases239 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert239 : row 8 (549807079039,18) (stages 9) := by
  refine ⟨cones239,cases239,?_,?_,?_⟩ <;> decide +kernel
def cones240 : List CopyRule := [(4,true,2203456544), (9,true,1649947664), (17,true,1698185744), (24,true,1749361424), (33,true,1681412624), (40,true,1750344464), (48,true,1750279184), (72,true,1214583584), (80,true,946148384), (96,true,946083104), (136,true,1215632160), (144,true,947196960), (160,true,947131680)]
def cases240 : List IsoRule := [(67, 1649318756095, 36344967696), (131, 1649318756095, 36093309456), (193, 6047365234431, 36344967696), (194, 6047365234431, 36344967681), (195, 653124894463, 23746327056)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert240 : row 8 (549807095423,19) (stages 9) := by
  refine ⟨cones240,cases240,?_,?_,?_⟩ <;> decide +kernel
def cones241 : List CopyRule := []
def cases241 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert241 : row 8 (119422527,18) (stages 9) := by
  refine ⟨cones241,cases241,?_,?_,?_⟩ <;> decide +kernel
def cones242 : List CopyRule := []
def cases242 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert242 : row 8 (6493707903,18) (stages 9) := by
  refine ⟨cones242,cases242,?_,?_,?_⟩ <;> decide +kernel
def cones243 : List CopyRule := []
def cases243 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert243 : row 8 (551954554495,18) (stages 9) := by
  refine ⟨cones243,cases243,?_,?_,?_⟩ <;> decide +kernel
def cones244 : List CopyRule := []
def cases244 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert244 : row 8 (556249521727,18) (stages 9) := by
  refine ⟨cones244,cases244,?_,?_,?_⟩ <;> decide +kernel
def cones245 : List CopyRule := [(2,true,2234925584), (4,true,2234925344), (8,true,2233876784), (32,true,2252546129)]
def cases245 : List IsoRule := [(81, 1664351084287, 36344967696), (145, 1664351084287, 36093309456), (193, 6053807660799, 36344967696), (208, 6062397595263, 36344967696), (209, 661714796287, 23746257216)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert245 : row 8 (556249521791,19) (stages 9) := by
  refine ⟨cones245,cases245,?_,?_,?_⟩ <;> decide +kernel
def cones246 : List CopyRule := []
def cases246 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert246 : row 8 (2199797311,18) (stages 9) := by
  refine ⟨cones246,cases246,?_,?_,?_⟩ <;> decide +kernel
def cones247 : List CopyRule := []
def cases247 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert247 : row 8 (109572922911,18) (stages 9) := by
  refine ⟨cones247,cases247,?_,?_,?_⟩ <;> decide +kernel
def cones248 : List CopyRule := []
def cases248 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert248 : row 8 (590609260063,18) (stages 9) := by
  refine ⟨cones248,cases248,?_,?_,?_⟩ <;> decide +kernel
def cones249 : List CopyRule := [(2,true,2253595664), (4,true,2253591584), (1,true,2253595649), (8,true,2253526064)]
def cases249 : List IsoRule := [(112, 1904869252639, 36344967696), (176, 1904869252639, 36093309456), (208, 6165476810271, 36344967696), (224, 6165476810271, 36343984656), (240, 6302915763743, 36344967696)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert249 : row 8 (659328736799,19) (stages 9) := by
  refine ⟨cones249,cases249,?_,?_,?_⟩ <;> decide +kernel
def cones250 : List CopyRule := []
def cases250 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert250 : row 8 (36558487103,18) (stages 9) := by
  refine ⟨cones250,cases250,?_,?_,?_⟩ <;> decide +kernel
def cones251 : List CopyRule := []
def cases251 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert251 : row 8 (36559535679,19) (stages 9) := by
  refine ⟨cones251,cases251,?_,?_,?_⟩ <;> decide +kernel
def cones252 : List CopyRule := []
def cases252 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert252 : row 8 (550880812671,18) (stages 9) := by
  refine ⟨cones252,cases252,?_,?_,?_⟩ <;> decide +kernel
def cones253 : List CopyRule := []
def cases253 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert253 : row 8 (550880828991,18) (stages 9) := by
  refine ⟨cones253,cases253,?_,?_,?_⟩ <;> decide +kernel
def cones254 : List CopyRule := []
def cases254 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert254 : row 8 (1125006975,18) (stages 9) := by
  refine ⟨cones254,cases254,?_,?_,?_⟩ <;> decide +kernel
def cones255 : List CopyRule := [(4,true,2220233504), (72,true,1214583584), (80,true,946148384), (96,true,946083104)]
def cases255 : List IsoRule := [(193, 5498683162367, 36344967696), (194, 5498683162367, 36344967681)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert255 : row 8 (1125023359,19) (stages 9) := by
  refine ⟨cones255,cases255,?_,?_,?_⟩ <;> decide +kernel
def cones256 : List CopyRule := []
def cases256 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert256 : row 8 (550880820799,18) (stages 9) := by
  refine ⟨cones256,cases256,?_,?_,?_⟩ <;> decide +kernel
def cones257 : List CopyRule := [(4,true,2220233504), (8,true,2220233264), (16,true,2203456064), (32,true,2202407504)]
def cases257 : List IsoRule := [(131, 5498683162367, 32318435856), (193, 6048438959871, 36344967696), (194, 6048438992511, 36344967696)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert257 : row 8 (550880820863,19) (stages 9) := by
  refine ⟨cones257,cases257,?_,?_,?_⟩ <;> decide +kernel
def cones258 : List CopyRule := [(4,true,2220233504), (8,true,2220233264), (16,true,2203456064), (32,true,2202407504)]
def cases258 : List IsoRule := [(3, 550880870143, 36344967696), (65, 1650392465151, 36344967696), (66, 1650392465151, 36344967681), (67, 1650392497919, 36344967696), (129, 1650392465151, 36093309456), (130, 1650392465151, 36093309441), (131, 1650392497919, 36093309456), (192, 6048438976127, 36344967696), (193, 6048438976255, 36344967696), (194, 6048438976255, 36344967681), (195, 6048439009023, 36344967696)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert258 : row 8 (550880837247,20) (stages 9) := by
  refine ⟨cones258,cases258,?_,?_,?_⟩ <;> decide +kernel
def cones259 : List CopyRule := []
def cases259 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert259 : row 8 (1126055487,18) (stages 9) := by
  refine ⟨cones259,cases259,?_,?_,?_⟩ <;> decide +kernel
def cones260 : List CopyRule := []
def cases260 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert260 : row 8 (1193164351,19) (stages 9) := by
  refine ⟨cones260,cases260,?_,?_,?_⟩ <;> decide +kernel
def cones261 : List CopyRule := []
def cases261 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert261 : row 8 (3340647999,20) (stages 9) := by
  refine ⟨cones261,cases261,?_,?_,?_⟩ <;> decide +kernel
def cones262 : List CopyRule := []
def cases262 : List IsoRule := [(128, 4435746897471, 36344967696)]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert262 : row 8 (37700386367,21) (stages 9) := by
  refine ⟨cones262,cases262,?_,?_,?_⟩ <;> decide +kernel
def cones263 : List CopyRule := [(5,true,927540496), (3,true,1194923296), (40,true,645484803), (6,true,929637633), (129,true,307852336), (48,true,377049604), (73,true,1133863200), (81,true,882205200), (82,true,1452491265), (76,true,1452552450), (146,true,1469203201), (140,true,1469133826), (88,true,1452296307), (162,true,1200641569), (164,true,932206098), (394,true,140867889), (404,true,140867906)]
def cases263 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert263 : row 9 (6163699349023,22) (stages 10) := by
  refine ⟨cones263,cases263,?_,?_,?_⟩ <;> decide +kernel
def cones264 : List CopyRule := [(5,true,927540496), (3,true,1178146080), (34,true,929649153), (36,true,913920258), (321,true,680878864), (76,true,1452552450), (81,true,613770000), (82,true,1452425985), (56,true,613830675), (137,true,328561696), (385,true,412447776), (146,true,1469268481), (140,true,1469133826), (138,true,59930193), (84,true,76638034), (168,true,663770643), (112,true,378558244), (30,true,1464046096), (297,true,677468419), (390,true,140867873), (216,true,41325624)]
def cases264 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert264 : row 9 (6163633288735,22) (stages 10) := by
  refine ⟨cones264,cases264,?_,?_,?_⟩ <;> decide +kernel
def cones265 : List CopyRule := [(384,true,1233147681)]
def cases265 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert265 : row 9 (4640803182143,22) (stages 10) := by
  refine ⟨cones265,cases265,?_,?_,?_⟩ <;> decide +kernel
def cones266 : List CopyRule := [(5,true,910763280), (33,true,879317520), (14,true,1670848593), (145,true,882209296), (146,true,1469268481), (140,true,1469329666), (290,true,1217419041), (42,true,1133989921), (50,true,1704149505), (52,true,882331666), (168,true,664162563), (193,true,915567888), (322,true,680878849), (324,true,412443650), (200,true,663775299), (176,true,395727364), (267,true,675690768)]
def cases266 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert266 : row 9 (5611729999423,22) (stages 10) := by
  refine ⟨cones266,cases266,?_,?_,?_⟩ <;> decide +kernel
def cones267 : List CopyRule := [(9,true,1214853648), (264,true,1233527568), (72,true,1231561488)]
def cases267 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert267 : row 9 (6121474629375,22) (stages 10) := by
  refine ⟨cones267,cases267,?_,?_,?_⟩ <;> decide +kernel
def cones268 : List CopyRule := []
def cases268 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert268 : row 9 (6084963262175,22) (stages 10) := by
  refine ⟨cones268,cases268,?_,?_,?_⟩ <;> decide +kernel
def cones269 : List CopyRule := [(2,true,2504532752), (4,true,2504528672), (256,true,2504135552)]
def cases269 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert269 : row 9 (660859162255,22) (stages 10) := by
  refine ⟨cones269,cases269,?_,?_,?_⟩ <;> decide +kernel
def cones270 : List CopyRule := [(4,true,2504528672)]
def cases270 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert270 : row 9 (669444902543,22) (stages 10) := by
  refine ⟨cones270,cases270,?_,?_,?_⟩ <;> decide +kernel
def cones271 : List CopyRule := []
def cases271 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert271 : row 9 (6048421707519,22) (stages 10) := by
  refine ⟨cones271,cases271,?_,?_,?_⟩ <;> decide +kernel
def cones272 : List CopyRule := []
def cases272 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert272 : row 9 (6048428990207,22) (stages 10) := by
  refine ⟨cones272,cases272,?_,?_,?_⟩ <;> decide +kernel
def cones273 : List CopyRule := [(48,true,1767052320)]
def cases273 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert273 : row 9 (6048898752031,22) (stages 10) := by
  refine ⟨cones273,cases273,?_,?_,?_⟩ <;> decide +kernel
def cones274 : List CopyRule := [(140,true,1469329426)]
def cases274 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert274 : row 9 (6287849307903,22) (stages 10) := by
  refine ⟨cones274,cases274,?_,?_,?_⟩ <;> decide +kernel
def cones275 : List CopyRule := []
def cases275 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert275 : row 9 (652856459007,22) (stages 10) := by
  refine ⟨cones275,cases275,?_,?_,?_⟩ <;> decide +kernel
def cones276 : List CopyRule := []
def cases276 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert276 : row 9 (653124861695,22) (stages 10) := by
  refine ⟨cones276,cases276,?_,?_,?_⟩ <;> decide +kernel
def cones277 : List CopyRule := [(64,false,645442048560), (128,false,649720238640), (4,true,2474972192), (9,true,1384723472), (17,true,1480147472), (24,true,1497899792), (40,true,1230377760), (48,true,961942560), (257,true,1413054992), (264,true,1501831952), (272,true,1501766672), (288,true,961812512)]
def cases277 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert277 : row 9 (653124894463,23) (stages 10) := by
  refine ⟨cones277,cases277,?_,?_,?_⟩ <;> decide +kernel
def cones278 : List CopyRule := []
def cases278 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert278 : row 9 (661714796159,22) (stages 10) := by
  refine ⟨cones278,cases278,?_,?_,?_⟩ <;> decide +kernel
def cones279 : List CopyRule := [(64,false,646515528240), (128,false,650793718320), (4,true,2554663712), (256,true,2501128322), (9,true,1418277392), (17,true,1401504272), (24,true,1497899792), (40,true,1230377760), (48,true,961942560)]
def cases279 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert279 : row 9 (661714796287,23) (stages 10) := by
  refine ⟨cones279,cases279,?_,?_,?_⟩ <;> decide +kernel
def cones280 : List CopyRule := [(24,true,1497768720)]
def cases280 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert280 : row 9 (6287850348287,22) (stages 10) := by
  refine ⟨cones280,cases280,?_,?_,?_⟩ <;> decide +kernel
def cones281 : List CopyRule := []
def cases281 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert281 : row 9 (25100031,22) (stages 10) := by
  refine ⟨cones281,cases281,?_,?_,?_⟩ <;> decide +kernel
def cones282 : List CopyRule := []
def cases282 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert282 : row 9 (1649318756095,22) (stages 10) := by
  refine ⟨cones282,cases282,?_,?_,?_⟩ <;> decide +kernel
def cones283 : List CopyRule := []
def cases283 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert283 : row 9 (6047365234431,22) (stages 10) := by
  refine ⟨cones283,cases283,?_,?_,?_⟩ <;> decide +kernel
def cones284 : List CopyRule := []
def cases284 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert284 : row 9 (1664351084287,22) (stages 10) := by
  refine ⟨cones284,cases284,?_,?_,?_⟩ <;> decide +kernel
def cones285 : List CopyRule := []
def cases285 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert285 : row 9 (6053807660799,22) (stages 10) := by
  refine ⟨cones285,cases285,?_,?_,?_⟩ <;> decide +kernel
def cones286 : List CopyRule := []
def cases286 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert286 : row 9 (6062397595263,22) (stages 10) := by
  refine ⟨cones286,cases286,?_,?_,?_⟩ <;> decide +kernel
def cones287 : List CopyRule := []
def cases287 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert287 : row 9 (1904869252639,22) (stages 10) := by
  refine ⟨cones287,cases287,?_,?_,?_⟩ <;> decide +kernel
def cones288 : List CopyRule := []
def cases288 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert288 : row 9 (6165476810271,22) (stages 10) := by
  refine ⟨cones288,cases288,?_,?_,?_⟩ <;> decide +kernel
def cones289 : List CopyRule := [(2,true,2522031120), (4,true,2522027040), (1,true,2522031105), (8,true,2521961520), (128,false,650793657360), (256,false,654568530960)]
def cases289 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert289 : row 9 (6302915763743,23) (stages 10) := by
  refine ⟨cones289,cases289,?_,?_,?_⟩ <;> decide +kernel
def cones290 : List CopyRule := []
def cases290 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert290 : row 9 (5498683162367,22) (stages 10) := by
  refine ⟨cones290,cases290,?_,?_,?_⟩ <;> decide +kernel
def cones291 : List CopyRule := []
def cases291 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert291 : row 9 (6048438959871,22) (stages 10) := by
  refine ⟨cones291,cases291,?_,?_,?_⟩ <;> decide +kernel
def cones292 : List CopyRule := []
def cases292 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert292 : row 9 (6048438992511,22) (stages 10) := by
  refine ⟨cones292,cases292,?_,?_,?_⟩ <;> decide +kernel
def cones293 : List CopyRule := []
def cases293 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert293 : row 9 (550880870143,22) (stages 10) := by
  refine ⟨cones293,cases293,?_,?_,?_⟩ <;> decide +kernel
def cones294 : List CopyRule := []
def cases294 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert294 : row 9 (1650392465151,22) (stages 10) := by
  refine ⟨cones294,cases294,?_,?_,?_⟩ <;> decide +kernel
def cones295 : List CopyRule := [(256,false,654032835120), (4,true,2488668960), (9,true,1683567120), (17,true,1666794000), (24,true,1766138640), (33,true,1665749520), (40,true,1767121680), (48,true,1767056400), (72,true,1231360800), (80,true,962925600), (96,true,962860320)]
def cases295 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert295 : row 9 (1650392497919,23) (stages 10) := by
  refine ⟨cones295,cases295,?_,?_,?_⟩ <;> decide +kernel
def cones296 : List CopyRule := []
def cases296 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert296 : row 9 (6048438976127,22) (stages 10) := by
  refine ⟨cones296,cases296,?_,?_,?_⟩ <;> decide +kernel
def cones297 : List CopyRule := [(256,false,654032835120), (4,true,2488668960), (9,true,1683567120), (17,true,1666794000), (24,true,1766138640), (33,true,1665749520), (40,true,1767121680), (48,true,1767056400), (72,true,1231360800), (80,true,962925600), (96,true,962860320)]
def cases297 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert297 : row 9 (6048438976255,23) (stages 10) := by
  refine ⟨cones297,cases297,?_,?_,?_⟩ <;> decide +kernel
def cones298 : List CopyRule := [(64,false,581051945520), (4,true,2488668960), (128,false,649754645040), (256,false,654032835120), (9,true,1683567120), (17,true,1666794000), (24,true,1766138640), (33,true,1665749520), (40,true,1767121680), (48,true,1767056400)]
def cases298 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert298 : row 9 (6048439009023,24) (stages 10) := by
  refine ⟨cones298,cases298,?_,?_,?_⟩ <;> decide +kernel
def cones299 : List CopyRule := []
def cases299 : List IsoRule := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem cert299 : row 9 (4435746897471,22) (stages 10) := by
  refine ⟨cones299,cases299,?_,?_,?_⟩ <;> decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem stage1 : ∀ s ∈ stages 1, row 1 s (stages 2) := by
  intro s hs
  simp only [stages,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl
  · exact cert0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem stage2 : ∀ s ∈ stages 2, row 2 s (stages 3) := by
  intro s hs
  simp only [stages,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl
  · exact cert1
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem stage3 : ∀ s ∈ stages 3, row 3 s (stages 4) := by
  intro s hs
  simp only [stages,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl
  · exact cert2
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem stage4 : ∀ s ∈ stages 4, row 4 s (stages 5) := by
  intro s hs
  simp only [stages,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl
  · exact cert3
  · exact cert4
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem stage5 : ∀ s ∈ stages 5, row 5 s (stages 6) := by
  intro s hs
  simp only [stages,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cert5
  · exact cert6
  · exact cert7
  · exact cert8
  · exact cert9
  · exact cert10
  · exact cert11
  · exact cert12
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem stage6 : ∀ s ∈ stages 6, row 6 s (stages 7) := by
  intro s hs
  simp only [stages,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cert13
  · exact cert14
  · exact cert15
  · exact cert16
  · exact cert17
  · exact cert18
  · exact cert19
  · exact cert20
  · exact cert21
  · exact cert22
  · exact cert23
  · exact cert24
  · exact cert25
  · exact cert26
  · exact cert27
  · exact cert28
  · exact cert29
  · exact cert30
  · exact cert31
  · exact cert32
  · exact cert33
  · exact cert34
  · exact cert35
  · exact cert36
  · exact cert37
  · exact cert38
  · exact cert39
  · exact cert40
  · exact cert41
  · exact cert42
  · exact cert43
  · exact cert44
  · exact cert45
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem stage7 : ∀ s ∈ stages 7, row 7 s (stages 8) := by
  intro s hs
  simp only [stages,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cert46
  · exact cert47
  · exact cert48
  · exact cert49
  · exact cert50
  · exact cert51
  · exact cert52
  · exact cert53
  · exact cert54
  · exact cert55
  · exact cert56
  · exact cert57
  · exact cert58
  · exact cert59
  · exact cert60
  · exact cert61
  · exact cert62
  · exact cert63
  · exact cert64
  · exact cert65
  · exact cert66
  · exact cert67
  · exact cert68
  · exact cert69
  · exact cert70
  · exact cert71
  · exact cert72
  · exact cert73
  · exact cert74
  · exact cert75
  · exact cert76
  · exact cert77
  · exact cert78
  · exact cert79
  · exact cert80
  · exact cert81
  · exact cert82
  · exact cert83
  · exact cert84
  · exact cert85
  · exact cert86
  · exact cert87
  · exact cert88
  · exact cert89
  · exact cert90
  · exact cert91
  · exact cert92
  · exact cert93
  · exact cert94
  · exact cert95
  · exact cert96
  · exact cert97
  · exact cert98
  · exact cert99
  · exact cert100
  · exact cert101
  · exact cert102
  · exact cert103
  · exact cert104
  · exact cert105
  · exact cert106
  · exact cert107
  · exact cert108
  · exact cert109
  · exact cert110
  · exact cert111
  · exact cert112
  · exact cert113
  · exact cert114
  · exact cert115
  · exact cert116
  · exact cert117
  · exact cert118
  · exact cert119
  · exact cert120
  · exact cert121
  · exact cert122
  · exact cert123
  · exact cert124
  · exact cert125
  · exact cert126
  · exact cert127
  · exact cert128
  · exact cert129
  · exact cert130
  · exact cert131
  · exact cert132
  · exact cert133
  · exact cert134
  · exact cert135
  · exact cert136
  · exact cert137
  · exact cert138
  · exact cert139
  · exact cert140
  · exact cert141
  · exact cert142
  · exact cert143
  · exact cert144
  · exact cert145
  · exact cert146
  · exact cert147
  · exact cert148
  · exact cert149
  · exact cert150
  · exact cert151
  · exact cert152
  · exact cert153
  · exact cert154
  · exact cert155
  · exact cert156
  · exact cert157
  · exact cert158
  · exact cert159
  · exact cert160
  · exact cert161
  · exact cert162
  · exact cert163
  · exact cert164
  · exact cert165
  · exact cert166
  · exact cert167
  · exact cert168
  · exact cert169
  · exact cert170
  · exact cert171
  · exact cert172
  · exact cert173
  · exact cert174
  · exact cert175
  · exact cert176
  · exact cert177
  · exact cert178
  · exact cert179
  · exact cert180
  · exact cert181
  · exact cert182
  · exact cert183
  · exact cert184
  · exact cert185
  · exact cert186
  · exact cert187
  · exact cert188
  · exact cert189
  · exact cert190
  · exact cert191
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem stage8 : ∀ s ∈ stages 8, row 8 s (stages 9) := by
  intro s hs
  simp only [stages,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cert192
  · exact cert193
  · exact cert194
  · exact cert195
  · exact cert196
  · exact cert197
  · exact cert198
  · exact cert199
  · exact cert200
  · exact cert201
  · exact cert202
  · exact cert203
  · exact cert204
  · exact cert205
  · exact cert206
  · exact cert207
  · exact cert208
  · exact cert209
  · exact cert210
  · exact cert211
  · exact cert212
  · exact cert213
  · exact cert214
  · exact cert215
  · exact cert216
  · exact cert217
  · exact cert218
  · exact cert219
  · exact cert220
  · exact cert221
  · exact cert222
  · exact cert223
  · exact cert224
  · exact cert225
  · exact cert226
  · exact cert227
  · exact cert228
  · exact cert229
  · exact cert230
  · exact cert231
  · exact cert232
  · exact cert233
  · exact cert234
  · exact cert235
  · exact cert236
  · exact cert237
  · exact cert238
  · exact cert239
  · exact cert240
  · exact cert241
  · exact cert242
  · exact cert243
  · exact cert244
  · exact cert245
  · exact cert246
  · exact cert247
  · exact cert248
  · exact cert249
  · exact cert250
  · exact cert251
  · exact cert252
  · exact cert253
  · exact cert254
  · exact cert255
  · exact cert256
  · exact cert257
  · exact cert258
  · exact cert259
  · exact cert260
  · exact cert261
  · exact cert262
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem stage9 : ∀ s ∈ stages 9, row 9 s (stages 10) := by
  intro s hs
  simp only [stages,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cert263
  · exact cert264
  · exact cert265
  · exact cert266
  · exact cert267
  · exact cert268
  · exact cert269
  · exact cert270
  · exact cert271
  · exact cert272
  · exact cert273
  · exact cert274
  · exact cert275
  · exact cert276
  · exact cert277
  · exact cert278
  · exact cert279
  · exact cert280
  · exact cert281
  · exact cert282
  · exact cert283
  · exact cert284
  · exact cert285
  · exact cert286
  · exact cert287
  · exact cert288
  · exact cert289
  · exact cert290
  · exact cert291
  · exact cert292
  · exact cert293
  · exact cert294
  · exact cert295
  · exact cert296
  · exact cert297
  · exact cert298
  · exact cert299
set_option maxRecDepth 40000 in
set_option maxHeartbeats 24000000 in
theorem allRows : ∀ n : Fin 10, 0<n.val → ∀ s ∈ stages n.val, row n.val s (stages (n.val+1)) := by
  intro n h
  fin_cases n
  · exact (by decide : ¬0<0) h |>.elim
  · exact stage1
  · exact stage2
  · exact stage3
  · exact stage4
  · exact stage5
  · exact stage6
  · exact stage7
  · exact stage8
  · exact stage9
end Astra1182.Ten

/- At order ten, every 27-edge graph contains a copy of one of the two cores. -/
namespace Astra1182.Ten
open SimpleGraph
abbrev V := Fin 10
def target (kind : Bool) (u v : V) := (mask kind).testBit ((min u v).val*10+(max u v).val)
theorem order_le (kind : Bool) : order kind ≤ 10 := by cases kind <;> decide
def incl (kind : Bool) := Fin.castLEEmb (order_le kind)

theorem active : ∀ kind : Bool, ∀ u v : V, target kind u v=true →
    ∃ i j : Fin (order kind), incl kind i=u ∧ incl kind j=v ∧ core kind i j=true := by decide +kernel

theorem rowTen (G : SimpleGraph V) (size : G.edgeSet.ncard=18) :
    ∃ m ∈ [618970019714747783169716278,72057645653176374], ∃ e : V ↪ V, ∀ i j, G.Adj i j →
      m.testBit ((min (e i) (e j)).val*10+(max (e i) (e j)).val)=false := by
  classical
  have count : G.edgeFinset.card=18 := by
    rwa [←show G.edgeSet.ncard=G.edgeFinset.card from Set.ncard_eq_toFinset_card' _]
  have csize : Gᶜ.edgeFinset.card=27 := by
    have sets : Gᶜ.edgeFinset = (⊤ : SimpleGraph V).edgeFinset \ G.edgeFinset := by
      apply Finset.coe_injective
      simp only [Finset.coe_sdiff,coe_edgeFinset,←edgeSet_sdiff,top_sdiff]
    rw [sets,Finset.card_sdiff_of_subset (edgeFinset_mono le_top),
      card_edgeFinset_top_eq_card_choose_two,Fintype.card_fin,count]
    decide
  obtain hc | ⟨s,hs,_,e,rel⟩ := classify stages (by decide) allRows 9 (by decide) V Gᶜ
    (by simp) (by rw [csize]; decide) (by rw [csize])
  · obtain ⟨kind,f,hf⟩ := hc
    obtain ⟨π,map⟩ := Equiv.Perm.exists_extending_pair (incl kind) f (incl kind).injective f.injective
    refine ⟨mask kind,by cases kind <;> simp [mask],π.symm.toEmbedding,?_⟩
    intro u v huv
    change target kind (π.symm u) (π.symm v)=false
    apply Bool.eq_false_iff.mpr
    intro bad
    obtain ⟨i,j,ha,hb,hit⟩ := active kind _ _ bad
    have ui : f i=u := by rw [←map i,ha,π.apply_symm_apply]
    have vj : f j=v := by rw [←map j,hb,π.apply_symm_apply]
    exact (hf i j hit).2 (by simpa [ui,vj] using huv)
  · simp [stages] at hs
end Astra1182.Ten

theorem OMA.solution : OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H1_R1_H1_R1.H3 := fun G _ h => Astra1182.Ten.rowTen G h
